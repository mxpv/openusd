import collections.abc
import warnings
from enum import IntEnum

try:
    import lz4
    import lz4.block
except ImportError:
    raise ImportError("LZ4 was not found, please install: pip3 install lz4")

from file_formats.parsers.binary import data_sizes
from file_formats.parsers.binary.constants import ENDIAN


class LZ4:
    """Wrapper class to include some of the LZ4 functions used by USD"""

    # From LZ4
    LZ4_MAX_INPUT_SIZE = 0x7E000000

    @classmethod
    def DecompressFromBuffer(cls, data, outputSize):
        """Uses standard decompression logic to handle decompressing data blocks with LZ4.
        All blocks must start with a number of chunks specified, so that the algorithm can
        decide whether to decompress in chunks or not.
        """
        numChunks = data[0]
        data = data[1:]
        if numChunks == 0:
            decompressed = lz4.block.decompress(data, outputSize)
            return decompressed
        else:
            warnings.warn("Chunked lists are rarely encountered in test data so not well tested")
            decompressed = []
            for chunk in range(numChunks):
                size = data[0]
                chunk = data[1 : size + 1]
                data = data[size + 1 :]
                decompressed.extend(lz4.block.decompress(chunk, size))

            return decompressed

    @classmethod
    def GetMaxInputSize(cls):
        """Copied from LZ4"""
        return 127 * cls.LZ4_MAX_INPUT_SIZE

    @classmethod
    def GetCompressBound(cls, isize):
        """Copied from LZ4"""
        if isize > cls.LZ4_MAX_INPUT_SIZE:
            return 0

        return (isize) + ((isize) // 255) + 16

    @classmethod
    def GetUncompressedBufferSize(cls, inputSize):
        """Infers the final buffer size of a buffer based on the compressed input size."""
        if inputSize > cls.GetMaxInputSize():
            return 0

        # If it fits within a single chunk, it's just the compressed bounds + 1
        if inputSize <= cls.LZ4_MAX_INPUT_SIZE:
            return cls.GetCompressBound(inputSize) + 1

        int32 = data_sizes.INT32
        numWholeChunks = inputSize // cls.LZ4_MAX_INPUT_SIZE
        size = 1 + numWholeChunks * (
            cls.GetCompressBound(cls.LZ4_MAX_INPUT_SIZE) + int32
        )  # Size includes a number of chunks int at the head

        partialChunkSize = inputSize % cls.LZ4_MAX_INPUT_SIZE
        if partialChunkSize:
            size += cls.GetCompressBound(partialChunkSize) + int32

        return size

    @classmethod
    def GetCompressedIntBufferSize(cls, count, size=data_sizes.UINT32):
        """Convenience method to infer a final buffer size for an array of integers of a given size"""
        encoded_size = IntegerArray.get_encoded_int_array_size(count, size=size)
        buffer_size = cls.GetUncompressedBufferSize(encoded_size)
        return buffer_size


class IntegerArray(collections.abc.Sequence[int]):
    """Crate compresses integer arrays with extra compression beyond LZ4.

    Arrays are first encoded as a delta of each value to the prior value.

    Following this, the most common value in the delta array is used as a starting point for encoding.
    This is the first value in the encoded array.

    Following this is a set of 2-bit codepoints that describe whether each index should use the common value, or
    whether we should add a signed integer. The codepoint also describes the size of the number.

    Finally there is an encoding of the actual delta values.
    """

    class _CodeType(IntEnum):
        CommonValue = 0
        QuarterSize = 1
        HalfSize = 2
        FullSize = 3

    @classmethod
    def _get_num_code_bytes(cls, count):
        # The data used to store the code bytes
        # Each entry takes 2 bits
        # An extra 7 is used to make sure it rounds up evenly
        # Finally, these are bits not bytes, so divided by eight
        return ((count * 2) + 7) // 8

    @classmethod
    def get_encoded_int_array_size(cls, count, size=4):
        if not count:
            return 0

        # Integers are pre-compressed before running through LZ4
        return sum(
            [
                # The most common value, also the same size as the main int type
                size,
                cls._get_num_code_bytes(count),
                # The maximum size that the final bytes can take
                (count * size),
            ]
        )

    def __init__(self, count, data, size=data_sizes.INT32):
        self._data = data
        self._count = count
        self._int_size = size

        # Constants
        self._quarter_int_size = self._int_size // 4
        self._half_int_size = self._int_size // 2

        # State
        self._common_value = self._read_int()
        self._previous_value = 0
        self._codes_offset = 0
        self._value_offset = 0

        # TODO: The compressed array interface and decoder state should be decoupled in a future revision. This could
        # allow for lazy decoding of compressed arrays.
        self._elements = []
        self._process()

    def __getitem__(self, index: int) -> int:
        return self._elements[index]

    def __len__(self) -> int:
        return len(self._elements)

    def __iter__(self) -> int:
        for element in self._elements:
            yield element

    def _process(self):
        """Integer arrays store their entries 4 elements per code byte (2 bits per entry).
        So run through each code byte and take 4 elements at a time to process the values
        """
        num_code_bytes = self._get_num_code_bytes(self._count)

        ints_left = self._count
        self._value_offset += num_code_bytes

        while ints_left >= 4:
            self._int_array_decoder(4)
            ints_left -= 4

        if ints_left:
            self._int_array_decoder(ints_left)

    def _int_array_decoder(self, count):
        """Iterate through the array and process the list of operations to construct the final array"""
        code_byte = self._read_code_byte()

        for i in range(count):
            # A single 8-bit code byte stores code-bits for 4 elements
            shifted = (code_byte >> (2 * i)) & 3
            if shifted == self._CodeType.CommonValue:
                self._previous_value += self._common_value
            elif shifted == self._CodeType.QuarterSize:
                self._previous_value += self._read_value_ints(self._quarter_int_size)
            elif shifted == self._CodeType.HalfSize:
                self._previous_value += self._read_value_ints(self._half_int_size)
            elif shifted == self._CodeType.FullSize:
                self._previous_value += self._read_value_ints(self._int_size)
            else:
                raise RuntimeError("Unknown code byte")

            self._elements.append(self._previous_value)

    def _read_code_byte(self):
        """Convenience method to read a code byte from the top of the array"""
        value = self._data[self._codes_offset]
        self._codes_offset += 1
        return value

    def _read_value_ints(self, size, signed=True):
        """Convenience method to read the actual byte from the integer section of the array"""
        value = self._data[self._value_offset : self._value_offset + size]
        self._value_offset += size

        result = int.from_bytes(value, signed=signed, byteorder=ENDIAN)
        return result

    def _read_int(self):
        """Convenience method to read an int from the array and advancing forward through the buffer"""
        bytes = self._data[: self._int_size]
        self._data = self._data[self._int_size :]
        return int.from_bytes(bytes, signed=True, byteorder=ENDIAN)
