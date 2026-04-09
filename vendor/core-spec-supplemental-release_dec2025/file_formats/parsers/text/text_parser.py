import os

from file_formats.format import Format
from file_formats.parsers.text.usda import UsdaVisitor, grammar


class TextParser:
    """
    Object responsible for parsing a text file and returning
    it's layer data.
    """

    def parse(self, file: str) -> Format:
        """
        Parses the content of the given file and
        returns the data model as a Format instance.
        """
        if not os.path.exists(file):
            raise ValueError(f"Given path {file} does not exist!")

        with open(file, "r", encoding="utf-8") as usda_file:
            content = grammar.parse(usda_file.read())

        visitor = UsdaVisitor()
        format = visitor.visit(content)

        return format
