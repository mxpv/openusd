// Native OpenUSD counterpart of the Rust open_bench example.
// Build with an OpenUSD SDK; see README.md in this directory.
#include "pxr/usd/usd/stage.h"
#include "pxr/usd/usd/primRange.h"
#include "pxr/usd/usd/attribute.h"
#include "pxr/usd/ar/resolverScopedCache.h"

#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <sys/resource.h>

PXR_NAMESPACE_USING_DIRECTIVE
using Clock = std::chrono::steady_clock;

static void phase(const char* name, Clock::time_point start) {
    std::cerr << name << " " << std::fixed << std::setprecision(6)
              << std::chrono::duration<double>(Clock::now() - start).count()
              << "s";
}

int main(int argc, char** argv) {
    try {
        bool proxies = false, authored = false, retraverse = false;
        bool noArrays = false, loadNone = false;
        std::string root, until, status;
        UsdTimeCode time = UsdTimeCode::Default();
        for (int i = 1; i < argc; ++i) {
            const std::string arg = argv[i];
            const auto next = [&]() -> std::string {
                if (++i == argc) throw std::runtime_error("missing option value");
                return argv[i];
            };
            if (arg == "--proxies") proxies = true;
            else if (arg == "--authored") authored = true;
            else if (arg == "--retraverse") retraverse = true;
            else if (arg == "--no-arrays") noArrays = true;
            else if (arg == "--load-none") loadNone = true;
            else if (arg == "--no-heap") {}
            else if (arg == "--until") until = next();
            else if (arg == "--status") status = next();
            else if (arg == "--time") time = UsdTimeCode(std::stod(next()));
            else if (arg.rfind("--", 0) == 0)
                throw std::runtime_error("unknown option: " + arg);
            else if (!root.empty()) throw std::runtime_error("multiple roots");
            else root = arg;
        }
        if (root.empty()) throw std::runtime_error("a root layer is required");
        if (!until.empty() && until != "open" && until != "metadata"
            && until != "retraverse" && until != "arrays")
            throw std::runtime_error("unknown phase: " + until);

        auto start = Clock::now();
        auto stage = UsdStage::Open(root, loadNone ? UsdStage::LoadNone : UsdStage::LoadAll);
        if (!stage) throw std::runtime_error("failed to open stage");
        phase("open", start);
        std::cerr << '\n';
        std::vector<SdfPath> paths;
        const auto traverse = [&]() {
            ArResolverScopedCache scope;
            std::vector<SdfPath> result;
            const auto predicate = proxies
                ? UsdTraverseInstanceProxies(UsdPrimDefaultPredicate)
                : Usd_PrimFlagsPredicate(UsdPrimDefaultPredicate);
            for (const auto& prim : stage->Traverse(predicate))
                result.push_back(prim.GetPath());
            for (const auto& path : result)
                stage->GetPrimAtPath(path).GetTypeName();
            return result;
        };
        if (until != "open") {
            start = Clock::now();
            paths = traverse();
            phase("metadata", start);
            std::cerr << " prims: " << paths.size() << '\n';
            if (!status.empty()) {
                std::ofstream out(status);
                out.exceptions(std::ios::failbit | std::ios::badbit);
                for (const auto& path : paths) {
                    const auto p = stage->GetPrimAtPath(path);
                    out << path << ' ' << p.IsActive() << p.IsLoaded()
                        << p.IsDefined() << p.IsAbstract()
                        << p.IsInstance() << p.IsInstanceProxy() << '\n';
                }
            }
        }
        if (retraverse && until != "open" && until != "metadata") {
            start = Clock::now();
            const auto count = traverse().size();
            phase("retraverse", start);
            std::cerr << " prims: " << count << '\n';
        }
        if (!noArrays && (until.empty() || until == "arrays")) {
            start = Clock::now();
            ArResolverScopedCache scope;
            size_t arrays = 0, elements = 0;
            for (const auto& path : paths) {
                const auto prim = stage->GetPrimAtPath(path);
                const auto attrs = authored ? prim.GetAuthoredAttributes() : prim.GetAttributes();
                for (const auto& attr : attrs) {
                    VtValue value;
                    if (attr.Get(&value, time) && value.IsArrayValued()) {
                        ++arrays;
                        elements += value.GetArraySize();
                    }
                }
            }
            phase("arrays", start);
            std::cerr << " arrays: " << arrays << " elements: " << elements << '\n';
        }
        rusage usage{};
        getrusage(RUSAGE_SELF, &usage);
        std::cerr << "rss_kib: " << usage.ru_maxrss << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
