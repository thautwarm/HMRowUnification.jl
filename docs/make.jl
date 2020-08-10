using HMRowUnification
using Documenter

makedocs(;
    modules=[HMRowUnification],
    authors="thautwarm <twshere@outlook.com> and contributors",
    repo="https://github.com/thautwarm/HMRowUnification.jl/blob/{commit}{path}#L{line}",
    sitename="HMRowUnification.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://thautwarm.github.io/HMRowUnification.jl",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/thautwarm/HMRowUnification.jl",
)
