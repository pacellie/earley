session Earley_Parser = HOL +
  options [
    timeout = 600,
    document = pdf,
    document_output = "build",
    (*document_build = "lipics_pdflatex"*)  (*or: "lipics" for LuaLaTeX*)
    document_build = "pdflatex"
  ]
  sessions
    "HOL-Library"
  theories [document = false]
    Limit
    CFG
    Derivations
    Earley
    Earley_Fixpoint
    Earley_Recognizer
    Earley_Parser
    Examples
  theories
    Document
  document_files
    "root.bib"
    "root.tex"
    "cc-by.pdf"
    "lipics-logo-bw.pdf"
    "lipics-v2021.cls"
    "orcid.pdf"
