module

public import RequestProject.Sec1_Introduction.Terms
public import RequestProject.Sec1_Introduction.PushPull

/-!
# Section 1: Introduction

The four judgements of the introduction:
`⊢_GR pull_□`, `⊢_GR push_□`, `⊢_LL pull_!` and `⊬_LL push_!`.

Like the introduction of the paper, this section *previews* claims whose precise setting comes
later: the terms are written in GrCore (Section 2), `⊢_GR push_□` is the derivation of
Section 3, and LL is IMELL (Section 4).  It is the only section that imports later sections.

Reading order:

1. `Sec1_Introduction/Terms.lean` — the GrCore terms `pushTerm`, `pullTerm` and their types.
2. `Sec1_Introduction/PushPull.lean` — the four judgements (`gr_pull`, `gr_push`, `ll_pull`,
   `ll_push_not_derivable`).
-/
