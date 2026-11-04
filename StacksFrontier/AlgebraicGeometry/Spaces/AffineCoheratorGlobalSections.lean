module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# The coherator of an affine algebraic space is the associated module of the global sections

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B` and set
`A = Γ(X, 𝒪_X)`.  Stacks 08H0 (1) says that the coherator

`Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)`

of Stacks 077V (2) is the functor sending an `𝒪_X`-module `𝓕` to the quasi-coherent
`𝒪_X`-module associated to the `A`-module `Γ(X, 𝓕)`.  That is proved here, in both of the
shapes in which it is a statement: `Γ(X, -) ⋙ (-)^~` *is* a right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, and consequently any coherator is naturally isomorphic to it.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionRingSmallEtale` is `A = Γ(X, 𝒪_X)`, the ring of
  compatible sections of the structure sheaf of the small étale ringed site of `X`.
* `AlgebraicGeometry.Space.moduleGlobalSectionsSmallEtale` is `Γ(X, -)`, global sections of
  `𝒪_X`-modules read as `A`-modules; it is `Stacks.Cohomology.SiteModules.globalSectionsFunctor`
  of Stacks 071H at the small étale ringed site of `X`.

## Main results

* `AlgebraicGeometry.Space.inclusionAdjunctionGlobalSectionsAssociated`: **Stacks 08H0 (1)** —
  `Γ(X, -) ⋙ (-)^~` is right adjoint to `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, so it *is* a coherator of `X`.
* `AlgebraicGeometry.Space.coheratorIsoAssociatedGlobalSections`: **Stacks 08H0 (1)** — any
  coherator of `X` is naturally isomorphic to `Γ(X, -) ⋙ (-)^~`.
* `AlgebraicGeometry.Space.exists_coheratorAdjunction_smallEtale`: a coherator with its
  adjunction exists, from Stacks 077V (2); this is the anti-vacuity check for the `Q`/`adjQ`
  binders.

## What is carried, and why it is an input and not the conclusion

Two data are carried as binders, exactly as the scheme analogue Stacks 08D9 consumes them from
the library (`Stacks.DerivedQCoh.coheratorSpecIso` of
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineCoherator`, which takes
`AlgebraicGeometry.coheratorAdjunction` and `AlgebraicGeometry.tildeEquiv` as given).  Both are
quantified over their own data, neither mentions this statement's `𝓕` or its conclusion, and
each constrains the *input*.

**The associated-module equivalence.**  `assoc : Mod(A) ≌ QCoh(𝒪_X)` together with
`adjAssoc : assoc.functor ⋙ ι ⊣ Γ(X, -)`: the functor `M ↦ M^~` taking an `A`-module to the
associated quasi-coherent `𝒪_X`-module, that it is an equivalence onto `QCoh(𝒪_X)`, and that as
a functor to all `𝒪_X`-modules it is left adjoint to global sections.  This is the affine case
of Stacks 03DX (2) / Stacks 03M3 together with Stacks 01BH (4); for an affine *scheme* it is
`AlgebraicGeometry.tildeEquiv` and `AlgebraicGeometry.tilde.adjunction` (Stacks 01I7), which is
how the scheme analogue gets it.  The development does not have it on the small étale site of
an algebraic space: the associated-module functor of Stacks 03DU (4) is built there only for
the small étale site of a *scheme*
(`AlgebraicGeometry.SmallEtale.associatedModule`), and
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` has no left adjoint anywhere in the tree.

**A coherator.**  `Q` together with `adjQ : ι ⊣ Q`, used only by
`AlgebraicGeometry.Space.coheratorIsoAssociatedGlobalSections`.  Stacks 077V (2) is available
here as `AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves`, which is a
`CategoryTheory.Functor.IsLeftAdjoint`, i.e. the *existence* of a right adjoint; a functor
chosen out of it by `CategoryTheory.Functor.rightAdjoint` is a `Classical.choose` and its
identity is about a chosen witness rather than about the coherator.  So the pair is taken as
data, and the statement is then about every coherator rather than about one chosen one, which
is stronger.

Neither carry is vacuous.  The coherator pair is satisfiable:
`AlgebraicGeometry.Space.exists_coheratorAdjunction_smallEtale` below produces it at the module
universe `u` from Stacks 077V (2), with no hypothesis.  The
associated-module equivalence is satisfiable because it is a theorem of the source — the affine
case of Stacks 03DX (2) — and it is satisfiable non-degenerately: `assoc` being an equivalence
forces `QCoh(𝒪_X)` to have as many objects as `Mod(A)` has, so it cannot be discharged by
collapsing the category.  What is *not* done here is to exhibit it in this development's
vocabulary; that is the missing input named above.

## Implementation notes

The module universe `m` of the `𝒪_X`-modules is free.  No abelian structure is used: both
statements are about adjunctions, and `QCoh(𝒪_X)` is the full subcategory
`AlgebraicGeometry.Space.QuasicoherentSheaves` of Stacks 03G9, which is a category with no
hypothesis.  Global sections of modules at universe `m` on a site whose objects lie in
`Type (u + 1)` are a module at `max (u + 1) m`, so `A`-modules are taken there.

Affineness of `X` is `AlgebraicGeometry.Space.IsAffineSpace`, and it is a binder of both
statements even though the proofs do not use it: the carried associated-module equivalence is
what the source derives *from* affineness, and a statement of Stacks 08H0 must not be about a
non-affine `X`.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- `A = Γ(X, 𝒪_X)`, the ring of compatible sections of the structure sheaf of the small étale
ringed site of the algebraic space `X`. -/
abbrev globalSectionRingSmallEtale :=
  GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- `Γ(X, -) : Mod(𝒪_X) ⥤ Mod(A)`, global sections of an `𝒪_X`-module read as a module over
`A = Γ(X, 𝒪_X)`.  This is `Stacks.Cohomology.SiteModules.globalSectionsFunctor` of Stacks 071H
at the small étale ringed site of `X`. -/
abbrev moduleGlobalSectionsSmallEtale :
    Modules.{u, m} B S hS F hF ⥤
      ModuleCat.{max (u + 1) m} (globalSectionRingSmallEtale B S hS F hF) :=
  globalSectionsFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- **The coherator pair carried below is satisfiable.**  At the module universe `u` of the
schemes, Stacks 077V (2) produces a right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)` together with an adjunction.

This is the anti-vacuity check for the `Q`/`adjQ` binders of
`AlgebraicGeometry.Space.coheratorIsoAssociatedGlobalSections`.  It is
`AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves` read as the existence statement
it is; the two closure classes it needs in scope are unconditional theorems, so no hypothesis
is added. -/
theorem exists_coheratorAdjunction_smallEtale :
    ∃ Q : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF,
      Nonempty ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ Q) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let := isLeftAdjoint_ι_quasicoherentSheaves B S hS F hF
  Functor.IsLeftAdjoint.exists_rightAdjoint

section Affine

variable (assoc : ModuleCat.{max (u + 1) m} (globalSectionRingSmallEtale B S hS F hF) ≌
      QuasicoherentSheaves.{u, m} B S hS F hF)
    (adjAssoc : assoc.functor ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
        moduleGlobalSectionsSmallEtale.{u, m} B S hS F hF)

/-- **Stacks 08H0 (1).**  Let `X` be an affine algebraic space and `A = Γ(X, 𝒪_X)`.  The functor
sending an `𝒪_X`-module `𝓕` to the quasi-coherent `𝒪_X`-module associated to the `A`-module
`Γ(X, 𝓕)` is a right adjoint of the inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`; that is, it is a
coherator of `X`.

Carried: the associated-module equivalence `assoc : Mod(A) ≌ QCoh(𝒪_X)` of the affine case of
Stacks 03DX (2) and its adjunction `adjAssoc` to global sections, Stacks 01BH (4).  See
"What is carried, and why it is an input and not the conclusion" in the module documentation.

The proof is the source's, and is the one the scheme analogue Stacks 08D9 (1) uses: composing
the adjunction `assoc.inverse ⊣ assoc.functor` of the equivalence with `adjAssoc` gives
`assoc.inverse ⋙ assoc.functor ⋙ ι ⊣ Γ(X, -) ⋙ assoc.functor`, and the left-hand side is `ι`
by the counit of the equivalence. -/
@[stacks 08H0 "(1): the coherator of an affine algebraic space is the associated module of the \
global sections; carried are the associated-module equivalence Mod(A) ≌ QCoh(O_X) of the affine \
case of Stacks 03DX(2) and its adjunction to global sections (Stacks 01BH(4)), neither of which \
this development has on the small etale site of an algebraic space"]
def inclusionAdjunctionGlobalSectionsAssociated (_hAffine : IsAffineSpace B S hS F) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
        moduleGlobalSectionsSmallEtale.{u, m} B S hS F hF ⋙ assoc.functor :=
  have hleft : assoc.inverse ⋙ (assoc.functor ⋙
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι) ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
    (Functor.associator assoc.inverse assoc.functor _).symm ≪≫
      Functor.isoWhiskerRight assoc.counitIso _ ≪≫ Functor.leftUnitor _
  (assoc.symm.toAdjunction.comp adjAssoc).ofNatIsoLeft hleft

/-- **Stacks 08H0 (1).**  Let `X` be an affine algebraic space and `A = Γ(X, 𝒪_X)`.  Every
coherator `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of `X` — every right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, which is what Stacks 077V (2) produces — is naturally isomorphic to the
functor sending `𝓕` to the quasi-coherent `𝒪_X`-module associated to the `A`-module
`Γ(X, 𝓕)`.

Carried: a coherator `Q` with its adjunction `adjQ`, and the associated-module equivalence; see
"What is carried, and why it is an input and not the conclusion" in the module documentation.
Both sides are right adjoints of the inclusion, by `adjQ` and by
`AlgebraicGeometry.Space.inclusionAdjunctionGlobalSectionsAssociated`, and a right adjoint is
unique up to a unique natural isomorphism. -/
@[stacks 08H0 "(1): every coherator of an affine algebraic space is naturally the associated \
module of the global sections; carried are a coherator with its adjunction (Stacks 077V(2), \
which the development has only as an existence statement) and the associated-module equivalence \
Mod(A) ≌ QCoh(O_X) of the affine case of Stacks 03DX(2) with its adjunction to global sections"]
def coheratorIsoAssociatedGlobalSections
    (Q : Modules.{u, m} B S hS F hF ⥤ QuasicoherentSheaves.{u, m} B S hS F hF)
    (adjQ : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ Q)
    (hAffine : IsAffineSpace B S hS F) :
    Q ≅ moduleGlobalSectionsSmallEtale.{u, m} B S hS F hF ⋙ assoc.functor :=
  Adjunction.rightAdjointUniq adjQ
    (inclusionAdjunctionGlobalSectionsAssociated B S hS F hF assoc adjAssoc hAffine)

end Affine

end AlgebraicGeometry.Space

end
