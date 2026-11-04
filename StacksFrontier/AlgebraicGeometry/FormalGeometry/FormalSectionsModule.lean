module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSections
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Formal sections as a module over the global functions

`Stacks.Algebraization.formalSections` evaluates the quotient tower `n ↦ F / Iⁿ F` on
`U = Spec(A) ∖ V(𝔞)` through `AlgebraicGeometry.Scheme.Modules.toPresheaf`, so it is valued in
`Ab` and its limit — the group of formal sections — is a bare abelian group. Every statement
about formal sections that mentions multiplication by a global function is therefore not merely
unproved but *unstatable* against it: `I · M` is a `Submodule`, and a bare abelian group has no
submodules over a ring.

This file gives the same limit its module structure, by evaluating the tower through
`SheafOfModules.evaluation` into `ModuleCat Γ(U, ⊤)` instead. The two towers differ by
`forget₂ (ModuleCat Γ(U, ⊤)) Ab`, which is the identity on sections and preserves limits, so the
`Ab`-valued limit already used by the comparison map of Stacks 0EG2 is canonically the underlying
group of the `ModuleCat`-valued one; `Stacks.Algebraization.ofFormalSections` transports an
element across that comparison, and `Stacks.Algebraization.π_ofFormalSections` says the transport
changes none of its components.

## Main definitions

* `Stacks.Algebraization.formalSectionsModule` — the tower `n ↦ Γ(U, F / Iⁿ F)` valued in
  `ModuleCat Γ(U, ⊤)`.
* `Stacks.Algebraization.formalSectionsLimitModule` — its limit `M`, an object of
  `ModuleCat Γ(U, ⊤)`; the formal sections of `F` along `U ∩ V(I)` with their module structure.
* `Stacks.Algebraization.formalSectionsLimitComparison` — the comparison of the two limits.
* `Stacks.Algebraization.ofFormalSections` — the induced bijection from the `Ab`-valued limit.
* `Stacks.Algebraization.idealSmulFormalSectionsLimit` — `I · M`, a genuine `Submodule`.

## Main results

* `Stacks.Algebraization.formalSectionsModule_comp_forget₂` — forgetting the module structure of
  the tower returns `formalSections` on the nose.
* `Stacks.Algebraization.π_ofFormalSections` — the transport commutes with the projections of the
  two limits.
* `Stacks.Algebraization.mem_idealSmulFormalSectionsLimit_of_mem` — the generators `r • m` of
  `I · M`, for `r` a global function in the image of `I`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.toPresheaf` is `SheafOfModules.forget` followed by
`PresheafOfModules.toPresheaf`, whose value on an object is the `forget₂`-image of the value of
`PresheafOfModules.evaluation`. So `formalSectionsModule ⋙ forget₂ _ Ab` is `formalSections`
by `rfl`, and `CategoryTheory.Limits.preservesLimitIso` for `forget₂` lands in
`limit (formalSections …)` without an `eqToIso` anywhere. This is what keeps the comparison from
being a transport of a module structure along an `AddEquiv`: the two limits are limits of the
very same diagram, read in two categories.

The ideal of `Γ(U, ⊤)` that multiplies `M` is `Stacks.Cohomology.FormalFunctions.baseIdeal`, the
image of `I` under `A ⟶ Γ(U, 𝒪_U)` — the same ideal whose quasi-coherent extension is the
`Stacks.Algebraization.idealSheafNearVanishing` already dividing the tower, so `I · M` is read
with respect to one ideal and not two.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The tower `n ↦ Γ(U, F / Iⁿ F)` of `Stacks.Algebraization.formalSections`, evaluated through
`SheafOfModules.evaluation` so that each term is a module over the global functions `Γ(U, ⊤)`
rather than a bare abelian group. -/
def formalSectionsModule :
    ℕᵒᵖ ⥤ ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤) :=
  quotientSystemNearVanishing A I a F ⋙ SheafOfModules.evaluation _ (op ⊤)

/-- **Forgetting the module structure of `formalSectionsModule` gives `formalSections`.** The two
towers are the same diagram: `AlgebraicGeometry.Scheme.Modules.toPresheaf` evaluates a sheaf of
modules at an open by taking the `forget₂`-image of `SheafOfModules.evaluation`. -/
theorem formalSectionsModule_comp_forget₂ :
    formalSectionsModule A I a F ⋙
        forget₂ (ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤)) Ab.{u} =
      formalSections A I a F :=
  rfl

/-- The term of `formalSectionsModule` at `n` is the sections of `F / Iⁿ F` on all of `U`. -/
theorem formalSectionsModule_obj (n : ℕᵒᵖ) :
    (formalSectionsModule A I a F).obj n =
      ((quotientSystemNearVanishing A I a F).obj n).val.obj (op ⊤) :=
  rfl

/-- **`M`, the formal sections of `F` along `U ∩ V(I)`, as a module over `Γ(U, ⊤)`.** The limit of
`Stacks.Algebraization.formalSectionsModule`, taken in `ModuleCat Γ(U, ⊤)`. Its underlying
abelian group is the `Ab`-valued `limit (formalSections …)` that the comparison map of Stacks
0EG2 lands in, by `Stacks.Algebraization.formalSectionsLimitComparison`. -/
abbrev formalSectionsLimitModule : ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤) :=
  limit (formalSectionsModule A I a F)

/-- **The comparison of the two limits of formal sections.** The forgetful functor
`forget₂ (ModuleCat Γ(U, ⊤)) Ab` preserves limits and carries `formalSectionsModule` to
`formalSections`, so the underlying abelian group of
`Stacks.Algebraization.formalSectionsLimitModule` is `limit (formalSections …)`. -/
def formalSectionsLimitComparison :
    (forget₂ (ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤)) Ab.{u}).obj
        (formalSectionsLimitModule A I a F) ≅
      limit (formalSections A I a F) :=
  preservesLimitIso _ (formalSectionsModule A I a F)

/-- The comparison `formalSectionsLimitComparison` followed by the `n`-th projection of
`limit (formalSections …)` is the `forget₂`-image of the `n`-th projection of
`formalSectionsLimitModule`. -/
@[reassoc]
theorem formalSectionsLimitComparison_hom_π (n : ℕᵒᵖ) :
    (formalSectionsLimitComparison A I a F).hom ≫ limit.π (formalSections A I a F) n =
      (forget₂ (ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤)) Ab.{u}).map
        (limit.π (formalSectionsModule A I a F) n) :=
  preservesLimitIso_hom_π _ _ n

/-- The inverse of `formalSectionsLimitComparison` followed by the `forget₂`-image of the `n`-th
projection of `formalSectionsLimitModule` is the `n`-th projection of
`limit (formalSections …)`. -/
@[reassoc]
theorem formalSectionsLimitComparison_inv_comp_π (n : ℕᵒᵖ) :
    (formalSectionsLimitComparison A I a F).inv ≫
        (forget₂ (ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤)) Ab.{u}).map
          (limit.π (formalSectionsModule A I a F) n) =
      limit.π (formalSections A I a F) n :=
  (Iso.inv_comp_eq _).2 (formalSectionsLimitComparison_hom_π A I a F n).symm

/-- **A formal section, read as an element of the module `M`.** The image of an element of the
`Ab`-valued `limit (formalSections …)` — where the comparison map of Stacks 0EG2 produces its
elements — under `Stacks.Algebraization.formalSectionsLimitComparison`. It changes no component
of the element, by `Stacks.Algebraization.π_ofFormalSections`. -/
def ofFormalSections (m : ToType (limit (formalSections A I a F))) :
    ToType (formalSectionsLimitModule A I a F) :=
  ConcreteCategory.hom (formalSectionsLimitComparison A I a F).inv m

/-- **The transport to `M` changes no component of a formal section.** -/
theorem π_ofFormalSections (n : ℕᵒᵖ) (m : ToType (limit (formalSections A I a F))) :
    ConcreteCategory.hom (limit.π (formalSectionsModule A I a F) n)
        (ofFormalSections A I a F m) =
      ConcreteCategory.hom (limit.π (formalSections A I a F) n) m :=
  (ConcreteCategory.comp_apply (formalSectionsLimitComparison A I a F).inv
      ((forget₂ (ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤)) Ab.{u}).map
        (limit.π (formalSectionsModule A I a F) n)) m).symm.trans
    (ConcreteCategory.congr_hom (formalSectionsLimitComparison_inv_comp_π A I a F n) m)

/-- `Stacks.Algebraization.ofFormalSections` is a bijection: it is the underlying map of an
isomorphism of abelian groups. -/
theorem bijective_ofFormalSections : Function.Bijective (ofFormalSections A I a F) :=
  (ConcreteCategory.bijective_of_isIso (formalSectionsLimitComparison A I a F).inv)

/-- **`I · M`, a genuine submodule of the formal sections.** The ideal is
`Stacks.Cohomology.FormalFunctions.baseIdeal`, the image of `I` in the global functions of `U`,
and `M` is `Stacks.Algebraization.formalSectionsLimitModule`. This is the submodule that Stacks
0EH8's clause `gᵉ ∉ I·M` is about. -/
def idealSmulFormalSectionsLimit :
    Submodule Γ((complementZeroLocus A a : Scheme), ⊤)
      (ToType (formalSectionsLimitModule A I a F)) :=
  Stacks.Cohomology.FormalFunctions.baseIdeal A I (complementZeroLocus A a).ι • ⊤

/-- The generators of `I · M`: a global function in the image of `I`, times a formal section. -/
theorem mem_idealSmulFormalSectionsLimit_of_mem {r : A} (hr : r ∈ I)
    (m : ToType (formalSectionsLimitModule A I a F)) :
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (complementZeroLocus A a).ι.appTop).hom r • m ∈
      idealSmulFormalSectionsLimit A I a F :=
  Submodule.smul_mem_smul (Stacks.Cohomology.FormalFunctions.mem_baseIdeal A I _ hr) trivial

end Stacks.Algebraization

end
