module

public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint

/-!
# Rank-one trivializations at a point with no proper open neighbourhood

Let `X` be a scheme and `w` a point of it whose only open neighbourhood is the whole space — the
closed point of the spectrum of a local ring, by
`AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing`. Then the germ map at `⊤` is an
isomorphism, for the structure sheaf and for every `𝒪_X`-module alike: the stalk colimit is
indexed by the open neighbourhoods of `w` and `⊤` is the initial one
(`TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top`). So a module is free of rank one at `w` exactly
when its module of global sections is free of rank one over the ring of global functions, and the
passage between the two statements is the content of this file.

The consumer is the stalk criterion `Stacks.BlowupTwistUnit.isIso_stalk_of_forall_ne`, which asks
for trivializations `F_w ≃ₗ[𝒪_{X,w}] 𝒪_{X,w}` of the two stalks at the centre of a blowup. For
the blowup of a local ring in its maximal ideal the trivializations are computed on global
sections — that is what a theorem about `H⁰` delivers — and the scalars there are `Γ(X, ⊤)`, not
the local ring. Nothing bridges two rings of scalars by itself, so the bridge is made explicit:
`Stacks.BlowupTwistUnit.transportTrivialization` carries a trivialization along a ring
equivalence whose action it matches, and the ring equivalence here is the germ of the structure
sheaf.

## Main definitions

* `Stacks.BlowupTwistUnit.transportTrivialization`: a rank-one trivialization over `R` is one
  over `S`, along a ring equivalence `R ≃+* S` acting the same way.
* `Stacks.BlowupTwistUnit.stalkRingEquivTop`: `Γ(X, ⊤) ≃+* 𝒪_{X,w}` at such a point.
* `Stacks.BlowupTwistUnit.germTopLinearEquiv`: **the germ map `Γ(F, ⊤) ≃ₗ F_w`** at such a
  point, over `Γ(X, ⊤)`.
* `Stacks.BlowupTwistUnit.stalkTrivializationOfSections`: **a rank-one trivialization of the
  global sections gives one of the stalk**, over the local ring.

## Implementation notes

Nothing here needs `F` to be quasi-coherent, and nothing needs `X` to be affine: the argument is
the topological one about the index category of the stalk colimit, so it applies to the structure
sheaf, to any `𝒪_X`-module, and to any presheaf. The quasi-coherence that the blowup argument
does need enters elsewhere, in the localization at the other primes.

The two module structures on a stalk are `Stacks.ModuleStalkSpecialization.stalkModule` over the
local ring and `Stacks.ModuleStalkSpecialization.sectionsStalkModule` over the sections, the
second being the first restricted along the germ. That is exactly the hypothesis
`transportTrivialization` asks for, so it is discharged by `rfl` and no compatibility lemma is
needed.

## References

* [Stacks Project, Tag 01J6](https://stacks.math.columbia.edu/tag/01J6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.BlowupTwistUnit

/-! ### Transport of a trivialization along a ring equivalence -/

/-- **A rank-one trivialization over `R` is one over `S`**, along a ring equivalence
`ρ : R ≃+* S` whose two actions on the module agree.

The underlying map is `ρ ∘ e`. Linearity over `S` is linearity over `R` read through `ρ`: a
scalar `s` acts as `ρ.symm s` does by the hypothesis, and `e` carries that to multiplication by
`ρ.symm s`, which `ρ` returns to multiplication by `s`. -/
def transportTrivialization {R S N : Type*} [CommRing R] [CommRing S] [AddCommGroup N]
    [Module R N] [Module S N] (ρ : R ≃+* S) (hsmul : ∀ (r : R) (n : N), r • n = ρ r • n)
    (e : N ≃ₗ[R] R) : N ≃ₗ[S] S where
  toFun n := ρ (e n)
  map_add' x y := by rw [map_add, map_add]
  map_smul' s n := by
    have h : s • n = ρ.symm s • n := by rw [hsmul, ρ.apply_symm_apply]
    simp only [h, map_smul, smul_eq_mul, map_mul, ρ.apply_symm_apply, RingHom.id_apply]
  invFun s := e.symm (ρ.symm s)
  left_inv n := by
    simp only [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv s := by
    simp only [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-! ### The germ at a point with no proper open neighbourhood -/

variable {X : Scheme.{u}}

/-- **The local ring at a point with no proper open neighbourhood is the ring of global
functions.** This is `TopCat.Presheaf.ΓgermIso` for the structure sheaf, read as a ring
equivalence. -/
def stalkRingEquivTop (w : X) (hw : ∀ V : X.Opens, w ∈ V → V = ⊤) :
    Γ(X, (⊤ : X.Opens)) ≃+* X.presheaf.stalk w :=
  (TopCat.Presheaf.ΓgermIso X.presheaf w hw).commRingCatIsoToRingEquiv

/-- **The germ map on global sections of an `𝒪_X`-module is a linear equivalence onto the stalk**
at a point with no proper open neighbourhood, over `Γ(X, ⊤)`.

The germ map is `Stacks.ModuleStalkSpecialization.germₗ`, which is `Γ(X, ⊤)`-linear by
construction, and it is bijective because `TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top` makes it
an isomorphism of abelian groups. -/
def germTopLinearEquiv (F : X.Modules) (w : X) (hw : ∀ V : X.Opens, w ∈ V → V = ⊤) :
    letI := sectionsStalkModule F (show w ∈ (⊤ : X.Opens) from trivial)
    Γ(F, (⊤ : X.Opens)) ≃ₗ[Γ(X, (⊤ : X.Opens))] F.presheaf.stalk w :=
  letI := sectionsStalkModule F (show w ∈ (⊤ : X.Opens) from trivial)
  LinearEquiv.ofBijective (germₗ F (show w ∈ (⊤ : X.Opens) from trivial))
    (by
      have := TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top F.presheaf w hw
      exact ConcreteCategory.bijective_of_isIso (F.presheaf.Γgerm w))

/-- **A rank-one trivialization of the global sections gives one of the stalk**, at a point with
no proper open neighbourhood.

The sections are the stalk by `Stacks.BlowupTwistUnit.germTopLinearEquiv` and the two rings of
scalars agree by `Stacks.BlowupTwistUnit.stalkRingEquivTop`, so
`Stacks.BlowupTwistUnit.transportTrivialization` applies; the compatibility of the two actions on
the stalk is the definition of
`Stacks.ModuleStalkSpecialization.sectionsStalkModule`. -/
def stalkTrivializationOfSections (F : X.Modules) (w : X)
    (hw : ∀ V : X.Opens, w ∈ V → V = ⊤)
    (e : Γ(F, (⊤ : X.Opens)) ≃ₗ[Γ(X, (⊤ : X.Opens))] Γ(X, (⊤ : X.Opens))) :
    letI := stalkModule F w
    F.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w :=
  letI := stalkModule F w
  letI := sectionsStalkModule F (show w ∈ (⊤ : X.Opens) from trivial)
  transportTrivialization (stalkRingEquivTop w hw) (fun _ _ ↦ rfl)
    ((germTopLinearEquiv F w hw).symm.trans e)

end Stacks.BlowupTwistUnit

end
