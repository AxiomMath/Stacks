module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.RingTheory.Catenary.Basic

/-!
# The affine-local criterion for universal catenarity

A locally Noetherian scheme is universally catenary exactly when the ring of sections over
every affine open is universally catenary.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_iff_forall_affineOpens` characterizes
  universal catenarity of a locally Noetherian scheme by a condition on the rings of sections
  over its affine opens.
* `AlgebraicGeometry.Scheme.ringIsUniversallyCatenary_of_isUniversallyCatenary` and
  `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_affineOpenCover` are its two directions,
  the latter stated for an arbitrary covering by affine opens rather than for all of them.

## Implementation notes

Both directions reduce to the corresponding criterion for catenarity,
`AlgebraicGeometry.isCatenarySpace_tfae`. For the forward direction a finite-type algebra `A`
over `Γ(S, U)` is realized as the source of a locally finite type morphism
`Spec A ⟶ Spec Γ(S, U) ⟶ S`, whose second factor is the open immersion
`IsAffineOpen.fromSpec`; catenarity of `Spec A` as a space is turned back into catenarity of
`A` as a ring by applying the affine-open criterion to the whole of `Spec A`. For the converse
an affine open cover of the source of a locally finite type morphism `f : X ⟶ S` is obtained
by refining the preimages of the affine opens of `S`, and on each piece `Γ(X, V)` is a
finite-type algebra over `Γ(S, U)` by `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`.

## References

* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

namespace AlgebraicGeometry.Scheme

universe u

/-- A ring is catenary as soon as its spectrum is a catenary space. -/
private theorem ringIsCatenary_of_isCatenarySpace_spec {A : Type u} [CommRing A]
    (h : IsCatenarySpace (Spec (CommRingCat.of A))) : Ring.IsCatenary A := by
  have h3 : ∀ V : (Spec (CommRingCat.of A)).affineOpens,
      Ring.IsCatenary Γ(Spec (CommRingCat.of A), V) :=
    ((isCatenarySpace_tfae (Spec (CommRingCat.of A))).out 1 3).mp h
  exact Ring.IsCatenary.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.surjective
    (h3 ⟨⊤, isAffineOpen_top _⟩)

/-- Every open cover of a scheme is refined by a cover by affine opens, indexed by the pairs
consisting of a member of the given cover and an affine open contained in it. -/
private theorem affineCover_refines (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (hU : IsOpenCover U) :
    IsOpenCover (fun j : Σ i : ι, {W : X.affineOpens // W.1 ≤ U i} ↦ (j.2.1 : X.Opens)) := by
  apply IsOpenCover.mk
  apply Opens.ext
  ext x
  constructor
  · intro _
    trivial
  · intro _
    simp only [Opens.coe_iSup, Set.mem_iUnion]
    obtain ⟨i, hix⟩ := hU.exists_mem x
    obtain ⟨W, hWa, hxW, hWle⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U i from hix)
    exact ⟨⟨i, ⟨⟨W, hWa⟩, hWle⟩⟩, hxW⟩

/-- A locally Noetherian scheme is universally catenary as soon as the rings of sections over
the members of one covering by affine opens are universally catenary. -/
theorem isUniversallyCatenary_of_affineOpenCover (S : Scheme.{u}) [IsLocallyNoetherian S]
    {ι : Type u} (U : ι → S.affineOpens) (hU : IsOpenCover fun i => (U i : S.Opens))
    (h : ∀ i, Ring.IsUniversallyCatenary Γ(S, U i)) : IsUniversallyCatenary S := by
  intro X f _
  apply ((isCatenarySpace_tfae X).out 4 1).mp
  refine ⟨Σ i : ι, {V : X.affineOpens // V.1 ≤ f ⁻¹ᵁ (U i).1},
    fun j => j.2.1, ?_, ?_⟩
  · exact affineCover_refines X (fun i => f ⁻¹ᵁ (U i).1) (hU.comap f.base.hom)
  · intro j
    let : Algebra Γ(S, (U j.1).1) Γ(X, j.2.1.1) :=
      (f.appLE (U j.1).1 j.2.1.1 j.2.2).hom.toAlgebra
    let : Algebra.FiniteType Γ(S, (U j.1).1) Γ(X, j.2.1.1) :=
      f.finiteType_appLE (U j.1).2 j.2.1.2 j.2.2
    exact h j.1 Γ(X, j.2.1.1)

/-- The ring of sections over an affine open of a universally catenary locally Noetherian
scheme is universally catenary. -/
theorem ringIsUniversallyCatenary_of_isUniversallyCatenary {S : Scheme.{u}}
    [IsLocallyNoetherian S] (hS : IsUniversallyCatenary S) (U : S.affineOpens) :
    Ring.IsUniversallyCatenary Γ(S, U) := by
  intro A _ _ _
  have h1 : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have h2 : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  exact ringIsCatenary_of_isCatenarySpace_spec
    (hS _ (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) A)) ≫ U.2.fromSpec))

/-- A locally Noetherian scheme is universally catenary if and only if the ring of sections
over each of its affine opens is universally catenary. -/
theorem isUniversallyCatenary_iff_forall_affineOpens (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsUniversallyCatenary S ↔ ∀ U : S.affineOpens, Ring.IsUniversallyCatenary Γ(S, U) :=
  ⟨ringIsUniversallyCatenary_of_isUniversallyCatenary,
    isUniversallyCatenary_of_affineOpenCover S (fun U => U)
      (IsOpenCover.mk (iSup_affineOpens_eq_top S))⟩

end AlgebraicGeometry.Scheme
