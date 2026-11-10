module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasCofibered

/-!
# Base change of a graded algebra, piece by piece

A map of graded algebras exhibits its target as an extension of scalars of its source exactly
when it does so in each degree. This file proves the degreewise criterion for an arbitrary pair
of graded algebras, and applies it to a base-change morphism of the category of graded algebras
finite projective in each degree: the restriction of such a morphism to the `d`-th graded piece
exhibits the `d`-th piece of the target as the extension of scalars of the `d`-th piece of the
source.

## Main definitions

* `Deformation.Examples.ProjectiveGradedAlgebra.homPieceMap`: the restriction of a base-change
  morphism to the `d`-th graded piece.

## Main results

* `Deformation.Examples.isBaseChange_of_graded`: a map of graded algebras is a base change as
  soon as each of its graded pieces is one.
* `Deformation.Examples.ProjectiveGradedAlgebra.homPiece_isBaseChange`: each graded piece of a
  base-change morphism of graded algebras is a base change.

## Implementation notes

The degreewise criterion is proved by transporting `IsBaseChange.directSum` across the two
decomposition equivalences, which is why it asks for the pieces of the target as submodules
restricted to the source base ring rather than as modules over the target base ring: that is
the shape in which the graded pieces of one map assemble into the map itself.

## References

* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace Deformation.Examples

universe u v w m

/-- A map of graded algebras which is a base change in each degree is a base change. -/
public theorem isBaseChange_of_graded
    {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra S B] [Module R B]
    [IsScalarTower R S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : A →ₗ[R] B)
    (ε : ∀ d, 𝒜 d →ₗ[R] (ℬ d).restrictScalars R)
    (hε : ∀ d (a : 𝒜 d), (ε d a).1 = f a.1)
    (hbc : ∀ d, IsBaseChange S (ε d)) : IsBaseChange S f := by
  let eA := (DirectSum.decomposeAlgEquiv 𝒜).toLinearEquiv.symm
  let eB := (DirectSum.decomposeAlgEquiv ℬ).toLinearEquiv.symm
  apply (IsBaseChange.iff_of_equiv_comm eA eB ?_).mp (IsBaseChange.directSum hbc)
  apply DirectSum.linearMap_ext
  intro d
  ext a
  change f ((DirectSum.decomposeAlgEquiv 𝒜).symm (DirectSum.of _ d a)) =
    (DirectSum.decomposeAlgEquiv ℬ).symm (DirectSum.lmap ε (DirectSum.of _ d a))
  rw [DirectSum.lmap_of]
  change f ((DirectSum.decomposeAlgEquiv 𝒜).symm (DirectSum.of _ d a)) =
    (DirectSum.decomposeAlgEquiv ℬ).symm
      (DirectSum.of (fun i => ↥(ℬ i)) d ⟨(ε d a).1, (ε d a).2⟩)
  rw [DirectSum.decomposeAlgEquiv_symm_apply, DirectSum.decompose_symm_of,
    DirectSum.decomposeAlgEquiv_symm_apply]
  change f a.1 = (DirectSum.decompose ℬ).symm
    (DirectSum.of (fun i => ↥(ℬ i)) d ⟨(ε d a).1, (ε d a).2⟩)
  rw [DirectSum.decompose_symm_of ℬ]
  exact (hε d a).symm

namespace ProjectiveGradedAlgebra

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The restriction of a base-change morphism of graded algebras to the `d`-th graded piece. -/
public def homPieceMap
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : ProjectiveGradedAlgebra.Hom X Y) (d : ℕ) :
    letI : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
    letI : Algebra (↑X.base) Y.carrier :=
      ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
    letI : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    X.grading d →ₗ[↑X.base] (Y.grading d).restrictScalars X.base := by
  letI : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  letI : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
  letI : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact {
    toFun := fun x => ⟨g.map x.1, g.map_mem d x.1 x.2⟩
    map_add' := by
      intro x y
      ext
      exact map_add g.map x.1 y.1
    map_smul' := by
      intro r x
      ext
      calc
        g.map (r • x.1) = g.base.hom r • g.map x.1 := g.map_smul r x.1
        _ = algebraMap (↑X.base) Y.carrier r • g.map x.1 := by
          have hscalar : algebraMap (↑Y.base) Y.carrier (g.base.hom r) =
              algebraMap (↑X.base) Y.carrier r := rfl
          simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply, RingHom.id_apply] using
            congrArg (fun s : Y.carrier => s * g.map x.1) hscalar }

/-- Each graded piece of a base-change morphism of graded algebras exhibits the piece of the
target as the extension of scalars of the piece of the source. -/
public theorem homPiece_isBaseChange
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : ProjectiveGradedAlgebra.Hom X Y) (d : ℕ) :
    letI : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
    IsBaseChange (↑Y.base) (homPieceMap g d) := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  let : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e := morphismPushoutEquiv g
  let inc := (X.grading d).subtype.baseChange (↑Y.base)
  have hmem (t : TensorProduct (↑X.base) (↑Y.base) (X.grading d)) :
      e (inc t) ∈ Y.grading d := by
    induction t using TensorProduct.inductionOn with
    | add a b ha hb =>
        rw [map_add, map_add]
        exact (Y.grading d).add_mem ha hb
    | tmul a x =>
        change e (a ⊗ₜ[↑X.base] (x : X.carrier)) ∈ Y.grading d
        rw [morphismPushoutEquiv_tmul]
        exact (Y.grading d).smul_mem a (g.map_mem d x.1 x.2)
  let e' : TensorProduct (↑X.base) (↑Y.base) (X.grading d) →ₗ[↑Y.base]
      (Y.grading d).restrictScalars X.base := {
    toFun := fun t => ⟨e (inc t), hmem t⟩
    map_add' _ _ := Subtype.ext <| by simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      change e (inc (a • x)) = a • e (inc x)
      exact (congrArg e (inc.map_smul a x)).trans (e.toLinearMap.map_smul a (inc x)) }
  let pr : X.carrier →ₗ[↑X.base] X.grading d :=
    (DFinsupp.lapply d).comp (DirectSum.decomposeAlgEquiv X.grading).toLinearMap
  have hc : (pr.baseChange (↑Y.base)).comp inc = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, show pr.comp (X.grading d).subtype = LinearMap.id by
      ext x
      simp [pr, DirectSum.decomposeAlgEquiv], LinearMap.baseChange_id]
  have hinc : Function.Injective inc := fun x y h ↦ by
    simpa only [← LinearMap.comp_apply, hc, LinearMap.id_apply] using
      congrArg (pr.baseChange (↑Y.base)) h
  have hbij : Function.Bijective e' := by
    refine ⟨fun x y h ↦ hinc (e.injective
      (congrArg (fun z : (Y.grading d).restrictScalars X.base => (z : Y.carrier)) h)), fun y ↦ ?_⟩
    obtain ⟨t, ht⟩ := pushout_symm_mem_baseChange g d y.1 y.2
    exact ⟨t, Subtype.ext ((congrArg e ht).trans (e.apply_symm_apply y.1))⟩
  apply IsBaseChange.of_equiv (LinearEquiv.ofBijective e' hbij)
  intro x
  apply Subtype.ext
  change e (inc (1 ⊗ₜ[↑X.base] x)) = g.map x.1
  rw [LinearMap.baseChange_tmul]
  change e (1 ⊗ₜ[↑X.base] (x : X.carrier)) = _
  rw [morphismPushoutEquiv_tmul]
  simp

end ProjectiveGradedAlgebra

end Deformation.Examples
