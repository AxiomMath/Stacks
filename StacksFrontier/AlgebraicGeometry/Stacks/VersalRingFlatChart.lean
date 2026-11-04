module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingChartPoint
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful

/-!
# Stacks 0DR2 at the closed fibre of a complete local object

This file proves the conclusion of **Stacks 0DR2** at one kind of point: the closed fibre
`ξ_0` of the formal object `ξ` that the approximation functor of **Stacks 07X6** attaches to a
complete local object `xR` of `𝒳`, when `ξ` is versal and `xR` is a flat object. This is the
input from a chart used in Step III of the source's proof, where `xR` is the restriction of a
smooth chart `U ⟶ 𝒳` to the spectrum of a completed local ring `𝒪^∧_{U, u₀}`, which is flat over
`U`.

Two identifications are needed. A formal object `ξ` over the site determines a formal object of
the predeformation category of its closed fibre
(`Deformation.Artin.FormalObject.predeformationFormalObject`), and back
(`Deformation.Artin.FormalObject.ofPredeformation`); the round trip is the identity on levels and
transitions, so it returns a formal object isomorphic to `ξ`
(`Deformation.Artin.FormalObject.nonempty_ofPredeformation_predeformationFormalObject_iso`).
Then any realization of the round trip is isomorphic to `xR` itself, by full faithfulness of the
approximation functor (**Stacks 07X8**), so it is flat when `xR` is.

## Main results

* `Deformation.Artin.FormalObject.nonempty_ofPredeformation_predeformationFormalObject_iso`: the
  round trip.
* `AlgebraicGeometry.Stack.exists_flat_realization_closedFibre`: a flat realization of the
  versal formal object at the closed fibre of a versal approximation of a flat complete local
  object.
* `AlgebraicGeometry.Stack.realizationsFlatAt_closedFibre`: the conclusion of Stacks 0DR2 at that
  closed fibre.

## References

* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0CXH](https://stacks.math.columbia.edu/tag/0CXH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- **The round trip from formal objects over the site to formal objects of the predeformation
category and back is the identity up to isomorphism.** The levels and transitions of the formal
object over the site obtained from `ξ.predeformationFormalObject` are those of `ξ`; only the
complete local base is presented differently. -/
theorem FormalObject.nonempty_ofPredeformation_predeformationFormalObject_iso
    (ξ : FormalObject B S hS p) (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ)) :
    Nonempty (FormalObject.ofPredeformation B S hS iΛ p (ξ.level 0) (ξ.basePoint Λ iΛ hR)
      hfinite (ξ.predeformationFormalObject Λ iΛ hR) ≅ ξ) :=
  have h (n : ℕ) : ξ.transition n ≫ 𝟙 _ = 𝟙 _ ≫ ξ.transition n := by simp
  ⟨{ hom := ⟨fun n => 𝟙 (ξ.level n), h⟩
     inv := ⟨fun n => 𝟙 (ξ.level n), h⟩
     hom_inv_id := FormalObject.Hom.ext fun n => Category.comp_id _
     inv_hom_id := FormalObject.Hom.ext fun n => Category.comp_id _ }⟩

end Deformation.Artin

namespace AlgebraicGeometry.Stack

universe u w

variable (D : VersalSituation.{u, w})

/-- **A realization at the closed fibre of a versal approximation of a complete local object,
mapping to it.** Let `xR` be a complete local object of `𝒳`, and suppose that the formal object
`ξ` the approximation functor of Stacks 07X6 attaches to it is versal, relative to an affine open
`Spec Λ ⊆ S` through which the structure morphism of its base factors. Then the formal object of
the predeformation category of the closed fibre `ξ_0` determined by `ξ` has a realization `y`
together with a morphism `y ⟶ xR` lying over a flat morphism of schemes (an isomorphism, by full
faithfulness of the approximation functor, Stacks 07X8). -/
theorem exists_realization_closedFibre_hom
    (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
    (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).obj xR)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property ξ Λ iΛ hΛ) :
    ∃ (hA : D.B.Contains (Spec (.of (ξ.predeformationFormalObject Λ iΛ hΛ).base)))
      (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ
          (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
          (ξ.predeformationFormalObject Λ iΛ hΛ).base) hA),
      Nonempty ((Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p
        (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
        (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
        (ξ.predeformationFormalObject Λ iΛ hΛ)).Realization hA y hy) ∧
      ∃ m : y ⟶ xR.obj.1, Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) := by
  classical
  let hp := D.𝒳.val.property
  let G := Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p hp
  have hfinite := locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ
  let ζ := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p
    (ξ.level 0) (ξ.basePoint Λ iΛ hΛ) hfinite (ξ.predeformationFormalObject Λ iΛ hΛ)
  obtain ⟨J⟩ :=
    Deformation.Artin.FormalObject.nonempty_ofPredeformation_predeformationFormalObject_iso
      ξ Λ iΛ hΛ hfinite
  -- the round trip is effective
  have heff : Deformation.Artin.FormalObject.IsEffective D.B D.S D.hS D.𝒳.val.val.p hp ζ :=
    ⟨xR, ⟨eqToIso hξ.symm ≪≫ J.symm⟩⟩
  obtain ⟨-, hbase, -⟩ := (Deformation.Artin.approximationFunctorData D.B D.S D.hS
    D.𝒳.val.val.p hp).2
  have hA : D.B.Contains (Spec (.of ζ.base.R)) := by
    show D.B.Contains (Spec (.of ξ.base.R))
    rw [hξ, hbase xR]
    exact Deformation.Artin.chosenContains D.B D.S D.hS D.𝒳.val.val.p xR.obj
  obtain ⟨y, hy, ⟨Ry⟩⟩ := Deformation.Artin.FormalObject.exists_realization_of_isEffective
    (hA := hA) hp heff
  -- the realizing object is isomorphic to `xR`
  obtain ⟨I⟩ := Ry.nonempty_approximationIso hp
  obtain ⟨_, _⟩ := Deformation.Artin.fullyFaithful_approximationFunctor_of_isAlgebraicStack
    D.𝒳.val D.𝒳.property
  let L := (Functor.FullyFaithful.ofFullyFaithful G).preimageIso
    (I ≪≫ J ≪≫ eqToIso hξ : G.obj Ry.completeLocalObject ≅ G.obj xR)
  let m : y ⟶ xR.obj.1 := L.hom.1.1
  have hm : IsIso m :=
    ⟨L.inv.1.1, congrArg (fun f => f.1.1) L.hom_inv_id, congrArg (fun f => f.1.1) L.inv_hom_id⟩
  have hmflat : Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) := by
    have h₁ : IsIso (D.𝒳.val.val.p.map m) := inferInstance
    have h₂ : IsIso ((Over.forget _).map (D.𝒳.val.val.p.map m)) := inferInstance
    have : IsIso (D.B.inclusion.map ((Over.forget _).map (D.𝒳.val.val.p.map m))) :=
      inferInstance
    show Flat (D.B.inclusion.map ((Over.forget _).map (D.𝒳.val.val.p.map m)))
    infer_instance
  exact ⟨hA, y, hy, ⟨Ry⟩, m, hmflat⟩


/-- **A flat realization at the closed fibre of a versal approximation of a flat complete local
object.** Let `xR` be a complete local object of `𝒳` which is a flat object, and suppose that the
formal object `ξ` the approximation functor of Stacks 07X6 attaches to it is versal, relative to
an affine open `Spec Λ ⊆ S` through which the structure morphism of its base factors. Then the
formal object of the predeformation category of the closed fibre `ξ_0` determined by `ξ` is
versal (by definition) and has a realization which is a flat object.

The formal object over the site that it determines back is isomorphic to `ξ`, hence effective;
its realization over its own base is isomorphic to `xR` by full faithfulness of the
approximation functor (Stacks 07X8), so it is flat. -/
theorem exists_flat_realization_closedFibre
    (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
    (hxR : flatObject D.B D.S D.hS D.𝒳.val xR.obj.1)
    (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).obj xR)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property ξ Λ iΛ hΛ) :
    ∃ (hA : D.B.Contains (Spec (.of (ξ.predeformationFormalObject Λ iΛ hΛ).base)))
      (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ
          (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
          (ξ.predeformationFormalObject Λ iΛ hΛ).base) hA),
      Nonempty ((Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p
        (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
        (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
        (ξ.predeformationFormalObject Λ iΛ hΛ)).Realization hA y hy) ∧
      flatObject D.B D.S D.hS D.𝒳.val y := by
  obtain ⟨hA, y, hy, Ry, m, hm⟩ := exists_realization_closedFibre_hom D xR ξ hξ Λ iΛ hΛ hversal
  exact ⟨hA, y, hy, Ry, flatObject_of_flat D.B D.S D.hS D.𝒳 m hm hxR⟩

/-- **Stacks 0DR2 at the closed fibre of a versal approximation of a flat complete local
object.** Let `xR` be a complete local object of `𝒳` which is a flat object, and suppose that the
formal object `ξ` the approximation functor of Stacks 07X6 attaches to it is versal. Then every
realization of every versal formal object at the closed fibre `ξ_0` of `ξ`, for every
presentation of `ξ_0`, is a flat object: one flat realization exists
(`AlgebraicGeometry.Stack.exists_flat_realization_closedFibre`) and Step I of the proof of
Stacks 0DR2 (`AlgebraicGeometry.Stack.realizationsFlatAt_of_flatObject`) spreads flatness to all
the others. -/
theorem realizationsFlatAt_closedFibre
    (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
    (hxR : flatObject D.B D.S D.hS D.𝒳.val xR.obj.1)
    (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property).obj xR)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p
      D.𝒳.val.property ξ Λ iΛ hΛ) :
    RealizationsFlatAt D (ξ.level 0) (ResidueField ξ.base.R) := by
  obtain ⟨_, _, _, ⟨Ry⟩, hflat⟩ :=
    exists_flat_realization_closedFibre D xR hxR ξ hξ Λ iΛ hΛ hversal
  exact realizationsFlatAt_of_flatObject D (ξ.level 0) iΛ hiΛ (ξ.basePoint Λ iΛ hΛ) _
    _ hversal Ry hflat

end AlgebraicGeometry.Stack

end
