module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Residue field points of the slice

Let `x` be an object of `𝒳` over a scheme `U` locally of finite type over a locally Noetherian
scheme `S`, and let `u₀` be a point of `U`. This file describes the field-valued points of the
slice of the big fppf site at `U`: the `l`-valued point `Spec l ⟶ U` underlying a slice object
with base `Spec l`, the canonical point `Spec κ(u₀) ⟶ U` as an object of the slice, the
finiteness of `κ(u₀)` over the residue field of the stalk of `S` below it, and the
change-of-fields situation along `l/κ(u₀)` over that stalk.

These are ingredients of `Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt`
(Stacks 07XG).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

-- `CategoryTheory.Functor.Fiber` is a plain `def`, so a term whose type mentions the underlying
-- object of a fibre -- such as the chosen cartesian lift `c.map f x`, whose source is
-- `(c.obj f x).1` where `(c.sliceFunctor x).obj f` is expected -- is not type-correct at
-- `implicit` transparency. Making it implicit-reducible here is what
-- `StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf` does for the same reason.
attribute [local implicit_reducible]
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.BasedFunctor.comp
  Deformation.changeOfFieldsBasedFunctor

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- The two-Yoneda morphism `(Sch/U)_{fppf} ⟶ 𝒳` attached to an object `x` by a choice of
Cartesian pullbacks is a morphism of categories over `Over S`. -/
public theorem sliceFunctor_comp_post (c : p.ChoiceOfPullbacks) (x : X) :
    c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)) ⋙ (p ⋙ Over.post B.inclusion) =
      Over.forget (p.obj x) ⋙ Over.post B.inclusion := by
  simpa only [Functor.assoc] using
    congrArg (fun q : Over (p.obj x) ⥤ AlgebraicGeometry.BigFppfOver B S hS =>
        q ⋙ Over.post B.inclusion)
      (c.sliceFunctor_comp (⟨x, rfl⟩ : p.Fiber (p.obj x)))

variable (x : X)
variable {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
variable (iΛ : Spec (.of Λ) ⟶ S) (uₗ₀ : Over (p.obj x))
variable (huₗ₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))

/-- The morphism `Spec l ⟶ U` underlying an object of the slice of the site at `U` whose
base is `Spec l`. -/
public abbrev fieldPointMap : Spec (.of l) ⟶ ((p ⋙ Over.post B.inclusion).obj x).left :=
  eqToHom (congrArg Over.left huₗ₀).symm ≫ ((Over.post B.inclusion).map uₗ₀.hom).left

/-- The morphism `Spec l ⟶ U` underlying a field-valued point of the slice at `U` composes
with the structure morphism of `U` to the given morphism `Spec l ⟶ S`. -/
public theorem fieldPointMap_comp_hom :
    fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let q := Over.forget (p.obj x) ⋙ Over.post B.inclusion
  have hcomm : ((Over.post B.inclusion).map uₗ₀.hom).left ≫ U.hom =
      (q.obj uₗ₀).hom := by
    simpa [q, U] using (Over.post B.inclusion).map uₗ₀.hom |>.w
  calc
    fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ ≫ U.hom =
        eqToHom (congrArg Over.left huₗ₀).symm ≫
          (((Over.post B.inclusion).map uₗ₀.hom).left ≫ U.hom) := by
            rfl
    _ = eqToHom (congrArg Over.left huₗ₀).symm ≫ (q.obj uₗ₀).hom := by rw [hcomm]
    _ = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
      let e : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) ⟶ q.obj uₗ₀ :=
        eqToHom huₗ₀.symm
      have he : e.left = eqToHom (congrArg Over.left huₗ₀).symm := by
        simp [e, Over.eqToHom_left]
      rw [← he]
      exact e.w

/-- The canonical morphism `Spec κ(y) ⟶ Y` from the spectrum of the residue field at a point
`y` is quasi-compact. -/
public theorem fromSpecResidueField_quasiCompact
    {Y : Scheme.{u}} (y : Y) :
    QuasiCompact (Y.fromSpecResidueField y) := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  exact (Set.toFinite (Y.fromSpecResidueField y ⁻¹' (V : Set Y))).isCompact

/-- For a point `u₀` of the scheme `U` underlying `x`, the spectrum of the residue field `κ(u₀)`
lies in the big site: `Spec κ(u₀) ⟶ U` is a quasi-compact monomorphism, so `Spec κ(u₀)` is no
larger than `U`. -/
public theorem residueFieldPoint_site_contains
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left) :
    B.Contains (Spec (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)) := by
  let Usite := (p.obj x).left
  let U := B.inclusion.obj Usite
  let u₀' : U := u₀
  let f := U.fromSpecResidueField u₀'
  have : IsPreimmersion f := by
    show IsPreimmersion (Spec.map (U.residue u₀') ≫ U.fromSpecStalk u₀')
    rw [IsPreimmersion.comp_iff]
    infer_instance
  have hmono : Mono f := SurjectiveOnStalks.mono_of_injective f.isEmbedding.injective
  have hqc : QuasiCompact f :=
    fromSpecResidueField_quasiCompact u₀
  exact lt_of_le_of_lt (@Scheme.size_le_of_mono_quasiCompact _ _ f hmono hqc)
    Usite.property

/-- The canonical morphism `Spec κ(u₀) ⟶ U`, for a point `u₀` of the scheme `U` underlying `x`,
as an object of the slice of the site at `U`. -/
public noncomputable def residueFieldSlicePoint
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hκ : B.Contains (Spec (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) :
    Over (p.obj x) := by
  let Usite := (p.obj x).left
  let U := B.inclusion.obj Usite
  let u₀' : U := u₀
  let V := B.obj hκ
  let m : V ⟶ Usite := B.inclusion.preimage (U.fromSpecResidueField u₀')
  let W : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (m ≫ (p.obj x).hom)
  exact Over.mk (Over.homMk (U := W) (V := p.obj x) m rfl)

theorem residueFieldSlicePoint_base_eq_stalk
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hκ : B.Contains (Spec (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) :
    let U := (p ⋙ Over.post B.inclusion).obj x
    let k := U.left.residueField u₀
    let S' := B.inclusion.obj (B.obj hS)
    let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
    let R := S'.presheaf.stalk (g (IsLocalRing.closedPoint k))
    letI : Algebra R k := (Scheme.stalkClosedPointTo g).hom.toAlgebra
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj
      (residueFieldSlicePoint B S hS p x u₀ hκ) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫
          S'.fromSpecStalk (g (IsLocalRing.closedPoint k))) := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let k := U.left.residueField u₀
  let S' := B.inclusion.obj (B.obj hS)
  let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
  let R := S'.presheaf.stalk (g (IsLocalRing.closedPoint k))
  let : Algebra R k := (Scheme.stalkClosedPointTo g).hom.toAlgebra
  let Usite := (p.obj x).left
  let V := B.obj hκ
  let m : V ⟶ Usite := B.inclusion.preimage (U.left.fromSpecResidueField u₀)
  show Over.mk
      (B.inclusion.map m ≫ U.hom) =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫
      S'.fromSpecStalk (g (IsLocalRing.closedPoint k)))
  congr 1
  rw [show B.inclusion.map m = U.left.fromSpecResidueField u₀ by
    dsimp [m]
    exact B.inclusion.map_preimage _]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g).symm

theorem residueFieldPoint_comp_hom
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    [Algebra (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l]
    (hfieldPoint : fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ =
      Spec.map (CommRingCat.ofHom (algebraMap
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l)) ≫
          ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀) :
    Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l)) ≫
        ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom := by
  calc
    _ = fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom :=
          (fieldPointMap_comp_hom B S hS p x iΛ uₗ₀ huₗ₀).symm
    _ = _ := by
      rw [hfieldPoint]
      simp [Category.assoc]

theorem residueFieldMap_finiteType
    (hU : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    let U := (p ⋙ Over.post B.inclusion).obj x
    let k := U.left.residueField u₀
    let g : Spec (.of k) ⟶ B.inclusion.obj (B.obj hS) :=
      U.left.fromSpecResidueField u₀ ≫ U.hom
    LocallyOfFiniteType g ∧ QuasiCompact g := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let k := U.left.residueField u₀
  let g : Spec (.of k) ⟶ B.inclusion.obj (B.obj hS) :=
    U.left.fromSpecResidueField u₀ ≫ U.hom
  let : LocallyOfFiniteType (U.left.fromSpecResidueField u₀) := hu₀.1
  let : QuasiCompact (U.left.fromSpecResidueField u₀) := hu₀.2
  let : LocallyOfFiniteType U.hom := hU
  exact ⟨inferInstance, inferInstance⟩

private theorem finite_residueFieldExtension_over_image
    (hU : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    let U := (p ⋙ Over.post B.inclusion).obj x
    let S' := B.inclusion.obj (B.obj hS)
    let k := U.left.residueField u₀
    let g := U.left.fromSpecResidueField u₀ ≫ U.hom
    let q := Scheme.SpecToEquivOfField k S' g
    letI : Algebra (S'.residueField q.1) k := q.2.hom.toAlgebra
    Module.Finite (S'.residueField q.1) k := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let S' := B.inclusion.obj (B.obj hS)
  let k := U.left.residueField u₀
  let g := U.left.fromSpecResidueField u₀ ≫ U.hom
  let q := Scheme.SpecToEquivOfField k S' g
  have hft : LocallyOfFiniteType g ∧ QuasiCompact g := by
    simpa [U, S', g] using residueFieldMap_finiteType B S hS p x hU u₀ hu₀
  let : Algebra (S'.residueField q.1) k := q.2.hom.toAlgebra
  obtain ⟨V, hV, y, hy, hclosed, hfinite⟩ :=
    ((AlgebraicGeometry.finiteType_specField_tfae g).out 2 4).mp hft.1
  exact hfinite

theorem finite_residueField_over_localRing
    (hU : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    let U := (p ⋙ Over.post B.inclusion).obj x
    let S' := B.inclusion.obj (B.obj hS)
    let k := U.left.residueField u₀
    let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
    let q := Scheme.SpecToEquivOfField k S' g
    let R := S'.presheaf.stalk (g (IsLocalRing.closedPoint k))
    let K := S'.residueField (g (IsLocalRing.closedPoint k))
    letI : Algebra R K := (S'.residue (g (IsLocalRing.closedPoint k))).hom.toAlgebra
    letI : Algebra K k := q.2.hom.toAlgebra
    letI : Algebra R k := (Scheme.stalkClosedPointTo g).hom.toAlgebra
    letI : IsScalarTower R K k := IsScalarTower.of_algebraMap_eq' (by
      change (q.2.hom.comp (S'.residue (g (IsLocalRing.closedPoint k))).hom) =
        (Scheme.stalkClosedPointTo g).hom
      exact congrArg CommRingCat.Hom.hom (S'.residue_descResidueField
        (Scheme.stalkClosedPointTo g)))
    Module.Finite R k := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let S' := B.inclusion.obj (B.obj hS)
  let k := U.left.residueField u₀
  let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
  let q := Scheme.SpecToEquivOfField k S' g
  let R := S'.presheaf.stalk (g (IsLocalRing.closedPoint k))
  let K := S'.residueField (g (IsLocalRing.closedPoint k))
  let : Algebra R K := (S'.residue (g (IsLocalRing.closedPoint k))).hom.toAlgebra
  let : Algebra K k := q.2.hom.toAlgebra
  let : Algebra R k := (Scheme.stalkClosedPointTo g).hom.toAlgebra
  let : IsScalarTower R K k := IsScalarTower.of_algebraMap_eq' (by
    show (q.2.hom.comp (S'.residue (g (IsLocalRing.closedPoint k))).hom) =
      (Scheme.stalkClosedPointTo g).hom
    exact congrArg CommRingCat.Hom.hom (S'.residue_descResidueField
      (Scheme.stalkClosedPointTo g)))
  let : Module.Finite R K := by
    show Module.Finite R (IsLocalRing.ResidueField R)
    infer_instance
  have hK : Module.Finite K k :=
    finite_residueFieldExtension_over_image B S hS p x hU u₀ hu₀
  exact Module.Finite.trans K k

theorem stalk_map_fieldExtension
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    (gk : Spec (.of k) ⟶ S) :
    let z : Spec (.of k) := IsLocalRing.closedPoint k
    let R := S.presheaf.stalk (gk z)
    let gl := Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ gk
    letI : Algebra R k := (Scheme.stalkClosedPointTo gk).hom.toAlgebra
    letI : Algebra R l := ((algebraMap k l).comp (algebraMap R k)).toAlgebra
    letI : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' (by rfl)
    Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫
      S.fromSpecStalk (gk z) = gl := by
  let z : Spec (.of k) := IsLocalRing.closedPoint k
  let R := S.presheaf.stalk (gk z)
  let gl := Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ gk
  let : Algebra R k := (Scheme.stalkClosedPointTo gk).hom.toAlgebra
  let : Algebra R l := ((algebraMap k l).comp (algebraMap R k)).toAlgebra
  let : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' (by rfl)
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R l)) =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [IsScalarTower.algebraMap_eq R k l]
    rw [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
  have hfactor :
      Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ S.fromSpecStalk (gk z) = gk := by
    show Spec.map (Scheme.stalkClosedPointTo gk) ≫ S.fromSpecStalk (gk z) = gk
    simpa [z] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk gk
  calc
    Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ S.fromSpecStalk
        (gk z) =
      Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫
          S.fromSpecStalk (gk z)) := by
            rw [hmap]
            rfl
    _ = gl := by
      calc
        _ = Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ gk :=
          congrArg (fun f => Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫ f) hfactor
        _ = gl := rfl

noncomputable def stalkChangeOfFieldsSituation
    [IsLocallyNoetherian S] (hU : LocallyOfFiniteType
      ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    [Algebra (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l]
    [Module.Finite (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l] :
    let U := (p ⋙ Over.post B.inclusion).obj x
    let S' := B.inclusion.obj (B.obj hS)
    let k := U.left.residueField u₀
    let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
    Deformation.ChangeOfFieldsSituation.{u, u, u} := by
  let U := (p ⋙ Over.post B.inclusion).obj x
  let S' := B.inclusion.obj (B.obj hS)
  let k := U.left.residueField u₀
  let g : Spec (.of k) ⟶ S' := U.left.fromSpecResidueField u₀ ≫ U.hom
  let R := S'.presheaf.stalk (g (IsLocalRing.closedPoint k))
  have hS' : S' = S := rfl
  letI : IsLocallyNoetherian S' := hS'.symm ▸ ‹IsLocallyNoetherian S›
  letI : IsNoetherianRing R := inferInstance
  letI : Algebra R k := (Scheme.stalkClosedPointTo g).hom.toAlgebra
  letI : Module.Finite R k := finite_residueField_over_localRing B S hS p x hU u₀ hu₀
  letI : Algebra R l := ((algebraMap k l).comp (algebraMap R k)).toAlgebra
  letI : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' (by rfl)
  exact { Λ := R, k := k, l := l }

attribute [local instance] PredeformationConstruction.category

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  InducedPredeformationFunctor.toBasedFunctor

/-- The image in schemes of the chosen pullback morphism of `x` along `uₗ₀`, read from `Spec l`
through the cast `hx₀`, is `fieldPointMap`. -/
public theorem chosenPullback_fieldPointMap
    (c : p.ChoiceOfPullbacks)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)) :
    eqToHom (congrArg Over.left hx₀).symm ≫
      ((p ⋙ Over.post B.inclusion).map
        (c.map uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left =
      fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ := by
  let := c.isStronglyCartesian uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  have hm := IsHomLift.fac' p uₗ₀.hom
    (c.map uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))
  simp [Functor.comp_map, hm, Over.comp_left, Over.eqToHom_left, fieldPointMap]

/-- At the slice object `residueFieldSlicePoint`, `fieldPointMap` is the canonical morphism
`Spec κ(u₀) ⟶ U`. -/
public theorem residueFieldSlicePoint_fieldPointMap
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hκ : B.Contains (Spec (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)))
    [Algebra Λ (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)]
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj
        (residueFieldSlicePoint B S hS p x u₀ hκ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) ≫ iΛ)) :
    fieldPointMap B S hS p x iΛ (residueFieldSlicePoint B S hS p x u₀ hκ) huκ =
      ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ := by
  show (𝟙 _) ≫ B.inclusion.map (B.inclusion.preimage
    (X := B.obj hκ) (Y := (p.obj x).left)
    (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀)) = _
  simpa only [Category.id_comp] using
    B.inclusion.map_preimage (X := B.obj hκ) (Y := (p.obj x).left)
      (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀)

theorem map_pointMorphism_base
    {Y : Type*} [Category Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S) (F : Y ⥤ Z)
    (hF : F ⋙ qZ = qY) {y₀ y₁ : Y} (η : y₁ ⟶ y₀)
    {K L : Scheme.{u}} {gk : K ⟶ S} {gl : L ⟶ S}
    (h₀ : qY.obj y₀ = Over.mk gk) (h₁ : qY.obj y₁ = Over.mk gl)
    (h₀' : qZ.obj (F.obj y₀) = Over.mk gk)
    (h₁' : qZ.obj (F.obj y₁) = Over.mk gl) :
    eqToHom (congrArg Over.left h₁').symm ≫ (qZ.map (F.map η)).left ≫
      eqToHom (congrArg Over.left h₀') =
    eqToHom (congrArg Over.left h₁).symm ≫ (qY.map η).left ≫
      eqToHom (congrArg Over.left h₀) := by
  subst qY
  rfl

/-- If `fieldPointMap` factors as `e : Spec l ⟶ K` followed by the structure morphism of an
object `v₀` of the slice at `U` lying over `gk : K ⟶ S`, then some arrow `δ : uₗ₀ ⟶ v₀` of the
slice has underlying morphism of schemes `e`. -/
public theorem exists_sliceArrow_of_fieldPointMap
    {K : Scheme.{u}} (gk : K ⟶ S) (v₀ : Over (p.obj x))
    (hv₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj v₀ = Over.mk gk)
    (e : Spec (.of l) ⟶ K)
    (he : e ≫ gk = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)
    (hpoint : fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ =
      e ≫ eqToHom (congrArg Over.left hv₀).symm ≫
        ((Over.post B.inclusion).map v₀.hom).left) :
    ∃ δ : uₗ₀ ⟶ v₀,
      eqToHom (congrArg Over.left huₗ₀).symm ≫
        ((Over.post B.inclusion).map δ.left).left ≫
          eqToHom (congrArg Over.left hv₀) = e := by
  let Q : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let : Q.Full := inferInstanceAs ((Over.post (X := B.obj hS) B.inclusion).Full)
  let : Q.Faithful := inferInstanceAs ((Over.post (X := B.obj hS) B.inclusion).Faithful)
  let a : Q.obj uₗ₀.left ⟶ Q.obj v₀.left :=
    eqToHom huₗ₀ ≫ Over.homMk (V := Over.mk gk) e he ≫ eqToHom hv₀.symm
  let f := Q.preimage a
  have hf : Q.map f = a := Q.map_preimage a
  have hw : f ≫ v₀.hom = uₗ₀.hom := by
    apply Q.map_injective
    apply Over.OverMorphism.ext
    simp only [Functor.map_comp, Over.comp_left, hf]
    apply (cancel_epi (eqToHom (congrArg Over.left huₗ₀).symm)).mp
    simp only [a, Over.comp_left, Over.eqToHom_left, Over.homMk_left, Category.assoc,
      eqToHom_trans_assoc]
    simpa only [eqToHom_refl, Category.id_comp, fieldPointMap, Category.assoc] using
      hpoint.symm
  refine ⟨Over.homMk f hw, ?_⟩
  show eqToHom _ ≫ (Q.map f).left ≫ eqToHom _ = e
  rw [hf]
  simp [a, Over.comp_left, Over.eqToHom_left]

end Deformation.Artin

end
