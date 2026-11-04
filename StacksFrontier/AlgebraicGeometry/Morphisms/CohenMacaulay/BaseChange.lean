module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayFieldChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay morphisms and base change

Let a scheme morphism have locally Noetherian fibres, and base change it along a locally finite
type morphism. Cohen–Macaulayness at a point is preserved by base change. It is reflected when
the original morphism is flat at the image point, or when the base morphism is flat at the
corresponding point.

## Main results

* `AlgebraicGeometry.isCohenMacaulayAt_pullback` gives preservation under base change.
* `AlgebraicGeometry.isCohenMacaulayAt_of_pullback_of_flat` gives reflection for an originally
  flat morphism.
* `AlgebraicGeometry.isCohenMacaulayAt_of_pullback_of_flat_base` gives reflection for a flat
  base morphism at the relevant point.

## Implementation notes

The base change is Mathlib's chosen pullback, with the second projection as the new morphism.
The locally Noetherian fibres needed by the Cohen–Macaulay-at-point predicate are supplied by
`AlgebraicGeometry.isLocallyNoetherian_fiber_pullback`. The three declarations correspond to
parts (1), (2), and (3) of the source lemma, respectively.

The flatness halves rest on
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, which presents the local ring
of a fibre product as a localization of a tensor product, together with the
flat-base-change criterion
`Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization`.
The Cohen–Macaulay halves reduce to the invariance of Cohen–Macaulayness of a local ring under
extension of the ground field,
`AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_baseChange_iff`, whose hypothesis is the
essential-finite-type disjunction rather than finite generation of the extension.

## References

* [Stacks Project, Tag 045T](https://stacks.math.columbia.edu/tag/045T)
-/

@[expose] public section

open CategoryTheory Limits
open RingTheory.Sequence
open IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- Cohen–Macaulayness of a stalk transports along an isomorphism of schemes. -/
private theorem isCohenMacaulayLocalRing_stalk_iso {A B : Scheme.{u}}
    (e : A ≅ B) (x : A)
    [IsNoetherianRing (A.presheaf.stalk x)]
    [IsNoetherianRing (B.presheaf.stalk (e.hom x))]
    [IsLocalRing (A.presheaf.stalk x)]
    [IsLocalRing (B.presheaf.stalk (e.hom x))] :
    IsCohenMacaulayLocalRing (A.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing (B.presheaf.stalk (e.hom x)) := by
  let E := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  rw [isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay,
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay]
  exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv E.symm

/-- The fibre local rings of a morphism and of its base change along a locally finite type
morphism have the same Cohen–Macaulayness. -/
private theorem fiber_stalk_isCohenMacaulay_iff_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (x' : (pullback f g : Scheme.{u}))
    [IsLocallyNoetherian
      ((pullback.snd f g).fiber ((pullback.snd f g) x'))] :
    IsCohenMacaulayLocalRing
        ((f.fiber (f ((pullback.fst f g) x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g) x'))) ↔
      IsCohenMacaulayLocalRing
        (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
          ((pullback.snd f g).asFiber x')) := by
  let pX := pullback.fst f g
  let pY := pullback.snd f g
  let y' := pY x'
  let y := g y'
  have hxy : f (pX x') = y :=
    congrArg (fun k : pullback f g ⟶ Y => k x') pullback.condition
  let eFiber := fiberIsoOfEq f hxy
  let oldPoint := eFiber.hom (f.asFiber (pX x'))
  let F := f.fiberToSpecResidueField y
  let G := Spec.map (g.residueFieldMap y')
  let hpb := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y'
  let e := hpb.isoPullback
  let z := pY.asFiber x'
  let z' := e.hom z
  have hefst : e.hom ≫
      pullback.fst (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y')) =
      pullback.map pY (Y'.fromSpecResidueField y') f
        (Y.fromSpecResidueField (g y')) pX (Spec.map (g.residueFieldMap y')) g
        pullback.condition.symm
        (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y').symm :=
    hpb.isoPullback_hom_fst
  have hFiberι : eFiber.hom ≫ f.fiberι y = f.fiberι (f (pX x')) :=
    fiberIsoOfEq_hom_fiberι f hxy
  have hpoint : oldPoint = pullback.fst F G z' := by
    apply (f.fiberι y).isEmbedding.injective
    have hold : f.fiberι y oldPoint = pX x' := by
      have h := congrArg (fun k => k (f.asFiber (pX x'))) hFiberι
      simpa [oldPoint, Scheme.Hom.fiberι_asFiber] using h
    have hnew : f.fiberι y (pullback.fst F G z') = pX x' := by
      have hm :
          (pullback.map pY (Y'.fromSpecResidueField y') f
            (Y.fromSpecResidueField y) pX G g
            pullback.condition.symm
            (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y').symm) ≫
              f.fiberι y = pY.fiberι y' ≫ pX := by
        change (pullback.map pY (Y'.fromSpecResidueField y') f
          (Y.fromSpecResidueField y) pX G g
          pullback.condition.symm
          (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y').symm) ≫
            pullback.fst f (Y.fromSpecResidueField y) =
          pullback.fst pY (Y'.fromSpecResidueField y') ≫ pX
        dsimp only [pullback.map]
        rw [pullback.lift_fst]
      calc
        f.fiberι y (pullback.fst F G z') =
            ((pullback.fst F G ≫ f.fiberι y) z') := rfl
        _ = ((e.hom ≫ pullback.fst F G ≫ f.fiberι y) z) := rfl
        _ = ((pullback.map pY (Y'.fromSpecResidueField y') f
              (Y.fromSpecResidueField y) pX G g pullback.condition.symm
              (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y').symm ≫
                f.fiberι y) z) := by
          dsimp only [F, G, y]
          exact congrArg (fun k => k z)
            (congrArg (fun k => k ≫ f.fiberι (g y')) hefst)
        _ = (pY.fiberι y' ≫ pX) z := congrArg (fun k => k z) hm
        _ = pX x' := by
          change pX ((pullback.snd f g).fiberι y'
            ((pullback.snd f g).asFiber x')) = pX x'
          rw [Scheme.Hom.fiberι_asFiber]
    exact hold.trans hnew.symm
  let K := Y.residueField y
  let L := Y'.residueField y'
  let _ : Algebra K L := (g.residueFieldMap y').hom.toAlgebra
  have hess : Algebra.EssFiniteType K L :=
    residueField_essFiniteType_of_locallyOfFiniteType g y'
  let _ : IsLocallyNoetherian (f.fiber y) := hf y
  let _ : IsLocallyNoetherian (f.fiber (f (pX x'))) := hf (f (pX x'))
  let _ : IsLocallyNoetherian (pY.fiber y') :=
    isLocallyNoetherian_fiber_pullback f g hf y'
  have he : CommRingCat.ofHom (algebraMap K L) = g.residueFieldMap y' := by
    ext r
    rfl
  have hG : G = Spec.map (CommRingCat.ofHom (algebraMap K L)) := congrArg Spec.map he.symm
  let G₀ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e₀ : pullback F G ≅ pullback F G₀ := pullback.congrHom rfl hG
  have he₀fst : e₀.hom ≫ pullback.fst F G₀ = pullback.fst F G := by
    dsimp [e₀, pullback.congrHom, pullback.map]
    rw [pullback.lift_fst]
    simp
  let eTarget : pY.fiber y' ≅ pullback F G₀ := e.trans e₀
  let z₀ := e₀.hom z'
  have hpoint₀ : pullback.fst F G₀ z₀ = oldPoint :=
    (congrArg (fun k => k z') he₀fst).trans hpoint.symm
  let _ : IsOpenImmersion eTarget.inv := IsOpenImmersion.of_isIso eTarget.inv
  let _ : IsLocallyNoetherian (pullback F G₀) :=
    isLocallyNoetherian_of_isOpenImmersion eTarget.inv
  have hcm : IsCohenMacaulayLocalRing ((f.fiber y).presheaf.stalk oldPoint) ↔
      IsCohenMacaulayLocalRing ((pullback F G₀).presheaf.stalk z₀) :=
    isCohenMacaulayLocalRing_stalk_baseChange_iff
      (k := K) (K := L) (X := f.fiber y) (f := F)
      (x := oldPoint) (x' := z₀) (hx' := hpoint₀) (.inr hess)
  exact (isCohenMacaulayLocalRing_stalk_iso eFiber (f.asFiber (pX x'))).trans
    (hcm.trans (isCohenMacaulayLocalRing_stalk_iso eTarget z).symm)

/-- Over the stalks of a base change, flatness of the first projection at `x'` over the base point
gives flatness of the second projection, and conversely when `g` is flat at the image point. -/
private theorem isFlatAt_pullback_snd_of_isFlatAt_fst_and_converse {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (x' : (pullback f g : Scheme)) :
    (IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') →
      IsFlatAt (pullback.snd f g).toLRSHom.toShHom x') ∧
    (IsFlatAt g.toLRSHom.toShHom ((pullback.snd f g).base x') →
      IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' →
      IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x')) := by
  let pX : pullback f g ⟶ X := pullback.fst f g
  let pY : pullback f g ⟶ Y' := pullback.snd f g
  have hsq : (pX ≫ f).base x' = (pY ≫ g).base x' :=
    congrArg (fun k : pullback f g ⟶ Y => k.base x') pullback.condition
  let R := Y.presheaf.stalk ((pX ≫ f).base x')
  let A := X.presheaf.stalk (pX.base x')
  let B := Y'.presheaf.stalk (pY.base x')
  let C := (pullback f g).presheaf.stalk x'
  let _ : Algebra R A := (f.stalkMap (pX.base x')).hom.toAlgebra
  let _ : Algebra R B :=
    ((eqToHom (congrArg Y.presheaf.stalk hsq)) ≫ g.stalkMap (pY.base x')).hom.toAlgebra
  let _ : Algebra A C := (pX.stalkMap x').hom.toAlgebra
  let _ : Algebra B C := (pY.stalkMap x').hom.toAlgebra
  have hloc := BaseChangeStalk.pullback_stalk_isLocalization f g x'
  dsimp only [pX, pY, R, A, B, C] at hloc
  obtain ⟨φ, hφX, hφY, M, hM⟩ := hloc
  let T := TensorProduct R A B
  let _ : Algebra R T := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra T C := φ.toAlgebra
  let _ : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change (pX.stalkMap x').hom a = φ (Algebra.TensorProduct.includeLeftRingHom a)
    exact (DFunLike.congr_fun hφX a).symm)
  let _ : IsScalarTower B T C := IsScalarTower.of_algebraMap_eq' (by
    ext b
    change (pY.stalkMap x').hom b = φ (Algebra.TensorProduct.includeRight.toRingHom b)
    exact (DFunLike.congr_fun hφY b).symm)
  let _ : Algebra.IsPushout R A B T := TensorProduct.isPushout
  let _ : IsLocalHom (algebraMap A C) := by
    change IsLocalHom (pX.stalkMap x').hom
    infer_instance
  have key := Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization
    (R := R) (S := A) (R' := B) (T := T) (S' := C) (M := A) (M' := C) M
    (Algebra.linearMap A C) (IsBaseChange.linearMap A C)
  refine ⟨fun h => ?_, fun hg h => ?_⟩
  · change (pY.stalkMap x').hom.Flat
    exact RingHom.flat_algebraMap_iff.mpr (key.1 (RingHom.flat_algebraMap_iff.mp h))
  · change (f.stalkMap (pX.base x')).hom.Flat
    exact RingHom.flat_algebraMap_iff.mpr <| key.2 (RingHom.flat_algebraMap_iff.mp h)
      (RingHom.flat_algebraMap_iff.mp <| RingHom.Flat.comp
        (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) hg)

/-- Unfolding `IsCohenMacaulayAt` for `f` and for its base change: both are flatness together with
the same Cohen–Macaulayness of a fibre local ring. -/
private theorem isCohenMacaulayAt_iff_isFlatAt_and {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme)) :
    ∃ P : Prop,
      (Scheme.Hom.IsCohenMacaulayAt f hf ((pullback.fst f g).base x') ↔
        IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') ∧ P) ∧
      (Scheme.Hom.IsCohenMacaulayAt (pullback.snd f g)
          (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x' ↔
        IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' ∧ P) := by
  let _ : IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x')) :=
    isLocallyNoetherian_fiber_pullback f g hf ((pullback.snd f g) x')
  refine ⟨_, ?_, Iff.rfl⟩
  change _ ↔ _ ∧ IsCohenMacaulayLocalRing
    (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
      ((pullback.snd f g).asFiber x'))
  rw [← fiber_stalk_isCohenMacaulay_iff_pullback f g hf x']

/-- **Stacks Project, Tag 045T (1).** Cohen–Macaulayness at a point is preserved under locally
finite-type base change. -/
@[stacks 045T "part (1)", ega "IV 6.8.3" "(iii) CM, h loc fin type"]
public theorem isCohenMacaulayAt_pullback {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme))
    (h : Scheme.Hom.IsCohenMacaulayAt f hf ((pullback.fst f g).base x')) :
    Scheme.Hom.IsCohenMacaulayAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x' := by
  obtain ⟨P, h₁, h₂⟩ := isCohenMacaulayAt_iff_isFlatAt_and f g hf x'
  exact h₂.mpr ⟨(isFlatAt_pullback_snd_of_isFlatAt_fst_and_converse f g x').1 (h₁.mp h).1,
    (h₁.mp h).2⟩

/-- **Stacks Project, Tag 045T (2).** Cohen–Macaulayness descends from a base change when the
original morphism is flat at the point in question. -/
@[stacks 045T "part (2)"]
public theorem isCohenMacaulayAt_of_pullback_of_flat {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme))
    (hflat : IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x'))
    (h : Scheme.Hom.IsCohenMacaulayAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x') :
    Scheme.Hom.IsCohenMacaulayAt f hf ((pullback.fst f g).base x') := by
  obtain ⟨P, h₁, h₂⟩ := isCohenMacaulayAt_iff_isFlatAt_and f g hf x'
  exact h₁.mpr ⟨hflat, (h₂.mp h).2⟩

/-- **Stacks Project, Tag 045T (3).** Cohen–Macaulayness descends from a base change flat at the
relevant base point. -/
@[stacks 045T "part (3)", ega "IV 6.8.3" "(iii) converse, CM"]
public theorem isCohenMacaulayAt_of_pullback_of_flat_base {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme))
    (hflat : IsFlatAt g.toLRSHom.toShHom ((pullback.snd f g).base x'))
    (h : Scheme.Hom.IsCohenMacaulayAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x') :
    Scheme.Hom.IsCohenMacaulayAt f hf ((pullback.fst f g).base x') := by
  obtain ⟨P, h₁, h₂⟩ := isCohenMacaulayAt_iff_isFlatAt_and f g hf x'
  have h' := h₂.mp h
  exact h₁.mpr ⟨(isFlatAt_pullback_snd_of_isFlatAt_fst_and_converse f g x').2 hflat h'.1, h'.2⟩

end AlgebraicGeometry
