module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Gorenstein morphisms and base change

Let a morphism of schemes have locally Noetherian fibres, and base change it along a morphism
locally of finite type. Gorensteinness at a point is preserved by such a base change. It is
reflected when the original morphism is flat at the image point, and also when the base morphism
is flat at the corresponding point of the new base.

When instead the *original* morphism is flat and locally of finite type, no finiteness is needed
of the base morphism at all: the Gorenstein locus of such a morphism commutes with arbitrary base
change.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_pullback` gives preservation under base change.
* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_of_pullback_of_flat` gives reflection for an
  originally flat morphism.
* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_of_pullback_of_flat_base` gives reflection for a
  base morphism flat at the relevant point.
* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_pullback_and` collects the three as one statement.
* `AlgebraicGeometry.Scheme.Hom.setOf_isGorensteinAt_pullback_eq_preimage` identifies the
  Gorenstein locus of an arbitrary base change of a flat morphism locally of finite type with the
  inverse image of the Gorenstein locus of that morphism.

## Implementation notes

The base change is Mathlib's chosen pullback, with the second projection as the new morphism.
The locally Noetherian fibres that the Gorenstein-at-a-point predicate requires are supplied by
`AlgebraicGeometry.isLocallyNoetherian_fiber_pullback`; the standing hypothesis is local
Noetherianity of the fibres of the original morphism only, never of its source or target.

Part (1) does not assume the original morphism flat at the point, so the two reflection
statements keep their own flatness hypotheses rather than being folded into one.

Both halves of the Gorenstein-at-a-point predicate move across the square independently, and
each is an equivalence, so all three parts are assembled from two lemmas. The fibre half is
`AlgebraicGeometry.Scheme.Hom.fiber_stalk_isGorenstein_iff_pullback`, which identifies the fibre
of the base change over a point `y'` with the base change of the fibre over the image of `y'`
along the residue field extension, finitely generated because the base morphism is locally of
finite type, and then applies the invariance of Gorensteinness of a local ring under such an
extension of the ground field. The flatness half rests on
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, which presents the local ring
of a fibre product as a localization of a tensor product, together with the flat-base-change
criterion
`Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization`.

For an arbitrary base change the residue field extension is no longer finitely generated, so the
fibre half is redone through the other half of Tag 0C03,
`AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType`, which allows an
arbitrary extension of the ground field at the price of the fibre being locally of finite type
over it — which it is, because the original morphism is. The flatness half is then free in both
directions, since flatness of the original morphism and of its base change are both hypotheses
rather than conclusions.

That a fibre is locally of finite type over its residue field is the instance
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`, and its local
Noetherianity follows from that instance. The two locally Noetherian hypotheses of the Gorenstein
locus statement are arguments, exactly as for the three parts of Tag 0C07 above, and both are
discharged this way, so the statement is never vacuous.

## References

* [Stacks Project, Tag 0C07](https://stacks.math.columbia.edu/tag/0C07)
* [Stacks Project, Tag 0E0Q](https://stacks.math.columbia.edu/tag/0E0Q)
* [Stacks Project, Tag 0C03](https://stacks.math.columbia.edu/tag/0C03)
* [Stacks Project, Tag 038R](https://stacks.math.columbia.edu/tag/038R)
* [Stacks Project, Tag 00MQ](https://stacks.math.columbia.edu/tag/00MQ)
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Gorensteinness of a stalk transports along an isomorphism of schemes. -/
private theorem isGorensteinLocalRing_stalk_iso {A B : Scheme.{u}} (e : A ≅ B) (x : A)
    [IsNoetherianRing (A.presheaf.stalk x)]
    [IsNoetherianRing (B.presheaf.stalk (e.hom x))]
    [IsLocalRing (A.presheaf.stalk x)]
    [IsLocalRing (B.presheaf.stalk (e.hom x))] :
    Dualizing.IsGorensteinLocalRing (A.presheaf.stalk x) ↔
      Dualizing.IsGorensteinLocalRing (B.presheaf.stalk (e.hom x)) :=
  Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- The point of the fibre of `f` over `g y'` corresponding to `x'` is the image of the point of
the fibre of the base change over `y'` under the identification of the latter with the base change
of the former along the residue field extension. -/
private theorem fiberIsoOfEq_asFiber_eq_fst {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (x' : (pullback f g : Scheme.{u})) (hxy : f (pullback.fst f g x') = g (pullback.snd f g x')) :
    (fiberIsoOfEq f hxy).hom (f.asFiber (pullback.fst f g x')) =
      pullback.fst (f.fiberToSpecResidueField (g (pullback.snd f g x')))
        (Spec.map (g.residueFieldMap (pullback.snd f g x')))
        ((isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g)
          (pullback.snd f g x')).isoPullback.hom ((pullback.snd f g).asFiber x')) := by
  let pX := pullback.fst f g
  let pY := pullback.snd f g
  let y' := pY x'
  let y := g y'
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
        (g.SpecMap_residueFieldMap_fromSpecResidueField y').symm :=
    hpb.isoPullback_hom_fst
  have hFiberι : eFiber.hom ≫ f.fiberι y = f.fiberι (f (pX x')) :=
    fiberIsoOfEq_hom_fiberι f hxy
  apply (f.fiberι y).isEmbedding.injective
  have hold : f.fiberι y oldPoint = pX x' := by
    have h := congrArg (fun k => k (f.asFiber (pX x'))) hFiberι
    simpa [oldPoint, Scheme.Hom.fiberι_asFiber] using h
  have hnew : f.fiberι y (pullback.fst F G z') = pX x' := by
    have hm :
        (pullback.map pY (Y'.fromSpecResidueField y') f
          (Y.fromSpecResidueField y) pX G g
          pullback.condition.symm
          (g.SpecMap_residueFieldMap_fromSpecResidueField y').symm) ≫
            f.fiberι y = pY.fiberι y' ≫ pX := by
      show (pullback.map pY (Y'.fromSpecResidueField y') f
        (Y.fromSpecResidueField y) pX G g
        pullback.condition.symm
        (g.SpecMap_residueFieldMap_fromSpecResidueField y').symm) ≫
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
            (g.SpecMap_residueFieldMap_fromSpecResidueField y').symm ≫
              f.fiberι y) z) := by
        dsimp only [F, G, y]
        exact congrArg (fun k => k z)
          (congrArg (fun k => k ≫ f.fiberι (g y')) hefst)
      _ = (pY.fiberι y' ≫ pX) z := by rw [hm]; rfl
      _ = pX x' := by
        show pX ((pullback.snd f g).fiberι y'
          ((pullback.snd f g).asFiber x')) = pX x'
        rw [Scheme.Hom.fiberι_asFiber]
  exact hold.trans hnew.symm

/-- The fibre local rings of a morphism and of its base change along a morphism locally of finite
type have the same Gorensteinness. -/
private theorem fiber_stalk_isGorenstein_iff_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (x' : (pullback f g : Scheme.{u}))
    [IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x'))] :
    Dualizing.IsGorensteinLocalRing
        ((f.fiber (f ((pullback.fst f g) x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g) x'))) ↔
      Dualizing.IsGorensteinLocalRing
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
  have hpoint : oldPoint = pullback.fst F G z' := fiberIsoOfEq_asFiber_eq_fst f g x' hxy
  let K := Y.residueField y
  let L := Y'.residueField y'
  let _ : Algebra K L := (g.residueFieldMap y').hom.toAlgebra
  let _ : Algebra.EssFiniteType K L :=
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
  let _ : IsLocallyNoetherian (pullback F G₀) :=
    (AlgebraicGeometry.isLocallyNoetherian_baseChange_iff K L (f.fiber y) F).mp inferInstance
  have hgor : Dualizing.IsGorensteinLocalRing ((f.fiber y).presheaf.stalk oldPoint) ↔
      Dualizing.IsGorensteinLocalRing ((pullback F G₀).presheaf.stalk z₀) :=
    AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_essFiniteType_fieldExtension
      K L (f.fiber y) F oldPoint z₀ hpoint₀
  have hOld := isGorensteinLocalRing_stalk_iso eFiber (f.asFiber (pX x'))
  have hNew := isGorensteinLocalRing_stalk_iso eTarget z
  exact hOld.trans (hgor.trans hNew.symm)

/-- Flatness at a point passes both ways across the base-change square: it ascends from the
original morphism to its base change, and, when the base morphism is flat at the relevant point,
it descends again. -/
private theorem isFlatAt_pullback_snd_and {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (x' : (pullback f g : Scheme.{u})) :
    (IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') →
        IsFlatAt (pullback.snd f g).toLRSHom.toShHom x') ∧
      (IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' →
        IsFlatAt g.toLRSHom.toShHom ((pullback.snd f g).base x') →
        IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x')) := by
  let pX : pullback f g ⟶ X := pullback.fst f g
  let pY : pullback f g ⟶ Y' := pullback.snd f g
  let x : X := pX.base x'
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
  have hloc := AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g x'
  dsimp only [pX, pY, R, A, B, C] at hloc
  obtain ⟨φ, hφX, hφY, M, hM⟩ := hloc
  let T := TensorProduct R A B
  let _ : Algebra R T := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra T C := φ.toAlgebra
  let _ : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    show (pX.stalkMap x').hom a = φ (Algebra.TensorProduct.includeLeftRingHom a)
    exact (DFunLike.congr_fun hφX a).symm)
  let _ : IsScalarTower B T C := IsScalarTower.of_algebraMap_eq' (by
    ext b
    show (pY.stalkMap x').hom b = φ (Algebra.TensorProduct.includeRight.toRingHom b)
    exact (DFunLike.congr_fun hφY b).symm)
  let _ : Algebra.IsPushout R A B T := TensorProduct.isPushout
  let fAC : A →ₗ[A] C := Algebra.linearMap A C
  have hbc : IsBaseChange C fAC := IsBaseChange.linearMap A C
  let _ : IsLocalHom (algebraMap A C) := by
    show IsLocalHom (pX.stalkMap x').hom
    infer_instance
  have hcrit :=
    Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization
      (R := R) (S := A) (R' := B) (T := T) (S' := C) (M := A) (M' := C) M fAC hbc
  constructor
  · intro hup
    have hflatA : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hup
    show (pY.stalkMap x').hom.Flat
    exact RingHom.flat_algebraMap_iff.mpr (hcrit.1 hflatA)
  · intro hdownC hdownB
    have hflatC : Module.Flat B C := RingHom.flat_algebraMap_iff.mp hdownC
    have hflatB : Module.Flat R B := RingHom.flat_algebraMap_iff.mp <|
      RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) hdownB
    show (f.stalkMap x).hom.Flat
    exact RingHom.flat_algebraMap_iff.mpr (hcrit.2 hflatC hflatB)

/-- **Stacks Project, Tag 0C07 (1).** Gorensteinness at a point is preserved under a base change
locally of finite type. -/
@[stacks 0C07 "part (1)"]
public theorem isGorensteinAt_pullback {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme.{u}))
    (h : IsGorensteinAt f hf ((pullback.fst f g).base x')) :
    IsGorensteinAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x' := by
  let _ : IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x')) :=
    isLocallyNoetherian_fiber_pullback f g hf ((pullback.snd f g) x')
  change IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') ∧
      Dualizing.IsGorensteinLocalRing
        ((f.fiber (f ((pullback.fst f g).base x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g).base x'))) at h
  show IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' ∧
      Dualizing.IsGorensteinLocalRing
        (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
          ((pullback.snd f g).asFiber x'))
  exact ⟨(isFlatAt_pullback_snd_and f g x').1 h.1,
    (fiber_stalk_isGorenstein_iff_pullback f g hf x').mp h.2⟩

/-- **Stacks Project, Tag 0C07 (2).** Gorensteinness descends from a base change locally of
finite type when the original morphism is flat at the point in question. -/
@[stacks 0C07 "part (2)"]
public theorem isGorensteinAt_of_pullback_of_flat {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme.{u}))
    (hflat : IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x'))
    (h : IsGorensteinAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x') :
    IsGorensteinAt f hf ((pullback.fst f g).base x') := by
  let _ : IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x')) :=
    isLocallyNoetherian_fiber_pullback f g hf ((pullback.snd f g) x')
  change IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' ∧
      Dualizing.IsGorensteinLocalRing
        (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
          ((pullback.snd f g).asFiber x')) at h
  show IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') ∧
      Dualizing.IsGorensteinLocalRing
        ((f.fiber (f ((pullback.fst f g).base x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g).base x')))
  exact ⟨hflat, (fiber_stalk_isGorenstein_iff_pullback f g hf x').mpr h.2⟩

/-- **Stacks Project, Tag 0C07 (3).** Gorensteinness descends from a base change locally of
finite type that is flat at the image of the point in the new base. -/
@[stacks 0C07 "part (3)"]
public theorem isGorensteinAt_of_pullback_of_flat_base {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme.{u}))
    (hflat : IsFlatAt g.toLRSHom.toShHom ((pullback.snd f g).base x'))
    (h : IsGorensteinAt (pullback.snd f g)
      (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x') :
    IsGorensteinAt f hf ((pullback.fst f g).base x') := by
  let _ : IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x')) :=
    isLocallyNoetherian_fiber_pullback f g hf ((pullback.snd f g) x')
  change IsFlatAt (pullback.snd f g).toLRSHom.toShHom x' ∧
      Dualizing.IsGorensteinLocalRing
        (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
          ((pullback.snd f g).asFiber x')) at h
  show IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') ∧
      Dualizing.IsGorensteinLocalRing
        ((f.fiber (f ((pullback.fst f g).base x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g).base x')))
  exact ⟨(isFlatAt_pullback_snd_and f g x').2 h.1 hflat,
    (fiber_stalk_isGorenstein_iff_pullback f g hf x').mpr h.2⟩

/-- **Stacks Project, Tag 0C07.** Let `f : X ⟶ Y` be a morphism of schemes all of whose fibres
are locally Noetherian, let `g : Y' ⟶ Y` be locally of finite type, let `f'` be the base change
of `f` along `g`, and let `x'` be a point of the base change with image `x` in `X`. Then (1) if
`f` is Gorenstein at `x`, so is `f'` at `x'`; (2) if `f` is flat at `x` and `f'` is Gorenstein at
`x'`, then `f` is Gorenstein at `x`; (3) if `g` is flat at the image of `x'` in `Y'` and `f'` is
Gorenstein at `x'`, then `f` is Gorenstein at `x`. -/
public theorem isGorensteinAt_pullback_and {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x' : (pullback f g : Scheme.{u})) :
    (IsGorensteinAt f hf ((pullback.fst f g).base x') →
        IsGorensteinAt (pullback.snd f g)
          (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x') ∧
      (IsFlatAt f.toLRSHom.toShHom ((pullback.fst f g).base x') →
        IsGorensteinAt (pullback.snd f g)
          (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x' →
        IsGorensteinAt f hf ((pullback.fst f g).base x')) ∧
      (IsFlatAt g.toLRSHom.toShHom ((pullback.snd f g).base x') →
        IsGorensteinAt (pullback.snd f g)
          (fun y' => isLocallyNoetherian_fiber_pullback f g hf y') x' →
        IsGorensteinAt f hf ((pullback.fst f g).base x')) :=
  ⟨isGorensteinAt_pullback f g hf x',
    isGorensteinAt_of_pullback_of_flat f g hf x',
    isGorensteinAt_of_pullback_of_flat_base f g hf x'⟩


/-! ### Arbitrary base change of a flat morphism locally of finite type -/

/-- The fibre local rings of a morphism locally of finite type and of its base change along an
*arbitrary* morphism have the same Gorensteinness. -/
private theorem fiber_stalk_isGorenstein_iff_pullback_of_locallyOfFiniteType
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType f]
    (x' : (pullback f g : Scheme.{u}))
    [IsLocallyNoetherian (f.fiber (f ((pullback.fst f g).base x')))]
    [IsLocallyNoetherian ((pullback.snd f g).fiber ((pullback.snd f g) x'))] :
    Dualizing.IsGorensteinLocalRing
        ((f.fiber (f ((pullback.fst f g).base x'))).presheaf.stalk
          (f.asFiber ((pullback.fst f g).base x'))) ↔
      Dualizing.IsGorensteinLocalRing
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
  have hpoint : oldPoint = pullback.fst F G z' := fiberIsoOfEq_asFiber_eq_fst f g x' hxy
  let K := Y.residueField y
  let L := Y'.residueField y'
  let _ : Algebra K L := (g.residueFieldMap y').hom.toAlgebra
  let _ : LocallyOfFiniteType F :=
    inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField y))
  let _ : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  let _ : IsLocallyNoetherian (pY.fiber y') :=
    LocallyOfFiniteType.isLocallyNoetherian ((pullback.snd f g).fiberToSpecResidueField y')
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
  let _ : IsLocallyNoetherian (pullback F G₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd F G₀)
  have hgor : Dualizing.IsGorensteinLocalRing ((f.fiber y).presheaf.stalk oldPoint) ↔
      Dualizing.IsGorensteinLocalRing ((pullback F G₀).presheaf.stalk z₀) :=
    AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType
      K L (f.fiber y) F oldPoint z₀ hpoint₀
  have hOld := isGorensteinLocalRing_stalk_iso eFiber (f.asFiber (pX x'))
  have hNew := isGorensteinLocalRing_stalk_iso eTarget z
  exact hOld.trans (hgor.trans hNew.symm)

/-- **Stacks Project, Tag 0E0Q.** Let `f : X ⟶ Y` be flat and locally of finite type, and let
`g : Y' ⟶ Y` be an arbitrary morphism. Then the set of points of `X ×_Y Y'` at which the base
change of `f` along `g` is Gorenstein is the inverse image, under the projection to `X`, of the
set of points of `X` at which `f` is Gorenstein; that is, formation of the Gorenstein locus of
`f` commutes with arbitrary base change. -/
@[stacks 0E0Q]
public theorem setOf_isGorensteinAt_pullback_eq_preimage {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hf' : ∀ y' : Y', IsLocallyNoetherian ((pullback.snd f g).fiber y')) :
    {x' : (pullback f g : Scheme.{u}) | IsGorensteinAt (pullback.snd f g) hf' x'} =
      (pullback.fst f g).base ⁻¹' {x : X | IsGorensteinAt f hf x} := by
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  let _ := hf (f ((pullback.fst f g).base x'))
  let _ := hf' ((pullback.snd f g) x')
  have hiff := fiber_stalk_isGorenstein_iff_pullback_of_locallyOfFiniteType f g x'
  exact ⟨fun h => ⟨Flat.stalkMap f ((pullback.fst f g).base x'), hiff.mpr h.2⟩,
    fun h => ⟨Flat.stalkMap (pullback.snd f g) x', hiff.mp h.2⟩⟩

end AlgebraicGeometry.Scheme.Hom
