module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.RingTheory.QuasiFinite.BaseChange

/-!
# Base change of quasi-finiteness

For a morphism locally of finite type, a point closed in its fibre stays closed in its fibre
after any base change. Closedness in the fibre is finiteness of the residue field extension, and
finiteness is preserved by the pushout of fields computing the residue field of a point of the
fibre product.

The same holds for quasi-finiteness: the quasi-finite locus of a morphism locally of finite type
pulls back to the quasi-finite locus of any base change. Consequently locally quasi-finite and
quasi-finite morphisms are stable under arbitrary base change.

## Main results

* `AlgebraicGeometry.isClosed_asFiber_of_isPullback` preserves closedness in a fibre under base
  change.
* `AlgebraicGeometry.quasiFiniteLocus_eq_preimage_of_isPullback` identifies the quasi-finite
  locus of a base change with the inverse image of the original quasi-finite locus.
* The base-change instances for `AlgebraicGeometry.LocallyOfFiniteType`,
  `AlgebraicGeometry.LocallyQuasiFinite` and `AlgebraicGeometry.QuasiCompact` jointly give
  stability of locally quasi-finite and of quasi-finite morphisms under base change.

## Implementation notes

A base change is expressed by a cartesian square, independently of a chosen fibre product.
Points of scheme-theoretic fibres are represented by `Scheme.Hom.asFiber`. The residue field at a
point of the fibre product is identified with the residue field of the corresponding prime of the
tensor product of residue fields, via `Scheme.Pullback.Triplet`.

The quasi-finite locus is `AlgebraicGeometry.quasiFiniteLocus`, so the first assertion is an
equality of opens of the source of the base change; the inverse image there is the set-theoretic
realization of the fibre product of the quasi-finite locus with the new base. Its proof reduces
to a square of affines, where the comparison becomes
`Algebra.quasiFiniteAt_baseChange_iff` for the pushout of rings computed by
`AlgebraicGeometry.isPushout_appTop_of_isPullback`. As in `AlgebraicGeometry.quasiFiniteAt`,
local quasi-finiteness is represented by the pair `LocallyOfFiniteType` and
`LocallyQuasiFinite`, and quasi-finiteness adds `QuasiCompact`; their Mathlib base-change
instances therefore already state the remaining assertions.

## References

* [Stacks Project, Tag 01TM](https://stacks.math.columbia.edu/tag/01TM)
* [Stacks Project, Tag 053M](https://stacks.math.columbia.edu/tag/053M)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open scoped TensorProduct

/-- A pushout of a finite extension of a field along any field extension is finite. -/
private lemma finite_pushout_right
    {K A B C : Type u} [Field K] [CommRing A] [Field B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra A C] [Algebra B C] [Algebra K C]
    [IsScalarTower K A C] [IsScalarTower K B C]
    [Algebra.IsPushout K A B C] [Module.Finite K A] : Module.Finite B C := by
  let : Algebra.IsPushout K B A C :=
    (Algebra.IsPushout.comm K A B C).mp (inferInstance : Algebra.IsPushout K A B C)
  let : Module.Finite B (B ⊗[K] A) := Module.Finite.base_change K B A
  exact Module.Finite.equiv (Algebra.IsPushout.equiv K B A C).toLinearEquiv

open Limits

/-- The tensor product of residue fields of a triplet is finite over the residue field of the
second point, when the residue field of the first point is finite over that of its image. -/
private lemma finite_tensor_residueField {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (t : Scheme.Pullback.Triplet f g)
    (hx : letI := (f.residueFieldMap t.x).hom.toAlgebra
      Module.Finite (S.residueField (f t.x)) (X.residueField t.x)) :
    letI := t.tensorInr.hom.toAlgebra
    Module.Finite (Y.residueField t.y) t.tensor := by
  let x := t.x
  let y := t.y
  let K := S.residueField t.s
  let K0 := S.residueField (f x)
  let L := X.residueField x
  let B := Y.residueField y
  let fL := (S.residueFieldCongr t.hx).inv ≫ f.residueFieldMap x
  let gB := (S.residueFieldCongr t.hy).inv ≫ g.residueFieldMap y
  let : Algebra K0 L := (f.residueFieldMap x).hom.toAlgebra
  have hfin0 : Module.Finite K0 L := hx
  let e : CommRingCat.of K ⟶ CommRingCat.of K0 := (S.residueFieldCongr t.hx).inv
  let : Algebra K K0 := e.hom.toAlgebra
  let : Module.Finite K K0 := Module.Finite.of_surjective (Algebra.linearMap K K0)
    (ConcreteCategory.bijective_of_isIso e).2
  let : Algebra K L := fL.hom.toAlgebra
  let : IsScalarTower K K0 L := IsScalarTower.of_algebraMap_eq' rfl
  have hfinKL : Module.Finite K L := Module.Finite.trans K0 L
  let : Algebra K B := gB.hom.toAlgebra
  let : Algebra L t.tensor := t.tensorInl.hom.toAlgebra
  let : Algebra B t.tensor := t.tensorInr.hom.toAlgebra
  let : Algebra K t.tensor := Algebra.compHom t.tensor (algebraMap K L)
  let : IsScalarTower K L t.tensor := IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : fL ≫ t.tensorInl = gB ≫ t.tensorInr := pushout.condition
  have hcommRing : t.tensorInl.hom.comp fL.hom = t.tensorInr.hom.comp gB.hom := by
    simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom hcomm
  have : IsScalarTower K B t.tensor := IsScalarTower.of_algebraMap_eq' hcommRing
  have : Algebra.IsPushout K L B t.tensor :=
    (CommRingCat.isPushout_iff_isPushout (R := K) (S := B) (R' := L) (S' := t.tensor)).mp
      ⟨⟨pushout.condition⟩, ⟨pushoutIsPushout fL gB⟩⟩
  exact finite_pushout_right (K := K) (A := L) (B := B) (C := t.tensor)

/-- The residue field at a prime of the tensor product of residue fields of a triplet is finite
over the residue field of the second point, when the residue field of the first point is finite
over that of its image. -/
private lemma finite_residueField_tensor {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (t : Scheme.Pullback.Triplet f g)
    (hx : letI := (f.residueFieldMap t.x).hom.toAlgebra
      Module.Finite (S.residueField (f t.x)) (X.residueField t.x)) (p : Spec t.tensor) :
    letI : p.asIdeal.IsPrime := p.2
    letI := ((algebraMap t.tensor p.asIdeal.ResidueField).comp t.tensorInr.hom).toAlgebra
    Module.Finite (Y.residueField t.y) p.asIdeal.ResidueField := by
  let B := Y.residueField t.y
  let : Algebra B t.tensor := t.tensorInr.hom.toAlgebra
  have hfinC : Module.Finite B t.tensor := finite_tensor_residueField t hx
  let : IsArtinianRing t.tensor := IsArtinianRing.of_finite B t.tensor
  let : p.asIdeal.IsPrime := p.2
  let : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
  let b : B →+* p.asIdeal.ResidueField :=
    (algebraMap t.tensor p.asIdeal.ResidueField).comp t.tensorInr.hom
  let : Algebra B p.asIdeal.ResidueField := b.toAlgebra
  let : Module B p.asIdeal.ResidueField := b.toAlgebra.toModule
  let : IsScalarTower B t.tensor p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.trans t.tensor p.asIdeal.ResidueField

/-- For a prime `p` of the tensor product of residue fields of a triplet, the residue field map of
the second projection at the corresponding point of the fibre product, followed by the canonical
isomorphism onto `κ(p)`, is the map `κ(y) → κ(p)` through the tensor product. -/
private lemma residueFieldMap_snd_specTensorTo {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (t : Scheme.Pullback.Triplet f g) (p : Spec t.tensor) :
    letI : p.asIdeal.IsPrime := p.2
    (t.SpecTensorTo.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso t.tensor p).hom).hom.comp
        ((Y.residueFieldCongr (t.snd_SpecTensorTo_apply p).symm).hom ≫
          (pullback.snd f g).residueFieldMap (t.SpecTensorTo p)).hom =
      (algebraMap t.tensor p.asIdeal.ResidueField).comp t.tensorInr.hom := by
  let : p.asIdeal.IsPrime := p.2
  let y := t.y
  let B := Y.residueField y
  let z0 := t.SpecTensorTo p
  let e0 : CommRingCat.of ((pullback f g).residueField z0) ⟶
      CommRingCat.of p.asIdeal.ResidueField :=
    t.SpecTensorTo.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso t.tensor p).hom
  let a : B →+* (pullback f g).residueField z0 :=
    ((Y.residueFieldCongr (t.snd_SpecTensorTo_apply p).symm).hom ≫
      (pullback.snd f g).residueFieldMap z0).hom
  let b : B →+* p.asIdeal.ResidueField :=
    (algebraMap t.tensor p.asIdeal.ResidueField).comp t.tensorInr.hom
  have hSpecIso : Spec.map (Scheme.Spec.residueFieldIso t.tensor p).hom ≫
      (Spec t.tensor).fromSpecResidueField p =
      Spec.map (CommRingCat.ofHom (algebraMap t.tensor p.asIdeal.ResidueField)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp]
    simp
  have hz : (pullback.snd f g) z0 = y := t.snd_SpecTensorTo_apply p
  have hA : Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecResidueField y =
      (pullback f g).fromSpecResidueField z0 ≫ pullback.snd f g := by
    calc
      Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecResidueField y =
          Spec.map (CommRingCat.ofHom ((pullback.snd f g).residueFieldMap z0).hom) ≫
            Y.fromSpecResidueField ((pullback.snd f g) z0) := by
        simp [a, CommRingCat.ofHom_comp, Spec.map_comp,
          Scheme.residueFieldCongr_fromSpecResidueField hz.symm]
      _ = (pullback f g).fromSpecResidueField z0 ≫ pullback.snd f g :=
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (pullback.snd f g) z0
  have hringCat : CommRingCat.ofHom (e0.hom.comp a) = CommRingCat.ofHom b := by
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← cancel_mono (Y.fromSpecResidueField y)]
    calc
      (Spec.map e0 ≫ Spec.map (CommRingCat.ofHom a)) ≫ Y.fromSpecResidueField y =
          Spec.map e0 ≫ ((pullback f g).fromSpecResidueField z0 ≫ pullback.snd f g) := by
        rw [Category.assoc, hA]
      _ = (Spec.map (Scheme.Spec.residueFieldIso t.tensor p).hom ≫
          (Spec t.tensor).fromSpecResidueField p) ≫ t.SpecTensorTo ≫ pullback.snd f g := by
        simp only [e0, Spec.map_comp]
        show Spec.map (Scheme.Spec.residueFieldIso t.tensor p).hom ≫
          (Spec.map (t.SpecTensorTo.residueFieldMap p) ≫
            (pullback f g).fromSpecResidueField (t.SpecTensorTo p)) ≫ pullback.snd f g = _
        rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap t.tensor p.asIdeal.ResidueField)) ≫
          Spec.map (CommRingCat.ofHom t.tensorInr.hom) ≫ Y.fromSpecResidueField y := by
        rw [hSpecIso, t.specTensorTo_snd]; rfl
      _ = Spec.map (CommRingCat.ofHom b) ≫ Y.fromSpecResidueField y := by
        simp [b, CommRingCat.ofHom_comp, Spec.map_comp]
  exact congrArg CommRingCat.Hom.hom hringCat

/-- In a fibre product, the residue field at a point is finite over the residue field of its
image in the new base, when the corresponding point upstairs is closed in its fibre. -/
private lemma finite_pullback_residueField
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
    (z : ↑(pullback f g))
    (hx : IsClosed ({f.asFiber (pullback.fst f g z)} : Set (f.fiber (f (pullback.fst f g z))))) :
    letI := ((pullback.snd f g).residueFieldMap z).hom.toAlgebra
    Module.Finite (Y.residueField ((pullback.snd f g) z)) ((pullback f g).residueField z) := by
  let t := Scheme.Pullback.Triplet.ofPoint z
  let B := Y.residueField t.y
  let p : ↑(Spec t.tensor) := Scheme.Pullback.SpecOfPoint z
  let : p.asIdeal.IsPrime := p.2
  let b : B →+* p.asIdeal.ResidueField :=
    (algebraMap t.tensor p.asIdeal.ResidueField).comp t.tensorInr.hom
  let : Algebra B p.asIdeal.ResidueField := b.toAlgebra
  have hfinP : Module.Finite B p.asIdeal.ResidueField :=
    finite_residueField_tensor t ((isClosed_asFiber_iff_finite_residueField f t.x).mp hx) p
  let z0 := t.SpecTensorTo p
  have hz0 : z0 = z := Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  let e0 : CommRingCat.of ((pullback f g).residueField z0) ⟶
      CommRingCat.of p.asIdeal.ResidueField :=
    t.SpecTensorTo.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso t.tensor p).hom
  have : IsIso e0 := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso t p
  let a : B →+* (pullback f g).residueField z0 :=
    ((Y.residueFieldCongr (t.snd_SpecTensorTo_apply p).symm).hom ≫
      (pullback.snd f g).residueFieldMap z0).hom
  let emap := (pullback f g).residueFieldCongr hz0
  let hy : t.y = (pullback.snd f g) z := rfl
  let c : CommRingCat.of B ⟶ CommRingCat.of ((pullback f g).residueField z) :=
    (Y.residueFieldCongr hy).hom ≫ (pullback.snd f g).residueFieldMap z
  let e1 : CommRingCat.of ((pullback f g).residueField z) ⟶
      CommRingCat.of p.asIdeal.ResidueField :=
    emap.inv ≫ e0
  have hbase : c ≫ emap.inv = CommRingCat.ofHom a := by
    let baseIso := Y.residueFieldCongr (congrArg (pullback.snd f g) hz0)
    calc
      c ≫ emap.inv = (Y.residueFieldCongr hy).hom ≫
          (baseIso.inv ≫ (baseIso.hom ≫ (pullback.snd f g).residueFieldMap z)) ≫ emap.inv := by
            simp [c, Category.assoc]
      _ = (Y.residueFieldCongr hy).hom ≫
          (baseIso.inv ≫ ((pullback.snd f g).residueFieldMap z0 ≫ emap.hom)) ≫ emap.inv := by
            rw [Scheme.Hom.residueFieldMap_congr' (f := pullback.snd f g) hz0]
      _ = (Y.residueFieldCongr hy).hom ≫ baseIso.inv ≫ (pullback.snd f g).residueFieldMap z0 := by
            simp [Category.assoc]
      _ = CommRingCat.ofHom a := by
            ext r
            simp [a, baseIso, t, Scheme.residueFieldCongr_inv]
  let : Algebra B ((pullback f g).residueField z) := c.hom.toAlgebra
  have hring1 : e1.hom.comp c.hom = b := by
    show e0.hom.comp (emap.inv.hom.comp c.hom) = b
    rw [← CommRingCat.hom_comp, hbase]
    exact residueFieldMap_snd_specTensorTo t p
  let alg : (pullback f g).residueField z →ₐ[B] p.asIdeal.ResidueField :=
    AlgHom.mk e1.hom fun r => RingHom.congr_fun hring1 r
  exact (Module.Finite.equiv
    (AlgEquiv.ofBijective alg (ConcreteCategory.bijective_of_isIso e1)).symm.toLinearEquiv :
      Module.Finite B ((pullback f g).residueField z))

/-- A point above a point closed in its fibre remains closed in its fibre after
base change of a locally finite type morphism. -/
@[stacks 053M]
public theorem isClosed_asFiber_of_isPullback
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} [LocallyOfFiniteType f]
    (sq : IsPullback g' f' f g) (x' : X')
    (hx : IsClosed ({f.asFiber (g' x')} : Set (f.fiber (f (g' x'))))) :
    IsClosed ({f'.asFiber x'} : Set (f'.fiber (f' x'))) := by
  let e := sq.isoPullback
  have hfst : (pullback.fst f g) (e.hom x') = g' x' :=
    congrArg (fun k : X' ⟶ X => k x') sq.isoPullback_hom_fst
  have hy : (pullback.snd f g) (e.hom x') = f' x' :=
    congrArg (fun k : X' ⟶ S' => k x') sq.isoPullback_hom_snd
  have hfin := finite_pullback_residueField f g (e.hom x') (by rwa [hfst])
  let bIso := S'.residueFieldCongr hy
  have : IsIso (e.hom.residueFieldMap x') := by infer_instance
  let e2 : (pullback f g).residueField (e.hom x') ≃+* X'.residueField x' :=
    RingEquiv.ofBijective (e.hom.residueFieldMap x').hom
      (ConcreteCategory.bijective_of_isIso (e.hom.residueFieldMap x'))
  let e1 : S'.residueField ((pullback.snd f g) (e.hom x')) ≃+* S'.residueField (f' x') :=
    RingEquiv.ofBijective bIso.hom.hom (ConcreteCategory.bijective_of_isIso bIso.hom)
  let : Algebra (S'.residueField ((pullback.snd f g) (e.hom x')))
      ((pullback f g).residueField (e.hom x')) :=
    ((pullback.snd f g).residueFieldMap (e.hom x')).hom.toAlgebra
  let : Algebra (S'.residueField (f' x')) (X'.residueField x') :=
    (f'.residueFieldMap x').hom.toAlgebra
  have hres := Scheme.Hom.residueFieldMap_congr sq.isoPullback_hom_snd x'
  rw [Scheme.residueFieldMap_comp] at hres
  have he : RingHom.comp (algebraMap (S'.residueField (f' x')) (X'.residueField x'))
      e1.toRingHom = RingHom.comp e2.toRingHom
        (algebraMap (S'.residueField ((pullback.snd f g) (e.hom x')))
          ((pullback f g).residueField (e.hom x'))) := by
    have h := congrArg CommRingCat.Hom.hom hres
    ext r
    simpa [e1, e2, bIso, RingEquiv.ofBijective_apply,
      RingHom.algebraMap_toAlgebra] using congrFun (congrArg DFunLike.coe h.symm) r
  have : LocallyOfFiniteType f' := by
    rw [← sq.isoPullback_hom_snd]
    infer_instance
  exact (isClosed_asFiber_iff_finite_residueField f' x').mpr (Module.Finite.of_equiv_equiv e1 e2 he)

/-! ### Base change of the quasi-finite locus -/

/-- On a compatible pair of affine opens, quasi-finiteness at a point of a morphism locally of
finite type is quasi-finiteness of the induced ring map at the corresponding prime. -/
private lemma quasiFiniteAt_iff_appLE_quasiFiniteAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (U : S.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (x : X) (hxV : x ∈ V) (hVU : V ≤ f ⁻¹ᵁ U) :
    quasiFiniteAt f x ↔
      (f.appLE U V hVU).hom.QuasiFiniteAt (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  refine ⟨fun ⟨_, hq⟩ => hq.quasiFiniteAt hV hU hVU hxV, fun hq => ?_⟩
  exact (quasiFiniteAt_iff_exists_affineOpens f x).mpr
    ⟨⟨U, by simpa [Scheme.affineOpens] using hU⟩,
      ⟨V, by simpa [Scheme.affineOpens] using hV⟩, hxV, hVU,
      f.finiteType_appLE hU hV hVU, hq⟩

/-- Restricting a morphism locally of finite type to a compatible pair of opens does not change
where it is quasi-finite. -/
private lemma quasiFiniteAt_resLE_iff {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (U : S.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (x : V.toScheme) :
    quasiFiniteAt (f.resLE U V hVU) x ↔ quasiFiniteAt f (V.ι x) := by
  have hbase : (f.resLE U V hVU).QuasiFiniteAt x ↔ f.QuasiFiniteAt (V.ι x) := by
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff (g := U.ι), Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
  simpa [quasiFiniteAt, finiteTypeAt_of_locallyOfFiniteType] using hbase

/-- The restriction of a morphism to the top opens is its global sections map. -/
private lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ (by simp) = f.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

/-- Quasi-finiteness of an algebra of finite type at a prime is unchanged by the pushout of the
base along any ring map, read at the prime lying under the given one. -/
private lemma quasiFiniteAt_iff_of_isPushout {R A B C : Type*} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C]
    [Algebra B C] [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R B A C]
    [Algebra.FiniteType R A] (qA : Ideal A) [qA.IsPrime] (qC : Ideal C) [qC.IsPrime]
    (hq : qA = qC.comap (algebraMap A C)) :
    Algebra.QuasiFiniteAt R qA ↔ Algebra.QuasiFiniteAt B qC := by
  let e := Algebra.IsPushout.equiv R B A C
  let qT := qC.comap e.toRingEquiv.toRingHom
  have hcomp : e.toRingEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      algebraMap A C := by
    ext a
    simpa [e] using Algebra.IsPushout.equiv_tmul R B A C (1 : B) a
  have hqT : qA = qT.comap Algebra.TensorProduct.includeRight.toRingHom := by
    rwa [Ideal.comap_comap, hcomp]
  have hEq : Algebra.QuasiFiniteAt B qC ↔ Algebra.QuasiFiniteAt B qT := by
    refine ⟨fun _ => inferInstance, fun _ => ?_⟩
    have hh : qT.comap e.symm.toRingEquiv.toRingHom = qC := by
      ext x
      simp [qT]
    simpa only [hh] using
      (inferInstance : Algebra.QuasiFiniteAt B (qT.comap e.symm.toRingEquiv.toRingHom))
  exact (Algebra.quasiFiniteAt_baseChange_iff B qA qT hqT).symm.trans hEq.symm

/-- The affine case of the comparison: in a cartesian square of affine schemes, the base change
of a morphism locally of finite type is quasi-finite at a point exactly when the original
morphism is quasi-finite at its image. -/
@[sga "3 V 7.4" "special case"]
private lemma quasiFiniteAt_isPullback_of_isAffine {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) [LocallyOfFiniteType f] (p : P) :
    quasiFiniteAt f (fst p) ↔ quasiFiniteAt snd p := by
  have : LocallyOfFiniteType snd :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h ‹LocallyOfFiniteType f›
  have : IsAffine P := IsAffine.of_isPullback h
  have hX : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hY : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
  have hZ : IsAffineOpen (⊤ : Z.Opens) := isAffineOpen_top Z
  have hP : IsAffineOpen (⊤ : P.Opens) := isAffineOpen_top P
  let R := (Γ(Z, ⊤)).1
  let A := (Γ(X, ⊤)).1
  let B := (Γ(Y, ⊤)).1
  let C := (Γ(P, ⊤)).1
  let qA : Ideal A := (hX.primeIdealOf ⟨fst p, by simp⟩).asIdeal
  let qC : Ideal C := (hP.primeIdealOf ⟨p, by simp⟩).asIdeal
  algebraize [f.appTop.hom, g.appTop.hom, fst.appTop.hom, snd.appTop.hom]
  let : Algebra R C := (fst.appTop.hom.comp f.appTop.hom).toAlgebra
  let : IsScalarTower R A C := .of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R B C := .of_algebraMap_eq (by
    intro r
    have hcat : f.appTop ≫ fst.appTop = g.appTop ≫ snd.appTop := by
      simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h.w
    have hw := congrArg (fun k : Γ(Z, ⊤) ⟶ Γ(P, ⊤) => (CommRingCat.Hom.hom k) r) hcat
    simpa [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using hw)
  let : Algebra.IsPushout R B A C := by
    apply CommRingCat.isPushout_iff_isPushout.mp
    simpa [R, A, B, C, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      (isPushout_appTop_of_isPullback h).flip
  let : Algebra.FiniteType R A := by
    have hft := f.finiteType_appLE hZ hX (by simp)
    rwa [appLE_top_top f] at hft
  have hcomap : qA = qC.comap (algebraMap A C) := by
    have hpoint := IsAffineOpen.comap_primeIdealOf_appLE ⊤ hX ⊤ hP
      (f := fst) (x := p) (by simp) (by simp)
    have hideal := congrArg (fun z : PrimeSpectrum A => z.asIdeal) hpoint
    simpa [qA, qC, appLE_top_top, RingHom.algebraMap_toAlgebra] using hideal.symm
  have hring := quasiFiniteAt_iff_of_isPushout (R := R) (A := A) (B := B) (C := C) qA qC hcomap
  have hf := quasiFiniteAt_iff_appLE_quasiFiniteAt f ⊤ hZ ⊤ hX (fst p) (by simp) (by simp)
  have hsnd := quasiFiniteAt_iff_appLE_quasiFiniteAt snd ⊤ hY ⊤ hP p (by simp) (by simp)
  exact (hf.trans (by simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using hring)).trans hsnd.symm

/-- The pointwise comparison: in a cartesian square, the base change of a morphism locally of
finite type is quasi-finite at a point exactly when the original morphism is quasi-finite at its
image. -/
@[sga "3 V 7.4"]
private lemma quasiFiniteAt_isPullback_iff {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} [LocallyOfFiniteType f] (sq : IsPullback g' f' f g) (x' : X') :
    quasiFiniteAt f' x' ↔ quasiFiniteAt f (g' x') := by
  have hsquare : f (g' x') = g (f' x') := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : X' ⟶ S => k x') sq.w
  obtain ⟨-, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g' x'))) isOpen_univ
  have hs'U : f' x' ∈ g ⁻¹ᵁ U := by
    show g (f' x') ∈ U
    exact hsquare ▸ hsU
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsU (f ⁻¹ᵁ U).2
  obtain ⟨-, ⟨W, hW, rfl⟩, hs'W, hWU⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open hs'U (g ⁻¹ᵁ U).2
  let V' : X'.Opens := g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W
  have hxV' : x' ∈ V' := ⟨hxV, hs'W⟩
  let pV : Scheme.Opens.toScheme V := ⟨g' x', hxV⟩
  let p' : Scheme.Opens.toScheme V' := ⟨x', hxV'⟩
  have hres := Scheme.Hom.isPullback_resLE sq hWU hVU (UY := V') rfl
  have : LocallyOfFiniteType f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFiniteType f›
  have : IsAffine (Scheme.Opens.toScheme V) := hV
  have : IsAffine (Scheme.Opens.toScheme W) := hW
  have : IsAffine (Scheme.Opens.toScheme U) := hU
  have : LocallyOfFiniteType (f.resLE U V hVU) := instLocallyOfFiniteTypeResLE f V U hVU
  have hloc := quasiFiniteAt_isPullback_of_isAffine hres p'
  have hleft := quasiFiniteAt_resLE_iff f U V hVU pV
  have hright := quasiFiniteAt_resLE_iff f' W V' (by simp [V']) p'
  have hpointV : (g'.resLE V V' (by simp [V'])) p' = pV :=
    Subtype.ext (g'.coe_resLE_apply (e := by simp [V']) p')
  rw [hpointV] at hloc
  exact hright.symm.trans (hloc.symm.trans hleft)

/-- **Stacks Project, Tag 01TM.** In a cartesian square, the quasi-finite locus of the
base-changed morphism is the inverse image of the quasi-finite locus of the original
morphism. -/
@[stacks 01TM "part (1)"]
public theorem quasiFiniteLocus_eq_preimage_of_isPullback {X S S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} [LocallyOfFiniteType f]
    (sq : IsPullback g' f' f g) : quasiFiniteLocus f' = g' ⁻¹ᵁ quasiFiniteLocus f := by
  have h : ∀ x' : X', x' ∈ quasiFiniteLocus f' ↔ g' x' ∈ quasiFiniteLocus f := fun x' => by
    rw [mem_quasiFiniteLocus_iff, mem_quasiFiniteLocus_iff]
    exact quasiFiniteAt_isPullback_iff sq x'
  exact TopologicalSpace.Opens.ext (Set.ext h)

add_to_stacks 01TM "parts (2) and (3), local finite-type condition"
  AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange

add_to_stacks 01TM "parts (2) and (3), fiber-isolation condition"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite
add_to_sga "3 V 7.4" "special case"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite
add_to_sga "3 VIB 10.1" "sufficiency"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite
add_to_sga "3 VIB 2.8" "(i) ⇒ (ii), partial"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite
add_to_ega "II 6.2.4" "(iii)" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite

add_to_stacks 01TM "part (3), quasi-compact condition"
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange

end AlgebraicGeometry
