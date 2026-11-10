module

public import Mathlib.AlgebraicGeometry.StructureSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.FaithfullyFlatStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.MaximalIdealFieldChange
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinFieldExtension
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalization

/-!
# Gorenstein local rings after extension of the ground field

Let `X` be a scheme over a field `k`. Gorensteinness of the local ring at a point is
unchanged on passing to a point above it after extending the ground field. For a locally
Noetherian scheme the extension is required to be finitely generated, while for a scheme
locally of finite type over `k` the field extension may be arbitrary.

## Main results

* `AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_essFiniteType_fieldExtension` treats a
  finitely generated field extension and a locally Noetherian scheme.
* `AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType` treats an arbitrary
  field extension when the scheme is locally of finite type over the ground field.

## Implementation notes

The base change is the categorical pullback of the structure morphism along
`Spec K ⟶ Spec k`, and a point upstairs lies over `x` when its image under the first
pullback projection is `x`. A finitely generated extension of fields is expressed by
`Algebra.EssFiniteType`; this is the essentially-finite-type condition appropriate to
generation as a field rather than generation as a `k`-algebra.

The two assertions in the source are independent and are stated separately.

In both cases the stalk map `𝒪_{X,x} → 𝒪_{Y,y}` of the first projection is faithfully flat,
so the criterion for a flat local homomorphism (Tag 0BJL) reduces the statement to
Gorensteinness of the special fibre `𝒪_{Y,y} / 𝔪_x 𝒪_{Y,y}`. That special fibre is a
localization of `κ(x) ⊗_k κ(y')`, where `y'` is the image of `y` in `Spec K`, so it suffices
to know that this tensor product of fields is Gorenstein. The two statements differ only in
which of the two factors is a finitely generated extension of `κ(x) ∩ κ(y') = k`: for the first
it is `κ(y')`, because `K / k` is finitely generated, and for the second it is `κ(x)`, because
`X` is locally of finite type over `k`.

## References

* [Stacks Project, Tag 0C03](https://stacks.math.columbia.edu/tag/0C03)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The residue field of `Spec k` at its unique point is `k`. -/
private noncomputable def fieldResidueEquiv (k : Type u) [Field k] :
    k ≃+* (Spec (.of k)).residueField
      (IsLocalRing.closedPoint (CommRingCat.of k)) := by
  let cp : Spec (.of k) := IsLocalRing.closedPoint (CommRingCat.of k)
  let R := (Spec (.of k)).presheaf.stalk cp
  letI : IsLocalRing R := (Spec (.of k)).isLocalRing cp
  let e :=
    (AlgebraicGeometry.stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv
  let q : IsLocalRing.ResidueField k ≃+* k :=
    (Ideal.quotientEquivAlgOfEq k IsLocalRing.maximalIdeal_eq_bot).toRingEquiv.trans
      (RingEquiv.quotientBot k)
  exact ((IsLocalRing.ResidueField.mapEquiv e).trans q).symm

/-- The identification of `k` with the residue field of `Spec k` is the residue map composed
with the canonical map from `k` to the stalk. -/
private theorem fieldResidueEquiv_apply (k : Type u) [Field k] (z : k) :
    fieldResidueEquiv k z =
      (Spec (.of k)).residue
        (IsLocalRing.closedPoint (CommRingCat.of k) : Spec (.of k))
        (StructureSheaf.toStalk k
          (IsLocalRing.closedPoint (CommRingCat.of k) : Spec (.of k)) z) := by
  let cp : Spec (.of k) := IsLocalRing.closedPoint (CommRingCat.of k)
  let R := (Spec (.of k)).presheaf.stalk cp
  let : IsLocalRing R := (Spec (.of k)).isLocalRing cp
  let e :=
    (AlgebraicGeometry.stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv
  let q : IsLocalRing.ResidueField k ≃+* k :=
    (Ideal.quotientEquivAlgOfEq k IsLocalRing.maximalIdeal_eq_bot).toRingEquiv.trans
      (RingEquiv.quotientBot k)
  change (IsLocalRing.ResidueField.mapEquiv e).symm (q.symm z) = _
  have hq : q.symm z = IsLocalRing.residue k z := by
    let f : (k ⧸ IsLocalRing.maximalIdeal k) ≃+* (k ⧸ (⊥ : Ideal k)) :=
      (Ideal.quotientEquivAlgOfEq k
        (IsLocalRing.maximalIdeal_eq_bot (R := k))).toRingEquiv
    change f.symm ((RingEquiv.quotientBot k).symm z) = IsLocalRing.residue k z
    apply f.injective
    change Ideal.Quotient.mk (⊥ : Ideal k) z =
      Ideal.quotientEquivAlgOfEq k (IsLocalRing.maximalIdeal_eq_bot (R := k))
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal k) z)
    exact (Ideal.quotientEquivAlgOfEq_mk k
      (IsLocalRing.maximalIdeal_eq_bot (R := k)) z).symm
  rw [hq, IsLocalRing.ResidueField.mapEquiv.symm]
  change IsLocalRing.residue R ((e.symm : k →+* R) z) = _
  have he : (e.symm : k →+* R) = (StructureSheaf.toStalk k cp).hom :=
    congrArg CommRingCat.Hom.hom (AlgebraicGeometry.stalkClosedPointIso_inv (.of k))
  rw [he]
  rfl

/-- Under the identifications of `k` and `K` with the residue fields of `Spec k` and `Spec K`,
the map on residue fields induced by `Spec K ⟶ Spec k` is the structure map `k → K`. -/
private theorem residueFieldMap_spec_field
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    let f : CommRingCat.of k ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap k K)
    let y : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
    let x : Spec (.of k) := (Spec.map f).base y
    let cp : Spec (.of k) := IsLocalRing.closedPoint (CommRingCat.of k)
    let hxy : x = cp := Subsingleton.elim _ _
    ((Spec.map f).residueFieldMap y).hom.comp
      ((fieldResidueEquiv k).trans
        ((Scheme.residueFieldCongr hxy).symm.commRingCatIsoToRingEquiv) :
          k →+* (Spec (.of k)).residueField x) =
      (fieldResidueEquiv K : K →+* (Spec (.of K)).residueField y).comp
        (algebraMap k K) := by
  intro f y x cp hxy
  have hcat :
      StructureSheaf.toStalk k x ≫ (Spec.map f).stalkMap y =
        f ≫ StructureSheaf.toStalk K y :=
    stalkMap_toStalk f y
  ext z
  change ((Spec.map f).residueFieldMap y).hom
      ((fieldResidueEquiv k).trans
        ((Scheme.residueFieldCongr hxy).symm.commRingCatIsoToRingEquiv) z) =
    (fieldResidueEquiv K) ((algebraMap k K) z)
  have hxyTop : (x : PrimeSpectrum.Top k) = (cp : PrimeSpectrum.Top k) := hxy
  let ic := (structurePresheafInCommRingCat k).stalkCongr (.of_eq hxyTop)
  have hst : StructureSheaf.toStalk k x ≫ ic.hom = StructureSheaf.toStalk k cp :=
    StructureSheaf.toStalk_stalkSpecializes (Inseparable.of_eq hxyTop).ge
  have hbase :
      (Scheme.residueFieldCongr hxy).symm.hom (fieldResidueEquiv k z) =
        (Spec (.of k)).residue x (StructureSheaf.toStalk k x z) := by
    rw [fieldResidueEquiv_apply k z]
    have hr := Scheme.residue_residueFieldCongr (Spec (.of k)) hxy
    have hrz := congrArg (fun q : CommRingCat.Hom
        ((Spec (.of k)).presheaf.stalk x) ((Spec (.of k)).residueField cp) =>
          q.hom (StructureSheaf.toStalk k x z)) hr
    have hstz : ic.hom (StructureSheaf.toStalk k x z) =
        StructureSheaf.toStalk k cp z := by
      simpa using congrArg (fun q : _ →+* _ => q z)
        (CommRingCat.hom_ext_iff.mp hst)
    change (Scheme.residueFieldCongr hxy).hom
        ((Spec (.of k)).residue x (StructureSheaf.toStalk k x z)) =
      (Spec (.of k)).residue cp (ic.hom (StructureSheaf.toStalk k x z)) at hrz
    rw [hstz] at hrz
    simpa [cp] using
      congrArg (fun t => (Scheme.residueFieldCongr hxy).symm.hom t) hrz.symm
  calc ((Spec.map f).residueFieldMap y).hom
        ((Scheme.residueFieldCongr hxy).symm.hom (fieldResidueEquiv k z))
      = ((Spec.map f).residueFieldMap y).hom
          ((Spec (.of k)).residue x (StructureSheaf.toStalk k x z)) :=
        congrArg (fun t => ((Spec.map f).residueFieldMap y).hom t) hbase
    _ = (Spec (.of K)).residue y
          (((Spec.map f).stalkMap y).hom (StructureSheaf.toStalk k x z)) := rfl
    _ = (Spec (.of K)).residue y (StructureSheaf.toStalk K y (algebraMap k K z)) :=
        congrArg (fun t => (Spec (.of K)).residue y t)
          (congrArg (fun q : CommRingCat.Hom _ _ => q.hom z) hcat)
    _ = (fieldResidueEquiv K) ((algebraMap k K) z) :=
        (fieldResidueEquiv_apply K (algebraMap k K z)).symm

/-- Essential finiteness of an extension of fields is transported along isomorphisms of the
source and the target which are compatible with the two structure maps. -/
private theorem essFiniteType_of_fieldEquivs
    {k F K L : Type u} [Field k] [Field F] [Field K] [Field L]
    (e : k ≃+* F) (q : K ≃+* L) [Algebra k K]
    (h : Algebra.EssFiniteType k K) (b : F →+* L)
    (he : b.comp (e : k →+* F) = q.toRingHom.comp (algebraMap k K)) :
    letI : Algebra F L := b.toAlgebra
    Algebra.EssFiniteType F L := by
  let : Algebra k F := e.toRingHom.toAlgebra
  let : Algebra F L := b.toAlgebra
  let : Algebra k L := (b.comp e.toRingHom).toAlgebra
  have : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq' rfl
  let qAlg : K ≃ₐ[k] L := AlgEquiv.ofRingEquiv (f := q) fun x ↦ (RingHom.congr_fun he x).symm
  let eAlg : k ≃ₐ[k] F := AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)
  have : Algebra.EssFiniteType k F :=
    Algebra.EssFiniteType.of_surjective eAlg.toAlgHom eAlg.surjective
  exact (Algebra.EssFiniteType.comp_iff k F L).mp
    ((Algebra.EssFiniteType.iff_of_algEquiv qAlg).mp h)

/-- For a triplet of points of a pullback of schemes, the tensor product of the two residue
fields over the residue field of the base is Noetherian and Gorenstein, provided the extension
on one of the two factors is finitely generated. -/
@[ega "IV 6.7.1.1" "more general"]
private theorem isGorensteinRing_pullbackTensor
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (T : Scheme.Pullback.Triplet f g)
    (h : (letI := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
      Algebra.EssFiniteType (S.residueField T.s) (X.residueField T.x)) ∨
      (letI := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
      Algebra.EssFiniteType (S.residueField T.s) (Y.residueField T.y))) :
    ∃ hC : IsNoetherianRing (T.tensor : Type u),
      letI : IsNoetherianRing (T.tensor : Type u) := hC
      Dualizing.IsGorensteinRing (T.tensor : Type u) := by
  let F := S.residueField T.s
  let A := X.residueField T.x
  let B := Y.residueField T.y
  let C := (T.tensor : Type u)
  let a : F →+* A := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom
  let b : F →+* B := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom
  let i : A →+* C := T.tensorInl.hom
  let j : B →+* C := T.tensorInr.hom
  let : Algebra F A := a.toAlgebra
  let : Algebra F B := b.toAlgebra
  let : Algebra A C := i.toAlgebra
  let : Algebra B C := j.toAlgebra
  let : Algebra F C := (i.comp a).toAlgebra
  have : IsScalarTower F A C := IsScalarTower.of_algebraMap_eq' rfl
  have hp0 : IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom b)
      T.tensorInl T.tensorInr := by
    simpa [F, A, B, C, a, b,
      Scheme.Pullback.Triplet.tensor, Scheme.Pullback.Triplet.tensorInl,
      Scheme.Pullback.Triplet.tensorInr, CommRingCat.of_carrier] using
      (IsPushout.of_hasPushout
        (CommRingCat.ofHom a) (CommRingCat.ofHom b))
  have : IsScalarTower F B C := IsScalarTower.of_algebraMap_eq' (by
    ext z
    change (i.comp a) z = (j.comp b) z
    exact congrArg (fun q : CommRingCat.Hom (CommRingCat.of F) T.tensor => q.hom z) hp0.w)
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap F A)) (CommRingCat.ofHom (algebraMap F B))
      (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom (algebraMap B C)) := by
    convert hp0 using 1
  have : Algebra.IsPushout F A B C := (CommRingCat.isPushout_iff_isPushout).mp hp
  rcases h with h | h
  · have : Algebra.EssFiniteType F A := by simpa [F, A, a] using h
    have : Algebra.IsPushout F B A C :=
      (Algebra.IsPushout.comm F A B C).mp inferInstance
    have : IsNoetherianRing (B ⊗[F] A) := Algebra.EssFiniteType.isNoetherianRing B _
    let e : B ⊗[F] A ≃ₐ[B] C := Algebra.IsPushout.equiv F B A C
    have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv (B ⊗[F] A) e.toRingEquiv
    exact ⟨inferInstance, Dualizing.isGorensteinRing_of_ringEquiv e.toRingEquiv
      (Dualizing.isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension
        (k := F) (R := B) (K := A) (Dualizing.IsRegularRing.isGorensteinRing B))⟩
  · have : Algebra.EssFiniteType F B := by simpa [F, B, b] using h
    have : IsNoetherianRing (A ⊗[F] B) := Algebra.EssFiniteType.isNoetherianRing A _
    let e : A ⊗[F] B ≃ₐ[A] C := Algebra.IsPushout.equiv F A B C
    have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv (A ⊗[F] B) e.toRingEquiv
    exact ⟨inferInstance, Dualizing.isGorensteinRing_of_ringEquiv e.toRingEquiv
      (Dualizing.isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension
        (k := F) (R := A) (K := B) (Dualizing.IsRegularRing.isGorensteinRing A))⟩

/-- Gorensteinness of the stalk at a point of a base change is equivalent to that of the stalk
downstairs, once the tensor product of the residue fields of the point is Noetherian and
Gorenstein. -/
@[ega "IV 6.7.1.1" "more general"]
private theorem isGorensteinLocalRing_stalk_iff_of_isGorensteinRing_tensor
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    [IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})]
    (hT : ∃ hC : IsNoetherianRing
        (Scheme.Pullback.Triplet.ofPoint (f := f)
          (g := Spec.map (CommRingCat.ofHom (algebraMap k K))) x').tensor,
      letI : IsNoetherianRing
        (Scheme.Pullback.Triplet.ofPoint (f := f)
          (g := Spec.map (CommRingCat.ofHom (algebraMap k K))) x').tensor := hC
      Dualizing.IsGorensteinRing
        (Scheme.Pullback.Triplet.ofPoint (f := f)
          (g := Spec.map (CommRingCat.ofHom (algebraMap k K))) x').tensor) :
    Dualizing.IsGorensteinLocalRing
        (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base
          x')) ↔
      Dualizing.IsGorensteinLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk
          x') := by
  let g := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let A := X.presheaf.stalk (g.base x')
  let B := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x'
  let φ := (g.stalkMap x').hom
  obtain ⟨_, hTensor⟩ := hT
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing B := inferInstance
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp
    (AlgebraicGeometry.faithfullyFlat_stalkMap_fieldExtension k K X f (g.base x') x' rfl).flat
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom φ)
  let I := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  let p := RingHom.ker (Scheme.Pullback.ofPointTensor x').hom
  have : p.IsPrime := RingHom.ker_isPrime _
  have hQ : Dualizing.IsGorensteinLocalRing (B ⧸ I) :=
    Dualizing.isGorensteinLocalRing_of_ringEquiv
      (AlgebraicGeometry.specialFibreRingEquiv k K f x') (hTensor p)
  have hcrit := Dualizing.isGorensteinLocalRing_iff_of_flat A B
  exact ⟨fun hA ↦ hcrit.mpr ⟨hA, hQ⟩, fun hB ↦ (hcrit.mp hB).1⟩

/-- **Stacks Project, Tag 0C03.** Gorensteinness of local rings is unchanged after a finitely
generated extension of the ground field of a locally Noetherian scheme. -/
@[stacks 0C03 "finitely generated field extension"]
public theorem isGorensteinLocalRing_stalk_iff_of_essFiniteType_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx' : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x) :
    letI : IsLocallyNoetherian
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
      (AlgebraicGeometry.isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      Dualizing.IsGorensteinLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk
          x') := by
  subst x
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : IsLocallyNoetherian Y :=
    (AlgebraicGeometry.isLocallyNoetherian_baseChange_iff k K X f).mp inferInstance
  let qSpec := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Scheme.Pullback.Triplet.ofPoint x'
  let F := (Spec (.of k)).residueField T.s
  let L := (Spec (.of K)).residueField T.y
  have hs : T.s = (IsLocalRing.closedPoint (CommRingCat.of k) : Spec (.of k)) :=
    Subsingleton.elim _ _
  have hy : T.y = (IsLocalRing.closedPoint (CommRingCat.of K) : Spec (.of K)) :=
    Subsingleton.elim _ _
  let e : k ≃+* F := (fieldResidueEquiv k).trans
    ((Scheme.residueFieldCongr hs.symm).commRingCatIsoToRingEquiv)
  let q : K ≃+* L := (fieldResidueEquiv K).trans
    ((Scheme.residueFieldCongr hy.symm).commRingCatIsoToRingEquiv)
  let b : F →+* L :=
    ((Scheme.residueFieldCongr T.hy).inv ≫ qSpec.residueFieldMap T.y).hom
  have he : b.comp (e : k →+* F) = q.toRingHom.comp (algebraMap k K) := by
    let x₀ : Spec (.of k) :=
      qSpec.base (IsLocalRing.closedPoint (CommRingCat.of K))
    let c₀ : Spec (.of k) := IsLocalRing.closedPoint (CommRingCat.of k)
    have h₀ : x₀ = c₀ := Subsingleton.elim _ _
    let α := ((Spec (.of k)).residueFieldCongr hs.symm).hom
    let β := ((Spec (.of k)).residueFieldCongr T.hy.symm).hom
    let γ := ((Spec (.of k)).residueFieldCongr h₀.symm).hom
    let δ := (Scheme.residueFieldCongr (congrArg qSpec hy.symm)).hom
    let τ := ((Spec (.of K)).residueFieldCongr hy.symm).hom
    let r₀ := qSpec.residueFieldMap (IsLocalRing.closedPoint (CommRingCat.of K))
    let rT := qSpec.residueFieldMap T.y
    have hsrc : α ≫ β = γ ≫ δ :=
      (Scheme.residueFieldCongr_trans_hom (Spec (.of k)) hs.symm T.hy.symm).trans
        (Scheme.residueFieldCongr_trans_hom (Spec (.of k)) h₀.symm (congrArg qSpec hy.symm)).symm
    have hnat := qSpec.residueFieldMap_congr' hy.symm
    have hcan' : r₀.hom.comp
        (((fieldResidueEquiv k).trans
          ((Scheme.residueFieldCongr h₀).symm.commRingCatIsoToRingEquiv) :
            k →+* (Spec (.of k)).residueField x₀)) =
          ((fieldResidueEquiv K : K →+* (Spec (.of K)).residueField
            (IsLocalRing.closedPoint (CommRingCat.of K))).comp (algebraMap k K)) :=
      residueFieldMap_spec_field k K
    ext z
    have hnatz := congrArg (fun q : CommRingCat.Hom _ _ => q.hom
      (γ.hom (fieldResidueEquiv k z))) hnat
    have heval : e z = α.hom (fieldResidueEquiv k z) := by
      simp only [e, α, RingEquiv.trans_apply]
      rfl
    have hqval : q (algebraMap k K z) =
        τ.hom (fieldResidueEquiv K (algebraMap k K z)) := by
      simp only [q, τ, RingEquiv.trans_apply]
      rfl
    change rT.hom (β.hom (e z)) = q.toRingHom (algebraMap k K z)
    calc
      rT.hom (β.hom (e z)) =
          rT.hom (β.hom (α.hom (fieldResidueEquiv k z))) := by rw [heval]
      _ = rT.hom (δ.hom (γ.hom (fieldResidueEquiv k z))) :=
        congrArg rT.hom
          (congrArg (fun q : CommRingCat.Hom _ _ => q.hom (fieldResidueEquiv k z)) hsrc)
      _ = τ.hom (r₀.hom (γ.hom (fieldResidueEquiv k z))) := by
        simpa [r₀, rT, α, β, γ, δ, τ] using hnatz.symm
      _ = τ.hom ((fieldResidueEquiv K) (algebraMap k K z)) :=
        congrArg τ.hom (by simpa using congrArg (fun q : _ →+* _ => q z) hcan')
      _ = q.toRingHom (algebraMap k K z) := hqval.symm
  have hExt : (let : Algebra F L := b.toAlgebra; Algebra.EssFiniteType F L) :=
    essFiniteType_of_fieldEquivs e q inferInstance b he
  have hT := isGorensteinRing_pullbackTensor f qSpec T (Or.inr hExt)
  exact isGorensteinLocalRing_stalk_iff_of_isGorensteinRing_tensor k K X f x' hT

/-- **Stacks Project, Tag 0C03.** Gorensteinness of local rings is unchanged after an arbitrary
extension of the ground field when the scheme is locally of finite type over that field. -/
@[stacks 0C03 "arbitrary field extension for a locally finite type scheme"]
public theorem isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx' : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x' = x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      Dualizing.IsGorensteinLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk
          x') := by
  subst x
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap k K))))
  let qSpec := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T := Scheme.Pullback.Triplet.ofPoint x'
  let F := (Spec (.of k)).residueField T.s
  let Ares := X.residueField T.x
  let e : (Spec (.of k)).residueField (f.base T.x) ≃+* F :=
    (Spec (.of k)).residueFieldCongr T.hx |>.commRingCatIsoToRingEquiv
  let a : F →+* Ares :=
    (f.residueFieldMap T.x).hom.comp (e.symm : _ →+* _)
  let : Algebra ((Spec (.of k)).residueField (f.base T.x)) Ares :=
    (f.residueFieldMap T.x).hom.toAlgebra
  have he : a.comp (e : _ →+* F) = (f.residueFieldMap T.x).hom := by
    ext z
    simp [a]
  have hfin : (let : Algebra ((Spec (.of k)).residueField (f.base T.x)) Ares :=
      (f.residueFieldMap T.x).hom.toAlgebra
      Algebra.EssFiniteType ((Spec (.of k)).residueField (f.base T.x)) Ares) :=
    residueField_essFiniteType_of_locallyOfFiniteType f T.x
  have hExt : (let : Algebra F Ares := a.toAlgebra; Algebra.EssFiniteType F Ares) :=
    essFiniteType_of_fieldEquivs e (RingEquiv.refl Ares) hfin a he
  have hT := isGorensteinRing_pullbackTensor f qSpec T (Or.inl hExt)
  exact isGorensteinLocalRing_stalk_iff_of_isGorensteinRing_tensor k K X f x' hT

end AlgebraicGeometry
