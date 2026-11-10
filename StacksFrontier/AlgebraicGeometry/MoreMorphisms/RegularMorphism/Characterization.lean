module

public import Mathlib.Topology.Sets.OpenCover
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularMorphism.SmoothLocalSource
public import StacksFrontier.RingTheory.Regular.RegularRingHom

/-!
# Characterizations of regular morphisms

For a morphism of schemes whose fibres are locally Noetherian, regularity can be tested by
flatness together with geometric regularity of the fibres, by regularity of the induced ring map
on every compatible pair of affine opens, or on suitable open coverings of the target and of the
inverse images of its members.

## Main results

* `AlgebraicGeometry.Scheme.Hom.regular_tfae`: for a morphism `f` with locally Noetherian fibres,
  the following are equivalent: `f` is regular; `f` is flat with geometrically regular fibres;
  `f.appLE V U` is a regular ring map (`IsRegularRingHom`) for every pair of affine opens with
  `U ≤ f ⁻¹ᵁ V`; there are an open cover `V` of the target and open covers of the `f ⁻¹ᵁ V j`
  such that every restriction `f.resLE (V j) (U i)` is regular; and the same with affine members
  and regular ring maps `f.appLE (V j) (U i)`.

## References

* [Stacks Project, Tag 07R8](https://stacks.math.columbia.edu/tag/07R8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private lemma geometricallyRegularAt_of_openImmersion {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : Z ⟶ X) [IsOpenImmersion j]
    (h : IsGeometricallyRegular f) (z : Z) :
    IsGeometricallyRegularAt (j ≫ f) z := by
  intro K _ _ _ _ z' hz'
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let q := pullback.map (j ≫ f) g f g j (𝟙 _) (𝟙 _) (by simp) (by simp)
  let w := q z'
  have hcomp : q ≫ pullback.fst f g = pullback.fst (j ≫ f) g ≫ j := pullback.lift_fst _ _ _
  have hw : pullback.fst f g w = j z := by
    have hq := congrArg (fun m => m z') hcomp
    change pullback.fst f g (q z') = j ((pullback.fst (j ≫ f) g) z') at hq
    rwa [hz'] at hq
  have hr := h (j z) K w hw
  have : IsOpenImmersion q := by
    dsimp [q]
    infer_instance
  let : IsRegularLocalRing ((pullback f g).presheaf.stalk w) := hr
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (q.stalkMap z')).commRingCatIsoToRingEquiv

private lemma geometricallyRegular_of_openImmersion {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : Z ⟶ X) [IsOpenImmersion j]
    (h : IsGeometricallyRegular f) :
    IsGeometricallyRegular (j ≫ f) :=
  fun z => geometricallyRegularAt_of_openImmersion f j h z

private lemma geometricallyRegularAt_of_openImmersion_of_mem {k : Type u} [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : Z ⟶ X) [IsOpenImmersion j]
    (z : Z) (h : IsGeometricallyRegularAt (j ≫ f) z) :
    IsGeometricallyRegularAt f (j z) := by
  intro K _ _ _ _ w hw
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let q := pullback.map (j ≫ f) g f g j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hcomp : q ≫ pullback.fst f g = pullback.fst (j ≫ f) g ≫ j := pullback.lift_fst _ _ _
  obtain ⟨z', hz'⟩ : w ∈ Set.range q := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨z, hw.symm⟩, ⟨pullback.snd f g w, rfl⟩⟩
  have hz : pullback.fst (j ≫ f) g z' = z := by
    have he := congrArg (fun m => m z') hcomp
    change (pullback.fst f g) (q z') = j ((pullback.fst (j ≫ f) g) z') at he
    rw [hz', hw] at he
    exact j.isEmbedding.injective he.symm
  let : IsOpenImmersion q := by
    dsimp [q]
    infer_instance
  let : IsRegularLocalRing ((pullback (j ≫ f) g).presheaf.stalk z') := by
    simpa [g] using h K z' hz
  change IsRegularLocalRing ((pullback f g).presheaf.stalk w)
  rw [← hz']
  exact IsRegularLocalRing.of_ringEquiv
    ((asIso (q.stalkMap z')).commRingCatIsoToRingEquiv).symm

private lemma geometricallyRegularAt_of_specFieldIso {k k' : Type u} [Field k] [Field k']
    (e : CommRingCat.of k' ≅ CommRingCat.of k) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (h : IsGeometricallyRegularAt f x) :
    IsGeometricallyRegularAt (f ≫ Spec.map e.hom) x := by
  intro K _ _ hess _ x' hx'
  let : Algebra k k' := e.inv.hom.toAlgebra
  let : Algebra k K := ((algebraMap k' K).comp e.inv.hom).toAlgebra
  let : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective e.inv.hom := fun z => ⟨e.hom z, by simp⟩
  have hft : (algebraMap k k').FiniteType :=
    RingHom.FiniteType.of_surjective _ hsurj
  let : Algebra.FiniteType k k' := RingHom.finiteType_algebraMap.mp hft
  let : Algebra.EssFiniteType k k' := inferInstance
  let : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k k' K
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let g' : Spec (.of K) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' K))
  let q := Spec.map e.inv
  have hcomp : g' ≫ q = g := by
    dsimp [g, g', q]
    rw [← Spec.map_comp]
    congr 1
  have hleft : (f ≫ Spec.map e.hom) ≫ q = 𝟙 X ≫ f := by
    rw [Category.assoc, ← Spec.map_comp, e.inv_hom_id, Spec.map_id]
    simp
  let m := pullback.map (f ≫ Spec.map e.hom) g' f g
    (𝟙 X) (𝟙 _) q hleft hcomp
  have : IsIso m := by
    dsimp [m, q]
    let qIso := Scheme.Spec.mapIso (asIso e.inv).op
    let : IsIso (Spec.map e.inv) := ⟨qIso.inv, qIso.hom_inv_id, qIso.inv_hom_id⟩
    exact pullback.map_isIso (f ≫ Spec.map e.hom) g' f g
      (𝟙 X) (𝟙 _) (Spec.map e.inv) hleft hcomp
  have hmfst : m ≫ pullback.fst f g = pullback.fst (f ≫ Spec.map e.hom) g' :=
    pullback.lift_fst _ _ _
  have hxg : pullback.fst f g (m x') = x := by
    have he := congrArg (fun a => a x') hmfst
    change pullback.fst f g (m x') = pullback.fst (f ≫ Spec.map e.hom) g' x' at he
    rwa [hx'] at he
  let : IsOpenImmersion m := IsOpenImmersion.of_isIso m
  let : IsRegularLocalRing ((pullback f g).presheaf.stalk (m x')) := h K (m x') hxg
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (m.stalkMap x')).commRingCatIsoToRingEquiv

private lemma geometricallyRegular_of_specFieldIso {k k' : Type u} [Field k] [Field k']
    (e : CommRingCat.of k' ≅ CommRingCat.of k) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (h : IsGeometricallyRegular f) :
    IsGeometricallyRegular (f ≫ Spec.map e.hom) :=
  fun x => geometricallyRegularAt_of_specFieldIso e f x (h x)

private lemma geometricallyRegular_resLE_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (_hU : IsAffineOpen U) (V : Y.Opens) (_hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (y : Y) (hy : y ∈ V)
    (hnoeth : IsLocallyNoetherian (f.fiber y))
    (hgeo : IsGeometricallyRegular (f.fiberToSpecResidueField y)) :
    IsLocallyNoetherian ((f.resLE V U hUV).fiber ⟨y, hy⟩) ∧
      IsGeometricallyRegular
        ((f.resLE V U hUV).fiberToSpecResidueField ⟨y, hy⟩) := by
  let g := f.resLE V U hUV
  let yV : V.toScheme := ⟨y, hy⟩
  have hyV : V.ι yV = y := by simp [yV]
  let kCat := Y.residueField (V.ι yV)
  let k'Cat := V.toScheme.residueField yV
  let k := (kCat : Type u)
  let k' := (k'Cat : Type u)
  let : Field k' := V.toScheme.instFieldCarrierResidueField yV
  let : Field (k'Cat : Type u) := V.toScheme.instFieldCarrierResidueField yV
  let α := V.ι.residueFieldMap yV
  let : IsIso α := inferInstance
  let : Algebra k k' := α.hom.toAlgebra
  have hfin : (algebraMap k k').FiniteType :=
    RingHom.FiniteType.of_surjective _ (asIso α).commRingCatIsoToRingEquiv.surjective
  let : Algebra.FiniteType k k' := RingHom.finiteType_algebraMap.mp hfin
  have hα : α = CommRingCat.ofHom (algebraMap k k') := rfl
  let i₂ : Spec k'Cat ⟶ Spec kCat := Spec.map α
  let F := f.fiber (V.ι yV)
  let Fmap := f.fiberToSpecResidueField (V.ι yV)
  let F' := pullback Fmap i₂
  let p₁ := pullback.fst Fmap i₂
  let p₂ := pullback.snd Fmap i₂
  have : IsIso p₁ := pullback_fst_iso_of_right_iso Fmap i₂
  let q : g.fiber yV ⟶ F :=
    pullback.map g (V.toScheme.fromSpecResidueField yV)
      f (Y.fromSpecResidueField (V.ι yV)) U.ι i₂ V.ι
      (by simp [g, Scheme.Hom.resLE_comp_ι f hUV])
      (by
        change V.toScheme.fromSpecResidueField yV ≫ V.ι =
          Spec.map α ≫ Y.fromSpecResidueField (V.ι yV)
        exact (V.ι.SpecMap_residueFieldMap_fromSpecResidueField yV).symm)
  have hqcomm : q ≫ Fmap = g.fiberToSpecResidueField yV ≫ i₂ := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  have hqopen : IsOpenImmersion q := by
    let : IsOpenImmersion i₂ := IsOpenImmersion.of_isIso i₂
    dsimp [q]
    exact Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  let q' : g.fiber yV ⟶ F' := q ≫ (asIso p₁).inv
  have hq'comm : q' ≫ p₂ = g.fiberToSpecResidueField yV := by
    apply (cancel_mono i₂).mp
    simp only [q', p₂, p₁, Category.assoc, ← pullback.condition, asIso_inv,
      IsIso.inv_hom_id_assoc, hqcomm]
  have hq'open : IsOpenImmersion q' := by
    dsimp [q']
    infer_instance
  let : IsLocallyNoetherian F := by
    change IsLocallyNoetherian (f.fiber (V.ι yV))
    rw [hyV]
    exact hnoeth
  have hbase := @geometricallyRegular_baseChange_iff k k'
    (Y.instFieldCarrierResidueField (V.ι yV))
    (V.toScheme.instFieldCarrierResidueField yV) (inferInstance) (inferInstance)
    F (inferInstance) Fmap
  have hgeo0 : IsGeometricallyRegular Fmap := by
    change IsGeometricallyRegular (f.fiberToSpecResidueField (V.ι yV))
    rw [hyV]
    exact hgeo
  have hgeo' : @IsGeometricallyRegular (k'Cat : Type u)
      (V.toScheme.instFieldCarrierResidueField yV) (pullback Fmap i₂) p₂ :=
    hbase.mp hgeo0
  refine ⟨isLocallyNoetherian_of_isOpenImmersion q, ?_⟩
  rw [← hq'comm]
  exact geometricallyRegular_of_openImmersion p₂ q' hgeo'


private lemma regularAt_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (x : X) (hx : x ∈ U)
    (hnoeth : IsLocallyNoetherian (f.fiber (f x)))
    (hreg : Scheme.Hom.IsRegularAt (f.resLE V U hUV) ⟨x, hx⟩) :
    Scheme.Hom.IsRegularAt f x := by
  let g := f.resLE V U hUV
  let zU : U.toScheme := ⟨x, hx⟩
  let yV : V.toScheme := g zU
  have hyV : V.ι yV = f x := by
    have he := congrArg (fun m => m zU) (Scheme.Hom.resLE_comp_ι f hUV)
    change V.ι (g zU) = f x at he
    simpa [g, yV, zU] using he
  have hflat : (f.stalkMap x).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f hUV zU)).mp hreg.1
  have hgeo : IsGeometricallyRegularAt
      (f.fiberToSpecResidueField (f x)) (f.asFiber x) := by
    let kCat := Y.residueField (V.ι yV)
    let k'Cat := V.toScheme.residueField yV
    let k := (kCat : Type u)
    let k' := (k'Cat : Type u)
    let : Field k' := V.toScheme.instFieldCarrierResidueField yV
    let : Field (k'Cat : Type u) := V.toScheme.instFieldCarrierResidueField yV
    let α := V.ι.residueFieldMap yV
    let : IsIso α := inferInstance
    let : Algebra k k' := α.hom.toAlgebra
    have hfin : (algebraMap k k').FiniteType :=
      RingHom.FiniteType.of_surjective _ (asIso α).commRingCatIsoToRingEquiv.surjective
    let : Algebra.FiniteType k k' := RingHom.finiteType_algebraMap.mp hfin
    have hα : α = CommRingCat.ofHom (algebraMap k k') := rfl
    let i₂ : Spec k'Cat ⟶ Spec kCat := Spec.map α
    let F := f.fiber (V.ι yV)
    let Fmap := f.fiberToSpecResidueField (V.ι yV)
    let q : g.fiber yV ⟶ F :=
      pullback.map g (V.toScheme.fromSpecResidueField yV)
        f (Y.fromSpecResidueField (V.ι yV)) U.ι i₂ V.ι
        (by simp [g, Scheme.Hom.resLE_comp_ι f hUV])
        (by
          change V.toScheme.fromSpecResidueField yV ≫ V.ι =
            Spec.map α ≫ Y.fromSpecResidueField (V.ι yV)
          exact (V.ι.SpecMap_residueFieldMap_fromSpecResidueField yV).symm)
    let zG : g.fiber yV := g.asFiber zU
    have hqgeo : IsGeometricallyRegularAt (g.fiberToSpecResidueField yV) zG := hreg.2
    let zF : f.fiber (V.ι yV) :=
      (f.fiberHomeo (V.ι yV)).symm ⟨x, hyV.symm⟩
    have hqpoint : q zG = zF := by
      apply (f.fiberι (V.ι yV)).isEmbedding.injective
      have hcomp : q ≫ f.fiberι (V.ι yV) =
          pullback.fst g (V.toScheme.fromSpecResidueField yV) ≫ U.ι := by
        dsimp [q, pullback.map]
        exact pullback.lift_fst _ _ _
      have hp := congrArg (fun m => m zG) hcomp
      change f.fiberι (V.ι yV) (q zG) = U.ι
        (pullback.fst g (V.toScheme.fromSpecResidueField yV) zG) at hp
      have hzU : pullback.fst g (V.toScheme.fromSpecResidueField yV) zG = zU := by
        change g.fiberι yV (g.asFiber zU) = zU
        simp [yV, g.fiberι_asFiber zU]
      rw [hzU] at hp
      have hι : f.fiberι (V.ι yV) zF = x := by
        simp [zF]
      exact hp.trans hι.symm
    let F' := pullback Fmap i₂
    let p₁ := pullback.fst Fmap i₂
    let p₂ := pullback.snd Fmap i₂
    have : IsIso p₁ := pullback_fst_iso_of_right_iso Fmap i₂
    let q' : g.fiber yV ⟶ F' := q ≫ (asIso p₁).inv
    have hqcomm : q ≫ Fmap = g.fiberToSpecResidueField yV ≫ i₂ := pullback.lift_snd _ _ _
    have hqopen : IsOpenImmersion q := by
      let : IsOpenImmersion i₂ := IsOpenImmersion.of_isIso i₂
      dsimp [q]
      exact Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
    have hq'comm : q' ≫ p₂ = g.fiberToSpecResidueField yV := by
      apply (cancel_mono i₂).mp
      simp only [q', p₂, p₁, Category.assoc, ← pullback.condition, asIso_inv,
        IsIso.inv_hom_id_assoc, hqcomm]
    have hq'open : IsOpenImmersion q' := by
      dsimp [q']
      infer_instance
    have hgeoF' : @IsGeometricallyRegularAt (k'Cat : Type u)
        (V.toScheme.instFieldCarrierResidueField yV) _ p₂ (q' zG) :=
      geometricallyRegularAt_of_openImmersion_of_mem p₂ q' zG (hq'comm.symm ▸ hqgeo)
    have hfst : pullback.fst Fmap i₂ (q' zG) = zF :=
      (congr($(show q' ≫ p₁ = q by simp [q']) zG)).trans hqpoint
    have : IsLocallyNoetherian F := by
      change IsLocallyNoetherian (f.fiber (V.ι yV))
      rw [hyV]
      exact hnoeth
    let fldBase : Field k := Y.instFieldCarrierResidueField (V.ι yV)
    let : Field k := fldBase
    have hbase := @geometricallyRegularAt_baseChange_iff
      k k' fldBase
      (V.toScheme.instFieldCarrierResidueField yV)
      (inferInstance : Algebra k k')
      (inferInstance : Algebra.EssFiniteType k k') F ‹IsLocallyNoetherian F›
      Fmap zF (q' zG) hfst
    have hgeoF : @IsGeometricallyRegularAt k fldBase F Fmap zF := by
      simpa [hα, k, k', kCat, k'Cat, Scheme.residueField] using hbase.mpr hgeoF'
    let P : {y : Y // f x = y} → Prop := fun s =>
      @IsGeometricallyRegularAt (Y.residueField s.1 : Type u)
        (Y.instFieldCarrierResidueField s.1) (f.fiber s.1)
        (f.fiberToSpecResidueField s.1) ((f.fiberHomeo s.1).symm ⟨x, s.2⟩)
    have hgeoP : P ⟨V.ι yV, hyV.symm⟩ := by
      change @IsGeometricallyRegularAt (Y.residueField (V.ι yV) : Type u)
        (Y.instFieldCarrierResidueField (V.ι yV)) F Fmap zF
      simpa [k, kCat, F, Fmap, P, zF, Scheme.residueField] using hgeoF
    have hp : (⟨V.ι yV, hyV.symm⟩ : {y : Y // f x = y}) = ⟨f x, rfl⟩ := Subtype.ext hyV
    have hgeoP' : P ⟨f x, rfl⟩ := hp ▸ hgeoP
    change @IsGeometricallyRegularAt (Y.residueField (f x) : Type u)
      (Y.instFieldCarrierResidueField (f x)) (f.fiber (f x))
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)
    simpa [P, Scheme.Hom.asFiber, Scheme.residueField] using hgeoP'
  exact ⟨hflat, hgeo⟩

/-- A geometrically regular algebra over a field has regular underlying ring. -/
private theorem isRegularRing_of_isGeometricallyRegular (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] (h : Algebra.IsGeometricallyRegular k A) : IsRegularRing A := by
  have _ : Algebra.IsGeometricallyRegular k A := h
  have _ : IsRegularRing (k ⊗[k] A) := inferInstance
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k A).toRingEquiv

/-- If an algebra over a field is geometrically regular, then its spectrum is geometrically
regular over that field. -/
private theorem isGeometricallyRegular_specMap_of_algebra (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] (h : Algebra.IsGeometricallyRegular k A) :
    IsGeometricallyRegular (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  have hreg : IsRegularRing A := isRegularRing_of_isGeometricallyRegular k A h
  have _ : IsNoetherianRing A := hreg.toIsNoetherian
  have _ : IsLocallyNoetherian (Spec (.of A)) := inferInstance
  have _ : Algebra.IsGeometricallyRegular k A := h
  rw [isGeometricallyRegular_iff_isRegular_baseChange k (Spec (.of A))]
  intro K _ _ _
  have hK : IsRegularRing (A ⊗[k] K) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k K A).toRingEquiv
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso (pullbackSpecIso k A K).symm
    ((isRegular_spec_iff (A ⊗[k] K)).mpr hK)

/-- If the spectrum of a Noetherian algebra over a field is geometrically regular over that
field, then the algebra is geometrically regular. -/
private theorem algebra_isGeometricallyRegular_of_specMap (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A]
    (h : IsGeometricallyRegular (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :
    Algebra.IsGeometricallyRegular k A := by
  have _ : IsLocallyNoetherian (Spec (.of A)) := inferInstance
  rw [isGeometricallyRegular_iff_isRegular_baseChange k (Spec (.of A))] at h
  refine ⟨fun K _ _ _ => ?_⟩
  have hr : IsRegular (Spec (.of (A ⊗[k] K))) :=
    ObjectProperty.IsClosedUnderIsomorphisms.of_iso (pullbackSpecIso k A K) (h K)
  have hK : IsRegularRing (A ⊗[k] K) := (isRegular_spec_iff (A ⊗[k] K)).mp hr
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv

private noncomputable def affineFiberToSpecFiberIso {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (y : Y)
    [(Y.isoSpec.hom y).asIdeal.IsPrime] :
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Arrow.mk (f.fiberToSpecResidueField y) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom <|
        algebraMap (Y.isoSpec.hom y).asIdeal.ResidueField
          ((Y.isoSpec.hom y).asIdeal.Fiber Γ(X, ⊤)))) := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let : Algebra R S := f.appTop.hom.toAlgebra
  let p : Spec R := Y.isoSpec.hom y
  let q : Spec (Y.residueField y) ⟶ Spec ((Spec R).residueField p) :=
    Spec.map (Y.isoSpec.hom.residueFieldMap y)
  have hq : IsIso q := by
    dsimp [q]
    infer_instance
  have hleft : f ≫ Y.isoSpec.hom = X.isoSpec.hom ≫ Spec.map f.appTop :=
    (Scheme.isoSpec_hom_naturality f).symm
  have hright : Y.fromSpecResidueField y ≫ Y.isoSpec.hom =
      q ≫ (Spec R).fromSpecResidueField p := by
    dsimp [q, p]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (f := Y.isoSpec.hom) y).symm
  let m₀ : pullback f (Y.fromSpecResidueField y) ⟶
      pullback (f ≫ Y.isoSpec.hom) (Y.fromSpecResidueField y ≫ Y.isoSpec.hom) :=
    pullback.map f (Y.fromSpecResidueField y)
      (f ≫ Y.isoSpec.hom) (Y.fromSpecResidueField y ≫ Y.isoSpec.hom)
      (𝟙 X) (𝟙 _) Y.isoSpec.hom (by simp) (by simp)
  have hm₀ : IsIso m₀ := by
    dsimp [m₀]
    exact pullback.map_isIso f (Y.fromSpecResidueField y)
      (f ≫ Y.isoSpec.hom) (Y.fromSpecResidueField y ≫ Y.isoSpec.hom)
      (𝟙 X) (𝟙 _) Y.isoSpec.hom (by simp) (by simp)
  let m₁ : pullback (f ≫ Y.isoSpec.hom)
      (Y.fromSpecResidueField y ≫ Y.isoSpec.hom) ⟶
      pullback (Spec.map f.appTop) ((Spec R).fromSpecResidueField p) :=
    pullback.map (f ≫ Y.isoSpec.hom)
      (Y.fromSpecResidueField y ≫ Y.isoSpec.hom)
      (Spec.map f.appTop) ((Spec R).fromSpecResidueField p)
      X.isoSpec.hom q (𝟙 _) (by simpa using hleft) (by simpa using hright)
  have hm₁ : IsIso m₁ := by
    dsimp [m₁]
    infer_instance
  let e₀ : Arrow.mk (pullback.snd f (Y.fromSpecResidueField y)) ≅
      Arrow.mk (pullback.snd (f ≫ Y.isoSpec.hom)
        (Y.fromSpecResidueField y ≫ Y.isoSpec.hom)) :=
    Arrow.isoMk (asIso m₀) (Iso.refl _) (by
      change m₀ ≫ pullback.snd (f ≫ Y.isoSpec.hom)
          (Y.fromSpecResidueField y ≫ Y.isoSpec.hom) =
        pullback.snd f (Y.fromSpecResidueField y)
      dsimp [m₀, pullback.map]
      rw [pullback.lift_snd]
      simp)
  let e₁ : Arrow.mk (pullback.snd (f ≫ Y.isoSpec.hom)
        (Y.fromSpecResidueField y ≫ Y.isoSpec.hom)) ≅
      Arrow.mk (pullback.snd (Spec.map f.appTop)
        ((Spec R).fromSpecResidueField p)) :=
    Arrow.isoMk (asIso m₁) (asIso q) (by
      dsimp [m₁, pullback.map]
      rw [pullback.lift_snd])
  have e : Arrow.mk (pullback.snd f (Y.fromSpecResidueField y)) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom <|
        algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))) :=
    e₀ ≪≫ e₁ ≪≫ Spec.fiberToSpecResidueFieldIso R S p
  change Arrow.mk (pullback.snd f (Y.fromSpecResidueField y)) ≅
    Arrow.mk (Spec.map (CommRingCat.ofHom
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))))
  simpa [Scheme.Hom.fiberToSpecResidueField] using e

/-- An isomorphism of arrows over spectra of rings induces an isomorphism of the rings. -/
private noncomputable def specRightIso {k k' : CommRingCat.{u}} {X Z : Scheme.{u}}
    {a : X ⟶ Spec k} {b : Z ⟶ Spec k'} (e : Arrow.mk a ≅ Arrow.mk b) : k' ≅ k where
  hom := Spec.preimage e.hom.right
  inv := Spec.preimage e.inv.right
  hom_inv_id := by
    apply Spec.map_injective
    have h : e.inv.right ≫ e.hom.right = 𝟙 (Spec k') := Arrow.hom.congr_right e.inv_hom_id
    simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using h
  inv_hom_id := by
    apply Spec.map_injective
    have h : e.hom.right ≫ e.inv.right = 𝟙 (Spec k) := Arrow.hom.congr_right e.hom_inv_id
    simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using h

private lemma geometricallyRegular_affineFiber_to_algebra
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (y : Y)
    [(Y.isoSpec.hom y).asIdeal.IsPrime]
    (hnoeth : IsLocallyNoetherian (f.fiber y))
    (hgeo : IsGeometricallyRegular (f.fiberToSpecResidueField y)) :
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    IsNoetherianRing (((Y.isoSpec.hom y).asIdeal).Fiber Γ(X, ⊤)) ∧
      Algebra.IsGeometricallyRegular
        ((Y.isoSpec.hom y).asIdeal.ResidueField)
        (((Y.isoSpec.hom y).asIdeal).Fiber Γ(X, ⊤)) := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let : Algebra R S := f.appTop.hom.toAlgebra
  let p : PrimeSpectrum (Γ(Y, ⊤)) := Y.isoSpec.hom y
  let k := (Y.residueField y : Type u)
  let k' := p.asIdeal.ResidueField
  let A := p.asIdeal.Fiber S
  let : Field k := Y.instFieldCarrierResidueField y
  let : Field k' := IsLocalRing.ResidueField.field (Localization.AtPrime p.asIdeal)
  let : Algebra k' A := inferInstance
  let eFiber := affineFiberToSpecFiberIso f y
  let eField : CommRingCat.of k' ≅ CommRingCat.of k := specRightIso eFiber
  let j := eFiber.hom.left
  let ringMap : Spec (.of A) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' A))
  have hright : eFiber.hom.right = Spec.map eField.hom := (Spec.map_preimage _).symm
  have hgeo' : IsGeometricallyRegular
      (f.fiberToSpecResidueField y ≫ Spec.map eField.hom) :=
    geometricallyRegular_of_specFieldIso eField (f.fiberToSpecResidueField y) hgeo
  have hgeoComp : IsGeometricallyRegular (j ≫ ringMap) := by
    rw [show j ≫ ringMap = f.fiberToSpecResidueField y ≫ Spec.map eField.hom by
      rw [← hright]; simp [j, ringMap]]
    exact hgeo'
  have hgeoRingMap : IsGeometricallyRegular ringMap := by
    let : IsIso j := inferInstance
    let : IsOpenImmersion j := IsOpenImmersion.of_isIso j
    intro z
    let zF : f.fiber y := (asIso j).inv z
    have hz : j zF = z := by
      change ((asIso j).inv ≫ (asIso j).hom) z = z
      exact congrArg (fun q => q z) (asIso j).inv_hom_id
    have hzgeo := geometricallyRegularAt_of_openImmersion_of_mem
      ringMap j zF (hgeoComp zF)
    simpa [hz] using hzgeo
  have hnoethA : IsNoetherianRing A := by
    let : IsLocallyNoetherian ((Arrow.mk (f.fiberToSpecResidueField y)).left) := by
      change IsLocallyNoetherian (f.fiber y)
      exact hnoeth
    let : IsIso j := inferInstance
    let jIso := asIso j
    let : IsOpenImmersion jIso.inv := IsOpenImmersion.of_isIso jIso.inv
    let : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_of_isOpenImmersion jIso.inv
    let : IsNoetherianRing Γ(Spec (.of A), ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec (.of A))⟩
    exact isNoetherianRing_of_ringEquiv Γ(Spec (.of A), ⊤)
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  exact ⟨hnoethA, algebra_isGeometricallyRegular_of_specMap _ _ hgeoRingMap⟩

private lemma geometricallyRegular_affineFiber_of_algebra
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (y : Y)
    [(Y.isoSpec.hom y).asIdeal.IsPrime]
    (hgeo : let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      Algebra.IsGeometricallyRegular
      ((Y.isoSpec.hom y).asIdeal.ResidueField)
      (((Y.isoSpec.hom y).asIdeal).Fiber Γ(X, ⊤))) :
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    IsGeometricallyRegular (f.fiberToSpecResidueField y) := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let : Algebra R S := f.appTop.hom.toAlgebra
  let p : PrimeSpectrum (Γ(Y, ⊤)) := Y.isoSpec.hom y
  let k := (Y.residueField y : Type u)
  let k' := p.asIdeal.ResidueField
  let A := p.asIdeal.Fiber S
  let : Field k := Y.instFieldCarrierResidueField y
  let : Field k' := IsLocalRing.ResidueField.field (Localization.AtPrime p.asIdeal)
  let : Algebra k' A := inferInstance
  let eFiber := affineFiberToSpecFiberIso f y
  let eField : CommRingCat.of k' ≅ CommRingCat.of k := specRightIso eFiber
  let j := eFiber.hom.left
  let ringMap : Spec (.of A) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' A))
  have hright : eFiber.hom.right = Spec.map eField.hom := (Spec.map_preimage _).symm
  have hgeoRingMap : IsGeometricallyRegular ringMap :=
    isGeometricallyRegular_specMap_of_algebra _ _ hgeo
  let : IsIso j := inferInstance
  let : IsOpenImmersion j := IsOpenImmersion.of_isIso j
  have hgeoComp : IsGeometricallyRegular
      (f.fiberToSpecResidueField y ≫ Spec.map eField.hom) := by
    rw [show f.fiberToSpecResidueField y ≫ Spec.map eField.hom = j ≫ ringMap by
      rw [← hright]; simp [j, ringMap]]
    exact geometricallyRegular_of_openImmersion ringMap j hgeoRingMap
  have hgeoBase : IsGeometricallyRegular
      ((f.fiberToSpecResidueField y ≫ Spec.map eField.hom) ≫ Spec.map eField.inv) :=
    geometricallyRegular_of_specFieldIso eField.symm _ hgeoComp
  rwa [show (f.fiberToSpecResidueField y ≫ Spec.map eField.hom) ≫ Spec.map eField.inv =
      f.fiberToSpecResidueField y by
    rw [Category.assoc, ← Spec.map_comp, eField.inv_hom_id, Spec.map_id]
    exact Category.comp_id _]
    at hgeoBase

private theorem isRegularRingHom_of_arrowIso
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S')
    (e : Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk (CommRingCat.ofHom g))
    (h : IsRegularRingHom f) : IsRegularRingHom g := by
  let eR : R ≃+* R' := (asIso e.hom.left).commRingCatIsoToRingEquiv
  let eS : S ≃+* S' := (asIso e.hom.right).commRingCatIsoToRingEquiv
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := g.toAlgebra
  have hAlg : IsRegularRingHom (algebraMap R S) := by
    simpa [RingHom.algebraMap_toAlgebra] using h
  have hcompat : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r) := fun r =>
    (congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of S' => m.hom r) (Arrow.w e.hom)).symm
  have h' := Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv eR eS hcompat hAlg
  simpa [RingHom.algebraMap_toAlgebra] using h'

private theorem regular_of_regularRingHom_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hreg : IsRegularRingHom f.appTop.hom) : Scheme.Hom.IsRegular f := by
  rw [Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers]
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have hregAlg : IsRegularRingHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) := by
    simpa [RingHom.algebraMap_toAlgebra] using hreg
  have hparts := (isRegularRingHom_algebraMap_iff.mp hregAlg)
  refine ⟨?_, fun y => ?_⟩
  · rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    exact hparts.1
  · have := (Y.isoSpec.hom y).isPrime
    exact geometricallyRegular_affineFiber_of_algebra f y (hparts.2 _).2

private theorem affineFiberData_eq_of_ideal_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p = q)
    (h : IsNoetherianRing (q.Fiber S) ∧
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber S)) :
    IsNoetherianRing (p.Fiber S) ∧
      Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  subst hpq
  exact h

/-- The five characterizations of a regular morphism with locally Noetherian fibres. -/
@[stacks 07R8]
public theorem Scheme.Hom.regular_tfae {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) :
    List.TFAE [
      Scheme.Hom.IsRegular f,
      Flat f ∧ ∀ y : Y,
        IsGeometricallyRegular (f.fiberToSpecResidueField y),
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        IsRegularRingHom (f.appLE V U hUV).hom,
      ∃ (J : Type u) (V : J → Y.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            ∀ i, Scheme.Hom.IsRegular
              (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)),
      ∃ (J : Type u) (V : J → Y.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                IsRegularRingHom (f.appLE (V j) (U i) hUV).hom] := by
  classical
  tfae_have 1 ↔ 2 := Scheme.Hom.isRegular_iff_flat_and_geometricallyRegularFibers f
  tfae_have 2 → 3 := by
    rintro ⟨hflat, hgeo⟩ U hU V hV hUV
    let g := f.resLE V U hUV
    let : IsAffine U.toScheme := hU
    let : IsAffine V.toScheme := hV
    have hregTop : IsRegularRingHom g.appTop.hom := by
      let R := Γ(V.toScheme, ⊤)
      let S := Γ(U.toScheme, ⊤)
      let : Algebra R S := g.appTop.hom.toAlgebra
      have hflatG : Flat g := by
        let : Flat f := hflat
        infer_instance
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)] at hflatG
      have hregAlg : IsRegularRingHom (algebraMap R S) := by
        rw [isRegularRingHom_algebraMap_iff]
        refine ⟨by simpa [R, S, RingHom.algebraMap_toAlgebra] using hflatG, fun p hp => ?_⟩
        let z : PrimeSpectrum R := ⟨p, hp⟩
        let y : V.toScheme := V.toScheme.isoSpec.inv z
        have hpEq : (V.toScheme.isoSpec.hom y).asIdeal = p := by
          have hz : V.toScheme.isoSpec.hom y = z := by
            change (V.toScheme.isoSpec.inv ≫ V.toScheme.isoSpec.hom) z = z
            exact congrArg (fun q : Spec (.of R) ⟶ Spec (.of R) => q z)
              V.toScheme.isoSpec.inv_hom_id
          simpa [z] using congrArg PrimeSpectrum.asIdeal hz
        have := (V.toScheme.isoSpec.hom y).isPrime
        have hgeoFiber := geometricallyRegular_resLE_fiber f U hU V hV hUV
            (V.ι y) y.property (h (V.ι y)) (hgeo (V.ι y))
        exact affineFiberData_eq_of_ideal_eq p _ hpEq.symm
          (geometricallyRegular_affineFiber_to_algebra g y hgeoFiber.1 hgeoFiber.2)
      simpa [R, S, RingHom.algebraMap_toAlgebra] using hregAlg
    exact isRegularRingHom_of_arrowIso g.appTop.hom
      (f.appLE V U hUV).hom (arrowResLEAppIso f V U hUV) hregTop
  tfae_have 3 → 5 := by
    intro h3
    let V : Y.affineCover.I₀ → Y.Opens := fun j => (Y.affineCover.f j).opensRange
    refine ⟨Y.affineCover.I₀, V, Y.affineCover.isOpenCover_opensRange,
      fun j => isAffineOpen_opensRange (Y.affineCover.f j), fun j => ?_⟩
    let W : X.Opens := f ⁻¹ᵁ V j
    let c : W.toScheme.OpenCover := W.toScheme.affineCover
    let U : c.I₀ → X.Opens := fun i => (c.f i ≫ W.ι).opensRange
    refine ⟨c.I₀, U, ?_, fun i => isAffineOpen_opensRange (c.f i ≫ W.ι), fun i => ?_⟩
    · apply Opens.ext
      ext x
      simp only [Opens.coe_iSup, Set.mem_iUnion, U]
      change (∃ i, ∃ z, (c.f i ≫ W.ι) z = x) ↔ x ∈ W
      refine ⟨fun ⟨i, z, hz⟩ => hz ▸ (c.f i z).property, fun hx => ?_⟩
      obtain ⟨i, z, hz⟩ := c.exists_eq (⟨x, hx⟩ : W.toScheme)
      exact ⟨i, z, congrArg W.ι hz⟩
    · let hUV : U i ≤ f ⁻¹ᵁ V j := by
        intro x hx
        rcases Scheme.Hom.mem_opensRange.mp hx with ⟨z, rfl⟩
        exact (c.f i z).property
      exact h3 (U i) (isAffineOpen_opensRange (c.f i ≫ W.ι))
        (V j) (isAffineOpen_opensRange (Y.affineCover.f j)) hUV
  tfae_have 5 → 4 := by
    rintro ⟨J, V, hV, hVaff, hcover⟩
    refine ⟨J, V, hV, fun j => ?_⟩
    obtain ⟨I, U, hU, hUaff, hring⟩ := hcover j
    refine ⟨I, U, hU, fun i => ?_⟩
    let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
    let g := f.resLE (V j) (U i) hUV
    let : IsAffine (U i).toScheme := hUaff i
    let : IsAffine (V j).toScheme := hVaff j
    have hregTop : IsRegularRingHom g.appTop.hom :=
      isRegularRingHom_of_arrowIso _ _ (arrowResLEAppIso f (V j) (U i) hUV).symm
        (hring i)
    exact regular_of_regularRingHom_affine g hregTop
  tfae_have 4 → 1 := by
    rintro ⟨J, V, hV, hcover⟩ x
    obtain ⟨j, hxV⟩ := hV.exists_mem (f x)
    obtain ⟨I, U, hU, hreg⟩ := hcover j
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i from hU ▸ hxV)
    exact regularAt_resLE f (U i) (V j) ((le_iSup U i).trans hU.le) x hxi
      (h (f x)) (hreg i ⟨x, hxi⟩)
  tfae_finish

end AlgebraicGeometry
