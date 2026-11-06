module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGalois
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGaloisAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Galois-fixed geometric connected components

Let `k` be a field with separable algebraic closure `kbar`, and let `X` be a scheme over `k`.
A connected component of `X_kbar` is fixed by the canonical action of the Galois group exactly
when it is the inverse image of a connected component of `X` which is geometrically connected
over `k`.

## Main definitions

* `AlgebraicGeometry.IsGeometricallyConnectedSubset` is geometric connectedness of a subset of a
  scheme over a field.

## Main results

* `AlgebraicGeometry.galoisActionOnGeometricConnectedComponents_fixed_iff` characterizes the
  components fixed by the Galois action.
* `AlgebraicGeometry.surjective_baseChange_fst` and
  `AlgebraicGeometry.surjective_baseChangeComparison` record surjectivity of the projection of a
  base change along a field extension and of the comparison map of a tower.

## Implementation notes

A connected component of a scheme is not in general an open subscheme, and the reduced induced
structure on a closed subset is not available, so geometric connectedness of a subset is stated
topologically: the inverse image of the subset in the base change along every field extension of
the ground field is connected. Taken on the whole space this is the topological content of
Mathlib's `AlgebraicGeometry.GeometricallyConnected`.

The component `T` of the first assertion is produced by descending the Galois-invariant closed
subset `Tbar` along the projection `q : X_kbar ⟶ X`. That the descended subset is a whole
connected component is the content of `eq_connectedComponent_of_preimage_eq`, which isolates the
topological input: `q` is surjective, open and closed, and `q` has no fibre meeting `Tbar` only
partially. Its proof uses the clopen-image criterion of Tag 038C.

Geometric connectedness of `T` is checked by comparing an arbitrary extension `K/k` with the
separable closure of `K`, into which `kbar` embeds over `k`: the inverse image of `T` upstairs is
a connected component because the comparison map on connected components is bijective over a
separably closed field, and the inverse image of `T` in `X_K` is its image under the surjective
comparison map.

## References

* [Stacks Project, Tag 038D](https://stacks.math.columbia.edu/tag/038D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A subset `T` of a scheme `X` over a field `k` is geometrically connected when its inverse
image in the base change of `X` along every field extension of `k` is connected. -/
public def IsGeometricallyConnectedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (T : Set X) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    _root_.IsConnected (⇑(pullback.fst f (spectrumMap k K)) ⁻¹' T)

/-- The projection of a base change along a field extension is surjective. -/
public theorem surjective_baseChange_fst (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Function.Surjective ⇑(pullback.fst f (spectrumMap k K)) := by
  have : Surjective (pullback.fst f (spectrumMap k K)) := inferInstance
  exact Scheme.Hom.surjective _

/-- Evaluating an equation `f ≫ g = h` of morphisms of schemes at a point. -/
private theorem apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (H : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← H]
  rfl

/-- The comparison map commutes with the projections to `X`. -/
private theorem baseChangeComparison_comp_fst
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    baseChangeComparison k K Ω X f ≫ pullback.fst f (spectrumMap k K) =
      pullback.fst f (spectrumMap k Ω) := pullback.lift_fst _ _ _

/-- The comparison map is compatible with the projections to the base fields. -/
private theorem baseChangeComparison_comp_snd
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    baseChangeComparison k K Ω X f ≫ pullback.snd f (spectrumMap k K) =
      pullback.snd f (spectrumMap k Ω) ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
  pullback.lift_snd _ _ _

/-- The comparison map between the base changes along a tower of field extensions is
surjective. -/
public theorem surjective_baseChangeComparison
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Function.Surjective ⇑(baseChangeComparison k K Ω X f) := by
  have hcomp : spectrumMap k Ω =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ spectrumMap k K := by
    show Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k K Ω)
  have hfac := baseChangeTowerIsoTo_comp_of_projection f (spectrumMap k K)
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (spectrumMap k Ω) hcomp
    (baseChangeComparison k K Ω X f) (baseChangeComparison_comp_fst k K Ω X f)
    (baseChangeComparison_comp_snd k K Ω X f)
  have hts : Function.Surjective ⇑(pullback.fst (pullback.snd f (spectrumMap k K))
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := Scheme.Hom.surjective _
  intro y
  obtain ⟨w, hw⟩ := hts y
  refine ⟨(baseChangeTowerIsoTo f (spectrumMap k K)
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (spectrumMap k Ω) hcomp).hom.base w, ?_⟩
  exact (apply_eq_of_comp_eq hfac w).trans hw

/-- A subset whose inverse image along a surjective, open and closed morphism is a connected
component is itself a connected component. -/
public theorem eq_connectedComponent_of_preimage_eq
    {Y Z : Scheme.{u}} (q : Y ⟶ Z) (hsurj : Function.Surjective ⇑q)
    (hopen : IsOpenMap ⇑q) (hclosed : IsClosedMap ⇑q)
    (T : Set Z) (ybar : Y) (hT : ⇑q ⁻¹' T = connectedComponent ybar) :
    ∃ x : Z, T = connectedComponent x := by
  have hTimg : T = ⇑q '' connectedComponent ybar := by
    rw [← hT, Set.image_preimage_eq _ hsurj]
  have hTconn : _root_.IsConnected T := by
    rw [hTimg]
    exact isConnected_connectedComponent.image _ q.continuous.continuousOn
  obtain ⟨x₀, hx₀⟩ := hTconn.nonempty
  refine ⟨x₀, ?_⟩
  have hsub : T ⊆ connectedComponent x₀ := hTconn.isPreconnected.subset_connectedComponent hx₀
  have hsub' : connectedComponent ybar ⊆ ⇑q ⁻¹' connectedComponent x₀ := by
    rw [← hT]
    exact Set.preimage_mono hsub
  have hyB : ybar ∈ ⇑q ⁻¹' connectedComponent x₀ := hsub' mem_connectedComponent
  have hconnA : ConnectedSpace ↥(connectedComponent ybar) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hconnC : ConnectedSpace ↥(connectedComponent x₀) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hBconn : ConnectedSpace ↥(⇑q ⁻¹' connectedComponent x₀) := by
    refine connectedSpace_of_clopen_image (Set.inclusion hsub')
      (Set.restrictPreimage (connectedComponent x₀) ⇑q) (continuous_inclusion hsub') ?_ ?_
    · intro U hU
      exact ⟨hclosed.restrictPreimage _ U hU.isClosed, hopen.restrictPreimage _ U hU.isOpen⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hqb : q b = q a := congrArg Subtype.val hab
      have haT : q a ∈ T := by
        have h : a ∈ ⇑q ⁻¹' T := by rw [hT]; exact ha
        exact h
      refine ⟨⟨b, ?_⟩, rfl⟩
      have h : b ∈ ⇑q ⁻¹' T := by
        show q b ∈ T
        rw [hqb]
        exact haT
      rw [hT] at h
      exact h
  have hBsub : ⇑q ⁻¹' connectedComponent x₀ ⊆ connectedComponent ybar :=
    (isConnected_iff_connectedSpace.mpr hBconn).isPreconnected.subset_connectedComponent hyB
  have hBeq : ⇑q ⁻¹' connectedComponent x₀ = ⇑q ⁻¹' T := by
    refine Set.Subset.antisymm ?_ (Set.preimage_mono hsub)
    rw [hT]
    exact hBsub
  exact (Set.preimage_injective.mpr hsurj hBeq).symm

/-- Over a separably closed field, a subset whose inverse image in one base change is a connected
component has the same property after any further field extension. -/
@[ega "IV 4.4.5" "partial, special case"]
private lemma exists_preimage_eq_connectedComponent_of_tower
    (k kbar Ω : Type u) [Field k] [Field kbar] [Field Ω]
    [Algebra k kbar] [Algebra k Ω] [Algebra kbar Ω] [IsScalarTower k kbar Ω]
    [IsSepClosed kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (T : Set X)
    (ybar : (pullback f (spectrumMap k kbar) : Scheme.{u}))
    (hT : ⇑(pullback.fst f (spectrumMap k kbar)) ⁻¹' T = connectedComponent ybar) :
    ∃ z : (pullback f (spectrumMap k Ω) : Scheme.{u}),
      ⇑(pullback.fst f (spectrumMap k Ω)) ⁻¹' T = connectedComponent z := by
  have hbij := baseChangeComparison_connectedComponents_bijective k kbar Ω (Over.mk f)
    (baseChangeComparison k kbar Ω X f) (baseChangeComparison_comp_fst k kbar Ω X f)
    (baseChangeComparison_comp_snd k kbar Ω X f)
  obtain ⟨C₀, hC₀⟩ := hbij.2 (ConnectedComponents.mk ybar)
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe C₀
  refine ⟨z, ?_⟩
  have hzy : ConnectedComponents.mk ((baseChangeComparison k kbar Ω X f).base z) =
      ConnectedComponents.mk ybar := hC₀
  ext w
  simp only [Set.mem_preimage, ← apply_eq_of_comp_eq (baseChangeComparison_comp_fst k kbar Ω X f) w]
  rw [← Set.mem_preimage (f := ⇑(pullback.fst f (spectrumMap k kbar))), hT,
    ← ConnectedComponents.coe_eq_coe', ← ConnectedComponents.coe_eq_coe', ← hzy]
  exact hbij.1.eq_iff (a := ConnectedComponents.mk w) (b := ConnectedComponents.mk z)

/-- A subset whose inverse image in the base change to a separable algebraic closure is a
connected component is geometrically connected. -/
@[ega "IV 4.4.5" "special case"]
public theorem isGeometricallyConnectedSubset_of_preimage_eq_connectedComponent
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsSepClosure k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (T : Set X)
    (ybar : (pullback f (spectrumMap k kbar) : Scheme.{u}))
    (hT : ⇑(pullback.fst f (spectrumMap k kbar)) ⁻¹' T = connectedComponent ybar) :
    IsGeometricallyConnectedSubset f T := by
  have hsep : IsSepClosed kbar := IsSepClosure.sep_closed k
  intro K _ _
  let : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι : kbar →ₐ[k] SeparableClosure K := IsSepClosed.lift
  let : Algebra kbar (SeparableClosure K) := ι.toRingHom.toAlgebra
  have : IsScalarTower k kbar (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨z, hz⟩ :=
    exists_preimage_eq_connectedComponent_of_tower k kbar (SeparableClosure K) f T ybar hT
  have hsurj := surjective_baseChangeComparison k K (SeparableClosure K) X f
  have hpre : ⇑(baseChangeComparison k K (SeparableClosure K) X f) ⁻¹'
      (⇑(pullback.fst f (spectrumMap k K)) ⁻¹' T) =
        ⇑(pullback.fst f (spectrumMap k (SeparableClosure K))) ⁻¹' T := by
    ext w
    simp only [Set.mem_preimage,
      apply_eq_of_comp_eq (baseChangeComparison_comp_fst k K (SeparableClosure K) X f) w]
  rw [← Set.image_preimage_eq (⇑(pullback.fst f (spectrumMap k K)) ⁻¹' T) hsurj, hpre, hz]
  exact isConnected_connectedComponent.image _
    (baseChangeComparison k K (SeparableClosure K) X f).continuous.continuousOn

/-- The Galois action on the base change to `kbar` commutes with the projection to `X`. -/
private theorem galoisActionOnBaseChange_fst_apply
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar]
    (X : Over (Spec (.of k))) (σ : MulOpposite (kbar ≃ₐ[k] kbar))
    (y : (galoisActionOnBaseChange k kbar X).V) :
    (pullback.fst X.hom (spectrumMap k kbar))
        (((galoisActionOnBaseChange k kbar X).ρ σ).asHom.base y) =
      (pullback.fst X.hom (spectrumMap k kbar)) y := by
  exact apply_eq_of_comp_eq (galoisBaseChangeMap_fst k kbar X.left X.hom σ.unop) y

/-- The Galois action on connected components is induced by the action on the base change. -/
private theorem galoisActionOnGeometricConnectedComponents_mk
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar]
    (X : Over (Spec (.of k))) (σ : MulOpposite (kbar ≃ₐ[k] kbar))
    (y : (galoisActionOnBaseChange k kbar X).V) :
    ConcreteCategory.hom ((galoisActionOnGeometricConnectedComponents k kbar X).ρ σ).asHom
        (ConnectedComponents.mk y) =
      ConnectedComponents.mk (((galoisActionOnBaseChange k kbar X).ρ σ).asHom.base y) := rfl

/-- A connected component of the base change to a separable algebraic closure `kbar` which is
fixed by the Galois action is the inverse image of a geometrically connected component of `X`. -/
private theorem exists_connectedComponent_preimage_eq_of_galois_fixed
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsSepClosure k kbar]
    (X : Over (Spec (.of k)))
    (C : ConnectedComponents (galoisActionOnBaseChange k kbar X).V)
    (hfix : ∀ σ : MulOpposite (kbar ≃ₐ[k] kbar),
        ConcreteCategory.hom
          ((galoisActionOnGeometricConnectedComponents k kbar X).ρ σ).asHom C = C) :
    ∃ T : Set X.left, (∃ x : X.left, T = connectedComponent x) ∧
      IsGeometricallyConnectedSubset X.hom T ∧
      ⇑(pullback.fst X.hom (spectrumMap k kbar)) ⁻¹' T = ConnectedComponents.mk ⁻¹' {C} := by
  have hgal : IsGalois k kbar := inferInstance
  obtain ⟨y₀, hy₀⟩ := ConnectedComponents.surjective_coe C
  have hTbar_eq : (ConnectedComponents.mk ⁻¹' {C} :
      Set (galoisActionOnBaseChange k kbar X).V) = connectedComponent y₀ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ConnectedComponents.coe_eq_coe'.1 (h.trans hy₀.symm),
      fun h => (ConnectedComponents.coe_eq_coe'.2 h).trans hy₀⟩
  have hTbar_closed : IsClosed (ConnectedComponents.mk ⁻¹' {C} :
      Set (galoisActionOnBaseChange k kbar X).V) := by
    rw [hTbar_eq]
    exact isClosed_connectedComponent
  let : MulAction (MulOpposite (kbar ≃ₐ[k] kbar))
      (galoisActionOnGeometricConnectedComponents k kbar X).V :=
    Action.instMulAction (galoisActionOnGeometricConnectedComponents k kbar X)
  have hinj : ∀ σ : MulOpposite (kbar ≃ₐ[k] kbar),
      Function.Injective (fun z : (galoisActionOnGeometricConnectedComponents k kbar X).V =>
        ConcreteCategory.hom
          ((galoisActionOnGeometricConnectedComponents k kbar X).ρ σ).asHom z) :=
    fun σ => MulAction.injective σ
  have hstable : ∀ σ : kbar ≃ₐ[k] kbar,
      ⇑(galoisBaseChangeMap k kbar X.left X.hom σ) ⁻¹'
          (ConnectedComponents.mk ⁻¹' {C}) = ConnectedComponents.mk ⁻¹' {C} := by
    intro σ
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hmk := galoisActionOnGeometricConnectedComponents_mk k kbar X (MulOpposite.op σ) y
    exact ⟨fun h => hinj (MulOpposite.op σ)
        ((hmk.trans h).trans (hfix (MulOpposite.op σ)).symm),
      fun h => (hmk.symm.trans
        (congrArg (ConcreteCategory.hom
          ((galoisActionOnGeometricConnectedComponents k kbar X).ρ (MulOpposite.op σ)).asHom)
          h)).trans (hfix (MulOpposite.op σ))⟩
  obtain ⟨T, -, hTpre⟩ :=
    exists_closed_subset_with_preimage_eq_of_galois_invariant k kbar X.left X.hom
      (ConnectedComponents.mk ⁻¹' {C}) hTbar_closed hstable
  have hint : IsIntegralHom (spectrumMap k kbar) := by
    show IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr ⟨IsGalois.integral k⟩
  have hT' : ⇑(pullback.fst X.hom (spectrumMap k kbar)) ⁻¹' T = connectedComponent y₀ := by
    rw [hTpre, hTbar_eq]
  exact ⟨T, eq_connectedComponent_of_preimage_eq _
    (surjective_baseChange_fst k kbar X.hom)
    (pullback.fst X.hom (spectrumMap k kbar)).isOpenMap
    (pullback.fst X.hom (spectrumMap k kbar)).isClosedMap T y₀ hT',
    isGeometricallyConnectedSubset_of_preimage_eq_connectedComponent k kbar X.hom T y₀ hT',
    hTpre⟩

/-- **Stacks Project, Tag 038D.** A connected component of the base change of `X` to a separable
algebraic closure `kbar` of `k` is fixed by the Galois action if and only if it is the inverse
image of a connected component of `X` which is geometrically connected over `k`. -/
@[stacks 038D "fixed_components"]
public theorem galoisActionOnGeometricConnectedComponents_fixed_iff
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsSepClosure k kbar]
    (X : Over (Spec (.of k)))
    (C : ConnectedComponents (galoisActionOnBaseChange k kbar X).V) :
    (∀ σ : MulOpposite (kbar ≃ₐ[k] kbar),
        ConcreteCategory.hom
          ((galoisActionOnGeometricConnectedComponents k kbar X).ρ σ).asHom C = C) ↔
      ∃ T : Set X.left, (∃ x : X.left, T = connectedComponent x) ∧
        IsGeometricallyConnectedSubset X.hom T ∧
        ⇑(pullback.fst X.hom (spectrumMap k kbar)) ⁻¹' T =
          ConnectedComponents.mk ⁻¹' {C} := by
  refine ⟨exists_connectedComponent_preimage_eq_of_galois_fixed k kbar X C, ?_⟩
  rintro ⟨T, -, -, hTpre⟩ σ
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe C
  refine (galoisActionOnGeometricConnectedComponents_mk k kbar X σ y).trans ?_
  have hy : y ∈ ⇑(pullback.fst X.hom (spectrumMap k kbar)) ⁻¹' T := by
    rw [hTpre]
    exact rfl
  have hy2 : ((galoisActionOnBaseChange k kbar X).ρ σ).asHom.base y ∈
      ⇑(pullback.fst X.hom (spectrumMap k kbar)) ⁻¹' T := by
    show (pullback.fst X.hom (spectrumMap k kbar))
      (((galoisActionOnBaseChange k kbar X).ρ σ).asHom.base y) ∈ T
    rw [galoisActionOnBaseChange_fst_apply k kbar X σ y]
    exact hy
  rwa [hTpre] at hy2

end AlgebraicGeometry

end
