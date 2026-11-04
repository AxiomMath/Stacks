module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorRigidity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFrobeniusDense
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# A point of a finite stage over the base coset, fixed by the geometric fundamental group

Let `X` be connected over a finite field `k`, `Y` a finite étale cover of `X` with fibre `π₁ ⧸ V`
at `x`, `r : Y ⟶ Spec k'` a structure of `Y` over a finite extension `k'` of `k` compatible with
`X ⟶ Spec k`, and `E/k'` a finite extension. The stage `Y_E = Spec E ×_{k'} Y` is finite étale over
`Y`, and it has a geometric point `e` over the base point of `Y`. Every `v ∈ V` in the geometric
fundamental group `ker(π₁(X) → π₁(Spec k))` fixes `e`: a point of `Y_E` is determined by its images
in `Y`, which `v ∈ V` fixes, and in `X_E = X ×_k E`, on whose fibre the geometric fundamental group
acts trivially.

## Main results

* `AlgebraicGeometry.exists_stagePoint`: the point and its invariance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) {x : GeometricPoint X}

omit [Fintype k] in
/-- The geometric fundamental group acts trivially on the fibres of covers pulled back from the
base. -/
theorem smul_eq_of_etaleFundamentalGroupMap_eq_one (W : FiniteEtaleOver (Spec (.of k)))
    (σ : EtaleFundamentalGroup X x) (hσ : etaleFundamentalGroupMap f x σ = 1)
    (p : (finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj W)) : σ • p = p := by
  apply (finiteEtaleFiberProjectionEquiv f x W).injective
  show finiteEtaleFiberProjection f x W ((σ.app _).hom p) = finiteEtaleFiberProjection f x W p
  rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection, hσ]
  rfl

variable {V : Subgroup (EtaleFundamentalGroup X x)} {Y : FiniteEtaleOver X}
  {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}
  (heY : ∀ (σ : EtaleFundamentalGroup X x) y, eY (σ • y) = σ • eY y)
  {K₀ : Type u} [Field K₀] [Algebra k K₀] [Module.Finite k K₀] (r : Y.left ⟶ Spec (.of K₀))
  (hr : r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)) = Y.hom ≫ f)
  {K : Type u} [Field K] [Algebra K₀ K]

include heY hr in
/-- **A point of a finite stage over the base coset, fixed by the geometric fundamental group.** -/
theorem exists_stagePoint (E : IntermediateField K₀ K) [FiniteDimensional K₀ E] :
    ∃ (hg : finiteEtale (pullback.snd (spectrumMap K₀ E) r))
      (e : x.source ⟶ pullback (spectrumMap K₀ E) r)
      (he : e ≫ pullback.snd (spectrumMap K₀ E) r = (eY.symm (QuotientGroup.mk 1)).1),
      ∀ v : V, etaleFundamentalGroupMap f x (v : EtaleFundamentalGroup X x) = 1 →
        (v : EtaleFundamentalGroup X x) • exPoint _ hg e he = exPoint _ hg e he := by
  have : Finite K₀ := Module.finite_of_finite k
  have : Fintype K₀ := Fintype.ofFinite K₀
  set y₀ := eY.symm (QuotientGroup.mk 1)
  have hE : finiteEtale (spectrumMap K₀ E) := (finiteFieldExtensionCover (k := K₀) E).prop
  have hK₀ : finiteEtale (Spec.map (CommRingCat.ofHom (algebraMap k K₀))) :=
    (finiteFieldExtensionCover (k := k) K₀).prop
  have hg : finiteEtale (pullback.snd (spectrumMap K₀ E) r) :=
    MorphismProperty.pullback_snd _ _ hE
  -- the point of `Spec E` over the image of the base point in `Spec K₀`
  let φ₀ : K₀ →+* x.residueField := (Spec.preimage (y₀.1 ≫ r)).hom
  let : Algebra K₀ x.residueField := φ₀.toAlgebra
  let φ₁ : E →ₐ[K₀] x.residueField := IsAlgClosed.lift
  let a : x.source ⟶ Spec (.of E) := Spec.map (CommRingCat.ofHom φ₁.toRingHom)
  have ha : a ≫ spectrumMap K₀ E = y₀.1 ≫ r := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap K₀ E) ≫ CommRingCat.ofHom φ₁.toRingHom =
        Spec.preimage (y₀.1 ≫ r) := by
      ext c
      exact φ₁.commutes c
    rw [this, Spec.map_preimage]
  let e : x.source ⟶ pullback (spectrumMap K₀ E) r := pullback.lift a y₀.1 ha
  have he : e ≫ pullback.snd (spectrumMap K₀ E) r = y₀.1 := pullback.lift_snd _ _ _
  refine ⟨hg, e, he, fun v hv => ?_⟩
  -- the cover `X_E` of `X` and the map of `Y_E` to it
  let W : FiniteEtaleOver (Spec (.of k)) := MorphismProperty.Over.mk ⊤
    (spectrumMap K₀ E ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)))
    (MorphismProperty.comp_mem _ _ _ hE hK₀)
  have hcomm : pullback.fst (spectrumMap K₀ E) r ≫ W.hom =
      (pullback.snd (spectrumMap K₀ E) r ≫ Y.hom) ≫ f := by
    show pullback.fst _ _ ≫ spectrumMap K₀ E ≫ _ = _
    rw [pullback.condition_assoc, hr, Category.assoc]
  let cE : FiniteEtaleOver.overComp (pullback.snd (spectrumMap K₀ E) r) hg ⟶
      (finiteEtaleBaseChange f).obj W :=
    MorphismProperty.Over.homMk (pullback.lift (pullback.fst (spectrumMap K₀ E) r)
      (pullback.snd (spectrumMap K₀ E) r ≫ Y.hom) hcomm) (pullback.lift_snd _ _ _)
  let gY : FiniteEtaleOver.overComp (pullback.snd (spectrumMap K₀ E) r) hg ⟶ Y :=
    MorphismProperty.Over.homMk (pullback.snd (spectrumMap K₀ E) r) rfl
  have hfix : (v : EtaleFundamentalGroup X x) • y₀ = y₀ := by
    apply eY.injective
    rw [heY, Equiv.apply_symm_apply]
    exact QuotientGroup.eq.2 (by simp)
  have h1 := finiteEtaleFiberFunctor_map_smul cE (v : EtaleFundamentalGroup X x) (exPoint _ hg e he)
  rw [smul_eq_of_etaleFundamentalGroupMap_eq_one f W _ hv] at h1
  have h2 := finiteEtaleFiberFunctor_map_smul gY (v : EtaleFundamentalGroup X x) (exPoint _ hg e he)
  have h3 : (finiteEtaleFiberFunctor x).map gY (exPoint _ hg e he) = y₀ := Subtype.ext he
  rw [h3, hfix] at h2
  apply Subtype.ext
  apply pullback.hom_ext
  · have key : cE.left ≫ pullback.fst W.hom f = pullback.fst (spectrumMap K₀ E) r :=
      pullback.lift_fst _ _ _
    have h4 : ((v : EtaleFundamentalGroup X x) • exPoint _ hg e he).1 ≫ cE.left ≫
        pullback.fst W.hom f = (exPoint _ hg e he).1 ≫ cE.left ≫ pullback.fst W.hom f := by
      have := congrArg (fun p => p.1 ≫ pullback.fst W.hom f) h1
      simp only [finiteEtaleFiberFunctor_map_val] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)).symm
    rwa [key] at h4
  · exact (congrArg Subtype.val h2).trans he.symm

end AlgebraicGeometry
