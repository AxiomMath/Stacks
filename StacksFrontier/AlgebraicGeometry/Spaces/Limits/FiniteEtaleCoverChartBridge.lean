module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteEtaleCoverStratificationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineOpenImmersionAffineOver
public import StacksFrontier.RingTheory.Etale.QuotientColimitDescent

/-!
# Reading a finite morphism over a closed subspace on an affine étale chart

Let `g : T ⟶ X` be a finite morphism from a scheme to an algebraic space, `q : V ⟶ X` an étale
morphism from an affine scheme, and `T_q = V ×_X T` the (affine) chart of `g`. For a closed
subspace `Z ⊆ X` with chart `Z_q = V ×_X Z ⊆ V`, the base change `T ×_X Z ⟶ Z` of `g` has, along
the étale chart `Z_q ⟶ Z`, the base change `P_q = T_q ×_V Z_q ⟶ Z_q`. This file builds that
square and shows that the base change of `g` to `Z` is étale at every point over the image of the
chart, resp. surjective onto the points of `Z` in that image, exactly when `P_q ⟶ Z_q` is étale,
resp. surjective.

## Main results

* `AlgebraicGeometry.Space.exists_chartSquare`: the square.
* `AlgebraicGeometry.Space.etale_toScheme_of_forall_isEtaleAt` and
  `AlgebraicGeometry.Space.isEtaleAt_of_etale_toScheme`: étaleness.
* `AlgebraicGeometry.Space.surjective_toScheme_iff`: surjectivity.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A cone `(u, v)` over the cospan `(f, g)` whose projection `v` to `g` is the base change of
`g` along `ζ ≫ f`, with `b ≫ ζ = u`, is the pullback of `fst f g` along `ζ`. -/
private theorem isPullback_pullback_lift {C : Type*} [Category C] {A X' Y R P : C} {f : A ⟶ X'}
    {g : Y ⟶ X'} [HasPullback f g] {u : P ⟶ A} {v : P ⟶ Y} {b : P ⟶ R} {ζ : R ⟶ A}
    (w : u ≫ f = v ≫ g) (hu : b ≫ ζ = u) (sq : IsPullback v b g (ζ ≫ f)) :
    IsPullback (pullback.lift u v w) b (pullback.fst f g) ζ := by
  refine IsPullback.of_right (h₁₂ := pullback.snd f g) (v₁₃ := g) ?_ ?_
    (IsPullback.of_hasPullback f g).flip
  · rwa [pullback.lift_snd]
  · rw [pullback.lift_fst, hu]

/-- **The chart square of a finite morphism over a closed subspace.** Given the chart
`T_q ⟶ V` of `g` along `q`, and a closed subspace `Z`, there are the chart `Z_q ⟶ V` of `Z`, the
scheme `P_q = T_q ×_V Z_q`, a cartesian square of schemes over `V`, and a cartesian square
exhibiting `P_q ⟶ Z_q` as the base change of `T ×_X Z ⟶ Z` along `Z_q ⟶ Z`. -/
theorem exists_chartSquare {V T Tq : BigFppfOver B S hS} {q : yoneda.obj V ⟶ X}
    {g : yoneda.obj T ⟶ X} {pT : Tq ⟶ V} {iT : yoneda.obj Tq ⟶ yoneda.obj T}
    (sqT : IsPullback iT (yoneda.map pT) g q) {Z : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z) :
    ∃ (Zq Pq : BigFppfOver B S hS) (z : Zq ⟶ V) (a : Pq ⟶ Tq) (b : Pq ⟶ Zq)
      (ζ : yoneda.obj Zq ⟶ Z.toFunctor) (k : yoneda.obj Pq ⟶ pullback Z.ι g),
      RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom =
        RingHom.ker ((BigFppfOver.toScheme B S hS).map (hZ.2.1.snd q)).appTop.hom ∧
      IsPullback ζ (yoneda.map z) Z.ι q ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map z) ∧
      IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map pT) (yoneda.map z) ∧
      IsPullback k (yoneda.map b) (pullback.fst Z.ι g) ζ := by
  have hrep := hZ.2.1
  let Zq := hrep.pullback q
  let z : Zq ⟶ V := hrep.snd q
  let ζ : yoneda.obj Zq ⟶ Z.toFunctor := hrep.fst q
  have sqZ : IsPullback ζ (yoneda.map z) Z.ι q := hrep.isPullback q
  let Pq := hrep.pullback (yoneda.map pT ≫ q)
  let a : Pq ⟶ Tq := hrep.snd (yoneda.map pT ≫ q)
  let ξ : yoneda.obj Pq ⟶ Z.toFunctor := hrep.fst (yoneda.map pT ≫ q)
  have sqP : IsPullback ξ (yoneda.map a) Z.ι (yoneda.map pT ≫ q) :=
    hrep.isPullback (yoneda.map pT ≫ q)
  let b' : yoneda.obj Pq ⟶ yoneda.obj Zq :=
    sqZ.lift ξ (yoneda.map a ≫ yoneda.map pT) (by rw [sqP.w, Category.assoc])
  let b : Pq ⟶ Zq := Yoneda.fullyFaithful.preimage b'
  have hb : yoneda.map b = b' := Yoneda.fullyFaithful.map_preimage b'
  have hbζ : yoneda.map b ≫ ζ = ξ := by
    rw [hb]
    exact sqZ.lift_fst _ _ _
  have hbz : yoneda.map b ≫ yoneda.map z = yoneda.map a ≫ yoneda.map pT := by
    rw [hb]
    exact sqZ.lift_snd _ _ _
  have sqPZ : IsPullback (yoneda.map b) (yoneda.map a) (yoneda.map z) (yoneda.map pT) :=
    IsPullback.of_right (hbζ.symm ▸ sqP) hbz sqZ
  let k : yoneda.obj Pq ⟶ pullback Z.ι g :=
    pullback.lift ξ (yoneda.map a ≫ iT) (by rw [sqP.w, Category.assoc, sqT.w])
  have sqk : IsPullback k (yoneda.map b) (pullback.fst Z.ι g) ζ :=
    isPullback_pullback_lift _ hbζ (by rw [sqZ.w]; exact sqPZ.flip.paste_horiz sqT)
  exact ⟨Zq, Pq, z, a, b, ζ, k, rfl, sqZ, hZ.2.2 q ζ z sqZ, sqPZ.flip, sqk⟩

section Bridge

variable {Z : Subfunctor X} {T Zq Pq : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X}
  {b : Pq ⟶ Zq} {ζ : yoneda.obj Zq ⟶ Z.toFunctor} {k : yoneda.obj Pq ⟶ pullback Z.ι g}

/-- **Étaleness over the chart from pointwise étaleness.** If the base change of `g` to `Z` is
étale at every point over the image of `Z_q`, then `P_q ⟶ Z_q` is étale. -/
theorem etale_toScheme_of_forall_isEtaleAt
    (sqk : IsPullback k (yoneda.map b) (pullback.fst Z.ι g) ζ)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor) (hP : IsAlgebraicSpace B S hS (pullback Z.ι g))
    (h : ∀ t : points B S hS (pullback Z.ι g),
      pointsMap B S hS _ (pullback.fst Z.ι g) t ∈ Set.range (pointsMap B S hS _ ζ) →
        IsEtaleAt B S hS (pullback.fst Z.ι g) t) :
    Etale ((BigFppfOver.toScheme B S hS).map b) := by
  refine etale_of_isEtale_yoneda_map B S hS ?_
  refine (isEtale_iff_forall_isEtaleAt B S hS (isAlgebraicSpace_yoneda B S hS Pq)
    (isAlgebraicSpace_yoneda B S hS Zq) (yoneda.map b)).2 fun p => ?_
  refine IsEtaleAt.of_isPullback sqk (isAlgebraicSpace_yoneda B S hS Pq) hP
    (isAlgebraicSpace_yoneda B S hS Zq) hZ (h _ ⟨pointsMap B S hS _ (yoneda.map b) p, ?_⟩)
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, sqk.w]

/-- **Pointwise étaleness from étaleness over the chart.** If `P_q ⟶ Z_q` is étale, then the base
change of `g` to `Z` is étale at every point over the image of the étale chart `Z_q ⟶ Z`. -/
theorem isEtaleAt_of_etale_toScheme
    (sqk : IsPullback k (yoneda.map b) (pullback.fst Z.ι g) ζ)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor) (hP : IsAlgebraicSpace B S hS (pullback Z.ι g))
    (hζ : IsEtale B S hS ζ) (hb : Etale ((BigFppfOver.toScheme B S hS).map b))
    (t : points B S hS (pullback Z.ι g))
    (ht : pointsMap B S hS _ (pullback.fst Z.ι g) t ∈ Set.range (pointsMap B S hS _ ζ)) :
    IsEtaleAt B S hS (pullback.fst Z.ι g) t := by
  let O : Subfunctor Z.toFunctor :=
    openSubspaceOfPoints B S hS Z.toFunctor (Set.range (pointsMap B S hS _ ζ))
  have hO : IsOpenSubspace B S hS O :=
    isOpenSubspace_openSubspaceOfPoints_range_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS Zq) hZ hζ
  have hOpts : Set.range (pointsMap B S hS O.toFunctor O.ι) = Set.range (pointsMap B S hS _ ζ) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  let ζ' : yoneda.obj Zq ⟶ O.toFunctor :=
    Subfunctor.lift ζ (range_le_openSubspaceOfPoints_range_pointsMap ζ)
  have hζ' : ζ' ≫ O.ι = ζ := Subfunctor.lift_ι _ _
  let fZ := pullback.fst Z.ι g
  let fO := pullback.fst O.ι fZ
  let k' : yoneda.obj Pq ⟶ pullback O.ι fZ :=
    pullback.lift (yoneda.map b ≫ ζ') k (by rw [Category.assoc, hζ', sqk.w])
  have sq' : IsPullback k' (yoneda.map b) fO ζ' :=
    isPullback_pullback_lift _ rfl (by rwa [hζ'])
  have hfO : IsEtale B S hS fO := by
    refine (isEtale_iff_exists_target_chart B S hS
      (isAlgebraicSpace_pullback B S hS _ _ hO.1 hP hZ) hO.1 fO).2 ⟨Zq, ζ', ?_, ?_, ?_⟩
    · refine (presheafSurjective_iff_isSurjective_yoneda B S hS O.toFunctor hO.1 Zq ζ').2
        fun o => ?_
      obtain ⟨w, hw⟩ : pointsMap B S hS _ O.ι o ∈ Set.range (pointsMap B S hS _ ζ) :=
        hOpts ▸ ⟨o, rfl⟩
      refine ⟨w, pointsMap_injective_of_mono B S hS O.ι ?_⟩
      rw [← pointsMap_comp_apply, hζ', hw]
    · exact (isEtale_iff_presheaf_of_yoneda B S hS ζ').1
        (isEtale_of_comp_mono B S hS ζ' O.ι (by rwa [hζ']))
    · have he : pullback.snd fO ζ' = sq'.isoPullback.inv ≫ yoneda.map b := by
        rw [IsPullback.isoPullback_inv_snd]
      rw [he]
      exact isEtale_comp B S hS (isEtale_of_iso B S hS sq'.isoPullback.symm)
        (isEtale_of_presheaf_etale B S hS
          ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Etale.{u}) b).2 hb))
  exact isEtaleAt_of_isEtale_pullback_fst B S hS hZ hP O hO fZ hfO t (by rwa [hOpts])

/-- **Surjectivity over the chart.** The points of `Z` over the image of the chart lie in the
image of the base change of `g` exactly when `P_q ⟶ Z_q` is surjective. -/
theorem surjective_toScheme_iff (sqk : IsPullback k (yoneda.map b) (pullback.fst Z.ι g) ζ) :
    (∀ z : points B S hS (yoneda.obj Zq),
        pointsMap B S hS _ ζ z ∈ Set.range (pointsMap B S hS _ (pullback.fst Z.ι g))) ↔
      Function.Surjective ((BigFppfOver.toScheme B S hS).map b) := by
  rw [← surjective_pointsMap_yoneda_iff B S hS b]
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · obtain ⟨t, ht⟩ := h z
    obtain ⟨p, -, hp⟩ := exists_points_of_isPullback B S hS sqk t z ht
    exact ⟨p, hp⟩
  · obtain ⟨p, rfl⟩ := h z
    refine ⟨pointsMap B S hS _ k p, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, sqk.w]

end Bridge

/-! ### From the chart square to rings -/

/-- A morphism of affine schemes is surjective exactly when the map of prime spectra of its ring
map of global functions is. -/
theorem surjective_iff_surjective_comap_appTop {X' Y' : Scheme.{u}} [IsAffine X'] [IsAffine Y']
    (f : X' ⟶ Y') :
    Function.Surjective f ↔ Function.Surjective (PrimeSpectrum.comap f.appTop.hom) := by
  have hfun : (Spec.map f.appTop : _ → _) ∘ X'.isoSpec.hom = Y'.isoSpec.hom ∘ f := by
    funext x
    exact congrArg (fun φ : X' ⟶ Spec Γ(Y', ⊤) => φ x)
      (Scheme.isoSpec_hom_naturality f)
  have hY : Function.Bijective (Y'.isoSpec.hom : Y' → Spec Γ(Y', ⊤)) :=
    Y'.isoSpec.hom.homeomorph.bijective
  have hspec : (Spec.map f.appTop : Spec Γ(X', ⊤) → Spec Γ(Y', ⊤)) =
      PrimeSpectrum.comap f.appTop.hom := rfl
  rw [← hspec]
  refine ⟨fun hf => ?_, fun hs => ?_⟩
  · have h' : Function.Surjective ((Spec.map f.appTop : _ → _) ∘ X'.isoSpec.hom) := by
      rw [hfun]
      exact hY.2.comp hf
    exact h'.of_comp
  · have h' : Function.Surjective ((Y'.isoSpec.hom : Y' → _) ∘ f) := by
      rw [← hfun]
      exact hs.comp X'.isoSpec.hom.homeomorph.bijective.2
    exact h'.of_comp_left hY.1

variable {V Tq Zq Pq : BigFppfOver B S hS} {pT : Tq ⟶ V} {z : Zq ⟶ V} {a : Pq ⟶ Tq}
  {b : Pq ⟶ Zq}

/-- **The chart square read on rings.** For the cartesian square `P_q = T_q ×_V Z_q` with `V` and
`T_q` affine and `Z_q ⟶ V` a closed immersion with kernel `K` on global functions, `P_q ⟶ Z_q` is
étale, resp. surjective, exactly when `Γ(V) ⧸ K ⟶ (Γ(V) ⧸ K) ⊗ Γ(T_q)` is étale, resp. surjective
on spectra. -/
theorem etale_and_surjective_toScheme_iff [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Tq)]
    [hz : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map z)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤)]
    (hA : algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤) =
        ((BigFppfOver.toScheme B S hS).map pT).appTop.hom)
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map pT) (yoneda.map z)) :
    (Etale ((BigFppfOver.toScheme B S hS).map b) ↔
      (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
          RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom)
        (TensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
            RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom)
          Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤))).Etale) ∧
    (Function.Surjective ((BigFppfOver.toScheme B S hS).map b) ↔
      Function.Surjective (PrimeSpectrum.comap
        (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
          RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom)
        (TensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
            RingHom.ker ((BigFppfOver.toScheme B S hS).map z).appTop.hom)
          Γ((BigFppfOver.toScheme B S hS).obj Tq, ⊤))))) := by
  let T := BigFppfOver.toScheme B S hS
  have sch : IsPullback (T.map a) (T.map b) (T.map pT) (T.map z) :=
    isPullback_map_toScheme_of_isPullback_yoneda B S hS h
  obtain ⟨_, hzs⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (T.map z)
  have : IsAffine (T.obj Pq) := .of_isPullback sch
  let : Algebra Γ(T.obj V, ⊤) Γ(T.obj Zq, ⊤) := (T.map z).appTop.hom.toAlgebra
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap Γ(T.obj V, ⊤) Γ(T.obj Zq, ⊤)))
      (CommRingCat.ofHom (algebraMap Γ(T.obj V, ⊤) Γ(T.obj Tq, ⊤)))
      (CommRingCat.ofHom (T.map b).appTop.hom) (CommRingCat.ofHom (T.map a).appTop.hom) := by
    rw [hA]
    exact (isPushout_appTop_of_isPullback sch).flip
  refine ⟨?_, ?_⟩
  · rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    exact Ideal.etale_iff_etale_quotient_tensor_of_isPushout hzs _ _ hpo'
  · rw [surjective_iff_surjective_comap_appTop]
    exact Ideal.surjective_comap_iff_quotient_tensor_of_isPushout hzs _ _ hpo'

end AlgebraicGeometry.Space

end
