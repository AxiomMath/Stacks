module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Blowup.CentreFromGlobalIdeal

/-!
# Lifting a closed subspace of finite presentation of a closed subspace

Let `P` be a quasi-compact and quasi-separated algebraic space and `Y ⊆ D ⊆ P` closed subspaces
such that `Y` is of finite presentation inside `D`. Then there is a closed subspace `T ⊆ P` of
finite presentation with `Y ⊆ T` and `T ∩ D ⊆ Y`, so `T ∩ D = Y`: the finitely many generators of
the ideal of `Y` in `D` on an affine chart are lifted to the chart of `P`, and the ideal-sheaf form
of Stacks 0829 (`AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`) produces `T`.

## Main results

* `AlgebraicGeometry.Space.mem_idealPoints_ofIdealTop_iff`: a morphism to an affine scheme factors
  through the closed subscheme cut out by an ideal of global functions exactly when it kills the
  ideal.
* `AlgebraicGeometry.Space.exists_isFinitePresentation_inf_le`: the statement above.

## References

* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Along a surjective ring map, a finitely generated ideal of the target is the image of a
finitely generated ideal of the source. -/
private theorem Ideal.exists_fg_map_eq_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Surjective f) {L : Ideal B} (hL : L.FG) :
    ∃ J : Ideal A, J.FG ∧ J.map f = L := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨Ideal.span (Function.surjInv hf '' s), ⟨s.image (Function.surjInv hf), by simp⟩, ?_⟩
  rw [Ideal.map_span, ← Set.image_comp, Function.comp_surjInv, Set.image_id]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Factoring through the closed subscheme of an ideal of global functions.** For `W` affine and
`I` an ideal of `Γ(W)`, a morphism `x : T ⟶ W` lies in the closed subscheme cut out by `I` exactly
when its ring map on global functions kills `I`. -/
theorem mem_idealPoints_ofIdealTop_iff {W T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) (x : T ⟶ W) :
    x ∈ (idealPoints B S hS (Scheme.IdealSheafData.ofIdealTop I)).obj (op T) ↔
      I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map x).appTop.hom := by
  rw [mem_subschemePoints_iff, Subobject.mk_factors_iff]
  have hJ : (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top _⟩ = I :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply I
  constructor
  · rintro ⟨l, hl⟩
    have hle : I ≤ RingHom.ker (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom := by
      have h₂ := Scheme.Hom.ideal_ker_le (Scheme.IdealSheafData.ofIdealTop I).subschemeι
        ⟨⊤, isAffineOpen_top _⟩
      rwa [Scheme.IdealSheafData.ker_subschemeι, hJ] at h₂
    intro i hi
    have h0 : (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom i = 0 :=
      (RingHom.mem_ker).1 (hle hi)
    rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.mem_ker, RingHom.comp_apply]
    exact (congrArg l.appTop.hom h0).trans (map_zero _)
  · intro h
    have hker : (Scheme.IdealSheafData.ofIdealTop I).subschemeι.ker ≤
        ((BigFppfOver.toScheme B S hS).map x).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.ker_of_isAffine]
      refine Scheme.IdealSheafData.le_of_isAffine ?_
      rw [hJ]
      exact h.trans (Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply _).ge
    have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        (Scheme.IdealSheafData.ofIdealTop I).subschemeι :=
      .of_isPreimmersion _ ((Scheme.IdealSheafData.ofIdealTop I).range_subschemeι ▸
        (Scheme.IdealSheafData.ofIdealTop I).support.isClosed)
    exact ⟨@_root_.AlgebraicGeometry.IsClosedImmersion.lift _ _ _
        (Scheme.IdealSheafData.ofIdealTop I).subschemeι ((BigFppfOver.toScheme B S hS).map x) hci
        hker,
      @_root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _ _ _ hci hker⟩

/-- A section of `V` whose image in `P` lies in a closed subspace `D` comes from the chart of
`D`. -/
theorem exists_comp_snd_eq_of_mem_preimage {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {D : Subfunctor P} (hD : IsClosedImmersion B S hS D.ι) {V T : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ P) (x : T ⟶ V) (hx : x ∈ (D.preimage φ).obj (op T)) :
    ∃ x' : T ⟶ hD.1.pullback φ, x' ≫ hD.1.snd φ = x := by
  let e : D.toFunctor.obj (op T) := ⟨φ.app (op T) x, hx⟩
  let m : yoneda.obj T ⟶ D.toFunctor := yonedaEquiv.symm e
  have hm : m ≫ D.ι = yoneda.map x ≫ φ := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    change ((yonedaEquiv (yonedaEquiv.symm e)) : P.obj (op T)) = _
    rw [Equiv.apply_symm_apply]
  let l := (hD.1.isPullback φ).lift m (yoneda.map x) hm
  refine ⟨Yoneda.fullyFaithful.preimage l, yoneda.map_injective ?_⟩
  rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage]
  exact (hD.1.isPullback φ).lift_snd _ _ _

/-- **The ideal of `Y` in `D`, lifted to an affine chart of `P`.** For `Y ⊆ D` closed subspaces of
`P` with `Y` of finite presentation inside `D` and an étale chart `φ : V ⟶ P` with `V` affine, some
finitely generated ideal `J` of `Γ(V)` cuts out `Y` among the sections of `V` lying in `D`. -/
private theorem exists_fg_forall_mem_preimage_iff (P : AlgebraicSpaces B S hS)
    (D Y : ClosedSubspaces B S hS P.1) (hfp : IsFinitePresentation B S hS (Y.1.preimage D.1.ι).ι)
    {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (φ : yoneda.obj V ⟶ P.1) (hφe : IsEtale B S hS φ) :
    ∃ J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤), J.FG ∧
      ∀ {T : BigFppfOver B S hS} (x : T ⟶ V), x ∈ (D.1.preimage φ).obj (op T) →
        (x ∈ (Y.1.preimage φ).obj (op T) ↔
          J ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map x).appTop.hom) := by
  have hDrep := D.2.2.1
  let d := hDrep.snd φ
  let δ := hDrep.fst φ
  have sqD : IsPullback δ (yoneda.map d) D.1.ι φ := hDrep.isPullback φ
  have hdci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map d) :=
    D.2.2.2 φ δ d sqD
  obtain ⟨hDVaff, hdsurj⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map d)
  have hYD' : IsClosedSubspace B S hS (Y.1.preimage D.1.ι) :=
    isClosedSubspace_preimage B S hS D.1.ι Y.1 P.2 D.2.1 Y.2
  have hδe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf δ :=
    (isEtale_iff_presheaf_of_yoneda B S hS δ).1
      (isEtale_of_isPullback_of_isAlgebraicSpace B S hS sqD (isAlgebraicSpace_yoneda B S hS _)
        D.2.1 (isAlgebraicSpace_yoneda B S hS V) P.2 hφe)
  -- the ideal of `Y` in the chart of `D` is finitely generated
  let Lsh := ((BigFppfOver.toScheme B S hS).map (hYD'.2.1.snd δ)).ker
  let L := Lsh.ideal ⟨⊤, isAffineOpen_top _⟩
  have hLfg : L.FG :=
    fg_ideal_ker_rep_snd_of_isFinitePresentation B S hS (Z := ⟨_, hYD'.1⟩)
      (X := ⟨D.1.toFunctor, D.2.1⟩) (ObjectProperty.homMk (Y.1.preimage D.1.ι).ι) hYD'.2 hfp hδe
      ⟨⊤, isAffineOpen_top _⟩
  have hLsh : Lsh = Scheme.IdealSheafData.ofIdealTop L :=
    (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply Lsh).symm
  have hLpts : (Y.1.preimage D.1.ι).preimage δ =
      idealPoints B S hS (Scheme.IdealSheafData.ofIdealTop L) := by
    rw [← hLsh]
    exact (idealPoints_ker_rep_snd hYD'.2 δ).symm
  -- lift the generators
  obtain ⟨J, hJfg, hJL⟩ := Ideal.exists_fg_map_eq_of_surjective hdsurj hLfg
  refine ⟨J, hJfg, fun {T} x hx => ?_⟩
  obtain ⟨x', rfl⟩ := exists_comp_snd_eq_of_mem_preimage D.2.2 φ x hx
  -- a section of the chart of `D` lies over `Y` exactly when its image in `P` does
  have hw := congrArg (fun k => k.app (op T) x') sqD.w
  simp only [NatTrans.comp_app, types_comp_apply] at hw
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comap_ker,
    ← Ideal.map_le_iff_le_comap, hJL, ← mem_idealPoints_ofIdealTop_iff, ← hLpts]
  change _ ↔ D.1.ι.app (op T) (δ.app (op T) x') ∈ Y.1.obj (op T)
  rw [hw]
  rfl

/-- **Lifting a closed subspace of finite presentation of a closed subspace.** Let `P` be
quasi-compact and quasi-separated and `Y ⊆ D ⊆ P` closed subspaces with `Y ⊆ D` of finite
presentation. Then some closed subspace `T ⊆ P` of finite presentation contains `Y` and meets `D`
inside `Y`. -/
theorem exists_isFinitePresentation_inf_le (hZ : B.Contains (⊤_ Scheme.{u}))
    (P : AlgebraicSpaces B S hS) (hPqc : IsQuasiCompactSpace B S hS P.1)
    (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1) (D Y : ClosedSubspaces B S hS P.1)
    (hYD : Y.1 ≤ D.1) (hfp : IsFinitePresentation B S hS (Y.1.preimage D.1.ι).ι) :
    ∃ T : ClosedSubspaces B S hS P.1, IsFinitePresentation B S hS T.1.ι ∧ Y.1 ≤ T.1 ∧
      T.1 ⊓ D.1 ≤ Y.1 := by
  obtain ⟨V, φ, hV, hφs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.2).1 hPqc
  obtain ⟨J, hJfg, hJ⟩ := exists_fg_forall_mem_preimage_iff P D Y hfp φ hφe
  have hφe' := (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφe
  -- the lifted ideal is contained in the ideal of `Y`
  have hA : Scheme.IdealSheafData.ofIdealTop J ≤ chartKer B S hS P Y φ := by
    rw [le_chartKer_iff]
    intro T x hx
    exact (mem_idealPoints_ofIdealTop_iff J x).2 ((hJ x (hYD _ hx)).1 hx)
  obtain ⟨T', hT'fp, hYT', hJT'⟩ := exists_isFinitePresentation_le_chartKer B S hS hZ P hPqc hPqs
    Y φ hφe' _ (Scheme.IdealSheafData.isFiniteType_ofIdealTop hJfg) hA
  let TD : ClosedSubspaces B S hS P.1 := ⟨T'.1 ⊓ D.1, inf_isClosedSubspace B S hS P.1 P.2 T' D⟩
  refine ⟨T', hT'fp, hYT', le_of_chartKer_le P TD Y hφs hφe' ?_⟩
  have hYpts : idealPoints B S hS (chartKer B S hS P Y φ) = Y.1.preimage φ :=
    idealPoints_ker_rep_snd Y.2.2 φ
  rw [le_chartKer_iff, hYpts]
  intro T x hx
  exact (hJ x hx.2).2 ((mem_idealPoints_ofIdealTop_iff J x).1
    ((le_chartKer_iff B S hS P T' φ _).1 hJT' _ hx.1))

end AlgebraicGeometry.Space

end
