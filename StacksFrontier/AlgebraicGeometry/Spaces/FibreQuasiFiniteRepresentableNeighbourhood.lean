module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Representability near a fibre over which a morphism to a scheme is locally quasi-finite

Let `f : X ⟶ h_Y` be a proper morphism from an algebraic space to a scheme `Y` of the big fppf
site, `O ⊆ X` an open subspace and `φ : O ⟶ h_P` a morphism to a scheme `P` over `Y`.  Suppose
that a fibre `X_K = X ×_Y K` of `f` over a morphism `K ⟶ Y` lies in `O` and that the base change
of `φ` to `P_K = P ×_Y K` is locally quasi-finite.  Then for every point `y` in the image of
`K ⟶ Y` there is an open neighbourhood `V` of `y` over which `X` is a scheme.

This is the step of the proof of Stacks 0D3A after the construction of `φ`: "by
Cohomology of Spaces, Lemma 0A4W we see that `φ` is finite over an open neighbourhood of the
fibre; using that `ℙʳ_Y ⟶ Y` is closed, after shrinking `Y` we may assume that `φ` is finite. In
particular `X` is a scheme."  Only the consequence "`X` is a scheme" is used there, and it is
reached here with quasi-finiteness in place of finiteness: by Stacks 0ABM the quasi-finite locus
of `φ` is open and is compatible with base change, so it contains the fibre; `|f|` is closed,
so the fibre has a neighbourhood `X_V` inside the locus; over it `φ` is locally quasi-finite and
separated, hence representable by Stacks 03XX.

## Main results

* `AlgebraicGeometry.Space.exists_mem_isRepresentable_of_isLocallyQuasiFinite_fibre`.

## References

* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A square whose top edge is a composite with a monomorphism `i` is cartesian once the square
with that composite is: the monomorphism moves to the right edge. -/
theorem isPullback_of_isPullback_comp_mono {C : Type*} [Category C] {W X X' Y Z : C}
    {p : W ⟶ X'} {q : W ⟶ Z} {i : X' ⟶ X} [Mono i] {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback (p ≫ i) q f g) : IsPullback p q (i ≫ f) g := by
  refine IsPullback.of_isLimit' ⟨by rw [← Category.assoc]; exact h.w⟩
    (PullbackCone.IsLimit.mk _ (fun s ↦ h.lift (s.fst ≫ i) s.snd (by
        rw [Category.assoc, s.condition]))
      (fun s ↦ ?_) (fun s ↦ h.lift_snd _ _ _) (fun s m hm₁ hm₂ ↦ ?_))
  · rw [← cancel_mono i, Category.assoc, h.lift_fst]
  · apply h.hom_ext
    · rw [h.lift_fst, ← Category.assoc, hm₁]
    · rw [h.lift_snd, hm₂]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A proper morphism to a scheme which, near one of its fibres, carries a morphism to a scheme
whose base change to that fibre is locally quasi-finite, has a schematic preimage of a
neighbourhood of the fibre.**

The data: `f : X ⟶ h_Y` proper, an open subspace `O ⊆ X` with `φ : O ⟶ h_P` over
`π : P ⟶ Y`, a cartesian square `P_K = P ×_Y K`, and a cartesian square `h_U = X ×_Y K`
factoring through `O`, along which `φ` restricts to the locally quasi-finite `ψ : U ⟶ P_K`.
Then every `y` in the image of `K ⟶ Y` has an open neighbourhood `V` such that every base
change `X_V = X ×_Y V` is representable. -/
theorem exists_mem_isRepresentable_of_isLocallyQuasiFinite_fibre
    {Y : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ representedAlgebraicSpace B S hS Y) (hf : IsProper B S hS f.hom)
    {O : Subfunctor X.1} (hO : IsOpenSubspace B S hS O)
    {P : BigFppfOver B S hS} (π : P ⟶ Y)
    (φ : O.toFunctor ⟶ yoneda.obj P) (hφ : φ ≫ yoneda.map π = O.ι ≫ f.hom)
    {K PK U : BigFppfOver B S hS} (κ : K ⟶ Y) (πK : PK ⟶ K) (ι : PK ⟶ P)
    (hPK : IsPullback ι πK π κ)
    (p : yoneda.obj U ⟶ O.toFunctor) (q : U ⟶ K)
    (hsq : IsPullback (p ≫ O.ι) (yoneda.map q) f.hom (yoneda.map κ))
    (ψ : U ⟶ PK) (hψι : yoneda.map (ψ ≫ ι) = p ≫ φ) (hψπ : ψ ≫ πK = q)
    (hψ : IsLocallyQuasiFinite B S hS (yoneda.map ψ))
    (y : (BigFppfOver.toScheme B S hS).obj Y)
    (hy : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map κ)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ ⦃XV : AlgebraicSpaces B S hS⦄ (pV : XV ⟶ X)
        (fV : XV ⟶ representedAlgebraicSpace B S hS (openSub Y V)),
        IsPullback pV fV f (ObjectProperty.homMk (yoneda.map (openSubHom Y V))) →
        XV.1.IsRepresentable := by
  classical
  have hOsp : IsAlgebraicSpace B S hS O.toFunctor := hO.1
  have hYsp := isAlgebraicSpace_yoneda B S hS Y
  have hPsp := isAlgebraicSpace_yoneda B S hS P
  -- the restriction of `φ` to the fibre is the base change of `φ`
  have hout : IsPullback p (yoneda.map ψ ≫ yoneda.map πK) (φ ≫ yoneda.map π) (yoneda.map κ) := by
    rw [← Functor.map_comp, hψπ, hφ]
    exact isPullback_of_isPullback_comp_mono hsq
  have htop : IsPullback p (yoneda.map ψ) φ (yoneda.map ι) :=
    IsPullback.of_bot hout (by rw [← Functor.map_comp, hψι]) (hPK.map yoneda)
  -- `φ` is locally of finite type
  have hlftOf : IsLocallyOfFiniteType B S hS (O.ι ≫ f.hom) :=
    isLocallyOfFiniteType_comp B S hS hOsp X.2 hYsp O.ι f.hom
      (isLocallyOfFiniteType_of_isEtale B S hS X.2 (isEtale_ι_of_isOpenSubspace hO))
      hf.2.1.1
  have hlftφ : IsLocallyOfFiniteType B S hS φ :=
    isLocallyOfFiniteType_of_comp B S hS hOsp hPsp hYsp φ (yoneda.map π) (by rw [hφ]; exact hlftOf)
  -- `φ` is quasi-finite at the points of the fibre (Stacks 0ABM, part (2))
  have hQF : ∀ u : points B S hS (yoneda.obj U),
      IsQuasiFiniteAt B S hS φ (pointsMap B S hS _ p u) := fun u ↦
    (isQuasiFiniteAt_iff_of_isPullback B S hS htop.flip hOsp hPsp
      (isAlgebraicSpace_yoneda B S hS PK) hlftφ u).mp
      (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS (isAlgebraicSpace_yoneda B S hS U) hψ u)
  -- the quasi-finite locus, its image in `|X|`, and the closed image of its complement
  let Q : Set (points B S hS O.toFunctor) := {o | IsQuasiFiniteAt B S hS φ o}
  have hQ : IsOpen Q := isOpen_setOf_isQuasiFiniteAt B S hS φ
  let Qx : Set (points B S hS X.1) := pointsMap B S hS _ O.ι '' Q
  have hQx : IsOpen Qx := isOpenMap_pointsMap_of_isOpenImmersion B S hS O.ι hO.2 Q hQ
  let C : Set (points B S hS (yoneda.obj Y)) := pointsMap B S hS _ f.hom '' Qxᶜ
  have hC : IsClosed C :=
    isClosed_of_universallyClosed B S hS hYsp f.hom hf.2.2 _ hQx.isClosed_compl
  let V : ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
    ⟨(schemePointsHomeomorph B S hS Y).symm ⁻¹' Cᶜ,
      hC.isOpen_compl.preimage (schemePointsHomeomorph B S hS Y).symm.continuous⟩
  refine ⟨V, ?_, fun XV pV fV hV ↦ ?_⟩
  · -- every point of `|X|` over `y` lies in the quasi-finite locus
    obtain ⟨k, rfl⟩ := hy
    rintro ⟨x, hxQ, hx⟩
    have hz : pointsMap B S hS _ (yoneda.map κ) ((schemePointsHomeomorph B S hS K).symm k) =
        pointsMap B S hS _ f.hom x := by
      rw [schemePointsHomeomorph_symm_naturality, hx]
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq x _ hz.symm
    refine hxQ ⟨pointsMap B S hS _ p w, hQF w, ?_⟩
    rw [← hw, pointsMap_comp_apply]
  · have hV' := AlgebraicSpaces.isPullback_hom B S hS hV
    -- every point of `X_V` lies over the quasi-finite locus
    have hmem : ∀ xv : points B S hS XV.1, pointsMap B S hS _ pV.hom xv ∈ Qx := by
      intro xv
      by_contra hxv
      have hc : pointsMap B S hS _ f.hom (pointsMap B S hS _ pV.hom xv) ∈ C := ⟨_, hxv, rfl⟩
      rw [pointsMap_apply_comm B S hS hV'.w] at hc
      have ha : (schemePointsHomeomorph B S hS Y) (pointsMap B S hS _
          (yoneda.map (openSubHom Y V)) (pointsMap B S hS _ fV.hom xv)) ∈ V := by
        rw [schemePointsHomeomorph_apply, pointsToScheme_pointsMap, toScheme_map_openSubHom]
        exact (Set.ext_iff.mp (Scheme.Opens.range_ι V) _).mp ⟨_, rfl⟩
      exact (show _ ∉ C from ha) (by rw [Homeomorph.symm_apply_apply]; exact hc)
    -- `X_V ⟶ X` factors through `O`
    have hrange : Subfunctor.range pV.hom ≤ O := by
      rintro T _ ⟨z, rfl⟩
      obtain ⟨τ', hτ'⟩ := exists_lift_of_range_pointsMap_subset
        (yonedaEquiv.symm z ≫ pV.hom) hO (by
          rintro _ ⟨a, rfl⟩
          obtain ⟨o, -, ho⟩ := hmem (pointsMap B S hS _ (yonedaEquiv.symm z) a)
          exact ⟨o, by rw [ho, pointsMap_comp_apply]⟩)
      have h1 := congrArg (fun η ↦ η.app T (𝟙 T.unop)) hτ'
      have h2 : (yonedaEquiv.symm z ≫ pV.hom).app T (𝟙 T.unop) = pV.hom.app T z :=
        (yonedaEquiv_comp _ _).trans (congrArg _ (Equiv.apply_symm_apply _ _))
      rw [← h2, ← h1]
      exact (τ'.app T (𝟙 T.unop)).2
    let τ : XV.1 ⟶ O.toFunctor := Subfunctor.lift pV.hom hrange
    have hτ : τ ≫ O.ι = pV.hom := Subfunctor.lift_ι _ _
    -- the base change `P_V` of `P` and the base change `φ_V` of `φ`
    let PV := openSub P ((BigFppfOver.toScheme B S hS).map π ⁻¹ᵁ V)
    have hbot := (isPullback_openSubHomOfRestrict π V).map yoneda
    have hw : (τ ≫ φ) ≫ yoneda.map π = fV.hom ≫ yoneda.map (openSubHom Y V) := by
      rw [Category.assoc, hφ, ← Category.assoc, hτ]
      exact hV'.w
    let φV : XV.1 ⟶ yoneda.obj PV := hbot.lift (τ ≫ φ) fV.hom hw
    have hs : IsPullback τ (φV ≫ yoneda.map (openSubHomOfRestrict π V)) (φ ≫ yoneda.map π)
        (yoneda.map (openSubHom Y V)) := by
      rw [hbot.lift_snd, hφ]
      exact isPullback_of_isPullback_comp_mono (by rwa [hτ])
    have htop' : IsPullback τ φV φ (yoneda.map (openSubHom P _)) :=
      IsPullback.of_bot hs (hbot.lift_fst _ _ _).symm hbot
    have hPVsp := isAlgebraicSpace_yoneda B S hS PV
    -- `φ_V` is locally quasi-finite
    have hlqf : IsLocallyQuasiFinite B S hS φV := by
      rw [isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS XV.2 hPVsp]
      intro xv
      refine (isQuasiFiniteAt_iff_of_isPullback B S hS htop'.flip hOsp hPsp hPVsp hlftφ xv).mpr ?_
      obtain ⟨o, ho, hox⟩ := hmem xv
      have : o = pointsMap B S hS _ τ xv := by
        apply pointsMap_injective_of_mono B S hS O.ι
        rw [hox, ← pointsMap_comp_apply, hτ]
      rwa [← this]
    -- `φ_V` is separated, its composite with `P_V ⟶ V` being the base change of `f`
    have hsepf : IsSeparated B S hS fV.hom :=
      (isProper_of_isPullback B S hS XV.2 X.2
        (isAlgebraicSpace_yoneda B S hS (openSub Y V)) hYsp hV' hf).1
    have hsep : IsSeparated B S hS φV :=
      isSeparated_of_comp B S hS φV (yoneda.map (openSubHomOfRestrict π V)) (by
        rwa [hbot.lift_snd])
    exact isRepresentable_of_locallyQuasiFinite_separated B S hS XV.1 (yoneda.obj PV) XV.2
      hPVsp φV inferInstance hlqf hsep

end AlgebraicGeometry.Space

end
