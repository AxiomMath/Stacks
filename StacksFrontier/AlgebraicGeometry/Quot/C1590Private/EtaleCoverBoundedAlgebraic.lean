module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued

/-!
# Algebraicity along an étale covering of the base with uniformly bounded charts

Let `π : P ⟶ h_U` be an fppf sheaf over an object `U` of the big fppf site of `S`, and let
`{gᵢ : Xᵢ ⟶ U}` be a jointly surjective family of étale morphisms of the site such that each
base change `Pᵢ = P ×_U Xᵢ` is an algebraic space. Then `P` is an algebraic space, provided the
family, the members `Xᵢ` and chosen étale atlases of the `Pᵢ` are bounded by one cardinal below
the cutoff of the site.

The family is not assumed finite, nor indexed below the cofinality of the cutoff, so
`AlgebraicGeometry.isAlgebraicSpace_of_etale_cover` (whose index carries
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`) does not apply; this is the shape in which
an étale covering of a non-quasi-compact scheme by affine schemes, indexed by its points, is
used.

## The argument

The members `Xᵢ` have a coproduct `W` in the site, with surjective étale `q : W ⟶ U`
(`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`). Its representable
sheaf is the coproduct of those of the `Xᵢ`
(`AlgebraicGeometry.C1590Private.isColimitYonedaCofanOfIsColimitToScheme`), so by universality
of coproducts of sheaves the base change `P_W = P ×_U W` is the coproduct of the `Pᵢ`
(`AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`). A coproduct of algebraic
spaces whose atlases have a coproduct in the site is an algebraic space (Stacks 02WQ,
`AlgebraicGeometry.isAlgebraicSpace_coproduct`), and the uniform bound puts that coproduct in
the site. Finally `P_W ⟶ P` is a base change of `q`, hence representable, surjective and
étale, and Stacks 0BGR concludes
(`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale`).

## Main results

* `AlgebraicGeometry.C1590Private.isColimitYonedaCofanOfIsColimitToScheme`: the representable
  sheaf of a coproduct of the site, computed on underlying schemes, is the coproduct of the
  representable sheaves.
* `AlgebraicGeometry.C1590Private.isAlgebraicSpace_of_etaleCover_isPullback_of_size_le`: the
  criterion.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of fppf sheaves on `BigFppfOver B S hS`: instance search for them times out under
Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_EtaleCoverBoundedAlgebraic :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type u)) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_EtaleCoverBoundedAlgebraic
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The representable sheaf of a coproduct of the site is the coproduct of the representable
sheaves.** If the underlying scheme of an object `V` of the big fppf site of `S` is the
coproduct of the underlying schemes of a family `X`, with the injections of the family as
coproduct injections, then the representable sheaf of `V` is the coproduct, among fppf sheaves
of `Type u`, of the representable sheaves of the `X i`. This is
`AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaCofan` in the value universe of the site. -/
noncomputable def isColimitYonedaCofanOfIsColimitToScheme
    [(BigFppfOver.topology B S hS).Subcanonical] {ι : Type u} (X : ι → BigFppfOver B S hS)
    {V : BigFppfOver B S hS} (j : ∀ i, X i ⟶ V)
    (hj : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
      fun i => (BigFppfOver.toScheme B S hS).map (j i))) :
    IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj V)
      fun i => (BigFppfOver.topology B S hS).yoneda.map (j i)) := by
  set Y : ι → Scheme.{u} := fun k => (BigFppfOver.toScheme B S hS).obj (X k)
  set e : (∐ Y) ≅ (BigFppfOver.toScheme B S hS).obj V :=
    (coproductIsCoproduct Y).coconePointUniqueUpToIso hj
  have hfac : ∀ i, Sigma.ι Y i ≫ e.hom = (BigFppfOver.toScheme B S hS).map (j i) := fun i =>
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hj (Discrete.mk i)
  have _ : ∀ i, Mono ((Cofan.mk V j).inj i) := fun i => by
    apply (Over.forget (B.obj hS)).mono_of_mono_map
    apply B.inclusion.mono_of_mono_map
    change Mono ((BigFppfOver.toScheme B S hS).map (j i))
    rw [← hfac i]
    infer_instance
  refine (BigFppfOver.topology B S hS).isColimitCofanMkYoneda (c := Cofan.mk V j) X
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j
      (BigFppfOver.isOpenImmersion_toScheme_map_of_isColimit B S hS X j hj)
      (BigFppfOver.exists_mem_range_toScheme_map_of_isColimit B S hS X j hj))
    (BigFppfOver.bot_mem_topology_of_isInitial B S hS) ?_
  intro i i' hii' Z a b hab
  have hab' : (BigFppfOver.toScheme B S hS).map a ≫ Sigma.ι Y i =
      (BigFppfOver.toScheme B S hS).map b ≫ Sigma.ι Y i' := by
    have h : (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map (j i) =
        (BigFppfOver.toScheme B S hS).map b ≫ (BigFppfOver.toScheme B S hS).map (j i') := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (BigFppfOver.toScheme B S hS).map hab
    rw [← hfac i, ← hfac i', ← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono e.hom).mp h
  have hZ : IsEmpty ((BigFppfOver.toScheme B S hS).obj Z) :=
    isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ hii'
  exact ⟨Over.isInitialOfIsInitialLeft (Y := Z)
    (isInitial_schemeBelow B (isInitial_iff_isEmpty.mpr hZ).some)⟩

/-- **Algebraicity along a uniformly bounded étale covering of the base.** Let `π : P ⟶ h_U` be
a morphism from an fppf sheaf to the representable sheaf of an object `U` of the big fppf site
of `S`, and let `gᵢ : Xᵢ ⟶ U`, for `i` in a type of the working universe, be étale morphisms of
the site whose images cover `U`. Suppose that each base change `Pᵢ = P ×_U Xᵢ` (given by a
cartesian square) is an algebraic space with a surjective étale atlas, and that the index type,
the members `Xᵢ` and those atlases are bounded by one cardinal `μ` below the cutoff. Then `P` is
an algebraic space. -/
theorem isAlgebraicSpace_of_etaleCover_isPullback_of_size_le
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    {U : BigFppfOver B S hS} (π : P ⟶ yoneda.obj U)
    {ι : Type u} (X : ι → BigFppfOver B S hS) (g : ∀ i, X i ⟶ U)
    (hg : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (g i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)))
    (Pi : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hPi : ∀ i, IsAlgebraicSpace B S hS (Pi i))
    (f : ∀ i, Pi i ⟶ P) (πi : ∀ i, Pi i ⟶ yoneda.obj (X i))
    (hsq : ∀ i, IsPullback (f i) (πi i) π (yoneda.map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (hatlas : ∀ i, ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ Pi i),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj A).size ≤ μ) :
    IsAlgebraicSpace B S hS P := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := BigFppfOver.subcanonical B S hS
  let := BigFppfOver.hasSheafify_type B S hS
  -- the coproduct `W` of the members and its surjective étale map to `U`
  obtain ⟨V, j, hjopen, hjcov, ⟨hj⟩, ⟨hjsite⟩, -⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  let q : V ⟶ U := Cofan.IsColimit.desc hjsite g
  have hjq : ∀ i, j i ≫ q = g i := fun i => Cofan.IsColimit.fac hjsite g i
  have hjqs : ∀ i, (BigFppfOver.toScheme B S hS).map (j i) ≫
      (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map (g i) := fun i => by
    rw [← Functor.map_comp, hjq]
  have hqsurj : Surjective ((BigFppfOver.toScheme B S hS).map q) := by
    rw [surjective_iff]
    intro t
    obtain ⟨i, y, hy⟩ := hcov t
    refine ⟨((BigFppfOver.toScheme B S hS).map (j i)) y, ?_⟩
    rw [← hy, ← hjqs i]
    rfl
  have hqet : Etale ((BigFppfOver.toScheme B S hS).map q) := by
    let 𝒰 : ((BigFppfOver.toScheme B S hS).obj V).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme B S hS).obj (X i)
        f := fun i => (BigFppfOver.toScheme B S hS).map (j i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjcov, hjopen⟩ }
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    show Etale ((BigFppfOver.toScheme B S hS).map (j i) ≫ (BigFppfOver.toScheme B S hS).map q)
    rw [hjqs i]
    exact hg i
  -- the base change `P_W = P ×_U W`, as a sheaf
  let Ps : Sheaf J (Type u) := ⟨P, hP⟩
  let πs : Ps ⟶ J.yoneda.obj U := ⟨π⟩
  let A := pullback πs (J.yoneda.map q)
  have hA : IsPullback (pullback.fst πs (J.yoneda.map q)).hom
      (pullback.snd πs (J.yoneda.map q)).hom π (yoneda.map q) :=
    (IsPullback.of_hasPullback πs (J.yoneda.map q)).map (sheafToPresheaf J (Type u))
  -- the `Pᵢ` map to `P_W`, cartesian over the inclusions `Xᵢ ⟶ W`
  have hw : ∀ i, f i ≫ π = (πi i ≫ yoneda.map (j i)) ≫ yoneda.map q := fun i => by
    rw [Category.assoc, ← Functor.map_comp, hjq]
    exact (hsq i).w
  let l : ∀ i, Pi i ⟶ A.obj := fun i => hA.lift (f i) (πi i ≫ yoneda.map (j i)) (hw i)
  have hl : ∀ i, IsPullback (l i) (πi i) (pullback.snd πs (J.yoneda.map q)).hom
      (yoneda.map (j i)) := fun i => by
    have houter : IsPullback (l i ≫ (pullback.fst πs (J.yoneda.map q)).hom) (πi i) π
        (yoneda.map (j i) ≫ yoneda.map q) := by
      rw [hA.lift_fst, ← Functor.map_comp, hjq]
      exact hsq i
    exact IsPullback.of_right houter (hA.lift_snd _ _ _) hA
  -- so `P_W` is the coproduct of the `Pᵢ`
  let ls : ∀ i, (⟨Pi i, (hPi i).isSheaf⟩ : Sheaf J (Type u)) ⟶ A := fun i => ⟨l i⟩
  let qs : ∀ i, (⟨Pi i, (hPi i).isSheaf⟩ : Sheaf J (Type u)) ⟶ J.yoneda.obj (X i) :=
    fun i => ⟨πi i⟩
  obtain ⟨hcolim⟩ := Space.nonempty_isColimit_cofanMk_of_isPullback B S hS
    (fun i => J.yoneda.map (j i)) (isColimitYonedaCofanOfIsColimitToScheme X j hj)
    (pullback.snd πs (J.yoneda.map q)) ls qs fun i => isPullback_sheaf_of_hom (hl i)
  -- which is an algebraic space: its members' atlases have a coproduct in the site
  choose Aa a ha₁ ha₂ ha₃ using hatlas
  obtain ⟨Vc, c, ⟨hc⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_le B S hS Aa
    (μ := max μ ℵ₀) (le_max_right _ _) (max_lt hμ B.aleph0_lt_cutoff)
    (hι.trans (le_max_left _ _)) fun i => (ha₃ i).trans (le_max_left _ _)
  have hAalg : IsAlgebraicSpace B S hS A.obj :=
    isAlgebraicSpace_coproduct B S hS Pi hPi A ls hcolim Aa a ha₁ ha₂ Vc c hc
  -- and `P_W ⟶ P` is a base change of `q`
  have hbc : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange],
      Q ((BigFppfOver.toScheme B S hS).map q) →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B S hS))) (pullback.fst πs (J.yoneda.map q)).hom :=
    fun Q _ hq => (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hA.flip
      (Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance q hq)
  exact isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS hAalg hP
    (pullback.fst πs (J.yoneda.map q)).hom (hbc _ hqsurj) (hbc _ hqet)

end AlgebraicGeometry.C1590Private

end
