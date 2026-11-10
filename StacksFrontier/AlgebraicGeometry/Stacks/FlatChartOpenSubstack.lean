module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatChartPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackPresentationCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver

/-!
# Open substacks cut out by invariant opens of a finite flat chart

Let `f : 𝒮_W ⟶ 𝒳` be a surjective, flat, finite and finitely presented 1-morphism from the
algebraic stack of an object `W` of the big fppf site, and let `[W/R] ⟶ 𝒳` be the presentation it
induces (`AlgebraicGeometry.Stack.exists_flatChartPresentation`). An open subspace `Z` of `h_W`
which is invariant under the relation `R` cuts out an open substack `𝒰_Z` of `𝒳`, and an object
`f(w)` of `𝒳` attached to a section `w` of `h_W` lies in `𝒰_Z` exactly when `w` lies in `Z`.

This is the direction of Stacks 0507 from invariant subspaces to substacks, for the presentation
by the finite flat chart rather than by a smooth one: the proof of that direction
(`AlgebraicGeometry.Stack.isSubstackWith_presentationProperty`) uses only that the canonical
1-morphism `[W/R] ⟶ 𝒳` is an equivalence, which holds by Stacks 04WY. The groupoid of Stacks 04T4
lives over the final algebraic space `AlgebraicGeometry.Space.terminalSpace`, and is moved to the
final algebraic space `AlgebraicGeometry.Stack.baseSpace` over which the correspondence is stated
by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.changeBase`, which changes neither the quotient
stack nor the source and target.

## Main results

* `AlgebraicGeometry.Stack.FlatChart.exists_openSubstack`: the open substack attached to an
  invariant open subspace, with its objects of the form `f(w)` characterized.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatChart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {W V : BigFppfOver B S hS}
  {f : schemeStack.{u, w} B S hS W ⟶ 𝒳}
  (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (presheafOfCategories
      ((⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).obj ⋙
        typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS W).val 𝒳.val f.hom.hom).val.p
    (presheafOfCategories
      ((⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS).obj ⋙
        typeToCat)).p)

/-- The presentation datum of Stacks 04T4 attached to the chart. -/
noncomputable abbrev presentation :=
  SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property

/-- The groupoid of the presentation, read over the final algebraic space `baseSpace`. -/
noncomputable abbrev groupoid : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS) :=
  GroupoidInAlgebraicSpaces.changeBase ((isTerminal_baseSpace B S hS).from _)
    (presentation eU eR).groupoid

/-- The canonical 1-morphism `[W/R] ⟶ 𝒳` of the presentation, as a functor. -/
noncomputable abbrev canonical : (quotientStack (groupoid eU eR)).obj ⥤ 𝒳.val.val.obj :=
  (presentation eU eR).canonicalMap.toFunctor

/-- The canonical 1-morphism `[W/R] ⟶ 𝒳` commutes with the projections to the site. -/
theorem canonical_comp_p :
    canonical eU eR ⋙ 𝒳.val.val.p = (quotientStack (groupoid eU eR)).p :=
  (presentation eU eR).canonicalMap.w

/-- The source of the groupoid is the second projection of the self-intersection. -/
theorem groupoid_source_hom :
    (groupoid eU eR).source.hom = SelfIntersection.relationSourceMap eU eR := rfl

/-- The target of the groupoid is the first projection of the self-intersection. -/
theorem groupoid_target_hom :
    (groupoid eU eR).target.hom = SelfIntersection.relationTargetMap eU eR := rfl

variable {eU eR} in
/-- The canonical 1-morphism `[W/R] ⟶ 𝒳` is an equivalence when it is one over the site. -/
theorem isEquivalence_canonical
    (hE : Functor.IsEquivalenceOver (quotientStack (presentation eU eR).groupoid).p 𝒳.val.val.p
      (presentation eU eR).canonicalMap.toFunctor) :
    (canonical eU eR).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (canonical eU eR) hE.inv hE.unitIso.symm
    hE.counitIso).isEquivalence_functor

variable {eU eR} in
/-- **The open substack cut out by an invariant open subspace of the chart.** If the canonical
1-morphism `[W/R] ⟶ 𝒳` is an equivalence over the site, then every open subspace `Z` of `h_W`
whose inverse image under the source of `R` is contained in its inverse image under the target
cuts out an open substack `𝒰` of `𝒳`: the object `f(z)` attached to an object `z` of `𝒮_W` lies
in `𝒰` exactly when the section of `h_W` that `z` names lies in `Z`.

The open substack is the one of Stacks 0507 for the presentation `[W/R] ≃ 𝒳`
(`AlgebraicGeometry.Stack.isSubstackWith_presentationProperty`), and the characterization is
`U ×_𝒳 𝒰 = Z` (`AlgebraicGeometry.Stack.presentationSubfunctor_presentationProperty`), read
through the comparison of the projection of `[W/R]` with `f` that the presentation datum
carries. -/
theorem exists_openSubstack
    (hE : Functor.IsEquivalenceOver (quotientStack (presentation eU eR).groupoid).p 𝒳.val.val.p
      (presentation eU eR).canonicalMap.toFunctor)
    (Z : Subfunctor (yoneda.obj W))
    (hZ : Space.IsSubspaceWith B S hS (@AlgebraicGeometry.IsOpenImmersion.{u}) Z)
    (hinv : Z.preimage (SelfIntersection.relationSourceMap eU eR) ≤
      Z.preimage (SelfIntersection.relationTargetMap eU eR)) :
    ∃ 𝒰 : OpenSubstack 𝒳, (∀ z : (schemeStack.{u, w} B S hS W).val.val.obj,
      𝒰.property (f.hom.hom.obj z) ↔
        (eU.hom.functor.obj z).fiber.as ∈ Z.obj (op (eU.hom.functor.obj z).base)) ∧
      ∀ y : (fibredCategory B S hS (groupoid eU eR).objects.obj).val.obj,
        𝒰.property ((presentationProjection (groupoid eU eR) (canonical eU eR)
          (canonical_comp_p eU eR)).obj y) ↔ y.fiber.as ∈ Z.obj (op y.base) := by
  have := isEquivalence_canonical hE
  have hsub := isSubstackWith_presentationProperty (groupoid eU eR) (canonical eU eR)
    (canonical_comp_p eU eR) (Space.isEffectiveDescentAlongCoveringSieve_isOpenImmersion B S hS)
    Z hZ hinv
  have hkey := presentationSubfunctor_presentationProperty (groupoid eU eR) (canonical eU eR)
    (canonical_comp_p eU eR) Z hinv
  refine ⟨(OpenSubstack.equivIsSubstackWith 𝒳).symm ⟨_, hsub⟩, fun z => ?_, fun y =>
    Iff.of_eq (congrArg (fun Y : Subfunctor (yoneda.obj W) => y.fiber.as ∈ Y.obj (op y.base)) hkey)⟩
  have hstrict := hsub.1
  change presentationProperty (presentationProjection (groupoid eU eR) (canonical eU eR)
      (canonical_comp_p eU eR)) Z (f.hom.hom.obj z) ↔ _
  rw [← (presentationProperty (presentationProjection (groupoid eU eR) (canonical eU eR)
      (canonical_comp_p eU eR)) Z).prop_iff_of_iso ((presentation eU eR).extends_f.1.app z)]
  exact Iff.of_eq (congrArg (fun Y : Subfunctor (yoneda.obj W) =>
    (eU.hom.functor.obj z).fiber.as ∈ Y.obj (op (eU.hom.functor.obj z).base)) hkey)

variable {eU eR} in
/-- **Open substacks cut out by a covering family of invariant opens cover.** If open substacks
`𝒰 i` of `𝒳` are cut out, on the objects of the presentation `[W/R] ≃ 𝒳`, by subfunctors `Z i`
of `h_W` which jointly cover `h_W` in the fppf topology, then the `𝒰 i` cover `𝒳` in the sense of
`AlgebraicGeometry.Stack.IsOpenSubstackCover`: an object of `𝒳` lifts locally to the presentation
(`AlgebraicGeometry.Stack.exists_local_hom_from_presentation`), the lift lies locally in some
`Z i`, and an object mapping to an object of an open substack lies in it. -/
theorem isOpenSubstackCover_of_presentation
    (hE : Functor.IsEquivalenceOver (quotientStack (presentation eU eR).groupoid).p 𝒳.val.val.p
      (presentation eU eR).canonicalMap.toFunctor)
    {I : Type*} (𝒰 : I → OpenSubstack 𝒳) (Z : I → Subfunctor (yoneda.obj W))
    (hchar : ∀ i (y : (fibredCategory B S hS (groupoid eU eR).objects.obj).val.obj),
      (𝒰 i).property ((presentationProjection (groupoid eU eR) (canonical eU eR)
        (canonical_comp_p eU eR)).obj y) ↔ y.fiber.as ∈ (Z i).obj (op y.base))
    (hcov : ∀ (T : BigFppfOver B S hS) (u : (yoneda.obj W).obj (op T)),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ T), R k →
        ∃ i, (yoneda.obj W).map k.op u ∈ (Z i).obj (op V)) :
    IsOpenSubstackCover 𝒳 𝒰 := by
  have := isEquivalence_canonical hE
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  set v := presentationProjection (groupoid eU eR) (canonical eU eR) (canonical_comp_p eU eR)
  intro T x
  -- the sieve of arrows along which the pullback of `x` lies in one of the substacks
  let R' : Sieve T :=
    { arrows := fun V f => ∃ i, (𝒰 i).property (Functor.pullbackFiber 𝒳.val.val.p x f).1
      downward_closed := by
        rintro V V' f ⟨i, hi⟩ g
        exact ⟨i, (𝒰 i).prop_of_hom B S hS (Functor.IsStronglyCartesian.map 𝒳.val.val.p f
          (Functor.IsPreFibered.pullbackMap x.2 f) (f' := g ≫ f) (g := g) rfl
          (Functor.IsPreFibered.pullbackMap x.2 (g ≫ f))) hi⟩ }
  obtain ⟨R, hR, hloc⟩ := exists_local_hom_from_presentation (groupoid eU eR) (canonical eU eR)
    (canonical_comp_p eU eR) T x
  refine ⟨R', (BigFppfOver.topology B S hS).transitive hR R' ?_, fun V f hf => hf⟩
  intro V k hk
  obtain ⟨uu, ζ, hζ⟩ := hloc hk
  have hw : 𝒳.val.val.p.obj (v.obj uu) = uu.base := v.w_obj uu
  have hd : uu.base = V := hw.symm.trans (@IsHomLift.domain_eq _ _ _ _ 𝒳.val.val.p _ _ _ _ k ζ hζ)
  subst hd
  obtain ⟨R0, hR0, hR0cov⟩ := hcov uu.base uu.fiber.as
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR0
  intro V'' g hg
  obtain ⟨i, hi⟩ := hR0cov g hg
  have hy := (hchar i ⟨V'', Discrete.mk ((yoneda.obj W).map g.op uu.fiber.as)⟩).2 hi
  let ρ := v.map (fibredCategoryRestrictHom g uu.fiber.as)
  have hρζ : 𝒳.val.val.p.IsHomLift (g ≫ k) (ρ ≫ ζ) :=
    @IsHomLift.comp _ _ _ _ 𝒳.val.val.p _ _ _ _ _ _ g k ρ ζ
      (isHomLift_map_fibredCategoryRestrictHom v _ _) hζ
  have := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift (g ≫ k) (ρ ≫ ζ)
  refine ⟨i, (𝒰 i).prop_of_hom B S hS ?_ hy⟩
  exact Functor.IsStronglyCartesian.map 𝒳.val.val.p (g ≫ k) (ρ ≫ ζ) (f' := g ≫ k) (g := 𝟙 _)
    (by simp) (Functor.IsPreFibered.pullbackMap x.2 (g ≫ k))

end FlatChart

end AlgebraicGeometry.Stack

end
