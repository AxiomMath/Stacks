module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHonestChartMemGenericModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple

/-!
# A free generator on a chart through `ξ` is a free generator of `ℒ_ξ`

Let `X` be a decent algebraic space over `S`, let `Z ⊆ X` be a prime divisor with generic point
`ξ`, let `ℒ` be an *invertible* `𝒪_X`-module and let `s` be a meromorphic section of `ℒ`.  If `s`
is over an étale chart `W` of `X` whose image on points contains `ξ` the image of a section `e`
of `ℒ` which generates `ℒ` **freely** over `W` and over every chart below it, then the germ of
`s` at `ξ` is the image of a **free generator** of `ℒ_ξ`.

This is the step that carries the first sentence of the proof of Stacks 0EPS to `ξ` with its
generating content intact.
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range` carries
honesty only, which is all the *first* collection of that lemma needs; the *second* collection
needs the germ to generate `ℒ_ξ`, because that is what makes the ratio `s / s_ξ` of Stacks 0EPR a
unit of `𝒪^h_{X, ξ}` and so `ord_{Z, ℒ}(s) = 0`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.honestFreeSieve_genericHenselianChart_mem`: the charts of
  `Spec(𝒪^h_{X, ξ})` over which `c_ξ^*s` is an honest free generator of `ℒ_ξ` cover the identity
  chart.
* `AlgebraicGeometry.Space.PrimeDivisor.generatesGenericModuleStalk_of_eval_eq_of_mem_range`:
  **the statement above** — the germ of `s` at `ξ` is the image of a free generator of `ℒ_ξ`.

## Implementation notes

No lift of `c_ξ` through `W` is available, so the argument is the one of
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range` with free
generation carried alongside honesty, and it needs the two sieve steps that honesty alone does
not.

The condition on the charts of `X` is *`s` is an honest free generator here and below*; it passes
to charts over one, because a restricted free generator over the charts below is again one, and it
holds on `W` by hypothesis — hence, `W` being open on points and containing `ξ`, around every point
in the image of `c_ξ`.  Cover-density
(`AlgebraicGeometry.Space.exists_ofArrows_hasAffineChartDiagramWith_onRange`) then produces a
covering family of the identity chart whose members carry affine chart diagrams over `c_ξ` with
that condition on their chart of `X`.

Over such a member the inverse image `c_ξ^*e` presents `c_ξ^*s` honestly
(`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_toMeromorphicSectionValue`) but is a
free generator only over a *further* covering sieve
(`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`): the inverse
image of a free generator cannot be seen to be free on the nose, the inverse image being a
sheafification.  Transitivity of the topology composes the two coverings, and
`AlgebraicGeometry.Space.exists_bijective_smul_eval_eq_of_honestFreeSieve_mem` descends the
result to the identity chart — honesty by the injectivity of `ℒ_ξ ⟶ 𝒦(ℒ_ξ)` for an invertible
module, free generation by `AlgebraicGeometry.Space.bijective_smul_of_sieve`.

The scalars are finally transported from the regular functions on `Spec(𝒪^h_{X, ξ})` to
`𝒪^h_{X, ξ}` itself along `Scheme.ΓSpecIso`, which is how
`AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalk` restricts them.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- **`s` generates `ℒ_ξ`**: the germ at the generic point `ξ` of a prime divisor of a
meromorphic section `s` of `ℒ` is the image, under the comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ`, of a *free
generator* of `ℒ_ξ = c_ξ^*ℒ`.

This strengthens `AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk`, which asks only
that the germ be the image of some section, and its negation defines the collection of prime
divisors that the second collection of Stacks 0EPS is contained in: where `s` generates `ℒ_ξ`,
the ratio `s / s_ξ` of Stacks 0EPR is a unit of `𝒪^h_{X, ξ}` and `ord_{Z, ℒ}(s) = 0`. -/
def PrimeDivisor.GeneratesGenericModuleStalk (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) : Prop :=
  ∃ t : Z.genericModuleStalk B S hS hX hdec R hR L,
    (Function.Bijective fun r : R ↦ r • t) ∧
      Z.genericModuleStalkToMeromorphic B S hS hX hdec R hR L t =
        Z.genericMeromorphicGerm B S hS hX hdec R hR L s

/-- Generating `ℒ_ξ` implies lying in `ℒ_ξ`: the free generator the first condition produces is
in particular a section of `ℒ_ξ` whose image is the germ. -/
theorem PrimeDivisor.memGenericModuleStalk_of_generatesGenericModuleStalk
    (L : Modules.{u, u} B S hS X hX) (s : MeromorphicSection.{u, u} B S hS X hX L)
    (h : Z.GeneratesGenericModuleStalk B S hS hX hdec R hR L s) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s :=
  ⟨h.choose, h.choose_spec.2⟩

/-- **The charts of `Spec(𝒪^h_{X, ξ})` over which `c_ξ^*s` is an honest free generator of `ℒ_ξ`
cover the identity chart.**  The hypothesis is a presentation of `s` as a free generator of `ℒ`
over one chart `W` of `X` whose image on points contains `ξ`, together with free generation over
every chart below `W`.

See the implementation notes of this module: cover-density of the affine chart diagrams over
`c_ξ` whose chart of `X` carries that presentation gives one covering, the inverse image of a
free generator being a free generator over a covering sieve gives a second, and transitivity of
the small étale topology composes them. -/
theorem PrimeDivisor.honestFreeSieve_genericHenselianChart_mem (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS X) (e : L.val.obj (op W))
    (he : s.eval (op W) = toMeromorphicSectionValue B S hS X hX L W e)
    (hfree : ∀ (W' : SmallEtale B S hS X) (κ : W' ⟶ W),
      Function.Bijective fun r : chartRing B S hS X hX W' ↦ r • chartRestrictLinear L κ e)
    (hmem : Z.genericPoint B S hS X ∈
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)) :
    honestFreeSieve B S hS (Z.genericHenselianSpace B S hS hX hdec R hR)
        (Z.genericHenselianPullback B S hS hX hdec R hR L)
        (pullbackMeromorphicSection B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L
          (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s)
        (Z.genericHenselianChart B S hS hX hdec R hR) ∈
      SmallEtale.topology B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianChart B S hS hX hdec R hR) := by
  classical
  -- The condition on the charts of `X`: `s` is an honest free generator there and below.
  set P : SmallEtale B S hS X → Prop := fun V =>
    ∃ e' : L.val.obj (op V), s.eval (op V) = toMeromorphicSectionValue B S hS X hX L V e' ∧
      ∀ (V' : SmallEtale B S hS X) (κ : V' ⟶ V),
        Function.Bijective fun r : chartRing B S hS X hX V' ↦ r • chartRestrictLinear L κ e'
    with hPdef
  have hPhom : ∀ {V V' : SmallEtale B S hS X}, (V' ⟶ V) → P V → P V' := by
    rintro V V' φ ⟨e', he', hf'⟩
    refine ⟨chartRestrictLinear L φ e',
      eval_eq_toMeromorphicSectionValue_of_hom B S hS X hX L s φ e' he', fun V'' κ => ?_⟩
    rw [← chartRestrictLinear_comp L φ κ e']
    exact hf' V'' (κ ≫ φ)
  have hPcov : ∀ x : points B S hS X,
      x ∈ Set.range (pointsMap B S hS
          (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianMorphism B S hS hX hdec R hR).hom) →
        ∃ V : SmallEtale B S hS X, P V ∧
          x ∈ Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.1.hom) := by
    intro x hx
    refine ⟨W, ⟨e, he, hfree⟩, ?_⟩
    refine Z.range_pointsMap_genericHenselianMorphism_subset B S hS hX hdec R hR
      (Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)) ?_ hmem hx
    exact isOpen_range_pointsMap_of_isEtale B S hS W.1.hom
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X).obj W)) hX
      ((isEtale_iff_presheaf_of_yoneda B S hS W.1.hom).mpr W.property)
  -- The first covering: charts of `Spec(𝒪^h_{X, ξ})` with an affine chart diagram over `c_ξ`
  -- whose chart of `X` carries `P`.
  obtain ⟨I, Yc, π, hcov, hdiag⟩ := exists_ofArrows_hasAffineChartDiagramWith_onRange B S hS P
    (Z.genericHenselianMorphism B S hS hX hdec R hR) hPhom hPcov
    (Z.genericHenselianChart B S hS hX hdec R hR)
  refine (SmallEtale.topology B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj).transitive hcov _ ?_
  rintro Q k hk
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff Yc π k).1 hk
  -- It suffices to cover `Yc i`, the pullback along `g` of a covering sieve being covering.
  rw [Sieve.pullback_comp]
  refine (SmallEtale.topology B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj).pullback_stable g ?_
  -- The second covering: the inverse image of the free generator of `P` is free there.
  obtain ⟨-, V, q, hcomm, -, e', he', hf'⟩ := hdiag i
  obtain ⟨T, hTcov, hTfree⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (Z.genericHenselianMorphism B S hS hX hdec R hR) L hL
    ⟨Yc i, V, q, hcomm.symm⟩ (fun Wv κ => chartRestrictLinear L κ e')
    (fun Wv Wv' κ γ => (chartRestrictLinear_comp L κ γ e').symm) hf'
  refine (SmallEtale.topology B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj).superset_covering ?_ hTcov
  intro Q' ι hι
  refine ⟨modulePullbackChartSectionRestrict B S hS
    (Z.genericHenselianMorphism B S hS hX hdec R hR) L ⟨Yc i, V, q, hcomm.symm⟩
    (chartRestrictLinear L (𝟙 V) e') ι, ?_, fun Q'' h => ?_⟩
  · refine eval_eq_toMeromorphicSectionValue_of_hom B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianPullback B S hS hX hdec R hR L) _ ι _ ?_
    refine pullbackMeromorphicSection_eval_toMeromorphicSectionValue B S hS
      (Z.genericHenselianMorphism B S hS hX hdec R hR) L
      (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s
      ⟨Yc i, V, q, hcomm.symm⟩ _ ?_
    rw [chartRestrictLinear_id L V e']
    exact he'
  · rw [show chartRestrictLinear (Z.genericHenselianPullback B S hS hX hdec R hR L) h
        (modulePullbackChartSectionRestrict B S hS
          (Z.genericHenselianMorphism B S hS hX hdec R hR) L ⟨Yc i, V, q, hcomm.symm⟩
          (chartRestrictLinear L (𝟙 V) e') ι) =
      modulePullbackChartSectionRestrict B S hS
        (Z.genericHenselianMorphism B S hS hX hdec R hR) L ⟨Yc i, V, q, hcomm.symm⟩
        (chartRestrictLinear L (𝟙 V) e') (h ≫ ι) from
      modulePullbackChartSectionRestrict_map B S hS
        (Z.genericHenselianMorphism B S hS hX hdec R hR) L ⟨Yc i, V, q, hcomm.symm⟩ _ ι h]
    exact hTfree ι hι Q'' h

/-- **A meromorphic section of an invertible module which freely generates it over a chart whose
image contains `ξ` has for its germ at `ξ` the image of a free generator of `ℒ_ξ`.**

This is the generating strengthening of
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_eq_of_mem_range`, and it is
the form the second collection of Stacks 0EPS needs: the ratio `s / s_ξ` of Stacks 0EPR against
any free generator of `ℒ_ξ` is then a unit of `𝒪^h_{X, ξ}`, so `ord_{Z, ℒ}(s) = 0`.

The sieve of charts of `Spec(𝒪^h_{X, ξ})` over which `c_ξ^*s` is an honest free generator covers
the identity chart, and both halves descend; the scalars are then carried from the regular
functions on `Spec(𝒪^h_{X, ξ})` to `𝒪^h_{X, ξ}` along `Scheme.ΓSpecIso`, which is bijective. -/
theorem PrimeDivisor.generatesGenericModuleStalk_of_eval_eq_of_mem_range
    (L : Modules.{u, u} B S hS X hX)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS X) (e : L.val.obj (op W))
    (he : s.eval (op W) = toMeromorphicSectionValue B S hS X hX L W e)
    (hfree : ∀ (W' : SmallEtale B S hS X) (κ : W' ⟶ W),
      Function.Bijective fun r : chartRing B S hS X hX W' ↦ r • chartRestrictLinear L κ e)
    (hmem : Z.genericPoint B S hS X ∈
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.1.hom)) :
    Z.GeneratesGenericModuleStalk B S hS hX hdec R hR L s := by
  obtain ⟨n, hn, hnfree⟩ := exists_bijective_smul_eval_eq_of_honestFreeSieve_mem B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR)
    (Z.genericHenselianPullback B S hS hX hdec R hR L)
    (isInvertible_modulePullback_obj B S hS
      (Z.genericHenselianMorphism B S hS hX hdec R hR) L hL)
    (pullbackMeromorphicSection B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L
      (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s)
    (Z.genericHenselianChart B S hS hX hdec R hR)
    (Z.honestFreeSieve_genericHenselianChart_mem B S hS hX hdec R hR L hL s W e he hfree hmem)
  have hsec1 : ∀ x : R, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = x := fun x => by
    simp
  have hsec2 : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := fun a =>
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id a
  have hbijΓ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    Function.bijective_iff_has_inverse.2
      ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hsec1, hsec2⟩
  exact ⟨n, hnfree.comp hbijΓ, hn.symm⟩

end Generic

end AlgebraicGeometry.Space

end
