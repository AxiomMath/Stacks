module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional

/-!
# The étale charts of Stacks 06N3 assembled from a uniform size bound

The proof of the substantial direction of **Stacks 06N3** cuts out an étale chart `Z_x ⟶ 𝒳` at
every finite type point `x` of `𝒳` and takes the disjoint union `W = ∐_x Z_x`. For that union to
be an object of the big fppf site something has to be known about the *sizes* of the charts: the
cutoff of an `AlgebraicGeometry.BigFppfSite` is only a strong prelimit of uncountable
cofinality, so `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` does not apply to a
family indexed by the finite type points of `𝒳`, and what does apply is
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_forall_size_le`, which asks for one bound on the
summands' sizes **uniform in the index**.

From a chart at each finite type point whose size is bounded by `2 ^ 2 ^ size U₀` for one fixed
smooth surjective scheme chart `a₀ : U₀ ⟶ 𝒳`, this file builds the family of
`AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM`, site-membership conjunct
included, and hence the substantial direction of **Stacks 06N3**.

## Main results

* `AlgebraicGeometry.Stack.exists_etaleChartFamily_of_forall_isFiniteTypePoint`: the family, with
  its coproduct in the site.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_forall_exists_isRelativelyEtale_chart`: such a
  stack is Deligne–Mumford.
* `AlgebraicGeometry.Stack.existsEtaleChartFamilyOfIsAbsolutelyDM_of_forall_exists_chart`: the
  chart construction of Stacks 06N3 reduced to its local half.
* `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart`: and
  with it the substantial direction of **Stacks 06N3**.

## The indexing trick

The family is indexed not by the finite type points of `𝒳` — a type of the wrong universe, and of
no useful cardinality — but by the **points of `U₀` lying over one**, which is a subtype of the
underlying type of a scheme of the site, hence of cardinality at most `2 ^ size U₀` by
`AlgebraicGeometry.Scheme.mk_le_two_pow_size` and so below the cutoff. That the family still
covers every finite type point is surjectivity of `a₀` on points: a finite type point of `𝒳` is
the image of some point of `U₀`, and that point is then an index. Both the index bound and the
bound `2 ^ 2 ^ size U₀ < cutoff` on the sizes come from
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`, applied twice.

Smoothness of `a₀` is not used for the assembly, only its surjectivity on points. It is the chart
at one finite type point that needs `a₀` smooth: **Stacks 06FX**, in the form
`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint`, bounds the size
of the smooth chart it produces by `size U₀`, and `2 ^ 2 ^ size U₀` bounds the size of a scheme
admitting a monomorphism into that chart (`AlgebraicGeometry.Scheme.size_le_of_mono`).

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open Cardinal CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The slice as an object of the site, with the uniform size bound.** Let `U₀` and `U` be
schemes of the site with `size U ≤ size U₀` — the relation **Stacks 06FX** delivers for the smooth
chart it produces at a finite type point — and let `ι : T ⟶ U` be a *monomorphism* of schemes, as
the slice `V(f₁, …, f_r) ⊆ U` of the chart construction of **Stacks 06N3** is. Then `T` is itself
an object of the site over `U`, of size at most `2 ^ 2 ^ size U₀`, and the morphism of the site
realizing `ι` is `ι` itself. -/
theorem exists_siteObject_toScheme_map_eq_size_le (U₀ U : BigFppfOver B S hS)
    (hUsize : ((BigFppfOver.toScheme B S hS).obj U).size ≤
      ((BigFppfOver.toScheme B S hS).obj U₀).size)
    {T : Scheme.{u}} (ι : T ⟶ (BigFppfOver.toScheme B S hS).obj U) [Mono ι] :
    ∃ (hT : B.Contains T) (j : siteObject B S hS hT (ι ≫ B.inclusion.map U.hom) ⟶ U),
      (BigFppfOver.toScheme B S hS).map j = ι ∧
        T.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
          ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  refine ⟨BigFppfSite.contains_of_mono B ι U.left.2,
    Over.homMk (ObjectProperty.homMk ι) rfl, rfl, ?_⟩
  refine (Scheme.size_le_of_mono ι).trans (max_le ?_ ?_)
  · exact power_le_power_left two_ne_zero
      (((BigFppfOver.toScheme B S hS).obj U).mk_le_two_pow_size.trans
        (power_le_power_left two_ne_zero hUsize))
  · exact hUsize.trans ((Cardinal.cantor _).le.trans (Cardinal.cantor _).le)

/-- **The étale charts of Stacks 06N3, assembled into a family whose coproduct lies in the
site.** Let `a₀ : U₀ ⟶ 𝒳` be a 1-morphism from a scheme of the site which is surjective on
points, and suppose that at every finite type point `x` of `𝒳` there is a scheme `Z` of the site
of size at most `2 ^ 2 ^ size U₀` with a relatively étale 1-morphism `Z ⟶ 𝒳` whose image on
points contains `x`. Then there is a family of such charts whose images cover the finite type
points of `𝒳` and whose coproduct is again a scheme of the site: the conclusion of
`AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM` at `𝒳`. -/
theorem exists_etaleChartFamily_of_forall_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U₀ : BigFppfOver B S hS)
    (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) (ha₀surj : IsSurjective B S hS a₀)
    (hchart : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
      IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
        ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
          IsRelativelyEtale B S hS c.hom ∧
          x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
          ((BigFppfOver.toScheme B S hS).obj Z).size ≤
            (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
              ((BigFppfOver.toScheme B S hS).obj U₀).size) :
    ∃ (I : Type u) (Z : I → BigFppfOver B S hS)
      (_hsum : B.Contains (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Z i)))
      (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳),
      (∀ i, IsRelativelyEtale B S hS (f i).hom) ∧
        finiteTypePoints B S hS 𝒳 ⊆
          ⋃ i, Set.range (AlgebraicStacks.pointsMap B S hS (f i)) := by
  classical
  let := pointTopology B S hS (schemeFibredCategory B S hS U₀)
  have hU₀ : ((BigFppfOver.toScheme B S hS).obj U₀).size < B.cutoff := U₀.left.2
  have hc : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
      ((BigFppfOver.toScheme B S hS).obj U₀).size < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hU₀)
  have hI : Cardinal.mk {v : (BigFppfOver.toScheme B S hS).obj U₀ //
      IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
        ((pointsHomeomorphScheme B S hS U₀).symm v))} < B.cutoff :=
    (Cardinal.mk_subtype_le _).trans_lt
      (((BigFppfOver.toScheme B S hS).obj U₀).mk_le_two_pow_size.trans_lt
        (B.cutoff_isStrongPrelimit hU₀))
  choose Z f hetale hmem hsize using fun
      (i : {v : (BigFppfOver.toScheme B S hS).obj U₀ //
        IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
          ((pointsHomeomorphScheme B S hS U₀).symm v))}) => hchart _ i.2
  refine ⟨_, Z, B.contains_sigma_of_forall_size_le hI _ _ hc hsize, f, hetale,
    fun x hx => ?_⟩
  obtain ⟨wx, rfl⟩ := ha₀surj x
  have hwmem : IsFiniteTypePoint.{u, w} B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS a₀
      ((pointsHomeomorphScheme B S hS U₀).symm (pointsHomeomorphScheme B S hS U₀ wx))) := by
    rwa [Homeomorph.symm_apply_apply]
  exact Set.mem_iUnion.2 ⟨⟨_, hwmem⟩, by simpa using hmem ⟨_, hwmem⟩⟩

/-- **An étale chart of bounded size at every finite type point makes an algebraic stack
Deligne–Mumford.** Let `a₀ : U₀ ⟶ 𝒳` be a 1-morphism from a scheme of the site which is
surjective on points, and suppose that at every finite type point `x` of `𝒳` there is a scheme `Z`
of the site of size at most `2 ^ 2 ^ size U₀` with a relatively étale 1-morphism `Z ⟶ 𝒳` whose
image on points contains `x`. Then `𝒳` is a Deligne–Mumford stack. -/
theorem isDeligneMumfordStack_of_forall_exists_isRelativelyEtale_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U₀ : BigFppfOver B S hS)
    (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) (ha₀surj : IsSurjective B S hS a₀)
    (hchart : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
      IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
        ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
          IsRelativelyEtale B S hS c.hom ∧
          x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
          ((BigFppfOver.toScheme B S hS).obj Z).size ≤
            (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
              ((BigFppfOver.toScheme B S hS).obj U₀).size) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val := by
  obtain ⟨I, Z, hsum, f, hetale, hft⟩ :=
    exists_etaleChartFamily_of_forall_isFiniteTypePoint.{u, w} B S hS 𝒳 U₀ a₀ ha₀surj hchart
  exact isDeligneMumfordStack_of_forall_isRelativelyEtale.{u, w} B S hS 𝒳 Z hsum f hetale hft

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The chart construction of Stacks 06N3 reduced to its local half.** If every DM algebraic
stack admits, at each of its finite type points and against each of its smooth surjective scheme
charts `a₀ : U₀ ⟶ 𝒳`, a relatively étale chart by a scheme of the site of size at most
`2 ^ 2 ^ size U₀` whose image contains that point, then
`AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM` holds. -/
theorem existsEtaleChartFamilyOfIsAbsolutelyDM_of_forall_exists_chart
    (hchart : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS),
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
      ∀ (U₀ : BigFppfOver B S hS) (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳),
        AlgebraicStacks.IsSmooth B S hS a₀ → IsSurjective B S hS a₀ →
        ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
          IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
            ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
              IsRelativelyEtale B S hS c.hom ∧
              x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
              ((BigFppfOver.toScheme B S hS).obj Z).size ≤
                (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                  ((BigFppfOver.toScheme B S hS).obj U₀).size) :
    ExistsEtaleChartFamilyOfIsAbsolutelyDM.{u, w} B S hS hZ := by
  intro 𝒳 h𝒳
  obtain ⟨U₀, a₀, ha₀sm, ha₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  exact exists_etaleChartFamily_of_forall_isFiniteTypePoint.{u, w} B S hS 𝒳 U₀ a₀ ha₀surj
    (hchart 𝒳 h𝒳 U₀ a₀ ha₀sm ha₀surj)

/-- **The substantial direction of Stacks 06N3 reduced to the chart at one finite type point.**
If every DM algebraic stack admits, at each of its finite type points and against each of its
smooth surjective scheme charts `a₀ : U₀ ⟶ 𝒳`, a relatively étale chart by a scheme of the site of
size at most `2 ^ 2 ^ size U₀` whose image contains that point, then
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM` holds. -/
theorem existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart
    (hchart : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS),
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
      ∀ (U₀ : BigFppfOver B S hS) (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳),
        AlgebraicStacks.IsSmooth B S hS a₀ → IsSurjective B S hS a₀ →
        ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
          IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
            ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
              IsRelativelyEtale B S hS c.hom ∧
              x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
              ((BigFppfOver.toScheme B S hS).obj Z).size ≤
                (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                  ((BigFppfOver.toScheme B S hS).obj U₀).size) :
    ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ :=
  existsEtalePresentationOfIsAbsolutelyDM_of_existsEtaleChartFamily.{u, w} B S hS hZ
    (existsEtaleChartFamilyOfIsAbsolutelyDM_of_forall_exists_chart.{u, w} B S hS hZ hchart)

end AlgebraicGeometry.Stack

end
