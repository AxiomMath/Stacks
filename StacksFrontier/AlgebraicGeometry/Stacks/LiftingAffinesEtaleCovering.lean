module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothEtaleRefinementRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory

/-!
# Étale coverings by smooth lifts along a thickening of algebraic stacks (Stacks 0CJV)

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S`, let `W` be an algebraic space
over `S` and let `x : W ⟶ 𝒳` be a smooth 1-morphism. Stacks 0CJV asserts that `W` is covered, in
the étale topology, by algebraic spaces each of which sits in a cartesian square over
`ι` whose right-hand vertical 1-morphism is smooth. One such square is one object of
`AlgebraicGeometry.Stack.EtaleSmoothLift` (**Stacks 0CJP**), so the assertion is exactly that the
`base` components of a family of smooth lifts can be chosen to cover `W` in the spaces-étale
topology. That is the shape of
`AlgebraicGeometry.Stack.exists_etaleCovering_etaleSmoothLift` below.

What is proved here is the first step of the source's argument, the step that produces the
covering. The source chooses a scheme `U'` smooth and surjective over `𝒳'`, puts
`U = 𝒳 ×_{𝒳'} U'` — so that `U ⟶ 𝒳` is smooth and surjective — and takes `V = W ×_𝒳 U`, a
smooth surjective algebraic space over `W`. **Stacks 0CFV**
(`AlgebraicGeometry.Space.exists_isEtaleCovering_representable_refining_isSmoothCovering`)
then refines the one-member smooth covering `{V ⟶ W}` by an étale covering whose members factor
through `V`, and
shrinking each member to its affine opens makes the members affine. The remaining three steps of
the source — the Koszul-regular immersion analysis of an affine `W` inside `𝐀ⁿ_U`, the lifting of
its equations to `U'`, and the smoothness over `𝒳'` of the resulting closed subspace — produce
the lift over one such affine member, and they are what the hypothesis `hlift` below stands in
for.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.ofRepresentable`: a scheme of the site, étale over an
  algebraic space `Z`, as an object of the spaces-étale site of `Z` (**Stacks 03G0**).

## Main results

* `AlgebraicGeometry.Stack.exists_etaleCovering_etaleSmoothLift`: **Stacks 0CJV**, the covering,
  from the lifts over the affine members.

## Implementation notes

**What `hlift` assumes, and what it does not.** The hypothesis is: *for every scheme `T` of the
site whose underlying scheme is affine, every étale morphism `t : T ⟶ W` and every factorisation
of `t` through the given smooth surjective `p : V₀ ⟶ W`, there is a smooth lift of the étale open
`t` along `ι`.* Instantiated at `V₀ = W ×_𝒳 (𝒳 ×_{𝒳'} U')` and `p` its projection, a
factorisation of `t` through `p` is exactly a morphism from the affine `T` to the chart `U` over
`𝒳`, so the hypothesis is exactly the conclusion of Steps 2–4 of the source's proof for one
affine member. It is *not* the statement being proved: the étale covering of `W` — the whole
content of 0CJV's conclusion — is produced here and is not assumed, and the hypothesis speaks
only about an affine scheme that is already given together with its factorisation.

**Why the covering is produced by Stacks 0CFV and not by a chart construction.** The datum
`(V₀, p)` is taken as a parameter rather than built from `ι`: building it means forming the
2-fibre product `𝒳 ×_{𝒳'} U'` and then `W ×_𝒳 U` *as algebraic spaces*, which is a separate
piece of the stack-to-space comparison. Taking it as a parameter keeps this statement about the
refinement step, and costs nothing: a consumer who has the chart supplies it, and `p` may always
be taken to be the identity of `W`.

**Inherited caveat.** Thickenings of algebraic stacks are
`AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)), which omits the
homeomorphism-of-underlying-spaces clause of the source for want of a library site for the point
topology of Stacks 04XL. That omission is inherited here, through
`AlgebraicGeometry.Stack.EtaleSmoothLift`.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0CFV](https://stacks.math.columbia.edu/tag/0CFV)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJV](https://stacks.math.columbia.edu/tag/0CJV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale scheme over an algebraic space, as an object of its spaces-étale site.** A scheme
`T` of the big fppf category over `S` together with an étale morphism `t` from its represented
presheaf to `Z` is an object of the spaces-étale site of `Z` (**Stacks 03G0**). -/
def SpacesEtale.ofRepresentable (Z : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (t : yoneda.obj T ⟶ Z.obj) (ht : IsEtale B S hS t) : SpacesEtale B S hS Z :=
  ⟨Over.mk (ObjectProperty.homMk (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) t), ht⟩

/-- The structure morphism of
`AlgebraicGeometry.Space.SpacesEtale.ofRepresentable` is the given étale morphism. -/
@[simp]
theorem SpacesEtale.ofRepresentable_hom (Z : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (t : yoneda.obj T ⟶ Z.obj) (ht : IsEtale B S hS t) :
    ((SpacesEtale.ofRepresentable B S hS Z T t ht).obj.hom).hom = t :=
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CJV, the covering.** Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over
`S`, let `W` be an algebraic space over `S` and let `x : W ⟶ 𝒳` be a smooth 1-morphism. Let
`p : V₀ ⟶ W` be a smooth morphism of algebraic spaces which is surjective on points, and suppose
that every affine scheme of the site which is étale over `W` through a morphism factoring through
`p` carries a smooth lift of that étale open along `ι`. Then there is a family of smooth lifts of
étale opens of `W` along `ι` whose bases form an étale covering of `W`.

The hypothesis `hlift` stands in for Steps 2–4 of the source's proof, which construct the lift
over one affine member of the covering: the immersion of the affine member into an affine space
over the chart is a Koszul-regular immersion, its equations lift to the ambient chart of `𝒳'`,
and the closed subspace they cut out there is smooth over `𝒳'` by **Stacks 0CER**. The covering
itself is not assumed: it is produced from `p` by **Stacks 0CFV**, and the members are shrunk to
affine opens. -/
@[stacks 0CJV "the covering, from the lifts over the affine members"]
theorem exists_etaleCovering_etaleSmoothLift
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳') (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    (V₀ : AlgebraicSpaces B S hS) (p : V₀ ⟶ W)
    (hp : Space.IsSmooth B S hS p.hom)
    (hpsurj : Function.Surjective (Space.pointsMap B S hS V₀.obj p.hom))
    (hlift : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t),
        (∃ s : yoneda.obj T ⟶ V₀.obj, s ≫ p.hom = t) →
          ∃ ξ : EtaleSmoothLift B S hS ι hι W x hx,
            ξ.base = Space.SpacesEtale.ofRepresentable B S hS W T t ht) :
    ∃ (J : Type (u + 1)) (ξ : J → EtaleSmoothLift B S hS ι hι W x hx),
      Space.IsEtaleCovering B S hS (fun j => ((ξ j).base.obj.left).obj)
        (fun j => ((ξ j).base.obj.hom).hom) := by
  classical
  -- `p` is a one-member smooth covering of `W`.
  have hpcov : Space.IsSmoothCovering B S hS (fun _ : Unit => V₀.obj) (fun _ => p.hom) := by
    refine ⟨W.property, fun _ => V₀.property, fun _ => hp, ?_⟩
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hpsurj
  -- Stacks 0CFV refines it by an étale covering of `W` by schemes of the site.
  obtain ⟨J, T, t, hcov, href⟩ :=
    Space.exists_isEtaleCovering_representable_refining_isSmoothCovering B S hS hpcov
  choose _ sec hsec using href
  -- Shrink each member to the affine opens of its underlying scheme.
  have haff : ∀ (j : J) (y : (BigFppfOver.toScheme B S hS).obj (T j)),
      ∃ (A : BigFppfOver B S hS) (m : A ⟶ T j),
        IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
          Space.IsEtale B S hS (yoneda.map m) ∧
            y ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) := by
    intro j y
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj (T j)) (x := y) (U := ⊤) trivial
    have hVaff : IsAffine V.toScheme := hV
    have hcontains : B.Contains V.toScheme :=
      Scheme.size_lt_of_isOpenImmersion V.ι (T j).left.property
    let cs : B.obj hcontains ⟶ (T j).left := B.inclusion.preimage
      (show B.inclusion.obj (B.obj hcontains) ⟶ B.inclusion.obj (T j).left from V.ι)
    have hm : (BigFppfOver.toScheme B S hS).map
        (Over.homMk cs : Over.mk (cs ≫ (T j).hom) ⟶ T j) = V.ι :=
      B.inclusion.map_preimage _
    refine ⟨Over.mk (cs ≫ (T j).hom), Over.homMk cs, hVaff, ?_, ?_⟩
    · refine (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
        ((Space.presheaf_yoneda_map_etale_iff B S hS _).2 ?_)
      rw [hm]
      infer_instance
    · rw [hm]
      exact ⟨⟨y, hyV⟩, rfl⟩
  choose A m hAaff hAet hApt using haff
  -- The hypothesis supplies a smooth lift based at each affine member.
  choose ξ hbase using fun (j : J) (y : (BigFppfOver.toScheme B S hS).obj (T j)) =>
    hlift (A j y) (hAaff j y) (yoneda.map (m j y) ≫ t j)
      (Space.isEtale_comp B S hS (hAet j y) (hcov.etale j))
      ⟨yoneda.map (m j y) ≫ sec j, by rw [Category.assoc, hsec j]⟩
  -- The points hit by an affine member are hit by the base of the lift over it.
  have hrange : ∀ (j : J) (y : (BigFppfOver.toScheme B S hS).obj (T j)),
      Set.range (Space.pointsMap B S hS (yoneda.obj (A j y)) (yoneda.map (m j y) ≫ t j)) ⊆
        Set.range (Space.pointsMap B S hS ((ξ j y).base.obj.left).obj
          ((ξ j y).base.obj.hom).hom) := by
    intro j y
    rw [hbase j y, Space.SpacesEtale.ofRepresentable_hom]
    exact subset_rfl
  refine ⟨(j : J) × ((BigFppfOver.toScheme B S hS).obj (T j)), fun z => ξ z.1 z.2,
    W.property, fun z => ((ξ z.1 z.2).base.obj.left).property,
    fun z => (ξ z.1 z.2).base.property, ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun q => ?_
  obtain ⟨j, z, hz⟩ :=
    Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective q)
  set y := Space.pointsToScheme B S hS (T j) z with hy
  obtain ⟨s, hs⟩ := hApt j y
  obtain ⟨r, hr⟩ := (Space.bijective_pointsToScheme B S hS (A j y)).surjective s
  have hzr : Space.pointsMap B S hS (yoneda.obj (A j y)) (yoneda.map (m j y)) r = z :=
    (Space.bijective_pointsToScheme B S hS (T j)).injective
      (by rw [Space.pointsToScheme_pointsMap_yoneda, hr, hs, hy])
  have hq : Space.pointsMap B S hS (yoneda.obj (A j y))
      (yoneda.map (m j y) ≫ t j) r = q := by
    rw [Space.pointsMap_comp B S hS _ (yoneda.map (m j y)) (t j), Function.comp_apply, hzr, hz]
  exact Set.mem_iUnion.mpr ⟨⟨j, y⟩, hrange j y ⟨r, hq⟩⟩

end AlgebraicGeometry.Stack

end
