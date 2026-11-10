module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothCoverings

/-!
# Étale refinements of smooth coverings, with representable members

Let `S` be a scheme contained in a big fppf site `B`. Every smooth covering of an algebraic
space over `S` is refined by an étale covering whose members are *schemes of the site*: given a
smooth covering `{Xᵢ ⟶ F}` there are objects `Yⱼ` of the site, an étale covering
`{yoneda.obj Yⱼ ⟶ F}` and, for every `j`, an index `i` and a morphism `yoneda.obj Yⱼ ⟶ Xᵢ` over
`F`.

Representability of the members is the point of this file, and it is what consumers that must
pass to affine opens of the members need. The refinement statement itself, for members that are
arbitrary presheaves, is
`AlgebraicGeometry.Space.exists_isEtaleCovering_refining_isSmoothCovering` in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothEtaleRefinement`; neither statement
follows from the other, since this one gains representability and pays for it with an index type
one universe up.

The proof is the proof of the source. A scheme atlas `a : U ⟶ F` and scheme atlases
`bᵢ : Wᵢ ⟶ Xᵢ` of the members turn the given covering into a smooth covering `{Wᵢ ⟶ F}` by
representables which refines it; base changing along `a` and then taking a scheme atlas `Zᵢ` of
each base change produces a smooth covering `{Zᵢ ⟶ U}` of *representables*, that is a smooth
covering of schemes. At every point of `U` the scheme-level étale local section of **Stacks 055U**
shrinks one member of that covering to an étale morphism hitting the point and factoring through
it, and composing with `a` gives the required étale covering of `F`.

## Main results

* `AlgebraicGeometry.Space.exists_isEtaleCovering_representable_refining_isSmoothCovering`:
  **Stacks 0CFV** with representable members.

## Implementation notes

The refining covering is indexed by the points of the underlying scheme of the chosen atlas of
`F`, lifted to `Type (u + 1)`: choosing one member per point is what replaces the source's
appeal to the scheme-level refinement statement of Stacks 055V for a whole covering, and it
frees the index type of the given covering from any smallness assumption.

An étale neighbourhood produced by Stacks 055U has an arbitrary underlying scheme, which need
not meet the size cutoff of the big fppf site. Replacing it by an affine open neighbourhood of
its distinguished point preserves all three conclusions — the inclusion of an open is an open
immersion, hence étale, the distinguished point still lies over the given point, and the lift
restricts — while making the source affine, hence quasi-compact and of size bounded by that of
the base. That is
`AlgebraicGeometry.Space.exists_etale_site_factorisation_of_smooth`.

Both the given and the produced covering are the structures of Stacks 041C and Stacks 041E on
families of morphisms of presheaves. The members of the produced covering are *schemes* of the
site, which is more than the source states and is what the construction gives: each member is an
affine open of an étale neighbourhood. A consumer who wants the covering as a family of
morphisms of the site can recover those morphisms through fullness of `CategoryTheory.yoneda`.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 041C](https://stacks.math.columbia.edu/tag/041C)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
* [Stacks Project, Tag 0CFV](https://stacks.math.columbia.edu/tag/0CFV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale morphism of the site through a prescribed point, factoring through a given smooth
morphism.** Let `m : T ⟶ U` be a morphism of the big fppf category over `S` which is smooth on
underlying schemes and let `x` be a point of the scheme of `U` in the image of `m`. Then there is
a morphism `c : R ⟶ T` of the site whose composite with `m` is étale and hits `x`.

**Stacks 055U** produces an étale neighbourhood of `(U, x)` together with a lift of its structure
morphism through `m`, but the scheme underlying that neighbourhood is arbitrary and need not
satisfy the size cutoff of `B`. Restricting to an affine open neighbourhood of the distinguished
point keeps all three conclusions and makes the source affine, hence quasi-compact and of size
bounded by that of `U`. -/
theorem exists_etale_site_factorisation_of_smooth {U T : BigFppfOver B S hS} (m : T ⟶ U)
    (hm : Smooth ((BigFppfOver.toScheme B S hS).map m))
    (x : (BigFppfOver.toScheme B S hS).obj U)
    (hx : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map m)) :
    ∃ (R : BigFppfOver B S hS) (c : R ⟶ T),
      Etale ((BigFppfOver.toScheme B S hS).map (c ≫ m)) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c ≫ m)) := by
  obtain ⟨N, g, hg⟩ :=
    exists_etaleNeighborhood_lift_of_smooth ((BigFppfOver.toScheme B S hS).map m) x hx
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := N.scheme) (x := N.point) (U := ⊤) trivial
  have : IsAffine V.toScheme := hV
  have hcontains : B.Contains V.toScheme :=
    (Scheme.size_le_of_locallyOfFiniteType (V.ι ≫ N.toBase)).trans_lt U.left.property
  let cs : B.obj hcontains ⟶ T.left := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hcontains) ⟶ B.inclusion.obj T.left from V.ι ≫ g)
  let R : BigFppfOver B S hS := Over.mk (cs ≫ T.hom)
  let c : R ⟶ T := Over.homMk cs
  have hc : (BigFppfOver.toScheme B S hS).map c = V.ι ≫ g := B.inclusion.map_preimage _
  have hkey : (BigFppfOver.toScheme B S hS).map (c ≫ m) = V.ι ≫ N.toBase := by
    rw [Functor.map_comp, hc, Category.assoc, hg]
  refine ⟨R, c, ?_, ?_⟩ <;> rw [hkey]
  · infer_instance
  · exact ⟨⟨N.point, hpV⟩, N.map_point⟩

/-- Every point of the scheme of `U` is hit by an étale morphism of the site factoring through
some member of a smooth covering of `yoneda.obj U` by representables. -/
private theorem exists_etale_site_factorisation_of_isSmoothCovering {I : Type v}
    {U : BigFppfOver B S hS} {Z : I → BigFppfOver B S hS} {q : ∀ i, Z i ⟶ U}
    (hq : IsSmoothCovering B S hS (fun i => yoneda.obj (Z i)) (fun i => yoneda.map (q i)))
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (i : I) (R : BigFppfOver B S hS) (e : R ⟶ Z i),
      Etale ((BigFppfOver.toScheme B S hS).map (e ≫ q i)) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (e ≫ q i)) := by
  obtain ⟨y, rfl⟩ := (bijective_pointsToScheme B S hS U).surjective x
  obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hq.jointly_surjective y)
  refine ⟨i, exists_etale_site_factorisation_of_smooth B S hS (q i)
    ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS Smooth.isEtaleLocalOnSourceAndTarget
      (q i)).1 (hq.smooth i)) (pointsToScheme B S hS U y) ⟨pointsToScheme B S hS (Z i) t, ?_⟩⟩
  rw [← pointsToScheme_pointsMap_yoneda B S hS (q i) t, ht]

/-- An algebraic space admits an étale morphism from a representable presheaf which is
surjective on points. -/
private theorem exists_etale_surjective_pointsMap_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ F),
      IsEtale B S hS b ∧ Function.Surjective (pointsMap B S hS (yoneda.obj W) b) := by
  obtain ⟨W, b, hs, he⟩ := hF.exists_atlas
  exact ⟨W, b, (isEtale_iff_presheaf_of_yoneda B S hS b).2 he,
    surjective_pointsMap_of_presheaf_surjective B S hS b hs⟩

/-- Precomposing the members of a smooth covering with étale morphisms from representables that
are surjective on points gives a smooth covering by representables. -/
private theorem IsSmoothCovering.comp_etale_atlas {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hsm : IsSmoothCovering B S hS X f) {W : I → BigFppfOver B S hS}
    {b : ∀ i, yoneda.obj (W i) ⟶ X i} (hb : ∀ i, IsEtale B S hS (b i))
    (hbpts : ∀ i, Function.Surjective (pointsMap B S hS (yoneda.obj (W i)) (b i))) :
    IsSmoothCovering B S hS (fun i => yoneda.obj (W i)) (fun i => b i ≫ f i) := by
  refine ⟨hsm.target_isAlgebraicSpace, fun i => isAlgebraicSpace_yoneda B S hS (W i),
    fun i => isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS (W i))
      (hsm.source_isAlgebraicSpace i) hsm.target_isAlgebraicSpace (b i) (f i)
      (isSmooth_of_isEtale B S hS (hsm.source_isAlgebraicSpace i) (hb i)) (hsm.smooth i), ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun p => ?_
  obtain ⟨i, r, hr⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hsm.jointly_surjective p)
  obtain ⟨q, hq⟩ := hbpts i r
  refine Set.mem_iUnion.mpr ⟨i, q, ?_⟩
  rw [pointsMap_comp B S hS (yoneda.obj (W i)) (b i) (f i), Function.comp_apply, hq, hr]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for pullbacks of presheaves on the big fppf site, used throughout the proof
/-- **Stacks 0CFV.** Every smooth covering of an algebraic space over `S` is refined by an étale
covering: there are an étale covering of the same target, whose members are schemes of the site,
and, for each of its members, a member of the given covering together with a morphism to it over
the common target. -/
@[stacks 0CFV "the refinement with every member of it representable by a scheme of the site"]
theorem exists_isEtaleCovering_representable_refining_isSmoothCovering
    {I : Type v} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (hsm : IsSmoothCovering B S hS X f) :
    ∃ (J : Type (u + 1)) (Y : J → BigFppfOver B S hS) (g : ∀ j, yoneda.obj (Y j) ⟶ F),
      IsEtaleCovering B S hS (fun j => yoneda.obj (Y j)) g ∧
        ∀ j, ∃ (i : I) (h : yoneda.obj (Y j) ⟶ X i), h ≫ f i = g j := by
  classical
  obtain ⟨U, a, ha, hapts⟩ :=
    exists_etale_surjective_pointsMap_of_isAlgebraicSpace B S hS hsm.target_isAlgebraicSpace
  choose W b hb hbpts using fun i =>
    exists_etale_surjective_pointsMap_of_isAlgebraicSpace B S hS (hsm.source_isAlgebraicSpace i)
  let Xs : AlgebraicSpaces B S hS := ⟨F, hsm.target_isAlgebraicSpace⟩
  let Us : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let Ws : I → AlgebraicSpaces B S hS :=
    fun i => ⟨yoneda.obj (W i), isAlgebraicSpace_yoneda B S hS (W i)⟩
  let asp : Us ⟶ Xs := ObjectProperty.homMk a
  let bsp : ∀ i, Ws i ⟶ Xs := fun i => ObjectProperty.homMk (b i ≫ f i)
  have hPcov : IsSmoothCovering B S hS (fun i => pullback a (b i ≫ f i))
      (fun i => pullback.fst a (b i ≫ f i)) :=
    isSmoothCovering_fiberProduct B S hS Ws bsp asp (hsm.comp_etale_atlas B S hS hb hbpts)
  choose Z d hdet hdpts using fun i =>
    exists_etale_surjective_pointsMap_of_isAlgebraicSpace B S hS (hPcov.source_isAlgebraicSpace i)
  obtain ⟨q, hqmap⟩ : ∃ q : ∀ i, Z i ⟶ U,
      ∀ i, yoneda.map (q i) = d i ≫ pullback.fst a (b i ≫ f i) :=
    ⟨fun i => yoneda.preimage _, fun i => yoneda.map_preimage _⟩
  choose idx R e hRet hRpt using exists_etale_site_factorisation_of_isSmoothCovering B S hS
    (q := q) (by simpa only [hqmap] using hPcov.comp_etale_atlas B S hS hdet hdpts)
  refine ⟨ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj U), fun j => R j.down,
    fun j => yoneda.map (e j.down ≫ q (idx j.down)) ≫ a,
    ⟨hsm.target_isAlgebraicSpace, fun j => isAlgebraicSpace_yoneda B S hS (R j.down),
      fun j => isEtale_comp B S hS
        ((isEtale_iff_presheaf_of_yoneda B S hS _).2
          ((presheaf_yoneda_map_etale_iff B S hS _).2 (hRet j.down))) ha, ?_⟩, fun j =>
    ⟨idx j.down, yoneda.map (e j.down) ≫ d (idx j.down) ≫
      pullback.snd a (b (idx j.down) ≫ f (idx j.down)) ≫ b (idx j.down), ?_⟩⟩
  · refine Set.eq_univ_iff_forall.mpr fun p => ?_
    obtain ⟨y, hy⟩ := hapts p
    obtain ⟨s, hs⟩ := hRpt (pointsToScheme B S hS U y)
    obtain ⟨r, hr⟩ :=
      (bijective_pointsToScheme B S hS (R (pointsToScheme B S hS U y))).surjective s
    refine Set.mem_iUnion.mpr ⟨ULift.up (pointsToScheme B S hS U y), r, ?_⟩
    have hy' : pointsMap B S hS (yoneda.obj (R (pointsToScheme B S hS U y)))
        (yoneda.map (e (pointsToScheme B S hS U y) ≫ q (idx (pointsToScheme B S hS U y)))) r
          = y :=
      (bijective_pointsToScheme B S hS U).injective
        (by rw [pointsToScheme_pointsMap_yoneda, hr, hs])
    rw [pointsMap_comp B S hS (yoneda.obj (R (pointsToScheme B S hS U y))) _ a,
      Function.comp_apply, hy', hy]
  · simp only [Functor.map_comp, hqmap, Category.assoc, pullback.condition]

end AlgebraicGeometry.Space

end
