module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMRelativePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Composition of locally quasi-finite 1-morphisms of algebraic stacks (Stacks 06UD)

A composite of locally quasi-finite 1-morphisms of algebraic stacks over `S` is locally
quasi-finite. Local quasi-finiteness (**Stacks 06PU**) is a conjunction of three conditions and
each is treated separately: the quasi-DM condition composes by **Stacks 050K**, local finite
type by **Stacks 06FT**, and the third condition — discreteness of the space of points of every
field-valued fibre — is the content of the source's proof.

For that third condition, a field-valued point `p : Spec(k) ⟶ 𝒵` of the final target gives the
fibre `𝒴_k` of `g` over `p`, and pasting the canonical 2-fibre-product squares (**Stacks 02XD**)
exhibits the fibre of `f ≫ g` over `p` as a 2-fibre product of the cospan `(f, 𝒴_k ⟶ 𝒴)`, i.e.
as `𝒳 ×_𝒴 𝒴_k`. By **Stacks 06UB** the two base changes `𝒳 ×_𝒴 𝒴_k ⟶ 𝒴_k` and `𝒴_k ⟶ Spec(k)`
are again locally quasi-finite, so everything is reduced to the case of a target which is
locally quasi-finite over a field; that case is
`AlgebraicGeometry.Stack.AlgebraicStacks.discreteTopology_points_of_isLocallyQuasiFinite_over_field`
below.

## The case of a target locally quasi-finite over a field

Let `h : 𝒲 ⟶ 𝒴₀` and `q : 𝒴₀ ⟶ Spec(k)` be locally quasi-finite. The source's argument charts
`𝒴₀` by a scheme `V` with a flat, locally finitely presented, locally quasi-finite surjection
(**Stacks 06MF**), writes `V` as a disjoint union of spectra of Artinian local rings
(**Stacks 06LH**) and compares the points of `Spec(A) ×_{𝒴₀} 𝒲` with those of
`Spec(A/𝔪) ×_{𝒴₀} 𝒲`. Since only the topology of `|𝒲|` is at stake, the argument here replaces
that chart by the spectrum of a local ring at a generic point of a smooth chart, which is flat
but not of finite presentation, and uses flatness only through the lifting of generalizations.

1. `|𝒴₀|` is discrete by the third clause of **Stacks 06PU** for `q` at the identity of
   `Spec(k)`.
2. Let `V ⟶ 𝒴₀` be a smooth surjective chart by a scheme, `v` a point of `V` over the image `y`
   of a given point of `𝒲`, and `η` the generic point of an irreducible component of `V` through
   `v`. The image of `η` is a generalization of `y`, hence is `y`. The spectrum `E` of the local
   ring `𝒪_{V,η}` has exactly one point, and `E ⟶ V ⟶ 𝒴₀` is flat.
3. The base change `P = 𝒲 ×_{𝒴₀} E` has no nontrivial specializations. Indeed
   `Spec κ ⟶ E`, for `κ` the residue field of the point of `E`, is a surjective closed immersion,
   so its base change `P' ⟶ P` is surjective and closed on points (**Stacks 0CL8**,
   **Stacks 0H20**), while `|P'|` is the field-valued fibre `|Spec κ ×_{𝒴₀} 𝒲|`, discrete by
   the third clause of Stacks 06PU for `h`.
4. For any 1-morphism `a : U ⟶ 𝒲` from a scheme, the induced map `|U| ⟶ |𝒲|` is constant on
   specializations. Given `u' ⤳ u`, lift `u` to a point of a scheme chart `U''` of
   `U ×_𝒲 P = U ×_{𝒴₀} E`; the morphism of schemes `U'' ⟶ U` is flat, so `u' ⤳ u` lifts to a
   specialization in `U''` (**Stacks 03HV**), whose image in `|P|` is trivial by step 3.
5. Choosing for `U` a smooth surjective chart of `𝒲`, the scheme `U` is locally of finite type
   over `k`, hence locally Noetherian, and each fibre of `|U| ⟶ |𝒲|` is stable under
   specialization and generalization by step 4, hence open. The map `|U| ⟶ |𝒲|` is open and
   surjective, so every point of `|𝒲|` is open.

No hypothesis is carried: in particular neither Stacks 06MF nor Stacks 06UC is used.

## Main results

* `AlgebraicGeometry.Stack.representingMap_eq_yoneda_map_siteMap`,
  `AlgebraicGeometry.Stack.flat_siteMap_of_isFlat` and
  `AlgebraicGeometry.Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType`: a flat,
  respectively locally of finite type, 1-morphism between the algebraic stacks of two schemes of
  the site comes from a flat, respectively locally of finite type, morphism of schemes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_schemeStackMap`: a closed immersion
  of the site induces a closed immersion of the represented algebraic stacks.
* `...AlgebraicStacks.eq_of_specializes_of_subsingleton_of_isLocallyQuasiFinite`: step 3 above.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_specializes_of_isLocallyQuasiFinite`:
  step 4 above.
* `...AlgebraicStacks.discreteTopology_points_of_isLocallyQuasiFinite_over_field`: an algebraic
  stack locally quasi-finite over a stack which is locally quasi-finite over a field has discrete
  space of points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_comp`: **Stacks 06UD**.

## Implementation notes

`AlgebraicGeometry.Stack.pointTopology` is a `def` and not an instance, so the topologies are
supplied explicitly throughout, exactly as in **Stacks 06UB**.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03HV](https://stacks.math.columbia.edu/tag/03HV)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
* [Stacks Project, Tag 06UD](https://stacks.math.columbia.edu/tag/06UD)
* [Stacks Project, Tag 0CL8](https://stacks.math.columbia.edu/tag/0CL8)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology
  AlgebraicGeometry.Stack.reprPointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of representing presheaves of a 1-morphism of represented algebraic stacks.**
A 1-morphism `c` between the algebraic stacks of two schemes `U`, `V` of the site induces, under
the identification of each slice with the category of elements of the presheaf its scheme
represents, the morphism `yoneda.map` of the morphism of the site underlying `c`.

The 1-morphism `c` is 2-isomorphic to the one induced by that morphism of the site
(`AlgebraicGeometry.Stack.schemeStackMapIso`), 2-isomorphic 1-morphisms have the same
representing map, and the representing map of an induced 1-morphism is
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`. -/
theorem representingMap_eq_yoneda_map_siteMap {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V) :
    representingMap B S hS (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
        (yoneda.obj U) (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (PresheafOfCategories.sliceElementsEquivalenceOver V) c.hom =
      yoneda.map (siteMap B S hS c) := by
  let e := schemeStackMapIso B S hS c
  let η : c.hom ≅ (schemeStackMap.{u, w} B S hS (siteMap B S hS c)).hom :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
      inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id }
  rw [representingMap_congr_twoIso B S hS (yoneda.obj U) (yoneda.obj V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V) η]
  exact representingMap_schemeFibredCategoryMap B S hS _

/-- A property of 1-morphisms of represented algebraic stacks holding on some smooth diagram
holds, for the morphism of schemes underlying the 1-morphism, on every étale chart. -/
private theorem toScheme_map_siteMap_of_hasPropertyOnSomeSmoothDiagram
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P) {Q : MorphismProperty Scheme.{u}}
    (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (hPQ : ∀ {V U : BigFppfOver B S hS} (k : V ⟶ U),
      P (yoneda.map k) → Space.HoldsOnEveryEtaleChart B S hS Q (yoneda.map k))
    {U V : BigFppfOver B S hS} (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : HasPropertyOnSomeSmoothDiagram B S hS P c.hom) :
    Q ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) := by
  have h := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _ hP
      (schemeStack.{u, w} B S hS U).property (schemeStack.{u, w} B S hS V).property
      (yoneda.obj U) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V) c.hom).1 hc
  rw [representingMap_eq_yoneda_map_siteMap] at h
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS hQ _).1 (hPQ _ h)

/-- **A flat 1-morphism of represented algebraic stacks comes from a flat morphism of
schemes.** Flatness of `c` (**Stacks 06PW**) is the existential smooth-diagram test of
**Stacks 06FM**, which for represented source and target is flatness of the induced morphism of
representing algebraic spaces, i.e. of `yoneda.map` of the morphism of the site underlying `c`,
i.e. of that morphism of schemes. -/
theorem flat_siteMap_of_isFlat {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : AlgebraicStacks.IsFlat B S hS c) :
    Flat ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) :=
  toScheme_map_siteMap_of_hasPropertyOnSomeSmoothDiagram B S hS
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) Flat.isEtaleLocalOnSourceAndTarget
    (fun _ => id) c ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS c).1 hc)

/-- **A 1-morphism of represented algebraic stacks which is locally of finite type comes from a
morphism of schemes locally of finite type.** Local finite type of `c` (**Stacks 06FS**,
part (1)) is the universal smooth-diagram test of **Stacks 06FM**; its existential form is, for
represented source and target, local finite type of `yoneda.map` of the morphism of the site
underlying `c`, i.e. of that morphism of schemes. -/
theorem locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) :=
  toScheme_map_siteMap_of_hasPropertyOnSomeSmoothDiagram B S hS
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (fun _ => id) c
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (schemeStack.{u, w} B S hS U).property (schemeStack.{u, w} B S hS V).property _).1 hc)

namespace AlgebraicStacks

/-- **A closed immersion of the site induces a closed immersion of the represented algebraic
stacks.** Being a closed immersion is stable under base change for morphisms of algebraic spaces
and fppf local on the target (**Stacks 0420**), so the relative property of Stacks 03YK at
closed immersions holds for the induced 1-morphism as soon as it holds for the morphism of
representable algebraic spaces that the morphism of the site induces. -/
theorem isClosedImmersion_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsClosedImmersion B S hS (Stack.schemeStackMap.{u, w} B S hS g) := by
  refine ⟨Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g, ?_⟩
  exact Stack.hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
    (Space.closedImmersionProperty B S hS) g
    ((Space.presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance g).2 hg)

/-- **A base change of a locally quasi-finite 1-morphism along a one-point scheme has no
nontrivial specializations.** Let `h : 𝒲 ⟶ 𝒴₀` be locally quasi-finite and `e : E ⟶ 𝒴₀` a
1-morphism from the algebraic stack of a scheme `E` of the site with at most one point. Then the
specialization relation on the points of `𝒲 ×_{𝒴₀} E` is trivial.

For `κ` the residue field of the point of `E`, the morphism `Spec κ ⟶ E` is a closed immersion
which is surjective, so its base change `P' ⟶ 𝒲 ×_{𝒴₀} E` is closed on points (**Stacks 0CL8**)
and every point of `𝒲 ×_{𝒴₀} E` lifts to `P'` (**Stacks 04XH**); and `P'` is a 2-fibre product
of `h` with the field-valued point `Spec κ ⟶ E ⟶ 𝒴₀` (**Stacks 02XD**), so `|P'|` is discrete by
the third clause of **Stacks 06PU**. A specialization `p₁ ⤳ p₂` therefore lifts to a
specialization in `|P'|` starting at any lift of `p₁`, which is trivial. -/
theorem eq_of_specializes_of_subsingleton_of_isLocallyQuasiFinite
    {𝒲 𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS} (h : 𝒲 ⟶ 𝒴₀)
    (hh : IsLocallyQuasiFinite B S hS h) {E : BigFppfOver B S hS}
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj E)]
    (e : Stack.schemeStack.{u, w} B S hS E ⟶ 𝒴₀)
    (p₁ p₂ : points B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS h e).pt)
    (hp : @Specializes _
      (Stack.pointTopology B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS h e).pt.val)
      p₁ p₂) :
    p₁ = p₂ := by
  classical
  let P := Stack.twoFibreProductSquareAlgebraicStacks B S hS h e
  have hP : Bicategory.IsTwoFibreProduct P :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h e
  set Z := (BigFppfOver.toScheme B S hS).obj E with hZ
  let z₀ : Z := Stack.pointsHomeomorphScheme B S hS E (pointsMap B S hS P.snd p₂)
  have hz₀ : _root_.IsClosed ({z₀} : Set Z) := by
    have hu : ({z₀} : Set Z) = Set.univ :=
      Set.eq_univ_of_forall (fun z => (Subsingleton.elim z z₀ : z ∈ ({z₀} : Set Z)))
    rw [hu]
    exact isClosed_univ
  have hι : AlgebraicGeometry.IsClosedImmersion (Z.fromSpecResidueField z₀) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz₀
  have hκ : B.Contains (Spec (.of (Z.residueField z₀))) :=
    BigFppfSite.residueField_spec_contains B E.left.2 z₀
  let ι : Spec (.of (Z.residueField z₀)) ⟶ Z := Z.fromSpecResidueField z₀
  let toBaseκ : Spec (.of (Z.residueField z₀)) ⟶ S := ι ≫ B.inclusion.map E.hom
  let K : BigFppfOver B S hS := Over.mk (⟨toBaseκ⟩ : B.obj hκ ⟶ B.obj hS)
  let i : K ⟶ E := Over.homMk ⟨ι⟩ rfl
  let iS := Stack.schemeStackMap.{u, w} B S hS i
  have hiCI : IsClosedImmersion B S hS iS := isClosedImmersion_schemeStackMap.{u, w} B S hS i hι
  let P' := Stack.twoFibreProductSquareAlgebraicStacks B S hS P.snd iS
  have hP' : Bicategory.IsTwoFibreProduct P' :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.snd iS
  have hclosed : IsClosedMap (pointsMap B S hS P'.fst) :=
    universallyClosed_of_isClosedImmersion B S hS iS hiCI P.pt P.snd
  have hdisc0 := hh.2.2 (Z.residueField z₀) hκ toBaseκ (iS ≫ e)
  have hdisc : @DiscreteTopology (Stack.points B S hS P'.pt.val.val P'.pt.val.property)
      (Stack.pointTopology B S hS P'.pt.val) :=
    Stack.discreteTopology_points_congr B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS h (iS ≫ e)).underlying
      (P.paste P').underlying
      (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h (iS ≫ e)))
      (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (Bicategory.isTwoFibreProduct_paste hP hP'))
      hdisc0
  let _ := hdisc
  have hEsub : Subsingleton (points B S hS (Stack.schemeStack.{u, w} B S hS E)) :=
    (Stack.pointsHomeomorphScheme B S hS E).injective.subsingleton
  obtain ⟨r₁, hr₁, -⟩ := exists_point_of_isTwoFibreProduct B S hS P' hP' p₁
    ((Stack.pointsHomeomorphScheme B S hS K).symm
      (IsLocalRing.closedPoint (Z.residueField z₀) : Spec (.of (Z.residueField z₀))))
    (Subsingleton.elim _ _)
  have hmem : p₂ ∈ pointsMap B S hS P'.fst '' closure {r₁} := by
    have hcl : _root_.IsClosed (pointsMap B S hS P'.fst '' closure {r₁}) :=
      hclosed _ isClosed_closure
    have h₁ : p₁ ∈ pointsMap B S hS P'.fst '' closure {r₁} := ⟨r₁, subset_closure rfl, hr₁⟩
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h₁)
      (specializes_iff_mem_closure.mp hp)
  obtain ⟨r₂, hr₂mem, hr₂⟩ := hmem
  have hr : r₁ = r₂ := (specializes_iff_mem_closure.mpr hr₂mem).eq
  rw [← hr₁, ← hr₂, hr]

/-- A 1-morphism from the algebraic stack of a scheme `U` preserves specializations of points of
`U`, read through `AlgebraicGeometry.Stack.pointsHomeomorphScheme`. -/
private theorem specializes_pointsMap_symm {U : BigFppfOver B S hS}
    {𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (c : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒵)
    {z' z : (BigFppfOver.toScheme B S hS).obj U} (hz : z' ⤳ z) :
    pointsMap B S hS c ((Stack.pointsHomeomorphScheme B S hS U).symm z') ⤳
      pointsMap B S hS c ((Stack.pointsHomeomorphScheme B S hS U).symm z) :=
  hz.map ((Stack.continuous_pointsMap B S hS (Stack.schemeStack.{u, w} B S hS U).val 𝒵.val
    c.hom.hom).comp (Stack.pointsHomeomorphScheme B S hS U).symm.continuous)

/-- **A scheme maps to a stack locally quasi-finite over a stack locally quasi-finite over a
field constantly along specializations.** Let `h : 𝒲 ⟶ 𝒴₀` and `q : 𝒴₀ ⟶ Spec(k)` be locally
quasi-finite, `k` a field whose spectrum is a scheme of the site over `S`, and let
`a : U ⟶ 𝒲` be any 1-morphism from the algebraic stack of a scheme `U` of the site. If `u'`
specializes to `u` in `U`, then `u'` and `u` have the same image in `|𝒲|`.

Let `y` be the image of `u` in `|𝒴₀|`, `V ⟶ 𝒴₀` a smooth surjective chart by a scheme, `v` a
point of `V` over `y` and `η` the generic point of an irreducible component of `V` through `v`.
The image of `η` specializes to `y`, so it is `y`, `|𝒴₀|` being discrete
(`AlgebraicGeometry.Stack.AlgebraicStacks.discreteTopology_points_of_isLocallyQuasiFinite`). The
spectrum `E` of `𝒪_{V,η}` has a single point, since `η` has no proper generalization, and
`E ⟶ V ⟶ 𝒴₀` is flat. Put `P = 𝒲 ×_{𝒴₀} E` and `Q = U ×_𝒲 P`; then `Q ⟶ U` is flat
(**Stacks 06PY**), and so is the morphism of schemes `U'' ⟶ U` for a smooth surjective chart
`U'' ⟶ Q` by a scheme. A point of `U''` over `u` and over a point `p` of `P` above `u` and the
point of `E` (**Stacks 04XH**) lifts `u' ⤳ u` to a specialization in `U''` (**Stacks 03HV**), whose
image in `|P|` is a specialization ending at `p`, hence trivial by
`AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_specializes_of_subsingleton_of_isLocallyQuasiFinite`;
mapping to `|𝒲|` through `P` and through `U` gives the claim. -/
theorem pointsMap_eq_of_specializes_of_isLocallyQuasiFinite
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    {𝒲 𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS} (h : 𝒲 ⟶ 𝒴₀)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hh : IsLocallyQuasiFinite B S hS h) (hq : IsLocallyQuasiFinite B S hS q)
    {U : BigFppfOver B S hS} (a : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒲)
    {u' u : (BigFppfOver.toScheme B S hS).obj U} (hu : u' ⤳ u) :
    pointsMap B S hS a ((Stack.pointsHomeomorphScheme B S hS U).symm u') =
      pointsMap B S hS a ((Stack.pointsHomeomorphScheme B S hS U).symm u) := by
  classical
  have hY := discreteTopology_points_of_isLocallyQuasiFinite B S hS k hk toBase q hq
  set uS := (Stack.pointsHomeomorphScheme B S hS U).symm u with huS
  set x := pointsMap B S hS a uS with hx
  -- A smooth chart of `𝒴₀` and a generic point over the image of `x`.
  obtain ⟨V, b, hbSm, hbSurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴₀
  obtain ⟨vS, hvS⟩ := hbSurj (pointsMap B S hS h x)
  set X := (BigFppfOver.toScheme B S hS).obj V with hX
  let v : X := Stack.pointsHomeomorphScheme B S hS V vS
  have hC := irreducibleComponent_mem_irreducibleComponents v
  let η : X := hC.1.genericPoint
  have hηcl : closure {η} = irreducibleComponent v :=
    hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hηv : η ⤳ v := specializes_iff_mem_closure.mpr (hηcl ▸ mem_irreducibleComponent)
  have hηmax : ∀ z : X, z ⤳ η → z = η := by
    intro z hz
    have h₁ : closure {η} ⊆ closure {z} :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
        isClosed_closure
    have h₂ : closure {z} ⊆ closure {η} := by
      rw [hηcl] at h₁ ⊢
      exact hC.2 isIrreducible_singleton.closure h₁
    exact (hz.antisymm (specializes_iff_mem_closure.mpr (h₂ (subset_closure rfl)))).eq
  have hbη : pointsMap B S hS b ((Stack.pointsHomeomorphScheme B S hS V).symm η) =
      pointsMap B S hS h x := by
    have hsp := specializes_pointsMap_symm B S hS b hηv
    simp only [v, Homeomorph.symm_apply_apply, hvS] at hsp
    exact hsp.eq
  -- The spectrum of the local ring at the generic point.
  let ν := X.fromSpecStalk η
  have hc : B.Contains (Spec (X.presheaf.stalk η)) := BigFppfSite.contains_of_mono B ν V.left.2
  let ν₀ : B.obj hc ⟶ V.left := B.inclusion.preimage ν
  have hν₀ : B.inclusion.map ν₀ = ν := B.inclusion.map_preimage (X := B.obj hc) (Y := V.left) ν
  let E : BigFppfOver B S hS := Over.mk (ν₀ ≫ V.hom)
  let j : E ⟶ V := Over.homMk ν₀
  have hj : (BigFppfOver.toScheme B S hS).map j = ν := hν₀
  have hνη : ∀ z, ν z = η := fun z => hηmax _ (by
    have hz := Set.mem_range_self (f := ν) z
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz)
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj E) :=
    ⟨fun z₁ z₂ => ν.isEmbedding.injective ((hνη z₁).trans (hνη z₂).symm)⟩
  have hjflat : Flat ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hj]
    exact flat_fromSpecStalk X η
  let e : Stack.schemeStack.{u, w} B S hS E ⟶ 𝒴₀ := Stack.schemeStackMap.{u, w} B S hS j ≫ b
  have he : IsFlat B S hS e :=
    isFlat_comp B S hS _ b (Stack.isFlat_schemeFibredCategoryMap.{u, w} B S hS j hjflat)
      (isFlat_of_isSmooth B S hS b hbSm)
  let eS : points B S hS (Stack.schemeStack.{u, w} B S hS E) :=
    (Stack.pointsHomeomorphScheme B S hS E).symm (IsLocalRing.closedPoint (X.presheaf.stalk η))
  have heS : pointsMap B S hS e eS = pointsMap B S hS h x := by
    have hjS : pointsMap B S hS (Stack.schemeStackMap.{u, w} B S hS j) eS =
        (Stack.pointsHomeomorphScheme B S hS V).symm η := by
      apply (Stack.pointsHomeomorphScheme B S hS V).injective
      rw [Homeomorph.apply_symm_apply, Stack.pointsHomeomorphScheme_pointsMap,
        Stack.siteMap_schemeStackMap, hj]
      exact hνη _
    rw [pointsMap_comp, Function.comp_apply, hjS, hbη]
  -- The base change `P = 𝒲 ×_{𝒴₀} E` and the point over `x` and `eS`.
  set P := Stack.twoFibreProductSquareAlgebraicStacks B S hS h e with hPdef
  have hP : Bicategory.IsTwoFibreProduct P :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h e
  have hPflat : IsFlat B S hS P.fst := isFlat_baseChange B S hS e h P hP he
  obtain ⟨p, hp1, -⟩ := exists_point_of_isTwoFibreProduct B S hS P hP x eS heS.symm
  -- The base change `Q = U ×_𝒲 P` and a scheme chart of it.
  set Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS a P.fst with hQdef
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a P.fst
  have hQflat : IsFlat B S hS Q.fst := isFlat_baseChange B S hS P.fst a Q hQ hPflat
  obtain ⟨qq, hq1, hq2⟩ := exists_point_of_isTwoFibreProduct B S hS Q hQ uS p hp1.symm
  obtain ⟨U'', c, hcSm, hcSurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS Q.pt
  obtain ⟨wS, hwS⟩ := hcSurj qq
  have hgflat : Flat ((BigFppfOver.toScheme B S hS).map (Stack.siteMap B S hS (c ≫ Q.fst))) :=
    Stack.flat_siteMap_of_isFlat B S hS _
      (isFlat_comp B S hS c Q.fst (isFlat_of_isSmooth B S hS c hcSm) hQflat)
  have hgw : (BigFppfOver.toScheme B S hS).map (Stack.siteMap B S hS (c ≫ Q.fst))
      (Stack.pointsHomeomorphScheme B S hS U'' wS) = u := by
    rw [← Stack.pointsHomeomorphScheme_pointsMap, pointsMap_comp, Function.comp_apply, hwS, hq1,
      huS, Homeomorph.apply_symm_apply]
  obtain ⟨w', hw'w, hgw'⟩ := Flat.generalizingMap
    ((BigFppfOver.toScheme B S hS).map (Stack.siteMap B S hS (c ≫ Q.fst))) (hgw ▸ hu)
  -- The image of the lifted specialization in `|P|` is trivial.
  set w'S := (Stack.pointsHomeomorphScheme B S hS U'').symm w' with hw'S
  have hρ := specializes_pointsMap_symm B S hS (c ≫ Q.snd) hw'w
  simp only [Homeomorph.symm_apply_apply] at hρ
  have hρw : pointsMap B S hS (c ≫ Q.snd) wS = p := by
    rw [pointsMap_comp, Function.comp_apply, hwS, hq2]
  have hρeq : pointsMap B S hS (c ≫ Q.snd) w'S = p :=
    eq_of_specializes_of_subsingleton_of_isLocallyQuasiFinite B S hS h hh e _ _ (hρw ▸ hρ)
  -- Conclusion.
  have hu'S : (Stack.pointsHomeomorphScheme B S hS U).symm u' =
      pointsMap B S hS (c ≫ Q.fst) w'S := by
    apply (Stack.pointsHomeomorphScheme B S hS U).injective
    rw [Homeomorph.apply_symm_apply, Stack.pointsHomeomorphScheme_pointsMap, hw'S,
      Homeomorph.apply_symm_apply, hgw']
  have e1 := congrFun (pointsMap_comp B S hS c Q.fst) w'S
  have e2 := congrFun (pointsMap_comp B S hS Q.fst a) (pointsMap B S hS c w'S)
  have e3 := congrFun (pointsMap_eq_of_hom₂ B S hS Q.iso.hom) (pointsMap B S hS c w'S)
  have e4 := congrFun (pointsMap_comp B S hS Q.snd P.fst) (pointsMap B S hS c w'S)
  have e5 := congrFun (pointsMap_comp B S hS c Q.snd) w'S
  simp only [Function.comp_apply] at e1 e2 e4 e5
  rw [hu'S, e1, ← e2, e3, e4, ← e5, hρeq, hp1]

/-- **A stack locally quasi-finite over a stack locally quasi-finite over a field has discrete
space of points.** If `h : 𝒲 ⟶ 𝒴₀` and `q : 𝒴₀ ⟶ Spec(k)` are locally quasi-finite, `k` a field
whose spectrum is a point of the site over `S`, then the space of points of `𝒲` is discrete.

This is the case of **Stacks 06UD** to which the source reduces its third condition. Let
`U ⟶ 𝒲` be a smooth surjective chart by a scheme. The composite `U ⟶ Spec(k)` is locally of
finite type (**Stacks 06FT**), so `U` is locally Noetherian; each fibre of `|U| ⟶ |𝒲|` is stable
under specialization and generalization by
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_specializes_of_isLocallyQuasiFinite`,
hence open; and `|U| ⟶ |𝒲|` is open (**Stacks 06R7**) and surjective, so each point of `|𝒲|` is
open. -/
theorem discreteTopology_points_of_isLocallyQuasiFinite_over_field
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (𝒲 𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS) (h : 𝒲 ⟶ 𝒴₀)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hh : IsLocallyQuasiFinite B S hS h) (hq : IsLocallyQuasiFinite B S hS q) :
    @DiscreteTopology (Stack.points B S hS 𝒲.val.val 𝒲.val.property)
      (Stack.pointTopology B S hS 𝒲.val) := by
  classical
  obtain ⟨U, a, haSm, haSurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒲
  let π : (BigFppfOver.toScheme B S hS).obj U → points B S hS 𝒲 :=
    fun z => pointsMap B S hS a ((Stack.pointsHomeomorphScheme B S hS U).symm z)
  have hπ : ∀ {u' u}, u' ⤳ u → π u' = π u := fun hu =>
    pointsMap_eq_of_specializes_of_isLocallyQuasiFinite B S hS k hk toBase h q hh hq a hu
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (Stack.siteMap B S hS (a ≫ h ≫ q))) :=
    Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S hS _
      (isLocallyOfFiniteType_comp B S hS a (h ≫ q)
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
          (isLocallyOfFinitePresentation_of_isSmooth B S hS a haSm))
        (isLocallyOfFiniteType_comp B S hS h q hh.2.1 hq.2.1))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).map (Stack.siteMap B S hS (a ≫ h ≫ q)))
  have hopen : IsOpenMap π :=
    (isOpenMap_pointsMap_of_isSmooth B S hS a haSm).comp
      (Stack.pointsHomeomorphScheme B S hS U).symm.isOpenMap
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  obtain ⟨uS, rfl⟩ := haSurj x
  have hF : _root_.IsOpen (π ⁻¹' {pointsMap B S hS a uS}) :=
    isOpen_of_stableUnderSpecialization_of_stableUnderGeneralization
      (finite_irreducibleComponents_of_isCompact _) (fun _ _ hab ha => (hπ hab).symm.trans ha)
      (fun _ _ hab hb => (hπ hab).trans hb)
  convert hopen _ hF using 1
  ext y
  constructor
  · rintro rfl
    exact ⟨Stack.pointsHomeomorphScheme B S hS U uS, by simp [π], by simp [π]⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- **Stacks 06UD.** A composite of locally quasi-finite 1-morphisms of algebraic stacks over
`S` is locally quasi-finite.

The quasi-DM condition composes by **Stacks 050K** and local finite type by **Stacks 06FT**. For
the third condition, the fibre of `f ≫ g` over a field-valued point `p` of `𝒵` is by
**Stacks 02XD** a 2-fibre product of the cospan `(f, 𝒴_k ⟶ 𝒴)`, where `𝒴_k` is the fibre of `g`
over `p`; both `𝒳 ×_𝒴 𝒴_k ⟶ 𝒴_k` and `𝒴_k ⟶ Spec(k)` are locally quasi-finite by
**Stacks 06UB**, so the discreteness is the case of a target locally quasi-finite over a
field. -/
@[stacks 06UD]
theorem isLocallyQuasiFinite_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsLocallyQuasiFinite B S hS f) (hg : IsLocallyQuasiFinite B S hS g) :
    IsLocallyQuasiFinite B S hS (f ≫ g) := by
  refine ⟨(isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS (f ≫ g)).2
      (isQuasiDM_comp B S hS f g
        ((isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).1 hf.1)
        ((isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS g).1 hg.1)),
    isLocallyOfFiniteType_comp B S hS f g hf.2.1 hg.2.1, ?_⟩
  intro k _ hk toBase p
  set Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS p g with hQdef
  set T := Stack.twoFibreProductSquareAlgebraicStacks B S hS Q.snd f with hTdef
  have hQfp : Bicategory.IsTwoFibreProduct Q :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p g
  have hTfp : Bicategory.IsTwoFibreProduct T :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS Q.snd f
  have hTfst : IsLocallyQuasiFinite B S hS T.fst :=
    isLocallyQuasiFinite_baseChange B S hS f Q.snd T hTfp hf
  have hQfst : IsLocallyQuasiFinite B S hS Q.fst :=
    isLocallyQuasiFinite_baseChange B S hS g p Q hQfp hg
  have hdisc := discreteTopology_points_of_isLocallyQuasiFinite_over_field B S hS
    k hk toBase T.pt Q.pt T.fst Q.fst hTfst hQfst
  exact Stack.discreteTopology_points_congr B S hS
    (Q.paste T).swap.underlying
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) p).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_paste hQfp hTfp)))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) p))
    hdisc

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
