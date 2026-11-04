module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage

/-!
# The essential image of the small étale direct image of sheaves of sets along an integral
universally injective morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. This file proves that a sheaf of sets on the small étale site of `X` lies in the
essential image of the direct image along `f` exactly when its restriction to the open
complement of the image of the point set of `Y` is the singleton sheaf. That is the
essential-image clause of Stacks 0AEH, part (1); the abelian clause is in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveEssentialImage.lean` and the
full-faithfulness and left-inverse clauses in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveSmallEtale.lean`.

## Main definitions

* `AlgebraicGeometry.Space.integralComplementSubfunctor`,
  `AlgebraicGeometry.Space.integralComplement` and
  `AlgebraicGeometry.Space.integralComplementHom`: the open complement `X ∖ f(|Y|)` of the image
  of an integral morphism, as a subfunctor of `X`, as an algebraic space, and with its open
  immersion into `X`. Its point set is `(f(|Y|))ᶜ` by
  `AlgebraicGeometry.Space.range_pointsMap_integralComplementHom`, which is what makes the clause
  below a statement about `|X| ∖ f(|Y|)`.
* `AlgebraicGeometry.Space.smallToposMorphismPushforwardRepresentable`: Stacks 03G8 at the
  universe `u + 1` of the small étale site — for a representable morphism the direct image of
  the morphism of small étale topoi of Stacks 03G2, part (3) is restriction along base change of
  étale scheme charts.

## Main results

* `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion`: a
  geometric point of `X` lying on the image of an open immersion comes from a geometric point of
  the source. An open immersion is étale and the base change along the point is surjective, so
  the section comes from `AlgebraicGeometry.Space.exists_section_of_surjective_etale_spec`.
* `AlgebraicGeometry.Space.isIso_of_bijective_stalkSetMap`: **the set-valued geometric stalks are
  conservative**, in every coefficient universe. This is the two halves of Stacks 04K5 fed into
  Mathlib's `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`.
* `AlgebraicGeometry.Space.isTerminal_inverseImage_pushforward_integralComplement`: **Étale
  Cohomology 04FX for sheaves of sets** — the restriction of a direct image along `f` to the
  complement of `f(|Y|)` is the singleton sheaf.
* `AlgebraicGeometry.Space.isIso_of_inverseImage_isIso_of_integralComplement`: a map of sheaves
  of sets invertible both on `Y` and on the complement of `f(|Y|)` is invertible.
* `AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_of_integral_universallyInjective`:
  **Stacks 0AEH, part (1), the essential image**, in both directions.

## Implementation notes

The clause is proved at `Type (u + 1)`, the coefficient universe of the morphism of small étale
topoi of Stacks 03G2, part (3), which is the `f_{small, *}` of the source; that is also where
the identification of the stalk of an inverse image with the stalk at the image point, part (4)
of Stacks 04K2, is available for sheaves of sets
(`AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso`). The same clause at `Type u` would
need that identification one universe down, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageOffSubspace` explain is not a
re-instantiation but a restatement.

Neither half of the clause is proved by reduction to charts. The "only if" half is sectionwise:
by Stacks 03LP the restriction along the open immersion of the complement is computed by
composing charts, and by Stacks 03G8 the direct image is restriction along chart base change, so
a section over a chart of the complement is a section over a chart of `Y` whose underlying
scheme is empty, of which there is exactly one. The "if" half is stalkwise, and uses the
geometric-point lift of
`AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom` on
`f(|Y|)` and the one for an open immersion on the complement — every geometric point of `X` lies
on one or the other, because the two point sets are complementary.

Universal injectivity is used only through full faithfulness, as in the source; the direct image
is the singleton sheaf off `f(|Y|)` for every integral morphism, as is the complement's being an
open subspace.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 04FZ](https://stacks.math.columbia.edu/tag/04FZ)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- A geometric point of `X` lying on the image of an open immersion comes from a geometric
point of the source. -/
theorem exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion {U : AlgebraicSpaces B S hS}
    (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS U.1 j.hom)) :
    ∃ y : GeometricPoint B S hS U.1, geometricPointMap j.hom y = x := by
  let hr := hj.rep
  let g : yoneda.obj x.val.siteObject ⟶ X.1 := yonedaEquiv.symm x.val.value
  have hgval : yonedaEquiv g = x.val.value := yonedaEquiv.apply_symm_apply _
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj (hr.pullback g)) :=
    nonempty_pullback_of_mem_range_pointsMap B S hS j hr x g hgval hx
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hr.snd g)) := hj.property_snd g
  have _ : IsAlgClosed x.val.carrier := x.property
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj x.val.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of x.val.carrier)))
  have hsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hr.snd g)) :=
    ⟨fun _ ↦ ⟨hne.some, Subsingleton.elim _ _⟩⟩
  obtain ⟨sec, hsec⟩ := exists_section_of_surjective_etale_spec x.val.carrier
    ((BigFppfOver.toScheme B S hS).map (hr.snd g))
  exact exists_geometricPoint_map_eq_of_scheme_section B S hS j hr x g hgval sec hsec

/-- **Stacks 03G8 at the universe of the small étale site.** For a representable morphism of
algebraic spaces the direct image of sheaves of sets of the morphism of small étale topoi of
Stacks 03G2, part (3) is restriction along base change of étale scheme charts.

This is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` one universe up: the
two comparisons of the small and spaces-étale direct images, Stacks 03G2, part (3) and part (4),
agree after whiskering with the comparison equivalence of Stacks 03G1, and that equivalence
reflects the identification. -/
def smallToposMorphismPushforwardRepresentable (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
    (smallToposMorphism B S hS f).pushforward ≅
      (smallBaseChange B S hS f hr).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  ((Functor.whiskeringLeft _ _ _).obj
    ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))).preimageIso
    (smallToposMorphism_comparison B S hS f ≪≫
      (smallBaseChangePushforwardComparison B S hS f hr (Type (u + 1))).symm)

/-! ### The open complement of the image of an integral morphism -/

section Complement

variable (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)

/-- The open complement `X ∖ f(|Y|)` of the image of an integral morphism `f : Y ⟶ X` of
algebraic spaces over `S`, as a subfunctor of `X`. -/
def integralComplementSubfunctor : Subfunctor X.1 :=
  openSubspaceOfPoints B S hS X.1 (Set.range (pointsMap B S hS Y.1 f.hom))ᶜ

include hf in
/-- The complement of the image of an integral morphism is an open subspace: the image is closed
by Stacks 0415 and Stacks 0CZG, so its complement is open, and part (1) of Stacks 03BZ turns an
open set of points into an open subspace. -/
theorem isOpenSubspace_integralComplementSubfunctor :
    IsOpenSubspace B S hS (integralComplementSubfunctor B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS X.property _
    (isClosed_range_pointsMap_of_isIntegralHom B S hS f hf).isOpen_compl

/-- The open complement `X ∖ f(|Y|)` of the image of an integral morphism, as an algebraic space
over `S`. -/
def integralComplement : AlgebraicSpaces B S hS :=
  ⟨(integralComplementSubfunctor B S hS f).toFunctor,
    (isOpenSubspace_integralComplementSubfunctor B S hS f hf).1⟩

/-- The open immersion of the complement of the image of an integral morphism into the ambient
algebraic space. -/
def integralComplementHom : integralComplement B S hS f hf ⟶ X :=
  ObjectProperty.homMk (integralComplementSubfunctor B S hS f).ι

/-- The inclusion of the complement of the image of an integral morphism is an open
immersion. -/
theorem isOpenImmersion_integralComplementHom :
    IsOpenImmersion B S hS (integralComplementHom B S hS f hf).hom :=
  (isOpenSubspace_integralComplementSubfunctor B S hS f hf).2

/-- The inclusion of the complement of the image of an integral morphism is étale, an open
immersion being étale. -/
theorem isEtale_integralComplementHom :
    IsEtale B S hS (integralComplementHom B S hS f hf).hom :=
  isEtale_of_isOpenImmersion B S hS (isOpenImmersion_integralComplementHom B S hS f hf)

/-- The point set of the complement of the image of an integral morphism is the complement of
that image, by part (1) of Stacks 03BZ. -/
theorem range_pointsMap_integralComplementHom :
    Set.range (pointsMap B S hS (integralComplement B S hS f hf).1
        (integralComplementHom B S hS f hf).hom) =
      (Set.range (pointsMap B S hS Y.1 f.hom))ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

end Complement

/-! ### Set-valued geometric stalks are conservative -/

/-- **The set-valued geometric stalks are conservative.** A morphism of sheaves of sets on the
small étale site of an algebraic space which is bijective on the stalk at every geometric point
is an isomorphism, in every coefficient universe. -/
theorem isIso_of_bijective_stalkSetMap {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {P Q : Sheaf (SmallEtale.topology B S hS F) (Type w)} (φ : P ⟶ Q)
    (h : ∀ x : GeometricPoint B S hS F, Function.Bijective (stalkSetMap x φ.hom)) :
    IsIso φ := by
  have hinj : ∀ U : SmallEtale B S hS F, Function.Injective (φ.hom.app (op U)) :=
    (injective_iff_stalkSetMap_injective B S hS F hF φ).2 fun x ↦ (h x).1
  have hli : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_injective _ φ.hom fun U ↦ hinj U.unop
  have hls : Sheaf.IsLocallySurjective φ :=
    (surjective_iff_stalkSetMap_surjective B S hS F hF φ).2 fun x ↦ (h x).2
  exact (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hli, hls⟩

/-! ### The direct image is the singleton sheaf off the image -/

/-- A sheaf with a terminal set of sections over every object of the site is terminal. -/
def isTerminal_of_forall_isTerminal_obj {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (F : Sheaf J (Type w))
    (h : ∀ U : Cᵒᵖ, IsTerminal (F.obj.obj U)) : IsTerminal F :=
  IsTerminal.ofUniqueHom
    (fun G ↦ ⟨{ app := fun U ↦ (h U).from _
                naturality := fun _ _ _ ↦ (h _).hom_ext _ _ }⟩)
    (fun G m ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ (h U).hom_ext _ _)))

/-- An étale chart of the complement of the image of an integral morphism, read as a chart of
the ambient space, has empty preimage of that image: its points lie in the complement. -/
theorem chartPreimage_smallEtalePostcomp_integralComplement (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom)
    (W : SmallEtale B S hS (integralComplement B S hS f hf).1) :
    chartPreimage B S hS f ((smallEtalePostcomp B S hS (integralComplementHom B S hS f hf)
      (isEtale_integralComplementHom B S hS f hf)).obj W) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  have hcomp : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS
        (integralComplement B S hS f hf).1).obj W))
      (((smallEtalePostcomp B S hS (integralComplementHom B S hS f hf)
        (isEtale_integralComplementHom B S hS f hf)).obj W).obj.hom) y =
      pointsMap B S hS (integralComplement B S hS f hf).1
        (integralComplementHom B S hS f hf).hom
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS
          (integralComplement B S hS f hf).1).obj W)) W.obj.hom y) := by
    rw [smallEtalePostcomp_obj_hom, pointsMap_comp]
    rfl
  have hmem : pointsMap B S hS (integralComplement B S hS f hf).1
        (integralComplementHom B S hS f hf).hom
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS
          (integralComplement B S hS f hf).1).obj W)) W.obj.hom y) ∈
      Set.range (pointsMap B S hS (integralComplement B S hS f hf).1
        (integralComplementHom B S hS f hf).hom) := Set.mem_range_self _
  rw [range_pointsMap_integralComplementHom B S hS f hf] at hmem
  exact hmem (hcomp ▸ hy)

/-- **Étale Cohomology 04FX for sheaves of sets.** The restriction to the complement of the
image of an integral morphism `f : Y ⟶ X` of the small étale direct image along `f` is the
singleton sheaf.

By Stacks 03LP the restriction along the open immersion of the complement is computed on
sections by composing charts, and by Stacks 03G8 the direct image is restriction along chart
base change, so a section over a chart `W` of the complement is a section of the original sheaf
over the base change along `f` of the chart `W` of `X`. That base change has empty underlying
scheme, because the points of `W` avoid the image of `f`, and a sheaf has exactly one section
over a chart covered by the empty sieve. -/
def isTerminal_inverseImage_pushforward_integralComplement (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :
    IsTerminal ((smallToposMorphism B S hS
        (integralComplementHom B S hS f hf)).inverseImage.obj
      ((smallToposMorphism B S hS f).pushforward.obj G)) := by
  let hr := relativelyRepresentable_of_isIntegralHom B S hS f hf
  letI := (smallBaseChange_isMorphismOfSites B S hS f hr).toIsContinuous
  refine isTerminal_of_forall_isTerminal_obj _ fun U ↦ ?_
  obtain ⟨W⟩ := U
  refine IsTerminal.ofIso ?_ (smallToposMorphism_inverseImage_obj_obj B S hS
    (integralComplementHom B S hS f hf) (isEtale_integralComplementHom B S hS f hf)
    ((smallToposMorphism B S hS f).pushforward.obj G) W).symm
  refine IsTerminal.ofIso ?_
    (((evaluation (SmallEtale B S hS X.1)ᵒᵖ (Type (u + 1))).obj
      (op ((smallEtalePostcomp B S hS (integralComplementHom B S hS f hf)
        (isEtale_integralComplementHom B S hS f hf)).obj W))).mapIso
      ((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))).mapIso
        ((smallToposMorphismPushforwardRepresentable B S hS f hr).app G))).symm
  exact G.isTerminalOfBotCover _ (SmallEtale.bot_mem_topology B S hS Y.1 _
    (isEmpty_smallBaseChange_of_disjoint_range B S hS f hr _
      (chartPreimage_smallEtalePostcomp_integralComplement B S hS f hf W)))

/-- The stalk of a map of sheaves of sets at the image of a geometric point is bijective once
the map becomes invertible under inverse image. -/
private theorem bijective_stalkSetMap_geometricPointMap_of_isIso_inverseImage
    {Z : AlgebraicSpaces B S hS} (g : Z ⟶ X)
    {P Q : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (φ : P ⟶ Q)
    (h : IsIso ((smallToposMorphism B S hS g).inverseImage.map φ))
    (z : GeometricPoint B S hS Z.1) :
    Function.Bijective (stalkSetMap (geometricPointMap g.hom z) φ.hom) := by
  have : IsIso (((smallToposMorphism B S hS g).inverseImage ⋙
      sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) ⋙
        stalkSetFunctor z).map φ) :=
    inferInstanceAs (IsIso ((stalkSetFunctor z).map
      ((smallToposMorphism B S hS g).inverseImage.map φ).hom))
  exact (isIso_iff_bijective _).1
    (isIso_map_of_natIso (smallEtaleInverseImageStalkIso B S hS g z) φ)

/-- **A map of sheaves of sets invertible on the image of an integral morphism and on the
complement of that image is invertible.** Every geometric point of `X` lies either on `f(|Y|)`,
where it comes from a geometric point of `Y`, or on the open complement, where it comes from a
geometric point of that subspace; in either case the stalk of the map at the point is the stalk
of one of the two restrictions, which are invertible by hypothesis. -/
theorem isIso_of_inverseImage_isIso_of_integralComplement (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom)
    {P Q : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (φ : P ⟶ Q)
    (h1 : IsIso ((smallToposMorphism B S hS f).inverseImage.map φ))
    (h2 : IsIso ((smallToposMorphism B S hS
      (integralComplementHom B S hS f hf)).inverseImage.map φ)) :
    IsIso φ := by
  refine isIso_of_bijective_stalkSetMap B S hS X.property φ fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Y.1 f.hom)
  · obtain ⟨y, rfl⟩ :=
      exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom B S hS f hf x hx
    exact bijective_stalkSetMap_geometricPointMap_of_isIso_inverseImage B S hS f φ h1 y
  · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion B S hS
      (integralComplementHom B S hS f hf) (isOpenImmersion_integralComplementHom B S hS f hf)
      x (by rwa [range_pointsMap_integralComplementHom B S hS f hf])
    exact bijective_stalkSetMap_geometricPointMap_of_isIso_inverseImage B S hS _ φ h2 z

/-! ### Stacks 0AEH, part (1), the essential image -/

/-- **Stacks 0AEH, part (1), full faithfulness, at the universe of the small étale site.** The
direct image of sheaves of sets of the morphism of small étale topoi of Stacks 03G2, part (3)
along an integral and universally injective morphism is fully faithful.

This is
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective` at
`Type (u + 1)`, read through Stacks 03G8; it carries no tag, part (1)'s full-faithfulness clause
being registered in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveSmallEtale.lean`. -/
def fullyFaithfulSmallToposMorphismPushforwardOfIntegralUniversallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom) :
    (smallToposMorphism B S hS f).pushforward.FullyFaithful :=
  Functor.FullyFaithful.ofIso
    (fullyFaithfulSmallEtaleRestrictionOfIntegralUniversallyInjective B S hS
      (Type (u + 1)) f hf hui)
    (smallToposMorphismPushforwardRepresentable B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).symm

/-- **Stacks 0AEH, part (1), the essential image.** For an integral and universally injective
morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`, a sheaf of sets on the small étale
site of `X` lies in the essential image of the direct image along `f` exactly when its
restriction to the open complement of the image of the point set of `Y` is the singleton sheaf.

One direction is Étale Cohomology 04FX for sheaves of sets,
`AlgebraicGeometry.Space.isTerminal_inverseImage_pushforward_integralComplement`. For the other,
the direct image is fully faithful, so membership of the essential image is invertibility of the
unit `F ⟶ f_*f^{-1}F`; the unit becomes invertible under `f^{-1}` by the triangle identity and
under restriction to the complement because both sides are then the singleton sheaf, and a map
of sheaves of sets invertible on both is invertible, every geometric point of `X` lying either
on the image of `f` or on its complement. -/
@[stacks 0AEH "part (1): the essential image, for an integral and universally injective \
morphism of algebraic spaces"]
theorem smallEtalePushforward_essImage_iff_of_integral_universallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).pushforward.essImage F ↔
      Nonempty (IsTerminal ((smallToposMorphism B S hS
        (integralComplementHom B S hS f hf)).inverseImage.obj F)) := by
  have hff := fullyFaithfulSmallToposMorphismPushforwardOfIntegralUniversallyInjective
    B S hS f hf hui
  have := hff.full
  have := hff.faithful
  set adj := (smallToposMorphism B S hS f).adj
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact ⟨(isTerminal_inverseImage_pushforward_integralComplement B S hS f hf G).ofIso
      ((smallToposMorphism B S hS
        (integralComplementHom B S hS f hf)).inverseImage.mapIso e)⟩
  · rintro ⟨hF⟩
    have htri : (smallToposMorphism B S hS f).inverseImage.map (adj.unit.app F) ≫
        adj.counit.app ((smallToposMorphism B S hS f).inverseImage.obj F) = 𝟙 _ :=
      adj.left_triangle_components F
    have hcomp : IsIso ((smallToposMorphism B S hS f).inverseImage.map (adj.unit.app F) ≫
        adj.counit.app ((smallToposMorphism B S hS f).inverseImage.obj F)) := by
      rw [htri]
      infer_instance
    have h1 : IsIso ((smallToposMorphism B S hS f).inverseImage.map (adj.unit.app F)) :=
      IsIso.of_isIso_comp_right _
        (adj.counit.app ((smallToposMorphism B S hS f).inverseImage.obj F))
    have h2 : IsIso ((smallToposMorphism B S hS
        (integralComplementHom B S hS f hf)).inverseImage.map (adj.unit.app F)) :=
      isIso_of_isTerminal hF
        (isTerminal_inverseImage_pushforward_integralComplement B S hS f hf _) _
    have : IsIso (adj.unit.app F) :=
      isIso_of_inverseImage_isIso_of_integralComplement B S hS f hf (adj.unit.app F) h1 h2
    exact adj.mem_essImage_of_unit_isIso F

end AlgebraicGeometry.Space

end
