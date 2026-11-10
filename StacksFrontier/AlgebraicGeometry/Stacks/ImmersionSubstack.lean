module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.EssentialImage
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor

/-!
# The substack cut out by an immersion of algebraic stacks (Stacks 0506)

Let `i : 𝒵 ⟶ 𝒳` be an immersion of algebraic stacks over `S`. **Stacks 0506** says that there is
a unique locally closed substack `𝒳' ⊆ 𝒳` through which `i` factors as an equivalence `𝒵 ⟶ 𝒳'`
followed by the inclusion `𝒳' ⟶ 𝒳`, and that `𝒳'` is a closed, respectively open, substack as
soon as `i` is a closed, respectively open, immersion.

That substack is the *essential image* of the functor underlying `i`. An immersion is a
monomorphism, hence fully faithful, so `𝒵` is equivalent to the full subcategory of `𝒳` on the
essential image; the essential image is closed under isomorphism and under strongly cartesian
pullbacks, which makes that full subcategory a category fibred in groupoids over the big fppf
site of `S`, and an algebraic stack because `𝒵` is one. The inclusion of the substack is then the
immersion `i` read across that equivalence, so it is itself an immersion of the same kind.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBased`: the 1-morphism over the big fppf
  site of `S` from the source of a 1-morphism of algebraic stacks onto the full subcategory of
  its target cut out by its essential image.
* `AlgebraicGeometry.Stack.AlgebraicStacks.essImageFibered`: that full subcategory, as a category
  fibred in groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.essImageEquivalence`: the 1-morphism onto it, as an
  equivalence over the site, for an immersion.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyClosedSubstack_essImage`: the essential
  image of an immersion is a locally closed substack of its target, **Stacks 0506**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isEquivalence_to_essImage`: the immersion
  factors as an equivalence onto that substack followed by the inclusion, **Stacks 0506**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_essImage_of_isEquivalence_factorization`: any
  strictly full algebraic substack through which the immersion factors by an equivalence is cut
  out by the essential image, **Stacks 0506**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.existsUnique_locallyClosedSubstack_of_isImmersion`:
  the three previous results assembled into the uniqueness statement of **Stacks 0506**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedSubstack_essImage` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.exists_openSubstack_essImage`: the closed and the open
  case of **Stacks 0506**.

## Implementation notes

A substack is a property of the objects of `𝒳` in the sense of
`StacksFrontier.AlgebraicGeometry.Stacks.Substack`, so "unique substack" is uniqueness of that
object property, and the factorization holds only up to a 2-isomorphism, as is appropriate in a
2-category. The statement therefore reads: there is exactly one object property `P` such that `P`
cuts out a locally closed substack and `i` factors through the inclusion of the full subcategory
on `P` by a 1-morphism whose underlying functor is an equivalence of categories.

Full faithfulness of the functor underlying `i` is
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps` (**Stacks 05UK**,
the implication (1) ⟹ (2) of **Stacks 04ZZ**) at the monomorphism hypothesis supplied by
`AlgebraicGeometry.Space.mono_of_isImmersion` (**Stacks 042R**). Composing those two is **Stacks
0504**, that an immersion is a monomorphism, which is used only through this consequence and so
is recreated here from its two inputs.

The immersion condition is transported from `i` to the inclusion of the substack by
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm` (**Stacks 0457**), which is
stated for the written-out quantifier of Stacks 04XB rather than for
`AlgebraicGeometry.Stack.HasRelativeProperty`; that matters, because the latter carries locality
of the property at the target for the fppf precoverage, which for immersions is Stacks 042U, a
result this library does not have. The three immersion predicates of Stacks 04YL are written out
in the same form, so the transport applies to them directly. The 2-commutative square it is
applied to has `AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBased` along the top and the
identity of `𝒳` along the bottom, and its 2-commutativity is
`CategoryTheory.Functor.toEssImageCompι`, whose components are identities and so are vertical;
this is why the quasi-inverse of that equivalence is not needed for the transport, only for the
algebraic-stack condition.

Fibredness in groupoids of the full subcategory on the essential image is
`CategoryTheory.Functor.isFibered_restrict_of_closed` (condition (1) of Stacks 04TU) together
with the observation that the fibres of the restriction embed fully faithfully in the fibres of
`𝒳` by `CategoryTheory.Functor.Fiber.full_mapOfComp` and
`CategoryTheory.Functor.Fiber.faithful_mapOfComp`, and that a fully faithful functor reflects
isomorphisms. The algebraic-stack condition then comes from `𝒵` across the equivalence over the
site, by `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence` (**Stacks 03YQ**); the
quasi-inverse over the site is **Stacks 003Z**,
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **An immersion of algebraic stacks is fully faithful.** An immersion is a monomorphism by
**Stacks 0504**, because an immersion of algebraic spaces is one (**Stacks 042R**,
`AlgebraicGeometry.Space.mono_of_isImmersion`), and a monomorphism is fully faithful by the
implication (1) ⟹ (2) of **Stacks 04ZZ**
(`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`). -/
theorem full_and_faithful_homFunctor_of_isImmersion (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i) :
    (CatFiberedInGroupoids.homFunctor i.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor i.hom).Faithful :=
  Stack.full_and_faithful_homFunctor_of_mono_representingMaps B S hS i.hom hi.1
    fun U y hy F hF he => Space.mono_of_isImmersion B S hS (hi.2 U y hy F hF he)

/-- The essential image of a 1-morphism of algebraic stacks is closed under strongly cartesian
pullbacks, i.e. satisfies condition (1) of Stacks 04TU.

A strongly cartesian lift `φ` of `f` at an object `x` isomorphic to `i(z)` is matched by a
strongly cartesian lift of `f` in `𝒵` at an object of `𝒵` lying over the base of `x` on the nose,
whose image is therefore a second strongly cartesian lift of `f` at `x`; the two have isomorphic
domains by the uniqueness of cartesian lifts. -/
theorem closedUnderStronglyCartesian_essImage (i : 𝒵 ⟶ 𝒳) :
    Functor.ClosedUnderStronglyCartesian 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor i.hom).essImage := by
  set p := 𝒳.val.val.p
  set pZ := 𝒵.val.val.p
  set F := CatFiberedInGroupoids.homFunctor i.hom
  apply (Functor.closedUnderStronglyCartesian_iff_upToIso p F.essImage).2
  intro V U y x f φ hφ hx
  have : p.IsHomLift f φ := hφ.toIsHomLift
  have hxU : p.obj x = U := IsHomLift.codomain_eq p f φ
  rcases hx with ⟨z, ⟨e⟩⟩
  have hFz : p.obj (F.obj z) = pZ.obj z := BasedFunctor.w_obj i.hom.hom z
  let c : pZ.obj z ≅ U := eqToIso hFz.symm ≪≫ p.mapIso e ≪≫ eqToIso hxU
  obtain ⟨zU, hzU, eU, heU⟩ := 𝒵.val.property.exists_iso_lift c
  let e0 : F.obj zU ≅ x := (F.mapIso eU).symm ≪≫ e
  have hE : p.IsHomLift c.hom e.hom := by
    apply IsHomLift.of_fac' p c.hom e.hom hFz hxU
    simp [c]
  have : p.IsHomLift c.hom (F.mapIso eU).hom := by
    simpa using BasedFunctor.preserves_isHomLift i.hom.hom c.hom eU.hom
  have hFEUinv : p.IsHomLift c.inv (F.mapIso eU).inv :=
    IsHomLift.inv_lift_inv p c (F.mapIso eU)
  have hE0 : p.IsHomLift (𝟙 U) e0.hom := by
    simpa [e0] using (IsHomLift.comp p c.inv c.hom (F.mapIso eU).inv e.hom)
  obtain ⟨zV, ψ, hψ⟩ := 𝒵.val.property.exists_lift f zU hzU
  have hFψSC : p.IsStronglyCartesian f (F.map ψ) :=
    CatFiberedInGroupoids.isStronglyCartesian_map i.hom f ψ
  have hE0SC : p.IsStronglyCartesian (𝟙 U) e0.hom :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒳.val.property (𝟙 U) e0.hom
  have hcompSC : p.IsStronglyCartesian f (F.map ψ ≫ e0.hom) := by
    simpa using (show p.IsStronglyCartesian (f ≫ 𝟙 U) (F.map ψ ≫ e0.hom) from inferInstance)
  have : p.IsStronglyCartesian f φ := hφ
  exact ⟨F.obj zV, ⟨zV, ⟨Iso.refl _⟩⟩,
    ⟨(Functor.IsCartesian.domainUniqueUpToIso p f φ (F.map ψ ≫ e0.hom)).symm⟩⟩

/-- The full subcategory of an algebraic stack cut out by the essential image of a 1-morphism of
algebraic stacks is fibred in groupoids over the big fppf site of `S`.

It is fibred by `CategoryTheory.Functor.isFibered_restrict_of_closed`, and its fibres are
groupoids because they embed fully faithfully into the fibres of `𝒳`, which are groupoids, and a
fully faithful functor reflects isomorphisms. -/
theorem isFiberedInGroupoids_essImage (i : 𝒵 ⟶ 𝒳) :
    ((CatFiberedInGroupoids.homFunctor i.hom).essImage.ι ⋙
      𝒳.val.val.p).IsFiberedInGroupoids := by
  set p := 𝒳.val.val.p
  set P := (CatFiberedInGroupoids.homFunctor i.hom).essImage
  have : p.IsFibered := 𝒳.val.property.isFibered
  have hFib : (P.ι ⋙ p).IsFibered :=
    Functor.isFibered_restrict_of_closed p P (closedUnderStronglyCartesian_essImage i)
  have hGroups : ∀ U : BigFppfOver B S hS, IsGroupoid ((P.ι ⋙ p).Fiber U) := by
    intro U
    have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
    set L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl U
    have : P.ι.Full := ObjectProperty.full_ι P
    have : P.ι.Faithful := ObjectProperty.faithful_ι P
    have : L.Full := Functor.Fiber.full_mapOfComp hrfl U
    have : L.Faithful := Functor.Fiber.faithful_mapOfComp hrfl U
    have hAmbient : IsGroupoid (p.Fiber U) := 𝒳.val.property.fiber_isGroupoid U
    refine { all_isIso := ?_ }
    intro a b f
    have : IsIso (L.map f) := hAmbient.all_isIso (L.map f)
    exact isIso_of_fully_faithful L f
  exact Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr ⟨hFib, hGroups⟩

/-- The full subcategory of an algebraic stack cut out by the essential image of a 1-morphism of
algebraic stacks, as a category fibred in groupoids over the big fppf site of `S`. -/
abbrev essImageFibered (i : 𝒵 ⟶ 𝒳) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)
    (isFiberedInGroupoids_essImage i)

/-- The 1-morphism over the big fppf site of `S` from the source of a 1-morphism of algebraic
stacks onto the full subcategory of its target cut out by its essential image: on objects it tags
the image with the proof that it lies in the essential image. -/
def toEssImageBased (i : 𝒵 ⟶ 𝒳) :
    𝒵.val.val ⥤ᵇ
      fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage where
  toFunctor := (CatFiberedInGroupoids.homFunctor i.hom).toEssImage
  w := i.hom.hom.w

/-- For an immersion, the 1-morphism onto the full subcategory cut out by the essential image has
underlying functor an equivalence of categories: it is full and faithful because the immersion is,
and essentially surjective by construction. -/
theorem isEquivalence_toEssImageBased (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i) :
    Functor.IsEquivalence (toEssImageBased i).toFunctor := by
  change Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor i.hom).toEssImage
  obtain ⟨hfull, hfaithful⟩ := full_and_faithful_homFunctor_of_isImmersion i hi
  have : (CatFiberedInGroupoids.homFunctor i.hom).Full := hfull
  have : (CatFiberedInGroupoids.homFunctor i.hom).Faithful := hfaithful
  exact Functor.IsEquivalence.mk

/-- The identity of `𝒳`, read as a 1-morphism over the big fppf site of `S`, has underlying
functor an equivalence of categories. -/
theorem isEquivalence_basedFunctorId :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor := by
  change Functor.IsEquivalence (𝟭 𝒳.val.val.obj)
  infer_instance

/-- The 2-commutativity of the square whose top edge is the 1-morphism onto the full subcategory
cut out by the essential image, whose bottom edge is the identity of `𝒳`, whose left edge is the
given 1-morphism and whose right edge is the inclusion of that full subcategory.

It is `CategoryTheory.Functor.toEssImageCompι`, whose components are identities and therefore lie
over identities of the site. -/
def toEssImageBasedSquareIso (i : 𝒵 ⟶ 𝒳) :
    BasedFunctor.comp (toEssImageBased i)
        (fullSubcategoryBasedInclusion 𝒳
          (CatFiberedInGroupoids.homFunctor i.hom).essImage) ≅
      BasedFunctor.comp i.hom.hom (BasedFunctor.id 𝒳.val.val) := by
  refine BasedNatIso.mkNatIso
    (Functor.toEssImageCompι (CatFiberedInGroupoids.homFunctor i.hom)) ?_
  intro x
  change 𝒳.val.val.p.IsHomLift (𝟙 (𝒵.val.val.p.obj x))
    ((Functor.toEssImageCompι (CatFiberedInGroupoids.homFunctor i.hom)).hom.app x)
  rw [Functor.toEssImageCompι_hom_app]
  exact IsHomLift.id (BasedFunctor.w_obj i.hom.hom x)

/-- The equivalence over the big fppf site of `S` between the source of an immersion and the full
subcategory of its target cut out by its essential image.

The forward 1-morphism is `AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBased`, whose
underlying functor is an equivalence of categories; a quasi-inverse *over the site*, with vertical
unit and counit, is then supplied by **Stacks 003Z**,
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`. -/
noncomputable def essImageEquivalence (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i) :
    BasedCategory.Equivalence 𝒵.val.val
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage) :=
  let h0 := Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.val.p
    ((CatFiberedInGroupoids.homFunctor i.hom).essImage.ι ⋙ 𝒳.val.val.p) 𝒵.val.property
    (isFiberedInGroupoids_essImage i) (toEssImageBased i).toFunctor (toEssImageBased i).w
    (isEquivalence_toEssImageBased i hi)
  let h1 := Classical.choose_spec h0
  let h2 := Classical.choose_spec h1
  let h3 := Classical.choose_spec h2
  { functor := toEssImageBased i
    inverse := ⟨Classical.choose h0, Classical.choose h1⟩
    unitIso := BasedNatIso.mkNatIso (Classical.choose h2) (Classical.choose_spec h3).1
    counitIso := BasedNatIso.mkNatIso (Classical.choose h3) (Classical.choose_spec h3).2 }

/-- The full subcategory of `𝒳` cut out by the essential image of an immersion is an algebraic
stack: it is equivalent over the big fppf site of `S` to the source of the immersion, and being an
algebraic stack is invariant under such an equivalence (**Stacks 03YQ**). -/
theorem isAlgebraicStack_essImage (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i) :
    IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage) :=
  (isAlgebraicStack_iff_of_equivalence B S hS (essImageEquivalence i hi)).mp 𝒵.property

/-- The inclusion of the full subcategory cut out by the essential image of an immersion is
representable by algebraic spaces: the immersion is, by **Stacks 04YL**, and representability by
algebraic spaces is invariant under a square of equivalences (**Stacks 0457**). -/
theorem isRepresentableByAlgebraicSpaces_essImageInclusion (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i) :
    IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryBasedInclusion 𝒳
        (CatFiberedInGroupoids.homFunctor i.hom).essImage) :=
  have _h1 : Functor.IsEquivalence (toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased i hi
  have _h2 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    isEquivalence_basedFunctorId
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (𝒳' := 𝒵.val) (𝒳 := essImageFibered i) (𝒴' := 𝒳.val) (𝒴 := 𝒳.val) i.hom.hom
    (fullSubcategoryBasedInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)
    (toEssImageBased i) (BasedFunctor.id 𝒳.val.val) (toEssImageBasedSquareIso i)).mpr hi.1

/-- The inclusion of the full subcategory cut out by the essential image of an immersion of
algebraic stacks is an immersion: the Stacks 04XB condition transports from `i` across the square
of equivalences by **Stacks 0457**. -/
theorem isImmersion_essImageInclusion (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    IsImmersion B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) :=
  have _h1 : Functor.IsEquivalence (toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased i hi
  have _h2 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    isEquivalence_basedFunctorId
  ⟨isRepresentableByAlgebraicSpaces_essImageInclusion i hi,
    relativeProperty_of_equivalences_symm B S hS
      (𝒳' := 𝒵.val) (𝒳 := essImageFibered i) (𝒴' := 𝒳.val) (𝒴 := 𝒳.val)
      (Space.immersionProperty B S hS) i.hom.hom
      (fullSubcategoryBasedInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)
      (toEssImageBased i) (BasedFunctor.id 𝒳.val.val) (toEssImageBasedSquareIso i) hi.2⟩

/-- The inclusion of the full subcategory cut out by the essential image of a closed immersion of
algebraic stacks is a closed immersion, by the same transport. -/
theorem isClosedImmersion_essImageInclusion (i : 𝒵 ⟶ 𝒳) (hi : IsClosedImmersion B S hS i)
    (hiImm : IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    IsClosedImmersion B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) :=
  have _h1 : Functor.IsEquivalence (toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased i hiImm
  have _h2 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    isEquivalence_basedFunctorId
  ⟨isRepresentableByAlgebraicSpaces_essImageInclusion i hiImm,
    relativeProperty_of_equivalences_symm B S hS
      (𝒳' := 𝒵.val) (𝒳 := essImageFibered i) (𝒴' := 𝒳.val) (𝒴 := 𝒳.val)
      (Space.closedImmersionProperty B S hS) i.hom.hom
      (fullSubcategoryBasedInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)
      (toEssImageBased i) (BasedFunctor.id 𝒳.val.val) (toEssImageBasedSquareIso i) hi.2⟩

/-- The inclusion of the full subcategory cut out by the essential image of an open immersion of
algebraic stacks is an open immersion, by the same transport. -/
theorem isOpenImmersion_essImageInclusion (i : 𝒵 ⟶ 𝒳) (hi : IsOpenImmersion B S hS i)
    (hiImm : IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    IsOpenImmersion B S hS
      (fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) :=
  have _h1 : Functor.IsEquivalence (toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased i hiImm
  have _h2 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    isEquivalence_basedFunctorId
  ⟨isRepresentableByAlgebraicSpaces_essImageInclusion i hiImm,
    relativeProperty_of_equivalences_symm B S hS
      (𝒳' := 𝒵.val) (𝒳 := essImageFibered i) (𝒴' := 𝒳.val) (𝒴 := 𝒳.val)
      (Space.openImmersionProperty B S hS) i.hom.hom
      (fullSubcategoryBasedInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)
      (toEssImageBased i) (BasedFunctor.id 𝒳.val.val) (toEssImageBasedSquareIso i) hi.2⟩

/-- **Stacks 0506**, the image is a locally closed substack. The essential image of an immersion
of algebraic stacks over `S` cuts out a locally closed substack of its target.

It is closed under isomorphism because an essential image always is; its full subcategory is an
algebraic stack by Stacks 03YQ; and the inclusion of that full subcategory is an immersion because
the immersion `i` factors through it by an equivalence, so Stacks 0457 transports both
representability by algebraic spaces and the Stacks 04XB immersion condition. -/
@[stacks 0506 "the image is a locally closed substack"]
theorem isLocallyClosedSubstack_essImage (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i) :
    IsLocallyClosedSubstack 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage :=
  ⟨inferInstance, isAlgebraicStack_essImage i hi,
    isImmersion_essImageInclusion i hi (isAlgebraicStack_essImage i hi)⟩

/-- **Stacks 0506**, the factorization. An immersion of algebraic stacks over `S` factors as a
1-morphism onto the full subcategory cut out by its essential image whose underlying functor is an
equivalence of categories, followed by the inclusion of that full subcategory. -/
@[stacks 0506 "the factorization through the image"]
theorem exists_isEquivalence_to_essImage (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    ∃ f : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳
        (CatFiberedInGroupoids.homFunctor i.hom).essImage hP,
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor f.hom) ∧
        Nonempty (f ≫ fullSubcategoryInclusion 𝒳
          (CatFiberedInGroupoids.homFunctor i.hom).essImage hP ≅ i) :=
  ⟨Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (toEssImageBased i)),
    isEquivalence_toEssImageBased i hi,
    ⟨Bicategory.InducedBicategory.isoMk
      (Bicategory.InducedBicategory.isoMk (toEssImageBasedSquareIso i))⟩⟩

/-- **Stacks 0506**, uniqueness. A strictly full subcategory of an algebraic stack which is an
algebraic stack and through which an immersion factors by a 1-morphism whose underlying functor is
an equivalence of categories is cut out by the essential image of the immersion.

The essential image of the inclusion of a strictly full subcategory is the property cutting it
out, and precomposing with an essentially surjective functor does not change an essential image,
so the essential image of the immersion is that property. -/
@[stacks 0506 "uniqueness of the substack"]
theorem eq_essImage_of_isEquivalence_factorization (i : 𝒵 ⟶ 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj) (hstrict : P.IsClosedUnderIsomorphisms)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (f : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP)
    (hf : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor f.hom))
    (α : f ≫ fullSubcategoryInclusion 𝒳 P hP ≅ i) :
    P = (CatFiberedInGroupoids.homFunctor i.hom).essImage := by
  have hNat : (CatFiberedInGroupoids.homFunctor f.hom ⋙ P.ι) ≅
      CatFiberedInGroupoids.homFunctor i.hom := by
    refine ⟨α.hom.hom.hom.toNatTrans, α.inv.hom.hom.toNatTrans, ?_, ?_⟩
    · have hh : α.hom.hom.hom ≫ α.inv.hom.hom = 𝟙 _ :=
        congrArg (fun z => z.hom.hom) α.hom_inv_id
      change (α.hom.hom.hom ≫ α.inv.hom.hom).toNatTrans = _
      exact congrArg (fun z => BasedNatTrans.toNatTrans z) hh
    · have hh : α.inv.hom.hom ≫ α.hom.hom.hom = 𝟙 _ :=
        congrArg (fun z => z.hom.hom) α.inv_hom_id
      change (α.inv.hom.hom ≫ α.hom.hom.hom).toNatTrans = _
      exact congrArg (fun z => BasedNatTrans.toNatTrans z) hh
  calc P = P.ι.essImage := by
        ext x
        exact ⟨fun hx => ⟨⟨x, hx⟩, ⟨Iso.refl _⟩⟩, fun ⟨y, ⟨e⟩⟩ => P.prop_of_iso e y.property⟩
    _ = (CatFiberedInGroupoids.homFunctor f.hom ⋙ P.ι).essImage :=
        (Functor.essImage_comp_of_essSurj
          (F := CatFiberedInGroupoids.homFunctor f.hom) (G := P.ι)).symm
    _ = (CatFiberedInGroupoids.homFunctor i.hom).essImage :=
        Functor.essImage_eq_of_natIso hNat

/-- **Stacks 0506.** For an immersion `i : 𝒵 ⟶ 𝒳` of algebraic stacks over `S` there is a
*unique* locally closed substack of `𝒳` through which `i` factors as a 1-morphism whose underlying
functor is an equivalence of categories followed by the inclusion of the substack.

That substack is cut out by the essential image of the functor underlying `i`. -/
@[stacks 0506]
theorem existsUnique_locallyClosedSubstack_of_isImmersion (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i) :
    ∃! P : ObjectProperty 𝒳.val.val.obj,
      IsLocallyClosedSubstack 𝒳 P ∧
        ∃ (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
          (f : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP),
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor f.hom) ∧
            Nonempty (f ≫ fullSubcategoryInclusion 𝒳 P hP ≅ i) := by
  obtain ⟨f, hfe, hfα⟩ :=
    exists_isEquivalence_to_essImage i hi (isAlgebraicStack_essImage i hi)
  refine ⟨(CatFiberedInGroupoids.homFunctor i.hom).essImage,
    ⟨isLocallyClosedSubstack_essImage i hi, isAlgebraicStack_essImage i hi, f, hfe, hfα⟩, ?_⟩
  rintro P ⟨⟨hstrict, -⟩, hPalg, g, hge, ⟨β⟩⟩
  exact eq_essImage_of_isEquivalence_factorization i P hstrict hPalg g hge β

/-- **Stacks 0506**, the closed case. The essential image of a closed immersion of algebraic
stacks over `S` cuts out a closed substack of its target.

A closed immersion is an immersion, so the essential image cuts out a locally closed substack; the
closed-immersion condition on the inclusion is the condition on `i` transported across the
equivalence by Stacks 0457. -/
@[stacks 0506 "the image of a closed immersion is a closed substack"]
theorem isClosedSubstack_essImage (i : 𝒵 ⟶ 𝒳) (hi : IsClosedImmersion B S hS i) :
    IsClosedSubstack 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage :=
  have hiImm : IsImmersion B S hS i :=
    ⟨hi.1, fun U y hy F hF he =>
      Space.isImmersion_of_isClosedImmersion B S hS (hi.2 U y hy F hF he)⟩
  ⟨inferInstance, isAlgebraicStack_essImage i hiImm,
    isClosedImmersion_essImageInclusion i hi hiImm (isAlgebraicStack_essImage i hiImm)⟩

/-- **Stacks 0506**, the open case. The essential image of an open immersion of algebraic stacks
over `S` is the object property of an open substack of its target.

An open immersion is an immersion, so the essential image cuts out a locally closed substack; the
open-immersion condition on the inclusion is the condition on `i` transported across the
equivalence by Stacks 0457. -/
@[stacks 0506 "the image of an open immersion is an open substack"]
theorem exists_openSubstack_essImage (i : 𝒵 ⟶ 𝒳) (hi : IsOpenImmersion B S hS i) :
    ∃ U : OpenSubstack 𝒳,
      U.property = (CatFiberedInGroupoids.homFunctor i.hom).essImage :=
  have hiImm : IsImmersion B S hS i :=
    ⟨hi.1, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U y hy F hF he)⟩
  ⟨⟨(CatFiberedInGroupoids.homFunctor i.hom).essImage, inferInstance,
    isAlgebraicStack_essImage i hiImm,
    isOpenImmersion_essImageInclusion i hi hiImm (isAlgebraicStack_essImage i hiImm)⟩, rfl⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
