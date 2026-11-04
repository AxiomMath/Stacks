module

public import Mathlib.CategoryTheory.EssentialImage
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor

/-!
# The essential image of a 1-morphism of categories fibred in groupoids

Let `i : 𝒵 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over a category `𝒞`. The
essential image of the underlying functor of `i` is closed under isomorphism, and — because a
1-morphism of categories fibred in groupoids carries strongly cartesian morphisms to strongly
cartesian morphisms — it is closed under strongly cartesian pullbacks as well. The full
subcategory it cuts out is therefore again a category fibred in groupoids over `𝒞`, and when the
underlying functor of `i` is full and faithful the induced 1-morphism onto that full subcategory
is an equivalence over `𝒞`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.fullSubcategoryBased`: the full subcategory of a category
  fibred in groupoids cut out by a property of its objects, as a category over `𝒞`.
* `CategoryTheory.CatFiberedInGroupoids.essImageFibered`: the full subcategory cut out by the
  essential image, as a category fibred in groupoids over `𝒞`.
* `CategoryTheory.CatFiberedInGroupoids.fullSubcategoryBasedι`: the inclusion of a full
  subcategory, as a 1-morphism over `𝒞`.
* `CategoryTheory.CatFiberedInGroupoids.toEssImageBased`: the induced 1-morphism onto the full
  subcategory cut out by the essential image.
* `CategoryTheory.CatFiberedInGroupoids.fullyFaithful_lift_essImage`: a full and faithful
  1-morphism factoring through that essential image, read as a full and faithful 1-morphism onto
  the full subcategory.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.closedUnderStronglyCartesian_essImage`: the essential
  image is closed under strongly cartesian pullbacks.
* `CategoryTheory.CatFiberedInGroupoids.isFiberedInGroupoids_essImage`: the full subcategory it
  cuts out is fibred in groupoids.
* `CategoryTheory.CatFiberedInGroupoids.isEquivalence_toEssImageBased`: for `i` full and
  faithful, the induced 1-morphism onto that full subcategory is an equivalence of categories.
* `CategoryTheory.CatFiberedInGroupoids.toEssImageBased_comp_ι`: the induced 1-morphism followed
  by the inclusion is `i` itself, on the nose.
* `CategoryTheory.CatFiberedInGroupoids.exists_inverse_toEssImageBased`: for `i` full and
  faithful, that 1-morphism is an equivalence in the 2-category of categories fibred in groupoids
  over `𝒞` — a quasi-inverse strictly over `𝒞`, with unit and counit over identities. This is
  **Stacks 003Z** at the equivalence of categories above.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
-/

@[expose] public section

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
  {𝒵 𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- The full subcategory of a category fibred in groupoids over `𝒞` cut out by a property of its
objects, as a category over `𝒞`: its structure functor is the structure functor of the ambient
category restricted along the inclusion. -/
abbrev fullSubcategoryBased (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞)
    (P : ObjectProperty 𝒳.val.obj) : BasedCategory.{v₂, u₂} 𝒞 :=
  BasedCategory.ofFunctor (P.ι ⋙ 𝒳.val.p)

/-- The inclusion of the full subcategory cut out by a property of the objects, as a 1-morphism
over `𝒞`. -/
@[implicit_reducible]
def fullSubcategoryBasedι (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞)
    (P : ObjectProperty 𝒳.val.obj) : fullSubcategoryBased 𝒳 P ⥤ᵇ 𝒳.val where
  toFunctor := P.ι
  w := rfl

/-- **The essential image of a 1-morphism of categories fibred in groupoids is closed under
strongly cartesian pullbacks**, i.e. satisfies condition (1) of Stacks 04TU. -/
theorem closedUnderStronglyCartesian_essImage (i : 𝒵 ⟶ 𝒳) :
    Functor.ClosedUnderStronglyCartesian 𝒳.val.p (homFunctor i).essImage := by
  set p := 𝒳.val.p
  set pZ := 𝒵.val.p
  set F := homFunctor i
  apply (Functor.closedUnderStronglyCartesian_iff_upToIso p F.essImage).2
  intro V U y x f φ hφ hx
  have : p.IsHomLift f φ := hφ.toIsHomLift
  have hxU : p.obj x = U := IsHomLift.codomain_eq p f φ
  rcases hx with ⟨z, ⟨e⟩⟩
  have hFz : p.obj (F.obj z) = pZ.obj z := BasedFunctor.w_obj i.hom z
  let c : pZ.obj z ≅ U := eqToIso hFz.symm ≪≫ p.mapIso e ≪≫ eqToIso hxU
  obtain ⟨zU, hzU, eU, heU⟩ := 𝒵.property.exists_iso_lift c
  let e0 : F.obj zU ≅ x := (F.mapIso eU).symm ≪≫ e
  have hE : p.IsHomLift c.hom e.hom := by
    apply IsHomLift.of_fac' p c.hom e.hom hFz hxU
    simp [c]
  have : p.IsHomLift c.hom (F.mapIso eU).hom := by
    simpa using BasedFunctor.preserves_isHomLift i.hom c.hom eU.hom
  have : p.IsHomLift c.inv (F.mapIso eU).inv := IsHomLift.inv_lift_inv p c (F.mapIso eU)
  have : p.IsHomLift (𝟙 U) e0.hom := by
    simpa [e0] using (IsHomLift.comp p c.inv c.hom (F.mapIso eU).inv e.hom)
  obtain ⟨zV, ψ, hψ⟩ := 𝒵.property.exists_lift f zU hzU
  have : p.IsStronglyCartesian f (F.map ψ) := CatFiberedInGroupoids.isStronglyCartesian_map i f ψ
  have : p.IsStronglyCartesian (𝟙 U) e0.hom :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift 𝒳.property (𝟙 U) e0.hom
  have : p.IsStronglyCartesian f (F.map ψ ≫ e0.hom) := by
    simpa using (show p.IsStronglyCartesian (f ≫ 𝟙 U) (F.map ψ ≫ e0.hom) from inferInstance)
  exact ⟨F.obj zV, ⟨zV, ⟨Iso.refl _⟩⟩,
    ⟨(Functor.IsCartesian.domainUniqueUpToIso p f φ (F.map ψ ≫ e0.hom)).symm⟩⟩

/-- **The full subcategory cut out by the essential image of a 1-morphism of categories fibred in
groupoids is fibred in groupoids.** -/
theorem isFiberedInGroupoids_essImage (i : 𝒵 ⟶ 𝒳) :
    ((homFunctor i).essImage.ι ⋙ 𝒳.val.p).IsFiberedInGroupoids := by
  set p := 𝒳.val.p
  set P := (homFunctor i).essImage
  have : p.IsFibered := 𝒳.property.isFibered
  refine Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr
    ⟨Functor.isFibered_restrict_of_closed p P (closedUnderStronglyCartesian_essImage i),
      fun U ↦ ⟨fun f ↦ ?_⟩⟩
  let L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι rfl U
  have : L.Full := Functor.Fiber.full_mapOfComp rfl U
  have : L.Faithful := Functor.Fiber.faithful_mapOfComp rfl U
  have : IsIso (L.map f) := (𝒳.property.fiber_isGroupoid U).all_isIso (L.map f)
  exact isIso_of_fully_faithful L f

/-- The full subcategory cut out by the essential image of a 1-morphism of categories fibred in
groupoids, as an object of the 2-category of categories fibred in groupoids over `𝒞`. -/
abbrev essImageFibered (i : 𝒵 ⟶ 𝒳) : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 (homFunctor i).essImage)
    (isFiberedInGroupoids_essImage i)

/-- The 1-morphism over `𝒞` from the source of a 1-morphism of categories fibred in groupoids
onto the full subcategory of its target cut out by its essential image: on objects it tags the
image with the proof that it lies in the essential image. -/
def toEssImageBased (i : 𝒵 ⟶ 𝒳) : 𝒵.val ⥤ᵇ fullSubcategoryBased 𝒳 (homFunctor i).essImage where
  toFunctor := (homFunctor i).toEssImage
  w := i.hom.w

/-- The 1-morphism onto the full subcategory cut out by the essential image, followed by the
inclusion of that full subcategory, is the original 1-morphism on the nose. -/
theorem toEssImageBased_comp_ι (i : 𝒵 ⟶ 𝒳) :
    (toEssImageBased i).comp (fullSubcategoryBasedι 𝒳 (homFunctor i).essImage) = i.hom := rfl

/-- For a full and faithful 1-morphism of categories fibred in groupoids, the 1-morphism onto the
full subcategory cut out by the essential image has underlying functor an equivalence of
categories. -/
theorem isEquivalence_toEssImageBased (i : 𝒵 ⟶ 𝒳) (hfull : (homFunctor i).Full)
    (hfaithful : (homFunctor i).Faithful) :
    Functor.IsEquivalence (toEssImageBased i).toFunctor := by
  change Functor.IsEquivalence (homFunctor i).toEssImage
  have := hfull
  have := hfaithful
  exact Functor.IsEquivalence.mk

/-- The inclusion of the full subcategory cut out by the essential image is full. -/
theorem full_essImage_ι (i : 𝒵 ⟶ 𝒳) : ((homFunctor i).essImage).ι.Full :=
  ObjectProperty.full_ι _

/-- The inclusion of the full subcategory cut out by the essential image is faithful. -/
theorem faithful_essImage_ι (i : 𝒵 ⟶ 𝒳) : ((homFunctor i).essImage).ι.Faithful :=
  ObjectProperty.faithful_ι _

/-- **A fully faithful 1-morphism factoring through the essential image of `i` is fully faithful
onto the full subcategory that essential image cuts out.** -/
def fullyFaithful_lift_essImage (i : 𝒵 ⟶ 𝒳) {𝒟 : BasedCategory.{v₂, u₂} 𝒞}
    (F : 𝒟 ⥤ᵇ 𝒳.val) (hF : ∀ d, (homFunctor i).essImage (F.obj d))
    (hFff : F.toFunctor.FullyFaithful) :
    (((homFunctor i).essImage).lift F.toFunctor hF).FullyFaithful :=
  haveI := faithful_essImage_ι i
  (show ((((homFunctor i).essImage).lift F.toFunctor hF) ⋙
    ((homFunctor i).essImage).ι).FullyFaithful from hFff).ofCompFaithful

/-- **The quasi-inverse over `𝒞` of the comparison with the essential image.** For a full and
faithful 1-morphism `i : 𝒵 ⟶ 𝒳` of categories fibred in groupoids over `𝒞`, the 1-morphism of
`CategoryTheory.CatFiberedInGroupoids.toEssImageBased` is an equivalence in the 2-category of
categories fibred in groupoids over `𝒞`: there is a 1-morphism back, strictly over `𝒞`, with
unit and counit lying over identities.

This is **Stacks 003Z** at the equivalence of categories of
`CategoryTheory.CatFiberedInGroupoids.isEquivalence_toEssImageBased`. -/
theorem exists_inverse_toEssImageBased (i : 𝒵 ⟶ 𝒳) (hfull : (homFunctor i).Full)
    (hfaithful : (homFunctor i).Faithful) :
    ∃ (K : fullSubcategoryBased 𝒳 (homFunctor i).essImage ⥤ᵇ 𝒵.val)
      (η : (toEssImageBased i).toFunctor ⋙ K.toFunctor ≅ 𝟭 𝒵.val.obj)
      (ε : K.toFunctor ⋙ (toEssImageBased i).toFunctor ≅
        𝟭 (fullSubcategoryBased 𝒳 (homFunctor i).essImage).obj),
      (∀ x : 𝒵.val.obj, 𝒵.val.p.IsHomLift (𝟙 (𝒵.val.p.obj x)) (η.hom.app x)) ∧
      (∀ x : (fullSubcategoryBased 𝒳 (homFunctor i).essImage).obj,
        (fullSubcategoryBased 𝒳 (homFunctor i).essImage).p.IsHomLift
          (𝟙 ((fullSubcategoryBased 𝒳 (homFunctor i).essImage).p.obj x)) (ε.hom.app x)) := by
  obtain ⟨K, hK, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.p
    ((homFunctor i).essImage.ι ⋙ 𝒳.val.p) 𝒵.property (isFiberedInGroupoids_essImage i)
    (toEssImageBased i).toFunctor (toEssImageBased i).w
    (isEquivalence_toEssImageBased i hfull hfaithful)
  exact ⟨⟨K, hK⟩, η, ε, hη, hε⟩

end CategoryTheory.CatFiberedInGroupoids

end
