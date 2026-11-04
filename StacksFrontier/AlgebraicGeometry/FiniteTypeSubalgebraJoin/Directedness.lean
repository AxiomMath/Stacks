module

public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Subobject
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.Generated
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.AlgebraSheaf
public import StacksFrontier.CategoryTheory.Images.Sheaf

/-!
# Directedness of the finite type quasi-coherent subalgebras, from three named inputs

Let `X` be a scheme and `A` a sheaf of commutative `𝒪_X`-algebras.  This file reduces **both**
assertions of [Stacks, Tag 05JT] to a short, explicitly named list of open statements, and proves
everything that separates the tag from that list.

The reduction locates the actual difficulty.
`CategoryTheory.Limits.HasImages (CategoryTheory.Under X.sheaf)` is not an obstruction; it
is available (`Stacks.SheafImages.hasImagesTopCatSheaf`), and so is the join of two arbitrary
subobjects.  What directedness needs is not the *existence* of the join but that the join lands
back inside the finite type quasi-coherent subalgebras, and that is a statement about images of
*algebra sheaves*, not about the subobject lattice.

## The three inputs

* `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.ImageIsQuasicoherent`: the image of a morphism
  of quasi-coherent algebra sheaves is quasi-coherent.
* `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.ImageIsLocallySurjective`: the corestriction of
  a morphism of algebra sheaves to its image is locally surjective.
* `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.CoprodIsQuasicoherentFiniteType`: the coproduct
  of two quasi-coherent algebra sheaves of finite type -- their tensor product over `𝒪_X` -- is
  again quasi-coherent and of finite type.

The first two are shared with the colimit assertion.  **The third is needed by directedness
alone and is not implied by the first two**: `isFiniteType_of_isLocallySurjective` reads finite
typeness of an image off its *source*, and the source of the map whose image is the join is the
coproduct, which in a category of sheaves is again a sheafification.  Its fibrewise content is
already in Mathlib -- `Algebra.FiniteType.baseChange` composed with `Algebra.FiniteType.trans` --
so what is open is the identification of the sections of the coproduct sheaf over an affine open
with the tensor product of the sections, not any commutative algebra.

**The third input is stated twice, and the weaker form is the one to discharge.**
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.ExistsFiniteTypeDominating` asks only that two
quasi-coherent finite type algebra sheaves over `A` be dominated by *some* quasi-coherent finite
type algebra sheaf over `A`, not that the ambient coproduct be one.  The coproduct input implies
it (`existsFiniteTypeDominating_of_coprod`) and the converse is not claimed.  This matters
because the ambient coproduct is a sheafification while the coproduct in the full subcategory of
*quasi-coherent* algebra sheaves is quasi-coherent by construction, and that subcategory is
already understood at this pin: `Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence`
is an unconditional anti-equivalence between it and the schemes affine over `X`, under which a
coproduct of algebras is a fibre product of affine morphisms.  Only the `∃`-shaped assertions can
be weakened this way; `supClosed_of_imageData` genuinely needs the ambient coproduct, because
`CategoryTheory.Subobject.semilatticeSup`'s `⊔` is defined from it.

## Main results

* `isFiniteType_unitAlgebra`: the structure sheaf, as an algebra over itself, is of finite type.
  Together with `Stacks.SectionEpiAffine.isQuasicoherent_unitAlgebra` this makes the initial
  algebra sheaf an admissible source, which is what nonemptiness is built from.
* `sup_eq_imageSubobject_coprodDesc`: **the join of two subobjects is the image of the morphism
  out of their coproduct.** A general fact about any category with images and binary coproducts,
  absent from Mathlib, which only ever uses this description inside the construction of
  `CategoryTheory.Subobject.semilatticeSup` and never states it.
* `nonempty_finiteTypeSubalgebra`: `FiniteTypeSubalgebra A` is nonempty, from the first two
  inputs only.
* `exists_join_of_dominating`, `exists_join_of_imageData` and `supClosed_of_imageData`: the upper
  bound that directedness asks for, in the three shapes the tree consumes it in.
* `isFiltered_of_dominating` and `isFiltered_of_imageData`: **the directedness assertion of
  [Stacks, Tag 05JT]**, with the tag's hypotheses and the three inputs.
* `nonempty_isColimit_of_imageData`: **the colimit assertion of [Stacks, Tag 05JT]**, with the
  tag's hypotheses, the three inputs and the affine sections statement.

## Implementation notes

`nonempty_finiteTypeSubalgebra` needs **only** the two image inputs, while the upper bound needs
all three.  The split is deliberate and is the point of stating the inputs separately: the
witness for nonemptiness is the image of the initial algebra sheaf `Under.mk (𝟙 X.sheaf)`, whose
structure map is an identity, so no coproduct is involved and no tensor product has to be
identified.

`exists_join_of_imageData` is proved **without** `sup_eq_imageSubobject_coprodDesc` and without
`CategoryTheory.Subobject.semilatticeSup`: the upper bound is produced directly as
`CategoryTheory.Subobject.imageSubobject` of the coproduct morphism, and the two inequalities are
`CategoryTheory.Subobject.le_mk_of_comm` applied to `coprod.inl ≫ factorThruImage` and
`coprod.inr ≫ factorThruImage`.  So directedness never needs the subobject lattice to be
complete, only the one image -- and `isFilteredOrEmpty_of_exists_join` consumes exactly that
`∃`-shape.  `supClosed_of_imageData` is supplied in addition because
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.SupClosed` is the shape the rest of the tree was
built against; it is strictly the longer route.

Dot notation is not available on an `image`: the type of `CategoryTheory.Limits.image φ` is
inferred as the unfolded `CategoryTheory.Comma`, not as
`Stacks.RelativeSpec.AlgebraSheaf X`, so `(image φ).IsFiniteType` is an invalid projection and
the properties have to be named as `Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType (image φ)`.
The same applies to `Under.mk (𝟙 X.sheaf)`.

## What is not done

The three inputs are not proved here, and no `stacks` attribute is attached: every statement
below carries hypotheses that [Stacks, Tag 05JT] does not.  The colimit assertion additionally
rests on the affine sections statement written out at
`StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraJoin/Generated.lean`, whose own inputs are
[Stacks, Tag 01PG] for modules and the surjectivity half of [Stacks, Tag 01YB].

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec

universe v u

/-- A subobject `S` of `A` whose arrow factors through `c : E ⟶ A` lies below the image of `c`. -/
private theorem le_imageSubobject_of_comm {C : Type u} [Category.{v} C] [HasImages C]
    {A E : C} (S : Subobject A) (c : E ⟶ A) (u : (S : C) ⟶ E)
    (hu : u ≫ c = S.arrow) : S ≤ imageSubobject c :=
  Subobject.le_mk_of_comm (u ≫ factorThruImage c) (by rw [Category.assoc, image.fac, hu])

namespace Stacks.SubobjectSup

variable {C : Type u} [Category.{v} C] [HasImages C] [HasBinaryCoproducts C]

/-- **The join of two subobjects is the image of the morphism out of their coproduct.**

This is the description `CategoryTheory.Subobject.semilatticeSup` is built from --
`CategoryTheory.Subobject.sup` is `CategoryTheory.MonoOver.sup` descended through the thin
skeleton, and `CategoryTheory.MonoOver.sup` is `CategoryTheory.Over.coprod` followed by
`CategoryTheory.Limits.image` -- but Mathlib never states it, so the join cannot be recognized as
an image without this lemma.

The proof is by antisymmetry rather than by unfolding the thin skeleton: `≤` is `sup_le` applied
to the two inclusions of the summands into the image, and `≥` factors the coproduct morphism
through the join by `CategoryTheory.Subobject.ofLE` and then through the image by
`CategoryTheory.Limits.image.lift`. -/
theorem sup_eq_imageSubobject_coprodDesc {A : C} (S T : Subobject A) :
    (S ⊔ T : Subobject A) = imageSubobject (coprod.desc S.arrow T.arrow) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact le_imageSubobject_of_comm _ _ coprod.inl (coprod.inl_desc _ _)
    · exact le_imageSubobject_of_comm _ _ coprod.inr (coprod.inr_desc _ _)
  · refine Subobject.mk_le_of_comm (image.lift
      { I := ((S ⊔ T : Subobject A) : C)
        m := (S ⊔ T : Subobject A).arrow
        e := coprod.desc (Subobject.ofLE _ _ le_sup_left) (Subobject.ofLE _ _ le_sup_right)
        fac := by ext <;> simp }) ?_
    exact image.lift_fac _

end Stacks.SubobjectSup

namespace Stacks.AlgebraicGeometry.FiniteTypeSubalgebras

variable {X : Scheme.{u}}

/-! ### Instance synthesis at the consumer's spelling

`Stacks.SheafImages.hasImagesTopCatSheaf` provides images at the `TopCat.Sheaf` spelling, but an
instance that exists and is not *found* at the spelling a consumer writes is worth nothing, and
this has twice gone wrong in this directory.  These three record that the chain is traversed by
instance search at `Stacks.RelativeSpec.AlgebraSheaf X`, which is where the join is used. -/

/-- **Images exist at the algebra sheaf spelling**, by instance search alone, through
`Stacks.SheafImages.hasImagesTopCatSheaf` and `Stacks.UnderImages.hasImages`. -/
theorem hasImages_algebraSheaf (X : Scheme.{u}) : HasImages (AlgebraSheaf X) := inferInstance

/-- **Any two subobjects of an algebra sheaf have an upper bound.**  Writing `S ⊔ T` at all
forces `CategoryTheory.Subobject.semilatticeSup` to be synthesized at this spelling, over
`hasImages_algebraSheaf` and
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.hasBinaryCoproducts`, so this records as a
declaration what was previously recorded only as a measurement.

It is `Stacks.SheafImages.sheafAlgebra_exists_sup` at the algebra sheaf spelling, and it is
emphatically **not** the directedness assertion of [Stacks, Tag 05JT]: the bound carries no
property at all, whereas directedness needs one that is quasi-coherent and of finite type.  That
gap is the whole content of `exists_join_of_imageData`. -/
theorem exists_sup_subobject_algebraSheaf (X : Scheme.{u}) (A : AlgebraSheaf X)
    (S T : Subobject A) : ∃ U : Subobject A, S ≤ U ∧ T ≤ U :=
  ⟨S ⊔ T, le_sup_left, le_sup_right⟩

/-! ### The initial algebra sheaf -/

/-- **The structure sheaf, as an algebra over itself, is of finite type.**  Its structure
morphism is the identity, so over every affine open the ring map whose finite typeness is tested
is the identity ring map.

This is the finite type counterpart of
`Stacks.SectionEpiAffine.isQuasicoherent_unitAlgebra`, and the pair of them is what makes
`Under.mk (𝟙 X.sheaf)` an admissible source for `isFiniteType_image`. -/
theorem isFiniteType_unitAlgebra (X : Scheme.{u}) :
    AlgebraSheaf.IsFiniteType (X := X) (Under.mk (𝟙 X.sheaf)) := fun _ _ =>
  RingHom.FiniteType.id _

/-- The canonical morphism from the initial algebra sheaf `𝒪_X` to an algebra sheaf `A`, namely
the structure morphism of `A` read as a morphism under `𝒪_X`. -/
def unitAlgebraHom (A : AlgebraSheaf X) : (Under.mk (𝟙 X.sheaf) : AlgebraSheaf X) ⟶ A :=
  Under.homMk A.hom (by simp)

/-! ### The three inputs -/

/-- **Input 1.** The image of a morphism of quasi-coherent algebra sheaves is quasi-coherent.

Unwinding `Stacks.SheafImages.hasImages`, the image of a morphism of sheaves is the
sheafification of the image presheaf; quasi-coherence of it is the identification of the
underlying module of that image algebra sheaf with the image of the underlying module morphism,
where `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel` then apply. -/
def ImageIsQuasicoherent (X : Scheme.{u}) : Prop :=
  ∀ (C D : AlgebraSheaf X) (φ : C ⟶ D), AlgebraSheaf.IsQuasicoherent C →
    AlgebraSheaf.IsQuasicoherent D → AlgebraSheaf.IsQuasicoherent (image φ)

/-- **Input 2.** The corestriction of a morphism of algebra sheaves to its image is locally
surjective.  Without this
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` cannot be
applied to an image at all. -/
def ImageIsLocallySurjective (X : Scheme.{u}) : Prop :=
  ∀ (C D : AlgebraSheaf X) (φ : C ⟶ D), Sheaf.IsLocallySurjective (factorThruImage φ).right

/-- **Input 3.** The coproduct of two quasi-coherent algebra sheaves of finite type -- their
tensor product over `𝒪_X`, by `Stacks.UnderCoproducts.hasBinaryCoproducts` -- is again
quasi-coherent and of finite type.

This input is **not** implied by the first two and is needed by the directedness assertion alone:
`isFiniteType_of_isLocallySurjective` reads finite typeness of an image off its source, and the
source of the morphism whose image is the join of two subobjects is their coproduct.  The
coproduct in a category of sheaves is a sheafification, so its sections over an affine open are
not visibly the tensor product of the sections; that identification, not any commutative algebra,
is the content.  The fibrewise statement is already in Mathlib, as `Algebra.FiniteType.baseChange`
composed with `Algebra.FiniteType.trans`. -/
def CoprodIsQuasicoherentFiniteType (X : Scheme.{u}) : Prop :=
  ∀ S T : AlgebraSheaf X, AlgebraSheaf.IsQuasicoherent S → AlgebraSheaf.IsFiniteType S →
    AlgebraSheaf.IsQuasicoherent T → AlgebraSheaf.IsFiniteType T →
    AlgebraSheaf.IsQuasicoherent (S ⨿ T) ∧ AlgebraSheaf.IsFiniteType (S ⨿ T)

/-- **Input 3, weakened -- and this is the form to discharge.**  Two quasi-coherent algebra
sheaves of finite type mapping to `A` are both dominated by a single quasi-coherent algebra sheaf
of finite type mapping to `A`.

`CoprodIsQuasicoherentFiniteType` implies this, by
`existsFiniteTypeDominating_of_coprod`, and the converse is not claimed: the dominating object
is **not** required to be the coproduct, only to receive both morphisms compatibly.  That freedom
matters, because the coproduct taken in the *ambient* category `AlgebraSheaf X` is a
sheafification and its affine sections are not visibly a tensor product, whereas the coproduct
taken in the full subcategory of *quasi-coherent* algebra sheaves is quasi-coherent by
construction.  The latter is reachable at this pin: `Stacks.AffineAlgebraEquivalence`
supplies an unconditional anti-equivalence between quasi-coherent algebra sheaves on `X` and
schemes affine over `X`, under which a coproduct of algebras is a fibre product of affine
morphisms -- and fibre products of schemes exist.  A dominating object produced that way satisfies
this input without any statement about the ambient coproduct. -/
def ExistsFiniteTypeDominating (X : Scheme.{u}) : Prop :=
  ∀ (A S T : AlgebraSheaf X) (s : S ⟶ A) (t : T ⟶ A),
    AlgebraSheaf.IsQuasicoherent S → AlgebraSheaf.IsFiniteType S →
    AlgebraSheaf.IsQuasicoherent T → AlgebraSheaf.IsFiniteType T →
    ∃ (C : AlgebraSheaf X) (c : C ⟶ A), AlgebraSheaf.IsQuasicoherent C ∧
      AlgebraSheaf.IsFiniteType C ∧ (∃ u : S ⟶ C, u ≫ c = s) ∧ (∃ v : T ⟶ C, v ≫ c = t)

/-- The coproduct input implies the dominating input: the coproduct dominates, with
`CategoryTheory.Limits.coprod.desc` as the morphism to `A` and the two coproduct inclusions as
the factorisations. -/
theorem existsFiniteTypeDominating_of_coprod (h₃ : CoprodIsQuasicoherentFiniteType X) :
    ExistsFiniteTypeDominating X := by
  intro A S T s t hSqc hSft hTqc hTft
  obtain ⟨hqc, hft⟩ := h₃ S T hSqc hSft hTqc hTft
  exact ⟨S ⨿ T, coprod.desc s t, hqc, hft, ⟨coprod.inl, coprod.inl_desc _ _⟩,
    ⟨coprod.inr, coprod.inr_desc _ _⟩⟩

/-! ### Images of algebra sheaves -/

/-- **The image of a quasi-coherent algebra sheaf of finite type is of finite type.**  Granted
the two image inputs, the corestriction `C ⟶ image φ` is a locally surjective morphism of
quasi-coherent algebra sheaves, so
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` applies.

No hypothesis on `X` is used. -/
theorem isFiniteType_image (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    {C D : AlgebraSheaf X} (φ : C ⟶ D) (hC : AlgebraSheaf.IsQuasicoherent C)
    (hD : AlgebraSheaf.IsQuasicoherent D) (hCft : AlgebraSheaf.IsFiniteType C) :
    AlgebraSheaf.IsFiniteType (image φ) :=
  isFiniteType_of_isLocallySurjective (factorThruImage φ) hC (h₁ C D φ hC hD) (h₂ C D φ) hCft

/-- The image of a morphism into `A` out of a quasi-coherent algebra sheaf of finite type, as an
object of `FiniteTypeSubalgebra A`. -/
def ofImage (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X) {A C : AlgebraSheaf X}
    (φ : C ⟶ A) (hC : AlgebraSheaf.IsQuasicoherent C) (hA : AlgebraSheaf.IsQuasicoherent A)
    (hCft : AlgebraSheaf.IsFiniteType C) : FiniteTypeSubalgebra A :=
  ofMono (image.ι φ) (h₁ C A φ hC hA) (isFiniteType_image h₁ h₂ φ hC hA hCft)

/-- The subobject underlying `ofImage h₁ h₂ φ hC hA hCft` is the image of `φ`. -/
@[simp]
theorem ofImage_obj (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    {A C : AlgebraSheaf X} (φ : C ⟶ A) (hC : AlgebraSheaf.IsQuasicoherent C)
    (hA : AlgebraSheaf.IsQuasicoherent A) (hCft : AlgebraSheaf.IsFiniteType C) :
    (ofImage h₁ h₂ φ hC hA hCft).obj = Subobject.mk (image.ι φ) :=
  rfl

/-! ### Nonemptiness -/

/-- **The finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf are
nonempty**, granted the two image inputs.

The witness is the image of the initial algebra sheaf `𝒪_X`, i.e. the subalgebra generated by no
sections.  This needs **neither** the coproduct input **nor** any hypothesis on `X`: the source
is `Under.mk (𝟙 X.sheaf)`, which is quasi-coherent by
`Stacks.SectionEpiAffine.isQuasicoherent_unitAlgebra` and of finite type by
`isFiniteType_unitAlgebra`, so no tensor product has to be identified.

`CategoryTheory.Subobject.orderBot` is *not* an alternative: it needs
`CategoryTheory.Limits.InitialMonoClass (CategoryTheory.Under X.sheaf)`, i.e. that every algebra
sheaf has injective structure morphism, which is false. -/
theorem nonempty_finiteTypeSubalgebra (h₁ : ImageIsQuasicoherent X)
    (h₂ : ImageIsLocallySurjective X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : Nonempty (FiniteTypeSubalgebra A) :=
  ⟨ofImage h₁ h₂ (unitAlgebraHom A) (Stacks.SectionEpiAffine.isQuasicoherent_unitAlgebra X) hA
    (isFiniteType_unitAlgebra X)⟩

/-! ### The upper bound -/

/-- **Any two finite type quasi-coherent subalgebras of `A` are contained in a third**, granted
all three inputs.

The third is the image of the morphism `S ⨿ T ⟶ A` out of the coproduct, i.e. the subalgebra
generated by both.  The two inequalities are `CategoryTheory.Subobject.le_mk_of_comm` applied to
`coprod.inl ≫ factorThruImage` and `coprod.inr ≫ factorThruImage`; in particular **the subobject
lattice is not used**, only the single image, which is why this is the `∃`-shape that
`isFilteredOrEmpty_of_exists_join` consumes verbatim. -/
theorem exists_join_of_dominating (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : ExistsFiniteTypeDominating X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) (B C : FiniteTypeSubalgebra A) :
    ∃ D : FiniteTypeSubalgebra A, B.obj ≤ D.obj ∧ C.obj ≤ D.obj := by
  obtain ⟨E, c, hEqc, hEft, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
    h₃ A _ _ B.obj.arrow C.obj.arrow B.property.1 B.property.2 C.property.1 C.property.2
  refine ⟨ofImage h₁ h₂ c hEqc hA hEft, ?_, ?_⟩
  · exact le_imageSubobject_of_comm _ c u hu
  · exact le_imageSubobject_of_comm _ c v hv

/-- The same upper bound from the stronger coproduct input, for consumers that have it in that
shape. -/
theorem exists_join_of_imageData (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) (B C : FiniteTypeSubalgebra A) :
    ∃ D : FiniteTypeSubalgebra A, B.obj ≤ D.obj ∧ C.obj ≤ D.obj :=
  exists_join_of_dominating h₁ h₂ (existsFiniteTypeDominating_of_coprod h₃) A hA B C

/-- **The join of two finite type quasi-coherent subobjects of `A` is again quasi-coherent and of
finite type**, granted all three inputs.

This is `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.SupClosed`, the shape the rest of the
tree was built against.  It is the longer route to directedness: the join has to be recognized as
an image first, by `Stacks.SubobjectSup.sup_eq_imageSubobject_coprodDesc`, whereas
`exists_join_of_imageData` produces the image directly and never mentions `⊔`. -/
theorem supClosed_of_imageData (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : SupClosed A := by
  intro S T hSqc hSft hTqc hTft
  obtain ⟨hqc, hft⟩ := h₃ _ _ hSqc hSft hTqc hTft
  rw [Stacks.SubobjectSup.sup_eq_imageSubobject_coprodDesc]
  exact ⟨isQuasicoherent_mk _ (h₁ _ _ _ hqc hA),
    isFiniteType_mk _ (isFiniteType_image h₁ h₂ _ hqc hA hft)⟩

/-! ### The two assertions of Tag 05JT -/

/-- **The directedness assertion of [Stacks, Tag 05JT], granted the three inputs.**  The finite
type quasi-coherent subalgebras of a quasi-coherent algebra sheaf form a filtered category.

The hypotheses are those of the tag -- an algebra sheaf `A` and its quasi-coherence -- together with
the three inputs, and **nothing else**: no quasi-compactness, no quasi-separatedness, no
Noetherian and no affineness hypothesis appears, as the source requires for this assertion.  The
formal part is `isFilteredOrEmpty_of_exists_join`; the content is
`nonempty_finiteTypeSubalgebra` and `exists_join_of_imageData`. -/
theorem isFiltered_of_dominating (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : ExistsFiniteTypeDominating X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : IsFiltered (FiniteTypeSubalgebra A) :=
  isFiltered_of_exists_join A (nonempty_finiteTypeSubalgebra h₁ h₂ A hA)
    (exists_join_of_dominating h₁ h₂ h₃ A hA)

/-- The same conclusion from the stronger coproduct input, for consumers that have it in that
shape. -/
theorem isFiltered_of_imageData (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : IsFiltered (FiniteTypeSubalgebra A) :=
  isFiltered_of_dominating h₁ h₂ (existsFiniteTypeDominating_of_coprod h₃) A hA

/-- **The colimit assertion of [Stacks, Tag 05JT], granted the three inputs and the affine
sections statement.**  On a quasi-compact and quasi-separated scheme a quasi-coherent algebra
sheaf is the colimit of its finite type quasi-coherent subalgebras, with the canonical inclusion
maps.

The affine sections hypothesis is `exists_finiteTypeSubalgebra_section` as written out in
`StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraJoin/Generated.lean`; it is where the two
instance hypotheses are genuinely used, and it is open.  Everything else is
`nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineSections` over
`isFiltered_of_imageData`. -/
theorem nonempty_isColimit_of_imageData [CompactSpace X] [QuasiSeparatedSpace X]
    (h₁ : ImageIsQuasicoherent X) (h₂ : ImageIsLocallySurjective X)
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (hsec : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (op U),
      ∃ (B : FiniteTypeSubalgebra A) (y : (B.obj : AlgebraSheaf X).right.obj.obj (op U)),
        (B.obj.arrow.right.hom.app (op U)) y = x) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone A)) :=
  have := isFiltered_of_imageData h₁ h₂ h₃ A hA
  nonempty_isColimit_finiteTypeSubalgebraCocone_of_affineSections A hsec

end Stacks.AlgebraicGeometry.FiniteTypeSubalgebras

end
