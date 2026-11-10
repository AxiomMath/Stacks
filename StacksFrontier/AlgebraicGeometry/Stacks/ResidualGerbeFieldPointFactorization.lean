module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery

/-!
# A field-valued point factors through the residual gerbe it lies on (Stacks 06MW)

**Stacks 06MW.** Let `𝒳` be an algebraic stack over `S`, let `x` be a point of `|𝒳|` and assume
the residual gerbe `𝒵_x` of `𝒳` at `x` exists. Let `f : Spec K ⟶ 𝒳` be a 1-morphism with `K` a
field in the equivalence class of `x`. Then `f` factors through the inclusion `𝒵_x ⟶ 𝒳`.

The proof is the source's, rearranged so that its hard half is the already-formalized **Stacks
06MQ** rather than a second run of that lemma's argument. The source forms `T = Spec K ×_𝒳 𝒵_x`,
notes that it is nonempty by **Stacks 04XH** and that `T ⟶ Spec K` is a monomorphism because
`𝒵_x ⟶ 𝒳` is, and concludes `T = Spec K` by **Stacks 06MG**. Here the same `T` is formed as the
canonical 2-fibre product of algebraic stacks; its projection to the algebraic stack of `Spec K`
is a monomorphism by **Stacks 04ZX**, and the algebraic stack of `Spec K` *is* covered by the
spectrum of a field — by its own identity 1-morphism. That is exactly the hypothesis of
**Stacks 06MQ**, which therefore turns the nonemptiness supplied by Stacks 04XH into an
equivalence over the site `T ≃ Spec K`. Composing a quasi-inverse of that equivalence with the
projection `T ⟶ 𝒵_x` gives the factorisation.

## Main results

* `AlgebraicGeometry.Stack.hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack`: the
  algebraic stack of a field spectrum satisfies condition (2) of **Stacks 06MP**, its identity
  being a surjective flat 1-morphism from a field spectrum which is locally of finite
  presentation.
* `AlgebraicGeometry.Stack.exists_factorization_of_hasUniquePointOver`: the factorisation, for a
  substack given by an object property whose full subcategory is an algebraic stack with a unique
  point lying over `x`.
* `AlgebraicGeometry.Stack.exists_factorization_of_isResidualGerbeAt`: **Stacks 06MW**.

## Implementation notes

The residual gerbe is the object property `P` of `AlgebraicGeometry.Stack.IsResidualGerbeAt` (the
specification of **Stacks 06MT**) and the inclusion `𝒵_x ⟶ 𝒳` is
`AlgebraicGeometry.Stack.fullSubcategoryInclusion`. Of the four clauses of `IsResidualGerbeAt`
only the last — that the full subcategory has exactly one point, lying over `x` — is used, so the
workhorse lemma asks for that clause alone and the statement at `IsResidualGerbeAt` is a
corollary. Reducedness and local Noetherianity play no role in the source's argument either.

"Factors through" is the literal one: a 1-morphism `g` to the substack together with a
2-isomorphism `g ≫ (𝒵_x ⟶ 𝒳) ≅ f` in the 2-category of algebraic stacks over `S`. It is
assembled from the 2-cell of the 2-fibre product square and the counit of the equivalence of
Stacks 06MQ; the counit is a natural isomorphism of the underlying functors whose components are
vertical, so `CategoryTheory.BasedNatIso.mkNatIso` repackages it as a 2-isomorphism and
`CategoryTheory.Bicategory.InducedBicategory.isoMk` lifts it through the two subtype layers
between `CategoryTheory.BasedCategory` and the algebraic stacks.

Monomorphy of the inclusion is not available unconditionally: `IsResidualGerbeAt` does not record
it, and `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` (**Stacks 04ZW**) has two
conjuncts, of which only the second,
`AlgebraicGeometry.Stack.AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion`, is
proved for a full subcategory inclusion outright. The first, representability by algebraic
spaces, is the implication (2) ⟹ (3) of **Stacks 04Y5** for the faithful inclusion, which the
library has from the bootstrap theorem Stacks 04S6 part (3)
(`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`
fed with `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`).
The workhorse lemma takes representability as a hypothesis on the substack, and the statement at
`IsResidualGerbeAt` supplies it from the bootstrap theorem; the two conjuncts are assembled
directly, as an `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism`.

"`K` is in the equivalence class of `x`" is spelled as: the 1-morphism is out of the algebraic
stack of an `AlgebraicGeometry.Stack.FieldSpectrum`, and some point of that stack maps to `x`.
Since the spectrum of a field has one point this is the same as asking that *the* point of
`Spec K` map to `x`.

Base change of a monomorphism (**Stacks 04ZX**) is available only for the canonical 2-fibre
product square `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, so that is the
model of `T` used here; the universal property that **Stacks 04XH** needs holds for it
unconditionally.

Flatness of an identity 1-morphism of algebraic stacks is reproved below, because the
proof in `StacksFrontier/AlgebraicGeometry/Stacks/GerbeFlatFinitePresentation.lean` is private.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZX](https://stacks.math.columbia.edu/tag/04ZX)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MW](https://stacks.math.columbia.edu/tag/06MW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity 1-morphism of an algebraic stack over `S` is flat.** A smooth presentation of
`𝒵` by an algebraic space `V`, surjective on objects, is a diagram of Stacks 06FM over `𝟙 𝒵`
whose two vertical 1-morphisms are that presentation and whose top horizontal morphism is `𝟙 V`,
which is flat.

This repeats a private declaration of
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeFlatFinitePresentation.lean`. -/
private theorem isFlat_id_algebraicStack (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsFlat B S hS (𝟙 𝒵) := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  obtain ⟨κ⟩ := nonempty_twoIso_associatedMap_id B S hS V
  refine ⟨V, V, hV, hV, b, b, 𝟙 V, ⟨?_⟩, hbsm, hbsu, hbsm, Space.isFlat_id B S hS hV⟩
  exact Bicategory.whiskerRightIso κ b ≪≫ Bicategory.leftUnitor b ≪≫
    (Bicategory.rightUnitor b).symm

/-- **The algebraic stack of a field spectrum is covered by the spectrum of a field**, in the
sense of condition (2) of **Stacks 06MP**: its identity 1-morphism is locally of finite
presentation, surjective and flat, and its source is the algebraic stack of a field spectrum.

This is what makes **Stacks 06MQ** applicable to a monomorphism *into* the algebraic stack of a
field spectrum. -/
theorem hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack
    (F : FieldSpectrum B S hS) :
    HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
      (schemeStack.{u, w} B S hS F.base) :=
  ⟨F, 𝟙 _,
    AlgebraicStacks.isLocallyOfFinitePresentation_id B S hS _,
    fun q => ⟨q, congrFun (AlgebraicStacks.pointsMap_id B S hS _) q⟩,
    isFlat_id_algebraicStack.{u, w} B S hS _⟩

/-- **A field-valued point lying on a one-point algebraic substack factors through it.** Let `P`
be a property of the objects of an algebraic stack `𝒳` over `S` whose full subcategory is an
algebraic stack, let `F` be a field spectrum and let `f` be a 1-morphism from the algebraic stack
of `F` to `𝒳` some point of which maps to a point `x` of `|𝒳|`. If the inclusion of the full
subcategory is representable by algebraic spaces and the full subcategory has exactly one point,
lying over `x`, then `f` factors through the inclusion, up to a 2-isomorphism.

This is the content of **Stacks 06MW**; see
`AlgebraicGeometry.Stack.exists_factorization_of_isResidualGerbeAt` for the statement at the
residual gerbe. **Stacks 04XH** puts a point on the canonical 2-fibre product of `f` with the
inclusion, whose projection to the algebraic stack of `F` is a monomorphism by **Stacks 04ZX**;
**Stacks 06MQ** then makes that projection an equivalence over the site, and a quasi-inverse of
it composed with the other projection is the factorisation. -/
theorem exists_factorization_of_hasUniquePointOver
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hrep : IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryInclusion 𝒳 P hP).hom.hom)
    (hx : HasUniquePointOver B S hS (fullSubcategoryInclusion 𝒳 P hP) x)
    (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (t : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base))
    (ht : AlgebraicStacks.pointsMap B S hS f t = x) :
    ∃ g : schemeStack.{u, w} B S hS F.base ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP,
      Nonempty (g ≫ fullSubcategoryInclusion 𝒳 P hP ≅ f) := by
  classical
  obtain ⟨z, -, hz⟩ := hx
  have hmono : AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒳 P hP) :=
    ⟨hrep, AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion B S hS 𝒳 P hP⟩
  set Q := twoFibreProductSquareAlgebraicStacks B S hS f (fullSubcategoryInclusion 𝒳 P hP) with hQ
  have hfst : AlgebraicStacks.IsMonomorphism B S hS Q.fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS f
      (fullSubcategoryInclusion 𝒳 P hP) hmono
  obtain ⟨r, -, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q
    (hQ ▸ isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f
      (fullSubcategoryInclusion 𝒳 P hP)) t z (ht.trans hz.symm)
  rcases isEmpty_points_or_isEquivalenceOver_of_isMonomorphism B S hS Q.pt
      (schemeStack.{u, w} B S hS F.base) Q.fst hfst
      (hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack.{u, w} B S hS F)
    with hempty | hne
  · exact hempty.elim r
  obtain ⟨e⟩ := hne
  have hcomp : (e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom) ⋙
      (schemeStack.{u, w} B S hS F.base).val.val.p =
        (schemeStack.{u, w} B S hS F.base).val.val.p :=
    calc (e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom) ⋙
          (schemeStack.{u, w} B S hS F.base).val.val.p
        = e.inv ⋙ (CatFiberedInGroupoids.homFunctor Q.fst.hom ⋙
            (schemeStack.{u, w} B S hS F.base).val.val.p) := Functor.assoc _ _ _
      _ = e.inv ⋙ Q.pt.val.val.p :=
          congrArg (e.inv ⋙ ·) (CatFiberedInGroupoids.homFunctor_comp_p Q.fst.hom)
      _ = (schemeStack.{u, w} B S hS F.base).val.val.p := e.inv_over
  have hbase : ∀ a : (schemeStack.{u, w} B S hS F.base).val.val.obj,
      (schemeStack.{u, w} B S hS F.base).val.val.p.obj
        ((e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom).obj a) =
      (schemeStack.{u, w} B S hS F.base).val.val.p.obj a :=
    fun a => Functor.congr_obj hcomp a
  obtain ⟨g, ⟨cu⟩⟩ : ∃ g : schemeStack.{u, w} B S hS F.base ⟶ Q.pt,
      Nonempty (g ≫ Q.fst ≅ 𝟙 (schemeStack.{u, w} B S hS F.base)) :=
    ⟨Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      ({ toFunctor := e.inv, w := e.inv_over } :
        (schemeStack.{u, w} B S hS F.base).val.val ⥤ᵇ Q.pt.val.val)),
      ⟨Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
        (BasedNatIso.mkNatIso e.counitIso fun a => by
          have h := e.counit_vertical a
          rwa [hbase a] at h))⟩⟩
  refine ⟨g ≫ Q.snd, ⟨?_⟩⟩
  exact (Bicategory.associator _ Q.snd (fullSubcategoryInclusion 𝒳 P hP)).trans
    ((Bicategory.whiskerLeftIso _ Q.iso).symm.trans
      ((Bicategory.associator _ Q.fst f).symm.trans
        ((Bicategory.whiskerRightIso cu f).trans (Bicategory.leftUnitor f))))

/-- **Stacks 06MW.** Let `𝒳` be an algebraic stack over `S`, let `x` be a point of `|𝒳|` and
assume the residual gerbe `𝒵_x` of `𝒳` at `x` exists, i.e. an object property `P` of `𝒳`
satisfies the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**. Let
`f` be a 1-morphism to `𝒳` from the algebraic stack of the spectrum of a field, some point of
which maps to `x`. Then `f` factors through the inclusion `𝒵_x ⟶ 𝒳`: there is a 1-morphism `g`
to the full subcategory selected by `P` and a 2-isomorphism `g ≫ (𝒵_x ⟶ 𝒳) ≅ f`.

The factorisation is `AlgebraicGeometry.Stack.exists_factorization_of_hasUniquePointOver`, which
uses only the one-point clause of `IsResidualGerbeAt`. It needs the inclusion `𝒵_x ⟶ 𝒳` to be a
monomorphism, so representable by algebraic spaces; the source has this from Stacks 04Y5, the
inclusion being fully faithful, and the library has the implication (2) ⟹ (3) of Stacks 04Y5 as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`,
from the bootstrap theorem Stacks 04S6 part (3). -/
@[stacks 06MW]
theorem exists_factorization_of_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsResidualGerbeAt B S hS 𝒳 x P)
    (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (t : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base))
    (ht : AlgebraicStacks.pointsMap B S hS f t = x) :
    ∃ g : schemeStack.{u, w} B S hS F.base ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP.2.choose,
      Nonempty (g ≫ fullSubcategoryInclusion 𝒳 P hP.2.choose ≅ f) :=
  exists_factorization_of_hasUniquePointOver.{u, w} B S hS 𝒳 x P hP.2.choose
    (AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful B S hS
      (fullSubcategoryInclusion 𝒳 P hP.2.choose) inferInstance)
    hP.2.choose_spec.2.2 F f t ht

end AlgebraicGeometry.Stack

end
