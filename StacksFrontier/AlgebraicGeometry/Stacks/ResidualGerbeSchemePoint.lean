module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFieldPointFactorization

/-!
# The residual gerbe at a point of a scheme or of an algebraic space (Stacks 0H21)

**Stacks 0H21** records two instances of the residual gerbe of **Stacks 06MU**.

1. Let `X` be a scheme and let `x ∈ X`. Identifying `x` with `Spec (κ(x))`, the monomorphism
   `x ⟶ X` is the residual gerbe of `X` at `x`.
2. Let `X` be an algebraic space and let `x ∈ |X|`. Then the residual gerbe of `X` at `x` — the
   *residual space* at `x` — always exists.

## Main definitions

* `AlgebraicGeometry.Stack.residueFieldSpectrum` and
  `AlgebraicGeometry.Stack.residueFieldInclusion`: the spectrum of the residue field at a point
  of an object of the big fppf site of `S`, as an object of that site over the given one, and its
  structure morphism `Spec (κ(x)) ⟶ X`.
* `AlgebraicGeometry.Stack.residueFieldPointClass`: the point of `|(Sch/X)_fppf|` determined by a
  point of the underlying scheme of `X`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_schemeStackMap_of_mono`: the
  1-morphism of algebraic stacks induced by a monomorphism of the big fppf site of `S` is a
  monomorphism of algebraic stacks in the sense of **Stacks 04ZW**.
* `AlgebraicGeometry.Stack.isResidualGerbeAt_essImage_schemeStackMap`: for a monomorphism
  `g : Spec (k) ⟶ X` in the big fppf site of `S` out of the spectrum of a field, the strictly
  full subcategory of `(Sch/X)_fppf` cut out by the essential image of `(Sch/Spec k)_fppf` is the
  residual gerbe of `(Sch/X)_fppf` at the point `g` picks out.
* `AlgebraicGeometry.Stack.isMonomorphism_and_isResidualGerbeAt_residueField`: **Stacks 0H21**,
  assertion (1).
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_algebraicSpaceStack`: **Stacks 0H21**,
  assertion (2).

## Implementation notes

The residual gerbe is the object property `P` of `AlgebraicGeometry.Stack.IsResidualGerbeAt`,
the specification of **Stacks 06MT**: `P` is closed under isomorphism, its full subcategory is a
reduced locally Noetherian algebraic stack, and that subcategory has exactly one point, lying
over the given point. Assertion (1) therefore has to exhibit `x ⟶ X` as a *strictly full
subcategory* of `(Sch/X)_fppf`, which is done by its essential image, as in **Stacks 06MR**: the
functor `(Sch/Spec κ(x))_fppf ⥤ (Sch/X)_fppf` given by composition with `x ⟶ X` is faithful
always and full because `x ⟶ X` is a monomorphism, so the factorization through the essential
image is an equivalence over the site, hence the essential image is an algebraic stack by
**Stacks 03YQ**, and condition (2) of **Stacks 06MP** travels to it from the algebraic stack of a
field spectrum, where it holds for the identity 1-morphism. Reducedness, local Noetherianity and
the uniqueness of the point then come from the implication (2) ⟹ (1) of Stacks 06MP, and the
point is the image of the point of `Spec (κ(x))` because the factorization composed with the
inclusion is 2-isomorphic to the original 1-morphism.

The spectrum of the residue field is asked to lie in the chosen big fppf site, which is a size
condition on a single scheme and is how every field-valued point in this library is presented;
the point `x` itself is a point of the underlying scheme of the site object.

Assertion (2) is read on the algebraic stack of **Stacks 03YS** associated with the algebraic
space, where existence of the residual gerbe is condition (1) of **Stacks 06MT**. It is the
statement of `AlgebraicGeometry.Stack`
`.hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace` at a stack represented by the
space itself; the monomorphism produced there is the one induced by the residual space
`AlgebraicGeometry.Space.IsResidualSpaceAt` of **Stacks 06R0**, whose existence is **Stacks 06QZ**
in Decent Spaces, Section 68.13 — the reference Stacks 0H21 gives for this assertion.

## References

* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 0H21](https://stacks.math.columbia.edu/tag/0H21)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Full faithfulness of the functor induced by a monomorphism of the site -/

/-- **Composition with a monomorphism of the big fppf category of `S` is full on slices.** A
morphism of the slice over the target between objects coming from the slice over the source is a
morphism of the site which becomes a morphism over the source after cancelling the
monomorphism. -/
theorem full_overMap_of_mono {U V : BigFppfOver B S hS} (g : U ⟶ V) (hg : Mono g) :
    (Over.map g).Full := by
  constructor
  intro a b f
  refine ⟨Over.homMk f.left ?_, Over.OverMorphism.ext rfl⟩
  rw [← cancel_mono g, Category.assoc]
  exact Over.w f

/-- **Composition with a morphism of the big fppf category of `S` is faithful on slices.** It
leaves the underlying morphism of the site unchanged, and a morphism of a slice is determined by
that morphism. -/
theorem faithful_overMap {U V : BigFppfOver B S hS} (g : U ⟶ V) : (Over.map g).Faithful :=
  ⟨fun h => Over.OverMorphism.ext (congrArg (fun k => k.left) h)⟩

/-- **A monomorphism of the big fppf category of `S` induces a full 1-morphism of the associated
algebraic stacks.** The underlying functor of that 1-morphism is composition with the
monomorphism on slices. -/
theorem full_homFunctor_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) (hg : Mono g) :
    (CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS g).hom).Full :=
  full_overMap_of_mono B S hS g hg

/-- **A morphism of the big fppf category of `S` induces a faithful 1-morphism of the associated
algebraic stacks.** -/
theorem faithful_homFunctor_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS g).hom).Faithful :=
  faithful_overMap B S hS g

/-- **Stacks 04ZW for a monomorphism of the big fppf category of `S`.** The induced 1-morphism of
the associated algebraic stacks is representable by algebraic spaces (**Stacks 02ZZ** for
represented source and target) and fully faithful, hence a monomorphism of algebraic stacks by
the implication (2) ⟹ (1) of **Stacks 04ZZ**. -/
theorem AlgebraicStacks.isMonomorphism_schemeStackMap_of_mono
    {U V : BigFppfOver B S hS} (g : U ⟶ V) (hg : Mono g) :
    AlgebraicStacks.IsMonomorphism B S hS (schemeStackMap.{u, w} B S hS g) :=
  ⟨isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g,
    fun U y hy F hF he => mono_representingMaps_of_full_and_faithful B S hS _
      (full_homFunctor_schemeStackMap.{u, w} B S hS g hg)
      (faithful_homFunctor_schemeStackMap.{u, w} B S hS g) U y hy F hF he⟩

/-! ### The residual gerbe at a point of a scheme -/

/-- **A monomorphism from the spectrum of a field cuts out the residual gerbe.** Let `X` be an
object of the big fppf site of `S`, let `F` be the spectrum of a field in that site and let
`g : F ⟶ X` be a monomorphism. Then the strictly full subcategory of `(Sch/X)_fppf` cut out by
the essential image of the induced 1-morphism is the residual gerbe of `(Sch/X)_fppf` at the
image of the point of `F`, in the sense of `AlgebraicGeometry.Stack.IsResidualGerbeAt`.

The induced functor is fully faithful, so the factorization through the essential image is an
equivalence over the big fppf site of `S`; the essential image is therefore an algebraic stack by
**Stacks 03YQ** and satisfies condition (2) of **Stacks 06MP**, which the algebraic stack of a
field spectrum satisfies through its identity 1-morphism. The implication (2) ⟹ (1) of
Stacks 06MP makes it reduced, locally Noetherian and with a single point, and that point lies
over the image of the point of `F` because the factorization followed by the inclusion is
2-isomorphic to the induced 1-morphism. -/
theorem isResidualGerbeAt_essImage_schemeStackMap
    (X : BigFppfOver B S hS) (F : FieldSpectrum B S hS) (g : F.base ⟶ X) (hg : Mono g)
    (x : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS X))
    (q : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base))
    (hx : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g) q = x) :
    IsResidualGerbeAt B S hS (schemeStack.{u, w} B S hS X) x
      (CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS g).hom).essImage := by
  classical
  set i := schemeStackMap.{u, w} B S hS g
  set P := (CatFiberedInGroupoids.homFunctor i.hom).essImage
  have hequiv : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased_of_full_of_faithful B S hS i
      (full_homFunctor_schemeStackMap.{u, w} B S hS g hg)
      (faithful_homFunctor_schemeStackMap.{u, w} B S hS g)
  obtain ⟨e, -⟩ := exists_basedEquivalence_functor_eq B S hS
    (schemeStack.{u, w} B S hS F.base).val (AlgebraicStacks.essImageFibered i)
    (AlgebraicStacks.toEssImageBased i) hequiv
  have hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased (schemeStack.{u, w} B S hS X) P) :=
    (isAlgebraicStack_iff_of_equivalence B S hS e).mp
      (schemeStack.{u, w} B S hS F.base).property
  set t : schemeStack.{u, w} B S hS F.base ⟶
      fullSubcategoryAlgebraicStack (schemeStack.{u, w} B S hS X) P hP :=
    Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (AlgebraicStacks.toEssImageBased i))
  have hcov : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
      (fullSubcategoryAlgebraicStack (schemeStack.{u, w} B S hS X) P hP) :=
    hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor B S hS t hequiv
      (hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack.{u, w} B S hS F)
  obtain ⟨⟨hred, -, hsub⟩, hln⟩ :=
    isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation.{u, w} B S hS
      (fullSubcategoryAlgebraicStack (schemeStack.{u, w} B S hS X) P hP) hcov
  refine ⟨inferInstance, hP, hred, hln,
    AlgebraicStacks.pointsMap B S hS t q, fun z' => hsub.elim z' _, ?_⟩
  have hκ : t ≫ fullSubcategoryInclusion (schemeStack.{u, w} B S hS X) P hP ≅
      i ≫ 𝟙 (schemeStack.{u, w} B S hS X) :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (AlgebraicStacks.toEssImageBasedSquareIso i))
  calc AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion (schemeStack.{u, w} B S hS X) P hP)
          (AlgebraicStacks.pointsMap B S hS t q)
      = AlgebraicStacks.pointsMap B S hS
          (t ≫ fullSubcategoryInclusion (schemeStack.{u, w} B S hS X) P hP) q := by
        simp only [AlgebraicStacks.pointsMap_comp, Function.comp_apply]
    _ = AlgebraicStacks.pointsMap B S hS (i ≫ 𝟙 (schemeStack.{u, w} B S hS X)) q := by
        rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hκ.hom]
    _ = x := by
        simpa only [AlgebraicStacks.pointsMap_comp, Function.comp_apply,
          AlgebraicStacks.pointsMap_id, id_eq] using hx

/-- The spectrum of the residue field of an object `X` of the big fppf site of `S` at a point `x`
of its underlying scheme, as an object of that site over `X`, together with the identification of
its underlying scheme with the spectrum of that field. -/
noncomputable def residueFieldSpectrum
    (X : BigFppfOver B S hS) (x : (BigFppfOver.toScheme B S hS).obj X)
    (hx : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj X).residueField x))) :
    FieldSpectrum B S hS where
  carrier := ((BigFppfOver.toScheme B S hS).obj X).residueField x
  base := Over.mk ((B.inclusion.preimage
    (((BigFppfOver.toScheme B S hS).obj X).fromSpecResidueField x) :
      B.obj hx ⟶ X.left) ≫ X.hom)
  isSpec := Iso.refl _

/-- The structure morphism `Spec (κ(x)) ⟶ X` of
`AlgebraicGeometry.Stack.residueFieldSpectrum`, as a morphism of the big fppf site of `S`. -/
noncomputable def residueFieldInclusion (X : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj X)
    (hx : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj X).residueField x))) :
    (residueFieldSpectrum B S hS X x hx).base ⟶ X :=
  Over.homMk (B.inclusion.preimage
    (((BigFppfOver.toScheme B S hS).obj X).fromSpecResidueField x) :
      B.obj hx ⟶ X.left) rfl

/-- The point of `|(Sch/X)_fppf|` determined by a point `x` of the underlying scheme of `X`: the
class of the tautological field-valued point of `Spec (κ(x))` pushed forward along
`AlgebraicGeometry.Stack.residueFieldInclusion`. -/
noncomputable def residueFieldPointClass (X : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj X)
    (hx : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj X).residueField x))) :
    AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS X) :=
  AlgebraicStacks.pointsMap B S hS
    (schemeStackMap.{u, w} B S hS (residueFieldInclusion B S hS X x hx))
    (pointClass B S hS _ _
      (fieldSpectrumPoint.{u, w} B S hS (residueFieldSpectrum B S hS X x hx)))

/-- **The canonical morphism from the spectrum of a residue field is a monomorphism of the big
fppf site of `S`.** On underlying schemes it is `Spec (κ(x)) ⟶ X`, which is a preimmersion and
hence a monomorphism of schemes; the canonical inclusion of the site and the forgetful functor of
the slice are both faithful, so each reflects monomorphy. -/
theorem mono_residueFieldInclusion (X : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj X)
    (hx : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj X).residueField x))) :
    Mono (residueFieldInclusion B S hS X x hx) := by
  have hmono : Mono (B.inclusion.map (B.inclusion.preimage
      (((BigFppfOver.toScheme B S hS).obj X).fromSpecResidueField x) :
        B.obj hx ⟶ X.left)) := by
    rw [Functor.map_preimage]
    exact inferInstanceAs
      (Mono (((BigFppfOver.toScheme B S hS).obj X).fromSpecResidueField x))
  have : Mono (residueFieldInclusion B S hS X x hx).left :=
    B.inclusion.mono_of_mono_map hmono
  exact Over.mono_of_mono_left _

/-- **Stacks 0H21, assertion (1).** Let `X` be an object of the big fppf site of `S`, let `x` be a
point of its underlying scheme and assume the spectrum of the residue field `κ(x)` lies in the
site. Identifying `x` with `Spec (κ(x))`, the 1-morphism `x ⟶ X` of algebraic stacks over `S` is
a monomorphism (**Stacks 04ZW**) and the strictly full subcategory of `(Sch/X)_fppf` it cuts out
is the residual gerbe of `(Sch/X)_fppf` at `x`, in the sense of
`AlgebraicGeometry.Stack.IsResidualGerbeAt` (the specification of **Stacks 06MT**).

The point of `|(Sch/X)_fppf|` is `AlgebraicGeometry.Stack.residueFieldPointClass`, the class of
the tautological field-valued point of `Spec (κ(x))`, which is the point determined by `x` under
the usual identification of the points of `(Sch/X)_fppf` with the points of `X`. -/
@[stacks 0H21 "the scheme case: the monomorphism x ⟶ X out of the spectrum of the residue \
field at a point x of a scheme X is the residual gerbe of X at x"]
theorem isMonomorphism_and_isResidualGerbeAt_residueField
    (X : BigFppfOver B S hS) (x : (BigFppfOver.toScheme B S hS).obj X)
    (hx : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj X).residueField x))) :
    AlgebraicStacks.IsMonomorphism B S hS
        (schemeStackMap.{u, w} B S hS (residueFieldInclusion B S hS X x hx)) ∧
      IsResidualGerbeAt B S hS (schemeStack.{u, w} B S hS X)
        (residueFieldPointClass.{u, w} B S hS X x hx)
        (CatFiberedInGroupoids.homFunctor
          (schemeStackMap.{u, w} B S hS (residueFieldInclusion B S hS X x hx)).hom).essImage :=
  ⟨AlgebraicStacks.isMonomorphism_schemeStackMap_of_mono.{u, w} B S hS _
      (mono_residueFieldInclusion B S hS X x hx),
    isResidualGerbeAt_essImage_schemeStackMap.{u, w} B S hS X (residueFieldSpectrum B S hS X x hx)
      (residueFieldInclusion B S hS X x hx) (mono_residueFieldInclusion B S hS X x hx) _ _ rfl⟩

/-! ### The residual space at a point of an algebraic space -/

/-- **Stacks 0H21, assertion (2).** Let `F` be an algebraic space over `S` and let `x` be a point
of `|F|`. Then the residual gerbe of `F` at `x` — the *residual space* at `x` — exists: the
algebraic stack of `F` satisfies condition (1) of **Stacks 06MT** at `x`, which by **Stacks 06MU**
is existence of the residual gerbe there.

The algebraic stack of `F` is represented by `F` itself, so this is
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace`, whose
witness is the 1-morphism induced by the residual space of **Stacks 06R0**; residual spaces exist
by **Stacks 06QZ**. -/
@[stacks 0H21 "the algebraic space case: the residual gerbe at a point of an algebraic space, \
called the residual space, always exists"]
theorem hasSingletonPointMonomorphism_algebraicSpaceStack
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (x : AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS F hF)) :
    HasSingletonPointMonomorphism B S hS (algebraicSpaceStack.{u, w} B S hS F hF) x :=
  hasSingletonPointMonomorphism_of_isRepresentableByAlgebraicSpace.{u, w} B S hS
    (algebraicSpaceStack.{u, w} B S hS F hF)
    ⟨F, hF, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩ x

end AlgebraicGeometry.Stack

end
