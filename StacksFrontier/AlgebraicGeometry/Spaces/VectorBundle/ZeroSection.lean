module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraBounded

/-!
# The zero section of a vector bundle on an algebraic space

Let `X` be an algebraic space over a scheme `S` in a big fppf site and `𝒜` a sheaf of commutative
`𝒪_X`-algebras. A morphism of `𝒪_X`-algebras `ε : 𝒜 ⟶ 𝒪_X` gives a section of the relative
spectrum `\underline{Spec}_X(𝒜) ⟶ X`: a point `x ∈ X(T)` goes to the pair `(x, α)` with
`α : 𝒜 ⟶ 𝒪_X ⟶ x_* 𝒪_T` the composite of `ε` with the structure map of the direct image.

For the vector bundle `p : E = \underline{Spec}_W(Sym(ℰ)) ⟶ W` of a finite locally free
`𝒪_W`-module `ℰ`, the augmentation `Sym(ℰ) ⟶ 𝒪_W` which kills `ℰ`, that is, which maps
`Symⁿ(ℰ)` to zero for all `n > 0`, gives the *zero section* `o : W ⟶ E`, with `p ∘ o = id_W`.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecSection`: the section of the relative spectrum given by a
  morphism of algebras `𝒜 ⟶ 𝒪_X`.
* `AlgebraicGeometry.Space.vectorBundleAugmentation`: the augmentation `Sym(ℰ) ⟶ 𝒪_W`.
* `AlgebraicGeometry.Space.vectorBundleZeroSection`: the zero section `o : W ⟶ E`.
* `AlgebraicGeometry.Space.vectorBundleZeroLocus`: its image `o(W)`, as a closed subspace of `E`.

## Main results

* `AlgebraicGeometry.Space.relativeSpecSection_comp_π`: a section of the relative spectrum is a
  section of its projection.
* `AlgebraicGeometry.Space.vectorBundleAugmentation_ungradedIncl_gen`: the augmentation vanishes
  on `ℰ`.
* `AlgebraicGeometry.Space.vectorBundleZeroSection_comp_projection`: `p ∘ o = id_W`.
* `AlgebraicGeometry.Space.isClosedImmersion_vectorBundleZeroSection`: `o` is a closed immersion,
  being a section of the affine, hence separated, projection (Stacks 03KP).

## References

* [Stacks Project, Tag 0ERH](https://stacks.math.columbia.edu/tag/0ERH)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections of a relative spectrum -/

section RelativeSpecSection

variable {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
  (ε : A ⟶ unitAlgebra B S hS X)

/-- The morphism of algebras `𝒜 ⟶ 𝒪_X ⟶ P_* 𝒪_P` given by `ε : 𝒜 ⟶ 𝒪_X`, into the direct image
of the structure sheaf of an algebraic space `P` over `X`. -/
def augmentationPushforwardAlgebraHom (P : Over X) : A ⟶ pushforwardAlgebra B S hS P :=
  ε ≫ unitAlgebraHom B S hS X _

/-- The morphisms `augmentationPushforwardAlgebraHom` are compatible with the maps of direct
images. -/
theorem compPushforwardAlgebraMap_augmentationPushforwardAlgebraHom {P Q : Over X} (f : Q ⟶ P) :
    compPushforwardAlgebraMap B S hS (augmentationPushforwardAlgebraHom B S hS A ε P) f =
      augmentationPushforwardAlgebraHom B S hS A ε Q := by
  rw [compPushforwardAlgebraMap_def, augmentationPushforwardAlgebraHom,
    augmentationPushforwardAlgebraHom, Category.assoc]
  congr 1
  exact AlgebraSheaf.Hom.ext
    ((unitAlgebra_hom_right B S hS _).trans (unitAlgebra_hom_right B S hS _).symm)

/-- The point of the relative spectrum over a point `x ∈ X(T)` given by `ε : 𝒜 ⟶ 𝒪_X`: the
morphism of algebras `𝒜 ⟶ 𝒪_X ⟶ x_* 𝒪_T`. -/
def relativeSpecSectionPoint (T : BigFppfOver B S hS) (x : X.1.obj (op T)) :
    RelativeSpecPoint B S hS A T :=
  ⟨x, augmentationPushforwardAlgebraHom B S hS A ε (specPointOver B S hS T x)⟩

/-- The points `relativeSpecSectionPoint` are compatible with pullback along `g : T' ⟶ T`: the
pullback of the point over `x` is the point over the restriction of `x` to `T'`. -/
theorem relativeSpecSectionPoint_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : X.1.obj (op T)) :
    (relativeSpecSectionPoint B S hS A ε T x).map B S hS g =
      relativeSpecSectionPoint B S hS A ε T' (X.1.map g.op x) := by
  rw [relativeSpecSectionPoint, RelativeSpecPoint.map_mk,
    compPushforwardAlgebraMap_augmentationPushforwardAlgebraHom]
  rfl

/-- **The section of the relative spectrum `\underline{Spec}_X(𝒜) ⟶ X` given by a morphism of
`𝒪_X`-algebras `ε : 𝒜 ⟶ 𝒪_X`.** -/
def relativeSpecSection : X.1 ⟶ relativeSpecPoints B S hS A where
  app T := ↾fun x => (relativeSpecPointsEquiv B S hS A T.unop).symm
    (relativeSpecSectionPoint B S hS A ε T.unop x)
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (relativeSpecPointsEquiv B S hS A T'.unop).injective
    change relativeSpecPointsEquiv B S hS A T'.unop
        ((relativeSpecPointsEquiv B S hS A T'.unop).symm
          (relativeSpecSectionPoint B S hS A ε T'.unop (X.1.map g x))) =
      relativeSpecPointsEquiv B S hS A T'.unop ((relativeSpecPoints B S hS A).map g.unop.op
        ((relativeSpecPointsEquiv B S hS A T.unop).symm
          (relativeSpecSectionPoint B S hS A ε T.unop x)))
    rw [relativeSpecPointsEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      relativeSpecSectionPoint_map]
    rfl

/-- Under `relativeSpecPointsEquiv`, the section `relativeSpecSection` takes a point `x ∈ X(T)`
to the point `relativeSpecSectionPoint` over `x`. -/
theorem relativeSpecPointsEquiv_relativeSpecSection_app (T : BigFppfOver B S hS)
    (x : X.1.obj (op T)) :
    relativeSpecPointsEquiv B S hS A T ((relativeSpecSection B S hS A ε).app (op T) x) =
      relativeSpecSectionPoint B S hS A ε T x :=
  Equiv.apply_symm_apply _ _

/-- **A section of the relative spectrum is a section of its projection.** -/
@[reassoc (attr := simp)]
theorem relativeSpecSection_comp_π :
    relativeSpecSection B S hS A ε ≫ relativeSpecPointsπ B S hS A = 𝟙 X.1 := by
  ext T x
  show (relativeSpecPointsEquiv B S hS A T.unop
    ((relativeSpecSection B S hS A ε).app T x)).pt = x
  rw [relativeSpecPointsEquiv_relativeSpecSection_app]
  rfl

end RelativeSpecSection

/-! ### The zero section of a vector bundle -/

variable (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- The zero morphism of `𝒪_W`-modules `ℰ ⟶ 𝒪_W`. -/
abbrev zeroToUnitAlgebra : F ⟶ AlgebraSheaf.underlyingModule (unitAlgebra B S hS W) :=
  ⟨0⟩

/-- **The augmentation `Sym(ℰ) ⟶ 𝒪_W`**: the morphism of `𝒪_W`-algebras which vanishes on `ℰ`, so
on `Symⁿ(ℰ)` for every `n > 0`. -/
def vectorBundleAugmentation : symmetricAlgebraSheaf B S hS W F ⟶ unitAlgebra B S hS W :=
  SymAlgSheaf.algebraLift B S hS W (unitAlgebra B S hS W) F (zeroToUnitAlgebra B S hS W F)

/-- **The augmentation vanishes on `ℰ`**: it takes the value `0` on the image in `Sym(ℰ)` of a
local section of `ℰ`. -/
theorem vectorBundleAugmentation_ungradedIncl_gen (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : F.val.obj V) :
    ((vectorBundleAugmentation B S hS W F).right.hom.app V).hom
        ((symmetricAlgebra B S hS W F).ungradedIncl 1
          ((symmetricAlgebraGen B S hS W F).val.app V s)) = 0 :=
  (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS W (unitAlgebra B S hS W) F
    (zeroToUnitAlgebra B S hS W F) V s).trans (by
      simp only [PresheafOfModules.zero_app, ModuleCat.hom_zero, LinearMap.zero_apply]
      rfl)

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]

/-- **The zero section `o : W ⟶ E` of the vector bundle**, the section of
`E = \underline{Spec}_W(Sym(ℰ))` corresponding to the augmentation `Sym(ℰ) ⟶ 𝒪_W`. -/
def vectorBundleZeroSection : W ⟶ (vectorBundle B S hS W F).obj.left :=
  ObjectProperty.homMk
    (relativeSpecSection B S hS (symmetricAlgebraSheaf B S hS W F)
      (vectorBundleAugmentation B S hS W F))

/-- **The zero section is a section of the projection**: `p ∘ o = id_W`. -/
@[reassoc (attr := simp)]
theorem vectorBundleZeroSection_comp_projection :
    vectorBundleZeroSection B S hS W F ≫ vectorBundleProjection B S hS W F = 𝟙 W :=
  ObjectProperty.hom_ext _
    (relativeSpecSection_comp_π B S hS (symmetricAlgebraSheaf B S hS W F)
      (vectorBundleAugmentation B S hS W F))

/-- **The zero section is a closed immersion**: it is a section of the projection, which is
affine and hence separated (Stacks 03KP, part (3)). -/
theorem isClosedImmersion_vectorBundleZeroSection :
    IsClosedImmersion B S hS (vectorBundleZeroSection B S hS W F).hom :=
  isClosedImmersion_of_isSeparated_of_section B S hS (vectorBundleProjection B S hS W F).hom
    (isSeparated_of_isAffineHom B S hS _ (vectorBundle B S hS W F).obj.left.2 W.2
      (isAffineHom_vectorBundleProjection B S hS W F)) _
    (congrArg (fun f => f.hom) (vectorBundleZeroSection_comp_projection B S hS W F))

/-- **The zero locus `o(W) ⊆ E`**, the image of the zero section, as a closed subspace of the
vector bundle. -/
def vectorBundleZeroLocus : ClosedSubspaces B S hS (vectorBundle B S hS W F).obj.left.1 :=
  ⟨Subfunctor.range (vectorBundleZeroSection B S hS W F).hom,
    isClosedSubspace_range_of_isClosedImmersion B S hS _ W.2
      (isClosedImmersion_vectorBundleZeroSection B S hS W F)⟩

end AlgebraicGeometry.Space

end
