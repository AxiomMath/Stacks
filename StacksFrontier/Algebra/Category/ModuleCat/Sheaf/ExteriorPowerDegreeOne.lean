module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction

/-!
# The degree-one exterior power of a sheaf of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`, let `F` be a sheaf of `O`-modules
and let `⋀(F)` be an exterior algebra of `F` in the sense of Stacks Section 17.21. The exterior
algebra is the quotient of the tensor algebra by an ideal generated in degree two, so nothing is
divided out in degree one: `⋀¹ F` is `F` itself, and the degree-one generator `F ⟶ ⋀¹ F` is the
identification. This file proves that, in the form `F ≅ ⋀¹ F` together with the invertibility of
the generator, for *every* exterior algebra of `F` — in particular for the exterior algebra of
any `SheafOfModules.TensorExteriorSymmetricAlgebras` bundle on `F`.

The universal property of the exterior algebra is initiality among graded algebras with a
square-zero degree-one generator, and initiality by itself says nothing about the degree-one
piece: a degree-one generator can be compared with another one only through a second exterior
algebra. The route is therefore to establish the identification for one exterior algebra and
transport it. The sectionwise exterior algebra `U ↦ ⋀_{O(U)}(F(U))` has the identification on the
nose, because the degree-one part of `ExteriorAlgebra R M` is the range of
`ExteriorAlgebra.ι R`, on which that map is injective; sheafification carries it to the exterior
algebra `⋀(F)` built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction`, and the
degreewise comparison of two exterior algebras of `F` carries it from there to any other.

## Main definitions

* `PresheafOfModules.exteriorAlgebraGenIso`: the degree-one generator of the sectionwise exterior
  algebra of a presheaf of modules, as an isomorphism of presheaves of modules.
* `SheafOfModules.sheafifiedExteriorPieceOneIso` and
  `SheafOfModules.sheafifiedExteriorGeneratorIso`: the degree-one identification of the
  sheafified sectionwise exterior algebra, in both directions.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorGeneratorIso`: **`F ≅ ⋀¹ F`**, the
  degree-one exterior power of a sheaf of modules is the sheaf itself, identified with the
  degree-one generator by `exteriorGeneratorIso_hom`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerOneIso`: the same statement with
  the degree-one piece spelled as the exterior power `⋀¹ F`.

## Main results

* `PresheafOfModules.exteriorAlgebraGen_injective` and `exteriorAlgebraGen_surjective`: on the
  sections over each object, the degree-one generator of the sectionwise exterior algebra is
  injective and its image is the whole degree-one piece.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_gen`: **the degree-one generator of any
  exterior algebra of `F` is an isomorphism.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isIso_exteriorGenerator`: the same for the
  exterior algebra of a bundle.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorGeneratorIso_exteriorAlgebraIso`: under
  the degree-one identifications, the canonical comparison of the exterior algebras of two
  bundles on `F` is the identity of `F`.

## Implementation notes

There is no route through the tensor algebra here, in contrast with the symmetric case: the
symmetric algebra of `F` can be recognized as the tensor algebra of `F` as soon as the degree-one
sections of the latter commute (`SheafOfModules.GradedAlgebra.IsTensorAlgebra.isSymmetricAlgebra`),
and then the degree-one identification `T¹ F ≅ F` carried by the bundle transports to it; the
degree-one generator of a tensor algebra never squares to zero, so the exterior algebra is not a
tensor algebra and the degree-one identification has to come from the construction instead.

Invertibility of the generator is stated as the isomorphism `F ≅ ⋀¹ F` whose forward map *is*
the generator (`exteriorGeneratorIso_hom`, a definitional identity), rather than as an `IsIso`
instance; `isIso_exteriorGenerator` is the `IsIso` form, obtained from it.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe v u w a

namespace PresheafOfModules

/-! ### The degree-one piece of the sectionwise exterior algebra -/

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The degree-one generator of the sectionwise exterior algebra is injective on sections: a
local section of `F` is determined by its degree-one image. -/
theorem exteriorAlgebraGen_injective (X : Cᵒᵖ) :
    Function.Injective (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X) := fun m m' h =>
  (ExteriorAlgebra.ι_inj ((O ⋙ forget₂ _ RingCat).obj X) m m').1
    (congrArg (exteriorAlgebraPieceVal 1 F X) h)

/-- The degree-one piece of the sectionwise exterior algebra is the range of the degree-one
generator: the first exterior power of a module is the range of `ExteriorAlgebra.ι`. -/
theorem mem_range_ι_of_exteriorAlgebraPieceVal_one (X : Cᵒᵖ)
    (z : (exteriorAlgebraPiece 1 F).obj X) :
    exteriorAlgebraPieceVal 1 F X z ∈
      LinearMap.range (ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) :
        F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] _) :=
  ExteriorAlgebra.intPiece_one ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) ▸
    (z : ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) 1)).2

/-- The degree-one generator of the sectionwise exterior algebra is surjective on sections. -/
theorem exteriorAlgebraGen_surjective (X : Cᵒᵖ) :
    Function.Surjective (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X) := fun z => by
  obtain ⟨m, hm⟩ := mem_range_ι_of_exteriorAlgebraPieceVal_one F X z
  exact ⟨m, exteriorAlgebraPieceVal_injective 1 F X hm⟩

/-- The degree-one generator, as a linear equivalence onto the degree-one piece over each object
of the site: `⋀¹_{O(X)}(F(X))` is `F(X)`. -/
noncomputable def exteriorAlgebraGenEquiv (X : Cᵒᵖ) :
    F.obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X] (exteriorAlgebraPiece 1 F).obj X :=
  LinearEquiv.ofBijective ((exteriorAlgebraGen F).app X).hom
    ⟨exteriorAlgebraGen_injective F X, exteriorAlgebraGen_surjective F X⟩

/-- **The degree-one generator of the sectionwise exterior algebra is an isomorphism**: the
degree-one piece of `⋀_{O(U)}(F(U))` is `F(U)`, naturally in `U`. -/
noncomputable def exteriorAlgebraGenIso : F ≅ exteriorAlgebraPiece 1 F := by
  have hiso : ∀ X : Cᵒᵖ, IsIso ((exteriorAlgebraGen F).app X) := fun X =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨exteriorAlgebraGen_injective F X, exteriorAlgebraGen_surjective F X⟩
  refine isoMk (fun X => asIso ((exteriorAlgebraGen F).app X)) ?_
  intro X Y f
  exact (exteriorAlgebraGen F).naturality f

/-- `PresheafOfModules.exteriorAlgebraGenIso` is the degree-one generator. -/
@[simp]
theorem exteriorAlgebraGenIso_hom : (exteriorAlgebraGenIso F).hom = exteriorAlgebraGen F := rfl

end Sectionwise

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-! ### The degree-one piece of the constructed exterior algebra -/

/-- **The degree-one identification** `⋀¹(F) ≅ F` for the exterior algebra `⋀(F)` built as the
degreewise sheafification of the sectionwise exterior algebra: the sectionwise degree-one
generator is an isomorphism, and the sheafification of `F.val` is `F`. -/
noncomputable def sheafifiedExteriorPieceOneIso :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (exteriorAlgebraPiece (1 : ℤ) F.val) ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (exteriorAlgebraGenIso F.val).symm ≪≫
    sheafifiedValIso J F

/-- The degree-one identification of `⋀(F)`, read as an isomorphism onto the degree-one piece. -/
noncomputable def sheafifiedExteriorGeneratorIso :
    F ≅ (sheafifiedExteriorAlgebra J F).piece 1 :=
  (sheafifiedExteriorPieceOneIso J F).symm

/-- The degree-one identification of `⋀(F)` is its degree-one generator. -/
theorem sheafifiedExteriorGeneratorIso_hom :
    (sheafifiedExteriorGeneratorIso J F).hom = sheafifiedExteriorGenerator J F := rfl

/-- The degree-one identification of `⋀(F)`, followed by the comparison of degree-one pieces with
any exterior algebra of `F`, is the generator of that exterior algebra. -/
private theorem generatorIso_hom_comp_pieceIso_hom {A : GradedAlgebra.{w, w} (toRingCat J Osharp)}
    {ι : F ⟶ A.piece 1} (hA : GradedAlgebra.IsExteriorAlgebra A ι) :
    (sheafifiedExteriorGeneratorIso J F).hom ≫
      ((isExteriorAlgebra_sheafifiedExteriorAlgebra J F).pieceIso hA 1).hom = ι := by
  rw [sheafifiedExteriorGeneratorIso_hom]
  exact GradedAlgebra.IsExteriorAlgebra.pieceIso_generator _ hA

namespace GradedAlgebra

/-- **The degree-one generator of an exterior algebra of `F` is an isomorphism**: the degree-one
exterior power of a sheaf of modules is the sheaf itself. -/
theorem IsExteriorAlgebra.isIso_gen {A : GradedAlgebra.{w, w} (toRingCat J Osharp)}
    {ι : F ⟶ A.piece 1} (hA : IsExteriorAlgebra A ι) : IsIso ι := by
  rw [← generatorIso_hom_comp_pieceIso_hom J F hA]
  infer_instance

end GradedAlgebra

namespace TensorExteriorSymmetricAlgebras

variable {J F} (A : TensorExteriorSymmetricAlgebras J F)

/-- **`F ≅ ⋀¹ F`**: the degree-one exterior power of a sheaf of modules is the sheaf itself, and
the identification is the degree-one generator of the exterior algebra. -/
noncomputable def exteriorGeneratorIso : F ≅ A.exterior.piece 1 :=
  sheafifiedExteriorGeneratorIso J F ≪≫
    (isExteriorAlgebra_sheafifiedExteriorAlgebra J F).pieceIso A.exterior_isExteriorAlgebra 1

/-- The identification of `F` with the degree-one exterior power is the degree-one generator of
the exterior algebra. -/
theorem exteriorGeneratorIso_hom : A.exteriorGeneratorIso.hom = A.exteriorGenerator := by
  exact generatorIso_hom_comp_pieceIso_hom J F A.exterior_isExteriorAlgebra

/-- **The degree-one generator of the exterior algebra of a bundle is an isomorphism.** -/
theorem isIso_exteriorGenerator : IsIso A.exteriorGenerator := by
  rw [← A.exteriorGeneratorIso_hom]
  infer_instance

/-- **`⋀¹ F ≅ F`**, with the degree-one piece spelled as the exterior power. -/
noncomputable def exteriorPowerOneIso : A.exteriorPower 1 ≅ F :=
  A.exteriorGeneratorIso.symm

/-- Under the degree-one identifications, the canonical comparison of the exterior algebras of
two bundles on `F` is the identity of `F`: both degree-one pieces are `F`, by generators that
the comparison matches. -/
theorem exteriorGeneratorIso_exteriorAlgebraIso (B : TensorExteriorSymmetricAlgebras J F) :
    A.exteriorGeneratorIso ≪≫ exteriorAlgebraIso A B 1 = B.exteriorGeneratorIso :=
  Iso.ext (by
    rw [show (A.exteriorGeneratorIso ≪≫ exteriorAlgebraIso A B 1).hom =
      A.exteriorGeneratorIso.hom ≫ (exteriorAlgebraIso A B 1).hom from rfl,
      A.exteriorGeneratorIso_hom, B.exteriorGeneratorIso_hom]
    exact exteriorAlgebraIso_generator A B)

end TensorExteriorSymmetricAlgebras

end SheafOfModules

end
