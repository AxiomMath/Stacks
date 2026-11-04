module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.RegularSectionSequence.Basic
import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist

/-!
# Multiplication by a global section of the hyperplane sheaf on projective space

Let `S` be a scheme, let `ℱ` be an `𝒪`-module on `ℙⁿ_S` and let `s` be a global section of the
hyperplane sheaf `𝒪(1)`. Multiplication by `s` is the morphism

`ℱ(d) = ℱ ⊗ 𝒪(d) ⟶ ℱ ⊗ 𝒪(d + 1) = ℱ(d + 1)`

obtained by tensoring `ℱ(d)` with `s : 𝒪 ⟶ 𝒪(1)` and multiplying the two twists of the structure
sheaf together. At `d = -1` the target is `ℱ ⊗ 𝒪(0) ≅ ℱ`, which gives the arrow `ℱ(-1) ⟶ ℱ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.sectionHom`: a global section of
  an `𝒪_X`-module as a morphism `𝒪_X ⟶ ℱ` from the structure sheaf.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`: the morphism
  `ℱ(d) ⟶ ℱ(d + 1)` of multiplication by `s`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMulNegOne`: the same
  morphism at `d = -1`, with its target identified with `ℱ`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistNegOneMulSection` and
  `twistNegOneTensorIso`: that morphism split as multiplication by `s` into `ℱ(-1) ⊗ 𝒪(1)`
  followed by the isomorphism `ℱ(-1) ⊗ 𝒪(1) ≅ ℱ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication` `.`
  `twistSectionMulNegOne_comp_hyperplaneUnit`: the composite `ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ` of
  [Stacks, Tag 08A0] vanishes, for every `ℱ`.
* `…isIso_unit_app_cokernel_twistSectionMulNegOne`: the unit of `i^* ⊣ i_*` is an isomorphism at
  the cokernel of `ℱ(-1) ⟶ ℱ`, for every `ℱ`. Both are read off the general statements of
  `StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean` through the
  splitting above.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso` is an isomorphism
`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` in all integer degrees and `twistZeroIsoUnit` is `𝒪(0) ≅ 𝒪`, both
unconditional on `ℙⁿ_S`; so neither invertibility of a multiplication map nor invertibility of a
comparison of `𝒪(0)` with `𝒪` is assumed here. The multiplication map of [Stacks, Tag 03GJ] is
stated on `Proj S`, and `ℙⁿ_S` is a base change of `Proj ℤ[T]` rather than a `Proj`, so it does
not apply at this spelling.

The unitors and the associator are taken in the `Stacks.SheafOfModules.TensorSheafification`
spelling, which is the one `Stacks.RelativeVeryAmple.tensorModules` and hence `twistOverMulIso`
use; functoriality of the tensor product is read off the bifunctor
`Stacks.RingedSpace.tensorSheaf`, which is where `tensorModules` gets its own functoriality. The
two functoriality steps are separate declarations with both of the bifunctor's object arguments
given explicitly: left to inference, the pair of morphisms is elaborated against the composite's
expected type and unification between the two spellings of the tensor product exhausts the
heartbeat budget.

## References

* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A global section of an `𝒪_X`-module, read as a morphism `𝒪_X ⟶ ℱ` from the structure
sheaf. -/
def sectionHom {X : Scheme.{u}} (F : X.Modules) (s : F.sections) :
    SheafOfModules.unit X.ringCatSheaf ⟶ F :=
  F.unitHomEquiv.symm s

variable (n : ℕ) (S : Scheme.{u})

/-- **The uncurried bifunctor at a morphism whose first component is an identity is the
fixed-first-argument functor at the second component.** Pure functoriality, stated for an
arbitrary bifunctor: the two tensor spellings below differ by exactly this step, and proving it
once in this generality keeps the identity out of the unifier, which cannot discharge it on the
sheaf tensor product without unfolding sheafification. -/
private theorem uncurry_map_id_left {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) (A : C) {B B' : D} (g : B ⟶ B') :
    (Functor.uncurry.obj F).map ((𝟙 A, g) : ((A, B) : C × D) ⟶ (A, B')) = (F.obj A).map g := by
  rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- Tensoring a module with a morphism of modules out of the structure sheaf, on the right. -/
def tensorRightOfUnitHom (A : (projectiveSpaceOver n S).Modules)
    {B : (projectiveSpaceOver n S).Modules}
    (f : SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf ⟶ B) :
    tensorModules (projectiveSpaceOver n S) A
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) ⟶
      tensorModules (projectiveSpaceOver n S) A B :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(((projectiveSpaceOver n S).toRingedSpace)).presheaf,
        (((projectiveSpaceOver n S).toRingedSpace)).IsSheaf⟩))).map
    (X := (A, SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)) (Y := (A, B))
    (𝟙 A, f)

/-- Tensoring a module with a morphism of modules, on the right. -/
def tensorRightOfHom (A : (projectiveSpaceOver n S).Modules)
    {B C : (projectiveSpaceOver n S).Modules} (f : B ⟶ C) :
    tensorModules (projectiveSpaceOver n S) A B ⟶ tensorModules (projectiveSpaceOver n S) A C :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(((projectiveSpaceOver n S).toRingedSpace)).presheaf,
        (((projectiveSpaceOver n S).toRingedSpace)).IsSheaf⟩))).map
    (X := (A, B)) (Y := (A, C)) (𝟙 A, f)

/-- **`tensorRightOfUnitHom` is the native tensor bifunctor with its first argument fixed.** This
is `uncurry_map_id_left`; it is the one step by which this spelling differs from the whiskering of
the tensor product, and the goals below are stated on the right-hand side so that the difference
is never put to the unifier. -/
theorem tensorRightOfUnitHom_eq_map (A : (projectiveSpaceOver n S).Modules)
    {B : (projectiveSpaceOver n S).Modules}
    (f : SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf ⟶ B) :
    tensorRightOfUnitHom n S A f =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((projectiveSpaceOver n S).toRingedSpace)).presheaf,
          (((projectiveSpaceOver n S).toRingedSpace)).IsSheaf⟩).obj A).map f :=
  uncurry_map_id_left _ A f

/-- **`tensorRightOfHom` is the native tensor bifunctor with its first argument fixed**, the
general-morphism companion of `tensorRightOfUnitHom_eq_map`. -/
theorem tensorRightOfHom_eq_map (A : (projectiveSpaceOver n S).Modules)
    {B C : (projectiveSpaceOver n S).Modules} (f : B ⟶ C) :
    tensorRightOfHom n S A f =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((projectiveSpaceOver n S).toRingedSpace)).presheaf,
          (((projectiveSpaceOver n S).toRingedSpace)).IsSheaf⟩).obj A).map f :=
  uncurry_map_id_left _ A f

/-- **Multiplication by a global section `s` of `𝒪(1)` on a twisted module over `ℙⁿ_S`**: the
morphism `ℱ ⊗ 𝒪(d) ⟶ ℱ ⊗ 𝒪(d + 1)` which tensors with `s : 𝒪 ⟶ 𝒪(1)` and then multiplies the
two twists of the structure sheaf together. -/
def twistSectionMul (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ⟶
      tensorModules (projectiveSpaceOver n S) F (twistOver n S (d + 1)) :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))).inv ≫
    tensorRightOfUnitHom n S (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
      (sectionHom (twistOver n S 1) s) ≫
    (Stacks.SheafOfModules.Invertible.tensorProductAssociator
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      F (twistOver n S d) (twistOver n S 1)).hom ≫
    tensorRightOfHom n S F (twistOverMulIso n S d 1).hom

/-- **Multiplication by a global section `s` of `𝒪(1)`, as an arrow `ℱ(-1) ⟶ ℱ`.** This is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul` at `d = -1`,
followed by the identifications `ℱ ⊗ 𝒪(0) ≅ ℱ ⊗ 𝒪 ≅ ℱ`. -/
def twistSectionMulNegOne (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)) ⟶ F :=
  twistSectionMul n S F s (-1) ≫
    tensorRightOfHom n S F
      (eqToHom (congrArg (twistOver n S) (show (-1 : ℤ) + 1 = 0 from by ring)) ≫
        (twistZeroIsoUnit n S).hom) ≫
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property F).hom

/-! ### The hyperplane cut out by a section, and the sequence of [Stacks, Tag 08A0] -/

/-- **Every twist on `ℙⁿ_S` is invertible**, at the spelling the zero-scheme API of Chapter 31
asks for: `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver` writes the
structure presheaf as `X.presheaf` and its sheaf condition as
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X`, and instance search does not unfold
either into `X.sheaf.obj` and `X.ringCatSheaf.property`. -/
instance isInvertible_twistOver (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveSpaceOver n S).sheaf.obj
      (projectiveSpaceOver n S).ringCatSheaf.property (twistOver n S d) :=
  isInvertibleModule_twistOver n S d

/-- **The hyperplane `H = V(s)` of a global section `s` of `𝒪(1)` on `ℙⁿ_S`**: the zero scheme of
`s`, as quasi-coherent ideal-sheaf data. -/
abbrev hyperplane (s : (twistOver n S 1).sections) : (projectiveSpaceOver n S).IdealSheafData :=
  AlgebraicGeometry.zeroScheme (projectiveSpaceOver n S) (twistOver n S 1)
    (s.eval (Opposite.op ⊤))

/-- The closed immersion `i : H ⟶ ℙⁿ_S` of the hyperplane cut out by `s`. -/
abbrev hyperplaneι (s : (twistOver n S 1).sections) :
    (hyperplane n S s).subscheme ⟶ projectiveSpaceOver n S :=
  (hyperplane n S s).subschemeι

/-- **The last arrow of [Stacks, Tag 08A0]'s sequence**, `ℱ ⟶ i_* i^* ℱ`: the unit of the
pullback–pushforward adjunction along the inclusion of the hyperplane cut out by `s`. -/
abbrev hyperplaneUnit (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    F ⟶ (Scheme.Modules.pushforward (hyperplaneι n S s)).obj
      ((Scheme.Modules.pullback (hyperplaneι n S s)).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app F

/-! ### Multiplication by `s` on `ℱ(-1)`, factored through `ℱ(-1) ⊗ 𝒪(1)` -/

/-- A composite of four arrows followed by a composite of two is the first two followed by the
last four; pure associativity, isolated as a lemma because the factors below mention two
spellings of the sheaf of rings and are not type-correct at the transparency `rw` works at. -/
private theorem assocFourTwo {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) :
    (a ≫ b ≫ c ≫ d) ≫ e ≫ f = (a ≫ b) ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

/-- A unit of an adjunction that is an isomorphism at one object is an isomorphism at every
isomorphic object: naturality of the unit writes the second component as the first conjugated by
the isomorphism and by its image under the right adjoint. -/
theorem isIso_unit_app_of_isoSource {C D : Type*} [Category C] [Category D]
    {Fun : C ⥤ D} {G : D ⥤ C} (adj : Fun ⊣ G) {A B : C} (e : A ≅ B)
    (h : IsIso (adj.unit.app A)) : IsIso (adj.unit.app B) := by
  have heq : adj.unit.app B = e.inv ≫ adj.unit.app A ≫ G.map (Fun.map e.hom) := by
    rw [adj.unit_naturality e.hom, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance


/-- **Multiplication by `s` on `ℱ(-1)`, before the twists are multiplied together**: the arrow
`ℱ(-1) ⟶ ℱ(-1) ⊗ 𝒪(1)` which tensors `ℱ(-1)` with `s : 𝒪 ⟶ 𝒪(1)` on the right. This is the
first two factors of
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul` at `d = -1`. -/
def twistNegOneMulSection (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)) ⟶
      tensorModules (projectiveSpaceOver n S)
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))) (twistOver n S 1) :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))).inv ≫
    tensorRightOfUnitHom n S (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
      (sectionHom (twistOver n S 1) s)

/-- **Multiplication by `s` on `ℱ(-1)`, with its second factor in the native spelling.** This is
`twistNegOneMulSection` with `tensorRightOfUnitHom_eq_map` applied to its second factor. The
zero-scheme results of [Stacks, Tag 0C6K] are stated at this spelling, so stating the step here
rather than at `tensorRightOfUnitHom` is what keeps the identity of `uncurry_map_id_left` out of
the unifier when those results are applied. -/
theorem twistNegOneMulSection_eq_map (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    twistNegOneMulSection n S F s =
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
          (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(((projectiveSpaceOver n S).toRingedSpace)).presheaf,
              (((projectiveSpaceOver n S).toRingedSpace)).IsSheaf⟩).obj
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))).map
          (sectionHom (twistOver n S 1) s) :=
  congrArg
    (fun k => (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))).inv ≫ k)
    (tensorRightOfUnitHom_eq_map n S
      (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
      (sectionHom (twistOver n S 1) s))

/-- **The identification `(ℱ(-1)) ⊗ 𝒪(1) ≅ ℱ`**: reassociate the three factors, multiply
`𝒪(-1) ⊗ 𝒪(1)` to `𝒪(-1 + 1)`, read that as `𝒪(0) ≅ 𝒪` and cancel the structure sheaf. These
are the last four factors of
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMulNegOne`. -/
def twistNegOneTensorIso (F : (projectiveSpaceOver n S).Modules) :
    tensorModules (projectiveSpaceOver n S)
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))) (twistOver n S 1) ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorProductAssociator
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
      F (twistOver n S (-1)) (twistOver n S 1) ≪≫
    tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl F) (twistOverMulIso n S (-1) 1) ≪≫
    tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl F)
      (eqToIso (congrArg (twistOver n S) (show (-1 : ℤ) + 1 = 0 from by ring)) ≪≫
        twistZeroIsoUnit n S) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property F

/-- The underlying arrow of `twistNegOneTensorIso` is the four-fold composite that
`twistSectionMulNegOne` ends with, the functoriality isomorphism of the tensor product being
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.tensorRightOfHom` on the nose. -/
theorem hom_twistNegOneTensorIso (F : (projectiveSpaceOver n S).Modules) :
    (twistNegOneTensorIso n S F).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductAssociator
        (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
        F (twistOver n S (-1)) (twistOver n S 1)).hom ≫
      tensorRightOfHom n S F (twistOverMulIso n S (-1) 1).hom ≫
      tensorRightOfHom n S F
        (eqToHom (congrArg (twistOver n S) (show (-1 : ℤ) + 1 = 0 from by ring)) ≫
          (twistZeroIsoUnit n S).hom) ≫
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
        (projectiveSpaceOver n S).presheaf
        (projectiveSpaceOver n S).ringCatSheaf.property F).hom :=
  rfl

/-- **`ℱ(-1) ⟶ ℱ` is multiplication by `s` on `ℱ(-1)` followed by an isomorphism.** Both sides
are the same six-fold composite; only the bracketing differs. -/
theorem twistSectionMulNegOne_eq_comp (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    twistSectionMulNegOne n S F s
      = twistNegOneMulSection n S F s ≫ (twistNegOneTensorIso n S F).hom := by
  rw [hom_twistNegOneTensorIso]
  exact assocFourTwo _ _ _ _ _ _

/-- **The composite `ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ` of [Stacks, Tag 08A0] vanishes**, for an arbitrary
`𝒪`-module `ℱ` on `ℙⁿ_S`. Multiplication by `s` on `ℱ(-1)` lands in `ℱ(-1) ⊗ 𝒪(1)`, where the
vanishing is `AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero'`; the identification
of `ℱ(-1) ⊗ 𝒪(1)` with `ℱ` is carried across by naturality of the unit. -/
theorem twistSectionMulNegOne_comp_hyperplaneUnit (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0 := by
  have h0 : twistNegOneMulSection n S F s ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
        (tensorModules (projectiveSpaceOver n S)
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
          (twistOver n S 1)) = 0 := by
    rw [twistNegOneMulSection_eq_map]
    exact AlgebraicGeometry.tensorSection_comp_unit_zeroScheme_eq_zero' (projectiveSpaceOver n S)
      (twistOver n S 1) s (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
  rw [twistSectionMulNegOne_eq_comp, Category.assoc,
    ← (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit_naturality
      (twistNegOneTensorIso n S F).hom, ← Category.assoc, h0, Limits.zero_comp]

/-- **The unit of `i^* ⊣ i_*` is an isomorphism at the cokernel of `ℱ(-1) ⟶ ℱ`**, for an
arbitrary `𝒪`-module `ℱ` on `ℙⁿ_S`. That cokernel is the cokernel of multiplication by `s` into
`ℱ(-1) ⊗ 𝒪(1)`, where the assertion is
`AlgebraicGeometry.isIso_unit_app_cokernel_tensorSection'`; the identification of
`ℱ(-1) ⊗ 𝒪(1)` with `ℱ` is an isomorphism and so leaves the cokernel unchanged. -/
theorem isIso_unit_app_cokernel_twistSectionMulNegOne (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (Limits.cokernel (twistSectionMulNegOne n S F s))) := by
  have h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (Limits.cokernel (twistNegOneMulSection n S F s))) := by
    rw [twistNegOneMulSection_eq_map]
    exact AlgebraicGeometry.isIso_unit_app_cokernel_tensorSection' (projectiveSpaceOver n S)
      (twistOver n S 1) s (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
  exact isIso_unit_app_of_isoSource _
    ((Limits.cokernelCompIsIso (twistNegOneMulSection n S F s)
        (twistNegOneTensorIso n S F).hom).symm ≪≫
      Limits.cokernelIsoOfEq (twistSectionMulNegOne_eq_comp n S F s).symm) h

/-- **The restriction map `ℱ ⟶ i_* i^* ℱ` is the cokernel of multiplication by `s`**, on the two
inputs that the hyperplane is owed: that the composite vanishes, and that the unit is an
isomorphism at the cokernel — equivalently, that the cokernel is annihilated by the ideal sheaf of
the hyperplane, which is the essential-image half of [Stacks, Tag 08KS].

Both inputs hold for every `ℱ`, and are `…twistSectionMulNegOne_comp_hyperplaneUnit` and
`…isIso_unit_app_cokernel_twistSectionMulNegOne` above. -/
theorem exists_cokernelIso_hyperplaneUnit (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections)
    (hz : twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0)
    (hiso : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (Limits.cokernel (twistSectionMulNegOne n S F s)))) :
    ∃ e : Limits.cokernel (twistSectionMulNegOne n S F s) ≅
        (Scheme.Modules.pushforward (hyperplaneι n S s)).obj
          ((Scheme.Modules.pullback (hyperplaneι n S s)).obj F),
      Limits.cokernel.π (twistSectionMulNegOne n S F s) ≫ e.hom = hyperplaneUnit n S F s :=
  have := hiso
  AlgebraicGeometry.exists_cokernelIso_of_isIso_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s))
    (twistSectionMulNegOne n S F s) hz

/-- **The sequence of [Stacks, Tag 08A0], on its three named inputs.** For `s` a global section
of `𝒪(1)` on `ℙⁿ_S` and `i : H ⟶ ℙⁿ_S` the hyperplane it cuts out, the sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`

is short exact as soon as multiplication by `s` is a monomorphism, the composite vanishes, and
the unit of the adjunction is an isomorphism at the cokernel.

Two of the three inputs hold for every `ℱ` and are proved above:
`…twistSectionMulNegOne_comp_hyperplaneUnit` and
`…isIso_unit_app_cokernel_twistSectionMulNegOne`. Monicity is the one that is a genuine
condition on `s`, and it is where the hypothesis that the base field be infinite enters in the
source — it holds exactly when `H` contains no associated point of `ℱ`, and such an `s` exists
because the sections of `𝒪(1)` vanishing at a given point form a proper subspace and a finite
union of proper subspaces cannot cover a vector space over an infinite field. No
`@[stacks 08A0]` attribute is attached here: the sequence on its monicity hypothesis is
`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing`. -/
theorem shortExact_hyperplaneUnit (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) [Mono (twistSectionMulNegOne n S F s)]
    (hz : twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0)
    (hiso : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (Limits.cokernel (twistSectionMulNegOne n S F s)))) :
    ∃ h : twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0,
      (ShortComplex.mk (twistSectionMulNegOne n S F s) (hyperplaneUnit n S F s) h).ShortExact :=
  Stacks.RegularSectionSequence.shortExact_of_mono_of_exists_cokernelIso _ _
    (exists_cokernelIso_hyperplaneUnit n S F s hz hiso)

end Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

end
