module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.CategoryTheory.Sites.RingSheafDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionCommonRefinement

/-!
# Square-zero extensions with the same class are isomorphic (towards Stacks 0GPZ and 08UC)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. An
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension f G` is a square-zero
extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras, and it carries a class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` (**Stacks 0GQ0**).
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom`
says a morphism of extensions forces the two classes to agree. This file proves the converse:
two extensions with the same class admit a morphism of extensions between them, as soon as the
identification of the square-zero ideal of the target with `𝒢` is bijective on sections, which
is what makes it an *extension* of `𝒪_X` by `𝒢`.

The proof is Step 3 of the proof of **Stacks 08U8**, read over the common refinement
`ℰ = 𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` of the two extensions. Write `a : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₁}` and
`b : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₂}` for the two algebra maps. Equality of the classes says that the
difference homomorphism `δ : ℐ/ℐ² ⟶ 𝒢` of the two extensions over `ℰ` has vanishing class, so
it factors as `θ ∘ d` through the degree `0` term of `𝖭𝖫(α)`. Then `b + θ ∘ d` is again a
homomorphism of sheaves of rings, it kills the kernel of `a`, and its descent along the locally
surjective `a` is the morphism of extensions.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.idealIncl`: for an
  extension whose ideal identification is bijective, the inclusion `𝒢 ⟶ 𝒪_{X'}` on sections.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.twistHom`: the twisted
  homomorphism `b + θ ∘ d : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₂}` of sheaves of rings.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.exists_hom_of_extClass_eq`:
  **two square-zero extensions with the same class admit a morphism of extensions** from the
  first to the second, compatible with the `f⁻¹𝒪_S`-algebra structures, the reductions and the
  identifications of the ideals with `𝒢`.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.extClass_eq_iff_exists_hom`:
  together with `extClass_eq_extClass_of_hom`, the classes agree exactly when such a morphism
  exists.

## Implementation notes

The bijectivity hypothesis is on the *target* only, and it cannot be dropped:
`AlgebraSquareZeroExtension.ideal` is an arbitrary natural family of maps from the square-zero
ideal to `𝒢`, and with the zero family on the target and the trivial extension as the source both
classes vanish while no compatible morphism exists. For a genuine extension of `𝒪_X` by `𝒢` the
identification is an isomorphism, so the hypothesis is part of the data.

The descent along `a` is `Stacks.Sites.RingDescent.desc`. The derivation `θ ∘ d` is read on
sections through `Stacks.Sites.Conormal.tensorDifferential`, the local section `1 ⊗ d p` of the
degree `0` term of `𝖭𝖫(α)`, whose derivation rules are
`Stacks.Sites.Conormal.tensorDifferential_add`, `tensorDifferential_mul` and
`tensorDifferential_coefficient`.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable freeAlgebraSheafDesc
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

namespace AlgebraSquareZeroExtension

/-! ### The inclusion of `𝒢` into an extension with bijective ideal identification -/

section Incl

variable (P : AlgebraSquareZeroExtension f G)
  (hP : ∀ U, Function.Bijective (P.ideal.app U))

/-- The inclusion `𝒢(U) ⟶ 𝒪_{X'}(U)` of an extension whose identification of the square-zero
ideal with `𝒢` is bijective: the inverse of that identification, followed by the inclusion of
the ideal. -/
def idealIncl (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) : P.sheaf.obj.obj U :=
  ((Equiv.ofBijective _ (hP U)).symm g : ↥(kernelIdeal P.reduction.hom U))

/-- The inclusion of `𝒢` lands in the square-zero ideal. -/
theorem idealIncl_mem (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) :
    P.idealIncl hP U g ∈ kernelIdeal P.reduction.hom U :=
  ((Equiv.ofBijective _ (hP U)).symm g).2

/-- The inclusion of `𝒢` is a section of the identification of the ideal with `𝒢`. -/
theorem ideal_idealIncl (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) :
    P.ideal.app U ⟨P.idealIncl hP U g, P.idealIncl_mem hP U g⟩ = g :=
  (Equiv.ofBijective _ (hP U)).apply_symm_apply g

/-- The inclusion of `𝒢` is a retraction of the identification of the ideal with `𝒢`. -/
theorem idealIncl_ideal (U : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom U)) :
    P.idealIncl hP U (P.ideal.app U y) = y :=
  congrArg Subtype.val ((Equiv.ofBijective _ (hP U)).symm_apply_apply y)

/-- A section of the square-zero ideal is the inclusion of its image in `𝒢`. -/
theorem idealIncl_eq_of_ideal_eq (U : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal P.reduction.hom U)) (g : G.val.obj U) (h : P.ideal.app U y = g) :
    P.idealIncl hP U g = y := by
  rw [← h]
  exact P.idealIncl_ideal hP U y

/-- The inclusion of `𝒢` lands in the kernel of the reduction. -/
theorem reduction_idealIncl (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) :
    (P.reduction.hom.app U).hom (P.idealIncl hP U g) = 0 :=
  P.idealIncl_mem hP U g

/-- The inclusion of `𝒢` is additive. -/
theorem idealIncl_add (U : (Opens X.carrier)ᵒᵖ) (g h : G.val.obj U) :
    P.idealIncl hP U (g + h) = P.idealIncl hP U g + P.idealIncl hP U h :=
  P.idealIncl_eq_of_ideal_eq hP U
    (⟨P.idealIncl hP U g, P.idealIncl_mem hP U g⟩ + ⟨P.idealIncl hP U h, P.idealIncl_mem hP U h⟩)
    (g + h) (by rw [map_add, P.ideal_idealIncl, P.ideal_idealIncl])

/-- The inclusion of `𝒢` sends `0` to `0`. -/
theorem idealIncl_zero (U : (Opens X.carrier)ᵒᵖ) : P.idealIncl hP U 0 = 0 :=
  P.idealIncl_eq_of_ideal_eq hP U 0 0 (map_zero _)

/-- The inclusion of `𝒢` commutes with subtraction. -/
theorem idealIncl_sub (U : (Opens X.carrier)ᵒᵖ) (g h : G.val.obj U) :
    P.idealIncl hP U (g - h) = P.idealIncl hP U g - P.idealIncl hP U h :=
  P.idealIncl_eq_of_ideal_eq hP U
    (⟨P.idealIncl hP U g, P.idealIncl_mem hP U g⟩ - ⟨P.idealIncl hP U h, P.idealIncl_mem hP U h⟩)
    (g - h) (by rw [map_sub, P.ideal_idealIncl, P.ideal_idealIncl])

/-- The inclusion of `𝒢` commutes with the restriction maps. -/
theorem idealIncl_map {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V) (g : G.val.obj U) :
    P.idealIncl hP V (G.val.map k g) = (P.sheaf.obj.map k).hom (P.idealIncl hP U g) := by
  refine P.idealIncl_eq_of_ideal_eq hP V
    ⟨(P.sheaf.obj.map k).hom (P.idealIncl hP U g),
      Stacks.Sites.Conormal.map_kernel P.reduction.hom k (P.idealIncl_mem hP U g)⟩ _ ?_
  refine (P.ideal.app_map k ⟨P.idealIncl hP U g, P.idealIncl_mem hP U g⟩).trans ?_
  rw [P.ideal_idealIncl]

/-- Multiplication of the inclusion of a section of `𝒢` by a section of `𝒪_{X'}` is the module
action of its reduction. -/
theorem mul_idealIncl (U : (Opens X.carrier)ᵒᵖ) (x : P.sheaf.obj.obj U) (g : G.val.obj U) :
    x * P.idealIncl hP U g = P.idealIncl hP U (presentationScalar P.reduction U x • g) := by
  refine (P.idealIncl_eq_of_ideal_eq hP U
    (x • ⟨P.idealIncl hP U g, P.idealIncl_mem hP U g⟩) _ ?_).symm
  rw [P.ideal.app_smul, P.ideal_idealIncl]

/-- The square-zero ideal has square zero. -/
theorem idealIncl_mul_idealIncl (U : (Opens X.carrier)ᵒᵖ) (g h : G.val.obj U) :
    P.idealIncl hP U g * P.idealIncl hP U h = 0 := by
  rw [mul_idealIncl, show presentationScalar P.reduction U (P.idealIncl hP U g) = 0 from
    P.reduction_idealIncl hP U g, zero_smul, idealIncl_zero]

end Incl

/-! ### Local surjectivity of the first projection of a fibre product -/

/-- The first projection of a fibre product of presheaves of sets is locally surjective when the
second map is. -/
instance isLocallySurjective_fibreProductFst {C : Type*} [Category C]
    (K : GrothendieckTopology C) {F G' H : Cᵒᵖ ⥤ Type u} (mF : F ⟶ H) (mG : G' ⟶ H)
    [Presheaf.IsLocallySurjective K mG] :
    Presheaf.IsLocallySurjective K (Presheaf.fibreProductFst mF mG) where
  imageSieve_mem {U} s := by
    refine K.superset_covering ?_ (Presheaf.imageSieve_mem K mG (mF.app (op U) s))
    rintro V k ⟨b, hb⟩
    refine ⟨⟨(F.map k.op s, b), ?_⟩, rfl⟩
    exact (NatTrans.naturality_apply mF k.op s).trans hb.symm

/-! ### The twisted homomorphism -/

section Twist

variable (P₁ P₂ : AlgebraSquareZeroExtension f G)
  (hP : ∀ U, Function.Bijective (P₂.ideal.app U))

/-- The free algebra `f⁻¹𝒪_S[ℰ]` on the common refinement `ℰ = 𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`. -/
abbrev pairAlgebra : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    (pairRefinementGenerators P₁ P₂)

/-- The algebra map `a : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₁}`. -/
abbrev fstLift : pairAlgebra P₁ P₂ ⟶ P₁.sheaf := (pairRefinementFst P₁ P₂).lift

/-- The algebra map `b : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₂}`. -/
abbrev sndLift : pairAlgebra P₁ P₂ ⟶ P₂.sheaf := (pairRefinementSnd P₁ P₂).lift

/-- The presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` of the common refinement. -/
abbrev pairPresentation : pairAlgebra P₁ P₂ ⟶ X.sheaf :=
  generatorsPresentation f (pairRefinementGenerators P₁ P₂) (pairRefinementMap P₁ P₂)

/-- The local section `1 ⊗ d p` of the degree `0` term of `𝖭𝖫(α)` for the common refinement. -/
abbrev pairDifferential (U : (Opens X.carrier)ᵒᵖ) (p : (pairAlgebra P₁ P₂).obj.obj U) :=
  Stacks.Sites.Conormal.tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) U p

variable (θ : (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
    (pairRefinementMap P₁ P₂)).base ⟶ G)

/-- The value of the twisted homomorphism `b + θ ∘ d` on a local section of `f⁻¹𝒪_S[ℰ]`. -/
def twistFun (U : (Opens X.carrier)ᵒᵖ) (p : (pairAlgebra P₁ P₂).obj.obj U) : P₂.sheaf.obj.obj U :=
  ((sndLift P₁ P₂).hom.app U).hom p +
    P₂.idealIncl hP U ((θ.val.app U).hom (pairDifferential P₁ P₂ U p))

/-- The reduction of `b(p)` is the presentation applied to `p`. -/
theorem reduction_lift_snd (U : (Opens X.carrier)ᵒᵖ) (p : (pairAlgebra P₁ P₂).obj.obj U) :
    (P₂.reduction.hom.app U).hom (((sndLift P₁ P₂).hom.app U).hom p) =
      ((pairPresentation P₁ P₂).hom.app U).hom p :=
  congrArg (fun t : _ ⟶ X.sheaf ↦ (t.hom.app U).hom p)
    (pairRefinementSnd P₁ P₂).lift_comp_reduction

/-- The reduction of `a(p)` is the presentation applied to `p`. -/
theorem reduction_lift_fst (U : (Opens X.carrier)ᵒᵖ) (p : (pairAlgebra P₁ P₂).obj.obj U) :
    (P₁.reduction.hom.app U).hom (((fstLift P₁ P₂).hom.app U).hom p) =
      ((pairPresentation P₁ P₂).hom.app U).hom p :=
  congrArg (fun t : _ ⟶ X.sheaf ↦ (t.hom.app U).hom p)
    (pairRefinementFst P₁ P₂).lift_comp_reduction

/-- `1 ⊗ d p` is additive in `p`. -/
theorem pairDifferential_add (U : (Opens X.carrier)ᵒᵖ) (p q : (pairAlgebra P₁ P₂).obj.obj U) :
    pairDifferential P₁ P₂ U (p + q) = pairDifferential P₁ P₂ U p + pairDifferential P₁ P₂ U q :=
  Stacks.Sites.Conormal.tensorDifferential_add.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) U p q

/-- `1 ⊗ d p` satisfies the Leibniz rule over the presentation. -/
theorem pairDifferential_mul (U : (Opens X.carrier)ᵒᵖ) (p q : (pairAlgebra P₁ P₂).obj.obj U) :
    pairDifferential P₁ P₂ U (p * q) =
      presentationScalar (pairPresentation P₁ P₂) U p • pairDifferential P₁ P₂ U q +
        presentationScalar (pairPresentation P₁ P₂) U q • pairDifferential P₁ P₂ U p :=
  Stacks.Sites.Conormal.tensorDifferential_mul.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) U p q

/-- `1 ⊗ d p` vanishes on coefficients. -/
theorem pairDifferential_coefficient (U : (Opens X.carrier)ᵒᵖ)
    (r : (inverseImageBaseRing f).obj.obj U) :
    pairDifferential P₁ P₂ U (((freeAlgebraSheafCoefficientMap
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      (pairRefinementGenerators P₁ P₂)).hom.app U).hom r) = 0 :=
  Stacks.Sites.Conormal.tensorDifferential_coefficient.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) U r

/-- `1 ⊗ d p` commutes with restriction. -/
theorem pairDifferential_map {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V)
    (p : (pairAlgebra P₁ P₂).obj.obj U) :
    pairDifferential P₁ P₂ V (((pairAlgebra P₁ P₂).obj.map k).hom p) =
      (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
        (pairRefinementMap P₁ P₂)).base.val.map k (pairDifferential P₁ P₂ U p) :=
  Stacks.Sites.Conormal.tensorDifferential_map.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) k p

/-- `1 ⊗ d 1 = 0`. -/
theorem pairDifferential_one (U : (Opens X.carrier)ᵒᵖ) : pairDifferential P₁ P₂ U 1 = 0 :=
  (congrArg (pairDifferential P₁ P₂ U) (map_one ((freeAlgebraSheafCoefficientMap
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      (pairRefinementGenerators P₁ P₂)).hom.app U).hom).symm).trans
    (pairDifferential_coefficient P₁ P₂ U 1)

/-- The twisted homomorphism agrees with `b` on coefficients. -/
private theorem twistFun_coefficient (U : (Opens X.carrier)ᵒᵖ)
    (r : (inverseImageBaseRing f).obj.obj U) :
    twistFun P₁ P₂ hP θ U (((freeAlgebraSheafCoefficientMap
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
        (pairRefinementGenerators P₁ P₂)).hom.app U).hom r) =
      ((sndLift P₁ P₂).hom.app U).hom (((freeAlgebraSheafCoefficientMap
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
        (pairRefinementGenerators P₁ P₂)).hom.app U).hom r) := by
  have h0 := (congrArg (θ.val.app U).hom (pairDifferential_coefficient P₁ P₂ U r)).trans
    (map_zero (θ.val.app U).hom)
  rw [twistFun, h0, idealIncl_zero, add_zero]

/-- The twisted homomorphism sends `1` to `1`. -/
theorem twistFun_one (U : (Opens X.carrier)ᵒᵖ) : twistFun P₁ P₂ hP θ U 1 = 1 := by
  have h := twistFun_coefficient P₁ P₂ hP θ U 1
  rwa [map_one, map_one] at h

/-- The twisted homomorphism is additive. -/
theorem twistFun_add (U : (Opens X.carrier)ᵒᵖ) (p q : (pairAlgebra P₁ P₂).obj.obj U) :
    twistFun P₁ P₂ hP θ U (p + q) = twistFun P₁ P₂ hP θ U p + twistFun P₁ P₂ hP θ U q := by
  have hl : ((sndLift P₁ P₂).hom.app U).hom (p + q) =
      ((sndLift P₁ P₂).hom.app U).hom p + ((sndLift P₁ P₂).hom.app U).hom q := map_add _ p q
  have hθ : (θ.val.app U).hom (pairDifferential P₁ P₂ U (p + q)) =
      (θ.val.app U).hom (pairDifferential P₁ P₂ U p) +
        (θ.val.app U).hom (pairDifferential P₁ P₂ U q) :=
    (congrArg (θ.val.app U).hom (pairDifferential_add P₁ P₂ U p q)).trans (map_add _ _ _)
  unfold twistFun
  rw [hl, hθ, idealIncl_add]
  abel

/-- The twisted homomorphism is multiplicative. -/
theorem twistFun_mul (U : (Opens X.carrier)ᵒᵖ) (p q : (pairAlgebra P₁ P₂).obj.obj U) :
    twistFun P₁ P₂ hP θ U (p * q) = twistFun P₁ P₂ hP θ U p * twistFun P₁ P₂ hP θ U q := by
  have hl : ((sndLift P₁ P₂).hom.app U).hom (p * q) =
      ((sndLift P₁ P₂).hom.app U).hom p * ((sndLift P₁ P₂).hom.app U).hom q := map_mul _ p q
  have hθ : (θ.val.app U).hom (pairDifferential P₁ P₂ U (p * q)) =
      presentationScalar (pairPresentation P₁ P₂) U p •
          (θ.val.app U).hom (pairDifferential P₁ P₂ U q) +
        presentationScalar (pairPresentation P₁ P₂) U q •
          (θ.val.app U).hom (pairDifferential P₁ P₂ U p) :=
    (congrArg (θ.val.app U).hom (pairDifferential_mul P₁ P₂ U p q)).trans
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (map_smul _ _ _) (map_smul _ _ _)))
  have hp : presentationScalar P₂.reduction U (((sndLift P₁ P₂).hom.app U).hom p) =
      presentationScalar (pairPresentation P₁ P₂) U p :=
    reduction_lift_snd P₁ P₂ U p
  have hq : presentationScalar P₂.reduction U (((sndLift P₁ P₂).hom.app U).hom q) =
      presentationScalar (pairPresentation P₁ P₂) U q :=
    reduction_lift_snd P₁ P₂ U q
  unfold twistFun
  rw [hl, hθ, idealIncl_add, add_mul, mul_add, mul_add, idealIncl_mul_idealIncl, add_zero,
    mul_idealIncl, mul_comm (P₂.idealIncl hP U _), mul_idealIncl, hp, hq]
  abel

/-- The twisted homomorphism commutes with the restriction maps. -/
theorem twistFun_naturality {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V)
    (p : (pairAlgebra P₁ P₂).obj.obj U) :
    twistFun P₁ P₂ hP θ V (((pairAlgebra P₁ P₂).obj.map k).hom p) =
      (P₂.sheaf.obj.map k).hom (twistFun P₁ P₂ hP θ U p) := by
  have hl : ((sndLift P₁ P₂).hom.app V).hom (((pairAlgebra P₁ P₂).obj.map k).hom p) =
      (P₂.sheaf.obj.map k).hom (((sndLift P₁ P₂).hom.app U).hom p) :=
    NatTrans.naturality_apply (sndLift P₁ P₂).hom k p
  have hθ : (θ.val.app V).hom (pairDifferential P₁ P₂ V (((pairAlgebra P₁ P₂).obj.map k).hom p)) =
      G.val.map k ((θ.val.app U).hom (pairDifferential P₁ P₂ U p)) :=
    (congrArg (θ.val.app V).hom (pairDifferential_map P₁ P₂ k p)).trans
      (PresheafOfModules.naturality_apply θ.val k _)
  have hm : (P₂.sheaf.obj.map k).hom (((sndLift P₁ P₂).hom.app U).hom p +
      P₂.idealIncl hP U ((θ.val.app U).hom (pairDifferential P₁ P₂ U p))) =
      (P₂.sheaf.obj.map k).hom (((sndLift P₁ P₂).hom.app U).hom p) +
      (P₂.sheaf.obj.map k).hom
        (P₂.idealIncl hP U ((θ.val.app U).hom (pairDifferential P₁ P₂ U p))) := map_add _ _ _
  unfold twistFun
  rw [hl, hθ, idealIncl_map, hm]

/-- **The twisted homomorphism `b + θ ∘ d : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₂}`** of Step 3 of the proof of
**Stacks 08U8**, as a homomorphism of sheaves of commutative rings. -/
def twistHom : pairAlgebra P₁ P₂ ⟶ P₂.sheaf :=
  ⟨{ app U := CommRingCat.ofHom
        { toFun := twistFun P₁ P₂ hP θ U
          map_one' := twistFun_one P₁ P₂ hP θ U
          map_mul' := twistFun_mul P₁ P₂ hP θ U
          map_zero' := by
            have h := twistFun_add P₁ P₂ hP θ U 0 0
            rw [add_zero] at h
            exact (add_eq_left.1 h.symm)
          map_add' := twistFun_add P₁ P₂ hP θ U }
     naturality {U V} k := by
       ext p
       exact twistFun_naturality P₁ P₂ hP θ k p }⟩

/-- The twisted homomorphism `twistHom` acts on sections by `twistFun`. -/
@[simp]
theorem twistHom_app (U : (Opens X.carrier)ᵒᵖ) (p : (pairAlgebra P₁ P₂).obj.obj U) :
    ((twistHom P₁ P₂ hP θ).hom.app U).hom p = twistFun P₁ P₂ hP θ U p :=
  rfl

/-- The generators of the common refinement surject onto the first extension. -/
instance isLocallySurjective_pairRefinementFst_liftGen :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (pairRefinementFst P₁ P₂).liftGen := by
  have h : (pairRefinementFst P₁ P₂).liftGen =
      Presheaf.fibreProductFst P₁.generatorsMap P₂.generatorsMap :=
    Category.comp_id _
  rw [h]
  exact isLocallySurjective_fibreProductFst _ _ _

/-- The algebra map `a : f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'₁}` is locally surjective. -/
instance isLocallySurjective_fstLift :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) (fstLift P₁ P₂).hom := by
  have := isLocallySurjective_pairRefinementFst_liftGen P₁ P₂
  exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    (pairRefinementFst P₁ P₂).sheaf (pairRefinementGenerators P₁ P₂)
    (pairRefinementFst P₁ P₂).base (pairRefinementFst P₁ P₂).liftGen

/-- The difference homomorphism of the two extensions over the common refinement, on a local
relation `k`: `P₁`'s value minus `P₂`'s. -/
theorem obstruction_conormalClass (U : (Opens X.carrier)ᵒᵖ)
    (k : ↥(kernelIdeal (pairPresentation P₁ P₂).hom U)) :
    ((PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
        (pairRefinementSnd P₁ P₂)).val.app U).hom
      (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
        (pairPresentation P₁ P₂) U k) =
      P₁.ideal.app U ⟨((fstLift P₁ P₂).hom.app U).hom k.1,
          (pairRefinementFst P₁ P₂).lift_mem_kernelIdeal U k⟩ -
        P₂.ideal.app U ⟨((sndLift P₁ P₂).hom.app U).hom k.1,
          (pairRefinementSnd P₁ P₂).lift_mem_kernelIdeal U k⟩ :=
  Stacks.Sites.Conormal.conormalDifference_toAssociatedModule (pairPresentation P₁ P₂) G
    (pairRefinementFst P₁ P₂).idealRestriction (pairRefinementSnd P₁ P₂).idealRestriction U k

variable {P₁ P₂ θ} in
/-- **The input of Step 3.** If `θ` factors the difference homomorphism through the degree `0`
term of `𝖭𝖫(α)`, then on a local relation `k` the derivation `θ ∘ d` takes the value
`P₁`'s identification of `a(k)` minus `P₂`'s identification of `b(k)`. -/
theorem theta_pairDifferential
    (hθ : (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
        (pairRefinementMap P₁ P₂)).d ≫ θ =
      PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
        (pairRefinementSnd P₁ P₂))
    (U : (Opens X.carrier)ᵒᵖ) (k : ↥(kernelIdeal (pairPresentation P₁ P₂).hom U)) :
    (θ.val.app U).hom (pairDifferential P₁ P₂ U k.1) =
      P₁.ideal.app U ⟨((fstLift P₁ P₂).hom.app U).hom k.1,
          (pairRefinementFst P₁ P₂).lift_mem_kernelIdeal U k⟩ -
        P₂.ideal.app U ⟨((sndLift P₁ P₂).hom.app U).hom k.1,
          (pairRefinementSnd P₁ P₂).lift_mem_kernelIdeal U k⟩ := by
  have hf := Stacks.Sites.Conormal.conormalSequence_f_class.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
    (pairPresentation P₁ P₂) U k
  have hv := congrArg (fun t => (t.val.app U).hom
      (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) (pairAlgebra P₁ P₂) X.sheaf
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂))
        (pairPresentation P₁ P₂) U k)) hθ
  exact ((congrArg (θ.val.app U).hom hf).symm.trans hv).trans
    (obstruction_conormalClass P₁ P₂ U k)

/-- A local section whose image under `a` lies in the square-zero ideal of `𝒪_{X'₁}` is a relation
of the presentation. -/
private theorem mem_kernelIdeal_pairPresentation (U : (Opens X.carrier)ᵒᵖ)
    (x : (pairAlgebra P₁ P₂).obj.obj U)
    (hx : ((fstLift P₁ P₂).hom.app U).hom x ∈ kernelIdeal P₁.reduction.hom U) :
    x ∈ kernelIdeal (pairPresentation P₁ P₂).hom U := by
  change ((pairPresentation P₁ P₂).hom.app U).hom x = 0
  rw [← reduction_lift_fst P₁ P₂ U x]
  exact hx

variable {P₁ P₂ θ} in
/-- The twisted homomorphism kills the kernel of `a`. -/
theorem twistHom_eq_zero_of_fstLift_eq_zero
    (hθ : (PresentedSquareZeroExtension.twoTerm f (pairRefinementGenerators P₁ P₂)
        (pairRefinementMap P₁ P₂)).d ≫ θ =
      PresentedSquareZeroExtension.obstruction (pairRefinementFst P₁ P₂)
        (pairRefinementSnd P₁ P₂))
    (U : (Opens X.carrier)ᵒᵖ) (x : (pairAlgebra P₁ P₂).obj.obj U)
    (hx : ((fstLift P₁ P₂).hom.app U).hom x = 0) :
    ((twistHom P₁ P₂ hP θ).hom.app U).hom x = 0 := by
  have hk := mem_kernelIdeal_pairPresentation P₁ P₂ U x (by rw [hx]; exact zero_mem _)
  have h := theta_pairDifferential hθ U ⟨x, hk⟩
  have h1 : P₁.ideal.app U ⟨((fstLift P₁ P₂).hom.app U).hom x,
      (pairRefinementFst P₁ P₂).lift_mem_kernelIdeal U ⟨x, hk⟩⟩ = 0 := by
    rw [show (⟨((fstLift P₁ P₂).hom.app U).hom x,
      (pairRefinementFst P₁ P₂).lift_mem_kernelIdeal U ⟨x, hk⟩⟩ :
        ↥(kernelIdeal P₁.reduction.hom U)) = 0 from Subtype.ext hx, map_zero]
  rw [h1, zero_sub] at h
  rw [twistHom_app, twistFun, h, show -(P₂.ideal.app U ⟨((sndLift P₁ P₂).hom.app U).hom x,
      (pairRefinementSnd P₁ P₂).lift_mem_kernelIdeal U ⟨x, hk⟩⟩) =
      P₂.ideal.app U (-⟨((sndLift P₁ P₂).hom.app U).hom x,
      (pairRefinementSnd P₁ P₂).lift_mem_kernelIdeal U ⟨x, hk⟩⟩) from (map_neg _ _).symm,
    idealIncl_ideal]
  exact add_neg_cancel _

end Twist

/-! ### The morphism of extensions -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Square-zero extensions with the same class admit a morphism of extensions.** If two
square-zero extensions `𝒪_{X'₁}`, `𝒪_{X'₂}` of `f⁻¹𝒪_S`-algebras have the same class in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, and the identification of the square-zero ideal of `𝒪_{X'₂}` with
`𝒢` is bijective on sections, there is a homomorphism `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of sheaves of rings
compatible with the `f⁻¹𝒪_S`-algebra structures, with the reductions to `𝒪_X` and with the two
identifications of the ideals with `𝒢`.

This is the converse of `extClass_eq_extClass_of_hom`: Step 3 of the proof of **Stacks 08U8**
over the common refinement `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`. -/
theorem exists_hom_of_extClass_eq (P₁ P₂ : AlgebraSquareZeroExtension f G)
    (hP : ∀ U, Function.Bijective (P₂.ideal.app U))
    (h : P₁.toPresented.extClass = P₂.toPresented.extClass) :
    ∃ (θ : P₁.sheaf ⟶ P₂.sheaf) (_ : P₁.base ≫ θ = P₂.base)
      (hred : θ ≫ P₂.reduction = P₁.reduction),
      ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
        P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
          θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y := by
  obtain ⟨θ, hθ⟩ := (NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff _ G _).1
    ((extClass_eq_extClass_iff_pairRefinement P₁ P₂).1 h)
  let φ : P₁.sheaf ⟶ P₂.sheaf := Stacks.Sites.RingDescent.desc (fstLift P₁ P₂)
    (twistHom P₁ P₂ hP θ) (twistHom_eq_zero_of_fstLift_eq_zero hP hθ)
  have hφ : fstLift P₁ P₂ ≫ φ = twistHom P₁ P₂ hP θ :=
    Stacks.Sites.RingDescent.comp_desc _ _ _
  have hφU : ∀ U x, (φ.hom.app U).hom (((fstLift P₁ P₂).hom.app U).hom x) =
      twistFun P₁ P₂ hP θ U x := fun U x =>
    congrArg (fun t : pairAlgebra P₁ P₂ ⟶ P₂.sheaf => (t.hom.app U).hom x) hφ
  have hred : φ ≫ P₂.reduction = P₁.reduction := by
    refine Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective (fstLift P₁ P₂) ?_
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
      (RingHom.ext fun x => ?_)))
    change (P₂.reduction.hom.app U).hom ((φ.hom.app U).hom (((fstLift P₁ P₂).hom.app U).hom x)) =
      (P₁.reduction.hom.app U).hom (((fstLift P₁ P₂).hom.app U).hom x)
    rw [hφU, twistFun, map_add, reduction_idealIncl, add_zero, reduction_lift_snd,
      reduction_lift_fst]
  refine ⟨φ, ?_, hred, ?_⟩
  · have hb₁ : freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂) ≫ fstLift P₁ P₂ = P₁.base :=
      freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _
    have hb₂ : freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) (pairRefinementGenerators P₁ P₂) ≫ sndLift P₁ P₂ = P₂.base :=
      freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _
    rw [← hb₁, Category.assoc, hφ, ← hb₂]
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
      (RingHom.ext fun r => ?_)))
    exact twistFun_coefficient P₁ P₂ hP θ U r
  · intro V y
    refine Stacks.Sites.SqZeroPushout.eq_of_locally_eq (Stacks.SheafOfModules.isSheaf_forget G)
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology X.carrier) (fstLift P₁ P₂).hom
        (y : P₁.sheaf.obj.obj V)) _ _ ?_
    rintro W k ⟨x, hx⟩
    have hx' : ((fstLift P₁ P₂).hom.app (op W)).hom x =
        (P₁.sheaf.obj.map k.op).hom (y : P₁.sheaf.obj.obj V) := hx
    have hk := mem_kernelIdeal_pairPresentation P₁ P₂ (op W) x
      (hx'.symm ▸ Stacks.Sites.Conormal.map_kernel P₁.reduction.hom k.op y.2)
    have hl := P₁.ideal.app_map k.op y
    have hr := P₂.ideal.app_map k.op ⟨φ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom
      P₂.reduction.hom φ.hom (hom_of_comp_eq hred) V y.2⟩
    change G.val.map k.op _ = G.val.map k.op _
    rw [← hl, ← hr]
    have hy : (⟨(P₁.sheaf.obj.map k.op).hom (y : P₁.sheaf.obj.obj V),
        Stacks.Sites.Conormal.map_kernel P₁.reduction.hom k.op y.2⟩ :
          ↥(kernelIdeal P₁.reduction.hom (op W))) =
        ⟨((fstLift P₁ P₂).hom.app (op W)).hom x,
          (pairRefinementFst P₁ P₂).lift_mem_kernelIdeal (op W) ⟨x, hk⟩⟩ :=
      Subtype.ext hx'.symm
    have hφy : (P₂.sheaf.obj.map k.op).hom (φ.hom.app V y) =
        twistFun P₁ P₂ hP θ (op W) x := by
      rw [← hφU, hx']
      exact (NatTrans.naturality_apply φ.hom k.op (y : P₁.sheaf.obj.obj V)).symm
    have hθx := theta_pairDifferential hθ (op W) ⟨x, hk⟩
    rw [hy]
    have hsplit : (⟨(P₂.sheaf.obj.map k.op).hom (φ.hom.app V y),
        Stacks.Sites.Conormal.map_kernel P₂.reduction.hom k.op
          (kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom φ.hom
            (hom_of_comp_eq hred) V y.2)⟩ : ↥(kernelIdeal P₂.reduction.hom (op W))) =
        ⟨((sndLift P₁ P₂).hom.app (op W)).hom x,
          (pairRefinementSnd P₁ P₂).lift_mem_kernelIdeal (op W) ⟨x, hk⟩⟩ +
        ⟨P₂.idealIncl hP (op W) ((θ.val.app (op W)).hom (pairDifferential P₁ P₂ (op W) x)),
          P₂.idealIncl_mem hP _ _⟩ :=
      Subtype.ext hφy
    rw [hsplit, map_add, ideal_idealIncl, hθx]
    abel

/-- **The class of a square-zero extension determines it up to morphisms of extensions.** For
square-zero extensions whose identification of the ideal with `𝒢` is bijective on sections, the
classes in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` agree exactly when there is a homomorphism of sheaves of
rings from the one to the other compatible with the algebra structures, the reductions and the
identifications of the ideals. -/
theorem extClass_eq_iff_exists_hom (P₁ P₂ : AlgebraSquareZeroExtension f G)
    (hP : ∀ U, Function.Bijective (P₂.ideal.app U)) :
    P₁.toPresented.extClass = P₂.toPresented.extClass ↔
      ∃ (θ : P₁.sheaf ⟶ P₂.sheaf) (_ : P₁.base ≫ θ = P₂.base)
        (hred : θ ≫ P₂.reduction = P₁.reduction),
        ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
          P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
            θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y :=
  ⟨exists_hom_of_extClass_eq P₁ P₂ hP, fun ⟨θ, hbase, hred, hideal⟩ =>
    extClass_eq_extClass_of_hom P₁ P₂ θ hbase hred hideal⟩

end Derived

/-! ### The short five lemma for square-zero extensions -/

section FiveLemma

variable {P₁ P₂ : AlgebraSquareZeroExtension f G}
  (h₁ : ∀ U, Function.Bijective (P₁.ideal.app U))
  (h₂ : ∀ U, Function.Bijective (P₂.ideal.app U))
  (θ : P₁.sheaf ⟶ P₂.sheaf) (hred : θ ≫ P₂.reduction = P₁.reduction)
  (hideal : ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P₁.reduction.hom V)),
    P₂.ideal.app V ⟨θ.hom.app V y, kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom
      θ.hom (hom_of_comp_eq hred) V y.2⟩ = P₁.ideal.app V y)

include hred in
omit h₂ in
/-- A homomorphism over `𝒪_X` commutes with the reductions on sections. -/
theorem reduction_hom_app (V : (Opens X.carrier)ᵒᵖ) (y : P₁.sheaf.obj.obj V) :
    (P₂.reduction.hom.app V).hom ((θ.hom.app V).hom y) = (P₁.reduction.hom.app V).hom y :=
  congrArg (fun t : P₁.sheaf ⟶ X.sheaf => (t.hom.app V).hom y) hred

include hideal in
/-- A morphism of extensions carries the inclusion of `𝒢` into the source to the inclusion of
`𝒢` into the target. -/
theorem hom_idealIncl (V : (Opens X.carrier)ᵒᵖ) (g : G.val.obj V) :
    (θ.hom.app V).hom (P₁.idealIncl h₁ V g) = P₂.idealIncl h₂ V g := by
  refine (P₂.idealIncl_eq_of_ideal_eq h₂ V ⟨(θ.hom.app V).hom (P₁.idealIncl h₁ V g),
    kernelIdeal_le_comap P₁.reduction.hom P₂.reduction.hom θ.hom (hom_of_comp_eq hred) V
      (P₁.idealIncl_mem h₁ V g)⟩ g ?_).symm
  exact (hideal V ⟨P₁.idealIncl h₁ V g, P₁.idealIncl_mem h₁ V g⟩).trans (P₁.ideal_idealIncl h₁ V g)

include hideal h₁ in
omit h₂ in
/-- A morphism of extensions whose source has bijective ideal identification is injective on
sections. -/
theorem injective_hom_app (V : (Opens X.carrier)ᵒᵖ) :
    Function.Injective (θ.hom.app V).hom := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have hk : y ∈ kernelIdeal P₁.reduction.hom V := by
    change (P₁.reduction.hom.app V).hom y = 0
    rw [← reduction_hom_app θ hred V y, hy, map_zero]
  have h0 : P₁.ideal.app V ⟨y, hk⟩ = 0 := by
    rw [← hideal V ⟨y, hk⟩]
    exact (congrArg (P₂.ideal.app V) (Subtype.ext hy)).trans (map_zero _)
  exact congrArg Subtype.val ((h₁ V).1 (h0.trans (map_zero _).symm))

include hideal h₁ h₂ in
/-- A morphism of extensions whose ideal identifications are bijective is locally surjective. -/
theorem isLocallySurjective_hom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) θ.hom where
  imageSieve_mem {V} z := by
    refine (Opens.grothendieckTopology X.carrier).superset_covering ?_
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology X.carrier) P₁.reduction.hom
        ((P₂.reduction.hom.app (op V)).hom z))
    rintro W k ⟨y, hy⟩
    have hz : (P₂.sheaf.obj.map k.op).hom z - (θ.hom.app (op W)).hom y ∈
        kernelIdeal P₂.reduction.hom (op W) := by
      change (P₂.reduction.hom.app (op W)).hom ((P₂.sheaf.obj.map k.op).hom z -
        (θ.hom.app (op W)).hom y) = 0
      rw [map_sub, reduction_hom_app θ hred, hy, NatTrans.naturality_apply P₂.reduction.hom k.op z,
        sub_self]
    refine ⟨y + P₁.idealIncl h₁ (op W) (P₂.ideal.app (op W) ⟨_, hz⟩), ?_⟩
    rw [map_add, hom_idealIncl h₁ h₂ θ hred hideal, P₂.idealIncl_ideal h₂]
    exact add_sub_cancel _ _

include hideal h₁ h₂ in
/-- **The short five lemma for square-zero extensions.** A morphism of square-zero extensions
of `f⁻¹𝒪_S`-algebras — a homomorphism of sheaves of rings over `𝒪_X` compatible with the two
identifications of the ideals with `𝒢` — between extensions whose identifications are bijective
is an isomorphism of sheaves of rings. -/
theorem isIso_of_hom : IsIso θ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) θ.hom :=
    isLocallySurjective_hom h₁ h₂ θ hred hideal
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier) θ.hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (injective_hom_app h₁ θ hred hideal)
  exact (Sheaf.isLocallyBijective_iff_isIso θ).1 ⟨inferInstance, inferInstance⟩

end FiveLemma

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
