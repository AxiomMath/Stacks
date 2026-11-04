module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.CartesianCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveAlgebraicallyClosedPoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Geometric points of a universal homeomorphism to an algebraic space

Let `F : 𝒴 ⟶ N` be a universal homeomorphism from an algebraic stack to (the algebraic stack of) an
algebraic space `N`, and let `V` be an object of the site whose underlying scheme is the spectrum
of an algebraically closed field. Then the isomorphism classes of objects of `𝒴` over `V` map
bijectively onto the `V`-points of `N`: injectivity is condition (3) of Stacks 0CPN for the
universally injective `F`, surjectivity is Stacks 0DTM.

With the cartesian criterion of `AlgebraicGeometry.Stack.KeelMoriEtaleLocal.CartesianCriterion`
this gives: a commutative square of an étale, stabilizer preserving `h : 𝒳' ⟶ 𝒳` over an étale
morphism of algebraic spaces, with universal homeomorphisms as vertical arrows, is cartesian.

## Main results

* `AlgebraicGeometry.Stack.exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace`
* `AlgebraicGeometry.Stack.exists_obj_of_universalHomeomorphism_algebraicSpace`
* `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_spaceModuliSquare_of_universalHomeomorphism`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universal homeomorphism of algebraic stacks is surjective on points**: it is its own base
change along the identity. -/
theorem surjective_pointsMap_of_universalHomeomorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (hf : UniversalHomeomorphism B S hS f) :
    Function.Surjective (pointsMap B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids f.hom.hom) := by
  have H := hf 𝒴 (𝟙 𝒴) (Bicategory.trivialBaseChangeSquare f).swap
    (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare f
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴))))
  let := pointTopology B S hS (Bicategory.trivialBaseChangeSquare f).swap.pt.val
  let := pointTopology B S hS 𝒴.val
  exact H.bijective.2

variable {B S hS}

section UniversalHomeomorphism

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} {N : AlgebraicSpaces B S hS}
  (F : 𝒴 ⟶ algebraicSpaceStack.{u, w} B S hS N.obj N.property)

/-- **Injectivity on isomorphism classes over an algebraically closed field.** Two objects of `𝒴`
over the spectrum of an algebraically closed field with the same image under a universal
homeomorphism to an algebraic space are isomorphic by a morphism over the identity
(Stacks 0CPN). -/
theorem exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
    (hF : UniversalHomeomorphism B S hS F)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (x₁ x₂ : 𝒴.val.val.obj) (h₁ : 𝒴.val.val.p.obj x₁ = V) (h₂ : 𝒴.val.val.p.obj x₂ = V)
    (h : F.hom.hom.obj x₁ = F.hom.hom.obj x₂) :
    ∃ α : x₁ ⟶ x₂, 𝒴.val.val.p.IsHomLift (𝟙 V) α := by
  have hl := (universallyInjective_iff_liftsTwoArrowsAtGeometricPoints B S hS F).1
    (universallyInjective_of_universalHomeomorphism B S hS hF)
  have hlift : (fibredCategory B S hS N.obj).val.p.IsHomLift (𝟙 V) (eqToHom h) :=
    IsHomLift.eqToHom_domain_lift_id h ((Functor.congr_obj F.hom.hom.w x₁).trans h₁)
  obtain ⟨α, hα, -⟩ := hl k V hV x₁ x₂ h₁ h₂ (eqToHom h) hlift
  exact ⟨α, hα⟩

/-- **Surjectivity over an algebraically closed field.** Every point of an algebraic space `N`
with values in the spectrum of an algebraically closed field is the image of an object of `𝒴`
under a universal homeomorphism `𝒴 ⟶ N` (Stacks 0DTM). -/
theorem exists_obj_of_universalHomeomorphism_algebraicSpace
    (hF : UniversalHomeomorphism B S hS F)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) (n : N.obj.obj (op V)) :
    ∃ (x : 𝒴.val.val.obj) (_ : 𝒴.val.val.p.obj x = V),
      F.hom.hom.obj x = (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS N.obj).val.obj) := by
  let y : FieldValuedPoint B S hS
      (algebraicSpaceStack.{u, w} B S hS N.obj N.property).val.val :=
    { carrier := k
      base := V
      isSpec := hV
      obj := ⟨V, Discrete.mk n⟩
      «over» := rfl }
  have : IsAlgClosed y.carrier := inferInstanceAs (IsAlgClosed k)
  obtain ⟨x, ⟨e⟩⟩ := exists_fiber_lift_of_universallyInjective B S hS F
    (universallyInjective_of_universalHomeomorphism B S hS hF) y
    (surjective_pointsMap_of_universalHomeomorphism B S hS hF _)
  exact ⟨x.1, x.2, fibredCategory_obj_eq_of_isHomLift_id B S hS
    ((Functor.congr_obj F.hom.hom.w x.1).trans x.2) rfl e.hom.1 e.hom.2⟩

end UniversalHomeomorphism

/-- **The cartesian criterion with universal homeomorphisms as vertical arrows.** A commutative
square of an étale `h : 𝒳' ⟶ 𝒳` inducing isomorphisms between automorphism groups (Stacks 0DTW)
over an étale morphism `g : M' ⟶ M` of algebraic spaces, whose vertical arrows `f : 𝒳 ⟶ M` and
`f' : 𝒳' ⟶ M'` are universal homeomorphisms, is a 2-fibre product. -/
theorem nonempty_isTwoFibreProduct_spaceModuliSquare_of_universalHomeomorphism
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳)
    {M M' : AlgebraicSpaces B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS M'.obj M'.property) (g : M' ⟶ M)
    (hcomm : f'.hom ≫ (associatedMap B S hS g.hom).1 = h.hom ≫ f.hom)
    (he : IsEtale B S hS h)
    (hauto : ∀ q : points B S hS 𝒳'.val.val 𝒳'.val.isFiberedInGroupoids,
      InducesIsomorphismAt B S hS h q)
    (hg : Space.IsEtale B S hS g.hom) (hf : UniversalHomeomorphism B S hS f)
    (hf' : UniversalHomeomorphism B S hS f') :
    Nonempty (Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS h f f' g hcomm)) :=
  nonempty_isTwoFibreProduct_spaceModuliSquare B S hS h f f' g hcomm he hauto hg
    (fun k _ _ V hV x₁ x₂ h₁ h₂ e =>
      exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace f hf k V hV x₁ x₂ h₁ h₂ e)
    (fun k _ _ V hV x₁ x₂ h₁ h₂ e =>
      exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace f' hf' k V hV x₁ x₂ h₁ h₂ e)
    (fun k _ _ V hV n => exists_obj_of_universalHomeomorphism_algebraicSpace f' hf' k V hV n)

end AlgebraicGeometry.Stack

end
