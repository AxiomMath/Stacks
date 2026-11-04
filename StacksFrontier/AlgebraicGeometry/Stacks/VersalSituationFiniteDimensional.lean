module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituation
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenary
public import StacksFrontier.Deformation.Artin.FiniteDimensional.AlgebraicStack
import StacksCore.Tactic.StacksAttribute

/-!
# The deformation category of a finite type point of an algebraic stack (Stacks 0DQW)

In Situation 0DQU — `𝒳` an algebraic stack locally of finite type over a locally Noetherian
scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a morphism with `k` a field of finite type over `S`. Then
`𝓕_{𝒳,k,x₀}` is a deformation category, and its tangent space and its space of infinitesimal
automorphisms are finite-dimensional over `k`.

## Main results

* `AlgebraicGeometry.Stack.isFiniteDimensionalDeformationCategory_of_versalSituation`: for `x₀`
  over a field `k` of finite type over `S`, `𝓕_{𝒳,k,x₀}` is a deformation category with
  finite-dimensional tangent space and space of infinitesimal automorphisms.

## Implementation notes

`𝓕_{𝒳,k,x₀}` is the predeformation category of Section 07T2, formed over `𝒞_Λ` for an affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with `Λ → k` finite; such an open exists by
Stacks 01TA, and the category does not depend on its choice up to canonical equivalence. The
statement is made for every such `Spec Λ`.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

/-- In Situation 0DQU, let `x₀` be an object of `𝒳` over `Spec k`, for a field `k` of finite type
over `S`, and let `Spec Λ ⊆ S` be an affine open through which `Spec k ⟶ S` factors with `Λ → k`
finite. Then `𝓕_{𝒳,k,x₀}` is a deformation category whose tangent space and space of infinitesimal
automorphisms are finite-dimensional over `k`. -/
@[stacks 0DQW]
theorem isFiniteDimensionalDeformationCategory_of_versalSituation
    (D : VersalSituation.{u, w}) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).category
    Deformation.IsFiniteDimensionalDeformationCategory
      (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection := by
  obtain ⟨hfib, hstack, hdiag, U, a, hrep, ha⟩ := D.𝒳.property
  let aS : schemeStack.{u, w} D.B D.S D.hS U ⟶ D.𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom a)
  have haS : AlgebraicStacks.IsSmooth D.B D.S D.hS aS :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} D.B D.S D.hS
      (fun _ _ k => Space.IsSmooth D.B D.S D.hS k) D.𝒳.property _ hrep
      (fun V y hy G hG he => (ha V y hy G hG he).2)
  have haType : AlgebraicStacks.IsLocallyOfFiniteType D.B D.S D.hS aS :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B D.S D.hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth D.B D.S D.hS aS haS)
  have hchain : AlgebraicStacks.IsLocallyOfFiniteType D.B D.S D.hS
      (aS ≫ structureMorphism D.B D.S D.hS D.𝒳) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp D.B D.S D.hS aS (structureMorphism D.B D.S D.hS D.𝒳)
      haType D.locallyFiniteType
  rw [comp_structureMorphism] at hchain
  have : LocallyOfFiniteType (D.B.inclusion.map U.hom) :=
    locallyOfFiniteType_structureMap.{u, w} D.B D.S D.hS U _ hchain
  exact Deformation.Artin.isFiniteDimensionalDeformationCategory_of_algebraicStack D.𝒳 U
    (Bicategory.InducedBicategory.mkHom a) hrep ha iΛ hiΛ x₀ hx₀ hfinite

end AlgebraicGeometry.Stack
