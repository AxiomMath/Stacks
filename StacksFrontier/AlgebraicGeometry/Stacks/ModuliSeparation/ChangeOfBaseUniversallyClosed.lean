module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ChangeOfBaseTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- The 1-morphism of Construction A that the hom-bijection of **Stacks 04X5** assigns to a
1-morphism of algebraic stacks over `S`, read in the 2-category of algebraic stacks over `S'`.
Its underlying functor is that of the given 1-morphism. -/
abbrev constructionAHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    changeBaseAlgebraicStack B S S' hS hS' g 𝒳 ⟶ changeBaseAlgebraicStack B S S' hS hS' g 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (algebraicStackConstructionHomEquiv.{u, w} B S S' hS hS' g 𝒳 𝒴 f).val

/-- **Closedness of a base change is carried along Construction A.** For 1-morphisms
`k : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, if the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵` is closed on points, so is the projection of the 2-fibre product over `S'` of the
1-morphisms of Construction A. Construction A of the 2-fibre product is the 2-fibre product of
Construction A (`AlgebraicGeometry.Stack.changeBaseTwoFibreProductHom`, an equivalence strictly
compatible with the projections), and the points of Construction A are those of the original
stack by a homeomorphism (`AlgebraicGeometry.Stack.isHomeomorph_changeBasePointsEquiv`). -/
theorem isClosed_constructionA_fst {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (k : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴)
    (h : AlgebraicStacks.IsClosed B S hS (twoFibreProductSquareAlgebraicStacks B S hS k f).fst) :
    AlgebraicStacks.IsClosed B S' hS'
      (twoFibreProductSquareAlgebraicStacks B S' hS'
        (constructionAHom B S S' hS hS' g k) (constructionAHom B S S' hS hS' g f)).fst := by
  set PS := twoFibreProductSquareAlgebraicStacks B S hS k f
  set PT := twoFibreProductSquareAlgebraicStacks B S' hS'
    (constructionAHom B S S' hS hS' g k) (constructionAHom B S S' hS hS' g f)
  let Hom := changeBaseTwoFibreProductHom B S S' hS hS' g 𝒴.val 𝒵.val 𝒳.val k.hom.hom f.hom.hom
  let := pointTopology B S hS PS.pt.val
  let := pointTopology B S hS 𝒵.val
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val)
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val)
  let := pointTopology B S' hS' PT.pt.val
  have hH : IsHomeomorph (Stack.pointsMap B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val).val
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val).property
      PT.pt.val.property Hom) :=
    isHomeomorph_pointsMap_of_isEquivalence B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g PS.pt.val) PT.pt.val Hom
      (isEquivalence_changeBaseTwoFibreProductHom B S S' hS hS' g _ _ _ _ _)
  let H := hH.homeomorph
  let EP := (isHomeomorph_changeBasePointsEquiv.{u, w} B S S' hS hS' g PS.pt.val
    PS.pt.property).homeomorph
  let EZ := (isHomeomorph_changeBasePointsEquiv.{u, w} B S S' hS hS' g 𝒵.val
    𝒵.property).homeomorph
  have hfun : Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val).property PT.fst.hom.hom =
      EZ ∘ Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property PS.fst.hom.hom ∘
        EP.symm ∘ H.symm := by
    funext x
    obtain ⟨y, rfl⟩ := H.surjective x
    obtain ⟨z, rfl⟩ := EP.surjective y
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    show Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property _ PT.fst.hom.hom
        (Stack.pointsMap B S' hS' _ _ PT.pt.val.property Hom
          (changeBasePointsEquiv B S S' hS hS' g PS.pt.val.val PS.pt.val.property z)) =
      changeBasePointsEquiv B S S' hS hS' g 𝒵.val.val 𝒵.val.property
        (Stack.pointsMap B S hS PS.pt.val.val PS.pt.val.property 𝒵.val.property PS.fst.hom.hom z)
    exact (Stack.pointsMap_comp B S' hS' _ _ _ _ Hom PT.fst.hom.hom _).trans
      (changeBasePointsEquiv_pointsMap B S S' hS hS' g PS.pt.val.property 𝒵.val.property
        PS.fst.hom.hom z).symm
  show IsClosedMap (Stack.pointsMap B S' hS' PT.pt.val.val PT.pt.val.property
    (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒵.val).property PT.fst.hom.hom)
  rw [hfun]
  exact EZ.isClosedMap.comp (h.comp (EP.symm.isClosedMap.comp H.symm.isClosedMap))

/-- **Universal closedness is carried along Construction A.** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` is universally closed (Stacks 0513), then so is the 1-morphism of
Construction A over `S'` that Stacks 04X5 assigns to it.

An algebraic stack `𝒵` over `S'` with a 1-morphism to Construction A of `𝒴` is, by the bijection
on objects of Stacks 04X5, Construction A of an algebraic stack over `S`, and the 1-morphism is
Construction A of one over `S`; so every base change to be tested is a base change of
`AlgebraicGeometry.Stack.isClosed_constructionA_fst`. -/
theorem universallyClosed_constructionAHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.UniversallyClosed B S hS f) :
    AlgebraicStacks.UniversallyClosed B S' hS' (constructionAHom B S S' hS hS' g f) := by
  intro 𝒵 k
  obtain ⟨𝒵S, h⟩ : ∃ 𝒵S, algebraicStackConstructionObjEquiv.{u, w} B S S' hS hS' g 𝒵S =
      ⟨𝒵, k.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒴⟩ :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  have h1 : changeBaseAlgebraicStack B S S' hS hS' g 𝒵S = 𝒵 := congrArg Sigma.fst h
  subst h1
  have h2 : changeBaseStructureHom B S S' hS hS' g 𝒵S =
      k.hom ≫ changeBaseStructureHom B S S' hS hS' g 𝒴 :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  let kS : 𝒵S ⟶ 𝒴 := (algebraicStackConstructionHomEquiv.{u, w} B S S' hS hS' g 𝒵S 𝒴).symm
    ⟨k.hom, h2.symm⟩
  exact isClosed_constructionA_fst B S S' hS hS' g kS f (hf 𝒵S kS)

end AlgebraicGeometry.Stack

end
