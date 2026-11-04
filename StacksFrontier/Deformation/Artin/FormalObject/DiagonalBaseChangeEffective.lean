module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismFromAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationTwoFibreProduct
import all StacksFrontier.Deformation.Artin.FormalObject.ApproximationTwoFibreProduct

/-!
# Effectivity of formal objects for a base change of the diagonal

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` satisfying axiom `[4]`
of Section 07XJ of the Stacks project: the functor of Stacks 07X6 from objects over complete
local bases to formal objects is an equivalence. For an object `V` of the site and a 1-morphism
`y : (Sch/V)_{fppf} ⟶ 𝒳 × 𝒳`, the 2-fibre product

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`

satisfies axiom `[4]` again. This is the step of the proof of Stacks 07Y5 that reads
"Axiom [4] follows from Lemmas 07X8 and 07X9": `(Sch/V)_{fppf}` and the final object
`(Sch/S)_{fppf}` are algebraic stacks, so Stacks 07X8 gives axiom `[4]` for them; the product
`𝒳 × 𝒳` is the 2-fibre product of `𝒳` with itself over the final object, and `𝒴` is a
2-fibre product, so Stacks 07X9 applies twice.

Effectivity of every formal object (the form in which Artin's criterion consumes axiom `[4]`)
is then transported along any equivalence over the site, which is how it reaches the category
fibred in sets of the functor of isomorphism classes of `𝒴`.

## Main results

* `Deformation.Artin.isEquivalence_approximationFunctor_product`: axiom `[4]` for `𝒳 × 𝒳`.
* `Deformation.Artin.isEquivalence_approximationFunctor_diagonalBaseChange`: axiom `[4]` for
  `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`.
* `Deformation.Artin.essSurj_approximationFunctor_of_equivalenceOver`: effectivity of all formal
  objects transports along an equivalence over the site.
* `Deformation.Artin.isEffective_of_equivalenceOver_diagonalBaseChange`: every formal object of
  a category equivalent over the site to `𝒴` is effective.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w vZ wZ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Axiom `[4]` for the final object.** The approximation functor of the identity of the big
fppf site of `S` is an equivalence: the final object is an algebraic stack, so this is
Stacks 07X8. -/
theorem isEquivalence_approximationFunctor_id :
    (approximationFunctor B S hS (𝟭 (BigFppfOver B S hS))
      Functor.isFiberedInGroupoids_id).IsEquivalence :=
  isEquivalence_approximationFunctor_algebraicStacks.{u, u + 1}
    (⟨CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        Functor.isFiberedInGroupoids_id,
      Stack.isAlgebraicStack_terminal.{u, u + 1} B S hS⟩ :
      Stack.AlgebraicStacks.{u, u + 1} B S hS)

/-- **Axiom `[4]` for the relocalized site.** For an object `V` of the big fppf site of `S`, the
approximation functor of `Over.map V.hom : (Sch/V)_{fppf} ⥤ (Sch/S)_{fppf}` is an equivalence:
`(Sch/V)_{fppf}` is an algebraic stack over `S`, so this is Stacks 07X8. -/
theorem isEquivalence_approximationFunctor_overMap (V : BigFppfOver B S hS) :
    (approximationFunctor B S hS (Over.map V.hom)
      (Functor.IsFiberedInGroupoids.over_map V.hom)).IsEquivalence :=
  isEquivalence_approximationFunctor_algebraicStacks.{u, u + 1}
    (⟨CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Over.map V.hom))
        (Functor.IsFiberedInGroupoids.over_map V.hom),
      Stack.isAlgebraicStack_overMap.{u, u + 1} B S hS V⟩ :
      Stack.AlgebraicStacks.{u, u + 1} B S hS)

/-- **Axiom `[4]` for a product.** If the approximation functor of `𝒳` (Stacks 07X6) is an
equivalence, so is that of `𝒳 × 𝒳`: the product is the 2-fibre product over the final object,
which satisfies axiom `[4]` by Stacks 07X8, so this is Stacks 07X9. -/
theorem isEquivalence_approximationFunctor_product
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).IsEquivalence) :
    (approximationFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids).IsEquivalence :=
  isEquivalence_approximationFunctor_twoFibreProduct B S hS 𝒳.val.p
    (𝟭 (BigFppfOver B S hS)) 𝒳.val.p 𝒳.val.p 𝒳.val.p 𝒳.isFiberedInGroupoids
    Functor.isFiberedInGroupoids_id 𝒳.isFiberedInGroupoids (Functor.comp_id _)
    (Functor.comp_id _) h𝒳 (isEquivalence_approximationFunctor_id B S hS) h𝒳

/-- **Axiom `[4]` for a base change of the diagonal along a fibred category with axiom `[4]`.**
Let `𝒳` satisfy axiom `[4]`, let `p𝒱 : 𝒱 ⥤ (Sch/S)_{fppf}` be fibred in groupoids with
approximation functor an equivalence, and let `g : 𝒱 ⥤ 𝒳 × 𝒳` be a 1-morphism over the site.
Then the approximation functor of `𝒱 ×_{g, 𝒳 × 𝒳, Δ} 𝒳` is an equivalence (Stacks 07X9,
applied after `isEquivalence_approximationFunctor_product`). -/
theorem isEquivalence_approximationFunctor_diagonalBaseChange_of_isEquivalence
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).IsEquivalence)
    {𝒱 : Type vZ} [Category.{wZ} 𝒱] (p𝒱 : 𝒱 ⥤ BigFppfOver B S hS)
    (hp𝒱 : p𝒱.IsFiberedInGroupoids)
    (h𝒱 : (approximationFunctor B S hS p𝒱 hp𝒱).IsEquivalence)
    (g : 𝒱 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hg : g ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = p𝒱) :
    (approximationFunctor B S hS
      (TwoFibreProductOver.structureFunctor p𝒱 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p g
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
      (TwoFibreProductOver.isFiberedInGroupoids p𝒱 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p g
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor hp𝒱 𝒳.isFiberedInGroupoids
        (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hg
        (Stack.diagonalBasedFunctor B S hS 𝒳).w)).IsEquivalence :=
  isEquivalence_approximationFunctor_twoFibreProduct B S hS p𝒱
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p 𝒳.val.p g
    (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor hp𝒱
    (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hg
    (Stack.diagonalBasedFunctor B S hS 𝒳).w h𝒱
    (isEquivalence_approximationFunctor_product B S hS 𝒳 h𝒳) h𝒳

/-- **Axiom `[4]` for `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`** (the step "Axiom [4] follows from
Lemmas 07X8 and 07X9" of the proof of Stacks 07Y5). Let `𝒳` satisfy axiom `[4]`, let `V` be an
object of the big fppf site of `S` and `y : (Sch/V)_{fppf} ⥤ 𝒳 × 𝒳` a 1-morphism over the site.
Then the approximation functor of the 2-fibre product of `y` and the diagonal is an
equivalence. -/
theorem isEquivalence_approximationFunctor_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).IsEquivalence)
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom) :
    (approximationFunctor B S hS
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
      (TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
        (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
        (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
        (Stack.diagonalBasedFunctor B S hS 𝒳).w)).IsEquivalence :=
  isEquivalence_approximationFunctor_diagonalBaseChange_of_isEquivalence B S hS 𝒳 h𝒳
    (Over.map V.hom) (Functor.IsFiberedInGroupoids.over_map V.hom)
    (isEquivalence_approximationFunctor_overMap B S hS V) y hy

section Transport

variable {B S hS}
variable {𝒮 : Type*} [Category 𝒮] {𝒯 : Type*} [Category 𝒯]
  {P : 𝒮 ⥤ BigFppfOver B S hS} {Q : 𝒯 ⥤ BigFppfOver B S hS}

/-- **Effectivity of formal objects transports along an equivalence over the site.** If every
formal object of `P` is effective and `Q` is equivalent to `P` over the big fppf site, every
formal object of `Q` is effective. A formal object `ξ` of `Q` is carried to `P` by the inverse
equivalence, approximated there by an object over a complete local base, and that object is
carried back; the approximation functors commute with both equivalences up to isomorphism, and
the counit identifies the round trip of `ξ` with `ξ`. -/
theorem essSurj_approximationFunctor_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS) P Q)
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids)
    (h : (approximationFunctor B S hS P hP).EssSurj) :
    (approximationFunctor B S hS Q hQ).EssSurj := by
  refine ⟨fun ξ => ?_⟩
  let ξ' := (mapFormalObjects e.inv.functor e.inv.w).obj ξ
  obtain ⟨x, ⟨φ⟩⟩ := h.mem_essImage ξ'
  let ψ : (mapFormalObjects e.hom.functor e.hom.w).obj ξ' ≅ ξ :=
    { hom := ⟨fun n => e.counitIso.hom.app (ξ.level n),
        fun n => e.counitIso.hom.naturality (ξ.transition n)⟩
      inv := ⟨fun n => e.counitIso.inv.app (ξ.level n),
        fun n => e.counitIso.inv.naturality (ξ.transition n)⟩
      hom_inv_id := FormalObject.Hom.ext fun n => e.counitIso.hom_inv_id_app (ξ.level n)
      inv_hom_id := FormalObject.Hom.ext fun n => e.counitIso.inv_hom_id_app (ξ.level n) }
  exact ⟨(mapCompleteLocalObjects e.hom.functor e.hom.w).obj x,
    ⟨(approximationMapIso e.hom.functor e.hom.w hP hQ).symm.app x ≪≫
      (mapFormalObjects e.hom.functor e.hom.w).mapIso φ ≪≫ ψ⟩⟩

/-- **Every formal object is effective for a category equivalent to a base change of the
diagonal.** Let `𝒳` satisfy axiom `[4]`, let `y : (Sch/V)_{fppf} ⥤ 𝒳 × 𝒳` be a 1-morphism over
the site, and let `Q` be equivalent over the site to `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` (for
example the category fibred in sets of its functor of isomorphism classes). Then every formal
object of `Q` is effective. This is axiom `[4]` for the functor `Y` in the proof of
Stacks 07Y5, in the form Artin's criterion for functors uses it. -/
theorem isEffective_of_equivalenceOver_diagonalBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : (approximationFunctor B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids).IsEquivalence)
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS)
      (TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor) Q)
    (hQ : Q.IsFiberedInGroupoids) (ξ : FormalObject B S hS Q) :
    FormalObject.IsEffective B S hS Q hQ ξ :=
  have := isEquivalence_approximationFunctor_diagonalBaseChange B S hS 𝒳 h𝒳 V y hy
  (essSurj_approximationFunctor_of_equivalenceOver e _ hQ inferInstance).mem_essImage ξ

end Transport

end Deformation.Artin

end
