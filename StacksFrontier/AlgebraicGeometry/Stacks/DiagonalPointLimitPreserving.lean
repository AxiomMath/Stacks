module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointFibreOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeSlice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Axiom [1] for the fibres of the diagonal (proof of Stacks 07Y5)

In the proof of Stacks 07Y5 one considers, for a scheme `V` over `S` locally of finite
presentation and an object `y` of `𝒳 × 𝒳` over `V`, the 2-fibre product

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`

over `(Sch/S)_{fppf}`, and checks that it satisfies Artin's axioms. Axiom [1] for `𝒴` is
Stacks 07XM: `(Sch/V)_{fppf}` is limit preserving because `V ⟶ S` is locally of finite
presentation (Stacks 01ZC), `𝒳 × 𝒳` is limit preserving because `𝒳` is, and a 2-fibre product of
limit preserving categories fibred in groupoids is limit preserving.

## Main results

* `AlgebraicGeometry.Stack.limitPreserving_yoneda_bigFppfOver_of_locallyOfFinitePresentation`:
  the functor of points on the big fppf site of `S` of a scheme locally of finite presentation
  over `S` is limit preserving (Stacks 01ZC).
* `AlgebraicGeometry.Stack.isLimitPreserving_schemeSlice`: `(Sch/V)_{fppf}`, over
  `(Sch/S)_{fppf}` through `Over.map V.hom`, is limit preserving in the sense of Stacks 07XL.
* `AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver_diagonalPointFibreOverBase`:
  Artin's axiom [1] for every category fibred in groupoids equivalent over the site to `𝒴`, for
  instance the category fibred in sets of its functor of isomorphism classes `Y`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u vZ uZ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor of points of a scheme locally of finite presentation over `S` is limit
preserving** on the big fppf site of `S` (Stacks 01ZC): for a cofiltered inverse system of affine
schemes over `S` with limit `T`, the canonical map `colim Mor_S(Tᵢ, V) ⟶ Mor_S(T, V)` is
bijective. This is `AlgebraicGeometry.Scheme.preservesColimit_yoneda`, read through the fully
faithful functor from the big fppf site of `S` to all schemes over `S`. -/
@[ega "IV 17.3.2" "partial"]
theorem limitPreserving_yoneda_bigFppfOver_of_locallyOfFinitePresentation
    (V : BigFppfOver B S hS) (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS) (yoneda.obj V) := by
  intro I _ _ D c hc hDaff _
  have : IsConnected I := IsCofiltered.isConnected I
  let P := Over.post (X := B.obj hS) B.inclusion
  let hP : P.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful P
  have hcP : IsLimit (P.mapCone c) := isLimitOfReflects (Over.forget _) hc
  have : ∀ i, IsAffine ((D ⋙ P).obj i).left := hDaff
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom ((D ⋙ P).map g).left := fun _ => inferInstance
  have : ∀ i, CompactSpace ((D ⋙ P).obj i).left := fun _ => inferInstance
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ P).obj i).left := fun _ => inferInstance
  have : LocallyOfFinitePresentation (P.obj V).hom := hV
  obtain ⟨key⟩ := (Scheme.preservesColimit_yoneda (D ⋙ P) (P.obj V)).preserves hcP.op
  let e : P.op ⋙ yoneda.obj (P.obj V) ≅ yoneda.obj V :=
    NatIso.ofComponents (fun W => Equiv.toIso (hP.homEquiv (X := W.unop) (Y := V)).symm)
      (by
        intro W W' g
        ext x
        apply hP.map_injective
        simp [Functor.FullyFaithful.homEquiv])
  exact ⟨IsColimit.mapCoconeEquiv e key⟩

/-- **`(Sch/V)_{fppf}` is limit preserving** for a scheme `V` locally of finite presentation over
`S`, viewed over `(Sch/S)_{fppf}` through `Over.map V.hom`: it is equivalent over the site to the
category fibred in sets of the functor of points of `V`, which is limit preserving by Stacks
01ZC, and Section 07XZ turns that into limit preservation in the sense of Stacks 07XL. -/
theorem isLimitPreserving_schemeSlice
    (V : BigFppfOver B S hS) (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS (schemeSlice B S hS V) :=
  isLimitPreserving_of_equivalenceOver B S hS (schemeSlice B S hS V)
    (fibredCategory B S hS (yoneda.obj V)) (schemeSliceEquivalenceOver B S hS V)
    (isLimitPreserving_fibredCategory B S hS
      (limitPreserving_yoneda_bigFppfOver_of_locallyOfFinitePresentation B S hS V hV))

/-- **Axiom [1] in the proof of Stacks 07Y5.** Let `𝒳` be a limit preserving category fibred in
groupoids over `(Sch/S)_{fppf}`, `V` a scheme over `S` locally of finite presentation and `y` an
object of `𝒳 × 𝒳` over `V`. Every category fibred in groupoids equivalent over the site to
`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` — for instance the category fibred in sets of its functor
of isomorphism classes `Y` — is limit preserving.

This is Stacks 07XM, part (2), for the three factors `(Sch/V)_{fppf}`
(`AlgebraicGeometry.Stack.isLimitPreserving_schemeSlice`), `𝒳 × 𝒳`
(`AlgebraicGeometry.Stack.isLimitPreserving_product`) and `𝒳`, transported along the
equivalence by `AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver`. -/
theorem isLimitPreserving_of_equivalenceOver_diagonalPointFibreOverBase
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (V : BigFppfOver B S hS) (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
    (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)
    (𝒵 : CatFiberedInGroupoids.{u, vZ, u + 1, uZ} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := BigFppfOver B S hS)
      (diagonalPointFibreOverBase B S hS 𝒳 V y) 𝒵.val.p) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, uZ, vZ} B S hS 𝒵 :=
  isLimitPreserving_of_equivalenceOver B S hS 𝒵
    (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS (schemeSlice B S hS V)
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 (schemeSliceMap B S hS V y hy)
      (Bicategory.InducedBicategory.mkHom (diagonalBasedFunctor B S hS 𝒳)))
    e.symm
    (isLimitPreserving_twoFibreProduct B S hS (schemeSlice B S hS V)
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 (schemeSliceMap B S hS V y hy)
      (Bicategory.InducedBicategory.mkHom (diagonalBasedFunctor B S hS 𝒳))
      (isLimitPreserving_schemeSlice B S hS V hV) (isLimitPreserving_product B S hS 𝒳 h𝒳) h𝒳)

end AlgebraicGeometry.Stack

end
