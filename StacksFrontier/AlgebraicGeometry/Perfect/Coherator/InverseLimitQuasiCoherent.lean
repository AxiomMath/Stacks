module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CoheratorRevisited
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived limits of quasi-coherent sheaves and the coherator

Let `X` be a scheme and let `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a right adjoint of the inclusion
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. Being a right adjoint, `DQ_X` commutes with products, and being exact it
carries the distinguished triangle witnessing a derived limit to one of the same shape; so for an
inverse system `(𝓕ₙ)` in `D_QCoh(𝒪_X)` and `K = R lim 𝓕ₙ` computed in `D(𝒪_X)`, the object
`DQ_X(K)` is a derived limit of `(𝓕ₙ)` in `D_QCoh(𝒪_X)`.

The commutation is proved for an arbitrary exact right adjoint between pre-triangulated
categories, which is the only property of `DQ_X` the argument uses.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.map_of_isTriangulated`: an exact functor that
  preserves the product of an inverse system carries a derived limit of that system to a derived
  limit of the image system.
* `Stacks.Duality.Coherator.isDerivedLimit_coherator_obj`: **[Stacks, Tag 0CSB]** — the coherator
  of a derived limit taken in `D(𝒪_X)` is the derived limit taken in `D_QCoh(𝒪_X)`.

## Implementation notes

The coherator is supplied as an adjunction `(derivedQuasiCoherent X).ι ⊣ DQ` together with a
`Functor.CommShift ℤ` structure on `DQ` making the adjunction triangulated, which is exactly the
data produced by
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`, the form of
[Stacks, Tag 0CR0] which assumes only that `X` is quasi-compact and quasi-separated; no choice of
`DQ_X` is made here, and the statement below holds for every coherator. The inclusion
`(derivedQuasiCoherent X).ι` is fully faithful, so the unit of the adjunction is invertible and
the image system `(𝓕ₙ) ⋙ ι ⋙ DQ` is identified with `(𝓕ₙ)`.

Existence of the product of the image system is part of the conclusion rather than a hypothesis,
because `D_QCoh(𝒪_X)` is not closed under products inside `D(𝒪_X)`: its products are produced by
the right adjoint, which is what the preservation statement provides.

## References

* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated Opposite

universe w u

namespace CategoryTheory.Limits

/-- A functor preserving the product of an inverse system of objects of a category makes the
image system have a product. -/
theorem hasProduct_comp_of_preservesLimit {D : Type*} [Category* D] {D' : Type*} [Category* D']
    (G : D ⥤ D') (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ F.obj (op n)]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj (op n)) G] :
    HasProduct fun n : ℕ ↦ (F ⋙ G).obj (op n) :=
  have : HasLimit (Discrete.functor (fun n : ℕ ↦ F.obj (op n)) ⋙ G) :=
    ⟨_, isLimitOfPreserves G (limit.isLimit _)⟩
  hasLimit_of_iso (F := Discrete.functor (fun n : ℕ ↦ F.obj (op n)) ⋙ G)
    (Discrete.natIso fun _ ↦ Iso.refl _)

end CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

section Abstract

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type*} [Category* D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- **An exact functor commutes with derived limits it preserves the products of.** If `G` is
exact, `K = R lim Fₙ`, and `G` preserves the product of the `Fₙ`, then `G K = R lim G Fₙ`.

The image under `G` of the distinguished triangle `K ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ K⟦1⟧` is distinguished, and
transporting its two outer objects along `G(∏ Fₙ) ≅ ∏ G Fₙ` turns its middle map, the image of
the difference map of the system, into the difference map of the image system. -/
theorem IsDerivedLimit.map_of_isTriangulated (G : D ⥤ D') [G.CommShift ℤ] [G.IsTriangulated]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ F.obj (op n)]
    [HasProduct fun n : ℕ ↦ (F ⋙ G).obj (op n)]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ F.obj (op n)) G]
    {K : D} (hK : IsDerivedLimit F K) :
    IsDerivedLimit (F ⋙ G) (G.obj K) := by
  obtain ⟨p, δ, hT⟩ := hK
  have : HasProduct fun n : ℕ ↦ G.obj (F.obj (op n)) :=
    inferInstanceAs (HasProduct fun n : ℕ ↦ (F ⋙ G).obj (op n))
  let e : G.obj (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ≅ ∏ᶜ fun n : ℕ ↦ (F ⋙ G).obj (op n) :=
    PreservesProduct.iso G (fun n : ℕ ↦ F.obj (op n))
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ ↦ (F ⋙ G).obj (op n)) n =
      G.map (Pi.π (fun n : ℕ ↦ F.obj (op n)) n) :=
    piComparison_comp_π G (fun n : ℕ ↦ F.obj (op n)) n
  let b := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
    Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let b' := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (F ⋙ G).obj (op n)) n -
    Pi.π (fun n : ℕ ↦ (F ⋙ G).obj (op n)) (n + 1) ≫ (F ⋙ G).map (homOfLE (Nat.le_succ n)).op
  have hb : G.map b ≫ e.hom = e.hom ≫ b' := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, he, ← G.map_comp]
    simp only [b, b', Pi.lift_comp_π, G.map_sub, G.map_comp, Category.assoc,
      Preadditive.comp_sub, he]
    rw [← Category.assoc, he]
    rfl
  have hinv : b' ≫ e.inv = e.inv ≫ G.map b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]
  have hGT : Triangle.mk (G.map p) (G.map b)
      (G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D' :=
    G.map_distinguished (Triangle.mk p b δ) hT
  have hfin : Triangle.mk (G.map p ≫ e.hom) b'
      (e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D' :=
    isomorphic_distinguished _ hGT _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm (by simp [Triangle.mk])
        (by simpa [Triangle.mk] using hinv) (by simp [Triangle.mk]))
  exact ⟨G.map p ≫ e.hom, e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K, hfin⟩

end Abstract

end CategoryTheory.Pretriangulated

namespace Stacks.Duality.Coherator

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- **[Stacks, Tag 0CSB].** Let `X` be a scheme and let `DQ` be a right adjoint of the inclusion
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` which makes the adjunction triangulated. If `L` is a derived limit in
`D(𝒪_X)` of an inverse system `F` of objects of `D_QCoh(𝒪_X)`, then `DQ L` is a derived limit of
`F` in `D_QCoh(𝒪_X)`.

Right adjoints preserve products, so `DQ` preserves the product of the system; it is exact, so it
carries the triangle witnessing the derived limit to one of the same shape. The inclusion is fully
faithful, so the unit of the adjunction identifies `F ⋙ ι ⋙ DQ` with `F`. -/
@[stacks 0CSB "the identification DQ_X(R lim 𝓕ₙ) = (R lim in D_QCoh(𝒪_X))(𝓕ₙ), for every \
coherator DQ of X, i.e. every exact right adjoint of the inclusion; one exists on any \
quasi-compact quasi-separated scheme by Stacks 0CR0, \
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`"]
theorem isDerivedLimit_coherator_obj
    (DQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      (derivedQuasiCoherent X).FullSubcategory)
    (adj : (derivedQuasiCoherent X).ι ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]
    (F : ℕᵒᵖ ⥤ (derivedQuasiCoherent X).FullSubcategory)
    [HasProduct fun n : ℕ ↦ (F ⋙ (derivedQuasiCoherent X).ι).obj (op n)]
    (L : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hL : IsDerivedLimit (F ⋙ (derivedQuasiCoherent X).ι) L) :
    ∃ h : HasProduct fun n : ℕ ↦ F.obj (op n),
      letI := h
      IsDerivedLimit F (DQ.obj L) := by
  have : DQ.IsRightAdjoint := adj.isRightAdjoint
  have : HasProduct fun n : ℕ ↦
      ((F ⋙ (derivedQuasiCoherent X).ι) ⋙ DQ).obj (op n) :=
    hasProduct_comp_of_preservesLimit DQ (F ⋙ (derivedQuasiCoherent X).ι)
  let c : (F ⋙ (derivedQuasiCoherent X).ι) ⋙ DQ ≅ F :=
    Functor.associator F (derivedQuasiCoherent X).ι DQ ≪≫
      (Functor.isoWhiskerLeft F (asIso adj.unit)).symm ≪≫ F.rightUnitor
  have hF : HasProduct fun n : ℕ ↦ F.obj (op n) :=
    hasProduct_of_equiv_of_iso (f := fun n : ℕ ↦ ((F ⋙ (derivedQuasiCoherent X).ι) ⋙ DQ).obj (op n))
      _ (Equiv.refl ℕ) fun n ↦ (c.app (op n)).symm
  exact ⟨hF, IsDerivedLimit.of_natIso c
    (IsDerivedLimit.map_of_isTriangulated DQ (F ⋙ (derivedQuasiCoherent X).ι) hL)⟩

end Stacks.Duality.Coherator

end
