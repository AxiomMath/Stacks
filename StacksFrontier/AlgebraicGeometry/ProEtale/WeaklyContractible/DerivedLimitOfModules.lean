module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.MilnorSequence

/-!
# Derived limits of inverse systems of modules on a weakly contractible site

On a ringed site carrying a covering collection of weakly contractible objects, let `(Fₙ)` be a
countable inverse system of sheaves of modules and let `L` be a derived limit of the system of
the `Fₙ` placed in degree zero. Then `Rᵖ lim Fₙ = Hᵖ(L)` vanishes outside degrees `0` and `1`,
and `R¹ lim Fₙ` is the cokernel of the difference map `1 - shift` on `∏ₙ Fₙ`. This is
Stacks 0947(6).

Both statements come from the Milnor short exact sequences of Stacks 0947(7): the inverse system
in the derived category is `Fₙ[0]`, whose cohomology sheaves are `Fₙ` in degree zero and zero
elsewhere, so in each degree one of the two outer terms of the Milnor sequence vanishes.

## Main results

* `Stacks.WeaklyContractible.isZero_homology_of_isDerivedLimit_single`: **Stacks 0947(6)**,
  `Rᵖ lim Fₙ = 0` for `p ∉ {0, 1}`, in particular for `p > 1`.
* `Stacks.WeaklyContractible.nonempty_cokernel_iso_homology_one_of_isDerivedLimit_single`:
  **Stacks 0947(6)**, `R¹ lim Fₙ` is the cokernel of `1 - shift` on `∏ₙ Fₙ`.

## Implementation notes

The vanishing is stated for every degree other than `0` and `1`, which is stronger than the
source's `p > 1` and costs nothing: the argument is the same in both directions.

The cokernel comparison is stated as `Nonempty (_ ≅ _)` rather than as a constructed
isomorphism. A derived limit is determined only up to non-unique isomorphism, and the triangle
presenting `L` as one is existentially quantified by
`CategoryTheory.Pretriangulated.IsDerivedLimit`, so there is no canonical comparison to name;
what the source asserts is exactly the existence of the isomorphism.

In the Milnor sequence of degree `r` the outer terms are built from the cohomology system in
degrees `r - 1` and `r`. At `r = 1` the degree-`r - 1` system is the system `Hᵖ⁻¹(Fₙ[0])`, which
is isomorphic to `(Fₙ)` itself rather than equal to it; the cokernels of the two difference maps
are identified by `cokernel_iso_of_natIso`, which transports the difference map along
`CategoryTheory.Limits.Pi.mapIso`.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (6)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u t

namespace Stacks.WeaklyContractible

/-- The cohomology of an object placed in degree zero vanishes in every nonzero degree. -/
private theorem isZero_homology_singleFunctor_obj
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] (M : A) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor A q).obj
      ((DerivedCategory.singleFunctor A 0).obj M)) :=
  IsZero.of_iso
    (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 M q hq).isZero_homology
    ((DerivedCategory.homologyFunctorFactors A q).app ((CochainComplex.singleFunctor A 0).obj M))

/-- An isomorphism of countable inverse systems identifies the cokernels of their difference
maps `1 - shift`. -/
private theorem cokernel_iso_of_natIso {A : Type*} [Category* A] [Abelian A]
    [HasProductsOfShape ℕ A] {X Y : ℕᵒᵖ ⥤ A} (α : X ≅ Y) :
    Nonempty (cokernel (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) (n + 1) ≫ X.map (homOfLE (Nat.le_succ n)).op) ≅
      cokernel (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Y.obj ⟨n⟩) (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op)) := by
  refine ⟨cokernel.mapIso _ _ (Pi.mapIso fun n : ℕ ↦ α.app ⟨n⟩)
    (Pi.mapIso fun n : ℕ ↦ α.app ⟨n⟩) ?_⟩
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π, Iso.app_hom,
    Preadditive.sub_comp, Preadditive.comp_sub,
    reassoc_of% (Pi.mapIso_hom_π (fun n : ℕ ↦ α.app ⟨n⟩) (n + 1))]
  congr 1
  exact congrArg (Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) (n + 1) ≫ ·)
    (α.hom.naturality (homOfLE (Nat.le_succ n)).op)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

-- As in `MilnorSequence.lean`: countable products in `D(O)` are a theorem here, Stacks 0947(4)
-- through 07KC(1), so naming a derived limit of the system below needs no instance argument.
attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- **Stacks 0947(6).** On a ringed site with a covering collection of weakly contractible
objects, the derived limit of a countable inverse system `(Fₙ)` of sheaves of modules has no
cohomology outside degrees `0` and `1`: `Rᵖ lim Fₙ = 0` for every `p ≠ 0, 1`, in particular for
every `p > 1`. -/
@[stacks 0947 "(6), vanishing of the higher derived limits"]
theorem isZero_homology_of_isDerivedLimit_single
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)]
    (G : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O)
    (L : DerivedCategory (SheafOfModules.{t} S.O))
    (hL : IsDerivedLimit (G ⋙ DerivedCategory.singleFunctor (SheafOfModules.{t} S.O) 0) L)
    (p : ℤ) (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) p).obj L) := by
  obtain ⟨a, b, hT, h⟩ :=
    exists_milnor_shortExact_of_weaklyContractibleObjectsSituation S _ L hL
  obtain ⟨e, i, q, w, he, hi, hq, hse⟩ := h p
  refine isZero_X₂_of_shortExact hse (isZero_cokernel_of_isZero ?_ _) ?_
  · exact isZero_limit_of_forall_isZero _ fun _ ↦
      isZero_homology_singleFunctor_obj _ (by omega : p - 1 ≠ 0)
  · exact isZero_limit_of_forall_isZero _ fun _ ↦ isZero_homology_singleFunctor_obj _ hp₀

/-- **Stacks 0947(6).** On a ringed site with a covering collection of weakly contractible
objects, the first derived limit of a countable inverse system `(Fₙ)` of sheaves of modules is
the cokernel of the difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product `∏ₙ Fₙ`. -/
@[stacks 0947 "(6), R¹lim as a cokernel"]
theorem nonempty_cokernel_iso_homology_one_of_isDerivedLimit_single
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)]
    (G : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O)
    (L : DerivedCategory (SheafOfModules.{t} S.O))
    (hL : IsDerivedLimit (G ⋙ DerivedCategory.singleFunctor (SheafOfModules.{t} S.O) 0) L) :
    Nonempty (cokernel (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) 1).obj L) := by
  obtain ⟨a, b, hT, h⟩ :=
    exists_milnor_shortExact_of_weaklyContractibleObjectsSituation S _ L hL
  obtain ⟨e, i, q, w, he, hi, hq, hse⟩ := h 1
  have h₃ : IsZero (limit ((G ⋙ DerivedCategory.singleFunctor (SheafOfModules.{t} S.O) 0) ⋙
      DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) 1)) :=
    isZero_limit_of_forall_isZero _ fun _ ↦ isZero_homology_singleFunctor_obj _ one_ne_zero
  have : Mono i := hse.mono_f
  have : Epi i := hse.exact.epi_f (h₃.eq_zero_of_tgt q)
  have : IsIso i := isIso_of_mono_of_epi i
  obtain ⟨φ⟩ := cokernel_iso_of_natIso
    (G.rightUnitor.symm ≪≫
      (Functor.isoWhiskerLeft G
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{t} S.O) 0)).symm ≪≫
      (Functor.associator G (DerivedCategory.singleFunctor (SheafOfModules.{t} S.O) 0)
        (DerivedCategory.homologyFunctor (SheafOfModules.{t} S.O) 0)).symm)
  exact ⟨φ ≪≫ asIso i⟩

end Stacks.WeaklyContractible

end
