module

public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import Mathlib.Algebra.Category.Grp.AB
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an object of a ringed site and derived inverse limits

Let `(C, O)` be a ringed site, `U` an object of `C` and `(Kₙ)` an inverse system in the unbounded
derived category `D(O)` with derived limit `L`. Derived sections over `U` carry `L` to a derived
limit of the system of derived sections, and the degree-`m` cohomology of `RΓ(U, L)` therefore
sits in the canonical Milnor short exact sequence

`0 ⟶ R¹lim Hᵐ⁻¹(U, Kₙ) ⟶ Hᵐ(U, L) ⟶ lim Hᵐ(U, Kₙ) ⟶ 0`,

with `R¹lim` presented as the cokernel of the difference map on the product.

Both statements are instances of one fact about right derived functors, proved here first: a
right derived functor of an additive functor that preserves countable products carries a
derived-limit triangle to a derived-limit triangle (Tag 08U1), and the Milnor sequence of the
resulting triangle is then the general one. Nothing about sites enters either step; what the
ringed site supplies is that sections over `U` are additive and preserve countable products, and
that the sheaves of modules form a Grothendieck abelian category.

## Main results

* `Stacks.Cohomology.DerivedSectionsMilnor.exists_milnor_shortExact_of_rightDerived`: the Milnor
  short exact sequence for the image of a derived limit under any right derived functor, with its
  structural map and its projection both characterized.
* `Stacks.Cohomology.DerivedSectionsMilnor.isDerivedLimit_map_derivedSectionsOverObject`
  (Tag 0D6K, derived sections over an object commute with derived limits).
* `Stacks.Cohomology.DerivedSectionsMilnor.exists_shortExact_limOne_cohomology_derivedSections`
  (Tag 0D6K, short exact sequence over an object).

## Implementation notes

The target of derived sections is `D(AddCommGrpCat)`, following
`Stacks.Cohomology.Localization.derivedSectionsOverObject`, rather than
`D(ModuleCat (O(U)))`. Countable products are exact in `AddCommGrpCat`, which is what the Milnor
sequence needs, and the first derived inverse limit of a tower of abelian groups is already
stated there (`Rlim.firstDerivedLimit`), so no forgetful comparison is needed downstream. The
same theorem applied to `SheafOfModules.evaluation` instead of
`Stacks.Cohomology.Localization.sectionsOverObject` gives the module-valued form.

`IsGrothendieckAbelian` for the sheaves of modules is a hypothesis with its own universe, as in
Tags 0BKV and 0BKW: it is what supplies the K-injective resolutions that Tag 08U1 consumes. At
`RingedSite.{u, u, u}` it is inferred, so the declarations elaborate against the hypotheses of
the source with nothing added.

`R¹lim` is the cokernel of the difference map rather than a chosen right-derived-limit functor,
which avoids an arbitrary identification and is what lets the inclusion be characterized by the
connecting morphism of the triangle.

## References

* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.Localization

namespace Stacks.Cohomology.DerivedSectionsMilnor

universe w w₁ w₂ v₁ v₂ u₁ u₂ u v g

attribute [local instance] HasDerivedCategory.standard

section General

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [IsGrothendieckAbelian.{w} A]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B] [HasLimitsOfShape ℕᵒᵖ B]

/-- The Milnor short exact sequence for the image of a derived limit under a right derived
functor. The structural map of the image triangle is the image of the given one followed by the
canonical product comparison, so its composite with each projection is `RF.map (p ≫ πₙ)`; the
projection onto the inverse limit of cohomologies is characterized by the same data.

Tag 08U1 supplies the image triangle and
`DerivedCategory.exists_milnor_shortExact_of_distTriang` its Milnor sequence. -/
theorem exists_milnor_shortExact_of_rightDerived
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory A) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor B (m - 1)
    let Hcur := DerivedCategory.homologyFunctor B m
    let E := K ⋙ RF
    let Fprev := E ⋙ Hprev
    let Fcur := E ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
            Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩,
      letI := h
      ∃ (a : RF.obj L ⟶ ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)
        (b : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ⟶ (RF.obj L)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫
              E.map (homOfLE (Nat.le_succ n)).op) b
        T ∈ distTriang (DerivedCategory B) ∧
        (∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
          RF.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
          (i : cokernel dprev ⟶ Hcur.obj (RF.obj L))
          (q : Hcur.obj (RF.obj L) ⟶ limit Fcur)
          (zero : i ≫ q = 0),
          ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
            cokernel.π dprev ≫ i =
              ePrev.inv ≫ DerivedCategory.HomologySequence.δ T (m - 1) m ∧
            (ShortComplex.mk i q zero).ShortExact ∧
            ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
              Hcur.map (RF.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) := by
  intro Hprev Hcur E Fprev Fcur dprev
  obtain ⟨h0, δ', htri'⟩ :=
    Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α K L p hL
  have h : HasProduct (fun n : ℕ ↦ E.obj ⟨n⟩) := h0
  have hπ : ∀ n : ℕ,
      (RF.map p ≫ piComparison RF (fun n : ℕ ↦ K.obj ⟨n⟩)) ≫
        Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
      RF.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) := by
    intro n
    rw [Category.assoc, show piComparison RF (fun n : ℕ ↦ K.obj ⟨n⟩) ≫
        Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n = RF.map (Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) from
      piComparison_comp_π RF (fun n : ℕ ↦ K.obj ⟨n⟩) n, ← Functor.map_comp]
  refine ⟨h, RF.map p ≫ piComparison RF (fun n : ℕ ↦ K.obj ⟨n⟩), δ', htri', hπ, ?_⟩
  obtain ⟨ePrev, i, q, zero, he, hi, hq, hse⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_distTriang E (RF.obj L)
      (RF.map p ≫ piComparison RF (fun n : ℕ ↦ K.obj ⟨n⟩)) δ' htri' m
  refine ⟨ePrev, i, q, zero, he, hi, hse, fun n ↦ ?_⟩
  rw [hq n, ← Functor.map_comp, hπ n]

end General

section RingedSite

/-- Evaluating sheaves of modules at an object preserves countable products. -/
private theorem preservesLimitsOfShape_evaluation_discrete_nat (X : RingedSite.{u, u, u})
    (U : X.C) : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
  SheafOfModules.evaluationPreservesLimitsOfShape.{u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (D := Discrete ℕ) (op U)

/-- **Stacks Project Tag 0D6K.** Derived sections over an object of a ringed site carry a
derived inverse limit to a derived inverse limit.

Sections over an object are additive and preserve countable products, so Tag 08U1 applies. -/
@[stacks 0D6K "derived sections over an object commute with derived limits"]
theorem isDerivedLimit_map_derivedSectionsOverObject (X : RingedSite.{u, u, u}) (U : X.C)
    [HasSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct fun n : ℕ ↦ (K ⋙ derivedSectionsOverObject X U).obj ⟨n⟩,
      letI := h
      IsDerivedLimit (K ⋙ derivedSectionsOverObject X U)
        ((derivedSectionsOverObject X U).obj L) := by
  have := preservesLimitsOfShape_evaluation_discrete_nat X U
  obtain ⟨p, δ, htri⟩ := hL
  obtain ⟨h0, δ', htri'⟩ :=
    Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor (sectionsOverObject X U)
      (derivedSectionsOverObject X U)
      ((homotopySectionsOverObject X U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
      K L p ⟨δ, htri⟩
  refine ⟨h0, (derivedSectionsOverObject X U).map p ≫
    piComparison (derivedSectionsOverObject X U) (fun n : ℕ ↦ K.obj ⟨n⟩), δ', htri'⟩

/-- **Stacks Project Tag 0D6K.** The canonical Milnor short exact sequence for cohomology over
an object of a ringed site: the first derived inverse limit of the degree-`m - 1` cohomologies
includes into the degree-`m` cohomology of derived sections of the derived limit, with quotient
the inverse limit of the degree-`m` cohomologies. -/
@[stacks 0D6K "short exact sequence over an object"]
theorem exists_shortExact_limOne_cohomology_derivedSections (X : RingedSite.{u, u, u}) (U : X.C)
    [HasSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let RG := derivedSectionsOverObject X U
    let Hprev := DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)
    let Hcur := DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    let E := K ⋙ RG
    let Fprev := E ⋙ Hprev
    let Fcur := E ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) :=
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
            Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩,
      letI := h
      ∃ (a : RG.obj L ⟶ ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)
        (b : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ⟶ (RG.obj L)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫
              E.map (homOfLE (Nat.le_succ n)).op) b
        T ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) ∧
        (∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
          RG.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
          (i : cokernel dprev ⟶ Hcur.obj (RG.obj L))
          (q : Hcur.obj (RG.obj L) ⟶ limit Fcur)
          (zero : i ≫ q = 0),
          ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
            cokernel.π dprev ≫ i =
              ePrev.inv ≫ DerivedCategory.HomologySequence.δ T (m - 1) m ∧
            (ShortComplex.mk i q zero).ShortExact ∧
            ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
              Hcur.map (RG.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :=
  have := preservesLimitsOfShape_evaluation_discrete_nat X U
  exists_milnor_shortExact_of_rightDerived (sectionsOverObject X U)
    (derivedSectionsOverObject X U)
    ((homotopySectionsOverObject X U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
    K L p hL m

end RingedSite

end Stacks.Cohomology.DerivedSectionsMilnor

end
