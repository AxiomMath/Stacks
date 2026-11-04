module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorsorsAndColimits.DerivedSections
public import StacksCore.Tactic.StacksAttribute

/-!
# `RΓ(C, -)` on the unbounded derived category of a ringed site

Let `(C, O)` be a ringed site. This file constructs the total right derived functor

`RΓ(C, -) : D(O) ⥤ D(Γ(C, O)-Mod)`

of global sections on the *whole* unbounded derived category of `O`-modules, and deduces the
two assertions of [Stacks, Tag 0D6K] about the whole site for it: `RΓ(C, -)` commutes with
`Rlim`, and the cohomology of a derived limit sits in the canonical Milnor short exact
sequence

`0 ⟶ R¹lim Hᵐ⁻¹(C, Kₙ) ⟶ Hᵐ(C, Rlim Kₙ) ⟶ lim Hᵐ(C, Kₙ) ⟶ 0`,

with `R¹lim` presented as the cokernel of the difference map on the product.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalSections.globalSectionsOnHomotopy`: degreewise global
  sections on the homotopy category of complexes of `O`-modules, followed by the localization
  to the derived category of `Γ(C, O)`-modules.
* `Stacks.Cohomology.DerivedGlobalSections.derivedGlobalSections`: the functor `RΓ(C, -)` on
  the unbounded derived category `D(O)`, as the total right derived functor of the previous
  one along `DerivedCategory.Qh`.
* `Stacks.Cohomology.DerivedGlobalSections.derivedGlobalSectionsUnit`: its unit
  `Γ(C, -) ⟶ Qh ⋙ RΓ(C, -)`, which exhibits it as that right derived functor.

## Main results

* `Stacks.Cohomology.DerivedGlobalSections.isDerivedLimit_map_derivedGlobalSections`
  (Tag 0D6K, global derived sections commute with derived limits).
* `DerivedGlobalSections.exists_shortExact_limOne_cohomology_derivedGlobalSections`
  (Tag 0D6K, short exact sequence over the whole site).

## Implementation notes

`Stacks.Cohomology.isDerivedLimit_map_derivedGlobalSections` and
`Stacks.Cohomology.exists_shortExact_limOne_cohomology_derivedGlobalSections` take the derived
functor, its comparison and its universal property as data. The content added here is that
this data exists unconditionally: sheaves of `O`-modules in the ambient universe form a
Grothendieck abelian category (`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`), so
every complex of them admits a K-injective resolution, and Spaltenstein's theorem
([Stacks, Tag 070K]) gives a right derived functor of *any* functor out of the homotopy
category — in particular of global sections — on the whole unbounded derived category. No
boundedness, no countable-product exactness and no choice of resolution enters.

The module universe is the ambient `max u v w z`, which is exactly the universe in which the
Grothendieck abelian property of `SheafOfModules` is available; consequently the two
statements below carry no instance hypothesis beyond the ringed site itself.

## References

* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology.DerivedGlobalSections

universe u v w z

variable (X : RingedSite.{u, v, w})

attribute [local instance] HasDerivedCategory.standard

/-- Degreewise global sections of a complex of `O`-modules, on the homotopy category, followed
by the localization to the derived category of `Γ(C, O)`-modules. This is the functor whose
total right derived functor is `RΓ(C, -)`. -/
public noncomputable abbrev globalSectionsOnHomotopy :
    HomotopyCategory (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{max u v w z}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) :=
  letI := globalSectionsFunctor_additive.{u, v, w, max u v w z}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  (globalSectionsFunctor.{u, v, w, max u v w z}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **`RΓ(C, -)` on the unbounded derived category of a ringed site**: the total right derived
functor of global sections of `O`-modules, defined on all of `D(O)`. -/
public noncomputable abbrev derivedGlobalSections :
    DerivedCategory (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{max u v w z}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) :=
  (globalSectionsOnHomotopy.{u, v, w, z} X).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The unit `Γ(C, -) ⟶ Qh ⋙ RΓ(C, -)` of the derived global sections functor. -/
public noncomputable abbrev derivedGlobalSectionsUnit :
    globalSectionsOnHomotopy.{u, v, w, z} X ⟶
      DerivedCategory.Qh ⋙ derivedGlobalSections.{u, v, w, z} X :=
  (globalSectionsOnHomotopy.{u, v, w, z} X).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- **Stacks Project, Tag 0D6K.** `RΓ(C, -)` commutes with `Rlim`: global derived sections of
a ringed site carry a derived inverse limit to a derived inverse limit. -/
@[stacks 0D6K "global derived sections commute with derived limits"]
public theorem isDerivedLimit_map_derivedGlobalSections
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedGlobalSections.{u, v, w, z} X).obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (ModuleCat.{max u v w z}
          (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))
        _ _ _ _ _ _ (K ⋙ derivedGlobalSections.{u, v, w, z} X) h
        ((derivedGlobalSections.{u, v, w, z} X).obj L) :=
  Stacks.Cohomology.isDerivedLimit_map_derivedGlobalSections X
    (derivedGlobalSections.{u, v, w, z} X) (derivedGlobalSectionsUnit.{u, v, w, z} X)
    inferInstance K L hL

/-- **Stacks Project, Tag 0D6K.** The canonical Milnor short exact sequence for the cohomology
of the whole ringed site: the first derived inverse limit of the degree-`m - 1` cohomologies
includes into the degree-`m` cohomology of `RΓ(C, Rlim Kₙ)`, with quotient the inverse limit
of the degree-`m` cohomologies. -/
@[stacks 0D6K "short exact sequence over the whole site"]
public theorem exists_shortExact_limOne_cohomology_derivedGlobalSections
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory
          (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let RGamma := derivedGlobalSections.{u, v, w, z} X
    let A := ModuleCat.{max u v w z}
      (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let E := K ⋙ RGamma
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶
        (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩),
      letI := h
      ∃ (a : RGamma.obj L ⟶ ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)
        (b : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ⟶ (RGamma.obj L)⟦(1 : ℤ)⟧),
      let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫
            E.map (homOfLE (Nat.le_succ n)).op) b
      T ∈ distTriang (DerivedCategory A) ∧
      (∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
        RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅
          ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
        (i : cokernel dprev ⟶ Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      (ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
        cokernel.π dprev ≫ i =
          ePrev.inv ≫ (DerivedCategory.homologyFunctor A 0).homologySequenceδ
            T (m - 1) m (by omega) ∧
        (ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) :=
  Stacks.Cohomology.exists_shortExact_limOne_cohomology_derivedGlobalSections X
    (derivedGlobalSections.{u, v, w, z} X) (derivedGlobalSectionsUnit.{u, v, w, z} X)
    inferInstance K L p hL m

/-! ### `RΓ(U, -)` for an object `U` of the site -/

section OverObject

variable (U : X.Cᵒᵖ)

/-- Evaluation of sheaves of `O`-modules at `U` is an additive functor. -/
noncomputable local instance evaluation_additive :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U :
      SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        ModuleCat.{max u v w z}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)).Additive where
  map_add := rfl

/-- Degreewise sections over `U` of a complex of `O`-modules, on the homotopy category,
followed by the localization to the derived category of `O(U)`-modules. -/
public noncomputable abbrev sectionsOnHomotopy :
    HomotopyCategory (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (ModuleCat.{max u v w z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) :=
  (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- **`RΓ(U, -)` on the unbounded derived category of a ringed site**: the total right derived
functor of sections over `U`, defined on all of `D(O)`. -/
public noncomputable abbrev derivedSections :
    DerivedCategory (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory
        (ModuleCat.{max u v w z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) :=
  (sectionsOnHomotopy.{u, v, w, z} X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The unit `Γ(U, -) ⟶ Qh ⋙ RΓ(U, -)` of the derived sections functor. -/
public noncomputable abbrev derivedSectionsUnit :
    sectionsOnHomotopy.{u, v, w, z} X U ⟶
      DerivedCategory.Qh ⋙ derivedSections.{u, v, w, z} X U :=
  (sectionsOnHomotopy.{u, v, w, z} X U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- **Stacks Project, Tag 0D6K.** `RΓ(U, -)` commutes with `Rlim`: derived sections over an
object of a ringed site carry a derived inverse limit to a derived inverse limit. -/
@[stacks 0D6K "derived sections over an object commute with derived limits"]
public theorem isDerivedLimit_map_derivedSections
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedSections.{u, v, w, z} X U).obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory
          (ModuleCat.{max u v w z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
        _ _ _ _ _ _ (K ⋙ derivedSections.{u, v, w, z} X U) h
        ((derivedSections.{u, v, w, z} X U).obj L) :=
  have : HasSheafify X.J AddCommGrpCat.{max u v w z} :=
    site_hasSheafify_addCommGrp.{u, v, max w z}
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w z} :=
    site_wEqualsLocallyBijective_addCommGrp.{u, v, max w z}
  Stacks.Cohomology.isDerivedLimit_map_derivedSections X U
    (derivedSections.{u, v, w, z} X U) (derivedSectionsUnit.{u, v, w, z} X U)
    inferInstance K L hL

/-- **Stacks Project, Tag 0D6K.** The canonical Milnor short exact sequence for the cohomology
over an object `U` of a ringed site: the first derived inverse limit of the degree-`m - 1`
cohomologies includes into the degree-`m` cohomology of `RΓ(U, Rlim Kₙ)`, with quotient the
inverse limit of the degree-`m` cohomologies. -/
@[stacks 0D6K "short exact sequence over an object"]
public theorem exists_shortExact_limOne_cohomology_derivedSections
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory
          (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let RGamma := derivedSections.{u, v, w, z} X U
    let A := ModuleCat.{max u v w z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let E := K ⋙ RGamma
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶
        (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩),
      letI := h
      ∃ (a : RGamma.obj L ⟶ ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)
        (b : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ⟶ (RGamma.obj L)⟦(1 : ℤ)⟧),
      let T := Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫
            E.map (homOfLE (Nat.le_succ n)).op) b
      T ∈ distTriang (DerivedCategory A) ∧
      (∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
        RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅
          ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
        (i : cokernel dprev ⟶ Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      (ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
        cokernel.π dprev ≫ i =
          ePrev.inv ≫ (DerivedCategory.homologyFunctor A 0).homologySequenceδ
            T (m - 1) m (by omega) ∧
        (ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) :=
  have : HasSheafify X.J AddCommGrpCat.{max u v w z} :=
    site_hasSheafify_addCommGrp.{u, v, max w z}
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w z} :=
    site_wEqualsLocallyBijective_addCommGrp.{u, v, max w z}
  Stacks.Cohomology.exists_shortExact_limOne_cohomology_derivedSections X U
    (derivedSections.{u, v, w, z} X U) (derivedSectionsUnit.{u, v, w, z} X U)
    inferInstance K L p hL m

end OverObject

end Stacks.Cohomology.DerivedGlobalSections

end
