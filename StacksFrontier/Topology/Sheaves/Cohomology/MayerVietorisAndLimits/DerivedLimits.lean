module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Functor.KanExtension.Precomposition
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Derived sections and derived inverse limits on a ringed space

Derived sections over an open of a ringed space commute with countable derived inverse
limits, and consequently the cohomology of such a derived limit sits in the Milnor short
exact sequence

`0 ⟶ R¹ lim Hᵐ⁻¹(U, Kₙ) ⟶ Hᵐ(U, R lim Kₙ) ⟶ lim Hᵐ(U, Kₙ) ⟶ 0`.

The first assertion is Stacks 08U1 applied to the additive-group-valued sections functor: the
only work is to convert its complex-level comparison map into the homotopy-category form that
08U1 expects, which is done by transporting the left-Kan-extension property along the
localisation of the homotopy category. The second assertion is then the long exact cohomology
sequence of the resulting derived-limit triangle, broken into short exact pieces by
identifying `lim` with the kernel of `1 - shift` on the product.

## Main results

* `Stacks.Cohomology.DerivedLimits.isDerivedLimit_map_derivedSections`: derived sections over
  an open carry a countable derived inverse limit to a derived inverse limit.
* `Stacks.Cohomology.DerivedLimits.exists_shortExact_limOne_cohomology_derivedLimit`: the
  Milnor short exact sequence for the cohomology of a derived limit over an open.
* `Stacks.Cohomology.DerivedLimits.exists_shortExact_limOne_cohomology_derivedLimit_family`:
  the same conclusion for a family of derived-sections functors indexed by the opens.
* `Stacks.Cohomology.DerivedLimits.isDerivedLimit_map_derivedSections_moduleCat` and
  `Stacks.Cohomology.DerivedLimits.exists_shortExact_limOne_cohomology_derivedLimit_moduleCat`:
  the module-valued forms, retaining the natural `𝒪_X(U)`-module structure.

## Implementation notes

Derived sections are represented by an arbitrary total right derived functor of the sections
functor over the chosen open, together with its comparison map and universal property, rather
than by a chosen model; a derived inverse limit is likewise represented by its defining
distinguished triangle. The term `R¹ lim` is the cokernel of the standard difference map on
the product of the cohomology groups, and the map to `lim` is characterised by all its
projections, which pins it down as the canonical map induced by the structural morphism of
the derived-limit triangle.

The Milnor sequence is extracted by `shortExact_of_derivedLimitTriangle`, which differs from
`DerivedCategory.isDerivedLimit_homology_shortExact` in taking the triangle's structural map
as an explicit argument instead of quantifying it existentially; that is what allows the
conclusion to be stated about the given map `p`.

The common universe for the space, the rings and the modules follows the existing
`structureSheafRing` and sheaves-of-modules interfaces.

## References

* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0BKQ](https://stacks.math.columbia.edu/tag/0BKQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedLimits

universe u u₁ v₁ w₁ u₂ v₂ w₂

attribute [local instance] HasDerivedCategory.standard

/-- Taking the inverse limit of an inverse system is additive. -/
local instance limitFunctor_additive {A : Type*} [Category A] [Preadditive A]
    [HasLimitsOfShape ℕᵒᵖ A] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive where
  map_add := limit.hom_ext fun _ => by simp

/-- Evaluating a sheaf of modules on an open is additive. -/
local instance sections_additive (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation (structureSheafRing X) (op U)).Additive where
  map_add := rfl

/-! ### The Milnor short exact sequence of an explicit derived-limit triangle -/

section Milnor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w₁} A]

/-- The product comparison morphism conjugates the difference map `1 - shift` of an inverse
system into the difference map of the inverse system of images. -/
private theorem map_pi_lift_sub_comp_piComparison
    {D : Type*} [Category D] [Preadditive D]
    {A' : Type*} [Category A'] [Preadditive A']
    (H : D ⥤ A') [H.Additive] (X : ℕ → D)
    [HasProduct X] [HasProduct fun n => H.obj (X n)] (τ : ∀ n, X (n + 1) ⟶ X n) :
    H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫ piComparison H X =
      piComparison H X ≫ Pi.lift fun n => Pi.π (fun n => H.obj (X n)) n -
        Pi.π (fun n => H.obj (X n)) (n + 1) ≫ H.map (τ n) := by
  have hLift : H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫
      piComparison H X = Pi.lift fun n =>
        H.map (Pi.π X n - Pi.π X (n + 1) ≫ τ n) := by
    refine Pi.hom_ext _ _ fun n => ?_
    rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]
  rw [hLift]
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
    piComparison_comp_π, H.map_sub, H.map_comp, ← Category.assoc,
    piComparison_comp_π]

/-- The Milnor short exact sequence attached to a derived-limit triangle whose structural map
is given explicitly. The cokernel of the degree-`m - 1` difference map is `R¹ lim`, and the
map to `lim` is characterised by its composites with the limit projections. -/
private theorem shortExact_of_derivedLimitTriangle
    (F : ℕᵒᵖ ⥤ DerivedCategory A) (K : DerivedCategory A)
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) b ∈ distTriang (DerivedCategory A))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := F ⋙ Hprev
    let Fcur := F ⋙ Hcur
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶
        (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶ Hcur.obj K)
      (q : Hcur.obj K ⟶ limit Fcur) (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map a ≫ Hcur.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n)) := by
  obtain ⟨-, i, q, w, -, -, hq, hS⟩ :=
    DerivedCategory.homology_shortExact_of_distinguished F K a b hT m
  exact ⟨i, q, w, hS, hq⟩

end Milnor

/-! ### Derived sections commute with derived limits -/

/-- Applying an additive-group-valued derived-sections functor to a derived-limit triangle
again gives a derived-limit triangle, with the image of the given structural map. -/
private theorem derivedSections_mappedTriangle
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison :
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) ⟶
          (RGamma.obj L)⟦(1 : ℤ)⟧,
        Triangle.mk
          (RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩))
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) (n + 1) ≫
                RGamma.map (K.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory AddCommGrpCat.{u}) := by
  let A := SheafOfModules.{u} (structureSheafRing X)
  let F := SheafOfModules.toSheaf (structureSheafRing X) ⋙
    (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj (op U)
  let _ : F.Additive := { map_add := rfl }
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    let e : (SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
        forget₂ (ModuleCat ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat) ≅ F :=
      NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl
    exact preservesLimitsOfShape_of_natIso (J := Discrete ℕ) e
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := AddCommGrpCat.{u})
  let eL := DerivedCategory.quotientCompQhIso A
  let eF : q ⋙ Fh ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := AddCommGrpCat.{u}) :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (C := AddCommGrpCat.{u}))
  let γ : q ⋙ Fh ⟶ (q ⋙ DerivedCategory.Qh (C := A)) ⋙ RGamma :=
    eF.hom ≫ comparison ≫ whiskerRight eL.inv RGamma
  let α : Fh ⟶ DerivedCategory.Qh (C := A) ⋙ RGamma :=
    ((whiskeringLeft _ _ _).obj q).preimage (γ ≫ (Functor.associator _ _ _).hom)
  have hαpre : whiskerLeft q α ≫ (Functor.associator _ _ _).inv = γ := by
    dsimp [α]
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have hγ : RGamma.IsLeftKanExtension γ := by
    have := hRGamma
    have hβ : RGamma.IsLeftKanExtension comparison :=
      Functor.IsRightDerivedFunctor.isLeftKanExtension RGamma comparison
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    let Lq := q ⋙ DerivedCategory.Qh (C := A)
    let e : Lq ⋙ 𝟭 _ ≅ DerivedCategory.Q (C := A) := (Functor.rightUnitor Lq).symm ≪≫ eL
    have hβ' : RGamma.IsLeftKanExtension
        (comparison ≫ whiskerRight e.inv RGamma ≫ (Functor.associator _ _ _).hom) :=
      (Functor.isLeftKanExtension_iff_postcomp₁
        (G := 𝟭 _) (e := e) (F' := RGamma) comparison).mp hβ
    exact (Functor.isLeftKanExtension_iff_of_iso₂ γ
      (comparison ≫ whiskerRight e.inv RGamma ≫
        (Functor.associator _ _ _).hom) eF (Iso.refl _) (by
        ext Y
        simp [γ, e, Lq, Category.assoc])).2 hβ'
  have hα : RGamma.IsLeftKanExtension α := by
    apply (isLeftKanExtension_iff_precomp_of_fullyFaithful q RGamma α).2
    rw [hαpre]
    simpa [γ, eL] using hγ
  let _ : RGamma.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := ⟨hα⟩
  exact Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor (F := F) RGamma α K L p hL

/-- **Stacks 0D60, first assertion.** Derived sections over an open carry a countable derived
inverse limit to a derived inverse limit. -/
@[stacks 0D60 "commutation with derived limits"]
theorem isDerivedLimit_map_derivedSections
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison :
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory AddCommGrpCat.{u}) _ _ _ _ _ _
        (K ⋙ RGamma) h (RGamma.obj L) := by
  obtain ⟨p, hL⟩ := hL
  obtain ⟨h, hT⟩ := derivedSections_mappedTriangle X U RGamma comparison hRGamma K L p hL
  exact ⟨h, _, hT⟩

/-- The Milnor short exact sequence for the image of a derived-limit triangle under a functor
of derived categories, given that the image triangle is distinguished. Both the
additive-group-valued and the module-valued forms of Stacks 0D60 are instances of this. -/
private theorem shortExact_limOne_of_mappedTriangle
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {A : Type u₂} [Category.{v₂} A] [Abelian A]
    [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w₂} A]
    (RGamma : DerivedCategory B ⥤ DerivedCategory A)
    (K : ℕᵒᵖ ⥤ DerivedCategory B) (L : DerivedCategory B)
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hmapped : ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) ⟶ (RGamma.obj L)⟦(1 : ℤ)⟧,
        Triangle.mk
          (RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩))
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) (n + 1) ≫
                RGamma.map (K.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory A))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let dprev := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶ Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) := by
  obtain ⟨hProduct, δ', hMappedTriangle⟩ := hmapped
  have hprodComp : HasProduct (fun n : ℕ ↦ (K ⋙ RGamma).obj (⟨n⟩ : ℕᵒᵖ)) := hProduct
  let mappedArrow := RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩)
  let Hcur := DerivedCategory.homologyFunctor A m
  obtain ⟨i, q, zero, hShort, hProjection⟩ :=
    shortExact_of_derivedLimitTriangle (A := A) (K ⋙ RGamma) (RGamma.obj L)
      mappedArrow δ' hMappedTriangle m
  refine ⟨i, q, zero, hShort, fun n => ?_⟩
  have hmap : mappedArrow ≫ Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n =
      RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) := by
    simp only [mappedArrow, Category.assoc, piComparison_comp_π, Functor.map_comp]
  exact ((hProjection n).trans (Hcur.map_comp _ _).symm).trans
    (congrArg Hcur.map hmap)

/-- **Stacks 0D60, second assertion.** For every open `U` and degree `m`, the cohomology of a
derived inverse limit lies in the Milnor short exact sequence
`0 ⟶ R¹ lim Hᵐ⁻¹(U,Kₙ) ⟶ Hᵐ(U,R lim Kₙ) ⟶ lim Hᵐ(U,Kₙ) ⟶ 0`.

Here `R¹ lim` is represented by the cokernel of the standard difference map on the product of
the underlying cohomology groups. The last map is characterized by its composites with the
limit projections, which are induced by the structural maps `L ⟶ Kₙ`. -/
@[stacks 0D60 "short exact sequence"]
theorem exists_shortExact_limOne_cohomology_derivedLimit
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (comparison :
      (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (m : ℤ) :
    let A := AddCommGrpCat.{u}
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let dprev := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶
        Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) :=
  shortExact_limOne_of_mappedTriangle RGamma K L p
    (derivedSections_mappedTriangle X U RGamma comparison hRGamma K L p hL) m

/-- **Stacks 0BKQ.** For a family of derived-sections functors indexed by the opens of a
ringed space, the cohomology of a derived inverse limit lies in the Milnor short exact
sequence over each open.

The last map is pinned down by its composites with the limit projections; they are the maps
on cohomology induced by the structural maps `L ⟶ Kₙ`.

This is the last assertion of the remark. Its first assertion, that the cohomology sheaves of
the system and of the derived limit are the sheafifications of the cohomology presheaves, and
the square of its diagram, are
`Stacks.Cohomology.DerivedLimits.sheafificationCohomologyPresheafSystemIso` and
`Stacks.Cohomology.DerivedLimits.cohomologyDerivedLimitDiagram`. -/
@[stacks 0BKQ "the short exact sequences of Equation 0BKR over each open U: \
0 → R¹ lim H^(m-1)(U, K_n) → H^m(U, R lim K_n) → lim H^m(U, K_n) → 0"]
theorem exists_shortExact_limOne_cohomology_derivedLimit_family
    (X : RingedSpace.{u, u})
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ => K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (RGamma : ∀ _U : Opens X.carrier,
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory AddCommGrpCat.{u})
    (comparison : ∀ U : Opens X.carrier,
      ((SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
            (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⟶ DerivedCategory.Q ⋙ RGamma U)
    (hRGamma : ∀ U : Opens X.carrier,
      (RGamma U).IsRightDerivedFunctor (comparison U)
        (HomologicalComplex.quasiIso
          (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)))
    (U : Opens X.carrier) (m : ℤ) :
    let Fprev := K ⋙ RGamma U ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)
    let Fcur := K ⋙ RGamma U ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} m
    let dprev := Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj ((RGamma U).obj L))
      (q : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj ((RGamma U).obj L) ⟶
        limit Fcur)
      (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
            ((RGamma U).map (p ≫ Pi.π (fun n : ℕ => K.obj ⟨n⟩) n))) :=
  exists_shortExact_limOne_cohomology_derivedLimit
    X U (RGamma U) (comparison U) (hRGamma U) K L p hL m

/-! ### The module-valued forms -/

/-- Applying a module-valued derived-sections functor to a derived-limit triangle again gives
a derived-limit triangle, with the image of the given structural map. The comparison map is
already given on the homotopy category here, so Stacks 08U1 applies directly. -/
private theorem derivedSections_mappedTriangle_moduleCat
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))))
    (comparison :
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) ⟶
          (RGamma.obj L)⟦(1 : ℤ)⟧,
        Triangle.mk
          (RGamma.map p ≫ piComparison RGamma (fun n : ℕ ↦ K.obj ⟨n⟩))
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)) (n + 1) ≫
                RGamma.map (K.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))) := by
  have _ := hRGamma
  exact Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (F := SheafOfModules.evaluation (structureSheafRing X) (op U)) RGamma comparison K L p hL

/-- **Stacks 0D60, first assertion, module-valued form.** Derived sections over an open, with
their natural module structure over the ring of sections, carry a countable derived inverse
limit to a derived inverse limit. -/
theorem isDerivedLimit_map_derivedSections_moduleCat
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))))
    (comparison :
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))) _ _ _ _ _ _
        (K ⋙ RGamma) h (RGamma.obj L) := by
  obtain ⟨p, hL⟩ := hL
  obtain ⟨h, hT⟩ :=
    derivedSections_mappedTriangle_moduleCat X U RGamma comparison hRGamma K L p hL
  exact ⟨h, _, hT⟩

/-- **Stacks 0D60, second assertion, module-valued form.** For every open `U` and degree `m`,
the cohomology of a derived inverse limit lies in the Milnor short exact sequence of
`𝒪_X(U)`-modules, with `R¹ lim` the cokernel of the standard difference map. -/
theorem exists_shortExact_limOne_cohomology_derivedLimit_moduleCat
    (X : RingedSpace.{u, u})
    (U : Opens X.carrier)
    (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))))
    (comparison :
      (SheafOfModules.evaluation (structureSheafRing X) (op U)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (m : ℤ) :
    let A := ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))
    let Hprev := DerivedCategory.homologyFunctor A (m - 1)
    let Hcur := DerivedCategory.homologyFunctor A m
    let Fprev := K ⋙ RGamma ⋙ Hprev
    let Fcur := K ⋙ RGamma ⋙ Hcur
    let dprev := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel dprev ⟶ Hcur.obj (RGamma.obj L))
      (q : Hcur.obj (RGamma.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      ((ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) :=
  shortExact_limOne_of_mappedTriangle RGamma K L p
    (derivedSections_mappedTriangle_moduleCat X U RGamma comparison hRGamma K L p hL) m

end Stacks.Cohomology.DerivedLimits

end
