module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# Derived sections of a ringed site and derived inverse limits

Derived sections over an object of a ringed site, and global derived sections over the whole
site, carry derived inverse limits to derived inverse limits. Their cohomology therefore fits
into the canonical Milnor short exact sequence.

## Main results

* `Stacks.Cohomology.isDerivedLimit_map_derivedSections` and
  `Stacks.Cohomology.isDerivedLimit_map_derivedGlobalSections`: derived sections over an object,
  respectively over the whole site, commute with derived inverse limits.
* `Stacks.Cohomology.exists_shortExact_limOne_cohomology_derivedSections` and
  `Stacks.Cohomology.exists_shortExact_limOne_cohomology_derivedGlobalSections`: the canonical
  Milnor short exact sequence for the cohomology of a derived limit of sections.

## Implementation notes

An arbitrary total right derived functor with its comparison and universal property represents
each derived-sections functor. A derived limit is specified by its distinguished product
triangle. The first derived inverse limit is represented by the cokernel of the canonical
`1 - shift` map on the product of a tower. In each sequence the projection onto the ordinary
limit is characterized by its components. The inclusion is characterized, after the standard
comparison of first derived inverse limit with the cokernel of the difference map, by the
connecting morphism of the derived-limit triangle.

The results for sections over an object allow an independent module universe, with
sheafification and the Grothendieck abelian property supplied explicitly for that category.

## References

* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology

universe u v w z g

variable (X : RingedSite.{u, v, w})

attribute [local instance] HasDerivedCategory.standard

noncomputable local instance evaluation_additive_ringSheaf (U : X.Cᵒᵖ) :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U :
      SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)).Additive where
  map_add := rfl

section Auxiliary

universe uG uA uB vA vB wA wB

/-- The comparison morphism `H(∏ Yₙ) ⟶ ∏ H(Yₙ)` carries the image of a `Pi.lift` to the
`Pi.lift` of the images. -/
private theorem map_piLift_comp_piComparison
    {D : Type uA} {E : Type uB} [Category.{vA} D] [Category.{vB} E]
    (H : D ⥤ E) (Y : ℕ → D) [HasProduct Y]
    [HasProduct fun n ↦ H.obj (Y n)] {Z : D} (w : ∀ n, Z ⟶ Y n) :
    H.map (Pi.lift w) ≫ piComparison H Y = Pi.lift (fun n ↦ H.map (w n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_π, Pi.lift_π]

/-- The comparison morphism `H(∏ Yₙ) ⟶ ∏ H(Yₙ)` conjugates the map `1 - shift` of an inverse
system into the map `1 - shift` of the inverse system of the images. -/
private theorem map_piLift_sub_comp_piComparison
    {D : Type uA} {E : Type uB} [Category.{vA} D] [Category.{vB} E]
    [Preadditive D] [Preadditive E]
    (H : D ⥤ E) [H.Additive] (Y : ℕ → D)
    [HasProduct Y] [HasProduct fun n ↦ H.obj (Y n)]
    (τ : ∀ n, Y (n + 1) ⟶ Y n) :
    H.map (Pi.lift fun n ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ τ n) ≫
        piComparison H Y =
      piComparison H Y ≫ Pi.lift (fun n ↦
        Pi.π (fun n ↦ H.obj (Y n)) n -
          Pi.π (fun n ↦ H.obj (Y n)) (n + 1) ≫ H.map (τ n)) := by
  rw [map_piLift_comp_piComparison]
  apply Pi.hom_ext
  intro n
  rw [Pi.lift_π, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    piComparison_comp_π, H.map_sub, H.map_comp, ← Category.assoc,
    piComparison_comp_π]

/-- A right derived functor carries a derived-limit triangle to a derived-limit triangle whose
structural map has the image of the original projections as its components. -/
private theorem rightDerivedMapDerivedLimitTriangle
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [IsGrothendieckAbelian.{uG} A] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory A)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
          K.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A)) :
    ∃ h : HasProduct (fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)),
      letI := h
      ∃ (a : RF.obj L ⟶ ∏ᶜ fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩))
        (b : (∏ᶜ fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)) ⟶ (RF.obj L)⟦(1 : ℤ)⟧),
        Triangle.mk a
          (Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)) n -
              (Pi.π (fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)) (n + 1) ≫
                RF.map (K.map (homOfLE (Nat.le_succ n)).op))) b ∈
          distTriang (DerivedCategory B) ∧
        ∀ n : ℕ, a ≫ Pi.π (fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)) n =
          RF.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) := by
  obtain ⟨h, b, hT'⟩ :=
    Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α K L p ⟨δ, hT⟩
  refine ⟨h, RF.map p ≫ piComparison RF (fun n : ℕ ↦ K.obj ⟨n⟩), b, hT', fun n ↦ ?_⟩
  rw [Category.assoc, piComparison_comp_π, ← RF.map_comp]

/-- A right derived functor carries a derived limit to a derived limit. -/
private theorem isDerivedLimit_map_rightDerived
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [IsGrothendieckAbelian.{uG} A] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory A) (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RF.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit (DerivedCategory B) _ _ _ _ _ _ (K ⋙ RF) h (RF.obj L) := by
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨h, a, b, hT', -⟩ := rightDerivedMapDerivedLimitTriangle F RF α K L p δ hT
  exact ⟨h, a, b, hT'⟩

/-- Global sections of sheaves of modules preserve countable products. -/
private theorem globalSectionsFunctor_preservesCountableProducts
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) :
    PreservesLimitsOfShape (Discrete ℕ)
      (globalSectionsFunctor.{u, v, w, max u v w z} R) := by
  let G := forget (ModuleCat.{max u v w z} (RingCat.sectionsSubring R.obj))
  let post := (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{max u v w z}
      (Type (max u v w z))).obj (forget AddCommGrpCat.{max u v w z})
  let F := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙ post ⋙
    Functor.sectionsFunctor.{v, max u v w z} Cᵒᵖ
  have hsections : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.sectionsFunctor R) := by
    show PreservesLimitsOfShape (Discrete ℕ) F
    have : PreservesLimitsOfShape (Discrete ℕ) (Functor.sectionsFunctor.{v, max u v w z} Cᵒᵖ) :=
      preservesLimitsOfShape_of_natIso
        (sectionsFunctorNatIsoCoyoneda.{v, u, max u v w z} (C := Cᵒᵖ) PUnit.{max u v w z + 1}).symm
    infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ)
      (globalSectionsFunctor.{u, v, w, max u v w z} R ⋙ G) :=
    preservesLimitsOfShape_of_natIso (globalSectionsFunctorForget.{u, v, w, max u v w z} R).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (globalSectionsFunctor.{u, v, w, max u v w z} R) G

/-- The Milnor short exact sequence for the cohomology of a derived limit, for a *given*
derived-limit triangle. The inclusion descends the connecting morphism of the triangle through
the cokernel of `1 - shift` in degree `r - 1`, and the projection to the inverse limit is
characterized by its composites with the limit projections. -/
private theorem derivedLimitMilnorSequence
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{wA} A]
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K : DerivedCategory A)
    (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) b ∈ distTriang (DerivedCategory A))
    (r : ℤ) :
    let H := DerivedCategory.homologyFunctor A r
    let Hprev := DerivedCategory.homologyFunctor A (r - 1)
    let homologySystem := F ⋙ H
    let X : ℕ → DerivedCategory A := fun n ↦ F.obj ⟨n⟩
    let P := ∏ᶜ fun n : ℕ ↦ Hprev.obj (X n)
    let dprev : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Hprev.obj (X n)) n -
        Pi.π (fun n : ℕ ↦ Hprev.obj (X n)) (n + 1) ≫
          Hprev.map (F.map (homOfLE (Nat.le_succ n)).op)
    ∃ (ePrev : Hprev.obj (∏ᶜ X) ≅ P)
      (i : cokernel dprev ⟶ H.obj K)
      (q : H.obj K ⟶ limit homologySystem)
      (zero : i ≫ q = 0),
      ePrev.hom = piComparison Hprev X ∧
        cokernel.π dprev ≫ i = ePrev.inv ≫
          (DerivedCategory.homologyFunctor A 0).homologySequenceδ
            (Triangle.mk a (Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
                Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
                  F.map (homOfLE (Nat.le_succ n)).op) b)
            (r - 1) r (by omega) ∧
        (ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π homologySystem ⟨n⟩ =
          H.map a ≫ H.map (Pi.π X n) := by
  let X : ℕ → DerivedCategory A := fun n ↦ F.obj ⟨n⟩
  let H := DerivedCategory.homologyFunctor A r
  let Hprev := DerivedCategory.homologyFunctor A (r - 1)
  let homologySystem := F ⋙ H
  let P := ∏ᶜ fun n : ℕ ↦ Hprev.obj (X n)
  let dprev := Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ Hprev.obj (X n)) n -
      Pi.π (fun n : ℕ ↦ Hprev.obj (X n)) (n + 1) ≫
        Hprev.map (F.map (homOfLE (Nat.le_succ n)).op)
  let dcur := Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ H.obj (X n)) n -
      Pi.π (fun n : ℕ ↦ H.obj (X n)) (n + 1) ≫
        H.map (F.map (homOfLE (Nat.le_succ n)).op)
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X (r - 1)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X r
  let ePrev := asIso (piComparison Hprev X)
  let eCur := asIso (piComparison H X)
  let T := Triangle.mk a
    (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫
      F.map (homOfLE (Nat.le_succ n)).op) b
  let c := DerivedCategory.HomologySequence.δ T (r - 1) r
  have hdPrev : Hprev.map T.mor₂ ≫ ePrev.hom = ePrev.hom ≫ dprev := by
    dsimp [T, ePrev, dprev]
    exact map_piLift_sub_comp_piComparison Hprev X
      (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  have hdCur : H.map T.mor₂ ≫ eCur.hom = eCur.hom ≫ dcur := by
    dsimp [T, eCur, dcur]
    exact map_piLift_sub_comp_piComparison H X
      (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  have hc : dprev ≫ ePrev.inv ≫ c = 0 := by
    rw [← cancel_epi ePrev.hom, ← Category.assoc, ← hdPrev]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero]
    exact DerivedCategory.HomologySequence.comp_δ T hT (r - 1) r
  have had : a ≫ T.mor₂ = 0 := comp_distTriang_mor_zero₁₂ T hT
  have hca : c ≫ H.map a = 0 := DerivedCategory.HomologySequence.δ_comp T hT (r - 1) r
  have ha : (H.map a ≫ eCur.hom) ≫ dcur = 0 := by
    rw [Category.assoc, ← hdCur, ← Category.assoc, ← H.map_comp, had, H.map_zero, zero_comp]
  let i := cokernel.desc dprev (ePrev.inv ≫ c) hc
  let q₀ := kernel.lift dcur (H.map a ≫ eCur.hom) ha
  let eLim : limit homologySystem ≅ kernel dcur :=
    (inverseSystemLimitKernelForkIsLimit homologySystem).conePointUniqueUpToIso
      (limit.isLimit _)
  let q := q₀ ≫ eLim.inv
  have heLim : eLim.hom ≫ kernel.ι dcur =
      Pi.lift (fun n : ℕ ↦ limit.π homologySystem ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hq : q ≫ Pi.lift (fun n : ℕ ↦ limit.π homologySystem ⟨n⟩) =
      H.map a ≫ eCur.hom := by
    rw [← heLim]
    simp [q, q₀]
  have hi : cokernel.π dprev ≫ i = ePrev.inv ≫ c := cokernel.π_desc _ _ _
  have hqn (n : ℕ) : q ≫ limit.π homologySystem ⟨n⟩ = H.map a ≫ H.map (Pi.π X n) := by
    have hLift : (Pi.lift (fun j : ℕ ↦ limit.π homologySystem ⟨j⟩)) ≫
        Pi.π (fun j : ℕ ↦ H.obj (X j)) n = limit.π homologySystem ⟨n⟩ := by
      simp [homologySystem, X, Functor.comp_obj]
    have h := congrArg (fun f ↦ f ≫ Pi.π (fun j : ℕ ↦ H.obj (X j)) n) hq
    rw [Category.assoc, hLift] at h
    simpa [eCur, Category.assoc, piComparison_comp_π] using h
  have hiq : i ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π dprev)]
    refine limit.hom_ext fun ⟨n⟩ ↦ ?_
    simp [hqn, reassoc_of% hi, reassoc_of% hca]
  have hprev : (ShortComplex.mk dprev (ePrev.inv ≫ c) hc).Exact := by
    apply ShortComplex.exact_of_iso _ (DerivedCategory.HomologySequence.exact₃ T hT (r - 1) r)
    exact ShortComplex.isoMk ePrev ePrev (Iso.refl _) (by simpa [T, Hprev] using hdPrev.symm)
      (by simp [c])
  have hcurr : (ShortComplex.mk (H.map a ≫ eCur.hom) dcur ha).Exact := by
    apply ShortComplex.exact_of_iso _ (DerivedCategory.HomologySequence.exact₂ T hT r)
    exact ShortComplex.isoMk (Iso.refl _) eCur eCur (by simp [T, H])
      (by simpa [T, H] using hdCur.symm)
  have hEpi : Epi q := by
    have := hcurr.epi_kernelLift
    dsimp only [q]
    infer_instance
  refine ⟨ePrev, i, q, hiq, rfl, hi, ?_, hqn⟩
  refine { exact := ?_, mono_f := hprev.mono_cokernelDesc, epi_g := hEpi }
  let S := ShortComplex.mk i (H.map a) (by
    rw [← cancel_epi (cokernel.π dprev), ← Category.assoc, hi]
    simp only [Category.assoc, hca, comp_zero])
  let φ : ShortComplex.mk c (H.map a)
      (DerivedCategory.HomologySequence.δ_comp T hT (r - 1) r) ⟶ S :=
    { τ₁ := ePrev.hom ≫ cokernel.π dprev
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, i]
      comm₂₃ := by simp [S] }
  have hS : S.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
      (DerivedCategory.HomologySequence.exact₁ T hT (r - 1) r)
  let ψ : ShortComplex.mk i q hiq ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := eLim.hom ≫ kernel.ι dcur ≫ eCur.inv
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S, q, q₀] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hS

/-- The Milnor short exact sequence for the cohomology of the image of a derived limit under a
right derived functor, with the triangle's structural map pinned to the image of the given one. -/
private theorem exists_shortExact_limOne_cohomology_rightDerived
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [IsGrothendieckAbelian.{uG} A] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : ℕᵒᵖ ⥤ DerivedCategory A)
    (L : DerivedCategory A)
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A))
    (m : ℤ) :
    let Hprev := DerivedCategory.homologyFunctor B (m - 1)
    let Hcur := DerivedCategory.homologyFunctor B m
    let Fprev := K ⋙ RF ⋙ Hprev
    let Fcur := K ⋙ RF ⋙ Hcur
    let E := K ⋙ RF
    let dprev : (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) ⟶
        (∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩) := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ Fprev.obj ⟨n⟩) (n + 1) ≫
          Fprev.map (homOfLE (Nat.le_succ n)).op
    ∃ (h : HasProduct fun n : ℕ ↦ E.obj ⟨n⟩),
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
      ∃ (ePrev : Hprev.obj (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩) ≅
          ∏ᶜ fun n : ℕ ↦ Fprev.obj ⟨n⟩)
        (i : cokernel dprev ⟶ Hcur.obj (RF.obj L))
      (q : Hcur.obj (RF.obj L) ⟶ limit Fcur)
      (zero : i ≫ q = 0),
      (ePrev.hom = piComparison Hprev (fun n : ℕ ↦ E.obj ⟨n⟩) ∧
        cokernel.π dprev ≫ i =
          ePrev.inv ≫ (DerivedCategory.homologyFunctor B 0).homologySequenceδ
            T (m - 1) m (by omega) ∧
        (ShortComplex.mk i q zero).ShortExact ∧
        ∀ n : ℕ, q ≫ limit.π Fcur ⟨n⟩ =
          Hcur.map (RF.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) := by
  let Hcur := DerivedCategory.homologyFunctor B m
  let E := K ⋙ RF
  obtain ⟨δ, hT⟩ := hL
  obtain ⟨h, a, b, hT', hπ⟩ :=
    rightDerivedMapDerivedLimitTriangle F RF α K L p δ hT
  let : HasProduct (fun n : ℕ ↦ E.obj ⟨n⟩) := h
  obtain ⟨ePrev, i, q, zero, hePrev, hi, hshort, hproj⟩ :=
    derivedLimitMilnorSequence E (RF.obj L) a b hT' m
  exact ⟨h, a, b, hT', hπ, ePrev, i, q, zero, hePrev, hi, hshort, fun n ↦
    (hproj n).trans <| (Hcur.map_comp _ _).symm.trans (congrArg Hcur.map (hπ n))⟩

end Auxiliary

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- Derived sections over an object preserve a derived inverse limit. -/
public theorem isDerivedLimit_map_derivedSections
    (U : X.Cᵒᵖ)
    [HasSheafify X.J AddCommGrpCat.{z}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (RGamma : DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
    (comparison :
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
        _ _ _ _ _ _ (K ⋙ RGamma) h (RGamma.obj L) :=
  by
    let := hRGamma
    let : PreservesLimitsOfShape (Discrete ℕ)
        (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
      SheafOfModules.evaluationPreservesLimitsOfShape.{z}
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (D := Discrete ℕ) U
    let : HasExactLimitsOfShape (Discrete ℕ)
        (ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) :=
      moduleCat_hasExactLimitsOfShape_discrete _ ℕ
    exact isDerivedLimit_map_rightDerived
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) RGamma
        comparison K L hL

/-- Global derived sections preserve a derived inverse limit. -/
public theorem isDerivedLimit_map_derivedGlobalSections
    (RGamma : DerivedCategory
        (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{max u v w z}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))
    (comparison :
      letI := globalSectionsFunctor_additive.{u, v, w, max u v w z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O);
      (globalSectionsFunctor.{u, v, w, max u v w z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (L : DerivedCategory
      (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ RGamma.obj (K.obj ⟨n⟩)),
      @IsDerivedLimit
        (DerivedCategory (ModuleCat.{max u v w z}
          (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))
        _ _ _ _ _ _ (K ⋙ RGamma) h (RGamma.obj L) :=
  by
    let := hRGamma
    let := globalSectionsFunctor_additive.{u, v, w, max u v w z}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    let : PreservesLimitsOfShape (Discrete ℕ) (globalSectionsFunctor.{u, v, w, max u v w z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      globalSectionsFunctor_preservesCountableProducts
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w z}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) :=
      moduleCat_hasExactLimitsOfShape_discrete _ ℕ
    exact isDerivedLimit_map_rightDerived
      (globalSectionsFunctor.{u, v, w, max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        RGamma comparison K L hL

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- The canonical Milnor sequence for cohomology over an object of a ringed site. -/
public theorem exists_shortExact_limOne_cohomology_derivedSections
    (U : X.Cᵒᵖ)
    [HasSheafify X.J AddCommGrpCat.{z}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (RGamma : DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
    (comparison :
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory
          (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (m : ℤ) :
    let A := ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
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
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) := by
  let : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    SheafOfModules.evaluationPreservesLimitsOfShape.{z}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (D := Discrete ℕ) U
  let : HasExactLimitsOfShape (Discrete ℕ)
      (ModuleCat.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) :=
    moduleCat_hasExactLimitsOfShape_discrete _ ℕ
  exact exists_shortExact_limOne_cohomology_rightDerived
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) RGamma comparison
      K L p hL m

/-- The canonical Milnor sequence for cohomology of the whole ringed site. -/
public theorem exists_shortExact_limOne_cohomology_derivedGlobalSections
    (RGamma : DerivedCategory
        (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (ModuleCat.{max u v w z}
        (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)))
    (comparison :
      letI := globalSectionsFunctor_additive.{u, v, w, max u v w z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O);
      (globalSectionsFunctor.{u, v, w, max u v w z}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RGamma)
    (hRGamma : RGamma.IsRightDerivedFunctor comparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))
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
          Hcur.map (RGamma.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))) := by
  let := globalSectionsFunctor_additive.{u, v, w, max u v w z}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : PreservesLimitsOfShape (Discrete ℕ) (globalSectionsFunctor.{u, v, w, max u v w z}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    globalSectionsFunctor_preservesCountableProducts (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w z}
      (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) :=
    moduleCat_hasExactLimitsOfShape_discrete _ ℕ
  exact exists_shortExact_limOne_cohomology_rightDerived
    (globalSectionsFunctor.{u, v, w, max u v w z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    RGamma comparison K L p hL m

end Stacks.Cohomology

end
