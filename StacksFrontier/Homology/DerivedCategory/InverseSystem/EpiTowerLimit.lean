module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SurjectiveTowerDifference
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Milnor limits of epimorphic towers

An inverse system of complexes of modules whose transition maps are epimorphisms computes its
derived inverse limit by its ordinary inverse limit.  The transition out of level `n + 1` is
always the map to level `n`; this convention is useful for towers indexed by positive powers,
where level `n` represents the power `n + 1`.

## Main results

* `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift` — the statement in
  an arbitrary abelian category with exact `ℕ`-indexed products, carrying as a hypothesis the
  one thing the proof needs of the ambient category: that the difference map
  `(x_n) ↦ (x_n - t_n x_{n+1})` of an epimorphic tower of *objects* is an epimorphism.
* `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi` — the same for `ModuleCat A`, where
  that hypothesis is surjectivity of the difference map, built one transition map at a time by
  `Stacks.InverseSystem.surjective_pi_sub_shift`.

`StacksFrontier/Homology/DerivedCategory/InverseSystem/AbEpiTowerLimit.lean` discharges the same
hypothesis for `AddCommGrpCat`, which is the shape [Stacks, Tag 07MV] needs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace DerivedCategory

/-- An additive functor intertwines the difference map of a tower with that of its image tower,
via the product comparison map. -/
private theorem map_pi_sub_shift_comp_piComparison
    {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
    (G : C ⥤ D) [G.Additive] (X : ℕ → C) [HasProduct X] [HasProduct fun n ↦ G.obj (X n)]
    (t : ∀ n, X (n + 1) ⟶ X n) :
    G.map (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ piComparison G X =
      piComparison G X ≫ Pi.lift fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n -
        Pi.π (fun n ↦ G.obj (X n)) (n + 1) ≫ G.map (t n) := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp]
  simp only [Pi.lift_π, G.map_sub, G.map_comp, Category.assoc,
    Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π]

private theorem isDerivedLimit_of_shortExact_product_difference
    {B : Type u} [Category.{v} B] [Abelian B]
    (F : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩)]
    [IsIso (piComparison DerivedCategory.Q (fun n : ℕ ↦ F.obj ⟨n⟩))]
    (K : CochainComplex B ℤ) (p : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (h : p ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op) = 0)
    (hs : (ShortComplex.mk p _ h).ShortExact) :
    letI : HasProduct fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).obj ⟨n⟩ :=
      inferInstanceAs (HasProduct fun n : ℕ ↦ DerivedCategory.Q.obj (F.obj ⟨n⟩))
    IsDerivedLimit (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj K) := by
  let Q : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let X := fun n : ℕ ↦ F.obj ⟨n⟩
  let d' := Pi.lift fun n : ℕ ↦ Pi.π (fun n ↦ Q.obj (X n)) n -
    Pi.π (fun n ↦ Q.obj (X n)) (n + 1) ≫ Q.map (F.map (homOfLE (Nat.le_succ n)).op)
  let e := asIso (piComparison Q X)
  have hd : Q.map _ ≫ e.hom = e.hom ≫ d' :=
    map_pi_sub_shift_comp_piComparison Q X fun n ↦ F.map (homOfLE (Nat.le_succ n)).op
  let t := DerivedCategory.triangleOfSES hs
  let s := Triangle.mk (Q.map p ≫ e.hom) d'
    (e.inv ≫ DerivedCategory.triangleOfSESδ hs)
  let he : t ≅ s := Triangle.isoMk _ _ (Iso.refl _) e e
    (Category.id_comp _).symm hd (by
      change DerivedCategory.triangleOfSESδ hs ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
        e.hom ≫ e.inv ≫ DerivedCategory.triangleOfSESδ hs
      rw [(shiftFunctor (DerivedCategory B) (1 : ℤ)).map_id]
      simp only [Category.comp_id, Iso.hom_inv_id_assoc])
  exact ⟨_, _, isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs)
    s he.symm⟩

private theorem epi_pi_sub_shift_of_epi
    {A : Type u} [Ring A] (X : ℕ → ModuleCat.{v} A)
    [HasProduct X] (t : ∀ n, X (n + 1) ⟶ X n) [∀ n, Epi (t n)] :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  refine (ModuleCat.epi_iff_surjective _).mpr fun y ↦ ?_
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift (fun n ↦ t n)
    (fun n ↦ (ModuleCat.epi_iff_surjective (t n)).mp inferInstance)
    ((ModuleCat.piIsoPi X).hom y)
  refine ⟨(ModuleCat.piIsoPi X).inv x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  change ((Pi.lift (fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ Pi.π X n)
    ((ModuleCat.piIsoPi X).inv x)) = _
  rw [Pi.lift_π]
  change (Pi.π X n) ((ModuleCat.piIsoPi X).inv x) -
    (t n) ((Pi.π X (n + 1)) ((ModuleCat.piIsoPi X).inv x)) =
      (ModuleCat.piIsoPi X).hom y n
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  exact congrFun hx n

/-- The difference map of an epimorphic tower of complexes is an epimorphism as soon as the
difference map of an epimorphic tower of *objects* is, which is the hypothesis `hB`: the
statement is degreewise, and evaluation in a degree preserves `ℕ`-indexed products. -/
private theorem epi_complex_pi_sub_shift_of_epi
    {B : Type u} [Category.{v} B] [Abelian B] [HasProductsOfShape ℕ B]
    (hB : ∀ (Y : ℕ → B) (c : ∀ n, Y (n + 1) ⟶ Y n), (∀ n, Epi (c n)) →
      Epi (Pi.lift fun n ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ c n))
    (X : ℕ → CochainComplex B ℤ)
    (t : ∀ n, X (n + 1) ⟶ X n) [∀ n, Epi (t n)] :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let G := HomologicalComplex.eval B (ComplexShape.up ℤ) i
  have := hB (fun n ↦ G.obj (X n)) (fun n ↦ G.map (t n)) fun n ↦ inferInstance
  have : IsIso (piComparison G X) := inferInstance
  have h := map_pi_sub_shift_comp_piComparison G X t
  have : Epi (G.map (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ piComparison G X) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison G X)).mp this

private def kernelForkOfInverseSystemCone
    {B : Type u} [Category.{v} B] [Preadditive B]
    {F : ℕᵒᵖ ⥤ B} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (s : Cone F) : KernelFork (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) :=
  KernelFork.ofι (Pi.lift fun n : ℕ ↦ s.π.app ⟨n⟩) (by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [Preadditive.comp_sub, s.w])

set_option backward.isDefEq.respectTransparency false in
private def kernelForkOfInverseSystemConeIsLimit
    {B : Type u} [Category.{v} B] [Preadditive B]
    {F : ℕᵒᵖ ⥤ B} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (s : Cone F) (hs : IsLimit s) : IsLimit (kernelForkOfInverseSystemCone s) := by
  let coneOfKernel (t : KernelFork (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op)) : Cone F :=
    { pt := t.pt
      π := NatTrans.ofOpSequence (fun n ↦ t.ι ≫ Pi.π _ n) (fun n ↦ by
        have h := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) t.condition
        simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, zero_comp] at h
        simpa using sub_eq_zero.mp h) }
  refine Fork.IsLimit.mk _ (fun t ↦ hs.lift (coneOfKernel t)) ?_ ?_
  · intro t
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [kernelForkOfInverseSystemCone, hs.fac, coneOfKernel]
  · intro t m hm
    refine hs.hom_ext fun n ↦ ?_
    simpa [kernelForkOfInverseSystemCone, coneOfKernel] using
      congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n.unop) hm

/-- **The ordinary limit of a tower of complexes with epimorphic transition maps represents its
derived inverse limit**, in any abelian category whose `ℕ`-indexed products are exact and in
which the difference map of an epimorphic tower of objects is an epimorphism (`hB`).

The second condition is the only non-formal input, and it is where the ambient category is used:
`hB` is what makes the Milnor sequence of the tower short exact, so that its triangle in the
derived category exhibits `Q(lim)` as `R lim`.  At index `n` the transition is the actual map
from `n + 1` to `n`. -/
public theorem isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift
    {B : Type u} [Category.{v} B] [Abelian B] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    (hB : ∀ (Y : ℕ → B) (c : ∀ n, Y (n + 1) ⟶ Y n), (∀ n, Epi (c n)) →
      Epi (Pi.lift fun n ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ c n))
    (F : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)]
    (s : Cone F) (hs : IsLimit s) :
    letI : HasProductsOfShape ℕ (DerivedCategory B) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj s.pt) := by
  have : HasProductsOfShape ℕ (DerivedCategory B) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := B)) := Stacks.DerivedProducts.preservesLimitsOfShape_Q
  have hk := kernelForkOfInverseSystemConeIsLimit s hs
  have := epi_complex_pi_sub_shift_of_epi hB (fun n : ℕ ↦ F.obj ⟨n⟩)
    (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)
  exact isDerivedLimit_of_shortExact_product_difference F s.pt
    (kernelForkOfInverseSystemCone s).ι (kernelForkOfInverseSystemCone s).condition
    { exact := ShortComplex.exact_of_f_is_kernel _ hk
      mono_f := mono_of_isLimit_fork hk
      epi_g := inferInstance }

/-- The ordinary limit of a tower of complexes with epimorphic transition maps represents its
derived inverse limit.  At index `n`, the transition is the actual map from `n + 1` to `n`.
Thus a positive-power tower has level `n` equal to power `n + 1`, not power `n`. -/
public theorem isDerivedLimit_of_limit_cone_of_epi
    {A : Type u} [CommRing A]
    (F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)]
    (s : Cone F) (hs : IsLimit s) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj s.pt) :=
  isDerivedLimit_of_limit_cone_of_epi_of_epi_pi_sub_shift (B := ModuleCat.{v} A)
    (fun Y c _ ↦ epi_pi_sub_shift_of_epi Y c) F s hs

end DerivedCategory
