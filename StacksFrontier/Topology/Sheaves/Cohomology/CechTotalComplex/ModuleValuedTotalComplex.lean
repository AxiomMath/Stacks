module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.FlasqueModuleCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.InjectiveQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections
public import StacksCore.CategoryTheory.Limits.Shapes.Countable
import StacksCore.Tactic.StacksAttribute

/-!
# The total Čech complex of a complex of modules, over the ring of sections

Let `(X, O_X)` be a ringed space, let `U` be an open subset and let `Ui : I → Opens X` be a family
of opens with `U = ⨆ i, Ui i`.  Write `A = O_X(U)` for the ring of sections of the structure sheaf
on `U`; at `U = ⊤` this is `A = Γ(X, O_X)`.  For a complex `K^•` of `O_X`-modules the Čech complex
of the cover is a complex of `A`-modules in each degree of `K^•`, and totalizing the resulting
double complex -- Čech degree first -- gives a functor

`Tot(Č^•(Ui, -)) : CochainComplex (SheafOfModules O_X) ℤ ⥤ CochainComplex (ModuleCat A) ℤ`,

together with the `A`-linear augmentation `Γ(U, K^•) ⟶ Tot(Č^•(Ui, K^•))` of [Stacks, Tag 07M9].
That augmentation is a quasi-isomorphism as soon as the terms of `K^•` are injective, and also as
soon as their underlying abelian sheaves are flasque.

## Main definitions

* `Stacks.Cech.Linear.totalCechComplexFunctor`: the total Čech complex of a complex of
  `O_X`-modules, as a complex of `A`-modules.
* `Stacks.Cech.Linear.sectionsComplexFunctor`: sections over `U`, degreewise.
* `Stacks.Cech.Linear.sectionsToTotalCech`: the `A`-linear augmentation of [Stacks, Tag 07M9].

## Main results

* `Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_injective` and
  `Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_isFlasque`: the augmentation is a
  quasi-isomorphism on a bounded below complex of injective, resp. of flasque, modules.

## Implementation notes

The double complex is `Stacks.Cohomology.CechDerived.cechBicomplex`, whose `(q, p)` term is the
Čech `p`-cochains of `K^q`; the functor is the total complex of its flip. The totalization exists
without any boundedness of `K^•`: a double complex of `A`-modules indexed by `ℤ × ℤ` has countable
antidiagonals and `ModuleCat A` has countable coproducts ([Stacks, Tag 012Z]).

The space, the structure sheaf, the modules and the index type of the cover share one universe.

## References

* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.CechDerived
open StacksDraft.TotalComplexQuasiIso

universe u

namespace Stacks.Cech.Linear

variable (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-! ### The total Čech complex and the complex of sections -/

/-- **The total Čech complex of a complex of `O_X`-modules, as a complex of `O_X(U)`-modules.**
The Čech complex of the cover is applied in each degree of the complex, the Čech degree is put
first and the two integer gradings are totalized. -/
def totalCechComplexFunctor :
    CochainComplex (SheafOfModules.{u} O) ℤ ⥤
      CochainComplex (ModuleCat.{u} (SectionRing O U)) ℤ :=
  (cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{u} (SectionRing O U)) (up ℤ) (up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} (SectionRing O U)) (up ℤ) (up ℤ) (up ℤ)

/-- The total Čech complex is the total complex of the flipped Čech bicomplex. -/
theorem totalCechComplexFunctor_obj (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (totalCechComplexFunctor X O U Ui hU).obj K =
      (cechBicomplex O U Ui hU K).flip.total (up ℤ) :=
  rfl

/-- **The complex of sections over `U` of a complex of `O_X`-modules**, a complex of
`O_X(U)`-modules. -/
def sectionsComplexFunctor :
    CochainComplex (SheafOfModules.{u} O) ℤ ⥤
      CochainComplex (ModuleCat.{u} (SectionRing O U)) ℤ :=
  (SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)

/-! ### The augmentation -/

/-- **The Čech augmentation is killed by the first Čech differential**, in integer degrees. -/
theorem cechAugmentationInt_comp_d (F : SheafOfModules.{u} O) :
    cechAugmentationInt O U Ui hU F ≫
      ((cechComplexIntFunctor O U Ui hU).obj F).d 0 1 = 0 :=
  (inducesIsoKernel_extendAugmentation
    (C := (cechComplexFunctorOfCover.{u, u, u} (R := O) (ι := I) U Ui hU).obj F)
    (cechAugmentation U Ui hU F) (cechAugmentation_comp_d U Ui hU F)
    (mono_cechAugmentation U Ui hU F) (exact_augmentedShortComplex U Ui hU F)
    ((sectionsTerminalFunctorIso (R := O) U).app F).symm rfl rfl
    (cechAugmentationInt O U Ui hU F) (Category.assoc _ _ _)).1

/-- Restriction of a section over `U` into Čech degree zero, followed by the inclusion of that
summand of the total complex: the map `Γ(U, K^•) ⟶ Tot(Č^•(Ui, K^•))` of complexes of
`O_X(U)`-modules, natural in `K^•`. -/
@[stacks 07M9 "the augmentation, with module coefficients"]
def sectionsToTotalCech :
    sectionsComplexFunctor X O U ⟶ totalCechComplexFunctor X O U Ui hU where
  app K :=
    { f := fun n => cechAugmentationInt O U Ui hU (K.X n) ≫
        (cechBicomplex O U Ui hU K).flip.ιTotal (up ℤ) 0 n n (by simp)
      comm' := by
        rintro n _ rfl
        exact ιTotalZero_comm (cechBicomplex O U Ui hU K).flip
          ((sectionsComplexFunctor X O U).obj K)
          (fun n => cechAugmentationInt O U Ui hU (K.X n))
          (fun n => cechAugmentationInt_comp_d X O U Ui hU (K.X n))
          (fun n => (cechAugmentationInt_naturality O U Ui hU (K.d n (n + 1))).symm) n }
  naturality K L f := HomologicalComplex.hom_ext _ _ fun n =>
    ιTotalZero_naturality (cechBicomplex O U Ui hU K).flip
      (cechBicomplex O U Ui hU L).flip
      ((HomologicalComplex₂.flipFunctor (ModuleCat.{u} (SectionRing O U)) (up ℤ) (up ℤ)).map
        (((cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ)).map f))
      ((sectionsComplexFunctor X O U).obj K) ((sectionsComplexFunctor X O U).obj L)
      ((sectionsComplexFunctor X O U).map f)
      (fun n => cechAugmentationInt O U Ui hU (K.X n))
      (fun n => cechAugmentationInt O U Ui hU (L.X n))
      (fun n => (cechAugmentationInt_naturality O U Ui hU (f.f n)).symm) n

/-- In degree `n` the augmentation restricts to Čech degree zero and includes that summand into
the total complex. -/
@[simp]
theorem sectionsToTotalCech_app_f (K : CochainComplex (SheafOfModules.{u} O) ℤ) (n : ℤ) :
    ((sectionsToTotalCech X O U Ui hU).app K).f n =
      cechAugmentationInt O U Ui hU (K.X n) ≫
        (cechBicomplex O U Ui hU K).flip.ιTotal (up ℤ) 0 n n (by simp) :=
  rfl

/-! ### The augmentation is a quasi-isomorphism on injective and on flasque complexes -/

/-- The augmentation is a quasi-isomorphism on a bounded below complex whose Čech columns are
exact away from Čech degree zero. -/
private theorem quasiIso_sectionsToTotalCech_of_exactAt
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hex : ∀ q p : ℤ, p ≠ 0 → ((cechBicomplex O U Ui hU K).X q).ExactAt p) :
    QuasiIso ((sectionsToTotalCech X O U Ui hU).app K) :=
  quasiIso_of_componentwise_resolution_map
    ((sectionsComplexFunctor X O U).obj K) (cechBicomplex O U Ui hU K).flip
    (cechAlphaRow O U Ui hU K)
    { diagonalFinite := diagonalFinite_cechBicomplex O U Ui hU K a
      zero_of_neg := fun q p hp => isZero_cechBicomplex_X_X O U Ui hU K q p (Or.inr hp)
      exactAt_of_ne_zero := hex
      inducesIsoKernel := inducesIsoKernel_cechAlphaRow O U Ui hU K }
    ((sectionsToTotalCech X O U Ui hU).app K) (fun _ => rfl)

/-- **The augmentation is a quasi-isomorphism on a bounded below complex of injective sheaves of
modules.** -/
theorem quasiIso_sectionsToTotalCech_of_injective
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hinj : ∀ n : ℤ, Injective (K.X n)) :
    QuasiIso ((sectionsToTotalCech X O U Ui hU).app K) :=
  quasiIso_sectionsToTotalCech_of_exactAt X O U Ui hU K a
    (exactAt_cechBicomplex_X O U Ui hU K hinj)

/-- **The columns of the Čech bicomplex of a complex of flasque modules are exact away from Čech
degree zero.** -/
theorem exactAt_cechBicomplex_X_of_isFlasque (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hfl : ∀ q : ℤ, (abSheaf (K.X q)).IsFlasque) (q p : ℤ) (hp : p ≠ 0) :
    ((cechBicomplex O U Ui hU K).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : embeddingUpNat.f p.toNat = p := by change ((p.toNat : ℕ) : ℤ) = p; omega
    exact (HomologicalComplex.extend_exactAt_iff _ embeddingUpNat hk).2 <|
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (isZero_cechComplex_homology_of_isFlasque U Ui hU (K.X q) (hfl q) p.toNat (by omega))

/-- **The augmentation is a quasi-isomorphism on a bounded below complex of modules whose
underlying abelian sheaves are flasque.** -/
theorem quasiIso_sectionsToTotalCech_of_isFlasque
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hfl : ∀ n : ℤ, (abSheaf (K.X n)).IsFlasque) :
    QuasiIso ((sectionsToTotalCech X O U Ui hU).app K) :=
  quasiIso_sectionsToTotalCech_of_exactAt X O U Ui hU K a
    (exactAt_cechBicomplex_X_of_isFlasque X O U Ui hU K hfl)

end Stacks.Cech.Linear

end
