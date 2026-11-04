module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.CategoryTheory.Sites.CechComplexCoefficientChange
public import StacksFrontier.CategoryTheory.Sites.CechComplexSliceBase
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CechStandardLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CechSheafCohomology

/-!
# The two Čech models of a covering agree, and compute local cohomology

Two Čech complexes of one covering `V = ⋃ U i` occur in this development, both of them
instances of Mathlib's `CategoryTheory.cechComplexFunctor`:

* the complex of Stacks 01EP, `Stacks.Cohomology.CechSheaf.cechComplex`, formed in the slice
  category `Over V` with coefficients in `ModuleCat Γ(V, 𝒪)`, which is the one the comparison
  with derived sections of Stacks 01EQ and Stacks 01ET is stated for;
* the complex formed in the lattice of opens with coefficients in abelian groups, which is the
  one the comparison with the alternating Čech complex of Stacks 01FM, and hence with the
  algebraic Čech complex of a family of ring elements, is stated for.

`StacksFrontier/CategoryTheory/Sites/CechComplexSliceBase.lean` and
`StacksFrontier/CategoryTheory/Sites/CechComplexCoefficientChange.lean` close the two gaps between
them — the ambient category and the coefficient category — and this file puts them together:
the two Čech cohomology objects of a covering vanish together.

Applied to the standard covering of `U = Spec A \ V(I)` by the basic opens of a family of
generators, and combined with
`Stacks.LocalCohomology.isZero_cechStandardHomology_iff_isZero_localCohomologyModule`, this
expresses the vanishing of the Stacks 01EP Čech cohomology of `M̃` in degree `n ≥ 1` as the
vanishing of `H^{n+1}_{V(I)}(M)`.

## Main results

* `Stacks.LocalCohomology.isZero_homology_forget₂_iff` — a complex of modules and its underlying
  complex of abelian groups have vanishing homology in the same degrees.
* `Stacks.LocalCohomology.isZero_cechComplex_homology_iff` — **the Čech cohomology of a covering
  formed in the slice category vanishes exactly when the one formed in the lattice of opens
  does.**
* `Stacks.LocalCohomology.cechPlusHomologyIso` — the degree-`p` cohomology of the Čech complex of
  Stacks 01EP, read in the bounded-below derived category, is its degree-`p` homology as a
  cochain complex of modules.
* `Stacks.LocalCohomology.isZero_cechPlusHomology_iff_isZero_localCohomologyModule` — **for
  `n ≥ 1` the degree-`n` Čech cohomology of `M̃` for the standard covering of
  `U = Spec A \ V(I)` vanishes exactly when `H^{n+1}_{V(I)}(M)` does.**

## Implementation notes

The identifications between the two spellings of a Čech complex are all definitional: the Stacks
01EP complex is `Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor` followed by Mathlib's
functor at the family `Stacks.Cohomology.CechSheaf.coverObject`, which is the family
`Stacks.CategoryTheory.CechComplex.overFamily` up to proof irrelevance in the inequality it
carries, and forgetting the module structure of the slice sections presheaf is restriction of
the underlying abelian presheaf along the forgetful functor of the slice. So no transport
appears below; only the two comparison isomorphisms of the Čech complexes themselves.

The passage from the bounded-below derived category to the cochain complex is
`CategoryTheory.DerivedCategory.homologyFunctorFactors` followed by
`HomologicalComplex.extendHomologyIso`, the latter because the Stacks 01EP complex is indexed by
`ℕ` and extended by zero to `ℤ` before being viewed in the derived category.

Everything is at module universe equal to the ring universe, which is forced by Stacks 01ET; see
the implementation notes of
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean`.

No Stacks tag attribute is placed here.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

universe u

namespace Stacks.LocalCohomology

/-! ### Forgetting the module structure does not change what vanishes -/

/-- A module is a zero object exactly when its underlying abelian group is: both say that the
underlying type is a subsingleton. -/
theorem isZero_forget₂_iff {R : Type u} [Ring R] (Z : ModuleCat.{u} R) :
    IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj Z) ↔ IsZero Z := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- **A complex of modules and its underlying complex of abelian groups have the same vanishing
homology.** Forgetting the module structure is exact, so it preserves homology, and it creates
neither nor destroys zero objects. -/
theorem isZero_homology_forget₂_iff {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    IsZero ((((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology n) ↔ IsZero (K.homology n) := by
  rw [← isZero_forget₂_iff (K.homology n)]
  exact (ShortComplex.mapHomologyIso (S := K.sc n)
    (F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).isZero_iff

/-! ### The two Čech complexes of a covering -/

/-- **The two Čech models of a covering vanish together.** The degree-`n` Čech cohomology of a
sheaf of modules for a covering of `V`, formed in the slice category over `V` with its module
structure as in Stacks 01EP, is a zero object exactly when the degree-`n` Čech cohomology of the
underlying abelian sheaf, formed in the lattice of opens, is.

The two gaps are closed separately:
`Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff` changes the coefficient
category and `Stacks.CategoryTheory.CechComplex.isZero_homology_slice_iff` changes the ambient
category. -/
theorem isZero_cechComplex_homology_iff {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (V : Opens X)
    {ι : Type u} (Ui : ι → Opens X) (hV : V = ⨆ i, Ui i) (F : SheafOfModules.{u} R) (n : ℕ) :
    IsZero ((cechComplex.{u, u, u, u} V Ui hV F).homology n) ↔
      IsZero (((CategoryTheory.cechComplexFunctor Ui).obj
        ((SheafOfModules.toSheaf R).obj F).obj).homology n) := by
  have hle : ∀ i, Ui i ≤ V := fun i ↦ hV ▸ le_iSup Ui i
  have h₁ := (isZero_homology_forget₂_iff (cechComplex.{u, u, u, u} V Ui hV F) n).symm
  have h₂ := (Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff
      (Stacks.CategoryTheory.CechComplex.overFamily Ui hle) (sectionsPresheaf.{u, u, u} V F)
      (forget₂ (ModuleCat.{u} (SectionRing R V)) AddCommGrpCat.{u}) n).symm
  have h₃ := Stacks.CategoryTheory.CechComplex.isZero_homology_slice_iff Ui hle
      ((SheafOfModules.toSheaf R).obj F).obj n
  exact h₁.trans (h₂.trans h₃)

/-! ### Reading the Stacks 01EP complex in the derived category -/

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (V : Opens X) {ι : Type u} (Ui : ι → Opens X) (hV : V = ⨆ i, Ui i) (F : SheafOfModules.{u} R)

/-- The degree-`p` cohomology of the Čech complex of Stacks 01EP, taken in the bounded-below
derived category of `Γ(V, 𝒪)`-modules as the comparison of Stacks 01EQ does, is its degree-`p`
homology as a cochain complex. -/
def cechPlusHomologyIso (p : ℕ) :
    (cechComplexPlusFunctor R V Ui hV ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj F ≅
      (cechComplex.{u, u, u, u} V Ui hV F).homology p :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (SectionRing R V)) (p : ℤ)).app
      ((cechComplexPlusFunctor R V Ui hV).obj F).obj ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat (j' := p) rfl

/-- The Čech cohomology of a covering, read in the bounded-below derived category, vanishes
exactly when the Čech cohomology of the underlying abelian sheaf formed in the lattice of opens
does. -/
theorem isZero_cechPlusHomology_iff (p : ℕ) :
    IsZero ((cechComplexPlusFunctor R V Ui hV ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj F) ↔
      IsZero (((CategoryTheory.cechComplexFunctor Ui).obj
        ((SheafOfModules.toSheaf R).obj F).obj).homology p) :=
  (cechPlusHomologyIso V Ui hV F p).isZero_iff.trans (isZero_cechComplex_homology_iff V Ui hV F p)

/-! ### The standard covering of the complement of a zero locus -/

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
  (hIf : Ideal.span (Set.range f) = I) (M : ModuleCat.{u} A)

/-- **The Čech cohomology of the standard covering is local cohomology, shifted.** For `n ≥ 1`
the degree-`n` Čech cohomology of `M̃` for the covering of `U = Spec A \ V(I)` by the basic opens
of a family of generators of `I`, in the model of Stacks 01EP and read in the bounded-below
derived category, is a zero object exactly when `H^{n+1}_{V(I)}(M)` is.

The two inputs are
`Stacks.LocalCohomology.isZero_cechPlusHomology_iff`, which moves the statement to the Čech
complex formed in the lattice of opens with abelian coefficients, and
`Stacks.LocalCohomology.isZero_cechStandardHomology_iff_isZero_localCohomologyModule`, the Čech
formula for local cohomology in that model. -/
theorem isZero_cechPlusHomology_iff_isZero_localCohomologyModule (hI : I.FG) (q : ℕ) :
    IsZero ((cechComplexPlusFunctor (Spec (CommRingCat.of A)).ringCatSheaf
          (complementZeroLocus A I) (cechStandardOpen f)
          (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor _ ((q : ℤ) + 1)).obj (associatedSheaf A M)) ↔
      IsZero (localCohomologyModule A I hI M ((q : ℤ) + 2)) := by
  have hcast : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
  rw [← hcast, isZero_cechPlusHomology_iff (complementZeroLocus A I) (cechStandardOpen f)
    (complementZeroLocus_eq_iSup_cechStandardOpen f I hIf) (associatedSheaf A M) (q + 1)]
  exact isZero_cechStandardHomology_iff_isZero_localCohomologyModule f M I hI hIf q

end Stacks.LocalCohomology

end
