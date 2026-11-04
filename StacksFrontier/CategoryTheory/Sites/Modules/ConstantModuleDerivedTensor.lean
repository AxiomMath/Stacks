module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensor
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.DerivedTensor.KFlatDescent
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import StacksFrontier.Homology.HomologyColimit

/-!
# The derived tensor product of a sheaf of modules with a module

Let `Λ` be a commutative ring and `J` a Grothendieck topology. For a `Λ`-module `M` the
derived tensor product `K ⊗^L_Λ M` of an object `K` of the unbounded derived category of
sheaves of `Λ`-modules with `M` (that is, with the constant sheaf `M̲`) is computed by a
projective resolution `P → M`: it is the functor induced by `K ↦ Tot(K ⊗_Λ P)`, which preserves
quasi-isomorphisms because a bounded above complex of projective (hence flat) modules is K-flat.

## Main definitions

* `Stacks.ConstantModuleTensor.resolution`: the chosen projective resolution of `M`, as a
  cochain complex in nonpositive degrees.
* `Stacks.ConstantModuleTensor.derivedTensor`: `K ↦ K ⊗^L_Λ M` on `D(J, Λ)`.

## Main results

* `Stacks.ConstantModuleTensor.kFlat_resolution`: the resolution is K-flat for the tensor
  product of sheaves with modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v₁ u₁

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]

/-- The chosen projective resolution of a `Λ`-module, as a cochain complex concentrated in
nonpositive degrees. -/
abbrev resolution (M : ModuleCat.{w} Λ) : CochainComplex (ModuleCat.{w} Λ) ℤ :=
  (CategoryTheory.projectiveResolution M).cochainComplex

variable [HasExactColimitsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))]

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- In an abelian category with exact colimits of shape `ℕ`, the colimit of an `ℕ`-indexed
diagram of acyclic cochain complexes is acyclic. -/
theorem acyclic_pt_of_isColimit {D : Type*} [Category D] [Abelian D] [HasColimitsOfShape ℕ D]
    [HasExactColimitsOfShape ℕ D]
    (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E) (hs : IsColimit s)
    (h : ∀ i, (E.obj i).Acyclic) : s.pt.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := D) (J := ℕ)
    (ComplexShape.up ℤ) n
  have hc := isColimitOfPreserves (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n) hs
  refine IsZero.of_iso ?_ (hc.coconePointUniqueUpToIso (colimit.isColimit _))
  rw [IsZero.iff_id_eq_zero]
  refine colimit.hom_ext fun i => ?_
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h i n)).eq_of_src _ _

/-- **A bounded above complex of flat modules is K-flat** for the tensor product of sheaves of
`Λ`-modules with `Λ`-modules. -/
theorem kFlat_of_isStrictlyLE_of_flat (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ q, Module.Flat Λ (P.X q)] :
    CochainComplex.KFlatBifunctor.KFlat (sheafTensor J Λ) P := by
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE (sheafTensor J Λ) P b
    (fun S => inferInstance) (fun E s hs h => acyclic_pt_of_isColimit E s hs h) fun q => ?_
  refine CochainComplex.KFlatBifunctor.kFlat_single_of_exact (sheafTensor J Λ) _ q fun G hG => ?_
  exact acyclic_mapHomologicalComplex_flipObj J Λ (P.X q) G hG

/-- **The projective resolution is K-flat** for the tensor product of sheaves of `Λ`-modules
with `Λ`-modules: `Tot(G ⊗_Λ P)` is acyclic for every acyclic complex of sheaves `G`. -/
theorem kFlat_resolution (M : ModuleCat.{w} Λ) :
    CochainComplex.KFlatBifunctor.KFlat (sheafTensor J Λ) (resolution Λ M) := by
  exact kFlat_of_isStrictlyLE_of_flat J Λ (resolution Λ M) 0

/-- The projective resolution of `M` is K-flat for the tensor product of sheaves of
`Λ`-modules with `Λ`-modules. -/
instance isKFlat_resolution (M : ModuleCat.{w} Λ) :
    Stacks.DerivedTensor.IsKFlat (sheafTensor J Λ) (resolution Λ M) :=
  ⟨fun K hK => kFlat_resolution J Λ M K hK⟩

variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]

/-- **The derived tensor product `K ↦ K ⊗^L_Λ M`** on the unbounded derived category of
sheaves of `Λ`-modules, computed by the chosen projective resolution of `M`. -/
def derivedTensor (M : ModuleCat.{w} Λ) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤ DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) (resolution Λ M)

end Stacks.ConstantModuleTensor
