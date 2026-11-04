module

public import StacksFrontier.AlgebraicGeometry.Duality.LocallyFreeTwist
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatRightFactorDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.NatTransMapDerivedCategoryShift
public import StacksFrontier.AlgebraicGeometry.Duality.UnitCorepresentation
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayDualizingComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Duality for finite locally free modules on a curve

Let `k` be a field, `f : X ⟶ Spec k`, `ω_X^• = f^×(𝒪_{Spec k})` the dualizing complex and
`ω_X = H^{-1}(ω_X^•)` the dualizing sheaf of [Stacks, Tag 0BS2]. For a finite locally free
`𝒪_X`-module `ℰ` with dual `ℰ^∨`, [Stacks, Tag 0BS4] displays the canonical isomorphisms

  `Hom_k(H^{-i}(X, ℰ), k) = H^i(X, ℰ^∨ ⊗^L_{𝒪_X} ω_X^•)`

and, when `X` is Cohen--Macaulay and equidimensional of dimension one,

  `Hom_k(H^{-i}(X, ℰ), k) = H^{1+i}(X, ℰ^∨ ⊗_{𝒪_X} ω_X)`.

## Main results

* `Stacks.Duality.LocallyFreeTwist.dualityDerivedTensorLinearEquiv` — **the first display**, as
  an isomorphism of `k`-vector spaces, for every quasi-compact quasi-separated `X` over `k`.
* `Stacks.Duality.LocallyFreeTwist.dualityTensorDualizingSheafLinearEquiv` — **the second
  display**, as an isomorphism of `k`-vector spaces, for `X` proper over `k`, Cohen--Macaulay and
  equidimensional of dimension one.

The two dimension formulas the Remark draws from the second display are in
`StacksFrontier/AlgebraicGeometry/Curves/DualizingInvertibleDimensionDuality.lean`.

## The argument

The source's: clause (4) of [Stacks, Tag 0BS2] at `ℰ[0]` (`Stacks.Duality.extDualityLinearEquiv`)
gives `Hom_k(H^{-i}(X, ℰ), k) = Ext^i(ℰ[0], ω_X^•)`, and the identification of the right-hand
side with `H^i(X, ℰ^∨ ⊗^L ω_X^•)` is [Stacks, Tag 08DQ] for the perfect object `ℰ[0]`. That
identification is assembled here, at the locally small model of `D(𝒪_X)` in which clause (4) of
Tag 0BS2 lives, from:

1. `ℰ[0] = (- ⊗ ℰ)~(𝒪_X[0])`, and the derived adjunction `(- ⊗ ℰ)~ ⊣ (- ⊗ ℰ^∨)~` of the exact
   pairing between `ℰ` and `ℰ^∨` ([Stacks, Tag 0FNV]),
   `Stacks.Duality.LocallyFreeTwist.derivedTwistHomLinearEquiv`;
2. the commutation of `(- ⊗ ℰ^∨)~` with the shift;
3. the corepresentation `Hom_{D(𝒪_X)}(𝒪_X[0], M) = H^0(X, M)`,
   `Stacks.Duality.UnitCorepresentation.unitHomLinearEquiv`, and `H^0(X, M⟦i⟧) = H^i(X, M)`;
4. `(- ⊗ ℰ^∨)~(K) = K ⊗^L ℰ^∨[0]`, `ℰ^∨[0]` being K-flat, and the symmetry of `⊗^L`
   ([Stacks, Tag 0FPT]), `Stacks.Duality.LocallyFreeTwist.GTIsoTensor`.

Each step is `k`-linear. The second display is the first with `ω_X^• = ω_X[1]` of
[Stacks, Tag 0BS3] (`Stacks.Duality.dualizingSheafShiftOneIsoOfIsCohenMacaulay`) substituted, the
derived tensor product with the flat `ℰ^∨` of a module in degree zero being the ordinary tensor
product in degree zero.

## Canonicity and naturality

The source calls the isomorphisms canonical. Every step is a canonical map, and none involves a
choice: in particular `GTIsoTensor` is the component of the natural isomorphism of functors
`(- ⊗ ℰ^∨)~ ≅ - ⊗^L ℰ^∨[0]`, `Stacks.DerivedTensor.RingedSite.flatTwistNatIso`, which is lifted
through the localization functor from cochain complexes and so is natural in the complex.

Naturality in `ℰ`: for `g : ℰ₁ ⟶ ℰ₂` with dual `g^∨ = dualMap g` (its right adjoint mate for the
evaluation pairings),

* `dualityTwistLinearEquiv_naturality` — the chain
  `Hom_k(H^{-i}(X, ℰ), k) ≃ₗ[k] H^i(X, (- ⊗ ℰ^∨)~(ω_X^•))` turns precomposition with
  `H^{-i}(X, g)` into `H^i(X, (- ⊗ g^∨)~(ω_X^•))`;
* `dualityTensorDualizingSheafLinearEquiv_naturality` — **the second display is natural in
  `ℰ`**: precomposition with `H^{-i}(X, g)` corresponds to `H^{1+i}(X, g^∨ ⊗ ω_X)`;
* `Stacks.DerivedTensor.RingedSite.flatTwistNatIso_naturality_right` — the identification
  `(- ⊗ N)~ ≅ - ⊗^L N[0]` is natural in the flat module `N`.

Not proved: the naturality in `ℰ` of the first display itself, i.e. of `GTIsoTensor` in `ℰ`.
The generic naturality above is stated for the category of modules spelled as modules over a
ringed site; comparing its natural transformation with `GTMap`, which lives at the spelling of
the monoidal structure of [Stacks, Tag 01CA], exceeds the elaborator's recursion limit, and the
comparison is not carried out.

## References

* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality.LocallyFreeTwist

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable {X : Scheme.{u}}

variable (X) in
/-- `𝒪_X[0]` in the homotopy category, read in `D(𝒪_X)`, is `𝒪_X` placed in degree zero. -/
def unitHomotopyIso :
    DerivedCategory.Qh.obj (UnitCorepresentation.unitHomotopy X) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X) :=
  (DerivedCategory.quotientCompQhIso X.Modules).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm

variable (E : Mod X) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- `(- ⊗ E)~` on `D(𝒪_X)`, read at the spelling `X.Modules`. -/
abbrev FT : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (twist X E).mapDerivedCategory

/-- `(- ⊗ E^∨)~` on `D(𝒪_X)`, read at the spelling `X.Modules`. -/
abbrev GT : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (twist X (dual E)).mapDerivedCategory

/-- The derived adjunction `(- ⊗ E)~ ⊣ (- ⊗ E^∨)~`. -/
def adjT : FT E ⊣ GT E := derivedTwistAdjunction E

/-- `(- ⊗ E^∨)~` commutes with the shift. -/
def GTCommShiftIso (n : ℤ) (K : DerivedCategory X.Modules) :
    (GT E).obj (K⟦n⟧) ≅ ((GT E).obj K)⟦n⟧ :=
  ((twist X (dual E)).mapDerivedCategory.commShiftIso n).app K

/-- `(𝒪_X ⊗ E)[0] ≅ E[0]`. -/
def twistUnitIso :
    (FT E).obj (DerivedCategory.Qh.obj (UnitCorepresentation.unitHomotopy X)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj E :=
  (twist X E).mapDerivedCategory.mapIso (unitHomotopyIso X) ≪≫
    ((twist X E).mapDerivedCategorySingleFunctor 0).app (Stacks.Ample.unitModule X) ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso (MonoidalCategory.leftUnitor (C := Mod X) E)

variable (X) in
/-- **The symmetry of the derived tensor product** `A ⊗^L B ≅ B ⊗^L A` of [Stacks, Tag 0FPT], at
the locally small model of `D(𝒪_X)`: the braiding of the symmetric monoidal structure
`AlgebraicGeometry.Scheme.Modules.derivedSymmetric`, read through the identification of its
tensor product with the derived tensor product. -/
def derivedTensorBraiding (A B : DerivedCategory X.Modules) :
    ((Stacks.Duality.derivedTensor X).obj A).obj B ≅
      ((Stacks.Duality.derivedTensor X).obj B).obj A :=
  letI := Scheme.Modules.derivedMonoidal X
  letI := Scheme.Modules.derivedSymmetric X
  let c := Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf
  ((c.app A).app B).symm ≪≫ (β_ A B) ≪≫ (c.app B).app A

/-- **`(- ⊗ E^∨)~ (K) ≅ E^∨[0] ⊗^L K`**: the derived functor of the exact functor `- ⊗ E^∨` is the
derived tensor product with `E^∨` placed in degree zero, `E^∨` being flat. -/
def GTIsoTensor (K : DerivedCategory X.Modules) :
    (GT E).obj K ≅ ((Stacks.Duality.derivedTensor X).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (dual E))).obj K :=
  letI : HasDerivedCategory.{u} (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) :=
    SheafOfModules.hasDerivedCategory (structureSheafRing X.toRingedSpace)
  (Stacks.DerivedTensor.RingedSite.flatTwistNatIso X.toRingedSpace.sheaf
      (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace) (dual E) (isFlat_dual E)
      (hAdd := (inferInstance : (twist X (dual E)).Additive))
      (hLim := (inferInstance : PreservesFiniteLimits (twist X (dual E))))
      (hColim := (inferInstance : PreservesFiniteColimits (twist X (dual E))))).app K ≪≫
    ((Stacks.Duality.derivedTensor X).obj K).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (Mod X) 0).app (dual E)).symm ≪≫
    derivedTensorBraiding X K _

section Linear

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- `(- ⊗ E^∨)~` is `k`-linear on morphisms: `(- ⊗ E^∨)~ (a • g) = a • (- ⊗ E^∨)~ g`. -/
theorem GT_map_smul (a : k) {A B : DerivedCategory X.Modules} (g : A ⟶ B) :
    letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
    (GT E).map (a • g) = a • (GT E).map g :=
  let : Linear k (Mod X) := Scheme.Modules.linearOverBase f
  let : (twist X (dual E)).Linear k := twist_linear f (dual E)
  Functor.map_smul (twist X (dual E)).mapDerivedCategory a g

/-- The derived adjunction `(- ⊗ E)~ ⊣ (- ⊗ E^∨)~` on Hom-spaces, `k`-linearly. -/
def derivedTwistHomLinearEquiv (A B : DerivedCategory X.Modules) :
    letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
    ((FT E).obj A ⟶ B) ≃ₗ[k] (A ⟶ (GT E).obj B) :=
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  { (adjT E).homEquiv A B with
    map_add' := fun g g' => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_apply]
      rw [show (GT E).map (g + g') = (GT E).map g + (GT E).map g' from
        (twist X (dual E)).mapDerivedCategory.map_add, Preadditive.comp_add]
    map_smul' := fun a g => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_apply, GT_map_smul E f,
        Linear.comp_smul, RingHom.id_apply] }

/-- `E` placed in degree zero, as an object of `D_QCoh(𝒪_X)`. -/
def singleQC : quasiCoherentDerivedCategory X :=
  singleQuasiCoherent E
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E) 0

variable [QuasiCompact f] [QuasiSeparated f]

/-- **The core chain of [Stacks, Tag 0BS4]**: for a finite locally free `E`,

  `Hom_k(H^{-i}(X, E), k) ≃ₗ[k] H^i(X, (ω_X^• ⊗ E^∨)~)`,

where `(- ⊗ E^∨)~` is the derived functor of the exact functor `- ⊗ E^∨`. It is clause (4) of
[Stacks, Tag 0BS2] at `E[0]`, followed by the derived adjunction `(- ⊗ E)~ ⊣ (- ⊗ E^∨)~` of the
exact pairing between `E` and `E^∨` ([Stacks, Tag 0FNV]), and the corepresentation of
hypercohomology by `𝒪_X[0]`. -/
def dualityTwistLinearEquiv (i : ℤ) :
    Module.Dual k (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        (-i)) ≃ₗ[k]
      derivedCohomologyOverField f
        ((GT E).obj (dualizingComplexOverField f).obj) i :=
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  (ModuleCat.homLinearEquiv (S := k)
    (M := derivedCohomologyOverField f (singleQC E).obj (-i)) (N := ModuleCat.of k k)).symm ≪≫ₗ
    (extDualityLinearEquiv f (singleQC E) i).symm ≪≫ₗ
    Linear.homCongr k (twistUnitIso E).symm (Iso.refl _) ≪≫ₗ
    derivedTwistHomLinearEquiv E f _ _ ≪≫ₗ
    Linear.homCongr k (Iso.refl _) (GTCommShiftIso E i _) ≪≫ₗ
    UnitCorepresentation.unitHomLinearEquiv f _ ≪≫ₗ
    (derivedCohomologyShiftIso f _ i).toLinearEquiv

/-- **[Stacks, Tag 0BS4], first display**: for a finite locally free `E` with dual `E^∨`,

  `Hom_k(H^{-i}(X, E), k) ≃ₗ[k] H^i(X, E^∨ ⊗^L ω_X^•)`,

with `ω_X^•` the dualizing complex of [Stacks, Tag 0BS2] and `⊗^L` the derived tensor product of
[Stacks, Tag 06YU]. The source assumes `X` proper of dimension at most one over `k`; only the
quasi-compactness and quasi-separatedness of `f`, under which clause (4) of Tag 0BS2 holds, are
used. -/
@[stacks 0BS4 "the first display, Hom_k(H^{-i}(X, E), k) = H^i(X, E^dual tensor^L omega^bullet), \
as an isomorphism of k-vector spaces, for E finite locally free; for every quasi-compact \
quasi-separated X over k, of which a proper X of dimension at most one is a case"]
def dualityDerivedTensorLinearEquiv (i : ℤ) :
    Module.Dual k (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        (-i)) ≃ₗ[k]
      derivedCohomologyOverField f (((Stacks.Duality.derivedTensor X).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (dual E))).obj
          (dualizingComplexOverField f).obj) i :=
  dualityTwistLinearEquiv E f i ≪≫ₗ
    ((derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso
      (GTIsoTensor E (dualizingComplexOverField f).obj)).toLinearEquiv

/-- `H^i(X, M⟦1⟧) ≅ H^{1+i}(X, M)`. -/
def derivedCohomologyShiftOneIso (M : DerivedCategory X.Modules) (i : ℤ) :
    derivedCohomologyOverField f (M⟦(1 : ℤ)⟧) i ≅ derivedCohomologyOverField f M (1 + i) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso
      (((derivedGlobalSectionsOver f).commShiftIso (1 : ℤ)).app M) ≪≫
    (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) i).symm).app _ ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso (1 : ℤ) i (1 + i) rfl).app _ ≪≫
    (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) (1 + i))).app _

/-- Three natural transformations in a row are natural. -/
theorem three_nat {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F₁ F₂ F₃ F₄ : 𝒞 ⥤ 𝒟}
    (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) {x y : 𝒞} (m : x ⟶ y) :
    F₁.map m ≫ a.app y ≫ b.app y ≫ c.app y = a.app x ≫ b.app x ≫ c.app x ≫ F₄.map m := by
  simp

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The isomorphism `H^i(X, M⟦1⟧) ≅ H^{1+i}(X, M)` is natural in `M`. -/
theorem derivedCohomologyShiftOneIso_naturality {M N : DerivedCategory X.Modules} (h : M ⟶ N)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
        ((derivedGlobalSectionsOver f).map (h⟦(1 : ℤ)⟧')) ≫
        (derivedCohomologyShiftOneIso f N i).hom =
      (derivedCohomologyShiftOneIso f M i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (1 + i)).map
          ((derivedGlobalSectionsOver f).map h) := by
  simp only [derivedCohomologyShiftOneIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  exact three_nat (Functor.whiskerLeft (shiftFunctor (DerivedCategory (ModuleCat.{u} k)) (1 : ℤ))
      (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) i).symm).hom)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso (1 : ℤ) i (1 + i) rfl).hom
    (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{u} k) (1 + i))).hom
    ((derivedGlobalSectionsOver f).map h)

/-- `(- ⊗ E^∨)~ (ω_X[1]) ≅ (E^∨ ⊗ ω_X)[0]⟦1⟧` on a Cohen--Macaulay curve. -/
def GTDualizingIsoOfIsCohenMacaulay [IsProper f] (hcm : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    (GT E).obj (dualizingComplexOverField f).obj ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj (dual E)).obj
          (dualizingSheafOverField f)))⟦(1 : ℤ)⟧ :=
  (GT E).mapIso (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).symm ≪≫
    GTCommShiftIso E 1 _ ≪≫
    (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).mapIso
      (((twist X (dual E)).mapDerivedCategorySingleFunctor 0).app (dualizingSheafOverField f) ≪≫
        (DerivedCategory.singleFunctor X.Modules 0).mapIso
          (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (R X)).app (dual E)).app
            (dualizingSheafOverField f)).symm)

/-- **[Stacks, Tag 0BS4], second display**: if `X` is proper over `k`, Cohen--Macaulay and
equidimensional of dimension one, then for a finite locally free `E` with dual `E^∨`,

  `Hom_k(H^{-i}(X, E), k) ≃ₗ[k] H^{1+i}(X, E^∨ ⊗_{𝒪_X} ω_X)`,

with `ω_X` the dualizing sheaf of [Stacks, Tag 0BS2]. This is the first display with
`ω_X^• = ω_X[1]` of [Stacks, Tag 0BS3] substituted. -/
@[stacks 0BS4 "the second display, Hom_k(H^{-i}(X, E), k) = H^{1+i}(X, E^dual tensor omega_X), \
as an isomorphism of k-vector spaces, for X proper over k, Cohen-Macaulay and equidimensional of \
dimension one, and E finite locally free"]
def dualityTensorDualizingSheafLinearEquiv [IsProper f]
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (i : ℤ) :
    Module.Dual k (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        (-i)) ≃ₗ[k]
      derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj (dual E)).obj
          (dualizingSheafOverField f))) (1 + i) :=
  dualityTwistLinearEquiv E f i ≪≫ₗ
    ((derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso
      (GTDualizingIsoOfIsCohenMacaulay E f hcm hequi hdim) ≪≫
      derivedCohomologyShiftOneIso f _ i).toLinearEquiv

end Linear

section Naturality

/-- The derived adjunction's Hom-bijection, natural in the left-adjoint variable for a pair of
adjunctions related by a square of units. -/
theorem homEquiv_unit_square {𝒟 : Type*} [Category 𝒟] {F₁ F₂ G₁ G₂ : 𝒟 ⥤ 𝒟}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (a : F₁ ⟶ F₂) (b : G₂ ⟶ G₁) {P A₁ A₂ W : 𝒟}
    (hU : adj₂.unit.app P ≫ b.app (F₂.obj P) = adj₁.unit.app P ≫ G₁.map (a.app P))
    (ι₁ : F₁.obj P ≅ A₁) (ι₂ : F₂.obj P ≅ A₂) (x : A₁ ⟶ A₂)
    (hK : a.app P ≫ ι₂.hom = ι₁.hom ≫ x) (β : A₂ ⟶ W) :
    adj₁.homEquiv _ _ (ι₁.hom ≫ x ≫ β) = adj₂.homEquiv _ _ (ι₂.hom ≫ β) ≫ b.app W := by
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, ← reassoc_of% hK, Category.assoc,
    G₁.map_comp, ← reassoc_of% hU, ← b.naturality]

/-- A natural transformation through three isomorphisms. -/
theorem nat_three_isos {𝒟 𝒟' : Type*} [Category 𝒟] [Category 𝒟'] {F₁ F₂ : 𝒟 ⥤ 𝒟'}
    (a : F₁ ⟶ F₂) {P S : 𝒟} (v : P ≅ S) {B₁ B₂ C₁ C₂ : 𝒟'} (m₁ : F₁.obj S ≅ B₁)
    (m₂ : F₂.obj S ≅ B₂) (y : B₁ ⟶ B₂) (hm : a.app S ≫ m₂.hom = m₁.hom ≫ y) (l₁ : B₁ ≅ C₁)
    (l₂ : B₂ ≅ C₂) (z : C₁ ⟶ C₂) (hl : y ≫ l₂.hom = l₁.hom ≫ z) :
    a.app P ≫ (F₂.mapIso v ≪≫ m₂ ≪≫ l₂).hom = (F₁.mapIso v ≪≫ m₁ ≪≫ l₁).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← a.naturality_assoc, reassoc_of% hm, hl]

/-- A functor carries a commutative square `f ≫ g = f' ≫ g'` to a commutative square. -/
private theorem map_comp_congr {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {a b c d : 𝒞} {f : a ⟶ b} {g : b ⟶ d} {f' : a ⟶ c} {g' : c ⟶ d} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  simp only [← F.map_comp, h]

variable (X) in
/-- The class of `𝒪_X[0]` in `D(𝒪_X)`. -/
abbrev unitObj : DerivedCategory X.Modules :=
  DerivedCategory.Qh.obj (UnitCorepresentation.unitHomotopy X)

variable {E₁ E₂ : Mod X} [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E₂] (g : E₁ ⟶ E₂)

/-- `(- ⊗ g)~ : (- ⊗ E₁)~ ⟶ (- ⊗ E₂)~`. -/
def FTMap : FT E₁ ⟶ FT E₂ := NatTrans.mapDerivedCategory (twistMap g)

/-- `(- ⊗ g^∨)~ : (- ⊗ E₂^∨)~ ⟶ (- ⊗ E₁^∨)~`. -/
def GTMap : GT E₂ ⟶ GT E₁ := NatTrans.mapDerivedCategory (twistMap (dualMap g))

/-- The units of the adjunctions `(- ⊗ E₁)~ ⊣ (- ⊗ E₁^∨)~` and `(- ⊗ E₂)~ ⊣ (- ⊗ E₂^∨)~` at
`𝒪_X[0]` are compatible with `(- ⊗ g)~` and `(- ⊗ g^∨)~`. -/
theorem adjT_unit_square :
    (adjT E₂).unit.app (unitObj X) ≫ (GTMap g).app ((FT E₂).obj (unitObj X)) =
      (adjT E₁).unit.app (unitObj X) ≫ (GT E₁).map ((FTMap g).app (unitObj X)) :=
  NatTrans.mapDerivedCategory_unit_conjugate (twistAdjunction E₂) (twistAdjunction E₁)
    (twistMap g) (twistMap (dualMap g)) (fun A => twistAdjunction_unit_dualMap g A) _

/-- The isomorphism `(𝒪_X ⊗ E)[0] ≅ E[0]` is natural in `E`: it intertwines `(- ⊗ g)~` at
`𝒪_X[0]` with `g[0]`. -/
theorem twistUnitIso_naturality :
    (FTMap g).app (unitObj X) ≫ (twistUnitIso E₂).hom =
      (twistUnitIso E₁).hom ≫ (DerivedCategory.singleFunctor X.Modules 0).map g := by
  have hl : (twistMap g).app (𝟙_ (Mod X)) ≫
      (MonoidalCategory.leftUnitor (C := Mod X) E₂).hom =
      (MonoidalCategory.leftUnitor (C := Mod X) E₁).hom ≫ g :=
    (congrArg (fun z => z ≫ _) (twistMap_app g _)).trans
      (MonoidalCategory.leftUnitor_naturality g)
  exact nat_three_isos (FTMap g) (unitHomotopyIso X)
    (((twist X E₁).mapDerivedCategorySingleFunctor 0).app (Stacks.Ample.unitModule X))
    (((twist X E₂).mapDerivedCategorySingleFunctor 0).app (Stacks.Ample.unitModule X))
    ((DerivedCategory.singleFunctor X.Modules 0).map ((twistMap g).app (𝟙_ (Mod X))))
    (NatTrans.mapDerivedCategory_app_singleFunctor (twistMap g) (Stacks.Ample.unitModule X))
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      (MonoidalCategory.leftUnitor (C := Mod X) E₁))
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      (MonoidalCategory.leftUnitor (C := Mod X) E₂))
    ((DerivedCategory.singleFunctor X.Modules 0).map g)
    (map_comp_congr _ hl)

/-- `(- ⊗ g^∨)~` commutes with the isomorphisms `(- ⊗ E^∨)~ (K⟦n⟧) ≅ ((- ⊗ E^∨)~ K)⟦n⟧`. -/
theorem GTMap_commShift (n : ℤ) (K : DerivedCategory X.Modules) :
    (GTMap g).app (K⟦n⟧) ≫ (GTCommShiftIso E₁ n K).hom =
      (GTCommShiftIso E₂ n K).hom ≫ ((GTMap g).app K)⟦n⟧' :=
  (NatTrans.shift_app_comm (NatTrans.mapDerivedCategory (twistMap (dualMap g))) n K).symm

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact f]
  [QuasiSeparated f]

/-- The inverse of the duality `Hom(E[0], ω_X^•⟦i⟧) ≃ₗ[k] Hom_k(H^{-i}(X, E), k)` is natural in
`E`: precomposition with `H^{-i}(X, g)` corresponds to precomposition with `g[0]`. -/
theorem extDuality_symm_naturality (i : ℤ)
    (φ : Module.Dual k (derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj E₂) (-i))) :
    letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
    letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
    (extDualityLinearEquiv f (singleQC E₁) i).symm
        ((ModuleCat.homLinearEquiv (S := k)).symm (φ ∘ₗ
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} k)
          (-i)).map ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom)) =
      (DerivedCategory.singleFunctor X.Modules 0).map g ≫
        (extDualityLinearEquiv f (singleQC E₂) i).symm
          ((ModuleCat.homLinearEquiv (S := k)).symm φ) := by
  let : Linear k X.Modules := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  apply (extDualityLinearEquiv f (singleQC E₁) i).injective
  rw [LinearEquiv.apply_symm_apply]
  refine Eq.trans ?_ (extDualityAddEquiv_naturality f (singleQC E₁) (singleQC E₂) i
    ((DerivedCategory.singleFunctor X.Modules 0).map g) _).symm
  show _ = _ ≫ (extDualityLinearEquiv f (singleQC E₂) i)
    ((extDualityLinearEquiv f (singleQC E₂) i).symm ((ModuleCat.homLinearEquiv (S := k)).symm φ))
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- An explicit formula for `dualityTwistLinearEquiv E f i φ` as the composite of its constituent
isomorphisms applied to `φ`. -/
theorem dualityTwistLinearEquiv_apply (E : Mod X)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (i : ℤ)
    (φ : Module.Dual k (derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj E) (-i))) :
    letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
    letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
    dualityTwistLinearEquiv E f i φ = (derivedCohomologyShiftIso f _ i).hom.hom
      (UnitCorepresentation.unitHomLinearEquiv f _ ((adjT E).homEquiv _ _
        ((twistUnitIso E).hom ≫ (extDualityLinearEquiv f (singleQC E) i).symm
          ((ModuleCat.homLinearEquiv (S := k)).symm φ)) ≫ (GTCommShiftIso E i _).hom)) := by
  let : Linear k X.Modules := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  show (derivedCohomologyShiftIso f _ i).hom.hom (UnitCorepresentation.unitHomLinearEquiv f _
    (((Iso.refl _).inv ≫ (adjT E).homEquiv _ _ (((twistUnitIso E).symm.inv ≫
      (extDualityLinearEquiv f (singleQC E) i).symm ((ModuleCat.homLinearEquiv (S := k)).symm φ)) ≫
        (Iso.refl _).hom)) ≫ (GTCommShiftIso E i _).hom)) = _
  rw [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rfl

/-- **The first chain of [Stacks, Tag 0BS4] is natural in `E`**: precomposition with
`H^{-i}(X, g)` on the left corresponds to `H^i(X, (- ⊗ g^∨)~(ω_X^•))` on the right. -/
theorem dualityTwistLinearEquiv_naturality (i : ℤ)
    (φ : Module.Dual k (derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj E₂) (-i))) :
    dualityTwistLinearEquiv E₁ f i (φ ∘ₗ ((DerivedCategory.homologyFunctor (ModuleCat.{u} k)
          (-i)).map ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
        ((derivedGlobalSectionsOver f).map ((GTMap g).app (dualizingComplexOverField f).obj))).hom
        (dualityTwistLinearEquiv E₂ f i φ) := by
  let : Linear k X.Modules := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  have a₁ := dualityTwistLinearEquiv_apply f E₁ i (φ ∘ₗ ((DerivedCategory.homologyFunctor
    (ModuleCat.{u} k) (-i)).map ((derivedGlobalSectionsOver f).map
      ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom)
  have a₂ := dualityTwistLinearEquiv_apply f E₂ i φ
  have hS := extDuality_symm_naturality g f i φ
  dsimp only at a₁ a₂ hS
  rw [a₁, a₂]
  refine (congrArg (fun β => (derivedCohomologyShiftIso f _ i).hom.hom
    (UnitCorepresentation.unitHomLinearEquiv f _ ((adjT E₁).homEquiv _ _
      ((twistUnitIso E₁).hom ≫ β) ≫ (GTCommShiftIso E₁ i _).hom))) hS).trans ?_
  set β₂ := (extDualityLinearEquiv f (singleQC E₂) i).symm
    ((ModuleCat.homLinearEquiv (S := k)).symm φ) with hβ
  have hsq := homEquiv_unit_square (adjT E₁) (adjT E₂) (FTMap g) (GTMap g) (adjT_unit_square g)
    (twistUnitIso E₁) (twistUnitIso E₂) _ (twistUnitIso_naturality g) β₂
  have hcs := GTMap_commShift g i (dualizingComplexOverField f).obj
  have h3 : (adjT E₁).homEquiv _ _ ((twistUnitIso E₁).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0).map g ≫ β₂) ≫
        (GTCommShiftIso E₁ i (dualizingComplexOverField f).obj).hom =
      ((adjT E₂).homEquiv _ _ ((twistUnitIso E₂).hom ≫ β₂) ≫
        (GTCommShiftIso E₂ i (dualizingComplexOverField f).obj).hom) ≫
        ((GTMap g).app (dualizingComplexOverField f).obj)⟦i⟧' := by
    rw [hsq, Category.assoc, hcs, Category.assoc]
  refine (congrArg (fun x => (derivedCohomologyShiftIso f _ i).hom.hom
    (UnitCorepresentation.unitHomLinearEquiv f _ x)) h3).trans ?_
  refine (congrArg (fun y => (derivedCohomologyShiftIso f _ i).hom.hom y)
    (UnitCorepresentation.unitHomLinearEquiv_naturality f _ _)).trans ?_
  have hn := (derivedCohomologyShiftNatIso f i).hom.naturality
    ((GTMap g).app (dualizingComplexOverField f).obj)
  exact congrArg (fun z => ModuleCat.Hom.hom z (UnitCorepresentation.unitHomLinearEquiv f _
    ((adjT E₂).homEquiv _ _ ((twistUnitIso E₂).hom ≫ β₂) ≫
      (GTCommShiftIso E₂ i (dualizingComplexOverField f).obj).hom))) hn

/-- Three commutative squares of isomorphisms paste. -/
theorem three_squares {𝒟 : Type*} [Category 𝒟] {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : 𝒟} (w : a₂ ⟶ a₁)
    (i₁ : a₁ ≅ b₁) (i₂ : a₂ ≅ b₂) (p : b₂ ⟶ b₁) (h₁ : w ≫ i₁.hom = i₂.hom ≫ p)
    (j₁ : b₁ ≅ c₁) (j₂ : b₂ ≅ c₂) (q : c₂ ⟶ c₁) (h₂ : p ≫ j₁.hom = j₂.hom ≫ q)
    (k₁ : c₁ ≅ d₁) (k₂ : c₂ ≅ d₂) (z : d₂ ⟶ d₁) (h₃ : q ≫ k₁.hom = k₂.hom ≫ z) :
    w ≫ (i₁ ≪≫ j₁ ≪≫ k₁).hom = (i₂ ≪≫ j₂ ≪≫ k₂).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- Two commutative squares of isomorphisms paste. -/
theorem two_squares {𝒟 : Type*} [Category 𝒟] {a₁ a₂ b₁ b₂ c₁ c₂ : 𝒟} (w : a₂ ⟶ a₁)
    (i₁ : a₁ ≅ b₁) (i₂ : a₂ ≅ b₂) (p : b₂ ⟶ b₁) (h₁ : w ≫ i₁.hom = i₂.hom ≫ p)
    (j₁ : b₁ ≅ c₁) (j₂ : b₂ ≅ c₂) (q : c₂ ⟶ c₁) (h₂ : p ≫ j₁.hom = j₂.hom ≫ q) :
    w ≫ (i₁ ≪≫ j₁).hom = (i₂ ≪≫ j₂).hom ≫ q := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h₁, h₂]

/-- The isomorphism `(- ⊗ E^∨)~ (ω_X[1]) ≅ (E^∨ ⊗ ω_X)[0]⟦1⟧` is natural in `E`: it intertwines
`(- ⊗ g^∨)~` with `((g^∨ ⊗ ω_X)[0])⟦1⟧`. -/
theorem GTDualizingIso_naturality [IsProper f] (hcm : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    (GTMap g).app (dualizingComplexOverField f).obj ≫
        (GTDualizingIsoOfIsCohenMacaulay E₁ f hcm hequi hdim).hom =
      (GTDualizingIsoOfIsCohenMacaulay E₂ f hcm hequi hdim).hom ≫
        ((DerivedCategory.singleFunctor X.Modules 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).map
            (dualMap g)).app (dualizingSheafOverField f)))⟦(1 : ℤ)⟧' := by
  have hbr := congrArg (fun τ => NatTrans.app τ (dualizingSheafOverField f))
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (R X)).inv.naturality (dualMap g))
  have hG3 := NatTrans.mapDerivedCategory_app_singleFunctor (twistMap (dualMap g))
    (dualizingSheafOverField f)
  refine three_squares _ _ _ _
    ((GTMap g).naturality (dualizingSheafShiftOneIsoOfIsCohenMacaulay f hcm hequi hdim).inv).symm
    _ _ _ (GTMap_commShift g 1 _) _ _ _ ?_
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  exact two_squares _ _ _ _ hG3 _ _ _
    (map_comp_congr (DerivedCategory.singleFunctor X.Modules 0) hbr)

/-- **The second display of [Stacks, Tag 0BS4] is natural in `E`**: for `g : E₁ ⟶ E₂` between
finite locally free modules, precomposition with `H^{-i}(X, g)` corresponds to
`H^{1+i}(X, g^∨ ⊗ ω_X)`, `g^∨` being the dual of `g`. -/
@[stacks 0BS4 "the second display: the canonical isomorphism is natural in the finite locally \
free E, for the dual map E_2^dual -> E_1^dual of E_1 -> E_2"]
theorem dualityTensorDualizingSheafLinearEquiv_naturality [IsProper f]
    (hcm : AlgebraicGeometry.IsCohenMacaulay X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (i : ℤ)
    (φ : Module.Dual k (derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj E₂) (-i))) :
    dualityTensorDualizingSheafLinearEquiv E₁ f hcm hequi hdim i
        (φ ∘ₗ ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map g))).hom) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (1 + i)).map
        ((derivedGlobalSectionsOver f).map ((DerivedCategory.singleFunctor X.Modules 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).map
            (dualMap g)).app (dualizingSheafOverField f))))).hom
        (dualityTensorDualizingSheafLinearEquiv E₂ f hcm hequi hdim i φ) := by
  have hc := dualityTwistLinearEquiv_naturality g f i φ
  have hD := GTDualizingIso_naturality g f hcm hequi hdim
  let F := derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) i
  have hmor := Stacks.DerivedTensor.RingedSite.paste_squares
    (F.map ((GTMap g).app (dualizingComplexOverField f).obj))
    (F.map (GTDualizingIsoOfIsCohenMacaulay E₁ f hcm hequi hdim).hom)
    (derivedCohomologyShiftOneIso f _ i).hom
    (F.map (GTDualizingIsoOfIsCohenMacaulay E₂ f hcm hequi hdim).hom)
    (F.map (((DerivedCategory.singleFunctor X.Modules 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).map
            (dualMap g)).app (dualizingSheafOverField f)))⟦(1 : ℤ)⟧'))
    (derivedCohomologyShiftOneIso f _ i).hom _
    (map_comp_congr F hD)
    (derivedCohomologyShiftOneIso_naturality f _ i)
  show (derivedCohomologyShiftOneIso f _ i).hom.hom ((F.map
      (GTDualizingIsoOfIsCohenMacaulay E₁ f hcm hequi hdim).hom).hom
      (dualityTwistLinearEquiv E₁ f i _)) = _
  rw [hc]
  exact congrArg (fun z => ModuleCat.Hom.hom z (dualityTwistLinearEquiv E₂ f i φ)) hmor

end Naturality

end Stacks.Duality.LocallyFreeTwist
