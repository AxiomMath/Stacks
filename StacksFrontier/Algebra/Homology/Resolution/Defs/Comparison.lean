module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute

/-!
# Left resolutions by objects of a given class

Let `Z` be an object of a category `C` with a zero object, and let `P` be a class of objects of
`C`. A *left resolution of `Z` by objects of `P`* is an exact complex

`… → F₂ → F₁ → F₀ → Z → 0`

in which every `Fᵢ` lies in `P`. As for `CategoryTheory.ProjectiveResolution`, such a
resolution is encoded as an `ℕ`-indexed chain complex `F` whose terms lie in `P`, together with a
morphism `π : F ⟶ Z[0]` to the complex concentrated in degree `0`; that `π` is a quasi-isomorphism
says exactly that the augmented complex `… → F₁ → F₀ → Z → 0` is exact.

For `C` the category of `R`-modules this is the notion of a left resolution of an `R`-module `M`
by objects of `P`: with `P = ⊤` a resolution `F_• → M`, with `P` the class of free `R`-modules a
resolution by free modules, and with `P` the class of finite free `R`-modules a resolution by
finite free modules. With `P` the class of projective objects it restates
`CategoryTheory.ProjectiveResolution`.

## Main definitions

* `CategoryTheory.ObjectProperty.LeftResolution P Z`: left resolutions of the object `Z` by
  objects of the class `P`.
* `CategoryTheory.ObjectProperty.LeftResolution.toProjectiveResolution`: a left resolution whose
  terms are projective, read as a `CategoryTheory.ProjectiveResolution`.
* `ModuleResolution R M`: resolutions `F_• → M` of an `R`-module `M`.
* `FreeModuleResolution R M`: resolutions of `M` by free `R`-modules.
* `FiniteFreeModuleResolution R M`: resolutions of `M` by finite free `R`-modules.

## Main results

* `nonempty_freeModuleResolution_iff`: `M` has a resolution by free `R`-modules if and only if
  it has a resolution whose terms are free.
* `nonempty_finiteFreeModuleResolution_iff`: `M` has a resolution by finite free `R`-modules if
  and only if it has a resolution by free `R`-modules whose terms are finitely generated.

## References

* [Stacks Project, Tag 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- A `P.LeftResolution Z` consists of a bundled `ℕ`-indexed chain complex whose terms lie in the
class `P`, along with a quasi-isomorphism to the complex consisting of just `Z` supported in
degree `0`; equivalently, an exact complex `… → F₁ → F₀ → Z → 0` with all `Fᵢ` in `P`. -/
@[stacks 00LQ]
public structure LeftResolution (P : ObjectProperty C) (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C ℕ
  /-- the terms of the chain complex must belong to the class `P` -/
  property : ∀ n, P (complex.X n)
  /-- the chain complex must have homology -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` must be a
  quasi-isomorphism, i.e. `… → F₁ → F₀ → Z → 0` is exact -/
  quasiIso : QuasiIso π := by infer_instance

attribute [instance] LeftResolution.hasHomology LeftResolution.quasiIso

/-- A left resolution of `Z` whose terms are projective, read as a projective resolution of `Z`. -/
public def LeftResolution.toProjectiveResolution {P : ObjectProperty C} {Z : C}
    (F : P.LeftResolution Z) (hP : ∀ n, Projective (F.complex.X n)) : ProjectiveResolution Z where
  complex := F.complex
  projective := hP
  π := F.π

end CategoryTheory.ObjectProperty

end

@[expose] public section

open CategoryTheory

universe u v

/-- A (left) *resolution* `F_• → M` of an `R`-module `M`: an exact chain complex
`… → F₂ → F₁ → F₀ → M → 0` of `R`-modules, encoded as an ℕ-indexed chain
complex together with a quasi-isomorphism to `M` in degree `0`. -/
@[stacks_fixed 00LQ "resolution", sga "4½ Etat_0 3.1.8" "special case"]
structure ModuleResolution (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] where
  /-- The underlying chain complex `… → F₂ → F₁ → F₀`. -/
  complex : ChainComplex (ModuleCat.{v} R) ℕ
  /-- The chain complex has homology in each degree. -/
  hasHomology : ∀ i, HomologicalComplex.HasHomology complex i
  /-- The augmentation `F_• → M` (as a chain map to `M` in degree `0`). -/
  π : complex ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj (ModuleCat.of R M)
  /-- The augmentation is a quasi-isomorphism — equivalently, the complex
  `… → F₁ → F₀ → M → 0` is exact. -/
  quasiIso : QuasiIso π

/-- A *resolution of `M` by free `R`-modules*: a resolution `F_• → M` such that
every `F_i` is a free `R`-module. -/
@[stacks_fixed 00LQ "free resolution", ega "0 11.4.1"]
structure FreeModuleResolution (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] extends ModuleResolution R M where
  /-- Every term `F_i` of the resolution is a free `R`-module. -/
  free : ∀ n, Module.Free R (toModuleResolution.complex.X n)

/-- A *resolution of `M` by finite free `R`-modules*: a resolution `F_• → M`
such that every `F_i` is a free and finitely generated `R`-module. -/
@[stacks_fixed 00LQ "finite free resolution"]
structure FiniteFreeModuleResolution (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] extends FreeModuleResolution R M where
  /-- Every term `F_i` is moreover finitely generated. -/
  finite : ∀ n, Module.Finite R (toFreeModuleResolution.complex.X n)

/-- `M` admits a resolution by free `R`-modules if and only if it admits a resolution
whose terms are all free `R`-modules. -/
theorem nonempty_freeModuleResolution_iff (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    Nonempty (FreeModuleResolution R M) ↔
      ∃ F : ModuleResolution R M, ∀ n, Module.Free R (F.complex.X n) :=
  ⟨fun ⟨F⟩ => ⟨F.toModuleResolution, F.free⟩, fun ⟨F, hF⟩ => ⟨⟨F, hF⟩⟩⟩

/-- `M` admits a resolution by finite free `R`-modules if and only if it admits a
resolution by free `R`-modules whose terms are all finitely generated. -/
theorem nonempty_finiteFreeModuleResolution_iff (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] :
    Nonempty (FiniteFreeModuleResolution R M) ↔
      ∃ F : FreeModuleResolution R M, ∀ n, Module.Finite R (F.complex.X n) :=
  ⟨fun ⟨F⟩ => ⟨F.toFreeModuleResolution, F.finite⟩, fun ⟨F, hF⟩ => ⟨⟨F, hF⟩⟩⟩

end
