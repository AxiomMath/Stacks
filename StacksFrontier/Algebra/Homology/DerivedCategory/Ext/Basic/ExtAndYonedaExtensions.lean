module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.Triangulated.Elementary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ext groups and Yoneda extensions

Let `𝒜` be an abelian category. The extension groups of `𝒜` are the Hom-groups of its derived
category, `Ext^i_𝒜(X, Y) = Hom_{D(𝒜)}(X, Y⟦i⟧)`, and for objects `A`, `B` of `𝒜` itself,
`Ext^i_𝒜(A, B) = Hom_{D(𝒜)}(A[0], B[0]⟦i⟧)`, which for `i = (n : ℕ)` is Mathlib's
`CategoryTheory.Abelian.Ext A B n`. This file defines these groups, and the Yoneda extensions
of an object by another together with their equivalence relation.

## Main definitions

* `CategoryTheory.DerivedCategory.Ext`, `CategoryTheory.Abelian.zExt`: the extension groups.
* `CategoryTheory.Abelian.YonedaExtension`: a degree `n + 1` Yoneda extension of `B` by `A`.
* `CategoryTheory.Abelian.YonedaExtension.Equivalent`: equivalence of Yoneda extensions.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

/-! ### Ext groups in the derived category -/

section ExtDefinition

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The `i`-th extension group `Ext^i_𝒜(X, Y) = Hom_{D(𝒜)}(X, Y⟦i⟧)` of an object `X` of the
derived category `D(𝒜)` of an abelian category `𝒜` by an object `Y`, for `i : ℤ`. It is
canonically identified with `Hom_{D(𝒜)}(X⟦-i⟧, Y)` via the adjunction between the shifts
`⟦-i⟧ ⊣ ⟦i⟧`. -/
@[stacks 06XQ, sga "4½ Etat_0 3.2.1"]
public noncomputable abbrev DerivedCategory.Ext (X Y : DerivedCategory C) (i : ℤ) : Type _ :=
  ShiftedHom X Y i

/-- The `i`-th extension group `Ext^i_𝒜(A, B) = Ext^i_𝒜(A[0], B[0])` of an object `A` of an
abelian category `𝒜` by an object `B`, for `i : ℤ`, where `A[0]` is the image of `A` under
`𝒜 ⥤ D(𝒜)`, the complex concentrated in degree `0`. For `i = (n : ℕ)` this is Mathlib's
`CategoryTheory.Abelian.Ext A B n`, up to the equivalence `Abelian.Ext.homEquiv`. -/
@[stacks 06XQ, sga "4½ Etat_0 3.2.1" "degree-0 objects"]
public noncomputable abbrev Abelian.zExt (A B : C) (i : ℤ) : Type _ :=
  DerivedCategory.Ext ((DerivedCategory.singleFunctor C 0).obj A)
    ((DerivedCategory.singleFunctor C 0).obj B) i

end ExtDefinition

namespace Abelian

open Limits ComposableArrows

/-! ### Yoneda extensions -/

section YonedaDefinition

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- A *degree `n + 1` Yoneda extension of `B` by `A`* in an abelian category `𝒜` is an exact
sequence `0 → A → Z_n → Z_{n - 1} → ⋯ → Z_0 → B → 0` in `𝒜`. It is given by the sequence
`Z : Fin (n + 1) ⥤ 𝒜` of its middle terms, `Z.obj' k = Z_{n - k}`, together with the outer
maps `f : A ⟶ Z.left = Z_n` and `g : Z.right = Z_0 ⟶ B`, and by the exactness of the sequence
at each of `A`, `Z_n, …, Z_0` and `B`. For `n = 0` this is a short exact sequence
`0 → A → Z_0 → B → 0`. -/
@[stacks 06XT]
public structure YonedaExtension (B A : 𝒜) (n : ℕ) where
  /-- The middle terms `Z_n → Z_{n - 1} → ⋯ → Z_0` of the extension. -/
  Z : ComposableArrows 𝒜 n
  /-- The map `A → Z_n` the extension starts with. -/
  f : A ⟶ Z.left
  /-- The map `Z_0 → B` the extension ends with. -/
  g : Z.right ⟶ B
  /-- The sequence is exact at `A`. -/
  [mono_f : Mono f]
  /-- The sequence `A → Z_n → ⋯ → Z_0` is a complex, exact at `Z_n, …, Z_1`. -/
  exact : (Z.precomp f).Exact
  /-- The sequence is exact at `Z_0`: the two-term sequence `Z_1 → Z_0 → B` is exact, where
  `Z_1 ⟶ Z_0` is read off as `(Z.precomp f).map' n (n + 1)`, which for `n = 0` is `f`. -/
  exact_g : (mk₂ ((Z.precomp f).map' n (n + 1)) g).Exact
  /-- The sequence is exact at `B`. -/
  [epi_g : Epi g]

attribute [instance] YonedaExtension.mono_f YonedaExtension.epi_g

variable {B A : 𝒜} {n : ℕ}

/-- Two degree `n + 1` Yoneda extensions `E`, `E'` of `B` by `A` in an abelian category are
*equivalent* if there exists a degree `n + 1` Yoneda extension `E''` of `B` by `A` and maps
`φ : E''.Z ⟶ E.Z` and `ψ : E''.Z ⟶ E'.Z` of the middle terms which are compatible with the
maps from `A` and the maps to `B`, i.e. such that the two diagrams obtained by putting `E''`
between `E` and `E'` commute, with the identity on `A` and on `B`. -/
@[stacks 06XT]
public def YonedaExtension.Equivalent (E E' : YonedaExtension B A n) : Prop :=
  ∃ (E'' : YonedaExtension B A n) (φ : E''.Z ⟶ E.Z) (ψ : E''.Z ⟶ E'.Z),
    E''.f ≫ app' φ 0 = E.f ∧ app' φ n ≫ E.g = E''.g ∧
      E''.f ≫ app' ψ 0 = E'.f ∧ app' ψ n ≫ E'.g = E''.g

end YonedaDefinition

end Abelian

end CategoryTheory

end
