module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
import StacksCore.Tactic.EgaSgaAttribute

/-! # Stalks and skyscrapers at a point of a topos

## Main results

* `ToposPoint`: a point of a topos, packaged as an adjoint pair with left-exact left adjoint.
* `ToposPoint.skyscraper`, `ToposPoint.stalk`: the skyscraper object `p_* E` and the stalk
  `p⁻¹ F` at a point.
* `ToposPoint.epsilon`, `ToposPoint.eta`: the two canonical maps `(p_* E)_p ⟶ E` and
  `E ⟶ (p_* E)_p`.
* `ToposPoint.epsilon_comp_eta`: their composite `E ⟶ (p_* E)_p ⟶ E` is the identity
  (Stacks 05UX).

Tags covered: 05UX.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

/-- A point of a topos `D` is an adjoint pair of functors `p⁻¹ ⊣ p_*` between
`D` and `Type v`, with `p⁻¹` left exact (i.e. preserving finite limits).

This abstracts the notion of a morphism of topoi `Sh(pt) → Sh(C)` from the
Stacks Project (Tag 05UX): in that setting, `D = Sh(C)`, `p⁻¹` is the
inverse image functor, and `p_*` is the direct image functor; the adjunction
`p⁻¹ ⊣ p_*` is required and `p⁻¹` is automatically left exact for a point. -/
@[sga "4 IV 6.1", sga "4 IV 3.1" "special case", sga "4 IV 4.6.2" "partial", sga "4 VIII 7.8"]
structure ToposPoint (D : Type u) [Category.{v} D] where
  /-- The inverse image functor `p⁻¹ : Sh(C) ⥤ Set`. -/
  pInv : D ⥤ Type v
  /-- The direct image functor `p_* : Set ⥤ Sh(C)`. -/
  pStar : Type v ⥤ D
  /-- The adjunction `p⁻¹ ⊣ p_*`. -/
  adj : pInv ⊣ pStar
  /-- The functor `p⁻¹` is left exact (preserves finite limits). -/
  pInvLex : PreservesFiniteLimits pInv

namespace ToposPoint

variable {D : Type u} [Category.{v} D] (p : ToposPoint D)

/-- `p_*` is a right adjoint, hence preserves all limits. -/
@[sga "4 IV 3.1.2" "special case"]
noncomputable instance pStarPreservesLimits : PreservesLimits p.pStar :=
  p.adj.rightAdjoint_preservesLimits

/-- The skyscraper sheaf at `p` with value `E` is `p_* E`. -/
def skyscraper (E : Type v) : D := p.pStar.obj E

/-- The stalk of a sheaf `F` at the point `p` is `p⁻¹ F`. -/
def stalk (F : D) : Type v := p.pInv.obj F

/-- `p_*(*)` is terminal in `D`. -/
noncomputable def pStarPUnitIsTerminal :
    IsTerminal (p.pStar.obj PUnit.{v+1}) :=
  IsTerminal.isTerminalObj p.pStar _ Types.isTerminalPUnit

/-- `p⁻¹(p_*(*))` is terminal in `Type v`. -/
noncomputable def pInvPStarPUnitIsTerminal :
    IsTerminal (p.pInv.obj (p.pStar.obj PUnit.{v+1})) := by
  haveI : PreservesLimit (Functor.empty.{0} D) p.pInv :=
    p.pInvLex.preservesFiniteLimits _ |>.preservesLimit
  exact IsTerminal.isTerminalObj p.pInv _ p.pStarPUnitIsTerminal

/-- `p⁻¹(p_*(*))` is a singleton. -/
noncomputable instance starUnique :
    Unique (p.pInv.obj (p.pStar.obj PUnit.{v+1})) :=
  (p.pInvPStarPUnitIsTerminal.uniqueUpToIso Types.isTerminalPUnit).toEquiv.unique

/-- The canonical map `ε_E : (p_* E)_p ⟶ E`, namely the counit at `E`. -/
def epsilon (E : Type v) : p.pInv.obj (p.pStar.obj E) → E :=
  p.adj.counit.app E

/-- The canonical map `η_E : E ⟶ (p_* E)_p`, defined elementwise. -/
noncomputable def eta (E : Type v) : E → p.pInv.obj (p.pStar.obj E) :=
  fun e => p.pInv.map (p.pStar.map (↾fun (_ : PUnit.{v+1}) => e)) default

/-- **Stacks 05UX.** For any set `E` there are canonical maps
`E ⟶ (p_* E)_p ⟶ E` whose composition is the identity of `E`.

Proof: apply naturality of the counit `ε` of `p⁻¹ ⊣ p_*` to the constant map
`i_e : PUnit → E`, then evaluate at `default : p⁻¹(p_*(PUnit))`. -/
@[stacks 05UX]
theorem epsilon_comp_eta (E : Type v) : p.epsilon E ∘ p.eta E = id := by
  funext e
  exact ConcreteCategory.congr_hom (p.adj.counit.naturality (↾fun _ : PUnit.{v+1} => e))
    (default : p.pInv.obj (p.pStar.obj PUnit.{v+1}))

end ToposPoint
