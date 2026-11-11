module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Enumerative.DyckWord
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left adjoints of restriction to an open subspace

Let `(X, O)` be a ringed space and let `j : (U, O|_U) → (X, O)` be the inclusion of an open
subspace. This file names the restriction functors `j^{-1}` on presheaves and on sheaves of modules
and Mathlib's abstract left adjoints of them, `PresheafOfModules.pullback` and
`SheafOfModules.pullback` along the identity comparison morphism `O|_U → j^{-1} O`. Mathlib defines
these left adjoints as a chosen left adjoint of the pushforward (`(pushforward φ).leftAdjoint`), so
the adjunctions below hold by construction.

They are the functors used by the files that import this one. Stacks 00A7 itself, about the
*explicit* extension by zero `j_{p!}F(V) = F(V)` for `V ⊆ U`, `0` otherwise, and its
sheafification `j_!`, is formalized in
`StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExplicit`
(`ExtensionByZeroModules.extendByZeroAdjunction`,
`ExtensionByZeroModules.jShriekExplicitAdjunction`,
`ExtensionByZeroModules.isZero_stalk_jShriekExplicit`,
`ExtensionByZeroModules.stalkJShriekExplicitLinearEquiv` and
`ExtensionByZeroModules.jShriekExplicitCompJStarIso`); that file also identifies the explicit
construction with Mathlib's abstract left adjoint.

## Main definitions

* `jpShriek`, `jShriek00A7`: Mathlib's abstract left adjoints of restriction (they are
  isomorphic to the extension-by-zero functors `j_{p!}` and `j_!`, see above).
* `restPMod`, `restMod`: the restriction functors on presheaves and on sheaves of modules.

## Main results

* `jpShriekAdjunction`: `jpShriek` is left adjoint to restriction of presheaves of modules.
* `jShriekAdjunction`: `jShriek00A7` is left adjoint to restriction of sheaves of modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


universe u

variable (X : SheafedSpace RingCat.{u}) (U : Opens X.carrier)

/-! ### Presheaf-level setup -/

/-- The underlying presheaf of rings on `X` coming from the structure sheaf. -/
noncomputable def OXpre : TopCat.Presheaf RingCat.{u} X.carrier := X.presheaf

/-- The image functor on opens induced by the open embedding `j : U ↪ X`. -/
noncomputable def jFun :
    Opens ((Opens.toTopCat _).obj U) ⥤ Opens X.carrier :=
  U.isOpenEmbedding.functor

/-- The underlying presheaf of rings on `U`. -/
@[sga "4 IV 14.1" "special case"]
noncomputable def OUpre : TopCat.Presheaf RingCat.{u} ((Opens.toTopCat _).obj U) :=
  (jFun X U).op ⋙ OXpre X

/-- The canonical comparison `O|_U → j^{-1} O` of presheaves of rings on `U`, the identity. -/
noncomputable def phiPre : OUpre X U ⟶ (jFun X U).op ⋙ OXpre X := 𝟙 _

/-- The restriction functor `j^{-1} : PMod(O) ⥤ PMod(O|_U)`. -/
@[sga "3 I 3.1.4" "special case", sga "4 IV 11.2.2" "special case"]
noncomputable def restPMod :
    PresheafOfModules.{u} (OXpre X) ⥤ PresheafOfModules.{u} (OUpre X U) :=
  PresheafOfModules.pushforward (phiPre X U)

/-- The left adjoint `PMod(O|_U) ⥤ PMod(O)` of restriction, Mathlib's abstract
`PresheafOfModules.pullback` (defined as a chosen left adjoint). It is isomorphic to the explicit
extension by zero `j_{p!}` of Stacks 00A4, but this is not part of its definition. -/
@[sga "4 IV 11.3.1" "special case"]
noncomputable def jpShriek :
    PresheafOfModules.{u} (OUpre X U) ⥤ PresheafOfModules.{u} (OXpre X) :=
  PresheafOfModules.pullback (phiPre X U)

/-! ### Sheaf-level setup -/

/-- The structure sheaf of `X` viewed as a sheaf of rings. -/
@[ega "0 4.1.1" "partial", sga "4 Vbis 4.2.0" "partial"]
noncomputable def OXSh :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} := X.sheaf

/-- The functor `jFun X U` is continuous for the Grothendieck topologies of open covers. -/
@[sga "4 III 1.9.2", sga "4 III 2.7" "continuity of Φ"]
instance instContinuousJFun : (jFun X U).IsContinuous
    (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) :=
  U.isOpenEmbedding.functor_isContinuous

/-- The restricted structure sheaf `O|_U`. -/
@[sga "4 IV 14.1" "special case"]
noncomputable def OUSh :
    Sheaf (Opens.grothendieckTopology ((Opens.toTopCat _).obj U)) RingCat.{u} :=
  ((jFun X U).sheafPushforwardContinuous RingCat.{u} _ _).obj (OXSh X)

/-- The canonical comparison `O|_U → j^{-1} O` of sheaves of rings on `U`, the identity. -/
noncomputable def phiSh :
    OUSh X U ⟶ ((jFun X U).sheafPushforwardContinuous _ _ _).obj (OXSh X) :=
  𝟙 _

/-- The restriction functor `j^{-1} : Mod(O) ⥤ Mod(O|_U)`. -/
@[sga "4 IV 11.2.2" "special case"]
noncomputable def restMod :
    SheafOfModules.{u} (OXSh X) ⥤ SheafOfModules.{u} (OUSh X U) :=
  SheafOfModules.pushforward (phiSh X U)

-- isDefEq transparency bump: infer jFun through sheaf-of-rings defs
set_option backward.isDefEq.respectTransparency.types false in
/-- The left adjoint `Mod(O|_U) ⥤ Mod(O)` of restriction, Mathlib's abstract
`SheafOfModules.pullback` (defined as a chosen left adjoint). It is isomorphic to the extension by
zero `j_!` of Stacks 00A4, but this is not part of its definition. -/
@[sga "2 I 1.7" "special case",
  sga "4 IV 11.3.1" "special case",
  sga "4 IV 14.2",
  sga "4 XVII 5.1.1" "partial",
  sga "4½ Arcata 6.1" "partial",
  sga "4½ Etat_0 6.2" "Ringed-space case"]
noncomputable def jShriek00A7 :
    SheafOfModules.{u} (OUSh X U) ⥤ SheafOfModules.{u} (OXSh X) :=
  SheafOfModules.pullback (phiSh X U)

/-! ### The adjunctions -/

/-- The adjunction between Mathlib's abstract left adjoint `jpShriek` and restriction of presheaves
of modules; it holds by the definition of `jpShriek`. For Stacks 00A7 (1), about the explicit
extension by zero, see `ExtensionByZeroModules.extendByZeroAdjunction`. -/
@[sga "4 IV 11.3.1" "presheaves on a space"]
noncomputable def jpShriekAdjunction : jpShriek X U ⊣ restPMod X U :=
  PresheafOfModules.pullbackPushforwardAdjunction _

-- isDefEq transparency bump: infer jFun through sheaf-of-rings defs
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction between Mathlib's abstract left adjoint `jShriek00A7` and restriction of sheaves
of modules; it holds by the definition of `jShriek00A7`. For Stacks 00A7 (2), about the
sheafification of the explicit extension by zero, see
`ExtensionByZeroModules.jShriekExplicitAdjunction`. -/
@[sga "4 IV 11.3.1" "ringed space, open U",
  sga "4 XVII 5.1.1" "ringed spaces, modules",
  sga "2 I 1.7" "special case",
  sga "4 IV 14.2" "partial"]
noncomputable def jShriekAdjunction : jShriek00A7 X U ⊣ restMod X U :=
  SheafOfModules.pullbackPushforwardAdjunction _

-- isDefEq transparency bump: infer jFun through sheaf-of-rings defs
set_option backward.isDefEq.respectTransparency.types false in
/-- Mathlib's abstract left adjoints `jpShriek` and `jShriek00A7` are left adjoint to the
restriction functors on presheaves and on sheaves of modules (by their definition). -/
@[sga "2 I 1.7" "special case",
  sga "4 IV 11.3.1" "special case",
  sga "4 IV 14.2" "partial",
  sga "4 V 2.2" "partial",
  sga "4 XVII 5.1.1" "partial"]
theorem jShriek_adjunctions :
    Nonempty (jpShriek X U ⊣ restPMod X U) ∧
    Nonempty (jShriek00A7 X U ⊣ restMod X U) :=
  ⟨⟨jpShriekAdjunction X U⟩, ⟨jShriekAdjunction X U⟩⟩
