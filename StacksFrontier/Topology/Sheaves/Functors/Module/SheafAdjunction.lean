module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
# Adjointness of Mathlib's abstract pullback and the pushforward of sheaves of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces and `O` a sheaf of rings on `Y`.
This file records Mathlib's adjunction `SheafOfModules.pullbackPushforwardAdjunction` over
the ring `f⁻¹O = (TopCat.Sheaf.pullback RingCat f).obj O`, where the `O`-module structure on
`f_*F` comes by restriction of scalars along the unit `O ⟶ f_*f⁻¹O` of the corresponding
adjunction on sheaves of rings (`adjunctionUnit`).

Mathlib's `SheafOfModules.pullback` is defined as the left adjoint of the pushforward, chosen
abstractly; it is not the concrete inverse image `f⁻¹G` of Stacks Tag 008X. Stacks Tag 008Y
for the concrete inverse image is
`InverseImageModules.inverseImageModulesHomEquiv` in
`StacksFrontier.Topology.Sheaves.Functors.Module.InverseImageAdjunction`; here
`adjointPullbackPushforward` and `homEquivPullbackPushforward` are the abstract counterparts.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u


variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Sheaf RingCat.{u} Y)

/-- The sheaf-of-rings pullback `f⁻¹O` on `X` of a sheaf of rings `O` on `Y` along a
continuous map `f : X → Y`. This is the sheafification of the presheaf
`U ↦ colim_{V ⊇ f(U)} O(V)`, equipped with its natural ring structure. -/
@[ega "0 3.5.3" "partial, special case", ega "0 3.7.1" "more general"]
noncomputable def invImageRings : TopCat.Sheaf RingCat.{u} X :=
  (TopCat.Sheaf.pullback RingCat.{u} f).obj O

/-- The pushforward `f_*` on sheaves of rings, expressed through `sheafPushforwardContinuous`
(definitionally equal to `TopCat.Sheaf.pushforward RingCat f`). This is the form used by
`SheafOfModules.pushforward`. -/
noncomputable abbrev pushforwardRings008Y :
    TopCat.Sheaf RingCat.{u} X ⥤ TopCat.Sheaf RingCat.{u} Y :=
  (Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The canonical morphism `O ⟶ f_*(f⁻¹O)` of sheaves of rings on `Y`. This is the unit of
the adjunction `f⁻¹ ⊣ f_*` for sheaves of rings, evaluated at `O`. It is the data used to
view a sheaf of `f⁻¹O`-modules `F` pushed forward to `Y` as a sheaf of `O`-modules (by
restriction of scalars). -/
@[sga "4 IV 11.2.1" "special case"]
noncomputable def adjunctionUnit :
    O ⟶ (pushforwardRings008Y f).obj (invImageRings f O) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app O

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- The pushforward functor on sheaves of modules: from sheaves of `f⁻¹O`-modules on `X`
to sheaves of `O`-modules on `Y`, where the `O`-module structure on `f_*F` comes by
restriction of scalars along the canonical adjunction unit `O → f_*f⁻¹O`. -/
@[ega "0 12.2.1" "special case", ega "0 4.2.1" "special case"]
noncomputable abbrev pushforwardModules008Y :
    SheafOfModules.{u} (invImageRings f O) ⥤ SheafOfModules.{u} O :=
  SheafOfModules.pushforward.{u} (adjunctionUnit f O)

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback functor on sheaves of modules: from sheaves of `O`-modules on `Y` to
sheaves of `f⁻¹O`-modules on `X`. -/
@[ega "0 4.3.1", sga "7 XIV 4.5"]
noncomputable abbrev pullbackModules008Y :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} (invImageRings f O) :=
  SheafOfModules.pullback.{u} (adjunctionUnit f O)

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- Adjointness of Mathlib's abstract pullback and the pushforward of sheaves of modules.

For a continuous map `f : X → Y` of topological spaces and a sheaf of rings `O` on `Y`,
Mathlib's pullback functor on sheaves of modules
`SheafOfModules.pullback : SheafOfModules O ⥤ SheafOfModules (f⁻¹O)`, defined as the
(abstractly chosen) left adjoint of the pushforward, is left adjoint to the pushforward
functor `f_* : SheafOfModules (f⁻¹O) ⥤ SheafOfModules O`, where:

* `f⁻¹O = (TopCat.Sheaf.pullback RingCat f).obj O` is the canonical pullback sheaf of
  rings;
* the sheaf-of-`O`-module structure on `f_*F` (for `F` a sheaf of `f⁻¹O`-modules) is
  obtained by restriction of scalars along the canonical adjunction unit
  `O → f_*f⁻¹O` for sheaves of rings (i.e. `adjunctionUnit f O`).

This is Mathlib's `SheafOfModules.pullbackPushforwardAdjunction` at that unit. Stacks
Tag 008Y, for the concrete inverse image `f⁻¹G` of Tag 008X, is
`InverseImageModules.inverseImageModulesHomEquiv`. -/
noncomputable def adjointPullbackPushforward :
    SheafOfModules.pullback.{u} (adjunctionUnit f O) ⊣
      SheafOfModules.pushforward.{u} (adjunctionUnit f O) :=
  SheafOfModules.pullbackPushforwardAdjunction (adjunctionUnit f O)

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence form of `adjointPullbackPushforward`: the pullback functor on sheaves of
modules admits the pushforward as a right adjoint. -/
@[ega "0 4.4.3" "(4.4.3.1), special case",
  sga "4 IV 13.4" "(13.4.1) for (X",
  sga "4 IV 14.2" "partial",
  sga "4 Vbis 1.3.6" "adjunction φ* ⊣ φ_*"]
theorem adjoint_pullback_pushforward :
    Nonempty
      (SheafOfModules.pullback.{u} (adjunctionUnit f O) ⊣
        SheafOfModules.pushforward.{u} (adjunctionUnit f O)) :=
  ⟨adjointPullbackPushforward f O⟩

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- Hom-set form of `adjointPullbackPushforward`: the natural bijection
```
  Mor_{Mod(f⁻¹O)}(f⁻¹G, F) ≃ Mor_{Mod(O)}(G, f_*F)
```
for a sheaf of `O`-modules `G` on `Y` and a sheaf of `f⁻¹O`-modules `F` on `X`,
where `f_*F` is viewed as an `O`-module by restriction of scalars along
`O → f_*f⁻¹O`. It is the hom-set bijection of `adjointPullbackPushforward`, so it is
bifunctorial in `G` and `F` by `Adjunction.homEquiv_naturality_left` and
`Adjunction.homEquiv_naturality_right`. Here the pullback is Mathlib's abstract left
adjoint; for Stacks Tag 008Y with the concrete inverse image of Tag 008X see
`InverseImageModules.inverseImageModulesHomEquiv`. -/
noncomputable def homEquivPullbackPushforward
    (G : SheafOfModules.{u} O) (F : SheafOfModules.{u} (invImageRings f O)) :
    ((SheafOfModules.pullback.{u} (adjunctionUnit f O)).obj G ⟶ F) ≃
      (G ⟶ (SheafOfModules.pushforward.{u} (adjunctionUnit f O)).obj F) :=
  (adjointPullbackPushforward f O).homEquiv G F

-- isDefEq transparency bump: `TopCat.Sheaf` against `Sheaf J RingCat`
set_option backward.isDefEq.respectTransparency.types false in
/-- Existence form of `homEquivPullbackPushforward`: the two hom-sets of Stacks 008Y are in
bijection. -/
theorem homEquiv_pullback_pushforward
    (G : SheafOfModules.{u} O) (F : SheafOfModules.{u} (invImageRings f O)) :
    Nonempty
      (((SheafOfModules.pullback.{u} (adjunctionUnit f O)).obj G ⟶ F) ≃
        (G ⟶ (SheafOfModules.pushforward.{u} (adjunctionUnit f O)).obj F)) :=
  ⟨homEquivPullbackPushforward f O G F⟩

