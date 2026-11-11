module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
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
# The abstract left adjoint of the pushforward over `f_*𝒪`

Let `f : X ⟶ Y` be a continuous map and `𝒪` a sheaf of rings on `X`, so that `f_*𝒪` is a
sheaf of rings on `Y`. This file records the pushforward `ℱ ↦ f_*ℱ` from sheaves of
`𝒪`-modules to sheaves of `f_*𝒪`-modules (`pushforwardModule`) and Mathlib's left adjoint of it
(`tensorPullbackModule`), together with the adjunction between them
(`pullbackPushforwardAdjunction008Z`).

`tensorPullbackModule` is `SheafOfModules.forget ⋙ PresheafOfModules.pullback ⋙ sheafification`,
where `PresheafOfModules.pullback` is Mathlib's *abstract* left adjoint of the presheaf
pushforward: it is not the tensor product `𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢` of Stacks 008Z, and nothing
here identifies it with that tensor product. Stacks 008Z, with its explicit tensor product along
the canonical map `f^{-1}f_*𝒪 ⟶ 𝒪`, is `TensorInverseImagePushforward.adjunction` in
`StacksFrontier.Topology.Sheaves.Functors.Module.TensorInverseImagePushforward`, where
`TensorInverseImagePushforward.tensorFunctorIsoTensorPullbackModule` identifies the explicit
functor with `tensorPullbackModule`.

Both functors here are taken along `canonicalRingHom`, the identity `𝟙 (f_*𝒪)`, which is the
transpose of the counit `f^{-1}f_*𝒪 ⟶ 𝒪` under the `(f^{-1}, f_*)` adjunction.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- The functor `V ↦ f^{-1}V` on opens induced by a continuous map `f : X ⟶ Y`. -/
@[sga "4 III 1.9.1", sga "4 IV 4.1.1" "the functor f^{-1}"]
abbrev opensMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Functor (Opens Y) (Opens X) :=
  Opens.map f

/-- The pushforward functor `f_*` on sheaves of rings, `(f_*𝒪)(V) = 𝒪(f^{-1}V)`. -/
noncomputable def pushforwardSheafRing {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) RingCat.{u} :=
  (opensMap f).sheafPushforwardContinuous RingCat _ _

/-- The sheaf of rings `f_*𝒪` on `Y` obtained by pushing forward `𝒪`. -/
noncomputable def pushOfRing {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Sheaf (Opens.grothendieckTopology Y) RingCat.{u} :=
  (pushforwardSheafRing f).obj 𝒪

/-- Transpose of the Stacks counit `c : f⁻¹ f_*𝒪 ⟶ 𝒪` under the `(f⁻¹, f_*)`
adjunction: the identity `𝟙 (f_*𝒪)`. -/
noncomputable def canonicalRingHom {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    pushOfRing f 𝒪 ⟶ (pushforwardSheafRing f).obj 𝒪 :=
  𝟙 (pushOfRing f 𝒪)

/-- The pushforward `f_* : Mod(𝒪) ⥤ Mod(f_*𝒪)` on sheaves of modules, the `f_*𝒪`-module
structure on `f_*ℱ` coming by restriction of scalars along `canonicalRingHom`. -/
@[ega "0 12.2.1" "special case", ega "0 4.2.1", sga "4 Vbis 1.3.6" "special case"]
noncomputable def pushforwardModule {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.{u} 𝒪 ⥤ SheafOfModules.{u} (pushOfRing f 𝒪) :=
  SheafOfModules.pushforward (canonicalRingHom f 𝒪)

-- isDefEq transparency bump: infer `F` through the pushforward definitions
set_option backward.isDefEq.respectTransparency.types false in
/-- Mathlib's left adjoint of the pushforward `f_* : Mod(𝒪) ⥤ Mod(f_*𝒪)`: the composition
`forget ⋙ PresheafOfModules.pullback ⋙ sheafification`, where `PresheafOfModules.pullback` is the
abstract left adjoint of the presheaf pushforward. It is not built as the tensor product
`𝒪 ⊗_{f⁻¹ f_*𝒪} f⁻¹(–)`; it is isomorphic to it by uniqueness of adjoints
(`TensorInverseImagePushforward.tensorFunctorIsoTensorPullbackModule`). -/
@[ega "0 4.3.1" "special case", sga "4 XVII 4.1" "special case", sga "6 VI 2.3.1" "more general"]
noncomputable def tensorPullbackModule {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.{u} (pushOfRing f 𝒪) ⥤ SheafOfModules.{u} 𝒪 :=
  SheafOfModules.forget (pushOfRing f 𝒪) ⋙
    PresheafOfModules.pullback (canonicalRingHom f 𝒪).hom ⋙
    PresheafOfModules.sheafification (R₀ := 𝒪.obj) (𝟙 𝒪.obj)

-- isDefEq transparency bump: infer `F` through the pushforward definitions
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction `tensorPullbackModule f 𝒪 ⊣ pushforwardModule f 𝒪`: Mathlib's
`SheafOfModules.PullbackConstruction.adjunction` at `canonicalRingHom`. Its left adjoint is the
abstract one, not the explicit tensor product of Stacks 008Z; Stacks 008Z itself is
`TensorInverseImagePushforward.adjunction`. -/
@[ega "0 4.4.3"]
noncomputable def pullbackPushforwardAdjunction008Z {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    tensorPullbackModule f 𝒪 ⊣ pushforwardModule f 𝒪 :=
  SheafOfModules.PullbackConstruction.adjunction (canonicalRingHom f 𝒪)

/-- Existence form of `pullbackPushforwardAdjunction008Z`: `tensorPullbackModule` admits the
pushforward `f_*` as a right adjoint. -/
@[ega "0 4.4.3" "(4.4.3.1), special case",
  sga "4 Vbis 1.3.6" "adjunction φ* ⊣ φ_*",
  sga "6 VI 2.3.1" "more general"]
theorem pullback_pushforward_adjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Nonempty (tensorPullbackModule f 𝒪 ⊣ pushforwardModule f 𝒪) :=
  ⟨pullbackPushforwardAdjunction008Z f 𝒪⟩

/-- Hom-set form of `pullbackPushforwardAdjunction008Z`: for a sheaf of `𝒪`-modules `ℱ` on `X`
and a sheaf of `f_*𝒪`-modules `𝒢` on `Y`, the bijection
`Mor_{Mod(𝒪)}(tensorPullbackModule 𝒢, ℱ) ≃ Mor_{Mod(f_*𝒪)}(𝒢, f_*ℱ)`, for the abstract left
adjoint `tensorPullbackModule` (Stacks 008Z with its explicit tensor product is
`TensorInverseImagePushforward.homEquiv`).  It is the hom-set bijection of
`pullbackPushforwardAdjunction008Z`, hence bifunctorial in `𝒢` and `ℱ` by
`Adjunction.homEquiv_naturality_left` and `Adjunction.homEquiv_naturality_right`. -/
@[ega "0 4.4.3" "(4.4.3.1), special case"]
noncomputable def morPullbackEquivMorPushforward {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (ℱ : SheafOfModules.{u} 𝒪)
    (𝒢 : SheafOfModules.{u} (pushOfRing f 𝒪)) :
    ((tensorPullbackModule f 𝒪).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (pushforwardModule f 𝒪).obj ℱ) :=
  (pullbackPushforwardAdjunction008Z f 𝒪).homEquiv 𝒢 ℱ

/-- Existence form of `morPullbackEquivMorPushforward`. -/
theorem mor_pullback_equiv_mor_pushforward {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (ℱ : SheafOfModules.{u} 𝒪)
    (𝒢 : SheafOfModules.{u} (pushOfRing f 𝒪)) :
    Nonempty
      (((tensorPullbackModule f 𝒪).obj 𝒢 ⟶ ℱ) ≃
        (𝒢 ⟶ (pushforwardModule f 𝒪).obj ℱ)) :=
  ⟨morPullbackEquivMorPushforward f 𝒪 ℱ 𝒢⟩

