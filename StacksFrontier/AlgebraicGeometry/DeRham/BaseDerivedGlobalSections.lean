module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafTwistedDifferential

/-!
# `RΓ(Y, -)` over the base ring, for complexes of `f^{-1}𝒪_S`-modules

Let `f : Y ⟶ S` be a morphism of schemes and let `A = Γ(S, 𝒪_S)`.  The twisted de Rham complex
`ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` of `StacksFrontier.AlgebraicGeometry.DeRham.ModuleConnection` is a complex of
sheaves of `f^{-1}𝒪_S`-modules on `Y`, its differential being only `f^{-1}𝒪_S`-linear.  Taking
global sections of such a sheaf and restricting scalars along the unit
`A ⟶ Γ(Y, f^{-1}𝒪_S)` of the inverse-image adjunction gives an additive functor to `A`-modules,
and this file records its bounded-below right derived functor

`RΓ(Y, -) : D⁺(Mod_{f^{-1}𝒪_S}) ⟶ D⁺(Mod_A)`,

together with the bundle `ℱ` with integrable connection whose twisted complex it is applied to.

## Main definitions

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `basePullbackSheaf`, `basePullbackRingSheaf` — the inverse image `f^{-1}𝒪_S` as a sheaf of
  commutative rings and as a sheaf of rings.
* `TwistedModules` — sheaves of `f^{-1}𝒪_S`-modules on `Y`, the category the twisted de Rham
  complex is a complex in.
* `baseToInverseImageRingHom` — the ring map `A = Γ(S, 𝒪_S) ⟶ Γ(Y, f^{-1}𝒪_S)`.
* `baseGlobalSectionsFunctor` — `Γ(Y, -)` on sheaves of `f^{-1}𝒪_S`-modules, valued in
  `A`-modules.
* `derivedBaseGlobalSections` — **`RΓ(Y, K) ∈ D⁺(Mod_A)`** for `K` a complex of sheaves of
  `f^{-1}𝒪_S`-modules concentrated in non-negative degrees.
* `ModuleWithConnection` — an `𝒪_Y`-module with integrable connection and its twisted de Rham
  differential.
* `ModuleWithConnection.complex` — the twisted de Rham complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` of such a
  bundle.
* `structureModuleWithConnection` — the structure sheaf `𝒪_Y` with its canonical connection
  `∇(b) = 1 ⊗ d b`.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe w w' u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {Y S : Scheme.{u}} (f : Y ⟶ S)

/-! ### The sheaf of rings the twisted complex is a complex over -/

/-- The inverse image `f^{-1}𝒪_S` of the structure sheaf of the base along `f : Y ⟶ S`, as a
sheaf of commutative rings on `Y`. -/
abbrev basePullbackSheaf : TopCat.Sheaf CommRingCat.{u} Y.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf

/-- The inverse image `f^{-1}𝒪_S`, as a sheaf of (not necessarily commutative) rings, which is
the form a category of sheaves of modules is taken over. -/
abbrev basePullbackRingSheaf : TopCat.Sheaf RingCat.{u} Y.carrier :=
  AlgebraicGeometry.SheafOfModules.underlyingRingSheaf.{u, u} (basePullbackSheaf f)

/-- Sheaves of `f^{-1}𝒪_S`-modules on `Y`: the category the twisted de Rham complex
`ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` is a complex in, its differential being only `f^{-1}𝒪_S`-linear. -/
abbrev TwistedModules : Type (u + 1) := _root_.SheafOfModules.{u} (basePullbackRingSheaf f)

/-- Sheafification inverts exactly the locally bijective maps of abelian presheaves on the opens
of `Y`. -/
local instance wEqualsLocallyBijective :
    (Opens.grothendieckTopology ↥Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  _root_.SheafOfModules.wEqualsLocallyBijective_opens ↥Y.carrier

/-- Sheaves of `f^{-1}𝒪_S`-modules on `Y` have enough injectives. -/
local instance enoughInjectives : EnoughInjectives (TwistedModules f) :=
  _root_.SheafOfModules.enoughInjectives_opens ↥Y.carrier (basePullbackRingSheaf f)

/-! ### `A`-linear global sections on `Y` -/

/-- The top open of `Y` is contained in the inverse image of the top open of `S`. -/
theorem top_le_preimage_top :
    (⊤ : Y.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj ⊤ :=
  fun _ _ ↦ trivial

/-- **The ring map `A = Γ(S, 𝒪_S) ⟶ Γ(Y, f^{-1}𝒪_S)`**: the unit of the inverse-image adjunction
`f^{-1} ⊣ f_*` at the structure sheaf of the base, evaluated at the top open and restricted along
`⊤ ≤ f^{-1}(⊤)`. -/
def baseToInverseImageRingHom :
    ↥Γ(S, ⊤) →+* ↥((basePullbackRingSheaf f).obj.obj (op (⊤ : Y.Opens))) :=
  ((basePullbackSheaf f).presheaf.map (homOfLE (top_le_preimage_top f)).op).hom.comp
    (((TopCat.Sheaf.forget CommRingCat.{u} _).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
        S.sheaf)).app (op ⊤)).hom

/-- `Γ(Y, -)` on sheaves of `f^{-1}𝒪_S`-modules, valued in `A`-modules at the module universe
`u + 1`. -/
abbrev baseGlobalSectionsFunctor : TwistedModules f ⥤ ModuleCat.{u + 1} ↥Γ(S, ⊤) :=
  _root_.SheafOfModules.evaluation (basePullbackRingSheaf f) (op ⊤) ⋙
    ModuleCat.restrictScalars (baseToInverseImageRingHom f) ⋙
    ModuleCat.uliftFunctor.{u + 1, u} ↥Γ(S, ⊤)

/-- Global sections of sheaves of `f^{-1}𝒪_S`-modules is an additive functor; on underlying
presheaves of modules it is evaluation at the top open. -/
local instance evaluation_additive :
    (_root_.SheafOfModules.evaluation (basePullbackRingSheaf f) (op ⊤)).Additive := by
  change (_root_.SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation (basePullbackRingSheaf f).obj (op ⊤)).Additive
  infer_instance

/-- `A`-linear global sections on `Y` is an additive functor. -/
local instance baseGlobalSectionsFunctor_additive : (baseGlobalSectionsFunctor f).Additive :=
  inferInstance

/-! ### `RΓ(Y, -)` on complexes -/

section Derived

variable [HasDerivedCategory.{w} (TwistedModules f)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} ↥Γ(S, ⊤))]

/-- An `ℕ`-indexed cochain complex of sheaves of `f^{-1}𝒪_S`-modules, read as an object of the
bounded-below derived category: it is extended over `ℤ` by zero and quotiented. -/
def plusObjectOfCochainComplex (K : CochainComplex (TwistedModules f) ℕ) :
    DerivedCategory.Plus (TwistedModules f) :=
  DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (TwistedModules f)).obj
    ⟨K.extend ComplexShape.embeddingUpNat, ⟨0, inferInstance⟩⟩)

/-- **`RΓ(Y, K) ∈ D⁺(Mod_A)`** for `K` a complex of sheaves of `f^{-1}𝒪_S`-modules on `Y`
concentrated in non-negative degrees: the bounded-below right derived functor of `A`-linear
global sections, applied to `K`. -/
def derivedBaseGlobalSections (K : CochainComplex (TwistedModules f) ℕ) :
    DerivedCategory.Plus (ModuleCat.{u + 1} ↥Γ(S, ⊤)) :=
  (baseGlobalSectionsFunctor f).rightDerivedFunctorPlus.obj (plusObjectOfCochainComplex f K)

end Derived

/-! ### Modules with integrable connection, and their twisted de Rham complexes -/

/-- **An `𝒪_Y`-module with integrable connection and its twisted de Rham differential.**

The connection is `AlgebraicGeometry.Scheme.Hom.ModuleConnection` relative to `f : Y ⟶ S`, which
is [Stacks, Tag 07I0] at the sheaf level, and its integrability is
`AlgebraicGeometry.Scheme.Hom.ModuleConnection.IsIntegrable`.  The twisted de Rham differential,
determined by the Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, is part of the data. -/
structure ModuleWithConnection where
  /-- The `𝒪_Y`-module `ℱ`. -/
  module : Y.Modules
  /-- The connection `∇ : ℱ ⟶ ℱ ⊗_{𝒪_Y} Ω_{Y/S}`. -/
  connection : ModuleConnection f module
  /-- The twisted de Rham differential of `(ℱ, ∇)`, pinned by the Leibniz rule
  `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`. -/
  differential : TwistedDeRhamDifferential connection
  /-- Consecutive twisted differentials compose to zero, so `ℱ ⊗ Ω^•_{Y/S}` is a complex. -/
  isComplex : differential.IsComplex
  /-- `∇` is integrable. -/
  isIntegrable : connection.IsIntegrable differential

namespace ModuleWithConnection

variable {f} (M : ModuleWithConnection f)

/-- **The twisted de Rham complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}`** of a module with integrable
connection: the complex of `AlgebraicGeometry.Scheme.Hom.twistedDeRhamComplex`, whose degree-`q`
term is `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` and whose differential obeys
`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`. -/
def complex : CochainComplex (TwistedModules f) ℕ :=
  twistedDeRhamComplex M.connection M.differential M.isComplex

/-- The degree-`q` term of `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` is `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}`, read as a sheaf of
`f^{-1}𝒪_S`-modules. -/
theorem complex_X (q : ℕ) : M.complex.X q = twistedTerm f M.module q := rfl

/-- The arrow of `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` out of degree `q` is the twisted de Rham differential of
the connection. -/
theorem complex_d (q : ℕ) : M.complex.d q (q + 1) = M.differential.d q :=
  twistedDeRhamComplex_d M.connection M.differential M.isComplex q

end ModuleWithConnection

/-- **The structure sheaf of `Y` with its canonical relative connection, as a module with
integrable connection.**  The connection is
`AlgebraicGeometry.Scheme.Hom.structureModuleConnection`, `∇(b) = 1 ⊗ d b`; its twisted de Rham
differential is `AlgebraicGeometry.Scheme.Hom.structureTwistedDeRhamDifferential`; and that
differential squares to zero, which gives both the complex property and integrability. -/
def structureModuleWithConnection : ModuleWithConnection f where
  module := _root_.SheafOfModules.unit Y.ringCatSheaf
  connection := structureModuleConnection f
  differential := structureTwistedDeRhamDifferential f
  isComplex := structureTwistedDeRhamDifferential_isComplex f
  isIntegrable := isIntegrable_structureModuleConnection f

end AlgebraicGeometry.Scheme.Hom

end

end
