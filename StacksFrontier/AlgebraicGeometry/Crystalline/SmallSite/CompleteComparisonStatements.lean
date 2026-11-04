module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompleteComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BaseDerivedGlobalSections

/-!
# The conclusion of [Stacks, Tag 07MZ]: crystalline cohomology as twisted de Rham cohomology

For the situation `Situation07MZ` of [Stacks, Tag 07MZ], with structure morphism `g : Y ⟶ S`,
this file defines the category of sheaves of modules on `Y` over the inverse image `g^{-1}𝒪_S` of
the structure sheaf of the base, their `A`-linear global sections and the bounded-below right
derived functor of those sections, and coherent `𝒪_Y`-modules with an integrable connection
together with the twisted de Rham complex `ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S}` that connection determines. It
then states the cohomological conclusion of the remark as the proposition `DeRhamComparison07MZ`.

## The statement of [Stacks, Tag 07MZ]

> Let `p` be a prime number.  Let `(A, I, γ)` be a divided power ring with `A` a Noetherian
> `p`-adically complete ring and `p` nilpotent in `A/I`.  Set `S = Spec(A)` and `S₀ = Spec(A/I)`.
> Let `Y` be a proper smooth scheme over `S` and set `X = Y ×_S S₀`.  Let `ℱ` be a finite type
> crystal in quasi-coherent `𝒪_{X/S}`-modules.  Then
>
> 1. there exists a coherent `𝒪_Y`-module `ℱ_Y` endowed with integrable connection
>    `∇ : ℱ_Y ⟶ ℱ_Y ⊗_{𝒪_Y} Ω_{Y/S}` such that `ℱ_Y/p^eℱ_Y` is the module with connection over
>    `A/p^eA` found in Remark [Stacks, Tag 07MW], and
> 2. we have `RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D(A)`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `Situation07MZ.basePullbackSheaf` and `Situation07MZ.basePullbackRingSheaf` — the inverse image
  `g^{-1}𝒪_S` of the structure sheaf of the base along `g : Y ⟶ S`, as a sheaf of commutative
  rings and as a sheaf of rings.
* `Situation07MZ.TwistedModules` — that category of sheaves of modules.
* `Situation07MZ.baseToInverseImageRingHom` — the ring map `A = Γ(S, 𝒪_S) ⟶ Γ(Y, g^{-1}𝒪_S)`
  given by the unit of the inverse-image adjunction.
* `Situation07MZ.baseGlobalSectionsFunctor` — `Γ(Y, -)` on sheaves of `g^{-1}𝒪_S`-modules, valued
  in `A`-modules at the module universe `u + 1`.
* `Situation07MZ.plusObjectOfCochainComplex` — an `ℕ`-indexed cochain complex read as an object of
  the bounded-below derived category.
* `Situation07MZ.derivedBaseGlobalSections` — **`RΓ(Y, K) ∈ D⁺(Mod_A)`** for `K` such a complex.
* `Situation07MZ.CoherentModuleWithConnection` — a coherent `𝒪_Y`-module with an integrable
  connection and the twisted de Rham differential of that connection.  Its `complex` is
  `ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S}`.
* `DeRhamComparison07MZ` — **the cohomological conclusion of [Stacks, Tag 07MZ]**, clause (2)
  together with the existence part of clause (1): for every finite type crystal in
  quasi-coherent `𝒪_{X/S}`-modules there is a coherent `𝒪_Y`-module with integrable connection
  whose twisted de Rham complex computes `RΓ(Cris(X/S), ℱ)` in `D(A)`.

## References

* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace Situation07MZ

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MZ S)

/-! ### The sheaf of rings the twisted complex is a complex over -/

/-- The inverse image `g^{-1}𝒪_S` of the structure sheaf of the base along the structure
morphism `g : Y ⟶ S` of [Stacks, Tag 07MZ], as a sheaf of commutative rings on `Y`. -/
abbrev basePullbackSheaf : TopCat.Sheaf CommRingCat.{u} T.Y.carrier :=
  AlgebraicGeometry.Scheme.Hom.basePullbackSheaf T.toBase

/-- The inverse image `g^{-1}𝒪_S`, as a sheaf of (not necessarily commutative) rings. -/
abbrev basePullbackRingSheaf : TopCat.Sheaf RingCat.{u} T.Y.carrier :=
  AlgebraicGeometry.Scheme.Hom.basePullbackRingSheaf T.toBase

/-- The category of sheaves of `g^{-1}𝒪_S`-modules on `Y`. -/
abbrev TwistedModules : Type (u + 1) := AlgebraicGeometry.Scheme.Hom.TwistedModules T.toBase

/-- Sheafification inverts exactly the locally bijective maps of abelian presheaves on the opens
of `Y`. -/
local instance wEqualsLocallyBijective :
    (Opens.grothendieckTopology ↥T.Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  _root_.SheafOfModules.wEqualsLocallyBijective_opens ↥T.Y.carrier

/-- Sheaves of `g^{-1}𝒪_S`-modules on `Y` have enough injectives. -/
local instance enoughInjectives : EnoughInjectives T.TwistedModules :=
  _root_.SheafOfModules.enoughInjectives_opens ↥T.Y.carrier T.basePullbackRingSheaf

/-! ### `A`-linear global sections on `Y` -/

/-- The top open of `Y` is contained in the preimage of the top open of `S`. -/
theorem top_le_preimage_top : (⊤ : Opens ↥T.Y.carrier) ≤ (Opens.map T.toBase.base).obj ⊤ :=
  AlgebraicGeometry.Scheme.Hom.top_le_preimage_top T.toBase

/-- **The ring map `A = Γ(S, 𝒪_S) ⟶ Γ(Y, g^{-1}𝒪_S)`**: the unit of the inverse-image adjunction
`g^{-1} ⊣ g_*` at the structure sheaf of the base, evaluated at the top open and restricted along
`⊤ ≤ g^{-1}(⊤)`. -/
def baseToInverseImageRingHom :
    ↥Γ(S.S.scheme, ⊤) →+* ↥(T.basePullbackRingSheaf.obj.obj (op (⊤ : Opens ↥T.Y.carrier))) :=
  AlgebraicGeometry.Scheme.Hom.baseToInverseImageRingHom T.toBase

/-- `Γ(Y, -)` on sheaves of `g^{-1}𝒪_S`-modules, valued in `A`-modules at the module universe
`u + 1`. -/
abbrev baseGlobalSectionsFunctor :
    T.TwistedModules ⥤ ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤) :=
  AlgebraicGeometry.Scheme.Hom.baseGlobalSectionsFunctor T.toBase

/-- Evaluation at the top open is an additive functor on sheaves of `g^{-1}𝒪_S`-modules. -/
local instance evaluation_additive :
    (_root_.SheafOfModules.evaluation T.basePullbackRingSheaf (op ⊤)).Additive := by
  change (_root_.SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation T.basePullbackRingSheaf.obj (op ⊤)).Additive
  infer_instance

/-- `A`-linear global sections on `Y` form an additive functor. -/
local instance baseGlobalSectionsFunctor_additive :
    (T.baseGlobalSectionsFunctor).Additive :=
  inferInstance

/-! ### `RΓ(Y, -)` on complexes -/

section Derived

variable [HasDerivedCategory.{w} T.TwistedModules]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤))]

/-- An `ℕ`-indexed cochain complex of sheaves of `g^{-1}𝒪_S`-modules, read as an object of the
bounded-below derived category: it is extended over `ℤ` by zero and quotiented. -/
def plusObjectOfCochainComplex (K : CochainComplex T.TwistedModules ℕ) :
    DerivedCategory.Plus T.TwistedModules :=
  AlgebraicGeometry.Scheme.Hom.plusObjectOfCochainComplex T.toBase K

/-- **`RΓ(Y, K) ∈ D⁺(Mod_A)`** for `K` a complex of sheaves of `g^{-1}𝒪_S`-modules on `Y`
concentrated in non-negative degrees: the bounded-below right derived functor of `A`-linear
global sections, applied to `K`. -/
def derivedBaseGlobalSections (K : CochainComplex T.TwistedModules ℕ) :
    DerivedCategory.Plus (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤)) :=
  AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections T.toBase K

end Derived

/-! ### The output of clause (1) -/

/-- **A coherent `𝒪_Y`-module with integrable connection and its twisted de Rham differential**:
a `AlgebraicGeometry.Scheme.Hom.ModuleWithConnection` at the structure morphism `Y ⟶ S` (a
module with a connection in the sense of [Stacks, Tag 07I0], a twisted de Rham differential, its
square-zero property and integrability) whose module is coherent. -/
structure CoherentModuleWithConnection extends ModuleWithConnection T.toBase where
  /-- `ℱ_Y` is coherent, [Stacks, Tag 01BV]. -/
  isCoherent : _root_.SheafOfModules.IsCoherent module

namespace CoherentModuleWithConnection

variable {T} (M : T.CoherentModuleWithConnection)

/-- **The twisted de Rham complex `ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S}`** of a coherent module with integrable
connection: the complex of
`AlgebraicGeometry.Scheme.Hom.twistedDeRhamComplex`, whose degree-`q` term is
`ℱ_Y ⊗_{𝒪_Y} Ω^q_{Y/S}` and whose differential obeys `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`. -/
def complex : CochainComplex T.TwistedModules ℕ :=
  M.toModuleWithConnection.complex

/-- The degree-`q` term of `ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S}` is `ℱ_Y ⊗_{𝒪_Y} Ω^q_{Y/S}`, read as a sheaf
of `g^{-1}𝒪_S`-modules. -/
theorem complex_X (q : ℕ) :
    M.complex.X q = twistedTerm T.toBase M.module q :=
  M.toModuleWithConnection.complex_X q

end CoherentModuleWithConnection

end Situation07MZ

/-! ### The conclusion of [Stacks, Tag 07MZ] -/

section Comparison

variable (S : GlobalCrystallineSituation.{u}) (T : Situation07MZ S)
  [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w} T.TwistedModules]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤))]

/-- **The cohomological conclusion of [Stacks, Tag 07MZ].**  In the situation of the remark —
`(A, I, γ)` a divided power ring with `A` Noetherian and `p`-adically complete and `p` nilpotent
in `A/I`, `S = Spec(A)`, `S₀ = Spec(A/I)`, `Y` proper and smooth over `S` and `X = Y ×_S S₀`, all
of which is `Situation07MZ` — let `ℱ` be a finite type crystal in quasi-coherent
`𝒪_{X/S}`-modules.  Then there is a coherent `𝒪_Y`-module `ℱ_Y` with integrable connection
`∇ : ℱ_Y ⟶ ℱ_Y ⊗_{𝒪_Y} Ω_{Y/S}` such that

`RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})`

in `D(A)`.

This is clause (2) of the remark together with the existence part of clause (1), without the
condition of clause (1) that `ℱ_Y/p^eℱ_Y` is the module with connection of [Stacks, Tag 07MW]
part (2). The left-hand side is `moduleULiftDerivedGlobalSections`, and the right-hand side is
`Situation07MZ.derivedBaseGlobalSections` of the twisted de Rham complex
`Situation07MZ.CoherentModuleWithConnection.complex`, whose differential obeys the Leibniz rule
`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`. -/
def DeRhamComparison07MZ : Prop :=
  ∀ F : _root_.SheafOfModules.{u} (structureSheaf S), IsFiniteTypeQuasicoherentCrystal F →
    ∃ M : T.CoherentModuleWithConnection,
      Nonempty (moduleULiftDerivedGlobalSections S F ≅ T.derivedBaseGlobalSections M.complex)

end Comparison

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
