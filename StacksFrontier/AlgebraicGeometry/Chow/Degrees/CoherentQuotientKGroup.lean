module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# The K-group of the coherent modules modulo a dimension bound

Let `(S, δ)` be a base situation with a dimension function and let `X` be a scheme locally of
finite type over `S`. By Stacks 02S8 the coherent `𝒪_X`-modules whose support has
delta-dimension at most `a` form a Serre subcategory `Coh_{≤a}(X)` of the category `Coh(X)` of
all coherent `𝒪_X`-modules, so the Serre quotient `Coh(X)/Coh_{≤a}(X)` and its Grothendieck
group `K₀(Coh(X)/Coh_{≤a}(X))` are available. Dropping an upper dimension bound `b` is an exact
functor from the dimension layer `Coh_{≤b}(X)/Coh_{≤a}(X)` to `Coh(X)/Coh_{≤a}(X)`, hence
induces the canonical homomorphism

`K₀(Coh_{≤b}(X)/Coh_{≤a}(X)) ⟶ K₀(Coh(X)/Coh_{≤a}(X))`.

Composing that homomorphism for `a = k - 1`, `b = k + 1` with the cycle class map
`CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of Stacks 0FDS yields the canonical map
`CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))`.

## Main definitions

* `Stacks.Chow.coherentQuotient` — the Serre quotient `Coh(X)/Coh_{≤a}(X)`.
* `Stacks.Chow.coherentQuotientKZero` and `Stacks.Chow.coherentQuotientKZeroMk` — its
  Grothendieck group and the class of a coherent module in it.
* `Stacks.Chow.coherentDimensionToQuotientFunctor` — the functor from the layer
  `Coh_{≤b}(X)/Coh_{≤a}(X)` to `Coh(X)/Coh_{≤a}(X)` given by dropping the upper bound.
* `Stacks.Chow.coherentDimensionToQuotientHom` — the induced homomorphism
  `K₀(Coh_{≤b}(X)/Coh_{≤a}(X)) ⟶ K₀(Coh(X)/Coh_{≤a}(X))`.
* `Stacks.Chow.chowToCoherentQuotientKZero` — the composite
  `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` of a cycle class map with that homomorphism.

## Main results

* `Stacks.Chow.coherentDimensionToQuotientHom_apply_mk` — the induced homomorphism sends the
  class of a coherent module of support dimension at most `b` to the class of the same module in
  `K₀(Coh(X)/Coh_{≤a}(X))`.

## References

* [Stacks Project, Tag 02SD](https://stacks.math.columbia.edu/tag/02SD)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### All coherent modules modulo a dimension bound -/

/-- The Serre quotient `Coh(X)/Coh_{≤a}(X)` of all coherent `𝒪_X`-modules by those whose support
has delta-dimension at most `a`. -/
abbrev coherentQuotient (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (a : ℤ) :=
  (coherentModulesDimLE C f a).isoModSerre.Localization

/-- A Serre quotient of an abelian category is abelian. -/
instance coherentQuotientAbelian (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a : ℤ) : Abelian (coherentQuotient C f a) :=
  ObjectProperty.SerreClassLocalization.abelian
    (coherentModulesDimLE C f a).isoModSerre.Q (coherentModulesDimLE C f a)

/-- The localization functor onto a Serre quotient is left exact. -/
instance preservesFiniteLimits_coherentQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a : ℤ) :
    PreservesFiniteLimits (coherentModulesDimLE C f a).isoModSerre.Q :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _ (coherentModulesDimLE C f a)

/-- The localization functor onto a Serre quotient is right exact. -/
instance preservesFiniteColimits_coherentQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a : ℤ) :
    PreservesFiniteColimits (coherentModulesDimLE C f a).isoModSerre.Q :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _ (coherentModulesDimLE C f a)

/-- The Grothendieck group `K₀(Coh(X)/Coh_{≤a}(X))` of all coherent `𝒪_X`-modules modulo those
whose support has delta-dimension at most `a`. -/
abbrev coherentQuotientKZero (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a : ℤ) : Type _ := KZero (coherentQuotient C f a)

/-- The class of a coherent `𝒪_X`-module in `K₀(Coh(X)/Coh_{≤a}(X))`. -/
def coherentQuotientKZeroMk (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (a : ℤ)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) : coherentQuotientKZero C f a :=
  KZero.mk _ ((coherentModulesDimLE C f a).isoModSerre.Q.obj F)

/-! ### Dropping the upper dimension bound -/

/-- The composite of the inclusion `Coh_{≤b}(X) ⟶ Coh(X)` with the localization onto
`Coh(X)/Coh_{≤a}(X)` inverts the morphisms inverted by the localization onto the layer
`Coh_{≤b}(X)/Coh_{≤a}(X)`. -/
theorem isInvertedBy_ι_comp_coherentQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    (lowerDimensionClass C f a b).isoModSerre.IsInvertedBy
      ((coherentModulesDimLE C f b).ι ⋙ (coherentModulesDimLE C f a).isoModSerre.Q) :=
  (ObjectProperty.isoModSerre_isInvertedBy_iff _ _).2 fun M hM ↦
    (ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (coherentModulesDimLE C f a).isoModSerre.Q (coherentModulesDimLE C f a) M.obj).2 hM

/-- The functor from the dimension layer `Coh_{≤b}(X)/Coh_{≤a}(X)` to `Coh(X)/Coh_{≤a}(X)` given
by dropping the upper dimension bound. -/
def coherentDimensionToQuotientFunctor (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    coherentDimensionQuotient C f a b ⥤ coherentQuotient C f a :=
  Localization.lift _ (isInvertedBy_ι_comp_coherentQuotientQ C f a b)
    (lowerDimensionClass C f a b).isoModSerre.Q

/-- The functor out of the dimension layer is compatible with the inclusion of the coherent
modules of support dimension at most `b` into all coherent modules. -/
def coherentDimensionToQuotientFunctorFac (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    (lowerDimensionClass C f a b).isoModSerre.Q ⋙ coherentDimensionToQuotientFunctor C f a b ≅
      (coherentModulesDimLE C f b).ι ⋙ (coherentModulesDimLE C f a).isoModSerre.Q :=
  Localization.fac _ (isInvertedBy_ι_comp_coherentQuotientQ C f a b) _

/-- The functor that drops the upper dimension bound is left exact. -/
instance preservesFiniteLimits_coherentDimensionToQuotientFunctor (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (a b : ℤ) :
    PreservesFiniteLimits (coherentDimensionToQuotientFunctor C f a b) :=
  have : PreservesFiniteLimits ((lowerDimensionClass C f a b).isoModSerre.Q ⋙
      coherentDimensionToQuotientFunctor C f a b) :=
    preservesFiniteLimits_of_natIso (coherentDimensionToQuotientFunctorFac C f a b).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff _
    (lowerDimensionClass C f a b) _).mp this

/-- The functor that drops the upper dimension bound is right exact. -/
instance preservesFiniteColimits_coherentDimensionToQuotientFunctor (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (a b : ℤ) :
    PreservesFiniteColimits (coherentDimensionToQuotientFunctor C f a b) :=
  have : PreservesFiniteColimits ((lowerDimensionClass C f a b).isoModSerre.Q ⋙
      coherentDimensionToQuotientFunctor C f a b) :=
    preservesFiniteColimits_of_natIso (coherentDimensionToQuotientFunctorFac C f a b).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff _
    (lowerDimensionClass C f a b) _).mp this

/-- The functor that drops the upper dimension bound is additive. -/
instance additive_coherentDimensionToQuotientFunctor (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    (coherentDimensionToQuotientFunctor C f a b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The canonical map out of the Chow group -/

/-- The canonical map `K₀(Coh_{≤b}(X)/Coh_{≤a}(X)) → K₀(Coh(X)/Coh_{≤a}(X))`: the homomorphism of
Grothendieck groups induced by the exact functor that drops the upper dimension bound. -/
@[stacks 02SD "the canonical map `K₀(Coh_{≤b}/Coh_{≤a}) → K₀(Coh/Coh_{≤a})`"]
def coherentDimensionToQuotientHom (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    coherentDimensionKZero C f a b →+ coherentQuotientKZero C f a :=
  KZero.lift (fun A ↦ KZero.mk _ ((coherentDimensionToQuotientFunctor C f a b).obj A))
    fun _ hS ↦ KZero.mk_of_shortExact _
      (hS.map_of_exact (coherentDimensionToQuotientFunctor C f a b))

/-- The canonical map `K₀(Coh_{≤b}(X)/Coh_{≤a}(X)) → K₀(Coh(X)/Coh_{≤a}(X))` sends the class of a
coherent module of support dimension at most `b` to the class of the same module. -/
@[simp]
theorem coherentDimensionToQuotientHom_apply_mk (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) (F : CoherentModulesDimLE C f b) :
    coherentDimensionToQuotientHom C f a b (coherentDimensionKZeroMk C f a b F) =
      coherentQuotientKZeroMk C f a F.obj :=
  (KZero.lift_mk _ _ _).trans
    (KZero.mk_eq_of_iso ((coherentDimensionToQuotientFunctorFac C f a b).app F))

/-- The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))`: the composite of a cycle class map
`φ : CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` with the canonical map that drops the upper
dimension bound. -/
@[stacks 02SD "the canonical map `CH_k(X) → K₀(Coh/Coh_{≤k-1})`"]
def chowToCoherentQuotientKZero (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) (φ : chowGroup C f k →+ coherentDimensionKZero C f (k - 1) (k + 1)) :
    chowGroup C f k →+ coherentQuotientKZero C f (k - 1) :=
  (coherentDimensionToQuotientHom C f (k - 1) (k + 1)).comp φ

/-- The canonical map `CH_k(X) → K₀(Coh(X)/Coh_{≤k-1}(X))` sends `α` to the image of `φ α` under
`coherentDimensionToQuotientHom`. -/
@[simp]
theorem chowToCoherentQuotientKZero_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ)
    (φ : chowGroup C f k →+ coherentDimensionKZero C f (k - 1) (k + 1))
    (α : chowGroup C f k) :
    chowToCoherentQuotientKZero C f k φ α =
      coherentDimensionToQuotientHom C f (k - 1) (k + 1) (φ α) :=
  rfl

end Stacks.Chow
