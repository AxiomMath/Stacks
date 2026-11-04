module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# The K-groups of a dimension layer of coherent modules

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project. By
Stacks 02S8 the coherent `𝒪_X`-modules whose support has delta-dimension at most `b` form a
Serre subcategory `Coh_{≤b}(𝒪_X)` of coherent modules, and for `a ≤ b` those of dimension at
most `a` form a Serre subcategory of that. The Serre quotient
`Coh_{≤b}(𝒪_X)/Coh_{≤a}(𝒪_X)` is the *layer* `(a, b]`, and its Grothendieck group is the group
the Stacks project writes `K₀(Coh_{≤b}/Coh_{≤a})`.

The inclusion of the layer `(k-1, k]` into the layer `(k-1, k+1]` is exact, hence induces a
homomorphism on Grothendieck groups, and `Bₖ(X)` is its image.

## Main definitions

* `Stacks.Chow.lowerDimensionClass` — the lower dimension bound read as a Serre class inside the
  category cut out by the upper bound.
* `Stacks.Chow.coherentDimensionQuotient` — the Serre quotient, i.e. the layer.
* `Stacks.Chow.coherentDimensionKZero` and `Stacks.Chow.coherentDimensionKZeroMk` — the
  Grothendieck group of a layer and the class of a module in it.
* `Stacks.Chow.dimensionLayerInclusion` and `Stacks.Chow.coherentDimensionLayerFunctor` — the
  inclusion of the `(k-1, k]` layer into the `(k-1, k+1]` layer, before and after passing to
  Serre quotients.
* `Stacks.Chow.coherentDimensionLayerHom` — the induced homomorphism on Grothendieck groups.
* `Stacks.Chow.coherentDimensionLayerImage` — the subgroup `Bₖ(X)`.

## Main results

* `Stacks.Chow.coherentDimensionLayerHom_apply_mk` — the induced homomorphism sends the class of
  a module to the class of the same module in the wider layer.

## Implementation notes

Every abelian structure in play is declared as an instance here: the one on a dimension-bounded
subcategory of coherent modules, the one on a Serre quotient, and the exactness of the
localization functors. The classes `Stacks.Chow.coherentDimensionKZero` and the homomorphism
between two of them only agree if the abelian structures used to form them are the same term, so
they are produced once by instance resolution rather than chosen afresh in each declaration.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02MV](https://stacks.math.columbia.edu/tag/02MV)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The layer as a Serre quotient -/

/-- Coherent `𝒪_X`-modules whose support has delta-dimension at most `a`, read as a property of
the coherent modules whose support has delta-dimension at most `b`. -/
abbrev lowerDimensionClass (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a b : ℤ) : ObjectProperty (CoherentModulesDimLE C f b) :=
  (coherentModulesDimLE C f a).inverseImage (coherentModulesDimLE C f b).ι

/-- The lower dimension bound is a Serre class inside the category cut out by the upper bound: it
is the inverse image of a Serre class along the exact inclusion of Stacks 02S8. -/
instance lowerDimensionClass_isSerreClass (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) : (lowerDimensionClass C f a b).IsSerreClass :=
  inferInstance

/-- The dimension layer `(a, b]`: the Serre quotient of the coherent `𝒪_X`-modules of support
dimension at most `b` by those of support dimension at most `a`. -/
abbrev coherentDimensionQuotient (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a b : ℤ) := (lowerDimensionClass C f a b).isoModSerre.Localization

/-- A Serre quotient of an abelian category is abelian. -/
instance coherentDimensionQuotientAbelian (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) : Abelian (coherentDimensionQuotient C f a b) :=
  ObjectProperty.SerreClassLocalization.abelian
    (lowerDimensionClass C f a b).isoModSerre.Q (lowerDimensionClass C f a b)

/-- The localization functor onto a Serre quotient is left exact. -/
instance preservesFiniteLimits_coherentDimensionQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    PreservesFiniteLimits (lowerDimensionClass C f a b).isoModSerre.Q :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _ (lowerDimensionClass C f a b)

/-- The localization functor onto a Serre quotient is right exact. -/
instance preservesFiniteColimits_coherentDimensionQuotientQ (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (a b : ℤ) :
    PreservesFiniteColimits (lowerDimensionClass C f a b).isoModSerre.Q :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _ (lowerDimensionClass C f a b)

/-! ### The Grothendieck group of a layer -/

/-- The Grothendieck group of the dimension layer `(a, b]` of coherent `𝒪_X`-modules. -/
abbrev coherentDimensionKZero (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a b : ℤ) : Type _ := KZero (coherentDimensionQuotient C f a b)

/-- The class in the Grothendieck group of the layer `(a, b]` of a coherent `𝒪_X`-module whose
support has delta-dimension at most `b`. -/
def coherentDimensionKZeroMk (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (a b : ℤ) (F : CoherentModulesDimLE C f b) : coherentDimensionKZero C f a b :=
  KZero.mk _ ((lowerDimensionClass C f a b).isoModSerre.Q.obj F)

/-! ### The map induced by widening the layer -/

/-- The inclusion of the coherent `𝒪_X`-modules of support dimension at most `k` into those of
support dimension at most `k + 1`. -/
def dimensionLayerInclusion (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) : CoherentModulesDimLE C f k ⥤ CoherentModulesDimLE C f (k + 1) :=
  ObjectProperty.ιOfLE (coherentModulesDimLE_le_coherentModulesDimLE C f (by omega))

/-- Composing the inclusion of dimension layers with the inclusion of the wider layer into all
coherent modules is the inclusion of the narrower layer. -/
def dimensionLayerInclusionCompι (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) :
    dimensionLayerInclusion C f k ⋙ (coherentModulesDimLE C f (k + 1)).ι ≅
      (coherentModulesDimLE C f k).ι :=
  ObjectProperty.ιOfLECompιIso _

/-- The inclusion of dimension layers preserves finite limits, since composing it with the
fully faithful inclusion into all coherent modules gives the inclusion of the narrower layer. -/
instance preservesFiniteLimits_dimensionLayerInclusion (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteLimits (dimensionLayerInclusion C f k) :=
  have : PreservesFiniteLimits
      (dimensionLayerInclusion C f k ⋙ (coherentModulesDimLE C f (k + 1)).ι) :=
    preservesFiniteLimits_of_natIso (dimensionLayerInclusionCompι C f k).symm
  preservesFiniteLimits_of_reflects_of_preserves _ (coherentModulesDimLE C f (k + 1)).ι

/-- The inclusion of dimension layers preserves finite colimits, since composing it with the
fully faithful inclusion into all coherent modules gives the inclusion of the narrower layer. -/
instance preservesFiniteColimits_dimensionLayerInclusion (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteColimits (dimensionLayerInclusion C f k) :=
  have : PreservesFiniteColimits
      (dimensionLayerInclusion C f k ⋙ (coherentModulesDimLE C f (k + 1)).ι) :=
    preservesFiniteColimits_of_natIso (dimensionLayerInclusionCompι C f k).symm
  preservesFiniteColimits_of_reflects_of_preserves _ (coherentModulesDimLE C f (k + 1)).ι

/-- Widening the upper dimension bound kills no more objects than the Serre class of the wider
layer does, so the composite of the inclusion with the localization onto the wider layer inverts
the morphisms inverted by the localization onto the narrower one. -/
theorem isInvertedBy_dimensionLayerInclusion_comp_q (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    (lowerDimensionClass C f (k - 1) k).isoModSerre.IsInvertedBy
      (dimensionLayerInclusion C f k ⋙ (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre.Q) :=
  (ObjectProperty.isoModSerre_isInvertedBy_iff _ _).2 (by
    intro M hM
    have hkill := ObjectProperty.le_kernel_of_isoModSerre_isInvertedBy
      (lowerDimensionClass C f (k - 1) (k + 1))
      (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre.Q
      (Localization.inverts _ (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre)
    exact hkill ((dimensionLayerInclusion C f k).obj M) hM)

/-- The functor between dimension layers induced by widening the upper bound from `k` to
`k + 1`. -/
def coherentDimensionLayerFunctor (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) :
    coherentDimensionQuotient C f (k - 1) k ⥤ coherentDimensionQuotient C f (k - 1) (k + 1) :=
  Localization.lift _ (isInvertedBy_dimensionLayerInclusion_comp_q C f k)
    (lowerDimensionClass C f (k - 1) k).isoModSerre.Q

/-- The functor between dimension layers is compatible with the inclusion of the underlying
categories of coherent modules. -/
def coherentDimensionLayerFunctorFac (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    (lowerDimensionClass C f (k - 1) k).isoModSerre.Q ⋙ coherentDimensionLayerFunctor C f k ≅
      dimensionLayerInclusion C f k ⋙
        (lowerDimensionClass C f (k - 1) (k + 1)).isoModSerre.Q :=
  Localization.fac _ (isInvertedBy_dimensionLayerInclusion_comp_q C f k) _

/-- The functor between dimension layers preserves finite limits. -/
instance preservesFiniteLimits_coherentDimensionLayerFunctor (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteLimits (coherentDimensionLayerFunctor C f k) :=
  have : PreservesFiniteLimits ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q ⋙
      coherentDimensionLayerFunctor C f k) :=
    preservesFiniteLimits_of_natIso (coherentDimensionLayerFunctorFac C f k).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff _
    (lowerDimensionClass C f (k - 1) k) _).mp this

/-- The functor between dimension layers preserves finite colimits. -/
instance preservesFiniteColimits_coherentDimensionLayerFunctor (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteColimits (coherentDimensionLayerFunctor C f k) :=
  have : PreservesFiniteColimits ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q ⋙
      coherentDimensionLayerFunctor C f k) :=
    preservesFiniteColimits_of_natIso (coherentDimensionLayerFunctorFac C f k).symm
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff _
    (lowerDimensionClass C f (k - 1) k) _).mp this

/-- The functor between dimension layers is additive. -/
instance additive_coherentDimensionLayerFunctor (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : (coherentDimensionLayerFunctor C f k).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The subgroup `Bₖ(X)` -/

/-- The homomorphism of Grothendieck groups induced by the inclusion of the dimension layer
`(k - 1, k]` into the layer `(k - 1, k + 1]`. -/
def coherentDimensionLayerHom (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) :
    coherentDimensionKZero C f (k - 1) k →+ coherentDimensionKZero C f (k - 1) (k + 1) :=
  KZero.lift (fun A => KZero.mk _ ((coherentDimensionLayerFunctor C f k).obj A))
    fun _ hS => KZero.mk_of_shortExact _ (hS.map_of_exact (coherentDimensionLayerFunctor C f k))

/-- The induced homomorphism sends the class of a coherent module of support dimension at most
`k` to the class of the same module in the layer `(k - 1, k + 1]`. -/
@[simp]
theorem coherentDimensionLayerHom_apply_mk (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (F : CoherentModulesDimLE C f k) :
    coherentDimensionLayerHom C f k (coherentDimensionKZeroMk C f (k - 1) k F) =
      coherentDimensionKZeroMk C f (k - 1) (k + 1)
        ((dimensionLayerInclusion C f k).obj F) :=
  (KZero.lift_mk _ _ _).trans
    (KZero.mk_eq_of_iso ((coherentDimensionLayerFunctorFac C f k).app F))

/-- **Stacks 02SC, `Bₖ(X)`.** The image of the homomorphism of Grothendieck groups induced by the
inclusion of the dimension layer `(k - 1, k]` into the layer `(k - 1, k + 1]`. -/
@[stacks 02SC "b_k_x"]
def coherentDimensionLayerImage (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (k : ℤ) : AddSubgroup (coherentDimensionKZero C f (k - 1) (k + 1)) :=
  (coherentDimensionLayerHom C f k).range

end Stacks.Chow
