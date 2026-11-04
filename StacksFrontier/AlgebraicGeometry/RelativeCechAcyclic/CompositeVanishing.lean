module

public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# Vanishing of the higher direct images of a composite above a degree

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of ringed spaces, or of schemes, and let
`F` be an `𝒪_X`-module which is acyclic for `f_*`, that is `R ᵠ f_* F = 0` for every `q > 0`.
If `R ᵖ g_*(f_* F) = 0` for every `p ≥ d`, then `R ⁿ (g ∘ f)_* F = 0` for every `n ≥ d`.

No hypothesis is placed on `f`, on `g` or on `F` beyond the two vanishing hypotheses, and no
spectral sequence is involved.  The collapse of the derived functor of a composite at an acyclic
object, [Stacks, Tag 089W] in the form `Stacks.AcyclicCollapse.objIso`, gives
`R ⁿ(f_* ⋙ g_*) F ≅ R ⁿ g_*(f_* F)` from the `f_*`-acyclicity of `F` together with the
acyclicity of pushforwards of injectives for a further pushforward; and `f_* ⋙ g_* = (g ∘ f)_*`
on the nose, so the source of that isomorphism is `R ⁿ(g ∘ f)_* F`.

## Main results

In the namespace `Stacks.AlgebraicGeometry.RelativeCechAcyclic`:

* `isZero_rightDerived_modulePushforward_comp_of_isZero` and
  `isZero_rightDerivedPlus_modulePushforward_comp_of_isZero`: the statement for morphisms of
  ringed spaces, in the `ℕ`- and the `ℤ`-indexed spelling of the higher direct images.
* `isZero_rightDerived_pushforward_comp_of_isZero` and
  `isZero_rightDerivedPlus_pushforward_comp_of_isZero`: the same for morphisms of schemes.

## Implementation notes

These are `isZero_rightDerived_pushforward_comp` and `isZero_rightDerivedPlus_pushforward_comp`
of `Stacks.AlgebraicGeometry.RelativeCechAcyclic.Basic` with the two appeals to affineness
replaced by explicit vanishing hypotheses, and with the collapse isomorphism read in the other
direction: there the vanishing is known at the composite and transported to `g_*`, here it is
assumed at `g_*` and transported to the composite.

The `ℤ`-indexed statements take the bound `d` in `ℕ`, so that a degree `i ≥ d` is automatically
nonnegative and `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` reduces them to the
`ℕ`-indexed ones; the hypotheses are the `ℕ`-indexed ones throughout, and
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` converts to them from the `ℤ`-indexed form.

**No `@[stacks ...]` attribute.** This is a step in the proofs of [Stacks, Tag 01XL] and of
[Stacks, Tag 0EHU], not the statement of either, and the consequence of [Stacks, Tag 01F6] it
records is not a labelled clause of that tag.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechAcyclic

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Vanishing of `R ⁿ G` at `X` for `n ≥ d` gives that of the `ℤ`-indexed `R ⁱ G` for `i ≥ d`. -/
private theorem isZero_rightDerivedPlus_obj_of_isZero_rightDerived {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [EnoughInjectives C] (G : C ⥤ D) [G.Additive] (X : C)
    (d : ℕ) (h : ∀ n : ℕ, d ≤ n → IsZero ((G.rightDerived n).obj X)) (i : ℤ) (hi : (d : ℤ) ≤ i) :
    IsZero ((G.rightDerivedPlus i).obj X) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff G rfl X).2 (h n (by omega))

section RingedSpaces

attribute [local instance] Stacks.RelativeLeray.preservesFiniteLimits_modulePushforward

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (F : SheafOfModules.{u} (structureSheafRing X)) (d : ℕ)
  (hF : ∀ q : ℕ, 0 < q → IsZero (((modulePushforward f).rightDerived q).obj F))
  (hg : ∀ p : ℕ, d ≤ p →
    IsZero (((modulePushforward g).rightDerived p).obj ((modulePushforward f).obj F)))

include hF hg in
/-- **`R ⁿ (g ∘ f)_* F = 0` for `n ≥ d`**, for morphisms of ringed spaces `f` and `g`, when `F`
is acyclic for `f_*` and `R ᵖ g_*(f_* F) = 0` for `p ≥ d`, in Mathlib's `ℕ`-indexed spelling. -/
public theorem isZero_rightDerived_modulePushforward_comp_of_isZero (n : ℕ) (hn : d ≤ n) :
    IsZero (((modulePushforward (f ≫ g)).rightDerived n).obj F) :=
  (hg n hn).of_iso
    (Stacks.AcyclicCollapse.objIso (modulePushforward f) (modulePushforward g)
      (fun I hI ↦ @Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective.{u}
        _ _ _ f g I hI) hF n)

include hF hg in
/-- **`R ⁱ (g ∘ f)_* F = 0` for `i ≥ d`**, for morphisms of ringed spaces `f` and `g`, in the
`ℤ`-indexed spelling `Functor.rightDerivedPlus`. -/
public theorem isZero_rightDerivedPlus_modulePushforward_comp_of_isZero (i : ℤ)
    (hi : (d : ℤ) ≤ i) :
    IsZero (((modulePushforward (f ≫ g)).rightDerivedPlus i).obj F) :=
  isZero_rightDerivedPlus_obj_of_isZero_rightDerived _ F d
    (isZero_rightDerived_modulePushforward_comp_of_isZero f g F d hF hg) i hi

end RingedSpaces

section Schemes

/-- Module sheaves on a scheme form an abelian category, in the spelling that unfolds
`AlgebraicGeometry.Scheme.Modules`. -/
noncomputable local instance abelian_schemeModules (W : Scheme.{u}) :
    Abelian (SheafOfModules.{u} W.ringCatSheaf) :=
  inferInstance

/-- Module sheaves on a scheme have enough injectives: they form a Grothendieck abelian
category. -/
local instance enoughInjectives_schemeModules (W : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} W.ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules) (d : ℕ)
  (hF : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F))
  (hg : ∀ p : ℕ, d ≤ p → IsZero (((Scheme.Modules.pushforward g).rightDerived p).obj
    ((Scheme.Modules.pushforward f).obj F)))

include hF hg in
/-- **`R ⁿ (g ∘ f)_* F = 0` for `n ≥ d`**, for morphisms of schemes `f` and `g`, when `F` is
acyclic for `f_*` and `R ᵖ g_*(f_* F) = 0` for `p ≥ d`, in Mathlib's `ℕ`-indexed spelling. -/
public theorem isZero_rightDerived_pushforward_comp_of_isZero (n : ℕ) (hn : d ≤ n) :
    IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).obj F) :=
  (hg n hn).of_iso
    (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g)
      (fun I hI ↦ rightAcyclic_pushforward_obj_injective f g I hI) hF n)

include hF hg in
/-- **`R ⁱ (g ∘ f)_* F = 0` for `i ≥ d`**, for morphisms of schemes `f` and `g`, in the
`ℤ`-indexed spelling `Functor.rightDerivedPlus`. -/
public theorem isZero_rightDerivedPlus_pushforward_comp_of_isZero (i : ℤ) (hi : (d : ℤ) ≤ i) :
    IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerivedPlus i).obj F) :=
  isZero_rightDerivedPlus_obj_of_isZero_rightDerived _ F d
    (isZero_rightDerived_pushforward_comp_of_isZero f g F d hF hg) i hi

end Schemes

end Stacks.AlgebraicGeometry.RelativeCechAcyclic

end
