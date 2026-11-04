module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Collapse of the relative Leray comparison at a module with no higher direct images

Let `π : Y ⟶ Z` and `g : Z ⟶ S` be morphisms of schemes and let `F` be an `𝒪_Y`-module whose
**positive higher direct images along `π` vanish**. Then for every degree `n`

`Rⁿ (π ≫ g)_* F ≅ Rⁿ g_* (π_* F)`.

This is the degenerate case of the relative Leray spectral sequence ([Stacks, Tag 01F6]) in
which the inner morphism contributes only in degree `0` *at the module in question*, and it is
the form the proof of [Stacks, Tag 02O5] uses it in: *"since `R ᵖ π_* ℒ ^⊗ n = 0` for `p > 0` the
relative Leray spectral sequence degenerates"*.

No spectral sequence is constructed, and no hypothesis whatsoever is placed on `π`, on `g` or on
`S`. Two inputs do all the work.

* `Stacks.RightDerivedComp.objIsoOfAcyclicImage` is the edge isomorphism
  `Rⁿ (T ∘ G)(A) ≅ Rⁿ T (G A)` at a `G`-acyclic object `A`, needing of `G` only that it carry
  injective objects to `T`-acyclic ones.
* `…ClosedImmersionRelativeLeray.rightAcyclic_pushforward_pushforward_obj_of_injective` supplies
  exactly that for the two pushforwards, **with no hypothesis on either morphism**: `π_* I` is
  flasque for injective `I` ([Stacks, Tag 01EX] part (2)) and a flasque module has vanishing
  positive higher direct images along any morphism ([Stacks, Tag 09T0]).

Compare `Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso`,
which is the same collapse for a **closed immersion** `π`: there `π_*` is exact, so the splitting
is an isomorphism of functors and holds at every module. Here the inner morphism is arbitrary and
the price is that the collapse holds only at a module for which the vanishing is given.

## Main results

* `…ProperCoherenceWitnessLeray.rightDerivedPushforwardCompObjIso`: the isomorphism
  `Rⁿ (π ≫ g)_* F ≅ Rⁿ g_* (π_* F)`. **Unconditional** beyond the vanishing of the positive
  `R ᵖ π_* F`.
* `…ProperCoherenceWitnessLeray.isCoherent_rightDerived_pushforward_pushforward_of_isZero`
  and `forall_isCoherent_rightDerived_pushforward_pushforward_of_isZero`: coherence transported
  across it, in the shape the dévissage of [Stacks, Tag 01YI] consumes.
* `…ProperCoherenceWitnessLeray.forall_isCoherentPlus_rightDerived_pushforward_of_isZero`: the
  same conclusion stated with the `ℤ`-indexed `Functor.rightDerivedPlus`, which is the indexing
  `AlgebraicGeometry.ProperCoherenceWitness.HasGenericCoherentWitness` is written in.

## Implementation notes

**No `@[stacks 01F6]` and no `@[stacks 02O5]` attribute is attached to anything here.**
[Stacks, Tag 01F6] asserts a spectral sequence with `E₂^{p,q} = R ᵖ g_* (R ᵑ π_* F)` for an
arbitrary pair of morphisms; nothing below produces a spectral sequence or says anything when the
inner higher direct images fail to vanish. [Stacks, Tag 02O5] has `IsProper` in it and no
statement here does.

The vanishing hypothesis is taken in Mathlib's `ℕ`-indexing, `Functor.rightDerived`, because that
is the indexing `Stacks.RightDerivedComp.objIsoOfAcyclicImage` is stated in; the two indexings
are compared by `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` and
`Stacks.DerivedIndexing.rightDerivedIso`, and both comparisons are used below so that a consumer
holding either form can apply the results.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperCoherenceWitnessLeray

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The collapse isomorphism -/

/-- **`Rⁿ (π ≫ g)_* F ≅ Rⁿ g_* (π_* F)` when the positive higher direct images of `F` along `π`
vanish.** No hypothesis on `π`, on `g` or on the schemes.

`π_*` carries injective modules to modules right acyclic for `g_*` — this is
`…ClosedImmersionRelativeLeray.rightAcyclic_pushforward_pushforward_obj_of_injective`, which
assumes nothing about the morphisms — so `Stacks.RightDerivedComp.objIsoOfAcyclicImage` splits
`Rⁿ (g_* ∘ π_*)` at the `π_*`-acyclic module `F`; Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` identifies that composite with `(π ≫ g)_*`. -/
noncomputable def rightDerivedPushforwardCompObjIso {Y Z S : Scheme.{u}} (π : Y ⟶ Z) (g : Z ⟶ S)
    (F : Y.Modules)
    (hF : ∀ n : ℕ, 0 < n → IsZero (((Scheme.Modules.pushforward π).rightDerived n).obj F))
    (n : ℕ) :
    ((Scheme.Modules.pushforward (π ≫ g)).rightDerived n).obj F ≅
      ((Scheme.Modules.pushforward g).rightDerived n).obj
        ((Scheme.Modules.pushforward π).obj F) :=
  ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
        (Scheme.Modules.pushforwardComp π g) n).symm.app F) ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage (Scheme.Modules.pushforward π)
      (Scheme.Modules.pushforward g) hF
      (fun I hI => (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic
          (Scheme.Modules.pushforward g) _).1
        (ClosedImmersionRelativeLeray.rightAcyclic_pushforward_pushforward_obj_of_injective
          π g I hI)) n

/-! ### Coherence across the collapse -/

/-- Coherence of a module transports backwards along an isomorphism. -/
private theorem isCoherent_of_iso_of_isCoherent {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N)
    (h : N.IsCoherent) : M.IsCoherent :=
  have := h
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf) e

/-- **Coherence transports across the collapse.** If the positive higher direct images of `F`
along `π` vanish and `Rⁿ (π ≫ g)_* F` is coherent, then so is `Rⁿ g_* (π_* F)`. -/
theorem isCoherent_rightDerived_pushforward_pushforward_of_isZero {Y Z S : Scheme.{u}}
    (π : Y ⟶ Z) (g : Z ⟶ S) (F : Y.Modules)
    (hF : ∀ n : ℕ, 0 < n → IsZero (((Scheme.Modules.pushforward π).rightDerived n).obj F))
    (n : ℕ)
    (hn : (((Scheme.Modules.pushforward (π ≫ g)).rightDerived n).obj F).IsCoherent) :
    (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward π).obj F)).IsCoherent :=
  isCoherent_of_iso_of_isCoherent (rightDerivedPushforwardCompObjIso π g F hF n).symm hn

/-- **Every higher direct image of `π_* F` along `g` is coherent** as soon as the positive higher
direct images of `F` along `π` vanish and every higher direct image of `F` along `π ≫ g` is
coherent. This is the conclusion the dévissage of [Stacks, Tag 01YI] consumes, in Mathlib's
`ℕ`-indexing. -/
theorem forall_isCoherent_rightDerived_pushforward_pushforward_of_isZero {Y Z S : Scheme.{u}}
    (π : Y ⟶ Z) (g : Z ⟶ S) (F : Y.Modules)
    (hF : ∀ n : ℕ, 0 < n → IsZero (((Scheme.Modules.pushforward π).rightDerived n).obj F))
    (hcomp : ∀ n : ℕ,
      (((Scheme.Modules.pushforward (π ≫ g)).rightDerived n).obj F).IsCoherent)
    (n : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward π).obj F)).IsCoherent :=
  isCoherent_rightDerived_pushforward_pushforward_of_isZero π g F hF n (hcomp n)

/-! ### The same statements in the `ℤ`-indexing of the derived category -/

/-- **The `ℤ`-indexed form of the vanishing hypothesis implies the `ℕ`-indexed one.** The two
indexings of the higher right derived functors are compared by
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`. -/
theorem isZero_rightDerived_of_isZero_rightDerivedPlus {Y Z : Scheme.{u}} (π : Y ⟶ Z)
    (F : Y.Modules)
    (hF : ∀ n : ℕ, 0 < n →
      IsZero (((Scheme.Modules.pushforward π).rightDerivedPlus (n : ℤ)).obj F))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward π).rightDerived n).obj F) :=
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (Scheme.Modules.pushforward π) n F).2
    (hF n hn)

/-- **Coherence in the `ℤ`-indexing from coherence in the `ℕ`-indexing**, across
`Stacks.DerivedIndexing.rightDerivedIso`. -/
theorem isCoherentPlus_of_isCoherent {Y S : Scheme.{u}} (g : Y ⟶ S) (M : Y.Modules) (n : ℕ)
    (h : (((Scheme.Modules.pushforward g).rightDerived n).obj M).IsCoherent) :
    (((Scheme.Modules.pushforward g).rightDerivedPlus (n : ℤ)).obj M).IsCoherent :=
  isCoherent_of_iso_of_isCoherent
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) n).app M).symm h

/-- **Coherence in the `ℕ`-indexing from coherence in the `ℤ`-indexing.** -/
theorem isCoherent_of_isCoherentPlus {Y S : Scheme.{u}} (g : Y ⟶ S) (M : Y.Modules) (n : ℕ)
    (h : (((Scheme.Modules.pushforward g).rightDerivedPlus (n : ℤ)).obj M).IsCoherent) :
    (((Scheme.Modules.pushforward g).rightDerived n).obj M).IsCoherent :=
  isCoherent_of_iso_of_isCoherent
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) n).app M) h

/-- **Every higher direct image of `π_* F` along `g` is coherent**, stated throughout in the
`ℤ`-indexed `Functor.rightDerivedPlus` of the derived-category convention — the indexing
`AlgebraicGeometry.ProperCoherenceWitness.HasGenericCoherentWitness` is written in.

No hypothesis on `π`, on `g` or on the schemes beyond the two displayed. -/
theorem forall_isCoherentPlus_rightDerived_pushforward_of_isZero {Y Z S : Scheme.{u}}
    (π : Y ⟶ Z) (g : Z ⟶ S) (F : Y.Modules)
    (hF : ∀ n : ℕ, 0 < n →
      IsZero (((Scheme.Modules.pushforward π).rightDerivedPlus (n : ℤ)).obj F))
    (hcomp : ∀ n : ℕ,
      (((Scheme.Modules.pushforward (π ≫ g)).rightDerivedPlus (n : ℤ)).obj F).IsCoherent)
    (n : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerivedPlus (n : ℤ)).obj
      ((Scheme.Modules.pushforward π).obj F)).IsCoherent :=
  isCoherentPlus_of_isCoherent g _ n
    (forall_isCoherent_rightDerived_pushforward_pushforward_of_isZero π g F
      (isZero_rightDerived_of_isZero_rightDerivedPlus π F hF)
      (fun m => isCoherent_of_isCoherentPlus (π ≫ g) F m (hcomp m)) n)

end Stacks.AlgebraicGeometry.ProperCoherenceWitnessLeray

end
