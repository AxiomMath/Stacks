module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleAlgebra

/-!
# Coherence and reflexivity of a direct image from an open subscheme

Let `j : Y ⟶ X` be an open immersion of schemes with `X` locally Noetherian, whose complement
consists of points at which `𝒪_X` has depth at least two, and let `M` be an `𝒪_Y`-module. This
file reduces coherence and reflexivity of `j_* M` to two conditions on the *restriction*
`(j_* M)|_W` to the open `W = j(Y)`, namely that it is reflexive and that it extends to a
coherent `𝒪_X`-module.

The point of the reduction is that `Stacks.FundamentalGroup.DepthCoherence` proves exactly that
statement for an open *subscheme* inclusion `W.ι`, and the direct image appearing in
[Stacks, Tag 0EY6] is taken along an arbitrary open immersion `j`. The comparison is
`isoPushforwardRestrictOpensRange`: a direct image along `j` is the direct image along `W.ι` of
its own restriction to `W`, because `j` factors as an isomorphism onto `W` followed by `W.ι`
and the direct image along `W.ι` is split by restriction.

Applied to the direct image of the structure sheaf of a finite étale cover, this gives the two
assertions of [Stacks, Tag 0EY6] about the extension algebra `𝓑 = j_* π_* 𝒪_V` — coherence and
reflexivity — from the two inputs isolated here.

## Main results

* `isoPushforwardRestrictOpensRange` — a direct image along an open immersion `j` is the direct
  image along the inclusion of `j.opensRange` of its own restriction there.
* `isCoherent_and_isReflexive_pushforward_of_extension` — `j_* M` is coherent and reflexive once
  `(j_* M)|_{j(Y)}` is reflexive and extends to a coherent module on `X`.
* `isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_extension` — the same for
  the extension algebra of a finite étale cover, which is the pair of assertions
  [Stacks, Tag 0EY6] makes about it.

## Implementation notes

No `@[stacks 0EY6 "algebra"]` attribute is placed on the conditional statements in this file; the
unconditional forms of the `algebra` clause live in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Algebra` and carry
`add_to_stacks 0EY6 "algebra"` there. The bare tag `0EY6` is registered as six
clauses (`algebra`, `flat_base_change`, `unique_extension`, `larger_open`,
`etale_iff_flat`, `etale_iff_free`), so coverage is recorded clause by clause.

The two hypotheses are exactly the two results this branch does not carry. Reflexivity of
`(j_* M)|_{j(Y)}`, for `M = π_* 𝒪_V` with `π` finite étale, is reflexivity of a finite locally
free sheaf of modules, for which no declaration exists here; the obstruction is recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean`. The
coherent extension is [Stacks, Tag 0G41] part (2).

The coherence predicate is written `_root_.SheafOfModules.IsCoherent` throughout. That is not
cosmetic: this branch carries two distinct coherence constants with identical fields, and inside
the `Stacks.` namespace both the unqualified name and dot notation resolve to the other one, with
no error anywhere. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/PushforwardCoherent.lean`.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtale

/-! ### A direct image along an open immersion comes from its range -/

/-- **A direct image along an open immersion is a direct image from its range.** For an open
immersion `j : Y ⟶ X` with range `W`, the module `j_* M` is the direct image along `W.ι` of its
own restriction `(j_* M)|_W`.

Indeed `j` factors as `j.isoOpensRange.hom ≫ W.ι`, so `j_* M = (W.ι)_* A` with
`A = (j.isoOpensRange.hom)_* M`; and `A` is recovered from `(W.ι)_* A` by restriction, because
the counit of the restriction–direct-image adjunction along an open immersion is an
isomorphism. -/
public def isoPushforwardRestrictOpensRange {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : Y.Modules) :
    (Scheme.Modules.pushforward j).obj M ≅
      (Scheme.Modules.pushforward j.opensRange.ι).obj
        (((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι) :=
  let e : (Scheme.Modules.pushforward j.opensRange.ι).obj
      ((Scheme.Modules.pushforward j.isoOpensRange.hom).obj M) ≅
        (Scheme.Modules.pushforward j).obj M :=
    (Scheme.Modules.pushforwardComp j.isoOpensRange.hom j.opensRange.ι).app M ≪≫
      (Scheme.Modules.pushforwardCongr j.isoOpensRange_hom_ι).app M
  e.symm ≪≫ (Scheme.Modules.pushforward j.opensRange.ι).mapIso
    (((Scheme.Modules.restrictFunctorAdjCounitIso j.opensRange.ι).app
      ((Scheme.Modules.pushforward j.isoOpensRange.hom).obj M)).symm ≪≫
        (Scheme.Modules.restrictFunctor j.opensRange.ι).mapIso e)

/-- **The restriction of `j_* M` to the range of `j` is the transport of `M` along the
isomorphism onto that range.** This is the component of `isoPushforwardRestrictOpensRange` that
lets a hypothesis about `(j_* M)|_{j(Y)}` be read as a hypothesis about `M`. -/
public def isoRestrictOpensRangePushforward {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : Y.Modules) :
    ((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι ≅
      (Scheme.Modules.pushforward j.isoOpensRange.hom).obj M :=
  (Scheme.Modules.restrictFunctor j.opensRange.ι).mapIso
      ((Scheme.Modules.pushforwardComp j.isoOpensRange.hom j.opensRange.ι).app M ≪≫
        (Scheme.Modules.pushforwardCongr j.isoOpensRange_hom_ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j.opensRange.ι).app
      ((Scheme.Modules.pushforward j.isoOpensRange.hom).obj M)

/-! ### Reflexivity is invariant under an isomorphism of schemes -/

/-- **Reflexivity transports along an isomorphism of schemes.** If `f : Y ⟶ Z` is an isomorphism
and `M` is a coherent reflexive `𝒪_Y`-module, then `f_* M` is reflexive.

The statement is reduced to the stalks by [Stacks, Tag 0AY3]: every point of `Z` is `f y`, the
stalk of `f_* M` there is the stalk of `(f_* M)|_Y ≅ M` at `y` by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_stalk_of_isReflexive_stalk_restrict`,
and the stalks of `M` are reflexive because `M` is. Working stalkwise is what avoids transporting
`dualSheaf` across the isomorphism, for which this branch has no comparison. -/
public theorem isReflexive_pushforward_of_isIso {Y Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : Y ⟶ Z) [IsIso f] (M : Y.Modules) [M.IsQuasicoherent]
    [_root_.SheafOfModules.IsCoherent M] (hM : IsReflexive M) :
    IsReflexive ((Scheme.Modules.pushforward f).obj M) := by
  have hY : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  have hMfp : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  have hMd : (dualSheaf M).IsFinitePresentation := isFinitePresentation_dualSheaf M
  have hA : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj M) :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite f M
  have hAfp : ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent _
  have hAd : (dualSheaf ((Scheme.Modules.pushforward f).obj M)).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  refine isReflexive_of_forall_isReflexive_stalk _ fun z => ?_
  have hz : f ((inv f) z) = z := by
    rw [← Scheme.Hom.comp_apply]
    simp
  rw [← hz]
  refine isReflexive_stalk_of_isReflexive_stalk_restrict f _ ((inv f) z) ?_
  have hstalk : Module.IsReflexive (Y.presheaf.stalk ((inv f) z))
      (((𝟭 Y.Modules).obj M).presheaf.stalk ((inv f) z)) :=
    isReflexive_stalk_of_isReflexive M hM _
  exact Module.equiv
    (stalkLinearEquivOfIso ((Scheme.Modules.restrictFunctorAdjCounitIso f).app M) ((inv f) z)).symm

/-! ### Coherence and reflexivity of the direct image -/

/-- **Coherence and reflexivity of a direct image across a depth-two complement.** Let
`j : Y ⟶ X` be an open immersion into a locally Noetherian scheme whose complement carries depth
at least two, and let `M` be an `𝒪_Y`-module. If the restriction `(j_* M)|_{j(Y)}` is reflexive
and is the restriction of some coherent `𝒪_X`-module, then `j_* M` is itself coherent and
reflexive.

This is `Stacks.FundamentalGroup.DepthCoherence.isCoherent_isReflexive_pushforward_of_extension`,
whose open subscheme is `j.opensRange`, transported along `isoPushforwardRestrictOpensRange`. -/
public theorem isCoherent_and_isReflexive_pushforward_of_extension {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (j : Y ⟶ X) [IsOpenImmersion j] (M : Y.Modules) (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E]
    (e : E.restrict j.opensRange.ι ≅
      ((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι)
    (hrefl : IsReflexive (((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι))
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward j).obj M) ∧
      IsReflexive ((Scheme.Modules.pushforward j).obj M) := by
  obtain ⟨hc, hr⟩ := DepthCoherence.isCoherent_isReflexive_pushforward_of_extension
    j.opensRange (((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι) E e hrefl hdepth
  have hc' : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward j).obj M) :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (isoPushforwardRestrictOpensRange j M)
  refine ⟨hc', isReflexive_of_iso (isoPushforwardRestrictOpensRange j M).symm hr⟩

/-! ### The extension algebra of a finite étale cover -/

/-- **The two module-level assertions of [Stacks, Tag 0EY6].** Let `j : U ⟶ X` be an open
immersion into a locally Noetherian scheme whose complement carries depth at least two and let
`π : V ⟶ U` be finite étale. Then the `𝒪_X`-module underlying the extension algebra
`𝓑 = (π ≫ j)_* 𝒪_V` is coherent and reflexive, granted that its restriction to `j(U)` is
reflexive and extends to a coherent `𝒪_X`-module.

Étaleness of `π` enters only through the two hypotheses: it is what makes `π_* 𝒪_V` finite
locally free, hence reflexive, and the coherent extension is produced from coherence of
`π_* 𝒪_V` by [Stacks, Tag 0G41] part (2). -/
public theorem isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_extension
    {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π] (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E]
    (e : E.restrict j.opensRange.ι ≅
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict j.opensRange.ι)
    (hrefl : IsReflexive
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict j.opensRange.ι))
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) ∧
      IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
  isCoherent_and_isReflexive_pushforward_of_extension j
    ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit V.ringCatSheaf)) E e hrefl hdepth

/-- **Coherence and reflexivity of a direct image, with reflexivity assumed upstairs.** The
same statement as `isCoherent_and_isReflexive_pushforward_of_extension`, with the reflexivity
hypothesis on `M` itself rather than on the restriction of `j_* M` to `j(Y)`; the two are
identified by `isoRestrictOpensRangePushforward` together with
`isReflexive_pushforward_of_isIso`. -/
public theorem isCoherent_and_isReflexive_pushforward_of_isReflexive {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (j : Y ⟶ X) [IsOpenImmersion j] (M : Y.Modules)
    [M.IsQuasicoherent] [_root_.SheafOfModules.IsCoherent M] (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E]
    (e : E.restrict j.opensRange.ι ≅
      ((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι)
    (hM : IsReflexive M)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward j).obj M) ∧
      IsReflexive ((Scheme.Modules.pushforward j).obj M) := by
  have hW : IsLocallyNoetherian j.opensRange.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion j.opensRange.ι
  have hA : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward j.isoOpensRange.hom).obj M) :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite
      j.isoOpensRange.hom M
  have hR : _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward j).obj M).restrict j.opensRange.ι) :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (isoRestrictOpensRangePushforward j M)
  exact isCoherent_and_isReflexive_pushforward_of_extension j M E e
    (isReflexive_of_iso (isoRestrictOpensRangePushforward j M).symm
      (isReflexive_pushforward_of_isIso j.isoOpensRange.hom M hM)) hdepth

/-- **The two module-level assertions of [Stacks, Tag 0EY6], reduced to their two missing
inputs.** Let `j : U ⟶ X` be an open immersion into a locally Noetherian scheme whose complement
carries depth at least two and let `π : V ⟶ U` be finite étale. Then the `𝒪_X`-module underlying
the extension algebra `𝓑 = (π ≫ j)_* 𝒪_V` is coherent and reflexive, granted

* `hrefl`: the `𝒪_U`-module `π_* 𝒪_V` is reflexive — which holds because `π` is finite étale,
  hence `π_* 𝒪_V` is finite locally free, but needs reflexivity of a finite locally free sheaf of
  modules, a statement no declaration on this branch carries;
* `E` with `e`: a coherent `𝒪_X`-module restricting to `π_* 𝒪_V` on `j(U)`, which is
  [Stacks, Tag 0G41] part (2).

Coherence of `π_* 𝒪_V` itself is not a hypothesis: it is
`Stacks.FundamentalGroup.isCoherent_underlyingModule_pushforwardAlgebra_of_isOpenImmersion`. -/
public theorem isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_isReflexive
    {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π] (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E]
    (e : E.restrict j.opensRange.ι ≅
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict j.opensRange.ι)
    (hrefl : IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)))
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) ∧
      IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) := by
  have hM : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit V.ringCatSheaf)) :=
    isCoherent_underlyingModule_pushforwardAlgebra_of_isOpenImmersion j π
  have hMq : ((Scheme.Modules.pushforward π).obj
      (SheafOfModules.unit V.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  exact isCoherent_and_isReflexive_pushforward_of_isReflexive j
    ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit V.ringCatSheaf)) E e hrefl hdepth

end Stacks.FundamentalGroup.ExtendedEtale

end
