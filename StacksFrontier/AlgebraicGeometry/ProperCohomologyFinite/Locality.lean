module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Locality
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# [Stacks, Tag 02O5] is local on the base, hence is exactly [Stacks, Tag 02O6]

[Stacks, Tag 02O5] says that the higher direct images of a coherent module along a proper
morphism to a locally Noetherian scheme are coherent; [Stacks, Tag 02O6] says that for `A`
Noetherian and `f : X ⟶ Spec A` proper, each `Hⁱ(X, F)` is a finite `A`-module. The source
proves the second from the first in one step and
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/Basic.lean` formalises that step as an
**equivalence over an affine base**.

This file supplies the other half, which is the first sentence of the source's own proof of
[Stacks, Tag 02O5] — *"since the problem is local on `S` we may assume that `S` is a Noetherian
scheme"* — and so turns the relation between the two tags into a theorem: coherence of
`Rⁱ f_* F` for a general base follows from coherence over each affine open of the base, because
`Rⁱ f_* F` is quasi-coherent ([Stacks, Tag 01XJ]) and being of finite type is local, and
restriction to an open of the base commutes with the higher direct image ([Stacks, Tag 01E5]).

The consequence is `forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`:
**[Stacks, Tag 02O5] and [Stacks, Tag 02O6], each quantified over all of its own data, are
equivalent.** Neither is proved here — the content of both is the finiteness theorem, whose proof
in the source is a dévissage ([Stacks, Tag 01YI]) over Chow's lemma ([Stacks, Tag 0200]) — but
after this file they are one obligation rather than two, and the affine case is the whole of it.

## Main results

* `Stacks.AlgebraicGeometry.ProperCohomologyFinite`'s
  `isFiniteType_rightDerivedPlus_of_forall_isAffineOpen`: being of finite type is local on the
  base for a higher direct image along a quasi-compact quasi-separated morphism.
* `…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_forall_isAffineOpen`: the same for
  coherence, over a locally Noetherian base.
* `…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_affineBase`: **[Stacks, Tag 02O5] from
  its own affine case**, universally quantified.
* `…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_moduleFinite_cohomology`: **[Stacks,
  Tag 02O5] from [Stacks, Tag 02O6]**, universally quantified — the first of the tag's two
  statements, conditional on the affine finiteness theorem and on nothing else.
* `…ProperCohomologyFinite.isCoherent_pushforward_of_moduleFinite_cohomology`: the same for the
  ordinary direct image, the tag's second statement.
* `…ProperCohomologyFinite.forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`:
  **[Stacks, Tag 02O5] ⟺ [Stacks, Tag 02O6]**.

## Implementation notes

**No `@[stacks 02O5]` and no `@[stacks 02O6]` attribute is attached to anything here.** Every
statement below carries the affine finiteness theorem as a hypothesis, so none of them asserts
either tag.

The reduction is to the covering of `S` by *all* its affine opens
(`AlgebraicGeometry.iSup_affineOpens_eq_top`), which is the cheapest cover to produce and is all
that `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isFiniteType_of_restrict_cover` needs; that
lemma requires the module to be quasi-coherent, which here is [Stacks, Tag 01XJ] found by
instance search.

The restriction comparison used is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, Tag 01E5 in
the scheme vocabulary for `CategoryTheory.Functor.rightDerivedPlus`. The hypotheses of the
affine-base results are stated for `CategoryTheory.Functor.rightDerived`, matching
`ProperCohomologyFinite/Basic.lean` and [Stacks, Tag 02O6]'s own `Hⁱ`, and the two indexings are
compared by `Stacks.DerivedIndexing.rightDerivedIso`.

`IsLocallyNoetherian X` is not assumed: a proper morphism is locally of finite type, so it
follows from local Noetherianness of `S` by Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, which is the "locally" clause of
[Stacks, Tag 01T6]. It is needed only to restrict the coherent module `F` to `f⁻¹(V)`.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.ProperCohomologyFinite

attribute [local instance] HasDerivedCategory.standard

/-! ### The higher direct images are local on the base -/

/-- **Being of finite type is local on the base for a higher direct image.** If `R ⁱ (f ∣_ V)_*`
of the restriction of `F` is of finite type for every affine open `V` of `S`, then `R ⁱ f_* F` is
of finite type.

The affine opens cover `S`; restriction to an open of the base commutes with the higher direct
image ([Stacks, Tag 01E5]); and a quasi-coherent module of finite type on each member of a
covering is of finite type. Quasi-coherence of `R ⁱ f_* F` is [Stacks, Tag 01XJ], found by
instance search from the quasi-compactness and quasi-separatedness of `f`. -/
theorem isFiniteType_rightDerivedPlus_of_forall_isAffineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ)
    (h : ∀ V : S.affineOpens,
      (((Scheme.Modules.pushforward (f ∣_ (V : S.Opens))).rightDerivedPlus (i : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj F)).IsFiniteType) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsFiniteType := by
  refine FiniteTypeSubmodule.isFiniteType_of_restrict_cover _
    (fun V : S.affineOpens => (V : S.Opens)) (iSup_affineOpens_eq_top S) fun V => ?_
  have := h V
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (rightDerivedPlusRestrictObjIso f (V : S.Opens) i F)

/-- **Coherence of a higher direct image is local on the base.** Over a locally Noetherian base,
coherence of `R ⁱ (f ∣_ V)_*` of the restriction of `F` for every affine open `V` of `S` gives
coherence of `R ⁱ f_* F`.

Coherence is quasi-coherence together with finite type over a locally Noetherian scheme
([Stacks, Tag 01XZ]): the hypothesis is turned into local finite type, which
`isFiniteType_rightDerivedPlus_of_forall_isAffineOpen` globalises, and quasi-coherence is
[Stacks, Tag 01XJ]. -/
theorem isCoherent_rightDerivedPlus_of_forall_isAffineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ)
    (h : ∀ V : S.affineOpens,
      (((Scheme.Modules.pushforward (f ∣_ (V : S.Opens))).rightDerived i).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj F)).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent := by
  have hft := isFiniteType_rightDerivedPlus_of_forall_isAffineOpen f F i (fun V => by
    have := h V
    obtain ⟨-, _⟩ := isQuasicoherent_isFiniteType_of_isCoherent
      (((Scheme.Modules.pushforward (f ∣_ (V : S.Opens))).rightDerived i).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj F))
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (f ∣_ (V : S.Opens))) i).app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj F)))
  exact isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- Coherence of the `ℤ`-indexed `R ⁱ f_* F` gives that of the `ℕ`-indexed `rightDerived`. -/
private theorem isCoherent_rightDerived_of_rightDerivedPlus {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (i : ℕ)
    [(((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent] :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsCoherent :=
  CoherentDevissage.isCoherent_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F)

/-! ### [Stacks, Tag 02O5] from its affine case -/

/-- **[Stacks, Tag 02O5] from its own affine case.** Granted coherence of every higher direct
image along every proper morphism onto an *affine* locally Noetherian scheme, the same holds for
an arbitrary locally Noetherian base.

This is the source's opening reduction. `f ∣_ V` is proper, `V` is affine and locally Noetherian,
and the restriction of the coherent `F` to `f⁻¹(V)` is coherent because `X` is locally Noetherian
— which is [Stacks, Tag 01T6], as Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, a proper morphism being locally of
finite type. -/
theorem isCoherent_rightDerivedPlus_of_affineBase {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ)
    (haff : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, G.IsCoherent → ∀ n : ℕ,
        (((Scheme.Modules.pushforward g).rightDerived n).obj G).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent := by
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isQuasicoherent_of_isCoherent F
  refine isCoherent_rightDerivedPlus_of_forall_isAffineOpen f F i fun V => ?_
  exact haff _ _ (f ∣_ (V : S.Opens)) inferInstance V.2 inferInstance _
    (ReflexiveModules.isCoherent_restrict_of_isOpenImmersion (f ⁻¹ᵁ (V : S.Opens)).ι F
      inferInstance) i

/-- **[Stacks, Tag 02O5] from [Stacks, Tag 02O6].** Granted that `Hⁿ(X₀, G)` is a finite
`Γ(S₀, ⊤)`-module for every proper morphism onto an affine locally Noetherian `S₀` and every
coherent `G`, every higher direct image of a coherent module along a proper morphism to a locally
Noetherian scheme is coherent.

This is the first of the two statements of Tag 02O5, with the affine finiteness theorem as its
only hypothesis: the affine case of [Stacks, Tag 02O5] is [Stacks, Tag 02O6] by
`isCoherent_of_moduleFinite_cohomology`, and `isCoherent_rightDerivedPlus_of_affineBase` globalises
it. -/
theorem isCoherent_rightDerivedPlus_of_moduleFinite_cohomology {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ)
    (h02O6 : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, G.IsCoherent → ∀ n : ℕ,
        Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent :=
  isCoherent_rightDerivedPlus_of_affineBase f F i
    (fun X₀ S₀ g hg hS₀ hS₀N G hG n => by
      have := isQuasicoherent_of_isCoherent G
      exact isCoherent_of_moduleFinite_cohomology g G n (h02O6 X₀ S₀ g hg hS₀ hS₀N G hG n))

/-- **The ordinary direct image clause of [Stacks, Tag 02O5] from [Stacks, Tag 02O6].** This is
the second of the two statements of Tag 02O5; it is the previous theorem in degree `0`,
transported along `Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroObjIso`,
the identification `R ⁰ f_* ≅ f_*`. -/
theorem isCoherent_pushforward_of_moduleFinite_cohomology {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent]
    (h02O6 : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, G.IsCoherent → ∀ n : ℕ,
        Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  have := isCoherent_rightDerivedPlus_of_moduleFinite_cohomology f F 0 h02O6
  have := isCoherent_rightDerived_of_rightDerivedPlus f F 0
  CoherentDevissage.isCoherent_of_iso
    (DerivedPushforward.pushforwardRightDerivedZeroObjIso f F).symm

/-! ### The two tags are one obligation -/

/-- **[Stacks, Tag 02O5] and [Stacks, Tag 02O6] are equivalent.** Coherence of every higher
direct image of every coherent module along every proper morphism to a locally Noetherian scheme
holds if and only if, for every proper morphism onto an affine locally Noetherian scheme and
every coherent module, every `Hⁿ` is a finite module over the global sections of the base.

The forward direction is the source's own proof of [Stacks, Tag 02O6] from [Stacks, Tag 02O5]
(`moduleFinite_cohomology_of_isCoherent`); the backward direction is
`isCoherent_rightDerivedPlus_of_moduleFinite_cohomology`. So the finiteness theorem over an
affine base is not merely sufficient for [Stacks, Tag 02O5] but is exactly as strong, and the
general proper morphism contributes nothing beyond it. -/
theorem forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology :
    (∀ (X S : Scheme.{u}) (f : X ⟶ S), IsProper f → IsLocallyNoetherian S →
        ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
          (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent) ↔
      (∀ (X S : Scheme.{u}) (f : X ⟶ S), IsProper f → IsAffine S → IsLocallyNoetherian S →
        ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
          Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
            (((moduleGlobalSections X).rightDerived i).obj F))) := by
  refine ⟨fun h X S f hf _ hSN F hF i => ?_,
    fun h X S f _ _ F _ i => isCoherent_rightDerivedPlus_of_moduleFinite_cohomology f F i h⟩
  have := isQuasicoherent_of_isCoherent F
  have := h X S f hf hSN F hF i
  exact moduleFinite_cohomology_of_isCoherent f F i
    (isCoherent_rightDerived_of_rightDerivedPlus f F i)

end Stacks.AlgebraicGeometry.ProperCohomologyFinite

end
