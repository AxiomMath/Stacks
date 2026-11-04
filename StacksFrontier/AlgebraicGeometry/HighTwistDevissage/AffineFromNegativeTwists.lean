module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageColimit.Cohomology
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.FiniteSum
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.OpensSheafificationInstances
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Affineness from the vanishing of the cohomology of negative ample twists

[Stacks, Tag 0EBD] says that a scheme `X` carrying an ample invertible module `L` is affine as
soon as `Hᵖ(X, L^{⊗ -n}) = 0` for all `p > 0` and all `n ≥ n₀`.

The source proves it in two halves. The first is the *claim*: positive-degree cohomology vanishes
on every quasi-coherent module, not only on the negative twists. The second is Serre's
cohomological criterion for affineness ([Stacks, Tag 01XF]), which turns the claim into
affineness. The claim itself is a descending induction on the degree, started from the vanishing
above the size of a finite affine cover ([Stacks, Tag 01XI]) and stepped, *at a module of finite
type*, by the short exact sequence `0 → F' → ⊕ⱼ L^{⊗ -dⱼ} → F → 0` that global generation after
an ample twist produces ([Stacks, Tag 01Q3], clause (8); quasi-coherence of the kernel `F'` is
Schemes, Lemma 26.24.1, formalized as
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` — and **not** 01PG). A module of infinite type is brought into range not by that sequence
but by a colimit argument on cohomology: [Stacks, Tag 01PG] writes it as the directed colimit of
its finite-type quasi-coherent submodules and Cohomology, Lemma 20.19.1 commutes cohomology with
that colimit.

This file performs the descending induction and nothing else: the four inputs just named are
hypotheses, since none of 01XF, 01XI, 01Q3 and 01PG is formalized at this pin (none of the four
carries an attribute in the library). What is
*proved* here is the implication from those four plus the tag's own vanishing hypothesis to
affineness, together with the step that the tag's hypothesis — about a single twist — suffices for
the finite direct sum of twists appearing in the sequence.

## Main results

* `Stacks.HighTwistDevissage.additive_hfunctor`: the cohomology functors of a scheme over an open
  are additive.
* `Stacks.HighTwistDevissage.isZero_hgroup_directSum_tensorPowModule`: the tag's hypothesis
  propagates to a finite direct sum of negative twists.
* `Stacks.HighTwistDevissage.isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower`: **the claim
  of [Stacks, Tag 0EBD]** — vanishing of the positive-degree cohomology of every quasi-coherent
  module, from the tag's hypothesis plus 01XI, 01Q3 (clause (8)) and the colimit reduction
  (01PG with Cohomology, Lemma 20.19.1).
* `Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`:
  **[Stacks, Tag 0EBD], conditional on [Stacks, Tag 01XF], [Stacks, Tag 01XI],
  [Stacks, Tag 01Q3] and [Stacks, Tag 01PG] (with Cohomology, Lemma 20.19.1).**

## Implementation notes

**The vocabulary.** The statement of this tag is phrased against names that do not exist in the
library (Tag 01PS's `IsAmple`, Tag 01CU's `tensorPower`, Tag 01CS's `IsInvertible`). They are
folded onto `Stacks.Ample.IsAmple`, `Stacks.Ample.tensorPowModule` and
`Stacks.Ample.IsInvertibleModule` respectively, which are the library's Tag 01PS, Tag 01CU and
Tag 01CS for a scheme and which carry the tag attributes. `Stacks.Ample.tensorPowModule` is
`Stacks.TensorPowers.tensorPow` of the scheme's structure presheaf by definition, so no bridge is
needed.

**Why the four inputs are hypotheses rather than open goals.** Each is the statement of a tag of
Chapter 28 or 30 not yet proved in this library, and each is stated here in the weakest form this
proof uses: 01XI only as the existence of *some* vanishing bound `e`, with no reference to a
cover; 01Q3 clause (8) only as the existence of a short exact sequence of the stated shape, with
no reference to global generation; and 01PG together with Cohomology, Lemma 20.19.1 only as the
existence, in each positive degree, of a presentation of `Hᵖ(X, F)` as a colimit of the `Hᵖ` of
finite-type quasi-coherent modules. Any instance of the source's lemmas supplies them.

**The finite-type hypothesis on `hgen` is not optional: without it this file would be vacuous.**
Without it, `hgen` would demand the dévissage sequence for *every* quasi-coherent `F`, which is
the false clause (8) rather than the source's: on a nonempty scheme no module of infinite type is
a quotient of a finite direct sum of invertible modules, so `hgen` would have **no instances** and both
theorems below would be unusable. The witness is `F = ∐_{i : I} 𝒪_X` for a countably infinite
`I : Type u`, quasi-coherent by
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma`; `S.ShortExact` makes
`S.g : S.X₂ ⟶ F` an epimorphism, epimorphisms of sheaves of modules are surjective on stalks, the
stalk functor commutes with the colimit ([Stacks, Tag 01AH]) and the stalks of an invertible
module are free of rank one, so an epimorphism from a sum of `r` invertibles would give a
surjection `𝒪_{X,x}^r → 𝒪_{X,x}^{(ℕ)}`, which tensoring with the residue field at `x` turns into
a surjection of a finite-dimensional vector space onto an infinite-dimensional one. (That
refutation is an argument, not a Lean proof; the module documentation of
`StacksFrontier/AlgebraicGeometry/AmpleGlobalGeneration/Basic.lean`, where it is discussed,
records which of its pieces are missing from the repository.) `hgen` carries
`SheafOfModules.IsFiniteType`, which is the hypothesis the source's clause (8) carries;
`Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists X L`, applied at `n₀`, then has exactly
the type of `hgen`, with no bridging lemma and no reassociation.

**Where the colimit reduction goes, and why it cannot be folded into `hgen`.** With `hgen`
restricted to finite-type modules, the dévissage sequence no longer exists for the general
quasi-coherent module the induction must descend over — and it must descend over all of them,
since the first term of the sequence, the kernel of a surjection onto a finite-type module, is
quasi-coherent and nothing more. Restoring the generality inside `hgen` reproduces the false
hypothesis instead of the source's argument. The reduction therefore enters as the separate input
`hcolim` and is consumed by the two-class engine
`Stacks.DevissageColimit.isZero_hgroup_of_descending_devissage_of_reduction`, whose dévissage
hypothesis is asked only of the finite-type modules while its conclusion is about all
quasi-coherent ones. `Stacks.DevissageColimit.isZero_obj_of_colimitPresentation` turns `hcolim`
into the engine's reduction hypothesis; it is proved, not assumed, and needs no filteredness of
the index category even though 01PG supplies it.

**Where the tag's own hypothesis is used.** Exactly once, in
`isZero_hgroup_directSum_tensorPowModule`, to see that the middle term of the dévissage sequence
is acyclic in positive degrees. It is load-bearing in the sense that dropping it leaves the
remaining hypotheses satisfiable by assuming the claim outright. That observation does *not*
establish that the reduction performed here is not a weakening of the tag: without the
finite-type hypothesis the reduction would be vacuous for the independent reason described
above, whatever `hvan` is. Nothing
below shows the four inputs jointly satisfiable, so the reduction's content is still exactly the
implication it states.

**The direct sum is a bicone, not `∐`.** The middle term is required to be the vertex of a
bilimit bicone over the family of twists, which is Mathlib's instance-free way of saying that an
object *is* their finite direct sum. Writing `∐` instead makes the statement unusable: see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/HighTwistDevissage/FiniteSum.lean`, where that failure is
documented. A consumer holding `S.X₂ ≅ ∐ fun j => …` supplies the bicone with
`CategoryTheory.Limits.biproduct.bicone`, `CategoryTheory.Limits.biproduct.isBilimit` and
`CategoryTheory.Limits.biproduct.isoCoproduct`.

**`SheafOfModules.IsFiniteType` is used with its universe pinned to the module universe**, as in
`Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`: the class quantifies the index universe
of its local generators existentially, so an unpinned `F.IsFiniteType` leaves a universe
metavariable.

**The instance hypotheses.** `HasSheafify` and `WEqualsLocallyBijective` for the site of opens of
a scheme are installed as local instances exactly as in
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean`; `EnoughInjectives` comes from Grothendieck
abelianness, as in the statements of Tags 0B5Q and 01YS; the two `HasDerivedCategory` instances are
`HasDerivedCategory.standard`, installed locally, and are what the long exact cohomology sequence
of `Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived` is built from.

**Additivity of `Hᵖ(X, -)`.** Mathlib has no `Additive` instance for
`CategoryTheory.Functor.rightDerived`; it is read off the `additive` field of the right derived
δ-functor, whose degree-`n` part is `(secF R U).rightDerived n` by `rfl`
(`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor`).

No tag attribute is attached: 0EBD's statement is not proved here, only reduced, and attaching the
tag would report the tag as formalized.

## References

* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.HighTwistDevissage

attribute [local instance] _root_.HasDerivedCategory.standard

-- Seated from `OpensSheafificationInstances`, not restated: sheafification for the site of
-- opens of a scheme, and its weak equivalences.
attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable (X : Scheme.{u})

/-- The cohomology functors of a scheme over an open are additive. Read off the `additive` field
of the right derived δ-functor of sections, whose degree-`n` part is the degree-`n` right derived
functor of sections on the nose. -/
theorem additive_hfunctor (U : X.Opens) (n : ℕ) : (Hfunctor X.ringCatSheaf U n).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF X.ringCatSheaf U)).additive n

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The hypothesis of [Stacks, Tag 0EBD] propagates to finite direct sums.** If every twist
`L^{⊗ -n}` with `n ≥ n₀` has vanishing positive-degree cohomology, then so does any object
exhibited as a finite direct sum of such twists, because `Hᵖ(X, -)` is additive. -/
theorem isZero_hgroup_directSum_tensorPowModule {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    {r : ℕ} (d : Fin r → ℤ) (hd : ∀ j, n₀ ≤ d j)
    {b : Bicone fun j : Fin r => Stacks.Ample.tensorPowModule X L (-(d j))} (hb : b.IsBilimit)
    (p : ℕ) (hp : 0 < p) : IsZero ((Hfunctor X.ringCatSheaf ⊤ p).obj b.pt) :=
  have _hadd : (Hfunctor X.ringCatSheaf ⊤ p).Additive := additive_hfunctor X ⊤ p
  isZero_obj_of_isBilimit (Hfunctor X.ringCatSheaf ⊤ p) hb
    (HasBiproduct.of_hasCoproduct _) fun j => hvan (d j) p (hd j) hp

/-- **The claim inside the proof of [Stacks, Tag 0EBD].** Positive-degree cohomology vanishes on
*every* quasi-coherent module, not only on the negative twists of `L`.

The inputs are the tag's own vanishing hypothesis `hvan`, a cohomological vanishing bound `hdim`
([Stacks, Tag 01XI]), the dévissage sequence `hgen` for the modules **of finite type**
([Stacks, Tag 01Q3], clause (8)), and the colimit reduction `hcolim` that brings a module of
infinite type into range ([Stacks, Tag 01PG] with Cohomology, Lemma 20.19.1). The proof is the
two-class descending induction of
`Stacks.DevissageColimit.isZero_hgroup_of_descending_devissage_of_reduction`: the dévissage
sequence is used only at the finite-type modules, its quasi-coherent kernel is handled one degree
up, and `hcolim` carries each degree from the finite-type modules to all quasi-coherent ones.

Restricting `hgen` to finite-type modules is forced: stated for all quasi-coherent modules it has
no instances on a nonempty scheme, and the version of this theorem that stated it so had no
content. See the implementation notes. -/
theorem isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    (e : ℕ)
    (hdim : ∀ (F : X.Modules) (p : ℕ), e < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F))
    (hgen : ∀ F : X.Modules, F.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} F →
      ∃ (S : ShortComplex X.Modules) (r : ℕ) (d : Fin r → ℤ)
        (b : Bicone fun j : Fin r => Stacks.Ample.tensorPowModule X L (-(d j)))
        (_ : b.IsBilimit) (_ : S.X₂ ≅ b.pt),
        S.ShortExact ∧ S.X₃ = F ∧ S.X₁.IsQuasicoherent ∧ ∀ j, n₀ ≤ d j)
    (hcolim : ∀ p : ℕ, 0 < p → ∀ F : X.Modules, F.IsQuasicoherent →
      ∃ (J : Type u) (_ : SmallCategory J) (pres : ColimitPresentation J F),
        (∀ j, (pres.diag.obj j).IsQuasicoherent) ∧
        (∀ j, SheafOfModules.IsFiniteType.{u, u, u} (pres.diag.obj j)) ∧
        Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone pres.cocone)))
    (F : X.Modules) (p : ℕ) (hp : 0 < p) (hF : F.IsQuasicoherent) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  refine Stacks.DevissageColimit.isZero_hgroup_of_descending_devissage_of_reduction
    X.ringCatSheaf ⊤ (fun G : X.Modules => G.IsQuasicoherent)
    (fun G : X.Modules => G.IsQuasicoherent ∧ SheafOfModules.IsFiniteType.{u, u, u} G) e
    (fun q hq G hG => hdim G q hq hG) ?_ ?_ p hp F hF
  · intro q hq hvanish G hG
    obtain ⟨J, _, pres, hqc, hft, ⟨hcol⟩⟩ := hcolim q hq G hG
    exact Stacks.DevissageColimit.isZero_obj_of_colimitPresentation
      (Hfunctor X.ringCatSheaf ⊤ q) _ hvanish pres (fun j => ⟨hqc j, hft j⟩) hcol
  · intro G hG
    obtain ⟨S, r, d, b, hb, iso, hS, hX₃, hqcS, hd⟩ := hgen G hG.1 hG.2
    refine ⟨S, hS, hX₃, hqcS, fun m hm => ?_⟩
    exact IsZero.of_iso (isZero_hgroup_directSum_tensorPowModule X L hvan d hd hb m hm)
      ((Hfunctor X.ringCatSheaf ⊤ m).mapIso iso)

/-- **[Stacks, Tag 0EBD], conditional on [Stacks, Tag 01XF], [Stacks, Tag 01XI],
[Stacks, Tag 01Q3] and [Stacks, Tag 01PG].** A scheme carrying an ample invertible module whose
sufficiently negative tensor powers have no higher cohomology is affine.

The five hypotheses are, in order: the tag's own vanishing hypothesis; Serre's cohomological
criterion for affineness (01XF); a cohomological vanishing bound on quasi-coherent modules
(01XI); the dévissage sequence from global generation after an ample twist, for the modules of
finite type (01Q3, clause (8), whose kernel is quasi-coherent by Schemes, Lemma 26.24.1 —
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` — rather than by 01PG); and the
presentation of the cohomology of a general quasi-coherent module as a colimit of the cohomology
of its finite-type quasi-coherent submodules (01PG with Cohomology, Lemma 20.19.1).
Quasi-compactness of `X`, which 01XF also needs, is supplied by ampleness. -/
theorem isAffine_of_isZero_cohomology_negative_tensorPower (hL : Stacks.Ample.IsAmple X L)
    {n₀ : ℤ}
    (hvan : ∀ (n : ℤ) (p : ℕ), n₀ ≤ n → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (Stacks.Ample.tensorPowModule X L (-n))))
    (serre : CompactSpace ↥X →
      (∀ (F : X.Modules) (p : ℕ), 0 < p → F.IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ p F)) → IsAffine X)
    (e : ℕ)
    (hdim : ∀ (F : X.Modules) (p : ℕ), e < p → F.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ p F))
    (hgen : ∀ F : X.Modules, F.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} F →
      ∃ (S : ShortComplex X.Modules) (r : ℕ) (d : Fin r → ℤ)
        (b : Bicone fun j : Fin r => Stacks.Ample.tensorPowModule X L (-(d j)))
        (_ : b.IsBilimit) (_ : S.X₂ ≅ b.pt),
        S.ShortExact ∧ S.X₃ = F ∧ S.X₁.IsQuasicoherent ∧ ∀ j, n₀ ≤ d j)
    (hcolim : ∀ p : ℕ, 0 < p → ∀ F : X.Modules, F.IsQuasicoherent →
      ∃ (J : Type u) (_ : SmallCategory J) (pres : ColimitPresentation J F),
        (∀ j, (pres.diag.obj j).IsQuasicoherent) ∧
        (∀ j, SheafOfModules.IsFiniteType.{u, u, u} (pres.diag.obj j)) ∧
        Nonempty (IsColimit ((Hfunctor X.ringCatSheaf ⊤ p).mapCocone pres.cocone))) :
    IsAffine X :=
  serre hL.1 fun F p hp hF =>
    isZero_hgroup_of_isAmple_of_isZero_negative_tensorPower X L hvan e hdim hgen hcolim F p hp hF

end Stacks.HighTwistDevissage

end
