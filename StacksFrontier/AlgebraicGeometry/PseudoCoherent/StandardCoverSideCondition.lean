module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenLocalization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition

/-!
# Stacks 09VE and 09VD with the affine-space side condition discharged

Stacks 09VE and Stacks 09VD at an arbitrary affine open are proved in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardCoverGluing.lean` and
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenLocalization.lean`, each carrying as a
hypothesis the side condition of Stacks 09VA at a closed immersion
`p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` of finite-dimensional affine spaces over `S`, *quantified over every such
closed immersion with no compatibility with the structure morphisms*. In that shape the
hypothesis is false; the counterexample is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean`.

It need not be repaired, because it need not be assumed at all. Both proofs use it only to apply
Stacks 09VC, and Stacks 09VC is proved with no hypotheses as
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin`; the side condition
there is discharged by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace`,
whose closed immersion *does* carry the compatibility
`p ≫ 𝔸ᵇ_S ↘ S = 𝔸ᵃ_S ↘ S`. This file replays the two proofs against that form of Stacks 09VC,
so that the hypothesis disappears.

What survives is the side condition of Stacks 09VA at the *standard opens* of the affine spaces
over the base — `hOb` below, and its counterpart `hOV` over an affine open `V ⊆ S`, and the
mixed-base `hOS`. Those are genuine residues: no result in this library yet says that
`q_*𝒪_{D(y)}` is a pseudo-coherent module for a closed immersion `q : D(y) ⟶ 𝔸ᴺ_S`, and they
too are stated here without the compatibility with the structure morphisms that they need. See
the implementation notes.

## Main results

* `isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen'` (in the
  `AlgebraicGeometry.Scheme.Modules` namespace): the local step of Stacks 09VE, with the
  affine-space side condition discharged.
* `exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen'` (same namespace): the
  implication (1) ⇒ (2) of Stacks 09VE, with the affine-space side condition discharged.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen'`: **Stacks
  09VE**, granted only the side condition of Stacks 09VA at the standard opens of the affine
  spaces over `S`.
* `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen'`:
  **Stacks 09VD at an arbitrary affine open**, granted only the side condition of Stacks 09VA at
  the standard opens of the affine spaces over `V` and over `S` and at the affine spaces over `V`
  mapping to the affine spaces over `S`.

## Implementation notes

**Why the proofs are replayed rather than reused.** The two existing results take the false form of
the side condition as a hypothesis, so nothing can be obtained from them by instantiation: a
`Π`-type hypothesis has to be supplied in full, and this one cannot be. The bodies below are the
original bodies with the single application of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin` replaced by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin`. The original results
are left untouched.

**The residual hypotheses are also stated without the compatibility they need, and so are also
not dischargeable as they stand.**
`AlgebraicGeometry.Scheme.Modules.PushforwardStructureSheafPseudoCoherent` quantifies over every
closed immersion `q : Y ⟶ 𝔸ᴺ_S`, and the counterexample of
`SideCondition.lean` applies verbatim at `N = 0`, `y = 1`: for `R = k[t₀, t₁, …]` and
`ψ : R ↠ R` sending `t_{2i} ↦ t_i`, `t_{2i+1} ↦ 0`, the map `φ : R[x] ↠ R` extending `ψ` by
`x ↦ 0` has non-finitely-generated kernel, and `Spec φ` is a closed immersion
`D(1) ⊆ 𝔸⁰_S ⟶ 𝔸¹_S` whose pushforward of the structure sheaf is not pseudo-coherent. The
compatibility `q ≫ 𝔸ᴺ_S ↘ S = Y ↪ 𝔸ᴹ_S ↘ S` is available at both call sites — it is the
`hqo` produced by `AlgebraicGeometry.exists_isClosedImmersion_affineSpace` — so adding it to the
predicate costs the consumers nothing.

**What the repaired residue then needs.** With the compatibility in place, the side condition at
`q : D(y) ⟶ 𝔸ᴺ_S` over `S` is, through
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_of_isAffine`,
the statement that `Γ(D(y), ⊤)` — a localization away of a polynomial ring over `Γ(S, ⊤)` — is
pseudo-coherent relative to `Γ(S, ⊤)`. The algebraic inputs for that are available:
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self` and Stacks 067D
(`PseudoCoherence.relativelyPseudoCoherent_iff_of_comp`) or Stacks 0679
(`PseudoCoherence.localization_preserves_relativePseudoCoherent`). The same statement with
`Γ(S, ⊤)` replaced by `Γ(V, ⊤)` covers `hOV`, and `hOS` is the case of the localization
`Γ(V, ⊤)[y₁, …, yₙ] = (Γ(S, ⊤)[y₁, …, yₙ])_b` of a polynomial ring over `Γ(S, ⊤)` when `V` is the
standard open `S_b` — which is the hypothesis `hV` that Stacks 09VD makes and that the
arbitrary-affine-open form drops.

**Two expected linter findings.**
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen'` and
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen'` each
carry the instance `[QuasiCompact f]` that the statements of Stacks 09VE and Stacks 09VD include
and that the proofs do not use — it is automatic for a morphism of affine schemes. It is kept
because the statement is the contract, so `lake lint` reports two `unusedArguments` findings on
this file; the same pattern is already present in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardCoverGluing.lean` and
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenLocalization.lean`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-- **The local step of the proof of Stacks 09VE, with the affine-space side condition
discharged.** This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen`
with its hypothesis `hO` removed: the application of Stacks 09VC inside the proof is the
hypothesis-free `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin`
rather than the conditional
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin`. -/
public theorem isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen'
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {M : ℕ}
    (i : X ⟶ AffineSpace (ULift.{u} (Fin M)) S) [IsClosedImmersion i] (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (hover : i ≫ (AffineSpace.over (ULift.{u} (Fin M)) S).hom = f)
    (y : Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤))
    (hOy : PushforwardStructureSheafPseudoCoherent S
      ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (k : ℕ) (l : (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom =
          (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor
              (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E)
            m) :
    IsPseudoCoherentFromAfterPushforward (i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y)
      ((restrictFunctor
        (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E) m := by
  have hWa : IsAffineOpen ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) :=
    (isAffineOpen_top _).basicOpen y
  have hWaff : IsAffine ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := hWa
  have hUaff : IsAffine (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := by
    rw [Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_top X).basicOpen _
  have hoverft : LocallyOfFiniteType ((AffineSpace.over (ULift.{u} (Fin M)) S).hom) := by
    rw [AffineSpace.over_hom_eq]
    infer_instance
  have hWft : LocallyOfFiniteType
      (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
        (AffineSpace.over (ULift.{u} (Fin M)) S).hom) :=
    MorphismProperty.comp_mem _ _ _ inferInstance hoverft
  obtain ⟨N, q, hq, hqo⟩ := exists_isClosedImmersion_affineSpace
    (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
      (AffineSpace.over (ULift.{u} (Fin M)) S).hom)
  have := hq
  have key : IsPseudoCoherentFromAfterPushforward
      ((i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) ≫ q) _ m :=
    (isPseudoCoherentFrom_some_iff_forall_fin
      ((i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f) _ m).mp h N _
      inferInstance (by rw [Category.assoc, hqo, ← Category.assoc, morphismRestrict_ι,
        Category.assoc, hover])
  rw [isPseudoCoherentFromAfterPushforward_comp_iff] at key
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact isPseudoCoherentFrom_of_pushforward_mapDerivedCategory q (hOy N q hq) m _ key

/-- **The implication (1) ⇒ (2) of Stacks 09VE, with the affine-space side condition
discharged.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen`
with its hypothesis `hO` removed; the local step is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen'`
above. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen'
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g)
    (h : ∀ j : Fin n, ∃ (k : ℕ) (l : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) :
    ∃ (K : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin K)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin K)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m := by
  obtain ⟨M, i, hi, hiover⟩ := exists_isClosedImmersion_affineSpace f
  have := hi
  obtain ⟨y, hy⟩ : ∃ y : Fin n → Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤),
      ∀ j, i.appTop (y j) = g j := by
    choose y hy using fun j => i.app_surjective ⊤ (isAffineOpen_top _) (g j)
    exact ⟨y, hy⟩
  have hpre : ∀ j, i ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j)) =
      X.basicOpen (g j) := by
    intro j
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen (hy j)
  have hcov : (⨆ j, X.basicOpen (g j)) = ⊤ :=
    (Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top g).mp hg
  refine ⟨M, i, hi, hiover, ?_⟩
  rw [isPseudoCoherentFromAfterPushforward_iff]
  refine RingedSpace.isPseudoCoherentFrom_of_local_restrict
    (X := (AffineSpace (ULift.{u} (Fin M)) S).toRingedSpace) _ m fun x => ?_
  by_cases hx : x ∈ Set.range i.toLRSHom.toShHom.hom.base
  · obtain ⟨z, rfl⟩ := hx
    have hz : z ∈ (⨆ j, X.basicOpen (g j)) := by
      rw [hcov]
      exact Opens.mem_top z
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz
    rw [← hpre j] at hj
    refine ⟨(AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j), hj, ?_⟩
    refine isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict i _ E m ?_
    exact isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen' i f hiover (y j)
      (hOb M (y j)) E m (by rw [hpre j]; exact h j)
  · have hopen : IsOpen (Set.range i.toLRSHom.toShHom.hom.base)ᶜ :=
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isClosed_range.isOpen_compl
    have hbot : (Opens.map i.toLRSHom.toShHom.hom.base).obj
        ⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩ = ⊥ := by
      ext w
      simp
    have hzero := RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot
      i.toLRSHom.toShHom ⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) hbot E
    exact ⟨⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩, hx,
      RingedSpace.IsPseudoCoherentFrom.of_isZero hzero m⟩

/-- **Stacks 09VE, with the affine-space side condition discharged.** Let `f : X ⟶ S` be a
morphism of affine schemes locally of finite type, let `E` be an object of `D(𝒪_X)` and let the
basic opens of `g : Fin n → Γ(X, ⊤)` be a standard affine open cover of `X`. Granted the side
condition of Stacks 09VA at the standard opens of the affine spaces over `S`, the equivalent
conditions of Stacks 09VC hold for every pair `(X_{gⱼ} ⟶ S, E|_{X_{gⱼ}})` if and only if they
hold for the pair `(X ⟶ S, E)`.

This is `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen` with its
hypothesis `hO` removed. No `stacks` attribute is placed: Stacks 09VE is stated without
hypotheses, and `hOb` remains. -/
public theorem isPseudoCoherentFrom_some_iff_forall_basicOpen' {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    (∀ j : Fin n, ∃ (k : ℕ) (i : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward i
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) ↔
      (∃ (k : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin k)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = f ∧
            IsPseudoCoherentFromAfterPushforward i E m) :=
  ⟨exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen' f hOb E m g hg,
    fun h j => exists_isPseudoCoherentFromAfterPushforward_basicOpen f hOb E m (g j) h⟩

/-- **Stacks 09VD at an arbitrary affine open of `X`, with the affine-space side condition
discharged.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen` with its
hypothesis `hO` removed; the gluing step is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen'`
above.

No `stacks` attribute is placed: Stacks 09VD is stated without hypotheses, and `hOV`, `hOS` and
`hOb` remain. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_affineOpen' {S X : Scheme.{u}}
    [IsAffine S] [IsAffine X] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hOV : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u}), ⊤)),
      PushforwardStructureSheafPseudoCoherent (V.1 : Scheme.{u})
        ((AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u})).basicOpen a).toScheme)
    (hOS : ∀ (n N : ℕ) (p : AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}) ⟶
        AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit
              (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).ringCatSheaf))))
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (U : X.affineOpens) (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward i
            ((restrictFunctor U.1.ι).mapDerivedCategory.obj E) m := by
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨N, b, hbU, hbcov⟩ := exists_fin_basicOpen_le_cover U.1
  have hpre : ∀ j, U.1.ι ⁻¹ᵁ X.basicOpen (b j) =
      (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (b j)) :=
    fun j => Scheme.preimage_basicOpen_top U.1.ι (b j)
  have hcov : (⨆ j, (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (b j))) = ⊤ :=
    (iSup_congr fun j => hpre j).symm.trans hbcov
  refine exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen'
    (U.1.ι ≫ f ≫ V.1.ι) hOb _ m (fun j => U.1.ι.appTop (b j))
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov) fun j => ?_
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen V f hOV hOS E m (b j) h
  have := hl
  rw [← hpre j]
  refine ⟨k, (Scheme.Opens.isoOfLE (hbU j)).hom ≫ l, inferInstance, ?_,
    isPseudoCoherentFromAfterPushforward_isoOfLE (hbU j) l E m hlpc⟩
  rw [Category.assoc, hlo, ← Category.assoc, ← Category.assoc,
    Scheme.Opens.isoOfLE_hom_ι (hbU j), Category.assoc, Category.assoc]

end AlgebraicGeometry.Scheme.Modules

end
