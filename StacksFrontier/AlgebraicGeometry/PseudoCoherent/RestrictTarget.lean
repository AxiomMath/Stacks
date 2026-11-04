module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SchemePushforwardPseudoCoherent
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion

/-!
# Restricting the target of a closed immersion, and the second paragraph of Stacks 09VD

Let `i : Z ⟶ Y` be a closed immersion of schemes, let `W` be an open subscheme of `Y` and write
`V = i⁻¹W`. If the derived pushforward `Ri_*E` is `m`-pseudo-coherent on `Y`, then the derived
pushforward of `E|_V` along the restricted closed immersion `i|_W : V ⟶ W` is `m`-pseudo-coherent
on `W`: pseudo-coherence is local, and `(Ri_*E)|_W` is `R(i|_W)_*(E|_V)`.

Both halves of that sentence are already in the library. What this file supplies is the passage
between the two vocabularies they are written in. The identification
`AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardObjIso` and the locality statement
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` are about a *ringed
space* `Y`, its open subspace `Y|_W`, the restriction functor
`AlgebraicGeometry.RingedSpace.restrictModules` and the restricted morphism
`AlgebraicGeometry.RingedSpace.restrictHom`; the local condition of Stacks 09UI is about a
*scheme* `Y`, the open subscheme `W.toScheme`, Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along `W.ι` and Mathlib's
`AlgebraicGeometry.morphismRestrict`. The two restriction functors and the two restricted
morphisms agree, but neither agreement is syntactic, and neither can be installed by typeclass
synthesis; see the implementation notes.

With the crossing available, **the second paragraph of the proof of Stacks 09VD** is a two-step
argument and is proved here. Its first paragraph is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen`, and
the two compose to Stacks 09VD at the standard opens its own proof produces.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`: the crossing on
  derived categories, `(·)|_U ≅ (·)|_{U.ι}`.
* `AlgebraicGeometry.Scheme.Modules.PushforwardStructureSheafPseudoCoherent`: the side condition
  of Stacks 09VA at the closed immersions of a fixed scheme into the finite-dimensional affine
  spaces over a base, named so that the hypotheses below can be read.

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict`: the
  local condition of Stacks 09UI at a closed immersion `i : Z ⟶ Y` implies it at the restriction
  `i|_W : i⁻¹W ⟶ W` for the restricted object. This is the step the second paragraph of
  Stacks 09VD takes, and it uses no pseudo-coherence theory beyond locality of the predicate.
* `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen`:
  **the second paragraph of the proof of Stacks 09VD.** For affine `S`, the equivalent conditions
  of Stacks 09VC for `(X ⟶ S, E)` imply them for `(X_g ⟶ S, E|_{X_g})`, for every global section
  `g` of `X`.
* `exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen`, in the same namespace:
  **Stacks 09VD at a standard open of `X`**, the two paragraphs composed.

## Implementation notes

**The crossing, and why it needs its instances written out.** `Scheme.Modules Y` is a `def` for
`SheafOfModules Y.ringCatSheaf` carrying its own `Category` instance, and
`Stacks.StrictlyPerfect.OXMod Y.toRingedSpace` is the same type a third time; the three agree
definitionally but not reducibly, so typeclass synthesis does not cross between them. Here the
wall is met in *both* directions at once, because
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` is an isomorphism *between* a
functor stated in the ringed-space idiom and one stated in Mathlib's, so whichever ambient
spelling the elaborator picks for the target category, the three exactness instances of the other
functor are not found. Pinning the spelling and supplying all six instances as terms —
`AlgebraicGeometry.RingedSpace.restrictModules_additive` and its two companions on one side, and
on the other `AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive` together with two
instances obtained by `have ... := inferInstance` where the functor's own spelling is still in
force — elaborates in about two seconds: a term ascription is checked at default transparency,
which does see through the `def`s.

**The restricted morphism.** `AlgebraicGeometry.RingedSpace.restrictHom` and Mathlib's
`AlgebraicGeometry.morphismRestrict` are equal but not definitionally so, and
`AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` takes the closed-embedding hypothesis as
an argument, so the equation cannot be rewritten under it — the motive is not type correct.
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.derivedPushforwardOXMod_congr` takes the two
morphisms and their equation as separate arguments and substitutes, after which the two
closed-embedding hypotheses are proofs of one proposition and so interchangeable.

**What is conditional and what is not.** The crossing and
`IsPseudoCoherentFromAfterPushforward.morphismRestrict` are unconditional. The two
`exists_...` results carry the side condition of Stacks 09VA — that the pushforward of the
structure sheaf along the closed immersion in question is a pseudo-coherent module — exactly as
the first paragraph of Stacks 09VD does, and for the same reason: Stacks 09VA is applied
to a closed immersion of the intermediate scheme into an affine space over the base. The
intermediate scheme here is a standard open `D(g')` of an affine space over the base, so the
hypothesis is asked for at those schemes only. Its algebraic content is
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective` together with the
*module-to-sheaf* half of Stacks 08E7, which is proved as
`Stacks.AffineTilde.isPseudoCoherent_tildeComplex`; what is missing between the two is the
identification of the pushforward of a structure sheaf along a closed immersion of affine schemes
with the sheaf associated to the target ring viewed as a module over the source, for which
`AlgebraicGeometry.pushforwardTildeIso` (Stacks 01I9) is the bridge.

No `stacks` attribute is placed here. Stacks 09VD quantifies over an arbitrary affine open `U` of
`X`, while its own proof — and the two results below — produce the conclusion for a *standard*
open; deducing the statement at an arbitrary affine open from the standard-open case is Stacks
09VE, whose remaining direction is not available (see the references in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairs.lean`).

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry

universe d u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-! ### The two vocabularies of restriction -/

/-- **The restriction of a morphism of schemes to an open subscheme of the target, in the two
vocabularies.** `AlgebraicGeometry.RingedSpace.restrictHom` of the underlying morphism of ringed
spaces is the underlying morphism of ringed spaces of Mathlib's
`AlgebraicGeometry.morphismRestrict`.

Both become the same morphism after composing with the open immersion `ι_W`, by
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict` and
`AlgebraicGeometry.morphismRestrict_ι`, and `ι_W` is a monomorphism of ringed spaces; cancelling
it proves the identity.

This duplicates `AlgebraicGeometry.RingedSpace.restrictHom_eq_morphismRestrict` in
`StacksFrontier/AlgebraicGeometry/Conormal/AffineSections.lean`, and is kept private here rather
than imported: that file sits at the top of the conormal development, and importing it into the
pseudo-coherence line to reach a four-line bridge would invert the dependency between two
unrelated chapters. Flagged for a repository-tier deduplication pass. -/
public theorem restrictHom_eq_morphismRestrict' {Z X : Scheme.{u}} (f : Z ⟶ X) (W : X.Opens) :
    restrictHom f.toLRSHom.toShHom W = (f ∣_ W).toLRSHom.toShHom := by
  refine (cancel_mono (X.toLocallyRingedSpace.toRingedSpace.ofRestrict W.isOpenEmbedding)).1 ?_
  rw [restrictHom_comp_ofRestrict]
  exact (congrArg (fun g : (f ⁻¹ᵁ W).toScheme ⟶ X => g.toLRSHom.toShHom)
    (morphismRestrict_ι f W)).symm

/-- **Restriction to an open subscheme on derived categories, in the two vocabularies.** The
functor induced on derived categories by the ringed-space restriction
`AlgebraicGeometry.RingedSpace.restrictModules` — which is
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` — is the one induced by Mathlib's
restriction along the open immersion `U.ι`.

The module-level identification is
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`; this carries it to derived
categories through `CategoryTheory.Functor.mapDerivedCategoryCongr`. All six exactness instances
are supplied as terms: the two functors live in two definitionally but not reducibly equal
spellings of one category, so whichever spelling is in force, synthesis fails for the other
functor. -/
public def derivedRestrictModulesIsoRestrictFunctor (Z : Scheme.{u}) (U : Z.Opens) :
    derivedRestrictModules Z.toRingedSpace U ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  have hL : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  have hC : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  @Functor.mapDerivedCategoryCongr _ _ _ _ _ _ _ _ _ _
    (restrictModules_additive Z.toRingedSpace U)
    (restrictModules_preservesFiniteLimits Z.toRingedSpace U)
    (restrictModules_preservesFiniteColimits Z.toRingedSpace U)
    (Scheme.Modules.restrictFunctor_additive U.ι) hL hC
    (restrictModulesIsoRestrictFunctor Z U)

/-- Sheaf-level `m`-pseudo-coherence of a derived pushforward is transported along an equality of
the morphism pushed forward along.

`AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` takes the closed-embedding hypothesis as
an explicit argument, so an equation between morphisms cannot be rewritten inside it: the motive
is not type correct. Taking the two morphisms and the equation as separate arguments and
substituting avoids that, and the two hypotheses are then proofs of one proposition. -/
public theorem IsPseudoCoherentFrom.derivedPushforwardOXMod_congr {Z X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Z)] [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (k k' : Z ⟶ X) (e : k = k') (hk : Topology.IsClosedEmbedding k.hom.base)
    (hk' : Topology.IsClosedEmbedding k'.hom.base) (A : DerivedCategory (OXMod.{u, u} Z)) (m : ℤ)
    (h : IsPseudoCoherentFrom ((derivedPushforwardOXMod k hk).obj A) m) :
    IsPseudoCoherentFrom ((derivedPushforwardOXMod k' hk').obj A) m := by
  subst e
  exact h

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

/-! ### Restricting the target of a closed immersion -/

/-- **The local condition of Stacks 09UI restricts to an open subscheme of the target.** Let
`i : Z ⟶ Y` be a closed immersion of schemes and let `W` be an open subscheme of `Y`. If the
derived pushforward of `E` along `i` is `m`-pseudo-coherent on `Y`, then the derived pushforward
of `E|_{i⁻¹W}` along the restricted closed immersion `i|_W : i⁻¹W ⟶ W` is `m`-pseudo-coherent
on `W`.

This is the step the second paragraph of Stacks 09VD takes, and it uses no pseudo-coherence theory
beyond locality: `(Ri_*E)|_W` is `m`-pseudo-coherent because `Ri_*E` is
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules`), and it is
isomorphic to `R(i|_W)_*(E|_{i⁻¹W})`
(`AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardObjIso`). Neither half of Stacks 09VA
is involved. -/
public theorem IsPseudoCoherentFromAfterPushforward.morphismRestrict {Z Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (W : Y.Opens) (E : DerivedCategory Z.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterPushforward i E m) :
    IsPseudoCoherentFromAfterPushforward (i ∣_ W)
      ((restrictFunctor (i ⁻¹ᵁ W).ι).mapDerivedCategory.obj E) m := by
  have hi : Topology.IsClosedEmbedding i.toLRSHom.toShHom.hom.base :=
    Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i
  have hiW : Topology.IsClosedEmbedding (i ∣_ W).toLRSHom.toShHom.hom.base :=
    Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom (i ∣_ W)
  have h₁ : RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
      ((RingedSpace.derivedPushforwardOXMod i.toLRSHom.toShHom hi).obj E) m :=
    (isPseudoCoherentFromAfterPushforward_iff i E m).mp h
  have h₂ := RingedSpace.isPseudoCoherentFrom_derivedRestrictModules _ m h₁ W
  have h₃ := h₂.of_iso (RingedSpace.derivedRestrictPushforwardObjIso i.toLRSHom.toShHom W hi E)
  have h₄ := RingedSpace.IsPseudoCoherentFrom.derivedPushforwardOXMod_congr _ _
    (RingedSpace.restrictHom_eq_morphismRestrict' i W) _ hiW _ _ h₃
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact h₄.of_iso
    ((RingedSpace.derivedPushforwardOXMod (i ∣_ W).toLRSHom.toShHom hiW).mapIso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Z (i ⁻¹ᵁ W)).app E))

/-! ### The second paragraph of Stacks 09VD -/

/-- **The side condition of Stacks 09VA at the closed immersions of `Y` into the
finite-dimensional affine spaces over `S`**: for every closed immersion
`p : Y ⟶ 𝔸ᴺ_S` with `N` finite, the pushforward `p_*𝒪_Y` is a pseudo-coherent sheaf of
`𝒪_{𝔸ᴺ_S}`-modules.

This is the hypothesis that
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_comp` asks for,
named so that the statements below are readable. It is a genuine condition on `Y`: asked for at
*every* affine `Y` of finite type over `S` it is false, being equivalent to relative
pseudo-coherence of `Y` over `S`. The results below ask for it only at the standard opens of
affine spaces over `S`, where it holds. -/
public abbrev PushforwardStructureSheafPseudoCoherent (S Y : Scheme.{u}) : Prop :=
  ∀ (N : ℕ) (p : Y ⟶ AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
    RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
      ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
        ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)))

/-- **The second paragraph of the proof of Stacks 09VD.** Let `S` be affine, let `E` be an object
of `D(𝒪_X)` and let `g` be a global section of `X`. Granted the side condition of
Stacks 09VA at the standard opens of the affine spaces over `S`, the equivalent conditions of
Stacks 09VC for the pair `(X ⟶ S, E)` imply them for the pair `(X_g ⟶ S, E|_{X_g})`.

The argument is the source's. A closed immersion `j : X ⟶ 𝔸ᴺ_S` over `S` is surjective on global
sections, so `g` lifts to `g'` on `𝔸ᴺ_S`, and then `j⁻¹(D(g')) = X_g`. Restricting the target of
`j` to `D(g')` keeps the pushforward `m`-pseudo-coherent, by
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict`; and
`D(g')` is an affine scheme locally of finite type over `S`, so
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_comp` composes
the closed immersion `X_g ⟶ D(g')` with a closed immersion of `D(g')` into an affine space over
`S`.

The source writes that closed immersion down in coordinates, as the surjection
`R[x₀, …, x_{N+1}] ↠ R[x₀, …, x_N, 1/g']`; it is not necessary to, because `D(g') ⟶ S` is locally
of finite type whatever `g'` is, being an open immersion followed by the structure morphism of an
affine space. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_basicOpen {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S)
    (hO : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ) (g : Γ(X, ⊤))
    (h : ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward j E m) :
    ∃ (N' : ℕ) (l : (X.basicOpen g).toScheme ⟶ AffineSpace (ULift.{u} (Fin N')) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin N')) S).hom = (X.basicOpen g).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor (X.basicOpen g).ι).mapDerivedCategory.obj E) m := by
  obtain ⟨N, j, hj, hjo, hpc⟩ := h
  have := hj
  obtain ⟨g', hg'⟩ := j.app_surjective ⊤ (isAffineOpen_top _) g
  have hpre : j ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') = X.basicOpen g := by
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen hg'
  rw [← hpre]
  let hWa : IsAffineOpen ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') :=
    (isAffineOpen_top _).basicOpen g'
  let _ : IsAffine ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g').toScheme := hWa
  have hover : LocallyOfFiniteType ((AffineSpace.over (ULift.{u} (Fin N)) S).hom) := by
    rw [AffineSpace.over_hom_eq]
    infer_instance
  have hgft : LocallyOfFiniteType
      (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g').ι ≫
        (AffineSpace.over (ULift.{u} (Fin N)) S).hom) :=
    MorphismProperty.comp_mem _ _ _ inferInstance hover
  obtain ⟨N', l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_of_comp
      (j ∣_ ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g'))
      (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g').ι ≫
        (AffineSpace.over (ULift.{u} (Fin N)) S).hom) (hO N g') _ m
      (IsPseudoCoherentFromAfterPushforward.morphismRestrict j
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') E m hpc)
  refine ⟨N', l, hl, ?_, hlpc⟩
  rw [hlo, ← Category.assoc, morphismRestrict_ι, Category.assoc, hjo]

/-- **Stacks 09VD at a standard open of `X`**, the two paragraphs of its proof composed. Let `S`
be affine, let `V` be an affine open of `S`, let `f : X ⟶ V` be a morphism of schemes, let `E` be
an object of `D(𝒪_X)` and let `g` be a global section of `X`.
Granted the side condition of Stacks 09VA at the two kinds of intermediate scheme that occur, the
equivalent conditions of Stacks 09VC for the pair `(X ⟶ V, E)` imply them for the pair
`(X_g ⟶ S, E|_{X_g})`.

The second paragraph shrinks `X` to `X_g` over `V`
(`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen`), and
the first then enlarges the base from `V` to `S`
(`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen`).
The source takes `V` to be a standard open of `S`; neither step needs that.

Stacks 09VD itself allows an arbitrary affine open of `X` in place of `X_g`. Its own proof
produces only the standard-open case, and passing from standard opens to an arbitrary affine open
is Stacks 09VE, which is why no `stacks` attribute is placed here. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen
    {S X : Scheme.{u}} [IsAffine S] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
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
    (E : DerivedCategory X.Modules) (m : ℤ) (g : Γ(X, ⊤))
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : (X.basicOpen g).toScheme ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = ((X.basicOpen g).ι ≫ f) ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward j
            ((restrictFunctor (X.basicOpen g).ι).mapDerivedCategory.obj E) m :=
  let : IsAffine (V.1 : Scheme.{u}) := V.2
  exists_isPseudoCoherentFromAfterPushforward_of_affineOpen V ((X.basicOpen g).ι ≫ f) hOS _ m
    (exists_isPseudoCoherentFromAfterPushforward_basicOpen f hOV E m g h)

end AlgebraicGeometry.Scheme.Modules

end
