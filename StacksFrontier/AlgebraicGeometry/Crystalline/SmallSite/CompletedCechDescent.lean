module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.CompletedToposMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Coproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.ChaoticSiteCoveringObject
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech engine of Stacks 07JM on the completed affine crystalline site

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]) and fix a surjective
polynomial presentation `g : P = A[x_i] → C`.  Following the proof of [Stacks, Tag 07JN] this file
runs the Čech engine [Stacks, Tag 07JM] on the site

`𝒞^∧ = (Cris^∧(C/A))ᵒᵖ`, chaotic topology,

with the generator `D` of [Stacks, Tag 07KI] as the covering object and the coproducts
`D(n) = D ⨿ ⋯ ⨿ D` of [Stacks, Tag 07L4] as its powers, and transports the result along the
direct image of the morphism of topoi `g : Sh(𝒞) → Sh(𝒞^∧)` of [Stacks, Tag 07JL].

The engine cannot be run on `𝒞 = (Cris(C/A))ᵒᵖ` itself: `𝒞` has no weakly terminal object, because
the generator of [Stacks, Tag 07KI] is the `p`-adic completion of a divided power envelope, in
which `p` is not nilpotent, so it is not an object of `Cris(C/A)` at all.  See
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalLimits.lean`, lines 35-43.

## The smallness question, settled

[Stacks, Tag 07JM] — `Stacks.Cohomology.nonempty_addEquiv_sheafH_homology_powerCechComplex` — asks
its site to be a `CategoryTheory.SmallCategory`, and the module docstring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean` records that on the
*global* side the objects of `Cris(X/S)` form a `Type (u + 1)` while its morphisms form a
`Type u`, so that the site is not a `SmallCategory` on the nose.  The question raised there is
whether on the affine side the sizes are `Type u` throughout, in which case the obstruction would
dissolve.

**They are not.**  An object of `Cris^∧(C/A)` bundles a `DividedPowerRing.{t}`
(`Crystalline.CompletedCrystallineThickening`, field `ring`), and a `DividedPowerRing.{t}` bundles
its own carrier `Type t`; so the objects of
`Crystalline.CompletedCrystallineThickening.{u, v, t} s` form a `Type (max u v (t + 1))`, while a
morphism is a divided power map between the carriers and the morphisms form a `Type t`.  The
mismatch on the affine side is exactly the mismatch on the global side, and no choice of universes
removes it: `Type (max u v (t + 1))` is never `Type t`.

**The obstruction dissolves anyway, for a different reason.**  Lean's `SmallCategory C` is by
definition `Category.{u, u} C` for `C : Type u` — it does not say that `C` is a small *set*, only
that its objects and its morphisms live in one and the same universe.  That is always arrangeable:
`CategoryTheory.AsSmall.{0} 𝒟` replaces a `Category.{v, u} 𝒟` by an equivalent category whose
objects and morphisms both live in `Type (max u v)`.  Applied to `(Cris^∧(C/A))ᵒᵖ` the common
universe is `max (max u v (t + 1)) t = max u v (t + 1)`, which is *exactly* the coefficient
universe `Ab.{max u v (t + 1)}` in which `Crystalline.abelianSheafPushforward`, the direct image of
[Stacks, Tag 07JL], is defined.  So no universe bookkeeping is lost by passing to the small model:
`CompletedSmallSite` below is the site of [Stacks, Tag 07JL] as a `SmallCategory`, at the
coefficient universe the rest of the development already uses, and
`completedSmallSheafToposEquivalence` identifies the two sheaf topoi.

This is a statement about `SmallCategory`, not about `Small`: the objects of `Cris^∧(C/A)` are
*not* `t`-small (there are divided power thickenings of `C` on arbitrarily large index sets), and
nothing below asserts that they are.  `Small.{t}` holds only for the morphisms, which form a
`Type t` and so are `t`-small by Mathlib's `small_self`.

## Main definitions

* `Crystalline.CompletedSmallSite` — the site `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` of [Stacks, Tag 07JL] as a
  `SmallCategory`, in the universe `max u v (t + 1)`.
* `Crystalline.completedSmallSiteEquiv`, `Crystalline.completedSmallSiteOpEquiv` — its
  equivalences with `(Cris^∧(C/A))ᵒᵖ` and, after another opposite, with `Cris^∧(C/A)`.
* `Crystalline.completedSmallSheafEquivalence`,
  `Crystalline.completedSmallSheafToposEquivalence` — abelian sheaves on the small model are
  abelian presheaves on `Cris^∧(C/A)`, hence the same as abelian sheaves on the site of
  [Stacks, Tag 07JL].
* `Crystalline.smallSheafOfPresheaf` — an abelian presheaf on `Cris^∧(C/A)` read as an abelian
  sheaf on the small model.
* `Crystalline.generator` — the generator `D` of [Stacks, Tag 07KI] as an object of the site.
* `Crystalline.generatorPowerFan` — the fan exhibiting `D(n)` as the `(n + 1)`-fold power of `D`
  in the site, i.e. as the `(n + 1)`-fold coproduct of `D` in `Cris^∧(C/A)`.

## Main results

* `Crystalline.nonempty_hom_to_generator` — **`D` is a covering object**: every object of the site
  admits a morphism to `D`.  This is [Stacks, Tag 07KI] in the form [Stacks, Tag 07JM] consumes.
* `Crystalline.hasBinaryProducts_completedSmallSite` — the site has products of pairs as soon as
  `Cris^∧(C/A)` has coproducts of pairs.  Nothing here uses it; see the note below.
* `Crystalline.isLimitGeneratorPowerFan` — **[Stacks, Tag 07L4] in the site**: `D(n)` is the
  `(n + 1)`-fold power of `D` in `𝒞^∧`.
* `Crystalline.hasProduct_generator` — hence the nonempty finite powers of `D` exist in `𝒞^∧`,
  which is the products hypothesis of [Stacks, Tag 07JM] in full.
* `Crystalline.addEquivSheafHHomologyPowerCechComplexGenerator` — **[Stacks, Tag 07JM] on
  `Cris^∧(C/A)` with its comparison named**: the isomorphism of the cohomology of an abelian
  sheaf on `𝒞^∧` with the cohomology of `𝓖(D) → 𝓖(D × D) → ⋯`, as a `def`.
* `Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_generator` — **[Stacks,
  Tag 07JM] on `Cris^∧(C/A)`**: the cohomology of an abelian sheaf on `𝒞^∧` is, in every degree,
  the cohomology of the complex `𝓖(D) → 𝓖(D × D) → ⋯`.  The previous `def`, read as an existence
  statement.
* `Crystalline.powerCechComplexXIsoTensorPowerEnvelope` and
  `Crystalline.powerCechComplex_X_eq_tensorPowerEnvelope` — the degree-`n` term of that complex is
  `𝓖(D(n))`.
* `Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_directImage` — **the descent of
  [Stacks, Tag 07JM] along [Stacks, Tag 07JL]**: for an abelian presheaf `𝓕` on `Cris(C/A)` the
  cohomology of `𝒞^∧` with coefficients in the direct image `g_* 𝓕` is the cohomology of
  `(g_* 𝓕)(D) → (g_* 𝓕)(D(1)) → ⋯`.

## What is and is not proved

No tag attribute is placed: everything here is a step of the proof of [Stacks, Tag 07JN], not a
tag.

What is proved is the Čech engine on the completed site, and its transport along the direct image
of [Stacks, Tag 07JL].  One thing is **not** proved, and it is recorded as an explicit hypothesis
rather than hidden:

1. **Coproducts of pairs in `Cris^∧(C/A)` are not needed.**
   [Stacks, Tag 07JM] asks its site to have products of pairs globally, while the source's proof
   of [Stacks, Tag 07JN] checks only that the *particular* products `D × ⋯ × D = D(n)` exist, by
   [Stacks, Tag 07L4]; a hypothesis
   `[HasBinaryCoproducts (Crystalline.CompletedCrystallineThickening s)]` on every result below
   that forms the powers of the generator would therefore ask too much.  The engine's proof
   forms no product other than the powers of its covering object, and it asks for exactly
   those, as `∀ n, HasProduct (fun _ : Fin (n + 1) => X)`.  Those powers of `D` the library has
   outright, by `Crystalline.isLimitGeneratorPowerFan`, and `Crystalline.hasProduct_generator`
   registers them; so nothing below carries a coproducts hypothesis.

   The reason coproducts of arbitrary pairs were not available, is why the engine asks only for
   the powers of its covering object, is that `CRIS(C/A)` and `Cris(C/A)` have all nonempty finite
   colimits (`Crystalline.hasNonemptyFiniteColimits_dividedPowerThickening`, in
   `StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Colimit.lean`) by a construction that
   needs `p` nilpotent, so it says nothing about the completed category, where a coproduct is the
   `p`-adic completion of the divided power envelope of `B ⊗_A B'`;
   `Crystalline.completedEnvelope_isCoproduct` gives the coproducts of copies of `D` and no
   others.
2. **`R^p g_* = 0` for `p ≥ 1`**, the vanishing the source deduces from the two hypotheses of
   [Stacks, Tag 07JN] on `𝓕`.  It is not used here at all: everything below is about the
   cohomology of `𝒞^∧` with coefficients in `g_* 𝓕`.  Composing it with the vanishing — that is,
   with the Leray comparison `H^j(𝒞, 𝓕) ≅ H^j(𝒞^∧, g_* 𝓕)` — is what turns
   `nonempty_addEquiv_sheafH_homology_powerCechComplex_directImage` into [Stacks, Tag 07JN]; the
   interface is `Crystalline.abelianSheafPushforward` and
   `Crystalline.abelianSheafPushforwardIsoDirectImage`, which identify the direct image used here
   (the right Kan extension `Crystalline.abelianDirectImage`) with the direct image of the
   morphism of topoi, so that the hypothesis `R^p g_* = 0` can be stated about either.  The
   Leray degeneration that consumes it is
   `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso`, whose hypotheses on the functor being
   derived are discharged for `Crystalline.abelianSheafPushforward` by
   `Crystalline.abelianSheafPushforward_additive` together with
   `preservesFiniteLimits_abelianSheafPushforward` and
   `preservesInjectiveObjects_abelianSheafPushforward` below; what is still owed is the
   comparison of global sections `Γ(𝒞^∧, g_* -) ≅ Γ(𝒞, -)`, which by uniqueness of right
   adjoints is the statement that the inverse image of [Stacks, Tag 07JL] carries the constant
   abelian sheaf of `𝒞^∧` to the constant abelian sheaf of `𝒞`.

Also not proved, and not needed for the statements here, is the *cosimplicial* comparison of the
complex `𝓖(D) → 𝓖(D × D) → ⋯` of [Stacks, Tag 07JM] with the complex `M(0) → M(1) → ⋯` of
`Crystalline.GlobalCrystallineSituation.SmallSite.sectionsComplex`.  What is proved is the
degreewise identification of the terms, `powerCechComplexXIsoTensorPowerEnvelope`: the degree-`n`
term is `𝓖(D(n))`.  Matching the differentials needs the cosimplicial structure of `D(•)`, which
is not in the library.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

noncomputable section

namespace Crystalline

/-! ### The completed affine crystalline site as a small category -/

/-- **The site `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` of [Stacks, Tag 07JL] as a small category.**  Its objects
and its morphisms both live in `Type (max u v (t + 1))`, the coefficient universe of
`Crystalline.abelianSheafPushforward`; see the module docstring for why the site is not a
`CategoryTheory.SmallCategory` on the nose and why passing to this model costs nothing. -/
abbrev CompletedSmallSite (s : AffineCrystallineSituation.{u, v}) : Type (max u v (t + 1)) :=
  AsSmall.{0} ((CompletedCrystallineThickening.{u, v, t} s)ᵒᵖ)

variable (s : AffineCrystallineSituation.{u, v})

/-- The small model of the site is the site. -/
def completedSmallSiteEquiv :
    CompletedSmallSite.{u, v, t} s ≌ (CompletedCrystallineThickening.{u, v, t} s)ᵒᵖ :=
  AsSmall.equiv.symm

/-- The opposite of the small model of the site is `Cris^∧(C/A)`, so a presheaf on the small model
is a covariant functor on completed divided power thickenings — which is what a crystalline sheaf
is. -/
def completedSmallSiteOpEquiv :
    (CompletedSmallSite.{u, v, t} s)ᵒᵖ ≌ CompletedCrystallineThickening.{u, v, t} s :=
  (completedSmallSiteEquiv s).op.trans (opOpEquivalence _)

/-- The equivalence `completedSmallSiteOpEquiv` sends the object of the small model represented by
`B` back to `B`. -/
@[simp]
lemma completedSmallSiteOpEquiv_functor_obj_op_up_op
    (B : CompletedCrystallineThickening.{u, v, t} s) :
    (completedSmallSiteOpEquiv s).functor.obj (op (AsSmall.up.obj (op B))) = B :=
  rfl

/-- Abelian sheaves on the small model of `𝒞^∧` are abelian presheaves on `Cris^∧(C/A)`: the
topology is chaotic, so every presheaf is a sheaf. -/
def completedSmallSheafEquivalence :
    Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, t} s)) Ab.{max u v (t + 1)} ≌
      (CompletedCrystallineThickening.{u, v, t} s ⥤ Ab.{max u v (t + 1)}) :=
  (sheafBotEquivalence (C := CompletedSmallSite.{u, v, t} s) Ab.{max u v (t + 1)}).trans
    (Equivalence.congrLeft (completedSmallSiteOpEquiv s))

/-- **The two sheaf topoi agree.**  The chaotic topos of the small model of `𝒞^∧` is the chaotic
topos of `(Cris^∧(C/A))ᵒᵖ`, at the coefficient universe of [Stacks, Tag 07JL].  So the cohomology
computed on the small model is the cohomology of the site of [Stacks, Tag 07JL]. -/
def completedSmallSheafToposEquivalence :
    Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, t} s)) Ab.{max u v (t + 1)} ≌
      Sheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, t} s)ᵒᵖ)
        Ab.{max u v (t + 1)} :=
  (completedSmallSheafEquivalence s).trans (completedAbelianSheafEquivalence.{u, v, t} s).symm

/-- An abelian presheaf on `Cris^∧(C/A)` read as an abelian sheaf on the small model of `𝒞^∧`.
Every presheaf is a sheaf for the chaotic topology, so this is a relabelling; its sections are
computed by `smallSheafOfPresheaf_obj`. -/
def smallSheafOfPresheaf
    (𝓖 : CompletedCrystallineThickening.{u, v, t} s ⥤ Ab.{max u v (t + 1)}) :
    Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, t} s)) Ab.{max u v (t + 1)} :=
  ⟨(completedSmallSiteOpEquiv s).functor ⋙ 𝓖, Presheaf.isSheaf_bot _⟩

/-- The sections of `smallSheafOfPresheaf s 𝓖` over the object of the small model represented by
`B` are `𝓖.obj B`. -/
@[simp]
lemma smallSheafOfPresheaf_obj
    (𝓖 : CompletedCrystallineThickening.{u, v, t} s ⥤ Ab.{max u v (t + 1)})
    (B : CompletedCrystallineThickening.{u, v, t} s) :
    (smallSheafOfPresheaf s 𝓖).obj.obj (op (AsSmall.up.obj (op B))) = 𝓖.obj B :=
  rfl

/-- The abelian sheaves on the small model of `𝒞^∧` have `Ext`-groups in the universe of the site.
This is the `HasExt` hypothesis of [Stacks, Tag 07JM]; it is not registered as an instance, since
`HasExt` instances must be chosen one universe at a time. -/
theorem hasExt_sheaf_completedSmallSite :
    HasExt.{max u v (t + 1)}
      (Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, t} s)) Ab.{max u v (t + 1)}) :=
  hasExt_of_enoughInjectives _

/-- **Products of pairs in `𝒞^∧`**, from coproducts of pairs in `Cris^∧(C/A)`.  Nothing below
needs it: the Čech engine [Stacks, Tag 07JM] asks only for the powers of its covering object, and
those are supplied by [Stacks, Tag 07L4] through `Crystalline.hasProduct_generator`.  This note
previously said the instance was registered so that the products `D × ⋯ × D` of the statements
below would elaborate, and that it was inert because
`HasBinaryCoproducts (CompletedCrystallineThickening s)` is nowhere available; the products now
elaborate from `hasProduct_generator` and no statement below carries the coproducts hypothesis. -/
instance hasBinaryProducts_completedSmallSite
    [HasBinaryCoproducts (CompletedCrystallineThickening.{u, v, t} s)] :
    HasBinaryProducts (CompletedSmallSite.{u, v, t} s) := by
  have h1 : HasColimitsOfShape (Discrete WalkingPair)ᵒᵖ
      (CompletedCrystallineThickening.{u, v, t} s) :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite WalkingPair).symm
  have h2 : HasBinaryProducts (CompletedCrystallineThickening.{u, v, t} s)ᵒᵖ :=
    hasLimitsOfShape_op_of_hasColimitsOfShape
  exact Adjunction.hasLimitsOfShape_of_equivalence (completedSmallSiteEquiv s).functor

/-! ### The generator `D` as a covering object -/

section Generator

variable {ι : Type w} (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- The object of `Cris^∧(C/A)` underlying the realisation
`Crystalline.completedEnvelopeThickening` of [Stacks, Tag 07L4] is the object `D` of
[Stacks, Tag 07KI].  Both are pinned down by the same data — the completed envelope as a divided
power ring, its map from the base, and its map to `C` after the surjection from the presentation
algebra — so they agree. -/
lemma completedEnvelopeThickening_thickening_eq :
    (completedEnvelopeThickening s g hg).thickening
      = (completedPolynomialEnvelopeThickening s g hg).1 := by
  classical
  have hspecY := (completedPolynomialEnvelopeThickening s g hg).2
  generalize hYd : (completedPolynomialEnvelopeThickening s g hg).1 = Y at hspecY ⊢
  clear hYd
  dsimp only at hspecY
  obtain ⟨hp', hr', hb', hq'⟩ := hspecY
  set X := completedEnvelopeThickening s g hg with hXd
  clear_value X
  clear hXd
  obtain ⟨hp, T, hr, pm, hpm, hb, hq⟩ := X
  obtain ⟨TR, Tb, Tc, Tt, Tcomm, Tbij⟩ := T
  obtain ⟨YR, Yb, Yc, Yt, Ycomm, Ybij⟩ := Y
  dsimp only at hr hb hq hr' hb' hq' ⊢
  subst hr hr'
  have hbb : Tb = Yb :=
    DividedPowers.DPMorphism.ext (congrArg DFunLike.coe ((eq_of_heq hb).trans (eq_of_heq hb').symm))
  have htt : Tt = Yt := by
    refine RingHom.ext (hg.forall.mpr fun q => ?_)
    exact (eq_of_heq (hq q)).trans (RingHom.congr_fun (eq_of_heq hq') q).symm
  subst hbb htt
  rfl

/-- **[Stacks, Tag 07KI] for the realisation of `D` used by [Stacks, Tag 07L4].**  Every completed
divided power thickening of `C` over `A` receives a morphism from `D`. -/
theorem nonempty_hom_from_completedEnvelopeThickening
    (B : CompletedCrystallineThickening.{u, v, max u w} s) :
    Nonempty ((completedEnvelopeThickening s g hg).thickening ⟶ B) := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_hom_from_completedPolynomialEnvelope s g hg B
  rw [completedEnvelopeThickening_thickening_eq s g hg]
  exact ⟨{ hom := q, fromBase_comp := hq₁, toQuotient_comp := hq₂ }⟩

/-- **The generator `D` of [Stacks, Tag 07KI] as an object of the site `𝒞^∧`.** -/
def generator : CompletedSmallSite.{u, v, max u w} s :=
  AsSmall.up.obj (op (completedEnvelopeThickening s g hg).thickening)

/-- The object of `(Cris^∧(C/A))ᵒᵖ` underlying `generator s g hg` is the opposite of the
thickening of `completedEnvelopeThickening s g hg`. -/
@[simp]
lemma generator_down :
    ULift.down (generator s g hg) = op (completedEnvelopeThickening s g hg).thickening :=
  rfl

/-- **`D` is a covering object of `𝒞^∧`**: every object of the site admits a morphism to it.  This
is the hypothesis of [Stacks, Tag 07JM], and it holds by [Stacks, Tag 07KI] — in the site the
arrows are reversed, so a morphism `U ⟶ D` of `𝒞^∧` is a divided power map out of `D`. -/
theorem nonempty_hom_to_generator (U : CompletedSmallSite.{u, v, max u w} s) :
    Nonempty (U ⟶ generator s g hg) := by
  obtain ⟨k⟩ :=
    nonempty_hom_from_completedEnvelopeThickening s g hg (ULift.down U).unop
  exact ⟨⟨k.op⟩⟩

/-! ### `D(n)` is the `(n + 1)`-fold power of `D` in the site -/

/-- The fan of the `n + 1` canonical morphisms `D(n) ⟶ D` of the site `𝒞^∧`, that is, of the
`n + 1` coprojections `D → D(n)` of [Stacks, Tag 07L4]. -/
def generatorPowerFan (n : ℕ) : Fan (fun _ : Fin (n + 1) => generator s g hg) :=
  Fan.mk (AsSmall.up.obj (op (tensorPowerEnvelopeThickening s g hg n).thickening))
    (fun j => ULift.up (completedEnvelopeCoprojection s g hg n j).op)

/-- **[Stacks, Tag 07L4] in the site `𝒞^∧`**: `D(n)` is the `(n + 1)`-fold power of `D`, the
coprojections of the coproduct `D(n) = ∐_{j = 0, …, n} D` of `Cris^∧(C/A)` being its projections.
This is the case of the products hypothesis of [Stacks, Tag 07JM] that the source's proof of
[Stacks, Tag 07JN] actually checks, and — the engine having been weakened to ask for exactly
that case — it is the whole of it; it needs no coproducts beyond those of [Stacks, Tag 07L4]. -/
def isLimitGeneratorPowerFan (n : ℕ) : IsLimit (generatorPowerFan s g hg n) := by
  classical
  let hc := (completedEnvelope_isCoproduct s g hg n).some
  refine Fan.IsLimit.mk _
    (fun S => ULift.up (Quiver.Hom.op
      (hc.desc (Cofan.mk (ULift.down S.pt).unop
        (fun j => (ULift.down (S.proj j)).unop))))) ?_ ?_
  · intro S j
    refine congrArg ULift.up ?_
    apply Quiver.Hom.unop_inj
    exact hc.fac (Cofan.mk (ULift.down S.pt).unop
      (fun j => (ULift.down (S.proj j)).unop)) ⟨j⟩
  · intro S m hm
    refine congrArg ULift.up ?_
    apply Quiver.Hom.unop_inj
    refine hc.uniq (Cofan.mk (ULift.down S.pt).unop
      (fun j => (ULift.down (S.proj j)).unop)) (ULift.down m).unop ?_
    rintro ⟨j⟩
    exact congrArg (fun h => (ULift.down h).unop) (hm j)

/-- **The nonempty finite powers of the generator exist in `𝒞^∧`.**  This is the products
hypothesis of [Stacks, Tag 07JM] in the shape that engine consumes, and
`Crystalline.isLimitGeneratorPowerFan` — that is, [Stacks, Tag 07L4] — supplies it outright: the
power `D^{n + 1}` is the object `D(n)`.  Only coproducts of copies of the single object `D` are
involved, so no hypothesis about coproducts of arbitrary pairs of objects of `Cris^∧(C/A)` is
needed. -/
instance hasProduct_generator (n : ℕ) :
    HasProduct (fun _ : Fin (n + 1) => generator s g hg) :=
  HasLimit.mk ⟨generatorPowerFan s g hg n, isLimitGeneratorPowerFan s g hg n⟩

/-! ### The Čech engine on the completed site -/

section Cech

/-- **The comparison of [Stacks, Tag 07JM] on the completed affine crystalline site, named.**
The isomorphism of `H^n(𝒞^∧, 𝓖)` with the degree-`n` cohomology of the Čech complex of the
generator `D` of [Stacks, Tag 07KI], as a `def`.

It is `Stacks.Cohomology.addEquivSheafHHomologyPowerCechComplex` at the covering object `D`, the
hypotheses of [Stacks, Tag 07JM] being discharged by `nonempty_hom_to_generator` and
`hasProduct_generator`.  The existence statement is
`nonempty_addEquiv_sheafH_homology_powerCechComplex_generator` below. -/
def addEquivSheafHHomologyPowerCechComplexGenerator
    (𝓖 : Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, max u w} s))
      Ab.{max u v (max u w + 1)}) (n : ℕ) :
    Sheaf.H 𝓖 n ≃+
      (Stacks.Cohomology.powerCechComplex 𝓖.obj (generator s g hg)).homology n :=
  have := hasExt_sheaf_completedSmallSite.{u, v, max u w} s
  Stacks.Cohomology.addEquivSheafHHomologyPowerCechComplex
    (generator s g hg) (nonempty_hom_to_generator s g hg) 𝓖 n

/-- **[Stacks, Tag 07JM] on the completed affine crystalline site.**  For every abelian sheaf `𝓖`
on `𝒞^∧ = (Cris^∧(C/A))ᵒᵖ` with the chaotic topology, the cohomology `H^n(𝒞^∧, 𝓖)` is the
degree-`n` cohomology of the complex

`𝓖(D) → 𝓖(D × D) → 𝓖(D × D × D) → ⋯`

of the values of `𝓖` on the powers of the generator `D` of [Stacks, Tag 07KI].  The hypotheses of
[Stacks, Tag 07JM] are discharged by `nonempty_hom_to_generator` ([Stacks, Tag 07KI]) and by
`hasProduct_generator` ([Stacks, Tag 07L4]), so there is no hypothesis beyond the ambient affine
crystalline situation; the powers are the objects `D(n)`, which is the content of
`powerCechComplexXIsoTensorPowerEnvelope`.

The comparison is named: it is `addEquivSheafHHomologyPowerCechComplexGenerator` below. -/
theorem nonempty_addEquiv_sheafH_homology_powerCechComplex_generator
    (𝓖 : Sheaf (⊥ : GrothendieckTopology (CompletedSmallSite.{u, v, max u w} s))
      Ab.{max u v (max u w + 1)}) (n : ℕ) :
    Nonempty (Sheaf.H 𝓖 n ≃+
      (Stacks.Cohomology.powerCechComplex 𝓖.obj (generator s g hg)).homology n) :=
  ⟨addEquivSheafHHomologyPowerCechComplexGenerator s g hg 𝓖 n⟩

/-- The `(n + 1)`-fold power of `D` in the site `𝒞^∧` is `D(n)`. -/
def generatorPowerIso (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => generator s g hg) ≅
      AsSmall.up.obj (op (tensorPowerEnvelopeThickening s g hg n).thickening) :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitGeneratorPowerFan s g hg n)

/-- **The degree-`n` term of the Čech complex of `D` is `𝓖(D(n))`.**  The complex of
[Stacks, Tag 07JM] has `𝓖(D^{n + 1})` in degree `n`, and `D^{n + 1} = D(n)` by
[Stacks, Tag 07L4]. -/
def powerCechComplexXIsoTensorPowerEnvelope
    (𝓖 : (CompletedSmallSite.{u, v, max u w} s)ᵒᵖ ⥤ Ab.{max u v (max u w + 1)}) (n : ℕ) :
    (Stacks.Cohomology.powerCechComplex 𝓖 (generator s g hg)).X n ≅
      𝓖.obj (op (AsSmall.up.obj (op (tensorPowerEnvelopeThickening s g hg n).thickening))) :=
  (𝓖.mapIso (generatorPowerIso s g hg n).op).symm

/-- The degree-`n` term of the Čech complex of `D`, for a sheaf coming from an abelian presheaf
`𝓖` on `Cris^∧(C/A)`, is `𝓖(D(n))`. -/
def powerCechComplexXIsoSections
    (𝓖 : CompletedCrystallineThickening.{u, v, max u w} s ⥤ Ab.{max u v (max u w + 1)}) (n : ℕ) :
    (Stacks.Cohomology.powerCechComplex (smallSheafOfPresheaf s 𝓖).obj
        (generator s g hg)).X n ≅
      𝓖.obj (tensorPowerEnvelopeThickening s g hg n).thickening :=
  powerCechComplexXIsoTensorPowerEnvelope s g hg (smallSheafOfPresheaf s 𝓖).obj n

/-! ### Descent along the morphism of topoi of Stacks 07JL -/

/-- **The Čech engine descended along [Stacks, Tag 07JL].**  Let `𝓕` be an abelian presheaf on
`Cris(C/A)`, that is, an abelian sheaf on `𝒞 = (Cris(C/A))ᵒᵖ` for the chaotic topology, and let
`g_* 𝓕 = Crystalline.abelianDirectImage` be the direct image of the morphism of topoi
`g : Sh(𝒞) → Sh(𝒞^∧)` of [Stacks, Tag 07JL] — identified with the direct image of that morphism of
topoi by `Crystalline.abelianSheafPushforwardIsoDirectImage`.  Then for every `n` the cohomology
`H^n(𝒞^∧, g_* 𝓕)` is the degree-`n` cohomology of the complex

`(g_* 𝓕)(D) → (g_* 𝓕)(D(1)) → (g_* 𝓕)(D(2)) → ⋯`,

whose degree-`n` term is `(g_* 𝓕)(D(n))` by `powerCechComplex_X_eq_tensorPowerEnvelope`.

This is the step of [Stacks, Tag 07JN] that does not use the vanishing `R^p g_* 𝓕 = 0`: composing
it with that vanishing — through the Leray comparison `H^j(𝒞, 𝓕) ≅ H^j(𝒞^∧, g_* 𝓕)` — is what
yields [Stacks, Tag 07JN].  See the module docstring. -/
theorem nonempty_addEquiv_sheafH_homology_powerCechComplex_directImage
    (𝓕 : CrystallineThickening.{u, v, max u w} s ⥤ Ab.{max u v (max u w + 1)}) (n : ℕ) :
    Nonempty (Sheaf.H (smallSheafOfPresheaf s ((abelianDirectImage s).obj 𝓕)) n ≃+
      (Stacks.Cohomology.powerCechComplex
        (smallSheafOfPresheaf s ((abelianDirectImage s).obj 𝓕)).obj
        (generator s g hg)).homology n) :=
  nonempty_addEquiv_sheafH_homology_powerCechComplex_generator s g hg _ n

end Cech

end Generator

/-! ### The interface to the vanishing `R^p g_* = 0`

The three hypotheses that `Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso` — the Leray
degeneration in the range `1 ≤ q ≤ j` — asks of the functor it derives.  Supplying them for the
direct image of [Stacks, Tag 07JL] is what lets the vanishing `R^p g_* 𝓕 = 0` be fed into that
comparison; additivity is already
`Crystalline.abelianSheafPushforward_additive`. -/

/-- The direct image of [Stacks, Tag 07JL] on abelian sheaves is a right adjoint, its left adjoint
being the inverse image of the same morphism of topoi. -/
instance abelianSheafPushforward_isRightAdjoint :
    (abelianSheafPushforward.{u, v, t} s).IsRightAdjoint :=
  ⟨⟨_, ⟨(crystallineToCompleted s).op.sheafAdjunctionCocontinuous
    Ab.{max u v (t + 1)} ⊥ ⊥⟩⟩⟩

/-- The direct image of [Stacks, Tag 07JL] is left exact: it is a right adjoint. -/
instance preservesFiniteLimits_abelianSheafPushforward :
    PreservesFiniteLimits (abelianSheafPushforward.{u, v, t} s) :=
  inferInstance

/-- **The direct image of [Stacks, Tag 07JL] preserves injective abelian sheaves.**  Its left
adjoint is the inverse image of the same morphism of topoi, which preserves monomorphisms. -/
instance preservesInjectiveObjects_abelianSheafPushforward :
    (abelianSheafPushforward.{u, v, t} s).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((crystallineToCompleted s).op.sheafAdjunctionCocontinuous Ab.{max u v (t + 1)} ⊥ ⊥)

end Crystalline

end

end
