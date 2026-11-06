module

public import StacksCore.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Monomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFromThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.RingTheory.Nilpotent.Descent

/-!
# Monomorphisms through which the reduction of the target factors

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` which is representable by algebraic spaces and a monomorphism, and
through which the inclusion of a reduction of `Y` factors. Stacks 0GHZ says that `f` is a closed
immersion as soon as `f` is locally of finite type or `Y` is locally Noetherian.

## Main definitions

* `AlgebraicGeometry.FormalSpace.Is07VT`: the conclusion of **Stacks 07VT** — an algebraic space
  over `S` receiving a surjective universally closed morphism from an affine scheme of the site
  is an affine scheme — which is granted as a hypothesis below.
* `AlgebraicGeometry.FormalSpace.HasNoetherianAffineSchemeCover`: a family of scheme-valued
  points with Noetherian affine sources whose induced map from the coproduct is a surjection of
  sheaves.

## Main results

* `AlgebraicGeometry.FormalSpace.surjective_algebraMap_of_isLocallyNilpotent`: **Stacks 07RD**
  and **Stacks 00DV (11)** combined — a ring map which is surjective modulo a locally nilpotent
  ideal of the source is surjective when the target is of finite type or the source is
  Noetherian.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_isPullback_of_isThickening`: the affine
  case — a morphism of affine schemes whose base change along a thickening of the target is an
  isomorphism is a closed immersion, under the same finiteness alternative.
* `AlgebraicGeometry.FormalSpace.Space.isClosedImmersion_of_mono_of_thickening_factors` and its
  Noetherian counterpart
  `…Space.isClosedImmersion_of_mono_of_thickening_factors_of_isNoetherianRing`: the two cases
  for a monomorphism of algebraic spaces over `S` to a scheme of the site through which a
  thickening of that scheme factors.
* `AlgebraicGeometry.FormalSpace.hasNoetherianAffineSchemeCover_of_isLocallyNoetherian`:
  **Stacks 0AKM** with **Stacks 0AI7** — a locally Noetherian formal algebraic space over `S` is
  covered by Noetherian affine schemes of the site.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_mono_of_isLocallyOfFiniteType`:
  **Stacks 0GHZ** in the locally-of-finite-type case, with nothing granted.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_pullback_snd_of_isReduction'`: the key step
  at one scheme-valued point of the target; the unprimed form additionally assumes
  `AlgebraicGeometry.FormalSpace.Is07VT` in the Noetherian alternative.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_mono_of_reduction_factors`:
  **Stacks 0GHZ**.

## Implementation notes

The reduction, its inclusion and the factorisation of the inclusion through `f` are
hypotheses rather than consequences of a chosen reduction; this is the shape Stacks 0GB8
already takes in `StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction`, it is more general
than the statement about a chosen reduction, and it needs no choice. Such a reduction always
exists, by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`. For the same
reason the statements below do not use witnesses that `X` and `Y` are formal algebraic spaces
and are stated for arbitrary morphisms of fppf sheaves, as the conditions of Stacks 03XZ they
are built from are.

Both cases of the finiteness alternative go through the base change of `f` along a scheme-valued
point `T ⟶ Y` of the target. Monomorphy of `f` makes that base change `V ⟶ T` a monomorphism,
and the factorisation of the reduction base-changes to a morphism from the base change of the
reduction — a thickening of `T` — into `V`. Being the base change of a morphism representable by
algebraic spaces, `V` is an algebraic space over `S` with values in `Type (u + 1)`, hence
isomorphic to the universe lift of an algebraic space over `S` in the value universe of the
site; the whole situation therefore transports to that universe, where the sorites of
`StacksDraft.AlgebraicGeometry.Spaces` are available, and the conclusion transports back because
being represented by a closed immersion of the site is invariant under the universe lift.

In the value universe the thickening is finite, hence universally closed, and surjective; the
monomorphism `V ⟶ T` is therefore universally closed by Stacks 08AJ. If `f` is locally of finite
type, so is `V ⟶ T`, and Stacks 05W8 identifies a universally closed monomorphism locally of
finite type with a closed immersion; the scheme-valued points are then assembled by Stacks 0GHY.
If instead `Y` is only locally Noetherian the scheme-valued points have to be restricted, since
the condition defining a closed immersion quantifies over all of them and the ring-level
statement is false without a finiteness hypothesis (Stacks 06RH). They are restricted to the
Noetherian affine schemes of the site, which cover `Y` by Stacks 0AKM, and the restriction is
undone by the descent step of Stacks 0GHY. Over such a point `V ⟶ T` is again locally of finite
type, so the same criterion applies: monomorphy cuts the thickening of `T` out of `V` by a
cartesian square, a thickening of a Noetherian affine scheme is of finite order, and Stacks 09ZW
carries local finite type across a cartesian morphism of thickenings whose base thickening is of
finite order. That step is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_mono_of_thickening_factors_of_isNoetherianRing`,
in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFromThickening`.

Stacks 0GHZ itself grants nothing. The source proof of the Noetherian case runs the other way:
it makes `V` an affine scheme by Stacks 07VT and then reads the surjectivity of its ring map off
Stacks 07RD and Stacks 00DV (11). That route is unavailable here, because the library's 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`, is itself stated
with three granted hypotheses and proving it outright calls for Stacks 09YA, 07SQ, 07VS, 05ZH
and 05W5, none of which this library carries; Stacks 09YA has no carrier at all. It is recorded
below all the same: `AlgebraicGeometry.FormalSpace.Is07VT`, together with the two declarations
that take it as a hypothesis —
`…Space.isClosedImmersion_of_mono_of_thickening_factors_of_isNoetherianRing` and
`…isClosedImmersion_pullback_snd_of_isReduction` — spells out the source's argument, and the
second of those is deduced from its primed form, which does without the hypothesis. So is the
ring-level half, `…isClosedImmersion_of_isPullback_of_isThickening`, which is the affine case of
the tag and needs nothing beyond the finiteness alternative.

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 06RH](https://stacks.math.columbia.edu/tag/06RH)
* [Stacks Project, Tag 07RD](https://stacks.math.columbia.edu/tag/07RD)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
* [Stacks Project, Tag 0GHZ](https://stacks.math.columbia.edu/tag/0GHZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The ring-theoretic core -/

/-- **Stacks 07RD and Stacks 00DV (11), combined.** Let `A` be an algebra over a commutative
ring `R` and let `J ⊆ R` be a locally nilpotent ideal with `R ⟶ A/JA` surjective. If `A` is of
finite type over `R`, or `R` is Noetherian, then `R ⟶ A` is surjective. -/
theorem surjective_algebraMap_of_isLocallyNilpotent {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    (hquot : Function.Surjective
      ((Ideal.Quotient.mk (J.map (algebraMap R A))).comp (algebraMap R A)))
    (hfin : Algebra.FiniteType R A ∨ IsNoetherianRing R) :
    Function.Surjective (algebraMap R A) := by
  rcases hfin with hft | hnoeth
  · exact surjective_of_surjective_mod_locallyNilpotent J hJ (Algebra.ofId R A) hquot hft
  · have hJnil : IsNilpotent J := by
      obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical R
      refine ⟨n, le_bot_iff.mp ?_⟩
      calc J ^ n ≤ nilradical R ^ n := by
            gcongr
            exact fun x hx ↦ mem_nilradical.mpr (hJ x hx)
        _ = ⊥ := by simpa using hn
    refine LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent J
      (Algebra.linearMap R A) hJnil ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R A)) y
    obtain ⟨r, hr⟩ := hquot (Ideal.Quotient.mk (J.map (algebraMap R A)) a)
    refine ⟨r, ?_⟩
    have hmem : algebraMap R A r - a ∈ J.map (algebraMap R A) := Ideal.Quotient.eq.mp hr
    show Submodule.Quotient.mk (algebraMap R A r) = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq, Ideal.smul_top_eq_map]
    exact hmem

/-! ### The closed immersion criterion for algebraic spaces -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a thickening `m : b ⟶ T` factors through a monomorphism `a` via `c`, then `yoneda.map m` is
universally closed and `c` is surjective. -/
private theorem universallyClosed_and_isSurjective_of_thickening_factors
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T b : BigFppfOver B S hS} (a : F ⟶ yoneda.obj T)
    (hmono : Mono a) (m : b ⟶ T)
    (hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m))
    (c : yoneda.obj b ⟶ F) (hc : c ≫ a = yoneda.map m) :
    Space.UniversallyClosed B S hS (yoneda.map m) ∧ Space.IsSurjective B S hS c := by
  have hb : IsAlgebraicSpace B S hS (yoneda.obj b) := isAlgebraicSpace_yoneda B S hS b
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hmCI : Space.IsClosedImmersion B S hS (yoneda.map m) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) m).2 hm.1
  have hmSurj : Space.IsSurjective B S hS (yoneda.map m) :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj T) hT b
      (yoneda.map m)).1
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Surjective.{u}) m).2 ⟨hm.2⟩)
  refine ⟨Space.universallyClosed_of_isFinite B S hS hb hT
    (Space.isFinite_of_isClosedImmersion B S hS _ hmCI), fun z ↦ ?_⟩
  have hainj : Function.Injective (Space.pointsMap B S hS F a) :=
    Space.pointsMap_injective_of_mono B S hS a
  obtain ⟨x, hx⟩ := hmSurj (Space.pointsMap B S hS F a z)
  refine ⟨x, hainj ?_⟩
  have hcomp := congrFun (Space.pointsMap_comp B S hS (F := yoneda.obj b) c a) x
  simp only [Function.comp_apply] at hcomp
  rw [← hcomp, hc, hx]

/-- A monomorphism of algebraic spaces over `S` to a scheme of the site, locally of finite
type, through which a thickening of that scheme factors, is a closed immersion.

The thickening is universally closed and surjects onto its image, so the monomorphism is
universally closed by Stacks 08AJ; a universally closed monomorphism locally of finite type is
a closed immersion by Stacks 05W8. -/
theorem Space.isClosedImmersion_of_mono_of_thickening_factors
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T b : BigFppfOver B S hS} (a : F ⟶ yoneda.obj T) (hmono : Mono a) (m : b ⟶ T)
    (hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m))
    (c : yoneda.obj b ⟶ F) (hc : c ≫ a = yoneda.map m)
    (hft : Space.IsLocallyOfFiniteType B S hS a) :
    Space.IsClosedImmersion B S hS a := by
  have : Mono a := hmono
  have hb : IsAlgebraicSpace B S hS (yoneda.obj b) := isAlgebraicSpace_yoneda B S hS b
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  obtain ⟨hmUC, hcSurj⟩ :=
    universallyClosed_and_isSurjective_of_thickening_factors B S hS a hmono m hm c hc
  have haUC : Space.UniversallyClosed B S hS a :=
    Space.universallyClosed_of_isSurjective_comp B S hS hb hF hT c a (hc ▸ hmUC) hcSurj
  have hcond : Space.UniversallyClosed B S hS a ∧
      (Space.IsLocallyOfFiniteType B S hS a ∧ Mono a) := ⟨haUC, hft, hmono⟩
  exact ((Space.closedImmersion_conditions_tfae B S hS hF hT a).out 4 1).mp hcond

/-! ### Transfer between the two value universes -/

/-- Being represented by a closed immersion of the site is unchanged by the universe lift. -/
private theorem relative_isClosedImmersion_map_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
        ((uliftPresheaf B S hS).map a) ↔
      Space.IsClosedImmersion B S hS a :=
  Space.relative_comp_map_iff yoneda (uliftPresheaf B S hS) _ a

/-- A morphism of fppf sheaves on the big fppf site of `S` whose represented base changes are
closed immersions of the site is a closed immersion of formal algebraic spaces: the represented
base changes are algebraic spaces because they are represented, and the closed-immersion
condition is stable under base change. -/
private theorem isClosedImmersion_of_relative {V W : FppfSheaf B S hS} (p : V ⟶ W)
    (hp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) p.hom) :
    IsClosedImmersion B S hS p := by
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom := by
    intro U ξ
    obtain ⟨V', s, q, hpb⟩ := hp.rep ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hpb.flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V')
  refine ⟨hrep, fun U ξ ↦ ?_⟩
  have hstable := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  exact hstable.of_isPullback (IsPullback.of_hasPullback ξ p.hom).flip hp

/-- A monomorphism of fppf sheaves on the big fppf site of `S` is a monomorphism of the
underlying presheaves: a section over an object of the site is a morphism out of the sheaf
represented by that object, so injectivity on sections follows from cancelling the
monomorphism. -/
private theorem mono_hom_of_mono {V W : FppfSheaf B S hS} (p : V ⟶ W) (hp : Mono p) :
    Mono p.hom := by
  have : Mono p := hp
  have happ : ∀ U : (BigFppfOver B S hS)ᵒᵖ, Function.Injective (p.hom.app U) := by
    intro U x y hxy
    have hx : (⟨uliftYonedaEquiv.{u + 1}.symm x⟩ : yonedaSheaf B S hS U.unop ⟶ V) ≫ p =
        (⟨uliftYonedaEquiv.{u + 1}.symm y⟩ : yonedaSheaf B S hS U.unop ⟶ V) ≫ p := by
      refine Sheaf.hom_ext ?_
      show uliftYonedaEquiv.{u + 1}.symm x ≫ p.hom =
        uliftYonedaEquiv.{u + 1}.symm y ≫ p.hom
      rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
      exact congrArg uliftYonedaEquiv.{u + 1}.symm hxy
    have h := (cancel_mono p).mp hx
    have h' : uliftYonedaEquiv.{u + 1}.symm x = uliftYonedaEquiv.{u + 1}.symm y :=
      congrArg (fun m : yonedaSheaf B S hS U.unop ⟶ V ↦ m.hom) h
    exact uliftYonedaEquiv.{u + 1}.symm.injective h'
  have : ∀ U : (BigFppfOver B S hS)ᵒᵖ, Mono (p.hom.app U) := fun U ↦
    (mono_iff_injective _).mpr (happ U)
  exact NatTrans.mono_of_mono_app p.hom

/-! ### The criterion at a scheme-valued point of the target -/

/-- The relative closed-immersion property of the big fppf site of `S` respects isomorphisms,
being stable under base change. -/
private theorem respectsIso_relative_isClosedImmersion :
    ((MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})).RespectsIso :=
  (MorphismProperty.relative_isStableUnderBaseChange _ (F := uliftYoneda.{u + 1})).respectsIso

/-! ### The affine case -/

/-- A closed immersion into an affine scheme which is surjective on points is cut out by a
locally nilpotent ideal: its support is everything, so its kernel lies in the nilradical. -/
private theorem isLocallyNilpotent_ker_appTop {X Z : Scheme.{u}} [IsAffine Z] (i : X ⟶ Z)
    [AlgebraicGeometry.IsClosedImmersion i] (hi : Function.Surjective i.base) :
    Ideal.IsLocallyNilpotent (RingHom.ker i.appTop.hom) := by
  classical
  have hsupport : (i.ker.support : Set Z) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hi, closure_univ]
  rw [Scheme.ker_of_isAffine i] at hsupport
  have hker : (RingHom.ker i.appTop.hom : Set Γ(Z, ⊤)) ⊆ nilradical Γ(Z, ⊤) := by
    rw [← Scheme.zeroLocus_eq_univ_iff_subset_nilradical]
    simpa using hsupport
  intro a ha
  have ha' : a ∈ (⊥ : Ideal Γ(Z, ⊤)).radical := by
    simpa [nilradical] using hker ha
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha'
  exact ⟨n, by simpa using hn⟩

/-- **The affine case of Stacks 0GHZ.** A morphism `g : X ⟶ Z` of affine schemes whose base
change along a thickening `i : W ⟶ Z` of its target is an isomorphism is a closed immersion,
provided it is locally of finite type or the ring of `Z` is Noetherian.

The cartesian square becomes a pushout of global sections, which identifies `Γ(X)/JΓ(X)` with
`Γ(W) = Γ(Z)/J` for `J` the locally nilpotent ideal of the thickening; so `Γ(Z) ⟶ Γ(X)` is
surjective modulo `J`, and
`AlgebraicGeometry.FormalSpace.surjective_algebraMap_of_isLocallyNilpotent` applies. -/
theorem isClosedImmersion_of_isPullback_of_isThickening {X Z W : Scheme.{u}} [IsAffine X]
    [IsAffine Z] {g : X ⟶ Z} {i : W ⟶ Z} {j : W ⟶ X}
    (hi : Stacks.Thickenings.IsThickening i) (hsq : IsPullback j (𝟙 W) g i)
    (hfin : AlgebraicGeometry.LocallyOfFiniteType g ∨ IsNoetherianRing Γ(Z, ⊤)) :
    AlgebraicGeometry.IsClosedImmersion g := by
  classical
  have hiCI : AlgebraicGeometry.IsClosedImmersion i := hi.1
  have hWaff : IsAffine W := isAffine_of_isAffineHom i
  have hχ : Function.Surjective i.appTop.hom :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hpo : IsPushout g.appTop i.appTop j.appTop (𝟙 Γ(W, ⊤)) := by
    simpa using isPushout_appTop_of_isPullback hsq
  let : Algebra Γ(Z, ⊤) Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have halg : (algebraMap Γ(Z, ⊤) Γ(X, ⊤)) = g.appTop.hom := rfl
  set J : Ideal Γ(Z, ⊤) := RingHom.ker i.appTop.hom with hJ
  have hJnil : J.IsLocallyNilpotent := isLocallyNilpotent_ker_appTop i hi.2
  set JA : Ideal Γ(X, ⊤) := J.map (algebraMap Γ(Z, ⊤) Γ(X, ⊤)) with hJA
  set D : CommRingCat.{u} := CommRingCat.of (Γ(X, ⊤) ⧸ JA) with hD
  set α : Γ(X, ⊤) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.mk JA) with hα
  have hkerle : J ≤ RingHom.ker (g.appTop ≫ α).hom := by
    intro x hx
    have hmem : (algebraMap Γ(Z, ⊤) Γ(X, ⊤)) x ∈ JA := Ideal.mem_map_of_mem _ hx
    simpa [hα, RingHom.mem_ker, halg] using (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  set β : Γ(W, ⊤) ⟶ D := CommRingCat.ofHom
    ((Ideal.Quotient.lift J (g.appTop ≫ α).hom hkerle).comp
      (RingHom.quotientKerEquivOfSurjective hχ).symm.toRingHom) with hβ
  have hw : g.appTop ≫ α = i.appTop ≫ β := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    have h1 : (RingHom.quotientKerEquivOfSurjective hχ).symm (i.appTop.hom r) =
        Ideal.Quotient.mk J r :=
      RingHom.quotientKerEquivOfSurjective_symm_apply hχ r
    simp [hβ, h1]
  have hd : hpo.desc α β hw = β := by
    have h := hpo.inr_desc α β hw
    rwa [Category.id_comp] at h
  have hfac : j.appTop ≫ β = α := by
    have h := hpo.inl_desc α β hw
    rwa [hd] at h
  have hquot : Function.Surjective
      ((Ideal.Quotient.mk JA).comp (algebraMap Γ(Z, ⊤) Γ(X, ⊤))) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hχ (j.appTop.hom a)
    refine ⟨r, ?_⟩
    have h1 : α.hom a = β.hom (j.appTop.hom a) :=
      (congrArg (fun k : Γ(X, ⊤) ⟶ D ↦ k.hom a) hfac).symm
    have h2 : (g.appTop ≫ α).hom r = β.hom (i.appTop.hom r) :=
      congrArg (fun k : Γ(Z, ⊤) ⟶ D ↦ k.hom r) hw
    have h3 : α.hom (g.appTop.hom r) = α.hom a := by rw [h1, ← hr, ← h2]; rfl
    simpa [hα, halg] using h3
  have hsurjφ : Function.Surjective (algebraMap Γ(Z, ⊤) Γ(X, ⊤)) := by
    refine surjective_algebraMap_of_isLocallyNilpotent J hJnil hquot ?_
    rcases hfin with h | h
    · exact Or.inl ((HasRingHomProperty.iff_of_isAffine
        (P := @AlgebraicGeometry.LocallyOfFiniteType)).mp h)
    · exact Or.inr h
  exact AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine g hsurjφ

/-! ### The Noetherian case at the level of algebraic spaces -/

/-- **Stacks 07VT**, in the form in which it is used below and which this library does not
prove: an algebraic space over `S` receiving a surjective universally closed morphism from an
affine scheme of the site is an affine scheme. -/
abbrev Is07VT : Prop :=
  ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (c : yoneda.obj T ⟶ F),
    IsAlgebraicSpace B S hS F → IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    Space.IsSurjective B S hS c → Space.UniversallyClosed B S hS c →
    Space.IsAffineSpace B S hS F

/-- A monomorphism of algebraic spaces over `S` to a Noetherian affine scheme of the site
through which a thickening of that scheme factors is a closed immersion.

The thickening is surjective and universally closed and the monomorphism is separated, so the
morphism from the thickening to the source is surjective and universally closed; hence the
source is an affine scheme by Stacks 07VT, and the morphism is a closed immersion of affine
schemes by `isClosedImmersion_of_isPullback_of_isThickening`. -/
theorem Space.isClosedImmersion_of_mono_of_thickening_factors_of_isNoetherianRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T b : BigFppfOver B S hS} (a : F ⟶ yoneda.obj T) (hmono : Mono a)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTN : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (m : b ⟶ T)
    (hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m))
    (c : yoneda.obj b ⟶ F) (hc : c ≫ a = yoneda.map m) (h07VT : Is07VT B S hS) :
    Space.IsClosedImmersion B S hS a := by
  have : Mono a := hmono
  have hb : IsAlgebraicSpace B S hS (yoneda.obj b) := isAlgebraicSpace_yoneda B S hS b
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  obtain ⟨hmUC, hcSurj⟩ :=
    universallyClosed_and_isSurjective_of_thickening_factors B S hS a hmono m hm c hc
  have hcUC : Space.UniversallyClosed B S hS c :=
    Space.universallyClosed_of_comp_of_isSeparated B S hS hb hF hT c a (hc ▸ hmUC)
      (Space.isSeparated_of_mono B S hS a hmono)
  have hbaff : IsAffine ((BigFppfOver.toScheme B S hS).obj b) := by
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) := hm.1
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map m)
  obtain ⟨T', hT'aff, ⟨eF⟩⟩ := h07VT c hF hbaff hcSurj hcUC
  obtain ⟨q, hq⟩ := yoneda.map_surjective (eF.inv ≫ a)
  obtain ⟨c', hc'⟩ := yoneda.map_surjective (c ≫ eF.hom)
  have hfac : c' ≫ q = m := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hc', hq]
    refine Eq.trans (Category.assoc c eF.hom (eF.inv ≫ a)) (Eq.trans ?_ hc)
    exact congrArg (fun k : F ⟶ yoneda.obj T ↦ c ≫ k) (Iso.hom_inv_id_assoc eF a)
  have hmonoq : Mono q := by
    refine yoneda.mono_of_mono_map (f := q) ?_
    rw [hq]
    have heF : Mono eF.inv :=
      ⟨fun g h w ↦ by
        have w' := congrArg (· ≫ eF.hom) w
        rwa [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Category.comp_id] at w'⟩
    exact CategoryTheory.mono_comp' heF hmono
  have hcart : IsPullback c' (𝟙 b) q m := by
    have hwq : c' ≫ q = (𝟙 b) ≫ m := by rw [Category.id_comp]; exact hfac
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hwq (fun s ↦ s.snd) ?_ ?_ ?_)
    · intro s
      refine (cancel_mono q).mp ?_
      rw [Category.assoc, hfac, s.condition]
    · intro s
      exact Category.comp_id _
    · intro s n hn₁ hn₂
      simpa using hn₂
  have hpb := hcart.map (BigFppfOver.toScheme B S hS)
  rw [CategoryTheory.Functor.map_id] at hpb
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'aff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  have hqCI : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) :=
    isClosedImmersion_of_isPullback_of_isThickening hm hpb (Or.inr hTN)
  have hyq : Space.IsClosedImmersion B S hS (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) q).2 hqCI
  rw [hq] at hyq
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _ (F := yoneda)).respectsIso
  exact ((MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).cancel_left_of_respectsIso eF.inv a).mp hyq

/-! ### The criterion at a scheme-valued point of the target -/

/-- **The key step of Stacks 0GHZ.** Let `f : X ⟶ Y` be a monomorphism of fppf sheaves on the
big fppf site of `S` which is representable by algebraic spaces, let `iY : Yred ⟶ Y` be a
reduction of `Y` and suppose `iY` factors through `f`. If `f` is locally of finite type, or the
scheme-valued point is a Noetherian affine scheme, then the base change of `f` along that point
is a closed immersion.

The base change `V = X ×_Y T` receives the base change `Yred ×_Y T` of the reduction, which is a
thickening of `T`; so `V ⟶ T` is a monomorphism of algebraic spaces over `S`, locally of finite
type, through which a thickening of `T` factors, and
`AlgebraicGeometry.FormalSpace.Space.isClosedImmersion_of_mono_of_thickening_factors` applies in
the value universe of the site; if instead `T` is a Noetherian affine scheme, the thickening is
of finite order and Stacks 09ZW supplies the same local finite type.

This is `AlgebraicGeometry.FormalSpace.isClosedImmersion_pullback_snd_of_isReduction` with
`AlgebraicGeometry.FormalSpace.Is07VT` dropped from the Noetherian alternative, which the route
through Stacks 09ZW no longer needs; that declaration keeps its hypothesis and is deduced from
this one. -/
theorem isClosedImmersion_pullback_snd_of_isReduction' {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hmono : Mono f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {Yred : FppfSheaf B S hS} {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    (r : Yred ⟶ X) (hr : r ≫ f = iY) (T : BigFppfOver B S hS)
    (t : yonedaSheaf B S hS T ⟶ Y)
    (hfin : IsLocallyOfFiniteType B S hS f ∨
      (IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) :
    IsClosedImmersion B S hS (pullback.snd f t) := by
  have hsq : IsPullback (pullback.fst f t).hom (pullback.snd f t).hom f.hom t.hom :=
    (IsPullback.of_hasPullback f t).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hV : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback f t).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hsq.flip.isoPullback.symm (hrep T t.hom)
  obtain ⟨F, ⟨e⟩⟩ := Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hV
  have hF : IsAlgebraicSpace B S hS F :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hV)
  obtain ⟨a, ha⟩ := (uliftPresheaf B S hS).map_surjective (X := F) (Y := yoneda.obj T)
    (e.hom ≫ (pullback.snd f t).hom)
  have hmp : Mono (pullback.snd f t).hom :=
    mono_hom_of_mono B S hS _
      (Mono.of_isPullback B S hS (IsPullback.of_hasPullback f t).flip hmono)
  have hmonoa : Mono a := by
    refine (uliftPresheaf B S hS).mono_of_mono_map (f := a) ?_
    rw [ha]
    have he : Mono e.hom := inferInstance
    exact CategoryTheory.mono_comp' he hmp
  obtain ⟨b, m, fst, sq⟩ := hiY.representable t.hom
  have hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m) :=
    hiY.thickening t.hom fst m sq
  have hcond : ((⟨fst⟩ : yonedaSheaf B S hS b ⟶ Yred) ≫ r) ≫ f =
      (⟨(uliftYoneda.{u + 1}).map m⟩ : yonedaSheaf B S hS b ⟶ yonedaSheaf B S hS T) ≫ t := by
    refine Sheaf.hom_ext ?_
    have hrh : r.hom ≫ f.hom = iY.hom := congrArg (fun k : Yred ⟶ Y ↦ k.hom) hr
    show (fst ≫ r.hom) ≫ f.hom = (uliftYoneda.{u + 1}).map m ≫ t.hom
    rw [Category.assoc, hrh]
    exact sq.w
  obtain ⟨w, hw⟩ : ∃ w : yonedaSheaf B S hS b ⟶ pullback f t,
      w ≫ pullback.snd f t =
        (⟨(uliftYoneda.{u + 1}).map m⟩ : yonedaSheaf B S hS b ⟶ yonedaSheaf B S hS T) :=
    ⟨pullback.lift _ _ hcond, pullback.lift_snd _ _ hcond⟩
  obtain ⟨c, hc'⟩ := (uliftPresheaf B S hS).map_surjective (X := yoneda.obj b) (Y := F)
    (w.hom ≫ e.inv)
  have hwp : w.hom ≫ (pullback.snd f t).hom =
      (uliftPresheaf B S hS).map (yoneda.map m) :=
    congrArg (fun k : yonedaSheaf B S hS b ⟶ yonedaSheaf B S hS T ↦ k.hom) hw
  have hc : c ≫ a = yoneda.map m := by
    refine (uliftPresheaf B S hS).map_injective ?_
    rw [Functor.map_comp, hc', ha]
    refine Eq.trans (Category.assoc w.hom e.inv (e.hom ≫ (pullback.snd f t).hom))
      (Eq.trans ?_ hwp)
    exact congrArg (fun k : (pullback f t).obj ⟶ (yonedaSheaf B S hS T).obj ↦ w.hom ≫ k)
      (Iso.inv_hom_id_assoc e (pullback.snd f t).hom)
  have hCI : Space.IsClosedImmersion B S hS a := by
    rcases hfin with hft | ⟨hTaff, hTN⟩
    · have hprop := hft.choose_spec
      have hfta : Space.IsLocallyOfFiniteType B S hS a := by
        have h1 : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
            (pullback.fst t.hom f.hom) := hprop T t.hom
        have h2 : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
            (pullback.snd f t).hom := by
          have h := Space.holdsOnEveryEtaleChartULift_precomp B S hS
            (@AlgebraicGeometry.LocallyOfFiniteType.{u}) hsq.flip.isoPullback.hom _ h1
          rwa [hsq.flip.isoPullback_hom_fst] at h
        have h3 : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
            ((uliftPresheaf B S hS).map a) := by
          rw [ha]
          exact Space.holdsOnEveryEtaleChartULift_precomp B S hS
            (@AlgebraicGeometry.LocallyOfFiniteType.{u}) e.hom _ h2
        exact (Space.isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS a).mp h3
      exact Space.isClosedImmersion_of_mono_of_thickening_factors B S hS hF a hmonoa m hm c hc
        hfta
    · exact Space.isClosedImmersion_of_mono_of_thickening_factors B S hS hF a hmonoa m hm c hc
        (Space.isLocallyOfFiniteType_of_mono_of_thickening_factors_of_isNoetherianRing B S hS a
          hmonoa hTaff hTN m hm c hc)
  refine isClosedImmersion_of_relative B S hS _ ?_
  have h4 := (relative_isClosedImmersion_map_iff B S hS a).mpr hCI
  rw [ha] at h4
  have _ := respectsIso_relative_isClosedImmersion B S hS
  exact (((MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})).cancel_left_of_respectsIso
      e.hom _).mp h4

/-- **The key step of Stacks 0GHZ.** Let `f : X ⟶ Y` be a monomorphism of fppf sheaves on the
big fppf site of `S` which is representable by algebraic spaces, let `iY : Yred ⟶ Y` be a
reduction of `Y` and suppose `iY` factors through `f`. If `f` is locally of finite type, or the
scheme-valued point is a Noetherian affine scheme, then the base change of `f` along that point
is a closed immersion. -/
theorem isClosedImmersion_pullback_snd_of_isReduction {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hmono : Mono f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {Yred : FppfSheaf B S hS} {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    (r : Yred ⟶ X) (hr : r ≫ f = iY) (T : BigFppfOver B S hS)
    (t : yonedaSheaf B S hS T ⟶ Y)
    (hfin : IsLocallyOfFiniteType B S hS f ∨
      (IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ∧ Is07VT B S hS)) :
    IsClosedImmersion B S hS (pullback.snd f t) :=
  isClosedImmersion_pullback_snd_of_isReduction' B S hS hmono hrep hiY r hr T t
    (hfin.imp id fun h ↦ ⟨h.1, h.2.1⟩)

/-! ### Covering a locally Noetherian formal algebraic space by Noetherian affine schemes -/

/-- A cover of an fppf sheaf on the big fppf site of `S` by Noetherian affine schemes of the
site: a family of scheme-valued points with Noetherian affine sources whose induced map from
the coproduct is a surjection of sheaves. -/
abbrev HasNoetherianAffineSchemeCover (Y : FppfSheaf B S hS) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (T : I → BigFppfOver B S hS)
    (g : ∀ i, yonedaSheaf B S hS (T i) ⟶ Y),
    (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T i))) ∧
    (∀ i, IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (T i), ⊤)) ∧
    Sheaf.IsLocallySurjective (Sigma.desc g)

/-- An affine scheme-valued point of an fppf sheaf on the big fppf site of `S`, taken with the
sheafified Yoneda embedding in which the presentations of Stacks 0AI7 are stated. -/
abbrev AffineSchemePoints (Z : FppfSheaf B S hS) : Type (u + 1) :=
  Σ W : BigAffineFppf B S hS,
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj W) ⟶ Z

/-- A scheme-valued point of an fppf sheaf on the big fppf site of `S` whose source is a
Noetherian affine scheme of the site. -/
abbrev NoetherianAffineSchemePoints (Y : FppfSheaf B S hS) : Type (u + 1) :=
  { p : (T : BigFppfOver B S hS) × (yonedaSheaf B S hS T ⟶ Y) //
      IsAffine ((BigFppfOver.toScheme B S hS).obj p.1) ∧
      IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj p.1, ⊤) }

/-- The sheaf represented by an object of the big fppf site of `S` is isomorphic to the
sheafification of its Yoneda presheaf, that topology being subcanonical. -/
noncomputable def yonedaSheafIsoSheafifiedYoneda (W : BigFppfOver B S hS) :
    yonedaSheaf B S hS W ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W :=
  (Functor.FullyFaithful.ofFullyFaithful
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).preimageIso
    (sheafifiedYonedaObjIso B S hS W)

/-- The ring of global sections of a Noetherian affine scheme is a Noetherian ring. -/
private theorem isNoetherianRing_of_isNoetherian {Z : Scheme.{u}} [IsAffine Z]
    (hZ : AlgebraicGeometry.IsNoetherian Z) : IsNoetherianRing Γ(Z, ⊤) :=
  have _ : AlgebraicGeometry.IsLocallyNoetherian Z := hZ.toIsLocallyNoetherian
  AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩

/-- The affine scheme-valued points of an affine formal algebraic space over `S` are jointly
surjective: the stages of a presentation as in Stacks 0AI7 are among them, and the map from the
coproduct of the stages to their colimit is an epimorphism. -/
theorem isLocallySurjective_sigmaDesc_affineSchemePoints {Z : FppfSheaf B S hS}
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective
      (Sigma.desc (fun p : AffineSchemePoints B S hS Z ↦ p.2)) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, Λ, pre, hne, hdir, D, hD, ⟨eD⟩⟩ := hZ
  let _ : Preorder Λ := pre
  have _ : Nonempty Λ := hne
  have _ : IsDirected Λ (· ≤ ·) := hdir
  set K := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) with hK
  set A : AffineSchemePoints B S hS Z → FppfSheaf B S hS := fun p ↦
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj p.1) with hA
  set σ : Λ → AffineSchemePoints B S hS Z := fun l ↦ ⟨D.obj l, colimit.ι K l ≫ eD.inv⟩ with hσ
  rw [Sheaf.isLocallySurjective_iff_epi]
  have hstage : Epi (Sigma.desc (fun l : Λ ↦ colimit.ι K l ≫ eD.inv)) := by
    have h : (Sigma.desc (fun l : Λ ↦ colimit.ι K l ≫ eD.inv)) =
        Sigma.desc (colimit.ι K) ≫ eD.inv := by
      refine Sigma.hom_ext _ _ fun l ↦ ?_
      simp
    rw [h]
    infer_instance
  have hcomp : Sigma.desc (fun l : Λ ↦ Sigma.ι A (σ l)) ≫
      Sigma.desc (fun p : AffineSchemePoints B S hS Z ↦ p.2) =
      Sigma.desc (fun l : Λ ↦ colimit.ι K l ≫ eD.inv) := by
    refine Sigma.hom_ext _ _ fun l ↦ ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
    rfl
  have _ : Epi (Sigma.desc (fun l : Λ ↦ Sigma.ι A (σ l)) ≫
      Sigma.desc (fun p : AffineSchemePoints B S hS Z ↦ p.2)) := by
    rw [hcomp]; exact hstage
  exact epi_of_epi (Sigma.desc (fun l : Λ ↦ Sigma.ι A (σ l))) _

/-- **Stacks 0AKM with Stacks 0AI7.** A locally Noetherian formal algebraic space over `S` is
covered by Noetherian affine schemes of the site: the charts of an atlas as in Stacks 0AIM are
Noetherian affine formal algebraic spaces, so each has a presentation with Noetherian affine
stages, and every affine scheme-valued point of a chart factors through one of its stages. -/
theorem hasNoetherianAffineSchemeCover_of_isLocallyNoetherian {Y : FppfSheaf B S hS}
    (hY : IsLocallyNoetherian B S hS Y) : HasNoetherianAffineSchemeCover B S hS Y := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Yi, c, haffI, -, hsurj, hnoethI⟩ := hY.2
  have hbig : Sheaf.IsLocallySurjective
      (Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
        p.2.2 ≫ Sigma.ι Yi p.1)) :=
    Sheaf.isLocallySurjective_sigmaDesc_sigma
      (κ := fun i : I ↦ AffineSchemePoints B S hS (Yi i))
      (A := fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj p.2.1))
      (Gm := Yi) (fun p ↦ p.2.2)
      fun i ↦ isLocallySurjective_sigmaDesc_affineSchemePoints B S hS (haffI i)
  have hepi : Epi (Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
      p.2.2 ≫ c p.1)) := by
    have h : Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
        p.2.2 ≫ c p.1) =
        Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
          p.2.2 ≫ Sigma.ι Yi p.1) ≫ Sigma.desc c := by
      refine Sigma.hom_ext _ _ fun p ↦ ?_
      simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    rw [h]
    have _ : Epi (Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
        p.2.2 ≫ Sigma.ι Yi p.1)) := (Sheaf.isLocallySurjective_iff_epi _).1 hbig
    have _ : Epi (Sigma.desc c) := (Sheaf.isLocallySurjective_iff_epi _).1 hsurj
    exact epi_comp _ _
  have hfactor : ∀ p : Σ i : I, AffineSchemePoints B S hS (Yi i),
      ∃ (q : NoetherianAffineSchemePoints B S hS Y)
        (v : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
              ((BigAffineFppf.inclusion B S hS).obj p.2.1) ⟶ yonedaSheaf B S hS q.1.1),
        v ≫ q.1.2 = p.2.2 ≫ c p.1 := by
    rintro ⟨i, W, a⟩
    obtain ⟨-, Λ, pre, hne, hdir, D, hD, ⟨eD⟩, hN⟩ :=
      isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS (hnoethI i)
    let _ : Preorder Λ := pre
    have _ : Nonempty Λ := hne
    have _ : IsDirected Λ (· ≤ ·) := hdir
    obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS (Yi i) Λ D hD eD W a
    have haffj : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj j))) := (D.obj j).property
    refine ⟨⟨⟨(BigAffineFppf.inclusion B S hS).obj (D.obj j),
      (yonedaSheafIsoSheafifiedYoneda B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.obj j))).hom ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) j ≫ eD.inv ≫ c i⟩,
      haffj, isNoetherianRing_of_isNoetherian (hN j)⟩,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        (yonedaSheafIsoSheafifiedYoneda B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.obj j))).inv, ?_⟩
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← hg]
    simp only [Category.assoc]
  choose q v hv using hfactor
  refine ⟨NoetherianAffineSchemePoints B S hS Y, fun p ↦ p.1.1, fun p ↦ p.1.2,
    fun p ↦ p.2.1, fun p ↦ p.2.2, ?_⟩
  rw [Sheaf.isLocallySurjective_iff_epi]
  have hcomp : Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
      v p ≫ Sigma.ι (fun r : NoetherianAffineSchemePoints B S hS Y ↦
        yonedaSheaf B S hS r.1.1) (q p)) ≫
      Sigma.desc (fun r : NoetherianAffineSchemePoints B S hS Y ↦ r.1.2) =
      Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦ p.2.2 ≫ c p.1) := by
    refine Sigma.hom_ext _ _ fun p ↦ ?_
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc, hv p]
  have _ : Epi (Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
      v p ≫ Sigma.ι (fun r : NoetherianAffineSchemePoints B S hS Y ↦
        yonedaSheaf B S hS r.1.1) (q p)) ≫
      Sigma.desc (fun r : NoetherianAffineSchemePoints B S hS Y ↦ r.1.2)) := by
    rw [hcomp]; exact hepi
  exact epi_of_epi (Sigma.desc (fun p : Σ i : I, AffineSchemePoints B S hS (Yi i) ↦
    v p ≫ Sigma.ι (fun r : NoetherianAffineSchemePoints B S hS Y ↦
      yonedaSheaf B S hS r.1.1) (q p))) _

/-! ### Stacks 0GHZ -/

/-- **Stacks 0GHZ** when `f` is locally of finite type, with no granted hypothesis: a
monomorphism of formal algebraic spaces over `S` which is locally of finite type and through
which a reduction of its target factors is a closed immersion. -/
theorem isClosedImmersion_of_mono_of_isLocallyOfFiniteType {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hmono : Mono f) (hft : IsLocallyOfFiniteType B S hS f)
    {Yred : FppfSheaf B S hS} {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    (r : Yred ⟶ X) (hr : r ≫ f = iY) :
    IsClosedImmersion B S hS f :=
  isClosedImmersion_of_forall_scheme B S hS f fun T t ↦
    isClosedImmersion_pullback_snd_of_isReduction B S hS hmono hft.choose hiY r hr T t
      (Or.inl hft)

/-- Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which is representable by
algebraic spaces and a monomorphism, and through which the inclusion `iY : Yred ⟶ Y` of a
reduction of `Y` factors. If `f` is locally of finite type, or `Y` is locally Noetherian, then `f`
is a closed immersion. -/
@[stacks 0GHZ "the reduction, its inclusion and the factorisation are data, as in Stacks 0GB8"]
theorem isClosedImmersion_of_mono_of_reduction_factors {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) (hmono : Mono f)
    {Yred : FppfSheaf B S hS} {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    (r : Yred ⟶ X) (hr : r ≫ f = iY)
    (hfin : IsLocallyOfFiniteType B S hS f ∨ IsLocallyNoetherian B S hS Y) :
    IsClosedImmersion B S hS f := by
  rcases hfin with hft | hnoeth
  · exact isClosedImmersion_of_mono_of_isLocallyOfFiniteType B S hS hmono hft hiY r hr
  · obtain ⟨I, T, g, haff, hN, hsurj⟩ :=
      hasNoetherianAffineSchemeCover_of_isLocallyNoetherian B S hS hnoeth
    exact isClosedImmersion_of_locallySurjectiveFamily B S hS I
      (fun i ↦ yonedaSheaf B S hS (T i)) g hsurj fun i ↦
      isClosedImmersion_pullback_snd_of_isReduction' B S hS hmono hrep hiY r hr (T i) (g i)
        (Or.inr ⟨haff i, hN i⟩)

end AlgebraicGeometry.FormalSpace

end
