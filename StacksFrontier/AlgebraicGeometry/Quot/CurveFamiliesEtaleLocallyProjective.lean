module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProperRelativeAmpleProjective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleAffineBaseTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ImmersionTwistGapUniform
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite

/-!
# Families of curves are étale locally H-projective schemes (Stacks 0E6F)

Stacks 0E6F: for a family of curves `X ⟶ S` there is an étale covering `{S_i ⟶ S}` such that
each `X_i = X ×_S S_i` is a scheme, and even H-projective over `S_i`. The source's proof is a
corollary of the smoothness of `PolarizedCurves ⟶ Curves` (Stacks 0DQ0): after a smooth
surjective base change `S' ⟶ S` the family is a scheme with a relatively ample invertible
module; the smooth covering is refined by an étale one (Stacks 055V, via 055U); and a proper
morphism with a relatively ample invertible module is H-projective over affine opens of the
base (Stacks 0B5N, 01WB).

This module proves everything in that argument after its first sentence. The input it takes is
`AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized`, the statement of Stacks 0DQ0 about a
single family that the first sentence of the proof unwinds to; none of the results below is
registered, and the registration of Stacks 0E6F waits for that input to be proved for every
family.

The statements cover finitely many families over the same base at once, with one étale
covering for all of them, which is how Stacks 0E6F is used for several total spaces together
(for example in the proof of Stacks 0E88).

## Main definitions

* `AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized`: through every point of the base
  there is a smooth chart along which the family is a scheme with a relatively ample invertible
  module.

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isRelativelyAmple_of_isAffine`: over an
  affine base a proper morphism with a relatively ample invertible module is H-projective.
* `AlgebraicGeometry.CurveFamily.exists_affine_etale_sections_of_smooth`: finitely many smooth
  morphisms through a point have a common affine étale local section (Stacks 055U, iterated).
* `CurveFamily.exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized`:
  Stacks 0E6F pointwise, for finitely many families over one base, from their smooth local
  polarizations.
* `CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized`:
  the same as an étale covering.

## Implementation notes

"`X ×_S S_i` is a scheme" is a cartesian square of algebraic spaces whose corner is the algebraic
space `schemeSpace Z` of a scheme `Z` of the site, with `Z ⟶ S_i` a morphism of the site; this is
the form the rest of the moduli-of-curves files consume. H-projectivity is
`AlgebraicGeometry.IsProjectiveMorphism` of Stacks 01W8. An étale covering of `S` is a jointly
surjective family of morphisms of the site, étale on underlying schemes; its members have to be
objects of the site for the base changes to be algebraic spaces over it, so they are taken
affine, which bounds their size.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
* [Stacks Project, Tag 0B5N](https://stacks.math.columbia.edu/tag/0B5N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}


open Stacks.Ample in
/-- **Over an affine base, a proper morphism carrying a relatively ample invertible module is
H-projective.** Over an affine base relative ampleness is ampleness
(`Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine`), so Stacks 01VS
(`Stacks.Tag01VT.eventually_hasImmersionTwistOver_of_isAmple`) gives an immersion into some
`ℙⁿ` over the base, which is closed by properness (Stacks 01W6,
`Stacks.ProperRelativeAmpleProjective.isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver`).
-/
theorem _root_.AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isRelativelyAmple_of_isAffine
    {Z U : Scheme.{u}} [IsAffine U] (q : Z ⟶ U) [IsProper q] (L : Z.Modules)
    [IsInvertibleModule Z L] (hL : Stacks.RelativeAmple.IsRelativelyAmple q L) :
    IsProjectiveMorphism q := by
  obtain ⟨d₀, -, hd⟩ := Stacks.Tag01VT.eventually_hasImmersionTwistOver_of_isAmple
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform q L
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine q L hL)
  exact
    Stacks.ProperRelativeAmpleProjective.isProjectiveMorphism_of_isProper_of_hasImmersionTwistOver
      q (hd d₀ le_rfl)

/-- A morphism of schemes between the schemes underlying two objects of the big fppf site over
`Spec ℤ` is a morphism of that site: the structure morphisms go to a terminal scheme. -/
abbrev siteHom {U V : BigFppfOver B integerBase hZ}
    (f : (BigFppfOver.toScheme B integerBase hZ).obj U ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj V) : U ⟶ V :=
  BigFppfOver.homOfCompEq B integerBase hZ f (specULiftZIsTerminal.hom_ext _ _)

/-- The morphism of schemes underlying `siteHom f` is `f`. -/
@[simp]
theorem toScheme_map_siteHom {U V : BigFppfOver B integerBase hZ}
    (f : (BigFppfOver.toScheme B integerBase hZ).obj U ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj V) :
    (BigFppfOver.toScheme B integerBase hZ).map (siteHom f) = f :=
  BigFppfOver.toScheme_map_homOfCompEq B integerBase hZ _ _

/-- A scheme contained in the site, as an object of the big fppf site over `Spec ℤ`. -/
abbrev siteObj {Y : Scheme.{u}} (hY : B.Contains Y) : BigFppfOver B integerBase hZ :=
  BigFppfOver.mk B integerBase hZ hY (specULiftZIsTerminal.from Y)

/-- A morphism of schemes out of a scheme contained in the site, as a morphism of the site out
of the corresponding object. -/
abbrev siteHomOfContains {Y : Scheme.{u}} (hY : B.Contains Y) {V : BigFppfOver B integerBase hZ}
    (f : Y ⟶ (BigFppfOver.toScheme B integerBase hZ).obj V) : siteObj (hZ := hZ) hY ⟶ V :=
  siteHom f

/-- The morphism of schemes underlying `siteHomOfContains hY f` is `f`. -/
@[simp]
theorem toScheme_map_siteHomOfContains {Y : Scheme.{u}} (hY : B.Contains Y)
    {V : BigFppfOver B integerBase hZ} (f : Y ⟶ (BigFppfOver.toScheme B integerBase hZ).obj V) :
    (BigFppfOver.toScheme B integerBase hZ).map (siteHomOfContains (hZ := hZ) hY f) = f :=
  toScheme_map_siteHom _

/-- A cartesian square of the site is cartesian after reading its schemes as algebraic
spaces. -/
theorem isPullback_schemeSpaceMap_fst_snd {Z U T' : BigFppfOver B integerBase hZ}
    (q : Z ⟶ T') (g : U ⟶ T') :
    IsPullback (schemeSpaceMap (pullback.fst q g)) (schemeSpaceMap (pullback.snd q g))
      (schemeSpaceMap q) (schemeSpaceMap g) :=
  Space.isPullback_homMk B integerBase hZ _ _ _ _ ((IsPullback.of_hasPullback q g).map yoneda)

end AlgebraicGeometry.CurveFamily

namespace AlgebraicGeometry.CurveFamily
variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}


open Stacks.Ample in
/-- **Base change of a polarized scheme chart of a family of curves to an affine scheme.** Let
`X` be a family of curves, `π : T' ⟶ X.base` a morphism of the site, and suppose that the base
change of `X` along `π` is a scheme `Z` (a cartesian square with `schemeSpace Z` at its corner)
carrying an invertible module ample relative to `Z ⟶ T'`. Then for every affine `U` of the site
mapping to `T'`, the base change of `X` along `U ⟶ T' ⟶ X.base` is a scheme which is
H-projective over `U`.

The scheme is `Z ×_{T'} U`; properness of `Z ⟶ T'` comes from that of the family (Stacks 0EPD
and Stacks 03ZM on a represented morphism), relative ampleness passes to the base change
(Stacks 0893), and over the affine `U` a proper morphism with a relatively ample invertible
module is H-projective. -/
theorem exists_isPullback_isProjectiveMorphism_of_polarizedChart (X : CurveFamily B hZ)
    {T' Z U : BigFppfOver B integerBase hZ} {π : T' ⟶ X.base} {p : schemeSpace Z ⟶ X.total}
    {q : Z ⟶ T'} (hsq : IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap π))
    (L : ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules)
    [IsInvertibleModule _ L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B integerBase hZ).map q) L)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U)] (g : U ⟶ T') :
    ∃ (Z' : BigFppfOver B integerBase hZ) (p' : schemeSpace Z' ⟶ X.total) (q' : Z' ⟶ U),
      IsPullback p' (schemeSpaceMap q') X.toBase (schemeSpaceMap (g ≫ π)) ∧
      IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q') := by
  refine ⟨pullback q g, schemeSpaceMap (pullback.fst q g) ≫ p, pullback.snd q g, ?_, ?_⟩
  · rw [schemeSpaceMap_comp]
    exact (isPullback_schemeSpaceMap_fst_snd q g).paste_horiz hsq
  · have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q) :=
      Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ q
        (Space.isProper_of_isPullback B integerBase hZ (schemeSpace Z).property X.total.property
          (schemeSpace T').property (schemeSpace X.base).property
          (AlgebraicSpaces.isPullback_hom B integerBase hZ hsq) X.proper)
    have hsqS := (IsPullback.of_hasPullback q g).map (BigFppfOver.toScheme B integerBase hZ)
    have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd q g)) :=
      MorphismProperty.of_isPullback hsqS this
    exact isProjectiveMorphism_of_isProper_of_isRelativelyAmple_of_isAffine _ _
      (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsqS L hL)


/-- **Finitely many smooth morphisms to a scheme of the site have a common affine étale local
section through any point of all their images.** Given a point `s` of the base and finitely many
smooth morphisms `π i : T' i ⟶ S` of the site whose images contain `s`, there is an affine scheme
`U` of the site with an étale morphism `φ : U ⟶ S` whose image contains `s`, through which every
`π i` has a section over `S`.

This is Stacks 055U applied once per morphism: the morphisms are added one at a time, and the
next one is base changed to the étale neighbourhood already found, where it is still smooth and
still has `u` in its image; an affine open of the étale neighbourhood that 055U produces keeps
the scheme of bounded size, so inside the site. -/
theorem exists_affine_etale_sections_of_smooth {ι : Type*} [Finite ι]
    {S : BigFppfOver B integerBase hZ} (s : (BigFppfOver.toScheme B integerBase hZ).obj S)
    (T' : ι → BigFppfOver B integerBase hZ) (π : ∀ i, T' i ⟶ S)
    (hπ : ∀ i, Smooth ((BigFppfOver.toScheme B integerBase hZ).map (π i)))
    (hs : ∀ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (π i)).base) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj U),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
      (BigFppfOver.toScheme B integerBase hZ).map φ u = s ∧
      ∀ i, ∃ g : U ⟶ T' i, g ≫ π i = φ := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ F : Finset ι, ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj U),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
      (BigFppfOver.toScheme B integerBase hZ).map φ u = s ∧
      ∀ i ∈ F, ∃ g : U ⟶ T' i, g ≫ π i = φ := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset
        (X := (BigFppfOver.toScheme B integerBase hZ).obj S) (x := s) (U := ⊤) trivial
      have hcont : B.Contains (V : Scheme.{u}) :=
        BigFppfOver.contains_opens B S.left.property V
      refine ⟨siteObj hcont, siteHomOfContains hcont V.ι, ⟨s, hsV⟩, ?_, hV, ?_, by simp⟩
      · have : Etale V.ι := inferInstance
        rw [toScheme_map_siteHomOfContains]
        exact this
      · rw [toScheme_map_siteHomOfContains]
        rfl
    | insert a F ha ih =>
      obtain ⟨U, φ, u, hφ, hU, hu, hg⟩ := ih
      obtain ⟨t, ht⟩ := hs a
      have := hπ a
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback u t (hu.trans ht.symm)
      obtain ⟨W, g₀, hg₀⟩ := exists_etaleNeighborhood_lift_of_smooth
        (pullback.fst ((BigFppfOver.toScheme B integerBase hZ).map φ)
          ((BigFppfOver.toScheme B integerBase hZ).map (π a))) u ⟨z, hz1⟩
      obtain ⟨W₀, hW₀, hpt, -⟩ := exists_isAffineOpen_mem_and_subset
        (X := W.scheme) (x := W.point) (U := ⊤) trivial
      have : IsAffine (W₀ : Scheme.{u}) := hW₀
      let ν : (W₀ : Scheme.{u}) ⟶ (BigFppfOver.toScheme B integerBase hZ).obj U :=
        W₀.ι ≫ W.toBase
      have : QuasiCompact ν := inferInstance
      have hcont : B.Contains (W₀ : Scheme.{u}) :=
        Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ν U.left.property
      refine ⟨siteObj hcont, siteHomOfContains hcont ν ≫ φ, ⟨W.point, hpt⟩, ?_, hW₀, ?_, ?_⟩
      · have := hφ
        have : Etale (ν ≫ (BigFppfOver.toScheme B integerBase hZ).map φ) := inferInstance
        rw [Functor.map_comp, toScheme_map_siteHomOfContains]; exact this
      · rw [Functor.map_comp, toScheme_map_siteHomOfContains]
        change (BigFppfOver.toScheme B integerBase hZ).map φ (W.toBase W.point) = s
        rw [W.map_point, hu]
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · refine ⟨siteHomOfContains hcont (W₀.ι ≫ g₀ ≫ pullback.snd _ _), ?_⟩
          have e : (W₀.ι ≫ g₀ ≫ pullback.snd _ _) ≫
              (BigFppfOver.toScheme B integerBase hZ).map (π i) =
                ν ≫ (BigFppfOver.toScheme B integerBase hZ).map φ := by
            simp only [Category.assoc, ν]
            rw [← pullback.condition, ← Category.assoc g₀, hg₀]
          apply (BigFppfOver.toScheme B integerBase hZ).map_injective
          rw [Functor.map_comp, Functor.map_comp, toScheme_map_siteHomOfContains,
            toScheme_map_siteHomOfContains]
          exact e
        · obtain ⟨g, hg⟩ := hg i hi
          exact ⟨siteHomOfContains hcont ν ≫ g, by rw [Category.assoc, hg]⟩
  obtain ⟨U, φ, u, h1, h2, h3, h4⟩ := key Finset.univ
  exact ⟨U, φ, u, h1, h2, h3, fun i => h4 i (Finset.mem_univ i)⟩


open Stacks.Ample in
/-- A family of curves is *smooth locally polarized* when through every point of its base there
is a smooth morphism `π : T' ⟶ X.base` of the site along which the base change of `X` is a
scheme `Z` — a cartesian square of algebraic spaces with `schemeSpace Z` at its corner — carrying
an invertible module ample relative to `Z ⟶ T'`.

This is what the smoothness half of Stacks 0DQ0 says about a single family `X ⟶ S`, unwound as
in the proof of Stacks 0E6F: the base change of `PolarizedCurves ⟶ Curves` along `S ⟶ Curves`
is smooth and surjective over `S`, and a smooth chart of it through a point is a smooth
`S' ⟶ S` with an object `(X_{S'}, L')` of `PolarizedCurves` over `S'` mapping to `X_{S'}`. -/
def IsSmoothLocallyPolarized (X : CurveFamily B hZ) : Prop :=
  ∀ t : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
    ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
      Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
      ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ T'),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap π) ∧
        ∃ (L : ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules)
          (_ : IsInvertibleModule _ L),
          Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B integerBase hZ).map q) L

open Stacks.Ample in
/-- `AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized` read over a scheme equal to the
base of the family. -/
theorem IsSmoothLocallyPolarized.of_base_eq {X : CurveFamily B hZ}
    {S : BigFppfOver B integerBase hZ} (h : X.base = S) (hX : X.IsSmoothLocallyPolarized)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj S) :
    ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ S),
      Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
      ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ T'),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (π ≫ eqToHom h.symm)) ∧
        ∃ (L : ((BigFppfOver.toScheme B integerBase hZ).obj Z).Modules)
          (_ : IsInvertibleModule _ L),
          Stacks.RelativeAmple.IsRelativelyAmple
            ((BigFppfOver.toScheme B integerBase hZ).map q) L := by
  subst h
  obtain ⟨T', π, h1, h2, Z, p, q, h3, h4⟩ := hX s
  exact ⟨T', π, h1, h2, Z, p, q, by simpa using h3, h4⟩

/-- **Stacks 0E6F, pointwise, for finitely many families over one base, from the smooth local
polarizations of Stacks 0DQ0.** Let `X i`, for `i` in a finite type, be families of curves over
a common base `S`, each smooth locally polarized. Through every point `s` of `S` there is an
étale morphism `φ : U ⟶ S` of the site whose image contains `s`, along which the base change of
every `X i` is a scheme `Z` — a cartesian square of algebraic spaces with `schemeSpace Z` at its
corner — which is H-projective over `U`.

Each `X i` is polarized after a smooth base change through `s`; Stacks 055U, used once per
family, gives one affine étale neighbourhood `U` of `s` mapping to all of those smooth charts;
and the polarized chart of each family pulls back to `U`, where properness and relative
ampleness make it H-projective because `U` is affine. -/
theorem exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized
    {ι : Type*} [Finite ι] {S : BigFppfOver B integerBase hZ} (X : ι → CurveFamily B hZ)
    (hX : ∀ i, (X i).base = S) (hpol : ∀ i, (X i).IsSmoothLocallyPolarized)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj S) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ S)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj U),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      (BigFppfOver.toScheme B integerBase hZ).map φ u = s ∧
      ∀ i, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ (X i).total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) (X i).toBase
          (schemeSpaceMap (φ ≫ eqToHom (hX i).symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  choose T' π hπ hs Z p q hsq L hL hamp using
    fun i => (hpol i).of_base_eq (hX i) s
  obtain ⟨U, φ, u, hφ, hU, hu, hg⟩ := exists_affine_etale_sections_of_smooth s T' π hπ hs
  refine ⟨U, φ, u, hφ, hu, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hg i
  have := hL i
  obtain ⟨Z', p', q', h1, h2⟩ :=
    exists_isPullback_isProjectiveMorphism_of_polarizedChart (X i) (hsq i) (L i) (hamp i) g
  rw [← Category.assoc, hg] at h1
  exact ⟨Z', p', q', h1, h2⟩

/-- **Stacks 0E6F, as an étale covering, for finitely many families over one base, from the
smooth local polarizations of Stacks 0DQ0.** For finitely many smooth locally polarized families
of curves `X i` over a common base `S` there is a jointly surjective family of étale morphisms
`φ j : U j ⟶ S` of the site such that every base change `X i ×_S U j` is a scheme, H-projective
over `U j`. -/
theorem exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized
    {ι : Type*} [Finite ι] {S : BigFppfOver B integerBase hZ} (X : ι → CurveFamily B hZ)
    (hX : ∀ i, (X i).base = S) (hpol : ∀ i, (X i).IsSmoothLocallyPolarized) :
    ∃ (J : Type u) (U : J → BigFppfOver B integerBase hZ) (φ : ∀ j, U j ⟶ S),
      (∀ j, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      (∀ s : (BigFppfOver.toScheme B integerBase hZ).obj S,
        ∃ j, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      ∀ j i, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ (X i).total)
        (q : Z ⟶ U j),
        IsPullback p (schemeSpaceMap q) (X i).toBase
          (schemeSpaceMap (φ j ≫ eqToHom (hX i).symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  choose U φ u hφ hu hZ' using
    exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized X hX hpol
  exact ⟨_, U, φ, hφ, fun s => ⟨s, u s, hu s⟩, hZ'⟩

/-- **Stacks 0E6F, for one family, from the smooth local polarizations of Stacks 0DQ0.** A
smooth locally polarized family of curves `X ⟶ S` has an étale covering `{S_j ⟶ S}` such that
each `X ×_S S_j` is a scheme, H-projective over `S_j`. -/
theorem exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized_one
    (X : CurveFamily B hZ) (hpol : X.IsSmoothLocallyPolarized) :
    ∃ (J : Type u) (U : J → BigFppfOver B integerBase hZ) (φ : ∀ j, U j ⟶ X.base),
      (∀ j, Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      (∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
        ∃ j, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ j))) ∧
      ∀ j, ∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ X.total) (q : Z ⟶ U j),
        IsPullback p (schemeSpaceMap q) X.toBase (schemeSpaceMap (φ j)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q) := by
  obtain ⟨J, U, φ, hφ, hs, hZ'⟩ :=
    exists_etaleCovering_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized
      (fun _ : Unit => X) (fun _ => rfl) (fun _ => hpol)
  refine ⟨J, U, φ, hφ, hs, fun j => ?_⟩
  obtain ⟨Z, p, q, h1, h2⟩ := hZ' j ()
  exact ⟨Z, p, q, by simpa using h1, h2⟩

end AlgebraicGeometry.CurveFamily

end
