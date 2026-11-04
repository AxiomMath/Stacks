module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Enlargement
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SiteAxioms
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Enlarging a small pro-étale site

A small pro-étale site of a scheme `S` is cut out of a chosen big pro-étale site containing
`S`, so a containment of chosen big pro-étale sites induces an inclusion of the two small
pro-étale sites of `S` that they cut out. That inclusion is fully faithful, continuous and
cocontinuous, it commutes with fibre products, and it carries the final object `S/S` of the
smaller small site to the final object of the larger one; that is, it satisfies the hypotheses
of Stacks 00XU. There are therefore morphisms of topoi `g` and `f` in both directions whose
composite is isomorphic to the identity and which satisfy `f_* = g^{-1}`; and restriction along
the inclusion leaves cohomology unchanged.

## Main definitions

* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.smallFunctor` — the inclusion of
  the small pro-étale site of `S` cut out by the smaller big site into the one cut out by the
  larger big site.

## Main results

* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.fullyFaithfulSmallFunctor`,
  `IsContainedIn.smallFunctor_isCocontinuous`,
  `IsContainedIn.smallFunctor_preservesFiniteLimits` and
  `IsContainedIn.smallFunctor_isMorphismOfSites` are the hypotheses of Stacks 00XU for the
  inclusion of the two small sites.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.smallToposRetraction` is the
  resulting pair of morphisms of topoi together with the retraction of their composite.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.smallCohomologyRestrictionIso`:
  `H^p` of an abelian sheaf on the larger small site agrees with `H^p` of its restriction to
  the smaller one, and
  `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.smallCohomologyPushforwardIso`,
  `IsContainedIn.smallCohomologyLowerShriekIso`: `H^p` of an abelian sheaf on the smaller small
  site agrees with `H^p` of its image under `g_*` and under `f^{-1}`.

## Implementation notes

Cocontinuity is again the only clause with pro-étale content, and it is proved from Stacks 098J
exactly as for the big sites, with one extra step: the covering family that Stacks 098J produces
lives in the chosen big category, and has to be read back in the small site. Its members are
weakly étale over the object being covered, being members of a pro-étale covering family, hence
weakly étale over `S`; so each of them carries a structure morphism making it an object of the
small site, and the family is a small-site covering because its image in the big category is the
family one started from.

The small sites have fibre products and a final object, both computed in the chosen big category
(Stacks 098M); that is what makes the inclusion left exact.

The comparison of cohomology is Stacks 03YU applied to the inclusion. Its two hypotheses on the
restriction functor on abelian sheaves are discharged here: right exactness because restriction
is a left adjoint, the inclusion being cocontinuous, and preservation of injective objects
because its left adjoint `g_!` is left exact, the smaller small site having fibre products and
equalizers preserved by the inclusion (Stacks 04BH). The abelian sheaves on a small pro-étale
site form a Grothendieck abelian category, which is what supplies the injective resolutions and
`Ext`-groups the comparison is stated with.

## References

* [Stacks Project, Tag 098Y](https://stacks.math.columbia.edu/tag/098Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- The functor sending an object of a small pro-étale site to the underlying object of the
chosen big pro-étale category. -/
private abbrev smallToBig (B : BigProetaleSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) : SmallProetale B S hS ⥤ B.Scheme :=
  SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS

/-- Abelian sheaves on a small pro-étale site form a Grothendieck abelian category: the site is
small at the universe of the coefficients, so the general criterion applies. -/
instance smallProetale_isGrothendieckAbelian (B : BigProetaleSite.{u})
    (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallProetale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_small _ _

namespace BigProetaleSite.IsContainedIn

variable {B B' : BigProetaleSite.{u}} (h : B.IsContainedIn B')
  (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the small pro-étale site of `S` cut out by a chosen big pro-étale site into
the small pro-étale site of `S` cut out by a chosen big pro-étale site containing it.

An object of the smaller small site is an object of the smaller big category over `S` whose
structure morphism is weakly étale; it is sent to the same scheme over `S`, read in the larger
big category, whose structure morphism is the same morphism of schemes and so is weakly étale
again. -/
def smallFunctor : SmallProetale B S hS ⥤ SmallProetale B' S (h.contains hS) :=
  ObjectProperty.lift (IsWeaklyEtaleOver B' S (h.contains hS))
    (SmallProetale.inclusion B S hS ⋙ h.functorOver S hS) (fun X ↦ X.property)

/-- **Stacks 098Y**, hypothesis (c) of Stacks 00XU: the inclusion of the two small pro-étale
sites of `S` is fully faithful.

Both small sites are full subcategories of nested big pro-étale categories over `S`, and the
inclusion of those is fully faithful. -/
@[stacks 098Y "hypothesis (c) of 00XU for the inclusion of the small sites: full faithfulness"]
def fullyFaithfulSmallFunctor : (h.smallFunctor S hS).FullyFaithful where
  preimage {_ _} f := ObjectProperty.homMk ((h.fullyFaithfulFunctorOver S hS).preimage f.hom)
  map_preimage {_ _} f :=
    ObjectProperty.hom_ext _ ((h.fullyFaithfulFunctorOver S hS).map_preimage f.hom)
  preimage_map {_ _} f :=
    ObjectProperty.hom_ext _ ((h.fullyFaithfulFunctorOver S hS).preimage_map f.hom)

/-- The inclusion of the two small pro-étale sites of `S` is full. -/
instance smallFunctor_full : (h.smallFunctor S hS).Full :=
  (h.fullyFaithfulSmallFunctor S hS).full

/-- The inclusion of the two small pro-étale sites of `S` is faithful. -/
instance smallFunctor_faithful : (h.smallFunctor S hS).Faithful :=
  (h.fullyFaithfulSmallFunctor S hS).faithful


/-- **Stacks 098Y**, hypotheses (d) and (e) of Stacks 00XU: fibre products exist in the smaller
small pro-étale site and are preserved by the inclusion, which also carries the final object
`S/S` to the final object `S/S`.

Both small sites have fibre products and the final object `𝟙 S` (Stacks 098M), both computed in
the ambient big pro-étale category over `S`; the inclusion therefore preserves all finite
limits. -/
@[stacks 098Y
  "hypotheses (d) and (e) of 00XU for the inclusion of the small sites: preservation of fibre
  products and of the final object"]
theorem smallFunctor_preservesFiniteLimits : PreservesFiniteLimits (h.smallFunctor S hS) := by
  have hId : (h.smallFunctor S hS).obj (smallIdentity B S hS) =
      smallIdentity B' S (h.contains hS) := rfl
  let : PreservesLimitsOfShape WalkingCospan (SmallProetale.inclusion B S hS) := by
    let : CreatesLimitsOfShape WalkingCospan (SmallProetale.inclusion B S hS) :=
      smallProetaleInclusion_createsPullbacks B S hS
    infer_instance
  let : PreservesFiniteLimits (h.functorOver S hS) := h.functorOver_preservesFiniteLimits S hS
  let : PreservesLimitsOfShape WalkingCospan
      (h.smallFunctor S hS ⋙ SmallProetale.inclusion B' S (h.contains hS)) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B S hS ⋙ h.functorOver S hS))
  let : ReflectsLimitsOfShape WalkingCospan
      (SmallProetale.inclusion B' S (h.contains hS)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimitsOfShape WalkingCospan (h.smallFunctor S hS) :=
    preservesLimitsOfShape_of_reflects_of_preserves (h.smallFunctor S hS)
      (SmallProetale.inclusion B' S (h.contains hS))
  let : PreservesLimit (Functor.empty.{0} (SmallProetale B S hS)) (h.smallFunctor S hS) :=
    preservesTerminal_of_iso (h.smallFunctor S hS)
      ((h.smallFunctor S hS).mapIso
          ((terminalIsTerminal (C := SmallProetale B S hS)).uniqueUpToIso
            (smallIdentity_isTerminal B S hS)) ≪≫ eqToIso hId ≪≫
        (smallIdentity_isTerminal B' S (h.contains hS)).uniqueUpToIso terminalIsTerminal)
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (h.smallFunctor S hS) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal (h.smallFunctor S hS)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks (h.smallFunctor S hS)

/-- **Stacks 098Y**, hypothesis (a) of Stacks 00XU: the inclusion of the two small pro-étale
sites of `S` is cocontinuous.

A covering sieve of the larger small site at an object `X` of the smaller one contains a
covering family of the larger small site, whose image in the larger big pro-étale category is a
chosen covering family there, hence an arbitrary pro-étale covering of the scheme underlying
`X`. By Stacks 098J that covering is refined by a chosen covering family of the *smaller* big
site. The members of the refining family are weakly étale over `X`, being members of a pro-étale
covering, hence weakly étale over `S`, so the family is a covering family of the smaller small
site; and each of its members factors through a member of the given family, over `S` because the
factorization is compatible with the maps to `X`. -/
@[stacks 098Y "hypothesis (a) of 00XU for the inclusion of the small sites: cocontinuity"]
instance smallFunctor_isCocontinuous :
    (h.smallFunctor S hS).IsCocontinuous (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) := by
  set K := smallToBig B S hS
  set K' := smallToBig B' S (h.contains hS)
  constructor
  intro X R hR
  obtain ⟨E', hE', hE'R⟩ := exists_covering_le_of_isSite
    (SmallProetale.IsCovering B' S (h.contains hS))
    (SmallProetale.isSite B' S (h.contains hS))
    (SmallProetale.precoverage B' S (h.contains hS)) (fun _ _ ↦ Iff.rfl) R hR
  have hcov : Presieve.ofArrows (fun j ↦ (K'.obj (E'.X j)).obj)
      (fun j ↦ B'.inclusion.map (K'.map (E'.f j))) ∈
        Scheme.proetalePrecoverage.coverings (K.obj X).obj :=
    (B'.isProetaleCovering_iff ⟨K'.obj ((h.smallFunctor S hS).obj X), E'.map K'⟩).mp hE'.1
  obtain ⟨E, hE, href⟩ := exists_covering_refining_proetaleCovering B (K.obj X)
    (fun j ↦ (K'.obj (E'.X j)).obj) (fun j ↦ B'.inclusion.map (K'.map (E'.f j))) hcov
  -- the members of the refining family are weakly étale over `S`
  have hweS (j : E.I₀) : WeaklyEtale (B.inclusion.map (E.f j ≫ X.obj.hom)) := by
    have : WeaklyEtale (B.inclusion.map (E.f j)) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale (K.obj X).obj
        ((B.isProetaleCovering_iff ⟨K.obj X, E⟩).mp hE.1) (Presieve.ofArrows.mk j)
    have : WeaklyEtale (B.inclusion.map X.obj.hom) := X.property
    rw [B.inclusion.map_comp]
    infer_instance
  -- the refining family, read in the smaller small site
  let W : E.I₀ → SmallProetale B S hS := fun j ↦ ⟨Over.mk (E.f j ≫ X.obj.hom), hweS j⟩
  let φ : (j : E.I₀) → W j ⟶ X := fun j ↦ ObjectProperty.homMk (Over.homMk (E.f j))
  let F : PreZeroHypercover.{u + 1} X := ⟨E.I₀, W, φ⟩
  refine (SmallProetale.topology B S hS).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE⟩)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨j⟩
  obtain ⟨i, q, hq⟩ := href j
  let q₁ : K'.obj ((h.smallFunctor S hS).obj (W j)) ⟶ K'.obj (E'.X i) :=
    B'.inclusion.preimage
      (show B'.inclusion.obj (K'.obj ((h.smallFunctor S hS).obj (W j))) ⟶
        B'.inclusion.obj (K'.obj (E'.X i)) from q)
  have hq₁ : q₁ ≫ K'.map (E'.f i) = K'.map ((h.smallFunctor S hS).map (φ j)) :=
    B'.inclusion.map_injective (by rwa [Functor.map_comp, B'.inclusion.map_preimage])
  have hw : q₁ ≫ (E'.X i).obj.hom =
      ((h.smallFunctor S hS).obj (W j)).obj.hom := by
    have hover : K'.map (E'.f i) ≫ ((h.smallFunctor S hS).obj X).obj.hom =
        (E'.X i).obj.hom := Over.w _
    rw [← hover, ← Category.assoc, hq₁]
    exact (Over.w ((SmallProetale.inclusion B S hS ⋙ h.functorOver S hS).map (φ j))).symm
  let ψ : (h.smallFunctor S hS).obj (W j) ⟶ E'.X i :=
    ObjectProperty.homMk (Over.homMk q₁ hw)
  have hψ : ψ ≫ E'.f i = (h.smallFunctor S hS).map (φ j) :=
    K'.map_injective (by rwa [Functor.map_comp])
  change R.arrows ((h.smallFunctor S hS).map (φ j))
  rw [← hψ]
  exact R.downward_closed (hE'R _ _ (Presieve.ofArrows.mk i)) ψ


/-- The inclusion of the two small pro-étale sites of `S` preserves covering sieves. -/
private theorem smallFunctor_coverPreserving :
    CoverPreserving (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) (h.smallFunctor S hS) := by
  constructor
  intro X R hR
  obtain ⟨E, hE, hER⟩ := exists_covering_le_of_isSite (SmallProetale.IsCovering B S hS)
    (SmallProetale.isSite B S hS) (SmallProetale.precoverage B S hS) (fun _ _ ↦ Iff.rfl) R hR
  have hmap : SmallProetale.IsCovering B' S (h.contains hS)
      ⟨(h.smallFunctor S hS).obj X, E.map (h.smallFunctor S hS)⟩ :=
    h.covering_map ⟨(smallToBig B S hS).obj X, E.map (smallToBig B S hS)⟩ hE
  refine (SmallProetale.topology B' S (h.contains hS)).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck ⟨E.map (h.smallFunctor S hS), rfl, hmap⟩)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact R.image_mem_functorPushforward (h.smallFunctor S hS) (hER _ _ (Presieve.ofArrows.mk i))

/-- **Stacks 098Y**, hypothesis (b) of Stacks 00XU: the inclusion of the two small pro-étale
sites of `S` is continuous, and in fact defines a morphism of sites.

Continuity follows from cover-preservation because the inclusion is representably flat, being
left exact; the left adjoint of the pushforward on sheaves of sets is the sheafified left Kan
extension, which is left exact for the same reason. -/
@[stacks 098Y
  "hypothesis (b) of 00XU for the inclusion of the small sites: continuity, in the form of
  being a morphism of sites"]
theorem smallFunctor_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (h.smallFunctor S hS)
      (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)) := by
  let : HasFiniteLimits (SmallProetale B S hS) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesFiniteLimits (h.smallFunctor S hS) := h.smallFunctor_preservesFiniteLimits S hS
  let : RepresentablyFlat (h.smallFunctor S hS) :=
    flat_of_preservesFiniteLimits (h.smallFunctor S hS)
  let : (h.smallFunctor S hS).IsContinuous (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ (h.smallFunctor S hS)) (h.smallFunctor_coverPreserving S hS)
  let : PreservesFiniteLimits ((h.smallFunctor S hS).op.lan :
      ((SmallProetale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
        (SmallProetale B' S (h.contains hS))ᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
      (h.smallFunctor S hS)
  exact { __ := (inferInstance : (h.smallFunctor S hS).IsContinuous
            (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)))
          hasExactLeftAdjoint :=
            ⟨(h.smallFunctor S hS).sheafPullback (Type (u + 1))
                (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)),
              ⟨(h.smallFunctor S hS).sheafAdjunctionContinuous (Type (u + 1))
                (SmallProetale.topology B S hS)
                (SmallProetale.topology B' S (h.contains hS))⟩,
              Functor.sheafPullbackConstruction.preservesFiniteLimits (h.smallFunctor S hS)
                (Type (u + 1)) (SmallProetale.topology B S hS)
                (SmallProetale.topology B' S (h.contains hS))⟩ }

/-- **Stacks 098Y**, the conclusion of Stacks 00XU for the two small pro-étale sites of `S`: the
morphisms of topoi `g : Sh(S_proetale) → Sh(S'_proetale)` and `f : Sh(S'_proetale) →
Sh(S_proetale)` induced by the inclusion, whose composite is isomorphic to the identity and
which satisfy `f_* = g^{-1}`.

The direct image of `g` is the cocontinuous pushforward and the direct image of `f` is the
continuous pushforward, which is also the inverse image of `g`; that is the identification
`f_* = g^{-1}`. The retraction is the counit of the adjunction `g^{-1} ⊣ g_*`, invertible
because the inclusion is fully faithful and cocontinuous. -/
@[stacks 098Y
  "the two morphisms of topoi of the small sites, with `f ∘ g` isomorphic to the identity and
  `f_* = g^{-1}`"]
noncomputable def smallToposRetraction :
    letI : (h.smallFunctor S hS).IsCocontinuous (SmallProetale.topology B S hS)
        (SmallProetale.topology B' S (h.contains hS)) := h.smallFunctor_isCocontinuous S hS
    letI : (h.smallFunctor S hS).IsContinuous (SmallProetale.topology B S hS)
        (SmallProetale.topology B' S (h.contains hS)) :=
      (h.smallFunctor_isMorphismOfSites S hS).toIsContinuous
    ToposRetraction (SmallProetale B S hS) (SmallProetale B' S (h.contains hS))
      (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
      (h.smallFunctor S hS) := by
  letI : (h.smallFunctor S hS).IsCocontinuous (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) := h.smallFunctor_isCocontinuous S hS
  letI : (h.smallFunctor S hS).IsContinuous (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) :=
    (h.smallFunctor_isMorphismOfSites S hS).toIsContinuous
  refine ⟨{ pushforward := (h.smallFunctor S hS).sheafPushforwardCocontinuous (Type (u + 1))
              (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
            inverseImage := (h.smallFunctor S hS).sheafPushforwardContinuous (Type (u + 1))
              (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
            adj := (h.smallFunctor S hS).sheafAdjunctionCocontinuous (Type (u + 1))
              (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
            preservesFiniteLimits := inferInstance },
    { pushforward := (h.smallFunctor S hS).sheafPushforwardContinuous (Type (u + 1))
        (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
      inverseImage := (h.smallFunctor S hS).sheafPullback (Type (u + 1))
        (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
      adj := (h.smallFunctor S hS).sheafAdjunctionContinuous (Type (u + 1))
        (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
      preservesFiniteLimits := ?_ },
    Iso.refl _, Iso.refl _, ?_⟩
  · let : HasFiniteLimits (SmallProetale B S hS) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    let : PreservesFiniteLimits (h.smallFunctor S hS) :=
      h.smallFunctor_preservesFiniteLimits S hS
    let : RepresentablyFlat (h.smallFunctor S hS) :=
      flat_of_preservesFiniteLimits (h.smallFunctor S hS)
    let : PreservesFiniteLimits ((h.smallFunctor S hS).op.lan :
        ((SmallProetale B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
          (SmallProetale B' S (h.contains hS))ᵒᵖ ⥤ Type (u + 1)) :=
      CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
        (h.smallFunctor S hS)
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits (h.smallFunctor S hS)
      (Type (u + 1)) (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))
  · letI : IsIso ((h.smallFunctor S hS).sheafAdjunctionCocontinuous (Type (u + 1))
        (SmallProetale.topology B S hS)
        (SmallProetale.topology B' S (h.contains hS))).counit :=
      Functor.isIso_sheafAdjunctionCocontinuous_counit (h.smallFunctor S hS) (Type (u + 1))
        (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
    exact asIso ((h.smallFunctor S hS).sheafAdjunctionCocontinuous (Type (u + 1))
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).counit


/-- The inclusion of the two small pro-étale sites of `S` is continuous. This is the continuity
half of `smallFunctor_isMorphismOfSites`, as an instance, so that the restriction functor on
sheaves is available to instance search. -/
instance smallFunctor_isContinuous :
    (h.smallFunctor S hS).IsContinuous (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS)) :=
  (h.smallFunctor_isMorphismOfSites S hS).toIsContinuous

/-! ### Cohomology

Restriction along the inclusion of the two small pro-étale sites does not change cohomology.
-/

/-- Restriction of abelian sheaves along the inclusion of the two small pro-étale sites of `S`
preserves finite colimits: it is a left adjoint, the inclusion being cocontinuous. -/
instance smallRestriction_preservesFiniteColimits :
    Limits.PreservesFiniteColimits ((h.smallFunctor S hS).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))) :=
  have : Limits.PreservesColimitsOfSize.{0, 0}
      ((h.smallFunctor S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))) :=
    ((h.smallFunctor S hS).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).leftAdjoint_preservesColimits
  Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 04BH for the inclusion of the two small pro-étale sites of `S`.** Lower shriek on
abelian sheaves is left exact, the smaller small site having fibre products and equalizers which
the inclusion preserves. -/
instance smallLowerShriek_preservesFiniteLimits :
    Limits.PreservesFiniteLimits ((h.smallFunctor S hS).sheafPullback AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))) := by
  have : Limits.PreservesFiniteLimits (h.smallFunctor S hS) :=
    h.smallFunctor_preservesFiniteLimits S hS
  have hc : Limits.PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (h.smallFunctor S hS)
        AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
        (SmallProetale.topology B' S (h.contains hS))) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u, u, u + 1, u + 1}
      (h.smallFunctor S hS) (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))
  exact Limits.preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (h.smallFunctor S hS)
      AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).symm

/-- Restriction of abelian sheaves along the inclusion of the two small pro-étale sites of `S`
carries injective sheaves to injective sheaves, being right adjoint to the exact lower
shriek. -/
instance smallRestriction_preservesInjectiveObjects :
    ((h.smallFunctor S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((h.smallFunctor S hS).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)))

/-- **Stacks 098Y, part (1).** For an abelian sheaf `F'` on the larger small pro-étale site of
`S` and every degree `p`,

`H^p(S'_proetale, F') = H^p(S_proetale, g^{-1} F')`,

naturally in `F'`.

This is Stacks 03YU applied to the inclusion: restriction along it is exact and carries
injective abelian sheaves to injective abelian sheaves, because its left adjoint `g_!` is exact
(Stacks 04BH), and it matches the two final objects `S/S`. -/
@[stacks 098Y "part (1): `H^p(S'_proetale, F') = H^p(S_proetale, g^{-1} F')`"]
noncomputable def smallCohomologyRestrictionIso (p : ℕ) :
    (h.smallFunctor S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (SmallProetale.topology B S hS) p ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (SmallProetale.topology B' S (h.contains hS)) p :=
  Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso.{u + 1, u, u + 1}
    (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
    (h.smallFunctor S hS) (smallIdentity_isTerminal B S hS)
    (smallIdentity_isTerminal B' S (h.contains hS)) rfl p

/-- **Stacks 098Y, part (2), first equality.** For an abelian sheaf `F` on the smaller small
pro-étale site of `S` and every degree `p`,

`H^p(S_proetale, F) = H^p(S'_proetale, g_* F)`,

naturally in `F`. This follows from part (1) because `g^{-1} g_* F = F`, the counit of
`g^{-1} ⊣ g_*` being invertible for a fully faithful cocontinuous functor. -/
@[stacks 098Y "part (2), first equality: `H^p(S_proetale, F) = H^p(S'_proetale, g_* F)`"]
noncomputable def smallCohomologyPushforwardIso (p : ℕ) :
    Sheaf.functorH.{u + 1, u + 1, u, u + 1} (SmallProetale.topology B S hS) p ≅
      (h.smallFunctor S hS).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1}
          (SmallProetale.topology B' S (h.contains hS)) p :=
  have : IsIso ((h.smallFunctor S hS).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).counit :=
    Functor.isIso_sheafAdjunctionCocontinuous_counit (h.smallFunctor S hS) AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso ((h.smallFunctor S hS).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (h.smallCohomologyRestrictionIso S hS p)

/-- **Stacks 098Y, part (2), second equality.** For an abelian sheaf `F` on the smaller small
pro-étale site of `S` and every degree `p`,

`H^p(S_proetale, F) = H^p(S'_proetale, f^{-1} F)`,

naturally in `F`. This follows from part (1) because `g^{-1} f^{-1} F = F`: the inverse image
`f^{-1} = g_!` is fully faithful (Stacks 00XU), so the unit of `g_! ⊣ g^{-1}` is invertible. -/
@[stacks 098Y "part (2), second equality: `H^p(S_proetale, F) = H^p(S'_proetale, f^{-1} F)`"]
noncomputable def smallCohomologyLowerShriekIso (p : ℕ) :
    Sheaf.functorH.{u + 1, u + 1, u, u + 1} (SmallProetale.topology B S hS) p ≅
      (h.smallFunctor S hS).sheafPullback AddCommGrpCat.{u + 1}
          (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS)) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1}
          (SmallProetale.topology B' S (h.contains hS)) p :=
  have hff := Functor.full_and_faithful_sheafPullback (h.smallFunctor S hS)
    AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
    (SmallProetale.topology B' S (h.contains hS))
  have : ((h.smallFunctor S hS).sheafPullback AddCommGrpCat.{u + 1}
    (SmallProetale.topology B S hS) (SmallProetale.topology B' S (h.contains hS))).Full := hff.1
  have : ((h.smallFunctor S hS).sheafPullback AddCommGrpCat.{u + 1}
    (SmallProetale.topology B S hS)
    (SmallProetale.topology B' S (h.contains hS))).Faithful := hff.2
  have : IsIso ((h.smallFunctor S hS).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).unit :=
    ((h.smallFunctor S hS).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).unit_isIso_of_L_fully_faithful
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso ((h.smallFunctor S hS).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (SmallProetale.topology B S hS)
      (SmallProetale.topology B' S (h.contains hS))).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (h.smallCohomologyRestrictionIso S hS p)

end BigProetaleSite.IsContainedIn

end AlgebraicGeometry.ProEtale

end
