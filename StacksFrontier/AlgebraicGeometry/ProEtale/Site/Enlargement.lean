module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.PartialUniverseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksCore.Tactic.StacksAttribute

/-!
# Enlarging a big pro-étale site

A chosen big pro-étale site is contained in another when its size cutoff is no larger and each
of its chosen covering families is a chosen covering family of the other. The inclusion functor
of the two underlying categories is then fully faithful, continuous and cocontinuous, it
commutes with fibre products, and it carries the final object `Spec ℤ` of the smaller category
to that of the larger one; that is, it satisfies the hypotheses of Stacks 00XU. Consequently
there are morphisms of topoi in both directions whose composite retracts to the identity, and
the same holds after localizing at a scheme of the smaller site.

## Main definitions

* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn` — containment of one chosen big
  pro-étale site in another, and `IsContainedIn.functor` the resulting inclusion of the
  underlying categories.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.functorOver` — the inclusion of the
  slices over a scheme of the smaller site.

## Main results

* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.fullyFaithfulFunctor`,
  `IsContainedIn.functor_isCocontinuous`, `IsContainedIn.functor_isMorphismOfSites` and
  `IsContainedIn.functor_preservesFiniteLimits` are the hypotheses of Stacks 00XU for the
  inclusion of the big sites, and `IsContainedIn.toposRetraction` is the resulting pair of
  morphisms of topoi together with the retraction of their composite.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.IsContainedIn.fullyFaithfulFunctorOver`,
  `IsContainedIn.functorOver_isCocontinuous`, `IsContainedIn.functorOver_isMorphismOfSites`,
  `IsContainedIn.functorOver_preservesFiniteLimits` and `IsContainedIn.toposRetractionOver` are
  the same statements for the slices over a scheme of the smaller site.

## Implementation notes

The retraction is recorded as `AlgebraicGeometry.ToposRetraction`, whose two pushforward
isomorphisms pin the two morphisms of topoi down to the ones the inclusion induces; in
particular its `f_pushforward_iso` field is the identification `f_* = g^{-1}` of Stacks 00XU.

## References

* [Stacks Project, Tag 0F4S](https://stacks.math.columbia.edu/tag/0F4S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- A scheme below a cutoff is below any larger cutoff. -/
theorem boundedSchemeProperty_le_of_le {κ κ' : Cardinal.{u}} (h : κ ≤ κ') :
    boundedSchemeProperty κ ≤ boundedSchemeProperty κ' := fun _ hX ↦ hX.trans_le h

/-- The full inclusion of the schemes below a cutoff into the schemes below a larger one. -/
abbrev boundedSchemeEnlargement {κ κ' : Cardinal.{u}} (h : κ ≤ κ') :
    BoundedScheme κ ⥤ BoundedScheme κ' :=
  ObjectProperty.ιOfLE (boundedSchemeProperty_le_of_le h)

/-- **A chosen big pro-étale site contained in another.** The cutoff of `B` is at most that of
`B'`, so that the underlying category of `B` is a full subcategory of that of `B'`, and every
chosen covering family of `B` is a chosen covering family of `B'`. -/
structure BigProetaleSite.IsContainedIn (B B' : BigProetaleSite.{u}) : Prop where
  /-- The cutoff of the smaller site is at most that of the larger one. -/
  cutoff_le : B.cutoff ≤ B'.cutoff
  /-- Every chosen covering family of the smaller site is one of the larger site. -/
  covering_map : ∀ E : Covering B.Scheme, B.covering E →
    B'.covering ⟨(boundedSchemeEnlargement cutoff_le).obj E.1,
      E.2.map (boundedSchemeEnlargement cutoff_le)⟩

namespace BigProetaleSite.IsContainedIn

variable {B B' : BigProetaleSite.{u}} (h : B.IsContainedIn B')

/-- The inclusion functor of the underlying categories of two nested chosen big pro-étale
sites. -/
abbrev functor : B.Scheme ⥤ B'.Scheme := boundedSchemeEnlargement h.cutoff_le

/-- A scheme belonging to the smaller of two nested chosen big pro-étale sites belongs to the
larger one. -/
theorem contains (h : B.IsContainedIn B') {S : AlgebraicGeometry.Scheme.{u}}
    (hS : B.Contains S) : B'.Contains S :=
  hS.trans_le h.cutoff_le

/-- Hypothesis (c) of Stacks 00XU for the big sites: the inclusion functor is fully faithful. -/
@[stacks 0F4S "hypothesis (c) of 00XU for the inclusion of the big sites: full faithfulness"]
def fullyFaithfulFunctor : h.functor.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

/-- Hypothesis (a) of Stacks 00XU for the big sites: the inclusion functor is cocontinuous. -/
@[stacks 0F4S "hypothesis (a) of 00XU for the inclusion of the big sites: cocontinuity"]
theorem functor_isCocontinuous : h.functor.IsCocontinuous B.topology B'.topology := by
  constructor
  intro X R hR
  obtain ⟨E', hE', hE'R⟩ := (B'.mem_topology_iff R).mp hR
  have hcov : Presieve.ofArrows (fun j ↦ (E'.X j).obj)
      (fun j ↦ B'.inclusion.map (E'.f j)) ∈
        Scheme.proetalePrecoverage.coverings X.obj :=
    (B'.isProetaleCovering_iff ⟨h.functor.obj X, E'⟩).mp hE'.1
  obtain ⟨E, hE, href⟩ := exists_covering_refining_proetaleCovering B X
    (fun j ↦ (E'.X j).obj) (fun j ↦ B'.inclusion.map (E'.f j)) hcov
  refine (B.mem_topology_iff (R.functorPullback h.functor)).mpr ⟨E, hE, ?_⟩
  rintro _ _ ⟨j⟩
  obtain ⟨i, q, hq⟩ := href j
  let q' : h.functor.obj (E.X j) ⟶ E'.X i := B'.inclusion.preimage
    (show B'.inclusion.obj (h.functor.obj (E.X j)) ⟶ B'.inclusion.obj (E'.X i) from q)
  have hfac : q' ≫ E'.f i = h.functor.map (E.f j) :=
    B'.inclusion.map_injective (by rw [Functor.map_comp, B'.inclusion.map_preimage]; exact hq)
  change R.arrows (h.functor.map (E.f j))
  exact hfac ▸ R.downward_closed (hE'R _ _ (Presieve.ofArrows.mk i)) q'

/-- Hypotheses (d) and (e) of Stacks 00XU for the big sites: fibre products exist in the smaller
category and are preserved by the inclusion, which also carries the final object `Spec ℤ` to the
final object `Spec ℤ`; that is, the inclusion preserves finite limits. -/
@[stacks 0F4S
  "hypotheses (d) and (e) of 00XU for the inclusion of the big sites: preservation of fibre
  products and of the final object"]
theorem functor_preservesFiniteLimits : PreservesFiniteLimits h.functor := by
  have hZ : h.functor.obj (specZObject B) = specZObject B' := rfl
  let : PreservesLimitsOfShape WalkingCospan (h.functor ⋙ B'.inclusion) :=
    preservesLimitsOfShape_of_natIso (ObjectProperty.ιOfLECompιIso _).symm
  let : ReflectsLimitsOfShape WalkingCospan B'.inclusion :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimitsOfShape WalkingCospan h.functor :=
    preservesLimitsOfShape_of_reflects_of_preserves h.functor B'.inclusion
  let : PreservesLimit (Functor.empty.{0} B.Scheme) h.functor :=
    preservesTerminal_of_iso h.functor
      (h.functor.mapIso ((terminalIsTerminal (C := B.Scheme)).uniqueUpToIso
          (specZObject_isTerminal B)) ≪≫ eqToIso hZ ≪≫
        (specZObject_isTerminal B').uniqueUpToIso terminalIsTerminal)
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) h.functor :=
    preservesLimitsOfShape_pempty_of_preservesTerminal h.functor
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks h.functor

/-- The inclusion functor of two nested chosen big pro-étale sites preserves covering sieves. -/
private theorem functor_coverPreserving :
    CoverPreserving B.topology B'.topology h.functor := by
  constructor
  intro X R hR
  obtain ⟨E, hE, hER⟩ := (B.mem_topology_iff R).mp hR
  refine (B'.mem_topology_iff (R.functorPushforward h.functor)).mpr
    ⟨E.map h.functor, h.covering_map ⟨X, E⟩ hE, ?_⟩
  rintro _ _ ⟨i⟩
  exact R.image_mem_functorPushforward h.functor (hER _ _ (Presieve.ofArrows.mk i))

/-- A cover-preserving functor between big sites preserving finite limits is a morphism of
sites. -/
private theorem isMorphismOfSites_of_coverPreserving {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] [HasFiniteLimits C] (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [PreservesFiniteLimits F] (hF : CoverPreserving J K F) :
    _root_.IsMorphismOfSites.{u + 1} F J K := by
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let : F.IsContinuous J K :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat K F) hF
  let : PreservesFiniteLimits (F.op.lan :
      (Cᵒᵖ ⥤ Type (u + 1)) ⥤ Dᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1} F
  exact { hasExactLeftAdjoint :=
    ⟨F.sheafPullback (Type (u + 1)) J K, ⟨F.sheafAdjunctionContinuous (Type (u + 1)) J K⟩,
      Functor.sheafPullbackConstruction.preservesFiniteLimits F (Type (u + 1)) J K⟩ }

/-- Hypothesis (b) of Stacks 00XU for the big sites: the inclusion functor is continuous, and in
fact defines a morphism of sites. -/
@[stacks 0F4S
  "hypothesis (b) of 00XU for the inclusion of the big sites: continuity, in the form of being
  a morphism of sites"]
theorem functor_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} h.functor B.topology B'.topology := by
  let : HasFiniteLimits B.Scheme := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesFiniteLimits h.functor := h.functor_preservesFiniteLimits
  exact isMorphismOfSites_of_coverPreserving h.functor _ _ h.functor_coverPreserving

/-- The conclusion of Stacks 00XU for the big sites: the two morphisms of topoi
`g : Sh(Sch_proetale) → Sh(Sch'_proetale)` and `f : Sh(Sch'_proetale) → Sh(Sch_proetale)`
induced by the inclusion, together with the isomorphism `f ∘ g ≅ id`.

The direct image of `g` is the cocontinuous pushforward and the direct image of `f` is the
continuous pushforward, which is also the inverse image of `g`; this is the identification
`f_* = g^{-1}`. The retraction is the counit of the adjunction `g^{-1} ⊣ g_*`. -/
@[stacks 0F4S
  "the two morphisms of topoi of the big sites, with `f ∘ g` isomorphic to the identity and
  `f_* = g^{-1}`"]
noncomputable def toposRetraction :
    let : h.functor.IsCocontinuous B.topology B'.topology := h.functor_isCocontinuous
    let : h.functor.IsContinuous B.topology B'.topology :=
      h.functor_isMorphismOfSites.toIsContinuous
    ToposRetraction B.Scheme B'.Scheme B.topology B'.topology h.functor := by
  let : h.functor.IsCocontinuous B.topology B'.topology := h.functor_isCocontinuous
  let : h.functor.IsContinuous B.topology B'.topology :=
    h.functor_isMorphismOfSites.toIsContinuous
  refine ⟨{ pushforward := h.functor.sheafPushforwardCocontinuous (Type (u + 1))
              B.topology B'.topology
            inverseImage := h.functor.sheafPushforwardContinuous (Type (u + 1))
              B.topology B'.topology
            adj := h.functor.sheafAdjunctionCocontinuous (Type (u + 1)) B.topology B'.topology
            preservesFiniteLimits := inferInstance },
    { pushforward := h.functor.sheafPushforwardContinuous (Type (u + 1))
        B.topology B'.topology
      inverseImage := h.functor.sheafPullback (Type (u + 1)) B.topology B'.topology
      adj := h.functor.sheafAdjunctionContinuous (Type (u + 1)) B.topology B'.topology
      preservesFiniteLimits := ?_ },
    Iso.refl _, Iso.refl _, ?_⟩
  · let : HasFiniteLimits B.Scheme := hasFiniteLimits_of_hasTerminal_and_pullbacks
    let : PreservesFiniteLimits h.functor := h.functor_preservesFiniteLimits
    let : RepresentablyFlat h.functor := flat_of_preservesFiniteLimits h.functor
    let : PreservesFiniteLimits (h.functor.op.lan :
        (B.Schemeᵒᵖ ⥤ Type (u + 1)) ⥤ B'.Schemeᵒᵖ ⥤ Type (u + 1)) :=
      CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
        h.functor
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits h.functor
      (Type (u + 1)) B.topology B'.topology
  · let : IsIso (h.functor.sheafAdjunctionCocontinuous (Type (u + 1))
        B.topology B'.topology).counit :=
      Functor.isIso_sheafAdjunctionCocontinuous_counit h.functor (Type (u + 1))
        B.topology B'.topology
    exact asIso (h.functor.sheafAdjunctionCocontinuous (Type (u + 1))
      B.topology B'.topology).counit

variable (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S)

/-- The inclusion functor of the slices of two nested chosen big pro-étale sites over a scheme
of the smaller one. -/
abbrev functorOver : BigProetaleOver B S hS ⥤ BigProetaleOver B' S (h.contains hS) :=
  Over.post h.functor

/-- Hypothesis (c) of Stacks 00XU for the slices: the inclusion functor of the slices over `S` is
fully faithful. -/
@[stacks 0F4S "hypothesis (c) of 00XU for the inclusion of the slices: full faithfulness"]
def fullyFaithfulFunctorOver : (h.functorOver S hS).FullyFaithful :=
  Functor.FullyFaithful.over (⟨S, hS⟩ : B.Scheme) h.functor h.fullyFaithfulFunctor

/-- Hypothesis (a) of Stacks 00XU for the slices: the inclusion functor of the slices over `S` is
cocontinuous. -/
@[stacks 0F4S "hypothesis (a) of 00XU for the inclusion of the slices: cocontinuity"]
theorem functorOver_isCocontinuous :
    (h.functorOver S hS).IsCocontinuous (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS)) := by
  let : h.functor.IsCocontinuous B.topology B'.topology := h.functor_isCocontinuous
  exact inferInstanceAs ((Over.post (X := (⟨S, hS⟩ : B.Scheme)) h.functor).IsCocontinuous
    (B.topology.over (⟨S, hS⟩ : B.Scheme))
    (B'.topology.over (h.functor.obj (⟨S, hS⟩ : B.Scheme))))

/-- Hypotheses (d) and (e) of Stacks 00XU for the slices: the inclusion functor of the slices
over `S` preserves finite limits. -/
@[stacks 0F4S
  "hypotheses (d) and (e) of 00XU for the inclusion of the slices: preservation of fibre
  products and of the final object"]
theorem functorOver_preservesFiniteLimits : PreservesFiniteLimits (h.functorOver S hS) := by
  let : PreservesFiniteLimits h.functor := h.functor_preservesFiniteLimits
  exact inferInstanceAs (PreservesFiniteLimits (Over.post (X := (⟨S, hS⟩ : B.Scheme)) h.functor))

/-- Hypothesis (b) of Stacks 00XU for the slices: the inclusion functor of the slices over `S` is
continuous, and in fact defines a morphism of sites. -/
@[stacks 0F4S
  "hypothesis (b) of 00XU for the inclusion of the slices: continuity, in the form of being a
  morphism of sites"]
theorem functorOver_isMorphismOfSites :
    _root_.IsMorphismOfSites.{u + 1} (h.functorOver S hS)
      (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS)) := by
  let : HasFiniteLimits B.Scheme := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : HasFiniteLimits (BigProetaleOver B S hS) := inferInstance
  let : PreservesFiniteLimits (h.functorOver S hS) := h.functorOver_preservesFiniteLimits S hS
  exact isMorphismOfSites_of_coverPreserving (h.functorOver S hS) _ _
    (h.functor_coverPreserving.overPost (⟨S, hS⟩ : B.Scheme))


/-- The conclusion of Stacks 00XU for the slices: the two morphisms of topoi
`g : Sh((Sch/S)_proetale) → Sh((Sch'/S)_proetale)` and `f` in the other direction induced by the
inclusion of the slices over `S`, together with the isomorphism `f ∘ g ≅ id`. -/
@[stacks 0F4S
  "the two morphisms of topoi of the slices, with `f ∘ g` isomorphic to the identity and
  `f_* = g^{-1}`"]
noncomputable def toposRetractionOver :
    let : (h.functorOver S hS).IsCocontinuous (BigProetaleOver.topology B S hS)
        (BigProetaleOver.topology B' S (h.contains hS)) := h.functorOver_isCocontinuous S hS
    let : (h.functorOver S hS).IsContinuous (BigProetaleOver.topology B S hS)
        (BigProetaleOver.topology B' S (h.contains hS)) :=
      (h.functorOver_isMorphismOfSites S hS).toIsContinuous
    ToposRetraction (BigProetaleOver B S hS) (BigProetaleOver B' S (h.contains hS))
      (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
      (h.functorOver S hS) := by
  let : (h.functorOver S hS).IsCocontinuous (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS)) := h.functorOver_isCocontinuous S hS
  let : (h.functorOver S hS).IsContinuous (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS)) :=
    (h.functorOver_isMorphismOfSites S hS).toIsContinuous
  let : (h.functorOver S hS).Full := (h.fullyFaithfulFunctorOver S hS).full
  let : (h.functorOver S hS).Faithful := (h.fullyFaithfulFunctorOver S hS).faithful
  refine ⟨{ pushforward := (h.functorOver S hS).sheafPushforwardCocontinuous (Type (u + 1))
              (BigProetaleOver.topology B S hS)
              (BigProetaleOver.topology B' S (h.contains hS))
            inverseImage := (h.functorOver S hS).sheafPushforwardContinuous (Type (u + 1))
              (BigProetaleOver.topology B S hS)
              (BigProetaleOver.topology B' S (h.contains hS))
            adj := (h.functorOver S hS).sheafAdjunctionCocontinuous (Type (u + 1))
              (BigProetaleOver.topology B S hS)
              (BigProetaleOver.topology B' S (h.contains hS))
            preservesFiniteLimits := inferInstance },
    { pushforward := (h.functorOver S hS).sheafPushforwardContinuous (Type (u + 1))
        (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
      inverseImage := (h.functorOver S hS).sheafPullback (Type (u + 1))
        (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
      adj := (h.functorOver S hS).sheafAdjunctionContinuous (Type (u + 1))
        (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
      preservesFiniteLimits := ?_ },
    Iso.refl _, Iso.refl _, ?_⟩
  · let : HasFiniteLimits B.Scheme := hasFiniteLimits_of_hasTerminal_and_pullbacks
    let : HasFiniteLimits (BigProetaleOver B S hS) := inferInstance
    let : PreservesFiniteLimits (h.functorOver S hS) := h.functorOver_preservesFiniteLimits S hS
    let : RepresentablyFlat (h.functorOver S hS) :=
      flat_of_preservesFiniteLimits (h.functorOver S hS)
    let : PreservesFiniteLimits ((h.functorOver S hS).op.lan :
        ((BigProetaleOver B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
          (BigProetaleOver B' S (h.contains hS))ᵒᵖ ⥤ Type (u + 1)) :=
      CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u + 1, u + 1}
        (h.functorOver S hS)
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits (h.functorOver S hS)
      (Type (u + 1)) (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS))
  · let : IsIso ((h.functorOver S hS).sheafAdjunctionCocontinuous (Type (u + 1))
        (BigProetaleOver.topology B S hS)
        (BigProetaleOver.topology B' S (h.contains hS))).counit :=
      Functor.isIso_sheafAdjunctionCocontinuous_counit (h.functorOver S hS) (Type (u + 1))
        (BigProetaleOver.topology B S hS) (BigProetaleOver.topology B' S (h.contains hS))
    exact asIso ((h.functorOver S hS).sheafAdjunctionCocontinuous (Type (u + 1))
      (BigProetaleOver.topology B S hS)
      (BigProetaleOver.topology B' S (h.contains hS))).counit

end BigProetaleSite.IsContainedIn

end AlgebraicGeometry.ProEtale

end
