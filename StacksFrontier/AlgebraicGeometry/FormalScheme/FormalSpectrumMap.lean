module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleLimit

/-!
# The formal spectrum of a continuous ring map

A continuous homomorphism `φ : A → B` of pre-admissible topological rings induces a morphism
`Spf φ : Spf B → Spf A` of presheafed spaces of topological rings: on points it takes an open
prime `q` of `B` to the open prime `φ⁻¹(q)` of `A`, and on sections it is assembled from the maps
`Spec (B/J) → Spec (A/I)` attached to the pairs of ideals of definition with `I ⊆ φ⁻¹(J)`.

## Main definitions

* `AlgebraicGeometry.spfMapBase`: the map of spaces `Spf B → Spf A`.
* `AlgebraicGeometry.spfPullbackIdeal` and `AlgebraicGeometry.spfPullbackFunctor`: the ideal of
  definition `I₀ ⊓ φ⁻¹(J)` of `A` attached to an ideal of definition `J` of `B`, and the induced
  monotone map of index posets.
* `AlgebraicGeometry.spfComponentMap`: for ideals of definition `I` of `A` and `J` of `B` with
  `I ⊆ φ⁻¹(J)`, the induced map `𝒪^A_I → (Spf φ)_* 𝒪^B_J` of sheaves of rings on `Spf A`.
* `AlgebraicGeometry.spfMap`: the morphism `Spf φ : Spf B → Spf A` of presheafed spaces of
  topological rings.

## Main results

* `TopologicalRing.isIdealOfDefinition_inf_comap`: for `J` an open ideal of `B` and `I₀` an ideal
  of definition of `A`, the ideal `I₀ ⊓ φ⁻¹(J)` is an ideal of definition of `A` contained in
  `φ⁻¹(J)`; this is what makes the index posets comparable.
* `AlgebraicGeometry.spfTransition_comp_spfComponentMap` and
  `AlgebraicGeometry.spfComponentMap_comp_spfTransition`: the induced maps of sheaves are
  compatible with the transition maps of both inverse systems, so they depend on `I` only through
  the inequality `I ⊆ φ⁻¹(J)`.
* `AlgebraicGeometry.continuous_pseudoDiscrete_pushforward`: on a space with a basis of
  quasi-compact opens every map of presheaves of rings into a pushforward is automatically
  continuous for the pseudo-discrete topologies.
* `AlgebraicGeometry.spfMap_eq`: `Spf φ` does not depend on the chosen ideal of definition `I₀`
  of `A`, so it is canonically attached to `φ`.

## Implementation notes

The structure presheaf of a formal spectrum is a limit over the ideals of definition, and `φ`
runs between rings with different index posets. The choice of index comparison is made canonical
by fixing one ideal of definition `I₀` of `A` and sending `J` to `I₀ ⊓ φ⁻¹(J)`, which is monotone
in `J` and therefore a functor; `AlgebraicGeometry.spfComponentMap` is stated for an arbitrary
`I` with `I ⊆ φ⁻¹(J)`, so the two compatibility results above express that the resulting map on
limits does not see the choice beyond that inequality. The relevant codirectedness of the index
poset is that the intersection of two ideals of definition is again one, which is
`TopologicalRing.IsIdealOfDefinition.inf`.

The comparison map on sections is built at the level of presheaves rather than one open at a
time: pushing a presheaf forward is precomposition with a functor, hence preserves limits, so the
map is the composite of `CategoryTheory.Limits.limit.pre` along the index comparison with
`CategoryTheory.Limits.limMap` of the maps of sheaves. No naturality in the open set has to be
checked by hand.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

/-- On a space with a basis of quasi-compact opens, a compact subset of an open set is contained
in a quasi-compact open contained in that open set: cover it by basic opens and take a finite
subcover. -/
theorem exists_isCompact_opens_subset {X : Type u} [TopologicalSpace X] [PrespectralSpace X]
    {K : Set X} {U : Opens X} (hK : IsCompact K) (hKU : K ⊆ (U : Set X)) :
    ∃ V : Opens X, IsCompact (V : Set X) ∧ V ≤ U ∧ K ⊆ (V : Set X) := by
  classical
  have hcover : K ⊆ ⋃ V : {V : Opens X // IsCompact (V : Set X) ∧ V ≤ U}, (V.1 : Set X) := by
    intro point hpoint
    obtain ⟨small, ⟨hopen, hcompact⟩, hpointSmall, hsmall⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hKU hpoint) U.isOpen
    exact Set.mem_iUnion.2 ⟨⟨⟨small, hopen⟩, hcompact, hsmall⟩, hpointSmall⟩
  obtain ⟨finiteCover, hfiniteCover⟩ := hK.elim_finite_subcover
    (fun V : {V : Opens X // IsCompact (V : Set X) ∧ V ≤ U} => (V.1 : Set X))
    (fun V => V.1.isOpen) hcover
  refine ⟨⨆ V ∈ finiteCover, V.1, ?_, iSup₂_le fun V _ => V.2.2, ?_⟩
  · simpa only [Opens.coe_iSup] using finiteCover.isCompact_biUnion fun V _ => V.2.1
  · intro point hpoint
    obtain ⟨V, hV⟩ := Set.mem_iUnion.1 (hfiniteCover hpoint)
    obtain ⟨hmem, hpointV⟩ := Set.mem_iUnion.1 hV
    exact Opens.mem_iSup.2 ⟨V, Opens.mem_iSup.2 ⟨hmem, hpointV⟩⟩

namespace Ideal

/-- Factoring through a larger ideal before mapping to a quotient of the target is the same as
mapping to that quotient directly. -/
theorem quotientMap_comp_factor {R S : Type u} [CommRing R] [CommRing S] {I I' : Ideal R}
    (J : Ideal S) (f : R →+* S) (h : I ≤ I') (hI' : I' ≤ Ideal.comap f J) :
    (Ideal.quotientMap J f hI').comp (Ideal.Quotient.factor h)
      = Ideal.quotientMap J f (h.trans hI') :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- Mapping to a quotient of the target and then factoring through a larger ideal there is the
same as mapping to the larger quotient directly. -/
theorem factor_comp_quotientMap {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R}
    {J J' : Ideal S} (f : R →+* S) (hI : I ≤ Ideal.comap f J) (h : J ≤ J') :
    (Ideal.Quotient.factor h).comp (Ideal.quotientMap J f hI)
      = Ideal.quotientMap J' f (hI.trans (Ideal.comap_mono h)) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

end Ideal

namespace TopologicalRing

/-- Given an ideal of definition `I` of `A`, an open ideal `J` of `B` and a continuous ring map
`φ : A → B`, the ideal `I ⊓ φ⁻¹(J)` is an ideal of definition of `A` contained in `φ⁻¹(J)`. This
is the pre-admissibility step that lets a continuous ring map be compared on the inverse systems
of the two formal spectra. -/
theorem isIdealOfDefinition_inf_comap {A : Type u} [CommRing A] [TopologicalSpace A]
    {B : Type u} [CommRing B] [TopologicalSpace B] {φ : A →+* B} (hφ : Continuous φ)
    {I : Ideal A} (hI : IsIdealOfDefinition I) {J : Ideal B} (hJ : IsOpen (J : Set B)) :
    IsIdealOfDefinition (I ⊓ Ideal.comap φ J) :=
  hI.inf_of_isOpen (hφ.isOpen_preimage _ hJ)

end TopologicalRing

namespace AlgebraicGeometry

namespace StructureSheaf

/-- The comparison map of the structure sheaves attached to a ring homomorphism depends on the
homomorphism only through its value, the containment of opens being a proposition. -/
theorem comap_congr {R S : Type u} [CommRing R] [CommRing S] {f g : R →+* S} (hfg : f = g)
    (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hf : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hg : ∀ p ∈ V, PrimeSpectrum.comap g p ∈ U) :
    comap f U V hf = comap g U V hg := by
  subst hfg
  rfl

end StructureSheaf

open TopologicalRing

/-- The comparison map of structure sheaves of a composite of ring homomorphisms is the composite
of the comparison maps. -/
private theorem comap_eq_comp_comap {R S P : Type u} [CommRing R] [CommRing S] [CommRing P]
    {f : R →+* S} {g : S →+* P} {h : R →+* P} (e : g.comp f = h)
    (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (W : Opens (PrimeSpectrum.Top P)) (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U)
    (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) (hUW : ∀ p ∈ W, PrimeSpectrum.comap h p ∈ U) :
    StructureSheaf.comap h U W hUW = (StructureSheaf.comap g V W hVW).comp
      (StructureSheaf.comap f U V hUV) := by
  subst e
  exact StructureSheaf.comap_comp ..

/-! ### Pseudo-discrete presheaves and pushforward -/

/-- On a space with a basis of quasi-compact opens, the component of a map of presheaves of rings
into a pushforward is continuous for the pseudo-discrete topologies: a quasi-compact open of the
source space has compact image, which sits inside a quasi-compact open of the target space,
through whose discrete ring of sections the map factors. -/
theorem continuous_pseudoDiscrete_pushforward {Y Z : TopCat.{u}} [PrespectralSpace Z]
    (g : Y ⟶ Z) {F : Y.Presheaf CommRingCat.{u}} {G : Z.Presheaf CommRingCat.{u}}
    (α : G ⟶ g _* F) (V : Opens Z) :
    Continuous[pseudoDiscreteTopology G V, pseudoDiscreteTopology F ((Opens.map g).obj V)]
      (α.app (op V)).hom := by
  refine continuous_iInf_rng.2 fun W => continuous_induced_rng.2 ?_
  obtain ⟨V', hV'compact, hV'le, hWV'⟩ := exists_isCompact_opens_subset
    (W.2.1.image g.hom.continuous)
    (show g.hom '' (W.1 : Set Y) ⊆ (V : Set Z) from
      Set.image_subset_iff.2 fun _ hx => W.2.2 hx)
  have hWle' : W.1 ≤ (Opens.map g).obj V' := fun x hx => hWV' ⟨x, hx, rfl⟩
  have heq : (F.map (homOfLE W.2.2).op).hom.comp (α.app (op V)).hom
      = (F.map (homOfLE hWle').op).hom.comp
          ((α.app (op V')).hom.comp (G.map (homOfLE hV'le).op).hom) := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      α.naturality, Category.assoc]
    show (α.app (op V) ≫ F.map _).hom = (α.app (op V) ≫ F.map _ ≫ F.map _).hom
    rw [← F.map_comp]
    congr 2
  show Continuous[pseudoDiscreteTopology G V, ⊥]
    ((F.map (homOfLE W.2.2).op).hom.comp (α.app (op V)).hom)
  rw [heq]
  let _ : TopologicalSpace (G.obj (op V)) := pseudoDiscreteTopology G V
  let _ : TopologicalSpace (G.obj (op V')) := ⊥
  let _ : TopologicalSpace (F.obj (op W.1)) := ⊥
  exact (@continuous_of_discreteTopology _ ⊥ (discreteTopology_bot _) _ ⊥
    ((F.map (homOfLE hWle').op).hom.comp (α.app (op V')).hom)).comp
    (continuous_pseudoDiscreteTopology_restrict G hV'compact hV'le)

/-- A map of presheaves of rings into a pushforward, pseudo-discretised: on a space with a basis
of quasi-compact opens no continuity condition is lost, by
`AlgebraicGeometry.continuous_pseudoDiscrete_pushforward`. -/
def pseudoDiscretePushforward {Y Z : TopCat.{u}} [PrespectralSpace Z] (g : Y ⟶ Z)
    {F : Y.Presheaf CommRingCat.{u}} {G : Z.Presheaf CommRingCat.{u}} (α : G ⟶ g _* F) :
    pseudoDiscrete G ⟶ g _* pseudoDiscrete F where
  app V := ⟨(α.app V).hom, continuous_pseudoDiscrete_pushforward g α V.unop⟩
  naturality _ _ i := Subtype.ext (congrArg CommRingCat.Hom.hom (α.naturality i))

/-- The pseudo-discretisation of a map of presheaves of rings into a pushforward is determined by
the map itself. -/
@[simp]
theorem pseudoDiscretePushforward_app_val {Y Z : TopCat.{u}} [PrespectralSpace Z] (g : Y ⟶ Z)
    {F : Y.Presheaf CommRingCat.{u}} {G : Z.Presheaf CommRingCat.{u}} (α : G ⟶ g _* F)
    (V : (Opens Z)ᵒᵖ) : ((pseudoDiscretePushforward g α).app V).1 = (α.app V).hom := rfl

/-! ### The formal spectrum of a continuous ring map -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- The preimage of an open prime under a continuous ring map is an open prime. -/
theorem comap_mem_openPrimes {φ : A →+* B} (hφ : Continuous φ) (q : openPrimes B) :
    PrimeSpectrum.comap φ q.1 ∈ openPrimes A :=
  hφ.isOpen_preimage _ q.2

/-- The map of spaces underlying `Spf φ`: an open prime `q` of `B` goes to the open prime
`φ⁻¹(q)` of `A`, which is the restriction to the open primes of `Spec φ`. -/
def spfMapBase {φ : A →+* B} (hφ : Continuous φ) : spfSpace B ⟶ spfSpace A :=
  TopCat.ofHom ⟨fun q => ⟨PrimeSpectrum.comap φ q.1, comap_mem_openPrimes A B hφ q⟩,
    ((PrimeSpectrum.continuous_comap φ).comp continuous_subtype_val).subtype_mk _⟩

/-- On sections the transition map of the inverse system defining `𝒪_{Spf A}` is the comparison
map of the structure sheaves of `Spec (A/I)` and `Spec (A/J)`. -/
theorem spfTransition_app {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1)
    (V : Opens (spfSpace A)) :
    ((spfTransition A h).app (op V)).hom
      = StructureSheaf.comap (Ideal.Quotient.factor h)
          ((Opens.map (spfOfQuotient A I)).obj V) ((Opens.map (spfOfQuotient A J)).obj V)
          (fun _ hx => hx) := rfl

variable {φ : A →+* B} (hφ : Continuous φ)

/-- For ideals of definition `I` of `A` and `J` of `B` with `I ⊆ φ⁻¹(J)`, the induced map
`𝒪^A_I → (Spf φ)_* 𝒪^B_J` of sheaves of rings on `Spf A`: the comparison map of the morphism
`Spec (B/J) → Spec (A/I)` induced by `φ`, pushed forward to `Spf A`. No transport is needed, the
square of spectra over `Spf A` commuting definitionally. -/
noncomputable def spfComponentMap (J : IdealsOfDefinition B) (I : IdealsOfDefinition A)
    (hI : I.1 ≤ Ideal.comap φ J.1) :
    spfComponent A I ⟶ (spfMapBase A B hφ) _* spfComponent B J :=
  Functor.whiskerLeft _ (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI))).c

/-- On sections the induced map `𝒪^A_I → (Spf φ)_* 𝒪^B_J` is the comparison map of the structure
sheaves of `Spec (A/I)` and `Spec (B/J)`. -/
theorem spfComponentMap_app (J : IdealsOfDefinition B) (I : IdealsOfDefinition A)
    (hI : I.1 ≤ Ideal.comap φ J.1) (V : Opens (spfSpace A)) :
    ((spfComponentMap A B hφ J I hI).app (op V)).hom
      = StructureSheaf.comap (Ideal.quotientMap J.1 φ hI)
          ((Opens.map (spfOfQuotient A I)).obj V)
          ((Opens.map (spfOfQuotient B J)).obj ((Opens.map (spfMapBase A B hφ)).obj V))
          (fun _ hx => hx) := rfl

/-- The induced maps of sheaves are compatible with the transition maps of the inverse system of
`A`: shrinking the ideal of definition of `A` and then mapping to `𝒪^B_J` is mapping to `𝒪^B_J`
directly. -/
theorem spfTransition_comp_spfComponentMap (J : IdealsOfDefinition B)
    {I I' : IdealsOfDefinition A} (h : I.1 ≤ I'.1) (hI' : I'.1 ≤ Ideal.comap φ J.1) :
    spfTransition A h ≫ spfComponentMap A B hφ J I' hI'
      = spfComponentMap A B hφ J I (h.trans hI') := by
  refine NatTrans.ext (funext fun V => CommRingCat.hom_ext ?_)
  exact (comap_eq_comp_comap (Ideal.quotientMap_comp_factor J.1 φ h hI') ..).symm

/-- The induced maps of sheaves are compatible with the transition maps of the inverse system of
`B`: mapping to `𝒪^B_J` and then enlarging the ideal of definition of `B` is mapping to
`𝒪^B_{J'}` directly. -/
theorem spfComponentMap_comp_spfTransition (I : IdealsOfDefinition A)
    {J J' : IdealsOfDefinition B} (hI : I.1 ≤ Ideal.comap φ J.1) (h : J.1 ≤ J'.1) :
    spfComponentMap A B hφ J I hI ≫
        Functor.whiskerLeft (Opens.map (spfMapBase A B hφ)).op (spfTransition B h)
      = spfComponentMap A B hφ J' I (hI.trans (Ideal.comap_mono h)) := by
  refine NatTrans.ext (funext fun V => CommRingCat.hom_ext ?_)
  exact (comap_eq_comp_comap (Ideal.factor_comp_quotientMap φ hI h) ..).symm

/-- The pseudo-discretised form of `AlgebraicGeometry.spfTransition_comp_spfComponentMap`:
shrinking the ideal of definition of `A` before mapping to `𝒪^B_J` changes nothing. -/
theorem pseudoDiscretePushforward_spfComponentMap_comp [PrespectralSpace (spfSpace A)]
    (J : IdealsOfDefinition B) {I I' : IdealsOfDefinition A} (h : I.1 ≤ I'.1)
    (hI' : I'.1 ≤ Ideal.comap φ J.1) :
    (spfDiagram A ⋙ pseudoDiscreteFunctor).map (homOfLE h) ≫
        pseudoDiscretePushforward (spfMapBase A B hφ) (spfComponentMap A B hφ J I' hI')
      = pseudoDiscretePushforward (spfMapBase A B hφ)
          (spfComponentMap A B hφ J I (h.trans hI')) :=
  NatTrans.ext (funext fun V => Subtype.ext (congrArg CommRingCat.Hom.hom
    (congrFun (congrArg NatTrans.app
      (spfTransition_comp_spfComponentMap A B hφ J h hI')) V)))

variable (I₀ : IdealsOfDefinition A)

/-- The ideal of definition `I₀ ⊓ φ⁻¹(J)` of `A` attached to an ideal of definition `J` of `B`:
the canonical choice, once `I₀` is fixed, of an ideal of definition of `A` contained in
`φ⁻¹(J)`. -/
def spfPullbackIdeal (J : IdealsOfDefinition B) : IdealsOfDefinition A :=
  ⟨I₀.1 ⊓ Ideal.comap φ J.1,
    TopologicalRing.isIdealOfDefinition_inf_comap hφ I₀.2 J.2.1⟩

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- The ideal of definition `I₀ ⊓ φ⁻¹(J)` is contained in `φ⁻¹(J)`. -/
theorem spfPullbackIdeal_le (J : IdealsOfDefinition B) :
    (spfPullbackIdeal A B hφ I₀ J).1 ≤ Ideal.comap φ J.1 := inf_le_right

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- Enlarging the ideal of definition of `B` enlarges `I₀ ⊓ φ⁻¹(J)`, so the choice is monotone
and hence a map of index posets. -/
theorem monotone_spfPullbackIdeal : Monotone (spfPullbackIdeal A B hφ I₀) :=
  fun _ _ h => inf_le_inf_left _ (Ideal.comap_mono h)

/-- The comparison of index posets attached to `φ` and `I₀`: the functor sending an ideal of
definition `J` of `B` to the ideal of definition `I₀ ⊓ φ⁻¹(J)` of `A`. -/
def spfPullbackFunctor : IdealsOfDefinition B ⥤ IdealsOfDefinition A :=
  (monotone_spfPullbackIdeal A B hφ I₀).functor

variable (hA : IsPreAdmissible A)

/-- The map of inverse systems underlying `Spf φ` on sections: over the comparison of index
posets, the induced maps `𝒪^A_{I₀ ⊓ φ⁻¹(J)} → (Spf φ)_* 𝒪^B_J` of pseudo-discrete sheaves of
topological rings. -/
noncomputable def spfDiagramMap :
    spfPullbackFunctor A B hφ I₀ ⋙ (spfDiagram A ⋙ pseudoDiscreteFunctor)
      ⟶ (spfDiagram B ⋙ pseudoDiscreteFunctor) ⋙
          TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ) :=
  letI := prespectralSpace_spfSpace_of_isWeaklyPreAdmissible A
    (isWeaklyPreAdmissible_of_isPreAdmissible hA)
  { app := fun J => pseudoDiscretePushforward (spfMapBase A B hφ)
      (spfComponentMap A B hφ J (spfPullbackIdeal A B hφ I₀ J)
        (spfPullbackIdeal_le A B hφ I₀ J))
    naturality := fun _ _ h => NatTrans.ext (funext fun V => Subtype.ext
      (congrArg CommRingCat.Hom.hom (congrFun (congrArg NatTrans.app
        ((spfTransition_comp_spfComponentMap A B hφ _
            (monotone_spfPullbackIdeal A B hφ I₀ (leOfHom h)) _).trans
          (spfComponentMap_comp_spfTransition A B hφ _ _ (leOfHom h)).symm)) V))) }

/-- The map of inverse limits induced by `Spf φ`: the comparison of index posets followed by the
induced maps of sheaves. -/
noncomputable def spfLimitMap :
    limit (spfDiagram A ⋙ pseudoDiscreteFunctor) ⟶
      limit ((spfDiagram B ⋙ pseudoDiscreteFunctor) ⋙
        TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ)) :=
  limit.pre (spfDiagram A ⋙ pseudoDiscreteFunctor) (spfPullbackFunctor A B hφ I₀)
    ≫ limMap (spfDiagramMap A B hφ I₀ hA)

/-- The comparison map on sections underlying `Spf φ`:
`𝒪_{Spf A} → (Spf φ)_* 𝒪_{Spf B}`. Pushing forward preserves limits, so it is the map of limits
`AlgebraicGeometry.spfLimitMap` read through that identification. -/
noncomputable def spfMapC : spfPresheaf A ⟶ (spfMapBase A B hφ) _* spfPresheaf B :=
  letI : PreservesLimitsOfShape (IdealsOfDefinition B)
      (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ)) :=
    whiskeringLeft_preservesLimitsOfShape (IdealsOfDefinition B)
      (Opens.map (spfMapBase A B hφ)).op
  spfLimitMap A B hφ I₀ hA
    ≫ (preservesLimitIso (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ))
        (spfDiagram B ⋙ pseudoDiscreteFunctor)).inv

/-- `Spf` on morphisms: the morphism `Spf φ : Spf B → Spf A` of presheafed spaces of topological
rings induced by a continuous ring map `φ : A → B`, for `A` pre-admissible. On points it is
`q ↦ φ⁻¹(q)` and on sections it is `AlgebraicGeometry.spfMapC`. -/
noncomputable def spfMap : Spf B ⟶ Spf A where
  base := spfMapBase A B hφ
  c := spfMapC A B hφ I₀ hA

/-! ### Independence of the comparison of index posets -/

/-- The map of inverse limits induced by `Spf φ` does not depend on the chosen ideal of
definition `I₀` of `A`: for a second choice `I₀'` the two maps agree after composing with each
projection, because both factor through the intersection
`(I₀ ⊓ φ⁻¹(J)) ⊓ (I₀' ⊓ φ⁻¹(J))`, again an ideal of definition contained in `φ⁻¹(J)`. -/
theorem spfLimitMap_eq (I₀ I₀' : IdealsOfDefinition A) :
    spfLimitMap A B hφ I₀ hA = spfLimitMap A B hφ I₀' hA := by
  let := prespectralSpace_spfSpace_of_isWeaklyPreAdmissible A
    (isWeaklyPreAdmissible_of_isPreAdmissible hA)
  refine limit.hom_ext fun J => ?_
  let K : IdealsOfDefinition A := ⟨(spfPullbackIdeal A B hφ I₀ J).1 ⊓
    (spfPullbackIdeal A B hφ I₀' J).1,
    (spfPullbackIdeal A B hφ I₀ J).2.inf (spfPullbackIdeal A B hφ I₀' J).2⟩
  have step (I₁ : IdealsOfDefinition A) (hK : K.1 ≤ (spfPullbackIdeal A B hφ I₁ J).1) :
      spfLimitMap A B hφ I₁ hA ≫ limit.π ((spfDiagram B ⋙ pseudoDiscreteFunctor) ⋙
          TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ)) J
        = limit.π (spfDiagram A ⋙ pseudoDiscreteFunctor) K
          ≫ pseudoDiscretePushforward (spfMapBase A B hφ)
              (spfComponentMap A B hφ J K (hK.trans (spfPullbackIdeal_le A B hφ I₁ J))) := by
    rw [spfLimitMap, Category.assoc, limMap_π, ← Category.assoc, limit.pre_π]
    exact (congrArg (fun m => m ≫ (spfDiagramMap A B hφ I₁ hA).app J)
        (limit.w (spfDiagram A ⋙ pseudoDiscreteFunctor) (homOfLE hK)).symm).trans
      ((Category.assoc _ _ _).trans (congrArg
        (fun m => limit.π (spfDiagram A ⋙ pseudoDiscreteFunctor) K ≫ m)
        (pseudoDiscretePushforward_spfComponentMap_comp A B hφ J hK
          (spfPullbackIdeal_le A B hφ I₁ J))))
  rw [step I₀ inf_le_left, step I₀' inf_le_right]

/-- The comparison map on sections of `Spf φ` does not depend on the chosen ideal of definition
`I₀` of `A`. -/
theorem spfMapC_eq (I₀ I₀' : IdealsOfDefinition A) :
    spfMapC A B hφ I₀ hA = spfMapC A B hφ I₀' hA := by
  show spfLimitMap A B hφ I₀ hA ≫ _ = spfLimitMap A B hφ I₀' hA ≫ _
  rw [spfLimitMap_eq A B hφ hA I₀ I₀']

/-- `Spf φ` does not depend on the chosen ideal of definition `I₀` of `A`, so it is canonically
attached to the continuous ring map `φ`. -/
theorem spfMap_eq (I₀ I₀' : IdealsOfDefinition A) :
    spfMap A B hφ I₀ hA = spfMap A B hφ I₀' hA :=
  congrArg (fun k => (⟨spfMapBase A B hφ, k⟩ : Spf B ⟶ Spf A))
    (spfMapC_eq A B hφ hA I₀ I₀')

/-- The map of spaces underlying `Spf φ` is `AlgebraicGeometry.spfMapBase`. -/
@[simp]
theorem spfMap_base : (spfMap A B hφ I₀ hA).base = spfMapBase A B hφ := rfl

/-- The comparison map on sections of `Spf φ` is `AlgebraicGeometry.spfMapC`. -/
@[simp]
theorem spfMap_c : (spfMap A B hφ I₀ hA).c = spfMapC A B hφ I₀ hA := rfl

end

end AlgebraicGeometry
