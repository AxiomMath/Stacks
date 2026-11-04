module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumBasicOpen
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumBijection
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global sections of the formal spectrum of an admissible ring

For an admissible topological ring `A` the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` is an
isomorphism of topological rings. This is the case `f = 1` of the source's deferred verification
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}`, and it is where completeness of `A` enters: the
sections of `𝒪_{Spf A} = lim 𝒪_λ` over the whole space are the limit of the discrete rings
`A/I_λ`, and an admissible ring *is* that limit.

## Main definitions

* `AlgebraicGeometry.spfGammaResidueOn`: the residue of a global section of `𝒪_{Spf A}` in `A/I`,
  its image in `𝒪_I` read through the identification `Γ(Spec (A/I), 𝒪) = A/I`.
* `AlgebraicGeometry.spfGammaEquiv`: the canonical map as a ring isomorphism.
* `AlgebraicGeometry.spfGammaIso`: the identification `A = Γ(Spf A, 𝒪_{Spf A})` of topological
  rings.
* `AlgebraicGeometry.ltrsGlobalSectionsRingHom` and
  `AlgebraicGeometry.ltrsGlobalSectionsTopHom`: the continuous ring homomorphism `A → B`
  recovered from a morphism `Spf B → Spf A` of locally topologically ringed spaces.

## Main results

* `AlgebraicGeometry.isIso_spfGammaHom` and `AlgebraicGeometry.spfGammaIso`: **Stacks 0AHY**, the
  identification `Γ(Spf A, 𝒪_{Spf A}) = A` for an admissible topological ring.
* `AlgebraicGeometry.isIso_spfGammaHomOn`: the same identification for the formal spectrum taken
  along any fundamental system of ideals of a complete separated topological ring.
* `AlgebraicGeometry.isIso_spfwGammaHom` and `AlgebraicGeometry.spfwGammaIso`: **Stacks 0AI3**.
  The counterpart `Γ(Spfw A, 𝒪) = A` for a weakly admissible topological ring, taken
  along its *weak* ideals of definition. This is what the counterparts of Lemmas 87.2.1 and
  87.2.2 consume, and the one step of their proofs that is not a formal consequence of the weak
  ideal system interface: it runs over the whole directed family of weak ideals of definition,
  the powers of a single one not being cofinal.
* `AlgebraicGeometry.surjective_spfGammaHom`: the canonical map is surjective. With
  `AlgebraicGeometry.injective_spfGammaHom` this makes it bijective.
* `AlgebraicGeometry.spfPresheafOn_top_ext`: two global sections of `𝒪_{Spf A}` agree as soon as
  their images in every term `𝒪_λ` of the inverse system agree.
* `TopCommRingCat.eq_of_isLimit` and `TopCommRingCat.isIso_of_ringEquiv`: elements of the apex of
  a limit cone of topological rings are determined by their components, and a continuous ring
  isomorphism with continuous inverse is an isomorphism of topological rings.
* `TopCommRingCat.exists_finset_forall_app_eq_zero`: a continuous homomorphism out of a limit of
  discrete topological rings into a discrete ring is killed by the common kernel of finitely many
  of the projections.
* `AlgebraicGeometry.exists_spfIndex_forall_app_eq_zero`: **one term of the inverse system
  serving a finite family of quasi-compact opens.** Given a continuous homomorphism from the
  sections of `𝒪_{Spf A}` over each member of a finite family of quasi-compact opens into a
  discrete ring, a single member `I` of the weak ideal system has the property that all of them
  kill the kernel of the projection onto `𝒪^A_I`, so all of them factor through that one term of
  the inverse system.
* `AlgebraicGeometry.exists_ltrsGlobalSectionsMap_eq_and_base_eq`: for admissible `A` and `B`,
  every morphism `Spf B → Spf A` of locally topologically ringed spaces agrees with the morphism
  attached to a continuous ring homomorphism `A → B` on global sections and on underlying
  topological spaces. This is as far towards the surjectivity half of Stacks 0AHZ as the
  identification `Γ(Spf A, 𝒪_{Spf A}) = A` carries on its own; see the implementation notes.
* `AlgebraicGeometry.exists_isIdealOfDefinition_quotient_ltrsGlobalSectionsRingHom`: for each
  ideal of definition `J` of `B` the recovered homomorphism, reduced modulo `J`, factors through
  a single quotient `A/I` of `A` by an ideal of definition.

## Implementation notes

Completeness is used exactly once, through
`TopologicalRing.toIdealOfDefinitionLimit_surjective`, to produce the element of `A` realizing a
compatible family of residues; separatedness is what
`AlgebraicGeometry.injective_spfGammaHom` already used. Both are packaged in
`TopologicalRing.IsAdmissible`, so no hypothesis beyond admissibility (and linearity of the
topology, which the ideals of definition need in order to form a basis of neighbourhoods of
zero) is assumed.

Continuity of the inverse is proved exactly as for the limit of quotients: the kernel of each
projection `Γ(Spf A, 𝒪_{Spf A}) → Γ(Spf A, 𝒪_λ)` is open because `Spf A` is quasi-compact — it
is `D(1) ∩ Spf A` — so those sections are discrete, and the ideals of definition form a basis of
neighbourhoods of zero in `A`.

The surjectivity half of Stacks 0AHZ is not proved here; it is completed in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSurjectivity`. A morphism
of locally topologically ringed spaces is a continuous map together with a comparison map of
sheaves, and equality of two such morphisms is equality of both halves:
`AlgebraicGeometry.LTRS.Hom.ext'` reduces it to equality of the underlying morphisms of
presheafed spaces. The continuous maps are handled by
`AlgebraicGeometry.base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn`, and the comparison maps agree
at the whole space by `AlgebraicGeometry.spfMapGammaHom_ltrsGlobalSectionsRingHom`, which is what
`AlgebraicGeometry.exists_ltrsGlobalSectionsMap_eq_and_base_eq` records. What is still missing is
that they agree at every open. Since pushing forward preserves limits, the target
`g_* 𝒪_{Spf B}` is the limit of the `g_* 𝒪^B_J`, so it suffices to compare the two after
projecting to each `g_* 𝒪^B_J`; and there the comparison map of `Spf φ` is pinned down by
`AlgebraicGeometry.spfMapC_comp_spfProjection`. What remains is to see that the two maps
`𝒪_{Spf A} → g_* 𝒪^B_J` agree at every open.

The factoring of such a map through a single term `𝒪^A_I` of `𝒪_{Spf A} = lim 𝒪_λ` is available
over a quasi-compact open, and uniformly over a finite family of them: the sections of
`𝒪_{Spf A}` over a quasi-compact open are the limit of the discrete rings of sections of the
`𝒪_λ` there, so `TopCommRingCat.exists_finset_forall_app_eq_zero` applies, and the finitely many
members of the system it produces are intersected by
`AlgebraicGeometry.exists_spfIndex_forall_le`. That is
`AlgebraicGeometry.exists_spfIndex_forall_app_eq_zero`; at the whole space the
ring-level shadow of it is
`AlgebraicGeometry.exists_isIdealOfDefinition_quotient_ltrsGlobalSectionsRingHom`, whose uniform
form over finitely many `J` is
`AlgebraicGeometry.exists_isIdealOfDefinition_forall_quotient_ltrsGlobalSectionsRingHom`.

Two steps remain, and both are carried out in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSurjectivity`. First, the comparison at
a general open has to be reduced to the
comparison at the basic opens `D(a) ∩ Spf A`, which are quasi-compact: those form a basis of
`Spf A`, and the target `g_* 𝒪^B_J` is the pushforward of a sheaf, hence separated, so a map out
of `𝒪_{Spf A}` is determined by its values there. Second, at a basic open the two maps have to be
identified: applying the uniformity above to the *pair* of them over that one open makes both
factor through the sections of `𝒪^A_I` over `D(a) ∩ Spf A`, which are the localization
`(A/I)_{\bar a}` by `AlgebraicGeometry.isLocalization_spfComponentOn_spfBasicOpen`; so every
section there has `\bar a^n` times it coming from `A`, the two maps agree on sections coming from
`A` by the comparison at the whole space, and the image of `a` is invertible in the target
`(B/J)_{\overline{φ(a)}}`. Those three facts force the two maps to agree.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace TopCommRingCat

variable {J : Type u} [SmallCategory J]

/-- A limit cone point is isomorphic to the subring of compatible families, compatibly with the
projections. -/
private theorem exists_iso_limitSubring {F : J ⥤ TopCommRingCat.{u}} {c : Cone F}
    (hc : IsLimit c) : ∃ e : c.pt ≅ TopCommRingCat.of (limitSubring F),
      (∀ (j : J) (z : c.pt.α), (e.hom.1 z).1 j = (c.π.app j).1 z) ∧
        ∀ z : c.pt.α, e.inv.1 (e.hom.1 z) = z :=
  ⟨hc.conePointUniqueUpToIso (limitConeIsLimit F), fun j z =>
    congrArg (fun g : c.pt ⟶ F.obj j => g.1 z)
      (hc.conePointUniqueUpToIso_hom_comp (limitConeIsLimit F) j), fun z =>
    congrArg (fun g : c.pt ⟶ c.pt => g.1 z)
      (hc.conePointUniqueUpToIso (limitConeIsLimit F)).hom_inv_id⟩

/-- Two elements of the apex of a limit cone of topological rings agree as soon as all of their
components agree. -/
theorem eq_of_isLimit {F : J ⥤ TopCommRingCat.{u}} {c : Cone F} (hc : IsLimit c) {x y : c.pt.α}
    (h : ∀ j, (c.π.app j).1 x = (c.π.app j).1 y) : x = y := by
  obtain ⟨e, hcomp, hinv⟩ := exists_iso_limitSubring hc
  have hxy : e.hom.1 x = e.hom.1 y :=
    Subtype.ext (funext fun j => ((hcomp j x).trans (h j)).trans (hcomp j y).symm)
  rw [← hinv x, ← hinv y, hxy]

/-- **A continuous homomorphism out of a limit of discrete topological rings is killed by the
common kernel of finitely many projections.** Equivalently: in such a limit the common kernels
of the finite families of projections form a neighbourhood basis of zero.

The limit is the subring of compatible families inside the product of the terms, so a
neighbourhood of zero there contains a basic neighbourhood of the product topology, which is cut
out by finitely many coordinates; the target being discrete, the preimage of zero is such a
neighbourhood. When the index is codirected a single projection suffices, the intersection of
the finitely many terms being again a term; that final step is left to the caller, who knows the
index. -/
theorem exists_finset_forall_app_eq_zero {F : J ⥤ TopCommRingCat.{u}}
    [∀ j, DiscreteTopology (F.obj j).α] {c : Cone F} (hc : IsLimit c)
    {T : TopCommRingCat.{u}} [DiscreteTopology T.α] (ψ : c.pt ⟶ T) :
    ∃ s : Finset J, ∀ x : c.pt.α, (∀ j ∈ s, (c.π.app j).1 x = 0) → ψ.1 x = 0 := by
  classical
  obtain ⟨e, hcomp, hinv⟩ := exists_iso_limitSubring hc
  have hpre : IsOpen ((fun y : limitSubring F => ψ.1 (e.inv.1 y)) ⁻¹' {0}) :=
    (isOpen_discrete {(0 : T.α)}).preimage (ψ.2.comp e.inv.2)
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.1 hpre
  have hzero : (0 : ∀ j, (F.obj j).α) ∈ V := by
    have h0 : (0 : limitSubring F) ∈
        (fun y : limitSubring F => ψ.1 (e.inv.1 y)) ⁻¹' {0} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, map_zero]
    have h1 := hVeq ▸ h0
    simpa using h1
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.1 hVopen _ hzero
  refine ⟨s, fun x hx => ?_⟩
  have hmem : (e.hom.1 x).1 ∈ V := by
    refine hsub fun j hj => ?_
    rw [hcomp j x, hx j hj]
    exact (hu j hj).2
  have hx0 : e.hom.1 x ∈ (fun y : limitSubring F => ψ.1 (e.inv.1 y)) ⁻¹' {0} := hVeq ▸ hmem
  simpa [hinv x] using hx0

/-- A morphism of topological rings that is a ring isomorphism with continuous inverse is an
isomorphism of topological rings. -/
theorem isIso_of_ringEquiv {R S : TopCommRingCat.{u}} (f : R ⟶ S) (e : R.α ≃+* S.α)
    (he : ∀ r, e r = f.1 r) (hcont : Continuous e.symm) : IsIso f :=
  ⟨⟨⟨(e.symm : S.α →+* R.α), hcont⟩,
    Subtype.ext (RingHom.ext fun r =>
      (congrArg e.symm (he r).symm).trans (e.symm_apply_apply r)),
    Subtype.ext (RingHom.ext fun s =>
      (he (e.symm s)).symm.trans (e.apply_symm_apply s))⟩⟩

end TopCommRingCat

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### Global sections of the terms of the inverse system -/

/-- The sections of `𝒪_λ` over the whole space of open primes are discrete: that space is
quasi-compact, being `D(1)` intersected with it. -/
theorem discreteTopology_spfComponentOn_top (hA : IsWeaklyPreAdmissible A) (I : SpfIndex A P) :
    DiscreteTopology ((pseudoDiscrete (spfComponentOn A I)).obj (op ⊤)).α := by
  have h := discreteTopology_spfComponentOn_spfBasicOpen A hA 1 I
  rwa [spfBasicOpen_one] at h

/-- The sections of `𝒪_λ` over the whole of `Spf A` are discrete: `Spf A` is quasi-compact,
being `D(1) ∩ Spf A`.

The ideals-of-definition case of `discreteTopology_spfComponentOn_top`. -/
theorem discreteTopology_spfComponent_top (hA : IsPreAdmissible A) (I : IdealsOfDefinition A) :
    DiscreteTopology ((pseudoDiscrete (spfComponent A I)).obj (op ⊤)).α :=
  discreteTopology_spfComponentOn_top (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (I := I)

variable (P) in
/-- The sections of `lim 𝒪_λ` over an open set are the limit of the sections of the `𝒪_λ` there,
limits of presheaves being computed objectwise. -/
noncomputable def spfObjIsLimitOn (V : Opens (spfSpace A)) :
    IsLimit (((evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op V)).mapCone
      (limit.cone (spfDiagramOn A P ⋙ pseudoDiscreteFunctor))) :=
  isLimitOfPreserves ((evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op V))
    (limit.isLimit (spfDiagramOn A P ⋙ pseudoDiscreteFunctor))

/-- The sections of `𝒪_{Spf A} = lim 𝒪_λ` over an open set are the limit of the sections of the
`𝒪_λ` there, limits of presheaves being computed objectwise.

The ideals-of-definition case of `spfObjIsLimitOn`. -/
@[reducible] noncomputable def spfObjIsLimit (V : Opens (spfSpace A)) :
    IsLimit (((evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op V)).mapCone
      (limit.cone (spfDiagram A ⋙ pseudoDiscreteFunctor))) :=
  spfObjIsLimitOn (A := A) (P := IsIdealOfDefinition) (V := V)

variable (P) in
/-- The global sections of `lim 𝒪_λ` are the limit of the global sections of the `𝒪_λ`, limits of
presheaves being computed objectwise. -/
noncomputable def spfGammaTopIsLimitOn :
    IsLimit (((evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op ⊤)).mapCone
      (limit.cone (spfDiagramOn A P ⋙ pseudoDiscreteFunctor))) :=
  spfObjIsLimitOn A P ⊤

/-- The global sections of `𝒪_{Spf A} = lim 𝒪_λ` are the limit of the global sections of the
`𝒪_λ`, limits of presheaves being computed objectwise.

The ideals-of-definition case of `spfGammaTopIsLimitOn`. -/
@[reducible] noncomputable def spfGammaTopIsLimit :
    IsLimit (((evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op ⊤)).mapCone
      (limit.cone (spfDiagram A ⋙ pseudoDiscreteFunctor))) :=
  spfGammaTopIsLimitOn (A := A) (P := IsIdealOfDefinition)

/-- Two global sections of `lim 𝒪_λ` agree as soon as their images in every term `𝒪_λ` of the
inverse system agree. -/
theorem spfPresheafOn_top_ext {s t : ((spfPresheafOn A P).obj (op ⊤)).α}
    (h : ∀ I : SpfIndex A P,
      ((spfProjectionOn A I).app (op ⊤)).1 s = ((spfProjectionOn A I).app (op ⊤)).1 t) : s = t :=
  TopCommRingCat.eq_of_isLimit (spfGammaTopIsLimitOn A P) h

/-- Two global sections of `𝒪_{Spf A}` agree as soon as their images in every term `𝒪_λ` of the
inverse system agree.

The ideals-of-definition case of `spfPresheafOn_top_ext`. -/
theorem spfPresheaf_top_ext {s t : ((spfPresheaf A).obj (op ⊤)).α}
    (h : ∀ I : IdealsOfDefinition A,
      ((spfProjection A I).app (op ⊤)).1 s = ((spfProjection A I).app (op ⊤)).1 t) : s = t :=
  spfPresheafOn_top_ext (A := A) (P := IsIdealOfDefinition) (s := s) (t := t) (h := h)

/-! ### One ideal of definition for finitely many quasi-compact opens at once -/

/-- Over a quasi-compact open of `Spf A` a continuous homomorphism from the sections of
`𝒪_{Spf A}` into a discrete ring is killed by the common kernel of finitely many of the
projections onto the terms `𝒪_λ`: those sections are the limit of the sections of the `𝒪_λ`,
which are discrete over a quasi-compact open. -/
theorem exists_finset_forall_spfProjectionOn_app_eq_zero {V : Opens (spfSpace A)}
    (hV : IsCompact (V : Set (spfSpace A))) {T : TopCommRingCat.{u}} [DiscreteTopology T.α]
    (α : (spfPresheafOn A P).obj (op V) ⟶ T) :
    ∃ t : Finset (SpfIndex A P), ∀ s : ((spfPresheafOn A P).obj (op V)).α,
      (∀ I ∈ t, ((spfProjectionOn A I).app (op V)).1 s = 0) → α.1 s = 0 := by
  have hdisc : ∀ I : SpfIndex A P,
      DiscreteTopology ((((spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op V)).obj I).α) :=
    fun I => isPseudoDiscrete_pseudoDiscrete (spfComponentOn A I) V hV
  exact TopCommRingCat.exists_finset_forall_app_eq_zero (spfObjIsLimitOn A P V) α

/-- Over a quasi-compact open of `Spf A` a continuous homomorphism from the sections of
`𝒪_{Spf A}` into a discrete ring is killed by the common kernel of finitely many of the
projections onto the terms `𝒪_λ`: those sections are the limit of the sections of the `𝒪_λ`,
which are discrete over a quasi-compact open.

The ideals-of-definition case of `exists_finset_forall_spfProjectionOn_app_eq_zero`. -/
theorem exists_finset_forall_spfProjection_app_eq_zero {V : Opens (spfSpace A)}
    (hV : IsCompact (V : Set (spfSpace A))) {T : TopCommRingCat.{u}} [DiscreteTopology T.α]
    (α : (spfPresheaf A).obj (op V) ⟶ T) :
    ∃ t : Finset (IdealsOfDefinition A), ∀ s : ((spfPresheaf A).obj (op V)).α,
      (∀ I ∈ t, ((spfProjection A I).app (op V)).1 s = 0) → α.1 s = 0 :=
  exists_finset_forall_spfProjectionOn_app_eq_zero (A := A) (P := IsIdealOfDefinition) (V := V)
    (hV := hV) (T := T) (α := α)

/-- **One ideal of definition serving a finite family of quasi-compact opens.** Given, for each
member of a finite family of quasi-compact opens of `Spf A`, a continuous homomorphism from the
sections of `𝒪_{Spf A}` there into a discrete ring, there is a *single* ideal of definition `I`
of `A` such that every one of those homomorphisms kills the kernel of the projection onto
`𝒪^A_I` — so each of them factors through the sections of that one term of the inverse system.

Over one open the factoring is `AlgebraicGeometry.exists_finset_forall_spfProjectionOn_app_eq_zero`
and produces a finite set of members of the system depending on the open; the ideals produced by
the whole family are then intersected, which is legitimate because a finite family of open ideals
has a common lower bound that is again a member of the system
(`AlgebraicGeometry.exists_spfIndex_forall_le`), and because the projections of `𝒪_{Spf A}` are
compatible with the transition maps, so shrinking the member only enlarges the kernel. -/
theorem exists_spfIndex_forall_app_eq_zero (I₀ : SpfIndex A P) {ι : Type*}
    [Finite ι] (V : ι → Opens (spfSpace A))
    (hV : ∀ i, IsCompact ((V i : Opens (spfSpace A)) : Set (spfSpace A)))
    (T : ι → TopCommRingCat.{u}) [∀ i, DiscreteTopology (T i).α]
    (α : ∀ i, (spfPresheafOn A P).obj (op (V i)) ⟶ T i) :
    ∃ I : SpfIndex A P, ∀ (i : ι) (s : ((spfPresheafOn A P).obj (op (V i))).α),
      ((spfProjectionOn A I).app (op (V i))).1 s = 0 → (α i).1 s = 0 := by
  classical
  choose t ht using fun i =>
    exists_finset_forall_spfProjectionOn_app_eq_zero A (hV i) (α i)
  obtain ⟨I, hle⟩ := exists_spfIndex_forall_le A I₀
    (fun p : Σ i : ι, {K : SpfIndex A P // K ∈ t i} => (p.2.1).1)
    fun p => (p.2.1).isWeakIdealOfDefinition.1
  refine ⟨I, fun i s hs => ht i s fun K hK => ?_⟩
  have hleK : I.1 ≤ K.1 := hle ⟨i, ⟨K, hK⟩⟩
  rw [← spfProjectionOn_app_spfTransitionOn_app A hleK (op (V i)) s, hs]
  exact map_zero _

/-- **One ideal of definition serving a finite family of quasi-compact opens.** Given, for each
member of a finite family of quasi-compact opens of `Spf A`, a continuous homomorphism from the
sections of `𝒪_{Spf A}` there into a discrete ring, there is a *single* ideal of definition `I`
of `A` such that every one of those homomorphisms kills the kernel of the projection onto
`𝒪^A_I` — so each of them factors through the sections of that one term of the inverse system.

Over one open the factoring is `AlgebraicGeometry.exists_finset_forall_spfProjection_app_eq_zero`
and produces a finite set of ideals of definition depending on the open; the ideals produced by
the whole family are then intersected, which is legitimate because a finite family of open ideals
has a common lower bound that is again an ideal of definition
(`TopologicalRing.exists_isIdealOfDefinition_le`), and because the projections of `𝒪_{Spf A}` are
compatible with the transition maps, so shrinking the ideal of definition only enlarges the
kernel.

The ideals-of-definition case of `AlgebraicGeometry.exists_spfIndex_forall_app_eq_zero`. -/
theorem exists_isIdealOfDefinition_forall_app_eq_zero (hA : IsPreAdmissible A) {ι : Type*}
    [Finite ι] (V : ι → Opens (spfSpace A))
    (hV : ∀ i, IsCompact ((V i : Opens (spfSpace A)) : Set (spfSpace A)))
    (T : ι → TopCommRingCat.{u}) [∀ i, DiscreteTopology (T i).α]
    (α : ∀ i, (spfPresheaf A).obj (op (V i)) ⟶ T i) :
    ∃ I : IdealsOfDefinition A, ∀ (i : ι) (s : ((spfPresheaf A).obj (op (V i))).α),
      ((spfProjection A I).app (op (V i))).1 s = 0 → (α i).1 s = 0 :=
  exists_spfIndex_forall_app_eq_zero A (preAdmissibleSpfIndex A hA) V hV T α

/-! ### The residues of a global section -/

/-- The residue of a global section of `𝒪_{Spf A}` in `A/I`: its image in the term `𝒪_I` of the
inverse system, read through the identification of `Γ(Spec (A/I), 𝒪)` with `A/I`. -/
noncomputable def spfGammaResidueOn (I : SpfIndex A P)
    (s : ((spfPresheafOn A P).obj (op ⊤)).α) : A ⧸ I.1 :=
  (Scheme.ΓSpecIso (spfQuotientOn A I)).hom.hom (((spfProjectionOn A I).app (op ⊤)).1 s)

/-- The residue of a global section of `𝒪_{Spf A}` in `A/I`: its image in the term `𝒪_I` of the
inverse system, read through the identification of `Γ(Spec (A/I), 𝒪)` with `A/I`.

The ideals-of-definition case of `spfGammaResidueOn`. -/
@[reducible] noncomputable def spfGammaResidue (I : IdealsOfDefinition A)
    (s : ((spfPresheaf A).obj (op ⊤)).α) : A ⧸ I.1 :=
  spfGammaResidueOn (A := A) (P := IsIdealOfDefinition) (I := I) (s := s)

/-- The residue of a global section is its image in `𝒪_I` read through the identification of
`Γ(Spec (A/I), 𝒪)` with `A/I`. -/
theorem spfGammaResidueOn_apply (I : SpfIndex A P)
    (s : ((spfPresheafOn A P).obj (op ⊤)).α) :
    spfGammaResidueOn A I s =
      (Scheme.ΓSpecIso (spfQuotientOn A I)).hom.hom (((spfProjectionOn A I).app (op ⊤)).1 s) :=
  rfl

/-- The residue of a global section is its image in `𝒪_I` read through the identification of
`Γ(Spec (A/I), 𝒪)` with `A/I`.

The ideals-of-definition case of `spfGammaResidueOn_apply`. -/
theorem spfGammaResidue_apply (I : IdealsOfDefinition A)
    (s : ((spfPresheaf A).obj (op ⊤)).α) :
    spfGammaResidue A I s =
      (Scheme.ΓSpecIso (spfQuotient A I)).hom.hom (((spfProjection A I).app (op ⊤)).1 s) :=
  spfGammaResidueOn_apply (A := A) (P := IsIdealOfDefinition) (I := I) (s := s)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The identification of `Γ(Spec (A/I), 𝒪)` with `A/I` is injective. -/
theorem ΓSpecIso_spfQuotientOn_hom_injective (I : SpfIndex A P) :
    Function.Injective (Scheme.ΓSpecIso (spfQuotientOn A I)).hom.hom := by
  intro t t' h
  have e : ∀ u, (Scheme.ΓSpecIso (spfQuotientOn A I)).inv.hom
      ((Scheme.ΓSpecIso (spfQuotientOn A I)).hom.hom u) = u := fun u =>
    congrArg (fun k : Γ(Spec (spfQuotientOn A I), ⊤) ⟶ Γ(Spec (spfQuotientOn A I), ⊤) => k.hom u)
      (Scheme.ΓSpecIso (spfQuotientOn A I)).hom_inv_id
  rw [← e t, ← e t', h]

omit [IsTopologicalRing A] in
/-- The identification of `Γ(Spec (A/I), 𝒪)` with `A/I` is injective.

The ideals-of-definition case of `ΓSpecIso_spfQuotientOn_hom_injective`. -/
theorem ΓSpecIso_hom_injective (I : IdealsOfDefinition A) :
    Function.Injective (Scheme.ΓSpecIso (spfQuotient A I)).hom.hom :=
  ΓSpecIso_spfQuotientOn_hom_injective (A := A) (P := IsIdealOfDefinition) (I := I)

variable (P) in
/-- The residues of a global section are compatible with the transition maps `A/I → A/J`, so
they form an element of the limit of the quotients of `A` along the family. -/
theorem spfGammaResidueOn_mem (s : ((spfPresheafOn A P).obj (op ⊤)).α) :
    (fun I : {I : Ideal A // P I} => spfGammaResidueOn A I s) ∈ idealLimit A P := by
  intro I J h
  dsimp only
  have hnat : ∀ t : Γ(Spec (spfQuotientOn A I), ⊤),
      (Scheme.ΓSpecIso (spfQuotientOn A J)).hom.hom ((spfTransitionOn A h).app (op ⊤) t)
        = Ideal.Quotient.factor h ((Scheme.ΓSpecIso (spfQuotientOn A I)).hom.hom t) := fun t =>
    congrArg (fun k : Γ(Spec (spfQuotientOn A I), ⊤) ⟶ spfQuotientOn A J => k.hom t)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.factor h)))
  rw [spfGammaResidueOn_apply, spfGammaResidueOn_apply,
    ← spfProjectionOn_app_spfTransitionOn_app A h (op ⊤) s]
  exact (hnat _).symm

/-- The residues of a global section are compatible with the transition maps `A/I → A/J`, so
they form an element of the limit of the quotients of `A` by its ideals of definition.

The ideals-of-definition case of `spfGammaResidueOn_mem`. -/
theorem spfGammaResidue_mem (s : ((spfPresheaf A).obj (op ⊤)).α) :
    (fun I : IdealOfDefinition A => spfGammaResidue A I s) ∈ idealOfDefinitionLimit A :=
  spfGammaResidueOn_mem (A := A) (P := IsIdealOfDefinition) (s := s)

/-- The residue in `A/I` of the image of `a : A` under the canonical map is the residue of `a`
itself. -/
theorem spfGammaResidueOn_spfGammaHomOn (I : SpfIndex A P) (a : A) :
    spfGammaResidueOn A I ((spfGammaHomOn A P).1 a) = Ideal.Quotient.mk I.1 a := by
  have h1 : ((spfProjectionOn A I).app (op ⊤)).1 ((spfGammaHomOn A P).1 a)
      = (spfGammaComponentOn A I).1 a :=
    congrArg
      (fun k : TopCommRingCat.of A ⟶ (pseudoDiscrete (spfComponentOn A I)).obj (op ⊤) => k.1 a)
      (spfGammaHomOn_comp_spfProjection_app_top A I)
  rw [spfGammaResidueOn_apply, h1]
  exact congrArg (fun k : CommRingCat.of A ⟶ spfQuotientOn A I => k.hom a)
    (spfGammaComponentHomOn_comp_ΓSpecIso_hom A I)

/-- The residue in `A/I` of the image of `a : A` under the canonical map is the residue of `a`
itself.

The ideals-of-definition case of `spfGammaResidueOn_spfGammaHomOn`. -/
theorem spfGammaResidue_spfGammaHom (I : IdealsOfDefinition A) (a : A) :
    spfGammaResidue A I ((spfGammaHom A).1 a) = Ideal.Quotient.mk I.1 a :=
  spfGammaResidueOn_spfGammaHomOn (A := A) (P := IsIdealOfDefinition) (I := I) (a := a)

/-! ### The identification `Γ(lim 𝒪_λ) = A` -/

variable (P) in
/-- **For a complete ring the canonical map into the global sections of the formal spectrum taken
along a fundamental system of ideals is surjective.** The residues of a global section form a
compatible family along the family of ideals, and completeness of `A` realizes any such family by
an element of `A`.

The family of ideals is used as a whole: no cofinality of the powers of one of its members is
needed, which is what makes this available for the weak ideals of definition of a weakly
admissible ring as well as for the ideals of definition of an admissible one. -/
theorem surjective_spfGammaHomOn (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Function.Surjective (spfGammaHomOn A P).1 := by
  intro s
  obtain ⟨a, ha⟩ := toIdealLimit_surjective h hc
    ⟨fun I => spfGammaResidueOn A I s, spfGammaResidueOn_mem A P s⟩
  refine ⟨a, spfPresheafOn_top_ext A fun I => ?_⟩
  refine ΓSpecIso_spfQuotientOn_hom_injective A I ?_
  rw [← spfGammaResidueOn_apply, ← spfGammaResidueOn_apply, spfGammaResidueOn_spfGammaHomOn]
  exact congrArg (fun z : idealLimit A P => z.1 I) ha

variable (P) in
/-- For a complete separated ring the canonical map into the global sections of the formal
spectrum taken along a fundamental system of ideals is a ring isomorphism: it is injective by
separatedness and surjective by completeness. -/
noncomputable def spfGammaEquivOn [T2Space A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    A ≃+* ((spfPresheafOn A P).obj (op ⊤)).α :=
  RingEquiv.ofBijective (spfGammaHomOn A P).1
    ⟨injective_spfGammaHomOn A P h, surjective_spfGammaHomOn A P h hc⟩

variable (P) in
/-- The residue in `A/I` of the preimage of a global section is the section's own residue. -/
theorem spfGammaResidue_symmOn [T2Space A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (I : SpfIndex A P) (s : ((spfPresheafOn A P).obj (op ⊤)).α) :
    Ideal.Quotient.mk I.1 ((spfGammaEquivOn A P h hc).symm s) = spfGammaResidueOn A I s := by
  rw [← spfGammaResidueOn_spfGammaHomOn A I ((spfGammaEquivOn A P h hc).symm s)]
  exact congrArg (spfGammaResidueOn A I) ((spfGammaEquivOn A P h hc).apply_symm_apply s)

variable (P) in
/-- The inverse of the canonical map is continuous: a global section of `lim 𝒪_λ` whose image in
`𝒪_I` vanishes has its preimage in `I`, and the sections of `𝒪_I` over the quasi-compact space of
open primes are discrete, so that condition is open. -/
theorem continuous_spfGammaEquivOn_symm [T2Space A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Continuous (spfGammaEquivOn A P h hc).symm := by
  obtain ⟨I₀, hI₀⟩ := h.exists_mem
  have hwA : IsWeaklyPreAdmissible A := isWeaklyPreAdmissible_of_spfIndex A ⟨I₀, hI₀⟩
  apply continuous_of_tendsto_nhds_zero (spfGammaEquivOn A P h hc).symm.toAddMonoidHom
  refine h.hasBasis.tendsto_right_iff.mpr fun I hI => ?_
  have := discreteTopology_spfComponentOn_top A hwA (⟨I, hI⟩ : SpfIndex A P)
  have hnbhd : {s : ((spfPresheafOn A P).obj (op ⊤)).α |
      ((spfProjectionOn A ⟨I, hI⟩).app (op ⊤)).1 s = 0} ∈
        nhds (0 : ((spfPresheafOn A P).obj (op ⊤)).α) :=
    ((isOpen_discrete {(0 : ((pseudoDiscrete (spfComponentOn A ⟨I, hI⟩)).obj (op ⊤)).α)}).preimage
      ((spfProjectionOn A ⟨I, hI⟩).app (op ⊤)).2).mem_nhds (map_zero _)
  refine Filter.mem_of_superset hnbhd fun s hs => ?_
  have hs' : ((spfProjectionOn A (⟨I, hI⟩ : SpfIndex A P)).app (op ⊤)).1 s = 0 := hs
  have hz : spfGammaResidueOn A (⟨I, hI⟩ : SpfIndex A P) s = 0 :=
    (congrArg
      (Scheme.ΓSpecIso (spfQuotientOn A (⟨I, hI⟩ : SpfIndex A P))).hom.hom hs').trans
      (map_zero _)
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((spfGammaResidue_symmOn A P h hc ⟨I, hI⟩ s).trans hz)

variable (P) in
/-- **The identification `A = Γ(lim 𝒪_λ)` of topological rings**, for the formal spectrum of a
complete separated topological ring taken along a fundamental system of ideals. -/
theorem isIso_spfGammaHomOn [T2Space A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    IsIso (spfGammaHomOn A P) :=
  TopCommRingCat.isIso_of_ringEquiv (spfGammaHomOn A P) (spfGammaEquivOn A P h hc)
    (fun _ => rfl) (continuous_spfGammaEquivOn_symm A P h hc)

variable (P) in
/-- The identification `A = Γ(lim 𝒪_λ)` of topological rings, as an isomorphism. -/
noncomputable def spfGammaIsoOn [T2Space A] (h : IsFundamentalIdealSystem A P)
    (hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    TopCommRingCat.of A ≅ (spfPresheafOn A P).obj (op ⊤) :=
  letI := isIso_spfGammaHomOn A P h hc
  asIso (spfGammaHomOn A P)

/-- For an admissible topological ring the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` is
surjective. -/
theorem surjective_spfGammaHom [IsLinearTopology A A] (hA : IsAdmissible A) :
    Function.Surjective (spfGammaHom A).1 :=
  surjective_spfGammaHomOn A IsIdealOfDefinition
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2

/-- For an admissible topological ring the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` is a ring
isomorphism: it is injective by separatedness and surjective by completeness. -/
@[reducible] noncomputable def spfGammaEquiv [IsLinearTopology A A] (hA : IsAdmissible A) :
    A ≃+* ((spfPresheaf A).obj (op ⊤)).α :=
  letI := hA.2.1
  spfGammaEquivOn A IsIdealOfDefinition (isFundamentalIdealSystem_isIdealOfDefinition hA.1)
    hA.2.2

/-- The residue in `A/I` of the preimage of a global section is the section's own residue. -/
theorem spfGammaResidue_symm [IsLinearTopology A A] (hA : IsAdmissible A)
    (I : IdealsOfDefinition A) (s : ((spfPresheaf A).obj (op ⊤)).α) :
    Ideal.Quotient.mk I.1 ((spfGammaEquiv A hA).symm s) = spfGammaResidue A I s :=
  let := hA.2.1
  spfGammaResidue_symmOn A IsIdealOfDefinition
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2 I s

/-- The inverse of the canonical map of an admissible topological ring is continuous. -/
theorem continuous_spfGammaEquiv_symm [IsLinearTopology A A] (hA : IsAdmissible A) :
    Continuous (spfGammaEquiv A hA).symm :=
  let := hA.2.1
  continuous_spfGammaEquivOn_symm A IsIdealOfDefinition
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2

/-- **Stacks 0AHY**, the source's deferred verification `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}`
in the case `f = 1`: for an admissible topological ring the canonical map
`A → Γ(Spf A, 𝒪_{Spf A})` is an isomorphism of topological rings.

The global sections of `𝒪_{Spf A} = lim 𝒪_λ` are the limit of the discrete rings
`Γ(Spec (A/I_λ), 𝒪) = A/I_λ`, and an admissible ring is precisely the limit of its quotients by
its ideals of definition. -/
@[stacks 0AHY "Γ(Spf A, 𝒪_{Spf A}) = A for an admissible topological ring"]
theorem isIso_spfGammaHom [IsLinearTopology A A] (hA : IsAdmissible A) :
    IsIso (spfGammaHom A) :=
  let := hA.2.1
  isIso_spfGammaHomOn A IsIdealOfDefinition
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1) hA.2.2

/-- **Stacks 0AHY.** The identification `A = Γ(Spf A, 𝒪_{Spf A})` of topological rings, for an
admissible topological ring `A`. -/
@[stacks 0AHY "Γ(Spf A, 𝒪_{Spf A}) = A for an admissible topological ring"]
noncomputable def spfGammaIso [IsLinearTopology A A] (hA : IsAdmissible A) :
    TopCommRingCat.of A ≅ (spfPresheaf A).obj (op ⊤) :=
  letI := isIso_spfGammaHom A hA
  asIso (spfGammaHom A)

/-- The identification of `A` with the global sections of `𝒪_{Spf A}` is the canonical map. -/
@[simp]
theorem spfGammaIso_hom [IsLinearTopology A A] (hA : IsAdmissible A) :
    (spfGammaIso A hA).hom = spfGammaHom A := rfl

/-! ### The identification `Γ(Spfw A, 𝒪) = A` for a weakly admissible ring -/

/-- **The counterpart for McQuillan's weakening of the identification
`Γ(Spf A, 𝒪_{Spf A}) = A`.** For a weakly admissible topological ring `A` the canonical map
`A → Γ(Spfw A, 𝒪)` into the global sections of the formal spectrum taken along the *weak* ideals
of definition of `A` is an isomorphism of topological rings.

The proof is the one for an admissible ring, run over the whole family of weak ideals of
definition instead of over the powers of a single ideal of definition. What it needs of the
family is exactly that its members are open, that it is closed under intersection, and that it is
a fundamental system of open neighbourhoods of zero — the last two being the intersection clause
and the fundamental-system clause of Stacks 0AI3 — together with completeness and separatedness
of `A`. The cofinality of the powers `Iⁿ` of a single `I`, which an ideal of definition has and a
weak ideal of definition need not, is used nowhere. -/
@[stacks 0AI3 "the identification the counterparts of Lemmas 87.2.1 and 87.2.2 \
consume: Γ(Spfw A, 𝒪) = A for a weakly admissible ring, over the whole system of weak ideals of \
definition"]
theorem isIso_spfwGammaHom [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    IsIso (spfGammaHomOn A IsWeakIdealOfDefinition) :=
  let := hA.2.2
  isIso_spfGammaHomOn A IsWeakIdealOfDefinition
    (isFundamentalIdealSystem_isWeakIdealOfDefinition hA) hA.2.1

/-- **The identification `A = Γ(Spfw A, 𝒪)` of topological rings** for a weakly admissible
topological ring: McQuillan's counterpart of the identification `Γ(Spf A, 𝒪_{Spf A}) = A`. -/
@[stacks 0AI3 "the identification the counterparts of Lemmas 87.2.1 and 87.2.2 \
consume: A = Γ(Spfw A, 𝒪) as topological rings, for a weakly admissible ring"]
noncomputable def spfwGammaIso [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    TopCommRingCat.of A ≅ (spfPresheafOn A IsWeakIdealOfDefinition).obj (op ⊤) :=
  letI := isIso_spfwGammaHom A hA
  asIso (spfGammaHomOn A IsWeakIdealOfDefinition)

/-- The identification of `A` with the global sections of `𝒪_{Spfw A}` is the canonical map. -/
@[simp]
theorem spfwGammaIso_hom [IsLinearTopology A A] (hA : IsWeaklyAdmissible A) :
    (spfwGammaIso A hA).hom = spfGammaHomOn A IsWeakIdealOfDefinition := rfl

/-! ### Recovering a continuous ring homomorphism from a morphism of formal spectra -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] (hA : IsAdmissible A) (hB : IsAdmissible B)
  (I₀ : IdealsOfDefinition A)

/-- The ring homomorphism `A → B` attached to a morphism `g : Spf B → Spf A` of locally
topologically ringed spaces: the map `g` induces on global sections, read through the
identifications `A = Γ(Spf A, 𝒪_{Spf A})` and `B = Γ(Spf B, 𝒪_{Spf B})` of Stacks 0AHY.

Admissibility of `B` is what makes this definable: inverting `B → Γ(Spf B, 𝒪_{Spf B})` needs
that map to be bijective, which is `AlgebraicGeometry.spfGammaEquiv`. -/
@[sga "3 VIIB 1.1" "ring map f♮"]
noncomputable def ltrsGlobalSectionsRingHom (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) : A →+* B :=
  (spfGammaEquiv B hB).symm.toRingHom.comp ((ltrsGlobalSectionsMap g).1.comp (spfGammaHom A).1)

omit [IsLinearTopology A A] in
/-- The homomorphism recovered from a morphism of formal spectra is continuous: it is a
composite of the canonical map of `A`, the map on global sections, and the inverse of the
canonical map of `B`, each of which is continuous. -/
@[sga "3 VIIB 1.1" "continuity of f♮"]
theorem continuous_ltrsGlobalSectionsRingHom (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    Continuous (ltrsGlobalSectionsRingHom A B hA hB g) :=
  (continuous_spfGammaEquiv_symm B hB).comp
    ((ltrsGlobalSectionsMap g).2.comp (spfGammaHom A).2)

/-- The homomorphism recovered from a morphism of formal spectra, as a morphism of topological
rings. -/
@[sga "3 VIIB 1.1" "partial"]
noncomputable def ltrsGlobalSectionsTopHom (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    TopCommRingCat.of A ⟶ TopCommRingCat.of B :=
  ⟨ltrsGlobalSectionsRingHom A B hA hB g, continuous_ltrsGlobalSectionsRingHom A B hA hB g⟩

omit [IsLinearTopology A A] in
/-- The recovered homomorphism is, by construction, the map on global sections read through the
canonical maps: the square defining it commutes. -/
theorem ltrsGlobalSectionsTopHom_comp_spfGammaHom (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    ltrsGlobalSectionsTopHom A B hA hB g ≫ spfGammaHom B
      = spfGammaHom A ≫ ltrsGlobalSectionsMap g :=
  Subtype.ext (RingHom.ext fun a =>
    (spfGammaEquiv B hB).apply_symm_apply
      ((ltrsGlobalSectionsMap g).1 ((spfGammaHom A).1 a)))

/-- The morphism of formal spectra attached to the recovered homomorphism induces on global
sections exactly the map the given morphism induces.

Both become the same map after composition with the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` —
for the attached morphism by `AlgebraicGeometry.spfGammaHom_comp_spfMapGammaHom`, and for the
given one by the definition of the recovered homomorphism — and that canonical map is an
isomorphism by Stacks 0AHY, hence an epimorphism. -/
theorem spfMapGammaHom_ltrsGlobalSectionsRingHom (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    spfMapGammaHom A B (continuous_ltrsGlobalSectionsRingHom A B hA hB g) hA.1 I₀
      = ltrsGlobalSectionsMap g := by
  let _ := isIso_spfGammaHom A hA
  refine (cancel_epi (spfGammaHom A)).1 ?_
  rw [spfGammaHom_comp_spfMapGammaHom A B
    (continuous_ltrsGlobalSectionsRingHom A B hA hB g) hA.1 I₀]
  exact ltrsGlobalSectionsTopHom_comp_spfGammaHom A B hA hB g

/-- The map on global sections of the morphism of formal spectra attached to the recovered
homomorphism is the map on global sections of the given morphism. -/
theorem ltrsGlobalSectionsMap_spfLTRSMap_ltrsGlobalSectionsTopHom
    (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    ltrsGlobalSectionsMap
        (spfLTRSMap A B hA.1 I₀ hB.1 (ltrsGlobalSectionsTopHom A B hA hB g))
      = ltrsGlobalSectionsMap g :=
  (ltrsGlobalSectionsMap_spfLTRSMap A B hA.1 I₀ hB.1
      (ltrsGlobalSectionsTopHom A B hA hB g)).trans
    (spfMapGammaHom_ltrsGlobalSectionsRingHom A B hA hB I₀ g)

/-- **The comparison map of Stacks 0AHZ hits every morphism up to its comparison map of
sheaves.** Every morphism `g : Spf B → Spf A` of locally topologically ringed spaces between the
formal spectra of admissible topological rings comes from a continuous ring homomorphism
`A → B` as far as the map on global sections and the map of underlying topological spaces are
concerned.

This is the part of the surjectivity of `AlgebraicGeometry.spfLTRSMap` that the identification
`Γ(Spf A, 𝒪_{Spf A}) = A` of Stacks 0AHY settles on its own: the homomorphism is read off the
map on global sections, and the two morphisms then agree on global sections, which by
`AlgebraicGeometry.base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn` forces their underlying
continuous maps to agree. Full surjectivity needs in addition that the comparison maps of sheaves
agree at every open, not only at the whole space. -/
theorem exists_ltrsGlobalSectionsMap_eq_and_base_eq (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) :
    ∃ f : TopCommRingCat.of A ⟶ TopCommRingCat.of B,
      ltrsGlobalSectionsMap (spfLTRSMap A B hA.1 I₀ hB.1 f) = ltrsGlobalSectionsMap g ∧
        (spfLTRSMap A B hA.1 I₀ hB.1 f).toHom.base = g.toHom.base :=
  ⟨ltrsGlobalSectionsTopHom A B hA hB g,
    ltrsGlobalSectionsMap_spfLTRSMap_ltrsGlobalSectionsTopHom A B hA hB I₀ g,
    base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn A
      (ltrsGlobalSectionsMap_spfLTRSMap_ltrsGlobalSectionsTopHom A B hA hB I₀ g)⟩

/-- For each ideal of definition `J` of `B`, the homomorphism recovered from a morphism
`g : Spf B → Spf A` becomes, after reduction modulo `J`, a map that factors through a single
quotient `A/I` of `A` by an ideal of definition.

This is `TopologicalRing.IsFundamentalIdealSystem.exists_ringHom_comp_mk` applied to
`A → B → B/J`, whose target is discrete because `J` is open. It is the ring-level input to the
remaining step of Stacks 0AHZ: the resulting map `A/I → B/J` is what the adjunction between
`Spec` and global sections turns into the component `𝒪^A_I → g_* 𝒪^B_J` of a comparison map of
sheaves. -/
theorem exists_isIdealOfDefinition_quotient_ltrsGlobalSectionsRingHom
    (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) (J : IdealsOfDefinition B) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ χ : A ⧸ I →+* B ⧸ J.1,
      χ.comp (Ideal.Quotient.mk I)
        = (Ideal.Quotient.mk J.1).comp (ltrsGlobalSectionsRingHom A B hA hB g) := by
  have : DiscreteTopology (B ⧸ J.1) := discreteTopology_quotient_of_isOpen J.2.1
  exact IsFundamentalIdealSystem.exists_ringHom_comp_mk
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1)
    ((Ideal.Quotient.mk J.1).comp (ltrsGlobalSectionsRingHom A B hA hB g))
    (continuous_quot_mk.comp (continuous_ltrsGlobalSectionsRingHom A B hA hB g))

/-- The uniform form of `exists_isIdealOfDefinition_quotient_ltrsGlobalSectionsRingHom`: for a
*finite* family of ideals of definition of `B` the reductions of the recovered homomorphism all
factor through the quotient of `A` by one and the same ideal of definition.

The ideal produced one `J` at a time depends on `J`; this is the statement that over a finite
family the choice can be made uniform, which is
`TopologicalRing.IsFundamentalIdealSystem.exists_forall_ringHom_comp_mk`. -/
theorem exists_isIdealOfDefinition_forall_quotient_ltrsGlobalSectionsRingHom
    (g : spfLTRS B hB.1 ⟶ spfLTRS A hA.1) {ι : Type*} [Finite ι]
    (Js : ι → IdealsOfDefinition B) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ χ : ∀ i, A ⧸ I →+* B ⧸ (Js i).1,
      ∀ i, (χ i).comp (Ideal.Quotient.mk I)
        = (Ideal.Quotient.mk (Js i).1).comp (ltrsGlobalSectionsRingHom A B hA hB g) := by
  have hdisc : ∀ i, DiscreteTopology (B ⧸ (Js i).1) := fun i =>
    discreteTopology_quotient_of_isOpen (Js i).2.1
  exact IsFundamentalIdealSystem.exists_forall_ringHom_comp_mk
    (isFundamentalIdealSystem_isIdealOfDefinition hA.1)
    (fun i => (Ideal.Quotient.mk (Js i).1).comp (ltrsGlobalSectionsRingHom A B hA hB g))
    fun _ => continuous_quot_mk.comp (continuous_ltrsGlobalSectionsRingHom A B hA hB g)

end

end AlgebraicGeometry
