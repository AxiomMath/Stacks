module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleQuotientSystem
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The dévissage datum of Stacks 09YQ on the small étale sites

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage` is the dévissage datum of the
source's proof of [Stacks, Tag 09YQ], and it is the hypothesis `Hdev` of the dimension shift
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`.
For a presented system `E` it asks for a presented system `mid` whose sheaf at every level is
injective, a quotient presented system `quot`, short exact sequences at every level **and on the
limit**, and the compatibility of all of it with the legs and the transitions — sixteen fields.

This file builds one, for an **arbitrary** system with a colimit presentation, from the single
remaining input: [Stacks, Tag 0EXZ] on the small étale sites, i.e. the statement that every system
of abelian étale sheaves on the levels admits a levelwise monomorphism into a pointwise injective
one. That statement is named here as
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasPointwiseInjectiveEmbeddings`; everything
else is supplied.

What had to be built is three things, and the first two are what made the datum unreachable:

* **the two colimit presentations.** `mid` and `quot` are *presented* systems, so the colimits
  `colim_i f_i^{-1}G_i` and `colim_i f_i^{-1}Q_i` must exist on the limit site. They do, by
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_isColimitPresentation`, which gets them
  from the Karoubi envelope of the sheaf category.
* **the short exact sequence on the limit.** The quotient's sheaf is taken to be the *cokernel* of
  the induced map `φ : E.sheaf ⟶ mid.sheaf`, which makes the right-hand half of the sequence
  automatic; the content is that `φ` is a monomorphism, which is
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.mono_of_pointwise_mono`, i.e. the exactness of
  filtered colimits in the sheaf category. That the cokernel really is `colim_i f_i^{-1}Q_i` is
  checked here, by a chase through the levelwise cokernel property.
* **the quotient system**, which is
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.quotientSystem`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasPointwiseInjectiveEmbeddings` — [Stacks,
  Tag 0EXZ] for systems of abelian sheaves on the small étale sites of an inverse system of
  schemes.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage_of_mono_to_injective` —
  **a dévissage datum, from one levelwise embedding into a pointwise injective system.**
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage` — the same, with the
  embedding quantified: `HasPointwiseInjectiveEmbeddings` implies the hypothesis `Hdev` of the
  dimension shift, for every presented system at once.
* `isCohomologyColimit_of_degreeZero_of_vanishing_of_injectiveEmbeddings`, in the namespace
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology` — the dimension shift with `Hdev`
  discharged: the colimit statement of Stacks 09YQ in every degree, from the degree-zero
  statement, the vanishing statement, and the levelwise [Stacks, Tag 0EXZ].

## Implementation notes

**Why the cokernel and not a third application of `exists_isColimitPresentation`.** A colimit
presentation of the quotient system exists by itself, but then the short exact sequence on the
limit would have to be proved for *that* sheaf, and the comparison with the cokernel of `φ` would
be an extra step. Taking the cokernel of `φ` outright makes `ShortComplex.ShortExact` immediate
from `Mono φ`, and what has to be checked instead — that the cokernel satisfies the universal
property of `colim_i f_i^{-1}Q_i` — is a chase in which every step is the cokernel property at a
level, together with the joint epimorphy of the legs of the two presentations already in hand.

**Why the levelwise statement is in the `systemPullback` vocabulary.**
`HasPointwiseInjectiveEmbeddings` states the compatibility of the embedding with the transitions
along `Stacks.EtaleCohomology.systemPullback`, the abstract left adjoint that
`Stacks.EtaleCohomology.EtaleSheafSystem` carries its transitions along; the dévissage datum states
it along the constructed inverse image. The translation is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_naturality_of_map`. Stating
the hypothesis in the first vocabulary is what makes it the literal content of Tag 0EXZ for these
systems, with no comparison isomorphism in its statement.

**The hypotheses on the index.** `UnivLE.{v, u + 1}` and `Nonempty I` are used through
`mono_of_pointwise_mono` and `exists_isColimitPresentation`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleKaroubiColimit.lean` on why
they are not restrictions on the mathematics. `IsDirected I (· ≤ ·)` is already a hypothesis of
the dimension shift.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **[Stacks, Tag 0EXZ] for systems of abelian sheaves on the small étale sites.** Every system
of abelian sheaves on the small étale sites of the levels of an inverse system of schemes admits a
levelwise monomorphism, compatible with the transitions, into a system whose sheaf at every level
is an injective object.

The compatibility is stated along `Stacks.EtaleCohomology.systemPullback`, the inverse image that
`Stacks.EtaleCohomology.EtaleSheafSystem` carries its transitions along, so that the statement is
the literal content of Tag 0EXZ for these systems with no comparison isomorphism in it. -/
def HasPointwiseInjectiveEmbeddings (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] : Prop :=
  ∀ F : EtaleSheafSystem D AddCommGrpCat.{u + 1},
    ∃ (G : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (f : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i),
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
          (systemPullback D AddCommGrpCat.{u + 1} a).map (f j) ≫ G.map a = F.map a ≫ f i) ∧
        (∀ i : Iᵒᵖ, Mono (f i)) ∧ ∀ i : Iᵒᵖ, Injective (G.obj i)

/-- **A dévissage datum for a presented system, from one levelwise embedding into a pointwise
injective system.**

Given a presented system `E` and an embedding `f_i : F_i ⟶ G_i` of its system into a pointwise
injective one, the datum is assembled as follows. The middle presented system is `G` with any
colimit presentation, which exists by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_isColimitPresentation`; the map `φ` on the
limit is the one the presentation of `E` induces from the family
`f_i^{-1}F_i ⟶ f_i^{-1}G_i ⟶ colim f_i^{-1}G_i`, and it is a monomorphism by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.mono_of_pointwise_mono`. The quotient system is
the levelwise cokernel and its presenting sheaf is the cokernel of `φ`; the legs come from the
cokernel property at each level, and the universal property is checked against the two
presentations already in hand. -/
theorem nonempty_devissage_of_mono_to_injective [IsDirected I (· ≤ ·)] [Nonempty I]
    [UnivLE.{v, u + 1}] (E : PresentedSystem (c := c) IsColimitPresentation)
    (G : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (f : ∀ i : Iᵒᵖ, E.sys.obj i ⟶ G.obj i)
    (hf : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback D AddCommGrpCat.{u + 1} a).map (f j) ≫ G.map a = E.sys.map a ≫ f i)
    (hmono : ∀ i : Iᵒᵖ, Mono (f i)) (hinj : ∀ i : Iᵒᵖ, Injective (G.obj i)) :
    Nonempty (Devissage E) := by
  -- the embedding and the levelwise projections, read in the constructed inverse image
  have hfe : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (f j) ≫ systemTransitionMap G a =
        systemTransitionMap E.sys a ≫ f i :=
    fun a => systemTransitionMap_naturality_of_map f hf a
  have hge : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (quotientSystemπ f hf j) ≫
          systemTransitionMap (quotientSystem f hf) a =
        systemTransitionMap G a ≫ quotientSystemπ f hf i :=
    fun a => systemTransitionMap_quotientSystemπ f hf a
  -- a colimit presentation of the injective system
  obtain ⟨𝒢G, ιG, hG⟩ := exists_isColimitPresentation (c := c) G
  -- the induced map on the limit, and its monomorphy
  have hτ : IsCompatibleFamily E.sys 𝒢G
      fun i => (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (f i) ≫ ιG i := by
    rw [isCompatibleFamily_iff_systemDiagramMap]
    intro i j a
    rw [← Category.assoc, systemDiagramMap_naturality f hfe a, Category.assoc,
      (isCompatibleFamily_iff_systemDiagramMap G 𝒢G ιG).mp hG.compatible a]
  obtain ⟨φ, hφfac⟩ : ∃ φ : E.sheaf ⟶ 𝒢G, ∀ i : Iᵒᵖ,
      E.ι i ≫ φ =
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (f i) ≫ ιG i :=
    ⟨E.pres.desc hτ, E.pres.desc_fac hτ⟩
  have : Mono φ := mono_of_pointwise_mono E.pres hG f hfe hmono φ hφfac
  -- the legs of the quotient presentation, out of the cokernel at each level
  have hzero : ∀ i : Iᵒᵖ,
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (f i) ≫ ιG i ≫ cokernel.π φ = 0 := by
    intro i
    rw [← Category.assoc, ← hφfac i, Category.assoc, cokernel.condition, comp_zero]
  choose ιQ hιQfac hιQuniq using fun i : Iᵒᵖ =>
    existsUnique_desc_quotientSystem f hf (conePi c i) (ιG i ≫ cokernel.π φ) (hzero i)
  have hepi : ∀ i : Iᵒᵖ,
      Epi ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (quotientSystemπ f hf i)) :=
    fun i => epi_map_quotientSystemπ f hf (conePi c i)
  -- the cokernel of `φ` presents the colimit of the quotient system
  have hQcomp : IsCompatibleFamily (quotientSystem f hf) (cokernel φ) ιQ := by
    rw [isCompatibleFamily_iff_systemDiagramMap]
    intro i j a
    have := hepi j
    refine (cancel_epi ((etaleAbelianInverseImage.{u, u + 1} (conePi c j)).map
      (quotientSystemπ f hf j))).mp ?_
    rw [← Category.assoc,
      ← systemDiagramMap_naturality (quotientSystemπ f hf) hge a, Category.assoc,
      hιQfac i, ← Category.assoc,
      (isCompatibleFamily_iff_systemDiagramMap G 𝒢G ιG).mp hG.compatible a, hιQfac j]
  have hQ : IsColimitPresentation (quotientSystem f hf) (cokernel φ) ιQ := by
    refine ⟨hQcomp, fun H σ hσ => ?_⟩
    have hσ' : IsCompatibleFamily G H
        fun i => (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map
          (quotientSystemπ f hf i) ≫ σ i := by
      rw [isCompatibleFamily_iff_systemDiagramMap]
      intro i j a
      rw [← Category.assoc, systemDiagramMap_naturality (quotientSystemπ f hf) hge a,
        Category.assoc, (isCompatibleFamily_iff_systemDiagramMap _ H σ).mp hσ a]
    obtain ⟨χ, hχfac⟩ : ∃ χ : 𝒢G ⟶ H, ∀ i : Iᵒᵖ, ιG i ≫ χ =
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (quotientSystemπ f hf i) ≫ σ i :=
      ⟨hG.desc hσ', hG.desc_fac hσ'⟩
    have hφχ : φ ≫ χ = 0 := by
      refine E.pres.hom_ext fun i => ?_
      rw [← Category.assoc, hφfac i, Category.assoc, hχfac i, ← Category.assoc,
        ← Functor.map_comp, comp_quotientSystemπ, Functor.map_zero, zero_comp, comp_zero]
    refine ⟨cokernel.desc φ χ hφχ, fun i => ?_, fun y hy => ?_⟩
    · have := hepi i
      refine (cancel_epi ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map
        (quotientSystemπ f hf i))).mp ?_
      rw [← Category.assoc, hιQfac i, Category.assoc, cokernel.π_desc, hχfac i]
    · have h1 : ∀ i : Iᵒᵖ, ιG i ≫ cokernel.π φ ≫ y =
          (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (quotientSystemπ f hf i) ≫
            σ i := by
        intro i
        rw [← Category.assoc, ← hιQfac i, Category.assoc, hy i]
      have h2 : cokernel.π φ ≫ y = χ := hG.hom_ext fun i => by rw [h1 i, hχfac i]
      refine (cancel_epi (cokernel.π φ)).mp ?_
      rw [h2, cokernel.π_desc]
  -- the short exact sequence on the limit
  have hSE' : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact φ
      mono_f := inferInstance
      epi_g := inferInstance }
  exact ⟨{ mid := presentedSystemOfIsColimitPresentation G 𝒢G ιG hG
           quot := presentedSystemOfIsColimitPresentation (quotientSystem f hf) (cokernel φ) ιQ hQ
           injective := hinj
           f := f
           g := quotientSystemπ f hf
           wf := comp_quotientSystemπ f hf
           shortExact := fun i => shortExact_quotientSystemπ f hf i (hmono i)
           φ := φ
           ψ := cokernel.π φ
           wφ := cokernel.condition φ
           shortExact' := hSE'
           ι_f := fun i => (hφfac i).symm
           ι_g := hιQfac
           map_f := fun a => hfe a
           map_g := fun a => hge a }⟩

/-- **[Stacks, Tag 0EXZ] on the small étale sites supplies the dévissage hypothesis of the
dimension shift of [Stacks, Tag 09YQ]**, for every presented system at once.

This is the hypothesis `Hdev` of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`,
discharged from the levelwise statement alone: the two colimit presentations and the short exact
sequence on the limit, which the datum also asks for, are supplied here. -/
theorem nonempty_devissage [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    (H : HasPointwiseInjectiveEmbeddings D) (E : PresentedSystem (c := c) IsColimitPresentation) :
    Nonempty (Devissage E) := by
  obtain ⟨G, f, hf, hmono, hinj⟩ := H E.sys
  exact nonempty_devissage_of_mono_to_injective E G f hf hmono hinj

/-- **The dimension shift of [Stacks, Tag 09YQ] with its dévissage hypothesis discharged.** Given

* the degree-zero statement `H0`,
* the vanishing `HV` of `H^q(X, colim f_i^{-1}G_i)` in positive degrees for a pointwise injective
  system, and
* [Stacks, Tag 0EXZ] on the small étale sites,

the colimit statement of Stacks 09YQ holds in every degree, for every system with a colimit
presentation.

This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`
with `Hdev` supplied by `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage`, and
it records what the dévissage of the source now costs: the levelwise statement alone. -/
theorem isCohomologyColimit_of_degreeZero_of_vanishing_of_injectiveEmbeddings
    [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    (H0 : ∀ E : PresentedSystem (c := c) IsColimitPresentation, IsCohomologyColimit E 0)
    (HV : ∀ E : PresentedSystem (c := c) IsColimitPresentation,
      (∀ i : Iᵒᵖ, Injective (E.sys.obj i)) →
      ∀ p : ℕ, 0 < p → Subsingleton (Sheaf.H.{u + 1, u + 1} E.sheaf p))
    (H0EXZ : HasPointwiseInjectiveEmbeddings D) (p : ℕ)
    (E : PresentedSystem (c := c) IsColimitPresentation) : IsCohomologyColimit E p :=
  isCohomologyColimit_of_degreeZero_of_vanishing H0 HV (nonempty_devissage H0EXZ) p E

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
