module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartMapCompletedEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumFiniteProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuotientSystemTransport
public import StacksFrontier.RingTheory.Rig.RigSmoothStabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjectiveRefined

/-!
# A finite affine étale covering of a chart is a completed étale localization

Let `S` be a scheme contained in a big fppf site `B` and let `τ : U₀ ⟶ V₀` be a chart map of
affine formal algebraic spaces over `S`, covered by a finite affine étale family
`{W s ⟶ U₀}` whose members carry maps `m s : W s ⟶ Z s` to affine formal algebraic spaces
representable étale over `V₀`. The proof of **Stacks 0ANG** needs this covering read on rings:
the chart rings of the `W s` are the completions of étale ring maps out of the chart ring of
`U₀`, the chart rings of the `Z s` are the completions of étale ring maps out of the chart ring
of `V₀`, and the *product* of the first family is the completion of a single étale and
**faithfully flat** ring map. That is exactly
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`, and this file concludes
it.

## Main results

* `AlgebraicGeometry.FormalSpace.isCompletedEtaleFiniteCoverOfChartMap_of_presentation`:
  `AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap` for a finite affine
  étale covering of the source of a chart map, at a class `C` which is closed under the
  completion of Stacks 0AN6 along an étale ring map and invariant under an isomorphism of
  topological rings.
* `isCompletedEtaleFiniteCoverOfChartMap_of_isCountablyWeaklyAdmissible`: the same at
  `C = WAdmᶜᵒᵘⁿᵗ`, where all three class conditions are theorems.
* `exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover`:
  `exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover` with its
  missing conjunct supplied, hence the whole conclusion of
  `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` at `C = WAdmᶜᵒᵘⁿᵗ`.

## The class condition this needs, and why it is not a gap

Beyond the two conditions its neighbours already carry — every ring of the class is weakly
admissible with a countable fundamental system of open ideals (`hCwa`), and the class is closed
under the completion of Stacks 0AN6 along an étale ring map (`hCcomp`) — concluding the clause
needs one more: `C` is invariant under an isomorphism of topological rings (`hCiso`). It is
unavoidable and it is not a stand-in.

The clause asks for `C (∀ i, Wr i)` on the *product* of the chart rings of the covering. The
product is not itself a completion: what the construction produces is the completion
`CompletionOver c` of the single étale ring map `c : R →+* ∀ i, Bw i` whose factors present the
members, and the identification with the product is the bicontinuous
`TopologicalRing.CompletionOver.piRingEquiv`. So `C` of the product is `C` of a completion read
through an isomorphism, and nothing weaker than invariance under one will do.

It is a condition on the class *parameter*, dischargeable wherever the parameter is
instantiated, not a deferred theorem: it holds for `WAdmᶜᵒᵘⁿᵗ` by
`TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv` and for `WAdmᴺᵒᵉᵗʰ` by
`TopologicalRing.isNoetherianAdic_of_ringEquiv`, which are the two classes at which the
consumers of `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` instantiate it.
It is also the shape `TopologicalRing.PropertyIsLocal'` already carries for the property `P`, as
its field `isomorphismInvariant`. It is placed on this theorem rather than on
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` itself, so that the predicate
and its nine consumers are untouched.

## Implementation notes

The index type. `IsCompletedEtaleFiniteCoverOfChartMap` asks for a finite `ι : Type u` together
with `κ : ι → σ`, where the covering is indexed by a finite `σ : Type (u + 1)`; `ι` must be in
the universe of the chart rings because the rings `Zr i`, `Wr i`, `Bz i` it indexes are there.
A finite type is equivalent to `ULift.{u} (Fin n)`, and `κ` is that equivalence inverted. The
members of the covering are reindexed by `κ` and the covering itself is not: joint surjectivity
is consumed at the original index `σ`, so one `eqToHom` mediates, and
`eqToHom (congrArg W h) ≫ p t = p s` for `h : s = t` is proved where it is used.

Why the members are presentable at all. The clause demands rings of the class presenting
`W (κ i)` and `Z (κ i)`, and neither is hypothesised: `W (κ i) ⟶ U₀` and `Z (κ i) ⟶ V₀` are
representable étale out of affine formal algebraic spaces, so the essential-surjectivity clause
of **Stacks 0AN8**, `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`, presents them as
the formal spectra of completions of étale ring maps out of the given presentations of `U₀` and
`V₀`. That is why `ez i` can be taken to be the identity: the ring presenting `Z (κ i)` *is*
`CompletionOver (bz i)`, not merely isomorphic to it.

Faithful flatness. This is the only place the covering hypothesis is used, through
**Stacks 0AN9**: condition (1) of `etaleFormalSpectrumMap_surjective_tfae` is surjectivity of a
*single* formal spectrum map, and the covering gives a jointly surjective *family*. The passage
is `AlgebraicGeometry.FormalSpace.isSurjective_formalSpectrumMap_continuousHomPi`'s underlying
lemma, `AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective_sigmaDesc_of_factors`:
each member factors through `Spf (∀ i, Wr i)` along the formal spectrum of a coordinate
projection, and `Spf (∀ i, Wr i) ≅ Spf (CompletionOver c)` because a quotient system transports
along a bicontinuous isomorphism
(`AlgebraicGeometry.FormalSpace.quotientSystemOfRingEquiv`). Stacks 0AN9 is applied at the
transported system, which is the one its statement is about.

The final ring equation is not checked by hand on the product. Coordinatewise it is the
commutativity of the triangle `A → R → Wr i` versus `A → Zr i → Wr i`, and that is settled the
way the square of
`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation` is:
the two composites are continuous homomorphisms over `S` whose formal spectra agree — the given
square `p s ≫ τ = m s ≫ d s` transported along the identifications — and faithfulness of `Spf`,
the uniqueness half of
`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`, forces the ring
maps to agree.

## What this does *not* close

`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` is still open, and not because
of this clause. Its *first* presentation clause needs the members `U i`, `V i` of the covering
being refined to be countably indexed, which the predicate's hypothesis — that the two ends of
`f` are locally countably indexed — gives only through the implication (2) ⟹ (1) of
**Stacks 0AKX**; that implication is not in the library. So
`exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover` below asks countable
indexedness of the members directly, exactly as the theorem it extends does, and Stacks 0AKX is
now the sole remaining obstruction (and as quantified over an arbitrary property it is false;
see `AtlasChartCountablyIndexed.lean`).

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)

/-- **A finite affine étale covering of the source of a chart map, presented by completed étale
localizations.** Let `τ : U₀ ⟶ V₀` be a chart map of affine formal algebraic spaces over `S`,
let `{p s : W s ⟶ U₀}` be a finite affine étale covering of its source, and let
`m s : W s ⟶ Z s`, `d s : Z s ⟶ V₀` be a factorization of `p s ≫ τ` through affine formal
algebraic spaces representable étale over `V₀`. Then the covering is presented by completed
étale localizations in the sense of
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`.

Given a presentation `g : A →+* R` of `τ` by rings of the class `C`, the essential-surjectivity
clause of **Stacks 0AN8** presents each `W (κ i)` as `Spf (CompletionOver (bw i))` for an étale
`bw i : R →+* Bw i` and each `Z (κ i)` as `Spf (CompletionOver (bz i))` for an étale
`bz i : A →+* Bz i`; **Stacks 0AN0** then presents each `m (κ i)` by a continuous homomorphism
between those two rings. The completion of the single étale map `c := RingHom.pi bw` is the
product of the `CompletionOver (bw i)` by
`TopologicalRing.CompletionOver.piRingEquiv`, and `c` is faithfully flat by **Stacks 0AN9**,
whose condition (1) — surjectivity of `Spf (CompletionOver c) ⟶ Spf R` — is the joint
surjectivity of the covering read through that identification.

The hypothesis `hCwa` says that every ring of the class is weakly admissible with a countable
fundamental system of open ideals and `hCcomp` that the class is closed under the completion of
Stacks 0AN6 along an étale ring map, as in
`AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation`;
`hCiso` says that the class is invariant under an isomorphism of topological rings, which is
what `C` of the *product* of the chart rings of the covering needs. All three hold for
`WAdmᶜᵒᵘⁿᵗ` and for `WAdmᴺᵒᵉᵗʰ`; see the module docstring.

NO TAG IS ATTACHED: this is finite-product bookkeeping inside the proof of Stacks 0ANG, not a
numbered statement of the source, and the three source results it rests on — Stacks 0AN8,
Stacks 0AN0 and Stacks 0AN9 — are registered where they are proved. -/
theorem isCompletedEtaleFiniteCoverOfChartMap_of_presentation
    (hCwa : ∀ (X : Type u) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X], C X →
      TopologicalRing.IsWeaklyAdmissible X ∧ (nhds (0 : X)).IsCountablyGenerated)
    (hCcomp : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] (φ : X →+* Y),
      TopologicalRing.IsWeaklyAdmissible X → φ.Etale → C X →
        C (TopologicalRing.CompletionOver φ))
    (hCiso : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y]
      [IsLinearTopology Y Y] (e : X ≃+* Y), Continuous e → Continuous e.symm → C X → C Y)
    {U₀ V₀ : FppfSheaf B S hS} {τ : U₀ ⟶ V₀} {σ : Type (u + 1)} (hσ : Finite σ)
    {W Z : σ → FppfSheaf B S hS} (p : ∀ s, W s ⟶ U₀) (m : ∀ s, W s ⟶ Z s) (d : ∀ s, Z s ⟶ V₀)
    (hWcover : IsAffineEtaleCover B S hS W p)
    (hZaffine : ∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s))
    (hd : ∀ s, IsRepresentableEtale B S hS (d s))
    (hsq : ∀ s, p s ≫ τ = m s ≫ d s) :
    IsCompletedEtaleFiniteCoverOfChartMap B S hS C τ W Z m := by
  have := hσ
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg Goal hGoal
  have hRwa : TopologicalRing.IsWeaklyAdmissible R := (hCwa R hCR).1
  -- the index type of the product: a finite type in the universe of the chart rings
  obtain ⟨n, ⟨e0⟩⟩ := Finite.exists_equiv_fin σ
  set ε : σ ≃ ULift.{u} (Fin n) := e0.trans Equiv.ulift.symm
  set κ : ULift.{u} (Fin n) → σ := fun i ↦ ε.symm i
  -- a map out of the covering may be reindexed along `κ ∘ ε = id`
  have hreidx : ∀ {X : FppfSheaf B S hS} (q : ∀ s, W s ⟶ X) (s t : σ) (h : s = t),
      eqToHom (congrArg W h) ≫ q t = q s := by
    intro X q s t h
    subst h
    simp
  -- the members of the covering, and the charts they map to, are presented by Stacks 0AN8
  choose Bw iBwR iBwA hBwE Ew cw εw hcw hεw using fun i ↦
    isEssentiallySurjectiveSpf B S hS R hRwa E
      (hasLargeSite_of_mk_lt_cutoff E
        (mk_lt_cutoff_of_isCountablyGenerated B S hS E hRwa (hCwa R hCR).2)) (W (κ i))
      (p (κ i) ≫ eU.hom) (hWcover.1 (κ i))
      ((hWcover.2.1 (κ i)).comp B S hS (isRepresentableEtale_of_isIso B S hS _))
  choose Bz iBzR iBzA hBzE Dz cz εz hcz hεz using fun i ↦
    isEssentiallySurjectiveSpf B S hS A hA D
      (hasLargeSite_of_mk_lt_cutoff D
        (mk_lt_cutoff_of_isCountablyGenerated B S hS D hA (hCwa A hCA).2)) (Z (κ i))
      (d (κ i) ≫ eV.hom) (hZaffine (κ i))
      ((hd (κ i)).comp B S hS (isRepresentableEtale_of_isIso B S hS _))
  let : ∀ i, CommRing (Bw i) := iBwR
  let : ∀ i, Algebra R (Bw i) := iBwA
  let : ∀ i, Algebra.Etale R (Bw i) := hBwE
  let : ∀ i, CommRing (Bz i) := iBzR
  let : ∀ i, Algebra A (Bz i) := iBzA
  let : ∀ i, Algebra.Etale A (Bz i) := hBzE
  set bw : ∀ i, R →+* Bw i := fun i ↦ algebraMap R (Bw i)
  set bz : ∀ i, A →+* Bz i := fun i ↦ algebraMap A (Bz i)
  have hbwE : ∀ i, (bw i).Etale := fun i ↦ RingHom.etale_algebraMap.mpr (hBwE i)
  have hbzE : ∀ i, (bz i).Etale := fun i ↦ RingHom.etale_algebraMap.mpr (hBzE i)
  have hWrwa : ∀ i, TopologicalRing.IsWeaklyAdmissible
      (TopologicalRing.CompletionOver (bw i)) := fun i ↦
    TopologicalRing.completionOver_isWeaklyAdmissible _ hRwa
  have hZrwa : ∀ i, TopologicalRing.IsWeaklyAdmissible
      (TopologicalRing.CompletionOver (bz i)) := fun i ↦
    TopologicalRing.completionOver_isWeaklyAdmissible _ hA
  have hCWr : ∀ i, C (TopologicalRing.CompletionOver (bw i)) := fun i ↦
    hCcomp (bw i) hRwa (hbwE i) hCR
  have hCZr : ∀ i, C (TopologicalRing.CompletionOver (bz i)) := fun i ↦
    hCcomp (bz i) hA (hbzE i) hCA
  -- Stacks 0AN0 presents each `m (κ i)` between the two chart rings
  choose μ hμ using fun i ↦ (existsUnique_continuousHom_formalSpectrumMap_eq (hZrwa i)
    (hWrwa i) ((εw i).inv ≫ m (κ i) ≫ (εz i).hom)).exists
  have hmeq : ∀ i, m (κ i) =
      (εw i).hom ≫ formalSpectrumMap (hZrwa i) (μ i) ≫ (εz i).inv := by
    intro i
    rw [hμ i]
    simp
  -- the product of the chart rings of the covering is the completion of one étale map
  let : IsLinearTopology (∀ i, TopologicalRing.CompletionOver (bw i))
      (∀ i, TopologicalRing.CompletionOver (bw i)) := TopologicalRing.pi_isLinearTopology
  set c : R →+* ∀ i, Bw i := RingHom.pi bw
  have hcE : c.Etale := RingHom.Etale.pi bw hbwE
  set ew : TopologicalRing.CompletionOver c ≃+*
      ∀ i, TopologicalRing.CompletionOver (bw i) :=
    TopologicalRing.CompletionOver.piRingEquiv bw
  have hewc : Continuous ew := TopologicalRing.CompletionOver.continuous_piRingEquiv bw
  have hewsc : Continuous ew.symm :=
    TopologicalRing.CompletionOver.continuous_piRingEquiv_symm bw
  have hewss : Continuous ew.symm.symm := hewc
  have hprodwa : TopologicalRing.IsWeaklyAdmissible
      (∀ i, TopologicalRing.CompletionOver (bw i)) :=
    TopologicalRing.isWeaklyAdmissible_pi _ hWrwa
  have hccwa : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletionOver c) :=
    TopologicalRing.completionOver_isWeaklyAdmissible c hRwa
  have hCprod : C (∀ i, TopologicalRing.CompletionOver (bw i)) :=
    hCiso ew hewc hewsc (hCcomp c hRwa hcE hCR)
  -- the quotient system of the product, transported to the completion of `c`
  set Eprod := quotientSystemPi B S hS Ew
  set gprod : ContinuousHom E Eprod := continuousHomPi B S hS Ew cw with hgprod
  set Ec : QuotientSystem B S hS (TopologicalRing.CompletionOver c) :=
    quotientSystemOfRingEquiv B S hS ew.symm hewsc hewss Eprod
  set chOf : ContinuousHom Eprod Ec :=
    continuousHomOfRingEquiv B S hS ew.symm hewsc hewss Eprod
  set chSymm : ContinuousHom Ec Eprod :=
    continuousHomOfRingEquivSymm B S hS ew.symm hewsc hewss Eprod
  set gc : ContinuousHom E Ec := ContinuousHom.comp hprodwa hRwa chOf gprod with hgc
  have hcanon : ∀ x : R, ew (TopologicalRing.CompletionOver.canonicalMap c x) =
      fun i ↦ (cw i).toRingHom x := by
    intro x
    funext i
    rw [hcw i]
    exact congrFun (TopologicalRing.CompletionOver.piRingEquiv_canonicalMap bw x) i
  have hgcring : gc.toRingHom = TopologicalRing.CompletionOver.canonicalMap c := by
    refine RingHom.ext fun x ↦ ?_
    have hstep : gc.toRingHom x = ew.symm (fun i ↦ (cw i).toRingHom x) := rfl
    rw [hstep, ← hcanon x, ew.symm_apply_apply]
  -- Stacks 0AN9, condition (1): the covering makes `Spf (CompletionOver c) ⟶ Spf R` surjective
  have hiso : formalSpectrumMap hccwa chSymm ≫ formalSpectrumMap hprodwa chOf =
      𝟙 (formalSpectrum Eprod) := by
    rw [formalSpectrumMap_comp_eq hccwa hprodwa chSymm chOf]
    refine formalSpectrumMap_id hprodwa _ ?_
    refine RingHom.ext fun x ↦ ?_
    change ew (ew.symm x) = x
    exact ew.apply_symm_apply x
  have hρ : formalSpectrumMap hccwa chSymm ≫ formalSpectrumMap hRwa gc =
      formalSpectrumMap hRwa gprod := by
    rw [hgc, ← formalSpectrumMap_comp_eq hprodwa hRwa chOf gprod, ← Category.assoc, hiso,
      Category.id_comp]
  have hls : Sheaf.IsLocallySurjective (Sigma.desc fun s ↦ p s ≫ eU.hom) := by
    have := hWcover.2.2
    have heq : (Sigma.desc fun s ↦ p s ≫ eU.hom) = Sigma.desc p ≫ eU.hom :=
      Sigma.hom_ext _ _ fun s ↦ by simp
    rw [heq]
    infer_instance
  have hfactor : ∀ s, (eqToHom (congrArg W (ε.symm_apply_apply s).symm) ≫ (εw (ε s)).hom ≫
        formalSpectrumMap hprodwa (continuousHomPiProjection B S hS Ew (ε s)) ≫
          formalSpectrumMap hccwa chSymm) ≫ formalSpectrumMap hRwa gc = p s ≫ eU.hom := by
    intro s
    rw [Category.assoc, Category.assoc, Category.assoc, hρ, hgprod,
      formalSpectrumMap_continuousHomPiProjection_comp B S hS hprodwa hRwa Ew cw (ε s),
      hεw (ε s), ← Category.assoc]
    exact hreidx (fun t ↦ p t ≫ eU.hom) s (κ (ε s)) (ε.symm_apply_apply s).symm
  have hsurj : IsSurjective B S hS (formalSpectrumMap hRwa gc) :=
    isSurjective_of_isLocallySurjective_sigmaDesc_of_factors B S hS
      (fun s ↦ p s ≫ eU.hom) hls _ hfactor
  have hcff : c.FaithfullyFlat :=
    ((etaleFormalSpectrumMap_surjective_tfae B S hS c hcE hRwa E Ec gc hgcring).out 1 2).mp hsurj
  -- the final ring equation, coordinatewise the commutativity of `A → R → Wr i`
  have hkey : ∀ i, (cw i).toRingHom.comp g.toRingHom =
      (μ i).toRingHom.comp (cz i).toRingHom := by
    intro i
    have hgeo : formalSpectrumMap hRwa (cw i) ≫ formalSpectrumMap hA g =
        formalSpectrumMap (hZrwa i) (μ i) ≫ formalSpectrumMap hA (cz i) := by
      refine (Iso.cancel_iso_hom_left (εw i) _ _).mp ?_
      have hleft : (εw i).hom ≫ formalSpectrumMap hRwa (cw i) ≫ formalSpectrumMap hA g =
          p (κ i) ≫ eU.hom ≫ formalSpectrumMap hA g := by
        rw [← Category.assoc, hεw i, Category.assoc]
      have hmid : eU.hom ≫ formalSpectrumMap hA g = τ ≫ eV.hom := by
        rw [hg]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hright : (εw i).hom ≫ formalSpectrumMap (hZrwa i) (μ i) ≫
            formalSpectrumMap hA (cz i) =
          m (κ i) ≫ (εz i).hom ≫ formalSpectrumMap hA (cz i) := by
        rw [hmeq i]
        simp
      rw [hleft, hright, hmid, hεz i, ← Category.assoc, ← Category.assoc, hsq (κ i)]
    have hceq : ContinuousHom.comp hRwa hA (cw i) g =
        ContinuousHom.comp (hZrwa i) hA (μ i) (cz i) := by
      refine (existsUnique_continuousHom_formalSpectrumMap_eq hA (hWrwa i)
        (formalSpectrumMap hRwa (cw i) ≫ formalSpectrumMap hA g)).unique
        (formalSpectrumMap_comp_eq hRwa hA (cw i) g).symm ?_
      rw [← formalSpectrumMap_comp_eq (hZrwa i) hA (μ i) (cz i), ← hgeo]
    simpa only [ContinuousHom.comp_toRingHom] using congrArg ContinuousHom.toRingHom hceq
  refine hGoal (ULift.{u} (Fin n)) κ (fun i ↦ TopologicalRing.CompletionOver (bz i))
    (fun i ↦ TopologicalRing.CompletionOver (bw i)) Bz (∀ i, Bw i) hCZr hCWr hCprod hZrwa
    Dz Ew εw εz μ hmeq bz hbzE (fun i ↦ RingEquiv.refl _) (fun _ ↦ continuous_id)
    (fun _ ↦ continuous_id) c hcE hcff ew hewc hewsc ?_
  refine RingHom.ext fun x ↦ funext fun i ↦ ?_
  change ew (TopologicalRing.CompletionOver.canonicalMap c (g.toRingHom x)) i = _
  rw [hcanon]
  have := RingHom.congr_fun (hkey i) x
  simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
  rw [this, hcz i]
  rfl

/-- **A finite affine étale covering of the source of a chart map of countably indexed affine
formal algebraic spaces is presented by completed étale localizations.** At the class
`WAdmᶜᵒᵘⁿᵗ` the three class conditions of
`AlgebraicGeometry.FormalSpace.isCompletedEtaleFiniteCoverOfChartMap_of_presentation` are
theorems: `hCwa` holds by the definition of
`TopologicalRing.IsCountablyWeaklyAdmissible`, `hCcomp` is
`TopologicalRing.isCountablyWeaklyAdmissible_completionOver` — two clauses of **Stacks 0ANB** —
and `hCiso` is `TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv`.

This is the shape in which the proof of Stacks 0ANG uses the clause. NO TAG IS ATTACHED, for
the reason given on
`AlgebraicGeometry.FormalSpace.isCompletedEtaleFiniteCoverOfChartMap_of_presentation`. -/
theorem isCompletedEtaleFiniteCoverOfChartMap_of_isCountablyWeaklyAdmissible
    {U₀ V₀ : FppfSheaf B S hS} {τ : U₀ ⟶ V₀} {σ : Type (u + 1)} (hσ : Finite σ)
    {W Z : σ → FppfSheaf B S hS} (p : ∀ s, W s ⟶ U₀) (m : ∀ s, W s ⟶ Z s) (d : ∀ s, Z s ⟶ V₀)
    (hWcover : IsAffineEtaleCover B S hS W p)
    (hZaffine : ∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s))
    (hd : ∀ s, IsRepresentableEtale B S hS (d s))
    (hsq : ∀ s, p s ≫ τ = m s ≫ d s) :
    IsCompletedEtaleFiniteCoverOfChartMap B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible τ W Z m :=
  isCompletedEtaleFiniteCoverOfChartMap_of_presentation B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible (fun _ _ _ _ _ hX ↦ hX)
    (fun φ _ _ hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hX)
    (fun e he he' hX ↦ TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv e he he' hX)
    hσ p m d hWcover hZaffine hd hsq

/-- **The refinement of a covering of the source against an affine étale diagram, presented.**
This is `exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover` with its
missing conjunct supplied: the conclusion below is *verbatim* the conclusion of
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` at
`C = WAdmᶜᵒᵘⁿᵗ`, both presentation clauses included.

What separates this from that predicate is no longer either clause but the two hypotheses
`hUcount` and `hVcount`: the predicate asks only that the two ends of `f` be locally countably
indexed, and the step from there to countable indexedness of the members `U i`, `V i` of the
covering being refined is the implication (2) ⟹ (1) of **Stacks 0AKX**, which the library does
not carry.

NO TAG IS ATTACHED: like the refinement it extends, this is a step inside the proof of
Stacks 0ANG rather than a numbered statement of the source. -/
theorem exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    (hUcount : ∀ i, IsCountablyIndexed B S hS (U i))
    (hVcount : ∀ i, IsCountablyIndexed B S hS (V i))
    {U₀ V₀ : FppfSheaf B S hS} (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ (∀ s, p s ≫ τ = m s ≫ c s) ∧
        (∀ s, IsCompletedEtaleLocalizationOfChartMap B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible (t (k s)) (m s)) ∧
        IsCompletedEtaleFiniteCoverOfChartMap B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible τ W Z m := by
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂, hloc⟩ :=
    exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover B S hS f U V
      u v t hUcover hVaffine hVetale hVsquare hUcount hVcount a b τ hU₀ hV₀ ha hb hsquare
  exact ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂, hloc,
    isCompletedEtaleFiniteCoverOfChartMap_of_isCountablyWeaklyAdmissible B S hS hσ p m c
      hWcover hZaffine hc hsq₂⟩

end AlgebraicGeometry.FormalSpace

end
