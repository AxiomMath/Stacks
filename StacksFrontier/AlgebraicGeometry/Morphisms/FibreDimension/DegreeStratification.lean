module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Free
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.Topology.Constructible.MeetConstructible

/-!
# Stratification of the base by the degree of a flat locally quasi-finite morphism

Let `f : X ⟶ S` be separated, flat, locally of finite presentation and locally quasi-finite, with
universally bounded fibres. Then `S` carries a finite filtration by closed subsets
`∅ = Z₋₁ ⊆ Z₀ ⊆ … ⊆ Zₙ = S` whose strata `Sᵣ = Zᵣ ∖ Zᵣ₋₁` are characterised by a universal
property: for a morphism `g : T ⟶ S`, the projection `X ×_S T ⟶ T` is finite locally free of
degree `r` exactly when the image of `T` lies in `Sᵣ`. This is [Stacks Project, Tag 07RY].

Dropping the bound on the fibre degrees and asking instead that `f` be quasi-finite, the same
filtration exists with infinitely many steps, and each stratum is an immersed subscheme of `S`
whose inclusion is quasi-compact. This is [Stacks Project, Tag 07RZ].

## Main results

* `AlgebraicGeometry.exists_closed_filtration_characterizing_finiteLocallyFree_rank` constructs
  the filtration and states its universal property.
* `AlgebraicGeometry.exists_quasiCompact_stratification_of_finiteLocallyFree_rank` is the same
  for a quasi-finite morphism, with no bound on the fibre degrees assumed, and adds that the
  inclusion of each stratum is quasi-compact.
* `AlgebraicGeometry.isClosed_fiber_rank_lt` is the lower semicontinuity of the fibre degree
  which makes each `Zᵣ` closed, and `AlgebraicGeometry.existsUnique_rank_of_bounded_fiber`,
  `AlgebraicGeometry.finiteLocallyFree_rank_unique` say that a bounded fibre has one and only
  one degree.
* `AlgebraicGeometry.finite_open_rank_le_of_field` compares the degrees of a finite scheme over
  a field and of an open subscheme of it, and
  `AlgebraicGeometry.finiteLocallyFreeOfRank_residueFiber_baseChange`,
  `AlgebraicGeometry.rank_of_constant_fiber_rank`,
  `AlgebraicGeometry.rank_pullback_symmetry` move a degree between a morphism, its base changes
  and its fibres.

## Implementation notes

For a bound `n` the filtration from `Z₋₁` through `Zₙ` is indexed by `Fin (n + 2)`, so that the
stratum of degree `r` is `Z (r + 1) ∖ Z r`. Set-theoretic containment of the image of a morphism
of schemes is expressed through its underlying map of topological spaces.

The whole argument rests on the étale splitting of a locally quasi-finite separated morphism,
[Stacks Project, Tag 02LP]: around any point of the base there is an elementary étale
neighbourhood over which the source splits as a finite part and a part with no isolated point in
the distinguished fibre, and universal boundedness makes the second part's fibre empty. The
finite part is finite locally free because it is finite, flat and locally of finite presentation,
[Stacks Project, Tag 02KB], and after shrinking the neighbourhood its degree is the degree of the
fibre one started from. This gives at once lower semicontinuity of the fibre degree — whence each
`Zᵣ` is closed — and, when the fibre degree is constant, finite local freeness of `f` of that
degree.

The passage from the étale-local statement to the global one is done in two steps rather than by
descending the degree along the covering. Being finite locally free is fpqc local on the base,
`Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc_of_isAffineHom` together with
[Stacks Project, Tag 02L5], so `f` is finite locally free; the degree is then pinned down by the
decomposition of the base into clopen pieces of constant degree,
[Stacks Project, Tag 04MH], since the fibre degree over a piece of degree `d` is `d` and the
fibre degree over a field determines, and is determined by, the dimension of the global sections.
Only Zariski locality of the degree is used.

Without a bound on the fibre degrees the filtration is indexed by `ℕ`, the `r`-th step being the
locus where the fibre degree is less than `r`, so that the source's `Z₋₁` is the empty zeroth
step. Each fibre has a degree because a quasi-finite flat morphism of finite presentation is
finite over a field, and the bound that lower semicontinuity needs is supplied one affine open of
the base at a time by [Stacks Project, Tag 03JA]. Quasi-compactness of the inclusion of a stratum
is retrocompactness of its underlying set, proved by induction on `r`: inside an affine open of
the base lying over the previous strata, the locus of degree `r` is the image of a closed
immersion of finite presentation, so its complement is constructible and hence retrocompact by
Chevalley's theorem. That closed immersion comes from writing the stratum as the limit of the
closed subschemes of finite presentation containing it and descending finite local freeness to a
stage, [Stacks Project, Tag 06AC], and then passing to the clopen piece of that stage on which
the degree is `r`; the fixed-degree refinement of Tag 06AC is not needed.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 02LP](https://stacks.math.columbia.edu/tag/02LP)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
* [Stacks Project, Tag 054J](https://stacks.math.columbia.edu/tag/054J)
* [Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Morphisms AlgebraicGeometry.ConnectedComponentSection

universe u

namespace AlgebraicGeometry

/-- Precomposition with an isomorphism does not change the rank of a finite locally free
morphism. -/
public lemma rank_comp_iso {X Y S : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ S) (r : ℕ) :
    IsFiniteLocallyFreeOfRank f r ↔ IsFiniteLocallyFreeOfRank (e.hom ≫ f) r :=
  (MorphismProperty.cancel_left_of_respectsIso
    (P := IsFiniteLocallyFreeOfRank.property.{u} r) e.hom f).symm

/-- A property invariant under isomorphisms does not distinguish the two projections of a fibre
product. -/
private lemma prop_pullback_symm_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    P (pullback.fst g f) ↔ P (pullback.snd f g) := by
  have he : (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g := by simp
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P)
    (pullbackSymmetry f g).hom (pullback.fst g f)).symm

/-- The rank of a restriction to an open of the base is the rank of the base change along the
inclusion of that open. -/
private lemma rank_pullback_snd_ι_of_restrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (r : ℕ) (h : IsFiniteLocallyFreeOfRank (f ∣_ U) r) :
    IsFiniteLocallyFreeOfRank (pullback.snd f U.ι) r := by
  have he : (pullbackRestrictIsoRestrict f U).hom ≫ (f ∣_ U) = pullback.snd f U.ι := by simp
  rw [← he]
  exact (rank_comp_iso (pullbackRestrictIsoRestrict f U) (f ∣_ U) r).mp h

/-- The two projections of a fibre product carry the same rank data. -/
public lemma rank_pullback_symmetry {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (r : ℕ) :
    IsFiniteLocallyFreeOfRank (pullback.fst g f) r ↔
      IsFiniteLocallyFreeOfRank (pullback.snd f g) r :=
  prop_pullback_symm_iff (IsFiniteLocallyFreeOfRank.property.{u} r) f g

/-- The rank of a finite locally free morphism is inherited by its base changes. -/
private lemma rank_pullback_snd {X S T : Scheme.{u}} {f : X ⟶ S} (g : T ⟶ S) {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank f r) : IsFiniteLocallyFreeOfRank (pullback.snd f g) r := by
  let := h
  exact IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback f g)

/-- Fixed ranks over a field agree, as both are the dimension of global sections. -/
public lemma finiteLocallyFree_rank_unique
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (r t : ℕ)
    (hr : IsFiniteLocallyFreeOfRank f r)
    (ht : IsFiniteLocallyFreeOfRank f t) : r = t := by
  let : IsFiniteLocallyFreeOfRank f r := hr
  let : IsFiniteLocallyFreeOfRank f t := ht
  exact (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank f r).2.symm.trans
    (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank f t).2

/-- For a closed immersion between finite locally free schemes over a field, the surjection on
global sections forces `n ≤ m` for the degrees, and if moreover `m ≤ n` the dimensions agree, so
the surjection is injective and the closed immersion is an isomorphism. -/
private lemma closedImmersion_rank_le_and_isIso
    {k : Type u} [Field k] {Z V : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (i : V ⟶ Z) (m n : ℕ)
    (hm : IsFiniteLocallyFreeOfRank p m)
    (hn : IsFiniteLocallyFreeOfRank (i ≫ p) n)
    (hclosed : IsClosedImmersion i) : n ≤ m ∧ (m ≤ n → IsIso i) := by
  let : IsFiniteLocallyFreeOfRank p m := hm
  let : IsFiniteLocallyFreeOfRank (i ≫ p) n := hn
  let : IsAffine Z := isAffine_of_isAffineHom p
  let : IsAffine V := isAffine_of_isAffineHom (i ≫ p)
  let : IsClosedImmersion i := hclosed
  let A := Γ(Z, ⊤)
  let B := Γ(V, ⊤)
  let α : CommRingCat.of k ⟶ Γ(Z, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  let β : CommRingCat.of k ⟶ Γ(V, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ p).appTop
  let : Algebra k A := α.hom.toAlgebra
  let : Algebra k B := β.hom.toAlgebra
  have hcomp : i.appTop.hom.comp α.hom = β.hom := by
    have hcat : α ≫ i.appTop = β := by
      dsimp [α, β]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom hcat
  let φ : A →ₐ[k] B := {
    toRingHom := i.appTop.hom
    commutes' := fun x => congrArg (fun q : k →+* B => q x) hcomp }
  have hsurj : Function.Surjective φ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hdimA := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank
    (k := k) p m
  have hdimB := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank
    (k := k) (i ≫ p) n
  let : Module.Finite k A := hdimA.1
  let : Module.Finite k B := hdimB.1
  have hA : Module.finrank k A = m := hdimA.2
  have hB : Module.finrank k B = n := hdimB.2
  have hn_le_m : n ≤ m := by
    rw [← hB, ← hA]
    exact LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj
  refine ⟨hn_le_m, fun hmn => ?_⟩
  have heq : Module.finrank k A = Module.finrank k B := by omega
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) heq).mpr hsurj
  exact IsClosedImmersion.isIso_of_injective_of_isAffine (f := i) hinj

/-- An open immersion into a finite scheme over a field has degree at most that of the ambient
scheme: the ambient scheme is discrete, so the open immersion is also closed, and its map on
global sections is surjective. -/
public lemma finite_open_rank_le_of_field
    {k : Type u} [Field k] {A B : Scheme.{u}} (i : B ⟶ A)
    (p : A ⟶ Spec (.of k)) (r s : ℕ)
    [IsOpenImmersion i] [IsFinite p] [IsFinite (i ≫ p)]
    (hr : IsFiniteLocallyFreeOfRank p r)
    (hs : IsFiniteLocallyFreeOfRank (i ≫ p) s) : s ≤ r := by
  let : IsFiniteLocallyFreeOfRank p r := hr
  let : IsFiniteLocallyFreeOfRank (i ≫ p) s := hs
  let : IsArtinianScheme A := {
    toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite p
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p
  }
  have : DiscreteTopology A :=
    IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mp inferInstance |>.2
  have hclosed : IsClosedImmersion i := .of_isPreimmersion i
    (isClosed_discrete (Set.range i.base))
  exact (closedImmersion_rank_le_and_isIso p i r s hr hs hclosed).1

/-- The spectrum of the residue field at a point of an open subscheme maps into that open
subscheme, compatibly with the canonical morphism to the whole scheme, with the point as image. -/
private lemma residueField_lift_to_open
    {S : Scheme.{u}} (U : S.Opens) (s : S) (hs : s ∈ U) :
    ∃ (g : Spec (S.residueField s) ⟶ U),
      g ≫ U.ι = S.fromSpecResidueField s ∧
        Set.range g.base = {⟨s, hs⟩} := by
  have hsub : Set.range (S.fromSpecResidueField s).base ⊆ Set.range U.ι.base := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hs
  let g := IsOpenImmersion.lift U.ι (S.fromSpecResidueField s) hsub
  refine ⟨g, IsOpenImmersion.lift_fac U.ι (S.fromSpecResidueField s) hsub, ?_⟩
  have hg (t : Spec (S.residueField s)) : g t = ⟨s, hs⟩ := by
    apply U.ι.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac U.ι
      (S.fromSpecResidueField s) hsub]
    simp
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact hg t
  · intro hx
    have ht : Nonempty (Spec (S.residueField s)) := by
      have hne : (Set.range (S.fromSpecResidueField s).base).Nonempty := by
        rw [Scheme.range_fromSpecResidueField]
        exact Set.singleton_nonempty _
      obtain ⟨_, t, _⟩ := hne
      exact ⟨t⟩
    exact ⟨Classical.choice ht, by simpa [hg] using hx.symm⟩

/-- Complementary opens have complementary underlying sets. -/
private lemma isCompl_coe_of_isCompl {Y : Scheme.{u}} {W V : Y.Opens} (hc : IsCompl W V) :
    IsCompl (W : Set Y) (V : Set Y) :=
  ⟨Opens.coe_disjoint.mpr hc.disjoint, codisjoint_iff.mpr (by
    change (W : Set Y) ∪ V = Set.univ
    simpa only [Opens.coe_sup, Opens.coe_top] using
      congrArg (fun a : Y.Opens => (a : Set Y)) hc.sup_eq_top)⟩

/-- For a complementary pair of opens, the inclusion of either one is a closed immersion: its
range is the complement of the other, which is closed. -/
private lemma isClosedImmersion_ι_of_isCompl {Y : Scheme.{u}} {W V : Y.Opens}
    (hc : IsCompl W V) : IsClosedImmersion V.ι := by
  refine .of_isPreimmersion V.ι ?_
  rw [Scheme.Opens.range_ι, ← (isCompl_coe_of_isCompl hc).compl_eq]
  exact W.isOpen.isClosed_compl

/-- If a complementary pair of opens of the source has the first one with empty fibre over a
point, the fibre of the second one over that point is the whole fibre. -/
private theorem fiberMapOfCompl_isIso {B S : Scheme.{u}} (g : B ⟶ S) (s : S)
    (W V : B.Opens) (hcompl : IsCompl W V)
    (hW : IsEmpty ((W.ι ≫ g).fiber s)) :
    IsIso (fiberMapOfSourceHom V.ι g s) := by
  have hcover : (W : Set B) ∪ (V : Set B) = Set.univ :=
    (isCompl_coe_of_isCompl hcompl).sup_eq_top
  have hsurj : Function.Surjective (fiberMapOfSourceHom V.ι g s).base := by
    intro z
    let b := (g.fiberHomeo s z).1
    have hgb : g b = s := (g.fiberHomeo s z).2
    have hb : b ∈ (W : Set B) ∪ (V : Set B) := by rw [hcover]; simp
    rcases hb with hWb | hVb
    · exact (hW.false (((W.ι ≫ g).fiberHomeo s).symm ⟨⟨b, hWb⟩, hgb⟩)).elim
    · let zV : (V.ι ≫ g).fiber s := ((V.ι ≫ g).fiberHomeo s).symm ⟨⟨b, hVb⟩, hgb⟩
      refine ⟨zV, ?_⟩
      apply (g.fiberHomeo s).injective
      apply Subtype.ext
      change g.fiberι s ((fiberMapOfSourceHom V.ι g s).base zV) = g.fiberι s z
      have hmap := congrArg (fun k : _ ⟶ B => k.base zV)
        (fiberMapOfSourceHom_fiberι V.ι g s)
      calc
        g.fiberι s ((fiberMapOfSourceHom V.ι g s).base zV) =
            V.ι ((V.ι ≫ g).fiberι s zV) := by
              simpa only [Scheme.Hom.comp_apply] using hmap
        _ = b := by
          rw [Scheme.Hom.fiberι_fiberHomeo_symm]
          rfl
        _ = g.fiberι s z := by simp [b, Scheme.Hom.fiberHomeo_apply]
  have : IsOpenImmersion (fiberMapOfSourceHom V.ι g s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (fiberMapOfSourceHom_isPullback V.ι g s).flip inferInstance
  have : Epi (fiberMapOfSourceHom V.ι g s).base :=
    (TopCat.epi_iff_surjective _).2 hsurj
  exact IsOpenImmersion.isIso _

/-- The residue-field fibre degree is inherited by a base change at every point lying over a
point of the original base. -/
private lemma rank_on_basechanged_fiber
    {X S B T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {k : B ⟶ X} {p : B ⟶ T} (sq : IsPullback k p f g) (t : T) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (g t)) r) :
    IsFiniteLocallyFreeOfRank (p.fiberToSpecResidueField t) r := by
  let := h
  exact IsFiniteLocallyFreeOfRank.of_isPullback
    (f := f.fiberToSpecResidueField (g t))
    (f' := p.fiberToSpecResidueField t)
    (g := Spec.map (g.residueFieldMap t))
    (isPullback_fiberToSpecResidueField_of_isPullback sq t)

/-- The residue-field fibre of a base change is the base change of the residue-field fibre, so
it has the same degree. -/
public lemma finiteLocallyFreeOfRank_residueFiber_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S) (t : T) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (a t)) r) :
    IsFiniteLocallyFreeOfRank
      ((pullback.snd f a).fiberToSpecResidueField t) r :=
  rank_on_basechanged_fiber (IsPullback.of_hasPullback f a) t r h

/-- The degree of a fibre is unchanged by base change, provided the fibre over `a t` has some
degree: the other direction is `AlgebraicGeometry.finiteLocallyFreeOfRank_residueFiber_baseChange`
and a fibre has at most one degree. -/
private lemma rank_residueFiber_baseChange_iff_of_exists {X S T : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (t : T) (r : ℕ)
    (hex : ∃ m, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (a t)) m) :
    IsFiniteLocallyFreeOfRank ((pullback.snd f a).fiberToSpecResidueField t) r ↔
      IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (a t)) r := by
  refine ⟨fun h => ?_, finiteLocallyFreeOfRank_residueFiber_baseChange f a t r⟩
  obtain ⟨m, hm⟩ := hex
  have hmr := finiteLocallyFree_rank_unique _ m r
    (finiteLocallyFreeOfRank_residueFiber_baseChange f a t m hm) h
  exact hmr ▸ hm

/-- With a complementary pair of opens whose first member has empty fibre, the degree of the
fibre is carried by the second member alone. -/
private lemma finiteLocallyFreeOfRank_fiber_of_compl
    {B S : Scheme.{u}} (g : B ⟶ S) (s : S) (W V : B.Opens)
    (hcompl : IsCompl W V) (hW : IsEmpty ((W.ι ≫ g).fiber s)) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField s) r) :
    IsFiniteLocallyFreeOfRank
      ((V.ι ≫ g).fiberToSpecResidueField s) r := by
  let : IsIso (fiberMapOfSourceHom V.ι g s) :=
    fiberMapOfCompl_isIso g s W V hcompl hW
  let e : (V.ι ≫ g).fiber s ≅ g.fiber s := asIso (fiberMapOfSourceHom V.ι g s)
  have he : e.hom ≫ g.fiberToSpecResidueField s =
      (V.ι ≫ g).fiberToSpecResidueField s := by
    change fiberMapOfSourceHom V.ι g s ≫ g.fiberToSpecResidueField s =
      (V.ι ≫ g).fiberToSpecResidueField s
    dsimp [fiberMapOfSourceHom, Scheme.Hom.fiber,
      Scheme.Hom.fiberToSpecResidueField]
    exact pullback.lift_snd _ _ _
  simpa only [he] using (rank_comp_iso e (g.fiberToSpecResidueField s) r).mp h

/-- A rank on a restriction to an open of the base determines the residue-field rank at every
point of that open. -/
private lemma finiteLocallyFreeOfRank_residueFiber_of_open_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (s : S) (hs : s ∈ U)
    (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (f ∣_ U) r) :
    IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r := by
  obtain ⟨g, hfac, -⟩ := residueField_lift_to_open U s hs
  let q := pullback.fst U.ι f
  have hq : IsFiniteLocallyFreeOfRank q r :=
    (rank_pullback_symmetry f U.ι r).mpr (rank_pullback_snd_ι_of_restrict f U r h)
  have hfst : IsFiniteLocallyFreeOfRank (pullback.fst g q) r :=
    (rank_pullback_symmetry q g r).mpr (rank_pullback_snd g hq)
  let e := pullbackRightPullbackFstIso U.ι f g
  have he : e.hom ≫ pullback.fst (g ≫ U.ι) f = pullback.fst g q :=
    pullbackRightPullbackFstIso_hom_fst U.ι f g
  have htransport : IsFiniteLocallyFreeOfRank
      (e.hom ≫ pullback.fst (g ≫ U.ι) f) r := by simpa only [he] using hfst
  have hsource : IsFiniteLocallyFreeOfRank
      (pullback.fst (g ≫ U.ι) f) r :=
    (rank_comp_iso e
      (pullback.fst (g ≫ U.ι) f) r).mpr htransport
  let e' : pullback (g ≫ U.ι) f ≅
      pullback (S.fromSpecResidueField s) f := pullback.congrHom hfac rfl
  have he' : e'.hom ≫ pullback.fst (S.fromSpecResidueField s) f =
      pullback.fst (g ≫ U.ι) f := by
    rw [pullback.congrHom_hom]
    change (pullback.lift
      (pullback.fst (g ≫ U.ι) f ≫ 𝟙 _)
      (pullback.snd (g ≫ U.ι) f ≫ 𝟙 _) _) ≫
        pullback.fst (S.fromSpecResidueField s) f = _
    rw [pullback.lift_fst]
    simp
  have hglobal : IsFiniteLocallyFreeOfRank
      (pullback.fst (S.fromSpecResidueField s) f) r := by
    apply (rank_comp_iso e'
      (pullback.fst (S.fromSpecResidueField s) f) r).mpr
    simpa [he'] using hsource
  exact (rank_pullback_symmetry f
    (S.fromSpecResidueField s) r).mp hglobal

/-- A universally bounded fibre has finitely many underlying points. -/
private lemma finite_underlying_points_of_bounded_fiber
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hbounded : HasUniversallyBoundedFibers f) (s : S) :
    Finite (Scheme.Hom.fiber f s) := by
  obtain ⟨n, hn⟩ := hbounded
  obtain ⟨r, -, hrank⟩ := hn s
  let p := f.fiberToSpecResidueField s
  let : IsFiniteLocallyFreeOfRank p r := hrank
  let : IsFiniteLocallyFree p :=
    IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r
  let : IsFinite p :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
      inferInstance |>.1
  let y : Spec (S.residueField s) := default
  have hpoints : (p ⁻¹' {y}).Finite :=
    (locallyQuasiFinite_iff_finite_preimage_singleton (f := p)).mp inferInstance _
  let : Finite (p ⁻¹' {y}) := hpoints.to_subtype
  let e : Scheme.Hom.fiber f s → (p ⁻¹' {y}) := fun x =>
    ⟨x, by change p x = y; exact Subsingleton.elim _ _⟩
  exact Finite.of_injective e (fun x x' h => congrArg Subtype.val h)

/-- A bounded residue-field fiber has finitely many isolated points. -/
private lemma finite_isolated_points_of_bounded_fiber
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hbounded : HasUniversallyBoundedFibers f) (s : S) :
    {x : f.fiber s | IsIsolatedPoint x}.Finite := by
  let := finite_underlying_points_of_bounded_fiber f hbounded s
  exact Set.toFinite _

/-- The étale split-off theorem has empty complementary fiber here, since the
residue fiber is finite. -/
private lemma exists_etale_split_with_empty_fiber_of_bounded
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [IsSeparated f] (hbounded : HasUniversallyBoundedFibers f) (s : S) :
    ∃ (U : EtaleNeighborhood S s), U.IsElementary ∧
      ∃ (W V : (pullback f U.toBase).Opens), IsCompl W V ∧
        IsFinite (V.ι ≫ pullback.snd f U.toBase) ∧
        IsEmpty ((W.ι ≫ pullback.snd f U.toBase).fiber U.point) := by
  obtain ⟨U, hU, W, V, hWV, hVfinite, hW, hEmptyIfFinite⟩ :=
    exists_elementaryEtaleNeighborhood_isCompl f s
      (finite_isolated_points_of_bounded_fiber f hbounded s)
  have hpreimage : (f ⁻¹' {s}).Finite :=
    (f.fiberHomeo s).finite_iff.mp
      (finite_underlying_points_of_bounded_fiber f hbounded s)
  exact ⟨U, hU, W, V, hWV, hVfinite, hEmptyIfFinite hpreimage⟩

/-- The finite summand in the étale splitting is finite locally free. -/
private lemma finite_part_isFiniteLocallyFree
    {X S : Scheme.{u}} (s : S) (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (U : EtaleNeighborhood S s)
    (V : (pullback f U.toBase).Opens)
    (hfinite : IsFinite (V.ι ≫ pullback.snd f U.toBase)) :
    IsFiniteLocallyFree (V.ι ≫ pullback.snd f U.toBase) :=
  (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2
    ⟨hfinite, inferInstance, inferInstance⟩

/-- If one piece of the clopen decomposition by the degree is everything, `f` has that degree. -/
private lemma rank_of_clopen_piece_eq_top {X S : Scheme.{u}} {f : X ⟶ S} {R : ℕ → S.Opens}
    (hrank : ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ R d) d) {r : ℕ} (hR : R r = ⊤) :
    IsFiniteLocallyFreeOfRank f r :=
  IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := IsFiniteLocallyFreeOfRank.property.{u} r) (fun _ : Unit => R r) (by simpa using hR)
    fun _ => hrank r

/-- A finite locally free morphism has a fixed rank on an open around any target point. -/
private lemma exists_open_fixed_rank_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFiniteLocallyFree f] (s : S) :
    ∃ (r : ℕ) (U : S.Opens), s ∈ U ∧ IsFiniteLocallyFreeOfRank (f ∣_ U) r := by
  obtain ⟨R, hdec, hrank⟩ := exists_isClopenDecomposition_isFiniteLocallyFreeOfRank f
  obtain ⟨r, hrs⟩ := hdec.exists_mem s
  exact ⟨r, R r, hrs, hrank r⟩

/-- The degree of a bounded residue-field fibre is uniquely determined. -/
public lemma existsUnique_rank_of_bounded_fiber
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hbounded : HasUniversallyBoundedFibers f) (s : S) :
    ∃! r : ℕ, IsFiniteLocallyFreeOfRank
      (f.fiberToSpecResidueField s) r := by
  obtain ⟨n, hn⟩ := hbounded
  obtain ⟨r, -, hrank⟩ := hn s
  exact ⟨r, hrank, fun t ht => (finiteLocallyFree_rank_unique _ r t hrank ht).symm⟩

/-- A universal bound on the fibre degrees may be taken to be a natural number. -/
private lemma exists_nat_bound_of_universally_bounded {X S : Scheme.{u}}
    (f : X ⟶ S) (hbounded : HasUniversallyBoundedFibers f) :
    ∃ n : ℕ, BoundsFiberDegrees f (n : ℤ) := by
  classical
  obtain ⟨b, hb⟩ := hbounded
  by_cases hS : Nonempty S
  · obtain ⟨r, hr, -⟩ := hb (Classical.choice hS)
    have hbnonneg : 0 ≤ b := by omega
    refine ⟨b.toNat, ?_⟩
    simpa [Int.toNat_of_nonneg hbnonneg] using hb
  · exact ⟨0, fun s => (hS ⟨s⟩).elim⟩

/-- A finite locally free morphism of degree `r` has every residue-field fibre of degree `r`. -/
private lemma rank_on_fiber {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank f r) (s : S) :
    IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r :=
  rank_pullback_snd (S.fromSpecResidueField s) h

/-- The degree of a chosen fibre product transfers to any cartesian square over the same pair of
morphisms. -/
private lemma rank_of_pullback_square {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {i : X' ⟶ X} {p : X' ⟶ S'}
    (sq : IsPullback i p f g) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank (pullback.snd f g) r) :
    IsFiniteLocallyFreeOfRank p r := by
  simpa using (rank_comp_iso sq.isoPullback (pullback.snd f g) r).mp h

/-- A morphism which is both an open and a closed immersion is an isomorphism as soon as the
composite with a finite locally free morphism already attains the fibre-degree bound: each fibre
comparison map is then an isomorphism, so the morphism is surjective. -/
private lemma open_closed_immersion_isIso_of_rank_bound
    {A B S : Scheme.{u}} (i : A ⟶ B) (p : B ⟶ S) [IsOpenImmersion i]
    [IsClosedImmersion i] (n : ℕ)
    (hb : BoundsFiberDegrees p (n : ℤ))
    (ha : IsFiniteLocallyFreeOfRank (i ≫ p) n) : IsIso i := by
  have hi (s : S) : IsIso (fiberMapOfSourceHom i p s) := by
    obtain ⟨m, hm, hr⟩ := hb s
    have hn := rank_on_fiber (i ≫ p) n ha s
    rw [← fiberMapOfSourceHom_fiberToSpecResidueField] at hn
    have hc : IsClosedImmersion (fiberMapOfSourceHom i p s) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (fiberMapOfSourceHom_isPullback i p s).flip inferInstance
    exact (closedImmersion_rank_le_and_isIso _ _ m n hr hn hc).2 (by omega)
  have hsurj : Function.Surjective i := by
    intro b
    let z := (p.fiberHomeo (p b)).symm ⟨b, rfl⟩
    let := hi (p b)
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
      (fiberMapOfSourceHom i p (p b)).base).surjective z
    refine ⟨(i ≫ p).fiberι (p b) a, ?_⟩
    have he := congrArg (fun k : _ ⟶ B => k a)
      (fiberMapOfSourceHom_fiberι i p (p b))
    simpa only [Scheme.Hom.comp_apply, ha, z, Scheme.Hom.fiberι_fiberHomeo_symm] using he.symm
  let : Epi i.base := (TopCat.epi_iff_surjective _).2 hsurj
  exact IsOpenImmersion.isIso i

/-- The degree of the composite of an open immersion with a finite locally free morphism is at
most the degree of the residue-field fibre. -/
private lemma rank_le_of_open_immersion
    {A B S : Scheme.{u}} (i : A ⟶ B) (p : B ⟶ S) [IsOpenImmersion i]
    (n : ℕ) (ha : IsFiniteLocallyFreeOfRank (i ≫ p) n)
    (s : S) (m : ℕ)
    (hm : IsFiniteLocallyFreeOfRank (p.fiberToSpecResidueField s) m) :
    n ≤ m := by
  have hn := rank_on_fiber (i ≫ p) n ha s
  rw [← fiberMapOfSourceHom_fiberToSpecResidueField] at hn
  let j := fiberMapOfSourceHom i p s
  let q := p.fiberToSpecResidueField s
  let : IsOpenImmersion j := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (fiberMapOfSourceHom_isPullback i p s).flip inferInstance
  let : IsFiniteLocallyFreeOfRank q m := hm
  let : IsFiniteLocallyFreeOfRank (j ≫ q) n := hn
  let : IsFinite q :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation q).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree q m) |>.1
  let : IsFinite (j ≫ q) :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation (j ≫ q)).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (j ≫ q) n) |>.1
  exact @finite_open_rank_le_of_field (S.residueField s) inferInstance
    (p.fiber s) ((i ≫ p).fiber s) j q m n inferInstance
    ‹IsFinite q› ‹IsFinite (j ≫ q)› hm hn

/-- The finite summand can be given the rank of the original fibre after shrinking
an étale neighbourhood. -/
private lemma exists_etale_finite_rank_part
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (hb : HasUniversallyBoundedFibers f)
    (s : S) (n : ℕ)
    (hn : IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) n) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (t : T), Etale g ∧ g t = s ∧
      ∃ (B : Scheme.{u}) (p : B ⟶ T) (k : B ⟶ X), IsPullback k p f g ∧
        ∃ (A : Scheme.{u}) (i : A ⟶ B), IsOpenImmersion i ∧ IsClosedImmersion i ∧
          IsFiniteLocallyFreeOfRank (i ≫ p) n := by
  obtain ⟨U, hU, W, V, hc, hf, he⟩ :=
    exists_etale_split_with_empty_fiber_of_bounded f hb s
  let q := pullback.snd f U.toBase
  let : IsFiniteLocallyFree (V.ι ≫ q) :=
    finite_part_isFiniteLocallyFree s f U V hf
  obtain ⟨r, O, ht, hr⟩ := exists_open_fixed_rank_neighborhood (V.ι ≫ q) U.point
  have hn' : IsFiniteLocallyFreeOfRank (q.fiberToSpecResidueField U.point) n :=
    finiteLocallyFreeOfRank_residueFiber_baseChange f U.toBase U.point n (by rwa [U.map_point])
  have hnV := finiteLocallyFreeOfRank_fiber_of_compl q U.point W V hc he n hn'
  have hrV := finiteLocallyFreeOfRank_residueFiber_of_open_restriction
    (V.ι ≫ q) O U.point ht r hr
  have hrn := finiteLocallyFree_rank_unique _ r n hrV hnV
  subst r
  let B := pullback q O.ι
  let p : B ⟶ O := pullback.snd q O.ι
  let b : B ⟶ pullback f U.toBase := pullback.fst q O.ι
  let A := pullback V.ι b
  let i : A ⟶ B := pullback.snd V.ι b
  have sq : IsPullback (b ≫ pullback.fst f U.toBase) p f (O.ι ≫ U.toBase) :=
    (IsPullback.of_hasPullback q O.ι).paste_horiz (IsPullback.of_hasPullback f U.toBase)
  have sqV : IsPullback (pullback.fst V.ι b) (i ≫ p) (V.ι ≫ q) O.ι :=
    (IsPullback.of_hasPullback V.ι b).paste_vert (IsPullback.of_hasPullback q O.ι)
  have : IsClosedImmersion V.ι := isClosedImmersion_ι_of_isCompl hc
  refine ⟨O, O.ι ≫ U.toBase, ⟨U.point, ht⟩, inferInstance, ?_,
    B, p, b ≫ pullback.fst f U.toBase, sq, A, i, inferInstance, inferInstance, ?_⟩
  · change U.toBase U.point = s
    exact U.map_point
  · exact rank_of_pullback_square sqV n (rank_pullback_snd_ι_of_restrict _ O n hr)

/-- The degree carried by one side of a cartesian square transfers to the chosen fibre
product. -/
private lemma rank_to_pullback_square {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {i : X' ⟶ X} {p : X' ⟶ S'}
    (sq : IsPullback i p f g) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank p r) :
    IsFiniteLocallyFreeOfRank (pullback.snd f g) r := by
  simpa using (rank_comp_iso sq.isoPullback.symm p r).mp h

/-- Constant finite fibre degree makes the finite summand over an étale neighbourhood
exhaust the whole source, so fixed-rank descent applies. -/
public lemma rank_of_constant_fiber_rank
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (r : ℕ)
    (hr : ∀ s, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r) :
    IsFiniteLocallyFreeOfRank f r := by
  classical
  have hb : BoundsFiberDegrees f (r : ℤ) := fun s => ⟨r, le_rfl, hr s⟩
  have hlocal (s : S) : ∃ (T : Scheme.{u}) (g : T ⟶ S) (t : T),
      Etale g ∧ g t = s ∧ IsFiniteLocallyFreeOfRank (pullback.snd f g) r := by
    obtain ⟨T, g, t, he, ht, B, p, k, sq, A, i, ho, hc, hi⟩ :=
      exists_etale_finite_rank_part f ⟨r, hb⟩ s r (hr s)
    let := ho
    let := hc
    have hb' : BoundsFiberDegrees p (r : ℤ) :=
      (boundsFiberDegrees_isStableUnderBaseChange (r : ℤ)).of_isPullback sq hb
    let : IsIso i := open_closed_immersion_isIso_of_rank_bound i p r hb' hi
    have hp : IsFiniteLocallyFreeOfRank p r :=
      (rank_comp_iso (asIso i) p r).mpr hi
    exact ⟨T, g, t, he, ht, rank_to_pullback_square sq r hp⟩
  choose T g t he ht hlocal using hlocal
  have hcover : Presieve.ofArrows T g ∈ Scheme.etalePrecoverage S :=
    (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun s => ⟨s, t s, ht s⟩, he⟩
  have hfpqc : MorphismProperty.IsLocalAtTarget
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
    isFiniteLocallyFree_isLocalAtTarget_fpqc_of_isAffineHom
      Stacks.Descent.isAffineHom_isLocalAtTarget_fpqc
  have : IsFiniteLocallyFree f := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := @IsFiniteLocallyFree)
      (Scheme.etalePrecoverage_le_fpqcPrecoverage _ hcover)
    intro T' g' _ hg'
    cases hg' with
    | mk s =>
      have := hlocal s
      exact IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (pullback.snd f (g s)) r
  obtain ⟨R, hdec, hrank⟩ := exists_isClopenDecomposition_isFiniteLocallyFreeOfRank f
  have hRr : R r = ⊤ := by
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨d, hd⟩ := hdec.exists_mem s
    have hfib := finiteLocallyFreeOfRank_residueFiber_of_open_restriction f (R d) s hd d (hrank d)
    exact finiteLocallyFree_rank_unique _ d r hfib (hr s) ▸ hd
  exact rank_of_clopen_piece_eq_top hrank hRr

/-- The degree function is lower semicontinuous. -/
public lemma isClosed_fiber_rank_lt
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (hb : HasUniversallyBoundedFibers f) (d : ℕ) :
    IsClosed {s : S | ∃ r < d,
      IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  obtain ⟨r, hr, -⟩ := existsUnique_rank_of_bounded_fiber f hb s
  have hdr : d ≤ r := by
    by_contra h
    exact hs ⟨r, by omega, hr⟩
  obtain ⟨T, g, t, he, ht, B, p, k, sq, A, i, ho, hc, hi⟩ :=
    exists_etale_finite_rank_part f hb s r hr
  let := he
  let := ho
  refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, ⟨t, ht⟩⟩
  rintro y ⟨t', rfl⟩ ⟨m, hmd, hm⟩
  have hm' := rank_on_basechanged_fiber sq t' m hm
  have hrm := rank_le_of_open_immersion i p r hi t' m hm'
  omega

/-- The locus in the base over which the fibre of `f` is finite locally free of degree `r`. -/
private def fiberDegreeLocus {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Set S :=
  {s | IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r}

/-- The locus in the base over which the fibre of `f` is finite locally free of degree less
than `r`. -/
private def fiberDegreeFiltration {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Set S :=
  {s | ∃ q < r, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) q}

private lemma fiberDegreeFiltration_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    fiberDegreeFiltration f 0 = ∅ := by
  ext s
  simp [fiberDegreeFiltration]

private lemma fiberDegreeFiltration_mono {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) :
    fiberDegreeFiltration f r ⊆ fiberDegreeFiltration f (r + 1) := by
  rintro s ⟨q, hq, h⟩
  exact ⟨q, by omega, h⟩

/-- The `r`-th stratum of the filtration by the fibre degree is the locus of degree `r`. -/
private lemma fiberDegreeFiltration_succ_sdiff {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) :
    fiberDegreeFiltration f (r + 1) \ fiberDegreeFiltration f r = fiberDegreeLocus f r := by
  ext s
  constructor
  · rintro ⟨⟨q, hq, h⟩, hnot⟩
    have hqr : q = r := by
      by_contra hne
      exact hnot ⟨q, by omega, h⟩
    exact hqr ▸ h
  · intro h
    refine ⟨⟨r, by omega, h⟩, ?_⟩
    rintro ⟨q, hq, hq'⟩
    have := finiteLocallyFree_rank_unique _ q r hq' h
    omega

/-- A base change of `f` is finite locally free of degree `r` exactly when the image of the base
lies in the locus of fibre degree `r`, once every fibre has some degree. -/
private lemma rank_pullback_iff_range_fiber_rank_of_exists
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (hex : ∀ s, ∃ m, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) m)
    (r : ℕ) (T : Scheme.{u}) (g : T ⟶ S) :
    IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
      Set.range g.base ⊆ fiberDegreeLocus f r := by
  constructor
  · rintro h s ⟨t, rfl⟩
    exact (rank_residueFiber_baseChange_iff_of_exists f g t r (hex _)).mp
      (rank_on_fiber (pullback.snd f g) r h t)
  · exact fun h => rank_of_constant_fiber_rank _ r fun t =>
      finiteLocallyFreeOfRank_residueFiber_baseChange f g t r (h ⟨t, rfl⟩)

/-- **Stacks Project, Tag 07RY.** A separated, flat, locally finitely presented, locally
quasi-finite morphism with universally bounded fibres admits a finite closed filtration whose
strata universally characterize finite locally free base changes of each degree. -/
@[stacks 07RY]
public theorem exists_closed_filtration_characterizing_finiteLocallyFree_rank
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] [LocallyQuasiFinite f] (hbounded : HasUniversallyBoundedFibers f) :
    ∃ (n : ℕ) (Z : Fin (n + 2) → Set S),
      (∀ i, IsClosed (Z i)) ∧
        Z 0 = ∅ ∧
        Z (Fin.last (n + 1)) = Set.univ ∧
        (∀ i : Fin (n + 1), Z i.castSucc ⊆ Z i.succ) ∧
        ∀ (r : Fin (n + 1)) (T : Scheme.{u}) (g : T ⟶ S),
          IsFiniteLocallyFreeOfRank (pullback.snd f g) r.val ↔
            Set.range g.base ⊆ Z r.succ \ Z r.castSucc := by
  obtain ⟨n, hn⟩ := exists_nat_bound_of_universally_bounded f hbounded
  let Z : Fin (n + 2) → Set S := fun i => fiberDegreeFiltration f i.val
  refine ⟨n, Z, fun i => isClosed_fiber_rank_lt f hbounded i.val, ?_, ?_, ?_, ?_⟩
  · exact fiberDegreeFiltration_zero f
  · apply Set.eq_univ_of_forall
    intro s
    obtain ⟨r, hr, h⟩ := hn s
    exact ⟨r, by change r < n + 1; omega, h⟩
  · exact fun i => fiberDegreeFiltration_mono f i.val
  · intro r T g
    rw [show Z r.succ \ Z r.castSucc = fiberDegreeLocus f r.val from
      fiberDegreeFiltration_succ_sdiff f r.val]
    exact rank_pullback_iff_range_fiber_rank_of_exists f
      (fun s => (existsUnique_rank_of_bounded_fiber f hbounded s).exists) r.val T g

/-! ### Dropping the bound on the fibre degrees -/

/-- A property stable under base change passes to the second projection of a fibre product. -/
private lemma prop_pullback_snd {X S T : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (f : X ⟶ S) (g : T ⟶ S) (h : P f) :
    P (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) h

/-- Every fibre of a flat, locally finitely presented, locally quasi-finite and quasi-compact
morphism is finite locally free of some degree: it is finite over a field, hence finite locally
free, and the spectrum of a field is connected. -/
private lemma exists_rank_residueFiber {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [LocallyQuasiFinite f] [QuasiCompact f] (s : S) :
    ∃ r : ℕ, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r := by
  have hfin : IsFinite (f.fiberToSpecResidueField s) :=
    (locallyQuasiFinite_iff_isFinite_fiber (f := f)).mp inferInstance s
  have hflat : Flat (f.fiberToSpecResidueField s) :=
    prop_pullback_snd @Flat f (S.fromSpecResidueField s) inferInstance
  have hfp : LocallyOfFinitePresentation (f.fiberToSpecResidueField s) :=
    prop_pullback_snd @LocallyOfFinitePresentation f (S.fromSpecResidueField s) inferInstance
  have hflf : IsFiniteLocallyFree (f.fiberToSpecResidueField s) :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2 ⟨hfin, hflat, hfp⟩
  let := hflf
  obtain ⟨R, hdec, hrank⟩ :=
    exists_isClopenDecomposition_isFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s)
  obtain ⟨d, hd⟩ := hdec.exists_mem default
  have hRd : R d = ⊤ := eq_top_iff.mpr fun y _ => (Subsingleton.elim y default) ▸ hd
  exact ⟨d, rank_of_clopen_piece_eq_top hrank hRd⟩

/-- The degree of a fibre is unchanged by base change: one direction is
`AlgebraicGeometry.finiteLocallyFreeOfRank_residueFiber_baseChange`, and the other follows from
it because a fibre has exactly one degree. -/
private lemma rank_residueFiber_baseChange_iff {X S T : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [LocallyQuasiFinite f] [QuasiCompact f]
    (a : T ⟶ S) (t : T) (r : ℕ) :
    IsFiniteLocallyFreeOfRank ((pullback.snd f a).fiberToSpecResidueField t) r ↔
      IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (a t)) r :=
  rank_residueFiber_baseChange_iff_of_exists f a t r (exists_rank_residueFiber f _)

/-- The fibre degree of a base change to an affine open of the base is bounded, by
[Stacks Project, Tag 03JA]. -/
private lemma hasUniversallyBoundedFibers_pullback_affineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [LocallyQuasiFinite f] [QuasiCompact f]
    (W : S.Opens) (hW : IsAffineOpen W) : HasUniversallyBoundedFibers (pullback.snd f W.ι) := by
  let : IsAffine W := hW
  let : CompactSpace W := inferInstance
  let := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f W.ι)
  let : LocallyOfFinitePresentation (pullback.snd f W.ι) :=
    prop_pullback_snd @LocallyOfFinitePresentation f W.ι inferInstance
  let : LocallyQuasiFinite (pullback.snd f W.ι) :=
    prop_pullback_snd @LocallyQuasiFinite f W.ι inferInstance
  exact hasUniversallyBoundedFibers_of_locallyQuasiFinite (pullback.snd f W.ι)

/-- Lower semicontinuity of the fibre degree with no bound on the degrees: the locus of degree
less than `d` is closed because it is so on every affine open of the base. -/
private lemma isClosed_fiberDegreeFiltration {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] [QuasiCompact f]
    (d : ℕ) : IsClosed (fiberDegreeFiltration f d) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨W, hW, hsW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := s) (U := (⊤ : S.Opens)) trivial
  refine ⟨(W : Set S) ∩ (fiberDegreeFiltration f d)ᶜ, Set.inter_subset_right, ?_, hsW, hs⟩
  have hset : W.ι.base ⁻¹' fiberDegreeFiltration f d =
      {t : W | ∃ q < d, IsFiniteLocallyFreeOfRank
        ((pullback.snd f W.ι).fiberToSpecResidueField t) q} := by
    ext t
    simp only [Set.mem_preimage, fiberDegreeFiltration, Set.mem_ofPred_eq]
    exact exists_congr fun q => and_congr_right fun _ =>
      (rank_residueFiber_baseChange_iff f W.ι t q).symm
  have hclW : IsClosed (W.ι.base ⁻¹' fiberDegreeFiltration f d) := by
    rw [hset]
    exact isClosed_fiber_rank_lt (pullback.snd f W.ι)
      (hasUniversallyBoundedFibers_pullback_affineOpen f W hW) d
  have himg := W.ι.isOpenMap _ hclW.isOpen_compl
  rwa [← Set.preimage_compl, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι, Set.inter_comm] at himg

/-- **The universal property of the strata.** A base change of `f` is finite locally free of
degree `r` exactly when the image of the base lies in the locus of fibre degree `r`. -/
private lemma rank_pullback_iff_range_subset_fiberDegreeLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    [QuasiCompact f] (r : ℕ) (T : Scheme.{u}) (g : T ⟶ S) :
    IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
      Set.range g.base ⊆ fiberDegreeLocus f r :=
  rank_pullback_iff_range_fiber_rank_of_exists f (exists_rank_residueFiber f) r T g

/-! ### Quasi-compactness of the strata -/

section Strata

universe w v

/-- The base change of `f` computed in the over category agrees with the fibre product. -/
private lemma prop_overPullback_left_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    P ((Over.pullback g).map (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 S))).left ↔
      P (pullback.fst g f) := by
  let e : pullback (𝟙 S) g ≅ T := asIso (pullback.snd (𝟙 S) g)
  have hcomm : ((Over.pullback g).map
      (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 S))).left ≫ e.hom = pullback.snd f g := by
    change pullback.lift (pullback.fst f g ≫ f) (pullback.snd f g) _ ≫
      pullback.snd (𝟙 S) g = pullback.snd f g
    exact pullback.lift_snd _ _ _
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (Iso.refl (pullback f g)) e hcomm.symm)).trans
    (prop_pullback_symm_iff P f g).symm

/-- Base change in the over category along a composite is base change twice. -/
private lemma prop_overPullback_comp_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T U : Scheme.{u}} (a : T ⟶ S) (b : U ⟶ T) {X Y : Over S} (h : X ⟶ Y) :
    P ((Over.pullback (b ≫ a)).map h).left ↔
      P ((Over.pullback b).map ((Over.pullback a).map h)).left := by
  let e := Over.pullbackComp b a
  let α := (Over.forget U).mapIso (e.app X)
  let β := (Over.forget U).mapIso (e.app Y)
  have hn : ((Over.pullback (b ≫ a)).map h).left ≫ β.hom =
      α.hom ≫ ((Over.pullback b).map ((Over.pullback a).map h)).left :=
    congrArg Over.Hom.left (e.hom.naturality h)
  exact P.arrow_mk_iso_iff (Arrow.isoMk α β hn.symm)

/-- [Stacks Project, Tag 06AC] in the projection convention of this file: a base change of `f`
to the limit of a cofiltered system which is finite locally free is already so at a stage. -/
private lemma exists_isFiniteLocallyFree_later_stage
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : Functor I Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i₀ : I) [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (a : D.obj i₀ ⟶ S) (j : c.pt ⟶ S) (hj : c.π.app i₀ ≫ a = j)
    (hflf : IsFiniteLocallyFree (pullback.fst j f)) :
    ∃ (i : I) (h : i ⟶ i₀), IsFiniteLocallyFree (pullback.fst (D.map h ≫ a) f) := by
  let φ : Over.mk f ⟶ Over.mk (𝟙 S) := Over.homMk f
  let X₀ := (Over.pullback a).obj (Over.mk f)
  let Y₀ := (Over.pullback a).obj (Over.mk (𝟙 S))
  let f₀ : X₀ ⟶ Y₀ := (Over.pullback a).map φ
  have : QuasiCompact X₀.hom := by change QuasiCompact (pullback.snd f a); infer_instance
  have : QuasiSeparated X₀.hom := by
    change QuasiSeparated (pullback.snd f a)
    exact prop_pullback_snd @QuasiSeparated f a inferInstance
  have : QuasiCompact Y₀.hom := by change QuasiCompact (pullback.snd (𝟙 S) a); infer_instance
  have : QuasiSeparated Y₀.hom := by
    change QuasiSeparated (pullback.snd (𝟙 S) a)
    exact prop_pullback_snd @QuasiSeparated (𝟙 S) a inferInstance
  let := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  let := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  let := QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  let := quasiSeparatedSpace_of_quasiSeparated Y₀.hom
  have : LocallyOfFinitePresentation φ.left := by
    change LocallyOfFinitePresentation f
    infer_instance
  have : LocallyOfFinitePresentation f₀.left :=
    MorphismProperty.overPullbackMap a φ inferInstance
  have h₀ : IsFiniteLocallyFree ((Over.pullback (c.π.app i₀)).map f₀).left := by
    apply (prop_overPullback_comp_iff (@IsFiniteLocallyFree) a (c.π.app i₀) φ).mp
    apply (prop_overPullback_left_iff (@IsFiniteLocallyFree) f (c.π.app i₀ ≫ a)).mpr
    rw [hj]
    exact hflf
  let := h₀
  obtain ⟨i, h, hi⟩ :=
    exists_isFiniteLocallyFree_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀
  exact ⟨i, h, (prop_overPullback_left_iff (@IsFiniteLocallyFree) f (D.map h ≫ a)).mp
    ((prop_overPullback_comp_iff (@IsFiniteLocallyFree) a (D.map h) φ).mpr hi)⟩

/-- A closed subscheme over which a base change of `f` is finite locally free is contained in a
closed subscheme of finite presentation with the same property: the closed subscheme is the limit
of the closed subschemes of finite presentation containing it, and finite local freeness descends
to a stage of that limit. -/
private lemma exists_finitePresentation_closed_stage {X S C : Scheme.{u}} (f : X ⟶ S)
    (j : C ⟶ S) [IsClosedImmersion j] [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hflf : IsFiniteLocallyFree (pullback.fst j f)) :
    ∃ (T : Scheme.{u}) (i : T ⟶ S), IsClosedImmersion i ∧ FinitePresentation i ∧
      IsFiniteLocallyFree (pullback.fst i f) ∧ Set.range j.base ⊆ Set.range i.base := by
  obtain ⟨I, hpre, hnon, hdir, D, t, p, hc, hcompat, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation j
  let := hpre
  let := hnon
  let := hdir
  let : IsCofiltered Iᵒᵖ := inferInstance
  let : ∀ {i k : Iᵒᵖ} (h : i ⟶ k), IsAffineHom (D.map h) := by
    intro i k h
    have hm : D.map h ≫ t.app k = t.app i := by simp
    have hcomp : IsAffineHom (D.map h ≫ t.app k) := by
      rw [hm]
      let : IsClosedImmersion (t.app i) := (hstage i).1
      infer_instance
    let := hcomp
    let : IsSeparated (t.app k) := by
      let : IsClosedImmersion (t.app k) := (hstage k).1
      infer_instance
    exact IsAffineHom.of_comp (D.map h) (t.app k)
  let i₀ : Iᵒᵖ := .op (Classical.choice hnon)
  let : CompactSpace (((Functor.const Iᵒᵖ).obj S).obj i₀) := ‹CompactSpace S›
  let : QuasiSeparatedSpace (((Functor.const Iᵒᵖ).obj S).obj i₀) := ‹QuasiSeparatedSpace S›
  let : CompactSpace (D.obj i₀) := by
    let : IsClosedImmersion (t.app i₀) := (hstage i₀).1
    exact QuasiCompact.compactSpace_of_compactSpace (t.app i₀)
  let : QuasiSeparatedSpace (D.obj i₀) := by
    let : IsClosedImmersion (t.app i₀) := (hstage i₀).1
    exact quasiSeparatedSpace_of_quasiSeparated (t.app i₀)
  have hji (i : Iᵒᵖ) : p.app i ≫ t.app i = j := by
    have q := congrArg (fun η => η.app i) hcompat
    simpa using q
  obtain ⟨i, h, hi⟩ :=
    exists_isFiniteLocallyFree_later_stage D (Cone.mk C p) hc i₀ f (t.app i₀) j (hji i₀) hflf
  have hm : D.map h ≫ t.app i₀ = t.app i := by simp
  rw [hm] at hi
  refine ⟨D.obj i, t.app i, (hstage i).1, (hstage i).2, hi, ?_⟩
  rintro s ⟨x, rfl⟩
  exact ⟨p.app i x, by simp only [← Scheme.Hom.comp_apply, hji i]⟩

/-- The complement of the image of a morphism of finite presentation into a quasi-compact and
quasi-separated scheme is retrocompact, by Chevalley's theorem. -/
private lemma isRetrocompact_compl_range_of_finitePresentation {T S : Scheme.{u}} (j : T ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation j] [QuasiCompact j] :
    IsRetrocompact (Set.range j.base)ᶜ := by
  have hc : Topology.IsConstructible (Set.range j.base) := by
    simpa only [Set.image_univ] using
      j.isConstructible_image (s := Set.univ) Topology.IsConstructible.univ
  exact IsRetrocompact_of_IsConstructible hc.compl

/-- An open set that is also closed is complementary to the open set formed by its
complement. -/
private lemma isCompl_compl_opens_of_isClopen {T : Scheme.{u}} (V : T.Opens)
    (hV : IsClopen (V : Set T)) :
    IsCompl (⟨(V : Set T)ᶜ, hV.1.isOpen_compl⟩ : T.Opens) V := by
  constructor
  · rw [disjoint_iff]
    ext x
    simp
  · rw [codisjoint_iff]
    ext x
    simp

/-- Above the preceding stratum, the locus of fibre degree `r` on a quasi-compact and
quasi-separated open of the base is the image of a closed immersion of finite presentation, so
its complement is retrocompact. -/
private lemma isRetrocompact_compl_preimage_fiberDegreeLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f]
    [QuasiCompact f] (U : S.Opens) [CompactSpace U] [QuasiSeparatedSpace U] (r : ℕ)
    (hclosed : IsClosed (U.ι.base ⁻¹' fiberDegreeLocus f r)) :
    IsRetrocompact (U.ι.base ⁻¹' fiberDegreeLocus f r)ᶜ := by
  classical
  let q := pullback.snd f U.ι
  let : Flat q := inferInstanceAs (Flat (pullback.snd f U.ι))
  let : LocallyOfFinitePresentation q :=
    prop_pullback_snd @LocallyOfFinitePresentation f U.ι inferInstance
  let : IsSeparated q := prop_pullback_snd @IsSeparated f U.ι inferInstance
  let : LocallyQuasiFinite q := prop_pullback_snd @LocallyQuasiFinite f U.ι inferInstance
  let : QuasiCompact q := inferInstanceAs (QuasiCompact (pullback.snd f U.ι))
  let : QuasiSeparated q := prop_pullback_snd @QuasiSeparated f U.ι inferInstance
  have hlocus : fiberDegreeLocus q r = U.ι.base ⁻¹' fiberDegreeLocus f r :=
    Set.ext fun t => rank_residueFiber_baseChange_iff f U.ι t r
  -- the reduced closed subscheme carried by the locus of degree `r`
  let K : Scheme.IdealSheafData U := Scheme.IdealSheafData.vanishingIdeal ⟨_, hclosed⟩
  let jc : K.subscheme ⟶ U := K.subschemeι
  have hjrange : Set.range jc.base = U.ι.base ⁻¹' fiberDegreeLocus f r := by
    simp [jc, K, Scheme.IdealSheafData.range_subschemeι K]
  have : IsFiniteLocallyFreeOfRank (pullback.snd q jc) r :=
    (rank_pullback_iff_range_subset_fiberDegreeLocus q r _ jc).mpr (by rw [hjrange, hlocus])
  have hjflf : IsFiniteLocallyFree (pullback.fst jc q) :=
    (prop_pullback_symm_iff (@IsFiniteLocallyFree) q jc).mpr
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (pullback.snd q jc) r)
  obtain ⟨T, i, hicl, hifp, hiflf, hsub⟩ := exists_finitePresentation_closed_stage q jc hjflf
  let := hicl
  have : IsFiniteLocallyFree (pullback.snd q i) :=
    (prop_pullback_symm_iff (@IsFiniteLocallyFree) q i).mp hiflf
  obtain ⟨V, hdec, hVrank⟩ :=
    exists_isClopenDecomposition_isFiniteLocallyFreeOfRank (pullback.snd q i)
  have hfib (d : ℕ) (x : T) (hx : x ∈ V d) :
      IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField (U.ι (i x))) d :=
    (rank_residueFiber_baseChange_iff f U.ι (i x) d).mp
      ((rank_residueFiber_baseChange_iff q i x d).mp
        (finiteLocallyFreeOfRank_residueFiber_of_open_restriction (pullback.snd q i) (V d) x hx d
          (hVrank d)))
  have hrange : Set.range ((V r).ι ≫ i).base = U.ι.base ⁻¹' fiberDegreeLocus f r := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hfib r x hx
    · intro y hy
      obtain ⟨x, rfl⟩ := hsub (by rwa [hjrange])
      obtain ⟨d, hd⟩ := hdec.exists_mem x
      have hdr : d = r := finiteLocallyFree_rank_unique _ d r (hfib d x hd) hy
      exact ⟨x, hdr ▸ hd, rfl⟩
  rw [← hrange]
  have : IsClosedImmersion (V r).ι :=
    isClosedImmersion_ι_of_isCompl (isCompl_compl_opens_of_isClopen (V r) (hdec.isClopen r))
  have : LocallyOfFinitePresentation i := hifp.1
  exact isRetrocompact_compl_range_of_finitePresentation ((V r).ι ≫ i)

/-- Retrocompactness can be checked on the affine opens inside a retrocompact ambient open
set. -/
private lemma isRetrocompact_of_local_affine {S : Scheme.{u}} {E V : Set S} (hEV : E ⊆ V)
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V)
    (hlocal : ∀ W : S.Opens, IsAffineOpen W → (W : Set S) ⊆ V →
      IsCompact (W.ι.base ⁻¹' E)) : IsRetrocompact E := by
  intro K hKcompact hKopen
  let A : S.Opens := ⟨V ∩ K, hVopen.inter hKopen⟩
  let ι := {W : S.Opens // IsAffineOpen W ∧ (W : Set S) ⊆ A}
  let O : ι → Set S := fun W => W.1
  have hcover : V ∩ K ⊆ ⋃ W : ι, O W := by
    intro s hs
    obtain ⟨W, hWa, hsW, hWA⟩ := exists_isAffineOpen_mem_and_subset (U := A) hs
    exact Set.mem_iUnion.mpr ⟨⟨W, hWa, hWA⟩, hsW⟩
  have hopen (W : ι) : IsOpen (O W) := W.1.2
  obtain ⟨F, hF⟩ := (hVretro hKcompact hKopen).elim_finite_subcover O hopen hcover
  have hcompact (W : ι) : IsCompact (O W ∩ E) := by
    have hW := hlocal W.1 W.2.1 (W.2.2.trans Set.inter_subset_left)
    have himage := hW.image W.1.ι.continuous
    simpa [O, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
      using himage
  have heq : E ∩ K = ⋃ W ∈ F, O W ∩ E := by
    ext s
    constructor
    · rintro ⟨hsE, hsK⟩
      obtain ⟨W, hWF, hsW⟩ := Set.mem_iUnion₂.mp (hF ⟨hEV hsE, hsK⟩)
      exact Set.mem_iUnion₂.mpr ⟨W, hWF, hsW, hsE⟩
    · intro hs
      obtain ⟨W, -, hsW, hsE⟩ := Set.mem_iUnion₂.mp hs
      exact ⟨hsE, (W.2.2 hsW).2⟩
  rw [heq]
  exact F.isCompact_biUnion fun W _ => hcompact W

/-- The complement of the locus of fibre degree less than `r` is retrocompact. -/
private lemma isRetrocompact_compl_fiberDegreeFiltration {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] [QuasiCompact f]
    (r : ℕ) : IsRetrocompact (fiberDegreeFiltration f r)ᶜ := by
  induction r with
  | zero =>
    rw [fiberDegreeFiltration_zero, Set.compl_empty]
    exact IsRetrocompact.univ
  | succ r ih =>
    refine isRetrocompact_of_local_affine
      (Set.compl_subset_compl.mpr (fiberDegreeFiltration_mono f r))
      (isClosed_fiberDegreeFiltration f r).isOpen_compl ih fun W hW hWV => ?_
    let : IsAffine W := hW
    let : CompactSpace W := inferInstance
    let : QuasiSeparatedSpace W := inferInstance
    have hpre : W.ι.base ⁻¹' fiberDegreeFiltration f (r + 1) =
        W.ι.base ⁻¹' fiberDegreeLocus f r := by
      ext x
      have hx : (W.ι.base x) ∈ (fiberDegreeFiltration f r)ᶜ :=
        hWV (by rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self x)
      refine ⟨fun hmem => ?_, fun hmem => ⟨r, by omega, hmem⟩⟩
      obtain ⟨d, hd, h⟩ := hmem
      have hdr : d = r := by
        by_contra hne
        exact hx ⟨d, by omega, h⟩
      exact hdr ▸ h
    have hclosed : IsClosed (W.ι.base ⁻¹' fiberDegreeLocus f r) := by
      rw [← hpre]
      exact (isClosed_fiberDegreeFiltration f (r + 1)).preimage W.ι.continuous
    rw [Set.preimage_compl, hpre]
    exact (isRetrocompact_compl_preimage_fiberDegreeLocus f W r hclosed).isCompact

/-- Each stratum of the filtration by the fibre degree is retrocompact. -/
private lemma isRetrocompact_fiberDegreeLocus {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] [QuasiCompact f]
    (r : ℕ) : IsRetrocompact (fiberDegreeLocus f r) := by
  rw [← fiberDegreeFiltration_succ_sdiff f r]
  intro K hK hKopen
  have h := (isRetrocompact_compl_fiberDegreeFiltration f r) hK hKopen
  have hc := h.inter_left (isClosed_fiberDegreeFiltration f (r + 1))
  convert hc using 1
  ext s
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
  tauto

/-- The difference of two closed subsets carries a locally closed subscheme structure with that
difference as its underlying set. -/
private lemma exists_immersion_range_eq_sdiff {S : Scheme.{u}} (C D : Set S) (hC : IsClosed C)
    (hD : IsClosed D) :
    ∃ (T : Scheme.{u}) (i : T ⟶ S), IsImmersion i ∧ Set.range i.base = C \ D := by
  let K := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : TopologicalSpace.Closeds S)
  let A : K.subscheme.Opens := K.subschemeι ⁻¹ᵁ (⟨Dᶜ, hD.isOpen_compl⟩ : S.Opens)
  refine ⟨A, A.ι ≫ K.subschemeι, inferInstance, ?_⟩
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  change K.subschemeι.base '' (K.subschemeι.base ⁻¹' Dᶜ) = C \ D
  rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι]
  simp [K, Set.sdiff_eq, Set.inter_comm]

/-- An immersion with retrocompact image is quasi-compact. -/
private lemma quasiCompact_of_isImmersion_of_isRetrocompact_range {T S : Scheme.{u}} (i : T ⟶ S)
    [IsImmersion i] (hi : IsRetrocompact (Set.range i.base)) : QuasiCompact i := by
  refine quasiCompact_iff_isSpectralMap.mpr ⟨i.continuous, fun K hKopen hKcompact => ?_⟩
  rw [i.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range, Set.inter_comm]
  exact hi hKcompact hKopen

/-- **Stacks Project, Tag 07RZ.** A flat, locally finitely presented, separated and quasi-finite
morphism admits an increasing sequence of closed subsets of its target whose successive
differences are quasi-compactly immersed and are characterised by the degree of the finite
locally free base changes of the morphism. -/
@[stacks 07RZ]
public theorem exists_quasiCompact_stratification_of_finiteLocallyFree_rank
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    [LocallyQuasiFinite f] [QuasiCompact f] :
    ∃ (Z : ℕ → Set S) (Y : ℕ → Scheme.{u}) (i : (r : ℕ) → Y r ⟶ S),
      (∀ r, IsClosed (Z r)) ∧
        Z 0 = ∅ ∧
        (∀ r, Z r ⊆ Z (r + 1)) ∧
        (⋃ r, Z r) = Set.univ ∧
        (∀ r, IsImmersion (i r)) ∧
        (∀ r, QuasiCompact (i r)) ∧
        (∀ r, Set.range (i r).base = Z (r + 1) \ Z r) ∧
        ∀ (r : ℕ) (T : Scheme.{u}) (g : T ⟶ S),
          IsFiniteLocallyFreeOfRank (pullback.snd f g) r ↔
            Set.range g.base ⊆ Z (r + 1) \ Z r := by
  classical
  have hstr (r : ℕ) : ∃ (Y : Scheme.{u}) (i : Y ⟶ S), IsImmersion i ∧
      Set.range i.base = fiberDegreeFiltration f (r + 1) \ fiberDegreeFiltration f r :=
    exists_immersion_range_eq_sdiff _ _ (isClosed_fiberDegreeFiltration f (r + 1))
      (isClosed_fiberDegreeFiltration f r)
  choose Y i himm hrange using hstr
  refine ⟨fiberDegreeFiltration f, Y, i, isClosed_fiberDegreeFiltration f,
    fiberDegreeFiltration_zero f, fiberDegreeFiltration_mono f, ?_, himm, ?_, hrange, ?_⟩
  · refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨d, hd⟩ := exists_rank_residueFiber f s
    exact Set.mem_iUnion.mpr ⟨d + 1, d, by omega, hd⟩
  · intro r
    let := himm r
    refine quasiCompact_of_isImmersion_of_isRetrocompact_range (i r) ?_
    rw [hrange r, fiberDegreeFiltration_succ_sdiff]
    exact isRetrocompact_fiberDegreeLocus f r
  · intro r T g
    rw [fiberDegreeFiltration_succ_sdiff]
    exact rank_pullback_iff_range_subset_fiberDegreeLocus f r T g

end Strata

end AlgebraicGeometry

end
