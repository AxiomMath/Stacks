module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Surgery on constructible stratifications

`AlgebraicGeometry.ConstructibleStratification B X U` partitions one open subscheme `U` of `X`.
Comparing the partitions produced on *different* open subschemes — which is what the Zariski-local
criterion of Stacks 095E does — needs three operations on that datum which neither building it from
a partition (`AlgebraicGeometry.ConstructibleStratification.ofPartition`) nor refining two of the
same open against each other (`AlgebraicGeometry.ConstructibleStratification.inf`) provides.

The first enlarges the open: a stratification of a quasi-compact open `V` of a quasi-compact
quasi-separated scheme becomes a stratification of the whole scheme on adjoining the closed
complement of `V` as one further stratum. This is where Stacks 09YD enters, in the form Mathlib
gives it (`Topology.IsConstructible.image_of_isOpenEmbedding`): a stratum constructible inside `V`
has to be constructible in the ambient scheme before it can be a stratum of a stratification of the
whole.

The second discards the empty strata, producing a refinement all of whose strata have a point. A
condition on strata need not hold on an empty one, so a construction which compares finitely many
stratifications and locates each resulting stratum inside one of them by choosing a point in it has
to arrange for the points to exist.

The third moves a stratification forward along an open immersion, keeping the strata and composing
their structure morphisms, so that a partition manufactured on a member of an open cover becomes a
partition of its image.

## Main results

* `AlgebraicGeometry.isConstructible_opens_ι_preimage_iff`: for a subset of a quasi-compact open
  subscheme of a quasi-separated scheme, constructibility inside that open and in the ambient
  scheme agree.
* `AlgebraicGeometry.ConstructibleStratification.addComplement`: a stratification of a
  quasi-compact open, extended by the complement to a stratification of the whole scheme.
* `AlgebraicGeometry.ConstructibleStratification.exists_refines_nonempty`: every stratification is
  refined by one whose strata are all nonempty.
* `AlgebraicGeometry.ConstructibleStratification.pushOpenImmersion`: a stratification carried
  forward along an open immersion.

## Implementation notes

The strata of all three constructions are the *same* objects of the big étale site as the strata
they come from — the pieces are never rebuilt — so a condition tested on a stratum's own small
étale site is carried along unchanged, up to the composition comparison for inverse image where a
structure morphism changes. That is what makes these operations usable for transporting a stratum
condition, and it is why `AlgebraicGeometry.ConstructibleStratification.ofPartition`, which
replaces every part by the reduced induced scheme on it, cannot be used instead.

`addComplement` indexes its strata by `Fin.cons`, so that the new stratum is the zeroth one and the
old strata keep their indices shifted by one. The two projections of `Fin.cons` hold by definitional
unfolding of `Fin.cases`, which is what lets
`AlgebraicGeometry.ConstructibleStratification.addInclusion_succ` be stated at all, the type of a
structure morphism depending on the stratum it belongs to. The family of strata and the family of
their structure morphisms are therefore named separately, as
`AlgebraicGeometry.ConstructibleStratification.addPiece` and `.addInclusion`, so that the proofs of
the stratification axioms can rewrite with those two projections.

## References

* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 09YD](https://stacks.math.columbia.edu/tag/09YD)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- **Stacks 09YD for an open subscheme.** A subset of a quasi-compact open subscheme of a
quasi-separated scheme is constructible there exactly when it is constructible in the ambient
scheme.

The forward direction is the content: it is Mathlib's
`Topology.IsConstructible.image_of_isOpenEmbedding`, which is Tag 09YD, applied to the open
immersion of the subscheme, whose image is retrocompact because it is a quasi-compact open of a
quasi-separated space. -/
@[sga "3 VIB 3.7" "(ii)"]
public theorem isConstructible_opens_ι_preimage_iff {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) {A : Set Y} (hA : A ⊆ (V : Set Y)) :
    Topology.IsConstructible (V.ι.base ⁻¹' A) ↔ Topology.IsConstructible A :=
  Topology.isConstructible_preimage_iff_of_isOpenEmbedding V.isOpenEmbedding
    (by rw [V.range_ι]; exact hV.isRetrocompact V.2) (by rw [V.range_ι]; exact hA)

/-- Constructibility inside the whole scheme, viewed as the top open subscheme, is constructibility
in the scheme. -/
public theorem isConstructible_top_ι_preimage_iff {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (A : Set Y) :
    Topology.IsConstructible ((⊤ : Y.Opens).ι.base ⁻¹' A) ↔ Topology.IsConstructible A :=
  isConstructible_opens_ι_preimage_iff (⊤ : Y.Opens)
    (by rw [TopologicalSpace.Opens.coe_top]; exact CompactSpace.isCompact_univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact Set.subset_univ _)

namespace ConstructibleStratification

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

variable {B : BigEtaleSite.{u}} {X : B.Scheme}

/-! ### Adjoining the complement of a quasi-compact open -/

section AddComplement

variable {Y : B.Scheme} (V : Y.obj.Opens) (s : ConstructibleStratification B Y V)

/-- The complement of an open subscheme `V`, as an object of the big étale site immersed in `Y`:
the reduced induced scheme on the closed set `Vᶜ`. -/
public def complementPiece : B.Scheme :=
  partitionPiece B Y ((V : Set Y.obj)ᶜ) V.2.isClosed_compl.isLocallyClosed

/-- The structure morphism of `AlgebraicGeometry.ConstructibleStratification.complementPiece`. -/
public def complementInclusion : complementPiece V ⟶ Y :=
  partitionInclusion B Y ((V : Set Y.obj)ᶜ) V.2.isClosed_compl.isLocallyClosed

/-- The complementary stratum is immersed in `Y`. -/
public theorem isImmersion_complementInclusion :
    IsImmersion (B.inclusion.map (complementInclusion V)) := by
  have h : IsImmersion (B.inclusion.map
      (partitionInclusion B Y ((V : Set Y.obj)ᶜ) V.2.isClosed_compl.isLocallyClosed)) := by
    rw [map_partitionInclusion]
    exact isImmersion_reducedInducedInclusion _ _
  exact h

/-- The complementary stratum has image the complement of `V`. -/
public theorem range_complementInclusion :
    Set.range (B.inclusion.map (complementInclusion V)).base = ((V : Set Y.obj)ᶜ) :=
  range_partitionInclusion B Y _ _

/-- The strata of `AlgebraicGeometry.ConstructibleStratification.addComplement`: the complementary
stratum in position zero, the strata of `s` after it. -/
public def addPiece : Fin (s.n + 1) → B.Scheme := Fin.cons (complementPiece V) s.piece

/-- The structure morphisms of the strata of
`AlgebraicGeometry.ConstructibleStratification.addComplement`. -/
public def addInclusion : ∀ i : Fin (s.n + 1), addPiece V s i ⟶ Y :=
  Fin.cases (motive := fun i => addPiece V s i ⟶ Y) (complementInclusion V) s.inclusion

public theorem addInclusion_zero : addInclusion V s 0 = complementInclusion V := rfl

public theorem addInclusion_succ (i : Fin s.n) : addInclusion V s i.succ = s.inclusion i := rfl

/-- **A stratification of a quasi-compact open, extended to the whole scheme.** Adjoining the
reduced induced scheme on the closed complement of `V` as a zeroth stratum turns a constructible
stratification of `V` into one of `Y`.

The old strata keep their objects of the big étale site and their structure morphisms, so a
condition tested on a stratum is untouched; only their indices shift by one. Their images, which
were constructible inside `V`, are constructible in `Y` by
`AlgebraicGeometry.isConstructible_opens_ι_preimage_iff`, which is Stacks 09YD. -/
public def addComplement [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    (hV : IsCompact (V : Set Y.obj)) : ConstructibleStratification B Y ⊤ where
  n := s.n + 1
  piece := addPiece V s
  inclusion := addInclusion V s
  isImmersion := by
    refine Fin.cases ?_ fun i => s.isImmersion i
    exact isImmersion_complementInclusion V
  contained i := by rw [TopologicalSpace.Opens.coe_top]; exact Set.subset_univ _
  constructible := by
    have hzero : Topology.IsConstructible ((⊤ : Y.obj.Opens).ι.base ⁻¹'
        Set.range (B.inclusion.map (complementInclusion V)).base) := by
      rw [isConstructible_top_ι_preimage_iff, range_complementInclusion]
      exact Topology.isConstructible_compl.mpr (hV.isConstructible V.2)
    have hsucc : ∀ i : Fin s.n, Topology.IsConstructible ((⊤ : Y.obj.Opens).ι.base ⁻¹'
        Set.range (B.inclusion.map (s.inclusion i)).base) := by
      intro i
      rw [isConstructible_top_ι_preimage_iff,
        ← isConstructible_opens_ι_preimage_iff V hV (s.contained i)]
      exact s.constructible i
    exact Fin.cases hzero hsucc
  pairwise_disjoint := by
    have key : ∀ i : Fin s.n, Disjoint
        (Set.range (B.inclusion.map (complementInclusion V)).base)
        (Set.range (B.inclusion.map (s.inclusion i)).base) := by
      intro i
      rw [range_complementInclusion]
      exact Set.disjoint_left.mpr fun x hx hx' => hx (s.contained i hx')
    exact Fin.cases (Fin.cases (fun h => absurd rfl h) fun j _ => key j)
      fun i => Fin.cases (fun _ => (key i).symm)
        fun j hij => s.pairwise_disjoint i j fun h => hij (by rw [h])
  covers := by
    have hunion : ⋃ i : Fin (s.n + 1), Set.range (B.inclusion.map (addInclusion V s i)).base =
        Set.range (B.inclusion.map (complementInclusion V)).base ∪ ⋃ i : Fin s.n,
          Set.range (B.inclusion.map (s.inclusion i)).base := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact Or.inl hi
        · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hi⟩)
      · rcases hx with hx | hx
        · exact Set.mem_iUnion.mpr ⟨0, hx⟩
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨j.succ, hj⟩
    rw [hunion, range_complementInclusion, ← s.covers, TopologicalSpace.Opens.coe_top,
      Set.compl_union_self]

public theorem addComplement_n [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    (hV : IsCompact (V : Set Y.obj)) : (addComplement V s hV).n = s.n + 1 := rfl

/-- The strata of `AlgebraicGeometry.ConstructibleStratification.addComplement` are the
complementary stratum and the strata of the original stratification. -/
public theorem addComplement_inclusion [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    (hV : IsCompact (V : Set Y.obj)) (i : Fin (s.n + 1)) :
    (addComplement V s hV).inclusion i = addInclusion V s i := rfl

end AddComplement

/-! ### Discarding the empty strata -/

/-- **Every stratification is refined by one all of whose strata are nonempty.** The refinement is
the subfamily of the strata whose image has a point; it covers the same open subscheme, because the
discarded strata contribute nothing to the union, and each of its strata is literally a stratum of
the original, so it refines it by identity morphisms.

A condition on strata need not hold on a stratum with no points, so a construction which locates a
stratum inside a given stratification by choosing a point in it has to discard the empty strata
first. -/
public theorem exists_refines_nonempty {U : X.obj.Opens} (s : ConstructibleStratification B X U) :
    ∃ r : ConstructibleStratification B X U, r.Refines s ∧
      ∀ k : Fin r.n, (Set.range (B.inclusion.map (r.inclusion k)).base).Nonempty := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin
    {k : Fin s.n // (Set.range (B.inclusion.map (s.inclusion k)).base).Nonempty}
  refine ⟨{ n := m
            piece := fun k => s.piece (e.symm k)
            inclusion := fun k => s.inclusion (e.symm k)
            isImmersion := fun k => s.isImmersion _
            contained := fun k => s.contained _
            constructible := fun k => s.constructible _
            pairwise_disjoint := fun k l hkl =>
              s.pairwise_disjoint _ _ fun h => hkl (by
                have : e.symm k = e.symm l := Subtype.ext h
                simpa using congrArg e this)
            covers := ?_ },
    fun k => ⟨(e.symm k).1, 𝟙 _, by rw [CategoryTheory.Functor.map_id]; infer_instance,
      by rw [Category.id_comp]⟩,
    fun k => (e.symm k).2⟩
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [s.covers] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨e ⟨i, ⟨x, hi⟩⟩, ?_⟩
    rw [e.symm_apply_apply ⟨i, ⟨x, hi⟩⟩]
    exact hi
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact s.contained _ hk

/-! ### Pushing a stratification forward along an open immersion -/

section Push

variable {Y : B.Scheme} (f : Y ⟶ X) (hf : IsOpenImmersion (B.inclusion.map f))
  {V : Y.obj.Opens} (s : ConstructibleStratification B Y V)

/-- The image of a composite in the big étale site is the image of the image. -/
public theorem range_map_comp {W' T S : B.Scheme} (g : W' ⟶ T) (h : T ⟶ S) :
    Set.range (B.inclusion.map (g ≫ h)).base =
      (B.inclusion.map h).base '' Set.range (B.inclusion.map g).base := by
  rw [Functor.map_comp, show ((B.inclusion.map g ≫ B.inclusion.map h).base : _ → _) =
    (B.inclusion.map h).base ∘ (B.inclusion.map g).base from
    funext fun z => by simp only [Scheme.Hom.comp_apply, Function.comp_apply]]
  exact Set.range_comp _ _

/-- **A stratification carried forward along an open immersion.** The strata are unchanged as
objects of the big étale site; their structure morphisms are composed with `f`, and they partition
the open subscheme `W` of the target which is the image of `V`.

This is how a partition manufactured on a member of an open cover becomes a partition of an open
subscheme of the ambient scheme. The images of the strata, constructible inside `V`, are
constructible inside `W` by Stacks 09YD applied to the open embedding `V → W` cut out by `f`, whose
image `W` is retrocompact because it is a quasi-compact open of a quasi-separated space. -/
public def pushOpenImmersion [QuasiSeparatedSpace X.obj] (W : X.obj.Opens)
    (hW : (W : Set X.obj) = (B.inclusion.map f).base '' (V : Set Y.obj))
    (hWc : IsCompact (W : Set X.obj)) :
    ConstructibleStratification B X W where
  n := s.n
  piece := s.piece
  inclusion i := s.inclusion i ≫ f
  isImmersion i := by
    have h₁ : IsImmersion (B.inclusion.map (s.inclusion i)) := s.isImmersion i
    have h₂ : IsOpenImmersion (B.inclusion.map f) := hf
    simpa only [Functor.map_comp] using
      (inferInstance : IsImmersion (B.inclusion.map (s.inclusion i) ≫ B.inclusion.map f))
  contained i := by
    rw [range_map_comp, hW]
    exact Set.image_mono (s.contained i)
  constructible i := by
    have hfe : Topology.IsOpenEmbedding (B.inclusion.map f).base := by
      have := hf; exact (B.inclusion.map f).isOpenEmbedding
    -- the open embedding of `V` into `X` cut out by `f`, whose image is `W`
    have hge : Topology.IsOpenEmbedding
        ((B.inclusion.map f).base ∘ (V.ι.base : V.toScheme → Y.obj)) :=
      hfe.comp V.isOpenEmbedding
    have hgr : Set.range ((B.inclusion.map f).base ∘ (V.ι.base : V.toScheme → Y.obj)) =
        (W : Set X.obj) := by
      rw [Set.range_comp, V.range_ι, hW]
    refine (isConstructible_opens_ι_preimage_iff W hWc
      (by rw [range_map_comp, hW]; exact Set.image_mono (s.contained i))).mpr ?_
    have himg : (B.inclusion.map f).base ∘ (V.ι.base : V.toScheme → Y.obj) ''
        (V.ι.base ⁻¹' Set.range (B.inclusion.map (s.inclusion i)).base) =
        Set.range (B.inclusion.map (s.inclusion i ≫ f)).base := by
      rw [Set.image_comp, Set.image_preimage_eq_inter_range, V.range_ι,
        Set.inter_eq_left.mpr (s.contained i), range_map_comp]
    rw [← himg]
    exact (s.constructible i).image_of_isOpenEmbedding hge
      (by rw [hgr]; exact hWc.isRetrocompact W.2)
  pairwise_disjoint i j hij := by
    have hfe : Topology.IsOpenEmbedding (B.inclusion.map f).base := by
      have := hf; exact (B.inclusion.map f).isOpenEmbedding
    rw [range_map_comp, range_map_comp]
    exact (Set.disjoint_image_iff hfe.injective).mpr (s.pairwise_disjoint i j hij)
  covers := by
    rw [hW, s.covers, Set.image_iUnion]
    exact Set.iUnion_congr fun i => (range_map_comp (s.inclusion i) f).symm

public theorem pushOpenImmersion_n [QuasiSeparatedSpace X.obj] (W : X.obj.Opens)
    (hW : (W : Set X.obj) = (B.inclusion.map f).base '' (V : Set Y.obj))
    (hWc : IsCompact (W : Set X.obj)) : (pushOpenImmersion f hf s W hW hWc).n = s.n := rfl

/-- The strata of `AlgebraicGeometry.ConstructibleStratification.pushOpenImmersion` are the strata
of the original, with structure morphism composed with the open immersion. -/
public theorem pushOpenImmersion_inclusion [QuasiSeparatedSpace X.obj] (W : X.obj.Opens)
    (hW : (W : Set X.obj) = (B.inclusion.map f).base '' (V : Set Y.obj))
    (hWc : IsCompact (W : Set X.obj)) (i : Fin s.n) :
    (pushOpenImmersion f hf s W hW hWc).inclusion i = s.inclusion i ≫ f := rfl

end Push

end ConstructibleStratification

end AlgebraicGeometry

end
