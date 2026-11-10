module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation

/-!
# The weakly contractible objects situation on the small pro-étale site

Let `X` be a scheme and let `𝒪` be a sheaf of rings on the small pro-étale site `X.ProEt`. The
affine weakly contractible objects of that site cover it, by [Stacks, Tag 0990], and a locally
surjective morphism of sheaves of sets is surjective on sections over each of them. Those two
facts together with `𝒪` are exactly the data of a
`Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation`, which this file assembles.

The bundle is assembled at the value universe `u + 1` of the sheaves of sets, which is the
universe the sheaves of modules on this site take their sections in: the objects of `X.ProEt`
live in `Type (u + 1)` while its morphisms live in `Type u`. That is why the bundle is needed
at all. `CategoryTheory.GrothendieckTopology.IsWeaklyContractible` tests sheaves of sets in the
morphism universe `Type u` only, and the derived-completeness results stated for a
`AlgebraicGeometry.RingedSite` with `Small.{v} X.C` and `HasSheafify X.J (Type v)` cannot be
read at this site at all, since `X.ProEt` is not `Small.{u}`. The bundle asks for neither: its
weak contractibility condition is stated at an independent universe, and the sections
statement proved here is the one for sheaves of sets in `Type (u + 1)`.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.exists_clopenRefinement_of_isWContractible`: every covering
  sieve of an affine object of `X.ProEt` with w-contractible ring of global sections contains a
  finite family whose images form a disjoint clopen cover and which generates a covering sieve.
* `AlgebraicGeometry.Scheme.ProEt.surjective_sections_of_isWContractible`: such an object tests
  surjectivity of morphisms of sheaves of sets on `X.ProEt`, in any universe of values.
* `AlgebraicGeometry.Scheme.ProEt.weaklyContractibleObjectsSituation`: the bundle, with the
  affine weakly contractible objects as its collection.

## Implementation notes

The refinement property is the clopen-refinement form of [Stacks, Tag 098H], which is what
`CategoryTheory.GrothendieckTopology.surjective_sections_of_clopenRefinements` consumes: the
compatibility of a family of sections indexed by a disjoint clopen decomposition is automatic,
and that is what makes the statement free of the value universe. The weaker disjoint-union form
`AlgebraicGeometry.Scheme.ProEt.exists_disjointUnionRefinement_of_isWeaklyContractible` records
only that the decomposition is a colimit cofan, which does not by itself give compatibility.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe t w u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- **Stacks 098H, (1) implies (3), for the small pro-étale site `X.ProEt`.** Every covering
sieve of an affine object `W` of `X.ProEt` whose ring of global sections is w-contractible
contains a finite family of objects of `X.ProEt` whose underlying schemes form a disjoint
clopen cover of `W` and which generates a covering sieve.

The sieve is pushed forward to a pro-étale covering sieve of the spectrum of the w-contractible
ring `Γ(W, ⊤)`, where w-contractibility refines it by a finite disjoint clopen Zariski cover;
the members of that cover are open subschemes of `W`, hence weakly étale over `X`, so they are
again objects of `X.ProEt`. -/
theorem exists_clopenRefinement_of_isWContractible (W : X.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    (R : Sieve W) (hR : R ∈ ProEt.topology X W) :
    ∃ (n : ℕ) (V : Fin n → X.ProEt) (f : (i : Fin n) → V i ⟶ W),
      IsClopenDecompositionCover (fun i ↦ (ProEtale.proetaleToScheme X).obj (V i))
          (fun i ↦ (ProEtale.proetaleToScheme X).map (f i)) ∧
        Sieve.ofArrows V f ∈ ProEt.topology X W ∧ ∀ i, R.arrows (f i) := by
  classical
  let e : specOf Γ(W.left, ⊤) ≅ W.left := W.left.isoSpec.symm
  have hpush : R.functorPushforward (ProEtale.proetaleToScheme X) ∈
      Scheme.proetaleTopology W.left :=
    (CoverPreserving.of_isContinuous (ProEtale.proetaleToScheme X) (ProEt.topology X)
      Scheme.proetaleTopology).cover_preserve hR
  obtain ⟨n, V, g, hdec, href⟩ :=
    everyProetaleCoverHasZariskiRefinement_of_wContractible Γ(W.left, ⊤) hW
      ((R.functorPushforward (ProEtale.proetaleToScheme X)).pullback e.hom)
      (Scheme.proetaleTopology.pullback_stable e.hom hpush)
  have hdecW := IsClopenDecompositionCover.comp_iso e V g hdec
  have hoi : ∀ i, IsOpenImmersion (g i ≫ e.hom) := hdecW.openImmersion
  have hwe : ∀ i, WeaklyEtale (g i ≫ e.hom) := fun i ↦ by
    have := hoi i
    infer_instance
  have hweW : WeaklyEtale W.hom := W.prop
  have hwecomp : ∀ i, WeaklyEtale ((g i ≫ e.hom) ≫ W.hom) := fun i ↦ by
    have := hwe i
    infer_instance
  let U : Fin n → X.ProEt := fun i ↦
    @Scheme.ProEt.mk X _ ((g i ≫ e.hom) ≫ W.hom) (hwecomp i)
  let f : ∀ i, U i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (g i ≫ e.hom) rfl
  have hqc : ∀ i, QuasiCompact (f i).hom.left := by
    intro i
    change QuasiCompact (g i ≫ e.hom)
    have hclosed : Topology.IsClosedEmbedding (g i ≫ e.hom).base :=
      ⟨(hoi i).base_open.isEmbedding, (hdecW.clopen i).1⟩
    have _ : CompactSpace ↥(V i) := hclosed.compactSpace
    exact quasiCompact_of_compactSpace _
  have hsurj : ∀ x : W.left, ∃ i y, (f i).hom.left.base y = x := by
    intro x
    have hx : x ∈ ⋃ i, Set.range (g i ≫ e.hom).base := by
      rw [hdecW.cover]
      trivial
    exact Set.mem_iUnion.mp hx
  refine ⟨n, U, f, hdecW,
    ProEtale.sieve_ofArrows_mem_proetaleTopology U f hwe hqc hsurj, fun i ↦ ?_⟩
  obtain ⟨Z, k, h, hk, hfac⟩ := href i
  have hw : h ≫ Z.hom = (U i).hom := by
    have hkw : k.hom.left ≫ W.hom = Z.hom := by simp
    change h ≫ Z.hom = (g i ≫ e.hom) ≫ W.hom
    refine Eq.trans (congrArg (fun q ↦ h ≫ q) hkw.symm) ?_
    refine Eq.trans (Category.assoc h k.hom.left W.hom).symm ?_
    exact congrArg (fun q ↦ q ≫ W.hom) hfac.symm
  let h' : U i ⟶ Z := MorphismProperty.Over.homMk h hw
  rw [show f i = h' ≫ k from
    MorphismProperty.Comma.Hom.ext' (Comma.hom_ext _ _ hfac (Subsingleton.elim _ _))]
  exact R.downward_closed hk h'

/-- **An affine object of `X.ProEt` with w-contractible ring of global sections tests
surjectivity of morphisms of sheaves of sets**, in any universe of values: a locally surjective
morphism is surjective on sections over such an object.

At the morphism universe `Type u` this is weak contractibility in the sense of
`CategoryTheory.GrothendieckTopology.IsWeaklyContractible`, which is
`AlgebraicGeometry.ProEtale.isWeaklyContractible_of_isWContractible`. The value universe is free
because compatibility of a family of sections indexed by a disjoint clopen decomposition is
automatic, so nothing in the argument quantifies over sheaves. -/
theorem surjective_sections_of_isWContractible (W : X.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤))
    (F G : Sheaf (ProEt.topology X) (Type t)) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op W)) :=
  GrothendieckTopology.surjective_sections_of_clopenRefinements (ProEt.topology X)
    (ProEtale.proetaleToScheme X) W
    (fun Z hZ ↦ have _ : IsEmpty Z.left := hZ; ProEt.bot_mem_topology Z)
    (fun _ hf ↦ (ProEtale.proetaleToScheme X).mono_of_mono_map hf)
    (exists_clopenRefinement_of_isWContractible W hW) F G φ hφ

/-- The affine weakly contractible objects of the small pro-étale site of `X`, together with a
sheaf of rings `𝒪` on that site, form a
`Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation` whose weak contractibility is
tested on sheaves of sets in `Type (u + 1)`.

That is the universe in which sheaves of modules on this site take their sections, the objects
of `X.ProEt` lying in `Type (u + 1)` and its morphisms in `Type u`. The covering condition is
[Stacks, Tag 0990] for this site,
`AlgebraicGeometry.ProEtale.hasEnoughObjects_isAffine_isWeaklyContractible`. -/
def weaklyContractibleObjectsSituation (X : Scheme.{u})
    (O : Sheaf (ProEt.topology X) RingCat.{w}) :
    _root_.Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, u, u + 1, u + 1}
      X.ProEt (ProEt.topology X) where
  B W := IsAffine W.left ∧ (ProEt.topology X).IsWeaklyContractible W
  isWeaklyContractible {W} hW F G φ hφ :=
    have _ : IsAffine W.left := hW.1
    surjective_sections_of_isWContractible W
      (isWContractible_globalSections_of_isWeaklyContractible W hW.2) F G φ hφ
  hasEnoughObjects := ProEtale.hasEnoughObjects_isAffine_isWeaklyContractible X
  O := O

end AlgebraicGeometry.Scheme.ProEt

end
