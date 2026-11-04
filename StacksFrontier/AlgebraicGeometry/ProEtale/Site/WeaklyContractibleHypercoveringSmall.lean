module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallFiniteCoproducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleHypercovering
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleOneElementCoversSmall
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.CoveredByFiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map

/-!
# Weakly contractible hypercoverings in the pro-étale site of a scheme

Let `X` be a scheme in a chosen big pro-étale site and `X_proétale` its small pro-étale site. Every
object `U` of `X_proétale` has a hypercovering whose term in each degree is a single weakly
contractible object of `X_proétale` covering `U`; if `U` is quasi-compact and quasi-separated, the
term in each degree can moreover be chosen affine.

## Main definitions

* `AlgebraicGeometry.ProEtale.SmallProetale.Qcqs`: the full subcategory `X_{qcqs, proétale}` of
  quasi-compact and quasi-separated objects, with the topology
  `AlgebraicGeometry.ProEtale.SmallProetale.qcqsTopology` induced from `X_proétale`.

## Main results

* `CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_isColimit`: on a finitary extensive
  site covered by finite disjoint unions, a finite disjoint union of weakly contractible objects
  is weakly contractible.
* `AlgebraicGeometry.ProEtale.SmallProetale.exists_weaklyContractible_hypercovering`: Stacks 09A1
  (1).
* `AlgebraicGeometry.ProEtale.SmallProetale.exists_affine_weaklyContractible_hypercovering`:
  Stacks 09A1 (2).

## Implementation notes

The proof is the source's. Every object of `X_proétale` has a one-element covering by a weakly
contractible object (Stacks 0F4P), so Stacks 094K gives a hypercovering whose families are finite
and consist of weakly contractible objects; the small pro-étale site is finitary extensive and
the summands of a finite disjoint union cover it, so taking disjoint unions degreewise again
gives a hypercovering (Stacks 0DB2), by
`Hypercovering.exists_singleton_hypercovering_objects_in_finiteDisjointUnions`. A finite disjoint
union of weakly contractible objects is weakly contractible because its summands form a covering
by pairwise disjoint subobjects.

For (2) the construction of Stacks 094K is run in `X_{qcqs, proétale}`, where every object has a
one-element covering by an affine weakly contractible object (Stacks 0F4P, quasi-compact case);
the quasi-compact and quasi-separated objects are closed under fibre products, so the resulting
hypercovering is one of `X_proétale` by Stacks 0DAZ, and its finite families of affine weakly
contractible objects are replaced by their disjoint unions in `X_proétale`, a finite disjoint
union of affine schemes being affine. The source takes the finite pro-étale coverings as the
coverings of `X_{qcqs, proétale}`; here it carries the topology induced from `X_proétale`, which
is all the construction uses: that the inclusion is continuous and that the one-element affine
coverings are coverings.

## References

* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 0F4P](https://stacks.math.columbia.edu/tag/0F4P)
* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

universe w v u' u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u'} [Category.{v} C] [FinitaryExtensive C] {T : GrothendieckTopology C}

/-- On a finitary extensive site covered by finite disjoint unions, a finite disjoint union of
weakly contractible objects is weakly contractible: its summands are monomorphisms covering it,
and two distinct summands meet only in an initial object, which is covered by the empty sieve,
being the disjoint union of the empty family. -/
theorem isWeaklyContractible_of_isColimit (hT : CoveredByFiniteCoproducts.{w} T)
    {ι : Type w} [Finite ι] {Y : ι → C} (c : Cofan Y) (hc : IsColimit c)
    (hY : ∀ i, T.IsWeaklyContractible (Y i)) : T.IsWeaklyContractible c.pt := by
  refine T.isWeaklyContractible_of_disjointCover Y c.inj (hT c hc)
    (fun i ↦ FinitaryExtensive.mono_ι hc ⟨i⟩) (fun i j hij Z a b hab ↦ ?_) hY
  have hZ : IsInitial Z := IsInitial.ofStrict
    ((FinitaryExtensive.isPullback_initial_to hc ⟨i⟩ ⟨j⟩ (by simpa using hij)).lift a b hab)
    initialIsInitial
  have h := hT (Cofan.mk (f := fun k : PEmpty.{w + 1} ↦ k.elim) Z (fun k ↦ k.elim))
    ((isColimitEquivIsInitialOfIsEmpty _ _).symm hZ)
  refine T.superset_covering ?_ h
  rintro _ _ ⟨_, _, _, ⟨k⟩, _⟩
  exact k.elim

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.ProEtale.SmallProetale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finite coproducts in a slice of the small pro-étale site are van Kampen, because they are in
the small pro-étale site and the forgetful functor preserves them, preserves fibre products and
reflects isomorphisms. -/
instance finitaryExtensive_over (U : SmallProetale B S hS) : FinitaryExtensive (Over U) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget U)

/-- The summands of finite disjoint unions cover them in the small pro-étale site. -/
theorem coveredByFiniteCoproducts : CoveredByFiniteCoproducts.{w} (topology B S hS) :=
  fun _ _ _ c hc ↦ ofArrows_mem_topology_of_isColimit B S hS c hc

/-- **Stacks Project, Tag 09A1 (1).** Let `S` be a scheme in a chosen big pro-étale site. Every
object `U` of the small pro-étale site `S_proétale` admits a hypercovering `K` of `U` in
`S_proétale` such that each term `K_n` consists of a single weakly contractible object of
`S_proétale` covering `U`. -/
@[stacks 09A1 "(1)"]
theorem exists_weaklyContractible_hypercovering (U : SmallProetale B S hS) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over U)),
      IsHypercovering (topology B S hS).toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            (topology B S hS).IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              (topology B S hS).toPretopology U := by
  refine exists_singleton_hypercovering_objects_in_finiteDisjointUnions (topology B S hS)
    {V | (topology B S hS).IsWeaklyContractible V} U
    (takeUnionsFinPreservesCoverings_of_coveredByFiniteCoproducts
      (coveredByFiniteCoproducts B S hS) U)
    (fun A _ hA ↦ GrothendieckTopology.isWeaklyContractible_of_isColimit
      (coveredByFiniteCoproducts B S hS) _
      (isColimitOfHasCoproductOfPreservesColimit (Over.forget U) A.obj) hA)
    (fun Y ↦ ?_)
  obtain ⟨V, p, hcov, hwc⟩ := exists_weaklyContractible_singleton_covering_small B S hS Y
  refine ⟨PUnit.{w + 1}, fun _ ↦ V, fun _ ↦ p, inferInstance, fun _ ↦ hwc, ?_⟩
  rw [ofArrows_pUnit'.{w} p, GrothendieckTopology.mem_toPretopology]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨PreZeroHypercover.singleton p, by simp [PreZeroHypercover.presieve₀], hcov⟩

/-! ### The affine version on quasi-compact and quasi-separated objects -/

/-- The quasi-compact and quasi-separated objects of the small pro-étale site. -/
def IsQcqs : ObjectProperty (SmallProetale B S hS) := fun V ↦
  CompactSpace ((toScheme B S hS).obj V) ∧ QuasiSeparatedSpace ((toScheme B S hS).obj V)

/-- The full subcategory `S_{qcqs, proétale}` of quasi-compact and quasi-separated objects of the
small pro-étale site. -/
abbrev Qcqs := (IsQcqs B S hS).FullSubcategory

/-- An affine object of the small pro-étale site is quasi-compact and quasi-separated. -/
theorem isQcqs_of_isAffine {V : SmallProetale B S hS} (hV : IsAffine ((toScheme B S hS).obj V)) :
    IsQcqs B S hS V :=
  ⟨inferInstance, inferInstance⟩

/-- Quasi-compact and quasi-separated objects are closed under fibre products: a morphism from a
quasi-compact scheme to a quasi-separated one is quasi-compact, and quasi-separatedness passes to
base changes. -/
instance : (IsQcqs B S hS).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let F := toScheme B S hS
    let f := p.diag.map WalkingCospan.Hom.inl
    let g := p.diag.map WalkingCospan.Hom.inr
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.left
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.right
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.one
    have hc := (IsLimit.postcomposeHomEquiv (diagramIsoCospan p.diag) _).symm p.isLimit
    let e : F.obj X ≅ pullback (F.map f) (F.map g) :=
      ((PullbackCone.isLimitMapConeEquiv _ F).1 (isLimitOfPreserves F hc)).conePointUniqueUpToIso
        (pullback.isLimit _ _)
    have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) (F.map f) (F.map g)) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (F.map f) (F.map g))
    exact ⟨e.inv.homeomorph.compactSpace, (quasiSeparatedSpace_congr e.hom.homeomorph).2 ‹_›⟩

/-- The quasi-compact and quasi-separated objects cover every object of the small pro-étale site:
the affine opens of its underlying scheme do. -/
instance : (IsQcqs B S hS).ι.IsCoverDense (topology B S hS) where
  is_cover X := by
    refine (topology B S hS).superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (ofArrows_affineCoverObject_mem_precoverage B ⟨S, hS⟩ X))
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨⟨⟨_, isQcqs_of_isAffine B S hS (isAffine_affineCoverObject B ⟨S, hS⟩ X i)⟩,
      𝟙 _, affineCoverMap B ⟨S, hS⟩ X i, (Category.id_comp _).symm⟩⟩

/-- The site `S_{qcqs, proétale}`: the topology induced from the small pro-étale site, whose
covering sieves are those whose image covers in `S_proétale`. -/
abbrev qcqsTopology : GrothendieckTopology (Qcqs B S hS) :=
  (IsQcqs B S hS).ι.inducedTopology (topology B S hS)

/-- The inclusion of `S_{qcqs, proétale}` into `S_proétale` takes covering families to covering
families. -/
theorem mapsCoveringsToCoverings_qcqs :
    MapsCoveringsToCoverings.{w} (IsQcqs B S hS).ι (qcqsTopology B S hS).toPretopology
      (topology B S hS).toPretopology := by
  intro V ι A g hg
  rw [GrothendieckTopology.mem_toPretopology] at hg ⊢
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hg
  rwa [← Sieve.ofArrows, ← Sieve.functorPushforward_ofArrows]

/-- **Stacks Project, Tag 09A1 (2).** Let `S` be a scheme in a chosen big pro-étale site. Every
quasi-compact and quasi-separated object `U` of the small pro-étale site `S_proétale` admits a
hypercovering `K` of `U` in `S_proétale` such that each term `K_n` consists of a single affine
and weakly contractible object of `S_proétale` covering `U`. -/
@[stacks 09A1 "(2)"]
theorem exists_affine_weaklyContractible_hypercovering (U : SmallProetale B S hS)
    [CompactSpace ((toScheme B S hS).obj U)] [QuasiSeparatedSpace ((toScheme B S hS).obj U)] :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over U)),
      IsHypercovering (topology B S hS).toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            IsAffine ((toScheme B S hS).obj ((K.obj (op ⦋n⦌)).obj i).left) ∧
            (topology B S hS).IsWeaklyContractible ((K.obj (op ⦋n⦌)).obj i).left ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈
              (topology B S hS).toPretopology U := by
  let P : Set (SmallProetale B S hS) :=
    {V | IsAffine ((toScheme B S hS).obj V) ∧ (topology B S hS).IsWeaklyContractible V}
  let U' : Qcqs B S hS := ⟨U, inferInstance, inferInstance⟩
  -- a hypercovering of `U` in `S_{qcqs, proétale}` by finite families of affine weakly
  -- contractible objects (Stacks 094K)
  obtain ⟨K, hK, hfin⟩ := exists_finite_hypercovering (qcqsTopology B S hS).toPretopology
    {V | V.obj ∈ P} (fun Y ↦ by
      obtain ⟨_, _⟩ := Y.property
      obtain ⟨V, p, hcov, haff, hwc⟩ :=
        exists_affine_weaklyContractible_singleton_covering_small B S hS Y.obj
      refine ⟨PUnit.{w + 1}, fun _ ↦ ⟨V, isQcqs_of_isAffine B S hS haff⟩,
        fun _ ↦ ObjectProperty.homMk p, inferInstance, fun _ ↦ ⟨haff, hwc⟩, ?_⟩
      rw [GrothendieckTopology.mem_toPretopology,
        Functor.mem_inducedTopology_iff_of_isCoverDense, ← Sieve.ofArrows,
        Sieve.functorPushforward_ofArrows]
      show Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{w + 1} ↦ V) (fun _ ↦ p)) ∈ _
      rw [ofArrows_pUnit'.{w}]
      exact Precoverage.generate_mem_toGrothendieck
        ⟨PreZeroHypercover.singleton p, by simp [PreZeroHypercover.presieve₀], hcov⟩)
    (coverOfAdjoin_toPretopology.{w} (qcqsTopology B S hS) {V | V.obj ∈ P}) U'
  -- its image in `S_proétale` is a hypercovering of `U` (Stacks 0DAZ)
  have hK' := IsHypercovering.map _ _ _ (mapsCoveringsToCoverings_qcqs B S hS) K hK
  -- and its terms may be replaced by their disjoint unions (Stacks 0DB2)
  have hsum : SumMemFin.{w} P U := by
    intro A _ hA
    have : ∀ k, IsAffine ((Over.forget U ⋙ toScheme B S hS).obj (A.obj k)) :=
      fun k ↦ (hA k).1
    refine ⟨IsAffine.of_isIso
      (PreservesCoproduct.iso (Over.forget U ⋙ toScheme B S hS) A.obj).hom, ?_⟩
    exact GrothendieckTopology.isWeaklyContractible_of_isColimit
      (coveredByFiniteCoproducts B S hS) _
      (isColimitOfHasCoproductOfPreservesColimit (Over.forget U) A.obj) (fun k ↦ (hA k).2)
  obtain ⟨L, hL, hLn⟩ := exists_singleton_hypercovering_of_finite (topology B S hS) P
    (takeUnionsFinPreservesCoverings_of_coveredByFiniteCoproducts
      (coveredByFiniteCoproducts B S hS) U) hsum _ hK'
    (fun n ↦ ⟨(hfin n).1, fun i ↦ (hfin n).2 i⟩)
  exact ⟨L, hL, fun n ↦ by
    obtain ⟨i, hi, hP, hcov⟩ := hLn n
    exact ⟨i, hi, hP.1, hP.2, hcov⟩⟩

end AlgebraicGeometry.ProEtale.SmallProetale

end
