module

public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.CoveringExistence

/-!
# Descent of standard coverings along affine inverse limits, uniformly in the topology

A standard `τ`-covering of an affine inverse limit of affine schemes is the base change of a
standard `τ`-covering at some stage of the system, for each of the five topologies Zariski,
étale, smooth, syntomic and fppf. The five topologies are treated uniformly by quantifying over
`AlgebraicGeometry.CoveringTopology`.

## Main results

* `AlgebraicGeometry.exists_isStandardCovering_of_isLimit`: Stacks 049N (1) stated once for
  `AlgebraicGeometry.IsStandardCovering`.

## Implementation notes

The five topology-specific descent theorems of
`StacksFrontier/AlgebraicGeometry/Topologies/Vtopology/CoveringExistence.lean` each phrase a
standard covering in the idiom native to their topology: a bundled
`AlgebraicGeometry.Scheme.Cover` for the Zariski topology, a bundled
`AlgebraicGeometry.Scheme.AffineCover` for the étale topology, and a bare indexed family for the
smooth, syntomic and fppf topologies. `AlgebraicGeometry.IsStandardCovering`, the predicate the
extending-functors development is stated over, is a bare indexed family for all five. This file
performs the translation in both directions once, so that a consumer quantifying over
`AlgebraicGeometry.CoveringTopology` needs no case analysis on the topology.

In the bundled cases the descended covering is reindexed along the index equivalence returned by
the topology-specific theorem, so that the conclusion is indexed by the original index type for
every topology; the joint surjectivity of the reindexed family is read off from the `covers`
field of the bundled cover.

## References

* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- The index of a member of a jointly surjective family covering a given point, together with a
preimage of the point. -/
private lemma exists_idx_of_jointly_surjective {T : Scheme.{u}} {J : Type w}
    {U : J → Scheme.{u}} {f : ∀ j, U j ⟶ T} (h : (⋃ j, Set.range (f j)) = Set.univ) (x : T) :
    ∃ j, ∃ y : U j, f j y = x :=
  let hx : x ∈ ⋃ j, Set.range (f j) := h ▸ Set.mem_univ x
  let ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  ⟨j, hj.choose, hj.choose_spec⟩

/-- A family reindexed along a surjection of index types is jointly surjective when the original
family is, the reindexing being recorded by an index map and an identification of the members. -/
private lemma iUnion_range_eq_univ_of_covers {T : Scheme.{u}} {J K : Type w}
    {X : K → Scheme.{u}} {g : ∀ k, X k ⟶ T} (e : J ≃ K) (idx : T → K)
    (covers : ∀ x : T, x ∈ Set.range (g (idx x))) :
    (⋃ j, Set.range (g (e j))) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨e.symm (idx x), ?_⟩
  rw [e.apply_symm_apply]
  exact covers x

/-- **Stacks 049N (1), uniformly in the topology.** Let `T = lim Tᵢ` be an affine scheme written
as an inverse limit of a cofiltered system of affine schemes. A standard `τ`-covering of `T` is,
member by member, the base change along `T ⟶ Tᵢ` of a standard `τ`-covering of `Tᵢ` for some
stage `i`, for each of the five topologies. -/
@[stacks 049N "covering_existence, stated once for AlgebraicGeometry.IsStandardCovering rather \
than separately in the idiom native to each of the five topologies"]
theorem exists_isStandardCovering_of_isLimit (τ : CoveringTopology)
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsAffine c.pt] [∀ i, IsAffine (D.obj i)]
    {J : Type w} (U : J → Scheme.{u}) (f : ∀ j, U j ⟶ c.pt)
    (h : IsStandardCovering τ U f) :
    ∃ (i : I) (Uᵢ : J → Scheme.{u}) (fᵢ : ∀ j, Uᵢ j ⟶ D.obj i),
      IsStandardCovering τ Uᵢ fᵢ ∧
        ∀ j : J, Nonempty ((Over.pullback (c.π.app i)).obj (Over.mk (fᵢ j)) ≅
          Over.mk (f j)) := by
  classical
  have hfin : Finite J := h.finite_index
  cases τ with
  | fppf =>
      obtain ⟨i, Uᵢ, fᵢ, hfᵢ, he⟩ := exists_standardFppfCovering_of_isLimit D c hc U f
        { finite_index := h.finite_index
          affine_target := inferInstance
          affine_source := h.affine_source
          flat := fun j => (h.standard j).1
          finite_presentation := fun j => (h.standard j).2
          jointly_surjective := h.jointly_surjective }
      exact ⟨i, Uᵢ, fᵢ,
        { finite_index := hfᵢ.finite_index
          affine_source := hfᵢ.affine_source
          jointly_surjective := hfᵢ.jointly_surjective
          standard := fun j => ⟨hfᵢ.flat j, hfᵢ.finite_presentation j⟩ }, he⟩
  | syntomic =>
      obtain ⟨i, Uᵢ, fᵢ, hfᵢ, he⟩ := exists_standardSyntomicCovering_of_isLimit D c hc U f
        { finite_index := h.finite_index
          affine_target := inferInstance
          affine_source := h.affine_source
          standard_syntomic := h.standard
          jointly_surjective := h.jointly_surjective }
      exact ⟨i, Uᵢ, fᵢ,
        { finite_index := hfᵢ.finite_index
          affine_source := hfᵢ.affine_source
          jointly_surjective := hfᵢ.jointly_surjective
          standard := hfᵢ.standard_syntomic }, he⟩
  | smooth =>
      have hUaff : ∀ j, IsAffine (U j) := h.affine_source
      obtain ⟨i, Uᵢ, hUᵢ, fᵢ, hfᵢ, he⟩ := exists_standardSmoothCovering_of_isLimit D c hc U f
        ⟨h.standard, h.jointly_surjective⟩
      exact ⟨i, Uᵢ, fᵢ,
        { finite_index := hfin
          affine_source := hUᵢ
          jointly_surjective := hfᵢ.2
          standard := hfᵢ.1 }, he⟩
  | etale =>
      have hUaff : ∀ j, IsAffine (U j) := h.affine_source
      have hetale : ∀ j, Etale (f j) := h.standard
      have hcov := exists_idx_of_jointly_surjective h.jointly_surjective
      let 𝒰 : c.pt.AffineCover.{w} @Etale :=
        { I₀ := J
          X j := Γ(U j, ⊤)
          f j := (U j).isoSpec.inv ≫ f j
          idx x := (hcov x).choose
          covers x := by
            refine ⟨(U (hcov x).choose).isoSpec.hom (hcov x).choose_spec.choose, ?_⟩
            rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
            exact (hcov x).choose_spec.choose_spec
          map_prop j := by
            have := hetale j
            infer_instance }
      obtain ⟨i, 𝒰ᵢ, hfinᵢ, e, he⟩ := exists_standardEtaleCovering_of_isLimit D c hc 𝒰
      refine ⟨i, fun j => Spec (𝒰ᵢ.X (e j)), fun j => 𝒰ᵢ.f (e j),
        { finite_index := hfin
          affine_source := fun j => inferInstance
          jointly_surjective :=
            iUnion_range_eq_univ_of_covers e 𝒰ᵢ.idx 𝒰ᵢ.covers
          standard := fun j => 𝒰ᵢ.map_prop (e j) }, fun j => ?_⟩
      exact ⟨(he j).some ≪≫ Over.isoMk (U j).isoSpec.symm rfl⟩
  | zariski =>
      have hopen : ∀ j, IsOpenImmersion (f j) := by
        intro j
        obtain ⟨a, eq, hfj⟩ := h.standard j
        rw [hfj]
        infer_instance
      let 𝒰 : c.pt.Cover.{w} Scheme.zariskiPrecoverage :=
        Scheme.Cover.mkOfCovers J U f (exists_idx_of_jointly_surjective h.jointly_surjective)
          hopen
      obtain ⟨i, 𝒰ᵢ, h𝒰ᵢ, e, he⟩ := exists_standardZariskiCovering_of_isLimit D c hc 𝒰
        ⟨h.finite_index, h.standard⟩
      refine ⟨i, fun j => 𝒰ᵢ.X (e j), fun j => 𝒰ᵢ.f (e j),
        { finite_index := hfin
          affine_source := fun j => ?_
          jointly_surjective :=
            iUnion_range_eq_univ_of_covers e 𝒰ᵢ.idx 𝒰ᵢ.covers
          standard := fun j => h𝒰ᵢ.2 (e j) }, fun j => ⟨(he j).some⟩⟩
      obtain ⟨a, eq, -⟩ := h𝒰ᵢ.2 (e j)
      have : IsAffine ((D.obj i).basicOpen a).toScheme :=
        (isAffineOpen_top (D.obj i)).basicOpen a
      exact (IsAffine.iff_of_isIso eq.hom).2 inferInstance

end AlgebraicGeometry

end
