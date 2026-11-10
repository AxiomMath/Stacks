module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Separation.Regular

/-!
# Pro-`p` groups and maximal pro-`p` subgroups

Let `p` be a prime. A topological group is *pro-`p`* if its quotient by every open normal
subgroup is a `p`-group; for a profinite group this says that it is a limit of finite `p`-groups.
A *maximal pro-`p` subgroup* of a topological group `G` is a closed subgroup which is pro-`p` for
the subspace topology and is not properly contained in another closed pro-`p` subgroup.

The main result is that a maximal pro-`p` subgroup `H` of a profinite group `G` is a Sylow
subgroup "at every finite level": for every open normal subgroup `N` of `G` the image of `H` in
the finite group `G ⧸ N` is a Sylow `p`-subgroup. Consequently every open subgroup of `G`
containing `H` has index prime to `p`. In the language of supernatural numbers, `H` is a
`p`-Sylow subgroup of `G`.

## Main definitions

* `IsProPGroup p G`: the quotient of `G` by every open normal subgroup is a `p`-group.
* `IsMaximalProPSubgroup p H`: `H` is maximal among the closed pro-`p` subgroups of `G`.

## Main results

* `IsProPGroup.isPGroup_map`: the image of a pro-`p` subgroup in the quotient by an open normal
  subgroup is a `p`-group.
* `IsMaximalProPSubgroup.exists_sylow_eq_map`: the image of a maximal pro-`p` subgroup of a
  profinite group in the quotient by an open normal subgroup is a Sylow `p`-subgroup.
* `IsMaximalProPSubgroup.not_dvd_index`: an open subgroup containing a maximal pro-`p` subgroup
  of a profinite group has index prime to `p`.

## Implementation notes

Profiniteness of `G` is expressed by `CompactSpace G` and `TotallyDisconnectedSpace G` for a
topological group, which is what makes the open normal subgroups a basis of neighbourhoods of
the identity.

The proof of `IsMaximalProPSubgroup.exists_sylow_eq_map` is the usual compactness argument. The
Sylow subgroups of the finite quotients `G ⧸ N` containing the image of `H` form an inverse
system of nonempty finite sets, which therefore has a compatible family `(P_N)`. The
intersection `Q` of the preimages of the `P_N` is a closed pro-`p` subgroup containing `H`, so
`Q = H` by maximality; a second compactness argument shows that `Q` maps onto each `P_N`.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [J.-P. Serre, *Galois cohomology*, I.1.4][serre1997galois]
-/

@[expose] public section

open CategoryTheory

universe u

/-- A topological group is *pro-`p`* if its quotient by every open normal subgroup is a
`p`-group. For a profinite group this says that it is a limit of finite `p`-groups. -/
def IsProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G, IsPGroup p (G ⧸ N.toSubgroup)

/-- A subgroup `H` of a topological group `G` is a *maximal pro-`p` subgroup* if it is closed,
pro-`p` for the subspace topology, and not properly contained in another closed pro-`p`
subgroup of `G`. -/
def IsMaximalProPSubgroup (p : ℕ) {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) :
    Prop :=
  Maximal (fun K : Subgroup G ↦ IsClosed (K : Set G) ∧ IsProPGroup p K) H

namespace IsProPGroup

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]

/-- The image of a pro-`p` subgroup in the quotient by an open normal subgroup is a
`p`-group. -/
theorem isPGroup_map {K : Subgroup G} (hK : IsProPGroup p K) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : IsPGroup p (K.map (QuotientGroup.mk' N)) := by
  let N' : OpenNormalSubgroup K :=
    { toSubgroup := N.subgroupOf K
      isOpen' := hN.preimage continuous_subtype_val
      isNormal' := inferInstance }
  let ψ := (QuotientGroup.mk' N).subgroupMap K
  have hle : N'.toSubgroup ≤ ψ.ker := fun x hx ↦ by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).mpr hx)
  refine IsPGroup.of_surjective (hK N') (QuotientGroup.lift _ ψ hle) fun y ↦ ?_
  obtain ⟨x, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ y
  exact ⟨x, rfl⟩

end IsProPGroup

namespace IsMaximalProPSubgroup

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {H : Subgroup G}

/-- A compact totally disconnected topological group is zero-dimensional. -/
private instance : ZeroDimensionalSpace G :=
  haveI : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.mpr
    (connectedComponent_eq_singleton (1 : G) ▸ isClosed_connectedComponent)
  inferInstance

/-- The map between the quotients by two nested normal subgroups. -/
private abbrev quotMap {N N' : Subgroup G} [N.Normal] [N'.Normal] (h : N ≤ N') :
    G ⧸ N →* G ⧸ N' :=
  QuotientGroup.map N N' (MonoidHom.id G) h

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private lemma quotMap_surjective {N N' : Subgroup G} [N.Normal] [N'.Normal] (h : N ≤ N') :
    Function.Surjective (quotMap h) :=
  QuotientGroup.map_surjective_of_surjective _ _ _
    (QuotientGroup.mk_surjective.comp Function.surjective_id) h

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private lemma quotMap_mk {N N' : Subgroup G} [N.Normal] [N'.Normal] (h : N ≤ N') (x : G) :
    quotMap h (x : G ⧸ N) = (x : G ⧸ N') := rfl

/-- The image of a Sylow subgroup of `G ⧸ N` containing the image of `H` in a coarser
quotient. -/
private def sylowMap {N N' : OpenNormalSubgroup G} (h : N ≤ N')
    (P : {P : Sylow p (G ⧸ N.toSubgroup) // H.map (QuotientGroup.mk' N.toSubgroup) ≤ P}) :
    {P : Sylow p (G ⧸ N'.toSubgroup) // H.map (QuotientGroup.mk' N'.toSubgroup) ≤ P} :=
  ⟨Sylow.mapSurjective (quotMap_surjective h) P.1, by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, P.2 ⟨x, hx, rfl⟩, rfl⟩⟩

omit [TotallyDisconnectedSpace G] in
private lemma sylowMap_coe {N N' : OpenNormalSubgroup G} (h : N ≤ N')
    (P : {P : Sylow p (G ⧸ N.toSubgroup) // H.map (QuotientGroup.mk' N.toSubgroup) ≤ P}) :
    (sylowMap h P).1.toSubgroup = P.1.toSubgroup.map (quotMap h) :=
  Sylow.coe_mapSurjective (quotMap_surjective h) _

/-- The Sylow subgroups of `G ⧸ N` containing the image of `H`, as an inverse system indexed by
the open normal subgroups `N`. -/
private def sylowSystem (H : Subgroup G) : OpenNormalSubgroup G ⥤ Type u where
  obj N := {P : Sylow p (G ⧸ N.toSubgroup) // H.map (QuotientGroup.mk' N.toSubgroup) ≤ P}
  map f := TypeCat.ofHom (sylowMap (leOfHom f))
  map_id N := by
    ext P y
    change y ∈ (sylowMap le_rfl P).1.toSubgroup ↔ y ∈ P.1.toSubgroup
    rw [sylowMap_coe]
    induction y using QuotientGroup.induction_on
    refine ⟨?_, fun hy ↦ ⟨_, hy, rfl⟩⟩
    rintro ⟨z, hz, hzy⟩
    induction z using QuotientGroup.induction_on
    rw [← hzy]
    exact hz
  map_comp {N N' N''} f g := by
    ext P y
    change y ∈ (sylowMap _ P).1.toSubgroup ↔ y ∈ (sylowMap _ (sylowMap _ P)).1.toSubgroup
    rw [sylowMap_coe, sylowMap_coe, sylowMap_coe, Subgroup.map_map,
      show quotMap (leOfHom (f ≫ g)) = (quotMap (leOfHom g)).comp (quotMap (leOfHom f)) from
        QuotientGroup.monoidHom_ext _ rfl]

private instance (N : OpenNormalSubgroup G) : Finite (G ⧸ N.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen'

private instance (N : OpenNormalSubgroup G) : Finite ((sylowSystem (p := p) H).obj N) :=
  Subtype.finite

omit [TotallyDisconnectedSpace G] in
private lemma nonempty_sylowSystem (hH : IsMaximalProPSubgroup p H) (N : OpenNormalSubgroup G) :
    Nonempty ((sylowSystem (p := p) H).obj N) := by
  obtain ⟨P, hP⟩ := (hH.prop.2.isPGroup_map N.toSubgroup N.isOpen').exists_le_sylow
  exact ⟨⟨P, hP⟩⟩

omit [TotallyDisconnectedSpace G] in
/-- A compatible family of Sylow subgroups of the finite quotients containing the images of a
maximal pro-`p` subgroup. -/
private lemma exists_section (hH : IsMaximalProPSubgroup p H) :
    ∃ s : ∀ N : OpenNormalSubgroup G, (sylowSystem (p := p) H).obj N,
      ∀ {N N' : OpenNormalSubgroup G} (h : N ≤ N'), sylowMap h (s N) = s N' := by
  have := nonempty_sylowSystem hH
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (sylowSystem (p := p) H)
  exact ⟨s, fun h ↦ hs (homOfLE h)⟩

/-- **The image of a maximal pro-`p` subgroup of a profinite group in the quotient by an open
normal subgroup is a Sylow `p`-subgroup.** -/
theorem exists_sylow_eq_map (hH : IsMaximalProPSubgroup p H) (N : OpenNormalSubgroup G) :
    ∃ P : Sylow p (G ⧸ N.toSubgroup), (P : Subgroup (G ⧸ N.toSubgroup)) =
      H.map (QuotientGroup.mk' N.toSubgroup) := by
  obtain ⟨s, hs⟩ := exists_section hH
  -- the preimage in `G` of the chosen Sylow subgroup at level `M`
  let T : OpenNormalSubgroup G → Subgroup G := fun M ↦
    (s M).1.toSubgroup.comap (QuotientGroup.mk' M.toSubgroup)
  have hHT : ∀ M, H ≤ T M := fun M x hx ↦ (s M).2 ⟨x, hx, rfl⟩
  have hNT : ∀ M : OpenNormalSubgroup G, M.toSubgroup ≤ T M := fun M x hx ↦ by
    change ((x : G ⧸ M.toSubgroup)) ∈ (s M).1.toSubgroup
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hTclosed : ∀ M, IsClosed (T M : Set G) := fun M ↦
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (hNT M) M.isOpen')
  -- compatibility: the chosen Sylow subgroups map onto each other
  have hmap : ∀ {M M' : OpenNormalSubgroup G} (h : M ≤ M'),
      (s M).1.toSubgroup.map (quotMap h) = (s M').1.toSubgroup := fun h ↦ by
    rw [← hs h]
    exact (sylowMap_coe h (s _)).symm
  have hTmono : ∀ {M M' : OpenNormalSubgroup G}, M ≤ M' → T M ≤ T M' := by
    intro M M' h x hx
    change ((x : G ⧸ M'.toSubgroup)) ∈ (s M').1.toSubgroup
    rw [← hmap h]
    exact ⟨_, hx, rfl⟩
  -- the intersection is a closed pro-`p` subgroup containing `H`, hence equal to `H`
  let Q : Subgroup G := ⨅ M, T M
  have hHQ : H ≤ Q := le_iInf hHT
  have hQclosed : IsClosed (Q : Set G) := by
    simpa only [Q, Subgroup.coe_iInf] using isClosed_iInter hTclosed
  have hQpro : IsProPGroup p Q := by
    intro W
    obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp W.isOpen'
    obtain ⟨M, hMO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO
      ((Set.ext_iff.mp hOW 1).mpr W.toSubgroup.one_mem)
    let ψ := (QuotientGroup.mk' M.toSubgroup).subgroupMap Q
    have hker : ψ.ker ≤ W.toSubgroup := fun x hx ↦ by
      have hx' : ((x : G) : G ⧸ M.toSubgroup) = 1 := congrArg Subtype.val hx
      have : x ∈ Subtype.val ⁻¹' O := hMO ((QuotientGroup.eq_one_iff (x : G)).mp hx')
      rwa [hOW] at this
    exact IsPGroup.of_surjective
      (IsPGroup.of_injective
        ((s M).1.isPGroup'.to_le (Subgroup.map_le_iff_le_comap.mpr (iInf_le T M)))
        (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ))
      (quotMap hker) (quotMap_surjective hker)
  have hQH : Q = H := le_antisymm (hH.2 ⟨hQclosed, hQpro⟩ hHQ) hHQ
  -- `Q` maps onto each chosen Sylow subgroup
  refine ⟨(s N).1, le_antisymm ?_ (s N).2⟩
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  let C : OpenNormalSubgroup G → Set G := fun M ↦
    (T M : Set G) ∩ {x | g⁻¹ * x ∈ N.toSubgroup}
  have hCclosed : ∀ M, IsClosed (C M) := fun M ↦ (hTclosed M).inter
    ((Subgroup.isClosed_of_isOpen _ N.isOpen').preimage (continuous_const_mul g⁻¹))
  have hCne : ∀ M, (C M).Nonempty := fun M ↦ by
    obtain ⟨z, hz, hzg⟩ := (hmap (inf_le_right : M ⊓ N ≤ N)).ge hy
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨g', hTmono inf_le_left hz,
      QuotientGroup.eq.mp (hzg : ((g' : G) : G ⧸ N.toSubgroup) = g).symm⟩
  have hCdir : Directed (· ⊇ ·) C := fun M M' ↦
    ⟨M ⊓ M', fun x hx ↦ ⟨hTmono inf_le_left hx.1, hx.2⟩,
      fun x hx ↦ ⟨hTmono inf_le_right hx.1, hx.2⟩⟩
  have : Nonempty (OpenNormalSubgroup G) := ⟨N⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir
    hCne (fun M ↦ (hCclosed M).isCompact) hCclosed
  have hx' := Set.mem_iInter.mp hx
  refine ⟨x, hQH ▸ Subgroup.mem_iInf.mpr fun M ↦ (hx' M).1, ?_⟩
  change (x : G ⧸ N.toSubgroup) = g
  exact (QuotientGroup.eq.mpr (by simpa using (hx' N).2)).symm

/-- **An open subgroup containing a maximal pro-`p` subgroup of a profinite group has index prime
to `p`.** -/
theorem not_dvd_index (hH : IsMaximalProPSubgroup p H) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) (hHU : H ≤ U) : ¬ p ∣ U.index := by
  obtain ⟨N, hNU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU U.one_mem
  obtain ⟨P, hP⟩ := exists_sylow_eq_map hH N
  have hle : (H.map (QuotientGroup.mk' N.toSubgroup)).comap (QuotientGroup.mk' N.toSubgroup) ≤
      U := by
    rintro x ⟨h, hh, hhx⟩
    simpa using U.mul_mem (hHU hh) (hNU (QuotientGroup.eq.mp hhx))
  have hidx : U.index ∣ (P : Subgroup (G ⧸ N.toSubgroup)).index := by
    rw [hP, ← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact Subgroup.index_dvd_of_le hle
  exact fun h ↦ P.not_dvd_index (h.trans hidx)

end IsMaximalProPSubgroup

end
