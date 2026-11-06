module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
public import StacksFrontier.Topology.Limits.Defs
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Limits of spectral spaces along spectral maps are quasi-compact (Stacks 0A2V)

Let `F : J ⥤ TopCat` be a diagram in which every `F.obj j` is a spectral space
(Mathlib's `SpectralSpace`, i.e. `T0Space` + `CompactSpace` + `QuasiSober` +
`QuasiSeparatedSpace` + `PrespectralSpace`) and every transition map `F.map a` is a spectral map
(`IsSpectralMap`: continuous, with quasi-compact preimages of quasi-compact opens). Stacks 0A2V
says that

1. for subsets `Z j ⊆ F.obj j` closed in the constructible topology of `F.obj j`, the subset
   `limitSubset F Z = {x ∈ lim F | ∀ j, π j x ∈ Z j}` of the limit is quasi-compact, and
2. `lim F` itself is quasi-compact.

Part (2) is part (1) for `Z j = univ`.

The proof does not work in the given topologies, which are not Hausdorff: it passes to the
product of the *constructible* topologies, where each factor is compact Hausdorff
(`compactSpace_constructibleTopology`, `t2Space_constructibleTopology`) and each transition map
is still continuous (`IsSpectralMap.continuous_constructibleTopology`) — all three supplied by
`StacksFrontier.Topology.Spectral.ConstructibleTopology`. There `limitSubset F Z` is an
intersection of the closed equalizers `{u | F.map a (u i) = u j}` with the closed conditions
`{u | u j ∈ Z j}`, hence closed in a compact space, hence compact. Since the constructible
topology refines the original one (`constructibleTopology_le`), the product of the
constructible topologies refines the product topology, and compactness transfers down
(`isCompact_of_le_of_isCompact`).

Deliberate deviation from the source, not an omission: Stacks
states part (1) with the compatibility hypothesis `F.map a '' Z j ⊆ Z i`. It is **not** assumed
here, and it is not needed. The set `limitSubset F Z` is defined by the conditions
`π j x ∈ Z j` imposed at *every* index simultaneously, and that set is quasi-compact from
constructible-closedness of the `Z j` alone; compatibility is what makes the Stacks formulation's
`lim Z i` agree with it, and is only needed for the *nonemptiness* statement, Stacks 0A2W. So the
statement proved here is more general than the source's.
-/

@[expose] public section

open CategoryTheory Limits Set TopologicalSpace

universe u v

namespace SpectralLimits

variable {J : Type v} [SmallCategory J] (F : J ⥤ TopCat.{max v u})

/-- The product of the constructible topologies on `∀ j, F.obj j`. -/
abbrev piConstructibleTopology : TopologicalSpace (∀ j, (F.obj j : Type (max v u))) :=
  Pi.topologicalSpace (t₂ := fun j => constructibleTopology (F.obj j))

/-- Each projection is continuous from the product of the constructible topologies to the
constructible topology of the factor. -/
private theorem continuous_apply_piConstructible (j : J) :
    @Continuous (∀ k, (F.obj k : Type (max v u))) (F.obj j : Type (max v u))
      (piConstructibleTopology F) (constructibleTopology (F.obj j)) (fun u => u j) :=
  @continuous_apply J (fun k => (F.obj k : Type (max v u)))
    (fun k => constructibleTopology (F.obj k)) j

variable [hSpec : ∀ j, SpectralSpace (F.obj j)]

/-- By Tychonoff, the product of the constructible topologies is compact, because each factor
is compact in its constructible topology. -/
theorem compactSpace_piConstructible :
    @CompactSpace (∀ j, (F.obj j : Type (max v u))) (piConstructibleTopology F) :=
  @Pi.compactSpace J (fun j => (F.obj j : Type (max v u)))
    (fun j => constructibleTopology (F.obj j))
    (fun j => compactSpace_constructibleTopology (F.obj j))

/-- The equalizer `{u | F.map a (u i) = u j}` of a morphism `a : i ⟶ j` is closed in the product
of the constructible topologies: both sides are continuous there and `F.obj j` is Hausdorff in its
constructible topology. -/
theorem isClosed_equalizer_piConstructible
    (hF : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (F.map a).hom) {i j : J} (a : i ⟶ j) :
    @IsClosed (∀ k, (F.obj k : Type (max v u))) (piConstructibleTopology F)
      { u | (F.map a).hom (u i) = u j } := by
  exact @isClosed_eq (F.obj j : Type (max v u)) (∀ k, (F.obj k : Type (max v u)))
    (constructibleTopology (F.obj j)) (piConstructibleTopology F)
    (t2Space_constructibleTopology (F.obj j)) (fun u => (F.map a).hom (u i)) (fun u => u j)
    (@Continuous.comp _ _ _ (piConstructibleTopology F) (constructibleTopology (F.obj i))
      (constructibleTopology (F.obj j)) _ _ (hF a).continuous_constructibleTopology
      (continuous_apply_piConstructible F i))
    (continuous_apply_piConstructible F j)

omit hSpec in
/-- The condition `u j₀ ∈ Z j₀` is closed in the product of the constructible topologies, being
the preimage of a constructibly closed set under a projection. -/
theorem isClosed_apply_mem_piConstructible (Z : ∀ j, Set (F.obj j))
    (hZ_closed : ∀ j, @IsClosed _ (constructibleTopology (F.obj j)) (Z j)) (j₀ : J) :
    @IsClosed (∀ j, (F.obj j : Type (max v u))) (piConstructibleTopology F)
      { u | u j₀ ∈ Z j₀ } :=
  @IsClosed.preimage _ _ (piConstructibleTopology F) (constructibleTopology (F.obj j₀))
    _ (continuous_apply_piConstructible F j₀) _ (hZ_closed j₀)

/-- The set of compatible families lying in the `Z j` is compact in the product of the
constructible topologies: it is the intersection of the closed sets of the two previous lemmas
inside a compact space. -/
theorem isCompact_compatible_piConstructible
    (hF : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (F.map a).hom) (Z : ∀ j, Set (F.obj j))
    (hZ_closed : ∀ j, @IsClosed _ (constructibleTopology (F.obj j)) (Z j)) :
    @IsCompact (∀ j, (F.obj j : Type (max v u))) (piConstructibleTopology F)
      { u | (∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).hom (u i) = u j) ∧ (∀ j, u j ∈ Z j) } := by
  have hS_eq : { u : ∀ j, (F.obj j : Type (max v u)) |
      (∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).hom (u i) = u j) ∧ (∀ j, u j ∈ Z j) } =
      (⋂ (i : J), ⋂ (j : J), ⋂ (f : i ⟶ j), { u | (F.map f).hom (u i) = u j }) ∩
        ⋂ (j : J), { u | u j ∈ Z j } := by
    ext u
    simp [Set.mem_iInter]
  rw [hS_eq]
  refine @IsClosed.isCompact _ (piConstructibleTopology F) _
    (compactSpace_piConstructible F) (@IsClosed.inter _ _ _ (piConstructibleTopology F) ?_ ?_)
  · exact @isClosed_iInter _ _ (piConstructibleTopology F) _ fun i =>
      @isClosed_iInter _ _ (piConstructibleTopology F) _ fun j =>
        @isClosed_iInter _ _ (piConstructibleTopology F) _ fun f =>
          isClosed_equalizer_piConstructible F hF f
  · exact @isClosed_iInter _ _ (piConstructibleTopology F) _ fun j =>
      isClosed_apply_mem_piConstructible F Z hZ_closed j

/-- The subset of `lim F` consisting of the points whose `j`-th coordinate lies in `Z j`
for every object `j`. -/
noncomputable def limitSubset (Z : ∀ j, Set (F.obj j)) : Set ((limit F : TopCat.{max v u})) :=
  { x | ∀ j, (limit.π F j).hom x ∈ Z j }

/-- **Stacks 0A2V (1).** For a diagram of spectral spaces along spectral maps and subsets
`Z j ⊆ F.obj j` closed in the constructible topology, the subset
`{x ∈ lim F | ∀ j, π j x ∈ Z j}` of the limit is quasi-compact for the limit topology. -/
@[stacks 0A2V "part (1)"]
theorem isCompact_limitSubset
    (hF : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (F.map a).hom) (Z : ∀ j, Set (F.obj j))
    (hZ_closed : ∀ j, @IsClosed _ (constructibleTopology (F.obj j)) (Z j)) :
    IsCompact (limitSubset F Z) := by
  -- Identify `lim F` with the explicit limit cone point, a subtype of `∀ j, F.obj j`.
  let e : (limit F : TopCat.{max v u}) ≃ₜ ↑(TopCat.limitCone F).pt :=
    TopCat.homeoOfIso ((limit.isLimit F).conePointUniqueUpToIso (TopCat.limitConeIsLimit F))
  have h_eq : limitSubset F Z = e ⁻¹' { u | ∀ j, u.val j ∈ Z j } := by
    ext x
    simp only [limitSubset, mem_ofPred_eq, mem_preimage]
    have hcoord : ∀ j, (e x).val j = (limit.π F j).hom x := by
      intro j
      have h := (limit.isLimit F).conePointUniqueUpToIso_hom_comp (TopCat.limitConeIsLimit F) j
      rw [limit.cone_π] at h
      dsimp only [e]
      rw [← h, ConcreteCategory.comp_apply, TopCat.limitCone_π_app_apply, TopCat.homeoOfIso_apply]
    exact forall_congr' fun j => by rw [hcoord]
  rw [h_eq, e.isCompact_preimage]
  have hemb : @Topology.IsEmbedding _ _ (TopCat.limitCone F).pt.str Pi.topologicalSpace
      Subtype.val :=
    { toIsInducing := { eq_induced := rfl }, injective := Subtype.val_injective }
  rw [hemb.isCompact_iff]
  suffices h : IsCompact { f : ∀ j, (F.obj j : Type (max v u)) |
      (∀ ⦃i j : J⦄ (a : i ⟶ j), (F.map a).hom (f i) = f j) ∧ (∀ j, f j ∈ Z j) } by
    convert h using 1
    ext f
    constructor
    · rintro ⟨g, hgZ, rfl⟩
      exact ⟨fun {_ _} a => g.property a, hgZ⟩
    · rintro ⟨hcompat, hZ⟩
      exact ⟨⟨f, fun a => hcompat a⟩, hZ, rfl⟩
  -- Compactness in the product of the constructible topologies transfers to the coarser
  -- product topology.
  refine isCompact_of_le_of_isCompact ?_ (isCompact_compatible_piConstructible F hF Z hZ_closed)
  simp only [piConstructibleTopology, Pi.topologicalSpace]
  exact iInf_mono fun i => induced_mono (constructibleTopology_le (F.obj i))

/-- **Stacks 0A2V (2).** The limit of a diagram of spectral spaces along spectral maps is
quasi-compact. This is part (1) with `Z j = univ`. -/
@[stacks 0A2V "part (2)"]
theorem compactSpace_limit (hF : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (F.map a).hom) :
    CompactSpace ((limit F : TopCat.{max v u})) :=
  ⟨by simpa [limitSubset] using isCompact_limitSubset F hF (fun _ => univ) fun j =>
    @isClosed_univ _ (constructibleTopology (F.obj j))⟩

end SpectralLimits
