module

public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.AlgebraicStructure
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Basic
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections

/-!
# Invertible sheaves on a closed cover with discrete pairwise intersections

Let `X` be a reduced scheme covered, set theoretically, by finitely many closed subschemes
`Z i`, and suppose that two distinct members of the cover meet in a discrete space. An
invertible sheaf given on each `Z i` then extends to an invertible sheaf on `X` restricting
to the given ones, and a compatible family of sections that do not vanish along the pairwise
intersections extends simultaneously.

Both constructions go through the same two open sets. Away from the *overlap locus* -- the
union of the pairwise intersections of the images of the cover -- the cover is locally a
single one of its members, because a closed immersion into a reduced scheme with open image
is an open immersion. The overlap locus itself is closed and discrete, so the coproduct of
the `Z i` maps to `X` by a finite morphism which is an isomorphism over the complement of a
discrete closed set, and an invertible sheaf descends along such a morphism.

## Main results

* `AlgebraicGeometry.exists_invertible_of_closed_cover_discrete_intersections`: the
  invertible sheaf with the prescribed restrictions.
* `AlgebraicGeometry.exists_invertible_with_sections_of_closed_cover_discrete_intersections`:
  the same, together with a global section restricting to the prescribed sections.
* `AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit`: a sheaf of modules on a
  scheme is invertible exactly when it is locally isomorphic to the structure sheaf.

## Implementation notes

The closed subschemes are presented by closed immersions `f i : Z i ⟶ X`, and set-theoretic
covering by joint surjectivity of their underlying maps. "Restricts to `L i`" is the
existence of an isomorphism from the module pullback along `f i` to `L i`; in the second
statement the same isomorphism identifies the pullback of the glued section with the
prescribed one.

Invertibility enters both proofs only through
`AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit`, which turns it into a
pointwise trivialization by the structure sheaf.

The hypothesis that distinct members of the cover meet in a discrete space is not needed
for the second statement: once the sections are given and do not vanish along the pairwise
intersections, the invertible sheaf is built directly by patching the product of the direct
images, and no descent along the coproduct is used. The hypothesis is kept, since it is one
of the standing assumptions of the source, and its name is prefixed accordingly.

## References

* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open RingedSpaceModuleAdjunction

universe u v

namespace AlgebraicGeometry

/-- The locus where two distinct members of the cover meet. -/
private alias overlapLocus := StacksTag09NE.overlapLocus

/-- A finite union of the pairwise intersections in a closed cover is still discrete. -/
private lemma overlapLocus_discrete {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    DiscreteTopology (overlapLocus X Z f) := by
  rw [← isDiscrete_iff_discreteTopology]
  apply IsDiscrete.biUnion (I := {p : ι × ι | p.1 ≠ p.2}) (Set.toFinite _)
  · rintro ⟨i, j⟩ hp
    exact isDiscrete_iff_discreteTopology.mpr (hdiscrete i j hp)
  · rintro ⟨i, j⟩ -
    exact (f i).isClosedEmbedding.isClosed_range.inter (f j).isClosedEmbedding.isClosed_range

/-- The pairwise intersection locus is closed, so its complement is an open neighborhood of
every point lying on exactly one member of the cover. -/
private lemma overlapLocus_closed {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)] :
    IsClosed (overlapLocus X Z f) := by
  unfold overlapLocus StacksTag09NE.overlapLocus
  exact (Set.toFinite {p : ι × ι | p.1 ≠ p.2}).isClosed_biUnion fun p hp =>
    (f p.1).isClosedEmbedding.isClosed_range.inter (f p.2).isClosedEmbedding.isClosed_range

/-- The discrete complement hypothesis in `0C0T` holds after removing the overlap locus. -/
private lemma overlapComplement_discrete {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    DiscreteTopology (Uᶜ : Set X) := by
  dsimp only
  rw [Opens.coe_mk, compl_compl]
  exact overlapLocus_discrete X Z f hdiscrete


/-- The free sheaf of modules on a one-element index type is the structure sheaf. -/
private noncomputable def freeFinOneIsoUnit {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) (ULift.{u} (Fin 1)) ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
  Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
    SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- **Local triviality of invertible sheaves.** A sheaf of modules on a scheme is invertible
exactly when every point has an open neighbourhood on which it is isomorphic to the
structure sheaf.

Invertibility is finite local freeness of rank one
([Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)), and on a scheme
that is the existence of trivializations of the restrictions to the members of an open cover
by the free sheaf on a one-element index type. -/
public theorem isInvertible_iff_exists_restrict_iso_unit (X : Scheme.{u}) (M : X.Modules) :
    IsInvertible X.presheaf X.ringCatSheaf.2 M ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        Nonempty (M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) := by
  rw [show IsInvertible X.presheaf X.ringCatSheaf.2 M ↔
        SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1 from
      Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one X M,
    ← Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨U, hU, ⟨e⟩⟩ := h x
    exact ⟨U, hU, ⟨e ≪≫ freeFinOneIsoUnit U⟩⟩
  · obtain ⟨U, hU, ⟨e⟩⟩ := h x
    exact ⟨U, hU, ⟨e ≪≫ (freeFinOneIsoUnit U).symm⟩⟩

/-- A point lying on two distinct members of the cover is in the overlap locus. -/
private lemma mem_overlapLocus {ι : Type v} (X : Scheme.{u}) (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) {i j : ι} (hij : i ≠ j) {z : Z i} {z' : Z j} (h : f i z = f j z') :
    f i z ∈ overlapLocus X Z f := by
  simp only [overlapLocus, StacksTag09NE.overlapLocus, Set.mem_iUnion]
  exact ⟨(i, j), hij, ⟨z, rfl⟩, ⟨z', h.symm⟩⟩

/-- Outside the pairwise intersection locus, a point in a closed cover belongs to a unique
member. -/
private lemma existsUnique_mem_range_of_not_overlap {ι : Type v} (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (hcover : ∀ x : X, ∃ i z, f i z = x) {x : X}
    (hx : x ∉ overlapLocus X Z f) : ∃! i, x ∈ Set.range (f i) := by
  obtain ⟨i, z, rfl⟩ := hcover x
  refine ⟨i, ⟨z, rfl⟩, ?_⟩
  rintro j ⟨z', hz'⟩
  by_contra hij
  exact hx (mem_overlapLocus X Z f (Ne.symm hij) hz'.symm)

/-- An open neighborhood in a closed subscheme is induced by an open neighborhood in the
ambient scheme. -/
private lemma exists_open_in_ambient_of_open_in_closed {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (V : Y.Opens) {y : Y} (hy : y ∈ V) :
    ∃ W : X.Opens, f y ∈ W ∧ f ⁻¹ᵁ W = V := by
  obtain ⟨W, hW, hpre⟩ := f.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp V.2
  exact ⟨⟨W, hW⟩, (Set.ext_iff.mp hpre y).mpr hy, Opens.ext hpre⟩

/-- Finitely many local neighborhoods on the closed pieces can be imposed by one ambient open
neighborhood. -/
private lemma exists_open_shrinking_component_preimages {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] {x : X} (V : ∀ i, (Z i).Opens)
    (hV : ∀ i (z : Z i), f i z = x → z ∈ V i) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i, f i ⁻¹ᵁ U ≤ V i := by
  classical
  let W : ∀ i, X.Opens := fun i => if hxi : ∃ z, f i z = x then
      Classical.choose (exists_open_in_ambient_of_open_in_closed (f i) (V i)
        (hV i (Classical.choose hxi) (Classical.choose_spec hxi)))
    else ⟨(Set.range (f i))ᶜ, (f i).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : X.Opens := ⨅ i, W i
  refine ⟨U, ?_, ?_⟩
  · change x ∈ (U : Set X)
    simp only [U, Opens.coe_iInf, Set.mem_iInter]
    intro i
    by_cases hxi : ∃ z, f i z = x
    · simpa [W, hxi, Classical.choose_spec hxi] using
        (Classical.choose_spec (exists_open_in_ambient_of_open_in_closed
          (f i) (V i) (hV i (Classical.choose hxi) (Classical.choose_spec hxi)))).1
    · simp [W, hxi]
  · intro i z hz
    change (f i) z ∈ (U : Set X) at hz
    simp only [U, Opens.coe_iInf, Set.mem_iInter] at hz
    have hzW : (f i) z ∈ W i := hz i
    by_cases hxi : ∃ z, f i z = x
    · let z₀ : Z i := Classical.choose hxi
      have hz₀ : f i z₀ = x := Classical.choose_spec hxi
      have hpre := (Classical.choose_spec (exists_open_in_ambient_of_open_in_closed
        (f i) (V i) (hV i z₀ hz₀))).2
      have hzW' : (f i) z ∈ Classical.choose (exists_open_in_ambient_of_open_in_closed
          (f i) (V i) (hV i z₀ hz₀)) := by
        simpa [W, hxi] using hzW
      rw [← hpre]
      exact hzW'
    · simp [W, hxi] at hzW

/-- A prescribed section on a member of the cover is nonvanishing at every point of that
member which lies in the overlap locus. -/
private lemma nonvanishing_of_mem_overlap {ι : Type v} (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.NonvanishingTrivialize.nonvanishingLocus (Z i).toRingedSpace (L i) (s i))
    {i : ι} {z : Z i} (hz : (f i) z ∈ overlapLocus X Z f) :
    z ∈ Stacks.NonvanishingTrivialize.nonvanishingLocus (Z i).toRingedSpace (L i) (s i) := by
  change (f i) z ∈ ⋃ p ∈ {p : ι × ι | p.1 ≠ p.2},
    Set.range (f p.1) ∩ Set.range (f p.2) at hz
  obtain ⟨⟨j, k⟩, hp⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hp, ⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ := Set.mem_iUnion.mp hp
  change j ≠ k at hp
  by_cases hi : i = j
  · subst j
    exact hs i k hp z ⟨z₂, hz₂⟩
  · exact hs i j hi z ⟨z₁, hz₁⟩

/-- Away from the overlap locus, a closed cover is locally just one of its members: after
shrinking around such a point, the unique member maps isomorphically to the neighborhood. -/
private lemma exists_open_neighborhood_isIso_component_of_not_overlap
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X] (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x) {x : X}
    (hx : x ∉ overlapLocus X Z f) :
    ∃ (i : ι) (U : X.Opens), x ∈ U ∧ IsIso ((f i) ∣_ U) ∧
      ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥ := by
  classical
  obtain ⟨i, hi, huniq⟩ := existsUnique_mem_range_of_not_overlap X Z f hcover hx
  let V : ∀ j, (Z j).Opens := fun j => if j = i then ⊤ else ⊥
  have hV : ∀ j (z : Z j), f j z = x → z ∈ V j := by
    intro j z hz
    obtain rfl := huniq j ⟨z, hz⟩
    simp [V]
  obtain ⟨U, hxU, hpre⟩ := exists_open_shrinking_component_preimages X Z f V hV
  refine ⟨i, U, hxU, ?_, ?_⟩
  · have hsurj : Surjective ((f i) ∣_ U) := by
      refine ⟨fun y => ?_⟩
      obtain ⟨j, z, hz⟩ := hcover y.1
      have hzU : z ∈ f j ⁻¹ᵁ U := by
        change f j z ∈ U
        rw [hz]
        exact y.2
      by_cases hji : j = i
      · subst j
        refine ⟨⟨z, hzU⟩, U.ι.isOpenEmbedding.injective ?_⟩
        exact (morphismRestrict_base_coe (f i) U ⟨z, hzU⟩).trans hz
      · simpa [V, hji] using hpre j hzU
    have : IsClosedImmersion ((f i) ∣_ U) := inferInstance
    have : IsReduced U.toScheme := inferInstance
    exact isIso_of_isClosedImmersion_of_surjective ((f i) ∣_ U)
  · exact fun j hji => le_bot_iff.mp (by simpa [V, hji] using hpre j)

/-- A disjoint open cover of schemes with common target presents that target as their
coproduct. -/
private alias isIso_sigmaDesc_of_disjointOpenCover :=
  StacksTag09NE.isIso_sigmaDesc_of_disjointOpenCover

/-- A closed immersion into a reduced scheme is an open immersion when its image is open. -/
private lemma isOpenImmersion_of_closedImmersion_of_open_range {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) [IsClosedImmersion g] [IsReduced Z]
    (hopen : IsOpen (Set.range ⇑g)) : IsOpenImmersion g := by
  let U : Z.Opens := ⟨Set.range ⇑g, hopen⟩
  have hsub : Set.range ⇑g ⊆ Set.range ⇑U.ι := by simp [U]
  let q : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hsub
  have hfac : q ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hsub
  have hqcomp : IsClosedImmersion (q ≫ U.ι) := hfac ▸ inferInstance
  have hqclosed : IsClosedImmersion q := IsClosedImmersion.of_comp q U.ι
  have hqsurjective : Surjective q := ⟨fun ⟨z, hz⟩ ↦ by
    change z ∈ Set.range ⇑g at hz
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    have hqg : U.ι (q y) = g y := by
      simpa only [← Scheme.Hom.comp_apply] using congr($hfac y)
    rw [hqg, hy]
    rfl⟩
  have : IsReduced U.toScheme := inferInstance
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  rw [← hfac]
  infer_instance

/-- Every member of a finite disjoint closed cover is open. -/
private alias isOpen_of_finite_disjoint_closed_cover_piece :=
  StacksTag09NE.isOpen_of_finite_disjoint_closed_cover_piece

/-- A finite family of closed immersions with disjoint images that cover a scheme is a
coproduct presentation. -/
private lemma isIso_sigmaDesc_of_disjointClosedCover {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdisjoint : Pairwise (Function.onFun Disjoint (fun i => Set.range ⇑(f i))))
    (hcover : ∀ x : X, ∃ i z, f i z = x) : IsIso (Limits.Sigma.desc f) := by
  have hclosed : ∀ i, IsClosed (Set.range ⇑(f i)) := fun i =>
    (f i).isClosedEmbedding.isClosed_range
  have hcover' : (⋃ i, Set.range ⇑(f i)) = Set.univ := Set.iUnion_eq_univ_iff.mpr hcover
  have hopen : ∀ i, IsOpen (Set.range ⇑(f i)) := fun i =>
    isOpen_of_finite_disjoint_closed_cover_piece (fun i => Set.range ⇑(f i))
      hclosed hdisjoint hcover' i
  have (i : ι) : IsOpenImmersion (f i) :=
    isOpenImmersion_of_closedImmersion_of_open_range (f i) (hopen i)
  exact isIso_sigmaDesc_of_disjointOpenCover Z f hdisjoint hcover

/-- Away from the overlap locus, the restrictions of the closed cover pieces are a disjoint
closed cover, hence form a scheme coproduct. -/
private lemma isIso_sigmaDesc_restrict_complement_overlap {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x) :
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (Limits.Sigma.desc (fun i => f i ∣_ U)) := by
  let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i => Set.range ⇑(f i ∣_ U))) := by
    intro i j hij
    change Disjoint (Set.range ⇑(f i ∣_ U)) (Set.range ⇑(f j ∣_ U))
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨yi, hyi⟩ := hxi
    obtain ⟨yj, hyj⟩ := hxj
    have hxi_val : (f i) yi.1 = x.1 := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hyi
    have hval : (f i) yi.1 = (f j) yj.1 := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val (hyi.trans hyj.symm)
    refine (show (x.1 : X) ∉ overlapLocus X Z f from x.2) ?_
    rw [← hxi_val]
    exact mem_overlapLocus X Z f hij hval
  have hcoverU : ∀ x : U, ∃ i z, (f i ∣_ U) z = x := by
    intro x
    obtain ⟨i, z, hz⟩ := hcover x.1
    have hzU : (f i) z ∈ U := hz ▸ x.2
    exact ⟨i, ⟨z, hzU⟩, Subtype.ext ((morphismRestrict_base_coe (f i) U ⟨z, hzU⟩).trans hz)⟩
  have : IsReduced U.toScheme := inferInstance
  exact isIso_sigmaDesc_of_disjointClosedCover
    (fun i => (f i ⁻¹ᵁ U).toScheme) (fun i => f i ∣_ U) hdisjoint hcoverU

/-- Every point of a scheme coproduct lies in one of its summands. -/
private alias exists_component_point_of_sigma := StacksTag09NE.exists_component_point_of_sigma

/-- Restriction commutes with the finite coproduct presentation over the complement of the
overlap locus. -/
private lemma isIso_sigmaDesc_morphismRestrict_complement_overlap {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x) :
    let g := Limits.Sigma.desc f
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (g ∣_ U) := by
  classical
  dsimp only
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  let W : (∐ Z).Opens := g ⁻¹ᵁ U
  have hsub (i : ι) :
      Set.range ⇑((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⊆ Set.range ⇑W.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι z), ?_⟩, rfl⟩
    change (Limits.Sigma.ι Z i ≫ Limits.Sigma.desc f) ((f i ⁻¹ᵁ U).ι z) ∈ U
    rw [Limits.Sigma.ι_comp_desc]
    exact z.2
  let kf : ∀ i, (f i ⁻¹ᵁ U).toScheme ⟶ W.toScheme := fun i =>
    IsOpenImmersion.lift W.ι ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) (hsub i)
  have hfac (i : ι) : kf i ≫ W.ι = (f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i :=
    IsOpenImmersion.lift_fac W.ι _ (hsub i)
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i => Set.range ⇑(kf i))) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨yi, hyi⟩ ⟨yj, hyj⟩
    have hEq : Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι yi) =
        Limits.Sigma.ι Z j ((f j ⁻¹ᵁ U).ι yj) :=
      calc
        Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι yi) = W.ι (kf i yi) := by
          simpa using (congrArg (fun q => q.base yi) (hfac i)).symm
        _ = W.ι (kf j yj) := congrArg W.ι (hyi.trans hyj.symm)
        _ = Limits.Sigma.ι Z j ((f j ⁻¹ᵁ U).ι yj) := by
          simpa using congrArg (fun q => q.base yj) (hfac j)
    exact hij (congrArg Sigma.fst
      ((sigmaι_eq_iff Z i j ((f i ⁻¹ᵁ U).ι yi) ((f j ⁻¹ᵁ U).ι yj)).mp hEq))
  have hcoverW : ∀ x : W.toScheme, ∃ i z, kf i z = x := by
    intro x
    obtain ⟨i, z, hpoint⟩ := exists_component_point_of_sigma Z (W.ι x)
    have hzU : z ∈ f i ⁻¹ᵁ U := by
      change f i z ∈ U
      have hval : f i z = g (W.ι x) := by
        rw [← hpoint]
        change f i z = (Limits.Sigma.ι Z i ≫ g) z
        rw [Limits.Sigma.ι_comp_desc]
      exact hval ▸ x.2
    refine ⟨i, ⟨z, hzU⟩, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    calc
      W.ι (kf i ⟨z, hzU⟩) = (kf i ≫ W.ι) ⟨z, hzU⟩ := rfl
      _ = ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⟨z, hzU⟩ :=
        congrArg (fun q => q ⟨z, hzU⟩) (hfac i)
      _ = Limits.Sigma.ι Z i z := by
        change Limits.Sigma.ι Z i (((f i ⁻¹ᵁ U).ι ⟨z, hzU⟩)) = _
        simp
      _ = W.ι x := hpoint
  have hopenComp (i : ι) : IsOpenImmersion
      ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) := inferInstance
  have (i : ι) : IsOpenImmersion (kf i) := inferInstance
  have hk : IsIso (Limits.Sigma.desc kf) :=
    isIso_sigmaDesc_of_disjointOpenCover (fun i => (f i ⁻¹ᵁ U).toScheme) kf
      hdisjoint hcoverW
  have hh : IsIso (Limits.Sigma.desc (fun i => f i ∣_ U)) :=
    isIso_sigmaDesc_restrict_complement_overlap Z f hcover
  have hcomponent (i : ι) : kf i ≫ g ∣_ U = f i ∣_ U := by
    apply (cancel_mono U.ι).1
    calc
      (kf i ≫ g ∣_ U) ≫ U.ι = kf i ≫ (g ∣_ U ≫ U.ι) := by rw [Category.assoc]
      _ = kf i ≫ (W.ι ≫ g) := by rw [morphismRestrict_ι]
      _ = (kf i ≫ W.ι) ≫ g := by rw [Category.assoc]
      _ = ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ≫ g := by rw [hfac]
      _ = (f i ⁻¹ᵁ U).ι ≫ (Limits.Sigma.ι Z i ≫ g) := by rw [Category.assoc]
      _ = (f i ⁻¹ᵁ U).ι ≫ f i := by
        change (f i ⁻¹ᵁ U).ι ≫ (Limits.Sigma.ι Z i ≫ Limits.Sigma.desc f) = _
        rw [Limits.Sigma.ι_comp_desc]
      _ = (f i ∣_ U) ≫ U.ι := (morphismRestrict_ι (f i) U).symm
  have hcomp : Limits.Sigma.desc kf ≫ g ∣_ U =
      Limits.Sigma.desc (fun i => f i ∣_ U) := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc]
    exact hcomponent i
  have hresult : g ∣_ U = inv (Limits.Sigma.desc kf) ≫
      Limits.Sigma.desc (fun i => f i ∣_ U) := by
    rw [← hcomp]
    simp
  have : IsIso (g ∣_ U) := hresult ▸ (inferInstance : IsIso
    (inv (Limits.Sigma.desc kf) ≫ Limits.Sigma.desc (fun i => f i ∣_ U)))
  infer_instance

/-- On a scheme coproduct the component modules combine by extension by zero on each
open-and-closed summand. -/
private noncomputable def pullback_pushforward_self {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M) ≅ M :=
  ((Scheme.Modules.restrictFunctorIsoPullback f).app
      ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso f).app M

private alias subsingleton_module_of_subsingleton_ring :=
  StacksTag09NE.subsingleton_module_of_subsingleton_ring

private alias restrict_pushforward_isZero_of_disjoint :=
  StacksTag09NE.restrict_pushforward_isZero_of_disjoint

private alias moduleOnSchemeSigma := StacksTag09NE.moduleOnSchemeSigma

private noncomputable def pullback_moduleOnSchemeSigma {ι : Type v} [Finite ι]
    [Small.{u} ι] (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules) (i : ι) :
    (Scheme.Modules.pullback (Limits.Sigma.ι Z i)).obj (moduleOnSchemeSigma Z L) ≅ L i := by
  classical
  let A : ι → (∐ Z).Modules := fun j =>
    (Scheme.Modules.pushforward (Limits.Sigma.ι Z j)).obj (L j)
  let F := Scheme.Modules.pullback (Limits.Sigma.ι Z i)
  let B : ι → (Z i).Modules := fun j => F.obj (A j)
  have hdisjoint (j k : ι) (hjk : j ≠ k) :
      Disjoint (Set.range ⇑(Limits.Sigma.ι Z j)) (Set.range ⇑(Limits.Sigma.ι Z k)) := by
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨yj, rfl⟩ ⟨yk, hyk⟩
    exact hjk (congrArg Sigma.fst ((sigmaι_eq_iff Z j k yj yk).mp hyk.symm))
  have hzero (j : ι) (hji : j ≠ i) : Limits.IsZero (B j) :=
    Limits.IsZero.of_iso (restrict_pushforward_isZero_of_disjoint (Limits.Sigma.ι Z i)
      (Limits.Sigma.ι Z j) (hdisjoint i j (Ne.symm hji)) (L j))
      ((Scheme.Modules.restrictFunctorIsoPullback (Limits.Sigma.ι Z i)).app (A j)).symm
  let eSelf : B i ≅ L i := pullback_pushforward_self (Limits.Sigma.ι Z i) (L i)
  let inj : ∀ j, B j ⟶ L i := fun j => if hji : j = i then
    eqToHom (by subst j; rfl) ≫ eSelf.hom else (hzero j hji).to_ (L i)
  let hpres := preservesColimitIso F (Discrete.functor A)
  let D := Discrete.functor A ⋙ F
  let c' : Cocone D := Cocone.mk (L i) (Discrete.natTrans fun j => inj j.as)
  have hc' : IsColimit c' := by
    refine IsColimit.mk (fun s => eSelf.inv ≫ s.ι.app ⟨i⟩) ?_ ?_
    · intro s j
      by_cases hji : j.as = i
      · have hj : j = ⟨i⟩ := Discrete.ext hji
        subst j
        simp [c', inj, eSelf]
      · exact (hzero j.as hji).eq_of_src _ _
    · intro s m hm
      have hmi : eSelf.hom ≫ m = s.ι.app ⟨i⟩ := by
        simpa [c', inj, eSelf] using hm ⟨i⟩
      rw [← Iso.inv_hom_id_assoc eSelf m, hmi]
  exact hpres ≪≫ (IsColimit.coconePointUniqueUpToIso hc' (colimit.isColimit D)).symm

/-- The module assembled on the coproduct of the cover is trivial near every point: a point
of the coproduct lies in one summand, where the module restricts to the invertible sheaf
given on that member of the cover. -/
private lemma moduleOnSchemeSigma_exists_restrict_iso_unit
    {ι : Type v} [Finite ι] [Small.{u} ι]
    (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules)
    [∀ i, IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (x : ↥(∐ Z)) :
    ∃ U : (∐ Z).Opens, x ∈ U ∧ Nonempty ((moduleOnSchemeSigma Z L).restrict U.ι ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) := by
  obtain ⟨i, y, hy⟩ := exists_component_point_of_sigma Z x
  obtain ⟨V, hyV, ⟨eV⟩⟩ :=
    (isInvertible_iff_exists_restrict_iso_unit (Z i) (L i)).mp inferInstance y
  let f := Limits.Sigma.ι Z i
  let U : (∐ Z).Opens := f ''ᵁ V
  let eImg := f.isoImage V
  let N := (moduleOnSchemeSigma Z L).restrict U.ι
  let GF := Scheme.Modules.restrictFunctor eImg.hom
  let GG := Scheme.Modules.restrictFunctor eImg.inv
  let eCompFiber : (Scheme.Modules.restrictFunctor f).obj
      (moduleOnSchemeSigma Z L) ≅ L i :=
    (Scheme.Modules.restrictFunctorIsoPullback f).app (moduleOnSchemeSigma Z L) ≪≫
      pullback_moduleOnSchemeSigma Z L i
  let eComp : (Scheme.Modules.restrictFunctor (V.ι ≫ f)).obj
      (moduleOnSchemeSigma Z L) ≅ (L i).restrict V.ι :=
    (Scheme.Modules.restrictFunctorComp V.ι f).app (moduleOnSchemeSigma Z L) ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso eCompFiber
  have hEq : eImg.hom ≫ U.ι = V.ι ≫ f := Scheme.Hom.isoImage_hom_ι f V
  let eToComp : GF.obj N ≅ (L i).restrict V.ι :=
    ((Scheme.Modules.restrictFunctorComp eImg.hom U.ι).app (moduleOnSchemeSigma Z L)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hEq).app (moduleOnSchemeSigma Z L) ≪≫
      eComp
  let eRound : N ≅ GG.obj (GF.obj N) :=
    ((Scheme.Modules.restrictFunctorId (X := U.toScheme)).app N).symm ≪≫
      ((Scheme.Modules.restrictFunctorCongr eImg.inv_hom_id).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorComp eImg.inv eImg.hom).app N
  exact ⟨U, by
    change x ∈ f '' V
    exact ⟨y, hyV, hy⟩,
    ⟨eRound ≪≫ GG.mapIso (eToComp ≪≫ eV) ≪≫
      Scheme.Modules.restrictUnitIso eImg.inv⟩⟩

/-- Invertible sheaves on a finite closed cover of a reduced scheme extend when
pairwise intersections are discrete. -/
@[stacks 09NE "existence of an invertible sheaf"]
public theorem exists_invertible_of_closed_cover_discrete_intersections
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X]
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    (L : ∀ i, (Z i).Modules)
    [∀ i, IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)] :
    ∃ (M : X.Modules)
      (_ : IsInvertible X.presheaf X.ringCatSheaf.2 M),
      ∀ i, Nonempty ((modulePullback (f i).toLRSHom.toShHom).obj M ≅ L i) := by
  classical
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let U : X.Opens :=
    ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  let Lcop : (∐ Z).Modules := moduleOnSchemeSigma Z L
  have hLcop : IsInvertible (∐ Z).presheaf (∐ Z).ringCatSheaf.2 Lcop :=
    (isInvertible_iff_exists_restrict_iso_unit (∐ Z) Lcop).mpr
      (moduleOnSchemeSigma_exists_restrict_iso_unit Z L)
  have : IsFinite g := inferInstance
  have : IsIso (g ∣_ U) := isIso_sigmaDesc_morphismRestrict_complement_overlap Z f hcover
  have : DiscreteTopology (Uᶜ : Set X) := overlapComplement_discrete X Z f hdiscrete
  obtain ⟨M, hM, ⟨eM⟩⟩ :=
    Stacks.PicFinite.exists_isInvertible_modulePullback_iso g U Lcop hLcop
  refine ⟨M, hM, fun i => ?_⟩
  have hdesc : Limits.Sigma.ι Z i ≫ g = f i := Limits.Sigma.ι_comp_desc f i
  let eEq : (Scheme.Modules.pullback (Limits.Sigma.ι Z i ≫ g)).obj M ≅
      (Scheme.Modules.pullback (f i)).obj M :=
    eqToIso (congrArg (fun q => (Scheme.Modules.pullback q).obj M) hdesc)
  let eComp := (Scheme.Modules.pullbackComp (Limits.Sigma.ι Z i) g).app M
  exact ⟨eEq.symm.trans (eComp.symm.trans
    (((Scheme.Modules.pullback (Limits.Sigma.ι Z i)).mapIso eM).trans
      (pullback_moduleOnSchemeSigma Z L i)))⟩


private alias restrictFunctor_preservesLimits := StacksTag09NE.restrictFunctor_preservesLimits

@[reducible] private alias replaceOnOpen := StacksTag09NE.replaceOnOpen

private noncomputable def replaceOnOpenLift {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) : F ⟶ replaceOnOpen a W :=
  pullback.lift a ((Scheme.Modules.restrictAdjunction W.ι).unit.app F)
    ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality a)

private lemma replaceOnOpenLift_fst {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    replaceOnOpenLift a W ≫ pullback.fst _ _ = a := pullback.lift_fst ..

private lemma replaceOnOpenLift_snd {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    replaceOnOpenLift a W ≫ pullback.snd _ _ =
      (Scheme.Modules.restrictAdjunction W.ι).unit.app F := pullback.lift_snd ..

private lemma isIso_restrict_replaceOnOpenLift {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (replaceOnOpenLift a W)) := by
  let R := Scheme.Modules.restrictFunctor W.ι
  let adj := Scheme.Modules.restrictAdjunction W.ι
  have : PreservesLimits R := restrictFunctor_preservesLimits W.ι
  have hunit (N : X.Modules) : IsIso (R.map (adj.unit.app N)) := by
    dsimp only [R, adj]
    let b := (Scheme.Modules.restrictAdjunction W.ι).counit.app
      ((Scheme.Modules.restrictFunctor W.ι).obj N)
    have hb : IsIso b := inferInstance
    have ht : (Scheme.Modules.restrictFunctor W.ι).map
        ((Scheme.Modules.restrictAdjunction W.ι).unit.app N) ≫ b = 𝟙 _ :=
      (Scheme.Modules.restrictAdjunction W.ι).left_triangle_components N
    refine ⟨⟨b, ht, ?_⟩⟩
    apply (cancel_mono b).mp
    simp only [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have hsnd : IsIso (R.map (pullback.snd (adj.unit.app G)
      ((R ⋙ Scheme.Modules.pushforward W.ι).map a))) :=
    (R.map_isPullback (IsPullback.of_hasPullback _ _)).isIso_snd_of_isIso
  have heq : R.map (replaceOnOpenLift a W) ≫ R.map (pullback.snd _ _) =
      R.map (adj.unit.app F) := by
    rw [← R.map_comp, replaceOnOpenLift_snd]
  have hcomp : IsIso (R.map (replaceOnOpenLift a W) ≫ R.map (pullback.snd _ _)) := by
    rw [heq]
    infer_instance
  have hlift : R.map (replaceOnOpenLift a W) =
      R.map (adj.unit.app F) ≫ inv (R.map (pullback.snd _ _)) := by
    apply (cancel_mono (R.map (pullback.snd _ _))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, heq]
  rw [hlift]
  infer_instance

private alias isIso_over_iff_app := StacksTag09NE.isIso_over_iff_app

private alias isIso_restrict_pushforward_restrict_map :=
  StacksTag09NE.isIso_restrict_pushforward_restrict_map

private alias isIso_restrict_replaceOnOpen_fst := StacksTag09NE.isIso_restrict_replaceOnOpen_fst

/-- Restricting an isomorphism to a smaller open gives an isomorphism. -/
private lemma isIso_over_of_le {Y : Scheme.{u}} {F G : Y.Modules} (φ : F ⟶ G)
    {U V : Y.Opens} (hUV : U ≤ V) [hV : IsIso (φ.over V)] : IsIso (φ.over U) :=
  (isIso_over_iff_app φ U).mpr fun W hW =>
    (isIso_over_iff_app φ V).mp hV W (hW.trans hUV)

/-- The complement of the images of the zero loci is an ambient open on which all
prescribed sections trivialize their respective sheaves. -/
private lemma exists_open_all_sections_trivial
    {ι : Type v} [Finite ι] (X : Scheme.{u}) (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (L : ∀ i, (Z i).Modules)
    [∀ i, IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.NonvanishingTrivialize.nonvanishingLocus (Z i).toRingedSpace (L i) (s i)) :
    ∃ W : X.Opens, overlapLocus X Z f ⊆ W ∧
      ∀ i, IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W)) := by
  have (i : ι) : IsInvertible (Z i).sheaf.obj
      (Z i).ringCatSheaf.property (L i) := by
    change IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)
    infer_instance
  let V (i : ι) : (Z i).Opens :=
    Stacks.NonvanishingTrivialize.nonvanishingOpen (Z i).toRingedSpace (L i) (s i)
  let C : Set X := ⋃ i, f i '' (V i : Set (Z i))ᶜ
  have hC : IsClosed C :=
    isClosed_iUnion_of_finite fun i =>
      (f i).isClosedEmbedding.isClosedMap _ (V i).isOpen.isClosed_compl
  let W : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  refine ⟨W, ?_, fun i => ?_⟩
  · intro x hx hxC
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hxC
    exact hz (nonvanishing_of_mem_overlap X Z f L s hs hx)
  · have hWV : f i ⁻¹ᵁ W ≤ V i := by
      intro z hz
      by_contra hzV
      exact hz (Set.mem_iUnion.mpr ⟨i, z, hzV, rfl⟩)
    have : IsIso (((L i).unitHomEquiv.symm (s i)).over (V i)) :=
      Stacks.NonvanishingTrivialize.isIso_over_nonvanishingOpen
        (X := (Z i).toRingedSpace) (L := L i) (s i)
    exact isIso_over_of_le _ hWV


private noncomputable def pullbackRestrictIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f ∣_ U))

private alias isIso_restrict_pullback_map := StacksTag09NE.isIso_restrict_pullback_map

/-- The pushforward of sheaves of modules along the map of structure sheaves underlying a
morphism of schemes has a left adjoint. This is `Scheme.Modules.pushforward`, whose adjoint
is recorded in the library at the spelling `Scheme.Modules.pullback`; stating it again at the
unfolded spelling makes the adjoint available to declarations such as
`SheafOfModules.pullbackObjUnitToUnit`, which are phrased in terms of the map of sheaves of
rings rather than of the morphism of schemes. -/
private instance pushforwardRingCatSheafHom_isRightAdjoint {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Functor.IsRightAdjoint.{u, u, u + 1, u + 1}
      (SheafOfModules.pushforward f.toRingCatSheafHom) :=
  have : (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  SheafOfModules.instIsRightAdjointPushforward f.toRingCatSheafHom

/-- A composite of isomorphisms is an isomorphism. The two factors are arguments rather than
instances, so that the ambient category is passed as a term. -/
private theorem isIso_comp_of {C : Type*} [Category C] {A B D : C} {g : A ⟶ B} {h : B ⟶ D}
    (hg : IsIso g) (hh : IsIso h) : IsIso (g ≫ h) :=
  have := hg
  have := hh
  inferInstance

/-- A morphism whose composite with an isomorphism is an isomorphism is itself an
isomorphism. Both isomorphisms are arguments rather than instances, so that the ambient
category is passed as a term. -/
private theorem isIso_of_comp_right {C : Type*} [Category C] {A B D : C} {g : A ⟶ B}
    {h : B ⟶ D} (hh : IsIso h) (hgh : IsIso (g ≫ h)) : IsIso g :=
  have := hh
  (isIso_comp_right_iff g h).mp hgh

/-- A functor carries an isomorphism to an isomorphism. The isomorphism is an argument rather
than an instance, so that the ambient categories are passed as terms. -/
private theorem isIso_map_of {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B : C}
    {g : A ⟶ B} (hg : IsIso g) : IsIso (F.map g) :=
  have := hg
  inferInstance

private alias opens_map_final := StacksTag09NE.opens_map_final

private lemma isIso_pullbackUnit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
  have := opens_map_final f
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom

private alias isIso_restrict_iff_over := StacksTag09NE.isIso_restrict_iff_over

/-- The map from the structure sheaf picking out the direct image of a section of `L` is the
comparison of structure sheaves followed by the direct image of the map picking out that
section. -/
private alias unitHomEquiv_symm_pushforwardSections :=
  StacksTag09NE.unitHomEquiv_symm_pushforwardSections

private alias pullback_section_comp_adjoint := StacksTag09NE.pullback_section_comp_adjoint

private alias isIso_restrict_adjoint_of_section := StacksTag09NE.isIso_restrict_adjoint_of_section

private noncomputable abbrev closedCoverModule {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) : X.Modules :=
  ∏ᶜ fun i => (Scheme.Modules.pushforward (f i)).obj (L i)

private noncomputable def closedCoverSection {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) :
    SheafOfModules.unit X.ringCatSheaf ⟶ closedCoverModule Z f L :=
  Pi.lift (f := fun j => (Scheme.Modules.pushforward (f j)).obj (L j))
    fun i => ((Scheme.Modules.pushforward (f i)).obj (L i)).unitHomEquiv.symm
      (SheafOfModules.pushforwardSections (f i).toRingCatSheafHom (s i))

/-- The `i`-th component of `closedCoverSection` is the direct image of the `i`-th prescribed
section. -/
private lemma closedCoverSection_pi {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (i : ι) :
    closedCoverSection Z f L s ≫
        Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i =
      ((Scheme.Modules.pushforward (f i)).obj (L i)).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections (f i).toRingCatSheafHom (s i)) :=
  Pi.lift_comp_π (f := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) _ i

private alias adjoint_section_eq := StacksTag09NE.adjoint_section_eq

/-- The sheaf obtained by replacing the product of the direct images by the unit
sheaf on an open where the prescribed sections do not vanish. -/
private noncomputable abbrev patchedClosedCoverModule {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) : X.Modules :=
  replaceOnOpen (closedCoverSection Z f L s) W

/-- The prescribed sections give a section of the patched sheaf. -/
private noncomputable def patchedClosedCoverSection {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) :
    (patchedClosedCoverModule Z f L s W).sections :=
  (patchedClosedCoverModule Z f L s W).unitHomEquiv
    (replaceOnOpenLift (closedCoverSection Z f L s) W)

/-- Projection to a component, expressed as a morphism from the pullback. -/
private noncomputable def patchedClosedCoverComparison {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (patchedClosedCoverModule Z f L s W) ⟶ L i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (f i)).homEquiv _ _).symm
    (pullback.fst _ _ ≫ Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i)

/-- The patched lift followed by the projection to the `i`-th component is the direct image of
the `i`-th prescribed section. -/
private lemma replaceOnOpenLift_comp_pi {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    replaceOnOpenLift (closedCoverSection Z f L s) W ≫
        (pullback.fst _ _ ≫ Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i) =
      ((Scheme.Modules.pushforward (f i)).obj (L i)).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections (f i).toRingCatSheafHom (s i)) :=
  ((Category.assoc _ _ _).symm.trans
    (eq_whisker (replaceOnOpenLift_fst (closedCoverSection Z f L s) W) _)).trans
      (closedCoverSection_pi Z f L s i)

/-- The component comparisons carry the patched section to the prescribed sections. -/
private lemma patchedClosedCoverComparison_section {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    (patchedClosedCoverComparison Z f L s W i).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f i)).unit.app
        (patchedClosedCoverModule Z f L s W)).val.app (op ⊤)
          ((patchedClosedCoverSection Z f L s W).eval (op ⊤))) = (s i).eval (op ⊤) := by
  exact adjoint_section_eq _ _ _ _ _ _ (replaceOnOpenLift_comp_pi Z f L s W i)

/-- The patched sheaf is trivial on the replacement open, with its patched section
as the chosen basis. -/
private noncomputable def patchedClosedCoverModule_restrictIsoUnit
    {ι : Type v} [Finite ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (s : ∀ i, (L i).sections) (W : X.Opens) :
    (patchedClosedCoverModule Z f L s W).restrict W.ι ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf := by
  have := isIso_restrict_replaceOnOpenLift (closedCoverSection Z f L s) W
  exact (asIso ((Scheme.Modules.restrictFunctor W.ι).map
    (replaceOnOpenLift (closedCoverSection Z f L s) W))).symm ≪≫
      Scheme.Modules.restrictUnitIso W.ι

/-- The comparison with each component is an isomorphism over the common
nonvanishing open. -/
private lemma patchedClosedCoverComparison_isIso_restrict
    {ι : Type v} [Finite ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ W).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
  have := isIso_restrict_replaceOnOpenLift (closedCoverSection Z f L s) W
  apply isIso_restrict_adjoint_of_section (f i) _ (L i)
    (replaceOnOpenLift (closedCoverSection Z f L s) W) _ (s i) _ W
  exact replaceOnOpenLift_comp_pi Z f L s W i

/-- Isomorphisms of sheaves of modules can be checked in neighborhoods of points. -/
private alias isIso_of_pointwise_restrict := StacksTag09NE.isIso_of_pointwise_restrict

private alias module_isZero_of_sections_subsingleton :=
  StacksTag09NE.module_isZero_of_sections_subsingleton

private alias restrict_pushforward_isZero_of_preimage_eq_bot :=
  StacksTag09NE.restrict_pushforward_isZero_of_preimage_eq_bot

private alias isIso_map_pi_of_isZero := StacksTag09NE.isIso_map_pi_of_isZero

private alias adjoint_isIso_iff := StacksTag09NE.adjoint_isIso_iff

private alias isIso_restrict_adjoint_of_open_comp :=
  StacksTag09NE.isIso_restrict_adjoint_of_open_comp

private alias isIso_restrict_of_image_le := StacksTag09NE.isIso_restrict_of_image_le

private alias isIso_restrict_unitToPushforward := StacksTag09NE.isIso_restrict_unitToPushforward

/-- Over an open meeting only the `i`-th piece, the projection from the product of the direct
images to the `i`-th one is an isomorphism after restriction. -/
private lemma isIso_restrict_pi_of_preimage_eq_bot {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (i : ι) (U : X.Opens) (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i)) := by
  have : PreservesLimits (Scheme.Modules.restrictFunctor U.ι) :=
    restrictFunctor_preservesLimits U.ι
  exact isIso_map_pi_of_isZero _ _ i fun j hj =>
    restrict_pushforward_isZero_of_preimage_eq_bot (f j) U (hzero j hj) (L j)

private lemma isIso_closedCoverSection_over {ι : Type v} [Finite ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections)
    (i : ι) (U W : X.Opens) [IsIso (f i ∣_ U)]
    (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((closedCoverSection Z f L s).over (U ⊓ W)) := by
  let A : ι → X.Modules := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)
  have hp := isIso_restrict_pi_of_preimage_eq_bot Z f L i U hzero
  have hp' : IsIso ((Pi.π A i).over (U ⊓ W)) := by
    have := (isIso_restrict_iff_over _ _).mp hp
    exact isIso_over_of_le _ inf_le_left
  have hu := isIso_restrict_unitToPushforward (f i) U
  have hu' : IsIso ((SheafOfModules.unitToPushforwardObjUnit
      (f i).toRingCatSheafHom).over (U ⊓ W)) := by
    have := (isIso_restrict_iff_over _ _).mp hu
    exact isIso_over_of_le _ inf_le_left
  have hs' : IsIso (((Scheme.Modules.pushforward (f i)).map
      ((L i).unitHomEquiv.symm (s i))).over (U ⊓ W)) := by
    refine (isIso_over_iff_app _ _).mpr fun V hV => ?_
    apply (isIso_over_iff_app ((L i).unitHomEquiv.symm (s i)) (f i ⁻¹ᵁ W)).mp
      inferInstance
    exact Scheme.Hom.preimage_mono _ (hV.trans inf_le_right)
  have he : closedCoverSection Z f L s ≫ Pi.π A i =
      SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (f i)).map ((L i).unitHomEquiv.symm (s i)) :=
    (closedCoverSection_pi Z f L s i).trans
      (unitHomEquiv_symm_pushforwardSections (f i) (L i) (s i))
  have he' := congrArg (fun a => a.over (U ⊓ W)) he
  change (closedCoverSection Z f L s).over (U ⊓ W) ≫ (Pi.π A i).over (U ⊓ W) =
    (SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom).over (U ⊓ W) ≫
      ((Scheme.Modules.pushforward (f i)).map
        ((L i).unitHomEquiv.symm (s i))).over (U ⊓ W) at he'
  have hi : IsIso ((closedCoverSection Z f L s).over (U ⊓ W) ≫
      (Pi.π A i).over (U ⊓ W)) :=
    Eq.mpr (congrArg (fun q => IsIso q) he') (isIso_comp_of hu' hs')
  exact (isIso_comp_right_iff _ _).mp hi

/-- Over an open on which a morphism restricts to an isomorphism, the inclusion composed with
the morphism is an open immersion. -/
private lemma isOpenImmersion_preimage_ι_comp {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  infer_instance

private lemma patchedClosedCoverComparison_isIso_of_single_component
    {ι : Type v} [Finite ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W U : X.Opens) (i : ι)
    [IsIso (f i ∣_ U)] (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ U).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
  let A : ι → X.Modules := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)
  have hp := isIso_restrict_pi_of_preimage_eq_bot Z f L i U hzero
  have ha := isIso_closedCoverSection_over Z f L s i U W hzero
  have hf := isIso_restrict_replaceOnOpen_fst (closedCoverSection Z f L s) U W
  let b : patchedClosedCoverModule Z f L s W ⟶ (Scheme.Modules.pushforward (f i)).obj (L i) :=
    pullback.fst _ _ ≫ Pi.π A i
  have hb : IsIso ((Scheme.Modules.restrictFunctor U.ι).map b) := by
    dsimp only [b]
    rw [Functor.map_comp]
    infer_instance
  have hb' : IsIso (b.over U) := (isIso_restrict_iff_over _ _).mp hb
  let g := (f i ⁻¹ᵁ U).ι
  have : IsOpenImmersion (g ≫ f i) := isOpenImmersion_preimage_ι_comp (f i) U
  have : IsIso ((Scheme.Modules.restrictFunctor (g ≫ f i)).map b) :=
    isIso_restrict_of_image_le b _ U (Set.range_subset_iff.mpr fun y => y.2)
  exact isIso_restrict_adjoint_of_open_comp (f i) g
    (f i).isClosedEmbedding.injective _ (L i) b

private lemma exists_trivialization_of_local_comparison {X Y T : Scheme.{u}}
    (k : T ⟶ X) (g : T ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion g]
    (M : X.Modules) (L : Y.Modules)
    [IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (e : M.restrict k ≅ L.restrict g) (z : T) :
    ∃ U : X.Opens, k z ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨V₀, hz, ⟨eL⟩⟩ :=
    (isInvertible_iff_exists_restrict_iso_unit Y L).mp inferInstance (g z)
  let V := g ⁻¹ᵁ V₀
  let h := g ∣_ V₀
  let eS : (L.restrict g).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorComp V.ι g).app L).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι g V₀).symm).app L ≪≫
      (Scheme.Modules.restrictFunctorComp h V₀.ι).app L ≪≫
      (Scheme.Modules.restrictFunctor h).mapIso eL ≪≫ Scheme.Modules.restrictUnitIso h
  let l := V.ι ≫ k
  let el : M.restrict l ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorComp V.ι k).app M ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso e ≪≫ eS
  let U := l.opensRange
  let eU : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorCongr l.isoOpensRange_inv_comp).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp l.isoOpensRange.inv l).app M ≪≫
      (Scheme.Modules.restrictFunctor l.isoOpensRange.inv).mapIso el ≪≫
      Scheme.Modules.restrictUnitIso l.isoOpensRange.inv
  exact ⟨U, ⟨⟨z, hz⟩, rfl⟩, ⟨eU⟩⟩

/-- Sections nonvanishing along the pairwise intersections can be glued along
with the invertible sheaves. -/
@[stacks 09NE "existence with prescribed sections"]
public theorem exists_invertible_with_sections_of_closed_cover_discrete_intersections
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X]
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (_hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    (L : ∀ i, (Z i).Modules)
    [∀ i, IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.NonvanishingTrivialize.nonvanishingLocus (Z i).toRingedSpace (L i) (s i)) :
    ∃ (M : X.Modules)
      (_ : IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (t : M.sections),
      ∀ i, ∃ e : (modulePullback (f i).toLRSHom.toShHom).obj M ≅ L i,
        e.hom.val.app (op ⊤)
          (((modulePullbackPushforwardAdjunction (f i).toLRSHom.toShHom).unit.app M).val.app
            (op ⊤) (t.eval (op ⊤))) = (s i).eval (op ⊤) := by
  classical
  obtain ⟨W, hW, htrivial⟩ := exists_open_all_sections_trivial X Z f L s hs
  let M := patchedClosedCoverModule Z f L s W
  let t := patchedClosedCoverSection Z f L s W
  have hWiso (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ W).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
    have := htrivial i
    exact patchedClosedCoverComparison_isIso_restrict Z f L s W i
  have hcomparison (i : ι) : IsIso (patchedClosedCoverComparison Z f L s W i) := by
    refine isIso_of_pointwise_restrict _ fun z => ?_
    by_cases hz : f i z ∈ W
    · exact ⟨f i ⁻¹ᵁ W, hz, hWiso i⟩
    · obtain ⟨j, U, hxU, hj, hzero⟩ :=
        exists_open_neighborhood_isIso_component_of_not_overlap X Z f hcover
          (fun h => hz (hW h))
      have he : i = j := by
        by_contra hij
        have hzi : z ∈ f i ⁻¹ᵁ U := hxU
        rw [hzero i hij] at hzi
        exact hzi
      subst j
      have := htrivial i
      exact ⟨f i ⁻¹ᵁ U, hxU,
        patchedClosedCoverComparison_isIso_of_single_component Z f L s W U i hzero⟩
  have hM : IsInvertible X.presheaf X.ringCatSheaf.2 M := by
    refine (isInvertible_iff_exists_restrict_iso_unit X M).mpr fun x => ?_
    by_cases hx : x ∈ W
    · exact ⟨W, hx, ⟨patchedClosedCoverModule_restrictIsoUnit Z f L s W⟩⟩
    · obtain ⟨i, U, hxU, hi, hzero⟩ :=
        exists_open_neighborhood_isIso_component_of_not_overlap X Z f hcover
          (fun h => hx (hW h))
      let g := (f i ⁻¹ᵁ U).ι
      let k := g ≫ f i
      have : IsOpenImmersion k := isOpenImmersion_preimage_ι_comp (f i) U
      let e : M.restrict k ≅ (L i).restrict g :=
        (Scheme.Modules.restrictFunctorIsoPullback k).app M ≪≫
          ((Scheme.Modules.pullbackComp g (f i)).app M).symm ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback g).app
            ((Scheme.Modules.pullback (f i)).obj M)).symm ≪≫
          (Scheme.Modules.restrictFunctor g).mapIso
            (asIso (patchedClosedCoverComparison Z f L s W i))
      obtain ⟨z, hz⟩ := (f i ∣_ U).surjective ⟨x, hxU⟩
      have hkz : k z = x :=
        (morphismRestrict_base_coe (f i) U z).symm.trans (congrArg U.ι hz)
      simpa only [hkz] using exists_trivialization_of_local_comparison k g M (L i) e z
  exact ⟨M, hM, t, fun i =>
    ⟨@asIso _ _ _ _ (patchedClosedCoverComparison Z f L s W i) (hcomparison i),
      patchedClosedCoverComparison_section Z f L s W i⟩⟩
end AlgebraicGeometry

end
