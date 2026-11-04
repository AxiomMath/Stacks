module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Lifting an invertible module across a closed immersion into a curve

Let `i : Z ⟶ X` be a closed immersion of schemes with `X` Noetherian of dimension at most one.
[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) asserts that every invertible
`𝒪_Z`-module is the pullback of an invertible `𝒪_X`-module, equivalently that
`Pic(X) → Pic(Z)` is surjective. The Stacks proof runs the long exact cohomology sequence of
`0 → (1 + ℐ) ∩ 𝒪_X^* → 𝒪_X^* → i_*𝒪_Z^* → 0`, using `H²(X, −) = 0` for a Noetherian space of
dimension at most one (Tag 02UZ) and the comparison `H¹(X, i_*𝒪_Z^*) = H¹(Z, 𝒪_Z^*)` along a
closed immersion (Tag 02UV). Neither of those is available here, and neither is the kernel
sheaf, so the tag itself is **not** proved in this file.

Two families of special cases are. The first is the case in which the closed immersion is
already an isomorphism away from a sufficiently small closed set: there the module descends by
the finite-morphism descent of [Stacks, Tag 0C0T], which is available, and the dimension
hypothesis enters only through the purely topological fact that the complement of such an open
is a finite set of closed points. The second is the case in which `Z` is a discrete space, where
every invertible module is globally trivial and one may take `M = 𝒪_X`; under the hypotheses of
Tag 09NY this covers `dim X ≤ 0`, and `dim X ≤ 1` with `Z` containing no irreducible component
of `X` — that is, `Z` a finite set of (possibly fat) points on a curve.

What is **not** covered is the case the cohomological argument is really for: `Z` a proper
closed subscheme meeting every irreducible component of `X` in a proper closed subset, for
instance the reduction of a nowhere reduced `X`, which is what Tag 09NZ consumes.

## Main results

* `Stacks.LiftInvertible.discreteTopology_compl_of_topologicalKrullDim_le_one`: in a Noetherian
  scheme of dimension at most one, the complement of an open set that meets every irreducible
  component is a discrete space.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_isIso_restrict` and
  `…_of_isIso_restrict_of_dimension_le_one`: **the conclusion of Tag 09NY when `i` is an
  isomorphism over an open `V`** whose complement is discrete, respectively contains no
  irreducible component of `X`.
* `Stacks.SheafOfModules.exists_sections_eval_eq_of_pairwise_disjoint`: a family of sections
  indexed by a pairwise disjoint open cover glues, with no compatibility hypothesis — the
  overlaps are empty. The `Pairwise`-disjoint companion of
  `Stacks.SheafOfModules.exists_sections_eval_eq`.
* `Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`: an invertible module on a
  scheme whose underlying space is discrete is isomorphic to the structure sheaf.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_nonempty_iso_unit`,
  `…_of_discreteTopology`, `…_of_topologicalKrullDim_le_zero` and
  `…_of_not_irreducibleComponent_subset_range`: the conclusion of Tag 09NY for a trivial `L`,
  for discrete `Z`, and the two instances of that under Tag 09NY's own hypotheses.

## Implementation notes

The two pullback functors `AlgebraicGeometry.Scheme.Modules.pullback f` and
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` are equal by `rfl`: the ring
sheaf spellings `AlgebraicGeometry.Scheme.ringCatSheaf` and
`structureSheafRing _.toRingedSpace` have the same underlying presheaf and
the sheaf condition is a proposition, and `f.toRingCatSheafHom` is
`RingedSpaceModuleAdjunction.structureSheafHom f.toLRSHom.toShHom`. So no comparison
isomorphism is needed and the statements below are literally in the spelling of Tag 09NY.

Invertibility is read through both of Tag 01CS's two classes: the statements take
`AlgebraicGeometry.SheafOfModules.IsInvertible`, which is what Tag 09NY asks for, and the
trivialization API speaks `Stacks.SheafOfModules.IsInvertible`; the crossing is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` and happens once, in
`exists_modulePullback_iso_of_discreteTopology`.

No `@[stacks 09NY]` attribute is attached to anything in this file: every statement here
carries a hypothesis that the tag does not have.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Set
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- **Sections over a pairwise disjoint open cover glue, unconditionally.** Any family of
sections of `L`, one over each member of a pairwise disjoint open cover, is the restriction of a
global section: the compatibility hypothesis of the sheaf condition is vacuous because two
distinct members meet in the empty open, where a sheaf has at most one section.

This is the `Pairwise`-disjoint companion of `Stacks.SheafOfModules.exists_sections_eval_eq`,
which glues two sections over a two-open cover at the price of their agreeing on the overlap. -/
theorem exists_sections_eval_eq_of_pairwise_disjoint {ι : Type*} (U : ι → Opens X.carrier)
    (hcover : IsOpenCover U) (hdisj : Pairwise (Function.onFun Disjoint U))
    (a : ∀ i, L.val.obj (op (U i))) :
    ∃ s : L.val.sections, ∀ i, s.eval (op (U i)) = a i := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat X.carrier :=
    ⟨L.val.presheaf, _root_.SheafOfModules.isSheaf L⟩
  have hc : TopCat.Presheaf.IsCompatible L.val.presheaf U a := by
    intro i j
    rcases eq_or_ne i j with rfl | h
    · rfl
    · refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) F (U i ⊓ U j) _ _ ?_
      intro y hy
      rw [disjoint_iff.mp (hdisj h)] at hy
      exact absurd hy (by simp)
  obtain ⟨g₀, hg, -⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top)
    (le_of_eq hcover.iSup_eq_top.symm) a hc
  let g : L.val.obj (op ⊤) := g₀
  have hg' : ∀ i, L.val.map (homOfLE (le_top (a := U i))).op g = a i := hg
  refine ⟨PresheafOfModules.sectionsMk
    (fun A => L.val.map (homOfLE (le_top (a := A.unop))).op g) ?_, hg'⟩
  intro A B f
  rw [← L.val.map_comp_apply]
  exact L.val.congr_map_apply (Subsingleton.elim _ _) g

/-- **An invertible module on a scheme with discrete underlying space is trivial.** Every point
is an open set, so clause 2 of [Stacks, Tag 0B8M] trivializes `L` on each point separately, and
the resulting sections glue over the pairwise disjoint cover by points. In particular the
Picard group of such a scheme vanishes.

No finiteness of the space is needed: the cover is indexed by the points. -/
theorem nonempty_iso_unit_of_discreteTopology (Z : Scheme.{u}) [DiscreteTopology (Z : Type u)]
    (M : _root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property M] :
    Nonempty (M ≅ _root_.SheafOfModules.unit (structureSheafRing Z.toRingedSpace)) := by
  classical
  have (z : Z.toRingedSpace.carrier) :
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z.toRingedSpace z) :=
    Z.isLocalRing z
  choose W hzW aW haW using fun z : Z.toRingedSpace.carrier =>
    exists_bijective_smul_of_isInvertible (X := Z.toRingedSpace) M z
  set U : Z.toRingedSpace.carrier → Opens Z.toRingedSpace.carrier :=
    fun z => ⟨{z}, isOpen_discrete _⟩ with hU
  have hUW : ∀ z, U z ≤ W z := fun z y (hy : y = z) => hy ▸ hzW z
  have hcover : IsOpenCover U := le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro z z' h
    simp only [Function.onFun]
    refine disjoint_iff.mpr ?_
    ext y
    simp only [Opens.coe_inf, Opens.coe_bot, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
      hU, Opens.coe_mk, Set.mem_singleton_iff, not_and]
    rintro rfl
    exact h
  obtain ⟨s, hs⟩ := exists_sections_eval_eq_of_pairwise_disjoint M U hcover hdisj
    (fun z => M.val.map (homOfLE (hUW z)).op (aW z))
  refine nonempty_iso_unit_of_bijective_smul_on_cover M s U hcover fun z V hV => ?_
  have hev : s.eval (op V) = M.val.map (homOfLE hV).op (s.eval (op (U z))) :=
    (PresheafOfModules.sections_property s (homOfLE hV).op).symm
  rw [hev, hs z, map_restrict_comp M hV (hUW z) (aW z)]
  exact haW z V (hV.trans (hUW z))

end Stacks.SheafOfModules

namespace Stacks.LiftInvertible

/-- **The dimension hypothesis of Tag 09NY, in topological form.** If `X` is a Noetherian scheme
of Krull dimension at most one and `V` is an open set whose complement contains no irreducible
component of `X`, then `Vᶜ` is a finite set of closed points, hence a discrete space.

Both halves come from `StacksFrontier/Topology/Dimension/DimensionLEOne.lean`: a closed set
containing no irreducible component of a space of dimension at most one consists of closed
points, and is finite when the space is Noetherian and sober. A scheme is `T0` and sober. -/
theorem discreteTopology_compl_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens)
    (hV : ∀ C ∈ irreducibleComponents (X : Type u), ¬ C ⊆ ((V : Set X)ᶜ)) :
    DiscreteTopology (((V : Set X)ᶜ) : Set X) := by
  have hT : IsClosed ((V : Set X)ᶜ) := V.isOpen.isClosed_compl
  have _ : Finite (((V : Set X)ᶜ) : Set X) :=
    (Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hT hV).to_subtype
  have _ : T1Space (((V : Set X)ᶜ) : Set X) := by
    refine ⟨fun x => ?_⟩
    have he : ({x} : Set (((V : Set X)ᶜ) : Set X))
        = Subtype.val ⁻¹' ({(x : X)} : Set X) := by
      ext y
      simp [Subtype.ext_iff]
    rw [he]
    exact (Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim hT hV x.2).preimage continuous_subtype_val
  infer_instance

/-- **Tag 09NY for a closed immersion that is an isomorphism off a discrete closed set.** If
`i : Z ⟶ X` is a closed immersion which is an isomorphism over an open `V` of `X` whose
complement is discrete, then every invertible `𝒪_Z`-module is the pullback of an invertible
`𝒪_X`-module.

This is `Stacks.PicFinite.exists_isInvertible_modulePullback_iso` (Tag 0C0T) — a closed
immersion is finite — read in the `RingedSpaceModuleAdjunction.modulePullback` spelling in which
Tag 09NY is stated. The two pullback functors are equal by `rfl`.

Neither Noetherianness nor the dimension bound of Tag 09NY is used; they enter only through
`Stacks.LiftInvertible.discreteTopology_compl_of_topologicalKrullDim_le_one`, which supplies
the discreteness. The tag is withheld: `IsIso (i ∣_ V)` is not a hypothesis of Tag 09NY. -/
theorem exists_modulePullback_iso_of_isIso_restrict (X Z : Scheme.{u}) (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.Opens) [IsIso (i ∣_ V)]
    [DiscreteTopology (((V : Set X)ᶜ) : Set X)]
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  let ⟨M, hM, hiso⟩ := Stacks.PicFinite.exists_isInvertible_modulePullback_iso i V L hL
  ⟨M, hM, hiso⟩

/-- **Tag 09NY for a closed immersion that is an isomorphism outside a set containing no
irreducible component.** The hypotheses of Tag 09NY — `X` Noetherian of dimension at most one —
together with an open `V` over which `i` is an isomorphism and whose complement contains no
irreducible component of `X`, suffice for the conclusion.

Geometrically: `Z` agrees with `X` away from finitely many closed points. The tag is withheld:
`IsIso (i ∣_ V)` and `hV` are not hypotheses of Tag 09NY. -/
theorem exists_modulePullback_iso_of_isIso_restrict_of_dimension_le_one (X Z : Scheme.{u})
    (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens) [IsIso (i ∣_ V)]
    (hV : ∀ C ∈ irreducibleComponents (X : Type u), ¬ C ⊆ ((V : Set X)ᶜ))
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  let := discreteTopology_compl_of_topologicalKrullDim_le_one X hdim V hV
  exists_modulePullback_iso_of_isIso_restrict X Z i V L

/-- **Tag 09NY for a trivial module**, with no hypothesis on `X`, `Z` or the morphism: if `L` is
isomorphic to `𝒪_Z` then it is the pullback of `𝒪_X`, which is invertible. The comparison is
`Stacks.StrictlyPerfect.Pullback.modulePullbackStructureModuleIso`, the statement that `f^*𝒪_X =
  𝒪_Z`. -/
theorem exists_modulePullback_iso_of_nonempty_iso_unit (X Z : Scheme.{u}) (i : Z ⟶ X)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : Nonempty (L ≅ SheafOfModules.unit (structureSheafRing Z.toRingedSpace))) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  ⟨SheafOfModules.unit (structureSheafRing X.toRingedSpace),
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Stacks.SheafOfModules.isInvertible_unit _ _),
    hL.map fun e =>
      Stacks.StrictlyPerfect.Pullback.modulePullbackStructureModuleIso i.toLRSHom.toShHom ≪≫ e.symm⟩

/-- **Tag 09NY for a closed subscheme with discrete underlying space**, with no hypothesis on
`X`: every invertible module on such a `Z` is trivial, so `𝒪_X` lifts it. -/
theorem exists_modulePullback_iso_of_discreteTopology (X Z : Scheme.{u}) (i : Z ⟶ X)
    [DiscreteTopology (Z : Type u)]
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  have _hL' : Stacks.SheafOfModules.IsInvertible Z.presheaf
      (structureSheafRing Z.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  exists_modulePullback_iso_of_nonempty_iso_unit X Z i L
    (Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology Z L)

/-- **Tag 09NY in dimension zero.** A Noetherian scheme of Krull dimension at most zero is a
finite discrete space, so a closed subscheme of it is discrete and every invertible module on it
is trivial. The tag is withheld: Tag 09NY allows dimension one. -/
theorem exists_modulePullback_iso_of_topologicalKrullDim_le_zero (X Z : Scheme.{u}) (i : Z ⟶ X)
    [IsClosedImmersion i] [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 0)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) := by
  have _ : Finite (X : Type u) := Set.finite_univ_iff.mp
    (Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero (X := (X : Type u)) hdim)
  have _ : T1Space (X : Type u) :=
    ⟨fun x => Stacks.Topology.Dimension.isClosed_singleton_of_topologicalKrullDim_le_zero hdim x⟩
  have _ : DiscreteTopology (Z : Type u) :=
    (IsClosedImmersion.isClosedEmbedding i).isEmbedding.discreteTopology
  exact exists_modulePullback_iso_of_discreteTopology X Z i L

/-- **Tag 09NY when `Z` contains no irreducible component of `X`.** Under the hypotheses of Tag
09NY, a closed subscheme whose underlying set contains no irreducible component of `X` is a
finite set of closed points — a finite collection of possibly fat points on a curve — hence a
discrete space, so every invertible module on it is trivial and `𝒪_X` lifts it.

This is the case in which the Picard group of `Z` vanishes. The complementary case, where `Z`
does contain a component, is the one that needs the cohomological argument. The tag is withheld:
`hZ` is not a hypothesis of Tag 09NY. -/
theorem exists_modulePullback_iso_of_not_irreducibleComponent_subset_range (X Z : Scheme.{u})
    (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hZ : ∀ C ∈ irreducibleComponents (X : Type u), ¬ C ⊆ Set.range i.base)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) := by
  have hemb := IsClosedImmersion.isClosedEmbedding i
  have hT : IsClosed (Set.range i.base) := hemb.isClosed_range
  have _ : Finite ↥(Set.range i.base) :=
    (Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hT hZ).to_subtype
  have _ : Finite (Z : Type u) := Finite.of_equiv _ (Equiv.ofInjective i.base hemb.injective).symm
  have _ : T1Space (Z : Type u) := by
    refine ⟨fun z => ?_⟩
    have he : ({z} : Set (Z : Type u)) = i.base ⁻¹' ({i.base z} : Set (X : Type u)) := by
      ext y
      simp [hemb.injective.eq_iff]
    rw [he]
    exact (Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim hT hZ (Set.mem_range_self z)).preimage hemb.continuous
  exact exists_modulePullback_iso_of_discreteTopology X Z i L

end Stacks.LiftInvertible

end
