module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SoftAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsOfCoeff
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The restriction of a flasque sheaf to a quasi-compact separated subset is soft

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points of
which have disjoint open neighbourhoods in `X`, and let `F` be a flasque sheaf of abelian groups
on `X`. This file proves that the restriction `F|_Z` — the inverse image of `F` along the
inclusion `Z → X` — is a soft sheaf on `Z`, and hence, `Z` being compact Hausdorff, is right
acyclic for global sections.

This gives the vanishing `H^p(Z, I|_Z) = 0` for `p > 0` and `I` injective which the
positive-degree half of [Stacks, Tag 09V3] needs, and which [Stacks, Tag 09V5] uses to compute
the cohomology of the fibre of a proper map. The Stacks proof of the vanishing goes through Čech
cohomology on a compact Hausdorff space ([Stacks, Tag 09V2]); softness replaces that, and needs
no Čech theory.

## Main results

* `Stacks.Topology.isSoft_pullback_of_isFlasque`: the restriction of a flasque abelian sheaf to a
  quasi-compact subset with separated points is soft.
* `Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque`: that restriction is therefore
  right acyclic for global sections.
* `Stacks.Topology.isFlasque_of_injective`: an injective abelian sheaf is flasque, so the two
  results above apply to injective sheaves.

## Implementation notes

The proof of softness does not use the degree-zero comparison of
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/SubsetSectionsOfCoeff.lean` for closed
subsets of `Z`, which would require transporting the inverse image along a subset of a subset.
It works directly with the ambient space: a section of `F|_Z` on an open `W` of `Z` is, near
every point of a closed `K ⊆ W`, induced by a section of `F` on an ambient open
(`Stacks.Topology.exists_ambient_repr_of_subset`); those ambient sections glue over a
neighbourhood of the compact image of `K` in `X`
(`Stacks.Topology.exists_opens_glue_of_isCompact_of_pairwiseSeparated`); flasqueness of `F`
extends the glued section to the whole of `X`; and the global section of `F|_Z` it induces agrees
with the original one on a neighbourhood of `K`, because their germs agree there.

So flasqueness is used only once, and only on `X`. No normality of `Z` and no shrinking of covers
inside `Z` is needed: all of the shrinking happens in `X`, inside the gluing lemma.

The identities on germs are applied as terms rather than by `rw`; see the implementation notes of
`StacksFrontier/Topology/Sheaves/Functors/Pullback/SectionsAndStalks.lean` for why.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe w w' v u

noncomputable section

variable {X : TopCat.{u}}

/-- The restriction of a flasque abelian sheaf to a quasi-compact subset whose distinct points
have disjoint open neighbourhoods in the ambient space is soft. -/
@[sga "4 Vbis 4.1.5"]
theorem isSoft_pullback_of_isFlasque (F : X.Sheaf AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsSoft ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F) := by
  classical
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  intro K hKclosed W hKW s
  have hK'cpt : IsCompact (Subtype.val '' K) :=
    hKclosed.isCompact.image continuous_subtype_val
  have hK'Z : Subtype.val '' K ⊆ Z := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  choose N hzN hNW a ha using fun z : K ↦
    exists_ambient_repr_of_subset F Z s (z : TopCat.of Z) (hKW z.2)
  have hcover : Subtype.val '' K ⊆ ⋃ z : K, (N z : Set X) := by
    rintro x ⟨z, hzK, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨z, hzK⟩, hzN ⟨z, hzK⟩⟩
  have hcompat : ∀ p q : K, ∀ x ∈ Subtype.val '' K ∩ (N p : Set X) ∩ (N q : Set X),
      ∃ (M : Opens X) (_ : x ∈ M) (iMp : M ⟶ N p) (iMq : M ⟶ N q),
        F.presheaf.map iMp.op (a p) = F.presheaf.map iMq.op (a q) := by
    intro p q x hx
    have hxZ : x ∈ Z := hK'Z hx.1.1
    have hg : F.presheaf.germ (N p) x hx.1.2 (a p) = F.presheaf.germ (N q) x hx.2 (a q) :=
      ambientStalkHom_injective (Stacks.subsetInclusion X Z) F ⟨x, hxZ⟩
        ((ha p x hxZ hx.1.2).trans (ha q x hxZ hx.2).symm)
    exact F.presheaf.germ_eq x hx.1.2 hx.2 _ _ hg
  obtain ⟨V, iVN, hKV, b, hb⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hK'cpt
      (fun x hx y hy hxy ↦ hSep x (hK'Z hx) y (hK'Z hy) hxy) N a hcover hcompat
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.presheaf.map (homOfLE (le_top : (⨆ z : K, V z) ≤ ⊤)).op)).mp inferInstance b
  have htop : (⊤ : Opens (TopCat.of Z)) ≤
      (Opens.map (Stacks.subsetInclusion X Z)).obj (⊤ : Opens X) := fun _ _ ↦ _root_.trivial
  refine ⟨ambientSection (Stacks.subsetInclusion X Z) F htop c,
    (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W, inf_le_right,
    fun z hzK ↦ ⟨hKV ⟨z, hzK, rfl⟩, hKW hzK⟩, ?_⟩
  refine TopCat.Presheaf.section_ext
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F) _ _ _
    fun z hz ↦ ?_
  obtain ⟨z', hz'⟩ := Opens.mem_iSup.1 hz.1
  refine Eq.trans (((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X Z)).obj F).presheaf.germ_res_apply
    (homOfLE (le_top :
      (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W ≤ ⊤)) z hz _) ?_
  refine Eq.trans (germ_ambientSection (Stacks.subsetInclusion X Z) F htop z _root_.trivial c) ?_
  refine Eq.trans (congrArg (ambientStalkHom (Stacks.subsetInclusion X Z) F z)
    (((((F.presheaf.germ_res_apply
          (homOfLE (le_top : (⨆ z : K, V z) ≤ ⊤)) (z : X) hz.1 c).symm.trans
        (congrArg (F.presheaf.germ (⨆ z : K, V z) (z : X) hz.1) hc)).trans
      (F.presheaf.germ_res_apply (Opens.leSupr V z') (z : X) hz' b).symm).trans
      (congrArg (F.presheaf.germ (V z') (z : X) hz') (hb z'))).trans
      (F.presheaf.germ_res_apply (iVN z') (z : X) hz' (a z')))) ?_
  exact (ha z' (z : X) z.2 ((iVN z').le hz')).trans
    (((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X Z)).obj F).presheaf.germ_res_apply
      (homOfLE (inf_le_right :
        (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W ≤ W)) z hz s).symm

/-- The restriction of a flasque abelian sheaf to a quasi-compact subset with separated points
is right acyclic for global sections, that subset being compact Hausdorff in its subspace
topology. -/
theorem rightAcyclic_sections_pullback_of_isFlasque (F : X.Sheaf AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    [HasDerivedCategory.{w}
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))]
    [((sectionsFunctor (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))] :
    (sectionsFunctor (TopCat.of Z)).rightAcyclic
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F) := by
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  have : T2Space Z := t2Space_coe_of_pairwiseSeparated hSep
  exact rightAcyclic_sections_of_isSoft _ (isSoft_pullback_of_isFlasque F hZ hSep)

/-- An injective sheaf of abelian groups is flasque, by [Stacks, Tag 01EA]. The coefficient
universe is independent of the space's. -/
@[sga "4 V 4.6" "special case"]
theorem isFlasque_of_injective (F : X.Sheaf AddCommGrpCat.{v}) [Injective F] :
    TopCat.Sheaf.IsFlasque F :=
  ⟨fun {_ _} i ↦ (AddCommGrpCat.epi_iff_surjective _).2
    (Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
      F (leOfHom i.unop))⟩

end

end Stacks.Topology

end
