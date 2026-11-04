module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionVanishingUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SoftSheavesUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The restriction of a flasque sheaf to a quasi-compact separated subset is soft, in a coefficient
universe of its own

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points of
which have disjoint open neighbourhoods in `X`, and let `F` be a flasque sheaf of abelian groups
on `X`. `Stacks.Topology.isSoft_pullback_of_isFlasque` proves that the restriction `F|_Z` is soft,
but only with the coefficient universe pinned to the universe of the space: it is stated for
`F : X.Sheaf AddCommGrpCat.{u}` with `X : TopCat.{u}`, because `TopCat.Sheaf.pullback` ties the
coefficients to the space and because its proof runs on germs, and `TopCat.Presheaf.stalk` is
declared for `X : TopCat.{v}` with `[Category.{v} C]`.

This file proves it at a coefficient universe independent of the space, **without germs**. The
restriction is `Stacks.Topology.restrictionFunctorUnivLE`, and the thirteen germ-based steps of
the pinned proof are replaced by the filtered-colimit interface of
`CompactSubset/SubsetSectionsUnivLE.lean`:

* `exists_ambient_repr_of_subset` becomes `exists_ambient_repr_toSheafify`;
* `ambientStalkHom_injective` and `TopCat.Presheaf.germ_eq` become
  `CategoryTheory.Presheaf.equalizerSieve_mem` followed by
  `exists_restrict_eq_of_preAmbientSectionUnivLE_eq`;
* `exists_ambientSection_germ` becomes `exists_preAmbientSectionUnivLE`;
* `TopCat.Presheaf.germ_res_apply` and `germ_ambientSection` become
  `preAmbientSectionUnivLE_res_apply`, `preAmbientSectionUnivLE_map_apply` and
  `toSheafify_preAmbientSectionUnivLE_restrict`;
* `TopCat.Presheaf.section_ext` becomes `TopCat.Sheaf.eq_of_locally_eq'` on
  `sheafRestrictionUnivLE`.

## Main results

All in the namespace `Stacks.Topology`.

* `IsSoft.of_iso`: softness is invariant under isomorphism of sheaves. This is what carries the
  statement between the constructed inverse image, where `CategoryTheory.toSheafify` lives, and
  the abstract one, which is the functor every consumer uses.
* `isSoft_sheafRestrictionUnivLE_of_isFlasque`: **the restriction of a flasque abelian sheaf to a
  quasi-compact subset with separated points is soft, at a coefficient universe independent of the
  space**, for the constructed inverse image.
* `isSoft_restrictionFunctorUnivLE_of_isFlasque`: the same for
  `Stacks.Topology.restrictionFunctorUnivLE`.
* `rightAcyclic_sections_pullback_of_isFlasque_univLE`: **that restriction is therefore right
  acyclic for global sections** — the deliverable this file exists for.
* `isZero_cohomologyPresheaf_restriction_of_isFlasque`: combined with
  `Stacks.Topology.isZero_cohomologyPresheaf_restriction_of_rightAcyclic`, the vanishing
  `H^p(Z, F|_Z) = 0` for `p > 0` at a coefficient universe independent of the space.
* `isSoft_pullback_of_isFlasque_of_univLE` and
  `rightAcyclic_sections_pullback_of_isFlasque_of_univLE`: nothing is weakened — at `t := s` these
  *are* the library's `Stacks.Topology.isSoft_pullback_of_isFlasque` and
  `Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque`, same statements about Mathlib's
  own `TopCat.Sheaf.pullback`, with exactly the originals' hypotheses.

## Implementation notes

The structure of the proof is the pinned one. A section `σ` of `F|_Z` on an open `W₀` of `Z`
containing a closed `K` is, near every point of `K`, induced by a section of `F` on an open `M` of
`X` whose inverse image is exactly the open of `Z` on which the two agree; those ambient sections
are pairwise compatible near every point of `Z` lying in two of them, so
`Stacks.Topology.exists_opens_glue_of_isCompact_of_pairwiseSeparated` shrinks the cover and glues
them over an open neighbourhood of the compact image of `K` in `X`; flasqueness of `F` extends the
glued section to the whole of `X`; and the global section of `F|_Z` it induces agrees with `σ` on
`i^{-1}(⋃ V) ⊓ W₀`, checked on that cover by the sheaf axiom.

So flasqueness is used only once, and only on `X`. No normality of `Z` and no shrinking of covers
inside `Z` is needed: all of the shrinking happens in `X`, inside the gluing lemma. What is new
relative to the pinned proof is only *how* a point-local statement about sections is extracted —
by a covering sieve rather than by an equality of germs.

`Stacks.Topology.exists_ambient_repr_toSheafify` and
`Stacks.Topology.toSheafify_preAmbientSectionUnivLE_restrict` were stated for a section over `⊤`,
which is the shape the degree-zero comparison needs; softness needs them over an arbitrary open
`W₀`, so both were generalised in place in `CompactSubset/SubsetSectionsUnivLE.lean` rather than
copied here.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library. Clause 8 is not what is missing:
`Stacks.Topology.properDerivedImageComparison_isIso` is proved, at
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImageIso`, in a
file with no gaps.

Clause 7b is proved too, in degree `i`, as
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.rightDerivedZariskiBaseChangeIso`
(`...LocallyQuasiCompact.ZariskiHigherDirectImageClass`): `R^i f_{Zar,*}(π_X^{-1}G) ≅
π_Y^{-1}(R^i g_* G)`. Note that the separate remark in
`...LocallyQuasiCompact.ZariskiDerivedProperBaseChange` calling clause 7b unproved is **not**
stale: it is about a different map, built from `spaceDirectImage` rather than
`topologicalPushforward`, and identifying those two spellings is still owed.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe w w' t s

noncomputable section

/-- **Softness is invariant under isomorphism of sheaves.** The extension of a section is
transported through the isomorphism, and the two naturality squares of its two directions say
that the transported extension still agrees with the original section. -/
theorem IsSoft.of_iso {Y : TopCat.{s}} {G G' : Sheaf AddCommGrpCat.{t} Y} (e : G ≅ G')
    (h : IsSoft G) : IsSoft G' := by
  intro K hK U hKU s
  have e' : G.obj ≅ G'.obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg (fun m : G ⟶ G ↦ m.hom) e.hom_inv_id
      inv_hom_id := congrArg (fun m : G' ⟶ G' ↦ m.hom) e.inv_hom_id }
  obtain ⟨u, V, hVU, hKV, hu⟩ := h K hK U hKU (e'.inv.app (op U) s)
  refine ⟨e'.hom.app (op ⊤) u, V, hVU, hKV, ?_⟩
  have hcancel : ConcreteCategory.hom (e'.hom.app (op V))
      (ConcreteCategory.hom (e'.inv.app (op V)) (s |_ₗ V ⟪hVU⟫)) = s |_ₗ V ⟪hVU⟫ :=
    (ConcreteCategory.comp_apply (e'.inv.app (op V)) (e'.hom.app (op V)) _).symm.trans
      ((ConcreteCategory.congr_hom (e'.inv_hom_id_app (op V)) _).trans (by simp))
  exact ((Presheaf.map_restrict e'.hom le_top u).symm.trans
    (congrArg (fun z ↦ ConcreteCategory.hom (e'.hom.app (op V)) z)
      (hu.trans (Presheaf.map_restrict e'.inv hVU s).symm))).trans hcancel

variable {X : TopCat.{s}} [UnivLE.{s, t}] (F : X.Sheaf AddCommGrpCat.{t}) (Z : Set X)

/-- **The restriction of a flasque abelian sheaf to a quasi-compact subset whose distinct points
have disjoint open neighbourhoods in the ambient space is soft, at a coefficient universe
independent of the space.** This is for the *constructed* inverse image, the sheafification of the
left Kan extension, where `CategoryTheory.toSheafify` and its local bijectivity live; see
`isSoft_restrictionFunctorUnivLE_of_isFlasque` for the abstract one. -/
@[sga "4 Vbis 4.1.5"]
theorem isSoft_sheafRestrictionUnivLE_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsSoft (sheafRestrictionUnivLE.{t} F Z) := by
  classical
  have _hcpt : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  intro K hKclosed W₀ hKW₀ σ
  have hK'cpt : IsCompact (Subtype.val '' K) :=
    hKclosed.isCompact.image continuous_subtype_val
  have hK'Z : Subtype.val '' K ⊆ Z := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  choose M W hzW hWW₀ hWM hMW a ha using fun z : K ↦
    exists_ambient_repr_toSheafify.{t} F Z σ (z : TopCat.of Z) (hKW₀ z.2)
  have hcover : Subtype.val '' K ⊆ ⋃ z : K, (M z : Set X) := by
    rintro x ⟨z, hzK, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨z, hzK⟩, hWM ⟨z, hzK⟩ (hzW ⟨z, hzK⟩)⟩
  -- the chosen ambient representatives are pairwise compatible near every point of `Z` in two of
  -- them, by local injectivity of `toSheafify` on the intersection of the two opens of `Z`
  have hcompat : ∀ p q : K, ∀ x ∈ Subtype.val '' K ∩ (M p : Set X) ∩ (M q : Set X),
      ∃ (R : Opens X) (_ : x ∈ R) (iRp : R ⟶ M p) (iRq : R ⟶ M q),
        F.presheaf.map iRp.op (a p) = F.presheaf.map iRq.op (a q) := by
    intro p q x hx
    have hxZ : x ∈ Z := hK'Z hx.1.1
    have hzp : (⟨x, hxZ⟩ : TopCat.of Z) ∈ W p := hMW p hx.1.2
    have hzq : (⟨x, hxZ⟩ : TopCat.of Z) ∈ W q := hMW q hx.2
    have hkp : W p ⊓ W q ⟶ W p := homOfLE inf_le_left
    have hkq : W p ⊓ W q ⟶ W q := homOfLE inf_le_right
    have hgpq : W p ⊓ W q ⟶ W₀ := homOfLE (inf_le_left.trans (hWW₀ p))
    have hsec := fun (r : K) (k : W p ⊓ W q ⟶ W r) ↦
      toSheafify_preAmbientSectionUnivLE_restrict.{t} F Z (hWM r) (a r) σ
        (homOfLE (hWW₀ r)) (ha r) k hgpq
    have hsieve := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (TopCat.of Z))
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z)) (presheafRestrictionUnivLE.{t} F Z))
      (preAmbientSectionUnivLE.{t} F Z (hkp.le.trans (hWM p)) (a p))
      (preAmbientSectionUnivLE.{t} F Z (hkq.le.trans (hWM q)) (a q))
      ((hsec p hkp).trans (hsec q hkq).symm)
    obtain ⟨W'', k, hk, hzW''⟩ := hsieve (⟨x, hxZ⟩ : TopCat.of Z) ⟨hzp, hzq⟩
    have hres := fun (r : K) (h : W p ⊓ W q ⟶ W r) ↦
      preAmbientSectionUnivLE_res_apply.{t} F Z k (h.le.trans (hWM r)) (a r)
    have hk' := (hres p hkp).symm.trans (hk.trans (hres q hkq))
    obtain ⟨R, hR, m, m', hmm⟩ :=
      exists_restrict_eq_of_preAmbientSectionUnivLE_eq.{t} F Z _ _ (a p) (a q) hk'
    exact ⟨R, hR hzW'', m, m', hmm⟩
  obtain ⟨V, iVM, hKV, b, hb⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hK'cpt
      (fun x hx y hy hxy ↦ hSep x (hK'Z hx) y (hK'Z hy) hxy) M a hcover hcompat
  -- flasqueness extends the glued section from the neighbourhood of `K` to the whole of `X`
  obtain ⟨g, hg⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.presheaf.map (homOfLE (le_top : (⨆ z : K, V z) ≤ ⊤)).op)).mp inferInstance b
  have htop : (⊤ : Opens (TopCat.of Z)) ≤
      (Opens.map (Stacks.subsetInclusion X Z)).obj (⊤ : Opens X) := fun _ _ ↦ _root_.trivial
  refine ⟨(toSheafify (Opens.grothendieckTopology (TopCat.of Z))
      (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)
      (preAmbientSectionUnivLE.{t} F Z htop g),
    (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W₀, inf_le_right,
    fun z hzK ↦ ⟨hKV ⟨z, hzK, rfl⟩, hKW₀ hzK⟩, ?_⟩
  -- the two sections agree on each `i^{-1}(V z) ⊓ W₀`, which cover the open above
  refine TopCat.Sheaf.eq_of_locally_eq' (sheafRestrictionUnivLE.{t} F Z)
    (fun z : K ↦ (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀) _
    (fun _ ↦ homOfLE (inf_le_inf_right _ (fun y hy ↦ (Opens.leSupr V _).le hy)))
    (fun y hy ↦ ?_) _ _ fun z ↦ ?_
  · obtain ⟨z, hz⟩ := Opens.mem_iSup.1 hy.1
    exact Opens.mem_iSup.2 ⟨z, hz, hy.2⟩
  · have hQVz : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤
        (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) := inf_le_left
    have hQsup : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤
        (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) :=
      fun y hy ↦ (Opens.leSupr V z).le hy.1
    have hQM : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤
        (Opens.map (Stacks.subsetInclusion X Z)).obj (M z) :=
      fun y hy ↦ (iVM z).le hy.1
    have hQtop : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤
        (Opens.map (Stacks.subsetInclusion X Z)).obj (⊤ : Opens X) := fun _ _ ↦ _root_.trivial
    have hQW : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ⟶ W z :=
      homOfLE fun y hy ↦ hMW z ((iVM z).le hy.1)
    have hQW₀ : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ⟶ W₀ :=
      homOfLE inf_le_right
    -- the right-hand side: the prescribed section, through the chosen representative at `z`
    have hRHS := toSheafify_preAmbientSectionUnivLE_restrict.{t} F Z (hWM z) (a z) σ
      (homOfLE (hWW₀ z)) (ha z) hQW hQW₀
    -- the left-hand side: the flasque extension, back down to `V z` and then to `M z`
    have hres : (presheafRestrictionUnivLE.{t} F Z).map
          (homOfLE (le_top :
            (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤ ⊤)).op
          (preAmbientSectionUnivLE.{t} F Z htop g) =
        preAmbientSectionUnivLE.{t} F Z hQM (a z) :=
      (preAmbientSectionUnivLE_res_apply.{t} F Z
          (homOfLE (le_top :
            (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤ ⊤)) htop g).trans
        ((preAmbientSectionUnivLE_map_apply.{t} F Z
            (homOfLE (le_top : (⨆ z : K, V z) ≤ ⊤)) hQsup hQtop g).symm.trans
          ((congrArg (preAmbientSectionUnivLE.{t} F Z hQsup) hg).trans
            ((preAmbientSectionUnivLE_map_apply.{t} F Z (Opens.leSupr V z) hQVz hQsup b).symm.trans
              ((congrArg (preAmbientSectionUnivLE.{t} F Z hQVz) (hb z)).trans
                (preAmbientSectionUnivLE_map_apply.{t} F Z (iVM z) hQVz hQM (a z))))))
    have hLHS := (congrArg (fun x ↦ ConcreteCategory.hom
        ((toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app
          (op ((Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀))) x) hres).symm.trans
      (NatTrans.naturality_apply (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z))
        (homOfLE (le_top :
          (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤ ⊤)).op
        (preAmbientSectionUnivLE.{t} F Z htop g))
    refine (map_op_comp_apply (sheafRestrictionUnivLE.{t} F Z).presheaf
      (homOfLE (inf_le_inf_right _ (fun y hy ↦ (Opens.leSupr V z).le hy)))
      (homOfLE (le_top :
        (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W₀ ≤ ⊤))
      (homOfLE (le_top :
        (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⊓ W₀ ≤ ⊤)) _).trans
      ((hLHS.symm.trans hRHS).trans
        (map_op_comp_apply (sheafRestrictionUnivLE.{t} F Z).presheaf
          (homOfLE (inf_le_inf_right _ (fun y hy ↦ (Opens.leSupr V z).le hy)))
          (homOfLE (inf_le_right :
            (Opens.map (Stacks.subsetInclusion X Z)).obj (⨆ z : K, V z) ⊓ W₀ ≤ W₀))
          hQW₀ σ).symm)

/-- **The restriction of a flasque abelian sheaf to a quasi-compact subset whose distinct points
have disjoint open neighbourhoods in the ambient space is soft**, at a coefficient universe
independent of the space, for `Stacks.Topology.restrictionFunctorUnivLE` — the inverse image every
consumer uses. It is carried from the constructed inverse image by
`Stacks.Topology.sheafifyRestrictionIso`. -/
@[sga "4 Vbis 4.1.5"]
theorem isSoft_restrictionFunctorUnivLE_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsSoft ((restrictionFunctorUnivLE.{t} X Z).obj F) :=
  IsSoft.of_iso (sheafifyRestrictionIso.{t} F Z).symm
    (isSoft_sheafRestrictionUnivLE_of_isFlasque.{t} F Z hZ hSep)

section Acyclic

variable [HasDerivedCategory.{w}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{t}]
  [((sectionsFunctorUnivLE.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t}))]

/-- **The restriction of a flasque abelian sheaf to a quasi-compact subset with separated points
is right acyclic for global sections, at a coefficient universe independent of the space**, that
subset being compact Hausdorff in its subspace topology. This is the acyclicity input that
`CompactSubset/RestrictionVanishingUnivLE.lean` carries as a hypothesis, and the deliverable of
this file. -/
theorem rightAcyclic_sections_pullback_of_isFlasque_univLE [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    (sectionsFunctorUnivLE.{t} (TopCat.of Z)).rightAcyclic
      ((restrictionFunctorUnivLE.{t} X Z).obj F) :=
  have _hcpt : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  have _ht2 : T2Space Z := t2Space_coe_of_pairwiseSeparated hSep
  rightAcyclic_sections_of_isSoft_univLE.{w, w', t} _
    (isSoft_restrictionFunctorUnivLE_of_isFlasque.{t} F Z hZ hSep)

end Acyclic

end

section Vanishing

noncomputable section

variable {X : TopCat.{s}} (F : X.Sheaf AddCommGrpCat.{max s t}) {Z : Set X}

/-- **The higher cohomology of the restriction of a flasque abelian sheaf to a quasi-compact
subset with separated points vanishes, at a coefficient universe independent of the space.**

This is the composite of this file's acyclicity with the transport
`Stacks.Topology.isZero_cohomologyPresheaf_restriction_of_rightAcyclic`, whose acyclicity
hypothesis this file supplies at mixed universes: it is the mixed-universe form
of `Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque`. -/
theorem isZero_cohomologyPresheaf_restriction_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
      AddCommGrpCat.{max s t})]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
      AddCommGrpCat.{max s t})]
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
      AddCommGrpCat.{max s t})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
    [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F) p).obj (op ⊤)) :=
  have _hei : EnoughInjectives (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
      AddCommGrpCat.{max s t}) :=
    enoughInjectives_sheafOpens.{max s t} (TopCat.of Z)
  have _hrd : ((sectionsFunctorUnivLE.{max s t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})) :=
    inferInstanceAs (((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})))
  isZero_cohomologyPresheaf_restriction_of_rightAcyclic.{w, w', t, s} F
    (rightAcyclic_sections_pullback_of_isFlasque_univLE.{w, w', max s t} F Z hZ hSep) p hp

end

end Vanishing

section NoWeakening

noncomputable section

variable {X : TopCat.{s}} (F : X.Sheaf AddCommGrpCat.{s}) (Z : Set X)

/-- **Nothing is weakened: at `t := s` the softness proved here is the library's
`Stacks.Topology.isSoft_pullback_of_isFlasque`** — softness of Mathlib's own
`TopCat.Sheaf.pullback` of `F` along the inclusion of `Z`, with exactly the original's
hypotheses. The two restrictions are not merely isomorphic:
`Stacks.Topology.restrictionFunctorUnivLE_eq_pullback` is `rfl`. -/
@[sga "4 Vbis 4.1.5"]
theorem isSoft_pullback_of_isFlasque_of_univLE [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsSoft ((TopCat.Sheaf.pullback AddCommGrpCat.{s} (Stacks.subsetInclusion X Z)).obj F) :=
  isSoft_restrictionFunctorUnivLE_of_isFlasque.{s} F Z hZ hSep

/-- **Nothing is weakened: at `t := s` the acyclicity proved here is the library's
`Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque`** — the same conclusion about the
library's own `Stacks.Topology.sectionsFunctor` and Mathlib's own `TopCat.Sheaf.pullback`, with
exactly the original's hypotheses. -/
theorem rightAcyclic_sections_pullback_of_isFlasque_of_univLE [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    [HasDerivedCategory.{w}
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{s})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{s}]
    [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{s} (TopCat.of Z))]
    [((sectionsFunctor (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{s}))] :
    (sectionsFunctor (TopCat.of Z)).rightAcyclic
      ((TopCat.Sheaf.pullback AddCommGrpCat.{s} (Stacks.subsetInclusion X Z)).obj F) :=
  rightAcyclic_sections_pullback_of_isFlasque_univLE.{w, w', s} F Z hZ hSep

end

end NoWeakening

end Stacks.Topology

end
