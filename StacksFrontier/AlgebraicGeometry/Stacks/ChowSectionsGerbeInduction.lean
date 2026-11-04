module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionCoverUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionLocalIso
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionsInduction

/-!
# Sections over a gerbe locus give compactifiable covers (Stacks 0CQ7, paragraphs (d)–(g))

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space, all of
whose values lie in an open `W ⊆ Y`, which is a gerbe over an open `V ⊆ Y`. Let `p : Y' ⟶ Y` be a
proper morphism from a quasi-compact quasi-separated algebraic space, and let `x₀ : U₀ ⟶ 𝒳` and
`x i : U i ⟶ 𝒳` be 1-morphisms over `Y` out of quasi-compact opens covering `p⁻¹(W)`. Then for
every quasi-compact open `V' ⊆ p⁻¹(V)` contained in all the `U`'s, one section cover
(`HasSectionCovers`) of `f` covers the image of `|V'|` in `|Y|`.

This is the part of the proof of [Stacks, Tag 0CQ7] after condition (d) has been arranged. The
source makes all the sections isomorphic at once and then glues; here they are glued one at a
time. Two of them are isomorphic Zariski locally over `V'` after a finite surjective base change
(`exists_finite_cover_iso_of_isGerbeOver`, which is the step "(d) ⟹ (e)"); over each of finitely
many quasi-compact pieces of the cover they become isomorphic on the intersection of their
domains after an admissible blowup and glue (`exists_glued_section_of_iso`, the steps
"(f) ⟹ (g)"), which removes one section; the conclusion for `V'` is the union of the conclusions
for the pieces.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasSectionCovers_of_sections_of_isGerbeOver`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

variable (hf : IsSeparated B S hS f) (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
  (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
  (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
  (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)

/-- The source of a proper morphism to a quasi-compact, absolutely quasi-separated algebraic space
is again quasi-compact and absolutely quasi-separated. -/
private theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper
    {Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY₂ : IsAlgebraicSpace B S hS Y₂) (hqc : Space.IsQuasiCompactSpace B S hS Y₂)
    (hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₂) {g : Y₁ ⟶ Y₂}
    (hg : Space.IsProper B S hS g) :
    Space.IsQuasiCompactSpace B S hS Y₁ ∧
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₁ :=
  ⟨Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY₂ hqc hg.2.1.2,
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY₁ hqs
      (Space.isQuasiSeparated_of_isSeparated B S hS hg.1)⟩

/-- A point lies in the points of a preimage subspace iff its image lies in the subspace. -/
private theorem mem_range_pointsMap_preimage_ι_iff {Y₁ Y₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Y₁ ⟶ Y₂) (Z : Subfunctor Y₂) (y : Space.points B S hS Y₁) :
    y ∈ Set.range (Space.pointsMap B S hS (Z.preimage g).toFunctor (Z.preimage g).ι) ↔
      Space.pointsMap B S hS Y₁ g y ∈ Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) := by
  rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage]

/-- A point of `(g ≫ p)⁻¹(Z)` maps under `g` to a point of `p⁻¹(Z)`. -/
private theorem pointsMap_mem_range_preimage_ι_of_comp
    {Y₁ Y₂ Y₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y₁ ⟶ Y₂) (p : Y₂ ⟶ Y₃) (Z : Subfunctor Y₃)
    {y : Space.points B S hS Y₁}
    (hy : y ∈ Set.range (Space.pointsMap B S hS (Z.preimage (g ≫ p)).toFunctor
      (Z.preimage (g ≫ p)).ι)) :
    Space.pointsMap B S hS Y₁ g y ∈ Set.range (Space.pointsMap B S hS (Z.preimage p).toFunctor
      (Z.preimage p).ι) := by
  rw [mem_range_pointsMap_preimage_ι_iff] at hy ⊢
  rwa [← Space.pointsMap_comp_apply]

include hf hW hfW hG in
/-- **Sections over a gerbe locus give compactifiable covers** (the steps (d)–(g) of the proof of
[Stacks, Tag 0CQ7]). Let `f : 𝒳 ⟶ Y` be separated, with all its values in an open `W ⊆ Y`, and a
gerbe over an open `V ⊆ Y`; let `p : Y' ⟶ Y` be proper with `Y'` quasi-compact and
quasi-separated, and let `x₀ : U₀ ⟶ 𝒳`, `x i : U i ⟶ 𝒳` (`i < n`) be 1-morphisms over `Y` out of
quasi-compact opens of `p⁻¹(W)` covering it. Then for every quasi-compact open `V' ⊆ p⁻¹(V)`
contained in `U₀` and in all `U i`, one section cover (`HasSectionCovers`) of `f` covers
the image of `|V'|` in `|Y|`.

By induction on `n`. For `n = 0` the section `x₀` is defined over `p⁻¹(W)`
(`CompactifiableCover.ofSection`). Otherwise `x₀` and `x 0` are isomorphic Zariski locally over
`V'` after a finite surjective `g : Y'' ⟶ Y'` (`exists_finite_cover_iso_of_isGerbeOver`); finitely
many quasi-compact opens `N` on which they are isomorphic cover `g⁻¹(V')`, and over each of them
the two sections glue after an `N`-admissible blowup (`exists_glued_section_of_iso`), leaving `n`
sections, to which the induction hypothesis applies. -/
theorem hasSectionCovers_of_sections_of_isGerbeOver :
    ∀ (n : ℕ) {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (_ : Space.IsQuasiCompactSpace B S hS Y')
    (_ : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y') (p : Y' ⟶ Y)
    (_ : Space.IsProper B S hS p) (V' U₀ : Subfunctor Y') (hV' : Space.IsOpenSubspace B S hS V')
    (_ : Space.IsQuasiCompactSpace B S hS V'.toFunctor) (_ : V' ≤ V.preimage p)
    (hU₀ : Space.IsOpenSubspace B S hS U₀)
    (_ : Space.IsQuasiCompactSpace B S hS U₀.toFunctor) (_ : U₀ ≤ W.preimage p) (_ : V' ≤ U₀)
    (x₀ : algebraicSpaceStack.{u, w} B S hS U₀.toFunctor hU₀.1 ⟶ 𝒳)
    (_ : Nonempty (x₀ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU₀.1 hY (U₀.ι ≫ p)))
    (U : Fin n → Subfunctor Y') (hU : ∀ i, Space.IsOpenSubspace B S hS (U i))
    (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (U i).toFunctor) (_ : ∀ i, U i ≤ W.preimage p)
    (_ : ∀ i, V' ≤ U i)
    (x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i).1 ⟶ 𝒳)
    (_ : ∀ i, Nonempty (x i ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS (hU i).1 hY ((U i).ι ≫ p)))
    (_ : Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor (W.preimage p).ι) ⊆
      Set.range (Space.pointsMap B S hS U₀.toFunctor U₀.ι) ∪
        ⋃ i, Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)),
    HasSectionCovers hY f hf W hW hfW (Space.pointsMap B S hS Y' p ''
      Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι)) := by
  intro n
  induction n with
  | zero =>
    intro Y' hY' _ _ p hp V' U₀ hV' _ _ hU₀ _ hU₀W hVU₀ x₀ ex₀ U hU _ _ hVU x _ hcov
    have hle : W.preimage p ≤ U₀ := by
      refine Space.le_of_range_pointsMap_ι_subset B S hS hU₀ fun y hy => ?_
      rcases hcov hy with h | h
      · exact h
      · obtain ⟨i, -⟩ := Set.mem_iUnion.1 h
        exact i.elim0
    obtain rfl : U₀ = W.preimage p := le_antisymm hU₀W hle
    refine HasSectionCovers.of_section hY' p hp x₀ ex₀ ?_
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe hVU₀) v, ?_⟩
    show Space.pointsMap B S hS _ ((W.preimage p).ι ≫ p) _ = _
    refine (Space.pointsMap_comp_apply B S hS _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Space.pointsMap_comp_apply B S hS _ _ _)
    rw [← Category.assoc, Subfunctor.homOfLe_ι]
  | succ n ih =>
    intro Y' hY' hY'qc hY'qs p hp V' U₀ hV' hV'qc hV'V hU₀ hU₀qc hU₀W hVU₀ x₀ ex₀ U hU hUqc hUW
      hVU x ex hcov
    let := Space.pointTopology B S hS Y'
    obtain ⟨e₀⟩ := ex₀
    obtain ⟨e₁⟩ := ex 0
    have hU₁ := hU 0
    -- the intersection `U₀ ∩ U 0` and the two sections over it
    have hInt := Space.isOpenSubspace_inf B S hS hY' U₀ (U 0) hU₀ hU₁
    have hV'Int : V' ≤ U₀ ⊓ U 0 := le_inf hVU₀ (hVU 0)
    let xa :=
      algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₀.1 (Subfunctor.homOfLe inf_le_left) ≫ x₀
    let xb := algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₁.1 (Subfunctor.homOfLe inf_le_right) ≫
      x 0
    have restrict : ∀ {U₁ : Subfunctor Y'} (hU₁ : Space.IsOpenSubspace B S hS U₁)
        (h : U₀ ⊓ U 0 ≤ U₁) (x₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor hU₁.1 ⟶ 𝒳)
        (e : x₁ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU₁.1 hY (U₁.ι ≫ p)),
        (algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₁.1 (Subfunctor.homOfLe h) ≫ x₁) ≫ f ≅
          algebraicSpaceStackMap.{u, w} B S hS hInt.1 hY ((U₀ ⊓ U 0).ι ≫ p) :=
      fun _ h _ e => α_ _ _ _ ≪≫ whiskerLeftIso _ e ≪≫
        eqToIso ((algebraicSpaceStackMap_comp_eq _ _ _ _ _).symm.trans
          (congrArg _ (by rw [← Category.assoc, Subfunctor.homOfLe_ι])))
    have ea := restrict hU₀ inf_le_left x₀ e₀
    have eb := restrict hU₁ inf_le_right (x 0) e₁
    -- the finite cover over which the two sections are locally isomorphic over `V'`
    obtain ⟨Y₂, hY₂, g, hgf, hgs, J, O, hO, hOV, hOcov, hOiso⟩ :=
      exists_finite_cover_iso_of_isGerbeOver hY f V hV hG hY' hY'qc hY'qs p (U₀ ⊓ U 0) V' hInt hV'
        hV'qc hV'Int hV'V xa xb ea eb
    let := Space.pointTopology B S hS Y₂
    have hgp : Space.IsProper B S hS g :=
      ((Space.isFinite_iff_isAffineHom_and_isProper B S hS hY₂ hY' g).1 hgf).2
    obtain ⟨hY₂qc, hY₂qs⟩ :=
      isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper hY₂ hY' hY'qc hY'qs hgp
    have hpre : ∀ {O' : Subfunctor Y'}, Space.IsOpenSubspace B S hS O' →
        Space.IsOpenSubspace B S hS (O'.preimage g) := fun hO' =>
      Space.isOpenSubspace_preimage B S hS g _ hY' hY₂ hO'
    have hpreqc : ∀ {O' : Subfunctor Y'} (hO' : Space.IsOpenSubspace B S hS O'),
        Space.IsQuasiCompactSpace B S hS O'.toFunctor →
        Space.IsQuasiCompactSpace B S hS (O'.preimage g).toFunctor := fun hO' hO'qc =>
      Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY' hY₂ g hgp.2.1.2 hO' hO'qc
    -- the sections pulled back to `Y₂`
    let x₀₂ := algebraicSpaceStackMap.{u, w} B S hS (hpre hU₀).1 hU₀.1 (U₀.fromPreimage g) ≫ x₀
    have e₀₂ := pullbackSectionIso f hY' hY₂ p g hU₀ x₀ e₀
    let x₂ : ∀ i, algebraicSpaceStack.{u, w} B S hS ((U i).preimage g).toFunctor (hpre (hU i)).1 ⟶
        𝒳 := fun i =>
      algebraicSpaceStackMap.{u, w} B S hS (hpre (hU i)).1 (hU i).1 ((U i).fromPreimage g) ≫ x i
    have e₂ : ∀ i, Nonempty (x₂ i ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hpre (hU i)).1 hY
        (((U i).preimage g).ι ≫ g ≫ p)) := fun i =>
      (ex i).map fun e => pullbackSectionIso f hY' hY₂ p g (hU i) (x i) e
    -- the conclusion over one quasi-compact piece of the cover
    have claim : ∀ (N : Subfunctor Y₂) (hN : Space.IsOpenSubspace B S hS N)
        (_ : Space.IsQuasiCompactSpace B S hS N.toFunctor) (j : J) (_ : N ≤ O j),
        HasSectionCovers hY f hf W hW hfW (Space.pointsMap B S hS Y₂ (g ≫ p) ''
          Set.range (Space.pointsMap B S hS N.toFunctor N.ι)) := by
      intro N hN hNqc j hNO
      have hNV' : N ≤ V'.preimage g := hNO.trans (hOV j)
      have hNU₀ : N ≤ U₀.preimage g := fun T y hy => hVU₀ _ (hNV' T hy)
      have hNU₁ : N ≤ (U 0).preimage g := fun T y hy => hVU 0 _ (hNV' T hy)
      obtain ⟨θ⟩ := hOiso j
      have LR : ∀ {U₁ : Subfunctor Y'} (hU₁ : Space.IsOpenSubspace B S hS U₁)
          (h : U₀ ⊓ U 0 ≤ U₁) (hNU : N ≤ U₁.preimage g)
          (x₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor hU₁.1 ⟶ 𝒳),
          algebraicSpaceStackMap.{u, w} B S hS hN.1 (hpre hU₁).1 (Subfunctor.homOfLe hNU) ≫
            (algebraicSpaceStackMap.{u, w} B S hS (hpre hU₁).1 hU₁.1 (U₁.fromPreimage g) ≫ x₁) =
          algebraicSpaceStackMap.{u, w} B S hS hN.1 (hO j).1 (Subfunctor.homOfLe hNO) ≫
            algebraicSpaceStackMap.{u, w} B S hS (hO j).1 hInt.1
              (Subfunctor.homOfLe (hOV j) ≫ V'.fromPreimage g ≫ Subfunctor.homOfLe hV'Int) ≫
                ((algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₁.1 (Subfunctor.homOfLe h)) ≫
                  x₁) := by
        intro U₁ hU₁ h hNU x₁
        rw [← Category.assoc, Stack.algebraicSpaceStackMap_comp B S hS, ← Category.assoc,
          ← Category.assoc, Stack.algebraicSpaceStackMap_comp B S hS,
          Stack.algebraicSpaceStackMap_comp B S hS]
        rfl
      have φ : algebraicSpaceStackMap.{u, w} B S hS hN.1 (hpre hU₀).1 (Subfunctor.homOfLe hNU₀) ≫
          x₀₂ ≅ algebraicSpaceStackMap.{u, w} B S hS hN.1 (hpre hU₁).1 (Subfunctor.homOfLe hNU₁) ≫
            x₂ 0 :=
        eqToIso (LR hU₀ inf_le_left hNU₀ x₀) ≪≫ whiskerLeftIso _ θ ≪≫
          eqToIso (LR hU₁ inf_le_right hNU₁ (x 0)).symm
      -- glue `x₀` and `x 0` over `N`, after an `N`-admissible blowup
      obtain ⟨Y'', bl, hbl, Z, hZ, hZ₀, hZ₁, hZrange, G, ⟨eG⟩, -⟩ :=
        exists_glued_section_of_iso f hf hY₂ hY₂qc hY₂qs (g ≫ p) N (U₀.preimage g)
          ((U 0).preimage g) hN hNqc (hpre hU₀) (hpreqc hU₀ hU₀qc) (hpre hU₁) (hpreqc hU₁ (hUqc 0))
          hNU₀ hNU₁ x₀₂ ⟨e₀₂⟩ (x₂ 0) (e₂ 0) φ
      let := Space.pointTopology B S hS Y''.1
      have hblp : Space.IsProper B S hS bl.hom := hbl.isProper
      obtain ⟨hY''qc, hY''qs⟩ :=
        isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper Y''.2 hY₂ hY₂qc hY₂qs hblp
      have hp'' : Space.IsProper B S hS (bl.hom ≫ g ≫ p) :=
        Space.isProper_comp B S hS Y''.2 hY₂ hY bl.hom (g ≫ p) hblp
          (Space.isProper_comp B S hS hY₂ hY' hY g p hgp hp)
      have hpre' : ∀ {O' : Subfunctor Y₂}, Space.IsOpenSubspace B S hS O' →
          Space.IsOpenSubspace B S hS (O'.preimage bl.hom) := fun hO' =>
        Space.isOpenSubspace_preimage B S hS bl.hom _ hY₂ Y''.2 hO'
      have hpreqc' : ∀ {O' : Subfunctor Y₂} (hO' : Space.IsOpenSubspace B S hS O'),
          Space.IsQuasiCompactSpace B S hS O'.toFunctor →
          Space.IsQuasiCompactSpace B S hS (O'.preimage bl.hom).toFunctor := fun hO' hO'qc =>
        Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₂ Y''.2 bl.hom hblp.2.1.2 hO'
          hO'qc
      have hV''Z : N.preimage bl.hom ≤ Z :=
        le_trans (show N.preimage bl.hom ≤ (U₀.preimage g).preimage bl.hom from
          fun T _ hy => hNU₀ T hy) hZ₀
      have hZW : Z ≤ W.preimage (bl.hom ≫ g ≫ p) := by
        refine Space.le_of_range_pointsMap_ι_subset B S hS
          (hpre' (hpre (Space.isOpenSubspace_preimage B S hS p W hY hY' hW))) ?_
        have hsub : ∀ {U' : Subfunctor Y'}, U' ≤ W.preimage p →
            Set.range (Space.pointsMap B S hS ((U'.preimage g).preimage bl.hom).toFunctor
              ((U'.preimage g).preimage bl.hom).ι) ⊆
            Set.range (Space.pointsMap B S hS
              (((W.preimage p).preimage g).preimage bl.hom).toFunctor
              (((W.preimage p).preimage g).preimage bl.hom).ι) := by
          rintro U' hU' _ ⟨z, rfl⟩
          refine ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe
            (fun T _ h => hU' T h : (U'.preimage g).preimage bl.hom ≤
              ((W.preimage p).preimage g).preimage bl.hom)) z, ?_⟩
          rw [← Space.pointsMap_comp_apply]
          rfl
        rw [hZrange]
        exact Set.union_subset (hsub hU₀W) (hsub (hUW 0))
      have hZqc : Space.IsQuasiCompactSpace B S hS Z.toFunctor := by
        refine Space.isQuasiCompactSpace_of_isCompact_range B S hS Y''.2 hZ ?_
        rw [hZrange]
        exact (Space.isCompact_range_of_isQuasiCompactSpace B S hS (hpre' (hpre hU₀))
          (hpreqc' (hpre hU₀) (hpreqc hU₀ hU₀qc))).union
          (Space.isCompact_range_of_isQuasiCompactSpace B S hS (hpre' (hpre hU₁))
            (hpreqc' (hpre hU₁) (hpreqc hU₁ (hUqc 0))))
      have h := ih Y''.2 hY''qc hY''qs (bl.hom ≫ g ≫ p) hp'' (N.preimage bl.hom) Z (hpre' hN)
        (hpreqc' hN hNqc) (fun T y hy => hV'V _ (hNV' _ hy)) hZ hZqc hZW hV''Z G ⟨eG⟩
        (fun i => ((U i.succ).preimage g).preimage bl.hom) (fun i => hpre' (hpre (hU i.succ)))
        (fun i => hpreqc' (hpre (hU i.succ)) (hpreqc (hU i.succ) (hUqc i.succ)))
        (fun i T _ h => hUW i.succ T h) (fun i T y hy => hVU i.succ _ (hNV' _ hy))
        (fun i => algebraicSpaceStackMap.{u, w} B S hS (hpre' (hpre (hU i.succ))).1
          (hpre (hU i.succ)).1 (((U i.succ).preimage g).fromPreimage bl.hom) ≫ x₂ i.succ)
        (fun i => (e₂ i.succ).map fun e =>
          pullbackSectionIso f hY₂ Y''.2 (g ≫ p) bl.hom (hpre (hU i.succ)) _ e) ?_
      · refine h.mono ?_
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨v', hv', rfl⟩ := Space.range_pointsMap_subset_image_of_isAdmissibleBlowup
          (X := ⟨Y₂, hY₂⟩) ⟨N, hN⟩ hbl hv
        exact ⟨v', hv', Space.pointsMap_comp_apply B S hS _ _ _⟩
      · have back : ∀ {Z : Subfunctor Y'} {y : Space.points B S hS Y''.1},
            Space.pointsMap B S hS _ (bl.hom ≫ g) y ∈
              Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) →
            y ∈ Set.range (Space.pointsMap B S hS ((Z.preimage g).preimage bl.hom).toFunctor
              ((Z.preimage g).preimage bl.hom).ι) := fun h =>
          (mem_range_pointsMap_preimage_ι_iff _ _ _).2
            ((mem_range_pointsMap_preimage_ι_iff _ _ _).2 (by rwa [← Space.pointsMap_comp_apply]))
        intro y hy
        rcases hcov (pointsMap_mem_range_preimage_ι_of_comp (bl.hom ≫ g) p W hy) with h₀ | h₁
        · left
          rw [hZrange]
          left
          exact back h₀
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h₁
          refine Fin.cases ?_ (fun j hj => ?_) i hi
          · intro h0
            left
            rw [hZrange]
            right
            exact back h0
          · right
            exact Set.mem_iUnion.2 ⟨j, back hj⟩
    -- finitely many pieces cover `g⁻¹(V')`
    have hpiece : ∀ y : Space.points B S hS Y₂,
        y ∈ Set.range (Space.pointsMap B S hS (V'.preimage g).toFunctor (V'.preimage g).ι) →
        ∃ (N : Subfunctor Y₂) (_ : Space.IsOpenSubspace B S hS N)
          (_ : Space.IsQuasiCompactSpace B S hS N.toFunctor) (j : J) (_ : N ≤ O j),
          y ∈ Set.range (Space.pointsMap B S hS N.toFunctor N.ι) := by
      intro y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hOcov hy)
      obtain ⟨N, hN, hNqc, hyN, hNsub⟩ :=
        Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hY₂ _
          (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (O j).ι (hO j).2) y hj
      exact ⟨N, hN, hNqc, j, Space.le_of_range_pointsMap_ι_subset B S hS (hO j) hNsub, hyN⟩
    choose Nf hNf hNfqc jf hNfO hyNf using hpiece
    let K := Set.range (Space.pointsMap B S hS (V'.preimage g).toFunctor (V'.preimage g).ι)
    have hK : IsCompact K :=
      Space.isCompact_range_of_isQuasiCompactSpace B S hS (hpre hV') (hpreqc hV' hV'qc)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun y : K => Set.range (Space.pointsMap B S hS (Nf y.1 y.2).toFunctor (Nf y.1 y.2).ι))
      (fun y => Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hNf y.1 y.2).2)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyNf y hy⟩)
    refine (HasSectionCovers.biUnion (t : Set K) t.finite_toSet
      (fun y : K => Space.pointsMap B S hS Y₂ (g ≫ p) ''
        Set.range (Space.pointsMap B S hS (Nf y.1 y.2).toFunctor (Nf y.1 y.2).ι))
      (fun y _ => claim (Nf y.1 y.2) (hNf y.1 y.2) (hNfqc y.1 y.2) (jf y.1 y.2)
        (hNfO y.1 y.2))).mono ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y₀, hy₀⟩ := hgs v
    have hy₀K : y₀ ∈ K := by
      show y₀ ∈ Set.range (Space.pointsMap B S hS (V'.preimage g).toFunctor (V'.preimage g).ι)
      rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hy₀]
      exact hv
    obtain ⟨k, hk, hk'⟩ := Set.mem_iUnion₂.1 (ht hy₀K)
    refine Set.mem_iUnion₂.2 ⟨k, hk, y₀, hk', ?_⟩
    rw [Space.pointsMap_comp_apply, hy₀]

include hf hW hfW hG in
/-- **Sections over opens covering `p⁻¹(W)` give compactifiable covers over the gerbe locus**
(the steps (c)–(g) of the proof of [Stacks, Tag 0CQ7]). Let `f : 𝒳 ⟶ Y` be separated, with all
its values in an open `W ⊆ Y`, and a gerbe over an open `V ⊆ Y`; let `p : Y' ⟶ Y` be proper with
`Y'` quasi-compact and quasi-separated, and let `x i : U i ⟶ 𝒳` be 1-morphisms over `Y` out of
quasi-compact opens of `p⁻¹(W)` covering it. Then for every quasi-compact open
`V' ⊆ p⁻¹(V) ∩ p⁻¹(W)` one section cover (`HasSectionCovers`) of `f` covers the image of
`|V'|` in `|Y|`.

By induction on the number of opens, as in the source: `|V'|` is covered by `|V' ∩ ⋂ U i|`, which
is `hasSectionCovers_of_sections_of_isGerbeOver`, and by the `|V'| ∖ |U i|`, which are the
points of `V'` on the reduced closed complement `Y_i` of `U i` (Stacks 03IQ), over which the
other `n` sections cover the inverse image of `W`. -/
theorem hasSectionCovers_of_sections_of_isGerbeOver_cover :
    ∀ (n : ℕ) {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (_ : Space.IsQuasiCompactSpace B S hS Y')
    (_ : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y') (p : Y' ⟶ Y)
    (_ : Space.IsProper B S hS p) (V' : Subfunctor Y') (hV' : Space.IsOpenSubspace B S hS V')
    (_ : Space.IsQuasiCompactSpace B S hS V'.toFunctor) (_ : V' ≤ V.preimage p)
    (_ : V' ≤ W.preimage p)
    (U : Fin n → Subfunctor Y') (hU : ∀ i, Space.IsOpenSubspace B S hS (U i))
    (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (U i).toFunctor) (_ : ∀ i, U i ≤ W.preimage p)
    (x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i).1 ⟶ 𝒳)
    (_ : ∀ i, Nonempty (x i ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS (hU i).1 hY ((U i).ι ≫ p)))
    (_ : Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor (W.preimage p).ι) ⊆
        ⋃ i, Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)),
    HasSectionCovers hY f hf W hW hfW (Space.pointsMap B S hS Y' p ''
      Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι)) := by
  intro n
  induction n with
  | zero =>
    intro Y' hY' _ _ p _ V' hV' _ _ hV'W U hU _ _ x _ hcov
    refine HasSectionCovers.empty.mono ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈
        Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor (W.preimage p).ι) := by
      obtain ⟨z, rfl⟩ := hv
      exact ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe hV'W) z, by
        rw [← Space.pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩
    obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hcov hv')
    exact i.elim0
  | succ n ih =>
    intro Y' hY' hY'qc hY'qs p hp V' hV' hV'qc hV'V hV'W U hU hUqc hUW x ex hcov
    let := Space.pointTopology B S hS Y'
    have := Space.quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y' hY' hY'qs
    have hUo : ∀ i, _root_.IsOpen
        (Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)) := fun i =>
      Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (U i).ι (hU i).2
    have hV'o : _root_.IsOpen (Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι)) :=
      Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS V'.ι hV'.2
    -- the points of `V'` in all the `U i`
    let T₀ := Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) ∩
      ⋂ i, Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)
    have hT₀o : _root_.IsOpen T₀ := hV'o.inter (isOpen_iInter_of_finite hUo)
    have hT₀c : IsCompact T₀ := by
      have h := QuasiSeparatedSpace.isCompact_sInter_of_nonempty
        ((Set.finite_range fun i =>
          Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)).insert
            (Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι)))
        (Set.insert_nonempty _ _)
        (Set.forall_mem_insert.2 ⟨Or.inl hV'o, Set.forall_mem_range.2 fun i => Or.inl (hUo i)⟩)
        (Set.forall_mem_insert.2 ⟨Space.isCompact_range_of_isQuasiCompactSpace B S hS hV' hV'qc,
          Set.forall_mem_range.2 fun i =>
            Space.isCompact_range_of_isQuasiCompactSpace B S hS (hU i) (hUqc i)⟩)
      rwa [Set.sInter_insert, Set.sInter_range] at h
    obtain ⟨V₀, hV₀, hV₀r⟩ := Space.exists_isOpenSubspace_range_pointsMap_eq B S hS hY' T₀ hT₀o
    have hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor :=
      Space.isQuasiCompactSpace_of_isCompact_range B S hS hY' hV₀ (hV₀r ▸ hT₀c)
    have hV₀V' : V₀ ≤ V' := Space.le_of_range_pointsMap_ι_subset B S hS hV' (by
      rw [hV₀r]; exact Set.inter_subset_left)
    have hV₀U : ∀ i, V₀ ≤ U i := fun i => Space.le_of_range_pointsMap_ι_subset B S hS (hU i) (by
      rw [hV₀r]; exact Set.inter_subset_right.trans (Set.iInter_subset _ i))
    -- the points of `V'` in all the `U i`
    have hmain := hasSectionCovers_of_sections_of_isGerbeOver f hf W hW hfW V hV hG n hY'
      hY'qc hY'qs p hp V₀ (U 0) hV₀ hV₀qc (hV₀V'.trans hV'V) (hU 0) (hUqc 0) (hUW 0) (hV₀U 0)
      (x 0) (ex 0) (fun i => U i.succ) (fun i => hU i.succ) (fun i => hUqc i.succ)
      (fun i => hUW i.succ) (fun i => hV₀U i.succ) (fun i => x i.succ) (fun i => ex i.succ) (by
        intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hy)
        exact Fin.cases (fun h => Or.inl h) (fun j h => Or.inr (Set.mem_iUnion.2 ⟨j, h⟩)) i hi)
    -- the points of `V'` outside `U i`, on the reduced closed complement of `U i`
    have hcomp : ∀ i, HasSectionCovers hY f hf W hW hfW (Space.pointsMap B S hS Y' p ''
        (Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) \
          Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι))) := by
      intro i
      let C := Space.reducedClosedSubspace B S hS Y' hY'
        (Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι))ᶜ (hUo i).isClosed_compl
      have hC : Space.IsClosedSubspace B S hS C :=
        Space.isClosedSubspace_reducedClosedSubspace B S hS Y' hY' _ _
      have hCr : Set.range (Space.pointsMap B S hS C.toFunctor C.ι) =
          (Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι))ᶜ :=
        Space.range_pointsMap_ι_reducedClosedSubspace B S hS Y' hY' _ _
      have hCp : Space.IsProper B S hS C.ι :=
        Space.isProper_of_isClosedImmersion B S hS hC.1 hY' C.ι hC.2
      obtain ⟨hCqc, hCqs⟩ :=
        isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isProper hC.1 hY' hY'qc hY'qs hCp
      have hpre : ∀ {O' : Subfunctor Y'}, Space.IsOpenSubspace B S hS O' →
          Space.IsOpenSubspace B S hS (O'.preimage C.ι) := fun hO' =>
        Space.isOpenSubspace_preimage B S hS C.ι _ hY' hC.1 hO'
      have hpreqc : ∀ {O' : Subfunctor Y'} (hO' : Space.IsOpenSubspace B S hS O'),
          Space.IsQuasiCompactSpace B S hS O'.toFunctor →
          Space.IsQuasiCompactSpace B S hS (O'.preimage C.ι).toFunctor := fun hO' hO'qc =>
        Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY' hC.1 C.ι hCp.2.1.2 hO'
          hO'qc
      have h := ih hC.1 hCqc hCqs (C.ι ≫ p) (Space.isProper_comp B S hS hC.1 hY' hY C.ι p hCp hp)
        (V'.preimage C.ι) (hpre hV') (hpreqc hV' hV'qc) (fun T _ h => hV'V T h)
        (fun T _ h => hV'W T h) (fun j => (U (i.succAbove j)).preimage C.ι)
        (fun j => hpre (hU _)) (fun j => hpreqc (hU _) (hUqc _)) (fun j T _ h => hUW _ T h)
        (fun j => algebraicSpaceStackMap.{u, w} B S hS (hpre (hU _)).1 (hU _).1
          ((U (i.succAbove j)).fromPreimage C.ι) ≫ x (i.succAbove j))
        (fun j => (ex _).map fun e => pullbackSectionIso f hY' hC.1 p C.ι (hU _) _ e) (by
          intro y hy
          obtain ⟨k, hk⟩ := Set.mem_iUnion.1
            (hcov (pointsMap_mem_range_preimage_ι_of_comp C.ι p W hy))
          have hki : k ≠ i := by
            rintro rfl
            have : Space.pointsMap B S hS _ C.ι y ∈
                Set.range (Space.pointsMap B S hS C.toFunctor C.ι) := ⟨y, rfl⟩
            rw [hCr] at this
            exact this hk
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
          refine Set.mem_iUnion.2 ⟨j, ?_⟩
          rwa [Space.range_pointsMap_preimage_ι])
      refine h.mono ?_
      rintro _ ⟨v, ⟨hv, hvU⟩, rfl⟩
      have hvC : v ∈ Set.range (Space.pointsMap B S hS C.toFunctor C.ι) := by rwa [hCr]
      obtain ⟨c, rfl⟩ := hvC
      refine ⟨c, ?_, Space.pointsMap_comp_apply B S hS _ _ _⟩
      rwa [Space.range_pointsMap_preimage_ι]
    refine (hmain.union (HasSectionCovers.iUnion _ hcomp)).mono ?_
    rintro _ ⟨v, hv, rfl⟩
    by_cases h : ∀ i, v ∈ Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι)
    · left
      refine ⟨v, ?_, rfl⟩
      rw [hV₀r]
      exact ⟨hv, Set.mem_iInter.2 h⟩
    · obtain ⟨i, hi⟩ := not_forall.1 h
      exact Or.inr (Set.mem_iUnion.2 ⟨i, v, ⟨hv, hi⟩, rfl⟩)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
