module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowRelativeSections

/-!
# Gluing two sections of a separated stack after an admissible blowup

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space, and let
`x₀ : U₀ ⟶ 𝒳`, `x₁ : U₁ ⟶ 𝒳` be 1-morphisms over `Y` out of quasi-compact opens of a
quasi-compact quasi-separated algebraic space `Y'` over `Y`, 2-isomorphic over a quasi-compact
open `V ⊆ U₀ ∩ U₁`. After a `V`-admissible blowup `b : Y'' ⟶ Y'` the two sections are
2-isomorphic over `b⁻¹(U₀ ∩ U₁)` ([Stacks, Tag 0CPI],
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_isAdmissibleBlowup_iso_of_iso`), and two sections
glue without a cocycle condition (`AlgebraicGeometry.Stack.AlgebraicStacks.exists_hom_of_two_le`),
so they glue to one section over an open with the points of `b⁻¹(U₀) ∪ b⁻¹(U₁)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_restrict_two_le`: two 1-morphisms into the stack
  of an algebraic space agreeing on two opens agree on their union.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_glued_section_of_iso`: two sections isomorphic
  over `V` glue after a `V`-admissible blowup.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Two 1-morphisms into the stack of an algebraic space agreeing on two opens covering an
open `Z` agree on `Z`.** -/
theorem eq_of_restrict_two_le {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hY : IsAlgebraicSpace B S hS Y) {Z U₀ U₁ : Subfunctor T}
    (hZ : Space.IsOpenSubspace B S hS Z) (hU₀ : Space.IsOpenSubspace B S hS U₀)
    (hU₁ : Space.IsOpenSubspace B S hS U₁) (h₀ : U₀ ≤ Z) (h₁ : U₁ ≤ Z)
    (hcov : Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) ⊆
      Set.range (Space.pointsMap B S hS U₀.toFunctor U₀.ι) ∪
        Set.range (Space.pointsMap B S hS U₁.toFunctor U₁.ι))
    (g g' : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZ.1 ⟶
      algebraicSpaceStack.{u, w} B S hS Y hY)
    (e₀ : algebraicSpaceStackMap.{u, w} B S hS hU₀.1 hZ.1 (Subfunctor.homOfLe h₀) ≫ g ≅
      algebraicSpaceStackMap.{u, w} B S hS hU₀.1 hZ.1 (Subfunctor.homOfLe h₀) ≫ g')
    (e₁ : algebraicSpaceStackMap.{u, w} B S hS hU₁.1 hZ.1 (Subfunctor.homOfLe h₁) ≫ g ≅
      algebraicSpaceStackMap.{u, w} B S hS hU₁.1 hZ.1 (Subfunctor.homOfLe h₁) ≫ g') :
    g = g' := by
  let r := representingMap B S hS _ _ Z.toFunctor Y
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) g.hom
  let r' := representingMap B S hS _ _ Z.toFunctor Y
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) g'.hom
  have hr : algebraicSpaceStackMap.{u, w} B S hS hZ.1 hY r = g :=
    algebraicSpaceStackMap_representingMap hZ.1 hY g
  have hr' : algebraicSpaceStackMap.{u, w} B S hS hZ.1 hY r' = g' :=
    algebraicSpaceStackMap_representingMap hZ.1 hY g'
  have hk : ∀ {U : Subfunctor T} (hU : Space.IsOpenSubspace B S hS U) (h : U ≤ Z),
      (algebraicSpaceStackMap.{u, w} B S hS hU.1 hZ.1 (Subfunctor.homOfLe h) ≫ g ≅
        algebraicSpaceStackMap.{u, w} B S hS hU.1 hZ.1 (Subfunctor.homOfLe h) ≫ g') →
      (U.preimage Z.ι).ι ≫ r = (U.preimage Z.ι).ι ≫ r' := by
    intro U hU h e
    have hUZ : Subfunctor.homOfLe h ≫ r = Subfunctor.homOfLe h ≫ r' := by
      refine eq_of_algebraicSpaceStackMap_eq hU.1 hY ?_
      rw [algebraicSpaceStackMap_comp_eq hU.1 hZ.1 hY, algebraicSpaceStackMap_comp_eq hU.1 hZ.1 hY,
        hr, hr']
      exact eq_of_iso_algebraicSpaceStack hY e
    have hfac : (U.preimage Z.ι).ι = U.fromPreimage Z.ι ≫ Subfunctor.homOfLe h := rfl
    rw [hfac, Category.assoc, Category.assoc, hUZ]
  let V : ULift.{u} Bool → Subfunctor Z.toFunctor := fun k =>
    bif k.down then U₁.preimage Z.ι else U₀.preimage Z.ι
  have hV : ∀ k, Space.IsOpenSubspace B S hS (V k) := fun k => by
    rcases k with ⟨_ | _⟩
    exacts [Space.isOpenSubspace_preimage B S hS Z.ι U₀ hT hZ.1 hU₀,
      Space.isOpenSubspace_preimage B S hS Z.ι U₁ hT hZ.1 hU₁]
  have hcovV : Space.IsZariskiCover B S hS (ULift.{u} Bool) V := by
    refine (Space.isZariskiCover_iff_iUnion_points B S hS _ hZ.1 _ V hV).2
      (Set.eq_univ_of_forall fun z => ?_)
    exact (hcov ⟨z, rfl⟩).elim
      (fun hz => Set.mem_iUnion.2 ⟨⟨false⟩,
        (Space.range_pointsMap_preimage_ι B S hS Z.ι U₀).ge hz⟩)
      fun hz => Set.mem_iUnion.2 ⟨⟨true⟩, (Space.range_pointsMap_preimage_ι B S hS Z.ι U₁).ge hz⟩
  have hrr : r = r' := Space.hom_ext_of_isZariskiCover B S hS V hcovV hY.isSheaf r r' fun k => by
    rcases k with ⟨_ | _⟩
    · exact hk hU₀ h₀ e₀
    · exact hk hU₁ h₁ e₁
  rw [← hr, ← hr', hrr]

section Induction

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **A section over an open pulls back along a morphism of the base.** If `x : U ⟶ 𝒳` lies
over `U ⟶ Y' ⟶ Y`, then its restriction along `b⁻¹(U) ⟶ U` lies over `b⁻¹(U) ⟶ Y'' ⟶ Y`. -/
def pullbackSectionIso {Y' Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (hY'' : IsAlgebraicSpace B S hS Y'') (p : Y' ⟶ Y)
    (b : Y'' ⟶ Y') {U : Subfunctor Y'} (hU : Space.IsOpenSubspace B S hS U)
    (x : algebraicSpaceStack.{u, w} B S hS U.toFunctor hU.1 ⟶ 𝒳)
    (ex : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p)) :
    (algebraicSpaceStackMap.{u, w} B S hS (Space.isOpenSubspace_preimage B S hS b U hY' hY'' hU).1
        hU.1 (U.fromPreimage b) ≫ x) ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS (Space.isOpenSubspace_preimage B S hS b U hY' hY'' hU).1
        hY ((U.preimage b).ι ≫ b ≫ p) :=
  α_ _ _ _ ≪≫ whiskerLeftIso _ ex ≪≫
    eqToIso ((algebraicSpaceStackMap_comp_eq _ hU.1 hY _ _).symm.trans
      (congrArg _ (by rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc])))

/-- Restricting a section over an open `U` of `Y'` to a space `W` mapping to `U` gives a section
over `Y` along any `q : W ⟶ Y` equal to the composite `W ⟶ U ⟶ Y' ⟶ Y`. -/
private def restrictSectionIso {Y' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : Y' ⟶ Y}
    {U : Subfunctor Y'} (hU : Space.IsOpenSubspace B S hS U) (hW : IsAlgebraicSpace B S hS W)
    (k : W ⟶ U.toFunctor) (q : W ⟶ Y) (hq : k ≫ U.ι ≫ p = q)
    (x : algebraicSpaceStack.{u, w} B S hS U.toFunctor hU.1 ⟶ 𝒳)
    (ex : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p)) :
    (algebraicSpaceStackMap.{u, w} B S hS hW hU.1 k ≫ x) ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS hW hY q :=
  α_ _ _ _ ≪≫ whiskerLeftIso _ ex ≪≫
    eqToIso ((algebraicSpaceStackMap_comp_eq _ hU.1 hY _ _).symm.trans (congrArg _ hq))

/-- Two factorizations of one morphism of algebraic spaces give equal composites of the induced
1-morphisms. -/
theorem algebraicSpaceStackMap_comp_eq_of_eq {X₁ X₂ X₂' X₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h₁ : IsAlgebraicSpace B S hS X₁) (h₂ : IsAlgebraicSpace B S hS X₂)
    (h₂' : IsAlgebraicSpace B S hS X₂') (h₃ : IsAlgebraicSpace B S hS X₃) (g : X₁ ⟶ X₂)
    (g' : X₂ ⟶ X₃) (k : X₁ ⟶ X₂') (k' : X₂' ⟶ X₃) (h : g ≫ g' = k ≫ k') :
    algebraicSpaceStackMap.{u, w} B S hS h₁ h₂ g ≫ algebraicSpaceStackMap.{u, w} B S hS h₂ h₃ g' =
      algebraicSpaceStackMap.{u, w} B S hS h₁ h₂' k ≫
        algebraicSpaceStackMap.{u, w} B S hS h₂' h₃ k' := by
  rw [← algebraicSpaceStackMap_comp_eq, ← algebraicSpaceStackMap_comp_eq, h]

variable (hf : IsSeparated B S hS f)

include hf in
/-- **Gluing two sections isomorphic over `V`, after a `V`-admissible blowup.** Let `x₀ : U₀ ⟶ 𝒳`
and `x₁ : U₁ ⟶ 𝒳` be 1-morphisms over `Y` out of quasi-compact opens of `Y'`, 2-isomorphic over a
quasi-compact open `V ⊆ U₀ ∩ U₁`. Then there are a `V`-admissible blowup `b : Y'' ⟶ Y'`, an open
`Z ⊆ Y''` with the points of `b⁻¹(U₀) ∪ b⁻¹(U₁)` and a 1-morphism `G : Z ⟶ 𝒳` over `Y` restricting
to the pullback of `x₀` on `b⁻¹(U₀)`. -/
theorem exists_glued_section_of_iso {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (hY'qc : Space.IsQuasiCompactSpace B S hS Y')
    (hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y') (p : Y' ⟶ Y)
    (V U₀ U₁ : Subfunctor Y') (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor) (hU₀ : Space.IsOpenSubspace B S hS U₀)
    (hU₀qc : Space.IsQuasiCompactSpace B S hS U₀.toFunctor) (hU₁ : Space.IsOpenSubspace B S hS U₁)
    (hU₁qc : Space.IsQuasiCompactSpace B S hS U₁.toFunctor) (hVU₀ : V ≤ U₀) (hVU₁ : V ≤ U₁)
    (x₀ : algebraicSpaceStack.{u, w} B S hS U₀.toFunctor hU₀.1 ⟶ 𝒳)
    (ex₀ : Nonempty (x₀ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU₀.1 hY (U₀.ι ≫ p)))
    (x₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor hU₁.1 ⟶ 𝒳)
    (ex₁ : Nonempty (x₁ ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU₁.1 hY (U₁.ι ≫ p)))
    (φ₁ : algebraicSpaceStackMap.{u, w} B S hS hV.1 hU₀.1 (Subfunctor.homOfLe hVU₀) ≫ x₀ ≅
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hU₁.1 (Subfunctor.homOfLe hVU₁) ≫ x₁) :
    ∃ (Y'' : AlgebraicSpaces B S hS) (bl : Y'' ⟶ ⟨Y', hY'⟩),
      Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ bl ∧
      ∃ (Z : Subfunctor Y''.1) (hZ : Space.IsOpenSubspace B S hS Z)
        (hZ₀ : U₀.preimage bl.hom ≤ Z) (_ : U₁.preimage bl.hom ≤ Z),
        Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) =
          Set.range (Space.pointsMap B S hS (U₀.preimage bl.hom).toFunctor
            (U₀.preimage bl.hom).ι) ∪
            Set.range (Space.pointsMap B S hS (U₁.preimage bl.hom).toFunctor
              (U₁.preimage bl.hom).ι) ∧
        ∃ G : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZ.1 ⟶ 𝒳,
          Nonempty (G ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ.1 hY (Z.ι ≫ bl.hom ≫ p)) ∧
          Nonempty (algebraicSpaceStackMap.{u, w} B S hS
              (Space.isOpenSubspace_preimage B S hS bl.hom U₀ hY' Y''.2 hU₀).1 hZ.1
              (Subfunctor.homOfLe hZ₀) ≫ G ≅
            algebraicSpaceStackMap.{u, w} B S hS
              (Space.isOpenSubspace_preimage B S hS bl.hom U₀ hY' Y''.2 hU₀).1 hU₀.1
              (U₀.fromPreimage bl.hom) ≫ x₀) := by
  obtain ⟨e₀⟩ := ex₀
  obtain ⟨e₁⟩ := ex₁
  have hInt := Space.isOpenSubspace_inf B S hS hY' U₀ U₁ hU₀ hU₁
  have hIntqc := Space.isQuasiCompactSpace_inf hY' hY'qs hU₀ hU₁ hU₀qc hU₁qc
  have hVInt : V ≤ U₀ ⊓ U₁ := le_inf hVU₀ hVU₁
  let xa := algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₀.1 (Subfunctor.homOfLe inf_le_left) ≫ x₀
  let xb := algebraicSpaceStackMap.{u, w} B S hS hInt.1 hU₁.1 (Subfunctor.homOfLe inf_le_right) ≫
    x₁
  have ea := restrictSectionIso f hU₀ hInt.1 (Subfunctor.homOfLe inf_le_left) _
    (by rw [← Category.assoc, Subfunctor.homOfLe_ι]) x₀ e₀
  have eb := restrictSectionIso f hU₁ hInt.1 (Subfunctor.homOfLe inf_le_right) _
    (by rw [← Category.assoc, Subfunctor.homOfLe_ι]) x₁ e₁
  have ψ : algebraicSpaceStackMap.{u, w} B S hS hV.1 hInt.1 (Subfunctor.homOfLe hVInt) ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hInt.1 (Subfunctor.homOfLe hVInt) ≫ xb :=
    (α_ _ _ _).symm ≪≫ eqToIso (congrArg (· ≫ x₀)
      (algebraicSpaceStackMap_comp_eq hV.1 hInt.1 hU₀.1 _ _).symm) ≪≫ φ₁ ≪≫
      eqToIso (congrArg (· ≫ x₁) (algebraicSpaceStackMap_comp_eq hV.1 hInt.1 hU₁.1
        (Subfunctor.homOfLe hVInt) (Subfunctor.homOfLe inf_le_right))) ≪≫
      α_ _ _ _
  obtain ⟨Y'', bl, hbl, ⟨Ψ⟩⟩ := exists_isAdmissibleBlowup_iso_of_iso hY f hf hY' hY'qc hY'qs p
    (U₀ ⊓ U₁) V hInt hV hIntqc hVqc hVInt xa xb ea eb ψ
  have hblp : Space.IsProper B S hS bl.hom := hbl.isProper
  have hY''qc : Space.IsQuasiCompactSpace B S hS Y''.1 :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY' hY'qc hblp.2.1.2
  have hY''qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y''.1 :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal Y''.2 hY'qs
      (Space.isQuasiSeparated_of_isSeparated B S hS hblp.1)
  have hpre : ∀ {O : Subfunctor Y'}, Space.IsOpenSubspace B S hS O →
      Space.IsOpenSubspace B S hS (O.preimage bl.hom) := fun hO =>
    Space.isOpenSubspace_preimage B S hS bl.hom _ hY' Y''.2 hO
  have hpreqc : ∀ {O : Subfunctor Y'} (hO : Space.IsOpenSubspace B S hS O),
      Space.IsQuasiCompactSpace B S hS O.toFunctor →
      Space.IsQuasiCompactSpace B S hS (O.preimage bl.hom).toFunctor := fun hO hOqc =>
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY' Y''.2 bl.hom hblp.2.1.2 hO
      hOqc
  obtain ⟨Z, hZ, hZ₀, hZ₁, hZrange⟩ := Space.exists_openSubspace_range_eq_union B S hS Y''.2
    (hpre hU₀) (hpre hU₁)
  let x₀' := algebraicSpaceStackMap.{u, w} B S hS (hpre hU₀).1 hU₀.1 (U₀.fromPreimage bl.hom) ≫ x₀
  let x₁' := algebraicSpaceStackMap.{u, w} B S hS (hpre hU₁).1 hU₁.1 (U₁.fromPreimage bl.hom) ≫
    x₁
  have hInt'' := (Space.isOpenSubspace_inf B S hS Y''.2 _ _ (hpre hU₀) (hpre hU₁)).1
  have hk₀ : (Subfunctor.homOfLe inf_le_left ≫ U₀.fromPreimage bl.hom :
      (U₀.preimage bl.hom ⊓ U₁.preimage bl.hom).toFunctor ⟶ U₀.toFunctor) =
      (U₀ ⊓ U₁).fromPreimage bl.hom ≫ Subfunctor.homOfLe inf_le_left := rfl
  have hk₁ : (Subfunctor.homOfLe inf_le_right ≫ U₁.fromPreimage bl.hom :
      (U₀.preimage bl.hom ⊓ U₁.preimage bl.hom).toFunctor ⟶ U₁.toFunctor) =
      (U₀ ⊓ U₁).fromPreimage bl.hom ≫ Subfunctor.homOfLe inf_le_right := rfl
  have ψ' : algebraicSpaceStackMap.{u, w} B S hS hInt'' (hpre hU₀).1
        (Subfunctor.homOfLe inf_le_left) ≫ x₀' ≅
      algebraicSpaceStackMap.{u, w} B S hS hInt'' (hpre hU₁).1
        (Subfunctor.homOfLe inf_le_right) ≫ x₁' :=
    (α_ _ _ _).symm ≪≫ eqToIso (congrArg (· ≫ x₀) (algebraicSpaceStackMap_comp_eq_of_eq
        hInt'' (hpre hU₀).1 hInt.1 hU₀.1 _ _ _ _ hk₀)) ≪≫ α_ _ _ _ ≪≫ Ψ ≪≫ (α_ _ _ _).symm ≪≫
      eqToIso (congrArg (· ≫ x₁) (algebraicSpaceStackMap_comp_eq_of_eq
        hInt'' hInt.1 (hpre hU₁).1 hU₁.1 _ _ _ _ hk₁.symm)) ≪≫ α_ _ _ _
  obtain ⟨G, ⟨i₀⟩, ⟨i₁⟩⟩ := exists_hom_of_two_le Y''.2 hZ (hpre hU₀) (hpre hU₁) hZ₀ hZ₁
    hZrange.subset x₀' x₁' ψ'
  have e₀' := pullbackSectionIso f hY' Y''.2 p bl.hom hU₀ x₀ e₀
  have e₁' := pullbackSectionIso f hY' Y''.2 p bl.hom hU₁ x₁ e₁
  have eG : G ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hZ.1 hY (Z.ι ≫ bl.hom ≫ p) := by
    refine eqToIso (eq_of_restrict_two_le Y''.2 hY hZ (hpre hU₀) (hpre hU₁) hZ₀ hZ₁
      hZrange.subset _ _ ?_ ?_)
    · exact (α_ _ _ _).symm ≪≫ whiskerRightIso i₀ f ≪≫ e₀' ≪≫ eqToIso
        ((congrArg _ (by rw [← Subfunctor.homOfLe_ι hZ₀]; simp only [Category.assoc])).trans
          (algebraicSpaceStackMap_comp_eq _ _ _ _ _))
    · exact (α_ _ _ _).symm ≪≫ whiskerRightIso i₁ f ≪≫ e₁' ≪≫ eqToIso
        ((congrArg _ (by rw [← Subfunctor.homOfLe_ι hZ₁]; simp only [Category.assoc])).trans
          (algebraicSpaceStackMap_comp_eq _ _ _ _ _))
  exact ⟨Y'', bl, hbl, Z, hZ, hZ₀, hZ₁, hZrange, G, ⟨eG⟩, ⟨i₀⟩⟩

end Induction

end AlgebraicGeometry.Stack.AlgebraicStacks

end
