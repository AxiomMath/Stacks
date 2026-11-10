module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.ExtendIsos
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Flattening
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Glue
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.InitialSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.IsomGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.IsomProper
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.LocalIsos
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.LocalPieces
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Union
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective

/-!
# Stacks 0CQ7 from the statements of Stacks 0CQ4, 0CQ6 and 0CPI

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite type from an algebraic stack to a
quasi-compact and quasi-separated algebraic space and `V ⊆ Y` a quasi-compact open over which `𝒳`
is a gerbe. [Stacks, Tag 0CQ7] gives a diagram `Z̄ ⟵ Z ⟶ 𝒳` over `Y` with `Z ⟶ Z̄` an open
immersion, `Z̄ ⟶ Y` and `Z ⟶ 𝒳` proper, and `|V|` in the image of `|Z|`
(`HasProperCompactifiableCover`). This file assembles the source's proof from the steps in this
directory; the three results of other chapters it uses enter as explicit hypotheses, in the
statements under which they are registered: Stacks 0CQ4 (`h0CQ4`, flattening by an admissible
blowup), Stacks 0CQ6 (`h0CQ6`, Zariski local sections after a finite surjective base change)
and Stacks 0CPI (`h0CPI`, extending a section after an admissible blowup).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.hasSectionCoverOver_of_le`: situation
  (d) of the proof, where `V` lies in every `Wᵢ`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_isFlat_of`: the case
  of a flat `f` of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasProperCompactifiableCover_of_isGerbeOver_of`:
  Stacks 0CQ7, from the statements of Stacks 0CQ4, 0CQ6 and 0CPI.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Situation (d) of the proof of Stacks 0CQ7.** Over a quasi-compact quasi-separated base
`q₀ : Y₀ ⟶ Y`, a family of local sections and a quasi-compact open `V₀` lying over the gerbe
locus `V` and in every open of the family have a section cover: Stacks 0CQ6 makes the sections
Zariski locally isomorphic over `V₀` (`exists_finite_cover_localIsos`), which gives compatible
isomorphisms on pieces of `V₀` (`hasSectionCoverOver_of_localIsos`); Stacks 0CPI extends them to
the overlaps (`exists_isos_of_isosOn`), and they glue (`hasSectionCoverOver_of_isos`). -/
theorem SectionFamily.hasSectionCoverOver_of_le
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1),
      IsSurjective B S hS f → AlgebraicStacks.IsFlat B S hS f →
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS},
      Space.IsQuasiCompactSpace B S hS Y.1 →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1),
      Space.IsQuasiCompactSpace B S hS U.1.toFunctor →
      Space.IsQuasiCompactSpace B S hS W.1.toFunctor →
      ∀ (f : X ⟶ Space.openSubspace B S hS Y W), Space.IsProper B S hS f.hom →
      ∀ (s : U.1.toFunctor ⟶ X.1), s ≫ f.hom = Subfunctor.homOfLe hUW →
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
    (hf : IsSeparated B S hS f) (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    {W : Subfunctor Y} (hW : Space.IsOpenSubspace B S hS W) (hVW : V ≤ W)
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀) (q₀ : Y₀ ⟶ Y)
    {n : ℕ} (F : SectionFamily hY f W hY₀ q₀ (Fin n))
    (hY₀qc : Space.IsQuasiCompactSpace B S hS Y₀)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    (V₀ : Subfunctor Y₀) (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i)
    (hV₀V : V₀ ≤ V.preimage q₀) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  have hproper := fun Z hZ x₁ x₂ h =>
    isProper_isomSpaceOverSpaceProj_of_isSeparated B S hS hY f hf Z hZ x₁ x₂ h
  have hgerbe := fun Z hZ x₁ x₂ g h₁ h₂ =>
    isSurjective_isFlat_isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_isGerbeOver
      B S hS hY f V hV hG Z hZ x₁ x₂ g h₁ h₂
  have hV₀W : V₀ ≤ W.preimage q₀ := fun T y hy => hVW _ (hV₀V T hy)
  cases n with
  | zero =>
    exact F.hasSectionCoverOver_of_isos hW hproper hY₀qs V₀ hV₀ hV₀qc hVU hV₀W
      (fun i => i.elim0) (fun i => i.elim0)
  | succ m =>
    obtain ⟨Y₁, hY₁, r, hr, hrs, hY₁qc, hY₁qs, hloc⟩ :=
      F.exists_finite_cover_localIsos h0CQ6 V hV hgerbe hY₀qc hY₀qs V₀ hV₀ hV₀qc hVU hV₀V
    set F₁ := F.restrict hY₁ r hr.2.1.2
    have hV₁ : Space.IsOpenSubspace B S hS (V₀.preimage r) :=
      Space.isOpenSubspace_preimage B S hS r V₀ hY₀ hY₁ hV₀
    have hV₁qc : Space.IsQuasiCompactSpace B S hS (V₀.preimage r).toFunctor :=
      Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hY₁ r hr.2.1.2 hV₀ hV₀qc
    have hVU₁ : ∀ i, V₀.preimage r ≤ F₁.U i := fun i T y hy => hVU i T hy
    have h₁ : HasSectionCoverOver hY f W hW hY₁ (r ≫ q₀) (V₀.preimage r) := by
      refine F₁.hasSectionCoverOver_of_localIsos hW
        (fun V₁ V₂ V' h₁ h₂ h => h₁.union h₂ h) (fun V' h => HasSectionCoverOver.of_isEmpty h)
        (V₀.preimage r) hV₁ hV₁qc hVU₁ ?_ ?_
      · intro y hy j
        have hy' : Space.pointsMap B S hS Y₁ r y ∈
            Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) := by
          rw [Space.range_pointsMap_preimage_ι] at hy
          exact hy
        exact hloc y hy' 0 j
      · intro N hN hNqc hNU φ hcoc
        obtain ⟨Y₂, hY₂, r₂, hr₂, -, hY₂qs, hpts, hVU', φ', hcoc'⟩ :=
          F₁.exists_isos_of_isosOn h0CPI hproper hY₁qc hY₁qs N hN hNqc hNU φ hcoc
        have hN₂ : Space.IsOpenSubspace B S hS (N.preimage r₂) :=
          Space.isOpenSubspace_preimage B S hS r₂ N hY₁ hY₂ hN
        have hN₂qc : Space.IsQuasiCompactSpace B S hS (N.preimage r₂).toFunctor :=
          Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₁ hY₂ r₂ hr₂.2.1.2 hN
            hNqc
        have h₂ := (F₁.restrict hY₂ r₂ hr₂.2.1.2).hasSectionCoverOver_of_isos hW hproper hY₂qs
          (N.preimage r₂) hN₂ hN₂qc hVU' (fun T y hy => F.le 0 T (hNU 0 T hy)) φ' hcoc'
        exact HasSectionCoverOver.trans hY₁ hY₂ r₂ hr₂ h₂ hpts
    refine HasSectionCoverOver.trans hY₀ hY₁ r hr h₁ ?_
    rintro _ ⟨v, rfl⟩
    obtain ⟨y, hy⟩ := hrs (Space.pointsMap B S hS _ V₀.ι v)
    refine ⟨y, ?_, hy⟩
    rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hy]
    exact ⟨v, rfl⟩


/-- **The flat case of Stacks 0CQ7.** If moreover `f` is flat and of finite presentation, the
image `W` of `|f|` is a quasi-compact open containing `V`, a finite surjective base change gives a
family of local sections covering `W` (Stacks 0CQ6, `exists_sectionFamily_of_isFlat`), the
induction on their number (`hasSectionCoverOver_of_sectionFamily_of_step`) reduces to situation
(d) (`SectionFamily.hasSectionCoverOver_of_le`), and the resulting section cover gives the
conclusion (`HasSectionCoverOver.hasProperCompactifiableCover`, the last step of the source). -/
theorem hasProperCompactifiableCover_of_isFlat_of
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1),
      IsSurjective B S hS f → AlgebraicStacks.IsFlat B S hS f →
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS},
      Space.IsQuasiCompactSpace B S hS Y.1 →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1),
      Space.IsQuasiCompactSpace B S hS U.1.toFunctor →
      Space.IsQuasiCompactSpace B S hS W.1.toFunctor →
      ∀ (f : X ⟶ Space.openSubspace B S hS Y W), Space.IsProper B S hS f.hom →
      ∀ (s : U.1.toFunctor ⟶ X.1), s ≫ f.hom = Subfunctor.homOfLe hUW →
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (hfl : IsFlat B S hS f)
    (hfp : IsFinitePresentation B S hS f) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨W, hW, hfW, hVle, Y₀, hY₀, g, hgp, hgs, hY₀qc, hY₀qs, n, ⟨F⟩⟩ :=
    exists_sectionFamily_of_isFlat h0CQ6 hY f hft hfl hfp.1 hYqc hYqs
  have hVW : V ≤ W := hVle V hV (isSurjective_of_isGerbeOver B S hS _ hG)
  have hV₀ : Space.IsOpenSubspace B S hS (V.preimage g) :=
    Space.isOpenSubspace_preimage B S hS g V hY hY₀ hV
  have hV₀qc : Space.IsQuasiCompactSpace B S hS (V.preimage g).toFunctor :=
    Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY hY₀ g hgp.2.1.2 hV hVqc
  have hc := hasSectionCoverOver_of_sectionFamily_of_step hW V
    (fun _ _ _ _ _ h₁ h₂ h => h₁.union h₂ h)
    (fun hY₀ q₀ _ F hqc hqs V₀ hV₀ hV₀qc hVU hV₀V =>
      F.hasSectionCoverOver_of_le h0CQ6 h0CPI hsep V hV hG hW hVW hY₀ q₀ hqc hqs V₀ hV₀ hV₀qc
        hVU hV₀V)
    n hY₀ g F hY₀qc hY₀qs (V.preimage g) hV₀ hV₀qc le_rfl
  have hc' : HasSectionCoverOver hY f W hW hY₀ (g ≫ 𝟙 Y) (V.preimage g) := by
    rw [Category.comp_id]
    exact hc
  refine (HasSectionCoverOver.trans hY hY₀ g hgp hc' ?_).hasProperCompactifiableCover hsep hfW
  rintro _ ⟨v, rfl⟩
  obtain ⟨y, hy⟩ := hgs (Space.pointsMap B S hS _ V.ι v)
  refine ⟨y, ?_, hy⟩
  rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hy]
  exact ⟨v, rfl⟩

/-- **[Stacks, Tag 0CQ7], from the statements of Stacks 0CQ4, 0CQ6 and 0CPI.** Let
`f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an open
subspace, such that `f` is separated and of finite type, `Y` is quasi-compact and
quasi-separated, `V` is quasi-compact and `𝒳_V` is a gerbe over `V`. Then there are algebraic
spaces `Z ⊆ Z̄` (an open immersion `j`), a proper `ḡ : Z̄ ⟶ Y` and a proper `h : Z ⟶ 𝒳` with
`f ∘ h ≅ ḡ ∘ j`, such that `|V|` lies in the image of `|Z|` (`HasProperCompactifiableCover`).

The inputs are the statements of Stacks 0CQ4 (`h0CQ4`), Stacks 0CQ6 (`h0CQ6`) and Stacks 0CPI
(`h0CPI`), in the forms in which they are stated; every other step of the source's proof is
proved: the reduction to the flat case (`hasProperCompactifiableCover_of_flat_case`, with Stacks
06QI) and the flat case (`hasProperCompactifiableCover_of_isFlat_of`). The conclusion is exactly
the hypothesis `h0CQ7` of `hasChowCover_of_isNoetherian_of_isReducedStack`. -/
theorem hasProperCompactifiableCover_of_isGerbeOver_of
    (h0CQ4 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      IsFiniteType B S hS f → IsQuasiSeparated B S hS f →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsFlat B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      IsLocallyOfFinitePresentation B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ ⟨Y, hY⟩),
        Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b ∧
        ∃ P : ObjectProperty (twoFibreProductSquare B S hS
            (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj,
          IsClosedSubstack _ P ∧
          (∀ x, ((twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                x).fiber.as ∈ (V.preimage b.hom).obj (Opposite.op ((twoFibreProductSquare B S hS
                  (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                    x).base) →
            P x) ∧
          ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P),
            IsFlat B S hS (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) ∧
            IsFinitePresentation B S hS (fullSubcategoryInclusion _ P hP ≫
              (twoFibreProductSquare B S hS
                (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst))
    (h0CQ6 : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS}
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1),
      IsSurjective B S hS f → AlgebraicStacks.IsFlat B S hS f →
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ Y),
        Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
        ∃ (J : Type u) (W : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (hW : ∀ j, IsAlgebraicSpace B S hS (W j)) (ι : ∀ j, W j ⟶ Y')
          (q : ∀ j, W j ⟶ V.toFunctor)
          (x : ∀ j, algebraicSpaceStack.{u, w} B S hS (W j) (hW j) ⟶ 𝒳),
          (∀ j, Space.IsOpenImmersion B S hS (ι j)) ∧ (∀ j, ι j ≫ g = q j ≫ V.ι) ∧
          (∀ y : Space.points B S hS Y',
            Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι) →
              ∃ j, y ∈ Set.range (Space.pointsMap B S hS (W j) (ι j))) ∧
          ∀ j, Nonempty (x j ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS (hW j) hV.1 (q j)))
    (h0CPI : ∀ {X Y : AlgebraicSpaces B S hS},
      Space.IsQuasiCompactSpace B S hS Y.1 →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 →
      ∀ (U W : Space.OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1),
      Space.IsQuasiCompactSpace B S hS U.1.toFunctor →
      Space.IsQuasiCompactSpace B S hS W.1.toFunctor →
      ∀ (f : X ⟶ Space.openSubspace B S hS Y W), Space.IsProper B S hS f.hom →
      ∀ (s : U.1.toFunctor ⟶ X.1), s ≫ f.hom = Subfunctor.homOfLe hUW →
      ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), Space.IsAdmissibleBlowup B S hS U b ∧
        ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1, s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
            U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' = U.1.fromPreimage b.hom ≫ s)
    : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSeparated B S hS f → IsFiniteType B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
        HasProperCompactifiableCover.{u, w} B S hS hY f V :=
  fun _ hY _ f V hV hsep hft hYqc hYqs hVqc hG =>
    hasProperCompactifiableCover_of_flat_case B S hS h0CQ4
      (fun _ hY _ f V hV hsep hft hfl hfp hYqc hYqs hVqc hG =>
        hasProperCompactifiableCover_of_isFlat_of h0CQ6 h0CPI hY f V hV hsep hft hfl hfp hYqc
          hYqs hVqc hG)
      hY f V hV hsep hft hYqc hYqs hVqc hG

end AlgebraicGeometry.Stack.AlgebraicStacks

end
