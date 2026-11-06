module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorizationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionIsomExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.InnerSquareOfOuterTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Two sections over a gerbe locus are locally isomorphic after a finite cover

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space which is
a gerbe over an open `V ⊆ Y`, let `p : Y' ⟶ Y` be a morphism from a quasi-compact
quasi-separated algebraic space and let `x_a, x_b : U ⟶ 𝒳` be two 1-morphisms over `Y` out of an
open `U ⊆ Y'`. Over a quasi-compact open `V' ⊆ U ∩ p⁻¹(V)` the isomorphism space of `x_a` and `x_b`
is surjective, flat and locally of finite presentation (the relative diagonal of a gerbe is, by
Stacks 0CPR; here it is read as the base change of a section of a gerbe, which is flat, locally of
finite presentation and surjective). So by [Stacks, Tag 0CQ6] there is a finite surjective
`g : Y'' ⟶ Y'` such that `x_a` and `x_b` become isomorphic on the members of an open covering of
`g⁻¹(V')`. This is the step "(d) ⟹ (e)" of the proof of [Stacks, Tag 0CQ7].

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_baseChangeSquare_fst`: the base change
  of a gerbe over `V` along a morphism into `V` is a gerbe.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_of_section_of_isGerbeOver`: a section of
  a gerbe is surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_finite_cover_iso_of_isGerbeOver`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A section of a gerbe is surjective.** The gerbe is injective on points (Stacks 06R9), and
the section followed by the gerbe is the identity on points. -/
theorem isSurjective_of_section_of_isGerbeOver {𝒲 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (π : 𝒲 ⟶ 𝒵) (s : 𝒵 ⟶ 𝒲) (e : s ≫ π ≅ 𝟙 𝒵) (hπ : IsGerbeOver B S hS π) :
    IsSurjective B S hS s := by
  intro y
  let := pointTopology B S hS 𝒲.val
  let := pointTopology B S hS 𝒵.val
  refine ⟨pointsMap B S hS π y, (isHomeomorph_pointsMap_of_isGerbeOver B S hS π hπ).injective ?_⟩
  have h := congrFun (AlgebraicStacks.pointsMap_eq_of_iso B S hS e) (pointsMap B S hS π y)
  rw [pointsMap_comp] at h
  exact h.trans (congrFun (pointsMap_id B S hS 𝒵) _)

/-- The isomorphism space of two sections of a gerbe is surjective, flat and locally of finite
presentation over the base. -/
theorem isSurjective_isFlat_isLocallyOfFinitePresentation_twoFibreProductSquare_fst
    {𝒲 𝒵 : AlgebraicStacks.{u, w} B S hS} (π : 𝒲 ⟶ 𝒵) (hπ : IsGerbeOver B S hS π)
    (sa sb : 𝒵 ⟶ 𝒲) (e : sb ≫ π ≅ 𝟙 𝒵) :
    IsSurjective B S hS (twoFibreProductSquare B S hS sa sb).fst ∧
      IsFlat B S hS (twoFibreProductSquare B S hS sa sb).fst ∧
      IsLocallyOfFinitePresentation B S hS (twoFibreProductSquare B S hS sa sb).fst := by
  have hI := isTwoFibreProduct_twoFibreProductSquare B S hS sa sb
  have hs := isFlat_and_isLocallyOfFinitePresentation_of_section_of_isGerbeOver B S hS π sb e hπ
  exact ⟨isSurjective_fst_of_isTwoFibreProduct B S hS _ hI
      (isSurjective_of_section_of_isGerbeOver π sb e hπ),
    isFlat_baseChange B S hS sb sa _ hI hs.1,
    isLocallyOfFinitePresentation_baseChange B S hS sb sa _ hI hs.2⟩

section BaseChange

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **The base change of a gerbe over `V` along a morphism into `V` is a gerbe.** If `𝒳_V ⟶ V`
is a gerbe and `φ : U ⟶ Y` factors through `V`, then `𝒳 ×_Y U ⟶ U` is a gerbe: it is the base
change of `𝒳_V ⟶ V` along `U ⟶ V` (Stacks 02XD, read backwards), and gerbes are stable under base
change (Stacks 06QE). -/
theorem isGerbeOver_baseChangeSquare_fst (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U) (φ : U ⟶ Y)
    (k : U ⟶ V.toFunctor) (hk : k ≫ V.ι = φ) :
    IsGerbeOver B S hS (baseChangeSquare hY hU φ f).fst := by
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  have hQ : IsTwoFibreProduct Q.swap :=
    isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f)
  let θ : algebraicSpaceStackMap.{u, w} B S hS hU hV.1 k ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι ≅
        algebraicSpaceStackMap.{u, w} B S hS hU hY φ :=
    eqToIso ((Stack.algebraicSpaceStackMap_comp B S hS hU hV.1 hY k V.ι).trans (by rw [hk]))
  let N := (baseChangeSquare hY hU φ f).swap
  let inner := innerSquareOfOuter B S hS Q.swap hQ θ N
  exact isGerbeOver_of_isEquivalence_comp B S hS (𝟙 _) N.snd inner.snd
    (inferInstanceAs (𝟭 _).IsEquivalence)
    (λ_ _ ≪≫ innerSquareOfOuter_snd_iso B S hS Q.swap hQ θ N)
    (isGerbeOver_of_isTwoFibreProduct B S hS inner (isTwoFibreProduct_innerSquareOfOuter B S hS
      Q.swap hQ θ N (isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare B S hS _ f)))
      hG)

end BaseChange

section LocalIso

/-- A morphism `ι` whose composite with `g` factors through `V` has range inside `V.preimage g`. -/
theorem _root_.CategoryTheory.Subfunctor.range_le_preimage_of_comp_eq.{v} {C : Type*} [Category C]
    {F G H : C ⥤ Type v} (V : Subfunctor G) {ι : H ⟶ F} {g : F ⟶ G} {q : H ⟶ V.toFunctor}
    (h : ι ≫ g = q ≫ V.ι) : Subfunctor.range ι ≤ V.preimage g := by
  rintro T _ ⟨y, rfl⟩
  change g.app T (ι.app T y) ∈ V.obj T
  rw [← NatTrans.comp_app_apply, h, NatTrans.comp_app_apply]
  exact (q.app T y).2

/-- For a mono `ι` with `ι ≫ g = q ≫ V.ι`, the inclusion of the range of `ι` into `V.preimage g`
followed by `V.fromPreimage g` is `q` transported along `range ι ≅ H`. -/
theorem _root_.CategoryTheory.Subfunctor.homOfLe_fromPreimage_eq.{v} {C : Type*} [Category C]
    {F G H : C ⥤ Type v} (V : Subfunctor G) {ι : H ⟶ F} [Mono ι] {g : F ⟶ G}
    {q : H ⟶ V.toFunctor} (h : ι ≫ g = q ≫ V.ι) :
    Subfunctor.homOfLe (V.range_le_preimage_of_comp_eq h) ≫ V.fromPreimage g =
      inv (Subfunctor.toRange ι) ≫ q := by
  rw [← cancel_mono V.ι, ← cancel_epi (Subfunctor.toRange ι)]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Subfunctor.fromPreimage_ι]
  rw [← Category.assoc (Subfunctor.homOfLe _), Subfunctor.homOfLe_ι, ← Category.assoc,
    Subfunctor.toRange_ι, h]

/-- Two 1-morphisms out of an algebraic space which are 2-isomorphic after restriction along
`b ≫ c` are 2-isomorphic after restriction along any `d = a ≫ b ≫ c`. -/
theorem nonempty_iso_algebraicSpaceStackMap_of_eq_comp {A A' W T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hA' : IsAlgebraicSpace B S hS A')
    (hW : IsAlgebraicSpace B S hS W) (hT : IsAlgebraicSpace B S hS T)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (xa xb : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (a : A ⟶ A') (b : A' ⟶ W) (c : W ⟶ T)
    (θ : algebraicSpaceStackMap.{u, w} B S hS hA' hW b ≫
        algebraicSpaceStackMap.{u, w} B S hS hW hT c ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hA' hW b ≫
        algebraicSpaceStackMap.{u, w} B S hS hW hT c ≫ xb)
    {d : A ⟶ T} (hd : d = a ≫ b ≫ c) :
    Nonempty (algebraicSpaceStackMap.{u, w} B S hS hA hT d ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hA hT d ≫ xb) := by
  subst hd
  have h : ∀ x : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳,
      algebraicSpaceStackMap.{u, w} B S hS hA hT (a ≫ b ≫ c) ≫ x =
        algebraicSpaceStackMap.{u, w} B S hS hA hA' a ≫
          algebraicSpaceStackMap.{u, w} B S hS hA' hW b ≫
            algebraicSpaceStackMap.{u, w} B S hS hW hT c ≫ x := by
    intro x
    rw [← Stack.algebraicSpaceStackMap_comp B S hS hA hA' hT,
      ← Stack.algebraicSpaceStackMap_comp B S hS hA' hW hT]
    simp only [Category.assoc]
  exact ⟨eqToIso (h xa) ≪≫ whiskerLeftIso _ θ ≪≫ eqToIso (h xb).symm⟩

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **Two sections over a gerbe locus are isomorphic, Zariski locally after a finite surjective
cover** (the step "(d) ⟹ (e)" of the proof of [Stacks, Tag 0CQ7]). Let `f : 𝒳 ⟶ Y` be separated
with `𝒳_V ⟶ V` a gerbe over an open `V ⊆ Y`, let `p : Y' ⟶ Y` with `Y'` quasi-compact and
quasi-separated, let `x_a, x_b : U ⟶ 𝒳` be 1-morphisms over `Y` out of an open `U ⊆ Y'` and let
`V' ⊆ U ∩ p⁻¹(V)` be a quasi-compact open. Then there are a finite surjective `g : Y'' ⟶ Y'` and
opens `O j ⊆ g⁻¹(V')` covering `g⁻¹(V')` over each of which `x_a` and `x_b` become 2-isomorphic.

The isomorphism space `I = V' ×_{s_a, 𝒳_{V'}, s_b} V'` of the two sections of the base change
`𝒳_{V'} ⟶ V'` is surjective, flat and locally of finite presentation over `V'`, as a base change
of the section `s_b` of the gerbe `𝒳_{V'} ⟶ V'` (Stacks 06QG (3)); [Stacks, Tag 0CQ6] gives the
finite cover with local sections of `I`, which are local isomorphisms. -/
theorem exists_finite_cover_iso_of_isGerbeOver (V : Subfunctor Y)
    (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (hY'qc : Space.IsQuasiCompactSpace B S hS Y')
    (hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y') (p : Y' ⟶ Y)
    (U V' : Subfunctor Y') (hU : Space.IsOpenSubspace B S hS U)
    (hV' : Space.IsOpenSubspace B S hS V') (hV'qc : Space.IsQuasiCompactSpace B S hS V'.toFunctor)
    (hV'U : V' ≤ U) (hV'V : V' ≤ V.preimage p)
    (xa xb : algebraicSpaceStack.{u, w} B S hS U.toFunctor hU.1 ⟶ 𝒳)
    (ea : xa ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p))
    (eb : xb ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p)) :
    ∃ (Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY'' : IsAlgebraicSpace B S hS Y'') (g : Y'' ⟶ Y'),
      Space.IsFinite B S hS g ∧ Space.IsSurjective B S hS g ∧
      ∃ (J : Type u) (O : J → Subfunctor Y'') (hO : ∀ j, Space.IsOpenSubspace B S hS (O j))
        (hOV : ∀ j, O j ≤ V'.preimage g),
        Set.range (Space.pointsMap B S hS (V'.preimage g).toFunctor (V'.preimage g).ι) ⊆
          ⋃ j, Set.range (Space.pointsMap B S hS (O j).toFunctor (O j).ι) ∧
        ∀ j, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hO j).1 hU.1
            (Subfunctor.homOfLe (hOV j) ≫ V'.fromPreimage g ≫ Subfunctor.homOfLe hV'U) ≫ xa ≅
          algebraicSpaceStackMap.{u, w} B S hS (hO j).1 hU.1
            (Subfunctor.homOfLe (hOV j) ≫ V'.fromPreimage g ≫ Subfunctor.homOfLe hV'U) ≫ xb) := by
  have hV'a := hV'.1
  let k : V'.toFunctor ⟶ V.toFunctor :=
    Subfunctor.lift (V'.ι ≫ p) (by rintro T _ ⟨y, rfl⟩; exact hV'V T y.2)
  let ρ := algebraicSpaceStackMap.{u, w} B S hS hV'a hU.1 (Subfunctor.homOfLe hV'U)
  have hρ : algebraicSpaceStackMap.{u, w} B S hS hV'a hU.1 (Subfunctor.homOfLe hV'U) ≫
      algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p) =
        algebraicSpaceStackMap.{u, w} B S hS hV'a hY (V'.ι ≫ p) := by
    rw [Stack.algebraicSpaceStackMap_comp B S hS hV'a hU.1 hY, ← Category.assoc,
      Subfunctor.homOfLe_ι]
  let e' x (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p)) :=
    α_ _ _ _ ≪≫ whiskerLeftIso ρ e ≪≫ eqToIso hρ
  let P := baseChangeSquare hY hV'a (V'.ι ≫ p) f
  have hPg : IsGerbeOver B S hS P.fst :=
    isGerbeOver_baseChangeSquare_fst hY f V hV hG hV'a (V'.ι ≫ p) k (Subfunctor.lift_ι _ _)
  let s x (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p)) :=
    baseChangeSection hY hV'a (V'.ι ≫ p) f (ρ ≫ x) (e' x e)
  let I := twoFibreProductSquare B S hS (s xa ea) (s xb eb)
  obtain ⟨hIs, hIf, hIl⟩ :=
    isSurjective_isFlat_isLocallyOfFinitePresentation_twoFibreProductSquare_fst P.fst
      hPg _ _ (baseChangeSectionFst hY hV'a (V'.ι ≫ p) f (ρ ≫ xb) (e' xb eb))
  obtain ⟨Y'', hY'', g, hgf, hgs, J, Wj, hWj, ι, q, σ, hι, hιq, hcov, hσ⟩ :=
    Stack.exists_finite_surjective_zariskiLocal_factorization B S hS hY' hY'qc
      hY'qs V' hV' hV'qc I.fst hIs hIf hIl
  have hI12 : I.fst = I.snd := eq_of_iso_algebraicSpaceStack hV'a
    ((ρ_ _).symm ≪≫
      whiskerLeftIso _ (baseChangeSectionFst hY hV'a (V'.ι ≫ p) f (ρ ≫ xa) (e' xa ea)).symm ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso I.iso _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (baseChangeSectionFst hY hV'a (V'.ι ≫ p) f (ρ ≫ xb) (e' xb eb)) ≪≫ ρ_ _)
  refine ⟨Y'', hY'', g, hgf, hgs, J, fun j => Subfunctor.range (ι j),
    fun j => Space.isOpenSubspace_subfunctorRange B S hS (hWj j) (hι j),
    fun j => V'.range_le_preimage_of_comp_eq (hιq j), ?_, fun j => ?_⟩
  · intro y hy
    obtain ⟨j, z, rfl⟩ := hcov y (by rwa [Space.range_pointsMap_preimage_ι] at hy)
    refine Set.mem_iUnion.2 ⟨j, Space.pointsMap B S hS _ (Subfunctor.toRange (ι j)) z, ?_⟩
    rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
  · obtain ⟨eσ⟩ := hσ j
    have : Mono (ι j) := Space.mono_of_isOpenImmersion B S hS (ι j) (hι j)
    have θ : algebraicSpaceStackMap.{u, w} B S hS (hWj j) hV'a (q j) ≫ s xa ea ≅
        algebraicSpaceStackMap.{u, w} B S hS (hWj j) hV'a (q j) ≫ s xb eb :=
      whiskerRightIso eσ.symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ I.iso ≪≫ (α_ _ _ _).symm ≪≫
        eqToIso (by rw [← hI12]) ≪≫ whiskerRightIso eσ _
    obtain ⟨θ'⟩ := nonempty_iso_of_iso_baseChangeSection hY hV'a (V'.ι ≫ p) f (hWj j) (q j)
      (ρ ≫ xa) (ρ ≫ xb) (e' xa ea) (e' xb eb) θ
    exact nonempty_iso_algebraicSpaceStackMap_of_eq_comp _ (hWj j) hV'a hU.1 xa xb
      (inv (Subfunctor.toRange (ι j))) (q j) (Subfunctor.homOfLe hV'U) θ'
      (by rw [← Category.assoc, V'.homOfLe_fromPreimage_eq (hιq j), Category.assoc])

end LocalIso

end AlgebraicGeometry.Stack.AlgebraicStacks

end
