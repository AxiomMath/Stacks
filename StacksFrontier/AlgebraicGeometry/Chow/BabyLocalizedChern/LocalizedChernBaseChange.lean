module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectRestriction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The localized Chern classes of a closed cover commute with base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with `X = X₁ ∪ X₂`
set theoretically, and let `E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes are defined,
with `E₂|_{X₁ ∩ X₂}` zero, resp. finite locally free of rank `< p` in degree `0`. Stacks 0F9H
gives the class `P'_p(E₂)`, resp. `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`, characterized by
`P'_p(E₂) ∩ i_{2,*} α₂ = P_p(E₂) ∩ α₂` and `P'_p(E₂) ∩ i_{1,*} α₁ = 0` on every test scheme.

**Stacks 0GUG**: for `q : X' ⟶ X` locally of finite type, with `X'_j = X_j ×_X X'` and
`E'₂ = (X'₂ ⟶ X₂)^* E₂`, the class `P'_p(E'₂)`, resp. `c'_p(E'₂) ∈ A^p(X'₂ ⟶ X')` built by Stacks
0F9H from `X' = X'₁ ∪ X'₂` and `E'₂` is the restriction (Remark 0F9Z) of `P'_p(E₂)`, resp.
`c'_p(E₂)`.

The proof is the source's: both classes satisfy the characterization of Stacks 0F9H at `X'`. The
ambient class `P_p(E'₂)`, resp. `c_p(E'₂)`, is the restriction of `P_p(E₂)`, resp. `c_p(E₂)`, to
`X'₂`, and the base change of `X_j` along a test scheme `T ⟶ X'` is the base change of `X_j`
along `T ⟶ X' ⟶ X`. Along the way `E'₂` is shown to satisfy the hypotheses of Stacks 0F9H: it is
perfect with defined Chern classes, and `E'₂|_{X'₁ ∩ X'₂}` is the pullback of `E₂|_{X₁ ∩ X₂}`,
hence zero, resp. finite locally free of rank `< p` in degree `0`.

## Main results

* `Stacks.Chow.closedCoverLocalizedClass_baseChange` — the localized class of a class `κ'` on
  `X'₂` operating as the restriction of `κ` is the restriction of the localized class of `κ`.
* `Stacks.Chow.res_perfectPowerSumTotal_derivedPullback` — the classes `P_p` of `Lh^*E` are the
  restrictions of those of `E`.
* `Stacks.Chow.exists_iso_single_baseChange`, `Stacks.Chow.isZero_baseChange` — the hypotheses of
  Stacks 0F9H on `E₂|_{X₁ ∩ X₂}` pass to `E'₂|_{X'₁ ∩ X'₂}`.
* `Stacks.Chow.localizedChernClassOfClosedCover_baseChange` — **Stacks 0GUG** for `c'_p`.
* `Stacks.Chow.localizedPowerSumOfClosedCover_baseChange` — **Stacks 0GUG** for `P'_p`.

## Implementation notes

The restriction `Stacks.Chow.bivariantRestrictionOfInvertible` of Remark 0F9Z is a class for the
chosen fibre product `X₂ ×_X X' ⟶ X'` with the structure morphism `X₂ ×_X X' ⟶ X₂ ⟶ S`, while the
class of Stacks 0F9H at `X'` is stated with `X'₂ ⟶ X' ⟶ S`. The two structure morphisms are equal
but not syntactically, so the restriction is carried to the second one by
`Stacks.Chow.bivariantTransport` along the identity of `X₂ ×_X X'`.

## References

* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized class of a closed cover and base change -/

section ClosedCoverBaseChange

variable (C : ChowSituation.{u}) {X X₁ X₂ X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S)
  [LocallyOfFiniteType sX₂] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁)
  (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂)
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
  (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p)
  (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ (pullback.snd i₁ i₂) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
  (q : X' ⟶ X) [LocallyOfFiniteType q]
  (sX₁' : pullback i₁ q ⟶ C.S) [LocallyOfFiniteType sX₁']
  (hi₁' : pullback.snd i₁ q ≫ q ≫ sX = sX₁')
  (sX₂' : pullback i₂ q ⟶ C.S) [LocallyOfFiniteType sX₂']
  (hi₂' : pullback.snd i₂ q ≫ q ≫ sX = sX₂')
  (κ' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂' p)
  (hκ' : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂'
    (pullback.snd (pullback.snd i₁ q) (pullback.snd i₂ q)) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ' = 0)

omit [LocallyOfFiniteType sX] [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
include hi₂ hi₂' in
/-- The identification of `X₂ ×_X T` with `(X₂ ×_X X') ×_{X'} T` lies over the base. -/
theorem pullbackLeftPullbackSndIso_hom_fst_comp_structure {T : Scheme.{u}} (g : T ⟶ X') :
    (pullbackLeftPullbackSndIso i₂ q g).hom ≫ pullback.fst i₂ (g ≫ q) ≫ sX₂ =
      pullback.fst (pullback.snd i₂ q) g ≫ sX₂' := by
  subst hi₂ hi₂'
  rw [pullbackLeftPullbackSndIso_hom_fst_assoc, pullback.condition_assoc]

include hi₁ hi₂ hcover hκ hi₁' hi₂' in
/-- **The localized class of a closed cover commutes with base change.** Let `κ' ∈ A^p(X'₂)` be a
class on `X'₂ = X₂ ×_X X'` operating on every test scheme `t : V ⟶ X'₂` as `κ` operates on
`V ⟶ X'₂ ⟶ X₂`, i.e. the restriction of `κ`. Then the localized class `κ''` of `κ'` for the cover
`X' = X'₁ ∪ X'₂` is the restriction (Remark 0F9Z) of the localized class `κ'` of `κ` for the cover
`X = X₁ ∪ X₂`. Both satisfy the characterization of `Stacks.Chow.eq_closedCoverLocalizedClass`
at `X'`. -/
theorem closedCoverLocalizedClass_baseChange
    (hres : ∀ {V : Scheme.{u}} (t : V ⟶ pullback i₂ q) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX₂') k)
      (β : chowGroup C ((t ≫ pullback.fst i₂ q) ≫ sX₂) k), α ≍ β →
      κ'.idRule C sX₂' (gysinSystemOfInvertible C) t k α ≍
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (t ≫ pullback.fst i₂ q) k β) :
    closedCoverLocalizedClass C (q ≫ sX) sX₁' sX₂' (pullback.snd i₁ q) hi₁'
        (pullback.snd i₂ q) hi₂' (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover q) κ'
        hκ' =
      bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i₂ q ≫ sX₂) sX₂' (q ≫ sX)
        (pullback.snd i₂ q) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ q)
        (pullback.snd i₂ q) hi₂' (Iso.refl _) (Category.id_comp _) p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C sX₂ sX i₂ hi₂ q p
          (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ)) := by
  refine (eq_closedCoverLocalizedClass C (q ≫ sX) sX₁' sX₂' (pullback.snd i₁ q) hi₁'
    (pullback.snd i₂ q) hi₂' _ κ' hκ' _ ?_ ?_).symm
  · intro T g _ k α
    have hv := pullbackLeftPullbackSndIso_hom_fst_comp_structure C sX sX₂ i₂ hi₂ q sX₂' hi₂' g
    have hpush := pullbackSnd_comp_structureMorphism_eq C sX₂' (q ≫ sX) (pullback.snd i₂ q) hi₂' g
    have h0 : (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap (g ≫ q) k
        (chowGroupCongr C (Category.assoc g q sX).symm k
          (chowPush C (pullback.fst (pullback.snd i₂ q) g ≫ sX₂') (g ≫ q ≫ sX)
            (pullback.snd (pullback.snd i₂ q) g) hpush k α)) =
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ (g ≫ q)) k
          (chowPush C _ _ (pullbackLeftPullbackSndIso i₂ q g).hom hv k α) := by
      rw [chowGroupCongr_chowPush C _ (Category.assoc g q sX).symm _ _
        (by rw [← Category.assoc]; exact hpush)]
      exact closedCoverLocalizedCap_chowPush_right C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
        (g ≫ q) _ (pullbackLeftPullbackSndIso i₂ q g).hom hv _
        (pullbackLeftPullbackSndIso_hom_snd i₂ q g) _ k α
    have hT : (transportPullbackIso (pullback.snd i₂ q) (pullback.snd i₂ q) (Iso.refl _)
        (Category.id_comp _) g).hom = 𝟙 _ := by
      ext <;> simp
    rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestrictionOfInvertible_cap,
      bivariantRestrictionCap_apply, h0,
      idRule_chowPush_of_eq C sX₂ κ (pullback.fst i₂ (g ≫ q))
        (pullback.fst (pullback.snd i₂ q) g ≫ pullback.fst i₂ q)
        (pullbackLeftPullbackSndIso i₂ q g).hom (pullbackLeftPullbackSndIso_hom_fst i₂ q g) _
        (by rw [Category.assoc, ← pullbackLeftPullbackSndIso_hom_fst_assoc]; exact hv) hv k α]
    show chowPushforwardOfIso C _ _ _ _ (k - p) (chowPushforwardOfIso C _ _ _ _ (k - p)
      (chowPushforwardOfIso C _ _ (pullbackLeftPullbackSndIso i₂ q g).hom _ (k - p) _)) = _
    have hid : (pullbackLeftPullbackSndIso i₂ q g).hom ≫ (pullbackLeftPullbackSndIso i₂ q g).inv ≫
        (transportPullbackIso (pullback.snd i₂ q) (pullback.snd i₂ q) (Iso.refl _)
          (Category.id_comp _) g).hom = 𝟙 _ := by
      rw [hT, Category.comp_id, Iso.hom_inv_id]
    have hstr : 𝟙 _ ≫ (pullback.fst (pullback.snd i₂ q) g ≫ sX₂') =
        (pullback.fst (pullback.snd i₂ q) g ≫ pullback.fst i₂ q) ≫ sX₂ := by
      rw [Category.id_comp, ← hv, ← Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        Category.assoc]
    rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) hid _ hstr,
      chowPushforwardOfIso_id_eq_chowGroupCongr]
    exact eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
      (hres (pullback.fst (pullback.snd i₂ q) g) k α _ (chowGroupCongr_heq C _ _ _).symm).symm)
  · intro T g _ k α
    have hv := pullbackLeftPullbackSndIso_hom_fst_comp_structure C sX sX₁ i₁ hi₁ q sX₁' hi₁' g
    have h0 : (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap (g ≫ q) k
        (chowGroupCongr C (Category.assoc g q sX).symm k
          (chowPush C (pullback.fst (pullback.snd i₁ q) g ≫ sX₁') (g ≫ q ≫ sX)
            (pullback.snd (pullback.snd i₁ q) g)
            (pullbackSnd_comp_structureMorphism_eq C sX₁' (q ≫ sX) (pullback.snd i₁ q) hi₁' g)
            k α)) = 0 := by
      rw [chowGroupCongr_chowPush C _ (Category.assoc g q sX).symm _ _
        (by rw [← Category.assoc]
            exact pullbackSnd_comp_structureMorphism_eq C sX₁' (q ≫ sX) (pullback.snd i₁ q)
              hi₁' g)]
      exact closedCoverLocalizedCap_chowPush_left C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ (g ≫ q)
        _ (pullbackLeftPullbackSndIso i₁ q g).hom hv _
        (pullbackLeftPullbackSndIso_hom_snd i₁ q g) _ k α
    rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestrictionOfInvertible_cap,
      bivariantRestrictionCap_apply, h0, map_zero, map_zero]

end ClosedCoverBaseChange

/-! ### The hypotheses of Stacks 0F9H after a base change -/

section Hypotheses

/-- **Finite local freeness of rank `< p` is stable under pullback**: if `M` is finite locally
free of rank `< p`, so is `f^*M`, the rank of `f^*M` near `y` being the rank of `M` near `f y`. -/
theorem IsFiniteLocallyFreeOfRankLT.pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    {p : ℕ} (hM : IsFiniteLocallyFreeOfRankLT M p) :
    IsFiniteLocallyFreeOfRankLT ((Scheme.Modules.pullback f).obj M) p := by
  refine ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme f M hM.1,
    fun y ↦ ?_⟩
  obtain ⟨U₀, hyU, r, hr, hU⟩ := hM.2 (f.base y)
  let U : X.Opens := U₀
  have hU' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj M) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app M) hU
  refine ⟨f ⁻¹ᵁ U, hyU, r, hr, ?_⟩
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y (f ⁻¹ᵁ U)).app _ ≪≫
      Stacks.BlowUpComplexes.pullbackRestrictIso f U M).symm
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (f ∣_ U) _ r)

variable {A B D F : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ F) (c : A ⟶ D) (d : D ⟶ F)
  (hcomm : a ≫ b = c ≫ d) (E : DerivedCategory F.Modules)

include hcomm in
/-- Derived pullback along the two sides of a commutative square: `La^* Lb^* E ≅ Lc^* Ld^* E`
when `b ∘ a = d ∘ c`. -/
theorem nonempty_derivedPullback_iso_of_comp_eq :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj E) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback c.toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback d.toLRSHom.toShHom).obj
          E)) := by
  have he : a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = c.toLRSHom.toShHom ≫ d.toLRSHom.toShHom :=
    congrArg (fun f ↦ f.toLRSHom.toShHom) hcomm
  exact ⟨(Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom b.toLRSHom.toShHom).app E ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq he)).app E ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      c.toLRSHom.toShHom d.toLRSHom.toShHom).app E).symm⟩

include hcomm in
/-- **Vanishing is stable under base change**: if `Ld^*E = 0` then `La^* Lb^* E = 0` for a
commutative square `b ∘ a = d ∘ c`. -/
theorem isZero_derivedPullback_of_comp_eq
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      d.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj E)) :=
  (Functor.map_isZero (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    c.toLRSHom.toShHom) h).of_iso (nonempty_derivedPullback_iso_of_comp_eq a b c d hcomm E).some

include hcomm in
/-- **Being a finite locally free module of rank `< p` in degree `0` is stable under base
change**: if `Ld^*E ≅ M[0]` with `M` finite locally free of rank `< p`, then
`La^* Lb^* E ≅ (c^*M)[0]` for a commutative square `b ∘ a = d ∘ c`, and `c^*M` is again finite
locally free of rank `< p`. The complex `M[0]` is K-flat, so its derived pullback is computed
termwise. -/
theorem exists_iso_single_derivedPullback_of_comp_eq {p : ℕ}
    (h : ∃ M : D.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          d.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor D.Modules 0).obj M)) :
    ∃ M : A.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          a.toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj
            E) ≅ (DerivedCategory.singleFunctor A.Modules 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  refine ⟨(Scheme.Modules.pullback c).obj M, hM.pullback c, ⟨?_⟩⟩
  exact (nonempty_derivedPullback_iso_of_comp_eq a b c d hcomm E).some ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback c.toLRSHom.toShHom).mapIso
      (e ≪≫ (DerivedCategory.singleFunctorIsoCompQ D.Modules 0).app M) ≪≫
    Cohomology.derivedPullbackIsoPullbackOfKFlat c.toLRSHom.toShHom (singleZero M)
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _
        (isLocallyBoundedFiniteLocallyFree_singleZero M hM.1)) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pullback c) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A.Modules 0).app _).symm

end Hypotheses

/-! ### The Chern classes and the classes `P_p` of a pullback -/

section Restriction

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (h : Z ⟶ X) [LocallyOfFiniteType h]
  (hs : h ≫ sX = sZ) {E : DerivedCategory X.Modules}

/-- **The Chern classes of a derived pullback** (Stacks 0F9E): for `h : Z ⟶ X` locally of finite
type, the restriction of `c(E)` to `Z` is `c(Lh^*E)`, for any structure morphism of `Z` equal to
`h ≫ sX`. -/
theorem res_perfectChernClass_derivedPullback_of_eq (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res h hs (perfectChernClass C sX hE) = perfectChernClass C sZ hE' := by
  subst hs
  exact res_perfectChernClass_derivedPullback C sX h hE hE'

/-- **The rank of a derived pullback**: the restriction of `r(E)` along `h : Z ⟶ X` is
`r(Lh^*E)`, the Euler characteristic of the derived fibres of `Lh^*E` at `z` being that of `E` at
`h(z)`. -/
theorem res_perfectRankClass_derivedPullback
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E)
    (perfect' : RingedSpace.IsPerfect.{u, u + 1} (X := Z.toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E))
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res h hs (perfectRankClass C sX hE) = perfectRankClass C sZ hE' := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_eulerLoci perfect') fun m ↦ ?_
  have hz : ∀ z, (eulerLocus perfect' m.down).ι.base z ∈ eulerLocus perfect' m.down := by
    intro z
    show _ ∈ ((eulerLocus perfect' m.down : Z.Opens) : Set Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨z, rfl⟩
  have h1 := res_perfectRankClass_of_range perfect C sX hE ((eulerLocus perfect' m.down).ι ≫ h)
    (by rw [Category.assoc, hs]) m.down (by
      rintro _ ⟨z, rfl⟩
      refine (mem_eulerLocus perfect).mpr ?_
      have h2 := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback h E
        (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect))
        ((eulerLocus perfect' m.down).ι.base z)
      exact h2.symm.trans ((mem_eulerLocus perfect').mp (hz z)))
  have h3 := res_perfectRankClass_of_range perfect' C sZ hE' (eulerLocus perfect' m.down).ι rfl
    m.down (by
      rintro _ ⟨z, rfl⟩
      exact hz z)
  exact (TotalChowClass.res_res h hs _ rfl _).trans (h1.trans h3.symm)

/-- **The classes `P_p` of a derived pullback**: the restriction of the total class
`(r(E), P_1(E), P_2(E), …)` along `h : Z ⟶ X` is that of `Lh^*E`. -/
theorem res_perfectPowerSumTotal_derivedPullback
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hE : HasDefinedChernClasses E)
    (perfect' : RingedSpace.IsPerfect.{u, u + 1} (X := Z.toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E))
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res h hs (perfectPowerSumTotal C sX hE) = perfectPowerSumTotal C sZ hE' := by
  subst hs
  refine TotalChowClass.ext fun n ↦ ?_
  rw [TotalChowClass.res_rfl_apply, perfectPowerSumTotal_apply]
  show _ = perfectPowerSumComponent C (h ≫ sX) hE' n
  rcases n with _ | n
  · rw [perfectPowerSumComponent_zero C sX hE, perfectPowerSumComponent_zero C (h ≫ sX) hE',
      ← TotalChowClass.res_rfl_apply,
      res_perfectRankClass_derivedPullback C sX h rfl perfect hE perfect' hE']
  · have hnewton : ∀ {W W' : Scheme.{u}} {sW : W ⟶ C.S} [LocallyOfFiniteType sW] (k : W' ⟶ W)
        [LocallyOfFiniteType k] (c : TotalChowClass C sW),
        TotalChowClass.res k rfl (TotalChowClass.newtonComponents c (n + 1)) =
          TotalChowClass.newtonComponents (TotalChowClass.res k rfl c) (n + 1) := by
      intro W W' sW _ k _ c
      rw [TotalChowClass.newtonComponents, map_newtonPowerSum (TotalChowClass.res k rfl), map_zero]
      simp only [TotalChowClass.res_homComponent]
    rw [perfectPowerSumComponent_succ C sX hE, perfectPowerSumComponent_succ C (h ≫ sX) hE',
      ← TotalChowClass.res_rfl_apply, hnewton, res_perfectChernClass_derivedPullback C sX h hE hE']

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] in
/-- If `c'` is the restriction of `c` along `h`, then on every test scheme `t : V ⟶ Z` the
components of `c'` operate as those of `c` do on `t ≫ h`. -/
theorem idRule_heq_of_res_eq [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ]
    {c : TotalChowClass C sX} {c' : TotalChowClass C sZ}
    (hc : TotalChowClass.res h hs c = c') (n : ℕ) {V : Scheme.{u}} (t : V ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k)
    (β : chowGroup C ((t ≫ h) ≫ sX) k) (hαβ : α ≍ β) :
    (c' n).idRule C sZ (gysinSystemOfInvertible C) t k α ≍
      (c n).idRule C sX (gysinSystemOfInvertible C) (t ≫ h) k β := by
  subst hc
  exact TotalChowClass.op_res_apply h hs c t k n α β hαβ

end Restriction

/-! ### Stacks 0GUG -/

section BaseChange

variable (C : ChowSituation.{u}) {X X₁ X₂ X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)
  (q : X' ⟶ X) [LocallyOfFiniteType q]

/-- The morphism `X'₁ ∩ X'₂ ⟶ X₁ ∩ X₂` of the scheme-theoretic intersections, for the base
changes `X'_j = X_j ×_X X'` along `q : X' ⟶ X`. -/
abbrev intersectionBaseChange :
    pullback (pullback.snd i₁ q) (pullback.snd i₂ q) ⟶ pullback i₁ i₂ :=
  pullback.map _ _ _ _ (pullback.fst i₁ q) (pullback.fst i₂ q) q pullback.condition.symm
    pullback.condition.symm

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
/-- The restriction of `E'₂` to `X'₁ ∩ X'₂` is the pullback of the restriction of `E₂` to
`X₁ ∩ X₂`: the two composites `X'₁ ∩ X'₂ ⟶ X₂` agree. -/
theorem intersectionBaseChange_comp_snd :
    pullback.snd (pullback.snd i₁ q) (pullback.snd i₂ q) ≫ pullback.fst i₂ q =
      intersectionBaseChange i₁ i₂ q ≫ pullback.snd i₁ i₂ := by
  simp

omit [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
include hE₂ in
/-- The pullback `E'₂ = (X'₂ ⟶ X₂)^* E₂` has defined Chern classes. -/
theorem hasDefinedChernClasses_baseChange :
    HasDefinedChernClasses ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst i₂ q).toLRSHom.toShHom).obj E₂) :=
  hasDefinedChernClasses_of_derivedPullback _ _ _ hE₂ (Iso.refl _)

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
/-- If `E₂|_{X₁ ∩ X₂}` is finite locally free of rank `< p` in degree `0`, so is
`E'₂|_{X'₁ ∩ X'₂}`. -/
theorem exists_iso_single_baseChange
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M)) :
    ∃ M : (pullback (pullback.snd i₁ q) (pullback.snd i₂ q)).Modules,
      IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd (pullback.snd i₁ q) (pullback.snd i₂ q)).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (pullback.fst i₂ q).toLRSHom.toShHom).obj E₂) ≅
        (DerivedCategory.singleFunctor
          (pullback (pullback.snd i₁ q) (pullback.snd i₂ q)).Modules 0).obj M) :=
  exists_iso_single_derivedPullback_of_comp_eq _ _ _ _ (intersectionBaseChange_comp_snd i₁ i₂ q)
    E₂ hres

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
/-- If `E₂|_{X₁ ∩ X₂}` is zero, so is `E'₂|_{X'₁ ∩ X'₂}`. -/
theorem isZero_baseChange
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd (pullback.snd i₁ q) (pullback.snd i₂ q)).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst i₂ q).toLRSHom.toShHom).obj E₂)) :=
  isZero_derivedPullback_of_comp_eq _ _ _ _ (intersectionBaseChange_comp_snd i₁ i₂ q) E₂ hzero

omit [IsClosedImmersion i₂] [LocallyOfFiniteType q] in
/-- The pullback `E'₂ = (X'₂ ⟶ X₂)^* E₂` of a perfect object is perfect. -/
theorem isPerfect_baseChange
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂) :
    RingedSpace.IsPerfect.{u, u + 1} (X := (pullback i₂ q).toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst i₂ q).toLRSHom.toShHom).obj E₂) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E₂ perfect

/-- If `c'` is the restriction of `c` along `X'₂ ⟶ X₂`, then the components of `c'` operate on
every test scheme `t : V ⟶ X'₂` as those of `c` do on `t ≫ (X'₂ ⟶ X₂)`. -/
private theorem idRule_heq_of_res_fst_eq {c : TotalChowClass C (i₂ ≫ sX)}
    {c' : TotalChowClass C (pullback.snd i₂ q ≫ q ≫ sX)}
    (hc : TotalChowClass.res (pullback.fst i₂ q)
      (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl q).symm c = c') (n : ℕ) :
    ∀ {V : Scheme.{u}} (t : V ⟶ pullback i₂ q) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ pullback.snd i₂ q ≫ q ≫ sX) k)
      (β : chowGroup C ((t ≫ pullback.fst i₂ q) ≫ i₂ ≫ sX) k), α ≍ β →
      (c' n).idRule C (pullback.snd i₂ q ≫ q ≫ sX) (gysinSystemOfInvertible C) t k α ≍
        (c n).idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C) (t ≫ pullback.fst i₂ q) k β :=
  fun t _ k α β hαβ ↦ idRule_heq_of_res_eq C (i₂ ≫ sX) (pullback.fst i₂ q) _ hc n t k α β hαβ

/-- **Stacks 0GUG, for the Chern classes.** In the situation of Stacks 0F9H, with `E₂|_{X₁ ∩ X₂}`
finite locally free of rank `< p` in degree `0`, let `q : X' ⟶ X` be locally of finite type,
let `X' = X'₁ ∪ X'₂` with `X'_j = X_j ×_X X'`, and let `E'₂ = (X'₂ ⟶ X₂)^* E₂`. Then `E'₂`
satisfies the hypotheses of Stacks 0F9H for this cover, and the class `c'_p(E'₂) ∈ A^p(X'₂ ⟶ X')`
constructed by Stacks 0F9H from `X' = X'₁ ∪ X'₂` and `E'₂` is the restriction (Remark 0F9Z) of
`c'_p(E₂) ∈ A^p(X₂ ⟶ X)`.

The restriction is a class for `X₂ ×_X X' ⟶ X'` whose source carries the structure morphism
`X₂ ×_X X' ⟶ X₂ ⟶ S`, while the class of Stacks 0F9H at `X'` carries `X'₂ ⟶ X' ⟶ S`; the two are
equal, and the restriction is read with the second one by `Stacks.Chow.bivariantTransport` along
the identity. -/
@[stacks 0GUG "the classes c'_p: c'_p(E'₂) built from X' = X'₁ ∪ X'₂ and E'₂ is the restriction \
of c'_p(E₂)"]
theorem localizedChernClassOfClosedCover_baseChange
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M)) :
    localizedChernClassOfClosedCover C (q ≫ sX) (pullback.snd i₁ q) (pullback.snd i₂ q)
        (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover q)
        (hasDefinedChernClasses_baseChange i₂ hE₂ q) p
        (exists_iso_single_baseChange i₁ i₂ p q hres) =
      bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i₂ q ≫ i₂ ≫ sX)
        (pullback.snd i₂ q ≫ q ≫ sX) (q ≫ sX) (pullback.snd i₂ q)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl q)
        (pullback.snd i₂ q) rfl (Iso.refl _) (Category.id_comp _) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (i₂ ≫ sX) sX i₂ rfl q (p : ℤ)
          (localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres)) :=
  closedCoverLocalizedClass_baseChange C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover _ _ q _ rfl
    _ rfl _ _ (idRule_heq_of_res_fst_eq C sX i₂ q
      (res_perfectChernClass_derivedPullback_of_eq C (i₂ ≫ sX) (pullback.fst i₂ q) _ hE₂
        (hasDefinedChernClasses_baseChange i₂ hE₂ q)) p)

/-- **Stacks 0GUG, for the classes `P_p`.** In the situation of Stacks 0F9H, with `E₂` perfect
and `E₂|_{X₁ ∩ X₂}` zero, let `q : X' ⟶ X` be locally of finite type, let `X' = X'₁ ∪ X'₂` with
`X'_j = X_j ×_X X'`, and let `E'₂ = (X'₂ ⟶ X₂)^* E₂`. Then `E'₂` satisfies the hypotheses of
Stacks 0F9H for this cover, and the class `P'_p(E'₂) ∈ A^p(X'₂ ⟶ X')` constructed by Stacks 0F9H
from `X' = X'₁ ∪ X'₂` and `E'₂` is the restriction (Remark 0F9Z) of `P'_p(E₂) ∈ A^p(X₂ ⟶ X)`,
read with the structure morphism `X'₂ ⟶ X' ⟶ S` as in
`Stacks.Chow.localizedChernClassOfClosedCover_baseChange`. -/
@[stacks 0GUG "the classes P'_p: P'_p(E'₂) built from X' = X'₁ ∪ X'₂ and E'₂ is the restriction \
of P'_p(E₂)"]
theorem localizedPowerSumOfClosedCover_baseChange
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂)) :
    localizedPowerSumOfClosedCover C (q ≫ sX) (pullback.snd i₁ q) (pullback.snd i₂ q)
        (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover q)
        (hasDefinedChernClasses_baseChange i₂ hE₂ q) p (isPerfect_baseChange i₂ q perfect)
        (isZero_baseChange i₁ i₂ q hzero) =
      bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i₂ q ≫ i₂ ≫ sX)
        (pullback.snd i₂ q ≫ q ≫ sX) (q ≫ sX) (pullback.snd i₂ q)
        (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX i₂ rfl q)
        (pullback.snd i₂ q) rfl (Iso.refl _) (Category.id_comp _) (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestrictionOfInvertible C (i₂ ≫ sX) sX i₂ rfl q (p : ℤ)
          (localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero)) :=
  closedCoverLocalizedClass_baseChange C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover _ _ q _ rfl
    _ rfl _ _ (by
      rw [← perfectPowerSumTotal_apply C (i₂ ≫ sX) hE₂ p,
        ← perfectPowerSumTotal_apply C (pullback.snd i₂ q ≫ q ≫ sX)
          (hasDefinedChernClasses_baseChange i₂ hE₂ q) p]
      exact idRule_heq_of_res_fst_eq C sX i₂ q
        (res_perfectPowerSumTotal_derivedPullback C (i₂ ≫ sX) (pullback.fst i₂ q) _ perfect hE₂
          (isPerfect_baseChange i₂ q perfect) (hasDefinedChernClasses_baseChange i₂ hE₂ q)) p)

end BaseChange

end Stacks.Chow

end
