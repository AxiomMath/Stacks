module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.BoundedAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionGluing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationAtlasBound
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0ARA: the completion functor over a Noetherian affine base is an equivalence

Let `X = Spec R` be a Noetherian affine scheme of the big fppf site of `S`, `T ⊆ |X|` closed and
`U ⊂ X` the open subspace with `|U| = |X| ∖ T`. **Stacks 0ARA** says that the completion functor
of Stacks 0AR5 is an equivalence. Full faithfulness is Stacks 0GDR. This file proves essential
surjectivity, following the three steps of the source.

* Step 1 (`W` Noetherian affine) is Stacks 0AR4 followed by Stacks 0AR9; here it also gives an
  atlas of the algebraization whose size is bounded in terms of `R` alone.
* The gluing step: a covering `{Wₖ ⟶ W}` such that the `Wₖ` and the `Wₖ ×_W Wₗ` are completions
  of finite-type modifications with uniformly bounded atlases glues, through Stacks 0GDR,
  Stacks 0AR8 and Stacks 04S6, to a finite-type modification with completion `W`.
* Step 2 (`W` separated) applies the gluing step to an atlas of `W` indexed below the cutoff,
  with Step 1 for the `Wₖ` and the affine `Wₖ ×_W Wₗ`.
* Step 3 (`W` general): each `Wₖ ×_W Wₗ` is separated, since it maps monomorphically to the
  affine formal algebraic space `Wₖ ×_{X_{/T}} Wₗ`, so Step 2 applies to it; a representable sheaf
  of bounded size surjects onto it, which bounds the atlas of its algebraization.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_of_cover`: the
  gluing step.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_atlas_size_le`:
  Step 1 with the atlas bound.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_of_isSeparated`:
  Step 2.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_of_isRigEtale`:
  Step 3, essential surjectivity.
* `AlgebraicGeometry.FormalSpace.isEquivalence_completionModificationFunctor_affineOver`:
  **Stacks 0ARA**.

## Implementation notes

The atlas of `W` of Definition 0AIM is indexed by a type of `Type (u + 1)`; the gluing uses the
subfamily of `AlgebraicGeometry.FormalSpace.exists_isFormalAtlas_of_mk_lt_cutoff`, indexed by a
type of `Type u` of cardinality below the cutoff. Coproducts of algebraic spaces indexed this way
are algebraic spaces once their summands have atlases bounded by one cardinal below the cutoff
(Stacks 02WQ); the bounds come from
`AlgebraicGeometry.Space.exists_atlas_size_le_of_epi_completionSheaf`. An empty covering forces
`W` to be empty, and then `U` itself is the algebraization.

## References

* [Stacks Project, Tag 0ARA](https://stacks.math.columbia.edu/tag/0ARA)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0AR8](https://stacks.math.columbia.edu/tag/0AR8)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace CategoryTheory.Sheaf

universe w' v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- A sheaf of sets all of whose sections live over objects covered by the empty sieve is an
initial object: every sheaf has exactly one section over such an object. -/
noncomputable def isInitialOfBotMem {F : Sheaf J (Type w')}
    (h : ∀ (U : C) (_ : F.obj.obj (Opposite.op U)), (⊥ : Sieve U) ∈ J U) : IsInitial F := by
  classical
  let hU (G : Sheaf J (Type w')) (U : C) (e : (⊥ : Sieve U) ∈ J U) :
      Unique (G.obj.obj (Opposite.op U)) :=
    Types.isTerminalEquivUnique _ (G.isTerminalOfBotCover U e)
  refine IsInitial.ofUniqueHom (fun G => (⟨{
    app := fun U => ↾fun x => (hU G U.unop (h U.unop x)).default
    naturality := ?_ }⟩ : F ⟶ G)) ?_
  · rename_i G
    intro U V f
    ext x
    let := hU G V.unop (h V.unop (F.obj.map f x))
    exact Subsingleton.elim _ _
  · intro G f
    ext U x
    let := hU G U.unop (h U.unop x)
    exact Subsingleton.elim _ _

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The completion of an isomorphism of presheaves is an isomorphism. -/
theorem isIso_completionSheafMap_of_isIso {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : X' ⟶ X)
    [IsIso φ] (T : Set (Space.points B S hS X)) :
    IsIso (Space.completionSheafMap B S hS φ T) := by
  have : IsIso (Space.sheafifiedULiftMap B S hS φ) :=
    ⟨Space.sheafifiedULiftMap B S hS (inv φ), by
      rw [← Space.sheafifiedULiftMap_comp, IsIso.hom_inv_id, Space.sheafifiedULiftMap_id], by
      rw [← Space.sheafifiedULiftMap_comp, IsIso.inv_hom_id, Space.sheafifiedULiftMap_id]⟩
  exact (Space.isPullback_completionSheafMap B S hS φ T).isIso_snd_of_isIso

/-- Raising `2` to a power is monotone. -/
private theorem two_pow_le_two_pow {a b : Cardinal.{u}} (h : a ≤ b) :
    (2 : Cardinal.{u}) ^ a ≤ 2 ^ b :=
  power_le_power_left two_ne_zero h

/-- **The completion of an affine object of the site of controlled size along a closed set is
covered by one object of the site of controlled size.** Let `Y` be an object of the site whose
underlying scheme is affine of size at most `σ`, and let `T` be a closed set of points of `h_Y`.
Then there is an object `V` of the site with `size V ≤ 2 ^ σ` (so `#V ≤ 2 ^ 2 ^ σ`) and a
surjection
`h_V ⟶ (h_Y)_{/T}`: writing `Y = Spec A`, the quotient stages `Spec (A ⧸ J)` cutting out `T`
glue to `V` (`AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_zeroLocusCompletion`). -/
theorem exists_epi_uliftYoneda_completionSheaf_of_isAffine (Y : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)] (T : Set (Space.points B S hS (yoneda.obj Y)))
    (hT : IsClosed T) {σ : Cardinal.{u}} (hσ : ((BigFppfOver.toScheme B S hS).obj Y).size ≤ σ) :
    ∃ (V : BigFppfOver B S hS)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶
        Space.completionSheaf B S hS (yoneda.obj Y) T),
      Epi q ∧ ((BigFppfOver.toScheme B S hS).obj V).size ≤ (2 : Cardinal.{u}) ^ σ ∧
        #((BigFppfOver.toScheme B S hS).obj V) ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ σ := by
  have hA := contains_spec_globalSections B S hS Y
  let ι : affineOver B S hS hA (((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv ≫ Y.hom.hom) ⟶
      Y := siteHom B S hS ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv rfl
  have : IsIso ((BigFppfOver.toScheme B S hS).map ι) := by
    change IsIso ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv
    infer_instance
  have : IsIso ι := isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  obtain ⟨Ti, hTi, hTpts⟩ := exists_isClosed_preimage_eq_supportedPoints hT (yoneda.map ι)
  have hP : Space.pointsMap B S hS _ (yoneda.map ι) ⁻¹' T =
      zeroLocusPoints B S hS hA _ (PrimeSpectrum.vanishingIdeal Ti) :=
    hTpts.trans ((congrArg (supportedPoints B S hS (affineOver B S hS hA _))
      (hTi.closure_eq.symm.trans
        (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Ti).symm)).trans
      (supportedPoints_zeroLocus B S hS hA _ _))
  obtain ⟨V, hVsize, q, hq⟩ :=
    exists_epi_uliftYoneda_zeroLocusCompletion hA _ (PrimeSpectrum.vanishingIdeal Ti)
  have := isIso_completionSheafMap_of_isIso (yoneda.map ι) T
  refine ⟨V, q ≫ eqToHom (congrArg (Space.completionSheaf B S hS _) hP.symm) ≫
    Space.completionSheafMap B S hS (yoneda.map ι) T, inferInstance, ?_⟩
  have hAc : #Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) ≤ σ :=
    (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩).trans hσ
  have hV : ((BigFppfOver.toScheme B S hS).obj V).size ≤ 2 ^ σ :=
    hVsize.trans (max_le (((Scheme.aleph0_le_size _).trans hσ).trans (cantor σ).le)
      (two_pow_le_two_pow hAc))
  exact ⟨hV, (Scheme.mk_le_two_pow_size _).trans (two_pow_le_two_pow hV)⟩

/-- The completion of a morphism over `X` is the restriction morphism of completions along the
inverse images of `T`. -/
theorem completionOverMap_eq_completionSheafRestrict {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) {M N : Over X} (a : M ⟶ N)
    (h : Space.pointsMap B S hS M.left M.hom ⁻¹' T ⊆
      Space.pointsMap B S hS M.left a.left ⁻¹' (Space.pointsMap B S hS N.left N.hom ⁻¹' T)) :
    Space.completionOverMap B S hS T a =
      Space.completionSheafRestrict B S hS a.left _ _ h := by
  rw [completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _
    (Space.preimage_pointsMap_over B S hS T a)]
  rfl

/-- **The gluing step of Stacks 0ARA.** Let `X` be a locally Noetherian algebraic space, `T ⊆ |X|`
closed, `g : W ⟶ X_{/T}` a morphism of fppf sheaves, and `wₖ : Wₖ ⟶ W` (`k ∈ K`, `K` nonempty
and `u`-small) representable étale morphisms which are jointly surjective. Suppose each
`Wₖ ⟶ X_{/T}` is the completion of a finite-type modification `Mₖ` of `X` away from `T`, each
`Wₖ ×_W Wₗ ⟶ X_{/T}` is the completion of a finite-type modification `N₍ₖ,ₗ₎`, and the atlases of
the `Mₖ` and `N₍ₖ,ₗ₎` and the index `K` are bounded by one cardinal `μ` below the cutoff. Then
`g` is the completion of a finite-type modification of `X` away from `T`.

This is the argument of Steps 2 and 3 of the source: full faithfulness (Stacks 0GDR) gives
`t₍ₖ,ₗ₎ : N₍ₖ,ₗ₎ ⟶ Mₖ` and `s₍ₖ,ₗ₎ : N₍ₖ,ₗ₎ ⟶ Mₗ` lifting the projections; with `V = ∐ Mₖ` and
`R = ∐ N₍ₖ,ₗ₎` (algebraic spaces by the size bound, Stacks 02WQ), Stacks 0AR8 makes
`(t, s) : R ⟶ V ×_X V` an étale equivalence relation; its quotient `X' = V/R` is an algebraic
space (Stacks 04S6), and `X'_{/T} ≅ W` because completion commutes with fibre products and
quotients. -/
theorem exists_finiteTypeModification_completion_iso_of_nonempty_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    {K : Type u} [Nonempty K] {Wk : K → FppfSheaf B S hS} (w : ∀ k, Wk k ⟶ W)
    (hw : ∀ k, IsRepresentableEtale B S hS (w k))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun i : ULift.{u + 1} K ↦ w i.down))
    (M : K → Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (γ : ∀ k, (Space.completionOverFunctor B S hS T).obj (M k).obj ≅ Over.mk (w k ≫ g))
    (N : K × K → Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (δ : ∀ p : K × K, (Space.completionOverFunctor B S hS T).obj (N p).obj ≅
      Over.mk (pullback.fst (w p.1) (w p.2) ≫ w p.1 ≫ g))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hMat : ∀ k, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ (M k).obj.left),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ)
    (hNat : ∀ p, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ (N p).obj.left),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    ∃ M' : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M'.obj ≅ Over.mk g) := by
  classical
  let J := BigFppfOver.topology B S hS
  have hMsp : ∀ k, IsAlgebraicSpace B S hS (M k).obj.left := fun k ↦ (M k).property.1.1
  have hNsp : ∀ p, IsAlgebraicSpace B S hS (N p).obj.left := fun p ↦ (N p).property.1.1
  have hMnoeth : ∀ k, Space.HasEtaleLocalProperty B S hS (M k).obj.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) := fun k ↦
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (hMsp k) hX (M k).obj.hom
      (M k).property.2 hXnoeth
  have hNnoeth : ∀ p, Space.HasEtaleLocalProperty B S hS (N p).obj.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) := fun p ↦
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (hNsp p) hX (N p).obj.hom
      (N p).property.2 hXnoeth
  -- the lifts `t₍ₖ,ₗ₎` and `s₍ₖ,ₗ₎`, from Stacks 0GDR
  have hlift : ∀ (p : K × K) (k : K) (pr : pullback (w p.1) (w p.2) ⟶ Wk k)
      (hpr : pr ≫ w k = pullback.fst (w p.1) (w p.2) ≫ w p.1),
      ∃ a : (N p).obj ⟶ (M k).obj, (Space.completionOverFunctor B S hS T).map a =
        (δ p).hom ≫ Over.homMk (U := Over.mk (pullback.fst (w p.1) (w p.2) ≫ w p.1 ≫ g))
          (V := Over.mk (w k ≫ g)) pr (by simp only [Over.mk_hom]; rw [reassoc_of% hpr]) ≫
            (γ k).inv :=
    fun p k _ _ ↦ (Space.completionOverFunctor_map_bijective hX hXnoeth hT (hMsp k)
      (M k).property.2 (M k).property.1.2 (N p).obj.hom (hNsp p) (hNnoeth p)).2 _
  choose tt htt using fun p : K × K ↦ hlift p p.1 (pullback.fst (w p.1) (w p.2)) rfl
  choose ss hss using fun p : K × K ↦ hlift p p.2 (pullback.snd (w p.1) (w p.2))
    pullback.condition.symm
  -- the coproducts `V = ∐ Mₖ` and `R = ∐ N₍ₖ,ₗ₎`
  let A : K → Sheaf J (Type u) := fun k ↦ Space.Descent.spaceSheaf (M k).obj.left (hMsp k)
  let C : K × K → Sheaf J (Type u) := fun p ↦ Space.Descent.spaceSheaf (N p).obj.left (hNsp p)
  let XS : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  have hKs : #(Shrink.{u} K) ≤ μ := by
    rw [← Cardinal.mk_congr (equivShrink.{u} K)]; exact hK
  have hKKs : #(Shrink.{u} (K × K)) ≤ μ := by
    rw [← Cardinal.mk_congr (equivShrink.{u} (K × K)), Cardinal.mk_prod, Cardinal.lift_id]
    exact (mul_le_mul' hK hK).trans (Cardinal.mul_eq_self hℵ).le
  obtain ⟨V, ιV, ⟨hV⟩, hVsp⟩ : ∃ (V : Sheaf J (Type u)) (ιV : ∀ k, A k ⟶ V),
      Nonempty (IsColimit (Cofan.mk V ιV)) ∧ IsAlgebraicSpace B S hS V.obj :=
    ⟨_, _, ⟨coproductIsCoproduct A⟩,
      Space.Descent.isAlgebraicSpace_sigma_of_size_le _ hMsp hℵ hμ hKs hMat⟩
  obtain ⟨R, κ, ⟨hR⟩, hRsp⟩ : ∃ (R : Sheaf J (Type u)) (κ : ∀ p, C p ⟶ R),
      Nonempty (IsColimit (Cofan.mk R κ)) ∧ IsAlgebraicSpace B S hS R.obj :=
    ⟨_, _, ⟨coproductIsCoproduct C⟩,
      Space.Descent.isAlgebraicSpace_sigma_of_size_le _ hNsp hℵ hμ hKKs hNat⟩
  obtain ⟨qVs, hqVs⟩ : ∃ qVs : V ⟶ XS, ∀ k, ιV k ≫ qVs = ObjectProperty.homMk (M k).obj.hom :=
    ⟨Cofan.IsColimit.desc hV _, Cofan.IsColimit.fac hV _⟩
  obtain ⟨qRs, hqRs⟩ : ∃ qRs : R ⟶ XS, ∀ p, κ p ≫ qRs = ObjectProperty.homMk (N p).obj.hom :=
    ⟨Cofan.IsColimit.desc hR _, Cofan.IsColimit.fac hR _⟩
  have hqV : ∀ k, (ιV k).hom ≫ qVs.hom = (M k).obj.hom := fun k ↦
    congrArg (fun φ ↦ φ.hom) (hqVs k)
  have hqR : ∀ p, (κ p).hom ≫ qRs.hom = (N p).obj.hom := fun p ↦
    congrArg (fun φ ↦ φ.hom) (hqRs p)
  let fst : ∀ p, C p ⟶ A p.1 := fun p ↦ ObjectProperty.homMk (tt p).left
  let snd : ∀ p, C p ⟶ A p.2 := fun p ↦ ObjectProperty.homMk (ss p).left
  have hfst : ∀ p, (fst p).hom ≫ (M p.1).obj.hom = (N p).obj.hom := fun p ↦ Over.w (tt p)
  have hsnd : ∀ p, (snd p).hom ≫ (M p.2).obj.hom = (N p).obj.hom := fun p ↦ Over.w (ss p)
  obtain ⟨t, ht⟩ : ∃ t : R ⟶ V, ∀ p, κ p ≫ t = fst p ≫ ιV p.1 :=
    ⟨Cofan.IsColimit.desc hR _, Cofan.IsColimit.fac hR _⟩
  obtain ⟨s, hs⟩ : ∃ s : R ⟶ V, ∀ p, κ p ≫ s = snd p ≫ ιV p.2 :=
    ⟨Cofan.IsColimit.desc hR _, Cofan.IsColimit.fac hR _⟩
  have ht' : t.hom ≫ qVs.hom = qRs.hom := congrArg (fun φ ↦ φ.hom)
    (Cofan.IsColimit.hom_ext hR (t ≫ qVs) qRs fun p ↦ by
      change κ p ≫ t ≫ qVs = κ p ≫ qRs
      rw [reassoc_of% (ht p), hqVs, hqRs]; exact ObjectProperty.hom_ext _ (hfst p))
  have hs' : s.hom ≫ qVs.hom = qRs.hom := congrArg (fun φ ↦ φ.hom)
    (Cofan.IsColimit.hom_ext hR (s ≫ qVs) qRs fun p ↦ by
      change κ p ≫ s ≫ qVs = κ p ≫ qRs
      rw [reassoc_of% (hs p), hqVs, hqRs]; exact ObjectProperty.hom_ext _ (hsnd p))
  -- the completed squares
  let β : ∀ k, Space.completionSheaf B S hS (A k).obj
      (Space.pointsMap B S hS _ (M k).obj.hom ⁻¹' T) ⟶ W := fun k ↦ (γ k).hom.left ≫ w k
  have hδ : ∀ p, IsIso (δ p).hom.left := fun p ↦
    inferInstanceAs (IsIso ((Over.forget _).map (δ p).hom))
  have hγ : ∀ k, IsIso (γ k).inv.left := fun k ↦
    inferInstanceAs (IsIso ((Over.forget _).map (γ k).inv))
  have hct : ∀ p, Space.completionOverMap B S hS T (tt p) =
      (δ p).hom.left ≫ pullback.fst (w p.1) (w p.2) ≫ (γ p.1).inv.left := fun p ↦ by
    simpa using congrArg CommaMorphism.left (htt p)
  have hcs : ∀ p, Space.completionOverMap B S hS T (ss p) =
      (δ p).hom.left ≫ pullback.snd (w p.1) (w p.2) ≫ (γ p.2).inv.left := fun p ↦ by
    simpa using congrArg CommaMorphism.left (hss p)
  have hsq : ∀ p, IsPullback
      (Space.completionSheafRestrict B S hS (tt p).left
        (Space.pointsMap B S hS (N p).obj.left (N p).obj.hom ⁻¹' T)
        (Space.pointsMap B S hS (M p.1).obj.left (M p.1).obj.hom ⁻¹' T)
        (preimage_subset_preimage_of_comp B S hS (tt p).left ((M p.1).obj.hom) ((N p).obj.hom)
          (hfst p) T))
      (Space.completionSheafRestrict B S hS (ss p).left
        (Space.pointsMap B S hS (N p).obj.left (N p).obj.hom ⁻¹' T)
        (Space.pointsMap B S hS (M p.2).obj.left (M p.2).obj.hom ⁻¹' T)
        (preimage_subset_preimage_of_comp B S hS (ss p).left ((M p.2).obj.hom) ((N p).obj.hom)
          (hsnd p) T))
      (β p.1) (β p.2) := fun p ↦ by
    rw [← completionOverMap_eq_completionSheafRestrict T (tt p),
      ← completionOverMap_eq_completionSheafRestrict T (ss p), hct, hcs]
    have aux : ∀ {P' X' Y' : FppfSheaf B S hS} (eP : P' ≅ pullback (w p.1) (w p.2))
        (eX : X' ≅ Wk p.1) (eY : Y' ≅ Wk p.2),
        IsPullback (eP.hom ≫ pullback.fst _ _ ≫ eX.inv) (eP.hom ≫ pullback.snd _ _ ≫ eY.inv)
          (eX.hom ≫ w p.1) (eY.hom ≫ w p.2) := fun eP eX eY ↦
      IsPullback.of_iso (IsPullback.of_hasPullback _ _) eP.symm eX.symm eY.symm (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
    exact aux ((Over.forget _).mapIso (δ p)) ((Over.forget _).mapIso (γ p.1))
      ((Over.forget _).mapIso (γ p.2))
  obtain ⟨φ, hφ, hpb⟩ := exists_isPullback_completionSheafRestrict_sigma (A := A) (C := C) (V := V)
    (R := R) (W := W) T (fun k ↦ hMsp k)
    (fun k ↦ (M k).obj.hom) ιV hV qVs.hom hqV (fun p ↦ hNsp p) (fun p ↦ (N p).obj.hom) κ hR
    qRs.hom hqR fst snd hfst hsnd t s ht hs ht' hs' β hsq
  have hφepi : Epi φ := ⟨fun {Z} h₁ h₂ hh ↦ by
    have hk : ∀ k, w k ≫ h₁ = w k ≫ h₂ := fun k ↦ by
      have h := congrArg (fun m ↦ Space.completionSheafRestrict B S hS (ιV k).hom _ _
        (preimage_subset_preimage_of_comp B S hS (ιV k).hom qVs.hom (M k).obj.hom (hqV k) T) ≫ m)
        hh
      simp only [← Category.assoc, hφ k] at h
      have h' : (γ k).hom.left ≫ w k ≫ h₁ = (γ k).hom.left ≫ w k ≫ h₂ :=
        (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
      have : IsIso (γ k).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (γ k).hom))
      exact (cancel_epi _).1 h'
    let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    have : Epi (Sigma.desc fun i : ULift.{u + 1} K ↦ w i.down) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp hcov
    rw [← cancel_epi (Sigma.desc fun i : ULift.{u + 1} K ↦ w i.down)]
    exact Sigma.hom_ext _ _ fun i ↦ by simp [hk i.down]⟩
  -- the relation `(t, s)` is an étale equivalence relation (Stacks 0AR8)
  have hrelc := (IsKernelPair.equivalenceRelation φ _ _ (pullback.isLimit _ _)
    hpb).isEquivalenceRelation
  have hopen := isPullback_openSubspaceOfPointsRestrict_sigma (A := A) (C := C) (V := V) (R := R) hX
    T hT
    (fun k ↦ hMsp k)
    (fun k ↦ (M k).obj.hom) (fun k ↦ (M k).property.1.2) hVsp ιV hV qVs.hom hqV
    (fun p ↦ hNsp p) (fun p ↦ (N p).obj.hom) (fun p ↦ (N p).property.1.2) hRsp κ hR qRs.hom hqR
    fst snd hfst hsnd t s ht hs ht' hs'
  have hrelo := (IsKernelPair.equivalenceRelation _ _ _ (pullback.isLimit _ _)
    hopen).isEquivalenceRelation
  have hqVft : Space.IsLocallyOfFiniteType B S hS qVs.hom :=
    isLocallyOfFiniteType_of_isColimit_cofan (A := A) (X := V) (fun k ↦ hMsp k) hVsp hX ιV hV
      qVs.hom fun k ↦ by rw [hqV]; exact (M k).property.2
  have hqRft : Space.IsLocallyOfFiniteType B S hS qRs.hom :=
    isLocallyOfFiniteType_of_isColimit_cofan (A := C) (X := R) (fun p ↦ hNsp p) hRsp hX κ hR
      qRs.hom fun p ↦ by rw [hqR]; exact (N p).property.2
  obtain ⟨-, hrel⟩ := isEquivalenceRelation_of_openComplement_and_completionSheaf B S hS hX
    hRsp hVsp qRs.hom qVs.hom s.hom t.hom hs' ht' T hT hXnoeth hqRft hqVft hrelo hrelc
  have hιet : ∀ k, Space.IsEtale B S hS (ιV k).hom :=
    (isEtaleCovering_of_isColimit_cofan (A := A) (X := V) (fun k ↦ hMsp k) hVsp ιV hV).etale
  have hliftet : ∀ (p : K × K) (k : K) (a : (N p).obj ⟶ (M k).obj)
      (pr : pullback (w p.1) (w p.2) ⟶ Wk k),
      IsRepresentableEtale B S hS pr →
      Space.completionOverMap B S hS T a = (δ p).hom.left ≫ pr ≫ (γ k).inv.left →
      Space.IsEtale B S hS a.left := by
    intro p k a pr hpr ha
    refine isEtale_of_isRepresentableEtale_completionSheafMap hX (hNsp p) (hMsp k) hXnoeth T hT
      a.left (N p).obj.hom (M k).obj.hom (Over.w a) (N p).property.2 (M k).property.2
      (N p).property.1.2 (M k).property.1.2 ?_
    have key : IsRepresentableEtale B S hS (Space.completionOverMap B S hS T a) := by
      rw [ha]
      exact (@isRepresentableEtale_of_isIso B S hS _ _ _ (hδ p)).comp B S hS
        (hpr.comp B S hS (@isRepresentableEtale_of_isIso B S hS _ _ _ (hγ k)))
    have h2 : Space.completionSheafMap B S hS a.left
        (Space.pointsMap B S hS _ (M k).obj.hom ⁻¹' T) =
          eqToHom (congrArg (Space.completionSheaf B S hS (N p).obj.left)
            (Space.preimage_pointsMap_over B S hS T a)).symm ≫
          Space.completionOverMap B S hS T a := by
      simp [Space.completionOverMap]
    rw [h2]
    exact (isRepresentableEtale_of_isIso B S hS _).comp B S hS key
  have htet : Space.IsEtale B S hS t.hom :=
    isEtale_of_isColimit_cofan (A := C) (X := R) (fun p ↦ hNsp p) hRsp hVsp κ hR t.hom fun p ↦ by
      rw [show (κ p).hom ≫ t.hom = (tt p).left ≫ (ιV p.1).hom from
        congrArg (fun φ ↦ φ.hom) (ht p)]
      exact Space.isEtale_comp B S hS (hliftet p p.1 (tt p) _
        (isRepresentableEtale_pullback_fst B S hS _ _ (hw p.2)) (hct p)) (hιet p.1)
  have hset : Space.IsEtale B S hS s.hom :=
    isEtale_of_isColimit_cofan (A := C) (X := R) (fun p ↦ hNsp p) hRsp hVsp κ hR s.hom fun p ↦ by
      rw [show (κ p).hom ≫ s.hom = (ss p).left ≫ (ιV p.2).hom from
        congrArg (fun φ ↦ φ.hom) (hs p)]
      exact Space.isEtale_comp B S hS (hliftet p p.2 (ss p) _
        (isRepresentableEtale_pullback_snd B S hS _ _ (hw p.1)) (hcs p)) (hιet p.2)
  -- the quotient `V/R` (Stacks 04S6) and its completion
  obtain ⟨Q, π, qQ, hπ, hk, hQ, hπet, hπs, hπq⟩ := exists_quotient_of_isEquivalenceRelation
    hX.isSheaf hVsp hRsp qVs.hom qRs.hom t s ht' hs' hrel htet hset
  have hφg : φ ≫ g = Space.completionSheafMap B S hS qVs.hom T := by
    obtain ⟨hc⟩ := nonempty_isColimit_cofan_completionSheafRestrict (A := A) (V := V) T
      (fun k ↦ hMsp k) (fun k ↦ (M k).obj.hom) ιV hV qVs.hom hqV
    refine Cofan.IsColimit.hom_ext hc _ _ fun k ↦ ?_
    change Space.completionSheafRestrict B S hS (ιV k).hom _ _ _ ≫ φ ≫ g =
      Space.completionSheafRestrict B S hS (ιV k).hom _ _ _ ≫
        Space.completionSheafMap B S hS qVs.hom T
    rw [reassoc_of% (hφ k), ← Space.completionSheafRestrict_self B S hS qVs.hom T subset_rfl,
      completionSheafRestrict_comp_eq B S hS _ _ _ (hqV k) _ _ _ _ _ subset_rfl,
      Space.completionSheafRestrict_self]
    simpa [β] using Over.w (γ k).hom
  have := hπ
  obtain ⟨e, he⟩ := exists_iso_completionSheaf_of_isPullback T π t s hk qVs.hom qRs.hom qQ hπq
    ht' hs' φ hpb g hφg
  have hQft : Space.IsLocallyOfFiniteType B S hS qQ :=
    Space.isLocallyOfFiniteType_of_comp_of_isEtale_of_isSurjective B S hS hVsp hQ hX hπet hπs
      (by rw [hπq]; exact hqVft)
  -- the quotient is an isomorphism over `U`, through a section of `V` over `U`
  obtain ⟨k₀⟩ := (inferInstance : Nonempty K)
  have h₀ : (Space.pointsMap B S hS _ (M k₀).obj.hom ⁻¹' T)ᶜ ⊆
      Space.pointsMap B S hS _ (M k₀).obj.hom ⁻¹' Tᶜ := by rw [Set.preimage_compl]
  have hr₀ := isIso_openSubspaceOfPointsRestrict_of_isIso_pullback_snd T (M k₀).obj.hom
    (M k₀).property.1.2 rfl h₀
  let σ := inv (Space.openSubspaceOfPointsRestrict B S hS (M k₀).obj.hom _ Tᶜ h₀) ≫
    Space.openSubspaceOfPointsRestrict B S hS (ιV k₀).hom _ _
      (compl_subset_preimage_compl B S hS (ιV k₀).hom qVs.hom (M k₀).obj.hom (hqV k₀) T)
  have hσ : σ ≫ Space.openSubspaceOfPointsRestrict B S hS qVs.hom _ Tᶜ
      (by rw [Set.preimage_compl]) = 𝟙 _ := by
    simp only [σ, Category.assoc]
    rw [← Space.openSubspaceOfPointsRestrict_comp B S hS _ _ _ _ _ _ _
        (by rw [hqV]; exact h₀),
      Space.openSubspaceOfPointsRestrict_congr B S hS (hqV k₀) _ _ _ h₀, IsIso.inv_hom_id]
  have hQU := isIso_pullback_snd_of_isPullback_quotient hX T hT hVsp hQ hRsp π t s hk qVs.hom
    qRs.hom qQ hπq ht' hs' hopen σ hσ
  exact ⟨⟨Over.mk qQ, ⟨hQ, hQU⟩, hQft⟩, ⟨Over.isoMk e he⟩⟩

/-- **The gluing step of Stacks 0ARA, for an empty covering.** If an empty family covers `W`,
then `W` is empty, and it is the completion of the open subspace `U` cut out by `|X| ∖ T`, whose
completion along the (empty) inverse image of `T` is empty. -/
theorem exists_finiteTypeModification_completion_iso_of_isEmpty
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    {K : Type u} [IsEmpty K] {Wk : K → FppfSheaf B S hS} (w : ∀ k, Wk k ⟶ W)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun i : ULift.{u + 1} K ↦ w i.down)) :
    ∃ M' : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M'.obj ≅ Over.mk g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  have hUo : Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hX _ hT.isOpen_compl
  have hUft : Space.IsLocallyOfFiniteType B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ).ι :=
    Space.isLocallyOfFiniteType_of_isEtale B S hS hX (Space.isEtale_ι_of_isOpenSubspace hUo)
  let M' : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) :=
    ⟨Over.mk (Space.openSubspaceOfPoints B S hS X Tᶜ).ι, ⟨hUo.1,
      (inferInstance : IsIso (pullback.snd (Space.openSubspaceOfPoints B S hS X Tᶜ).ι
        (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))⟩, hUft⟩
  have hempty : Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ⁻¹' T = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hp
    have hr : Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι p ∈
        Set.range (Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) :=
      ⟨p, rfl⟩
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints] at hr
    exact hr hp
  have hC : IsInitial ((Space.completionOverFunctor B S hS T).obj M'.obj).left := by
    refine Sheaf.isInitialOfBotMem fun V y ↦ ?_
    have hsieve := Presheaf.imageSieve_mem J (J.toSheafify (Space.completionSubfunctor B S hS
      (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor
      (Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ⁻¹' T)).toFunctor)
      (U := Opposite.op V) y
    refine J.transitive hsieve ⊥ fun V' f hf ↦ ?_
    obtain ⟨t, -⟩ := hf
    rw [Sieve.pullback_bot]
    exact Space.bot_mem_of_mem_openSubspaceOfPoints B S hS hempty (s := t.1.down)
      ((Space.mem_openSubspaceOfPoints_iff B S hS _ _).2
        ((Space.hasImageIn_iff_range_subset B S hS _ V' t.1.down).1 t.2))
  have hWi : IsInitial W := by
    refine Sheaf.isInitialOfBotMem fun V x ↦ ?_
    obtain ⟨T', hT', hT'm⟩ := Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc
      (fun i : ULift.{u + 1} K ↦ w i.down) hcov x
    refine J.superset_covering (fun V' f hf ↦ ?_) hT'
    obtain ⟨i, -⟩ := hT'm f hf
    exact (IsEmpty.false i.down).elim
  exact ⟨M', ⟨Over.isoMk (hC.uniqueUpToIso hWi) (hC.hom_ext _ _)⟩⟩

/-- **The gluing step of Stacks 0ARA**, for a covering indexed by any `u`-small type: the
nonempty case is `exists_finiteTypeModification_completion_iso_of_nonempty_cover`, and an empty
covering forces `W` to be empty
(`exists_finiteTypeModification_completion_iso_of_isEmpty`). -/
theorem exists_finiteTypeModification_completion_iso_of_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    {K : Type u} {Wk : K → FppfSheaf B S hS} (w : ∀ k, Wk k ⟶ W)
    (hw : ∀ k, IsRepresentableEtale B S hS (w k))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun i : ULift.{u + 1} K ↦ w i.down))
    (M : K → Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (γ : ∀ k, (Space.completionOverFunctor B S hS T).obj (M k).obj ≅ Over.mk (w k ≫ g))
    (N : K × K → Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (δ : ∀ p : K × K, (Space.completionOverFunctor B S hS T).obj (N p).obj ≅
      Over.mk (pullback.fst (w p.1) (w p.2) ≫ w p.1 ≫ g))
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hMat : ∀ k, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ (M k).obj.left),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ)
    (hNat : ∀ p, ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ (N p).obj.left),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ) :
    ∃ M' : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M'.obj ≅ Over.mk g) := by
  rcases isEmpty_or_nonempty K with hKe | hKn
  · exact exists_finiteTypeModification_completion_iso_of_isEmpty hX T hT g w hcov
  · exact exists_finiteTypeModification_completion_iso_of_nonempty_cover hX hXnoeth T hT g w hw
      hcov M γ N δ hℵ hμ hK hMat hNat

/-! ### Step 1, with a bound on the atlas -/

/-- **Step 1 of the proof of Stacks 0ARA, with a uniform bound on the atlas.** Let
`X = Spec R` be a Noetherian affine scheme of the site, `T ⊆ |X|` closed, `W` a Noetherian
affine formal algebraic space and `g : W ⟶ X_{/T}` rig-étale. Then `g` is the completion of a
finite-type modification `M` of `X` away from `T`, and `M` has a surjective étale atlas of size at
most `2 ^ 2 ^ size (Spec R)`, a bound which does not depend on `W`.

The algebraization is that of Stacks 0AR4 followed by Stacks 0AR9. The output `X''` of Stacks 0AR9
has the same completion as the finite type `X' ⟶ X` of Stacks 0AR4, which is affine of size at
most `size (Spec R)`; the quotient stages of `X'` along `T` glue to one object of the site of
cardinality at most `2 ^ 2 ^ size (Spec R)` covering that completion
(`exists_epi_uliftYoneda_completionSheaf_of_isAffine`), and
`AlgebraicGeometry.Space.exists_atlas_size_le_of_epi_completionSheaf` turns this into the atlas
bound. -/
theorem exists_finiteTypeModification_completion_iso_atlas_size_le
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (hWnoeth : IsNoetherian B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M.obj ≅ Over.mk g) ∧
      (∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ M.obj.left),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        ((BigFppfOver.toScheme B S hS).obj V).size ≤
          (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (Spec (.of R)).size) ∧
      ∃ (P : BigFppfOver B S hS)
        (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj P ⟶ W),
        Epi q ∧ ((BigFppfOver.toScheme B S hS).obj P).size ≤
          (2 : Cardinal.{u}) ^ (Spec (.of R)).size := by
  obtain ⟨X', hX'aff, f, e, hlft, hqc, het, he, -⟩ :=
    exists_affine_algebraization_of_isRigEtale B S hS hR s T hT hWaff hWnoeth g hg
  have hXsp := isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)
  have hX'sp := isAlgebraicSpace_yoneda B S hS X'
  have hfU := isEtale_pullback_snd_openSubspaceOfPoints_of_etaleAt f T hT het
  obtain ⟨X'', hX'', g', p, hgp, hp, hpU, hiso⟩ :=
    exists_factorization_isIso_completionSheafMap B S hS hXsp hX'sp T hT (yoneda.map f)
      ((Space.isLocallyOfFiniteType_yoneda_map_iff B S hS f).mpr hlft)
      (by rw [openSubspacesOrderIso_symm_compl B S hS hXsp T hT]; exact hfU)
  rw [openSubspacesOrderIso_symm_compl B S hS hXsp T hT] at hpU
  set σ := (Spec (.of R)).size with hσ
  have hX'size : ((BigFppfOver.toScheme B S hS).obj X').size ≤ σ :=
    @Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact _ _
      ((BigFppfOver.toScheme B S hS).map f) hlft hqc
  have := hX'aff
  obtain ⟨V, q, hq, hVsize, hVcard⟩ := exists_epi_uliftYoneda_completionSheaf_of_isAffine X'
    (Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' T)
    (hT.preimage (Space.continuous_pointsMap B S hS _)) hX'size
  refine ⟨⟨Over.mk p, ⟨hX'', hpU⟩, hp⟩, ⟨?_⟩, ?_, V, q ≫ e.hom, epi_comp' hq inferInstance, hVsize⟩
  · let a : Over.mk (yoneda.map f) ⟶ Over.mk p := Over.homMk g' hgp
    have hleft : IsIso ((Space.completionOverFunctor B S hS T).map a).left := by
      change IsIso (Space.completionOverMap B S hS T a)
      unfold Space.completionOverMap
      have : IsIso (Space.completionSheafMap B S hS a.left
          (Space.pointsMap B S hS (Over.mk p).left (Over.mk p).hom ⁻¹' T)) := hiso
      infer_instance
    have : IsIso ((Space.completionOverFunctor B S hS T).map a) :=
      have : IsIso ((Over.forget _).map ((Space.completionOverFunctor B S hS T).map a)) := hleft
      isIso_of_reflects_iso _ (Over.forget _)
    exact (asIso ((Space.completionOverFunctor B S hS T).map a)).symm ≪≫ Over.isoMk e he
  · have hRc : σ < B.cutoff := hR
    have hset : Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' T =
        Space.pointsMap B S hS _ g' ⁻¹' (Space.pointsMap B S hS X'' p ⁻¹' T) := by
      rw [Space.preimage_pointsMap_preimage_pointsMap, hgp]
    have := hiso
    have := hq
    have hℵ : ℵ₀ ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ σ :=
      ((Scheme.aleph0_le_size _).trans (cantor σ).le).trans (cantor _).le
    exact Space.exists_atlas_size_le_of_epi_completionSheaf hX'' p hp T hpU
      (q ≫ eqToHom (congrArg (Space.completionSheaf B S hS (yoneda.obj X')) hset) ≫
        Space.completionSheafMap B S hS g' (Space.pointsMap B S hS X'' p ⁻¹' T)) hℵ
      (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hRc))
      ((cantor σ).le.trans (cantor _).le)
      ((Scheme.mk_le_two_pow_size _).trans (cantor _).le) hVcard

/-! ### Step 2: a separated `W` -/

/-- The presheaf represented by `Spec R`, for a Noetherian ring `R`, has the étale local property
of being locally Noetherian. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_affineOver (hS : B.Contains S)
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S) :
    Space.HasEtaleLocalProperty B S hS (yoneda.obj (affineOver B S hS hR s))
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
  (Space.exists_atlas_iff_of_representable B S hS _
    (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) _ (Iso.refl _)).2
    (show _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)) from inferInstance)

/-- **Step 2 of the proof of Stacks 0ARA.** Let `X = Spec R` be a Noetherian affine scheme of the
site, `T ⊆ |X|` closed, and `g : W ⟶ X_{/T}` a rig-étale morphism from a locally Noetherian
formal algebraic space `W` which is separated (clause (2) of Stacks 0AJ7). Then `g` is the
completion of a finite-type modification of `X` away from `T`.

An atlas of `W` indexed below the cutoff (`exists_isFormalAtlas_of_mk_lt_cutoff`) consists of
Noetherian affine formal algebraic spaces `Wₖ`, and the `Wₖ ×_W Wₗ` are Noetherian affine
because `W` is separated; Step 1 algebraizes all of them with atlases bounded by
`2 ^ 2 ^ size (Spec R)`, and the gluing step
`exists_finiteTypeModification_completion_iso_of_cover` glues the algebraizations. -/
theorem exists_finiteTypeModification_completion_iso_of_isSeparated
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W) (hWsep : IsSeparated B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M.obj ≅ Over.mk g) := by
  have hXsp := isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)
  have hXnoeth := hasEtaleLocalProperty_isLocallyNoetherian_affineOver hS hR s
  obtain ⟨K, Xi, f, hK, haff, hrep, hcov⟩ := exists_isFormalAtlas_of_mk_lt_cutoff B S hS W hW.1
  have hrep' : ∀ i, IsRepresentableEtale B S hS (f i) := hrep
  have hnoeth : ∀ i, IsNoetherian B S hS (Xi i) := fun i ↦
    isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hW _ (haff i) (hrep' i)
  have hMk := fun k : K ↦
    exists_finiteTypeModification_completion_iso_atlas_size_le hR s T hT (haff ⟨k⟩)
      (hnoeth ⟨k⟩) (f ⟨k⟩ ≫ g) (isRigEtale_comp_of_isRepresentableEtale _ (hrep' ⟨k⟩) g hg)
  choose M hM hMat _ using hMk
  choose V a hsurj het hsize using hMat
  have hpair : ∀ p : K × K, ∃ N : Space.FiniteTypeModification B S hS
      (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj N.obj ≅
        Over.mk (pullback.fst (f ⟨p.1⟩) (f ⟨p.2⟩) ≫ f ⟨p.1⟩ ≫ g)) ∧
      ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ N.obj.left),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        ((BigFppfOver.toScheme B S hS).obj V).size ≤
          (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (Spec (.of R)).size := fun p ↦ by
    obtain ⟨haffp, hnoethp, hrepp⟩ := isNoetherian_pullback_of_isSeparated hW hWsep (f ⟨p.1⟩)
      (f ⟨p.2⟩) (haff _) (haff _) (hrep' _) (hrep' _)
    have hrig := isRigEtale_comp_of_isRepresentableEtale _ hrepp g hg
    rw [Category.assoc] at hrig
    obtain ⟨N, h1, h2, -⟩ :=
      exists_finiteTypeModification_completion_iso_atlas_size_le hR s T hT haffp hnoethp _ hrig
    exact ⟨N, h1, h2⟩
  choose N hN VN aN hsurjN hetN hsizeN using hpair
  set μ := max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (Spec (.of R)).size) #K with hμ
  have hRc : (Spec (.of R)).size < B.cutoff := hR
  exact exists_finiteTypeModification_completion_iso_of_cover hXsp hXnoeth T hT g
    (fun k : K ↦ f ⟨k⟩) (fun k ↦ hrep' ⟨k⟩) hcov M (fun k ↦ (hM k).some) N (fun p ↦ (hN p).some)
    (μ := μ) (le_max_of_le_left (((Scheme.aleph0_le_size _).trans (cantor _).le).trans
      (cantor _).le))
    (max_lt (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hRc)) hK) (le_max_right _ _)
    (fun k ↦ ⟨V k, a k, hsurj k, het k, (hsize k).trans (le_max_left _ _)⟩)
    (fun p ↦ ⟨VN p, aN p, hsurjN p, hetN p, (hsizeN p).trans (le_max_left _ _)⟩)

/-! ### Step 3: a general `W` -/

/-- An fppf sheaf with a monomorphism into a separated one (clause (2) of Stacks 0AJ7) is
separated: a fibre product over the source is a fibre product over the target. -/
theorem isSeparated_of_mono {Y P : FppfSheaf B S hS} (m : Y ⟶ P) [Mono m]
    (hP : IsSeparated B S hS P) : IsSeparated B S hS Y :=
  fun U V Q a b p q hU hV hsq ↦ hP U V Q (a ≫ m) (b ≫ m) p q hU hV
    ⟨⟨by rw [reassoc_of% hsq.w]⟩, ⟨PullbackCone.isLimitOfCompMono a b m _ hsq.isLimit⟩⟩

/-- An affine formal algebraic space with a morphism to the completion of a Noetherian affine
object of the site along a closed set is separated, as it maps to the affine scheme. -/
private theorem isSeparated_of_hom_completionSheaf_affineOver
    {R : Type u} [CommRing R] (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    {T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))} {P : FppfSheaf B S hS}
    (h : P ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hP : IsAffineFormalAlgebraicSpace B S hS P) : IsSeparated B S hS P :=
  isSeparated_of_isAffineFormalAlgebraicSpace B S hS (Z := affineOver B S hS hR s)
    (show IsAffine (Spec (.of R)) from inferInstance)
    (h ≫ Space.completionSheafRestrict B S hS (𝟙 _) T Set.univ (fun _ _ ↦ Set.mem_univ _) ≫
      (Space.uliftYonedaIsoCompletionSheaf (affineOver B S hS hR s) rfl).inv ≫
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).inv.app _) hP

/-- The completion of a Noetherian affine object of the site along a closed set is separated
(clause (2) of Stacks 0AJ7): it is an affine formal algebraic space (Stacks 0AIY) mapping to the
affine scheme. -/
@[ega "I 10.15.7" "special case"]
theorem isSeparated_completionSheaf_affineOver
    {R : Type u} [CommRing R] (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T) :
    IsSeparated B S hS (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T) := by
  have haff : IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T) := by
    obtain ⟨I, rfl⟩ := exists_zeroLocusPoints_eq_of_isClosed B S hS hR s T hT
    exact isAffineFormalAlgebraicSpace_zeroLocusCompletion B S hS hR s I
      (hasStageAtlas B S hS hR s I)
  exact isSeparated_of_hom_completionSheaf_affineOver hR s (𝟙 _) haff

/-- **A representable surjecting onto a fibre product, of controlled size.** Let `W` be a formal
algebraic space, `wₖ : Wₖ ⟶ W` and `wₗ : Wₗ ⟶ W`, and `qₖ : h_{Pₖ} ⟶ Wₖ`, `qₗ : h_{Pₗ} ⟶ Wₗ`
surjections from representable sheaves with `size Pₖ, size Pₗ ≤ ν`. Then `Wₖ ×_W Wₗ` receives a
surjection from a representable sheaf `h_Q` with `size Q ≤ 2 ^ 2 ^ ν`: `Q` represents
`h_{Pₖ} ×_W h_{Pₗ}` (the diagonal of `W` is representable, Stacks 0AIP) and maps
monomorphically to `Pₖ ×_S Pₗ`. -/
theorem exists_epi_uliftYoneda_pullback_of_isFormalAlgebraicSpace {W Wk Wl : FppfSheaf B S hS}
    (hW : IsFormalAlgebraicSpace B S hS W) (wk : Wk ⟶ W) (wl : Wl ⟶ W)
    {Pk Pl : BigFppfOver B S hS}
    (qk : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj Pk ⟶ Wk)
    (ql : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj Pl ⟶ Wl) [Epi qk] [Epi ql]
    {ν : Cardinal.{u}} (hk : ((BigFppfOver.toScheme B S hS).obj Pk).size ≤ ν)
    (hl : ((BigFppfOver.toScheme B S hS).obj Pl).size ≤ ν) :
    ∃ (Q : BigFppfOver B S hS)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj Q ⟶ pullback wk wl),
      Epi q ∧ ((BigFppfOver.toScheme B S hS).obj Q).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ν := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let sY := Sheaf.sheafifiedYoneda J
  let : sY.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let : sY.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let e := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  let ak : sY.obj Pk ⟶ Wk := e.hom.app Pk ≫ qk
  let al : sY.obj Pl ⟶ Wl := e.hom.app Pl ≫ ql
  have hrepk := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hW (ak ≫ wk)
  let Q := hrepk.pullback (al ≫ wl)
  let fst' : Q ⟶ Pk := hrepk.fst' (al ≫ wl)
  let snd : Q ⟶ Pl := hrepk.snd (al ≫ wl)
  have hpb : IsPullback (sY.map fst') (sY.map snd) (ak ≫ wk) (al ≫ wl) :=
    hrepk.isPullback' (al ≫ wl)
  -- the size of `Q`
  let m : Q ⟶ Pk ⨯ Pl := prod.lift fst' snd
  have hm : Mono m := ⟨fun a b hab ↦ by
    have h₁ : a ≫ fst' = b ≫ fst' := by simpa [m] using hab =≫ prod.fst
    have h₂ : a ≫ snd = b ≫ snd := by simpa [m] using hab =≫ prod.snd
    exact sY.map_injective (hpb.hom_ext (by simp only [← Functor.map_comp, h₁])
      (by simp only [← Functor.map_comp, h₂]))⟩
  have : Mono ((BigFppfOver.toScheme B S hS).map m) :=
    CategoryTheory.preserves_mono_of_preservesLimit (BigFppfOver.toScheme B S hS) m
  have hQ₁ := Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map m)
  have hprod : ((BigFppfOver.toScheme B S hS).obj (Pk ⨯ Pl)).size ≤ ν := by
    rw [Scheme.size_congr ((BigFppfOver.toScheme B S hS).mapIso (prodIsoPullback Pk Pl))]
    exact (Space.size_pullback_le B S hS _ _).trans (max_le hk hl)
  -- the surjection, through two base changes of surjections
  let L2 : pullback wk (al ≫ wl) ⟶ pullback wk wl :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ al) (by simp [pullback.condition])
  have hL2 : IsPullback L2 (pullback.snd wk (al ≫ wl)) (pullback.snd wk wl) al :=
    IsPullback.of_right (by
        rw [show L2 ≫ pullback.fst wk wl = pullback.fst wk (al ≫ wl) from pullback.lift_fst _ _ _]
        exact IsPullback.of_hasPullback wk (al ≫ wl))
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback wk wl)
  let L1 : sY.obj Q ⟶ pullback wk (al ≫ wl) :=
    pullback.lift (sY.map fst' ≫ ak) (sY.map snd) (by simpa using hpb.w)
  have hL1 : IsPullback L1 (sY.map fst') (pullback.fst wk (al ≫ wl)) ak :=
    IsPullback.of_right (by
        rw [show L1 ≫ pullback.snd wk (al ≫ wl) = sY.map snd from pullback.lift_snd _ _ _]
        exact hpb.flip)
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback wk (al ≫ wl)).flip
  have hepi : ∀ {A A' C' D : FppfSheaf B S hS} {p : A ⟶ A'} {q' : A ⟶ C'} {g' : A' ⟶ D}
      {f' : C' ⟶ D}, IsPullback p q' g' f' → Epi f' → Epi p := fun {A A' C' D p q' g' f'} h hf ↦ by
    have : Presheaf.IsLocallySurjective J f'.hom :=
      (Sheaf.isLocallySurjective_iff_epi f').2 hf
    have : Presheaf.IsLocallySurjective J ((sheafToPresheaf J _).map f') := this
    have hp : Presheaf.IsLocallySurjective J p.hom :=
      Presheaf.isLocallySurjective_of_isPullback J (h.map (sheafToPresheaf J _))
    exact (Sheaf.isLocallySurjective_iff_epi p).1 hp
  exact ⟨Q, e.inv.app Q ≫ L1 ≫ L2, epi_comp' inferInstance
    (epi_comp' (hepi hL1 (epi_comp' inferInstance inferInstance))
      (hepi hL2 (epi_comp' inferInstance inferInstance))),
    hQ₁.trans (max_le (two_pow_le_two_pow
        ((Scheme.mk_le_two_pow_size _).trans (two_pow_le_two_pow hprod)))
      (hprod.trans ((cantor ν).le.trans (cantor _).le)))⟩

/-- **Stacks 0ARA, essential surjectivity.** Let `X = Spec R` be a Noetherian affine scheme of the
site, `T ⊆ |X|` closed, and `g : W ⟶ X_{/T}` a rig-étale morphism from a locally Noetherian
formal algebraic space `W`. Then `g` is the completion of a finite-type modification of `X` away
from `T`.

This is Step 3 of the source. For an atlas `{Wₖ}` of `W` indexed below the cutoff, the `Wₖ` are
algebraized by Step 1, and each `Wₖ ×_W Wₗ` is a locally Noetherian formal algebraic space which
is separated, because it maps monomorphically to the affine formal algebraic space
`Wₖ ×_{X_{/T}} Wₗ`; so Step 2 algebraizes it. Its algebraization has an atlas bounded
independently of `k, l`, since `Wₖ ×_W Wₗ` is covered by a representable sheaf of bounded size
(`exists_epi_uliftYoneda_pullback_of_isFormalAlgebraicSpace`). The gluing step then applies. -/
theorem exists_finiteTypeModification_completion_iso_of_isRigEtale
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M.obj ≅ Over.mk g) := by
  have hXsp := isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)
  have hXnoeth := hasEtaleLocalProperty_isLocallyNoetherian_affineOver hS hR s
  set σ := (Spec (.of R)).size with hσ
  have hRc : σ < B.cutoff := hR
  obtain ⟨K, Xi, f, hK, haff, hrep, hcov⟩ := exists_isFormalAtlas_of_mk_lt_cutoff B S hS W hW.1
  have hrep' : ∀ i, IsRepresentableEtale B S hS (f i) := hrep
  have hnoeth : ∀ i, IsNoetherian B S hS (Xi i) := fun i ↦
    isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hW _ (haff i) (hrep' i)
  have hMk := fun k : K ↦
    exists_finiteTypeModification_completion_iso_atlas_size_le hR s T hT (haff ⟨k⟩)
      (hnoeth ⟨k⟩) (f ⟨k⟩ ≫ g) (isRigEtale_comp_of_isRepresentableEtale _ (hrep' ⟨k⟩) g hg)
  choose M hM hMat hMepi using hMk
  choose V a hsurj het hsize using hMat
  choose P qP hqP hPsize using hMepi
  -- the completion `X_{/T}` and the affine formal `Wₖ ×_{X/T} Wₗ`
  have hXT := isFormalAlgebraicSpace_completionSheaf_of_isClosed hXsp T hT
  have hXTsep := isSeparated_completionSheaf_affineOver hR s T hT
  set μN := (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
    (2 : Cardinal.{u}) ^ σ with hμN
  have hpair : ∀ p : K × K, ∃ N : Space.FiniteTypeModification B S hS
      (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj N.obj ≅
        Over.mk (pullback.fst (f ⟨p.1⟩) (f ⟨p.2⟩) ≫ f ⟨p.1⟩ ≫ g)) ∧
      ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ N.obj.left),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
        ((BigFppfOver.toScheme B S hS).obj V).size ≤ μN := fun p ↦ by
    let wk := f ⟨p.1⟩
    let wl := f ⟨p.2⟩
    have hYf : IsFormalAlgebraicSpace B S hS (pullback wk wl) :=
      isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS wk wl hW.1
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haff _))
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haff _))
    have hYrep : IsRepresentableEtale B S hS (pullback.fst wk wl ≫ wk) :=
      (isRepresentableEtale_pullback_fst B S hS _ _ (hrep' _)).comp B S hS (hrep' _)
    have hYn : IsLocallyNoetherian B S hS (pullback wk wl) := by
      obtain ⟨-, I, Zi, z, hzaff, hzet, hzsurj⟩ := id hYf
      exact ⟨hYf, I, Zi, z, hzaff, hzet, hzsurj, fun i =>
        isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hW _
          (hzaff i) (IsRepresentableEtale.comp B S hS (hzet i) hYrep)⟩
    have hPaff : IsAffineFormalAlgebraicSpace B S hS (pullback (wk ≫ g) (wl ≫ g)) :=
      isAffineFormalAlgebraicSpace_pullback B S hS _ _
        (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hXT) hXTsep
        (haff _) (haff _)
    have hPsep : IsSeparated B S hS (pullback (wk ≫ g) (wl ≫ g)) :=
      isSeparated_of_hom_completionSheaf_affineOver hR s (pullback.fst _ _ ≫ wk ≫ g) hPaff
    have : Mono (pullback.mapDesc wk wl g) := pullback.mono_mapDesc wk wl g
    have hYsep : IsSeparated B S hS (pullback wk wl) :=
      isSeparated_of_mono (pullback.mapDesc wk wl g) hPsep
    have hrig := isRigEtale_comp_of_isRepresentableEtale _ hYrep g hg
    rw [Category.assoc] at hrig
    obtain ⟨N, ⟨eN⟩⟩ := exists_finiteTypeModification_completion_iso_of_isSeparated hR s T hT hYn
      hYsep _ hrig
    refine ⟨N, ⟨eN⟩, ?_⟩
    have := hqP p.1
    have := hqP p.2
    obtain ⟨Q, q, hq, hQ⟩ := exists_epi_uliftYoneda_pullback_of_isFormalAlgebraicSpace hW.1 wk wl
      (qP p.1) (qP p.2) (hPsize p.1) (hPsize p.2)
    have hinv : Epi eN.inv.left := inferInstanceAs (Epi ((Over.forget _).map eN.inv))
    let q' : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj Q ⟶
        Space.completionSheaf B S hS N.obj.left (Space.pointsMap B S hS _ N.obj.hom ⁻¹' T) :=
      q ≫ eN.inv.left
    have : Epi q' := epi_comp' hq hinv
    exact Space.exists_atlas_size_le_of_epi_completionSheaf N.property.1.1 N.obj.hom
      N.property.2 T N.property.1.2 q'
      (((Scheme.aleph0_le_size _).trans (cantor σ).le).trans
        (((cantor _).le.trans (cantor _).le).trans ((cantor _).le.trans (cantor _).le)))
      (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit
        (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hRc)))))
      (((cantor σ).le.trans (cantor _).le).trans (((cantor _).le.trans (cantor _).le).trans
        (cantor _).le))
      ((Scheme.mk_le_two_pow_size _).trans (((cantor _).le.trans (cantor _).le).trans
        ((cantor _).le.trans (cantor _).le)))
      ((Scheme.mk_le_two_pow_size _).trans (two_pow_le_two_pow (hQ.trans (cantor _).le)))
  choose N hN VN aN hsurjN hetN hsizeN using hpair
  set μ := max (max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ σ) μN) #K with hμ
  exact exists_finiteTypeModification_completion_iso_of_cover hXsp hXnoeth T hT g
    (fun k : K ↦ f ⟨k⟩) (fun k ↦ hrep' ⟨k⟩) hcov M (fun k ↦ (hM k).some) N (fun p ↦ (hN p).some)
    (μ := μ) (le_max_of_le_left (le_max_of_le_left
      (((Scheme.aleph0_le_size _).trans (cantor _).le).trans (cantor _).le)))
    (max_lt (max_lt (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hRc))
      (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit
        (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hRc)))))) hK) (le_max_right _ _)
    (fun k ↦ ⟨V k, a k, hsurj k, het k, (hsize k).trans (le_max_of_le_left (le_max_left _ _))⟩)
    (fun p ↦ ⟨VN p, aN p, hsurjN p, hetN p,
      (hsizeN p).trans (le_max_of_le_left (le_max_right _ _))⟩)

/-! ### Stacks 0ARA -/

/-- The presheaf represented by `Spec R`, for a Noetherian ring `R`, is a locally Noetherian
algebraic space: every scheme étale over `Spec R` is locally Noetherian. -/
theorem _root_.AlgebraicGeometry.Space.isLocallyNoetherian_yoneda_affineOver
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S) :
    Space.IsLocallyNoetherian B S hS (yoneda.obj (affineOver B S hS hR s)) := fun W q hq ↦
  (Space.exists_atlas_iff_forall_etale B S hS _
    (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)
    (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s))).mp
    (hasEtaleLocalProperty_isLocallyNoetherian_affineOver hS hR s) W q
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).1 hq)

/-- **Stacks 0ARA.** Let `S` be a scheme, let `X` be a locally Noetherian algebraic space over
`S` which is affine, so `X = Spec R` with `R` Noetherian, let `T ⊆ |X|` be closed and let
`U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. Then the completion functor of Stacks 0AR5,
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`, from the morphisms `f : X' ⟶ X`
of algebraic spaces which are locally of finite type and an isomorphism over `U` to the
morphisms `g : W ⟶ X_{/T}` of formal algebraic spaces with `W` locally Noetherian and `g`
rig-étale, is an equivalence.

Full faithfulness is Stacks 0GDR
(`AlgebraicGeometry.FormalSpace.completionModificationFunctorFullyFaithful`). Essential
surjectivity is `exists_finiteTypeModification_completion_iso_of_isRigEtale`, assembled as in the
source from Step 1 (Stacks 0AR4 and 0AR9), Step 2 (a separated `W`: Stacks 0AR8 and 04S6 applied
to the algebraizations of an affine étale covering) and Step 3 (a general `W`, whose
`Wᵢ ×_W Wⱼ` are separated). -/
@[stacks 0ARA]
theorem isEquivalence_completionModificationFunctor_affineOver
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T) :
    (completionModificationFunctor T hT (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s))
      (Space.isLocallyNoetherian_yoneda_affineOver hR s)).IsEquivalence := by
  have hff := completionModificationFunctorFullyFaithful T hT
    (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s))
    (Space.isLocallyNoetherian_yoneda_affineOver hR s)
  have := hff.full
  have := hff.faithful
  have : (completionModificationFunctor T hT
      (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s))
      (Space.isLocallyNoetherian_yoneda_affineOver hR s)).EssSurj := ⟨fun W ↦ by
    obtain ⟨M, ⟨e⟩⟩ := exists_finiteTypeModification_completion_iso_of_isRigEtale hR s T hT
      W.property.2.1 W.obj.hom W.property.2.2
    exact ⟨M, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩⟩
  exact { }

end AlgebraicGeometry.FormalSpace

end
