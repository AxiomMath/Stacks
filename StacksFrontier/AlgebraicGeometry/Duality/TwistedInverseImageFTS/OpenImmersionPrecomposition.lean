module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionComposition

/-!
# Upper shriek of an open immersion followed by a morphism

For an open immersion `h` and a morphism `g` with a compactification `Ā` of `g`, the composition
isomorphism `(h ≫ g)^! ≅ h^! ∘ g^!` of [Stacks, Tag 0ATX], computed at the compactification of
`h ≫ g` restricted from `Ā` and the compactification of `h` by its target, is
`(h ≫ g)^! = L(h ≫ (X ⟶ Ā))^* ∘ a ≅ Lh^* ∘ g^!` after `h^! = Lh^*` ([Stacks, Tag 0AU0]). At the
compactifications of a choice of compactifications, this holds after the isomorphisms of
[Stacks, Tag 0AA0].

## Main definitions

* `Stacks.Duality.NestedCompactification.ofPrecompOpen`.

## Main results

* `Stacks.Duality.upperShriekCompIso_precompOpen_hom_app`.
* `Stacks.Duality.UpperShriek.factorIsoOf_hom_app_comp_shriekOfIsoPullbackOfIsOpenImmersion`.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

section PrecompOpen

variable {S₀ : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S₀] {A' A B : FTS S₀} (h : A' ⟶ A)
  [IsOpenImmersion h.left] (g : A ⟶ B) (j : CompactificationOf (Over.mk g.left))

/-- The nested compactification of `h ≫ g` for an open immersion `h`, over a compactification
`Ā` of `g`: `R = Ā` and `Q = A`. -/
def NestedCompactification.ofPrecompOpen : NestedCompactification h g j where
  R := j.space
  r := 𝟙 _
  isProper_r := inferInstanceAs (IsProper (𝟙 j.space))
  u := h.left ≫ j.immersion
  u_r := Category.comp_id _
  Q := A.left
  v := j.immersion
  rQ := 𝟙 _
  isPullback := IsPullback.id_vert j.immersion
  uQ := h.left
  uQ_v := rfl
  uQ_rQ := Category.comp_id _

omit [AlgebraicGeometry.IsNoetherian S₀] in
private lemma precompOpen_chase {C D E : Type*} [Category C] [Category D] [Category E]
    (Lu : C ⥤ D) (Li : C ⥤ E) (Lh : E ⥤ D) (P : Li ⋙ Lh ≅ Lu) {K₀ Z : C} {e : E}
    (T : K₀ ⟶ Z) (x : Z ⟶ K₀) (hT : T ≫ x = 𝟙 _) (b : Li.obj Z ⟶ e) (t : e ⟶ Li.obj K₀)
    (F2 : b ≫ t = Li.map x) (cg : Lu.obj Z ⟶ Lu.obj Z) (hc : cg = 𝟙 _) :
    (𝟙 _ ≫ (Lu.map T ≫ (cg ≫ P.inv.app Z) ≫ Lh.map b) ≫ 𝟙 _ ≫ 𝟙 _) ≫ Lh.map t =
      P.inv.app K₀ ≫ 𝟙 _ := by
  subst hc
  have n := P.inv.naturality x
  simp only [Functor.comp_map] at n
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Lh.map_comp, F2, ← n, ← Lu.map_comp_assoc, hT, Lu.map_id, Category.id_comp]

/-- **`(h ≫ g)^! ≅ h^! ∘ g^!` for an open immersion `h`**, at the compactification of `h ≫ g`
restricted from one of `g` and the compactification of `h` by its target, is
`(h ≫ g)^! ≅ Lh^* ∘ g^!` after `h^! = Lh^*` ([Stacks, Tag 0ATX], [Stacks, Tag 0AU0]). -/
theorem upperShriekCompIso_precompOpen_hom_app
    (K : quasiCoherentDerivedCategoryPlusOfModel B.left) :
    ((upperShriekCompIso h g (openCompactification h) j (j.precompOpen h.left)).hom.app K).hom ≫
        (upperShriekOpenIso h).hom.app ((upperShriek g j).obj K.obj) =
      (upperShriekPrecompOpenIso h g j).hom.app K.obj := by
  have H := congrArg (fun i => (i.hom.app K).hom)
    (NestedCompactification.upperShriekCompIso_eq_compIsoVia (openCompactification h) j
      (j.precompOpen h.left) (NestedCompactification.ofPrecompOpen h g j))
  refine (congrArg (· ≫ (upperShriekOpenIso h).hom.app ((upperShriek g j).obj K.obj)) H).trans ?_
  have F1 := NestedCompactification.compHom_app (NestedCompactification.ofPrecompOpen h g j) K.obj
  have F2 := openBaseChange_id_app_comp g j K
  have F3 : (twistedInverseImageCompIso (𝟙 j.space) j.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K.obj ≫
      (twistedInverseImageIdIsoOfComp j.space).hom.app
        ((twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K.obj) = 𝟙 _ := by
    rw [← twistedInverseImageCompIso_id_comp j.toBase K.obj, Iso.hom_inv_id_app_assoc]
    rfl
  have F5 : (quasiCoherentDerivedPullbackCongr (X := A'.left)
      (h₁ := h.left ≫ j.immersion) rfl).hom.app ((twistedInverseImage (𝟙 j.space)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((twistedInverseImage j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K.obj)) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    simp [quasiCoherentDerivedPullbackCongr]
  have U : (upperShriekPrecompOpenIso h g j).hom.app K.obj =
      (quasiCoherentDerivedPullbackCompIso h.left j.immersion).inv.app
        ((twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K.obj) ≫ 𝟙 _ := rfl
  rw [upperShriekOpenIso_hom_app, U]
  show (((DominatingCompactification.upperShriekPlusIso (h ≫ g) (j.precompOpen h.left)
      (NestedCompactification.ofPrecompOpen h g j).compFG).hom.app K).hom ≫
    (NestedCompactification.ofPrecompOpen h g j).compHom.app K.obj ≫
    ((DominatingCompactification.upperShriekPlusIso h
      (NestedCompactification.ofPrecompOpen h g j).compF
      (openCompactification h)).hom.app ((upperShriekPlus g j).obj K)).hom ≫
    ((Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso g j j)
      (upperShriekPlus h (openCompactification h))).hom.app K).hom) ≫ _ = _
  rw [F1, upperShriekPlusIso_refl g j]
  erw [upperShriekPlusIso_refl, upperShriekPlusIso_refl]
  simp only [Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.id_app]
  refine precompOpen_chase (quasiCoherentDerivedPullback' (h.left ≫ j.immersion))
    (quasiCoherentDerivedPullback' j.immersion) (quasiCoherentDerivedPullback' h.left)
    (quasiCoherentDerivedPullbackCompIso h.left j.immersion) _ _ F3 _ _ F2 _ ?_
  exact F5

end PrecompOpen

/-- The chase behind `factorIsoOf_hom_app_comp_shriekOfIsoPullbackOfIsOpenImmersion`. -/
theorem factorIso_precompOpen_chase {𝒟 : Type*} [Category 𝒟] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : 𝒟}
    (a : o₀ ⟶ o₁) (X : o₁ ⟶ o₅) (b : o₁ ⟶ o₂) (cc : o₂ ⟶ o₃) (d : o₃ ⟶ o₄) (ee : o₄ ⟶ o₅)
    (f : o₅ ⟶ o₆) (gg : o₆ ⟶ o₈) (f' : o₄ ⟶ o₃) (ee' : o₃ ⟶ o₆) (gg' : o₃ ⟶ o₇) (Lx : o₇ ⟶ o₈)
    (a' : o₀ ⟶ o₂) (U : o₂ ⟶ o₇)
    (hE : X = b ≫ cc ≫ d ≫ ee) (N1 : ee ≫ f = f' ≫ ee') (T1 : d ≫ f' = 𝟙 _)
    (N2 : ee' ≫ gg = gg' ≫ Lx) (T2 : a ≫ b = a') (P4 : cc ≫ gg' = U) :
    a ≫ X ≫ f ≫ gg = a' ≫ U ≫ Lx := by
  subst hE T2 P4
  simp only [Category.assoc]
  rw [reassoc_of% N1, reassoc_of% T1, N2]

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-- **`k^! ≅ h^! ∘ g^!` for an open immersion `h` and `h ≫ g = k`**, at the chosen
compactifications, followed by `h^! = Lh^*`: it is `k^! ≅ (h ≫ g)^!` at any compactification of
`k` and one of `g` restricted along `h`, then `(h ≫ g)^! ≅ Lh^* ∘ g^!` ([Stacks, Tag 0ATX],
[Stacks, Tag 0AU0], [Stacks, Tag 0AA0]). -/
theorem factorIsoOf_hom_app_comp_shriekOfIsoPullbackOfIsOpenImmersion {W V Y : Scheme.{u}}
    {h : W ⟶ V} {g : V ⟶ Y} {k : W ⟶ Y} (e : h ≫ g = k) (hh : IsShriekable h)
    (hg : IsShriekable g) (hk : IsShriekable k) [IsOpenImmersion h]
    (j : CompactificationOf (Over.mk g)) (jk : CompactificationOf (Over.mk k))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    haveI := hg.target_noetherian
    haveI : IsOpenImmersion (ftsHomOf h hk.separatedFiniteType hg.separatedFiniteType e).left :=
      inferInstanceAs (IsOpenImmersion h)
    ((DominatingCompactification.upperShriekPlusIso
        (ftsHomOf k hk.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id k))
        jk (c k hk)).hom.app K).hom ≫
      ((factorIsoOf c e hh hg hk).hom.app K).hom ≫
      (shriekOfIsoPullbackOfIsOpenImmersion c h hh).hom.app ((shriekOf c g hg).obj K) =
    ((upperShriekPlusCongr (show ftsHomOf k hk.separatedFiniteType (isSeparatedFiniteType_id Y)
          (Category.comp_id k) = ftsHomOf h hk.separatedFiniteType hg.separatedFiniteType e ≫
            ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g) by
          ext; exact e.symm) jk (j.precompOpen h)).hom.app K).hom ≫
      (upperShriekPrecompOpenIso (ftsHomOf h hk.separatedFiniteType hg.separatedFiniteType e)
        (ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g))
        j).hom.app K.obj ≫
      (quasiCoherentDerivedPullback' h).map ((DominatingCompactification.upperShriekPlusIso
        (ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g))
        j (c g hg)).hom.app K).hom := by
  subst e
  have := hg.target_noetherian
  let fh := ftsHomOf h hk.separatedFiniteType hg.separatedFiniteType rfl
  let fg := ftsHomOf g hg.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id g)
  have : IsOpenImmersion fh.left := inferInstanceAs (IsOpenImmersion h)
  have E1 := congrArg (fun i => (i.hom.app K).hom)
    (NestedCompactification.upperShriekCompIso_eq_conj (f := fh) (g := fg) (openCompactification fh)
      j (j.precompOpen h) (c h hh) (c g hg) (c (h ≫ g) hk))
  have N1 := congrArg (fun φ => φ.hom)
    ((DominatingCompactification.upperShriekPlusIso fh (c h hh)
      (openCompactification fh)).hom.naturality
      ((DominatingCompactification.upperShriekPlusIso fg j (c g hg)).hom.app K))
  have T1 := congrArg (fun i => (i.hom.app ((upperShriekPlus fg j).obj K)).hom)
    ((upperShriekPlusIso_trans fh (openCompactification fh) (c h hh)
      (openCompactification fh)).trans (upperShriekPlusIso_refl fh (openCompactification fh)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom] at T1
  have N2 := (upperShriekOpenIso fh).hom.naturality
    ((DominatingCompactification.upperShriekPlusIso fg j (c g hg)).hom.app K).hom
  have T2 := congrArg (fun i => (i.hom.app K).hom)
    (upperShriekPlusIso_trans (fh ≫ fg) jk (c (h ≫ g) hk) (j.precompOpen h))
  have P4 := upperShriekCompIso_precompOpen_hom_app fh fg j K
  exact factorIso_precompOpen_chase
    (a := ((DominatingCompactification.upperShriekPlusIso (fh ≫ fg) jk
      (c (h ≫ g) hk)).hom.app K).hom)
    (X := ((upperShriekCompIso fh fg (c h hh) (c g hg) (c (h ≫ g) hk)).hom.app K).hom)
    (b := ((DominatingCompactification.upperShriekPlusIso (fh ≫ fg) (c (h ≫ g) hk)
      (j.precompOpen h)).hom.app K).hom)
    (cc := ((upperShriekCompIso fh fg (openCompactification fh) j (j.precompOpen h)).hom.app K).hom)
    (d := ((DominatingCompactification.upperShriekPlusIso fh (openCompactification fh)
      (c h hh)).hom.app ((upperShriekPlus fg j).obj K)).hom)
    (ee := ((upperShriekPlus fh (c h hh)).map
      ((DominatingCompactification.upperShriekPlusIso fg j (c g hg)).hom.app K)).hom)
    (f := ((DominatingCompactification.upperShriekPlusIso fh (c h hh)
      (openCompactification fh)).hom.app ((upperShriekPlus fg (c g hg)).obj K)).hom)
    (gg := (upperShriekOpenIso fh).hom.app ((upperShriekPlus fg (c g hg)).obj K).obj)
    (f' := ((DominatingCompactification.upperShriekPlusIso fh (c h hh)
      (openCompactification fh)).hom.app ((upperShriekPlus fg j).obj K)).hom)
    (ee' := ((upperShriekPlus fh (openCompactification fh)).map
      ((DominatingCompactification.upperShriekPlusIso fg j (c g hg)).hom.app K)).hom)
    (gg' := (upperShriekOpenIso fh).hom.app ((upperShriekPlus fg j).obj K).obj)
    (Lx := (quasiCoherentDerivedPullback' h).map ((DominatingCompactification.upperShriekPlusIso
      fg j (c g hg)).hom.app K).hom)
    (a' := ((DominatingCompactification.upperShriekPlusIso (fh ≫ fg) jk (j.precompOpen h)).hom.app
      K).hom)
    (U := (upperShriekPrecompOpenIso fh fg j).hom.app K.obj)
    E1 N1 T1 N2 T2 P4

end UpperShriek

end Stacks.Duality

end
