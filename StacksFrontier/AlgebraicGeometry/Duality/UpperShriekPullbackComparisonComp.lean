module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonical
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapAlongComp
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The map `μ_{f,K}` and composition

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of `AlgebraicGeometry.FTS S`, the maps `μ` of
[Stacks, Tag 0B6T] for `f`, `g` and `g ∘ f` are compatible with the isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] (`Stacks.Duality.upperShriekCompIso`). The proof is
the source's: compute `(g ∘ f)^!` through a compactification `P` of `X` over `Z` proper over a
compactification `Ȳ` of `Y`, apply [Stacks, Tag 0B6R] to `P ⟶ Ȳ ⟶ Z`, restrict to the inverse
image `Q` of `Y` by [Stacks, Tag 0B6P], and remove the auxiliary compactifications with the
independence of `μ` of the compactification.

## Main results

* `Stacks.Duality.upperShriekCompareWithPullback_comp` — **[Stacks, Tag 0B6T]**, the
  compatibility of `μ` with composition, for arbitrary compactifications.
* `Stacks.Duality.CompCompactification.upperShriekCompareWithPullback_comp_upperShriekCompHom` —
  the same at the compactifications `P`, `Q` and `Ȳ`.
* `Stacks.Duality.CompCompactification.upperShriekCompHom_app_eq` — the comparison
  `(f ≫ g)^! ⟶ f^! ∘ g^!` at `P` and `Q` through the base change map along derived pullback.
* `Stacks.Duality.CompCompactification.quasiCoherentDerivedPullbackCompIso_restrict_coherence` —
  the coherence of the composition isomorphisms of derived pullback for `X ⊆ Q ⊆ P ⟶ Ȳ ⟶ Z`.

## References

* [Stacks Project, Tag 0B6T](https://stacks.math.columbia.edu/tag/0B6T)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0B6R](https://stacks.math.columbia.edu/tag/0B6R)
* [Stacks Project, Tag 0B6P](https://stacks.math.columbia.edu/tag/0B6P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

/-! ### Coherence of the composition isomorphisms of derived pullback for `X ⊆ Q ⊆ P ⟶ Ȳ ⟶ Z` -/

namespace Stacks.Duality

/-- The cocycle identity of [Stacks, Tag 0D5S] solved for the composite through `a ≫ b`. -/
theorem derivedPullbackCompIso_inv_comp_assoc {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (M : DerivedCategory W.Modules) :
    (derivedPullbackCompIso a b).inv.app ((derivedPullback c).obj M) ≫
        (derivedPullback a).map ((derivedPullbackCompIso b c).hom.app M) ≫
        (derivedPullbackCompIso a (b ≫ c)).hom.app M =
      (derivedPullbackCompIso (a ≫ b) c).hom.app M :=
  (Iso.inv_comp_eq ((derivedPullbackCompIso a b).app ((derivedPullback c).obj M))).2
    (derivedPullbackCompIso_assoc_app a b c M).symm

private lemma restrict_coherence_chase {D D' : Type*} [Category D] [Category D'] (F : D' ⥤ D)
    {S₀ S₁ T₀ T₁ U : D} {Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ Y₇ Y₈ : D'}
    (c : S₀ ⟶ T₀) (e₁ e₃ : T₀ ⟶ T₁) (ci : T₁ ⟶ U) (ch : U ⟶ T₁) (a : U ⟶ F.obj Y₆)
    (φ₁ : Y₆ ⟶ Y₇) (φ₂ : F.obj Y₇ ⟶ T₁) (xi : S₀ ⟶ S₁) (x : S₁ ⟶ S₀) (crsi' : S₁ ⟶ F.obj Y₁)
    (crsi : S₀ ⟶ F.obj Y₂) (z : Y₁ ⟶ Y₂) (csj : Y₁ ⟶ Y₃) (ew : Y₃ ⟶ Y₄) (cfpi : Y₄ ⟶ Y₅)
    (y : Y₅ ⟶ Y₆) (cfpg : Y₄ ⟶ Y₇) (csjg : Y₃ ⟶ Y₈) (e₂ : Y₈ ⟶ Y₇) (csjgb : Y₂ ⟶ Y₈)
    (crsjg : F.obj Y₈ ⟶ T₀) [Mono (F.map φ₁ ≫ φ₂)]
    (hL : a ≫ F.map φ₁ ≫ φ₂ = ch) (hci : ci ≫ ch = 𝟙 _) (hI : cfpi ≫ y ≫ φ₁ = cfpg)
    (hLw : csjg ≫ e₂ = ew ≫ cfpg) (hA : csj ≫ csjg = z ≫ csjgb)
    (hE : F.map e₂ ≫ φ₂ = crsjg ≫ e₃) (hN : x ≫ crsi = crsi' ≫ F.map z)
    (hL2 : crsi ≫ F.map csjgb ≫ crsjg = c) (hx : xi ≫ x = 𝟙 _) (he : e₃ = e₁) :
    c ≫ e₁ ≫ ci ≫ a = xi ≫ crsi' ≫ F.map (csj ≫ ew ≫ cfpi ≫ y) := by
  rw [← cancel_mono (F.map φ₁ ≫ φ₂)]
  simp only [Category.assoc]
  rw [hL, hci, Category.comp_id, ← F.map_comp_assoc]
  simp only [Category.assoc]
  rw [hI, ← hLw, reassoc_of% hA]
  simp only [F.map_comp, Category.assoc]
  rw [hE, ← reassoc_of% hN, reassoc_of% hx, reassoc_of% hL2, he]

/-- The coherence of the composition isomorphisms of derived pullback for `X ⊆ Q ⊆ P ⟶ Ȳ ⟶ Z`
over `X ⟶ Y ⊆ Ȳ`, with `Q = P ×_Ȳ Y`: the two identifications of `Lf^* Lg^*` with
`L(X ⟶ Q)^* L(Q ⟶ P)^* L(P ⟶ Z)^*` agree. -/
theorem derivedPullbackCompIso_restrict_coherence {X Q P Y Yb Z : Scheme.{u}} (r : X ⟶ Q)
    (fst : Q ⟶ P) (snd : Q ⟶ Y) (j : Y ⟶ Yb) (gb : Yb ⟶ Z) (p : P ⟶ Yb) (i : X ⟶ P)
    (f' : X ⟶ Y) (g' : Y ⟶ Z) (w : fst ≫ p = snd ≫ j) (hι : i = r ≫ fst) (hf : r ≫ snd = f')
    (hg : j ≫ gb = g') (hfg : i ≫ p ≫ gb = f' ≫ g') (M : DerivedCategory Z.Modules) :
    (derivedPullbackCompIso f' g').hom.app M ≫
        (eqToHom (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj M) hfg.symm) ≫
          (derivedPullbackCompIso i (p ≫ gb)).inv.app M) ≫
        (eqToHom (congrArg (fun h : X ⟶ P => (derivedPullback h).obj
            ((derivedPullback (p ≫ gb)).obj M)) hι) ≫
          (derivedPullbackCompIso r fst).inv.app ((derivedPullback (p ≫ gb)).obj M)) =
      (derivedPullback f').map (eqToHom (congrArg (fun h : Y ⟶ Z => (derivedPullback h).obj M)
          hg.symm) ≫ (derivedPullbackCompIso j gb).inv.app M) ≫
        (eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj
            ((derivedPullback j).obj ((derivedPullback gb).obj M))) hf.symm) ≫
          (derivedPullbackCompIso r snd).inv.app
            ((derivedPullback j).obj ((derivedPullback gb).obj M))) ≫
        (derivedPullback r).map
          (((derivedPullbackCompIso snd j).hom.app ((derivedPullback gb).obj M) ≫
            eqToHom (congrArg (fun h : Q ⟶ Yb => (derivedPullback h).obj
              ((derivedPullback gb).obj M)) w.symm) ≫
            (derivedPullbackCompIso fst p).inv.app ((derivedPullback gb).obj M)) ≫
          (derivedPullback fst).map ((derivedPullbackCompIso p gb).hom.app M)) := by
  subst hι hf hg
  have hL := derivedPullbackCompIso_inv_comp_assoc r fst (p ≫ gb) M
  have hI := derivedPullbackCompIso_inv_comp_assoc fst p gb M
  have hLw := derivedPullbackCompIso_hom_app_eqToHom_left gb w.symm M
  have hA := derivedPullbackCompIso_assoc_app snd j gb M
  have hE := map_eqToHom_derivedPullbackCompIso_hom_app r
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gb) w.symm).trans (Category.assoc _ _ _)))
    M
  have hN := (derivedPullbackCompIso r snd).inv.naturality ((derivedPullbackCompIso j gb).hom.app M)
  have hL2 := derivedPullbackCompIso_inv_comp_assoc r snd (j ≫ gb) M
  have hx : (derivedPullback (r ≫ snd)).map ((derivedPullbackCompIso j gb).inv.app M) ≫
      (derivedPullback (r ≫ snd)).map ((derivedPullbackCompIso j gb).hom.app M) = 𝟙 _ := by
    simp
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]
  exact restrict_coherence_chase (derivedPullback r)
    (φ₁ := (derivedPullbackCompIso fst (p ≫ gb)).hom.app M)
    (φ₂ := (derivedPullbackCompIso r (fst ≫ p ≫ gb)).hom.app M)
    (hL := hL) (hci := Iso.inv_hom_id_app _ _) (hI := hI) (hLw := hLw) (hA := hA) (hE := hE)
    (hN := hN) (hL2 := hL2) (hx := hx) (he := rfl)

/-- `Stacks.Duality.derivedPullbackCompIso_restrict_coherence` on the quasi-coherent derived
categories. -/
theorem quasiCoherentDerivedPullbackCompIso_restrict_coherence_aux {X Q P Y Yb Z : Scheme.{u}}
    (r : X ⟶ Q) (fst : Q ⟶ P) (snd : Q ⟶ Y) (j : Y ⟶ Yb) (gb : Yb ⟶ Z) (p : P ⟶ Yb) (i : X ⟶ P)
    (f' : X ⟶ Y) (g' : Y ⟶ Z) (w : fst ≫ p = snd ≫ j) (hι : i = r ≫ fst) (hf : r ≫ snd = f')
    (hg : j ≫ gb = g') (hfg : i ≫ p ≫ gb = f' ≫ g') (K : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPullbackCompIso f' g').hom.app K ≫
        (quasiCoherentDerivedPullbackCompIso i (p ≫ gb) ≪≫
          quasiCoherentDerivedPullbackCongr hfg).inv.app K ≫
        (quasiCoherentDerivedPullbackCongr hι ≪≫
          (quasiCoherentDerivedPullbackCompIso r fst).symm).hom.app
            ((quasiCoherentDerivedPullback' (p ≫ gb)).obj K) =
      (quasiCoherentDerivedPullback' f').map
          ((quasiCoherentDerivedPullbackCompIso j gb ≪≫
            quasiCoherentDerivedPullbackCongr hg).inv.app K) ≫
        (quasiCoherentDerivedPullbackCompIso r snd ≪≫ quasiCoherentDerivedPullbackCongr hf).inv.app
          ((quasiCoherentDerivedPullback' j).obj ((quasiCoherentDerivedPullback' gb).obj K)) ≫
        (quasiCoherentDerivedPullback' r).map
          ((Stacks.AffineProjectionFormula.squareCompositeIso
              (quasiCoherentDerivedPullbackCompIso snd j)
              (quasiCoherentDerivedPullbackCompIso fst p ≪≫
                quasiCoherentDerivedPullbackCongr w)).hom.app
            ((quasiCoherentDerivedPullback' gb).obj K) ≫
          (quasiCoherentDerivedPullback' fst).map
            ((quasiCoherentDerivedPullbackCompIso p gb).hom.app K)) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedPullback_map_hom,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Stacks.AffineProjectionFormula.squareCompositeIso_hom_app,
    quasiCoherentDerivedPullbackCongr_inv_app_hom, quasiCoherentDerivedPullbackCongr_hom_app_hom,
    quasiCoherentDerivedPullbackCompIso_inv_app_hom,
    quasiCoherentDerivedPullbackCompIso_hom_app_hom]
  exact derivedPullbackCompIso_restrict_coherence r fst snd j gb p i f' g' w hι hf hg hfg K.obj

end Stacks.Duality

namespace Stacks.Duality.CompCompactification

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y Z : FTS S}
  (f : X ⟶ Y) (g : Y ⟶ Z) (cg : CompactificationOf (Over.mk g.left))
  (cfg : CompactificationOf (Over.mk (f ≫ g).left))

/-- The base change map `a_{P/Ȳ} ⋙ L(Q ⟶ P)^* ⟶ L(Y ⟶ Ȳ)^* ⋙ a_{Q/Y}` of the right adjoints for
the cartesian square `Q ⊆ P` over `Y ⊆ Ȳ`, built with derived pullback. -/
abbrev restrictBaseChange :=
  haveI := isIso_rightAdjointSquare_of_isOpenImmersion (pullback.fst (proj f g cg cfg) cg.immersion)
    (pullback.snd (proj f g cg cfg) cg.immersion) (proj f g cg cfg) cg.immersion
    (IsPullback.of_hasPullback _ _)
  Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
    (quasiCoherentDerivedAdjunction (proj f g cg cfg) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction (pullback.snd (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction cg.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction (pullback.fst (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso (pullback.snd (proj f g cg cfg) cg.immersion)
      cg.immersion)
    (quasiCoherentDerivedPullbackCompIso (pullback.fst (proj f g cg cfg) cg.immersion)
        (proj f g cg cfg) ≪≫
      quasiCoherentDerivedPullbackCongr
        (IsPullback.of_hasPullback (proj f g cg cfg) cg.immersion).w)
    (twistedInverseImageAdjunction (proj f g cg cfg)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction (pullback.snd (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))

/-- `L(X ⟶ P)^* ≅ L(Q ⟶ P)^* ⋙ L(X ⟶ Q)^*`. -/
abbrev restrictPullbackIso :
    quasiCoherentDerivedPullback' (ι f g cg cfg) ≅
      quasiCoherentDerivedPullback' (pullback.fst (proj f g cg cfg) cg.immersion) ⋙
        quasiCoherentDerivedPullback' (restrictι f g cg cfg) :=
  quasiCoherentDerivedPullbackCongr (pullback.lift_fst _ _ _).symm ≪≫
    (quasiCoherentDerivedPullbackCompIso (restrictι f g cg cfg) (pullback.fst _ _)).symm

/-- `L(Y ⟶ Ȳ)^* ⋙ L(Q ⟶ Y)^* ≅ L(Q ⟶ Ȳ)^*` for `Q = P ×_Ȳ Y`. -/
abbrev restrictSquareLeft :=
  quasiCoherentDerivedPullbackCompIso (pullback.snd (proj f g cg cfg) cg.immersion) cg.immersion

/-- `L(P ⟶ Ȳ)^* ⋙ L(Q ⟶ P)^* ≅ L(Q ⟶ Ȳ)^*` for `Q = P ×_Ȳ Y`. -/
abbrev restrictSquareTop :=
  quasiCoherentDerivedPullbackCompIso (pullback.fst (proj f g cg cfg) cg.immersion)
      (proj f g cg cfg) ≪≫
    quasiCoherentDerivedPullbackCongr (IsPullback.of_hasPullback (proj f g cg cfg) cg.immersion).w

/-- **The composition isomorphisms of derived pullback for `X ⊆ Q ⊆ P ⟶ Ȳ ⟶ Z` are coherent**:
`Lf^* Lg^* ≅ L(g ∘ f)^*` read through `P` and `Q` agrees with `Lf^* Lg^*` read through `Ȳ`, `Q`
and the square `Q ⊆ P` over `Y ⊆ Ȳ`. -/
theorem quasiCoherentDerivedPullbackCompIso_restrict_coherence
    (K : quasiCoherentDerivedCategory Z.left) :
    (quasiCoherentDerivedPullbackCompIso f.left g.left).hom.app K ≫
        (quasiCoherentDerivedPullbackCompactificationIsoOfComp (f ≫ g)
          (compactification f g cg cfg)).inv.app K ≫
        (restrictPullbackIso f g cg cfg).hom.app
          ((quasiCoherentDerivedPullback' (compactification f g cg cfg).toBase).obj K) =
      (quasiCoherentDerivedPullback' f.left).map
          ((quasiCoherentDerivedPullbackCompactificationIsoOfComp g cg).inv.app K) ≫
        (quasiCoherentDerivedPullbackCompactificationIsoOfComp f
          (restrictCompactification f g cg cfg)).inv.app
          ((quasiCoherentDerivedPullback' cg.immersion).obj
            ((quasiCoherentDerivedPullback' cg.toBase).obj K)) ≫
        (pullRes f g cg cfg).map
          ((Stacks.AffineProjectionFormula.squareCompositeIso (restrictSquareLeft f g cg cfg)
              (restrictSquareTop f g cg cfg)).hom.app
            ((quasiCoherentDerivedPullback' cg.toBase).obj K) ≫
          (quasiCoherentDerivedPullback' (pullback.fst (proj f g cg cfg) cg.immersion)).map
            ((quasiCoherentDerivedPullbackCompIso (proj f g cg cfg) cg.toBase).hom.app K)) :=
  quasiCoherentDerivedPullbackCompIso_restrict_coherence_aux (restrictι f g cg cfg)
    (pullback.fst (proj f g cg cfg) cg.immersion) (pullback.snd (proj f g cg cfg) cg.immersion)
    cg.immersion cg.toBase (proj f g cg cfg) (ι f g cg cfg) f.left g.left
    (IsPullback.of_hasPullback (proj f g cg cfg) cg.immersion).w (pullback.lift_fst _ _ _).symm
    (pullback.lift_snd _ _ _) (immersion_comp_toBase g cg)
    (immersion_comp_toBase (f ≫ g) (compactification f g cg cfg)) K

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma compHom_app_aux {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B₁ B₂ : D} {E₀ E₁ E₂ E₃ : C} (x : A ⟶ B₁) (a : B₁ ⟶ B₂) (b : B₂ ⟶ F.obj E₀)
    (u : E₀ ⟶ E₁) (γ : E₁ ⟶ E₂) (w : E₂ ⟶ E₃) :
    (x ≫ ((a ≫ (b ≫ F.map u)) ≫ (𝟙 _ ≫ 𝟙 _))) ≫ F.map γ ≫ (𝟙 _ ≫ F.map w) ≫ 𝟙 _ =
      x ≫ (a ≫ b) ≫ F.map (u ≫ γ ≫ w) := by
  simp

/-- **The comparison `(f ≫ g)^! ⟶ f^! ∘ g^!` at `P` and `Q` through derived pullback**: it is
`L(X ⟶ P)^*` of `a_{P/Z} ≅ a_{P/Ȳ} ∘ a_{Ȳ/Z}`, the identification
`L(X ⟶ P)^* ≅ L(Q ⟶ P)^* ⋙ L(X ⟶ Q)^*`, and `L(X ⟶ Q)^*` of the base change map along derived
pullback for `Q ⊆ P` over `Y ⊆ Ȳ`. -/
theorem upperShriekCompHom_app_eq (K : quasiCoherentDerivedCategory Z.left) :
    (upperShriekCompHom f g cg cfg).app K =
      (quasiCoherentDerivedPullback' (ι f g cg cfg)).map
          ((twistedInverseImageCompIso (proj f g cg cfg) cg.toBase _ _ _).hom.app K) ≫
        (restrictPullbackIso f g cg cfg).hom.app ((aProj f g cg cfg).obj ((aBase g cg).obj K)) ≫
        (pullRes f g cg cfg).map
          ((restrictBaseChange f g cg cfg).app ((aBase g cg).obj K)) := by
  have hs : (srcIso f g cg cfg).hom.app K =
      (quasiCoherentDerivedPullback' (ι f g cg cfg)).map
          ((twistedInverseImageCompIso (proj f g cg cfg) cg.toBase _ _ _).hom.app K) ≫
        (((quasiCoherentDerivedPullbackCongr (pullback.lift_fst _ _ _).symm).hom.app
            ((aProj f g cg cfg).obj ((aBase g cg).obj K)) ≫
          ((quasiCoherentDerivedPullbackCompIso (restrictι f g cg cfg) (pullback.fst _ _)).inv.app
            ((aProj f g cg cfg).obj ((aBase g cg).obj K)) ≫
          (pullRes f g cg cfg).map ((restrictedDerivedRestrictAdjointIso
            (pullback.fst (proj f g cg cfg) cg.immersion)).inv.app
              ((aProj f g cg cfg).obj ((aBase g cg).obj K))))) ≫ (𝟙 _ ≫ 𝟙 _)) :=
    rfl
  have hm : (midIso f g cg cfg).hom.app K =
      (𝟙 _ ≫ (pullRes f g cg cfg).map ((aRes f g cg cfg).map
        ((restrictedDerivedRestrictAdjointIso cg.immersion).hom.app ((aBase g cg).obj K)))) ≫
        𝟙 _ :=
    rfl
  rw [restrictBaseChange, rightAdjointBaseChange_app_eq_twistedInverseImageRestrictionMap
    (pullback.fst (proj f g cg cfg) cg.immersion) (pullback.snd (proj f g cg cfg) cg.immersion)
    (proj f g cg cfg) cg.immersion (IsPullback.of_hasPullback _ _)]
  change (srcIso f g cg cfg).hom.app K ≫ (step₃ f g cg cfg).app K ≫
    (midIso f g cg cfg).hom.app K = _
  rw [hs, hm]
  exact compHom_app_aux _ _ _ _ _ _ _

/-! ### The compatibility of `μ` with composition at the compactifications `P`, `Q` and `Ȳ` -/

section Pentagon

variable [AlgebraicGeometry.IsNoetherian S]

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma inv_congr_of_eq {C : Type*} [Category C] {A B : C} {a b : A ⟶ B} (h : a = b)
    (ha : IsIso a) (hb : IsIso b) : @inv _ _ _ _ a ha = @inv _ _ _ _ b hb := by
  subst h
  rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma eq_inv_comp_of_eq_hom_comp {C : Type*} [Category C] {A B T : C} (e : A ≅ B)
    {μ : A ⟶ T} {c : B ⟶ T} (h : μ = e.hom ≫ c) : c = e.inv ≫ μ := by
  rw [h, Iso.inv_hom_id_assoc]

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma pentagon_chase {D W : Type*} [Category D] [Category W] [MonoidalCategory W]
    (U : D ⥤ W) {N N' G : D} {P₀ P₁ Q₀ Q₁ A₀ A₁ B₀ B₁ B₂ C₀ C₁ E₀ V₀ : W}
    (μN : P₀ ⟶ U.obj N) (μg : N ⟶ G) (iY : N ⟶ N') (cg' : N' ⟶ G) (e₂ : μg = iY ≫ cg')
    (Tk : P₀ ⟶ P₁) (μN' : P₁ ⟶ U.obj N') (nat : Tk ≫ μN' = μN ≫ U.map iY)
    (iX₁ : P₁ ⟶ Q₁) (cmpf' : Q₁ ⟶ U.obj N') (e₁ : μN' = iX₁ ≫ cmpf')
    (iX₀ : P₀ ⟶ Q₀) (kB : Q₀ ⟶ Q₁) (tn : Tk ≫ iX₁ = iX₀ ≫ kB)
    (d : Q₁ ⟶ (A₀ ⊗ A₁) ⊗ B₀) (cO : A₁ ⊗ B₀ ⟶ B₁) (iO : A₁ ⊗ B₀ ⟶ V₀) (μO : V₀ ⟶ B₁)
    (κ : A₀ ⟶ C₀) (iC iC' : B₁ ⟶ B₂) (cgf : C₀ ⊗ B₂ ⟶ E₀) (igf : C₀ ⊗ B₂ ⟶ C₁) (μgf : C₁ ⟶ E₀)
    (crh ch : E₀ ⟶ U.obj G)
    (key : cmpf' ≫ U.map cg' = d ≫ (α_ _ _ _).hom ≫ A₀ ◁ cO ≫ (κ ⊗ₘ iC) ≫ cgf ≫ crh)
    (hcO : cO = iO ≫ μO) (hiC : iC = iC') (hcgf : cgf = igf ≫ μgf) (hcrh : crh = ch) :
    μN ≫ U.map μg =
      iX₀ ≫ kB ≫ d ≫ (α_ _ _ _).hom ≫ A₀ ◁ (iO ≫ μO) ≫ (κ ⊗ₘ iC') ≫ igf ≫ μgf ≫ ch := by
  subst e₂ hcO hiC hcgf hcrh
  rw [U.map_comp, ← reassoc_of% nat, e₁, Category.assoc, reassoc_of% tn, key]
  simp only [Category.assoc]

/-- `𝒪_Z` is bounded below, so the map of [Stacks, Tag 0A9L] for `Q ⊆ P` over `Y ⊆ Ȳ` is
invertible at `ā_Ȳ(𝒪_Z)`. -/
instance isIso_restrictionMap_app_structureSheaf :
    IsIso ((restrictionMap f g cg cfg).app
      ((aBase g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) :=
  isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ _ _
    (isBoundedBelow_twistedInverseImage_obj cg.toBase _
      (Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _))

open Stacks.CategoryTheory.BaseChange in
/-- **The compatibility of `μ` with composition at the compactifications `P`, `Q` and `Ȳ`** (the
diagram of [Stacks, Tag 0B6T]): `μ_f` at `Lg^*K ⊗ g^!𝒪_Z` followed by `f^!μ_{g,K}` is the oplax
structure of `Lf^*`, the associator, `Lf^*Lg^*K ⊗ μ_f` at `g^!𝒪_Z`, the identifications
`Lf^*Lg^* ≅ L(g ∘ f)^*` and `f^!g^!𝒪_Z ≅ (g ∘ f)^!𝒪_Z`, `μ_{g ∘ f}` at `K` and
`(g ∘ f)^!K ⟶ f^!g^!K`. -/
theorem upperShriekCompareWithPullback_comp_upperShriekCompHom
    (K : quasiCoherentDerivedCategory Z.left) :
    upperShriekCompareWithPullbackCanonical f (restrictCompactification f g cg cfg)
        (((quasiCoherentDerivedTensor Y.left).obj
            ((quasiCoherentDerivedPullback' g.left).obj K)).obj
          ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ≫
        (upperShriek f (restrictCompactification f g cg cfg)).map
          (upperShriekCompareWithPullbackCanonical g cg K) =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).hom.app
          ((quasiCoherentDerivedPullback' f.left).obj
            (((quasiCoherentDerivedTensor Y.left).obj
              ((quasiCoherentDerivedPullback' g.left).obj K)).obj
              ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))))).app
          ((upperShriek f (restrictCompactification f g cg cfg)).obj
            (DerivedPushforward.derivedStructureSheaf Y.left)) ≫
        (quasiCoherentDerivedPullback' f.left).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y.left).hom.app
            ((quasiCoherentDerivedPullback' g.left).obj K)).app
            ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ▷ _ ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f.left)
          ((quasiCoherentDerivedPullback' g.left).obj K)
          ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left)) ▷ _ ≫
        (α_ _ _ _).hom ≫
        (quasiCoherentDerivedPullback' f.left).obj ((quasiCoherentDerivedPullback' g.left).obj K) ◁
          (((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app
            ((quasiCoherentDerivedPullback' f.left).obj
              ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left)))).app
            ((upperShriek f (restrictCompactification f g cg cfg)).obj
              (DerivedPushforward.derivedStructureSheaf Y.left)) ≫
          upperShriekCompareWithPullbackCanonical f (restrictCompactification f g cg cfg)
            ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ≫
        ((quasiCoherentDerivedPullbackCompIso f.left g.left).hom.app K ⊗ₘ
          inv ((upperShriekCompHom f g cg cfg).app
            (DerivedPushforward.derivedStructureSheaf Z.left))) ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app
            ((quasiCoherentDerivedPullback' (f ≫ g).left).obj K)).app
          ((upperShriek (f ≫ g) (compactification f g cg cfg)).obj
            (DerivedPushforward.derivedStructureSheaf Z.left)) ≫
        upperShriekCompareWithPullbackCanonical (f ≫ g) (compactification f g cg cfg) K ≫
        (upperShriekCompHom f g cg cfg).app K := by
  have : NatTrans.IsMonoidal (restrictSquareTop f g cg cfg).hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      ((quasiCoherentDerivedPullbackCompIso (pullback.fst (proj f g cg cfg) cg.immersion)
        (proj f g cg cfg)).hom ≫ (quasiCoherentDerivedPullbackCongr
          (IsPullback.of_hasPullback (proj f g cg cfg) cg.immersion).w).hom))
  have : NatTrans.IsMonoidal (restrictPullbackIso f g cg cfg).hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      ((quasiCoherentDerivedPullbackCongr (pullback.lift_fst _ _ _).symm).hom ≫
        (quasiCoherentDerivedPullbackCompIso (restrictι f g cg cfg) (pullback.fst _ _)).inv))
  have : NatTrans.IsMonoidal (quasiCoherentDerivedPullbackCompactificationIsoOfComp f
      (restrictCompactification f g cg cfg)).hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      ((quasiCoherentDerivedPullbackCompIso (restrictCompactification f g cg cfg).immersion
        (restrictCompactification f g cg cfg).toBase).hom ≫
        (quasiCoherentDerivedPullbackCongr (immersion_comp_toBase f
          (restrictCompactification f g cg cfg))).hom))
  have := isIso_twoSquare_of_isOpenImmersion (pullback.fst (proj f g cg cfg) cg.immersion)
    (pullback.snd (proj f g cg cfg) cg.immersion) (proj f g cg cfg) cg.immersion
    (IsPullback.of_hasPullback _ _)
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion
    (pullback.fst (proj f g cg cfg) cg.immersion) (pullback.snd (proj f g cg cfg) cg.immersion)
    (proj f g cg cfg) cg.immersion (IsPullback.of_hasPullback _ _)
    (DerivedPushforward.derivedStructureSheaf cg.space)
    (Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _)
  have := isIso_rightAdjointBaseChange_app_of_isOpenImmersion
    (pullback.fst (proj f g cg cfg) cg.immersion) (pullback.snd (proj f g cg cfg) cg.immersion)
    (proj f g cg cfg) cg.immersion (IsPullback.of_hasPullback _ _)
    ((aBase g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))
    (isBoundedBelow_twistedInverseImage_obj cg.toBase _
      (Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _))
  have key := comparisonMapAlong_comp_pentagon
    (adjg := quasiCoherentDerivedAdjunction cg.toBase (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (bg := twistedInverseImageAdjunction cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (adjp := quasiCoherentDerivedAdjunction (proj f g cg cfg)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (bp := twistedInverseImageAdjunction (proj f g cg cfg)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (adjP := quasiCoherentDerivedAdjunction (proj f g cg cfg ≫ cg.toBase)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (bP := twistedInverseImageAdjunction (proj f g cg cfg ≫ cg.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (eP := quasiCoherentDerivedPullbackCompIso (proj f g cg cfg) cg.toBase)
    (iP := quasiCoherentDerivedPushforwardCompIso (proj f g cg cfg) cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (jP := (twistedInverseImageCompIso (proj f g cg cfg) cg.toBase _ _ _).symm)
    (heP := NatTrans.IsMonoidal.δ_comp_tensorHom
      (quasiCoherentDerivedPullbackCompIso (proj f g cg cfg) cg.toBase).hom)
    (hiP := map_quasiCoherentDerivedPushforwardCompIso_comp_counit (proj f g cg cfg) cg.toBase)
    (hjP := map_twistedInverseImageCompIso_inv_comp_counit (proj f g cg cfg) cg.toBase)
    (adjJY := quasiCoherentDerivedAdjunction cg.immersion
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (adjJQ := quasiCoherentDerivedAdjunction (pullback.fst (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (adjQ := quasiCoherentDerivedAdjunction (pullback.snd (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (bQ := twistedInverseImageAdjunction (pullback.snd (proj f g cg cfg) cg.immersion)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (eg := restrictSquareLeft f g cg cfg) (ef := restrictSquareTop f g cg cfg)
    (hsq := squareComposite_δ_compat _ _
      (NatTrans.IsMonoidal.δ_comp_tensorHom (restrictSquareLeft f g cg cfg).hom)
      (NatTrans.IsMonoidal.δ_comp_tensorHom (restrictSquareTop f g cg cfg).hom))
    (JX := pullRes f g cg cfg) (ν := restrictPullbackIso f g cg cfg)
    (hν := NatTrans.IsMonoidal.δ_comp_tensorHom (restrictPullbackIso f g cg cfg).hom)
    (κf := quasiCoherentDerivedPullbackCompactificationIsoOfComp f
      (restrictCompactification f g cg cfg))
    (hκf := NatTrans.IsMonoidal.δ_comp_tensorHom
      (quasiCoherentDerivedPullbackCompactificationIsoOfComp f
        (restrictCompactification f g cg cfg)).hom)
    (κg := quasiCoherentDerivedPullbackCompactificationIsoOfComp g cg)
    (κgf := quasiCoherentDerivedPullbackCompactificationIsoOfComp (f ≫ g)
      (compactification f g cg cfg))
    (κ := quasiCoherentDerivedPullbackCompIso f.left g.left)
    (hκ := quasiCoherentDerivedPullbackCompIso_restrict_coherence f g cg cfg)
    (hA := tensorUnit_quasiCoherentDerivedCategory Z.left)
    (hB := tensorUnit_quasiCoherentDerivedCategory cg.space)
    (hD := tensorUnit_quasiCoherentDerivedCategory Y.left) K
  have hO := upperShriekCompHom_app_eq f g cg cfg (DerivedPushforward.derivedStructureSheaf Z.left)
  have hK := upperShriekCompHom_app_eq f g cg cfg K
  exact pentagon_chase (upperShriek f (restrictCompactification f g cg cfg))
    (upperShriekCompareWithPullbackCanonical f (restrictCompactification f g cg cfg) _)
    (upperShriekCompareWithPullbackCanonical g cg K) _ _
    (upperShriekCompareWithPullback_eq_comparisonMapAlong g cg K) _ _
    (upperShriekCompareWithPullbackCanonical_naturality f (restrictCompactification f g cg cfg) _)
    _ _
    (upperShriekCompareWithPullback_eq_comparisonMapAlong f (restrictCompactification f g cg cfg) _)
    _ _ (tensorIso_hom_naturality_left _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ key
    (eq_inv_comp_of_eq_hom_comp _ (upperShriekCompareWithPullback_eq_comparisonMapAlong f
      (restrictCompactification f g cg cfg) _))
    (inv_congr_of_eq hO.symm _ (isIso_upperShriekCompHom_app f g cg cfg _))
    (eq_inv_comp_of_eq_hom_comp _ (upperShriekCompareWithPullback_eq_comparisonMapAlong (f ≫ g)
      (compactification f g cg cfg) K))
    hK.symm

end Pentagon

end Stacks.Duality.CompCompactification

/-! ### The compatibility of `μ` with composition for arbitrary compactifications -/

namespace Stacks.Duality

private lemma final_chase {W : Type*} [Category W] [MonoidalCategory W]
    {SQ Sc W1Q W1c GQ Gc L L' A A' B BQ Bc VQ Vc HQ Hc R R' VP V' E E' : W}
    (tφ : SQ ⟶ Sc) [Epi tφ] (μQT : SQ ⟶ W1Q) (fμQ : W1Q ⟶ GQ) (φG : GQ ⟶ Gc) (μcT : Sc ⟶ W1c)
    (fμc : W1c ⟶ Gc) (ιhQ : SQ ⟶ L ⊗ BQ) (ιhc : Sc ⟶ L ⊗ Bc) (u : L ⟶ L') (δ : L' ⟶ A ⊗ B)
    (ιiQ : B ⊗ BQ ⟶ VQ) (μQO : VQ ⟶ HQ) (κ : A ⟶ A') (invC : HQ ⟶ R) (ιiP : A' ⊗ R ⟶ VP)
    (μP : VP ⟶ E) (CK : E ⟶ GQ) (ιic : B ⊗ Bc ⟶ Vc) (μcO : Vc ⟶ Hc) (einvO : Hc ⟶ R')
    (ιi' : A' ⊗ R' ⟶ V') (μcfg : V' ⟶ E') (eK : E' ⟶ Gc) (φO : BQ ⟶ Bc) (tφB : VQ ⟶ Vc)
    (φH : HQ ⟶ Hc) (ψK : E' ⟶ E) (ψinvO : R ⟶ R') (tψ : VP ⟶ V')
    (T1 : μQT ≫ fμQ ≫ φG = tφ ≫ μcT ≫ fμc)
    (pent : μQT ≫ fμQ = ιhQ ≫ u ▷ BQ ≫ δ ▷ BQ ≫ (α_ _ _ _).hom ≫ A ◁ (ιiQ ≫ μQO) ≫
      (κ ⊗ₘ invC) ≫ ιiP ≫ μP ≫ CK)
    (nιh : tφ ≫ ιhc = ιhQ ≫ L ◁ φO) (nιi : B ◁ φO ≫ ιic = ιiQ ≫ tφB)
    (T2 : μQO ≫ φH = tφB ≫ μcO) (hE : eK = ψK ≫ CK ≫ φG)
    (heinv : φH ≫ einvO = invC ≫ ψinvO) (nιi' : A' ◁ ψinvO ≫ ιi' = ιiP ≫ tψ)
    (T3 : tψ ≫ μcfg ≫ ψK = μP) :
    μcT ≫ fμc = ιhc ≫ u ▷ Bc ≫ δ ▷ Bc ≫ (α_ _ _ _).hom ≫ A ◁ (ιic ≫ μcO) ≫
      (κ ⊗ₘ einvO) ≫ ιi' ≫ μcfg ≫ eK := by
  rw [← cancel_epi tφ, ← T1, reassoc_of% pent, reassoc_of% nιh, hE]
  congr 1
  rw [whisker_exchange_assoc, whisker_exchange_assoc,
    MonoidalCategory.associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    reassoc_of% nιi, ← T2]
  have h1 : A ◁ (ιiQ ≫ μQO ≫ φH) ≫ (κ ⊗ₘ einvO) = A ◁ (ιiQ ≫ μQO) ≫ (κ ⊗ₘ invC) ≫ A' ◁ ψinvO := by
    rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
    simp only [Category.assoc, heinv]
  rw [reassoc_of% h1, reassoc_of% nιi', reassoc_of% T3]

private lemma map_inv_comp_of_comp_eq {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {O₁ O₂ : C} {A E : D} (ψi : O₂ ⟶ O₁) (ψ : O₁ ⟶ O₂) (μ : T.obj O₁ ⟶ A) (ψK : A ⟶ E)
    (μP : T.obj O₂ ⟶ E) (h : μ ≫ ψK = T.map ψ ≫ μP) (hi : ψi ≫ ψ = 𝟙 _) :
    T.map ψi ≫ μ ≫ ψK = μP := by
  rw [h, ← T.map_comp_assoc, hi, T.map_id, Category.id_comp]

private lemma inv_comp_eq_of_hom_comp {C : Type*} [Category C] {O₁ O₂ O₃ O₄ : C} (ψ : O₁ ⟶ O₂)
    (ψi : O₂ ⟶ O₁) (c : O₂ ⟶ O₃) (ci : O₃ ⟶ O₂) (φ : O₃ ⟶ O₄) (ei : O₄ ⟶ O₁)
    (hψ' : ψi ≫ ψ = 𝟙 _) (hc' : ci ≫ c = 𝟙 _) (he : (ψ ≫ c ≫ φ) ≫ ei = 𝟙 _) :
    φ ≫ ei = ci ≫ ψi := by
  have h : c ≫ φ ≫ ei = ψi := by
    simpa [reassoc_of% hψ'] using congrArg (ψi ≫ ·) he
  simpa [reassoc_of% hc'] using congrArg (ci ≫ ·) h

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  [AlgebraicGeometry.IsNoetherian S] {X Y Z : FTS S} (f : X ⟶ Y) (g : Y ⟶ Z)

open CompCompactification DominatingCompactification in
/-- **Stacks Project, Tag 0B6T (Lemma 48.16.5), compatibility with composition.** Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of `AlgebraicGeometry.FTS S` with `S` Noetherian, and
let `cf`, `cg`, `cfg` be compactifications of `f`, `g` and `g ∘ f`, computing `f^!`, `g^!` and
`(g ∘ f)^!`. For `K ∈ D⁺_QCoh(𝒪_Z)`, the map `μ_f` at `Lg^*K ⊗ g^!𝒪_Z` followed by `f^!μ_{g,K}`
equals: the identification
`Lf^*(Lg^*K ⊗ g^!𝒪_Z) ⊗ f^!𝒪_Y = Lf^*Lg^*K ⊗ (Lf^*g^!𝒪_Z ⊗ f^!𝒪_Y)` (the tensor structure of
`Lf^*` and the associator), `Lf^*Lg^*K ⊗ μ_f` at `g^!𝒪_Z`, the identifications
`Lf^*Lg^*K = L(g ∘ f)^*K` and `f^!g^!𝒪_Z = (g ∘ f)^!𝒪_Z` of [Stacks, Tag 0ATX]
(`Stacks.Duality.upperShriekCompIso`), `μ_{g ∘ f}` at `K`, and `(g ∘ f)^!K = f^!g^!K`. The
tensor products are `Stacks.Duality.quasiCoherentDerivedTensor`, read through
`Stacks.Duality.quasiCoherentDerivedTensorIsoCurriedTensor` where the monoidal structure of
`D_QCoh` is used. -/
@[stacks 0B6T "compatibility with composition"]
theorem upperShriekCompareWithPullback_comp (cf : CompactificationOf (Over.mk f.left))
    (cg : CompactificationOf (Over.mk g.left)) (cfg : CompactificationOf (Over.mk (f ≫ g).left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Z.left) :
    upperShriekCompareWithPullbackCanonical f cf
        (((quasiCoherentDerivedTensor Y.left).obj
          ((quasiCoherentDerivedPullback' g.left).obj K.obj)).obj
          ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ≫
        (upperShriek f cf).map (upperShriekCompareWithPullbackCanonical g cg K.obj) =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).hom.app
          ((quasiCoherentDerivedPullback' f.left).obj
            (((quasiCoherentDerivedTensor Y.left).obj
              ((quasiCoherentDerivedPullback' g.left).obj K.obj)).obj
              ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))))).app
          ((upperShriek f cf).obj (DerivedPushforward.derivedStructureSheaf Y.left)) ≫
        (quasiCoherentDerivedPullback' f.left).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor Y.left).hom.app
            ((quasiCoherentDerivedPullback' g.left).obj K.obj)).app
            ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ▷ _ ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f.left)
          ((quasiCoherentDerivedPullback' g.left).obj K.obj)
          ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left)) ▷ _ ≫
        (α_ _ _ _).hom ≫
        (quasiCoherentDerivedPullback' f.left).obj
            ((quasiCoherentDerivedPullback' g.left).obj K.obj) ◁
          (((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app
            ((quasiCoherentDerivedPullback' f.left).obj
              ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left)))).app
            ((upperShriek f cf).obj (DerivedPushforward.derivedStructureSheaf Y.left)) ≫
          upperShriekCompareWithPullbackCanonical f cf
            ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))) ≫
        ((quasiCoherentDerivedPullbackCompIso f.left g.left).hom.app K.obj ⊗ₘ
          ((upperShriekCompIso f g cf cg cfg).inv.app (derivedStructureSheafPlus Z.left)).hom) ≫
        ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app
            ((quasiCoherentDerivedPullback' (f ≫ g).left).obj K.obj)).app
          ((upperShriek (f ≫ g) cfg).obj (DerivedPushforward.derivedStructureSheaf Z.left)) ≫
        upperShriekCompareWithPullbackCanonical (f ≫ g) cfg K.obj ≫
        ((upperShriekCompIso f g cf cg cfg).hom.app K).hom := by
  set Q := restrictCompactification f g cg cfg
  set P := compactification f g cg cfg
  set dQ := upperShriekPlusIso f Q cf
  set dP := upperShriekPlusIso (f ≫ g) cfg P
  set e := ((quasiCoherentDerivedTensor X.left).obj ((quasiCoherentDerivedPullback' f.left).obj
      (((quasiCoherentDerivedTensor Y.left).obj
        ((quasiCoherentDerivedPullback' g.left).obj K.obj)).obj
        ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))))).mapIso
    ((ObjectProperty.ι _).mapIso (dQ.app (derivedStructureSheafPlus Y.left)))
  have hE : ∀ L : quasiCoherentDerivedCategoryPlusOfModel Z.left,
      ((upperShriekCompIso f g cf cg cfg).hom.app L).hom =
        (dP.hom.app L).hom ≫ (upperShriekCompHom f g cg cfg).app L.obj ≫
          (dQ.hom.app ((upperShriekPlus g cg).obj L)).hom := fun L => rfl
  have hψ' : (dP.inv.app (derivedStructureSheafPlus Z.left)).hom ≫
      (dP.hom.app (derivedStructureSheafPlus Z.left)).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  have T3 := map_inv_comp_of_comp_eq _ _ _ _ _ _
    (upperShriekCompareWithPullback_comp_upperShriekPlusIso (f ≫ g) cfg P K) hψ'
  have he : ((dP.hom.app (derivedStructureSheafPlus Z.left)).hom ≫
      (upperShriekCompHom f g cg cfg).app (DerivedPushforward.derivedStructureSheaf Z.left) ≫
        (dQ.hom.app ((upperShriekPlus g cg).obj (derivedStructureSheafPlus Z.left))).hom) ≫
      ((upperShriekCompIso f g cf cg cfg).inv.app (derivedStructureSheafPlus Z.left)).hom =
      𝟙 _ := by
    rw [← hE, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    rfl
  have : Epi (((quasiCoherentDerivedTensor X.left).obj ((quasiCoherentDerivedPullback' f.left).obj
      (((quasiCoherentDerivedTensor Y.left).obj
        ((quasiCoherentDerivedPullback' g.left).obj K.obj)).obj
        ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))))).map
      (dQ.hom.app (derivedStructureSheafPlus Y.left)).hom) := (inferInstance : Epi e.hom)
  refine final_chase (tφ := ((quasiCoherentDerivedTensor X.left).obj
      ((quasiCoherentDerivedPullback' f.left).obj
      (((quasiCoherentDerivedTensor Y.left).obj
        ((quasiCoherentDerivedPullback' g.left).obj K.obj)).obj
        ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left))))).map
      (dQ.hom.app (derivedStructureSheafPlus Y.left)).hom)
    (μQT := upperShriekCompareWithPullbackCanonical f Q _)
    (fμQ := (upperShriek f Q).map (upperShriekCompareWithPullbackCanonical g cg K.obj))
    (φG := (dQ.hom.app ((upperShriekPlus g cg).obj K)).hom)
    (CK := (upperShriekCompHom f g cg cfg).app K.obj)
    (φO := (dQ.hom.app (derivedStructureSheafPlus Y.left)).hom)
    (φH := (dQ.hom.app ((upperShriekPlus g cg).obj (derivedStructureSheafPlus Z.left))).hom)
    (ψK := (dP.hom.app K).hom) (ψinvO := (dP.inv.app (derivedStructureSheafPlus Z.left)).hom)
    (invC := inv ((upperShriekCompHom f g cg cfg).app
      (DerivedPushforward.derivedStructureSheaf Z.left)))
    (μQO := upperShriekCompareWithPullbackCanonical f Q
      ((upperShriek g cg).obj (DerivedPushforward.derivedStructureSheaf Z.left)))
    (μP := upperShriekCompareWithPullbackCanonical (f ≫ g) P K.obj)
    (T1 := upperShriekCompareWithPullback_comp_map_comp_upperShriekPlusIso f Q cf
      (M := (upperShriekPlus g cg).obj K) (upperShriekCompareWithPullbackCanonical g cg K.obj))
    (pent := upperShriekCompareWithPullback_comp_upperShriekCompHom f g cg cfg K.obj)
    (nιh := tensorIso_hom_naturality_right _ _ _ _)
    (nιi := ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app _).naturality _)
    (T2 := upperShriekCompareWithPullback_comp_upperShriekPlusIso f Q cf
      ((upperShriekPlus g cg).obj (derivedStructureSheafPlus Z.left)))
    (hE := hE K)
    (heinv := inv_comp_eq_of_hom_comp _ _ _ _ _ _ hψ' (IsIso.inv_hom_id _) he)
    (nιi' := ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).inv.app _).naturality _)
    (T3 := T3)

end Stacks.Duality

end
