module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts

/-!
# Fullness and faithfulness of the base change to a limit bounded by the cutoff

This is the fullness and faithfulness of Stacks 07SK, for a cofiltered inverse system of
quasi-compact, absolutely quasi-separated algebraic spaces with affine transition morphisms
satisfying `AlgebraicGeometry.Space.IsCutoffBoundedSystem` in place of the bound of the index
category by the cofinality of the cutoff which the registered forms in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent` ask for. It uses the
affine charts of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts`
and proves the descent of monomorphisms and of lifts through a pair of morphisms which the
essential surjectivity uses.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_morphism_after_baseChange`: fullness.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.eventually_eq_of_baseChange_eq`: faithfulness.

Nothing here is registered: Stacks 07SK is registered on the forms bounded by the cofinality.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

namespace IsCutoffBoundedSystem

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Surjectivity and étaleness of a morphism of presheaves pass to its base changes. -/
private theorem surjective_etale_of_isPullback
    {T X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : T ⟶ X} {b : T ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b ∧
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b := by
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  exact ⟨P.presheaf.of_isPullback h hs, Q.presheaf.of_isPullback h he⟩

/-- A pullback square over `p ≫ g` factors through the pullback of `g` along `h`. -/
private theorem isPullback_lift_of_comp {C : Type*} [Category* C] [HasPullbacks C]
    {A Y Z X T : C} (p : A ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) {a : T ⟶ A} {b : T ⟶ X}
    (H : IsPullback a b (p ≫ g) h) :
    IsPullback a (pullback.lift (a ≫ p) b (by simpa using H.w)) p (pullback.fst g h) := by
  apply IsPullback.of_bot _ (by simp) (IsPullback.of_hasPullback g h)
  simpa using H

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hD hAffine hQc hQs

/-- **Stacks 07SK, fullness, for a system bounded by the cutoff.** A morphism between the base
changes to the limit of two algebraic spaces of finite presentation over a stage is the base
change of a morphism over a later stage. This is
`AlgebraicGeometry.Space.exists_morphism_after_baseChange` for a system satisfying
`AlgebraicGeometry.Space.IsCutoffBoundedSystem` in place of the bound of the index category by the
cofinality of the cutoff. -/
public theorem exists_morphism_after_baseChange
    (hConv : IsCutoffBoundedSystem B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶
      (Over.pullback (limit.π D i)).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj Yᵢ ⟶
        (Over.pullback (D.map e)).obj Zᵢ)
      (α : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Yᵢ) ≅
        (Over.pullback (limit.π D i)).obj Yᵢ)
      (β : (Over.pullback (limit.π D j)).obj
          ((Over.pullback (D.map e)).obj Zᵢ) ≅
        (Over.pullback (limit.π D i)).obj Zᵢ),
      (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
          pullback.fst Yᵢ.hom (D.map e)) ∧
      (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
        pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
          pullback.fst Zᵢ.hom (D.map e)) ∧
      α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  have hYqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B S hS hZ hY (hQs i) hYfp.2.2
  let f₀ := f.left ≫ pullback.fst Zᵢ.hom (limit.π D i)
  have hf₀ : f₀ ≫ Zᵢ.hom = pullback.fst Yᵢ.hom (limit.π D i) ≫ Yᵢ.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have hw : f.left ≫ pullback.snd Zᵢ.hom (limit.π D i) =
        pullback.snd Yᵢ.hom (limit.π D i) := f.w
    rw [← Category.assoc, hw]
  obtain ⟨j, U, p, g, hs, he, hg, hgf⟩ := exists_stage_atlas_factorization
    B S hS D hD hAffine hConv i Yᵢ hY hYqc hZ' Zᵢ.hom hZfp.1 f₀ hf₀
  let Yj := (Over.pullback (D.map j.hom)).obj Yᵢ
  have hYj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have hYjqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_pullback
    B S hS hZ Yᵢ.hom (D.map j.hom) hY (hD j.left) (hD i) hYqs (hQs j.left)
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U.obj
  have hUqc := isQuasiCompactSpace_yoneda_of_isAffine B S hS U.obj U.property
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p p hU hU hYj
  have hRqc := AlgebraicGeometry.Space.isQuasiCompactSpace_pullback
    B S hS hZ p p hU hYj hUqc hUqc hYjqs
  have hlim := equalizes_kernelPair_after_baseChange p Yj.hom (limit.π D j.left)
    ((iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ).hom.left ≫ f₀) g hgf
  obtain ⟨k, e, hkg⟩ := eventually_eq_on_quasiCompact_source B S hS D hD hAffine
    hConv j.left hR hZ' (hD i) hRqc
    (pullback.fst p p ≫ p ≫ Yj.hom) Zᵢ.hom (D.map j.hom) hZfp.1
    (pullback.fst p p ≫ g) (pullback.snd p p ≫ g)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc] using
      congrArg (fun t => pullback.fst p p ≫ t) hg)
    (by simpa only [Yj, Over.pullback_obj_hom, Category.assoc, pullback.condition_assoc] using
      congrArg (fun t => pullback.snd p p ≫ t) hg) hlim
  let K := affineStageChart B S hS D j.left U (p ≫ Yj.hom) hAffine (Over.mk e)
  let Yk := (Over.pullback (D.map e)).obj Yj
  let pK : yoneda.obj K.U.obj ⟶ Yk.left :=
    pullback.lift (yoneda.map K.toChart ≫ p) K.toStage
      (by simpa only [Category.assoc, Over.mk_hom] using K.isPullback.w.symm)
  have hpK : IsPullback (yoneda.map K.toChart) pK p (pullback.fst Yj.hom (D.map e)) :=
    isPullback_lift_of_comp p Yj.hom (D.map e) K.isPullback.flip
  have hYk := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (D.map e)
    hYj (hD k) (hD j.left)
  obtain ⟨hKs, hKe⟩ := surjective_etale_of_isPullback B S hS hpK hs he
  obtain ⟨gK, hgK⟩ := exists_hom_of_equalizes_atlas B S hS hYk hZ'.isSheaf pK hKs hKe
    (yoneda.map K.toChart ≫ g)
    (equalizes_kernelPair_of_baseChange_eq p Yj.hom (D.map e)
      (pullback.fst Yj.hom (D.map e)) (pullback.snd Yj.hom (D.map e)) pullback.condition
      (yoneda.map K.toChart) pK (by simp [pK]) g hkg)
  have hgKa : gK ≫ Zᵢ.hom = Yk.hom ≫ D.map e ≫ D.map j.hom := by
    apply hom_ext_of_surjective_etale_atlas B S hS hYk (hD i).isSheaf pK hKs hKe
    rw [← Category.assoc, hgK, Category.assoc, hg]
    have hw := congrArg (fun t => t ≫ D.map j.hom) K.isPullback.w
    simpa only [Yj, Yk, pK, Over.pullback_obj_hom, pullback.lift_snd_assoc,
      Over.mk_hom, Category.assoc] using hw.symm
  let d := e ≫ j.hom
  let η := iteratedBaseChangeIso (D.map j.hom) (D.map e) (D.map d)
    (D.map_comp e j.hom).symm Yᵢ
  let raw : pullback Yᵢ.hom (D.map d) ⟶ Zᵢ.left := η.inv.left ≫ gK
  have hrawa : raw ≫ Zᵢ.hom = pullback.snd Yᵢ.hom (D.map d) ≫ D.map d := by
    dsimp only [raw]
    rw [Category.assoc, hgKa]
    simpa only [d, Yk, Yj, Over.pullback_obj_hom, Functor.map_comp, Category.assoc] using
      congrArg (fun t => t ≫ D.map d) (Over.w η.inv)
  let g' : (Over.pullback (D.map d)).obj Yᵢ ⟶ (Over.pullback (D.map d)).obj Zᵢ :=
    Over.homMk (pullback.lift raw (pullback.snd Yᵢ.hom (D.map d)) hrawa) (by simp)
  let α := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Yᵢ
  let β := iteratedBaseChangeIso (D.map d) (limit.π D k) (limit.π D i) (limit.w D d) Zᵢ
  let m : pullback Yᵢ.hom (limit.π D i) ⟶ pullback Yᵢ.hom (D.map d) :=
    pullback.lift (pullback.fst Yᵢ.hom (limit.π D i))
      (pullback.snd Yᵢ.hom (limit.π D i) ≫ limit.π D k)
      (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hraw : m ≫ raw = f₀ := by
    let A := iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
      (limit.w D j.hom) Yᵢ
    let q : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ pullback Yj.hom (limit.π D j.left) :=
      pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
        (by simp only [Category.assoc, pullback.condition])
    have hq : IsPullback (pullback.fst (p ≫ Yj.hom) (limit.π D j.left)) q p
        (pullback.fst Yj.hom (limit.π D j.left)) :=
      isPullback_lift_of_comp p Yj.hom (limit.π D j.left) (IsPullback.of_hasPullback _ _)
    let l : pullback (p ≫ Yj.hom) (limit.π D j.left) ⟶ yoneda.obj K.U.obj :=
      K.isPullback.lift (pullback.snd _ _ ≫ limit.π D k) (pullback.fst _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition.symm)
    have hl : q ≫ A.hom.left ≫ m ≫ η.inv.left = l ≫ pK := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
        · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
            iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc, limit.w,
            pullback.condition]
      · simp [Yj, Yk, q, A, m, η, l, pK, iteratedBaseChangeIso_hom_left,
          iteratedBaseChangeIso_inv_left, Over.mk_hom, Category.assoc]
    have hEq : q ≫ A.hom.left ≫ (m ≫ raw) = q ≫ A.hom.left ≫ f₀ := by
      change q ≫ A.hom.left ≫ m ≫ η.inv.left ≫ gK = _
      have hh := congrArg (fun t => t ≫ gK) hl
      simp only [Category.assoc, hgK] at hh
      rw [hh]
      simpa [l, Category.assoc, q, A, Yj] using hgf
    obtain ⟨V, v, w, hV⟩ := isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hConv
      hAffine j.left U (p ≫ Yj.hom)
    let vq := hV.flip.isoPullback.hom ≫ q
    have hqs := surjective_etale_of_isPullback B S hS hq hs he
    have hEq' : A.hom.left ≫ (m ≫ raw) = A.hom.left ≫ f₀ := by
      apply hom_ext_of_surjective_etale_atlas B S hS
        (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yj.hom (limit.π D j.left)
          hYj (isAlgebraicSpace_limit_of_isCutoffBoundedSystem B S hS D hConv hD hAffine)
          (hD j.left))
        hZ'.isSheaf vq
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q hqs.1)
        (MorphismProperty.RespectsIso.precomp _ hV.flip.isoPullback.hom q hqs.2)
      simpa only [vq, Category.assoc] using
        congrArg (fun t => hV.flip.isoPullback.hom ≫ t) hEq
    let : IsIso A.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (limit D)).map A.hom))
    exact (cancel_epi A.hom.left).mp hEq'
  refine ⟨k, d, g', α, β, iteratedBaseChangeIso_hom_fst _ _ _ _ _,
    iteratedBaseChangeIso_hom_fst _ _ _ _ _, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hm : α.hom.left ≫ m =
        pullback.fst ((Over.pullback (D.map d)).obj Yᵢ).hom (limit.π D k) := by
      apply pullback.hom_ext <;>
        simp [α, m, iteratedBaseChangeIso_hom_left, Category.assoc, pullback.condition]
    have hh := congrArg (fun t => α.hom.left ≫ t) hraw
    rw [← Category.assoc α.hom.left m raw, hm] at hh
    simpa [g', f₀, Category.assoc, β, iteratedBaseChangeIso_hom_left,
      iteratedBaseChangeIso_inv_left, Over.pullback_map_left] using hh.symm
  · simpa only [Over.comp_left, Over.pullback_obj_hom] using
      (Over.w (α.hom ≫ f)).trans
        (Over.w ((Over.pullback (limit.π D k)).map g' ≫ β.hom)).symm


omit hQs in
/-- **Stacks 07SK, faithfulness, for a system bounded by the cutoff.** Two morphisms between
algebraic spaces of finite presentation over a stage whose base changes to the limit agree
already agree over a later stage. This is `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq`
for a system satisfying `AlgebraicGeometry.Space.IsCutoffBoundedSystem` in place of the bound of
the index category by the cofinality of the cutoff. -/
public theorem eventually_eq_of_baseChange_eq
    (hConv : IsCutoffBoundedSystem B S hS D)
    (i : I) (Yᵢ Zᵢ : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f g : Yᵢ ⟶ Zᵢ)
    (hfg : (Over.pullback (limit.π D i)).map f =
      (Over.pullback (limit.π D i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (Over.pullback (D.map e)).map f =
        (Over.pullback (D.map e)).map g := by
  classical
  have hYqc := AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation B S hS Yᵢ.hom
    (hD i) (hQc i) hYfp
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Yᵢ.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hf : (q₀ ≫ f.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  have hg : (q₀ ≫ g.left) ≫ Zᵢ.hom = q₀ ≫ Yᵢ.hom := by simp
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart B S hS D hD hAffine
    hConv i U (q₀ ≫ Yᵢ.hom) hZ' Zᵢ.hom hZfp.1
    (q₀ ≫ f.left) (q₀ ≫ g.left) hf hg
    (precomp_eq_of_baseChange_eq (limit.π D i) Yᵢ Zᵢ f g hfg q₀)
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ Yᵢ.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Yᵢ.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀ (pullback.fst Yᵢ.hom (D.map j.hom)) :=
    isPullback_lift_of_comp q₀ Yᵢ.hom (D.map j.hom) C.isPullback.flip
  have hpalgebraic := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS Yᵢ.hom (D.map j.hom)
    hY (hD j.left) (hD i)
  have heq : pullback.fst Yᵢ.hom (D.map j.hom) ≫ f.left =
      pullback.fst Yᵢ.hom (D.map j.hom) ≫ g.left := by
    obtain ⟨hps, hpe⟩ := surjective_etale_of_isPullback B S hS hp hsurj
      (represented_etale_of_isEtale B S hS q₀ het)
    apply hom_ext_of_surjective_etale_atlas B S hS hpalgebraic hZ'.isSheaf p hps hpe
    simpa [p, Category.assoc] using hj
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left] using heq
  · simp [Over.pullback_map_left]



private theorem exists_mono_after_baseChange
    (hConv : IsCutoffBoundedSystem B S hS D)
    (i : I) (Y Z : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Z.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Y.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Z.hom)
    (f : Y ⟶ Z) [Mono ((Over.pullback (limit.π D i)).map f)] :
    ∃ (j : I) (e : j ⟶ i), Mono ((Over.pullback (D.map e)).map f) := by
  let c := overPullbackCone f f
  have hc := overPullbackCone_isPullback f f
  have hf := isFinitePresentation_overHom B S hS hZ (hD i) (hQc i) (hQs i)
    Y Z hY hZ' hYfp hZfp f
  have hR : AlgebraicGeometry.IsAlgebraicSpace B S hS c.pt.left :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.left f.left hY hY hZ'
  have hRfst := isFinitePresentation_of_isPullback B S hS hR hY hY hZ'
    (IsPullback.of_hasPullback f.left f.left).flip hf
  have hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS c.pt.hom :=
    AlgebraicGeometry.Space.isFinitePresentation_comp B S hS hR hY (hD i)
      (pullback.fst f.left f.left) Y.hom hRfst hYfp
  have heq : (Over.pullback (limit.π D i)).map c.fst =
      (Over.pullback (limit.π D i)).map c.snd := by
    apply (cancel_mono ((Over.pullback (limit.π D i)).map f)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, c.condition]
  obtain ⟨j, e, hj⟩ := eventually_eq_of_baseChange_eq B S hS D hD hAffine hQc
    hConv i c.pt Y hR hY hRfp hYfp c.fst c.snd heq
  exact ⟨j, e, IsKernelPair.mono_of_eq_fst_snd (hc.map (Over.pullback (D.map e))) hj⟩

private theorem exists_lift_pair_after_baseChange
    (hConv : IsCutoffBoundedSystem B S hS D)
    (i : I) (A R W : Over (D.obj i))
    (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A.left)
    (hR : AlgebraicGeometry.IsAlgebraicSpace B S hS R.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W.left)
    (hAfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS A.hom)
    (hRfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS R.hom)
    (hWfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS W.hom)
    (s t : R ⟶ W) (a b : A ⟶ W)
    (u : (Over.pullback (limit.π D i)).obj A ⟶ (Over.pullback (limit.π D i)).obj R)
    (hu₁ : u ≫ (Over.pullback (limit.π D i)).map s = (Over.pullback (limit.π D i)).map a)
    (hu₂ : u ≫ (Over.pullback (limit.π D i)).map t = (Over.pullback (limit.π D i)).map b) :
    ∃ (j : I) (e : j ⟶ i)
      (v : (Over.pullback (D.map e)).obj A ⟶ (Over.pullback (D.map e)).obj R),
      v ≫ (Over.pullback (D.map e)).map s = (Over.pullback (D.map e)).map a ∧
      v ≫ (Over.pullback (D.map e)).map t = (Over.pullback (D.map e)).map b := by
  classical
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange
    B S hS hZ D hD hAffine hQc hQs hConv i A R hA hR hAfp hRfp u
  have hα' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) A α hα
  have hβ' := iteratedBaseChangeIso_unique (D.map e) (limit.π D j) (limit.π D i)
    (limit.w D e) R β hβ
  let γ := iteratedBaseChangeIso (D.map e) (limit.π D j) (limit.π D i) (limit.w D e) W
  have heq (v : R ⟶ W) (z : A ⟶ W)
      (hz : u ≫ (Over.pullback (limit.π D i)).map v = (Over.pullback (limit.π D i)).map z) :
      (Over.pullback (limit.π D j)).map (g ≫ (Over.pullback (D.map e)).map v) =
        (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) := by
    have hv : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map v) ≫
        γ.hom = β.hom ≫ (Over.pullback (limit.π D i)).map v := by
      rw [hβ']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) v
    have hz' : (Over.pullback (limit.π D j)).map ((Over.pullback (D.map e)).map z) ≫
        γ.hom = α.hom ≫ (Over.pullback (limit.π D i)).map z := by
      rw [hα']
      exact iteratedBaseChangeIso_naturality _ _ _ (limit.w D e) z
    refine (Iso.cancel_iso_hom_right _ _ γ).mp ?_
    rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, ← hg,
      Category.assoc, hz, hz']
  let Aj := (Over.pullback (D.map e)).obj A
  let Wj := (Over.pullback (D.map e)).obj W
  have hAj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS A.hom (D.map e) hA (hD j) (hD i)
  have hWj := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS W.hom (D.map e) hW (hD j) (hD i)
  have hAjfp := isFinitePresentation_of_isPullback B S hS hAj hA (hD j) (hD i)
    (IsPullback.of_hasPullback A.hom (D.map e)) hAfp
  have hWjfp := isFinitePresentation_of_isPullback B S hS hWj hW (hD j) (hD i)
    (IsPullback.of_hasPullback W.hom (D.map e)) hWfp
  obtain ⟨k₁, e₁, hk₁⟩ := eventually_eq_of_baseChange_eq B S hS D hD hAffine hQc
    hConv j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map s) ((Over.pullback (D.map e)).map a) (heq s a hu₁)
  obtain ⟨k₂, e₂, hk₂⟩ := eventually_eq_of_baseChange_eq B S hS D hD hAffine hQc
    hConv j Aj Wj hAj hWj hAjfp hWjfp
    (g ≫ (Over.pullback (D.map e)).map t) ((Over.pullback (D.map e)).map b) (heq t b hu₂)
  let k := IsCofiltered.min (Over.mk e₁) (Over.mk e₂)
  let c₁ := IsCofiltered.minToLeft (Over.mk e₁) (Over.mk e₂)
  let c₂ := IsCofiltered.minToRight (Over.mk e₁) (Over.mk e₂)
  have hk₁' := baseChange_eq_of_baseChange_eq (D.map e₁) (D.map c₁.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₁.w) _ _ hk₁
  have hk₂' := baseChange_eq_of_baseChange_eq (D.map e₂) (D.map c₂.left) (D.map k.hom)
    (by rw [← D.map_comp]; exact congrArg D.map c₂.w) _ _ hk₂
  let δ (Z : Over (D.obj i)) := iteratedBaseChangeIso (D.map e) (D.map k.hom)
    (D.map (k.hom ≫ e)) (D.map_comp _ _).symm Z
  let v := (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫ (δ R).hom
  have hfinal (x : R ⟶ W) (z : A ⟶ W)
      (hx : (Over.pullback (D.map k.hom)).map (g ≫ (Over.pullback (D.map e)).map x) =
        (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map z)) :
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
        (Over.pullback (D.map (k.hom ≫ e))).map z := by
    have hn := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm x
    have hz' := iteratedBaseChangeIso_naturality (D.map e) (D.map k.hom)
      (D.map (k.hom ≫ e)) (D.map_comp _ _).symm z
    calc
      v ≫ (Over.pullback (D.map (k.hom ≫ e))).map x =
          (δ A).inv ≫ (Over.pullback (D.map k.hom)).map g ≫
            (Over.pullback (D.map k.hom)).map ((Over.pullback (D.map e)).map x) ≫
            (δ W).hom := by
        simp only [v, Category.assoc]
        rw [← hn]
      _ = (δ A).inv ≫ (Over.pullback (D.map k.hom)).map
          ((Over.pullback (D.map e)).map z) ≫ (δ W).hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun z => (δ A).inv ≫ z ≫ (δ W).hom) hx
      _ = (Over.pullback (D.map (k.hom ≫ e))).map z := by
        rw [hz', Iso.inv_hom_id_assoc]
  exact ⟨k.left, k.hom ≫ e, v, hfinal s a hk₁', hfinal t b hk₂'⟩

end IsCutoffBoundedSystem

end AlgebraicGeometry.Space

end
