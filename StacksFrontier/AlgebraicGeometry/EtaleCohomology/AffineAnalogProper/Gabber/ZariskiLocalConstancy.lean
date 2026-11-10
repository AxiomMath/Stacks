module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# A finite locally constant sheaf is Zariski-locally constant when the local rings are strictly
henselian

Let `R` be a scheme all of whose local rings are strictly henselian, and `K` a finite locally
constant abelian sheaf on `R_étale` (Stacks Tag 093Q (3)). Then every point of `R` has an open
neighbourhood `O` on which `K` is constant: `K|_O` is the constant sheaf on a finite group. The
trivializing étale covering is refined by a Zariski covering, because an étale morphism has a
section over a Zariski neighbourhood of a strictly henselian point
(`AlgebraicGeometry.exists_opens_section_of_etale`).

The definition of local constancy restricts `K` to the localized sites `R_étale / V`; the first
result here identifies that restriction with the inverse image to the small étale site of the
scheme `V`, through the equivalence `R_étale / V ≌ V_étale`.

## Main results

* `Stacks.EtaleCohomology.nonempty_etaleAbelianInverseImage_iso_constant_of_overPullback`.
* `Stacks.EtaleCohomology.exists_opens_etaleAbelianInverseImage_iso_constant`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The equivalence `X_étale / P ≌ P_étale` between the localized site at an object `P` of the
small étale site and the small étale site of the underlying scheme of `P`. -/
def overSmallEtaleEquivalence {X : Scheme.{u}} (P : X.Etale) : Over P ≌ P.left.Etale where
  functor :=
    { obj V := MorphismProperty.Over.mk ⊤ V.hom.left inferInstance
      map g := MorphismProperty.Over.homMk g.left.left (by
        have := congrArg (fun morphism ↦ morphism.left) g.w
        exact this)
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj V := Over.mk (MorphismProperty.Over.homMk
        (A := MorphismProperty.Over.mk (P := (@Etale : MorphismProperty Scheme.{u}))
          ⊤ (V.hom ≫ P.hom) inferInstance)
        (B := P) V.hom)
      map {V W} g := Over.homMk (MorphismProperty.Over.homMk g.left (by
        change g.left ≫ (W.hom ≫ P.hom) = V.hom ≫ P.hom
        have h : g.left ≫ W.hom = V.hom := by simp
        rw [← Category.assoc, h])) (MorphismProperty.Comma.Hom.ext g.w (Subsingleton.elim _ _))
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (V.hom.left ≫ P.hom) = V.left.hom
      simp)) (by
        apply MorphismProperty.Comma.Hom.ext
        · change 𝟙 _ ≫ V.hom.left = V.hom.left
          simp
        · apply Subsingleton.elim)) (by
          intro V W g
          apply Over.OverMorphism.ext
          apply MorphismProperty.Comma.Hom.ext
          · change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
            simp
          · apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)) (by
      intro V W g
      apply MorphismProperty.Comma.Hom.ext
      · change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
        simp
      · apply Subsingleton.elim)

/-- The functor `X_étale / P ⥤ P_étale` of `overSmallEtaleEquivalence P` sends coverings of the
localized site to étale coverings. -/
theorem overSmallEtaleEquivalence_functor_coverPreserving {X : Scheme.{u}} (P : X.Etale) :
    CoverPreserving ((smallEtaleTopology X).over P) (smallEtaleTopology P.left)
      (overSmallEtaleEquivalence P).functor := by
  refine ⟨fun {V S} hS ↦ ?_⟩
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  rw [Sieve.functorPushforward_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr
    ((ofArrows_mem_smallEtaleTopology_iff (fun member ↦ (g member).left)).mp hS)

/-- The functor `P_étale ⥤ X_étale / P` of `overSmallEtaleEquivalence P` sends étale coverings
to coverings of the localized site. -/
theorem overSmallEtaleEquivalence_inverse_coverPreserving {X : Scheme.{u}} (P : X.Etale) :
    CoverPreserving (smallEtaleTopology P.left) ((smallEtaleTopology X).over P)
      (overSmallEtaleEquivalence P).inverse := by
  refine ⟨fun {V S} hS ↦ ?_⟩
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr ((ofArrows_mem_smallEtaleTopology_iff g).mp hS)

/-- The functor `P_étale ⥤ X_étale / P` of `overSmallEtaleEquivalence P` makes `P_étale` a
dense subsite of the localized site `X_étale / P`. -/
instance overSmallEtaleEquivalence_inverse_isDenseSubsite {X : Scheme.{u}} (P : X.Etale) :
    (overSmallEtaleEquivalence P).inverse.IsDenseSubsite
      (smallEtaleTopology P.left) ((smallEtaleTopology X).over P) := by
  have : (overSmallEtaleEquivalence P).functor.IsCocontinuous
      ((smallEtaleTopology X).over P) (smallEtaleTopology P.left) :=
    ((overSmallEtaleEquivalence P).toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (overSmallEtaleEquivalence_inverse_coverPreserving P)
  have : (overSmallEtaleEquivalence P).inverse.IsCocontinuous
      (smallEtaleTopology P.left) ((smallEtaleTopology X).over P) :=
    ((overSmallEtaleEquivalence P).symm.toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (overSmallEtaleEquivalence_functor_coverPreserving P)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- **Constancy on a localized site is constancy of the inverse image.** If the restriction of
`K` to the localized site `X_étale / U` is the constant sheaf `E`, then so is the inverse image
of `K` to the small étale site of the scheme `U`. -/
theorem nonempty_etaleAbelianInverseImage_iso_constant_of_overPullback {X : Scheme.{u}}
    (U : X.Etale) (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (E : AddCommGrpCat.{u + 1})
    (e : (constantSheaf ((smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}).obj E ≅
      ((smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U).obj K) :
    Nonempty ((etaleAbelianInverseImage.{u, 0} U.hom).obj K ≅
      (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) := by
  let eqv := overSmallEtaleEquivalence U
  let SE := eqv.sheafCongr ((smallEtaleTopology X).over U) (smallEtaleTopology U.left)
    AddCommGrpCat.{u + 1}
  have : eqv.symm.functor.IsContinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology X).over U) :=
    inferInstanceAs (eqv.inverse.IsContinuous _ _)
  have : eqv.symm.inverse.IsContinuous ((smallEtaleTopology X).over U)
      (smallEtaleTopology U.left) :=
    inferInstanceAs (eqv.functor.IsContinuous _ _)
  let hterminal := Over.mkIdTerminal (X := U)
  let ec : constantSheaf ((smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} ⋙ SE.functor ≅
      constantSheaf (smallEtaleTopology U.left) AddCommGrpCat.{u + 1} :=
    ((constantSheafAdj ((smallEtaleTopology X).over U) AddCommGrpCat.{u + 1} hterminal).comp
      (eqv.symm.toAdjunction.sheafPushforwardContinuous
        (smallEtaleTopology U.left) ((smallEtaleTopology X).over U))).leftAdjointUniq
      (constantSheafAdj (smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
        (hterminal.isTerminalObj eqv.functor (Over.mk (𝟙 U))))
  let eres : (etaleRestriction.{u, 0} U.hom).obj K ≅
      SE.functor.obj (((smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U).obj K) :=
    Iso.refl _
  exact ⟨(etaleAbelianInverseImageRestrictionIso.{u, 0} U.hom).app K ≪≫ eres ≪≫
    SE.functor.mapIso e.symm ≪≫ ec.app E⟩

/-- **A finite locally constant sheaf is Zariski-locally constant at strictly henselian
points.** If every local ring of `R` is strictly henselian and `K` is finite locally constant
on `R_étale`, then every point of `R` has an open neighbourhood `O` with `K|_O` constant on a
finite group. -/
theorem exists_opens_etaleAbelianInverseImage_iso_constant {R : Scheme.{u}}
    (hlocal : ∀ x : R, StrictlyHenselianLocalRing ↥(R.presheaf.stalk x))
    (K : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hK : ConstantSheaf.IsFiniteLocallyConstant R.smallEtaleTopology K) (y : R) :
    ∃ (O : R.Opens) (_ : y ∈ O) (E : AddCommGrpCat.{u + 1}), Finite E ∧
      Nonempty ((etaleAbelianInverseImage.{u, 0} O.ι).obj K ≅
        (constantSheaf O.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) := by
  obtain ⟨I, Xs, f, hcov, hconst⟩ := hK.exists_finite_cover (Scheme.Etale.mk (𝟙 R))
  have hy : y ∈ ⋃ i, Set.range (f i).left :=
    ((ofArrows_mem_smallEtaleTopology_iff f).mp hcov).symm ▸ Set.mem_univ y
  obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp hy
  have hw' : (Xs i).hom.base w = y := by
    have h := MorphismProperty.Over.w (f i)
    rw [← hw]
    change (Xs i).hom.base w = (f i).left.base w
    rw [← h]
    rfl
  obtain ⟨E, hfin, ⟨e⟩⟩ := hconst i
  obtain ⟨e'⟩ := nonempty_etaleAbelianInverseImage_iso_constant_of_overPullback (Xs i) K E e
  obtain ⟨V, hyV, g, hg⟩ := exists_opens_section_of_etale (Xs i).hom w (hw' ▸ hlocal y)
  refine ⟨V, hw' ▸ hyV, E, hfin, ⟨?_⟩⟩
  exact (etaleAbelianInverseImageCompIso'.{u, 0} g (Xs i).hom V.ι hg.symm).app K ≪≫
    (etaleAbelianInverseImage.{u, 0} g).mapIso e' ≪≫
    (etaleAbelianInverseImageConstantIso.{u, 0} g).app E

end Stacks.EtaleCohomology
