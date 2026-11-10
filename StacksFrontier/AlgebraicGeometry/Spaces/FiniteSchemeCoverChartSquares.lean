module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite

/-!
# Cartesian squares over charts, and finite étale loci read on a chart

Three pieces of bookkeeping for the proof of Stacks 0GUN.

* A chart `u₀ : h_{U₀} ⟶ U` of an open subspace `U ⊆ X` turns a square exhibiting `Z` as
  `F ×_X U₀` into one exhibiting `Z` as `(U ×_X F) ×_U U₀`
  (`AlgebraicGeometry.Space.isPullback_lift_pullback_fst`).
* The base change of a morphism `g : Y ⟶ Z` over `X` to an étale chart `V` of `X` is cartesian
  over `g` (`AlgebraicGeometry.Space.isPullback_fst_smallBaseChangeOverMap`).
* A closed subspace `C` of `P` whose base change to a chart `Z = P ×_X U₀` over `U` is the range
  of a closed immersion `W ⟶ Z` with `W ⟶ U₀` finite étale is finite étale over `U`
  (`AlgebraicGeometry.Space.isFinite_isEtale_pullback_fst_of_preimage_eq_range`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A square over a chart of an open subspace is a square over the open subspace.** -/
theorem isPullback_lift_pullback_fst {X F Z U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ X) (U : Subfunctor X) (u₀ : U₀ ⟶ U.toFunctor) (a : Z ⟶ F) (b : Z ⟶ U₀)
    (sq : IsPullback a b f (u₀ ≫ U.ι)) :
    IsPullback (pullback.lift (b ≫ u₀) a (by simpa only [Category.assoc] using sq.w.symm)) b
      (pullback.fst U.ι f) u₀ := by
  refine IsPullback.of_right (h₁₂ := pullback.snd U.ι f) (h₂₂ := U.ι) ?_ ?_
    (IsPullback.of_hasPullback U.ι f).flip
  · rw [pullback.lift_snd]; exact sq
  · rw [pullback.lift_fst]

/-- **The base change of a morphism over `X` to an étale chart is cartesian over it.** -/
theorem isPullback_fst_smallBaseChangeOverMap {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (g : Y ⟶ Z) (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    IsPullback (hY.fst V.obj.hom) (yoneda.map (smallBaseChangeOverMap B S hS g hY hZ V))
      g.left.hom (hZ.fst V.obj.hom) := by
  have hfac : g.left.hom ≫ Z.hom.hom = Y.hom.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y.left ⟶ X => m.hom) (Over.w g)
  refine IsPullback.of_bot ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ V).symm
    (hZ.isPullback V.obj.hom)
  rw [← Functor.map_comp, smallBaseChangeOverMap_snd, hfac]
  exact hY.isPullback V.obj.hom

/-- A morphism of the site is finite as a morphism of presheaves exactly when it is finite as a
morphism of schemes. -/
theorem isFinite_yoneda_map_iff {M N : BigFppfOver B S hS} (m : M ⟶ N) :
    IsFinite B S hS (yoneda.map m) ↔
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map m) :=
  ⟨fun h => (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsFinite.{u})
      inferInstance _).1
      (presheaf_isFinite_of_isFinite _ (Functor.relativelyRepresentable.map yoneda _) h),
    fun hm => isFinite_of_presheaf_isFinite (yoneda.map m)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.IsFinite.{u}) m).2 hm)⟩

/-- **The finite étale locus of a closed subspace, read on a chart.** -/
theorem isFinite_isEtale_pullback_fst_of_preimage_eq_range {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) {U₀ Z W : BigFppfOver B S hS}
    (u₀ : yoneda.obj U₀ ⟶ U.toFunctor) (hu₀s : IsSurjective B S hS u₀)
    (hu₀e : IsEtale B S hS u₀) (φ : yoneda.obj Z ⟶ P.1) (π : Z ⟶ U₀)
    (hsq : IsPullback φ (yoneda.map π) q (u₀ ≫ U.ι)) (C : ClosedSubspaces B S hS P.1)
    (m : W ⟶ Z) (hm : Mono (yoneda.map m))
    (hC : C.1.preimage φ = Subfunctor.range (yoneda.map m))
    (hfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map (m ≫ π)))
    (het : Etale ((BigFppfOver.toScheme B S hS).map (m ≫ π))) :
    IsFinite B S hS (pullback.fst U.ι (C.1.ι ≫ q)) ∧
      IsEtale B S hS (pullback.fst U.ι (C.1.ι ≫ q)) := by
  have big : IsPullback (C.1.fromPreimage φ) ((C.1.preimage φ).ι ≫ yoneda.map π) (C.1.ι ≫ q)
      (u₀ ≫ U.ι) := (Subfunctor.isPullback_preimage φ C.1).paste_vert hsq
  have sq := isPullback_lift_pullback_fst B S hS (C.1.ι ≫ q) U u₀ _ _ big
  -- The chart of `C` over `U₀` is `W`.
  have hinv : inv (Subfunctor.toRange (yoneda.map m)) ≫ yoneda.map m =
      (Subfunctor.range (yoneda.map m)).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
  let e : (C.1.preimage φ).toFunctor ≅ yoneda.obj W :=
    { hom := Subfunctor.homOfLe hC.le ≫ inv (Subfunctor.toRange (yoneda.map m))
      inv := Subfunctor.lift (yoneda.map m) hC.ge
      hom_inv_id := by
        rw [← cancel_mono (C.1.preimage φ).ι, Category.assoc, Category.assoc, Subfunctor.lift_ι,
          Category.id_comp]
        rw [hinv, Subfunctor.homOfLe_ι]
      inv_hom_id := by
        rw [← cancel_mono (yoneda.map m), Category.assoc, Category.assoc]
        rw [hinv, ← Category.assoc, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.lift_ι,
          Category.id_comp] }
  have he : (C.1.preimage φ).ι ≫ yoneda.map π = e.hom ≫ yoneda.map (m ≫ π) := by
    rw [Functor.map_comp, ← Category.assoc]
    congr 1
    change _ = (Subfunctor.homOfLe hC.le ≫ inv (Subfunctor.toRange (yoneda.map m))) ≫ yoneda.map m
    rw [Category.assoc, hinv, Subfunctor.homOfLe_ι]
  have hsnd : pullback.snd (pullback.fst U.ι (C.1.ι ≫ q)) u₀ =
      sq.isoPullback.inv ≫ e.hom ≫ yoneda.map (m ≫ π) := by
    rw [← he, sq.isoPullback_inv_snd]
  have hCalg : IsAlgebraicSpace B S hS (pullback U.ι (C.1.ι ≫ q)) :=
    isAlgebraicSpace_pullback B S hS _ _ hU.1 C.2.1 hX
  refine ⟨isFinite_of_surjectiveEtaleChart B S hS hCalg hU.1 _ hu₀s hu₀e ?_,
    isEtale_of_isEtale_pullback_snd B S hS hU.1 _ u₀
      ((presheafSurjective_iff_isSurjective_yoneda B S hS _ hU.1 _ u₀).2 hu₀s)
      (presheaf_etale_of_isEtale B S hS hu₀e) ?_⟩
  · have : IsIso e.hom := Iso.isIso_hom e
    rw [hsnd]
    exact isFinite_comp B S hS (isFinite_of_isIso B S hS _)
      (isFinite_comp B S hS (isFinite_of_isIso B S hS _)
        ((isFinite_yoneda_map_iff B S hS _).2 hfin))
  · have : IsIso e.hom := Iso.isIso_hom e
    rw [hsnd]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _)
      (isEtale_comp B S hS (isEtale_of_isIso B S hS _)
        (isEtale_of_presheaf_etale B S hS ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
          (@AlgebraicGeometry.Etale.{u}) (m ≫ π)).2 het)))

end AlgebraicGeometry.Space

end
