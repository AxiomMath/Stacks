module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethTruncation

/-!
# The truncation engine for a family of Künneth maps given by its formula

`Stacks.Cohomology.BoxKunneth.isIso_of_isIso_stupidTrunc` runs the truncation argument of
[Stacks, Tag 0FMC] for a family of maps typed through the definitions
`Stacks.Cohomology.BoxKunneth.KunnethFamily`, `KunnethFamily.NaturalLeft` and
`KunnethFamily.NaturalRight`. This file runs the same argument with the family and its two
naturality conditions written out as hypotheses.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_of_isIso_stupidTrunc_of_inline`: a family of Künneth maps
  natural in both complexes, invertible at every pair `(σ^{≤N}F^•, σ^{≤N}G^•)`, is invertible at
  `(F^•, G^•)`, for `F^•` locally bounded with terms flat over `a^{-1}𝒪_S`.

## Implementation notes

The bodies of the definitions above contain the instance arguments of the total complex, which
Lean abstracts into auxiliary lemmas. Matching those against the instance arguments of a concrete
family such as `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMapUnbounded` costs the kernel more
than a minute for each declaration that does it. With the types written out, a concrete family and
its naturality lemmas fit the hypotheses here syntactically. The helpers of the argument are those
of `StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethTruncation`.

## References

* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.BoxKunneth

open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open HomologicalComplex ComplexShape

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y S : Scheme.{u}}

variable {a : X ⟶ S} {b : Y ⟶ S} [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b]
  [QuasiSeparated b]

/- The family of maps the truncation argument runs on, one map
`Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^• ⟶ Rf_*Tot(F^• ⊠ G^•)` for each pair of complexes, and its two
naturality conditions `hl` and `hr`. They are section variables with their types written out,
not definitions: a definition would abstract the instance arguments in its body (the existence
of the total complex, of the sheafification) into auxiliary lemmas, and matching those against
the instance arguments of a concrete family such as `relativeBoxKunnethMapUnbounded` costs the
kernel more than a minute per use. -/
variable
  (ψ : ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ),
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L))) ⟶
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
      (DerivedCategory.Q.obj
        (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b) (up ℤ))))

/- Naturality of the family in the first complex. -/
variable
  (hl : ∀ {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    (φ : K ⟶ K') (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ),
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules a).mapHomologicalComplex (up ℤ)).map φ)))).app
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ≫ ψ K' L =
      ψ K L ≫ (derivedPushforward.{u, u + 1, u + 1}
        (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
            (boxProductRelativeCurried a b) (up ℤ))))

/- Naturality of the family in the second complex. -/
variable
  (hr : ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (χ : L ⟶ L'),
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules b).mapHomologicalComplex (up ℤ)).map χ))) ≫ ψ K L' =
      ψ K L ≫ (derivedPushforward.{u, u + 1, u + 1}
        (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) χ
            (boxProductRelativeCurried a b) (up ℤ))))

/-- If `s ≫ f' = f ≫ t` and `H` maps `s`, `f'`, `t` to isomorphisms, then it maps `f` to one. -/
private theorem isIso_map_of_comp_eq {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {A B A' B' : C} {f : A ⟶ B} {s : A ⟶ A'} {f' : A' ⟶ B'} {t : B ⟶ B'}
    (hs : IsIso (H.map s)) (hf' : IsIso (H.map f')) (ht : IsIso (H.map t))
    (hcomm : s ≫ f' = f ≫ t) : IsIso (H.map f) := by
  have : IsIso (H.map f ≫ H.map t) := by
    rw [← H.map_comp, ← hcomm, H.map_comp]
    exact IsIso.comp_isIso' hs hf'
  exact IsIso.of_isIso_comp_right _ (H.map t)

include hr in
/-- **Truncating the second complex does not change cohomology in degrees `< N + n₁ - 1`.** -/
theorem isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_right_of_inline
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ : ℤ) [K.IsStrictlyGE n₁]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (N d : ℤ) (hd : d < N + n₁ - 1)
    (h : IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map
      (ψ K (L.stupidTrunc (embeddingUpIntLE N))))) :
    IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map (ψ K L)) := by
  let H := DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d
  let T := canonicalDerivedTensorProduct.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)
  let A := (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
    (DerivedCategory.Q.obj (leftComplex a K))
  let L'' := L.stupidTrunc (embeddingUpIntGE (N + 1))
  let πL := L.πStupidTrunc (embeddingUpIntLE N)
  let g := inverseImageBaseProjection (pullback.fst a b ≫ a)
  let _ := derivedPushforwardCommShift (inverseImageBaseProjection b)
  have _ := derivedPushforward_isTriangulated (inverseImageBaseProjection b)
  let _ := derivedPushforwardCommShift g
  have _ := derivedPushforward_isTriangulated g
  let _ : (T.tensor.obj A).CommShift ℤ := T.commShift_right A
  have _ : (T.tensor.obj A).IsTriangulated := T.exact_right A
  have hEL'' : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L''))) :=
    derivedCategoryB_derivedPushforward_obj_of_isStrictlyGE b _ (N + 1)
      (fun i => (L''.X i).module) (fun _ => inferInstance) (fun _ => Iso.refl _)
  have hGL'' : ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
      (DerivedCategory.Q.obj (rightComplex b L''))).IsGE (N + 1) :=
    isGE_derivedPushforward_obj_of_isGE _ _ (N + 1) (by
      rw [DerivedCategory.isGE_Q_obj_iff]; infer_instance)
  have hs : IsIso (H.map ((T.tensor.obj A).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
        (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex (up ℤ)).map
          πL))))) :=
    isIso_homologyMap_map_Q_map_g_of_isGE
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙ T.tensor.obj A)
      (mapStupidTruncShortComplex_shortExact (toInverseImageModules b) L N) (n₁ + (N + 1))
      (isGE_derivedTensor_derivedPushforward_obj a (leftComplex a K) n₁ hK hKflat
        (fun i => (K.X i).module) (fun _ => inferInstance) (fun _ => Iso.refl _) _ hEL''
        (N + 1)) d (by omega)
  have ht : IsIso (H.map ((derivedPushforward.{u, u + 1, u + 1} g).map
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) πL
        (boxProductRelativeCurried a b) (up ℤ))))) :=
    isIso_homologyMap_map_Q_map_of_isIso_f (derivedPushforward.{u, u + 1, u + 1} g)
      (isGE_derivedPushforward_obj_of_isGE g) _ (N + n₁) (fun k hk =>
        isIso_mapBifunctorMap_f a b _ _ k fun p q hpq => by
          by_cases hq : q ≤ N
          · exact Or.inl ⟨inferInstance,
              StacksDraft.StupidTruncation.isIso_πStupidTruncLE_f L N q hq⟩
          · exact Or.inr (Or.inl ⟨CochainComplex.isZero_of_isStrictlyGE _ n₁ p (by omega),
              CochainComplex.isZero_of_isStrictlyGE _ n₁ p (by omega)⟩)) d (by omega)
  exact isIso_map_of_comp_eq H hs h ht (hr K πL)

include hl in
/-- **Truncating the first complex does not change cohomology in degrees `< N + n₂ - 1`.** Here
the first complex is only locally bounded, which is where [Stacks, Tag 0FML] (5) enters. -/
theorem isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_left_of_inline
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₂ : ℤ) [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (N d : ℤ) (hd : d < N + n₂ - 1)
    (h : IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map
      (ψ (K.stupidTrunc (embeddingUpIntLE N)) L))) :
    IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map (ψ K L)) := by
  let H := DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d
  let T := canonicalDerivedTensorProduct.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)
  let E := (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
    (DerivedCategory.Q.obj (rightComplex b L))
  let K'' := K.stupidTrunc (embeddingUpIntGE (N + 1))
  let πK := K.πStupidTrunc (embeddingUpIntLE N)
  let g := inverseImageBaseProjection (pullback.fst a b ≫ a)
  let _ := derivedPushforwardCommShift (inverseImageBaseProjection a)
  have _ := derivedPushforward_isTriangulated (inverseImageBaseProjection a)
  let _ := derivedPushforwardCommShift g
  have _ := derivedPushforward_isTriangulated g
  let _ : (T.tensor.flip.obj E).CommShift ℤ := T.commShift_left E
  have _ : (T.tensor.flip.obj E).IsTriangulated := T.exact_left E
  have hK'' := isLocallyBounded_and_isFlat_leftComplex_stupidTrunc hK hKflat
    (embeddingUpIntGE (N + 1))
  have hEL : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) E :=
    derivedCategoryB_derivedPushforward_obj_of_isStrictlyGE b _ n₂ (fun i => (L.X i).module)
      (fun _ => inferInstance) (fun _ => Iso.refl _)
  have hGL : E.IsGE n₂ :=
    isGE_derivedPushforward_obj_of_isGE _ _ n₂ (by
      rw [DerivedCategory.isGE_Q_obj_iff]; infer_instance)
  have hs : IsIso (H.map ((T.tensor.flip.obj E).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
        (DerivedCategory.Q.map (((toInverseImageModules a).mapHomologicalComplex (up ℤ)).map
          πK))))) :=
    isIso_homologyMap_map_Q_map_g_of_isGE
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙ T.tensor.flip.obj E)
      (mapStupidTruncShortComplex_shortExact (toInverseImageModules a) K N) ((N + 1) + n₂)
      (isGE_derivedTensor_derivedPushforward_obj a (leftComplex a K'') (N + 1) hK''.1 hK''.2
        (fun i => (K''.X i).module) (fun _ => inferInstance) (fun _ => Iso.refl _) E hEL n₂)
      d (by omega)
  have ht : IsIso (H.map ((derivedPushforward.{u, u + 1, u + 1} g).map
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap πK (𝟙 L)
        (boxProductRelativeCurried a b) (up ℤ))))) :=
    isIso_homologyMap_map_Q_map_of_isIso_f (derivedPushforward.{u, u + 1, u + 1} g)
      (isGE_derivedPushforward_obj_of_isGE g) _ (N + n₂) (fun k hk =>
        isIso_mapBifunctorMap_f a b _ _ k fun p q hpq => by
          by_cases hp : p ≤ N
          · exact Or.inl ⟨StacksDraft.StupidTruncation.isIso_πStupidTruncLE_f K N p hp,
              inferInstance⟩
          · exact Or.inr (Or.inr ⟨CochainComplex.isZero_of_isStrictlyGE _ n₂ q (by omega),
              CochainComplex.isZero_of_isStrictlyGE _ n₂ q (by omega)⟩)) d (by omega)
  exact isIso_map_of_comp_eq H hs h ht (hl πK L)

include hl hr in
/-- **A natural family of Künneth maps is invertible at a locally bounded complex as soon as it
is invertible at its stupid truncations.** Let `ψ` be a family of maps
`Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^• ⟶ Rf_*Tot(F^• ⊠ G^•)`, natural in both complexes, for `a` and `b`
quasi-compact and quasi-separated. Let `F^•` be locally bounded with terms flat over
`a^{-1}𝒪_S`, and let both complexes be strictly bounded below. If `ψ` is invertible at
`(σ^{≤N}F^•, σ^{≤N}G^•)` for every `N`, then it is invertible at `(F^•, G^•)`.

This is the truncation step of the proof of [Stacks, Tag 0FLT], run in the relative setting.
Cohomology in a fixed degree `d` is unchanged by truncating both complexes at `N ≫ d`. On the
target the truncation map is invertible in every total degree `≤ N + n`. On the source the
kernel `σ^{≥N+1}` of each truncation contributes only in degrees `> N`; this is
`isGE_derivedTensor_derivedPushforward_obj`, which rests on [Stacks, Tag 0FML] (5) at the merely
locally bounded `F^•`. That is why no cover of `S` and no global bound on `F^•` is needed, and
why nothing beyond strict boundedness below is asked of `G^•`. -/
theorem isIso_of_isIso_stupidTrunc_of_inline
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (hB : ∀ N : ℤ, IsIso (ψ (K.stupidTrunc (embeddingUpIntLE N))
      (L.stupidTrunc (embeddingUpIntLE N)))) :
    IsIso (ψ K L) := by
  rw [DerivedCategory.isIso_iff]
  intro d
  let N : ℤ := max (d - n₁ + 2) (d - n₂ + 2)
  have hK' := isLocallyBounded_and_isFlat_leftComplex_stupidTrunc hK hKflat (embeddingUpIntLE N)
  refine isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_left_of_inline ψ hl K L n₂ hK hKflat
    N d (by omega) ?_
  exact isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_right_of_inline ψ hr _ L n₁ hK'.1
    hK'.2 N d (by omega) (Functor.map_isIso _ _)

end Stacks.Cohomology.BoxKunneth

end
