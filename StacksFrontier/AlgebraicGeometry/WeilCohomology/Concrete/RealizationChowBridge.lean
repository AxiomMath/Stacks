module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Chow classes of equidimensional schemes, graded by dimension and by codimension

Chapter 45 grades the Chow groups of a smooth projective scheme `X` over `k` by codimension,
`CH^c(X) = ∏_d CH_{d-c}(X_d)` (`Stacks.Chow.codimensionChowGroup`), while the correspondences of
Section 0FFZ are classes graded by dimension on the equidimensional pieces. For `X` of constant
dimension `n` a class `α ∈ CH_{n-c}(X)` is read in `CH^c(X)` by `chowGroupToCodimension`. This
file proves that this reading carries proper pushforward of cycles to the pushforward
`Stacks.WeilCohomology.equidimensionalPushforward` of axiom (C)(b).

## Main results

* `Stacks.WeilCohomology.properChowPushforward_dimPart_restrict`: for `X` of constant dimension
  `n`, pushing forward from the part `X_n` the restriction of a class is pushing the class forward.
* `Stacks.WeilCohomology.chowGroupToCodimension_properChowPushforward`:
  `φ_*` on classes graded by dimension is `equidimensionalPushforward` on classes graded by
  codimension, for `φ` between schemes of the same constant dimension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- For `M` of constant dimension `n` and `φ : M ⟶ N` proper over `k`, pushing forward along
`M_n ⟶ M ⟶ N` the restriction of a class to the part `M_n` is pushing the class forward along
`φ`: the part `M_n` is all of `M`. -/
theorem properChowPushforward_dimPart_restrict {M N : Scheme.{u}}
    (sM : M ⟶ (fieldChowSituation k).S) (sN : N ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sM] [LocallyOfFiniteType sN] [Smooth sM] {n : ℕ}
    (hM : RelativeDimension sM n) (φ : M ⟶ N) [IsProper φ] (hφ : φ ≫ sN = sM) (m : ℤ)
    (x : chowGroup (fieldChowSituation k) sM m) :
    haveI := (isClopenDecomposition_dimPart sM).isProper_ι n
    properChowPushforward (fieldChowSituation k) (partBase sM n) sN ((dimPart sM n).ι ≫ φ)
        (by rw [Category.assoc, hφ]) m (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sM (partBase sM n) (dimPart sM n).ι rfl m x) =
      properChowPushforward (fieldChowSituation k) sM sN φ hφ m
        (properPushforwardDescends _ _ _ _ _ _) x := by
  have := (isClopenDecomposition_dimPart sM).isProper_ι n
  have h := sum_properChowPushforward_chowGroupRestrict_of_isClopenDecomposition
    (fieldChowSituation k) sM (isClopenDecomposition_dimPart sM) {n}
    (fun d ⟨y, hy⟩ ↦ Finset.mem_singleton.2 (eq_of_mem_dimPart sM hM hy)) m x
  rw [Finset.sum_singleton] at h
  conv_rhs => rw [← h]
  rw [← AddMonoidHom.comp_apply (properChowPushforward _ _ sN φ hφ m _),
    properChowPushforward_comp]

/-- A morphism of smooth projective schemes over `k` is proper: the source is proper over `k` and
the target separated. -/
theorem SmoothProjectiveScheme.isProper_hom_left {M N : (SmoothProjectiveScheme k).FullSubcategory}
    (f : M ⟶ N) : IsProper f.hom.left := by
  have : IsProper (f.hom.left ≫ N.obj.hom) := by rw [Over.w f.hom]; infer_instance
  exact IsProper.of_comp f.hom.left N.obj.hom

/-- **Proper pushforward, read in codimension.** For a morphism `f : M ⟶ N` of smooth projective
schemes over `k` of constant dimensions `n` and `n'`, the reading in codimension `q = n' - m` of
`f_*x`, for `x` of dimension `m`, is `equidimensionalPushforward` of the reading of `x` in
codimension `p = n - m`. -/
theorem chowGroupToCodimension_properChowPushforward
    {M N : (SmoothProjectiveScheme k).FullSubcategory}
    {n n' : ℕ} (hM : RelativeDimension M.obj.hom n) (f : M ⟶ N) (m p q : ℤ) (hp : p = n - m)
    (hq : q = n' - m) (x : chowGroup (fieldChowSituation k) M.obj.hom m) :
    haveI := SmoothProjectiveScheme.isProper_hom_left f
    chowGroupToCodimension N.obj.hom m q
        (properChowPushforward (fieldChowSituation k) M.obj.hom N.obj.hom f.hom.left (Over.w f.hom)
          m (properPushforwardDescends _ _ _ _ _ _) x) =
      equidimensionalPushforward f n n' p q (by omega)
        (chowGroupToCodimension M.obj.hom m p x) := by
  have := SmoothProjectiveScheme.isProper_hom_left f
  obtain rfl : m = n - p := by omega
  funext e
  by_cases he : e = n'
  · subst he
    rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ (by omega)]
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, dite_true,
      AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
      AddEquiv.coe_toAddMonoidHom]
    rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ rfl]
    exact congrArg (chowGroupDegreeEquiv _ _ _) (congrArg (chowGroupRestrict _ _ _ _ _ _)
      (properChowPushforward_dimPart_restrict M.obj.hom N.obj.hom hM f.hom.left (Over.w f.hom) _
        x).symm)
  · rw [chowGroupToCodimension_apply_of_ne _ _ _ _ _ (by omega)]
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, dif_neg he,
      AddMonoidHom.zero_apply]

/-- For `X` of constant dimension `d`, the Chow groups of a part `X_e` with `e ≠ d` are trivial. -/
private theorem chowGroup_partBase_eq_of_ne {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sX] [Smooth sX] {d e : ℕ} (hX : RelativeDimension sX d) (he : e ≠ d)
    {m : ℤ} (x y : chowGroup (fieldChowSituation k) (partBase sX e) m) : x = y := by
  have := isEmpty_dimPart_of_ne sX hX he
  have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX e) m
  exact Subsingleton.elim _ _

/-- **The intersection product, read in codimension**: for `W` smooth over `k` of constant
dimension `N`, the canonical intersection product of Stacks 0FC0 on classes graded by dimension,
`CH_a(W) × CH_b(W) ⟶ CH_{a+b-N}(W)`, is `codimensionIntersectionProduct` on their readings in
codimensions `N - a` and `N - b`. -/
theorem chowGroupToCodimension_selfIntersectionProduct {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW] {N : ℕ}
    (hN : RelativeDimension sW N) (a b i j : ℤ) (ha : a = N - i) (hb : b = N - j)
    (x : chowGroup (fieldChowSituation k) sW a) (y : chowGroup (fieldChowSituation k) sW b) :
    chowGroupToCodimension sW (a + b - N) (i + j)
        (selfIntersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) (fieldGysinSystem k)
          sW N (canonicalDiagonalClassFamily k sW N hN) a b x y) =
      codimensionIntersectionProduct k sW i j (chowGroupToCodimension sW a i x)
        (chowGroupToCodimension sW b j y) := by
  funext p
  by_cases hp : p = N
  · subst hp
    rw [codimensionIntersectionProduct_apply, chowGroupToCodimension_apply_of_eq _ _ _ _ _
      (by omega)]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      ((heq_of_eq (chowGroupRestrict_selfIntersectionProduct_canonical sW (partBase sW p)
        (dimPart sW p).ι rfl hN (relativeDimension_partBase sW p) a b x y)).trans
      ((selfIntersectionProduct_heq_of_heq (partBase sW p) _ _ ha hb
        (chowGroupToCodimension_apply_heq sW a i x p ha).symm
        (chowGroupToCodimension_apply_heq sW b j y p hb).symm).trans
      (chowGroupDegreeEquiv_heq _ _ _ _).symm)))
  · exact chowGroup_partBase_eq_of_ne sW hN hp _ _

/-- **The cycle of a closed subscheme, read in codimension**: for a closed subscheme `Z ⊂ X` of
pure dimension `e`, the class of the cycle `[Z]_m`, `m = e`, read in codimension `c` is the class
`[Z] ∈ CH^c(X)`. -/
theorem chowGroupToCodimension_mk_cycleAssociatedToClosedSubscheme {X Z : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (i : Z ⟶ X) [IsClosedImmersion i] {e : ℕ}
    (hZ : RelativeDimension (i ≫ sX) e) (m c : ℤ) (hm : m = e) :
    chowGroupToCodimension sX m c
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i m)) =
      closedSubschemeClass sX i c := by
  subst hm
  rw [← chowGroupToCodimension_properChowPushforward_fundamentalChowClass sX i hZ c,
    properChowPushforward_fundamentalChowClass_eq_mk]
  rfl

section Flat

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX)

/-- **Flat pullback, read in codimension, is the Gysin map** (Stacks 0FF4): for a flat morphism
`f : X ⟶ Y` of schemes smooth over `k`, of constant dimensions `d` and `e`, with `f` of relative
dimension `t = d - e`, the codimension-`c` reading of `f^*x`, for `x` of dimension `e - c`, is
`f^!` of the reading of `x`. The proof is that of
`Stacks.Chow.codimensionGysin_closedSubschemeClass_of_flat`, for an arbitrary class. -/
theorem codimensionGysin_chowGroupToCodimension_of_flat {d e t : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension sX d)
    (hY : AlgebraicGeometry.RelativeDimension sY e)
    (ht : AlgebraicGeometry.RelativeDimension f t) (htd : t + e = d) (c : ℤ)
    (x : chowGroup (fieldChowSituation k) sY ((e : ℤ) - c)) :
    codimensionGysin sX sY hf c (chowGroupToCodimension sY ((e : ℤ) - c) c x) =
      chowGroupToCodimension sX ((e : ℤ) - c + t) c
        (flatPullbackChow (fieldChowSituation k) sX sY f hf t ht ((e : ℤ) - c)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x) := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  swap
  · exact chowGroup_partBase_eq_of_ne sX hX hd _ _
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d' ((d' : ℤ) - c)).injective
    (funext fun e' ↦ ?_)
  obtain ⟨e'⟩ := e'
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  rcases eq_or_ne e' e with rfl | he
  swap
  · have hemp := isEmpty_dimPart_of_ne sY hY he
    have : IsEmpty (dimPartPiece sX sY f d' e').toScheme :=
      ⟨fun w ↦ hemp.false ⟨_, w.2⟩⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase sX sY f d' e') ((d' : ℤ) - c)
    exact Subsingleton.elim _ _
  have hres : AlgebraicGeometry.RelativeDimension (f ∣_ dimPart sY e') t :=
    AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_morphismRestrict f (dimPart sY e')).flip ht
  have hq : AlgebraicGeometry.RelativeDimension (dimPartPieceHom sX sY f d' e') t :=
    AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion _ _ hres
  have : Flat (dimPartPieceHom sX sY f d' e') := by
    dsimp only [dimPartPieceHom]; infer_instance
  have hra : AlgebraicGeometry.RelativeDimension
      ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) 0 :=
    relativeDimension_of_isOpenImmersion _
  have ha : ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ≫ sX =
      dimPartPieceBase sX sY f d' e' := by
    rw [Category.assoc]
  have hqa : dimPartPieceHom sX sY f d' e' ≫ (dimPart sY e').ι =
      ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ≫ f := by
    rw [dimPartPieceHom_ι, Category.assoc]
  -- `f^! = q^*` on the piece
  have h1 := dimPartPieceGysin_heq_flatPullbackChow sX sY hf d' e' c hq htd
    (chowGroupToCodimension sY ((e' : ℤ) - c) c x e')
  have h1' := flatPullbackChow_heq_of_heq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') (partBase sY e') (dimPartPieceHom sX sY f d' e')
    (dimPartPieceHom_comp_partBase sX sY hf d' e') t hq (rfl : (e' : ℤ) - c = (e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (chowGroupToCodimension_apply_heq sY ((e' : ℤ) - c) c x e' rfl)
  -- restriction to `Y_e` is flat pullback along its inclusion
  have h2 := flatPullbackChow_heq_of_heq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') (partBase sY e') (dimPartPieceHom sX sY f d' e')
    (dimPartPieceHom_comp_partBase sX sY hf d' e') t hq (add_zero ((e' : ℤ) - c)).symm
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (chowGroupRestrict_heq_flatPullbackChow sY (partBase sY e') (dimPart sY e').ι rfl
      ((e' : ℤ) - c) x)
  -- `q^* ∘ ι_e^* = (q ≫ ι_e)^*`
  have h3 := flatPullbackChow_comp (fieldChowSituation k) (dimPartPieceBase sX sY f d' e')
    (partBase sY e') sY (dimPartPieceHom sX sY f d' e') (dimPart sY e').ι
    (dimPartPieceHom_comp_partBase sX sY hf d' e') rfl t 0 hq
    (relativeDimension_of_isOpenImmersion (dimPart sY e').ι) ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x
  -- `q ≫ ι_e = (ι_{X_{d,e}} ≫ ι_{X_d}) ≫ f`
  have h4 := flatPullbackChow_heq_of_morphism_eq (C := fieldChowSituation k)
    (dimPartPieceBase sX sY f d' e') sY hqa
    (by rw [Category.assoc]; exact dimPartPieceHom_comp_partBase sX sY hf d' e')
    (by rw [Category.assoc, hf, ha]) (by omega : t + 0 = 0 + t)
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ _ hq
      (relativeDimension_of_isOpenImmersion (dimPart sY e').ι))
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ f hra ht) ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x
  -- `(a ≫ f)^* = a^* ∘ f^*`
  have h5 := flatPullbackChow_comp (fieldChowSituation k) (dimPartPieceBase sX sY f d' e')
    sX sY _ f ha hf 0 t hra ht ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x
  -- the right side, read as a flat pullback to the piece
  set y := flatPullbackChow (fieldChowSituation k) sX sY f hf t ht ((e' : ℤ) - c)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x
  have h6 := chowGroupRestrict_heq_of_heq (fieldChowSituation k) (partBase sX d')
    (dimPartPieceBase sX sY f d' e') (dimPartPiece sX sY f d' e').ι rfl
    (by omega : (d' : ℤ) - c = (e' : ℤ) - c + t) _ _
    (chowGroupToCodimension_apply_heq sX ((e' : ℤ) - c + t) c y d' (by omega))
  rw [chowGroupRestrict_comp] at h6
  have h7 := chowGroupRestrict_heq_flatPullbackChow sX (dimPartPieceBase sX sY f d' e')
    ((dimPartPiece sX sY f d' e').ι ≫ (dimPart sX d').ι) ha ((e' : ℤ) - c + t) y
  exact eq_of_heq (h1.trans (h1'.trans (h2.trans (h3.trans (h4.trans (h5.symm.trans
    (h7.symm.trans h6.symm)))))))

/-- `codimensionGysin_chowGroupToCodimension_of_flat` for a class of dimension `m = e - c`
written freely. -/
theorem codimensionGysin_chowGroupToCodimension_of_flat' {d e t : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension sX d)
    (hY : AlgebraicGeometry.RelativeDimension sY e)
    (ht : AlgebraicGeometry.RelativeDimension f t) (htd : t + e = d) (m c : ℤ) (hm : m = e - c)
    (x : chowGroup (fieldChowSituation k) sY m) :
    codimensionGysin sX sY hf c (chowGroupToCodimension sY m c x) =
      chowGroupToCodimension sX (m + t) c
        (flatPullbackChow (fieldChowSituation k) sX sY f hf t ht m
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x) := by
  subst hm
  exact codimensionGysin_chowGroupToCodimension_of_flat sX sY hf hX hY ht htd c x

end Flat

end Stacks.WeilCohomology

end
