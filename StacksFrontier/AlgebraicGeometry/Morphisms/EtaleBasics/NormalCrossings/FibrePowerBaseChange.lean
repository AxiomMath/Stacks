module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import
  StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCriterion
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono

/-!
# Fibre powers under base change and along a monomorphism

The `n`-fold fibre power of a morphism, and the complement of its fat diagonal, are compatible
with base change: if `ν'` is the base change of `ν` along `β`, then the `n`-fold fibre power of
`ν'` is the base change of the `n`-fold fibre power of `ν` along `β`, and the complement of the
fat diagonal of `ν'` is the preimage of the complement of the fat diagonal of `ν`. Separately,
the fibre power of a morphism does not change if the target is enlarged along a monomorphism:
`Y ×_S ⋯ ×_S Y = Y ×_T ⋯ ×_T Y` whenever `S ⟶ T` is a monomorphism.

## Main definitions

* `AlgebraicGeometry.fibrePowerPullbackBaseChangeMap` is the comparison morphism between the
  fibre squares of a morphism and of its base change.
* `AlgebraicGeometry.fibrePowerBaseChangeMap` is the comparison morphism from the `n`-fold fibre
  power of a base change to the `n`-fold fibre power.
* `AlgebraicGeometry.fibrePowerOneIso` identifies the one-fold fibre power of `f : Y ⟶ S` with
  `Y`.
* `AlgebraicGeometry.pullbackCompMonoIso` and `AlgebraicGeometry.fibrePowerMonoIso` identify the
  fibre square and the fibre powers of `ν : Y ⟶ S` over `S` with those of `ν ≫ m : Y ⟶ T` over
  `T`, for a monomorphism `m : S ⟶ T`.

## Main results

* `AlgebraicGeometry.isPullback_fibrePowerBaseChangeMap`: the `n`-fold fibre power of a base
  change is the base change of the `n`-fold fibre power.
* `AlgebraicGeometry.fibrePowerBaseChangeMap_comp_leg` and
  `AlgebraicGeometry.fibrePowerBaseChangeMap_comp_pair`: the comparison morphism is compatible
  with the coordinates of a fibre power and with the morphisms to the fibre square.
* `AlgebraicGeometry.fibrePowerDistinctLocus_eq_preimage`: the complement of the fat diagonal of
  a base change is the preimage of the complement of the fat diagonal.
* `AlgebraicGeometry.isPullback_resLE_preimage`: a cartesian square restricts to a cartesian
  square over an open of the base of its right column and the preimage of that open.
* `AlgebraicGeometry.fibrePowerMonoIso_hom_leg`, `AlgebraicGeometry.fibrePowerMonoIso_hom_proj`
  and `AlgebraicGeometry.fibrePowerDistinctLocus_mono`: the identification of the fibre powers
  over `S` and over `T` respects the coordinates, the structure morphism (after composing with
  `m`), and the complement of the fat diagonal.

## Implementation notes

Both comparison morphisms are built by recursion on the number of factors, and in both cases the
morphism and the cartesian square (respectively the compatibility with the structure morphism)
that is needed to construct the next stage have to be produced together; the recursions therefore
take values in a subtype, and the two projections are then exposed as a definition and a theorem.

The `n`-fold fibre power of `f : Y ⟶ S` for `n = 0` is `S` itself, so the identification of the
fibre powers of `ν` and of `ν ≫ m` cannot hold for `n = 0`: it would say `T ≅ S`. The
declarations of the second half of this file are therefore indexed so that they speak about
`n + 1` factors; this is a deviation from the statements this file was asked for, which asked for
`fibrePower (ν ≫ m) n ≅ fibrePower ν n` for every `n`.

The statements about the complement of the fat diagonal are proved through
`AlgebraicGeometry.fibrePowerDistinctLocus_eq_iInter`, i.e. as equalities of preimages of sets
rather than pointwise, which avoids unfolding the coercion of a morphism of schemes to a function
on points.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-- The comparison morphism of pullbacks, read off on the first projection. -/
@[reassoc]
public theorem pullback_map_comp_fst {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y)
    (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.fst g₁ g₂
      = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The comparison morphism of pullbacks, read off on the second projection. -/
@[reassoc]
public theorem pullback_map_comp_snd {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y)
    (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.snd g₁ g₂
      = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Generalities on cartesian squares of schemes -/

/-- Taking preimages of a set of points along a composite is taking preimages twice. -/
public theorem preimage_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Set Z) :
    (f ≫ g).base ⁻¹' s = f.base ⁻¹' (g.base ⁻¹' s) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

/-- In a cartesian square of schemes the range of the top morphism is the preimage of the range
of the bottom morphism; this is `AlgebraicGeometry.Scheme.Pullback.range_fst` for an arbitrary
cartesian square. -/
public theorem range_base_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    refine ⟨snd.base p, ?_⟩
    have : (fst ≫ f).base p = (snd ≫ g).base p := by rw [h.w]
    simpa [Scheme.Hom.comp_base] using this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

/-- A cartesian square restricts to a cartesian square over an open of the base of the right
column and its preimage. -/
public theorem isPullback_resLE_preimage {W W' T T' : Scheme.{u}} {p : W' ⟶ T'} {q : W' ⟶ W}
    {b : T' ⟶ T} {r : W ⟶ T} (h : IsPullback p q b r) (V : W.Opens) :
    IsPullback ((q ⁻¹ᵁ V).ι ≫ p) (q.resLE V (q ⁻¹ᵁ V) le_rfl) b (V.ι ≫ r) := by
  refine IsPullback.paste_horiz ?_ h
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict q V).flip

/-- A pullback of a cartesian square by a cartesian square: the comparison morphism between two
pullbacks whose legs are related by cartesian squares over a common morphism `b` of bases
exhibits the smaller pullback as a base change of the larger one. -/
public theorem isPullback_pullback_map_fst {A A' B B' S S' : Scheme.{u}} {p : A ⟶ S}
    {p' : A' ⟶ S'} {g : B ⟶ S} {g' : B' ⟶ S'} {φ : A' ⟶ A} {ψ : B' ⟶ B} {b : S' ⟶ S}
    (k : IsPullback p' φ b p) (h : IsPullback g' ψ b g) :
    IsPullback (pullback.fst p' g') (pullback.map p' g' p g φ ψ b k.w h.w) φ
      (pullback.fst p g) := by
  have s : IsPullback (pullback.fst p' g')
      (pullback.map p' g' p g φ ψ b k.w h.w ≫ pullback.snd p g) (φ ≫ p) g := by
    rw [pullback_map_comp_snd, ← k.w]
    exact (IsPullback.of_hasPullback p' g').paste_vert h
  exact IsPullback.of_bot s (pullback_map_comp_fst _ _ _ _ _ _ _ _ _).symm
    (IsPullback.of_hasPullback p g)

/-! ### Fibre powers commute with base change -/

section BaseChange

variable {S S' Y Y' : Scheme.{u}} {ν : Y ⟶ S} {ν' : Y' ⟶ S'} {α : Y' ⟶ Y} {β : S' ⟶ S}

/-- The comparison morphism between the fibre square of `ν'` and the fibre square of `ν`, for a
cartesian square exhibiting `ν'` as a base change of `ν`. -/
public noncomputable def fibrePowerPullbackBaseChangeMap (h : IsPullback ν' α β ν) :
    pullback ν' ν' ⟶ pullback ν ν :=
  pullback.map ν' ν' ν ν α α β h.w h.w

/-- The comparison morphism of fibre powers, together with the cartesian square that is needed to
build the next stage of the recursion. -/
public noncomputable def fibrePowerBaseChangeAux (h : IsPullback ν' α β ν) :
    (n : ℕ) → {g : fibrePower ν' n ⟶ fibrePower ν n //
      IsPullback (fibrePowerProj ν' n) g β (fibrePowerProj ν n)}
  | 0 => ⟨β, by exact IsPullback.of_id_fst⟩
  | n + 1 =>
      ⟨pullback.map (fibrePowerProj ν' n) ν' (fibrePowerProj ν n) ν
          (fibrePowerBaseChangeAux h n).1 α β (fibrePowerBaseChangeAux h n).2.w h.w,
        (isPullback_pullback_map_fst (fibrePowerBaseChangeAux h n).2 h).paste_horiz
          (fibrePowerBaseChangeAux h n).2⟩

/-- The comparison morphism from the fibre power of a base change to the fibre power. -/
public noncomputable def fibrePowerBaseChangeMap (h : IsPullback ν' α β ν) (n : ℕ) :
    fibrePower ν' n ⟶ fibrePower ν n :=
  (fibrePowerBaseChangeAux h n).1

/-- The fibre power of a base change is the base change of the fibre power. -/
public theorem isPullback_fibrePowerBaseChangeMap (h : IsPullback ν' α β ν) (n : ℕ) :
    IsPullback (fibrePowerProj ν' n) (fibrePowerBaseChangeMap h n) β (fibrePowerProj ν n) :=
  (fibrePowerBaseChangeAux h n).2

/-- With no factors the comparison morphism is the morphism of bases. -/
public theorem fibrePowerBaseChangeMap_zero (h : IsPullback ν' α β ν) :
    fibrePowerBaseChangeMap h 0 = β := rfl

/-- One more factor in the comparison morphism is one more application of `pullback.map`. -/
public theorem fibrePowerBaseChangeMap_succ (h : IsPullback ν' α β ν) (n : ℕ) :
    fibrePowerBaseChangeMap h (n + 1) =
      pullback.map (fibrePowerProj ν' n) ν' (fibrePowerProj ν n) ν
        (fibrePowerBaseChangeMap h n) α β (isPullback_fibrePowerBaseChangeMap h n).w h.w := rfl

/-- If a morphism of fibre powers lies over a morphism of fibre squares compatible with the
diagonals, then the fat diagonal of the source is the preimage of the fat diagonal of the target. -/
private theorem fibrePowerDistinctLocus_eq_preimage_of_pair {Y Y' S S' : Scheme.{u}}
    {f : Y ⟶ S} {f' : Y' ⟶ S'} {n : ℕ} (g : fibrePower f' n ⟶ fibrePower f n)
    (k : pullback f' f' ⟶ pullback f f)
    (hg : ∀ i j : Fin n, g ≫ fibrePowerPair f n i j = fibrePowerPair f' n i j ≫ k)
    (hk : Set.range (pullback.diagonal f').base = k.base ⁻¹' Set.range (pullback.diagonal f).base) :
    fibrePowerDistinctLocus f' n = g.base ⁻¹' fibrePowerDistinctLocus f n := by
  rw [fibrePowerDistinctLocus_eq_iInter, fibrePowerDistinctLocus_eq_iInter, Set.preimage_iInter]
  refine Set.iInter_congr fun p => ?_
  rw [hk, ← Set.preimage_compl, ← preimage_base_comp, ← hg, preimage_base_comp]

/-- The comparison morphism of fibre powers is compatible with the coordinates. -/
public theorem fibrePowerBaseChangeMap_comp_leg (h : IsPullback ν' α β ν) :
    ∀ (n : ℕ) (k : Fin n),
      fibrePowerBaseChangeMap h n ≫ fibrePowerLeg ν n k = fibrePowerLeg ν' n k ≫ α
  | 0, k => k.elim0
  | n + 1, k => by
      induction k using Fin.lastCases with
      | last =>
          rw [fibrePowerLeg_last, fibrePowerLeg_last, fibrePowerBaseChangeMap_succ,
            pullback_map_comp_snd]
      | cast i =>
          have ih := fibrePowerBaseChangeMap_comp_leg h n i
          rw [fibrePowerLeg_castSucc, fibrePowerLeg_castSucc, fibrePowerBaseChangeMap_succ,
            pullback_map_comp_fst_assoc, Category.assoc, ih]

/-- The comparison morphism of fibre powers is compatible with the morphisms to the fibre
square. -/
public theorem fibrePowerBaseChangeMap_comp_pair (h : IsPullback ν' α β ν) (n : ℕ) (i j : Fin n) :
    fibrePowerBaseChangeMap h n ≫ fibrePowerPair ν n i j =
      fibrePowerPair ν' n i j ≫ fibrePowerPullbackBaseChangeMap h := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [fibrePowerPair, fibrePowerPullbackBaseChangeMap, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      fibrePowerBaseChangeMap_comp_leg]

/-- The diagonal of a base change is the base change of the diagonal. -/
public theorem isPullback_diagonal_baseChange (h : IsPullback ν' α β ν) :
    IsPullback (pullback.diagonal ν') α (fibrePowerPullbackBaseChangeMap h)
      (pullback.diagonal ν) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_pullback_map_fst h h)
  · simp only [pullback.diagonal_fst]
    exact IsPullback.of_id_fst
  · refine pullback.hom_ext ?_ ?_ <;>
      simp only [fibrePowerPullbackBaseChangeMap, Category.assoc, pullback_map_comp_fst,
        pullback_map_comp_snd, pullback.diagonal_fst, pullback.diagonal_fst_assoc,
        pullback.diagonal_snd, pullback.diagonal_snd_assoc, Category.comp_id]

/-- The range of the diagonal of a base change is the preimage of the range of the diagonal. -/
public theorem range_diagonal_baseChange (h : IsPullback ν' α β ν) :
    Set.range (pullback.diagonal ν').base =
      (fibrePowerPullbackBaseChangeMap h).base ⁻¹' Set.range (pullback.diagonal ν).base :=
  range_base_of_isPullback (isPullback_diagonal_baseChange h)

/-- The fat diagonal of a base change is the preimage of the fat diagonal. -/
public theorem fibrePowerDistinctLocus_eq_preimage (h : IsPullback ν' α β ν) (n : ℕ) :
    fibrePowerDistinctLocus ν' n =
      (fibrePowerBaseChangeMap h n).base ⁻¹' fibrePowerDistinctLocus ν n := by
  exact fibrePowerDistinctLocus_eq_preimage_of_pair _ _ (fibrePowerBaseChangeMap_comp_pair h n)
    (range_diagonal_baseChange h)

end BaseChange

/-! ### Fibre powers do not see a monomorphism on the target -/

section Mono

variable {Y S T : Scheme.{u}} (ν : Y ⟶ S) (m : S ⟶ T) [Mono m]

/-- The one-fold fibre power of `f : Y ⟶ S` is `Y` itself. -/
public noncomputable def fibrePowerOneIso {Y S : Scheme.{u}} (f : Y ⟶ S) :
    fibrePower f 1 ≅ Y :=
  haveI : IsIso (fibrePowerProj f 0) := (inferInstance : IsIso (𝟙 S))
  asIso (pullback.snd (fibrePowerProj f 0) f)

/-- The identification of the one-fold fibre power with `Y` is the second projection. -/
public theorem fibrePowerOneIso_hom_eq {Y S : Scheme.{u}} (f : Y ⟶ S) :
    (fibrePowerOneIso f).hom = pullback.snd (fibrePowerProj f 0) f := rfl

/-- The identification of the one-fold fibre power with `Y` is its unique coordinate. -/
public theorem fibrePowerOneIso_hom {Y S : Scheme.{u}} (f : Y ⟶ S) :
    (fibrePowerOneIso f).hom = fibrePowerLeg f 1 (Fin.last 0) := by
  rw [fibrePowerLeg_last, fibrePowerOneIso_hom_eq]

/-- The cartesian square exhibiting the `(n + 2)`-fold fibre power of `ν` over `S` as a fibre
product over `T` of the `(n + 1)`-fold fibre power of `ν ≫ m` with `Y`. -/
public theorem isPullback_fibrePowerMonoStep (n : ℕ)
    (e : fibrePower (ν ≫ m) (n + 1) ≅ fibrePower ν (n + 1))
    (he : e.hom ≫ fibrePowerProj ν (n + 1) ≫ m = fibrePowerProj (ν ≫ m) (n + 1)) :
    IsPullback (pullback.fst (fibrePowerProj ν (n + 1)) ν ≫ e.inv)
      (pullback.snd (fibrePowerProj ν (n + 1)) ν)
      (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m) :=
  (IsPullback.of_hasPullback (fibrePowerProj ν (n + 1)) ν).paste_horiz
    (IsPullback.of_horiz_isIso_mono ⟨by rw [Iso.inv_comp_eq]; exact he.symm⟩)

/-- The identification of the fibre powers of `ν` and of `ν ≫ m`, together with the
compatibility with the structure morphisms that is needed to build the next stage of the
recursion. -/
public noncomputable def fibrePowerMonoAux :
    (n : ℕ) → {e : fibrePower (ν ≫ m) (n + 1) ≅ fibrePower ν (n + 1) //
      e.hom ≫ fibrePowerProj ν (n + 1) ≫ m = fibrePowerProj (ν ≫ m) (n + 1)}
  | 0 => ⟨fibrePowerOneIso (ν ≫ m) ≪≫ (fibrePowerOneIso ν).symm, by
      rw [show fibrePowerProj ν 1 = (fibrePowerOneIso ν).hom ≫ ν from by
            rw [fibrePowerOneIso_hom, fibrePowerLeg_comp],
          show fibrePowerProj (ν ≫ m) 1 = (fibrePowerOneIso (ν ≫ m)).hom ≫ (ν ≫ m) from by
            rw [fibrePowerOneIso_hom, fibrePowerLeg_comp]]
      simp⟩
  | n + 1 =>
      ⟨(IsPullback.of_hasPullback (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m)).isoIsPullback _ _
          (isPullback_fibrePowerMonoStep ν m n (fibrePowerMonoAux n).1 (fibrePowerMonoAux n).2),
        by
          have h1 : fibrePowerProj ν (n + 1 + 1)
              = pullback.snd (fibrePowerProj ν (n + 1)) ν ≫ ν := by
            rw [fibrePowerProj_succ]; exact pullback.condition
          have h2 : fibrePowerProj (ν ≫ m) (n + 1 + 1)
              = pullback.snd (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m) ≫ (ν ≫ m) := by
            rw [fibrePowerProj_succ]; exact pullback.condition
          rw [h1, h2]
          simp⟩

/-- `Y ×_S ⋯ ×_S Y = Y ×_T ⋯ ×_T Y` when `S ⟶ T` is a monomorphism. -/
public noncomputable def fibrePowerMonoIso (n : ℕ) :
    fibrePower (ν ≫ m) (n + 1) ≅ fibrePower ν (n + 1) :=
  (fibrePowerMonoAux ν m n).1

/-- The identification of the fibre powers over `S` and over `T` is compatible with the structure
morphisms. -/
public theorem fibrePowerMonoIso_hom_proj (n : ℕ) :
    (fibrePowerMonoIso ν m n).hom ≫ fibrePowerProj ν (n + 1) ≫ m
      = fibrePowerProj (ν ≫ m) (n + 1) :=
  (fibrePowerMonoAux ν m n).2

/-- With one factor the identification of the fibre powers over `S` and over `T` is the
composite of the two identifications with `Y`. -/
public theorem fibrePowerMonoIso_zero_hom :
    (fibrePowerMonoIso ν m 0).hom
      = (fibrePowerOneIso (ν ≫ m)).hom ≫ (fibrePowerOneIso ν).inv := rfl

/-- One more factor in the identification of the fibre powers over `S` and over `T`, read off on
the first projection. -/
public theorem fibrePowerMonoIso_succ_hom_comp_fst (n : ℕ) :
    (fibrePowerMonoIso ν m (n + 1)).hom ≫
        pullback.fst (fibrePowerProj ν (n + 1)) ν ≫ (fibrePowerMonoIso ν m n).inv
      = pullback.fst (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m) :=
  IsPullback.isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m))
    (isPullback_fibrePowerMonoStep ν m n _ (fibrePowerMonoIso_hom_proj ν m n))

/-- One more factor in the identification of the fibre powers over `S` and over `T`, read off on
the second projection. -/
public theorem fibrePowerMonoIso_succ_hom_comp_snd (n : ℕ) :
    (fibrePowerMonoIso ν m (n + 1)).hom ≫ pullback.snd (fibrePowerProj ν (n + 1)) ν
      = pullback.snd (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m) :=
  IsPullback.isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback (fibrePowerProj (ν ≫ m) (n + 1)) (ν ≫ m))
    (isPullback_fibrePowerMonoStep ν m n _ (fibrePowerMonoIso_hom_proj ν m n))

/-- The identification of the fibre powers over `S` and over `T` is compatible with the
coordinates. -/
public theorem fibrePowerMonoIso_hom_leg :
    ∀ (n : ℕ) (k : Fin (n + 1)),
      (fibrePowerMonoIso ν m n).hom ≫ fibrePowerLeg ν (n + 1) k
        = fibrePowerLeg (ν ≫ m) (n + 1) k
  | 0, k => by
      induction k using Fin.lastCases with
      | last =>
          rw [fibrePowerLeg_last, fibrePowerLeg_last, fibrePowerMonoIso_zero_hom,
            ← fibrePowerOneIso_hom_eq ν, ← fibrePowerOneIso_hom_eq (ν ≫ m), Category.assoc,
            Iso.inv_hom_id, Category.comp_id]
      | cast i => exact i.elim0
  | n + 1, k => by
      induction k using Fin.lastCases with
      | last =>
          rw [fibrePowerLeg_last, fibrePowerLeg_last]
          exact fibrePowerMonoIso_succ_hom_comp_snd ν m n
      | cast i =>
          have ih := fibrePowerMonoIso_hom_leg n i
          rw [fibrePowerLeg_castSucc, fibrePowerLeg_castSucc,
            show fibrePowerLeg ν (n + 1) i
                = (fibrePowerMonoIso ν m n).inv ≫ fibrePowerLeg (ν ≫ m) (n + 1) i from by
              rw [Iso.eq_inv_comp]; exact ih,
            ← fibrePowerMonoIso_succ_hom_comp_fst ν m n]
          simp

/-- When `m` is a monomorphism, the fibre square of `ν` over `S` is the fibre square of `ν ≫ m`
over `T`. -/
public noncomputable def pullbackCompMonoIso : pullback ν ν ≅ pullback (ν ≫ m) (ν ≫ m) :=
  ((IsPullback.of_hasPullback ν ν).comp_mono m).isoIsPullback _ _
    (IsPullback.of_hasPullback (ν ≫ m) (ν ≫ m))

/-- The diagonal of `ν` is the diagonal of `ν ≫ m` under the identification of the two fibre
squares. -/
public theorem diagonal_comp_pullbackCompMonoIso :
    pullback.diagonal ν ≫ (pullbackCompMonoIso ν m).hom = pullback.diagonal (ν ≫ m) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [pullbackCompMonoIso, Category.assoc, IsPullback.isoIsPullback_hom_fst,
      IsPullback.isoIsPullback_hom_snd, pullback.diagonal_fst, pullback.diagonal_snd]

/-- The range of the diagonal of `ν ≫ m` is the preimage of the range of the diagonal of `ν`. -/
public theorem range_diagonal_comp_mono :
    Set.range (pullback.diagonal (ν ≫ m)).base
      = (pullbackCompMonoIso ν m).inv.base ⁻¹' Set.range (pullback.diagonal ν).base := by
  refine range_base_of_isPullback (snd := 𝟙 Y) (IsPullback.of_vert_isIso ⟨?_⟩)
  rw [Category.id_comp, ← diagonal_comp_pullbackCompMonoIso ν m, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The identification of the fibre powers over `S` and over `T` is compatible with the morphisms
to the fibre squares. -/
public theorem fibrePowerMonoIso_hom_comp_pair (n : ℕ) (i j : Fin (n + 1)) :
    (fibrePowerMonoIso ν m n).hom ≫ fibrePowerPair ν (n + 1) i j
      = fibrePowerPair (ν ≫ m) (n + 1) i j ≫ (pullbackCompMonoIso ν m).inv := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [fibrePowerPair, pullbackCompMonoIso, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, IsPullback.isoIsPullback_inv_fst, IsPullback.isoIsPullback_inv_snd,
      fibrePowerMonoIso_hom_leg]

/-- The fat diagonal of `ν ≫ m` is the fat diagonal of `ν` under the identification of the fibre
powers over `S` and over `T`. -/
public theorem fibrePowerDistinctLocus_mono (n : ℕ) :
    fibrePowerDistinctLocus (ν ≫ m) (n + 1)
      = (fibrePowerMonoIso ν m n).hom.base ⁻¹' fibrePowerDistinctLocus ν (n + 1) := by
  exact fibrePowerDistinctLocus_eq_preimage_of_pair _ _ (fibrePowerMonoIso_hom_comp_pair ν m n)
    (range_diagonal_comp_mono ν m)

end Mono

end AlgebraicGeometry

end
