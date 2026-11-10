module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Amplitude
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialDerivedPushforward
public import StacksFrontier.Algebra.Homology.StupidTruncationSplitTriangles

/-!
# Restricting a trace on `Rf_*(Ω^•[2n])` to the top piece

The inclusion `Rf_*Ω^n[n] ⟶ Rf_*(Ω^•[2n])` induces an isomorphism on `H^0`: surjectivity because
the cokernel `Rf_*σ_{≤n-1}Ω^•[2n]` lives in degrees `< 0`, injectivity because the top de Rham
differential vanishes on `R^nf_*` ([Stacks, Tag 0G8J]). Both objects lie in degrees `≤ 0`, so maps
from them to `𝒪_S` correspond to maps on `H^0`, and restriction is a bijection.

In detail, write `K = Ω^•_{X/S}` and `Rf_*` for the derived direct image along
`(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. The top inclusion `Kⁿ[-n] ⟶ K` is, up to the isomorphism
`K ≅ σ^{≤n}K`, the first map of the triangle `Kⁿ[-n] ⟶ σ^{≤n}K ⟶ σ^{≤n-1}K ⟶ Kⁿ[-n][1]` of the
stupid filtration. Since `Rf_*(K^q[-q])` lies in degrees `≤ n + q`, `Rf_*σ^{≤m}K` lies in degrees
`≤ n + m`; hence `H^{2n}` of `Rf_*σ^{≤n-1}K` vanishes and `H^{2n-1}` of `Rf_*σ^{≤n-1}K` is a
quotient of `R^{2n-1}f_*(K^{n-1}[-(n-1)]) = R^nf_*Ω^{n-1}`. On that quotient the connecting map
of the triangle is the differential `R^nf_*Ω^{n-1} ⟶ R^nf_*Ωⁿ`, which vanishes.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.bijective_topInclusion_comp_of_topDifferential`:
  restriction along `Rf_*Ωⁿ[n] ⟶ Rf_*(Ω^•[2n])` is a bijection on maps into `𝒪_S`.
* `AlgebraicGeometry.RelativeDualitySituation.isIso_homologyFunctor_zero_map_topInclusion`:
  that inclusion is an isomorphism on `H^0`.
* `StacksDraft.StupidTruncation.isIso_homologyFunctor_map_map_Q_map_stupidTruncLEι`: for a
  triangulated functor `F` and a complex `K` in degrees `≥ 0` with `F(K^q[-q])` in degrees
  `≤ N + q`, the top inclusion `Kᵖ[-p] ⟶ σ^{≤p}K` is an isomorphism on `H^{N+p}` after `F`, as
  soon as `F` kills the differential `K^{p-1} ⟶ Kᵖ` on `H^{N+p-1}`.
* `StacksDraft.StupidTruncation.stupidTruncLEι_comp_homOfDegreewiseSplit`: the connecting map of
  the stupid filtration, restricted to the next term down, is the differential of `K`.

## Implementation notes

The case `n = 0` needs no separate argument: then `K^{n-1} = 0`, and the vanishing of the
connecting map is automatic.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace DerivedCategory

open Pretriangulated

section

variable {C C' : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* C'] [Abelian C'] [HasDerivedCategory C']
  (F : DerivedCategory C ⥤ DerivedCategory C') [F.CommShift ℤ] [F.IsTriangulated]

/-- The functors `X ↦ H^{b+q}(F(X[-q]))` and `X ↦ H^b(F(X[0]))` agree. -/
def singleFunctorCompHomologyShiftIso (q b : ℤ) :
    singleFunctor C q ⋙ F ⋙ homologyFunctor C' (b + q) ≅
      singleFunctor C 0 ⋙ F ⋙ homologyFunctor C' b :=
  Functor.isoWhiskerRight ((singleFunctors C).shiftIso (-q) q 0 (by omega)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.commShiftIso (-q)) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F ((homologyFunctor C' 0).shiftIso (-q) (b + q) b (by omega)))

omit [F.IsTriangulated] in
/-- If `F` kills `g` placed in degree `0` on `H^b`, it kills `g` placed in degree `q` on
`H^{b+q}`. -/
theorem homologyFunctor_map_map_singleFunctor_map_eq_zero {M M' : C} (g : M ⟶ M') (q b : ℤ)
    (h : (homologyFunctor C' b).map (F.map ((singleFunctor C 0).map g)) = 0) :
    (homologyFunctor C' (b + q)).map (F.map ((singleFunctor C q).map g)) = 0 := by
  refine (NatIso.naturality_2 (singleFunctorCompHomologyShiftIso F q b) g).symm.trans ?_
  change _ ≫ (homologyFunctor C' b).map (F.map ((singleFunctor C 0).map g)) ≫ _ = 0
  rw [h, zero_comp, comp_zero]

omit [F.IsTriangulated] in
/-- If `H^b(F(M[0])) = 0`, then `H^{b+q}(F(M[-q])) = 0`. -/
theorem isZero_homologyFunctor_obj_map_singleFunctor_obj (M : C) (q b : ℤ)
    (h : IsZero ((homologyFunctor C' b).obj (F.obj ((singleFunctor C 0).obj M)))) :
    IsZero ((homologyFunctor C' (b + q)).obj (F.obj ((singleFunctor C q).obj M))) :=
  h.of_iso ((singleFunctorCompHomologyShiftIso F q b).app M)

omit [F.IsTriangulated] in
/-- If `F(f)` is invertible on `H^a`, then `F(f[a])` is invertible on `H^0`. -/
theorem isIso_homologyFunctor_zero_map_map_shift_map {X Y : DerivedCategory C} (f : X ⟶ Y)
    (a : ℤ) (h : IsIso ((homologyFunctor C' a).map (F.map f))) :
    IsIso ((homologyFunctor C' 0).map (F.map (f⟦a⟧'))) := by
  have : IsIso ((homologyFunctor C' 0).map ((F.map f)⟦a⟧')) :=
    (NatIso.isIso_map_iff ((homologyFunctor C' 0).shiftIso a 0 a (add_zero a)) (F.map f)).2 h
  have e : F.map (f⟦a⟧') = (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' ≫
      (F.commShiftIso a).inv.app Y := by
    simp
  rw [e, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A criterion for the first map of a triangle to be invertible on `H^b`.** For a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X[1]`, the map `H^b(X) ⟶ H^b(Y)` is an isomorphism as soon
as `H^b(Y) ⟶ H^b(Z)` vanishes and the connecting map `H^{b-1}(Z) ⟶ H^b(X)` vanishes on the
image of some `H^{b-1}(W) ⟶ H^{b-1}(Z)` which is surjective. -/
theorem isIso_homologyFunctor_map_of_distinguished {X Y Z W : DerivedCategory C'} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang _) (u : W ⟶ Z)
    (a b : ℤ) (hab : a + 1 = b) (hg : (homologyFunctor C' b).map g = 0)
    (hu : Epi ((homologyFunctor C' a).map u)) (huh : (homologyFunctor C' a).map (u ≫ h) = 0) :
    IsIso ((homologyFunctor C' b).map f) := by
  have hepi : Epi ((homologyFunctor C' b).map f) :=
    (HomologySequence.epi_homologyMap_mor₁_iff _ hT b).2 hg
  have hmono : Mono ((homologyFunctor C' b).map f) := by
    refine (HomologySequence.mono_homologyMap_mor₁_iff _ hT a b hab).2 ?_
    refine (cancel_epi ((homologyFunctor C' a).map u)).1 ?_
    rw [comp_zero]
    change ((homologyFunctor C' 0).shift a).map u ≫
      (homologyFunctor C' 0).shiftMap h a b (by omega) = 0
    rw [← Functor.shiftMap_comp', Functor.shiftMap]
    change (homologyFunctor C' a).map (u ≫ h) ≫ _ = 0
    rw [huh]
    exact zero_comp
  exact isIso_of_mono_of_epi _

/-- **Precomposition with a map inducing an isomorphism on `H^a`** is a bijection on maps into an
object in degrees `≥ a`, between objects in degrees `≤ a`: such maps are determined by their
effect on `H^a`. -/
theorem bijective_comp_of_isIso_homologyFunctor_map {X Y Z : DerivedCategory C'} (i : X ⟶ Y)
    (a : ℤ) [hX : X.IsLE a] [hY : Y.IsLE a] [hZ : Z.IsGE a]
    (hi : IsIso ((homologyFunctor C' a).map i)) :
    Function.Bijective (fun s : Y ⟶ Z => i ≫ s) := by
  have bX := bijective_homologyFunctor_map_of_isLE_of_isGE X Z a
  have bY := bijective_homologyFunctor_map_of_isLE_of_isGE Y Z a
  refine ⟨fun s s' hs => bY.1 ?_, fun t => ?_⟩
  · have := congrArg (homologyFunctor C' a).map hs
    simp only [Functor.map_comp] at this
    exact (cancel_epi _).1 this
  · obtain ⟨s, hs⟩ := bY.2 (inv ((homologyFunctor C' a).map i) ≫ (homologyFunctor C' a).map t)
    refine ⟨s, bX.1 ?_⟩
    simp only [Functor.map_comp] at hs ⊢
    rw [hs, IsIso.hom_inv_id_assoc]

end

end DerivedCategory

namespace StacksDraft.StupidTruncation

open DerivedCategory Pretriangulated HomologicalComplex ComplexShape

/-- **The connecting map of the stupid filtration on the next term down is the differential.**
The inclusion `K^{p'}[-p'] ⟶ σ^{≤p'}K` followed by the connecting map
`σ^{≤p'}K ⟶ Kᵖ[-p][1]` of the triangle of `σ^{≤p}K` is the differential `K^{p'} ⟶ Kᵖ` placed in
degree `p'`, read through `Kᵖ[-p][1] ≅ Kᵖ[-p']`. -/
theorem stupidTruncLEι_comp_homOfDegreewiseSplit {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (p p' : ℤ) (hp : p' + 1 = p) :
    stupidTruncLEι K p' ≫
        CochainComplex.homOfDegreewiseSplit _ (stupidTruncLESplitting K p p' hp) =
      (single C (up ℤ) p').map (K.d p' p) ≫
        ((CochainComplex.singleFunctors C).shiftIso 1 p' p (by omega)).inv.app (K.X p) := by
  subst hp
  apply from_single_hom_ext
  have := isIso_stupidTruncLEMapLE_f_of_ne K (p' + 1) p' rfl p' (by omega)
  have := isIso_stupidTruncLEι_f_self K (p' + 1)
  have hs : inv ((stupidTruncLEMapLE K (show p' ≤ p' + 1 by omega)).f p') =
      (stupidTruncLEXIso K p' p' le_rfl).hom ≫ (stupidTruncLEXIso K (p' + 1) p' (by omega)).inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [stupidTruncLEMapLE_f K _ p' le_rfl]; simp)
  have hr : inv ((stupidTruncLEι K (p' + 1)).f (p' + 1)) =
      (stupidTruncLEXIso K (p' + 1) (p' + 1) le_rfl).hom ≫
        (singleObjXSelf (up ℤ) (p' + 1) (K.X (p' + 1))).inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [stupidTruncLEι_f]; simp)
  have hd : (stupidTruncLEShortComplex K (p' + 1) p' rfl).X₂.d p' (p' + 1) =
      (stupidTruncLEXIso K (p' + 1) p' (by omega)).hom ≫ K.d p' (p' + 1) ≫
        (stupidTruncLEXIso K (p' + 1) (p' + 1) le_rfl).inv :=
    K.stupidTrunc_d_eq (embeddingUpIntLE (p' + 1)) _ _
  change (stupidTruncLEι K p').f p' ≫ (CochainComplex.homOfDegreewiseSplit _
    (stupidTruncLESplitting K (p' + 1) p' rfl)).f p' = _
  rw [CochainComplex.homOfDegreewiseSplit_f, CochainComplex.cocycleOfDegreewiseSplit,
    CochainComplex.HomComplex.Cocycle.mk_coe, CochainComplex.HomComplex.Cochain.mk_v,
    HomologicalComplex.comp_f,
    stupidTruncLESplitting_s_of_ne K _ _ rfl p' (by omega), stupidTruncLESplitting_r_self]
  simp only [hs, hr, hd]
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    HomologicalComplex.eval_obj, stupidTruncLEShortComplex]
  simp only [stupidTruncLEι_f, single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  simp [singleObjXSelf, singleObjXIsoOfEq]

section Derived

variable {C C' : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* C'] [Abelian C'] [HasDerivedCategory C']
  (F : DerivedCategory C ⥤ DerivedCategory C') [F.CommShift ℤ] [F.IsTriangulated]
  (K : CochainComplex C ℤ)

/-- **Amplitude of the stupid truncations.** If `F` sends each term `Kᵖ[-p]` (`p ≥ 0`) of a
complex concentrated in degrees `≥ 0` into degrees `≤ N + p`, then it sends `σ^{≤m}K` into
degrees `≤ N + m`. -/
theorem isZero_homologyFunctor_obj_map_Q_obj_stupidTruncLE
    (hK₀ : ∀ j : ℤ, j < 0 → IsZero (K.X j)) (N : ℤ)
    (hK : ∀ p : ℤ, 0 ≤ p → ∀ i : ℤ, N + p < i →
      IsZero ((homologyFunctor C' i).obj (F.obj ((singleFunctor C p).obj (K.X p)))))
    (m i : ℤ) (hi : N + m < i) :
    IsZero ((homologyFunctor C' i).obj
      (F.obj (Q.obj (K.stupidTrunc (embeddingUpIntLE m))))) := by
  have hzero : ∀ m : ℤ, m < 0 → ∀ i : ℤ, IsZero ((homologyFunctor C' i).obj
      (F.obj (Q.obj (K.stupidTrunc (embeddingUpIntLE m))))) := by
    intro m hm i
    have : IsZero (K.stupidTrunc (embeddingUpIntLE m)) := by
      rw [HomologicalComplex.isZero_stupidTrunc_iff]
      exact ⟨fun j => hK₀ (m - j) (by omega)⟩
    exact (homologyFunctor C' i).map_isZero (F.map_isZero (Q.map_isZero this))
  have key : ∀ m : ℤ, (h : -1 ≤ m) → ∀ i : ℤ, N + m < i → IsZero ((homologyFunctor C' i).obj
      (F.obj (Q.obj (K.stupidTrunc (embeddingUpIntLE m))))) := by
    intro m hm
    induction m, hm using Int.leInduction with
    | base => exact fun i _ => hzero (-1) (by omega) i
    | succ m hm ih =>
      intro i hi
      have hT := F.map_distinguished _ (stupidTruncLESplitTriangleQ_distinguished K (m + 1) m rfl)
      exact (HomologySequence.exact₂ _ hT i).isZero_X₂
        ((hK (m + 1) (by omega) i (by omega)).eq_of_src _ _) ((ih i (by omega)).eq_of_tgt _ _)
  rcases lt_or_ge m 0 with hm | hm
  · exact hzero m hm i
  · exact key m (by omega) i hi

/-- **The top term of a stupid truncation on cohomology.** Let `K` be concentrated in degrees
`≥ 0` and let `F` send each `K^q[-q]` into degrees `≤ N + q`. If `F` kills the differential
`K^{p'} ⟶ Kᵖ` (`p' + 1 = p`) on `H^{N+p'}`, then the inclusion `Kᵖ[-p] ⟶ σ^{≤p}K` induces an
isomorphism on `H^{N+p}` after applying `F`. -/
theorem isIso_homologyFunctor_map_map_Q_map_stupidTruncLEι
    (hK₀ : ∀ j : ℤ, j < 0 → IsZero (K.X j)) (N p p' p'' : ℤ) (hp : p' + 1 = p) (hp' : p'' + 1 = p')
    (hK : ∀ q : ℤ, 0 ≤ q → ∀ i : ℤ, N + q < i →
      IsZero ((homologyFunctor C' i).obj (F.obj ((singleFunctor C q).obj (K.X q)))))
    (hd : (homologyFunctor C' (N + p')).map (F.map ((singleFunctor C p').map (K.d p' p))) = 0) :
    IsIso ((homologyFunctor C' (N + p)).map (F.map (Q.map (stupidTruncLEι K p)))) := by
  let ψ : K.stupidTrunc (embeddingUpIntLE p') ⟶ ((single C (up ℤ) p).obj (K.X p))⟦(1 : ℤ)⟧ :=
    CochainComplex.homOfDegreewiseSplit _ (stupidTruncLESplitting K p p' hp)
  have hψ : stupidTruncLEι K p' ≫ ψ = (single C (up ℤ) p').map (K.d p' p) ≫
      ((CochainComplex.singleFunctors C).shiftIso 1 p' p (by omega)).inv.app (K.X p) :=
    stupidTruncLEι_comp_homOfDegreewiseSplit K p p' hp
  have hT₁ : Triangle.mk (F.map (Q.map (stupidTruncLEι K p)))
      (F.map (Q.map (stupidTruncLEMapLE K (show p' ≤ p by omega))))
      (F.map (Q.map ψ ≫ (Q.commShiftIso (1 : ℤ)).hom.app _) ≫
        (F.commShiftIso (1 : ℤ)).hom.app _) ∈ distTriang _ :=
    F.map_distinguished _ (stupidTruncLESplitTriangleQ_distinguished K p p' hp)
  have hT₂ := F.map_distinguished _ (stupidTruncLESplitTriangleQ_distinguished K p' p'' hp')
  refine isIso_homologyFunctor_map_of_distinguished _ _ _ hT₁ (F.map (Q.map (stupidTruncLEι K p')))
    (N + p') (N + p) (by omega)
    ((isZero_homologyFunctor_obj_map_Q_obj_stupidTruncLE F K hK₀ N hK p' (N + p)
      (by omega)).eq_of_tgt _ _)
    ((HomologySequence.epi_homologyMap_mor₁_iff _ hT₂ (N + p')).2
      ((isZero_homologyFunctor_obj_map_Q_obj_stupidTruncLE F K hK₀ N hK p'' (N + p')
        (by omega)).eq_of_tgt _ _)) ?_
  rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← Q.map_comp, hψ]
  simp only [Functor.map_comp, Category.assoc]
  change (homologyFunctor C' (N + p')).map (F.map ((singleFunctor C p').map (K.d p' p))) ≫ _ = 0
  rw [hd, zero_comp]

end Derived

end StacksDraft.StupidTruncation

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

open StacksDraft.StupidTruncation DerivedCategory

/-- `Ω^•_{X/S}`, extended by zero to `ℤ`, lives in degrees `≤ n`. -/
theorem isStrictlyLE_deRhamCx_extend :
    CochainComplex.IsStrictlyLE (D.deRhamCx.extend ComplexShape.embeddingUpNat) D.n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro j hj
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
  exact ((SheafOfModules.restrictScalars _).map_isZero
    (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension D.f D.n k
      (by omega))).of_iso (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := k) rfl)

/-- `R^if_*(Ω^q_{X/S}[-q]) = 0` for `i > n + q`, read along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. -/
theorem isZero_homologyFunctor_obj_derivedPushforward_deRhamCx_X (q : ℤ) (hq : 0 ≤ q) (i : ℤ)
    (hi : (D.n : ℤ) + q < i) :
    IsZero ((DerivedCategory.homologyFunctor D.S.Modules i).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).obj
        ((DerivedCategory.singleFunctor _ q).obj
          ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X q)))) := by
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (inverseImageBaseProjection D.f)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain ⟨b, rfl⟩ : ∃ b, i = b + k := ⟨i - k, by omega⟩
  refine isZero_homologyFunctor_obj_map_singleFunctor_obj
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)) _ (k : ℤ) b ?_
  have := D.isLE_derivedPushforward_formsInDegreeZero k
  exact (DerivedCategory.isZero_of_isLE
    ((Stacks.Duality.derivedPushforward D.f).obj (D.f.formsInDegreeZero k)) D.n b
      (by omega)).of_iso
    ((DerivedCategory.homologyFunctor D.S.Modules b).mapIso
      ((derivedPushforward (inverseImageBaseProjection D.f)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := k) rfl)) ≪≫
        (D.f.formsDirectImageIso k).symm))

/-- **The top de Rham differential vanishes on `R^{2n-1}f_*` of `Ω^{n-1}[-(n-1)]`**, given that
it vanishes on `R^nf_*Ω^{n-1} ⟶ R^nf_*Ω^n` ([Stacks, Tag 0G8J]). For `n = 0` the source is
zero. -/
theorem homologyFunctor_map_derivedPushforward_singleFunctor_map_deRhamCx_extend_d
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    (DerivedCategory.homologyFunctor D.S.Modules ((D.n : ℤ) + ((D.n : ℤ) - 1))).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
        ((DerivedCategory.singleFunctor _ ((D.n : ℤ) - 1)).map
          ((D.deRhamCx.extend ComplexShape.embeddingUpNat).d ((D.n : ℤ) - 1) D.n))) = 0 := by
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (inverseImageBaseProjection D.f)
  refine homologyFunctor_map_map_singleFunctor_map_eq_zero
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)) _ ((D.n : ℤ) - 1)
    D.n ?_
  rcases Nat.eq_zero_or_pos D.n with hn | hn
  · have hz : IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X ((D.n : ℤ) - 1)) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)
    exact ((DerivedCategory.homologyFunctor D.S.Modules D.n).map_isZero
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map_isZero
        ((DerivedCategory.singleFunctor _ 0).map_isZero hz))).eq_of_src _ _
  · let G := DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing
      (inverseImageBase D.f))) 0 ⋙
      derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f) ⋙
      DerivedCategory.homologyFunctor D.S.Modules D.n
    have hG : G.map (D.deRhamCx.d (D.n - 1) D.n) = 0 :=
      D.homologyFunctor_map_derivedPushforward_deRham_d_eq_zero h
    rw [HomologicalComplex.extend_d_eq D.deRhamCx ComplexShape.embeddingUpNat
      (i' := (D.n : ℤ) - 1) (j' := D.n) (i := D.n - 1) (j := D.n) (by simp; omega) rfl]
    refine ((G.map_comp _ _).trans (congrArg (G.map _ ≫ ·) (G.map_comp _ _))).trans ?_
    rw [hG, zero_comp, comp_zero]
    rfl

/-- The inclusion `Ωⁿ[-n] ⟶ Ω^•` of the top piece, followed by the projection
`Ω^• ⟶ σ^{≤n}Ω^•` (an isomorphism), is the inclusion of the top term of `σ^{≤n}Ω^•`. -/
theorem topFormsToDeRham_comp_πStupidTrunc :
    D.topFormsToDeRham ≫
        (D.deRhamCx.extend ComplexShape.embeddingUpNat).πStupidTrunc
          (ComplexShape.embeddingUpIntLE D.n) =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).map
          (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n) rfl).inv ≫
        stupidTruncLEι (D.deRhamCx.extend ComplexShape.embeddingUpNat) D.n := by
  apply HomologicalComplex.from_single_hom_ext
  have h₁ : D.topFormsToDeRham.f D.n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) D.n D.topForms).hom ≫
        (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n) rfl).inv :=
    HomologicalComplex.mkHomFromSingle_f _ _
  have h₂ : ((D.deRhamCx.extend ComplexShape.embeddingUpNat).πStupidTrunc
      (ComplexShape.embeddingUpIntLE D.n)).f D.n =
      (stupidTruncLEXIso (D.deRhamCx.extend ComplexShape.embeddingUpNat) D.n D.n le_rfl).inv :=
    πStupidTrunc_f _ _ (i := ((D.n : ℤ) - D.n).toNat)
      (by change (D.n : ℤ) - (((D.n : ℤ) - D.n).toNat : ℤ) = D.n; omega)
  refine ((HomologicalComplex.comp_f _ _ _).trans ?_).trans (HomologicalComplex.comp_f _ _ _).symm
  rw [h₁, h₂, stupidTruncLEι_f, HomologicalComplex.single_map_f_self]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom, eqToIso.inv]
  have key : ∀ {𝒞 : Type _} [Category 𝒞] {P Q R R' T : 𝒞} (e₁ e₁' : P = Q) (x : Q ⟶ R)
      (e₂ : R = R') (e₃ : R' = R) (y : R ⟶ T),
      (eqToHom e₁ ≫ x) ≫ y = (eqToHom e₁' ≫ x ≫ eqToHom e₂) ≫ eqToHom e₃ ≫ y := by
    intros
    subst_vars
    simp
  exact key _ _ _ _ _ _

/-- **`R^nf_*Ωⁿ ⟶ R^{2n}f_*Ω^•` is an isomorphism**, given the vanishing of the top de Rham
differential on `R^nf_*` ([Stacks, Tag 0G8J]). -/
theorem isIso_homologyFunctor_map_derivedPushforward_Q_map_topFormsToDeRham
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    IsIso ((DerivedCategory.homologyFunctor D.S.Modules (2 * D.n : ℤ)).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
        (DerivedCategory.Q.map D.topFormsToDeRham))) := by
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (inverseImageBaseProjection D.f)
  have _ := D.isStrictlyLE_deRhamCx_extend
  have hι := isIso_homologyFunctor_map_map_Q_map_stupidTruncLEι
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f))
    (D.deRhamCx.extend ComplexShape.embeddingUpNat)
    (fun j hj => HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega))
    D.n D.n (D.n - 1) (D.n - 1 - 1) (by omega) (by omega)
    (fun q hq i hi => D.isZero_homologyFunctor_obj_derivedPushforward_deRhamCx_X q hq i hi)
    (D.homologyFunctor_map_derivedPushforward_singleFunctor_map_deRhamCx_extend_d h)
  let G := (DerivedCategory.Q : CochainComplex (SheafOfModules.{u} (structureSheafRing
      (inverseImageBase D.f))) ℤ ⥤ _) ⋙
    derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f) ⋙
    DerivedCategory.homologyFunctor D.S.Modules (D.n + D.n)
  have hι' : IsIso (G.map (stupidTruncLEι (D.deRhamCx.extend ComplexShape.embeddingUpNat) D.n)) :=
    hι
  have hπ : IsIso (G.map ((D.deRhamCx.extend ComplexShape.embeddingUpNat).πStupidTrunc
      (ComplexShape.embeddingUpIntLE D.n))) :=
    (G.mapIso (@asIso _ _ _ _ ((D.deRhamCx.extend ComplexShape.embeddingUpNat).πStupidTrunc
      (ComplexShape.embeddingUpIntLE D.n)) (isIso_πStupidTruncLE _ _))).isIso_hom
  have hu : IsIso (G.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).map
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n) rfl).inv)) :=
    (G.mapIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).mapIso
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n) rfl).symm)).isIso_hom
  have hfac := ((G.map_comp _ _).symm.trans
    (congrArg G.map D.topFormsToDeRham_comp_πStupidTrunc)).trans (G.map_comp _ _)
  rw [show (2 * D.n : ℤ) = D.n + D.n by ring]
  change IsIso (G.map D.topFormsToDeRham)
  rw [← IsIso.eq_comp_inv] at hfac
  rw [hfac]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' hu hι') (IsIso.inv_isIso (f := G.map _))

/-- **The top inclusion `Rf_*Ωⁿ[n] ⟶ Rf_*(Ω^•[2n])` is an isomorphism on `H^0`**, given the
vanishing of the top de Rham differential on `R^nf_*` ([Stacks, Tag 0G8J]). -/
theorem isIso_homologyFunctor_zero_map_topInclusion
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    IsIso ((DerivedCategory.homologyFunctor D.S.Modules 0).map D.topInclusion) := by
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (inverseImageBaseProjection D.f)
  have h₁ := isIso_homologyFunctor_zero_map_map_shift_map
    (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f))
    (DerivedCategory.Q.map D.topFormsToDeRham) (2 * D.n : ℤ)
    (D.isIso_homologyFunctor_map_derivedPushforward_Q_map_topFormsToDeRham h)
  have e : (DerivedCategory.homologyFunctor D.S.Modules 0).map D.topInclusion =
      (DerivedCategory.homologyFunctor D.S.Modules 0).map D.topPieceIso.hom ≫
        (DerivedCategory.homologyFunctor D.S.Modules 0).map
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
            ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf)
              (2 * D.n : ℤ)).map (DerivedCategory.Q.map D.topFormsToDeRham))) :=
    (DerivedCategory.homologyFunctor D.S.Modules 0).map_comp _ _
  rw [e]
  exact IsIso.comp_isIso'
    ((DerivedCategory.homologyFunctor D.S.Modules 0).mapIso D.topPieceIso).isIso_hom h₁

/-- **Maps out of `Rf_*(Ω^•[2n])` are determined by their restriction to the top piece**, given
that the top de Rham differential `d : R^nf_*Ω^{n-1} ⟶ R^nf_*Ω^n` vanishes ([Stacks, Tag 0G8J]). -/
theorem bijective_topInclusion_comp_of_topDifferential
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    Function.Bijective
      (fun s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj =>
        D.topInclusion ≫ s) :=
  bijective_comp_of_isIso_homologyFunctor_map D.topInclusion 0
    (hX := D.isLE_derivedPushforward_formsTop) (hY := D.isLE_deRhamDirectImageTop)
    (hZ := DerivedCategory.instIsGEObjSingleFunctor _ _)
    (D.isIso_homologyFunctor_zero_map_topInclusion h)

end AlgebraicGeometry.RelativeDualitySituation

end
