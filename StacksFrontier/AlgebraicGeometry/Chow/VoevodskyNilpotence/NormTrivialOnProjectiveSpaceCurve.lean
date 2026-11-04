module

public import
  StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormTrivialOnProjectiveSpaceLocal
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.FibrePowerPermutation
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk

/-!
# The norm sheaf of Stacks 0FH9 is trivial on projective spaces: the curve case

Let `X` be a smooth curve over a field `k` with two `k`-rational points `x, x'`, and let
`ℒ = 𝒪_X(x - x')`, characterized by its class `[ℐ_{x'}] - [ℐ_x]` in `Pic(X)`, where `ℐ_t` is the
ideal sheaf of the point `t`. Let `π : Xⁿ ⟶ H` be finite locally free of rank `n!` over `k` and
`𝒩 = Norm_π(pr₁^*ℒ)`. This file proves, as the last paragraph of the proof of Stacks 0FH9
asserts, that `j^*𝒩` is trivial for every `m` and every morphism `j : ℙᵐ_k ⟶ H` over `k`.

The family is the source's: `T = X`, `p = x'`, `q = x`, and on `X × T` the invertible module
`𝒪_{X × X}(Δ) ⊗ pr₁^*𝒪_X(-x')`, whose class is `pr₁^*[ℐ_{x'}] - [ℐ_Δ]`. By
`Stacks.Hilbert.pullbackPicardClass_fibreAt_diagonalIdeal` its restriction to the fibre over a
point `t` has class `[ℐ_{x'}] - [ℐ_t]`: trivial over `x'`, and `[ℒ]` over `x`. The family is
pulled back to `T × Xⁿ` along `id_T × pr₁`, and
`Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily_specializes`
concludes: the local rings of a smooth curve at its closed points are discrete valuation rings
(`AlgebraicGeometry.IsCurve.isDiscreteValuationRing_stalk_of_isClosed`), and the local ring at the
generic point is the function field.

Nothing about `H` or `π` is used beyond finite local freeness of constant rank.

## Main results

* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_curve`: for any `g : P ⟶ X` and
  any finite locally free `π : P ⟶ Q` over `k`, `j^*Norm_π(g^*ℒ)` is trivial.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_fibrePower_eq_zero`: **the statement of
  the source**, for `P = Xⁿ`, `g = pr₁` and `π` of rank `n!`.
* `Stacks.Divisors.isTrivial_pullback_normInvertible_fibrePower`: the same, as triviality of
  the invertible module `j^*𝒩`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.SheafOfModules Stacks.Hilbert

universe u

namespace Stacks.Divisors

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}

/-- The class `[ℐ_t] = [𝒪_X(-t)]` in `Pic(X)` of the ideal sheaf of a section `t` of a separated
smooth relative curve. -/
def pointIdealClass (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (t : Spec (CommRingCat.of k) ⟶ X) (ht : t ≫ f = 𝟙 _) :
    X.picardGroup :=
  X.picardClass (negativeTwist' t.ker) (isInvertible_negativeTwist' _
    (isEffectiveCartierDivisor_ker_section t ht))

variable {P Q : Scheme.{u}}

/-- The morphism `(T ×_k Q) ×_Q P ⟶ X ×_k T`, `T = X`, given by `g` on the first factor and the
projection to `T` on the second. -/
def curveFamilyMap (f : X ⟶ Spec (CommRingCat.of k)) (π : P ⟶ Q)
    (sQ : Q ⟶ Spec (CommRingCat.of k)) (g : P ⟶ X) (hg : g ≫ f = π ≫ sQ) :
    pullback (pullback.snd f sQ) π ⟶ pullback f f :=
  pullback.lift (pullback.snd _ π ≫ g) (pullback.fst _ π ≫ pullback.fst f sQ) (by
    rw [Category.assoc, hg, ← Category.assoc, ← pullback.condition, Category.assoc,
      Category.assoc, pullback.condition])

/-- The restriction of `curveFamilyMap` to the fibre of `(T ×_k Q) ×_Q P` over a section `t` of
`T = X` is `g` followed by the inclusion `fibreAt t` of the fibre of `X ×_k T` over `t`. -/
theorem sourceFibreInclusion_comp_curveFamilyMap (π : P ⟶ Q)
    (sQ : Q ⟶ Spec (CommRingCat.of k)) (g : P ⟶ X) (hg : g ≫ f = π ≫ sQ)
    (t : Spec (CommRingCat.of k) ⟶ X) (ht : t ≫ f = 𝟙 _) :
    sourceFibreInclusion f sQ π t ht ≫ curveFamilyMap f π sQ g hg = g ≫ fibreAt t ht := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, curveFamilyMap, pullback.lift_fst, sourceFibreInclusion, ← Category.assoc,
      pullback.lift_snd, Category.id_comp, Category.assoc, fibreAt_fst, Category.comp_id]
  · rw [Category.assoc, curveFamilyMap, pullback.lift_snd, sourceFibreInclusion,
      ← Category.assoc, pullback.lift_fst, Category.assoc, fibreInclusion, pullback.lift_fst,
      Category.assoc, fibreAt_snd, ← Category.assoc, ← hg, Category.assoc]

/-- The image of a section of a separated morphism is a closed point. -/
theorem isClosed_singleton_section [IsSeparated f] (t : Spec (CommRingCat.of k) ⟶ X)
    (ht : t ≫ f = 𝟙 _) :
    IsClosed ({t (IsLocalRing.closedPoint (CommRingCat.of k))} : Set X) := by
  have : IsClosedImmersion (t ≫ f) := by
    rw [ht]
    infer_instance
  have := IsClosedImmersion.of_comp t f
  have hr : Set.range t = {t (IsLocalRing.closedPoint (CommRingCat.of k))} := by
    ext y
    refine ⟨?_, fun h ↦ ⟨_, (Set.mem_singleton_iff.1 h).symm⟩⟩
    rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint (CommRingCat.of k))]
    rfl
  exact hr ▸ t.isClosedEmbedding.isClosed_range

section Separated

variable [IsSeparated f] [SmoothOfRelativeDimension 1 f]

/-- The class `pr₁^*[ℐ_{x'}] - [ℐ_Δ]` on `X ×_k X` of the source's family
`𝒪_{X × X}(Δ) ⊗ pr₁^*𝒪_X(-x')`. -/
def curveFamilyClass (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (x' : Spec (CommRingCat.of k) ⟶ X) (hx' : x' ≫ f = 𝟙 _) :
    (pullback f f).picardGroup :=
  pullbackPicardHom (pullback.fst f f) (pointIdealClass f x' hx') -
    (pullback f f).picardClass (negativeTwist' (diagonalIdeal f))
      (isInvertible_negativeTwist' _ (isEffectiveCartierDivisor_diagonalIdeal f))

/-- **The fibres of the source's family**: over a point `t` the class of the family is
`[ℐ_{x'}] - [ℐ_t]`. -/
theorem pullbackPicardHom_fibreAt_curveFamilyClass (x' : Spec (CommRingCat.of k) ⟶ X)
    (hx' : x' ≫ f = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ X) (ht : t ≫ f = 𝟙 _) :
    pullbackPicardHom (fibreAt t ht) (curveFamilyClass f x' hx') =
      pointIdealClass f x' hx' - pointIdealClass f t ht := by
  rw [curveFamilyClass, map_sub, ← pullbackPicardHom_comp_apply, fibreAt_fst,
    pullbackPicardHom_id, pullbackPicardHom_picardClass,
    pullbackPicardClass_fibreAt_diagonalIdeal]
  rfl

/-- `𝒪_X(x - x')` exists: there is an invertible module on `X` of class `[ℐ_{x'}] - [ℐ_x]`. -/
theorem exists_isInvertible_picardClass_eq_pointIdealClass_sub
    (x x' : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L),
      X.picardClass L hL = pointIdealClass f x' hx' - pointIdealClass f x hx :=
  exists_picardClass_eq X.presheaf X.ringCatIsSheaf _

end Separated

variable [IsCurve k f] [SmoothOfRelativeDimension 1 f]

/-- **The norm sheaf is trivial on projective space, for the source's family on a smooth
curve.** Let `X` be a smooth curve over a field `k`, `x, x'` two `k`-points, and `ℒ` an
invertible module on `X` of class `[ℐ_{x'}] - [ℐ_x]`, i.e. `ℒ ≅ 𝒪_X(x - x')`. Let `g : P ⟶ X`
and `π : P ⟶ Q` finite locally free of rank `d > 0`, compatibly over `k`. Then for every morphism
`j : ℙᵐ_k ⟶ Q` over `k`, `j^*Norm_π(g^*ℒ)` is trivial. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_curve
    (x x' : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
    (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hLc : X.picardClass L hL = pointIdealClass f x' hx' - pointIdealClass f x hx)
    (π : P ⟶ Q) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (sQ : Q ⟶ Spec (CommRingCat.of k)) (g : P ⟶ X) (hg : g ≫ f = π ≫ sQ)
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ Q)
    (hj : j ≫ sQ = projectiveSpaceStructure m (Spec (CommRingCat.of k))) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    haveI := hL
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap
          ((modulePullback g.toLRSHom.toShHom).obj L))
        (isInvertible_normInvertible π _ _
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π _
            (Stacks.RingedSpace.modulePullback_isInvertible _ L))) = 0 := by
  have := hL
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hcl := fun (t : Spec (CommRingCat.of k) ⟶ X) (ht : t ≫ f = 𝟙 _) =>
    IsCurve.isDiscreteValuationRing_stalk_of_isClosed k f (isClosed_singleton_section t ht)
  have := hcl x hx
  have := hcl x' hx'
  have : IsDomain (X.presheaf.stalk (genericPoint X)) :=
    inferInstanceAs (IsDomain X.functionField)
  have : UniqueFactorizationMonoid (X.presheaf.stalk (genericPoint X)) :=
    inferInstanceAs (UniqueFactorizationMonoid X.functionField)
  obtain ⟨L', hL', hL'c⟩ := exists_picardClass_eq _ _
    (pullbackPicardHom (curveFamilyMap f π sQ g hg) (curveFamilyClass f x' hx'))
  have hfib : ∀ (t : Spec (CommRingCat.of k) ⟶ X) (ht : t ≫ f = 𝟙 _),
      pullbackPicardClass (sourceFibreInclusion f sQ π t ht) L' hL' =
        pullbackPicardHom g (pointIdealClass f x' hx' - pointIdealClass f t ht) :=
    fun t ht => (pullbackPicardHom_picardClass _ L' hL').symm.trans
      ((congrArg (pullbackPicardHom (sourceFibreInclusion f sQ π t ht)) hL'c).trans
        ((pullbackPicardHom_comp_apply _ _ _).symm.trans
          ((congrArg (fun φ => pullbackPicardHom φ (curveFamilyClass f x' hx'))
            (sourceFibreInclusion_comp_curveFamilyMap π sQ g hg t ht)).trans
            ((pullbackPicardHom_comp_apply g (fibreAt t ht) _).trans
              (congrArg (pullbackPicardHom g)
                (pullbackPicardHom_fibreAt_curveFamilyClass x' hx' t ht))))))
  refine pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily_specializes π d hd m f
    x' x hx' hx (genericPoint X) (genericPoint_specializes _) (genericPoint_specializes _) sQ j hj
    L' hL' ?_ ((modulePullback g.toLRSHom.toShHom).obj L)
    (Stacks.RingedSpace.modulePullback_isInvertible _ L) ?_
  · rw [hfib x' hx', sub_self, map_zero]
  · exact (hfib x hx).trans ((congrArg (pullbackPicardHom g) hLc.symm).trans
      (pullbackPicardHom_picardClass g L hL))

/-- **Stacks 0FH9, last paragraph: the norm sheaf `𝒩 = Norm_π(pr₁^*𝒪_X(x - x'))` is trivial on
every projective space mapping to `Sⁿ(X)`.** Let `X` be a smooth curve over a field `k` with
`k`-points `x, x'`, let `ℒ` be invertible on `X` of class `[ℐ_{x'}] - [ℐ_x]`, i.e.
`ℒ ≅ 𝒪_X(x - x')`, and let `Xⁿ` be the `n`-fold fibre power of `X` over `k`. Let
`π : Xⁿ ⟶ H` be finite locally free of rank `n!` over `k` and let `ℒ_{i₀} = pr_{i₀}^*ℒ`. Then for
every `m` and every morphism `j : ℙᵐ_k ⟶ H` over `k`, `j^*Norm_π(ℒ_{i₀})` is trivial. -/
theorem pullbackPicardClass_normInvertible_fibrePower_eq_zero
    (x x' : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
    (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hLc : X.picardClass L hL = pointIdealClass f x' hx' - pointIdealClass f x hx)
    {n : ℕ} (i₀ : Fin n) {H : Scheme.{u}} (sH : H ⟶ Spec (CommRingCat.of k))
    (π : (∏ᶜ fun _ : Fin n => Over.mk f).left ⟶ H)
    [Morphisms.IsFiniteLocallyFreeOfRank π n.factorial]
    (hπ : π ≫ sH = (∏ᶜ fun _ : Fin n => Over.mk f).hom) (m : ℕ)
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ H)
    (hj : j ≫ sH = projectiveSpaceStructure m (Spec (CommRingCat.of k))) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π n.factorial
    haveI := hL
    pullbackPicardClass j
        (normInvertible π
          (finiteLocallyFreeNormOfRank π n.factorial n.factorial_pos).1.toMorphismNormMap
          ((modulePullback (Pi.π (fun _ : Fin n => Over.mk f) i₀).left.toLRSHom.toShHom).obj L))
        (isInvertible_normInvertible π _ _
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π _
            (Stacks.RingedSpace.modulePullback_isInvertible _ L))) = 0 :=
  pullbackPicardClass_normInvertible_eq_zero_of_curve x x' hx hx' L hL hLc π n.factorial
    n.factorial_pos m sH (Pi.π (fun _ : Fin n => Over.mk f) i₀).left
    ((Over.w (Pi.π (fun _ : Fin n => Over.mk f) i₀)).trans hπ.symm) j hj

/-- **Stacks 0FH9, last paragraph**, as triviality of the invertible module `j^*𝒩` on `ℙᵐ_k`,
under the hypotheses of `Stacks.Divisors.pullbackPicardClass_normInvertible_fibrePower_eq_zero`. -/
theorem isTrivial_pullback_normInvertible_fibrePower
    (x x' : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
    (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hLc : X.picardClass L hL = pointIdealClass f x' hx' - pointIdealClass f x hx)
    {n : ℕ} (i₀ : Fin n) {H : Scheme.{u}} (sH : H ⟶ Spec (CommRingCat.of k))
    (π : (∏ᶜ fun _ : Fin n => Over.mk f).left ⟶ H)
    [Morphisms.IsFiniteLocallyFreeOfRank π n.factorial]
    (hπ : π ≫ sH = (∏ᶜ fun _ : Fin n => Over.mk f).hom) (m : ℕ)
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ H)
    (hj : j ≫ sH = projectiveSpaceStructure m (Spec (CommRingCat.of k))) :
    IsTrivial (projectiveSpaceOverRing m (CommRingCat.of k)).presheaf
      (projectiveSpaceOverRing m (CommRingCat.of k)).ringCatIsSheaf
      ((modulePullback j.toLRSHom.toShHom).obj
        (normInvertible π
          (finiteLocallyFreeNormOfRank π n.factorial n.factorial_pos).1.toMorphismNormMap
          ((modulePullback (Pi.π (fun _ : Fin n => Over.mk f) i₀).left.toLRSHom.toShHom).obj
            L))) :=
  (pullbackPicardClass_eq_zero_iff j _ _).mp
    (pullbackPicardClass_normInvertible_fibrePower_eq_zero x x' hx hx' L hL hLc i₀ sH π hπ m j hj)

end Stacks.Divisors

end
