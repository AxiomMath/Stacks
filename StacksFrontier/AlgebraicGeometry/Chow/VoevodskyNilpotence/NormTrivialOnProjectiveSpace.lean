module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.BaseChange
public import StacksFrontier.AlgebraicGeometry.NormInvertible.WellDefined
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceRigidity
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange

/-!
# The norm sheaf of Stacks 0FH9 is trivial on projective spaces

The last paragraph of the proof of Stacks 0FH9 shows that `𝒩 = Norm_π(ℒ₁)` on `Sⁿ(X)` is trivial
on a fibre `F ≅ ℙᵐ_k` of `Sⁿ(X) ⟶ Pic^n_{X/k}`. The argument is a family argument: there is a
connected base `T` with two `k`-points `p`, `q` and an invertible module `ℒ'` on `T × Xⁿ` whose
fibre over `p` is trivial and whose fibre over `q` is `ℒ₁`; then `𝒩' = Norm_{id_T × π}(ℒ')` on
`T × Sⁿ(X)` has fibre `𝒪` over `p` and fibre `𝒩` over `q`, because the norm commutes with base
change, and its restriction to `T × ℙᵐ` is an invertible module whose fibre over `p` is trivial.
The source concludes with Euler characteristics (Stacks 0B9T and 01XT).

This file proves the conclusion, for every morphism `j : ℙᵐ_k ⟶ Sⁿ(X)` over `k`, in the
generality the argument has: for **any** finite locally free `π : P ⟶ Q` of constant rank
`d > 0` and **any** family of invertible modules over a base `T = Spec A` with `A` a unique
factorization domain. In place of Euler characteristics it uses the rigidity of Picard groups
of projective space over a unique factorization domain
(`Stacks.PicardUFD.injective_pullbackPicardHom_projectiveSpaceOverMap`, from Stacks 0BXJ):
an invertible module on `ℙᵐ_A` trivial over `p` is trivial on `ℙᵐ_A`, hence over `q`. For the
curve case of 0FH9 the base can be taken to be the spectrum of the semilocal ring of `X` at the
two points `x, x'`, a semilocal Dedekind domain and so a principal ideal domain.

## Main results

* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_family`: **the abstract form.**
  A finite locally free `π' : P' ⟶ Q'` of rank `d`, two cartesian squares exhibiting `π` as its
  base change along `i_p, i_q : Q ⟶ Q'`, a morphism `J : ℙᵐ_A ⟶ Q'` restricting to `j` over `p`
  and over `q`, and an invertible `ℒ'` on `P'` with `i'_p^*ℒ'` trivial and `i'_q^*ℒ' ≅ ℒ` give
  `j^*(Norm_π ℒ) ≅ 𝒪`.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily`: **the form
  of the source**, with the family over `T × Q`, `T = Spec A ⟶ Spec k`, built here, and the only
  inputs `ℒ'` on `(T × Q) ×_Q P` together with its two fibres. Here `j : ℙᵐ_k ⟶ Q` is any morphism
  over `k`.
* `Stacks.Divisors.isTrivial_pullback_normInvertible_of_baseChangeFamily`: the same, as
  triviality of the module `j^*𝒩`.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_iso_projectiveSpace` and
  `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_projModel`: the same for any
  scheme `F` identified with `ℙᵐ_k` over `k`, in particular for `F = Proj k[T₀, …, Tₘ]`; this is
  the form in which a fibre `F ≅ ℙᵐ_k` of a projective bundle consumes it.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.Divisors

variable {P Q : Scheme.{u}}

/-- The Picard class of the canonical norm, `[Norm_π ℒ] ∈ Pic(Q)`, for `π` finite locally free
of rank `d > 0` and `ℒ` invertible. -/
abbrev normPicardClass (π : P ⟶ Q) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d]
    (hd : 0 < d) (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L) :
    Q.picardGroup :=
  haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  Q.picardClass (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
    (isInvertible_normInvertible π _ L
      (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL))

/-- The class of the canonical norm depends only on the class of the module. -/
theorem normPicardClass_congr (π : P ⟶ Q) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d]
    (hd : 0 < d) (L M : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hM : IsInvertible P.presheaf P.ringCatIsSheaf M)
    (h : P.picardClass L hL = P.picardClass M hM) :
    normPicardClass π d hd L hL = normPicardClass π d hd M hM := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  obtain ⟨e⟩ := (P.picardClass_eq_iff L M hL hM).mp h
  exact picardClass_normInvertible_congr π (finiteLocallyFreeNormOfRank π d hd).1 e
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible π M hM)

/-- The class of the canonical norm of a trivial module vanishes. -/
theorem normPicardClass_eq_zero (π : P ⟶ Q) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d]
    (hd : 0 < d) (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (h : P.picardClass L hL = 0) : normPicardClass π d hd L hL = 0 := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  exact picardClass_normInvertible_eq_zero π (finiteLocallyFreeNormOfRank π d hd).1 L hL h

/-- The fibre of the norm of a family: pulling `[Norm_{π'} ℒ']` back along `i` is the class of the
norm of the pullback of `ℒ'`, when `π` is the base change of `π'` along `i`. -/
theorem pullbackPicardHom_normPicardClass {P' Q' : Scheme.{u}} (π : P ⟶ Q) (π' : P' ⟶ Q')
    (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d] [Morphisms.IsFiniteLocallyFreeOfRank π' d]
    (hd : 0 < d) (i : Q ⟶ Q') (i' : P ⟶ P') (sq : IsPullback i' π π' i) (L' : P'.Modules)
    (hL' : IsInvertible P'.presheaf P'.ringCatIsSheaf L') :
    pullbackPicardHom i (normPicardClass π' d hd L' hL') =
      normPicardClass π d hd ((modulePullback i'.toLRSHom.toShHom).obj L')
        (by have := hL'; exact Stacks.RingedSpace.modulePullback_isInvertible _ L') :=
  (pullbackPicardHom_picardClass i _ _).trans
    (pullbackPicardClass_normInvertible_baseChange π' π i' i d hd sq L' hL')

variable {A B : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]

/-- **The norm sheaf is trivial on projective space, abstract form.** Let `π : P ⟶ Q` and
`π' : P' ⟶ Q'` be finite locally free of rank `d > 0`, and let `π` be the base change of `π'`
along two morphisms `i_p, i_q : Q ⟶ Q'` (the fibres of a family over two points). Let
`r : Spec A ⟶ Spec B` have the section `p`, with `A`, `B` unique factorization domains, let `q`
be another morphism `Spec B ⟶ Spec A`, and let `J : ℙᵐ_A ⟶ Q'` restrict to `j : ℙᵐ_B ⟶ Q`
over `p` and over `q`. If `ℒ'` is invertible on `P'` with `i'_p^*ℒ'` trivial and `i'_q^*ℒ' ≅ ℒ`,
then `j^*(Norm_π ℒ)` is trivial. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_family {P' Q' : Scheme.{u}}
    (π : P ⟶ Q) (π' : P' ⟶ Q') (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank π d]
    [Morphisms.IsFiniteLocallyFreeOfRank π' d] (hd : 0 < d) (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (p q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (ip iq : Q ⟶ Q') (ip' iq' : P ⟶ P') (sqp : IsPullback ip' π π' ip)
    (sqq : IsPullback iq' π π' iq)
    (j : projectiveSpaceOverRing m (CommRingCat.of B) ⟶ Q)
    (J : projectiveSpaceOverRing m (CommRingCat.of A) ⟶ Q')
    (hJp : projectiveSpaceOverMap m p ≫ J = j ≫ ip)
    (hJq : projectiveSpaceOverMap m q ≫ J = j ≫ iq)
    (L' : P'.Modules) (hL' : IsInvertible P'.presheaf P'.ringCatIsSheaf L')
    (hpL' : pullbackPicardClass ip' L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass iq' L' hL' = P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  have hinv : ∀ i' : P ⟶ P', IsInvertible P.presheaf P.ringCatIsSheaf
      ((modulePullback i'.toLRSHom.toShHom).obj L') := fun i' => by
    have := hL'; exact Stacks.RingedSpace.modulePullback_isInvertible _ L'
  let x := pullbackPicardHom J (normPicardClass π' d hd L' hL')
  -- the restriction of `x` over a point `t` is `j^*` of the norm of the fibre of `ℒ'`
  have hfib : ∀ (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (it : Q ⟶ Q')
      (it' : P ⟶ P') (sq : IsPullback it' π π' it)
      (_ : projectiveSpaceOverMap m t ≫ J = j ≫ it),
      pullbackPicardHom (projectiveSpaceOverMap m t) x =
        pullbackPicardHom j (normPicardClass π d hd _ (hinv it')) := by
    intro t it it' sq ht
    rw [← pullbackPicardHom_comp_apply, ht, pullbackPicardHom_comp_apply,
      pullbackPicardHom_normPicardClass π π' d hd it it' sq L' hL']
  have hp0 : pullbackPicardHom (projectiveSpaceOverMap m p) x = 0 := by
    rw [hfib p ip ip' sqp hJp, normPicardClass_eq_zero π d hd _ _ hpL', map_zero]
  have hx : x = 0 :=
    Stacks.PicardUFD.eq_zero_of_pullbackPicardHom_projectiveSpaceOverMap_eq_zero m r p hp x hp0
  have hq0 := hfib q iq iq' sqq hJq
  rw [hx, map_zero, normPicardClass_congr π d hd _ L _ hL hqL'] at hq0
  exact (pullbackPicardHom_picardClass j _ _).symm.trans hq0.symm

section BaseChangeFamily

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The fibre `Q ⟶ T ×_S Q` of the product family over a section `t` of `r : T ⟶ S`. -/
def fibreInclusion {T S : Scheme.{u}} (r : T ⟶ S) (sQ : Q ⟶ S) (t : S ⟶ T) (ht : t ≫ r = 𝟙 S) :
    Q ⟶ pullback r sQ :=
  pullback.lift (sQ ≫ t) (𝟙 Q) (by rw [Category.assoc, ht, Category.comp_id, Category.id_comp])

/-- The fibre inclusion `Q ⟶ T ×_S Q` over a section `t` is a section of the second projection
`T ×_S Q ⟶ Q`. -/
@[reassoc (attr := simp)]
theorem fibreInclusion_snd {T S : Scheme.{u}} (r : T ⟶ S) (sQ : Q ⟶ S) (t : S ⟶ T)
    (ht : t ≫ r = 𝟙 S) : fibreInclusion r sQ t ht ≫ pullback.snd r sQ = 𝟙 Q :=
  pullback.lift_snd _ _ _

/-- The fibre `P ⟶ (T ×_S Q) ×_Q P` of the base-changed source over a section. -/
def sourceFibreInclusion {T S : Scheme.{u}} (r : T ⟶ S) (sQ : Q ⟶ S) (π : P ⟶ Q) (t : S ⟶ T)
    (ht : t ≫ r = 𝟙 S) : P ⟶ pullback (pullback.snd r sQ) π :=
  pullback.lift (π ≫ fibreInclusion r sQ t ht) (𝟙 P) (by simp)

/-- The source fibre and the target fibre form a cartesian square over `π`. -/
theorem isPullback_sourceFibreInclusion {T S : Scheme.{u}} (r : T ⟶ S) (sQ : Q ⟶ S)
    (π : P ⟶ Q) (t : S ⟶ T) (ht : t ≫ r = 𝟙 S) :
    IsPullback (sourceFibreInclusion r sQ π t ht) π
      (pullback.fst (pullback.snd r sQ) π) (fibreInclusion r sQ t ht) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (pullback.snd r sQ) π).flip
  rw [sourceFibreInclusion, pullback.lift_snd, fibreInclusion_snd]
  exact IsPullback.id_horiz π

variable {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- The structure morphism `ℙᵐ_S ⟶ S` of the base-change model of projective space. -/
abbrev projectiveSpaceStructure (m : ℕ) (S : Scheme.{u}) : projectiveSpaceOver m S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} m))

/-- The morphism `ℙᵐ_T ⟶ T ×_S Q` induced by a morphism `j : ℙᵐ_S ⟶ Q` over `S`: the structure
morphism on the first factor, `j` after the projection `ℙᵐ_T ⟶ ℙᵐ_S` on the second. -/
def familyMorphism (m : ℕ) {T S : Scheme.{u}} (r : T ⟶ S) (sQ : Q ⟶ S)
    (j : projectiveSpaceOver m S ⟶ Q) (hj : j ≫ sQ = projectiveSpaceStructure m S) :
    projectiveSpaceOver m T ⟶ pullback r sQ :=
  pullback.lift (projectiveSpaceStructure m T) (projectiveSpaceOverMap m r ≫ j) (by
    rw [Category.assoc, hj, projectiveSpaceOverMap_fst])

/-- The restriction of `familyMorphism m r sQ j hj` along the fibre `ℙᵐ_S ⟶ ℙᵐ_T` over a section
`t` of `r` is `j` followed by `fibreInclusion r sQ t ht`. -/
theorem projectiveSpaceOverMap_comp_familyMorphism (m : ℕ) {T S : Scheme.{u}} (r : T ⟶ S)
    (sQ : Q ⟶ S) (j : projectiveSpaceOver m S ⟶ Q)
    (hj : j ≫ sQ = projectiveSpaceStructure m S) (t : S ⟶ T) (ht : t ≫ r = 𝟙 S) :
    projectiveSpaceOverMap m t ≫ familyMorphism m r sQ j hj = j ≫ fibreInclusion r sQ t ht := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, familyMorphism, pullback.lift_fst, projectiveSpaceOverMap_fst,
      Category.assoc, fibreInclusion, pullback.lift_fst, ← Category.assoc, hj]
  · rw [Category.assoc, familyMorphism, pullback.lift_snd, ← Category.assoc,
      projectiveSpaceOverMap_comp, ht, projectiveSpaceOverMap_id, Category.id_comp,
      Category.assoc, fibreInclusion_snd, Category.comp_id]

/-- **The norm sheaf is trivial on projective space, in the form of the source.** Let
`π : P ⟶ Q` be finite locally free of rank `d > 0` over `k` (structure morphism `sQ`), and let
`T = Spec A ⟶ Spec k` be a base with two `k`-points `p` and `q`, `A` a unique factorization
domain. Let `ℒ'` be an invertible module on `(T ×_k Q) ×_Q P = T ×_k P` whose fibre over `p` is
trivial and whose fibre over `q` is `ℒ`. Then for every `m` and every morphism `j : ℙᵐ_k ⟶ Q`
over `k`, `j^*(Norm_π ℒ)` is trivial. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily (π : P ⟶ Q) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (hq : q ≫ r = 𝟙 _) (sQ : Q ⟶ Spec (CommRingCat.of k))
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ Q)
    (hj : j ≫ sQ = projectiveSpaceStructure m (Spec (CommRingCat.of k)))
    (L' : (pullback (pullback.snd r sQ) π).Modules)
    (hL' : IsInvertible (pullback (pullback.snd r sQ) π).presheaf
      (pullback (pullback.snd r sQ) π).ringCatIsSheaf L')
    (hpL' : pullbackPicardClass (sourceFibreInclusion r sQ π p hp) L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass (sourceFibreInclusion r sQ π q hq) L' hL' =
      P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 := by
  have : Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst (pullback.snd r sQ) π) d :=
    Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd r sQ) π).flip
  exact pullbackPicardClass_normInvertible_eq_zero_of_family π
    (pullback.fst (pullback.snd r sQ) π) d hd m r p q hp
    (fibreInclusion r sQ p hp) (fibreInclusion r sQ q hq)
    (sourceFibreInclusion r sQ π p hp) (sourceFibreInclusion r sQ π q hq)
    (isPullback_sourceFibreInclusion r sQ π p hp) (isPullback_sourceFibreInclusion r sQ π q hq)
    j (familyMorphism m r sQ j hj)
    (projectiveSpaceOverMap_comp_familyMorphism m r sQ j hj p hp)
    (projectiveSpaceOverMap_comp_familyMorphism m r sQ j hj q hq) L' hL' hpL' L hL hqL'

/-- **The norm sheaf is trivial on projective space**, as triviality of the invertible module
`j^*(Norm_π ℒ)`, under the hypotheses of
`Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily`. -/
theorem isTrivial_pullback_normInvertible_of_baseChangeFamily (π : P ⟶ Q) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (hq : q ≫ r = 𝟙 _) (sQ : Q ⟶ Spec (CommRingCat.of k))
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶ Q)
    (hj : j ≫ sQ = projectiveSpaceStructure m (Spec (CommRingCat.of k)))
    (L' : (pullback (pullback.snd r sQ) π).Modules)
    (hL' : IsInvertible (pullback (pullback.snd r sQ) π).presheaf
      (pullback (pullback.snd r sQ) π).ringCatIsSheaf L')
    (hpL' : pullbackPicardClass (sourceFibreInclusion r sQ π p hp) L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass (sourceFibreInclusion r sQ π q hq) L' hL' =
      P.picardClass L hL) :
    IsTrivial (projectiveSpaceOverRing m (CommRingCat.of k)).presheaf
      (projectiveSpaceOverRing m (CommRingCat.of k)).ringCatIsSheaf
      ((modulePullback j.toLRSHom.toShHom).obj
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)) :=
  (pullbackPicardClass_eq_zero_iff j _ _).mp
    (pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily π d hd m r p q hp hq sQ j
      hj L' hL' hpL' L hL hqL')

/-- **The norm sheaf is trivial on any scheme identified with `ℙᵐ_k` over `k`**, e.g. a fibre
of a projective bundle: if `e : F ≅ ℙᵐ_k` and `j : F ⟶ Q` lies over `k` through `e`, then
`j^*(Norm_π ℒ)` is trivial, under the hypotheses of
`Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily`. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_iso_projectiveSpace (π : P ⟶ Q) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (hq : q ≫ r = 𝟙 _) (sQ : Q ⟶ Spec (CommRingCat.of k)) {F : Scheme.{u}}
    (e : F ≅ projectiveSpaceOverRing m (CommRingCat.of k)) (j : F ⟶ Q)
    (hj : j ≫ sQ = e.hom ≫ projectiveSpaceStructure m (Spec (CommRingCat.of k)))
    (L' : (pullback (pullback.snd r sQ) π).Modules)
    (hL' : IsInvertible (pullback (pullback.snd r sQ) π).presheaf
      (pullback (pullback.snd r sQ) π).ringCatIsSheaf L')
    (hpL' : pullbackPicardClass (sourceFibreInclusion r sQ π p hp) L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass (sourceFibreInclusion r sQ π q hq) L' hL' =
      P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  have hj' : (e.inv ≫ j) ≫ sQ = projectiveSpaceStructure m (Spec (CommRingCat.of k)) := by
    rw [Category.assoc, hj, Iso.inv_hom_id_assoc]
  have h0 := pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily π d hd m r p q hp hq
    sQ (e.inv ≫ j) hj' L' hL' hpL' L hL hqL'
  have h1 : pullbackPicardHom (e.hom ≫ e.inv ≫ j) (normPicardClass π d hd L hL) = 0 :=
    (pullbackPicardHom_comp_apply e.hom (e.inv ≫ j) _).trans
      ((congrArg (pullbackPicardHom e.hom)
        ((pullbackPicardHom_picardClass (e.inv ≫ j) _ _).trans h0)).trans (map_zero _))
  rw [Iso.hom_inv_id_assoc] at h1
  exact (pullbackPicardHom_picardClass j _ _).symm.trans h1

/-- **The norm sheaf is trivial on `Proj k[T₀, …, Tₘ]`** mapping to `Q` over `k`, under the
hypotheses of `Stacks.Divisors.pullbackPicardClass_normInvertible_eq_zero_of_baseChangeFamily`.
This is the model of projective space in which Stacks 0BXJ is stated. -/
theorem pullbackPicardClass_normInvertible_eq_zero_of_projModel (π : P ⟶ Q) (d : ℕ)
    [Morphisms.IsFiniteLocallyFreeOfRank π d] (hd : 0 < d) (m : ℕ)
    (r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) (hp : p ≫ r = 𝟙 _)
    (hq : q ≫ r = 𝟙 _) (sQ : Q ⟶ Spec (CommRingCat.of k))
    (j : AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading k m) ⟶ Q)
    (hj : j ≫ sQ = Stacks.ProjectiveCohomology.projModelToSpec k m)
    (L' : (pullback (pullback.snd r sQ) π).Modules)
    (hL' : IsInvertible (pullback (pullback.snd r sQ) π).presheaf
      (pullback (pullback.snd r sQ) π).ringCatIsSheaf L')
    (hpL' : pullbackPicardClass (sourceFibreInclusion r sQ π p hp) L' hL' = 0)
    (L : P.Modules) (hL : IsInvertible P.presheaf P.ringCatIsSheaf L)
    (hqL' : pullbackPicardClass (sourceFibreInclusion r sQ π q hq) L' hL' =
      P.picardClass L hL) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    pullbackPicardClass j
        (normInvertible π (finiteLocallyFreeNormOfRank π d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible π _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible π L hL)) = 0 :=
  pullbackPicardClass_normInvertible_eq_zero_of_iso_projectiveSpace π d hd m r p q hp hq sQ
    (Stacks.ProjectiveCohomology.projModelIso k m) j
    (hj.trans (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k m).symm)
    L' hL' hpL' L hL hqL'

end BaseChangeFamily

end Stacks.Divisors

end
