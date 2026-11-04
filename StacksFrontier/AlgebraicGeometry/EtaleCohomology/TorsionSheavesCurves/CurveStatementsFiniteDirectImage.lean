module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageRestriction

/-!
# The bundled statements of Situation 0A52 pass to a finite direct image

Lemma 0A5D: for a finite morphism `f : X ⟶ Y` of separated finite type schemes of dimension at
most one over an algebraically closed field and a torsion abelian sheaf `F` on `X`, if statements
(1) -- (8) of Situation 0A52 hold for `F`, they hold for `f_* F`. The source proves it from
`H^q(X, F) = H^q(Y, f_* F)` (Tags 03QP and 0733) and, for (6), (7) and (8), from the
compatibility of `f_*` with base change (Tag 0959).

This file proves the lemma for a constructible `F` killed by a prime `ℓ`, which is the case in
which the proof of Theorem 03SC applies it (Lemmas 0A3Q and 03SD). For such `F` the torsion side
conditions of statements (3), (4) and (6) need no transfer from `f_* F` to `F`: either `F` itself
satisfies them, or `f_* F` is killed by `ℓ` and also of torsion coprime to `ℓ`, hence zero.

## Main results

* `Stacks.EtaleCohomology.CurveStatements.directImage_of_nsmul_eq_zero`.

## Implementation notes

The identification of cohomology is
`Stacks.EtaleCohomology.etaleCohomologyDirectImageMap_bijective` and the restriction maps are moved
by `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_iff` and its
surjective companion, applied to the squares formed by the scalar extensions of `X` and `Y` and by
an open `U ⊆ Y` and its inverse image, whose base change comparisons are invertible by
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback`. The coefficients
are `AddCommGrpCat.{u + 1}`, where that base change is available, and the `Ext`-universe is
`u + 1`, in which every category of abelian sheaves on a small étale site has its `Ext`-groups:
statements (6) and (7) for `f_* F` are about the scalar extension of `Y`, and to compare them with
those for `F` the `Ext`-groups over the scalar extension of `X` must exist too.

## References

* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- `Ext` of abelian sheaves on a small étale site at the coefficients `AddCommGrpCat.{u + 1}`
lives in the universe `u + 1`. -/
theorem hasExt_sheaf_smallEtale_succ (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have : IsGrothendieckAbelian.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse S
  IsGrothendieckAbelian.hasExt _

attribute [local instance] hasExt_sheaf_smallEtale_succ

section Torsion

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{u + 1}}

omit [Category C] in
private theorem nsmul_section_eq_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F : Sheaf J AddCommGrpCat.{u + 1}} {n : ℕ} (hF : n • 𝟙 F = 0) (U : Cᵒᵖ)
    (x : F.obj.obj U) : n • x = 0 := by
  have h := congrArg (fun φ : F ⟶ F ↦ ((sheafToPresheaf J _).map φ).app U) hF
  simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero,
    NatTrans.app_nsmul, NatTrans.id_app, NatTrans.app_zero] at h
  have h' := congrArg (fun φ ↦ φ x) h
  simpa using h'

/-- An abelian sheaf killed by `ℓ > 0` is `ℓ`-power torsion. -/
theorem isPrimePowerTorsion_of_nsmul_eq_zero {ℓ : ℕ} (hF : ℓ • 𝟙 F = 0) :
    Stacks.Torsion.IsPrimePowerTorsion J ℓ F := fun U x ↦
  ⟨⊤, J.top_mem U, fun V f _ ↦ ⟨1, Nat.one_pos, by
    rw [pow_one]; exact nsmul_section_eq_zero hF _ _⟩⟩

/-- An abelian sheaf killed by a positive `ℓ` coprime to `p` is of torsion prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_of_nsmul_eq_zero {ℓ p : ℕ} (hℓ : 0 < ℓ)
    (hcop : ℓ.Coprime p) (hF : ℓ • 𝟙 F = 0) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J p F := fun U _ ↦
  ⟨⊤, J.top_mem U, fun _ _ _ ↦ ⟨ℓ, hℓ, hcop, nsmul_section_eq_zero hF _ _⟩⟩

end Torsion

/-- Étale cohomology of a zero sheaf vanishes. -/
theorem subsingleton_sheafH_of_isZero {S : Scheme.{u}} {G : Sheaf S.smallEtaleTopology
    AddCommGrpCat.{u + 1}} (hG : IsZero G) (q : ℕ) : Subsingleton (Sheaf.H.{u + 1} G q) :=
  ⟨fun x y ↦ by
    rw [← Ext.comp_mk₀_id x, ← Ext.comp_mk₀_id y, hG.eq_of_src (𝟙 G) 0, Ext.mk₀_zero,
      Ext.comp_zero, Ext.comp_zero]⟩

/-- Restriction is bijective on the cohomology of a zero sheaf. -/
theorem bijective_etaleCohomologyRestrictionMap_of_isZero {S T : Scheme.{u}} (i : T ⟶ S)
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (hG : IsZero G) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i G q) := by
  have := subsingleton_sheafH_of_isZero hG q
  have := subsingleton_sheafH_of_isZero
    ((etaleAbelianInverseImage.{u, 0} i).map_isZero hG) q
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The scalar extension of `X` along `k'/k` is the base change of the scalar extension of `Y`
along `f : X ⟶ Y`. -/
theorem isPullback_scalarExtension {k : Type u} [Field k] (k' : Type u) [Field k']
    [Algebra k k'] {X Y : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ Spec (.of k)) :
    IsPullback (scalarExtensionFst k k' (f ≫ π))
      (pullback.map (f ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap k k'))) π
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f (𝟙 _) (𝟙 _) (by simp) (by simp))
      f (scalarExtensionFst k k' π) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd π _) (h₂₂ := π)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k k'))) ?_ (by simp) ?_).flip
  · simpa using (IsPullback.of_hasPullback (f ≫ π)
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).flip
  · exact (IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom (algebraMap k k')))).flip

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f]

/-- In a cartesian square with `f` finite, `f'` is finite and the base change comparison is
invertible. -/
private theorem isFinite_and_isIso_baseChange_of_isPullback {X' Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) :
    IsFinite f' ∧ IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) :=
  have : IsFinite f' := MorphismProperty.of_isPullback sq ‹IsFinite f›
  ⟨this, isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback f g g' f' sq⟩

/-- Restriction along `g` on the cohomology of `f_* F` is bijective iff restriction along `g'` on
the cohomology of `F` is, for a cartesian square with `f` finite. -/
private theorem bijective_iff_of_isPullback {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g' F q) := by
  obtain ⟨_, _⟩ := isFinite_and_isIso_baseChange_of_isPullback f sq
  exact bijective_etaleCohomologyRestrictionMap_directImage_iff.{u, 0, u + 1} f g g' f' sq.w F q

/-- The surjective form of `bijective_iff_of_isPullback`. -/
private theorem surjective_iff_of_isPullback {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} g' F q) := by
  obtain ⟨_, _⟩ := isFinite_and_isIso_baseChange_of_isPullback f sq
  exact surjective_etaleCohomologyRestrictionMap_directImage_iff.{u, 0, u + 1} f g g' f' sq.w F q

/-- For a prime `ℓ`, either `ℓ` is prime to the exponential characteristic of `k`, or every
sheaf killed by `ℓ` and of torsion prime to the characteristic is zero. -/
theorem coprime_ringExpChar_or_isZero (k : Type u) [Field k] {S : Scheme.{u}} {ℓ : ℕ}
    (hℓ : ℓ.Prime) :
    ℓ.Coprime (ringExpChar k) ∨ ∀ G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
      ℓ • 𝟙 G = 0 → Stacks.Torsion.IsPrimeToCharacteristicTorsion S.smallEtaleTopology
        (ringExpChar k) G → IsZero G := by
  rcases expChar_is_prime_or_one k (ringExpChar k) with hp | h1
  · by_cases hℓp : ℓ = ringExpChar k
    · refine Or.inr fun G hG ht ↦ ?_
      rw [hℓp] at hG
      exact isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion
        (isPrimePowerTorsion_of_nsmul_eq_zero hG) ht
    · exact Or.inl ((Nat.coprime_primes hℓ hp).mpr hℓp)
  · exact Or.inl (h1 ▸ Nat.coprime_one_right ℓ)

/-- **Lemma 0A5D for a constructible sheaf killed by a prime.** Let `f : X ⟶ Y` be a finite
morphism of schemes over a field `k`, and `F` an abelian sheaf on `X_étale` which is constructible
and killed by a prime `ℓ`. If statements (1) -- (8) of Situation 0A52 hold for `F`, they hold for
`f_* F`. -/
theorem CurveStatements.directImage_of_nsmul_eq_zero
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓF : ℓ • 𝟙 F = 0)
    (hc : ∀ (B : BigEtaleSite.{u}) (hX : B.Contains X)
      [∀ (T T' : B.Scheme) (f : T' ⟶ T),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
          (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
      [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
        HasWeakSheafify
          ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{u + 1}],
      IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F)
    (h : CurveStatements.{u, 0, u + 1} (f ≫ π) F) :
    CurveStatements.{u, 0, u + 1} π ((etaleAbelianDirectImage.{u, 0} f).obj F) := by
  have hℓG : ℓ • 𝟙 ((etaleAbelianDirectImage.{u, 0} f).obj F) = 0 := by
    simpa using congrArg (etaleAbelianDirectImage.{u, 0} f).map hℓF
  have hinj := fun q ↦ (etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} f F q).1
  have hsub : ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} f).obj F) q) :=
    fun q hq ↦ (hinj q).subsingleton
  have hfin : ∀ q, Finite (Sheaf.H.{u + 1} F q) →
      Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} f).obj F) q) :=
    fun q hq ↦ Finite.of_injective _ (hinj q)
  let B' := BigEtaleSite.containing X
  have hX' : B'.Contains X := BigEtaleSite.contains_containing X
  have i₁ : ∀ (T T' : B'.Scheme) (f : T' ⟶ T),
      ((AlgebraicGeometry.smallEtaleBaseChange B' f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (AlgebraicGeometry.SmallEtale.topology B' T.obj T.property)
        (AlgebraicGeometry.SmallEtale.topology B' T'.obj T'.property)).IsRightAdjoint :=
    fun _ _ _ ↦ inferInstance
  have i₂ : ∀ (T : B'.Scheme) (V : AlgebraicGeometry.SmallEtale B' T.obj T.property),
      HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B' T.obj T.property).over V)
        AddCommGrpCat.{u + 1} :=
    fun _ _ ↦ inferInstance
  have hcF := hc B' hX'
  refine
    { vanishing := fun q hq ↦ hsub q (h.vanishing q hq)
      affineVanishing := fun hY q hq ↦ by
        have : IsAffine Y := hY
        exact hsub q (h.affineVanishing (isAffine_of_isAffineHom f) q hq)
      primePowerVanishing := fun p _ hp htor q hq ↦ by
        by_cases hℓp : ℓ = p
        · subst hℓp
          exact hsub q (h.primePowerVanishing ℓ hp
            (isPrimePowerTorsion_of_nsmul_eq_zero hℓF) q hq)
        · have hpp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp.ne'
          exact subsingleton_sheafH_of_isZero
            (isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion htor
              (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos
                ((Nat.coprime_primes hℓ hpp).mpr hℓp) hℓG)) q
      finite_of_isPrimeToCharacteristicTorsion := fun B hY _ _ _ htor q ↦ by
        rcases coprime_ringExpChar_or_isZero k (S := Y) hℓ with hcop | hz
        · exact hfin q (h.finite_of_isPrimeToCharacteristicTorsion B' hX' hcF
            (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos hcop hℓF) q)
        · have := subsingleton_sheafH_of_isZero (hz _ hℓG htor) q
          exact Finite.of_subsingleton
      finite_of_isProper := fun B hY _ _ hπ _ q ↦ by
        have : IsProper π := hπ
        exact hfin q (h.finite_of_isProper B' hX' inferInstance hcF q)
      bijective_of_isPrimeToCharacteristicTorsion := fun htor k' _ _ _ _ _ q ↦ by
        rcases coprime_ringExpChar_or_isZero k (S := Y) hℓ with hcop | hz
        · exact (bijective_iff_of_isPullback f (isPullback_scalarExtension k' f π) F q).mpr
            (h.bijective_of_isPrimeToCharacteristicTorsion
              (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos hcop hℓF) k' q)
        · exact bijective_etaleCohomologyRestrictionMap_of_isZero _ (hz _ hℓG htor) q
      bijective_of_isProper := fun hπ k' _ _ _ _ _ q ↦ by
        have : IsProper π := hπ
        exact (bijective_iff_of_isPullback f (isPullback_scalarExtension k' f π) F q).mpr
          (h.bijective_of_isProper inferInstance k' q)
      surjective := fun U _ ↦
        (surjective_iff_of_isPullback f (isPullback_morphismRestrict f U).flip F 2).mpr
          (h.surjective (f ⁻¹ᵁ U)) }

end Stacks.EtaleCohomology

end
