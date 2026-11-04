module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# The complement of the diagonal of an étale separated morphism, and its fibre degrees

Let `t : T' ⟶ T` be a separated morphism of schemes. Its diagonal
`pullback.diagonal t : T' ⟶ T' ×_T T'` is a closed immersion, so the complement of its image is an
open subscheme `AlgebraicGeometry.diagonalComplement` of `T' ×_T T'`. For `t` étale, the image of
the diagonal is also open, and if `n + 1` bounds the degrees of the fibres of `t`, then `n` bounds
the degrees of the fibres of the second projection restricted to the complement of the diagonal.
The degrees of the fibres of an étale morphism with quasi-compact source are bounded by a natural
number.

## Main definitions

* `AlgebraicGeometry.diagonalComplement`: for a separated `t : T' ⟶ T`, the open subscheme of
  `T' ×_T T'` complementary to the image of the diagonal.

## Main results

* `AlgebraicGeometry.isClopen_range_diagonal`: the image of the diagonal of an étale separated
  morphism is open and closed.
* `AlgebraicGeometry.exists_nat_boundsFiberDegrees_of_etale_of_compactSpace`: an étale morphism
  with quasi-compact source has its fibre degrees bounded by a natural number.
* `AlgebraicGeometry.boundsFiberDegrees_diagonalComplement`: if `n + 1` bounds the degrees of the
  fibres of an étale separated `t`, then `n` bounds the degrees of the fibres of the second
  projection `T' ×_T T' ⟶ T'` restricted to the complement of the diagonal.

## Implementation notes

The bound of `AlgebraicGeometry.boundsFiberDegrees_diagonalComplement` is written `n + 1` rather
than as a subtraction, so that no truncated subtraction appears.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {T' T : Scheme.{u}} (t : T' ⟶ T)

/-- The image of the diagonal of an étale separated morphism of schemes is open and closed. -/
public theorem isClopen_range_diagonal [Etale t] [IsSeparated t] :
    IsClopen (Set.range (pullback.diagonal t).base) :=
  ⟨(inferInstance : IsClosedImmersion (pullback.diagonal t)).isClosedEmbedding.isClosed_range,
    (inferInstance : IsOpenImmersion (pullback.diagonal t)).isOpen_range⟩

/-- The open subscheme of `T' ×_T T'` complementary to the image of the diagonal of a separated
morphism `t : T' ⟶ T`. -/
public noncomputable def diagonalComplement [IsSeparated t] : (pullback t t).Opens :=
  ⟨(Set.range (pullback.diagonal t).base)ᶜ, isOpen_compl_iff.mpr
    (inferInstance : IsClosedImmersion (pullback.diagonal t)).isClosedEmbedding.isClosed_range⟩

/-- The underlying set of `AlgebraicGeometry.diagonalComplement` is the complement of the image of
the diagonal. -/
public theorem coe_diagonalComplement [IsSeparated t] :
    ((diagonalComplement t : (pullback t t).Opens) : Set ↥(pullback t t))
      = (Set.range (pullback.diagonal t).base)ᶜ :=
  rfl

/-- The complement of the diagonal of an étale separated morphism is a closed subset of
`T' ×_T T'`. -/
public theorem isClosed_diagonalComplement [Etale t] [IsSeparated t] :
    IsClosed ((diagonalComplement t : (pullback t t).Opens) : Set ↥(pullback t t)) :=
  (isClopen_range_diagonal t).2.isClosed_compl

/-- An étale morphism with quasi-compact source has its fibre degrees bounded by a natural
number. -/
public theorem exists_nat_boundsFiberDegrees_of_etale_of_compactSpace {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Etale f] [CompactSpace X] : ∃ n : ℕ, BoundsFiberDegrees f (n : ℤ) := by
  obtain ⟨_, _⟩ := locallyQuasiFinite_of_etale f
  obtain ⟨m, hm⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace f
  refine ⟨m.toNat, fun y => ?_⟩
  obtain ⟨r, hr, hrank⟩ := hm y
  exact ⟨r, by omega, hrank⟩

/-- Let `t : T' ⟶ T` be an étale separated morphism of schemes whose fibre degrees are bounded
by `n + 1`. Then the fibre degrees of the second projection `T' ×_T T' ⟶ T'`, restricted to the
complement of the diagonal, are bounded by `n`. -/
public theorem boundsFiberDegrees_diagonalComplement [Etale t] [IsSeparated t] (n : ℕ)
    (h : BoundsFiberDegrees t ((n + 1 : ℕ) : ℤ)) :
    BoundsFiberDegrees ((diagonalComplement t).ι ≫ pullback.snd t t) ((n : ℕ) : ℤ) := by
  have hp : BoundsFiberDegrees (pullback.snd t t) ((n + 1 : ℕ) : ℤ) :=
    (boundsFiberDegrees_isStableUnderBaseChange ((n + 1 : ℕ) : ℤ)).of_isPullback
      (IsPullback.of_hasPullback t t) h
  have hcard := ((etale_boundsFiberDegrees_tfae (pullback.snd t t) (n + 1)).out 1 2).mp hp
  refine ((etale_boundsFiberDegrees_tfae
    ((diagonalComplement t).ι ≫ pullback.snd t t) n).out 2 1).mp ?_
  intro k _ g
  set h₁ : pullback (pullback.snd t t) g ⟶ pullback t t :=
    pullback.fst (pullback.snd t t) g with hh₁
  set R : Set ↥(pullback t t) := Set.range (pullback.diagonal t).base with hRdef
  have hAle : Cardinal.mk ↥(pullback (pullback.snd t t) g) ≤ ((n + 1 : ℕ) : Cardinal) := by
    refine le_of_eq_of_le (Cardinal.mk_congr ?_) (hcard k g)
    exact (pullbackSymmetry (pullback.snd t t) g).hom.homeomorph.toEquiv
  have hinj : Function.Injective (pullback.snd (diagonalComplement t).ι h₁).base :=
    (inferInstance :
      IsOpenImmersion (pullback.snd (diagonalComplement t).ι h₁)).base_open.injective
  have hgoal : Cardinal.mk ↥(pullback g ((diagonalComplement t).ι ≫ pullback.snd t t))
      = Cardinal.mk ↥((h₁.base ⁻¹' R)ᶜ) := by
    have e1 : pullback g ((diagonalComplement t).ι ≫ pullback.snd t t)
        ≅ pullback ((diagonalComplement t).ι ≫ pullback.snd t t) g := pullbackSymmetry _ _
    have e2 : pullback ((diagonalComplement t).ι ≫ pullback.snd t t) g
        ≅ pullback (diagonalComplement t).ι h₁ :=
      (pullbackRightPullbackFstIso (pullback.snd t t) g (diagonalComplement t).ι).symm
    have e3 : Cardinal.mk ↥(pullback (diagonalComplement t).ι h₁)
        = Cardinal.mk ↥(Set.range (pullback.snd (diagonalComplement t).ι h₁).base) :=
      (Cardinal.mk_range_eq _ hinj).symm
    have e4 : Set.range (pullback.snd (diagonalComplement t).ι h₁).base
        = (h₁.base ⁻¹' R)ᶜ := by
      rw [IsOpenImmersion.range_pullbackSnd]
      simp only [diagonalComplement, Scheme.Opens.opensRange_ι]
      rw [← Set.preimage_compl]
      rfl
    rw [Cardinal.mk_congr e1.hom.homeomorph.toEquiv,
      Cardinal.mk_congr e2.hom.homeomorph.toEquiv, e3, e4]
  rw [hgoal]
  have hne : Nonempty ↥(h₁.base ⁻¹' R) := by
    obtain ⟨x⟩ : Nonempty (Spec (.of k) : Scheme.{u}) := inferInstance
    let a : (Spec (.of k) : Scheme.{u}) ⟶ pullback (pullback.snd t t) g :=
      pullback.lift (g ≫ pullback.diagonal t) (𝟙 _) (by simp)
    have hafst : a ≫ h₁ = g ≫ pullback.diagonal t := pullback.lift_fst _ _ _
    refine ⟨⟨a.base x, ?_⟩⟩
    have hx : h₁.base (a.base x) = (pullback.diagonal t).base (g.base x) := by
      simpa using congrArg (fun m : (Spec (.of k) : Scheme.{u}) ⟶ pullback t t => m.base x) hafst
    exact ⟨g.base x, hx.symm⟩
  have hone : (1 : Cardinal) ≤ Cardinal.mk ↥(h₁.base ⁻¹' R) :=
    Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr hne)
  have hsum : Cardinal.mk ↥(h₁.base ⁻¹' R) + Cardinal.mk ↥((h₁.base ⁻¹' R)ᶜ)
      = Cardinal.mk ↥(pullback (pullback.snd t t) g) := Cardinal.mk_sum_compl _
  have hkey : (1 : Cardinal) + Cardinal.mk ↥((h₁.base ⁻¹' R)ᶜ) ≤ ((n + 1 : ℕ) : Cardinal) := by
    exact (add_le_add hone le_rfl).trans (hsum ▸ hAle)
  have hlt : Cardinal.mk ↥((h₁.base ⁻¹' R)ᶜ) < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_trans (self_le_add_left _ 1) hkey) (Cardinal.lt_aleph0.2 ⟨n + 1, rfl⟩)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at hkey ⊢
  have hmn : (1 : ℕ) + m ≤ n + 1 := by exact_mod_cast hkey
  exact_mod_cast (show m ≤ n by omega)

end AlgebraicGeometry

end
