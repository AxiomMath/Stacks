module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal

/-!
# The blowup square and the exceptional divisor under flat base change

Let `i : Z ⟶ X` be a closed immersion, let `ε : X₁ ⟶ X` be flat and let `i₁ : Z₁ ⟶ X₁` be the
base change of `i` along `ε`. Write `b : X' ⟶ X` and `b₁ : X₁' ⟶ X₁` for the blowups of `X` and
`X₁` along the two centres (in the construction `Stacks.Blowup.blowUp`), `j : E ⟶ X'` and
`j₁ : E₁ ⟶ X₁'` for their exceptional divisors and `p : E ⟶ Z`, `p₁ : E₁ ⟶ Z₁` for the
projections of the exceptional divisors onto the centres. Blowing up commutes with flat base
change ([Stacks, Tag 0805]), so `X₁' = X' ×_X X₁`; this file records that, and that the
exceptional divisor then base changes too:

* `E₁ = E ×_{X'} X₁'`, the square of the two inclusions of exceptional divisors, and
* `E₁ = E ×_Z Z₁`, the square of the two projections onto the centres.

## Main results

* `Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback`: **[Stacks, Tag 0805] for
  `Stacks.Blowup.blowUp`**, read at a cartesian square of closed immersions.
* `Stacks.Blowup.exists_isPullback_exceptionalDivisor`: the two cartesian squares of the
  exceptional divisors.
* `Stacks.Blowup.quasiCompact_blowUpToBase_of_fg`: the blowup morphism of a quasi-coherent ideal
  sheaf of finite type is quasi-compact.

## Implementation notes

[Stacks, Tag 0805] is proved as `AlgebraicGeometry.exists_isPullback_blowUpToBase_comap` for the
other construction of the blowup, `AlgebraicGeometry.blowUp`; it is carried across the
comparison isomorphism `AlgebraicGeometry.blowUpIso`, which is an isomorphism over `X`. The two
exceptional squares are obtained by pasting cartesian squares: the exceptional divisor is the
fibre product of the blowup with the centre (`Stacks.Blowup.isPullback_exceptionalToCentre`).

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.Blowup

variable {X X₁ Z Z₁ : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {ε : X₁ ⟶ X}
  {δ : Z₁ ⟶ Z} {i₁ : Z₁ ⟶ X₁} [IsClosedImmersion i₁]

/-- **Blowing up commutes with flat base change**, for `Stacks.Blowup.blowUp` and an ideal sheaf
on `X₁` equal to the inverse image of one on `X`. -/
theorem exists_isPullback_blowUpToBase_of_eq_comap [Flat ε] (I : X.IdealSheafData)
    (J : X₁.IdealSheafData) (hJ : I.comap ε = J) :
    ∃ ε' : blowUp J ⟶ blowUp I, IsPullback ε' (blowUpToBase J) (blowUpToBase I) ε := by
  subst hJ
  obtain ⟨h, hpb⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap ε I
  refine ⟨(AlgebraicGeometry.blowUpIso (I.comap ε)).inv ≫ h ≫ (AlgebraicGeometry.blowUpIso I).hom,
    hpb.flip.of_iso (AlgebraicGeometry.blowUpIso (I.comap ε)) (AlgebraicGeometry.blowUpIso I)
      (Iso.refl _) (Iso.refl _) (by simp) ?_ ?_ (by simp)⟩
  all_goals simp [AlgebraicGeometry.blowUpIso_hom_blowUpToBase]

omit [IsClosedImmersion i₁] in
/-- **[Stacks, Tag 0805] for `Stacks.Blowup.blowUp`, at a cartesian square of closed
immersions.** If `i₁` is the base change of the closed immersion `i` along the flat morphism
`ε`, the blowup of `X₁` along `Z₁` is the base change along `ε` of the blowup of `X` along `Z`. -/
theorem exists_isPullback_blowUpToBase_of_isPullback [Flat ε] (H : IsPullback δ i₁ i ε) :
    ∃ ε' : blowUp i₁.ker ⟶ blowUp i.ker,
      IsPullback ε' (blowUpToBase i₁.ker) (blowUpToBase i.ker) ε :=
  exists_isPullback_blowUpToBase_of_eq_comap i.ker i₁.ker
    (AlgebraicGeometry.ker_eq_comap_ker_of_isPullback H.flip).symm

/-- The left square of a horizontal pasting is cartesian when the right one and the outer
rectangle are, with the outer rectangle presented through equal composites. -/
theorem isPullback_of_right_of_eq {C : Type*} [Category C] {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
    {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} {a : X₁₁ ⟶ X₁₃} {c : X₂₁ ⟶ X₂₃}
    (s : IsPullback a v₁₁ v₁₃ c) (ha : h₁₁ ≫ h₁₂ = a) (hc : h₂₁ ≫ h₂₂ = c)
    (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback h₁₁ v₁₁ v₁₂ h₂₁ := by
  subst ha hc
  exact s.of_right p t

/-- **The exceptional divisor under base change.** If `i₁` is the base change of the closed
immersion `i` along `ε` and the blowup of `X₁` along `Z₁` is the base change of the blowup of `X`
along `Z`, then the exceptional divisor `E₁` of the first is the base change of the exceptional
divisor `E` of the second, both along the inclusion of exceptional divisors, `E₁ = E ×_{X'} X₁'`,
and along the projection onto the centre, `E₁ = E ×_Z Z₁`. -/
theorem exists_isPullback_exceptionalDivisor {ε' : blowUp i₁.ker ⟶ blowUp i.ker}
    (hb : IsPullback ε' (blowUpToBase i₁.ker) (blowUpToBase i.ker) ε)
    (H : IsPullback δ i₁ i ε) :
    ∃ ε'' : exceptionalDivisor i₁.ker ⟶ exceptionalDivisor i.ker,
      IsPullback ε'' (exceptionalIdeal i₁.ker).subschemeι (exceptionalIdeal i.ker).subschemeι
          ε' ∧
        IsPullback ε'' (exceptionalToCentre i₁) (exceptionalToCentre i) δ := by
  have hE := isPullback_exceptionalToCentre i
  have hE₁ := isPullback_exceptionalToCentre i₁
  have hw : ((exceptionalIdeal i₁.ker).subschemeι ≫ ε') ≫ blowUpToBase i.ker =
      (exceptionalToCentre i₁ ≫ δ) ≫ i := by
    simp only [Category.assoc]
    rw [hb.w, reassoc_of% hE₁.w, H.w]
    exact Category.assoc _ _ _
  refine ⟨hE.lift _ _ hw, ?_, ?_⟩
  · exact isPullback_of_right_of_eq (hE₁.flip.paste_horiz H) (hE.lift_snd _ _ hw) hb.w
      (hE.lift_fst _ _ hw) hE.flip
  · exact isPullback_of_right_of_eq (hE₁.paste_horiz hb) (hE.lift_fst _ _ hw) H.w
      (hE.lift_snd _ _ hw) hE

/-- **The blowup morphism of an ideal sheaf of finite type is quasi-compact**: it is proper. -/
theorem quasiCompact_blowUpToBase_of_fg {S : Scheme.{u}} (I : S.IdealSheafData)
    (hI : ∀ U : S.affineOpens, (I.ideal U).FG) : QuasiCompact (blowUpToBase I) :=
  have := isProper_blowUpToBase I hI
  inferInstance

end Stacks.Blowup

end
