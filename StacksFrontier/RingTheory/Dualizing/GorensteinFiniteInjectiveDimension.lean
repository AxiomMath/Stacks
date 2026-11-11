module

public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.GorensteinRingDualizing
public import StacksFrontier.RingTheory.Dualizing.IsDualizingComplexModels
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Dualizing.NormalizedShiftSelfUniverse
public import StacksFrontier.RingTheory.Dualizing.QuotientExtConcentration

/-!
# Gorenstein rings of finite injective dimension over themselves

A Noetherian ring has finite injective dimension as a module over itself exactly when it is
Gorenstein and of finite Krull dimension, and in that case the ring placed in degree zero is a
dualizing complex.

## Main results

* `Dualizing.hasInjectiveDimensionLE_of_isGorensteinLocalRing` — over a Gorenstein local ring of
  Krull dimension at most `d`, the regular module has injective dimension at most `d`.
* `Dualizing.hasInjectiveDimensionLE_of_isGorensteinRing` — the same bound over a Gorenstein ring
  of Krull dimension at most `d`.
* `Dualizing.exists_hasInjectiveDimensionLE_self_iff_isGorensteinRing` — **[Stacks, Tag 0HB2]**.

## Implementation notes

The forward implication is the route of the source: finite injective dimension of `A` makes `A[0]`
a dualizing complex (`Dualizing.isDualizingComplex_single_self_iff`), a ring with a dualizing
complex has finite Krull dimension ([Stacks, Tag 0A80]), and a ring for which `A[0]` is dualizing
is Gorenstein, since each localization of `A[0]` is dualizing ([Stacks, Tag 0A7G]).

For the converse, `Ext^{d + 1}_A(A/I, A)` is tested at the maximal ideals `𝔪`: its localization is
`Ext^{d + 1}_{A_𝔪}((A/I)_𝔪, A_𝔪)` (`Dualizing.localized_ext_nontrivial_iff`), which vanishes because
`A_𝔪[e]`, `e = dim A_𝔪 ≤ d`, is a normalized dualizing complex
(`Dualizing.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self`) and Ext from
a finite module into a normalized dualizing complex is concentrated in nonpositive degrees
([Stacks, Tag 0A7U]). Baer's criterion in the form `ModuleCat.hasInjectiveDimensionLE_of_quotients`
turns the vanishing into the bound.

The statements are about modules and do not mention the derived category, except for the final
clause, which is stated for an arbitrary model `[HasDerivedCategory (ModuleCat A)]` and is reduced
to the standard model by `Dualizing.isDualizingComplex_modelEquiv_iff`. The standard model is used
only inside proofs.

## References

* [Stacks Project, Tag 0HB2](https://stacks.math.columbia.edu/tag/0HB2)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Dualizing

/-- **Gorenstein local rings have injective dimension at most their dimension.** Over a Noetherian
local Gorenstein ring of Krull dimension at most `d`, the ring has injective dimension at most `d`
as a module over itself. -/
theorem hasInjectiveDimensionLE_of_isGorensteinLocalRing
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (hB : IsGorensteinLocalRing B) (d : ℕ) (hdim : ringKrullDim B ≤ d) :
    HasInjectiveDimensionLE (ModuleCat.of B B) d := by
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim B = (e : WithBot ℕ∞) := by
    have hbot : ringKrullDim B ≠ ⊥ := fun h => by
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim B := ringKrullDim_nonneg_of_nontrivial
      rw [h] at h0
      exact absurd h0 (by simp)
    obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have htop : x ≠ ⊤ := by
      rintro rfl
      rw [← hx] at hdim
      exact absurd hdim
        (not_le.mpr (by exact_mod_cast WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)))
    obtain ⟨e, rfl⟩ := ENat.ne_top_iff_exists.mp htop
    exact ⟨e, hx.symm⟩
  have hed : e ≤ d := by
    have := he ▸ hdim
    exact_mod_cast this
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  have hK :=
    LocalDuality.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self B hB e he
  refine ModuleCat.hasInjectiveDimensionLE_of_quotients (ModuleCat.of B B) d fun J => ?_
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ J))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N
  suffices hX : Subsingleton (DerivedCategory.Ext X S ((d + 1 : ℕ) : ℤ)) from
    @Equiv.subsingleton _ _ (CategoryTheory.Abelian.Ext.homEquiv (C := ModuleCat.{u} B)
      (X := N) (Y := ModuleCat.of B B) (n := d + 1)) hX
  have eShift : S⟦((d + 1 : ℕ) : ℤ)⟧ ≅ (S⟦(e : ℤ)⟧)⟦((d + 1 : ℕ) : ℤ) - e⟧ :=
    (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} B)) (e : ℤ) (((d + 1 : ℕ) : ℤ) - e)
      ((d + 1 : ℕ) : ℤ) (by omega)).app S
  suffices h' : Subsingleton (DerivedCategory.Ext X (S⟦(e : ℤ)⟧) (((d + 1 : ℕ) : ℤ) - e)) from
    (Iso.homCongr (Iso.refl X) eShift).subsingleton_congr.2 h'
  rcases subsingleton_or_nontrivial (Shrink.{u} (B ⧸ J)) with hsub | hnt
  · have hN : IsZero N := ModuleCat.isZero_of_subsingleton N
    have hXz : IsZero X := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map_isZero hN
    exact ⟨fun f g => hXz.eq_of_src f g⟩
  · have : Module.Finite B (Shrink.{u} (B ⧸ J)) :=
      Module.Finite.equiv (Shrink.linearEquiv B (B ⧸ J)).symm
    obtain ⟨s, hs⟩ : ∃ s : ℕ, Module.supportDim B (Shrink.{u} (B ⧸ J)) = (s : WithBot ℕ∞) := by
      have hbot := Module.supportDim_ne_bot_of_nontrivial (R := B) (M := Shrink.{u} (B ⧸ J))
      obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
      have hle : Module.supportDim B (Shrink.{u} (B ⧸ J)) ≤ (e : WithBot ℕ∞) :=
        he ▸ Module.supportDim_le_ringKrullDim B _
      have htop : x ≠ ⊤ := by
        rintro rfl
        rw [← hx] at hle
        exact absurd hle
          (not_le.mpr (by exact_mod_cast WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top e)))
      obtain ⟨s, rfl⟩ := ENat.ne_top_iff_exists.mp htop
      exact ⟨s, hx.symm⟩
    refine not_nontrivial_iff_subsingleton.mp fun hExt => ?_
    have hmem := ext_degree_mem_Icc_of_nontrivial.{u, u} (A := B)
      (M := Shrink.{u} (B ⧸ J)) _ hK s hs _ hExt
    have := hmem.2
    omega

/-- **Gorenstein rings of finite dimension have finite injective dimension.** Over a Noetherian
Gorenstein ring of Krull dimension at most `d`, the ring has injective dimension at most `d` as a
module over itself. -/
theorem hasInjectiveDimensionLE_of_isGorensteinRing
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hA : IsGorensteinRing A) (d : ℕ) (hdim : ringKrullDim A ≤ d) :
    HasInjectiveDimensionLE (ModuleCat.of A A) d := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  refine ModuleCat.hasInjectiveDimensionLE_of_quotients (ModuleCat.of A A) d fun I => ?_
  let N : ModuleCat.{u} A := ModuleCat.of A (Shrink.{u} (A ⧸ I))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  suffices hX : Subsingleton (DerivedCategory.Ext X K ((d + 1 : ℕ) : ℤ)) from
    @Equiv.subsingleton _ _ (CategoryTheory.Abelian.Ext.homEquiv (C := ModuleCat.{u} A)
      (X := N) (Y := ModuleCat.of A A) (n := d + 1)) hX
  have : Module.Finite A (Shrink.{u} (A ⧸ I)) :=
    Module.Finite.equiv (Shrink.linearEquiv A (A ⧸ I)).symm
  refine Module.subsingleton_of_localization_maximal (R := A)
    (fun (m : Ideal A) _ =>
      LocalizedModule m.primeCompl (DerivedCategory.Ext X K ((d + 1 : ℕ) : ℤ)))
    (fun (m : Ideal A) _ => LocalizedModule.mkLinearMap m.primeCompl
      (DerivedCategory.Ext X K ((d + 1 : ℕ) : ℤ))) fun m hm => ?_
  let T := m.primeCompl
  let B := Localization T
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  refine not_nontrivial_iff_subsingleton.mp fun hloc => ?_
  have hKge : ∃ b : ℤ, K.IsGE b := ⟨0, by dsimp [K]; infer_instance⟩
  have hB := (localized_ext_nontrivial_iff.{u, u} (T := T) (M := Shrink.{u} (A ⧸ I)) K hKge
    ((d + 1 : ℕ) : ℤ)).mp hloc
  let G := ModuleCat.localizedModuleFunctor.{u} T
  let eB : G.obj (ModuleCat.of A A) ≅ ModuleCat.of B B :=
    ((Shrink.linearEquiv B (LocalizedModule T A)).trans
      ((LocalizedModule.equivTensorProduct T A).trans
        (TensorProduct.AlgebraTensorModule.rid A B B))).toModuleIso
  let eK : G.mapDerivedCategory.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) :=
    (G.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso eB
  have hdimB : ringKrullDim B ≤ d := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m B]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
  have hinjB := hasInjectiveDimensionLE_of_isGorensteinLocalRing B (hA m) d hdimB
  let NB : ModuleCat.{u} B := G.obj N
  have hsub : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj NB)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
      ((d + 1 : ℕ) : ℤ)) := by
    have := HasInjectiveDimensionLT.subsingleton.{u} (ModuleCat.of B B) (d + 1) (d + 1) le_rfl NB
    exact @Equiv.subsingleton _ _ (CategoryTheory.Abelian.Ext.homEquiv (C := ModuleCat.{u} B)
      (X := NB) (Y := ModuleCat.of B B) (n := d + 1)).symm this
  exact not_subsingleton_iff_nontrivial.mpr hB
    ((Iso.homCongr (Iso.refl _) ((shiftFunctor _ ((d + 1 : ℕ) : ℤ)).mapIso eK)).subsingleton_congr.2
      hsub)

/-- **Stacks Project, Tag 0HB2.** Let `A` be a Noetherian ring. Then `A` has finite injective
dimension as a module over itself if and only if `A` is Gorenstein and finite dimensional. In this
case `A[0]` is a dualizing complex, in any model of the derived category of `A`-modules. -/
@[stacks 0HB2]
theorem exists_hasInjectiveDimensionLE_self_iff_isGorensteinRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    ((∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n) ↔
        IsGorensteinRing A ∧ ringKrullDim A < ⊤) ∧
      ((∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n) →
        IsDualizingComplex
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) := by
  let h₂ : HasDerivedCategory.{w} (ModuleCat.{u} A) := inferInstance
  let h₁ := HasDerivedCategory.standard (ModuleCat.{u} A)
  have hstd : (∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n) →
      @IsDualizingComplex A _ _ h₁
        (@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _ h₁ 0 |>.obj (ModuleCat.of A A)) :=
    fun h => (isDualizingComplex_single_self_iff A).2 h
  refine ⟨⟨fun h => ⟨isGorensteinRing_of_isDualizingComplex_self A (hstd h),
      ringKrullDim_lt_top_of_isDualizingComplex (hstd h)⟩, fun ⟨hG, hdim⟩ => ?_⟩, fun h => ?_⟩
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim A ≤ d := by
      by_cases hbot : ringKrullDim A = ⊥
      · exact ⟨0, hbot ▸ bot_le⟩
      obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hbot
      have htop : x ≠ ⊤ := by
        rintro rfl
        rw [← hx] at hdim
        exact lt_irrefl _ hdim
      obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp htop
      exact ⟨d, hx ▸ le_rfl⟩
    exact ⟨d, hasInjectiveDimensionLE_of_isGorensteinRing A hG d hd⟩
  · let L := (@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _ h₂ 0).obj (ModuleCat.of A A)
    let e : (StacksDraft.DerivedModel.modelEquiv h₂ h₁).functor.obj L ≅
        (@DerivedCategory.singleFunctor (ModuleCat.{u} A) _ _ h₁ 0).obj (ModuleCat.of A A) :=
      (StacksDraft.DerivedModel.modelEquiv h₂ h₁).functor.mapIso
          ((@DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) _ _ h₂ 0).app
            (ModuleCat.of A A)) ≪≫
        (StacksDraft.DerivedModel.modelCompQIso h₂ h₁).app _ ≪≫
        ((@DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) _ _ h₁ 0).app
          (ModuleCat.of A A)).symm
    exact (isDualizingComplex_modelEquiv_iff h₂ h₁ L).1
      ((isDualizingComplex_iff_of_iso e).2 (hstd h))

end Dualizing
