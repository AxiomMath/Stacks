module

public import StacksFrontier.Homology.Perfect.Colimit

/-!
# Bounded complexes of finite projective modules descend along a filtered colimit of rings

Let `R : I ⥤ CommRingCat` be a filtered system of commutative rings with colimit `A = c.pt`,
computed on underlying sets. Every bounded complex `C` of finite projective `A`-modules is, in the
derived category of `A`, isomorphic to the termwise extension of scalars `C_i ⊗_{R_i} A` of a
bounded complex `C_i` of finite projective `R_i`-modules, for some stage `i`.

This is the descent of perfect complexes of Stacks 0BC7
(`StacksDraft.Perfect.perfectComplexes_filteredColimit`) read on representatives: the perfect
object `C_i` produced there is represented by a bounded complex of finite projective modules, and
on such a complex derived extension of scalars is computed termwise, a bounded complex of
projectives computing it (Section 064F).

## Main results

* `StacksDraft.Perfect.exists_finiteProjective_extendScalars_iso`.

## References

* [Stacks Project, Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7)
* [Stacks Project, Tag 064F](https://stacks.math.columbia.edu/tag/064F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe uI uR

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- Termwise extension of scalars of a complex of finite projective modules has finite projective
terms. -/
theorem finite_projective_extendScalars_obj {A A' : Type uR} [CommRing A] [CommRing A']
    (f : A →+* A') (M : ModuleCat.{uR} A) [Module.Finite A M] [Module.Projective A M] :
    Module.Finite A' ((ModuleCat.extendScalars.{uR, uR, uR} f).obj M) ∧
      Module.Projective A' ((ModuleCat.extendScalars.{uR, uR, uR} f).obj M) := by
  let := f.toAlgebra
  exact ⟨inferInstanceAs (Module.Finite A' (TensorProduct A A' M)),
    inferInstanceAs (Module.Projective A' (TensorProduct A A' M))⟩

/-- **Bounded complexes of finite projective modules descend along a filtered colimit of
rings.** For a filtered system of commutative rings `R` whose colimit `c.pt` is computed on
underlying sets, every bounded complex `C` of finite projective `c.pt`-modules is isomorphic in
`D(c.pt)` to the termwise extension of scalars of a bounded complex of finite projective
`R.obj i`-modules, for some stage `i`. -/
theorem exists_finiteProjective_extendScalars_iso
    {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{uR}) [PreservesColimit R (forget CommRingCat.{uR})]
    (c : Cocone R) (hc : IsColimit c) (C : CochainComplex (ModuleCat.{uR} c.pt) ℤ) (a b : ℤ)
    (ha : C.IsStrictlyGE a) (hb : C.IsStrictlyLE b) (hfin : ∀ n : ℤ, Module.Finite c.pt (C.X n))
    (hproj : ∀ n : ℤ, Module.Projective c.pt (C.X n)) :
    ∃ (i : I) (Cᵢ : CochainComplex (ModuleCat.{uR} (R.obj i)) ℤ) (a' b' : ℤ),
      Cᵢ.IsStrictlyGE a' ∧ Cᵢ.IsStrictlyLE b' ∧ (∀ n : ℤ, Module.Finite (R.obj i) (Cᵢ.X n)) ∧
      (∀ n : ℤ, Module.Projective (R.obj i) (Cᵢ.X n)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{uR, uR, uR} (c.ι.app i).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Cᵢ) ≅ DerivedCategory.Q.obj C) := by
  obtain ⟨hdesc, -⟩ := perfectComplexes_filteredColimit.{uI, uR} R c hc
  obtain ⟨i, K, ⟨P, a', b', ha', hb', hPfin, hPproj, ⟨eP⟩⟩, ⟨eK⟩⟩ :=
    hdesc (DerivedCategory.Q.obj C) ⟨C, a, b, ha, hb, hfin, hproj, ⟨Iso.refl _⟩⟩
  let D := totalDerivedExtensionScalars.{uR, uR, uR} (c.ι.app i).hom
  have : ∀ n, Projective (P.X n) := fun n =>
    (IsProjective.iff_projective (R := R.obj i) (P := P.X n)).1 (hPproj n)
  have := hb'
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b'
  refine ⟨i, P, a', b', ha', hb', hPfin, hPproj, ⟨?_⟩⟩
  exact (asIso (D.comparison.app P)).symm ≪≫ D.functor.mapIso eP.symm ≪≫ eK.symm

end StacksDraft.Perfect
