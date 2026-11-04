module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# Unbounded right derived functors computed by K-injectives are absolute

Let `A` be an abelian category in which every cochain complex admits a quasi-isomorphism into a
K-injective complex, and let `RF : D(A) ⥤ H` be the right derived functor of a functor
`F : K(A) ⥤ H` along the quasi-isomorphisms. Then `RF` is *absolute*: for every functor
`G : H ⥤ H'`, the composite `RF ⋙ G` is the right derived functor of `F ⋙ G`.

This is what makes the derived adjunction of `CategoryTheory.Adjunction.derived` available for
such derived functors: that construction descends the counit of an adjunction `G ⊣ F` to the
derived functors, and for this it needs the right derived functor of `F` to stay a right derived
functor after post-composition with the left one.

The proof is a comparison. Both `F` and `F ⋙ G` have pointwise right derived functors
(Stacks 070K), and for *any* right derived functor the structure map is an isomorphism at a
K-injective complex. So the canonical comparison from the universal right derived functor of
`F ⋙ G` to `RF ⋙ G` is an isomorphism at every object represented by a K-injective complex,
hence — every object of `D(A)` being so represented — an isomorphism.

## Main results

* `Stacks.SmallDerivedCategory.isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective` —
  absoluteness of an unbounded right derived functor computed by K-injective resolutions.

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 070Y](https://stacks.math.columbia.edu/tag/070Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace Stacks.SmallDerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- Every object of the unbounded derived category of an abelian category with K-injective
resolutions is isomorphic to the image of a K-injective complex. -/
theorem exists_isKInjective_iso_of_exists_quasiIso_isKInjective
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ X) := by
  obtain ⟨I, f, hI, hf⟩ := hA (DerivedCategory.Q.objPreimage X)
  have := hf
  exact ⟨I, hI, ⟨(DerivedCategory.quotientCompQhIso A).app I ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

variable {H : Type*} [Category* H] {H' : Type*} [Category* H']

/-- **An unbounded right derived functor computed by K-injective resolutions is absolute.** Let
`A` be an abelian category in which every complex admits a quasi-isomorphism into a K-injective
complex, let `RF : D(A) ⥤ H` be a right derived functor of `F : K(A) ⥤ H` along the
quasi-isomorphisms, and let `G : H ⥤ H'` be an arbitrary functor. Then `RF ⋙ G` is a right
derived functor of `F ⋙ G`. -/
theorem isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) (RF : DerivedCategory A ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : H ⥤ H') :
    (RF ⋙ G).IsRightDerivedFunctor (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  set W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ) with hW
  obtain ⟨-, hiso⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective F hA
  obtain ⟨hpt, hiso'⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F ⋙ G) hA
  have := hpt
  set RFG := (F ⋙ G).totalRightDerived DerivedCategory.Qh W with hRFG
  set γ := (F ⋙ G).totalRightDerivedUnit DerivedCategory.Qh W with hγ
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc RFG γ W]
  set θ := RFG.rightDerivedDesc γ W (RF ⋙ G)
    (whiskerRight α G ≫ (Functor.associator _ _ _).hom) with hθ
  have key (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (θ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    have h₁ : IsIso (γ.app ((HomotopyCategory.quotient _ _).obj I)) :=
      hiso' DerivedCategory.Qh RFG γ I hI
    have h₂ : IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)) :=
      hiso DerivedCategory.Qh RF α I hI
    have hfac := RFG.rightDerived_fac_app γ W (RF ⋙ G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom) ((HomotopyCategory.quotient _ _).obj I)
    rw [← hθ] at hfac
    have h₃ : IsIso (γ.app ((HomotopyCategory.quotient _ _).obj I) ≫
        θ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
      rw [hfac]
      simp only [NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app,
        Category.comp_id]
      infer_instance
    exact IsIso.of_isIso_comp_left (γ.app ((HomotopyCategory.quotient _ _).obj I)) _
  have happ : ∀ X, IsIso (θ.app X) := by
    intro X
    obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_of_exists_quasiIso_isKInjective hA X
    have := key I hI
    have h₃ : IsIso (RFG.map e.hom ≫ θ.app X) := by
      rw [θ.naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_left (RFG.map e.hom) _
  exact NatIso.isIso_of_isIso_app θ

end Stacks.SmallDerivedCategory

end
