module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictDerivedReduction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictnessFailure
public import StacksFrontier.RingTheory.Koszul.WeaklyProregular

/-!
# Systems (1) and (3) of Stacks 0GA5 are not strictly pro-isomorphic in `D(A)`

Stacks 0GA5 asserts that the systems (1) `M•/IⁿM•` and (3) `M ⊗ᴸ_A Kₙ` cannot be strictly
pro-isomorphic in general, even for `M = A[0]`, where they are the systems `(A/Iⁿ)[0]` and
`Kₙ` of `D(A)`: applying `H⁰` to a strict pro-isomorphism would give a strict pro-isomorphism
between `A/Iⁿ` and `H⁰(Kₙ) = A/(f₁ⁿ, …, f_rⁿ)`, which fails for `A = ℤ[x₁, …, x_r]`, `fᵢ = xᵢ`,
`r ≥ 2` (`Stacks.LocalCohomology.UniformityII.not_nonempty_iso_proObj_monomial`).  This file
carries out that argument in the strict pro-category of `D(A)` itself.

## Main results

* `Stacks.LocalCohomology.nonempty_iso_proObj_comp`: a functor carries isomorphic objects of
  the strict pro-category to isomorphic objects.
* `Stacks.LocalCohomology.nonempty_iso_proObj_of_iso`: isomorphic inverse sequences are
  isomorphic in the strict pro-category.
* `Stacks.LocalCohomology.UniformityII.not_nonempty_iso_proObj_derived_monomial`: **for
  `A = ℤ[x₀, …, x_{r-1}]`, `r ≥ 2`, the systems `(A/Iⁿ)[0]` and `Kₙ` of `D(A)` are not isomorphic
  in the strict pro-category.**

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.LocalCohomology

universe w v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The image of a representative of a strict pro-morphism under a functor. -/
def StrictProHomRep.map (F : C ⥤ D) {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y) :
    StrictProHomRep (X ⋙ F) (Y ⋙ F) :=
  ⟨f.shift, Functor.whiskerRight f.hom F⟩

/-- If `g ∘ f` is equivalent to the identity, so is its image under a functor. -/
theorem StrictProHomRep.comp_map_equivalent_id (F : C ⥤ D) {X Y : Functor ℕᵒᵖ C}
    (f : StrictProHomRep X Y) (g : StrictProHomRep Y X)
    (h : (f.comp g).Equivalent (StrictProHomRep.id X)) :
    ((f.map F).comp (g.map F)).Equivalent (StrictProHomRep.id (X ⋙ F)) := by
  obtain ⟨d, N, hf, hg, h⟩ := h
  refine ⟨d, N, hf, hg, fun n hn => ?_⟩
  have := congrArg F.map (h n hn)
  dsimp only [StrictProHomRep.map, StrictProHomRep.comp, StrictProHomRep.id,
    shiftedInverseSequenceTransition, Functor.whiskerRight_app, Functor.comp_map] at this ⊢
  simpa only [Functor.map_comp, Functor.map_id, Category.comp_id] using this

/-- **A functor preserves isomorphism in the strict pro-category.** -/
theorem nonempty_iso_proObj_comp (F : C ⥤ D) {X Y : Functor ℕᵒᵖ C}
    (h : Nonempty (proObj X ≅ proObj Y)) : Nonempty (proObj (X ⋙ F) ≅ proObj (Y ⋙ F)) := by
  obtain ⟨f, g, hfg, hgf⟩ := nonempty_iso_iff_exists_rep.1 h
  exact nonempty_iso_iff_exists_rep.2 ⟨f.map F, g.map F,
    StrictProHomRep.comp_map_equivalent_id F f g hfg,
    StrictProHomRep.comp_map_equivalent_id F g f hgf⟩

/-- **Isomorphic inverse sequences are isomorphic in the strict pro-category.** -/
theorem nonempty_iso_proObj_of_iso {X Y : Functor ℕᵒᵖ C} (e : X ≅ Y) :
    Nonempty (proObj X ≅ proObj Y) := by
  have := isIso_proHom_of_hasUniformInverses e.hom
    (CategoryTheory.InverseSequence.HasUniformInverses.of_isIso e.hom)
  exact ⟨asIso (proHom (⟨0, e.hom⟩ : StrictProHomRep X Y))⟩

namespace UniformityII

open MvPolynomial

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- `H⁰` of the system `(A/I^(n+1))[0]` of `D(A)` is the system `A/I^(n+1)`. -/
def homologyZeroIdealPowerSystemIso (I : Ideal A) :
    (AdicCompletionTor.idealPowerQuotientModuleSystem I ⋙
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅
      AdicCompletionTor.idealPowerQuotientModuleSystem I :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
      Functor.rightUnitor _

/-- `H⁰` of the system of Koszul complexes `K_{n+1}` on the powers of `f` is the system
`A/(f₀^(n+1), …, f_{r-1}^(n+1))`, by the Koszul augmentations. -/
def homologyZeroKoszulSystemIso {r : ℕ} (f : Fin r → A) :
    Koszul.powDerivedSystem f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅
      Koszul.powQuotientSystem f := by
  have : ∀ n, IsIso ((Functor.whiskerRight (Koszul.powAugmentationDerived f)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)).app n) := fun n =>
    Koszul.isIso_homologyFunctor_map_Q_map _ 0
      ((quasiIsoAt_iff_isIso_homologyMap _ 0).1 (Koszul.quasiIsoAt_powAugmentation f (n.unop + 1)))
  have := NatIso.isIso_of_isIso_app (Functor.whiskerRight (Koszul.powAugmentationDerived f)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0))
  exact asIso (Functor.whiskerRight (Koszul.powAugmentationDerived f)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (HomologicalComplex.homologyFunctorSingleIso _ _ 0) ≪≫
    Functor.rightUnitor _

/-- **Stacks 0GA5, failure of strictness for (1) and (3), in `D(A)`.**  Let
`A = ℤ[x₀, …, x_{r-1}]` with `r ≥ 2`, `fᵢ = xᵢ` and `I = (x₀, …, x_{r-1})`.  For `M = A[0]` the
system (1) is `n ↦ (A/I^(n+1))[0]` and the system (3) is `n ↦ A ⊗ᴸ K_{n+1} = K_{n+1}`, the
Koszul complex on `x₀^(n+1), …, x_{r-1}^(n+1)`.  These two inverse systems of `D(A)` are not
isomorphic in the strict pro-category of `D(A)`.

Applying `H⁰` to an isomorphism of the strict pro-category gives one between the systems
`A/I^(n+1)` and `H⁰(K_{n+1}) = A/(x₀^(n+1), …, x_{r-1}^(n+1))` of modules, which
`not_nonempty_iso_proObj_monomial` rules out. -/
@[stacks 0GA5 "systems (1) and (3) are not strictly pro-isomorphic, even for `M = A[0]`: the \
example `A = ℤ[x₁, …, x_r]`, `fᵢ = xᵢ`, read in the strict pro-category of `D(A)`"]
theorem not_nonempty_iso_proObj_derived_monomial {r : ℕ}
    [HasDerivedCategory.{w} (ModuleCat.{0} (MvPolynomial (Fin r) ℤ))] (hr : 2 ≤ r) :
    ¬ Nonempty
      (proObj (AdicCompletionTor.idealPowerQuotientModuleSystem
          (Ideal.span (Set.range fun i : Fin r => (X i : MvPolynomial (Fin r) ℤ))) ⋙
          DerivedCategory.singleFunctor (ModuleCat.{0} (MvPolynomial (Fin r) ℤ)) 0) ≅
        proObj (Koszul.powDerivedSystem fun i : Fin r => (X i : MvPolynomial (Fin r) ℤ))) := by
  intro h
  have h₀ := nonempty_iso_proObj_comp (DerivedCategory.homologyFunctor _ 0) h
  obtain ⟨e₀⟩ := h₀
  obtain ⟨e₁⟩ := nonempty_iso_proObj_of_iso (homologyZeroIdealPowerSystemIso
    (Ideal.span (Set.range fun i : Fin r => (X i : MvPolynomial (Fin r) ℤ))))
  obtain ⟨e₂⟩ := nonempty_iso_proObj_of_iso (homologyZeroKoszulSystemIso
    (fun i : Fin r => (X i : MvPolynomial (Fin r) ℤ)))
  exact not_nonempty_iso_proObj_monomial r hr ⟨e₁.symm ≪≫ e₀ ≪≫ e₂⟩

end UniformityII

end Stacks.LocalCohomology

end
