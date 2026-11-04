module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.A72
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFinite

/-!
# Dualizing complexes under a finite ring map

Let `f : A → B` be a finite homomorphism of Noetherian rings and let `ω` be a dualizing
complex over `A`. Tag 0AX0 asserts that `RHom_A(B, ω)` is a dualizing complex over `B`. Being
dualizing is the conjunction of three conditions (Tag 0A7B), and the source proves them
separately: finite injective dimension, because a bounded complex of injective `A`-modules
representing `ω` is carried by `Hom_A(B, -)` to a bounded complex of injective `B`-modules in
the same degrees (Tag 08XR); finiteness of the cohomology modules, which is Tag 0A72; and the
homothety condition, which is the computation
`Hom_{D(B)}(RHom_A(B, ω), RHom_A(B, ω)[n]) = Hom_{D(A)}(RHom_A(B, ω), ω[n])`, equal to `B` for
`n = 0` and to `0` otherwise.

This file supplies the first two conditions for the canonical derived functor
`Dualizing.derivedHom` of Tag 0A70, and reduces the third one to a statement about derived
endomorphisms of a single object, with no reference to a choice of model. The predicate
`Dualizing.IsDerivedHomothetyQuasiIso` quantifies over every bounded injective representative
of its argument, which makes it awkward to verify directly;
`Dualizing.isDerivedHomothetyQuasiIso_of_end` replaces that quantifier by the two
hypotheses the source's computation produces, namely a `B`-linear identification
`End_{D(B)}(L) ≃ₗ[B] B` and the vanishing of `Hom_{D(B)}(L, L[n])` for `n ≠ 0`. Combining the
three gives `Dualizing.isDualizingComplex_derivedHom_of_finite_of_end`, which is Tag 0AX0 with
exactly the source's remaining Hom computation as its hypothesis.

## Main results

* `Dualizing.endLinearEquivOfIso` — conjugation by an isomorphism of a derived category of
  modules is a linear equivalence of endomorphism modules.
* `Dualizing.isZero_homology_homComplexR_of_subsingleton` — for a bounded-below complex of
  injectives, the degree-`n` cohomology of its Hom complex vanishes as soon as
  `Hom_{D(B)}(QJ, QJ[n])` does.
* `Dualizing.isDerivedHomothetyQuasiIso_of_end` — the model-free criterion for the homothety
  condition of Tag 0A7B.
* `Dualizing.finiteCohomology_derivedHom_obj` — the cohomology modules of `RHom_A(B, ω)` are
  finite over `B`; this is the second condition of Tag 0AX0, obtained from Tag 0A72.
* `Dualizing.isDualizingComplex_derivedHom_of_finite_of_homothetyQuasiIso` and
  `Dualizing.isDualizingComplex_derivedHom_of_finite_of_end` — Tag 0AX0 modulo its third
  condition, respectively in the form of Tag 0A7B and in the Hom-computation form.

## Implementation notes

The reduction of the homothety condition runs through
`Dualizing.homothety_quasiIso_of_rankOne`, which asks for the degree-zero cohomology of the
`B`-valued Hom complex `CochainComplex.HomComplexR B J J` of a K-injective representative `J`
and for the vanishing of the other degrees. Degree zero is `Dualizing.homologyEndLinearEquiv`
followed by conjugation along the chosen isomorphism `QJ ≅ L`. The other degrees go through
`Dualizing.homComplex_represents_derivedHom`, which identifies the degree-`n` cohomology
classes of the Hom complex of a bounded-below complex of injectives with morphisms in the
derived category; that identification is stated for the `AddCommGrpCat`-valued Hom complex, so
the comparison `ShortComplex.mapHomologyIso` along `forget₂ (ModuleCat B) AddCommGrpCat`
transports the resulting vanishing back to `CochainComplex.HomComplexR`.

Nothing here is tagged `0AX0`: the third condition of that tag is not proved. It needs the
biduality half of Tag 0A7C, which the library currently has only as the criterion
`Dualizing.isIso_dualizingBidualityMor`.

## References

* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A72](https://stacks.math.columbia.edu/tag/0A72)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### Endomorphism modules along an isomorphism -/

section Endomorphisms

variable {B : Type u} [CommRing B]

/-- Conjugation by an isomorphism `X ≅ Y` of the derived category of `B`-modules is a
`B`-linear equivalence `End X ≃ₗ[B] End Y`. -/
noncomputable def endLinearEquivOfIso {X Y : DerivedCategory (ModuleCat.{max v u} B)}
    (e : X ≅ Y) : End X ≃ₗ[B] End Y :=
  LinearEquiv.ofLinearMap
    ((Linear.leftComp B Y e.inv).comp (Linear.rightComp B X e.hom))
    ((Linear.leftComp B X e.hom).comp (Linear.rightComp B Y e.inv))
    (by
      ext g
      dsimp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        Linear.leftComp, Linear.rightComp, LinearMap.coe_mk, AddHom.coe_mk]
      simp)
    (by
      ext f
      dsimp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        Linear.leftComp, Linear.rightComp, LinearMap.coe_mk, AddHom.coe_mk]
      simp)

end Endomorphisms

/-! ### The homothety condition from derived endomorphisms -/

section Homothety

variable {B : Type u} [CommRing B]

/-- For a bounded-below complex of injective `B`-modules, the degree-`n` cohomology of its
`B`-valued Hom complex vanishes as soon as there is no nonzero morphism `QJ ⟶ QJ[n]` in the
derived category. -/
theorem isZero_homology_homComplexR_of_subsingleton
    (J : CochainComplex (ModuleCat.{max v u} B) ℤ) (a n : ℤ) [J.IsStrictlyGE a]
    [∀ i, Injective (J.X i)]
    (h : Subsingleton (DerivedCategory.Q.obj J ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
        (DerivedCategory.Q.obj J))) :
    IsZero ((CochainComplex.HomComplexR B J J).homology n) := by
  have eSrc : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).obj J) ≅
        DerivedCategory.Q.obj J :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).app J
  have eTgt : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).obj (J⟦n⟧)) ≅
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
          (DerivedCategory.Q.obj J) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).app (J⟦n⟧) ≪≫
      (DerivedCategory.Q.commShiftIso n).app J
  have hsub : Subsingleton
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).obj J) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{max v u} B) (.up ℤ)).obj (J⟦n⟧))) :=
    Equiv.subsingleton (Iso.homCongr eSrc eTgt)
  have hcc : Subsingleton (CochainComplex.HomComplex.CohomologyClass J J n) :=
    ⟨fun x y => (homComplex_represents_derivedHom J a n).1 (Subsingleton.elim _ _)⟩
  have hadd : Subsingleton ((CochainComplex.HomComplex J J).homology n : Type _) :=
    (CochainComplex.HomComplex.homologyAddEquiv J J n).toEquiv.subsingleton
  let V := forget₂ (ModuleCat.{max v u} B) AddCommGrpCat
  let H := CochainComplex.HomComplexR B J J
  have hsurj : Function.Surjective
      (ConcreteCategory.hom ((H.sc n).mapHomologyIso V).hom) :=
    (ConcreteCategory.bijective_of_isIso ((H.sc n).mapHomologyIso V).hom).2
  have : Subsingleton ((V.obj (H.homology n) : AddCommGrpCat) : Type _) :=
    @Function.Surjective.subsingleton _ _ _ hadd hsurj
  exact ModuleCat.isZero_of_subsingleton _

/-- **The homothety condition of Tag 0A7B, read off from derived endomorphisms.** The predicate
`Dualizing.IsDerivedHomothetyQuasiIso L` quantifies over all bounded injective representatives
of `L`; it holds as soon as `End_{D(B)}(L)` is free of rank one on the identity, in the sense
that it is `B`-linearly isomorphic to `B`, and there is no nonzero morphism `L ⟶ L[n]` for
`n ≠ 0`. These are exactly the two statements produced by the Hom computation in the proof of
Tag 0AX0. -/
theorem isDerivedHomothetyQuasiIso_of_end {L : DerivedCategory (ModuleCat.{max v u} B)}
    (e₀ : End L ≃ₗ[B] B)
    (hvanish : ∀ n : ℤ, n ≠ 0 → Subsingleton
      (L ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj L)) :
    IsDerivedHomothetyQuasiIso L := by
  rintro J ⟨e⟩ hinj ⟨a, b, hGE, hLE⟩
  have := hinj
  have := hGE
  have := hLE
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  refine quasiIso_homothety_of_rankOne J
    ((homologyZeroEndLinearEquiv J).trans ((endLinearEquivOfIso e).trans e₀)) fun n hn => ?_
  refine isZero_homology_homComplexR_of_subsingleton J a n ?_
  have := hvanish n hn
  exact Equiv.subsingleton
    (Iso.homCongr e ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).mapIso e))

end Homothety

/-! ### The three conditions for derived Hom along a finite map -/

section FiniteMap

variable {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Tag 0AX0, second condition.** For a finite homomorphism of Noetherian rings and a
dualizing complex `ω` over the source, every cohomology module of `RHom_A(B, ω)` is finite
over `B`. A dualizing complex lies in `D⁺_Coh(A)`, and Tag 0A72 says derived coextension of
scalars along a finite map carries `D⁺_Coh(A)` into `D⁺_Coh(B)`. -/
theorem finiteCohomology_derivedHom_obj (f : A →+* B) (hf : f.Finite)
    {K : DerivedCategory (ModuleCat.{max v u} A)} (hK : IsDualizingComplex K) (i : ℤ) :
    Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) i).obj
      ((derivedHom.{u, v, u} f).obj K)) :=
  (isBoundedBelowCoherent_obj_rightDerivedCoextendScalars f hf (derivedHom.{u, v, u} f)
    ((coextendScalarsToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)))
    (derivedCategoryBPlus_of_isDualizingComplex hK)).2 i

/-- **Tag 0AX0 modulo its third condition.** For a finite homomorphism of Noetherian rings and
a dualizing complex `ω` over the source, `RHom_A(B, ω)` has finite injective dimension and
finite cohomology modules; so it is a dualizing complex as soon as its homothety map is a
quasi-isomorphism. -/
theorem isDualizingComplex_derivedHom_of_finite_of_homothetyQuasiIso (f : A →+* B) (hf : f.Finite)
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (hhom : IsDerivedHomothetyQuasiIso ((derivedHom.{u, v, u} f).obj K)) :
    IsDualizingComplex ((derivedHom.{u, v, u} f).obj K) where
  finiteInjectiveDimension :=
    hasFiniteInjectiveDimension_derivedHom_obj f hK.finiteInjectiveDimension
  finiteCohomology := finiteCohomology_derivedHom_obj f hf hK
  homothetyQuasiIso := hhom

/-- **Tag 0AX0 modulo the source's Hom computation.** For a finite homomorphism of Noetherian
rings and a dualizing complex `ω` over the source, `RHom_A(B, ω)` is a dualizing complex over
`B` as soon as its derived endomorphism module is `B` and its higher derived self-extensions
vanish. The source deduces those two statements from Tag 0A70 and the biduality half of
Tag 0A7C; everything else in Tag 0AX0 is proved here. -/
theorem isDualizingComplex_derivedHom_of_finite_of_end (f : A →+* B) (hf : f.Finite)
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (e₀ : End ((derivedHom.{u, v, u} f).obj K) ≃ₗ[B] B)
    (hvanish : ∀ n : ℤ, n ≠ 0 → Subsingleton ((derivedHom.{u, v, u} f).obj K ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
        ((derivedHom.{u, v, u} f).obj K))) :
    IsDualizingComplex ((derivedHom.{u, v, u} f).obj K) :=
  isDualizingComplex_derivedHom_of_finite_of_homothetyQuasiIso f hf K hK
    (isDerivedHomothetyQuasiIso_of_end e₀ hvanish)

end FiniteMap

end Dualizing

end
