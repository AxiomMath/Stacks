module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteFlatDeRhamComplexTrace
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.AbelianAcyclic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass

/-!
# The trace map on de Rham cohomology of a finite syntomic morphism

Let `f : X ⟶ P` be a finite syntomic morphism of schemes such that `f_*𝒪_X` is finite locally
free of constant rank `e`, let `sP : P ⟶ S` be a morphism and `sX = f ≫ sP`. In the proof of
Axiom (A6) for de Rham cohomology (Stacks, Section 0FWC, "Proof of Axiom (A6) for `X`
irreducible") the trace map `Θ_f : f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}` of Proposition 0FLC, whose
composite with the canonical map `Ω^•_{P/S} ⟶ f_*Ω^•_{X/S}` is multiplication by `e`, gives a map
`Θ : H^n_{dR}(X/S) ⟶ H^n_{dR}(P/S)` with `Θ ∘ f^* = e`. This file constructs `Θ` in every degree
and proves the identity, and deduces that `f^*` is injective when `e` is invertible on `S`, for
instance when `S = Spec k` with `k` a field of characteristic zero and `e ≥ 1`.

The map is `Θ_n = H^n(RΓ(P, Θ_f)) ∘ (H^n(X, Ω^•_{X/S}) = H^n(P, f_*Ω^•_{X/S}))`. The identification
uses that `f` is affine, so the terms of `Ω^•_{X/S}`, being quasi-coherent, are acyclic for the
direct image of abelian sheaves ([Stacks, Tag 01XC]) and `f_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}` is an
isomorphism; `RΓ(X, -) = RΓ(P, Rf_* -)` is [Stacks, Tag 01EZ].

## Main definitions

* `Stacks.WeilDeRham.deRhamAbelianTraceMapPlus`: the trace map of de Rham complexes as a
  morphism of bounded below complexes of abelian sheaves on `P`.
* `Stacks.WeilDeRham.deRhamDerivedSectionsTrace`: the trace map
  `RΓ(X, Ω^•_{X/S}) ⟶ RΓ(P, Ω^•_{P/S})`.
* `Stacks.WeilDeRham.deRhamCohomologyTrace`: the trace map
  `Θ_n : H^n_{dR}(X/S) ⟶ H^n_{dR}(P/S)`.

## Main results

* `Stacks.WeilDeRham.isIso_deRhamPushforwardToDerived_of_isAffineHom`: for an affine morphism,
  `f_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}` is an isomorphism.
* `Stacks.WeilDeRham.deRhamCohomologyTrace_deRhamCohomologyPullback`: **`Θ_n(f^* x) = e • x`.**
* `Stacks.WeilDeRham.exists_deRhamCohomologyTrace`: the same for any structure morphism `sX`
  with `f ≫ sP = sX ≫ 𝟙 S`.
* `Stacks.WeilDeRham.injective_deRhamCohomologyPullback`: `f^*` is injective when `e` is a unit of
  `Γ(S, 𝒪_S)`.
* `Stacks.WeilDeRham.injective_deRhamCohomologyPullback_of_charZero`: `f^*` is injective over
  a field of characteristic zero when `e ≥ 1`.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.Cohomology.LerayLowDegree Stacks.Cohomology.Leray
open Stacks.AlgebraicGeometry.HigherDirectImage
  (rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom)

universe u

namespace Stacks.WeilDeRham

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### `f_* = Rf_*` on the de Rham complex along an affine morphism -/

section Affine

variable {X P S : Scheme.{u}} (f : X ⟶ P) [IsAffineHom f] (sX : X ⟶ S)

/-- **The higher derived functors of the direct image of abelian sheaves along an affine morphism
vanish on the abelian sheaf underlying a quasi-coherent module** ([Stacks, Tag 01XC]). The
statement involves no derived category; the proof reads it off the right acyclicity of
`Stacks.AlgebraicGeometry.HigherDirectImage.rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom`
in the standard model of the derived categories. -/
theorem isZero_rightDerived_abelianPushforward_toSheaf_of_isAffineHom (M : X.Modules)
    [M.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (((abelianPushforward.{u, u} f.base).rightDerived p).obj
      ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M)) := by
  let := HasDerivedCategory.standard (AbelianSheaf X.toRingedSpace.carrier)
  let := HasDerivedCategory.standard (AbelianSheaf P.toRingedSpace.carrier)
  exact (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).1
    (rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom f M) p hp

variable [HasDerivedCategory (AbelianSheaf X.toRingedSpace.carrier)]
  [HasDerivedCategory (AbelianSheaf P.toRingedSpace.carrier)] in
/-- **Every degree of the `ℤ`-indexed abelian de Rham complex is right acyclic for the direct
image of abelian sheaves along an affine morphism**, for any model of the derived categories. In
degree `p ≥ 0` the term is the abelian sheaf underlying the quasi-coherent module `Ω^p_{X/S}`,
acyclic by [Stacks, Tag 01XC]; in negative degrees the term is zero. -/
theorem rightAcyclic_abelianPushforward_deRhamTermInt_of_isAffineHom (n : ℤ) :
    (abelianPushforward.{u, u} f.base).rightAcyclic
      ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras sX))).X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
      (HomologicalComplex.isZero_extend_X _ _ n (fun i hi => by
        have hi' : (i : ℤ) = n := hi
        omega))
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h : (abelianPushforward.{u, u} f.base).rightAcyclic
        ((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj
          (relativeDifferentialForms sX (p : ℤ))) :=
      have := isQuasicoherent_relativeDifferentialForms sX p
      (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
        (isZero_rightDerived_abelianPushforward_toSheaf_of_isAffineHom f _)
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := p) rfl).symm h

/-- **`f_*Ω^•_{X/S} = Rf_*Ω^•_{X/S}` along an affine morphism `f`**: the comparison
`AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` is an isomorphism, by Leray's
acyclicity lemma applied to the degreewise acyclicity above. -/
theorem isIso_deRhamPushforwardToDerived_of_isAffineHom :
    IsIso (deRhamPushforwardToDerived f sX) := by
  let := HasDerivedCategory.standard (AbelianSheaf X.toRingedSpace.carrier)
  let := HasDerivedCategory.standard (AbelianSheaf P.toRingedSpace.carrier)
  have : IsIso ((abelianPushforward.{u, u} f.base).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient (AbelianSheaf X.toRingedSpace.carrier)).obj
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras sX)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras sX))))) :=
    CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _
      (rightAcyclic_abelianPushforward_deRhamTermInt_of_isAffineHom f sX)
  delta deRhamPushforwardToDerived
  infer_instance

end Affine

/-! ### The trace map on derived global sections and on de Rham cohomology -/

variable {X P S : Scheme.{u}} (f : X ⟶ P) (sP : P ⟶ S) [IsFinite f] (hf : Syntomic f) (e : ℕ)

/-- **The trace map of de Rham complexes as a morphism of bounded below complexes**
`f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}` of abelian sheaves on `P`: `Stacks.WeilDeRham.deRhamAbelianTraceMap`
extended by zero to negative degrees. -/
def deRhamAbelianTraceMapPlus :
    deRhamPushforwardPlus f (f ≫ sP) ⟶
      AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras sP)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras sP)) :=
  ⟨(HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} f.base) _ ComplexShape.embeddingUpNat).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor _).map (deRhamAbelianTraceMap f sP hf)⟩

/-- An additive functor sends a factorization `a ≫ b = e • 𝟙 _` to one. -/
private theorem map_comp_eq_nsmul_id {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C} {a : A ⟶ B} {b : B ⟶ A} {e : ℕ}
    (h : a ≫ b = e • 𝟙 A) : F.map a ≫ F.map b = e • 𝟙 (F.obj A) := by
  rw [← F.map_comp, h, F.map_nsmul, F.map_id]

/-- **The canonical map followed by the trace map is multiplication by `e`** on the bounded
below abelian de Rham complex of `P`. -/
theorem deRhamAbelianPushforwardMapPlus_comp_deRhamAbelianTraceMapPlus
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (hcomm : f ≫ sP = (f ≫ sP) ≫ 𝟙 S) :
    deRhamAbelianPushforwardMapPlus f sP (f ≫ sP) (𝟙 S) hcomm ≫
        deRhamAbelianTraceMapPlus f sP hf = e • 𝟙 _ := by
  apply (CochainComplex.Plus.ι _).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id]
  change (((ComplexShape.embeddingUpNat.extendFunctor _).map
      (deRhamAbelianPushforwardMap f sP (f ≫ sP) (𝟙 S) hcomm) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} f.base) _ ComplexShape.embeddingUpNat).hom) ≫
    ((HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} f.base) _ ComplexShape.embeddingUpNat).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor _).map (deRhamAbelianTraceMap f sP hf))) = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun φ => _ ≫ φ) (Iso.hom_inv_id_assoc _ _)).trans
    (map_comp_eq_nsmul_id _ (deRhamAbelianPushforwardMap_comp_deRhamAbelianTraceMap f sP hf e)))

/-- **The trace map on derived global sections** `RΓ(X, Ω^•_{X/S}) ⟶ RΓ(P, Ω^•_{P/S})` of a
finite syntomic `f : X ⟶ P` over `sP : P ⟶ S`: the identification
`RΓ(X, -) ≅ RΓ(P, Rf_* -)` of [Stacks, Tag 01EZ], the inverse of the isomorphism
`f_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}` (`f` is affine), and `RΓ(P, Θ_f)`. -/
def deRhamDerivedSectionsTrace :
    letI := HasDerivedCategory.standard (AbelianSheaf X.toRingedSpace.carrier)
    letI := HasDerivedCategory.standard (AbelianSheaf P.toRingedSpace.carrier)
    letI := HasDerivedCategory.standard AddCommGrpCat.{u}
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras (f ≫ sP))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (deRhamAlgebras (f ≫ sP))))) ⟶
      (sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras sP)
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras sP)))) :=
  letI := HasDerivedCategory.standard (AbelianSheaf X.toRingedSpace.carrier)
  letI := HasDerivedCategory.standard (AbelianSheaf P.toRingedSpace.carrier)
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  haveI := isIso_deRhamPushforwardToDerived_of_isAffineHom f (f ≫ sP)
  (derivedSectionsPushforwardIso f).hom.app
      (DerivedCategory.Plus.Q.obj
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras (f ≫ sP))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ sP))))) ≫
    (sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (inv (deRhamPushforwardToDerived f (f ≫ sP))) ≫
    (sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (deRhamAbelianTraceMapPlus f sP hf))

/-- **The trace map on de Rham cohomology** `Θ_n : H^n_{dR}(X/S) ⟶ H^n_{dR}(P/S)` of a finite
syntomic `f : X ⟶ P` over `sP : P ⟶ S`, in every degree `n`: the map induced on cohomology by
`Stacks.WeilDeRham.deRhamDerivedSectionsTrace`. -/
def deRhamCohomologyTrace (n : ℤ) :
    deRhamCohomology (f ≫ sP) n ⟶ deRhamCohomology sP n :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    (deRhamDerivedSectionsTrace f sP hf)

/-- **The pullback followed by the trace on derived global sections is multiplication by `e`.**
The two identifications of `RΓ(X, -)` cancel, and what is left is `RΓ(P, -)` of the composite
`Ω^•_{P/S} ⟶ f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}`, which is `e • 𝟙`. -/
theorem deRhamDerivedSectionsPullback_comp_deRhamDerivedSectionsTrace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (hcomm : f ≫ sP = (f ≫ sP) ≫ 𝟙 S) :
    deRhamDerivedSectionsPullback f sP (f ≫ sP) (𝟙 S) hcomm ≫
        deRhamDerivedSectionsTrace f sP hf = e • 𝟙 _ := by
  let := HasDerivedCategory.standard (AbelianSheaf X.toRingedSpace.carrier)
  let := HasDerivedCategory.standard (AbelianSheaf P.toRingedSpace.carrier)
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have : (DerivedCategory.Plus.Q (C := AbelianSheaf P.toRingedSpace.carrier)).Additive := by
    have : (DerivedCategory.Plus.Q (C := AbelianSheaf P.toRingedSpace.carrier) ⋙
        DerivedCategory.Plus.ι).Additive :=
      Functor.additive_of_iso (Iso.refl (CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q))
    exact Functor.additive_of_comp_faithful _ DerivedCategory.Plus.ι
  have : (sectionsFunctor P.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.Additive :=
    let := CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
      (sectionsFunctor P.toRingedSpace.carrier ⊤)
    have := CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus
      (sectionsFunctor P.toRingedSpace.carrier ⊤)
    inferInstance
  have := isIso_deRhamPushforwardToDerived_of_isAffineHom f (f ≫ sP)
  have key := deRhamAbelianPushforwardMapPlus_comp_deRhamAbelianTraceMapPlus f sP hf e hcomm
  unfold deRhamDerivedSectionsPullback deRhamDerivedSectionsTrace
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    IsIso.hom_inv_id, Category.comp_id]
  exact map_comp_eq_nsmul_id _ (map_comp_eq_nsmul_id _ key)

/-- **`Θ_n ∘ f^* = e` on de Rham cohomology**, as morphisms of abelian groups. -/
theorem deRhamCohomologyPullback_comp_deRhamCohomologyTrace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (hcomm : f ≫ sP = (f ≫ sP) ≫ 𝟙 S) (n : ℤ) :
    deRhamCohomologyPullback f sP (f ≫ sP) (𝟙 S) hcomm n ≫
        deRhamCohomologyTrace f sP hf n = e • 𝟙 _ :=
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  map_comp_eq_nsmul_id _
    (deRhamDerivedSectionsPullback_comp_deRhamDerivedSectionsTrace f sP hf e hcomm)

/-- **The trace map on de Rham cohomology of a finite syntomic morphism** (Stacks, Section 0FWC,
proof of axiom (A6)). Let `f : X ⟶ P` be a finite syntomic morphism of schemes such that
`f_*𝒪_X` is finite locally free of constant rank `e`, and let `sP : P ⟶ S`. Then for every
`n : ℤ` and every `x ∈ H^n_{dR}(P/S)`, the trace map
`Θ_n : H^n_{dR}(X/S) ⟶ H^n_{dR}(P/S)` satisfies `Θ_n(f^* x) = e • x`, where `f^*` is the
pullback of the square `f ≫ sP = (f ≫ sP) ≫ 𝟙 S`. -/
theorem deRhamCohomologyTrace_deRhamCohomologyPullback
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (hcomm : f ≫ sP = (f ≫ sP) ≫ 𝟙 S) (n : ℤ) (x : deRhamCohomology sP n) :
    (deRhamCohomologyTrace f sP hf n).hom
        ((deRhamCohomologyPullback f sP (f ≫ sP) (𝟙 S) hcomm n).hom x) = e • x :=
  ConcreteCategory.congr_hom
    (deRhamCohomologyPullback_comp_deRhamCohomologyTrace f sP hf e hcomm n) x

include hf in
/-- **A trace map on de Rham cohomology exists for any structure morphism of `X` over `S`.** Let
`f : X ⟶ P` be finite syntomic with `f_*𝒪_X` finite locally free of constant rank `e`, and let
`sP : P ⟶ S`, `sX : X ⟶ S` with `f ≫ sP = sX ≫ 𝟙 S`. Then in every degree `n` there is a map
`Θ_n : H^n_{dR}(X/S) ⟶ H^n_{dR}(P/S)` with `Θ_n(f^* x) = e • x` for all `x`. -/
theorem exists_deRhamCohomologyTrace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ S) (hcomm : f ≫ sP = sX ≫ 𝟙 S) (n : ℤ) :
    ∃ Θ : deRhamCohomology sX n ⟶ deRhamCohomology sP n, ∀ x : deRhamCohomology sP n,
      Θ.hom ((deRhamCohomologyPullback f sP sX (𝟙 S) hcomm n).hom x) = e • x := by
  obtain rfl : sX = f ≫ sP := (Category.comp_id sX).symm.trans hcomm.symm
  exact ⟨deRhamCohomologyTrace f sP hf n,
    deRhamCohomologyTrace_deRhamCohomologyPullback f sP hf e hcomm n⟩

/-! ### Injectivity of the pullback -/

/-- **Multiplication by an integer invertible on the base is injective on de Rham cohomology.**
`H^n_{dR}(Y/T)` is a module over `Γ(T, 𝒪_T)`
(`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyBaseModule`, through the comparison
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology` of the two
realizations, which is additive), and `m • z` is the action of the image of `m` in
`Γ(T, 𝒪_T)`; if that image is a unit, `m • z = 0` forces `z = 0`. -/
theorem eq_zero_of_nsmul_eq_zero {Y T : Scheme.{u}} (p : Y ⟶ T) (n : ℤ) {m : ℕ}
    (hm : IsUnit (m : T.sheaf.obj.obj (Opposite.op ⊤))) {z : deRhamCohomology p n}
    (hz : m • z = 0) : z = 0 := by
  let φ := AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (deRhamAlgebras p) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras p)) n
  let w : deRhamCohomologyBaseModule p n := φ.hom.hom z
  have hw : w = 0 := hm.smul_eq_zero.mp <| by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_nsmul φ.hom.hom m z).symm.trans ((congrArg φ.hom.hom hz).trans (map_zero _))
  exact (ConcreteCategory.congr_hom φ.hom_inv_id z).symm.trans
    ((congrArg φ.inv.hom hw).trans (map_zero _))

include hf in
/-- **The pullback along a finite syntomic morphism of constant rank `e` is injective on de Rham
cohomology when `e` is invertible on the base.** Let `f : X ⟶ P` be finite syntomic with
`f_*𝒪_X` finite locally free of constant rank `e`, let `sP : P ⟶ S` and `sX : X ⟶ S` with
`f ≫ sP = sX ≫ 𝟙 S`, and suppose `e` is a unit of `Γ(S, 𝒪_S)`. Then
`f^* : H^n_{dR}(P/S) ⟶ H^n_{dR}(X/S)` is injective in every degree. -/
theorem injective_deRhamCohomologyPullback
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ S) (hcomm : f ≫ sP = sX ≫ 𝟙 S) (he : IsUnit (e : S.sheaf.obj.obj (Opposite.op ⊤)))
    (n : ℤ) : Function.Injective (deRhamCohomologyPullback f sP sX (𝟙 S) hcomm n).hom := by
  obtain ⟨Θ, hΘ⟩ := exists_deRhamCohomologyTrace f sP hf e sX hcomm n
  refine (injective_iff_map_eq_zero _).2 fun x hx => eq_zero_of_nsmul_eq_zero sP n he ?_
  rw [← hΘ x, hx, map_zero]

/-- A positive integer is a unit in the global sections of the spectrum of a field of
characteristic zero. -/
theorem isUnit_natCast_spec_globalSections (k : Type u) [Field k] [CharZero k] {m : ℕ}
    (hm : m ≠ 0) : IsUnit (m : (Spec (CommRingCat.of k)).sheaf.obj.obj (Opposite.op ⊤)) := by
  have h : IsUnit (m : k) := (Nat.cast_ne_zero.mpr hm).isUnit
  have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  rwa [map_natCast] at h'

include hf in
/-- **The pullback along a finite syntomic morphism of positive constant degree is injective on
de Rham cohomology over a field of characteristic zero** (the consequence used in the proof of
Axiom (A6), Stacks, Section 0FWC). Let `k` be a field of characteristic zero, `f : X ⟶ P` a
finite syntomic morphism of `k`-schemes with `f_*𝒪_X` finite locally free of constant rank
`e ≥ 1`. Then `f^* : H^n_{dR}(P/k) ⟶ H^n_{dR}(X/k)` is injective in every degree. -/
theorem injective_deRhamCohomologyPullback_of_charZero {k : Type u} [Field k] [CharZero k]
    (sP : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]
    (sX : X ⟶ Spec (CommRingCat.of k)) (hcomm : f ≫ sP = sX ≫ 𝟙 _) (he : 1 ≤ e) (n : ℤ) :
    Function.Injective (deRhamCohomologyPullback f sP sX (𝟙 _) hcomm n).hom :=
  injective_deRhamCohomologyPullback f sP hf e sX hcomm
    (isUnit_natCast_spec_globalSections k (Nat.one_le_iff_ne_zero.mp he)) n

end Stacks.WeilDeRham

end
