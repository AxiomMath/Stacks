module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.CompositeCancellation
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeEdgeComparison

/-!
# The crossing of the two models of `Rⁿ(r ∘ w)` under precomposition by an exact functor

`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw αw hres n` is the
crossing of the two models of the classical right derived functor: it identifies `Hⁿ(Rw(X[0]))`,
computed in the unbounded derived category, with Mathlib's `w.rightDerived n` at `X`. For a
composite `r ⋙ w` with `r` exact and preserving injective objects there is a second comparison
in play, `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso r w n :
(r ⋙ w).rightDerived n ≅ r ⋙ w.rightDerived n`, which moves `r` out of the classical derived
functor.

This file proves that the two are compatible: the crossing at `r ⋙ w`, followed by that
comparison, is the degree-`n` cohomology of a comparison `θ : R(r ∘ w) ⟶ r.mapDerivedCategory ∘ Rw`
of the unbounded models, then of `Rw` applied to Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, then the crossing at `w` alone,
evaluated at `r X`. It is the **pre**composition counterpart of
`Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv` and of
`Stacks.Cohomology.AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`,
which both move a functor out on the right.

Nothing is assumed of `w` beyond additivity, and nothing of the object.

## Main results

* `Stacks.Cohomology.DerivedCompTransport.mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app`
  `_comp_factorsh`: the purely Mathlib-level identity on the single functors — `r` applied to the
  comparison of `X[0]` with `Qh(X[0])`, followed by the factorisation of `r.mapDerivedCategory`
  through the homotopy category, is `mapDerivedCategorySingleFunctor`, the same comparison
  downstairs, and `HomologicalComplex.singleMapHomologicalComplex` inverted.
* `Stacks.Cohomology.DerivedCompTransport.mapDerivedCategory_map_singleIsoResCompQh_hom_app_comp`
  `_factorsh`: the same with the chosen extended injective resolutions in place of the single
  complexes, the comparison of the resolutions being
  `Stacks.DerivedIndexing.extendResolutionComparison`.
* `Stacks.Cohomology.DerivedCompTransport.isIso_unit_app_mapHomotopyCategory_resH_obj`: **the unit
  of `Rw` is invertible at `r` applied to the chosen extended resolution.**
* `Stacks.Cohomology.DerivedCompTransport.map_singleIsoResCompQh_hom_app_comp_resCompUnitIso_inv`
  `_app`: the derived half of the compatibility, an identity in `D(ℬ)`.
* `Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso`
  `_hom`: **the compatibility itself.**

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

universe vC uC vA uA vB uB

/-! ### The chases, at variables -/

section Abstract

variable {V : Type*} [Category* V]

/-- **A leading cancelling pair under a functor and a trailing identity, both removed.** -/
private theorem map_head_cancel_tail_id {W : Type*} [Category* W] (H : V ⥤ W)
    {P₁ P₂ : V} (i : P₁ ⟶ P₂) (j : P₂ ⟶ P₁) (hij : i ≫ j = 𝟙 P₁)
    {R S : W} (b : H.obj P₁ ⟶ R) (c : R ⟶ S) (z : S ⟶ S) (hz : z = 𝟙 S) :
    H.map i ≫ H.map j ≫ b ≫ c ≫ z = b ≫ c := by
  rw [← H.map_comp_assoc, hij]
  simp [hz]

/-- **A morphism solved for out of a known composite with an invertible left factor.** -/
private theorem eq_comp_of_inv_comp {P₁ P₂ R : V} {i : P₁ ⟶ P₂} {ii : P₂ ⟶ P₁}
    (h : i ≫ ii = 𝟙 P₁) {f : P₁ ⟶ R} {g : P₂ ⟶ R} (hf : ii ≫ f = g) : f = i ≫ g := by
  subst hf
  simp [reassoc_of% h]

/-- **A commuting square followed by a cancelling pair.** -/
private theorem comp_square_cancel {P Q R S T : V}
    (a : P ⟶ Q) {b : Q ⟶ R} {c : R ⟶ S} {e : Q ⟶ T} {f : T ⟶ S} {d : S ⟶ T}
    (h : b ≫ c = e ≫ f) (hfd : f ≫ d = 𝟙 T) :
    a ≫ b ≫ c ≫ d = a ≫ e := by
  simp [reassoc_of% h, hfd]

/-- **Two commuting squares and one computed composite, glued.** -/
private theorem chase_two_squares {P Q R S T U W' T' : V}
    {u₁ : P ⟶ Q} {u₂ : Q ⟶ R} {φ₂ : R ⟶ S} {φ₁ : Q ⟶ T} {v : T ⟶ S}
    {k₁ : P ⟶ U} {k₂ : U ⟶ W'} {k₃ : W' ⟶ T} {e₁ : W' ⟶ T'} {e₂ : T' ⟶ S}
    (hnat : u₂ ≫ φ₂ = φ₁ ≫ v) (hsingle : u₁ ≫ φ₁ = k₁ ≫ k₂ ≫ k₃)
    (hcomp : k₃ ≫ v = e₁ ≫ e₂)
    {a : P ⟶ R} (ha : a = u₁ ≫ u₂) {b : U ⟶ T'} (hb : b = k₂ ≫ e₁) :
    a ≫ φ₂ = k₁ ≫ b ≫ e₂ := by
  subst ha hb
  simp [hnat, reassoc_of% hsingle, hcomp]

/-- **A morphism cancelled off the right of an equation**, with the invertibility given on plain
morphisms. -/
private theorem cancel_right {P Q R : V} {f g : P ⟶ Q} {u : Q ⟶ R} {ui : R ⟶ Q}
    (hu : u ≫ ui = 𝟙 Q) (h : f ≫ u = g ≫ u) : f = g := by
  simpa [hu] using h =≫ ui

/-- **An inverse against a known naturality square.** From `ii ≫ i = 𝟙` and `x ≫ y = i ≫ z`,
`ii ≫ x ≫ y = z`. -/
private theorem inv_comp_square {P Q R S : V} {ii : P ⟶ Q} {i : Q ⟶ P}
    (h : ii ≫ i = 𝟙 P) {x : Q ⟶ R} {y : R ⟶ S} {z : P ⟶ S} (hx : x ≫ y = i ≫ z) :
    ii ≫ x ≫ y = z := by
  rw [hx, reassoc_of% h]

/-- **The left-hand chain of the derived half.** A composite through a cancelling pair `ii`, `i`,
rewritten by the square `hth` (with a leading factor known to be an identity), the square `hnat`
and the factorisation `hI`. -/
private theorem derived_left {W : Type*} [Category* W] (H : W ⥤ V)
    {Y₀ Y₁ Y₂ Z₁ Z₂ : W} {f : Y₀ ⟶ Y₁} {g : Y₁ ⟶ Y₂} {gi : Y₂ ⟶ Y₁}
    {c₁ : Y₀ ⟶ Z₁} {c₂ : Z₁ ⟶ Z₂} {c₃ : Z₂ ⟶ Y₂}
    {P₀ P₁ P₂ : V} {a : P₀ ⟶ P₁} {ii : P₁ ⟶ P₂} {i : P₂ ⟶ P₁} {u : P₂ ⟶ H.obj Y₂}
    {t : P₀ ⟶ H.obj Y₀} {th : P₁ ⟶ H.obj Y₁} {z : P₂ ⟶ P₂}
    (hii : ii ≫ i = 𝟙 P₁) (hz : z = 𝟙 P₂) (hth : i ≫ th = z ≫ u ≫ H.map gi)
    (hgi : gi ≫ g = 𝟙 Y₂) (hnat : a ≫ th = t ≫ H.map f) (hI : f ≫ g = c₁ ≫ c₂ ≫ c₃) :
    (a ≫ ii) ≫ u = t ≫ H.map c₁ ≫ H.map c₂ ≫ H.map c₃ := by
  subst hz
  have hH : ii ≫ u = th ≫ H.map g := by
    simpa [reassoc_of% hii, CategoryTheory.map_comp_cancel H hgi] using
      (ii ≫= hth =≫ H.map g).symm
  rw [Category.assoc, hH, reassoc_of% hnat, ← H.map_comp, hI]
  simp

/-- **The right-hand chain of the derived half.** A trailing composite `n₂ ≫ mq ≫ u` replaced by
the image of `c₃`. -/
private theorem derived_right {W : Type*} [Category* W] (H : W ⥤ V)
    {Y₀ Z₁ Z₂ Y₂ : W} {c₁ : Y₀ ⟶ Z₁} {c₂ : Z₁ ⟶ Z₂} {c₃ : Z₂ ⟶ Y₂}
    {P₀ P₂ P₄ : V} {t : P₀ ⟶ H.obj Y₀} {n₂ : H.obj Z₂ ⟶ P₄} {mq : P₄ ⟶ P₂}
    {u : P₂ ⟶ H.obj Y₂} (hUc : n₂ ≫ mq ≫ u = H.map c₃) :
    (t ≫ H.map c₁ ≫ H.map c₂ ≫ n₂ ≫ mq) ≫ u =
      t ≫ H.map c₁ ≫ H.map c₂ ≫ H.map c₃ := by
  simp [hUc]

/-- **A two-fold composite identified with a five-fold one, carried under a functor.** -/
private theorem map_chain_five {W : Type*} [Category* W] (H : V ⥤ W)
    {P₀ P₁ P₂ Q₁ Q₂ Q₃ Q₄ : V} {a : P₀ ⟶ P₁} {b : P₁ ⟶ P₂}
    {t : P₀ ⟶ Q₁} {c₁ : Q₁ ⟶ Q₂} {c₂ : Q₂ ⟶ Q₃} {c₃ : Q₃ ⟶ Q₄} {c₄ : Q₄ ⟶ P₂}
    (h : a ≫ b = t ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄) :
    H.map a ≫ H.map b = H.map t ≫ H.map c₁ ≫ H.map c₂ ≫ H.map c₃ ≫ H.map c₄ := by
  simpa using H.congr_map h

/-- **The residue.** Given `e ≫ h = g ≫ m` with `e`, `h` and `g` invertible,
`m ≫ h⁻¹ ≫ e⁻¹ = g⁻¹`. -/
private theorem residue_cancel {P Q R S : V} {e : P ⟶ Q} {ei : Q ⟶ P} (hei : e ≫ ei = 𝟙 P)
    {h : Q ⟶ S} {hi : S ⟶ Q} (hhi : h ≫ hi = 𝟙 Q)
    {g : P ⟶ R} {gi : R ⟶ P} (hgi : gi ≫ g = 𝟙 R)
    {m : R ⟶ S} (hm : e ≫ h = g ≫ m) :
    m ≫ hi ≫ ei = gi := by
  obtain rfl := eq_comp_of_inv_comp hgi hm.symm
  simp [reassoc_of% hhi, hei]

/-- **The outer assembly.** Three equations `hD`, `hNat` and `hRes` glued along their common
factors. -/
private theorem glue_final {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ : V}
    {a₁ : P₀ ⟶ P₁} {a₂ : P₁ ⟶ P₂} {fs : P₂ ⟶ P₃} {hi : P₃ ⟶ P₄} {ei : P₄ ⟶ P₅}
    {t₁ : P₀ ⟶ Q₁} {t₂ : Q₁ ⟶ Q₂} {b₁ : Q₂ ⟶ Q₃} {b₂ : Q₃ ⟶ Q₄} {mm : Q₄ ⟶ P₂}
    {gs : Q₄ ⟶ Q₅} {m : Q₅ ⟶ P₃} {gi : Q₅ ⟶ P₅}
    (hD : a₁ ≫ a₂ = t₁ ≫ t₂ ≫ b₁ ≫ b₂ ≫ mm) (hNat : mm ≫ fs = gs ≫ m)
    (hRes : m ≫ hi ≫ ei = gi) :
    (a₁ ≫ a₂ ≫ fs ≫ hi) ≫ ei = t₁ ≫ t₂ ≫ b₁ ≫ b₂ ≫ gs ≫ gi := by
  simp [reassoc_of% hD, reassoc_of% hNat, hRes]

end Abstract

/-! ### The single-functor identities -/

section Single

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]
  {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  (r : C ⥤ A) [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [r.PreservesInjectiveObjects]

omit [EnoughInjectives C] [EnoughInjectives A] [r.PreservesInjectiveObjects] in
/-- **The Mathlib-level identity on the single functors.** `r.mapDerivedCategory` applied to the
comparison of `X[0]` with the localization of the single complex, followed by the factorisation of
`r.mapDerivedCategory` through the homotopy category, is
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, the same comparison downstairs, and the
image of `HomologicalComplex.singleMapHomologicalComplex` inverted. -/
theorem mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app_comp_factorsh (X : C) :
    r.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X) ≫
        r.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) =
      (r.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app (r.obj X) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex r
              (ComplexShape.up ℤ) 0).inv.app X)) := by
  rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app,
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
  have hz : DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((CochainComplex.singleFunctor C 0).obj X)) = 𝟙 _ := DerivedCategory.Qh.map_id _
  refine ((congrArg
      (fun g => r.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app
        ((CochainComplex.singleFunctor C 0).obj X)) ≫ g)
      (Functor.mapDerivedCategoryFactorsh_hom_app r
        ((CochainComplex.singleFunctor C 0).obj X))).trans
    (map_head_cancel_tail_id r.mapDerivedCategory _ _
      ((DerivedCategory.quotientCompQhIso C).inv_hom_id_app
        ((CochainComplex.singleFunctor C 0).obj X))
      (r.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X))
      ((DerivedCategory.quotientCompQhIso A).inv.app
        ((r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj X))) _ hz)).trans ?_
  have hsingle : (r.mapDerivedCategorySingleFunctor 0).hom.app X =
      r.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Q.map ((r.mapCochainComplexSingleFunctor 0).hom.app X) :=
    eq_comp_of_inv_comp
      (r.mapDerivedCategoryFactors.hom_inv_id_app ((CochainComplex.singleFunctor C 0).obj X))
      (Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app r X)
  rw [hsingle, Category.assoc]
  exact (comp_square_cancel
    (r.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X))
    (DerivedCategory.quotientCompQhIso_inv_naturality
      ((r.mapCochainComplexSingleFunctor 0).hom.app X))
    (CategoryTheory.map_comp_cancel DerivedCategory.Qh
      (CategoryTheory.map_comp_cancel (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        ((HomologicalComplex.singleMapHomologicalComplex r
          (ComplexShape.up ℤ) 0).hom_inv_id_app X)))).symm

/-- **The same identity at the chosen extended injective resolutions.** `r.mapDerivedCategory`
applied to the identification of `X[0]` with the localization of the chosen extended resolution,
followed by the factorisation of `r.mapDerivedCategory` through the homotopy category, is
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, the identification downstairs at `r X`,
and the comparison `Stacks.DerivedIndexing.extendResolutionComparison` of the two resolutions. -/
theorem mapDerivedCategory_map_singleIsoResCompQh_hom_app_comp_factorsh (X : C) :
    r.mapDerivedCategory.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X) ≫
        r.mapDerivedCategoryFactorsh.hom.app (Stacks.DerivedIndexing.resH.obj X) =
      (r.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (r.obj X) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (Stacks.DerivedIndexing.extendResolutionComparison r X)) :=
  chase_two_squares
    (r.mapDerivedCategoryFactorsh.hom.naturality (Stacks.DerivedIndexing.resUnit.app X))
    (mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app_comp_factorsh r X)
    ((DerivedCategory.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Qh.map
        (Stacks.DerivedIndexing.resUnit_app_comp_quotient_map_extendResolutionComparison
          r X).symm).trans (DerivedCategory.Qh.map_comp _ _)))
    (r.mapDerivedCategory.map_comp ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X)
      (DerivedCategory.Qh.map (Stacks.DerivedIndexing.resUnit.app X)))
    rfl

end Single

/-! ### The compatibility -/

section Crossing

variable {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]
  {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  (r : C ⥤ A) [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [r.PreservesInjectiveObjects]
  (w : A ⥤ B) [w.Additive]
  (Rrw : DerivedCategory C ⥤ DerivedCategory B)
  (αrw : (r ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rrw)
  [Rrw.IsRightDerivedFunctor αrw (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (αw : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor αw (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (θ : Rrw ⟶ r.mapDerivedCategory ⋙ Rw)

omit [HasDerivedCategory C] [EnoughInjectives A] in
/-- **The unit of `Rw` is invertible at `r` applied to the chosen extended injective resolution of
an object**, provided K-injective resolutions exist in `A`. -/
theorem isIso_unit_app_mapHomotopyCategory_resH_obj
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : C) :
    IsIso (αw.app ((r.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      (Stacks.DerivedIndexing.resH.obj X))) := by
  have h₁ : CochainComplex.IsKInjective
      (((r.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex).extend ComplexShape.embeddingUpNat) :=
    CochainComplex.isKInjective_of_injective
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes r
        (injectiveResolution X)).cochainComplex 0
  have hK : CochainComplex.IsKInjective
      ((r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex) :=
    CochainComplex.isKInjective_of_iso
      (Stacks.DerivedIndexing.mapExtendIso r ComplexShape.embeddingUpNat
        (injectiveResolution X).cocomplex)
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresA).2
      DerivedCategory.Qh Rw αw _ hK

/-- **The derived half of the compatibility, in `D(ℬ)`.** `R(r ∘ w)` applied to the identification
of `X[0]` with the localization of the chosen extended resolution, followed by the unit of
`R(r ∘ w)` there inverted, is `θ` at `X[0]`, then `Rw` of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and of the identification downstairs at
`r X`, then the unit of `Rw` inverted, then `w` applied to the comparison of the two chosen
resolutions. -/
theorem map_singleIsoResCompQh_hom_app_comp_resCompUnitIso_inv_app
    (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory C (ComplexShape.up ℤ),
      αrw.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ w))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αw.app ((r.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          Rw.map (r.mapDerivedCategoryFactorsh.inv.app L))
    (X : C) :
    Rrw.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X) ≫
        (Stacks.DerivedFunctor.resCompUnitIso (r ⋙ w) Rrw αrw hresC).inv.app X =
      θ.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        Rw.map ((r.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
          Rw.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (r.obj X)) ≫
            (Stacks.DerivedFunctor.resCompUnitIso w Rw αw hresA).inv.app (r.obj X) ≫
              DerivedCategory.Qh.map ((w.mapHomotopyCategory (ComplexShape.up ℤ)).map
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
                  (Stacks.DerivedIndexing.extendResolutionComparison r X))) := by
  have := isIso_unit_app_mapHomotopyCategory_resH_obj r w Rw αw hresA X
  refine cancel_right (IsIso.hom_inv_id
    (f := αw.app ((r.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      (Stacks.DerivedIndexing.resH.obj X)))) ?_
  refine (derived_left Rw
    ((Stacks.DerivedFunctor.resCompUnitIso (r ⋙ w) Rrw αrw hresC).inv_hom_id_app X)
    (DerivedCategory.Qh.map_id _)
    (hθ (Stacks.DerivedIndexing.resH.obj X))
    (r.mapDerivedCategoryFactorsh.inv_hom_id_app (Stacks.DerivedIndexing.resH.obj X))
    (θ.naturality ((Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X))
    (mapDerivedCategory_map_singleIsoResCompQh_hom_app_comp_factorsh r X)).trans ?_
  exact (derived_right Rw
    (inv_comp_square
      ((Stacks.DerivedFunctor.resCompUnitIso w Rw αw hresA).inv_hom_id_app (r.obj X))
      (αw.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (Stacks.DerivedIndexing.extendResolutionComparison r X))))).symm

/-- **The crossing of the two models of `Rⁿ(r ∘ w)` is compatible with moving `r` out of the
classical right derived functor.** For `r : C ⥤ A` exact, additive and preserving injective
objects, `w : A ⥤ B` additive, unbounded right derived functors `Rrw` and `Rw` of the two
degreewise functors, and a comparison `θ : Rrw ⟶ r.mapDerivedCategory ⋙ Rw` satisfying the
factorisation `hθ` that characterises it,

> the crossing of the two models at `r ⋙ w`, followed by
> `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, is the degree-`n` cohomology
> of `θ` at `X[0]`, then of `Rw` applied to
> `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, then the crossing of the two models
> at `w` alone, evaluated at `r X`. -/
theorem singleCompDerived_hom_app_comp_compRightDerivedNatIso_hom
    (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory C (ComplexShape.up ℤ),
      αrw.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ w))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αw.app ((r.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          Rw.map (r.mapDerivedCategoryFactorsh.inv.app L))
    (n : ℕ) (X : C) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (r ⋙ w) Rrw αrw
            hresC n).hom.app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso r w n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (θ.app ((DerivedCategory.singleFunctor C 0).obj X)) ≫
        (DerivedCategory.homologyFunctor B (n : ℤ)).map
            (Rw.map ((r.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw αw
            hresA n).hom.app (r.obj X) := by
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res
      (r ⋙ w) Rrw αrw hresC n X,
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res
      w Rw αw hresA n (r.obj X)]
  exact glue_final
    (map_chain_five (DerivedCategory.homologyFunctor B (n : ℤ))
      (map_singleIsoResCompQh_hom_app_comp_resCompUnitIso_inv_app r w Rrw αrw Rw αw θ
        hresC hresA hθ X))
    ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.naturality
      ((w.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (Stacks.DerivedIndexing.extendResolutionComparison r X))))
    (residue_cancel
      (edge_app_comp_compRightDerivedNatIso_hom_app r w n X)
      ((Stacks.DerivedIndexing.rightDerivedIsoRes (r ⋙ w) n).hom_inv_id_app X)
      ((Stacks.DerivedIndexing.rightDerivedIsoRes w n).inv_hom_id_app (r.obj X))
      (Stacks.DerivedIndexing.edge_comp_rightDerivedIsoRes r w n X))

end Crossing

end Stacks.Cohomology.DerivedCompTransport

end
