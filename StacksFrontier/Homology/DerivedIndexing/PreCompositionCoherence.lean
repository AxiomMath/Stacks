module

public import
  StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompCoherence
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` carries pre-composition to the composite comparison

Let `C`, `A`, `B` be abelian categories, `C` and `A` with enough injectives and all three with
unbounded derived categories, let `F : C ⥤ A` be additive, exact and preserving injective
objects, and let `w : A ⥤ B` be additive. Let `Rw : D(A) ⥤ D(B)` with unit `α` be a right
derived functor of `w` on the unbounded derived category, and let `F.mapDerivedCategory ⋙ Rw`,
with the unit assembled from `α` and the factorization
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `F.mapDerivedCategory` through the
homotopy category, be a right derived functor of `F ⋙ w`.

Both sides of `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` then carry a
comparison between the datum for `F ⋙ w` and the datum for `w` read at `F X`: on the derived
side the single-functor comparison
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, and on the classical side
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`. **They agree**; that is
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`.

This is one of the three coherences a comparison of an excision statement proved in the
unbounded derived category with one proved from Mathlib's `CategoryTheory.Functor.rightDerived`
needs — the one for *pre-composition with an exact functor preserving injectives*, as opposed to
the one for the degreewise comparison itself
(`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality`) and the one for
post-composition. The implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record all three; this file
supplies this one.

## Main definitions

* `Stacks.DerivedIndexing.extendResolutionComparisonQh`: the comparison of the chosen extended
  injective resolution of `F X` with `F` applied to the chosen extended injective resolution of
  `X`, read in `D(A)` and composed with the factorization of `F.mapDerivedCategory` through the
  homotopy category, so that it lands at `F.mapDerivedCategory` of the resolution of `X`.

## Main results

* `Stacks.DerivedIndexing.mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh`:
  **the single-functor comparison of `F.mapDerivedCategory`, read through the two
  identifications of the single functors with the single functors into the homotopy category, is
  the factorization of `F.mapDerivedCategory` through the homotopy category.** No injectives and
  no resolutions are involved; this is the `Qh`-level form of the `Q`-level definition of
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.
* `Stacks.DerivedIndexing.mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh`: **the
  augmentation square**: the single-functor comparison followed by the augmentation of the
  chosen resolution of `F X` and by `extendResolutionComparisonQh` is `F.mapDerivedCategory`
  applied to the augmentation of the chosen resolution of `X`. This is the unbounded form of
  `Stacks.DerivedIndexing.singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus`, the
  identity (S2) of `StacksFrontier.Homology.DerivedIndexing.Composite`.
* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp_app`,
  `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`: **the
  coherence**, componentwise and as an equality of natural transformations.

## Implementation notes

**What the proof is.** Four squares, pasted:

* the augmentation square `mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh`, which is
  where all the content about resolutions sits;
* the naturality of `α` at the comparison of the two resolutions, which together with the
  hypothesis `hα'` that the unit of `F.mapDerivedCategory ⋙ Rw` is the composite of `α` with
  `mapDerivedCategoryFactorsh` is the whole of the derived-functor content — *no invertibility of
  `α` at `F` applied to a resolution is needed*, only invertibility at the two chosen
  resolutions, which `Stacks.DerivedFunctor.resCompUnitIso` provides;
* the naturality of `CategoryTheory.DerivedCategory.homologyFunctorFactorsh`; and
* `Stacks.DerivedIndexing.compRightDerivedNatIso_inv_app_comp_rightDerivedIsoRes`, the classical
  half, already proved in
  `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompCoherence`.

The middle two are free. So the coherence does *not* need the identification, for a derived
functor taken as data, of the unit on the unbounded derived category with
`Stacks.DerivedIndexing.extendResolutionComparison` that the implementation notes of
`RightDerivedCompCoherence` named as the missing half: that identification is what one would
need if `α'` were produced by the universal property rather than written down, and the
formulation here writes it down.

**The unit is a hypothesis, not a construction.** `α'` and the statement that
`F.mapDerivedCategory ⋙ Rw` is a right derived functor of `F ⋙ w` for it are arguments, with
`hα'` pinning `α'` componentwise. Writing `α'` as a composite of whiskerings instead would need
`(F ⋙ w).mapHomotopyCategory c` and `F.mapHomotopyCategory c ⋙ w.mapHomotopyCategory c` to be
interchangeable as *functors* — they are not even propositionally equal in the library, only
pointwise so — and `CategoryTheory.Functor.comp` carries universe arguments for the intermediate
category which the two bracketings of a triple composite instantiate differently. Both obstacles
disappear once the only thing asked of `α'` is its components.

**Transparency.** `HomotopyCategory.singleFunctor C 0` and the quotient of the single cochain
complex, `Stacks.DerivedIndexing.resH` and the quotient of the chosen resolution, and
`(F ⋙ w).mapHomotopyCategory c` and `F.mapHomotopyCategory c ⋙ w.mapHomotopyCategory c` on
objects, are all definitionally but not syntactically equal, so `rw` and `simp only` fail on
goals stated with one spelling and lemmas stated with the other: the rewrite motive is not
type-correct at `implicit` transparency. Every chase here is therefore a private lemma at a
variable category with the objects implicit and the morphisms explicit, applied with `exact`,
which unifies at default transparency and never matches a pattern against the goal.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.DerivedIndexing

universe wC wA wB vC vA vB uC uA uB

/-! ### The chases -/

/-- Two factorizations of one morphism, the second of which ends in an isomorphism. Stated at an
arbitrary category with the objects implicit and the morphisms explicit. -/
private lemma comp_inv_of_comm {E : Type*} [Category* E] {P₀ P₂ P₃ P₄ P₅ : E}
    (m : P₀ ⟶ P₂) (g₁ : P₂ ⟶ P₃) (g₂ : P₃ ⟶ P₄) (d : P₀ ⟶ P₅) (h : P₅ ≅ P₄)
    (hcomm : m ≫ g₁ ≫ g₂ = d ≫ h.hom) : m ≫ g₁ ≫ g₂ ≫ h.inv = d := by
  rw [← Category.assoc g₁ g₂ h.inv, ← Category.assoc m (g₁ ≫ g₂) h.inv, Iso.comp_inv_eq]
  exact hcomm

/-- A morphism computed from its composite with an isomorphism. Stated at an arbitrary category
with the objects implicit and the morphisms explicit. -/
private lemma eq_comp_inv {E : Type*} [Category* E] {P₄ P₅ P₆ : E}
    (h : P₅ ⟶ P₄) (e : P₄ ≅ P₆) (g : P₅ ⟶ P₆) (hcomm : h ≫ e.hom = g) : h = g ≫ e.inv := by
  rw [← hcomm, Category.assoc, e.hom_inv_id, Category.comp_id]


/-- The chase behind `mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh`:
`m` factors as `a ≫ b`, the pair `(b, i)` commutes with `(j, p)`, `p` is a section of `q` and
`d` of `d'`, and `h` is computed. Stated at an arbitrary category with the objects implicit and
the morphisms explicit. -/
private lemma single_chase {E : Type*} [Category* E] {P₀ P₁ P₂ P₃ P₄ P₅ : E}
    (m : P₀ ⟶ P₂) (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (i : P₂ ⟶ P₃) (q : P₃ ⟶ P₄) (j : P₁ ⟶ P₄)
    (p : P₄ ⟶ P₃) (d : P₀ ⟶ P₅) (d' : P₅ ⟶ P₀) (h : P₅ ⟶ P₄)
    (hm : m = a ≫ b) (hnat : b ≫ i = j ≫ p) (hpq : p ≫ q = 𝟙 P₄) (hd : d ≫ d' = 𝟙 P₀)
    (hh : h = (d' ≫ a) ≫ j) :
    m ≫ i ≫ q = d ≫ h := by
  have hL : m ≫ i ≫ q = a ≫ j := by
    rw [hm, Category.assoc, ← Category.assoc b i q, hnat, Category.assoc, hpq, Category.comp_id]
  have hR : d ≫ h = a ≫ j := by
    rw [hh, ← Category.assoc, ← Category.assoc, hd, Category.id_comp]
  rw [hL, hR]

/-- The chase behind `mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh`: the augmentation
of the resolution of `F X` commutes past the comparison of the resolutions, the factorization
through the homotopy category is natural in the complex, and the single-functor coherence
`single_chase` has already been applied. Stated at an arbitrary category with the objects
implicit and the morphisms explicit. -/
private lemma augmentation_chase {E : Type*} [Category* E] {T₀ T₂ T₃ T₄ T₅ R₃ R₄ R₅ : E}
    (m : T₀ ⟶ T₂) (i : T₂ ⟶ T₃) (ruA : T₃ ⟶ R₃) (ψ : R₃ ⟶ R₄) (fr : R₄ ⟶ R₅)
    (smq : T₃ ⟶ T₄) (ru' : T₄ ⟶ R₄) (fs : T₄ ⟶ T₅) (d : T₀ ⟶ T₅) (e : T₅ ⟶ R₅)
    (hψ : ruA ≫ ψ = smq ≫ ru') (hfr : ru' ≫ fr = fs ≫ e)
    (h0 : m ≫ i ≫ smq ≫ fs = d) :
    m ≫ (i ≫ ruA) ≫ ψ ≫ fr = d ≫ e := by
  have h : m ≫ (i ≫ ruA) ≫ ψ ≫ fr = (m ≫ i ≫ smq ≫ fs) ≫ e := by
    simp only [Category.assoc]
    rw [← Category.assoc ruA ψ fr, hψ, Category.assoc, hfr]
  rw [h, h0]

/-- The chase behind the naturality of the unit at the comparison of the two resolutions: the
unit of the composite is the unit of the outer functor followed by the factorization of the inner
one, and the unit of the outer functor is natural. Stated at an arbitrary category with the
objects implicit and the morphisms explicit. -/
private lemma unit_chase {E : Type*} [Category* E] {U₀ U₁ U₂ U₃ U₄ : E}
    (a : U₀ ⟶ U₁) (p : U₁ ⟶ U₂) (f : U₂ ⟶ U₃) (gg : U₀ ⟶ U₄) (a' : U₄ ⟶ U₂) (u : U₄ ⟶ U₃)
    (hnat : gg ≫ a' = a ≫ p) (hu : u = a' ≫ f) : a ≫ p ≫ f = gg ≫ u := by
  rw [hu, ← Category.assoc, ← hnat, Category.assoc]

/-- A commuting square of isomorphisms read as a computation of one inverse. Stated at an
arbitrary category with the objects implicit and the morphisms explicit. -/
private lemma comm_to_inv {E : Type*} [Category* E] {P₃ P₄ Q₃ Q₄ : E}
    (r : Q₄ ≅ Q₃) (r' : P₄ ≅ P₃) (cn : P₄ ≅ Q₄) (c : Q₃ ⟶ P₃)
    (h : cn.inv ≫ r'.hom = r.hom ≫ c) : c ≫ r'.inv ≫ cn.hom = r.inv := by
  rw [← cancel_epi r.hom, ← Category.assoc, ← h, Category.assoc, r'.hom_inv_id_assoc,
    cn.inv_hom_id, r.hom_inv_id]

/-- Four squares pasted, in the shape in which
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app` produces the two
sides: the leftmost square is the computation of `a₁`, the two middle ones are honest squares and
the rightmost is the computation of `b₄`. Stated at an arbitrary category with the objects
implicit and the morphisms explicit. -/
private lemma paste_ladder {E : Type*} [Category* E] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : E}
    (v₀ : X₀ ⟶ Y₀) (v₄ : X₄ ⟶ Y₄) (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄)
    (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₄ : Y₃ ⟶ Y₄)
    (c₁ : Y₁ ⟶ X₁) (c₂ : Y₂ ⟶ X₂) (c₃ : Y₃ ⟶ X₃)
    (h₁ : v₀ ≫ b₁ ≫ c₁ = a₁) (h₂ : c₁ ≫ a₂ = b₂ ≫ c₂) (h₃ : c₂ ≫ a₃ = b₃ ≫ c₃)
    (h₄ : c₃ ≫ a₄ ≫ v₄ = b₄) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ v₄ = v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ := by
  have e₃ : c₂ ≫ a₃ ≫ a₄ ≫ v₄ = b₃ ≫ c₃ ≫ a₄ ≫ v₄ := by
    rw [← Category.assoc, h₃, Category.assoc]
  have e₂ : c₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ v₄ = b₂ ≫ b₃ ≫ c₃ ≫ a₄ ≫ v₄ := by
    rw [← Category.assoc, h₂, Category.assoc, e₃]
  have e₁ : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ v₄ = v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ c₃ ≫ a₄ ≫ v₄ := by
    rw [← h₁, Category.assoc, Category.assoc, e₂]
  simp only [Category.assoc]
  rw [e₁, h₄]

/-! ### The single-functor coherence -/

section SingleFunctor

variable {C : Type uC} {A : Type uA} [Category.{vC} C] [Category.{vA} A]
  [Abelian C] [Abelian A] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The components of `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` in degree zero.
Mathlib builds it as a seven-fold `CategoryTheory.Iso.trans` four of whose factors are
reassociations and two of whose factors are the identity isomorphism
`CategoryTheory.DerivedCategory.singleFunctorIsoCompQ`; all six contribute identity morphisms,
which are removed here. The same computation is private in
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso` and in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ExactFunctorSingleHomology`, so it is
copied rather than imported. -/
private lemma mapDerivedCategorySingleFunctor_zero_hom_app (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) :=
  (show (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategory.map (𝟙 _) ≫ 𝟙 _ ≫
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫ 𝟙 _ ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) ≫
            𝟙 _ ≫ 𝟙 _ from rfl).trans (by simp)

/-- **The single-functor comparison of `F.mapDerivedCategory`, read at the homotopy category.**
Composing `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` with the identification of the
single functor into `D(A)` with the single functor into `K(A)` followed by `Qh`, and with the
termwise comparison `HomologicalComplex.singleMapHomologicalComplex` of `F` applied to a single
complex, gives the factorization
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `F.mapDerivedCategory` through the
homotopy category, precomposed with the same identification on the source side.

Both sides are morphisms `F.mapDerivedCategory(X[0]) ⟶ Qh(F(X[0]))` in `D(A)`; neither
injectives nor resolutions are involved. -/
theorem mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app (F.obj X) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) 0).inv.app X)) =
      F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) := by
  have hpq : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).hom.app X)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).inv.app X)) = 𝟙 _ := by
    simp
  have hd : F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
        ((CochainComplex.singleFunctor C 0).obj X)) = 𝟙 _ := by
    rw [singleFunctorIsoCompQh_hom_app]
    exact (F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app
      ((CochainComplex.singleFunctor C 0).obj X))).inv_hom_id
  refine single_chase ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
    (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X))
    (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X))
    ((DerivedCategory.singleFunctorIsoCompQh A 0).hom.app (F.obj X))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X)))
    ((DerivedCategory.quotientCompQhIso A).inv.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj X)))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X)))
    (F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X))
    (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
      ((CochainComplex.singleFunctor C 0).obj X)))
    (F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X))
    (mapDerivedCategorySingleFunctor_zero_hom_app F X) ?_ hpq hd ?_
  · rw [singleFunctorIsoCompQh_hom_app]
    exact (DerivedCategory.quotientCompQhIso A).inv.naturality _
  · exact (Iso.eq_comp_inv ((DerivedCategory.quotientCompQhIso A).app _)).2
      (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso F
        ((CochainComplex.singleFunctor C 0).obj X))

end SingleFunctor

/-! ### The augmentation square -/

section Augmentation

variable {C : Type uC} {A : Type uA} [Category.{vC} C] [Category.{vA} A]
  [Abelian C] [Abelian A] [EnoughInjectives C] [EnoughInjectives A]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]

/-- **The comparison of the chosen extended injective resolutions, read in `D(A)`.** The class in
`D(A)` of `Stacks.DerivedIndexing.extendResolutionComparison`, followed by the factorization of
`F.mapDerivedCategory` through the homotopy category, so that it is a morphism from the chosen
resolution of `F X` to `F.mapDerivedCategory` of the chosen resolution of `X`. -/
def extendResolutionComparisonQh (X : C) :
    DerivedCategory.Qh.obj (resH.obj (F.obj X)) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj (resH.obj X)) :=
  DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (extendResolutionComparison F X)) ≫
    F.mapDerivedCategoryFactorsh.inv.app (resH.obj X)

/-- The components of `Stacks.DerivedFunctor.singleIsoResCompQh`: the identification of the
single functor with the single functor into the homotopy category, followed by the augmentation
of the chosen extended injective resolution. -/
private lemma singleIsoResCompQh_hom_app (X : C) :
    (Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X =
      (DerivedCategory.quotientCompQhIso C).inv.app
          ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Qh.map (resUnit.app X) :=
  congrArg (fun z => z ≫ DerivedCategory.Qh.map (resUnit.app X))
    (singleFunctorIsoCompQh_hom_app 0 X)

/-- **The augmentation square.** The single-functor comparison of `F.mapDerivedCategory`,
followed by the augmentation of the chosen extended injective resolution of `F X` and then by the
comparison of that resolution with `F` applied to the chosen resolution of `X`, is
`F.mapDerivedCategory` applied to the augmentation of the chosen resolution of `X`.

This is the unbounded form of
`Stacks.DerivedIndexing.singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus`, the
identity (S2) of `StacksFrontier.Homology.DerivedIndexing.Composite`, and the only step of the
pre-composition coherence that says anything about resolutions. -/
theorem mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (F.obj X) ≫
          extendResolutionComparisonQh F X =
      F.mapDerivedCategory.map
        ((Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X) := by
  have hE0 : (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
            ((CochainComplex.singleFunctor A 0).obj (F.obj X)) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) 0).inv.app X)) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app
          ((CochainComplex.singleFunctor C 0).obj X)) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) :=
    ((congrArg (fun z => (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫ z ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X)))
        (singleFunctorIsoCompQh_hom_app 0 (F.obj X))).symm.trans
      (mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh F X)).trans
      (congrArg (fun z => F.mapDerivedCategory.map z ≫
          F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X))
        (singleFunctorIsoCompQh_hom_app 0 X))
  have h0 := comp_inv_of_comm ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
    ((DerivedCategory.quotientCompQhIso A).inv.app
      ((CochainComplex.singleFunctor A 0).obj (F.obj X)))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X)))
    (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app
      ((CochainComplex.singleFunctor C 0).obj X)))
    (F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.singleFunctor C 0).obj X)) hE0
  have hψ : DerivedCategory.Qh.map (resUnit.app (F.obj X)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (extendResolutionComparison F X)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).inv.app X)) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (resUnit.app X)) :=
    (DerivedCategory.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Qh.map
          (resUnit_app_comp_quotient_map_extendResolutionComparison F X)).trans
        (DerivedCategory.Qh.map_comp _ _))
  refine Eq.trans (congrArg (fun z => (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
    z ≫ extendResolutionComparisonQh F X) (singleIsoResCompQh_hom_app (F.obj X))) ?_
  refine Eq.trans ?_ (congrArg F.mapDerivedCategory.map
    (singleIsoResCompQh_hom_app X)).symm
  refine Eq.trans ?_ (F.mapDerivedCategory.map_comp _ _).symm
  exact augmentation_chase ((F.mapDerivedCategorySingleFunctor 0).hom.app X)
    ((DerivedCategory.quotientCompQhIso A).inv.app
      ((CochainComplex.singleFunctor A 0).obj (F.obj X)))
    (DerivedCategory.Qh.map (resUnit.app (F.obj X)))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (extendResolutionComparison F X)))
    (F.mapDerivedCategoryFactorsh.inv.app (resH.obj X))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X)))
    (DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (resUnit.app X)))
    (F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.singleFunctor C 0).obj X))
    (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app
      ((CochainComplex.singleFunctor C 0).obj X)))
    (F.mapDerivedCategory.map (DerivedCategory.Qh.map (resUnit.app X)))
    hψ (F.mapDerivedCategoryFactorsh.inv.naturality (resUnit.app X)) h0

end Augmentation

/-! ### The coherence -/

section PreComposition

variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B] [EnoughInjectives C] [EnoughInjectives A]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]
  (w : A ⥤ B) [w.Additive]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (α' : (F ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ Rw))
  [(F.mapDerivedCategory ⋙ Rw).IsRightDerivedFunctor α'
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (hα' : ∀ K : HomotopyCategory C (ComplexShape.up ℤ), α'.app K =
    α.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      Rw.map (F.mapDerivedCategoryFactorsh.inv.app K))
  (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

omit [EnoughInjectives C] [EnoughInjectives A] [F.PreservesInjectiveObjects] in
/-- **The derived side of the coherence, as a natural transformation**: the single-functor
comparison of `F.mapDerivedCategory`, read on the degree-`n` cohomology of `Rw` applied to an
object placed in degree `0`. The components are written out rather than assembled by whiskering:
whiskering would produce the bracketings `(singleFunctor C 0 ⋙ F.mapDerivedCategory) ⋙ (Rw ⋙ Hⁿ)`
and `(F ⋙ singleFunctor A 0) ⋙ (Rw ⋙ Hⁿ)`, which are definitionally but not unifiably equal to
the ones the bridge is stated at. -/
def preCompSingleHomologyNatTrans (n : ℤ) :
    DerivedCategory.singleFunctor C 0 ⋙ (F.mapDerivedCategory ⋙ Rw) ⋙
        DerivedCategory.homologyFunctor B n ⟶
      F ⋙ DerivedCategory.singleFunctor A 0 ⋙ Rw ⋙ DerivedCategory.homologyFunctor B n where
  app X := (DerivedCategory.homologyFunctor B n).map
    (Rw.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X))
  naturality _ Y f :=
    ((DerivedCategory.homologyFunctor B n).map_comp _ _).symm.trans
      ((congrArg (DerivedCategory.homologyFunctor B n).map
          (((Rw.map_comp (F.mapDerivedCategory.map
                  ((DerivedCategory.singleFunctor C 0).map f))
                ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)).symm.trans
              (congrArg Rw.map
                ((F.mapDerivedCategorySingleFunctor 0).hom.naturality f))).trans
            (Rw.map_comp _ _))).trans
        ((DerivedCategory.homologyFunctor B n).map_comp _ _))

include hα'

/-- **The bridge carries pre-composition with an exact functor preserving injectives to the
composite right derived comparison**, componentwise. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_preComp_app (n : ℕ) (X : C) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (F ⋙ w)
            (F.mapDerivedCategory ⋙ Rw) α' hresC n).hom.app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (Rw.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α
          hresA n).hom.app (F.obj X) := by
  set Hn := DerivedCategory.homologyFunctor B (n : ℤ) with hHn
  set Hz := HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ) with hHz
  set g := (w.mapHomotopyCategory (ComplexShape.up ℤ)).map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (extendResolutionComparison F X)) with hg
  -- the first square: the augmentation square, pushed through `Rw` and `Hⁿ`
  have h₁ : Hn.map (Rw.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
        Hn.map (Rw.map
            ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (F.obj X))) ≫
          Hn.map (Rw.map (extendResolutionComparisonQh F X)) =
      Hn.map ((F.mapDerivedCategory ⋙ Rw).map
        ((Stacks.DerivedFunctor.singleIsoResCompQh (A := C)).hom.app X)) := by
    rw [← Hn.map_comp, ← Hn.map_comp, ← Rw.map_comp, ← Rw.map_comp]
    exact congrArg (fun z => Hn.map (Rw.map z))
      (mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh F X)
  -- the second square: the naturality of `α` at the comparison of the resolutions
  have hsq0 : α.app (resH.obj (F.obj X)) ≫ Rw.map (extendResolutionComparisonQh F X) =
      DerivedCategory.Qh.map g ≫ α'.app (resH.obj X) :=
    (congrArg (fun z => α.app (resH.obj (F.obj X)) ≫ z)
      (Rw.map_comp (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (extendResolutionComparison F X)))
        (F.mapDerivedCategoryFactorsh.inv.app (resH.obj X)))).trans
      (unit_chase _ _ _ _ _ _
        (α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (extendResolutionComparison F X)))
        (hα' (resH.obj X)))
  have hsq : Hn.map ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hresA).hom.app (F.obj X)) ≫
        Hn.map (Rw.map (extendResolutionComparisonQh F X)) =
      Hn.map (DerivedCategory.Qh.map g) ≫
        Hn.map ((Stacks.DerivedFunctor.resCompUnitIso (F ⋙ w)
          (F.mapDerivedCategory ⋙ Rw) α' hresC).hom.app X) :=
    (Hn.map_comp _ _).symm.trans ((congrArg Hn.map hsq0).trans (Hn.map_comp _ _))
  have h₂ := comm_of_comm_inv
    (Hn.mapIso ((Stacks.DerivedFunctor.resCompUnitIso w Rw α hresA).app (F.obj X)))
    (Hn.mapIso ((Stacks.DerivedFunctor.resCompUnitIso (F ⋙ w)
      (F.mapDerivedCategory ⋙ Rw) α' hresC).app X))
    (Hn.map (DerivedCategory.Qh.map g))
    (Hn.map (Rw.map (extendResolutionComparisonQh F X))) hsq
  -- the third square: the naturality of the factorization of the cohomology functor
  have h₃ := (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.naturality g
  -- the fourth square: the classical half
  have h₄ := comm_to_inv ((rightDerivedIsoRes w n).app (F.obj X))
    ((rightDerivedIsoRes (F ⋙ w) n).app X)
    ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w n).app X)
    (Hz.map g)
    (compRightDerivedNatIso_inv_app_comp_rightDerivedIsoRes F w n X)
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app]
  exact paste_ladder _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

/-- **The bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` carries pre-composition with an exact functor
preserving injective objects to the composite right derived comparison.** For `F : C ⥤ A`
additive, exact and preserving injectives and `w : A ⥤ B` additive, the bridge for `F ⋙ w` taken
at `F.mapDerivedCategory ⋙ Rw` is the bridge for `w` read at `F X` through the single-functor
comparison of `F.mapDerivedCategory` and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_preComp (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (F ⋙ w)
            (F.mapDerivedCategory ⋙ Rw) α' hresC n).hom ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w n).hom =
      preCompSingleHomologyNatTrans F Rw (n : ℤ) ≫
        Functor.whiskerLeft F
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α
            hresA n).hom :=
  NatTrans.ext (funext fun X ↦
    singleCompDerivedCompHomologyIsoRightDerived_preComp_app F w Rw α α' hα' hresC hresA n X)

end PreComposition

end Stacks.DerivedIndexing

end
