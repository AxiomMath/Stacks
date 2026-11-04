module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction

/-! # The composition comparison on `D⁺` is the one on `D`

Let `F : A ⥤ B` and `G : B ⥤ C` be additive, with `A` and `B` having enough injectives and
K-injective resolutions. Two comparisons `R(G ∘ F) ⟶ RG ∘ RF` of [Stacks, Tag 05T2] are then in
play: `CategoryTheory.Functor.rightDerivedFunctorPlusComp` on the bounded below derived
categories, and an unbounded one — for sections over an open that is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, the Leray comparison of
[Stacks, Tag 0D5W].

Both are descents, through the universal property of the respective right derived functor of
degreewise `G ∘ F`, of literally the same three-factor transformation: the coherence identifying
the functor induced by `G ∘ F` with the composite of the induced functors, the unit of the outer
derived functor at the image of the inner degreewise functor, and the outer derived functor
applied to the unit of the inner one. Compare
`CategoryTheory.Functor.rightComparisonUnit` with
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit`: they are the same expression.

**This file proves that the two comparisons correspond** under
`CategoryTheory.Functor.boundedDerivedIso`. The unbounded comparison is taken as data, with its
factorisation as the hypothesis `hθ`, exactly as
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` takes the unbounded derived
functor as data: without the factorisation there is no canonical map to compare with. For the
Leray comparison `hθ` is
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app`.

## Main results

* `CategoryTheory.Functor.boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp`: **the square
  commutes**, as an identity of natural transformations `R⁺(G ∘ F) ⋙ ι ⟶ ι ⋙ (RF ⋙ RG)`.
* `CategoryTheory.Functor.boundedDerivedIso_hom_app_comp_rightDerivedFunctorPlusComp`: the same
  at an object of `D⁺(A)`.

## Implementation notes

*The proof is the uniqueness of transformations out of a right derived functor on `K⁺(A)`.*
`R⁺(G ∘ F) ⋙ ι` is a right derived functor of degreewise `G ∘ F` on `K⁺(A)` with unit
`CategoryTheory.Functor.boundedUnitPlus` — that is
`isRightDerivedFunctor_boundedUnitPlus` — so the two routes agree as soon as they agree after
that unit. There each collapses, by its own factorisation, to the three-factor transformation,
and the two results are matched by `boundedDerivedIso_hom_app` at `F` and at `G` together with
the naturality of the crossing for `G` at the unit of `R⁺F`.

*This statement needs no reassociation and no coherence lemma.* The `≫` joining
`CategoryTheory.Functor.whiskerRight _ DerivedCategory.Plus.ι`, whose target is
`(F⁺ ⋙ G⁺) ⋙ ι`, to `CategoryTheory.Functor.whiskerLeft F.rightDerivedFunctorPlus _`, whose
source is `F⁺ ⋙ (G⁺ ⋙ ι)`, typechecks as written — no
`CategoryTheory.Functor.associator`, no reassociation declaration — although the intermediate
categories, and so the universe arguments of `CategoryTheory.Functor.comp`, differ. That
contradicts the blanket form of the note in `DerivedFunctorSingleRightDerived.lean`, which has
been corrected there: the obstruction is a metavariable in the middle of an `Iso.trans` chain,
not the regrouping. Likewise the Plus-against-unbounded coherence
`ι(Plus.Qh.map cohPlus.inv) = Qh.map coh.inv`, which the chase needs as its hypothesis `f6`, is
discharged by the unifier when `hθ` is applied at `ι L`; no bridging lemma is required.

*No acyclicity and no invertibility is assumed.* The statement is about the comparison
transformations, not about the isomorphisms
`Stacks.Cohomology.DerivedPushforwardSections.compIso` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` they become under
[Stacks, Tag 015M] and [Stacks, Tag 0D5W]; a consumer holding those reads the statement through
`Stacks.Cohomology.DerivedPushforwardSections.compIso_hom`.

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v u vB uB vC uC wA wB wC

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RG : DerivedCategory B ⥤ DerivedCategory C)
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (RFG : DerivedCategory A ⥤ DerivedCategory C)
  (αFG : (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RFG)
  [RFG.IsRightDerivedFunctor αFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (θ : RFG ⟶ RF ⋙ RG)

/-- A two-fold composite carried through a functor, with the value of the composite known as a
three-fold one. At variables. -/
private lemma map_comp_eq_three {C' D' : Type*} [Category* C'] [Category* D'] (H : C' ⥤ D')
    {P Q R S S' : C'} {n : P ⟶ Q} {c : Q ⟶ R} {d₁ : P ⟶ S} {d₂ : S ⟶ S'} {d₃ : S' ⟶ R}
    (h : n ≫ c = d₁ ≫ d₂ ≫ d₃) :
    H.map n ≫ H.map c = H.map d₁ ≫ H.map d₂ ≫ H.map d₃ := by
  rw [← H.map_comp, h, H.map_comp, H.map_comp]

/-- A composite carried through a functor. At variables. -/
private lemma map_comp_eq {C' D' : Type*} [Category* C'] [Category* D'] (H : C' ⥤ D')
    {P Q R : C'} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ R} (h : a ≫ b = c) :
    H.map a ≫ H.map b = H.map c := by
  rw [← H.map_comp, h]

/-- The chase that compares the two composition comparisons, at variables of an abstract
category. Its six hypotheses are, in order: the factorisation of the `D⁺` comparison, the
naturality of the crossing for `G`, the pinning of that crossing at the image of the inner
degreewise functor, the pinning of the crossing for `F` carried through `RG`, the pinning of the
crossing for `G ∘ F`, and the factorisation of the unbounded comparison. -/
private lemma chase_comp {D' : Type*} [Category* D'] {P Q R S S' T T' U V : D'}
    {n : P ⟶ Q} {c : Q ⟶ R} {d₁ : P ⟶ S} {d₂ : S ⟶ S'} {d₃ : S' ⟶ R}
    (f1 : n ≫ c = d₁ ≫ d₂ ≫ d₃)
    {bG : R ⟶ T} {bG' : S' ⟶ T'} {rgu : T' ⟶ T} (f2 : d₃ ≫ bG = bG' ≫ rgu)
    {aG : S ⟶ T'} (f3 : d₂ ≫ bG' = aG)
    {rbF : T ⟶ U} {raF : T' ⟶ U} (f4 : rgu ≫ rbF = raF)
    {bFG : Q ⟶ V} {th : V ⟶ U} {aFG : P ⟶ V} (f5 : n ≫ bFG = aFG)
    (f6 : aFG ≫ th = d₁ ≫ aG ≫ raF) :
    n ≫ c ≫ bG ≫ rbF = n ≫ bFG ≫ th := by
  have h : d₂ ≫ d₃ ≫ bG ≫ rbF = aG ≫ raF := by
    rw [← Category.assoc d₃, f2, Category.assoc, ← Category.assoc d₂, f3, f4]
  rw [← Category.assoc n c, f1, ← Category.assoc n bFG, f5, f6]
  simp only [Category.assoc]
  rw [h]

/-- **The two composition comparisons correspond under the `D⁺`-to-`D` crossings.** The
hypothesis `hθ` is the factorisation that characterises the unbounded comparison: its composite
with the unit of `R(G ∘ F)` is the three-factor transformation of [Stacks, Tag 05T2]. -/
theorem boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L)) :
    Functor.whiskerRight (rightDerivedFunctorPlusComp F G) DerivedCategory.Plus.ι ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
            (boundedDerivedIso G RG αG hresB).hom ≫
          Functor.whiskerRight (boundedDerivedIso F RF αF hresA).hom RG =
      (boundedDerivedIso (F ⋙ G) RFG αFG hresA).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι θ := by
  apply ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).rightDerived_ext
    (boundedUnitPlus (F ⋙ G)) (HomotopyCategory.Plus.quasiIso A)
  ext L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    boundedUnitPlus_app]
  exact chase_comp
    (map_comp_eq_three DerivedCategory.Plus.ι (rightDerivedFunctorPlusComp_fac_app F G L))
    ((boundedDerivedIso G RG αG hresB).hom.naturality (F.rightDerivedFunctorPlusUnit.app L))
    (boundedDerivedIso_hom_app G RG αG hresB (F.mapHomotopyCategoryPlus.obj L))
    (map_comp_eq RG (boundedDerivedIso_hom_app F RF αF hresA L))
    (boundedDerivedIso_hom_app (F ⋙ G) RFG αFG hresA L)
    (hθ ((HomotopyCategory.Plus.ι A).obj L))

/-- **The two composition comparisons correspond under the `D⁺`-to-`D` crossings**, at an object
of `D⁺(A)`. This is the component form of
`boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp`, and it is the form a consumer rewrites
with. -/
theorem boundedDerivedIso_hom_app_comp_rightDerivedFunctorPlusComp
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L))
    (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.map ((rightDerivedFunctorPlusComp F G).app K) ≫
        (boundedDerivedIso G RG αG hresB).hom.app (F.rightDerivedFunctorPlus.obj K) ≫
          RG.map ((boundedDerivedIso F RF αF hresA).hom.app K) =
      (boundedDerivedIso (F ⋙ G) RFG αFG hresA).hom.app K ≫
        θ.app (DerivedCategory.Plus.ι.obj K) := by
  have h := congr_app (boundedDerivedIso_hom_comp_rightDerivedFunctorPlusComp F G RF αF RG αG
    RFG αFG hresA hresB θ hθ) K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using h

end CategoryTheory.Functor


end
