module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayHirschIsomorphism

/-!
# Base change of `Rf_*Ω^p_{X/S}` along a cartesian square, on cohomology

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and `g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` the morphism of
ringed spaces of the square. The canonical map of differential forms (Tag 07HX) has a transpose
`g₀^*(Ω^p_{X/S}[0]) ⟶ Ω^p_{X'/S'}[0]`, and with the comparison of derived and termwise pullback
it gives the canonical comparison `Lg₀^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`. On cohomology this comparison,
after the pullback of classes along `g₀`, is the pullback `g'^*` of Hodge cohomology along the
square (Section 50.5, Tag 0FM4).

For `f` proper and smooth and the square cartesian, the derived base change map at `Ω^p_{X/S}`
followed by the comparison is an isomorphism `Lg^*Rf_*Ω^p_{X/S} ≅ Rf'_*Ω^p_{X'/S'}`: this is
[Stacks, Tag 0FM0] for the graded pieces of the stupid filtration of the de Rham complex. Read on
cohomology through the Leray identifications `H^q(S, Rf_*Ω^p_{X/S}) = H^q(X, Ω^p_{X/S})`
(Tag 0D5W), this isomorphism is the pullback of Hodge cohomology along the square.

## Main definitions

* `Stacks.HodgeWeil.formsSinglePullback`: the canonical map `g₀^*(Ω^p_{X/S}[0]) ⟶ Ω^p_{X'/S'}[0]`.
* `Stacks.HodgeWeil.hodgeBaseChangeComparison`: the comparison `Lg₀^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`.
* `Stacks.HodgeWeil.derivedFormsDirectImage`: `Rf_*Ω^p_{X/S}`, the derived direct image along
  `(X, f⁻¹𝒪_S) ⟶ S` of `Ω^p_{X/S}` placed in degree `0`.
* `Stacks.HodgeWeil.formsDirectImageBaseChangeIso`: the base change isomorphism
  `Lg^*Rf_*Ω^p_{X/S} ≅ Rf'_*Ω^p_{X'/S'}` for `f` proper smooth and a cartesian square.

## Main results

* `Stacks.HodgeWeil.homEquiv_derivedPullbackComparison_comp_pushforwardComparisonQ`: for a
  morphism of ringed spaces `h` and a morphism of complexes `φ : K ⟶ h_*K'`, the transpose of the
  derived pullback comparison followed by the transpose of `φ` is `φ` followed by `h_* ⟶ Rh_*`.
* `Stacks.HodgeWeil.hodgeBaseChangeComparison_homologyPullback`: the comparison on cohomology is
  the pullback of Hodge cohomology along the square.
* `Stacks.HodgeWeil.isIso_derivedBaseChangeMap_formsSingle`: for `f` proper and smooth and a
  cartesian square, the derived base change map at `Ω^p_{X/S}` followed by the canonical
  comparison `Lg₀^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` is an isomorphism.
* `Stacks.HodgeWeil.lerayCohomologyIso_formsDirectImageBaseChangeIso_homologyPullback`: the base
  change isomorphism on cohomology is the pullback of Hodge cohomology along the square.
* `Stacks.HodgeWeil.homologyPullback_unitCycleClass_formsDirectImageBaseChangeIso`: the same for
  the value at the pulled back class of `1` of a morphism `𝒪_S[-q] ⟶ Rf_*Ω^p_{X/S}`.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HomologyPullback
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard

section General

variable {Z Z' : RingedSpace.{u, u}} (h : Z' ⟶ Z)

/-- **The transpose of a derived pullback comparison followed by a termwise map.** For a morphism
of complexes `φ : K ⟶ h_*K'` with transpose `r : h^*K ⟶ K'`, the transpose under `Lh^* ⊣ Rh_*` of
the comparison `Lh^*K ⟶ h^*K` followed by `r`, conjugated by the identifications of `Q` with
`Qh ∘ quotient`, is the class of `φ` followed by the comparison `h_*K' ⟶ Rh_*K'`. -/
theorem homEquiv_derivedPullbackComparison_comp_pushforwardComparisonQ
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') :
    (DerivedCategory.quotientCompQhIso _).inv.app K ≫
        (derivedAdjunction h).homEquiv _ _
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison h).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((((modulePullbackPushforwardAdjunction h).mapHomologicalComplex
                (ComplexShape.up ℤ)).homEquiv _ _).symm φ))) ≫
        (derivedPushforward h).map ((DerivedCategory.quotientCompQhIso _).hom.app K') =
      DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K' := by
  set r := (((modulePullbackPushforwardAdjunction h).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _).symm φ with hr
  have hφ : ((modulePullbackPushforwardAdjunction h).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app K ≫
        ((modulePushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).map r = φ :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ φ)
  have hq : (homotopyPullbackPushforwardAdjunction h).unit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      ((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ :=
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map hφ)
  have hadj : (derivedAdjunction h).homEquiv _ _
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison h).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) ≫
        (derivedPushforwardUnit h).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K') := by
    refine ((derivedAdjunction h).homEquiv_naturality_right _ _).trans ?_
    refine (congrArg (· ≫ _)
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackComparison_homEquiv h _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((derivedPushforwardUnit h).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map r)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ _) ((DerivedCategory.Qh.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Qh.map hq))
  refine (congrArg (fun t => (DerivedCategory.quotientCompQhIso _).inv.app K ≫ t ≫
    (derivedPushforward h).map ((DerivedCategory.quotientCompQhIso _).hom.app K')) hadj).trans ?_
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
    (DerivedCategory.quotientCompQhIso_inv_naturality_assoc φ _).symm

/-- Transposing `L(a) ≫ e⁻¹ ≫ e ≫ φ ≫ c` under an adjunction `L ⊣ R`. -/
private theorem homEquiv_map_comp_inv_comp {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A A' : C} {M B B' : D} (a : A ⟶ A') (e : M ≅ L.obj A')
    (φ : L.obj A' ⟶ B') (c : B' ⟶ B) :
    adj.homEquiv A B ((L.map a ≫ e.inv) ≫ e.hom ≫ φ ≫ c) =
      a ≫ adj.homEquiv A' B' φ ≫ R.map c := by
  rw [Category.assoc, Iso.inv_hom_id_assoc, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]

open Stacks.CategoryTheory.ComparisonFiveLemma in
/-- **Moving a map of single complexes from degree `a'` to degree `a` by a shift.** For an
additive functor `F` and `φ : F N ⟶ N'`, the map `F(N[-a']) ⟶ N'[-a']` induced by `φ`, shifted by
`n` with `n + a = a'`, is the map `F(N[-a]) ⟶ N'[-a]` induced by `φ`, through the
identifications `(N[-a'])[n] ≅ N[-a]`. -/
theorem mapHomologicalComplex_map_shiftIso_comp_single_map {A B : Type*} [Category* A]
    [Category* B] [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    (F : A ⥤ B) [F.Additive] {N : A} {N' : B} (φ : F.obj N ⟶ N') (n a a' : ℤ)
    (h : n + a = a') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CochainComplex.singleFunctors A).shiftIso n a a' h).hom.app N) ≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a).hom.app N ≫
          (HomologicalComplex.single B (ComplexShape.up ℤ) a).map φ =
      shiftData (F.mapHomologicalComplex (ComplexShape.up ℤ))
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a').hom.app N ≫
            (HomologicalComplex.single B (ComplexShape.up ℤ) a').map φ) n ≫
        ((CochainComplex.singleFunctors B).shiftIso n a a' h).hom.app N' := by
  obtain rfl : a' = a + n := by omega
  refine HomologicalComplex.to_single_hom_ext ?_
  simp [shiftData, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]

end General

section Square

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The canonical map `g₀^*(Ω^p_{X/S}[0]) ⟶ Ω^p_{X'/S'}[0]`** of a commutative square, where
`g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` is the morphism of ringed spaces of the square: the
transpose under `g₀^* ⊣ g₀_*` of the canonical map of differential forms of Tag 07HX, placed in
degree `0`. -/
def formsSinglePullback (p : ℕ) :
    ((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (formsSingle f p) ⟶ formsSingle f' p :=
  (HomologicalComplex.singleMapHomologicalComplex (modulePullback (inverseImageBaseMap g' f' f g w))
      (ComplexShape.up ℤ) 0).hom.app _ ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _).symm
        (formsPushforward g' f' f g w p))

/-- **The canonical map `g₀^*(Ω^p_{X/S}[0]) ⟶ Ω^p_{X'/S'}[0]` is the transpose of
`Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])`** under the degreewise adjunction `g₀^* ⊣ g₀_*`. -/
theorem formsSinglePullback_eq (p : ℕ) :
    formsSinglePullback g' f' f g w p =
      (((modulePullbackPushforwardAdjunction
        (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv _ _).symm (formsSinglePushforward g' f' f g w p) := by
  refine (Equiv.eq_symm_apply _).2 (HomologicalComplex.from_single_hom_ext ?_)
  refine Eq.trans ?_ (formsSinglePushforward_f_zero g' f' f g w p).symm
  have h₁ := HomologicalComplex.singleMapHomologicalComplex_hom_app_self
    (modulePullback (inverseImageBaseMap g' f' f g w)) (ComplexShape.up ℤ) 0
    ((Scheme.Hom.deRhamComplex f).X p)
  have h₂ := HomologicalComplex.single_map_f_self
    (V := SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))) (c := ComplexShape.up ℤ) 0
    (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _).symm
      (formsPushforward g' f' f g w p))
  exact (congrArg ((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv
    _ _) (congrArg₂ (· ≫ ·) h₁ h₂)).trans ((homEquiv_map_comp_inv_comp _ _ _ _ _).trans
      (congrArg (fun t => _ ≫ t ≫ _) (Equiv.apply_symm_apply _ _)))

/-- **The canonical comparison `Lg₀^*(Ω^p_{X/S}[0]) ⟶ Ω^p_{X'/S'}[0]`** of a commutative square:
the comparison of the derived and the termwise pullback along `g₀`, followed by
`formsSinglePullback`. -/
def hodgeBaseChangeComparison (p : ℕ) :
    (derivedPullback (inverseImageBaseMap g' f' f g w)).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (formsSingle f p))) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (formsSingle f' p)) :=
  (derivedPullbackComparison (inverseImageBaseMap g' f' f g w)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (formsSingle f p)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (formsSinglePullback g' f' f g w p))

/-- **The transpose of the canonical comparison, read at the localization functor `Q`**: after
conjugating by `DerivedCategory.quotientCompQhIso`, the transpose of
`hodgeBaseChangeComparison` under `Lg₀^* ⊣ Rg₀_*` is `Q` of the canonical map
`Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])` followed by the comparison `g₀_* ⟶ Rg₀_*`. -/
theorem homEquiv_hodgeBaseChangeComparison_pushforwardComparisonQ (p : ℕ) :
    (DerivedCategory.quotientCompQhIso _).inv.app (formsSingle f p) ≫
        (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
          (hodgeBaseChangeComparison g' f' f g w p) ≫
        (derivedPushforward (inverseImageBaseMap g' f' f g w)).map
          ((DerivedCategory.quotientCompQhIso _).hom.app (formsSingle f' p)) =
      DerivedCategory.Q.map (formsSinglePushforward g' f' f g w p) ≫
        pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (formsSingle f' p) := by
  rw [hodgeBaseChangeComparison, formsSinglePullback_eq]
  exact homEquiv_derivedPullbackComparison_comp_pushforwardComparisonQ _ _

/-- **The canonical comparison on cohomology is the pullback on Hodge cohomology.** The pullback
of a class of `H^q(X, Ω^p_{X/S})` along `g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)`, followed by the
canonical comparison `Lg₀^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`, is its pullback along the square
(Section 50.5, Tag 0FM4). -/
theorem hodgeBaseChangeComparison_homologyPullback (p : ℕ) (q : ℤ)
    (z : cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) q) :
    ((DerivedCategory.homologyFunctor _ q).map ((baseSections _).map
        ((derivedPullback (inverseImageBaseMap g' f' f g w)).map
            ((DerivedCategory.quotientCompQhIso _).inv.app (formsSingle f p)) ≫
          hodgeBaseChangeComparison g' f' f g w p ≫
          (DerivedCategory.quotientCompQhIso _).hom.app (formsSingle f' p)))).hom
        (homologyPullback (inverseImageBaseMap g' f' f g w) _ q z) =
      hodgePullback g' f' f g w p q z := by
  refine (homologyPullback_homEquiv (inverseImageBaseMap g' f' f g w) _ q z).trans ?_
  have hadj : (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
      ((derivedPullback (inverseImageBaseMap g' f' f g w)).map
          ((DerivedCategory.quotientCompQhIso _).inv.app (formsSingle f p)) ≫
        hodgeBaseChangeComparison g' f' f g w p ≫
        (DerivedCategory.quotientCompQhIso _).hom.app (formsSingle f' p)) =
      DerivedCategory.Q.map (formsSinglePushforward g' f' f g w p) ≫
        pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (formsSingle f' p) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    exact homEquiv_hodgeBaseChangeComparison_pushforwardComparisonQ g' f' f g w p
  rw [hadj]
  rfl

end Square


section Cartesian

open Stacks.CategoryTheory.ComparisonFiveLemma AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedBaseChange Stacks.AlgebraicGeometry.FlatSourceBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

/-- **`Rf_*Ω^p_{X/S}`**, the derived direct image along `(X, f⁻¹𝒪_S) ⟶ S` of `Ω^p_{X/S}` placed in
degree `0`; its cohomology over `S` is the Hodge cohomology `H^q(X, Ω^p_{X/S})` (Tag 0D5W). -/
abbrev derivedFormsDirectImage (f : X ⟶ S) (p : ℕ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
  (derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj (formsSingle f p))

variable (hsq : IsPullback g' f' f g)

/-- Base change for `Ω^p_{X/S}` placed in degree `p`, at every shift, in the form of the five
lemma: the comparison along the map `g₀^*(Ω^p_{X/S}[-p]) ⟶ Ω^p_{X'/S'}[-p]` induced by the
transpose of the canonical map of differential forms is invertible at every shift. -/
theorem allShifts_single_formsPushforward [IsProper f] [Smooth f] (p : ℕ) :
    AllShifts (deRhamBaseChangeTrans g' f' f g hsq.w)
      ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback (inverseImageBaseMap g' f' f g hsq.w)) (ComplexShape.up ℤ)
            (p : ℤ)).hom.app ((Scheme.Hom.deRhamComplex f).X p) ≫
        (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))
          (ComplexShape.up ℤ) (p : ℤ)).map
          (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g hsq.w)).homEquiv
            _ _).symm (formsPushforward g' f' f g hsq.w p))) := by
  have hφ : (structuralBaseChange g' f' f g hsq.w).app
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
      (modulePushforward (toInverseImageBase f')).map
        (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w p) =
      ((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g hsq.w)).homEquiv
        _ _).symm (formsPushforward g' f' f g hsq.w p) :=
    (Equiv.eq_symm_apply _).2 (homEquiv_structuralBaseChange_comp g' f' f g hsq.w p)
  have key := StacksDraft.StupidTruncation.mapHomologicalComplex_single_comp_eq_iso
    (modulePushforward (toInverseImageBase f)) (modulePushforward (toInverseImageBase f'))
    (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
    (modulePullback g'.toLRSHom.toShHom) (structuralBaseChange g' f' f g hsq.w)
    (N := (Scheme.Hom.deRhamComplex f).X p) (N' := (Scheme.Hom.deRhamComplex f').X p)
    (M := Scheme.Hom.relativeDifferentialForms f (p : ℤ))
    (M' := Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) (Iso.refl _) (Iso.refl _)
    (((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g hsq.w)).homEquiv
      _ _).symm (formsPushforward g' f' f g hsq.w p))
    (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w p)
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
      ((Category.id_comp _).trans (hφ.trans (Category.comp_id _).symm))) (p : ℤ)
  refine (allShifts_iff_of_hom (deRhamBaseChangeTrans g' f' f g hsq.w) _ _ _ _ key).2 ?_
  have h₀ := allShifts_restrictScalars_formsSingle hsq p
  unfold formsSingleMap at h₀
  convert h₀ using 4

/-- **Base change for `Ω^p_{X/S}` placed in degree `0`**, in the form of the five lemma: the
comparison along `formsSinglePullback` is invertible. -/
theorem isIso_comparison_formsSinglePullback [IsProper f] [Smooth f] (p : ℕ) :
    IsIso (comparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (formsSinglePullback g' f' f g hsq.w p)) :=
  (isIso_comparison_iff_of_hom (deRhamBaseChangeTrans g' f' f g hsq.w) _ _
    (((CochainComplex.singleFunctors (SheafOfModules.{u}
      (structureSheafRing (inverseImageBase f)))).shiftIso (p : ℤ) 0 (p : ℤ) (add_zero _)).app
        ((Scheme.Hom.deRhamComplex f).X p)).hom
    (((CochainComplex.singleFunctors (SheafOfModules.{u}
      (structureSheafRing (inverseImageBase f')))).shiftIso (p : ℤ) 0 (p : ℤ) (add_zero _)).app
        ((Scheme.Hom.deRhamComplex f').X p)).hom
    (mapHomologicalComplex_map_shiftIso_comp_single_map _ _ _ _ _ (add_zero _))).1
    (allShifts_single_formsPushforward g' f' f g hsq p (p : ℤ))

/-- **[Stacks, Tag 0FM0] for the graded pieces: base change for `Rf_*Ω^p_{X/S}`.** For `f` proper
and smooth and a cartesian square, the derived base change map at `Ω^p_{X/S}` along the
inverse-image ringed spaces, followed by `Rπ'_*` of the canonical comparison
`Lg₀^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`, is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_formsSingle [IsProper f] [Smooth f] (p : ℕ) :
    IsIso (derivedBaseChangeMap (inverseImageBaseMap g' f' f g hsq.w)
        (inverseImageBaseProjection f') (inverseImageBaseProjection f) g.toLRSHom.toShHom
        (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (formsSingle f p))) ≫
      (derivedPushforward (inverseImageBaseProjection f')).map
        (hodgeBaseChangeComparison g' f' f g hsq.w p)) := by
  have key := isIso_comparison_formsSinglePullback g' f' f g hsq p
  simp only [comparison, deRhamBaseChangeTrans, derivedBaseChangeComplexTrans_app,
    Functor.comp_map] at key
  rw [hodgeBaseChangeComparison, Functor.map_comp, ← Category.assoc]
  exact key

/-- **The base change isomorphism `Lg^*Rf_*Ω^p_{X/S} ≅ Rf'_*Ω^p_{X'/S'}`** for `f` proper and
smooth and a cartesian square ([Stacks, Tag 0FM0], graded pieces). -/
def formsDirectImageBaseChangeIso [IsProper f] [Smooth f] (p : ℕ) :
    (derivedPullback g.toLRSHom.toShHom).obj (derivedFormsDirectImage f p) ≅
      derivedFormsDirectImage f' p :=
  have := isIso_derivedBaseChangeMap_formsSingle g' f' f g hsq p
  (derivedPullback g.toLRSHom.toShHom).mapIso
      ((derivedPushforward (inverseImageBaseProjection f)).mapIso
        ((DerivedCategory.quotientCompQhIso _).app _).symm) ≪≫
    @asIso _ _ _ _ _ this ≪≫
    (derivedPushforward (inverseImageBaseProjection f')).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _)

/-- **The base change isomorphism on cohomology is the pullback on Hodge cohomology.** A class
`z` of `H^q(X, Ω^p_{X/S})`, read in `H^q(S, Rf_*Ω^p_{X/S})` through the Leray identification,
pulled back to `S'` and carried by `Lg^*Rf_*Ω^p_{X/S} ≅ Rf'_*Ω^p_{X'/S'}`, is, read in
`H^q(X', Ω^p_{X'/S'})`, the pullback `g'^* z` along the square. -/
theorem lerayCohomologyIso_formsDirectImageBaseChangeIso_homologyPullback [IsProper f]
    [Smooth f] (p : ℕ) (q : ℤ) (z : cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) q) :
    (lerayCohomologyIso (inverseImageBaseProjection f')
        (DerivedCategory.Q.obj (formsSingle f' p)) q).hom
      (((DerivedCategory.homologyFunctor _ q).map ((baseSections _).map
        (formsDirectImageBaseChangeIso g' f' f g hsq p).hom)).hom
        (homologyPullback g.toLRSHom.toShHom (derivedFormsDirectImage f p) q
          ((lerayCohomologyIso (inverseImageBaseProjection f)
            (DerivedCategory.Q.obj (formsSingle f p)) q).inv z))) =
      hodgePullback g' f' f g hsq.w p q z :=
  (DeRhamLerayHirsch.lerayCohomologyIso_derivedBaseChangeMap_comp
    (inverseImageBaseMap g' f' f g hsq.w) (inverseImageBaseProjection f')
    (inverseImageBaseProjection f) g.toLRSHom.toShHom
    (inverseImageBaseMap_comp_inverseImageBaseProjection _ _ f _ hsq.w)
    ((DerivedCategory.quotientCompQhIso _).inv.app (formsSingle f p))
    (hodgeBaseChangeComparison g' f' f g hsq.w p)
    ((DerivedCategory.quotientCompQhIso _).hom.app (formsSingle f' p)) q z).trans
    (hodgeBaseChangeComparison_homologyPullback g' f' f g hsq.w p q z)

open Stacks.Cohomology.DerivedGlobalCupProduct (unitComplex unitCycleClass evalUnit) in
/-- **The value of a morphism `𝒪_S[-q] ⟶ Rf_*Ω^p_{X/S}` after base change.** For
`a : 𝒪_S[-q] ⟶ Rf_*Ω^p_{X/S}`, the pullback to `S'` of the class of `1`, carried by `Lg^*a` and
the base change isomorphism, is, read in `H^q(X', Ω^p_{X'/S'})`, the pullback along the square
of the value of `a` at the class of `1`, read in `H^q(X, Ω^p_{X/S})`. -/
theorem homologyPullback_unitCycleClass_formsDirectImageBaseChangeIso [IsProper f] [Smooth f]
    (p : ℕ) (q : ℤ)
    (a : DerivedCategory.Q.obj (unitComplex S.toRingedSpace q) ⟶ derivedFormsDirectImage f p) :
    (lerayCohomologyIso (inverseImageBaseProjection f')
        (DerivedCategory.Q.obj (formsSingle f' p)) q).hom
      (((DerivedCategory.homologyFunctor _ q).map ((baseSections _).map
        ((derivedPullback g.toLRSHom.toShHom).map a ≫
          (formsDirectImageBaseChangeIso g' f' f g hsq p).hom))).hom
        (homologyPullback g.toLRSHom.toShHom _ q (unitCycleClass S.toRingedSpace q))) =
      hodgePullback g' f' f g hsq.w p q
        ((lerayCohomologyIso (inverseImageBaseProjection f)
          (DerivedCategory.Q.obj (formsSingle f p)) q).hom
          (evalUnit (derivedFormsDirectImage f p) q a)) := by
  have h := lerayCohomologyIso_formsDirectImageBaseChangeIso_homologyPullback g' f' f g hsq p q
    ((lerayCohomologyIso (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (formsSingle f p)) q).hom
      (evalUnit (derivedFormsDirectImage f p) q a))
  have hE : (lerayCohomologyIso (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (formsSingle f p)) q).inv
      ((lerayCohomologyIso (inverseImageBaseProjection f)
        (DerivedCategory.Q.obj (formsSingle f p)) q).hom
        (evalUnit (derivedFormsDirectImage f p) q a)) =
      evalUnit (derivedFormsDirectImage f p) q a :=
    Iso.hom_inv_id_apply _ _
  rw [hE] at h
  refine Eq.trans ?_ h
  refine congrArg (lerayCohomologyIso (inverseImageBaseProjection f')
    (DerivedCategory.Q.obj (formsSingle f' p)) q).hom ?_
  refine (map_map_comp_apply (baseSections _) (DerivedCategory.homologyFunctor _ q) _ _ _).trans ?_
  exact congrArg _ (homologyPullback_naturality g.toLRSHom.toShHom a q _).symm

end Cartesian

end Stacks.HodgeWeil

end
