module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.SectionsPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayComposite
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.FibreReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.UnitClassPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import Mathlib.LinearAlgebra.DFinsupp
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray--Hirsch theorem for the relative de Rham complex

Let `f : X ⟶ Y` be a smooth proper morphism of schemes, let `n_1, …, n_N ≥ 0` be integers and let
`ξ_i ∈ H^{n_i}_{dR}(X/Y)`. Through the identifications

`H^m_{dR}(X/Y) = H^m(X, Ω^•_{X/Y}) = H^m(Y, Rf_*Ω^•_{X/Y}) = Hom_{D(𝒪_Y)}(𝒪_Y[-m], Rf_*Ω^•_{X/Y})`

each `ξ_i` is a morphism `𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}`. If at every point `y ∈ Y` the images of
the `ξ_i` in `H^*_{dR}(X_y/κ(y))` form a basis over `κ(y)`, then

`⨁_{i=1}^N 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}`

is an isomorphism ([Stacks, Tag 0FMP]).

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamClassToDirectImage`: the morphism
  `𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` attached to a class of `H^m_{dR}(X/Y)`: evaluation at the unit
  (`Stacks.Cohomology.DerivedGlobalCupProduct.evalUnitEquiv`) inverts the class into a morphism
  `𝒪_X[-m] ⟶ Ω^•_{X/Y}` of `D(f^{-1}𝒪_Y)`, which is carried to `Y` by
  `Stacks.Cohomology.UnitClassPullback.classPushforward`.
* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamClassSumMorphism`: the morphism of the statement.
* `AlgebraicGeometry.DeRhamLerayHirsch.fibreDeRhamClass`: the image of a class in the
  `κ(y)`-vector space `H^m_{dR}(X_y/κ(y))`: the pullback of de Rham cohomology along the fibre
  square ([Stacks, Tag 0FL6]) read through the comparison of the two realizations of de Rham
  cohomology ([Stacks, Tag 01F1]).
* `AlgebraicGeometry.DeRhamLerayHirsch.HasFibrewiseDeRhamBasis`: the hypothesis of the theorem.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.lerayCohomologyIso_evalUnit_deRhamClassToDirectImage` and
  `AlgebraicGeometry.DeRhamLerayHirsch.deRhamClassToDirectImage_bijective`: the morphism attached
  to a class evaluates to the class, and `H^m_{dR}(X/Y) = Hom(𝒪_Y[-m], Rf_*Ω^•_{X/Y})`.
* `AlgebraicGeometry.DeRhamLerayHirsch.homologyPullback_deRhamClassToDirectImage`: the morphism
  attached to a class, pulled back to a point and base changed to the fibre, sends the pullback of
  the class of `1` to the restriction of the class to the fibre.
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_deRhamClassSumMorphism`: **[Stacks, Tag 0FMP]**.

## Implementation notes

The proof is the source's. Source and target are perfect (the target by [Stacks, Tag 0FM0]), so
it suffices that the derived pullback to every point `i_y : Spec κ(y) ⟶ Y` be an isomorphism
(`AlgebraicGeometry.DerivedFibreDetection.isIso_of_forall_isIso_derivedPullback`, which is
[Stacks, Tags 08CR, 0BCD, 06Z0, 08EB]); base change ([Stacks, Tag 0FM0]) identifies the target of
`Li_y^*` with `R(f_y)_*Ω^•_{X_y/κ(y)}`, and over a field a direct sum of lines is mapped
isomorphically as soon as the images of the generators form a basis
(`AlgebraicGeometry.DeRhamLerayHirsch.isIso_biproduct_desc_of_forall_basis`). What remains is the
identification of those images with the restrictions of the classes to the fibre, which is
`homologyPullback_deRhamClassToDirectImage`: the class of `1` is carried by the morphism to the
class itself (`Stacks.Cohomology.UnitClassPullback.lerayCohomologyIso_evalUnit_classPushforward`),
derived base change carries pullback of classes along the point to pullback along the fibre square
(`Stacks.Cohomology.LerayComposite.lerayCohomologyIso_homologyPullback_derivedBaseChangeMap`), and
pullback of classes along the fibre square followed by the comparison of de Rham complexes is the
pullback map of de Rham cohomology, through the comparison of realizations.

`Rf_*Ω^•_{X/Y}` is taken in the unbounded derived category
(`AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded`), where
[Stacks, Tag 0FM0] is stated.

## References

* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.HomologyPullback Stacks.Cohomology.ResidueFieldPoint
open Stacks.Cohomology.UnitClassPullback Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedBaseChange
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamCohomologyDirectImage Stacks.DeRhamBaseChange
open AlgebraicGeometry.ProperSmoothDeRham

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The morphism `𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` attached to a de Rham class** `ξ ∈ H^m_{dR}(X/Y)`:
the class, read in the module realization `H^m(X, Ω^•_{X/Y})` of de Rham cohomology through the
comparison of realizations of [Stacks, Tag 01F1], is the value at the unit of a unique morphism
`𝒪_X[-m] ⟶ Ω^•_{X/Y}` of `D(f^{-1}𝒪_Y)` (`evalUnitEquiv`), which is carried to `Y` by
`classPushforward`. -/
def deRhamClassToDirectImage (m : ℤ) (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) :
    DerivedCategory.Q.obj (unitComplex Y.toRingedSpace m) ⟶ derivedDeRhamDirectImageUnbounded f :=
  classPushforward (inverseImageBaseProjection f) m
    ((evalUnitEquiv (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).symm
      ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom ξ))

/-- **The morphism attached to a class evaluates to the class.** Read through the Leray
identification `H^m(Y, Rf_*Ω^•_{X/Y}) = H^m(X, Ω^•_{X/Y})`, the value at the unit of the morphism
`𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` attached to `ξ` is `ξ`, in the module realization of de Rham
cohomology. -/
theorem lerayCohomologyIso_evalUnit_deRhamClassToDirectImage (m : ℤ)
    (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) :
    (lerayCohomologyIso (inverseImageBaseProjection f)
        (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).hom
      (evalUnit (derivedDeRhamDirectImageUnbounded f) m (deRhamClassToDirectImage f m ξ)) =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom ξ :=
  (lerayCohomologyIso_evalUnit_classPushforward (inverseImageBaseProjection f) m
      ((evalUnitEquiv (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).symm
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom ξ))).trans
    ((evalUnitEquiv (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).apply_symm_apply _)

/-- **`H^m_{dR}(X/Y) = Hom_{D(𝒪_Y)}(𝒪_Y[-m], Rf_*Ω^•_{X/Y})`**: the morphism attached to a de Rham
class determines the class, and every morphism `𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` is attached to a class. -/
theorem deRhamClassToDirectImage_bijective (m : ℤ) :
    Function.Bijective (deRhamClassToDirectImage f m) := by
  let e₁ := (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras f) (SheafOfModules.deRhamDifferential _) m).addCommGroupIsoToAddEquiv
  let e₂ := (lerayCohomologyIso (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).toLinearEquiv.toEquiv
  let e₃ := evalUnitEquiv (derivedDeRhamDirectImageUnbounded f) m
  have h : deRhamClassToDirectImage f m = e₃.symm ∘ e₂.symm ∘ e₁.toEquiv := by
    funext ξ
    refine e₃.injective (e₂.injective ?_)
    refine (lerayCohomologyIso_evalUnit_deRhamClassToDirectImage f m ξ).trans ?_
    show _ = e₂ (e₃ (e₃.symm (e₂.symm (e₁ ξ))))
    rw [Equiv.apply_symm_apply]
    exact (e₂.apply_symm_apply (e₁ ξ)).symm
  rw [h]
  exact e₃.symm.bijective.comp (e₂.symm.bijective.comp e₁.toEquiv.bijective)

/-- **The image of a relative de Rham class in the de Rham cohomology of the fibre over `y`**:
the pullback map of de Rham cohomology along the fibre square ([Stacks, Tag 0FL6]), read in the
`κ(y)`-vector space `H^m_{dR}(X_y/κ(y))` through the comparison of the two realizations of de Rham
cohomology ([Stacks, Tag 01F1]). -/
def fibreDeRhamClass (y : Y) (m : ℤ) (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) :
    ↥(fibreDeRhamModule f y m) :=
  (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom
    ((fibreRestriction f y m).hom ξ)

/-- **The fibrewise basis hypothesis of [Stacks, Tag 0FMP]**: for every point `y ∈ Y` the images
of `ξ_1, …, ξ_N` in the total de Rham cohomology `⨁_m H^m_{dR}(X_y/κ(y))` of the fibre form a basis
over `κ(y)`, the image of `ξ_i` sitting in degree `n_i`. -/
def HasFibrewiseDeRhamBasis {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) : Prop :=
  ∀ y : Y, ∃ b : Module.Basis (Fin N) (Y.residueField y)
      (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
    ∀ i : Fin N, b i = DirectSum.lof (Y.residueField y) ℤ
      (fun m : ℤ => ↥(fibreDeRhamModule f y m)) (n i : ℤ) (fibreDeRhamClass f y (n i : ℤ) (ξ i))

/-- An element is the inverse image of its image under an isomorphism of modules. -/
private theorem eq_inv_apply_of_hom_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) {x : M} {y : N} (h : e.hom x = y) : x = e.inv y := by
  rw [← h, Iso.hom_inv_id_apply]

/-- The transpose of `L(q) ≫ c ≫ q'`. -/
private theorem homEquiv_map_comp_comp {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A A' : C} {B B' : D} (q : A ⟶ A') (c : L.obj A' ⟶ B)
    (q' : B ⟶ B') : adj.homEquiv A B' (L.map q ≫ c ≫ q') = q ≫ adj.homEquiv A' B c ≫ R.map q' := by
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

/-- The morphism of inverse-image ringed spaces `(X_y, f_y^{-1}𝒪_{κ(y)}) ⟶ (X, f^{-1}𝒪_Y)` of the
fibre square. -/
abbrev fibreBaseMap (y : Y) :
    inverseImageBase (f.fiberToSpecResidueField y) ⟶ inverseImageBase f :=
  inverseImageBaseMap (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y)
    pullback.condition

/-- The canonical map `Lg₀^*Ω^•_{X/Y} ⟶ Ω^•_{X_y/κ(y)}` of the fibre square, on the localizations
of the two de Rham complexes. -/
def fibreDeRhamComparison (y : Y) :
    (derivedPullback (fibreBaseMap f y)).obj (DerivedCategory.Q.obj (deRhamCochainComplex f)) ⟶
      DerivedCategory.Q.obj (deRhamCochainComplex (f.fiberToSpecResidueField y)) :=
  (derivedPullback (fibreBaseMap f y)).map
      ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f)) ≫
    ProperSmoothDeRham.deRhamBaseChangeComparison (f.fiberι y) (f.fiberToSpecResidueField y) f
      (Y.fromSpecResidueField y) pullback.condition ≫
    (DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt (f.fiberToSpecResidueField y))

section Abstract

variable {X' X Z W : RingedSpace.{u, u}} (g₀ : X' ⟶ X) (π' : X' ⟶ Z) (π : X ⟶ W) (g : Z ⟶ W)
  (sq : g₀ ≫ π = π' ≫ g)

/-- **Pullback of classes against the derived base change map, with coefficients changed.** For a
commutative square `g₀ ≫ π = π' ≫ g`, morphisms `q : K ⟶ M` in `D(𝒪_X)` and
`c : Lg₀^*M ⟶ K'`, `q' : K' ⟶ K''` in `D(𝒪_{X'})`, a class of `H^n(X, K)`, read in
`H^n(W, Rπ_*K)`, pulled back along `g` and carried by
`Lg^*Rπ_*q`, the base change map, and `Rπ'_*(c ≫ q')`, is, in `H^n(X', K'')`, the pullback of the
class along `g₀` carried by `Lg₀^*q ≫ c ≫ q'`. -/
theorem lerayCohomologyIso_derivedBaseChangeMap_comp
    {K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {K' K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (q : K ⟶ M) (c : (derivedPullback g₀).obj M ⟶ K') (q' : K' ⟶ K'') (n : ℤ)
    (x : cohomologyModule K n) :
    (lerayCohomologyIso π' K'' n).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
        ((derivedPullback g).map ((derivedPushforward π).map q) ≫
          (derivedBaseChangeMap g₀ π' π g sq M ≫ (derivedPushforward π').map c) ≫
          (derivedPushforward π').map q'))).hom
        (homologyPullback g ((derivedPushforward π).obj K) n
          ((lerayCohomologyIso π K n).inv x))) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X').map
        ((derivedPullback g₀).map q ≫ c ≫ q'))).hom (homologyPullback g₀ K n x) := by
  have h₁ : ((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
      ((derivedPushforward π).map q))).hom ((lerayCohomologyIso π K n).inv x) =
      (lerayCohomologyIso π M n).inv
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map q)).hom x) :=
    eq_inv_apply_of_hom_apply _ ((lerayCohomologyIso_naturality_apply π q n _).trans
      (congrArg _ (Iso.inv_hom_id_apply (lerayCohomologyIso π K n) x)))
  have h₃ :=
    Stacks.Cohomology.LerayComposite.lerayCohomologyIso_homologyPullback_derivedBaseChangeMap
      g₀ π' π g sq M n
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map q)).hom x)
  simp only [map_map_comp_apply]
  refine (lerayCohomologyIso_naturality_apply π' q' n _).trans ?_
  refine (congrArg _ (lerayCohomologyIso_naturality_apply π' c n _)).trans ?_
  refine congrArg (fun t => ((DerivedCategory.homologyFunctor _ n).map
    ((baseSections X').map q')).hom (((DerivedCategory.homologyFunctor _ n).map
    ((baseSections X').map c)).hom t)) ?_
  refine Eq.trans ?_ (homologyPullback_naturality g₀ q n x)
  have hBC := Stacks.Cohomology.SectionsPullback.derivedBaseChangeMap_eq_mate g₀ π' π g sq M
  refine Eq.trans ?_ ((congrArg (fun φ => (lerayCohomologyIso π' ((derivedPullback g₀).obj M) n).hom
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map φ)).hom
      (homologyPullback g ((derivedPushforward π).obj M) n ((lerayCohomologyIso π M n).inv
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map q)).hom x))))) hBC).trans
    h₃)
  refine congrArg (fun t => (lerayCohomologyIso π' ((derivedPullback g₀).obj M) n).hom
    (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections Z).map (derivedBaseChangeMap g₀ π' π g sq M))).hom t)) ?_
  exact (homologyPullback_naturality g ((derivedPushforward π).map q) n
    ((lerayCohomologyIso π K n).inv x)).symm.trans
      (congrArg (homologyPullback g ((derivedPushforward π).obj M) n) h₁)

end Abstract

/-- **The base change map to a fibre, on cohomology.** A class of `H^n(X, Ω^•_{X/Y})`, read in
`H^n(Y, Rf_*Ω^•_{X/Y})`, pulled back to `Spec κ(y)` and carried by the base change isomorphism,
is, in `H^n(X_y, Ω^•_{X_y/κ(y)})`, the pullback of the class along the fibre square followed by
the canonical map of de Rham complexes. -/
theorem lerayCohomologyIso_fibreBaseChange (y : Y) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) n) :
    (lerayCohomologyIso (inverseImageBaseProjection (f.fiberToSpecResidueField y))
        (DerivedCategory.Q.obj (deRhamCochainComplex (f.fiberToSpecResidueField y))) n).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections _).map
        (fibreBaseChange f y))).hom
        (homologyPullback (residuePoint y) (derivedDeRhamDirectImageUnbounded f) n
          ((lerayCohomologyIso (inverseImageBaseProjection f)
            (DerivedCategory.Q.obj (deRhamCochainComplex f)) n).inv x))) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections _).map
        (fibreDeRhamComparison f y))).hom
        (homologyPullback (fibreBaseMap f y) _ n x) :=
  lerayCohomologyIso_derivedBaseChangeMap_comp (fibreBaseMap f y)
    (inverseImageBaseProjection (f.fiberToSpecResidueField y)) (inverseImageBaseProjection f)
    (residuePoint y)
    (inverseImageBaseMap_comp_inverseImageBaseProjection _ _ f _ pullback.condition)
    ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f))
    (deRhamBaseChangeComparison (f.fiberι y) (f.fiberToSpecResidueField y) f
      (Y.fromSpecResidueField y) pullback.condition)
    ((DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt (f.fiberToSpecResidueField y)))
    n x

/-- **The comparison of de Rham complexes along the fibre square, on cohomology, through its
transpose.** The pullback of a class along `g₀` followed by the canonical map
`Lg₀^*Ω^•_{X/Y} ⟶ Ω^•_{X_y/κ(y)}` is the class carried by the canonical map of complexes
`Ω^•_{X/Y} ⟶ (g₀)_*Ω^•_{X_y/κ(y)}` and the comparison `(g₀)_* ⟶ Rg₀_*`, read through the Leray
identification for `g₀`. -/
theorem fibreDeRhamComparison_homologyPullback_eq (y : Y) (m : ℤ)
    (z : cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    ((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        (fibreDeRhamComparison f y))).hom (homologyPullback (fibreBaseMap f y) _ m z) =
      (lerayCohomologyIso (fibreBaseMap f y)
        (DerivedCategory.Q.obj (deRhamCochainComplex (f.fiberToSpecResidueField y))) m).hom
        (((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
          (DerivedCategory.Q.map (deRhamPushforwardInt (f.fiberι y) (f.fiberToSpecResidueField y) f
            (Y.fromSpecResidueField y) pullback.condition) ≫
          Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
            (fibreBaseMap f y) (deRhamComplexInt (f.fiberToSpecResidueField y))))).hom z) := by
  refine (homologyPullback_homEquiv (fibreBaseMap f y) (fibreDeRhamComparison f y) m z).trans ?_
  refine congrArg (fun φ => (lerayCohomologyIso (fibreBaseMap f y) _ m).hom
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map φ)).hom z)) ?_
  refine Eq.trans ?_ (homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ (f.fiberι y)
    (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y) pullback.condition)
  exact homEquiv_map_comp_comp (derivedAdjunction (fibreBaseMap f y)) _ _ _

/-- **Pullback of classes along the fibre square is the restriction of de Rham classes.** The
pullback along `g₀ : (X_y, f_y^{-1}𝒪_{κ(y)}) ⟶ (X, f^{-1}𝒪_Y)` of a de Rham class, followed by the
canonical map `Lg₀^*Ω^•_{X/Y} ⟶ Ω^•_{X_y/κ(y)}`, is the pullback of de Rham cohomology to the fibre
([Stacks, Tag 0FL6]), read through the comparison of the two realizations of de Rham cohomology
([Stacks, Tag 01F1]). -/
theorem fibreDeRhamComparison_homologyPullback (y : Y) (m : ℤ)
    (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) :
    ((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        (fibreDeRhamComparison f y))).hom
        (homologyPullback (fibreBaseMap f y) _ m
          ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom ξ)) =
      fibreDeRhamClass f y m ξ :=
  (fibreDeRhamComparison_homologyPullback_eq f y m _).trans
    (Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback
      (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y)
      pullback.condition m ξ).symm

/-- **The value of the Leray--Hirsch morphism on the fibre.** The pullback to `Spec κ(y)` of the
class of `1` in `H^m(Y, 𝒪_Y[-m])`, carried by `Li_y^*` of the morphism attached to `ξ` and by base
change to the fibre, is the restriction of `ξ` to the fibre, read through the Leray
identification of the fibre. -/
theorem homologyPullback_deRhamClassToDirectImage (y : Y) (m : ℤ)
    (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) :
    ((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        ((derivedPullback (residuePoint y)).map (deRhamClassToDirectImage f m ξ) ≫
          fibreBaseChange f y))).hom
        (homologyPullback (residuePoint y) _ m (unitCycleClass Y.toRingedSpace m)) =
      (lerayCohomologyIso (inverseImageBaseProjection (f.fiberToSpecResidueField y))
        (DerivedCategory.Q.obj (deRhamCochainComplex (f.fiberToSpecResidueField y))) m).inv
        (fibreDeRhamClass f y m ξ) := by
  have hev : evalUnit (derivedDeRhamDirectImageUnbounded f) m (deRhamClassToDirectImage f m ξ) =
      (lerayCohomologyIso (inverseImageBaseProjection f)
        (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).inv
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom ξ) :=
    eq_inv_apply_of_hom_apply _ (lerayCohomologyIso_evalUnit_deRhamClassToDirectImage f m ξ)
  refine eq_inv_apply_of_hom_apply _ ?_
  refine (congrArg _ (map_map_comp_apply (baseSections _) (DerivedCategory.homologyFunctor _ m)
    _ _ _)).trans ?_
  refine (congrArg (fun t => (lerayCohomologyIso _ _ m).hom
    (((DerivedCategory.homologyFunctor _ m).map
    ((baseSections _).map (fibreBaseChange f y))).hom t))
    (homologyPullback_naturality (residuePoint y) (deRhamClassToDirectImage f m ξ) m
      (unitCycleClass Y.toRingedSpace m)).symm).trans ?_
  refine (congrArg (fun t => (lerayCohomologyIso _ _ m).hom
    (((DerivedCategory.homologyFunctor _ m).map
    ((baseSections _).map (fibreBaseChange f y))).hom
      (homologyPullback (residuePoint y) (derivedDeRhamDirectImageUnbounded f) m t))) hev).trans ?_
  exact (lerayCohomologyIso_fibreBaseChange f y m _).trans
    (fibreDeRhamComparison_homologyPullback f y m ξ)

/-- The Leray identification `H^k(Spec κ(y), R(f_y)_*Ω^•_{X_y/κ(y)}) = H^k_{dR}(X_y/κ(y))` for the
fibre, as an isomorphism of `κ(y)`-vector spaces. -/
def fibreLerayEquiv (y : Y) (k : ℤ) :
    (restrictToField (ResidueType y)).obj
        (cohomologyModule (derivedDeRhamDirectImageUnbounded (f.fiberToSpecResidueField y)) k) ≃ₗ[
          ResidueType y] ↥(fibreDeRhamModule f y k) :=
  ((restrictToField (ResidueType y)).mapIso
    (lerayCohomologyIso (inverseImageBaseProjection (f.fiberToSpecResidueField y))
      (DerivedCategory.Q.obj (deRhamCochainComplex (f.fiberToSpecResidueField y))) k)).toLinearEquiv

/-- **The morphism `⨁_{i=1}^N 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` associated to `ξ_1, …, ξ_N`**: on the
`i`-th summand, the morphism attached to `ξ_i ∈ H^{n_i}_{dR}(X/Y)`. -/
def deRhamClassSumMorphism {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) :
    (⨁ fun i => DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i : ℤ))) ⟶
      derivedDeRhamDirectImageUnbounded f :=
  biproduct.desc fun i => deRhamClassToDirectImage f (n i : ℤ) (ξ i)

/-- **[Stacks, Tag 0FMP], the Leray--Hirsch theorem for de Rham cohomology.** Let `f : X ⟶ Y` be a
smooth proper morphism of schemes, let `n_1, …, n_N ≥ 0` be integers and let
`ξ_i ∈ H^{n_i}_{dR}(X/Y)`. If for every point `y ∈ Y` the images of `ξ_1, …, ξ_N` in
`H^*_{dR}(X_y/κ(y))` form a basis over `κ(y)`, then the morphism

`⨁_{i=1}^N 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}`

associated to `ξ_1, …, ξ_N` is an isomorphism in `D(𝒪_Y)`.

The source and the target are perfect, the target by [Stacks, Tag 0FM0], so it suffices that its
derived pullback to every point be an isomorphism; the formation of `Rf_*Ω^•_{X/Y}` commutes with
that base change ([Stacks, Tag 0FM0]), and over `κ(y)` the morphism carries the pullbacks of the
classes of `1` to the images of the `ξ_i` in the de Rham cohomology of the fibre, which form a
basis. -/
@[stacks 0FMP "the Leray-Hirsch isomorphism for de Rham cohomology: for f : X -> Y smooth \
proper, classes xi_i in H^{n_i}_dR(X/Y) whose images in H^*_dR(X_y/kappa(y)) form a \
kappa(y)-basis at every point y give an isomorphism (+)_i O_Y[-n_i] -> Rf_*Omega^bullet_{X/Y} in \
D(O_Y); the morphism is constructed from the classes through H^m_dR(X/Y) = \
Hom(O_Y[-m], Rf_*Omega^bullet_{X/Y}), and perfectness and base change of Rf_*Omega^bullet \
(Tag 0FM0) are the library's unconditional theorems"]
theorem isIso_deRhamClassSumMorphism [Smooth f] [IsProper f] {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ)))
    (hb : HasFibrewiseDeRhamBasis f n ξ) :
    IsIso (deRhamClassSumMorphism f n ξ) := by
  refine isIso_biproduct_desc_of_forall_basis f (fun i => (n i : ℤ)) _ fun y => ?_
  obtain ⟨b, hb⟩ := hb y
  let L := DFinsupp.mapRange.linearEquiv (fun k : ℤ => fibreLerayEquiv f y k)
  refine ⟨b.map L.symm, fun i => ?_⟩
  rw [Module.Basis.map_apply, hb i, homologyPullback_deRhamClassToDirectImage]
  exact (DFinsupp.mapRange_single (hf := fun k => (fibreLerayEquiv f y k).symm.map_zero)).trans
    rfl

end AlgebraicGeometry.DeRhamLerayHirsch
