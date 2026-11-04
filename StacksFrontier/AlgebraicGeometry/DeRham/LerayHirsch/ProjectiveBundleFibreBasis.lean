module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundlePowers
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirschAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackIsomorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupPower
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FibreProjectiveSpace

/-!
# The fibre classes of the cup powers of `c₁^{dR}(𝒪_P(1))` form a basis

Let `g : X ⟶ S` be a morphism of schemes, `ℰ` a quasi-coherent `𝒪_X`-module, finite locally free of
constant rank `n + 1`, and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle. For every point `y ∈ X` the
images in `H^*_{dR}(P_y/κ(y))` of the classes `c₁^{dR}(𝒪_P(1))^t ∈ H^{2t}_{dR}(P/S)`,
`0 ≤ t ≤ n`, form a basis over `κ(y)`. This is the step "the classes `c₁^{dR}(𝒪_P(1))^i`
restricted to a fibre `X_y = ℙ^{r-1}_y` freely generate the de Rham cohomology `H^*_{dR}(X_y/y)`
over `κ(y)`, see Lemma 0FMJ" of the proof of [Stacks, Tag 0FMT]: it is the fibre hypothesis of
the Leray–Hirsch theorem (Tag 0FMR, and Tag 0FUM over an affine base) for these classes.

## The argument

The fibre `P_y` is `ℙⁿ_{κ(y)}` by a cartesian square along which `𝒪_P(1)` pulls back to `𝒪(1)`
(`Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle`). Pullback along the resulting
isomorphism `ℙⁿ_{κ(y)} ≅ P_y` over `Spec κ(y)` is a `κ(y)`-linear isomorphism of de Rham
cohomology (`Stacks.ProjectiveBundleDeRham.coeffDeRhamPullbackEquiv`); it carries the fibre
classes of the powers to the powers of `c₁^{dR}(𝒪(1))`, since pullback is multiplicative, preserves
the unit and commutes with the first Chern class (Tag 0FMD), and those form a basis by Tag 0FMJ
(`Stacks.ProjectiveBundleDeRham.exists_basis_projectiveDeRhamCohomology_classPow`).

## Main results

* `Stacks.ProjectiveBundleDeRham.coeffDeRhamPullbackEquiv`: pullback along an isomorphism over
  `Spec R` is an `R`-linear isomorphism of de Rham cohomology.
* `Stacks.ProjectiveBundleDeRham.projectiveBundleChernClass_eq_deRhamFirstChernClassPicard`.
* `Stacks.ProjectiveBundleDeRham.exists_basis_fibreClassOverS_classPow`: **the fibre basis.**

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.ProjectiveBundleDeRham

/-! ### Pullback along an isomorphism over `Spec R` is `R`-linear -/

section Linear

variable {R : CommRingCat.{u}} {X X' : Scheme.{u}} (ψ : X' ⟶ X) (p : X ⟶ Spec R)
  (p' : X' ⟶ Spec R) (w : ψ ≫ p = p' ≫ 𝟙 (Spec R))

/-- `H^m_{dR}(X/R)` as an `R`-module, through `R ≅ Γ(Spec R, 𝒪)`. -/
abbrev coeffDeRhamModule {X : Scheme.{u}} (p : X ⟶ Spec R) (m : ℤ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom).obj
    (Scheme.Hom.deRhamCohomologyBaseModule p m)

/-- **Pullback of de Rham cohomology along a morphism over `Spec R` is `R`-linear.** -/
def coeffDeRhamPullback (m : ℤ) : coeffDeRhamModule p m →ₗ[R] coeffDeRhamModule p' m where
  toFun := Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ p' p (𝟙 _) w m
  map_add' := map_add _
  map_smul' a x :=
    (Stacks.DeRhamBaseChange.deRhamPullbackSquare_smul ψ p' p (𝟙 _) w m _ x).trans
      (congrArg (· • _) (Stacks.DeRhamWeil.globalRingHom_inverseImageBaseMap_baseScalarHom p ψ p'
        (𝟙 _) w ((Scheme.ΓSpecIso R).inv.hom a)))

/-- The `R`-linear pullback `coeffDeRhamPullback` agrees, as a function, with
`Stacks.DeRhamBaseChange.deRhamPullbackSquare`. -/
theorem coeffDeRhamPullback_apply (m : ℤ) (x : coeffDeRhamModule p m) :
    coeffDeRhamPullback ψ p p' w m x =
      Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ p' p (𝟙 _) w m x :=
  rfl

/-- **Pullback along an isomorphism over `Spec R` is an `R`-linear isomorphism** of de Rham
cohomology. -/
def coeffDeRhamPullbackEquiv [IsIso ψ] (m : ℤ) :
    coeffDeRhamModule p m ≃ₗ[R] coeffDeRhamModule p' m :=
  LinearEquiv.ofBijective (coeffDeRhamPullback ψ p p' w m)
    (Stacks.DeRhamBaseChange.bijective_deRhamPullbackSquare_of_isIso ψ p' p w m)

end Linear

/-! ### The first Chern class of the tautological twist -/

section ChernClass

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **The de Rham first Chern class of an invertible module is its first Chern class on the
Picard group**: both are logarithmic differentiation, carried to the module realization. -/
theorem deRhamCohomologyFirstChernClass_eq_deRhamFirstChernClassPicard (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hL' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L) :
    Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard p
        (Stacks.WeilCohomology.picardClassOf X L hL) =
      SheafOfModules.deRhamCohomologyFirstChernClass (X := X.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) L hL' := by
  have e : Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
      (Stacks.WeilCohomology.picardClassOf X L hL) =
      Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (_root_.structureSheaf X.toRingedSpace.sheaf).property L hL' :=
    Stacks.GluePicard.picardModelAddEquiv_classOf X.toRingedSpace L _
  refine (congrArg (fun c => (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
      2).hom.hom (SheafOfModules.deRhamFirstChernClassAbelian (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) c)) e).trans ?_
  rfl

/-- `c₁^{dR}(𝒪_P(1))` is the first Chern class of the class of `𝒪_P(1)` in `Pic(P)`. -/
theorem projectiveBundleChernClass_eq_deRhamFirstChernClassPicard (g : X ⟶ S) (E : X.Modules)
    [E.IsQuasicoherent] :
    DeRhamLerayHirsch.projectiveBundleChernClass g E =
      Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard (projectiveBundleToBase X E ≫ g)
        (Stacks.WeilCohomology.picardClassOf _ (tautologicalDatumTwist E)
          (isInvertible_tautologicalDatumTwist E)) :=
  (deRhamCohomologyFirstChernClass_eq_deRhamFirstChernClassPicard _ _ _ _).symm

end ChernClass

/-! ### The fibre basis -/

section FibreBasis

/-- The fibre class is the pullback along the fibre square, on the module realization. -/
theorem fibreClassOverS_eq {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (y : Y) (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    DeRhamLerayHirsch.fibreClassOverS f g y m ξ =
      Stacks.DeRhamBaseChange.deRhamPullbackSquare (f.fiberι y) (f.fiberToSpecResidueField y)
        (f ≫ g) (Y.fromSpecResidueField y ≫ g) (DeRhamLerayHirsch.fiberι_comp_comp f g y) m ξ :=
  rfl

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

variable {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules) [E.IsQuasicoherent] (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- **The fibre classes of the cup powers of `c₁^{dR}(𝒪_P(1))` form a basis**: for every point
`y ∈ X`, the images in `⨁_m H^m_{dR}(P_y/κ(y))` of `c₁^{dR}(𝒪_P(1))^t ∈ H^{2t}_{dR}(P/S)`,
`0 ≤ t ≤ n`, form a `κ(y)`-basis. This is the fibre hypothesis of the Leray–Hirsch theorem
(Tags 0FMR, 0FUM) for the projective bundle of a module finite locally free of rank `n + 1`. -/
theorem exists_basis_fibreClassOverS_classPow (y : X) :
    ∃ b : Module.Basis (Fin (n + 1)) (X.residueField y)
        (DirectSum ℤ fun m : ℤ =>
          ↥(DeRhamLerayHirsch.fibreDeRhamModule (projectiveBundleToBase X E) y m)),
      ∀ i : Fin (n + 1), b i = DirectSum.lof (X.residueField y) ℤ
        (fun m : ℤ => ↥(DeRhamLerayHirsch.fibreDeRhamModule (projectiveBundleToBase X E) y m))
        ((2 * (i : ℕ) : ℕ) : ℤ)
        (DeRhamLerayHirsch.fibreClassOverS (projectiveBundleToBase X E) g y ((2 * (i : ℕ) : ℕ) : ℤ)
          (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
            (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)) := by
  classical
  obtain ⟨φ, hpb, htw⟩ := Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle E n y
  let q : AlgebraicGeometry.Proj
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (X.residueField y) n) ⟶
      Spec (X.residueField y) := projToSpecCoeff (X.residueField y) n
  let ψ := hpb.isoPullback
  have hψ1 : ψ.hom ≫ (projectiveBundleToBase X E).fiberι y = φ := hpb.isoPullback_hom_fst
  have hψ2 : ψ.hom ≫ (projectiveBundleToBase X E).fiberToSpecResidueField y = q :=
    hpb.isoPullback_hom_snd
  have w : ψ.hom ≫ (projectiveBundleToBase X E).fiberToSpecResidueField y = q ≫ 𝟙 _ :=
    hψ2.trans (Category.comp_id _).symm
  let e : ∀ m : ℤ,
      DeRhamLerayHirsch.fibreDeRhamModule (projectiveBundleToBase X E) y m ≃ₗ[X.residueField y]
        coeffDeRhamModule q m := fun m =>
    coeffDeRhamPullbackEquiv ψ.hom ((projectiveBundleToBase X E).fiberToSpecResidueField y) q w m
  let eS := DFinsupp.mapRange.linearEquiv e
  obtain ⟨bQ, hbQ⟩ := exists_basis_projectiveDeRhamCohomology_classPow n (X.residueField y)
  refine ⟨bQ.map eS.symm, fun i => ?_⟩
  rw [Module.Basis.map_apply, hbQ, LinearEquiv.symm_apply_eq]
  have w4 : φ ≫ (projectiveBundleToBase X E ≫ g) = q ≫ (X.fromSpecResidueField y ≫ g) := by
    rw [← Category.assoc, hpb.w, Category.assoc]
  have w3 : (ψ.hom ≫ (projectiveBundleToBase X E).fiberι y) ≫ (projectiveBundleToBase X E ≫ g) =
      q ≫ (𝟙 _ ≫ (X.fromSpecResidueField y ≫ g)) := by
    rw [hψ1, Category.id_comp]
    exact w4
  have key : e _ (DeRhamLerayHirsch.fibreClassOverS (projectiveBundleToBase X E) g y
      ((2 * (i : ℕ) : ℕ) : ℤ) (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
        (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)) =
      SheafOfModules.deRhamCohomologyPow _ _ 2 (projectiveChernClass (X.residueField y) n) i := by
    have h_comp := Stacks.DeRhamBaseChange.deRhamPullbackSquare_comp
      ((projectiveBundleToBase X E).fiberι y)
      ((projectiveBundleToBase X E).fiberToSpecResidueField y) (projectiveBundleToBase X E ≫ g)
      (X.fromSpecResidueField y ≫ g) (DeRhamLerayHirsch.fiberι_comp_comp _ g y) ψ.hom q (𝟙 _) w w3
      _ (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
        (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)
    have h_congr := Stacks.DeRhamBaseChange.deRhamPullbackSquare_congr (f' := q)
      (f := projectiveBundleToBase X E ≫ g) hψ1 (Category.id_comp _) w3 w4 _
      (DeRhamLerayHirsch.classPow (projectiveBundleToBase X E ≫ g) 2
        (DeRhamLerayHirsch.projectiveBundleChernClass g E) i)
    have h_pow := Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamCohomologyPow φ q
      (projectiveBundleToBase X E ≫ g) (X.fromSpecResidueField y ≫ g) w4 2
      (DeRhamLerayHirsch.projectiveBundleChernClass g E) i
    have h_c : Stacks.DeRhamBaseChange.deRhamPullbackSquare φ q (projectiveBundleToBase X E ≫ g)
        (X.fromSpecResidueField y ≫ g) w4 _ (DeRhamLerayHirsch.projectiveBundleChernClass g E) =
        projectiveChernClass (X.residueField y) n :=
      (congrArg (Stacks.DeRhamBaseChange.deRhamPullbackSquare φ q (projectiveBundleToBase X E ≫ g)
        (X.fromSpecResidueField y ≫ g) w4 _)
          (projectiveBundleChernClass_eq_deRhamFirstChernClassPicard g E)).trans
        ((Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamFirstChernClassPicard φ q
          (projectiveBundleToBase X E ≫ g) (X.fromSpecResidueField y ≫ g) w4
          (tautologicalDatumTwist E) (isInvertible_tautologicalDatumTwist E)).trans
          (congrArg (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard q)
            ((Stacks.ProjectiveBundleFibre.pullbackPicardHom_picardClassOf φ _ _).symm.trans htw)))
    exact (h_comp.trans h_congr).trans
      (h_pow.trans (congrArg (fun c => SheafOfModules.deRhamCohomologyPow _ _ 2 c i) h_c))
  rw [← key]
  exact (DFinsupp.mapRange_single (hf := fun m => map_zero (e m))).symm

end FibreBasis

end Stacks.ProjectiveBundleDeRham
