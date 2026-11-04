module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirschAffineCech
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechUnitBasis
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.KatzOdaCechProjectionPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.AffineBaseBasis
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.CechCupComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray–Hirsch theorem for de Rham cohomology over an affine base

Let `f : X ⟶ Y` be a smooth proper morphism of schemes over `S`, with `Y` and `S` affine, and let
`ξ_i ∈ H^{n_i}_{dR}(X/S)` be classes whose images in `H^*_{dR}(X_y/κ(y))` form a basis over
`κ(y)` at every point `y ∈ Y`. Then `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is an isomorphism
`⨁_i H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S)` ([Stacks, Tag 0FUM]).

The proof follows Stacks. Choose a finite covering `U` of `X` by affine opens (with affine
intersections, `X` being separated) and cocycles `x_i` of `K = Tot(Č(U, Ω^•_{X/S}))` representing
the `ξ_i`. The map `x̃ : ⨁_i Ω^•_{A/R}[-n_i] ⟶ K`, `ω ↦ ∑ x_i ∧ ω`, induces the map of the
statement on cohomology
(`AlgebraicGeometry.DeRhamKatzOdaCech.bijective_sum_deRhamCup_of_quasiIso`), and it is a
quasi-isomorphism as soon as its graded piece for the filtration by forms pulled back from `Y`,
`⨁_i A[-n_i] ⟶ Tot(Č(U, Ω^•_{X/Y}))`, `1_i ↦ x̄_i`, is one. The class of `x̄_i` in
`H^{n_i}_{dR}(X/Y)` is the image of `ξ_i` under `H_{dR}(X/S) ⟶ H_{dR}(X/Y)`
(`AlgebraicGeometry.DeRhamKatzOdaCech.classMap_projHom`), these images restrict to the images of
the `ξ_i` in the fibres, so [Stacks, Tag 0FMP] applies to them, and over the affine `Y` it says
that they form a basis of `H^*_{dR}(X/Y)` over `A = Γ(Y, 𝒪_Y)`
(`AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_smul_deRhamClass`).

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.fibreClassOverS`: the image of a class of `H^m_{dR}(X/S)`
  in `H^m_{dR}(X_y/κ(y))`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_deRhamCup_pullback`: [Stacks, Tag 0FUM].

## References

* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The pullback of de Rham cohomology only depends on the top map of the square. -/
theorem deRhamCohomologyPullback_congr {X X' S S' : Scheme.{u}} {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (h₁ : f₁ ≫ p = p' ≫ g) (h₂ : f₂ ≫ p = p' ≫ g)
    (i : ℤ) :
    deRhamCohomologyPullback f₁ p p' g h₁ i = deRhamCohomologyPullback f₂ p p' g h₂ i := by
  subst e
  rfl

/-- The cup product computed by Čech cocycles is the cup product of Section 0FKU, moved to the
degree `k = i + j`. -/
theorem deRhamCup_eq_eqToHom {X S : Scheme.{u}} (p : X ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))] (i j k : ℤ) (h : i + j = k)
    (x : deRhamCohomologyBaseModule p i) (y : deRhamCohomologyBaseModule p j) :
    deRhamCup p i j k h x y = (eqToHom (congrArg (SheafOfModules.deRhamCohomology
      (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p))) h)).hom
        (SheafOfModules.deRhamCohomologyCup _ _ i j x y) := by
  subst h
  exact deRhamCup_eq_deRhamCohomologyCup p i j x y

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The fibre square over `y`, composed with `g`. -/
theorem fiberι_comp_comp (y : Y) :
    f.fiberι y ≫ (f ≫ g) = f.fiberToSpecResidueField y ≫ (Y.fromSpecResidueField y ≫ g) :=
  pullback.condition_assoc g

/-- **The image of a class of `H^m_{dR}(X/S)` in the de Rham cohomology `H^m_{dR}(X_y/κ(y))` of
the fibre over `y`**: the pullback of de Rham cohomology ([Stacks, Tag 0FL6]) along the square
`(X_y ⟶ X, Spec κ(y) ⟶ S)`, in the module realization of de Rham cohomology through the
comparison of the two realizations ([Stacks, Tag 01F1]). -/
def fibreClassOverS (y : Y) (m : ℤ) (ξ : SheafOfModules.deRhamCohomology
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    ↥(fibreDeRhamModule f y m) :=
  (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom
    ((Scheme.Hom.deRhamCohomologyPullback (f.fiberι y) (f ≫ g) (f.fiberToSpecResidueField y)
      (Y.fromSpecResidueField y ≫ g) (fiberι_comp_comp f g y) m).hom
      ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m).inv.hom ξ))

/-- The image of a class of `H^m_{dR}(X/S)` in `H^m_{dR}(X/Y)`, in the abelian realization: the
pullback along the square `(𝟙 X, g)`. -/
def relativeClass (m : ℤ) (ξ : Scheme.Hom.deRhamCohomologyBaseModule (f ≫ g) m) :
    ToType (Scheme.Hom.deRhamCohomology f m) :=
  (Scheme.Hom.deRhamCohomologyPullback (𝟙 X) (f ≫ g) f g (Category.id_comp _) m).hom
    ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m).inv.hom ξ)

/-- The image in the fibre of the image in `H_{dR}(X/Y)` is the image in the fibre. -/
theorem fibreDeRhamClass_relativeClass (y : Y) (m : ℤ)
    (ξ : Scheme.Hom.deRhamCohomologyBaseModule (f ≫ g) m) :
    fibreDeRhamClass f y m (relativeClass f g m ξ) = fibreClassOverS f g y m ξ := by
  have h := (Scheme.Hom.deRhamCohomologyPullback_comp (f.fiberι y) (𝟙 X) (f ≫ g) f
    (f.fiberToSpecResidueField y) g (Y.fromSpecResidueField y) (Category.id_comp _)
    pullback.condition (by simpa only [Category.comp_id] using fiberι_comp_comp f g y) m).trans
    (Scheme.Hom.deRhamCohomologyPullback_congr (Category.comp_id _) _ _ _ _
      (fiberι_comp_comp f g y) m)
  exact congrArg (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ m).hom.hom
    (congrArg (fun φ => φ.hom ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m).inv.hom ξ)) h)

end AlgebraicGeometry.DeRhamLerayHirsch


namespace Stacks.KatzOda.Cech

/-- A cochain read in the same degree is itself. -/
theorem reTot_self.{w, v, w'} {C : Type w'} [Category.{v} C] [HasFiniteProducts C] {ι : Type w}
    (U : ι → C) {S : Type w} [Ring S] {P' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} S) ℕ} {q : ℤ}
    (h : q = q) (y : TotX U P' q) : reTot h y = y :=
  rfl

end Stacks.KatzOda.Cech

namespace CategoryTheory

/-- A morphism of modules on a linear combination. -/
theorem ModuleCat.hom_sum_smul {R : Type*} [Ring R] {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    {J : Type*} [Fintype J] (v : J → R) (z : J → M) :
    φ.hom (∑ j, v j • z j) = ∑ j, v j • φ.hom (z j) := by
  simp only [map_sum, map_smul]

end CategoryTheory

namespace AlgebraicGeometry.DeRhamKatzOdaCech

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)
  {r : ℕ} (n : Fin r → ℕ)
  (x : ∀ i : ULift.{u} (Fin r), TotX U (f ≫ g).sectionsDeRhamComplex (n i.down))
  (hx : ∀ i, totDTo U (f ≫ g).sectionsDeRhamComplex (n i.down) (n i.down + 1) rfl (x i) = 0)

/-- The images in `H_{dR}(X/Y)` of the classes `ξ_i` of the cocycles `x_i`. -/
abbrev relativeClasses (j : Fin r) : ToType (Scheme.Hom.deRhamCohomology f (n j : ℤ)) :=
  DeRhamLerayHirsch.relativeClass f g (n j)
    (cechDeRhamClass f g U hU (fun i : ULift.{u} (Fin r) => n i.down) x hx ⟨j⟩)

include hx in
/-- **The class of `x̄_i` in `H^{n_i}_{dR}(X/Y)` is the image of `ξ_i`.** -/
theorem classMap_unitClass (q : ℤ)
    (i : {i : ULift.{u} (Fin r) // ((fun i : ULift.{u} (Fin r) => n i.down) i : ℤ) = q}) :
    (classMap f U hU q).hom (Stacks.KatzOda.Cech.unitClass (chartData f g U haff)
        (formsDataTotal f g U haff) (fun i : ULift.{u} (Fin r) => n i.down) x hx
        (formsDataRel f g U haff) q i) =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ q).hom.hom
        (DeRhamLerayHirsch.castClass f n (relativeClasses f g U hU n x hx) q ⟨i.1.down, i.2⟩) := by
  obtain ⟨⟨i⟩, rfl⟩ := i
  have hpx : ((cechTot U f.sectionsDeRhamComplex).d (n i) (n i + 1)).hom
      ((Stacks.KatzOda.Cech.projHom (chartData f g U haff) (formsDataTotal f g U haff)
        (formsDataRel f g U haff)).totAddHom (n i) (x ⟨i⟩)) = 0 := by
    rw [cechTot_d_apply' U _ rfl]
    have h0 := Stacks.KatzOda.Cech.totDTo_xbar (chartData f g U haff) (formsDataTotal f g U haff)
      (fun i : ULift.{u} (Fin r) => n i.down) x hx (formsDataRel f g U haff) ⟨i⟩
    simp only [Stacks.KatzOda.Cech.xbar] at h0
    convert h0 using 3
  refine Eq.trans ?_ (classMap_projHom f g U hU haff (n i) (x ⟨i⟩)
    (d_x f g U (fun i : ULift.{u} (Fin r) => n i.down) x hx ⟨i⟩) hpx)
  refine congrArg (classMap f U hU (n i)).hom (ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.cocycleClass_congr _ (congrArg toMor ?_) _ _) 1)
  have h1 := Stacks.KatzOda.Cech.unitMap_single (chartData f g U haff) (formsDataTotal f g U haff)
    (fun i : ULift.{u} (Fin r) => n i.down) x (formsDataRel f g U haff) _ ⟨⟨i⟩, rfl⟩
  simp only [Stacks.KatzOda.Cech.xbar, Stacks.KatzOda.Cech.reTot_self] at h1
  convert h1 using 3

include hx in
/-- **The classes of the `x̄_i` form a basis of `H^*(Tot(Č(U, Ω^•_{X/Y})))` over `A`**, when the
images of the `ξ_i` in the fibres form bases ([Stacks, Tag 0FMP] over the affine `Y`). -/
theorem bijective_sum_smul_unitClass [IsProper f]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hUaff : ∀ i, IsAffineOpen (U i))
    (hb : DeRhamLerayHirsch.HasFibrewiseDeRhamBasis f n (relativeClasses f g U hU n x hx))
    (q : ℤ) :
    Function.Bijective (fun v : {i : ULift.{u} (Fin r) // ((n i.down : ℕ) : ℤ) = q} → Γ(Y, ⊤) =>
      ∑ i, v i • Stacks.KatzOda.Cech.unitClass (chartData f g U haff)
        (formsDataTotal f g U haff) (fun i : ULift.{u} (Fin r) => n i.down) x hx
        (formsDataRel f g U haff) q i) := by
  have := DeRhamLerayHirsch.isIso_deRhamClassSumMorphism f n _ hb
  refine (Function.Bijective.of_comp_iff' (bijective_classMap f U hU hUaff q) _).1 ?_
  let e : {i : ULift.{u} (Fin r) // ((n i.down : ℕ) : ℤ) = q} ≃
      {j : Fin r // ((n j : ℕ) : ℤ) = q} :=
    ⟨fun i => ⟨i.1.down, i.2⟩, fun j => ⟨⟨j.1⟩, j.2⟩, fun _ => rfl, fun _ => rfl⟩
  refine Eq.subst (motive := Function.Bijective) ?_
    ((DeRhamLerayHirsch.bijective_sum_smul_deRhamClass f n (relativeClasses f g U hU n x hx)
      q).comp (e.arrowCongr (Equiv.refl Γ(Y, ⊤))).bijective)
  funext v
  refine Eq.symm ((CategoryTheory.ModuleCat.hom_sum_smul (classMap f U hU q) v _).trans ?_)
  refine Fintype.sum_equiv e _ _ fun i => ?_
  exact congrArg (fun z : Scheme.Hom.deRhamCohomologyBaseModule f q =>
    @id (Y.sheaf.obj.obj (Opposite.op ⊤)) (v i) • z)
    (classMap_unitClass f g U haff hU n x hx q i)

include hx in
/-- **The graded piece of `x̃` is a quasi-isomorphism** under the hypotheses of
[Stacks, Tag 0FUM]. -/
theorem quasiIso_unitHomScheme_of_hasFibrewiseDeRhamBasis [IsProper f]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hUaff : ∀ i, IsAffineOpen (U i))
    (hb : DeRhamLerayHirsch.HasFibrewiseDeRhamBasis f n (relativeClasses f g U hU n x hx)) :
    QuasiIso (unitHomScheme f g U haff (fun i : ULift.{u} (Fin r) => n i.down) x hx) :=
  Stacks.KatzOda.Cech.quasiIso_unitHom_of_bijective _ _ _ x hx _
    (bijective_sum_smul_unitClass f g U haff hU n x hx hUaff hb)

end AlgebraicGeometry.DeRhamKatzOdaCech


namespace AlgebraicGeometry.DeRhamLerayHirsch

open DeRhamKatzOdaCech

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- Every de Rham class of degree `k` is the image under `classMap` of the class of a Čech
cocycle, for a cover by affine opens. -/
theorem exists_cocycle_classMap_eq (p : X ⟶ S) {ι : Type u} (U : ι → X.Opens)
    (hU : ⊤ = ⨆ i, U i) [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hUaff : ∀ i, IsAffineOpen (U i)) (k : ℕ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) (k : ℤ)) :
    ∃ (z : TotX U p.sectionsDeRhamComplex k)
      (hz : ((cechTot U p.sectionsDeRhamComplex).d k (k + 1)).hom z = 0),
      (classMap p U hU k).hom ((cocycleClass k (toMor z) (toMor_comp_d_eq_zero _ hz)).hom 1) =
        ξ := by
  obtain ⟨c, hc⟩ := (bijective_classMap p U hU hUaff _).2 ξ
  obtain ⟨z, hz, rfl⟩ := exists_cocycleClass_eq _ c
  exact ⟨z, hz, hc⟩

/-- A quasi-compact scheme is covered by finitely many affine opens, indexed by `ULift (Fin m)`. -/
theorem exists_ulift_affineOpens_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (m : ℕ) (U : ULift.{u} (Fin m) → X.Opens), (⊤ = ⨆ i, U i) ∧ ∀ i, IsAffineOpen (U i) := by
  obtain ⟨m, A, -, hA⟩ := exists_finite_affineOpens_cover_of_isCompact (Set.univ : Set X)
    isCompact_univ ⊤ (by simp)
  refine ⟨m, fun i => (A i.down).1, le_antisymm (fun p _ => ?_) le_top, fun i => (A i.down).2⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hA (Set.mem_univ p))
  exact Opens.mem_iSup.mpr ⟨⟨j⟩, hj⟩

/-- **[Stacks, Tag 0FUM]**, the Leray–Hirsch theorem over an affine base. Let `f : X ⟶ Y` be a
smooth proper morphism of schemes over `S`, with `Y` and `S` affine, let `n_1, …, n_r ≥ 0` and let
`ξ_i ∈ H^{n_i}_{dR}(X/S)` be classes whose images in `H^*_{dR}(X_y/κ(y))` form a basis over
`κ(y)` for every point `y ∈ Y`. Then

`⨁_{i=1}^r H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S)`, `(a_1, …, a_r) ↦ ∑ ξ_i ∪ f^*a_i`

is an isomorphism: in every degree `N` the map `⨁_i H^{N-n_i}_{dR}(Y/S) ⟶ H^N_{dR}(X/S)` is
bijective. -/
@[stacks 0FUM "Leray-Hirsch over an affine base: for f : X -> Y smooth proper over S with Y and \
S affine, and classes xi_i in H^{n_i}_dR(X/S) (n_i >= 0) whose images in H^*_dR(X_y/kappa(y)) \
form a kappa(y)-basis at every point y of Y, the map (+)_i H^*_dR(Y/S) -> H^*_dR(X/S), \
(a_i) |-> sum xi_i cup f^*a_i, is an isomorphism, i.e. bijective in every degree N"]
theorem bijective_sum_deRhamCup_pullback [Smooth f] [IsProper f] [IsAffine Y] [IsAffine S]
    {r : ℕ} (n : Fin r → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    (hb : ∀ y : Y, ∃ b : Module.Basis (Fin r) (Y.residueField y)
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
      ∀ i, b i = DirectSum.lof (Y.residueField y) ℤ (fun m : ℤ => ↥(fibreDeRhamModule f y m))
        (n i : ℤ) (fibreClassOverS f g y (n i : ℤ) (ξ i)))
    (N : ℤ) :
    Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (N - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) N))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (N - n i) (ξ i)
          (deRhamPullbackModule f g (N - n i) (a i)))) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsSeparated (terminal.from X) := by
    simpa using (inferInstance : IsSeparated (f ≫ terminal.from Y))
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  obtain ⟨m, U, hU, hUaff⟩ := exists_ulift_affineOpens_cover X
  have haff : ∀ {k : ℕ} (t : Fin (k + 1) → ULift.{u} (Fin m)), IsAffineOpen (inter U t) :=
    fun t => by
      rw [inter_eq_iInf]
      exact IsAffineOpen.iInf fun a => hUaff (t a)
  choose x hxd hxξ using fun i : ULift.{u} (Fin r) =>
    exists_cocycle_classMap_eq (f ≫ g) U hU hUaff (n i.down) (ξ i.down)
  have hx : ∀ i, totDTo U (f ≫ g).sectionsDeRhamComplex (n i.down) (n i.down + 1) rfl (x i) = 0 :=
    fun i => (cechTot_d_apply' U _ rfl (x i)).symm.trans (hxd i)
  have hcl : ∀ i, cechDeRhamClass f g U hU (fun i : ULift.{u} (Fin r) => n i.down) x hx i =
      ξ i.down := hxξ
  have hfb : HasFibrewiseDeRhamBasis f n (relativeClasses f g U hU n x hx) := by
    intro y
    obtain ⟨b, hb⟩ := hb y
    refine ⟨b, fun i => (hb i).trans ?_⟩
    rw [relativeClasses, fibreDeRhamClass_relativeClass, hcl]
  have := quasiIso_unitHomScheme_of_hasFibrewiseDeRhamBasis f g U haff hU n x hx hUaff hfb
  let E : (∀ i : Fin r, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (N - n i)) ≃
      (∀ i : ULift.{u} (Fin r), Scheme.Hom.deRhamCohomologyBaseModule g (N - n i.down)) :=
    ⟨fun a i => a i.down, fun a i => a ⟨i⟩, fun _ => rfl, fun _ => rfl⟩
  convert (bijective_sum_deRhamCup_of_quasiIso f g U haff hU
    (fun i : ULift.{u} (Fin r) => n i.down) x hx N).comp E.bijective using 1
  · rfl
  · refine heq_of_eq (funext fun a => ?_)
    refine Fintype.sum_equiv Equiv.ulift.symm _ _ fun i => ?_
    refine Eq.trans ?_ (Scheme.Hom.deRhamCup_eq_eqToHom (f ≫ g) _ _ _ _ _ _).symm
    exact congrArg (fun z => (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) N))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (N - n i) z
          (deRhamPullbackModule f g (N - n i) (a i)))) (hcl ⟨i⟩).symm

end AlgebraicGeometry.DeRhamLerayHirsch

end
