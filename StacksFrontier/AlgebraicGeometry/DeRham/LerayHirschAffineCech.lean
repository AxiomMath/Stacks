module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechCupPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupAdditivity

/-!
# The Leray–Hirsch map over an affine base, on Čech classes

Let `f : X ⟶ Y` be smooth with `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)`, `R = Γ(S, 𝒪_S)`, let `U` be
a finite covering of `X` (with affine diagonal) by affine opens with affine intersections, and let
`x_i` be cocycles of `Tot(Č(U, Ω^•_{X/S}))` of degrees `n_i`, with classes
`ξ_i ∈ H^{n_i}_{dR}(X/S)`. This file identifies the map of the statement of [Stacks, Tag 0FUM],

`⨁_i H^{N-n_i}_{dR}(Y/S) ⟶ H^N_{dR}(X/S)`, `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`,

with the map induced on cohomology by `x̃ : ⨁_i Ω^•_{A/R}[-n_i] ⟶ Tot(Č(U, Ω^•_{X/S}))`, through
`H^N(⨁_i Ω^•_{A/R}[-n_i]) = ⨁_i H^{N-n_i}(Ω^•_{A/R})` and `H^*(Ω^•_{A/R}) = H^*_{dR}(Y/S)`, and
concludes that it is bijective as soon as the zeroth graded piece of `x̃` is a
quasi-isomorphism.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamCup_eq_cupHomScheme`: the identification on a
  summand.
* `AlgebraicGeometry.DeRhamKatzOdaCech.bijective_sum_deRhamCup_of_quasiIso`: the bijectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace Stacks.KatzOda.Cech

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{u}} {gR : R ⟶ A} (D : ChartData (ι := ι) gR)
  {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (EP : FormsData U D D.ψ D.ψ_ρ P)
  {I : Type u} [Fintype I] [DecidableEq I] (n : I → ℕ) (x : ∀ i, TotX U P (n i))

omit [Fintype ι] [DecidableEq ι] in
/-- **`x̃` on the summand `i`**: on a form of degree `b` placed in the summand `i`, `x̃` is the
product of `x_i` with the form. -/
theorem cupMap_injF (i : I) (N : ℤ) (b : ℕ) (hb : (n i : ℤ) + b = N)
    (ν : (ShiftedSum.intComplex gR).X (N + -(n i : ℤ))) :
    cupMap D EP n x N (ShiftedSum.injF gR n i N ν) =
      mulTot D EP b (toForms gR ((ShiftedSum.intXIso gR b (by omega)).hom ν)) hb (x i) := by
  rw [cupMap_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem ⟨b, hb⟩ (Finset.mem_univ _), ShiftedSum.injF_apply_self]
    rintro ⟨b', hb''⟩ _ hb'
    exact absurd (Subtype.ext (show b' = b by omega)) hb'
  · intro j _ hji
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [ShiftedSum.injF_apply_ne gR n hji]
    exact mulTot_zero_form D EP b'.1 b'.2 (x j)

end Stacks.KatzOda.Cech

namespace Stacks.KatzOda.ShiftedSum

variable {R A : CommRingCat.{u}} (gR : R ⟶ A) {I : Type u} [DecidableEq I] (n : I → ℕ)

/-- The summand `i` of a cocycle of `Ω^•_{A/R}` of degree `N - n_i` is a cocycle of
`⨁_i Ω^•_{A/R}[-n_i]` of degree `N`. -/
theorem d_injF_shift (i : I) (N : ℤ) (ν : (intComplex gR).X (N - n i))
    (hν : ((intComplex gR).d (N - n i) (N - n i + 1)).hom ν = 0) :
    ((complex gR n).d N (N + 1)).hom (injF gR n i N
      ((CochainComplex.shiftFunctorObjXIso (intComplex gR) (-(n i : ℤ)) N (N - n i)
        (by omega)).inv.hom ν)) = 0 := by
  rw [complex_d_apply gR n rfl, dTo_injF]
  have h1 := ConcreteCategory.congr_hom ((intComplex gR).XIsoOfEq_hom_comp_d
    (show N - (n i : ℤ) = N + -(n i : ℤ) by omega) (N + 1 + -(n i : ℤ))) ν
  have h2 := ConcreteCategory.congr_hom ((intComplex gR).d_comp_XIsoOfEq_hom
    (show N - (n i : ℤ) + 1 = N + 1 + -(n i : ℤ) by omega) (N - (n i : ℤ))) ν
  have h3 : ((intComplex gR).d (N + -(n i : ℤ)) (N + 1 + -(n i : ℤ))).hom
      ((CochainComplex.shiftFunctorObjXIso (intComplex gR) (-(n i : ℤ)) N (N - n i)
        (by omega)).inv.hom ν) = 0 := by
    refine (ConcreteCategory.comp_apply _ _ _).symm.trans (h1.trans (h2.symm.trans ?_))
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    rw [hν]
    exact map_zero _
  rw [h3, smul_zero, map_zero]

/-- **The class of a summand**: `homologyInj` sends the class of a cocycle `ν` of degree
`N - n_i` to the class of `ν` placed in the summand `i`. -/
theorem homologyInj_cocycleClass (i : I) (N : ℤ) (ν : (intComplex gR).X (N - n i))
    (hν : ((intComplex gR).d (N - n i) (N - n i + 1)).hom ν = 0) :
    (homologyInj gR n i N).hom ((cocycleClass (N - n i) (toMor ν)
      (AlgebraicGeometry.DeRhamKatzOdaCech.toMor_comp_d_eq_zero _ hν)).hom 1) =
    (cocycleClass N (toMor (injF gR n i N
      ((CochainComplex.shiftFunctorObjXIso (intComplex gR) (-(n i : ℤ)) N (N - n i)
        (by omega)).inv.hom ν)))
      (AlgebraicGeometry.DeRhamKatzOdaCech.toMor_comp_d_eq_zero _
        (d_injF_shift gR n i N ν hν))).hom 1 := by
  have h := liftCycles_homologyπ_homologyInj gR n i N (toMor ν)
    (AlgebraicGeometry.DeRhamKatzOdaCech.toMor_comp_d_eq_zero _ hν) _
    (AlgebraicGeometry.DeRhamKatzOdaCech.toMor_comp_d_eq_zero _ (d_injF_shift gR n i N ν hν))
    (by rw [← Category.assoc, Stacks.Cech.Hypercohomology.toMor_comp,
      Stacks.Cech.Hypercohomology.toMor_comp]; rfl)
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom ((Category.assoc _ _ _).trans h) 1).trans rfl)

end Stacks.KatzOda.ShiftedSum

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section Generic

/-- The class of the cocycle `ι z`, for `z` a cycle, is the homology class of `z`. -/
private theorem cocycleClass_toMor_iCycles {R : Type u} [Ring R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (d : ℤ) (ν : K.X d) (z : K.cycles d)
    (hz : (K.iCycles d).hom z = ν) (h : toMor ν ≫ K.d d (d + 1) = 0) :
    (cocycleClass d (toMor ν) h).hom 1 = (K.homologyπ d).hom z := by
  have hz' : (K.liftCycles (toMor ν) (d + 1) (CochainComplex.next ℤ d) h).hom 1 = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles d)).1 inferInstance
    exact (ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) 1).trans
      ((Stacks.Cech.Hypercohomology.toMor_apply_one _).trans hz.symm)
  exact (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hz')

/-- Every cohomology class of a complex of modules is the class of a cocycle. -/
theorem exists_cocycleClass_eq {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : ℤ) (c : K.homology d) :
    ∃ (ν : K.X d) (hν : (K.d d (d + 1)).hom ν = 0),
      (cocycleClass d (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1 = c := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ d)).1 inferInstance c
  have hν : (K.d d (d + 1)).hom ((K.iCycles d).hom z) = 0 :=
    (ConcreteCategory.congr_hom (K.iCycles_d d (d + 1)) z).trans rfl
  exact ⟨_, hν, cocycleClass_toMor_iCycles d _ z rfl _⟩

/-- The class of the zero cocycle vanishes. -/
theorem cocycleClass_toMor_zero {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : ℤ) (h : toMor (0 : K.X d) ≫ K.d d (d + 1) = 0) :
    (cocycleClass d (toMor (0 : K.X d)) h).hom 1 = 0 :=
  (cocycleClass_toMor_iCycles d 0 0 (map_zero _) h).trans (map_zero _)

/-- A cocycle stays a cocycle when its degree is respelled. -/
theorem d_XIsoOfEq_hom {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℤ) {d d' : ℤ}
    (h : d = d') (ν : K.X d) (hν : (K.d d (d + 1)).hom ν = 0) :
    (K.d d' (d' + 1)).hom ((K.XIsoOfEq h).hom ν) = 0 := by
  subst h
  exact hν

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c) (e : c.Embedding c')

/-- The identifications of the terms of an extension with the terms of the complex do not
depend on the spelling of the degree. -/
theorem extendXIso_hom_XIsoOfEq {i : ι} {d₁ d₂ d₃ : ι'} (h₁₂ : d₁ = d₂) (h₁₃ : d₁ = d₃)
    (h₂ : e.f i = d₂) (h₃ : e.f i = d₃) :
    ((K.extend e).XIsoOfEq h₁₂).hom ≫ (K.extendXIso e h₂).hom =
      ((K.extend e).XIsoOfEq h₁₃).hom ≫ (K.extendXIso e h₃).hom := by
  subst h₁₂ h₁₃
  rfl

end Generic

section Assembly

/-- The cup product of de Rham cohomology is additive in its second argument; in particular it
vanishes on `0`. -/
theorem deRhamCup_zero_right {X S : Scheme.{u}} (p : X ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))] (i j k : ℤ) (h : i + j = k)
    (a : Scheme.Hom.deRhamCohomologyBaseModule p i) :
    Scheme.Hom.deRhamCup p i j k h a 0 = 0 := by
  change (SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) k).hom.hom
    (Stacks.Cech.Hypercohomology.cup _ (Scheme.Hom.cechComputes_deRhamComplexPlus p)
      (Scheme.Hom.cechComputes_deRhamComplexPlus p) _ i j k h
      ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) i).inv.hom a)
      ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) j).inv.hom 0)) = 0
  rw [map_zero]
  have key := Stacks.Cech.Hypercohomology.cup_add_right _
    (Scheme.Hom.cechComputes_deRhamComplexPlus p) (Scheme.Hom.cechComputes_deRhamComplexPlus p)
    (SheafOfModules.deRhamCechPairing (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))) i j k h
    ((SheafOfModules.hypercohomologyIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) i).inv.hom a) 0 0
  rw [add_zero] at key
  rw [left_eq_add.1 key]
  exact map_zero _

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)
  {I : Type u} [Fintype I] [DecidableEq I] (n : I → ℕ)
  (x : ∀ i, TotX U (f ≫ g).sectionsDeRhamComplex (n i))
  (hx : ∀ i, totDTo U (f ≫ g).sectionsDeRhamComplex (n i) (n i + 1) rfl (x i) = 0)

omit [IsAffine Y] [IsAffine S] [Smooth f] [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] in
include hx in
/-- The Čech total differential of `Tot(Č(U, Ω^•_{X/S}))` vanishes on each cocycle `x i`. -/
theorem d_x (i : I) :
    ((cechTot U (f ≫ g).sectionsDeRhamComplex).d (n i) (n i + 1)).hom (x i) = 0 := by
  rw [cechTot_d_apply' U _ rfl]
  exact hx i

/-- The class `ξ_i ∈ H^{n_i}_{dR}(X/S)` of the cocycle `x_i`. -/
def cechDeRhamClass (i : I) : Scheme.Hom.deRhamCohomologyBaseModule (f ≫ g) (n i) :=
  (classMap (f ≫ g) U hU (n i)).hom ((cocycleClass (n i) (toMor (x i))
    (toMor_comp_d_eq_zero _ (d_x f g U n x hx i))).hom 1)

omit [Smooth f] in
/-- Moving the degree of the second factor. -/
theorem deRhamCup_affine_transport [IsAffineHom (pullback.diagonal (terminal.from X))]
    (m : ℕ) {d : ℤ} (b : ℕ) (h : d = b) {N : ℤ} (hN : (m : ℤ) + d = N) (hN' : (m : ℤ) + b = N)
    (ξ : Scheme.Hom.deRhamCohomologyBaseModule (f ≫ g) m)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X d)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d d (d + 1)).hom ν = 0)
    (hν' : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom
      (((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).XIsoOfEq h).hom ν) = 0) :
    Scheme.Hom.deRhamCup (f ≫ g) m d N hN ξ (deRhamPullbackModule f g d ((affineClassMap g d).hom
      ((cocycleClass d (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1))) =
    Scheme.Hom.deRhamCup (f ≫ g) m b N hN' ξ (deRhamPullbackModule f g b ((affineClassMap g b).hom
      ((cocycleClass b (toMor (((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).XIsoOfEq
        h).hom ν)) (toMor_comp_d_eq_zero _ hν')).hom 1))) := by
  subst h
  rfl

/-- **The map of the statement of [Stacks, Tag 0FUM] on the summand `i` is `x̃`**: for a cocycle
`ν` of `Ω^•_{A/R}` of degree `N - n_i`, `ξ_i ∪ f^*[ν]` is the class of `x̃` applied to `ν` placed
in the summand `i`. -/
theorem deRhamCup_eq_cupHomScheme [IsAffineHom (pullback.diagonal (terminal.from X))] (i : I)
    (N : ℤ) (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X (N - n i))
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d (N - n i) (N - n i + 1)).hom
      ν = 0) :
    Scheme.Hom.deRhamCup (f ≫ g) (n i) (N - n i) N (by ring) (cechDeRhamClass f g U hU n x hx i)
        (deRhamPullbackModule f g (N - n i) ((affineClassMap g (N - n i)).hom
          ((cocycleClass (N - n i) (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1))) =
      (HomologicalComplex.homologyMap (cupHomScheme f g U haff n x hx) N ≫
        classMap (f ≫ g) U hU N).hom ((Stacks.KatzOda.ShiftedSum.homologyInj (baseMap g) n i N).hom
          ((cocycleClass (N - n i) (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1)) := by
  rw [Stacks.KatzOda.ShiftedSum.homologyInj_cocycleClass (baseMap g) n i N ν hν, cechDeRhamClass]
  refine Eq.trans ?_ (congrArg (classMap (f ≫ g) U hU N).hom (ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap (cupHomScheme f g U haff n x hx) N
      _ _) 1).symm)
  by_cases hN : (n i : ℤ) ≤ N
  · obtain ⟨b, hb⟩ : ∃ b : ℕ, (n i : ℤ) + b = N := ⟨(N - n i).toNat, by omega⟩
    have h : N - (n i : ℤ) = b := by omega
    have hν' := d_XIsoOfEq_hom _ h ν hν
    rw [deRhamCup_affine_transport f g (n i) b h _ hb _ ν hν hν',
      ← classMap_mulTot_intForm f g U haff hU (n i) b hb (x i) (d_x f g U n x hx i) _ hν']
    refine congrArg (classMap (f ≫ g) U hU N).hom (ConcreteCategory.congr_hom
      (Stacks.Cech.Hypercohomology.cocycleClass_congr N ?_ _ _) 1)
    refine Eq.trans ?_ (Stacks.Cech.Hypercohomology.toMor_comp _ _).symm
    refine congrArg toMor ((Stacks.KatzOda.Cech.cupMap_injF _ _ n x i N b hb _).trans ?_).symm
    refine congrArg (fun ω => Stacks.KatzOda.Cech.mulTot (chartData f g U haff)
      (formsDataTotal f g U haff) b ω hb (x i)) ?_
    exact congrArg (Stacks.KatzOda.Cech.toForms (baseMap g)) (ConcreteCategory.congr_hom
      (extendXIso_hom_XIsoOfEq _ ComplexShape.embeddingUpNat
        (show N - (n i : ℤ) = N + -(n i : ℤ) by omega) h
        (by change (b : ℤ) = N + -(n i : ℤ); omega) rfl) ν)
  · have := Stacks.KatzOda.ShiftedSum.subsingleton_intComplex_X (baseMap g) (N - n i)
      (by omega)
    obtain rfl : ν = 0 := Subsingleton.elim _ _
    refine Eq.trans (b := (0 : Scheme.Hom.deRhamCohomologyBaseModule (f ≫ g) N)) ?_ ?_
    · rw [cocycleClass_toMor_zero]
      refine (congrArg (Scheme.Hom.deRhamCup (f ≫ g) (n i) (N - n i) N (by ring)
        (cechDeRhamClass f g U hU n x hx i)) ((congrArg (deRhamPullbackModule f g (N - n i))
          (map_zero (affineClassMap g (N - n i)).hom)).trans
          (map_zero (deRhamPullbackModule f g (N - n i))))).trans ?_
      exact deRhamCup_zero_right _ _ _ _ _ _
    · have h0 : toMor (Stacks.KatzOda.ShiftedSum.injF (baseMap g) n i N
          ((CochainComplex.shiftFunctorObjXIso (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g))
            (-(n i : ℤ)) N (N - n i) (by omega)).inv.hom 0)) ≫
          (cupHomScheme f g U haff n x hx).f N = toMor 0 := by
        rw [Stacks.Cech.Hypercohomology.toMor_comp, map_zero, map_zero, map_zero]
      rw [Stacks.Cech.Hypercohomology.cocycleClass_congr N h0 _
        (toMor_comp_d_eq_zero _ (map_zero _)), cocycleClass_toMor_zero, map_zero]

omit [DecidableEq I] in
/-- **[Stacks, Tag 0FUM], given the quasi-isomorphism of the zeroth graded pieces**: for `f`
smooth, `Y`, `S` affine, a finite covering of `X` (with affine diagonal) by affine opens with
affine intersections and cocycles `x_i` of `Tot(Č(U, Ω^•_{X/S}))` of degrees `n_i` with classes
`ξ_i ∈ H^{n_i}_{dR}(X/S)`, if `⨁_i A[-n_i] ⟶ Tot(Č(U, Ω^•_{X/Y}))`, `1_i ↦ x̄_i`, is a
quasi-isomorphism then in every degree `N` the map `⨁_i H^{N-n_i}_{dR}(Y/S) ⟶ H^N_{dR}(X/S)`,
`(a_i) ↦ ∑ ξ_i ∪ f^*a_i`, is bijective. -/
theorem bijective_sum_deRhamCup_of_quasiIso [IsAffineHom (pullback.diagonal (terminal.from X))]
    [QuasiIso (unitHomScheme f g U haff n x hx)] (N : ℤ) :
    Function.Bijective (fun a : ∀ i, Scheme.Hom.deRhamCohomologyBaseModule g (N - n i) =>
      ∑ i, Scheme.Hom.deRhamCup (f ≫ g) (n i) (N - n i) N (by ring)
        (cechDeRhamClass f g U hU n x hx i) (deRhamPullbackModule f g (N - n i) (a i))) := by
  classical
  have hAff : Function.Bijective (fun (c : ∀ i,
      (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).homology (N - n i)) i =>
        (affineClassMap g (N - n i)).hom (c i)) :=
    Function.Bijective.piMap fun i => bijective_affineClassMap g (N - n i)
  have hT := (bijective_classMap_cupHomScheme f g U haff n x hx hU N).comp
    (Stacks.KatzOda.ShiftedSum.homologyEquiv (baseMap g) n N).bijective
  refine (Function.Bijective.of_comp_iff _ hAff).1 ?_
  convert hT using 1
  funext c
  change ∑ i, _ = (HomologicalComplex.homologyMap (cupHomScheme f g U haff n x hx) N ≫
    classMap (f ≫ g) U hU N).hom (∑ i, (Stacks.KatzOda.ShiftedSum.homologyInj (baseMap g) n i N).hom
      (c i))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨ν, hν, hc⟩ := exists_cocycleClass_eq (N - n i) (c i)
  beta_reduce
  rw [← hc]
  exact deRhamCup_eq_cupHomScheme f g U haff hU n x hx i N ν hν

end Assembly

end AlgebraicGeometry.DeRhamKatzOdaCech

end
