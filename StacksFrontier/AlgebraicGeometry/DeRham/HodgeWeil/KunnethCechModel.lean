module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechHodgeClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Kunneth
public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.SchemeCech
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.RestrictScalarsCechComputes
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# Hodge cohomology computed by a Čech covering

Let `f : X ⟶ S` be a morphism of schemes and `φ : k ⟶ Γ(X, f⁻¹𝒪_S)` a ring map. The sections of
`Ω^p_{X/S}` form a presheaf of `k`-modules `Stacks.HodgeWeil.hodgeSectionsK f φ p`, whose Čech
complex on a family `𝒰` of opens is the Čech complex of [Stacks, Tag 01ED]. The class
`Stacks.HodgeWeil.hodgeCechClass` of a Čech cocycle in `H^q(X, Ω^p_{X/S})` is additive, compatible
with the action of `k`, and unchanged by refinement of the covering ([Stacks, Tag 01FD]).

For a scheme `f : X ⟶ Spec k` over a field, the classes of Čech cocycles therefore give a
`k`-linear map `Ȟ^q(𝒰, Ω^p_{X/k}) ⟶ H^q(X, Ω^p_{X/k})`. When all finite intersections of the
covering are affine it is bijective: `Ω^p_{X/k}` is quasi-coherent, so it has no higher
cohomology on the affine intersections ([Stacks, Tag 01XB]), also when read as a sheaf of
`f⁻¹𝒪_{Spec k}`-modules, and Čech cohomology of such a covering computes cohomology
([Stacks, Tag 01XD]).

## Main definitions

* `Stacks.HodgeWeil.hodgeCechMap`: the `k`-linear class map
  `Ȟ^q(𝒰, Ω^p_{X/k}) ⟶ H^q(X, Ω^p_{X/k})`.

## Main results

* `Stacks.HodgeWeil.d_hodgeSectionsK`: the Čech differential of `hodgeSectionsK` is that of the
  underlying abelian presheaf.
* `Stacks.HodgeWeil.hodgeCechClass_add`, `Stacks.HodgeWeil.hodgeCechClass_smul`: the class of a
  Čech cocycle is additive and compatible with the scalars.
* `Stacks.HodgeWeil.hodgeCechClass_refCochain`: the class is unchanged by refinement.
* `Stacks.HodgeWeil.bijective_hodgeCechMap`: the class map is bijective when the finite
  intersections of the covering are affine.

## References

* [Stacks Project, Tag 01ED](https://stacks.math.columbia.edu/tag/01ED)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (SectionRing abSections)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm baseRingedSpace)
open Stacks.CechKunneth (Cochain d H Hmk refCochain)
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

/-! ### Acyclicity on coverings with affine finite intersections -/

/-- **A quasi-coherent module read over a sheaf of rings `R ⟶ 𝒪_X` and placed in degree zero is
acyclic on the finite intersections of a covering whose finite intersections are affine**: a
quasi-coherent module has no higher cohomology on an affine open ([Stacks, Tag 01XB]), and
restricting the sheaf of rings changes no cohomology group. -/
theorem isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen_inter (Y : Scheme.{u})
    {R : Sheaf (Opens.grothendieckTopology Y.carrier) CommRingCat.{u}}
    (ψ : Stacks.SheafOfModules.Tensor.ringSheaf R ⟶ Y.ringCatSheaf) (F : Y.Modules)
    [F.IsQuasicoherent] {J : Type u} (V : J → Y.Opens)
    (hV : ∀ (r : ℕ) (s : Fin (r + 1) → J), IsAffineOpen (⨅ j, V (s j)))
    (q : ℤ) (r : ℕ) (s : Fin (r + 1) → J) (m : ℕ) (hm : 0 < m) :
    IsZero (((_root_.SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)
      (op (⨅ k, V (s k)))).rightDerived m).obj
        ((singlePlus R ((_root_.SheafOfModules.restrictScalars ψ).obj F) 0).1.X q)) := by
  by_cases hq : q = 0
  · subst hq
    refine (Stacks.SerreCriterionH1.isZero_rightDerived_evaluation_of_isZero_hgroup
      (Stacks.SheafOfModules.Tensor.ringSheaf R) _ m _
      ((Stacks.Cohomology.ModuleComparison.isZero_hgroup_restrictScalars_iff ψ _ m F).2
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Y F _ (hV r s) m hm))).of_iso
      (((_root_.SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)
        (op (⨅ k, V (s k)))).rightDerived m).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _))
  · have : (_root_.SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)
        (op (⨅ k, V (s k)))).Additive :=
      Stacks.Cohomology.FlasqueAcyclic.evaluation_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf R) (op (⨅ k, V (s k)))
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

section General

variable {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) {I : Type u} (U : I → X.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The Čech class map of `Ω^p_{X/S}` on a covering with affine finite intersections is
bijective** ([Stacks, Tag 01XD]), `Ω^p_{X/S}` read as a sheaf of `f⁻¹𝒪_S`-modules. -/
theorem bijective_cechClass_deRhamTerm
    (hUaff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, U (s j))) (n : ℤ) :
    Function.Bijective (cechClass (baseRingedSpace (f.inverseImageRingSheaf)).sheaf U hU
      (singlePlus (baseRingedSpace (f.inverseImageRingSheaf)).sheaf
        (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0) n) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  refine bijective_cechClass_of_acyclic _ U hU _ (fun q r s m hm => ?_) n
  exact isZero_rightDerived_singlePlus_restrictScalars_of_isAffineOpen_inter X
    (R := (baseRingedSpace (f.inverseImageRingSheaf)).sheaf)
    (SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap f))
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) U hUaff q r s m hm

/-- `hodgeCechClass` is the class `Stacks.Cech.Hypercohomology.cechCocycleClassAt` of the
bounded below model of the ringed space `(X, f⁻¹𝒪_S)`, followed by the identification of the two
models of derived global sections. -/
theorem hodgeCechClass_eq {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0) :
    hodgeCechClass f U hU p c hc =
      ((DerivedCategory.homologyFunctor _ ((q : ℤ) + 0)).map
          ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
            (baseRingedSpace (f.inverseImageRingSheaf))).hom.app
            (singlePlus (baseRingedSpace (f.inverseImageRingSheaf)).sheaf
              (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0))).hom
        (cechCocycleClassAt U hU (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0 c
          hc) :=
  cechSheafClass_eq (baseRingedSpace (f.inverseImageRingSheaf)) U hU
    (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) c hc

/-- **The class of a Čech cocycle is additive in the cocycle.** -/
theorem hodgeCechClass_add {q : ℕ}
    (c c' : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0)
    (hc' : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c' = 0) :
    hodgeCechClass f U hU p (c + c') (by rw [map_add, hc, hc', add_zero]) =
      hodgeCechClass f U hU p c hc + hodgeCechClass f U hU p c' hc' :=
  (hodgeCechClass_eq f p U hU _ _).trans ((congrArg _
    (cechCocycleClassAt_add U hU (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0 c c'
      hc hc')).trans ((map_add _ _ _).trans (congrArg₂ (· + ·)
        (hodgeCechClass_eq f p U hU c hc).symm (hodgeCechClass_eq f p U hU c' hc').symm)))

/-- The class `hodgeCechClass` of a Čech cocycle vanishes if its `cechCocycleClassAt` does. -/
private theorem hodgeCechClass_eq_zero_of_cechCocycleClassAt_eq_zero {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0)
    (h : cechCocycleClassAt U hU (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0 c hc =
      0) :
    hodgeCechClass f U hU p c hc = 0 :=
  (hodgeCechClass_eq f p U hU c hc).trans ((congrArg _ h).trans (map_zero _))

/-- **The class of a Čech coboundary is zero.** -/
theorem hodgeCechClass_eq_zero {q : ℕ}
    (t : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) (q + 1))
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) (q + 1) c = 0)
    (ht : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q t = c) :
    hodgeCechClass f U hU p c hc = 0 :=
  hodgeCechClass_eq_zero_of_cechCocycleClassAt_eq_zero f p U hU c hc
    (cechCocycleClassAt_eq_zero U hU (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0
      t c hc ht)

/-- **The class of the zero cocycle is zero.** -/
theorem hodgeCechClass_zero (q : ℕ) :
    hodgeCechClass f U hU p (0 : CechCochains.Cochain U
      (abSections (deRhamTerm (formsAlgebras f) p)) q) (map_zero _) = 0 :=
  hodgeCechClass_eq_zero_of_cechCocycleClassAt_eq_zero f p U hU _ _
    (cechCocycleClassAt_eq_zero_of_eq_zero U hU 0 _ _ rfl)

variable {k : Type u} [CommRing k] (φ : k →+* hodgeBaseRing f)

/-- **The Čech differential of `hodgeSectionsK` is the Čech differential of the underlying
abelian presheaf** of `Ω^p_{X/S}`. -/
theorem d_hodgeSectionsK {q : ℕ} (c : Cochain (hodgeSectionsK f φ p) U q) :
    d (hodgeSectionsK f φ p) U q c =
      CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c := by
  funext s
  rw [Stacks.CechKunneth.d_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- **The class of a Čech cocycle is compatible with the scalars**: the class of `a • c` is
`φ(a)` times the class of `c`. -/
theorem hodgeCechClass_smul {q : ℕ} (a : k) (c : Cochain (hodgeSectionsK f φ p) U q)
    (hc : d (hodgeSectionsK f φ p) U q c = 0) :
    hodgeCechClass f U hU p (a • c : Cochain (hodgeSectionsK f φ p) U q)
        ((d_hodgeSectionsK f p U φ (a • c)).symm.trans
          ((map_smul (d (hodgeSectionsK f φ p) U q) a c).trans
            ((congrArg (a • ·) hc).trans (smul_zero a)))) =
      φ a • hodgeCechClass f U hU p c ((d_hodgeSectionsK f p U φ c).symm.trans hc) := by
  have hc' := (d_hodgeSectionsK f p U φ c).symm.trans hc
  have h := hypercohomologyMap_smulHom_cechCocycleClassAt
    (X := baseRingedSpace (f.inverseImageRingSheaf)) (φ a) U hU
    (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0 c hc'
  have h2 := (hypercohomologyMap_cechCocycleClassAt U hU 0
    (Stacks.Cohomology.InvertibleDerived.smulHom
      (X := baseRingedSpace (f.inverseImageRingSheaf)) (φ a)
      (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)) c hc').symm.trans h
  exact (hodgeCechClass_eq f p U hU _ _).trans ((congrArg _ h2).trans
    ((LinearMap.map_smul ((DerivedCategory.homologyFunctor _ ((q : ℤ) + 0)).map
      ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
        (baseRingedSpace (f.inverseImageRingSheaf))).hom.app
        (singlePlus (baseRingedSpace (f.inverseImageRingSheaf)).sheaf
          (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0))).hom (φ a) _).trans
      (congrArg (fun x => (show SectionRing (_root_.structureSheafRing
        (baseRingedSpace (f.inverseImageRingSheaf))) ⊤ from φ a) • x)
          (hodgeCechClass_eq f p U hU c hc').symm)))

/-- **The class of a Čech cocycle is unchanged by refinement** ([Stacks, Tag 01FD]): for
`r : J → I` with `V_j ⊆ U_{r j}`, the refined cocycle has the same class. -/
theorem hodgeCechClass_refCochain {J : Type u} (V : J → X.Opens) (hV : (⊤ : X.Opens) = ⨆ j, V j)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) {q : ℕ} (c : Cochain (hodgeSectionsK f φ p) U q)
    (hc : d (hodgeSectionsK f φ p) U q c = 0) :
    hodgeCechClass f V hV p (refCochain _ U V r hr q c)
        ((d_hodgeSectionsK f p V φ _).symm.trans
          ((Stacks.CechKunneth.refCochain_d _ U V r hr q c).trans
            ((congrArg _ hc).trans (map_zero _)))) =
      hodgeCechClass f U hU p c ((d_hodgeSectionsK f p U φ c).symm.trans hc) :=
  (hodgeCechClass_eq f p V hV _ _).trans ((congrArg _
    (cechCocycleClassAt_refinement U hU (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0
      V hV r hr c ((d_hodgeSectionsK f p U φ c).symm.trans hc))).trans
        (hodgeCechClass_eq f p U hU c _).symm)

end General

/-! ### The class map over a field -/

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : ℕ) {I : Type u}
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The class map** `Ȟ^q(𝒰, Ω^p_{X/k}) ⟶ H^q(X, Ω^p_{X/k})` of a scheme over a field `k`,
linear over `k`: the class `hodgeCechClass` of a Čech cocycle. -/
def hodgeCechMap (q : ℕ) :
    H (hodgeSectionsK f (hodgeScalarsOverField f) p) U q →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras f) p (q : ℤ) :=
  Submodule.liftQ _
    { toFun := fun c => hodgeCechClass f U hU p c.1
        ((d_hodgeSectionsK f p U _ c.1).symm.trans c.2)
      map_add' := fun c c' => hodgeCechClass_add f p U hU c.1 c'.1 _ _
      map_smul' := fun a c => hodgeCechClass_smul f p U hU _ a c.1 c.2 }
    (by
      cases q with
      | zero =>
        intro c hc
        simp only [Stacks.CechKunneth.coboundaries, Submodule.mem_bot] at hc
        subst hc
        exact hodgeCechClass_zero f p U hU 0
      | succ q =>
        rintro ⟨c, hc⟩ ⟨t, rfl⟩
        exact hodgeCechClass_eq_zero f p U hU t _
          ((d_hodgeSectionsK f p U _ _).symm.trans hc) (d_hodgeSectionsK f p U _ t).symm)

/-- The class map on the class of a cocycle is the class `hodgeCechClass` of the cocycle. -/
theorem hodgeCechMap_Hmk {q : ℕ} (c : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) p) U q)
    (hc : d (hodgeSectionsK f (hodgeScalarsOverField f) p) U q c = 0) :
    hodgeCechMap f p U hU q (Hmk _ U c hc) =
      hodgeCechClass f U hU p c ((d_hodgeSectionsK f p U _ c).symm.trans hc) :=
  rfl

/-- **The class of a Čech cocycle is compatible with the action of `k`.** -/
theorem hodgeCechClass_smul_field {q : ℕ} (a : k)
    (c : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) p) U q)
    (hc : d (hodgeSectionsK f (hodgeScalarsOverField f) p) U q c = 0) :
    hodgeCechClass f U hU p (a • c : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) p) U q)
        ((d_hodgeSectionsK f p U _ (a • c)).symm.trans
          ((map_smul (d (hodgeSectionsK f (hodgeScalarsOverField f) p) U q) a c).trans
            ((congrArg (a • ·) hc).trans (smul_zero a)))) =
      a • hodgeCechClass f U hU p c ((d_hodgeSectionsK f p U _ c).symm.trans hc) :=
  hodgeCechClass_smul f p U hU _ a c hc

/-- **The class map is compatible with refinement of coverings** ([Stacks, Tag 01FD]). -/
theorem hodgeCechMap_refCochain {J : Type u} (V : J → X.Opens) (hV : (⊤ : X.Opens) = ⨆ j, V j)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) {q : ℕ}
    (c : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) p) U q)
    (hc : d (hodgeSectionsK f (hodgeScalarsOverField f) p) U q c = 0) :
    hodgeCechMap f p V hV q (Hmk _ V (refCochain _ U V r hr q c)
        (by rw [Stacks.CechKunneth.refCochain_d, hc, map_zero])) =
      hodgeCechMap f p U hU q (Hmk _ U c hc) :=
  hodgeCechClass_refCochain f p U hU _ V hV r hr c hc

/-- **Hodge cohomology is computed by a covering with affine finite intersections**
([Stacks, Tag 01XD]): the class map `Ȟ^q(𝒰, Ω^p_{X/k}) ⟶ H^q(X, Ω^p_{X/k})` is bijective. -/
theorem bijective_hodgeCechMap
    (hUaff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, U (s j))) (q : ℕ) :
    Function.Bijective (hodgeCechMap f p U hU q) := by
  have hb := bijective_cechClass_deRhamTerm f p U hU hUaff ((q : ℤ) + 0)
  have hE := ConcreteCategory.bijective_of_isIso
    ((DerivedCategory.homologyFunctor _ ((q : ℤ) + 0)).mapIso
      ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
        (baseRingedSpace (f.inverseImageRingSheaf))).app
        (singlePlus (baseRingedSpace (f.inverseImageRingSheaf)).sheaf
          (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0))).hom
  refine ⟨?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Stacks.CechKunneth.Hmk_surjective _ U x
    have hc' := (d_hodgeSectionsK f p U _ c).symm.trans hc
    have hx' := hE.1 (((hodgeCechClass_eq f p U hU c hc').symm.trans hx).trans (map_zero _).symm)
    cases q with
    | zero =>
      rw [Stacks.CechKunneth.Hmk_eq_zero_iff_zero]
      exact eq_zero_of_cechCocycleClassAt_eq_zero U hU _ 0 hb.1 c hc' hx'
    | succ q =>
      rw [Stacks.CechKunneth.Hmk_eq_zero_iff_succ]
      obtain ⟨t, ht⟩ := exists_cechD_eq_of_cechCocycleClassAt_eq_zero U hU _ 0 hb.1 c hc' hx'
      exact ⟨t, (d_hodgeSectionsK f p U _ t).trans ht⟩
  · obtain ⟨y, rfl⟩ := hE.2 x
    obtain ⟨c, hc, rfl⟩ := exists_cechCocycleClassAt_eq_of_surjective U hU _ 0 q hb.2 y
    exact ⟨Hmk _ U c ((d_hodgeSectionsK f p U _ c).trans hc), hodgeCechClass_eq f p U hU c hc⟩

end Field

end Stacks.HodgeWeil

end
