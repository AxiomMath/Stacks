module

public import StacksFrontier.Algebra.Homology.Resolution.Defs.InjectiveResolution
public import StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Basic
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.ChangeOfRingsTorsion

/-!
# Derived torsion is the torsion subcomplex of an injective resolution

Let `A` be a commutative ring and `I ⊆ A` a finitely generated ideal. Section 47.8 of the
Stacks project, [Stacks, Tag 0BJA], introduces derived `I`-power torsion `RΓ_I`, the right derived
functor of `M ↦ M[I^∞] = ⋃_n M[I^n]`. This file computes it on an injective resolution: if
`M → J^0 → J^1 → ⋯` is a resolution of `M` by injective `A`-modules, then the termwise
`I`-power-torsion subcomplex `⋃_n J^•[I^n]` represents `RΓ_I(M)` in `D(A)`.

This file proves it for an arbitrary injective resolution of the single complex on `M`
and with no Noetherian hypothesis: a bounded-below complex of injectives is K-injective, and the
unit of the total right derived functor `RΓ_I` is invertible at a K-injective complex
(`Dualizing.TorsionCounit.isIso_derivedPowerTorsionUnit_app_of_isKInjective`), so the derived
functor is computed by the termwise torsion submodules. The isomorphism is pinned down by its
compatibility with the two maps onto `M⟦0⟧`: the inclusion of the torsion subcomplex followed by
the inverse of the resolution map on one side, and the structure map
`Stacks.LocalCohomology.derivedPowerTorsionObjCounit` on the other.

The declarations below carry no `stacks` attribute: Section 47.8 introduces `RΓ_I` as a
derived functor and does not state this computation as a separate result. The computation is not
about the functor `RΓ_Z` of Section 47.9, [Stacks, Tag 0952]: that functor is the right adjoint of
the inclusion `D_{I^∞-torsion}(A) → D(A)` (`Dualizing.localCohomologyRightAdjoint`), and by
[Stacks, Tag 0A6P] it differs from `RΓ_I` over a general ring.

## Main definitions

* `Stacks.LocalCohomology.powerTorsionComplexι` — the degreewise inclusion
  `Dualizing.powerTorsionComplex A I J ⟶ J` of the termwise `I`-power-torsion subcomplex.
* `Stacks.LocalCohomology.powerTorsionComplexIso` — the comparison between
  `Dualizing.powerTorsionComplex`, whose terms are cut out by
  `Dualizing.powerTorsionSubmodule`, and the spelling of the same subcomplex used by
  `Dualizing.TorsionCounit.powerTorsionSubcomplexι`, whose terms are `Ideal.primaryComponent`.
* `Stacks.LocalCohomology.injectiveResolutionIso` — the isomorphism `Q(J^•) ≅ M⟦0⟧` carried by an
  injective resolution.
* `Stacks.LocalCohomology.powerTorsionComplexInjectiveResolutionIso` — **the main result**:
  `Q(Γ_I(J^•)) ≅ RΓ_I(M)` for an injective resolution `J^•` of `M`.
* `Stacks.LocalCohomology.powerTorsionComplexComparison` — its underlying map, with an `IsIso`
  instance, for consumers that need a morphism rather than an isomorphism.

## Main results

* `Stacks.LocalCohomology.isKInjective_injectiveResolution_cocomplex` — the resolving complex of
  an injective resolution is K-injective.
* `Stacks.LocalCohomology.powerTorsionComplexComparison_comp_counit` — the comparison carries
  `Stacks.LocalCohomology.derivedPowerTorsionObjCounit` to the degreewise inclusion followed by
  the resolution isomorphism.
* `Stacks.LocalCohomology.powerTorsionComplexInjectiveResolutionIsoLocalCohomologyObj` — over a
  Noetherian ring the same complex computes `RΓ_Z` for `Z = V(I)`, by part (3) of
  [Stacks, Tag 0955].

## Implementation notes

`Dualizing.powerTorsionComplex` is written for `A : Type u` and modules in `ModuleCat.{u} A`,
while derived `I`-power torsion is universe polymorphic in the module. Everything here is
therefore at the diagonal `ModuleCat.{u} A`, which is the instance
`Stacks.LocalCohomology.derivedPowerTorsionObj.{u, u}`.

Noetherianity is not used for the main statement. It enters only in
`powerTorsionComplexInjectiveResolutionIsoLocalCohomologyObj`, through part (3) of
[Stacks, Tag 0955], which is where the source needs it as well: over a general ring `RΓ_I` and
`RΓ_Z` differ, by [Stacks, Tag 0A6P].

## References

* [Stacks Project, Tag 0BJA](https://stacks.math.columbia.edu/tag/0BJA)
* [Stacks Project, Tag 0952](https://stacks.math.columbia.edu/tag/0952)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### The two spellings of the termwise torsion subcomplex -/

/-- The submodule of elements killed by a power of `I` is Mathlib's `I`-primary component: both
are the union of the submodules annihilated by `I ^ n`. -/
lemma powerTorsionSubmodule_eq_primaryComponent (M : Type u) [AddCommGroup M] [Module A M] :
    Dualizing.powerTorsionSubmodule A I M = Ideal.primaryComponent M I := by
  apply le_antisymm
  · refine iSup_le fun n ↦ ?_
    intro x hx
    rw [Ideal.primaryComponent_mem]
    exact ⟨n, hx⟩
  · intro x hx
    rw [Ideal.primaryComponent_mem] at hx
    obtain ⟨n, hn⟩ := hx
    exact Submodule.mem_iSup_of_mem n hn

/-- The termwise `I`-power-torsion subcomplex of `J`, in the spelling used by
`Dualizing.TorsionCounit.powerTorsionSubcomplexι`. -/
abbrev torsionSubcomplex (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((Dualizing.powerTorsionFunctor.{u, u} A I).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (ObjectProperty.ι (fun M : ModuleCat.{u} A ↦ IsIPowerTorsion A M I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J

/-- The degreewise inclusion of the termwise `I`-power-torsion subcomplex into the complex. -/
def powerTorsionComplexι (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    Dualizing.powerTorsionComplex A I J ⟶ J where
  f n := ModuleCat.ofHom (Dualizing.powerTorsionSubmodule A I (J.X n)).subtype
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The two spellings of the termwise `I`-power-torsion subcomplex agree. -/
def powerTorsionComplexIso (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    Dualizing.powerTorsionComplex A I J ≅ torsionSubcomplex A I J := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) ?_
  · exact (LinearEquiv.ofEq _ _
      (powerTorsionSubmodule_eq_primaryComponent A I (J.X n))).toModuleIso
  · intro i j _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- The comparison of the two spellings is compatible with their inclusions into the complex. -/
lemma powerTorsionComplexIso_hom_comp_subcomplexι (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    (powerTorsionComplexIso A I J).hom ≫
        (Dualizing.TorsionCounit.powerTorsionSubcomplexι.{u, u} A I).app J =
      powerTorsionComplexι A I J := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-! ### Associativity and cancellation, in the shape used below -/

/-- Flattening the one bracketing that appears when the comparison is composed with the
structure map. -/
private lemma comp₆_comp₂_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C}
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) (f₅ : X₄ ⟶ X₅)
    (f₆ : X₅ ⟶ X₆) (f₇ : X₆ ⟶ X₇) (f₈ : X₇ ⟶ X₈) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ≫ f₇ ≫ f₈ =
      f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇ ≫ f₈ := by
  simp only [Category.assoc]

/-- Pasting a morphism onto an identity of three-fold composites. -/
private lemma comp₃_comp_eq {C : Type*} [Category C] {V W X Y Z : C} (a : V ⟶ W) (b : W ⟶ X)
    (c : X ⟶ Y) (d : V ⟶ Y) (h : a ≫ b ≫ c = d) (e : Y ⟶ Z) :
    a ≫ b ≫ c ≫ e = d ≫ e := by
  rw [← h]
  simp only [Category.assoc]

/-! ### The main statement, for an injective resolution -/

section Resolution

variable (hI : I.FG) (M : ModuleCat.{u} A)
  (R : CochainComplex.InjectiveResolution
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))

/-- The resolving complex of an injective resolution is K-injective: it is bounded below with
injective terms. -/
lemma isKInjective_injectiveResolution_cocomplex : R.cocomplex.IsKInjective := by
  obtain ⟨a, ha⟩ := R.boundedBelow
  have : R.cocomplex.IsStrictlyGE a := ha
  exact CochainComplex.isKInjective_of_injective R.cocomplex a

/-- An injective resolution of the single complex on `M` identifies the object it represents
with `M` placed in degree zero. -/
def injectiveResolutionIso :
    DerivedCategory.Q.obj R.cocomplex ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M :=
  (@asIso _ _ _ _ (DerivedCategory.Q.map R.ι)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr R.quasiIso)).symm ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm

/-- **The `I`-power-torsion subcomplex of an injective resolution represents `RΓ_I(M)`.** Let `A`
be a commutative ring, `I ⊆ A` a finitely generated ideal and `M` an `A`-module, and let
`M → J^•` be a resolution of `M` by injective `A`-modules. Then the termwise `I`-power-torsion
subcomplex `⋃_n J^•[I^n]` represents derived `I`-power torsion `RΓ_I(M)` in `D(A)`.

Here `RΓ_I` is derived `I`-power torsion of [Stacks, Tag 0BJA], not the functor `RΓ_Z` of
[Stacks, Tag 0952]; the two agree over a Noetherian ring, see
`Stacks.LocalCohomology.powerTorsionComplexInjectiveResolutionIsoLocalCohomologyObj`. No
Noetherian hypothesis is needed: a bounded-below complex of injectives is K-injective, and a right
derived functor is computed by a K-injective resolution.

The isomorphism is the composite of: the identification of the two spellings of the termwise
torsion subcomplex; the passage from the derived category to the homotopy category; the
comparison of `Γ_I` on the homotopy category with its derived-category avatar; the unit of the
total right derived functor `RΓ_I` at the K-injective complex `J^•`; the identification of
`Q(J^•)` with `M⟦0⟧`; and the comparison functor of [Stacks, Tag 0A6N]. Every factor is
invertible for formal reasons except the unit, which is invertible because `J^•` is
K-injective. -/
def powerTorsionComplexInjectiveResolutionIso :
    DerivedCategory.Q.obj (Dualizing.powerTorsionComplex A I R.cocomplex) ≅
      derivedPowerTorsionObj.{u, u} A I hI M :=
  DerivedCategory.Q.mapIso (powerTorsionComplexIso A I R.cocomplex) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
        (torsionSubcomplex A I R.cocomplex)).symm ≪≫
      ((Dualizing.powerTorsionModuleProperty A I hI).ι.mapDerivedCategoryFactorsh.app
          (((Dualizing.powerTorsionFunctor.{u, u} A I).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
                R.cocomplex))).symm ≪≫
        (Dualizing.powerTorsionModuleProperty A I hI).ι.mapDerivedCategory.mapIso
            (@asIso _ _ _ _ ((Dualizing.derivedPowerTorsionUnit.{u, u} A I hI).app
                ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
                  R.cocomplex))
              (Dualizing.TorsionCounit.isIso_derivedPowerTorsionUnit_app_of_isKInjective.{u, u}
                A I hI R.cocomplex
                (isKInjective_injectiveResolution_cocomplex A M R))) ≪≫
          (Dualizing.powerTorsionModuleProperty A I hI).ι.mapDerivedCategory.mapIso
              ((Dualizing.derivedPowerTorsion.{u, u} A I hI).mapIso
                ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app R.cocomplex ≪≫
                  injectiveResolutionIso A M R)) ≪≫
            ((Dualizing.powerTorsionComparisonCompInclusionIso.{u, u} A I hI).app
              ((Dualizing.derivedPowerTorsion.{u, u} A I hI).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).symm

/-- The forward map `Γ_I(J^•) ⟶ RΓ_I(M)` of
`Stacks.LocalCohomology.powerTorsionComplexInjectiveResolutionIso`. -/
def powerTorsionComplexComparison :
    DerivedCategory.Q.obj (Dualizing.powerTorsionComplex A I R.cocomplex) ⟶
      derivedPowerTorsionObj.{u, u} A I hI M :=
  (powerTorsionComplexInjectiveResolutionIso A I hI M R).hom

/-- The comparison map `Stacks.LocalCohomology.powerTorsionComplexComparison` is an
isomorphism. -/
instance isIso_powerTorsionComplexComparison :
    IsIso (powerTorsionComplexComparison A I hI M R) :=
  (powerTorsionComplexInjectiveResolutionIso A I hI M R).isIso_hom

/-- **The comparison carries the structure map of `RΓ_I(M)` to the degreewise inclusion.**
Composing `Stacks.LocalCohomology.powerTorsionComplexComparison` with the structure map
`Stacks.LocalCohomology.derivedPowerTorsionObjCounit` of `RΓ_I(M)` gives the degreewise
inclusion `Γ_I(J^•) ⟶ J^•` of the termwise torsion subcomplex followed by the identification of
`Q(J^•)` with `M⟦0⟧`.

This is the normalization of the counit of [Stacks, Tag 0A6L] read on the K-injective complex
`J^•`. -/
lemma powerTorsionComplexComparison_comp_counit :
    powerTorsionComplexComparison A I hI M R ≫ derivedPowerTorsionObjCounit.{u, u} A I hI M =
      DerivedCategory.Q.map (powerTorsionComplexι A I R.cocomplex) ≫
        (injectiveResolutionIso A M R).hom := by
  have hcan := Dualizing.derivedPowerTorsionCounit_isCanonical.{u, u} A I hI
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj R.cocomplex)
  rw [Dualizing.TorsionCounit.powerTorsionHomotopyInclusion_app_quotient_obj.{u, u} A I
    R.cocomplex] at hcan
  set ts := torsionSubcomplex A I R.cocomplex
  set iota := (Dualizing.TorsionCounit.powerTorsionSubcomplexι.{u, u} A I).app R.cocomplex
  set qc := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  set T := Dualizing.derivedPowerTorsion.{u, u} A I hI
  set Li := (Dualizing.powerTorsionModuleProperty A I hI).ι.mapDerivedCategory
  set Ph := (Dualizing.powerTorsionModuleProperty A I hI).ι.mapDerivedCategoryFactorsh
  set Pc := Dualizing.powerTorsionComparisonCompInclusionIso.{u, u} A I hI
  set eps := Dualizing.derivedPowerTorsionCounit.{u, u} A I hI
  set eta := Dualizing.derivedPowerTorsionUnit.{u, u} A I hI
  set KK := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj R.cocomplex
  set FhK := ((Dualizing.powerTorsionFunctor.{u, u} A I).mapHomotopyCategory
    (ComplexShape.up ℤ)).obj KK
  set sfM := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  set eM := (injectiveResolutionIso A M R).hom
  set Qhiota := DerivedCategory.Qh.map
    ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map iota)
  -- the canonicity equation of the counit at the K-injective complex, in this spelling
  have hcan' : Li.map (eta.app KK) ≫ eps.app (DerivedCategory.Qh.obj KK) =
      Ph.hom.app FhK ≫ Qhiota := hcan
  -- and the same, with the comparison on the homotopy category cancelled off
  have aux1 : Ph.inv.app FhK ≫ Li.map (eta.app KK) ≫
      eps.app (DerivedCategory.Qh.obj KK) = Qhiota :=
    (congrArg (fun x ↦ Ph.inv.app FhK ≫ x) hcan').trans
      (Iso.inv_hom_id_app_assoc Ph FhK Qhiota)
  -- naturality of the derived torsion counit along `Qh(J^•) ≅ M⟦0⟧`
  have stepB : Li.map (T.map (qc.hom.app R.cocomplex ≫ eM)) ≫ eps.app sfM =
      eps.app (DerivedCategory.Qh.obj KK) ≫ qc.hom.app R.cocomplex ≫ eM :=
    eps.naturality (qc.hom.app R.cocomplex ≫ eM)
  -- naturality of `quotient ⋙ Qh ≅ Q` along the degreewise inclusion
  have stepD : Qhiota ≫ qc.hom.app R.cocomplex ≫ eM =
      qc.hom.app ts ≫ DerivedCategory.Q.map iota ≫ eM :=
    (reassoc_of% (qc.hom.naturality iota)) eM
  -- the two spellings of the torsion subcomplex have the same inclusion
  have stepF : DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
      DerivedCategory.Q.map iota ≫ eM =
      DerivedCategory.Q.map (powerTorsionComplexι A I R.cocomplex) ≫ eM :=
    (reassoc_of% ((DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map
        (powerTorsionComplexIso_hom_comp_subcomplexι A I R.cocomplex)))) eM
  change (DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
      qc.inv.app ts ≫ Ph.inv.app FhK ≫ Li.map (eta.app KK) ≫
        Li.map (T.map (qc.hom.app R.cocomplex ≫ eM)) ≫ Pc.inv.app (T.obj sfM)) ≫
      Pc.hom.app (T.obj sfM) ≫ eps.app sfM =
    DerivedCategory.Q.map (powerTorsionComplexι A I R.cocomplex) ≫ eM
  refine (comp₆_comp₂_assoc _ _ _ _ _ _ _ _).trans ?_
  refine (congrArg (fun x ↦ DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
    qc.inv.app ts ≫ Ph.inv.app FhK ≫ Li.map (eta.app KK) ≫
      Li.map (T.map (qc.hom.app R.cocomplex ≫ eM)) ≫ x)
    (Iso.inv_hom_id_app_assoc Pc (T.obj sfM) (eps.app sfM))).trans ?_
  refine (congrArg (fun x ↦ DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
    qc.inv.app ts ≫ Ph.inv.app FhK ≫ Li.map (eta.app KK) ≫ x) stepB).trans ?_
  refine (congrArg (fun x ↦ DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
    qc.inv.app ts ≫ x)
    (comp₃_comp_eq _ _ _ _ aux1 (qc.hom.app R.cocomplex ≫ eM))).trans ?_
  refine (congrArg (fun x ↦ DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫
    qc.inv.app ts ≫ x) stepD).trans ?_
  refine (congrArg (fun x ↦ DerivedCategory.Q.map (powerTorsionComplexIso A I R.cocomplex).hom ≫ x)
    (Iso.inv_hom_id_app_assoc qc ts (DerivedCategory.Q.map iota ≫ eM))).trans stepF

/-- **Over a Noetherian ring the same complex computes `RΓ_Z` for `Z = V(I)`.** The canonical
comparison `RΓ_I ⟶ RΓ_Z` is invertible over a Noetherian ring — part (3) of
[Stacks, Tag 0955] — so the termwise `I`-power-torsion subcomplex of an injective resolution of
`M` also represents local cohomology with support in `V(I)`. -/
def powerTorsionComplexInjectiveResolutionIsoLocalCohomologyObj [IsNoetherianRing A] :
    DerivedCategory.Q.obj (Dualizing.powerTorsionComplex A I R.cocomplex) ≅
      (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor.{u, u} A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) :=
  powerTorsionComplexInjectiveResolutionIso A I hI M R ≪≫
    Dualizing.derivedPowerTorsionObjIsoLocalCohomologyObj.{u, u} A I hI M

end Resolution

end Stacks.LocalCohomology

end
