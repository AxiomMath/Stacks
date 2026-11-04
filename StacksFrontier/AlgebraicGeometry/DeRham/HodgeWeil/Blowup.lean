module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Data
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsRetractionCorrected
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingle
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Hodge cohomology and blowing up a smooth centre

Let `f : X ⟶ S` be smooth, let `Z ⊆ X` be a closed subscheme, cut out by a quasi-coherent ideal
`I`, which is smooth over `S` and has empty interior in `X`, and let `b : X' ⟶ X` be the blowing
up of `X` along `Z`. Proposition 0FUW of the Stacks project says that the canonical map
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a left inverse; its proof splits off each
`Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` in `D(𝒪_X)` ([Stacks, Tag 0G5J]). Applying `H^q(X, -)` degreewise
gives the statement for Hodge cohomology: the pullback
`b^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S})` is injective for all `p` and `q`. Over a field
this is axiom (A7) of Weil cohomology theories (Section 0FID) for Hodge cohomology, as Remark
0FWE asserts.

The Hodge pullback is defined through the sheaves of `f⁻¹𝒪_S`-modules `Ω^p_{X/S}` on `X`, as
`H^q(RΓ(X, -))` of `Ω^p_{X/S} ⟶ b₀_*Ω^p_{X'/S} ⟶ Rb₀_*Ω^p_{X'/S}` followed by the Leray
identification, where `b₀ : (X', (b ≫ f)⁻¹𝒪_S) ⟶ (X, f⁻¹𝒪_S)` is the morphism of the square. It
is therefore injective as soon as that map of `D(X, f⁻¹𝒪_S)` has a left inverse. Write
`ρ : (X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` and `ρ' : (X', 𝒪_{X'}) ⟶ (X', (b ≫ f)⁻¹𝒪_S)`, which are the
identity on spaces and restriction of scalars on modules, so that `ρ' ≫ b₀ = b ≫ ρ`. Since `ρ_*`
is exact, `Rρ_*` of the left inverse of `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` in `D(𝒪_X)` is a left
inverse of `Ω^p_{X/S} ⟶ Rρ_*Rb_*Ω^p_{X'/S}` in `D(X, f⁻¹𝒪_S)`, and the composition isomorphisms
`Rρ_*Rb_* ≅ R(b ≫ ρ)_* = R(ρ' ≫ b₀)_* ≅ Rb₀_*Rρ'_*` of [Stacks, Tag 0D5T] identify this map with
the one defining the Hodge pullback, followed by `Rb₀_*` of `Ω^p_{X'/S} ⟶ Rρ'_*Ω^p_{X'/S}`.

## Main results

* `Stacks.HodgeWeil.injective_cohomologyPullback_of_retraction`: a pullback on cohomology along a
  morphism of ringed spaces is injective when the underlying map `K ⟶ Rh_*K'` has a left inverse.
* `Stacks.HodgeWeil.exists_retraction_hodgeComparison`: a left inverse of
  `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` in `D(𝒪_X)` gives one of the map defining the Hodge pullback.
* `Stacks.HodgeWeil.injective_hodgePullback_blowUpToBase_ker`,
  `Stacks.HodgeWeil.injective_hodgePullback_of_isBlowUp_ker` (centre a closed immersion) and
  `Stacks.HodgeWeil.injective_hodgePullback_blowUpToBase`,
  `Stacks.HodgeWeil.injective_hodgePullback_of_isBlowUp` (centre a quasi-coherent ideal): the
  Hodge pullback along the blowing up of a smooth centre with empty interior is injective.
* `Stacks.HodgeWeil.injective_hodgeAlgebraPullback`: the pullback on `H^*_{Hodge}` is injective as
  soon as the pullbacks on the groups `H^q(X, Ω^p_{X/S})` are.
* `Stacks.HodgeWeil.injective_hodgePullback_blowupHom` and
  `Stacks.HodgeWeil.injective_pull_hodgeFirstChernClassData_blowupHom`: **axiom (A7) for Hodge
  cohomology** over a field, on the groups `H^q(X, Ω^p_{X/k})` and on `H^*_{Hodge}(X/k)`, for the
  blowing up `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupHom` in a nowhere dense closed
  immersion of smooth projective schemes; `Stacks.HodgeWeil.hodge_blowupAxiom` is (A7) in the
  shape `Stacks.WeilCohomology.FirstChernClassData.BlowupAxiom`.
* `Stacks.HodgeWeil.injective_hodgePullback_blowUp` and
  `Stacks.HodgeWeil.injective_pull_hodgeFirstChernClassData_blowUp`: the same for a blowing up
  presented by a quasi-coherent ideal of `X` with smooth closed subscheme.

## Implementation notes

A blowing up is given either by a closed immersion `i : Z ⟶ X` with `Z` smooth over the base,
blown up in its ideal `i.ker`, or by a quasi-coherent ideal `I` of `X` whose closed subscheme is
smooth over the base; in both cases `b` is identified with `AlgebraicGeometry.blowUpToBase` by an
isomorphism of `X'` with `AlgebraicGeometry.blowUp`. The base's blowing up
`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupHom i` of (A7) is
`Stacks.Blowup.blowUpToBase i.ker`, identified with `AlgebraicGeometry.blowUpToBase i.ker` by
`AlgebraicGeometry.blowUpIso`. The hypothesis that the centre has empty interior in `X` is the
one under which [Stacks, Tag 0G5J] is proved in
`Stacks.DeRham.existsUnique_blowUpFormsRetraction_blowUpToBase`; for a closed centre it is
nowhere density, the hypothesis of the base (A7). It cannot be dropped: for
`X = Z = Spec k` the ideal is zero, the blowing up is empty
(`Stacks.DeRham.isEmpty_blowUp_bot`), and `b^* : H^0(X, 𝒪_X) = k ⟶ 0` is not injective.

The derived categories are those of `HasDerivedCategory.standard`, in which the Hodge groups and
[Stacks, Tag 0G5J] are stated.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit
  derivedPushforwardCompIso)
open Stacks.Cohomology.LerayComposite (pushforwardCompComplexHom pushforwardComparisonQ_comp)

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard

section RingedSpace

variable {Z X Y : RingedSpace.{u, u}}

/-- The identity chain map `p_*(i_* I) ⟶ (i ≫ p)_* I`: in each degree the component of the
composition isomorphism `modulePushforwardComp`. It is inverse to
`Stacks.Cohomology.LerayComposite.pushforwardCompComplexHom`. -/
def pushforwardCompComplexInv (i : Z ⟶ X) (p : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (pushforwardComplex p).obj ((pushforwardComplex i).obj I) ⟶
      (pushforwardComplex (i ≫ p)).obj I where
  f j := (modulePushforwardComp i p).hom.app (I.X j)
  comm' j k _ := ((modulePushforwardComp i p).hom.naturality (I.d j k)).symm

/-- `pushforwardCompComplexInv` is a left inverse of `pushforwardCompComplexHom`. -/
@[reassoc (attr := simp)]
theorem pushforwardCompComplexInv_comp_hom (i : Z ⟶ X) (p : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    pushforwardCompComplexInv i p I ≫ pushforwardCompComplexHom i p I = 𝟙 _ := by
  ext j : 1
  exact (modulePushforwardComp i p).hom_inv_id_app (I.X j)

/-- **The comparison `m_* ⟶ Rm_*` along two equal morphisms of ringed spaces**: a morphism of
complexes into `m₂_*K`, transported to `m₁_*K` and followed by the comparison for `m₁`, is the
comparison for `m₂` followed by the identification `Rm₂_*K = Rm₁_*K`. -/
theorem pushforwardComparisonQ_congr {m₁ m₂ : X ⟶ Y} (e : m₁ = m₂)
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (l : L ⟶ (pushforwardComplex m₂).obj K) :
    DerivedCategory.Q.map (l ≫ pushforwardComplexCongr e.symm K) ≫ pushforwardComparisonQ m₁ K =
      DerivedCategory.Q.map l ≫ pushforwardComparisonQ m₂ K ≫
        eqToHom (congrArg (fun m => (derivedPushforward m).obj (DerivedCategory.Q.obj K))
          e.symm) := by
  subst e
  simp [pushforwardComplexCongr]

/-- **Along an exact direct image the comparison `h_* ⟶ Rh_*` is invertible**, at every complex:
the comparison of the derived functor
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit`) between the two
identifications of `Q` with `Qh ∘ quotient`. -/
instance isIso_pushforwardComparisonQ_of_preservesFiniteColimits (h : X ⟶ Y)
    [PreservesFiniteColimits (modulePushforward h)]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso (pushforwardComparisonQ h K) := by
  have : IsIso ((derivedPushforwardUnit h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
    have := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit h
    infer_instance
  unfold pushforwardComparisonQ
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

/-- **A retraction of `K ⟶ h_*K' ⟶ Rh_*K'` makes the pullback injective**: if the class of
`φ : K ⟶ h_*K'` followed by the comparison `h_*K' ⟶ Rh_*K'` has a left inverse in the derived
category, then the pullback `H^n(Z, K) ⟶ H^n(Z', K')` along `h` and `φ` is injective, since it is
`H^n(RΓ(Z, -))` of that split monomorphism followed by the Leray isomorphism. -/
theorem injective_cohomologyPullback_of_retraction (h : Z ⟶ X)
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (n : ℤ)
    (hr : ∃ r, (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K') ≫ r = 𝟙 _) :
    Function.Injective (cohomologyPullback h φ n).hom := by
  obtain ⟨r, hr⟩ := hr
  intro x y hxy
  have h1 : ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map
      (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K'))).hom x =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map
      (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K'))).hom y :=
    (ConcreteCategory.bijective_of_isIso
      (lerayCohomologyIso h (DerivedCategory.Q.obj K') n).hom).1 hxy
  have key : ∀ z, ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map r)).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map
        (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K'))).hom z) = z := fun z => by
    rw [← Stacks.Cohomology.HomologyPullback.map_map_comp_apply, hr, (baseSections X).map_id,
      (DerivedCategory.homologyFunctor _ n).map_id]
    rfl
  exact (key x).symm.trans ((congrArg _ h1).trans (key y))

end RingedSpace

section Scheme

/-- `Stacks.DeRham.pushforwardSingleToDerived` is the comparison of
`Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ` at a
complex concentrated in degree zero. -/
theorem pushforwardSingleToDerived_eq {X Y : Scheme.{u}} (g : X ⟶ Y) (N : X.Modules) :
    Stacks.DeRham.pushforwardSingleToDerived g N =
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pushforward g) (ComplexShape.up ℤ) 0).inv.app N) ≫
        pushforwardComparisonQ g.toLRSHom.toShHom
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) := by
  have hinv : (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).inv.app N =
      (DerivedCategory.quotientCompQhIso X.Modules).hom.app
        ((CochainComplex.singleFunctor X.Modules 0).obj N) :=
    congrArg Iso.inv (Iso.ext (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 N) :
      (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).app N =
        ((DerivedCategory.quotientCompQhIso X.Modules).app _).symm)
  rw [Stacks.DeRham.pushforwardSingleToDerived,
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app,
    Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app, hinv, pushforwardComparisonQ]
  exact (DerivedCategory.quotientCompQhIso_inv_naturality_assoc (C := Y.Modules) _ _).symm

end Scheme

section Square

variable {X X' S : Scheme.{u}}

/-- The sheaf `Ω^p_{X/S}` of relative differential `p`-forms of `g : X ⟶ S`, as an
`𝒪_X`-module placed in degree `0`. -/
abbrev formsSingleComplex (g : X ⟶ S) (p : ℕ) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (Scheme.Hom.relativeDifferentialForms g (p : ℤ))

variable (f : X ⟶ S) (b : X' ⟶ X) (p : ℕ)

/-- The canonical map `Ω^p_{X/S}[0] ⟶ b_*(Ω^p_{X'/S}[0])` of complexes of `𝒪_X`-modules: the map
`Ω^p_{X/S} ⟶ b_*Ω^p_{X'/S}` of `AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison` placed in
degree `0`. -/
def formsSingleDirectImage :
    formsSingleComplex f p ⟶
      (pushforwardComplex b.toLRSHom.toShHom).obj (formsSingleComplex (b ≫ f) p) :=
  (HomologicalComplex.single _ _ 0).map (Scheme.Hom.formsDirectImageComparison b f p) ≫
    (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward b)
      (ComplexShape.up ℤ) 0).inv.app _

/-- **The canonical map `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` of `D(𝒪_X)` is the comparison of
`formsSingleDirectImage`**: `Stacks.DeRham.formsDerivedDirectImage` is the class of the map of
complexes `Ω^p_{X/S}[0] ⟶ b_*(Ω^p_{X'/S}[0])` followed by the comparison `b_* ⟶ Rb_*`. -/
theorem formsDerivedDirectImage_eq_comparisonQ :
    Stacks.DeRham.formsDerivedDirectImage f b (p : ℤ) =
      DerivedCategory.Q.map (formsSingleDirectImage f b p) ≫
        pushforwardComparisonQ b.toLRSHom.toShHom (formsSingleComplex (b ≫ f) p) := by
  rw [Stacks.DeRham.formsDerivedDirectImage_eq, pushforwardSingleToDerived_eq]
  exact (DerivedCategory.Q.map_comp_assoc _ _ _).symm

/-- The identification of `Ω^p_{X/S}[0]`, as a complex of `g⁻¹𝒪_S`-modules, with the restriction
of scalars along `g⁻¹𝒪_S ⟶ 𝒪_X` of the complex of `𝒪_X`-modules `Ω^p_{X/S}[0]`. -/
def formsSingleRestrictScalars (g : X ⟶ S) (p : ℕ) :
    formsSingle g p ⟶ (pushforwardComplex (toInverseImageBase g)).obj (formsSingleComplex g p) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase g)) (ComplexShape.up ℤ) 0).inv.app
      (Scheme.Hom.relativeDifferentialForms g (p : ℤ))

/-- The identification `formsSingleRestrictScalars` is an isomorphism of complexes. -/
instance isIso_formsSingleRestrictScalars (g : X ⟶ S) (p : ℕ) :
    IsIso (formsSingleRestrictScalars g p) :=
  Iso.isIso_inv ((HomologicalComplex.singleMapHomologicalComplex
    (StacksDraft.KFlat.modulePushforward (toInverseImageBase g)) (ComplexShape.up ℤ) 0).app
      (Scheme.Hom.relativeDifferentialForms g (p : ℤ)))

variable (w : b ≫ f = (b ≫ f) ≫ 𝟙 S)

/-- **The canonical map of Hodge cohomology is the restriction of scalars of the one of
`𝒪_X`-modules.** Write `ρ : (X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)`, `ρ'` for its analogue on `X'` and
`b₀ : (X', (b ≫ f)⁻¹𝒪_S) ⟶ (X, f⁻¹𝒪_S)` for the morphism of the square, so that
`ρ' ≫ b₀ = b ≫ ρ`. Then the restriction of scalars of `Ω^p_{X/S}[0] ⟶ b_*(Ω^p_{X'/S}[0])`, read
in `(b ≫ ρ)_* = (ρ' ≫ b₀)_*`, is the canonical map `formsSinglePushforward` followed by `b₀_*` of
the identification of `Ω^p_{X'/S}[0]` with a restriction of scalars. On local sections both
sides are the pullback of differential forms. -/
theorem formsSinglePushforward_comp_restrictScalars :
    ((formsSingleRestrictScalars f p ≫ (pushforwardComplex (toInverseImageBase f)).map
        (formsSingleDirectImage f b p) ≫
        pushforwardCompComplexInv b.toLRSHom.toShHom (toInverseImageBase f) _) ≫
      pushforwardComplexCongr
        (toInverseImageBase_comp_inverseImageBaseMap b (b ≫ f) f (𝟙 S) w).symm _) ≫
      pushforwardCompComplexHom (toInverseImageBase (b ≫ f))
        (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w) _ =
    formsSinglePushforward b (b ≫ f) f (𝟙 S) w p ≫
      (pushforwardComplex (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w)).map
        (formsSingleRestrictScalars (b ≫ f) p) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  ext U x
  have e := toInverseImageBase_comp_inverseImageBaseMap b (b ≫ f) f (𝟙 S) w
  have h3 := pushforwardComplexCongr_f_val_app_heq e.symm (formsSingleComplex (b ≫ f) p) 0 U
    (((formsSingleRestrictScalars f p ≫ (pushforwardComplex (toInverseImageBase f)).map
        (formsSingleDirectImage f b p) ≫
        pushforwardCompComplexInv b.toLRSHom.toShHom (toInverseImageBase f) _).f 0).val.app U x)
  have hR : HEq (Scheme.Hom.relativeDifferentialFormsPullback b f (b ≫ f) (𝟙 S) w (p : ℤ) U.unop x)
      (((formsSinglePushforward b (b ≫ f) f (𝟙 S) w p ≫
        (pushforwardComplex (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w)).map
          (formsSingleRestrictScalars (b ≫ f) p)).f 0).val.app U x) :=
    (formsSinglePushforward_f_zero_val_app_heq b (b ≫ f) f (𝟙 S) w p U x).symm
  exact eq_of_heq (h3.trans hR)

/-- The bookkeeping of `exists_retraction_hodgeComparison`: `c₀` is, up to isomorphisms, the
split monomorphism `c`. -/
private theorem exists_retraction_of_comp_eq {C : Type*} [Category* C]
    {P P₁ Q₀ Q₁ M T₀ T₂ : C} (c₀ : P ⟶ Q₀) (U : P ⟶ P₁) [IsIso U] (c : P₁ ⟶ Q₁)
    (r : Q₁ ⟶ P₁) (hr : c ≫ r = 𝟙 P₁) (g₀ : Q₀ ⟶ T₀) (n : P ⟶ T₂) (e₀ : T₂ ⟶ T₀) [IsIso e₀]
    (m : P ⟶ M) (e₂ : M ⟶ T₂) [IsIso e₂] (e₁ : M ⟶ Q₁) (h₀ : n ≫ e₀ = c₀ ≫ g₀)
    (hn : n = m ≫ e₂) (h₁ : m ≫ e₁ = U ≫ c) :
    ∃ r₀, c₀ ≫ r₀ = 𝟙 P := by
  refine ⟨g₀ ≫ inv e₀ ≫ inv e₂ ≫ e₁ ≫ r ≫ inv U, ?_⟩
  rw [← Category.assoc c₀ g₀, ← h₀, hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [reassoc_of% h₁, reassoc_of% hr, IsIso.hom_inv_id]

/-- **A retraction of `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` in `D(𝒪_X)` gives one of the map defining the
Hodge pullback.** Restriction of scalars to `f⁻¹𝒪_S` is exact, so it carries the canonical map
of `D(𝒪_X)` to the canonical map `Ω^p_{X/S} ⟶ Rb₀_*Ω^p_{X'/S}` of `D(X, f⁻¹𝒪_S)` up to the
composition isomorphisms `R(b ≫ ρ)_* ≅ Rρ_* Rb_*` and `R(ρ' ≫ b₀)_* ≅ Rb₀_* Rρ'_*` of
[Stacks, Tag 0D5T]; a retraction of the former therefore yields one of the latter. -/
theorem exists_retraction_hodgeComparison
    (h : ∃ r, Stacks.DeRham.formsDerivedDirectImage f b (p : ℤ) ≫ r = 𝟙 _) :
    ∃ r₀, (DerivedCategory.Q.map (formsSinglePushforward b (b ≫ f) f (𝟙 S) w p) ≫
      pushforwardComparisonQ (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w)
        (formsSingle (b ≫ f) p)) ≫ r₀ = 𝟙 _ := by
  obtain ⟨r, hr⟩ := h
  have : PreservesFiniteColimits (modulePushforward (toInverseImageBase f)) :=
    preservesFiniteColimits_pushforward_toInverseImageBase f
  have e := toInverseImageBase_comp_inverseImageBaseMap b (b ≫ f) f (𝟙 S) w
  let K' := formsSingleComplex (b ≫ f) p
  let K := formsSingleComplex f p
  let l := formsSingleRestrictScalars f p ≫ (pushforwardComplex (toInverseImageBase f)).map
    (formsSingleDirectImage f b p) ≫
    pushforwardCompComplexInv b.toLRSHom.toShHom (toInverseImageBase f) K'
  have hl : l ≫ pushforwardCompComplexHom b.toLRSHom.toShHom (toInverseImageBase f) K' =
      formsSingleRestrictScalars f p ≫ (pushforwardComplex (toInverseImageBase f)).map
        (formsSingleDirectImage f b p) := by
    ext n U
    rfl
  have hk : (l ≫ pushforwardComplexCongr e.symm K') ≫
      pushforwardCompComplexHom (toInverseImageBase (b ≫ f))
        (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w) K' =
      formsSinglePushforward b (b ≫ f) f (𝟙 S) w p ≫
        (pushforwardComplex (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w)).map
          (formsSingleRestrictScalars (b ≫ f) p) :=
    formsSinglePushforward_comp_restrictScalars f b p w
  have h₁ := comparisonQ_comp_derivedPushforwardCompIso_inv (toInverseImageBase f)
    b.toLRSHom.toShHom (formsSingleRestrictScalars f p) (formsSingleDirectImage f b p) l hl
  have h₀ := comparisonQ_comp_derivedPushforwardCompIso_inv
    (inverseImageBaseMap b (b ≫ f) f (𝟙 S) w) (toInverseImageBase (b ≫ f))
    (formsSinglePushforward b (b ≫ f) f (𝟙 S) w p) (formsSingleRestrictScalars (b ≫ f) p)
    (l ≫ pushforwardComplexCongr e.symm K') hk
  have hn := pushforwardComparisonQ_congr e l
  have hr' : (DerivedCategory.Q.map (formsSingleDirectImage f b p) ≫
      pushforwardComparisonQ b.toLRSHom.toShHom K') ≫ r = 𝟙 _ := by
    rw [← formsDerivedDirectImage_eq_comparisonQ]
    exact hr
  have hΦ := ((derivedPushforward (toInverseImageBase f)).map_comp _ _).symm.trans
    ((congrArg (derivedPushforward (toInverseImageBase f)).map hr').trans
      ((derivedPushforward (toInverseImageBase f)).map_id _))
  have := isIso_pushforwardComparisonQ_of_preservesFiniteColimits (toInverseImageBase f) K
  have : IsIso (DerivedCategory.Q.map (formsSingleRestrictScalars f p) ≫
      pushforwardComparisonQ (toInverseImageBase f) K) := IsIso.comp_isIso
  exact exists_retraction_of_comp_eq _
    (DerivedCategory.Q.map (formsSingleRestrictScalars f p) ≫
      pushforwardComparisonQ (toInverseImageBase f) K) _ _ hΦ _ _ _ _ _ _ h₀
      (hn.trans (Category.assoc _ _ _).symm) h₁

end Square

/-! ### Injectivity of the Hodge pullback -/

section Injective

variable {X X' S : Scheme.{u}}

/-- **The Hodge pullback is injective when `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` has a left inverse**:
for a morphism `b : X' ⟶ X` of `S`-schemes, if the canonical map
`Stacks.DeRham.formsDerivedDirectImage` of `D(𝒪_X)` has a retraction, then
`b^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S})` is injective for every `q`. -/
theorem injective_hodgePullback_of_retraction (f : X ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S)
    (w : b ≫ f = f' ≫ 𝟙 S) (p : ℕ)
    (h : ∃ r, Stacks.DeRham.formsDerivedDirectImage f b (p : ℤ) ≫ r = 𝟙 _) (q : ℤ) :
    Function.Injective (hodgePullback b f' f (𝟙 S) w p q) := by
  obtain rfl : f' = b ≫ f := ((Category.comp_id f').symm.trans w.symm)
  exact injective_cohomologyPullback_of_retraction _ _ q
    (exists_retraction_hodgeComparison f b p w h)

/-- **Hodge cohomology injects into that of the blowing up of a smooth centre**
(Stacks, Proposition 0FUW read on `H^q(X, -)`, for Hodge cohomology). Let `f : X ⟶ S` be smooth,
let `I` cut out a closed subscheme `Z` of `X` which is smooth over `S` and has empty interior in
`X`, and let `b : X' ⟶ X` be the blowing up of `X` along `Z`. Then
`b^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S})` is injective for all `p` and `q`: by
[Stacks, Tag 0G5J] the canonical map `Ω^p_{X/S} ⟶ Rb_*Ω^p_{X'/S}` has a left inverse in
`D(𝒪_X)`. -/
theorem injective_hodgePullback_blowUpToBase_ker (f : X ⟶ S) [Smooth f] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅)
    (f' : blowUp i.ker ⟶ S) (w : blowUpToBase i.ker ≫ f = f' ≫ 𝟙 S) (p : ℕ) (q : ℤ) :
    Function.Injective (hodgePullback (blowUpToBase i.ker) f' f (𝟙 S) w p q) := by
  obtain ⟨r, hr, -⟩ := Stacks.DeRham.existsUnique_blowUpFormsRetraction_blowUpToBase f i hint p
  exact injective_hodgePullback_of_retraction f (blowUpToBase i.ker) f' w p ⟨r, hr⟩ q

/-- **Hodge cohomology injects into that of the blowing up of a smooth centre**, for the centre
the closed subscheme of a quasi-coherent ideal `I`: `injective_hodgePullback_blowUpToBase_ker`
for its closed immersion `I.subschemeι`, whose ideal is `I`. -/
theorem injective_hodgePullback_blowUpToBase (f : X ⟶ S) [Smooth f] (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] (hint : interior (Set.range I.subschemeι.base) = ∅)
    (f' : blowUp I ⟶ S) (w : blowUpToBase I ≫ f = f' ≫ 𝟙 S) (p : ℕ) (q : ℤ) :
    Function.Injective (hodgePullback (blowUpToBase I) f' f (𝟙 S) w p q) := by
  have key : ∀ (J : X.IdealSheafData), I.subschemeι.ker = J → ∀ (f' : blowUp J ⟶ S)
      (w : blowUpToBase J ≫ f = f' ≫ 𝟙 S),
      Function.Injective (hodgePullback (blowUpToBase J) f' f (𝟙 S) w p q) := by
    rintro J rfl f' w
    exact injective_hodgePullback_blowUpToBase_ker f I.subschemeι hint f' w p q
  exact key I (Scheme.IdealSheafData.ker_subschemeι I) f' w

/-- **Hodge cohomology injects into that of a blowing up of a smooth centre**, for a morphism
`b : X' ⟶ X` of `S`-schemes identified with `AlgebraicGeometry.blowUpToBase i.ker` by an
isomorphism `X' ≅ AlgebraicGeometry.blowUp i.ker`, under the hypotheses of
`injective_hodgePullback_blowUpToBase_ker`. -/
theorem injective_hodgePullback_of_isBlowUp_ker (f : X ⟶ S) [Smooth f] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅)
    (b : X' ⟶ X) (f' : X' ⟶ S) (w : b ≫ f = f' ≫ 𝟙 S) (e : X' ≅ blowUp i.ker)
    (he : e.hom ≫ blowUpToBase i.ker = b) (p : ℕ) (q : ℤ) :
    Function.Injective (hodgePullback b f' f (𝟙 S) w p q) := by
  subst he
  have w₁ : blowUpToBase i.ker ≫ f = (blowUpToBase i.ker ≫ f) ≫ 𝟙 S := (Category.comp_id _).symm
  have w₂ : e.hom ≫ blowUpToBase i.ker ≫ f = f' ≫ 𝟙 S := by
    rw [← Category.assoc]
    exact w
  intro x y hxy
  rw [hodgePullback_comp_overBase (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) f' e.hom w₁ w₂
      w p q x,
    hodgePullback_comp_overBase (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) f' e.hom w₁ w₂
      w p q y] at hxy
  exact injective_hodgePullback_blowUpToBase_ker f i hint _ w₁ p q
    ((bijective_hodgePullback_of_isIso e.hom (blowUpToBase i.ker ≫ f) f' w₂ p q).1 hxy)

/-- **Hodge cohomology injects into that of a blowing up of a smooth centre**, for a morphism
`b : X' ⟶ X` of `S`-schemes identified with `AlgebraicGeometry.blowUpToBase I` by an isomorphism
`X' ≅ AlgebraicGeometry.blowUp I`, under the hypotheses of
`injective_hodgePullback_blowUpToBase`. -/
theorem injective_hodgePullback_of_isBlowUp (f : X ⟶ S) [Smooth f] (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] (hint : interior (Set.range I.subschemeι.base) = ∅)
    (b : X' ⟶ X) (f' : X' ⟶ S) (w : b ≫ f = f' ≫ 𝟙 S) (e : X' ≅ blowUp I)
    (he : e.hom ≫ blowUpToBase I = b) (p : ℕ) (q : ℤ) :
    Function.Injective (hodgePullback b f' f (𝟙 S) w p q) := by
  have key : ∀ (J : X.IdealSheafData), I.subschemeι.ker = J → ∀ (e : X' ≅ blowUp J),
      e.hom ≫ blowUpToBase J = b → Function.Injective (hodgePullback b f' f (𝟙 S) w p q) := by
    rintro J rfl e he
    exact injective_hodgePullback_of_isBlowUp_ker f I.subschemeι hint b f' w e he p q
  exact key I (Scheme.IdealSheafData.ker_subschemeι I) e he

/-- The pullback on `H^n_{Hodge}` is injective as soon as the pullbacks on the groups
`H^q(X, Ω^p_{X/S})` are. -/
theorem injective_hodgePiecePullback {S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
    (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g)
    (h : ∀ (p : ℕ) (q : ℤ), Function.Injective (hodgePullback g' f' f g w p q)) (n : ℤ) :
    Function.Injective (hodgePiecePullback g' f' f g w n) :=
  (DirectSum.map_injective _).2 fun i => h i.1.1 (i.1.2 : ℤ)

/-- **The pullback on `H^*_{Hodge}` is injective as soon as the pullbacks on the groups
`H^q(X, Ω^p_{X/S})` are**: it is the direct sum of the pullbacks on the pieces
`H^n_{Hodge}`. -/
theorem injective_hodgeAlgebraPullback {S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g)
    (h : ∀ (p : ℕ) (q : ℤ), Function.Injective (hodgePullback g' f' f g w p q)) :
    Function.Injective (hodgeAlgebraPullback g' f' f g w) := by
  have key : ∀ a, hodgeAlgebraPullback g' f' f g w a =
      DirectSum.map (fun n => hodgePiecePullback g' f' f g w n) a := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add a a' ha ha' => simp only [map_add, ha, ha']
    | of n x => rw [hodgeAlgebraPullback_of, DirectSum.map_of]
  intro a a' haa
  rw [key, key] at haa
  exact (DirectSum.map_injective _).2 (injective_hodgePiecePullback g' f' f g w h) haa

end Injective

/-! ### The axiom (A7) for Hodge cohomology -/

section Field

variable {k : Type u} [Field k]

/-- **The axiom (A7) for the groups of Hodge cohomology** (Remark 0FWE): let `i : Z ⟶ X` be a
closed immersion of smooth projective schemes over a field `k` with `Z` nowhere dense in `X`, and
`b : X' ⟶ X` the blowing up `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupHom i` of `X` in
`Z`. Then `b^* : H^q(X, Ω^p_{X/k}) ⟶ H^q(X', Ω^p_{X'/k})` is injective for all `p` and `q`. -/
theorem injective_hodgePullback_blowupHom {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X) [IsClosedImmersion i.hom.left] (hZ : IsNowhereDense (Set.range i.hom.left.base))
    (p : ℕ) (q : ℤ) :
    Function.Injective (hodgePullback (blowupHom i).hom.left (blowupObj i).obj.hom X.obj.hom
      (𝟙 _) (hodgeSquare_w (blowupHom i)) p q) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hint : interior (Set.range i.hom.left.base) = ∅ :=
    i.hom.left.isClosedEmbedding.isClosed_range.isNowhereDense_iff.1 hZ
  refine injective_hodgePullback_of_isBlowUp_ker X.obj.hom i.hom.left hint
    (blowupHom i).hom.left (blowupObj i).obj.hom (hodgeSquare_w (blowupHom i))
    (AlgebraicGeometry.blowUpIso i.hom.left.ker).symm ?_ p q
  rw [Iso.symm_hom, ← AlgebraicGeometry.blowUpIso_hom_blowUpToBase]
  exact Iso.inv_hom_id_assoc _ _

/-- **The axiom (A7) for Hodge cohomology** (Remark 0FWE), on `H^*_{Hodge}`: under the hypotheses
of `injective_hodgePullback_blowupHom`, the pullback `b^* : H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X'/k)`
of the data `hodgeFirstChernClassData k` along the blowing up `b` is injective. -/
theorem injective_pull_hodgeFirstChernClassData_blowupHom
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) :
    Function.Injective ((hodgeFirstChernClassData k).pull (blowupHom i)) :=
  injective_hodgeAlgebraPullback (blowupHom i).hom.left (blowupObj i).obj.hom X.obj.hom (𝟙 _)
    (hodgeSquare_w (blowupHom i)) (injective_hodgePullback_blowupHom i hZ)

/-- **The axiom (A7) for the groups of Hodge cohomology** (Remark 0FWE): let `b : X' ⟶ X` be a
morphism of smooth projective schemes over a field `k` which is the blowing up of `X` along a
closed subscheme `Z`, cut out by `I`, smooth over `k` and with empty interior in `X`. Then
`b^* : H^q(X, Ω^p_{X/k}) ⟶ H^q(X', Ω^p_{X'/k})` is injective for all `p` and `q`. -/
theorem injective_hodgePullback_blowUp {X X' : (SmoothProjectiveScheme k).FullSubcategory}
    (b : X' ⟶ X) (I : ((toScheme k).obj X).IdealSheafData) (hZ : Smooth (I.subschemeι ≫ X.obj.hom))
    (hint : interior (Set.range I.subschemeι.base) = ∅)
    (he : ∃ e : (toScheme k).obj X' ≅ AlgebraicGeometry.blowUp I,
      e.hom ≫ AlgebraicGeometry.blowUpToBase I = (toScheme k).map b) (p : ℕ) (q : ℤ) :
    Function.Injective
      (hodgePullback b.hom.left X'.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w b) p q) := by
  obtain ⟨e, he⟩ := he
  exact injective_hodgePullback_of_isBlowUp X.obj.hom I hint b.hom.left X'.obj.hom
    (hodgeSquare_w b) e he p q

/-- **The axiom (A7) for Hodge cohomology** (Remark 0FWE), on `H^*_{Hodge}`: under the hypotheses
of `injective_hodgePullback_blowUp`, the pullback `b^* : H^*_{Hodge}(X/k) ⟶ H^*_{Hodge}(X'/k)` of
the data `hodgeFirstChernClassData k` is injective. -/
theorem injective_pull_hodgeFirstChernClassData_blowUp
    {X X' : (SmoothProjectiveScheme k).FullSubcategory}
    (b : X' ⟶ X) (I : ((toScheme k).obj X).IdealSheafData) (hZ : Smooth (I.subschemeι ≫ X.obj.hom))
    (hint : interior (Set.range I.subschemeι.base) = ∅)
    (he : ∃ e : (toScheme k).obj X' ≅ AlgebraicGeometry.blowUp I,
      e.hom ≫ AlgebraicGeometry.blowUpToBase I = (toScheme k).map b) :
    Function.Injective ((hodgeFirstChernClassData k).pull b) :=
  injective_hodgeAlgebraPullback b.hom.left X'.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w b)
    (injective_hodgePullback_blowUp b I hZ hint he)

variable (k) in
/-- **The axiom (A7) for the data of Hodge cohomology** (Remark 0FWE), in the shape
`Stacks.WeilCohomology.FirstChernClassData.BlowupAxiom`: the pullback along the blowing up of a
smooth projective scheme over `k` in a nowhere dense smooth centre, a closed immersion of smooth
projective schemes, is injective. -/
theorem hodge_blowupAxiom : (hodgeFirstChernClassData k).BlowupAxiom :=
  fun _ _ i _ hZ => injective_pull_hodgeFirstChernClassData_blowupHom i hZ

end Field

end Stacks.HodgeWeil

end
