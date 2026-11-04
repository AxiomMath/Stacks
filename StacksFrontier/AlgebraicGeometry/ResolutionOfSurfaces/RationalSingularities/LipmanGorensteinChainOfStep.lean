module

public import StacksFrontier.RingTheory.Dualizing.GorensteinOfDualizingQuotient
public import StacksFrontier.RingTheory.Dualizing.CanonicalIdealExtension
public import StacksFrontier.RingTheory.Dualizing.QuotientExtConcentration
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.DominatingStageLocalRings
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartCaseTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedPointBlowupRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensionsRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.NormalSurfaceAssembly
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingDefinesRational
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings

/-!
# The Gorenstein chain of [Stacks, Tag 0BBV], from a per-blowup step

Let `A` be a two-dimensional normal Nagata local domain defining a rational singularity and
having a dualizing complex. [Stacks, Tag 0BBV] produces a finite sequence of normalized blowups
of `Spec A` at points over the closed point whose local rings are all Gorenstein. This file
carries out the chain induction and the assembly of the source's proof from a per-blowup local
step (`AlgebraicGeometry.LipmanGorensteinChain.DualizingLocalStep`): the extension of a
dualizing ideal of such a ring to every local ring of its normalized blowup at the closed point
is a dualizing module.

1. `A` is Cohen–Macaulay (Serre's criterion in dimension two), so a dualizing complex is a
   module `ω_A` in a single degree ([Stacks, Tag 0AWS]), and `ω_A ≅ I` for a nonzero ideal `I`
   (a dualizing module of a domain is torsion free of rank one).
2. A normal modification of `Spec A` on which `I` becomes principal (the normalized blowup in
   `I`) is dominated by a chain of normalized blowups at points over the closed point
   ([Stacks, Tag 0BBT]).
3. Along the chain, the extension of `I` to every local ring is a dualizing module: on `Spec A`
   it is a localization ([Stacks, Tag 0A7G]); off a blown-up point the normalized blowup is an
   isomorphism; over a blown-up point `w` the normalized blowup is the base change of the
   normalized blowup of `Spec 𝒪_{W, w}` along the flat preimmersion `Spec 𝒪_{W, w} ⟶ W`, which
   is an isomorphism on local rings, and the local step applies to `𝒪_{W, w}` (normal, Nagata, of
   dimension two, rational by [Stacks, Tag 0BG0]).
4. On the last stage the extension of `I` is principal, hence free of rank one, so the local
   rings are Gorenstein.

## Main results

* `AlgebraicGeometry.exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk_of_step`:
  the conclusion of [Stacks, Tag 0BBV], in the form of the `hgorenstein` binder of
  `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_stalk_of_dominates_isResolution`, from the
  local step.
* `AlgebraicGeometry.LipmanGorensteinChain.isDualizingIdealOn_of_chain`: step 3.
* `AlgebraicGeometry.LipmanGorensteinChain.exists_ideal_isDualizingRingModule`: step 1.
* `LipmanGorensteinChain.exists_isModification_map_eq_span_singleton_stalkHomOfSpec`: the
  modification of step 2 (`exists_isModification_map_eq_span_singleton`, read through
  `AlgebraicGeometry.stalkHomOfSpec`).

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

namespace LipmanGorensteinChain

/-! ### Dualizing modules along localizations and isomorphisms -/

section RingLevel

/-- A dualizing module placed in some degree gives a dualizing complex in degree zero. -/
theorem isDualizingComplex_single_zero_of_isDualizingRingModule {A : Type u} [CommRing A]
    [IsNoetherianRing A] {M : Type u} [AddCommGroup M] [Module A M]
    (hM : Stacks.Duality.IsDualizingRingModule A M) :
    Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) := by
  obtain ⟨-, n, hn⟩ := hM
  exact (Dualizing.isDualizingComplex_iff_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n 0 n (add_zero n)).app
      (ModuleCat.of A M))).mp (Dualizing.isDualizingComplex_shift _ hn n)

/-- The extension of a dualizing ideal to a localization is a dualizing ideal of the
localization ([Stacks, Tag 0A7G]). -/
theorem isDualizingRingModule_map_of_isLocalization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] (S : Submonoid A) [IsLocalization S B] (J : Ideal A)
    (hJ : Stacks.Duality.IsDualizingRingModule A J) :
    letI : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
    Stacks.Duality.IsDualizingRingModule B (J.map (algebraMap A B)) := by
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  have h0 := isDualizingComplex_single_zero_of_isDualizingRingModule hJ
  have hflat : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive :=
    extendScalars_additive.{u, u} _
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  let : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hext := Dualizing.isDualizingComplex_extendScalars_of_isLocalization (B := B) S _ h0
  have h1 := (Dualizing.isDualizingComplex_iff_of_iso
    (Stacks.Duality.mapDerivedCategorySingleZeroIso _ (ModuleCat.of A J))).mp hext
  let g : J →ₗ[A] ↥(J.localized' B S (Algebra.linearMap A B)) :=
    J.toLocalized' B S (Algebra.linearMap A B)
  have hb : IsBaseChange B g := IsLocalizedModule.isBaseChange S B g
  let e : B ⊗[A] J ≃ₗ[B] (J.map (algebraMap A B) : Ideal B) :=
    hb.equiv.trans (LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map B S J))
  let e' : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A J) ≅
      ModuleCat.of B (J.map (algebraMap A B) : Ideal B) :=
    ((StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
      (ModuleCat.of A J)).trans e).toModuleIso
  exact ⟨inferInstance, 0, (Dualizing.isDualizingComplex_iff_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso e')).mp h1⟩

/-- The extension of a dualizing ideal along a ring isomorphism is a dualizing ideal. -/
theorem isDualizingRingModule_map_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) (hφ : Function.Bijective φ)
    (J : Ideal A) (hJ : Stacks.Duality.IsDualizingRingModule A J) :
    Stacks.Duality.IsDualizingRingModule B (J.map φ) := by
  let : Algebra A B := φ.toAlgebra
  have : IsLocalization (Submonoid.powers (1 : A)) B :=
    IsLocalization.away_of_isUnit_of_bijective B isUnit_one hφ
  exact isDualizingRingModule_map_of_isLocalization (Submonoid.powers (1 : A)) J hJ

/-- A normal Noetherian local domain of dimension two with a dualizing complex has a nonzero
ideal which is a dualizing module. -/
theorem exists_ideal_isDualizingRingModule (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    (hK : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    ∃ I : Ideal A, I ≠ ⊥ ∧ Stacks.Duality.IsDualizingRingModule A I := by
  obtain ⟨K, hK⟩ := hK
  have hCM : Module.IsMaximalCohenMacaulay A A := by
    have h2 := Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed A (hdim ▸ le_rfl)
    have hle : (Module.depth A (maximalIdeal A) A : WithBot ℕ∞) ≤ ringKrullDim A := by
      calc _ ≤ Module.supportDim A A :=
            Module.depth_le_supportDim A _ A
              (by simpa using (maximalIdeal.isMaximal A).ne_top)
        _ = ringKrullDim A := Module.supportDim_self_eq_ringKrullDim A
    exact le_antisymm hle (hdim ▸ WithBot.coe_le_coe.mpr h2)
  obtain ⟨d, hd⟩ := Dualizing.exists_homology_concentrated_of_isMaximalCohenMacaulay_self.{u, u}
    K hK hCM
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K d hd
  let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj K
  have hω : Stacks.Duality.IsDualizingRingModule A ω :=
    ⟨hK.finiteCohomology d, d, (Dualizing.isDualizingComplex_iff_of_iso e).mp hK⟩
  obtain ⟨I, hI, ⟨eI⟩⟩ := Dualizing.exists_linearEquiv_ideal_of_isDualizingRingModule hω
  exact ⟨I, hI, Stacks.Duality.isDualizingRingModule_of_linearEquiv hω eI⟩

/-- A Noetherian local domain one of whose principal ideals is a dualizing module is
Gorenstein. -/
theorem isGorensteinLocalRing_of_isDualizingRingModule_span_singleton {B : Type u}
    [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B] (d : B)
    (hd : Stacks.Duality.IsDualizingRingModule B (Ideal.span {d} : Ideal B)) :
    Dualizing.IsGorensteinLocalRing B := by
  have hnt := Stacks.Duality.IsDualizingRingModule.nontrivial
    (M := ModuleCat.of B (Ideal.span {d} : Ideal B)) hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := hnt
    apply hxy
    have h0 : ∀ z : (Ideal.span {(0 : B)} : Ideal B), (z : B) = 0 := fun z =>
      (Submodule.mem_bot B).mp
        ((Ideal.span_singleton_eq_bot (x := (0 : B))).mpr rfl ▸ z.2)
    exact Subtype.ext ((h0 x).trans (h0 y).symm)
  exact Dualizing.isGorensteinLocalRing_of_linearEquiv hd
    (LinearEquiv.toSpanNonzeroSingleton B B d hd0).symm

end RingLevel

/-! ### The map from the base ring to the local rings -/

section StalkHom

/-- `AlgebraicGeometry.stalkHomOfSpec` is compatible with composition. -/
theorem stalkHomOfSpec_comp {A : Type u} [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (f : Y ⟶ Spec (.of A)) (x : X) :
    stalkHomOfSpec (g ≫ f) x = (g.stalkMap x).hom.comp (stalkHomOfSpec f (g x)) := by
  ext b
  simp only [stalkHomOfSpec, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Category.assoc]
  exact (Scheme.Hom.germ_stalkMap_apply g ⊤ x trivial _).symm

/-- `AlgebraicGeometry.stalkHomOfSpec` along `Spec` of a ring map is the composite. -/
theorem stalkHomOfSpec_comp_specMap {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of B)) (φ : A →+* B) (x : X) :
    stalkHomOfSpec (p ≫ Spec.map (CommRingCat.ofHom φ)) x = (stalkHomOfSpec p x).comp φ := by
  ext b
  have h := congrArg (fun k => k.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [stalkHomOfSpec, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← h]

/-- The morphism `Spec 𝒪_{X, x} ⟶ X ⟶ Spec A` is `Spec` of the map from `A` to the local ring. -/
theorem fromSpecStalk_comp_eq_specMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) :
    X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (stalkHomOfSpec f x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq]
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1
  ext b
  exact (stalkHomOfSpec_apply f x b).symm

/-- If the extension of `J` at `g x` is principal, so is its extension at `x`, along `g ≫ f`. -/
private theorem map_stalkHomOfSpec_comp_eq_span {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    {g : X ⟶ Y} {f : Y ⟶ Spec (.of A)} {x : X} {J : Ideal A} {d : Y.presheaf.stalk (g x)}
    (h : J.map (stalkHomOfSpec f (g x)) = Ideal.span {d}) :
    J.map (stalkHomOfSpec (g ≫ f) x) = Ideal.span {(g.stalkMap x).hom d} := by
  rw [stalkHomOfSpec_comp, ← Ideal.map_map, h, Ideal.map_span, Set.image_singleton]

end StalkHom

/-! ### The dualizing ideal along the chain -/

section Chain

/-- Along an isomorphism of local rings, the extension of an ideal is dualizing exactly when it is
after the isomorphism. -/
theorem isDualizingRingModule_map_comp_of_isIso {A : Type u} [CommRing A] {R S : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing S] (φ : R ⟶ S) [IsIso φ] (s : A →+* R) (I : Ideal A)
    (h : Stacks.Duality.IsDualizingRingModule S (I.map (φ.hom.comp s))) :
    Stacks.Duality.IsDualizingRingModule R (I.map s) := by
  have hφ := ConcreteCategory.bijective_of_isIso (inv φ)
  have heq : I.map s = (I.map (φ.hom.comp s)).map (inv φ).hom := by
    rw [Ideal.map_map, ← RingHom.comp_assoc, ← CommRingCat.hom_comp, IsIso.hom_inv_id,
      CommRingCat.hom_id, RingHom.id_comp]
  rw [heq]
  exact isDualizingRingModule_map_of_bijective _ hφ _ h

/-- The forward direction of `isDualizingRingModule_map_comp_of_isIso`. -/
theorem isDualizingRingModule_map_comp_of_isIso' {A : Type u} [CommRing A]
    {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S] (φ : R ⟶ S) [IsIso φ]
    (s : A →+* R) (I : Ideal A) (h : Stacks.Duality.IsDualizingRingModule R (I.map s)) :
    Stacks.Duality.IsDualizingRingModule S (I.map (φ.hom.comp s)) := by
  rw [← Ideal.map_map]
  exact isDualizingRingModule_map_of_bijective _ (ConcreteCategory.bijective_of_isIso φ) _ h

variable {A : Type u} [CommRing A]

/-- At every point of the scheme `Y` over `Spec A`, the local ring is Noetherian and the
extension of `I` to it is a dualizing module. -/
def IsDualizingIdealOn (I : Ideal A) {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) : Prop :=
  ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
    Stacks.Duality.IsDualizingRingModule (Y.presheaf.stalk y) (I.map (stalkHomOfSpec f y))

/-- On `Spec A` itself the extension of a dualizing ideal to every local ring is dualizing. -/
theorem isDualizingIdealOn_id [IsNoetherianRing A] (I : Ideal A)
    (hI : Stacks.Duality.IsDualizingRingModule A I) :
    IsDualizingIdealOn I (𝟙 (Spec (.of A))) := by
  intro p
  have : p.asIdeal.IsPrime := p.isPrime
  have hloc := isDualizingRingModule_map_of_isLocalization (B := Localization.AtPrime p.asIdeal)
    p.asIdeal.primeCompl I hI
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have : IsNoetherianRing ((Spec (.of A)).presheaf.stalk p) :=
    isNoetherianRing_of_ringEquiv _ (Spec.stalkIso (.of A) p).symm.commRingCatIsoToRingEquiv
  refine ⟨inferInstance, ?_⟩
  have heq : stalkHomOfSpec (𝟙 (Spec (.of A))) p =
      (Spec.stalkIso (.of A) p).inv.hom.comp (algebraMap A (Localization.AtPrime p.asIdeal)) := by
    have h := congrArg CommRingCat.Hom.hom (Spec.algebraMap_stalkIso_inv (R := .of A) p)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
    rw [h]
    simp [stalkHomOfSpec]
  rw [heq]
  exact isDualizingRingModule_map_comp_of_isIso' (R := .of (Localization.AtPrime p.asIdeal))
    (Spec.stalkIso (.of A) p).inv _ I hloc

/-- For every two-dimensional normal Nagata local domain `B` defining a rational singularity,
the extension of a dualizing ideal of `B` to every local ring of the normalized blowup of
`Spec B` at its closed point is dualizing. -/
def DualizingLocalStep : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B] (hN : IsNagataRing B),
    ringKrullDim B = 2 → DefinesRationalSingularity B → ∀ (J : Ideal B),
    (letI := hN.1; Stacks.Duality.IsDualizingRingModule B J) →
    ∀ (hW : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
        (irreducibleComponents U).Finite)
      (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))))
      (x : Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc),
      ∃ _ : IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
          (IsLocalRing.closedPoint B) hc).presheaf.stalk x),
        Stacks.Duality.IsDualizingRingModule ((Stacks.Blowup.normalizedBlowUpScheme
            (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc).presheaf.stalk x)
          (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫
          (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hW (IsLocalRing.closedPoint B)
            hc).appTop ≫
          (Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B)
            hc).presheaf.germ ⊤ x trivial).hom)

/-- Given `DualizingLocalStep`, `IsDualizingIdealOn I` passes from a stage `W` of a chain of
normalized point blowups over the closed point of `Spec A` to the normalized blowup of `W` at a
closed point lying over the closed point of `Spec A`. -/
theorem isDualizingIdealOn_step [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hstep : DualizingLocalStep.{u}) (I : Ideal A) {W : Scheme.{u}} {h : W ⟶ Spec (.of A)}
    (hh : Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
      {IsLocalRing.closedPoint A} W h)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ ({IsLocalRing.closedPoint A} : Set _))
    (ih : IsDualizingIdealOn I h) :
    IsDualizingIdealOn I (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ h) := by
  have : IsNoetherianRing A := hN.1
  obtain ⟨hmod, hWn, hWnoeth, hWdim⟩ := isModification_of_normalizedBlowUpSeq A hN hdim
    (normalizedBlowUpSeq_of_normalizedPointBlowupChain (hh.mono (Set.subset_univ _)))
  obtain ⟨hmod', hWn', hWnoeth', -⟩ := isModification_of_normalizedBlowUpSeq A hN hdim
    (normalizedBlowUpSeq_of_normalizedPointBlowupChain ((hh.step hW w hw hwT).mono
      (Set.subset_univ _)))
  have := hWn
  have := hWnoeth
  have := hWnoeth'
  set ν := Stacks.Blowup.normalizedBlowUp W hW w hw with hν
  have : IsLocallyNoetherian (Stacks.Blowup.normalizedBlowUpScheme W hW w hw) :=
    IsNoetherian.toIsLocallyNoetherian
  intro x'
  have hN' :
      IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme W hW w hw).presheaf.stalk x') :=
    inferInstance
  by_cases hx : ν.base x' = w
  · have : IsIntegral W := hmod.source_isIntegral
    have : IsProper h := hmod.isProper
    have : IsLocallyNoetherian W := IsNoetherian.toIsLocallyNoetherian
    let B : Type u := W.presheaf.stalk w
    have : IsNormalDomain B := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
    have hNagB : IsNagataRing B :=
      isNagataRing_stalk_of_isNagataScheme (isNagataScheme_of_isNagataRing h hN) w
    have hdimB : ringKrullDim B = 2 :=
      ringKrullDim_stalk_eq_two_of_isModification A hdim h hmod w hw
    have hxη : letI := hmod.source_isIntegral; w ≠ genericPoint W := by
      intro hxg
      obtain ⟨z, hz⟩ := exists_ne_of_topologicalKrullDim_eq_two hWdim w
      have hzc : z ∈ closure ({w} : Set W) := by
        rw [hxg, (genericPoint_spec W).def]
        exact Set.mem_univ z
      rw [hw.closure_eq] at hzc
      exact hz hzc
    have hratB : DefinesRationalSingularity B :=
      definesRationalSingularity_stalk_of_isModification A hdim hrat h hmod w hw hxη
    obtain ⟨hNw, hJ⟩ := ih w
    have : IsNoetherian (Spec (.of B)) := inferInstance
    have hWB : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
        (irreducibleComponents U).Finite :=
      Stacks.ResolutionOfSurfaces.finite_irreducibleComponents_isCompactOpen_of_isNoetherian
    have hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))) :=
      IsLocalRing.isClosed_singleton_closedPoint B
    have hloc := hstep B hNagB hdimB hratB (I.map (stalkHomOfSpec h w)) hJ hWB hc
    have hideal : (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds W)).comap (W.fromSpecStalk w) =
        Scheme.IdealSheafData.vanishingIdeal
          (⟨{IsLocalRing.closedPoint B}, hc⟩ : TopologicalSpace.Closeds (Spec (.of B))) := by
      rw [comap_fromSpecStalk_vanishingIdeal_singleton W w hw,
        vanishingIdeal_closedPoint_eq_maximalIdealSheaf B hc]
    have : Flat (W.fromSpecStalk w) := flat_fromSpecStalk W w
    obtain ⟨m, hm⟩ := exists_isPullback_normalizedBlowUp_comap (W.fromSpecStalk w) hW hWB w hw
      (IsLocalRing.closedPoint B) hc hideal
    have : Flat m := MorphismProperty.IsStableUnderBaseChange.of_isPullback hm.flip inferInstance
    have : IsPreimmersion m :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hm.flip inferInstance
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ν)
      (g := W.fromSpecStalk w) x' (IsLocalRing.closedPoint B)
      (by rw [hx, Scheme.fromSpecStalk_closedPoint])
    set x'' := hm.isoPullback.inv t with hx''
    have hmx : m.base x'' = x' := by
      change (hm.isoPullback.inv ≫ m).base t = x'
      rw [hm.isoPullback_inv_fst]
      exact ht1
    subst hmx
    have : IsIso (m.stalkMap x'') := isIso_stalkMap_of_flat_isPreimmersion m x''
    obtain ⟨hN'', hd''⟩ := hloc x''
    have hσ : (stalkHomOfSpec (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hWB
        (IsLocalRing.closedPoint B) hc) x'').comp (stalkHomOfSpec h w) =
        (m.stalkMap x'').hom.comp (stalkHomOfSpec (ν ≫ h) (m.base x'')) := by
      rw [← stalkHomOfSpec_comp_specMap, ← fromSpecStalk_comp_eq_specMap, ← stalkHomOfSpec_comp]
      congr 1
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) hm.w).symm.trans
        (Category.assoc _ _ _))
    refine ⟨hN', isDualizingRingModule_map_comp_of_isIso (m.stalkMap x'') _ I ?_⟩
    rw [← hσ, ← Ideal.map_map]
    exact hd''
  · have hiso := isIso_normalizedBlowUp_restrict_compl_singleton hW w hw
    have : IsIso (ν.stalkMap x') :=
      isIso_stalkMap_of_isIso_morphismRestrict ν hiso (U := ⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩)
        (show ν.base x' ∈ ({w} : Set W)ᶜ from hx)
    obtain ⟨hN0, hd⟩ := ih (ν.base x')
    refine ⟨hN', ?_⟩
    rw [stalkHomOfSpec_comp ν h x']
    exact isDualizingRingModule_map_comp_of_isIso' (ν.stalkMap x') _ I hd

/-- Given `DualizingLocalStep`, the extension of a dualizing ideal of `A` is dualizing at every
point of every chain of normalized blowups of `Spec A` at points over the closed point. -/
theorem isDualizingIdealOn_of_chain [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hstep : DualizingLocalStep.{u}) (I : Ideal A)
    (hI : letI := hN.1; Stacks.Duality.IsDualizingRingModule A I) {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of A)}
    (hc : Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
      {IsLocalRing.closedPoint A} Y f) :
    IsDualizingIdealOn I f := by
  have : IsNoetherianRing A := hN.1
  induction hc with
  | refl => exact isDualizingIdealOn_id I hI
  | step hh hW w hw hwT ih => exact isDualizingIdealOn_step hN hdim hrat hstep I hh hW w hw hwT ih

/-- A nonzero ideal of a Nagata domain `A` becomes principal at every point of some normal
modification of `Spec A`. -/
theorem exists_isModification_map_eq_span_singleton_stalkHomOfSpec (A : Type u) [CommRing A]
    [IsDomain A] [IsNagataRing A] (J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsNormal X ∧ IsModification f ∧
      ∀ x : X, ∃ d, J.map (stalkHomOfSpec f x) = Ideal.span {d} := by
  let e := Scheme.ΓSpecIso (CommRingCat.of A)
  let I : (Spec (.of A)).IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (Ideal.map e.inv.hom J)
  have hItop : I.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.map e.inv.hom J :=
    Stacks.Blowup.ideal_ofIdealTop_top _
  have hI : I ≠ ⊥ := by
    intro h
    apply hJ
    have h0 : Ideal.map e.inv.hom J = ⊥ := by rw [← hItop, h]; rfl
    exact (Ideal.map_eq_bot_iff_of_injective (ConcreteCategory.bijective_of_isIso e.inv).1).mp h0
  have hNagata : IsNagataScheme (Spec (.of A)) :=
    isNagataScheme_spec_of_isNagataRing _ inferInstance
  let hS := Stacks.ResolutionOfSurfaces.finite_irreducibleComponents_isCompactOpen_of_isNoetherian
    (X := Spec (.of A))
  let hX := Stacks.Blowup.finite_irreducibleComponents_blowUp I hS
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  have hNagataX : IsNagataScheme (blowUp I) :=
    isNagataScheme_of_locallyOfFiniteType (blowUpToBase I) hNagata
  have : IsFinite (Scheme.normalization (blowUp I) hX) :=
    Scheme.isFinite_normalization hNagataX hX
  let ν := Scheme.normalization (blowUp I) hX
  refine ⟨_, ν ≫ blowUpToBase I, Scheme.isNormal_normalizationScheme _ hX,
    ⟨(Scheme.isBirational_normalization _ hX).comp (isBirational_blowUpToBase I hI),
      inferInstance, inferInstance⟩, fun x => ?_⟩
  obtain ⟨d, -, hd⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
    (exceptionalIdeal I) inferInstance (ν x)
  refine ⟨(ν.stalkMap x).hom d, ?_⟩
  have hstalk : IdealSheafData.stalk I (blowUpToBase I (ν x)) =
      J.map (((Spec (.of A)).presheaf.germ ⊤ (blowUpToBase I (ν x)) trivial).hom.comp
        e.inv.hom) := by
    rw [IdealSheafData.stalk_eq_map_germ I _ ⟨⊤, isAffineOpen_top _⟩ trivial, hItop,
      Ideal.map_map]
  have hexc : IdealSheafData.stalk (exceptionalIdeal I) (ν x) =
      (IdealSheafData.stalk I (blowUpToBase I (ν x))).map
        ((blowUpToBase I).stalkMap (ν x)).hom :=
    stalk_comap I (blowUpToBase I) (ν x)
  have key : J.map (stalkHomOfSpec (blowUpToBase I) (ν x)) = Ideal.span {d} := by
    rw [← hd, hexc, hstalk, Ideal.map_map]
    congr 1
    ext b
    exact stalkHomOfSpec_apply _ _ b
  exact map_stalkHomOfSpec_comp_eq_span key

end Chain

end LipmanGorensteinChain

open LipmanGorensteinChain in
/-- **[Stacks, Tag 0BBV], from the per-blowup local step.** Let `A` be a two-dimensional normal
Nagata local domain defining a rational singularity and having a dualizing complex. Then there is
a finite chain of normalized blowups of `Spec A` at points over the closed point all of whose
local rings are Gorenstein, provided the local step `hstep` holds: the extension of a dualizing
ideal of a two-dimensional normal Nagata local domain defining a rational singularity to every
local ring of its normalized blowup at the closed point is dualizing. -/
theorem exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk_of_step
    (hstep : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B] (hN : IsNagataRing B),
      ringKrullDim B = 2 → DefinesRationalSingularity B → ∀ (J : Ideal B),
      (letI := hN.1; Stacks.Duality.IsDualizingRingModule B J) →
      ∀ (hW : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
          (irreducibleComponents U).Finite)
        (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))))
        (x : Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B)
          hc),
        ∃ _ : IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
            (IsLocalRing.closedPoint B) hc).presheaf.stalk x),
          Stacks.Duality.IsDualizingRingModule ((Stacks.Blowup.normalizedBlowUpScheme
              (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc).presheaf.stalk x)
            (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫
            (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hW (IsLocalRing.closedPoint B)
              hc).appTop ≫
            (Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B)
              hc).presheaf.germ ⊤ x trivial).hom)) :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y) := by
  intro A _ _ _ hN hdim hrat hK
  have : IsNoetherianRing A := hN.1
  have : IsNagataRing A := hN
  obtain ⟨I, hI0, hI⟩ := exists_ideal_isDualizingRingModule A hdim hK
  obtain ⟨X, g, -, hgmod, hprinc⟩ :=
    exists_isModification_map_eq_span_singleton_stalkHomOfSpec A I hI0
  obtain ⟨W, gW, dom, hseq, hWn, -, hcomm⟩ :=
    exists_normalizedBlowUpSeq_isModification_dominating A hN hdim g hgmod
  have hchain := normalizedPointBlowupChain_closedPoint_of_normalizedBlowUpSeq A hN hseq
  refine ⟨W, gW, hchain, fun y => ?_⟩
  obtain ⟨hNy, hy⟩ := isDualizingIdealOn_of_chain hN hdim hrat hstep I hI hchain y
  obtain ⟨d, hd⟩ := hprinc (dom.base y)
  have : IsDomain (W.presheaf.stalk y) := hWn.stalk_isDomain y
  rw [← hcomm, map_stalkHomOfSpec_comp_eq_span hd] at hy
  exact ⟨hNy, isGorensteinLocalRing_of_isDualizingRingModule_span_singleton _ hy⟩

end AlgebraicGeometry

end
