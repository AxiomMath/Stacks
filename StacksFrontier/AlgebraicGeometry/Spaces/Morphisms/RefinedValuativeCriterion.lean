module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperTFAE
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Valuation.Constructions

/-!
# A refined valuative criterion for universal closedness and separatedness

Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, with `f` and `h` quasi-compact and the image of `|U|` dense in `|X|`.
Consider the solid diagrams consisting of a valuation ring `A` with fraction field `K`, a
morphism `Spec K ⟶ U`, and a morphism `Spec A ⟶ Y` making the square with `U ⟶ X ⟶ Y` and
`Spec K ⟶ Spec A` commute. If every such diagram admits at most one dotted arrow
`Spec A ⟶ X`, and admits one after replacing `K` by an extension `K'` and `A` by a valuation
ring `A' ⊆ K'` dominating `A`, then `f` is universally closed; if `f` is moreover
quasi-separated, then `f` is separated.

Uniqueness is `Subsingleton` of the type of dotted arrows, and existence is a dominating
extension of the valuative square carrying a dotted arrow.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_of_refinedValuativeCriterion`: under the refined
  valuative criterion, `f` is universally closed.
* `AlgebraicGeometry.Space.isSeparated_of_refinedValuativeCriterion`: if moreover `f` is
  quasi-separated, then `f` is separated.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_lift_to_atlas`: a field-valued point of an
  algebraic space lifts to an étale scheme chart after one extension of its field.

## References

* [Stacks Project, Tag 089B](https://stacks.math.columbia.edu/tag/089B)
* [Stacks Project, Tag 089G](https://stacks.math.columbia.edu/tag/089G)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The inverse image of a base-change-stable morphism property along a functor preserving
pullbacks is base-change stable. -/
private theorem inverseImage_isStableUnderBaseChange_of_preservesCospan
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange] :
    (P.inverseImage F).IsStableUnderBaseChange where
  of_isPullback sq hg := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P) (sq.map F) hg

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

private theorem siteOverHasPullbacks (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance

attribute [local instance] siteOverHasPullbacks

open IsLocalRing in
private theorem exists_prime_over_valuationRing_extension
    {A D : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing D] [IsDomain D] [IsLocalRing D]
    (i : A →+* D) (hi : Function.Injective i) [IsLocalHom i]
    (p : Ideal A) [p.IsPrime] :
    ∃ P : Ideal D, P.IsPrime ∧ P.comap i = p := by
  let : Algebra A D := i.toAlgebra
  have : Module.IsTorsionFree A D :=
    Module.IsTorsionFree.comap i
      (fun r hr => isRegular_iff_ne_zero.mpr (by
        simpa only [map_zero] using hi.ne (isRegular_iff_ne_zero.mp hr)))
      (fun r m => rfl)
  have : Module.Flat A D :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Module.FaithfullyFlat A D := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := D) p
  exact ⟨P, hP, hPp.over.symm⟩

private theorem isLocalHom_of_comp_surjective
    {A D E : Type*} [CommRing A] [CommRing D] [CommRing E]
    (f : A →+* D) (g : D →+* E) (hf : Function.Surjective f)
    [IsLocalHom (g.comp f)] : IsLocalHom g := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := hf x
  exact (isUnit_of_map_unit (g.comp f) a hx).map f

private theorem exists_quotient_extension_of_surjective
    {C W D : Type*} [CommRing C] [IsDomain C] [ValuationRing C]
    [CommRing W] [IsDomain W] [CommRing D] [IsDomain D] [ValuationRing D]
    (c : C →+* W) (hc : Function.Surjective c)
    (i : C →+* D) (hi : Function.Injective i) [IsLocalHom i] :
    ∃ (P : Ideal D) (_ : P.IsPrime) (j : W →+* D ⧸ P),
      Function.Injective j ∧ IsLocalHom j ∧
        j.comp c = (Ideal.Quotient.mk P).comp i ∧ P.comap i = RingHom.ker c := by
  have : (RingHom.ker c).IsPrime := RingHom.ker_isPrime c
  obtain ⟨P, hP, hPc⟩ := exists_prime_over_valuationRing_extension i hi (RingHom.ker c)
  let := hP
  let d := (Ideal.Quotient.mk P).comp i
  have hker : RingHom.ker c = RingHom.ker d := by
    ext x
    change c x = 0 ↔ Ideal.Quotient.mk P (i x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact SetLike.ext_iff.mp hPc.symm x
  let j := c.liftOfSurjective hc ⟨d, hker.le⟩
  have hj : j.comp c = d := RingHom.liftOfSurjective_comp _ _ _
  have hjinj : Function.Injective j := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm _ bot_le
    intro w hw
    obtain ⟨x, rfl⟩ := hc w
    have hx : x ∈ RingHom.ker d := by
      change d x = 0
      rw [← hj]
      exact hw
    exact (show x ∈ RingHom.ker c from hker.symm ▸ hx)
  have : IsLocalHom (Ideal.Quotient.mk P) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (j.comp c) := by rw [hj]; dsimp [d]; infer_instance
  exact ⟨P, hP, j, hjinj, isLocalHom_of_comp_surjective c j hc, hj, hPc⟩

private noncomputable def valuationSubringLocalizationMap
    {K L : Type*} [Field K] [Field L] (C : ValuationSubring K)
    (D : ValuationSubring L) (i : C →+* D) (p : Ideal C) [p.IsPrime]
    (P : Ideal D) [P.IsPrime] (hp : P.comap i = p) :
    C.ofPrime p →+* D.ofPrime P :=
  IsLocalization.map (M := p.primeCompl) (T := P.primeCompl) (D.ofPrime P) i (by
    intro x hx
    change i x ∉ P
    change x ∉ p at hx
    exact fun h => hx (hp ▸ h))

private theorem valuationSubringLocalizationMap_comp
    {K L : Type*} [Field K] [Field L] (C : ValuationSubring K)
    (D : ValuationSubring L) (i : C →+* D) (p : Ideal C) [p.IsPrime]
    (P : Ideal D) [P.IsPrime] (hp : P.comap i = p) :
    (valuationSubringLocalizationMap C D i p P hp).comp (algebraMap C (C.ofPrime p)) =
      (algebraMap D (D.ofPrime P)).comp i := by
  dsimp only [valuationSubringLocalizationMap]
  exact IsLocalization.map_comp _

private theorem valuationSubringLocalizationMap_subtype_comp
    {K L : Type*} [Field K] [Field L] (C : ValuationSubring K)
    (D : ValuationSubring L) (i : C →+* D) (j : K →+* L)
    (hij : D.subtype.comp i = j.comp C.subtype)
    (p : Ideal C) [p.IsPrime] (P : Ideal D) [P.IsPrime] (hp : P.comap i = p) :
    (D.ofPrime P).subtype.comp (valuationSubringLocalizationMap C D i p P hp) =
      j.comp (C.ofPrime p).subtype := by
  apply IsLocalization.ringHom_ext p.primeCompl
  rw [RingHom.comp_assoc, valuationSubringLocalizationMap_comp,
    ← RingHom.comp_assoc, RingHom.comp_assoc]
  exact hij

private theorem exists_valuationSubring_factorization_isLocalHom
    {A L : Type*} [CommRing A] [IsLocalRing A] [Field L] (φ : A →+* L) :
    ∃ (V : ValuationSubring L) (ψ : A →+* V),
      (∀ a : A, (ψ a : L) = φ a) ∧ IsLocalHom ψ := by
  let A₀ : LocalSubring L := LocalSubring.range φ
  obtain ⟨V, hV⟩ := A₀.exists_le_valuationSubring
  obtain ⟨hsub, hlocal⟩ := LocalSubring.le_def.mp hV
  let fA : A →+* A₀.toSubring := φ.codRestrict A₀.toSubring (fun a ↦ ⟨a, rfl⟩)
  have hfA : Function.Surjective fA := fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩
  let fV : A₀.toSubring →+* V := Subring.inclusion hsub
  let ψ : A →+* V := fV.comp fA
  let : IsLocalHom fA := IsLocalHom.of_surjective fA hfA
  let : IsLocalHom fV := hlocal
  exact ⟨V, ψ, fun _ => rfl, inferInstance⟩

open IsLocalRing in
private theorem residueValuationSubring_le {L : Type*} [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (ResidueField V)) :
    residueValuationSubring' V W ≤ V :=
  fun _ hx => (mem_residueValuationSubring.mp hx).choose

open IsLocalRing in
private noncomputable def residueValuationSubringResidue {L : Type*} [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (ResidueField V)) :
    residueValuationSubring' V W →+* W :=
  ((residue V).comp ((residueValuationSubring' V W).inclusion V
    (residueValuationSubring_le V W))).codRestrict W.toSubring (by
      intro x
      exact (mem_residueValuationSubring.mp x.property).choose_spec)

open IsLocalRing in
private theorem residueValuationSubringResidue_surjective {L : Type*} [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (ResidueField V)) :
    Function.Surjective (residueValuationSubringResidue V W) := by
  intro w
  obtain ⟨v, hv⟩ := residue_surjective (w : ResidueField V)
  have h : (v : L) ∈ residueValuationSubring' V W :=
    mem_residueValuationSubring.mpr ⟨v.property, hv ▸ w.property⟩
  exact ⟨⟨v, h⟩, Subtype.ext hv⟩

open IsLocalRing in
private theorem residueValuationSubringResidue_ker {L : Type*} [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (ResidueField V)) :
    RingHom.ker (residueValuationSubringResidue V W) =
      (residueValuationSubring' V W).idealOfLE V (residueValuationSubring_le V W) := by
  ext x
  change (residueValuationSubringResidue V W) x = 0 ↔
    (residueValuationSubring' V W).inclusion V _ x ∈ maximalIdeal V
  rw [← residue_eq_zero_iff]
  exact Subtype.ext_iff

open IsLocalRing in
private theorem residueValuationSubring_ofPrime {L : Type*} [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (ResidueField V)) :
    (residueValuationSubring' V W).ofPrime
      ((residueValuationSubring' V W).idealOfLE V (residueValuationSubring_le V W)) = V :=
  ValuationSubring.ofPrime_idealOfLE _ _ _

private noncomputable def residueValuationSubringLift
    {R L : Type*} [CommRing R] [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (IsLocalRing.ResidueField V))
    (r : R →+* V) (w : R →+* W)
    (h : (IsLocalRing.residue V).comp r = W.subtype.comp w) :
    R →+* residueValuationSubring' V W :=
  (V.subtype.comp r).codRestrict (residueValuationSubring' V W).toSubring (by
    intro x
    apply mem_residueValuationSubring.mpr
    refine ⟨(r x).property, ?_⟩
    have hx := DFunLike.congr_fun h x
    change IsLocalRing.residue V (r x) = (w x : IsLocalRing.ResidueField V) at hx
    change IsLocalRing.residue V (r x) ∈ W
    rw [hx]
    exact (w x).property)

private theorem residueValuationSubringLift_comp_inclusion
    {R L : Type*} [CommRing R] [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (IsLocalRing.ResidueField V))
    (r : R →+* V) (w : R →+* W)
    (h : (IsLocalRing.residue V).comp r = W.subtype.comp w) :
    ((residueValuationSubring' V W).inclusion V (residueValuationSubring_le V W)).comp
      (residueValuationSubringLift V W r w h) = r := by
  ext x
  rfl

private theorem residueValuationSubringLift_comp_residue
    {R L : Type*} [CommRing R] [Field L]
    (V : ValuationSubring L) (W : ValuationSubring (IsLocalRing.ResidueField V))
    (r : R →+* V) (w : R →+* W)
    (h : (IsLocalRing.residue V).comp r = W.subtype.comp w) :
    (residueValuationSubringResidue V W).comp
      (residueValuationSubringLift V W r w h) = w := by
  ext x
  exact DFunLike.congr_fun h x

private theorem specMap_preimage {R T : CommRingCat.{u}} (f : Spec T ⟶ Spec R) :
    Spec.map (CommRingCat.ofHom (Scheme.Spec.preimage f).unop.hom) = f :=
  Scheme.Spec.map_preimage f

private theorem ringHom_eq_of_specMap_eq
    {R T : Type u} [CommRing R] [CommRing T] {i j : R →+* T}
    (h : Spec.map (CommRingCat.ofHom i) = Spec.map (CommRingCat.ofHom j)) : i = j :=
  congrArg (fun t => t.unop.hom) (Scheme.Spec.map_injective h)

private theorem exists_residueField_map_of_comap_closedPoint_eq
    {P A K : Type*} [CommRing P] [CommRing A] [IsLocalRing A] [Field K]
    (e : P →+* K) (he : Function.Surjective e) (g : P →+* A)
    (h : PrimeSpectrum.comap g (IsLocalRing.closedPoint A) =
      PrimeSpectrum.comap e (IsLocalRing.closedPoint K)) :
    ∃ φ : K →+* IsLocalRing.ResidueField A, φ.comp e = (IsLocalRing.residue A).comp g := by
  have hker : RingHom.ker e ≤ RingHom.ker ((IsLocalRing.residue A).comp g) := by
    intro x hx
    change IsLocalRing.residue A (g x) = 0
    apply (IsLocalRing.residue_eq_zero_iff _).2
    have hx' : x ∈ (PrimeSpectrum.comap e (IsLocalRing.closedPoint K)).asIdeal := by
      change e x ∈ IsLocalRing.maximalIdeal K
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact hx
    rwa [← h] at hx'
  exact ⟨e.liftOfSurjective he ⟨(IsLocalRing.residue A).comp g, hker⟩,
    RingHom.liftOfSurjective_comp _ _ _⟩

private theorem exists_residueField_map_of_spec_closedPoint_eq
    {P A K : Type u} [CommRing P] [CommRing A] [IsLocalRing A] [Field K]
    (e : P →+* K) (he : Function.Surjective e) (s : Spec (.of A) ⟶ Spec (.of P))
    (h : s (IsLocalRing.closedPoint A) =
      Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint K)) :
    ∃ φ : K →+* IsLocalRing.ResidueField A,
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s =
        Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom e) := by
  let g := (Scheme.Spec.preimage s).unop.hom
  have hg : Spec.map (CommRingCat.ofHom g) = s := specMap_preimage s
  obtain ⟨φ, hφ⟩ := exists_residueField_map_of_comap_closedPoint_eq e he g (by
    change Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint A) = _
    rw [hg]
    exact h)
  refine ⟨φ, ?_⟩
  rw [← hg, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom hφ.symm)

private theorem fieldValuedPoint_map_subfunctor_transport
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z Z' : Subfunctor X} (e : Z = Z')
    (p : FieldValuedPoint B S hS Z.toFunctor) :
    FieldValuedPoint.map B S hS Z'.toFunctor Z'.ι (e ▸ p) =
      FieldValuedPoint.map B S hS Z.toFunctor Z.ι p := by
  subst Z'
  rfl

private theorem yoneda_hasEtaleLocalProperty_isReduced
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (hred : IsReduced ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun V : Scheme.{u} => IsReduced V) :=
  (AlgebraicGeometry.Space.exists_atlas_iff_of_representable B S hS
    (yoneda.obj T) (fun V : Scheme.{u} => IsReduced V) T (Iso.refl _)).2 hred

private theorem flat_of_etale_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj W ⟶ F)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    IsFlat B S hS a := by
  let : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan G := by infer_instance
  let : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G) :=
    inverseImage_isStableUnderBaseChange_of_preservesCospan G
      (@Etale.{u} : MorphismProperty Scheme.{u})
  let : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) G) :=
    inverseImage_isStableUnderBaseChange_of_preservesCospan G
      (@Surjective.{u} : MorphismProperty Scheme.{u})
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart
    (B := B) (S := S) (hS := hS) (P := @Flat)
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hF a).2
  refine ⟨W, W, yoneda.map (𝟙 W), a, 𝟙 W, ?_, ha, ?_, ?_, ?_⟩
  · exact (MorphismProperty.relative_map_iff
      (P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G)
      (F := yoneda) (f := 𝟙 W)).2 (by
        change Etale (G.map (𝟙 W))
        simpa using (show Etale (𝟙 (G.obj W)) from inferInstance))
  · exact (MorphismProperty.relative_map_iff
      (P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) G)
      (F := yoneda) (f := 𝟙 W)).2 (by
        change Surjective (G.map (𝟙 W))
        simpa using (show Surjective (𝟙 (G.obj W)) from inferInstance))
  · simp
  · infer_instance

/-- **A field-valued point of an algebraic space lifts to an étale scheme chart after one
extension of its field.**  For a field-valued point `p` of `X` there are an étale scheme chart
`a : W ⟶ X`, a field-valued point `p'` of `W` with the same image point as `p`, and a morphism
`j` from the spectrum of the field of `p'` to that of `p` along which `p` restricts to
`a ∘ p'`. -/
theorem exists_fieldValuedPoint_lift_to_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (p : FieldValuedPoint B S hS X) :
    ∃ (W : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj W ⟶ X)
      (_ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
      (p' : FieldValuedPoint B S hS (yoneda.obj W))
      (j : p'.siteObject ⟶ p.siteObject),
      (FieldValuedPoint.map B S hS (yoneda.obj W) a p').class
        B S hS X = p.class B S hS X ∧
      X.map j.op p.value =
        (FieldValuedPoint.map B S hS (yoneda.obj W) a p').value := by
  obtain ⟨W, a, ha, haEtale⟩ := hX.exists_atlas
  have hsurj := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda
    B S hS X hX W a).mp ha
  obtain ⟨z, hz⟩ := hsurj (p.class B S hS X)
  obtain ⟨p₀, rfl⟩ := Quot.exists_rep z
  have hpclass : (FieldValuedPoint.map B S hS
      (yoneda.obj W) a p₀).class B S hS X = p.class B S hS X := by
    simpa using hz
  obtain ⟨r, ⟨b, hb⟩, ⟨c, hc⟩⟩ :=
    (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS X
      (FieldValuedPoint.map B S hS (yoneda.obj W) a p₀) p).mp hpclass
  let b₀ : r.siteObject ⟶ p₀.siteObject := b
  let α₀ := yonedaEquiv.symm p₀.value
  let α₁ : yoneda.obj r.siteObject ⟶ yoneda.obj W := yoneda.map b₀ ≫ α₀
  let p₁ : FieldValuedPoint B S hS (yoneda.obj W) := {
    carrier := r.carrier
    field := r.field
    contained := r.contained
    toBase := r.toBase
    value := α₁.app (Opposite.op r.siteObject) (𝟙 r.siteObject) }
  have hp₁value : p₁.value = (yoneda.obj W).map b₀.op p₀.value := by
    change yonedaEquiv α₁ = (yoneda.obj W).map b₀.op p₀.value
    rw [← yonedaEquiv_naturality α₀ b₀]
    simp [α₀]
  have hmapvalue :
      (FieldValuedPoint.map B S hS (yoneda.obj W) a p₁).value =
        X.map b₀.op (FieldValuedPoint.map B S hS (yoneda.obj W) a p₀).value := by
    change a.app (Opposite.op r.siteObject) p₁.value =
      X.map b₀.op (a.app (Opposite.op p₀.siteObject) p₀.value)
    rw [hp₁value]
    exact NatTrans.naturality_apply a b₀.op p₀.value
  have hp₁ : (FieldValuedPoint.map B S hS (yoneda.obj W) a p₁).class
      B S hS X = (FieldValuedPoint.map B S hS (yoneda.obj W) a p₀).class
      B S hS X := by
    apply Quot.sound
    refine ⟨r, ⟨𝟙 r.siteObject, ?_⟩, ⟨b₀, hb⟩⟩
    change X.map (𝟙 (Opposite.op r.siteObject))
      ((FieldValuedPoint.map B S hS (yoneda.obj W) a p₁).value) = r.value
    exact (Functor.map_id_apply X (Opposite.op r.siteObject)
      ((FieldValuedPoint.map B S hS (yoneda.obj W) a p₁).value)).trans
      (hmapvalue.trans hb)
  let c₀ : p₁.siteObject ⟶ p.siteObject := c
  exact ⟨W, a, haEtale, p₁, c₀, hp₁.trans hpclass, hc.trans (hmapvalue.trans hb).symm⟩

private theorem yoneda_flat
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U T : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ T)
    (hf : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) :
    IsFlat B S hS (yoneda.map f) := by
  change HoldsOnEveryEtaleChart B S hS (@Flat) (yoneda.map f)
  rw [holdsOnEveryEtaleChart_iff_representable
    (B := B) (S := S) (hS := hS) (P := @Flat)
    (hP := AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget)
    (F := yoneda.obj U) (G := yoneda.obj T)]
  let e := yoneda.preimage (yoneda.obj U).reprW.hom
  let b := yoneda.preimage (yoneda.obj T).reprW.inv
  have hemap : yoneda.map e = (yoneda.obj U).reprW.hom := by
    simp [e]
  have hbmap : yoneda.map b = (yoneda.obj T).reprW.inv := by
    simp [b]
  let : IsIso (yoneda.map e) := by rw [hemap]; infer_instance
  let : IsIso (yoneda.map b) := by rw [hbmap]; infer_instance
  let : IsIso e := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful e
  let : IsIso b := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful b
  let : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map e) :=
    Functor.map_isIso _ e
  let : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b) :=
    Functor.map_isIso _ b
  have he : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map e) := inferInstance
  have hb : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b) := inferInstance
  have h1 := MorphismProperty.comp_mem (@Flat) _ _ he hf
  have h2 := MorphismProperty.comp_mem (@Flat) _ _ h1 hb
  simpa [e, b] using h2

private theorem isFlat_pullback_fst
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hT : AlgebraicGeometry.IsAlgebraicSpace B S hS T)
    (f : X ⟶ Y) (a : T ⟶ Y) (ha : IsFlat B S hS a) :
    IsFlat B S hS (pullback.fst f a) := by
  let F : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let G : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let H : AlgebraicSpaces B S hS := ⟨T, hT⟩
  let f' : F ⟶ G := ObjectProperty.homMk f
  let a' : H ⟶ G := ObjectProperty.homMk a
  exact (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS f' a').flip ha


private theorem mvPolynomial_eval_surjective
    {A L : Type u} [CommRing A] [Field L] (φ : A →+* L) :
    Function.Surjective (MvPolynomial.eval₂Hom φ (fun x : L => x)) :=
  fun x => ⟨MvPolynomial.X x, MvPolynomial.eval₂Hom_X' _ _ _⟩

private theorem mvPolynomial_spec_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) {A L : Type u}
    [CommRing A] [Field L] (hA : (Spec (.of A)).size < B.cutoff)
    (hL : (Spec (.of L)).size < B.cutoff) :
    (Spec (.of (MvPolynomial L A))).size < B.cutoff := by
  rw [Scheme.size_Spec] at hA hL
  have hA' : Cardinal.mk A < B.cutoff := lt_of_le_of_lt (le_max_right _ _) hA
  have hL' : Cardinal.mk L < B.cutoff := lt_of_le_of_lt (le_max_right _ _) hL
  have hP : Cardinal.mk (MvPolynomial L A) < B.cutoff := by
    have hmax : max (max (Cardinal.mk A) (Cardinal.mk L)) Cardinal.aleph0 < B.cutoff :=
      max_lt (max_lt hA' hL') B.aleph0_lt_cutoff
    exact lt_of_le_of_lt
      (show Cardinal.mk (MvPolynomial L A) ≤
        max (max (Cardinal.mk A) (Cardinal.mk L)) Cardinal.aleph0 by
          simpa [max_assoc] using
            (MvPolynomial.cardinalMk_le_max (σ := L) (R := A))) hmax
  have hsize : max Cardinal.aleph0 (Cardinal.mk (MvPolynomial L A)) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff hP
  simpa only [Scheme.size_Spec] using hsize

private theorem exists_flat_mvPolynomial_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) {W : Scheme.{u}}
    (hW : W.size < B.cutoff) {L : Type u} [Field L]
    (hL : (Spec (.of L)).size < B.cutoff) (t : Spec (.of L) ⟶ W) :
    ∃ (_ : B.Contains (Spec (.of
        (MvPolynomial L (W.presheaf.stalk (t (IsLocalRing.closedPoint L)))))))
      (g : Spec (.of
        (MvPolynomial L (W.presheaf.stalk (t (IsLocalRing.closedPoint L))))) ⟶ W),
      Function.Surjective
        (MvPolynomial.eval₂Hom
          (Scheme.stalkClosedPointTo t).hom (fun x : L => x)) ∧
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (Scheme.stalkClosedPointTo t).hom
          (fun x : L => x))) ≫ g = t ∧ Flat g := by
  let x := t (IsLocalRing.closedPoint L)
  let A := W.presheaf.stalk x
  let P := MvPolynomial L A
  let ev : P →+* L := MvPolynomial.eval₂Hom (Scheme.stalkClosedPointTo t).hom
    (fun z : L => z)
  have hASize : (Spec (.of A)).size < B.cutoff := by
    apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit (.of A) hW
    calc
      Cardinal.mk A ≤ W.size := Scheme.mk_stalk_le_size W x
      _ ≤ W.size ^ Cardinal.aleph0 :=
        Cardinal.self_le_power _ Cardinal.one_le_aleph0
  have hPSize : (Spec (.of P)).size < B.cutoff := by
    dsimp [P, A]
    exact mvPolynomial_spec_mem B hASize hL
  have hev : Function.Surjective ev := mvPolynomial_eval_surjective _
  let g : Spec (.of P) ⟶ W :=
    Spec.map (CommRingCat.ofHom (algebraMap A P)) ≫ W.fromSpecStalk x
  have hflatPoly : Flat (Spec.map (CommRingCat.ofHom (algebraMap A P))) := by
    rw [Flat.SpecMap_iff]
    change (algebraMap (↑A) P).Flat
    let : Module.Free (↑A) P := inferInstance
    exact RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free
  have hflat : Flat g :=
    MorphismProperty.comp_mem (@Flat) _ _ hflatPoly (flat_fromSpecStalk _ x)
  have hcomp : (ev.comp (algebraMap A P)) = (Scheme.stalkClosedPointTo t).hom := by
    ext a
    change ev (algebraMap A P a) = (Scheme.stalkClosedPointTo t).hom a
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C]
  have hmap : Spec.map (CommRingCat.ofHom ev) ≫ g = t := by
    calc
      Spec.map (CommRingCat.ofHom ev) ≫ g =
          Spec.map (CommRingCat.ofHom (ev.comp (algebraMap A P))) ≫
            W.fromSpecStalk x := by
              simp [g, CommRingCat.ofHom_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo t) ≫ W.fromSpecStalk x := by
            have hhom : CommRingCat.ofHom (ev.comp (algebraMap A P)) =
                Scheme.stalkClosedPointTo t := CommRingCat.hom_ext hcomp
            rw [hhom]
      _ = t := by simpa [x] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk t
  exact ⟨hPSize, g, hev, hmap, hflat⟩

private theorem reduced_map_factors_of_points_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z)
    (hpoints : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = Set.univ)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (hred : AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (yoneda.obj T)
      (fun V : Scheme.{u} => IsReduced V))
    (g : yoneda.obj T ⟶ X) :
    ∃ g' : yoneda.obj T ⟶ Z.toFunctor, g' ≫ Z.ι = g := by
  apply (AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset
    B S hS hX (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
    Z hZ hred g).2
  rw [hpoints]
  exact Set.subset_univ _

private theorem schemeTheoreticImage_points_surjective_of_dense
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (h : U ⟶ X)
    (hdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        pointTopology B S hS X
      DenseRange (pointsMap B S hS U h)) :
    Function.Surjective (pointsMap B S hS
      (schemeTheoreticImageSubfunctor B S hS h).toFunctor
      (schemeTheoreticImageSubfunctor B S hS h).ι) := by
  let I : Subfunctor X := schemeTheoreticImageSubfunctor B S hS h
  have hIclosed : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hX
  have hIfactors : Subfunctor.range h ≤ I :=
    range_le_schemeTheoreticImageSubfunctor B S hS h
  let i : I.toFunctor ⟶ X := I.ι
  have hiCI : IsClosedImmersion B S hS i := hIclosed.2
  have hiImm : IsImmersion B S hS i :=
    isImmersion_of_isClosedImmersion B S hS hiCI
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
    pointTopology B S hS X
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS I.toFunctor) :=
    pointTopology B S hS I.toFunctor
  have hiClosed : @IsClosed _ (pointTopology B S hS X)
      (Set.range (pointsMap B S hS I.toFunctor i)) :=
    (AlgebraicGeometry.Space.isClosedImmersion_iff_isClosed_range_pointsMap
      B S hS hX i hiImm).mp hiCI
  have hImage : Set.range (pointsMap B S hS U h) ⊆
      Set.range (pointsMap B S hS I.toFunctor i) := by
    conv_lhs => rw [← Subfunctor.lift_ι h hIfactors, pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  intro x
  have hx : x ∈ closure (Set.range (pointsMap B S hS U h)) := by
    rw [hdense.closure_range]
    trivial
  have hx' : x ∈ Set.range (pointsMap B S hS I.toFunctor i) :=
    (closure_minimal hImage hiClosed) hx
  simpa [i] using hx'

/-- The valuative square for `f` obtained from one for `pullback.diagonal f` by composing its
bottom edge with `pullback.fst f f ≫ f`. -/
private noncomputable abbrev diagonalValuativeSquare
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (q : ValuativeSquare (pullback.diagonal f)) : ValuativeSquare f where
  R := q.R
  K := q.K
  ring_mem := q.ring_mem
  field_mem := q.field_mem
  base := q.base
  generic := q.generic
  special := q.special ≫ pullback.fst f f ≫ f
  comm := by
    have hc := congrArg (fun k => k ≫ pullback.fst f f ≫ f) q.comm
    simpa [Category.assoc] using hc

private lemma diagonal_refined_valuative_uniqueness
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : U ⟶ X) (f : X ⟶ Y)
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift) :
    ∀ (q : ValuativeSquare (pullback.diagonal f))
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift := by
  intro q g hg
  let qf := diagonalValuativeSquare q
  have hqf : g ≫ h = qf.generic := hg
  let : Subsingleton qf.Lift := hunique qf g hqf
  refine ⟨fun a b => ?_⟩
  let toLift (a : q.Lift) : qf.Lift := {
    map := a.map
    generic_comm := a.generic_comm
    special_comm :=
      (by simp : a.map ≫ f = (a.map ≫ pullback.diagonal f) ≫ pullback.fst f f ≫ f).trans
        (congrArg (· ≫ pullback.fst f f ≫ f) a.special_comm) }
  have hab : a.map = b.map :=
    congrArg (fun l : qf.Lift => l.map) (Subsingleton.elim (toLift a) (toLift b))
  cases a with
  | mk amap ag aspec =>
    cases b with
    | mk bmap bg bspec =>
      dsimp at hab
      subst bmap
      rfl

private lemma diagonal_refined_valuative_existence
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : U ⟶ X) (f : X ⟶ Y)
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    (hexists : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    ∀ (q : ValuativeSquare (pullback.diagonal f))
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift := by
  intro q g hg
  let qf := diagonalValuativeSquare q
  have hqf : g ≫ h = qf.generic := hg
  obtain ⟨e, ⟨lift⟩⟩ := hexists qf g hqf
  let g' := yoneda.map e.genericOver ≫ g
  have hg' : g' ≫ h = e.square.generic := by
    calc
      g' ≫ h = yoneda.map e.genericOver ≫ (g ≫ h) := Category.assoc _ _ _
      _ = yoneda.map e.genericOver ≫ qf.generic := congrArg (yoneda.map e.genericOver ≫ ·) hqf
      _ = e.square.generic := e.generic_comm.symm
  let qArrow :
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem)
  let eArrow :
      siteObject B S hS e.square.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base) ⟶
      siteObject B S hS e.square.ring_mem e.square.base :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K))) :
      B.obj e.square.field_mem ⟶ B.obj e.square.ring_mem)
  have hqArrow_map : B.inclusion.map qArrow.left =
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := rfl
  have heArrow_map : B.inclusion.map eArrow.left =
      Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) := rfl
  have hArrow : e.genericOver ≫ qArrow = eArrow ≫ e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map e.genericOver.left ≫ B.inclusion.map qArrow.left =
      B.inclusion.map eArrow.left ≫ B.inclusion.map e.specialOver.left
    rw [e.genericOver_left, hqArrow_map, heArrow_map, e.specialOver_left]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom e.fraction_comm.symm)
  have : Subsingleton e.square.Lift := hunique e.square g' hg'
  have key : ∀ π : pullback f f ⟶ X, pullback.diagonal f ≫ π = 𝟙 X →
      π ≫ f = pullback.fst f f ≫ f →
      yoneda.map eArrow ≫ (yoneda.map e.specialOver ≫ q.special ≫ π) = e.square.generic ∧
        lift.map = yoneda.map e.specialOver ≫ q.special ≫ π := by
    intro π hπ hπf
    let L : e.square.Lift := {
      map := yoneda.map e.specialOver ≫ q.special ≫ π
      generic_comm := by
        calc
          yoneda.map eArrow ≫ (yoneda.map e.specialOver ≫ q.special ≫ π) =
              yoneda.map (eArrow ≫ e.specialOver) ≫ q.special ≫ π := by simp [Category.assoc]
          _ = yoneda.map (e.genericOver ≫ qArrow) ≫ q.special ≫ π := by rw [hArrow]
          _ = yoneda.map e.genericOver ≫ (yoneda.map qArrow ≫ q.special ≫ π) := by
            simp [Category.assoc]
          _ = yoneda.map e.genericOver ≫ q.generic := by
            congr 1
            have hc := congrArg (fun k => k ≫ π) q.comm
            simpa [Category.assoc, hπ] using hc.symm
          _ = e.square.generic := e.generic_comm.symm
      special_comm := by
        calc
          (yoneda.map e.specialOver ≫ q.special ≫ π) ≫ f =
              yoneda.map e.specialOver ≫ q.special ≫ pullback.fst f f ≫ f := by
            simp only [Category.assoc, hπf]
          _ = yoneda.map e.specialOver ≫ qf.special := rfl
          _ = e.square.special := e.special_comm.symm }
    exact ⟨L.generic_comm, congrArg (fun l : e.square.Lift => l.map) (Subsingleton.elim lift L)⟩
  obtain ⟨hgenSnd, hMapSnd⟩ :=
    key (pullback.snd f f) (pullback.diagonal_snd f) pullback.condition.symm
  obtain ⟨hgenFst, hMapFst⟩ := key (pullback.fst f f) (pullback.diagonal_fst f) rfl
  let specialDiag := pullback.lift (f := f) (g := f)
    (yoneda.map e.specialOver ≫ q.special ≫ pullback.fst f f)
    (yoneda.map e.specialOver ≫ q.special ≫ pullback.snd f f)
    (by simp only [Category.assoc, pullback.condition])
  let qd : ValuativeSquare (pullback.diagonal f) := {
    R := e.square.R
    K := e.square.K
    ring_mem := e.square.ring_mem
    field_mem := e.square.field_mem
    base := e.square.base
    generic := e.square.generic
    special := specialDiag
    comm := by
      apply pullback.hom_ext
      · simpa [specialDiag, pullback.lift_fst] using hgenFst.symm
      · simpa [specialDiag, pullback.lift_snd] using hgenSnd.symm }
  refine ⟨{
    square := qd
    ringMap := e.ringMap
    fieldMap := e.fieldMap
    isLocalHom := e.isLocalHom
    fraction_comm := e.fraction_comm
    base_comm := e.base_comm
    genericOver := e.genericOver
    genericOver_left := e.genericOver_left
    specialOver := e.specialOver
    specialOver_left := e.specialOver_left
    generic_comm := e.generic_comm
    special_comm := by
      apply pullback.hom_ext <;> simp [qd, specialDiag, pullback.lift_fst, pullback.lift_snd] }, ?_⟩
  exact ⟨{
    map := lift.map
    generic_comm := lift.generic_comm
    special_comm := by
      apply pullback.hom_ext
      · simpa [qd, specialDiag, pullback.lift_fst] using hMapFst
      · simpa [qd, specialDiag, pullback.lift_snd] using hMapSnd }⟩

private noncomputable def dominatingExtensionTrans
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {q : ValuativeSquare f}
    (e : q.DominatingExtension) (e' : e.square.DominatingExtension) :
    q.DominatingExtension := by
  letI := e.isLocalHom
  letI := e'.isLocalHom
  exact {
    square := e'.square
    ringMap := e'.ringMap.comp e.ringMap
    fieldMap := e'.fieldMap.comp e.fieldMap
    isLocalHom := inferInstance
    fraction_comm := by
      rw [← RingHom.comp_assoc, e'.fraction_comm, RingHom.comp_assoc,
        e.fraction_comm, RingHom.comp_assoc]
    base_comm := by
      rw [e'.base_comm, e.base_comm, ← Category.assoc, ← Spec.map_comp]
      rfl
    genericOver := e'.genericOver ≫ e.genericOver
    genericOver_left := by
      change B.inclusion.map e'.genericOver.left ≫
        B.inclusion.map e.genericOver.left = _
      rw [e'.genericOver_left, e.genericOver_left, ← Spec.map_comp]
      rfl
    specialOver := e'.specialOver ≫ e.specialOver
    specialOver_left := by
      change B.inclusion.map e'.specialOver.left ≫
        B.inclusion.map e.specialOver.left = _
      rw [e'.specialOver_left, e.specialOver_left, ← Spec.map_comp]
      rfl
    generic_comm := by rw [e'.generic_comm, e.generic_comm]; simp
    special_comm := by rw [e'.special_comm, e.special_comm]; simp }

private theorem eq_of_refinedValuative_uniqueness
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : U ⟶ X) (f : X ⟶ Y)
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hA : B.Contains (Spec (.of A))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of A) ⟶ S)
    (a b : yoneda.obj (siteObject B S hS hA base) ⟶ X)
    (g : yoneda.obj (siteObject B S hS hK
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ base)) ⟶ U)
    (ha : yoneda.map (Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))) ≫ a = g ≫ h)
    (hb : yoneda.map (Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))) ≫ b = g ≫ h)
    (hab : a ≫ f = b ≫ f) : a = b := by
  let q : ValuativeSquare f := {
    R := A, K := K, ring_mem := hA, field_mem := hK, base := base
    generic := g ≫ h, special := a ≫ f
    comm := by rw [← ha, Category.assoc] }
  let la : q.Lift := ⟨a, ha, rfl⟩
  let lb : q.Lift := ⟨b, hb, hab.symm⟩
  exact congrArg ValuativeSquare.Lift.map ((hunique q g rfl).elim la lb)

private theorem exists_dominatingExtension_lift_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (q : ValuativeSquare f) :
    ∃ (e : q.DominatingExtension) (W : AlgebraicGeometry.BigFppfOver B S hS)
      (a : yoneda.obj W ⟶ Y)
      (l : yoneda.obj (siteObject B S hS e.square.ring_mem
        e.square.base) ⟶ yoneda.obj W),
      IsFlat B S hS a ∧ l ≫ a = e.square.special := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let T := siteObject B S hS q.ring_mem q.base
  let k := IsLocalRing.ResidueField q.R
  have hk : B.Contains (Spec (.of k)) :=
    spec_mem_of_surjective B q.ring_mem (IsLocalRing.residue q.R)
      IsLocalRing.residue_surjective
  let p : FieldValuedPoint B S hS (yoneda.obj T) := {
    carrier := k, contained := hk
    toBase := Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R)) ≫ q.base
    value := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R)))) }
  obtain ⟨W, a, ha, haEtale⟩ := hY.exists_atlas
  have hflat := flat_of_etale_atlas B S hS Y hY W a haEtale
  have hsurj := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda
    B S hS Y hY W a).mp ha
  obtain ⟨A, hAring, hAdomain, hAval, i, hi, V, eV, j, l, hj, hl⟩ :=
    AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat q.R
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hY
      a hflat T (Iso.refl _) q.special p
      (by exact IsLocalRing.comap_closedPoint (IsLocalRing.residue q.R))
      (hsurj _)
  let := hAring
  let := hAdomain
  let := hAval
  have hA : B.Contains (Spec (.of A)) := by
    change (Spec (.of A)).size < B.cutoff
    rw [← Scheme.size_congr eV]
    exact V.left.2
  let L := FractionRing A
  have hL : B.Contains (Spec (.of L)) := spec_fractionRing_mem B hA
  let kmap : q.K →+* L := IsFractionRing.lift (A := q.R) (K := q.K)
    (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1)
  have hkmap : (algebraMap A L).comp i = kmap.comp (algebraMap q.R q.K) := by
    ext x
    exact (IsFractionRing.lift_algebraMap (K := q.K)
      (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1) x).symm
  let e := dominatingExtensionOfRingHom q hA hL i kmap hi.2 hkmap
  have hj' : G.map j = eV.hom ≫ Spec.map (CommRingCat.ofHom i) :=
    (Category.comp_id _).symm.trans hj
  have hb : eV.inv ≫ B.inclusion.map V.hom = e.square.base := by
    change eV.inv ≫ B.inclusion.map V.hom = Spec.map (CommRingCat.ofHom i) ≫ q.base
    have hw : G.map j ≫ q.base = B.inclusion.map V.hom :=
      congrArg B.inclusion.map j.w
    rw [← hw, hj']
    simp
  let v : siteObject B S hS e.square.ring_mem e.square.base ⟶ V :=
    Over.homMk (ObjectProperty.homMk eV.inv)
      (by apply B.inclusion.map_injective; exact hb)
  have hv : v ≫ j = e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change eV.inv ≫ G.map j = Spec.map (CommRingCat.ofHom i)
    rw [hj']
    simp
  refine ⟨e, W, a, yoneda.map v ≫ l, hflat, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, ← yoneda.map_comp, hv]
  exact e.special_comm.symm

private theorem exists_dominatingExtension_lift_affine
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (q : ValuativeSquare f) :
    ∃ (e : q.DominatingExtension) (R : CommRingCat.{u})
      (hR : B.Contains (Spec R)) (bR : Spec R ⟶ S)
      (a : yoneda.obj (siteObject B S hS hR bR) ⟶ Y)
      (l : siteObject B S hS e.square.ring_mem e.square.base ⟶
        siteObject B S hS hR bR),
      IsFlat B S hS a ∧ yoneda.map l ≫ a = e.square.special := by
  obtain ⟨e, W, a, l, ha, hl⟩ := exists_dominatingExtension_lift_atlas B S hS hY q
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let j := yoneda.preimage l
  have hj : yoneda.map j = l := yoneda.map_preimage l
  let t := G.map j
  let z := t (IsLocalRing.closedPoint e.square.R)
  let R := (G.obj W).presheaf.stalk z
  have hR : B.Contains (Spec R) := by
    apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit R W.left.2
    exact (Scheme.mk_stalk_le_size (G.obj W) z).trans
      (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  let bR := (G.obj W).fromSpecStalk z ≫ B.inclusion.map W.hom
  let T := siteObject B S hS hR bR
  let jR : T ⟶ W := Over.homMk (ObjectProperty.homMk ((G.obj W).fromSpecStalk z))
  have ht : Spec.map (Scheme.stalkClosedPointTo t) ≫ (G.obj W).fromSpecStalk z = t :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk t
  have htbase : Spec.map (Scheme.stalkClosedPointTo t) ≫ bR = e.square.base := by
    rw [← Category.assoc, ht]
    exact congrArg B.inclusion.map j.w
  let lR : siteObject B S hS e.square.ring_mem e.square.base ⟶ T :=
    Over.homMk (ObjectProperty.homMk (Spec.map (Scheme.stalkClosedPointTo t)))
      (by apply B.inclusion.map_injective; exact htbase)
  have hlR : lR ≫ jR = j := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact ht
  refine ⟨e, R, hR, bR, yoneda.map jR ≫ a, lR, ?_, ?_⟩
  · exact AlgebraicGeometry.Space.isFlat_comp B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hY
      (yoneda.map jR) a (yoneda_flat B S hS jR (flat_fromSpecStalk _ z)) ha
  · rw [← Category.assoc, ← yoneda.map_comp, hlR, hj, hl]

/-- For a quasi-compact morphism `f` of algebraic spaces over `S` with scheme-theoretic image `Z`
and a point `z` of `|Z|`, there is a valuative square for `f` whose bottom edge factors through
`Z`, a field-valued representative of `z` and a morphism from its spectrum to the spectrum of the
valuation ring landing on the closed point and restricting the factorization to that
representative. -/
private theorem exists_valuativeSquare_special_factors_of_schemeTheoreticImage_point
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor) :
    ∃ (q : ValuativeSquare f)
      (k : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶
        (schemeTheoreticImageSubfunctor B S hS f).toFunctor)
      (p : FieldValuedPoint B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor)
      (c : p.siteObject B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor ⟶
        siteObject B S hS q.ring_mem q.base),
      q.special = k ≫ (schemeTheoreticImageSubfunctor B S hS f).ι ∧
      p.class B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor = z ∧
      p.value = (schemeTheoreticImageSubfunctor B S hS f).toFunctor.map c.op (yonedaEquiv k) ∧
      (∀ x : Spec (.of p.carrier),
        ((B.inclusion).map c.left) x = IsLocalRing.closedPoint q.R) := by
  classical
  obtain ⟨q, w, hwclosed, hwspecial⟩ :=
    exists_valuativeSquare_toSchemeTheoreticImage B S hS f hX hY hf z
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : FieldValuedPoint B S hS
      (yoneda.obj (siteObject B S hS q.ring_mem q.base)),
      p₀.class B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base)) = w :=
    Quot.exists_rep w
  refine ⟨{ R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem
            base := q.base, generic := q.generic
            special := q.special ≫ (schemeTheoreticImageSubfunctor B S hS f).ι
            comm := ?_ },
          q.special,
          FieldValuedPoint.map B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base))
            q.special p₀,
          p₀.value, rfl, ?_, ?_, ?_⟩
  · calc q.generic ≫ f
        = q.generic ≫ (toSchemeTheoreticImage B S hS f ≫
            (schemeTheoreticImageSubfunctor B S hS f).ι) := by
          rw [toSchemeTheoreticImage_ι]
      _ = (q.generic ≫ toSchemeTheoreticImage B S hS f) ≫
            (schemeTheoreticImageSubfunctor B S hS f).ι := by rw [Category.assoc]
      _ = _ := by rw [q.comm, Category.assoc]
  · rw [← pointsMap_class, hp₀]
    exact hwspecial
  · rw [yonedaEquiv_apply]
    refine Eq.trans (congrArg (q.special.app (Opposite.op p₀.siteObject))
      (Category.comp_id p₀.value).symm) ?_
    exact NatTrans.naturality_apply q.special p₀.value.op
      (𝟙 (siteObject B S hS q.ring_mem q.base))
  · intro x
    have hsub : Subsingleton (Spec (CommRingCat.of p₀.carrier)) := inferInstance
    have hval : schemePoint B S hS (siteObject B S hS q.ring_mem q.base) p₀ =
        IsLocalRing.closedPoint q.R := by
      rw [← pointsToScheme_class B S hS (siteObject B S hS q.ring_mem q.base) p₀, hp₀]
      exact hwclosed
    exact (congrArg (fun y ↦ (B.inclusion).map p₀.value.left y)
      (hsub.elim x (IsLocalRing.closedPoint p₀.carrier))).trans hval

/-- A field-valued point of a chart `T` of an algebraic space `X` takes values in the
scheme-theoretic image of a morphism `h` with dense image on points. -/
private theorem fieldValuedPoint_value_mem_schemeTheoreticImageSubfunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X) (h : U ⟶ X)
    (hdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        pointTopology B S hS X
      DenseRange (pointsMap B S hS U h))
    {T : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj T ⟶ X)
    (p : FieldValuedPoint B S hS (yoneda.obj T)) :
    a.app (Opposite.op p.siteObject) p.value ∈
      (schemeTheoreticImageSubfunctor B S hS h).obj (Opposite.op p.siteObject) := by
  let I : Subfunctor X := schemeTheoreticImageSubfunctor B S hS h
  have hIclosed : IsClosedSubspace B S hS I :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hX
  have hIpoints := schemeTheoreticImage_points_surjective_of_dense B S hS hX h hdense
  have hIrange : Set.range (pointsMap B S hS I.toFunctor I.ι) = Set.univ :=
    Set.range_eq_univ.mpr hIpoints
  have hred : AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS
      (yoneda.obj p.siteObject) (fun V : Scheme.{u} => IsReduced V) := by
    apply yoneda_hasEtaleLocalProperty_isReduced B S hS p.siteObject
    change IsReduced (Spec (.of p.carrier))
    infer_instance
  let pto : yoneda.obj p.siteObject ⟶ yoneda.obj T := yonedaEquiv.symm p.value
  obtain ⟨gI, hgI⟩ := reduced_map_factors_of_points_surjective
    B S hS hX I hIclosed hIrange p.siteObject hred (pto ≫ a)
  have hpto : pto.app (Opposite.op p.siteObject) (𝟙 p.siteObject) = p.value := by
    calc
      pto.app (Opposite.op p.siteObject) (𝟙 p.siteObject) = yonedaEquiv pto :=
        (yonedaEquiv_apply pto).symm
      _ = p.value := Equiv.apply_symm_apply _ _
  have hsection : (I.ι).app (Opposite.op p.siteObject)
      (gI.app (Opposite.op p.siteObject) (𝟙 p.siteObject)) =
        a.app (Opposite.op p.siteObject) p.value := by
    calc
      _ = (gI ≫ I.ι).app (Opposite.op p.siteObject) (𝟙 p.siteObject) := rfl
      _ = (pto ≫ a).app (Opposite.op p.siteObject) (𝟙 p.siteObject) := by rw [hgI]
      _ = a.app (Opposite.op p.siteObject) p.value := by simp [hpto]
  rw [← hsection]
  exact (gI.app (Opposite.op p.siteObject) (𝟙 p.siteObject)).property

/-- A valuative square for the base change of `h` along a flat quasi-compact chart `g` of `X`,
reaching a prescribed field-valued point of the chart. The bottom edge of the square is
represented by a morphism of site objects carrying the closed point of the valuation ring to the
given point. -/
private theorem exists_valuativeSquare_of_flat_chart_point
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : AlgebraicGeometry.IsAlgebraicSpace B S hS U)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (h : U ⟶ X) (hh : AlgebraicGeometry.Space.IsQuasiCompact B S hS h)
    {T : AlgebraicGeometry.BigFppfOver B S hS} (g : yoneda.obj T ⟶ X)
    (hflat : IsFlat B S hS g)
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hmem : g.app (Opposite.op p.siteObject) p.value ∈
      (schemeTheoreticImageSubfunctor B S hS h).obj (Opposite.op p.siteObject)) :
    ∃ (qP : ValuativeSquare (pullback.snd h g))
      (s : siteObject B S hS qP.ring_mem qP.base ⟶ T),
      yoneda.map s = qP.special ∧
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s
          (IsLocalRing.closedPoint qP.R) =
        schemePoint B S hS T p := by
  let I : Subfunctor X := schemeTheoreticImageSubfunctor B S hS h
  have hPB : AlgebraicGeometry.IsAlgebraicSpace B S hS (pullback h g) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS h g hU
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) hX
  have hqcPB : AlgebraicGeometry.Space.IsQuasiCompact B S hS (pullback.snd h g) := by
    intro Z hZ hZqc k
    let e := ((pullbackSymmetry k (pullback.snd h g)).trans
      (pullbackLeftPullbackSndIso h g k)).trans
        (pullbackSymmetry h (k ≫ g))
    exact isQuasiCompactSpace_of_iso B S hS e.symm (hh Z hZ hZqc (k ≫ g))
  let J : Subfunctor (yoneda.obj T) :=
    schemeTheoreticImageSubfunctor B S hS (pullback.snd h g)
  have hJ : J = I.preimage g :=
    schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS g h
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) hX hU hflat hh
  let pPre : FieldValuedPoint B S hS (I.preimage g).toFunctor := {
    carrier := p.carrier
    field := p.field
    contained := p.contained
    toBase := p.toBase
    value := ⟨p.value, hmem⟩ }
  let pJ : FieldValuedPoint B S hS J.toFunctor := hJ.symm ▸ pPre
  obtain ⟨qP, gB, pB, cB, hspecialB, hclassB, hvalueB, hclosedB⟩ :=
    exists_valuativeSquare_special_factors_of_schemeTheoreticImage_point
      B S hS hPB (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
      (pullback.snd h g) hqcPB (pJ.class B S hS J.toFunctor)
  let sP := yoneda.preimage qP.special
  have hsP : yoneda.map sP = qP.special := yoneda.map_preimage qP.special
  let pBP := FieldValuedPoint.map B S hS J.toFunctor J.ι pB
  have hpJP : FieldValuedPoint.map B S hS J.toFunctor J.ι pJ = p := by
    dsimp only [pJ]
    rw [fieldValuedPoint_map_subfunctor_transport]
    rfl
  have hpBP : pBP.class B S hS (yoneda.obj T) = p.class B S hS (yoneda.obj T) := by
    have hc := congrArg (pointsMap B S hS J.toFunctor J.ι) hclassB
    change pBP.class B S hS (yoneda.obj T) =
      (FieldValuedPoint.map B S hS J.toFunctor J.ι pJ).class
        B S hS (yoneda.obj T) at hc
    rwa [hpJP] at hc
  have hcBsP : cB ≫ sP = pBP.value := by
    have hv := congrArg Subtype.val hvalueB
    change pBP.value = (yoneda.obj T).map cB.op
      (yonedaEquiv (gB ≫ J.ι)) at hv
    rw [← hspecialB, ← hsP, yonedaEquiv_yoneda_map] at hv
    exact hv.symm
  refine ⟨qP, sP, hsP, ?_⟩
  have hp := schemePoint_eq_of_class_eq B S hS T _ _ hpBP
  change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pBP.value
    (IsLocalRing.closedPoint pB.carrier) = _ at hp
  rw [← hcBsP] at hp
  change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sP
    ((B.inclusion).map cB.left (IsLocalRing.closedPoint pB.carrier)) = _ at hp
  rwa [hclosedB (IsLocalRing.closedPoint pB.carrier)] at hp

/-- The lift produced by a quotient of a dominating valuation ring.

The data are: a valuative square `q` for `f` whose bottom edge factors through a flat chart
`aR₀` of the target; a valuative square `qC` for `f` over a ring receiving `R₀`, with a
dominating extension `eC` and a lift `liftC` of it; a valuative square `qP` for the base change
of `h` along a chart `fP` of `X`; a localisation `V₁` of the dominating valuation ring receiving
both `eC.square.R` and `qP.R`, over which the lift agrees with the chart; and a dominating
extension `eE` of `q` whose valuation ring receives `eC.square.R` and whose fraction field
receives the coordinate field `K₀` of the chart compatibly. Then composing `liftC` with the
induced morphism of site objects lifts the dominating extension `eE`. -/
private theorem nonempty_lift_of_dominatingExtension_of_quotient
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : U ⟶ X) (f : X ⟶ Y) (q : ValuativeSquare f)
    (R₀ : CommRingCat.{u}) (hR₀ : B.Contains (Spec R₀)) (bR₀ : Spec R₀ ⟶ S)
    (aR₀ : yoneda.obj (siteObject B S hS hR₀ bR₀) ⟶ Y)
    (lR₀ : siteObject B S hS q.ring_mem q.base ⟶ siteObject B S hS hR₀ bR₀)
    (hlR₀ : yoneda.map lR₀ ≫ aR₀ = q.special)
    (rA₀ : R₀ →+* q.R)
    (hrA₀ : Spec.map (CommRingCat.ofHom rA₀) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map lR₀)
    {K₀ : Type u} [Field K₀] (hK₀ : B.Contains (Spec (.of K₀)))
    (bK₀ : Spec (.of K₀) ⟶ S)
    (jW : siteObject B S hS hK₀ bK₀ ⟶ siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
    (kP : q.K →+* K₀)
    (hkP : (B.inclusion).map jW.left = Spec.map (CommRingCat.ofHom kP))
    {P₀ : Type u} [CommRing P₀] (hP₀ : B.Contains (Spec (.of P₀)))
    (bP : Spec (.of P₀) ⟶ S) (evP : P₀ →+* K₀)
    (hevbase : Spec.map (CommRingCat.ofHom evP) ≫ bP = bK₀)
    (fP : yoneda.obj (siteObject B S hS hP₀ bP) ⟶ X)
    (evArrow : siteObject B S hS hK₀ bK₀ ⟶ siteObject B S hS hP₀ bP)
    (hevArrow : (B.inclusion).map evArrow.left = Spec.map (CommRingCat.ofHom evP))
    (hOriginalGeneric : yoneda.map evArrow ≫ fP = yoneda.map jW ≫ q.generic)
    (qP : ValuativeSquare (pullback.snd h fP))
    (sP : siteObject B S hS qP.ring_mem qP.base ⟶ siteObject B S hS hP₀ bP)
    (hsP : yoneda.map sP = qP.special)
    (rS : P₀ →+* qP.R)
    (hrS : Spec.map (CommRingCat.ofHom rS) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sP)
    (qC : ValuativeSquare f) (rC : R₀ →+* qC.R)
    (hqCbase : qC.base = Spec.map (CommRingCat.ofHom rC) ≫ bR₀)
    (cR₀ : siteObject B S hS qC.ring_mem qC.base ⟶ siteObject B S hS hR₀ bR₀)
    (hcR₀ : (B.inclusion).map cR₀.left = Spec.map (CommRingCat.ofHom rC))
    (hqCspecial : qC.special = yoneda.map cR₀ ≫ aR₀)
    (eC : qC.DominatingExtension) (liftC : eC.square.Lift)
    (eE : q.DominatingExtension) (rE : eC.square.R →+* eE.square.R)
    (hrER : (rE.comp eC.ringMap).comp rC = eE.ringMap.comp rA₀)
    (V₁ : ValuationSubring eC.square.K) (hV₁mem : B.Contains (Spec (.of V₁)))
    (dLoc : eC.square.R →+* V₁) (vLoc : qP.R →+* V₁)
    (rResid : V₁ →+* eE.square.K)
    (hresE : rResid.comp dLoc = (algebraMap eE.square.R eE.square.K).comp rE)
    (wKE : K₀ →+* eE.square.K) (hwKE : wKE.comp kP = eE.fieldMap)
    (hresP : (rResid.comp vLoc).comp rS = wKE.comp evP)
    (baseLoc : Spec (.of V₁) ⟶ S)
    (hbaseLoc : baseLoc = Spec.map (CommRingCat.ofHom dLoc) ≫ eC.square.base)
    (hbaseLocV : Spec.map (CommRingCat.ofHom vLoc) ≫ qP.base = baseLoc)
    (dOver : siteObject B S hS hV₁mem baseLoc ⟶
      siteObject B S hS eC.square.ring_mem eC.square.base)
    (hdOver : (B.inclusion).map dOver.left = Spec.map (CommRingCat.ofHom dLoc))
    (vOver : siteObject B S hS hV₁mem baseLoc ⟶ siteObject B S hS qP.ring_mem qP.base)
    (hvOver : (B.inclusion).map vOver.left = Spec.map (CommRingCat.ofHom vLoc))
    (habLoc : yoneda.map dOver ≫ liftC.map = yoneda.map vOver ≫ qP.special ≫ fP) :
    Nonempty eE.square.Lift := by
  have hbaseE : Spec.map (CommRingCat.ofHom rE) ≫ eC.square.base = eE.square.base := by
    rw [eC.base_comm, hqCbase, ← Category.assoc, ← Spec.map_comp, ← Category.assoc,
      ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((rE.comp eC.ringMap).comp rC)) ≫ bR₀ = _
    rw [hrER, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hbaseA : Spec.map (CommRingCat.ofHom rA₀) ≫ bR₀ = q.base := by
      rw [hrA₀]
      exact congrArg B.inclusion.map lR₀.w
    rw [hbaseA, eE.base_comm]
  let eOver : siteObject B S hS eE.square.ring_mem eE.square.base ⟶
      siteObject B S hS eC.square.ring_mem eC.square.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom rE)))
      (by apply B.inclusion.map_injective; exact hbaseE)
  have hresBase : Spec.map (CommRingCat.ofHom rResid) ≫ baseLoc =
      Spec.map (CommRingCat.ofHom (algebraMap eE.square.R eE.square.K)) ≫
        eE.square.base := by
    rw [hbaseLoc, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (rResid.comp dLoc)) ≫ eC.square.base = _
    rw [hresE, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hbaseE]
  let resOver : siteObject B S hS eE.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap eE.square.R eE.square.K)) ≫
        eE.square.base) ⟶ siteObject B S hS hV₁mem baseLoc :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom rResid)))
      (by apply B.inclusion.map_injective; exact hresBase)
  have hresOver : resOver ≫ dOver = specializationArrow eE.square ≫ eOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom rResid) ≫ (B.inclusion).map dOver.left =
      Spec.map (CommRingCat.ofHom (algebraMap eE.square.R eE.square.K)) ≫
        Spec.map (CommRingCat.ofHom rE)
    rw [hdOver, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hresE
  have hwBase : Spec.map (CommRingCat.ofHom wKE) ≫ bK₀ =
      Spec.map (CommRingCat.ofHom (algebraMap eE.square.R eE.square.K)) ≫
        eE.square.base := by
    rw [← hevbase, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (wKE.comp evP)) ≫ bP = _
    rw [← hresP, CommRingCat.ofHom_comp, Spec.map_comp,
      CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc]
    have hsBase : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sP ≫ bP =
        qP.base := congrArg B.inclusion.map sP.w
    rw [hrS, hsBase, hbaseLocV, hresBase]
  let wOver : siteObject B S hS eE.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap eE.square.R eE.square.K)) ≫
        eE.square.base) ⟶ siteObject B S hS hK₀ bK₀ :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom wKE)))
      (by apply B.inclusion.map_injective; exact hwBase)
  have hwOverK : wOver ≫ jW = eE.genericOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom wKE) ≫ (B.inclusion).map jW.left =
      (B.inclusion).map eE.genericOver.left
    rw [hkP, eE.genericOver_left, ← hwKE, CommRingCat.ofHom_comp, Spec.map_comp]
  have hwOverP : wOver ≫ evArrow = resOver ≫ vOver ≫ sP := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom wKE) ≫ (B.inclusion).map evArrow.left =
      Spec.map (CommRingCat.ofHom rResid) ≫ (B.inclusion).map vOver.left ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sP
    rw [hevArrow, hvOver, ← hrS, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hresP.symm
  have heOverR : eOver ≫ eC.specialOver ≫ cR₀ = eE.specialOver ≫ lR₀ := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom rE) ≫ (B.inclusion).map eC.specialOver.left ≫
      (B.inclusion).map cR₀.left = (B.inclusion).map eE.specialOver.left ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map lR₀
    rw [eC.specialOver_left, eE.specialOver_left, hcR₀, ← hrA₀, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hrER
  refine ⟨{
    map := yoneda.map eOver ≫ liftC.map
    generic_comm := ?_
    special_comm := ?_ }⟩
  · have hmap : yoneda.map (specializationArrow eE.square) ≫ yoneda.map eOver =
        yoneda.map resOver ≫ yoneda.map dOver :=
      (yoneda.map_comp (specializationArrow eE.square) eOver).symm.trans
        ((congrArg yoneda.map hresOver.symm).trans (yoneda.map_comp resOver dOver))
    have hgeneric1 :
        yoneda.map (specializationArrow eE.square) ≫ (yoneda.map eOver ≫ liftC.map) =
          yoneda.map resOver ≫ yoneda.map dOver ≫ liftC.map :=
      (Category.assoc (yoneda.map (specializationArrow eE.square))
        (yoneda.map eOver) liftC.map).symm.trans
        ((congrArg (fun t => t ≫ liftC.map) hmap).trans
          (Category.assoc (yoneda.map resOver) (yoneda.map dOver) liftC.map))
    have hgeneric2 :
        yoneda.map (specializationArrow eE.square) ≫ (yoneda.map eOver ≫ liftC.map) =
          yoneda.map resOver ≫ yoneda.map vOver ≫ qP.special ≫ fP :=
      hgeneric1.trans (by rw [habLoc])
    have hgeneric3 : yoneda.map resOver ≫ yoneda.map vOver ≫ qP.special ≫ fP =
        yoneda.map wOver ≫ yoneda.map evArrow ≫ fP := by
      rw [← hsP]
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun r => yoneda.map r ≫ fP) hwOverP.symm
    have hgeneric4 : yoneda.map wOver ≫ yoneda.map evArrow ≫ fP =
        yoneda.map eE.genericOver ≫ q.generic := by
      have h₁ := congrArg (fun t => yoneda.map wOver ≫ t) hOriginalGeneric
      have h₂ := congrArg (fun t => yoneda.map t ≫ q.generic) hwOverK
      have hmap := congrArg (fun t => t ≫ q.generic) (yoneda.map_comp wOver jW)
      exact h₁.trans ((Category.assoc (yoneda.map wOver) (yoneda.map jW)
        q.generic).symm.trans (hmap.symm.trans h₂))
    exact hgeneric2.trans (hgeneric3.trans
      (hgeneric4.trans eE.generic_comm.symm))
  · rw [Category.assoc, liftC.special_comm, eC.special_comm, hqCspecial,
      ← Category.assoc, ← yoneda.map_comp, ← Category.assoc, ← yoneda.map_comp,
      Category.assoc, heOverR, Functor.map_comp, Category.assoc, hlR₀]
    exact eE.special_comm.symm

/-- The existence half of the refined valuative criterion, over a flat chart of the source.

Let `q` be a valuative square for `f` whose bottom edge factors through a flat chart
`a : T₀ ⟶ Y` of the target, and let `fP : TP ⟶ X` be a flat chart of `X` whose underlying
scheme is the spectrum of a ring `P₀` surjecting onto a field `K₀`, carrying the generic point
of `q` and having its base-change along `h` dominant over the point of `Spec P₀` cut out by
that surjection. Then `q` has a dominating extension with a lift. -/
private theorem exists_dominatingExtension_lift_of_flat_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : AlgebraicGeometry.IsAlgebraicSpace B S hS U)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (h : U ⟶ X) (f : X ⟶ Y)
    (hh : AlgebraicGeometry.Space.IsQuasiCompact B S hS h)
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    (hexists : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift)
    (q : ValuativeSquare f)
    (R₀ : CommRingCat.{u}) (hR₀ : B.Contains (Spec R₀)) (bR₀ : Spec R₀ ⟶ S)
    (aR₀ : yoneda.obj (siteObject B S hS hR₀ bR₀) ⟶ Y)
    (lR₀ : siteObject B S hS q.ring_mem q.base ⟶ siteObject B S hS hR₀ bR₀)
    (hlR₀ : yoneda.map lR₀ ≫ aR₀ = q.special)
    {K₀ : Type u} [Field K₀] (hK₀ : B.Contains (Spec (.of K₀)))
    (bK₀ : Spec (.of K₀) ⟶ S)
    {P₀ : Type u} [CommRing P₀] (hP₀ : B.Contains (Spec (.of P₀)))
    (bP : Spec (.of P₀) ⟶ S)
    (evP : P₀ →+* K₀) (hevP : Function.Surjective evP)
    (hevbase : Spec.map (CommRingCat.ofHom evP) ≫ bP = bK₀)
    (fP : yoneda.obj (siteObject B S hS hP₀ bP) ⟶ X) (hflatFP : IsFlat B S hS fP)
    (bP₀ : siteObject B S hS hP₀ bP ⟶ siteObject B S hS hR₀ bR₀)
    (hfP₀ : fP ≫ f = yoneda.map bP₀ ≫ aR₀)
    (evArrow : siteObject B S hS hK₀ bK₀ ⟶ siteObject B S hS hP₀ bP)
    (hevArrow : (B.inclusion).map evArrow.left = Spec.map (CommRingCat.ofHom evP))
    (jW : siteObject B S hS hK₀ bK₀ ⟶ siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
    (kP : q.K →+* K₀)
    (hkP : (B.inclusion).map jW.left = Spec.map (CommRingCat.ofHom kP))
    (hOriginalGeneric : yoneda.map evArrow ≫ fP = yoneda.map jW ≫ q.generic)
    (hEvR₀ : evArrow ≫ bP₀ = jW ≫ specializationArrow q ≫ lR₀)
    (hmem : fP.app (Opposite.op (siteObject B S hS hK₀ bK₀)) evArrow ∈
      (schemeTheoreticImageSubfunctor B S hS h).obj
        (Opposite.op (siteObject B S hS hK₀ bK₀))) :
    ∃ e : q.DominatingExtension, Nonempty e.square.Lift := by
  let T₀ := siteObject B S hS hR₀ bR₀
  let evSpec := Spec.map (CommRingCat.ofHom evP)
  let pP : FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS hP₀ bP)) := {
    carrier := K₀
    field := inferInstance
    contained := hK₀
    toBase := bK₀
    value := evArrow }
  obtain ⟨qP, sP, hsP, hclosedPt⟩ := exists_valuativeSquare_of_flat_chart_point
    B S hS hU hX h hh fP hflatFP pP hmem
  let sPS : Spec (.of qP.R) ⟶ Spec (.of P₀) :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sP
  have hclosedP : sPS (IsLocalRing.closedPoint qP.R) =
      evSpec (IsLocalRing.closedPoint K₀) := by
    have hpt : ((B.inclusion).map evArrow.left) (IsLocalRing.closedPoint K₀) =
        evSpec (IsLocalRing.closedPoint K₀) :=
      congrArg (fun m => m (IsLocalRing.closedPoint K₀)) hevArrow
    exact hclosedPt.trans hpt
  obtain ⟨φP, hφP⟩ := exists_residueField_map_of_spec_closedPoint_eq
    evP hevP sPS hclosedP
  let V : ValuationSubring qP.K := (ValuationRing.valuation qP.R qP.K).valuationSubring
  let eV : qP.R ≃+* V := ValuationRing.equivInteger qP.R qP.K
  let φ : q.K →+* IsLocalRing.ResidueField V :=
    ((IsLocalRing.ResidueField.mapEquiv eV).toRingHom.comp φP).comp kP
  let : IsLocalHom eV.toRingHom := IsLocalHom.of_surjective _ eV.surjective
  obtain ⟨W', aW, haW, hlocalW⟩ :=
    exists_valuationSubring_factorization_isLocalHom (φ.comp (algebraMap q.R q.K))
  let C := residueValuationSubring' V W'
  let cV : C →+* V := C.inclusion V (residueValuationSubring_le V W')
  let cW : C →+* W' := residueValuationSubringResidue V W'
  have hcW : Function.Surjective cW := residueValuationSubringResidue_surjective V W'
  let prime : Ideal C := C.idealOfLE V (residueValuationSubring_le V W')
  have hprime : prime = RingHom.ker cW := (residueValuationSubringResidue_ker V W').symm
  have hlocalization : C.ofPrime prime = V := residueValuationSubring_ofPrime V W'
  have hCmem : B.Contains (Spec (.of C)) :=
    spec_mem_of_injective B qP.field_mem C.subtype C.subtype_injective
  let rP₀ : R₀ →+* P₀ :=
    (Scheme.Spec.preimage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bP₀)).unop.hom
  let rA₀ : R₀ →+* q.R :=
    (Scheme.Spec.preimage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map lR₀)).unop.hom
  let rS : P₀ →+* qP.R :=
    (Scheme.Spec.preimage sPS).unop.hom
  have hev₀ : evP.comp rP₀ = kP.comp ((algebraMap q.R q.K).comp rA₀) := by
    apply ringHom_eq_of_specMap_eq
    simp only [Spec.map_comp, CommRingCat.ofHom_comp]
    change evSpec ≫ Spec.map (CommRingCat.ofHom rP₀) =
      Spec.map (CommRingCat.ofHom kP) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom rA₀)
    simp only [rP₀, rA₀, specMap_preimage]
    let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
    have hmapEv' : F.map evArrow = evSpec := hevArrow
    have hmapjW' : F.map jW = Spec.map (CommRingCat.ofHom kP) := hkP
    have hmapspec' : F.map (specializationArrow q) =
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := rfl
    have htail : F.map (jW ≫ specializationArrow q ≫ lR₀) =
        F.map jW ≫ (F.map (specializationArrow q) ≫ F.map lR₀) :=
      (F.map_comp jW (specializationArrow q ≫ lR₀)).trans
        (congrArg (fun z => F.map jW ≫ z) (F.map_comp (specializationArrow q) lR₀))
    calc
      evSpec ≫ F.map bP₀ = F.map (evArrow ≫ bP₀) :=
        (congrArg (fun t => t ≫ F.map bP₀) hmapEv'.symm).trans
          (F.map_comp evArrow bP₀).symm
      _ = F.map (jW ≫ specializationArrow q ≫ lR₀) := congrArg F.map hEvR₀
      _ = F.map jW ≫ (F.map (specializationArrow q) ≫ F.map lR₀) := htail
      _ = Spec.map (CommRingCat.ofHom kP) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ F.map lR₀) :=
        (congrArg (fun t => t ≫ (F.map (specializationArrow q) ≫ F.map lR₀))
          hmapjW').trans (congrArg
            (fun t => Spec.map (CommRingCat.ofHom kP) ≫ (t ≫ F.map lR₀)) hmapspec')
  have hφPring : φP.comp evP = (IsLocalRing.residue qP.R).comp rS := by
    apply ringHom_eq_of_specMap_eq
    simpa only [Spec.map_comp, CommRingCat.ofHom_comp, rS,
      specMap_preimage] using hφP.symm
  let rV : R₀ →+* V := eV.toRingHom.comp (rS.comp rP₀)
  let rW : R₀ →+* W' := aW.comp rA₀
  have hrVW : (IsLocalRing.residue V).comp rV = W'.subtype.comp rW := by
    ext x
    change IsLocalRing.residue V (eV (rS (rP₀ x))) = (aW (rA₀ x) : _)
    rw [haW]
    change _ = IsLocalRing.ResidueField.mapEquiv eV (φP (kP (algebraMap q.R q.K (rA₀ x))))
    have htarget : φP (kP ((algebraMap q.R q.K) (rA₀ x))) =
        IsLocalRing.residue qP.R (rS (rP₀ x)) := by
      have h₁ := DFunLike.congr_fun hev₀ x
      have h₂ := DFunLike.congr_fun hφPring (rP₀ x)
      calc
        _ = φP (evP (rP₀ x)) := congrArg φP h₁.symm
        _ = _ := h₂
    rw [htarget]
    exact (IsLocalRing.ResidueField.map_residue eV.toRingHom _).symm
  let rC : R₀ →+* C := residueValuationSubringLift V W' rV rW hrVW
  have hrCV : cV.comp rC = rV := residueValuationSubringLift_comp_inclusion V W' rV rW hrVW
  have hrCW : cW.comp rC = rW := residueValuationSubringLift_comp_residue V W' rV rW hrVW
  let vMap : C →+* qP.R := eV.symm.toRingHom.comp cV
  have hvMap : vMap.comp rC = rS.comp rP₀ := by
    rw [RingHom.comp_assoc, hrCV]
    ext x
    exact eV.symm_apply_apply _
  have hvFrac : (algebraMap qP.R qP.K).comp vMap = algebraMap C qP.K := by
    ext x
    change algebraMap qP.R qP.K (eV.symm (cV x)) = (x : qP.K)
    calc
      _ = (eV (eV.symm (cV x)) : qP.K) :=
        (ValuationRing.coe_equivInteger_apply qP.R qP.K _).symm
      _ = (x : qP.K) := by rw [eV.apply_symm_apply]; rfl
  let baseC := Spec.map (CommRingCat.ofHom rC) ≫ bR₀
  have hbaseV : Spec.map (CommRingCat.ofHom vMap) ≫ baseC = qP.base := by
    change Spec.map (CommRingCat.ofHom vMap) ≫ Spec.map (CommRingCat.ofHom rC) ≫ bR₀ = _
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (vMap.comp rC)) ≫ bR₀ = _
    rw [hvMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    dsimp only [rS, rP₀]
    rw [specMap_preimage, specMap_preimage]
    have hbP := congrArg B.inclusion.map bP₀.w
    have hsPbase := congrArg B.inclusion.map sP.w
    exact (congrArg (fun t => sPS ≫ t) hbP).trans hsPbase
  have hbaseK : Spec.map (CommRingCat.ofHom (algebraMap C qP.K)) ≫ baseC =
      Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K)) ≫ qP.base := by
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K)) ≫
          Spec.map (CommRingCat.ofHom vMap) ≫ baseC := by
        simpa only [Spec.map_comp, CommRingCat.ofHom_comp, Category.assoc] using
          (congrArg (fun r => Spec.map (CommRingCat.ofHom r) ≫ baseC) hvFrac).symm
      _ = _ := by rw [hbaseV]
  let TC := siteObject B S hS hCmem baseC
  let KC := siteObject B S hS qP.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap C qP.K)) ≫ baseC)
  let cR₀ : TC ⟶ T₀ := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom rC)))
  let vC : siteObject B S hS qP.ring_mem qP.base ⟶ TC :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom vMap)))
      (by apply B.inclusion.map_injective; exact hbaseV)
  let kC : KC ⟶ siteObject B S hS qP.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K)) ≫ qP.base) :=
    Over.homMk (ObjectProperty.homMk (𝟙 (Spec (.of qP.K))))
      (by
        apply B.inclusion.map_injective
        change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K)) ≫
          qP.base = Spec.map (CommRingCat.ofHom (algebraMap C qP.K)) ≫ baseC
        simpa only [Category.id_comp] using hbaseK.symm)
  let sC : KC ⟶ TC := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap C qP.K))))
  have hkv : kC ≫ specializationArrow qP ≫ vC = sC := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K)) ≫
      Spec.map (CommRingCat.ofHom vMap) = Spec.map (CommRingCat.ofHom (algebraMap C qP.K))
    rw [Category.id_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hvFrac
  have hvR : vC ≫ cR₀ = sP ≫ bP₀ := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom vMap) ≫ Spec.map (CommRingCat.ofHom rC) =
      sPS ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bP₀
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (vMap.comp rC)) = _
    rw [hvMap, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [rS, rP₀, specMap_preimage]
  let uC : yoneda.obj KC ⟶ U :=
    yoneda.map kC ≫ qP.generic ≫ pullback.fst h fP
  have hgenC : (uC ≫ h) ≫ f = yoneda.map sC ≫ yoneda.map cR₀ ≫ aR₀ := by
    calc
      _ = yoneda.map kC ≫ qP.generic ≫ pullback.snd h fP ≫ fP ≫ f := by
        simp only [uC, Category.assoc, pullback.condition]
      _ = yoneda.map kC ≫ yoneda.map (specializationArrow qP) ≫
          qP.special ≫ fP ≫ f := by
        rw [← Category.assoc qP.generic, qP.comm]
        simp only [Category.assoc]
      _ = yoneda.map kC ≫ yoneda.map (specializationArrow qP) ≫
          yoneda.map sP ≫ yoneda.map bP₀ ≫ aR₀ := by
        rw [← hsP, hfP₀]
      _ = yoneda.map sC ≫ yoneda.map cR₀ ≫ aR₀ := by
        have hpath : kC ≫ specializationArrow qP ≫ sP ≫ bP₀ = sC ≫ cR₀ := by
          calc
            _ = (kC ≫ specializationArrow qP) ≫ (sP ≫ bP₀) := by
              simp only [Category.assoc]
            _ = (kC ≫ specializationArrow qP) ≫ (vC ≫ cR₀) := by rw [hvR]
            _ = sC ≫ cR₀ := by
              simpa only [Category.assoc] using
                (congrArg (fun t => t ≫ cR₀) hkv)
        simpa only [Functor.map_comp, Category.assoc] using
          (congrArg (fun t => yoneda.map t ≫ aR₀) hpath)
  let qC : ValuativeSquare f := {
    R := C, K := qP.K, ring_mem := hCmem, field_mem := qP.field_mem
    base := baseC, generic := uC ≫ h, special := yoneda.map cR₀ ≫ aR₀
    comm := hgenC }
  obtain ⟨eC, ⟨liftC⟩⟩ := hexists qC uC rfl
  let D : ValuationSubring eC.square.K :=
    (ValuationRing.valuation eC.square.R eC.square.K).valuationSubring
  let eD : eC.square.R ≃+* D := ValuationRing.equivInteger eC.square.R eC.square.K
  let iD : C →+* D := eD.toRingHom.comp eC.ringMap
  have hiC : Function.Injective eC.ringMap := by
    intro x y hxy
    apply IsFractionRing.injective C qP.K
    apply eC.fieldMap.injective
    have hc := congrArg (algebraMap eC.square.R eC.square.K) hxy
    simpa only [← RingHom.comp_apply, eC.fraction_comm] using hc
  have hiD : Function.Injective iD := eD.injective.comp hiC
  let : IsLocalHom eC.ringMap := eC.isLocalHom
  let : IsLocalHom eD.toRingHom := IsLocalHom.of_surjective _ eD.surjective
  let : IsLocalHom iD := inferInstance
  obtain ⟨P, hP, jE, hjE, hjElocal, hjEcomp, hPc⟩ :=
    exists_quotient_extension_of_surjective cW hcW iD hiD
  let := hP
  let E := D ⧸ P
  let : ValuationRing E := valuationRing_quotient_of_prime P
  let KE := FractionRing E
  have hDmem : B.Contains (Spec (.of D)) :=
    spec_mem_of_injective B eC.square.field_mem D.subtype D.subtype_injective
  have hEmem : B.Contains (Spec (.of E)) :=
    spec_mem_of_surjective B hDmem (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hKEmem : B.Contains (Spec (.of KE)) := spec_fractionRing_mem B hEmem
  let kE : IsLocalRing.ResidueField V →+* KE :=
    IsFractionRing.lift (A := W') (K := IsLocalRing.ResidueField V)
      (L := KE) (g := (algebraMap E KE).comp jE)
      ((IsFractionRing.injective E KE).comp hjE)
  let aE : q.R →+* E := jE.comp aW
  let fieldE : q.K →+* KE := kE.comp φ
  have hfracE : (algebraMap E KE).comp aE = fieldE.comp (algebraMap q.R q.K) := by
    ext x
    change algebraMap E KE (jE (aW x)) = kE (φ (algebraMap q.R q.K x))
    have hx : (aW x : IsLocalRing.ResidueField V) =
        φ (algebraMap q.R q.K x) := by
      simpa only [RingHom.comp_apply] using haW x
    rw [← hx]
    simpa only [kE, RingHom.comp_apply, ValuationSubring.algebraMap_apply] using
      (IsFractionRing.lift_algebraMap
        (A := W') (K := IsLocalRing.ResidueField V) (L := KE)
        (g := (algebraMap E KE).comp jE)
        ((IsFractionRing.injective E KE).comp hjE) (aW x)).symm
  let : IsLocalHom aW := hlocalW
  let : IsLocalHom jE := hjElocal
  let eE := dominatingExtensionOfRingHom q hEmem hKEmem aE fieldE
    (show IsLocalHom aE from inferInstance) hfracE
  let : prime.IsPrime := by rw [hprime]; exact RingHom.ker_isPrime cW
  have hPprime : P.comap iD = prime := hPc.trans hprime.symm
  let V₁ := D.ofPrime P
  let mV := valuationSubringLocalizationMap C D iD prime P hPprime
  have hiDfrac : D.subtype.comp iD = eC.fieldMap.comp C.subtype := by
    ext x
    change (eD (eC.ringMap x) : eC.square.K) = eC.fieldMap (x : qP.K)
    rw [ValuationRing.coe_equivInteger_apply]
    exact DFunLike.congr_fun eC.fraction_comm x
  have hmVfrac := valuationSubringLocalizationMap_subtype_comp C D iD
    eC.fieldMap hiDfrac prime P hPprime
  let vToPrime : V →+* C.ofPrime prime := V.inclusion _ hlocalization.ge
  let primeToV : C.ofPrime prime →+* V := (C.ofPrime prime).inclusion V hlocalization.le
  let vLoc : qP.R →+* V₁ := mV.comp (vToPrime.comp eV.toRingHom)
  let dLoc : eC.square.R →+* V₁ := (algebraMap D V₁).comp eD.toRingHom
  let rE : eC.square.R →+* E := (Ideal.Quotient.mk P).comp eD.toRingHom
  have hvLocFrac : V₁.subtype.comp vLoc = eC.fieldMap.comp (algebraMap qP.R qP.K) := by
    ext x
    have h := DFunLike.congr_fun hmVfrac (vToPrime (eV x))
    change (vLoc x : eC.square.K) = eC.fieldMap (algebraMap qP.R qP.K x)
    exact h.trans (congrArg eC.fieldMap (ValuationRing.coe_equivInteger_apply qP.R qP.K x))
  have hdLocFrac : V₁.subtype.comp dLoc = algebraMap eC.square.R eC.square.K := by
    ext x
    exact ValuationRing.coe_equivInteger_apply eC.square.R eC.square.K x
  have hvLoc : vLoc.comp vMap = dLoc.comp eC.ringMap := by
    ext x
    change V₁.subtype (vLoc (vMap x)) = V₁.subtype (dLoc (eC.ringMap x))
    calc
      _ = eC.fieldMap (algebraMap qP.R qP.K (vMap x)) := by
        simpa only [RingHom.comp_apply] using DFunLike.congr_fun hvLocFrac (vMap x)
      _ = eC.fieldMap (algebraMap C qP.K x) :=
        congrArg eC.fieldMap (DFunLike.congr_fun hvFrac x)
      _ = algebraMap eC.square.R eC.square.K (eC.ringMap x) := by
        simpa only [RingHom.comp_apply] using
          (DFunLike.congr_fun eC.fraction_comm x).symm
      _ = _ := by
        simpa only [RingHom.comp_apply] using
          (DFunLike.congr_fun hdLocFrac (eC.ringMap x)).symm
  let rResid : V₁ →+* KE :=
    IsLocalization.lift (M := P.primeCompl) (g := (algebraMap E KE).comp (Ideal.Quotient.mk P))
      (by
        intro x
        apply isUnit_iff_ne_zero.mpr
        change algebraMap E KE (Ideal.Quotient.mk P x) ≠ 0
        intro hx
        have hx' := (IsFractionRing.injective E KE) (hx.trans (map_zero _).symm)
        exact x.property (Ideal.Quotient.eq_zero_iff_mem.mp hx'))
  have hresD : rResid.comp (algebraMap D V₁) =
      (algebraMap E KE).comp (Ideal.Quotient.mk P) := IsLocalization.lift_comp _
  have hresM : rResid.comp mV = kE.comp ((IsLocalRing.residue V).comp primeToV) := by
    apply IsLocalization.ringHom_ext prime.primeCompl
    rw [RingHom.comp_assoc, valuationSubringLocalizationMap_comp, ← RingHom.comp_assoc, hresD]
    ext x
    change algebraMap E KE (Ideal.Quotient.mk P (iD x)) =
      kE (IsLocalRing.residue V (cV x))
    have hx : Ideal.Quotient.mk P (iD x) = jE (cW x) := by
      simpa only [RingHom.comp_apply] using (DFunLike.congr_fun hjEcomp x).symm
    rw [hx]
    change algebraMap E KE (jE (cW x)) = kE ((cW x : IsLocalRing.ResidueField V))
    simpa only [kE, RingHom.comp_apply, ValuationSubring.algebraMap_apply] using
      (IsFractionRing.lift_algebraMap
        (A := W') (K := IsLocalRing.ResidueField V) (L := KE)
        (g := (algebraMap E KE).comp jE)
        ((IsFractionRing.injective E KE).comp hjE) (cW x)).symm
  have hresV : rResid.comp vLoc =
      kE.comp ((IsLocalRing.residue V).comp eV.toRingHom) := by
    rw [← RingHom.comp_assoc, hresM]
    rfl
  have hresE : rResid.comp dLoc = (algebraMap E KE).comp rE := by
    rw [← RingHom.comp_assoc, hresD]
    rfl
  let baseLoc := Spec.map (CommRingCat.ofHom dLoc) ≫ eC.square.base
  have hbaseLocV : Spec.map (CommRingCat.ofHom vLoc) ≫ qP.base = baseLoc := by
    calc
      _ = Spec.map (CommRingCat.ofHom vLoc) ≫
          Spec.map (CommRingCat.ofHom vMap) ≫ baseC := by rw [hbaseV]
      _ = Spec.map (CommRingCat.ofHom dLoc) ≫
          Spec.map (CommRingCat.ofHom eC.ringMap) ≫ baseC := by
        simpa only [Spec.map_comp, CommRingCat.ofHom_comp, Category.assoc] using
          (congrArg (fun r => Spec.map (CommRingCat.ofHom r) ≫ baseC) hvLoc)
      _ = baseLoc := by rw [← eC.base_comm]
  have hV₁mem : B.Contains (Spec (.of V₁)) :=
    spec_mem_of_injective B eC.square.field_mem V₁.subtype V₁.subtype_injective
  let TV₁ := siteObject B S hS hV₁mem baseLoc
  let dOver : TV₁ ⟶ siteObject B S hS eC.square.ring_mem eC.square.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom dLoc)))
  let vOver : TV₁ ⟶ siteObject B S hS qP.ring_mem qP.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom vLoc)))
      (by apply B.inclusion.map_injective; exact hbaseLocV)
  let aLoc : yoneda.obj TV₁ ⟶ X := yoneda.map dOver ≫ liftC.map
  let bLoc : yoneda.obj TV₁ ⟶ X := yoneda.map vOver ≫ qP.special ≫ fP
  have hkLocBase : Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K)) ≫ baseLoc =
      Spec.map (CommRingCat.ofHom (algebraMap eC.square.R eC.square.K)) ≫ eC.square.base := by
    dsimp only [baseLoc]
    rw [← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r) ≫ eC.square.base) hdLocFrac
  let KL := siteObject B S hS eC.square.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K)) ≫ baseLoc)
  let kLoc : KL ⟶ siteObject B S hS eC.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap eC.square.R eC.square.K)) ≫ eC.square.base) :=
    Over.homMk (ObjectProperty.homMk (𝟙 (Spec (.of eC.square.K))))
      (by
        apply B.inclusion.map_injective
        change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap eC.square.R eC.square.K)) ≫
          eC.square.base =
          Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K)) ≫ baseLoc
        simpa only [Category.id_comp] using hkLocBase.symm)
  let sLoc : KL ⟶ TV₁ := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K))))
  have hkLoc : sLoc ≫ dOver = kLoc ≫ specializationArrow eC.square := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K)) ≫
      Spec.map (CommRingCat.ofHom dLoc) = 𝟙 _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap eC.square.R eC.square.K))
    rw [Category.id_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hdLocFrac
  have hkLocV : sLoc ≫ vOver =
      kLoc ≫ eC.genericOver ≫ kC ≫ specializationArrow qP := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom (algebraMap V₁ eC.square.K)) ≫
      Spec.map (CommRingCat.ofHom vLoc) = 𝟙 _ ≫
        B.inclusion.map eC.genericOver.left ≫ 𝟙 _ ≫
          Spec.map (CommRingCat.ofHom (algebraMap qP.R qP.K))
    rw [eC.genericOver_left, Category.id_comp, Category.id_comp,
      ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hvLocFrac
  have hvLocOver : vOver ≫ vC = dOver ≫ eC.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom vLoc) ≫ Spec.map (CommRingCat.ofHom vMap) =
      Spec.map (CommRingCat.ofHom dLoc) ≫ B.inclusion.map eC.specialOver.left
    rw [eC.specialOver_left, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hvLoc
  let uLoc : yoneda.obj KL ⟶ U := yoneda.map kLoc ≫ yoneda.map eC.genericOver ≫ uC
  have haLoc : yoneda.map sLoc ≫ aLoc = uLoc ≫ h := by
    dsimp only [aLoc, uLoc]
    rw [← Category.assoc, ← yoneda.map_comp, hkLoc, Functor.map_comp,
      Category.assoc, liftC.generic_comm, eC.generic_comm]
    rfl
  have hbLoc : yoneda.map sLoc ≫ bLoc = uLoc ≫ h := by
    dsimp only [bLoc]
    rw [← Category.assoc, ← yoneda.map_comp, hkLocV]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Category.assoc, ← qP.comm]
    dsimp only [uLoc, uC]
    simp only [Category.assoc, pullback.condition]
  have habLoc : aLoc ≫ f = bLoc ≫ f := by
    dsimp only [aLoc, bLoc]
    rw [Category.assoc, liftC.special_comm, eC.special_comm]
    change yoneda.map dOver ≫ yoneda.map eC.specialOver ≫ yoneda.map cR₀ ≫ aR₀ = _
    rw [← Category.assoc, ← yoneda.map_comp, ← hvLocOver]
    simp only [Functor.map_comp, Category.assoc]
    have hvR' := congrArg (fun z => yoneda.map vOver ≫ yoneda.map z ≫ aR₀) hvR
    simpa only [Functor.map_comp, Category.assoc, hsP, ← hfP₀] using hvR'
  have habLoc' : aLoc = bLoc := eq_of_refinedValuative_uniqueness h f hunique
    hV₁mem eC.square.field_mem baseLoc aLoc bLoc uLoc haLoc hbLoc habLoc
  let wKE : K₀ →+* KE :=
    kE.comp ((IsLocalRing.ResidueField.mapEquiv eV).toRingHom.comp φP)
  have hwKE : wKE.comp kP = fieldE := rfl
  have hresP : (rResid.comp vLoc).comp rS = wKE.comp evP := by
    rw [hresV]
    apply RingHom.ext
    intro x
    change kE (IsLocalRing.residue V (eV (rS x))) =
      kE (IsLocalRing.ResidueField.mapEquiv eV (φP (evP x)))
    rw [show φP (evP x) = IsLocalRing.residue qP.R (rS x) from
      DFunLike.congr_fun hφPring x]
    exact congrArg kE (IsLocalRing.ResidueField.map_residue eV.toRingHom _).symm
  have hrEi : rE.comp eC.ringMap = jE.comp cW := hjEcomp.symm
  have hrER : (rE.comp eC.ringMap).comp rC = aE.comp rA₀ := by
    rw [hrEi, RingHom.comp_assoc, hrCW]
    rfl
  exact ⟨eE, nonempty_lift_of_dominatingExtension_of_quotient B S hS h f q R₀ hR₀ bR₀
    aR₀ lR₀ hlR₀ rA₀
    (specMap_preimage ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map lR₀))
    hK₀ bK₀ jW kP hkP hP₀ bP evP hevbase fP evArrow hevArrow hOriginalGeneric
    qP sP hsP rS (specMap_preimage sPS) qC rC rfl cR₀ rfl rfl eC liftC eE rE hrER
    V₁ hV₁mem dLoc vLoc rResid hresE wKE hwKE hresP baseLoc rfl hbaseLocV
    dOver rfl vOver rfl habLoc'⟩

/-- The refined valuative criterion makes `f` universally closed when the quasi-compact map `h`
has dense image. -/
@[stacks 089G "universally closed conclusion"]
public theorem universallyClosed_of_refinedValuativeCriterion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : AlgebraicGeometry.IsAlgebraicSpace B S hS U)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (h : U ⟶ X) (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (hh : AlgebraicGeometry.Space.IsQuasiCompact B S hS h)
    (hdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        pointTopology B S hS X
      DenseRange (pointsMap B S hS U h))
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    (hexists : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    UniversallyClosed B S hS f := by
  have hval : AlgebraicGeometry.Space.ValuativeCriterion.Existence f := by
    intro q₀
    obtain ⟨e₀, R₀, hR₀, bR₀, aR₀, lR₀, haR₀, hlR₀⟩ :=
      exists_dominatingExtension_lift_affine B S hS hY q₀
    suffices hval' : ∃ e : e₀.square.DominatingExtension, Nonempty e.square.Lift by
      obtain ⟨e, he⟩ := hval'
      exact ⟨dominatingExtensionTrans e₀ e, he⟩
    let q := e₀.square
    let T₀ := siteObject B S hS hR₀ bR₀
    let hT₀ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₀
    let X₀ := pullback f aR₀
    let hX₀ := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f aR₀ hX hT₀ hY
    let gen := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))
    let T_K := siteObject B S hS q.field_mem (gen ≫ q.base)
    let pK : FieldValuedPoint B S hS (yoneda.obj T_K) := {
      carrier := q.K
      field := q.field
      contained := q.field_mem
      toBase := gen ≫ q.base
      value := 𝟙 T_K }
    let g₀ : yoneda.obj T_K ⟶ X₀ :=
      pullback.lift q.generic (yoneda.map (specializationArrow q ≫ lR₀)) (by
        rw [Functor.map_comp, Category.assoc, hlR₀]
        exact q.comm)
    let pX₀ := FieldValuedPoint.map B S hS (yoneda.obj T_K) g₀ pK
    obtain ⟨W, a₀, haEtaleW, pW, jW, hpW, hvW⟩ :=
      exists_fieldValuedPoint_lift_to_atlas B S hS hX₀ pX₀
    let a : yoneda.obj W ⟶ X := a₀ ≫ pullback.fst f aR₀
    let wR₀ : W ⟶ T₀ := yoneda.preimage (a₀ ≫ pullback.snd f aR₀)
    have hwR₀ : yoneda.map wR₀ = a₀ ≫ pullback.snd f aR₀ :=
      yoneda.map_preimage _
    let t : Spec (.of pW.carrier) ⟶
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W :=
      (B.inclusion).map (yoneda.preimage (yonedaEquiv.symm pW.value)).left
    have hWsize : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W).size < B.cutoff :=
      W.left.2
    obtain ⟨hP, gP, hevP, hmapP, hflatP⟩ := exists_flat_mvPolynomial_chart
      B hWsize pW.contained t
    let TP := siteObject B S hS hP
      (gP ≫ (B.inclusion).map W.hom)
    let jP : TP ⟶ W := Over.homMk (ObjectProperty.homMk gP)
    let fP : yoneda.obj TP ⟶ X := yoneda.map jP ≫ a
    have hflatA : IsFlat B S hS a :=
      AlgebraicGeometry.Space.isFlat_comp B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hX₀ hX
        a₀ (pullback.fst f aR₀)
        (flat_of_etale_atlas B S hS X₀ hX₀ W a₀ haEtaleW)
        (isFlat_pullback_fst B S hS hX hY hT₀ f aR₀ haR₀)
    have hflatFP : IsFlat B S hS fP :=
      AlgebraicGeometry.Space.isFlat_comp B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS TP)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hX
        (yoneda.map jP) a (yoneda_flat B S hS jP hflatP) hflatA
    let bP₀ : TP ⟶ T₀ := jP ≫ wR₀
    have hfP₀ : fP ≫ f = yoneda.map bP₀ ≫ aR₀ := by
      dsimp [fP, a, bP₀]
      rw [Functor.map_comp, Category.assoc, hwR₀]
      simp only [Category.assoc, pullback.condition]
    let xP := t (IsLocalRing.closedPoint pW.carrier)
    let WS := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W
    let AP := WS.presheaf.stalk xP
    let evP : MvPolynomial pW.carrier AP →+* pW.carrier :=
      MvPolynomial.eval₂Hom (Scheme.stalkClosedPointTo t).hom (fun z : pW.carrier => z)
    let evSpec := Spec.map (CommRingCat.ofHom evP)
    have htbase : t ≫ (B.inclusion).map W.hom = pW.toBase := by
      change (B.inclusion).map (yoneda.preimage (yonedaEquiv.symm pW.value)).left ≫
        (B.inclusion).map W.hom = pW.toBase
      exact congrArg (B.inclusion).map (yoneda.preimage (yonedaEquiv.symm pW.value)).w
    have hmapPt : evSpec ≫ gP = t := hmapP
    have hevbase : evSpec ≫ gP ≫ (B.inclusion).map W.hom = pW.toBase := by
      rw [← Category.assoc, hmapPt, htbase]
    let evArrow : pW.siteObject ⟶ TP :=
      Over.homMk (ObjectProperty.homMk evSpec)
    let wArrow := yoneda.preimage (yonedaEquiv.symm pW.value)
    have hmapWArrow : yoneda.map wArrow = yonedaEquiv.symm pW.value := by
      simp [wArrow]
    have hwArrow : wArrow = pW.value := by
      calc
        wArrow = yonedaEquiv (yoneda.map wArrow) := by rw [yonedaEquiv_yoneda_map]
        _ = yonedaEquiv (yonedaEquiv.symm pW.value) := congrArg yonedaEquiv hmapWArrow
        _ = pW.value := Equiv.apply_symm_apply _ _
    have hArrowPW : evArrow ≫ jP = wArrow := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      exact hmapPt
    have hpX₀val : yonedaEquiv.symm pX₀.value = g₀ := Equiv.symm_apply_apply _ _
    have hgW₀ : yoneda.map jW ≫ g₀ = (yonedaEquiv.symm pW.value) ≫ a₀ := by
      have h₁ : yoneda.map jW ≫ g₀ =
          yonedaEquiv.symm (X₀.map jW.op pX₀.value) := by
        rw [yonedaEquiv_symm_map, hpX₀val]
        rfl
      have h₂ := congrArg yonedaEquiv.symm hvW
      have h₃ : yonedaEquiv.symm
          ((FieldValuedPoint.map B S hS (yoneda.obj W) a₀ pW).value) =
          yonedaEquiv.symm pW.value ≫ a₀ := by
        change yonedaEquiv.symm (a₀.app _ pW.value) =
          yonedaEquiv.symm pW.value ≫ a₀
        apply yonedaEquiv.injective
        simp only [Equiv.apply_symm_apply, yonedaEquiv_comp]
      exact h₁.trans (h₂.trans h₃)
    have hEvR₀ : evArrow ≫ bP₀ = jW ≫ specializationArrow q ≫ lR₀ := by
      apply yoneda.map_injective
      calc
        yoneda.map (evArrow ≫ bP₀) =
            (yonedaEquiv.symm pW.value) ≫ (a₀ ≫ pullback.snd f aR₀) := by
          dsimp [bP₀]
          rw [← Category.assoc, hArrowPW, Functor.map_comp, hmapWArrow, hwR₀]
        _ = yoneda.map jW ≫ g₀ ≫ pullback.snd f aR₀ :=
          congrArg (fun t => t ≫ pullback.snd f aR₀) hgW₀.symm
        _ = yoneda.map (jW ≫ specializationArrow q ≫ lR₀) := by
          have hg₀snd : g₀ ≫ pullback.snd f aR₀ =
              yoneda.map (specializationArrow q ≫ lR₀) := by
            simp only [g₀, pullback.lift_snd]
          calc
            _ = yoneda.map jW ≫ yoneda.map (specializationArrow q ≫ lR₀) :=
              congrArg (fun t => yoneda.map jW ≫ t) hg₀snd
            _ = yoneda.map (jW ≫ specializationArrow q ≫ lR₀) :=
              (yoneda.map_comp jW (specializationArrow q ≫ lR₀)).symm
    let kP : q.K →+* pW.carrier :=
      (Scheme.Spec.preimage ((B.inclusion).map jW.left)).unop.hom
    have hOriginalGeneric : yoneda.map evArrow ≫ fP = yoneda.map jW ≫ q.generic := by
      calc
        _ = (yonedaEquiv.symm pW.value) ≫ a₀ ≫ pullback.fst f aR₀ := by
          dsimp only [fP, a]
          rw [← Category.assoc, ← yoneda.map_comp, hArrowPW, hmapWArrow]
        _ = yoneda.map jW ≫ g₀ ≫ pullback.fst f aR₀ := by
          calc
            _ = (yoneda.map jW ≫ g₀) ≫ pullback.fst f aR₀ :=
              congrArg (fun t => t ≫ pullback.fst f aR₀) hgW₀.symm
            _ = _ := Category.assoc _ _ _
        _ = _ := by
          have hg₀fst : g₀ ≫ pullback.fst f aR₀ = q.generic :=
            pullback.lift_fst _ _ _
          exact congrArg (fun t => yoneda.map jW ≫ t) hg₀fst
    have hmem : fP.app (Opposite.op pW.siteObject) evArrow ∈
        (schemeTheoreticImageSubfunctor B S hS h).obj (Opposite.op pW.siteObject) := by
      change a.app (Opposite.op pW.siteObject)
        ((yoneda.map jP).app (Opposite.op pW.siteObject) evArrow) ∈ _
      rw [show (yoneda.map jP).app (Opposite.op pW.siteObject) evArrow = pW.value from
        hArrowPW.trans hwArrow]
      exact fieldValuedPoint_value_mem_schemeTheoreticImageSubfunctor
        B S hS hX h hdense a pW
    exact exists_dominatingExtension_lift_of_flat_chart B S hS hU hX h f hh hunique hexists
      q R₀ hR₀ bR₀ aR₀ lR₀ hlR₀ pW.contained pW.toBase hP
      (gP ≫ (B.inclusion).map W.hom) evP hevP hevbase fP hflatFP bP₀ hfP₀
      evArrow rfl jW kP ((specMap_preimage ((B.inclusion).map jW.left)).symm)
      hOriginalGeneric hEvR₀ hmem
  exact AlgebraicGeometry.Space.universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence
    hX hY f hf hval

/-- With quasi-separatedness, the same refined valuative criterion makes `f` separated. -/
@[stacks 089G "separated conclusion"]
public theorem isSeparated_of_refinedValuativeCriterion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : AlgebraicGeometry.IsAlgebraicSpace B S hS U)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (h : U ⟶ X) (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f)
    (hh : AlgebraicGeometry.Space.IsQuasiCompact B S hS h)
    (hqs : AlgebraicGeometry.Space.IsQuasiSeparated B S hS f)
    (hdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        pointTopology B S hS X
      DenseRange (pointsMap B S hS U h))
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    (hexists : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    AlgebraicGeometry.Space.IsSeparated B S hS f := by
  let hXX := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hDiagUC : UniversallyClosed B S hS
      (pullback.diagonal f) :=
    universallyClosed_of_refinedValuativeCriterion B S hS hU hX hXX h
      (pullback.diagonal f) hqs hh hdense
      (diagonal_refined_valuative_uniqueness B S hS h f hunique)
      (diagonal_refined_valuative_existence B S hS h f hunique hexists)
  have htfae := AlgebraicGeometry.Space.isSeparated_tfae_diagonal
    B S hS f hX hY
  exact (htfae.out 2 1).mp hDiagUC

end AlgebraicGeometry.Space

end
