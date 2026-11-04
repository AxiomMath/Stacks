module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.PushDownSolution
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# The Noetherian valuative criteria over complete discrete valuation rings

In the Noetherian valuative criteria for separatedness and for properness of a morphism of
algebraic spaces it suffices to consider complete discrete valuation rings: for separatedness, at
most one dotted arrow in every valuative square over a complete discrete valuation ring; for
properness, for every valuative square over a complete discrete valuation ring `A` with fraction
field `K`, an extension `A ⊂ A'` of complete discrete valuation rings, inducing `K ⊂ K'`, over
which there is exactly one dotted arrow. More generally any class of discrete valuation rings will
do in which every discrete valuation ring has an extension, for instance the complete discrete
valuation rings with algebraically closed residue field.

Completeness of a discrete valuation ring is completeness for its maximal-ideal-adic topology, and
an extension of discrete valuation rings is an injective local homomorphism,
`IsDiscreteValuationRing.IsExtension`. The spectra of the valuation rings occurring are objects of
the chosen big site.

## Main definitions

* `AlgebraicGeometry.Space.IsCofinalDiscreteValuationRingClass`: a class of discrete valuation
  rings in which every discrete valuation ring (with spectrum in the big site) has an extension.

## Main results

* `AlgebraicGeometry.Space.isSeparated_iff_discreteValuativeUniqueness_of_isCofinal` and
  `AlgebraicGeometry.Space.isProper_iff_discreteValuativeCriterion_of_isCofinal`: the
  Noetherian valuative criteria for separatedness and properness over an arbitrary cofinal class.
* `AlgebraicGeometry.Space.isSeparated_iff_completeDiscreteValuativeUniqueness` and
  `AlgebraicGeometry.Space.isProper_iff_completeDiscreteValuativeCriterion`: the criteria over
  complete discrete valuation rings.
* `AlgebraicGeometry.Space.isSeparated_iff_completeAlgClosedDiscreteValuativeUniqueness` and
  `AlgebraicGeometry.Space.isProper_iff_completeAlgClosedDiscreteValuativeCriterion`: the criteria
  over complete discrete valuation rings with algebraically closed residue field.
* `AlgebraicGeometry.Space.isCofinalDiscreteValuationRingClass_isAdicComplete` and
  `AlgebraicGeometry.Space.isCofinalDiscreteValuationRingClass_isAdicComplete_isAlgClosed`: those
  two classes are cofinal.

## References

* [Stacks Project, Tag 0ARL](https://stacks.math.columbia.edu/tag/0ARL)
* [Stacks Project, Tag 0ARJ](https://stacks.math.columbia.edu/tag/0ARJ)
* [Stacks Project, Tag 0ARK](https://stacks.math.columbia.edu/tag/0ARK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A class `P` of discrete valuation rings is cofinal for the big site `B` if every discrete
valuation ring `A` whose spectrum lies in `B` has an extension `A ⊂ A'` of discrete valuation rings
with `A'` in the class, the spectrum of `A'` again lying in `B`. -/
def IsCofinalDiscreteValuationRingClass (B : BigFppfSite.{u})
    (P : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], Prop) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A],
    B.Contains (Spec (.of A)) →
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A A'), IsDiscreteValuationRing.IsExtension A A' ∧
        B.Contains (Spec (.of A')) ∧ P A'

/-- An extension of discrete valuation rings `q.R ⊂ C`, with the spectrum of `C` in the big site,
gives a dominating extension of the valuative square `q`, with valuation ring `C` and a fraction
field `L` of it. -/
private theorem ValuativeSquare.exists_dominatingExtension_of_isExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (q : ValuativeSquare f)
    [IsDiscreteValuationRing q.R]
    (P : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], Prop)
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra q.R C]
    [IsDiscreteValuationRing.IsExtension q.R C] (hC : B.Contains (Spec (.of C))) (hPC : P C)
    (L : Type u) [Field L] [Algebra C L] [IsFractionRing C L] :
    ∃ e : q.DominatingExtension, ∃ _ : IsDiscreteValuationRing e.square.R, P e.square.R := by
  let g : q.R →+* L := (algebraMap C L).comp (algebraMap q.R C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective q.R C)
  let j : q.K →+* L := IsFractionRing.lift (A := q.R) (K := q.K) (g := g) hg
  have hij : g = j.comp (algebraMap q.R q.K) :=
    RingHom.ext fun r ↦ (IsFractionRing.lift_algebraMap hg r).symm
  exact ⟨dominatingExtensionOfRingHom q hC (spec_fractionRing_mem B hC) (algebraMap q.R C) j
    inferInstance hij, inferInstanceAs (IsDiscreteValuationRing C), hPC⟩

/-- For a cofinal class `P`, a valuative square over a discrete valuation ring has a dominating
extension whose valuation ring is a discrete valuation ring in `P`. -/
theorem ValuativeSquare.exists_dominatingExtension_of_isCofinal
    {P : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], Prop}
    (cofinal : IsCofinalDiscreteValuationRingClass B P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (q : ValuativeSquare f)
    (hq : IsDiscreteValuationRing q.R) :
    ∃ e : q.DominatingExtension, ∃ _ : IsDiscreteValuationRing e.square.R, P e.square.R := by
  obtain ⟨C, _, _, _, _, _, hC, hPC⟩ := cofinal q.R q.ring_mem
  exact q.exists_dominatingExtension_of_isExtension P C hC hPC (FractionRing C)

/-- A ring `C` of cardinality at most `max ℵ₀ #A ^ ℵ₀` has its spectrum in the big site `B` as soon
as the spectrum of `A` is. -/
private theorem contains_spec_of_card_le {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (C : Type u) [CommRing C]
    (h : Cardinal.mk C ≤ max Cardinal.aleph0 (Cardinal.mk A) ^ Cardinal.aleph0) :
    B.Contains (Spec (.of C)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hA (by
    rwa [Scheme.size_Spec])

/-- An injective local ring homomorphism `A → C` of discrete valuation rings is an extension. -/
private theorem isExtension_of_injective_of_isLocalHom (A C : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C]
    (hinj : Function.Injective (algebraMap A C))
    (hloc : IsLocalHom (algebraMap A C)) :
    IsDiscreteValuationRing.IsExtension A C :=
  { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A C).mpr hinj
    toIsLocalHom := hloc }

/-- The complete discrete valuation rings form a cofinal class. -/
theorem isCofinalDiscreteValuationRingClass_isAdicComplete (B : BigFppfSite.{u}) :
    IsCofinalDiscreteValuationRingClass B
      (fun A _ _ _ => IsAdicComplete (IsLocalRing.maximalIdeal A) A) := by
  intro A _ _ _ hA
  obtain ⟨hCdom, hCdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := A)).mp ⟨inferInstance, ‹_›⟩
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have hCmem := contains_spec_of_card_le hA C ((cardinal_mk_adicCompletion_le _).trans
    (Cardinal.power_le_power_right (le_max_right _ _)))
  have hext := isExtension_of_injective_of_isLocalHom A C
    (AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A) inferInstance
  exact ⟨C, inferInstance, hCdom, hCdvr, inferInstance, hext, hCmem,
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal C) C)⟩

/-- The complete discrete valuation rings with algebraically closed residue field form a cofinal
class. -/
@[ega "IV 11.8.2" "(i)", ega "IV 15.7.7", sga "3 XV 3.3" "partial"]
theorem isCofinalDiscreteValuationRingClass_isAdicComplete_isAlgClosed (B : BigFppfSite.{u}) :
    IsCofinalDiscreteValuationRingClass B (fun A _ _ _ =>
      IsAdicComplete (IsLocalRing.maximalIdeal A) A ∧
        IsAlgClosed (IsLocalRing.ResidueField A)) := by
  intro A _ _ _ hA
  obtain ⟨C, _, hCdom, hCdvr, hCc, hCres, ⟨φ, hφloc, hφinj⟩, hcard⟩ :=
    exists_isAdicComplete_isAlgClosed_residueField_extension A
  let : Algebra A C := φ.toAlgebra
  exact ⟨C, inferInstance, hCdom, hCdvr, inferInstance,
    isExtension_of_injective_of_isLocalHom A C hφinj hφloc, contains_spec_of_card_le hA C hcard,
    hCc, hCres⟩

/-- A valuative square whose valuation ring is a discrete valuation ring has a dominating
extension whose valuation ring is a complete discrete valuation ring. -/
@[ega "IV 15.7.7" "partial"]
theorem ValuativeSquare.exists_completion_dominatingExtension
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (q : ValuativeSquare f)
    (hq : IsDiscreteValuationRing q.R) :
    ∃ e : q.DominatingExtension, IsDiscreteValuationRing e.square.R ∧
      IsAdicComplete (IsLocalRing.maximalIdeal e.square.R) e.square.R :=
  (q.exists_dominatingExtension_of_isCofinal (isCofinalDiscreteValuationRingClass_isAdicComplete B)
    hq).imp fun _ ⟨he, hec⟩ ↦ ⟨he, hec⟩

variable (B S hS)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is locally of finite type and quasi-separated. Let `P` be a class of discrete valuation
rings such that every discrete valuation ring has an extension in the class. If every valuative
square for `f` whose valuation ring is a discrete valuation ring in the class admits at most one
dotted arrow, then `f` is separated; and conversely. -/
@[stacks 0ARL "Lemma 69.19.1 (0ARJ) for any class of discrete valuation rings in which every
discrete valuation ring has an extension"]
theorem isSeparated_iff_discreteValuativeUniqueness_of_isCofinal
    {P : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], Prop}
    (cofinal : IsCofinalDiscreteValuationRingClass B P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsLocallyOfFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsSeparated B S hS f ↔
      ∀ q : ValuativeSquare f, ∀ _ : IsDiscreteValuationRing q.R, P q.R → Subsingleton q.Lift := by
  refine ⟨fun sepf q _ _ ↦ valuativeCriterion_uniqueness_of_isSeparated f sepf q,
    fun uniq ↦ ?_⟩
  refine isSeparated_of_isQuasiSeparated_of_discreteValuativeUniqueness B S hS algX algY f noethY
    finf qsepf fun q hq ↦ ?_
  obtain ⟨e, he, hPe⟩ := q.exists_dominatingExtension_of_isCofinal cofinal hq
  exact subsingleton_lift_of_dominatingExtension algX q e (uniq e.square he hPe)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is of finite type and quasi-separated. Let `P` be a class of discrete valuation rings
such that every discrete valuation ring has an extension in the class. If for every valuative
square for `f` whose valuation ring `A` is a discrete valuation ring in the class there is an
extension `A ⊂ A'` of discrete valuation rings in the class, inducing an extension of fraction
fields, over which the square has exactly one dotted arrow `Spec A' ⟶ X`, then `f` is proper; and
conversely. -/
@[stacks 0ARL "Lemma 69.19.2 (0ARK) for any class of discrete valuation rings in which every
discrete valuation ring has an extension"]
theorem isProper_iff_discreteValuativeCriterion_of_isCofinal
    {P : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], Prop}
    (cofinal : IsCofinalDiscreteValuationRingClass B P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔ ∀ q : ValuativeSquare f, ∀ _ : IsDiscreteValuationRing q.R, P q.R →
      ∃ e : q.DominatingExtension, ∃ _ : IsDiscreteValuationRing e.square.R, P e.square.R ∧
        Nonempty e.square.Lift ∧ Subsingleton e.square.Lift := by
  refine ⟨fun propf q hq hPq ↦ ⟨q.idDominatingExtension, hq, hPq,
    (isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated algX algY f finf
      qsepf).mp propf q⟩, fun liftExt ↦ ?_⟩
  have uniq : ∀ q : ValuativeSquare f, ∀ _ : IsDiscreteValuationRing q.R, P q.R →
      Subsingleton q.Lift := fun q hq hPq ↦
    let ⟨e, _, _, _, he⟩ := liftExt q hq hPq
    subsingleton_lift_of_dominatingExtension algX q e he
  have sepf : IsSeparated B S hS f :=
    (isSeparated_iff_discreteValuativeUniqueness_of_isCofinal B S hS cofinal algX algY f noethY
      finf.1 qsepf).mpr uniq
  refine isProper_of_isQuasiSeparated_of_discreteValuativeCriterion B S hS algX algY f noethY finf
    qsepf fun q hq ↦ ?_
  obtain ⟨e, he, hPe⟩ := q.exists_dominatingExtension_of_isCofinal cofinal hq
  obtain ⟨e', -, -, hl, -⟩ := liftExt e.square he hPe
  exact ⟨exists_lift_of_dominatingExtension algX algY sepf q e
      (exists_lift_of_dominatingExtension algX algY sepf e.square e' hl),
    subsingleton_lift_of_dominatingExtension algX q e (uniq e.square he hPe)⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is locally of finite type and quasi-separated. If every valuative square for `f` whose
valuation ring is a complete discrete valuation ring admits at most one dotted arrow, then `f` is
separated; and conversely. -/
@[stacks 0ARL "Lemma 69.19.1 (0ARJ) with complete discrete valuation rings"]
theorem isSeparated_iff_completeDiscreteValuativeUniqueness
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsLocallyOfFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsSeparated B S hS f ↔ ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R → Subsingleton q.Lift :=
  isSeparated_iff_discreteValuativeUniqueness_of_isCofinal B S hS
    (isCofinalDiscreteValuationRingClass_isAdicComplete B) algX algY f noethY finf qsepf

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is of finite type and quasi-separated. If for every valuative square for `f` whose
valuation ring `A` is a complete discrete valuation ring, with fraction field `K`, there is an
extension `A ⊂ A'` of complete discrete valuation rings inducing an extension `K ⊂ K'` of fraction
fields over which the square has exactly one dotted arrow `Spec A' ⟶ X`, then `f` is proper; and
conversely. -/
@[stacks 0ARL "Lemma 69.19.2 (0ARK) with complete discrete valuation rings"]
theorem isProper_iff_completeDiscreteValuativeCriterion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔ ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R →
      ∃ e : q.DominatingExtension, IsDiscreteValuationRing e.square.R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal e.square.R) e.square.R ∧
        Nonempty e.square.Lift ∧ Subsingleton e.square.Lift := by
  rw [isProper_iff_discreteValuativeCriterion_of_isCofinal B S hS
    (isCofinalDiscreteValuationRingClass_isAdicComplete B) algX algY f noethY finf qsepf]
  refine ⟨fun h q hq hqc ↦ ?_, fun h q hq hqc ↦ ?_⟩ <;>
    obtain ⟨e, he, hec, hl⟩ := h q hq hqc <;> exact ⟨e, he, hec, hl⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is locally of finite type and quasi-separated. If every valuative square for `f` whose
valuation ring is a complete discrete valuation ring with algebraically closed residue field admits
at most one dotted arrow, then `f` is separated; and conversely. -/
@[stacks 0ARL "Lemma 69.19.1 (0ARJ) with complete discrete valuation rings with algebraically
closed residue field"]
theorem isSeparated_iff_completeAlgClosedDiscreteValuativeUniqueness
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsLocallyOfFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsSeparated B S hS f ↔ ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R →
      IsAlgClosed (IsLocalRing.ResidueField q.R) → Subsingleton q.Lift := by
  rw [isSeparated_iff_discreteValuativeUniqueness_of_isCofinal B S hS
    (isCofinalDiscreteValuationRingClass_isAdicComplete_isAlgClosed B) algX algY f noethY finf
    qsepf]
  exact ⟨fun h q hq hqc hqa ↦ h q hq ⟨hqc, hqa⟩, fun h q hq hP ↦ h q hq hP.1 hP.2⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y` locally Noetherian, and
assume `f` is of finite type and quasi-separated. If for every valuative square for `f` whose
valuation ring `A` is a complete discrete valuation ring with algebraically closed residue field
there is an extension `A ⊂ A'` of such rings, inducing an extension of fraction fields, over which
the square has exactly one dotted arrow `Spec A' ⟶ X`, then `f` is proper; and conversely. -/
@[stacks 0ARL "Lemma 69.19.2 (0ARK) with complete discrete valuation rings with algebraically
closed residue field"]
theorem isProper_iff_completeAlgClosedDiscreteValuativeCriterion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (noethY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (finf : IsFiniteType B S hS f) (qsepf : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔ ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      IsAdicComplete (IsLocalRing.maximalIdeal q.R) q.R →
      IsAlgClosed (IsLocalRing.ResidueField q.R) →
      ∃ e : q.DominatingExtension, IsDiscreteValuationRing e.square.R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal e.square.R) e.square.R ∧
        IsAlgClosed (IsLocalRing.ResidueField e.square.R) ∧
        Nonempty e.square.Lift ∧ Subsingleton e.square.Lift := by
  rw [isProper_iff_discreteValuativeCriterion_of_isCofinal B S hS
    (isCofinalDiscreteValuationRingClass_isAdicComplete_isAlgClosed B) algX algY f noethY finf
    qsepf]
  refine ⟨fun h q hq hqc hqa ↦ ?_, fun h q hq hP ↦ ?_⟩
  · obtain ⟨e, he, ⟨hec, hea⟩, hl⟩ := h q hq ⟨hqc, hqa⟩
    exact ⟨e, he, hec, hea, hl⟩
  · obtain ⟨e, he, hec, hea, hl⟩ := h q hq hP.1 hP.2
    exact ⟨e, he, ⟨hec, hea⟩, hl⟩

end AlgebraicGeometry.Space

end
