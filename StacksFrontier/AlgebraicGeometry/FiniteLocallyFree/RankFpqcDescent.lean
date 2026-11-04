module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
import StacksCore.Tactic.EgaSgaAttribute
/-!
# Finite local freeness of a given rank satisfies fpqc descent

Being finite locally free of rank `d` descends along a surjective flat quasi-compact morphism: if
the base change of `g` along such a morphism is finite locally free of rank `d`, then so is `g`.
This is the one input, besides Zariski locality on the target and stability under base change, that
the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` needs.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_baseChange`: being finite locally free of rank `d` descends
  along a faithfully flat base change.
* `RingHom.FiniteLocallyFreeOfRank`: the property of a ring homomorphism that its target is a
  finite locally free module of rank `d` over its source.
* `RingHom.FiniteLocallyFreeOfRank.codescendsAlong_faithfullyFlat`: the ring-homomorphism form of
  the module descent.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  being finite locally free of rank `d` satisfies fpqc descent.

## Implementation notes

The module-level descent runs through the Fitting ideals rather than through a trivialising cover,
because no cover has to be transported that way. By Tag 07ZD a finite module `M` is finite locally
free of rank `d` exactly when its `(d-1)`st Fitting ideal vanishes and its `d`th Fitting ideal is
the unit ideal (`finiteLocallyFreeOfRank_fittingIdeal_tfae`), and by Tag 07ZA the Fitting ideals of
a base change are the extensions of the Fitting ideals
(`fittingIdeal_basic_properties`). A faithfully flat extension reflects both the zero ideal — its
structure map is injective — and the unit ideal, by
`IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat`. Finiteness of `M` itself is recovered
from finiteness of the base change by `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.

The passage from modules to schemes is Mathlib's
`AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`, which reduces the claim
to a surjective flat morphism of affine schemes and an arbitrary target `Y`, together with
`AlgebraicGeometry.of_pullback_fst_Spec_of_codescendsAlong`, which performs the identification of
the global sections of a fibre product of affine schemes with a tensor product. The target `Y` is
affine because the base change of `g` is affine and affineness descends (Tag 02L5), so `Y` may be
replaced by the spectrum of its global functions.

The stability and locality facts about surjective flat morphisms that the descent argument needs
are the shared re-packagings in `StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing`; they are
stated there because instance synthesis cannot solve for the ring-homomorphism parameter of
`AlgebraicGeometry.HasRingHomProperty`, nor match a morphism property appearing as a factor of an
infimum, without reducibility settings that this development does not use.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TensorProduct Stacks.Descent

universe u v w

/-! ### Faithfully flat descent for modules -/

/-- A faithfully flat extension reflects the zero ideal: its structure map is injective, so an
ideal whose extension vanishes vanishes. -/
private lemma eq_bot_of_map_eq_bot {R : Type u} [CommRing R] (S : Type w) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] {I : Ideal R}
    (h : Ideal.map (algebraMap R S) I = ⊥) : I = ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp h

/-- A faithfully flat extension reflects the unit ideal. -/
private lemma eq_top_of_map_eq_top {R : Type u} [CommRing R] (S : Type w) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] {I : Ideal R}
    (h : Ideal.map (algebraMap R S) I = ⊤) : I = ⊤ := by
  have key := IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat R R
    (IsBaseChange.linearMap R S) I
  simp only [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
    Submodule.restrictScalars_self, ne_eq, not_iff_not] at key
  exact key.mp h

/-- Being finite locally free of rank `d` descends along a faithfully flat base change: if
`S ⊗[R] M` is a finite locally free `S`-module of rank `d` and `S` is a faithfully flat
`R`-algebra, then `M` is a finite locally free `R`-module of rank `d`. -/
@[ega "IV 2.5.2" "(iv), special case",
  sga "1 VIII 1.11" "special case",
  sga "4½ Arcata 1.4.2" "more general"]
theorem Module.IsFiniteLocallyFreeOfRank.of_baseChange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (S : Type w) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank S (TensorProduct R S M) d) :
    Module.IsFiniteLocallyFreeOfRank R M d := by
  have hfinS : Module.Finite S (TensorProduct R S M) := h.finite
  have hfin : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨hprev, htop⟩ := (finiteLocallyFreeOfRank_fittingIdeal_tfae
    (R := S) (M := TensorProduct R S M) d).out 1 2 |>.mp h
  have hbc (k : ℕ) : fittingIdeal (R := S) (M := TensorProduct R S M) (k : ℤ) =
      Ideal.map (algebraMap R S) (fittingIdeal (R := R) (M := M) (k : ℤ)) :=
    (fittingIdeal_basic_properties.{u, v, v, w} (R := R) (M := M)).2.2.1 S k
  refine ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := R) (M := M) d).out 2 1).mp
    (And.intro ?_ (eq_top_of_map_eq_top S (by rwa [hbc d] at htop)))
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [fittingIdeal]
  · have hindex : (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) := by omega
    rw [hindex] at hprev ⊢
    exact eq_bot_of_map_eq_bot S (by rwa [hbc (d - 1)] at hprev)

/-! ### The ring-homomorphism property -/

/-- A ring homomorphism `φ : R →+* S` is *finite locally free of rank `d`* if `S` is a finite
locally free module of rank `d` over `R` for the algebra structure given by `φ`. -/
def RingHom.FiniteLocallyFreeOfRank (d : ℕ) {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  letI : Algebra R S := φ.toAlgebra
  Module.IsFiniteLocallyFreeOfRank R S d

/-- For the structure map of an algebra, being finite locally free of rank `d` as a ring
homomorphism is being finite locally free of rank `d` as a module. -/
theorem RingHom.finiteLocallyFreeOfRank_algebraMap_iff (d : ℕ) {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] :
    RingHom.FiniteLocallyFreeOfRank d (algebraMap R S) ↔
      Module.IsFiniteLocallyFreeOfRank R S d := by
  rw [RingHom.FiniteLocallyFreeOfRank, toAlgebra_algebraMap]

/-- Being finite locally free of rank `d` codescends along faithfully flat ring homomorphisms. -/
theorem RingHom.FiniteLocallyFreeOfRank.codescendsAlong_faithfullyFlat (d : ℕ) :
    RingHom.CodescendsAlong (RingHom.FiniteLocallyFreeOfRank.{u} d) RingHom.FaithfullyFlat := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hff hP
  have _ : Module.FaithfullyFlat R R' := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  exact (RingHom.finiteLocallyFreeOfRank_algebraMap_iff d).mpr
    (Module.IsFiniteLocallyFreeOfRank.of_baseChange R'
      (.of_linearEquiv
        (Algebra.IsPushout.symm ‹Algebra.IsPushout R S R' S'›).equiv.symm.toLinearEquiv
        ((RingHom.finiteLocallyFreeOfRank_algebraMap_iff d).mp hP)))

namespace Stacks.Morphisms

/-! ### Descent for morphisms of schemes -/

/-- A surjective flat morphism of affine schemes has faithfully flat global sections. -/
private lemma faithfullyFlat_of_surjective_inf_flat {A B : CommRingCat.{u}} {ψ : A ⟶ B}
    (h : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) (Spec.map ψ)) :
    RingHom.FaithfullyFlat ψ.hom := by
  obtain ⟨hs, hfl⟩ := h
  have _ : Surjective (Spec.map ψ) := hs
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨?_, (Spec.map ψ).surjective⟩
  rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hfl

/-- A morphism of affine schemes is finite locally free of rank `d` exactly when the ring
homomorphism inducing it is. -/
private lemma isFiniteLocallyFreeOfRank_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (d : ℕ) :
    IsFiniteLocallyFreeOfRank (Spec.map φ) d ↔ RingHom.FiniteLocallyFreeOfRank d φ.hom := by
  let algG : Algebra ↑R ↑Γ(Spec S, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop).hom.toAlgebra
  let algS : Algebra ↑R ↑S := φ.hom.toAlgebra
  have hcomp : (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso S).hom = φ := by
    simp
  let e : ↑Γ(Spec S, ⊤) ≃ₐ[↑R] ↑S :=
    AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv)
      fun r ↦ congrArg (fun ψ : R ⟶ S ↦ ψ.hom r) hcomp
  rw [isFiniteLocallyFreeOfRank_iff, and_iff_right (inferInstance : IsAffineHom (Spec.map φ)),
    sheafOfModules_isFiniteLocallyFreeOfRank_iff_module (Spec.map φ) d]
  exact ⟨.of_linearEquiv e.toLinearEquiv, .of_linearEquiv e.symm.toLinearEquiv⟩

/-- The descent step over an affine base: if the base change of `g : Y ⟶ Spec R` along a
surjective flat morphism `Spec S ⟶ Spec R` is finite locally free of rank `d`, then so is `g`. -/
@[sga "1 VIII 5.7" "special case"]
private lemma isFiniteLocallyFreeOfRank_of_pullback_fst (d : ℕ) {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (φ : R ⟶ S) (g : Y ⟶ Spec R)
    (hφ : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) (Spec.map φ))
    (hf : IsFiniteLocallyFreeOfRank.property.{u} d (pullback.fst (Spec.map φ) g)) :
    IsFiniteLocallyFreeOfRank.property.{u} d g := by
  have := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have hYaff : IsAffine Y := by
    have _ : IsAffineHom g := MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨hφ, inferInstance⟩
      ((IsFiniteLocallyFreeOfRank.property_iff _ d).mp hf).toIsAffineHom
    exact isAffine_of_isAffineHom g
  wlog hY : ∃ T, Y = Spec T generalizing Y
  · rw [← (IsFiniteLocallyFreeOfRank.property.{u} d).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.inv (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, (IsFiniteLocallyFreeOfRank.property.{u} d).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  exact of_pullback_fst_Spec_of_codescendsAlong _ _
    (RingHom.FiniteLocallyFreeOfRank.codescendsAlong_faithfullyFlat d)
    (fun h ↦ faithfullyFlat_of_surjective_inf_flat h)
    (fun {_ _ ψ} ↦ isFiniteLocallyFreeOfRank_SpecMap_iff ψ d) hφ hf

/-- Being finite locally free of rank `d` satisfies fpqc descent: if the base change of `g` along
a surjective flat quasi-compact morphism is finite locally free of rank `d`, then so is `g`. -/
@[sga "1 VIII 5.7" "special case"]
instance isFiniteLocallyFreeOfRank_descendsAlong_surjective_inf_flat_inf_quasiCompact (d : ℕ) :
    MorphismProperty.DescendsAlong (IsFiniteLocallyFreeOfRank.property.{u} d)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isStableUnderBaseChange_surjective_inf_flat.{u}
  have := isStableUnderComposition_surjective_inf_flat.{u}
  have := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  exact IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
    (IsFiniteLocallyFreeOfRank.property.{u} d) (@Surjective ⊓ @Flat)
    isLocalIso_inf_surjective_le_surjective_inf_flat
    fun φ g hφ hf ↦ isFiniteLocallyFreeOfRank_of_pullback_fst d φ g hφ hf

end Stacks.Morphisms

end
