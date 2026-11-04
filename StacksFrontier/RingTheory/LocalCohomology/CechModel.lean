module

public import StacksFrontier.RingTheory.Cech.Cohomology
public import StacksFrontier.RingTheory.Cech.Extended
public import StacksFrontier.RingTheory.LocalCohomology.CechModel.LocalObjects
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.FiniteCohomologicalDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The Čech model of local cohomology

Let `A` be a commutative ring, let `f₁, …, f_r ∈ A`, let `I = (f₁, …, f_r)` and let `M` be an
`A`-module. Local cohomology `RΓ_{V(I)}` is defined in
`StacksFrontier/RingTheory/Dualizing/PowerTorsionComparison/LocalCohomologyFunctor.lean` as the right
adjoint of the inclusion of the complexes with `I`-power-torsion cohomology, so its values are
only accessible through that universal property. This file identifies the value at a module with
the explicit complex of Stacks 0A6R: the extended alternating Čech complex
$$ M \longrightarrow \bigoplus_{i} M_{f_i} \longrightarrow
   \bigoplus_{i < j} M_{f_i f_j} \longrightarrow \cdots \longrightarrow M_{f_1 \cdots f_r} $$
in degrees `0, …, r`, which is the complex built in `StacksFrontier/RingTheory/Cech/`.

Both halves of the Stacks argument are available. The cohomology of the Čech complex is
`I`-power torsion — this is the content of Tag 0G6K, proved in
`StacksFrontier/RingTheory/Cech/Cohomology.lean` — so the Čech complex is an object of
`D_{I^∞-torsion}(A)`. And the augmentation onto `M` in degree zero is universal among morphisms
from such objects: the remaining terms of the complex are finite direct sums of localizations
`M_{f_{i_0} \cdots f_{i_p}}` with `p ≥ 0`, on each of which some `f_i` acts invertibly, and such
a module admits no nonzero morphism from a complex killed by the derived localization at that
`f_i`. Stupid-filtering the complex propagates this from its terms to the complex itself. The
identification then follows from the uniqueness of a coreflection, which is
`Stacks.LocalCohomology.nonempty_localCohomology_iso_coreflection`.

Two consequences are recorded: the local cohomology modules `H^i_{V(I)}(M)` are the cohomology
modules of the Čech complex, and they vanish outside the degrees `0, …, r`.

## Main definitions

* `Stacks.LocalCohomology.extendedCechComplex` — the extended alternating Čech complex in
  integer degrees.
* `Stacks.LocalCohomology.extendedCechObject` — the corresponding object of `D(A)`.
* `Stacks.LocalCohomology.extendedCechAugmentation` — the augmentation onto `M` in degree zero.

## Main results

* `Stacks.LocalCohomology.derivedPowerTorsionProperty_extendedCechObject` — the Čech object has
  `I`-power-torsion cohomology.
* `Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom` — the augmentation is
  universal among morphisms from objects with `I`-power-torsion cohomology.
* `Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject` — **the
  identification** `RΓ_{V(I)}(M) ≅ C^•(f₁, …, f_r; M)`.
* `Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology` — the local
  cohomology modules are the cohomology modules of the Čech complex.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_outside_range` — local cohomology of
  a module vanishes outside the degrees `0, …, r`.

## Implementation notes

The universal property is proved through the right orthogonal of the class of torsion objects,
which is a triangulated subcategory of `D(A)`; the input about the terms of the complex is
`Stacks.LocalCohomology.subsingleton_hom_singleFunctor_directSum`, and the stupid filtration is
`Stacks.LocalCohomology.bijective_comp_toSingle`. Nothing here needs the derived tensor product.

Two things asserted by Tag 0A6R are *not* proved here. The identification is obtained from the
uniqueness of a coreflection, so it is produced as a `Nonempty` and is not natural in `M`; and
the value of `RΓ_{V(I)}` is identified only at an object concentrated in degree zero, not at an
arbitrary object of `D(A)`, which in the source is the statement that `RΓ_{V(I)}` is the derived
tensor product with the Čech complex. Both are supplied elsewhere, by the same two inputs applied
to the derived tensor product rather than to a fixed module:
`Stacks.LocalCohomology.CechFormula.localCohomologyCechIso` is the natural isomorphism
`RΓ_Z ≅ C(f) ⊗^L_A -` of functors on `D(A)`, and it carries the `@[stacks 0A6R]` attribute for
that half of the tag.

In particular the commutation `H^i_{V(I)}(\bigoplus_J M_j) = \bigoplus_J H^i_{V(I)}(M_j)` needed
by the induction in Tag 0DX7 is not proved here. What this file reduces it to is a statement
about the Čech complex alone: `H^i_{V(I)}(M)` is `H^i` of `C^•(f₁, …, f_r; M)` by
`nonempty_homology_localCohomology_iso_cechHomology`, the terms of that complex are
localizations of `M`, and localization and cohomology both commute with direct sums. The missing
step is the complex-level identification `C^•(f; \bigoplus_J M_j) ≅ \bigoplus_J C^•(f; M_j)`,
with its differentials — the degreewise isomorphism is
`LocalizedModule S (\bigoplus_J M_j) ≅ \bigoplus_J LocalizedModule S (M_j)`, which the library
does not yet have.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{max u v} R)

/-- The extended alternating Čech complex `C^•(f₁, …, f_r; M)`, regarded as a cochain complex in
integer degrees.

Read at `M = A`, this is **item (1) of tag 099D** for a pair carrying a chosen finite generating
family: the complex of `A`-modules attached to the pair. -/
@[stacks 099D "item (1) for a pair with a chosen finite generating family"]
abbrev extendedCechComplex : CochainComplex (ModuleCat.{max u v} R) ℤ :=
  (Cech.cechComplex f M).extend ComplexShape.embeddingUpNat

/-- The extended alternating Čech complex as an object of the derived category of `R`. -/
abbrev extendedCechObject : DerivedCategory (ModuleCat.{max u v} R) :=
  DerivedCategory.Q.obj (extendedCechComplex f M)

/-! ### The terms of the complex -/

/-- Above degree `r` the Čech complex has no summands. -/
theorem subsingleton_cechTerm_of_lt {n : ℕ} (h : r < n) : Subsingleton (Cech.cechTerm f M n) := by
  have hempty : IsEmpty {s : Finset (Fin r) // s.card = n} := by
    refine ⟨fun s => ?_⟩
    have hs := Finset.card_le_univ s.1
    rw [s.2] at hs
    simp only [Fintype.card_fin] at hs
    omega
  exact ⟨fun x y => DFinsupp.ext fun s => hempty.elim s⟩

/-- The integer-indexed Čech complex vanishes outside the degrees `0, …, r`. -/
theorem isZero_extendedCechComplex_X (i : ℤ) (hi : i < 0 ∨ (r : ℤ) + 1 ≤ i) :
    IsZero ((extendedCechComplex f M).X i) := by
  rcases hi with hneg | hbig
  · refine HomologicalComplex.isZero_extend_X _ _ _ (fun n hn => ?_)
    rw [ComplexShape.embeddingUpNat_f] at hn
    omega
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    have hrn : r < n := by exact_mod_cast (by omega : (r : ℤ) < (n : ℤ))
    refine IsZero.of_iso ?_ (HomologicalComplex.extendXIso (Cech.cechComplex f M)
      ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) (by simp))
    rw [ModuleCat.isZero_iff_subsingleton]
    exact subsingleton_cechTerm_of_lt f M hrn

/-- Each summand of the Čech complex in a positive degree is a localization in which some `f i`
has been inverted. -/
theorem isUnit_algebraMap_cechMod {s : Finset (Fin r)} {i : Fin r} (hi : i ∈ s) :
    IsUnit (algebraMap R (Module.End R (Cech.cechMod f M s)) (f i)) := by
  have hmem : f i ∈ Cech.cechSub f ({i} : Finset (Fin r)) := by
    rw [show Cech.cechSub f ({i} : Finset (Fin r)) = Submonoid.powers (f i) by
      simp [Cech.cechSub]]
    exact Submonoid.mem_powers _
  exact Cech.isUnit_algebraMap f M (Finset.singleton_subset_iff.mpr hi)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M) ⟨f i, hmem⟩

/-- Having `I`-power-torsion cohomology is detected by the derived localizations at the `f i`. -/
private theorem derivedPowerTorsionProperty_iff_forall_isZero_locDerived
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (W : DerivedCategory (ModuleCat.{max u v} R)) :
    Dualizing.derivedPowerTorsionProperty R I hI W ↔
      ∀ i, IsZero ((Dualizing.PowerTorsionBaseChange.locDerived.{v} (f i)).obj W) := by
  classical
  have hgen : Ideal.span ((Finset.image f Finset.univ : Finset R) : Set R) = I := by
    rw [← hIf, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [Dualizing.PowerTorsionBaseChange.derivedPowerTorsion_iff_locDerived_isZero I hI _ hgen]
  simp

/-- **The terms away from degree zero are invisible to torsion objects.** A complex with
`I`-power-torsion cohomology admits no nonzero morphism to any term of the Čech complex other
than the degree-zero one, placed in any degree. -/
theorem subsingleton_hom_singleFunctor_extendedCechComplex_X
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) (i : ℤ) (hi : i ≠ 0) (q : ℤ) :
    Subsingleton (W ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) q).obj
      ((extendedCechComplex f M).X i)) := by
  classical
  by_cases hout : i < 0 ∨ (r : ℤ) + 1 ≤ i
  · have hz := (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) q).map_isZero
      (isZero_extendedCechComplex_X f M i hout)
    exact ⟨fun u u' => hz.eq_of_tgt u u'⟩
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · exact absurd rfl hi
      · exact hp
    have hWloc := (derivedPowerTorsionProperty_iff_forall_isZero_locDerived f I hI hIf W).mp hW
    have hne : ∀ s : {s : Finset (Fin r) // s.card = p}, s.1.Nonempty := fun s =>
      Finset.card_pos.mp (by rw [s.2]; exact hp)
    refine subsingleton_hom_of_iso
      (((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) q).mapIso
        (HomologicalComplex.extendXIso (Cech.cechComplex f M) ComplexShape.embeddingUpNat
          (i := p) (i' := (p : ℤ)) (by simp))).symm) ?_
    refine subsingleton_hom_singleFunctor_directSum
      (fun s : {s : Finset (Fin r) // s.card = p} => f (hne s).choose)
      (fun s => ModuleCat.of R (Cech.cechMod f M s.1)) W (fun s => ?_) (fun s => ?_) q
    · exact hWloc _
    · exact isUnit_algebraMap_cechMod f M (hne s).choose_spec

/-! ### The augmentation -/

/-- The degree-zero term of the Čech complex is `M` itself: the only index set of cardinality
zero is the empty one, and localizing at the empty product inverts nothing. -/
def cechTermZeroEquiv : Cech.cechTerm f M 0 ≃ₗ[R] M :=
  (DirectSum.linearEquivFunOnFintype R _ _).trans
    ((LinearEquiv.piUnique (R := R)
      (fun s : ExtendedAlternatingCech.Idx r 0 => Cech.cechMod f M s.1)).trans
      (Stacks.CechBaseChange.cechModEmptyEquiv f M))

/-- The degree-zero term of the integer-indexed Čech complex is `M`. -/
def extendedCechXZeroIso : (extendedCechComplex f M).X 0 ≅ ModuleCat.of R M :=
  HomologicalComplex.extendXIso (Cech.cechComplex f M) ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) (by simp) ≪≫
    (cechTermZeroEquiv f M).toModuleIso

/-- **The augmentation of the Čech complex.** It is the identity on `M` in degree zero and zero
elsewhere; the Stacks map `C^•(f₁, …, f_r; M) → M`.

Read at `M = A`, this is **item (2) of tag 099D** for a pair carrying a chosen finite generating
family: the map from the complex onto the ring. -/
@[stacks 099D "item (2) for a pair with a chosen finite generating family"]
def extendedCechAugmentation :
    extendedCechComplex f M ⟶
      (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M :=
  bottomProjection (extendedCechComplex f M) 0
      (fun i hi => isZero_extendedCechComplex_X f M i (Or.inl hi)) ≫
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map (extendedCechXZeroIso f M).hom

/-- The augmentation is invertible in degree zero. -/
theorem isIso_extendedCechAugmentation_f_zero :
    IsIso ((extendedCechAugmentation f M).f 0) := by
  have h₁ : IsIso ((bottomProjection (extendedCechComplex f M) 0
      (fun i hi => isZero_extendedCechComplex_X f M i (Or.inl hi))).f 0) :=
    isIso_bottomProjection_f _ _ _
  have h₂ : IsIso (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map
      (extendedCechXZeroIso f M).hom).f 0) :=
    inferInstanceAs (IsIso ((HomologicalComplex.eval (ModuleCat.{max u v} R)
      (ComplexShape.up ℤ) 0).map ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map
        (extendedCechXZeroIso f M).hom)))
  have hfac : (extendedCechAugmentation f M).f 0 =
      (bottomProjection (extendedCechComplex f M) 0
        (fun i hi => isZero_extendedCechComplex_X f M i (Or.inl hi))).f 0 ≫
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map
        (extendedCechXZeroIso f M).hom).f 0 := rfl
  rw [hfac]
  infer_instance

/-- The augmentation, as a morphism of the derived category onto `M` placed in degree zero. -/
def extendedCechAugmentationHom :
    extendedCechObject f M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M :=
  DerivedCategory.Q.map (extendedCechAugmentation f M) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app
      M).inv

/-! ### The identification -/

/-- **Tag 0G6K in the derived category.** The Čech object has `I`-power-torsion cohomology, so it
is an object of `D_{I^∞-torsion}(R)`. -/
theorem derivedPowerTorsionProperty_extendedCechObject
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    Dualizing.derivedPowerTorsionProperty R I hI (extendedCechObject f M) := by
  rw [derivedPowerTorsionProperty_iff_forall_isZero_locDerived f I hI hIf]
  intro i
  rw [Dualizing.PowerTorsionBaseChange.locDerived_isZero_iff]
  intro q
  rw [Dualizing.PowerTorsionBaseChange.locFunctor_isZero_iff]
  intro m
  have e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) q).app
    (extendedCechComplex f M)
  obtain ⟨n, -, hn⟩ := (Cech.cechComplex_homology_torsion_support_vanishes f M q).2.1 i
    (e.toLinearEquiv m)
  refine ⟨n, e.toLinearEquiv.injective ?_⟩
  rw [map_zero, map_smul]
  exact hn

/-- **The universal property of the augmentation.** For every object `W` of `D(R)` with
`I`-power-torsion cohomology, composing with the augmentation identifies the morphisms from `W`
to the Čech object with the morphisms from `W` to `M`. -/
theorem bijective_comp_extendedCechAugmentationHom
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I)
    (W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective
      (fun g : W ⟶ extendedCechObject f M => g ≫ extendedCechAugmentationHom f M) := by
  have hbase := bijective_comp_toSingle W (extendedCechComplex f M) M 0 0 (r + 1)
    (extendedCechAugmentation f M) (isIso_extendedCechAugmentation_f_zero f M)
    (fun i hi => isZero_extendedCechComplex_X f M i (by push_cast at hi ⊢; omega))
    (fun i hi q => subsingleton_hom_singleFunctor_extendedCechComplex_X f M I hI hIf W hW i hi q)
  set e := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app
    M with he
  have hpost : Function.Bijective
      (fun h : W ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{max u v} R) 0).obj M) => h ≫ e.inv) :=
    ⟨fun _ _ hh => (cancel_mono e.inv).1 hh, fun h => ⟨h ≫ e.hom, by simp⟩⟩
  have hcomp := hpost.comp hbase
  simpa only [Function.comp_def, extendedCechAugmentationHom, Category.assoc] using hcomp

/-- **The Čech model of local cohomology, at a module.** Let `I = (f₁, …, f_r)` be a finitely
generated ideal of `R` and `M` an `R`-module. Then the value of local cohomology
`RΓ_{V(I)}` at `M` placed in degree zero is isomorphic, as an object of `D(R)`, to the extended
alternating Čech complex `C^•(f₁, …, f_r; M)`.

This deliberately carries NO `@[stacks 0A6R]` attribute: it is strictly weaker than either half
of the tag, both of which are tagged elsewhere. Tag 0A6R has two halves: that the inclusion of the
power-torsion subcategory has a right adjoint — tagged on
`Dualizing.localCohomologyRightAdjoint` — and the explicit formula, which the source states as
`RΓ_Z(K) = (A → ∏ A_{f_i} → … → A_{f₁⋯f_r}) ⊗^L_A K`, *functorially in `K ∈ D(A)`* — tagged on
`Stacks.LocalCohomology.CechFormula.localCohomologyCechIso` and its normalization. What is proved
here is that formula only at objects of the form `M⟦0⟧` for a module `M`, with neither naturality
in `M` nor the derived-tensor form at a general `K`, so tagging it would add nothing the tagged
declarations do not already state.

It is nonetheless the result chapter 51 needs, because it is what makes `RΓ_{V(I)}` concrete: see
`nonempty_homology_localCohomology_iso_cechHomology` for the explicit computation of a local
cohomology module, and `isZero_homology_localCohomology_of_outside_range` for the vanishing it
yields. -/
theorem nonempty_localCohomology_iso_extendedCechObject
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    Nonempty ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) ≅
      extendedCechObject f M) :=
  nonempty_localCohomology_iso_coreflection I hI
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)
    (extendedCechAugmentationHom f M)
    (fun W hW => bijective_comp_extendedCechAugmentationHom f M I hI hIf W hW)

/-- **The local cohomology modules are the Čech cohomology modules.** `H^i_{V(I)}(M)` is the
`i`-th cohomology of the extended alternating Čech complex `C^•(f₁, …, f_r; M)`. -/
theorem nonempty_homology_localCohomology_iso_cechHomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))) ≅
      (extendedCechComplex f M).homology i) := by
  obtain ⟨e⟩ := nonempty_localCohomology_iso_extendedCechObject f M I hI hIf
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app
      (extendedCechComplex f M)⟩

/-! ### The identification as a named isomorphism -/

/-- **The comparison morphism of the Čech model.** The transpose of the augmentation along the
local-cohomology adjunction of Stacks 0A6Q: a morphism `C^•(f₁, …, f_r; M) ⟶ RΓ_{V(I)}(M)` in
`D(R)`, built from the adjunction and using no choice. -/
def extendedCechObjectToLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    extendedCechObject f M ⟶
      (Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) :=
  coreflectionToLocalCohomology I hI
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)
    (extendedCechAugmentationHom f M)

/-- The comparison morphism of the Čech model lifts the augmentation along the counit. -/
theorem extendedCechObjectToLocalCohomology_comp_counit
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    extendedCechObjectToLocalCohomology f M I hI hIf ≫
        (Dualizing.localCohomologyAdjunction R I hI).counit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) =
      extendedCechAugmentationHom f M :=
  coreflectionToLocalCohomology_comp_counit I hI
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)
    (extendedCechAugmentationHom f M)

/-- **The Čech model of local cohomology, for a specific morphism.** The comparison morphism of
the Čech model is an isomorphism. -/
instance isIso_extendedCechObjectToLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    IsIso (extendedCechObjectToLocalCohomology f M I hI hIf) :=
  isIso_coreflectionToLocalCohomology I hI
    (derivedPowerTorsionProperty_extendedCechObject f M I hI hIf)
    (extendedCechAugmentationHom f M)
    (fun W hW => bijective_comp_extendedCechAugmentationHom f M I hI hIf W hW)

/-- **The Čech model of local cohomology, as a named isomorphism.** The choice-free form of
`Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject`. -/
def extendedCechObjectIsoLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    extendedCechObject f M ≅
      (Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) :=
  asIso (extendedCechObjectToLocalCohomology f M I hI hIf)

/-- The named Čech model isomorphism, in the direction of
`Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject`. -/
def localCohomologyIsoExtendedCechObject
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) :
    (Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) ≅
      extendedCechObject f M :=
  (extendedCechObjectIsoLocalCohomology f M I hI hIf).symm

/-- **Čech cohomology is local cohomology, as `R`-modules.** The degree-`i` homology of the
comparison morphism of the Čech model, as an isomorphism of `R`-modules. -/
def extendedCechHomologyIsoLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    (extendedCechComplex f M).homology i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app
      (extendedCechComplex f M)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso
      (extendedCechObjectIsoLocalCohomology f M I hI hIf)

/-- **The `R`-linear comparison of Čech cohomology with local cohomology.** The degree-`i`
homology of the comparison morphism of the Čech model. -/
def extendedCechHomologyToLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    (extendedCechComplex f M).homology i ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))) :=
  (extendedCechHomologyIsoLocalCohomology f M I hI hIf i).hom

/-- The comparison on homology is the homology of the comparison morphism. -/
theorem extendedCechHomologyToLocalCohomology_eq
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    extendedCechHomologyToLocalCohomology f M I hI hIf i =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app
          (extendedCechComplex f M)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
          (extendedCechObjectToLocalCohomology f M I hI hIf) := rfl

/-- The `R`-linear comparison of Čech cohomology with local cohomology is an isomorphism. -/
instance isIso_extendedCechHomologyToLocalCohomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    IsIso (extendedCechHomologyToLocalCohomology f M I hI hIf i) :=
  (extendedCechHomologyIsoLocalCohomology f M I hI hIf i).isIso_hom

/-- **The local cohomology modules are the Čech cohomology modules.** The choice-free form of
`Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology`. -/
def localCohomologyIsoExtendedCechHomology
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
        ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
          ((Dualizing.localCohomologyFunctor R I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))) ≅
      (extendedCechComplex f M).homology i :=
  (extendedCechHomologyIsoLocalCohomology f M I hI hIf i).symm

/-- **Local cohomology is concentrated in degrees `0, …, r`.** For an ideal generated by `r`
elements, the local cohomology of a module vanishes in negative degrees and above degree `r`.
This is the degree bound of Tag 0G6K, transported to `RΓ_{V(I)}` through the Čech model. -/
theorem isZero_homology_localCohomology_of_outside_range
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ)
    (hi : i < 0 ∨ (r : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)))) := by
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology f M I hI hIf i
  refine IsZero.of_iso ?_ e
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (Cech.cechComplex_homology_torsion_support_vanishes f M i).1 hi

end Stacks.LocalCohomology

end
