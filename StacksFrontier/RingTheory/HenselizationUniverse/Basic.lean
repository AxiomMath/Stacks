module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The henselization with the base and the henselization in independent universes

`IsLocalRing.IsHenselization R L Rh` already binds the universes of `R`, `L` and `Rh`
independently: its `ind_etale` field speaks about `ULift.{u} Rh`, which is
`StacksDraft.IndEtale R Rh`. Its two universal properties, however, are proved for `R` and `Rh`
in one universe — `HenselianLocalRing.indEtaleAlgHom` (Lemma 04GS) and
`HenselianLocalRing.indEtaleAlgHomOfResidue` (Lemma 04GU) both take
`{R Rh : Type u}`. This file restates them at independent universes, proving each from the
single-universe form by lifting the base and the algebra into a common universe with `ULift`.

## Main results

* `StacksDraft.existsUnique_isLocalHom_of_indEtale`: Lemma 04GS with `R`, `Rh` and the target
  henselian local ring in three independent universes.
* `StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale`: Lemma 04GU likewise.
* `StacksDraft.existsUnique_henselization_map`: the henselization map over a base ring, at
  independent universes.
* `StacksDraft.isHenselization_of_indEtale_of_surjective`,
  `StacksDraft.exists_isHenselization_of_indEtale`: recognising a henselization from
  ind-étaleness, at independent universes.

## Implementation notes

Nothing in `StacksFrontier/RingTheory/Henselian/` is modified: the generalisations are obtained from
its public API. The lifting step is always the same — replace `R : Type u` by `ULift.{v} R` and
`Rh : Type v` by `ULift.{u} Rh`, both of which live in `Type (max u v)`, transport the ind-étale
hypothesis with `StacksDraft.indEtale_of_equiv`, apply the single-universe lemma, and carry the
resulting algebra map back along `ULift.ringEquiv`. Residue fields are carried along by
`IsLocalRing.ResidueField.map` of `ULift.ringEquiv`, which is a local ring map because a ring
equivalence is.

## References

* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ)

## Tags

henselization, strict henselization, universal property, ind-étale, universe, ULift
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace StacksDraft

/-- A henselization is ind-étale over its base, in the universe-independent sense. This is the
`ind_etale` field of `IsLocalRing.IsHenselization` read through `StacksDraft.IndEtale`. -/
theorem indEtale_of_isHenselization {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh] :
    IndEtale R Rh :=
  IsHenselization.ind_etale (R := R) (L := L) (Rh := Rh)

section Lift

/-- The fully lifted map `ULift A → ULift B` is local when `A → B` is. -/
private theorem isLocalHom_ulift {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    letI : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
    IsLocalHom (algebraMap (ULift.{v} A) (ULift.{u} B)) := by
  let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
  refine ⟨fun a ha => ?_⟩
  have h1 : IsUnit (algebraMap A B a.down) :=
    (MulEquiv.isUnit_map (ULift.ringEquiv : ULift.{u} B ≃+* B)).mpr ha
  exact (MulEquiv.isUnit_map (ULift.ringEquiv : ULift.{v} A ≃+* A)).mp
    (IsLocalHom.map_nonunit (f := algebraMap A B) a.down h1)

/-- The residue field map of the fully lifted map is surjective when that of `A → B` is. -/
private theorem residueFieldMap_ulift_surjective {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hs : Function.Surjective (ResidueField.map (algebraMap A B))) :
    letI : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
    letI : IsLocalRing (ULift.{v} A) := (ULift.ringEquiv.symm : A ≃+* ULift.{v} A).isLocalRing
    letI : IsLocalRing (ULift.{u} B) := (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).isLocalRing
    letI : IsLocalHom (algebraMap (ULift.{v} A) (ULift.{u} B)) := isLocalHom_ulift
    Function.Surjective (ResidueField.map (algebraMap (ULift.{v} A) (ULift.{u} B))) := by
  let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
  let : IsLocalRing (ULift.{v} A) := (ULift.ringEquiv.symm : A ≃+* ULift.{v} A).isLocalRing
  let : IsLocalRing (ULift.{u} B) := (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).isLocalRing
  let : IsLocalHom (algebraMap (ULift.{v} A) (ULift.{u} B)) := isLocalHom_ulift
  let : IsLocalHom (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom :=
    ⟨(isLocalHom_equiv (ULift.ringEquiv.symm : B ≃+* ULift.{u} B)).map_nonunit⟩
  intro z
  obtain ⟨b, rfl⟩ := residue_surjective z
  obtain ⟨a, ha⟩ := hs (residue B b.down)
  obtain ⟨a, rfl⟩ := residue_surjective a
  refine ⟨residue (ULift.{v} A) ⟨a⟩, ?_⟩
  rw [ResidueField.map_residue] at ha ⊢
  have hh := congrArg
    (ResidueField.map (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom) ha
  simp only [ResidueField.map_residue] at hh
  convert hh using 1 <;> rfl

end Lift

/-- **The universal property of the henselization at independent universes** (Lemma 04GS). Let
`A` be a local ring, let `B` be a local `A`-algebra which is ind-étale with surjective residue
field map, and let `C` be a henselian local ring with `A → C` local. Then there is exactly one
`A`-algebra map `B → C` which is a local ring map. The three rings have independent universes. -/
@[ega "IV 18.6.6" "more general", sga "4 VIII 4.1" "partial"]
theorem existsUnique_isLocalHom_of_indEtale
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [HenselianLocalRing C] [Algebra A B] [Algebra A C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    (hi : IndEtale A B) (hs : Function.Surjective (ResidueField.map (algebraMap A B))) :
    ∃! f : B →ₐ[A] C, IsLocalHom f :=
  ⟨HenselianLocalRing.indEtaleAlgHom hi hs,
    HenselianLocalRing.isLocalHom_indEtaleAlgHom hi hs,
    HenselianLocalRing.indEtaleAlgHom_unique hi hs⟩

/-- **The universal property of the strict henselization at independent universes** (Lemma 04GU).
Let `A` be a local ring, let `B` be a local `A`-algebra which is ind-étale, and let `C` be a
henselian local ring. A ring map `φ : κ(B) → κ(C)` compatible with the two structure maps out of
`A` is induced by exactly one local `A`-algebra map `B → C`. The three rings have independent
universes. -/
@[ega "IV 18.6.6" "more general", ega "IV 18.8.8" "more general", sga "4 VIII 4.4" "more general"]
theorem existsUnique_isLocalHom_comp_residue_of_indEtale
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsLocalRing B] [HenselianLocalRing C]
    (hi : IndEtale A B) (φ : ResidueField B →+* ResidueField C)
    (hφ : φ.comp ((residue B).comp (algebraMap A B)) = (residue C).comp (algebraMap A C)) :
    ∃! f : B →ₐ[A] C, IsLocalHom f ∧
      (residue C).comp f.toRingHom = φ.comp (residue B) :=
  ⟨HenselianLocalRing.indEtaleAlgHomOfResidue hi φ hφ,
    ⟨HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hi φ hφ,
      HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hi φ hφ⟩,
    fun g hg => HenselianLocalRing.indEtaleAlgHomOfResidue_unique hi φ hφ g hg.1 hg.2⟩

/-- **The henselization map over a base ring, at independent universes.** Let `A → Ah` be a
henselization of the local ring `A` and let `B` be a henselian local ring with `A → B` local,
everything over a base ring `R`. There is exactly one `R`-algebra map `Ah → B` which is local and
compatible with `A → B`. -/
theorem existsUnique_henselization_map
    {R : Type*} {A Ah : Type*} {B : Type*}
    [CommRing R] [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [CommRing B] [HenselianLocalRing B]
    [Algebra R A] [Algebra R Ah] [Algebra A Ah] [IsScalarTower R A Ah]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsHenselization A (ResidueField A) Ah] [IsLocalHom (algebraMap A B)] :
    ∃ f : Ah →ₐ[R] B, IsLocalHom f ∧
      f.toRingHom.comp (algebraMap A Ah) = algebraMap A B ∧
      (∀ f' : Ah →ₐ[R] B, IsLocalHom f' →
        f'.toRingHom.comp (algebraMap A Ah) = algebraMap A B → f' = f) := by
  let : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  obtain ⟨f, hf, huniq⟩ := existsUnique_isLocalHom_of_indEtale (C := B)
    (indEtale_of_isHenselization (ResidueField A) (Rh := Ah))
    (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah)).2
  refine ⟨f.restrictScalars R, ⟨hf.map_nonunit⟩, RingHom.ext fun a => f.commutes a,
    fun f' hf' hcomp => AlgHom.ext fun x => AlgHom.congr_fun (huniq
      { f'.toRingHom with commutes' := fun a => RingHom.congr_fun hcomp a }
      ⟨hf'.map_nonunit⟩) x⟩

/-- **Recognising the henselization**, at independent universes: a henselian local ind-étale
`A`-algebra with surjective residue field map is a henselization of `A`. -/
theorem isHenselization_of_indEtale_of_surjective
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [HenselianLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (h : IndEtale A B) (hs : Function.Surjective (ResidueField.map (algebraMap A B))) :
    IsHenselization A (ResidueField A) B :=
  ⟨inferInstance, h,
    RingEquiv.ofBijective _ ⟨RingHom.injective _, hs⟩, fun a => ResidueField.map_residue _ a⟩

/-- The residue field maps of a tower `A → B → C` of local rings compose on residue classes. -/
private theorem map_map_residue_of_tower
    {A B C : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] (a : A) :
    ResidueField.map (algebraMap B C) (ResidueField.map (algebraMap A B) (residue A a)) =
      residue C (algebraMap A C a) := by
  simp [← IsScalarTower.algebraMap_apply A B C]

/-- **Recognising the henselization at an intermediate ring**, at independent universes. If `C` is
a henselization of `A` with residue field `L` and `C` is ind-étale over an intermediate local ring
`B`, with `A → B → C` local, then `C` is a henselization of `B` with residue field `L`; and if `L`
is a separable algebraic closure of `κ(A)` it is one of `κ(B)`. -/
theorem exists_isHenselization_of_indEtale
    {A B C L : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [Field L] [Algebra (ResidueField A) L]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    [IsHenselization A L C] (hi : IndEtale B C) :
    ∃ alg : Algebra (ResidueField B) L,
      letI := alg
      IsHenselization B L C ∧
        (IsSepClosure (ResidueField A) L → IsSepClosure (ResidueField B) L) := by
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := A) (L := L) (Rh := C)
  let φ := e.symm.toRingHom.comp (ResidueField.map (algebraMap B C))
  let := φ.toAlgebra
  refine ⟨φ.toAlgebra, ⟨IsHenselization.henselian (R := A) (L := L), hi, e, fun b => ?_⟩,
    fun hs => ?_⟩
  · show e (e.symm (ResidueField.map (algebraMap B C) (residue B b))) = _
    rw [e.apply_symm_apply, ResidueField.map_residue]
  · let := hs
    let : Algebra (ResidueField A) (ResidueField B) :=
      (ResidueField.map (algebraMap A B)).toAlgebra
    have : IsScalarTower (ResidueField A) (ResidueField B) L := by
      refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => ?_)
      obtain ⟨a, rfl⟩ := residue_surjective a
      apply e.injective
      show e (algebraMap (ResidueField A) L (residue A a)) =
        e (e.symm (ResidueField.map (algebraMap B C)
          (ResidueField.map (algebraMap A B) (residue A a))))
      rw [he, e.apply_symm_apply, map_map_residue_of_tower]
    exact ⟨IsSepClosure.sep_closed (ResidueField A),
      Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField B) L⟩

/-- A local map `A → B → C` of local rings which is surjective on residue fields overall is
surjective on residue fields at the second step. -/
theorem residueFieldMap_surjective_of_tower
    {A B C : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap A C)]
    (hs : Function.Surjective (ResidueField.map (algebraMap A C))) :
    Function.Surjective (ResidueField.map (algebraMap B C)) := fun c => by
  obtain ⟨a, rfl⟩ := hs c
  obtain ⟨a, rfl⟩ := residue_surjective a
  exact ⟨ResidueField.map (algebraMap A B) (residue A a), map_map_residue_of_tower a⟩

end StacksDraft

end
