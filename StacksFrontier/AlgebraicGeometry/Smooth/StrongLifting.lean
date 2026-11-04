module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smooth.Lifting

/-!
# The strong lifting property of a smooth morphism of affine schemes

A *thickening* of schemes is a closed immersion which is surjective on points; equivalently, over
an affine target, a surjection of rings whose kernel is a locally nilpotent ideal. Such a
thickening need not be a finite chain of first-order ones, so the infinitesimal lifting property
of a smooth morphism — which only speaks about square-zero extensions — does not by itself
produce lifts across it. What does is Algebra, Lemma 10.138.17: a smooth ring map lifts along a
*locally* nilpotent ideal, by replacing the ideal by a finitely generated — hence nilpotent —
sub-ideal.

This file turns that ring statement into the geometric one, for a smooth morphism of affine
schemes.

## Main definitions

* `Stacks.Smooth.StrongLifting` is the lifting property of a morphism of schemes against the
  spectrum of every surjection of rings with locally nilpotent kernel.

## Main results

* `AlgebraicGeometry.isLocallyNilpotent_ker_appTop_of_surjective`: a closed immersion into an
  affine scheme which is surjective on points is cut out by a locally nilpotent ideal.
* `Stacks.Smooth.strongLifting_specMap`: the ring dictionary, in the direction that turns a
  smooth ring map into the geometric lifting property.
* `Stacks.Smooth.strongLifting_of_isAffine`: a smooth morphism of affine schemes has the strong
  lifting property.
* `Stacks.Smooth.exists_lift_of_isClosedImmersion_of_surjective`: **the engine.** Let `f : X ⟶ S`
  be a smooth morphism of affine schemes, let `i : T ⟶ T'` be a closed immersion of schemes with
  `T'` affine which is surjective on points, and let `a : T ⟶ X` and `h : T' ⟶ S` present a
  lifting problem for `f` along `i`. Then the problem has a solution.

## Implementation notes

`Stacks.Smooth.StrongLifting` is the exact analogue of Mathlib's `AlgebraicGeometry.FormallySmooth`
with `RingHom.ker φ ^ 2 = ⊥` weakened to `Ideal.IsLocallyNilpotent (RingHom.ker φ)`, and the
proofs of `Stacks.Smooth.StrongLifting.of_iso`, `Stacks.Smooth.strongLifting_specMap` and
`Stacks.Smooth.exists_lift_of_isClosedImmersion_of_surjective` follow
`Stacks.Smooth.FormallySmooth.of_iso`, `Stacks.Smooth.formallySmooth_specMap` and
`Stacks.Smooth.formallySmoothScheme_of_formallySmooth` of
`StacksFrontier/AlgebraicGeometry/Smooth/FormallySmoothCriterion.lean` and
`StacksFrontier/AlgebraicGeometry/Smooth/FormallySmoothScheme.lean` step for step, with
`main_theorem07K4` in place of `Algebra.FormallySmooth.liftOfSurjective`. Unlike the first-order
case, no uniqueness is available and none is claimed: `main_theorem07K4` asserts only existence.

The hypotheses are that `X` and `S` are affine, not that `f` is an affine morphism. The
first-order statement `Stacks.Smooth.formallySmooth_of_isAffineHom` gets the affine-morphism case
by base changing `f` along `h : T' ⟶ S`, which turns a lift into a section of the base change;
that argument applies verbatim here, but the only consumer of this file —
`AlgebraicGeometry.Space.exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom` — feeds it a
smooth morphism of two affine schemes of the big fppf site, so the stronger form is not needed.

`AlgebraicGeometry.isLocallyNilpotent_ker_appTop_of_surjective` duplicates two *private* lemmas of
this library, `isLocallyNilpotent_ker_appTop` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/MonomorphismClosedImmersion.lean` and
`isLocallyNilpotent_ker_of_surjective` of
`StacksFrontier/AlgebraicGeometry/Topologies/EtaleDescentIntegral.lean`; neither is usable from
outside its file, so the statement is proved here once, publicly, and the two private copies can
be routed onto it.

## References

* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A thickening of an affine scheme is cut out by a locally nilpotent ideal.** A closed
immersion into an affine scheme which is surjective on points has support everything, so its
kernel on global sections lies in the nilradical. -/
theorem isLocallyNilpotent_ker_appTop_of_surjective {X Z : Scheme.{u}} [IsAffine Z] (i : X ⟶ Z)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) :
    Ideal.IsLocallyNilpotent (RingHom.ker i.appTop.hom) := by
  have hsupport : (i.ker.support : Set Z) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hi, closure_univ]
  rw [Scheme.ker_of_isAffine i] at hsupport
  have hker : (RingHom.ker i.appTop.hom : Set Γ(Z, ⊤)) ⊆ nilradical Γ(Z, ⊤) := by
    rw [← Scheme.zeroLocus_eq_univ_iff_subset_nilradical]
    simpa using hsupport
  intro a ha
  have ha' : a ∈ (⊥ : Ideal Γ(Z, ⊤)).radical := by
    simpa [nilradical] using hker ha
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha'
  exact ⟨n, by simpa using hn⟩

end AlgebraicGeometry

namespace Stacks.Smooth

open AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ S` has the **strong lifting property** when every commutative
square
```
Spec A  --g--→ X
  |            |
Spec φ         f
  ↓            ↓
Spec R  --h--→ S
```
in which `φ : R ⟶ A` is a surjection of rings with locally nilpotent kernel has a diagonal
filler. This is the infinitesimal lifting property of Mathlib's
`AlgebraicGeometry.FormallySmooth` with the square-zero condition on the kernel relaxed to local
nilpotence. -/
abbrev StrongLifting {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (R A : CommRingCat.{u}) (φ : R ⟶ A), Function.Surjective φ.hom →
    Ideal.IsLocallyNilpotent (RingHom.ker φ.hom) →
    ∀ (g : Spec A ⟶ X) (h : Spec R ⟶ S), g ≫ f = Spec.map φ ≫ h →
      ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧ Spec.map φ ≫ g' = g

/-- The strong lifting property transports along an isomorphism of arrows. -/
theorem StrongLifting.of_iso {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    (eX : X ≅ X') (eS : S ≅ S') (he : f ≫ eS.hom = eX.hom ≫ f') (hf : StrongLifting f) :
    StrongLifting f' := by
  have he' : eX.inv ≫ f = f' ≫ eS.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, he, Iso.inv_hom_id_assoc]
  intro R A φ hφ hnil g h hcomm
  obtain ⟨k, hk1, hk2⟩ := hf R A φ hφ hnil (g ≫ eX.inv) (h ≫ eS.inv)
    (by rw [Category.assoc, he', ← Category.assoc, hcomm, Category.assoc])
  refine ⟨k ≫ eX.hom, ?_, ?_⟩
  · rw [Category.assoc, ← he, ← Category.assoc, hk1, Category.assoc, eS.inv_hom_id,
      Category.comp_id]
  · rw [← Category.assoc, hk2, Category.assoc, eX.inv_hom_id, Category.comp_id]

/-- **The ring dictionary for the strong lifting property.** The spectrum of a smooth ring map
has the strong lifting property; the lift is the one produced by Algebra, Lemma 10.138.17. -/
@[stacks 07K4 "the geometric form for the spectrum of a smooth ring map"]
theorem strongLifting_specMap {R A : CommRingCat.{u}} {ψ : R ⟶ A} (hψ : RingHom.Smooth ψ.hom) :
    StrongLifting (Spec.map ψ) := by
  intro R' A' φ hφ hnil g h hcomm
  obtain ⟨a, rfl⟩ := Spec.map_surjective g
  obtain ⟨b, rfl⟩ := Spec.map_surjective h
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hcomm
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra R R' := b.hom.toAlgebra
  let : Algebra R A' := (b ≫ φ).hom.toAlgebra
  have hsm : Algebra.Smooth R A := hψ
  let aA : A →ₐ[R] A' := { a.hom with commutes' := fun r => congrArg (fun k => k.hom r) hcomm }
  let φA : R' →ₐ[R] A' := { φ.hom with commutes' := fun _ => rfl }
  have hφA : Function.Surjective φA := hφ
  obtain ⟨f₀, hf₀⟩ := main_theorem07K4 R A R' (RingHom.ker φA) hnil
    ((Ideal.quotientKerAlgEquivOfSurjective hφA).symm.toAlgHom.comp aA)
  refine ⟨Spec.map (CommRingCat.ofHom f₀.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, Spec.map_inj]
    ext r
    exact f₀.commutes r
  · rw [← Spec.map_comp, Spec.map_inj]
    ext x
    have hx : Ideal.Quotient.mk (RingHom.ker φA) (f₀ x)
        = (Ideal.quotientKerAlgEquivOfSurjective hφA).symm (aA x) :=
      AlgHom.congr_fun hf₀ x
    have h2 := Ideal.quotientKerAlgEquivOfSurjective_mk hφA (f₀ x)
    rw [hx, AlgEquiv.apply_symm_apply] at h2
    exact h2.symm

/-- **A smooth morphism of affine schemes has the strong lifting property.** -/
@[stacks 07K4 "the geometric form for a smooth morphism of affine schemes"]
theorem strongLifting_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
    [AlgebraicGeometry.Smooth f] : StrongLifting f :=
  (strongLifting_specMap
      ((HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Smooth.{u})).mp ‹_›)).of_iso
    X.isoSpec.symm S.isoSpec.symm (Scheme.isoSpec_inv_naturality f)

/-- **Lifting along a thickening for a smooth morphism of affine schemes.** Let `f : X ⟶ S` be a
smooth morphism of affine schemes, let `i : T ⟶ T'` be a closed immersion of schemes with `T'`
affine which is surjective on points, and let `a : T ⟶ X` and `h : T' ⟶ S` present a lifting
problem for `f` along `i`. Then there is a morphism `b : T' ⟶ X` with `b ≫ f = h` and
`i ≫ b = a`.

The thickening is the spectrum of the surjection `i.appTop` on global sections, whose kernel is
locally nilpotent by
`AlgebraicGeometry.isLocallyNilpotent_ker_appTop_of_surjective`, so
`Stacks.Smooth.strongLifting_of_isAffine` applies. -/
@[stacks 07K4 "the lifting problem along a thickening of affine schemes",
  sga "3 III 2.5" "(a), special case",
  sga "3 IX 3.3" "special case"]
theorem exists_lift_of_isClosedImmersion_of_surjective {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [AlgebraicGeometry.Smooth f] [IsAffine T'] {i : T ⟶ T'}
    [IsClosedImmersion i] (hi : Function.Surjective i.base) (a : T ⟶ X) (h : T' ⟶ S)
    (hcomm : a ≫ f = i ≫ h) :
    ∃ b : T' ⟶ X, b ≫ f = h ∧ i ≫ b = a := by
  have hTaff : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  obtain ⟨g₀, hg1, hg2⟩ := strongLifting_of_isAffine f Γ(T', ⊤) Γ(T, ⊤) i.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    (isLocallyNilpotent_ker_appTop_of_surjective i hi) (T.isoSpec.inv ≫ a) (T'.isoSpec.inv ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← Category.assoc,
      Scheme.isoSpec_inv_naturality])
  refine ⟨T'.isoSpec.hom ≫ g₀, ?_, ?_⟩
  · rw [Category.assoc, hg1, Iso.hom_inv_id_assoc]
  · rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, hg2,
      Iso.hom_inv_id_assoc]

end Stacks.Smooth

end
