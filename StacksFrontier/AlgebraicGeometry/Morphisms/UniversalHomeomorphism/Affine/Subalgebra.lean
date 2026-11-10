module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal homeomorphisms and intermediate algebras

Let `A → B` be a ring map whose morphism on spectra is a universal homeomorphism, and let `B'`
be an intermediate `A`-subalgebra of `B`. Then the morphism on spectra attached to `A → B'` is
again a universal homeomorphism, and if `A → B` does not change residue fields neither does
`A → B'`. Dually, the morphism attached to `B' → B` is a universal homeomorphism as well.

## Main definitions

* `AlgebraicGeometry.subalgebraToSubringEquiv` is the ring isomorphism between a subalgebra and
  its underlying subring.

## Main results

* `AlgebraicGeometry.universallyClosed_specMap_subalgebra` and
  `AlgebraicGeometry.universallyInjective_specMap_subalgebra`: universal closedness and
  universal injectivity pass to an intermediate subalgebra.
* `AlgebraicGeometry.universalHomeomorphism_specMap_subalgebra`: so does being a universal
  homeomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_specMap_subalgebra`: so does inducing isomorphisms
  on residue fields.
* `AlgebraicGeometry.universalHomeomorphism_specMap_to_subalgebra` and
  `AlgebraicGeometry.isIso_residueFieldMap_specMap_to_subalgebra`: the two properties also
  descend to the morphism `Spec B → Spec B'` in the other direction.
* `AlgebraicGeometry.universalHomeomorphism_specMap_to_subring`: the same for the underlying
  subring of a subalgebra.

## Implementation notes

The ring map is represented by an `Algebra` structure and the intermediate ring by a
`Subalgebra`. Lying over for the intermediate algebra,
`AlgebraicGeometry.primeSpectrum_comap_subalgebra_surjective_of_isIntegral`, is what makes the
point-set arguments go through; it is recorded first.

## References

* [Stacks Project, Tag 0CN7](https://stacks.math.columbia.edu/tag/0CN7)
* [Stacks Project, Lemma 29.45.4](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- If `B` is integral over `A`, every prime of an intermediate `A`-subalgebra `S` is
the contraction of a prime of `B`. -/
theorem primeSpectrum_comap_subalgebra_surjective_of_isIntegral
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (S : Subalgebra A B) :
    Function.Surjective (PrimeSpectrum.comap (Subalgebra.val S).toRingHom) := by
  have hcomp :
      (Subalgebra.val S).toRingHom.comp (algebraMap A S) = algebraMap A B := by
    ext a
    rfl
  have hIntegral : ((Subalgebra.val S).toRingHom).IsIntegral :=
    RingHom.IsIntegral.tower_top (f := algebraMap A S)
      (g := (Subalgebra.val S).toRingHom) <| by
        rw [hcomp]
        exact algebraMap_isIntegral_iff.mpr inferInstance
  exact integral_overring_surjective (Subalgebra.val S).toRingHom hIntegral
    Subtype.val_injective

/-- **Stacks 0CN7.** If the morphism on spectra associated to an algebra is universally closed,
the same holds for the morphism associated to any subalgebra. -/
@[stacks 0CN7 "universally_closed"]
lemma universallyClosed_specMap_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (B' : Subalgebra A B)
    [UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := by
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp <|
    (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom (algebraMap A B))).mp <|
      IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have : Algebra.IsIntegral A B' := .of_injective B'.val Subtype.val_injective
  exact (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp
    (IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance))).1

/-- **Stacks 0CN7.** Universal injectivity of the map on spectra passes from an algebra to any
of its subalgebras, provided the original map is universally closed and universally
injective. -/
@[stacks 0CN7 "universally_closed_and_injective"]
lemma universallyInjective_specMap_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [UniversallyClosed (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)]
    [UniversallyInjective (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)]
    (B' : Subalgebra A B) :
    UniversallyInjective (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op) := by
  classical
  let f₀ : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B') :=
    Scheme.Spec.map (CommRingCat.ofHom (Subalgebra.val B').toRingHom).op
  let f' : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op
  have hcomp : g ≫ f' = f₀ := by
    change Spec.map (CommRingCat.ofHom (Subalgebra.val B').toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B')) =
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext a
    simp
  have hIntHom : IsIntegralHom f₀ :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have : Algebra.IsIntegral A B :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hIntHom)
  have hLift : Function.Surjective g := primeSpectrum_comap_subalgebra_surjective_of_isIntegral B'
  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := g ≫ f'
  have hUi : UniversallyInjective f := by
    rw [show f = f₀ from hcomp]
    infer_instance
  have hcrit := ((tfae_universallyInjective f).out 1 3).mp hUi
  apply ((tfae_universallyInjective f').out 1 3).mpr
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨qx, rfl⟩ := hLift x
    obtain ⟨qy, rfl⟩ := hLift y
    exact congrArg g (hcrit.1 (by simpa [f, Scheme.Hom.comp_apply] using hxy))
  · obtain ⟨q, rfl⟩ := hLift x
    let K : Type u := (Spec (CommRingCat.of A)).residueField (f' (g q))
    let E : Type u := (Spec (CommRingCat.of B')).residueField (g q)
    let L : Type u := (Spec (CommRingCat.of B)).residueField q
    let α : K →+* E := (f'.residueFieldMap (g q)).hom
    let β : E →+* L := (g.residueFieldMap q).hom
    let γ : K →+* L := (f.residueFieldMap q).hom
    have hγα : γ = β.comp α := by
      simp [α, β, γ, f, CommRingCat.hom_comp]
    let : Algebra K E := α.toAlgebra
    let : Algebra E L := β.toAlgebra
    let : Algebra K L := γ.toAlgebra
    have : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' hγα
    have : IsPurelyInseparable K L := hcrit.2 q
    change α.IsPurelyInseparable
    exact IsPurelyInseparable.tower_bot K E L

/-- **Stacks 0CN7.** If the map on spectra of an algebra is a universal homeomorphism, then so
is the map on spectra of any intermediate subalgebra. -/
@[stacks 0CN7 "universal_homeomorphism"]
lemma universalHomeomorphism_specMap_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)]
    (B' : Subalgebra A B) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op) := by
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  obtain ⟨hi, hj, hs⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
      inferInstance
  have : UniversallyClosed f := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hi).1
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hi)
  refine (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr
      (Algebra.IsIntegral.of_injective B'.val Subtype.val_injective)),
      universallyInjective_specMap_subalgebra B', ?_⟩
  let g := Scheme.Spec.map (CommRingCat.ofHom (B'.val : B' →+* B)).op
  have hc : g ≫ Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op = f := by
    change Spec.map (CommRingCat.ofHom (B'.val : B' →+* B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B')) =
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    rw [← Spec.map_comp]
    congr 1
  rw [← hc] at hs
  exact Surjective.of_comp g _

/-- Every prime of an intermediate subalgebra lifts to a prime of the larger ring, read as a
statement about the induced morphism of affine schemes. -/
private lemma exists_spec_point_lift_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (B' : Subalgebra A B) (x : Spec (.of B')) :
    ∃ y : Spec (.of B),
      (Scheme.Spec.map (CommRingCat.ofHom (Subalgebra.val B')).op) y = x := by
  change ∃ y : PrimeSpectrum B,
    PrimeSpectrum.comap (Subalgebra.val B').toRingHom y = x
  exact primeSpectrum_comap_subalgebra_surjective_of_isIntegral B' x

/-- The morphism of spectra attached to an intermediate subalgebra factors the morphism
attached to the whole algebra. -/
private lemma specMap_subalgebra_comp
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (B' : Subalgebra A B) :
    (Scheme.Spec.map (CommRingCat.ofHom (Subalgebra.val B')).op) ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op := by
  rw [← Functor.map_comp]
  congr 1

/-- The morphism of spectra attached to an intermediate subalgebra `C`, composed with the one
attached to `A → C`, is the morphism attached to `A → B`. -/
private lemma specMap_algebraMap_subalgebra_comp
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) :
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op := by
  rw [← Functor.map_comp]
  congr 1

/-- **Stacks 0CN7.** If a universal homeomorphism between affine spectra induces isomorphisms
on residue fields, then so does the map associated to any intermediate subalgebra. -/
@[stacks 0CN7 "universal_homeomorphism_residue_fields"]
lemma isIso_residueFieldMap_specMap_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)]
    (hres : ∀ x : Spec (.of B),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap x))
    (B' : Subalgebra A B) :
    ∀ x : Spec (.of B'),
      IsIso ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op).residueFieldMap x) := by
  intro x
  have : Algebra.IsIntegral A B :=
    universalHomeomorphism_algebra_isIntegral (A := A) (B := B)
  obtain ⟨y', rfl⟩ := exists_spec_point_lift_subalgebra B' x
  let g : Spec (.of B) ⟶ Spec (.of B') :=
    Scheme.Spec.map (CommRingCat.ofHom (Subalgebra.val B')).op
  let f : Spec (.of B') ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B')).op
  have hcomp : IsIso ((g ≫ f).residueFieldMap y') := by
    rw [Scheme.Hom.residueFieldMap_congr (specMap_subalgebra_comp B') y']
    exact IsIso.comp_isIso' (Scheme.residueFieldCongr _).isIso_hom (hres y')
  exact isIso_residueFieldMap_of_isIso_comp g f y' hcomp

/-- A subalgebra and its underlying subring are the same ring. -/
def subalgebraToSubringEquiv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (C : Subalgebra A B) : C ≃+* C.toSubring where
  toFun x := ⟨x.val, (Subalgebra.mem_toSubring).2 x.property⟩
  invFun x := ⟨x.val, (Subalgebra.mem_toSubring).1 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- If `Spec B → Spec A` is a universal homeomorphism and `C` is an intermediate subalgebra,
then `Spec B → Spec C` is a universal homeomorphism too. -/
lemma universalHomeomorphism_specMap_to_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (C : Subalgebra A B) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op) := by
  let f := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  let g := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op
  let h := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  have hcomp : g ≫ h = f := specMap_algebraMap_subalgebra_comp C
  exact (universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty).of_postcomp
    g h (universalHomeomorphism_specMap_subalgebra C) (hcomp ▸ hAB)

/-- If `Spec B → Spec A` is a universal homeomorphism with unchanged residue fields and `C` is
an intermediate subalgebra, then `Spec B → Spec C` has unchanged residue fields too. -/
lemma isIso_residueFieldMap_specMap_to_subalgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (hres : ∀ x : Spec (.of B), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op).residueFieldMap x))
    (C : Subalgebra A B) :
    ∀ x : Spec (.of B), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op).residueFieldMap x) := by
  let fCB := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op
  let fAC := Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op
  have hACres : ∀ x : Spec (.of C), IsIso (fAC.residueFieldMap x) :=
    isIso_residueFieldMap_specMap_subalgebra hres C
  intro x
  have hcomp : IsIso (fAC.residueFieldMap (fCB x) ≫ fCB.residueFieldMap x) := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (specMap_algebraMap_subalgebra_comp C) x]
    exact IsIso.comp_isIso' (Scheme.residueFieldCongr _).isIso_hom (hres x)
  exact (isIso_comp_left_iff _ _).mp hcomp

/-- If `Spec B → Spec C` is a universal homeomorphism for a subalgebra `C`, then so is the
morphism attached to the underlying subring of `C`. -/
lemma universalHomeomorphism_specMap_to_subring
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B)
    (hCB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op) := by
  let e := subalgebraToSubringEquiv C
  let g := Scheme.Spec.map (CommRingCat.ofHom (algebraMap C B)).op
  let j := Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op
  have hj : UniversalHomeomorphism j := by
    have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.symm.bijective
    exact universalHomeomorphism_of_isIso _
  have hcomp : g ≫ j =
      Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op := by
    change Scheme.Spec.map ((CommRingCat.ofHom (algebraMap C B)).op) ≫
      Scheme.Spec.map ((CommRingCat.ofHom e.symm.toRingHom).op) =
      Scheme.Spec.map (CommRingCat.ofHom C.toSubring.subtype).op
    rw [← Functor.map_comp]
    congr 1
  exact hcomp ▸
    universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition.comp_mem g j hCB hj

end AlgebraicGeometry

end
