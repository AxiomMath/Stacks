module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.RingTheory.Artinian.Basic

/-!
# A scheme finite over a field: its stalks and its ring of global sections

Let `k` be a field and let `g : Y ⟶ Spec(k)` be a finite morphism. Then `Y` is affine, its ring
of global sections is a finite `k`-algebra, hence an Artinian ring, and `Y` is a finite discrete
space whose points correspond to the maximal ideals of that ring, the stalk at a point being the
localization there. This file records the two numerical consequences of that description:

* `dim_k Γ(Y, 𝒪_Y) = ∑_{y ∈ Y} dim_k 𝒪_{Y, y}`, because an Artinian ring is the product of its
  localizations at its maximal ideals;
* `dim_k 𝒪_{Y, y} = length(𝒪_{Y, y}) · [κ(y) : k]`, because the length of a module over a local
  ring counts the factors of a composition series, each of which is the residue field.

Multiplying the second by the first is the computation
`∑_y length(𝒪_{Y,y}) · [κ(y) : k] = dim_k Γ(Y, 𝒪_Y)`, which is the penultimate display in the
proof of [Stacks, Tag 0AZ3]: there it is attributed to [Stacks, Tag 02M0] "using that `D` is
affine", and the affineness is what the first item above is.

## Main results

* `AlgebraicGeometry.finite_globalSections_of_isFinite_over_field` — the ring of global sections
  is a finite `k`-module.
* `AlgebraicGeometry.finite_of_isFinite_over_field` — the space is finite.
* `AlgebraicGeometry.finite_stalk_of_isFinite_over_field` — each stalk is a finite `k`-module.
* `AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk` — the global sections are
  the product of the stalks.
* `Stacks.RingTheory.finrank_eq_length_mul_finrank_residueField` — the local computation, for a
  local ring finite over a field.
* `AlgebraicGeometry.finrank_stalk_eq_length_mul_finrank_residueField` — that computation at a
  stalk.

## Implementation notes

The `k`-algebra structures on `Γ(Y, 𝒪_Y)` and on a stalk are the ones induced by the structure
morphism, namely `k ⟶ Γ(Spec(k), 𝒪) ⟶ Γ(Y, 𝒪_Y) ⟶ 𝒪_{Y, y}`; they depend on `g` and not only
on the rings, so they are supplied inside the statements as `letI` rather than as instances.
This is the same spelling that `Stacks.Chow.cycleDegree_eq_sum_finrank` ([Stacks, Tag 0AZ2]) and,
in the namespace `Stacks.AlgebraicGeometry`,
`ProperSectionsGeom.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` use, so no
transport is needed between them.

The `k`-algebra structure on the residue field `κ(y)` is *not* supplied: it is Mathlib's
instance `IsLocalRing.ResidueField.algebra` applied to the `k`-algebra structure on the stalk,
which is exactly `k ⟶ 𝒪_{Y,y} ⟶ κ(y)`.

## References

* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.RingTheory

/-- **The dimension of a local ring finite over a field is its length times the degree of its
residue field.** Both sides count the same composition series: a composition series of `B` over
itself has `length(B)` steps and each step contributes a copy of the residue field, whose
dimension over `k` is `[κ(B) : k]`. -/
theorem finrank_eq_length_mul_finrank_residueField (k : Type u) [Field k] (B : Type v)
    [CommRing B] [IsLocalRing B] [Algebra k B] [Module.Finite k B] :
    Module.finrank k B =
      (Module.length B B).toNat * Module.finrank k (IsLocalRing.ResidueField B) := by
  have hlocal : IsLocalHom (algebraMap k B) :=
    ⟨fun a ha ↦ by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha
        exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have hfinκ : Module.Finite k (IsLocalRing.ResidueField B) :=
    Module.Finite.of_surjective
      ((Algebra.linearMap B (IsLocalRing.ResidueField B)).restrictScalars k)
      IsLocalRing.residue_surjective
  have hBB : Module.length B B ≠ ⊤ := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  have key := IsLocalRing.length_restrictScalars k B B
  rw [Module.length_eq_finrank k B,
    ← Module.length_eq_of_surjective (S := k) (M := IsLocalRing.ResidueField B)
      IsLocalRing.residue_surjective,
    Module.length_eq_finrank k (IsLocalRing.ResidueField B)] at key
  lift Module.length B B to ℕ using hBB with n hn
  simpa using congrArg ENat.toNat key

end Stacks.RingTheory

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- The ring of global sections of a scheme finite over a field is a finite module over that
field: the morphism being finite and the target affine, the map on global sections is finite,
and the isomorphism `k ≅ Γ(Spec(k), 𝒪)` is surjective. -/
theorem finite_globalSections_of_isFinite_over_field [IsFinite g] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.Finite k Γ(Y, ⊤) := by
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have htop : g.appTop.hom.Finite := Scheme.Hom.finite_appTop g
  have hΓ : ((Scheme.ΓSpecIso (.of k)).inv).hom.Finite :=
    RingHom.Finite.of_surjective _ ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
  exact RingHom.Finite.comp htop hΓ

/-- The ring of global sections of a scheme finite over a field is an Artinian ring. -/
theorem isArtinianRing_globalSections_of_isFinite_over_field [IsFinite g] :
    IsArtinianRing Γ(Y, ⊤) :=
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite k Γ(Y, ⊤) := finite_globalSections_of_isFinite_over_field k g
  IsArtinianRing.of_finite k _

/-- A scheme finite over a field has finitely many points: it is the spectrum of an Artinian
ring. -/
theorem finite_of_isFinite_over_field [IsFinite g] : Finite Y := by
  have : IsAffine Y := isAffine_of_isAffineHom g
  have := isArtinianRing_globalSections_of_isFinite_over_field k g
  exact Finite.of_equiv (PrimeSpectrum Γ(Y, ⊤)) (Scheme.homeoOfIso Y.isoSpec.symm).toEquiv

/-- A stalk of a scheme finite over a field is a finite module over that field: it is a
localization of the ring of global sections, which is Artinian, so the localization map is
surjective. -/
theorem finite_stalk_of_isFinite_over_field [IsFinite g] (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    Module.Finite k (Y.presheaf.stalk y) := by
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : Module.Finite k Γ(Y, ⊤) := finite_globalSections_of_isFinite_over_field k g
  have := isArtinianRing_globalSections_of_isFinite_over_field k g
  let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk y) := (Y.presheaf.germ ⊤ y (by simp)).hom.toAlgebra
  have : IsScalarTower k Γ(Y, ⊤) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  let q := (isAffineOpen_top Y).primeIdealOf ⟨y, by simp⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) q.asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk ⟨y, by simp⟩
  exact Module.Finite.of_surjective
    ((Algebra.linearMap Γ(Y, ⊤) (Y.presheaf.stalk y)).restrictScalars k)
    (IsArtinianRing.localization_surjective q.asIdeal.primeCompl (Y.presheaf.stalk y))

/-- **The ring of global sections of a scheme finite over a field is the product of its
stalks**, read as an equality of dimensions: an Artinian ring is the product of its
localizations at its maximal ideals, and those localizations are the stalks. -/
private theorem finrank_globalSections_eq_sum_finrank_stalk [IsAffine Y] [IsFinite g]
    [Fintype (MaximalSpectrum Γ(Y, ⊤))] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) =
      ∑ m : MaximalSpectrum Γ(Y, ⊤),
        letI : Algebra k (Y.presheaf.stalk ((isAffineOpen_top Y).fromSpec m.toPrimeSpectrum)) :=
          ((Y.presheaf.germ ⊤ ((isAffineOpen_top Y).fromSpec m.toPrimeSpectrum) (by simp)).hom.comp
            ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
        Module.finrank k (Y.presheaf.stalk ((isAffineOpen_top Y).fromSpec m.toPrimeSpectrum)) := by
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite k Γ(Y, ⊤) := finite_globalSections_of_isFinite_over_field k g
  have := isArtinianRing_globalSections_of_isFinite_over_field k g
  let A := Γ(Y, ⊤)
  let x (m : MaximalSpectrum A) := (isAffineOpen_top Y).fromSpec m.toPrimeSpectrum
  let R (m : MaximalSpectrum A) : Type u := Y.presheaf.stalk (x m)
  let : ∀ m : MaximalSpectrum A, Algebra A (R m) := fun m ↦
    (Y.presheaf.germ ⊤ (x m) (by simp)).hom.toAlgebra
  let : ∀ m : MaximalSpectrum A, Algebra k (R m) := fun m ↦
    ((Y.presheaf.germ ⊤ (x m) (by simp)).hom.comp (algebraMap k A)).toAlgebra
  have : ∀ m : MaximalSpectrum A, IsScalarTower k A (R m) := fun _ ↦
    IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ m : MaximalSpectrum A, IsLocalization.AtPrime (R m) m.asIdeal := fun m ↦
    (isAffineOpen_top Y).isLocalization_stalk' m.toPrimeSpectrum (by simp)
  let e : A ≃ₐ[A] (∀ m : MaximalSpectrum A, R m) :=
    AlgEquiv.ofBijective (Algebra.ofId A (∀ m : MaximalSpectrum A, R m))
      (MaximalSpectrum.algebraMap_pi_bijective A R)
  have : ∀ m : MaximalSpectrum A, Module.Finite k (R m) := fun m ↦
    finite_stalk_of_isFinite_over_field k g (x m)
  show Module.finrank k A = ∑ m : MaximalSpectrum A, Module.finrank k (R m)
  calc Module.finrank k A = Module.finrank k (∀ m : MaximalSpectrum A, R m) :=
        (e.toLinearEquiv.restrictScalars k).finrank_eq
    _ = _ := Module.finrank_pi_fintype k

/-- **The dimension of the ring of global sections of a scheme finite over a field is the sum of
the dimensions of its stalks.** This is
`AlgebraicGeometry.finrank_globalSections_eq_sum_finrank_stalk` reindexed along the bijection
between the maximal ideals of the ring of global sections and the points of the space. -/
theorem finrank_globalSections_eq_finsum_finrank_stalk [IsFinite g] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) =
      ∑ᶠ y : Y,
        letI : Algebra k (Y.presheaf.stalk y) :=
          ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
            ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
        Module.finrank k (Y.presheaf.stalk y) := by
  classical
  have : IsAffine Y := isAffine_of_isAffineHom g
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite k Γ(Y, ⊤) := finite_globalSections_of_isFinite_over_field k g
  have := isArtinianRing_globalSections_of_isFinite_over_field k g
  let : Fintype (MaximalSpectrum Γ(Y, ⊤)) := Fintype.ofFinite _
  have hb : Function.Bijective ((isAffineOpen_top Y).fromSpec) := by
    rw [IsAffineOpen.fromSpec_top]
    exact (Scheme.homeoOfIso Y.isoSpec.symm).bijective
  let e : MaximalSpectrum Γ(Y, ⊤) ≃ Y := Equiv.ofBijective
    (fun m ↦ (isAffineOpen_top Y).fromSpec m.toPrimeSpectrum)
    (hb.comp IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.bijective)
  rw [finrank_globalSections_eq_sum_finrank_stalk k g, ← finsum_comp_equiv e,
    finsum_eq_sum_of_fintype]
  rfl

/-- **The dimension of a stalk of a scheme finite over a field is the length of that stalk times
the degree of the residue field there.** This is
`Stacks.RingTheory.finrank_eq_length_mul_finrank_residueField` at the stalk, which is a local
ring finite over the field. -/
theorem finrank_stalk_eq_length_mul_finrank_residueField [IsFinite g] (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    Module.finrank k (Y.presheaf.stalk y) =
      (Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y)).toNat *
        Module.finrank k (IsLocalRing.ResidueField (Y.presheaf.stalk y)) :=
  let : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  have : Module.Finite k (Y.presheaf.stalk y) := finite_stalk_of_isFinite_over_field k g y
  Stacks.RingTheory.finrank_eq_length_mul_finrank_residueField k (Y.presheaf.stalk y)

end AlgebraicGeometry

end
