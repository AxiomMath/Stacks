module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Factorizations through universal homeomorphisms, and relative normalization

A factorization of a morphism of schemes through a universal homeomorphism is an intermediate
scheme together with the two legs. These factorizations form a category, and so do the
factorizations whose second leg also induces isomorphisms on all residue fields. Weak
normalization and seminormalization are initial objects in those two categories.

Composing the first leg with the canonical morphism to the relative normalization turns a
factorization of the relative normalization of a morphism into a factorization of the morphism
itself, and this operation preserves initiality: a universal homeomorphism out of the relative
normalization is integral, so the universal property of the relative normalization produces the
comparison map, and `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext` makes it unique.

## Main definitions

* `AlgebraicGeometry.UniversalHomeomorphismFactorization` is the category of factorizations
  through universal homeomorphisms.
* `AlgebraicGeometry.SubintegralFactorization` is the category of factorizations whose second
  leg also induces isomorphisms on all residue fields.
* `AlgebraicGeometry.UniversalHomeomorphismFactorization.ofNormalization` composes the first
  leg of a factorization with the normalization map.
* `AlgebraicGeometry.SubintegralFactorization.ofNormalization` does the same for factorizations
  inducing residue-field isomorphisms.

## Main results

* `AlgebraicGeometry.UniversalHomeomorphismFactorization.isInitial_ofNormalization` transfers
  initiality in the universal-homeomorphism category.
* `AlgebraicGeometry.SubintegralFactorization.isInitial_ofNormalization` transfers initiality in
  the residue-field-isomorphism category.

## Implementation notes

The two factorization categories are defined here, independently of the existence theorems that
produce their initial objects; those theorems import this module, so their proofs can use the
normalization reduction without a dependency cycle.

Dominance is not needed for this reduction; relative normalization and its universal property
only require quasi-compactness and quasi-separatedness.

## References

* [Stacks Project, Tag 0H3N](https://stacks.math.columbia.edu/tag/0H3N),
  first paragraph of the proof, using Tags 035I and 04DF.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A factorization of `f` whose second map is a universal homeomorphism. -/
public structure UniversalHomeomorphismFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) where
  /-- The intermediate scheme. -/
  middle : Scheme.{u}
  /-- The map from the source to the intermediate scheme. -/
  toMiddle : Y ⟶ middle
  /-- The universal homeomorphism to the target. -/
  toBase : middle ⟶ X
  /-- The two maps form a factorization of `f`. -/
  fac : toMiddle ≫ toBase = f
  /-- The second map is a universal homeomorphism. -/
  universalHomeomorphism : UniversalHomeomorphism toBase

namespace UniversalHomeomorphismFactorization

variable {Y X : Scheme.{u}} {f : Y ⟶ X}

/-- A morphism of factorizations is a morphism of their intermediate schemes
compatible with both maps in the factorization. -/
@[ext]
public structure Hom (A B : UniversalHomeomorphismFactorization f) where
  /-- The map of intermediate schemes. -/
  hom : A.middle ⟶ B.middle
  /-- Compatibility with the map from the source. -/
  toMiddle_hom : A.toMiddle ≫ hom = B.toMiddle := by aesop_cat
  /-- Compatibility with the map to the target. -/
  hom_toBase : hom ≫ B.toBase = A.toBase := by aesop_cat

/-- The category of factorizations of `f` through a universal homeomorphism, with morphisms the
compatible maps of intermediate schemes. -/
public instance : Category.{u} (UniversalHomeomorphismFactorization f) where
  Hom := Hom
  id A := ⟨𝟙 A.middle, by simp, by simp⟩
  comp α β :=
    ⟨α.hom ≫ β.hom,
      by rw [← Category.assoc, α.toMiddle_hom, β.toMiddle_hom],
      by rw [Category.assoc, β.hom_toBase, α.hom_toBase]⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; simp [Category.assoc]

end UniversalHomeomorphismFactorization

/-- A factorization of `f` whose second map is a universal homeomorphism and
induces isomorphisms on all residue fields. -/
public structure SubintegralFactorization {Y X : Scheme.{u}} (f : Y ⟶ X) where
  /-- The intermediate scheme. -/
  middle : Scheme.{u}
  /-- The map from the source to the intermediate scheme. -/
  toMiddle : Y ⟶ middle
  /-- The subintegral map to the target. -/
  toBase : middle ⟶ X
  /-- The two maps form a factorization of `f`. -/
  fac : toMiddle ≫ toBase = f
  /-- The map to the target is a universal homeomorphism. -/
  universalHomeomorphism : UniversalHomeomorphism toBase
  /-- The map to the target induces isomorphisms on residue fields. -/
  residueFieldIsomorphisms : ∀ x : middle, IsIso (toBase.residueFieldMap x)

namespace SubintegralFactorization

variable {Y X : Scheme.{u}} {f : Y ⟶ X}

/-- A morphism of factorizations is a morphism of their intermediate schemes
compatible with both maps in the factorization. -/
@[ext]
public structure Hom (A B : SubintegralFactorization f) where
  /-- The map of intermediate schemes. -/
  hom : A.middle ⟶ B.middle
  /-- Compatibility with the map from the source. -/
  toMiddle_hom : A.toMiddle ≫ hom = B.toMiddle := by aesop_cat
  /-- Compatibility with the map to the target. -/
  hom_toBase : hom ≫ B.toBase = A.toBase := by aesop_cat

/-- The category of subintegral factorizations of `f`, with morphisms the compatible maps of
intermediate schemes. -/
public instance : Category.{u} (SubintegralFactorization f) where
  Hom := Hom
  id A := ⟨𝟙 A.middle, by simp, by simp⟩
  comp α β := ⟨α.hom ≫ β.hom, by rw [← Category.assoc, α.toMiddle_hom, β.toMiddle_hom],
    by rw [Category.assoc, β.hom_toBase, α.hom_toBase]⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; simp [Category.assoc]

end SubintegralFactorization

namespace UniversalHomeomorphismFactorization

/-- Compose the first leg of a factorization with the normalization map. -/
public def ofNormalization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (A : UniversalHomeomorphismFactorization f.fromNormalization) :
    UniversalHomeomorphismFactorization f where
  middle := A.middle
  toMiddle := f.toNormalization ≫ A.toMiddle
  toBase := A.toBase
  fac := by rw [Category.assoc, A.fac, f.toNormalization_fromNormalization]
  universalHomeomorphism := A.universalHomeomorphism

/-- Initiality among universal-homeomorphism factorizations passes from the
relative normalization to the original morphism. -/
public noncomputable def isInitial_ofNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (A : UniversalHomeomorphismFactorization f.fromNormalization)
    (hA : Limits.IsInitial A) :
    Limits.IsInitial (ofNormalization f A) := by
  refine Limits.IsInitial.ofUniqueHom (fun B => ?_) (fun B m => ?_)
  · have : IsIntegralHom B.toBase :=
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        B.toBase).mp B.universalHomeomorphism |>.1
    let k := f.normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₁ : f.toNormalization ≫ k = B.toMiddle := by
      dsimp [k]
      exact f.toNormalization_normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₂ : k ≫ B.toBase = f.fromNormalization := by
      dsimp [k]
      exact f.normalizationDesc_comp B.toMiddle B.toBase B.fac.symm
    let B' : UniversalHomeomorphismFactorization f.fromNormalization :=
      ⟨B.middle, k, B.toBase, hk₂, B.universalHomeomorphism⟩
    let α := hA.to B'
    refine ⟨α.hom, ?_, ?_⟩
    · change f.toNormalization ≫ A.toMiddle ≫ α.hom = B.toMiddle
      calc
        f.toNormalization ≫ A.toMiddle ≫ α.hom = f.toNormalization ≫ k := by
          simp [B', α.toMiddle_hom]
        _ = B.toMiddle := hk₁
    · exact α.hom_toBase
  · have : IsIntegralHom B.toBase :=
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        B.toBase).mp B.universalHomeomorphism |>.1
    let k := f.normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₁ : f.toNormalization ≫ k = B.toMiddle := by
      dsimp [k]
      exact f.toNormalization_normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₂ : k ≫ B.toBase = f.fromNormalization := by
      dsimp [k]
      exact f.normalizationDesc_comp B.toMiddle B.toBase B.fac.symm
    let B' : UniversalHomeomorphismFactorization f.fromNormalization :=
      ⟨B.middle, k, B.toBase, hk₂, B.universalHomeomorphism⟩
    let α := hA.to B'
    apply Hom.ext
    let mhom : A.middle ⟶ B.middle := m.hom
    have msrc : f.toNormalization ≫ A.toMiddle ≫ mhom = B.toMiddle := by
      simpa [mhom, ofNormalization, Category.assoc] using m.toMiddle_hom
    have mbase : mhom ≫ B.toBase = A.toBase := by
      simpa [mhom, ofNormalization] using m.hom_toBase
    have hbase : (A.toMiddle ≫ mhom) ≫ B.toBase = f.fromNormalization := by
      calc
        (A.toMiddle ≫ mhom) ≫ B.toBase = A.toMiddle ≫ A.toBase := by
          rw [Category.assoc, mbase]
        _ = f.fromNormalization := A.fac
    have hpre : f.toNormalization ≫ (A.toMiddle ≫ mhom) = f.toNormalization ≫ k := by
      calc
        f.toNormalization ≫ (A.toMiddle ≫ mhom) = B.toMiddle := by
          simpa [Category.assoc] using msrc
        _ = f.toNormalization ≫ k := hk₁.symm
    have hcomp : A.toMiddle ≫ mhom = k :=
      Scheme.Hom.normalization.hom_ext (f := f)
        (f₁ := A.toMiddle ≫ mhom) (f₂ := k) B.toBase hpre hbase hk₂
    let hm' : A ⟶ B' := ⟨mhom, hcomp, mbase⟩
    have heq : hm' = α := hA.hom_ext hm' α
    change mhom = (hA.to B').hom
    simpa [hm', α, B', k] using congrArg (fun t => t.hom) heq

end UniversalHomeomorphismFactorization

namespace SubintegralFactorization

/-- Compose the first leg of a residue-field-preserving factorization with the
normalization map. -/
public def ofNormalization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (A : SubintegralFactorization f.fromNormalization) :
    SubintegralFactorization f where
  middle := A.middle
  toMiddle := f.toNormalization ≫ A.toMiddle
  toBase := A.toBase
  fac := by rw [Category.assoc, A.fac, f.toNormalization_fromNormalization]
  universalHomeomorphism := A.universalHomeomorphism
  residueFieldIsomorphisms := A.residueFieldIsomorphisms

/-- Initiality among universal homeomorphisms inducing residue-field
isomorphisms passes from the relative normalization to the original morphism. -/
public noncomputable def isInitial_ofNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (A : SubintegralFactorization f.fromNormalization)
    (hA : Limits.IsInitial A) :
    Limits.IsInitial (ofNormalization f A) := by
  refine Limits.IsInitial.ofUniqueHom (fun B => ?_) (fun B m => ?_)
  · have : IsIntegralHom B.toBase :=
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        B.toBase).mp B.universalHomeomorphism |>.1
    let k := f.normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₁ : f.toNormalization ≫ k = B.toMiddle := by
      dsimp [k]
      exact f.toNormalization_normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₂ : k ≫ B.toBase = f.fromNormalization := by
      dsimp [k]
      exact f.normalizationDesc_comp B.toMiddle B.toBase B.fac.symm
    let B' : SubintegralFactorization f.fromNormalization :=
      ⟨B.middle, k, B.toBase, hk₂, B.universalHomeomorphism,
        B.residueFieldIsomorphisms⟩
    let α := hA.to B'
    refine ⟨α.hom, ?_, α.hom_toBase⟩
    · change f.toNormalization ≫ A.toMiddle ≫ α.hom = B.toMiddle
      simp [B', α.toMiddle_hom, hk₁]
  · have : IsIntegralHom B.toBase :=
      (universalHomeomorphism_iff_integral_universallyInjective_surjective
        B.toBase).mp B.universalHomeomorphism |>.1
    let k := f.normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₁ : f.toNormalization ≫ k = B.toMiddle := by
      dsimp [k]
      exact f.toNormalization_normalizationDesc B.toMiddle B.toBase B.fac.symm
    have hk₂ : k ≫ B.toBase = f.fromNormalization := by
      dsimp [k]
      exact f.normalizationDesc_comp B.toMiddle B.toBase B.fac.symm
    let B' : SubintegralFactorization f.fromNormalization :=
      ⟨B.middle, k, B.toBase, hk₂, B.universalHomeomorphism,
        B.residueFieldIsomorphisms⟩
    let α := hA.to B'
    apply Hom.ext
    let mhom : A.middle ⟶ B.middle := m.hom
    have msrc : f.toNormalization ≫ A.toMiddle ≫ mhom = B.toMiddle := by
      simpa [mhom, ofNormalization, Category.assoc] using m.toMiddle_hom
    have mbase : mhom ≫ B.toBase = A.toBase := by
      simpa [mhom, ofNormalization] using m.hom_toBase
    have hbase : (A.toMiddle ≫ mhom) ≫ B.toBase = f.fromNormalization := by
      calc
        (A.toMiddle ≫ mhom) ≫ B.toBase = A.toMiddle ≫ A.toBase := by
          rw [Category.assoc, mbase]
        _ = f.fromNormalization := A.fac
    have hpre : f.toNormalization ≫ (A.toMiddle ≫ mhom) = f.toNormalization ≫ k := by
      calc
        f.toNormalization ≫ (A.toMiddle ≫ mhom) = B.toMiddle := by
          simpa [Category.assoc] using msrc
        _ = f.toNormalization ≫ k := hk₁.symm
    have hcomp : A.toMiddle ≫ mhom = k :=
      Scheme.Hom.normalization.hom_ext (f := f)
        (f₁ := A.toMiddle ≫ mhom) (f₂ := k) B.toBase hpre hbase hk₂
    let hm' : A ⟶ B' := ⟨mhom, hcomp, mbase⟩
    have heq : hm' = α := hA.hom_ext hm' α
    change mhom = (hA.to B').hom
    simpa [hm', α, B', k] using congrArg (fun t => t.hom) heq

end SubintegralFactorization

end AlgebraicGeometry
