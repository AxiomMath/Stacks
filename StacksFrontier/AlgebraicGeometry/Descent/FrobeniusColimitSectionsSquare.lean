module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorNoetherianCorners

/-!
# The cartesian square of `Γ(colim_F 𝒪, -)` at the two-generator almost blowup square

Let `p` be a prime. For a quasi-compact quasi-separated scheme `X` in characteristic `p` the
comparison `AlgebraicGeometry.frobeniusColimitSectionsComparison`

`colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)`

is bijective, so a cartesian square of Frobenius colimits of global functions is a cartesian
square of global sections of the Frobenius colimits of the structure sheaves. This file performs
that transport, and instantiates it at the almost blowup square of More on Flatness,
Example 0EVH, whose square of `colim_F Γ(-, 𝒪)` is cartesian by
`AlgebraicGeometry.isPullback_frobeniusColimit_twoGeneratorModel`.

The result is the identification

`Γ(colim_F 𝒪_X, X) = Γ(colim_F 𝒪_Z, Z) ×_{Γ(colim_F 𝒪_E, E)} Γ(colim_F 𝒪_{X'}, X')`

whose target is the object out of which the Hom-sets of
`AlgebraicGeometry.frobeniusColimitVectorBundles` are built; it is what the proof of Stacks Tag
0EXD uses for the full faithfulness of
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` on free modules.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitSectionsRestrictHom`: restriction of global sections of
  `colim_F 𝒪` along a morphism of schemes, as a morphism of types.
* `AlgebraicGeometry.frobeniusColimitSectionsIso`: **the comparison as an isomorphism**, for a
  quasi-compact quasi-separated scheme.

## Main results

* `AlgebraicGeometry.isPullback_frobeniusColimitSectionsRestrict_of_isPullback`: **a cartesian
  square of Frobenius colimits of global functions over quasi-compact quasi-separated schemes in
  characteristic `p` is a cartesian square of global sections of the Frobenius colimits of the
  structure sheaves.**
* `AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`: **the square of
  `Γ(colim_F 𝒪, -)` attached to the almost blowup square of Example 0EVH is cartesian.**

## Implementation notes

The transport is `CategoryTheory.IsPullback.of_iso` at the four comparison isomorphisms; its
four commutativity hypotheses are `AlgebraicGeometry.frobeniusColimitSectionsComparison_naturality`
at the four legs, turned from an equation of functions into an equation of morphisms of types by
`ext`.

Morphisms of `Type u` are not functions: `A ⟶ B` is the structure `TypeCat.Hom A B` wrapping
one. So `TypeCat.ofHom` (`↾`) is applied once, in
`AlgebraicGeometry.frobeniusColimitSectionsRestrictHom`, and the cartesian squares are stated
with that.

The two Proj corners of the square are quasi-compact by
`Stacks.AlmostBlowUp.compactSpace_proj_modificationGrading` and by
`Stacks.ProjAmple.compactSpace_proj_polyGrading` — the exceptional corner is the projective line
over the centre, so its grading *is* a polynomial grading — and quasi-separated because every
`Proj` is (`Stacks.AlgebraicGeometry.ProjQuasiSeparated.quasiSeparatedSpace_proj`).

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.AlmostBlowUp TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **Restriction of global sections of `colim_F 𝒪` along a morphism of schemes**, as a morphism
of types. This is `AlgebraicGeometry.frobeniusColimitSectionsRestrict` read in the category of
types, which is where a cartesian square lives. -/
noncomputable def frobeniusColimitSectionsRestrictHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    ToType ((frobeniusColimitRingSheaf Y p hY).obj.obj (op ⊤)) ⟶
      ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤)) :=
  ↾(frobeniusColimitSectionsRestrict p f hX hY)

/-- **The comparison `colim_F Γ(X, 𝒪) ⟶ Γ(colim_F 𝒪_X, X)` as an isomorphism of types**, for a
quasi-compact quasi-separated scheme in characteristic `p`. -/
noncomputable def frobeniusColimitSectionsIso (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (frobeniusColimitGlobalSections.{u} p).obj (op X) ≅
      ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤)) :=
  (Equiv.ofBijective _ (bijective_frobeniusColimitSectionsComparison X p hX)).toIso

/-- The forward direction of the comparison isomorphism is the comparison. -/
lemma frobeniusColimitSectionsIso_hom_apply (X : Scheme.{u}) (hX : IsInCharacteristic X p)
    [CompactSpace X] [QuasiSeparatedSpace X]
    (x : (frobeniusColimitGlobalSections.{u} p).obj (op X)) :
    (frobeniusColimitSectionsIso p X hX).hom x =
      frobeniusColimitSectionsComparison X p hX x := rfl

/-- **The comparison turns restriction of Frobenius colimits of global functions into
restriction of global sections of the Frobenius colimits**, as an equation of morphisms of
types. This is `AlgebraicGeometry.frobeniusColimitSectionsComparison_naturality` read in the
category of types. -/
lemma frobeniusColimitGlobalSections_map_comp_frobeniusColimitSectionsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (frobeniusColimitGlobalSections.{u} p).map f.op ≫
        (frobeniusColimitSectionsIso p X hX).hom =
      (frobeniusColimitSectionsIso p Y hY).hom ≫
        frobeniusColimitSectionsRestrictHom p f hX hY := by
  ext x
  exact frobeniusColimitSectionsComparison_naturality p f hX hY x

/-- **A cartesian square of Frobenius colimits of global functions over quasi-compact
quasi-separated schemes in characteristic `p` is a cartesian square of global sections of the
Frobenius colimits of the structure sheaves.** The comparison is bijective at each of the four
corners, and natural in the scheme, so this is `CategoryTheory.IsPullback.of_iso`.

The statement is made for an arbitrary commutative square, so that nothing about almost blowup
squares enters; the instance it is used at is the square of Example 0EVH. -/
theorem isPullback_frobeniusColimitSectionsRestrict_of_isPullback {X X' Z E : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace E] [QuasiSeparatedSpace E]
    (h : IsPullback ((frobeniusColimitGlobalSections.{u} p).map z.op)
      ((frobeniusColimitGlobalSections.{u} p).map b.op)
      ((frobeniusColimitGlobalSections.{u} p).map e.op)
      ((frobeniusColimitGlobalSections.{u} p).map d.op)) :
    IsPullback (frobeniusColimitSectionsRestrictHom p z hZ hX)
      (frobeniusColimitSectionsRestrictHom p b hX' hX)
      (frobeniusColimitSectionsRestrictHom p e hE hZ)
      (frobeniusColimitSectionsRestrictHom p d hE hX') :=
  h.of_iso (frobeniusColimitSectionsIso p X hX) (frobeniusColimitSectionsIso p Z hZ)
    (frobeniusColimitSectionsIso p X' hX') (frobeniusColimitSectionsIso p E hE)
    (frobeniusColimitGlobalSections_map_comp_frobeniusColimitSectionsIso p z hZ hX)
    (frobeniusColimitGlobalSections_map_comp_frobeniusColimitSectionsIso p b hX' hX)
    (frobeniusColimitGlobalSections_map_comp_frobeniusColimitSectionsIso p e hE hZ)
    (frobeniusColimitGlobalSections_map_comp_frobeniusColimitSectionsIso p d hE hX')

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The modification of the two-generator square is quasi-compact. -/
instance compactSpace_twoGeneratorModification (A : Type u) [CommRing A] (f₁ f₂ : A) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    CompactSpace (Proj (modificationGrading A f₁ f₂)) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  compactSpace_proj_modificationGrading A f₁ f₂

/-- The exceptional fibre of the two-generator square is quasi-compact: it is the projective
line over the centre. -/
instance compactSpace_twoGeneratorExceptional (A : Type u) [CommRing A] (f₁ f₂ : A) :
    CompactSpace (Proj (exceptionalGrading A f₁ f₂)) :=
  Stacks.ProjAmple.compactSpace_proj_polyGrading (centerRing A f₁ f₂) 1

/-- **The square of `Γ(colim_F 𝒪, -)` attached to the almost blowup square of Example 0EVH is
cartesian.**

This is the identification
`Γ(colim_F 𝒪_X, X) = Γ(colim_F 𝒪_Z, Z) ×_{Γ(colim_F 𝒪_E, E)} Γ(colim_F 𝒪_{X'}, X')`,
the form in which the proof of Stacks Tag 0EXD uses the cartesianness of Stacks 0EVK: the
Hom-sets of `AlgebraicGeometry.frobeniusColimitVectorBundles` are built from global sections of
`colim_F 𝒪` and not from `colim_F Γ(-, 𝒪)`. -/
theorem isPullback_frobeniusColimitSections_twoGenerator (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsPullback
      (frobeniusColimitSectionsRestrictHom p (centerToBase A f₁ f₂)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_spec A p hpA))
      (frobeniusColimitSectionsRestrictHom p (modificationToBase A f₁ f₂)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_spec A p hpA))
      (frobeniusColimitSectionsRestrictHom p (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
      (frobeniusColimitSectionsRestrictHom p (exceptionalToModification A f₁ f₂)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hcast : (p : Γ(Spec (.of A), ⊤)) = 0 :=
    cast_eq_zero_of_isInCharacteristic (isInCharacteristic_spec A p hpA) ⊤
  refine isPullback_frobeniusColimitSectionsRestrict_of_isPullback p
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂) _ _ _ _ ?_
  exact isPullback_frobeniusColimit_twoGeneratorModel p hp A f₁ f₂ hcast _
    (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    (twoGenerator_isPullback A f₁ f₂).flip

end AlgebraicGeometry

end
