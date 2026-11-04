module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import StacksCore.Tactic.StacksAttribute

/-!
# The Frobenius colimit of the structure sheaf

Let `φ : R ⟶ R` be an endomorphism of an object of a category. Iterating `φ` gives the
sequential diagram `R → R → R → ⋯`, and when its colimit exists the morphism `φ` induces an
endomorphism of that colimit. **That induced endomorphism is always an isomorphism**: its
inverse is the morphism which reads the colimit leg at stage `n` as the leg at stage `n + 1`.
This is the structural reason the colimit along an endomorphism is the universal object on which
the endomorphism becomes invertible.

Specialising to the structure sheaf of a scheme `X` in characteristic `p` — where the relevant
endomorphism of `𝒪_X` is the `p`-th power map on sections, the map induced by the absolute
Frobenius — produces the sheaf of rings `colim_F 𝒪_X` on which Frobenius acts invertibly.

## Main definitions

* `CategoryTheory.Limits.endoSequence`: the sequential diagram `R → R → R → ⋯` all of whose
  transition maps are a given endomorphism `φ` of `R`.
* `CategoryTheory.Limits.endoColimitMap` and `CategoryTheory.Limits.endoColimitShift`: the
  endomorphism of `colim φ` induced by `φ` stage by stage, and the endomorphism obtained by
  shifting the colimit legs by one stage.
* `AlgebraicGeometry.frobeniusPresheafHom`: the endomorphism of the structure sheaf of a scheme
  in characteristic `p` which raises sections to their `p`-th powers.
* `AlgebraicGeometry.frobeniusColimitStructureSheaf`: the sheaf of rings `colim_F 𝒪_X`, the
  colimit of `𝒪_X` along that endomorphism.

## Main results

* `CategoryTheory.Limits.isIso_endoColimitMap`: the endomorphism induced by `φ` on the colimit
  of the iterates of `φ` is an isomorphism, with `endoColimitShift φ` as its inverse.
* `AlgebraicGeometry.frobeniusPresheafHom_app_eq_absoluteFrobenius_app`: on sections this
  endomorphism of `𝒪_X` is the map induced by the absolute Frobenius of `X`.
* `AlgebraicGeometry.isIso_frobeniusColimitStructureSheafMap`: Frobenius acts invertibly on
  `colim_F 𝒪_X`.

## Implementation notes

The colimit legs of `endoSequence φ` are morphisms out of `(endoSequence φ).obj n`, which is the
object `R` but is not syntactically `R`; composing a leg with `φ` therefore produces terms whose
implicit object arguments differ while remaining definitionally equal, and rewriting fails on
them. `CategoryTheory.Limits.endoColimitι` is the colimit leg with its source pinned to `R`, so
that every statement about the legs is expressed at one and the same type and the two inverse
identities are ordinary rewrites.

The inverse of the induced endomorphism is the descent of the cocone whose leg at stage `n` is
the colimit leg at stage `n + 1`. Its legs are assembled by `CategoryTheory.NatTrans.ofSequence`,
which asks for naturality only across a single step `n ⟶ n + 1`; there the required identity is
exactly the colimit relation one stage up. The cocone is supplied as an anonymous structure
rather than as a named definition so that its summit reduces to the colimit by projection.

Colimits of sheaves of rings are available from `CategoryTheory.Sites.Limits` for a site whose
underlying category and morphisms lie in the same universe as the rings, which is the case for
the opens of a scheme. The instance is not found through the abbreviation `TopCat.Sheaf`, so
`CategoryTheory.Limits.ringSheafEndoColimit` records the construction once in the generic sheaf
setting and the structure sheaf of a scheme is obtained by applying it.

The endomorphism of `𝒪_X` is built on the structure *presheaf*, where the rings of sections are
reached without unfolding the sheaf condition, and only then packaged as a morphism of sheaves;
this keeps the section formula `g ↦ g ^ p` provable by rewriting. The zero ring, where `p` need
not be the characteristic, is covered by `Stacks.Frobenius.primePowerEndomorphism`.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe v u

namespace CategoryTheory.Limits

variable {𝒞 : Type u} [Category.{v} 𝒞] {R : 𝒞}

/-! ### The colimit along an endomorphism -/

/-- The sequential diagram `R → R → R → ⋯` all of whose transition maps are the endomorphism
`φ` of `R`. -/
def endoSequence (φ : R ⟶ R) : ℕ ⥤ 𝒞 :=
  Functor.ofSequence (X := fun _ ↦ R) (fun _ ↦ φ)

/-- Every stage of the diagram of iterates of `φ` is `R` itself. -/
lemma endoSequence_obj (φ : R ⟶ R) (n : ℕ) : (endoSequence φ).obj n = R := rfl

/-- A single step of the diagram of iterates of `φ` is `φ`. -/
@[simp]
lemma endoSequence_map_succ (φ : R ⟶ R) (n : ℕ) :
    (endoSequence φ).map (homOfLE (Nat.le_add_right n 1)) = φ :=
  Functor.ofSequence_map_homOfLE_succ _ n

variable (φ : R ⟶ R) [HasColimit (endoSequence φ)]

/-- The leg of the colimit of the iterates of `φ` at stage `n`, with its source read as `R`
rather than as the value of the diagram at `n`. -/
noncomputable abbrev endoColimitι (n : ℕ) : R ⟶ colimit (endoSequence φ) :=
  colimit.ι (endoSequence φ) n

/-- Passing from stage `n` to stage `n + 1` of the colimit absorbs one copy of `φ`. -/
lemma comp_endoColimitι_succ (n : ℕ) :
    φ ≫ endoColimitι φ (n + 1) = endoColimitι φ n := by
  have h := colimit.w (endoSequence φ) (homOfLE (Nat.le_add_right n 1))
  rw [endoSequence_map_succ] at h
  exact h

/-- The colimit legs, shifted by one stage, viewed as a family of morphisms into the colimit.
These are the legs of the cocone whose descent inverts the endomorphism induced by `φ`. -/
noncomputable def endoSequenceShift :
    endoSequence φ ⟶ (Functor.const ℕ).obj (colimit (endoSequence φ)) :=
  NatTrans.ofSequence (fun n ↦ endoColimitι φ (n + 1))
    (fun n ↦ by
      simp only [endoSequence_map_succ, Functor.const_obj_map]
      exact (comp_endoColimitι_succ φ (n + 1)).trans (Category.comp_id _).symm)

/-- The endomorphism of `colim φ` induced by `φ` at every stage of the diagram. -/
noncomputable def endoColimitMap : colimit (endoSequence φ) ⟶ colimit (endoSequence φ) :=
  colimMap (NatTrans.ofSequence (F := endoSequence φ) (G := endoSequence φ)
    (fun _ ↦ φ) (fun n ↦ by simp only [endoSequence_map_succ]; rfl))

/-- The endomorphism of `colim φ` which reads the leg at stage `n` as the leg at stage
`n + 1`. -/
noncomputable def endoColimitShift : colimit (endoSequence φ) ⟶ colimit (endoSequence φ) :=
  colimit.desc _ { pt := colimit (endoSequence φ), ι := endoSequenceShift φ }

/-- The endomorphism induced by `φ` acts on the stage-`n` leg by precomposition with `φ`. -/
lemma endoColimitι_comp_endoColimitMap (n : ℕ) :
    endoColimitι φ n ≫ endoColimitMap φ = φ ≫ endoColimitι φ n := by
  rw [endoColimitMap]
  exact ι_colimMap _ n

/-- The shift carries the stage-`n` leg to the stage-`n + 1` leg. -/
lemma endoColimitι_comp_endoColimitShift (n : ℕ) :
    endoColimitι φ n ≫ endoColimitShift φ = endoColimitι φ (n + 1) := by
  rw [endoColimitShift]
  exact colimit.ι_desc _ n

/-- An endomorphism of `colim φ` fixing every colimit leg is the identity. -/
private lemma eq_id_of_endoColimitι_comp_eq
    (f : colimit (endoSequence φ) ⟶ colimit (endoSequence φ))
    (h : ∀ n, endoColimitι φ n ≫ f = endoColimitι φ n) : f = 𝟙 _ :=
  colimit.hom_ext fun n ↦ (h n).trans (Category.comp_id _).symm

/-- The shift is a right inverse of the endomorphism induced by `φ`. -/
lemma endoColimitMap_comp_endoColimitShift :
    endoColimitMap φ ≫ endoColimitShift φ = 𝟙 _ :=
  eq_id_of_endoColimitι_comp_eq φ _ fun n ↦ by
    rw [← Category.assoc, endoColimitι_comp_endoColimitMap, Category.assoc,
      endoColimitι_comp_endoColimitShift, comp_endoColimitι_succ]

/-- The shift is a left inverse of the endomorphism induced by `φ`. -/
lemma endoColimitShift_comp_endoColimitMap :
    endoColimitShift φ ≫ endoColimitMap φ = 𝟙 _ :=
  eq_id_of_endoColimitι_comp_eq φ _ fun n ↦ by
    rw [← Category.assoc, endoColimitι_comp_endoColimitShift,
      endoColimitι_comp_endoColimitMap, comp_endoColimitι_succ]

/-- **An endomorphism becomes invertible on the colimit of its own iterates.** The
endomorphism of `colim φ` induced by `φ` is an isomorphism, with inverse the shift of the
colimit legs by one stage. -/
instance isIso_endoColimitMap : IsIso (endoColimitMap φ) :=
  ⟨endoColimitShift φ, endoColimitMap_comp_endoColimitShift φ,
    endoColimitShift_comp_endoColimitMap φ⟩

/-- The automorphism of `colim φ` induced by `φ`. -/
noncomputable def endoColimitMapIso : colimit (endoSequence φ) ≅ colimit (endoSequence φ) :=
  asIso (endoColimitMap φ)

/-! ### The colimit of a sheaf of rings along an endomorphism -/

section RingSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- The colimit of a sheaf of rings along an endomorphism of it. -/
noncomputable def ringSheafEndoColimit (ψ : S ⟶ S) : Sheaf J RingCat.{u} :=
  colimit (endoSequence ψ)

/-- The endomorphism induced by `ψ` on the colimit of the iterates of `ψ`. -/
noncomputable def ringSheafEndoColimitMap (ψ : S ⟶ S) :
    ringSheafEndoColimit ψ ⟶ ringSheafEndoColimit ψ :=
  endoColimitMap ψ

/-- An endomorphism of a sheaf of rings becomes invertible on the colimit of its iterates. -/
theorem isIso_ringSheafEndoColimitMap (ψ : S ⟶ S) : IsIso (ringSheafEndoColimitMap ψ) :=
  isIso_endoColimitMap ψ

end RingSheaf

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### Frobenius on the structure sheaf -/

/-- The endomorphism of the structure presheaf of a scheme in characteristic `p` which raises
every section to its `p`-th power. -/
@[sga "7 XXII 6.2" "(6.2.1), special case"]
noncomputable def frobeniusPresheafHom : X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom
    (primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U.unop))
  naturality := by
    intro U V f
    ext g
    change primePowerEndomorphism _ p
        (cast_eq_zero_of_isInCharacteristic hX V.unop) ((X.presheaf.map f) g) =
      X.presheaf.map f (primePowerEndomorphism _ p
        (cast_eq_zero_of_isInCharacteristic hX U.unop) g)
    rw [primePowerEndomorphism_apply, primePowerEndomorphism_apply, map_pow]

/-- On sections, the Frobenius endomorphism of the structure sheaf is the `p`-th power map. -/
@[simp]
lemma frobeniusPresheafHom_app_apply (U : X.Opens) (g : Γ(X, U)) :
    (frobeniusPresheafHom X p hX).app (op U) g = g ^ p :=
  primePowerEndomorphism_apply _ p (cast_eq_zero_of_isInCharacteristic hX U) g

/-- The Frobenius endomorphism of the structure sheaf is the map on sections induced by the
absolute Frobenius of the scheme. -/
@[sga "3 VIIA 4.1" "partial"]
lemma frobeniusPresheafHom_app_eq_absoluteFrobenius_app (U : X.Opens) (g : Γ(X, U)) :
    (frobeniusPresheafHom X p hX).app (op U) g = (absoluteFrobenius X p hX).app U g := by
  rw [frobeniusPresheafHom_app_apply, absoluteFrobenius_app_apply]

/-- The Frobenius endomorphism of the structure sheaf, as a morphism of sheaves of commutative
rings. -/
@[sga "3 VIIA 4.3.3"]
noncomputable def frobeniusSheafHom : X.sheaf ⟶ X.sheaf :=
  ⟨frobeniusPresheafHom X p hX⟩

/-- The Frobenius endomorphism of the structure sheaf, as a morphism of sheaves of rings. -/
@[sga "3 VIIA 4.3.3"]
noncomputable def frobeniusRingCatSheafHom : X.ringCatSheaf ⟶ X.ringCatSheaf :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).map (frobeniusSheafHom X p hX)

/-- The sheaf of rings `colim_F 𝒪_X` on a scheme `X` in characteristic `p`: the colimit of the
structure sheaf along the Frobenius endomorphism which raises sections to their `p`-th
powers. -/
noncomputable def frobeniusColimitStructureSheaf : TopCat.Sheaf RingCat.{u} X :=
  ringSheafEndoColimit (frobeniusRingCatSheafHom X p hX)

/-- The endomorphism of `colim_F 𝒪_X` induced by Frobenius. -/
noncomputable def frobeniusColimitStructureSheafMap :
    frobeniusColimitStructureSheaf X p hX ⟶ frobeniusColimitStructureSheaf X p hX :=
  ringSheafEndoColimitMap (frobeniusRingCatSheafHom X p hX)

/-- **Frobenius acts invertibly on `colim_F 𝒪_X`.** The endomorphism of the Frobenius colimit
of the structure sheaf induced by Frobenius is an isomorphism of sheaves of rings. -/
theorem isIso_frobeniusColimitStructureSheafMap :
    IsIso (frobeniusColimitStructureSheafMap X p hX) :=
  isIso_ringSheafEndoColimitMap _

end AlgebraicGeometry

end
