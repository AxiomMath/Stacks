module

public import StacksFrontier.AlgebraicGeometry.Descent.FreeHomMatrixPullback
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeHomMatrix
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSectionsSquare
public import StacksFrontier.CategoryTheory.Limits.IsPullbackPiType

/-!
# The cartesian square of Hom-sets of free Frobenius-colimit bundles at Example 0EVH

Let `p` be a prime. For a morphism `f : X ⟶ Y` of schemes in characteristic `p` the transition
functor of Stacks Tag 0EXE is extension of scalars along the canonical morphism
`colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)`, and it carries a free `colim_F 𝒪_Y`-module to a free
`colim_F 𝒪_X`-module. Conjugated by that identification it is a map

`((colim_F 𝒪_Y)^{⊕I} ⟶ (colim_F 𝒪_Y)^{⊕L}) ⟶ ((colim_F 𝒪_X)^{⊕I} ⟶ (colim_F 𝒪_X)^{⊕L})`

of Hom-sets, and on matrices it is `AlgebraicGeometry.frobeniusColimitSectionsRestrict`
entrywise. Consequently a cartesian square of global sections of the Frobenius colimits of the
structure sheaves gives a **cartesian square of Hom-sets of free modules**, and at the almost
blowup square of More on Flatness, Example 0EVH, the square of global sections is cartesian by
`AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`.

This is the full faithfulness half of Stacks Tag 0EXD at *free* modules: a morphism of
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`'s target over a pair of free modules
is a pair of morphisms over `Z` and over `X'` agreeing over `E`, and the square below says
exactly that such a pair comes from a unique morphism over `X`.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitFreeHomRestrict`: **the transition map on Hom-sets of free
  `colim_F 𝒪`-modules**, as a morphism of types.

## Main results

* `AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom`: **the transition map
  acts on the matrix of a morphism of free modules entrywise by
  `AlgebraicGeometry.frobeniusColimitSectionsRestrict`.**
* `AlgebraicGeometry.isPullback_frobeniusColimitFreeHomRestrict_of_isPullback`: **a cartesian
  square of global sections of the Frobenius colimits gives a cartesian square of Hom-sets of
  free modules.**
* `AlgebraicGeometry.isPullback_frobeniusColimitFreeHom_twoGenerator`: **the square of Hom-sets
  of free modules attached to the almost blowup square of Example 0EVH is cartesian**, under
  exactly the hypotheses of Example 0EVH: a ring `A`, two elements of it, and a prime `p` which
  vanishes in `A`.
* `AlgebraicGeometry.isPullback_frobeniusColimitFreeHom_twoGenerator_zmodTwo`: those hypotheses
  are inhabited, so the previous theorem is not vacuously true.

## Implementation notes

**No `@[stacks 0EXD]` attribute appears in this file.** What the tag asserts is that
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence; the square proved
here is its full faithfulness at free modules only, and neither the passage from free modules to
finite locally free ones — which asks for the same square over each member of a trivialising
affine cover of `Spec A` — nor essential surjectivity is proved here.

The transport is `CategoryTheory.IsPullback.of_iso` along the matrix description of the four
Hom-sets, whose four commutativity hypotheses are
`AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom` at the four legs. The
cartesian square of matrices is the cartesian square of global sections pushed through
`CategoryTheory.Limits.Types.isPullback_matrix`.

No quasi-compactness or quasi-separatedness hypothesis appears: the matrix description of the
Hom-sets of free modules is over the *top open*, which is the terminal object of the site of
opens, and there no sheaf condition has to be solved. Those hypotheses are needed only to
identify the global sections of `colim_F 𝒪_X` with `colim_F Γ(X, 𝒪)`, which is already done
inside `AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`.

**Why the entrywise lemma is proved through the coordinate form.** Stated directly at
`Stacks.SheafOfModules.freeHomMatrixEquiv`, the instantiation of
`Stacks.SheafOfModules.freeHomMatrixEquiv_pullbackFreeHom` at a concrete morphism of schemes
times out in `whnf`: the generic statement's terminal object downstairs is
`(Opens.map f.base).obj ⊤`, the concrete one is `⊤`, and forcing that identification underneath
the composite equivalence is what costs. Unfolding both sides to
`Stacks.SheafOfModules.freeCoord` first — which
`Stacks.SheafOfModules.freeHomMatrixEquiv_apply` does by definition — and applying the
terminality-free `Stacks.SheafOfModules.freeCoord_pullbackFreeHom` leaves the same
identification underneath nothing but a coordinate projection, where it is immediate.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.AlmostBlowUp TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **The transition map on Hom-sets of free `colim_F 𝒪`-modules**, as a morphism of types: the
transition functor of Stacks Tag 0EXE carries free modules to free modules, and
`Stacks.SheafOfModules.pullbackFreeHom` is its action on a morphism of free modules, conjugated
by that identification. -/
noncomputable def frobeniusColimitFreeHomRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (I L : Type u) :
    (SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I ⟶
        SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) L) ⟶
      (SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I ⟶
        SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L) :=
  ↾(Stacks.SheafOfModules.pullbackFreeHom (frobeniusColimitStructureSheafHom p f hX hY) I L)

/-- **The transition map acts entrywise on the matrix of a morphism of free modules.** The
`(i, k)` entry of the matrix of the transition of `g` is the restriction along `f` of the
`(i, k)` entry of the matrix of `g`. -/
theorem frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (I L : Type u) [Fintype L] [DecidableEq L]
    (g : SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I ⟶
      SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) L) (i : I) (k : L) :
    frobeniusColimitFreeHomMatrixEquiv X p hX I L
        (Stacks.SheafOfModules.pullbackFreeHom
          (frobeniusColimitStructureSheafHom p f hX hY) I L g) i k =
      frobeniusColimitSectionsRestrict p f hX hY
        (frobeniusColimitFreeHomMatrixEquiv Y p hY I L g i k) := by
  simp only [frobeniusColimitFreeHomMatrixEquiv,
    Stacks.SheafOfModules.freeHomMatrixEquiv_apply]
  exact Stacks.SheafOfModules.freeCoord_pullbackFreeHom
    (frobeniusColimitStructureSheafHom p f hX hY) I L g i k ⊤

/-- **The matrix description of the Hom-set of free `colim_F 𝒪_X`-modules, as an isomorphism of
types**, in the direction a cartesian square of matrices is transported along. -/
noncomputable def frobeniusColimitFreeHomMatrixIso (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (I L : Type u) [Fintype L] [DecidableEq L] :
    (I → L → ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤))) ≅
      (SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I ⟶
        SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L) :=
  (frobeniusColimitFreeHomMatrixEquiv X p hX I L).symm.toIso

/-- **The matrix description is compatible with the transition maps.** Restricting a matrix
entrywise and then reading it as a morphism of free modules is reading it as a morphism of free
modules and then applying the transition map. This is
`AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom` read as an equation of
morphisms of types. -/
theorem frobeniusColimitFreeHomMatrixIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (I L : Type u) [Fintype L] [DecidableEq L] :
    (↾fun (M : I → L → ToType ((frobeniusColimitRingSheaf Y p hY).obj.obj (op ⊤)))
          (i : I) (k : L) => frobeniusColimitSectionsRestrictHom p f hX hY (M i k)) ≫
        (frobeniusColimitFreeHomMatrixIso p X hX I L).hom =
      (frobeniusColimitFreeHomMatrixIso p Y hY I L).hom ≫
        frobeniusColimitFreeHomRestrict p f hX hY I L := by
  have key : ∀ M : I → L → ToType ((frobeniusColimitRingSheaf Y p hY).obj.obj (op ⊤)),
      (frobeniusColimitFreeHomMatrixEquiv X p hX I L).symm
          (fun i k => frobeniusColimitSectionsRestrict p f hX hY (M i k)) =
        Stacks.SheafOfModules.pullbackFreeHom
          (frobeniusColimitStructureSheafHom p f hX hY) I L
          ((frobeniusColimitFreeHomMatrixEquiv Y p hY I L).symm M) := fun M =>
    (Equiv.symm_apply_eq _).2 <| funext₂ fun i k => by
      rw [frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom p f hX hY I L _ i k,
        Equiv.apply_symm_apply]
  ext : 2
  funext M
  exact key M

/-- **A cartesian square of global sections of the Frobenius colimits gives a cartesian square of
Hom-sets of free modules.** The Hom-set of free modules is a set of matrices over the global
sections of `colim_F 𝒪`, the transition maps act on those matrices entrywise, and taking matrices
preserves cartesian squares of types.

The statement is made for an arbitrary square of schemes in characteristic `p`, so that nothing
about almost blowup squares enters; the instance it is used at is the square of Example 0EVH. -/
theorem isPullback_frobeniusColimitFreeHomRestrict_of_isPullback {X X' Z E : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
    (I L : Type u) [Finite L]
    (h : IsPullback (frobeniusColimitSectionsRestrictHom p z hZ hX)
      (frobeniusColimitSectionsRestrictHom p b hX' hX)
      (frobeniusColimitSectionsRestrictHom p e hE hZ)
      (frobeniusColimitSectionsRestrictHom p d hE hX')) :
    IsPullback (frobeniusColimitFreeHomRestrict p z hZ hX I L)
      (frobeniusColimitFreeHomRestrict p b hX' hX I L)
      (frobeniusColimitFreeHomRestrict p e hE hZ I L)
      (frobeniusColimitFreeHomRestrict p d hE hX' I L) := by
  classical
  let := Fintype.ofFinite L
  exact (Types.isPullback_matrix h I L).of_iso
    (frobeniusColimitFreeHomMatrixIso p X hX I L) (frobeniusColimitFreeHomMatrixIso p Z hZ I L)
    (frobeniusColimitFreeHomMatrixIso p X' hX' I L)
    (frobeniusColimitFreeHomMatrixIso p E hE I L)
    (frobeniusColimitFreeHomMatrixIso_naturality p z hZ hX I L)
    (frobeniusColimitFreeHomMatrixIso_naturality p b hX' hX I L)
    (frobeniusColimitFreeHomMatrixIso_naturality p e hE hZ I L)
    (frobeniusColimitFreeHomMatrixIso_naturality p d hE hX' I L)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The square of Hom-sets of free `colim_F 𝒪`-modules attached to the almost blowup square of
Example 0EVH is cartesian.**

This is the full faithfulness of Stacks Tag 0EXD's comparison functor at *free* modules: a
morphism `(colim_F 𝒪_X)^{⊕I} ⟶ (colim_F 𝒪_X)^{⊕L}` is the same thing as a pair of morphisms over
the centre and over the modification which agree over the exceptional corner. The hypotheses are
exactly those of Example 0EVH — a ring `A`, elements `f₁, f₂` of it and a prime `p` with
`p = 0` in `A` — and they are not vacuous: they hold for `A = ZMod 2`, `f₁ = f₂ = 0` and
`p = 2`. -/
theorem isPullback_frobeniusColimitFreeHom_twoGenerator (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0)
    (I L : Type u) [Finite L] :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsPullback
      (frobeniusColimitFreeHomRestrict p (centerToBase A f₁ f₂)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_spec A p hpA) I L)
      (frobeniusColimitFreeHomRestrict p (modificationToBase A f₁ f₂)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_spec A p hpA) I L)
      (frobeniusColimitFreeHomRestrict p (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA) I L)
      (frobeniusColimitFreeHomRestrict p (exceptionalToModification A f₁ f₂)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA) I L) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact isPullback_frobeniusColimitFreeHomRestrict_of_isPullback p (modificationToBase A f₁ f₂)
    (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    _ _ _ _ I L (isPullback_frobeniusColimitSections_twoGenerator p hp A f₁ f₂ hpA)

/-- **The hypotheses of the previous theorem are inhabited**, so that it is not vacuously true:
they hold for `A = ZMod 2`, `f₁ = f₂ = 0` and `p = 2`, at one-dimensional free modules. -/
theorem isPullback_frobeniusColimitFreeHom_twoGenerator_zmodTwo :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI := (twoGeneratorSquare (ZMod 2) 0 0).modificationGraded
    IsPullback
      (frobeniusColimitFreeHomRestrict 2 (centerToBase (ZMod 2) 0 0)
        (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (by decide))
        (isInCharacteristic_spec (ZMod 2) 2 (by decide)) (Fin 1) (Fin 1))
      (frobeniusColimitFreeHomRestrict 2 (modificationToBase (ZMod 2) 0 0)
        (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (by decide))
        (isInCharacteristic_spec (ZMod 2) 2 (by decide)) (Fin 1) (Fin 1))
      (frobeniusColimitFreeHomRestrict 2 (exceptionalToCenter (ZMod 2) 0 0)
        (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (by decide))
        (isInCharacteristic_twoGeneratorCenter (ZMod 2) 0 0 2 (by decide)) (Fin 1) (Fin 1))
      (frobeniusColimitFreeHomRestrict 2 (exceptionalToModification (ZMod 2) 0 0)
        (isInCharacteristic_twoGeneratorExceptional (ZMod 2) 0 0 2 (by decide))
        (isInCharacteristic_twoGeneratorModification (ZMod 2) 0 0 2 (by decide))
        (Fin 1) (Fin 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := (twoGeneratorSquare (ZMod 2) 0 0).modificationGraded
  exact isPullback_frobeniusColimitFreeHom_twoGenerator 2 Nat.prime_two (ZMod 2) 0 0
    (by decide) (Fin 1) (Fin 1)

end AlgebraicGeometry

end
