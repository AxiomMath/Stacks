module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.FreeBasis
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex on a finite family of sections is a complex of sheaves

Let `X` be a ringed space and let `f₁, …, f_r` be sections of its structure sheaf. The Koszul
complex `K_•(O_X, f₁, …, f_r)` of Stacks tag 062L is built in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Sequence` as a complex of *presheaves* of modules: its
degree-`n` term is the presheaf `U ↦ ⋀^n_{O_X(U)}(O_X(U)^r)` of sectionwise exterior powers.

This file proves that each of those presheaves is a **sheaf**, and promotes the complex to a chain
complex of sheaves of modules. The reason is that the degree-`n` term is free of rank `C(r, n)`
over the structure sheaf, with the basis of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.FreeBasis`: a presheaf of modules with a basis whose
index type does not depend on the open set, and whose basis vectors are preserved by restriction,
satisfies the sheaf condition as soon as the structure sheaf does, because a section is then the
same thing as a tuple of sections of the structure sheaf.

This is what makes the Koszul-regularity conditions of Stacks tag 063D parts (2) and (3) statable;
they are stated in `StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Regular`.

## Main definitions

* `Stacks.AlgebraicGeometry.SeqKoszul.piece`: the degree-`n` term of `K_•(O_X, f_•)` as a presheaf
  of modules.
* `Stacks.AlgebraicGeometry.SeqKoszul.sheafPiece`: the same, as a sheaf of modules.
* `Stacks.AlgebraicGeometry.SeqKoszul.diff`: the Koszul differential.
* `Stacks.AlgebraicGeometry.SeqKoszul.sheafComplex`: **`K_•(O_X, f₁, …, f_r)` as a chain complex of
  sheaves of modules.**

## Main results

* `PresheafOfModules.isSheaf_of_basis`: a presheaf of modules on a ringed space which has a
  restriction-compatible basis indexed by a fixed finite type is a sheaf.
* `PresheafOfModules.isSheaf_exteriorAlgebraPiece_finFree`: the sectionwise exterior powers of the
  free presheaf of modules of finite rank are sheaves.
* `Stacks.AlgebraicGeometry.SeqKoszul.sheafComplex_d`: the differential of the complex of sheaves
  is the Koszul differential.

## Implementation notes

**The sheaf condition is proved through unique gluing, not through a limit.** A presheaf of modules
which is a limit of sheaves is a sheaf (`PresheafOfModules.isSheaf_of_isLimit`), and the degree-`n`
term is a product of `C(r, n)` copies of the structure sheaf; but exhibiting it as a categorical
product means producing a limit cone whose apex is that presheaf on the nose, and the comparison
with the concrete product cone of `ModuleCat` has to be transported across a change of indexing
functor. Unique gluing (`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`) asks instead for a
statement about elements, which the coordinates of the basis reduce to unique gluing for the
structure sheaf, one coordinate at a time. The price is that the statement is for a ringed space
rather than for a general site; nothing below needs more.

**The universes of `RingedSpace` are pinned to be equal.** `RingedSpace.{u, v}` has `u` the
universe of the underlying space and `v` that of the rings; the sheaf condition for a presheaf
valued in `AddCommGrpCat.{v}` quantifies over index types in the universe of the space, and the
limits needed to express it exist only when the two agree. So the statements are for
`RingedSpace.{u, u}`, as the stalk statements of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk` are.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 063D](https://stacks.math.columbia.edu/tag/063D)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

open scoped ExteriorAlgebra

universe u

open AlgebraicGeometry

namespace PresheafOfModules

/-- **A presheaf of modules with a restriction-compatible basis is a sheaf.** If the sections of
`M` over every open set carry a basis indexed by one fixed finite type, and restriction carries
each basis vector to the basis vector with the same index, then `M` satisfies the sheaf condition:
a section is a tuple of sections of the structure sheaf, and those glue uniquely. -/
theorem isSheaf_of_basis (X : RingedSpace.{u, u})
    (M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    {T : Type*} [Finite T]
    (β : ∀ A : (Opens X)ᵒᵖ,
      Module.Basis T ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj A) (M.obj A))
    (hβ : ∀ {A B : (Opens X)ᵒᵖ} (g : A ⟶ B) (t : T), M.map g (β A t) = β B t) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf := by
  have := Fintype.ofFinite T
  have hrepr : ∀ {A B : (Opens X)ᵒᵖ} (g : A ⟶ B) (y : M.obj A) (t : T),
      (β B).repr (M.map g y) t = X.presheaf.map g ((β A).repr y t) :=
    fun g y t => Module.Basis.repr_map_of_map_basis (β _) (β _) (M.restrictₛₗ g)
      (fun t => hβ g t) y t
  have key : ∀ ⦃ι : Type u⦄ (V : ι → Opens X) (sf : ∀ i : ι, M.obj (op (V i))),
      (∀ i j : ι, M.map ((V i).infLELeft (V j)).op (sf i) =
        M.map ((V i).infLERight (V j)).op (sf j)) →
      ∃! s : M.obj (op (iSup V)), ∀ i : ι, M.map (Opens.leSupr V i).op s = sf i := by
    intro ι V sf hsf
    have hcompat : ∀ t : T, TopCat.Presheaf.IsCompatible X.presheaf V
        (fun i => (β (op (V i))).repr (sf i) t) := by
      intro t i j
      rw [← hrepr, ← hrepr, hsf i j]
    choose d hd hdu using fun t : T =>
      X.IsSheaf.isSheafUniqueGluing V (fun i => (β (op (V i))).repr (sf i) t) (hcompat t)
    refine ⟨∑ t : T, d t • β (op (iSup V)) t, ?_, ?_⟩
    · intro i
      show M.restrictₛₗ (Opens.leSupr V i).op _ = sf i
      rw [map_sum]
      conv_rhs => rw [← (β (op (V i))).sum_repr (sf i)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ, restrictₛₗ_apply, hβ]
      exact congrArg (fun c => c • β (op (V i)) t) (hd t i)
    · intro s' hs'
      have he : ∀ t : T, (β (op (iSup V))).repr s' t = d t := by
        intro t
        exact hdu t _ fun i => by rw [← hrepr, hs' i]
      conv_lhs => rw [← (β (op (iSup V))).sum_repr s']
      exact Finset.sum_congr rfl fun t _ => congrArg (fun c => c • β (op (iSup V)) t) (he t)
  exact (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier) M.presheaf).mpr key

/-- **The sectionwise exterior powers of a finite free presheaf of modules on a ringed space are
sheaves.** The degree-`n` piece is free of rank `C(r, n)` with the basis
`PresheafOfModules.exteriorFinFreeBasis`, whose vectors restriction preserves. -/
theorem isSheaf_exteriorAlgebraPiece_finFree (X : RingedSpace.{u, u}) (r n : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (exteriorAlgebraPiece (n : ℤ) (finFree X.presheaf r)).presheaf :=
  isSheaf_of_basis X _ (exteriorFinFreeBasis X.presheaf r n)
    fun g t => map_exteriorFinFreeBasis X.presheaf r n g t

end PresheafOfModules

namespace Stacks.AlgebraicGeometry.SeqKoszul

variable (X : RingedSpace.{u, u}) (r : ℕ)

/-- The sheaf of rings of a ringed space, read in `RingCat`: this is the base over which the terms
of the Koszul complex are sheaves of modules. -/
noncomputable abbrev ringSheaf :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf

/-- **The degree-`n` term of `K_•(O_X, f₁, …, f_r)`**, as a presheaf of modules: the presheaf
`U ↦ ⋀^n_{O_X(U)}(O_X(U)^r)` of sectionwise exterior powers of the free module of rank `r`. -/
noncomputable abbrev piece (n : ℕ) :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.exteriorAlgebraPiece (n : ℤ) (PresheafOfModules.finFree X.presheaf r)

/-- **The degree-`n` term of `K_•(O_X, f₁, …, f_r)` as a sheaf of modules.** -/
noncomputable def sheafPiece (n : ℕ) : SheafOfModules.{u} (ringSheaf X) where
  val := piece X r n
  isSheaf := PresheafOfModules.isSheaf_exteriorAlgebraPiece_finFree X r n

/-- The underlying presheaf of modules of `sheafPiece X r n` is `piece X r n`. -/
@[simp]
theorem sheafPiece_val (n : ℕ) : (sheafPiece X r n).val = piece X r n := rfl

variable (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- **The Koszul differential of a family of sections of the structure sheaf**, from degree `n + 1`
to degree `n`: contraction of the sectionwise exterior algebra by the functional
`(f₁, …, f_r) : O_X^{⊕ r} → O_X`. -/
noncomputable def diff (n : ℕ) : piece X r (n + 1) ⟶ piece X r n :=
  PresheafOfModules.exteriorKoszulD (PresheafOfModules.finFree X.presheaf r)
    (PresheafOfModules.seqExteriorFunctional
      (PresheafOfModules.Sequence.ofRingedSpace X f)) (n : ℤ)

/-- The differential of `PresheafOfModules.seqExteriorKoszulComplex` attached to the family `f`,
from degree `n + 1` to degree `n`, is `diff X r f n`. -/
theorem seqExteriorKoszulComplex_d_eq (n : ℕ) :
    (PresheafOfModules.seqExteriorKoszulComplex
        (PresheafOfModules.Sequence.ofRingedSpace X f)).d (n + 1) n = diff X r f n :=
  PresheafOfModules.seqExteriorKoszulComplex_d _ n

/-- The Koszul differential as a morphism of sheaves of modules. -/
noncomputable def sheafDiff (n : ℕ) : sheafPiece X r (n + 1) ⟶ sheafPiece X r n :=
  ⟨diff X r f n⟩

/-- **`K_•(O_X, f₁, …, f_r)` as a chain complex of sheaves of modules.** In degree `n` it is the
sheaf of exterior powers `U ↦ ⋀^n_{O_X(U)}(O_X(U)^r)` and the differential is contraction by
`(f₁, …, f_r)`. This is the complex whose acyclicity in positive degrees is Koszul-regularity of
the family, in the sense of Stacks tag 063D. -/
@[stacks 062L "the complex `K_•(O_X, f₁, …, f_r)` itself, on a ringed space and as a chain \
complex of sheaves of modules",
  ega "III 1.1.1" "more general",
  sga "3 III 4.6.1" "more general",
  sga "6 VII 1.1" "special case"]
noncomputable def sheafComplex : ChainComplex (SheafOfModules.{u} (ringSheaf X)) ℕ :=
  ChainComplex.of (sheafPiece X r) (sheafDiff X r f) fun n =>
    SheafOfModules.hom_ext
      (PresheafOfModules.exteriorKoszulD_comp_exteriorKoszulD _ _ (n : ℤ))

/-- The degree-`n` term of `sheafComplex X r f` is `sheafPiece X r n`. -/
@[simp]
theorem sheafComplex_X (n : ℕ) : (sheafComplex X r f).X n = sheafPiece X r n := rfl

/-- The differential of `sheafComplex X r f` from degree `n + 1` to degree `n` is
`sheafDiff X r f n`. -/
@[simp]
theorem sheafComplex_d (n : ℕ) :
    (sheafComplex X r f).d (n + 1) n = sheafDiff X r f n :=
  ChainComplex.of_d (sheafPiece X r) (sheafDiff X r f) n

end Stacks.AlgebraicGeometry.SeqKoszul

end
