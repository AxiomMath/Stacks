module

public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Complex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex on a finite family of sections

Stacks tag 062L specializes the Koszul complex of tag 062K to the map
`(f₁, …, f_r) : O^{⊕ r} → O` attached to a finite family of sections of the structure presheaf.
This file builds that specialization: the free presheaf of modules of finite rank, the
functional a family of sections defines on it, and hence the Koszul complex
`K_•(O, f₁, …, f_r)`.

## Main definitions

* `PresheafOfModules.finFree`: the free presheaf of modules of finite rank `r`, whose sections
  over `U` are the `r`-tuples of sections of the structure presheaf with componentwise
  restriction.
* `PresheafOfModules.Sequence`: a finite family of sections of the structure presheaf available
  over every object, which is the datum `f₁, …, f_r ∈ Γ(X, O_X)` of the source;
  `PresheafOfModules.Sequence.ofRingedSpace` builds one from global sections on a ringed space.
* `PresheafOfModules.seqExteriorFunctional`: the functional `v ↦ ∑ i, vᵢ fᵢ` on `finFree O r`
  attached to such a family, i.e. the map `(f₁, …, f_r) : O^{⊕ r} → O`.
* `PresheafOfModules.seqExteriorKoszulComplex`: **the Koszul complex on `f₁, …, f_r`.**

## Main results

* `PresheafOfModules.seqExteriorFunctional_dual`: the functional over `U` is the ring-level
  `Koszul.seqDual` of the family of sections restricted to `U`, which is how Stacks tag 0623
  presents it.
* `PresheafOfModules.exteriorAlgebraPieceVal_seqExteriorKoszulD`: the differential acts on
  sections over `U` as the ring-level Koszul differential of the restricted family.

## Implementation notes

**The family of sections is given over a fixed object, with restrictions to all others.** Tag
062L is stated for a ringed space and global sections `f₁, …, f_r ∈ Γ(X, O_X)`; the
corresponding datum over an arbitrary category is a family of sections over one object together
with a restriction morphism to every other object, compatible with composition. That is the
`Sequence` structure. For a ringed space the object is `op ⊤` and the morphisms are the
restrictions along `U ≤ ⊤`, which is `Sequence.ofRingedSpace`; the compatibility holds because
`Opens X` is a partial order, so its hom types are subsingletons.

**Why `finFree` and not a finite product of copies of `unit`.** A product of `r` copies of
`PresheafOfModules.unit` has sections over `U` only *isomorphic* to `Fin r → O(U)`, whereas the
ring-level Koszul complex of a sequence (`Koszul.seqComplex`) is the Koszul complex of a
functional on the literal module `Fin r → R`. Taking the sections to be `Fin r → O(U)` on the
nose makes the comparison with the ring-level complex an identity rather than a transport: the
sections of the degree-`n` piece over `U` are `⋀ⁿ(O(U)^r)` itself.

**Why `finFree` is an `abbrev`.** Its sections over `X` are `Fin r → O(X)` definitionally, but
`PresheafOfModules.ofPresheaf` is semireducible, so a section of it is not *applied* to an index
unless the definition unfolds at reducible transparency. Making it reducible is what lets
`Koszul.seqDual` be used directly as a linear form on those sections, with no transport.

## References

* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

open scoped ExteriorAlgebra

universe v u w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **The free presheaf of modules of finite rank `r`.** Its sections over `X` are the
`r`-tuples of sections of the structure presheaf, restricted componentwise. -/
noncomputable abbrev finFree (O : Cᵒᵖ ⥤ CommRingCat.{w}) (r : ℕ) :
    PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat) :=
  ofPresheaf
    { obj X := AddCommGrpCat.of (Fin r → (O ⋙ forget₂ CommRingCat RingCat).obj X)
      map {X Y} f := AddCommGrpCat.ofHom
        { toFun := fun v i => ((O ⋙ forget₂ CommRingCat RingCat).map f).hom (v i)
          map_zero' := funext fun _ => map_zero _
          map_add' := fun v v' => funext fun i => map_add _ (v i) (v' i) }
      map_id X := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun v => funext fun i =>
        congrArg (fun ψ : (O ⋙ forget₂ CommRingCat RingCat).obj X ⟶
            (O ⋙ forget₂ CommRingCat RingCat).obj X => (ConcreteCategory.hom ψ) (v i))
          ((O ⋙ forget₂ CommRingCat RingCat).map_id X))
      map_comp {X _ Z} f g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun v => funext fun i =>
        congrArg (fun ψ : (O ⋙ forget₂ CommRingCat RingCat).obj X ⟶
            (O ⋙ forget₂ CommRingCat RingCat).obj Z => (ConcreteCategory.hom ψ) (v i))
          ((O ⋙ forget₂ CommRingCat RingCat).map_comp f g)) }
    fun {_ _} g c v => funext fun i => by
      change ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (c * v i) =
        ((O ⋙ forget₂ CommRingCat RingCat).map g).hom c *
          ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (v i)
      exact map_mul _ _ _

/-- The restriction map of `finFree O r` along `g` applies the restriction map of the structure
presheaf to each component. -/
@[simp]
theorem finFree_map_apply (r : ℕ) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (v : (finFree O r).obj X) (i : Fin r) :
    (finFree O r).map g v i = ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (v i) :=
  rfl

/-- **A finite family of sections of the structure presheaf, available over every object.** It
consists of sections over a chosen object `base` together with a restriction morphism to every
object, compatible with composition. For a ringed space this is a family of global sections,
restricted to each open; see `PresheafOfModules.Sequence.ofRingedSpace`. -/
structure Sequence (O : Cᵒᵖ ⥤ CommRingCat.{w}) (r : ℕ) where
  /-- The object the family is defined over. -/
  base : Cᵒᵖ
  /-- The family of sections over `base`. -/
  elem : Fin r → (O ⋙ forget₂ CommRingCat RingCat).obj base
  /-- The restriction morphism from `base` to an arbitrary object. -/
  res (X : Cᵒᵖ) : base ⟶ X
  /-- The restriction morphisms are compatible with composition. -/
  res_comp {X Y : Cᵒᵖ} (f : X ⟶ Y) : res X ≫ f = res Y

namespace Sequence

variable {r : ℕ} (f : Sequence O r)

/-- The family of sections restricted to an object, as a sequence in the ring of sections
there. -/
noncomputable def restrict (X : Cᵒᵖ) : Fin r → (O ⋙ forget₂ CommRingCat RingCat).obj X :=
  fun i => ((O ⋙ forget₂ CommRingCat RingCat).map (f.res X)).hom (f.elem i)

/-- Restricting further is restricting: the family restricted to `X` and then to `Y` is the
family restricted to `Y`. -/
theorem map_restrict {X Y : Cᵒᵖ} (g : X ⟶ Y) (i : Fin r) :
    ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (f.restrict X i) = f.restrict Y i := by
  rw [restrict, restrict]
  conv_rhs => rw [← f.res_comp g]
  rw [Functor.map_comp]
  rfl

/-- **A family of global sections on a ringed space is a `Sequence`.** The base object is the
whole space and the restriction morphisms are the inclusions of the opens. -/
noncomputable def ofRingedSpace (X : AlgebraicGeometry.RingedSpace.{u, v}) {r : ℕ}
    (g : Fin r → X.presheaf.obj (op (⊤ : Opens X))) : Sequence X.presheaf r where
  base := op (⊤ : Opens X)
  elem := g
  res _ := (homOfLE le_top).op
  res_comp _ := Subsingleton.elim _ _

end Sequence

/-- The ring-level functional of a restricted family commutes with restriction. This is the
naturality of `PresheafOfModules.seqExteriorFunctional`, stated on the literal product module
`Fin r → O(X)` rather than on the sections of `finFree O r`. -/
theorem seqDual_restrict_naturality {r : ℕ} (f : Sequence O r) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (v : Fin r → ((O ⋙ forget₂ CommRingCat RingCat).obj X : Type w)) :
    ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (Koszul.seqDual (f.restrict X) v) =
      Koszul.seqDual (f.restrict Y)
        (fun i => ((O ⋙ forget₂ CommRingCat RingCat).map g).hom (v i)) := by
  rw [Koszul.seqDual_apply, Koszul.seqDual_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, f.map_restrict g i]

/-- **The functional `(f₁, …, f_r) : O^{⊕ r} → O`.** Over each object it is the ring-level
`Koszul.seqDual` of the family of sections restricted there. On a ringed space, the Koszul
complex of Stacks tag 062L attached to it is
`Stacks.AlgebraicGeometry.SeqKoszul.koszulDifferentialGradedAlgebra`. -/
noncomputable def seqExteriorFunctional {r : ℕ} (f : Sequence O r) :
    ExteriorFunctional.{v, u, w, w} (finFree O r) where
  dual X := Koszul.seqDual (f.restrict X)
  naturality {_ _} g v := seqDual_restrict_naturality f g v

/-- Over an object `X`, the functional attached to `f` is `Koszul.seqDual` of the family `f`
restricted to `X`. -/
theorem seqExteriorFunctional_dual {r : ℕ} (f : Sequence O r) (X : Cᵒᵖ) :
    (seqExteriorFunctional f).dual X = Koszul.seqDual (f.restrict X) :=
  rfl

/-- **The Koszul complex on a family of sections `f₁, …, f_r`**, written
`K_•(O, f₁, …, f_r)` in Stacks tag 062L: the Koszul complex of the functional
`(f₁, …, f_r) : O^{⊕ r} → O`. In degree `n` it is the presheaf of exterior powers
`U ↦ ⋀^n_{O(U)}(O(U)^r)`. -/
@[sga "6 IX 1.8" "partial"]
noncomputable def seqExteriorKoszulComplex {r : ℕ} (f : Sequence O r) :
    ChainComplex (PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)) ℕ :=
  exteriorKoszulComplex (finFree O r) (seqExteriorFunctional f)

/-- The differential of `K_•(O, f₁, …, f_r)` from degree `n + 1` to degree `n` is
`exteriorKoszulD` of the functional `(f₁, …, f_r)`. -/
theorem seqExteriorKoszulComplex_d {r : ℕ} (f : Sequence O r) (n : ℕ) :
    (seqExteriorKoszulComplex f).d (n + 1) n =
      exteriorKoszulD (finFree O r) (seqExteriorFunctional f) (n : ℤ) :=
  exteriorKoszulComplex_d (finFree O r) (seqExteriorFunctional f) n

/-- **The differential of `K_•(O, f₁, …, f_r)` on sections.** Over an object `X` it is
contraction by the ring-level functional `Koszul.seqDual` of the restricted family, that is, the
ring-level Koszul differential of `f₁|_X, …, f_r|_X`. -/
theorem exteriorAlgebraPieceVal_seqExteriorKoszulD {r : ℕ} (f : Sequence O r) (n : ℤ) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece (n + 1) (finFree O r)).obj X) :
    exteriorAlgebraPieceVal n (finFree O r) X
        (Hom.app (exteriorKoszulD (finFree O r) (seqExteriorFunctional f) n) X x) =
      Koszul.contraction (Koszul.seqDual (f.restrict X))
        (exteriorAlgebraPieceVal (n + 1) (finFree O r) X x) :=
  rfl

end PresheafOfModules

end
