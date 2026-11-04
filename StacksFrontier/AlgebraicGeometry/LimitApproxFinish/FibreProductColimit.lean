module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre products along a filtered colimit of rings

Let `R = colim_i R_i` be a filtered colimit of commutative rings and let `s : B ⟶ R` be a ring
map. Form the fibre products `B_i = B ×_R R_i`. Then the first projections exhibit `B` as the
filtered colimit of the `B_i`.

## Main definitions

* `Stacks.FibreProduct.subring`: the fibre product of two ring maps `s : B ⟶ R` and
  `t : R' ⟶ R`, as a subring of `B × R'`.
* `Stacks.FibreProduct.obj`: the fibre product as an object of `CommRingCat`, with projections
  `Stacks.FibreProduct.fst` and `Stacks.FibreProduct.snd`.
* `Stacks.FibreProduct.diagram`: the diagram `i ↦ B ×_R R_i` along a cocone with vertex `R`.
* `Stacks.FibreProduct.cocone`: the cocone over `Stacks.FibreProduct.diagram` with vertex `B`
  given by the first projections.

## Main results

* `Stacks.FibreProduct.isPullback`: the fibre product square is cartesian.
* `Stacks.FibreProduct.nonempty_isColimitCocone`: if `R` is the filtered colimit of the `R_i`,
  then `B` is the colimit of the fibre products `B ×_R R_i`.

## Implementation notes

The index category is kept in the universe of the rings. `Stacks.FibreProduct.subring` is
definitionally Mathlib's `RingHom.eqLocus` of the two composites with the product projections,
so its fibre product square is that of `CommRingCat.pullbackCone`. The transition maps of
`Stacks.FibreProduct.diagram` act on the second component only, so the first projections are
natural by definition.

## What is NOT done here

Nothing in this file mentions schemes.  It does not identify `R` as the sections of the overlap,
and it does not produce the finite-type subalgebras of `B_i` of Tag 01Z7.  Tag 07RN is not
proved and no tag attribute is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FibreProduct

/-! ### The fibre product of two ring maps -/

section Square

variable {B R R' : CommRingCat.{u}} (s : B ⟶ R) (t : R' ⟶ R)

/-- The fibre product of two ring maps `s : B ⟶ R` and `t : R' ⟶ R`, as a subring of the
product `B × R'`. -/
@[ega "IV 19.3.2.1"]
def subring : Subring (B × R') :=
  RingHom.eqLocus (s.hom.comp (RingHom.fst B R')) (t.hom.comp (RingHom.snd B R'))

/-- A pair `x : B × R'` lies in the fibre product if and only if `s x.1 = t x.2`. -/
@[simp]
lemma mem_subring (x : B × R') : x ∈ subring s t ↔ s x.1 = t x.2 := Iff.rfl

/-- The fibre product of two ring maps, as an object of `CommRingCat`. -/
def obj : CommRingCat.{u} := CommRingCat.of (subring s t)

/-- The projection of the fibre product onto the first factor. -/
def fst : obj s t ⟶ B := CommRingCat.ofHom ((RingHom.fst _ _).comp (subring s t).subtype)

/-- The projection of the fibre product onto the second factor. -/
def snd : obj s t ⟶ R' := CommRingCat.ofHom ((RingHom.snd _ _).comp (subring s t).subtype)

/-- The fibre product square is cartesian. -/
lemma isPullback : IsPullback (fst s t) (snd s t) s t :=
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit s t)

/-- The two projections of an element of the fibre product have the same image in the base. -/
lemma compat (x : obj s t) : s (fst s t x) = t (snd s t x) := by
  simpa using congrArg (fun g : obj s t ⟶ R ↦ g.hom x) (isPullback s t).w

/-- Elements of the fibre product are determined by their two projections. -/
lemma ext {x y : obj s t} (h₁ : fst s t x = fst s t y) (h₂ : snd s t x = snd s t y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- The element of the fibre product cut out by a compatible pair. -/
def mk (b : B) (r : R') (h : s b = t r) : obj s t := show subring s t from ⟨(b, r), h⟩

/-- The first projection of `mk s t b r h` is `b`. -/
@[simp] lemma fst_mk (b : B) (r : R') (h : s b = t r) : fst s t (mk s t b r h) = b := rfl

/-- The second projection of `mk s t b r h` is `r`. -/
@[simp] lemma snd_mk (b : B) (r : R') (h : s b = t r) : snd s t (mk s t b r h) = r := rfl

end Square

/-! ### Elementwise description of a filtered colimit of rings -/

section Elements

variable {K : Type u} [Category.{u} K] [IsFiltered K] {F : K ⥤ CommRingCat.{u}}
  {R : CommRingCat.{u}} {τ : F ⟶ (Functor.const K).obj R}

/-- Every element of the vertex of a filtered colimit cocone of rings comes from a stage. -/
lemma exists_app_eq (hτ : IsColimit (Cocone.mk R τ)) (x : R) :
    ∃ (i : K) (y : F.obj i), τ.app i y = x := by
  simpa using Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat) hτ) x

/-- Finitely many elements of the vertex of a filtered colimit cocone of rings all come from a
single stage. -/
lemma exists_app_eq_fin (hτ : IsColimit (Cocone.mk R τ)) :
    ∀ {n : ℕ} (x : Fin n → R), ∃ (i : K) (y : Fin n → F.obj i), ∀ l, τ.app i (y l) = x l := by
  intro n
  induction n with
  | zero => exact fun _ ↦ ⟨(IsFiltered.nonempty (C := K)).some, Fin.elim0, fun l ↦ l.elim0⟩
  | succ n ih =>
    intro x
    obtain ⟨i₀, y₀, hy₀⟩ := exists_app_eq hτ (x 0)
    obtain ⟨i₁, y₁, hy₁⟩ := ih fun l ↦ x l.succ
    refine ⟨IsFiltered.max i₀ i₁, Fin.cons (F.map (IsFiltered.leftToMax i₀ i₁) y₀)
      fun l ↦ F.map (IsFiltered.rightToMax i₀ i₁) (y₁ l), fun l ↦ ?_⟩
    refine Fin.cases ?_ (fun l ↦ ?_) l
    · simpa using hy₀
    · simpa using hy₁ l

/-- Two elements of a stage with the same image in a filtered colimit of rings already agree at
a later stage. -/
lemma exists_map_eq (hτ : IsColimit (Cocone.mk R τ)) {i : K} (y z : F.obj i)
    (h : τ.app i y = τ.app i z) : ∃ (j : K) (f : i ⟶ j), F.map f y = F.map f z := by
  simpa using (Types.FilteredColimit.isColimit_eq_iff' (F := F ⋙ forget CommRingCat)
    (isColimitOfPreserves (forget CommRingCat) hτ) y z).mp (by simpa using h)

end Elements

/-! ### The diagram of fibre products along a cocone -/

section Diagram

variable {K : Type u} [Category.{u} K] (F : K ⥤ CommRingCat.{u}) {R : CommRingCat.{u}}
  (τ : F ⟶ (Functor.const K).obj R) {B : CommRingCat.{u}} (s : B ⟶ R)

/-- A cocone with constant vertex is compatible with the transition maps of its diagram. -/
lemma app_naturality {i j : K} (f : i ⟶ j) (y : F.obj i) : τ.app j (F.map f y) = τ.app i y := by
  simp

/-- The transition map of the diagram of fibre products: it acts on the second component only. -/
def diagramMap {i j : K} (f : i ⟶ j) : obj s (τ.app i) ⟶ obj s (τ.app j) :=
  CommRingCat.ofHom
    ((((RingHom.fst _ _).prod ((F.map f).hom.comp (RingHom.snd _ _))).comp
        (subring s (τ.app i)).subtype).codRestrict (subring s (τ.app j))
      (fun x ↦ by
        simp only [mem_subring]
        exact (compat s (τ.app i) x).trans (app_naturality F τ f (snd s (τ.app i) x)).symm))

/-- The transition maps of the diagram of fibre products commute with the first projections. -/
lemma fst_diagramMap {i j : K} (f : i ⟶ j) (x : obj s (τ.app i)) :
    fst s (τ.app j) (diagramMap F τ s f x) = fst s (τ.app i) x := rfl

/-- The transition map along `f` acts on the second projection by `F.map f`. -/
lemma snd_diagramMap {i j : K} (f : i ⟶ j) (x : obj s (τ.app i)) :
    snd s (τ.app j) (diagramMap F τ s f x) = F.map f (snd s (τ.app i) x) := rfl

/-- The diagram of fibre products `i ↦ B ×_R R_i` along a cocone `τ` with vertex `R`. -/
def diagram : K ⥤ CommRingCat.{u} where
  obj i := obj s (τ.app i)
  map f := diagramMap F τ s f
  map_id i := CommRingCat.hom_ext (RingHom.ext fun x ↦
    ext s (τ.app i) rfl (by simp [snd_diagramMap]))
  map_comp {i j k} f g := CommRingCat.hom_ext (RingHom.ext fun x ↦
    ext s (τ.app k) rfl (by simp [snd_diagramMap]))

/-- The cocone over `Stacks.FibreProduct.diagram` with vertex `B`, given by the first
projections. -/
def cocone : Cocone (diagram F τ s) where
  pt := B
  ι.app i := fst s (τ.app i)
  ι.naturality := fun {_ _} _ ↦ CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)

/-- The component of `Stacks.FibreProduct.cocone` at `i` is the first projection. -/
@[simp] lemma cocone_ι_app (i : K) : (cocone F τ s).ι.app i = fst s (τ.app i) := rfl

variable [IsFiltered K]

/-- If `R` is the filtered colimit of the `R_i`, then `B` is the colimit of the fibre products
`B ×_R R_i`, with the first projections as colimit cocone. -/
lemma nonempty_isColimitCocone (hτ : IsColimit (Cocone.mk R τ)) :
    Nonempty (IsColimit (cocone F τ s)) := by
  have : ReflectsFilteredColimits (forget CommRingCat) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine ReflectsColimit.reflects (F := forget CommRingCat)
    (Types.FilteredColimit.isColimitOf' (diagram F τ s ⋙ forget CommRingCat)
      ((forget CommRingCat).mapCocone (cocone F τ s)) (fun b ↦ ?_) (fun i x y h ↦ ?_))
  · obtain ⟨i, y, hy⟩ := exists_app_eq hτ (s b)
    exact ⟨i, mk s (τ.app i) b y hy.symm, rfl⟩
  · have h₁ : fst s (τ.app i) x = fst s (τ.app i) y := h
    obtain ⟨j, f, hf⟩ := exists_map_eq hτ (snd s (τ.app i) x) (snd s (τ.app i) y)
      (by rw [← compat s (τ.app i) x, ← compat s (τ.app i) y, h₁])
    exact ⟨j, f, ext s (τ.app j) h₁ hf⟩

/-- A chosen colimit structure on `Stacks.FibreProduct.cocone`, when `R` is the filtered colimit
of the `R_i`. -/
noncomputable def isColimitCocone (hτ : IsColimit (Cocone.mk R τ)) : IsColimit (cocone F τ s) :=
  (nonempty_isColimitCocone F τ s hτ).some

end Diagram

end Stacks.FibreProduct
