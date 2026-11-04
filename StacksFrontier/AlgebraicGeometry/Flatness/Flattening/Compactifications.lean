module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# The category of compactifications of a scheme over a base

Let `X` be a scheme over a scheme `S`. A compactification of `X` over `S` is an open
immersion from `X` into an `S`-scheme proper over `S`. Compactifications form a category: a
morphism is a morphism of the ambient `S`-schemes whose composite with the source open
immersion is the target open immersion.

If the interior of a compactification is dense in its ambient scheme, then along any morphism
of compactifications the inverse image of the target interior is exactly the source
interior.

## Main definitions

* `AlgebraicGeometry.IsCompactificationOf` is the property that a structured arrow of
  `S`-schemes is an open immersion with proper target.
* `AlgebraicGeometry.CompactificationOf` is the category of such structured arrows.
* `AlgebraicGeometry.CategoryOfCompactifications` bundles the base, the scheme over it, the
  finiteness hypotheses on the base, and the assumed quasi-compact compactification.

## Main results

* `AlgebraicGeometry.preimage_range_immersion_eq` identifies the inverse image of the
  interior of the target compactification.

The category structure on `CompactificationOf` is inherited from the category of structured
arrows in `S`-schemes.

## Implementation notes

Schemes over `S` are represented by `Over S`. Thus the condition that both the open immersion
and every morphism of compactifications lie over `S` is built into their types, while the
commuting triangle is built into `StructuredArrow`. The quasi-compactness assumption applies
to the compactification whose existence is assumed, not to every object of the category.

The interiors are expressed as the ranges of the underlying maps of the two open immersions.
The displayed equality is proved by exhibiting the preimage as an equalizer of two morphisms
from the open subscheme cut out by the target interior: the equalizer is closed, contains the
dense source interior, and is therefore everything.

A separate, quasi-compactness-carrying notion of compactification with a *varying* interior
is `AlgebraicGeometry.IsCompactification`; the two are genuinely different objects and the
present file is the one with the interior fixed.

## References

* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A structured arrow of schemes over `S` is a compactification of its source when its
arrow is an open immersion and its target is proper over `S`. -/
def IsCompactificationOf {S : Scheme.{u}} (X : Over S)
    (j : StructuredArrow X (𝟭 (Over S))) : Prop :=
  IsOpenImmersion j.hom.left ∧ IsProper j.right.hom

/-- The category of compactifications of the `S`-scheme `X`. -/
abbrev CompactificationOf {S : Scheme.{u}} (X : Over S) :=
  ObjectProperty.FullSubcategory (IsCompactificationOf X)

namespace CompactificationOf

variable {S : Scheme.{u}} {X : Over S}

/-- The ambient scheme of a compactification. -/
abbrev space (j : CompactificationOf X) : Scheme.{u} := j.obj.right.left

/-- The open immersion of a compactification. -/
abbrev immersion (j : CompactificationOf X) : X.left ⟶ j.space := j.obj.hom.left

/-- The structure morphism from the ambient scheme to the base. -/
abbrev toBase (j : CompactificationOf X) : j.space ⟶ S := j.obj.right.hom

/-- The underlying morphism of ambient schemes of a morphism of compactifications. -/
abbrev Hom.map {j k : CompactificationOf X} (f : j ⟶ k) : j.space ⟶ k.space :=
  f.hom.right.left

/-- The structure map of a compactification is an open immersion. -/
instance (j : CompactificationOf X) : IsOpenImmersion j.immersion := j.property.1

/-- The ambient scheme of a compactification is proper over the base. -/
instance (j : CompactificationOf X) : IsProper j.toBase := j.property.2

end CompactificationOf

/-- The standing data for the category of compactifications of a scheme over a quasi-compact,
quasi-separated base. The distinguished existence assertion includes quasi-compactness of
the open immersion, as in the source situation. -/
structure CategoryOfCompactifications where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The scheme over the base. -/
  X : Over S
  /-- The base scheme is quasi-compact. -/
  isQuasiCompact : CompactSpace S
  /-- The base scheme is quasi-separated. -/
  isQuasiSeparated : QuasiSeparatedSpace S
  /-- The scheme admits a quasi-compact open immersion into a scheme proper over the base. -/
  exists_quasiCompact_compactification :
    ∃ j : CompactificationOf X, QuasiCompact j.immersion

namespace CategoryOfCompactifications

/-- The base of the standing data is quasi-compact. -/
instance (C : CategoryOfCompactifications.{u}) : CompactSpace C.S :=
  C.isQuasiCompact

/-- The base of the standing data is quasi-separated. -/
instance (C : CategoryOfCompactifications.{u}) : QuasiSeparatedSpace C.S :=
  C.isQuasiSeparated

/-- The category of compactifications attached to the standing data. -/
abbrev category (D : CategoryOfCompactifications.{u}) := CompactificationOf D.X

/-- The category of compactifications of the standing data is nonempty: it contains the assumed
quasi-compact compactification. -/
instance (D : CategoryOfCompactifications.{u}) : Nonempty D.category :=
  D.exists_quasiCompact_compactification.elim fun j _ ↦ ⟨j⟩

end CategoryOfCompactifications

/-- **Stacks Project, Tag 0ATU.** For a morphism between compactifications whose source
interior is dense, the inverse image of the target interior is exactly the source
interior. -/
@[stacks 0ATU "preimage_of_interior"]
lemma preimage_range_immersion_eq
    (D : CategoryOfCompactifications.{u}) (j' j : D.category) (f : j' ⟶ j)
    (hdense : DenseRange j'.immersion.base) :
    (CompactificationOf.Hom.map f).base ⁻¹'
      Set.range j.immersion.base = Set.range j'.immersion.base := by
  let F := CompactificationOf.Hom.map f
  let U := j.immersion.opensRange
  let V := F ⁻¹ᵁ U
  have hcomp : j'.immersion ≫ F = j.immersion := by
    simpa [F, CompactificationOf.Hom.map] using congrArg (Over.forget D.S).map f.hom.w
  have hbase (k : D.category) : k.immersion ≫ k.toBase = D.X.hom := by
    simp [CompactificationOf.immersion, CompactificationOf.toBase]
  have happ {A B : Scheme.{u}} {k l : A ⟶ B} (h : k = l) (x : A) : k.base x = l.base x := by
    rw [h]
  have hbaseF : F ≫ j.toBase = j'.toBase := by
    simp [F, CompactificationOf.Hom.map, CompactificationOf.toBase]
  have hVmem : Set.range j'.immersion.base ⊆ (V : Set j'.space) := by
    rintro y ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simpa using (happ hcomp x).symm
  have hq : (⊤ : D.X.left.Opens) ≤ j'.immersion ⁻¹ᵁ V := by
    show (Set.univ : Set D.X.left) ⊆ (j'.immersion ⁻¹ᵁ V : Set D.X.left)
    intro x _; exact hVmem ⟨x, rfl⟩
  let q : D.X.left ⟶ V.toScheme :=
    (Scheme.topIso D.X.left).inv ≫ j'.immersion.resLE V ⊤ hq
  have hqι : q ≫ V.ι = j'.immersion := by
    dsimp [q]; rw [Category.assoc, Scheme.Hom.resLE_comp_ι]; simp
  have hqbase : (V.ι ∘ q : D.X.left → j'.space) = j'.immersion := by
    funext x
    exact happ hqι x
  have hqdense : DenseRange q.base := by
    show Dense (Set.range q)
    apply (Scheme.Hom.isOpenEmbedding V.ι).isInducing.dense_iff.mpr
    intro y; rw [← Set.range_comp, hqbase]
    exact hdense.closure_range ▸ Set.mem_univ _
  have hIso : j.immersion.isoOpensRange.inv ≫ D.X.hom =
      j.immersion.opensRange.ι ≫ j.toBase := by
    apply (cancel_epi j.immersion.isoOpensRange.hom).1
    simp [hbase j]
  let s : V.toScheme ⟶ D.X.left :=
    F.resLE U V le_rfl ≫ j.immersion.isoOpensRange.inv
  have hs : s ≫ D.X.hom = V.ι ≫ j'.toBase := by
    dsimp [s]
    simp only [Category.assoc, hIso]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hbaseF]
  let Vobj : Over D.S := Over.mk (V.ι ≫ j'.toBase)
  let qO : D.X ⟶ Vobj := Over.homMk q (by
    show q ≫ (V.ι ≫ j'.toBase) = D.X.hom
    rw [← Category.assoc, hqι, hbase j'])
  let sO : Vobj ⟶ D.X := Over.homMk s hs
  let inc : Vobj ⟶ j'.obj.right := Over.homMk V.ι rfl
  let g : Vobj ⟶ j'.obj.right := sO ≫ j'.obj.hom
  have hqf : q ≫ F.resLE U V le_rfl = j.immersion.isoOpensRange.hom := by
    apply (cancel_mono U.ι).1
    show (q ≫ F.resLE U V le_rfl) ≫ U.ι =
      j.immersion.isoOpensRange.hom ≫ U.ι
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      hqι, hcomp, Scheme.Hom.isoOpensRange_hom_ι]
  have hqs : q ≫ s = 𝟙 D.X.left := by
    dsimp [s]
    rw [← Category.assoc, hqf]
    exact j.immersion.isoOpensRange.hom_inv_id
  have hqOsO : qO ≫ sO = 𝟙 D.X := by
    apply Over.OverMorphism.ext
    simpa [qO, sO, Over.comp_left] using hqs
  have hqi : qO ≫ inc = j'.obj.hom := by
    apply Over.OverMorphism.ext
    simpa [qO, inc, Over.comp_left] using hqι
  have hfactor : qO ≫ inc = qO ≫ g := by
    rw [hqi]
    simp [g, ← Category.assoc, hqOsO]
  have hclosed : IsClosed
      (Set.range (Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base) := by
    simpa using (isClosedImmersion_equalizer_ι_left inc g).isClosedEmbedding.isClosed_range
  let e : D.X ⟶ CategoryTheory.Limits.equalizer inc g :=
    CategoryTheory.Limits.equalizer.lift qO hfactor
  have hrange : Set.range q.base ⊆
      Set.range (Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base := by
    rintro y ⟨x, rfl⟩
    refine ⟨(Over.Hom.left e) x, ?_⟩
    have heq : (Over.Hom.left e) ≫
        Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g) = q := by
      simpa only [Over.forget_map, Over.comp_left, Over.homMk_left, qO] using
        congrArg (Over.forget D.S).map (CategoryTheory.Limits.equalizer.lift_ι qO hfactor)
    exact happ heq x
  have heDense :
      DenseRange (Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base :=
    hqdense.mono hrange
  have heSurj : Function.Surjective
      (Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base :=
    Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans heDense.closure_range)
  ext y
  constructor
  · intro hy
    let yV : V := ⟨y, hy⟩
    have heval : V.ι.base yV = (s ≫ j'.immersion).base yV := by
      obtain ⟨z, hz⟩ := heSurj yV
      have h := happ (congrArg Over.Hom.left (CategoryTheory.Limits.equalizer.condition inc g)) z
      have h' : V.ι.base
            ((Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base z) =
          (s ≫ j'.immersion).base
            ((Over.Hom.left (CategoryTheory.Limits.equalizer.ι inc g)).base z) := by
        simpa [inc, g, sO] using h
      simpa [hz] using h'
    exact ⟨s.base yV, heval.symm⟩
  · exact fun hy ↦ hVmem hy

end AlgebraicGeometry
