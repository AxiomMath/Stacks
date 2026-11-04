module

public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans

@[expose] public noncomputable section

/-!
# Two transformations of exact functors agreeing on a compact generator: the dévissage fails

`StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated` runs a dévissage along the cell
presentation of [stacks 09SN] for the property `IsIso (τ.app X)` of one morphism `τ : F ⟶ G` of
exact direct-sum-preserving functors. This file asks the same question for the property

`Φ.app X = Ψ.app X`

of *two* morphisms `Φ, Ψ : F ⟶ G`, which is what an identity between two canonical comparisons
of functors needs — for instance the compatibility of tensor comparisons in [stacks 0E2A], whose
two sides are the components of two natural isomorphisms of the functors
`baseChangeR ⋙ (- ⊗ baseChangeR A[0])` and `baseChangeR ⋙ (- ⊗ A'[0])`.

**It does not run.** Three of the four closure properties hold, and are proved here:

* isomorphisms, by naturality — `eq_app_of_iso`;
* shifts, by `CategoryTheory.NatTrans.app_shift` — `eq_app_shift`;
* colimits both functors preserve, in particular direct sums, because two morphisms out of a
  colimit agreeing on the cocone are equal — `eq_app_of_isColimit`, and
  `eq_app_of_colimitsOfShape_shiftClosure` for the direct sums of shifts that the cell
  presentation puts on its tower.

The fourth, extension in a distinguished triangle, is **false**, and the last two results of this
file are why. At the third vertex of a distinguished triangle `T`, agreement at the first two
vertices leaves exactly two constraints on the difference `δ = Φ.app T.obj₃ - Ψ.app T.obj₃`:

`F.map T.mor₂ ≫ δ = 0` and `δ ≫ G.map T.mor₃ = 0`

(`comp_sub_app_obj₃_eq_zero` and `sub_app_obj₃_comp_eq_zero` — the two naturality squares of a
morphism of triangles whose first two components vanish). Those two constraints are satisfied by
every morphism of the form

`F.map T.mor₃ ≫ u ≫ G.map T.mor₂`,  `u : F.obj (T.obj₁⟦1⟧) ⟶ G.obj T.obj₂`

— `comp_sandwich_eq_zero` and `sandwich_comp_eq_zero`, which need nothing but `T.mor₂ ≫ T.mor₃ = 0`
and the additivity of the two functors. So the data of a map of triangles with two vanishing
components does not determine the third, and no amount of rearranging the five lemma will supply
the cone step: `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂` concludes that a morphism is
*invertible*, which is a property of one morphism and is stable under adding a sandwich, whereas
equality is not.

The indeterminacy is not formal only. `Hom(F (T.obj₁⟦1⟧), G T.obj₂)` is nonzero as soon as the two
vertices are shifts of one another — which is the generic case on the tower of a cell
presentation, whose vertices are direct sums of shifts of the generator — and the same obstruction
reappears one level up: a map out of the derived colimit of the tower is not determined by its
restrictions to the stages, the kernel of the restriction being the `lim¹` term of the Milnor
sequence. Both are the phantom-map phenomenon, and both say that **an equality of morphisms in a
triangulated category is not detected by a family of compact generators**, however invertible the
two sides are.

Consequently an identity between two comparisons cannot be transported from a compact generator
by this dévissage: it has to be proved where its two sides are constructed.

## Main results

* `StacksDraft.CompactDevissage.eq_app_of_iso`, `StacksDraft.CompactDevissage.eq_app_shift`,
  `StacksDraft.CompactDevissage.eq_app_of_isColimit`,
  `StacksDraft.CompactDevissage.eq_app_of_colimitsOfShape_shiftClosure` — the three closure
  properties of the agreement locus that do hold.
* `StacksDraft.CompactDevissage.comp_sub_app_obj₃_eq_zero`,
  `StacksDraft.CompactDevissage.sub_app_obj₃_comp_eq_zero` — all that agreement at the first two
  vertices of a distinguished triangle says about the third.
* `StacksDraft.CompactDevissage.comp_sandwich_eq_zero`,
  `StacksDraft.CompactDevissage.sandwich_comp_eq_zero` — **the cone step is false**: those two
  constraints hold of every sandwich through the two connecting morphisms, so they do not
  determine the difference.

## References

* [The Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [The Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty

namespace StacksDraft.CompactDevissage

universe v v' u u'

/-! ### The two closure properties that need no shift -/

section Colimits

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
  {F G : D ⥤ D'} (Φ Ψ : F ⟶ G)

/-- Agreement of `Φ` and `Ψ` at an object only depends on the isomorphism class of that object:
conjugating by the image of an isomorphism is the same operation on both. -/
lemma eq_app_of_iso {X Y : D} (e : X ≅ Y) (h : Φ.app X = Ψ.app X) : Φ.app Y = Ψ.app Y := by
  have key (Θ : F ⟶ G) : Θ.app Y = inv (F.map e.hom) ≫ Θ.app X ≫ G.map e.hom := by
    rw [← Θ.naturality e.hom, IsIso.inv_hom_id_assoc]
  rw [key Φ, key Ψ, h]

/-- If `Φ` and `Ψ` agree on a diagram whose colimit `F` preserves, they agree at the colimit: two
morphisms out of a colimit which agree on the cocone are equal, and naturality identifies their
composites with the legs. Only `F` has to preserve the colimit — unlike for invertibility, where
the two colimit cocones are compared with one another. -/
lemma eq_app_of_isColimit {J : Type*} [Category J] (Z : J ⥤ D) {c : Cocone Z}
    (hc : IsColimit c) [PreservesColimit Z F] (h : ∀ j, Φ.app (Z.obj j) = Ψ.app (Z.obj j)) :
    Φ.app c.pt = Ψ.app c.pt :=
  (isColimitOfPreserves F hc).hom_ext fun j =>
    (Φ.naturality (c.ι.app j)).trans
      ((congrArg (· ≫ G.map (c.ι.app j)) (h j)).trans (Ψ.naturality (c.ι.app j)).symm)

end Colimits

/-! ### The shift -/

section Shift

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
  {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ]
  (Φ Ψ : F ⟶ G) [NatTrans.CommShift Φ ℤ] [NatTrans.CommShift Ψ ℤ]

/-- If `Φ` and `Ψ` agree at `X` they agree at every shift of `X`: both components are the same
conjugate of the component at `X` by the isomorphisms expressing that `F` and `G` commute with the
shift. -/
lemma eq_app_shift {X : D} (h : Φ.app X = Ψ.app X) (n : ℤ) :
    Φ.app (X⟦n⟧) = Ψ.app (X⟦n⟧) := by
  rw [NatTrans.app_shift Φ n X, NatTrans.app_shift Ψ n X, h]

end Shift

/-! ### Direct sums of shifts -/

section DirectSums

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
  {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
  (Φ Ψ : F ⟶ G) [NatTrans.CommShift Φ ℤ] [NatTrans.CommShift Ψ ℤ]

/-- `Φ` and `Ψ` agree on every direct sum of shifts of a family on which they agree. This is the
object property that the cell presentation of [stacks 09SN] puts on the base of its tower and on
each of the cells attached along the way; what it has no counterpart of, for an equality, is the
step that attaches them. -/
lemma eq_app_of_colimitsOfShape_shiftClosure {ι : Type v} (E : ι → D)
    (hΦΨ : ∀ i, Φ.app (E i) = Ψ.app (E i)) (Y : D)
    (hY : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y) :
    Φ.app Y = Ψ.app Y := by
  rw [ObjectProperty.prop_iSup_iff] at hY
  obtain ⟨J, hJ⟩ := hY
  obtain ⟨p⟩ := hJ
  refine eq_app_of_isColimit Φ Ψ p.diag p.isColimit fun j => ?_
  obtain ⟨W, n, e, ⟨i⟩⟩ := p.prop_diag_obj j
  exact eq_app_of_iso Φ Ψ e.symm (eq_app_shift Φ Ψ (hΦΨ i) n)

end DirectSums

/-! ### Extensions in a distinguished triangle: the step that fails -/

section Triangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] [F.Additive] [G.Additive]

section Difference

variable (Φ Ψ : F ⟶ G)

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.CommShift ℤ] [G.CommShift ℤ] [F.Additive] [G.Additive] [Preadditive D] [HasShift D' ℤ] in
/-- **The first of the two constraints the cone step has.** If `Φ` and `Ψ` agree at the second
vertex of a triangle, the difference of their components at the third vertex is killed by
precomposition with the image of the second morphism — the first naturality square of the morphism
of triangles the pair induces. -/
lemma comp_sub_app_obj₃_eq_zero (T : Triangle D) (h₂ : Φ.app T.obj₂ = Ψ.app T.obj₂) :
    F.map T.mor₂ ≫ (Φ.app T.obj₃ - Ψ.app T.obj₃) = 0 := by
  rw [Preadditive.comp_sub, Φ.naturality T.mor₂, Ψ.naturality T.mor₂, h₂, sub_self]

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasZeroObject D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.Additive] [G.Additive] [Preadditive D] in
/-- **The second of the two constraints the cone step has.** If `Φ` and `Ψ` agree at the first
vertex of a triangle, the difference of their components at the third vertex is killed by
postcomposition with the image of the third morphism — the second naturality square, after the
agreement at the first vertex is moved onto its shift by
`StacksDraft.CompactDevissage.eq_app_shift`. -/
lemma sub_app_obj₃_comp_eq_zero [NatTrans.CommShift Φ ℤ] [NatTrans.CommShift Ψ ℤ]
    (T : Triangle D) (h₁ : Φ.app T.obj₁ = Ψ.app T.obj₁) :
    (Φ.app T.obj₃ - Ψ.app T.obj₃) ≫ G.map T.mor₃ = 0 := by
  rw [Preadditive.sub_comp, ← Φ.naturality T.mor₃, ← Ψ.naturality T.mor₃,
    eq_app_shift Φ Ψ h₁ (1 : ℤ), sub_self]

end Difference

omit [HasZeroObject D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.CommShift ℤ] [G.CommShift ℤ] [G.Additive] [HasShift D' ℤ] in
/-- **The cone step is false: the two constraints do not determine the difference, first half.**
For *any* morphism `u` out of the shifted first vertex, the sandwich `F T.mor₃ ≫ u ≫ G T.mor₂`
satisfies the constraint of `StacksDraft.CompactDevissage.comp_sub_app_obj₃_eq_zero`. Nothing but
`T.mor₂ ≫ T.mor₃ = 0` and the additivity of `F` is used. -/
lemma comp_sandwich_eq_zero (T : Triangle D) (hT : T ∈ distTriang D)
    (u : F.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ G.obj T.obj₂) :
    F.map T.mor₂ ≫ F.map T.mor₃ ≫ u ≫ G.map T.mor₂ = 0 := by
  rw [← Category.assoc, ← F.map_comp, comp_distTriang_mor_zero₂₃ T hT, F.map_zero, zero_comp]

omit [HasZeroObject D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  [F.CommShift ℤ] [G.CommShift ℤ] [F.Additive] [HasShift D' ℤ] in
/-- **The cone step is false: the two constraints do not determine the difference, second half.**
The same sandwich satisfies the constraint of
`StacksDraft.CompactDevissage.sub_app_obj₃_comp_eq_zero`.

Together with `StacksDraft.CompactDevissage.comp_sandwich_eq_zero` this exhibits a family of
morphisms, indexed by `Hom (F (T.obj₁⟦1⟧)) (G T.obj₂)` and nonzero in general, satisfying every
constraint that agreement at the first two vertices of a distinguished triangle imposes at the
third. So the agreement locus of two morphisms of exact functors is *not* closed under extensions,
and the dévissage of `StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated` has no
counterpart for an equality. -/
lemma sandwich_comp_eq_zero (T : Triangle D) (hT : T ∈ distTriang D)
    (u : F.obj (T.obj₁⟦(1 : ℤ)⟧) ⟶ G.obj T.obj₂) :
    (F.map T.mor₃ ≫ u ≫ G.map T.mor₂) ≫ G.map T.mor₃ = 0 := by
  rw [Category.assoc, Category.assoc, ← G.map_comp, comp_distTriang_mor_zero₂₃ T hT, G.map_zero,
    comp_zero, comp_zero]

end Triangulated

end StacksDraft.CompactDevissage

end
