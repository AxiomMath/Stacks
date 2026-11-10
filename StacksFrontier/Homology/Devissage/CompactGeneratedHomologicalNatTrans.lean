module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.Perfect.LargeUniverse

@[expose] public noncomputable section

/-!
# A morphism of homological direct-sum-preserving functors invertible on compact generators

`StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule` propagates an identification of
two *triangulated* functors from a compact generator to the whole of a compactly generated
triangulated category. The statements the affine reduction of [stacks 0DJ8] needs are statements
about *cohomology*, so the functors they compare are homological rather than triangulated, and
there is no cone to put the five lemma on. This file redoes the same four closure steps for a
morphism `θ : H ⟶ H'` of homological functors:

* isomorphisms, by naturality;
* direct sums, by comparing the two colimit cocones that preservation supplies;
* extensions in a distinguished triangle, by the five lemma applied to the two long exact
  sequences — this is the step that differs, and it is why the invertibility of `θ` has to be
  carried at *every* shift of an object rather than at the object alone;
* shifts, which for a homological functor are not a consequence of the other steps and are
  therefore part of the induction hypothesis.

The object property the dévissage propagates is accordingly
`fun X => ∀ n : ℤ, IsIso (θ.app (X⟦n⟧))`, not `fun X => IsIso (θ.app X)`: a homological functor
loses the information of the shifts, and the long exact sequence of a triangle mixes degree `n`
with degree `n + 1`.

The long exact sequence is assembled by hand out of `CategoryTheory.Functor.IsHomological`
applied to a triangle and to its first two rotations, rather than through Mathlib's
`CategoryTheory.Functor.homologySequenceδ`. The reason is that every arrow of the resulting
`CategoryTheory.ComposableArrows` is then literally `H.map` of a morphism of `D`, so that the
comparison of the two rows is `θ` at each vertex and each of its four squares is an instance of
naturality; a connecting morphism produced by a shift sequence would need `θ` to be compatible
with that extra structure.

## Main results

* `StacksDraft.HomologicalDevissage.isIso_app_obj₃`: the five lemma step.
* `StacksDraft.HomologicalDevissage.isIso_app_shift_of_isCompactlyGenerated` and
  `StacksDraft.HomologicalDevissage.isIso_of_isCompactlyGenerated`: the dévissage itself.
* `StacksDraft.HomologicalDevissage.isIso_app_shift_of_isIso_app_shift_regularModule` and
  `StacksDraft.HomologicalDevissage.isIso_of_isIso_app_shift_regularModule`: its form
  for `D(R)`, where the regular module in degree zero is a compact generator. As in the
  triangulated case the model of the derived category is pinned to one whose morphisms live in
  the module universe, `[HasDerivedCategory.{u} (ModuleCat.{u} R)]`, because that is the only
  place where the compactness available and the compactness the cell presentation tests agree.

## References

* [The Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty

namespace StacksDraft.HomologicalDevissage

open StacksDraft.NatTransDevissage

universe v v' u u'

/-! ### The long exact sequence of a triangle as a five-term row -/

section Rows

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {A : Type u'} [Category.{v'} A] [Abelian A]

/-- Five consecutive terms of the long exact sequence of a homological functor at a triangle:
`H(X₁) ⟶ H(X₂) ⟶ H(X₃) ⟶ H(X₁⟦1⟧) ⟶ H(X₂⟦1⟧)`. Every arrow is `H.map` of a morphism of the
triangle or of one of its rotations. -/
def homologyRow (H : D ⥤ A) (T : Triangle D) : ComposableArrows A 4 :=
  ComposableArrows.mk₄ (H.map T.mor₁) (H.map T.mor₂) (H.map T.mor₃) (H.map T.rotate.mor₃)

/-- The five-term row of a distinguished triangle is exact: its three interior positions are
the exactness of `H` at the triangle, at its rotation and at its double rotation. -/
lemma homologyRow_exact (H : D ⥤ A) [H.IsHomological] (T : Triangle D)
    (hT : T ∈ distTriang D) : (homologyRow H T).Exact :=
  ComposableArrows.exact_of_δ₀ (H.map_distinguished_exact T hT).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (H.map_distinguished_exact T.rotate (rot_of_distTriang _ hT)).exact_toComposableArrows
      (H.map_distinguished_exact T.rotate.rotate
          (rot_of_distTriang _ (rot_of_distTriang _ hT))).exact_toComposableArrows)

variable {H H' : D ⥤ A} (θ : H ⟶ H')

/-- The comparison of the two five-term rows induced by `θ`: it is `θ` at each of the five
vertices, and each of its four squares is an instance of naturality. -/
def homologyRowHom (T : Triangle D) : homologyRow H T ⟶ homologyRow H' T :=
  ComposableArrows.homMk₄ (θ.app T.obj₁) (θ.app T.obj₂) (θ.app T.obj₃)
    (θ.app (T.obj₁⟦(1 : ℤ)⟧)) (θ.app (T.obj₂⟦(1 : ℤ)⟧))
    (θ.naturality _) (θ.naturality _) (θ.naturality _) (θ.naturality _)

end Rows

/-! ### The five lemma step -/

section FiveLemma

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {A : Type u'} [Category.{v'} A] [Abelian A]
  {H H' : D ⥤ A} [H.IsHomological] [H'.IsHomological] (θ : H ⟶ H')

/-- **The five lemma step.** `θ` is invertible at the third vertex of a distinguished triangle
as soon as it is invertible at the first two vertices and at their shifts by one. -/
theorem isIso_app_obj₃ (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : IsIso (θ.app T.obj₁)) (h₂ : IsIso (θ.app T.obj₂))
    (h₁' : IsIso (θ.app (T.obj₁⟦(1 : ℤ)⟧))) (h₂' : IsIso (θ.app (T.obj₂⟦(1 : ℤ)⟧))) :
    IsIso (θ.app T.obj₃) := by
  have := h₁
  have := h₂
  have := h₁'
  have := h₂'
  refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (homologyRow_exact H T hT)
    (homologyRow_exact H' T hT) (homologyRowHom θ T) ?_ ?_ ?_ ?_
  · change Epi (θ.app T.obj₁)
    infer_instance
  · change IsIso (θ.app T.obj₂)
    infer_instance
  · change IsIso (θ.app (T.obj₁⟦(1 : ℤ)⟧))
    infer_instance
  · change Mono (θ.app (T.obj₂⟦(1 : ℤ)⟧))
    infer_instance

/-- The five lemma step, carried at every shift: if `θ` is invertible at every shift of the
first two vertices of a distinguished triangle, it is invertible at every shift of the third.
The shifted triangle is distinguished, so each degree is an instance of `isIso_app_obj₃`. -/
theorem isIso_app_shift_obj₃ (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : ∀ n : ℤ, IsIso (θ.app (T.obj₁⟦n⟧))) (h₂ : ∀ n : ℤ, IsIso (θ.app (T.obj₂⟦n⟧)))
    (n : ℤ) : IsIso (θ.app (T.obj₃⟦n⟧)) :=
  isIso_app_obj₃ θ ((Triangle.shiftFunctor D n).obj T)
    (Triangle.shift_distinguished T hT n) (h₁ n) (h₂ n)
    (isIso_app_of_iso θ ((shiftFunctorAdd' D n 1 (n + 1) rfl).app T.obj₁) (h₁ (n + 1)))
    (isIso_app_of_iso θ ((shiftFunctorAdd' D n 1 (n + 1) rfl).app T.obj₂) (h₂ (n + 1)))

end FiveLemma

/-! ### Direct sums of shifts -/

section DirectSums

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
  {A : Type u'} [Category.{v'} A]
  {H H' : D ⥤ A}
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H']
  (θ : H ⟶ H')

/-- `θ` is invertible at every shift of a direct sum of shifts of a family on which it is
invertible in every degree. This is the object property that the cell presentation puts on the
base of its tower and on each of the cells attached along the way. -/
lemma isIso_app_shift_of_colimitsOfShape_shiftClosure {ι : Type v} (E : ι → D)
    (hθ : ∀ (i : ι) (m : ℤ), IsIso (θ.app ((E i)⟦m⟧))) (Y : D)
    (hY : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y)
    (n : ℤ) : IsIso (θ.app (Y⟦n⟧)) := by
  rw [ObjectProperty.prop_iSup_iff] at hY
  obtain ⟨J, hJ⟩ := hY
  obtain ⟨p⟩ := hJ
  refine isIso_app_of_isColimit θ (p.diag ⋙ shiftFunctor D n)
    (isColimitOfPreserves (shiftFunctor D n) p.isColimit) fun j => ?_
  obtain ⟨W, m, e, ⟨i⟩⟩ := p.prop_diag_obj j
  exact isIso_app_of_iso θ
    ((shiftFunctorAdd' D m n (m + n) rfl).app (E i) ≪≫ (shiftFunctor D n).mapIso e.symm)
    (hθ i (m + n))

end DirectSums

/-! ### The dévissage -/

section Devissage

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{v} D]
  {A : Type u'} [Category.{v'} A] [Abelian A]
  {H H' : D ⥤ A} [H.IsHomological] [H'.IsHomological]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) H']
  (θ : H ⟶ H')

/-- **The dévissage for homological functors.** Let `D` be a pre-triangulated category with
direct sums generated by a family `E` of compact objects, and let `H, H' : D ⥤ A` be homological
functors into an abelian category which preserve those direct sums. A morphism `θ : H ⟶ H'`
which is invertible at every shift of each `E i` is invertible at every shift of every object.

Every object `X` of `D` has a cell presentation `X = hocolim Xₙ` whose base and whose attached
cells are direct sums of shifts of the `E i` ([stacks 09SN]); `θ` is invertible in all degrees
on all of those by the direct-sum step, hence on each `Xₙ` by the five lemma step, hence on
`∐ Xₙ` and so on `X` itself. -/
theorem isIso_app_shift_of_isCompactlyGenerated {ι : Type v} (E : ι → D)
    (hEc : ∀ i, IsCompactObject.{v} (E i))
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y)
    (hθ : ∀ (i : ι) (m : ℤ), IsIso (θ.app ((E i)⟦m⟧)))
    (X : D) (n : ℤ) : IsIso (θ.app (X⟦n⟧)) := by
  have := hEc
  obtain ⟨W, hcolim, h₀, hstep⟩ :=
    Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated E hE X
  have hW : ∀ (k : ℕ) (m : ℤ), IsIso (θ.app ((W.obj k)⟦m⟧)) := by
    intro k
    induction k with
    | zero => exact isIso_app_shift_of_colimitsOfShape_shiftClosure θ E hθ _ h₀
    | succ k ih =>
        obtain ⟨Y, hY, f, g, hT⟩ := hstep k
        exact isIso_app_shift_obj₃ θ (Triangle.mk f (W.map (homOfLE (Nat.le_succ k))) g) hT
          (isIso_app_shift_of_colimitsOfShape_shiftClosure θ E hθ _ hY) ih
  obtain ⟨p, q, hT⟩ := hcolim
  -- the direct sum in the defining triangle of the derived colimit is indexed by `ℕ`, which is
  -- `ULift.{v} ℕ` up to an equivalence of discrete categories
  have : PreservesColimitsOfShape (Discrete ℕ) H :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) H
  have : PreservesColimitsOfShape (Discrete ℕ) H' :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) H'
  have hsum : ∀ m : ℤ, IsIso (θ.app ((∐ W.obj)⟦m⟧)) := fun m =>
    isIso_app_of_isColimit θ (Discrete.functor W.obj ⋙ shiftFunctor D m)
      (isColimitOfPreserves (shiftFunctor D m) (colimit.isColimit _)) fun j => hW j.as m
  exact isIso_app_shift_obj₃ θ _ hT hsum hsum n

/-- The dévissage, read as the invertibility of `θ` in the functor category: the shift by zero
is an isomorphism, so invertibility at every shift includes invertibility at the object. -/
theorem isIso_of_isCompactlyGenerated {ι : Type v} (E : ι → D)
    (hEc : ∀ i, IsCompactObject.{v} (E i))
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y)
    (hθ : ∀ (i : ι) (m : ℤ), IsIso (θ.app ((E i)⟦m⟧))) : IsIso θ := by
  have h : ∀ X, IsIso (θ.app X) := fun X =>
    isIso_app_of_iso θ ((shiftFunctorZero D ℤ).app X)
      (isIso_app_shift_of_isCompactlyGenerated θ E hEc hE hθ X 0)
  have := h
  exact NatIso.isIso_of_isIso_app θ

end Devissage

/-! ### The case of the derived category of a ring -/

section DerivedModuleCat

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  {A : Type u'} [Category.{v'} A] [Abelian A]
  {H H' : DerivedCategory (ModuleCat.{u} R) ⥤ A} [H.IsHomological] [H'.IsHomological]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J) H]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J) H']
  (θ : H ⟶ H')

/-- **Two homological direct-sum-preserving functors out of `D(R)` which agree on every shift of
`R[0]` agree.** A morphism `θ : H ⟶ H'` of homological functors out of a chosen derived category
of `R`-modules which preserve direct sums is invertible at every shift of every object as soon
as it is invertible at every shift of the regular module placed in degree zero.

The hypothesis `[HasDerivedCategory.{u} (ModuleCat.{u} R)]` is a *free* choice of model, and the
morphism universe `u` is forced rather than chosen, exactly as in
`StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule`. -/
theorem isIso_app_shift_of_isIso_app_shift_regularModule
    (hθ : ∀ m : ℤ, IsIso (θ.app
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦m⟧)))
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) : IsIso (θ.app (X⟦n⟧)) := by
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} R) :=
    StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat.{u, u}
  have : IsCompactObject.{u} (ModuleCat.of R R) :=
    StacksDraft.Perfect.isCompactObject_regularModule
  have : HasCoproducts.{u} (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory (ModuleCat.{u} R)
  have hgen := StacksDraft.Perfect.isWeakTriangulatedGenerator_regularModule (R := R)
  -- `ObjectProperty.singleton` is indexed by `Unit : Type 0`, while the dévissage needs its
  -- index type in the morphism universe; the two generating properties are compared by hand
  have hle : ∀ Z : DerivedCategory (ModuleCat.{u} R),
      ((ObjectProperty.singleton ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).shiftClosure ℤ) Z →
        ((ObjectProperty.ofObj (fun _ : PUnit.{u + 1} =>
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R R))).shiftClosure ℤ) Z := by
    intro Z hZ
    obtain ⟨W, m, e, ⟨_⟩⟩ := hZ
    exact ⟨_, m, e, ObjectProperty.ofObj_apply _ PUnit.unit⟩
  exact isIso_app_shift_of_isCompactlyGenerated θ
    (fun _ : PUnit.{u + 1} => (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))
    (fun _ => StacksDraft.Perfect.isCompactObject_derived_single _ 0)
    (fun Y hY => hgen Y fun {_Z} f hZ => hY f (hle _ hZ)) (fun _ => hθ) X n

/-- The dévissage over `D(R)`, read as the invertibility of `θ` in the functor category. -/
theorem isIso_of_isIso_app_shift_regularModule
    (hθ : ∀ m : ℤ, IsIso (θ.app
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦m⟧))) :
    IsIso θ := by
  have h : ∀ X, IsIso (θ.app X) := fun X =>
    isIso_app_of_iso θ ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app X)
      (isIso_app_shift_of_isIso_app_shift_regularModule θ hθ X 0)
  have := h
  exact NatIso.isIso_of_isIso_app θ

end DerivedModuleCat

end StacksDraft.HomologicalDevissage

end
