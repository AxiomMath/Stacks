module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring

/-!
# The projection formula on the zeroth K-group of a triangulated category

Let `C` act on `D` and `C'` act on `D'` by tensor products exact in each variable, so that
`K₀(D)` is a module over the Grothendieck ring `K₀(C)` and `K₀(D')` is one over `K₀(C')`
(`CategoryTheory.Pretriangulated.K0.TensorAction.module`). Let `F : D ⥤ D'` be an exact
"pushforward" and `G : C' ⥤ C` an exact "pullback". The **projection formula** is the identity

`F(G(β) · α) = β · F(α)` in `K₀(D')`, for `α ∈ K₀(D)` and `β ∈ K₀(C')`,

where the two products are the two module structures and `F`, `G` are read as the induced
homomorphisms of [Stacks, Tag 0FCQ]. This file proves it from a single piece of data: an
isomorphism of *objects*

`F(G(Y) ⊗ W) ≅ Y ⊗ F(W)` for `Y : C'` and `W : D`,

with no naturality and no coherence, which is all `K₀` can see — the same economy
`TensorStructure` and `TensorAction` already practise for their associators and unitors.

## Main definitions

* `CategoryTheory.Pretriangulated.K0.liftFunctor`: the restriction of a functor `C ⥤ D` to
  triangulated subcategories `P ⊆ C` and `Q ⊆ D`, when it carries `P` into `Q`, together with
  its shift-commutation data `liftFunctorCommShift` and its exactness
  `liftFunctor_isTriangulated`. This is the one-variable companion of `liftBifunctor`.
* `CategoryTheory.Pretriangulated.K0.mapSubcategory`: the resulting homomorphism
  `K₀(P) ⟶ K₀(Q)`, with `mapSubcategory_cls` its defining property.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.selfAction`: a tensor structure on `C`
  acting on `C` itself, which is the case `D = C` of a `TensorAction`.

## Main results

* `CategoryTheory.Pretriangulated.K0.smul_map_comm`: the projection formula, phrased with the
  bilinear pairings `TensorAction.smul`.
* `CategoryTheory.Pretriangulated.K0.map_smul`: the same identity phrased with the scalar
  multiplication of the two module structures, so that it literally reads
  `F (G β • α) = β • F α`.
* `CategoryTheory.Pretriangulated.K0.map_id`: `K₀(𝟭) = id`, which is what lets `G = 𝟭` be
  substituted into the projection formula.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.map_tensorObj_mul`: the projection formula
  at the pushforward "tensor with a fixed object `Z`" and the pullback `𝟭`, where the object
  isomorphism is assembled from the associator and the braiding. It says that multiplication by
  `[Z]` on `K₀(C)` commutes with multiplication by any other class.

## Relation to Tag 0FDM

The identity below is the K-group argument of [Stacks, Tag 0FDM], the projection formula
`f_*(α · f^*β) = f_*α · β` for a proper morphism of locally Noetherian schemes, in the case where
all the objects involved are bounded: the object isomorphism `e` is then the derived projection
formula `Rf_*E ⊗^𝐋_{𝒪_Y} K ≅ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` of [Stacks, Tag 08EU]. The tag itself is
`AlgebraicGeometry.properPushforward_perfectCoherentSMul_perfectPullbackKZero`, which works with
the parity Euler class of `StacksFrontier/AlgebraicGeometry/Perfect/ProjectionFormulaKZero` so as to
cover locally Noetherian schemes that are not quasi-compact, on which the derived direct image of
a coherent sheaf need not be bounded.

## References

* [Stacks, Tag 0FCQ](https://stacks.math.columbia.edu/tag/0FCQ)
* [Stacks, Tag 0FCT](https://stacks.math.columbia.edu/tag/0FCT)
* [Stacks, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks, Tag 0FDM](https://stacks.math.columbia.edu/tag/0FDM)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.K0

universe v u v' u' w t w' t'

/-! ### The induced homomorphism of the identity functor -/

section Identity

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The homomorphism induced on `K₀` by the identity functor is the identity. -/
@[simp] theorem map_id : map (𝟭 C) = AddMonoidHom.id (K0 C) :=
  hom_ext fun X => by rw [map_cls, AddMonoidHom.id_apply]; rfl

end Identity

/-! ### K₀ of a triangulated subcategory, functorially -/

section LiftFunctor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (P : ObjectProperty C) (Q : ObjectProperty D) [P.IsTriangulated] [Q.IsTriangulated]
  (F : C ⥤ D) (hF : ∀ Y : C, P Y → Q (F.obj Y))

/-- The restriction of a functor `C ⥤ D` to full subcategories, the source to `P` and the
target to `Q`, when `F` carries `P` into `Q`. This is the one-variable companion of
`liftBifunctor`. -/
def liftFunctor (hF : ∀ Y : C, P Y → Q (F.obj Y)) : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) fun Y => hF Y.obj Y.property

/-- The restricted functor commutes with the inclusions of the subcategories. -/
def liftFunctorCompιIso : liftFunctor P Q F hF ⋙ Q.ι ≅ P.ι ⋙ F :=
  Q.liftCompιIso (P.ι ⋙ F) fun Y => hF Y.obj Y.property

/-- The restricted functor commutes with the shift, because composing it with the inclusion of
`Q` identifies it with the inclusion of `P` followed by `F`, and that inclusion is fully
faithful.

The shift-commutation of `F` is an explicit argument rather than an instance, exactly as in
`liftBifunctor`: the categories here are usually derived categories whose `HasShift` instance a
caller reaches by a different route than the one a declared `CommShift` instance was elaborated
against, and then instance *search* does not match the two even though they are definitionally
equal. Passing the datum lets the unifier do it. -/
@[instance_reducible]
noncomputable def liftFunctorCommShift (cs : F.CommShift ℤ) :
    (liftFunctor P Q F hF).CommShift ℤ :=
  letI := cs
  Functor.CommShift.ofComp (liftFunctorCompιIso P Q F hF) ℤ

/-- The restriction of an exact functor is exact: after composing with the inclusion of `Q` it
becomes the inclusion of `P` followed by `F`, and the inclusion is exact and detects
exactness. -/
theorem liftFunctor_isTriangulated (cs : F.CommShift ℤ)
    (hT : letI := cs; F.IsTriangulated) :
    letI := liftFunctorCommShift P Q F hF cs
    (liftFunctor P Q F hF).IsTriangulated := by
  let := cs
  let := hT
  let := liftFunctorCommShift P Q F hF cs
  have : NatTrans.CommShift (liftFunctorCompιIso P Q F hF).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (liftFunctorCompιIso P Q F hF) ℤ
  exact (Functor.isTriangulated_iff_comp_right (liftFunctorCompιIso P Q F hF)).2 inferInstance

/-- **The homomorphism `K₀(P) ⟶ K₀(Q)` induced by an exact functor carrying `P` into `Q`.**
This is [Stacks, Tag 0FCQ] for the restricted functor; it is the construction that turns an
exact functor between two ambient triangulated categories into a map of the `K`-groups of
triangulated subcategories of them. -/
noncomputable def mapSubcategory (cs : F.CommShift ℤ) (hT : letI := cs; F.IsTriangulated) :
    K0 P.FullSubcategory →+ K0 Q.FullSubcategory :=
  letI := liftFunctorCommShift P Q F hF cs
  letI := liftFunctor_isTriangulated P Q F hF cs hT
  map (liftFunctor P Q F hF)

/-- `mapSubcategory` sends the class of an object of `P` to the class of its image, taken in
`Q`. -/
@[simp] theorem mapSubcategory_cls (cs : F.CommShift ℤ) (hT : letI := cs; F.IsTriangulated)
    (Y : P.FullSubcategory) :
    mapSubcategory P Q F hF cs hT (cls Y) = cls ⟨F.obj Y.obj, hF Y.obj Y.property⟩ := by
  let := liftFunctorCommShift P Q F hF cs
  let := liftFunctor_isTriangulated P Q F hF cs hT
  exact map_cls (liftFunctor P Q F hF) Y

/-- **`mapSubcategory` together with its characterising property, asserted at once.**

The ambient instances of `C` and `D` occur in the type of `mapSubcategory` only inside the
instances of `K₀(P)` and `K₀(Q)`, where they are *not* recoverable — the zero object of
`P.FullSubcategory` comes from `ObjectProperty.ContainsZero` and not from a zero object of `C`.
Against an *ascribed* existential type they are all fixed by unification instead. -/
theorem exists_mapSubcategory (cs : F.CommShift ℤ) (hT : letI := cs; F.IsTriangulated) :
    ∃ φ : K0 P.FullSubcategory →+ K0 Q.FullSubcategory,
      ∀ Y : P.FullSubcategory, φ (cls Y) = cls ⟨F.obj Y.obj, hF Y.obj Y.property⟩ :=
  ⟨mapSubcategory P Q F hF cs hT, mapSubcategory_cls P Q F hF cs hT⟩

end LiftFunctor

/-! ### A tensor structure acting on its own category -/

section SelfAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A tensor structure on `C` acts on `C` itself: the action is the tensor product, its
associator is the associator, and its unitor is the left unitor.

This is the diagonal case `D = C` of `TensorAction`, and it is what makes the projection formula
below specialise to a statement about the Grothendieck *ring* rather than only about a module
over it. -/
def TensorStructure.selfAction (T : TensorStructure C) : TensorAction T C where
  act := T.tensor
  commShiftRight := T.commShiftRight
  isTriangulatedRight := T.isTriangulatedRight
  commShiftLeft := T.commShiftLeft
  isTriangulatedLeft := T.isTriangulatedLeft
  associator := T.associator
  unitor := T.leftUnitor

/-- The action of the self-action is the tensor product. -/
@[simp] theorem TensorStructure.selfAction_act (T : TensorStructure C) :
    T.selfAction.act = T.tensor :=
  rfl

/-- The pairing of the self-action is the multiplication of the Grothendieck ring: both are
the bilinear map of [Stacks, Tag 0FCT] attached to the same bifunctor with the same exactness
data. -/
theorem TensorStructure.selfAction_smul (T : TensorStructure C) : T.selfAction.smul = T.mul :=
  rfl

end SelfAction

/-! ### The projection formula -/

section Projection

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {T : TensorStructure C}
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {C' : Type t} [Category.{w} C'] [HasZeroObject C'] [HasShift C' ℤ] [Preadditive C']
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C'] {T' : TensorStructure C'}
  {D' : Type t'} [Category.{w'} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  (A : TensorAction T D) (A' : TensorAction T' D')
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  (G : C' ⥤ C) [G.CommShift ℤ] [G.IsTriangulated]

omit [G.CommShift ℤ] [G.IsTriangulated] in
/-- **The projection formula on `K₀`, one scalar at a time.** Fix an object `Y` of `C'`. If the
pushforward of the result of acting by `G Y` is the result of acting by `Y` on the pushforward,
object by object, then the same holds of every element of `K₀(D)`. -/
theorem map_comp_smul_cls
    (e : ∀ (Y : C') (W : D),
      F.obj ((A.act.obj (G.obj Y)).obj W) ≅ (A'.act.obj Y).obj (F.obj W))
    (Y : C') :
    (map F).comp (A.smul (cls (G.obj Y))) = (A'.smul (cls Y)).comp (map F) :=
  hom_ext fun W => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, A.smul_cls, map_cls, map_cls,
      A'.smul_cls]
    exact cls_eq_of_iso (e Y W)

/-- **The projection formula on `K₀`**, phrased with the bilinear pairings of
[Stacks, Tag 0FCT]: for an exact pushforward `F : D ⥤ D'`, an exact pullback `G : C' ⥤ C` and an
object isomorphism `F(G Y ⊗ W) ≅ Y ⊗ F W`,

`F (G β · α) = β · F α` for `α ∈ K₀(D)` and `β ∈ K₀(C')`.

Only the isomorphism of objects is used: `K₀` identifies isomorphic objects
(`cls_eq_of_iso`), so no naturality in `Y` or `W` and no coherence is needed. -/
theorem smul_map_comm
    (e : ∀ (Y : C') (W : D),
      F.obj ((A.act.obj (G.obj Y)).obj W) ≅ (A'.act.obj Y).obj (F.obj W))
    (y : K0 C') (w : K0 D) :
    map F (A.smul (map G y) w) = A'.smul y (map F w) := by
  have outer : (map F).comp (((evalHom w).comp A.smul).comp (map G)) =
      (evalHom (map F w)).comp A'.smul := by
    refine hom_ext fun Y => ?_
    simp only [AddMonoidHom.comp_apply, evalHom_apply, map_cls]
    exact congrArg (fun f : K0 D →+ K0 D' => f w) (map_comp_smul_cls A A' F G e Y)
  exact congrArg (fun f : K0 C' →+ K0 D' => f y) outer

/-- **The projection formula on `K₀`, in module notation.** The statement of `smul_map_comm`
read through the two module structures of `TensorAction.module`, where it literally says

`F (G β • α) = β • F α`. -/
theorem map_smul
    (e : ∀ (Y : C') (W : D),
      F.obj ((A.act.obj (G.obj Y)).obj W) ≅ (A'.act.obj Y).obj (F.obj W))
    (y : K0 C') (w : K0 D) :
    letI := T.commRing
    letI := A.module
    letI := T'.commRing
    letI := A'.module
    map F ((map G y : K0 C) • w) = y • map F w :=
  smul_map_comm A A' F G e y w

end Projection

/-! ### The projection formula at a tensoring pushforward -/

section TensorPushforward

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The object isomorphism `Z ⊗ (Y ⊗ W) ≅ Y ⊗ (Z ⊗ W)` of a tensor structure, assembled from
two instances of the associator and one of the braiding.

This is the hypothesis `e` of `smul_map_comm` at the pushforward `F = Z ⊗ -` and the pullback
`G = 𝟭`. -/
def TensorStructure.tensorObjExchange (T : TensorStructure C) (Z Y : C) (W : C) :
    (T.tensor.obj Z).obj ((T.tensor.obj Y).obj W) ≅
      (T.tensor.obj Y).obj ((T.tensor.obj Z).obj W) :=
  (T.associator Z Y W).symm ≪≫ (T.tensor.mapIso (T.braiding Z Y)).app W ≪≫
    T.associator Y Z W

/-- **The projection formula at the pushforward `Z ⊗ -` and the pullback `𝟭`.** Multiplication
by the class of a fixed object `Z` on `K₀(C)`, read as the homomorphism induced by the exact
functor `Z ⊗ -`, commutes with multiplication by any element of `K₀(C)`.

Every binder of `smul_map_comm` is instantiated here from the fields of `T` alone: the
pushforward `Z ⊗ -` is exact by `T.isTriangulatedRight`, the pullback is `𝟭`, and the object
isomorphism is `TensorStructure.tensorObjExchange`. -/
theorem TensorStructure.map_tensorObj_mul (T : TensorStructure C) (Z : C) (y w : K0 C) :
    letI := T.commShiftRight Z
    letI := T.isTriangulatedRight Z
    map (T.tensor.obj Z) (T.mul y w) = T.mul y (map (T.tensor.obj Z) w) := by
  let := T.commShiftRight Z
  let := T.isTriangulatedRight Z
  have h := smul_map_comm T.selfAction T.selfAction (T.tensor.obj Z) (𝟭 C)
    (fun Y W => T.tensorObjExchange Z Y W) y w
  rwa [T.selfAction_smul, map_id, AddMonoidHom.id_apply] at h

end TensorPushforward

end CategoryTheory.Pretriangulated.K0

end

end
