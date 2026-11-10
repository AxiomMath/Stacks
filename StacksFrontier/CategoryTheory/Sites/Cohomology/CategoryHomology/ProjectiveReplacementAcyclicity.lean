module

public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementDeltaFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Acyclicity of the simplicial replacement of a projective presheaf

Let `C` be a small category.
`Stacks.CategoryHomology.representableReplacementComplex_homology_isZero` proves that the
simplicial replacement complex `K_•(F)` has vanishing homology in positive degrees for one
presheaf `F`: the extension by zero `j_{U!}ℤ_U` of the constant integer sheaf on the slice over
`U`. This file extends that computation to every projective presheaf.

## Main definitions

* `Stacks.CategoryHomology.directSumPresheaf`, with its summand inclusions
  `directSumPresheafIncl` and its universal morphism `directSumPresheafDesc`: the sectionwise
  direct sum of a family of abelian-group-valued presheaves, a coproduct of the family.
* `Stacks.CategoryHomology.freeRepresentablePresheaf` and
  `Stacks.CategoryHomology.freeCover`: the free abelian presheaf on a representable, and the
  canonical presentation of a presheaf by a direct sum of such.
* `Stacks.CategoryHomology.directSumSwapHom` and `directSumSwapEquiv`: swapping the two
  indices of a double direct sum.

## Main results

* `Stacks.CategoryHomology.replacementComplex_homology_isZero_of_iso` and
  `replacementComplex_homology_isZero_of_retract`: acyclicity of the replacement in a fixed
  degree only depends on the presheaf up to isomorphism, and passes to retracts.
* `Stacks.CategoryHomology.freeRepresentablePresheaf_homology_isZero`: the free abelian
  presheaf `V ↦ ℤ^{(V ⟶ U)}` on a representable has acyclic replacement.
* `Stacks.CategoryHomology.replacementComplex_homology_isZero_of_directSum`: acyclicity in a
  fixed degree passes to a sectionwise direct sum of presheaves.
* `Stacks.CategoryHomology.projective_replacementComplex_homology_isZero`: `Hₙ(K_•(P)) = 0`
  for `n > 0` and `P` projective, together with its sheaf-level form
  `projective_chaoticSheafReplacementComplex_homology_isZero`.

## Implementation notes

Coproducts are built by hand as sectionwise direct sums (`directSumPresheaf`), not taken as `∐`
in the presheaf category.

`Stacks.CategoryHomology.directSumSwapHom` and its computation rules are stated for an abstract
family: at a concrete family the `AddCommMonoid` instance on a summand is found by two different
routes and no rewrite fires, which is also why `replacementGroupDirectSumEquiv_ladder` is proved
by a term-mode chain of `Eq.trans`. `directSumSwapEquiv_apply` unfolds the equivalence at an
abstract family, where the terms are small; at a concrete family the same `rfl` exhausts the
`whnf` budget.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryHomology

universe u v w

variable {C : Type u} [SmallCategory C]

/-- The free abelian presheaf on a representable: `V ↦ ℤ^{(V ⟶ U)}`, the free abelian group on
the set of arrows to `U`. On a chaotic site this is the extension by zero of the constant
integer sheaf from the slice site over `U`
(`Stacks.CategoryHomology.integerExtensionByZero_iso_freeYoneda`). -/
abbrev freeRepresentablePresheaf (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj U ⋙ AddCommGrpCat.free

/-- Vanishing of the homology of the simplicial replacement in a fixed degree depends on the
presheaf only through its isomorphism class. -/
theorem replacementComplex_homology_isZero_of_iso {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (e : F ≅ G)
    (n : ℕ) (h : IsZero ((simplicialReplacementComplex G).homology n)) :
    IsZero ((simplicialReplacementComplex F).homology n) :=
  h.of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((replacementComplexFunctor (C := C)).mapIso e))

/-- Vanishing of the homology of the simplicial replacement in a fixed degree passes to
retracts. -/
theorem replacementComplex_homology_isZero_of_retract {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F) (n : ℕ)
    (h : IsZero ((simplicialReplacementComplex G).homology n)) :
    IsZero ((simplicialReplacementComplex F).homology n) := by
  let T : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    replacementComplexFunctor (C := C) ⋙ HomologicalComplex.homologyFunctor _ _ n
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (T.obj F) = 0
  rw [← T.map_id, ← hir, T.map_comp, (show IsZero (T.obj G) from h).eq_of_tgt (T.map i) 0,
    zero_comp]

/-- The simplicial replacement complex of the free abelian presheaf on a representable has
vanishing homology in every positive degree. -/
theorem freeRepresentablePresheaf_homology_isZero (U : C) (n : ℕ) (hn : 0 < n) :
    IsZero ((simplicialReplacementComplex (freeRepresentablePresheaf U)).homology n) :=
  replacementComplex_homology_isZero_of_iso
    (integerExtensionByZero_iso_freeYoneda U).symm n
    (representableReplacementComplex_homology_isZero U n hn)


section DirectSum

open scoped DirectSum

/-- The degree-`n` component of the simplicial replacement complex functor is
`Stacks.CategoryHomology.replacementGroupMap`. -/
lemma replacementComplexFunctor_map_f {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) (n : ℕ) :
    ((replacementComplexFunctor (C := C)).map η).f n = replacementGroupMap η n :=
  (simplicialReplacementComplexFunctor (C := C)).property.2.1 η n rfl rfl

/-- Swapping the two indices of a double direct sum: the summand indexed by `(i, j)` goes to
the summand indexed by `(j, i)`. -/
def directSumSwapHom {I J : Type*} [DecidableEq I] (A : I → J → Type*)
    [∀ i j, AddCommMonoid (A i j)] : (⨁ i, ⨁ j, A i j) →+ (⨁ j, ⨁ i, A i j) :=
  DirectSum.toAddMonoid fun i ↦ DirectSum.map fun j ↦ DirectSum.of (fun i' ↦ A i' j) i

/-- The value of `Stacks.CategoryHomology.directSumSwapHom` on the `i`th summand: it is the
degreewise inclusion of the `i`th summand of each inner sum. -/
lemma directSumSwapHom_apply_of {I J : Type*} [DecidableEq I] (A : I → J → Type*)
    [∀ i j, AddCommMonoid (A i j)] (i : I) (y : ⨁ j, A i j) :
    directSumSwapHom A (DirectSum.of (fun i' ↦ ⨁ j', A i' j') i y) =
      DirectSum.map (fun j ↦ DirectSum.of (fun i' ↦ A i' j) i) y := by
  change (DirectSum.toAddMonoid fun i ↦ DirectSum.map fun j ↦
      DirectSum.of (fun i' ↦ A i' j) i) (DirectSum.of (fun i' ↦ ⨁ j', A i' j') i y) = _
  rw [DirectSum.toAddMonoid_of]

/-- The computation rule for `Stacks.CategoryHomology.directSumSwapHom` on a generator. -/
@[simp]
lemma directSumSwapHom_of {I J : Type*} [DecidableEq I] [DecidableEq J] (A : I → J → Type*)
    [∀ i j, AddCommMonoid (A i j)] (i : I) (j : J) (a : A i j) :
    directSumSwapHom A (DirectSum.of (fun i' ↦ ⨁ j', A i' j') i
        (DirectSum.of (fun j' ↦ A i j') j a)) =
      DirectSum.of (fun j' ↦ ⨁ i', A i' j') j (DirectSum.of (fun i' ↦ A i' j) i a) := by
  rw [directSumSwapHom_apply_of, DirectSum.map_of]

/-- Swapping the two indices of a double direct sum, as an isomorphism: the two swaps are
mutually inverse. -/
def directSumSwapEquiv {I J : Type*} [DecidableEq I] [DecidableEq J] (A : I → J → Type*)
    [∀ i j, AddCommMonoid (A i j)] : (⨁ i, ⨁ j, A i j) ≃+ (⨁ j, ⨁ i, A i j) := by
  refine
    { directSumSwapHom A with
      toFun := directSumSwapHom A
      invFun := directSumSwapHom fun j i ↦ A i j
      left_inv := ?_
      right_inv := ?_ }
  · have h : (directSumSwapHom fun j i ↦ A i j).comp (directSumSwapHom A)
        = AddMonoidHom.id _ :=
      DirectSum.addHom_ext' fun i ↦ DirectSum.addHom_ext' fun j ↦ AddMonoidHom.ext fun a ↦ by simp
    exact DFunLike.congr_fun h
  · have h : (directSumSwapHom A).comp (directSumSwapHom fun j i ↦ A i j)
        = AddMonoidHom.id _ :=
      DirectSum.addHom_ext' fun j ↦ DirectSum.addHom_ext' fun i ↦ AddMonoidHom.ext fun a ↦ by simp
    exact DFunLike.congr_fun h

/-- `Stacks.CategoryHomology.directSumSwapEquiv` acts as
`Stacks.CategoryHomology.directSumSwapHom`. -/
@[simp]
lemma directSumSwapEquiv_apply {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : I → J → Type*) [∀ i j, AddCommMonoid (A i j)] (z : ⨁ i, ⨁ j, A i j) :
    directSumSwapEquiv A z = directSumSwapHom A z :=
  rfl

/-- `DirectSum.map` on the `i`th summand, as an identity of homomorphisms. -/
lemma directSum_map_comp_of {I : Type*} [DecidableEq I] {α β : I → Type*}
    [∀ i, AddCommMonoid (α i)] [∀ i, AddCommMonoid (β i)] (f : ∀ i, α i →+ β i) (i : I) :
    (DirectSum.map f).comp (DirectSum.of α i) = (DirectSum.of β i).comp (f i) := by
  ext x
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.map_of]

variable {ι : Type w} (F : ι → (Cᵒᵖ ⥤ AddCommGrpCat.{w}))

/-- The sectionwise direct sum of a family of abelian-group-valued presheaves, a coproduct of
the family. -/
@[implicit_reducible]
def directSumPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj Y := AddCommGrpCat.of (⨁ i, (F i).obj Y)
  map f := AddCommGrpCat.ofHom (DirectSum.map fun i ↦ ((F i).map f).hom)
  map_id Y := by
    have h : (fun i ↦ ((F i).map (𝟙 Y)).hom) = fun i ↦ AddMonoidHom.id ((F i).obj Y) := by
      funext i
      rw [(F i).map_id]
      rfl
    rw [h, DirectSum.map_id]
    rfl
  map_comp f g := by
    have h : (fun i ↦ ((F i).map (f ≫ g)).hom)
        = fun i ↦ (((F i).map g).hom).comp (((F i).map f).hom) := by
      funext i
      rw [(F i).map_comp]
      rfl
    rw [h, DirectSum.map_comp, AddCommGrpCat.ofHom_comp]

section DecidableIndex

variable [DecidableEq ι]

/-- The inclusion of the `i`th summand into the sectionwise direct sum. -/
def directSumPresheafIncl (i : ι) : F i ⟶ directSumPresheaf F where
  app Y := AddCommGrpCat.ofHom (DirectSum.of (fun j ↦ (F j).obj Y) i)
  naturality Y Z f := by
    ext x
    exact (DirectSum.map_of (fun j ↦ ((F j).map f).hom) i x).symm

/-- The morphism out of a sectionwise direct sum determined by a family of morphisms out of its
summands. -/
def directSumPresheafDesc {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (η : ∀ i, F i ⟶ G) :
    directSumPresheaf F ⟶ G where
  app Y := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun i ↦ ((η i).app Y).hom)
  naturality Y Z f := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext'
    intro i
    apply AddMonoidHom.ext
    intro x
    change (DirectSum.toAddMonoid fun j ↦ ((η j).app Z).hom)
        ((DirectSum.map fun j ↦ ((F j).map f).hom)
          (DirectSum.of (fun j ↦ ((F j).obj Y : Type w)) i x))
      = ((G.map f)) ((DirectSum.toAddMonoid fun j ↦ ((η j).app Y).hom)
          (DirectSum.of (fun j ↦ ((F j).obj Y : Type w)) i x))
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact NatTrans.naturality_apply (η i) f x

/-- The value of `Stacks.CategoryHomology.directSumPresheafDesc` on the `i`th summand. -/
lemma directSumPresheafDesc_app_of {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (η : ∀ i, F i ⟶ G) (i : ι)
    (Y : Cᵒᵖ) (x : (F i).obj Y) :
    (directSumPresheafDesc F η).app Y (DirectSum.of (fun j ↦ ((F j).obj Y : Type w)) i x) =
      (η i).app Y x := by
  change (DirectSum.toAddMonoid fun j ↦ ((η j).app Y).hom)
      (DirectSum.of (fun j ↦ ((F j).obj Y : Type w)) i x) = _
  rw [DirectSum.toAddMonoid_of]

/-- `Stacks.CategoryHomology.directSumPresheafDesc` is an epimorphism as soon as every section
of the target is the image of a section of some summand. -/
theorem epi_directSumPresheafDesc {G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (η : ∀ i, F i ⟶ G)
    (h : ∀ (Y : Cᵒᵖ) (s : (G.obj Y : Type w)), ∃ (i : ι) (x : ((F i).obj Y : Type w)),
      (η i).app Y x = s) :
    Epi (directSumPresheafDesc F η) := by
  have happ (Y : Cᵒᵖ) : Epi ((directSumPresheafDesc F η).app Y) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨i, x, hx⟩ := h Y s
    exact ⟨DirectSum.of (fun j ↦ ((F j).obj Y : Type w)) i x,
      (directSumPresheafDesc_app_of F η i Y x).trans hx⟩
  exact NatTrans.epi_of_epi_app _

section Comparison

variable [∀ p : ℕ, DecidableEq (ComposableArrows C p)]

/-- The degree-`p` comparison between the direct sum of the simplicial replacement groups of a
family and the simplicial replacement group of the sectionwise direct sum. Both are the direct
sum of the groups `Fᵢ(U₀)` over pairs of a string of arrows and an index, summed in the two
possible orders. -/
noncomputable def replacementGroupDirectSumEquiv (p : ℕ) :
    (⨁ i, (replacementGroup (F i) p : Type (max u w))) ≃+
      (replacementGroup (directSumPresheaf F) p : Type (max u w)) :=
  directSumSwapEquiv fun (i : ι) (x : ComposableArrows C p) ↦
    ((F i).obj (op x.right) : Type w)

/-- The degree-`p` comparison restricted to the `i`th summand is the map induced by the `i`th
summand inclusion of presheaves. -/
lemma replacementGroupDirectSumEquiv_comp_of (p : ℕ) (i : ι) :
    (replacementGroupDirectSumEquiv F p).toAddMonoidHom.comp
        (DirectSum.of (fun j ↦ (replacementGroup (F j) p : Type (max u w))) i)
      = (replacementGroupMap (directSumPresheafIncl F i) p).hom := by
  apply AddMonoidHom.ext
  intro y
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, replacementGroupDirectSumEquiv,
    directSumSwapEquiv_apply, directSumSwapHom_apply_of]
  rfl

/-- The degree-`p` comparison on a generator of the `i`th summand. -/
lemma replacementGroupDirectSumEquiv_of (p : ℕ) (i : ι)
    (y : (replacementGroup (F i) p : Type (max u w))) :
    replacementGroupDirectSumEquiv F p
        (DirectSum.of (fun j ↦ (replacementGroup (F j) p : Type (max u w))) i y) =
      replacementGroupMap (directSumPresheafIncl F i) p y :=
  DFunLike.congr_fun (replacementGroupDirectSumEquiv_comp_of F p i) y

/-- The ladder square: the degree-`p` comparison is compatible with the differentials of the
simplicial replacement complexes. -/
lemma replacementGroupDirectSumEquiv_ladder (p q : ℕ) :
    AddMonoidHom.comp ((simplicialReplacementComplex (directSumPresheaf F)).d p q).hom
        (replacementGroupDirectSumEquiv F p).toAddMonoidHom
      = AddMonoidHom.comp (replacementGroupDirectSumEquiv F q).toAddMonoidHom
          (DirectSum.map fun i ↦ ((simplicialReplacementComplex (F i)).d p q).hom) := by
  apply DirectSum.addHom_ext'
  intro i
  apply AddMonoidHom.ext
  intro y
  have hcomm := ((replacementComplexFunctor (C := C)).map (directSumPresheafIncl F i)).comm p q
  rw [replacementComplexFunctor_map_f, replacementComplexFunctor_map_f] at hcomm
  have h4 : ((simplicialReplacementComplex (directSumPresheaf F)).d p q).hom
        ((replacementGroupMap (directSumPresheafIncl F i) p).hom y)
      = (replacementGroupMap (directSumPresheafIncl F i) q).hom
        (((simplicialReplacementComplex (F i)).d p q).hom y) :=
    DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hcomm) y
  exact (congrArg (fun z ↦ ((simplicialReplacementComplex (directSumPresheaf F)).d p q).hom z)
      (replacementGroupDirectSumEquiv_of F p i y)).trans
    (h4.trans ((replacementGroupDirectSumEquiv_of F q i
        (((simplicialReplacementComplex (F i)).d p q).hom y)).symm.trans
      (congrArg (fun z ↦ replacementGroupDirectSumEquiv F q z)
        (DirectSum.map_of
          (fun j ↦ ((simplicialReplacementComplex (F j)).d p q).hom) i y).symm)))

end Comparison

end DecidableIndex

/-- **Acyclicity of the simplicial replacement passes to direct sums.** If the simplicial
replacement of each `Fᵢ` has vanishing homology in degree `n + 1`, so does the simplicial
replacement of the sectionwise direct sum. -/
theorem replacementComplex_homology_isZero_of_directSum (n : ℕ)
    (h : ∀ i, IsZero ((simplicialReplacementComplex (F i)).homology (n + 1))) :
    IsZero ((simplicialReplacementComplex (directSumPresheaf F)).homology (n + 1)) := by
  classical
  simp only [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
      (ChainComplex.next_nat_succ n),
    ShortComplex.ab_exact_iff_function_exact] at h ⊢
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (replacementGroupDirectSumEquiv F (n + 2)) (replacementGroupDirectSumEquiv F (n + 1))
    (replacementGroupDirectSumEquiv F n)
    (replacementGroupDirectSumEquiv_ladder F (n + 2) (n + 1))
    (replacementGroupDirectSumEquiv_ladder F (n + 1) n) ?_
  exact directSum_exact _ _ h

end DirectSum

section Projective

open scoped DirectSum

/-- The morphism out of the free abelian presheaf on a representable determined by a section
over the representing object: the generator `h : V ⟶ U` is sent to the restriction of the
section along `h`. -/
def freeRepresentableHom {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (U : C) (s : F.obj (op U)) :
    freeRepresentablePresheaf U ⟶ F where
  app Y := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun h : Y.unop ⟶ U ↦ (F.map h.op) s)
  naturality Y Z f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change (FreeAbelianGroup.lift fun h : Z.unop ⟶ U ↦ (F.map h.op) s)
        ((AddCommGrpCat.free.map ((yoneda.obj U).map f)) (FreeAbelianGroup.of g))
      = (F.map f) ((FreeAbelianGroup.lift fun h : Y.unop ⟶ U ↦ (F.map h.op) s)
          (FreeAbelianGroup.of g))
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    change (F.map (f.unop ≫ g).op) s = (F.map f) ((F.map g.op) s)
    rw [CategoryTheory.op_comp, F.map_comp, CategoryTheory.comp_apply]
    rfl

/-- The value of `Stacks.CategoryHomology.freeRepresentableHom` on the generator `𝟙 U`: it is
the given section. -/
lemma freeRepresentableHom_id {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (U : C) (s : F.obj (op U)) :
    (freeRepresentableHom U s).app (op U) (FreeAbelianGroup.of (𝟙 U)) = s := by
  change (FreeAbelianGroup.lift fun h : U ⟶ U ↦ (F.map h.op) s) (FreeAbelianGroup.of (𝟙 U)) = s
  rw [FreeAbelianGroup.lift_apply_of, op_id, F.map_id]
  rfl

/-- The index set of the canonical presentation of a presheaf: a pair of an object of `C` and a
section over it. -/
abbrev freeCoverIndex (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Type u :=
  Σ U : C, (F.obj (op U) : Type u)

/-- The canonical presentation of a presheaf by free abelian presheaves on representables: the
sectionwise direct sum of one copy of `freeRepresentablePresheaf U` for every section over
every `U`. -/
noncomputable def freeCover (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  directSumPresheaf fun i : freeCoverIndex F ↦ freeRepresentablePresheaf i.1

/-- The canonical presentation morphism, assembled from
`Stacks.CategoryHomology.freeRepresentableHom`. -/
noncomputable def freeCoverHom (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : freeCover F ⟶ F :=
  letI : DecidableEq (freeCoverIndex F) := Classical.decEq _
  directSumPresheafDesc _ fun i : freeCoverIndex F ↦ freeRepresentableHom i.1 i.2

/-- The canonical presentation morphism is an epimorphism. -/
instance freeCoverHom_epi (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Epi (freeCoverHom F) :=
  letI : DecidableEq (freeCoverIndex F) := Classical.decEq _
  epi_directSumPresheafDesc _ _ fun Y s ↦
    ⟨⟨Y.unop, s⟩, FreeAbelianGroup.of (𝟙 Y.unop), freeRepresentableHom_id Y.unop s⟩

/-- The canonical presentation of a presheaf has acyclic simplicial replacement in every
positive degree. -/
theorem freeCover_homology_isZero (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (hn : 0 < n) :
    IsZero ((simplicialReplacementComplex (freeCover F)).homology n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  exact replacementComplex_homology_isZero_of_directSum _ m
    fun i ↦ freeRepresentablePresheaf_homology_isZero i.1 (m + 1) hn

/-- **The simplicial replacement complex of a projective presheaf is acyclic.** For a
projective abelian-group-valued presheaf `P` on a small category, `Hₙ(K_•(P)) = 0` for every
`n > 0`. -/
theorem projective_replacementComplex_homology_isZero (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    [Projective P] (n : ℕ) (hn : 0 < n) :
    IsZero ((simplicialReplacementComplex P).homology n) :=
  replacementComplex_homology_isZero_of_retract
    (Projective.factorThru (𝟙 P) (freeCoverHom P)) (freeCoverHom P)
    (Projective.factorThru_comp _ _) n (freeCover_homology_isZero P n hn)

/-- The simplicial replacement complex of a projective abelian sheaf on the chaotic site has
vanishing homology in every positive degree. -/
theorem projective_chaoticSheafReplacementComplex_homology_isZero
    (P : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u}) [Projective P] (n : ℕ)
    (hn : 0 < n) :
    IsZero (((chaoticSheafReplacementComplexFunctor (C := C)).obj P).homology n) := by
  have hpp : (chaoticAbSheafEquivalence (C := C)).functor.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_isEquivalence
  exact projective_replacementComplex_homology_isZero
    ((chaoticAbSheafEquivalence (C := C)).functor.obj P) n hn

end Projective

end Stacks.CategoryHomology
