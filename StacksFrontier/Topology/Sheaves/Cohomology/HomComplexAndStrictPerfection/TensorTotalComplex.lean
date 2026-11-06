module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# The total tensor product of complexes of modules on a ringed space

Let `(X, O_X)` be a ringed space. The tensor product of two complexes `A` and `B` of
`O_X`-modules is the degreewise sheafification of the total complex of the tensor-product double
complex of the underlying complexes of presheaves of modules. Since sheafification preserves
direct sums, this is also the total complex of the sheaf tensor-product double complex; its
differential on bidegree `(t, r)` is `d₁ + (-1)^t d₂`, and neither boundedness nor finiteness
of the complexes is required.

This file records that complex, its functoriality, the local pure tensors that generate it, and
the vocabulary needed to specify a morphism out of it by its effect on those pure tensors: the
evaluation of a local section of an internal Hom complex on a local section of its source, and
the structure `Stacks.SheafOfModules.EvaluationConstruction` of [Stacks, Tag 0A8P].

## Main definitions

* `Stacks.SheafOfModules.underlyingComplex`: the underlying complex of presheaves of modules.
* `Stacks.SheafOfModules.tensorTotal` and `Stacks.SheafOfModules.tensorTotalMap`: the total
  tensor-product complex and the morphism induced by two chain maps.
* `Stacks.SheafOfModules.tensorTotalSection`: the local pure tensor of two homogeneous local
  sections, as a section of the total complex.
* `Stacks.SheafOfModules.applyHomSection`: evaluation of a homogeneous local section of an
  internal Hom complex on a local section of its source.
* `Stacks.SheafOfModules.EvaluationConstruction`: evaluation morphisms for internal Hom
  complexes, specified by the signed evaluation formula on homogeneous local pure tensors.

## Main results

* `Stacks.SheafOfModules.tensorTotalMap_comp`: functoriality of `tensorTotalMap`.
* `Stacks.SheafOfModules.tensorTotalMap_section`: its effect on a local pure tensor.
* `Stacks.SheafOfModules.applyHomSection_map`: the effect on evaluation of a map of internal
  Hom complexes induced by morphisms in the two variables.

## Implementation notes

The sign in `EvaluationConstruction.evaluate_tmul` is `(-1)^(r + (-a) * r)` with `a = r + s`,
where `t`, `r` and `s` are the degrees of the outer Hom section, of the section of `K` and of
the inner Hom section. It is the sign of the direct construction of [Stacks, Tag 0A60], to
which the proof of [Stacks, Tag 0A8P] refers.

The monoidal structure on presheaves of modules over the structure sheaf is Mathlib's, but
instance search cannot see it through the definition of `Stacks.structureSheaf`, which composes
with the forgetful functor to `RingCat`; the instances below name it for that spelling. They
are stated as the corresponding Mathlib terms, so there is only one monoidal structure in play.

## References

* [Stacks Project, Tag 0A8P](https://stacks.math.columbia.edu/tag/0A8P)
* [Stacks Project, Tag 0A60](https://stacks.math.columbia.edu/tag/0A60)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- The sections of the structure sheaf of rings over an open set form a commutative ring,
since they are the sections of a sheaf of commutative rings. -/
noncomputable instance commRing_structureSheaf_obj (U : (Opens X)ᵒᵖ) :
    CommRing ((structureSheaf Rc).obj.obj U) :=
  inferInstanceAs (CommRing (Rc.obj.obj U))

/-- The monoidal structure on presheaves of modules over the structure sheaf of rings. -/
noncomputable instance monoidalCategory_presheafOfModules :
    MonoidalCategory (PresheafOfModules.{u} (structureSheaf Rc).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := Rc.obj)

/-- The tensor product of presheaves of modules is additive in its first variable. -/
instance curriedTensor_additive :
    (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)).Additive where
  map_add := by
    intro A B f g
    apply NatTrans.ext
    funext C
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    exact TensorProduct.add_tmul _ _ _

/-- The tensor product of presheaves of modules is additive in its second variable. -/
instance curriedTensor_obj_additive (A : PresheafOfModules.{u} (structureSheaf Rc).obj) :
    ((curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)).obj A).Additive where
  map_add := by
    intro B C f g
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    exact TensorProduct.tmul_add _ _ _

/-- The underlying complex of presheaves of modules of a complex of `O_X`-modules. -/
noncomputable abbrev underlyingComplex (K : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (PresheafOfModules.{u} (structureSheaf Rc).obj) ℤ :=
  ((SheafOfModules.forget (structureSheaf Rc)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The total tensor-product complex, obtained by sheafifying the presheaf total complex
degreewise. -/
noncomputable abbrev tensorTotal (A B : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (StructureSheafModules Rc) ℤ :=
  ((PresheafOfModules.sheafification (𝟙 (structureSheaf Rc).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (HomologicalComplex.mapBifunctor (underlyingComplex Rc A) (underlyingComplex Rc B)
        (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ))

/-- The morphism of total tensor-product complexes induced by two chain maps. -/
noncomputable abbrev tensorTotalMap
    {A A' B B' : CochainComplex (StructureSheafModules Rc) ℤ} (f : A ⟶ A') (g : B ⟶ B') :
    tensorTotal Rc A B ⟶ tensorTotal Rc A' B' :=
  ((PresheafOfModules.sheafification (𝟙 (structureSheaf Rc).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (HomologicalComplex.mapBifunctorMap
        (((SheafOfModules.forget (structureSheaf Rc)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)
        (((SheafOfModules.forget (structureSheaf Rc)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g)
        (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ))

/-- The local pure tensor in bidegree `(t, r)`, included in the total complex and then mapped
to its sheafification. -/
noncomputable abbrev tensorTotalSection (A B : CochainComplex (StructureSheafModules Rc) ℤ)
    (U : Opens X) (t r : ℤ) (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal Rc A B).X (t + r)).val.obj (op U) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
    ((HomologicalComplex.mapBifunctor (underlyingComplex Rc A) (underlyingComplex Rc B)
      (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ)).X
        (t + r))).app (op U))
    ((HomologicalComplex.ιMapBifunctor (underlyingComplex Rc A) (underlyingComplex Rc B)
      (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ)
      t r (t + r) rfl).app (op U) (a ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] b))

/-- Evaluate a component of a homogeneous internal Hom section on a section of its source,
using the canonical identification with cochains on the open set. -/
noncomputable abbrev applyHomSection {K L : CochainComplex (StructureSheafModules Rc) ℤ}
    (H : SheafHomComplex Rc K L) (U : Opens X) (n p q : ℤ) (hpq : p + n = q)
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op U)) :
    (L.X q).val.obj (op U) :=
  (((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) f).v p q hpq).val.app
    (op (Over.mk (𝟙 U)))) x

/-- Evaluation morphisms of complexes, specified by the signed evaluation formula on
homogeneous local pure tensors. -/
structure EvaluationConstruction where
  /-- The evaluation morphism attached to three complexes. -/
  evaluate : (K L M : CochainComplex (StructureSheafModules Rc) ℤ) →
    tensorTotal Rc (sheafHomComplex Rc L M).obj K ⟶
      (sheafHomComplex Rc (sheafHomComplex Rc K L).obj M).obj
  /-- On every open set the map is the signed composite `ψ ↦ φ(ψ(k))`. -/
  evaluate_tmul : ∀ (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
      (U : Opens X) (t r s a p : ℤ) (hra : r + s = a) (hap : a + t = p)
      (φ : ((sheafHomComplex Rc L M).obj.X t).val.obj (op U))
      (k : (K.X r).val.obj (op U))
      (ψ : ((sheafHomComplex Rc K L).obj.X s).val.obj (op U)),
    applyHomSection Rc (sheafHomComplex Rc (sheafHomComplex Rc K L).obj M)
        U (t + r) s p (by omega)
        (((evaluate K L M).f (t + r)).val.app (op U)
          (tensorTotalSection Rc (sheafHomComplex Rc L M).obj K U t r φ k)) ψ =
      (r + (-a) * r).negOnePow •
        applyHomSection Rc (sheafHomComplex Rc L M) U t a p hap φ
          (applyHomSection Rc (sheafHomComplex Rc K L) U s r a hra ψ k)

/-- Morphisms of total tensor products compose as expected. -/
theorem tensorTotalMap_comp
    {A A' A'' B B' B'' : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    tensorTotalMap Rc f g ≫ tensorTotalMap Rc f' g' =
      tensorTotalMap Rc (f ≫ f') (g ≫ g') := by
  unfold tensorTotalMap
  rw [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp, HomologicalComplex.mapBifunctorMap,
    ← HomologicalComplex₂.total.map_comp]
  congr 1
  simp only [NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc]

/-- A morphism of total tensor products sends a local pure tensor to the local pure tensor of
the images. -/
theorem tensorTotalMap_section
    {A A' B B' : CochainComplex (StructureSheafModules Rc) ℤ} (f : A ⟶ A') (g : B ⟶ B')
    (U : Opens X) (t r : ℤ) (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotalMap Rc f g).f (t + r)).val.app (op U)
      (tensorTotalSection Rc A B U t r a b) =
    tensorTotalSection Rc A' B' U t r ((f.f t).val.app (op U) a)
      ((g.f r).val.app (op U) b) := by
  let F := (SheafOfModules.forget (structureSheaf Rc)).mapHomologicalComplex (ComplexShape.up ℤ)
  let T := curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)
  let h := HomologicalComplex.mapBifunctorMap (F.map f) (F.map g) T (ComplexShape.up ℤ)
  let i := HomologicalComplex.ιMapBifunctor (F.obj A) (F.obj B) T
    (ComplexShape.up ℤ) t r (t + r) rfl
  have hu := congrArg (fun z => (z.app (op U)).hom)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.naturality
      (h.f (t + r)))
  refine (DFunLike.congr_fun hu
    (i.app (op U) (a ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] b))).symm.trans ?_
  have hi := congrArg (fun z => (z.app (op U)).hom)
    (HomologicalComplex.ι_mapBifunctorMap (F.map f) (F.map g) T
      (ComplexShape.up ℤ) t r (t + r) rfl)
  exact congrArg (fun z =>
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
      (((F.obj A').mapBifunctor (F.obj B') T (ComplexShape.up ℤ)).X (t + r))).app (op U) z)
    (DFunLike.congr_fun hi (a ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] b))

/-- Evaluating the image of a Hom section under an induced map of internal Hom complexes is
evaluating the section itself, pre- and postcomposed with the two morphisms. -/
theorem applyHomSection_map
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ}
    (g : K' ⟶ K) (f : I' ⟶ I)
    (H : SheafHomComplex Rc K I') (H' : SheafHomComplex Rc K' I)
    (h : H.obj ⟶ H'.obj)
    (hh : SheafHomComplex.IsInducedMap Rc g f H H' h)
    (U : Opens X) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) (x : (K'.X p).val.obj (op U)) :
    applyHomSection Rc H' U n p q hpq ((h.f n).val.app (op U) s) x =
      (f.f q).val.app (op U) (applyHomSection Rc H U n p q hpq s
        ((g.f p).val.app (op U) x)) :=
  DFunLike.congr_fun
    (congrArg (fun z => (z.val.app (op (Over.mk (𝟙 U)))).hom) (hh U n p q hpq s)) x

end Stacks.SheafOfModules

end
