module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Deformation.ToposThickening.Basic

/-!
# Tensor products of sheaves of modules, read on sections

Let `O` be a sheaf of commutative rings on a site. The tensor product of two sheaves of
`O`-modules is the sheafification of the objectwise tensor product, so a morphism out of it is
determined by its values on the images of pure tensors, and may be built from a family of
bilinear pairings on sections compatible with restriction. This file collects the resulting
extensionality and lifting principles together with the left unit isomorphism, the maps induced
in either variable, and the comparison with restriction of scalars. Nothing here mentions a
thickening.

## Main definitions

* `Deformation.ToposThickening.tensorSheafLift`: the morphism out of a tensor product sheaf
  determined by a compatible family of bilinear pairings on sections.
* `Deformation.ToposThickening.tensorSheafUnitIso`: the left unit isomorphism `O ⊗ H ≅ H`.
* `Deformation.ToposThickening.tensorSheafMapRight`: the map on tensor products induced by a
  morphism of second factors.
* `Deformation.ToposThickening.tensorSheafRestrictMap`: the comparison of a tensor product with
  one formed after restriction of scalars.

## Main results

* `Deformation.ToposThickening.restrictScalars_exact`: restriction of scalars along a morphism
  of sheaves of rings preserves finite limits and finite colimits.
* `Deformation.ToposThickening.tensorSheaf_hom_ext` and
  `Deformation.ToposThickening.tensorSheaf_hom_ext_of_locallySurjective`: two morphisms out of a
  tensor product sheaf agree once they agree on pure tensors, and in the second variable it is
  enough to test on a locally surjective family of sections.
* `Deformation.ToposThickening.tensorSheafRestrictMap_epi`: the comparison map is an
  epimorphism as soon as the map of second factors is.

The Stacks tag 03EW part (4) — every sheaf of modules is a quotient of a flat one — is recorded
here against `Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat`, which proves it.

## Implementation notes

Local surjectivity of an epimorphism of sheaves of modules is
`Deformation.ToposThickening.sheafModule_epi_locallySurjective`, and full faithfulness of
restriction of scalars along a locally surjective morphism of sheaves of rings is
`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`; neither is restated
here.

`restrictScalars_exact` keeps the module universe independent of the universe of the sections of
the sheaves of rings. `Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars` is the
same statement with those two universes identified, an identification inherited from the
finite-limits half of its proof; the proof used here goes through faithfulness and exactness of
the underlying abelian sheaf functor instead, so it does not inherit that constraint.

Sections of a sheaf of modules over `O` are a module over the *ring* of sections of `O`, while
the pairings below are bilinear over the *commutative ring* of sections; the two scalar rings
differ by `forget₂ CommRingCat RingCat`, which no amount of unfolding available to instance
search sees through. `sectionsModuleOfCommRing` is the bridging instance, local to this file,
and the `attribute [local implicit_reducible]` block lists the definitions along the way from
one spelling of the scalars to the other, so that the rewrites below see a goal that is
type-correct at the transparency they use.

The subtype-valued form of `tensorSheafLift` and of `tensorSheafRestrictMap` carries the
characterizing formula on pure tensors alongside the morphism, which is what the extensionality
principles consume; the morphism alone does not determine the formula syntactically, since the
sheafification unit is not an epimorphism of presheaves.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
open AlgebraicGeometry.SheafOfModules (ringPresheaf)

universe v u w w'

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

namespace Deformation.ToposThickening

section Exactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits and
finite colimits: short exactness of a sequence of sheaves of modules is a property of the
underlying sequence of abelian sheaves, which it does not change. -/
lemma restrictScalars_exact {R S : Sheaf J RingCat.{w}} (α : R ⟶ S)
    [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify J AddCommGrpCat.{w'}] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{w'} α) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{w'} α) := by
  refine ((Functor.exact_tfae (SheafOfModules.restrictScalars.{w'} α)).out 1 4).mp fun T hT => ?_
  apply ShortExact.reflects_shortExact_of_faithful (SheafOfModules.toSheaf R)
  change (T.map (SheafOfModules.toSheaf S)).ShortExact
  exact hT.map_of_exact (SheafOfModules.toSheaf S)

/-- Two morphisms of sheaves of modules agree on a family of elements built from a bilinear
expression compatible with restriction, once they do so after replacing the second argument by
the image of a locally surjective family. -/
private theorem eq_of_locallySurjective_aux {R R' : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R} {S P : SheafOfModules.{w} R'}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (p : Q ⟶ N.val.presheaf) [Presheaf.IsLocallySurjective J p]
    (e : ∀ U : Cᵒᵖ, M.val.obj U → N.val.obj U → S.val.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U),
      S.val.map f (e U x y) = e V (M.val.map f x) (N.val.map f y))
    {f g : S ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : Q.obj U),
      f.val.app U (e U x (p.app U y)) = g.val.app U (e U x (p.app U y))) :
    ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (e U x y) = g.val.app U (e U x y) := by
  intro U x y
  apply P.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J p y)
  rintro V a ⟨z, hz⟩
  have key (k : S ⟶ P) :
      P.val.map a.op (k.val.app U (e U x y)) =
        k.val.app (Opposite.op V) (e _ (M.val.map a.op x) (N.val.map a.op y)) :=
    (PresheafOfModules.naturality_apply k.val a.op _).symm.trans
      (congrArg (k.val.app (Opposite.op V)) (he a.op x y))
  refine (key f).trans (Eq.trans ?_ (key g).symm)
  change p.app _ z = N.val.map a.op y at hz
  rw [← hz]
  exact h _ _ _

end Exactness

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sections of a sheaf of modules over the sheaf of rings underlying a sheaf of commutative
rings `O` form a module over the commutative ring of sections of `O`. -/
local instance sectionsModuleOfCommRing {O : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ) :
    Module (O.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

add_to_stacks 03EW "part (4): every sheaf of modules is a quotient of a flat one"
  Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat

/-- Two additive maps out of a tensor product agree once they agree on pure tensors. -/
private theorem tensor_hom_ext {F R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N]
    [FunLike F (M ⊗[R] N) P] [AddMonoidHomClass F (M ⊗[R] N) P] (f g : F)
    (h : ∀ (x : M) (y : N), f (x ⊗ₜ[R] y) = g (x ⊗ₜ[R] y)) : f = g := by
  refine DFunLike.ext _ _ fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms out of a tensor product sheaf agree as soon as they agree on the images of
pure tensors of sections. -/
lemma tensorSheaf_hom_ext (O : Sheaf J CommRingCat.{w})
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {f g : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U (x ⊗ₜ[O.obj.obj U] y)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U (x ⊗ₜ[O.obj.obj U] y))) :
    f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  exact ModuleCat.hom_ext (tensor_hom_ext (R := O.obj.obj U) _ _ (h U))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Restriction carries the image of a pure tensor to the image of the pure tensor of the
restrictions. -/
lemma tensorSheafificationUnit_naturality {O : Sheaf J CommRingCat.{w}}
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M).val.map f
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U (x ⊗ₜ[O.obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app V
        (M.val.map f x ⊗ₜ[O.obj.obj V] N.val.map f y) :=
  (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
    (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)) f
    (x ⊗ₜ[O.obj.obj U] y)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms out of a tensor product sheaf agree as soon as they agree on the images of
pure tensors whose second factor comes from a locally surjective family of sections. -/
lemma tensorSheaf_hom_ext_of_locallySurjective (O : Sheaf J CommRingCat.{w})
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (p : Q ⟶ N.val.presheaf)
    [Presheaf.IsLocallySurjective J p]
    {f g : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : Q.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
        (x ⊗ₜ[O.obj.obj U] p.app U y)) =
      g.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
        (x ⊗ₜ[O.obj.obj U] p.app U y))) :
    f = g := by
  apply tensorSheaf_hom_ext O
  intro U x y
  exact eq_of_locallySurjective_aux p _ (tensorSheafificationUnit_naturality M N) h U x y

/-- A family of bilinear pairings on sections compatible with restriction defines a morphism
out of the tensor product sheaf, characterized by its values on pure tensors. -/
noncomputable def tensorSheafLift (O : Sheaf J CommRingCat.{w})
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (b : ∀ U : Cᵒᵖ, M.val.obj U →ₗ[O.obj.obj U] N.val.obj U →ₗ[O.obj.obj U] P.val.obj U)
    (hb : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U),
      b V (M.val.map f x) (N.val.map f y) = P.val.map f (b U x y)) :
    { l : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M ⟶ P //
      ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        l.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
          (x ⊗ₜ[O.obj.obj U] y)) = b U x y } := by
  letI instP (U : Cᵒᵖ) : Module ((ringPresheaf O.obj).obj U) (P.val.obj U) :=
    (P.val.obj U).isModule
  let a := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  let b' : PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj P.val :=
    { app U := ModuleCat.ofHom (TensorProduct.lift (b U))
      naturality := by
        intro U V f
        refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
        change M.val.obj U ⊗[O.obj.obj U] N.val.obj U at t
        induction t using TensorProduct.inductionOn with
        | tmul x y => exact hb f x y
        | add x y hx hy =>
          exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm) }
  exact ⟨(a.homEquiv _ _).symm b', fun U x y =>
    congrArg (fun φ => φ.app U (x ⊗ₜ[O.obj.obj U] y)) ((a.homEquiv _ _).apply_symm_apply b')⟩

/-- The left unit isomorphism: tensoring a sheaf of modules with the structure sheaf gives it
back, by multiplication on sections. -/
noncomputable def tensorSheafUnitIso (O : Sheaf J CommRingCat.{w})
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅ H := by
  let A := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let μ := tensorSheafLift O (M := A) (N := H) (P := H)
    (fun U => LinearMap.lsmul (O.obj.obj U) (H.val.obj U))
    (fun f r x => (H.val.map_smul f r x).symm)
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
    (PresheafOfModules.tensorObj.{v, u, w, w, w} A.val H.val)
  let s : H ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).obj A :=
    { val :=
      { app U := ModuleCat.ofHom
          (Y := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).obj
            A).val.obj U)
          (id (((id (η.app U).hom : (A.val.obj U ⊗[O.obj.obj U] H.val.obj U) →ₗ[O.obj.obj U]
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
                H).obj A).val.obj U).comp
            (TensorProduct.mk (O.obj.obj U) (A.val.obj U) (H.val.obj U) (1 : O.obj.obj U))) :
              H.val.obj U →ₗ[O.obj.obj U]
                (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
                  H).obj A).val.obj U))
        naturality := by
          intro U V f
          ext x
          symm
          change (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
              H).obj A).val.map f
            (η.app U ((1 : O.obj.obj U) ⊗ₜ[O.obj.obj U] x)) =
              η.app V ((1 : O.obj.obj V) ⊗ₜ[O.obj.obj V] H.val.map f x)
          refine (tensorSheafificationUnit_naturality A H f (1 : O.obj.obj U) x).trans ?_
          change η.app V (O.obj.map f 1 ⊗ₜ[O.obj.obj V] H.val.map f x) = _
          rw [map_one] } }
  refine ⟨μ.1, s, ?_, ?_⟩
  · apply tensorSheaf_hom_ext O
    intro U r x
    change s.val.app U (μ.1.val.app U (η.app U (r ⊗ₜ[O.obj.obj U] x))) =
      η.app U (r ⊗ₜ[O.obj.obj U] x)
    refine (congrArg (fun t => s.val.app U t) (μ.2 U r x)).trans ?_
    change O.obj.obj U at r
    change η.app U ((1 : O.obj.obj U) ⊗ₜ[O.obj.obj U] (r • x)) = η.app U (r ⊗ₜ[O.obj.obj U] x)
    have key : ((1 : O.obj.obj U) ⊗ₜ[O.obj.obj U] (r • x) :
        O.obj.obj U ⊗[O.obj.obj U] H.val.obj U) = r ⊗ₜ[O.obj.obj U] x :=
      (TensorProduct.tmul_smul r (1 : O.obj.obj U) x).trans
        ((TensorProduct.smul_tmul' r (1 : O.obj.obj U) x).symm.trans
          (congrArg (fun t : O.obj.obj U => t ⊗ₜ[O.obj.obj U] x) (mul_one r)))
    exact congrArg (fun t => η.app U t) key
  · ext U x
    change μ.1.val.app U (η.app U ((1 : O.obj.obj U) ⊗ₜ[O.obj.obj U] x)) = x
    refine (μ.2 U (1 : O.obj.obj U) x).trans ?_
    change (1 : O.obj.obj U) • x = x
    exact one_smul _ _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The left unit isomorphism sends the image of a pure tensor to the product of its factors. -/
lemma tensorSheafUnitIso_hom_unit_tmul (O : Sheaf J CommRingCat.{w})
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (U : Cᵒᵖ) (r : O.obj.obj U) (x : H.val.obj U) :
    (tensorSheafUnitIso O H).hom.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w}
          ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).val
          H.val)).app U
        (r ⊗ₜ[O.obj.obj U] x)) = r • x :=
  (tensorSheafLift O (M := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (N := H) (P := H)
    (fun U => LinearMap.lsmul (O.obj.obj U) (H.val.obj U))
    (fun f r x => (H.val.map_smul f r x).symm)).2 U r x

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring a morphism on the right with a sheaf of modules acts on the image of a pure
tensor by applying the morphism to the first factor. -/
lemma tensorSheaf_map_unit_tmul (O : Sheaf J CommRingCat.{w})
    {M N H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : H.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).map f).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val H.val)).app U (x ⊗ₜ[O.obj.obj U] y)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} N.val H.val)).app U
          (f.val.app U x ⊗ₜ[O.obj.obj U] y) :=
  (congrArg (fun φ => φ.app U (x ⊗ₜ[O.obj.obj U] y))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality
        (PresheafOfModules.tensorHom f.val (𝟙 H.val)))).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms from a tensor product sheaf restricted along a morphism of sheaves of rings
agree as soon as they agree on the images of pure tensors of sections. -/
lemma tensorSheaf_restrict_hom_ext {R : Sheaf J RingCat.{w}} (O : Sheaf J CommRingCat.{w})
    (α : R ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {P : SheafOfModules.{w} R}
    {f g : (SheafOfModules.restrictScalars α).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U (x ⊗ₜ[O.obj.obj U] y)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U (x ⊗ₜ[O.obj.obj U] y))) :
    f = g := by
  apply (SheafOfModules.toSheaf R).map_injective
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  apply NatTrans.ext
  funext U
  exact AddCommGrpCat.hom_ext (tensor_hom_ext (R := O.obj.obj U) _ _ (h U))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms from a restricted tensor product sheaf agree as soon as they agree on the
images of pure tensors whose second factor comes from a locally surjective family. -/
lemma tensorSheaf_restrict_hom_ext_of_locallySurjective {R : Sheaf J RingCat.{w}}
    (O : Sheaf J CommRingCat.{w}) (α : R ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {P : SheafOfModules.{w} R}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (p : Q ⟶ N.val.presheaf)
    [Presheaf.IsLocallySurjective J p]
    {f g : (SheafOfModules.restrictScalars α).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : Q.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
        (x ⊗ₜ[O.obj.obj U] p.app U y)) =
      g.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
        (x ⊗ₜ[O.obj.obj U] p.app U y))) :
    f = g := by
  apply tensorSheaf_restrict_hom_ext O α
  intro U x y
  exact eq_of_locallySurjective_aux p _ (tensorSheafificationUnit_naturality M N)
    (S := (SheafOfModules.restrictScalars α).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N).obj M))
    (f := f) (g := g) h U x y

/-- The map on tensor product sheaves induced by a morphism of second factors. -/
noncomputable def tensorSheafMapRight (O : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {H H' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : H ⟶ H') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).obj M ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H').obj M :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map
    (PresheafOfModules.tensorHom (𝟙 M.val) f.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The map induced by a morphism of second factors acts on the image of a pure tensor by
applying that morphism to the second factor. -/
lemma tensorSheafMapRight_unit_tmul (O : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {H H' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : H ⟶ H')
    (U : Cᵒᵖ) (a : M.val.obj U) (x : H.val.obj U) :
    (tensorSheafMapRight O M f).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val H.val)).app U (a ⊗ₜ[O.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val H'.val)).app U
          (a ⊗ₜ[O.obj.obj U] f.val.app U x) :=
  (congrArg (fun φ => φ.app U (a ⊗ₜ[O.obj.obj U] x))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality
        (PresheafOfModules.tensorHom (𝟙 M.val) f.val))).symm

/-- Tensoring with a sheaf of modules mapping to a restriction of scalars compares with the
tensor product formed over the larger ring, through the given map on second factors. -/
noncomputable def tensorSheafRestrictMap (O O' : Sheaf J CommRingCat.{w})
    (α : Stacks.SheafOfModules.Tensor.ringSheaf O ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O')
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (p : H ⟶ (SheafOfModules.restrictScalars α).obj N) :
    { b : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj H).obj
          ((SheafOfModules.restrictScalars α).obj M) ⟶
        (SheafOfModules.restrictScalars α).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj N).obj M) //
      ∀ (U : Cᵒᵖ) (a : M.val.obj U) (x : H.val.obj U),
        b.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w}
            (((SheafOfModules.restrictScalars α).obj M)).val H.val)).app U
            (a ⊗ₜ[O.obj.obj U] x)) =
        ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O')
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
          (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)).app U
            (a ⊗ₜ[O'.obj.obj U] p.val.app U x) } := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O')
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
    (PresheafOfModules.tensorObj.{v, u, w, w, w} M.val N.val)
  apply tensorSheafLift O
    (M := (SheafOfModules.restrictScalars α).obj M) (N := H)
    (P := (SheafOfModules.restrictScalars α).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj N).obj M))
    (fun U =>
    { toFun a :=
        { toFun x := η.app U (a ⊗ₜ[O'.obj.obj U] p.val.app U x)
          map_add' x y :=
            (congrArg (fun z => η.app U (a ⊗ₜ[O'.obj.obj U] z))
                ((p.val.app U).hom.map_add x y)).trans
              ((congrArg (fun t => η.app U t)
                  (TensorProduct.tmul_add (R := O'.obj.obj U) (M := M.val.obj U)
                    (N := N.val.obj U) a (p.val.app U x) (p.val.app U y))).trans
                ((η.app U).hom.map_add _ _))
          map_smul' r x :=
            (congrArg (fun z => η.app U (a ⊗ₜ[O'.obj.obj U] z))
                ((p.val.app U).hom.map_smul r x)).trans
              ((congrArg (fun t => η.app U t)
                  (TensorProduct.tmul_smul (R := O'.obj.obj U) (R' := O'.obj.obj U)
                    (M := M.val.obj U) (N := N.val.obj U)
                    (α.hom.app U r) a (p.val.app U x))).trans
                ((η.app U).hom.map_smul (α.hom.app U r) _)) }
      map_add' a b := LinearMap.ext fun x =>
        (congrArg (fun t => η.app U t)
            (TensorProduct.add_tmul (R := O'.obj.obj U) (M := M.val.obj U)
              (N := N.val.obj U) a b (p.val.app U x))).trans
          ((η.app U).hom.map_add _ _)
      map_smul' r a := LinearMap.ext fun x =>
        (η.app U).hom.map_smul (α.hom.app U r)
          (@TensorProduct.tmul (O'.obj.obj U) _ (M.val.obj U) (N.val.obj U) _ _ _ _
            a (p.val.app U x)) })
  intro U V f a x
  change η.app V (M.val.map f a ⊗ₜ[O'.obj.obj V] p.val.app V (H.val.map f x)) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj N).obj M).val.map f
      (η.app U (a ⊗ₜ[O'.obj.obj U] p.val.app U x))
  rw [tensorSheafificationUnit_naturality]
  exact congrArg (fun y => η.app V (M.val.map f a ⊗ₜ[O'.obj.obj V] y))
    (PresheafOfModules.naturality_apply p.val f x)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison map of `tensorSheafRestrictMap` is an epimorphism when the map of second
factors is. -/
lemma tensorSheafRestrictMap_epi (O O' : Sheaf J CommRingCat.{w})
    [HasSheafify J AddCommGrpCat.{w}]
    (α : Stacks.SheafOfModules.Tensor.ringSheaf O ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O')
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (p : H ⟶ (SheafOfModules.restrictScalars α).obj N) [Epi p] :
    Epi (tensorSheafRestrictMap O O' α M N p).1 := by
  let p' : H.val.presheaf ⟶ N.val.presheaf :=
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map p.val
  have : Presheaf.IsLocallySurjective J p' := sheafModule_epi_locallySurjective p
  refine ⟨fun {P} f g h => ?_⟩
  apply tensorSheaf_restrict_hom_ext_of_locallySurjective O' α p'
  intro U a x
  have hh := congrArg (fun k => k.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj.{v, u, w, w, w} ((SheafOfModules.restrictScalars α).obj M).val
        H.val)).app U (a ⊗ₜ[O.obj.obj U] x))) h
  change f.val.app U ((tensorSheafRestrictMap O O' α M N p).1.val.app U _) =
    g.val.app U ((tensorSheafRestrictMap O O' α M N p).1.val.app U _) at hh
  exact (congrArg (fun z => f.val.app U z)
      ((tensorSheafRestrictMap O O' α M N p).2 U a x)).symm.trans
    (hh.trans (congrArg (fun z => g.val.app U z)
      ((tensorSheafRestrictMap O O' α M N p).2 U a x)))

end Tensor

end Deformation.ToposThickening

end
