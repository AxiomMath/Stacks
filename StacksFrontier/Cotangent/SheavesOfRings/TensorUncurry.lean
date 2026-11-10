module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProdLocallyBijective
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahDifferentialsLowerShriek

/-!
# Uncurrying commutes with tensoring by an inverse-image module

Let `C` be a small site, let `ℬ` be a sheaf of commutative rings on it, let `ℱ` be a sheaf of
`ℬ`-modules and let `G_•` be a simplicial sheaf of `ℬ`-modules. Read on the simplicial site
`Δ × C` of [Stacks, Tag 09D0], the uncurrying `uncurryMod(G_•)` is a sheaf of `π^{-1}ℬ`-modules,
and this file proves

`π^{-1}ℱ ⊗_{π^{-1}ℬ} uncurryMod(G_•) ≅ uncurryMod(G_• ⊗_ℬ ℱ)`.

Both sides are sheafifications, the left one on `Δ × C` and the right one levelwise on `C`, so
this is a statement about sheafification on `Δ × C` and not a formal consequence of the
equivalence `Stacks.SimplicialModules.simplicialModuleEquivalence`.

## Main definitions

* `Stacks.SimplicialModules.TensorUncurry.tensorUncurryBilinear` and
  `Stacks.SimplicialModules.TensorUncurry.tensorUncurryHom`: **the comparison**, written once on
  `Δ × C` as the transpose of the levelwise sheafification unit.
* `Stacks.SimplicialModules.TensorUncurry.tensorSwapHom`: the symmetry of the objectwise tensor
  product of presheaves of modules, which is what makes the two orders of the factors
  interchangeable.

## Main results

* `Stacks.SimplicialModules.TensorUncurry.isLocallySurjective_level` and
  `isLocallyInjective_level`: the comparison is locally bijective in each simplicial degree,
  where it *is* the levelwise sheafification unit after the swap.
* `Stacks.SimplicialModules.TensorUncurry.tensorUncurryIso`: **the isomorphism.**

## How it is proved, and what it does not need

The comparison is not assembled degreewise. It is written once on `Δ × C`: its sections over
`(n, U)` are the sheafification unit of `G_n ⊗ ℱ` over `U`, precomposed with the swap of the two
tensor factors, and its compatibility with the restriction maps of `Δ × C` is the naturality of
that unit in both the presheaf (for the simplicial direction) and the site object (for the
other). Since a bilinear map of presheaves of modules is exactly a morphism out of the objectwise
tensor product (`Stacks.tensorHomEquiv`), the comparison is produced by giving the bilinear map
and transposing; nothing has to be checked about the module structures on the sheafified tensor
product.

It is then inverted by local bijectivity. On the fibre `{n} × C` the comparison is the levelwise
sheafification unit, which is locally bijective because sheafification inverts exactly the
locally bijective maps; and local bijectivity on `Δ × C` for the topology inherited along the
second projection is the levelwise condition
(`CategoryTheory.Presheaf.isLocallySurjective_inheritedTopology_prodSnd` and
`isLocallyInjective_inheritedTopology_prodSnd`). Finally
`Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective` turns a locally bijective
comparison into a sheaf into the identification of the sheafification with that sheaf.

**In particular `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` is not
needed, and neither is any naturality of it in the functor of sites.** The degreewise comparisons
of `Stacks.Sheaves.Differentials.restrictedSheafTensorRightIso` rest on that isomorphism, and
assembling them would need it natural in the functor of sites; the route above never restricts to
a fibre at all except to check a condition that is pointwise in the degree.

## Implementation notes

The three sheaves in play carry two spellings of one sheaf of rings — `π^{-1}ℬ` on `Δ × C` and
`ℬ` on `C` — which agree on sections over `(n, U)` but are not syntactically equal, so instance
search does not transport the module structures between them. `moduleOfTensorRingSections` records
the action in the spelling the objectwise tensor product uses, in the manner of
`CategoryTheory.Sheaf.moduleOfSections`, and `uncurryTensorLevelCoeff` and
`uncurryTensorLevelSection` read a section over `(n, U)` as a section over `U` of the degree-`n`
term. Without them the pure tensors below do not elaborate.

Each of the two restriction lemmas `uncurrySource_map_prodSnd` and `uncurryTarget_map_prodSnd`
undoes one factor `G(𝟙_n)` that the uncurried presheaf inserts, which is the identity by
`CategoryTheory.Functor.map_id`; that is the only place the difference between the fibrewise
reading of an uncurrying and the original simplicial object has to be addressed.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0), the simplicial site and
  its topology.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), a simplicial module as a
  sheaf of modules on `Δ × C`.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA), the tensor product of
  sheaves of modules as a sheafification.
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), whose first-term
  identification this serves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.SimplicialModules (projection projectionTopology projectionRing projectionCommRing
  uncurryMod uncurryModPresheaf_map_apply)

universe u

namespace Stacks.SimplicialModules.TensorUncurry

open CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {B : Sheaf J CommRingCat.{u}}
  (F : SheafOfModules.{u} (targetRing J (B := B)))
  (G : SimplicialObject (SheafOfModules.{u} (targetRing J (B := B))))

/-- the levelwise sheafification unit -/
abbrev tensorLevelUnit (n : SimplexCategoryᵒᵖ) :=
  (PresheafOfModules.sheafificationAdjunction (R := targetRing J (B := B)) (𝟙 _)).unit.app
    (Stacks.tensorObj (G.obj n).val F.val)

/-- the levelwise tensor product, read on `Δ × C` -/
abbrev tensorUncurry :=
  (uncurryMod C J (targetRing J (B := B))).obj
    (G ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F)

/-- the second tensor factor, in the shape the transitivity isomorphism produces -/
abbrev uncurrySource :=
  (PresheafOfModules.restrictScalars
      (𝟙 (projectionRing C J (targetRing J (B := B))).obj)).obj
    ((SheafOfModules.forget _).obj ((uncurryMod C J (targetRing J (B := B))).obj G))

/-- the target of the comparison -/
abbrev uncurryTarget :=
  (PresheafOfModules.restrictScalars
      (𝟙 (projectionRing C J (targetRing J (B := B))).obj)).obj
    ((SheafOfModules.forget _).obj (tensorUncurry J F G))

/-- The sections of `ℬ` act on the sections of a sheaf of `ℬ`-modules in the ring spelling the
objectwise tensor product of presheaves of modules uses. -/
@[instance_reducible]
def moduleOfTensorRingSections (M : SheafOfModules.{u} (targetRing J (B := B))) (U : Cᵒᵖ) :
    Module ((Stacks.ringPresheaf B.obj).obj U)
      (M.val.obj U) :=
  inferInstanceAs (Module ((targetRing J (B := B)).obj.obj U) (M.val.obj U))

attribute [local instance] moduleOfTensorRingSections

/-- The sections of `π^{-1}ℱ` over `(n, U)` are the sections of `ℱ` over `U`. -/
abbrev uncurryTensorLevelCoeff (X : (SimplexCategory × C)ᵒᵖ)
    (x : (projectionCoefficients J (B := B) F).val.obj X) :
    F.val.obj (op X.unop.2) := x

/-- The sections of the uncurrying over `(n, U)` are the sections of `G_n` over `U`. -/
abbrev uncurryTensorLevelSection (X : (SimplexCategory × C)ᵒᵖ) (y : (uncurrySource J G).obj X) :
    (G.obj (op X.unop.1)).val.obj (op X.unop.2) := y

omit [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The levelwise sheafification unit is natural in the simplicial module: for `φ : G_m ⟶ G_n`,
applying `φ ⊗ ℱ` after the unit of `G_m ⊗ ℱ` equals the unit of `G_n ⊗ ℱ` after `φ ⊗ ℱ`. -/
theorem tensorLevelUnit_naturality_presheaf {m n : SimplexCategoryᵒᵖ} (φ : G.obj m ⟶ G.obj n)
    (V : Cᵒᵖ) (z : (Stacks.tensorObj (G.obj m).val F.val).obj V) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F).map φ)).val.app V
        ((tensorLevelUnit J F G m).app V z) =
      (tensorLevelUnit J F G n).app V (((Stacks.tensorRight F.val).map φ.val).app V z) :=
  (congrArg (fun k : Stacks.tensorObj (G.obj m).val F.val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (targetRing J (B := B)).obj)).obj
        ((SheafOfModules.forget _).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F).obj (G.obj n))) =>
    ConcreteCategory.hom (k.app V) z)
    ((PresheafOfModules.sheafificationAdjunction (R := targetRing J (B := B))
      (𝟙 _)).unit.naturality ((Stacks.tensorRight F.val).map φ.val))).symm

/-- **The comparison**: swap the two tensor factors, then the levelwise sheafification unit. -/
def tensorUncurryBilinear :
    Stacks.BilinearMap (R := Stacks.ringPresheaf ((projectionCommRing J B)).obj)
        (projectionCoefficients J (B := B) F).val (uncurrySource J G)
      (uncurryTarget J F G) where
  app X := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => (tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)
        (uncurryTensorLevelSection J G X y ⊗ₜ uncurryTensorLevelCoeff J F X x))
      (fun y y' =>
        (congrArg (fun z : (Stacks.tensorObj (G.obj (op X.unop.1)).val F.val).obj (op X.unop.2) =>
            ConcreteCategory.hom
              ((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)) z)
          (TensorProduct.add_tmul (uncurryTensorLevelSection J G X y)
            (uncurryTensorLevelSection J G X y') (uncurryTensorLevelCoeff J F X x))).trans
          (((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)).hom.map_add _ _)))
    (fun x x' => AddMonoidHom.ext fun y =>
      (congrArg (fun z : (Stacks.tensorObj (G.obj (op X.unop.1)).val F.val).obj (op X.unop.2) =>
          ConcreteCategory.hom
            ((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)) z)
        (TensorProduct.tmul_add (uncurryTensorLevelSection J G X y)
          (uncurryTensorLevelCoeff J F X x) (uncurryTensorLevelCoeff J F X x'))).trans
        (((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)).hom.map_add _ _))
  map_smul_left X r x y :=
    letI r' : ((Stacks.ringPresheaf B.obj).obj
      (op X.unop.2)) := r
    (congrArg (fun z : (Stacks.tensorObj (G.obj (op X.unop.1)).val F.val).obj (op X.unop.2) =>
        ConcreteCategory.hom
          ((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)) z)
      (TensorProduct.tmul_smul (R := ((Stacks.ringPresheaf B.obj).obj (op X.unop.2))) r'
        (uncurryTensorLevelSection J G X y) (uncurryTensorLevelCoeff J F X x))).trans
      (((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)).hom.map_smul r
        (uncurryTensorLevelSection J G X y ⊗ₜ uncurryTensorLevelCoeff J F X x))
  map_smul_right X r x y :=
    letI r' : ((Stacks.ringPresheaf B.obj).obj
      (op X.unop.2)) := r
    (congrArg (fun z : (Stacks.tensorObj (G.obj (op X.unop.1)).val F.val).obj (op X.unop.2) =>
        ConcreteCategory.hom
          ((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)) z)
      (TensorProduct.smul_tmul' (R := ((Stacks.ringPresheaf B.obj).obj (op X.unop.2))) r'
        (uncurryTensorLevelSection J G X y) (uncurryTensorLevelCoeff J F X x))).trans
      (((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)).hom.map_smul r
        (uncurryTensorLevelSection J G X y ⊗ₜ uncurryTensorLevelCoeff J F X x))
  naturality {X Y} g x y := by
    refine Eq.trans (uncurryModPresheaf_map_apply C J (targetRing J (B := B))
      (G ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F) g _) ?_
    refine Eq.trans (congrArg (fun z => ConcreteCategory.hom
        ((((G ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F).obj
          (op Y.unop.1))).val.map (g.unop.2).op) z)
      (tensorLevelUnit_naturality_presheaf J F G (G.map (g.unop.1).op) (op X.unop.2)
        (y ⊗ₜ x))) ?_
    refine Eq.trans (PresheafOfModules.naturality_apply
      (tensorLevelUnit J F G (op Y.unop.1)) (g.unop.2).op _).symm ?_
    exact congrArg (fun w => ConcreteCategory.hom
        ((tensorLevelUnit J F G (op Y.unop.1)).app (op Y.unop.2))
        (w ⊗ₜ (F.val.map (g.unop.2).op x)))
      (uncurryModPresheaf_map_apply C J (targetRing J (B := B)) G g y).symm

/-- The symmetry of the objectwise tensor product of presheaves of modules. -/
def tensorSwapHom {D : Type u} [SmallCategory D] {O : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (Stacks.ringPresheaf O)) :
    Stacks.tensorObj M N ⟶ Stacks.tensorObj N M :=
  Stacks.tensorHomEquiv.symm (Stacks.tensorHomEquiv (𝟙 (Stacks.tensorObj N M))).flip

/-- The symmetry of the objectwise tensor product is an involution. -/
theorem tensorSwapHom_comp {D : Type u} [SmallCategory D] {O : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (Stacks.ringPresheaf O)) :
    tensorSwapHom M N ≫ tensorSwapHom N M = 𝟙 _ := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (TensorProduct.ext ?_)
  ext x y
  rfl

/-- Applying the symmetry of the objectwise tensor product twice to a section returns it. -/
theorem tensorSwapHom_app_swap {D : Type u} [SmallCategory D] {O : Dᵒᵖ ⥤ CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (Stacks.ringPresheaf O)) (X : Dᵒᵖ)
    (w : (Stacks.tensorObj M N).obj X) :
    (tensorSwapHom N M).app X ((tensorSwapHom M N).app X w) = w :=
  congrArg (fun k : Stacks.tensorObj M N ⟶ Stacks.tensorObj M N =>
    ConcreteCategory.hom (k.app X) w) (tensorSwapHom_comp M N)

/-- **The comparison morphism on `Δ × C`**, the transpose of the levelwise sheafification
unit. -/
def tensorUncurryHom :
    Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
        (projectionCoefficients J (B := B) F).val (uncurrySource J G) ⟶
      uncurryTarget J F G :=
  Stacks.BilinearMap.toTensorHom (tensorUncurryBilinear J F G)

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The comparison is the levelwise sheafification unit, after the swap. -/
theorem tensorUncurryHom_app (X : (SimplexCategory × C)ᵒᵖ)
    (w : (Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
      (projectionCoefficients J (B := B) F).val (uncurrySource J G)).obj X) :
    (tensorUncurryHom J F G).app X w =
      (tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)
        ((tensorSwapHom (O := ((projectionCommRing J B)).obj)
          (projectionCoefficients J (B := B) F).val
          (uncurrySource J G)).app X w) := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add w w' hw hw' =>
    exact (((tensorUncurryHom J F G).app X).hom.map_add w w').trans
      (((congrArg₂ (· + ·) hw hw').trans
        (((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)).hom.map_add _ _).symm).trans
        (congrArg (fun z => ConcreteCategory.hom
            ((tensorLevelUnit J F G (op X.unop.1)).app (op X.unop.2)) z)
          (((tensorSwapHom (O := ((projectionCommRing J B)).obj)
            (projectionCoefficients J (B := B) F).val
            (uncurrySource J G)).app X).hom.map_add w w').symm))

/-- The restriction of an uncurrying along `(𝟙, ψ)` is its restriction inside the degree: the
uncurried presheaf inserts the factor `H(𝟙_n)`, which is the identity. -/
private theorem uncurry_map_prodSnd {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {B : Sheaf J CommRingCat.{u}}
    (H : SimplicialObject (SheafOfModules.{u} (targetRing J (B := B)))) (n : SimplexCategory)
    {U V : C} (ψ : V ⟶ U)
    (y : ((PresheafOfModules.restrictScalars
      (𝟙 (projectionRing C J (targetRing J (B := B))).obj)).obj
        ((SheafOfModules.forget _).obj ((uncurryMod C J (targetRing J (B := B))).obj H))).obj
          (op (n, U))) :
    ((PresheafOfModules.restrictScalars
      (𝟙 (projectionRing C J (targetRing J (B := B))).obj)).obj
        ((SheafOfModules.forget _).obj ((uncurryMod C J (targetRing J (B := B))).obj H))).map
          ((Functor.prodSectionSnd (C := C) n).map ψ).op y =
      (H.obj (op n)).val.map ψ.op y := by
  refine Eq.trans (uncurryModPresheaf_map_apply C J (targetRing J (B := B)) H
    ((Functor.prodSectionSnd (C := C) n).map ψ).op y) ?_
  change (H.obj (op n)).val.map ψ.op ((H.map (𝟙 (op n))).val.app (op U) y) = _
  rw [H.map_id]
  rfl

omit [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The restriction of the uncurrying along `(𝟙, ψ)` is its restriction inside the degree: the
uncurried presheaf inserts the factor `G(𝟙_n)`, which is the identity. -/
theorem uncurrySource_map_prodSnd (n : SimplexCategory) {U V : C} (ψ : V ⟶ U)
    (y : (uncurrySource J G).obj (op (n, U))) :
    (uncurrySource J G).map ((Functor.prodSectionSnd (C := C) n).map ψ).op y =
      (G.obj (op n)).val.map ψ.op y :=
  uncurry_map_prodSnd J G n ψ y

omit [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The same for the levelwise tensor product with `ℱ`. -/
theorem uncurryTarget_map_prodSnd (n : SimplexCategory) {U V : C} (ψ : V ⟶ U)
    (s : (uncurryTarget J F G).obj (op (n, U))) :
    (uncurryTarget J F G).map ((Functor.prodSectionSnd (C := C) n).map ψ).op s =
      ((G ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F).obj
        (op n)).val.map ψ.op s :=
  uncurry_map_prodSnd J (G ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor B).flip.obj F) n ψ s

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The restriction of the swapped source along `(𝟙, ψ)` is the levelwise restriction. -/
theorem tensorLevel_map_prodSnd (n : SimplexCategory) {U V : C} (ψ : V ⟶ U)
    (z : (Stacks.tensorObj (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
      (projectionCoefficients J (B := B) F).val).obj (op (n, U))) :
    (Stacks.tensorObj (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
          (projectionCoefficients J (B := B) F).val).map
        ((Functor.prodSectionSnd (C := C) n).map ψ).op z =
      (Stacks.tensorObj (G.obj (op n)).val F.val).map ψ.op z := by
  induction z using TensorProduct.inductionOn with
  | tmul y x =>
    exact congrArg (fun w => (show (Stacks.tensorObj (G.obj (op n)).val F.val).obj (op V) from
        w ⊗ₜ uncurryTensorLevelCoeff J F (op (n, V)) ((projectionCoefficients J (B := B) F).val.map
          ((Functor.prodSectionSnd (C := C) n).map ψ).op x)))
      (uncurrySource_map_prodSnd J G n ψ y)
  | add z z' hz hz' =>
    exact ((((Stacks.tensorObj (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
        (projectionCoefficients J (B := B) F).val).map
          ((Functor.prodSectionSnd (C := C) n).map ψ).op)).hom.map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans
        (((Stacks.tensorObj (G.obj (op n)).val F.val).map ψ.op).hom.map_add z z').symm)

/-! ### Local bijectivity -/

/-- The levelwise sheafification unit is locally surjective. -/
instance isLocallySurjective_tensorLevelUnit (n : SimplexCategoryᵒᵖ) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (tensorLevelUnit J F G n)) :=
  (J.W_toSheafify (Stacks.tensorObj (G.obj n).val F.val).presheaf).isLocallySurjective

/-- The levelwise sheafification unit is locally injective. -/
instance isLocallyInjective_tensorLevelUnit (n : SimplexCategoryᵒᵖ) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (tensorLevelUnit J F G n)) :=
  (J.W_toSheafify (Stacks.tensorObj (G.obj n).val F.val).presheaf).isLocallyInjective

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The restriction of `tensorUncurryHom` to the fibre `{n} × C` is locally surjective. -/
theorem isLocallySurjective_level (n : SimplexCategory) :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) n).op
        ((PresheafOfModules.toPresheaf _).map (tensorUncurryHom J F G))) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
      ((PresheafOfModules.toPresheaf _).map (tensorLevelUnit J F G (op n))) s)
    intro V g hg
    obtain ⟨z, hz⟩ := hg
    refine ⟨(tensorSwapHom (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
      (projectionCoefficients J (B := B) F).val).app (op (n, V)) z, ?_⟩
    refine (tensorUncurryHom_app J F G (op (n, V)) _).trans ?_
    refine Eq.trans (congrArg (fun w => ConcreteCategory.hom
        ((tensorLevelUnit J F G (op n)).app (op V)) w)
      (tensorSwapHom_app_swap (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
        (projectionCoefficients J (B := B) F).val (op (n, V)) z)) ?_
    exact hz.trans (uncurryTarget_map_prodSnd J F G n g s).symm

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The restriction of `tensorUncurryHom` to the fibre `{n} × C` is locally injective. -/
theorem isLocallyInjective_level (n : SimplexCategory) :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) n).op
        ((PresheafOfModules.toPresheaf _).map (tensorUncurryHom J F G))) where
  equalizerSieve_mem {U} x y hxy := by
    have h : ConcreteCategory.hom ((tensorLevelUnit J F G (op n)).app U)
          ((tensorSwapHom (O := ((projectionCommRing J B)).obj)
            (projectionCoefficients J (B := B) F).val (uncurrySource J G)).app
              (op (n, U.unop)) x) =
        ConcreteCategory.hom ((tensorLevelUnit J F G (op n)).app U)
          ((tensorSwapHom (O := ((projectionCommRing J B)).obj)
            (projectionCoefficients J (B := B) F).val (uncurrySource J G)).app
              (op (n, U.unop)) y) :=
      (tensorUncurryHom_app J F G (op (n, U.unop)) x).symm.trans
        (hxy.trans (tensorUncurryHom_app J F G (op (n, U.unop)) y))
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
      ((PresheafOfModules.toPresheaf _).map (tensorLevelUnit J F G (op n))) _ _ h)
    intro V g hg
    have key : ∀ w : (Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
          (projectionCoefficients J (B := B) F).val (uncurrySource J G)).obj (op (n, U.unop)),
        (Stacks.tensorObj (G.obj (op n)).val F.val).map g.op
            ((tensorSwapHom (O := ((projectionCommRing J B)).obj)
              (projectionCoefficients J (B := B) F).val (uncurrySource J G)).app
                (op (n, U.unop)) w) =
          (tensorSwapHom (O := ((projectionCommRing J B)).obj)
            (projectionCoefficients J (B := B) F).val (uncurrySource J G)).app (op (n, V))
            ((Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
              (projectionCoefficients J (B := B) F).val (uncurrySource J G)).map
                ((Functor.prodSectionSnd (C := C) n).map g).op w) := by
      intro w
      exact (tensorLevel_map_prodSnd J F G n g _).symm.trans
        (PresheafOfModules.naturality_apply
          (tensorSwapHom (O := ((projectionCommRing J B)).obj)
            (projectionCoefficients J (B := B) F).val (uncurrySource J G))
          ((Functor.prodSectionSnd (C := C) n).map g).op w).symm
    have h2 := ((key x).symm.trans hg).trans (key y)
    exact (tensorSwapHom_app_swap (O := ((projectionCommRing J B)).obj)
        (projectionCoefficients J (B := B) F).val (uncurrySource J G) (op (n, V)) _).symm.trans
      ((congrArg (fun w => ConcreteCategory.hom
          ((tensorSwapHom (O := ((projectionCommRing J B)).obj) (uncurrySource J G)
            (projectionCoefficients J (B := B) F).val).app (op (n, V))) w) h2).trans
        (tensorSwapHom_app_swap (O := ((projectionCommRing J B)).obj)
          (projectionCoefficients J (B := B) F).val (uncurrySource J G) (op (n, V)) _))

/-! ### The isomorphism -/

/-- The comparison `tensorUncurryHom` is locally surjective on `Δ × C`. -/
instance isLocallySurjective_tensorUncurryHom :
    PresheafOfModules.IsLocallySurjective (projectionTopology C J) (tensorUncurryHom J F G) :=
  Presheaf.isLocallySurjective_inheritedTopology_prodSnd J _ (isLocallySurjective_level J F G)

/-- The comparison `tensorUncurryHom` is locally injective on `Δ × C`. -/
instance isLocallyInjective_tensorUncurryHom :
    PresheafOfModules.IsLocallyInjective (projectionTopology C J) (tensorUncurryHom J F G) :=
  Presheaf.isLocallyInjective_inheritedTopology_prodSnd J _ (isLocallyInjective_level J F G)

/-- **Uncurrying commutes with tensoring by an inverse-image module.** -/
def tensorUncurryIso :
    (PresheafOfModules.sheafification
          (R := projectionRing C J (targetRing J (B := B))) (𝟙 _)).obj
        (Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
          (projectionCoefficients J (B := B) F).val (uncurrySource J G)) ≅
      tensorUncurry J F G :=
  Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective
    (𝟙 (projectionRing C J (targetRing J (B := B))).obj) (tensorUncurry J F G)
    (tensorUncurryHom J F G) (isLocallyInjective_tensorUncurryHom J F G)
    (isLocallySurjective_tensorUncurryHom J F G)


end Stacks.SimplicialModules.TensorUncurry

end
