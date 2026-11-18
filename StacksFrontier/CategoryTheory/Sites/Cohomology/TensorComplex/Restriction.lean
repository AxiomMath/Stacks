module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.MorphismsOutOfASheafifiedPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Restriction to a slice commutes with the tensor product of sheaves of modules

Let `(C, O)` be a ringed site and let `U` be an object of `C`. The tensor product `A ⊗_O B` of
two sheaves of `O`-modules is the sheafification of the objectwise tensor product of the
underlying presheaves, so its restriction to the site over `U` and the tensor product
`A|_U ⊗_{O|_U} B|_U` formed there are two sheafifications of one and the same presheaf: the
objectwise tensor product commutes with restriction on the nose, both sides being computed
over each object of the site over `U` from the same sections. This file identifies them, and
records the naturality of that identification in each variable, which is what a comparison of
the two total tensor complexes of a pair of complexes of `O`-modules is assembled from
degreewise.

The identification is an instance of a general principle: two sheaves of modules receiving
locally bijective morphisms from isomorphic presheaves of modules are canonically isomorphic,
and the isomorphism is the one determined by the comparison of the presheaves. The first part
of the file sets that out, together with the characterisation of the resulting morphism by the
equation it satisfies on the presheaf level, from which its naturality follows.

## Main definitions

* `AlgebraicGeometry.RingedSite.homEquivOfUnit`: morphisms of sheaves of modules out of the
  target of a locally bijective morphism from a presheaf of modules are morphisms out of that
  presheaf.
* `AlgebraicGeometry.RingedSite.liftOfUnit`: the morphism of sheaves of modules determined by a
  presheaf-level morphism.
* `AlgebraicGeometry.RingedSite.isoOfUnits`: the isomorphism between two sheaves of modules
  receiving locally bijective morphisms from isomorphic presheaves of modules.
* `AlgebraicGeometry.RingedSite.overSheafificationUnit`: the restriction to the site over `U`
  of the unit of the sealed sheafification `Stacks.SheafOfModules.Tensor.sheafification`.
* `AlgebraicGeometry.RingedSite.globalTensorPresheaf` and
  `AlgebraicGeometry.RingedSite.overTensorPresheaf`: the objectwise tensor product of the
  underlying presheaves of two sheaves of `O`-modules, and the one formed on the site over `U`
  from their restrictions.
* `AlgebraicGeometry.RingedSite.overTensorUnit`: the unit of the sealed sheafification on the
  site over `U`, out of `overTensorPresheaf`.
* `AlgebraicGeometry.RingedSite.overPresheafTensorIso`: restriction commutes with the
  objectwise tensor product of presheaves of modules.
* `AlgebraicGeometry.RingedSite.sheafTensorOverIso`: **restriction commutes with the tensor
  product of sheaves of modules**, the restriction of `A ⊗_O B` to the site over `U` being
  `A|_U ⊗_{O|_U} B|_U`.
* `AlgebraicGeometry.RingedSite.sheafTensorBicomplex` and
  `AlgebraicGeometry.RingedSite.overSheafTensorBicomplex`: the double complex of sheaf tensor
  products of the terms of two complexes of `O`-modules, and the one formed over `U` from their
  restrictions.
* `AlgebraicGeometry.RingedSite.overSheafTensorBicomplexIso`: the two double complexes are
  identified degreewise by `sheafTensorOverIso`.
* `AlgebraicGeometry.RingedSite.tensorComplexOverIso`: **restriction commutes with the total
  tensor complex**, the restriction of `Tot(A ⊗_O B)` to the site over `U` being
  `Tot(A|_U ⊗_{O|_U} B|_U)`.

## Main results

* `AlgebraicGeometry.RingedSite.comp_liftOfUnit` and
  `AlgebraicGeometry.RingedSite.hom_ext_of_unit`: the defining equation of `liftOfUnit` and the
  extensionality principle it comes with.
* `AlgebraicGeometry.RingedSite.isoOfUnits_naturality`: `isoOfUnits` carries a morphism induced
  by a morphism of the presheaves to the morphism induced by its counterpart, as soon as the
  two comparisons of presheaves agree on it.
* `AlgebraicGeometry.RingedSite.overSheafificationUnit_naturality` and
  `AlgebraicGeometry.RingedSite.overTensorUnit_naturality`: the two sheafification units
  entering `sheafTensorOverIso` are natural.
* `AlgebraicGeometry.RingedSite.sheafTensorOverIso_naturality_left` and
  `AlgebraicGeometry.RingedSite.sheafTensorOverIso_naturality_right`: `sheafTensorOverIso` is
  natural in each variable separately.

## Implementation notes

The tensor product used throughout is `Stacks.SheafOfModules.Tensor.sheafTensor`, the one of
Stacks 06YM entering the derived tensor product, and the restriction of a sheaf of modules to a
slice is Mathlib's `SheafOfModules.overFunctor`; no second notion of either is introduced. The
units entering the comparison are those of the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification` in terms of which `sheafTensor` is defined, taken
with the plain forgetful functor as right adjoint. The restriction of such a unit to the site
over `U` is still locally bijective, because the forgetful functor of the site over `U` is
cocontinuous, exactly as for Mathlib's unit in `AlgebraicGeometry.RingedSite.overSheafifyHomEquiv`.

Comparing the two sheaves directly — by unfolding the restriction of a tensor product into the
tensor product of restrictions as whole structures — is expensive, because the restriction maps
of the two sides are reached by different routes. Nothing of the kind is done here: the
comparison is made on the underlying presheaves, where over each object of the site over `U`
both sides are literally the same tensor product of sections, and `isoOfUnits` transports it.

The restricted sheaf of rings has two spellings, the one produced by
`Stacks.SheafOfModules.Tensor.ringSheaf` from the restricted structure sheaf,
`Tensor.ringSheaf (X.O.over U)`, and the one produced by restricting the sheaf of rings of
`X`, `(Tensor.ringSheaf X.O).over U`. They are the same term, but
only after unfolding definitions that instance search does not unfold, so a statement reaching
for the slice machinery at the first spelling finds no instances. One spelling is therefore
fixed once, by the ascribed type of `overTensorPresheaf`. In the same way the objectwise tensor
product of `X` is built over `X.O.obj ⋙ forget₂ CommRingCat RingCat`, which is
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj` only after unfolding, and
`globalTensorPresheaf` ascribes it the second spelling, at which the restricted unit and its
instances are stated. `sheafTensorOverIso` names the sealed sheafification of that presheaf in
an intermediate step and lets the definition of `sheafTensor`, whose last step is that sealed
sheafification, carry it to the tensor product. No weakening of the unifier is needed anywhere.

The passage from the degreewise identification to the total complexes is
`HomologicalComplex₂.TotalMap.totalIso`, which says that an additive functor preserving the
relevant coproducts commutes with the total complex of a bicomplex, with no finiteness
hypothesis. Restriction to a slice preserves those coproducts, which is not formal: it is a
right adjoint, and is known to be a left adjoint only over a site with pullbacks. The fact used
is `Stacks.SheafOfModules.pushforward_preservesColimits`, shrunk to the universe of the
bidegrees. The two double complexes themselves are not definitionally equal, so the total
complex of the restricted one is available only after transporting the existence of the
coproducts along the degreewise identification, which is `HomologicalComplex₂.hasTotal_of_iso`.

The three universes are free and independent: the objects and the morphisms of the site, and
the sections of the structure sheaf, in which the sections of the modules are taken as well.
The site over `U` has its objects in `max u v` and its morphisms still in `v`, which the
general results above accommodate, since they fix no relation between the two.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.RingedSite

section LocallyBijective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] {R : Sheaf J RingCat.{w}}
  {P Q : PresheafOfModules.{w} R.obj} {M N : SheafOfModules.{w} R}

/-- Composing with a locally bijective morphism `f : P ⟶ M` of presheaves of modules whose
target is a sheaf is a bijection from the morphisms of sheaves of modules out of `M` to the
morphisms of presheaves of modules out of `P`. -/
def homEquivOfUnit (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f] :
    (M ⟶ N) ≃ (P ⟶ N.val) where
  toFun φ := f ≫ φ.val
  invFun h := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective f N.isSheaf).symm h⟩
  left_inv φ := SheafOfModules.hom_ext
    ((PresheafOfModules.homEquivOfIsLocallyBijective f N.isSheaf).left_inv φ.val)
  right_inv h := (PresheafOfModules.homEquivOfIsLocallyBijective f N.isSheaf).right_inv h

/-- The morphism of sheaves of modules `M ⟶ N` determined by a morphism of presheaves of
modules `P ⟶ N` along a locally bijective `P ⟶ M`. -/
def liftOfUnit (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    (h : P ⟶ N.val) : M ⟶ N :=
  (homEquivOfUnit (N := N) f).symm h

/-- `liftOfUnit f h` restricts along `f` to `h`. -/
lemma comp_liftOfUnit (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    (h : P ⟶ N.val) : f ≫ (liftOfUnit (N := N) f h).val = h :=
  (homEquivOfUnit (N := N) f).apply_symm_apply h

/-- Two morphisms of sheaves of modules out of `M` agreeing after a locally bijective
`f : P ⟶ M` are equal. -/
lemma hom_ext_of_unit (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    {φ ψ : M ⟶ N} (h : f ≫ φ.val = f ≫ ψ.val) : φ = ψ :=
  (homEquivOfUnit (N := N) f).injective h

/-- Two sheaves of modules receiving locally bijective morphisms from isomorphic presheaves of
modules are isomorphic, by the morphism determined by the comparison of the presheaves. -/
def isoOfUnits (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g] [PresheafOfModules.IsLocallySurjective J g]
    (e : P ≅ Q) : M ≅ N where
  hom := liftOfUnit f (e.hom ≫ g)
  inv := liftOfUnit g (e.inv ≫ f)
  hom_inv_id := by
    refine hom_ext_of_unit f ?_
    rw [SheafOfModules.comp_val, SheafOfModules.id_val, Category.comp_id,
      ← Category.assoc, comp_liftOfUnit, Category.assoc, comp_liftOfUnit,
      ← Category.assoc, e.hom_inv_id, Category.id_comp]
  inv_hom_id := by
    refine hom_ext_of_unit g ?_
    rw [SheafOfModules.comp_val, SheafOfModules.id_val, Category.comp_id,
      ← Category.assoc, comp_liftOfUnit, Category.assoc, comp_liftOfUnit,
      ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The forward morphism of `isoOfUnits` is the one determined by the comparison of the
presheaves. -/
lemma isoOfUnits_hom (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g] [PresheafOfModules.IsLocallySurjective J g]
    (e : P ≅ Q) : (isoOfUnits f g e).hom = liftOfUnit f (e.hom ≫ g) := rfl

variable {P' Q' : PresheafOfModules.{w} R.obj} {M' N' : SheafOfModules.{w} R}

/-- **`isoOfUnits` is natural.** If a morphism `φ : M ⟶ M'` is induced by a morphism
`p : P ⟶ P'` of the presheaves, a morphism `ψ : N ⟶ N'` by `q : Q ⟶ Q'`, and the comparisons
`e : P ≅ Q` and `e' : P' ≅ Q'` carry `p` to `q`, then `φ` and `ψ` are carried to one another by
the two isomorphisms. -/
lemma isoOfUnits_naturality
    (f : P ⟶ M.val) (g : Q ⟶ N.val) (f' : P' ⟶ M'.val) (g' : Q' ⟶ N'.val)
    [PresheafOfModules.IsLocallyInjective J f] [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g] [PresheafOfModules.IsLocallySurjective J g]
    [PresheafOfModules.IsLocallyInjective J f'] [PresheafOfModules.IsLocallySurjective J f']
    [PresheafOfModules.IsLocallyInjective J g'] [PresheafOfModules.IsLocallySurjective J g']
    (e : P ≅ Q) (e' : P' ≅ Q') {φ : M ⟶ M'} {ψ : N ⟶ N'} {p : P ⟶ P'} {q : Q ⟶ Q'}
    (hφ : f ≫ φ.val = p ≫ f') (hψ : g ≫ ψ.val = q ≫ g')
    (hpq : p ≫ e'.hom = e.hom ≫ q) :
    φ ≫ (isoOfUnits f' g' e').hom = (isoOfUnits f g e).hom ≫ ψ := by
  refine hom_ext_of_unit f ?_
  have h1 : f ≫ (φ ≫ (isoOfUnits f' g' e').hom).val = p ≫ e'.hom ≫ g' :=
    ((Category.assoc f φ.val _).symm.trans
        (congrArg (fun m => m ≫ (isoOfUnits f' g' e').hom.val) hφ)).trans
      ((Category.assoc p f' _).trans
        (congrArg (fun m => p ≫ m) (comp_liftOfUnit f' (e'.hom ≫ g'))))
  have h2 : f ≫ ((isoOfUnits f g e).hom ≫ ψ).val = e.hom ≫ q ≫ g' :=
    ((Category.assoc f _ ψ.val).symm.trans
        (congrArg (fun m => m ≫ ψ.val) (comp_liftOfUnit f (e.hom ≫ g)))).trans
      ((Category.assoc e.hom g ψ.val).trans (congrArg (fun m => e.hom ≫ m) hψ))
  have h3 : p ≫ e'.hom ≫ g' = e.hom ≫ q ≫ g' :=
    ((Category.assoc p e'.hom g').symm.trans (congrArg (fun m => m ≫ g') hpq)).trans
      (Category.assoc e.hom q g')
  exact h1.trans (h3.trans h2.symm)

end LocallyBijective

section SealedUnit

open Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The unit of the sealed sheafification, with the plain forgetful functor as right adjoint, is
locally injective. -/
lemma isLocallyInjective_sheafificationForgetAdjunction_unit_app
    (P : PresheafOfModules.{w} (ringSheaf R).obj) :
    PresheafOfModules.IsLocallyInjective J ((sheafificationForgetAdjunction R).unit.app P) := by
  rw [sheafificationForgetAdjunction_unit_app, PresheafOfModules.IsLocallyInjective,
    Functor.map_comp]
  infer_instance

/-- The unit of the sealed sheafification, with the plain forgetful functor as right adjoint, is
locally surjective. -/
lemma isLocallySurjective_sheafificationForgetAdjunction_unit_app
    (P : PresheafOfModules.{w} (ringSheaf R).obj) :
    PresheafOfModules.IsLocallySurjective J ((sheafificationForgetAdjunction R).unit.app P) := by
  rw [sheafificationForgetAdjunction_unit_app, PresheafOfModules.IsLocallySurjective,
    Functor.map_comp]
  infer_instance

end SealedUnit

section GlobalUnit

open Stacks.SheafOfModules.Tensor

variable (X : RingedSite.{u, v, w}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The restriction to the site over `U` of the unit of the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification` of a presheaf of `O`-modules. -/
def overSheafificationUnit (P : PresheafOfModules.{w} (ringSheaf X.O).obj) :
    overPresheaf X U P ⟶ (((sheafification X.O).obj P).over U).val :=
  overPresheafMap X U ((sheafificationForgetAdjunction X.O).unit.app P)

/-- On underlying presheaves of abelian groups, the restricted sealed sheafification unit is the
sealed sheafification unit whiskered with `(Over.forget U).op`. -/
lemma toPresheaf_map_overSheafificationUnit (P : PresheafOfModules.{w} (ringSheaf X.O).obj) :
    (PresheafOfModules.toPresheaf _).map (overSheafificationUnit X U P) =
      (Over.forget U).op.whiskerLeft
        ((PresheafOfModules.toPresheaf _).map ((sheafificationForgetAdjunction X.O).unit.app P)) :=
  rfl

/-- The restriction to the site over `U` of the sealed sheafification unit is locally injective,
because the forgetful functor of the site over `U` is cocontinuous. -/
instance isLocallyInjective_overSheafificationUnit
    (P : PresheafOfModules.{w} (ringSheaf X.O).obj) :
    PresheafOfModules.IsLocallyInjective (X.J.over U) (overSheafificationUnit X U P) := by
  have := isLocallyInjective_sheafificationForgetAdjunction_unit_app X.O P
  rw [PresheafOfModules.IsLocallyInjective, toPresheaf_map_overSheafificationUnit]
  exact Presheaf.isLocallyInjective_whisker (X.J.over U) X.J (Over.forget U) _

/-- The restriction to the site over `U` of the sealed sheafification unit is locally
surjective, because the forgetful functor of the site over `U` is cocontinuous. -/
instance isLocallySurjective_overSheafificationUnit
    (P : PresheafOfModules.{w} (ringSheaf X.O).obj) :
    PresheafOfModules.IsLocallySurjective (X.J.over U) (overSheafificationUnit X U P) := by
  have := isLocallySurjective_sheafificationForgetAdjunction_unit_app X.O P
  rw [PresheafOfModules.IsLocallySurjective, toPresheaf_map_overSheafificationUnit]
  exact Presheaf.isLocallySurjective_whisker (X.J.over U) X.J (Over.forget U) _

/-- The restriction to the site over `U` of the sealed sheafification unit is natural: it is the
restriction of a natural transformation. -/
lemma overSheafificationUnit_naturality {P P' : PresheafOfModules.{w} (ringSheaf X.O).obj}
    (p : P ⟶ P') :
    overSheafificationUnit X U P ≫ (((sheafification X.O).map p).over U).val =
      overPresheafMap X U p ≫ overSheafificationUnit X U P' :=
  ((PresheafOfModules.pushforward _).map_comp _ _).symm.trans
    ((congrArg (PresheafOfModules.pushforward _).map
      ((sheafificationForgetAdjunction X.O).unit.naturality p).symm).trans
      ((PresheafOfModules.pushforward _).map_comp _ _))

end GlobalUnit

section Tensor

open Stacks.SheafOfModules.Tensor

attribute [local implicit_reducible] PresheafOfModules.tensorBifunctor PresheafOfModules.tensorObj

variable (X : RingedSite.{u, v, w}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The objectwise tensor product of the underlying presheaves of two sheaves of `O`-modules.
The ascribed type names the sheaf of rings in the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf X.O` at which the sealed sheafification and the
restriction to the site over `U` are indexed. -/
abbrev globalTensorPresheaf (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    PresheafOfModules.{w} (ringSheaf X.O).obj :=
  ((PresheafOfModules.tensorBifunctor X.O.obj).obj M.val).obj N.val

/-- The objectwise tensor product, formed on the site over `U`, of the restrictions of the
underlying presheaves of two sheaves of `O`-modules. The ascribed type names the restricted
sheaf of rings in the spelling `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U` at which
the slice machinery is indexed. -/
abbrev overTensorPresheaf (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    PresheafOfModules.{w} ((ringSheaf X.O).over U).obj :=
  ((PresheafOfModules.tensorBifunctor (X.O.over U).obj).obj (M.over U).val).obj (N.over U).val

/-- The objectwise tensor product of the underlying presheaves of two sheaves of `O`-modules,
restricted to the site over `U`, is the objectwise tensor product formed over `U`: over each
object of the site over `U` both sides are the same tensor product of sections. -/
def overPresheafTensorIso (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    overPresheaf X U (globalTensorPresheaf X M N) ≅
      overTensorPresheaf X U M N :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)

/-- The unit of the sealed sheafification on the site over `U`, from the objectwise tensor
product of the restrictions of two sheaves of `O`-modules to their sheaf tensor product formed
over `U`. Its type is read over the restricted sheaf of rings in the spelling
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U` of `overTensorPresheaf`. -/
def overTensorUnit (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    overTensorPresheaf X U M N ⟶ SheafOfModules.val (R := (ringSheaf X.O).over U)
      (((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).obj (M.over U)).obj (N.over U)) :=
  (sheafificationForgetAdjunction (X.O.over U)).unit.app (overTensorPresheaf X U M N)

instance isLocallyInjective_overTensorUnit (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    PresheafOfModules.IsLocallyInjective (X.J.over U) (overTensorUnit X U M N) :=
  isLocallyInjective_sheafificationForgetAdjunction_unit_app (X.O.over U) _

instance isLocallySurjective_overTensorUnit (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    PresheafOfModules.IsLocallySurjective (X.J.over U) (overTensorUnit X U M N) :=
  isLocallySurjective_sheafificationForgetAdjunction_unit_app (X.O.over U) _

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `overTensorUnit` is natural: it is a component of the unit of the sealed sheafification on
the site over `U`. -/
lemma overTensorUnit_naturality {M N M' N' : SheafOfModules.{w} (ringSheaf X.O)}
    (q : overTensorPresheaf X U M N ⟶ overTensorPresheaf X U M' N') :
    overTensorUnit X U M N ≫ ((sheafification (X.O.over U)).map q).val =
      q ≫ overTensorUnit X U M' N' :=
  ((sheafificationForgetAdjunction (X.O.over U)).unit.naturality q).symm

/-- The restriction to the site over `U` of the sheaf tensor product of two sheaves of
`O`-modules is the sheaf tensor product formed over `U`. Both sides receive a locally bijective
morphism from the restricted objectwise tensor product of the underlying presheaves: the
left-hand one the restriction of the sheafification unit, which is locally bijective because
the forgetful functor of the site over `U` is cocontinuous, and the right-hand one its own
sheafification unit. -/
def sheafTensorOverIso (M N : SheafOfModules.{w} (ringSheaf X.O)) :
    (((sheafTensor.{u, v, w, w, w} X.O).obj M).obj N).over U ≅
      ((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).obj (M.over U)).obj (N.over U) :=
  isoOfUnits (R := (ringSheaf X.O).over U)
    (M := ((sheafification X.O).obj (globalTensorPresheaf X M N)).over U)
    (overSheafificationUnit X U (globalTensorPresheaf X M N))
    (overTensorUnit X U M N) (overPresheafTensorIso X U M N)

/-- Naturality of `sheafTensorOverIso` for a morphism induced by a morphism of the presheaves,
given the corresponding square on the restricted objectwise tensor products. -/
private theorem sheafTensorOverIso_naturality_aux
    {M N M' N' : SheafOfModules.{w} (ringSheaf X.O)}
    (p : globalTensorPresheaf X M N ⟶ globalTensorPresheaf X M' N')
    (q : overTensorPresheaf X U M N ⟶ overTensorPresheaf X U M' N')
    (hpq : overPresheafMap X U p ≫ (overPresheafTensorIso X U M' N').hom =
      (overPresheafTensorIso X U M N).hom ≫ q) :
    ((sheafification X.O).map p).over U ≫ (sheafTensorOverIso X U M' N').hom =
      (sheafTensorOverIso X U M N).hom ≫ (sheafification (X.O.over U)).map q :=
  isoOfUnits_naturality (R := (ringSheaf X.O).over U)
    (overSheafificationUnit X U (globalTensorPresheaf X M N)) (overTensorUnit X U M N)
    (overSheafificationUnit X U (globalTensorPresheaf X M' N')) (overTensorUnit X U M' N')
    (overPresheafTensorIso X U M N) (overPresheafTensorIso X U M' N')
    (overSheafificationUnit_naturality X U p) (overTensorUnit_naturality X U q) hpq

attribute [local instance] ringSheafOverSectionsCommRing

/-- **`sheafTensorOverIso` is natural in the first variable.** -/
lemma sheafTensorOverIso_naturality_left
    {M M' : SheafOfModules.{w} (ringSheaf X.O)} (f : M ⟶ M')
    (N : SheafOfModules.{w} (ringSheaf X.O)) :
    (((sheafTensor.{u, v, w, w, w} X.O).map f).app N).over U ≫ (sheafTensorOverIso X U M' N).hom =
      (sheafTensorOverIso X U M N).hom ≫
        ((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).map (f.over U)).app (N.over U) :=
  sheafTensorOverIso_naturality_aux X U
    (((PresheafOfModules.tensorBifunctor X.O.obj).map f.val).app N.val)
    (((PresheafOfModules.tensorBifunctor (X.O.over U).obj).map (f.over U).val).app
      (N.over U).val)
    (PresheafOfModules.hom_ext fun _ => ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl)

/-- **`sheafTensorOverIso` is natural in the second variable.** -/
lemma sheafTensorOverIso_naturality_right
    (M : SheafOfModules.{w} (ringSheaf X.O))
    {N N' : SheafOfModules.{w} (ringSheaf X.O)} (g : N ⟶ N') :
    (((sheafTensor.{u, v, w, w, w} X.O).obj M).map g).over U ≫ (sheafTensorOverIso X U M N').hom =
      (sheafTensorOverIso X U M N).hom ≫
        ((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).obj (M.over U)).map (g.over U) :=
  sheafTensorOverIso_naturality_aux X U
    (((PresheafOfModules.tensorBifunctor X.O.obj).obj M.val).map g.val)
    (((PresheafOfModules.tensorBifunctor (X.O.over U).obj).obj (M.over U).val).map
      (g.over U).val)
    (PresheafOfModules.hom_ext fun _ => ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl)

end Tensor

section TensorComplex

open Stacks.SheafOfModules.Tensor

attribute [local implicit_reducible] PresheafOfModules.tensorBifunctor PresheafOfModules.tensorObj

variable (X : RingedSite.{u, v, w}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{max u v, v, w, w, w} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (sheafTensor.{max u v, v, w, w, w} (X.O.over U)) (ComplexShape.up ℤ)]

variable (A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The double complex of sheaf tensor products of the terms of two complexes of `O`-modules.
Its total complex is the total tensor complex. -/
abbrev sheafTensorBicomplex :
    HomologicalComplex₂ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor.{u, v, w, w, w} X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A).obj B

/-- The double complex of sheaf tensor products, formed on the site over `U`, of the terms of
the restrictions of two complexes of `O`-modules. -/
abbrev overSheafTensorBicomplex :
    HomologicalComplex₂
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor.{max u v, v, w, w, w} (X.O.over U)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj (restrictComplex X A U)).obj
      (restrictComplex X B U)

/-- The termwise restriction to the site over `U` of the double complex of sheaf tensor
products of two complexes of `O`-modules is the double complex formed over `U` from their
restrictions: in bidegree `(p, q)` this is `sheafTensorOverIso`, and the two differentials are
the two naturality squares of that identification. -/
def overSheafTensorBicomplexIso :
    HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (sheafTensorBicomplex X A B) ≅
      overSheafTensorBicomplex X U A B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => sheafTensorOverIso X U (A.X p) (B.X q))
      (fun i j _ => (sheafTensorOverIso_naturality_right X U (A.X p) (B.d i j)).symm))
    (fun i j _ => by
      ext q : 1
      exact (sheafTensorOverIso_naturality_left X U (A.d i j) (B.X q)).symm)

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the restricted total complex exceeds the default limit
set_option maxHeartbeats 800000 in
-- elaborating the total-complex isomorphism over the restriction functor is heavy
/-- **Restriction to the site over `U` commutes with the total tensor complex**: the
restriction of `Tot(A ⊗_O B)` is `Tot(A|_U ⊗_{O|_U} B|_U)`.

Degreewise this is the identification `overSheafTensorBicomplexIso` of the two double
complexes, and the passage to the total complexes is
`HomologicalComplex₂.TotalMap.totalIso`, whose hypothesis is that restriction preserves the
coproducts indexed by the bidegrees of a fixed total degree. -/
def tensorComplexOverIso :
    restrictComplex X (((tensorComplex X.O).obj A).obj B) U ≅
      ((tensorComplex (X.O.over U)).obj (restrictComplex X A U)).obj
        (restrictComplex X B U) := by
  have : PreservesColimitsOfSize.{w, w}
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    preservesColimitsOfSize_shrink _
  have : HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
          (sheafTensorBicomplex X A B))
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (overSheafTensorBicomplexIso X U A B).symm _
  exact (HomologicalComplex₂.TotalMap.totalIso
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (sheafTensorBicomplex X A B)).symm ≪≫
    HomologicalComplex₂.total.mapIso (overSheafTensorBicomplexIso X U A B)
      (ComplexShape.up ℤ)

end TensorComplex

end AlgebraicGeometry.RingedSite

end
