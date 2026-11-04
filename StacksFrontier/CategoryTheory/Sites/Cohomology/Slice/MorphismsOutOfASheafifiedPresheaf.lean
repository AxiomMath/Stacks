module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-! # Morphisms out of the restriction of a sheafified presheaf of modules

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `P` be a presheaf of
`O`-modules. Restricting the associated sheaf `P^#` to the localized site `C/U` gives the sheaf
of `O|_U`-modules associated to the restriction `P|_U`: that is, a morphism of sheaves of
`O|_U`-modules out of `(P^#)|_U` is the same thing as a morphism of presheaves of
`O|_U`-modules out of `P|_U`.

## Main definitions

* `AlgebraicGeometry.RingedSite.overPresheaf` and
  `AlgebraicGeometry.RingedSite.overPresheafMap`: restriction of a presheaf of `O`-modules, and
  of a morphism of such, to the localized site over `U`.
* `AlgebraicGeometry.RingedSite.sheafifyModules`: the sheaf of `O`-modules associated to a
  presheaf of `O`-modules.
* `AlgebraicGeometry.RingedSite.overSheafifyUnit`: the restriction to `C/U` of the
  sheafification unit.
* `AlgebraicGeometry.RingedSite.overSheafifyHomEquiv`: the universal property, namely that
  composing with `overSheafifyUnit` is a bijection from the morphisms of sheaves of
  `O|_U`-modules out of `(P^#)|_U` to the morphisms of presheaves of `O|_U`-modules out of
  `P|_U`.
* `AlgebraicGeometry.RingedSite.overSheafifyLift`: the morphism on the slice determined by a
  presheaf-level morphism.

## Main results

* `AlgebraicGeometry.RingedSite.overSheafifyUnit_comp_overSheafifyLift` and
  `AlgebraicGeometry.RingedSite.overSheafifyLift_apply`: `overSheafifyLift f` restricts along
  the unit to `f`, degreewise and on sections.
* `AlgebraicGeometry.RingedSite.overSheafify_hom_ext`: two morphisms on the slice out of a
  sheafified presheaf of modules which agree after the unit are equal.

## Implementation notes

The whole content is that the restricted unit is still locally bijective. Restriction to the
localized site is precomposition with `(Over.forget U).op`, and `Over.forget U` is cocontinuous
from `J.over U` to `J`, so `CategoryTheory.Presheaf.isLocallyInjective_whisker` and
`isLocallySurjective_whisker` apply; the identification of the restricted unit with the
whiskered sheafification unit of the underlying presheaf of abelian groups is a definitional
equality, recorded as `toPresheaf_map_overSheafifyUnit` so that the two instances can be
rewritten into shape. Given local bijectivity, the universal property is Mathlib's
`PresheafOfModules.homEquivOfIsLocallyBijective`, which asks only for a locally bijective
morphism into a sheaf and not for the target to be Mathlib's sheafification construction. No
comparison between `(P^#)|_U` and the sheafification of `P|_U` is therefore needed, and in
particular neither the right adjoint `j_{U*}` — which Mathlib provides only for a site with
binary products — nor the exactness of restriction is used.

`overSheafifyHomEquiv` is built by hand rather than as a composite of
`SheafOfModules.fullyFaithfulForget`'s `homEquiv` with
`PresheafOfModules.homEquivOfIsLocallyBijective`, so that its forward direction is literally
composition with the unit; the composite's forward direction is not that spelling, and the
characterising lemmas below would then not be `rfl`.

`overPresheaf` and `sheafifyModules` are abbreviations, so that `(A.over U).val` and the terms
of a degreewise sheafification are seen to be of those forms with no rewriting.

The instance `(J.over U).WEqualsLocallyBijective AddCommGrpCat` is assumed rather than derived,
since at unrelated universes it is not available; it is synthesized automatically whenever the
ambient one is, as on the site universes of Stacks 0A90.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w}) (U : X.C)

/-- The sections of the restricted structure sheaf over an object of the site over `U` are a
commutative ring: they are the sections of the structure sheaf over the underlying object of
the site. -/
noncomputable local instance ringSheafOverSectionsCommRing (V : (Over U)ᵒᵖ) :
    CommRing (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj V) :=
  inferInstanceAs (CommRing (X.O.obj.obj (Opposite.op V.unop.left)))

/-- The restriction of a presheaf of `O`-modules to the site over `U`: precomposition with
`(Over.forget U).op`, read over the restricted sheaf of rings `O|_U`. -/
abbrev overPresheaf (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    PresheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj :=
  (PresheafOfModules.pushforward (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)).obj P

/-- The restriction of a morphism of presheaves of `O`-modules to the site over `U`. -/
abbrev overPresheafMap
    {P Q : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj} (f : P ⟶ Q) :
    overPresheaf X U P ⟶ overPresheaf X U Q :=
  (PresheafOfModules.pushforward (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj)).map f

variable [HasWeakSheafify X.J AddCommGrpCat.{m}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The sheaf of `O`-modules associated to a presheaf of `O`-modules. -/
abbrev sheafifyModules
    (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj P

/-- The restriction to the site over `U` of the unit of the sheafification of a presheaf of
`O`-modules. -/
def overSheafifyUnit (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    overPresheaf X U P ⟶ ((sheafifyModules X P).over U).val :=
  overPresheafMap X U
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app P)

/-- On underlying presheaves of abelian groups, the restricted sheafification unit is the
sheafification unit whiskered with `(Over.forget U).op`. -/
lemma toPresheaf_map_overSheafifyUnit
    (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    (PresheafOfModules.toPresheaf _).map (overSheafifyUnit X U P) =
      (Over.forget U).op.whiskerLeft (CategoryTheory.toSheafify X.J P.presheaf) := rfl

/-- The restriction to the site over `U` of the sheafification unit of a presheaf of
`O`-modules is locally injective. -/
instance isLocallyInjective_overSheafifyUnit
    (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    PresheafOfModules.IsLocallyInjective (X.J.over U) (overSheafifyUnit X U P) := by
  rw [PresheafOfModules.IsLocallyInjective, toPresheaf_map_overSheafifyUnit]
  exact Presheaf.isLocallyInjective_whisker (X.J.over U) X.J (Over.forget U) _

/-- The restriction to the site over `U` of the sheafification unit of a presheaf of
`O`-modules is locally surjective. -/
instance isLocallySurjective_overSheafifyUnit
    (P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    PresheafOfModules.IsLocallySurjective (X.J.over U) (overSheafifyUnit X U P) := by
  rw [PresheafOfModules.IsLocallySurjective, toPresheaf_map_overSheafifyUnit]
  exact Presheaf.isLocallySurjective_whisker (X.J.over U) X.J (Over.forget U) _

variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable {P : PresheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {N : SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)}

/-- **The universal property of sheafification on a slice.** Composing with the restricted
sheafification unit is a bijection from the morphisms of sheaves of `O|_U`-modules
`(P^#)|_U ⟶ N` to the morphisms of presheaves of `O|_U`-modules `P|_U ⟶ N`. -/
def overSheafifyHomEquiv :
    ((sheafifyModules X P).over U ⟶ N) ≃ (overPresheaf X U P ⟶ N.val) where
  toFun φ := overSheafifyUnit X U P ≫ φ.val
  invFun f := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (overSheafifyUnit X U P) N.isSheaf).symm f⟩
  left_inv φ := SheafOfModules.hom_ext
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (overSheafifyUnit X U P) N.isSheaf).left_inv φ.val)
  right_inv f := (PresheafOfModules.homEquivOfIsLocallyBijective
    (overSheafifyUnit X U P) N.isSheaf).right_inv f

/-- `overSheafifyHomEquiv` is composition with the restricted sheafification unit. -/
lemma overSheafifyHomEquiv_apply (φ : (sheafifyModules X P).over U ⟶ N) :
    overSheafifyHomEquiv X U φ = overSheafifyUnit X U P ≫ φ.val := rfl

/-- The morphism of sheaves of `O|_U`-modules out of `(P^#)|_U` determined by a morphism of
presheaves of `O|_U`-modules out of `P|_U`. -/
def overSheafifyLift (f : overPresheaf X U P ⟶ N.val) :
    (sheafifyModules X P).over U ⟶ N :=
  (overSheafifyHomEquiv X U).symm f

/-- `overSheafifyLift f` restricts along the restricted sheafification unit to `f`. -/
lemma overSheafifyUnit_comp_overSheafifyLift (f : overPresheaf X U P ⟶ N.val) :
    overSheafifyUnit X U P ≫ (overSheafifyLift X U f).val = f :=
  (overSheafifyHomEquiv X U).apply_symm_apply f

/-- `overSheafifyLift f` agrees with `f` on the sections coming from the presheaf level. -/
lemma overSheafifyLift_apply (f : overPresheaf X U P ⟶ N.val) (W : (Over U)ᵒᵖ)
    (x : (overPresheaf X U P).obj W) :
    (overSheafifyLift X U f).val.app W ((overSheafifyUnit X U P).app W x) = f.app W x :=
  congrArg (fun g ↦ g.app W x) (overSheafifyUnit_comp_overSheafifyLift X U f)

/-- Two morphisms of sheaves of `O|_U`-modules out of `(P^#)|_U` which agree after the
restricted sheafification unit are equal. -/
lemma overSheafify_hom_ext {φ ψ : (sheafifyModules X P).over U ⟶ N}
    (h : overSheafifyUnit X U P ≫ φ.val = overSheafifyUnit X U P ≫ ψ.val) : φ = ψ :=
  (overSheafifyHomEquiv X U).injective h

end AlgebraicGeometry.RingedSite

end
