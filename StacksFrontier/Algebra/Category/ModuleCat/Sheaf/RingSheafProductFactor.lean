module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Algebra.Category.Ring.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A factor of a product of sheaves of rings is a direct summand of the structure sheaf

Let `R` be a sheaf of commutative rings on a site `(C, J)` which is a product `R ≅ ∏ factor n`
of a family of sheaves of commutative rings.  For each index `n` the sheaf `factor n`, read as a
sheaf of `R`-modules through the projection `R ⟶ factor n`, is a direct summand of `R` itself:
the inclusion sends a section `a` of `factor n` to the section of `R` whose `n`-th component is
`a` and whose other components vanish.

## Main definitions

* `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`: a family of projections
  `R ⟶ factor n` whose joint evaluation on the sections over every object of the site is
  bijective.
* `Stacks.SheafOfModules.RingSheafProductFactor.factorModule`: the sheaf `factor n` read as a
  sheaf of `R`-modules along the `n`-th projection.
* `Stacks.SheafOfModules.RingSheafProductFactor.factorProjection`,
  `Stacks.SheafOfModules.RingSheafProductFactor.factorInclusion`: the two morphisms of sheaves of
  `R`-modules exhibiting `factorModule` as a direct summand of the structure sheaf.
* `Stacks.SheafOfModules.RingSheafProductFactor.retract`,
  `Stacks.SheafOfModules.RingSheafProductFactor.retractOfIso`,
  `Stacks.SheafOfModules.RingSheafProductFactor.retractOfProduct`: the resulting retracts, for a
  product presentation, for a sheaf of rings isomorphic to `∏ factor`, and for `∏ factor` itself.
* `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIsLimit`,
  `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofIso`,
  `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.ofProduct`: the projections of
  a limit fan, of a sheaf of rings isomorphic to `∏ factor`, and of `∏ factor` itself form a
  product presentation.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor.factorInclusion_comp_factorProjection`: the
  inclusion followed by the projection is the identity of `factorModule`.
* `Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract`,
  `Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_of_iso`,
  `Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract_of_product`: the same three
  statements in `Nonempty (Retract _ _)` form, which needs no decidable equality on the index
  type.

## Implementation notes

The inclusion is not a morphism of sheaves of rings — it is not unital — so it is built on
sections, as the preimage of the family `Pi.single n a` under the bijection of
`ProductPresentation`.  Its additivity, its `R`-linearity and its naturality are each checked by
comparing components, which the injectivity half of the bijection reduces to identities between
sections of the factors.

The bijectivity is deduced from a limit fan by pushing the fan through `sheafToPresheaf`,
evaluation at an object of the site and the forgetful functor to types, all three of which
preserve products, and then testing the resulting limit cone in `Type w` against the one-point
set: that gives injectivity and surjectivity at once, with no product of types in sight.  This is
what keeps the index type in an arbitrary universe, independent of the universe of the sections.

## References

* `Mathlib.CategoryTheory.Retract`, for `CategoryTheory.Retract`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, for
  `SheafOfModules.restrictScalars`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf`, for `SheafOfModules.unit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w t

namespace Stacks.SheafOfModules

namespace Tensor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Invertibility of a sheaf of modules over a sheaf of commutative rings**
([Stacks, Tag 01CS]), stated over the sheaf of (not necessarily commutative) rings
`Tensor.ringSheaf S` over which modules are actually taken.

This is `Stacks.SheafOfModules.IsInvertible`, whose sheaf-condition argument is here supplied by
`ringSheaf` rather than carried separately; a sheaf of commutative rings is all a consumer has
when the ring sheaf arises as one factor of a product decomposition, which is the situation of
every use. -/
abbrev IsInvertibleModule {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (S : Sheaf J CommRingCat.{w}) (L : _root_.SheafOfModules.{w} (ringSheaf S)) : Prop :=
  Stacks.SheafOfModules.IsInvertible S.obj (ringSheaf S).property L

end Tensor

namespace RingSheafProductFactor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}

/-- A presentation of a sheaf of commutative rings `R` as the product of a family `factor`:
a family of morphisms of sheaves of rings `π n : R ⟶ factor n` whose joint evaluation on the
sections over any object of the site is a bijection onto the product of the sections of the
factors. -/
structure ProductPresentation (R : Sheaf J CommRingCat.{w})
    (factor : ι → Sheaf J CommRingCat.{w}) where
  /-- the projection onto the `n`-th factor -/
  π (n : ι) : R ⟶ factor n
  /-- a section of `R` is determined by its components -/
  injective ⦃U : Cᵒᵖ⦄ ⦃r r' : ↥(R.obj.obj U)⦄
    (h : ∀ n, (π n).hom.app U r = (π n).hom.app U r') : r = r'
  /-- every family of sections of the factors is the family of components of a section of `R` -/
  surjective (U : Cᵒᵖ) (a : ∀ n, ↥((factor n).obj.obj U)) :
    ∃ r : ↥(R.obj.obj U), ∀ n, (π n).hom.app U r = a n

variable {factor : ι → Sheaf J CommRingCat.{w}} {R : Sheaf J CommRingCat.{w}}
  (hp : ProductPresentation R factor)

namespace ProductPresentation

/-- The naturality of the `n`-th projection, read on sections. -/
lemma app_map (n : ι) {U V : Cᵒᵖ} (f : U ⟶ V) (r : ↥(R.obj.obj U)) :
    (hp.π n).hom.app V (R.obj.map f r) = (factor n).obj.map f ((hp.π n).hom.app U r) := by
  simp

/-- The `n`-th projection is additive on sections. -/
lemma app_add (n : ι) (U : Cᵒᵖ) (x y : ↥(R.obj.obj U)) :
    (hp.π n).hom.app U (x + y) = (hp.π n).hom.app U x + (hp.π n).hom.app U y :=
  map_add _ x y

/-- The `n`-th projection is multiplicative on sections. -/
lemma app_mul (n : ι) (U : Cᵒᵖ) (x y : ↥(R.obj.obj U)) :
    (hp.π n).hom.app U (x * y) = (hp.π n).hom.app U x * (hp.π n).hom.app U y :=
  map_mul _ x y

variable [DecidableEq ι]

/-- The section of `R` whose `n`-th component is `a` and whose other components vanish. -/
def inclSection (n : ι) (U : Cᵒᵖ) (a : ↥((factor n).obj.obj U)) : ↥(R.obj.obj U) :=
  (hp.surjective U (Pi.single n a)).choose

/-- The `m`-th component of `inclSection hp n U a` is `a` when `m = n` and `0` otherwise. -/
lemma app_inclSection (n m : ι) (U : Cᵒᵖ) (a : ↥((factor n).obj.obj U)) :
    (hp.π m).hom.app U (hp.inclSection n U a)
      = (Pi.single n a : ∀ m, ↥((factor m).obj.obj U)) m :=
  (hp.surjective U (Pi.single n a)).choose_spec m

/-- The `n`-th component of `inclSection hp n U a` is `a`. -/
lemma app_inclSection_self (n : ι) (U : Cᵒᵖ) (a : ↥((factor n).obj.obj U)) :
    (hp.π n).hom.app U (hp.inclSection n U a) = a := by
  rw [hp.app_inclSection n n U a, Pi.single_eq_same]

/-- The `m`-th component of `inclSection hp n U a` vanishes for `m ≠ n`. -/
lemma app_inclSection_of_ne {n m : ι} (hmn : m ≠ n) (U : Cᵒᵖ)
    (a : ↥((factor n).obj.obj U)) :
    (hp.π m).hom.app U (hp.inclSection n U a) = 0 := by
  rw [hp.app_inclSection n m U a, Pi.single_eq_of_ne hmn]

/-- `inclSection hp n U` is additive. -/
lemma inclSection_add (n : ι) (U : Cᵒᵖ) (a b : ↥((factor n).obj.obj U)) :
    hp.inclSection n U (a + b) = hp.inclSection n U a + hp.inclSection n U b := by
  refine hp.injective fun m ↦ ?_
  simp [hp.app_inclSection, Pi.single_add]

/-- `inclSection hp n U` is `R`-linear, the action on the factor being through the `n`-th
projection. -/
lemma inclSection_smul (n : ι) (U : Cᵒᵖ) (r : ↥(R.obj.obj U))
    (a : ↥((factor n).obj.obj U)) :
    hp.inclSection n U ((hp.π n).hom.app U r * a) = r * hp.inclSection n U a := by
  refine hp.injective fun m ↦ ?_
  by_cases hmn : m = n
  · subst hmn
    simp [hp.app_inclSection]
  · simp [hp.app_inclSection, hmn]

/-- `inclSection hp n` is compatible with the restriction maps of the sheaves. -/
lemma map_inclSection (n : ι) {U V : Cᵒᵖ} (f : U ⟶ V) (a : ↥((factor n).obj.obj U)) :
    R.obj.map f (hp.inclSection n U a) = hp.inclSection n V ((factor n).obj.map f a) := by
  refine hp.injective fun m ↦ ?_
  rw [hp.app_map m f]
  by_cases hmn : m = n
  · subst hmn
    simp [hp.app_inclSection]
  · simp [hp.app_inclSection, hmn]

end ProductPresentation

/-- The sheaf of commutative rings `factor n`, read as a sheaf of modules over `R` through the
`n`-th projection. -/
def factorModule (n : ι) : _root_.SheafOfModules.{w} (Tensor.ringSheaf R) :=
  (_root_.SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (hp.π n))).obj
    (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n)))

/-- The `n`-th projection, read as a morphism of sheaves of `R`-modules from the structure sheaf
to the `n`-th factor.  On sections it is `r ↦ π n r`. -/
def factorProjection (n : ι) :
    _root_.SheafOfModules.unit (Tensor.ringSheaf R) ⟶ factorModule hp n where
  val :=
    { app := fun U ↦ ConcreteCategory.ofHom
        { toFun := fun r ↦ (hp.π n).hom.app U r
          map_add' := fun x y ↦ hp.app_add n U x y
          map_smul' := fun c x ↦ hp.app_mul n U c x }
      naturality := fun {U V} f ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        exact hp.app_map n f x }

section Inclusion

variable [DecidableEq ι]

/-- The inclusion of the `n`-th factor into the structure sheaf, as a morphism of sheaves of
`R`-modules.  On sections it sends `a` to the section of `R` with `n`-th component `a` and all
other components zero; it is `R`-linear but not a morphism of sheaves of rings. -/
def factorInclusion (n : ι) :
    factorModule hp n ⟶ _root_.SheafOfModules.unit (Tensor.ringSheaf R) where
  val :=
    { app := fun U ↦ ConcreteCategory.ofHom
        { toFun := hp.inclSection n U
          map_add' := hp.inclSection_add n U
          map_smul' := fun c x ↦ hp.inclSection_smul n U c x }
      naturality := fun {U V} f ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        exact (hp.map_inclSection n f x).symm }

/-- **The `n`-th factor is a direct summand of the structure sheaf**: the inclusion followed by
the projection is the identity. -/
theorem factorInclusion_comp_factorProjection (n : ι) :
    factorInclusion hp n ≫ factorProjection hp n = 𝟙 (factorModule hp n) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_))
  change (hp.π n).hom.app U (hp.inclSection n U a) = a
  exact hp.app_inclSection_self n U a

/-- **The `n`-th factor, read as a sheaf of `R`-modules, is a retract of the structure sheaf.** -/
def retract (n : ι) :
    Retract (factorModule hp n) (_root_.SheafOfModules.unit (Tensor.ringSheaf R)) where
  i := factorInclusion hp n
  r := factorProjection hp n
  retract := factorInclusion_comp_factorProjection hp n

end Inclusion

/-- **The `n`-th factor, read as a sheaf of `R`-modules, is a retract of the structure sheaf.**
The statement is independent of a decidable equality on the index type. -/
theorem nonempty_retract (n : ι) :
    Nonempty (Retract (factorModule hp n)
      (_root_.SheafOfModules.unit (Tensor.ringSheaf R))) := by
  classical
  exact ⟨retract hp n⟩

namespace ProductPresentation

variable [HasLimitsOfShape (Discrete ι) CommRingCat.{w}]

/-- Products of sheaves of commutative rings, given products in `CommRingCat`, through
presheaves (instance search no longer finds this unaided; a local instance below). -/
theorem hasLimitsOfShape_sheaf_discrete : HasLimitsOfShape (Discrete ι) (Sheaf J CommRingCat.{w}) :=
  haveI : HasLimitsOfShape (Discrete ι) (Cᵒᵖ ⥤ CommRingCat.{w}) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J CommRingCat.{w})

theorem hasProduct_factor (factor : ι → Sheaf J CommRingCat.{w}) : HasProduct factor :=
  HasLimitsOfShape.has_limit (self := hasLimitsOfShape_sheaf_discrete) _

attribute [local instance high] hasProduct_factor

/-- **A limit fan of sheaves of commutative rings is a product presentation.**  Taking sections
over an object of the site preserves the product, and the resulting limit cone in types is tested
against the one-point set, which gives injectivity and surjectivity at once. -/
def ofIsLimit (p : ∀ n, R ⟶ factor n) (hlim : IsLimit (Fan.mk R p)) :
    ProductPresentation R factor where
  π := p
  injective := fun U r r' h ↦ by
    have h' := isLimitOfPreserves (sheafToPresheaf J CommRingCat.{w} ⋙
      (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{w}).obj U ⋙
        CategoryTheory.forget CommRingCat.{w}) hlim
    refine ConcreteCategory.congr_hom
      (h'.hom_ext (f := TypeCat.ofHom fun _ : PUnit.{w + 1} ↦ r)
        (f' := TypeCat.ofHom fun _ : PUnit.{w + 1} ↦ r') ?_) PUnit.unit
    rintro ⟨n⟩
    ext _
    exact h n
  surjective := fun U a ↦ by
    have h' := isLimitOfPreserves (sheafToPresheaf J CommRingCat.{w} ⋙
      (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{w}).obj U ⋙
        CategoryTheory.forget CommRingCat.{w}) hlim
    let c : Cone (Discrete.functor factor ⋙ (sheafToPresheaf J CommRingCat.{w} ⋙
        (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{w}).obj U ⋙
          CategoryTheory.forget CommRingCat.{w})) :=
      { pt := PUnit.{w + 1}
        π := Discrete.natTrans fun j ↦ TypeCat.ofHom fun _ : PUnit.{w + 1} ↦ a j.as }
    exact ⟨h'.lift c PUnit.unit, fun n ↦ ConcreteCategory.congr_hom (h'.fac c ⟨n⟩) PUnit.unit⟩

/-- **A sheaf of commutative rings isomorphic to `∏ factor` is a product presentation of
`factor`**, with projections the composites of the isomorphism with the product projections. -/
def ofIso (e : R ≅ ∏ᶜ factor) : ProductPresentation R factor :=
  ofIsLimit (fun n ↦ e.hom ≫ Limits.Pi.π factor n)
    ((productIsProduct factor).ofIsoLimit (Cone.ext e.symm (by rintro ⟨n⟩; simp)))

/-- **The product `∏ factor` is a product presentation of `factor`**, with projections the
product projections. -/
def ofProduct [HasProduct factor] : ProductPresentation (∏ᶜ factor) factor :=
  ofIsLimit (Limits.Pi.π factor) (productIsProduct factor)

end ProductPresentation

section OfIso

variable [HasLimitsOfShape (Discrete ι) CommRingCat.{w}]

/-- Products of sheaves of commutative rings, given products in `CommRingCat`, through
presheaves (instance search no longer finds this unaided; a local instance below). -/
theorem hasLimitsOfShape_sheaf_discrete' :
    HasLimitsOfShape (Discrete ι) (Sheaf J CommRingCat.{w}) :=
  haveI : HasLimitsOfShape (Discrete ι) (Cᵒᵖ ⥤ CommRingCat.{w}) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J CommRingCat.{w})

theorem hasProduct_factor' (factor : ι → Sheaf J CommRingCat.{w}) : HasProduct factor :=
  HasLimitsOfShape.has_limit (self := hasLimitsOfShape_sheaf_discrete') _

attribute [local instance high] hasProduct_factor'

/-- **A factor of a product of sheaves of commutative rings is a direct summand of the structure
sheaf.**  For `e : R ≅ ∏ factor`, the sheaf `factor n` read as a sheaf of `R`-modules along
`e.hom ≫ Pi.π factor n` is a retract of `R` read as a module over itself. -/
theorem nonempty_retract_of_iso (e : R ≅ ∏ᶜ factor) (n : ι) :
    Nonempty (Retract
      ((_root_.SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (e.hom ≫ Limits.Pi.π factor n))).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))))
      (_root_.SheafOfModules.unit (Tensor.ringSheaf R))) := by
  classical
  exact ⟨retract (ProductPresentation.ofIso e) n⟩

/-- **A factor of a product of sheaves of commutative rings is a direct summand of the structure
sheaf**, stated for the product `∏ factor` itself. -/
theorem nonempty_retract_of_product [HasProduct factor] (n : ι) :
    Nonempty (Retract
      ((_root_.SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (Limits.Pi.π factor n))).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))))
      (_root_.SheafOfModules.unit (Tensor.ringSheaf (∏ᶜ factor)))) := by
  classical
  exact ⟨retract (ProductPresentation.ofProduct (factor := factor)) n⟩

section
variable [DecidableEq ι]

/-- **A factor of a product of sheaves of commutative rings is a direct summand of the structure
sheaf**, as an explicit retract, for `e : R ≅ ∏ factor`. -/
def retractOfIso (e : R ≅ ∏ᶜ factor) (n : ι) :
    Retract
      ((_root_.SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (e.hom ≫ Limits.Pi.π factor n))).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))))
      (_root_.SheafOfModules.unit (Tensor.ringSheaf R)) :=
  retract (ProductPresentation.ofIso e) n

/-- **A factor of a product of sheaves of commutative rings is a direct summand of the structure
sheaf**, as an explicit retract, for the product `∏ factor` itself. -/
def retractOfProduct [HasProduct factor] (n : ι) :
    Retract
      ((_root_.SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
            (Limits.Pi.π factor n))).obj
        (_root_.SheafOfModules.unit (Tensor.ringSheaf (factor n))))
      (_root_.SheafOfModules.unit (Tensor.ringSheaf (∏ᶜ factor))) :=
  retract (ProductPresentation.ofProduct (factor := factor)) n

end

end OfIso

end RingSheafProductFactor

end Stacks.SheafOfModules

end
