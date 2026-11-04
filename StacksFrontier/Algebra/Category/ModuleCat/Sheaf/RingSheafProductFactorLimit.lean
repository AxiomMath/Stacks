module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactor

/-!
# A product of sheaves of rings is the product of its factors as a sheaf of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)` presented as a product
`R ≅ ∏ factor n` of a family of sheaves of commutative rings, in the sense of
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`. Reading each `factor n` as a
sheaf of `R`-modules along the `n`-th projection
(`Stacks.SheafOfModules.RingSheafProductFactor.factorModule`), the structure sheaf `R` *is* the
product of the `factorModule hp n` in the category of sheaves of `R`-modules, the projections
being `Stacks.SheafOfModules.RingSheafProductFactor.factorProjection`.

The point is that the product is exhibited as a limit cone rather than compared with the
categorical product `∏ᶜ`: the universal property is checked on sections, where a product
presentation is by definition a bijection, and nothing about how a product of sheaves of modules
is computed is needed.

## Main definitions

* `Stacks.SheafOfModules.RingSheafProductFactor.liftSection`: the section of `R` whose family of
  components is a prescribed family of sections of the factors.
* `Stacks.SheafOfModules.RingSheafProductFactor.liftHom`: the morphism of sheaves of `R`-modules
  into `R` determined by a family of morphisms into the factors.
* `Stacks.SheafOfModules.RingSheafProductFactor.unitFan`: the fan with vertex `R` and projections
  `factorProjection`.
* `Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit`: the resulting isomorphism
  `∏_n factor n ≅ R` of sheaves of `R`-modules.

## Main results

* `Stacks.SheafOfModules.RingSheafProductFactor.isLimitUnitFan`: `unitFan` is a limit fan.
* `Stacks.SheafOfModules.RingSheafProductFactor.hasProduct_factorModule`: consequently the family
  of factors has a product, with no hypothesis on the ambient category of sheaves of modules.
* `Stacks.SheafOfModules.RingSheafProductFactor.piIsoUnit_inv_comp_π`: the isomorphism is the one
  identifying the product projections with `factorProjection`, which is what pins it down.

## Implementation notes

**Why the section-level steps are separate lemmas, and why linearity is split in two.** The
carrier of the sections of `Stacks.SheafOfModules.Tensor.ringSheaf R` over `U` receives its
`Ring` instance through `RingCat` while the same carrier read as the sections of `R` receives one
through `CommRingCat`, so a goal mentioning both spellings is not type-correct at `implicit`
transparency and no rewriting tactic acts on it; only a single `isDefEq` at default transparency
crosses it. Additivity, linearity and naturality are therefore three separate lemmas, each
costing one such crossing, and the component computation of a scalar multiple
(`app_liftSection_smul`) is split off from the linearity itself (`liftSection_smul`) so that
neither declaration pays for more than two. This is the same discipline, and for the same
reason, as in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorOrthogonal`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose proof uses the identification `∏_n 𝒪_n ≅ 𝒪_X`.
* `Mathlib.CategoryTheory.Limits.Shapes.Products`, for `CategoryTheory.Limits.Fan`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w t

namespace Stacks.SheafOfModules.RingSheafProductFactor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}
  {factor : ι → Sheaf J CommRingCat.{w}} {R : Sheaf J CommRingCat.{w}}

variable (hp : ProductPresentation R factor)
  {M : _root_.SheafOfModules.{w} (Tensor.ringSheaf R)} (f : ∀ n, M ⟶ factorModule hp n)

/-- The section of `R` whose `n`-th component is the image of a section `m` of `M` under the
`n`-th of a family of morphisms `M ⟶ factorModule hp n`. -/
def liftSection (U : Cᵒᵖ) (m : ↥(M.val.obj U)) : ↥(R.obj.obj U) :=
  (hp.surjective U fun n ↦ (f n).val.app U m).choose

/-- The `n`-th component of `liftSection hp f U m` is the `n`-th prescribed section. -/
theorem app_liftSection (n : ι) (U : Cᵒᵖ) (m : ↥(M.val.obj U)) :
    (hp.π n).hom.app U (liftSection hp f U m) = (f n).val.app U m :=
  (hp.surjective U fun n ↦ (f n).val.app U m).choose_spec n

/-- The `k`-th component of the image of a sum. -/
theorem app_liftSection_add (k : ι) (U : Cᵒᵖ) (m m' : ↥(M.val.obj U)) :
    (hp.π k).hom.app U (liftSection hp f U (m + m'))
      = (hp.π k).hom.app U (liftSection hp f U m)
        + (hp.π k).hom.app U (liftSection hp f U m') :=
  ((app_liftSection hp f k U (m + m')).trans (((f k).val.app U).hom.map_add m m')).trans
    (congrArg₂ (· + ·) (app_liftSection hp f k U m).symm (app_liftSection hp f k U m').symm)

/-- `liftSection hp f U` is additive. -/
theorem liftSection_add (U : Cᵒᵖ) (m m' : ↥(M.val.obj U)) :
    liftSection hp f U (m + m') = liftSection hp f U m + liftSection hp f U m' :=
  hp.injective fun k ↦ (app_liftSection_add hp f k U m m').trans
    (hp.app_add k U (liftSection hp f U m) (liftSection hp f U m')).symm

/-- The `k`-th component of the image of a scalar multiple. -/
theorem app_liftSection_smul (k : ι) (U : Cᵒᵖ) (r : ↥(R.obj.obj U)) (m : ↥(M.val.obj U)) :
    (hp.π k).hom.app U
        (liftSection hp f U ((show ↥((Tensor.ringSheaf R).obj.obj U) from r) • m))
      = (hp.π k).hom.app U r * (hp.π k).hom.app U (liftSection hp f U m) :=
  ((app_liftSection hp f k U _).trans (((f k).val.app U).hom.map_smul r m)).trans
    (congrArg (fun z : ↥((factor k).obj.obj U) ↦ (hp.π k).hom.app U r * z)
      (app_liftSection hp f k U m).symm)

/-- `liftSection hp f U` is `R`-linear, the action on `M` being the one it carries as a sheaf of
`R`-modules. -/
theorem liftSection_smul (U : Cᵒᵖ) (r : ↥(R.obj.obj U)) (m : ↥(M.val.obj U)) :
    liftSection hp f U ((show ↥((Tensor.ringSheaf R).obj.obj U) from r) • m)
      = r * liftSection hp f U m :=
  hp.injective fun k ↦ (app_liftSection_smul hp f k U r m).trans
    (hp.app_mul k U r (liftSection hp f U m)).symm

/-- The `k`-th component of the image of a restricted section. -/
theorem app_map_liftSection (k : ι) {U V : Cᵒᵖ} (g : U ⟶ V) (m : ↥(M.val.obj U)) :
    (hp.π k).hom.app V (liftSection hp f V (M.val.map g m))
      = (factor k).obj.map g ((hp.π k).hom.app U (liftSection hp f U m)) :=
  ((app_liftSection hp f k V _).trans
      (PresheafOfModules.naturality_apply (f k).val g m)).trans
    (congrArg (fun z : ↥((factor k).obj.obj U) ↦ (factor k).obj.map g z)
      (app_liftSection hp f k U m).symm)

/-- `liftSection hp f` is compatible with the restriction maps of the sheaves. -/
theorem map_liftSection {U V : Cᵒᵖ} (g : U ⟶ V) (m : ↥(M.val.obj U)) :
    liftSection hp f V (M.val.map g m) = R.obj.map g (liftSection hp f U m) :=
  hp.injective fun k ↦ (app_map_liftSection hp f k g m).trans
    (hp.app_map k g (liftSection hp f U m)).symm

/-- **The morphism of sheaves of `R`-modules into the structure sheaf determined by a family of
morphisms into the factors.** On sections it is `m ↦` the section of `R` with components the
images of `m`. -/
def liftHom : M ⟶ _root_.SheafOfModules.unit (Tensor.ringSheaf R) where
  val :=
    { app := fun U ↦ ConcreteCategory.ofHom
        { toFun := liftSection hp f U
          map_add' := liftSection_add hp f U
          map_smul' := fun r m ↦ liftSection_smul hp f U r m }
      naturality := fun {U V} g ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
        exact map_liftSection hp f g m }

/-- `liftHom` followed by the `n`-th projection is the `n`-th prescribed morphism. -/
theorem liftHom_comp_factorProjection (n : ι) :
    liftHom hp f ≫ factorProjection hp n = f n :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ app_liftSection hp f n U m))

/-- `liftHom` is the only morphism into the structure sheaf with the prescribed components. -/
theorem eq_liftHom (φ : M ⟶ _root_.SheafOfModules.unit (Tensor.ringSheaf R))
    (hφ : ∀ n, φ ≫ factorProjection hp n = f n) : φ = liftHom hp f :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ hp.injective fun k ↦ by
      refine Eq.trans ?_ (app_liftSection hp f k U m).symm
      exact congrArg (fun ψ : M ⟶ factorModule hp k ↦ ψ.val.app U m) (hφ k)))

/-- The fan with vertex the structure sheaf and projections
`Stacks.SheafOfModules.RingSheafProductFactor.factorProjection`. -/
def unitFan : Fan (factorModule hp) :=
  Fan.mk (_root_.SheafOfModules.unit (Tensor.ringSheaf R)) (factorProjection hp)

/-- **The structure sheaf is the product of the factors, as a sheaf of modules over itself.**
The universal property is the defining bijection of a product presentation, read on sections. -/
def isLimitUnitFan : IsLimit (unitFan hp) :=
  Fan.IsLimit.mk _ (fun s ↦ liftHom hp s.proj)
    (fun s n ↦ liftHom_comp_factorProjection hp s.proj n)
    (fun s φ hφ ↦ eq_liftHom hp s.proj φ hφ)

/-- The family of factors of a product presentation, read as sheaves of modules over the
structure sheaf, has a product: the structure sheaf itself. -/
theorem hasProduct_factorModule : HasProduct (factorModule hp) :=
  HasLimit.mk ⟨unitFan hp, isLimitUnitFan hp⟩

variable [HasProduct (factorModule hp)]

/-- **The product of the factors of a product presentation is the structure sheaf**, as an
isomorphism of sheaves of modules `∏_n factor n ≅ R`. -/
def piIsoUnit : (∏ᶜ factorModule hp) ≅ _root_.SheafOfModules.unit (Tensor.ringSheaf R) :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitUnitFan hp)

/-- The isomorphism `piIsoUnit` is the one carrying the `n`-th product projection to the `n`-th
projection `factorProjection`. This pins it down. -/
@[reassoc]
theorem piIsoUnit_inv_comp_π (n : ι) :
    (piIsoUnit hp).inv ≫ Pi.π (factorModule hp) n = factorProjection hp n :=
  (limit.isLimit _).conePointUniqueUpToIso_inv_comp (isLimitUnitFan hp) ⟨n⟩

end Stacks.SheafOfModules.RingSheafProductFactor

end
