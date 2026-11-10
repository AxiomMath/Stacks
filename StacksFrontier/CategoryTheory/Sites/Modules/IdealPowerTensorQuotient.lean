module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# `ℱ ⊗_𝒪 𝒪/ℐⁿ` is `ℱ/ℐⁿℱ`, for an arbitrary sheaf of modules

Let `(C, 𝒪)` be a ringed site, `ℐ ⊆ 𝒪` a sheaf of ideals and `ℱ` an arbitrary sheaf of
`𝒪`-modules. Tensoring the presentation `ℐ ⟶ 𝒪 ⟶ 𝒪/ℐ` of `𝒪/ℐ` with `ℱ` and using the unit
law `ℱ ⊗_𝒪 𝒪 ≅ ℱ` presents `ℱ ⊗_𝒪 𝒪/ℐ` as the cokernel of a multiplication map
`ℱ ⊗_𝒪 ℐ ⟶ ℱ`, whose image is the submodule `ℐℱ`. So `ℱ ⊗_𝒪 𝒪/ℐ` is the quotient `ℱ/ℐℱ`,
compatibly with the two canonical maps out of `ℱ`. No flatness is needed: this is right
exactness of the tensor product, which is Tag 05NB.

Applied to the powers of `ℐ` this identifies the `n`-th term `ℱ ⊗_𝒪 𝒪/ℐⁿ` of the reduction
tower with the `n`-th term `ℱ/ℐⁿℱ` of the adic filtration quotient tower, compatibly with the
transition maps of both towers.

## Main definitions

* `Stacks.Sites.tensorSmulMap`: for `g : 𝒢 ⟶ 𝒪`, the map `ℱ ⊗_𝒪 𝒢 ⟶ ℱ ⊗_𝒪 𝒪 ≅ ℱ`.
* `Stacks.Sites.idealTensorSmulMap`: the multiplication map `ℱ ⊗_𝒪 ℐ ⟶ ℱ`, the case `g = ℐ ⟶ 𝒪`.
* `Stacks.Sites.idealSmulQuotient` and `Stacks.Sites.idealSmulQuotientπ`: **the quotient
  `ℱ/ℐℱ`** and its projection from `ℱ`.
* `Stacks.Sites.idealSmulQuotientMap`: the transition map `ℱ/𝒥ℱ ⟶ ℱ/ℐℱ` for `𝒥 ⊆ ℐ`.
* `Stacks.Sites.tensorIdealQuotientUnit` and `Stacks.Sites.adicQuotientTensorUnit`: the
  canonical maps `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐ` and `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐⁿ` obtained by tensoring the unit.
* `Stacks.Sites.tensorIdealQuotientIso`: **`ℱ ⊗_𝒪 𝒪/ℐ ≅ ℱ/ℐℱ`.**
* `Stacks.Sites.tensorAdicQuotientModuleIso`: **`ℱ ⊗_𝒪 𝒪/ℐⁿ ≅ ℱ/ℐⁿℱ`**, the same at the `n`-th
  power, written against `Stacks.Sites.adicQuotientModule`.

## Main results

* `Stacks.Sites.tensorSmulMap_unit_tmul`: on the pure tensor `x ⊗ a`, the multiplication map is
  `g(a) · x`.
* `Stacks.Sites.imageSubmodule_idealTensorSmulMap`: **the image of `ℱ ⊗_𝒪 ℐ ⟶ ℱ` is `ℐℱ`.**
* `Stacks.Sites.tensorIdealQuotientUnit_comp_tensorIdealQuotientIso_hom` and
  `Stacks.Sites.adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom`: **the
  identification is compatible with the two canonical maps out of `ℱ`** — tensoring the
  projection `𝒪 ⟶ 𝒪/ℐⁿ` with `ℱ` and then applying it is the projection `ℱ ⟶ ℱ/ℐⁿℱ`.
* `Stacks.Sites.tensorAdicQuotientModuleIso_hom_naturality`: **the identification is compatible
  with the transition maps of the two towers.**
* `Stacks.Sites.epi_tensorIdealQuotientUnit`: the canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐ` is an
  epimorphism.

## Implementation notes

`ℐℱ` is `Stacks.Sites.idealSmul ℐ (⊤ : ℱ.Submodule)`, the smallest submodule with local
membership containing every objectwise product of a section of `ℐ` with a section of `ℱ`; at the
`n`-th power it is `Stacks.Sites.idealPowSmul ℐ n ⊤` on the nose, that abbreviation being
`idealSmul (idealPow ℐ n)`. Both inclusions of
`Stacks.Sites.imageSubmodule_idealTensorSmulMap` go through the formula for the multiplication
map on a pure tensor: a section of `ℱ ⊗_𝒪 ℐ` is only *locally* a sum of pure tensors, the tensor
product of sheaves of modules being the sheafification of the objectwise one, and both `ℐℱ` and
the image subsheaf are defined by local membership, so neither inclusion is objectwise.

The quotient is formed in `Mod(𝒪)`, as the cokernel of the inclusion of a submodule, exactly as
`Stacks.Sites.adicQuotientModule` is; that keeps both towers inside one abelian category.
Because `adicQuotientModule ℐ n` is by definition the cokernel of `ℐⁿ ⟶ 𝒪`, the results at the
`n`-th power are the general ones with `ℐ` replaced by `idealPow ℐ n` — but
`Stacks.Sites.idealPow` leaves its sheaf of rings implicit and does not determine it from the
expected type here, so every such application pins it with `(O := X.O)`.

Right exactness enters as `Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj`,
installed as a section-local instance rather than restated: the global instance of
`StacksFrontier/CategoryTheory/Sites/Modules/FlatTensorShortExact.lean` is pinned to a small site
with sections in the same universe, which a ringed site with an independent sections universe
does not satisfy.

Not to be confused with `AlgebraicGeometry.Space.SiteAdicCohomology.adicQuotient`
(`StacksFrontier/AlgebraicGeometry/Spaces/FormalFunctionsAdicLimit.lean`), which is the quotient of
a sheaf of modules by an ideal of its *global sections* rather than by a sheaf of ideals, and is
a different object.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open TensorProduct

universe u v w

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
  Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj

/- The global instance `SheafOfModules.preservesColimitsOfSize_sheafTensor_obj` is stated for
sheaves of modules with sections in the universe `max u v w` of the ambient site; tried against
the sections universe `w` of a ringed site it leaves a stuck universe constraint. Right exactness
is supplied here by the local instance above instead. -/
attribute [-instance] SheafOfModules.preservesColimitsOfSize_sheafTensor_obj

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The unit of the sheafification of the objectwise tensor product of two sheaves of
modules. -/
abbrev tensorSheafifyUnit (F G : Modules.{u, v, w} X) :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
    (PresheafOfModules.tensorObj (O := X.O.obj) F.val G.val)

/-- The multiplication map `ℱ ⊗_𝒪 𝒢 ⟶ ℱ` attached to a morphism `g : 𝒢 ⟶ 𝒪`: tensor `g` into
the second variable and read the target through the unit law `ℱ ⊗_𝒪 𝒪 ≅ ℱ`. -/
abbrev tensorSmulMap (F : Modules.{u, v, w} X) {G : Modules.{u, v, w} X}
    (g : G ⟶ _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G ⟶ F :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map g ≫
    (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).hom

/-- **On a pure tensor `x ⊗ a`, the multiplication map is `g(a) · x`.** Both the tensor product
and its unit law are sheafifications of objectwise constructions, so the value on the image of
the sheafification unit is computed by the naturality of that unit together with the objectwise
right unitor `x ⊗ r ↦ r · x`. -/
theorem tensorSmulMap_unit_tmul (F : Modules.{u, v, w} X) {G : Modules.{u, v, w} X}
    (g : G ⟶ _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (V : X.Cᵒᵖ)
    (x : F.val.obj V) (a : G.val.obj V) :
    (tensorSmulMap F g).val.app V
        ((tensorSheafifyUnit F G).app V
          (x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V] a)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V from g.val.app V a) • x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let Sh := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  have h1 : (Sh.map (PresheafOfModules.tensorHom (O := X.O.obj) (𝟙 F.val) g.val)).val.app V
        ((adj.unit.app (PresheafOfModules.tensorObj (O := X.O.obj) F.val G.val)).app V (x ⊗ₜ a)) =
      (adj.unit.app (PresheafOfModules.tensorObj (O := X.O.obj) F.val
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val)).app V
          (x ⊗ₜ g.val.app V a) :=
    (congrArg (fun ψ ↦ ψ.app V (x ⊗ₜ a))
      (adj.unit.naturality (PresheafOfModules.tensorHom (O := X.O.obj) (𝟙 F.val) g.val))).symm
  have h2 : (Sh.map (ρ_ F.val).hom).val.app V
        ((adj.unit.app (PresheafOfModules.tensorObj (O := X.O.obj) F.val
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val)).app V
            (x ⊗ₜ g.val.app V a)) =
      (adj.unit.app F.val).app V ((ρ_ F.val).hom.app V (x ⊗ₜ g.val.app V a)) :=
    (congrArg (fun ψ ↦ ψ.app V (x ⊗ₜ g.val.app V a))
      (adj.unit.naturality (ρ_ F.val).hom)).symm
  have h3 : (adj.counit.app F).val.app V
        ((adj.unit.app F.val).app V ((ρ_ F.val).hom.app V (x ⊗ₜ g.val.app V a))) =
      (ρ_ F.val).hom.app V (x ⊗ₜ g.val.app V a) :=
    congrArg (fun ψ ↦ ψ.app V ((ρ_ F.val).hom.app V (x ⊗ₜ g.val.app V a)))
      (adj.right_triangle_components F)
  change (adj.counit.app F).val.app V ((Sh.map (ρ_ F.val).hom).val.app V
    ((Sh.map (PresheafOfModules.tensorHom (O := X.O.obj) (𝟙 F.val) g.val)).val.app V
      ((adj.unit.app (PresheafOfModules.tensorObj (O := X.O.obj) F.val G.val)).app V
        (x ⊗ₜ a)))) = _
  rw [h1, h2, h3]
  exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply x _

/-! ### The image of the multiplication map is `ℐℱ` -/

section Ideal

variable (F : Modules.{u, v, w} X) (I : IdealSubsheaf.{v, u, w} X.O)

/-- The multiplication map `ℱ ⊗_𝒪 ℐ ⟶ ℱ` of a sheaf of ideals: the map `ℱ ⊗_𝒪 ℐ ⟶ ℱ ⊗_𝒪 𝒪 ≅ ℱ`
induced by the inclusion `ℐ ⟶ 𝒪`. -/
abbrev idealTensorSmulMap :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj I.toSheafOfModules ⟶ F :=
  tensorSmulMap F I.ι

/-- On the image under the sheafification unit of an element of the objectwise tensor product,
the multiplication map takes values in the objectwise product `ℐ · ℱ`: on a pure tensor `x ⊗ a`
its value is `a · x`. -/
theorem idealTensorSmulMap_unit_mem_presheafIdealSmul (V : X.Cᵒᵖ)
    (u : ((PresheafOfModules.tensorObj (O := X.O.obj) F.val)
      I.toSheafOfModules.val).obj V) :
    (idealTensorSmulMap F I).val.app V ((tensorSheafifyUnit F I.toSheafOfModules).app V u) ∈
      (presheafIdealSmul I (⊤ : F.Submodule).toSubmodule).obj V := by
  induction u using TensorProduct.inductionOn with
  | add p q hp hq =>
    refine Eq.mpr (congrArg (· ∈ (presheafIdealSmul I (⊤ : F.Submodule).toSubmodule).obj V)
      ((congrArg (ConcreteCategory.hom ((idealTensorSmulMap F I).val.app V))
          (map_add (ConcreteCategory.hom
            ((tensorSheafifyUnit F I.toSheafOfModules).app V)) p q)).trans
        (map_add (ConcreteCategory.hom ((idealTensorSmulMap F I).val.app V)) _ _)))
      (add_mem hp hq)
  | tmul x a =>
    refine Eq.mpr (congrArg (· ∈ (presheafIdealSmul I (⊤ : F.Submodule).toSubmodule).obj V)
      (tensorSmulMap_unit_tmul F I.ι V x a)) ?_
    refine smul_mem_presheafIdealSmul I a.2 ?_
    rw [Stacks.SheafOfModules.toSubmodule_top]
    exact _root_.Submodule.mem_top

/-- **The multiplication map `ℱ ⊗_𝒪 ℐ ⟶ ℱ` takes values in `ℐℱ`.** A section of the tensor
product is, after restriction along the arrows of a covering sieve, the image of an element of
the objectwise tensor product, where the value is an objectwise product; membership in `ℐℱ` is
a local condition. -/
theorem idealTensorSmulMap_mem_idealSmul (V : X.Cᵒᵖ)
    (t : (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj
      I.toSheafOfModules).val.obj V) :
    (idealTensorSmulMap F I).val.app V t ∈ (idealSmul I (⊤ : F.Submodule)).obj V := by
  have : Presheaf.IsLocallySurjective X.J ((PresheafOfModules.toPresheaf _).map
      (tensorSheafifyUnit F I.toSheafOfModules)) := by
    change Presheaf.IsLocallySurjective X.J (CategoryTheory.toSheafify X.J _)
    infer_instance
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem
    (Presheaf.imageSieve_mem X.J ((PresheafOfModules.toPresheaf _).map
      (tensorSheafifyUnit F I.toSheafOfModules)) t) ?_
  rintro Y f ⟨u, hu⟩
  have hnat := PresheafOfModules.naturality_apply (idealTensorSmulMap F I).val f.op t
  exact (hnat.symm.trans (congrArg _ hu.symm)) ▸
    idealTensorSmulMap_unit_mem_presheafIdealSmul F I (op Y) u

/-- `ℱ ⊗_𝒪 ℐ ⟶ ℱ` composed with the projection onto `ℱ/ℐℱ` vanishes. -/
@[reassoc]
theorem idealTensorSmulMap_comp_cokernelπ :
    idealTensorSmulMap F I ≫ cokernel.π (idealSmul I (⊤ : F.Submodule)).ι = 0 := by
  refine (_root_.SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_))
  exact Stacks.SheafOfModules.val_app_apply_eq_zero (idealSmul I (⊤ : F.Submodule)).ι
    (cokernel.π _) (cokernel.condition _) V
    ⟨_, idealTensorSmulMap_mem_idealSmul F I V t⟩

/-- **The image of the multiplication map `ℱ ⊗_𝒪 ℐ ⟶ ℱ` is the product `ℐℱ`.** One inclusion is
that the map takes values in `ℐℱ`; the other is that an objectwise product `a · x` is the value
of the pure tensor `x ⊗ a`, so it lies in the range, and `ℐℱ` is generated by such products
under local membership. -/
theorem imageSubmodule_idealTensorSmulMap :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (idealTensorSmulMap F I) =
      idealSmul I (⊤ : F.Submodule) := by
  refine le_antisymm
    ((Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le_iff _).2
      (idealTensorSmulMap_mem_idealSmul F I))
    (Stacks.SheafOfModules.sheafifySubmodule_le (presheafIdealSmul_le I ?_))
  intro V a ha m _
  refine Eq.mpr (congrArg
    (· ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      (idealTensorSmulMap F I)).toSubmodule.obj V)
    (tensorSmulMap_unit_tmul F I.ι V m ⟨a, ha⟩).symm) ?_
  exact Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule _ _

/-- The image subsheaf of the multiplication map dies in its cokernel: the factorisation of a
morphism through its image is an epimorphism. -/
@[reassoc]
theorem imageSubmodule_ι_comp_cokernelπ_idealTensorSmulMap :
    (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (idealTensorSmulMap F I)).ι ≫
      cokernel.π (idealTensorSmulMap F I) = 0 := by
  rw [← cancel_epi (Stacks.SheafOfModules.ImageSubsheaf.toImage (idealTensorSmulMap F I)),
    comp_zero, ← Category.assoc, Stacks.SheafOfModules.ImageSubsheaf.toImage_ι,
    cokernel.condition]

/-- **`ℐℱ` dies in `coker(ℱ ⊗_𝒪 ℐ ⟶ ℱ)`**, being the image of the multiplication map. -/
@[reassoc]
theorem idealSmul_ι_comp_cokernelπ_idealTensorSmulMap :
    (idealSmul I (⊤ : F.Submodule)).ι ≫ cokernel.π (idealTensorSmulMap F I) = 0 := by
  rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι
      (le_of_eq (imageSubmodule_idealTensorSmulMap F I).symm),
    Category.assoc, imageSubmodule_ι_comp_cokernelπ_idealTensorSmulMap, comp_zero]

/-! ### The quotient `ℱ/ℐℱ` and its identification with `ℱ ⊗_𝒪 𝒪/ℐ` -/

/-- **The quotient `ℱ/ℐℱ`** of a sheaf of modules by the product of a sheaf of ideals with it:
the cokernel, in sheaves of `𝒪`-modules, of the inclusion of `ℐℱ` into `ℱ`. -/
abbrev idealSmulQuotient : Modules.{u, v, w} X :=
  cokernel (idealSmul I (⊤ : F.Submodule)).ι

/-- The projection `ℱ ⟶ ℱ/ℐℱ`. -/
abbrev idealSmulQuotientπ : F ⟶ idealSmulQuotient F I :=
  cokernel.π (idealSmul I (⊤ : F.Submodule)).ι

/-- **The canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐ`**: tensor the projection `𝒪 ⟶ 𝒪/ℐ` with `ℱ` and read
the source through `ℱ ⊗_𝒪 𝒪 ≅ ℱ`. -/
def tensorIdealQuotientUnit :
    F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj (cokernel I.ι) :=
  (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map (cokernel.π I.ι)

/-- `coker(ℱ ⊗_𝒪 ℐ ⟶ ℱ)` is `ℱ/ℐℱ`: the two cokernels are taken of two morphisms with the same
image, namely `ℐℱ`. -/
def cokernelIdealTensorSmulMapIso :
    cokernel (idealTensorSmulMap F I) ≅ idealSmulQuotient F I where
  hom := cokernel.desc _ (idealSmulQuotientπ F I) (idealTensorSmulMap_comp_cokernelπ F I)
  inv := cokernel.desc _ (cokernel.π (idealTensorSmulMap F I))
    (idealSmul_ι_comp_cokernelπ_idealTensorSmulMap F I)
  hom_inv_id := by
    rw [← cancel_epi (cokernel.π (idealTensorSmulMap F I)), cokernel.π_desc_assoc,
      cokernel.π_desc, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi (idealSmulQuotientπ F I), cokernel.π_desc_assoc, cokernel.π_desc,
      Category.comp_id]

/-- **`ℱ ⊗_𝒪 𝒪/ℐ ≅ ℱ/ℐℱ`.** Tensoring with `ℱ` is right exact, so it carries the presentation
`ℐ ⟶ 𝒪 ⟶ 𝒪/ℐ` of `𝒪/ℐ` to a presentation of `ℱ ⊗_𝒪 𝒪/ℐ`; the image of `ℱ ⊗_𝒪 ℐ ⟶ ℱ` is
`ℐℱ`. -/
def tensorIdealQuotientIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj (cokernel I.ι) ≅
      idealSmulQuotient F I :=
  PreservesCokernel.iso ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F) I.ι ≪≫
    (cokernelCompIsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map I.ι)
      (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).hom).symm ≪≫
    cokernelIdealTensorSmulMapIso F I

/-- **The identification `ℱ ⊗_𝒪 𝒪/ℐ ≅ ℱ/ℐℱ` is compatible with the two canonical maps out of
`ℱ`:** the map obtained by tensoring the projection `𝒪 ⟶ 𝒪/ℐ` with `ℱ`, followed by the
identification, is the projection `ℱ ⟶ ℱ/ℐℱ`. -/
@[reassoc (attr := simp)]
theorem tensorIdealQuotientUnit_comp_tensorIdealQuotientIso_hom :
    tensorIdealQuotientUnit F I ≫ (tensorIdealQuotientIso F I).hom =
      idealSmulQuotientπ F I := by
  rw [tensorIdealQuotientUnit, tensorIdealQuotientIso, Iso.trans_hom, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, PreservesCokernel.π_iso_hom_assoc, cokernelCompIsIso_inv,
    cokernel.π_desc_assoc, Category.assoc, Iso.inv_hom_id_assoc]
  exact cokernel.π_desc _ _ _

/-- The canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐ` is an epimorphism: through the identification it is the
projection onto `ℱ/ℐℱ`. -/
instance epi_tensorIdealQuotientUnit : Epi (tensorIdealQuotientUnit F I) := by
  have h : tensorIdealQuotientUnit F I =
      idealSmulQuotientπ F I ≫ (tensorIdealQuotientIso F I).inv := by
    rw [← tensorIdealQuotientUnit_comp_tensorIdealQuotientIso_hom F I, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

end Ideal

/-! ### The tower of quotients `ℱ/ℐⁿℱ` -/

section Tower

variable (F : Modules.{u, v, w} X)

/-- The transition map `ℱ/𝒥ℱ ⟶ ℱ/ℐℱ` for `𝒥 ⊆ ℐ`: the projection onto the larger quotient
kills `𝒥ℱ`, since `𝒥ℱ ⊆ ℐℱ`. -/
def idealSmulQuotientMap {I J : IdealSubsheaf.{v, u, w} X.O} (h : J ≤ I) :
    idealSmulQuotient F J ⟶ idealSmulQuotient F I :=
  cokernel.desc _ (idealSmulQuotientπ F I) (by
    rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι
        (idealSmul_mono_left h (⊤ : F.Submodule)),
      Category.assoc, cokernel.condition, comp_zero])

/-- The transition maps of the tower of quotients are compatible with the projections
from `ℱ`. -/
@[reassoc (attr := simp)]
lemma idealSmulQuotientπ_comp_idealSmulQuotientMap {I J : IdealSubsheaf.{v, u, w} X.O}
    (h : J ≤ I) :
    idealSmulQuotientπ F J ≫ idealSmulQuotientMap F h = idealSmulQuotientπ F I :=
  cokernel.π_desc _ _ _

variable (I : IdealSubsheaf.{v, u, w} X.O)

/-- **The canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐⁿ`**, obtained by tensoring the projection
`𝒪 ⟶ 𝒪/ℐⁿ` with `ℱ`. -/
def adicQuotientTensorUnit (n : ℕ) :
    F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj (adicQuotientModule I n) :=
  (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections X.O F).inv ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map (adicQuotientModuleπ I n)

/-- **`ℱ ⊗_𝒪 𝒪/ℐⁿ ≅ ℱ/ℐⁿℱ`**, the identification of the `n`-th term of the reduction tower of
`ℱ` with the `n`-th term of its adic filtration quotient tower. -/
def tensorAdicQuotientModuleIso (n : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj (adicQuotientModule I n) ≅
      idealSmulQuotient F (Stacks.Sites.idealPow (O := X.O) I n) :=
  tensorIdealQuotientIso F (Stacks.Sites.idealPow (O := X.O) I n)

/-- **The identification `ℱ ⊗_𝒪 𝒪/ℐⁿ ≅ ℱ/ℐⁿℱ` is compatible with the two canonical maps out of
`ℱ`:** tensoring the projection `𝒪 ⟶ 𝒪/ℐⁿ` with `ℱ` and then applying the identification is the
projection `ℱ ⟶ ℱ/ℐⁿℱ`. -/
@[reassoc (attr := simp)]
theorem adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom (n : ℕ) :
    adicQuotientTensorUnit F I n ≫ (tensorAdicQuotientModuleIso F I n).hom =
      idealSmulQuotientπ F (Stacks.Sites.idealPow (O := X.O) I n) :=
  tensorIdealQuotientUnit_comp_tensorIdealQuotientIso_hom F
    (Stacks.Sites.idealPow (O := X.O) I n)

/-- The canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐⁿ` is an epimorphism. -/
instance epi_adicQuotientTensorUnit (n : ℕ) : Epi (adicQuotientTensorUnit F I n) := by
  have h : adicQuotientTensorUnit F I n =
      idealSmulQuotientπ F (Stacks.Sites.idealPow (O := X.O) I n) ≫
        (tensorAdicQuotientModuleIso F I n).inv := by
    rw [← adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom F I n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- Tensoring the transition map of the tower `n ↦ 𝒪/ℐⁿ` with `ℱ` is compatible with the
canonical maps out of `ℱ`. -/
@[reassoc]
lemma adicQuotientTensorUnit_comp_map_adicQuotientModuleMap {m n : ℕ} (h : m ≤ n) :
    adicQuotientTensorUnit F I n ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map (adicQuotientModuleMap I h) =
      adicQuotientTensorUnit F I m := by
  rw [adicQuotientTensorUnit, adicQuotientTensorUnit, Category.assoc, ← Functor.map_comp,
    adicQuotientModuleπ_comp_adicQuotientModuleMap]

/-- **The identification `ℱ ⊗_𝒪 𝒪/ℐⁿ ≅ ℱ/ℐⁿℱ` is compatible with the transition maps of the two
towers.** Both sides agree after precomposition with the canonical map `ℱ ⟶ ℱ ⊗_𝒪 𝒪/ℐⁿ`, which
is an epimorphism, because both are then the projection `ℱ ⟶ ℱ/ℐᵐℱ`. -/
@[reassoc]
theorem tensorAdicQuotientModuleIso_hom_naturality {m n : ℕ} (h : m ≤ n) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).map (adicQuotientModuleMap I h) ≫
        (tensorAdicQuotientModuleIso F I m).hom =
      (tensorAdicQuotientModuleIso F I n).hom ≫
        idealSmulQuotientMap F (Stacks.Sites.idealPow_antitone (O := X.O) I h) := by
  rw [← cancel_epi (adicQuotientTensorUnit F I n),
    adicQuotientTensorUnit_comp_map_adicQuotientModuleMap_assoc,
    adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom,
    adicQuotientTensorUnit_comp_tensorAdicQuotientModuleIso_hom_assoc,
    idealSmulQuotientπ_comp_idealSmulQuotientMap]

end Tower

end Stacks.Sites

end
