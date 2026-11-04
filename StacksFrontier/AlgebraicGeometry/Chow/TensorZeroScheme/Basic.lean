module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Composite

/-!
# The zero scheme of a section of a tensor product of two invertible modules

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. [Stacks, Tag 0F97] produces a
scheme `L` over `Y` carrying two sections `s₁` of `p^*L₁` and `s₂` of `p^*L₂` whose product is
`p^*s`, and whose two zero schemes `D₁`, `D₂` are line bundles over `D`.

Here `L` is the zero scheme, inside the fibre product `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the
two line bundles of [Stacks, Tag 01M2], of the equation `z₁ ⊗ z₂ - q^*s` in the two fibre
coordinates, and conditions (1) and (3) of the tag are proved for it.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.totalSpace`: the fibre product
  `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})`, with `totalProj` its structure morphism `q` to `Y`.
* `Stacks.Chow.TensorZeroScheme.coord₁` and `coord₂`: the two fibre coordinates `z₁`, `z₂`, as
  global sections of `q^*L₁` and `q^*L₂`.
* `Stacks.Chow.TensorZeroScheme.equation`: the equation `z₁ ⊗ z₂ - q^*s`.
* `Stacks.Chow.TensorZeroScheme.spaceIdeal`: the scheme `L`, as the quasi-coherent ideal sheaf of
  the zero scheme of that equation; `spaceι` is the closed immersion
  `ι : L ⟶ Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` and `proj` the composite `p = ι ≫ q`.
* `Stacks.Chow.TensorZeroScheme.section₁` and `section₂`: the sections `s₁`, `s₂` of `p^*L₁` and
  `p^*L₂`, the two fibre coordinates restricted to `L`.
* `Stacks.Chow.TensorZeroScheme.branch₁` and `branch₂`: the two branches `D₁`, `D₂`, the zero
  schemes of `s₁` and of `s₂`.

## Main results

* `Stacks.Chow.TensorZeroScheme.pullbackTensorSection_proj`: `p^*s = s₁ ⊗ s₂`.
* `Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme` and `branch₂_eq_zeroScheme`: `Dᵢ` is the
  zero scheme of `sᵢ`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.LineBundle (lineBundleProj lineBundlePullback fibreCoordinate)
open Stacks.PullbackTensorIso (pullbackCompHom pullbackTensorSection)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-- The tensor product of two invertible modules on a scheme is invertible. -/
instance isInvertible_tensorSheaf :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
        (Y.ringCatSheaf.property)⟩).obj (L₁)).obj (L₂))) := by
  change AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
      (Y.ringCatSheaf.property)⟩).obj (L₁))).obj L₂)
  exact Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.sheaf.obj
    Y.ringCatSheaf.property L₁ L₂

/-- Transport of the pullback of a module along an equality of morphisms. -/
def pullbackCongrHom {W V : Scheme.{u}} {m m' : W ⟶ V} (h : m = m') (M : V.Modules) :
    (Scheme.Modules.pullback m).obj M ⟶ (Scheme.Modules.pullback m').obj M :=
  eqToHom (congrArg (fun k : W ⟶ V => (Scheme.Modules.pullback k).obj M) h)

include h₁ h₂ in
/-- The fibre product `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line bundles. -/
def totalSpace : Scheme.{u} :=
  Limits.pullback (lineBundleProj Y L₁) (lineBundleProj Y L₂)

include h₁ h₂ in
/-- The projection of the fibre product to the first line bundle. -/
def firstProj : totalSpace Y L₁ L₂ ⟶ Stacks.LineBundle.lineBundleSpace Y L₁ :=
  Limits.pullback.fst _ _

include h₁ h₂ in
/-- The projection of the fibre product to the second line bundle. -/
def secondProj : totalSpace Y L₁ L₂ ⟶ Stacks.LineBundle.lineBundleSpace Y L₂ :=
  Limits.pullback.snd _ _

include h₁ h₂ in
/-- The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y`. -/
def totalProj : totalSpace Y L₁ L₂ ⟶ Y :=
  firstProj Y L₁ L₂ ≫ lineBundleProj Y L₁

include h₁ h₂ in
/-- The second projection, followed by the second line bundle's structure morphism, is the
structure morphism of the fibre product. -/
theorem secondProj_comp :
    secondProj Y L₁ L₂ ≫ lineBundleProj Y L₂ = totalProj Y L₁ L₂ :=
  Limits.pullback.condition.symm

include h₁ h₂ in
/-- The first fibre coordinate `z₁` on the fibre product, as a global section of `q^*L₁`. -/
def coord₁ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁, ⊤) :=
  PresheafOfModules.Hom.app
    (pullbackCompHom (firstProj Y L₁ L₂) (lineBundleProj Y L₁) L₁).val (op ⊤)
    (pullbackGlobalSections (firstProj Y L₁ L₂) (lineBundlePullback Y L₁) (fibreCoordinate Y L₁))

include h₁ h₂ in
/-- The second fibre coordinate `z₂`, as a global section of the pullback of `L₂` along the
second projection followed by the second line bundle's structure morphism. -/
def coord₂Pre : Γ((Scheme.Modules.pullback
    (secondProj Y L₁ L₂ ≫ lineBundleProj Y L₂)).obj L₂, ⊤) :=
  PresheafOfModules.Hom.app
    (pullbackCompHom (secondProj Y L₁ L₂) (lineBundleProj Y L₂) L₂).val (op ⊤)
    (pullbackGlobalSections (secondProj Y L₁ L₂) (lineBundlePullback Y L₂)
      (fibreCoordinate Y L₂))

include h₁ h₂ in
/-- The second fibre coordinate `z₂`, transported into the pullback of `L₂` along a morphism `m`
equal to the second projection followed by the second line bundle's structure morphism. -/
def coord₂Of {m : totalSpace Y L₁ L₂ ⟶ Y}
    (hm : secondProj Y L₁ L₂ ≫ lineBundleProj Y L₂ = m) :
    Γ((Scheme.Modules.pullback m).obj L₂, ⊤) :=
  PresheafOfModules.Hom.app (pullbackCongrHom hm L₂).val (op ⊤) (coord₂Pre Y L₁ L₂)

include h₁ h₂ in
/-- The second fibre coordinate `z₂` on the fibre product, as a global section of `q^*L₂`. -/
def coord₂ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂, ⊤) :=
  coord₂Of Y L₁ L₂ (secondProj_comp Y L₁ L₂)

variable (s : Γ((((Stacks.SheafOfModules.Tensor.sheafTensor
  ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
  (Y.ringCatSheaf.property)⟩).obj (L₁)).obj (L₂)), ⊤))

include h₁ h₂ in
/-- The product `z₁ ⊗ z₂` of the two fibre coordinates, a global section of `q^*L₁ ⊗ q^*L₂`. -/
def coordProduct :
    Γ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(totalSpace Y L₁ L₂).sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ ((totalSpace Y L₁ L₂).sheaf.obj)
      (forget₂ CommRingCat RingCat) ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂))), ⊤) :=
  tensorSectionsAt (totalSpace Y L₁ L₂).sheaf.obj
    (totalSpace Y L₁ L₂).ringCatSheaf.property (op ⊤)
    ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
    ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
    (coord₁ Y L₁ L₂) (coord₂ Y L₁ L₂)

include h₁ h₂ in
/-- The section `z₁ ⊗ z₂ - q^*s` of `q^*L₁ ⊗ q^*L₂` on the fibre product. -/
def equation :
    Γ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(totalSpace Y L₁ L₂).sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ ((totalSpace Y L₁ L₂).sheaf.obj)
      (forget₂ CommRingCat RingCat) ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂))), ⊤) :=
  coordProduct Y L₁ L₂ - pullbackTensorSection (totalProj Y L₁ L₂) L₁ L₂ s

include h₁ h₂ in
/-- The scheme `L`: the zero scheme of `z₁ ⊗ z₂ - q^*s` in the fibre product, as a
quasi-coherent ideal sheaf. -/
def spaceIdeal : (totalSpace Y L₁ L₂).IdealSheafData :=
  Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(totalSpace Y L₁ L₂).sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ ((totalSpace Y L₁ L₂).sheaf.obj)
      (forget₂ CommRingCat RingCat) ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)))) (equation Y L₁ L₂ s)

include h₁ h₂ in
/-- The closed immersion `ι : L ⟶ Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})`. -/
def spaceι : (spaceIdeal Y L₁ L₂ s).subscheme ⟶ totalSpace Y L₁ L₂ :=
  (spaceIdeal Y L₁ L₂ s).subschemeι

include h₁ h₂ in
/-- The structure morphism `p = ι ≫ q : L ⟶ Y`. -/
def proj : (spaceIdeal Y L₁ L₂ s).subscheme ⟶ Y :=
  spaceι Y L₁ L₂ s ≫ totalProj Y L₁ L₂

include h₁ h₂ in
/-- The section `s₁` of `p^*L₁`: the first fibre coordinate restricted to `L`. -/
def section₁ : Γ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁, ⊤) :=
  PresheafOfModules.Hom.app
    (pullbackCompHom (spaceι Y L₁ L₂ s) (totalProj Y L₁ L₂) L₁).val (op ⊤)
    (pullbackGlobalSections (spaceι Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂))

include h₁ h₂ in
/-- The section `s₂` of `p^*L₂`: the second fibre coordinate restricted to `L`. -/
def section₂ : Γ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂, ⊤) :=
  PresheafOfModules.Hom.app
    (pullbackCompHom (spaceι Y L₁ L₂ s) (totalProj Y L₁ L₂) L₂).val (op ⊤)
    (pullbackGlobalSections (spaceι Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂))

include h₁ h₂ in
/-- The branch `D₁`: the zero scheme of `s₁`, as an ideal sheaf on `L`. -/
def branch₁ : (spaceIdeal Y L₁ L₂ s).subscheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
    ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁) (section₁ Y L₁ L₂ s)

include h₁ h₂ in
/-- The branch `D₂`: the zero scheme of `s₂`, as an ideal sheaf on `L`. -/
def branch₂ : (spaceIdeal Y L₁ L₂ s).subscheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
    ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂) (section₂ Y L₁ L₂ s)

include h₁ h₂ in
/-- The branch `D₁` is the zero scheme of `s₁`. -/
theorem branch₁_eq_zeroScheme :
    branch₁ Y L₁ L₂ s =
      Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁) (section₁ Y L₁ L₂ s) :=
  rfl

include h₁ h₂ in
/-- The branch `D₂` is the zero scheme of `s₂`. -/
theorem branch₂_eq_zeroScheme :
    branch₂ Y L₁ L₂ s =
      Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂) (section₂ Y L₁ L₂ s) :=
  rfl

include h₁ h₂ in
/-- The equation vanishes on the zero scheme it cuts out. -/
theorem pullbackGlobalSections_equation_eq_zero :
    pullbackGlobalSections (spaceι Y L₁ L₂ s)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(totalSpace Y L₁ L₂).sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
          ((totalSpace Y L₁ L₂).sheaf.obj) (forget₂ CommRingCat RingCat)
          ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂))))
        (equation Y L₁ L₂ s) = 0 :=
  (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (totalSpace Y L₁ L₂)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(totalSpace Y L₁ L₂).sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ ((totalSpace Y L₁ L₂).sheaf.obj)
      (forget₂ CommRingCat RingCat) ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
      (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂))))
    (equation Y L₁ L₂ s) (spaceι Y L₁ L₂ s)).2 ⟨CategoryStruct.id _, Category.id_comp _⟩

include h₁ h₂ in
/-- On the zero scheme of the equation the product of the two fibre coordinates agrees with the
pullback of `s`. -/
theorem pullbackGlobalSections_coordProduct :
    pullbackGlobalSections (spaceι Y L₁ L₂ s)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(totalSpace Y L₁ L₂).sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
          ((totalSpace Y L₁ L₂).sheaf.obj) (forget₂ CommRingCat RingCat)
          ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)))) (coordProduct Y L₁ L₂) =
      pullbackGlobalSections (spaceι Y L₁ L₂ s)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(totalSpace Y L₁ L₂).sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
          ((totalSpace Y L₁ L₂).sheaf.obj) (forget₂ CommRingCat RingCat)
          ((totalSpace Y L₁ L₂).ringCatSheaf.property)⟩).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁))).obj
          (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂))))
        (pullbackTensorSection (totalProj Y L₁ L₂) L₁ L₂ s) := by
  have hvan := pullbackGlobalSections_equation_eq_zero Y L₁ L₂ s
  rwa [equation, map_sub, sub_eq_zero] at hvan

include h₁ h₂ in
/-- The pullback `p^*s` of the section to the zero scheme `L` of `z₁ ⊗ z₂ - q^*s`, read in
`p^*L₁ ⊗ p^*L₂`, is the product `s₁ ⊗ s₂` of the two restricted fibre coordinates. -/
@[stacks 0F97 "the construction and conditions (1), (3); (2) and (4)-(7) not proved here"]
theorem pullbackTensorSection_proj :
    pullbackTensorSection (proj Y L₁ L₂ s) L₁ L₂ s =
      tensorSectionsAt (spaceIdeal Y L₁ L₂ s).subscheme.sheaf.obj
        (spaceIdeal Y L₁ L₂ s).subscheme.ringCatSheaf.property (op ⊤)
        ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
        ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂)
        (section₁ Y L₁ L₂ s) (section₂ Y L₁ L₂ s) := by
  have key : pullbackTensorSection (spaceι Y L₁ L₂ s)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
        (pullbackTensorSection (totalProj Y L₁ L₂) L₁ L₂ s) =
      tensorSectionsAt (spaceIdeal Y L₁ L₂ s).subscheme.sheaf.obj
        (spaceIdeal Y L₁ L₂ s).subscheme.ringCatSheaf.property (op ⊤) _ _
        (pullbackGlobalSections (spaceι Y L₁ L₂ s)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂))
        (pullbackGlobalSections (spaceι Y L₁ L₂ s)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂)) := by
    rw [Stacks.PullbackTensorIso.pullbackTensorSection,
      ← pullbackGlobalSections_coordProduct Y L₁ L₂ s, coordProduct]
    exact Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt
      (spaceι Y L₁ L₂ s) ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₁ Y L₁ L₂) (coord₂ Y L₁ L₂)
  refine Eq.trans (Stacks.PullbackTensorIso.pullbackTensorSection_comp
    (spaceι Y L₁ L₂ s) (totalProj Y L₁ L₂) L₁ L₂ s) ?_
  rw [key, Stacks.PullbackTensorIso.tensorSheafMap_tensorSectionsAt]
  rfl

end Stacks.Chow.TensorZeroScheme

end
