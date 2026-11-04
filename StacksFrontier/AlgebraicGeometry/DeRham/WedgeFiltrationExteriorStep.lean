module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsImageSubobject
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeComponentRestrictScalars
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# The degree-`m` step of the wedge filtration is the step of the exterior-power filtration

Section 50.12 of the Stacks project filters the relative de Rham complex `Ω^•_{X/S}` by the forms
pulled back from `Y`, and [Stacks, Section 0FMK] computes the graded pieces of that filtration
*one sheaf at a time*, from the filtration of the single sheaf `Ω^n_{X/S}` by the images of
`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^{n-k}Ω_{X/S}`. The two filtrations are built from different data:

* the complex-level one from the wedge maps out of `Tot(σ^{≥k}P^• ⊗_A Ω^•_{X/S})`, with `A` the
  base ring sheaf `(f∘g)^{-1}𝒪_S` and `P^• = f^{-1}Ω^•_{Y/S}`, so its steps are subobjects in
  sheaves of `A`-modules (`AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep`);
* the sheaf-level one from the wedge maps `⋀^kF ⊗_{𝒪_X} ⋀^{n-k}Ω_{X/S} ⟶ ⋀^nΩ_{X/S}`, so its
  steps are subobjects in sheaves of `𝒪_X`-modules
  (`SheafOfModules.exteriorImageFiltration`).

**This file identifies them in each degree.** The input is the factorization of `ι` through the
exterior powers of `F`: for the de Rham pullback map `ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` the
degree-`i` component factors as

`f^{-1}Ω^i_{Y/S} ⟶ ⋀^i(f^*Ω_{Y/S}) ⟶ ⋀^iΩ_{X/S}`,

the second map being the morphism on exterior powers induced by `f^*Ω_{Y/S} ⟶ Ω_{X/S}`
(`Stacks.DeRhamPullback.deRhamPullbackChain_f_exteriorPowerPullback`), and that factorization is
all the construction uses; it is taken as the hypothesis `hc` below rather than instantiated
here, so that the statements stay at the generic binders of
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`.

Given it, the `(i, j)` summand of the degree-`m` wedge map is the `𝒜`-linear wedge map of the
exterior-power filtration precomposed with `c i ⊗ 1`
(`AlgebraicGeometry.SheafOfModules.summand_eq_laxComparison_comp`), so its image is *contained*
in the degree-`m` step of the exterior-power filtration read over `A`
(`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_le_exteriorImageFiltration`), and
*equal* to it as soon as `c i ⊗ 1` followed by the lax comparison is an epimorphism
(`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_eq_exteriorImageFiltration`). Since the
exterior-power filtration decreases, the containment at `i ≥ k` and the equality at `i = k`
together give the dominance of the `i = k` summand that
`AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_of_le_summand` asks for, and
hence the degreewise identification of the two filtrations.

## Main results

* `AlgebraicGeometry.SheafOfModules.summand_eq_laxComparison_comp`: **the summand of the wedge
  map is the wedge map of the exterior-power filtration**, precomposed with `c i ⊗ 1` and with the
  lax comparison of the two tensor products. Checked on local pure tensors, where both sides are
  the product in the exterior algebra of `Ω_{X/S}`.
* `AlgebraicGeometry.SheafOfModules.imageSubobject_summand_le_exteriorImageFiltration` and
  `AlgebraicGeometry.SheafOfModules.imageSubobject_summand_eq_exteriorImageFiltration`: the image
  of that summand is contained in, and under the epimorphy hypothesis equal to, the degree-`m`
  step of `SheafOfModules.exteriorImageFiltration` transported along restriction of scalars.
* `AlgebraicGeometry.SheafOfModules.imageSubobject_summand_le_summand`: **the dominance of the
  `i = k` summand**, which is the hypothesis of
  `AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_of_le_summand`.
* `AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_exteriorImageFiltration`:
  **the degree-`m` image of the wedge map on the `k`-th brutal truncation is the degree-`m` step
  of the sheaf-level filtration**, read over the base ring sheaf.
* `AlgebraicGeometry.SheafOfModules.mapSubobjects_wedgeFiltrationStep_eq_exteriorImageFiltration`:
  **the degree-`m` term of the `k`-th step of the filtration of Section 50.12 is that step**, the
  two being compared across the extension by zero of the de Rham complex.

## Implementation notes

**What the epimorphy hypothesis is.** `c k` is in Section 50.12 the comparison
`f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S}`, which is not itself an epimorphism; what is asked is that

`f^{-1}Ω^k_{Y/S} ⊗_A Ω^{m-k}_{X/S} ⟶ (f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m-k}_{X/S})|_A`

be one, and that is true for the trivial reason that a local section `(b ⊗ ω) ⊗ η` of the target
is the image of `ω ⊗ (b·η)`: the `𝒪_X`-linearity of the right-hand tensor factor is what moves
the scalar across. It is the underived identity `F ⊗_{𝒪_X} f^*G ≅ F ⊗_{f^{-1}𝒪_Y} f^{-1}G` of
[Stacks, Tag 08DE] in surjective form. It is named as a hypothesis here, so that the statements
stay at the generic binders, and it is **discharged** at the de Rham pullback map by
`Stacks.DeRhamSmooth.epi_pulledBackFormsComparison_tensor_comp_laxComparison` of
`StacksFrontier.AlgebraicGeometry.DeRham.PulledBackFormsComparisonEpi`, which deduces it from the
local generation of a pullback by the pullback-unit sections; so this file leaves no obligation
open. Everything else — the containment at every `i ≥ k`, the dominance, and the identification
of the two filtrations — is proved from it.

**The equalities of morphisms are checked on local pure tensors.** A morphism out of a tensor
product sheaf is not determined by its values on local pure tensors, but two morphisms agreeing on
them are equal (`PresheafOfModules.tensorSheaf_hom_ext`), and that is how
`summand_eq_laxComparison_comp` is proved, from
`AlgebraicGeometry.SheafOfModules.exteriorProductComponent_unit_apply` on one side and
`SheafOfModules.prodWedgeHomIdRight_val_app_tensorSheafUnit` on the other. This is the same device
as `AlgebraicGeometry.SheafOfModules.laxComparison_comp_restrictScalars_mulSheaf`, whose statement
this one is the `ι`-twisted form of.

**The abelian structures are named, not re-derived.** `Stacks.SheafOfModules.abelianOfSmallSite`
for sheaves of `𝒪_X`-modules and `AlgebraicGeometry.SheafOfModules.abelianModules` for sheaves of
`A`-modules are the two instances the subobject lattices of the two filtrations are elaborated
against in `StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` and in
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`; they are turned on here rather than left
to instance search, which at these binders would both exceed the synthesis budget and risk
picking a second, definitionally equal, copy that then fails to unify with the statements being
combined.

**The two index sets.** The complex-level filtration is indexed by `ℤ`, its ambient complex
being the extension by zero of the `ℕ`-indexed de Rham complex, so its degree-`m` term is a
subobject of `(Ω^•_{X/S})_ext^m` while the exterior-power filtration lives in `⋀^mΩ_{X/S}`. The
final statement carries the second into the first along `HomologicalComplex.extendXIso`, through
`Stacks.CategoryTheory.map_imageSubobject_of_isIso`; the reindexing `(k : ℤ).toNat = k` needs no
rewriting, being a reduction.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorRestrictScalars (laxComparison epi_laxComparison)
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)

universe u

namespace Stacks.CategoryTheory

/-- **Transporting an image along a monomorphism of its ambient object.** For `t : Q ⟶ R` a
monomorphism the image of `g : P ⟶ Q`, pushed into `R` along `t`, is the image of `g ≫ t`:
the image factorization of `g` composed with `t` is one of `g ≫ t`. Stated at generic objects,
which is also what makes it usable at the concrete objects of the wedge filtration: there two
definitionally equal category instances are in scope, and a statement proved at generic objects
instantiates with no search at all. -/
theorem map_imageSubobject {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    [_root_.CategoryTheory.Abelian C₁] {P Q R : C₁} (g : P ⟶ Q) (t : Q ⟶ R) [Mono t] :
    (_root_.CategoryTheory.Subobject.map t).obj (imageSubobject g) = imageSubobject (g ≫ t) :=
  _root_.CategoryTheory.Subobject.mk_eq_imageSubobject_of_mono (factorThruImage g)
    (image.ι g ≫ t) (by rw [← Category.assoc, image.fac])

/-- **Precomposing with an isomorphism does not change an image subobject.** This is
`CategoryTheory.Limits.imageSubobject_iso_comp` with the invertibility of the first factor
carried by an `Iso` rather than by an instance: at the concrete objects of the wedge filtration
instance search cannot find `IsIso e.hom` for an honest isomorphism `e`, which is the same
obstruction `Stacks.CategoryTheory.epi_isoHom_comp` of
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonSource` works around. -/
theorem imageSubobject_isoHom_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    [_root_.CategoryTheory.Abelian C₁] {P Q R : C₁} (e : P ≅ Q) (g : Q ⟶ R) :
    imageSubobject (e.hom ≫ g) = imageSubobject g :=
  have : IsIso e.hom := Iso.isIso_hom e
  imageSubobject_iso_comp e.hom g

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)
  {F : _root_.SheafOfModules.{u}
    (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf)}
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)
  (iF : F ⟶ moduleOfDifferentials.{u, u, u} φ)
  (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
  (ι : P ⟶ deRhamComplex B D)
  (c : ∀ i : ℕ, P.X i ⟶
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).obj
      (AF.exteriorPower i))
  (hc : ∀ i : ℕ, ι.f i = c i ≫
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
      ((AF.exterior_isExteriorAlgebra.map B.exterior_isExteriorAlgebra iF).app (i : ℤ)))

/-! The abelian structures of the two categories of sheaves of modules, named rather than
searched for: these are the instances the two filtrations are elaborated against, in
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` and in
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

/-! The two binders of `Stacks.SheafOfModules.Tensor.sheafTensor` on the open-cover site, and the
transparency settings, under which `StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`
elaborates the wedge maps; the statements below are read against those elaborations. -/
attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The summand of the wedge map, read through the exterior powers of `F` -/

/-- **The reindexing isomorphism of the de Rham complex is the restriction of scalars of a
transport of exterior powers.** Both sides are the transport of `⋀^•Ω_{X/S}` along `i + j = m`;
on the left it is formed in sheaves of `A`-modules and on the right in sheaves of
`𝒪_X`-modules. -/
theorem deRhamComplex_XIsoOfEq_hom {i j m : ℕ} (h : i + j = m) :
    ((deRhamComplex B D).XIsoOfEq h).hom =
      (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
        (eqToHom (congrArg (fun t : ℕ => B.exteriorPower t) h)) := by
  subst h
  exact ((congrArg
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
      (eqToHom_refl _ _)).trans (_root_.CategoryTheory.Functor.map_id _ _)).symm

include hc in
/-- **The `(i, j)` summand of the wedge map is the wedge map of the exterior-power
filtration.** The summand map

`P^i ⊗_A Ω^j_{X/S} ⟶ Ω^i_{X/S} ⊗_A Ω^j_{X/S} ⟶ Ω^{i+j}_{X/S}`

is `c i ⊗ 1`, the lax comparison
`(⋀^iF)|_A ⊗_A (⋀^jΩ_{X/S})|_A ⟶ (⋀^iF ⊗_{𝒪_X} ⋀^jΩ_{X/S})|_A`, and the restriction of scalars
of `SheafOfModules.prodWedgeHom`. Both sides are checked on a local pure tensor `x ⊗ y`, where
each is the product of the image of `x` in `⋀^iΩ_{X/S}` with `y` in the exterior algebra of
`Ω_{X/S}`. -/
theorem summand_eq_laxComparison_comp (i j : ℕ) :
    ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j =
      ((sheafTensor.{u,u,u,u,u} A).map (c i)).app ((deRhamComplex B D).X j) ≫
        laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j) ≫
          (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
            (_root_.SheafOfModules.prodWedgeHom AF B B iF (𝟙 _) i j) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := A) (F := P.X i)
    (G := deRhamTerm B j) (Q := deRhamTerm B (i + j)) fun U x y => ?_
  refine Eq.trans (congrArg ((exteriorProductComponent B i j).val.app U)
    (tensorFunctor_map_unit_apply (ι.f i) U x y)) ?_
  refine Eq.trans (exteriorProductComponent_unit_apply B i j U ((ι.f i).val.app U x) y) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun z => (_root_.SheafOfModules.prodWedgeHom AF B B iF (𝟙 _) i j).val.app U
      ((laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j)).val.app U z))
    (tensorFunctor_map_unit_apply (c i) U x y)) ?_)
  refine Eq.trans (congrArg
    ((_root_.SheafOfModules.prodWedgeHom AF B B iF (𝟙 _) i j).val.app U)
    (laxComparison_val_app_tensorSheafUnit (φ := φ) (AF.exteriorPower i) (B.exteriorPower j)
      U ((c i).val.app U x) y)) ?_
  refine Eq.trans (_root_.SheafOfModules.prodWedgeHomIdRight_val_app_tensorSheafUnit
    AF B iF i j U ((c i).val.app U x) y) ?_
  exact congrArg (fun t => (B.exterior.mul (i : ℤ) (j : ℤ)).app U t y)
    (congrArg (fun t : P.X i ⟶ deRhamTerm B i => t.val.app U x) (hc i)).symm

include hc in
/-- `AlgebraicGeometry.SheafOfModules.summand_eq_laxComparison_comp` with the total degree named
by a hypothesis, which is the shape the summands of the wedge filtration are written in. -/
theorem summandOfEq_eq_laxComparison_comp (i j m : ℕ) (h : i + j = m) :
    ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom =
      ((sheafTensor.{u,u,u,u,u} A).map (c i)).app ((deRhamComplex B D).X j) ≫
        laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j) ≫
          (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
            (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) i j m h) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ ((deRhamComplex B D).XIsoOfEq h).hom)
    (summand_eq_laxComparison_comp B D AF iF P ι c hc i j)) ?_
  refine Eq.trans (congrArg (fun t => (((sheafTensor.{u,u,u,u,u} A).map (c i)).app
        ((deRhamComplex B D).X j) ≫
      laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j) ≫
        (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
          (_root_.SheafOfModules.prodWedgeHom AF B B iF (𝟙 _) i j)) ≫ t)
    (deRhamComplex_XIsoOfEq_hom B D h)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (((sheafTensor.{u,u,u,u,u} A).map (c i)).app ((deRhamComplex B D).X j) ≫ ·) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j) ≫ ·) ?_
  exact (_root_.CategoryTheory.Functor.map_comp (_root_.SheafOfModules.restrictScalars
    (underlyingRingHom (φ := φ))) _ _).symm

/-! ### Restriction of scalars on the subobject lattices -/

/-- **Restriction of scalars along `φ`, on the lattice of subobjects of `⋀^mΩ_{X/S}`**: it
carries a sheaf of `𝒪_X`-submodules of `⋀^mΩ_{X/S}` to the same subsheaf, read as a sheaf of
`A`-submodules. This is `CategoryTheory.mapSubobjects` at
`SheafOfModules.restrictScalars`, and it is given a name because a `def` with an ascribed result
type propagates the category instances of the two subobject lattices while a theorem statement
does not: written inline in a statement, the hom universe of the lattice of subobjects is left
undetermined and instance search for its category structure fails. -/
def exteriorPowerSubobjectRestriction (m : ℕ) :
    Subobject (B.exteriorPower m) ⥤ Subobject (deRhamTerm B m) :=
  mapSubobjects (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))) _

/-- **Restriction of scalars does not change the image of a morphism**: the image of the
restricted morphism is the restriction of the image, restriction of scalars being exact. This is
`Stacks.SheafOfModules.ChangeOfRings.imageSubobject_map_restrictScalars` at the binders of the de
Rham complex. -/
theorem exteriorPowerSubobjectRestriction_imageSubobject (m : ℕ)
    {M : _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf)}
    (f : M ⟶ B.exteriorPower m) :
    imageSubobject ((_root_.SheafOfModules.restrictScalars.{u}
        (underlyingRingHom (φ := φ))).map f) =
      (exteriorPowerSubobjectRestriction B m).obj (imageSubobject f) :=
  Stacks.SheafOfModules.ChangeOfRings.imageSubobject_map_restrictScalars _ f

/-- **Restriction of scalars is monotone on subobjects**: it is a functor between the two
lattices, read as categories. -/
theorem exteriorPowerSubobjectRestriction_monotone (m : ℕ) :
    Monotone (exteriorPowerSubobjectRestriction B m).obj :=
  fun _ _ h => leOfHom ((exteriorPowerSubobjectRestriction B m).map (homOfLE h))

/-- The degree-`m` step at `i` of the exterior-power filtration, read over the base ring sheaf,
is the image of the restriction of scalars of the wedge map cutting it out. -/
theorem exteriorPowerSubobjectRestriction_exteriorImageFiltration (i j m : ℕ) (h : i + j = m) :
    (exteriorPowerSubobjectRestriction B m).obj
        (_root_.SheafOfModules.exteriorImageFiltration AF B iF m i) =
      imageSubobject ((_root_.SheafOfModules.restrictScalars.{u}
          (underlyingRingHom (φ := φ))).map
        (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) i j m h)) :=
  (congrArg (exteriorPowerSubobjectRestriction B m).obj
      (_root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject AF B iF i j m h)).trans
    (exteriorPowerSubobjectRestriction_imageSubobject B m _).symm

/-! ### The image of the summand -/

include hc in
/-- **The image of the `(i, j)` summand is contained in the degree-`m` step of the
exterior-power filtration**, read over the base ring sheaf. The summand factors through the
wedge map `⋀^iF ⊗_{𝒪_X} ⋀^jΩ_{X/S} ⟶ ⋀^mΩ_{X/S}` cutting out that step, by
`AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp`, and the lax comparison —
being an epimorphism — does not change the image. -/
theorem imageSubobject_summand_le_exteriorImageFiltration (i j m : ℕ) (h : i + j = m) :
    imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≤
      (exteriorPowerSubobjectRestriction B m).obj
        (_root_.SheafOfModules.exteriorImageFiltration AF B iF m i) := by
  refine le_of_le_of_eq ?_
    (exteriorPowerSubobjectRestriction_exteriorImageFiltration B AF iF i j m h).symm
  refine le_of_le_of_eq (Stacks.CategoryTheory.imageSubobject_le_imageSubobject_of_eq_comp _
    (((sheafTensor.{u,u,u,u,u} A).map (c i)).app ((deRhamComplex B D).X j))
    (laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j) ≫
      (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
        (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) i j m h))
    (summandOfEq_eq_laxComparison_comp B D AF iF P ι c hc i j m h)) ?_
  exact Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp _
    (epi_laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j)) _

include hc in
/-- **The image of the `(i, j)` summand is the degree-`m` step of the exterior-power
filtration**, read over the base ring sheaf, as soon as `c i ⊗ 1` followed by the lax comparison
is an epimorphism. That hypothesis is Section 50.12's surjection
`f^{-1}Ω^i_{Y/S} ⊗_A Ω^j_{X/S} ⟶ (f^*Ω^i_{Y/S} ⊗_{𝒪_X} Ω^j_{X/S})|_A`; see the implementation
notes. -/
theorem imageSubobject_summand_eq_exteriorImageFiltration (i j m : ℕ) (h : i + j = m)
    (hepi : Epi (((sheafTensor.{u, u, u, u, u} A).map (c i)).app ((deRhamComplex B D).X j) ≫
      laxComparison A X.sheaf φ (AF.exteriorPower i) (B.exteriorPower j))) :
    imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) =
      (exteriorPowerSubobjectRestriction B m).obj
        (_root_.SheafOfModules.exteriorImageFiltration AF B iF m i) := by
  refine Eq.trans ?_
    (exteriorPowerSubobjectRestriction_exteriorImageFiltration B AF iF i j m h).symm
  refine Eq.trans (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr
    (summandOfEq_eq_laxComparison_comp B D AF iF P ι c hc i j m h)) ?_
  refine Eq.trans (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr
    (Category.assoc _ _ _).symm) ?_
  exact Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp _ hepi _

/-! ### The dominance of the `i = k` summand -/

include hc in
/-- **The `i = k` summand dominates the summands above it.** For `k ≤ i` and `i + j = m` the
image of the `(i, j)` summand of the degree-`m` wedge map is contained in the image of the
`(k, m - k)` summand: the first is contained in the degree-`m` step at `i` of the exterior-power
filtration, which is contained in its step at `k` because that filtration decreases, and the
second *is* the step at `k` under the epimorphy hypothesis. This is the dominance hypothesis of
`AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_of_le_summand`. -/
theorem imageSubobject_summand_le_summand (k i j m : ℕ) (hk : k ≤ i) (h : i + j = m)
    (hepi : Epi (((sheafTensor.{u, u, u, u, u} A).map (c k)).app ((deRhamComplex B D).X (m - k)) ≫
      laxComparison A X.sheaf φ (AF.exteriorPower k) (B.exteriorPower (m - k)))) :
    imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≤
      imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f k)).app
          ((deRhamComplex B D).X (m - k)) ≫
        exteriorProductComponent B k (m - k) ≫
        ((deRhamComplex B D).XIsoOfEq (show k + (m - k) = m by omega)).hom) := by
  refine le_of_le_of_eq ?_ (imageSubobject_summand_eq_exteriorImageFiltration B D AF iF P ι c hc
    k (m - k) m (by omega) hepi).symm
  refine le_trans
    (imageSubobject_summand_le_exteriorImageFiltration B D AF iF P ι c hc i j m h) ?_
  exact exteriorPowerSubobjectRestriction_monotone B m
    (_root_.SheafOfModules.exteriorImageFiltration_antitone AF B iF m hk)

include hc in
/-- **The degree-`m` step of the complex-level wedge filtration is the degree-`m` step of the
exterior-power filtration**, read over the base ring sheaf: the image of the degree-`m` component
of the wedge map out of `Tot(σ^{≥k}P^• ⊗_A Ω^•_{X/S})` is the step
`SheafOfModules.exteriorImageFiltration` of `⋀^mΩ_{X/S}` at `k`, which is the image of
`⋀^kF ⊗_{𝒪_X} ⋀^{m-k}Ω_{X/S} ⟶ ⋀^mΩ_{X/S}`.

This is the comparison [Stacks, Section 0FMK] needs in order to read its sheaf-level
identification of the graded pieces on the filtration of the complex: the summands of the wedge
map above the cut are dominated by the one at `i = k`
(`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_le_summand`), the ones below it vanish,
and the surviving one cuts out the step of the exterior-power filtration. -/
theorem imageSubobject_wedgeAlongBrutal_eq_exteriorImageFiltration (k m : ℕ) (hk : k ≤ m)
    (hepi : Epi (((sheafTensor.{u, u, u, u, u} A).map (c k)).app ((deRhamComplex B D).X (m - k)) ≫
      laxComparison A X.sheaf φ (AF.exteriorPower k) (B.exteriorPower (m - k)))) :
    imageSubobject ((CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) =
      (exteriorPowerSubobjectRestriction B m).obj
        (_root_.SheafOfModules.exteriorImageFiltration AF B iF m k) := by
  refine Eq.trans (imageSubobject_wedgeAlongBrutal_eq_of_le_summand B D P ι k m hk
    fun i j hik h => imageSubobject_summand_le_summand B D AF iF P ι c hc k i j m hik h hepi) ?_
  refine Eq.trans (imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_of_le B D P ι k k (m - k) m
    le_rfl (show k + (m - k) = m by omega)) ?_
  exact imageSubobject_summand_eq_exteriorImageFiltration B D AF iF P ι c hc k (m - k) m
    (by omega) hepi

include hc in
/-- **The degree-`m` term of the `k`-th step of the filtration of Section 50.12 is the
degree-`m` step of the filtration of [Stacks, Section 0FMK]**, for `k ≥ 1`. On the left the
`k`-th step of the filtration of the complex `Ω^•_{X/S}`, evaluated in degree `m`; on the right
the step at `k` of `SheafOfModules.exteriorImageFiltration` of the single sheaf `⋀^mΩ_{X/S}`,
read over the base ring sheaf and pushed into the degree-`m` term of the extension by zero of
the de Rham complex along `HomologicalComplex.extendXIso`.

This is the identification the complex-level statement of Section 0FMK needs: it is what lets
the sheaf-level computation of `gr^kΩ^m_{X/S}` be read on the filtered complex. -/
theorem mapSubobjects_wedgeFiltrationStep_eq_exteriorImageFiltration (k m : ℕ) (hk0 : 0 < k)
    (hk : k ≤ m)
    (hepi : Epi (((sheafTensor.{u, u, u, u, u} A).map (c k)).app ((deRhamComplex B D).X (m - k)) ≫
      laxComparison A X.sheaf φ (AF.exteriorPower k) (B.exteriorPower (m - k)))) :
    (mapSubobjects (HomologicalComplex.eval _ (ComplexShape.up ℤ) (m : ℤ))
          (deRhamComplexInt B D)).obj (wedgeFiltrationStep B D P ι (k : ℤ)) =
      (_root_.CategoryTheory.Subobject.map
            ((deRhamComplex B D).extendXIso ComplexShape.embeddingUpNat
              (i := m) (i' := (m : ℤ)) rfl).inv).obj
        ((exteriorPowerSubobjectRestriction B m).obj
          (_root_.SheafOfModules.exteriorImageFiltration AF B iF m k)) := by
  rw [mapSubobjects_wedgeFiltrationStep B D P ι (k : ℤ) (by exact_mod_cast hk0) (m : ℤ),
    ← imageSubobject_wedgeAlongBrutal_eq_exteriorImageFiltration B D AF iF P ι c hc k m hk hepi,
    Stacks.CategoryTheory.map_imageSubobject]
  exact (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr
    (HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ))
      rfl)).trans (Stacks.CategoryTheory.imageSubobject_isoHom_comp _ _)

end AlgebraicGeometry.SheafOfModules

end
