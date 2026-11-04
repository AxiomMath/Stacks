module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Stacks Tag 01CY remark `X_s ∩ X_{s'} = X_{s ⊗ s'}`, for two arbitrary modules

For `F` and `G` two `𝒪_X`-modules and `e`, `f` global sections of them, the product `e ⊗ f` is a
global section of `F ⊗ G`, and this file proves that its nonvanishing locus is the intersection of
the two:

  `X_{e ⊗ f} = X_e ∩ X_f`.

This is the remark of [Stacks, Tag 01CY] in the generality the source states it.
`StacksFrontier/AlgebraicGeometry/AmplePowers/Basic.lean` records the gap in its own "What is not
done":
*"The remark `X_s ∩ X_{s'} = X_{s ⊗ s'}` is proved only in the case where `s'` is a section of the
structure sheaf, because the general case is a statement about the tensor product of two modules
and so belongs with Tag 01CU."* The structure-sheaf case is
`Stacks.Ample.nonvanishingLocus_smul`; the case of two tensor *powers of one* invertible module,
multiplied in the graded ring of sections, is `Stacks.SectionProduct.nonvanishingLocus_mul`. What
is proved here is the case of two arbitrary invertible modules, with no graded ring and no
tensor-power indexing anywhere, and the degenerate direction (`⊆`) with no invertibility at all.

## The product, and why it is a composite rather than an elementary tensor

A global section of `F` is a morphism `𝟙_ X.Modules ⟶ F` — that is
`Stacks.SectionProduct.globalSection`'s packaging, and the equivalence with `Γ(F, ⊤)` is
`Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`. The product of two such is therefore
available as a composite of structural morphisms, with no formula for the monoidal product on
sections needed:

  `Stacks.TensorSectionNonvanishing.unitMul e f := e ≫ (ρ_ F).inv ≫ F ◁ f`.

This matters. The monoidal product of `X.Modules` is built by localizing the sectionwise one, so
`F ⊗ G` carries no formula on sections; `Stacks.SectionTensorFormula.tensorSection` supplies one,
but it is the image of an elementary tensor under a map that is only *locally* bijective, and
relating it to the whiskering above is a statement about the monoidality isomorphism of
sheafification on sections, which this repository does not have. Everything below is therefore
stated about `unitMul` and never about an elementary tensor — exactly as
`Stacks.SectionProduct.nonvanishingLocus_mul` is stated about `Stacks.GradedSections.mul` and not
about one. See "What is not done".

## Main definitions

* `Stacks.TensorSectionNonvanishing.mulRight F f`: multiplication by a global section `f` of `G`,
  as a morphism of modules `F ⟶ F ⊗ G`.
* `Stacks.TensorSectionNonvanishing.mulLeft e G`: multiplication by a global section `e` of `F`,
  as a morphism `G ⟶ F ⊗ G`.
* `Stacks.TensorSectionNonvanishing.mulSec F f m`: the product of a section `m` of `F` over an
  **arbitrary open** `U` with a global section `f` of `G`, a section of `F ⊗ G` over `U`.
* `Stacks.TensorSectionNonvanishing.unitMul e f`: the product of two global sections, as a
  morphism `𝟙_ X.Modules ⟶ F ⊗ G`.

## Main results

* `Stacks.TensorSectionNonvanishing.unitMul_eq_mulLeft`: **the product is symmetric in the two
  roles.** `unitMul e f` is both `e` multiplied by `f` on the right and `f` multiplied by `e` on
  the left. This is what makes the two halves of the `⊆` direction one argument applied twice,
  and it is the only place the monoidal coherence of `X.Modules` is used.
* `Stacks.TensorSectionNonvanishing.surjStalk_mulRight`: **multiplication by a global section of
  an invertible `G` is surjective on the stalk at every point where that section does not
  vanish**, for an arbitrary `F`. The generalisation of
  `Stacks.SectionProduct.surjStalk_mulMap` off the tensor powers of a single module.
* `Stacks.TensorSectionNonvanishing.generates_mulSec`: **generation passes along multiplication by
  a nonvanishing global section**, over an arbitrary open. This is the form a consumer holding a
  section over an affine chart wants.
* `Stacks.TensorSectionNonvanishing.nonvanishingLocus_unitMul_subset_left` and
  `..._subset_right`: the `⊆` direction, **with no invertibility hypothesis on anything**.
* `Stacks.TensorSectionNonvanishing.nonvanishingLocus_unitMul`: **`X_{e ⊗ f} = X_e ∩ X_f`** for
  `F` and `G` invertible.
* `Stacks.TensorSectionNonvanishing.nonvanishingOpen_unitMul`: the same as an equality of opens,
  for the consumers stated over `Stacks.NonvanishingOpen.nonvanishingOpen`.

## Implementation notes

**The `⊆` direction needs only linearity of a stalk map.** `unitMul e f` is `e ≫ mulRight F f`, so
its germ is the image of the germ of `e` under a morphism of modules, and
`Stacks.SectionProduct.mapFun_mem_maximalSmul` carries `𝔪_x F_x` into `𝔪_x (F ⊗ G)_x`. No
invertibility, no local freeness and no stalk computation enters, which is why those two lemmas
are stated for arbitrary `F` and `G`. `Stacks.SectionProduct.nonvanishingLocus_mul_subset_right`
is the same observation inside the graded ring.

**The `⊇` direction is surjectivity on stalks, and the invertibility is used exactly twice.**
Once to know that multiplication by `f` is surjective on the stalk at a point of `X_f`
(`Stacks.SectionProduct.surjStalk_of_mem_nonvanishingLocus`, which needs `G` invertible), and once
to know that the germ of `e` generates `F_x` rather than merely avoiding `𝔪_x F_x`
(`Stacks.SectionProduct.exists_smul_Γgerm`, which needs `F` invertible). The conclusion is then
`Stacks.SectionProduct.notMem_maximalSmul_of_generates` for `F ⊗ G`, whose invertibility is
`Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules` — an instance, so it is never
supplied by hand below.

**`Stacks.SectionProduct.SurjStalk.whiskerLeft` is what makes this cheap**, and it is available: the
monoidal `tensorLeft` of `SheafOfModules` is the sheafified sectionwise tensor product, and only
the fact that that comparison is an isomorphism is used, never a formula for it. So no part of
this file computes the tensor product on sections.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

**No `@[stacks]` attribute is attached.** Tag 01CY's own assertions are the openness of `X_s` and
the triviality of `M` on it; the displayed equality is a *remark* of that tag, carries no label of
its own in the source, and nothing here proves either assertion. Tag 01CU is the construction of the
integer tensor powers, which is formalized elsewhere and is not this file.

**The product is not related to `Stacks.SectionTensorFormula.tensorSection`.** That is the one
thing a consumer might expect and it is genuinely absent: `tensorSection F G m n` is the image of
the elementary tensor `m ⊗ₜ n` under `Stacks.SectionTensorFormula.toTensorSection`, and
identifying it with `mulSec F f m` for `n` the global section of `f` needs two statements this
repository does not have — naturality of `toTensorSection` in its second variable, and the formula
for it against the right unitor at `G = 𝟙_ X.Modules`. Both are statements about the monoidality
isomorphism of sheafification on sections, which
`StacksFrontier/AlgebraicGeometry/SectionProduct/Stalk.lean` also records as missing in its own
"What is not done" ("no formula is proved for the monoidality isomorphism of sheafification on
sections"), and which is the reason the literal multiplication clause of Tag 01CV is still open.
Consequently the module-valued form of [Stacks, Tag 01PW]
(`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple`), whose conclusion is
stated with `tensorSection`, **cannot yet be composed with the results below**; that bridge, and
not any statement here, is what clause (5) of [Stacks, Tag 01Q3] is waiting on.

**Only surjectivity on stalks is treated**, so nothing here says that multiplication by a
nonvanishing section is injective, or an isomorphism, on the nonvanishing locus — that is clause 2
of Tag 01CY and is open, as `SectionProduct/Stalk.lean` records.

**Nothing is proved for a section of `G` over a proper open.** `mulRight` needs `f` global, since
it is built by whiskering a morphism out of the monoidal unit; the product of two sections over
the same open `U` would need the monoidal structure of `SheafOfModules.overFunctor`, which is the
open problem recorded in the "What is not done" of
`StacksFrontier/AlgebraicGeometry/TwistTensor/Basic.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
open TopologicalSpace
open Stacks.Ample Stacks.ModuleStalk Stacks.SectionProduct

universe u

namespace Stacks.TensorSectionNonvanishing

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-! ### Multiplication by a global section -/

/-- **Multiplication by a global section `f` of `G`**, as a morphism of `𝒪_X`-modules
`F ⟶ F ⊗ G`. A global section of `G` is a morphism out of the monoidal unit, so this is that
morphism whiskered by `F` and read through the right unitor. -/
def mulRight (F : X.Modules) {G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) : F ⟶ F ⊗ G :=
  (ρ_ F).inv ≫ F ◁ f

/-- **Multiplication by a global section `e` of `F`**, as a morphism `G ⟶ F ⊗ G`. -/
def mulLeft {F : X.Modules} (e : 𝟙_ X.Modules ⟶ F) (G : X.Modules) : G ⟶ F ⊗ G :=
  (λ_ G).inv ≫ e ▷ G

/-- **The product of a section of `F` over an arbitrary open with a global section of `G`.** This
is `mulRight` evaluated on sections, and it is the shape a consumer holding a section over an
affine chart wants. -/
def mulSec (F : X.Modules) {G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) {U : X.Opens} (m : Γ(F, U)) :
    Γ(F ⊗ G, U) :=
  (mulRight F f).app U m

/-- The product of sections commutes with restriction, being the evaluation of a morphism of
modules. -/
theorem map_mulSec (F : X.Modules) {G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) {U V : X.Opens}
    (i : V ⟶ U) (m : Γ(F, U)) :
    (F ⊗ G).presheaf.map i.op (mulSec F f m) = mulSec F f (F.presheaf.map i.op m) :=
  (PresheafOfModules.naturality_apply (mulRight F f).val i.op m).symm

/-- **A tensor product of invertible modules is invertible**, at the monoidal product of
`X.Modules` this file is written over.

`Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules` is the same fact stated for
`Stacks.RelativeVeryAmple.tensorModules`, and its own docstring records that instance search
crosses neither spelling; so
`AlgebraicGeometry.SheafOfModules.isInvertible_tensor` is invoked explicitly here. It is `scoped`
rather than global precisely because the monoidal product it is keyed on is the local one this
file installs. -/
scoped instance isInvertibleModule_tensorObj (F G : X.Modules) [IsInvertibleModule X F]
    [IsInvertibleModule X G] : IsInvertibleModule X (F ⊗ G) :=
  AlgebraicGeometry.SheafOfModules.isInvertible_tensor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F G

/-- **The product of two global sections**, as a morphism out of the monoidal unit. It is `e`
multiplied on the right by `f`; `unitMul_eq_mulLeft` says it is equally `f` multiplied on the left
by `e`. -/
def unitMul {F G : X.Modules} (e : 𝟙_ X.Modules ⟶ F) (f : 𝟙_ X.Modules ⟶ G) :
    𝟙_ X.Modules ⟶ F ⊗ G :=
  e ≫ mulRight F f

/-- **The product of two global sections is symmetric in the two roles.** Both readings are the
composite of the inverse unitor with `e ⊗ f`; the proof is the naturality of the two unitors, the
exchange law, and `MonoidalCategory.unitors_inv_equal`. This is the only place the monoidal
coherence of `X.Modules` is used, and it is what lets the two halves of
`nonvanishingLocus_unitMul` be one argument applied twice. -/
theorem unitMul_eq_mulLeft {F G : X.Modules} (e : 𝟙_ X.Modules ⟶ F) (f : 𝟙_ X.Modules ⟶ G) :
    unitMul e f = f ≫ mulLeft e G := by
  rw [unitMul, mulRight, mulLeft, ← Category.assoc,
    MonoidalCategory.rightUnitor_inv_naturality, ← Category.assoc,
    MonoidalCategory.leftUnitor_inv_naturality, Category.assoc, Category.assoc,
    MonoidalCategory.whisker_exchange, MonoidalCategory.unitors_inv_equal]

/-- The global section attached to a product is the product of sections, by
`Stacks.SectionProduct.globalSection_comp`. -/
theorem globalSection_unitMul {F G : X.Modules} (e : 𝟙_ X.Modules ⟶ F)
    (f : 𝟙_ X.Modules ⟶ G) :
    globalSection X (F ⊗ G) (unitMul e f) = mulSec F f (globalSection X F e) :=
  globalSection_comp F (F ⊗ G) e (mulRight F f)

/-! ### Surjectivity on stalks, and generation -/

/-- **Multiplication by a global section of an invertible `G` is surjective on the stalk at every
point where that section does not vanish.** `F` is arbitrary.

This is `Stacks.SectionProduct.surjStalk_mulMap` with the tensor powers of a single module
replaced by two unrelated modules: the two inputs are
`Stacks.SectionProduct.surjStalk_of_mem_nonvanishingLocus`, which turns nonvanishing into
surjectivity for the morphism out of the unit, and
`Stacks.SectionProduct.SurjStalk.whiskerLeft`. The right unitor contributes nothing beyond being
an isomorphism. -/
theorem surjStalk_mulRight (F : X.Modules) {G : X.Modules} [IsInvertibleModule X G]
    (f : 𝟙_ X.Modules ⟶ G) (x : X)
    (hx : x ∈ nonvanishingLocus G (globalSection X G f)) :
    SurjStalk (mulRight F f) x :=
  (surjStalk_of_inv (ρ_ F).hom_inv_id x).comp
    ((surjStalk_of_mem_nonvanishingLocus G f x hx).whiskerLeft F)

/-- **Generation passes along multiplication by a nonvanishing global section.** If the germ at
`x` of a section `m` of `F` over an open `U` generates `F_x`, and multiplication by `f` is
surjective on the stalk at `x`, then the germ of `mulSec F f m` generates `(F ⊗ G)_x`.

Stated over an arbitrary open `U` rather than over `⊤`: the stalk map of a morphism of modules
carries the germ of a section over `U` to the germ of its image
(`Stacks.ModuleStalk.mapFun_germ`), so nothing is lost and a consumer holding a section over an
affine chart can use it directly. -/
theorem generates_mulSec (F : X.Modules) {G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) {x : X}
    (hsurj : SurjStalk (mulRight F f) x) {U : X.Opens} (hx : x ∈ U) (m : Γ(F, U))
    (hm : ∀ v : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x,
      ∃ r : X.presheaf.stalk x, v = r • (F.presheaf.germ U x hx).hom m)
    (w : TopCat.Presheaf.stalk (C := Ab.{u}) (F ⊗ G).presheaf x) :
    ∃ r : X.presheaf.stalk x,
      w = r • ((F ⊗ G).presheaf.germ U x hx).hom (mulSec F f m) := by
  obtain ⟨v, hv⟩ := hsurj w
  obtain ⟨r, hr⟩ := hm v
  refine ⟨r, ?_⟩
  rw [← hv, hr, mapFun_smul, mapFun_germ]
  rfl

/-! ### The product formula for the nonvanishing loci -/

/-- A section composed with a morphism of modules vanishes wherever the section does. -/
private theorem nonvanishingLocus_comp_subset {A B : X.Modules} (s : 𝟙_ X.Modules ⟶ A)
    (g : A ⟶ B) :
    nonvanishingLocus B (globalSection X B (s ≫ g)) ⊆
      nonvanishingLocus A (globalSection X A s) := by
  intro x hx
  rw [mem_nonvanishingLocus_iff] at hx ⊢
  intro hc
  exact hx ((Γgerm_globalSection_comp A B s g x).symm ▸ mapFun_mem_maximalSmul g x hc)

/-- **A product vanishes wherever its left factor does.** No invertibility hypothesis: the germ of
the product is the image of the germ of `e` under a morphism of modules, and a stalk map carries
`𝔪_x F_x` into `𝔪_x (F ⊗ G)_x`. -/
@[ega "0 5.5.3" "partial"]
theorem nonvanishingLocus_unitMul_subset_left {F G : X.Modules} (e : 𝟙_ X.Modules ⟶ F)
    (f : 𝟙_ X.Modules ⟶ G) :
    nonvanishingLocus (F ⊗ G) (globalSection X (F ⊗ G) (unitMul e f)) ⊆
      nonvanishingLocus F (globalSection X F e) :=
  nonvanishingLocus_comp_subset e (mulRight F f)

/-- **A product vanishes wherever its right factor does**, by `unitMul_eq_mulLeft` and the same
argument. -/
@[ega "0 5.5.3" "partial"]
theorem nonvanishingLocus_unitMul_subset_right {F G : X.Modules} (e : 𝟙_ X.Modules ⟶ F)
    (f : 𝟙_ X.Modules ⟶ G) :
    nonvanishingLocus (F ⊗ G) (globalSection X (F ⊗ G) (unitMul e f)) ⊆
      nonvanishingLocus G (globalSection X G f) := by
  rw [unitMul_eq_mulLeft]
  exact nonvanishingLocus_comp_subset f (mulLeft e G)

/-- **The Stacks Tag 01CY remark `X_{e ⊗ f} = X_e ∩ X_f`, for two arbitrary invertible
`𝒪_X`-modules.**

The `⊆` direction is the two lemmas above and needs no invertibility. The `⊇` direction is
`surjStalk_mulRight` together with `generates_mulSec`: at a point of `X_e ∩ X_f` the germ of `e`
generates `F_x` and multiplication by `f` is surjective on the stalk, so the germ of the product
generates `(F ⊗ G)_x`, hence avoids `𝔪_x (F ⊗ G)_x`. -/
@[ega "0 5.5.3" "special case", ega "II 4.6.13.1" "(ii)"]
theorem nonvanishingLocus_unitMul {F G : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] (e : 𝟙_ X.Modules ⟶ F) (f : 𝟙_ X.Modules ⟶ G) :
    nonvanishingLocus (F ⊗ G) (globalSection X (F ⊗ G) (unitMul e f)) =
      nonvanishingLocus F (globalSection X F e) ∩
        nonvanishingLocus G (globalSection X G f) := by
  refine Set.Subset.antisymm (Set.subset_inter
    (nonvanishingLocus_unitMul_subset_left e f)
    (nonvanishingLocus_unitMul_subset_right e f)) ?_
  rintro x ⟨he, hf⟩
  rw [mem_nonvanishingLocus_iff]
  refine notMem_maximalSmul_of_generates (F ⊗ G) x fun w => ?_
  rw [globalSection_unitMul]
  exact generates_mulSec F f (surjStalk_mulRight F f x hf) (U := ⊤) True.intro
    (globalSection X F e) (fun v => exists_smul_Γgerm F (globalSection X F e) he v) w

/-- `X_{e ⊗ f} = X_e ∩ X_f` as an equality of opens, for the consumers stated over
`Stacks.NonvanishingOpen.nonvanishingOpen`. -/
theorem nonvanishingOpen_unitMul {F G : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] (e : 𝟙_ X.Modules ⟶ F) (f : 𝟙_ X.Modules ⟶ G) :
    Stacks.NonvanishingOpen.nonvanishingOpen X (F ⊗ G)
          (globalSection X (F ⊗ G) (unitMul e f)) =
      Stacks.NonvanishingOpen.nonvanishingOpen X F (globalSection X F e) ⊓
        Stacks.NonvanishingOpen.nonvanishingOpen X G (globalSection X G f) := by
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen,
    Stacks.NonvanishingOpen.coe_nonvanishingOpen,
    Stacks.NonvanishingOpen.coe_nonvanishingOpen, nonvanishingLocus_unitMul]

end Stacks.TensorSectionNonvanishing

end
