module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Stalk
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme

/-!
# Germs of a product of sections span the stalk of a tensor product

Let `F` and `G` be `𝒪_X`-modules on a scheme `X` with `G` invertible, let `n` be a global section
of `G` and let `x` be a point where `n` does not vanish. If a family of sections `t i` of `F` over
an open `V ∋ x` has germs spanning the stalk `F_x`, then the germs at `x` of the products
`t i ⊗ₛ n|_V` span the stalk `(F ⊗ G)_x`.

## Main definitions

* `Stacks.SectionTensorFormula.mulPre`: multiplication by a global section of `G`, as a morphism
  of presheaves of modules `F.val ⟶ (F ⊗ G).val`.
* `Stacks.SectionTensorFormula.mulSec`: the same as a morphism `F ⟶ F ⊗ G` of `𝒪_X`-modules.
* `Stacks.SectionTensorFormula.preTensor`: the sectionwise tensor product of the underlying
  presheaves.

## Main results

* `Stacks.SectionTensorFormula.surjective_pstalkHom_toTensorSection`: the comparison
  `F.val ⊗ G.val ⟶ (F ⊗ G).val` is surjective on every stalk.
* `Stacks.SectionTensorFormula.surjStalk_mulSec`: multiplication by a global section of an
  invertible module is surjective on the stalk at every point where the section does not vanish.
* `Stacks.SectionTensorFormula.span_transport`: a spanning family of germs stays spanning along a
  morphism that is surjective on the stalk.
* `Stacks.SectionTensorFormula.span_germ_tensorSection_eq_top`: the germs of the products
  `t i ⊗ₛ n|_V` span the stalk, for sections `t i` of `F` over an open and a global section `n`
  of `G`.
* `Stacks.SectionTensorFormula.span_Γgerm_tensorSection_eq_top`: the same for global sections of
  `F`.

## Implementation notes

The span is taken over the stalk of the `RingCat`-valued structure sheaf, with the scoped
instance `Stacks.FinGenFromCover.ringStalkModule`, which is the ring
`AlgebraicGeometry.generates_iff_stalkwise_generates` and
`Stacks.AmpleLocalGeneration.IsFinGenOn` use.

`mulSec` is defined sectionwise rather than through the right unitor `F ≅ F ⊗ 𝒪_X`: the monoidal
structure `Stacks.SheafInternalHom.schemeMonoidalCategory` is a
`CategoryTheory.LocalizedMonoidal` lift, and its right unitor has no sectionwise formula here.

Only surjectivity of the comparison `F_x ⊗ G_x → (F ⊗ G)_x` is used, never its injectivity, so
the stalk comparison of [Stacks, Tag 01CB] is not needed: a germ of a section of `F ⊗ G` comes
from a germ of a section of the sectionwise tensor product, a finite sum of pure tensors, and each
pure tensor is handled by `Stacks.SectionProduct.exists_smul_Γgerm`, which needs `n` to be a
global section.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample Stacks.SheafOfModules.TensorSheafification
open Stacks.SectionProduct
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-! ### Restriction of a global section -/

/-- The germ of the restriction of a global section is its germ. -/
lemma germ_resTop (G : X.Modules) (n : Γ(G, ⊤)) (U : X.Opens) (x : X) (hx : x ∈ U) :
    (G.presheaf.germ U x hx).hom (Stacks.SectionExtension.resTop U n) =
      (G.presheaf.Γgerm x).hom n :=
  TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (le_top : U ≤ ⊤)) x hx n

/-! ### Multiplication by a global section, as a morphism -/

/-- **Multiplication by a global section `n : Γ(G, ⊤)`, at the level of presheaves of modules.**
Over an open `U` it is `m ↦ m ⊗ₛ n|_U`. -/
def mulPre (F G : X.Modules) (n : Γ(G, ⊤)) : F.val ⟶ (F ⊗ G).val where
  app U := ModuleCat.ofHom
    { toFun := fun m => tensorSection F G m (Stacks.SectionExtension.resTop U.unop n)
      map_add' := fun m m' => tensorSection_add_left F G m m' _
      map_smul' := fun r m => tensorSection_smul_left F G r m _ }
  naturality := by
    intro U V f
    ext m
    change tensorSection F G (F.presheaf.map f m) (Stacks.SectionExtension.resTop (unop V) n)
      = (F ⊗ G).presheaf.map f
        (tensorSection F G m (Stacks.SectionExtension.resTop (unop U) n))
    exact ((map_tensorSection F G f.unop m (Stacks.SectionExtension.resTop (unop U) n)).trans
      (congrArg (fun y => tensorSection F G (F.presheaf.map f.unop.op m) y)
        (Stacks.SectionExtension.res_resTop n f.unop.le))).symm

/-- **Multiplication by a global section `n : Γ(G, ⊤)`, as a morphism `F ⟶ F ⊗ G`** of
`𝒪_X`-modules. -/
def mulSec (F G : X.Modules) (n : Γ(G, ⊤)) : F ⟶ F ⊗ G :=
  ⟨mulPre F G n⟩

/-- **The section formula for `mulSec`**: over `U` it multiplies by `n|_U`. -/
lemma mulSec_app (F G : X.Modules) (n : Γ(G, ⊤)) (U : X.Opens) (m : Γ(F, U)) :
    (mulSec F G n).app U m = tensorSection F G m (Stacks.SectionExtension.resTop U n) := rfl

/-- Restricting a global section to the top open set does nothing. -/
private lemma resTop_top (G : X.Modules) (n : Γ(G, ⊤)) :
    Stacks.SectionExtension.resTop (⊤ : X.Opens) n = n := by
  simp [Stacks.SectionExtension.resTop]

/-- **The section formula for `mulSec` on global sections.** -/
lemma mulSec_app_top (F G : X.Modules) (n : Γ(G, ⊤)) (m : Γ(F, ⊤)) :
    (mulSec F G n).app ⊤ m = tensorSection F G m n := by
  rw [mulSec_app, resTop_top]

/-! ### The stalk map of `mulSec` is surjective where the section does not vanish -/

/-- The germ at `x` of a product `m ⊗ₛ q` of sections over `U` lies in the image of the stalk map
of `mulSec F G n`, when `G` is invertible and `n` does not vanish at `x`. -/
lemma mem_range_germ_tensorSection (F G : X.Modules) [IsInvertibleModule X G] (n : Γ(G, ⊤))
    {x : X} (hx : x ∈ nonvanishingLocus G n) (U : X.Opens) (hxU : x ∈ U)
    (m : Γ(F, U)) (q : Γ(G, U)) :
    ((F ⊗ G).presheaf.germ U x hxU).hom (tensorSection F G m q)
      ∈ LinearMap.range (Stacks.ModuleStalk.map (mulSec F G n) x) := by
  obtain ⟨r, hr⟩ := exists_smul_Γgerm G n hx ((G.presheaf.germ U x hxU).hom q)
  obtain ⟨U₁, hxU₁, r₀, hr₀⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  set W : X.Opens := U ⊓ U₁ with hW
  have hxW : x ∈ W := ⟨hxU, hxU₁⟩
  set a : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_right : W ≤ U₁)).op r₀ with ha
  have hgerm_a : (X.presheaf.germ W x hxW).hom a = r :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x hxW r₀).trans hr₀
  have hq1 : (G.presheaf.germ U x hxU).hom q
      = (G.presheaf.germ W x hxW).hom (a • Stacks.SectionExtension.resTop W n) := by
    rw [Stacks.ModuleStalk.germ_smul, hgerm_a, germ_resTop, hr]
  obtain ⟨W', hxW', iU, iW, heq⟩ :=
    TopCat.Presheaf.germ_eq G.presheaf x hxU hxW q (a • Stacks.SectionExtension.resTop W n) hq1
  set b : Γ(X, W') := X.presheaf.map iW.op a with hb
  have hqres : G.presheaf.map iU.op q = b • Stacks.SectionExtension.resTop W' n := by
    refine heq.trans (Eq.trans (PresheafOfModules.map_smul G.val iW.op a
      (Stacks.SectionExtension.resTop W n)) ?_)
    exact congrArg (fun y : Γ(G, W') => b • y) (Stacks.SectionExtension.res_resTop n iW.le)
  refine ⟨(F.presheaf.germ W' x hxW').hom (b • F.presheaf.map iU.op m), ?_⟩
  rw [Stacks.ModuleStalk.map_apply, Stacks.ModuleStalk.mapFun_germ, mulSec_app,
    tensorSection_smul_left, ← TopCat.Presheaf.germ_res_apply (F ⊗ G).presheaf iU x hxW'
    (tensorSection F G m q), map_tensorSection, hqres, tensorSection_smul_right]

/-- The sectionwise tensor product of the presheaves of modules underlying `F` and `G`. -/
abbrev preTensor (F G : X.Modules) :
    PresheafOfModules (structureRingPresheaf X.presheaf) :=
  (F.val : PresheafOfModules (structureRingPresheaf X.presheaf)) ⊗
    (G.val : PresheafOfModules (structureRingPresheaf X.presheaf))

/-- **The comparison `F.val ⊗ G.val ⟶ (F ⊗ G).val` is surjective on every stalk.** -/
theorem surjective_pstalkHom_toTensorSection (F G : X.Modules) (x : X) :
    Function.Surjective
      (pstalkHom (toTensorSection X.presheaf (schemeSheafCondition X) F G) x) := by
  have hIso : IsIso (C := PresheafOfModulesOfCommRing X.presheaf)
      (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val :=
    (tensorPresheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).isIso_hom
  intro z
  obtain ⟨y, hy⟩ := (pstalkHom_bijective_of_isIso
    (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val x).2 z
  obtain ⟨v, hv⟩ := (pstalkHom_toSheafify_bijective (preTensor F G) x).2 y
  exact ⟨v, (pstalkHom_comp
    (toSheafify X.presheaf (schemeSheafCondition X) (preTensor F G))
    (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val x v).trans
    ((congrArg (pstalkHom
      (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val x) hv).trans hy)⟩

/-- Every germ of a section of the sectionwise tensor product, read in `F ⊗ G`, lies in the image
of the stalk map of `mulSec`. -/
lemma mem_range_germ_tensorSectionLinear (F G : X.Modules) [IsInvertibleModule X G]
    (n : Γ(G, ⊤)) {x : X} (hx : x ∈ nonvanishingLocus G n) (U : X.Opens) (hxU : x ∈ U)
    (w : TensorProduct Γ(X, U) Γ(F, U) Γ(G, U)) :
    ((F ⊗ G).presheaf.germ U x hxU).hom (tensorSectionLinear F G U w)
      ∈ LinearMap.range (Stacks.ModuleStalk.map (mulSec F G n) x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul m q => exact mem_range_germ_tensorSection F G n hx U hxU m q
  | add w w' hw hw' =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hw hw'

/-- **Multiplication by a global section of an invertible module is surjective on the stalk at
every point where the section does not vanish.** -/
theorem surjStalk_mulSec (F G : X.Modules) [IsInvertibleModule X G] (n : Γ(G, ⊤)) {x : X}
    (hx : x ∈ nonvanishingLocus G n) : SurjStalk (mulSec F G n) x := by
  intro z
  obtain ⟨z', hz'⟩ := surjective_pstalkHom_toTensorSection F G x z
  obtain ⟨U, hxU, w, rfl⟩ := exists_pgerm_eq (preTensor F G) z'
  obtain ⟨v, hv⟩ := mem_range_germ_tensorSectionLinear F G n hx U hxU w
  exact ⟨v, hv.trans ((pstalkHom_pgerm (toTensorSection X.presheaf (schemeSheafCondition X) F G)
    x U hxU w).symm.trans hz')⟩

/-! ### The span statement -/

/-- **Transport of a spanning family of germs along a morphism surjective on the stalk.** -/
theorem span_transport {F H : X.Modules} (μ : F ⟶ H) {x : X} (hsurj : SurjStalk μ x)
    (V : X.Opens) (hxV : x ∈ V) {I : Type u} (t : I → Γ(F, V))
    (hspan : Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i => (F.presheaf.germ V x hxV).hom (t i)) = ⊤) :
    Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i => (H.presheaf.germ V x hxV).hom (μ.app V (t i))) = ⊤ := by
  set R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat) with hR
  set L := ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map μ).hom with hL
  have himg : ∀ i, L ((F.presheaf.germ V x hxV).hom (t i))
      = (H.presheaf.germ V x hxV).hom (μ.app V (t i)) :=
    fun i => Stacks.ModuleStalk.mapFun_germ μ x V hxV (t i)
  have hspan' : Submodule.span R
      (M := ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj F : Type u))
      (Set.range fun i => (F.presheaf.germ V x hxV).hom (t i)) = ⊤ := hspan
  have hrange : (Set.range fun i => (H.presheaf.germ V x hxV).hom (μ.app V (t i)))
      = L '' (Set.range fun i => (F.presheaf.germ V x hxV).hom (t i)) := by
    apply Set.eq_of_subset_of_subset
    · rintro - ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, himg i⟩
    · rintro - ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (himg i).symm⟩
  have key : Submodule.span R
      (M := ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj H : Type u))
      (L '' (Set.range fun i => (F.presheaf.germ V x hxV).hom (t i))) = ⊤ := by
    rw [Submodule.span_image, hspan', Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  exact hrange ▸ key

/-- Let `G` be an invertible `𝒪_X`-module, `n` a global section of `G` not vanishing at `x`, and
`t : I → Γ(F, V)` a family of sections over an open `V ∋ x` whose germs span the stalk of `F` at
`x`. Then the germs at `x` of the products `t i ⊗ₛ n|_V` span the stalk of `F ⊗ G` at `x`. -/
theorem span_germ_tensorSection_eq_top (F G : X.Modules) [IsInvertibleModule X G]
    {I : Type u} (V : X.Opens) (t : I → Γ(F, V)) (n : Γ(G, ⊤)) {x : X} (hxV : x ∈ V)
    (hx : x ∈ nonvanishingLocus G n)
    (hspan : Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i => (F.presheaf.germ V x hxV).hom (t i)) = ⊤) :
    Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i => ((F ⊗ G).presheaf.germ V x hxV).hom
        (tensorSection F G (t i) (Stacks.SectionExtension.resTop V n))) = ⊤ :=
  span_transport (mulSec F G n) (surjStalk_mulSec F G n hx) V hxV t hspan

/-- Let `G` be an invertible `𝒪_X`-module, `n` a global section of `G` not vanishing at `x`, and
`t : I → Γ(F, ⊤)` global sections of `F` whose germs span the stalk of `F` at `x`. Then the germs
at `x` of the products `t i ⊗ₛ n` span the stalk of `F ⊗ G` at `x`. -/
theorem span_Γgerm_tensorSection_eq_top (F G : X.Modules) [IsInvertibleModule X G]
    {I : Type u} (t : I → Γ(F, ⊤)) (n : Γ(G, ⊤)) {x : X}
    (hx : x ∈ nonvanishingLocus G n)
    (hspan : Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i => (F.presheaf.Γgerm x).hom (t i)) = ⊤) :
    Submodule.span (R := (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
      (Set.range fun i =>
        ((F ⊗ G).presheaf.Γgerm x).hom (tensorSection F G (t i) n)) = ⊤ := by
  have h := span_germ_tensorSection_eq_top F G ⊤ t n (x := x) trivial hx hspan
  rwa [resTop_top] at h

end Stacks.SectionTensorFormula

end
