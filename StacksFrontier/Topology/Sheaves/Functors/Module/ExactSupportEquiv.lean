module

public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportDescend
import StacksCore.Tactic.StacksAttribute

/-!
# The sections of sheaf Hom with exact support

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces with kernel ideal
`ℐ = ker(𝒪_X ⟶ i_* 𝒪_Z)`, and let `F` be an `𝒪_X`-module.  If `V ⊆ Z` is the inverse image of
`U ⊆ X`, this file identifies the sections over `V` of the sheaf Hom with exact support of
Tag 0A75 with the sections of `F` over `U` annihilated sheaf-locally by `ℐ`.

A section over `V` is a morphism `ψ : (i_* 𝒪_Z)|_W ⟶ F|_W` of `𝒪_X|_W`-modules, where
`W = i_! V` is the largest open of `X` with inverse image `V`; the identification sends `ψ` to
`ψ(1)|_U`.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.sectionsSheafHomExactSupportEquiv`, in the namespace
  `RingedSpaceModuleAdjunction`, is the identification itself.
* `ClosedQuotientMorphismOfRingedSpaces.sectionsSheafHomExactSupportEquiv_apply` identifies it
  with the counit of the exact-support adjunction.
* `ClosedQuotientMorphismOfRingedSpaces.sectionsSheafHomExactSupportEquiv_naturality` and
  `ClosedQuotientMorphismOfRingedSpaces.sectionsSheafHomExactSupportEquiv_restrict` record that
  it is natural in the module and compatible with restriction, so that it is an identification
  of sheaves rather than an objectwise choice.

## Implementation notes

Everything is phrased through `evalHom`, the evaluation of a section of the internal Hom at an
open subset of `W`.  Its three properties — semilinearity over `𝒪_X`, compatibility with
restriction, and the fact that a morphism of presheaves of modules on the slice `Over W` is
determined by its values — are the naturality and linearity of `ψ` read off at the slice objects
`Over.mk (homOfLE _)`, which in a poset of opens exhaust the slice category up to definitional
equality.  Nothing here needs the coherence isomorphisms of Tag 0932: the one place where
restriction in the internal Hom appears, `invSecVal_coextRestrFun`, is obtained from the
naturality of `Stacks.PresheafOfModules.CoextendScalars.invSecPresheaf` at the identity morphism.

Surjectivity is where the content lies.  A section annihilated by `ℐ` over `U` is first extended
by zero to `W` (`exists_mem_sections_restrict_eq`), and the morphism `ψ` is then assembled from
the descended action `descendedSmul`, whose construction is the one use of local surjectivity of
the comorphism.  Injectivity uses the same covering `W ≤ U ⊔ (W ∖ i(Z))`: off the image of `Z`
the sheaf `i_* 𝒪_Z` vanishes, so there `ψ` has nothing to say.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction

/-! ### Evaluation at `1` in the internal Hom of Tag 0932 -/

section InternalHom

variable {C : Type u} [Category.{u} C] {O O' : Cᵒᵖ ⥤ RingCat.{u}}

private lemma coextObj_presheaf_map_apply (φ : O ⟶ O') (F : PresheafOfModules.{u} O)
    {A B : Cᵒᵖ} (f : A ⟶ B) (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec φ F A) :
    (Stacks.PresheafOfModules.CoextendScalars.coextObj φ F).presheaf.map f ψ =
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun φ F f ψ :=
  rfl

private lemma invSecPresheaf_app_apply (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (A : Cᵒᵖ)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec φ F A) :
    (Stacks.PresheafOfModules.CoextendScalars.invSecPresheaf φ
      (Stacks.PresheafOfModules.CoextendScalars.coextObj φ F) F (𝟙 _)).app A ψ =
      Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A ψ :=
  rfl

private lemma presheaf_map_apply (F : PresheafOfModules.{u} O) {A B : Cᵒᵖ} (f : A ⟶ B)
    (x : F.obj A) : F.presheaf.map f x = F.map f x :=
  rfl

/-- Evaluation at `1` is additive. -/
lemma invSecVal_add (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (A : Cᵒᵖ)
    (ψ χ : Stacks.PresheafOfModules.CoextendScalars.coextSec φ F A) :
    Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A (ψ + χ) =
      Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A ψ +
        Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A χ :=
  Stacks.PresheafOfModules.CoextendScalars.invSec_add φ
    (Stacks.PresheafOfModules.CoextendScalars.coextObj φ F) F (𝟙 _) A ψ χ

/-- Evaluation at `1` commutes with restriction in the internal Hom.  This is the naturality of
`Stacks.PresheafOfModules.CoextendScalars.invSecPresheaf` at the identity morphism of the internal
  Hom. -/
lemma invSecVal_coextRestrFun (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {A B : Cᵒᵖ} (f : A ⟶ B)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec φ F A) :
    Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F B
      (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun φ F f ψ) =
      F.map f (Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A ψ) := by
  have h := NatTrans.naturality_apply
    (Stacks.PresheafOfModules.CoextendScalars.invSecPresheaf φ
      (Stacks.PresheafOfModules.CoextendScalars.coextObj φ F) F (𝟙 _)) f ψ
  rw [coextObj_presheaf_map_apply, invSecPresheaf_app_apply, invSecPresheaf_app_apply,
    presheaf_map_apply] at h
  exact h

/-- Evaluation at `1` is natural in the module: postcomposing a local homomorphism with `η` and
evaluating at `1` is evaluating at `1` and then applying `η`. -/
lemma invSecVal_coextFunMapFun (φ : O ⟶ O') {F G : PresheafOfModules.{u} O} (η : F ⟶ G)
    (A : Cᵒᵖ) (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec φ F A) :
    Stacks.PresheafOfModules.CoextendScalars.invSecVal φ G A
      (Stacks.PresheafOfModules.CoextendScalars.coextFunMapFun φ η A ψ) =
      η.app A (Stacks.PresheafOfModules.CoextendScalars.invSecVal φ F A ψ) :=
  rfl

end InternalHom

namespace ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The two open subsets `U` and `i_! i⁻¹ U` -/

/-- An open subset of `X` is contained in the largest open with the same inverse image. -/
lemma le_opensFunctor_obj_of_opensMap_eq {U : Opens S.X} {V : Opens S.Z}
    (hUV : (opensMap S.i).obj U = V) : U ≤ S.opensFunctor.obj V :=
  S.le_opensFunctor_obj_iff.2 (le_of_eq hUV)

/-- The largest open with inverse image `V` is covered by any open with inverse image `V`
together with the complement of the image of `Z`. -/
lemma opensFunctor_obj_le_sup_of_opensMap_eq {U : Opens S.X} {V : Opens S.Z}
    (hUV : (opensMap S.i).obj U = V) :
    S.opensFunctor.obj V ≤ U ⊔ (S.opensFunctor.obj V ⊓ S.opensComplRange) := by
  subst hUV
  exact S.opensFunctor_opensMap_le_sup U

/-! ### Evaluating a section of the internal Hom -/

section Evaluation

variable (F : SheafOfModules.{u} (structureSheafRing S.X)) {W : Opens S.X}

/-- The value of a section `ψ` of the internal Hom `SheafHom_{𝒪_X}(i_* 𝒪_Z, F)` over `W` at a
section `b` of `i_* 𝒪_Z` over an open `U ⊆ W`.  Concretely `ψ` is a morphism of presheaves of
modules on the slice category `Over W`, and this is its component at the slice object `U`. -/
noncomputable def evalHom (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom
  F.val (op W))
    {U : Opens S.X} (hUW : U ≤ W) (b : S.pushedRingSheaf.obj.obj (op U)) : F.val.obj (op U) :=
  ψ.app (op (Over.mk (homOfLE hUW))) b

/-- Evaluating at `W` itself on the section `1` is
  `Stacks.PresheafOfModules.CoextendScalars.invSecVal`, the map that the
counit of the exact-support adjunction is given by. -/
lemma evalHom_le_refl_one (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom
  F.val (op W)) :
    S.evalHom F ψ (le_refl W) 1 =
      Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W) ψ :=
  rfl

/-- Evaluation is additive, so it kills the zero section of `i_* 𝒪_Z`. -/
lemma evalHom_zero (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val
  (op W))
    {U : Opens S.X} (hUW : U ≤ W) : S.evalHom F ψ hUW 0 = 0 :=
  map_zero _

/-- Evaluation of the zero morphism is zero. -/
lemma evalHom_zero_hom {U : Opens S.X} (hUW : U ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op U)) :
    S.evalHom F (0 : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val (op
      W)) hUW b = 0 :=
  rfl

/-- Evaluation commutes with restriction: this is the naturality of `ψ` along the morphism
`U' ⟶ U` of the slice category `Over W`. -/
lemma evalHom_restrict (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom
  F.val (op W))
    {U U' : Opens S.X} (hUW : U ≤ W) (h : U' ≤ U) (hU'W : U' ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op U)) :
    F.val.map (homOfLE h).op (S.evalHom F ψ hUW b) =
      S.evalHom F ψ hU'W (S.pushedRingSheaf.obj.map (homOfLE h).op b) :=
  (PresheafOfModules.naturality_apply ψ
    (Over.homMk (homOfLE h) : Over.mk (homOfLE hU'W) ⟶ Over.mk (homOfLE hUW)).op b).symm

/-- Evaluation is semilinear over the structure sheaf: this is the `𝒪_X|_W`-linearity of `ψ`,
the scalar action on `i_* 𝒪_Z` being multiplication through the comorphism. -/
lemma evalHom_smul (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val
  (op W))
    {U : Opens S.X} (hUW : U ≤ W) (r : (structureSheafRing S.X).obj.obj (op U))
    (b : S.pushedRingSheaf.obj.obj (op U)) :
    S.evalHom F ψ hUW (S.pushedRingHom.hom.app (op U) r * b) = r • S.evalHom F ψ hUW b :=
  (ψ.app (op (Over.mk (homOfLE hUW)))).hom.map_smul r b

/-- A section of the internal Hom over `W` is determined by its evaluations: in a poset of
opens, the slice objects `Over.mk (homOfLE _)` are all of `Over W`. -/
lemma coextSec_ext {ψ χ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom
  F.val (op W)}
    (h : ∀ (U : Opens S.X) (hUW : U ≤ W) (b : S.pushedRingSheaf.obj.obj (op U)),
      S.evalHom F ψ hUW b = S.evalHom F χ hUW b) : ψ = χ :=
  PresheafOfModules.hom_ext fun T =>
    ModuleCat.hom_ext (LinearMap.ext fun b => h T.unop.left (leOfHom T.unop.hom) b)

/-- Restricting the value of `ψ` at `1` is evaluating `ψ` at `1` over the smaller open. -/
lemma map_invSecVal (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val
  (op W))
    {U : Opens S.X} (hUW : U ≤ W) :
    F.val.map (homOfLE hUW).op
        (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W) ψ) =
      S.evalHom F ψ hUW 1 := by
  rw [← S.evalHom_le_refl_one F ψ, S.evalHom_restrict F ψ (le_refl W) hUW hUW 1, map_one]

/-- The value of `ψ` at the image of a section `a` of `𝒪_X` is `a` acting on the value at `1`. -/
private lemma evalHom_pushedRingHom_app (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec
  S.pushedRingHom.hom F.val (op W))
    {U : Opens S.X} (hUW : U ≤ W) (a : (structureSheafRing S.X).obj.obj (op U)) :
    S.evalHom F ψ hUW (S.pushedRingHom.hom.app (op U) a) = a • S.evalHom F ψ hUW 1 :=
  (congrArg (S.evalHom F ψ hUW) (mul_one _).symm).trans (S.evalHom_smul F ψ hUW a 1)

/-- Restricting the value of `ψ` at `1` twice is evaluating `ψ` at `1` over the smaller open. -/
private lemma map_map_invSecVal (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec
  S.pushedRingHom.hom F.val (op W))
    {U C : Opens S.X} (hUW : U ≤ W) (hCU : C ≤ U) :
    F.val.map (homOfLE hCU).op (F.val.map (homOfLE hUW).op
      (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W) ψ)) =
      S.evalHom F ψ (hCU.trans hUW) 1 := by
  rw [map_map_of_le F.val hUW hCU (hCU.trans hUW), S.map_invSecVal F ψ (hCU.trans hUW)]

/-- A section of the kernel ideal kills the value of `ψ` at `1`. -/
lemma smul_evalHom_one (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom
  F.val (op W))
    {U : Opens S.X} (hUW : U ≤ W) (a : (structureSheafRing S.X).obj.obj (op U))
    (ha : a ∈ S.kernelIdeal U) : a • S.evalHom F ψ hUW 1 = 0 := by
  rw [← S.evalHom_pushedRingHom_app F ψ hUW a, show S.pushedRingHom.hom.app (op U) a = 0 from ha]
  exact S.evalHom_zero F ψ hUW

/-- Wherever a section `b` of `i_* 𝒪_Z` lifts to a section `a` of `𝒪_X`, the value of `ψ` at `b`
is `a` acting on the value of `ψ` at `1`. -/
lemma evalHom_eq_smul_evalHom_one (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec
  S.pushedRingHom.hom F.val (op W))
    {U C : Opens S.X} (hUW : U ≤ W) (hCU : C ≤ U) (hCW : C ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op U)) (a : (structureSheafRing S.X).obj.obj (op C))
    (ha : S.pushedRingHom.hom.app (op C) a = S.pushedRingSheaf.obj.map (homOfLE hCU).op b) :
    F.val.map (homOfLE hCU).op (S.evalHom F ψ hUW b) = a • S.evalHom F ψ hCW 1 := by
  rw [S.evalHom_restrict F ψ hUW hCU hCW b, ← ha]
  exact S.evalHom_pushedRingHom_app F ψ hCW a

/-- The value of `ψ` at `1`, restricted to an open subset, is annihilated sheaf-locally by the
kernel ideal. -/
lemma map_invSecVal_mem_sections (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec
  S.pushedRingHom.hom F.val (op W))
    {U : Opens S.X} (hUW : U ≤ W) :
    F.val.map (homOfLE hUW).op (Stacks.PresheafOfModules.CoextendScalars.invSecVal
      S.pushedRingHom.hom F.val (op W) ψ) ∈
      S.sectionsLocallyAnnihilatedByKernelIdeal F U := fun _ hU'U a ha =>
  (congrArg (a • ·) (S.map_map_invSecVal F ψ hUW hU'U)).trans
    (S.smul_evalHom_one F ψ (hU'U.trans hUW) a ha)

/-! ### The morphism attached to an annihilated section -/

/-- The morphism `(i_* 𝒪_Z)|_W ⟶ F|_W` of `𝒪_X|_W`-modules attached to a section of `F` over `W`
annihilated sheaf-locally by the kernel ideal: on an open `U ⊆ W` it is the descended action
`b ↦ b · r|_U`. -/
noncomputable def descendedHom (r : F.val.obj (op W))
    (hr : r ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W) :
    Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val (op W) :=
  PresheafOfModules.homMk
    { app := fun T => AddCommGrpCat.ofHom
        (show (S.pushedRingSheaf.obj.obj (op T.unop.left) : Type u) →+
            (F.val.obj (op T.unop.left) : Type u) from
          { toFun := fun b => S.descendedSmul F r hr (leOfHom T.unop.hom) b
            map_zero' := S.descendedSmul_zero F r hr (leOfHom T.unop.hom)
            map_add' := S.descendedSmul_add F r hr (leOfHom T.unop.hom) })
      naturality := fun {T _} m => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun b =>
        S.descendedSmul_restrict F r hr (leOfHom T.unop.hom) (leOfHom m.unop.left) b }
    fun T r' b => S.descendedSmul_pushedRingHom_mul F r hr (leOfHom T.unop.hom) r' b

/-- `descendedHom` evaluates to the descended action. -/
lemma evalHom_descendedHom (r : F.val.obj (op W))
    (hr : r ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W) {U : Opens S.X} (hUW : U ≤ W)
    (b : S.pushedRingSheaf.obj.obj (op U)) :
    S.evalHom F (S.descendedHom F r hr) hUW b = S.descendedSmul F r hr hUW b :=
  rfl

/-- The value of `descendedHom` at `1` is the section it was built from. -/
lemma invSecVal_descendedHom (r : F.val.obj (op W))
    (hr : r ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W) :
    Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W)
      (S.descendedHom F r hr) = r := by
  rw [← S.evalHom_le_refl_one F (S.descendedHom F r hr),
    S.evalHom_descendedHom F r hr (le_refl W) 1, S.descendedSmul_one F r hr]

/-! ### The identification of sections -/

/-- A section of the internal Hom over `W` whose value at `1` dies on `U` is zero, provided `U`
covers `W` up to the complement of the image of `Z`. -/
lemma eq_zero_of_map_invSecVal_eq_zero {U : Opens S.X} (hUW : U ≤ W)
    (hcover : W ≤ U ⊔ (W ⊓ S.opensComplRange))
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val (op W))
    (h0 : F.val.map (homOfLE hUW).op
      (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W) ψ) = 0) :
        ψ = 0 := by
  refine S.coextSec_ext F fun U₀ hU₀W b => ?_
  rw [S.evalHom_zero_hom F hU₀W b]
  refine S.eq_of_locally_eq_of_mem F U₀ _ 0 fun x hx => ?_
  rcases hcover (hU₀W hx) with hxU | hxB
  · obtain ⟨C, hCU₀U, hxC, a, ha⟩ := S.exists_lift_of_mem (U₀ ⊓ U)
      (S.pushedRingSheaf.obj.map (homOfLE (inf_le_left : U₀ ⊓ U ≤ U₀)).op b) ⟨hx, hxU⟩
    have hCU₀ : C ≤ U₀ := hCU₀U.trans inf_le_left
    have hCU : C ≤ U := hCU₀U.trans inf_le_right
    have hCW : C ≤ W := hCU.trans hUW
    refine ⟨C, hCU₀, hxC, ?_⟩
    have ha' : S.pushedRingHom.hom.app (op C) a =
        S.pushedRingSheaf.obj.map (homOfLE hCU₀).op b := by
      rw [ha, S.pushedRingSheaf_map_map (inf_le_left : U₀ ⊓ U ≤ U₀) hCU₀U hCU₀]
    have h1 : S.evalHom F ψ hCW 1 = 0 := by
      rw [← S.map_map_invSecVal F ψ hUW hCU, h0]
      exact map_zero _
    rw [S.evalHom_eq_smul_evalHom_one F ψ hU₀W hCU₀ hCW b a ha', h1, smul_zero]
    exact (map_zero _).symm
  · have hCU₀ : U₀ ⊓ (W ⊓ S.opensComplRange) ≤ U₀ := inf_le_left
    have hCW : U₀ ⊓ (W ⊓ S.opensComplRange) ≤ W := inf_le_left.trans hU₀W
    refine ⟨U₀ ⊓ (W ⊓ S.opensComplRange), hCU₀, ⟨hx, hxB⟩, ?_⟩
    rw [S.evalHom_restrict F ψ hU₀W hCU₀ hCW b,
      S.pushedRingSheaf_eq_zero_of_le_opensComplRange
        (inf_le_right.trans inf_le_right) (S.pushedRingSheaf.obj.map (homOfLE hCU₀).op b),
      S.evalHom_zero F ψ hCW]
    exact (map_zero _).symm

/-- Evaluating at `1` and restricting is additive. -/
lemma map_invSecVal_add {U : Opens S.X} (hUW : U ≤ W)
    (ψ χ : Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val (op W)) :
    F.val.map (homOfLE hUW).op
        (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W)
          (ψ + χ)) =
      F.val.map (homOfLE hUW).op
          (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W) ψ) +
        F.val.map (homOfLE hUW).op
          (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op W)
            χ) := by
  rw [invSecVal_add]
  exact map_add _ _ _

/-- The map `ψ ↦ ψ(1)|_U` from sections of the internal Hom over `i_! V` to the sections of `F`
over `U` annihilated sheaf-locally by the kernel ideal. -/
noncomputable def sectionsHom (U : Opens S.X) (V : Opens S.Z)
    (hUV : (opensMap S.i).obj U = V) :
    Stacks.PresheafOfModules.CoextendScalars.coextSec S.pushedRingHom.hom F.val (op
      (S.opensFunctor.obj V)) →+
      S.sectionsLocallyAnnihilatedByKernelIdeal F U :=
  AddMonoidHom.mk'
    (fun ψ => ⟨F.val.map (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hUV)).op
        (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op
          (S.opensFunctor.obj V)) ψ),
      S.map_invSecVal_mem_sections F ψ (S.le_opensFunctor_obj_of_opensMap_eq hUV)⟩)
    fun ψ χ =>
      Subtype.ext (S.map_invSecVal_add F (S.le_opensFunctor_obj_of_opensMap_eq hUV) ψ χ)

/-- `sectionsHom` is a bijection.  Injectivity uses that `i_* 𝒪_Z` vanishes off the image of `Z`,
so that a section of the internal Hom is determined by its values on `U`; surjectivity extends an
annihilated section from `U` to `i_! V` and uses the descended action. -/
lemma bijective_sectionsHom (U : Opens S.X) (V : Opens S.Z)
    (hUV : (opensMap S.i).obj U = V) : Function.Bijective (S.sectionsHom F U V hUV) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ψ hψ =>
    S.eq_zero_of_map_invSecVal_eq_zero F (S.le_opensFunctor_obj_of_opensMap_eq hUV)
      (S.opensFunctor_obj_le_sup_of_opensMap_eq hUV) ψ (congrArg Subtype.val hψ), fun t => ?_⟩
  obtain ⟨r, hr, hrt⟩ := S.exists_mem_sections_restrict_eq F
    (S.le_opensFunctor_obj_of_opensMap_eq hUV)
    (S.opensFunctor_obj_le_sup_of_opensMap_eq hUV) t.1 t.2
  exact ⟨S.descendedHom F r hr, Subtype.ext <|
    (congrArg (F.val.map (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hUV)).op)
      (S.invSecVal_descendedHom F r hr)).trans hrt⟩

/-- **Stacks Project, Tag 0A75 (sections).** If `V ⊆ Z` is the inverse image of `U ⊆ X`, sections
over `V` of sheaf Hom with exact support are canonically the sections of `F` over `U` annihilated
by the kernel ideal.  The map is `ψ ↦ ψ(1)|_U`. -/
@[stacks 0A75 "the description of sections"]
noncomputable def sectionsSheafHomExactSupportEquiv (U : Opens S.X) (V : Opens S.Z)
    (hUV : (opensMap S.i).obj U = V) :
    ((S.sheafHomExactSupport.obj F).val.obj (op V) : Type u) ≃+
      S.sectionsLocallyAnnihilatedByKernelIdeal F U :=
  AddEquiv.ofBijective (S.sectionsHom F U V hUV) (S.bijective_sectionsHom F U V hUV)

/-- The identification of sections sends `ψ` to `ψ(1)|_U`. -/
lemma sectionsSheafHomExactSupportEquiv_apply_coe (U : Opens S.X) (V : Opens S.Z)
    (hUV : (opensMap S.i).obj U = V) (ψ : (S.sheafHomExactSupport.obj F).val.obj (op V)) :
    (S.sectionsSheafHomExactSupportEquiv F U V hUV ψ).1 =
      F.val.map (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hUV)).op
        (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op
          (S.opensFunctor.obj V)) ψ) :=
  rfl

/-- The internal Hom identification of Tag 0A75 is, on sections over `U`, restriction from
`i_! i⁻¹ U` to `U` inside the internal Hom. -/
lemma modulePushforwardSheafHomExactSupportIsoHomSheaf_hom_app_val_app (U : Opens S.X)
    (t : ((modulePushforward S.i).obj (S.sheafHomExactSupport.obj F)).val.obj (op U)) :
    (S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom.app F).val.app (op U) t =
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun S.pushedRingHom.hom F.val
        (S.opensAdjunction.unit.app U).op t :=
  rfl

end Evaluation

/-! ### The characterisation by the counit, and the two naturalities -/

/-- **Stacks Project, Tag 0A75.** The section equivalence is the map induced by the adjunction
counit; equivalently, after the internal Hom identification it evaluates a local homomorphism
at `1`. -/
@[stacks 0A75 "evaluation characterization of the description of sections"]
theorem sectionsSheafHomExactSupportEquiv_apply
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X) (V : Opens S.Z)
    (hUV : (opensMap S.i).obj U = V)
    (s : (S.sheafHomExactSupport.obj F).val.obj (op V)) :
    (S.sectionsSheafHomExactSupportEquiv F U V hUV s).1 =
      (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op U)
        (by
          change (S.sheafHomExactSupport.obj F).val.obj
            (op ((opensMap S.i).obj U))
          exact hUV.symm ▸ s) := by
  subst hUV
  refine ((invSecVal_coextRestrFun S.pushedRingHom.hom F.val
    (S.opensAdjunction.unit.app U).op s).symm).trans ?_
  refine Eq.trans ?_ (S.modulePushforwardSheafHomExactSupportAdjunction_counit_app F U s).symm
  exact congrArg (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op
    U))
    (S.modulePushforwardSheafHomExactSupportIsoHomSheaf_hom_app_val_app F U s).symm

/-- **Stacks Project, Tag 0A75.** The section identification for sheaf Hom with exact support is
natural in the `𝒪_X`-module. -/
@[stacks 0A75 "naturality of the description of sections"]
theorem sectionsSheafHomExactSupportEquiv_naturality
    {F G : SheafOfModules.{u} (structureSheafRing S.X)} (f : F ⟶ G)
    (U : Opens S.X) (V : Opens S.Z) (hUV : (opensMap S.i).obj U = V)
    (s : (S.sheafHomExactSupport.obj F).val.obj (op V)) :
    ((S.sectionsSheafHomExactSupportEquiv G U V hUV
      ((S.sheafHomExactSupport.map f).val.app (op V) s)).1) =
        f.val.app (op U) ((S.sectionsSheafHomExactSupportEquiv F U V hUV s).1) := by
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply f.val
    (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hUV)).op
    (Stacks.PresheafOfModules.CoextendScalars.invSecVal S.pushedRingHom.hom F.val (op
      (S.opensFunctor.obj V)) s)).symm
  exact congrArg (fun x => G.val.map (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hUV)).op x)
    (invSecVal_coextFunMapFun S.pushedRingHom.hom f.val (op (S.opensFunctor.obj V)) s)

/-- **Stacks Project, Tag 0A75.** The section identification commutes with restriction to a
smaller open subset. -/
@[stacks 0A75 "restriction naturality of the description of sections"]
theorem sectionsSheafHomExactSupportEquiv_restrict
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    (U U' : Opens S.X) (hUU' : U' ≤ U)
    (V V' : Opens S.Z) (hVV' : V' ≤ V)
    (hUV : (opensMap S.i).obj U = V) (hU'V' : (opensMap S.i).obj U' = V')
    (s : (S.sheafHomExactSupport.obj F).val.obj (op V)) :
    (S.sectionsSheafHomExactSupportEquiv F U' V' hU'V'
      ((S.sheafHomExactSupport.obj F).val.map (homOfLE hVV').op s)).1 =
        F.val.map (homOfLE hUU').op
          ((S.sectionsSheafHomExactSupportEquiv F U V hUV s).1) := by
  have hU'W : U' ≤ S.opensFunctor.obj V :=
    hUU'.trans (S.le_opensFunctor_obj_of_opensMap_eq hUV)
  refine (S.sectionsSheafHomExactSupportEquiv_apply_coe F U' V' hU'V' _).trans ?_
  refine Eq.trans (congrArg (fun x => F.val.map
      (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hU'V')).op x)
    (invSecVal_coextRestrFun S.pushedRingHom.hom F.val
      (S.opensFunctor.map (homOfLE hVV')).op s)) ?_
  refine Eq.trans (map_map_of_hom F.val (S.opensFunctor.map (homOfLE hVV'))
    (homOfLE (S.le_opensFunctor_obj_of_opensMap_eq hU'V')) hU'W _) ?_
  exact (map_map_of_le F.val (S.le_opensFunctor_obj_of_opensMap_eq hUV) hUU' hU'W _).symm

end ClosedQuotientMorphismOfRingedSpaces

end RingedSpaceModuleAdjunction

end
