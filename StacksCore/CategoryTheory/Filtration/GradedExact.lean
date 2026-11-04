module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksCore.CategoryTheory.Filtration.Strict
public import StacksCore.CategoryTheory.Limits.Shapes.Kernels
import StacksCore.Tactic.StacksAttribute

/-! # Exactness of the graded pieces: Stacks 05SP

Stacks 05SP: in an abelian category, (1) for a filtered object `A` and a subobject `X ⊆ A` with
the induced filtration, `A/X` with the quotient filtration, the sequence
`0 → gr^p(X) → gr^p(A) → gr^p(A/X) → 0` is exact for every `p`; (2) for any morphism `f : A ⟶ B`
of filtered objects, `0 → gr^p(Ker f) → gr^p(A) → gr^p(Coim f) → 0` and
`0 → gr^p(Im f) → gr^p(B) → gr^p(Coker f) → 0` are exact.

We prove (1) in the general form `FilteredObject.shortExact_subQuotShortComplex_map_grMap`: for a
short exact sequence `0 → Y → A → Z → 0` of `𝒜` with `A` filtered, `Y` carrying the induced and `Z`
the quotient filtration (`FilteredObject.subQuotShortComplex`), the graded pieces along *any*
index arrow form a short exact sequence. The proof is Mathlib's snake lemma applied to the two rows
`0 → F^iY → F^iA → F^iZ → 0` and `0 → F^jY → F^jA → F^jZ → 0`, whose vertical maps are the (mono)
steps: the kernel row vanishes and the cokernel row is the graded sequence. This avoids the lattice
identity `F^pA ∩ (X + F^{p+1}A) = (F^pA ∩ X) + F^{p+1}A` of Stacks' proof, which is the modular
law. Stated intrinsically in `Fil(𝒜)` (`FilteredObject.shortExact_map_grMap`): a short complex of
filtered objects which is short exact in `𝒜` and whose two morphisms are strict (Stacks 0123, i.e.
induced and quotient filtrations by Stacks 0124) has short exact graded pieces. Part (2) is the
special case of the kernel/coimage and image/cokernel sequences of `f` computed in `Fil(𝒜)`, which
are strict by `FilteredObject.isStrict_kernel_ι` and `isStrict_cokernel_π`. No finiteness and no
strictness of `f` is needed anywhere.

The quotient rows `0 → gr_φ(X) → X/F^iX → X/F^jX → 0` are short exact as well
(`FilteredObject.quotStepShortComplex_shortExact`: `F^iX` is the pullback kernel of
`F^jX → X → X/F^iX` and `X/F^jX` the pushout cokernel), and a morphism `X ⟶ Y` is cartesian iff
it induces monomorphisms `X/F^iX ⟶ Y/F^iY` on all quotients
(`FilteredObject.isStrictHom_iff_forall_mono_quot_map`), the quotient counterpart of
`mono_grMap_map_of_isStrict`. Both serve the ascending induction of Stacks 05QH.

The quotient by a step, `X ↦ X/F^iX`, is right exact: it preserves cokernels
(`quotCokernelIsColimit`; `(Coker f)/F^i(Coker f) = B/(F^iB + f(A))` is a pushout,
`isPushout_quotπ_cokernel_π`) hence all finite colimits (`preservesFiniteColimits_quot`, for any
index category `I` and any additive `𝒜` with cokernels and strong epi images), so colimits in
`Fil(𝒜)` are computed on the quotients:
`(B ⊔_A D)/F^i = B/F^iB ⊔_{A/F^iA} D/F^iD` (`isPushout_quot_map`, Stacks 05SM). Strictness has
the matching criterion `isStrict_iff_kernelSubobject_quot_map_eq`: `f` is strict iff on every
quotient the kernel of `A/F^iA ⟶ B/F^iB` is the image of `Ker f` (the dual of
`isStrict_iff_imageSubobject_natTrans_app_eq`), used by Stacks 05SM in
`StacksCore.CategoryTheory.Filtration.Pushouts`.
-/

@[expose] public section

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

open Filtration

section Abelian

variable [Abelian C]

/-- The short complex `Y ⟶ A ⟶ Z` of filtered objects, with `Y` carrying the filtration induced
from `A` and `Z` the quotient filtration, for `m ≫ e = 0`. -/
noncomputable abbrev subQuotShortComplex (A : FilteredObject C I) {Y Z : C} (m : Y ⟶ A.X)
    (e : A.X ⟶ Z) (w : m ≫ e = 0) : ShortComplex (FilteredObject C I) :=
  ShortComplex.mk (pullbackHom A m) (pushforwardHom A e) (hom_ext w)

variable (A : FilteredObject C I) {Y Z : C} (m : Y ⟶ A.X) (e : A.X ⟶ Z) (w : m ≫ e = 0)

/-- The rows `F^iY ⟶ F^iA ⟶ F^iZ` of a short exact sequence `Y ⟶ A ⟶ Z` with the induced and
quotient filtrations are short exact. -/
lemma shortExact_subQuotShortComplex_map_eval (hS : (ShortComplex.mk m e w).ShortExact) (i : I) :
    ((subQuotShortComplex A m e w).map (eval i)).ShortExact := by
  have := hS.mono_f
  have hm : IsLimit (KernelFork.ofι m w) := hS.fIsKernel
  have hker := KernelFork.IsLimit.ofIsPullback (IsPullback.of_hasPullback (A.filtration.ι.app i) m)
    hm
  have h₁ : Mono ((subQuotShortComplex A m e w).map (eval i)).f :=
    inferInstanceAs (Mono (pullback.fst (A.filtration.ι.app i) m))
  have h₂ : Epi ((subQuotShortComplex A m e w).map (eval i)).g :=
    inferInstanceAs (Epi (factorThruImage (A.filtration.ι.app i ≫ e)))
  refine ShortComplex.ShortExact.mk' ?_ h₁ h₂
  let φ : (subQuotShortComplex A m e w).map (eval i) ⟶
      ShortComplex.mk (pullback.fst (A.filtration.ι.app i) m) (A.filtration.ι.app i ≫ e)
        (by rw [pullback.condition_assoc, w, comp_zero]) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι (A.filtration.ι.app i ≫ e)
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (image.fac _).symm }
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (image.ι _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (ShortComplex.exact_of_f_is_kernel _ hker)

/-- The snake input for Stacks 05SP: the two rows at `i` and `j`, whose kernels vanish and whose
cokernels are the graded pieces along `f : i ⟶ j`. -/
@[simps! L₀ L₁ L₂ L₃]
noncomputable def subQuotSnakeInput (hS : (ShortComplex.mk m e w).ShortExact) {i j : I}
    (f : i ⟶ j) : ShortComplex.SnakeInput C where
  L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)
  L₁ := (subQuotShortComplex A m e w).map (eval i)
  L₂ := (subQuotShortComplex A m e w).map (eval j)
  L₃ := (subQuotShortComplex A m e w).map (grMap f)
  v₀₁ := 0
  v₁₂ :=
    { τ₁ := (pullbackObj A m).filtration.step f
      τ₂ := A.filtration.step f
      τ₃ := (pushforwardObj A e).filtration.step f
      comm₁₂ := step_natTrans_app (pullbackHom A m) f
      comm₂₃ := step_natTrans_app (pushforwardHom A e) f }
  v₂₃ :=
    { τ₁ := grMapπ f (pullbackObj A m)
      τ₂ := grMapπ f A
      τ₃ := grMapπ f (pushforwardObj A e)
      comm₁₂ := grMapπ_map f (pullbackHom A m)
      comm₂₃ := grMapπ_map f (pushforwardHom A e) }
  w₀₂ := zero_comp
  w₁₃ := by ext <;> exact step_grMapπ _ _
  h₀ := by
    refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
        (inferInstanceAs (Mono ((pullbackObj A m).filtration.step f))) (Limits.isZero_zero C)
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
        (inferInstanceAs (Mono (A.filtration.step f))) (Limits.isZero_zero C)
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm <| KernelFork.IsLimit.ofMonoOfIsZero _
        (inferInstanceAs (Mono ((pushforwardObj A e).filtration.step f))) (Limits.isZero_zero C)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm (grMapIsCokernel _ _)
  L₁_exact := (shortExact_subQuotShortComplex_map_eval A m e w hS i).exact
  epi_L₁_g := (shortExact_subQuotShortComplex_map_eval A m e w hS i).epi_g
  L₂_exact := (shortExact_subQuotShortComplex_map_eval A m e w hS j).exact
  mono_L₂_f := (shortExact_subQuotShortComplex_map_eval A m e w hS j).mono_f

/-- Stacks 05SP (1), general form: for a short exact sequence `0 → Y → A → Z → 0` of `𝒜` with `A`
filtered, `Y` carrying the induced filtration and `Z` the quotient filtration, the sequence
`0 → gr(Y) → gr(A) → gr(Z) → 0` of graded pieces along any index arrow is short exact. -/
@[stacks 05SP "(1), general: any short exact `0 → Y → A → Z → 0` of `𝒜`, `Y` induced, `Z` quotient"]
theorem shortExact_subQuotShortComplex_map_grMap (hS : (ShortComplex.mk m e w).ShortExact)
    {i j : I} (f : i ⟶ j) :
    ((subQuotShortComplex A m e w).map (grMap f)).ShortExact := by
  have h₁ := (subQuotSnakeInput A m e w hS f).L₃_exact
  have hz : IsZero (subQuotSnakeInput A m e w hS f).L₂'.X₁ := by
    rw [ShortComplex.SnakeInput.L₂'_X₁, subQuotSnakeInput_L₀]
    exact Limits.isZero_zero C
  have h₂ : Mono (subQuotSnakeInput A m e w hS f).L₃.f :=
    (subQuotSnakeInput A m e w hS f).L₂'_exact.mono_g (hz.eq_of_src _ _)
  have : Epi (subQuotSnakeInput A m e w hS f).L₂.g := by
    rw [subQuotSnakeInput_L₂]
    exact (shortExact_subQuotShortComplex_map_eval A m e w hS j).epi_g
  have h₃ : Epi (subQuotSnakeInput A m e w hS f).L₃.g := (subQuotSnakeInput A m e w hS f).epi_L₃_g
  rw [subQuotSnakeInput_L₃] at h₁ h₂ h₃
  exact ShortComplex.ShortExact.mk' h₁ h₂ h₃

/-- Stacks 05SP (1), literally: for `X ⊆ A` with the induced filtration and `A/X` with the
quotient filtration, `0 → gr(X) → gr(A) → gr(A/X) → 0` is short exact, along any index arrow. -/
@[stacks 05SP "(1) literally: `X ⊆ A` induced, `A/X` quotient, along any index arrow"]
theorem shortExact_subQuotShortComplex_cokernel_map_grMap (A : FilteredObject C I) {Y : C}
    (m : Y ⟶ A.X) [Mono m] {i j : I} (f : i ⟶ j) :
    ((subQuotShortComplex A m (cokernel.π m) (cokernel.condition m)).map (grMap f)).ShortExact :=
  shortExact_subQuotShortComplex_map_grMap A m _ _ (ShortComplex.shortExact_mk_cokernel_π m) f

section StrictShortExact

variable (S : ShortComplex (FilteredObject C I))

/-- A short complex of filtered objects which is short exact in `𝒜` and whose two morphisms are
strict is isomorphic to the model `subQuotShortComplex`. -/
noncomputable def isoSubQuotShortComplex (hS : (S.map forget).ShortExact) [IsStrict S.f]
    [IsStrict S.g] :
    S ≅ subQuotShortComplex S.X₂ S.f.hom S.g.hom (congrArg Hom.hom S.zero) :=
  have : Mono S.f.hom := hS.mono_f
  have : Epi S.g.hom := hS.epi_g
  ShortComplex.isoMk (isoPullbackObjOfIsStrict S.f) (Iso.refl _)
    (isoPushforwardObjOfIsStrict S.g)
    (hom_ext ((Category.id_comp _).trans (Category.comp_id _).symm))
    (hom_ext ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- Stacks 05SP (1), intrinsically in `Fil(𝒜)`: if `0 → X → A → Q → 0` is a short exact sequence
of `𝒜` whose two morphisms are strict morphisms of filtered objects (equivalently, `X` has the
induced and `Q` the quotient filtration, Stacks 0124), then `0 → gr(X) → gr(A) → gr(Q) → 0` is
short exact, along any index arrow. -/
@[stacks 05SP "(1) in `Fil(𝒜)`: a short exact sequence of `𝒜` with strict morphisms, any arrow",
  ega "IV 19.6.1" "rows of (19.6.1.1)"]
theorem shortExact_map_grMap (hS : (S.map forget).ShortExact) [IsStrict S.f] [IsStrict S.g]
    {i j : I} (f : i ⟶ j) : (S.map (grMap f)).ShortExact :=
  ShortComplex.shortExact_of_iso
    ((grMap f).mapShortComplex.mapIso (isoSubQuotShortComplex S hS)).symm
    (shortExact_subQuotShortComplex_map_grMap _ _ _ _ hS f)

end StrictShortExact

section GrStrictMonoEpi

variable {A B : FilteredObject C I} (u : A ⟶ B) {i j : I} (f : i ⟶ j)

/-- Stacks 05SP (1), first consequence: `gr` of a strict monomorphism is a monomorphism. -/
lemma mono_grMap_map_of_isStrict [Mono u] [IsStrict u] : Mono ((grMap f).map u) :=
  (shortExact_map_grMap (ShortComplex.mk u (cokernel.π u) (cokernel.condition u))
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _
        (isColimitOfHasCokernelOfPreservesColimit forget u)) (forget.map_mono _)
      (forget.map_epi _)) f).mono_f

/-- Stacks 05SP (1), second consequence: `gr` of a strict epimorphism is an epimorphism. -/
lemma epi_grMap_map_of_isStrict [Epi u] [IsStrict u] : Epi ((grMap f).map u) :=
  (shortExact_map_grMap (ShortComplex.mk (kernel.ι u) u (kernel.condition u))
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _
        (isLimitOfHasKernelOfPreservesLimit forget u)) (forget.map_mono _) (forget.map_epi _))
      f).epi_g

/-- `gr(Ker u) → gr(A)` is a monomorphism (Stacks 05SP (2)). -/
instance : Mono ((grMap f).map (kernel.ι u)) := mono_grMap_map_of_isStrict _ f

/-- `gr(B) → gr(Coker u)` is an epimorphism (Stacks 05SP (2)). -/
instance : Epi ((grMap f).map (cokernel.π u)) := epi_grMap_map_of_isStrict _ f

end GrStrictMonoEpi

section Part2

variable {A B : FilteredObject C I} (f : A ⟶ B)

/-- The underlying short complex of `0 → Ker f → A → Coim f → 0` (computed in `Fil(𝒜)`) is short
exact in `𝒜`: the forgetful functor preserves kernels and cokernels. -/
lemma shortExact_map_forget_kernel_ι_coimage_π :
    ((ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)).map
      forget).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (isColimitOfHasCokernelOfPreservesColimit forget (kernel.ι f)))
    (forget.map_mono _) (forget.map_epi _)

/-- The underlying short complex of `0 → Im f → B → Coker f → 0` (computed in `Fil(𝒜)`) is short
exact in `𝒜`. -/
lemma shortExact_map_forget_image_ι_cokernel_π :
    ((ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (kernel.condition _)).map
      forget).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _
      (isLimitOfHasKernelOfPreservesLimit forget (cokernel.π f)))
    (forget.map_mono _) (forget.map_epi _)

/-- Stacks 05SP (2), first sequence: `0 → gr(Ker f) → gr(A) → gr(Coim f) → 0` is short exact, for
any morphism `f` of filtered objects, on Mathlib's kernel and coimage computed in `Fil(𝒜)`. -/
@[stacks 05SP "(2) `0 → gr(Ker f) → gr(A) → gr(Coim f) → 0`, any `f`, along any index arrow"]
theorem shortExact_map_grMap_kernel_ι_coimage_π {i j : I} (φ : i ⟶ j) :
    ((ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)).map
      (grMap φ)).ShortExact :=
  shortExact_map_grMap _ (shortExact_map_forget_kernel_ι_coimage_π f) φ

/-- Stacks 05SP (2), second sequence: `0 → gr(Im f) → gr(B) → gr(Coker f) → 0` is short exact, for
any morphism `f` of filtered objects, on Mathlib's image and cokernel computed in `Fil(𝒜)`. -/
@[stacks 05SP "(2) `0 → gr(Im f) → gr(B) → gr(Coker f) → 0`, any `f`, along any index arrow"]
theorem shortExact_map_grMap_image_ι_cokernel_π {i j : I} (φ : i ⟶ j) :
    ((ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (kernel.condition _)).map
      (grMap φ)).ShortExact :=
  shortExact_map_grMap _ (shortExact_map_forget_image_ι_cokernel_π f) φ

end Part2

end Abelian

section QuotStepExact

variable {i j : I} (φ : i ⟶ j) (X : FilteredObject C I)

/-- `F^jX ⟶ X ⟶ X/F^iX ⟶ X/F^jX` vanishes; only zero morphisms and cokernels are needed. -/
lemma ι_app_quotπ_quotStep [HasZeroMorphisms C] [HasCokernels C] :
    (X.filtration.ι.app j ≫ quotπ i X) ≫ quotStep φ X = 0 := by
  rw [Category.assoc, quotπ_quotStep, ι_app_quotπ]

variable [Abelian C]

/-- `F^iX ⟶ F^jX` is a kernel of `F^jX ⟶ X ⟶ X/F^iX`: the kernel of a composite is the pullback
of the kernel, and `F^jX ∩ F^iX = F^iX`. -/
noncomputable def stepIsKernel :
    IsLimit (KernelFork.ofι (X.filtration.step φ) (step_ι_app_quotπ φ X)) :=
  KernelFork.IsLimit.ofIsPullback
    (IsPullback.of_vert_isIso_mono ⟨by rw [step_comp_ι_app, Category.id_comp]⟩ :
      IsPullback (X.filtration.step φ) (𝟙 _) (X.filtration.ι.app j) (X.filtration.ι.app i))
    (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (quotπ i X) (ι_app_quotπ i X))
      (quotIsCokernel i X))

/-- The inclusion `gr_φ(X) ⟶ X/F^iX` is a monomorphism. -/
instance mono_grMapι : Mono (grMapι φ X) :=
  (ShortComplex.exact_iff_mono_cokernel_desc (ShortComplex.mk (X.filtration.step φ)
    (X.filtration.ι.app j ≫ quotπ i X) (step_ι_app_quotπ φ X))).mp
    (ShortComplex.exact_of_f_is_kernel _ (stepIsKernel φ X))

/-- `X/F^iX ⟶ X/F^jX` is a cokernel of `F^jX ⟶ X ⟶ X/F^iX`: the square of the two projections
out of `X` is a pushout, since `X ⟶ X/F^iX` is an epimorphism. -/
noncomputable def quotStepIsCokernelOfι :
    IsColimit (CokernelCofork.ofπ (quotStep φ X) (ι_app_quotπ_quotStep φ X)) :=
  CokernelCofork.IsColimit.ofIsPushout
    (IsPushout.of_horiz_isIso_epi ⟨(quotπ_quotStep φ X).trans (Category.comp_id _).symm⟩ :
      IsPushout (quotπ i X) (quotπ j X) (quotStep φ X) (𝟙 _))
    (m := X.filtration.ι.app j) (w := ι_app_quotπ j X) (quotIsCokernel j X)

/-- `X/F^iX ⟶ X/F^jX` is a cokernel of `gr_φ(X) ⟶ X/F^iX`. -/
noncomputable def quotStepIsCokernel :
    IsColimit (CokernelCofork.ofπ (quotStep φ X) (grMapι_quotStep φ X)) :=
  isCokernelOfComp (grMapπ φ X) (X.filtration.ι.app j ≫ quotπ i X) (quotStepIsCokernelOfι φ X)
    (grMapι_quotStep φ X) (grMapπ_grMapι φ X)

/-- The quotient step sequence `0 → gr_φ(X) → X/F^iX → X/F^jX → 0` is short exact: the dual of
`stepShortComplex_shortExact`. -/
lemma quotStepShortComplex_shortExact : (quotStepShortComplex φ X).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (quotStepIsCokernel φ X)

end QuotStepExact

section QuotMono

variable {X Y : FilteredObject C I} (v : X ⟶ Y) (i : I)

/-- `F^iX ⟶ X ⟶ Y ⟶ Y/F^iY` vanishes, for any morphism `v : X ⟶ Y` of filtered objects; only
zero morphisms and cokernels in `C` are needed. -/
@[reassoc (attr := simp)]
lemma ι_app_hom_quotπ [HasZeroMorphisms C] [HasCokernels C] :
    X.filtration.ι.app i ≫ v.hom ≫ quotπ i Y = 0 := by
  rw [← Category.assoc, ← v.comm, Category.assoc, ι_app_quotπ, comp_zero]

variable [Abelian C]

/-- For a cartesian morphism `v : X ⟶ Y` (Mathlib's `IsStrictHom`, `F^iX = v⁻¹(F^iY)`), `F^iX` is
the kernel of `X ⟶ Y ⟶ Y/F^iY`: the kernel of a composite is the pullback of the kernel. -/
noncomputable def ιAppIsKernelOfIsStrictHom [IsStrictHom v] :
    IsLimit (KernelFork.ofι (X.filtration.ι.app i) (ι_app_hom_quotπ v i)) :=
  KernelFork.IsLimit.ofIsPullback (IsStrictHom.isPullback v i).flip
    (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (quotπ i Y) (ι_app_quotπ i Y))
      (quotIsCokernel i Y))

/-- `F^iX ⟶ X ⟶ Y/F^iY` is exact iff `X/F^iX ⟶ Y/F^iY` is a monomorphism. -/
private lemma mono_quot_map_iff_exact :
    Mono ((quot i).map v) ↔
      (ShortComplex.mk (X.filtration.ι.app i) (v.hom ≫ quotπ i Y) (ι_app_hom_quotπ v i)).Exact :=
  (ShortComplex.exact_iff_mono_cokernel_desc (ShortComplex.mk (X.filtration.ι.app i)
    (v.hom ≫ quotπ i Y) (ι_app_hom_quotπ v i))).symm

/-- A cartesian morphism `v : X ⟶ Y` induces a monomorphism `X/F^iX ⟶ Y/F^iY`; in particular a
strict monomorphism does (`isStrict_iff_isStrictHom_of_mono`). The quotient counterpart of
`mono_grMap_map_of_isStrict`. -/
lemma mono_quot_map_of_isStrictHom [IsStrictHom v] : Mono ((quot i).map v) :=
  (mono_quot_map_iff_exact v i).mpr
    (ShortComplex.exact_of_f_is_kernel _ (ιAppIsKernelOfIsStrictHom v i))

/-- A morphism `v : X ⟶ Y` which is a monomorphism on every quotient `X/F^iX ⟶ Y/F^iY` is
cartesian: `F^iX` is then the kernel of `X ⟶ Y ⟶ Y/F^iY`, which is `v⁻¹(F^iY)`. The converse
of `mono_quot_map_of_isStrictHom`. -/
lemma isStrictHom_of_forall_mono_quot_map (h : ∀ i, Mono ((quot i).map v)) : IsStrictHom v where
  isPullback i := by
    exact (IsPullback.of_isKernel (v.comm i).symm 
      (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (quotπ i Y) (ι_app_quotπ i Y))
        (quotIsCokernel i Y))
      ((mono_quot_map_iff_exact v i).mp (h i)).fIsKernel).flip

/-- A morphism of filtered objects is cartesian iff it is a monomorphism on every quotient. -/
lemma isStrictHom_iff_forall_mono_quot_map : IsStrictHom v ↔ ∀ i, Mono ((quot i).map v) :=
  ⟨fun _ i => mono_quot_map_of_isStrictHom v i, isStrictHom_of_forall_mono_quot_map v⟩

end QuotMono

section QuotCokernel

variable [HasZeroMorphisms C] [HasCokernels C] [HasImages C] [HasStrongEpiImages C]
  {A B : FilteredObject C I} (f : A ⟶ B) (i : I)

/-- The square `B ⟶ B/F^iB`, `B ⟶ Coker f`, `B/F^iB ⟶ (Coker f)/F^i(Coker f)`,
`Coker f ⟶ (Coker f)/F^i(Coker f)` is a pushout: `(Coker f)/F^i(Coker f) = B/(F^iB + f(A))`.
Indeed `Coker f ⟶ (Coker f)/F^i(Coker f)` is a cokernel of `F^iB ⟶ B ⟶ Coker f`, since
`F^iB ⟶ F^i(Coker f)` is an epimorphism (`epi_cokernel_π_natTrans_app`), and a square between a
cokernel of `m` and a cokernel of `m ≫ g` is a pushout (`IsPushout.of_isCokernel`). -/
lemma isPushout_quotπ_cokernel_π :
    IsPushout (quotπ i B) (cokernel.π f).hom ((quot i).map (cokernel.π f))
      (quotπ i (cokernel f)) :=
  (IsPushout.of_isCokernel (quotπ_map i (cokernel.π f)).symm (quotIsCokernel i B)
    (isCokernelEpiComp (quotIsCokernel i (cokernel f)) ((cokernel.π f).natTrans.app i)
      ((cokernel.π f).comm i).symm)).flip

/-- `(Coker f)/F^i(Coker f)` is a cokernel of `A/F^iA ⟶ B/F^iB`: the quotient by a step,
`X ↦ X/F^iX`, preserves cokernels. Indeed `(Coker f)/F^i(Coker f) = B/(F^iB + f(A))` is the
pushout of `B/F^iB` along `B ⟶ Coker f` (`isPushout_quotπ_cokernel_π`), hence a cokernel of
`A ⟶ B ⟶ B/F^iB`, which factors through the epimorphism `A ⟶ A/F^iA`. -/
noncomputable def quotCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ ((quot i).map (cokernel.π f))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]) :
      CokernelCofork ((quot i).map f)) :=
  isCokernelOfComp (quotπ i A) (f.hom ≫ quotπ i B)
    (CokernelCofork.IsColimit.ofIsPushout (m := f.hom)
      (w := by rw [← comp_hom, cokernel.condition, zero_hom])
      (isPushout_quotπ_cokernel_π f i) (isColimitOfHasCokernelOfPreservesColimit forget f))
    _ (quotπ_map i f)

/-- `quot i` preserves the cokernel of `f`. -/
instance preservesColimit_parallelPair_quot : PreservesColimit (parallelPair f 0) (quot i) :=
  preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (quotCokernelIsColimit f i))

end QuotCokernel

section QuotFiniteColimits

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [HasCokernels C]
  [HasImages C] [HasStrongEpiImages C]

/-- The quotient by a step, `X ↦ X/F^iX`, is right exact: it preserves all finite colimits,
being an additive functor preserving cokernels (`quotCokernelIsColimit`), for any index
category `I` and any additive `𝒜` with cokernels and strong epi images (the hypotheses of
`hasFiniteColimits`). Over `ℤᵒᵖ` this also follows from `quot i` being a left adjoint
(`StacksCore.CategoryTheory.Filtration.Single`). -/
instance preservesFiniteColimits_quot (i : I) : PreservesFiniteColimits (quot (C := C) i) :=
  Functor.preservesFiniteColimits_of_preservesCokernels (quot i)

variable {A B D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D)

/-- Stacks 05SM, the pushout: `B ⊔_A D` exists in `Fil(𝒜)` (`hasFiniteColimits`) and its
quotients by the steps are computed level-wise,
`(B ⊔_A D)/F^i(B ⊔_A D) = B/F^iB ⊔_{A/F^iA} D/F^iD`, for any index category `I` and any additive
`𝒜` with cokernels and strong epi images. (The steps themselves are not computed level-wise:
`F^i(B ⊔_A D)` is the image of `F^iB ⊕ F^iD`.) -/
@[stacks 05SM "the pushout is level-wise on the quotients by the steps, for any `I`"]
theorem isPushout_quot_map (i : I) :
    IsPushout ((quot i).map f) ((quot i).map g) ((quot i).map (pushout.inl f g))
      ((quot i).map (pushout.inr f g)) :=
  (IsPushout.of_hasPushout f g).map (quot i)

end QuotFiniteColimits

section Criterion

variable [Abelian C] {A B : FilteredObject C I}

/-- The kernel of the projection `X ⟶ X/F^iX` is the step `F^iX`: the projection is a cokernel
of the monomorphism `F^iX ⟶ X`. -/
lemma kernelSubobject_quotπ (i : I) (X : FilteredObject C I) :
    kernelSubobject (quotπ i X) = X.subobject i :=
  (Abelian.kernelSubobject_eq_imageSubobject_of_isColimit (quotIsCokernel i X)).trans
    (imageSubobject_mono _)

/-- Stacks-strictness on the quotients by the steps: `f : A ⟶ B` is strict if and only if for
every `i` the kernel of `A/F^iA ⟶ B/F^iB` is the image of `Ker f` in `A/F^iA`. Indeed
`Ker(A/F^iA ⟶ B/F^iB) = f⁻¹(F^iB)/F^iA` and the image of `Ker f` is `(F^iA + Ker f)/F^iA`, so
this is the condition `f⁻¹(F^iB) = F^iA + Ker f` of the remark after Stacks 0123
(`isStrict_iff_pullback_eq_sup`). The dual of `isStrict_iff_imageSubobject_natTrans_app_eq`,
and the Stacks-strict counterpart of `isStrictHom_iff_forall_mono_quot_map`. -/
theorem isStrict_iff_kernelSubobject_quot_map_eq (f : A ⟶ B) :
    IsStrict f ↔ ∀ i, kernelSubobject ((quot i).map f) =
      (Subobject.exists (quotπ i A)).obj (kernelSubobject f.hom) := by
  rw [isStrict_iff_pullback_eq_sup]
  refine forall_congr' fun i => Iff.trans ?_
    (Abelian.Subobject.pullback_obj_injective_of_epi (quotπ i A)).eq_iff
  rw [Subobject.pullback_kernelSubobject, quotπ_map, ← Subobject.pullback_kernelSubobject,
    kernelSubobject_quotπ, Abelian.Subobject.pullback_exists_eq_sup, kernelSubobject_quotπ,
    sup_comm]

end Criterion

end FilteredObject

end CategoryTheory
