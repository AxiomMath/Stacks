module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Pi.Basic
public import StacksCore.CategoryTheory.Filtration.Finite
public import StacksCore.CategoryTheory.Filtration.Preadditive
import StacksCore.Tactic.StacksAttribute

/-!
# Graded pieces of a filtered object

For a filtered object `(A, F)` of an abelian category, the graded pieces are
`gr^p(A) = F^pA/F^{p+1}A`; they form an additive functor `gr^p : Fil(𝒜) ⥤ 𝒜`, and
`gr : Fil(𝒜) ⥤ Gr(𝒜)` is the graded object with `p`-th piece `gr^p(A)`. For an index arrow
`f : i ⟶ j`, the rows `0 → F^iA → F^jA → gr_f(A) → 0` are short exact. The quotients
`X ↦ X/F^iX` form functors, and along `φ : i ⟶ j` the graded piece `gr_φ(X)` includes into
`X/F^iX` with the transition `X/F^iX ⟶ X/F^jX` vanishing on it.

## Main definitions

* `FilteredObject.grMap`: the graded piece `F^jA/F^iA` along an index arrow `f : i ⟶ j`, as a
  functor on filtered objects.
* `FilteredObject.gr`: the graded piece `gr^p(A) = F^pA/F^{p+1}A` of a decreasing
  `ℤ`-filtration.
* `FilteredObject.grGraded`: the functor `gr : Fil(𝒜) ⥤ Gr(𝒜)`.
* `FilteredObject.quot`: the quotient `X/F^iX` by the `i`-th step, as a functor.
* `FilteredObject.quotStep`: the transition `X/F^iX ⟶ X/F^jX` along `φ : i ⟶ j`.
* `FilteredObject.grMapι`: the inclusion `gr_φ(X) ⟶ X/F^iX`.
* `FilteredObject.quotStepShortComplex`: the short complex `gr_φ(X) ⟶ X/F^iX ⟶ X/F^jX`.

## Main results

* `FilteredObject.stepShortComplex_shortExact`: the sequence `0 → F^iA → F^jA → gr_f(A) → 0`
  is short exact.
* `FilteredObject.isIso_grGraded_map_iff`: a morphism induces an isomorphism on `gr` if and only
  if it induces an isomorphism on every `gr^p`.
* `FilteredObject.grMap_additive`: `gr_f` is an additive functor.

## Implementation notes

The graded piece is defined along an arbitrary index arrow `f : i ⟶ j` as the cokernel of the
step `F^iA ⟶ F^jA`, which needs only zero morphisms and cokernels in `C`; `gr^p` is the case of
the arrow `op (p+1) ⟶ op p` of `ℤᵒᵖ`, and `grGraded` is `Functor.pi' gr`. The functors `grMap f`
and `quot i` are `def`s with a term-mode API (`grMapπ`, `grMap_hom_ext`, `grMapDesc`,
`grMapIsCokernel`, and `quotπ`, `quot_hom_ext`, `quotDesc`, `quotIsCokernel`); their projection
lemmas are not `simp` lemmas, and morphisms `(grMap f).obj X ⟶ W` are compared with
`grMap_hom_ext` rather than `ext`.
-/
@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

open Filtration

section GrMap

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The graded piece `F^jA/F^iA` along an index arrow `f : i ⟶ j`, as a functor on filtered
objects; Stacks' `gr^p` is the case `f : op (p+1) ⟶ op p` of `ℤᵒᵖ` (`FilteredObject.gr`). -/
@[implicit_reducible, simps -isSimp]
noncomputable def grMap {i j : I} (f : i ⟶ j) : FilteredObject C I ⥤ C where
  obj A := cokernel (A.filtration.step f)
  map {A B} φ := cokernel.map (A.filtration.step f) (B.filtration.step f)
    (φ.natTrans.app i) (φ.natTrans.app j) (step_natTrans_app φ f)
  map_id A := by ext; simp
  map_comp φ ψ := by ext; simp

variable {i j : I} (f : i ⟶ j)

/-- The projection `F^jA ⟶ gr_f(A)`. -/
noncomputable def grMapπ (A : FilteredObject C I) : A.filtration.obj j ⟶ (grMap f).obj A :=
  cokernel.π (A.filtration.step f)

/-- The step composed with the projection to the graded piece vanishes. -/
@[reassoc (attr := simp)]
lemma step_grMapπ (A : FilteredObject C I) : A.filtration.step f ≫ grMapπ f A = 0 :=
  cokernel.condition _

/-- The projection `F^jA ⟶ gr_f(A)` is an epimorphism. -/
instance (A : FilteredObject C I) : Epi (grMapπ f A) := inferInstanceAs (Epi (cokernel.π _))

/-- Naturality of the projections `F^jA ⟶ gr_f(A)`. -/
@[reassoc (attr := simp)]
lemma grMapπ_map {A B : FilteredObject C I} (φ : A ⟶ B) :
    grMapπ f A ≫ (grMap f).map φ = φ.natTrans.app j ≫ grMapπ f B :=
  cokernel.π_desc _ _ _

/-- Morphisms out of a graded piece are determined by their composite with the projection. -/
lemma grMap_hom_ext {A : FilteredObject C I} {W : C} {u v : (grMap f).obj A ⟶ W}
    (h : grMapπ f A ≫ u = grMapπ f A ≫ v) : u = v :=
  coequalizer.hom_ext h

/-- Descending from a graded piece. -/
noncomputable def grMapDesc {A : FilteredObject C I} {W : C} (k : A.filtration.obj j ⟶ W)
    (hk : A.filtration.step f ≫ k = 0) : (grMap f).obj A ⟶ W :=
  cokernel.desc _ k hk

/-- The projection composed with a descended morphism. -/
@[reassoc (attr := simp)]
lemma grMapπ_desc {A : FilteredObject C I} {W : C} (k : A.filtration.obj j ⟶ W)
    (hk : A.filtration.step f ≫ k = 0) : grMapπ f A ≫ grMapDesc f k hk = k :=
  cokernel.π_desc _ _ _

/-- `gr_f(A)` is the cokernel of the step `F^iA ⟶ F^jA`. -/
noncomputable def grMapIsCokernel (A : FilteredObject C I) :
    IsColimit (CokernelCofork.ofπ (grMapπ f A) (step_grMapπ f A)) :=
  cokernelIsCokernel _

/-- `gr_f` preserves zero morphisms. -/
instance grMap_preservesZeroMorphisms : (grMap (C := C) f).PreservesZeroMorphisms where
  map_zero := by intros; apply grMap_hom_ext; simp

/-- The step short complex `F^iA ⟶ F^jA ⟶ gr_f(A)`. -/
noncomputable abbrev stepShortComplex (A : FilteredObject C I) : ShortComplex C :=
  ShortComplex.mk (A.filtration.step f) (grMapπ f A) (step_grMapπ f A)

/-- The step short complex is functorial in `A`. -/
@[simps]
noncomputable def stepShortComplexMap {A B : FilteredObject C I} (φ : A ⟶ B) :
    stepShortComplex f A ⟶ stepShortComplex f B where
  τ₁ := φ.natTrans.app i
  τ₂ := φ.natTrans.app j
  τ₃ := (grMap f).map φ

/-- If the step `F^iA ⟶ F^jA` is an isomorphism, the graded piece vanishes. -/
lemma isZero_grMap_obj_of_isIso_step (A : FilteredObject C I) [IsIso (A.filtration.step f)] :
    IsZero ((grMap f).obj A) :=
  isZero_cokernel_of_epi _

/-- If `F^jA = 0`, the graded piece vanishes. -/
lemma isZero_grMap_obj_of_isZero (A : FilteredObject C I) (h : IsZero (A.filtration.obj j)) :
    IsZero ((grMap f).obj A) := by
  have : Epi (A.filtration.step f) := ⟨fun _ _ _ => h.eq_of_src _ _⟩
  exact isZero_cokernel_of_epi _

end GrMap

section Quot

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The quotient `X/F^iX` of a filtered object by its `i`-th step, as a functor on filtered
objects. -/
@[implicit_reducible, simps -isSimp]
noncomputable def quot (i : I) : FilteredObject C I ⥤ C where
  obj X := cokernel (X.filtration.ι.app i)
  map {X Y} u := cokernel.map (X.filtration.ι.app i) (Y.filtration.ι.app i) (u.natTrans.app i)
    u.hom (u.comm i).symm
  map_id X := by ext; simp
  map_comp u v := by ext; simp

variable (i : I)

/-- The projection `X ⟶ X/F^iX`. -/
noncomputable def quotπ (X : FilteredObject C I) : X.X ⟶ (quot i).obj X :=
  cokernel.π (X.filtration.ι.app i)

/-- The inclusion of `F^iX` composed with the projection to `X/F^iX` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_app_quotπ (X : FilteredObject C I) : X.filtration.ι.app i ≫ quotπ i X = 0 :=
  cokernel.condition _

/-- The inclusion of a smaller step `F^jX ⊆ F^iX` (an index arrow `j ⟶ i`) composed with the
projection to `X/F^iX` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_app_quotπ_of_hom {j : I} (f : j ⟶ i) (X : FilteredObject C I) :
    X.filtration.ι.app j ≫ quotπ i X = 0 := by
  rw [← X.filtration.step_comp_ι_app f, Category.assoc, ι_app_quotπ, comp_zero]

/-- The projection `X ⟶ X/F^iX` is an epimorphism. -/
instance (X : FilteredObject C I) : Epi (quotπ i X) := inferInstanceAs (Epi (cokernel.π _))

/-- Naturality of the projections `X ⟶ X/F^iX`. -/
@[reassoc (attr := simp)]
lemma quotπ_map {X Y : FilteredObject C I} (u : X ⟶ Y) :
    quotπ i X ≫ (quot i).map u = u.hom ≫ quotπ i Y :=
  cokernel.π_desc _ _ _

/-- Morphisms out of `X/F^iX` are determined by their composite with the projection. -/
lemma quot_hom_ext {X : FilteredObject C I} {W : C} {u v : (quot i).obj X ⟶ W}
    (h : quotπ i X ≫ u = quotπ i X ≫ v) : u = v :=
  coequalizer.hom_ext h

/-- Descending from `X/F^iX`. -/
noncomputable def quotDesc {X : FilteredObject C I} {W : C} (k : X.X ⟶ W)
    (hk : X.filtration.ι.app i ≫ k = 0) : (quot i).obj X ⟶ W :=
  cokernel.desc _ k hk

/-- The projection composed with a descended morphism. -/
@[reassoc (attr := simp)]
lemma quotπ_desc {X : FilteredObject C I} {W : C} (k : X.X ⟶ W)
    (hk : X.filtration.ι.app i ≫ k = 0) : quotπ i X ≫ quotDesc i k hk = k :=
  cokernel.π_desc _ _ _

/-- `X/F^iX` is the cokernel of the inclusion `F^iX ⟶ X`. -/
noncomputable def quotIsCokernel (X : FilteredObject C I) :
    IsColimit (CokernelCofork.ofπ (quotπ i X) (ι_app_quotπ i X)) :=
  cokernelIsCokernel _

/-- `X ↦ X/F^iX` preserves zero morphisms. -/
instance quot_preservesZeroMorphisms : (quot (C := C) i).PreservesZeroMorphisms where
  map_zero := by intros; apply quot_hom_ext; simp

/-- If `F^iX = X`, the quotient `X/F^iX` vanishes. -/
lemma isZero_quot_obj_of_isIso_ι_app (X : FilteredObject C I) [IsIso (X.filtration.ι.app i)] :
    IsZero ((quot i).obj X) :=
  isZero_cokernel_of_epi _

end Quot

section QuotStep

variable [HasZeroMorphisms C] [HasCokernels C] {i j : I} (φ : i ⟶ j)

/-- The transition `X/F^iX ⟶ X/F^jX` along an index arrow `φ : i ⟶ j` (so `F^iX ⊆ F^jX`). -/
noncomputable def quotStep (X : FilteredObject C I) : (quot i).obj X ⟶ (quot j).obj X :=
  quotDesc i (quotπ j X) (ι_app_quotπ_of_hom j φ X)

/-- The projections `X ⟶ X/F^iX ⟶ X/F^jX` compose to the projection `X ⟶ X/F^jX`. -/
@[reassoc (attr := simp)]
lemma quotπ_quotStep (X : FilteredObject C I) : quotπ i X ≫ quotStep φ X = quotπ j X :=
  quotπ_desc _ _ _

/-- The transition `X/F^iX ⟶ X/F^jX` is an epimorphism. -/
instance (X : FilteredObject C I) : Epi (quotStep φ X) := epi_of_epi_fac (quotπ_quotStep φ X)

/-- Naturality of the transitions `X/F^iX ⟶ X/F^jX`. -/
@[reassoc (attr := simp)]
lemma quotStep_map {X Y : FilteredObject C I} (u : X ⟶ Y) :
    quotStep φ X ≫ (quot j).map u = (quot i).map u ≫ quotStep φ Y := by
  apply quot_hom_ext
  rw [quotπ_quotStep_assoc, quotπ_map, quotπ_map_assoc, quotπ_quotStep]

/-- `F^iX ⟶ F^jX ⟶ X ⟶ X/F^iX` vanishes. -/
@[reassoc]
lemma step_ι_app_quotπ (X : FilteredObject C I) :
    X.filtration.step φ ≫ X.filtration.ι.app j ≫ quotπ i X = 0 := by
  rw [step_comp_ι_app_assoc, ι_app_quotπ]

/-- The inclusion `gr_φ(X) = F^jX/F^iX ⟶ X/F^iX` of the graded piece into the quotient. -/
noncomputable def grMapι (X : FilteredObject C I) : (grMap φ).obj X ⟶ (quot i).obj X :=
  grMapDesc φ (X.filtration.ι.app j ≫ quotπ i X) (step_ι_app_quotπ φ X)

/-- `F^jX ⟶ gr_φ(X) ⟶ X/F^iX` is `F^jX ⟶ X ⟶ X/F^iX`. -/
@[reassoc (attr := simp)]
lemma grMapπ_grMapι (X : FilteredObject C I) :
    grMapπ φ X ≫ grMapι φ X = X.filtration.ι.app j ≫ quotπ i X :=
  grMapπ_desc _ _ _

/-- Naturality of the inclusions `gr_φ(X) ⟶ X/F^iX`. -/
@[reassoc (attr := simp)]
lemma grMapι_map {X Y : FilteredObject C I} (u : X ⟶ Y) :
    grMapι φ X ≫ (quot i).map u = (grMap φ).map u ≫ grMapι φ Y := by
  apply grMap_hom_ext
  rw [grMapπ_grMapι_assoc, quotπ_map, grMapπ_map_assoc, grMapπ_grMapι, ← Category.assoc,
    ← u.comm, Category.assoc]

/-- `gr_φ(X) ⟶ X/F^iX ⟶ X/F^jX` vanishes. -/
@[reassoc (attr := simp)]
lemma grMapι_quotStep (X : FilteredObject C I) : grMapι φ X ≫ quotStep φ X = 0 := by
  apply grMap_hom_ext
  rw [grMapπ_grMapι_assoc, quotπ_quotStep, ι_app_quotπ, comp_zero]

/-- The quotient step short complex `gr_φ(X) ⟶ X/F^iX ⟶ X/F^jX`. -/
noncomputable abbrev quotStepShortComplex (X : FilteredObject C I) : ShortComplex C :=
  ShortComplex.mk (grMapι φ X) (quotStep φ X) (grMapι_quotStep φ X)

/-- The quotient step short complex is functorial in `X`. -/
@[simps]
noncomputable def quotStepShortComplexMap {X Y : FilteredObject C I} (u : X ⟶ Y) :
    quotStepShortComplex φ X ⟶ quotStepShortComplex φ Y where
  τ₁ := (grMap φ).map u
  τ₂ := (quot i).map u
  τ₃ := (quot j).map u

end QuotStep

section Gr

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The index arrow `op (p+1) ⟶ op p` of `ℤᵒᵖ`, i.e. `p ≤ p + 1`: the step `F^{p+1} ⊆ F^p` of a
decreasing `ℤ`-filtration. -/
abbrev succHom (p : ℤ) : op (p + 1) ⟶ op p := opHomOfLE (Int.lt_succ p).le

/-- Stacks' graded piece `gr^p(A) = F^pA/F^{p+1}A` of a decreasing `ℤ`-filtration (`I := ℤᵒᵖ`), as
a functor `Fil(𝒜) ⥤ 𝒜`; `(gr p).obj A = cokernel (A.filtration.step (succHom p))` by `rfl`. -/
@[stacks 0120 "the graded pieces `gr^p(A) = F^pA/F^{p+1}A` of the text before 05SP, as functors"]
noncomputable abbrev gr (p : ℤ) : FilteredObject C ℤᵒᵖ ⥤ C := grMap (succHom p)

/-- Stacks' `gr : Fil(𝒜) ⥤ Gr(𝒜)`, the graded object with `p`-th piece `gr^p(A)`;
`grGraded ⋙ GradedObject.eval p ≅ gr p` is `Iso.refl _`. -/
@[stacks 0120 "the functor `gr : Fil(𝒜) ⥤ Gr(𝒜)` of the paragraph before 05SP"]
noncomputable abbrev grGraded : FilteredObject C ℤᵒᵖ ⥤ GradedObject ℤ C :=
  Functor.pi' gr

/-- `gr : Fil(𝒜) ⥤ Gr(𝒜)` preserves zero morphisms. -/
instance : (grGraded (C := C)).PreservesZeroMorphisms where
  map_zero := by intros; funext p; exact (gr p).map_zero _ _

/-- A morphism of filtered objects induces an isomorphism on `gr` if and only if it induces an
isomorphism on every `gr^p`. -/
lemma isIso_grGraded_map_iff {A B : FilteredObject C ℤᵒᵖ} (φ : A ⟶ B) :
    IsIso (grGraded.map φ) ↔ ∀ p, IsIso ((gr p).map φ) :=
  ⟨fun _ p => inferInstanceAs (IsIso ((GradedObject.eval p).map (grGraded.map φ))),
    fun h => have : ∀ p, IsIso (grGraded.map φ p) := h; GradedObject.isIso_of_isIso_apply _⟩

/-- `gr^p(A) = 0` below a top step `F^nA = A`: for `p + 1 ≤ n`. -/
lemma isZero_gr_obj_of_isIso_ι_app (A : FilteredObject C ℤᵒᵖ) {n p : ℤ} (h : p + 1 ≤ n)
    (hn : IsIso (A.filtration.ι.app (op n))) : IsZero ((gr p).obj A) :=
  have := A.filtration.isIso_ι_app_of_le h hn
  have := A.filtration.isIso_step_of_isIso_ι_app (succHom p)
  isZero_grMap_obj_of_isIso_step (succHom p) A

/-- `gr^p(A) = 0` from a zero step `F^mA = 0` on: for `m ≤ p`. -/
lemma isZero_gr_obj_of_isZero (A : FilteredObject C ℤᵒᵖ) {m p : ℤ} (h : m ≤ p)
    (hm : IsZero (A.filtration.obj (op m))) : IsZero ((gr p).obj A) :=
  isZero_grMap_obj_of_isZero (succHom p) A (A.filtration.isZero_obj_of_le h hm)

end Gr

section Additive

variable [Preadditive C] [HasCokernels C] {i j : I} (f : i ⟶ j)

/-- `gr_f` is an additive functor. -/
instance grMap_additive : (grMap (C := C) f).Additive where
  map_add := by intros; apply grMap_hom_ext; simp

/-- `X ↦ X/F^iX` is an additive functor. -/
instance quot_additive : (quot (C := C) i).Additive where
  map_add := by intros; apply quot_hom_ext; simp

end Additive

section StepExact

variable [Preadditive C] [HasCokernels C] [CategoryWithHomology C] {i j : I} (f : i ⟶ j)

/-- The step sequence `0 → F^iA → F^jA → gr_f(A) → 0` is short exact. -/
lemma stepShortComplex_shortExact (A : FilteredObject C I) :
    (stepShortComplex f A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (grMapIsCokernel f A)

end StepExact

end FilteredObject

end CategoryTheory
