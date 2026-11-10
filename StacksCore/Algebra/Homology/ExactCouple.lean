module

public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Refinements
import StacksCore.CategoryTheory.Subobject.Limits
import StacksCore.Tactic.StacksAttribute

/-! # Exact couples and the derived exact couple: Stacks 011Q and 011R

Stacks 011Q: an *exact couple* in an abelian category is a datum `(A, E, α, f, g)` of objects
`A`, `E` and morphisms `α : A → A`, `f : E → A`, `g : A → E` such that `Ker α = Im f`,
`Ker f = Im g` and `Ker g = Im α`, i.e. the triangle `A →α A →g E →f A` is exact at each of its
three vertices; a morphism of exact couples `t = (t_A, t_E)` is a pair of morphisms commuting
with `α`, `f` and `g`. Stacks 011R: for an exact couple, `d = g ∘ f : E → E` satisfies
`d ∘ d = 0`, and (1) `Ker d = f⁻¹(Ker g) = f⁻¹(Im α)`, (2) `Im d = g(Im f) = g(Ker α)`,
(3) the *derived couple* `(A', E', α', f', g')` with `A' = Im α`, `E' = Ker d / Im d`,
`α'` induced by `α`, `f'` induced by `f` and `g' = g ∘ α⁻¹` is again an exact couple.

* `ExactCouple C` is the structure of 011Q (1), with the three zero conditions as autoParam
  fields and the three exactness conditions as `ShortComplex.Exact` fields. The endomorphism is
  typed as `α : End A`, so that `α ^ n` is Mathlib's monoid power on `End A` and the `n`-fold
  composite `α ∘ ⋯ ∘ α` of the spectral sequence of an exact couple (011S, 011T) needs no
  separate definition (`pow_succ_eq`, `pow_succ_eq'`, `pow_zero_eq` translate it to `≫`).
  `ExactCouple.Hom` is 011Q (2), and the `Category` instance is the evident one.
* `ExactCouple.d` is Stacks' `d = g ∘ f`, which in Lean's composition order is `X.f ≫ X.g`
  (`d_def`); `d_comp_d` carries the tag. `ExactCouple.dComplex` is the short complex
  `E →d E →d E`, an `abbrev` on purpose (load-bearing): with a `def`, statements such as
  `X.dComplex.iCycles ≫ X.f` are not type-correct at implicit transparency. Its homology
  `X.dComplex.homology` is `E' = Ker d / Im d`, and `Abelian.image X.α` is `A' = Im α`.
* The derived couple: `α' : Im α ⟶ Im α` (`α'_ι`, `factorThruImage_α'`), `f' : Ker d/Im d ⟶ Im α`
  (`homologyπ_f'_ι`, `liftCycles_homologyπ_f'_ι`) and `g' : Im α ⟶ Ker d/Im d`
  (`factorThruImage_g'`), each characterised by a `reassoc`/`simp` API through the canonical
  epi `Abelian.factorThruImage α`, mono `Abelian.image.ι α` and `homologyπ`. Exactness of the
  derived couple (011R (3), `derived`) is proved with Mathlib's *refinements*
  (`ShortComplex.exact_iff_exact_up_to_refinements`) rather than pseudoelements: Stacks' diagram
  chases translate line by line, the refinement lemmas are stated at the `ShortComplex` API level
  used here, and no `Pseudoelement` scoping is needed. `derived` is a load-bearing `abbrev` as
  well: the iterated derived couples need `X.derived.α` to reduce to `X.α'`.
* 011R (1) and (2) are the four lattice identities `kernelSubobject_d_eq_pullback_kernelSubobject`,
  `kernelSubobject_d_eq_pullback_imageSubobject`, `imageSubobject_d_eq_exists_imageSubobject`,
  `imageSubobject_d_eq_exists_kernelSubobject` in `Subobject X.E`, with `f⁻¹` as
  `Subobject.pullback X.f` and `g(-)` as `Subobject.exists X.g`.
* Functoriality of the derived couple (`Hom.derived`, `derivedFunctor`) is not stated in Stacks
  and is untagged. The spectral sequence of an exact couple (011S, 011T) is in
  `StacksCore.Algebra.Homology.ExactCouple.SpectralSequence`; 0AMJ (the variant with shift functors
  `S`, `T`: `α : A → T⁻¹A`, `g : A → SE`, so that `d_r : E_r → T^{r-1} S E_r`) is not
  formalised here.
-/

@[expose] public section

namespace CategoryTheory

open Limits Category Preadditive

variable {C : Type*} [Category* C] [Abelian C]

/-- An exact couple `(A, E, α, f, g)` in an abelian category: `Ker α = Im f`, `Ker f = Im g`
and `Ker g = Im α`. The endomorphism is typed as `α : End A` so that `α ^ n` is the `n`-fold
composite of `α`. -/
@[stacks 011Q "(1) exact couple: `Ker α = Im f`, `Ker f = Im g`, `Ker g = Im α`"]
structure ExactCouple (C : Type*) [Category* C] [Abelian C] where
  /-- The object `A` of the exact couple. -/
  A : C
  /-- The object `E` of the exact couple. -/
  E : C
  /-- The endomorphism `α : A → A`, as an element of the monoid `End A`. -/
  α : End A
  /-- The morphism `f : E → A`. -/
  f : E ⟶ A
  /-- The morphism `g : A → E`. -/
  g : A ⟶ E
  /-- `g ∘ α = 0`. -/
  α_g : α.asHom ≫ g = 0 := by cat_disch
  /-- `f ∘ g = 0`. -/
  g_f : g ≫ f = 0 := by cat_disch
  /-- `α ∘ f = 0`. -/
  f_α : f ≫ α.asHom = 0 := by cat_disch
  /-- Exactness at the target of `α`: `Ker g = Im α`. -/
  exact_α : (ShortComplex.mk α.asHom g α_g).Exact
  /-- Exactness at `E`: `Ker f = Im g`. -/
  exact_g : (ShortComplex.mk g f g_f).Exact
  /-- Exactness at the source of `α`: `Ker α = Im f`. -/
  exact_f : (ShortComplex.mk f α.asHom f_α).Exact

namespace ExactCouple

attribute [reassoc (attr := simp)] α_g g_f f_α

/-- A morphism of exact couples `t = (t_A, t_E) : X ⟶ Y`: a pair of morphisms commuting with
`α`, `f` and `g`. -/
@[stacks 011Q "(2) morphism `t = (t_A, t_E)` commuting with `α`, `f`, `g`", ext]
structure Hom (X Y : ExactCouple C) where
  /-- The component `t_A : X.A ⟶ Y.A`. -/
  tA : X.A ⟶ Y.A
  /-- The component `t_E : X.E ⟶ Y.E`. -/
  tE : X.E ⟶ Y.E
  /-- `t_A` commutes with `α`. -/
  comm_α : X.α.asHom ≫ tA = tA ≫ Y.α.asHom := by cat_disch
  /-- `t` commutes with `f`. -/
  comm_f : X.f ≫ tA = tE ≫ Y.f := by cat_disch
  /-- `t` commutes with `g`. -/
  comm_g : X.g ≫ tE = tA ≫ Y.g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm_α Hom.comm_f Hom.comm_g

/-- Exact couples in `C` form a category, with `ExactCouple.Hom` as morphisms and componentwise
identities and composition. -/
@[simps id_tA id_tE comp_tA comp_tE]
instance : Category (ExactCouple C) where
  Hom := Hom
  id _ := { tA := 𝟙 _, tE := 𝟙 _ }
  comp φ ψ := { tA := φ.tA ≫ ψ.tA, tE := φ.tE ≫ ψ.tE }

/-- Two morphisms of exact couples agreeing on both components are equal. -/
@[ext]
lemma hom_ext {X Y : ExactCouple C} {φ ψ : X ⟶ Y} (hA : φ.tA = ψ.tA) (hE : φ.tE = ψ.tE) :
    φ = ψ :=
  Hom.ext hA hE

variable (X : ExactCouple C)

/-- `α^{n+1} = α ≫ α^n`: the monoid power on `End A` as a composition. -/
lemma pow_succ_eq (n : ℕ) : (X.α ^ (n + 1)).asHom = X.α.asHom ≫ (X.α ^ n).asHom := by
  rw [pow_succ, End.mul_asHom]

/-- `α^{n+1} = α^n ≫ α`: the monoid power on `End A` as a composition. -/
lemma pow_succ_eq' (n : ℕ) : (X.α ^ (n + 1)).asHom = (X.α ^ n).asHom ≫ X.α.asHom := by
  rw [pow_succ', End.mul_asHom]

/-- `α^0 = 𝟙 A`. -/
lemma pow_zero_eq : (X.α ^ 0).asHom = 𝟙 X.A := by
  rw [pow_zero, End.one_asHom]

/-- The differential `d = g ∘ f : E ⟶ E` of an exact couple (in Lean's order, `f ≫ g`). -/
def d : X.E ⟶ X.E := X.f ≫ X.g

/-- Unfolding lemma for the differential: `d = f ≫ g`. -/
lemma d_def : X.d = X.f ≫ X.g := by
  unfold d; rfl

/-- `d ∘ d = 0`, since `f ∘ g = 0`. -/
@[stacks 011R "`d ∘ d = 0` for `d = g ∘ f`", reassoc (attr := simp)]
lemma d_comp_d : X.d ≫ X.d = 0 := by
  rw [d_def, assoc, X.g_f_assoc, zero_comp, comp_zero]

/-- `d ∘ g = 0`. -/
@[reassoc (attr := simp)]
lemma g_d : X.g ≫ X.d = 0 := by
  rw [d_def, X.g_f_assoc, zero_comp]

/-- `f ∘ d = 0`. -/
@[reassoc (attr := simp)]
lemma d_f : X.d ≫ X.f = 0 := by
  rw [d_def, assoc, X.g_f, comp_zero]

/-- The short complex `E →d E →d E`, whose homology is `E' = Ker d / Im d`. An `abbrev` on
purpose (load-bearing): with a `def`, `X.dComplex.iCycles ≫ X.f` is not type-correct at
implicit transparency. -/
abbrev dComplex : ShortComplex C := ShortComplex.mk X.d X.d X.d_comp_d

/-- The first map of `X.dComplex` is `d`. -/
@[simp] lemma dComplex_f : X.dComplex.f = X.d := rfl

/-- The second map of `X.dComplex` is `d`. -/
@[simp] lemma dComplex_g : X.dComplex.g = X.d := rfl

/-- `Ker d ⊆ Ker (g ∘ f)`: the cycles of `X.dComplex` are killed by `f ≫ g`. -/
@[reassoc (attr := simp)]
lemma iCycles_f_g : X.dComplex.iCycles ≫ X.f ≫ X.g = 0 := by
  rw [← d_def, ← dComplex_g, ShortComplex.iCycles_g]

/-- `Ker d` is killed by `d` (the simp-normal form of `X.dComplex.iCycles_g`, whose `X.dComplex.g`
`simp` displays as `X.d`). -/
@[reassoc (attr := simp)]
lemma iCycles_d : X.dComplex.iCycles ≫ X.d = 0 := X.dComplex.iCycles_g

/-- `d` is killed by the projection to the opcycles (the simp-normal form of
`X.dComplex.f_pOpcycles`). -/
@[reassoc (attr := simp)]
lemma d_pOpcycles : X.d ≫ X.dComplex.pOpcycles = 0 := X.dComplex.f_pOpcycles

/-- `α' : Im α ⟶ Im α`, the endomorphism of `A' = Im α` induced by `α`. -/
noncomputable def α' : Abelian.image X.α.asHom ⟶ Abelian.image X.α.asHom :=
  Abelian.image.ι X.α.asHom ≫ Abelian.factorThruImage X.α.asHom

/-- A map `g` between images of `a` and `b` lying over `p` is compatible with the projections. -/
private lemma factorThruImage_comp_eq_of_comp_ι {A B : C} {a : A ⟶ A} {b : B ⟶ B} {p : A ⟶ B}
    (h : a ≫ p = p ≫ b) {g : Abelian.image a ⟶ Abelian.image b}
    (hg : g ≫ Abelian.image.ι b = Abelian.image.ι a ≫ p) :
    Abelian.factorThruImage a ≫ g = p ≫ Abelian.factorThruImage b := by
  rw [← cancel_mono (Abelian.image.ι b), assoc, hg, ← assoc, Abelian.image.fac, assoc,
    Abelian.image.fac, h]

/-- `α'` followed by the inclusion `Im α ⊆ A` is the inclusion followed by `α`. -/
@[reassoc (attr := simp)]
lemma α'_ι : X.α' ≫ Abelian.image.ι X.α.asHom = Abelian.image.ι X.α.asHom ≫ X.α.asHom := by
  unfold α'; rw [assoc, Abelian.image.fac]

/-- The projection `A ↠ Im α` followed by `α'` is `α` followed by the projection. -/
@[reassoc (attr := simp)]
lemma factorThruImage_α' :
    Abelian.factorThruImage X.α.asHom ≫ X.α' = X.α.asHom ≫ Abelian.factorThruImage X.α.asHom := by
  exact factorThruImage_comp_eq_of_comp_ι rfl X.α'_ι

/-- `f` followed by the projection `A ↠ Im α` vanishes, since `α ∘ f = 0`. -/
@[reassoc (attr := simp)]
lemma f_factorThruImage : X.f ≫ Abelian.factorThruImage X.α.asHom = 0 := by
  rw [← cancel_mono (Abelian.image.ι X.α.asHom), assoc, Abelian.image.fac, X.f_α, zero_comp]

/-- `f` maps `Ker d` into `Im α = Ker (A ↠ Coker α)`, by exactness at the target of `α`. -/
lemma iCycles_f_comp_cokernelπ : (X.dComplex.iCycles ≫ X.f) ≫ cokernel.π X.α.asHom = 0 := by
  have h₁ : (X.dComplex.iCycles ≫ X.f) ≫ X.g = 0 := by
    rw [assoc, ← d_def, X.dComplex.iCycles_g]
  have h₂ := (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero _).1 X.exact_α
  rw [← kernel.lift_ι X.g _ h₁, assoc, h₂, comp_zero]

/-- `f' : Ker d / Im d ⟶ Im α`, the morphism induced by `f` on `E' = Ker d / Im d` (it kills
`Im d` since `f ∘ d = 0`). -/
noncomputable def f' : X.dComplex.homology ⟶ Abelian.image X.α.asHom :=
  X.dComplex.descHomology (kernel.lift (cokernel.π X.α.asHom) (X.dComplex.iCycles ≫ X.f)
    X.iCycles_f_comp_cokernelπ) (by
      rw [← cancel_mono (kernel.ι (cokernel.π X.α.asHom)), assoc, kernel.lift_ι, zero_comp,
        X.dComplex.toCycles_i_assoc, dComplex_f, d_f])

/-- `f'` composed with the quotient `Ker d ↠ E'` and the inclusion `Im α ⊆ A` is `f` on
`Ker d`. -/
@[reassoc (attr := simp)]
lemma homologyπ_f'_ι :
    X.dComplex.homologyπ ≫ X.f' ≫ Abelian.image.ι X.α.asHom = X.dComplex.iCycles ≫ X.f := by
  unfold f'; rw [ShortComplex.π_descHomology_assoc]; exact kernel.lift_ι _ _ _

/-- `f'` on the class of a cycle `k` is `f ∘ k`, viewed in `A`. -/
@[reassoc]
lemma liftCycles_homologyπ_f'_ι {T : C} (k : T ⟶ X.E) (hk : k ≫ X.dComplex.g = 0) :
    X.dComplex.liftCycles k hk ≫ X.dComplex.homologyπ ≫ X.f' ≫ Abelian.image.ι X.α.asHom =
      k ≫ X.f := by
  rw [homologyπ_f'_ι, ShortComplex.liftCycles_i_assoc]

/-- `g` lands in `Ker d`: `d ∘ g = 0`. -/
lemma g_dComplex_g : X.g ≫ X.dComplex.g = 0 := by
  rw [dComplex_g, g_d]

/-- `f` followed by `A →g Ker d ↠ E'` vanishes: `g ∘ f = d` is a boundary. -/
@[reassoc (attr := simp)]
lemma f_liftCycles_g_homologyπ :
    X.f ≫ X.dComplex.liftCycles X.g X.g_dComplex_g ≫ X.dComplex.homologyπ = 0 := by
  rw [ShortComplex.comp_liftCycles_assoc,
    X.dComplex.liftCycles_homologyπ_eq_zero_of_boundary _ (𝟙 _)
      (by rw [id_comp, dComplex_f, d_def])]

/-- `Ker α` is killed by `A →g Ker d ↠ E'`: by exactness at the source of `α`, an element of
`Ker α` is `f x`, and `g f x = d x` is a boundary. Proved by refinements. -/
lemma kernelι_comp_liftCycles_homologyπ :
    kernel.ι (Abelian.factorThruImage X.α.asHom) ≫
      X.dComplex.liftCycles X.g X.g_dComplex_g ≫ X.dComplex.homologyπ = 0 := by
  have h : (kernel.ι (Abelian.factorThruImage X.α.asHom)) ≫ X.α.asHom = 0 := by
    have h' := kernel.condition (Abelian.factorThruImage X.α.asHom) =≫ Abelian.image.ι X.α.asHom
    rwa [assoc, Abelian.image.fac, zero_comp] at h'
  obtain ⟨T, π, _, x, hx⟩ := X.exact_f.exact_up_to_refinements _ h
  dsimp only at x hx
  rw [← cancel_epi π, comp_zero, reassoc_of% hx, ShortComplex.comp_liftCycles_assoc,
    ShortComplex.comp_liftCycles_assoc,
    X.dComplex.liftCycles_homologyπ_eq_zero_of_boundary _ x (by rw [dComplex_f, d_def])]

/-- `g' : Im α ⟶ Ker d / Im d`, Stacks' `g ∘ α⁻¹`: the descent of `A →g Ker d ↠ E'` along the
epimorphism `A ↠ Im α`. -/
noncomputable def g' : Abelian.image X.α.asHom ⟶ X.dComplex.homology :=
  Abelian.epiDesc (Abelian.factorThruImage X.α.asHom)
    (X.dComplex.liftCycles X.g X.g_dComplex_g ≫ X.dComplex.homologyπ)
    X.kernelι_comp_liftCycles_homologyπ

/-- `g'` on the class `α a` is the class of `g a` in `E'`. -/
@[reassoc (attr := simp)]
lemma factorThruImage_g' :
    Abelian.factorThruImage X.α.asHom ≫ X.g' =
      X.dComplex.liftCycles X.g X.g_dComplex_g ≫ X.dComplex.homologyπ := by
  unfold g'; exact Abelian.comp_epiDesc _ _ _

/-- `Ker d = f⁻¹(Ker g)`, as subobjects of `E`. -/
@[stacks 011R "(1) `Ker d = f⁻¹(Ker g)`"]
lemma kernelSubobject_d_eq_pullback_kernelSubobject :
    kernelSubobject X.d = (Subobject.pullback X.f).obj (kernelSubobject X.g) := by
  rw [Subobject.pullback_kernelSubobject, d_def]

/-- `Ker d = f⁻¹(Im α)`, as subobjects of `E`. -/
@[stacks 011R "(1) `Ker d = f⁻¹(Im α)`"]
lemma kernelSubobject_d_eq_pullback_imageSubobject :
    kernelSubobject X.d = (Subobject.pullback X.f).obj (imageSubobject X.α.asHom) := by
  have h := (ShortComplex.exact_iff_image_eq_kernel _).1 X.exact_α
  dsimp only at h
  rw [kernelSubobject_d_eq_pullback_kernelSubobject, h]

/-- `Im d = g(Im f)`, as subobjects of `E`. -/
@[stacks 011R "(2) `Im d = g(Im f)`"]
lemma imageSubobject_d_eq_exists_imageSubobject :
    imageSubobject X.d = (Subobject.exists X.g).obj (imageSubobject X.f) := by
  rw [d_def, Subobject.imageSubobject_comp_eq_exists]

/-- `Im d = g(Ker α)`, as subobjects of `E`. -/
@[stacks 011R "(2) `Im d = g(Ker α)`"]
lemma imageSubobject_d_eq_exists_kernelSubobject :
    imageSubobject X.d = (Subobject.exists X.g).obj (kernelSubobject X.α.asHom) := by
  have h := (ShortComplex.exact_iff_image_eq_kernel _).1 X.exact_f
  dsimp only at h
  rw [imageSubobject_d_eq_exists_imageSubobject, h]

/-- `g' ∘ α' = 0`: on the class `α a`, `g' (α' (α a))` is the class of the cycle `g (α a) = 0`. -/
@[reassoc (attr := simp)]
lemma α'_g' : X.α' ≫ X.g' = 0 := by
  rw [← cancel_epi (Abelian.factorThruImage X.α.asHom), factorThruImage_α'_assoc,
    factorThruImage_g', comp_zero, ShortComplex.comp_liftCycles_assoc,
    X.dComplex.liftCycles_homologyπ_eq_zero_of_boundary _ 0 (by rw [X.α_g, zero_comp])]

/-- `f' ∘ g' = 0`, since `f ∘ g = 0`. -/
@[reassoc (attr := simp)]
lemma g'_f' : X.g' ≫ X.f' = 0 := by
  rw [← cancel_mono (Abelian.image.ι X.α.asHom),
    ← cancel_epi (Abelian.factorThruImage X.α.asHom), assoc, factorThruImage_g'_assoc,
    liftCycles_homologyπ_f'_ι, X.g_f, zero_comp, comp_zero]

/-- `α' ∘ f' = 0`, since `α ∘ f = 0`. -/
@[reassoc (attr := simp)]
lemma f'_α' : X.f' ≫ X.α' = 0 := by
  rw [← cancel_mono (Abelian.image.ι X.α.asHom), ← cancel_epi X.dComplex.homologyπ, assoc, α'_ι,
    homologyπ_f'_ι_assoc, X.f_α, comp_zero, zero_comp, comp_zero]

/-- Exactness of the derived couple at `A' →α' A' →g' E'`, i.e. `Ker g' = Im α'`. Stacks'
chase, by refinements: `a = α b` with `g' a = 0` gives `g b = d x = g f x`, so `b - f x = α y`
and `a = α' (α y)`. -/
lemma exact_α' : (ShortComplex.mk X.α' X.g' X.α'_g').Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T a ha
  dsimp only at a ha ⊢
  obtain ⟨T₁, π₁, _, b, hb⟩ :=
    surjective_up_to_refinements_of_epi (Abelian.factorThruImage X.α.asHom) a
  have hb' : b ≫ X.dComplex.liftCycles X.g X.g_dComplex_g ≫ X.dComplex.homologyπ = 0 := by
    rw [← factorThruImage_g', ← reassoc_of% hb, ha, comp_zero]
  rw [ShortComplex.comp_liftCycles_assoc] at hb'
  obtain ⟨T₂, π₂, _, x, hx⟩ :=
    (X.dComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _).1 hb'
  dsimp only at x hx
  have hsub : (π₂ ≫ b - x ≫ X.f) ≫ X.g = 0 := by
    rw [sub_comp, assoc, hx, d_def, assoc, sub_self]
  obtain ⟨T₃, π₃, _, y, hy⟩ := X.exact_α.exact_up_to_refinements _ hsub
  dsimp only at hy
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, y ≫ Abelian.factorThruImage X.α.asHom, ?_⟩
  simp only [assoc]
  rw [factorThruImage_α', ← reassoc_of% hy, sub_comp, assoc, assoc, f_factorThruImage,
    comp_zero, sub_zero, hb]

/-- Exactness of the derived couple at `A' →g' E' →f' A'`, i.e. `Ker f' = Im g'`. Stacks'
chase, by refinements: a class `e = [z]` with `f' e = 0` has `f z = 0`, so `z = g y` and
`e = g' (α y)`. -/
lemma exact_g' : (ShortComplex.mk X.g' X.f' X.g'_f').Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T e he
  dsimp only at e he ⊢
  obtain ⟨T₁, π₁, _, z, hz, hz'⟩ := X.dComplex.eq_liftCycles_homologyπ_up_to_refinements e
  have hzf : z ≫ X.f = 0 := by
    rw [← liftCycles_homologyπ_f'_ι X z hz, ← assoc, ← hz', assoc, reassoc_of% he, zero_comp,
      comp_zero]
  obtain ⟨T₂, π₂, _, y, hy⟩ := X.exact_g.exact_up_to_refinements _ hzf
  dsimp only at hy
  refine ⟨T₂, π₂ ≫ π₁, inferInstance, y ≫ Abelian.factorThruImage X.α.asHom, ?_⟩
  rw [assoc, hz', assoc, factorThruImage_g', ShortComplex.comp_liftCycles_assoc,
    ShortComplex.comp_liftCycles_assoc]
  congr 2

/-- Exactness of the derived couple at `E' →f' A' →α' A'`, i.e. `Ker α' = Im f'`. Stacks'
chase, by refinements: `a = α b` with `α' a = 0` gives `α (α b) = 0`, so `α b = f x` with
`d x = g α b = 0`, and `a = f' [x]`. -/
lemma exact_f' : (ShortComplex.mk X.f' X.α' X.f'_α').Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T a ha
  dsimp only at a ha ⊢
  obtain ⟨T₁, π₁, _, b, hb⟩ :=
    surjective_up_to_refinements_of_epi (Abelian.factorThruImage X.α.asHom) a
  have hbα : (b ≫ X.α.asHom) ≫ X.α.asHom = 0 := by
    have h := (reassoc_of% hb) (X.α' ≫ Abelian.image.ι X.α.asHom)
    rw [reassoc_of% ha, zero_comp, comp_zero, factorThruImage_α'_assoc, Abelian.image.fac] at h
    rw [assoc]; exact h.symm
  obtain ⟨T₂, π₂, _, x, hx⟩ := X.exact_f.exact_up_to_refinements _ hbα
  dsimp only at x hx
  have hxd : x ≫ X.dComplex.g = 0 := by
    rw [dComplex_g, d_def, ← assoc, ← hx, assoc, assoc, X.α_g, comp_zero, comp_zero]
  refine ⟨T₂, π₂ ≫ π₁, inferInstance,
    X.dComplex.liftCycles x hxd ≫ X.dComplex.homologyπ, ?_⟩
  rw [← cancel_mono (Abelian.image.ι X.α.asHom)]
  simp only [assoc]
  rw [liftCycles_homologyπ_f'_ι, ← hx, reassoc_of% hb, Abelian.image.fac]

/-- The derived exact couple `(A', E', α', f', g') = (Im α, Ker d / Im d, α', f', g')` of
Stacks 011R (3). An `abbrev` on purpose (load-bearing): the iterated derived couples need
`X.derived.α` to reduce to `X.α'` (and likewise for `A`, `E`, `f`, `g`). -/
@[stacks 011R "(3) the derived couple `(Im α, Ker d/Im d, α', f', g')` is exact", simps]
noncomputable abbrev derived : ExactCouple C where
  A := Abelian.image X.α.asHom
  E := X.dComplex.homology
  α := .of X.α'
  f := X.f'
  g := X.g'
  exact_α := X.exact_α'
  exact_g := X.exact_g'
  exact_f := X.exact_f'

/-- `Im(α^{n+1}) ⊆ Im(α^n)`, as subobjects of `A`. -/
lemma imageSubobject_pow_succ_le (n : ℕ) :
    imageSubobject (X.α ^ (n + 1)).asHom ≤ imageSubobject (X.α ^ n).asHom := by
  rw [pow_succ_eq]; exact imageSubobject_comp_le _ _

/-- `Ker(α^n) ⊆ Ker(α^{n+1})`, as subobjects of `A`. -/
lemma kernelSubobject_pow_le_succ (n : ℕ) :
    kernelSubobject (X.α ^ n).asHom ≤ kernelSubobject (X.α ^ (n + 1)).asHom := by
  rw [pow_succ_eq']; exact kernelSubobject_comp_le _ _

/-! ### Functoriality of the derived couple -/

section Hom

variable {X} {Y : ExactCouple C} (t : X ⟶ Y)

/-- A morphism of exact couples commutes with the differentials `d`. -/
@[reassoc (attr := simp)]
lemma Hom.comm_d : X.d ≫ t.tE = t.tE ≫ Y.d := by
  rw [d_def, d_def, assoc, t.comm_g, t.comm_f_assoc]

/-- `t_E` as a morphism of short complexes `X.dComplex ⟶ Y.dComplex`. -/
@[simps]
def Hom.dHom : X.dComplex ⟶ Y.dComplex where
  τ₁ := t.tE
  τ₂ := t.tE
  τ₃ := t.tE
  comm₁₂ := t.comm_d.symm
  comm₂₃ := t.comm_d.symm

/-- `t_A` maps `Im α` into `Im α = Ker (A ↠ Coker α)` of the target. -/
lemma Hom.image_ι_tA_cokernelπ : Abelian.image.ι X.α.asHom ≫ t.tA ≫ cokernel.π Y.α.asHom = 0 := by
  rw [← cancel_epi (Abelian.factorThruImage X.α.asHom), comp_zero, ← assoc, Abelian.image.fac,
    t.comm_α_assoc, cokernel.condition, comp_zero]

/-- `t_A' : Im α ⟶ Im α`, the restriction of `t_A` to the images of `α`. -/
noncomputable def Hom.tA' : Abelian.image X.α.asHom ⟶ Abelian.image Y.α.asHom :=
  kernel.lift (cokernel.π Y.α.asHom) (Abelian.image.ι X.α.asHom ≫ t.tA)
    (by rw [assoc, t.image_ι_tA_cokernelπ])

/-- `t_A'` followed by the inclusion `Im α ⊆ A` is the inclusion followed by `t_A`. -/
@[reassoc (attr := simp)]
lemma Hom.tA'_ι : t.tA' ≫ Abelian.image.ι Y.α.asHom = Abelian.image.ι X.α.asHom ≫ t.tA := by
  unfold tA'
  rw [kernel.lift_ι]

/-- The projection `A ↠ Im α` followed by `t_A'` is `t_A` followed by the projection. -/
@[reassoc (attr := simp)]
lemma Hom.factorThruImage_tA' :
    Abelian.factorThruImage X.α.asHom ≫ t.tA' = t.tA ≫ Abelian.factorThruImage Y.α.asHom := by
  exact factorThruImage_comp_eq_of_comp_ι t.comm_α t.tA'_ι

/-- `t_E' : Ker d / Im d ⟶ Ker d / Im d`, the morphism induced by `t_E` on homology. An `abbrev`
(load-bearing) so that `ShortComplex.homologyπ_naturality` fires on it. -/
noncomputable abbrev Hom.tE' : X.dComplex.homology ⟶ Y.dComplex.homology :=
  ShortComplex.homologyMap t.dHom

/-- `t_E` on cycles is compatible with the cycle `g` of the two couples. -/
@[reassoc]
lemma Hom.liftCycles_g_cyclesMap :
    X.dComplex.liftCycles X.g X.g_dComplex_g ≫ ShortComplex.cyclesMap t.dHom =
      t.tA ≫ Y.dComplex.liftCycles Y.g Y.g_dComplex_g := by
  rw [← cancel_mono Y.dComplex.iCycles, assoc, ShortComplex.cyclesMap_i,
    ShortComplex.liftCycles_i_assoc, Hom.dHom_τ₂, t.comm_g, assoc, ShortComplex.liftCycles_i]

/-- The derived morphism `(t_A', t_E') : X' ⟶ Y'` of derived exact couples. -/
noncomputable def Hom.derived : X.derived ⟶ Y.derived where
  tA := t.tA'
  tE := t.tE'
  comm_α := by
    rw [← cancel_mono (Abelian.image.ι Y.α.asHom), ← cancel_epi (Abelian.factorThruImage X.α.asHom)]
    simp [t.comm_α_assoc]
  comm_f := by
    rw [← cancel_mono (Abelian.image.ι Y.α.asHom), ← cancel_epi X.dComplex.homologyπ]
    simp [assoc, homologyπ_f'_ι_assoc, tA'_ι, Hom.tE',
      ShortComplex.homologyπ_naturality_assoc, homologyπ_f'_ι, ShortComplex.cyclesMap_i_assoc,
      Hom.dHom_τ₂, t.comm_f]
  comm_g := by
    rw [← cancel_epi (Abelian.factorThruImage X.α.asHom)]
    simp [factorThruImage_g'_assoc, Hom.tE', ShortComplex.homologyπ_naturality,
      factorThruImage_tA'_assoc, factorThruImage_g', ShortComplex.comp_liftCycles_assoc]

/-- The `A`-component of the derived morphism is `t_A'`. -/
@[simp] lemma Hom.derived_tA : t.derived.tA = t.tA' := rfl

/-- The `E`-component of the derived morphism is `t_E'`. -/
@[simp] lemma Hom.derived_tE : t.derived.tE = t.tE' := rfl

/-- `t_A'` of the identity is the identity. -/
lemma Hom.tA'_id (X : ExactCouple C) : Hom.tA' (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono (Abelian.image.ι X.α.asHom), tA'_ι, id_tA, comp_id, id_comp]

/-- `t_A'` is compatible with composition. -/
lemma Hom.tA'_comp {Z : ExactCouple C} (s : Y ⟶ Z) : Hom.tA' (t ≫ s) = t.tA' ≫ s.tA' := by
  rw [← cancel_mono (Abelian.image.ι Z.α.asHom), tA'_ι, comp_tA, assoc, tA'_ι, tA'_ι_assoc]

/-- `dHom` of the identity is the identity. -/
lemma Hom.dHom_id (X : ExactCouple C) : Hom.dHom (𝟙 X) = 𝟙 X.dComplex :=
  ShortComplex.hom_ext _ _ (by simp) (by simp) (by simp)

/-- `dHom` is compatible with composition. -/
lemma Hom.dHom_comp {Z : ExactCouple C} (s : Y ⟶ Z) : Hom.dHom (t ≫ s) = t.dHom ≫ s.dHom :=
  ShortComplex.hom_ext _ _ (by simp) (by simp) (by simp)

/-- The derived morphism of the identity is the identity. -/
@[simp]
lemma derived_id (X : ExactCouple C) : Hom.derived (𝟙 X) = 𝟙 X.derived := by
  ext
  · rw [Hom.derived_tA, Hom.tA'_id, id_tA]
  · rw [Hom.derived_tE, id_tE]
    dsimp only [Hom.tE']
    rw [Hom.dHom_id, ShortComplex.homologyMap_id]

/-- The derived morphism is compatible with composition. -/
@[simp]
lemma derived_comp {Z : ExactCouple C} (s : Y ⟶ Z) :
    Hom.derived (t ≫ s) = t.derived ≫ s.derived := by
  ext
  · rw [Hom.derived_tA, Hom.tA'_comp, comp_tA, Hom.derived_tA, Hom.derived_tA]
  · rw [Hom.derived_tE, comp_tE, Hom.derived_tE, Hom.derived_tE]
    dsimp only [Hom.tE']
    rw [Hom.dHom_comp, ShortComplex.homologyMap_comp]

end Hom

/-- The derived couple as an endofunctor of the category of exact couples. `implicit_reducible`
so that `derivedFunctor.obj X` unfolds to `X.derived` at implicit transparency and the `simps`
lemma `derivedFunctor_map` is type-correct. -/
@[implicit_reducible, simps obj map]
noncomputable def derivedFunctor : ExactCouple C ⥤ ExactCouple C where
  obj := derived
  map := Hom.derived
  map_id := derived_id
  map_comp := fun t s ↦ derived_comp t s

end ExactCouple

end CategoryTheory
