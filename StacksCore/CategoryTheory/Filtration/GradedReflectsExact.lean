module

public import StacksCore.Algebra.Homology.ShortComplex.Exact
public import StacksCore.CategoryTheory.Filtration.GradedStrict
public import StacksCore.CategoryTheory.Filtration.Single

/-! # Graded pieces reflect exactness: Stacks 05QH

Stacks 05QH: let `A → B → C` be a complex of filtered objects of an abelian category `𝒜` with
finite filtrations such that `gr(A) → gr(B) → gr(C)` is exact. Then (1) each
`gr^p(A) → gr^p(B) → gr^p(C)` is exact, (2) each `F^pA → F^pB → F^pC` is exact, (3) each
`A/F^pA → B/F^pB → C/F^pC` is exact, (4) `A → B` and `B → C` are strict, and (5) `A → B → C` is
exact in `𝒜`.

Finiteness is sharper than Stacks states: only `B` matters, `A` and `C` are arbitrary. (2) and
the strictness of `A → B` in (4) need a zero step of `B`
(`FilteredObject.exact_map_eval_of_exact_map_gr`, `FilteredObject.isStrict_f_of_exact_map_gr`),
(3) and the strictness of `B → C` in (4) a top step of `B`
(`FilteredObject.exact_map_quot_of_exact_map_gr`, `FilteredObject.isStrict_g_of_exact_map_gr`),
and (5) both (`FilteredObject.exact_map_forget_of_exact_map_gr`). (1) is
`FilteredObject.exact_map_grGraded_iff`; the bundled statement is
`FilteredObject.exact_of_exact_map_grGraded`.

The proofs run through `k : A ⟶ Ker g` and `c : Coker f ⟶ C`, computed in `Fil(𝒜)`. Exactness on
`gr^p` makes `gr^p(k)` an epimorphism and `gr^p(c)` a monomorphism (Stacks 05SP through
`ShortComplex.Exact.epi_map_kernel_lift` and `ShortComplex.Exact.mono_map_cokernel_desc`), and
the two inductions of Stacks 0127 turn these into level-wise statements: descending along the
rows `0 → F^{p+1} → F^p → gr^p → 0` from a zero step of `B`
(`FilteredObject.epi_natTrans_app_of_forall_epi_gr`, so `F^pA ↠ F^p(Ker g)`, hence `A ↠ Ker g`
at a top step of `B`), and ascending along the new rows `0 → gr^p → X/F^{p+1}X → X/F^pX → 0`
(`FilteredObject.quotStepShortComplex_shortExact`) from a top step of `B`
(`FilteredObject.mono_quot_map_of_forall_mono_gr`, so `(Coker f)/F^p ↪ C/F^pC`). The functors
`F^p = eval (op p)` and `forget` preserve the kernel of `g`, being right adjoints
(`FilteredObject.singleAdjEval`, `FilteredObject.ofBotAdjForget`), and `X ↦ X/F^pX = quot (op p)`
and `forget` preserve the cokernel of `f`, being left adjoints (`FilteredObject.quotAdjSingle`,
`FilteredObject.forgetAdjOfTop`), so exactness follows through the comparison morphisms
(`ShortComplex.exact_map_iff_epi_map_kernel_lift`,
`ShortComplex.exact_map_iff_mono_map_cokernel_desc`). Strictness: `k` is an epimorphism on all
levels, hence strict (`FilteredObject.isStrict_of_forall_epi_natTrans_app`), and
`f = k ≫ (Ker g → B)` (Stacks 05SJ); `c` is a monomorphism on all quotients, hence cartesian
(`FilteredObject.isStrictHom_of_forall_mono_quot_map`) and strict, and `g = (B → Coker f) ≫ c`.

The infrastructure lives elsewhere: the quotient functor `FilteredObject.quot` and the quotient
step rows in `StacksCore.CategoryTheory.Filtration.GradedPieces` and `…GradedExact`, the two
inductions in `…GradedStrict`, the adjunctions of `eval` and `quot` in `…Single`, the strictness
of level-wise epimorphisms in `…Strict`, and the functor-image exactness lemmas in
`StacksCore.Algebra.Homology.ShortComplex.Exact`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C]

namespace FilteredObject

open Filtration

section ReflectsExact

variable [Abelian C] (S : ShortComplex (FilteredObject C ℤᵒᵖ))

/-- `F^pA ⟶ F^p(Ker g)` is an epimorphism for every `p`, given a zero step of `B`. -/
lemma epi_kernel_lift_natTrans_app (hS : ∀ p, (S.map (gr p)).Exact)
    [HasBotStep S.X₂.filtration] (p : ℤᵒᵖ) :
    Epi ((kernel.lift S.g S.f S.zero).natTrans.app p) :=
  epi_natTrans_app_of_forall_epi_gr _ (fun p => (hS p).epi_map_kernel_lift) p

/-- `(Coker f)/F^p(Coker f) ⟶ C/F^pC` is a monomorphism for every `p`, given a top step of
`B`. -/
lemma mono_quot_map_cokernel_desc (hS : ∀ p, (S.map (gr p)).Exact)
    [HasTopStep S.X₂.filtration] (p : ℤᵒᵖ) :
    Mono ((quot p).map (cokernel.desc S.f S.g S.zero)) :=
  mono_quot_map_of_forall_mono_gr _ (fun p => (hS p).mono_map_cokernel_desc) p

/-- Stacks 05QH (2): if `gr(A) → gr(B) → gr(C)` is exact then `F^pA → F^pB → F^pC` is exact for
every `p`; needs only a zero step of `B`. -/
@[stacks 05QH "(2); needs only a zero step of `B`"]
theorem exact_map_eval_of_exact_map_gr (hS : ∀ p, (S.map (gr p)).Exact)
    [HasBotStep S.X₂.filtration] (p : ℤ) : (S.map (eval (op p))).Exact :=
  (ShortComplex.exact_map_iff_epi_map_kernel_lift S (eval (op p))).mpr
    (epi_kernel_lift_natTrans_app S hS (op p))

/-- Stacks 05QH (3): if `gr(A) → gr(B) → gr(C)` is exact then `A/F^pA → B/F^pB → C/F^pC` is
exact for every `p`; needs only a top step of `B`. -/
@[stacks 05QH "(3); needs only a top step of `B`"]
theorem exact_map_quot_of_exact_map_gr (hS : ∀ p, (S.map (gr p)).Exact)
    [HasTopStep S.X₂.filtration] (p : ℤ) : (S.map (quot (op p))).Exact :=
  (ShortComplex.exact_map_iff_mono_map_cokernel_desc S (quot (op p))).mpr
    (mono_quot_map_cokernel_desc S hS (op p))

/-- Stacks 05QH (5): if `gr(A) → gr(B) → gr(C)` is exact then `A → B → C` is exact in `𝒜`; needs
only a finite filtration on `B`. -/
@[stacks 05QH "(5); needs only a finite filtration on `B`"]
theorem exact_map_forget_of_exact_map_gr (hS : ∀ p, (S.map (gr p)).Exact)
    [HasTopStep S.X₂.filtration] [HasBotStep S.X₂.filtration] : (S.map forget).Exact :=
  (ShortComplex.exact_map_iff_epi_map_kernel_lift S forget).mpr
    (epi_hom_of_forall_epi_gr _ fun p => (hS p).epi_map_kernel_lift)

/-- `A → B` is strict as soon as `A → Ker g` is an epimorphism on every step: it is then the
composite of the strict morphism `A → Ker g` with the strict monomorphism `Ker g → B`
(Stacks 05SJ (2)). -/
lemma isStrict_f_of_epi_kernel_lift
    (hk : ∀ p, Epi ((kernel.lift S.g S.f S.zero).natTrans.app p)) : IsStrict S.f := by
  have := isStrict_of_forall_epi_natTrans_app (kernel.lift S.g S.f S.zero) hk
  have : Mono (kernel.ι S.g).hom := forget.map_mono _
  rw [← kernel.lift_ι S.g S.f S.zero]
  infer_instance

/-- Stacks 05QH (4) for `A → B`: if `gr(A) → gr(B) → gr(C)` is exact then `A → B` is strict; needs
only a zero step of `B`. -/
@[stacks 05QH "(4) for `A → B`; needs only a zero step of `B`"]
theorem isStrict_f_of_exact_map_gr (hS : ∀ p, (S.map (gr p)).Exact)
    [HasBotStep S.X₂.filtration] : IsStrict S.f :=
  isStrict_f_of_epi_kernel_lift S (epi_kernel_lift_natTrans_app S hS)

/-- `B → C` is strict as soon as `Coker f → C` is a monomorphism on every quotient: it is then
cartesian (`isStrictHom_of_forall_mono_quot_map`), hence strict, and `B → C` is the composite of
the strict epimorphism `B → Coker f` with it (Stacks 05SJ (3)). -/
lemma isStrict_g_of_mono_quot_map_cokernel_desc
    (hc : ∀ p, Mono ((quot p).map (cokernel.desc S.f S.g S.zero))) : IsStrict S.g := by
  have := isStrictHom_of_forall_mono_quot_map (cokernel.desc S.f S.g S.zero) hc
  have : Epi (cokernel.π S.f).hom := forget.map_epi _
  rw [← cokernel.π_desc S.f S.g S.zero]
  infer_instance

/-- Stacks 05QH (4) for `B → C`: if `gr(A) → gr(B) → gr(C)` is exact then `B → C` is strict; needs
only a top step of `B`. -/
@[stacks 05QH "(4) for `B → C`; needs only a top step of `B`"]
theorem isStrict_g_of_exact_map_gr (hS : ∀ p, (S.map (gr p)).Exact)
    [HasTopStep S.X₂.filtration] : IsStrict S.g :=
  isStrict_g_of_mono_quot_map_cokernel_desc S (mono_quot_map_cokernel_desc S hS)

/-- Stacks 05QH: let `A → B → C` be a complex of filtered objects of an abelian category with
`gr(A) → gr(B) → gr(C)` exact and `B` finitely filtered (Stacks assumes `A`, `B`, `C` finite).
Then (1) `gr^p(A) → gr^p(B) → gr^p(C)` is exact for every `p`, (2) `F^pA → F^pB → F^pC` is
exact for every `p`, (3) `A/F^pA → B/F^pB → C/F^pC` is exact for every `p`, (4) `A → B` and
`B → C` are strict, and (5) `A → B → C` is exact in `𝒜`. -/
@[stacks 05QH "needs only a finite filtration on `B`; `A` and `C` are arbitrary"]
theorem exact_of_exact_map_grGraded [IsFinite S.X₂.filtration] (hS : (S.map grGraded).Exact) :
    (∀ p, (S.map (gr p)).Exact) ∧ (∀ p, (S.map (eval (op p))).Exact) ∧
      (∀ p, (S.map (quot (op p))).Exact) ∧ (IsStrict S.f ∧ IsStrict S.g) ∧
      (S.map forget).Exact :=
  have hS' := (exact_map_grGraded_iff S).mp hS
  ⟨hS', exact_map_eval_of_exact_map_gr S hS', exact_map_quot_of_exact_map_gr S hS',
    ⟨isStrict_f_of_exact_map_gr S hS', isStrict_g_of_exact_map_gr S hS'⟩,
    exact_map_forget_of_exact_map_gr S hS'⟩

end ReflectsExact

end FilteredObject

end CategoryTheory
