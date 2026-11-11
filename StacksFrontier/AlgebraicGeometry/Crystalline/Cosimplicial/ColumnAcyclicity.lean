module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.ColumnAcyclicityInputs
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Acyclicity

/-!
# The columns of the double complex of [Stacks, Tag 07LG] are acyclic

The hypothesis `hcolumns` of `...SmallSite.computes07LG_of_doubleComplex`
(`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean`) asks, for a
double complex built as `Crystalline.CosimplicialCompletedPair.doubleComplex`, for the identity

`K^{a,b} = M(b) ⊗̂_{D̂(b)} Ω^a_{D(b)}  ≅  (M(•) ⊗̂_{D(•)} Ω^a_{D(•)})_b`

of `Crystalline.CosimplicialCompletedModule.column` with `Crystalline.columnTargetModule`, after
which `Crystalline.isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero` and
`Crystalline.isZero_homology_alternatingCofaceMapComplex_of_iso` finish from
`Crystalline.homotopic_id_columnTargetModule_zero`.

This module **proves that identity** — `Crystalline.columnTargetIso` — and reads `hcolumns` off
it: `Crystalline.isZero_homology_alternatingCofaceMapComplex_doubleComplex_X`.  The comparison is
built in two halves, the forms (`Crystalline.columnFormsMapₛₗ`) and the tensor factor
(`Crystalline.columnTensorMapₛₗ`), and every step of both obeys the three disciplines the
elaboration of such a comparison is forced to obey.

## The obstruction this module exists to route around

The two sides name the same ring and the same module by different terms.  The column uses
`Crystalline.CosimplicialDPAlgebra.completedRing` and
`Crystalline.CosimplicialDPAlgebra.completedDifferentials`, i.e. `AdicCompletion` of the
uncompleted envelope and of its differentials; [Stacks, Tag 07LA] uses the degrees
`(Crystalline.cosimplicialEnvelopeRing s f hf).obj n` and
`(Crystalline.cosimplicialEnvelopeDifferentials s f hf).obj (op (op n))` of the cosimplicial ring
and the cosimplicial module.  The two are definitionally equal, and Lean checks it cheaply for
the rings, for the differentials and for their transition maps — but **not under an exterior
power**: unifying `⋀[R]^a N` with `⋀[R']^a N'` across the two spellings drives the unifier
through the `TensorAlgebra` and `CliffordAlgebra` quotients underlying `ExteriorAlgebra`, whose
`ringCon` is sealed, and exhausts the heartbeat budget.

Three disciplines keep every step inside the budget, and all three are forced.

* **The change of spelling is performed once, on the ring and on the differentials, and carried
  into the exterior power by `ExteriorAlgebra.powMapₛₗ`.**  That is
  `Crystalline.columnRingHom`, `Crystalline.columnDifferentialsHom` and their inverses, and
  `Crystalline.columnFormsShapeMapₛₗ`.  Nothing in this module ever ascribes a type to an
  exterior power.

* **The index is substituted with the cosimplicial module a variable.**
  `Crystalline.CosimplicialIdeal.completion` is built through
  `Crystalline.SemilinearCosimplicialModule.toCosimplicialModule`, so the degree
  `(I.completion M).obj (op (op n))` is `AdicCompletion (I.obj (unop (unop (op (op n)))))
  (M.obj (op (op (unop (unop (op (op n)))))))`.  The index terms reduce to `n` and `op (op n)`,
  but at a concrete `M` the unifier attempts congruence on `M.obj` first, fails, and unfolds
  `M.obj` on both sides instead, descending into the exterior power with two differently spelled
  indices — the obstruction recorded in the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/Acyclicity.lean`.  So the substitution
  is performed once and for all in `Crystalline.completionDegree`, with the cosimplicial ideal
  and the cosimplicial module *variables*, and every degreewise construction below is written at
  `AdicCompletion (I.obj n) (M.obj (op (op n)))` and transported across it at the end.

* **Every equation between completions is an instance of an abstract lemma, applied with its
  type-carrying arguments left to be solved from the goal.**  `Crystalline.adicCompletionMapₛₗ`
  depends on its map only through the underlying function, which is what makes
  `Crystalline.adicCompletionMapₛₗ_square` and
  `Crystalline.adicCompletionMapₛₗ_comp_eq_self` available at all.

* **`Crystalline.completionDegree` and `Crystalline.tensorObjDegree` are never reduced.**  Both
  are `LinearEquiv.refl`, so every transport across them is a `rfl` — but *reducing* one at a
  concrete cosimplicial module makes the two `Module` instances on that degree meet, and at the
  degreewise exterior power that is the unification above.  So each comparison is read across its
  transport by one `rfl` lemma stated at the degree (`Crystalline.columnFormsMapₛₗ_apply`,
  `Crystalline.columnTensorShapeMapₛₗ_apply`, `Crystalline.columnTensorMapₛₗ_apply`) and every
  subsequent step uses `LinearEquiv.apply_symm_apply`, `LinearEquiv.symm_apply_apply` or
  `LinearEquiv.injective`, which are theorems about an arbitrary equiv and reduce nothing.

## Main definitions

* `Crystalline.completionDegree` and `Crystalline.tensorObjDegree` — the degree of a degreewise
  adic completion and of a tensor product of cosimplicial modules, with the index substituted.
* `Crystalline.columnFormsShapeMapₛₗ` and `...'` — **the two spellings of the forms of
  [Stacks, Tag 07LA] agree**, in each cosimplicial degree.
* `Crystalline.columnFormsMapₛₗ` and `...'` — **the forms `Ω^a_{D(n)}` are the degree `n` of
  `Crystalline.columnFormsModule`**, for `a > 0`.
* `Crystalline.columnModuleHom` and `...'` — `M(n)` is the degree `n` of
  `Crystalline.columnModule`.
* `Crystalline.columnTensorShapeMapₛₗ` and `Crystalline.columnTensorMapₛₗ`, with their primed
  inverses — **the term `M(n) ⊗̂_{D̂(n)} Ω^a_{D(n)}` of the double complex is the degree `n` of
  `Crystalline.columnTargetModule`**, before and after completion.
* `Crystalline.cosimplicialModuleForgetIso` — the assembly of an isomorphism of cosimplicial
  abelian groups onto the underlying cosimplicial abelian group of a cosimplicial module.
* `Crystalline.columnTargetIso` — **the identity `hcolumns` asks for.**

## Main results

* `Crystalline.adicCompletionMapₛₗ_square` and
  `Crystalline.adicCompletionMapₛₗ_comp_eq_self` — a commuting square of semilinear maps, and a
  composite which is the identity, stay so after `p`-adic completion.
* `Crystalline.columnFormsShapeMapₛₗ'_columnFormsShapeMapₛₗ` and
  `...columnFormsShapeMapₛₗ_columnFormsShapeMapₛₗ'` — **the change of spelling of the forms is
  invertible.**
* `Crystalline.columnFormsShapeMapₛₗ_natural`, `Crystalline.columnFormsMapₛₗ_natural`,
  `Crystalline.columnTensorShapeMapₛₗ_natural` and `Crystalline.columnTensorMapₛₗ_natural` —
  **every comparison above is natural in the cosimplicial direction.**
* `Crystalline.isZero_homology_alternatingCofaceMapComplex_column` and
  `...isZero_homology_alternatingCofaceMapComplex_doubleComplex_X` — **the Moore cochain complex
  of the column `K^{a,•}` of the double complex has vanishing homology in every degree, for
  `a > 0`**, which is `hcolumns`.

## What is and is not proved

`hcolumns` is discharged, for a double complex built as
`Crystalline.CosimplicialCompletedPair.doubleComplex`, by
`Crystalline.isZero_homology_alternatingCofaceMapComplex_doubleComplex_X`.

**No `@[stacks 07LG]` attribute is placed**: [Stacks, Proposition 60.21.3, Tag 07LG] is
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.  The earlier reduction
`...SmallSite.computes07LG_of_doubleComplex` that this column statement serves has four further
hypotheses — the double complex `K` for a general crystal, `hker`, the second half of `hcolumn0` and
the rowwise `hrows`.

[Stacks, Tag 07LA] carries its tag where it is proved, in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedForms.lean`; the statements
below are that lemma's input read at one column, not a second proof of it.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DividedPowers Opposite
open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### Completions of composites and of squares -/

section Spelling

/-- The composite of two semilinear maps, semilinear over the composite of the two ring maps. -/
def compₛₗ {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [AddCommGroup P] [Module T P]
    (σ : R →+* S) (τ : S →+* T) (g : M →ₛₗ[σ] N) (h : N →ₛₗ[τ] P) : M →ₛₗ[τ.comp σ] P where
  toFun m := h (g m)
  map_add' x y := (congrArg (fun z => h z) (map_add g x y)).trans (map_add h (g x) (g y))
  map_smul' r m :=
    (congrArg (fun z => h z) (g.map_smulₛₗ r m)).trans (h.map_smulₛₗ (σ r) (g m))

/-- `Crystalline.compₛₗ σ τ g h` sends `m` to `h (g m)`. -/
@[simp]
theorem compₛₗ_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [AddCommGroup P] [Module T P]
    (σ : R →+* S) (τ : S →+* T) (g : M →ₛₗ[σ] N) (h : N →ₛₗ[τ] P) (m : M) :
    compₛₗ σ τ g h m = h (g m) := rfl

/-- A round trip through two adic ideals stays inside the first one. -/
theorem map_ringHom_comp_le {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (σ : R →+* S) (τ : S →+* R) (hIJ : I.map σ ≤ J) (hJI : J.map τ ≤ I) :
    I.map (τ.comp σ) ≤ I :=
  le_trans (le_of_eq (Ideal.map_map σ τ).symm) (le_trans (Ideal.map_mono hIJ) hJI)

/-- **The completion of a commuting square of semilinear maps commutes.**

Both composites are the completion of one and the same map of the uncompleted modules — of
`Crystalline.compₛₗ`, by the hypothesis `hcomm` — and
`Crystalline.adicCompletionMapₛₗ_comp_apply` reads each of them off it.  No compatibility of the
four ring maps is needed: a completion depends on its map only through the underlying
function. -/
theorem adicCompletionMapₛₗ_square {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [CommRing S'] {I : Ideal R} {I' : Ideal R'} {J : Ideal S} {J' : Ideal S'}
    {X X' Y Y' : Type*} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R' X']
    [AddCommGroup Y] [Module S Y] [AddCommGroup Y'] [Module S' Y']
    {σ : R →+* S} {σ' : R' →+* S'} {ρ : R →+* R'} {ρ' : S →+* S'}
    (ψ' : Y →ₛₗ[ρ'] Y') (g : X →ₛₗ[σ] Y) (g' : X' →ₛₗ[σ'] Y') (ψ : X →ₛₗ[ρ] X')
    (hσ : I.map σ ≤ J) (hσ' : I'.map σ' ≤ J') (hρ : I.map ρ ≤ I') (hρ' : J.map ρ' ≤ J')
    (hcomm : ∀ x, g' (ψ x) = ψ' (g x)) (z : AdicCompletion I X) :
    adicCompletionMapₛₗ g' hσ' (adicCompletionMapₛₗ ψ hρ z) =
      adicCompletionMapₛₗ ψ' hρ' (adicCompletionMapₛₗ g hσ z) :=
  have hle : I.map (σ'.comp ρ) ≤ J' :=
    le_trans (le_of_eq (Ideal.map_map ρ σ').symm) (le_trans (Ideal.map_mono hρ) hσ')
  (adicCompletionMapₛₗ_comp_apply ψ g' (compₛₗ ρ σ' ψ g') hρ hσ' hle (fun _ => rfl) z).symm.trans
    (adicCompletionMapₛₗ_comp_apply g ψ' (compₛₗ ρ σ' ψ g') hσ hρ' hle hcomm z)

/-- **A completion of a composite is the identity as soon as the composite is.** -/
theorem adicCompletionMapₛₗ_comp_eq_self {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {J : Ideal S} {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y]
    {σ : R →+* S} {τ : S →+* R} (g : X →ₛₗ[σ] Y) (h : Y →ₛₗ[τ] X) (hσ : I.map σ ≤ J)
    (hτ : J.map τ ≤ I) (hgh : ∀ x, h (g x) = x) (z : AdicCompletion I X) :
    adicCompletionMapₛₗ h hτ (adicCompletionMapₛₗ g hσ z) = z :=
  (adicCompletionMapₛₗ_comp_apply g h (compₛₗ σ τ g h) hσ hτ
      (map_ringHom_comp_le σ τ hσ hτ) (fun _ => rfl) z).symm.trans
    (adicCompletionMapₛₗ_id_apply _ (map_ringHom_comp_le σ τ hσ hτ) hgh z)

/-- **The degree of a degreewise adic completion, with the index substituted.**

`Crystalline.CosimplicialIdeal.completion` is built through
`Crystalline.SemilinearCosimplicialModule.toCosimplicialModule`, which reads the degree of a
cosimplicial module off `unop (unop X)`; so the degree `op (op n)` of a completion carries the
index `unop (unop (op (op n)))` rather than `n`.  The two reduce to each other, but see the
module documentation: the substitution has to be made here, with the cosimplicial ideal and the
cosimplicial module *variables*, and cannot be made at a concrete module.

It is linear over the degree of the cosimplicial ring. -/
def completionDegree {A : CosimplicialObject CommRingCat.{u}} (I : CosimplicialIdeal A)
    (Mod : CosimplicialModule A) (n : SimplexCategory) :
    ((I.completion Mod).obj (op (op n)) : Type u) ≃ₗ[(A.obj n : Type u)]
      AdicCompletion (I.obj n) (Mod.obj (op (op n))) :=
  LinearEquiv.refl _ _

/-- **The transition map of a degreewise adic completion**, read across
`Crystalline.completionDegree`, is the completion of the transition map of the module. -/
theorem completionDegree_transition {A : CosimplicialObject CommRingCat.{u}}
    (I : CosimplicialIdeal A) (Mod : CosimplicialModule A) {n m : SimplexCategory} (φ : n ⟶ m)
    (y : ((I.completion Mod).obj (op (op n)) : Type u)) :
    completionDegree I Mod m (cosimplicialModuleTransition (I.completion Mod) φ y) =
      adicCompletionMapₛₗ (Mod.restrictₛₗ φ.op.op) (I.map_le φ) (completionDegree I Mod n y) :=
  rfl

/-- **The degree of a tensor product of cosimplicial modules, with the index substituted.**

As for `Crystalline.completionDegree`, the degree `op (op n)` of `L ⊗ K` carries the index
`unop (unop (op (op n)))`; the substitution has to be made here, with the two cosimplicial
modules *variables*. -/
def tensorObjDegree {A : CosimplicialObject CommRingCat.{u}} (L K : CosimplicialModule A)
    (n : SimplexCategory) :
    ((MonoidalCategory.tensorObj L K).obj (op (op n)) : Type u) ≃ₗ[(A.obj n : Type u)]
      (L.obj (op (op n)) : Type u) ⊗[(A.obj n : Type u)] (K.obj (op (op n)) : Type u) :=
  LinearEquiv.refl _ _

/-- **The transition map of a tensor product of cosimplicial modules**, read across
`Crystalline.tensorObjDegree`, is the tensor of the two transition maps.  This is
`CategoryTheory.PresheafOfModules.Monoidal.tensorObj_map_tmul`, with the index substituted. -/
theorem tensorObjDegree_symm_restrictₛₗ_tmul {A : CosimplicialObject CommRingCat.{u}}
    (L K : CosimplicialModule A) {n m : SimplexCategory} (φ : n ⟶ m)
    (y : (L.obj (op (op n)) : Type u)) (z : (K.obj (op (op n)) : Type u)) :
    (MonoidalCategory.tensorObj L K).restrictₛₗ φ.op.op
        ((tensorObjDegree L K n).symm (y ⊗ₜ z)) =
      (tensorObjDegree L K m).symm
        (L.restrictₛₗ φ.op.op y ⊗ₜ K.restrictₛₗ φ.op.op z) :=
  rfl

/-- **An isomorphism of cosimplicial abelian groups onto the underlying cosimplicial abelian
group of a cosimplicial module**, from degreewise additive isomorphisms written at the
`op (op n)` spelling of the index.

This is `Crystalline.cosimplicialModuleForgetUliftIso` without the universe lift; as there, the
reindexing along `CategoryTheory.opOp` is absorbed here, with the cosimplicial module a
*variable*, and it cannot be absorbed at a concrete one. -/
def cosimplicialModuleForgetIso {A : CosimplicialObject CommRingCat.{u}}
    (Mod : CosimplicialModule A) (K : CosimplicialObject AddCommGrpCat.{u})
    (comp : ∀ n : SimplexCategory, (K.obj n : Type u) ≃+ (Mod.obj (op (op n)) : Type u))
    (hcomp : ∀ {n m : SimplexCategory} (φ : n ⟶ m) (x : (K.obj n : Type u)),
      comp m (K.map φ x) = cosimplicialModuleTransition Mod φ (comp n x)) :
    K ≅ (cosimplicialModuleForget A).obj Mod :=
  NatIso.ofComponents (fun n ↦ AddEquiv.toAddCommGrpIso (comp n)) fun {_ _} φ ↦ by
    ext x
    exact hcomp φ x

/-- A round trip of tensor products of semilinear maps is the identity. -/
private theorem tensor_map_map_eq_self {R S : Type*} [CommRing R] [CommRing S] {M N M' N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M']
    [Module S M'] [AddCommGroup N'] [Module S N'] {σ : R →+* S} {τ : S →+* R}
    {f : M →ₛₗ[σ] M'} {g : N →ₛₗ[σ] N'} {f' : M' →ₛₗ[τ] M} {g' : N' →ₛₗ[τ] N}
    (hf : ∀ x, f' (f x) = x) (hg : ∀ y, g' (g y) = y) (z : M ⊗[R] N) :
    TensorProduct.map f' g' (TensorProduct.map f g z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul y ω => rw [TensorProduct.map_tmul, TensorProduct.map_tmul, hf, hg]
  | add x y hx hy => simp only [map_add, hx, hy]

end Spelling

/-! ### The two spellings of one cosimplicial degree of the envelope -/

section Column

open AlgebraicTopology Simplicial

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)
  (W : CosimplicialCompletedModule.{u, max u w, max u w} (envelopeDPAlgebra s f) s.p)

/-- **The completed ring `D̂(n)` of the cosimplicial divided power algebra, read as the degree `n`
of the cosimplicial ring `D(*)`.**  The two are the same ring; this is the identity. -/
def columnRingHom (n : SimplexCategory) :
    (envelopeDPAlgebra s f).completedRing s.p n.len →+*
      ((cosimplicialEnvelopeRing s f hf).obj n : Type (max u w)) :=
  RingHom.id _

/-- The same identity in the other direction. -/
def columnRingHom' (n : SimplexCategory) :
    ((cosimplicialEnvelopeRing s f hf).obj n : Type (max u w)) →+*
      (envelopeDPAlgebra s f).completedRing s.p n.len :=
  RingHom.id _

/-- **The completed differentials `Ω̂_{D(n)}`, read as the degree `n` of the cosimplicial module
`Ω_{D(*)}`.**  The two are the same module; this is the identity. -/
def columnDifferentialsHom (n : SimplexCategory) :
    (envelopeDPAlgebra s f).completedDifferentials s.p n.len →ₛₗ[columnRingHom s f hf n]
      ((cosimplicialEnvelopeDifferentials s f hf).obj (op (op n)) : Type (max u w)) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The same identity in the other direction. -/
def columnDifferentialsHom' (n : SimplexCategory) :
    ((cosimplicialEnvelopeDifferentials s f hf).obj (op (op n)) : Type (max u w)) →ₛₗ[
      columnRingHom' s f hf n]
      (envelopeDPAlgebra s f).completedDifferentials s.p n.len where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The two spellings of the forms of [Stacks, Lemma 60.19.1, Tag 07LA] agree.**

The domain is `Crystalline.CosimplicialDPAlgebra.formsShape`, the `p`-adic completion of the
exterior power of `Crystalline.CosimplicialDPAlgebra.completedDifferentials` over
`Crystalline.CosimplicialDPAlgebra.completedRing`; the codomain is the degree `n` of
`Crystalline.columnFormsModule`, the same thing written with the cosimplicial ring and the
cosimplicial module of differentials, read across `Crystalline.completionDegree`.  The change of
spelling is `ExteriorAlgebra.powMapₛₗ` of `Crystalline.columnDifferentialsHom`: it is performed
on the ring and on the differentials and carried into the exterior power, never ascribed to
one. -/
def columnFormsShapeMapₛₗ (a : ℕ) (n : SimplexCategory) :
    (envelopeDPAlgebra s f).formsShape s.p a n.len →ₛₗ[columnRingHom s f hf n]
      AdicCompletion ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).obj n)
        (((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
          (cosimplicialEnvelopeDifferentials s f hf)).obj (op (op n))) :=
  adicCompletionMapₛₗ (ExteriorAlgebra.powMapₛₗ a (columnRingHom s f hf n)
    (columnDifferentialsHom s f hf n)) (map_pAdicIdeal_le s.p (columnRingHom s f hf n))

/-- The comparison of the two spellings of the forms, in the other direction. -/
def columnFormsShapeMapₛₗ' (a : ℕ) (n : SimplexCategory) :
    AdicCompletion ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).obj n)
        (((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
          (cosimplicialEnvelopeDifferentials s f hf)).obj (op (op n))) →ₛₗ[
      columnRingHom' s f hf n]
      (envelopeDPAlgebra s f).formsShape s.p a n.len :=
  adicCompletionMapₛₗ (ExteriorAlgebra.powMapₛₗ a (columnRingHom' s f hf n)
    (columnDifferentialsHom' s f hf n)) (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))

/-- A round trip of semilinear maps stays the identity on the exterior power. -/
private theorem powMapₛₗ_comp_eq_self {R S : Type*} [CommRing R] [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (n : ℕ) {σ : R →+* S}
    {τ : S →+* R} (u : M →ₛₗ[σ] N) (v : N →ₛₗ[τ] M) (hστ : ∀ r, τ (σ r) = r)
    (huv : ∀ m, v (u m) = m) (z : ⋀[R]^n M) :
    ExteriorAlgebra.powMapₛₗ n τ v (ExteriorAlgebra.powMapₛₗ n σ u z) = z :=
  (ExteriorAlgebra.powMapₛₗ_eq_comp n u v (compₛₗ σ τ u v) (fun _ => rfl) (fun _ => rfl)
      z).symm.trans
    (ExteriorAlgebra.powMapₛₗ_eq_self n (compₛₗ σ τ u v) hστ huv z)

/-- **The comparison of the two spellings of the forms is invertible**, one way round. -/
theorem columnFormsShapeMapₛₗ'_columnFormsShapeMapₛₗ (a : ℕ) (n : SimplexCategory)
    (x : (envelopeDPAlgebra s f).formsShape s.p a n.len) :
    columnFormsShapeMapₛₗ' s f hf a n (columnFormsShapeMapₛₗ s f hf a n x) = x :=
  adicCompletionMapₛₗ_comp_eq_self
    (ExteriorAlgebra.powMapₛₗ a (columnRingHom s f hf n) (columnDifferentialsHom s f hf n))
    (ExteriorAlgebra.powMapₛₗ a (columnRingHom' s f hf n) (columnDifferentialsHom' s f hf n))
    (map_pAdicIdeal_le s.p (columnRingHom s f hf n))
    (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))
    (powMapₛₗ_comp_eq_self a (columnDifferentialsHom s f hf n)
      (columnDifferentialsHom' s f hf n) (fun _ => rfl) (fun _ => rfl)) x

/-- **The comparison of the two spellings of the forms is invertible**, the other way round. -/
theorem columnFormsShapeMapₛₗ_columnFormsShapeMapₛₗ' (a : ℕ) (n : SimplexCategory)
    (y : AdicCompletion ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).obj n)
      (((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
        (cosimplicialEnvelopeDifferentials s f hf)).obj (op (op n)))) :
    columnFormsShapeMapₛₗ s f hf a n (columnFormsShapeMapₛₗ' s f hf a n y) = y :=
  adicCompletionMapₛₗ_comp_eq_self
    (ExteriorAlgebra.powMapₛₗ a (columnRingHom' s f hf n) (columnDifferentialsHom' s f hf n))
    (ExteriorAlgebra.powMapₛₗ a (columnRingHom s f hf n) (columnDifferentialsHom s f hf n))
    (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))
    (map_pAdicIdeal_le s.p (columnRingHom s f hf n))
    (powMapₛₗ_comp_eq_self a (columnDifferentialsHom' s f hf n)
      (columnDifferentialsHom s f hf n) (fun _ => rfl) (fun _ => rfl)) y

/-- **The change of spelling of the forms is natural in the cosimplicial direction.**

The transition map of the degreewise exterior power is `ExteriorAlgebra.powMapₛₗ` of the
transition map of the differentials by `Crystalline.exteriorPowerFunctor_restrictₛₗ`, the
transition map of `Crystalline.CosimplicialDPAlgebra.formsShape` is `ExteriorAlgebra.powMapₛₗ`
of the transition map of `Crystalline.CosimplicialDPAlgebra.completedDifferentials`, and the two
transition maps of differentials are the same map; so both composites are
`ExteriorAlgebra.powMapₛₗ` of one composite map of differentials, and
`Crystalline.adicCompletionMapₛₗ_square` completes them. -/
theorem columnFormsShapeMapₛₗ_natural (a : ℕ) {n m : SimplexCategory} (φ : n ⟶ m)
    (x : (envelopeDPAlgebra s f).formsShape s.p a n.len) :
    columnFormsShapeMapₛₗ s f hf a m ((envelopeDPAlgebra s f).formsShapeMap s.p φ a x) =
      adicCompletionMapₛₗ
        (((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
          (cosimplicialEnvelopeDifferentials s f hf)).restrictₛₗ φ.op.op)
        ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).map_le φ)
        (columnFormsShapeMapₛₗ s f hf a n x) := by
  refine adicCompletionMapₛₗ_square _ _ _ _ _ _ _ _ ?_ x
  intro z
  rw [exteriorPowerFunctor_restrictₛₗ]
  exact (ExteriorAlgebra.powMapₛₗ_eq_comp a
        ((envelopeDPAlgebra s f).completedDifferentialsMap s.p φ)
        (columnDifferentialsHom s f hf m)
        (compₛₗ ((envelopeDPAlgebra s f).completedRingMap s.p φ) (columnRingHom s f hf m)
          ((envelopeDPAlgebra s f).completedDifferentialsMap s.p φ)
          (columnDifferentialsHom s f hf m)) (fun _ => rfl) (fun _ => rfl) z).symm.trans
    (ExteriorAlgebra.powMapₛₗ_eq_comp a (columnDifferentialsHom s f hf n)
      ((cosimplicialEnvelopeDifferentials s f hf).restrictₛₗ φ.op.op)
      (compₛₗ ((envelopeDPAlgebra s f).completedRingMap s.p φ) (columnRingHom s f hf m)
        ((envelopeDPAlgebra s f).completedDifferentialsMap s.p φ)
        (columnDifferentialsHom s f hf m)) (fun _ => rfl) (fun _ => rfl) z)

/-! ### The forms as the degrees of `columnFormsModule` -/

/-- The transport of `Crystalline.completionDegree` at the degreewise completion that
`Crystalline.columnFormsModule` is. -/
abbrev columnFormsDegree (a : ℕ) (n : SimplexCategory) :=
  completionDegree (pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p)
    ((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
      (cosimplicialEnvelopeDifferentials s f hf)) n

/-- **The forms `Ω^a_{D(n)}` as the degree `n` of `Crystalline.columnFormsModule`**, for `a > 0`:
the comparison of the two shapes of the forms,
`Crystalline.CosimplicialDPAlgebra.formsShapeEquiv`, then the change of spelling, then
`Crystalline.completionDegree`. -/
def columnFormsMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    (envelopeDPAlgebra s f).forms s.p a n.len →ₛₗ[columnRingHom s f hf n]
      ((columnFormsModule s f hf a).obj (op (op n)) : Type (max u w)) where
  toFun x := (columnFormsDegree s f hf a n).symm
    (columnFormsShapeMapₛₗ s f hf a n
      ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x))
  map_add' x y :=
    (congrArg (fun z => (columnFormsDegree s f hf a n).symm
          (columnFormsShapeMapₛₗ s f hf a n z))
        (map_add ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha) x y)).trans
      ((congrArg (fun z => (columnFormsDegree s f hf a n).symm z)
          (map_add (columnFormsShapeMapₛₗ s f hf a n) _ _)).trans
        (map_add (columnFormsDegree s f hf a n).symm _ _))
  map_smul' r x :=
    (congrArg (fun z => (columnFormsDegree s f hf a n).symm
          (columnFormsShapeMapₛₗ s f hf a n z))
        (map_smul ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha) r x)).trans
      ((congrArg (fun z => (columnFormsDegree s f hf a n).symm z)
          ((columnFormsShapeMapₛₗ s f hf a n).map_smulₛₗ r _)).trans
        (map_smul (columnFormsDegree s f hf a n).symm _ _))

/-- The same comparison in the other direction. -/
def columnFormsMapₛₗ' (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    ((columnFormsModule s f hf a).obj (op (op n)) : Type (max u w)) →ₛₗ[columnRingHom' s f hf n]
      (envelopeDPAlgebra s f).forms s.p a n.len where
  toFun y := ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm
    (columnFormsShapeMapₛₗ' s f hf a n (columnFormsDegree s f hf a n y))
  map_add' x y :=
    (congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm
          (columnFormsShapeMapₛₗ' s f hf a n z))
        (map_add (columnFormsDegree s f hf a n) x y)).trans
      ((congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm z)
          (map_add (columnFormsShapeMapₛₗ' s f hf a n) _ _)).trans
        (map_add ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm _ _))
  map_smul' t y :=
    (congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm
          (columnFormsShapeMapₛₗ' s f hf a n z))
        (map_smul (columnFormsDegree s f hf a n) t y)).trans
      ((congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm z)
          ((columnFormsShapeMapₛₗ' s f hf a n).map_smulₛₗ _ _)).trans
        (map_smul ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm _ _))

/-- **`Crystalline.columnFormsMapₛₗ` read across `Crystalline.completionDegree`** is the change
of spelling of the forms after the comparison of the two shapes.

The transport is undone by `LinearEquiv.apply_symm_apply` and not by reduction: see the module
documentation — `Crystalline.completionDegree` is `LinearEquiv.refl`, but *reducing* it at the
degreewise exterior power makes the two `Module` instances on that degree meet, which is the
unification this module exists to avoid. -/
theorem columnFormsMapₛₗ_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (x : (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnFormsMapₛₗ s f hf a ha n x =
      (columnFormsDegree s f hf a n).symm
        (columnFormsShapeMapₛₗ s f hf a n
          ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x)) :=
  rfl

/-- `Crystalline.columnFormsMapₛₗ` followed by `Crystalline.columnFormsDegree` is the change of
spelling of the forms after the comparison of the two shapes. -/
theorem columnFormsDegree_columnFormsMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (x : (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnFormsDegree s f hf a n (columnFormsMapₛₗ s f hf a ha n x) =
      columnFormsShapeMapₛₗ s f hf a n
        ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x) :=
  (congrArg (fun z => columnFormsDegree s f hf a n z)
      (columnFormsMapₛₗ_apply s f hf a ha n x)).trans
    ((columnFormsDegree s f hf a n).apply_symm_apply _)

/-- `Crystalline.columnFormsMapₛₗ'` is `Crystalline.columnFormsDegree`, then the change of
spelling of the forms back, then the inverse comparison of the two shapes. -/
theorem columnFormsMapₛₗ'_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (y : ((columnFormsModule s f hf a).obj (op (op n)) : Type (max u w))) :
    columnFormsMapₛₗ' s f hf a ha n y =
      ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm
        (columnFormsShapeMapₛₗ' s f hf a n (columnFormsDegree s f hf a n y)) :=
  rfl

/-- **The comparison of the forms with the degrees of `Crystalline.columnFormsModule` is
invertible**, one way round. -/
theorem columnFormsMapₛₗ'_columnFormsMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (x : (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnFormsMapₛₗ' s f hf a ha n (columnFormsMapₛₗ s f hf a ha n x) = x :=
  (columnFormsMapₛₗ'_apply s f hf a ha n (columnFormsMapₛₗ s f hf a ha n x)).trans
    ((congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm
            (columnFormsShapeMapₛₗ' s f hf a n z))
          (columnFormsDegree_columnFormsMapₛₗ s f hf a ha n x)).trans
      ((congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm z)
          (columnFormsShapeMapₛₗ'_columnFormsShapeMapₛₗ s f hf a n
            ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x))).trans
        (((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).symm_apply_apply x)))

/-- **The comparison of the forms with the degrees of `Crystalline.columnFormsModule` is
invertible**, the other way round. -/
theorem columnFormsMapₛₗ_columnFormsMapₛₗ' (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (y : ((columnFormsModule s f hf a).obj (op (op n)) : Type (max u w))) :
    columnFormsMapₛₗ s f hf a ha n (columnFormsMapₛₗ' s f hf a ha n y) = y :=
  (columnFormsDegree s f hf a n).injective
    ((columnFormsDegree_columnFormsMapₛₗ s f hf a ha n
          (columnFormsMapₛₗ' s f hf a ha n y)).trans
      ((congrArg (fun z => columnFormsShapeMapₛₗ s f hf a n z)
            ((congrArg (fun z => ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha) z)
                (columnFormsMapₛₗ'_apply s f hf a ha n y)).trans
              (((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha).apply_symm_apply
                (columnFormsShapeMapₛₗ' s f hf a n (columnFormsDegree s f hf a n y))))).trans
        (columnFormsShapeMapₛₗ_columnFormsShapeMapₛₗ' s f hf a n
          (columnFormsDegree s f hf a n y))))

/-- The transition map of `Crystalline.columnFormsModule`, read across
`Crystalline.completionDegree` on the image of the comparison of the forms. -/
theorem columnFormsDegree_cosimplicialModuleTransition (a : ℕ) (ha : 0 < a)
    {n m : SimplexCategory} (φ : n ⟶ m) (x : (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnFormsDegree s f hf a m
        (cosimplicialModuleTransition (columnFormsModule s f hf a) φ
          (columnFormsMapₛₗ s f hf a ha n x)) =
      adicCompletionMapₛₗ
        (((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
          (cosimplicialEnvelopeDifferentials s f hf)).restrictₛₗ φ.op.op)
        ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).map_le φ)
        (columnFormsShapeMapₛₗ s f hf a n
          ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x)) :=
  (completionDegree_transition _ _ φ _).trans
    (congrArg _ (columnFormsDegree_columnFormsMapₛₗ s f hf a ha n x))

/-- **The comparison of the forms with the degrees of `Crystalline.columnFormsModule` is natural
in the cosimplicial direction.** -/
theorem columnFormsMapₛₗ_natural (a : ℕ) (ha : 0 < a) {n m : SimplexCategory} (φ : n ⟶ m)
    (x : (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnFormsMapₛₗ s f hf a ha m ((envelopeDPAlgebra s f).formsMap s.p φ a x) =
      cosimplicialModuleTransition (columnFormsModule s f hf a) φ
        (columnFormsMapₛₗ s f hf a ha n x) :=
  (columnFormsDegree s f hf a m).injective
    ((columnFormsDegree_columnFormsMapₛₗ s f hf a ha m
          ((envelopeDPAlgebra s f).formsMap s.p φ a x)).trans
      ((congrArg (fun z => columnFormsShapeMapₛₗ s f hf a m z)
            ((envelopeDPAlgebra s f).formsShapeEquiv_formsMap s.p φ a ha x).symm).trans
        ((columnFormsShapeMapₛₗ_natural s f hf a φ
              ((envelopeDPAlgebra s f).formsShapeEquiv s.p a n.len ha x)).trans
          (columnFormsDegree_cosimplicialModuleTransition s f hf a ha φ x).symm)))

/-! ### The tensor direction -/

/-- **The module `M(n)` of the column, read as the degree `n` of `Crystalline.columnModule`.**
The two are the same module; this is the identity. -/
def columnModuleHom (n : SimplexCategory) :
    W.carrier n.len →ₛₗ[columnRingHom s f hf n]
      ((columnModule s f hf W).obj (op (op n)) : Type (max u w)) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The same identity in the other direction. -/
def columnModuleHom' (n : SimplexCategory) :
    ((columnModule s f hf W).obj (op (op n)) : Type (max u w)) →ₛₗ[columnRingHom' s f hf n]
      W.carrier n.len where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `Crystalline.columnModuleHom'` undoes `Crystalline.columnModuleHom`. -/
@[simp]
theorem columnModuleHom'_columnModuleHom (n : SimplexCategory) (y : W.carrier n.len) :
    columnModuleHom' s f hf W n (columnModuleHom s f hf W n y) = y :=
  rfl

/-- `Crystalline.columnModuleHom` undoes `Crystalline.columnModuleHom'`. -/
@[simp]
theorem columnModuleHom_columnModuleHom' (n : SimplexCategory)
    (y : ((columnModule s f hf W).obj (op (op n)) : Type (max u w))) :
    columnModuleHom s f hf W n (columnModuleHom' s f hf W n y) = y :=
  rfl

/-- **The transition map of `Crystalline.columnModule` is the transition map of `M(•)`.** -/
theorem columnModuleHom_natural {n m : SimplexCategory} (φ : n ⟶ m) (y : W.carrier n.len) :
    columnModuleHom s f hf W m (W.map φ y) =
      (columnModule s f hf W).restrictₛₗ φ.op.op (columnModuleHom s f hf W n y) :=
  rfl

/-- The transport of `Crystalline.tensorObjDegree` at the tensor product of cosimplicial modules
underlying `Crystalline.columnTargetModule`. -/
abbrev columnTensorDegree (a : ℕ) (n : SimplexCategory) :=
  tensorObjDegree (columnModule s f hf W) (columnFormsModule s f hf a) n

/-- **The uncompleted tensor product `M(n) ⊗_{D̂(n)} Ω^a_{D(n)}` of the column, read as the degree
`n` of `M(•) ⊗ Ω^a_{D(•)}`**, for `a > 0`: the tensor of `Crystalline.columnModuleHom` with
`Crystalline.columnFormsMapₛₗ`, read across `Crystalline.tensorObjDegree`. -/
def columnTensorShapeMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    (W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
        (envelopeDPAlgebra s f).forms s.p a n.len) →ₛₗ[columnRingHom s f hf n]
      ((MonoidalCategory.tensorObj (columnModule s f hf W)
        (columnFormsModule s f hf a)).obj (op (op n)) : Type (max u w)) where
  toFun z := (columnTensorDegree s f hf W a n).symm
    (TensorProduct.map (columnModuleHom s f hf W n) (columnFormsMapₛₗ s f hf a ha n) z)
  map_add' x y :=
    (congrArg (fun z => (columnTensorDegree s f hf W a n).symm z)
        (map_add (TensorProduct.map (columnModuleHom s f hf W n)
          (columnFormsMapₛₗ s f hf a ha n)) x y)).trans
      (map_add (columnTensorDegree s f hf W a n).symm _ _)
  map_smul' r z :=
    (congrArg (fun z => (columnTensorDegree s f hf W a n).symm z)
        ((TensorProduct.map (columnModuleHom s f hf W n)
          (columnFormsMapₛₗ s f hf a ha n)).map_smulₛₗ r z)).trans
      (map_smul (columnTensorDegree s f hf W a n).symm _ _)

/-- `Crystalline.columnTensorShapeMapₛₗ` is the tensor of `Crystalline.columnModuleHom` with
`Crystalline.columnFormsMapₛₗ`, read across `Crystalline.columnTensorDegree`. -/
theorem columnTensorShapeMapₛₗ_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
      (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnTensorShapeMapₛₗ s f hf W a ha n z =
      (columnTensorDegree s f hf W a n).symm
        (TensorProduct.map (columnModuleHom s f hf W n) (columnFormsMapₛₗ s f hf a ha n) z) :=
  rfl

/-- The same comparison in the other direction. -/
def columnTensorShapeMapₛₗ' (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    ((MonoidalCategory.tensorObj (columnModule s f hf W)
        (columnFormsModule s f hf a)).obj (op (op n)) : Type (max u w)) →ₛₗ[
      columnRingHom' s f hf n]
      (W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
        (envelopeDPAlgebra s f).forms s.p a n.len) where
  toFun z := TensorProduct.map (columnModuleHom' s f hf W n) (columnFormsMapₛₗ' s f hf a ha n)
    (columnTensorDegree s f hf W a n z)
  map_add' x y :=
    (congrArg (fun z => TensorProduct.map (columnModuleHom' s f hf W n)
          (columnFormsMapₛₗ' s f hf a ha n) z)
        (map_add (columnTensorDegree s f hf W a n) x y)).trans
      (map_add (TensorProduct.map (columnModuleHom' s f hf W n)
        (columnFormsMapₛₗ' s f hf a ha n)) _ _)
  map_smul' r z :=
    (congrArg (fun z => TensorProduct.map (columnModuleHom' s f hf W n)
          (columnFormsMapₛₗ' s f hf a ha n) z)
        (map_smul (columnTensorDegree s f hf W a n) r z)).trans
      ((TensorProduct.map (columnModuleHom' s f hf W n)
        (columnFormsMapₛₗ' s f hf a ha n)).map_smulₛₗ _ _)

/-- `Crystalline.columnTensorShapeMapₛₗ'` is `Crystalline.columnTensorDegree` followed by the
tensor of `Crystalline.columnModuleHom'` with `Crystalline.columnFormsMapₛₗ'`. -/
theorem columnTensorShapeMapₛₗ'_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : ((MonoidalCategory.tensorObj (columnModule s f hf W)
      (columnFormsModule s f hf a)).obj (op (op n)) : Type (max u w))) :
    columnTensorShapeMapₛₗ' s f hf W a ha n z =
      TensorProduct.map (columnModuleHom' s f hf W n) (columnFormsMapₛₗ' s f hf a ha n)
        (columnTensorDegree s f hf W a n z) :=
  rfl

/-- `Crystalline.columnTensorShapeMapₛₗ` followed by `Crystalline.columnTensorDegree` is the
tensor of `Crystalline.columnModuleHom` with `Crystalline.columnFormsMapₛₗ`. -/
theorem columnTensorDegree_columnTensorShapeMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
      (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnTensorDegree s f hf W a n (columnTensorShapeMapₛₗ s f hf W a ha n z) =
      TensorProduct.map (columnModuleHom s f hf W n) (columnFormsMapₛₗ s f hf a ha n) z :=
  (columnTensorDegree s f hf W a n).apply_symm_apply _

/-- **The tensor of the two comparisons is invertible on the uncompleted tensor product**, one
way round. -/
theorem columnTensorShapeMapₛₗ'_columnTensorShapeMapₛₗ (a : ℕ) (ha : 0 < a)
    (n : SimplexCategory)
    (z : W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
      (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnTensorShapeMapₛₗ' s f hf W a ha n (columnTensorShapeMapₛₗ s f hf W a ha n z) = z := by
  refine ((columnTensorShapeMapₛₗ'_apply s f hf W a ha n _).trans
    (congrArg (fun t => TensorProduct.map (columnModuleHom' s f hf W n)
        (columnFormsMapₛₗ' s f hf a ha n) t)
      (columnTensorDegree_columnTensorShapeMapₛₗ s f hf W a ha n z))).trans ?_
  exact tensor_map_map_eq_self (columnModuleHom'_columnModuleHom s f hf W n)
    (columnFormsMapₛₗ'_columnFormsMapₛₗ s f hf a ha n) z

/-- The round trip of the tensor of the two comparisons on the degree of `M(•) ⊗ Ω^a_{D(•)}`. -/
theorem columnTensorMap_columnTensorMap' (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (t : ((columnModule s f hf W).obj (op (op n)) : Type (max u w))
      ⊗[((cosimplicialEnvelopeRing s f hf).obj n : Type (max u w))]
      ((columnFormsModule s f hf a).obj (op (op n)) : Type (max u w))) :
    TensorProduct.map (columnModuleHom s f hf W n) (columnFormsMapₛₗ s f hf a ha n)
        (TensorProduct.map (columnModuleHom' s f hf W n)
          (columnFormsMapₛₗ' s f hf a ha n) t) = t :=
  tensor_map_map_eq_self (columnModuleHom_columnModuleHom' s f hf W n)
    (columnFormsMapₛₗ_columnFormsMapₛₗ' s f hf a ha n) t

/-- **The tensor of the two comparisons is invertible on the uncompleted tensor product**, the
other way round. -/
theorem columnTensorShapeMapₛₗ_columnTensorShapeMapₛₗ' (a : ℕ) (ha : 0 < a)
    (n : SimplexCategory)
    (w : ((MonoidalCategory.tensorObj (columnModule s f hf W)
      (columnFormsModule s f hf a)).obj (op (op n)) : Type (max u w))) :
    columnTensorShapeMapₛₗ s f hf W a ha n (columnTensorShapeMapₛₗ' s f hf W a ha n w) = w :=
  (columnTensorDegree s f hf W a n).injective
    ((columnTensorDegree_columnTensorShapeMapₛₗ s f hf W a ha n
          (columnTensorShapeMapₛₗ' s f hf W a ha n w)).trans
      ((congrArg (fun t => TensorProduct.map (columnModuleHom s f hf W n)
            (columnFormsMapₛₗ s f hf a ha n) t)
          (columnTensorShapeMapₛₗ'_apply s f hf W a ha n w)).trans
        (columnTensorMap_columnTensorMap' s f hf W a ha n
          (columnTensorDegree s f hf W a n w))))

/-- **The tensor of the two comparisons is natural in the cosimplicial direction.** -/
theorem columnTensorShapeMapₛₗ_natural (a : ℕ) (ha : 0 < a) {n m : SimplexCategory} (φ : n ⟶ m)
    (z : W.carrier n.len ⊗[(envelopeDPAlgebra s f).completedRing s.p n.len]
      (envelopeDPAlgebra s f).forms s.p a n.len) :
    columnTensorShapeMapₛₗ s f hf W a ha m
        (TensorProduct.map (W.map φ) ((envelopeDPAlgebra s f).formsMapCompleted s.p φ a) z) =
      (MonoidalCategory.tensorObj (columnModule s f hf W)
        (columnFormsModule s f hf a)).restrictₛₗ φ.op.op
        (columnTensorShapeMapₛₗ s f hf W a ha n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul y ω =>
    rw [columnTensorShapeMapₛₗ_apply, columnTensorShapeMapₛₗ_apply,
      TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      tensorObjDegree_symm_restrictₛₗ_tmul]
    exact congrArg (fun t => (columnTensorDegree s f hf W a m).symm
        (columnModuleHom s f hf W m (W.map φ y) ⊗ₜ t))
      (columnFormsMapₛₗ_natural s f hf a ha φ ω)
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The column as the degrees of `columnTargetModule` -/

/-- The transport of `Crystalline.completionDegree` at the degreewise completion that
`Crystalline.columnTargetModule` is. -/
abbrev columnTargetDegree (a : ℕ) (n : SimplexCategory) :=
  completionDegree (pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p)
    (MonoidalCategory.tensorObj (columnModule s f hf W) (columnFormsModule s f hf a)) n

/-- **The degree `(a, n)` term `M(n) ⊗̂_{D̂(n)} Ω^a_{D(n)}` of the double complex as the degree `n`
of `Crystalline.columnTargetModule`**, for `a > 0`: the `p`-adic completion of
`Crystalline.columnTensorShapeMapₛₗ`, read across `Crystalline.completionDegree`. -/
def columnTensorMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    W.obj a n.len →ₛₗ[columnRingHom s f hf n]
      ((columnTargetModule s f hf W a).obj (op (op n)) : Type (max u w)) where
  toFun z := (columnTargetDegree s f hf W a n).symm
    (adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
      (map_pAdicIdeal_le s.p (columnRingHom s f hf n)) z)
  map_add' x y :=
    (congrArg (fun t => (columnTargetDegree s f hf W a n).symm t)
        (map_add (adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom s f hf n))) x y)).trans
      (map_add (columnTargetDegree s f hf W a n).symm _ _)
  map_smul' r z :=
    (congrArg (fun t => (columnTargetDegree s f hf W a n).symm t)
        ((adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom s f hf n))).map_smulₛₗ r z)).trans
      (map_smul (columnTargetDegree s f hf W a n).symm _ _)

/-- `Crystalline.columnTensorMapₛₗ` is the `p`-adic completion of
`Crystalline.columnTensorShapeMapₛₗ`, read across `Crystalline.columnTargetDegree`. -/
theorem columnTensorMapₛₗ_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : W.obj a n.len) :
    columnTensorMapₛₗ s f hf W a ha n z =
      (columnTargetDegree s f hf W a n).symm
        (adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom s f hf n)) z) :=
  rfl

/-- `Crystalline.columnTensorMapₛₗ` followed by `Crystalline.columnTargetDegree` is the `p`-adic
completion of `Crystalline.columnTensorShapeMapₛₗ`. -/
theorem columnTargetDegree_columnTensorMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : W.obj a n.len) :
    columnTargetDegree s f hf W a n (columnTensorMapₛₗ s f hf W a ha n z) =
      adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
        (map_pAdicIdeal_le s.p (columnRingHom s f hf n)) z :=
  (congrArg (fun t => columnTargetDegree s f hf W a n t)
      (columnTensorMapₛₗ_apply s f hf W a ha n z)).trans
    ((columnTargetDegree s f hf W a n).apply_symm_apply _)

/-- The same comparison in the other direction. -/
def columnTensorMapₛₗ' (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    ((columnTargetModule s f hf W a).obj (op (op n)) : Type (max u w)) →ₛₗ[
      columnRingHom' s f hf n] W.obj a n.len where
  toFun w := adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
    (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))
    (columnTargetDegree s f hf W a n w)
  map_add' x y :=
    (congrArg (fun t => adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom' s f hf n)) t)
        (map_add (columnTargetDegree s f hf W a n) x y)).trans
      (map_add (adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
        (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))) _ _)
  map_smul' r w :=
    (congrArg (fun t => adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom' s f hf n)) t)
        (map_smul (columnTargetDegree s f hf W a n) r w)).trans
      ((adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
        (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))).map_smulₛₗ _ _)

/-- `Crystalline.columnTensorMapₛₗ'` is `Crystalline.columnTargetDegree` followed by the `p`-adic
completion of `Crystalline.columnTensorShapeMapₛₗ'`. -/
theorem columnTensorMapₛₗ'_apply (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (w : ((columnTargetModule s f hf W a).obj (op (op n)) : Type (max u w))) :
    columnTensorMapₛₗ' s f hf W a ha n w =
      adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
        (map_pAdicIdeal_le s.p (columnRingHom' s f hf n))
        (columnTargetDegree s f hf W a n w) :=
  rfl

/-- **The comparison of the column with the degrees of `Crystalline.columnTargetModule` is
invertible**, one way round. -/
theorem columnTensorMapₛₗ'_columnTensorMapₛₗ (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (z : W.obj a n.len) :
    columnTensorMapₛₗ' s f hf W a ha n (columnTensorMapₛₗ s f hf W a ha n z) = z :=
  (columnTensorMapₛₗ'_apply s f hf W a ha n (columnTensorMapₛₗ s f hf W a ha n z)).trans
    ((congrArg (fun t => adicCompletionMapₛₗ (columnTensorShapeMapₛₗ' s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom' s f hf n)) t)
        (columnTargetDegree_columnTensorMapₛₗ s f hf W a ha n z)).trans
      (adicCompletionMapₛₗ_comp_eq_self _ _ _ _
        (columnTensorShapeMapₛₗ'_columnTensorShapeMapₛₗ s f hf W a ha n) z))

/-- **The comparison of the column with the degrees of `Crystalline.columnTargetModule` is
invertible**, the other way round. -/
theorem columnTensorMapₛₗ_columnTensorMapₛₗ' (a : ℕ) (ha : 0 < a) (n : SimplexCategory)
    (w : ((columnTargetModule s f hf W a).obj (op (op n)) : Type (max u w))) :
    columnTensorMapₛₗ s f hf W a ha n (columnTensorMapₛₗ' s f hf W a ha n w) = w :=
  (columnTargetDegree s f hf W a n).injective
    ((columnTargetDegree_columnTensorMapₛₗ s f hf W a ha n
          (columnTensorMapₛₗ' s f hf W a ha n w)).trans
      ((congrArg (fun t => adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
            (map_pAdicIdeal_le s.p (columnRingHom s f hf n)) t)
          (columnTensorMapₛₗ'_apply s f hf W a ha n w)).trans
        (adicCompletionMapₛₗ_comp_eq_self _ _ _ _
          (columnTensorShapeMapₛₗ_columnTensorShapeMapₛₗ' s f hf W a ha n)
          (columnTargetDegree s f hf W a n w))))

/-- The transition map of `Crystalline.columnTargetModule`, read across
`Crystalline.completionDegree` on the image of the comparison of the column. -/
theorem columnTargetDegree_cosimplicialModuleTransition (a : ℕ) (ha : 0 < a)
    {n m : SimplexCategory} (φ : n ⟶ m) (z : W.obj a n.len) :
    columnTargetDegree s f hf W a m
        (cosimplicialModuleTransition (columnTargetModule s f hf W a) φ
          (columnTensorMapₛₗ s f hf W a ha n z)) =
      adicCompletionMapₛₗ
        ((MonoidalCategory.tensorObj (columnModule s f hf W)
          (columnFormsModule s f hf a)).restrictₛₗ φ.op.op)
        ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).map_le φ)
        (adicCompletionMapₛₗ (columnTensorShapeMapₛₗ s f hf W a ha n)
          (map_pAdicIdeal_le s.p (columnRingHom s f hf n)) z) :=
  (completionDegree_transition _ _ φ _).trans
    (congrArg _ (columnTargetDegree_columnTensorMapₛₗ s f hf W a ha n z))

/-- **The comparison of the column with the degrees of `Crystalline.columnTargetModule` is
natural in the cosimplicial direction.** -/
theorem columnTensorMapₛₗ_natural (a : ℕ) (ha : 0 < a) {n m : SimplexCategory} (φ : n ⟶ m)
    (z : W.obj a n.len) :
    columnTensorMapₛₗ s f hf W a ha m (W.tensorMap φ a z) =
      cosimplicialModuleTransition (columnTargetModule s f hf W a) φ
        (columnTensorMapₛₗ s f hf W a ha n z) :=
  (columnTargetDegree s f hf W a m).injective
    ((columnTargetDegree_columnTensorMapₛₗ s f hf W a ha m (W.tensorMap φ a z)).trans
      ((adicCompletionMapₛₗ_square _ _ _ _ _ _ _ _
            (columnTensorShapeMapₛₗ_natural s f hf W a ha φ) z).trans
        (columnTargetDegree_cosimplicialModuleTransition s f hf W a ha φ z).symm))

/-- **The degree `n` of the column `K^{a,•}` is the degree `n` of
`Crystalline.columnTargetModule`**, as abelian groups, for `a > 0`. -/
def columnTargetEquiv (a : ℕ) (ha : 0 < a) (n : SimplexCategory) :
    (((W.column a).obj n : Type (max u w))) ≃+
      ((columnTargetModule s f hf W a).obj (op (op n)) : Type (max u w)) where
  toFun := columnTensorMapₛₗ s f hf W a ha n
  invFun := columnTensorMapₛₗ' s f hf W a ha n
  left_inv := columnTensorMapₛₗ'_columnTensorMapₛₗ s f hf W a ha n
  right_inv := columnTensorMapₛₗ_columnTensorMapₛₗ' s f hf W a ha n
  map_add' := map_add (columnTensorMapₛₗ s f hf W a ha n)

/-- **The column `K^{a,•}` of the double complex is the underlying cosimplicial abelian group of
`Crystalline.columnTargetModule`**, for `a > 0`.

This is the identity `K^{a,b} = M(b) ⊗̂_{D̂(b)} Ω^a_{D(b)} ≅ (M(•) ⊗̂_{D(•)} Ω^a_{D(•)})_b` that
`hcolumns` asks for, assembled from `Crystalline.columnTensorMapₛₗ` and its naturality by
`Crystalline.cosimplicialModuleForgetIso`. -/
def columnTargetIso (a : ℕ) (ha : 0 < a) :
    W.column a ≅ (cosimplicialModuleForget (cosimplicialEnvelopeRing s f hf)).obj
      (columnTargetModule s f hf W a) :=
  cosimplicialModuleForgetIso (columnTargetModule s f hf W a) (W.column a)
    (columnTargetEquiv s f hf W a ha)
    (fun {_n _m} φ x => columnTensorMapₛₗ_natural s f hf W a ha φ x)

include hf in
/-- **[Stacks, Lemma 60.19.1, Tag 07LA] for the columns of the double complex**: the Moore
cochain complex of the column `K^{a,•}` has vanishing homology in every degree, for `a > 0`.

`Crystalline.columnTargetIso` identifies the column with the underlying cosimplicial abelian
group of `Crystalline.columnTargetModule`, whose identity is homotopic to zero by
`Crystalline.homotopic_id_columnTargetModule_zero`; no connection is involved. -/
theorem isZero_homology_alternatingCofaceMapComplex_column (a : ℕ) (ha : 0 < a) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max u w}).obj
      (W.column a)).homology j) :=
  isZero_homology_alternatingCofaceMapComplex_of_iso (columnTargetIso s f hf W a ha) j
    (isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero
      (homotopic_id_columnTargetModule_zero s f hf W a ha) j)

include hf in
/-- **`hcolumns` of `...SmallSite.computes07LG_of_doubleComplex` for a double complex built as
`Crystalline.CosimplicialCompletedPair.doubleComplex`**: the columns off `0` of `K` are acyclic.

`Crystalline.CosimplicialCompletedPair.doubleComplex_X` makes the exterior degree `a` of `K` the
column `K^{a,•}`, so this is
`Crystalline.isZero_homology_alternatingCofaceMapComplex_column`. -/
theorem isZero_homology_alternatingCofaceMapComplex_doubleComplex_X
    (V : CosimplicialCompletedPair.{u, max u w, max u w} (envelopeDPAlgebra s f) s.p) :
    ∀ a : ℕ, 0 < a → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max u w}).obj
        (V.doubleComplex.X a)).homology j) :=
  fun a ha j =>
    isZero_homology_alternatingCofaceMapComplex_column s f hf
      V.toCosimplicialCompletedModule a ha j

end Column

end Crystalline

end
