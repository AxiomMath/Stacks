module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import StacksFrontier.FieldTheory.SeparableTensorSplitting
public import StacksCore.FieldTheory.Galois.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the spectrum of a separable field extension

For a tower `k''/k'/k` of finite separable field extensions, pullback along
`Spec(k'') → Spec(k')` is injective on cohomology.

The proof is the source's. Replace `k''` by a normal closure `K` of `k''/k`, which is Galois
over `k`. The algebra `k' ⊗_k K` splits as the product of copies of `K` indexed by the
`k`-embeddings `σ : k' → K`, so that `Spec(k') × Spec(K)` is the disjoint union of copies of
`Spec(K)` whose `σ`-th coprojection has components `(Spec(σ), id)`. Künneth, axiom `(A5)`,
together with the splitting of the cohomology of a finite disjoint union, axiom `(A1)`,
therefore identifies `H^*(Spec(k')) ⊗_F H^*(Spec(K))` with `∏_σ H^*(Spec(K))` by
`a ⊗ b ↦ Spec(σ)^*a ∪ b`. Evaluating at `b = 1` makes every `Spec(σ)^*` injective, and each `σ`
extends to an automorphism of `K` over `k`, so injectivity of `Spec(σ)^*` for the embedding
`k' ⊆ k'' ⊆ K` gives it for all `σ`; that embedding factors through `Spec(k'')`, whence the
claim.

## Main definitions

* `Stacks.WeilCohomology.IsFiniteEtale`: the finite étale `k`-algebras, as an object property
  of the category of commutative `k`-algebras. These are exactly the finite products of finite
  separable field extensions of `k`, that is exactly the algebras whose spectrum is a
  zero-dimensional smooth projective scheme over `k`, so that `Spec` identifies the opposite of
  `Stacks.WeilCohomology.FinEtaleAlg k` with the full subcategory of smooth projective
  `k`-schemes of dimension zero.
* `Stacks.WeilCohomology.tensorObj`, `Stacks.WeilCohomology.piObj`: `Spec(A ⊗_k B)`, the product
  of `Spec(A)` and `Spec(B)` over `k`, and `Spec(∏_i A_i)`, the disjoint union of the
  `Spec(A_i)`.
* `Stacks.WeilCohomology.finEtaleKunnethMap`: the Künneth map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` of
  axiom `(A5)`, for the spectra of finite étale `k`-algebras.
* `Stacks.WeilCohomology.componentRestriction`: restriction to the components of a finite
  disjoint union, the map axiom `(A1)` asserts to be bijective.

## Main results

* `Stacks.WeilCohomology.injective_pullback_of_separable`: pullback on the cohomology of the
  spectra of a tower of finite separable field extensions is injective.
* `Stacks.WeilCohomology.nontrivial_of_traceMap`: the trace map of axiom `(A6)` exhibits the
  cohomology of the spectrum of a finite separable field extension as nonzero.

## Implementation notes

Section 45.14 has no bundled structure in this repository, and the lemmas of that section are
stated here, as elsewhere in this directory, by carrying the part of the data `(D0)`, `(D1)`,
`(D2')` and of the axioms `(A1)` -- `(A7)` that the argument consumes. What this argument
consumes is the following.

* `(D1)`, the contravariant functor `H^*`, is the functor `H` on `FinEtaleAlg k`: contravariant
  in the scheme is covariant in the algebra, so a `k`-algebra map `f : A → B` gives
  `H(Spec(f)) : H^*(Spec(A)) → H^*(Spec(B))`, a map of `F`-algebras. Functoriality is
  functoriality of `H`, so the two relations the argument needs — that `Spec` of the inclusion
  `k' ⊆ K` is `Spec(K) → Spec(k'') → Spec(k')` and that `Spec` of a `k`-embedding followed by an
  automorphism of `K` is the composite of their pullbacks — are instances of
  `CategoryTheory.Functor.map_comp` and are not hypotheses. The domain is restricted to the
  spectra of finite étale algebras, which is where `(D1)` supplies the functor, and no
  cohomological grading appears because the schemes are zero dimensional, so `H^0` and the total
  cohomology `H^*` agree.
* `(A5)`, Künneth, is `kunneth`: the map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` into the cohomology of
  `Spec(A) × Spec(B) = Spec(A ⊗_k B)` is bijective.
* `(A1)`, additivity, is `disjointUnion`: restriction to the components of the finite disjoint
  union `Spec(∏_i A_i) = ∐_i Spec(A_i)` is bijective.
* `(A6)` enters through `traceMap`, the trace map `∫_{Spec(L)} = λ : H^0(Spec(L)) → F` that the
  axiom attaches to the nonempty zero-dimensional scheme `Spec(L)`, and `(D2')` through
  `cycleClass`, the cycle class map `γ` of `Spec(L)` in degree zero; the zero cycles on the one
  point `Spec(L)` are free of rank one on `[Spec(L)]`, so `γ` on them is a homomorphism
  `ℤ → H^0(Spec(L))`. `traceMap_cycleClass` is axiom `(C)(b)` for the structure morphism of
  `Spec(L)`, compatibility of `γ` with proper pushforward, which evaluates the trace on
  `γ(n · [Spec(L)])` as its degree `n · [L : k]` read in `H^0(Spec(k)) = F`. Since the
  coefficient field of `(D0)` has characteristic zero, that degree is nonzero in `F`, and the
  cohomology of `Spec(L)` is therefore nonzero — which is the one fact about `Spec(L)` beyond
  functoriality that the argument needs, and is
  `Stacks.WeilCohomology.nontrivial_of_traceMap`. The axioms `(A2)`, `(A3)`, `(A4)` and `(A7)`
  play no further role here.

  Section 45.14 has no bundled structure in this repository, so `(A6)` is written out as the
  linear functional together with its normalisation, which is how every lemma of the chapter
  that consumes it reads it: `Stacks.Weil.cycleClass_fundamentalClass_eq_one` for Tag 0FHE
  (`trace`, `cycleClass`, `fundamentalClass` and `trace_fundamental`),
  `Stacks.WeilCohomology.integration_one_eq_finrank` for Tag 0FVR (`lam` and `normalization`),
  `IsCohomologicalChernCharacter.perfectDuality_diagonalClass_and_existsUnique_trace` (namespace
  `Stacks.WeilCohomology.FirstChernClassData`) for Tag 0FIK (`lam` and the equation
  `traceContract hA5 X d lam γ([Δ]) = 1`), and
  `Stacks.WeilCohomology.one_ne_zero_of_nonempty` for Tag 0FHF (`pushforward`,
  `cycleClass_pushforward` and the base-point datum `cycleClassPoint`). The two bundles the
  repository does have,
  `Stacks.WeilCohomology.PoincareDualityPushforwardSetup` and
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory`, package condition `(A)` of Section
  45.9 over an algebraically closed base field, which this tag cannot assume: over an
  algebraically closed `k` the only finite separable extension of `k` is `k`.

The normal closure does not appear in the statement: it is constructed inside the proof as
`IntermediateField.normalClosure k k'' (AlgebraicClosure k'')`. The decomposition of
`Spec(k') × Spec(K)` is `Stacks.FieldTheory.tensorPiEquiv'`, proved from the separability of
`k'/k` and the normality of `K/k`, and the product is indexed by the `k`-algebra homomorphisms
`k' → K`, which is the index set for which `η ⊗ ζ ↦ (σ(η) ζ)_σ` is a bijection
`k' ⊗_k K → ∏_σ K`; the source indexes it by a Galois group.

## References

* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Stacks.WeilCohomology

/-- The finite étale `k`-algebras, as an object property of the category of commutative
`k`-algebras: a commutative `k`-algebra is finite étale exactly when it is a finite product of
finite separable field extensions of `k`, that is exactly when its spectrum is a smooth
projective scheme over `k` of dimension zero. -/
def IsFiniteEtale (k : Type u) [Field k] : ObjectProperty (CommAlgCat.{u} k) :=
  fun A => Module.Finite k A ∧ Algebra.FormallyEtale k A

/-- The category of finite étale `k`-algebras; its opposite is the category of zero-dimensional
smooth projective schemes over `k`, via `Spec`. -/
abbrev FinEtaleAlg (k : Type u) [Field k] := (IsFiniteEtale k).FullSubcategory

variable {k : Type u} [Field k]

/-- The spectrum of a finite separable field extension `L/k` is a zero-dimensional smooth
projective scheme over `k`. -/
def ofField (k L : Type u) [Field k] [Field L] [Algebra k L] (hfin : Module.Finite k L)
    (hsep : Algebra.IsSeparable k L) : FinEtaleAlg k :=
  haveI := hfin
  haveI := hsep
  ⟨CommAlgCat.of k L, ⟨inferInstance, Algebra.FormallyEtale.of_isSeparable k L⟩⟩

/-- `Spec` of a map of finite étale `k`-algebras, as a morphism of the category. -/
def algHomMk {X Y : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) : X ⟶ Y :=
  ObjectProperty.homMk (CommAlgCat.ofHom f)

/-- Composition of morphisms built from `k`-algebra maps is the morphism built from the
composite map. -/
@[simp]
lemma algHomMk_comp {X Y Z : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) (g : Y.obj →ₐ[k] Z.obj) :
    algHomMk f ≫ algHomMk g = algHomMk (g.comp f) := rfl

/-- The morphism built from the identity `k`-algebra map is the identity morphism. -/
@[simp]
lemma algHomMk_id (X : FinEtaleAlg k) : algHomMk (AlgHom.id k X.obj) = 𝟙 X := rfl

/-- `Spec(A ⊗_k B)`, the product of `Spec(A)` and `Spec(B)` over `Spec(k)`. -/
def tensorObj (X Y : FinEtaleAlg k) : FinEtaleAlg k :=
  haveI := X.property.1
  haveI := X.property.2
  haveI := Y.property.1
  haveI := Y.property.2
  ⟨CommAlgCat.of k (X.obj ⊗[k] Y.obj),
    ⟨inferInstance, Algebra.FormallyEtale.comp k X.obj (X.obj ⊗[k] Y.obj)⟩⟩

/-- The first projection `Spec(A) × Spec(B) → Spec(A)`. -/
def tensorFst (X Y : FinEtaleAlg k) : X ⟶ tensorObj X Y :=
  algHomMk (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := X.obj) (B := Y.obj))

/-- The second projection `Spec(A) × Spec(B) → Spec(B)`. -/
def tensorSnd (X Y : FinEtaleAlg k) : Y ⟶ tensorObj X Y :=
  algHomMk (Algebra.TensorProduct.includeRight (R := k) (A := X.obj) (B := Y.obj))

/-- `Spec(∏_i A_i)`, the disjoint union of the `Spec(A_i)` over a finite index set. -/
def piObj {ι : Type u} [Fintype ι] (X : ι → FinEtaleAlg k) : FinEtaleAlg k :=
  haveI : ∀ i, Module.Finite k (X i).obj := fun i => (X i).property.1
  haveI : ∀ i, Algebra.FormallyEtale k (X i).obj := fun i => (X i).property.2
  ⟨CommAlgCat.of k (∀ i, (X i).obj), ⟨inferInstance, inferInstance⟩⟩

/-- The `i`-th coprojection `Spec(A_i) → ∐_j Spec(A_j)`. -/
def piCoproj {ι : Type u} [Fintype ι] (X : ι → FinEtaleAlg k) (i : ι) : piObj X ⟶ X i :=
  algHomMk (Pi.evalAlgHom k (fun j => (X j).obj) i)

variable {F : Type v} [Field F]

/-- The Künneth map `H^*(X) ⊗_F H^*(Y) → H^*(X × Y)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, of axiom
`(A5)`. -/
def finEtaleKunnethMap (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F) (X Y : FinEtaleAlg k) :
    H.obj X ⊗[F] H.obj Y →ₗ[F] H.obj (tensorObj X Y) :=
  (LinearMap.mul' F (H.obj (tensorObj X Y))).comp
    (TensorProduct.map (H.map (tensorFst X Y)).hom.toLinearMap
      (H.map (tensorSnd X Y)).hom.toLinearMap)

/-- The Künneth map sends `a ⊗ b` to `pr₁^*a ∪ pr₂^*b`. -/
@[simp]
lemma kunnethMap_tmul (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F) (X Y : FinEtaleAlg k)
    (a : H.obj X) (b : H.obj Y) :
    finEtaleKunnethMap H X Y (a ⊗ₜ[F] b) =
      (H.map (tensorFst X Y)).hom a * (H.map (tensorSnd X Y)).hom b := by
  simp [finEtaleKunnethMap]

/-- Restriction of a cohomology class on a finite disjoint union to its components; axiom `(A1)`
asserts that this map is bijective. -/
def componentRestriction (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F) {ι : Type u} [Fintype ι]
    (X : ι → FinEtaleAlg k) : H.obj (piObj X) →ₗ[F] ∀ i, H.obj (X i) :=
  LinearMap.pi fun i => (H.map (piCoproj X i)).hom.toLinearMap

/-- The `i`-th component of the restriction of a class `a` is its pullback along the `i`-th
coprojection. -/
@[simp]
lemma componentRestriction_apply (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F) {ι : Type u} [Fintype ι]
    (X : ι → FinEtaleAlg k) (a : H.obj (piObj X)) (i : ι) :
    componentRestriction H X a i = (H.map (piCoproj X i)).hom a := rfl

/-- Functoriality of the cohomology functor, read on the morphisms coming from `k`-algebra
maps: `Spec(g ∘ f)^* = Spec(f)^* ∘ Spec(g)^*`. -/
private lemma map_algHomMk_comp (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    {X Y Z : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) (g : Y.obj →ₐ[k] Z.obj) (a : H.obj X) :
    (H.map (algHomMk g)).hom ((H.map (algHomMk f)).hom a) =
      (H.map (algHomMk (g.comp f))).hom a := by
  rw [← algHomMk_comp, H.map_comp]
  rfl

/-- Functoriality of the cohomology functor at a composite that has been identified with a
third map. -/
private lemma map_algHomMk_comp' (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    {X Y Z : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) (g : Y.obj →ₐ[k] Z.obj)
    (h : X.obj →ₐ[k] Z.obj) (hh : ∀ x, g (f x) = h x) (a : H.obj X) :
    (H.map (algHomMk g)).hom ((H.map (algHomMk f)).hom a) = (H.map (algHomMk h)).hom a := by
  rw [map_algHomMk_comp, show g.comp f = h from AlgHom.ext hh]

/-- Functoriality of the cohomology functor at a composite that is the identity. -/
private lemma map_algHomMk_comp_id (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    {X Y : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) (g : Y.obj →ₐ[k] X.obj)
    (hh : ∀ x, g (f x) = x) (a : H.obj X) :
    (H.map (algHomMk g)).hom ((H.map (algHomMk f)).hom a) = a := by
  rw [map_algHomMk_comp' H f g (AlgHom.id k X.obj) hh, algHomMk_id, H.map_id]
  rfl

/-- Pullback along a composite of `k`-algebra maps kills a class killed by the first map. -/
private lemma map_algHomMk_eq_zero_of_comp (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    {X Y Z : FinEtaleAlg k} (f : X.obj →ₐ[k] Y.obj) (g : Y.obj →ₐ[k] Z.obj)
    (h : X.obj →ₐ[k] Z.obj) (hh : ∀ x, g (f x) = h x) {a : H.obj X}
    (ha : (H.map (algHomMk f)).hom a = 0) : (H.map (algHomMk h)).hom a = 0 := by
  rw [← map_algHomMk_comp' H f g h hh, ha, map_zero]

/-- Over a field `F`, tensoring an `F`-module with the unit of a nonzero `F`-algebra is
injective. -/
private theorem injective_tmul_one (F : Type v) [Field F] (A : Type w) [AddCommGroup A]
    [Module F A] (C : Type w) [Ring C] [Algebra F C] [Nontrivial C] :
    Function.Injective fun a : A => a ⊗ₜ[F] (1 : C) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : C) ≠ 0)
  intro a b hab
  have h := congrArg
    (fun t => TensorProduct.rid F A (TensorProduct.map (LinearMap.id (R := F) (M := A)) φ t)) hab
  simpa [hφ] using h

/-- **The trace map of axiom `(A6)` exhibits the cohomology of `Spec(L)` as nonzero.** Let `L/k`
be a finite separable field extension, so that `Spec(L)` is a nonempty smooth projective scheme
over `k`, equidimensional of dimension zero. Axiom `(A6)` then provides the trace map
`∫_{Spec(L)} = λ : H^0(Spec(L)) → F`, which is `traceMap`, and `(D2')` provides the cycle class
map `γ` of `Spec(L)` in degree zero, which is `cycleClass`: the group of zero cycles on the one
point `Spec(L)` is free of rank one on the fundamental class `[Spec(L)]`, so `γ` on it is a
homomorphism `ℤ → H^0(Spec(L))` and `γ([Spec(L)])` is its value at `1`. Axiom `(C)(b)` for the
structure morphism `Spec(L) → Spec(k)` — compatibility of `γ` with proper pushforward — then
evaluates the trace on `γ(n · [Spec(L)])` as the degree `n · [L : k]` of that zero cycle over
`Spec(k)`, read in `H^0(Spec(k)) = F`; this is the hypothesis `traceMap_cycleClass`.

Because the coefficient field `F` of `(D0)` has characteristic zero and `[L : k]` is positive,
the value `[L : k]` that the trace takes on `γ([Spec(L)])` is nonzero in `F`. Hence
`γ([Spec(L)])` is itself a nonzero element of `H^0(Spec(L))`, so the cohomology of `Spec(L)` is
nonzero.

This is the discharge of the nonvanishing used in the proof of Tag 0FVS below; the same
deduction from the normalisation of the trace map is made for the base point `Spec(k)`, where
the degree is `1`, in `StacksFrontier.AlgebraicGeometry.F6Rank201.WeilCohomologyBasePoint`. The
value is read on `γ([Spec(L)])` rather than on the unit class because the two statements that
would identify them are themselves results of the chapter: that `γ([Spec(L)])` is the unit is
the first clause of Tag 0FHF, and `∫_{Spec(L)} 1 = [L : k]` is Tag 0FVR. -/
theorem nontrivial_of_traceMap [CharZero F] (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    (L : Type u) [Field L] [Algebra k L] (hfin : Module.Finite k L)
    (hsep : Algebra.IsSeparable k L)
    (cycleClass : ℤ →+ H.obj (ofField k L hfin hsep))
    (traceMap : H.obj (ofField k L hfin hsep) →ₗ[F] F)
    (traceMap_cycleClass : ∀ n : ℤ,
      traceMap (cycleClass n) = (n : F) * (Module.finrank k L : F)) :
    Nontrivial (H.obj (ofField k L hfin hsep)) := by
  have := hfin
  refine ⟨cycleClass 1, 0, fun h => ?_⟩
  have h1 := traceMap_cycleClass 1
  rw [h, map_zero] at h1
  simp only [Int.cast_one, one_mul] at h1
  exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne' h1.symm

/-- Let `k''/k'/k` be finite separable field extensions and `K/k` a finite Galois extension
containing `k''`, with nonzero cohomology. Then pullback `H^*(Spec(k')) → H^*(Spec(k''))` is
injective. -/
private theorem injective_pullback_of_separable_aux
    (k k' k'' K : Type u) [Field k] [Field k'] [Field k''] [Field K]
    [Algebra k k'] [Algebra k k''] [Algebra k' k''] [IsScalarTower k k' k'']
    [Algebra k K] [Algebra k'' K] [IsScalarTower k k'' K]
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    [Algebra.IsSeparable k K] [Normal k K]
    (hfin'' : Module.Finite k k'') (hsep'' : Algebra.IsSeparable k k'')
    (hfinK : Module.Finite k K)
    (F : Type v) [Field F] (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    (kunneth : ∀ X Y : FinEtaleAlg k, Function.Bijective (finEtaleKunnethMap H X Y))
    (disjointUnion : ∀ (ι : Type u) [Fintype ι] (X : ι → FinEtaleAlg k),
      Function.Bijective (componentRestriction H X))
    (nontrivialK : Nontrivial (H.obj (ofField k K hfinK inferInstance))) :
    Function.Injective (H.map (algHomMk (X := ofField k k' inferInstance inferInstance)
      (Y := ofField k k'' hfin'' hsep'') (IsScalarTower.toAlgHom k k' k''))) := by
  classical
  have := hfin''
  have := hsep''
  have := hfinK
  have := nontrivialK
  have : Fintype (k' →ₐ[k] K) := minpoly.AlgHom.fintype k k' K
  let : Algebra k' K := ((algebraMap k'' K).comp (algebraMap k' k'')).toAlgebra
  have : IsScalarTower k k' K := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap k K x = algebraMap k'' K (algebraMap k' k'' (algebraMap k k' x))
    rw [← IsScalarTower.algebraMap_apply k k' k'', ← IsScalarTower.algebraMap_apply k k'' K]
  set X' : FinEtaleAlg k := ofField k k' inferInstance inferInstance
  set X'' : FinEtaleAlg k := ofField k k'' hfin'' hsep''
  set XK : FinEtaleAlg k := ofField k K hfinK inferInstance
  set P : FinEtaleAlg k := piObj (fun _ : (k' →ₐ[k] K) => XK)
  set emb : k' →ₐ[k] K := IsScalarTower.toAlgHom k k' K
  set e : k' ⊗[k] K ≃ₐ[k] ((k' →ₐ[k] K) → K) :=
    Stacks.FieldTheory.tensorPiEquiv' k k' K emb with he
  have hsplit : Function.Injective
      (fun z : H.obj (tensorObj X' XK) =>
        (H.map (algHomMk (X := tensorObj X' XK) (Y := P) e.toAlgHom)).hom z) := by
    have hinv : ∀ z : H.obj (tensorObj X' XK),
        (H.map (algHomMk (X := P) (Y := tensorObj X' XK) e.symm.toAlgHom)).hom
            ((H.map (algHomMk (X := tensorObj X' XK) (Y := P) e.toAlgHom)).hom z) = z :=
      map_algHomMk_comp_id H (X := tensorObj X' XK) (Y := P) e.toAlgHom e.symm.toAlgHom
        fun x => e.symm_apply_apply x
    exact Function.LeftInverse.injective hinv
  have hinj : Function.Injective (fun t : H.obj X' ⊗[F] H.obj XK =>
      componentRestriction H (fun _ : (k' →ₐ[k] K) => XK)
        ((H.map (algHomMk (X := tensorObj X' XK) (Y := P) e.toAlgHom)).hom
          (finEtaleKunnethMap H X' XK t))) :=
    (((disjointUnion (k' →ₐ[k] K) fun _ => XK).1.comp hsplit).comp (kunneth X' XK).1)
  have hval : ∀ (a : H.obj X') (c : H.obj XK) (σ : k' →ₐ[k] K),
      componentRestriction H (fun _ : (k' →ₐ[k] K) => XK)
          ((H.map (algHomMk (X := tensorObj X' XK) (Y := P) e.toAlgHom)).hom
            (finEtaleKunnethMap H X' XK (a ⊗ₜ[F] c))) σ =
        (H.map (algHomMk (X := X') (Y := XK) σ)).hom a * c := by
    intro a c σ
    set ψ : (tensorObj X' XK).obj →ₐ[k] XK.obj :=
      (Pi.evalAlgHom k (fun _ : (k' →ₐ[k] K) => K) σ).comp e.toAlgHom
    have hψ : ∀ x : k' ⊗[k] K,
        (Pi.evalAlgHom k (fun _ : (k' →ₐ[k] K) => K) σ) (e.toAlgHom x) = ψ x := fun _ => rfl
    have hfst : ∀ x : k',
        ψ (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k') (B := K) x) = σ x := by
      intro x
      change e (x ⊗ₜ[k] (1 : K)) σ = σ x
      rw [he, Stacks.FieldTheory.tensorPiEquiv'_tmul, mul_one]
    have hsnd : ∀ x : K,
        ψ (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := K) x) = x := by
      intro x
      change e ((1 : k') ⊗ₜ[k] x) σ = x
      rw [he, Stacks.FieldTheory.tensorPiEquiv'_tmul, map_one, one_mul]
    rw [componentRestriction_apply, kunnethMap_tmul]
    change (H.map (algHomMk (X := P) (Y := XK) (Pi.evalAlgHom k (fun _ => K) σ))).hom
        ((H.map (algHomMk (X := tensorObj X' XK) (Y := P) e.toAlgHom)).hom
          ((H.map (algHomMk (X := X') (Y := tensorObj X' XK)
              (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k') (B := K)))).hom a *
            (H.map (algHomMk (X := XK) (Y := tensorObj X' XK)
              (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := K)))).hom c)) =
      (H.map (algHomMk (X := X') (Y := XK) σ)).hom a * c
    rw [map_algHomMk_comp' H (X := tensorObj X' XK) (Y := P) (Z := XK) e.toAlgHom
        (Pi.evalAlgHom k (fun _ => K) σ) ψ hψ, map_mul,
      map_algHomMk_comp' H (X := X') (Y := tensorObj X' XK) (Z := XK)
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k') (B := K)) ψ σ hfst,
      map_algHomMk_comp_id H (X := XK) (Y := tensorObj X' XK)
        (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := K)) ψ hsnd]
  intro a b hab
  have hd : (H.map (algHomMk (X := X') (Y := XK) emb)).hom (a - b) = 0 :=
    map_algHomMk_eq_zero_of_comp H (X := X') (Y := X'') (Z := XK)
      (IsScalarTower.toAlgHom k k' k'') (IsScalarTower.toAlgHom k k'' K) emb (fun x => rfl)
      (by rw [map_sub, hab, sub_self])
  have hkey : ∀ σ : k' →ₐ[k] K,
      (H.map (algHomMk (X := X') (Y := XK) σ)).hom (a - b) = 0 := by
    intro σ
    obtain ⟨τ, hτ⟩ : ∃ τ : K ≃ₐ[k] K, (τ : K →ₐ[k] K).comp emb = σ :=
      ⟨AlgEquiv.ofBijective (σ.liftNormal K) (AlgHom.normal_bijective k K K _),
        AlgHom.ext fun x => σ.liftNormal_commutes K x⟩
    exact map_algHomMk_eq_zero_of_comp H (X := X') (Y := XK) (Z := XK) emb (τ : K →ₐ[k] K) σ
      (fun x => congrFun (congrArg (fun φ : k' →ₐ[k] K => (φ : k' → K)) hτ) x) hd
  have hzero : (a - b) ⊗ₜ[F] (1 : H.obj XK) = (0 : H.obj X') ⊗ₜ[F] (1 : H.obj XK) := by
    refine hinj ?_
    simp only [TensorProduct.zero_tmul, map_zero]
    funext σ
    rw [hval, hkey σ, zero_mul]
    rfl
  exact sub_eq_zero.mp (injective_tmul_one F (H.obj X') (H.obj XK) hzero)

/-- Let `k''/k'/k` be finite separable field extensions. Then pullback
`H^0(Spec(k')) → H^0(Spec(k''))` is injective.

Here `H` is the cohomology functor of `(D1)`, read on the spectra of finite étale `k`-algebras;
since these schemes are zero dimensional, `H^0` is the total cohomology `H^*`. The hypothesis
`kunneth` is axiom `(A5)` and `disjointUnion` is axiom `(A1)`; `traceMap` is the trace map
`∫_{Spec(L)}` of axiom `(A6)` for the zero-dimensional scheme `Spec(L)`, `cycleClass` is the
cycle class map `γ` of `(D2')` on the zero cycles of `Spec(L)`, free of rank one on `[Spec(L)]`,
and `traceMap_cycleClass` is axiom `(C)(b)` for the structure morphism of `Spec(L)`, which
evaluates that trace on `γ(n · [Spec(L)])` as its degree `n · [L : k]`. -/
@[stacks 0FVS "injectivity on cohomology for a tower of finite separable field extensions; \
  the Künneth decomposition of Spec(k') x Spec(K) as a product over the embeddings, the \
  functoriality relations, and the nonvanishing of the cohomology of Spec(K) are derived from \
  the functor of (D1) together with axioms (A1), (A5), (A6) and (C)(b), which are explicit \
  arguments here, as elsewhere in Section 45.14"]
theorem injective_pullback_of_separable
    (k k' k'' : Type u) [Field k] [Field k'] [Field k'']
    [Algebra k k'] [Algebra k k''] [Algebra k' k''] [IsScalarTower k k' k'']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    [FiniteDimensional k' k''] [Algebra.IsSeparable k' k'']
    (F : Type v) [Field F] [CharZero F] (H : FinEtaleAlg k ⥤ CommAlgCat.{w} F)
    (kunneth : ∀ X Y : FinEtaleAlg k, Function.Bijective (finEtaleKunnethMap H X Y))
    (disjointUnion : ∀ (ι : Type u) [Fintype ι] (X : ι → FinEtaleAlg k),
      Function.Bijective (componentRestriction H X))
    (cycleClass : ∀ (L : Type u) [Field L] [Algebra k L] (hfin : Module.Finite k L)
      (hsep : Algebra.IsSeparable k L), ℤ →+ H.obj (ofField k L hfin hsep))
    (traceMap : ∀ (L : Type u) [Field L] [Algebra k L] (hfin : Module.Finite k L)
      (hsep : Algebra.IsSeparable k L), H.obj (ofField k L hfin hsep) →ₗ[F] F)
    (traceMap_cycleClass : ∀ (L : Type u) [Field L] [Algebra k L]
      (hfin : Module.Finite k L) (hsep : Algebra.IsSeparable k L) (n : ℤ),
      traceMap L hfin hsep (cycleClass L hfin hsep n) =
        (n : F) * (Module.finrank k L : F)) :
    Function.Injective (H.map (algHomMk (X := ofField k k' inferInstance inferInstance)
      (Y := ofField k k'' (Module.Finite.trans k' k'') (Algebra.IsSeparable.trans k k' k''))
      (IsScalarTower.toAlgHom k k' k''))) := by
  have : Module.Finite k k'' := Module.Finite.trans k' k''
  have : Algebra.IsSeparable k k'' := Algebra.IsSeparable.trans k k' k''
  have hfinK : Module.Finite k (NormalClosure k k'') :=
    normalClosure.is_finiteDimensional k ↥(algebraicClosure k k'')
      (AlgebraicClosure ↥(algebraicClosure k k''))
  exact injective_pullback_of_separable_aux k k' k'' (NormalClosure k k'')
    inferInstance inferInstance hfinK F H kunneth disjointUnion
    (nontrivial_of_traceMap H (NormalClosure k k'') hfinK inferInstance
      (cycleClass (NormalClosure k k'') hfinK inferInstance)
      (traceMap (NormalClosure k k'') hfinK inferInstance)
      (traceMap_cycleClass (NormalClosure k k'') hfinK inferInstance))

end Stacks.WeilCohomology

end

end
