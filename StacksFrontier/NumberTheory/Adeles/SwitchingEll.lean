module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
public import StacksFrontier.NumberTheory.Adeles.HeckeEigenform

/-!
# Switching `ℓ`

Let `K` be a field, `Γ` a topological group, and `Frob : Place K → Γ` a family of elements of
`Γ` indexed by the places of `K` — in the situation of the Stacks source, `K` is the function
field of a smooth projective geometrically irreducible curve `X` over a finite field, `Γ` is
`π₁(X)`, and `Frob v` is the geometric Frobenius at the closed point of `X` corresponding to
`v`. Let `E` be a number field and `λ`, `λ'` two finite places of `E`. Given an absolutely
irreducible continuous `ρ : Γ → SL₂(E_λ)`, the switching lemma produces a finite extension
`E'_{λ'}` of `E_{λ'}` and an absolutely irreducible continuous `ρ' : Γ → SL₂(E'_{λ'})` with the
same characteristic polynomials of all Frobenii.

The Stacks source proves this by citation: Theorem 03VU produces an eigenform `f ∈ C(Q̄_ℓ)`
attached to `ρ`, Proposition 03VW lets one choose `f ∈ C(E')` with `E ⊂ E'` finite, completion
puts `f ∈ C(E'_{λ'})`, and Theorem 03VT turns `f` back into `ρ'`. The three cited inputs are
carried here as hypotheses; the four-step chain between them is proved.

## Main definitions

* `Stacks.Adeles.IsAbsolutelyIrreducible` — Burnside's criterion for absolute irreducibility of
  a two-dimensional representation.
* `Stacks.Adeles.FieldExtension` and `Stacks.Adeles.TopologicalFieldExtension` — a finite field
  extension, and a finite extension of a topological field carrying its module topology,
  bundled so that they can be produced by an existential statement.
* `Stacks.Adeles.DrinfeldMakeRho`, `Stacks.Adeles.DrinfeldMakeF` — Theorem 03VT and Theorem 03VU,
  each carried as a hypothesis.
* `Stacks.Adeles.CuspFormsFinite` — a hypothesis form of Proposition 03VW for `φ_v = q_v`, over
  an arbitrary field (the proposition itself is proved as
  `Stacks.Adeles.GlobalFunctionField.cuspFormsWithChar_fg_and_baseChange`).
* `Stacks.Adeles.CuspFormsFiniteDescent` — the one consequence the source draws from
  Proposition 03VW in the proof of Lemma 03VY, carried as a hypothesis taking Proposition 03VW
  as its input.

## Main results

* `Stacks.Adeles.det_eq_one_of_det_frobenius_eq_one` — a continuous representation whose
  Frobenius elements have determinant one has determinant one throughout, as soon as the
  Frobenius elements topologically generate.
* `Stacks.Adeles.exists_compatible_representation` — Lemma 03VY, switching `ℓ`.

## Implementation notes

**The Galois side is abstracted.** The source's `π₁(X)` is replaced by an arbitrary topological
group `Γ` and the source's Frobenius `F_v` by an arbitrary family `Frob : Place K → Γ`. Nothing
in the source's proof of Lemma 03VY uses any property of `π₁(X)` beyond being a topological
group carrying such a family, and the statement obtained is the source's statement universally
quantified over `(Γ, Frob)`: instantiating `Γ := π₁(X)` and `Frob v :=` the geometric Frobenius
at the closed point corresponding to `v` returns it. The abstraction is therefore a
generalization, and it is what keeps the three carried hypotheses free of the curve.

**The curve is absent.** For the same reason the source's `X`, its base field `k` and the
characteristic `p` do not appear. The source's hypothesis that `λ` and `λ'` do not lie above `p`
enters only through the carried hypotheses: it is what makes Theorem 03VT and Theorem 03VU
applicable at the completions of `E` at `λ` and at `λ'`, and it is the content of `hq` below,
the invertibility of the residue cardinalities `q_v` in the ring of integers of `E_{λ'}` (the
`q_v` are powers of `p`). It is therefore not repeated as a hypothesis; dropping it makes the
statement formally stronger.

**Why the three inputs are hypotheses.** Theorem 03VT, Theorem 03VU and Proposition 03VW are
proved in the Stacks source by citation alone: the proof bodies are `See \cite{D0}.`,
`See \cite{D1}.` and `See \cite[Proposition 4.7]{dJ-conjecture}.`, and the chapter's
introduction says that rigorous proofs will be added over time. They are therefore carried as
hypotheses of the form used by `Stacks.Chow.FlatPullbackDescends`. `DrinfeldMakeRho` and
`DrinfeldMakeF` carry the `stacks` attribute of the result they state: each is the formal
statement of its tag, which the results below take as a hypothesis, and not a proof of it.
`CuspFormsFinite` carries none: Proposition 03VW is proved, over a function field of a finite
field, as `Stacks.Adeles.GlobalFunctionField.cuspFormsWithChar_fg_and_baseChange`, and
`CuspFormsFinite` is the stronger form of its instance `φ_v = q_v` that this file, which works
over an arbitrary field, takes as a hypothesis. The one tag of this file whose proof the source
does give is 03VY.

**`DrinfeldMakeRho` and `DrinfeldMakeF` are stated over a parameter base field `F₀`.** The
source writes `Q_ℓ` and `Q̄_ℓ`; here the base local field is the parameter `F₀` and its
algebraic closure the parameter `Ω`. The tags are the instances `F₀ = Q_ℓ`, `Ω = Q̄_ℓ`. Below
they are used at `F₀ = E_λ` and `F₀ = E_{λ'}`, which are themselves instances of the tags: a
finite extension of `E_λ` is a finite extension of `Q_ℓ` and an algebraic closure of `E_λ` is an
algebraic closure of `Q_ℓ`, for `λ` of residue characteristic `ℓ`. Mathlib does not supply that
identification — the completion of a number field at a finite place is not known to it as a
finite extension of `Q_p` — which is why the base field is carried as a parameter instead of
being fixed to `Padic ℓ`.

**Integrality.** The source's hypothesis `u_v ∈ Z̄_ℓ^*` on the central eigenvalues of
Theorem 03VT is rendered as: `u_v` and `u_v⁻¹` are both integral over the ring of integers
`O₀ ⊆ F₀`, which is the parameter standing for `Z_ℓ`.

**Finite extensions are taken in the universe of the base field.** A finite extension of a
field `F : Type w` has a model in `Type w`, so this loses nothing; it keeps the bundled
extensions and the fields they extend in one universe, which is what lets the bundles be
applied at the completions themselves.

**Hausdorffness.** `TopologicalFieldExtension` records that the extension is Hausdorff. This is
a property of the object the source names — a finite extension of a complete discretely valued
field, with its unique topology as a topological vector space, is Hausdorff — and it is what
makes the subgroup `{g | det ρ(g) = 1}` closed, hence the step of the source's proof that lands
`ρ'` in `SL₂` rather than `GL₂`.

**Landing in `SL₂`.** The source says that Theorem 03VT yields `ρ' : π₁(X) → SL₂(E'_{λ'})`,
while Theorem 03VT as stated produces a representation into `GL₂` whose determinant at the
Frobenii is pinned by `u_v = q_v⁻¹ det ρ'(F_v)`. Since the eigenform has `u_v = q_v⁻¹`, the
determinant is `1` at every Frobenius element, and it is `1` throughout because the Frobenius
elements topologically generate — which is Stacks 03W5, formalized as
`AlgebraicGeometry.exists_finite_closedPoints_frobeniusElements_topologicalClosure_eq_top`, and is
carried here as the hypothesis `hFrob` because `Γ` is abstract.

**Characteristic polynomials.** For a matrix of determinant `1` the characteristic polynomial is
`X² - tr · X + 1`, so "the characteristic polynomials of all Frobenii are the same" is recorded
as the existence of one polynomial over the number field `E'` whose images are the two
characteristic polynomials. The image of the second is compared inside the algebraic closure
`Ω'` of `E_{λ'}`, along the embedding of the coefficient field of `ρ'` produced by
Theorem 03VT; since that embedding is injective it pins the characteristic polynomial of
`ρ'(F_v)` exactly.

## References

* [Stacks Project, Tag 03VY](https://stacks.math.columbia.edu/tag/03VY)
* [Stacks Project, Tag 03VT](https://stacks.math.columbia.edu/tag/03VT)
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
* [Stacks Project, Tag 03VW](https://stacks.math.columbia.edu/tag/03VW)
* [Stacks Project, Tag 03W5](https://stacks.math.columbia.edu/tag/03W5)
-/

@[expose] public noncomputable section

open Matrix

universe u v w s

namespace Stacks.Adeles

/-- A finite field extension of `F`, bundled so that it can be produced by an existential
statement. The larger field is taken in the universe of `F`. -/
public structure FieldExtension (F : Type w) [Field F] where
  /-- The larger field. -/
  carrier : Type w
  /-- The field structure of the extension. -/
  [field : Field carrier]
  /-- The extension is an `F`-algebra. -/
  [algebra : Algebra F carrier]
  /-- The extension is finite. -/
  [finiteDimensional : FiniteDimensional F carrier]

attribute [instance] FieldExtension.field FieldExtension.algebra
  FieldExtension.finiteDimensional

/-- A finite extension of a topological field, carrying its module topology and Hausdorff. For a
finite extension of a complete discretely valued field the module topology is its unique
topology as a topological vector space over the base, and it is Hausdorff. -/
public structure TopologicalFieldExtension (F : Type w) [Field F] [TopologicalSpace F] extends
    FieldExtension F where
  /-- The topology of the extension. -/
  [topology : TopologicalSpace carrier]
  /-- The topology is the module topology over the base field. -/
  [isModuleTopology : IsModuleTopology F carrier]
  /-- The topology is Hausdorff. -/
  [t2Space : T2Space carrier]

attribute [instance] TopologicalFieldExtension.topology
  TopologicalFieldExtension.isModuleTopology TopologicalFieldExtension.t2Space

/-- Burnside's criterion for absolute irreducibility of a two-dimensional representation: the
image spans the whole matrix algebra over the coefficient field. -/
public def IsAbsolutelyIrreducible {Γ : Type v} [Group Γ] {M : Type w} [Field M]
    (ρ : Γ →* GL (Fin 2) M) : Prop :=
  Submodule.span M (Set.range fun g => (ρ g : Matrix (Fin 2) (Fin 2) M)) = ⊤

/-! ### The three inputs the Stacks source proves by citation -/

/-- **Stacks 03VT, carried as a hypothesis.** Given an eigenform `f` with values in an
algebraic closure `Ω` of a local field `F₀` whose central eigenvalues `u_v` are units of the
integral closure of the ring of integers `O₀ ⊆ F₀`, there is a continuous absolutely irreducible
`ρ : Γ → GL₂(E)` with `E` a finite extension of `F₀` embedded in `Ω`, such that
`t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)` at every place.

The source's integrality hypothesis is `u_v ∈ Z̄_ℓ^*`, which excludes `u_v = 0`; the rendering
`IsIntegral O₀ (u v) ∧ IsIntegral O₀ (u v)⁻¹` allows it, since `0⁻¹ = 0` and `0` is integral.
The hypothesis is therefore formally weaker and the statement correspondingly stronger. This is
vacuous where the theorem is applied: an eigenform takes a unit value and `U_v` is translation
by an invertible adelic matrix, so `u_v = 0` would force `f = 0`.

The Stacks source proves this by citing Drinfeld, so it cannot be discharged here: this
declaration is the formal statement of the theorem, which the results below take as a
hypothesis. See the implementation notes of
`StacksFrontier.NumberTheory.Adeles.SwitchingEll`. -/
public def DrinfeldMakeRho (K : Type u) [Field K] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]
    (Frob : Place K → Γ) (F₀ : Type w) [Field F₀] [TopologicalSpace F₀] (O₀ : Subring F₀)
    (Ω : Type s) [Field Ω] [Algebra F₀ Ω] [IsAlgClosure F₀ Ω] : Prop :=
  ∀ (f : GL (Fin 2) (AdeleRing K) → Ω) (t u : Place K → Ω), IsEigenform f t u →
    (∀ v, IsIntegral O₀ (u v) ∧ IsIntegral O₀ (u v)⁻¹) →
      ∃ (E : TopologicalFieldExtension F₀) (j : E.carrier →+* Ω)
        (ρ : Γ →* GL (Fin 2) E.carrier),
        j.comp (algebraMap F₀ E.carrier) = algebraMap F₀ Ω ∧
          Continuous (fun g => (ρ g : Matrix (Fin 2) (Fin 2) E.carrier)) ∧
            IsAbsolutelyIrreducible ρ ∧
              ∀ v, t v = j (Matrix.trace (ρ (Frob v) : Matrix (Fin 2) (Fin 2) E.carrier)) ∧
                u v = (Place.residueCard v : Ω)⁻¹ *
                  j (Matrix.det (ρ (Frob v) : Matrix (Fin 2) (Fin 2) E.carrier))

/-- **Stacks 03VU, carried as a hypothesis.** Given a continuous absolutely irreducible
`ρ : Γ → GL₂(M)` with `M` a finite extension of a local field `F₀` embedded in an algebraic
closure `Ω` of `F₀`, there is an eigenform `f` with values in `Ω` whose eigenvalues satisfy
`t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)`.

The Stacks source proves this by citing Drinfeld, so it cannot be discharged here: this
declaration is the formal statement of the theorem, which the results below take as a
hypothesis. See the implementation notes of
`StacksFrontier.NumberTheory.Adeles.SwitchingEll`. -/
public def DrinfeldMakeF (K : Type u) [Field K] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]
    (Frob : Place K → Γ) (F₀ : Type w) [Field F₀] [TopologicalSpace F₀]
    (Ω : Type s) [Field Ω] [Algebra F₀ Ω] [IsAlgClosure F₀ Ω] : Prop :=
  ∀ (M : Type w) [Field M] [Algebra F₀ M] [FiniteDimensional F₀ M] [TopologicalSpace M]
    [IsModuleTopology F₀ M] [T2Space M] (j : M →+* Ω),
    j.comp (algebraMap F₀ M) = algebraMap F₀ Ω →
      ∀ ρ : Γ →* GL (Fin 2) M, Continuous (fun g => (ρ g : Matrix (Fin 2) (Fin 2) M)) →
        IsAbsolutelyIrreducible ρ →
          ∃ (f : GL (Fin 2) (AdeleRing K) → Ω) (t u : Place K → Ω), IsEigenform f t u ∧
            ∀ v, t v = j (Matrix.trace (ρ (Frob v) : Matrix (Fin 2) (Fin 2) M)) ∧
              u v = (Place.residueCard v : Ω)⁻¹ *
                j (Matrix.det (ρ (Frob v) : Matrix (Fin 2) (Fin 2) M))

/-- **A hypothesis form of Stacks 03VW, for the central character `φ_v = q_v`.** `C(Λ)` is a
finitely generated `Λ`-module for `Λ` Noetherian, and `C(Λ) = C(F) ⊗_F Λ` compatibly with `T_v`
for `Λ` a field with prime subfield `F`.

This is not the formalization of Proposition 03VW, and it carries no `stacks` attribute. The
proposition is proved, for every central character `φ` and with the source's hypotheses, as
`Stacks.Adeles.GlobalFunctionField.cuspFormsWithChar_fg_and_baseChange`, over a function field
`K` of a finite field; its instance `φ_v = q_v` is
`Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_fg_and_baseChange`. This structure
fixes `φ_v = q_v`, works over an arbitrary field `K`, and states clause (1) for every Noetherian
`Λ` (see below), so it is a different, stronger statement which the results of this file take
as a hypothesis.

The base change is recorded as the existence of a finite family in `C(F)` which is an `F`-basis
of `C(F)` and whose image under `F → Λ` is a `Λ`-basis of `C(Λ)`; that is what
`C(Λ) = C(F) ⊗_F Λ` says. Compatibility with `T_v` is automatic for this rendering, because the
map `C(F) → C(Λ)` is postcomposition with `F → Λ` and `T_v` commutes with postcomposition by a
ring homomorphism (`Stacks.Adeles.heckeOperator_mapCoeffs`). The prime subfield of `Λ` is the
bottom subfield `⊥`.

The subject of both clauses is `Stacks.Adeles.cuspFormsCentralChar`. The source defines `C(Λ)`
by the condition `U_v f = φ_v⁻¹ f` without ever defining `φ_v`; that definition reads `φ_v` as
`q_v`, the reading forced by the normalization `u_v = q_v⁻¹` for representations into `SL₂`,
and clears the inverse. See its docstring in `StacksFrontier.NumberTheory.Adeles.HeckeEigenform`.

Clause (1) is stated here for every Noetherian `Λ`. The source's section fixes `Λ` to be a ring
in which `p` is invertible and defines `C(Λ)` only for such `Λ`, so for a Noetherian `Λ` in
which some `q_v` is not invertible — `Λ = ℤ`, say — the cleared condition `q_v · U_v f = f` is
not the source's `U_v f = φ_v⁻¹ f` and the proposition asserts nothing. The field `fg` is
therefore stronger than the source's clause (1). Because the bundle is consumed whole, anything
discharging it owes the stronger statement.

Its two fields are the proposition's two clauses, in this stronger form. See the implementation
notes of `StacksFrontier.NumberTheory.Adeles.SwitchingEll`. -/
public structure CuspFormsFinite (K : Type u) [Field K] : Prop where
  /-- `C(Λ)` is a finitely generated `Λ`-module whenever `Λ` is Noetherian. -/
  fg : ∀ (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ], (cuspFormsCentralChar K Λ).FG
  /-- `C(Λ) = C(F) ⊗_F Λ` for `Λ` a field with prime subfield `F`. -/
  baseChange : ∀ (Λ : Type w) [Field Λ],
    ∃ (n : ℕ) (g : Fin n → GL (Fin 2) (AdeleRing K) → ↥(⊥ : Subfield Λ)),
      Submodule.span ↥(⊥ : Subfield Λ) (Set.range g) =
          cuspFormsCentralChar K ↥(⊥ : Subfield Λ) ∧
        LinearIndependent ↥(⊥ : Subfield Λ) g ∧
          Submodule.span Λ (Set.range fun i =>
              mapCoeffs (algebraMap ↥(⊥ : Subfield Λ) Λ) (g i)) = cuspFormsCentralChar K Λ ∧
            LinearIndependent Λ fun i => mapCoeffs (algebraMap ↥(⊥ : Subfield Λ) Λ) (g i)

/-- **The step of the source's proof of Lemma 03VY that applies Proposition 03VW**, carried as a
hypothesis which takes Proposition 03VW as its input. The source writes it in two sentences:
"use Proposition 03VW to see that we may choose `f ∈ C(E')` with `E ⊂ E'` finite. Next we may
complete `E'` to see that we get `f ∈ C(E'_{λ'})` eigenform with `E'_{λ'}` a finite extension of
`E_{λ'}`." Its conclusion therefore gives the number field `E'`, its two embeddings — into
`E_λ`, where the Hecke eigenvalues of the given form live, and into the finite extension
`E'_{λ'}` of `E_{λ'}` — the eigenvalues `t'` over `E'`, and the resulting eigenform over the
algebraic closure `Ω'` of `E_{λ'}`.

Deriving this from Proposition 03VW is not done here: it needs the rationality over the prime
field of a simultaneous eigenvector of the Hecke operators on the finite-dimensional space
`C(F)`, which the source leaves implicit. The implication is therefore carried, with
Proposition 03VW as its hypothesis so that the proposition is what justifies it, exactly as in
the source. It has no `stacks` attribute. -/
public def CuspFormsFiniteDescent (K : Type u) [Field K] (E : Type w) [Field E] [NumberField E]
    (lam lam' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (Ωlam : Type s) [Field Ωlam] [Algebra (lam.adicCompletion E) Ωlam]
    [IsAlgClosure (lam.adicCompletion E) Ωlam]
    (Ω' : Type s) [Field Ω'] [Algebra (lam'.adicCompletion E) Ω']
    [IsAlgClosure (lam'.adicCompletion E) Ω'] : Prop :=
  CuspFormsFinite.{u, w} K →
    ∀ (f : GL (Fin 2) (AdeleRing K) → Ωlam) (t : Place K → Ωlam),
      IsEigenform f t (fun v => (Place.residueCard v : Ωlam)⁻¹) →
        f ∈ cuspFormsCentralChar K Ωlam →
          ∃ (E' : FieldExtension E) (L : TopologicalFieldExtension (lam'.adicCompletion E))
            (j : E'.carrier →+* lam.adicCompletion E) (j' : E'.carrier →+* L.carrier)
            (iL : L.carrier →+* Ω') (t' : Place K → E'.carrier)
            (f' : GL (Fin 2) (AdeleRing K) → Ω'),
            j.comp (algebraMap E E'.carrier) = algebraMap E (lam.adicCompletion E) ∧
              j'.comp (algebraMap E E'.carrier) =
                  (algebraMap (lam'.adicCompletion E) L.carrier).comp
                    (algebraMap E (lam'.adicCompletion E)) ∧
                iL.comp (algebraMap (lam'.adicCompletion E) L.carrier) =
                    algebraMap (lam'.adicCompletion E) Ω' ∧
                  (∀ v, algebraMap (lam.adicCompletion E) Ωlam (j (t' v)) = t v) ∧
                    IsEigenform f' (fun v => iL (j' (t' v)))
                        (fun v => (Place.residueCard v : Ω')⁻¹) ∧
                      f' ∈ cuspFormsCentralChar K Ω'

/-! ### Landing in `SL₂` -/

/-- A continuous two-dimensional representation of a topological group whose determinant is `1`
at every member of a topologically generating family has determinant `1` throughout. This is the
step of the source's proof of Lemma 03VY that upgrades the representation produced by
Theorem 03VT from `GL₂` to `SL₂`; the generating family is the family of Frobenius elements,
which topologically generate by Stacks 03W5. -/
public theorem det_eq_one_of_det_frobenius_eq_one {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {ι : Type u} (Frob : ι → Γ)
    (hFrob : (Subgroup.closure (Set.range Frob)).topologicalClosure = ⊤) {M : Type w} [Field M]
    [TopologicalSpace M] [IsTopologicalRing M] [T2Space M] (ρ : Γ →* GL (Fin 2) M)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin 2) (Fin 2) M))
    (hdet : ∀ i, Matrix.det (ρ (Frob i) : Matrix (Fin 2) (Fin 2) M) = 1) (g : Γ) :
    Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) M) = 1 := by
  set S : Subgroup Γ := (Matrix.GeneralLinearGroup.det.comp ρ).ker with hS
  have hmem : ∀ x : Γ, x ∈ S ↔ Matrix.det (ρ x : Matrix (Fin 2) (Fin 2) M) = 1 := by
    intro x
    simp [hS, MonoidHom.mem_ker, Units.ext_iff]
  have hcarrier : (S : Set Γ) =
      (fun x => Matrix.det (ρ x : Matrix (Fin 2) (Fin 2) M)) ⁻¹' {1} := by
    ext x
    simpa using hmem x
  have hclosed : IsClosed (S : Set Γ) := by
    rw [hcarrier]
    exact (isClosed_singleton (x := (1 : M))).preimage hρ.matrix_det
  have hle : Subgroup.closure (Set.range Frob) ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    rintro x ⟨i, rfl⟩
    exact (hmem _).2 (hdet i)
  have htop : (⊤ : Subgroup Γ) ≤ S :=
    hFrob ▸ Subgroup.topologicalClosure_minimal _ hle hclosed
  exact (hmem g).1 (htop (Subgroup.mem_top g))

/-! ### Lemma 03VY -/

/-- The characteristic polynomial of a `2 × 2` matrix of determinant `1` is `X² - tr X + 1`. -/
private theorem charpoly_eq_of_det_eq_one {R : Type*} [CommRing R] [Nontrivial R]
    (A : Matrix (Fin 2) (Fin 2) R)
    (h : A.det = 1) :
    A.charpoly = Polynomial.X ^ 2 - Polynomial.C A.trace * Polynomial.X + Polynomial.C 1 := by
  rw [Matrix.charpoly_fin_two, h]

/-- **Stacks Project, Tag 03VY.** Switching `ℓ`. Let `E` be a number field and let
`ρ : Γ → SL₂(E_λ)` be absolutely irreducible and continuous, where `λ` is a finite place of `E`
(in the source, a place not lying above the characteristic `p` of the base field of the curve,
and `Γ = π₁(X)` with `Frob v` the geometric Frobenius at `v`). Then for any second finite place
`λ'` of `E` there are a finite extension `L` of `E_{λ'}` and an absolutely irreducible
continuous `ρ' : Γ → SL₂(L)` compatible with `ρ`, in the sense that the characteristic
polynomials of all Frobenii are the same: for every place `v` one polynomial over a number field
`E'` finite over `E` is the characteristic polynomial of both `ρ(F_v)` and `ρ'(F_v)`.

Theorem 03VT, Theorem 03VU and Proposition 03VW are carried as the hypotheses `hVT`, `hVU` and
`hVW`, the source's application of Proposition 03VW as `hdescent`, the topological generation of
`Γ` by the Frobenius elements (Stacks 03W5) as `hFrob`, and the invertibility of the residue
cardinalities in the integers of `E_{λ'}` (the content of `λ'` not lying above `p`) as `hq`. See
the implementation notes of `StacksFrontier.NumberTheory.Adeles.SwitchingEll`. -/
public theorem exists_compatible_representation {K : Type u} [Field K] {Γ : Type v} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Frob : Place K → Γ) (E : Type w) [Field E]
    [NumberField E]
    (lam lam' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (Ωlam : Type s) [Field Ωlam] [Algebra (lam.adicCompletion E) Ωlam]
    [IsAlgClosure (lam.adicCompletion E) Ωlam]
    (Ω' : Type s) [Field Ω'] [Algebra (lam'.adicCompletion E) Ω']
    [IsAlgClosure (lam'.adicCompletion E) Ω']
    (hVU : DrinfeldMakeF K Γ Frob (lam.adicCompletion E) Ωlam)
    (hVW : CuspFormsFinite.{u, w} K)
    (hdescent : CuspFormsFiniteDescent K E lam lam' Ωlam Ω')
    (hVT : DrinfeldMakeRho K Γ Frob (lam'.adicCompletion E)
      (lam'.adicCompletionIntegers E).toSubring Ω')
    (hFrob : (Subgroup.closure (Set.range Frob)).topologicalClosure = ⊤)
    (hq : ∀ v : Place K,
      IsUnit ((Place.residueCard v : ↥((lam'.adicCompletionIntegers E).toSubring))))
    (hqlam : ∀ v : Place K, (Place.residueCard v : Ωlam) ≠ 0)
    (ρ : Γ →* Matrix.SpecialLinearGroup (Fin 2) (lam.adicCompletion E))
    (hρ : Continuous fun g =>
      (ρ g : Matrix (Fin 2) (Fin 2) (lam.adicCompletion E)))
    (hρirr : IsAbsolutelyIrreducible (Matrix.SpecialLinearGroup.toGL.comp ρ)) :
    ∃ (L : TopologicalFieldExtension (lam'.adicCompletion E))
      (ρ' : Γ →* Matrix.SpecialLinearGroup (Fin 2) L.carrier)
      (iL : L.carrier →+* Ω') (E' : FieldExtension E)
      (j : E'.carrier →+* lam.adicCompletion E) (jΩ : E'.carrier →+* Ω'),
      Continuous (fun g => (ρ' g : Matrix (Fin 2) (Fin 2) L.carrier)) ∧
        IsAbsolutelyIrreducible (Matrix.SpecialLinearGroup.toGL.comp ρ') ∧
          iL.comp (algebraMap (lam'.adicCompletion E) L.carrier) =
              algebraMap (lam'.adicCompletion E) Ω' ∧
            j.comp (algebraMap E E'.carrier) = algebraMap E (lam.adicCompletion E) ∧
              jΩ.comp (algebraMap E E'.carrier) =
                  (algebraMap (lam'.adicCompletion E) Ω').comp
                    (algebraMap E (lam'.adicCompletion E)) ∧
                ∀ v : Place K, ∃ P : Polynomial E'.carrier,
                  (ρ (Frob v) :
                      Matrix (Fin 2) (Fin 2) (lam.adicCompletion E)).charpoly = P.map j ∧
                    ((ρ' (Frob v) : Matrix (Fin 2) (Fin 2) L.carrier).charpoly).map iL =
                      P.map jΩ := by
  -- Step 1: Theorem 03VU, at the coefficient field `E_λ` itself, produces an eigenform.
  obtain ⟨f, t, u, hf, hfeq⟩ :=
    hVU (lam.adicCompletion E) (algebraMap (lam.adicCompletion E) Ωlam) (by simp)
      (Matrix.SpecialLinearGroup.toGL.comp ρ) hρ hρirr
  -- Its central eigenvalues are `q_v⁻¹`, because `ρ` takes values in `SL₂`.
  have hu : u = fun v => (Place.residueCard v : Ωlam)⁻¹ := by
    funext v
    rw [(hfeq v).2]
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
  subst hu
  -- Hence the form lies in `C(Ωlam)`.
  have hfC : f ∈ cuspFormsCentralChar K Ωlam := by
    refine mem_cuspFormsCentralChar ⟨hf.isUnramifiedCuspForm, fun v a hdata x => ?_⟩
    rw [hf.central v a hdata x, ← mul_assoc, mul_inv_cancel₀ (hqlam v), one_mul]
  -- Steps 2 and 3: the source's application of Proposition 03VW, and completion.
  obtain ⟨E', Ld, jd, j'd, iLd, t', f', hjdE, hj'dE, hiLdE, htt, hf', -⟩ :=
    hdescent hVW f _ hf hfC
  -- The residue cardinalities are units of the integers of `E_{λ'}`, hence of `Ω'`.
  have hcast : ∀ v : Place K, (algebraMap ↥((lam'.adicCompletionIntegers E).toSubring) Ω')
      ((Place.residueCard v : ↥((lam'.adicCompletionIntegers E).toSubring))) =
      (Place.residueCard v : Ω') := fun _ => map_natCast _ _
  have hqne : ∀ v : Place K, (Place.residueCard v : Ω')⁻¹ ≠ 0 := fun v =>
    inv_ne_zero (hcast v ▸
      ((hq v).map (algebraMap ↥((lam'.adicCompletionIntegers E).toSubring) Ω'))).ne_zero
  have hqint : ∀ v : Place K,
      IsIntegral ((lam'.adicCompletionIntegers E).toSubring) ((Place.residueCard v : Ω')⁻¹) ∧
        IsIntegral ((lam'.adicCompletionIntegers E).toSubring)
          ((Place.residueCard v : Ω')⁻¹)⁻¹ := by
    intro v
    obtain ⟨c, hc⟩ := (hq v).exists_right_inv
    have hinv : (algebraMap ↥((lam'.adicCompletionIntegers E).toSubring) Ω') c =
        (Place.residueCard v : Ω')⁻¹ := by
      refine (inv_eq_of_mul_eq_one_right ?_).symm
      rw [← hcast v, ← map_mul, hc, map_one]
    exact ⟨hinv ▸ isIntegral_algebraMap, by rw [inv_inv, ← hcast v]; exact isIntegral_algebraMap⟩
  -- Step 4: Theorem 03VT turns the form back into a representation.
  obtain ⟨L₂, j₂, ρ₂, hj₂, hρ₂cont, hρ₂irr, hρ₂eq⟩ := hVT f' _ _ hf' hqint
  -- The determinant is one at every Frobenius element, hence everywhere.
  have hdet₂ : ∀ v : Place K,
      Matrix.det (ρ₂ (Frob v) : Matrix (Fin 2) (Fin 2) L₂.carrier) = 1 := by
    intro v
    refine j₂.injective ?_
    rw [map_one]
    exact (mul_left_cancel₀ (hqne v) (by rw [mul_one]; exact (hρ₂eq v).2)).symm
  have := IsModuleTopology.isTopologicalRing (lam'.adicCompletion E) L₂.carrier
  have hdetall : ∀ g : Γ, Matrix.det (ρ₂ g : Matrix (Fin 2) (Fin 2) L₂.carrier) = 1 :=
    det_eq_one_of_det_frobenius_eq_one Frob hFrob ρ₂ hρ₂cont hdet₂
  -- The resulting representation into `SL₂`.
  let σ : Γ →* Matrix.SpecialLinearGroup (Fin 2) L₂.carrier :=
    { toFun := fun g => ⟨(ρ₂ g : Matrix (Fin 2) (Fin 2) L₂.carrier), hdetall g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (ρ₂ (a * b) : Matrix (Fin 2) (Fin 2) L₂.carrier) =
          (ρ₂ a : Matrix (Fin 2) (Fin 2) L₂.carrier) *
            (ρ₂ b : Matrix (Fin 2) (Fin 2) L₂.carrier)
        rw [map_mul]
        rfl) }
  refine ⟨L₂, σ, j₂, E', jd, iLd.comp j'd, hρ₂cont, hρ₂irr, hj₂, hjdE, ?_, fun v => ?_⟩
  · ext x
    have h1 : j'd (algebraMap E E'.carrier x) =
        algebraMap (lam'.adicCompletion E) Ld.carrier
          (algebraMap E (lam'.adicCompletion E) x) := DFunLike.congr_fun hj'dE x
    have h2 := DFunLike.congr_fun hiLdE (algebraMap E (lam'.adicCompletion E) x)
    simp only [RingHom.coe_comp, Function.comp_apply] at h2 ⊢
    rw [h1, h2]
  · -- The common characteristic polynomial over the number field `E'`.
    have htrace : jd (t' v) =
        Matrix.trace (ρ (Frob v) : Matrix (Fin 2) (Fin 2) (lam.adicCompletion E)) := by
      refine (algebraMap (lam.adicCompletion E) Ωlam).injective ?_
      rw [htt v, (hfeq v).1]
      rfl
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (t' v) * Polynomial.X + Polynomial.C 1, ?_, ?_⟩
    · rw [charpoly_eq_of_det_eq_one _ (Matrix.SpecialLinearGroup.det_coe _), ← htrace]
      simp
    · rw [charpoly_eq_of_det_eq_one _ (σ (Frob v)).2]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, map_one, RingHom.coe_comp,
        Function.comp_apply]
      rw [(hρ₂eq v).1]
      rfl

end Stacks.Adeles

end
