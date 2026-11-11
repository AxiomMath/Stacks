module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SixTerm

/-!
# The Jacobi-Zariski six-term exact sequence of the naive cotangent complex

Let `A → B → C` be ring maps, let `α : A[x_s] → B` be a presentation of `B` over `A` with
kernel `I` and let `β : B[y_t] → C` be a presentation of `C` over `B` with kernel `J`.  They
induce a presentation `γ : A[x_s, y_t] → C` of `C` over `A`, with kernel `K`, and the three
naive cotangent complexes sit in a commutative diagram of `C`-modules
```
 C ⊗_B I/I²  ⟶    K/K²      ⟶    J/J²      ⟶ 0
      │              │              │
      ▼              ▼              ▼
0 ⟶ C ⊗_B Ω_{A[x]/A} ⟶ Ω_{A[x,y]/A} ⊗ C ⟶ Ω_{B[y]/B} ⊗ C ⟶ 0
```
whose degree-`0` row is short exact, because `dx_s` and `dy_t` together form a basis of the
middle term, and whose degree-`1` row is right exact.  The snake lemma therefore produces a
connecting map `δ` and a six-term exact sequence of `C`-modules
```
H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) --δ--> H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0.
```
This is **Stacks 00S2** for the *naive* cotangent complex.  Writing `H₀(NL(γ)) = Ω_{C/A}`
and `H₁(NL(γ)) = H₁(L_{C/A})`, and likewise for the other two columns, this is the six-term
sequence
```
H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0
```
of the source; the identification of the homology of `NL` of a presentation with the
presentation-independent modules is Stacks 00S1
(`NaiveCotangent.nlMap_canonical_isQuasiIso`), and none of it is used here, exactly as in
the source, whose own proof runs over the three chosen presentations.

## Main definitions

* `NaiveCotangent.nlBaseChange`: the complex `NL(α) ⊗_B C`.
* `NaiveCotangent.nlToComp`, `NaiveCotangent.nlOfComp`: the two chain maps
  `NL(α) ⊗_B C ⟶ NL(γ)` and `NL(γ) ⟶ NL(β)`.
* `NaiveCotangent.jacobiZariskiConnecting`: the connecting map
  `δ : H₁(NL(β)) → H₀(NL(α) ⊗_B C)`.

## Main results

* `NaiveCotangent.jacobiZariski_diagram`: the diagram above, with its exact rows.
* `NaiveCotangent.jacobiZariski_sixTerm_exact`: **Stacks 00S2**, the six-term sequence above
  is exact at each of its five interior nodes.
* `NaiveCotangent.exists_jacobiZariski_sixTerm_exact`: the same, with the connecting map
  existentially quantified, which is the form in which the source states it.

## Implementation notes

The homological content is `NaiveCotangent.exists_sixTerm_exact`, the snake lemma for a
degreewise exact triple of two-term complexes; all that happens here is that its five
hypotheses are supplied.  Four of them are Mathlib's description of the two rows of the
diagram: `Algebra.Generators.CotangentSpace.map_toComp_injective`,
`Algebra.Generators.CotangentSpace.exact` and
`Algebra.Generators.CotangentSpace.map_ofComp_surjective` for the degree-`0` row, and
`Algebra.Generators.Cotangent.exact` together with
`Algebra.Generators.Cotangent.surjective_map_ofComp` for the degree-`1` row.

Exactness at `H₁(NL(α) ⊗_B C)` is not asserted, and is false in general: the degree-`1` row
is only right exact.

The final assertion of Stacks 00S2, that `Tor₁^B(Ω_{B/A}, C) = Tor₂^B(Ω_{B/A}, C) = 0` gives
`H₁(NL_{B/A} ⊗_B C) = H₁(L_{B/A}) ⊗_B C`, is
`NaiveCotangent.bijective_h1BaseChangeMap_of_tor` in
`StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiTor`.

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), Lemma 10.134.4.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), Lemma 10.134.2.
-/

@[expose] public section

universe w₁ w₂ u₁ u₂ u₃

open Algebra Function TensorProduct

namespace NaiveCotangent

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {σ : Type w₂}

/-- The base change `NL(α) ⊗_S T` along `S → T` of the naive cotangent complex of a
presentation `α : P → S` of `S` over `R`: the two-term complex of `T`-modules
`T ⊗_S I/I² ⟶ T ⊗_S (Ω_{P/R} ⊗_P S)`, with differential the base change of the
differential of `NL(α)`. -/
public noncomputable def nlBaseChange (T : Type*) [CommRing T] [Algebra S T]
    (P : Generators R S σ) : TwoTerm T where
  X₁ := T ⊗[S] P.toExtension.Cotangent
  X₀ := T ⊗[S] P.toExtension.CotangentSpace
  d := P.toExtension.cotangentComplex.baseChange T

omit [Algebra R T] [IsScalarTower R S T] in
/-- The differential of `NL(α) ⊗_S T` is the base change of the differential of `NL(α)`. -/
@[simp] public theorem nlBaseChange_d (P : Generators R S σ) :
    (nlBaseChange T P).d = P.toExtension.cotangentComplex.baseChange T := rfl

/-- The chain map `NL(α) ⊗_B C ⟶ NL(γ)` induced by the inclusion `A[x_s] → A[x_s, y_t]` of
presentations: on conormal modules it is the base change along `B → C` of `I/I² → K/K²`,
and in degree `0` it is the base change of `Ω_{A[x]/A} ⊗ B → Ω_{A[x,y]/A} ⊗ C`. -/
public noncomputable def nlToComp (Q : Generators S T ι) (P : Generators R S σ) :
    ChainMap (nlBaseChange T P) (NL (Q.comp P)) where
  f₁ := (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T
  f₀ := (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T
  comm := (Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P).symm

/-- In degree `1`, `nlToComp` is the base change of the map `I/I² → K/K²` of conormal
modules. -/
@[simp] public theorem nlToComp_f₁ (Q : Generators S T ι) (P : Generators R S σ) :
    (nlToComp Q P).f₁ = (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T :=
  rfl

/-- In degree `0`, `nlToComp` is the base change of the map of cotangent spaces
`Ω_{A[x]/A} ⊗ B → Ω_{A[x,y]/A} ⊗ C`. -/
@[simp] public theorem nlToComp_f₀ (Q : Generators S T ι) (P : Generators R S σ) :
    (nlToComp Q P).f₀ =
      (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T := rfl

/-- The chain map `NL(γ) ⟶ NL(β)` induced by the surjection `A[x_s, y_t] → B[y_t]` of
presentations: it is `K/K² → J/J²` in degree `1` and
`Ω_{A[x,y]/A} ⊗ C → Ω_{B[y]/B} ⊗ C` in degree `0`. -/
public noncomputable def nlOfComp (Q : Generators S T ι) (P : Generators R S σ) :
    ChainMap (NL (Q.comp P)) (NL Q) where
  f₁ := Extension.Cotangent.map (Q.ofComp P).toExtensionHom
  f₀ := Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom
  comm := by
    ext x
    exact (Extension.CotangentSpace.map_cotangentComplex (Q.ofComp P).toExtensionHom x).symm

/-- In degree `1`, `nlOfComp` is the map `K/K² → J/J²` of conormal modules. -/
@[simp] public theorem nlOfComp_f₁ (Q : Generators S T ι) (P : Generators R S σ) :
    (nlOfComp Q P).f₁ = Extension.Cotangent.map (Q.ofComp P).toExtensionHom := rfl

/-- In degree `0`, `nlOfComp` is the map `Ω_{A[x,y]/A} ⊗ C → Ω_{B[y]/B} ⊗ C` of cotangent
spaces. -/
@[simp] public theorem nlOfComp_f₀ (Q : Generators S T ι) (P : Generators R S σ) :
    (nlOfComp Q P).f₀ = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom := rfl

/-- **The Jacobi-Zariski diagram** (Stacks 00S2, first assertion).  Let `A → B → C` be ring maps,
let `α : A[x_s] → B` and `β : B[y_t] → C` be presentations with kernels `I` and `J`, and let
`γ : A[x_s, y_t] → C` be the induced presentation, with kernel `K`.  In the canonical diagram
```
0 ⟶ C ⊗_B Ω_{A[x]/A} ⊗ B ⟶ Ω_{A[x,y]/A} ⊗ C ⟶ Ω_{B[y]/B} ⊗ C ⟶ 0
          ▲                       ▲                  ▲
     C ⊗_B I/I²       ⟶         K/K²       ⟶       J/J²        ⟶ 0
```
the top row is short exact, the bottom row is exact, and both squares commute: the vertical
maps are the differentials of `NL(α) ⊗_B C`, `NL(γ)` and `NL(β)`, and the horizontal ones are
the components of `NaiveCotangent.nlToComp` and `NaiveCotangent.nlOfComp`. -/
@[stacks 00S2 "The canonical commutative diagram with exact rows: the top row is short \
exact, the bottom row is exact with a surjection at its right end."]
public theorem jacobiZariski_diagram (Q : Generators S T ι) (P : Generators R S σ) :
    Injective (nlToComp Q P).f₀ ∧ Exact (nlToComp Q P).f₀ (nlOfComp Q P).f₀ ∧
      Surjective (nlOfComp Q P).f₀ ∧ Exact (nlToComp Q P).f₁ (nlOfComp Q P).f₁ ∧
      Surjective (nlOfComp Q P).f₁ ∧
      (NL (Q.comp P)).d ∘ₗ (nlToComp Q P).f₁ = (nlToComp Q P).f₀ ∘ₗ (nlBaseChange T P).d ∧
      (NL Q).d ∘ₗ (nlOfComp Q P).f₁ = (nlOfComp Q P).f₀ ∘ₗ (NL (Q.comp P)).d :=
  ⟨Generators.CotangentSpace.map_toComp_injective Q P, Generators.CotangentSpace.exact Q P,
    Generators.CotangentSpace.map_ofComp_surjective Q P, Generators.Cotangent.exact Q P,
    Generators.Cotangent.surjective_map_ofComp Q P, (nlToComp Q P).comm, (nlOfComp Q P).comm⟩

/-- **The Jacobi-Zariski connecting map** (Stacks 00S2): for ring maps `A → B → C` and
presentations `α : A[x_s] → B`, `β : B[y_t] → C` with induced presentation
`γ : A[x_s, y_t] → C`, the snake-lemma map
`δ : H₁(NL(β)) ⟶ H₀(NL(α) ⊗_B C)`, that is `H₁(L_{C/B}) → C ⊗_B Ω_{B/A}`. -/
@[stacks 00S2 "The connecting map of the six-term sequence, for the naive cotangent
complexes of three presentations as in the source's own proof."]
public noncomputable def jacobiZariskiConnecting (Q : Generators S T ι) (P : Generators R S σ) :
    H₁ (NL Q) →ₗ[T] H₀ (nlBaseChange T P) :=
  connecting (nlToComp Q P) (nlOfComp Q P)
    (Generators.CotangentSpace.map_toComp_injective Q P)
    (Generators.CotangentSpace.exact Q P)
    (Generators.Cotangent.surjective_map_ofComp Q P)
    (Generators.Cotangent.exact Q P)

/-- **The Jacobi-Zariski six-term exact sequence** (Stacks 00S2) for the naive cotangent
complex.  Let `A → B → C` be ring maps, let `α : A[x_s] → B` and `β : B[y_t] → C` be
presentations and let `γ : A[x_s, y_t] → C` be the induced presentation of `C` over `A`.
Then
```
H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) --δ--> H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0
```
is exact at each of its five interior nodes, `δ` being
`NaiveCotangent.jacobiZariskiConnecting`.  In the notation of the source this is
`H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0`. -/
@[stacks 00S2 "The six-term exact sequence for the naive cotangent complex, over the three
presentations of the source's own proof; `Stacks.KaehlerDifferential.JacobiZariski` records
only exactness at `H₁(L_{C/A})`, and for the full cotangent complex."]
public theorem jacobiZariski_sixTerm_exact (Q : Generators S T ι) (P : Generators R S σ) :
    Exact (nlToComp Q P).onH₁ (nlOfComp Q P).onH₁ ∧
      Exact (nlOfComp Q P).onH₁ (jacobiZariskiConnecting Q P) ∧
      Exact (jacobiZariskiConnecting Q P) (nlToComp Q P).onH₀ ∧
      Exact (nlToComp Q P).onH₀ (nlOfComp Q P).onH₀ ∧
      Surjective (nlOfComp Q P).onH₀ :=
  ⟨exact_onH₁ _ _ (Generators.CotangentSpace.map_toComp_injective Q P)
      (Generators.Cotangent.exact Q P),
    exact_onH₁_connecting _ _ _ _ _ _,
    exact_connecting_onH₀ _ _ _ _ _ _,
    exact_onH₀ _ _ (Generators.CotangentSpace.exact Q P)
      (Generators.Cotangent.surjective_map_ofComp Q P),
    surjective_onH₀ _ (Generators.CotangentSpace.map_ofComp_surjective Q P)⟩

/-- **Stacks 00S2** in the form in which the source states it: there *exists* a six-term
exact sequence
```
H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) → H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0
```
of `C`-modules, for ring maps `A → B → C`, presentations `α : A[x_s] → B`,
`β : B[y_t] → C` and the induced presentation `γ : A[x_s, y_t] → C`. -/
@[stacks 00S2 "The existential form of the six-term sequence for the naive cotangent
complex."]
public theorem exists_jacobiZariski_sixTerm_exact (Q : Generators S T ι)
    (P : Generators R S σ) :
    ∃ δ : H₁ (NL Q) →ₗ[T] H₀ (nlBaseChange T P),
      Exact (nlToComp Q P).onH₁ (nlOfComp Q P).onH₁ ∧
        Exact (nlOfComp Q P).onH₁ δ ∧
        Exact δ (nlToComp Q P).onH₀ ∧
        Exact (nlToComp Q P).onH₀ (nlOfComp Q P).onH₀ ∧
        Surjective (nlOfComp Q P).onH₀ :=
  ⟨jacobiZariskiConnecting Q P, jacobiZariski_sixTerm_exact Q P⟩

end NaiveCotangent

end
