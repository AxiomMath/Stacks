module

public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# The evaluation map at a relative dualizing complex

Let `R → A` be flat of finite presentation and let `ω` be a relative dualizing complex for
`R → A` in the sense of [stacks 0E2C]. The uniqueness of relative dualizing complexes
[stacks 0E2D] would follow at once from invertibility of the **evaluation map**

`ev_K : RHom_A(ω, K) ⊗ᴸ_A ω ⟶ K`,

the transpose of the identity of `RHom_A(ω, K)` under the tensor--Hom adjunction of
[stacks 0A63] (`StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation`): reading the defining
condition as `RHom_A(ω, K) ≅ A` for a second relative dualizing complex `K` turns the source of
`ev_K` into `ω`, so invertibility of `ev_K` gives `ω ≅ K`. Both readings are hypotheses of
`Dualizing.nonempty_iso_of_isIso_evaluation` below and neither follows from [stacks 0E2C] in this
library: the defining condition lives in `D(A ⊗[R] A)` and concerns one complex at a time. **The
first of the two is no longer out of reach**: when `ω` is in addition a dualizing complex for `A`
in the sense of [stacks 0A7B], `Dualizing.nonempty_derivedHom_iso_derivedTensorUnit_of_dualDual` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` produces `RHom_A(ω, K) ≅ A` from
`RHom_A(RHom_A(K, ω), A) ≅ A`, and that last statement is what the defining condition of
[stacks 0E2C] becomes once the diagonal functor `Δ^!(p₁^*-)` is commuted past derived Hom out of a
pseudo-coherent object — see the section "The duality route" of that module. **That commutation is
now a theorem**, `Dualizing.nonempty_relativeDualizingFunctor_modelHom_commutation` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessEnrichedAdjunction`, and so is the conclusion
drawn from it: `Dualizing.nonempty_modelHom_dual_iso_of_relativeDualizingCondition` of that module
produces `RHom_A(RHom_A(K, ω), 1) ≅ 1` from the defining condition at `ω` and at `K` together with
biduality at `K`. The route the source takes instead, through [stacks 0ATK] (3), is refuted in this
library — see the module docstring of `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` and
`Stacks.DerivedTensorHomDiagonal.isIso_diagonal_of_projective_quasiIso_theta`.

This file settles exactly when the evaluation map is invertible, and the answer is a negative
one for that route to [stacks 0E2D]: **`ev_K` is invertible for every `K` if and only if `ω`
has a tensor inverse**, and already invertibility of `ev_K` at the single object `K = A` forces
that. So the statement "`ev_K` is invertible for every `R`-perfect `K`" is not a theorem about
relative dualizing complexes; it is the hypothesis that `R → A` is Gorenstein, in disguise.

## Main results

* `Dualizing.isIso_evaluation_of_tensor_iso_one` — **from a tensor inverse to all of `D(A)`.**
  If `ω ⊗ᴸ ω' ≅ A` for some `ω'`, then `ev_K` is invertible for *every* object `K`, with no
  perfection, coherence or boundedness hypothesis on `K`.
* `Dualizing.nonempty_tensor_iso_one_of_isIso_evaluation` — **the converse, from one object.**
  If `ev_K` is invertible at `K = A` then `RHom_A(ω, A)` is a tensor inverse of `ω`.
* `Dualizing.isIso_evaluation_iff_nonempty_tensor_iso_one`,
  `Dualizing.isIso_evaluation_iff_isIso_evaluation_one` — the resulting characterisations: the
  evaluation map is invertible at every object iff `ω` is tensor-invertible iff it is invertible
  at the tensor unit alone.
* `Dualizing.isIso_evaluation_of_iso_right` — invertibility of the evaluation map at its target
  transports along an isomorphism of the target. Together with
  `Dualizing.derivedTensorUnitIsoSingle`, which identifies the tensor unit of `D(A)` with `A` in
  degree zero, this reads the characterisations above at `K = A[0]`.
* `Dualizing.nonempty_iso_of_isIso_evaluation` — **the conversion step.** If
  `RHom_A(ω, K) ≅ A` and the evaluation map at `K` is invertible, then `ω ≅ K`. This is the
  implication [stacks 0E2D] is after, isolated from any claim about which `K` the evaluation map
  is invertible at.
* `Dualizing.isIso_evaluation_self_of_isIso_derivedHomothety` — **what the uniqueness argument
  really needs.** At the single object `K = ω` the evaluation map is invertible as soon as the
  derived homothety `A ⟶ RHom_A(ω, ω)` is, which is [stacks 0E2G]. No dévissage, and no
  invertibility of `ω`.
* `Dualizing.isIso_evaluation_overRing_iff_nonempty_tensor_iso_derivedTensorUnit`,
  `Dualizing.isIso_evaluation_overRing_iff_isIso_evaluation_derivedTensorUnit` and
  `Dualizing.isIso_evaluation_overRing_self_of_isIso_derivedHomothety` — the same results for
  the adjunction of [stacks 0A63] over a ring, whose tensor unit, left unitor and the
  naturality of that unitor are `StacksDraft.DerivedHom.derivedTensorUnit`,
  `StacksDraft.DerivedHom.derivedTensorUnitLeft` and
  `StacksDraft.DerivedHom.derivedTensorUnitLeft_natural`.

## Why this refutes the evaluation route to [stacks 0E2D]

The tensor unit `A` is `R`-perfect: it is a bounded complex of finitely presented `A`-modules
flat over `R`, since `R → A` is flat of finite presentation. So the proposed statement — `ev_K`
invertible for every `R`-perfect `K` — contains the case `K = A`, and
`nonempty_tensor_iso_one_of_isIso_evaluation` turns that case into a tensor inverse for `ω`.
An invertible object of `D(A)` is, locally on `Spec A`, a shift of the structure sheaf
([stacks 0FNT], `DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit`); over a local
ring it is therefore `A[n]`, and a relative dualizing complex isomorphic to `A[n]` is exactly
what it means for `R → A` to be Gorenstein. The proposed statement is that hypothesis.

It fails for the witness already recorded in
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`: take `R = k` a field,
`A = k[x, y]/(x, y)²` and `ω = Hom_k(A, k)`. Then `R → A` is flat of finite presentation and `ω`
is a relative dualizing complex, while `A` is Artinian local of length `3` whose socle is the
maximal ideal `m = (x, y)`, so

`dim_k ω/mω = dim_k Hom_k(soc A, k) = dim_k m = 2`.

Hence `ω` needs two generators and is not isomorphic to any `A[n]`, so it has no tensor inverse
and `ev_A` is not invertible. The failure is visible without invoking [stacks 0FNT] at all, and
it is not confined to `K = A`: at the `R`-perfect object `K = A/m = k`, the complex
`RHom_A(ω, k)` has `H^i = Ext^i_A(ω, k) ≅ Hom_k(Tor_i^A(ω, k), k)` concentrated in degrees
`i ≥ 0` with `H^0 = Hom_A(ω, k) = k²`, so the lowest cohomology of the source of `ev_k` is

`H^0(RHom_A(ω, k) ⊗ᴸ_A ω) = H^0(RHom_A(ω, k)) ⊗_A ω = (ω/mω)² = k⁴`,

of dimension `4`, while `H^0(k)` has dimension `1`.

Two consequences for the chapter. First, the dévissage strategy for the proposed statement
cannot work, and for two independent reasons: its base case `K = A` is false, and the
`R`-perfect objects are not generated from `A` by shifts, cones and retracts — that process
generates the perfect objects, whereas over the witness above every bounded complex of
finite-length modules is `R`-perfect, `ω` among them, and `ω` has infinite projective dimension.
Second, the only instance of the evaluation map that [stacks 0E2D] actually needs is the one at
`K = ω`, where `isIso_evaluation_self_of_isIso_derivedHomothety` supplies it from [stacks 0E2G];
what is missing for uniqueness is therefore the identification of a *second* relative dualizing
complex with `ω`, not a biduality statement of this shape.

Third — and this closes the route rather than narrowing it — [stacks 0E2G] is not available
upstream of [stacks 0E2D] to supply even that instance. The source proves [stacks 0E2G] *from*
[stacks 0E2D], twice over: in the reduction to a Noetherian base, and again in the Noetherian
case, where the given relative dualizing complex is identified with `φ^!(R)` by [stacks 0E2D]
before [stacks 0BZW] is applied to it. So the evaluation map at `K = ω` is reachable from
[stacks 0E2G] only once uniqueness is already known, and the hypotheses of
`nonempty_iso_of_isIso_evaluation` at a second relative dualizing complex are of the strength of
uniqueness itself. Progress on [stacks 0E2D] has to come from the diagonal — the hypothesis
`hdiag` of `Dualizing.nonempty_iso_of_isRelativeDualizingComplex` and the Tor-amplitude bound
that would discharge it — or from identifying every relative dualizing complex with
`ω^•_{A/R}` directly.

**It is the second of those that is now open, and it does not go through the evaluation map at
all.** `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` identifies `K` with `ω`
directly: biduality with respect to `ω` writes `K` as the `ω`-dual of `P = RHom_A(K, ω)`, the
defining condition of [stacks 0E2C] becomes `RHom_A(P, A) ≅ A`, and
`Dualizing.nonempty_iso_of_dual_iso_one` converts `P ≅ A` into `K ≅ ω`. What that route leaves
open is `RHom_A(P, A) ≅ A ⟹ P ≅ A`, which — unlike the pure-acyclicity condition the diagonal
route reduces to — is a condition on `ω` and on `P` rather than on the ring. It was recorded here
as "a theorem over any Noetherian ring"; **that was an overstatement**, and the library's own
reduction of it says no such thing: the local computation it comes down to reads the extremal
degrees of a cohomological window it is given, so it needs `ω ⊗ᴸ_A κ(m)` and `P ⊗ᴸ_A κ(m)` bounded
**below**, which by [stacks 068V] is of the same strength as perfectness of those factors — at
which point the tag is already
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange`. At the witness of
this file the bound is false: `ω = Hom_k(A, k)` is not free over the Artinian local
`A = k[x, y]/(x, y)²`, so `Tor_i^A(ω, κ) ≠ 0` for every `i`. See the section "What is left" of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`, and for the one-sided computation
that would avoid the bound — whose first missing ingredient is now
`StacksDraft.ExtremalDegrees.extremalDegrees_top` of
`StacksFrontier.Homology.Tor.ExtremalDegreesTop` — the section "What a one-sided computation would
need instead" of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessLocalComputation`. The
evaluation map enters the route only positively, at an object with a tensor inverse, through
`Dualizing.nonempty_iso_one_of_tensor_iso_one_of_hom_iso_one`.

## Implementation notes

Everything is proved for an abstract `StacksDraft.DerivedHom.DerivedHomAdjunction` together
with a tensor unit `one` and a left unitor `lam`, since that is the shape in which the chapter's
evaluation map lives; the coherence actually used is only naturality of the associator, of the
symmetry and of the unitor (`DerivedHomAdjunction.IsUnitorNatural`), never the pentagon, the
hexagon or the unitor triangle. In particular no monoidal-category structure on `D(A)` is
needed, which matters because the monoidal structure of [stacks 0FNQ] is available in this
library only through the existential statement
`DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory`. "Tensor inverse" is
accordingly spelled out as an isomorphism `d.tensor.obj (ω, ω') ≅ one` rather than through
`CategoryTheory.MonoidalCategory.IsInvertible` of [stacks 0FFN]; the two readings are
interchangeable, by `Dualizing.monoidalTensorIsoDerivedHomTensor` and
`Dualizing.derivedTensorUnitIsoMonoidalUnit` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessPerfectionChain`, which identify that
monoidal structure's tensor and unit with this adjunction's.

The evaluation map is written with the tensor factors in the order
`RHom_A(ω, K) ⊗ᴸ_A ω ⟶ K`, which is the order in which the adjunction produces it; the map
`ω ⊗ᴸ_A RHom_A(ω, K) ⟶ K` is this one precomposed with the symmetry
`DerivedHomAdjunction.tensorSwap`, so each is invertible exactly when the other is.

The proof of `isIso_evaluation_of_tensor_iso_one` is the standard adjunction argument: `ev_K` is
the counit of the adjunction between `- ⊗ᴸ ω` and `RHom_A(ω, -)`, and a tensor inverse makes
`- ⊗ᴸ ω` an equivalence, hence makes the counit invertible. It is carried out by hand rather
than through `CategoryTheory.Adjunction`: tensoring with `ω` is shown to be bijective on
morphism sets (`Dualizing.bijective_tensorMap_right`), which together with the adjunction
bijection gives that composition with `ev_K` is bijective on morphisms out of every object, and
`CategoryTheory.isIso_of_yoneda_map_bijective` concludes.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public section

open CategoryTheory

namespace Dualizing

open StacksDraft.DerivedHom

noncomputable section

universe u₁ v₁ w₁

section Abstract

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v₁} R))
    (lam : ∀ K : DerivedCategory (ModuleCat.{v₁} R), d.tensor.obj (one, K) ≅ K)

/-- The transpose of `a : X ⟶ RHom(L, M)` under the tensor--Hom adjunction is `a` tensored with
the identity of `L`, followed by the evaluation map. -/
theorem homEquiv_eq_tensorMap_comp_evaluation
    (X L M : DerivedCategory (ModuleCat.{v₁} R)) (a : X ⟶ d.hom.obj (Opposite.op L, M)) :
    d.homEquiv X L M a =
      d.tensor.map (show (X, L) ⟶ (d.hom.obj (Opposite.op L, M), L) from (a, 𝟙 L)) ≫
        d.evaluation L M := by
  rw [DerivedHomAdjunction.evaluation, ← d.homEquiv_naturality_left, Category.comp_id]

/-- The tensor bifunctor applied to a pair of isomorphisms, as an isomorphism. -/
def tensorIso {X X' Y Y' : DerivedCategory (ModuleCat.{v₁} R)} (f : X ≅ X') (g : Y ≅ Y') :
    d.tensor.obj (X, Y) ≅ d.tensor.obj (X', Y') where
  hom := d.tensor.map (show (X, Y) ⟶ (X', Y') from (f.hom, g.hom))
  inv := d.tensor.map (show (X', Y') ⟶ (X, Y) from (f.inv, g.inv))
  hom_inv_id := by
    rw [d.tensor_map_comp, f.hom_inv_id, g.hom_inv_id, d.tensor_map_id]
  inv_hom_id := by
    rw [d.tensor_map_comp, f.inv_hom_id, g.inv_hom_id, d.tensor_map_id]

section TensorInverse

variable {L N : DerivedCategory (ModuleCat.{v₁} R)}

/-- **Cancelling a tensor inverse.** An isomorphism `L ⊗ᴸ N ≅ 1` makes `(X ⊗ᴸ L) ⊗ᴸ N`
isomorphic to `X`, by associativity, the isomorphism, the symmetry and the left unitor. -/
def tensorCancelIso (e : d.tensor.obj (L, N) ≅ one) (X : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.obj (d.tensor.obj (X, L), N) ≅ X :=
  d.tensorAssoc X L N ≪≫ tensorIso d (Iso.refl X) e ≪≫ d.tensorSwap X one ≪≫ lam X

/-- `Dualizing.tensorCancelIso` is natural: only naturality of the associator, of the symmetry
and of the unitor enters. -/
theorem tensorCancelIso_naturality (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (e : d.tensor.obj (L, N) ≅ one) {X Y : DerivedCategory (ModuleCat.{v₁} R)} (f : X ⟶ Y) :
    d.tensor.map (show (d.tensor.obj (X, L), N) ⟶ (d.tensor.obj (Y, L), N) from
        (d.tensor.map (show (X, L) ⟶ (Y, L) from (f, 𝟙 L)), 𝟙 N)) ≫
      (tensorCancelIso d one lam e Y).hom =
      (tensorCancelIso d one lam e X).hom ≫ f := by
  have hsplit : d.tensor.map (show (X, d.tensor.obj (L, N)) ⟶ (Y, one) from (f, e.hom)) =
      d.tensor.map (show (X, d.tensor.obj (L, N)) ⟶ (X, one) from (𝟙 X, e.hom)) ≫
        d.tensor.map (show (X, one) ⟶ (Y, one) from (f, 𝟙 one)) := by
    rw [d.tensor_map_comp, Category.id_comp, Category.comp_id]
  dsimp only [tensorCancelIso, tensorIso, Iso.trans_hom, Iso.refl_hom]
  simp only [Category.assoc]
  rw [d.tensorAssoc_naturality_assoc, d.tensor_map_id, d.tensor_map_comp_assoc,
    Category.comp_id, Category.id_comp, hsplit, Category.assoc,
    d.tensorSwap_naturality_assoc, hlam f]

/-- **Tensoring with an object that has a tensor inverse is faithful.** -/
theorem injective_tensorMap_right (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (e : d.tensor.obj (L, N) ≅ one) (X Y : DerivedCategory (ModuleCat.{v₁} R)) :
    Function.Injective
      (fun f : X ⟶ Y => d.tensor.map (show (X, L) ⟶ (Y, L) from (f, 𝟙 L))) := by
  intro f g hfg
  have hf := tensorCancelIso_naturality d one lam hlam e f
  have hg := tensorCancelIso_naturality d one lam hlam e g
  have key : d.tensor.map (show (d.tensor.obj (X, L), N) ⟶ (d.tensor.obj (Y, L), N) from
        (d.tensor.map (show (X, L) ⟶ (Y, L) from (f, 𝟙 L)), 𝟙 N)) =
      d.tensor.map (show (d.tensor.obj (X, L), N) ⟶ (d.tensor.obj (Y, L), N) from
        (d.tensor.map (show (X, L) ⟶ (Y, L) from (g, 𝟙 L)), 𝟙 N)) :=
    congrArg (fun m : d.tensor.obj (X, L) ⟶ d.tensor.obj (Y, L) =>
      d.tensor.map (show (d.tensor.obj (X, L), N) ⟶ (d.tensor.obj (Y, L), N) from (m, 𝟙 N))) hfg
  rw [key, hg] at hf
  exact ((Iso.cancel_iso_hom_left (tensorCancelIso d one lam e X) g f).1 hf).symm

/-- **Tensoring with an object that has a two-sided tensor inverse is fully faithful**: it is a
bijection on each morphism set. -/
theorem bijective_tensorMap_right (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (e : d.tensor.obj (L, N) ≅ one) (e' : d.tensor.obj (N, L) ≅ one)
    (X Y : DerivedCategory (ModuleCat.{v₁} R)) :
    Function.Bijective
      (fun f : X ⟶ Y => d.tensor.map (show (X, L) ⟶ (Y, L) from (f, 𝟙 L))) := by
  refine ⟨injective_tensorMap_right d one lam hlam e X Y, fun h => ?_⟩
  set m := (tensorCancelIso d one lam e X).inv ≫
    d.tensor.map (show (d.tensor.obj (X, L), N) ⟶ (d.tensor.obj (Y, L), N) from (h, 𝟙 N)) ≫
      (tensorCancelIso d one lam e Y).hom with hm
  refine ⟨m, injective_tensorMap_right d one lam hlam e' _ _ ?_⟩
  refine (Iso.cancel_iso_hom_right _ _ (tensorCancelIso d one lam e Y)).1 ?_
  simpa only [hm, Iso.hom_inv_id_assoc] using tensorCancelIso_naturality d one lam hlam e m

end TensorInverse

/-- **From a tensor inverse to invertibility of the evaluation map at every object.** If `ω` has
a tensor inverse `ω'`, then the evaluation map `RHom(ω, K) ⊗ᴸ ω ⟶ K` is an isomorphism for every
object `K`: no perfection, coherence or boundedness hypothesis is involved. This is the counit
of the adjunction between `- ⊗ᴸ ω` and `RHom(ω, -)`, and a tensor inverse makes `- ⊗ᴸ ω` an
equivalence. -/
theorem isIso_evaluation_of_tensor_iso_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (ω ω' : DerivedCategory (ModuleCat.{v₁} R)) (e : d.tensor.obj (ω, ω') ≅ one)
    (K : DerivedCategory (ModuleCat.{v₁} R)) :
    IsIso (d.evaluation ω K) := by
  have e' : d.tensor.obj (ω', ω) ≅ one := d.tensorSwap ω' ω ≪≫ e
  refine isIso_of_yoneda_map_bijective _ fun T => ?_
  have i : d.tensor.obj (d.tensor.obj (T, ω'), ω) ≅ T := tensorCancelIso d one lam e' T
  set X := d.tensor.obj (T, ω')
  have hb := bijective_tensorMap_right d one lam hlam e e' X (d.hom.obj (Opposite.op ω, K))
  have hev : Function.Bijective
      (fun x : d.tensor.obj (X, ω) ⟶ d.tensor.obj (d.hom.obj (Opposite.op ω, K), ω) =>
        x ≫ d.evaluation ω K) := by
    refine (Function.Bijective.of_comp_iff _ hb).1 ?_
    convert (d.homEquiv X ω K).bijective using 1
    funext a
    exact (homEquiv_eq_tensorMap_comp_evaluation d X ω K a).symm
  constructor
  · intro x₁ x₂ hx
    refine (Iso.cancel_iso_hom_left i x₁ x₂).1 (hev.1 ?_)
    simpa only [Category.assoc] using congrArg (fun z => i.hom ≫ z) hx
  · intro y
    obtain ⟨x, hxy⟩ := hev.2 (i.hom ≫ y)
    refine ⟨i.inv ≫ x, ?_⟩
    dsimp only at hxy ⊢
    rw [Category.assoc, hxy, Iso.inv_hom_id_assoc]

/-- **From invertibility of the evaluation map at the tensor unit to a tensor inverse.** If the
evaluation map `RHom(ω, 1) ⊗ᴸ ω ⟶ 1` is an isomorphism then `RHom(ω, 1)` is a tensor inverse of
`ω`. -/
theorem nonempty_tensor_iso_one_of_isIso_evaluation (ω : DerivedCategory (ModuleCat.{v₁} R))
    (h : IsIso (d.evaluation ω one)) :
    Nonempty (d.tensor.obj (ω, d.hom.obj (Opposite.op ω, one)) ≅ one) :=
  ⟨d.tensorSwap ω (d.hom.obj (Opposite.op ω, one)) ≪≫ @asIso _ _ _ _ _ h⟩

/-- Invertibility of the evaluation map at its target transports along an isomorphism of that
target: the evaluation maps at `K` and at `K'` differ by the derived Hom of an isomorphism and
by that isomorphism. -/
theorem isIso_evaluation_of_iso_right (ω : DerivedCategory (ModuleCat.{v₁} R))
    {K K' : DerivedCategory (ModuleCat.{v₁} R)} (f : K ≅ K')
    (h : IsIso (d.evaluation ω K)) :
    IsIso (d.evaluation ω K') := by
  have hpair : IsIso (show (Opposite.op ω, K) ⟶ (Opposite.op ω, K') from
      (𝟙 (Opposite.op ω), f.hom)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have htensor := DerivedHomAdjunction.isIso_tensor_map (d := d)
    (d.hom.map (show (Opposite.op ω, K) ⟶ (Opposite.op ω, K') from
      (𝟙 (Opposite.op ω), f.hom))) (𝟙 ω)
  have hcomp : IsIso (d.evaluation ω K ≫ f.hom) := inferInstance
  rw [← d.evaluation_naturality_right f.hom] at hcomp
  exact (isIso_comp_left_iff _ _).1 hcomp

/-- **The conversion step of [stacks 0E2D].** If derived Hom from `ω` into `K` is the tensor
unit and the evaluation map at `K` is invertible, then `ω ≅ K`. This is the implication the
uniqueness argument for relative dualizing complexes runs on, and the conclusion is
[stacks 0E2D]. Only the left unitor at `ω` is used, which is `lam ω` for any left unitor `lam`.

Both hypotheses are, for two relative dualizing complexes, of the strength of the tag itself, and
neither is supplied by the defining condition of [stacks 0E2C]: that condition is an isomorphism
in `D(A ⊗[R] A)` about the derived base change of a *single* complex, and nothing in the library
turns it into a statement about `RHom_A` of two of them. Given `i`, the evaluation map at `K` is
the composite `ω ≅ 1 ⊗ᴸ ω ⟶ K` that `i` names, so invertibility of `ev_K` *is* the assertion that
that particular map `ω ⟶ K` is an isomorphism. The content of [stacks 0E2D] is therefore not
redistributed by this lemma; it is isolated in its hypotheses. -/
theorem nonempty_iso_of_isIso_evaluation (ω K : DerivedCategory (ModuleCat.{v₁} R))
    (u : d.tensor.obj (one, ω) ≅ ω)
    (i : Nonempty (d.hom.obj (Opposite.op ω, K) ≅ one)) (h : IsIso (d.evaluation ω K)) :
    Nonempty (ω ≅ K) :=
  ⟨u.symm ≪≫ tensorIso d i.some.symm (Iso.refl ω) ≪≫ @asIso _ _ _ _ _ h⟩

/-- **The evaluation map is invertible everywhere exactly when `ω` is tensor-invertible.** -/
theorem isIso_evaluation_iff_nonempty_tensor_iso_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (ω : DerivedCategory (ModuleCat.{v₁} R)) :
    (∀ K : DerivedCategory (ModuleCat.{v₁} R), IsIso (d.evaluation ω K)) ↔
      ∃ ω' : DerivedCategory (ModuleCat.{v₁} R), Nonempty (d.tensor.obj (ω, ω') ≅ one) := by
  refine ⟨fun h => ⟨_, nonempty_tensor_iso_one_of_isIso_evaluation d one ω (h one)⟩, ?_⟩
  rintro ⟨ω', ⟨e⟩⟩ K
  exact isIso_evaluation_of_tensor_iso_one d one lam hlam ω ω' e K

/-- **One object decides all of them.** The evaluation map at `ω` is invertible at every object
as soon as it is invertible at the tensor unit. -/
theorem isIso_evaluation_iff_isIso_evaluation_one
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (ω : DerivedCategory (ModuleCat.{v₁} R)) :
    (∀ K : DerivedCategory (ModuleCat.{v₁} R), IsIso (d.evaluation ω K)) ↔
      IsIso (d.evaluation ω one) := by
  refine ⟨fun h => h one, fun h K => ?_⟩
  obtain ⟨e⟩ := nonempty_tensor_iso_one_of_isIso_evaluation d one ω h
  exact isIso_evaluation_of_tensor_iso_one d one lam hlam ω _ e K

/-- **The evaluation map at `K = ω` itself.** It is invertible as soon as the derived homothety
`1 ⟶ RHom(ω, ω)` is, which for a relative dualizing complex is [stacks 0E2G]. This is the single
instance of the evaluation map that the uniqueness argument of [stacks 0E2D] needs, and unlike
the statement for all `K` it does not force `ω` to be tensor-invertible. -/
alias isIso_evaluation_self_of_isIso_derivedHomothety := isIso_evaluation_of_isIso_derivedHomothety

end Abstract

/-! ### The adjunction of [stacks 0A63] over a ring -/

section OverRing

attribute [local instance] HasDerivedCategory.standard

universe u v

variable (A : Type u) [CommRing A]

/-- **The evaluation map of [stacks 0A63] is invertible everywhere exactly when `ω` is
tensor-invertible.** This is `Dualizing.isIso_evaluation_iff_nonempty_tensor_iso_one` at the
adjunction over a ring. -/
theorem isIso_evaluation_overRing_iff_nonempty_tensor_iso_derivedTensorUnit
    (ω : DerivedCategory (ModuleCat.{max u v} A)) :
    (∀ K : DerivedCategory (ModuleCat.{max u v} A),
        IsIso ((derivedHomAdjunctionOverRing.{u, v} A).evaluation ω K)) ↔
      ∃ ω' : DerivedCategory (ModuleCat.{max u v} A),
        Nonempty ((derivedHomAdjunctionOverRing.{u, v} A).tensor.obj (ω, ω') ≅
          derivedTensorUnit.{u, v} A) :=
  isIso_evaluation_iff_nonempty_tensor_iso_one _ _ _ (derivedTensorUnitLeft_natural.{u, v} A) ω

/-- **One object decides all of them**, for the adjunction of [stacks 0A63] over a ring: the
evaluation map at `ω` is invertible at every object of `D(A)` as soon as it is invertible at the
tensor unit. -/
theorem isIso_evaluation_overRing_iff_isIso_evaluation_derivedTensorUnit
    (ω : DerivedCategory (ModuleCat.{max u v} A)) :
    (∀ K : DerivedCategory (ModuleCat.{max u v} A),
        IsIso ((derivedHomAdjunctionOverRing.{u, v} A).evaluation ω K)) ↔
      IsIso ((derivedHomAdjunctionOverRing.{u, v} A).evaluation ω (derivedTensorUnit.{u, v} A)) :=
  isIso_evaluation_iff_isIso_evaluation_one _ _ _ (derivedTensorUnitLeft_natural.{u, v} A) ω

/-- **The evaluation map of [stacks 0A63] at `K = ω` itself**, invertible as soon as the derived
homothety `A ⟶ RHom_A(ω, ω)` is. -/
theorem isIso_evaluation_overRing_self_of_isIso_derivedHomothety
    (ω : DerivedCategory (ModuleCat.{max u v} A))
    (h : IsIso (derivedHomothety (derivedHomAdjunctionOverRing.{u, v} A)
      (derivedTensorUnit.{u, v} A) (derivedTensorUnitLeft.{u, v} A) ω)) :
    IsIso ((derivedHomAdjunctionOverRing.{u, v} A).evaluation ω ω) :=
  isIso_evaluation_self_of_isIso_derivedHomothety _ _ _ ω h

end OverRing

end

end Dualizing

end
