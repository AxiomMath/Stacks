module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation

/-!
# Pseudo-coherence of `p_*𝒪` along a closed immersion of affine spaces

The proof of Stacks 09VC reduces the comparison of two closed immersions of `X` into affine
spaces over `S` to transporting `m`-pseudo-coherence along a single closed immersion
`p : 𝔸ⁿ_S ⟶ 𝔸ᴺ_S` over `S`, and that transport is Stacks 09VA. Stacks 09VA has a side condition:
`p_*𝒪_{𝔸ⁿ_S}` must be a pseudo-coherent `𝒪_{𝔸ᴺ_S}`-module. This file supplies the algebraic
content of that side condition and records the form of the reduction in which the side condition
is available.

A closed immersion `p : 𝔸ⁿ_S ⟶ 𝔸ᴺ_S` over an affine `S = Spec R` is a surjection of `R`-algebras
`α : R[x_1, …, x_N] ↠ R[y_1, …, y_n]`, that is, a polynomial presentation of `R[y_1, …, y_n]`.
The first half of this file proves that `R[y_1, …, y_n]` is a pseudo-coherent module over the
source of *every* such presentation: it is so over the identity presentation, being free of rank
one there, and Stacks 065H makes the property independent of the presentation. Stacks 065H in
turn rests on Stacks 065G, whose proof is the Koszul argument — the exact sequence
`0 → R[x] → R[x] → R → 0` — carried out in `StacksDraft.Homology.PseudoCoherent.Relative`. So the
regular sequence of coordinates cutting out a closed immersion of affine spaces is already
accounted for, one variable at a time, in that algebraic argument.

## Main results

* `PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self` and
  `PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self`: a polynomial algebra in
  finitely many variables is pseudo-coherent, relative to its base ring, as a module over itself.
* `PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective`: the same statement
  unfolded at one presentation — for a surjection of `R`-algebras
  `α : R[x_1, …, x_N] ↠ R[y_1, …, y_n]`, the target is an `m`-pseudo-coherent module over the
  source, for every `m`. This is the algebraic form of pseudo-coherence of `p_*𝒪_{𝔸ⁿ_S}`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport_fin`:
  **Stacks 09VC assuming Stacks 09VA**, with the transport hypothesis asked for only at affine
  spaces of finite dimension over `S`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport` asks for
transport along a closed immersion `p : 𝔸^ι_S ⟶ 𝔸^κ_S` over `S` for *arbitrary* index types
`ι κ : Type u`, and that hypothesis cannot be satisfied: Stacks 09VA does not apply to a closed
immersion of affine spaces of infinite dimension, and its conclusion genuinely fails there. For
`R` a field, `ι` empty and `κ` countable, the zero section `p : S ⟶ 𝔸^ℕ_S` is a closed immersion
over `S` whose ideal `(x_0, x_1, …) ⊆ R[x_0, x_1, …]` is not finitely generated, nor is it
finitely generated after inverting any `f` with `f(0) ≠ 0`; so `p_*𝒪_S` is not a finitely
presented module on any neighbourhood of the origin, while `𝒪_S` placed in degree `m + 1` on
`𝔸^∅_S ≅ S` is strictly perfect and hence `m`-pseudo-coherent. A strictly perfect complex with no
cohomology above degree `m + 1` has finitely presented cohomology there, so the right-hand side
of the transport equivalence fails for that object and that `m`. The hypothesis is therefore
contradictory for every `m`, which makes the conclusion of that lemma unusable.

The statement below restricts the transport hypothesis to the index types `ULift (Fin a)`, which
are the only ones at which the proof applies it — `AffineSpace.exists_isClosedImmersion_fin_add`
produces closed immersions of `Fin`-indexed affine spaces. Restricting a hypothesis strengthens
the lemma, and this restriction makes the hypothesis true: at a finite index type the side
condition of Stacks 09VA is
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective` above, read through the
comparison between module-level pseudo-coherence on an affine scheme and pseudo-coherence of the
associated sheaf (Stacks 08E7). That comparison is not part of this library, and it is the only
thing still missing between this file and a proof of Stacks 09VC: the pseudo-coherence of
`p_*𝒪` is settled algebraically here, and the transport itself is Stacks 09VA.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
* [The Stacks Project, Lemma 15.82.2 (065G)](https://stacks.math.columbia.edu/tag/065G)
* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PseudoCoherence

open StacksDraft.PseudoCoherence

universe v u

attribute [local instance] HasDerivedCategory.standard

/-- An object of `D(R)` represented by a bounded complex of finite free modules is
`m`-pseudo-coherent for every `m`: the representing isomorphism is an isomorphism on cohomology
in every degree, in particular an isomorphism above `m` and an epimorphism in degree `m`. -/
public theorem isPseudoCoherentFrom_of_isBoundedFiniteFree_iso {R : Type u} [Ring R]
    {E : CochainComplex (ModuleCat.{v} R) ℤ} {K : DerivedCategory (ModuleCat.{v} R)}
    (hE : IsBoundedFiniteFree E) (e : DerivedCategory.Q.obj E ≅ K) (m : ℤ) :
    IsPseudoCoherentFrom K m :=
  ⟨E, hE, e.hom, fun _ _ => inferInstance, inferInstance⟩

/-- A finite free module placed in degree zero is `m`-pseudo-coherent for every `m`: it is its own
finite free resolution. -/
public theorem isPseudoCoherentFrom_single_of_finiteFree {R : Type u} [Ring R]
    (P : ModuleCat.{v} R) [Module.Finite R P] [Module.Free R P] (m : ℤ) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj P) m :=
  isPseudoCoherentFrom_of_isBoundedFiniteFree_iso (isBoundedFiniteFree_single P 0)
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).symm.app P) m

/-- **A polynomial algebra in finitely many variables is relatively `m`-pseudo-coherent as a
module over itself**, for every `m`.

Unfolded, this says that for every surjection of `R`-algebras
`α : R[x_1, …, x_N] ↠ R[y_1, …, y_n]` the target is an `m`-pseudo-coherent module over the
source; `PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective` is that reading.
Note that no such statement holds for a general finite-type `R`-algebra `A` in place of
`R[y_1, …, y_n]`: `A` is relatively `0`-pseudo-coherent over `R`, being finite over itself, but
in negative degrees relative pseudo-coherence of `A` is a real condition on `R → A`.

The proof is Stacks 065H: the property holds for the identity presentation, where restriction of
scalars is the identity and `R[y_1, …, y_n]` is free of rank one over itself, hence it holds for
every presentation. -/
public theorem isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self (R : Type u) [CommRing R]
    (n : ℕ) (m : ℤ) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R) m := by
  set A := MvPolynomial (Fin n) R
  have h := isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} (R := R) (A := A)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) m
  intro N α hα
  refine h.1.mp ⟨n, AlgHom.id R A, fun x => ⟨x, rfl⟩, ?_⟩ N α hα
  exact IsPseudoCoherentFrom.ofIso (isPseudoCoherentFrom_single_of_finiteFree _ m)
    (((ModuleCat.restrictScalars.{u} (AlgHom.id R A).toRingHom).mapDerivedCategorySingleFunctor
      0).app (ModuleCat.of A A)).symm

/-- **A polynomial algebra in finitely many variables is pseudo-coherent relative to its base ring
as a module over itself.** This is
`PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self` in every degree. -/
public theorem isModuleRelativelyPseudoCoherent_mvPolynomial_self (R : Type u) [CommRing R]
    (n : ℕ) :
    IsModuleRelativelyPseudoCoherent (R := R) (A := MvPolynomial (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  fun m => isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self R n m

/-- **The algebraic form of pseudo-coherence of `p_*𝒪` along a closed immersion of affine
spaces.** For a surjection of `R`-algebras `α : R[x_1, …, x_N] ↠ R[y_1, …, y_n]` — equivalently,
for a closed immersion `𝔸ⁿ_S ⟶ 𝔸ᴺ_S` over an affine base `S = Spec R` — the target
`R[y_1, …, y_n]`, viewed as a module over `R[x_1, …, x_N]` through `α`, is `m`-pseudo-coherent
for every `m`.

This is the side condition of Stacks 09VA for such a closed immersion, at the level of modules
over the rings of global sections. Note that surjectivity of `α` is the only hypothesis: the
coordinates of `p` are arbitrary polynomials. -/
public theorem isModulePseudoCoherentFrom_mvPolynomial_of_surjective {R : Type u} [CommRing R]
    {n N : ℕ} (α : MvPolynomial (Fin N) R →ₐ[R] MvPolynomial (Fin n) R)
    (hα : Function.Surjective α) (m : ℤ) :
    @IsModulePseudoCoherentFrom (MvPolynomial (Fin N) R) _ _ (MvPolynomial (Fin n) R) _
      (Module.compHom _ α.toRingHom) m := by
  set A := MvPolynomial (Fin n) R
  let _ : Module (MvPolynomial (Fin N) R) A := Module.compHom A α.toRingHom
  exact IsPseudoCoherentFrom.ofIso
    (isModuleRelativelyPseudoCoherentFrom_mvPolynomial_self R n m N α hα)
    (((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A))

end PseudoCoherence

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 09VC, granted Stacks 09VA for affine spaces of finite dimension.** Let `f : X ⟶ S` be
a morphism of affine schemes locally of finite type and let `E` be an object of the derived
category of `𝒪_X`-modules. If `m`-pseudo-coherence of the derived pushforward transports along
closed immersions of *finite-dimensional* affine spaces over `S`, then `m`-pseudo-coherence of
the derived pushforward of `E` along *some* closed immersion of `X` into an affine space over `S`
factoring `f` is equivalent to the same along *every* such closed immersion.

This is `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport` with
the transport hypothesis asked for only at the index types `ULift (Fin a)`, which are the only
ones the proof uses, and hence a stronger statement. The restriction matters: as the
implementation notes of this file record, the transport hypothesis at an arbitrary index type is
contradictory, because Stacks 09VA fails for a closed immersion of affine spaces of infinite
dimension, whereas at a finite index type its side condition holds —
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective`.

The proof is the one in the source, and is the proof of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport`: the
implication from "every" to "some" is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall`, and for
the converse `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_fin_add` dominates two
closed immersions `i` and `j` by closed immersions `k` and `l` into a common affine space over
`S` with `i ≫ k = j ≫ l`; transporting along `k` and back along `l`, and identifying `(i ≫ k)_*E`
with `(j ≫ l)_*E`, carries the hypothesis on `i` to the conclusion on `j`. -/
public theorem isPseudoCoherentFrom_some_iff_forall_of_transport_fin
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (transport : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      p ≫ (AffineSpace.over (ULift.{u} (Fin b)) S).hom =
        (AffineSpace.over (ULift.{u} (Fin a)) S).hom →
      ∀ A : DerivedCategory (AffineSpace (ULift.{u} (Fin a)) S).Modules,
        RingedSpace.IsPseudoCoherentFrom
            (X := (AffineSpace (ULift.{u} (Fin a)) S).toRingedSpace) A m ↔
          RingedSpace.IsPseudoCoherentFrom
            (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
            ((pushforward p).mapDerivedCategory.obj A) m) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) ↔
      (∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i →
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
            IsPseudoCoherentFromAfterPushforward i E m) := by
  refine ⟨?_, exists_isPseudoCoherentFromAfterPushforward_of_forall f E m⟩
  rintro ⟨n, i, hi, hiover, hPi⟩ n' j hj hjover
  have := hi
  have := hj
  obtain ⟨k, l, hk, hl, hko, hlo, hkl⟩ :=
    AffineSpace.exists_isClosedImmersion_fin_add i hiover j hjover
  have := hk
  have := hl
  rw [isPseudoCoherentFromAfterPushforward_iff] at hPi
  rw [isPseudoCoherentFromAfterPushforward_iff]
  rw [transport k hko] at hPi
  have h₁ : RingedSpace.IsPseudoCoherentFrom
      (X := (AffineSpace (ULift.{u} (Fin (n + n'))) S).toRingedSpace)
      ((pushforward (i ≫ k)).mapDerivedCategory.obj E) m :=
    hPi.of_iso ((mapDerivedCategoryPushforwardComp i k).app E)
  have h₂ : RingedSpace.IsPseudoCoherentFrom
      (X := (AffineSpace (ULift.{u} (Fin (n + n'))) S).toRingedSpace)
      ((pushforward (j ≫ l)).mapDerivedCategory.obj E) m :=
    h₁.of_iso ((Functor.mapDerivedCategoryCongr (pushforwardCongr hkl)).app E)
  exact (transport l hlo _).2
    (h₂.of_iso ((mapDerivedCategoryPushforwardComp j l).app E).symm)

end AlgebraicGeometry.Scheme.Modules

end
