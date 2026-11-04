module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.Algebra.Module.Reflexive.PlaneSubalgebra
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized

/-!
# Serre's condition for the extremal cohomology of a dual

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, let
`d = dim(A)` and let `ω_A = H^{-d}(ω_A^•)` be its canonical module.  This file proves that

`Ext^n_A(X, ω_A^•)`

satisfies Serre's condition `(S₂)` whenever `X` lies in `D^{≤ a}(A)` with finite cohomology in
degree `a` and `n + a ≤ -d`, that is, at and below the extremal degree at which the Ext group is
read off cohomology rather than computed.

## Main results

* `Dualizing.extremalExtLinearEquiv` — [Stacks, Tag 06XS] as an `A`-linear equivalence:
  at `n + a = a' ≤ b`, with `X` in `D^{≤ a}` and `Y` in `D^{≥ b}`,
  `Ext^n_A(X, Y) ≅ Hom_A(H^a(X), H^{a'}(Y))`.
* `Dualizing.isGE_of_isNormalizedDualizingComplex` — a normalized dualizing complex lies in
  `D^{≥ -d}(A)`, which is [Stacks, Tag 0A7U] in the form the Ext identification needs.
* `Dualizing.propertySkModule_of_subsingleton` — a zero module satisfies every `(Sₖ)`.
* `Dualizing.propertySkModule_linearMap_canonicalModule` — `Hom_A(M, ω_A)` satisfies `(S₂)` for
  every finite `M`.
* `Dualizing.propertySkModule_of_linearEquiv_extremalExt` — any module identified with
  `Ext^n_A(X, ω_A^•)` at `n + a ≤ -d` satisfies `(S₂)`.
* `Dualizing.propertySkModule_of_linearEquiv_extremalExt_upperShriek` — the same with the
  normalized dualizing complex at a maximal ideal supplied by [Stacks, Tag 0E9N], which is the
  `(S₂)` clause of [Stacks, Tag 0E9R] with only the duality formula left as a hypothesis.

## Relation to the source

These are the last two steps of the proof of [Stacks, Tag 0E9R], the ones that produce its
`(S₂)` clause once the duality formula has identified `H^{-r}(ω^•_{A/R})_𝔪` with
`Ext^{-r}_A(ω_R[d] ⊗_R^L A, ω_A^•)`: Serre's condition for the canonical module, which is
[Stacks, Tag 0AWE] part (2), available here as
`Dualizing.propertySkModule_canonicalModule`, and its inheritance by a module of
homomorphisms, which is [Stacks, Tag 0AV6] — More on Algebra, Lemma 15.24.11 of the source —
available here as `propertySk_linearMap_one_two_and_isTorsionFree`.  What is added is the edge
identification of the extremal Ext with a module of homomorphisms on cohomology, carried out
`A`-linearly so that Serre's condition can be transported across it.

Nothing here is specific to a relative dualizing complex: the statements are about an arbitrary
`X` of `D^{≤ a}(A)`, so they apply to `ω^•_{A/R}` through whatever identification of it with such
an `Ext` is available.  The tag's `(S₂)` clause for a general finite type `φ` is proved, by a
route that needs no dualizing complex on `R`, as
`Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay`.

For a *surjective* `φ` there is a second, elementary engine which needs no dualizing complex on
`R` at all: `propertySkModule_two_of_linearEquiv_dual` in
`StacksFrontier.RingTheory.Serre.Surjection`.  There `ω^•_{A/R} = RHom_R(A, R)`, so the clause
reduces to `(S₂)` of the `R`-dual `Hom_R(A, R)` — which `R` hands over by [Stacks, Tag 0AV6] as
soon as it satisfies `(S₂)` itself — carried across the surjection by
`propertySkModule_of_surjective_algebraMap`.  That engine's hypothesis, the `R`-linear
identification of `H^0(ω^•_{A/R})` with `Hom_R(A, R)`, is discharged in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerreSurjective`, where the
clause is therefore proved for a surjective `φ`.

## References

* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0AV6](https://stacks.math.columbia.edu/tag/0AV6)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **[Stacks, Tag 06XS] as an `A`-linear equivalence.** Let `X` lie in `D^{≤ a}(A)` and let `Y`
lie in `D^{≥ b}(A)`.  If `n + a = a'` and `a' ≤ b`, then taking homology in degree `a` identifies

`Ext^n_A(X, Y) ≅ Hom_A(H^a(X), H^{a'}(Y))` .

The underlying bijection is
`DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE`; what is added here is that
it is a map of `A`-modules, which is what a statement about depth or about Serre's condition for
the Ext group needs. -/
noncomputable def extremalExtLinearEquiv {A : Type u} [CommRing A]
    (X Y : DerivedCategory (ModuleCat.{u} A)) (a b n a' : ℤ) [X.IsLE a] [Y.IsGE b]
    (ha' : n + a = a') (hab : a' ≤ b) :
    DerivedCategory.Ext X Y n ≃ₗ[A]
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj X) →ₗ[A]
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a').obj Y)) :=
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let f : DerivedCategory.Ext X Y n →ₗ[A]
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj X) ⟶
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a').obj Y)) :=
    { toFun := fun g => (H.shiftMap g a a' ha' :
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj X ⟶
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) a').obj Y)
      map_add' := fun g h => by
        change ((H.shift a).map (g + h) ≫ (H.shiftIso n a a' ha').hom.app Y) =
          ((H.shift a).map g ≫ (H.shiftIso n a a' ha').hom.app Y) +
            ((H.shift a).map h ≫ (H.shiftIso n a a' ha').hom.app Y)
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := fun c g => by
        let : Functor.Linear A (H.shift a) := by
          rw [DerivedCategory.shift_homologyFunctor]
          infer_instance
        change ((H.shift a).map (c • g) ≫ (H.shiftIso n a a' ha').hom.app Y) =
          c • ((H.shift a).map g ≫ (H.shiftIso n a a' ha').hom.app Y)
        rw [Functor.map_smul, Linear.smul_comp] }
  (LinearEquiv.ofBijective f
    (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      X Y a b n a' ha' hab)).trans ModuleCat.homLinearEquiv

/-- **[Stacks, Tag 0A7U] as a bound in the canonical t-structure.** A normalized dualizing
complex over a Noetherian local ring of dimension `d` lies in `D^{≥ -d}(A)`. -/
theorem isGE_of_isNormalizedDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) : K.IsGE (-(d : ℤ)) :=
  (DerivedCategory.isGE_iff K (-(d : ℤ))).2 fun i hi =>
    isZero_homology_of_lt_neg_ringKrullDim K hK d hd i hi

/-- **Serre's condition `(S₂)` for a module of homomorphisms into the canonical module.** Let `A`
be a Noetherian local ring with a normalized dualizing complex `K`, let `d = dim(A)` and let
`ω_A = H^{-d}(K)` be its canonical module.  Then `Hom_A(M, ω_A)` satisfies `(S₂)` for every
finite `A`-module `M`.

The canonical module satisfies `(S₂)` by [Stacks, Tag 0AWE] part (2), and `(S₂)` passes to a
module of homomorphisms into it by [Stacks, Tag 0AV6]. -/
theorem propertySkModule_linearMap_canonicalModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    let d := ((ringKrullDim A).unbotD 0).toNat
    let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K
    letI : Module.Finite A ω := hK.1.finiteCohomology (-(d : ℤ))
    PropertySkModule A (M →ₗ[A] ω) 2 := by
  dsimp only
  let : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
        (-(((ringKrullDim A).unbotD 0).toNat : ℤ))).obj K) :=
    hK.1.finiteCohomology _
  exact (propertySk_linearMap_one_two_and_isTorsionFree (R := A) (M := M)
    (N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A)
      (-(((ringKrullDim A).unbotD 0).toNat : ℤ))).obj K)).2.1
    (propertySkModule_canonicalModule K hK)

/-- A module with at most one element satisfies every Serre condition: its support is empty, so
the dimension bound to be met is `0`. -/
theorem propertySkModule_of_subsingleton {R : Type*} [CommRing R] [IsNoetherianRing R]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] [Subsingleton N] (k : ℕ) :
    PropertySkModule R N k := by
  intro q _
  have hsub : Subsingleton (LocalizedModule.AtPrime q N) := by
    rw [LocalizedModule.subsingleton_iff]
    exact fun m => ⟨1, one_mem _, Subsingleton.elim _ _⟩
  have hbot : moduleSupportDim (Localization.AtPrime q) (LocalizedModule.AtPrime q N) = ⊥ := by
    unfold moduleSupportDim
    rw [topologicalKrullDim_eq_bot_iff_isEmpty]
    exact Set.isEmpty_coe_sort.mpr (Module.support_eq_empty_iff.mpr hsub)
  rw [hbot]
  simp

/-- **Serre's condition `(S₂)` for `Hom_A(M, H^j(K))` at and below the normalizing degree.** For
`j = -d` this is `Hom_A(M, ω_A)` and the statement is
`Dualizing.propertySkModule_linearMap_canonicalModule`; for `j < -d` the cohomology vanishes by
[Stacks, Tag 0A7U] and the module is zero. -/
private theorem propertySkModule_linearMap_homology_of_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (j : ℤ) (hj : j ≤ -(d : ℤ))
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K)] :
    PropertySkModule A
      (M →ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K)) 2 := by
  rcases eq_or_lt_of_le hj with heq | hlt
  · subst heq
    have hdim : ((ringKrullDim A).unbotD 0).toNat = d := by rw [hd]; simp
    have h := propertySkModule_linearMap_canonicalModule K hK M
    rw [hdim] at h
    exact h
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_homology_of_lt_neg_ringKrullDim K hK d hd j hlt)
    have : Subsingleton
        (M →ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K)) :=
      ⟨fun g h => LinearMap.ext fun x => Subsingleton.elim _ _⟩
    exact propertySkModule_of_subsingleton _ 2

/-- **Serre's condition `(S₂)` for the extremal `Ext` into a normalized dualizing complex.** Let
`A` be a Noetherian local ring of dimension `d` with a normalized dualizing complex `K`, let `X`
lie in `D^{≤ a}(A)` with `H^a(X)` finite, and let `n + a ≤ -d`.  Then any `A`-module identified
with `Ext^n_A(X, K)` satisfies `(S₂)`.

At such a degree the Ext group is `Hom_A(H^a(X), H^{n+a}(K))` by [Stacks, Tag 06XS], since `K`
lies in `D^{≥ -d}(A)` by [Stacks, Tag 0A7U]; and that module of homomorphisms satisfies `(S₂)`
by `Dualizing.propertySkModule_linearMap_canonicalModule` when `n + a = -d`, and is zero
otherwise.  The inequality rather than the equality is what the source's own bound supplies: it
proves `dim(A_𝔪) ≤ d + r` and reads the Ext group in degree `-r` off `X` in `D^{≤ -d}`, so
`n + a = -d - r ≤ -dim(A_𝔪)` with no claim of equality.

The identification is taken as the hypothesis `e` rather than the module being spelled as the Ext
group itself, because a consumer — [Stacks, Tag 0E9R], whose `(S₂)` clause this is the engine of
— arrives with a concrete module and an isomorphism onto such an `Ext`. -/
theorem propertySkModule_of_linearEquiv_extremalExt {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (X : DerivedCategory (ModuleCat.{u} A)) (a n : ℤ) [X.IsLE a]
    (hX : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj X))
    (han : n + a ≤ -(d : ℤ))
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (e : N ≃ₗ[A] DerivedCategory.Ext X K n) :
    PropertySkModule A N 2 := by
  have : K.IsGE (-(d : ℤ)) := isGE_of_isNormalizedDualizingComplex K hK d hd
  have : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + a)).obj K) :=
    hK.1.finiteCohomology _
  let eExt := extremalExtLinearEquiv X K a (-(d : ℤ)) n (n + a) rfl han
  have : Module.Finite A (DerivedCategory.Ext X K n) := Module.Finite.equiv eExt.symm
  exact propertySkModule_of_linearEquiv e 2
    (propertySkModule_of_linearEquiv eExt 2
      (propertySkModule_linearMap_homology_of_le K hK d hd _ (n + a) han))

/-- **The `(S₂)` clause of [Stacks, Tag 0E9R] at a maximal ideal, granted the duality formula.**
Let `R` be a Noetherian local ring with a normalized dualizing complex `ω_R^•`, let `φ : R → A`
be of finite type presented by `p`, and let `𝔪 ⊆ A` be a maximal ideal lying over the maximal
ideal of `R`, with `dim(A_𝔪) = d`.  Let `X` lie in `D^{≤ a}(A_𝔪)` with `H^a(X)` finite and let
`n + a = -d`.  Then any `A_𝔪`-module identified with `Ext^n_{A_𝔪}(X, (φ^!ω_R^•)_𝔪)` satisfies
`(S₂)`.

This is the `(S₂)` clause of the source with one hypothesis left standing: the identification
`e`, which is the duality formula [Stacks, Tag 0E9L] in the shape
`ω^•_{A/R} = RHom_A(ω_R[d] ⊗_R^L A, ω_A^•)` read on cohomology in degree `-r` and localized at
`𝔪`, with `X = ω_R[d] ⊗_R^L A_𝔪` — which lies in `D^{≤ -d}(A_𝔪)` — and `n = -r`, `a = -d`,
so that `n + a = -d - r`, which the bound `dim(A_𝔪) ≤ d + r` of the source's dimension formula
places at or below the extremal degree `-dim(A_𝔪)`.

What the source needs beyond `e` is discharged here from the library: that `(φ^!ω_R^•)_𝔪` is a
*normalized* dualizing complex for `A_𝔪` is [Stacks, Tag 0E9N], proved in full as
`Dualizing.PolynomialPresentation.upperShriekFunctor_localization_isNormalizedDualizingComplex`;
its concentration in degrees `≥ -dim(A_𝔪)` is [Stacks, Tag 0A7U]; Serre's condition for its
canonical module is [Stacks, Tag 0AWE] part (2); and the passage to a module of homomorphisms is
[Stacks, Tag 0AV6].  This is not the tag: `e` is a hypothesis the source does not
have, because what `e` is is Tag 0E9L *localized at `𝔪`*.  The unlocalized general case of
Tag 0E9L is proved unconditionally as
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom`; the
passage to `A_𝔪` is the base change of [Stacks, Tag 0BZV], which is conditional here. -/
theorem propertySkModule_of_linearEquiv_extremalExt_upperShriek
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [IsLocalRing R] {f : R →+* A} (p : PolynomialPresentation f)
    (m : Ideal A) [m.IsMaximal] (hlies : m.comap f = IsLocalRing.maximalIdeal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (d : ℕ) (hd : ringKrullDim (Localization.AtPrime m) = (d : WithBot ℕ∞))
    (X : DerivedCategory (ModuleCat.{u} (Localization.AtPrime m))) (a n : ℤ) [X.IsLE a]
    (hX : Module.Finite (Localization.AtPrime m)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime m)) a).obj X))
    (han : n + a ≤ -(d : ℤ))
    {N : Type u} [AddCommGroup N] [Module (Localization.AtPrime m) N]
    [Module.Finite (Localization.AtPrime m) N]
    (e : N ≃ₗ[Localization.AtPrime m] DerivedCategory.Ext X
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime m))).obj (p.upperShriekFunctor.{u, u}.obj K)) n) :
    PropertySkModule (Localization.AtPrime m) N 2 :=
  propertySkModule_of_linearEquiv_extremalExt _
    (p.upperShriekFunctor_localization_isNormalizedDualizingComplex m hlies K hK) d hd
    X a n hX han e

end Dualizing

end
