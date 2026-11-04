module

public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.Relative
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections

/-!
# Derived endomorphisms of a relative dualizing complex

Let `R → A` be a flat ring map of finite presentation and let `K` be a relative dualizing complex
for `R → A` in the sense of [stacks 0E2C], `Dualizing.IsRelativeDualizingComplex`. The canonical
map `A ⟶ RHom_A(K, K)` is the derived homothety `Dualizing.derivedHomothety` of [stacks 0A7C],
taken for the internal derived Hom of [stacks 0A63] in its standard model; [stacks 0E2G] asserts
that it is an isomorphism.

This file proves the two statements about that map which follow from the definition of a relative
dualizing complex alone: the map is injective on scalars, and its invertibility depends only on
the isomorphism class of `K`.

## Main results

* `Dualizing.isIso_derivedHomothety_iff_of_iso` — invertibility of the derived homothety is
  invariant under isomorphism of the object: the homothety at `K`, followed by the derived Hom of
  an isomorphism `K ≅ L` in both variables, is the homothety at `L`.
* `Dualizing.injective_smul_id_of_isRelativeDualizingComplex` — **scalars act injectively on a
  relative dualizing complex**: `a ↦ a • 𝟙 K` is injective `A → End_{D(A)}(K)`. This is the half
  of the degree-zero part of [stacks 0E2G] that the defining condition of [stacks 0E2C] gives on
  its own: applying the derived base change along the left coprojection and then derived Hom from
  the diagonal turns `a • 𝟙 K` into `a • 𝟙` on an object isomorphic to `A`, where scalars are
  faithful.
* `Dualizing.diagonalExtensionHomEquiv` — **the derived endomorphisms of `K`, read over
  `A ⊗[R] A` on the extension side**: `Hom_{D(A)}(M, N)` is `Hom_{D(A ⊗[R] A)}(M ⊗ᴸ_A S, N_S)`
  for `S = A ⊗[R] A`, by the adjunction between derived extension of scalars along the
  multiplication map and restriction along it, the left coprojection being a section of the
  multiplication map. At `M = N = K⟦i⟧` this is `Ext^i_A(K, K)`.
* `Dualizing.homDiagonalObjectEquivOfIsRelativeDualizingComplex` — **what [stacks 0E2C] computes**:
  `Hom_{D(A ⊗[R] A)}(M_S, K ⊗ᴸ_A S)` is `Hom_{D(A)}(M, A)`. The defining condition computes
  morphisms *out of* the diagonal into the base change of `K`, where they are the `A`-dual of `K`;
  the previous item shows the derived endomorphisms are the morphisms in the *opposite*
  direction. Nothing relates the two, and that gap is [stacks 0E2G].

## What is not here, and why

[stacks 0E2G] itself is not proved here. Its proof in the source reduces to the Noetherian case
by [stacks 02JO], identifies `K` there with `φ^!(R)` using [stacks 0E2D], [stacks 0E2E] and
[stacks 0E2F], computes `RHom_A(φ^!(R), φ^!(R)) = A` by [stacks 0BZW], and passes to a general
base by writing it as a filtered colimit of Noetherian algebras and appealing to [stacks 0DHX].

Of those inputs this library has [stacks 02JO] (`Algebra.FiniteTypeSystem.exists_flat_stage`) and
[stacks 0DHX] (`PseudoCoherence.relativelyPerfectComplexes_filteredColimit`), while [stacks 0E2D]
(`Dualizing.nonempty_iso_of_isRelativeDualizingComplex`), [stacks 0E2E] and [stacks 0E2F]
(`Dualizing.exists_isRelativeDualizingComplex`) are available only with their documented open
inputs carried. The computation of the derived endomorphisms of `φ^!(R)`, which is the
mathematical content of [stacks 0BZW] used here and is where the conclusion actually comes from,
is [stacks 0BZW] (1)(c), and that one is *not* conditional: it is
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule`, proved with
nothing carried beyond perfectness of `A` over the polynomial algebra of the presentation —
which by [stacks 068Y] is perfectness of `φ` — and for a flat `φ` of finite type over a
Noetherian base even that hypothesis is discharged, by part (2) of the same tag through
[stacks 067J]. The resulting statement,
`Dualizing.PolynomialPresentation.isIso_relativeHomothety_relativeDualizingComplex` of
`StacksFrontier.RingTheory.Dualizing.RelativeHomothety`, is [stacks 0E2G] at `φ^!(R)` with no
residue at all. A second route to (1)(c), which dispenses with perfectness instead, is
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isDualizingComplex`, for a
presentation whose polynomial algebra is its own dualizing complex, which is the case for a
regular or finite-dimensional Gorenstein base. Nothing in this file assumes any of that.

So the conclusion of [stacks 0E2G] at the *canonical* relative dualizing complex costs nothing.
What is still conditional is the tag at an *arbitrary* one, and for two reasons, neither of them
(1)(c): the identification with `φ^!(R)` is [stacks 0E2D], whose hypothesis `hdiag` is refuted in
the left/left configuration; and knowing `φ^!(R)` to be a relative dualizing complex at all is
[stacks 0E2E], which carries
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, the open input of [stacks 0E2A].

**The order of the two tags is the source's, and it is the opposite of a route to
[stacks 0E2D].** [stacks 0E2G] is proved in the source *from* [stacks 0E2D], at both of the steps
listed above: the reduction to a Noetherian base needs uniqueness to descend the complex, and in
the Noetherian case uniqueness is what identifies the given `K` with `φ^!(R)` before
[stacks 0BZW] is applied. So (1)(c) of [stacks 0BZW] does not unlock [stacks 0E2G] on its own —
only its combination with [stacks 0E2D], which is the tag one would be trying to prove — and
`Dualizing.isIso_derivedHomothety_iff_of_iso` below is exactly the transport that the missing
identification would feed. Proving [stacks 0E2G] without [stacks 0E2D] would need a route to
`End_{D(A)}(K) = A` from the defining condition of [stacks 0E2C] alone; the degree-zero half of
one direction of that is `Dualizing.injective_smul_id_of_isRelativeDualizingComplex`, and what is
missing is the surjectivity, i.e. that the functor
`X ↦ RHom_{A ⊗[R] A}(A, X ⊗ᴸ_A (A ⊗[R] A))` is faithful on endomorphisms of `K`.

### What the missing half is, exactly, and why it is not formal

Write `S = A ⊗[R] A`, let `p₁, p₂ : A → S` be the two coprojections and `μ : S → A` the
multiplication, so `μ ∘ p₁ = μ ∘ p₂ = 𝟙`, write `X_S` for restriction of scalars along `μ` (the
diagonal, `Δ_*`) and `Δ^! = RHom_S(A_S, ·)` for its right adjoint, and let
`F X = Δ^!(X ⊗ᴸ_A S)` be the functor just named, that is
`derivedHom μ ∘ diagonalDerivedExtension R A`, whose value at `K` the defining condition says is
`A`. What is needed is faithfulness of `F` on `Hom_A(K, K[i])` for **every** `i`. At `i = 0` that
is the missing surjectivity of `a ↦ a • 𝟙 K`, because `F` commutes with shifts, `F K ≅ A`, and the
resulting map `End_{D(A)}(K) → End_{D(A)}(F K) = A` is a *retraction* of `a ↦ a • 𝟙 K` — that is
the computation `key` in the proof below — so it is surjective and only injectivity is at stake.
At `i ≠ 0` faithfulness gives `Hom_A(K, K[i]) = Hom_A(A, A[i]) = 0`, hence `Ext^i_A(K, K) = 0`,
which the tag asserts as well: the degree-zero statement alone is strictly weaker than the tag,
since `A ⟶ RHom_A(K, K)` is invertible exactly when it is bijective on `H^0` and the other
cohomology vanishes.

**Where the two sides sit, and that both are now reached.** The derived endomorphisms live on the
extension side: by the adjunction between derived extension of scalars along `μ` and restriction
along it, together with `μ^*(K ⊗ᴸ_A S) ≅ K`, `End_{D(A)}(K) ≅ Hom_S(K ⊗ᴸ_A S, K_S)`. That is
`Dualizing.diagonalExtensionHomEquiv`, proved below with no hypothesis beyond flatness; an
earlier assessment recorded it as out of reach because it looked for it in coextension duality
`Dualizing.modelHomCoextendIsoRestrictScalars`, which indeed does not produce it — read along `μ`
that formula says `RHom_S(Y_S, X ⊗ᴸ_A S) ≅ RHom_A(Y, F X)_S`, which at `Y = A` is [stacks 0A71]
again and at `Y = X = K` returns `RHom_A(K, F K) ≅ RHom_A(K, A)`, the dual of `K`. The plain
adjunction supplies it instead. What the defining condition computes is the *other* direction,
`Hom_S(M_S, K ⊗ᴸ_A S) ≅ Hom_A(M, A)`, which is
`Dualizing.homDiagonalObjectEquivOfIsRelativeDualizingComplex`. So both Hom groups across the
diagonal are now available in closed form, and they are different ones: [stacks 0E2C] computes
morphisms *out of* the diagonal, [stacks 0E2G] is about the morphisms *into* it, and no formal
mechanism in this library connects the two.

**The conversion the earlier assessment sought does not exist.** That assessment proposed to
bridge the two by converting the coextension `RHom_A(S, ·)` along `p₁` into the extension
`· ⊗ᴸ_A S`, or equivalently `Δ^!(N)` into `Δ^*(N) ⊗ᴸ_A Δ^!(S)`. Neither can hold. The first needs
`S` to be a perfect `A`-module along `p₁`, which holds only when `A` is finite over `R`: for
`A = R[x]`, `S = A[y]` and `RHom_A(S, M) = ∏_ℕ M`, which is not `(M ⊗_A S) ⊗ᴸ_S RHom_A(S,A)`.
The second is worse than unavailable, it is refuted: it would turn the defining condition
`Δ^!(K ⊗ᴸ_A S) ≅ A` into `K ⊗ᴸ_A Δ^!(S) ≅ A`, making *every* relative dualizing complex
tensor-invertible, hence `R → A` Gorenstein — which
`Dualizing.isIso_evaluation_iff_nonempty_tensor_iso_one` of
`StacksFrontier.RingTheory.Dualizing.RelativeBiduality` shows fails for the witness `R = k` a field,
`A = k[x, y]/(x, y)²`, `K = Hom_k(A, k)`. Concretely `A` is not a perfect `S`-module there: `S` is
Artinian local of length `9` and `A` has length `3`, so finite projective dimension would force
`A` to be free over `S` of non-integral rank. That perfectness is a carried hypothesis of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject`, and its
Tor-amplitude form is what the docstring of
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude` refutes for that witness.

**What the two tags do and do not share.** The one statement that would supply [stacks 0E2D] is
the projection formula for the diagonal against a pullback along the complementary coprojection,

> `Δ^!(X ⊗ᴸ_S p₂^*L) ≅ Δ^!(X) ⊗ᴸ_A L`  at  `X = K ⊗ᴸ_A S`,

which is the instance of [stacks 0ATK] carried as `hdiag` in
`StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`; see that module for where its proof stops.
It does **not** supply this tag. Feeding it into the two Hom computations above only returns
`End_{D(A)}(K) ≅ End_{D(A)}(K)`: writing `K_S ≅ Δ_*Δ^!(K ⊠_R K)` and transposing recovers the
Hom group one started from, so the formula is consumed and nothing is gained. Nor is the formula
true for an arbitrary first argument — at `X = A_S` it asserts
`Δ^!Δ_*(L) ≅ Δ^!Δ_*(A) ⊗ᴸ_A L`, which already fails for `R = k`, `A = k[t]/t²`, `L = k`, where the
left side is `⊕_{i ≥ 0} k[-i]` and the right side has cohomology in arbitrarily negative degrees.
So [stacks 0E2G] needs strictly more than [stacks 0E2D] does, which is also what the source's
proof shows: it derives this tag *from* [stacks 0E2D] together with [stacks 0BZW] (1)(c) and the
Noetherian reduction.
Note finally that `F` is not conservative, so the alternative of applying `F` to the derived
homothety and proving the image invertible cannot conclude either.
`Dualizing.nonempty_modelHom_derivedHom_self_iso_doubleDual` does not help either: it computes
the endomorphisms of a derived coextension, so along `μ` at `X ⊗ᴸ_A S` the object it is about is
`F K ≅ A`, both sides collapse to `A_S`, and the statement is a tautology. It would compute
`End_{D(A)}(K)` only for a `K` exhibited as a coextension along `μ`, and exhibiting it so is the
identification [stacks 0E2D] supplies. The scalar bridge
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRingIso` transports morphism-level statements
between two spellings of derived Hom over one and the same ring; it removes a vocabulary
obstruction, not a mathematical one, and says nothing about the two coprojections `A → S`.

## References

* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

open StacksDraft.DerivedHom
open scoped ModuleCat.Algebra

/-! ### Linearity of the functors involved -/

/-- A left adjoint is `R`-linear as soon as its right adjoint is: transposing both sides of
`F (a • f) = a • F f` along the adjunction turns it into naturality of the unit. -/
theorem left_adjoint_linear {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Linear R] : F.Linear R := by
  constructor
  intro X Y f a
  apply (adj.homEquiv X (F.obj Y)).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, adj.unit_naturality, Functor.map_smul,
    Linear.comp_smul, adj.unit_naturality, Linear.smul_comp]

/-- A right adjoint is `R`-linear as soon as its left adjoint is, by the counit form of the
previous argument. -/
private theorem right_adjoint_linear {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Linear R] : G.Linear R := by
  constructor
  intro X Y f a
  apply (adj.homEquiv (G.obj X) Y).symm.injective
  rw [adj.homEquiv_counit, adj.homEquiv_counit, adj.counit_naturality, Functor.map_smul,
    Linear.smul_comp, adj.counit_naturality, Linear.comp_smul]

/-- Restriction of scalars along the structure map of an `A`-algebra `B` is `A`-linear. -/
private theorem linear_restrictScalars_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] : (ModuleCat.restrictScalars.{u} (algebraMap A B)).Linear A :=
  inferInstanceAs ((ModuleCat.restrictScalars.{u} (Algebra.ofId A B).toRingHom).Linear A)

/-- The derived coextension of scalars of [stacks 0A70] along `f : A →+* B` carries a scalar
multiple to the multiple by the image scalar: it is right adjoint to restriction of scalars,
which is `A`-linear. -/
private theorem derivedHom_map_smul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L) (a : A) :
    (derivedHom.{u, u} f).map (a • g) = f a • (derivedHom.{u, u} f).map g := by
  let : Algebra A B := f.toAlgebra
  let : (ModuleCat.restrictScalars.{u} f).Linear A := linear_restrictScalars_algebraMap
  let : (derivedHom.{u, u} f).Linear A :=
    right_adjoint_linear (Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, u} f))
  rw [Functor.map_smul]
  rfl

/-- The derived base change along the left coprojection `A → A ⊗[R] A` carries a scalar multiple
to the multiple by the image scalar: it is left adjoint to restriction of scalars, which is
`A`-linear. -/
private theorem diagonalDerivedExtension_map_smul {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] {K L : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ L)
    (a : A) :
    (diagonalDerivedExtension R A).map (a • g) =
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) a •
        (diagonalDerivedExtension R A).map g := by
  let f : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let : Algebra A (A ⊗[R] A) := f.toAlgebra
  let F := ModuleCat.extendScalars.{u, u, u} f
  let : (ModuleCat.restrictScalars.{u} f).Linear A := linear_restrictScalars_algebraMap
  let : F.Linear A := left_adjoint_linear (ModuleCat.extendRestrictScalarsAdj f)
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' f (includeLeftRingHom_flat R A)
  change F.mapDerivedCategory.map (a • g) = f a • F.mapDerivedCategory.map g
  rw [Functor.map_smul]
  rfl

/-! ### Scalars on a relative dualizing complex -/

/-- Two scalars acting equally on the identity of an object act equally on the identity of any
isomorphic object, by conjugation. -/
private theorem smul_id_eq_of_iso {A : Type u} [CommRing A] {C : Type*} [Category C]
    [Preadditive C] [Linear A C] {X Y : C} (e : X ≅ Y) {a b : A}
    (h : a • 𝟙 X = b • 𝟙 X) : a • 𝟙 Y = b • 𝟙 Y := by
  have h' : e.inv ≫ (a • 𝟙 X) ≫ e.hom = e.inv ≫ (b • 𝟙 X) ≫ e.hom := by rw [h]
  simpa [Linear.comp_smul, Linear.smul_comp] using h'

/-- **Scalars act faithfully on the tensor unit of `D(A)`.** The map `a ↦ a • 𝟙` from `A` to the
endomorphisms of the unit complex is bijective: it is so for the module `A`, the functor placing a
module in degree zero is fully faithful, and the unit complex is `A` placed in degree zero. -/
private theorem unit_smul_id_bijective {A : Type u} [CommRing A] :
    Function.Bijective (fun a : A => a • 𝟙 (DerivedCategory.Q.obj (𝟙_ (Model.Complex A)))) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  have h₁ : Function.Bijective (fun a : A => a • 𝟙 (ModuleCat.of A A)) :=
    ⟨fun a b h => by simpa using ConcreteCategory.congr_hom h (1 : A),
      fun f => ⟨f 1, ModuleCat.hom_ext <| LinearMap.ext_ring <| by simp⟩⟩
  have h₂ : Function.Bijective (S.map (X := ModuleCat.of A A) (Y := ModuleCat.of A A)) :=
    ⟨S.map_injective, S.map_surjective⟩
  let e : S.obj (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (𝟙_ (Model.Complex A)) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)
  convert (Iso.homCongr e e).bijective.comp (h₂.comp h₁) using 1
  ext a
  simp [Iso.homCongr, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- **Scalars act injectively on a relative dualizing complex.** For a relative dualizing complex
`K` of a flat, finitely presented map `R → A`, the map `a ↦ a • 𝟙 K` from `A` to the
endomorphisms of `K` in `D(A)` is injective.

This is what the defining condition of [stacks 0E2C] gives on its own towards [stacks 0E2G]: the
derived base change along the left coprojection and the derived Hom from the diagonal are both
`A`-linear up to the ring maps they are taken along, and the composite of the two maps `a` to the
scalar `a` again, because the left coprojection is a section of the multiplication map. So
`a • 𝟙 K` is carried to `a • 𝟙` on `RHom_{A ⊗[R] A}(A, K ⊗ᴸ_A (A ⊗[R] A))`, which the defining
condition says is `A` placed in degree zero, and there scalars are faithful. -/
theorem injective_smul_id_of_isRelativeDualizingComplex {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) :
    Function.Injective (fun a : A => a • 𝟙 K) := by
  let μ := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let F := diagonalDerivedExtension R A ⋙ derivedHom.{u, u} μ
  obtain ⟨e⟩ := hK.diagonalDerivedHom
  have key (c : A) : μ ((Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) c) = c := by
    simp [μ]
  intro a b hab
  have hh := congrArg F.map hab
  dsimp only [F, CategoryTheory.Functor.comp_map] at hh
  rw [diagonalDerivedExtension_map_smul, diagonalDerivedExtension_map_smul,
    derivedHom_map_smul, derivedHom_map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, key a, key b] at hh
  exact unit_smul_id_bijective.injective
    (smul_id_eq_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A))
      (smul_id_eq_of_iso e hh))

/-! ### Morphisms across the diagonal -/

/-- **Morphisms out of a derived base change along the left coprojection.** For a flat `R → A`,
morphisms in `D(A ⊗[R] A)` from the derived base change of `M` along the left coprojection into
the restriction of scalars of `N` along the multiplication map are morphisms `M ⟶ N` in `D(A)`.

Derived extension of scalars along the multiplication map is left adjoint to restriction of
scalars along it, and it carries the base change of `M` along the left coprojection back to `M`
because the coprojection is a section of the multiplication map
(`Dualizing.diagonalDerivedExtensionRetractionIso`).

At `M = N = K` this computes `End_{D(A)}(K)` as morphisms `K ⊗ᴸ_A (A ⊗[R] A) ⟶ A_B` in
`D(A ⊗[R] A)`, where `A_B` is the diagonal — the form in which the derived endomorphisms of `K`
are stated over `A ⊗[R] A` with the *extension* of scalars along the coprojection, which is the
functor the defining condition of [stacks 0E2C] concerns. Taking `N = K⟦i⟧` gives
`Ext^i_A(K, K)` in the same shape. -/
def diagonalExtensionHomEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (M N : DerivedCategory (ModuleCat.{u} A)) :
    ((diagonalDerivedExtension R A).obj M ⟶
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
            N) ≃ (M ⟶ N) :=
  let μ : A ⊗[R] A →+* A := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} μ
  let adj := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    (A ⊗[R] A) A _ _ μ _ _ T.functor T.comparison T.isLeftDerived
  (adj.homEquiv ((diagonalDerivedExtension R A).obj M) N).symm.trans
    ((diagonalDerivedExtensionRetractionIso R A M).homCongr (Iso.refl N))

/-- **Morphisms into the derived base change of a relative dualizing complex are the dual.** For
a relative dualizing complex `K`, morphisms in `D(A ⊗[R] A)` from the restriction of scalars of
`M` along the multiplication map into the derived base change of `K` along the left coprojection
are morphisms `M ⟶ A` in `D(A)`.

This is what the defining condition of [stacks 0E2C] computes on its own: restriction of scalars
along the multiplication map is left adjoint to the derived coextension of [stacks 0A70], and the
defining condition says that coextension applied to the base change of `K` is `A`. Taking
`M = K⟦-i⟧` gives `Ext^i_A(K, A)`.

Note which side this is. Together with `Dualizing.diagonalExtensionHomEquiv` it says that
[stacks 0E2C] computes morphisms in `D(A ⊗[R] A)` *out of* the diagonal into the base change of
`K`, where they are the `A`-dual of `K`, whereas the derived endomorphisms of `K` — the subject of
[stacks 0E2G] — are the morphisms in the opposite direction, *into* the diagonal out of the base
change. Nothing in this library relates the two, and that gap is exactly [stacks 0E2G]; see the
module documentation. -/
def homDiagonalObjectEquivOfIsRelativeDualizingComplex {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    ((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M ⟶
        (diagonalDerivedExtension R A).obj K) ≃
      (M ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) :=
  let μ : A ⊗[R] A →+* A := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let adj := Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, u} μ)
  (adj.homEquiv M ((diagonalDerivedExtension R A).obj K)).trans
    ((Iso.refl M).homCongr hK.diagonalDerivedHom.some)

/-! ### Invariance of the derived homothety under isomorphism -/

/-- Degree-zero derived Hom carries the derived homothety at `K` to the identity of `K`: the
homothety is by definition the transpose of the left unitor, and `homZeroEquiv` is that transpose
followed by the inverse unitor. -/
private theorem homZeroEquiv_derivedHomothety {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedInternalHom.Model.adjunction A).homZeroEquiv K K
        (derivedHomothety (DerivedInternalHom.Model.adjunction A).toDerivedHomAdjunction
          (DerivedCategory.Q.obj (𝟙_ (Model.Complex A)))
          (DerivedInternalHom.Model.adjunction A).tensorUnitLeft K) =
      𝟙 K := by
  simp [DerivedHomData.homZeroEquiv, derivedHomothety]

/-- Degree-zero derived Hom is natural in the source variable of the derived Hom bifunctor. -/
private theorem homZeroEquiv_naturality_left {A : Type u} [CommRing A] (d : DerivedHomData A)
    {K K' M : DerivedCategory (ModuleCat.{u} A)} (f : K' ⟶ K)
    (a : DerivedCategory.Q.obj (𝟙_ (Model.Complex A)) ⟶ d.hom.obj (Opposite.op K, M)) :
    d.homZeroEquiv K' M (a ≫ d.hom.map (f.op, 𝟙 M)) = f ≫ d.homZeroEquiv K M a := by
  dsimp [DerivedHomData.homZeroEquiv]
  rw [d.homEquiv_dinaturality]
  apply (cancel_epi (d.tensorUnitLeft K').hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← d.tensorUnitLeft_naturality f]
  simp

/-- Degree-zero derived Hom is natural in the target variable of the derived Hom bifunctor. -/
private theorem homZeroEquiv_naturality_right {A : Type u} [CommRing A] (d : DerivedHomData A)
    {K M M' : DerivedCategory (ModuleCat.{u} A)} (g : M ⟶ M')
    (a : DerivedCategory.Q.obj (𝟙_ (Model.Complex A)) ⟶ d.hom.obj (Opposite.op K, M)) :
    d.homZeroEquiv K M' (a ≫ d.hom.map (𝟙 (Opposite.op K), g)) = d.homZeroEquiv K M a ≫ g := by
  dsimp [DerivedHomData.homZeroEquiv]
  rw [d.homEquiv_naturality_right, Category.assoc]

/-- **Invertibility of the derived homothety is invariant under isomorphism.** An isomorphism
`e : K ≅ L` induces an isomorphism `RHom_A(K, K) ≅ RHom_A(L, L)` of the derived endomorphism
objects, and composing the homothety at `K` with it gives the homothety at `L`; so one is
invertible exactly when the other is.

This is how the conclusion of [stacks 0E2G] transports along the identification of a relative
dualizing complex with any other one, which is [stacks 0E2D]. -/
theorem isIso_derivedHomothety_iff_of_iso {A : Type u} [CommRing A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L) :
    IsIso (derivedHomothety (DerivedInternalHom.Model.adjunction A).toDerivedHomAdjunction
        (DerivedCategory.Q.obj (𝟙_ (Model.Complex A)))
        (DerivedInternalHom.Model.adjunction A).tensorUnitLeft K) ↔
      IsIso (derivedHomothety (DerivedInternalHom.Model.adjunction A).toDerivedHomAdjunction
        (DerivedCategory.Q.obj (𝟙_ (Model.Complex A)))
        (DerivedInternalHom.Model.adjunction A).tensorUnitLeft L) := by
  let adj := DerivedInternalHom.Model.adjunction A
  let H := DerivedInternalHom.Model.hom A
  let hK := derivedHomothety adj.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex A))) adj.tensorUnitLeft K
  let hL := derivedHomothety adj.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex A))) adj.tensorUnitLeft L
  let fIso : (Opposite.op K, K) ≅ (Opposite.op L, L) := e.symm.op.prod e
  let f₁ : (Opposite.op K, K) ⟶ (Opposite.op L, K) := (e.inv.op, 𝟙 K)
  let f₂ : (Opposite.op L, K) ⟶ (Opposite.op L, L) := (𝟙 (Opposite.op L), e.hom)
  let h : H.obj (Opposite.op K, K) ⟶ H.obj (Opposite.op L, L) := H.map fIso.hom
  have hcomp : hK ≫ h = hL := by
    apply (adj.homZeroEquiv L L).injective
    have hfactor : h = H.map f₁ ≫ H.map f₂ := by
      change H.map fIso.hom = _
      rw [← Functor.map_comp]
      congr 1
      ext <;> simp [fIso, f₁, f₂]
    rw [hfactor]
    calc
      adj.homZeroEquiv L L (hK ≫ adj.hom.map f₁ ≫ adj.hom.map f₂) =
          adj.homZeroEquiv L K (hK ≫ adj.hom.map f₁) ≫ e.hom := by
        simpa [f₂] using homZeroEquiv_naturality_right adj e.hom (hK ≫ adj.hom.map f₁)
      _ = (e.inv ≫ adj.homZeroEquiv K K hK) ≫ e.hom := by
        rw [homZeroEquiv_naturality_left adj e.inv]
      _ = 𝟙 L := by
        rw [homZeroEquiv_derivedHomothety]
        simp
      _ = adj.homZeroEquiv L L hL := (homZeroEquiv_derivedHomothety L).symm
  have : IsIso h := Functor.map_isIso H fIso.hom
  change IsIso hK ↔ IsIso hL
  rw [← hcomp]
  exact (isIso_comp_right_iff _ h).symm

end

end Dualizing

end
