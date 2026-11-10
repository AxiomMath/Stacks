module

public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionTensorFactor
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDiagonalComposition
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensorUnconditional
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange

/-!
# The free tensor factor of `Δ^!`, and what is left of [stacks 0E2D]

Let `R → A` be flat of finite presentation, write `B = A ⊗[R] A`, let `p₁, p₂ : A → B` be the two
coprojections and `Δ : B → A` the multiplication map.  Every route to [stacks 0E2D] considered in
this library reduces the tag to a **projection formula for `Δ^!`** at a tensor factor pulled back
along a coprojection,

`Δ^!(p₁^*X ⊗ᴸ_B Y) ≅ X`,

and every one of them stalls at the same place: the formula is available only when the factor is
*perfect* — `Dualizing.nonempty_derivedHom_tensor_includeLeft_isPerfect_iso` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixedPerfectFactor` — and a relative
dualizing
complex is not.  In full generality the formula is false: it is equivalent to `A` being a perfect
module over `B`, hence to `R → A` being a local complete intersection, which [stacks 0E2D] does
not assume.

**This file proves the formula with no hypothesis on `X` at all, for one particular `Y`.**  The
`Y` is `p₁^!(A)`, the relative dualizing complex of the coprojection itself, and the proof uses no
projection formula for `Δ^!`: it is the composition law `Δ^! ∘ p₁^! ≅ id` at a retract —
`Dualizing.nonempty_upperShriekFunctor_comp_derivedHom_iso_id`, unconditional — read through
[stacks 0BZU], which turns `p₁^!` into `p₁^*(-) ⊗ᴸ_B p₁^!(A)`.

## Main results

* `Dualizing.nonempty_derivedTensorProductOver_comp_derivedHom_retract_iso_id` — **the functor
  form, at an arbitrary retract**: if `h : B → A` is surjective, `s : A → B` is a section of it
  with polynomial presentation `q`, and `W` is an object of `D(B)` for which [stacks 0BZU] holds
  — `q^!(-) ≅ - ⊗ᴸ_A W` — then `h^!(- ⊗ᴸ_A W)` is the identity functor of `D(A)`.
* `Dualizing.nonempty_derivedHom_tensor_section_extension_iso` — the same read at an object and in
  the tensor vocabulary of [stacks 0A63]: `h^!(s^*N ⊗ᴸ_B W) ≅ N`, for **every** `N` in `D(A)`.
* `Dualizing.nonempty_upperShriekFunctor_includeLeft_iso_derivedTensorProduct` — [stacks 0BZU] at
  the left coprojection, discharged from flatness and finite presentation of `R → A` alone.
* `Dualizing.nonempty_derivedHom_lmul'_tensor_diagonalDerivedExtension_iso` — **the formula at the
  diagonal**: `Δ^!(p₁^*N ⊗ᴸ_B p₁^!(A)) ≅ N` for every `N` in `D(A)`, with nothing assumed of `N`.
* `Dualizing.nonempty_derivedHom_lmul'_tensor_includeRightExtension_iso` — its mirror at the
  right coprojection.
* `Dualizing.nonempty_iso_of_tensor_section_extension_iso` — the uniqueness reduction in the
  external-product vocabulary: at a surjection with two presented sections, one isomorphism
  `s₁^*K ⊗ᴸ_B W₁ ≅ s₂^*L ⊗ᴸ_B W₂` forces `K ≅ L`, with nothing assumed of `K` or `L`.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_of_tensor_coprojection_iso` — that
  reduction at the diagonal, with both instances of [stacks 0BZU] discharged.

## What this changes about [stacks 0E2D]

[stacks 0BZV] case (2) identifies `p₁^!(A)` with `p₂^*(ω^•_{A/R})`, `ω^•_{A/R} = φ^!(R)` being the
relative dualizing complex produced by [stacks 0E2E]; in this library that identification carries
`Dualizing.PolynomialPresentation.ProjectionCompatibility` and is not available, which is why the
statements below are made at `p₁^!(A)` rather than at `p₂^*(ω^•_{A/R})`.  Granting it, the last
theorem reads

`Δ^!(p₁^*N ⊗ᴸ_B p₂^*ω^•_{A/R}) ≅ N`   for every `N`, with no hypothesis on `N`,

so **the projection formula is not what [stacks 0E2D] is missing**.  At `N = K` a second relative
dualizing complex it supplies, unconditionally, the first of the two isomorphisms carried as
`hshriek` by
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`; the second
asks for the *same* object `Δ^!(p₁^*K ⊗ᴸ_B p₂^*ω^•_{A/R})` to be `ω^•_{A/R}`, and since the first
says it is `K`, the pair is equivalent to `K ≅ ω^•_{A/R}` and nothing else.  So the residual
content of [stacks 0E2D] is

> every relative dualizing complex for `R → A` is isomorphic to `φ^!(R)`,

and no projection formula, in any slot, will produce it: a composition law of the form
`Δ^! ∘ p^! ≅ id` returns the factor `p^!` was applied to, which is the one that is *not* the
relative dualizing complex of `p`.  That accounting is the one already recorded in the module
documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDiagonalComposition`; what is new here is
that
the first half of the pair is now a theorem rather than a hypothesis, so the asymmetry is visible
in the statements and not only in the prose.

No tag is claimed.  The reduction of [stacks 0E2D] to one isomorphism in `D(B)` is already
registered, with its hypothesis, on
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_upperShriek_coprojection_iso`, and
rewriting that hypothesis through [stacks 0BZU] — which is what this file does — leaves the same
statement.

## The two tensor products

The tensor product used below is the one of the tagged statement of [stacks 0A63],
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is also the vocabulary of
`Dualizing.nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension`, the bridge from the
change-of-rings tensor product of [stacks 06Y6] that [stacks 0BZU] is stated with.  It is *not*
`StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor`, the model-level bifunctor in which
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` phrases `hshriek`: the two are related
only through the `ULift` conjugation of `Dualizing.derivedHomAdjunctionOverRingIso`, and no
comparison of them is stated in this library.  The accounting of the previous section is therefore
mathematical rather than mechanical — the statements below do not plug into `hshriek` as they
stand.

## Why no statement below is Noetherian

The diagonal statements once carried `[IsNoetherianRing A]` and `[IsNoetherianRing (A ⊗[R] A)]`,
consumed by `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct`
and by `Dualizing.PolynomialPresentation.isPerfectModule_of_flat`.  Neither consumed it for the
mathematics.  The proof of the first names eight inputs — Tag 0BZE at a presentation, the shift and
unit comparisons of the change-of-rings tensor product, Tag 08YU, and four bookkeeping isomorphisms
— and not one of them carries a Noetherian hypothesis, so that signature has been relieved of it in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor`.  The second used it only to upgrade
finite type to finite presentation; that upgrade is free at a coprojection of a finitely presented
algebra, which is
`Dualizing.PolynomialPresentation.isPerfectModule_of_flat_of_finitePresentation`, and finite
presentation of `R → A` is a standing hypothesis of [stacks 0E2D] in any case.  So the diagonal
statements assume exactly what the tag assumes: `R → A` flat of finite presentation.  The retract
statements of the first section assume even less — they take [stacks 0BZU] as the hypothesis
`hBZU`.

## The reduction formula, and where the polynomial factorisation fails to carry it

What *would* settle the residue is the reduction formula

`Δ^!(p₁^*M ⊗ᴸ_B p₂^*N) ≅ RHom_A(RHom_A(M, ω^•_{A/R}), N)`   for `M` `R`-perfect and `N` arbitrary,

which specialises at `M = K`, `N = A` to `RHom_A(RHom_A(K, ω^•_{A/R}), A) ≅ A`. It is the reduction
theorem of Avramov, Iyengar, Lipman and Nayak (Adv. Math. 223 (2010) 735–772, Theorem 4.1), and the
natural approach here is to run their argument through the polynomial presentation this library
already has: write `A = P/I` with `P = R[x_1, …, x_n]`, put `C = P ⊗[R] P`, and use that the
diagonal of `P` over `R` is Koszul-regular — generated by the `x_i ⊗ 1 - 1 ⊗ x_i` — so that `P` is
a perfect `C`-module and the projection formula for `δ_P^!` is legal where it is illegal for `Δ`.

**It does not carry.**  Write `ρ : C → B` and `π : P → A` for the two surjections, so that
`Δ ∘ ρ = π ∘ δ_P`.  Composing derived Hom along surjections along the two factorisations gives

`RHom_C(A, W) ≅ RHom_B(A, ρ^!W) ≅ RHom_P(A, δ_P^!W)`,

and the right-hand side is computable by the Koszul-regular diagonal.  But the object the formula
is about is `M ⊠_R N` in `D(B)`, and that is `ρ_*` of nothing relevant: `ρ^!W = RHom_C(B, W)`, so
`ρ^!(M ⊠^C_R N) ≅ M ⊠^B_R N` would itself be a projection formula for `ρ`.  Transposing instead —
`RHom_C(A, ρ_*Z) ≅ RHom_B(A ⊗ᴸ_C B, Z)` — replaces `A` by `A ⊗ᴸ_C B`, and that is not `A`: the
square `C → B → A`, `C → P → A` is **not Tor-independent**, and not only in a pathological case.
For `R = k` a field and `A = k[x]/(x²)` — flat, finite presentation, and even a local complete
intersection — one has `P = k[x]`, `C = k[x, y]`, `B = k[x, y]/(x², y²)` and `A = C/(x - y, x²)`
with `x` and `y` both acting on `A` as `x`.  Since `(x², y²)` is a regular sequence in `C`, the
Koszul complex on it resolves `B`, and its image in `A` is the sequence `(0, 0)`, so

`A ⊗ᴸ_C B ≅ A ⊕ A[1]^{⊕2} ⊕ A[2]`.

So the polynomial factorisation transports the diagonal computation to `A ⊗ᴸ_C B`, not to `A`, and
the gap is not closed by assuming `R → A` lci.  This is why the cited argument runs its §§2–4
differential graded machinery at the *finite* map `P ↠ A` and not only at `R → A`: flatness of
`R → A` makes `A ⊗ᴸ_R A` the ordinary `A ⊗[R] A` and removes the resolutions there, but it says
nothing about `C → B`, which is where they are actually needed.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section Retract

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The change-of-rings tensor product `N ⊗ᴸ_A W` is the tensor product of `s^*N` and `W`. -/
private theorem nonempty_derivedTensorProductOver_obj_iso_tensor_section
    {s : A →+* B} (N : DerivedCategory (ModuleCat.{u} A)) (W : DerivedCategory (ModuleCat.{u} B)) :
    Nonempty ((derivedTensorProductOver.{u, u} s W).obj N ≅
      (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj
        ((totalDerivedExtensionScalars.{u, u, u} s).functor.obj N, W)) := by
  obtain ⟨e⟩ := nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension s N W
  exact ⟨e ≪≫ (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensorSwap _ _⟩

/-- **The composition law at a retract, read through [stacks 0BZU].**  Let `h : B → A` be a
surjective ring homomorphism, let `s : A → B` be a section of it with polynomial presentation `q`,
and let `W` be an object of `D(B)` for which upper shriek of `q` is derived tensor product over
`A` with `W` — the conclusion of [stacks 0BZU], carried here rather than proved.  Then derived
tensor product with `W` followed by derived Hom along `h` is the identity functor of `D(A)`:

`h^!(- ⊗ᴸ_A W) ≅ id`.

Nothing else is assumed: no flatness, no Noetherian hypothesis, nothing about the objects the
functor is evaluated at.  The whole proof is
`Dualizing.nonempty_upperShriekFunctor_comp_derivedHom_iso_id`, which is [stacks 0BZT] for a
surjective second map at the tower `A --s--> B --h--> A`, with the first functor rewritten by the
carried hypothesis. -/
theorem nonempty_derivedTensorProductOver_comp_derivedHom_retract_iso_id
    (h : B →+* A) (hh : Function.Surjective h) {s : A →+* B}
    (hs : h.comp s = RingHom.id A) (q : PolynomialPresentation s)
    (W : DerivedCategory (ModuleCat.{u} B))
    (hBZU : Nonempty (q.upperShriekFunctor.{u, u} ≅ derivedTensorProductOver.{u, u} s W)) :
    Nonempty (derivedTensorProductOver.{u, u} s W ⋙ derivedHom.{u, u} h ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A))) := by
  obtain ⟨e⟩ := hBZU
  obtain ⟨e₀⟩ := nonempty_upperShriekFunctor_comp_derivedHom_iso_id h hh hs q
  exact ⟨Functor.isoWhiskerRight e.symm (derivedHom.{u, u} h) ≪≫ e₀⟩

/-- **The projection formula for `h^!` at the free factor, with no hypothesis on the other
factor.**  In the situation of
`Dualizing.nonempty_derivedTensorProductOver_comp_derivedHom_retract_iso_id`, and in the tensor
vocabulary of [stacks 0A63],

`h^!(s^*N ⊗ᴸ_B W) ≅ N`   for every object `N` of `D(A)`,

where `s^*` is derived base change along the section.  The derived change-of-rings tensor product
`- ⊗ᴸ_A W` of [stacks 06Y6] is brought into that vocabulary by
`Dualizing.nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension`, which is
unconditional. -/
theorem nonempty_derivedHom_tensor_section_extension_iso
    (h : B →+* A) (hh : Function.Surjective h) {s : A →+* B}
    (hs : h.comp s = RingHom.id A) (q : PolynomialPresentation s)
    (W : DerivedCategory (ModuleCat.{u} B))
    (hBZU : Nonempty (q.upperShriekFunctor.{u, u} ≅ derivedTensorProductOver.{u, u} s W))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty ((derivedHom.{u, u} h).obj
        ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj
          ((totalDerivedExtensionScalars.{u, u, u} s).functor.obj N, W)) ≅ N) := by
  obtain ⟨e⟩ := nonempty_derivedTensorProductOver_comp_derivedHom_retract_iso_id h hh hs q W hBZU
  obtain ⟨e₂⟩ := nonempty_derivedTensorProductOver_obj_iso_tensor_section (s := s) N W
  exact ⟨(derivedHom.{u, u} h).mapIso e₂.symm ≪≫ e.app N⟩

/-- **Two external products, one isomorphism, and the objects are isomorphic.**  Let `h : B → A`
be surjective, let `s₁` and `s₂` be sections of `h` with polynomial presentations `q₁` and `q₂`,
and let `W₁` and `W₂` be objects of `D(B)` for which [stacks 0BZU] holds at the corresponding
section.  If

`s₁^*K ⊗ᴸ_B W₁ ≅ s₂^*L ⊗ᴸ_B W₂`

in `D(B)`, then `K ≅ L`.  Nothing is assumed of `K` or of `L`.

This is `Dualizing.nonempty_iso_of_nonempty_upperShriekFunctor_section_iso` with its hypothesis
`s₁^!(K) ≅ s₂^!(L)` rewritten as an isomorphism of tensor products, which is what the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDiagonalComposition` records
as needing [stacks 0BZU] together with a comparison of the two tensor products — the second of
those is `Dualizing.nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension`, and the
first is the carried `hBZU₁`, `hBZU₂`.  At `B = A ⊗[R] A`, `h` the multiplication map and
`s₁, s₂` the two coprojections, the hypothesis reads `K ⊠_R ω₁ ≅ ω₂ ⊠_R L`. -/
theorem nonempty_iso_of_tensor_section_extension_iso
    (h : B →+* A) (hh : Function.Surjective h) {s₁ s₂ : A →+* B}
    (hs₁ : h.comp s₁ = RingHom.id A) (hs₂ : h.comp s₂ = RingHom.id A)
    (q₁ : PolynomialPresentation s₁) (q₂ : PolynomialPresentation s₂)
    (W₁ W₂ : DerivedCategory (ModuleCat.{u} B))
    (hBZU₁ : Nonempty (q₁.upperShriekFunctor.{u, u} ≅ derivedTensorProductOver.{u, u} s₁ W₁))
    (hBZU₂ : Nonempty (q₂.upperShriekFunctor.{u, u} ≅ derivedTensorProductOver.{u, u} s₂ W₂))
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (e : Nonempty
      ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj
          ((totalDerivedExtensionScalars.{u, u, u} s₁).functor.obj K, W₁) ≅
        (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj
          ((totalDerivedExtensionScalars.{u, u, u} s₂).functor.obj L, W₂))) :
    Nonempty (K ≅ L) := by
  obtain ⟨e₁⟩ := nonempty_derivedTensorProductOver_obj_iso_tensor_section (s := s₁) K W₁
  obtain ⟨e₂⟩ := nonempty_derivedTensorProductOver_obj_iso_tensor_section (s := s₂) L W₂
  refine nonempty_iso_of_nonempty_upperShriekFunctor_section_iso h hh hs₁ hs₂ q₁ q₂
    ⟨hBZU₁.some.app K ≪≫ e₁ ≪≫ e.some ≪≫ e₂.symm ≪≫ (hBZU₂.some.app L).symm⟩

end Retract

section Coprojection

/-- **The right coprojection of a finitely presented algebra is of finite presentation.**  It is
the left coprojection followed by the commutativity isomorphism of `A ⊗[R] A`, and the left one is
the base change of `R → A` along itself. -/
theorem finitePresentation_includeRight (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    RingHom.FinitePresentation
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom := by
  have heq : (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom =
      ((Algebra.TensorProduct.comm R A A).toRingEquiv :
        A ⊗[R] A →+* A ⊗[R] A).comp (algebraMap A (A ⊗[R] A)) := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [heq]
  exact (RingHom.FinitePresentation.of_bijective (Algebra.TensorProduct.comm R A A).bijective).comp
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

end Coprojection

section Diagonal

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]

/-- **[stacks 0BZU] at the left coprojection `p₁ : A → A ⊗[R] A`.**  For `R → A` flat of finite
presentation, upper shriek of any polynomial presentation `q` of the left coprojection is derived
tensor product over `A` with the single object `q^!(A)` of `D(A ⊗[R] A)`.

The coprojection is flat and of finite presentation, being the base change of `R → A` along
itself, so `Dualizing.PolynomialPresentation.isPerfectModule_of_flat_of_finitePresentation` makes
`A ⊗[R] A` a perfect module over the polynomial algebra of `q`, which is the only hypothesis
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct` carries. -/
theorem nonempty_upperShriekFunctor_includeLeft_iso_derivedTensorProduct
    [Algebra.FinitePresentation R A]
    (q : PolynomialPresentation (algebraMap A (A ⊗[R] A))) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))
    Nonempty (q.upperShriekFunctor.{u, u} ≅
      derivedTensorProductOver.{u, u} (algebraMap A (A ⊗[R] A))
        (q.upperShriekFunctor.{u, u}.obj A₀)) :=
  q.nonempty_upperShriekFunctor_iso_derivedTensorProduct
    (q.isPerfectModule_of_flat_of_finitePresentation
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (RingHom.finitePresentation_algebraMap.mpr inferInstance))

/-- **The projection formula for `Δ^!` at the relative dualizing complex of the coprojection, with
no hypothesis on the other factor.**  Let `R → A` be flat of finite presentation, write
`B = A ⊗[R] A`, write `p₁ : A → B` for the left coprojection and `Δ : B → A` for the multiplication
map, and let `q` be a polynomial presentation of `p₁`.  Then

`Δ^!(p₁^*N ⊗ᴸ_B p₁^!(A)) ≅ N`   for every object `N` of `D(A)`.

Nothing is assumed of `N`: not perfectness, not pseudo-coherence, not a Tor-amplitude bound.  This
is what separates the statement from
`Dualizing.nonempty_derivedHom_tensor_includeLeft_isPerfect_iso`, which has an arbitrary second
factor and a perfect first one; here the second factor is pinned to `p₁^!(A)` and the first is
free.

By [stacks 0BZV] case (2) the second factor is `p₂^*(ω^•_{A/R})`, so this is the projection formula
the diagonal routes to [stacks 0E2D] ask for, at `L = ω^•_{A/R}`.  That identification carries
`Dualizing.PolynomialPresentation.ProjectionCompatibility` in this library and is not used; see the
module documentation for what the formula does and does not settle. -/
theorem nonempty_derivedHom_lmul'_tensor_diagonalDerivedExtension_iso
    [Algebra.FinitePresentation R A]
    (q : PolynomialPresentation (algebraMap A (A ⊗[R] A)))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))
    Nonempty ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.obj
          ((diagonalDerivedExtension R A).obj N, q.upperShriekFunctor.{u, u}.obj A₀)) ≅ N) := by
  obtain ⟨e⟩ := nonempty_derivedHom_tensor_section_extension_iso
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (surjective_lmul' R A)
    (lmul'_comp_includeLeftRingHom R A) q _
    (nonempty_upperShriekFunctor_includeLeft_iso_derivedTensorProduct R A q) N
  exact ⟨(derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
      ((derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.mapIso
        (((diagonalDerivedExtensionIsoTotalDerived R A).app N).symm.prod (Iso.refl _))) ≪≫ e⟩

/-- **[stacks 0BZU] at the right coprojection `p₂ : A → A ⊗[R] A`.**  The mirror of
`Dualizing.nonempty_upperShriekFunctor_includeLeft_iso_derivedTensorProduct`.  The right
coprojection is flat by `Dualizing.flat_includeRight` and of finite presentation by
`Dualizing.finitePresentation_includeRight`, and the two are fed to
`Dualizing.PolynomialPresentation.isPerfectModule_of_flat_of_finitePresentation` through the
algebra structure the coprojection itself defines on `A ⊗[R] A`, which is why the statement names
the coprojection rather than a structure map. -/
theorem nonempty_upperShriekFunctor_includeRight_iso_derivedTensorProduct
    [Algebra.FinitePresentation R A]
    (q : PolynomialPresentation
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))
    Nonempty (q.upperShriekFunctor.{u, u} ≅
      derivedTensorProductOver.{u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
        (q.upperShriekFunctor.{u, u}.obj A₀)) := by
  let : Algebra A (A ⊗[R] A) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom.toAlgebra
  exact q.nonempty_upperShriekFunctor_iso_derivedTensorProduct
    (q.isPerfectModule_of_flat_of_finitePresentation
      (flat_includeRight (R := R) (A := A) (R' := A)
        (RingHom.flat_algebraMap_iff.mpr inferInstance))
      (finitePresentation_includeRight R A))

/-- **The mirror of
`Dualizing.nonempty_derivedHom_lmul'_tensor_diagonalDerivedExtension_iso` at the right
coprojection**: `Δ^!(p₂^*N ⊗ᴸ_B p₂^!(A)) ≅ N` for every object `N` of `D(A)`, with nothing
assumed of `N`.

Both coprojections are sections of the multiplication map, so this is
`Dualizing.nonempty_derivedHom_tensor_section_extension_iso` run at the other one, with
[stacks 0BZU] supplied by
`Dualizing.nonempty_upperShriekFunctor_includeRight_iso_derivedTensorProduct`. -/
theorem nonempty_derivedHom_lmul'_tensor_includeRightExtension_iso
    [Algebra.FinitePresentation R A]
    (q : PolynomialPresentation
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom)
    (N : DerivedCategory (ModuleCat.{u} A)) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))
    Nonempty ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj N,
            q.upperShriekFunctor.{u, u}.obj A₀)) ≅ N) :=
  nonempty_derivedHom_tensor_section_extension_iso
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (surjective_lmul' R A)
    (lmul'_comp_includeRight R A) q _
    (nonempty_upperShriekFunctor_includeRight_iso_derivedTensorProduct R A q) N

/-- **[stacks 0E2D] from one isomorphism of external products.**  Let `R → A` be flat of finite
presentation, write `B = A ⊗[R] A`, let `K` and `L` be relative dualizing
complexes for `R → A`, let `q₁` and `q₂` be polynomial presentations of the two coprojections and
write `ω₁ = p₁^!(A)`, `ω₂ = p₂^!(A)`.  If

`p₁^*K ⊗ᴸ_B ω₁ ≅ p₂^*L ⊗ᴸ_B ω₂`

in `D(B)`, then `K ≅ L`.

The hypotheses `hK` and `hL` are recorded rather than consumed:
`Dualizing.nonempty_iso_of_tensor_section_extension_iso`, which is the whole proof, needs nothing
of `K` or of `L`.  Granting [stacks 0BZV] case (2) at both coprojections, so that `ω₁ = p₂^*ω` and
`ω₂ = p₁^*ω` for `ω = ω^•_{A/R}`, the hypothesis reads `K ⊠_R ω ≅ ω ⊠_R L`, which at `L = ω` is
the external-product form of the tag.

No tag attribute is attached.  The statement is
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_upperShriek_coprojection_iso` with
its hypothesis rewritten through [stacks 0BZU], and that theorem carries the registration. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_of_tensor_coprojection_iso
    [Algebra.FinitePresentation R A]
    (q₁ : PolynomialPresentation (algebraMap A (A ⊗[R] A)))
    (q₂ : PolynomialPresentation
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    let A₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))
    Nonempty
        ((derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.obj
            ((diagonalDerivedExtension R A).obj K, q₁.upperShriekFunctor.{u, u}.obj A₀) ≅
          (derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom).functor.obj L,
              q₂.upperShriekFunctor.{u, u}.obj A₀)) →
      Nonempty (K ≅ L) := by
  intro _ e
  have := hK
  have := hL
  exact nonempty_iso_of_tensor_section_extension_iso
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (surjective_lmul' R A)
    (lmul'_comp_includeLeftRingHom R A) (lmul'_comp_includeRight R A) q₁ q₂ _ _
    (nonempty_upperShriekFunctor_includeLeft_iso_derivedTensorProduct R A q₁)
    (nonempty_upperShriekFunctor_includeRight_iso_derivedTensorProduct R A q₂)
    ⟨(derivedHomAdjunctionOverRing.{u, u, u + 1} (A ⊗[R] A)).tensor.mapIso
      (((diagonalDerivedExtensionIsoTotalDerived R A).app K).prod (Iso.refl _)) ≪≫ e.some⟩

end Diagonal

end Dualizing

end
