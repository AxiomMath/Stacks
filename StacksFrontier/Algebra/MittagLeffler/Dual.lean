module

public import StacksFrontier.Algebra.MittagLeffler.Criteria

@[expose] public section

universe u v v' v'' w w' w''

/-!
# A directed system of finite projective modules is Mittag-Leffler as soon as its dual is

Let `R` be a commutative ring and let `F : J ⥤ ModuleCat R` be a diagram `(M i, f i j)` of
finitely generated projective `R`-modules. This file proves Stacks 059G: `F` is a Mittag-Leffler
system (Definition 059A) if and only if the single inverse system of `R`-duals
`(Hom_R(M i, R), Hom_R(f i j, R))` is Mittag-Leffler.

Only the reverse implication has content, the forward one being the specialization of
`IsMittagLefflerSystem` to the test module `R`. Two things have to be produced from the members
being finitely generated and projective: their finite presentation, which is
`Module.finitePresentation_of_projective`, and the passage from the test module `R` to an
arbitrary test module `N`. The latter is `range_lcomp_le_range_lcomp_of_dual`: writing `M i'` as a
direct summand `M i' →ᵍ R^n →ᶠ M i'` of a finite free module, a map `φ : M i' → N` satisfies
`φ ∘ f i i' = φ ∘ f ∘ (g ∘ f i i')`, and the `n` coordinates of `g ∘ f i i'` are `R`-valued maps
on `M i`, each of which the hypothesis factors through `f i k`; assembling those `n` factorizations
into a single map `q : M k → R^n` gives `g ∘ f i i' = q ∘ f i k`, whence
`φ ∘ f i i' = (φ ∘ f ∘ q) ∘ f i k`.

This is the source's argument. Where the source contracts `Hom_R(M i, R) ⊗_R N ≅ Hom_R(M i, N)`
and appeals to right exactness of `- ⊗_R N`, the summand decomposition performs the same reduction
without naming the tensor product; the two are the same computation, the isomorphism being
`dualTensorHom` and the finite free module being where it is evidently an isomorphism.

## Main results

* `Stacks.MittagLeffler.DualSystem.solution`: the statement of Stacks 059G.

## Implementation notes

`Stacks.MittagLeffler.DualSystem.range_lcomp_le_range_lcomp_of_dual` is stated for linear maps
rather than for
`ModuleCat` morphisms, with all four modules in independent universes: it is a statement about
precomposition maps `LinearMap.lcomp` between hom-modules and has nothing to do with the diagram.
It needs only the *target* of the first map to be finitely generated and projective.

`Stacks.MittagLeffler.DualSystem.isMittagLeffler_dual_iff_range_lcomp_le` restates Mathlib's
`Functor.IsMittagLeffler` for a dual system `F.op ⋙ yoneda.obj N` as a condition on the diagram
`F` itself: the images of the precomposition maps `Hom_R(M i', N) → Hom_R(M i, N)` are compared as
submodules. It reads the test module `N` through a linear equivalence `N ≃ₗ[R] N'`, which is what
lets the two sides of 059G be compared at all: the criterion's test module is a copy
`Shrink.{v} R` of `R` in the universe of the members, and the equivalence
`Shrink.linearEquiv R R` is what turns the criterion into a statement about `R`-valued
functionals, in the form `range_lcomp_le_range_lcomp_of_dual` consumes. Passing
`LinearEquiv.refl R N` recovers the plain reading. So the passage through `Opposite` and the
transport along `Shrink.linearEquiv` each happen once, in that lemma.

## References

* [StacksProject 059G](https://stacks.math.columbia.edu/tag/059G)
-/

@[expose] public section



open CategoryTheory

namespace Stacks.MittagLeffler.DualSystem

/-- Let `u : M → M'` and `v : M → K` be `R`-linear maps with `M'` finitely generated and
projective. If every `R`-valued functional on `M'`, precomposed with `u`, factors through `v`,
then so does every `N`-valued map on `M'`, for every `R`-module `N`.

This is the reduction of criterion (4) of Stacks 059E to the single test module `R`: for a finitely
generated projective `M'` the precomposition map `Hom_R(M', N) → Hom_R(M, N)` is
`Hom_R(M', R) → Hom_R(M, R)` tensored with `N`, so its image is determined by the image of the
latter. -/
private theorem range_lcomp_le_range_lcomp_of_dual {R : Type u} [CommRing R] {M : Type v}
    {M' : Type v'} {K : Type v''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup K] [Module R K]
    [Module.Finite R M'] [Module.Projective R M'] (N : Type w) [AddCommGroup N] [Module R N]
    (u : M →ₗ[R] M') (v : M →ₗ[R] K)
    (h : LinearMap.range (LinearMap.lcomp R R u) ≤ LinearMap.range (LinearMap.lcomp R R v)) :
    LinearMap.range (LinearMap.lcomp R N u) ≤ LinearMap.range (LinearMap.lcomp R N v) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M'
  choose β hβ using fun j : Fin n => h ⟨LinearMap.proj j ∘ₗ g, rfl⟩
  rintro _ ⟨φ, rfl⟩
  refine ⟨φ ∘ₗ f ∘ₗ LinearMap.pi β, ?_⟩
  ext x
  have hgu : LinearMap.pi β (v x) = g (u x) := funext fun j => LinearMap.congr_fun (hβ j) x
  simpa [hgu] using congrArg φ (LinearMap.congr_fun hfg (u x))

/-- The Mittag-Leffler condition on the inverse system of duals `(Hom_R(M i, N), Hom_R(f i j, N))`
of a diagram `F : J ⥤ ModuleCat R`, read on `F` itself and through a linear equivalence
`e : N ≃ₗ[R] N'`: for every `i` there is a transition map `f i i'` whose precomposition map
`Hom_R(M i', N') → Hom_R(M i, N')` has image inside that of `f i k`, for every transition map
`f i k`. -/
private theorem isMittagLeffler_dual_iff_range_lcomp_le {R : Type u} [CommRing R] {J : Type w}
    [Category.{w'} J] (F : J ⥤ ModuleCat.{v} R) (N : ModuleCat.{v} R) {N' : Type w''}
    [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') :
    (F.op ⋙ yoneda.obj N).IsMittagLeffler ↔
      ∀ i : J, ∃ (i' : J) (u : i ⟶ i'), ∀ (k : J) (v : i ⟶ k),
        LinearMap.range (LinearMap.lcomp R N' (F.map u).hom) ≤
          LinearMap.range (LinearMap.lcomp R N' (F.map v).hom) := by
  refine ⟨fun h i => ?_, fun h j => ?_⟩
  · obtain ⟨i', u, hu⟩ := h (Opposite.op i)
    refine ⟨i'.unop, u.unop, fun k v => ?_⟩
    rintro _ ⟨φ, rfl⟩
    obtain ⟨ψ, hψ⟩ := hu (k := Opposite.op k) v.op
      ⟨ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ φ), rfl⟩
    refine ⟨e.toLinearMap ∘ₗ ψ.hom, ?_⟩
    ext x
    simpa using congrArg e (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hψ) x)
  · obtain ⟨i', u, hu⟩ := h j.unop
    refine ⟨Opposite.op i', u.op, ?_⟩
    rintro k g _ ⟨φ, rfl⟩
    obtain ⟨ψ, hψ⟩ := hu k.unop g.unop ⟨e.toLinearMap ∘ₗ φ.hom, rfl⟩
    refine ⟨ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ ψ), ModuleCat.hom_ext ?_⟩
    ext x
    simpa using congrArg e.symm (LinearMap.congr_fun hψ x)

/-- Let `R` be a commutative ring and let `F : J ⥤ ModuleCat R` be a diagram of finitely
generated projective `R`-modules. Then `F` is a Mittag-Leffler system if and only if its inverse
system of `R`-duals `F.op ⋙ yoneda.obj (ModuleCat.of R (Shrink.{v} R))` is Mittag-Leffler. -/
public theorem solution {R : Type u} [CommRing R]
    [Small.{v} R] {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCat.{v} R)
    [∀ i, Module.Finite R (F.obj i)] [∀ i, Module.Projective R (F.obj i)] :
    F.IsMittagLefflerSystem ↔
      (F.op ⋙ yoneda.obj (ModuleCat.of R (Shrink.{v} R))).IsMittagLeffler := by
  refine ⟨fun h => h.2 _,
    fun h => ⟨fun i => Module.finitePresentation_of_projective R _, fun N => ?_⟩⟩
  rw [isMittagLeffler_dual_iff_range_lcomp_le F _ (Shrink.linearEquiv R R)] at h
  rw [isMittagLeffler_dual_iff_range_lcomp_le F N (LinearEquiv.refl R N)]
  intro i
  obtain ⟨i', u, hu⟩ := h i
  exact ⟨i', u, fun k v => range_lcomp_le_range_lcomp_of_dual N _ _ (hu k v)⟩

end Stacks.MittagLeffler.DualSystem

end

/-!
# A directed system of finite projective modules is Mittag-Leffler as soon as its dual is

Let `R` be a commutative ring and let `(M i, f i j)` be a directed system of `R`-modules whose
members are finitely generated and projective — a functor `F : J ⥤ ModuleCat R` — for instance
the system of finite free modules produced from a flat module by Lazard's theorem (Theorem 058G).
Dualizing the system into an `R`-module `N` gives the inverse system
`(Hom_R(M i, N), Hom_R(f i j, N))`, and `F` is a *Mittag-Leffler system* (Definition 059A) when
every one of those inverse systems is Mittag-Leffler and the members are of finite presentation.

For members which are finitely generated and projective a single test module suffices, namely
`N = R`: contraction is an isomorphism `Hom_R(M i, R) ⊗_R N ≅ Hom_R(M i, N)`, functorially in
`M i`, so the dual system into `N` is the dual system into `R` tensored with `N`; tensoring is
right exact, so it carries the containments of images that the Mittag-Leffler condition asks for
from the one system to the other. Together with criterion (4) of Proposition 059E this is what
makes the inverse system of duals `(Hom_R(M i, R), Hom_R(f i j, R))` a criterion for the colimit
`M = colim M i` to be a Mittag-Leffler module, which is how the remark is used (Lemma 059S).

## Main results

* `CategoryTheory.Functor.isMittagLefflerSystem_iff_isMittagLeffler_dual`: a diagram of finitely
  generated projective `R`-modules is a Mittag-Leffler system if and only if its inverse system
  of `R`-duals is Mittag-Leffler.

## Implementation notes

Departures from the source's form, none of them weakening it.

The remark reads "for `M` to be Mittag-Leffler it is enough for the inverse system of duals to be
Mittag-Leffler", and attributes that to criterion (4) of Proposition 059E. The content proper of
the remark is therefore the reduction of criterion (4) — the Mittag-Leffler condition on the dual
systems for *all* test modules — to the single test module `R`; the passage from criterion (4) to
`M` being Mittag-Leffler is Proposition 059E, which this file imports, and the production of a
system of finite free modules from flatness is Theorem 058G. So the statement is about the system
alone: no colimit cocone, no module `M`, and no flatness hypothesis, flatness being neither used
nor needed once the system is given. Composing with 059E, (4) ⟹ (1), recovers the remark as
stated.

Since the reverse implication is the specialization of criterion (4) to `N = R`, the criterion is
stated as an iff, which is stronger and is the form a reader wants.

The source's members are *free* and finite; they are here finitely generated and projective,
which is the generality of the contraction isomorphism `dualTensorHomEquiv` that the argument
runs on and also of `Module.finitePresentation_of_projective`, the finite presentation the
conclusion asks for. Directedness of `J` is not assumed either: the Mittag-Leffler condition is
transported index by index, so `J` is an arbitrary category, exactly as in Definition 059A.

The dual system is spelled as in Definition 059A: `F.op ⋙ yoneda.obj N` is the inverse system
`(Hom_R(M i, N), Hom_R(f i j, N))`, whose terms are the `R`-module homomorphisms `M i ⟶ N` and
whose transition maps are precomposition with the `f i j`. Its Mittag-Leffler condition is
Mathlib's `CategoryTheory.Functor.IsMittagLeffler` on the resulting `Type`-valued diagram.

Members and test modules live in one universe `v`, with `R` `v`-small, as in Proposition 059E;
this is what makes the left-hand side the source's condition for all `R`-modules. Smallness is
also what puts a copy of `R` itself in `Type v`, and the test module of the right-hand side is
that copy, `Shrink.{v} R`, which is `R` as an `R`-module (`Shrink.linearEquiv R R`). It holds
automatically when `R : Type v`, by `small_self`.

Faithfulness. (1) Every hypothesis is used by the conclusion: finiteness and projectivity of the
members are what make contraction an isomorphism, hence are what the reduction to the single test
module `R` rests on, and they are also what supplies the finite presentation of the members that
`IsMittagLefflerSystem` demands. Neither may be dropped: on a diagram with one object and no
non-identity morphism every dual system is Mittag-Leffler, all its transition maps being
identities, so the right-hand side holds while the left-hand side is finite presentation of the one
member — which fails for the free, not finitely generated `ℤ`-module `ℤ^(ℕ)`, and fails for the
finitely generated, not finitely presented module `R / (x₁, x₂, …)` over `R = ℤ[x₁, x₂, …]`.
`Small.{v} R` is used as described above. (2) The scalars and the base are the source's: one
commutative ring `R` throughout, the members are `R`-modules, the transition maps and the dual maps
are `R`-linear, the test modules are `R`-modules and nothing is localized or base changed. (3) The
dual systems are pinned, not merely asserted to exist: their terms are the `R`-module homomorphisms
`M i ⟶ N` and their transition maps are precomposition with the `f i j`, by the construction of
`F.op ⋙ yoneda.obj N`; the isomorphism `Hom_R(M i, R) ⊗_R N ≅ Hom_R(M i, N)` used to prove the
equivalence is Mathlib's contraction map `dualTensorHom`, which the statement does not need to
mention. (4) The instantiation is not degenerate: for `J` the finite subsets of a set `S` and `F`
the system of the free modules `R^i` with the coordinate inclusions, both sides hold, the dual maps
being split surjective, and both fail for `R = ℤ` and the system of the cyclic subgroups
`ℤ · (1 / n !)` of `ℚ`, whose `ℤ`-duals are `ℤ` with transition maps multiplication by `(n + 1)`,
so that the images at the first index are the `n ! ℤ` and never stabilize, `ℚ` being flat and
countably generated but not projective (Theorem 059Z). So neither side of the equivalence is
automatic.

## References

* [StacksProject 059G](https://stacks.math.columbia.edu/tag/059G)
-/



open CategoryTheory

@[expose] public section

namespace CategoryTheory.Functor

/-- **Stacks 059G.** Let `R` be a commutative ring and let `F : J ⥤ ModuleCat R` be a diagram
`(M i, f i j)` of finitely generated projective `R`-modules. Then `F` is a Mittag-Leffler system
— that is, the inverse system of duals `(Hom_R(M i, N), Hom_R(f i j, N))` is Mittag-Leffler for
every `R`-module `N`, and the `M i` are of finite presentation — if and only if the single
inverse system of `R`-duals `(Hom_R(M i, R), Hom_R(f i j, R))` is Mittag-Leffler.

Combined with criterion (4) of Proposition 059E, this says that for a flat module `M` written by
Lazard's theorem (Theorem 058G) as the colimit of a directed system of finite free modules
`M = colim M i`, it is enough for `(Hom_R(M i, R), Hom_R(f i j, R))` to be Mittag-Leffler for `M`
to be a Mittag-Leffler module. -/
@[stacks 059G "The content is the reduction of criterion (4) of 059E to the single test module
`R`, stated for finitely generated projective members and an arbitrary index category, and as an
iff; the passage to the colimit is 059E and the system comes from 058G. See the module
docstring."]
public theorem isMittagLefflerSystem_iff_isMittagLeffler_dual {R : Type u} [CommRing R]
    [Small.{v} R] {J : Type w} [Category.{w'} J] (F : J ⥤ ModuleCat.{v} R)
    [∀ i, Module.Finite R (F.obj i)] [∀ i, Module.Projective R (F.obj i)] :
    F.IsMittagLefflerSystem ↔
      (F.op ⋙ yoneda.obj (ModuleCat.of R (Shrink.{v} R))).IsMittagLeffler :=
  Stacks.MittagLeffler.DualSystem.solution F

end CategoryTheory.Functor

end
