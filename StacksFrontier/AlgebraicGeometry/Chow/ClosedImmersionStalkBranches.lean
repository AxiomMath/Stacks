module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.ClosedImmersionStalk

/-!
# The branches of a closed subscheme cut out by components of the ambient scheme

Let `h : T ⟶ V` be a closed immersion of schemes the image of each of whose irreducible
components is an irreducible component of `V` — that is, `T` is cut out by components of `V` and
not merely by closed subsets of them. This file carries that statement from the irreducible
components to the **local rings**: at a point `t` of `T`, every minimal prime of `𝒪_{T, t}`
contracts along the surjection `𝒪_{V, h t} → 𝒪_{T, t}` to a minimal prime of `𝒪_{V, h t}`.

That is more than
`AlgebraicGeometry.Scheme.Hom.mem_minimalPrimes_iff_comap_mem_minimalPrimes_ker_stalkMap`, which
identifies the minimal primes of `𝒪_{T, t}` with the primes *minimal over the kernel* of the
stalk map; a prime minimal over an ideal need not be a minimal prime of the ring, and that it is
one here is exactly the hypothesis on the components.

The irreducible components of a scheme through a point are the minimal primes of its local ring
there, `AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes`, a component corresponding to
the minimal prime whose image under `Spec 𝒪_{X, x} ⟶ X` is its generic point. The statement is
therefore read off the naturality of `Spec 𝒪_{X, x} ⟶ X` in `X`
(`AlgebraicGeometry.Scheme.Hom.fromSpecStalk_comap_stalkMap`): a minimal prime of `𝒪_{T, t}` is
carried to the generic point of a component `C` of `T`, so its contraction is carried to the
generic point of the image of `C`, which is a component of `V` by hypothesis, and hence is
minimal.

This is the local form of the step in the proof of Stacks 0EQ2 which groups the branches at a
point over the irreducible components through it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.comap_stalkMap_mem_minimalPrimes`: the statement above.

## References

* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T V : Scheme.{u}}

/-- **The branches of a closed subscheme cut out by components of the ambient scheme are branches
of the ambient scheme.** Let `h : T ⟶ V` be a closed immersion of schemes such that the image of
every irreducible component of `T` is an irreducible component of `V`, and let `t` be a point of
`T`. Then every minimal prime of `𝒪_{T, t}` contracts along `𝒪_{V, h t} → 𝒪_{T, t}` to a minimal
prime of `𝒪_{V, h t}`.

A minimal prime `𝔮` of `𝒪_{T, t}` is carried by `Spec 𝒪_{T, t} ⟶ T` to the generic point `η` of
an irreducible component `C` of `T` through `t`
(`AlgebraicGeometry.exists_irreducibleComponents_fromSpecStalk_eq`). By naturality its
contraction is carried by `Spec 𝒪_{V, h t} ⟶ V` to `h(η)`, which is a generic point of the image
of `C` because `h` is a closed embedding; and that image is an irreducible component of `V`
through `h t` by hypothesis. The minimal prime of `𝒪_{V, h t}` attached to that component is
carried to the same point (`AlgebraicGeometry.exists_mem_minimalPrimes_fromSpecStalk_eq`), and
`Spec 𝒪_{V, h t} ⟶ V` is injective, so the contraction *is* that minimal prime. -/
theorem comap_stalkMap_mem_minimalPrimes (h : T ⟶ V) [IsClosedImmersion h]
    (himg : ∀ C ∈ irreducibleComponents T, (h : T → V) '' C ∈ irreducibleComponents V)
    (t : T) (J : Ideal (T.presheaf.stalk t)) (hJ : J ∈ minimalPrimes (T.presheaf.stalk t)) :
    Ideal.comap (h.stalkMap t).hom J ∈ minimalPrimes (V.presheaf.stalk (h t)) := by
  have hJp : J.IsPrime := hJ.1.1
  have hemb := h.isClosedEmbedding
  set q : PrimeSpectrum (T.presheaf.stalk t) := ⟨J, hJp⟩ with hqdef
  obtain ⟨C, htC, hgen⟩ := exists_irreducibleComponents_fromSpecStalk_eq t q hJ
  -- the image of the component is a component of `V`, through `h t`
  have hW : (h : T → V) '' (C : Set T) ∈ irreducibleComponents V := himg _ C.2
  have hmem : h t ∈ (h : T → V) '' (C : Set T) := ⟨t, htC, rfl⟩
  -- the image of the generic point of `C` is the generic point of the image of `C`
  have hgenim : IsGenericPoint ((h : T → V) (genericPoints.ofComponent C))
      ((h : T → V) '' (C : Set T)) := by
    change closure _ = _
    rw [← Set.image_singleton, hemb.closure_image_eq,
      (genericPoints.isGenericPoint_ofComponent C).def]
  have hofc : (h : T → V) (genericPoints.ofComponent C) =
      (genericPoints.ofComponent (⟨_, hW⟩ : irreducibleComponents V) : V) :=
    hgenim.eq (genericPoints.isGenericPoint_ofComponent (⟨_, hW⟩ : irreducibleComponents V))
  -- the minimal prime of `𝒪_{V, h t}` attached to that component
  obtain ⟨p, hpmin, hp⟩ := exists_mem_minimalPrimes_fromSpecStalk_eq (h t)
    (⟨_, hW⟩ : irreducibleComponents V) hmem
  have hpt : PrimeSpectrum.comap (h.stalkMap t).hom q = p :=
    (V.fromSpecStalk (h t)).isEmbedding.injective
      (by rw [fromSpecStalk_comap_stalkMap h t q, hgen, hofc, hp])
  have heq : Ideal.comap (h.stalkMap t).hom J = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpt
  exact heq ▸ hpmin

end AlgebraicGeometry.Scheme.Hom

end
