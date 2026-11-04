module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs

@[expose] public section

universe u

/-!
# Irreducible components of a base change along a geometrically irreducible algebra

Let `k` be a field, let `S` be a geometrically irreducible `k`-algebra [stacks, 037L] and let `R`
be any `k`-algebra. Then taking images along `Spec (R ⊗[k] S) → Spec R` is a bijection from the
irreducible components of `Spec (R ⊗[k] S)` onto those of `Spec R`.

The morphism `Spec (R ⊗[k] S) ⟶ Spec R` is the base change of `Spec S ⟶ Spec k` along
`Spec R ⟶ Spec k`, so it is geometrically irreducible, geometric irreducibility being stable
under base change; and it is open, because `Spec (A ⊗[K] B) → Spec A` is open over a field `K`.
A geometrically irreducible open morphism induces a bijection on irreducible components, taking
a component to its image [stacks, 037A], and that bijection is the assertion of the lemma.

## Main results

* `Stacks.Irreducibility.ComponentsBijection.solution`: the statement of Stacks Tag 037O.

## Implementation notes

The source argues with minimal primes: flatness of `R → R ⊗[k] S` puts every minimal prime of
`R ⊗[k] S` over a minimal prime of `R` by going down, and for a prime `𝔭 ⊆ R` the ring
`(R ⊗[k] S)/𝔭(R ⊗[k] S) = (R/𝔭) ⊗[k] S` sits inside `κ(𝔭) ⊗[k] S`, whose spectrum is
irreducible by hypothesis, so it has a unique minimal prime. Read through the order-reversing
bijection between minimal primes and irreducible components of a spectrum [stacks, 00ES], that
is the statement proved here. The route taken instead is Mathlib's own: 037A is
`irreducibleComponentsEquivOfIsPreirreducibleFiber`, packaged for schemes as
`AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv`, so only the two inputs "geometrically
irreducible" and "open" have to be supplied, and both are available for this morphism — the
first by base change from the hypothesis on `S`, the second as
`PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`. The fibre irreducibility that
the source obtains by hand from `κ(𝔭) ⊗[k] S` is exactly what geometric irreducibility of the
morphism provides.

Mathlib phrases 037A as an equivalence of the subtypes of irreducible components;
`bijOn_image_irreducibleComponents` reads it as a bijection of sets, which is the form the
statement asks for. What that reading needs is that taking images and taking preimages are
mutually inverse on components, `f ⁻¹' (f '' Z) = Z` for `Z` a component of the source and
`f '' (f ⁻¹' T) = T` for `T` a component of the target; the first is the round trip of the
equivalence and the second is surjectivity of `f`, which geometric irreducibility supplies.

The scheme-level statement is used on the affine spectra directly: the carrier of
`Spec (of R)` and `PrimeSpectrum R` are definitionally equal, and so are
`(Spec.map (ofHom f)).base` and `PrimeSpectrum.comap f`, so no transport intervenes.

## References

* [Stacks Project, Tag 037O](https://stacks.math.columbia.edu/tag/037O)
-/

namespace Stacks.Irreducibility.ComponentsBijection



open AlgebraicGeometry CategoryTheory CommRingCat TensorProduct

/-- Geometric irreducibility is stable under base change: if `S` is a geometrically irreducible
`k`-algebra, then for every `k`-algebra `R` the morphism `Spec (R ⊗[k] S) ⟶ Spec R` induced by
`r ↦ r ⊗ₜ 1` is geometrically irreducible, being the base change of `Spec S ⟶ Spec k` along
`Spec R ⟶ Spec k`. -/
private theorem geometricallyIrreducible_specMap_algebraMap_tensorProduct (k R S : Type u)
    [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    [Algebra.IsGeometricallyIrreducible k S] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))) := by
  rw [← pullbackSpecIso_inv_fst' k R S]; infer_instance

/-- **Stacks 037A** as a bijection of sets: for an open geometrically irreducible morphism of
schemes `f : X ⟶ Y`, taking images along `f` is a bijection from the irreducible components of
`X` onto those of `Y`, with inverse taking preimages. This is
`AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv` read as a `Set.BijOn`. -/
private theorem bijOn_image_irreducibleComponents {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] (hf : IsOpenMap f.base) :
    Set.BijOn (f.base '' ·) (irreducibleComponents X) (irreducibleComponents Y) :=
  let e := Scheme.Hom.irreducibleComponentsEquiv f hf
  Set.InvOn.bijOn (f' := (f.base ⁻¹' ·))
    ⟨fun _ hZ => congrArg Subtype.val (e.symm_apply_apply ⟨_, hZ⟩),
      fun _ _ => Set.image_preimage_eq _ f.surjective⟩
    (fun _ hZ => (e ⟨_, hZ⟩).2) fun _ hT => (e.symm ⟨_, hT⟩).2

/-- For a field `k`, a geometrically irreducible `k`-algebra `S` and any `k`-algebra `R`, taking
images along `PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))` is a bijection from the irreducible
components of `Spec (R ⊗[k] S)` onto the irreducible components of `Spec R`. -/
public theorem solution (k R S : Type u) [Field k] [CommRing R] [Algebra k R] [CommRing S]
    [Algebra k S] [Algebra.IsGeometricallyIrreducible k S] :
    Set.BijOn (fun Z ↦ PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)) '' Z)
      (irreducibleComponents (PrimeSpectrum (R ⊗[k] S)))
      (irreducibleComponents (PrimeSpectrum R)) :=
  have := geometricallyIrreducible_specMap_algebraMap_tensorProduct k R S
  bijOn_image_irreducibleComponents (Spec.map (ofHom (algebraMap R (R ⊗[k] S))))
    PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

end Stacks.Irreducibility.ComponentsBijection

/-!
# Irreducible components of a base change along a geometrically irreducible algebra

Let `k` be a field, let `S` be a geometrically irreducible `k`-algebra [stacks, 037L] and let `R`
be an arbitrary `k`-algebra. Then the continuous map
`Spec (R ⊗[k] S) → Spec R` induced by the structure map `R → R ⊗[k] S` sets up a bijection
between the irreducible components of `Spec (R ⊗[k] S)` and those of `Spec R`.

The map is open and surjective with irreducible fibres: it is the base change of
`Spec S → Spec k` along `Spec R → Spec k`, geometric irreducibility of `S` says exactly that all
fibres of `Spec S → Spec k` over field-valued points are irreducible and is stable under base
change, and a morphism to the spectrum of a field is universally open. For such a map the image
of an irreducible component is an irreducible component and taking images is a bijection on
irreducible components, with inverse given by taking preimages [stacks, 037A]. The induced map of
the statement is therefore the image map of `Spec (R ⊗[k] S) → Spec R`, namely
`fun Z ↦ PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)) '' Z`.

Equivalently, in the language of the source's own proof: minimal primes of `R ⊗[k] S` correspond
to minimal primes of `R` under contraction along `R → R ⊗[k] S`, which is the same statement read
through the order-reversing bijection between minimal primes and irreducible components of a
spectrum [stacks, 00ES].

## Main results

* `Algebra.IsGeometricallyIrreducible.bijOn_irreducibleComponents_primeSpectrum_tensorProduct`:
  for a geometrically irreducible `k`-algebra `S` and any `k`-algebra `R`, taking images along
  `Spec (R ⊗[k] S) → Spec R` is a bijection from the irreducible components of
  `Spec (R ⊗[k] S)` onto the irreducible components of `Spec R`.

## Implementation notes

The source says that the map *induces a bijection on irreducible components*; the induced map is
pinned here rather than merely asserted to exist, as `Set.BijOn` for the concrete function
`fun Z ↦ PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)) '' Z` between the two sets
`irreducibleComponents (PrimeSpectrum _)`. This is Mathlib's choice of direction and of induced
map: `AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv`, the scheme-level statement for an
open geometrically irreducible morphism, is the equivalence whose forward map is `Z ↦ f '' Z`.
The `Set.BijOn` spelling says three things a bare equivalence of subtypes would not: that the
image of a component *is* a component, that distinct components have distinct images, and that
every component of `Spec R` is hit. The inverse map is `T ↦ PrimeSpectrum.comap _ ⁻¹' T`, which is
`preimage_mem_irreducibleComponents_of_isPreirreducible_fiber` applied to the same map,
and is therefore not restated here.

The spectra are the absolute ones, `PrimeSpectrum R` and `PrimeSpectrum (R ⊗[k] S)`, in the
algebraic spelling that tags 037K, 037M and 037U use for the same kind of conclusion, and the map
is `PrimeSpectrum.comap` of the structure map `algebraMap R (R ⊗[k] S)`, which is
`Algebra.TensorProduct.includeLeftRingHom`, `r ↦ r ⊗ₜ 1`. The carrier of the scheme
`Spec (R ⊗[k] S)` is homeomorphic to `PrimeSpectrum (R ⊗[k] S)`, so the affine statement and the
scheme-level one carry the same content; the algebraic form keeps the lemma usable without going
through the scheme-theoretic API.

The three rings lie in one universe. This follows `Algebra.IsGeometricallyIrreducible`
[stacks, 037L], whose quantifier over field extensions is `AlgebraicGeometry.geometrically` and
therefore single-universe; the same discipline is what makes the base-change route above
available, since `AlgebraicGeometry.pullbackSpecIso` identifies `Spec (R ⊗[k] S)` with a pullback
of schemes only when `k`, `R` and `S` share a universe.

Faithfulness to the source. (1) No hypothesis is idle: `R` and `S` both occur in the conclusion,
and geometric irreducibility of `S` cannot be weakened to irreducibility of `Spec S`, since for
`k = ℚ` and `R = S = ℚ(i)` the spectrum of `ℚ(i) ⊗[ℚ] ℚ(i) ≅ ℚ(i) × ℚ(i)` has two irreducible
components while `Spec ℚ(i)` is a point. (2) The scalars and base are the source's: the tensor
product is over the field `k` itself, along `algebraMap k R` and `algebraMap k S`, and it is the
same `k` whose field extensions geometric irreducibility of `S` quantifies over; no localization
or extension of scalars intervenes, and the bijection is between components of the spectra of `R`
and of `R ⊗[k] S`, not of a further base change. (3) The map the source names is pinned: it is
`PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))`, the spectrum of the canonical map
`r ↦ r ⊗ₜ 1`, and the bijection is its own action on subsets, not an unnamed one. (4) The
instantiation is not degenerate: with `k = ℚ`, `S = ℚ[X]`, which is geometrically irreducible
because `ℚ[X] ⊗[ℚ] k' ≅ k'[X]` is a domain for every field extension `k'/ℚ`, and `R = ℚ × ℚ`,
whose spectrum has two irreducible components, the ring `R ⊗[ℚ] S ≅ ℚ[X] × ℚ[X]` also has two,
and the statement matches them up; both sets of components are nonempty and have more than one
element, so neither side is vacuous or a singleton.

## References

* [Stacks Project, Tag 037O](https://stacks.math.columbia.edu/tag/037O)
-/

@[expose] public section



open TensorProduct

/-- **Stacks 037O.** Let `k` be a field, let `S` be a geometrically irreducible `k`-algebra and
let `R` be any `k`-algebra. Then the map `Spec (R ⊗[k] S) → Spec R` induced by `r ↦ r ⊗ₜ 1`
induces a bijection on irreducible components: taking images along it is a bijection from the
irreducible components of `Spec (R ⊗[k] S)` onto the irreducible components of `Spec R`. -/
@[stacks 037O]
public theorem
    Algebra.IsGeometricallyIrreducible.bijOn_irreducibleComponents_primeSpectrum_tensorProduct
    (k R S : Type u) [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    [Algebra.IsGeometricallyIrreducible k S] :
    Set.BijOn (fun Z ↦ PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)) '' Z)
      (irreducibleComponents (PrimeSpectrum (R ⊗[k] S)))
      (irreducibleComponents (PrimeSpectrum R)) := by apply
          Stacks.Irreducibility.ComponentsBijection.solution

end
