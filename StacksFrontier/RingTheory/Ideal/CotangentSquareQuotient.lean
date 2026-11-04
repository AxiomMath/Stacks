module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The conormal module of an ideal is unchanged by dividing out its square

Let `R → S` be a surjective ring map whose kernel is the square `J ^ 2` of an ideal `J ⊆ R`, and
let `I = J·S` be the image of `J`. Then `I ^ 2 = 0`, and the natural map `J/J² ⟶ I/I²` of
`Ideal.mapCotangent` is **bijective**: both sides are `J/J²`.

This is the chart-level content of [Stacks Project, Tag 04F0], which asserts that the conormal
sheaf of an immersion `i : Z ⟶ X` agrees with the conormal sheaf of the inclusion of `Z` into its
first-order infinitesimal neighbourhood `Z₁` of [Stacks Project, Tag 04EY]. On an affine open `V`
of the ambient open subscheme, `J` is the ideal cutting out `Z`, the chart of `Z₁` is the quotient
by `J ^ 2` (`Stacks.Thickenings.ker_app_firstOrderι`) and the ideal cutting `Z` out of that chart
is `J·S` (`Stacks.Thickenings.ker_app_nthOrderInclusion`), so the two conormal sections of
[Stacks Project, Tag 01R3] part (2) are the two sides of the bijection proved here, and the
induced map of [Stacks Project, Tag 01R4] is the map proved bijective.

**Nothing here carries a `@[stacks 04F0]` attribute**, and that is deliberate: Tag 04F0 asserts an
isomorphism of *sheaves of modules*, and a statement about one chart is not that statement. That
sheaf-level assertion is proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalConormalSheaf`, as
`Stacks.Thickenings.isIso_conormalTransitivityMap_nthOrderInclusion`, which carries the tag; the
chart input it uses is `Stacks.Thickenings.chart_app_surjective_and_ker`, phrased for the section
maps of the neighbourhood rather than for an abstract algebra as here.

## Main definitions

* `Stacks.RingTheory.cotangentMapOfAlgebraMap` is `Ideal.mapCotangent` for the structure map of an
  `R`-algebra `S`, from `J/J²` to `(J·S)/(J·S)²`.
* `Stacks.RingTheory.cotangentEquivOfKerEqSq` is the resulting `R`-linear equivalence, when
  `R → S` is surjective with kernel `J ^ 2`.
* `Stacks.RingTheory.cotangentEquivCotangentIdeal` is the canonical instance `S = R ⧸ J ^ 2`,
  where the target is `Ideal.cotangentIdeal`.

## Main results

* `Stacks.RingTheory.map_sq_eq_bot_of_ker_eq_sq`: the extended ideal has vanishing square, so
  `R → S` is a first-order thickening in the sense of [Stacks Project, Tag 04EX] part (2).
* `Stacks.RingTheory.injective_cotangentMapOfAlgebraMap` and
  `Stacks.RingTheory.surjective_cotangentMapOfAlgebraMap`.

## Implementation notes

Injectivity and surjectivity are proved directly from `Ideal.mapCotangent_toCotangent` rather than
through Mathlib's `Ideal.mapCotangent_ker_of_surjective` and
`Ideal.mapCotangent_surjective_of_comap_eq`, whose hypothesis is phrased as
`I.comap (algebraMap R S) = RingHom.ker (algebraMap R S) ⊔ J`. That hypothesis is equivalent to
the one used here, but the two statements then have to be matched against the shapes
`Submodule.comap J.subtype (RingHom.ker (algebraMap R S) ⊓ J)` and `Algebra.ofId`, which is longer
than the two three-line arguments it replaces.

The surjection is taken as a hypothesis on `algebraMap R S` rather than `S` being presented as
`R ⧸ J ^ 2`, because the consumer does not have the quotient on the nose: the chart ring of an
infinitesimal neighbourhood is the sections of a subscheme's structure sheaf, which is only
*isomorphic* to the quotient. `Stacks.RingTheory.cotangentEquivCotangentIdeal` records the
quotient case.

## References

* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

universe u

namespace Stacks.RingTheory

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal R)

/-- The ideal `J` is contained in the preimage of its extension `J·S` under the structure map of an
`R`-algebra `S`; this is the hypothesis `Ideal.mapCotangent` consumes. -/
theorem le_comap_map_algebraMap :
    J ≤ Ideal.comap (Algebra.ofId R S) (J.map (algebraMap R S)) := fun _ hx ↦
  Ideal.mem_map_of_mem _ hx

/-- The natural map `J/J² ⟶ (J·S)/(J·S)²` induced by the structure map of an `R`-algebra `S`.

This is `Ideal.mapCotangent` for `Algebra.ofId R S`; it sends the class of `a : J` to the class of
`algebraMap R S a`. -/
noncomputable def cotangentMapOfAlgebraMap :
    J.Cotangent →ₗ[R] (J.map (algebraMap R S)).Cotangent :=
  Ideal.mapCotangent J (J.map (algebraMap R S)) (Algebra.ofId R S) (le_comap_map_algebraMap J)

/-- `Stacks.RingTheory.cotangentMapOfAlgebraMap` sends the class of `x : J` in `J/J²` to the class
of `algebraMap R S x` in `(J·S)/(J·S)²`. -/
@[simp]
theorem cotangentMapOfAlgebraMap_toCotangent (x : J) :
    cotangentMapOfAlgebraMap (S := S) J (J.toCotangent x) =
      (J.map (algebraMap R S)).toCotangent
        ⟨algebraMap R S (x : R), Ideal.mem_map_of_mem _ x.2⟩ :=
  Ideal.mapCotangent_toCotangent _ _ _ _ x

/-- **The extended ideal has vanishing square.** If the kernel of `algebraMap R S` is `J ^ 2` then
`(J·S) ^ 2 = 0`, because `(J·S) ^ 2` is the image of `J ^ 2`, which is the kernel. -/
theorem map_sq_eq_bot_of_ker_eq_sq (hker : RingHom.ker (algebraMap R S) = J ^ 2) :
    J.map (algebraMap R S) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, ← hker]
  exact le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx ↦ by
    simpa [RingHom.mem_ker] using hx) bot_le

/-- **`J/J² ⟶ (J·S)/(J·S)²` is injective.** Two classes with the same image differ by an element of
`(J·S) ^ 2`, which is zero by `Stacks.RingTheory.map_sq_eq_bot_of_ker_eq_sq`; so their difference
lies in the kernel `J ^ 2` of `algebraMap R S` and the two classes in `J/J²` already agree. -/
theorem injective_cotangentMapOfAlgebraMap (hker : RingHom.ker (algebraMap R S) = J ^ 2) :
    Function.Injective (cotangentMapOfAlgebraMap (S := S) J) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := J.toCotangent_surjective x
  obtain ⟨b, rfl⟩ := J.toCotangent_surjective y
  rw [cotangentMapOfAlgebraMap_toCotangent, cotangentMapOfAlgebraMap_toCotangent,
    Ideal.toCotangent_eq, map_sq_eq_bot_of_ker_eq_sq J hker, Ideal.mem_bot] at hxy
  rw [Ideal.toCotangent_eq, ← hker, RingHom.mem_ker, map_sub]
  exact hxy

/-- **`J/J² ⟶ (J·S)/(J·S)²` is surjective** whenever `algebraMap R S` is, since then every element
of `J·S` is the image of an element of `J`. No hypothesis on the kernel is needed. -/
theorem surjective_cotangentMapOfAlgebraMap (hsurj : Function.Surjective (algebraMap R S)) :
    Function.Surjective (cotangentMapOfAlgebraMap (S := S) J) := by
  intro y
  obtain ⟨b, rfl⟩ := (J.map (algebraMap R S)).toCotangent_surjective y
  obtain ⟨a, ha, hab⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 b.2
  refine ⟨J.toCotangent ⟨a, ha⟩, ?_⟩
  rw [cotangentMapOfAlgebraMap_toCotangent]
  exact congrArg _ (Subtype.ext hab)

/-- **Dividing out the square of an ideal does not change its conormal module.** For a surjection
`R ⟶ S` with kernel `J ^ 2`, the natural map identifies `J/J²` with `(J·S)/(J·S)²`.

This is the chart-level form of [Stacks Project, Tag 04F0]; see the module docstring. -/
noncomputable def cotangentEquivOfKerEqSq (hker : RingHom.ker (algebraMap R S) = J ^ 2)
    (hsurj : Function.Surjective (algebraMap R S)) :
    J.Cotangent ≃ₗ[R] (J.map (algebraMap R S)).Cotangent :=
  LinearEquiv.ofBijective (cotangentMapOfAlgebraMap J)
    ⟨injective_cotangentMapOfAlgebraMap J hker, surjective_cotangentMapOfAlgebraMap J hsurj⟩

/-- The equivalence `Stacks.RingTheory.cotangentEquivOfKerEqSq` agrees with
`Stacks.RingTheory.cotangentMapOfAlgebraMap`. -/
@[simp]
theorem cotangentEquivOfKerEqSq_apply (hker : RingHom.ker (algebraMap R S) = J ^ 2)
    (hsurj : Function.Surjective (algebraMap R S)) (x : J.Cotangent) :
    cotangentEquivOfKerEqSq (S := S) J hker hsurj x = cotangentMapOfAlgebraMap J x := rfl

/-- The canonical instance of `Stacks.RingTheory.cotangentEquivOfKerEqSq`: the conormal module of
`J` is identified with the conormal module of `Ideal.cotangentIdeal J`, the image of `J` in
`R ⧸ J ^ 2`. -/
noncomputable def cotangentEquivCotangentIdeal :
    J.Cotangent ≃ₗ[R] (J.map (algebraMap R (R ⧸ J ^ 2))).Cotangent :=
  cotangentEquivOfKerEqSq J (by simp [Ideal.Quotient.algebraMap_eq])
    (by simpa [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective)

end Stacks.RingTheory

end
