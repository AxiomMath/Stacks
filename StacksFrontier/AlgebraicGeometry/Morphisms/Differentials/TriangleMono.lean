module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials

/-!
# Differentials over a monomorphic base change of base

Let `h : Y ⟶ Z` and `k : Z ⟶ Z'` be morphisms of schemes with `k` a **monomorphism** — for
instance an immersion. Then the canonical map

`Ω_{Y/Z'} ⟶ Ω_{Y/Z}`

of [Stacks Project, Tag 01UX] is an isomorphism: it is always an epimorphism, and the term of
the exact sequence to its left is `h^* Ω_{Z/Z'}`, which vanishes because a monomorphism has no
differentials ([Stacks Project, Tag 01UY]).

So for a thickening `Z ⊂ Z'` the differentials of a `Z'`-scheme lying over `Z` may be read
relative to `Z` or relative to `Z'` interchangeably. This is the identification left implicit by
[Stacks Project, Tag 0CK2], which acts on its lifting sheaf by
`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` where the general [Stacks Project, Tag 04FJ] acts by
`Hom_{𝒪_X}(a^*Ω_{Y/Z'}, 𝒞_{X/X'})`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentialsOfEq`: the canonical map
  `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` for a structure morphism `p : Y ⟶ Z'` presented as a composite
  `h ≫ k` by an equality rather than on the nose. This is the shape in which the map is needed:
  in a cartesian square the structure morphism of `Y` over `Z'` arrives as `j ≫ h'` and is only
  *equal* to `h ≫ k`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isZero_pullback_relativeDifferentials_of_mono`: `h^*Ω_{Z/Z'}`
  vanishes for `k` a monomorphism.
* `AlgebraicGeometry.Scheme.Hom.mono_toRelativeDifferentials_of_mono` and
  `AlgebraicGeometry.Scheme.Hom.isIso_toRelativeDifferentials_of_mono`: the canonical map
  `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` is a monomorphism, hence an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isIso_toRelativeDifferentialsOfEq` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoOfEq`: the same for the shape with the
  factorisation given by an equality, and the resulting isomorphism.

## Implementation notes

The displaced-composite shape is handled by `subst` on the structure morphism, which is a
variable in `AlgebraicGeometry.Scheme.Hom.isIso_toRelativeDifferentialsOfEq`; after the
substitution the map is `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials` itself, the
commutation proof entering only as an argument of a proposition. No `eqToHom` and no transport
of a statement along an equality of objects is involved.

Exactness at the middle term is `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_exact`;
a short complex whose first map is zero is exact exactly when its second map is a monomorphism,
and the first map here is zero because its source is a zero object. Monomorphism together with
epimorphism gives an isomorphism because sheaves of modules on a scheme form an abelian, hence
balanced, category.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX), the exact sequence.
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY), the vanishing of the
  differentials of a monomorphism.
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2), which uses the
  identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y Z Z' : Scheme.{u}}

/-- **The pullback of the differentials of a monomorphism vanishes.** For `k : Z ⟶ Z'` a
monomorphism and `h : Y ⟶ Z` any morphism, `h^*Ω_{Z/Z'}` is a zero object: `Ω_{Z/Z'}` is zero by
[Stacks Project, Tag 01UY] and the module pullback, being a left adjoint, preserves the zero
object. -/
theorem isZero_pullback_relativeDifferentials_of_mono (h : Y ⟶ Z) (k : Z ⟶ Z') [Mono k] :
    IsZero ((Scheme.Modules.pullback h).obj (relativeDifferentials k)) := by
  have : Functor.IsLeftAdjoint (Scheme.Modules.pullback h) :=
    ⟨Scheme.Modules.pushforward h, ⟨Scheme.Modules.pullbackPushforwardAdjunction h⟩⟩
  exact Functor.map_isZero _ (isZero_relativeDifferentials_of_mono k)

/-- **The canonical map `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` is a monomorphism when `Z ⟶ Z'` is.** The sequence
`h^*Ω_{Z/Z'} ⟶ Ω_{Y/Z'} ⟶ Ω_{Y/Z}` of [Stacks Project, Tag 01UX] is exact at the middle term,
and its first map is zero because its source is a zero object. -/
theorem mono_toRelativeDifferentials_of_mono (h : Y ⟶ Z) (k : Z ⟶ Z') [Mono k] :
    Mono (toRelativeDifferentials h k) := by
  obtain ⟨hzero, hexact⟩ := toRelativeDifferentials_exact h k
  refine (ShortComplex.exact_iff_mono _ ?_).mp hexact
  exact (isZero_pullback_relativeDifferentials_of_mono h k).eq_of_src _ _

/-- **The canonical map `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` is an isomorphism when `Z ⟶ Z'` is a
monomorphism.** It is an epimorphism by [Stacks Project, Tag 01UX] and a monomorphism by
`AlgebraicGeometry.Scheme.Hom.mono_toRelativeDifferentials_of_mono`; sheaves of modules on a
scheme form a balanced category. -/
theorem isIso_toRelativeDifferentials_of_mono (h : Y ⟶ Z) (k : Z ⟶ Z') [Mono k] :
    IsIso (toRelativeDifferentials h k) :=
  have := mono_toRelativeDifferentials_of_mono h k
  have := toRelativeDifferentials_epi h k
  isIso_of_mono_of_epi _

/-- **The canonical map `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` for a structure morphism presented as a composite
by an equality.** This is `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials` with the
composite `h ≫ k` replaced by any `p : Y ⟶ Z'` equal to it; in a cartesian square the structure
morphism of `Y` over `Z'` arrives as `j ≫ h'` and is equal to, not syntactically, `h ≫ k`. -/
noncomputable def toRelativeDifferentialsOfEq (p : Y ⟶ Z') (h : Y ⟶ Z) (k : Z ⟶ Z')
    (hp : p = h ≫ k) : relativeDifferentials p ⟶ relativeDifferentials h :=
  ((Scheme.Modules.pullbackId Y).inv.app (relativeDifferentials p)) ≫
    relativeDifferentialsMap (𝟙 Y) p h k (by rw [Category.id_comp, hp])

/-- The displaced map of `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentialsOfEq` is
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials` when the factorisation holds on the
nose. -/
theorem toRelativeDifferentialsOfEq_self (h : Y ⟶ Z) (k : Z ⟶ Z') :
    toRelativeDifferentialsOfEq (h ≫ k) h k rfl = toRelativeDifferentials h k := rfl

/-- **The displaced canonical map is an isomorphism when `Z ⟶ Z'` is a monomorphism.** -/
theorem isIso_toRelativeDifferentialsOfEq (p : Y ⟶ Z') (h : Y ⟶ Z) (k : Z ⟶ Z') [Mono k]
    (hp : p = h ≫ k) : IsIso (toRelativeDifferentialsOfEq p h k hp) := by
  subst hp
  exact isIso_toRelativeDifferentials_of_mono h k

/-- **`Ω_{Y/Z'} ≅ Ω_{Y/Z}` for a thickening `Z ⊂ Z'`**, as an isomorphism, with the structure
morphism of `Y` over `Z'` presented as a composite by an equality. -/
noncomputable def relativeDifferentialsIsoOfEq (p : Y ⟶ Z') (h : Y ⟶ Z) (k : Z ⟶ Z') [Mono k]
    (hp : p = h ≫ k) : relativeDifferentials p ≅ relativeDifferentials h :=
  have := isIso_toRelativeDifferentialsOfEq p h k hp
  asIso (toRelativeDifferentialsOfEq p h k hp)

end AlgebraicGeometry.Scheme.Hom

end
