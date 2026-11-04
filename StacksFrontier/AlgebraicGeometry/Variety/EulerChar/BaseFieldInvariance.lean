module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invariance of the Euler characteristic under extension of the ground field

For an extension of fields `k'/k`, a scheme `X` proper over `k`, a coherent `𝒪_X`-module `ℱ`
and the pullback `ℱ'` of `ℱ` to the base change `X' = X_{k'}`, the Euler characteristics agree:
`χ(X, ℱ) = χ(X', ℱ')`.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_baseChange_field`: the invariance, for an arbitrary
  cartesian square presenting the base change.
* `AlgebraicGeometry.eulerCharacteristic_pullback_specMapAlgebraMap`: the same for the
  canonical pullback.

## Implementation notes

The Euler characteristic is the alternating sum of the dimensions of the cohomology groups, so
it depends on no more than those dimensions; each of them is unchanged by the extension by
[Stacks, Tag 02KH] part (2) over a field, available here as
`AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field`.

Properness of the base-changed structure morphism is stability of properness under base change,
and coherence of the pullback is [Stacks, Tag 0EBF]; the latter needs the base change to be
locally Noetherian, which comes from its being of finite type over a field. Both are passed to
`AlgebraicGeometry.eulerCharacteristic` explicitly, since neither is available to instance
search from the cartesian square alone.

## References

* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X' X : Scheme.{u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k')) (f : X ⟶ Spec (.of k))

/-- A base change of a proper morphism along an extension of the ground field is proper. -/
public theorem isProper_of_isPullback_specMapAlgebraMap
    (h : IsPullback g' f' f (specMapAlgebraMap k k')) [IsProper f] : IsProper f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) h inferInstance

/-- A base change of a proper scheme over a field along an extension of that field is locally
Noetherian, being of finite type over a field. -/
@[ega "IV 6.7.1" "X proper over k"]
public theorem isLocallyNoetherian_of_isPullback_specMapAlgebraMap
    (h : IsPullback g' f' f (specMapAlgebraMap k k')) [IsProper f] : IsLocallyNoetherian X' :=
  have := isProper_of_isPullback_specMapAlgebraMap k k' g' f' f h
  LocallyOfFiniteType.isLocallyNoetherian f'

/-- The pullback of a coherent module to a base change of a proper scheme over a field along an
extension of that field is coherent. -/
public theorem isCoherent_pullback_of_isPullback_specMapAlgebraMap
    (h : IsPullback g' f' f (specMapAlgebraMap k k')) [IsProper f] (F : X.Modules)
    [F.IsCoherent] : ((Scheme.Modules.pullback g').obj F).IsCoherent :=
  have := isLocallyNoetherian_of_isPullback_specMapAlgebraMap k k' g' f' f h
  isCoherent_pullback g' F

/-- **The Euler characteristic is unchanged by extension of the ground field.** Let `k'/k` be an
extension of fields, let `X` be a proper scheme over `k`, let `ℱ` be a coherent `𝒪_X`-module and
let `ℱ'` be the pullback of `ℱ` to a base change `X'` of `X` to `k'`. Then
`χ(X, ℱ) = χ(X', ℱ')`. -/
@[stacks 08AB, ega "III 7.9.7" "special case"]
public theorem eulerCharacteristic_baseChange_field
    (h : IsPullback g' f' f (specMapAlgebraMap k k')) [IsProper f] (F : X.Modules)
    [F.IsCoherent] :
    eulerCharacteristic k f F =
      @eulerCharacteristic k' _ X' f' (isProper_of_isPullback_specMapAlgebraMap k k' g' f' f h)
        ((Scheme.Modules.pullback g').obj F)
        (isCoherent_pullback_of_isPullback_specMapAlgebraMap k k' g' f' f h F) :=
  have := isProper_of_isPullback_specMapAlgebraMap k k' g' f' f h
  have := isCoherent_pullback_of_isPullback_specMapAlgebraMap k k' g' f' f h F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  (eulerCharacteristic_eq_of_finrank_cohomologyOverField_eq k k' f F f'
    ((Scheme.Modules.pullback g').obj F)
    fun n => finrank_cohomologyOverField_baseChange_field k k' g' f' f h F n).symm

/-- **The Euler characteristic is unchanged by extension of the ground field**, for the
canonical base change `X' = X ×_{Spec k} Spec k'`. -/
public theorem eulerCharacteristic_pullback_specMapAlgebraMap [IsProper f] (F : X.Modules)
    [F.IsCoherent] :
    eulerCharacteristic k f F =
      @eulerCharacteristic k' _ (pullback f (specMapAlgebraMap k k'))
        (pullback.snd f (specMapAlgebraMap k k')) inferInstance
        ((Scheme.Modules.pullback (pullback.fst f (specMapAlgebraMap k k'))).obj F)
        (isCoherent_pullback (pullback.fst f (specMapAlgebraMap k k')) F) :=
  eulerCharacteristic_baseChange_field k k' _ _ f (IsPullback.of_hasPullback f _) F

end AlgebraicGeometry

end
