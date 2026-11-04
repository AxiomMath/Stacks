module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The zero section of a pointed family as a relative effective Cartier divisor

Let `(E, f, 0)` be a pointed family over `S` whose structure morphism `f` is separated. The
section `0 : S ⟶ E` is then a closed immersion, and its kernel is a closed subscheme of `E`, the
*zero divisor* `D = 0(S)`. When `f` is smooth of relative dimension one, `D` is a relative
effective Cartier divisor on `E/S`, because `D ⟶ S` is an isomorphism, so finite locally free
(Stacks 0B9D). The zero divisor is compatible with base change: the zero divisor of the
pulled-back family `E ×_{S,g} T` is the inverse image of the zero divisor of `E`.

## Main definitions

* `PointedFamily.zeroDivisor`: the closed subscheme `0(S) ⊆ E`.

## Main results

* `PointedFamily.isClosedImmersion_zero`: a section of a separated morphism is a closed
  immersion.
* `PointedFamily.isIso_zeroDivisor_subschemeι_comp_map`: the zero divisor maps isomorphically
  onto the base.
* `PointedFamily.isRelativeEffectiveCartierDivisor_zeroDivisor`: for a family smooth of relative
  dimension one, the zero divisor is a relative effective Cartier divisor.
* `PointedFamily.zeroDivisor_pullback`: the zero divisor of a pulled-back family is the inverse
  image of the zero divisor.

## References

* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Divisors

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

variable {S T : Scheme.{u}} (E : PointedFamily S)

/-- A section of a separated morphism is a closed immersion. -/
@[sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
instance isClosedImmersion_zero [IsSeparated E.map] : IsClosedImmersion E.zero := by
  have : IsClosedImmersion (E.zero ≫ E.map) := by rw [E.zero_map]; infer_instance
  exact IsClosedImmersion.of_comp E.zero E.map

/-- The zero divisor `0(S) ⊆ E` of a pointed family: the kernel of its section. -/
def zeroDivisor : E.total.IdealSheafData :=
  E.zero.ker

/-- The zero divisor is the kernel of the section `0 : S ⟶ E` of the family. -/
theorem zeroDivisor_eq_ker : E.zeroDivisor = E.zero.ker :=
  rfl

/-- The zero divisor maps isomorphically onto the base. -/
instance isIso_zeroDivisor_subschemeι_comp_map [IsSeparated E.map] :
    IsIso (E.zeroDivisor.subschemeι ≫ E.map) := by
  rw [zeroDivisor_eq_ker]
  have : IsIso E.zero.toImage := inferInstance
  have h : E.zero.imageι ≫ E.map = inv E.zero.toImage := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [Scheme.Hom.toImage_imageι_assoc, E.zero_map]
  change IsIso (E.zero.imageι ≫ E.map)
  rw [h]
  infer_instance

/-- **The zero divisor of a family smooth of relative dimension one is a relative effective
Cartier divisor.** -/
theorem isRelativeEffectiveCartierDivisor_zeroDivisor [IsSeparated E.map]
    [SmoothOfRelativeDimension 1 E.map] :
    IsRelativeEffectiveCartierDivisor E.map E.zeroDivisor := by
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (E.zeroDivisor.subschemeι ≫ E.map) 1 :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso _
  have : Stacks.Morphisms.IsFiniteLocallyFree (E.zeroDivisor.subschemeι ≫ E.map) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  exact isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree E.map E.zeroDivisor

/-- The zero divisor of a family smooth of relative dimension one is an effective Cartier
divisor. -/
instance isEffectiveCartierDivisor_zeroDivisor [IsSeparated E.map]
    [SmoothOfRelativeDimension 1 E.map] : IsEffectiveCartierDivisor E.zeroDivisor :=
  E.isRelativeEffectiveCartierDivisor_zeroDivisor.1

/-- The section of a pulled-back family is the base change of the section. -/
theorem isPullback_zero_pullback (g : T ⟶ S) :
    IsPullback (E.pullback g).zero g (Limits.pullback.fst E.map g) E.zero := by
  refine IsPullback.of_right (h₁₂ := Limits.pullback.snd E.map g) (h₂₂ := E.map) ?_
    (Limits.pullback.lift_fst _ _ _) (IsPullback.of_hasPullback E.map g).flip
  rw [(E.pullback g).zero_map, E.zero_map]
  exact IsPullback.id_horiz g

/-- **The zero divisor commutes with base change**: the zero divisor of `E ×_{S,g} T` is the
inverse image of the zero divisor of `E`. -/
theorem zeroDivisor_pullback [IsSeparated E.map] (g : T ⟶ S) :
    (E.pullback g).zeroDivisor = E.zeroDivisor.comap (Limits.pullback.fst E.map g) := by
  have h := E.isPullback_zero_pullback g
  rw [zeroDivisor_eq_ker, zeroDivisor_eq_ker]
  calc (E.pullback g).zero.ker
      = (h.isoPullback.hom ≫ Limits.pullback.fst (Limits.pullback.fst E.map g) E.zero).ker := by
        rw [h.isoPullback_hom_fst]
    _ = (Limits.pullback.fst (Limits.pullback.fst E.map g) E.zero).ker :=
        Scheme.Hom.ker_comp_of_isIso _ _
    _ = _ := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

/-! ### Base change of the zero divisor and of its invertible sheaf -/

/-- The pullback of a separated pointed family is separated. -/
instance isSeparated_pullback_map [IsSeparated E.map] (g : T ⟶ S) :
    IsSeparated (E.pullback g).map :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback E.map g) ‹_›

/-- The pullback of a pointed family smooth of relative dimension one is smooth of relative
dimension one. -/
instance smoothOfRelativeDimension_pullback_map [SmoothOfRelativeDimension 1 E.map]
    (g : T ⟶ S) : SmoothOfRelativeDimension 1 (E.pullback g).map :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback E.map g) ‹_›

/-- The pullback of the zero divisor along the projection of a pulled-back family is defined: it is
the zero divisor of the pulled-back family, an effective Cartier divisor. -/
instance isPullbackDefined_zeroDivisor [IsSeparated E.map] [SmoothOfRelativeDimension 1 E.map]
    (g : T ⟶ S) : IsPullbackDefined (Limits.pullback.fst E.map g) E.zeroDivisor := by
  change IsEffectiveCartierDivisor (E.zeroDivisor.comap (Limits.pullback.fst E.map g))
  rw [← E.zeroDivisor_pullback g]
  exact isEffectiveCartierDivisor_zeroDivisor (E.pullback g)

/-- Equal effective Cartier divisors have isomorphic invertible sheaves, compatibly with the
canonical sections. -/
theorem exists_invertibleSheaf'_iso_of_eq {X : Scheme.{u}} {D D' : X.IdealSheafData}
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] (h : D = D') :
    ∃ e : invertibleSheaf' D ≅ invertibleSheaf' D',
      Scheme.Modules.Hom.app e.hom ⊤ ((canonicalSection' D).val (op ⊤)) =
        (canonicalSection' D').val (op ⊤) := by
  subst h
  exact ⟨Iso.refl _, rfl⟩

/-- **The invertible sheaf of the zero divisor commutes with base change**: its pullback to
`E ×_{S,g} T` is the invertible sheaf of the zero divisor of the pulled-back family, and the
pullback of its canonical section is the canonical section. -/
theorem exists_pullback_zeroDivisor_invertibleSheaf_iso [IsSeparated E.map]
    [SmoothOfRelativeDimension 1 E.map] (g : T ⟶ S) :
    ∃ e : (Scheme.Modules.pullback (Limits.pullback.fst E.map g)).obj
        (invertibleSheaf' E.zeroDivisor) ≅ invertibleSheaf' (E.pullback g).zeroDivisor,
      Scheme.Modules.Hom.app e.hom ⊤ (pullbackCanonicalSection _ E.zeroDivisor) =
        (canonicalSection' (E.pullback g).zeroDivisor).val (op ⊤) := by
  have := isEffectiveCartierDivisor_zeroDivisor (E.pullback g)
  obtain ⟨e', he'⟩ := exists_invertibleSheaf'_iso_of_eq (E.zeroDivisor_pullback g).symm
  refine ⟨invertibleSheafPullbackIso _ E.zeroDivisor ≪≫ e', ?_⟩
  show Scheme.Modules.Hom.app e'.hom ⊤ (Scheme.Modules.Hom.app
    (invertibleSheafPullbackIso (Limits.pullback.fst E.map g) E.zeroDivisor).hom ⊤
      (pullbackCanonicalSection _ E.zeroDivisor)) = _
  rw [invertibleSheafPullbackIso_canonicalSection]
  exact he'


/-! ### The zero divisor over a field is the reduced point -/

/-- Over a field, the zero divisor of a separated pointed family is the reduced closed point
`0(Spec k)`: the vanishing ideal of the image of the section. -/
theorem zeroDivisor_eq_vanishingIdeal {k : Type u} [Field k] (F : PointedFamily (Spec (.of k)))
    [IsSeparated F.map] (x₀ : Spec (.of k)) :
    F.zeroDivisor = Scheme.IdealSheafData.vanishingIdeal
      ⟨{F.zero x₀}, by
        rw [← Set.image_singleton]
        exact F.zero.isClosedEmbedding.isClosedMap _ isClosed_singleton⟩ := by
  rw [zeroDivisor_eq_ker, Stacks.Chow.ker_eq_vanishingIdeal_support_of_isReduced F.zero]
  congr 1
  ext x
  rw [Scheme.Hom.support_ker, F.zero.isClosedEmbedding.isClosed_range.closure_eq]
  show x ∈ Set.range F.zero ↔ x = F.zero x₀
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y x₀]
  · rintro rfl
    exact ⟨x₀, rfl⟩

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
