module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Descent
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism

/-!
# Descending quasi-compact separated étale schemes

Let `f : X ⟶ S` be a morphism of schemes. The underlying `X`-scheme of the canonical descent
datum of an `S`-scheme relative to `f` is its base change along `f`, so the structure morphism
of that datum inherits every property of the original structure morphism that is stable under
base change. Applied to quasi-compactness and separatedness, this shows that the canonical
étale descent functor of `f` restricts to a functor from the schemes that are quasi-compact,
separated and étale over `S` to the étale descent data relative to `f` whose underlying
`X`-scheme is quasi-compact and separated.

When `f` is surjective both the canonical étale descent functor and its restriction are
faithful: two morphisms of schemes étale over `S` that become equal after base change along `f`
are already equal.

## Main definitions

* `AlgebraicGeometry.IsQuasiCompactSeparatedEtaleOver` is the property of a scheme étale over
  `S` that its structure morphism is quasi-compact and separated, and
  `AlgebraicGeometry.QuasiCompactSeparatedEtaleOver` is the resulting full subcategory.
* `AlgebraicGeometry.IsQuasiCompactSeparatedEtaleDescentData` is the corresponding property of
  an étale descent datum relative to `f`, and
  `AlgebraicGeometry.QuasiCompactSeparatedEtaleDescentData` the resulting full subcategory.
* `AlgebraicGeometry.quasiCompactSeparatedEtaleDescentFunctor` is the restriction of the
  canonical étale descent functor to these full subcategories.

## Main results

* `AlgebraicGeometry.canonicalDescentData_property`: the structure morphism of the canonical
  descent datum of an `S`-scheme has every base-change stable property of the structure
  morphism of that scheme; `AlgebraicGeometry.canonicalDescentData_quasiCompact` and
  `AlgebraicGeometry.canonicalDescentData_isSeparated` are the two instances of this used here.
* `AlgebraicGeometry.faithful_etaleForget_comp_canonicalFunctor`: taking canonical descent data
  of schemes étale over `S` is faithful along a surjective morphism, and
  `AlgebraicGeometry.quasiCompactSeparatedEtaleDescentFunctor_faithful`: so is the restriction
  of the canonical étale descent functor.
* `AlgebraicGeometry.fullyFaithful_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`:
  along a surjective integral morphism the restriction is fully faithful.
* `AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor`: for a surjective
  morphism, fullness of the canonical étale descent functor together with essential
  surjectivity of the restriction makes the restriction an equivalence.

## Implementation notes

The canonical descent functor is the composite of the trivial-datum functor with the pullback
functor of a commutative square, so the comparison between the underlying scheme of a canonical
datum and the base change is the `objIso` field of
`AlgebraicGeometry.DescentData.PullbackFunctor`. Both the base-change stability argument and
the faithfulness argument are phrased through that field, hence they apply to the canonical
functor on the nose rather than up to an unspecified isomorphism.

Faithfulness uses only surjectivity of `f`, through
`Stacks.Etale.injective_baseChange_hom_of_surjective`; no flatness is needed, so it does not go
through `AlgebraicGeometry.pullbackFunctor_faithful`.

Fullness of the canonical étale descent functor along a surjective integral morphism is Tag
0BTL for a surjective universally closed morphism, since an integral morphism is universally
closed; it is recorded as an instance so that the conditional equivalence
`isEquivalence_quasiCompactSeparatedEtaleDescentFunctor` then asks only for essential
surjectivity.

## References

* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}}

/-- The underlying `X`-scheme of the canonical descent datum of an `S`-scheme `U` relative to
`f : X ⟶ S` is the base change of `U` along `f`. Hence its structure morphism has every
property of the structure morphism of `U` that is stable under base change. -/
theorem canonicalDescentData_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (f : X ⟶ S) (U : Over S) (hU : P U.hom) :
    P (((DescentData.canonicalFunctor f).obj U).obj ()).hom := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let Pb := DescentData.pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)
  let D := (DescentData.trivialFunctor S).obj U
  change P ((Pb.functor.obj D).obj ()).hom
  have : IsIso (Pb.objIso D).hom.left :=
    inferInstanceAs (IsIso ((Over.forget X).map (Pb.objIso D).hom))
  rw [← Over.w (Pb.objIso D).hom]
  exact (P.cancel_left_of_respectsIso _ _).mpr (P.pullback_snd U.hom f hU)

/-- The canonical descent datum of a quasi-compact scheme over `S` has a quasi-compact
underlying scheme over `X`. -/
theorem canonicalDescentData_quasiCompact (f : X ⟶ S) (U : Over S) [QuasiCompact U.hom] :
    QuasiCompact (((DescentData.canonicalFunctor f).obj U).obj ()).hom :=
  canonicalDescentData_property @QuasiCompact f U ‹_›

/-- The canonical descent datum of a separated scheme over `S` has a separated underlying
scheme over `X`. -/
theorem canonicalDescentData_isSeparated (f : X ⟶ S) (U : Over S) [IsSeparated U.hom] :
    IsSeparated (((DescentData.canonicalFunctor f).obj U).obj ()).hom :=
  canonicalDescentData_property @IsSeparated f U ‹_›

/-- The property of a scheme étale over `S` that its structure morphism is quasi-compact and
separated. -/
abbrev IsQuasiCompactSeparatedEtaleOver (S : Scheme.{u}) : ObjectProperty S.Etale :=
  fun U ↦ QuasiCompact U.hom ∧ IsSeparated U.hom

/-- The category of quasi-compact separated schemes étale over `S`. -/
abbrev QuasiCompactSeparatedEtaleOver (S : Scheme.{u}) :=
  (IsQuasiCompactSeparatedEtaleOver S).FullSubcategory

/-- The property of an étale descent datum relative to `f : X ⟶ S` that the structure morphism
of its underlying scheme over `X` is quasi-compact and separated. -/
abbrev IsQuasiCompactSeparatedEtaleDescentData (f : X ⟶ S) :
    ObjectProperty (EtaleDescentData f) :=
  fun D ↦ QuasiCompact (D.obj.obj ()).hom ∧ IsSeparated (D.obj.obj ()).hom

/-- The category of étale descent data relative to `f : X ⟶ S` whose underlying scheme over `X`
is quasi-compact and separated. -/
abbrev QuasiCompactSeparatedEtaleDescentData (f : X ⟶ S) :=
  (IsQuasiCompactSeparatedEtaleDescentData f).FullSubcategory

/-- The canonical étale descent datum of a quasi-compact separated scheme étale over `S` has a
quasi-compact separated underlying scheme over `X`. -/
theorem etaleDescentFunctor_quasiCompactSeparated (f : X ⟶ S) (U : S.Etale)
    (hU : IsQuasiCompactSeparatedEtaleOver S U) :
    IsQuasiCompactSeparatedEtaleDescentData f ((etaleDescentFunctor f).obj U) :=
  ⟨canonicalDescentData_property @QuasiCompact f _ hU.1,
    canonicalDescentData_property @IsSeparated f _ hU.2⟩

/-- Pullback along `f : X ⟶ S` as a functor from the quasi-compact separated schemes étale over
`S` to the étale descent data relative to `f` with quasi-compact separated underlying scheme
over `X`. This is the functor whose being an equivalence, for `f` surjective and integral, is
Stacks Project, Tag 0BTP. -/
def quasiCompactSeparatedEtaleDescentFunctor (f : X ⟶ S) :
    QuasiCompactSeparatedEtaleOver S ⥤ QuasiCompactSeparatedEtaleDescentData f :=
  (IsQuasiCompactSeparatedEtaleDescentData f).lift
    ((IsQuasiCompactSeparatedEtaleOver S).ι ⋙ etaleDescentFunctor f)
    (fun U ↦ etaleDescentFunctor_quasiCompactSeparated f U.obj U.property)

/-- Taking canonical descent data of schemes étale over `S` is faithful along a surjective
morphism: two morphisms of étale `S`-schemes with the same base change along `f` are equal. -/
instance faithful_etaleForget_comp_canonicalFunctor (f : X ⟶ S) [Surjective f] :
    (Scheme.Etale.forget S ⋙ DescentData.canonicalFunctor f).Faithful where
  map_injective {U V φ ψ} h := by
    have hV : Etale ((Scheme.Etale.forget S).obj V).hom := V.prop
    let Pb := DescentData.pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)
    let D := (DescentData.trivialFunctor S).obj ((Scheme.Etale.forget S).obj U)
    let E := (DescentData.trivialFunctor S).obj ((Scheme.Etale.forget S).obj V)
    have key : ∀ χ : U ⟶ V,
        (Pb.objIso D).hom ≫ (Over.pullback f).map ((Scheme.Etale.forget S).map χ) =
          ((Scheme.Etale.forget S ⋙ DescentData.canonicalFunctor f).map χ).hom () ≫
            (Pb.objIso E).hom :=
      fun χ ↦ Pb.map ((DescentData.trivialFunctor S).map ((Scheme.Etale.forget S).map χ))
    have hcancel : (Pb.objIso D).hom ≫ (Over.pullback f).map ((Scheme.Etale.forget S).map φ) =
        (Pb.objIso D).hom ≫ (Over.pullback f).map ((Scheme.Etale.forget S).map ψ) := by
      rw [key φ, key ψ, h]
    exact (Scheme.Etale.forgetFullyFaithful S).map_injective
      (Stacks.Etale.injective_baseChange_hom_of_surjective f
        ((Scheme.Etale.forget S).obj V) ((Scheme.Etale.forget S).obj U)
        ((cancel_epi (Pb.objIso D).hom).mp hcancel))

-- Faithfulness of the canonical étale descent functor of a surjective morphism,
-- `AlgebraicGeometry.etaleDescentFunctor_faithful`, as an instance, so that the faithfulness of
-- the restriction below is found by instance search.
attribute [instance] etaleDescentFunctor_faithful

/-- The restriction of the canonical étale descent functor of a surjective morphism to
quasi-compact separated objects is faithful. -/
instance quasiCompactSeparatedEtaleDescentFunctor_faithful (f : X ⟶ S) [Surjective f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).Faithful :=
  Functor.Faithful.of_comp_iso
    ((IsQuasiCompactSeparatedEtaleDescentData f).liftCompιIso
      ((IsQuasiCompactSeparatedEtaleOver S).ι ⋙ etaleDescentFunctor f)
      (fun U ↦ etaleDescentFunctor_quasiCompactSeparated f U.obj U.property))

/-- Effective descent of quasi-compact separated étale schemes along a surjective morphism `f`
follows from fullness of the canonical étale descent functor of `f` together with essential
surjectivity of its restriction to quasi-compact separated objects. -/
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor (f : X ⟶ S) [Surjective f]
    [(etaleDescentFunctor f).Full]
    [(quasiCompactSeparatedEtaleDescentFunctor f).EssSurj] :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence where
  full := .of_comp_faithful_iso
    ((IsQuasiCompactSeparatedEtaleDescentData f).liftCompιIso
      ((IsQuasiCompactSeparatedEtaleOver S).ι ⋙ etaleDescentFunctor f)
      (fun U ↦ etaleDescentFunctor_quasiCompactSeparated f U.obj U.property))

/-- The canonical étale descent functor of a surjective integral morphism is full: an integral
morphism is universally closed, so Stacks Project, Tag 0BTL applies. -/
instance etaleDescentFunctor_full_of_isIntegralHom (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    (etaleDescentFunctor f).Full :=
  (etaleDescentFunctor_fullyFaithful_of_universallyClosed f).elim fun h ↦ h.full

/-- The restriction of the canonical étale descent functor of a surjective morphism to
quasi-compact separated objects is full as soon as the functor itself is. -/
instance quasiCompactSeparatedEtaleDescentFunctor_full (f : X ⟶ S)
    [(etaleDescentFunctor f).Full] : (quasiCompactSeparatedEtaleDescentFunctor f).Full :=
  .of_comp_faithful_iso
    ((IsQuasiCompactSeparatedEtaleDescentData f).liftCompιIso
      ((IsQuasiCompactSeparatedEtaleOver S).ι ⋙ etaleDescentFunctor f)
      (fun U ↦ etaleDescentFunctor_quasiCompactSeparated f U.obj U.property))

/-- **Stacks Project, Tag 0BTP, the fully faithful half.** Let `f : X ⟶ S` be a surjective
integral morphism. The functor of Tag 0BTI, restricted to the schemes quasi-compact, separated
and étale over `S` and to the descent data relative to `X/S` whose underlying `X`-scheme is
quasi-compact, separated and étale, is fully faithful.

Fullness is Tag 0BTL for a surjective universally closed morphism, which a surjective integral
morphism is, and faithfulness is Tag 0BTJ. -/
@[stacks 0BTP "the fully faithful half of the equivalence"]
theorem fullyFaithful_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom
    (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    Nonempty (quasiCompactSeparatedEtaleDescentFunctor f).FullyFaithful :=
  ⟨.ofFullyFaithful _⟩

end AlgebraicGeometry

end
