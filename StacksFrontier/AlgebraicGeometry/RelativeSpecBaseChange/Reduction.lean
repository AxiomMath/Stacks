module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# Tag 01SA reduced to two statements about base change of algebras

Let `S` be a scheme.  The anti-equivalence between the schemes affine over `S` and the
quasi-coherent sheaves of commutative `𝒪_S`-algebras is packaged by the structure
`Stacks.AffineAlgebraEquivalence.AffineAlgebraAntiEquivalence`, whose nine fields are the
anti-equivalence itself, its identification with pushforward of structure sheaves, pullback of
algebra sheaves with its universal property, and compatibility with arbitrary base change.

Six of those fields are already available: the algebra-pullback functor with its pushout
property, the anti-equivalence over each base, and the identification with pushforward together
with its naturality.  This file assembles the remaining three from the canonical base-change
morphism `baseChangeAlgebraHom`, so that the whole of Stacks Tag 01SA follows from exactly two
statements, taken here as hypotheses:

* `IsQuasicoherentAlgebraPullback`: the pullback `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of a quasi-coherent
  algebra is quasi-coherent;
* `IsIsoBaseChangeAlgebraHom`: for `X` affine over `S` the canonical morphism
  `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` is invertible.

Neither hypothesis is proved here; what is proved is that nothing else is missing.

## Main definitions

* `baseChangeOverMap` is the morphism `X ×_S T ⟶ Y ×_S T` induced by a morphism `X ⟶ Y` over
  `S`, regarded as a morphism over `S` through `g`.
* `IsQuasicoherentAlgebraPullback` and `IsIsoBaseChangeAlgebraHom` are the two statements above.
* `baseChangeIsoOfHyps` is the natural isomorphism expressing compatibility of the
  anti-equivalence with base change, given the two hypotheses.
* `affineAlgebraAntiEquivalenceOfHyps` is the full content of Stacks Tag 01SA, given them.

## Main results

* `algebraPushforward_map_pushforwardAlgebraMap`: the direct image of algebra sheaves carries
  the canonical map on pushed-forward structure sheaves of a morphism over `T` to the canonical
  map of the same morphism read over `S`.
* `baseChangeAlgebraHom_naturality`: the canonical base-change morphism is natural in the
  scheme over `S`.  This is what makes the base-change isomorphism a natural isomorphism, and
  it is proved formally, with no hypothesis on the morphisms involved.
* `baseChangeIsoOfHyps_hom_app`: the components of the base-change isomorphism, read in the
  category of all algebra sheaves, are the canonical base-change morphisms.

## Implementation notes

`baseChangeAlgebraHom` is defined as an adjunct, so its naturality is proved by applying
`CategoryTheory.Adjunction.homEquiv_naturality_left_symm` and
`CategoryTheory.Adjunction.homEquiv_naturality_right_symm` and comparing the two adjoint
morphisms, rather than by computing sections.  The comparison,
`pushforwardAlgebraMap_comp_baseChangeProjection`, is the contravariant functoriality
`pushforwardAlgebraMap_comp` applied to the equality of morphisms over `S`
`baseChangeProjection g X ≫ u = baseChangeOverMap g u ≫ baseChangeProjection g Y`, which is the
naturality square of the fibre product.

Three identifications are definitional and are used as such: the right component of
`algebraPushforward g` on a morphism is the direct image of its right component; direct image
of sheaves along a composite of continuous maps is the composite of the direct images, because
`TopologicalSpace.Opens.map` is strictly functorial; and composition of morphisms of schemes is
strictly associative.  Together they make
`algebraPushforward_map_pushforwardAlgebraMapAux` hold by `rfl`, and the version for
`pushforwardAlgebraMap` then differs only by `eqToHom`s between equal objects.

The proofs are in term mode, or end in `rfl`, wherever the statement straddles the two
spellings `(algebraPushforward g).obj (pushforwardAlgebra ((Over.pullback g).obj X).hom)` and
`pushforwardAlgebra (Over.mk (pullback.snd X.hom g ≫ g)).hom`: those are definitionally equal
but not type-correct at instance transparency, so a `rw` whose motive mentions either fails
with an application type mismatch while `exact` succeeds.

The components of `baseChangeIsoOfHyps` are built with `CategoryTheory.ObjectProperty.isoMk`
and not with `CategoryTheory.Functor.preimageIso` of the inclusion, although the inclusion is
fully faithful and either would typecheck.  The reason is that `isoMk` stores the given
morphism, so `baseChangeIsoOfHyps_hom_app` holds by `rfl`, whereas `Functor.map_preimage` is a
theorem proved from faithfulness and is not definitional.  With `rfl` available, a consumer
holding its own copy of these definitions — a different but definitionally equal spelling of
the full subcategory of quasi-coherent algebras — can reach the `baseChangeIso_canonical`
equation by `change`; with `preimageIso` it cannot, because `rw` on that goal fails: the
motive mentions `affineQuasicoherentEquivalence`, whose type is in the other spelling, so the
target is not type-correct at instance transparency.

The two hypotheses are stated as `Prop`-valued abbreviations over all pairs of schemes rather
than as hypotheses of a single base-change square, because `baseChangeIsoOfHyps` needs
`IsQuasicoherentAlgebraPullback` to state the functor whose target it is, and
`AffineAlgebraAntiEquivalence` quantifies over all bases in each of its fields.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-! ### Naturality of the canonical base-change morphism -/

/-- The direct image of algebra sheaves along `g` carries the canonical map
`p_* 𝒪_Y ⟶ (u ≫ p)_* 𝒪_X` of a morphism over `T` to the canonical map of the same data read
over `S`. -/
public theorem algebraPushforward_map_pushforwardAlgebraMapAux {X Y : Scheme.{u}} (p : Y ⟶ T)
    (u : X ⟶ Y) :
    (algebraPushforward g).map (pushforwardAlgebraMapAux p u) =
      pushforwardAlgebraMapAux (p ≫ g) u :=
  rfl

/-- A morphism `u : X ⟶ Y` over `S` induces `X ×_S T ⟶ Y ×_S T`, which is a morphism over `S`
between the fibre products regarded as schemes over `S` through `T`. -/
public noncomputable def baseChangeOverMap {X Y : Over S} (u : X ⟶ Y) :
    (Over.mk (pullback.snd X.hom g ≫ g) : Over S) ⟶ Over.mk (pullback.snd Y.hom g ≫ g) :=
  Over.homMk ((Over.pullback g).map u).left (by
    change pullback.lift _ _ _ ≫ pullback.snd Y.hom g ≫ g = pullback.snd X.hom g ≫ g
    rw [← Category.assoc, pullback.lift_snd])

/-- The naturality square of the fibre product, as an equality of morphisms over `S`: the
projection followed by `u` is the induced morphism followed by the projection. -/
public theorem baseChangeProjection_comp {X Y : Over S} (u : X ⟶ Y) :
    baseChangeProjection g X ≫ u = baseChangeOverMap g u ≫ baseChangeProjection g Y := by
  ext
  show pullback.fst X.hom g ≫ u.left =
    pullback.lift (pullback.fst X.hom g ≫ u.left) (pullback.snd X.hom g) _ ≫
      pullback.fst Y.hom g
  rw [pullback.lift_fst]

/-- The direct image of algebra sheaves along `g` carries the canonical map on pushed-forward
structure sheaves of `(Over.pullback g).map u` to the canonical map of `baseChangeOverMap g u`,
the same morphism read over `S`. -/
public theorem algebraPushforward_map_pushforwardAlgebraMap {X Y : Over S} (u : X ⟶ Y) :
    (algebraPushforward g).map (pushforwardAlgebraMap ((Over.pullback g).map u)) =
      pushforwardAlgebraMap (baseChangeOverMap g u) := by
  rw [pushforwardAlgebraMap, pushforwardAlgebraMap, CategoryTheory.Functor.map_comp,
    algebraPushforward_map_pushforwardAlgebraMapAux, eqToHom_map]
  rfl

/-- The two morphisms of `𝒪_S`-algebras to which the two sides of
`baseChangeAlgebraHom_naturality` are adjoint agree: both are the canonical map on
pushed-forward structure sheaves of the composite `X ×_S T ⟶ X ⟶ Y`. -/
public theorem pushforwardAlgebraMap_comp_baseChangeProjection {X Y : Over S} (u : X ⟶ Y) :
    pushforwardAlgebraMap u ≫ pushforwardAlgebraMap (baseChangeProjection g X) =
      pushforwardAlgebraMap (baseChangeProjection g Y) ≫
        (algebraPushforward g).map (pushforwardAlgebraMap ((Over.pullback g).map u)) :=
  Eq.trans (pushforwardAlgebraMap_comp (baseChangeProjection g X) u).symm
    (Eq.trans (congrArg pushforwardAlgebraMap (baseChangeProjection_comp g u))
      (Eq.trans (pushforwardAlgebraMap_comp (baseChangeOverMap g u) (baseChangeProjection g Y))
        (congrArg (fun k ↦ pushforwardAlgebraMap (baseChangeProjection g Y) ≫ k)
          (algebraPushforward_map_pushforwardAlgebraMap g u).symm)))

/-- **The canonical base-change morphism is natural.** No hypothesis on `g` or on the schemes
over `S` is needed: the statement is the mate of the naturality square of the fibre product
under the adjunction between pullback and pushforward of algebra sheaves. -/
public theorem baseChangeAlgebraHom_naturality {X Y : Over S} (u : X ⟶ Y) :
    (algebraPullback g).map (pushforwardAlgebraMap u) ≫ baseChangeAlgebraHom g X =
      baseChangeAlgebraHom g Y ≫ pushforwardAlgebraMap ((Over.pullback g).map u) :=
  Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _).symm
    (Eq.trans
      (congrArg ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm
        (pushforwardAlgebraMap_comp_baseChangeProjection g u))
      (Adjunction.homEquiv_naturality_right_symm _ _ _))

/-! ### The two remaining statements, and the reduction -/

/-- The pullback of a quasi-coherent algebra along an arbitrary morphism of schemes is
quasi-coherent.  This is the `algebraPullback_isQuasicoherent` clause of Stacks Tag 01SA. -/
public abbrev IsQuasicoherentAlgebraPullback : Prop :=
  ∀ {T S : Scheme.{u}} (g : T ⟶ S) (A : QuasicoherentAlgebra S),
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A.obj)

/-- For `X` affine over `S` the canonical base-change morphism of algebra sheaves is
invertible.  This is the base-change assertion of Stacks Tag 01SA. -/
public abbrev IsIsoBaseChangeAlgebraHom : Prop :=
  ∀ {T S : Scheme.{u}} (g : T ⟶ S) (X : Over S), IsAffineHom X.hom →
    IsIso (baseChangeAlgebraHom g X)

variable (hqc : IsQuasicoherentAlgebraPullback.{u}) (hbc : IsIsoBaseChangeAlgebraHom.{u})

/-- Given the two hypotheses, the anti-equivalence commutes with base change: the natural
isomorphism has `baseChangeAlgebraHom` for its components. -/
public noncomputable def baseChangeIsoOfHyps {T S : Scheme.{u}} (g : T ⟶ S) :
    (affineQuasicoherentEquivalence S).functor ⋙
        ObjectProperty.lift _ ((IsQuasicoherentAlgebra S).ι ⋙ algebraPullback g) (hqc g) ≅
      (affineBaseChange g).op ⋙ (affineQuasicoherentEquivalence T).functor :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ (baseChangeAlgebraHom g X.unop.obj)
        (hbc g X.unop.obj X.unop.property)))
    (by
      intro X Y f
      apply (IsQuasicoherentAlgebra T).ι.map_injective
      simp only [CategoryTheory.Functor.map_comp]
      exact baseChangeAlgebraHom_naturality g ((IsAffineHomOver S).ι.map f.unop))

/-- The components of `baseChangeIsoOfHyps`, read in the category of all algebra sheaves, are
the canonical base-change morphisms. -/
public theorem baseChangeIsoOfHyps_hom_app {T S : Scheme.{u}} (g : T ⟶ S) (X : AffineOver S) :
    (IsQuasicoherentAlgebra T).ι.map ((baseChangeIsoOfHyps hqc hbc g).hom.app (op X)) =
      baseChangeAlgebraHom g X.obj :=
  rfl

/-- The `baseChangeIso_canonical` clause of Stacks Tag 01SA, in the form in which the structure
asks for it: the identifications with pushforward of structure sheaves are identities, so the
clause is `algebraPullbackMap_comp_baseChangeAlgebraHom` with two of them inserted. -/
public theorem algebraPullbackMap_comp_baseChangeAlgebraHom_comp_id {T S : Scheme.{u}}
    (g : T ⟶ S) (X : Over S) :
    (algebraPullbackMap g).app (pushforwardAlgebra X.hom) ≫
        (baseChangeAlgebraHom g X ≫
          𝟙 (pushforwardAlgebra ((Over.pullback g).obj X).hom)).right =
      (TopCat.Sheaf.pullback CommRingCat g.base).map
          (𝟙 (pushforwardAlgebra X.hom).right) ≫
        pushforwardBaseChangeMap g X := by
  rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact algebraPullbackMap_comp_baseChangeAlgebraHom g X

/-- **Stacks Project, Tag 01SA, reduced to two statements.** Given that the pullback of a
quasi-coherent algebra is quasi-coherent and that the canonical base-change morphism is
invertible at the schemes affine over the base, the anti-equivalence between affine schemes
over `S` and quasi-coherent `𝒪_S`-algebras, compatible with arbitrary base change, exists. -/
public noncomputable def affineAlgebraAntiEquivalenceOfHyps :
    AffineAlgebraAntiEquivalence.{u} where
  algebraPullback g := algebraPullback g
  algebraPullbackMap g := algebraPullbackMap g
  algebraPullback_isPushout g A := algebraPullback_isPushout g A
  algebraPullback_isQuasicoherent g A := hqc g A
  equivalence S := affineQuasicoherentEquivalence S
  pushforwardIso S X := pushforwardIsoOfEquivalence S X
  pushforwardIso_naturality S := pushforwardIsoOfEquivalence_naturality S
  baseChangeIso g := baseChangeIsoOfHyps hqc hbc g
  baseChangeIso_canonical g X := by
    rw [baseChangeIsoOfHyps_hom_app]
    exact algebraPullbackMap_comp_baseChangeAlgebraHom_comp_id g X.obj

end Stacks.AffineAlgebraEquivalence

end
