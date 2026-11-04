module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Local properties of morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of continuous
homomorphisms between topological rings of a class `C`. Stacks 0ANG compares three ways of
asking that a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` have `P`:

1. every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y` has `P` on the induced map `U ⟶ V`;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with `P` on each `Uᵢ ⟶ Vⱼ`;
3. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` through an affine formal algebraic space representable and étale over `Y`
   with `P` on `Uᵢ ⟶ Vᵢ`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRepresentableEtale`: a morphism of fppf sheaves which is
  representable by algebraic spaces and étale.
* `AlgebraicGeometry.FormalSpace.IsAffineEtaleCover`: a covering as in Definition 0AIM.
* `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap`: the morphism of topological
  rings corresponding to a map of affine formal algebraic spaces has the property `P`.
* `AlgebraicGeometry.FormalSpace.HasPropertyOnEveryAffineEtaleDiagram`,
  `AlgebraicGeometry.FormalSpace.HasPropertyAfterTargetCover` and
  `AlgebraicGeometry.FormalSpace.HasPropertyAfterSourceCover`: the three conditions of
  **Stacks 0ANG**.
* `AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale` and
  `AlgebraicGeometry.FormalSpace.ChartPropertyDescendsAlongFiniteAffineEtaleCover`: the
  locality axioms of Situation 0CBA read on affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover`: the refinement of a
  covering as in condition (3) by charts over a diagram as in condition (1).

## Main results

* `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.comp` and
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_pullback_snd`: representable étale
  morphisms of fppf sheaves are closed under composition and stable under base change.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`:
  **Stacks 0ANG**, the implication from condition (1) to condition (2).
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover`:
  **Stacks 0ANG**, the implication from condition (3) to condition (1).

## Implementation notes

"The morphism `U ⟶ V` corresponds to a morphism of rings with property `P`" is rendered, as in
Tag 0GCP, by quantifying over presentations: over topological rings `A`, `R` of the class `C`,
over quotient systems presenting them over `S`, over identifications `U ≅ Spf E`, `V ≅ Spf D`,
and over continuous homomorphisms whose formal spectrum map is the given chart morphism. The
class of rings is a parameter, so that the countably indexed weakly admissible variant of the
source and the Noetherian adic variant of Remark 0ANI share one definition.

Condition (2) refers to the fibre product `Vⱼ ×_Y X`, which is formed in the category of fppf
sheaves; that it is a formal algebraic space is the assertion of Stacks 0AJ3, which this
library does not yet carry, so the implication below takes it as a hypothesis for the fibre
products it needs. Everything else in that implication is proved here: the charts of `Vⱼ ×_Y X`
map to `X` by a representable étale morphism, because the second projection is a base change of
`Vⱼ ⟶ Y`, and the square they form with `f` and `Vⱼ ⟶ Y` commutes by the universal property of
the fibre product.

The implication from condition (3) to condition (1) splits into a geometric half and a
ring-theoretic half. The geometric half refines a covering as in condition (3) against a
diagram as in condition (1): it uses that the fibre products `Yᵢ ×_Y V` are formal algebraic
spaces (Stacks 0AJ2) and that an affine formal algebraic space is quasi-compact, neither of
which this library carries, so it is the hypothesis `HasEtaleRefinementOfSourceCover`, which
mentions neither `C` nor `P`. The ring-theoretic half applies the locality axioms of Situation
0CBA to the resulting charts; translating those axioms from continuous ring maps to morphisms
of affine formal algebraic spaces is the equivalence of Stacks 0AN8 together with Stacks 0AN9,
which this library carries only for a morphism already presented by an étale ring map, so the
translated axioms are the hypotheses `ChartPropertyAscendsAlongAffineEtale` and
`ChartPropertyDescendsAlongFiniteAffineEtaleCover`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves on the big fppf site of `S` is *representable étale* when it is
representable by algebraic spaces and the morphism of algebraic spaces obtained from every
represented base change is étale. These are the maps appearing in the coverings of Definition
0AIM. -/
abbrev IsRepresentableEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hf

/-- **Definition 0AIM.** A family of maps into an fppf sheaf is an *affine étale covering* when
its sources are affine formal algebraic spaces, each map is representable étale, and the induced
map from the coproduct is a surjection of sheaves. -/
abbrev IsAffineEtaleCover {X : FppfSheaf B S hS} {I : Type (u + 1)} (U : I → FppfSheaf B S hS)
    (u : ∀ i, U i ⟶ X) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  (∀ i, IsAffineFormalAlgebraicSpace B S hS (U i)) ∧
    (∀ i, IsRepresentableEtale B S hS (u i)) ∧ Sheaf.IsLocallySurjective (Sigma.desc u)

/-- Representable étale morphisms of fppf sheaves are closed under composition. -/
theorem IsRepresentableEtale.comp {X Y Z : FppfSheaf B S hS} {a : X ⟶ Y} {b : Y ⟶ Z}
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    IsRepresentableEtale B S hS (a ≫ b) :=
  ⟨Space.isRepresentableByAlgebraicSpacesULift_comp B S hS a.hom b.hom ha.1 hb.1,
    isEtaleULift_pullback_fst_comp B S hS hb.1 hb.2 ha.2⟩

/-- Representable étale morphisms of fppf sheaves are stable under base change: the second
projection of the fibre product of a representable étale morphism with an arbitrary morphism
is representable étale. -/
theorem isRepresentableEtale_pullback_snd {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hv : IsRepresentableEtale B S hS v) :
    IsRepresentableEtale B S hS (pullback.snd v f) := by
  have hsq : IsPullback (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom :=
    (IsPullback.of_hasPullback v f).map (sheafToPresheaf (BigFppfOver.topology B S hS) _)
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
      (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom hsq hv.1,
    isEtaleULift_pullback_fst_of_isPullback B S hS hsq hv.2⟩

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The morphism of topological rings corresponding to a map `t : U ⟶ V` of affine formal
algebraic spaces has the property `P`: for every pair of rings of the class `C` presenting `V`
and `U` as formal spectra and every continuous homomorphism between them whose formal spectrum
map is `t`, that homomorphism has `P`. -/
abbrev HasPropertyOnAffineChartMap {U V : FppfSheaf B S hS} (t : U ⟶ V) : Prop :=
  ∀ (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R],
    C A → C R → ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
      (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
      (g : ContinuousHom D E),
      t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv → P g.toRingHom

/-- **Stacks 0ANG, condition (1).** Every commutative square whose vertical maps are
representable étale maps from affine formal algebraic spaces has `P` on its upper horizontal
map. -/
abbrev HasPropertyOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
    a ≫ f = t ≫ b → HasPropertyOnAffineChartMap B S hS C P t

/-- **Stacks 0ANG, condition (2).** There is an affine étale covering of the target and, for
each of its members, an affine étale covering of the fibre product of that member with the
source on which `P` holds. -/
abbrev HasPropertyAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
        (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, HasPropertyOnAffineChartMap B S hS C P (w i ≫ pullback.fst (v j) f)

/-- **Stacks 0ANG, condition (3).** There is an affine étale covering of the source, each
member of which factors through an affine formal algebraic space representable étale over the
target by a map with `P`. -/
abbrev HasPropertyAfterSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS v ∧
          u i ≫ f = t ≫ v ∧ HasPropertyOnAffineChartMap B S hS C P t

/-- **Stacks 0ANG, condition (1) implies condition (2).** If `P` holds on every affine étale
diagram over `f`, then the atlas of the target and the atlases of the fibre products of its
members with the source witness condition (2).

The hypothesis `hpb` is the assertion of Stacks 0AJ3 that the fibre product of the chart
`V ⟶ Y` with `f` is a formal algebraic space; the library does not yet carry Stacks 0AJ3, so it
is carried here as a hypothesis for the fibre products the statement needs. -/
@[stacks 0ANG "condition (1) implies condition (2), with Stacks 0AJ3 as a hypothesis"]
theorem hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hpb : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) :
    HasPropertyAfterTargetCover B S hS C P f := by
  obtain ⟨-, J, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  refine ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, I, U, w, hUaffine, hUetale, hUsurj⟩ := hpb (V j) (v j) (hVaffine j) (hVetale j)
  refine ⟨I, U, w, ⟨hUaffine, hUetale, hUsurj⟩, fun i ↦ ?_⟩
  refine hf (U i) (V j) (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f)
    (hUaffine i) (hVaffine j)
    (IsRepresentableEtale.comp B S hS (hUetale i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hVetale j)))
    (hVetale j) ?_
  rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- Axiom (1) of a local property of Situation 0CBA, read on affine formal algebraic spaces
through the equivalence of **Stacks 0AN8**: a representable étale change of source and of target
carries `P` from a map of affine formal algebraic spaces to the induced map. -/
abbrev ChartPropertyAscendsAlongAffineEtale : Prop :=
  ∀ {U V U' V' : FppfSheaf B S hS} (t : U ⟶ V) (t' : U' ⟶ V') (q : U' ⟶ U) (r : V' ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS U' → IsAffineFormalAlgebraicSpace B S hS V' →
    IsRepresentableEtale B S hS q → IsRepresentableEtale B S hS r → q ≫ t = t' ≫ r →
    HasPropertyOnAffineChartMap B S hS C P t → HasPropertyOnAffineChartMap B S hS C P t'

/-- Axioms (2) and (3) of a local property of Situation 0CBA, read on affine formal algebraic
spaces through the equivalences of **Stacks 0AN8** and **Stacks 0AN9**, in the single
combination the proof of Stacks 0ANG uses: `P` descends to `t : U ⟶ V` from a finite affine
étale covering `{Wₛ ⟶ U}` whose members map to representable étale charts `Zₛ ⟶ V` of the
target by maps with `P`, compatibly with `t`. -/
abbrev ChartPropertyDescendsAlongFiniteAffineEtaleCover : Prop :=
  ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
    IsAffineFormalAlgebraicSpace B S hS V →
    ∀ (σ : Type (u + 1)), Finite σ → ∀ (W Z : σ → FppfSheaf B S hS) (p : ∀ s, W s ⟶ U)
      (m : ∀ s, W s ⟶ Z s) (r : ∀ s, Z s ⟶ V),
      IsAffineEtaleCover B S hS W p →
      (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) →
      (∀ s, IsRepresentableEtale B S hS (r s)) → (∀ s, p s ≫ t = m s ≫ r s) →
      (∀ s, HasPropertyOnAffineChartMap B S hS C P (m s)) →
      HasPropertyOnAffineChartMap B S hS C P t

/-- The refinement of a covering constructed in the proof of **Stacks 0ANG**: for every
covering `{Uᵢ ⟶ X}` of the source with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through representable
étale charts of the target, and every commutative square `U₀ ⟶ V₀` over `f` with `U₀`, `V₀`
affine and representable étale over `X`, `Y`, there is a finite affine étale covering
`{Wₛ ⟶ U₀}` whose members map to a member `U (k s)` of the given covering and to a
representable étale chart `Zₛ` of `V₀` over `V (k s)`, both squares commuting.

In Stacks 0ANG the covering is `{Xᵢⱼₖ}` with `Xᵢⱼₖ ⟶ Yᵢⱼ`, obtained from coverings of the
fibre products `Yᵢ ×_Y V₀` and `Yᵢⱼ ×_{Yᵢ} Xᵢ ×_X U₀`, which are formal algebraic spaces by
Stacks 0AJ2, and finite because `U₀` is quasi-compact. -/
abbrev HasEtaleRefinementOfSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
      (t : ∀ i, U i ⟶ V i), IsAffineEtaleCover B S hS U u →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) →
      (∀ i, IsRepresentableEtale B S hS (v i)) → (∀ i, u i ≫ f = t i ≫ v i) →
    ∀ (U₀ V₀ : FppfSheaf B S hS) (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀),
      IsAffineFormalAlgebraicSpace B S hS U₀ → IsAffineFormalAlgebraicSpace B S hS V₀ →
      IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b → a ≫ f = τ ≫ b →
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ ∀ s, p s ≫ τ = m s ≫ c s

/-- **Stacks 0ANG, condition (3) implies condition (1).** If `P` holds on an affine étale
covering of the source of `f`, whose members factor through affine formal algebraic spaces
representable étale over the target, then `P` holds on every affine étale diagram over `f`.

Given a diagram as in condition (1), the covering is refined against it by `href`; axiom (1)
of locality carries `P` from the members of the covering to the refined charts, and axioms (2)
and (3) descend it along the finite covering of the chart `U₀` so obtained. -/
@[stacks 0ANG "condition (3) implies condition (1), with the refinement of the covering \
(Stacks 0AJ2 and quasi-compactness of an affine formal algebraic space) and the locality axioms \
of Situation 0CBA read through Stacks 0AN8 and Stacks 0AN9 carried as hypotheses"]
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS C P)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS C P)
    (href : HasEtaleRefinementOfSourceCover B S hS f)
    (hf : HasPropertyAfterSourceCover B S hS C P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := by
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaffine hVetale hVsquare hVproperty using hfac
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂⟩ :=
    href U V u v t hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  refine hdesc τ hU₀ hV₀ σ hσ W Z p m c hWcover hZaffine hc hsq₂ fun s ↦ ?_
  exact hasc (t (k s)) (m s) (q s) (r s) (hUcover.1 (k s)) (hVaffine (k s)) (hWcover.1 s)
    (hZaffine s) (hq s) (hr s) (hsq₁ s) (hVproperty (k s))

end AlgebraicGeometry.FormalSpace

end
