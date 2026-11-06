module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Properties of the relative Proj of an algebraic space, read on its scheme points

Let `π : P ⟶ X` be a morphism of algebraic spaces presented as a relative Proj over the scheme
points of `X` (`AlgebraicGeometry.Space.RelativeProjPoints`, the second assertion of
Stacks 084B): for every scheme point `g : T ⟶ X` the base change `T ×_X P` is the scheme
`Proj_T(g^*𝒜)` over `T`. A property of morphisms of schemes, stable under base change, of the
structure morphism `Proj_T(g^*𝒜) ⟶ T` is then a property of the base change of `π` along `g`;
for one surjective étale `g` this is the input of the étale-local-on-the-target criteria of
Morphisms of Spaces. This is how the source proves Stacks 084E–084H from the case of schemes.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.presheaf_pullback_snd` and
  `AlgebraicGeometry.Space.RelativeProjPoints.presheaf_pullback_fst`: a base-change-stable
  property of `Proj_T(g^*𝒜) ⟶ T` holds, in the representable sense, for the base change of `π`
  along `g`.
* `AlgebraicGeometry.Space.RelativeProjPoints.holdsOnSurjectiveEtaleChart`: condition (2) of
  Stacks 03MJ for `π`, from one surjective étale scheme point.
* `AlgebraicGeometry.Space.RelativeProjPoints.isQuasiCompact_of_etalePoint`,
  `AlgebraicGeometry.Space.RelativeProjPoints.isLocallyOfFiniteType_of_etalePoint` and
  `AlgebraicGeometry.Space.RelativeProjPoints.universallyClosed_of_etalePoint`: quasi-compactness,
  local finite type and universal closedness of `π` from those of `Proj_T(g^*𝒜) ⟶ T` at one
  surjective étale scheme point `g`.
* `AlgebraicGeometry.Space.RelativeProjPoints.exists_etalePoint`: an algebraic space has a
  surjective étale scheme point.
* `AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints`: a property of
  quasi-coherent graded algebras on schemes holds for the restriction `g^*𝒜` of the graded
  algebra of Situation 0849 at every étale scheme point `g`; this is how an étale-local condition
  on `𝒜` is read.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

universe u m

namespace AlgebraicGeometry.Space

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X} (d : RelativeProjPoints B S hS π)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_EtaleChartReduction (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_EtaleChartReduction
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A property of scheme morphisms invariant under isomorphism which holds for the structure
morphism `Proj_T(g^*𝒜) ⟶ T` holds for the structure morphism of the base change of `π` along
`g`. -/
theorem map_fibreHom_property (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (h : Q (relativeProj (d.algebra T g)).toBase) :
    Q ((BigFppfOver.toScheme B S hS).map (d.fibreHom T g)) := by
  rw [d.fibreHom_comp]
  exact MorphismProperty.RespectsIso.precomp Q _ _ h

/-- A base-change-stable property of `Proj_T(g^*𝒜) ⟶ T` holds, in the representable sense, for
the morphism of represented functors underlying the base change of `π` along `g`. -/
theorem presheaf_yoneda_fibreHom {Q : MorphismProperty Scheme.{u}}
    (hQ : Q.IsStableUnderBaseChange) (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (h : Q (relativeProj (d.algebra T g)).toBase) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (d.fibreHom T g)) :=
  have := hQ.respectsIso
  presheaf_yoneda_map_of_inverseImage B S hS hQ (d.fibreHom T g) (d.map_fibreHom_property Q T g h)

/-- **A base-change-stable property of `Proj_T(g^*𝒜) ⟶ T` holds for `pullback.snd π g`.** -/
theorem presheaf_pullback_snd {Q : MorphismProperty Scheme.{u}}
    (hQ : Q.IsStableUnderBaseChange) (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (h : Q (relativeProj (d.algebra T g)).toBase) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd π g) := by
  refine (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := (d.isPullback T g).isoPullback.inv)
      (g := 𝟙 (yoneda.obj T)) ⟨?_⟩) (d.presheaf_yoneda_fibreHom hQ T g h)
  rw [Category.comp_id]
  exact (d.isPullback T g).isoPullback_inv_snd

/-- **A base-change-stable property of `Proj_T(g^*𝒜) ⟶ T` holds for `pullback.fst g π`.** -/
theorem presheaf_pullback_fst {Q : MorphismProperty Scheme.{u}}
    (hQ : Q.IsStableUnderBaseChange) (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (h : Q (relativeProj (d.algebra T g)).toBase) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst g π) := by
  refine (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := (d.isPullback T g).flip.isoPullback.inv)
      (g := 𝟙 (yoneda.obj T)) ⟨?_⟩) (d.presheaf_yoneda_fibreHom hQ T g h)
  rw [Category.comp_id]
  exact (d.isPullback T g).flip.isoPullback_inv_fst

/-- **Condition (2) of Stacks 03MJ for `π`, from one surjective étale scheme point**: the base
change of `π` along a surjective étale scheme point `g` is a surjective étale chart of `P` over
the chart `g` of `X`, and its underlying morphism of schemes is `Proj_T(g^*𝒜) ⟶ T`. -/
theorem holdsOnSurjectiveEtaleChart (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (hgEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (hgSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (h : Q (relativeProj (d.algebra T g)).toBase) :
    HoldsOnSurjectiveEtaleChart B S hS Q π :=
  ⟨d.fibre T g, T, d.fibreToSpace T g, g, d.fibreHom T g,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (d.isPullback T g).flip
      hgEt,
    hgEt,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (d.isPullback T g).flip
      hgSurj,
    (d.isPullback T g).w.symm, d.map_fibreHom_property Q T g h⟩

/-- **Quasi-compactness of `π` from one surjective étale scheme point** (Stacks 03KG): if
`Proj_T(g^*𝒜) ⟶ T` is quasi-compact for a surjective étale scheme point `g` of `X`, then `π` is
quasi-compact. -/
theorem isQuasiCompact_of_etalePoint (hP : IsAlgebraicSpace B S hS P)
    (hX : IsAlgebraicSpace B S hS X) (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (hgEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (hgSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (h : AlgebraicGeometry.QuasiCompact (relativeProj (d.algebra T g)).toBase) :
    IsQuasiCompact B S hS π :=
  isQuasiCompact_of_surjectiveEtale_atlas B S hS π hP hX T g
    (isSurjective_of_presheafSurjective B S hS g hgSurj)
    ((isEtale_iff_presheaf_of_yoneda B S hS g).2 hgEt)
    (isQuasiCompact_of_presheaf_quasiCompact B S hS
      (d.presheaf_pullback_snd AlgebraicGeometry.quasiCompact_isStableUnderBaseChange T g h))

/-- **Local finite type of `π` from one surjective étale scheme point** (Stacks 040Y): if
`Proj_T(g^*𝒜) ⟶ T` is locally of finite type for a surjective étale scheme point `g` of `X`,
then `π` is locally of finite type. -/
theorem isLocallyOfFiniteType_of_etalePoint (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (hgEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (hgSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (h : AlgebraicGeometry.LocallyOfFiniteType (relativeProj (d.algebra T g)).toBase) :
    IsLocallyOfFiniteType B S hS π :=
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart B S hS
    (d.holdsOnSurjectiveEtaleChart (@AlgebraicGeometry.LocallyOfFiniteType.{u}) T g hgEt
      hgSurj h)

/-- **Universal closedness of `π` from one surjective étale scheme point** (Stacks 03IT): if
`Proj_T(g^*𝒜) ⟶ T` is universally closed for a surjective étale scheme point `g` of `X`, then
`π` is universally closed. -/
theorem universallyClosed_of_etalePoint (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X)
    (hgEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (hgSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g)
    (h : AlgebraicGeometry.UniversallyClosed (relativeProj (d.algebra T g)).toBase) :
    UniversallyClosed B S hS π := by
  refine universallyClosed_of_etale_atlas B S hS hX π T g
    (isSurjective_of_presheafSurjective B S hS g hgSurj)
    ((isEtale_iff_presheaf_of_yoneda B S hS g).2 hgEt) ?_
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hyon : UniversallyClosed B S hS (yoneda.map (d.fibreHom T g)) :=
    universallyClosed_yoneda_map B S hS (d.fibreHom T g)
      (d.map_fibreHom_property (@AlgebraicGeometry.UniversallyClosed.{u}) T g h)
  have hc := universallyClosed_comp B S hS
    (isAlgebraicSpace_yoneda B S hS (d.fibre T g)) (isAlgebraicSpace_yoneda B S hS T)
    (d.isPullback T g).flip.isoPullback.inv (yoneda.map (d.fibreHom T g))
    (universallyClosed_of_isIso B S hS _) hyon
  rwa [(d.isPullback T g).flip.isoPullback_inv_fst] at hc

include d in
/-- **An algebraic space has a surjective étale scheme point**: its atlas. -/
theorem exists_etalePoint (hX : IsAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
        Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g := by
  obtain ⟨T, g, hsurj, het⟩ := hX.exists_atlas
  exact ⟨T, g, het, hsurj⟩

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **A property of quasi-coherent graded algebras holds for `𝒜` étale locally**: it holds for
the restriction `g^*𝒜` of the graded algebra of Situation 0849 at every étale scheme point
`g : T ⟶ X`. The restriction is the one of Stacks 084B, `s.relativeProjPoints.algebra T g`. -/
def HoldsAtEtalePoints
    (p : ∀ {T : Scheme.{u}}, Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra T →
      Prop) : Prop :=
  ∀ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g →
    p (s.relativeProjPoints.algebra T g)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
