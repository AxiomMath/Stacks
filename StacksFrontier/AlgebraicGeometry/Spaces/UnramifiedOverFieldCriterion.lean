module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.GeometricallyReducedOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyQuasiFiniteOverFieldRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Algebraic spaces unramified over a field

Let `k` be a field and `G` an algebraic space locally of finite type over `k`. Then `G` is
unramified over `k` if and only if `G` is geometrically reduced over `k` and of dimension at
most zero. This is the equivalence of conditions (3)(b) and (3)(c) in Stacks 0DSW, whose proof
says: such a `G` is a scheme by Stacks 06LZ, and an affine open of it is proper over `k`, so
Stacks 0BUG applies.

## Main results

* `AlgebraicGeometry.Space.isUnramified_iff_isGeometricallyReduced_and_dimension_le_zero`: an
  algebraic space locally of finite type over a field is unramified over it exactly when it is
  geometrically reduced and of dimension at most zero.
* `AlgebraicGeometry.Space.isUnramified_iff_isGeometricallyReduced_viewOver_and_dimension_le_zero`:
  the same over a scheme of the site isomorphic to `Spec k`, the space being viewed over `Spec k`
  along the isomorphism (Stacks 03I5 (2)); this is the form a field-valued point of an algebraic
  stack presents.

## Implementation notes

The space lives over the big fppf site of `Spec k`, and its structure morphism goes to the
terminal object of that site, which is how the automorphism group algebraic space of a
field-valued point of an algebraic stack (Stacks 04YP) is presented.

Either side makes the space locally quasi-finite over `k`: an unramified morphism is locally
quasi-finite, and dimension at most zero is local quasi-finiteness by Stacks 0ACA
(`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero`). Then the space is
representable (`AlgebraicGeometry.Space.isRepresentable_of_isLocallyQuasiFinite_to_field`, the
scheme clause of Stacks 06LZ (2)), and the three conditions are read off the representing
scheme: unramifiedness and local quasi-finiteness by Stacks 03MJ at a morphism of the site,
geometric reducedness by Stacks 0DMS at the representing chart. The scheme statement is
`AlgebraicGeometry.unramified_iff_locallyQuasiFinite_and_geometricallyReduced`.

The dimension is bounded by `0` rather than required to equal `0`: the empty space is
unramified over `k` and has dimension `⊥`.

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0DMS](https://stacks.math.columbia.edu/tag/0DMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- An algebraic space `G` locally of finite type over a field `k` is unramified over `k` if and
only if it is geometrically reduced over `k` and has dimension at most zero. -/
theorem isUnramified_iff_isGeometricallyReduced_and_dimension_le_zero
    {G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B (Spec (.of k)) hk G)
    (g : G ⟶ yoneda.obj (⊤_ (BigFppfOver B (Spec (.of k)) hk)))
    (hlft : IsLocallyOfFiniteType B (Spec (.of k)) hk g) :
    IsUnramified B (Spec (.of k)) hk g ↔
      IsGeometricallyReduced k B hk G hG ∧ dimension B (Spec (.of k)) hk G hG ≤ 0 := by
  let T := ⊤_ (BigFppfOver B (Spec (.of k)) hk)
  let eT : T ≅ Over.mk (𝟙 (B.obj hk)) := terminalIsoIsTerminal Over.mkIdTerminal
  have hTiso : IsIso T.hom := by
    have : IsIso eT.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eT.hom))
    rw [← Over.w eT.hom]
    exact inferInstanceAs (IsIso (eT.hom.left ≫ 𝟙 _))
  let τ : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T ≅ Spec (.of k) :=
    asIso (B.inclusion.map T.hom)
  have hsub : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :=
    ⟨fun a b => τ.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  rw [← isLocallyQuasiFinite_iff_dimension_le_zero B (Spec (.of k)) hk hG hsub g hlft]
  suffices key : IsLocallyQuasiFinite B (Spec (.of k)) hk g →
      (IsUnramified B (Spec (.of k)) hk g ↔
        IsGeometricallyReduced k B hk G hG ∧ IsLocallyQuasiFinite B (Spec (.of k)) hk g) by
    refine ⟨fun h => (key ?_).mp h, fun h => (key h.2).mpr h⟩
    exact holdsOnEveryEtaleChart_mono B (Spec (.of k)) hk
      (fun f hf => by have := hf; exact ⟨inferInstance, inferInstance⟩) h
  intro hlqf
  have : G.IsRepresentable :=
    isRepresentable_of_isLocallyQuasiFinite_to_field B (Spec (.of k)) hk τ hG g hlqf
  let w := G.reprW
  let φ : G.reprX ⟶ T := yoneda.preimage (w.hom ≫ g)
  have hφ : yoneda.map φ = w.hom ≫ g := Functor.map_preimage _ _
  have htr : ∀ P : MorphismProperty Scheme.{u},
      HoldsOnEveryEtaleChart B (Spec (.of k)) hk P g ↔
        HoldsOnEveryEtaleChart B (Spec (.of k)) hk P (yoneda.map φ) := by
    intro P
    have := holdsOnEveryEtaleChart_respectsIso_presheaf B (Spec (.of k)) hk P
    rw [hφ]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (fun ⦃F G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B (Spec (.of k)) hk P f) w.hom g).symm
  let ψ : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj G.reprX ⟶ Spec (.of k) :=
    B.inclusion.map G.reprX.hom
  have hψ : ψ = (BigFppfOver.toScheme B (Spec (.of k)) hk).map φ ≫ τ.hom := by
    simp only [ψ, τ, asIso_hom, BigFppfOver.toScheme, Functor.comp_map, Over.forget_map,
      ← Functor.map_comp, Over.w φ]
  have hcancel : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      P ψ ↔ P ((BigFppfOver.toScheme B (Spec (.of k)) hk).map φ) := fun P _ => by
    rw [hψ, MorphismProperty.cancel_right_of_respectsIso P]
  have hU : IsUnramified B (Spec (.of k)) hk g ↔ Unramified ψ := by
    exact (htr _).trans ((holdsOnEveryEtaleChart_yoneda_map_iff B (Spec (.of k)) hk
      unramified_isEtaleLocalOnSourceAndTarget φ).trans (hcancel @Unramified.{u}).symm)
  have hLφ : LocallyOfFiniteType ((BigFppfOver.toScheme B (Spec (.of k)) hk).map φ) :=
    (isLocallyOfFiniteType_yoneda_map_iff B (Spec (.of k)) hk φ).mp ((htr _).mp hlft)
  have hL : LocallyOfFiniteType ψ := by
    rw [hψ]
    infer_instance
  have hQ : IsLocallyQuasiFinite B (Spec (.of k)) hk g ↔ LocallyQuasiFinite ψ := by
    refine (htr _).trans ((isLocallyQuasiFinite_yoneda_map_iff B (Spec (.of k)) hk φ).trans ?_)
    exact (and_iff_right hLφ).trans (hcancel @LocallyQuasiFinite.{u}).symm
  have hR : IsGeometricallyReduced k B hk G hG ↔ GeometricallyReduced ψ := by
    have hwet : IsEtale B (Spec (.of k)) hk w.hom := isEtale_of_isIso B (Spec (.of k)) hk w.hom
    have hwsurj : IsSurjective B (Spec (.of k)) hk w.hom := fun y => by
      refine ⟨pointsMap B (Spec (.of k)) hk G w.inv y, ?_⟩
      have h := congrFun (pointsMap_comp B (Spec (.of k)) hk G w.inv w.hom) y
      rw [w.inv_hom_id, pointsMap_id] at h
      exact h.symm
    exact ⟨fun h => (isGeometricallyReduced_iff_forall_etaleChart k B hk G hG).mp h _ w.hom hwet,
      fun h => (isGeometricallyReduced_iff_exists_surjective_etaleChart k B hk G hG).mpr
        ⟨_, w.hom, hwsurj, hwet, h⟩⟩
  rw [hU, hR, hQ, unramified_iff_locallyQuasiFinite_and_geometricallyReduced k ψ, and_comm]

/-- An algebraic space `G` locally of finite type over a scheme `W` of the site, together with an
isomorphism `ι` of the site from `W` onto `Spec k`, is unramified over `W` if and only if `G`,
viewed over `Spec k` along `ι` (Stacks 03I5 (2)), is geometrically reduced over `k` and has
dimension at most zero. A field-valued point of an algebraic stack records its field spectrum only
up to such an isomorphism, so this is the form of the criterion its automorphism group algebraic
space meets. -/
theorem isUnramified_iff_isGeometricallyReduced_viewOver_and_dimension_le_zero
    {W : Scheme.{u}} (hW : B.Contains W) (ι : B.obj hW ⟶ B.obj hk) [IsIso ι]
    {G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B W hW G)
    (g : G ⟶ yoneda.obj (⊤_ (BigFppfOver B W hW)))
    (hlft : IsLocallyOfFiniteType B W hW g) :
    IsUnramified B W hW g ↔
      IsGeometricallyReduced k B hk ((OverShriek.relocalizePresheafFunctor ι).obj G)
          (isAlgebraicSpace_viewOver B W (Spec (.of k)) hW hk ι G hG) ∧
        dimension B (Spec (.of k)) hk ((OverShriek.relocalizePresheafFunctor ι).obj G)
          (isAlgebraicSpace_viewOver B W (Spec (.of k)) hW hk ι G hG) ≤ 0 := by
  have hT : IsTerminal (Over.mk ι) :=
    Over.mkIdTerminal.ofIso (Over.isoMk (asIso ι) (by simp)).symm
  have : IsIso (terminal.from (Over.mk ι)) := isIso_of_isTerminal hT terminalIsTerminal _
  let g' := OverShriek.relocalizeToYoneda ι G ≫ yoneda.map (terminal.from (Over.mk ι))
  have key : ∀ P : MorphismProperty Scheme.{u},
      HoldsOnEveryEtaleChart B W hW P g ↔ HoldsOnEveryEtaleChart B (Spec (.of k)) hk P g' := by
    intro P
    have hg : g = toYonedaId B W hW G ≫ yoneda.map (terminal.from _) := by
      ext Z x
      exact terminalIsTerminal.hom_ext _ _
    have : IsIso (terminal.from (Over.mk (𝟙 (B.obj hW)))) :=
      isIso_of_isTerminal Over.mkIdTerminal terminalIsTerminal _
    rw [holdsOnEveryEtaleChart_comp_iso_iff, holdsOnEveryEtaleChart_relocalizeToYoneda_iff, hg,
      holdsOnEveryEtaleChart_comp_iso_iff]
  exact (key _).trans (isUnramified_iff_isGeometricallyReduced_and_dimension_le_zero k B hk
    (isAlgebraicSpace_viewOver B W (Spec (.of k)) hW hk ι G hG) g' ((key _).mp hlft))

end AlgebraicGeometry.Space
