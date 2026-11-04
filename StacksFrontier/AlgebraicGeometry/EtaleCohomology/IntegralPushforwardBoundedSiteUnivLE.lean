module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite

/-!
# Direct image along an integral morphism on the small étale site of Stacks 021B, at any
coefficient universe

Part (1) of Stacks 04C2 on the small étale site of Stacks 021B, for sheaves of sets in any
universe `v` with `UnivLE.{u, v}`: the direct image along bounded small étale base change by a
morphism with integral underlying morphism of schemes carries surjections to surjections. The case
of sheaves of sets in `Type (u + 1)` is in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite`.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms_of_univLE`:
  for `f` with integral underlying morphism of schemes, the direct image of sheaves of sets along
  bounded small étale base change carries surjections to surjections, in any universe `v` with
  `UnivLE.{u, v}`.

## References

* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- **Stacks 04C2, part (1), on the small étale site of Stacks 021B.** Let `f : T ⟶ S` be a
morphism of the underlying category of a big étale site whose morphism of schemes is integral — a
finite morphism, for instance.  Then the direct image of sheaves of sets along bounded small
étale base change along `f` carries surjections to surjections, for sheaves of sets in any
universe `v` at least as large as `u`. -/
theorem smallEtaleBaseChange_pushforward_preservesEpimorphisms_of_univLE
    [IsIntegralHom (B.inclusion.map f)] [UnivLE.{u, v}] :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (Type v)
      (topology B S.obj S.property) (topology B T.obj T.property)).PreservesEpimorphisms := by
  have hc : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  have hc1 : (toEtaleSite B S.obj S.property ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ S.obj.smallEtaleTopology _
  have hc2 : (AlgebraicGeometry.smallEtaleBaseChange B f ⋙
      toEtaleSite B T.obj T.property).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B T.obj T.property) _
  have hiso :
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
            (Type v) S.obj.smallEtaleTopology T.obj.smallEtaleTopology ⋙
          (toEtaleSite B S.obj S.property).sheafPushforwardContinuous (Type v)
            (topology B S.obj S.property) S.obj.smallEtaleTopology ≅
        (toEtaleSite B T.obj T.property).sheafPushforwardContinuous (Type v)
            (topology B T.obj T.property) T.obj.smallEtaleTopology ⋙
          (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (Type v)
            (topology B S.obj S.property) (topology B T.obj T.property) :=
    Functor.sheafPushforwardContinuousComp' (F := toEtaleSite B S.obj S.property)
        (G := Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
        (Iso.refl _) _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousIso (toEtaleSiteBaseChangeIso B f).symm _ _ _ ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (F := AlgebraicGeometry.smallEtaleBaseChange B f)
          (G := toEtaleSite B T.obj T.property) (Iso.refl _) _ _ _ _).symm
  have : ∀ (U : B.Scheme) (X : (U.obj.Etale)ᵒᵖ),
      HasLimitsOfShape (StructuredArrow X (toEtaleSite B U.obj U.property).op) (Type v) :=
    fun _ _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have hlhs := preservesEpimorphisms_comp
    ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
      (Type v) S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
    ((toEtaleSite B S.obj S.property).sheafPushforwardContinuous (Type v)
      (topology B S.obj S.property) S.obj.smallEtaleTopology)
    (Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom
      (B.inclusion.map f))
    inferInstance
  let e := ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous (Type v)
    (topology B T.obj T.property) T.obj.smallEtaleTopology).asEquivalence
  have hcancel := preservesEpimorphisms_comp e.inverse
    (e.functor ⋙ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (Type v) (topology B S.obj S.property) (topology B T.obj T.property))
    inferInstance (Functor.PreservesEpimorphisms.of_iso hiso)
  exact Functor.PreservesEpimorphisms.of_iso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso _ ≪≫ Functor.leftUnitor _)

end AlgebraicGeometry.SmallEtale

end
