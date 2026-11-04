module

public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Regularity of an algebraic space under base change along a flat preimmersion

Let `G` be a regular algebraic space over a scheme `S` with a morphism `q : G ⟶ V` locally of
finite type to a scheme `V` of the site, and let `τ : T ⟶ V` be a morphism of the site whose
underlying morphism of schemes is flat and a preimmersion, with `T` locally Noetherian — the
canonical morphism `Spec 𝒪_{V, v} ⟶ V` out of the spectrum of a local ring of a Noetherian `V`
is the case of interest. Then the base change `G ×_V T` is again regular.

A flat preimmersion induces isomorphisms on local rings
(`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`), and both flatness and being a
preimmersion are stable under base change; so for a regular étale atlas `Q ⟶ G` the base change
`Q ×_V T` has the local rings of `Q`, and it is locally Noetherian, being locally of finite type
over `T`. The base change of the atlas is an étale surjective atlas of `G ×_V T`.

## Main results

* `AlgebraicGeometry.isRegular_of_isIso_stalkMap`: a locally Noetherian scheme mapping to a
  regular scheme by a morphism which is an isomorphism on every local ring is regular.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_pullback_of_flat_isPreimmersion`:
  the base change of a regular algebraic space, locally of finite type over a scheme `V`, along
  a flat preimmersion `T ⟶ V` with `T` locally Noetherian is regular.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Regularity along isomorphisms of local rings.** A locally Noetherian scheme `Y` with a
morphism `i : Y ⟶ X` to a regular scheme which induces an isomorphism on every local ring is
regular: its local rings are those of `X`. -/
theorem isRegular_of_isIso_stalkMap {X Y : Scheme.{u}} (i : Y ⟶ X)
    (hi : ∀ y : Y, IsIso (i.stalkMap y)) (hY : IsLocallyNoetherian Y) (hX : IsRegular X) :
    IsRegular Y := by
  have hiff (W : Scheme.{u}) : IsRegular W ↔ IsLocallyNoetherian W ∧
      ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x) :=
    (isRegular_tfae W).out 1 2 (by simp) (by simp)
  obtain ⟨-, hregX⟩ := (hiff X).mp hX
  refine (hiff Y).mpr ⟨hY, fun y => ?_⟩
  have := hi y
  have := hregX (i y)
  exact IsRegularLocalRing.of_ringEquiv (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv

namespace Space

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Regularity under base change along a flat preimmersion.** Let `G` be a regular algebraic
space over `S`, let `q : G ⟶ V` be locally of finite type with `V` an object of the site, and let
`τ : T ⟶ V` be a morphism of the site whose underlying morphism of schemes is a flat
preimmersion, with `T` locally Noetherian. Then `G ×_V T` is regular.

For a regular étale surjective atlas `a : Q ⟶ G` the composite `Q ⟶ G ⟶ V` comes from a
morphism `ρ : Q ⟶ V` of the site, and `Q ×_V T` is an étale surjective atlas of `G ×_V T`, the
represented square being cartesian. Its first projection to `Q` is a base change of `τ`, hence a
flat preimmersion, so it is an isomorphism on local rings; and its second projection to `T` is a
base change of `ρ`, which is locally of finite type, so `Q ×_V T` is locally Noetherian. -/
theorem hasEtaleLocalProperty_isRegular_pullback_of_flat_isPreimmersion
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {V T : BigFppfOver B S hS} (q : G ⟶ yoneda.obj V) (hq : IsLocallyOfFiniteType B S hS q)
    (τ : T ⟶ V) [Flat ((BigFppfOver.toScheme B S hS).map τ)]
    [IsPreimmersion ((BigFppfOver.toScheme B S hS).map τ)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hreg : HasEtaleLocalProperty B S hS G (fun Z : Scheme.{u} => IsRegular Z)) :
    HasEtaleLocalProperty B S hS (pullback q (yoneda.map τ))
      (fun Z : Scheme.{u} => IsRegular Z) := by
  let := B.hasPullbacks_schemes
  let Tsch := BigFppfOver.toScheme B S hS
  obtain ⟨Q, a, hsurj, het, hQ⟩ := hreg
  let ρ : Q ⟶ V := yoneda.preimage (a ≫ q)
  have hρ : yoneda.map ρ = a ≫ q := yoneda.map_preimage _
  let a' : yoneda.obj (pullback ρ τ) ⟶ pullback q (yoneda.map τ) :=
    pullback.lift (yoneda.map (pullback.fst ρ τ) ≫ a) (yoneda.map (pullback.snd ρ τ))
      (by rw [Category.assoc, ← hρ, ← Functor.map_comp, pullback.condition, Functor.map_comp])
  have hbig : IsPullback (yoneda.map (pullback.fst ρ τ)) (a' ≫ pullback.snd q (yoneda.map τ))
      (a ≫ q) (yoneda.map τ) := by
    rw [pullback.lift_snd, ← hρ]
    exact (IsPullback.of_hasPullback ρ τ).map yoneda
  have hleft : IsPullback (yoneda.map (pullback.fst ρ τ)) a' a
      (pullback.fst q (yoneda.map τ)) :=
    IsPullback.of_bot hbig (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  have hGT : IsAlgebraicSpace B S hS (pullback q (yoneda.map τ)) :=
    isAlgebraicSpace_pullback B S hS q (yoneda.map τ) hG (isAlgebraicSpace_yoneda B S hS T)
      (isAlgebraicSpace_yoneda B S hS V)
  -- the base-changed atlas is étale and surjective
  have hsurj' : IsSurjective B S hS a' :=
    isSurjective_of_isPullback B S hS
      (W := ⟨yoneda.obj (pullback ρ τ), isAlgebraicSpace_yoneda B S hS _⟩)
      (Z := ⟨yoneda.obj Q, isAlgebraicSpace_yoneda B S hS _⟩) (X := ⟨_, hGT⟩) (Y := ⟨G, hG⟩)
      (p := ObjectProperty.homMk (yoneda.map (pullback.fst ρ τ))) (q := ObjectProperty.homMk a')
      (g := ObjectProperty.homMk a) (f := ObjectProperty.homMk (pullback.fst q (yoneda.map τ)))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hleft)
      ((presheafSurjective_iff_isSurjective_yoneda B S hS G hG Q a).mp hsurj)
  refine ⟨pullback ρ τ, a', (presheafSurjective_iff_isSurjective_yoneda B S hS _ hGT _ a').mpr
    hsurj', (isEtale_iff_presheaf_of_yoneda B S hS a').mp
      (isEtale_of_isPullback_yoneda B S hS hleft
        ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr het)), ?_⟩
  -- the scheme `Q ×_V T` is regular
  have hsch : IsPullback (Tsch.map (pullback.fst ρ τ)) (Tsch.map (pullback.snd ρ τ))
      (Tsch.map ρ) (Tsch.map τ) := (IsPullback.of_hasPullback ρ τ).map Tsch
  have hρlft : LocallyOfFiniteType (Tsch.map ρ) :=
    hq Q V a (𝟙 _) ρ het ((isEtale_iff_presheaf_of_yoneda B S hS _).mp (isEtale_id B S hS _))
      (by rw [Category.comp_id, hρ])
  have : Flat (Tsch.map (pullback.fst ρ τ)) :=
    MorphismProperty.of_isPullback (P := @Flat) hsch.flip inferInstance
  have : IsPreimmersion (Tsch.map (pullback.fst ρ τ)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hsch.flip inferInstance
  have : LocallyOfFiniteType (Tsch.map (pullback.snd ρ τ)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hsch hρlft
  exact isRegular_of_isIso_stalkMap (Tsch.map (pullback.fst ρ τ))
    (fun y => isIso_stalkMap_of_flat_isPreimmersion _ y)
    (LocallyOfFiniteType.isLocallyNoetherian (Tsch.map (pullback.snd ρ τ))) hQ

end Space

end AlgebraicGeometry

end
