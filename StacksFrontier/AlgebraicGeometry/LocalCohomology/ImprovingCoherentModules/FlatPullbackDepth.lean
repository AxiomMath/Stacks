module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.OpenExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Depth two on stalks under a flat pullback

A flat morphism carries the bound `depth 𝒪_{X,x}(F_x) ≥ 2` on the stalk of a coherent module to
the same bound on the stalk of its pullback. The stalk of the pullback is the base change of the
stalk, and the depth of a base change along a flat local homomorphism is the depth downstairs
plus the depth of the fibre, so dropping the fibre term leaves the bound intact.

This is the mechanism behind the flat-pullback assertion of [Stacks, Tag 0DX4]: for an open
immersion `j : U → X` and a coherent `𝒪_X`-module `F` with `F' = j_*(F|_U)` coherent, the depth
bound on `F'` along the complement of `U` is carried by a flat `f : Y → X` to the depth bound on
`f^*F'` along the complement of `f^{-1}(U)`, which is what makes `f^*F → f^*F'` the canonical
extension over `f^{-1}(U)`.

## Main results

* `AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat`: a flat pullback preserves the bound
  `depth ≥ 2` on the stalk of a coherent module.
* `AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict_of_depth`: the flat pullback
  of the canonical extension map is the canonical extension map over the inverse image of the
  open subscheme, assuming the depth bound on the complement of the open subscheme itself.
* `AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict_flat`: the same, with that
  depth bound discharged, so at the hypotheses of [Stacks, Tag 0DX4].
* `AlgebraicGeometry.isCoherent_pushforward_restrict_pullback_of_flat`: the coherence
  hypothesis of [Stacks, Tag 0DX4] holds again for `f^{-1}(U) ⊆ Y` and `f^*F`.

## Implementation notes

The stalk of a pullback is identified with the base change of the stalk by
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` ([Stacks, Tag 0098]), whose
tensor factors are already in the order `Module.depth_tensorProduct_of_flat` ([Stacks, Tag 0338])
expects, so no commutation of the tensor product is needed. Finiteness of the stalk over the
local ring is `SheafOfModules.finite_stalk`, flatness of the stalk map is Mathlib's
`AlgebraicGeometry.Flat.stalkMap`, and the transport of depth along the resulting linear
equivalence is `Module.depth_eq_depth_of_linearEquiv`.

The module structure on a stalk is spelled out in both the hypothesis and the conclusion, because
the stalk of an `𝒪_X`-module is built as an abelian group and carries no such instance by
default. The same spelling is used in
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two` and in
`AlgebraicGeometry.unique_iso_pushforward_restrict`, so the two fit together without transport.

The depth bound `depth 𝒪_{X,x}(F'_x) ≥ 2` for `x` outside `U`, which Tag 0DX4 asserts
unconditionally, is [Stacks, Tag 0EY0] part (3); applied to `F'`, which is canonically the
pushforward of its own restriction by `AlgebraicGeometry.isIso_unit_app_pushforward`, it is
`AlgebraicGeometry.two_le_depth_stalk_pushforward_restrict`.

## References

* [Stacks Project, Tag 0DX4](https://stacks.math.columbia.edu/tag/0DX4)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A flat morphism carries the bound `depth 𝒪_{X,f y}(G_{f y}) ≥ 2` on the stalk of a module of
finite type to the bound `depth 𝒪_{Y,y}((f^*G)_y) ≥ 2` on the stalk of its pullback.

The stalk of `f^*G` at `y` is `𝒪_{Y,y} ⊗_{𝒪_{X,f y}} G_{f y}`, and the depth of that base change
is `depth G_{f y}` plus the depth of the fibre `𝒪_{Y,y}/𝔪_{f y}𝒪_{Y,y}`, which is at least the
former. Only finite type of `G` is used, through finiteness of the stalk downstairs. -/
public theorem two_le_depth_stalk_pullback_of_flat {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X) [Flat f]
    (G : X.Modules) [G.IsFiniteType] (y : Y)
    (hdepth :
      letI : Module (X.presheaf.stalk (f.base y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val (f.base y)
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk (f.base y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y)))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y))) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) := by
  dsimp only at hdepth ⊢
  let R := X.presheaf.stalk (f.base y)
  let S := Y.presheaf.stalk y
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback f).obj G).val.presheaf y
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) G.val (f.base y)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
  let : Algebra R S := (f.stalkMap y).hom.toAlgebra
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing S := inferInstance
  have : Module.Finite R M := SheafOfModules.finite_stalk X.sheaf G (f.base y)
  have : IsLocalHom (algebraMap R S) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat R S := Flat.stalkMap f y
  have hformula := Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := M) (N := S)
  obtain ⟨E, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom G y
  have hdepthEq : Module.depth S (IsLocalRing.maximalIdeal S) N =
      Module.depth S (IsLocalRing.maximalIdeal S) (TensorProduct R S M) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) E
  show (2 : ℕ∞) ≤ Module.depth S (IsLocalRing.maximalIdeal S) N
  rw [hdepthEq, hformula]
  exact le_trans hdepth (le_add_of_nonneg_right (by positivity))

/-- The flat pullback of the canonical extension map `F → j_*(F|_U)` is the canonical extension
map over `f^{-1}(U)`: there is a unique isomorphism between `f^*j_*(F|_U)` and the extension of
`(f^*F)|_{f^{-1}(U)}` compatible with the two canonical maps out of `f^*F`.

The depth bound on the complement of `f^{-1}(U)` needed by
`AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict` is obtained from the depth
bound on the complement of `U` by `AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat`, so the
hypothesis here is the one [Stacks, Tag 0DX4] states on `X` itself rather than on `Y`. -/
public theorem existsUnique_iso_pullback_pushforward_restrict_of_depth
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent]
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      let F' := (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj F)
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F'.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F'.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F'.val.presheaf x)) :
    ∃! e : (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward U.ι).obj
          ((Scheme.Modules.pullback U.ι).obj F)) ≅
        (Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj
          ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback f).obj F)),
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback f).obj F) := by
  have : ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  refine existsUnique_iso_pullback_pushforward_restrict f F U fun y hy => ?_
  have hyU : f.base y ∉ (U : Set X) := by simpa using hy
  exact two_le_depth_stalk_pullback_of_flat f _ y (hdepth (f.base y) hyU)

/-- For a flat morphism `f : Y ⟶ X` of Noetherian schemes, `f^*F → f^*j_*(F|_U)` is the
canonical extension map for the open subscheme `f^{-1}(U) ⊆ Y`: there is a unique isomorphism
between `f^*j_*(F|_U)` and `j'_*((f^*F)|_{f^{-1}(U)})` compatible with the two canonical maps out
of `f^*F`. -/
@[stacks 0DX4 "flat pullback compatibility: the pullback of the canonical map is the canonical \
map for the inverse image of U"]
public theorem existsUnique_iso_pullback_pushforward_restrict_flat
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent] :
    ∃! e : (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward U.ι).obj
          ((Scheme.Modules.pullback U.ι).obj F)) ≅
        (Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj
          ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback f).obj F)),
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback f).obj F) :=
  existsUnique_iso_pullback_pushforward_restrict_of_depth f F U
    (two_le_depth_stalk_pushforward_restrict X F U)

/-- For a flat morphism `f : Y ⟶ X` of Noetherian schemes, the coherence hypothesis of
[Stacks, Tag 0DX4] holds again downstairs: `j'_*((f^*F)|_{f^{-1}(U)})` is a coherent
`𝒪_Y`-module. With `f^*F` coherent (`AlgebraicGeometry.isCoherent_pullback`), [Stacks, Tag 0DX4]
therefore applies to `f : Y ⟶ X`, `f^{-1}(U)` and `f^*F`. -/
@[stacks 0DX4 "flat pullback compatibility: the coherence hypothesis of the source holds again \
for the inverse image of U, so the lemma applies verbatim downstairs"]
public theorem isCoherent_pushforward_restrict_pullback_of_flat
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent] :
    ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback f).obj F))).IsCoherent := by
  obtain ⟨e, -⟩ := existsUnique_iso_pullback_pushforward_restrict_flat f F U
  have hc : ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj F))).IsCoherent := flat_pullback_coherent f F U
  have hfp : ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj F))).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent _
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation _
    ((SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e hfp)

end AlgebraicGeometry

end
