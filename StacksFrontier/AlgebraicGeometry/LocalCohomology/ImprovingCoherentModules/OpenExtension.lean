module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The extension of a coherent module across the complement of an open subscheme

Let `j : U → X` be an open immersion of schemes and let `F` be a coherent `𝒪_X`-module whose
extension `F' = j_*(F|_U)` is again coherent. The unit of the pullback--pushforward adjunction
is a map `F → F'` which is an isomorphism over `U`. Together with a depth bound on the
complement this pins the map down: any coherent module carrying a map from `F` which is
invertible over `U` and whose stalks on the complement have depth at least two is uniquely
isomorphic to `F'` under `F`.

Along a morphism `f : Y → X` the pullback of `F'` is coherent, and the pullback of the
canonical map `F → F'` is again invertible over `f^{-1}(U)`, so `f^*F → f^*F'` is a candidate
for the same extension over `f^{-1}(U)`; once the complement of `f^{-1}(U)` is known to carry
depth at least two, it is the canonical map there.

## Main results

* `AlgebraicGeometry.isIso_unit_app_pushforward`: a pushforward along an open immersion is
  canonically the extension of its own restriction.
* `AlgebraicGeometry.isIso_pullback_map_unit`: the canonical map restricts to an isomorphism
  over `U`.
* `AlgebraicGeometry.two_le_depth_stalk_pushforward_restrict`: the extension has depth at least
  two on the complement of `U`.
* `AlgebraicGeometry.unique_iso_pushforward_restrict`: the uniqueness of the extension under
  the original module.
* `AlgebraicGeometry.flat_pullback_coherent`: coherence of the pullback of the extension
  along a flat morphism.
* `AlgebraicGeometry.isIso_pullback_restrict_map_pullback`: a morphism invertible after
  restriction to `U` stays invertible after pullback along `f` and restriction to `f^{-1}(U)`.
* `AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict`: the pullback of the
  canonical map is the canonical map over `f^{-1}(U)`, under a depth hypothesis on the
  complement of `f^{-1}(U)`.

## Implementation notes

Restriction to the open subscheme `U` is pullback along `U.ι`, and the canonical map from a
module to the extension of its restriction is the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. The uniqueness is a formal
consequence of the unit being invertible on a module with depth at least two on the
complement, which is `AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`:
the comparison map is then the composite of that unit with the pushforward of the inverse of
the restricted map, and two maps to the extension agreeing under `F` agree because pullback
along `U.ι` is faithful on the relevant hom set.

The module structure on a stalk is spelled out in the depth hypothesis, because the stalk of
an `𝒪_X`-module is built as an abelian group and carries no such instance by default.

Coherence of `f^*F'` needs only a locally Noetherian source, not flatness of `f`: it is
`AlgebraicGeometry.isCoherent_pullback`.

The depth bound for `F'` itself on the complement of `U` is [Stacks, Tag 0EY0] part (3): a
quasi-compact quasi-separated pushforward has depth at least two at a point outside the image.
For the open immersion `U.ι` that is
`Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem`, and
its hypothesis, that the module is canonically the pushforward of its own restriction, holds
for `F'` by `AlgebraicGeometry.isIso_unit_app_pushforward`, since the counit of the adjunction is
invertible along an open immersion.

The depth hypothesis in `AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict` is
the bound on the complement of `f^{-1}(U)` in `Y`, not on the complement of `U` in `X`; for flat
`f` it follows from the bound on `X` by
`AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict_flat`.

## References

* [Stacks Project, Tag 0DX4](https://stacks.math.columbia.edu/tag/0DX4)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an adjunction `L ⊣ R` and a morphism `φ : F ⟶ G` whose image under `L` is invertible,
the target `G` is uniquely isomorphic to `R.obj (L.obj F)` under `F` as soon as the unit of the
adjunction at `G` is invertible.

The isomorphism is the unit at `G` followed by `R` applied to the inverse of `L.map φ`;
uniqueness holds because `L.map φ` is epic and `R.obj (L.obj F)` represents morphisms out of
`L.obj F`. -/
private theorem existsUnique_iso_of_isIso_unit {C : Type*} {D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {F G : C} (φ : F ⟶ G)
    [IsIso (L.map φ)] [IsIso (adj.unit.app G)] :
    ∃! e : G ≅ R.obj (L.obj F), φ ≫ e.hom = adj.unit.app F := by
  have heq : φ ≫ (adj.unit.app G ≫ R.map (inv (L.map φ))) = adj.unit.app F := by
    rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← Functor.map_comp,
      IsIso.hom_inv_id]
    simp
  refine ⟨asIso (adj.unit.app G ≫ R.map (inv (L.map φ))), heq, fun e' he' => Iso.ext ?_⟩
  have hrestr : L.map e'.hom = L.map (adj.unit.app G ≫ R.map (inv (L.map φ))) :=
    (cancel_epi (L.map φ)).1 <| by rw [← Functor.map_comp, ← Functor.map_comp, he', heq]
  refine (adj.homEquiv G (L.obj F)).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hrestr]
  rfl

/-- The unit of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` along the
inclusion of an open subscheme is an isomorphism at a pushforward: `j_*M` is canonically the
extension of its own restriction `(j_*M)|_U`.

The counit `j^*j_* ⟹ 𝟭` is invertible because `j_*` is fully faithful along an open immersion,
and the right unitality triangle then exhibits the unit at `j_*M` as the inverse of `j_*` applied
to the counit at `M`. -/
public theorem isIso_unit_app_pushforward {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
      ((Scheme.Modules.pushforward U.ι).obj M)) := by
  rw [← Adjunction.inv_counit_map (Scheme.Modules.pullbackPushforwardAdjunction U.ι)]
  infer_instance

/-- The canonical map `F → j_*(F|_U)` becomes an isomorphism after restriction to the open
subscheme `U`.

This is the left unitality triangle of the pullback--pushforward adjunction together with
invertibility of its counit along an open immersion. -/
@[stacks 0DX4 "clause (1) for the canonical map: it restricts to an isomorphism over U"]
public theorem isIso_pullback_map_unit {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    IsIso ((Scheme.Modules.pullback U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F)) :=
  inferInstance

/-- The stalks of the extension `F' = j_*(F|_U)` of a module along an open subscheme have depth
at least two at every point outside `U`.

The module `F'` is canonically the pushforward of its own restriction to `U`, by
`AlgebraicGeometry.isIso_unit_app_pushforward`, so the bound is [Stacks, Tag 0EY0] part (3) for
the open immersion `U.ι`, which is
`Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem`.
Only finite type of `F'` is used, so coherence of `F` is not assumed. -/
@[stacks 0DX4 "clause (2) for the canonical map: the extension has depth at least two \
outside U"]
public theorem two_le_depth_stalk_pushforward_restrict
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent] :
    ∀ x : X, x ∉ (U : Set X) →
      let F' := (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj F)
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F'.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F'.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F'.val.presheaf x) := by
  intro x hx
  have : ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  exact Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem
    U _ (isIso_unit_app_pushforward U _) x hx

/-- A coherent module carrying a map from `F` which becomes an isomorphism over the open
subscheme `U` and whose stalks have depth at least two outside `U` is uniquely isomorphic,
under `F`, to the extension `j_*(F|_U)` of the restriction of `F`. -/
@[stacks 0DX4 "uniqueness under the original module"]
public theorem unique_iso_pushforward_restrict
    (X : Scheme.{u}) [IsNoetherian X] (F G : X.Modules)
    [F.IsCoherent] [G.IsCoherent] (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent]
    (φ : F ⟶ G)
    (hφ : IsIso ((Scheme.Modules.pullback U.ι).map φ))
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x
      letI : Module (X.presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) M) :
    ∃! e : G ≅ (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F),
      φ ≫ e.hom = (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F := by
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two X G U hdepth
  exact existsUnique_iso_of_isIso_unit (Scheme.Modules.pullbackPushforwardAdjunction U.ι) φ

/-- The pullback of the extension `j_*(F|_U)` along a flat morphism is coherent.

Flatness of `f` is not needed: coherence of a pullback needs only a locally Noetherian source,
by [Stacks, Tag 0EBF]. -/
@[stacks 0DX4 "flat pullback coherence"]
public theorem flat_pullback_coherent
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent] :
    ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj F))).IsCoherent :=
  isCoherent_pullback f _

/-- A morphism of `𝒪_X`-modules which becomes an isomorphism after restriction to an open
subscheme `U` becomes an isomorphism after pullback along `f : Y ⟶ X` and restriction to
`f^{-1}(U)`.

The restriction of `f` to `f^{-1}(U) ⟶ U` composed with the inclusion of `U` is the inclusion
of `f^{-1}(U)` composed with `f`, so pullback along the two composites agree; one of them is
pullback along `f` followed by restriction to `f^{-1}(U)`, the other is restriction to `U`
followed by pullback along the restricted morphism. -/
public theorem isIso_pullback_restrict_map_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens)
    (hφ : IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map φ)) := by
  have : IsIso ((Scheme.Modules.pullback (morphismRestrict f U ≫ U.ι)).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp (morphismRestrict f U) U.ι) φ).mp
      (inferInstanceAs (IsIso ((Scheme.Modules.pullback (morphismRestrict f U)).map
        ((Scheme.Modules.pullback U.ι).map φ))))
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f) φ).mpr
    ((NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U)) φ).mp this)

/-- Under a depth hypothesis on the complement of `f^{-1}(U)`, the pullback along `f` of the
canonical map `F → j_*(F|_U)` is the canonical map over `f^{-1}(U)`: there is a unique
isomorphism between `f^*j_*(F|_U)` and the extension of `(f^*F)|_{f^{-1}(U)}` compatible with
the two canonical maps out of `f^*F`.

This is the pullback compatibility of [Stacks, Tag 0DX4]. The depth hypothesis is on the
complement of `f^{-1}(U)` in `Y`; for flat `f` it follows from
`AlgebraicGeometry.two_le_depth_stalk_pushforward_restrict`, which gives
`AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict_flat`. -/
public theorem existsUnique_iso_pullback_pushforward_restrict
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [Flat f] (F : X.Modules) [F.IsCoherent]
    (U : X.Opens)
    [((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj F)).IsCoherent]
    (hdepth : ∀ y : Y, y ∉ ((f ⁻¹ᵁ U : Y.Opens) : Set Y) →
      let G := (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj F))
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y
      letI : Module (Y.presheaf.stalk y) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          G.val y
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) M) :
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
  have hG : ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj F))).IsCoherent := flat_pullback_coherent f F U
  have : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F))) :=
    isIso_pullback_restrict_map_pullback f _ U inferInstance
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι).unit.app
      ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj F)))) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two Y _ (f ⁻¹ᵁ U) hdepth
  exact existsUnique_iso_of_isIso_unit
    (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι) _

end AlgebraicGeometry

end
