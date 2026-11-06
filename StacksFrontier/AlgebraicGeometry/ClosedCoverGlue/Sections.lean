module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic

/-!
# Glueing a section along with the invertible module

This file completes [Stacks, Tag 09NE]. `ClosedCoverGlue/Basic.lean` glues invertible modules
`L i` on a finite closed cover `f i : Z i ⟶ X` of a reduced scheme with discrete overlaps into
an invertible module `M` on `X`. Here prescribed sections `s i` of the `L i` are glued too: if
each `s i` is nonvanishing wherever `Z i` meets another member of the cover, there is a global
section `t` of `M` restricting to `s i` under the identifications.

## The construction

The sections are nonvanishing on the overlap locus `T`, so by
`exists_open_all_sections_trivial` there is one ambient open `W ⊇ T` on which *every* `s i`
trivializes its `L i`. The module produced by Basic.lean is modified over `W` — `replaceOnOpen`
forms the pullback of the unit of the restriction adjunction against the comparison, which
replaces `M` by a module agreeing with it away from `W` and carrying the glued section over
`W` — and the resulting `patchedClosedCoverModule` carries `patchedClosedCoverSection`.

Invertibility of the patched module is checked pointwise:
`isInvertible_of_pointwise_restrictIsoUnit` reduces it to exhibiting, around each point, an
isomorphism with the unit module, which
`patchedClosedCoverComparison_isIso_restrict` supplies on `W` and
`patchedClosedCoverComparison_isIso_of_single_component` supplies away from it, where the cover
is locally a single member.

## Main results

* `StacksTag09NE.exists_invertible_with_sections_of_closed_cover_discrete_intersections`:
  existence of the invertible module together with the glued section.

## References

* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u v

namespace StacksTag09NE

open Stacks.FiniteLocallyFree.ModuleTFAE
  (localGeneratorsDataOfTrivializations localGeneratorsDataOfTrivializations_isLocallyFreeData)


/-- Restriction of sheaves of modules along an open immersion preserves limits. -/
public theorem restrictFunctor_preservesLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesLimits (Scheme.Modules.restrictFunctor f) := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ : X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : (PresheafOfModules.pushforward φ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  have : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward φ
  exact (Adjunction.ofIsRightAdjoint (SheafOfModules.pushforward φ)).rightAdjoint_preservesLimits

/-- For `a : F ⟶ G` and an open `W`, the module obtained from `G` by replacing it with `F` over
`W`: the pullback of the unit `G ⟶ W.ι_* (G|_W)` of the restriction adjunction along
`W.ι_* (a|_W)`. -/
public noncomputable abbrev replaceOnOpen {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) : X.Modules :=
  pullback ((Scheme.Modules.restrictAdjunction W.ι).unit.app G)
    ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pushforward W.ι).map a)

/-- The morphism `F ⟶ replaceOnOpen a W` induced by `a` and by the unit `F ⟶ W.ι_* (F|_W)` of the
restriction adjunction. -/
public noncomputable def replaceOnOpenLift {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) : F ⟶ replaceOnOpen a W :=
  pullback.lift a ((Scheme.Modules.restrictAdjunction W.ι).unit.app F)
    ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality a)

/-- Composing `replaceOnOpenLift a W` with the first projection of the pullback gives `a`. -/
public theorem replaceOnOpenLift_fst {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    replaceOnOpenLift a W ≫ pullback.fst _ _ = a := pullback.lift_fst ..

/-- Composing `replaceOnOpenLift a W` with the second projection of the pullback gives the unit of
the restriction adjunction at `F`. -/
public theorem replaceOnOpenLift_snd {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    replaceOnOpenLift a W ≫ pullback.snd _ _ =
      (Scheme.Modules.restrictAdjunction W.ι).unit.app F := pullback.lift_snd ..

/-- The morphism `replaceOnOpenLift a W` becomes an isomorphism after restriction to `W`. -/
public theorem isIso_restrict_replaceOnOpenLift {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (W : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (replaceOnOpenLift a W)) := by
  let R := Scheme.Modules.restrictFunctor W.ι
  let adj := Scheme.Modules.restrictAdjunction W.ι
  have : PreservesLimits R := restrictFunctor_preservesLimits W.ι
  have hunit (N : X.Modules) : IsIso (R.map (adj.unit.app N)) := by
    dsimp only [R, adj]
    let b := (Scheme.Modules.restrictAdjunction W.ι).counit.app
      ((Scheme.Modules.restrictFunctor W.ι).obj N)
    have hb : IsIso b := inferInstance
    have ht : (Scheme.Modules.restrictFunctor W.ι).map
        ((Scheme.Modules.restrictAdjunction W.ι).unit.app N) ≫ b = 𝟙 _ :=
      (Scheme.Modules.restrictAdjunction W.ι).left_triangle_components N
    refine ⟨⟨b, ht, ?_⟩⟩
    apply (cancel_mono b).mp
    simp only [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have hsnd : IsIso (R.map (pullback.snd (adj.unit.app G)
      ((R ⋙ Scheme.Modules.pushforward W.ι).map a))) :=
    (R.map_isPullback (IsPullback.of_hasPullback _ _)).isIso_snd_of_isIso
  have heq : R.map (replaceOnOpenLift a W) ≫ R.map (pullback.snd _ _) =
      R.map (adj.unit.app F) := by
    rw [← R.map_comp, replaceOnOpenLift_snd]
  have hcomp : IsIso (R.map (replaceOnOpenLift a W) ≫ R.map (pullback.snd _ _)) := by
    rw [heq]
    infer_instance
  have hlift : R.map (replaceOnOpenLift a W) =
      R.map (adj.unit.app F) ≫ inv (R.map (pullback.snd _ _)) := by
    apply (cancel_mono (R.map (pullback.snd _ _))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, heq]
  rw [hlift]
  infer_instance

/-- A morphism of sheaves of modules is an isomorphism over an open `U` if and only if its
component at every open `V ≤ U` is an isomorphism. -/
public theorem isIso_over_iff_app {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (U : X.Opens) :
    IsIso (a.over U) ↔ ∀ V : X.Opens, V ≤ U → IsIso (a.app V) := by
  rw [← isIso_iff_of_reflects_iso (a.over U) (SheafOfModules.toSheaf _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h V hV ↦ h (op (Over.mk (homOfLE hV))), fun h V ↦ h V.unop.left (leOfHom V.unop.hom)⟩

/-- If `a` is an isomorphism over `U ⊓ W`, then `W.ι_* (a|_W)` becomes an isomorphism after
restriction to `U`. -/
public theorem isIso_restrict_pushforward_restrict_map {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (U W : X.Opens) [IsIso (a.over (U ⊓ W))] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pushforward W.ι).map a)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  show IsIso (a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ (U.ι ''ᵁ V))))
  apply (isIso_over_iff_app a (U ⊓ W)).mp inferInstance
  refine le_inf ?_ ?_
  · exact le_trans (W.ι.image_preimage_le _) (by simpa using U.ι.image_le_opensRange V)
  · simpa using W.ι.image_le_opensRange (W.ι ⁻¹ᵁ (U.ι ''ᵁ V))

/-- If `a` is an isomorphism over `U ⊓ W`, then the first projection `replaceOnOpen a W ⟶ G`
becomes an isomorphism after restriction to `U`. -/
public theorem isIso_restrict_replaceOnOpen_fst {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (U W : X.Opens) [IsIso (a.over (U ⊓ W))] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (pullback.fst ((Scheme.Modules.restrictAdjunction W.ι).unit.app G)
        ((Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pushforward W.ι).map a))) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have : PreservesLimits R := restrictFunctor_preservesLimits U.ι
  have := isIso_restrict_pushforward_restrict_map a U W
  exact (R.map_isPullback (IsPullback.of_hasPullback _ _)).isIso_fst_of_isIso

/-- A morphism of sheaves of modules that is an isomorphism over an open `V` is an isomorphism
over every open `U ≤ V`. -/
public theorem isIso_over_of_le {Y : Scheme.{u}} {F G : Y.Modules} (φ : F ⟶ G)
    {U V : Y.Opens} (hUV : U ≤ V) [IsIso (φ.over V)] : IsIso (φ.over U) :=
  (isIso_over_iff_app φ U).mpr fun A hA =>
    (isIso_over_iff_app φ V).mp ‹_› A (hA.trans hUV)

/-- There is an open `W` containing the overlap locus such that every prescribed section `s i`,
read as a morphism from the unit module to `L i`, is an isomorphism over `f i ⁻¹ᵁ W`. -/
public theorem exists_open_all_sections_trivial
    {ι : Type v} [Finite ι] (X : Scheme.{u}) (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (L : ∀ i, (Z i).Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (Z i).toRingedSpace) (L i) (s i)) :
    ∃ W : X.Opens, overlapLocus X Z f ⊆ W ∧
      ∀ i, IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W)) := by
  let V (i : ι) : (Z i).Opens :=
    Stacks.SheafOfModules.nonvanishingOpen (X := (Z i).toRingedSpace) (L i) (s i)
  let C : Set X := ⋃ i, f i '' (V i : Set (Z i))ᶜ
  have hC : IsClosed C := isClosed_iUnion_of_finite fun i =>
    (f i).isClosedEmbedding.isClosedMap _ (V i).isOpen.isClosed_compl
  let W : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  refine ⟨W, ?_, fun i => ?_⟩
  · intro x hx hxC
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hxC
    exact hz (nonvanishing_of_mem_overlap X Z f L s hs hx)
  · have hWV : f i ⁻¹ᵁ W ≤ V i := by
      intro z hz
      by_contra hzV
      exact hz (Set.mem_iUnion.mpr ⟨i, z, hzV, rfl⟩)
    have : IsIso (((L i).unitHomEquiv.symm (s i)).over (V i)) :=
      Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen (Z i) (L i) (s i)
    exact isIso_over_of_le _ hWV


/-- Pulling back along `f : Y ⟶ X` and then restricting to `f ⁻¹ᵁ U` is isomorphic to restricting
to `U` and then pulling back along `f ∣_ U`. -/
public noncomputable def pullbackRestrictIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f ∣_ U))

/-- If `a` becomes an isomorphism after restriction to `U`, then its pullback along `f` becomes an
isomorphism after restriction to `f ⁻¹ᵁ U`. -/
public theorem isIso_restrict_pullback_map {X Y : Scheme.{u}}
    (f : Y ⟶ X) (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map a)] :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullback f).map a)) := by
  let e := pullbackRestrictIso f U
  have he : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullback f).map a) = e.hom.app M ≫
        (Scheme.Modules.pullback (f ∣_ U)).map
          ((Scheme.Modules.restrictFunctor U.ι).map a) ≫ e.inv.app N := by
    have h := e.hom.naturality a
    dsimp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h, Category.assoc, e.hom_inv_id_app, Category.comp_id]
  rw [he]
  infer_instance

/-- For a morphism of schemes `f`, the preimage functor on opens is final. -/
public theorem opens_map_final {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  have : PreservesLimit (Functor.empty (X.Opens)) F := preservesTerminal_of_iso F
    (F.mapIso (terminalIsTerminal.uniqueUpToIso (isTerminalTop (α := X.Opens))) ≪≫
      eqToIso (show F.obj (⊤ : X.Opens) = ⊤ from rfl) ≪≫
      (isTerminalTop (α := Y.Opens)).uniqueUpToIso terminalIsTerminal)
  infer_instance

/-- **The pullback of the structure sheaf along a morphism of schemes is the structure sheaf**:
the comparison `f^* 𝒪_X ⟶ 𝒪_Y` is an isomorphism. -/
public instance isIso_pullbackUnit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      f.toRingCatSheafHom).homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (SheafOfModules.bijective_pushforwardSections f.toRingCatSheafHom M).comp
    (SheafOfModules.unitHomEquiv _).bijective
  ext g : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv f.toRingCatSheafHom g,
    EmbeddingLike.apply_eq_iff_eq, Adjunction.homEquiv_naturality_right]
  exact congrArg (· ≫ (SheafOfModules.pushforward f.toRingCatSheafHom).map g)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom)

/-- A morphism of sheaves of modules becomes an isomorphism after restriction to an open `U` if and
only if it is an isomorphism over `U`. -/
public theorem isIso_restrict_iff_over {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) ↔ IsIso (a.over U) := by
  rw [isIso_over_iff_app, Scheme.Modules.Hom.isIso_iff_isIso_app]
  constructor
  · intro h V hV
    have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
      ext x
      show x ∈ U.ι '' (U.ι ⁻¹' (V : Set X)) ↔ x ∈ V
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hV hx⟩, hx, rfl⟩
    have hi := h (U.ι ⁻¹ᵁ V)
    change IsIso (a.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) at hi
    exact Eq.mp (congrArg (fun V => IsIso (a.app V)) he) hi
  · intro h V
    exact h (U.ι ''ᵁ V) (by simpa using U.ι.image_le_opensRange V)

/-- The section `s` of `L`, read as a map out of the unit module after pushforward, is the
composite of `unitToPushforwardObjUnit` with the pushforward of `s` itself. -/
public theorem unitHomEquiv_symm_pushforwardSections {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : Y.Modules) (s : L.sections) :
    ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections f.toRingCatSheafHom s) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (L.unitHomEquiv.symm s) := by
  apply ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (SheafOfModules.pushforwardSections f.toRingCatSheafHom)
        (Equiv.apply_symm_apply _ s)).symm.trans
      (SheafOfModules.pushforwardSections_unitHomEquiv f.toRingCatSheafHom
        (L.unitHomEquiv.symm s)))

/-- If `a ≫ b` is the section of `f_* L` given by `s`, then the pullback of `a` followed by the
adjoint `f^* M ⟶ L` of `b` is the comparison `f^* 𝒪_X ⟶ 𝒪_Y` followed by the morphism `𝒪_Y ⟶ L`
given by `s`. -/
public theorem pullback_section_comp_adjoint {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (L : Y.Modules) (a : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (b : M ⟶ (Scheme.Modules.pushforward f).obj L) (s : L.sections)
    (h : a ≫ b = ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.symm
      (SheafOfModules.pushforwardSections f.toRingCatSheafHom s)) :
    (Scheme.Modules.pullback f).map a ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫ L.unitHomEquiv.symm s := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ L).injective
  have hL := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left a
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b)).trans
      (congrArg (a ≫ ·) (Equiv.apply_symm_apply _ b))
  have hR := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
        (L.unitHomEquiv.symm s)).trans
      (congrArg (· ≫ (Scheme.Modules.pushforward f).map (L.unitHomEquiv.symm s))
        (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
          f.toRingCatSheafHom))
  have hmid := unitHomEquiv_symm_pushforwardSections f L s
  exact hL.trans ((h.trans hmid).trans hR.symm)

/-- Let `a ≫ b` be the section of `f_* L` given by `s`. If `a` becomes an isomorphism after
restriction to `W` and `s` trivializes `L` over `f ⁻¹ᵁ W`, then the adjoint `f^* M ⟶ L` of `b`
becomes an isomorphism after restriction to `f ⁻¹ᵁ W`. -/
public theorem isIso_restrict_adjoint_of_section {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (L : Y.Modules) (a : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (b : M ⟶ (Scheme.Modules.pushforward f).obj L) (s : L.sections)
    (h : a ≫ b = ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.symm
      (SheafOfModules.pushforwardSections f.toRingCatSheafHom s)) (W : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor W.ι).map a)]
    [IsIso ((L.unitHomEquiv.symm s).over (f ⁻¹ᵁ W))] :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι).map
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b)) := by
  let R := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι
  let α := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b
  have hi := isIso_restrict_pullback_map f W a
  have hu : IsIso (R.map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)) :=
    @Functor.map_isIso _ _ _ _ _ _ R
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (isIso_pullbackUnit f)
  have hs : IsIso (R.map (L.unitHomEquiv.symm s)) :=
    (isIso_restrict_iff_over _ _).mpr inferInstance
  have he : R.map ((Scheme.Modules.pullback f).map a) ≫ R.map α =
      R.map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        R.map (L.unitHomEquiv.symm s) :=
    (R.map_comp _ _).symm.trans
      ((congrArg R.map (pullback_section_comp_adjoint f M L a b s h)).trans (R.map_comp _ _))
  have hcomp : IsIso (R.map ((Scheme.Modules.pullback f).map a) ≫ R.map α) :=
    Eq.mpr (congrArg IsIso he) (IsIso.comp_isIso' hu hs)
  exact IsIso.of_isIso_comp_left (R.map ((Scheme.Modules.pullback f).map a)) (R.map α)

/-- The product over `i` of the direct images `(f i)_* (L i)`. -/
public noncomputable abbrev closedCoverModule {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) : X.Modules :=
  ∏ᶜ fun i => (Scheme.Modules.pushforward (f i)).obj (L i)

/-- The morphism from the unit module to `closedCoverModule Z f L` whose `i`-th component is the
section of `(f i)_* (L i)` given by `s i`. -/
public noncomputable def closedCoverSection {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) :
    SheafOfModules.unit X.ringCatSheaf ⟶ closedCoverModule Z f L :=
  Pi.lift (f := fun i => (Scheme.Modules.pushforward (f i)).obj (L i))
    fun i => ((Scheme.Modules.pushforward (f i)).obj (L i)).unitHomEquiv.symm
      (SheafOfModules.pushforwardSections (f i).toRingCatSheafHom (s i))

/-- If `a ≫ b` is the section of `f_* L` given by `s`, then the adjoint `f^* M ⟶ L` of `b` carries
the image under the unit of the adjunction of the global section of `M` given by `a` to the global
section `s`. -/
public theorem adjoint_section_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (L : Y.Modules) (a : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (b : M ⟶ (Scheme.Modules.pushforward f).obj L) (s : L.sections)
    (h : a ≫ b = ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.symm
      (SheafOfModules.pushforwardSections f.toRingCatSheafHom s)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b).val.app
        (op ⊤) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
          (op ⊤) ((M.unitHomEquiv a).eval (op ⊤))) = s.eval (op ⊤) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let β := (adj.homEquiv M L).symm b
  have hb : adj.unit.app M ≫ (Scheme.Modules.pushforward f).map β = b :=
    (adj.homEquiv_unit M L β).symm.trans ((adj.homEquiv M L).apply_symm_apply b)
  have he : a ≫ adj.unit.app M ≫ (Scheme.Modules.pushforward f).map β =
      ((Scheme.Modules.pushforward f).obj L).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections f.toRingCatSheafHom s) :=
    (congrArg (a ≫ ·) hb).trans h
  have hv := congrArg
    (fun p : SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pushforward f).obj L =>
      (((Scheme.Modules.pushforward f).obj L).unitHomEquiv p).eval (op ⊤)) he
  exact hv.trans (congrArg
    (fun q : ((Scheme.Modules.pushforward f).obj L).sections => q.eval (op ⊤))
    (Equiv.apply_symm_apply _ _))

/-- The sheaf obtained by replacing the product of the direct images by the unit
sheaf on an open where the prescribed sections do not vanish. -/
public noncomputable abbrev patchedClosedCoverModule {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) : X.Modules :=
  replaceOnOpen (closedCoverSection Z f L s) W

/-- The prescribed sections give a section of the patched sheaf. -/
public noncomputable def patchedClosedCoverSection {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) :
    (patchedClosedCoverModule Z f L s W).sections :=
  (patchedClosedCoverModule Z f L s W).unitHomEquiv
    (replaceOnOpenLift (closedCoverSection Z f L s) W)

/-- The morphism `(f i)^* (patchedClosedCoverModule Z f L s W) ⟶ L i` adjoint to the first
projection of the patched module onto the product followed by the `i`-th projection. -/
public noncomputable def patchedClosedCoverComparison {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (patchedClosedCoverModule Z f L s W) ⟶ L i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (f i)).homEquiv _ _).symm
    (pullback.fst _ _ ≫ Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i)

/-- The patched section followed by the first projection and the `i`-th projection of the product
is the section of `(f i)_* (L i)` given by `s i`. -/
private theorem replaceOnOpenLift_comp_fst_pi_π {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    replaceOnOpenLift (closedCoverSection Z f L s) W ≫ (pullback.fst _ _ ≫
        Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i) =
      ((Scheme.Modules.pushforward (f i)).obj (L i)).unitHomEquiv.symm
        (SheafOfModules.pushforwardSections (f i).toRingCatSheafHom (s i)) :=
  ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i)
      (replaceOnOpenLift_fst (closedCoverSection Z f L s) W))).trans (Pi.lift_comp_π _ _)

/-- The component comparisons carry the patched section to the prescribed sections. -/
public theorem patchedClosedCoverComparison_section {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι) :
    (patchedClosedCoverComparison Z f L s W i).val.app (op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f i)).unit.app
        (patchedClosedCoverModule Z f L s W)).val.app (op ⊤)
          ((patchedClosedCoverSection Z f L s W).eval (op ⊤))) = (s i).eval (op ⊤) := by
  apply adjoint_section_eq
  exact replaceOnOpenLift_comp_fst_pi_π Z f L s W i

/-- The patched sheaf is trivial on the replacement open, with its patched section
as the chosen basis. -/
public noncomputable def patchedClosedCoverModule_restrictIsoUnit
    {ι : Type v} [Finite ι] [Small.{u} ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (s : ∀ i, (L i).sections) (W : X.Opens) :
    (patchedClosedCoverModule Z f L s W).restrict W.ι ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf := by
  have := isIso_restrict_replaceOnOpenLift (closedCoverSection Z f L s) W
  exact (asIso ((Scheme.Modules.restrictFunctor W.ι).map
    (replaceOnOpenLift (closedCoverSection Z f L s) W))).symm ≪≫
      Scheme.Modules.restrictUnitIso W.ι

/-- The comparison with each component is an isomorphism over the common
nonvanishing open. -/
public theorem patchedClosedCoverComparison_isIso_restrict
    {ι : Type v} [Finite ι] [Small.{u} ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (s : ∀ i, (L i).sections) (W : X.Opens) (i : ι)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ W).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
  have := isIso_restrict_replaceOnOpenLift (closedCoverSection Z f L s) W
  apply isIso_restrict_adjoint_of_section (f i) _ (L i)
    (replaceOnOpenLift (closedCoverSection Z f L s) W) _ (s i) _ W
  exact replaceOnOpenLift_comp_fst_pi_π Z f L s W i

/-- Isomorphisms of sheaves of modules can be checked in neighborhoods of points. -/
public theorem isIso_of_pointwise_restrict {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map a)) : IsIso a := by
  classical
  choose U hU ha using h
  have hc : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  have hi : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map a) := by
    apply Sheaf.isIso_of_coversTop hc
    intro x
    have : IsIso (a.over (U x)) := (isIso_restrict_iff_over _ _).mp (ha x)
    exact (SheafOfModules.toSheaf (X.ringCatSheaf.over (U x))).map_isIso (a.over (U x))
  apply (isIso_iff_of_reflects_iso a (Scheme.Modules.toPresheaf X)).mp
  exact (sheafToPresheaf _ _).map_isIso ((SheafOfModules.toSheaf X.ringCatSheaf).map a)

/-- A sheaf of modules locally isomorphic to the structure sheaf is invertible. -/
public theorem isInvertible_of_pointwise_restrictIsoUnit {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M := by
  classical
  choose U hU e using h
  let I : X → Type u := fun _ => PUnit.{u + 1}
  have efree (x : X) : Nonempty (M.restrict (U x).ι ≅ SheafOfModules.free (I x)) :=
    ⟨(e x).some ≪≫ (coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (U x).toScheme.ringCatSheaf)).symm⟩
  let q := localGeneratorsDataOfTrivializations M U hU I efree
  have hq := localGeneratorsDataOfTrivializations_isLocallyFreeData M U hU I efree
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology X)
      M 1 := @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
        (Opens X) _ (Opens.grothendieckTopology X) X.ringCatSheaf _ _ M 1
        ⟨q, hq, fun x => by
          show Nonempty (PUnit.{u + 1} ≃ Fin 1)
          exact ⟨Equiv.ofUnique _ _⟩⟩
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        M).1
    (Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
      (h := hflf) X.toRingedSpace M)

/-- A sheaf of modules whose module of sections over every open is a subsingleton is zero. -/
public theorem module_isZero_of_sections_subsingleton {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.Opens, Subsingleton Γ(M, U)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact (h U).elim _ _

/-- If `f ⁻¹ᵁ U = ⊥`, then the restriction of `f_* L` to `U` is zero. -/
public theorem restrict_pushforward_isZero_of_preimage_eq_bot {X Y : Scheme.{u}}
    (f : Y ⟶ X) (U : X.Opens) (hU : f ⁻¹ᵁ U = ⊥) (L : Y.Modules) :
    IsZero (((Scheme.Modules.pushforward f).obj L).restrict U.ι) := by
  apply module_isZero_of_sections_subsingleton
  intro V
  have hpre : f ⁻¹ᵁ (U.ι ''ᵁ V) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hU]
    exact Scheme.Hom.preimage_mono f (by simpa using U.ι.image_le_opensRange V)
  rw [Scheme.Modules.restrict_obj, Scheme.Modules.pushforward_obj_obj, hpre]
  exact subsingleton_module_of_subsingleton_ring
    (R := Γ(Y, (⊥ : Y.Opens)))

/-- If `R` preserves the product of the family `A` and sends every `A j` with `j ≠ i` to a zero
object, then `R` sends the projection `∏ᶜ A ⟶ A i` to an isomorphism. -/
public theorem isIso_map_pi_of_isZero {C : Type*} {D : Type*}
    [Category C] [Category D] [HasZeroMorphisms D]
    {κ : Type*} (A : κ → C) [HasProduct A] (R : C ⥤ D)
    [PreservesLimit (Discrete.functor A) R] (i : κ)
    (h : ∀ j, j ≠ i → IsZero (R.obj (A j))) : IsIso (R.map (Pi.π A i)) := by
  classical
  let c := R.mapCone (limit.cone (Discrete.functor A))
  let hc : IsLimit c := isLimitOfPreserves R (limit.isLimit (Discrete.functor A))
  let q : ∀ j, R.obj (A i) ⟶ R.obj (A j) :=
    fun j => if e : i = j then eqToHom (congrArg (fun k => R.obj (A k)) e) else 0
  let d : Cone (Discrete.functor A ⋙ R) :=
    ⟨R.obj (A i), Discrete.natTrans fun j => q j.as⟩
  refine ⟨⟨hc.lift d, ?_, ?_⟩⟩
  · apply hc.hom_ext
    intro j
    rw [Category.assoc, hc.fac]
    by_cases e : j.as = i
    · cases j
      dsimp at e
      subst e
      simp [d, q, c]
    · exact (h j.as e).eq_of_tgt _ _
  · have he := hc.fac d ⟨i⟩
    simpa [c, d, q] using he

/-- For two left adjoints `F` and `F'` of the same functor `G`, the adjoint of a morphism
`M ⟶ G.obj N` for one adjunction is an isomorphism if and only if its adjoint for the other is. -/
public theorem adjoint_isIso_iff {C : Type*} {D : Type*}
    [Category C] [Category D] {F F' : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G) {M : C} {N : D} (f : M ⟶ G.obj N) :
    IsIso ((a.homEquiv M N).symm f) ↔ IsIso ((b.homEquiv M N).symm f) := by
  have he : (a.homEquiv M N).symm f =
      (a.leftAdjointUniq b).hom.app M ≫ (b.homEquiv M N).symm f := by
    apply (a.homEquiv M N).injective
    rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← b.homEquiv_unit,
      Equiv.apply_symm_apply]
  rw [he]
  exact isIso_comp_left_iff _ _

/-- Let `f : Y ⟶ X` be injective and `g : T ⟶ Y` an open immersion with `g ≫ f` an open immersion.
If `b : M ⟶ f_* L` becomes an isomorphism after restriction along `g ≫ f`, then its adjoint
`f^* M ⟶ L` becomes an isomorphism after restriction along `g`. -/
public theorem isIso_restrict_adjoint_of_open_comp {X Y T : Scheme.{u}}
    (f : Y ⟶ X) (g : T ⟶ Y) [IsOpenImmersion g] [IsOpenImmersion (g ≫ f)]
    (hf : Function.Injective f)
    (M : X.Modules) (L : Y.Modules) (b : M ⟶ (Scheme.Modules.pushforward f).obj L)
    [IsIso ((Scheme.Modules.restrictFunctor (g ≫ f)).map b)] :
    IsIso ((Scheme.Modules.restrictFunctor g).map
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M L).symm b)) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let d := Scheme.Modules.restrictAdjunction g
  let c := Scheme.Modules.restrictAdjunction (g ≫ f)
  let e := Scheme.Modules.pushforwardComp g f
  let β := ((a.homEquiv M L).symm b)
  let q := b ≫ (Scheme.Modules.pushforward f).map (d.unit.app L)
  have hq : ((a.comp d).homEquiv M ((Scheme.Modules.restrictFunctor g).obj L)).symm q =
      (Scheme.Modules.restrictFunctor g).map β := by
    dsimp only [q]
    rw [Adjunction.comp_homEquiv]
    show (d.homEquiv _ _).symm ((a.homEquiv _ _).symm
      (b ≫ (Scheme.Modules.pushforward f).map (d.unit.app L))) = _
    rw [a.homEquiv_naturality_right_symm, d.homEquiv_naturality_left_symm]
    simp [β]
  rw [← hq]
  apply (adjoint_isIso_iff (a.comp d) (c.ofNatIsoRight e.symm) q).mpr
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  rw [c.homEquiv_counit]
  have hunit : IsIso ((Scheme.Modules.restrictFunctor (g ≫ f)).map
      ((Scheme.Modules.pushforward f).map (d.unit.app L))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro V
    show IsIso (L.presheaf.map (homOfLE
      (g.image_preimage_le (f ⁻¹ᵁ ((g ≫ f) ''ᵁ V)))).op)
    have he : g ''ᵁ (g ⁻¹ᵁ (f ⁻¹ᵁ ((g ≫ f) ''ᵁ V))) = f ⁻¹ᵁ ((g ≫ f) ''ᵁ V) := by
      ext y
      constructor
      · exact fun hy => g.image_preimage_le _ hy
      · intro hy
        obtain ⟨t, ht, he⟩ := hy
        exact ⟨t, ⟨t, ht, rfl⟩, hf he⟩
    have : IsIso (homOfLE (g.image_preimage_le (f ⁻¹ᵁ ((g ≫ f) ''ᵁ V)))) :=
      (eqToIso he).isIso_hom
    infer_instance
  dsimp only [q]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- A morphism that is an isomorphism over an open `U` becomes an isomorphism after restriction
along any open immersion whose image lies in `U`. -/
public theorem isIso_restrict_of_image_le {X Y : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens)
    (h : Set.range f ⊆ U) [IsIso (a.over U)] :
    IsIso ((Scheme.Modules.restrictFunctor f).map a) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  apply (isIso_over_iff_app a U).mp inferInstance
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h ⟨y, rfl⟩

/-- If `f ∣_ U` is an isomorphism, then the comparison `𝒪_X ⟶ f_* 𝒪_Y` becomes an isomorphism after
restriction to `U`. -/
public theorem isIso_restrict_unitToPushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have h0 : IsIso ((f ∣_ U).app V) := inferInstance
  have hfapp : IsIso (f.app (U.ι ''ᵁ V)) :=
    IsIso.of_isIso_fac_right
      (f := Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)
      (hh := h0) (morphismRestrict_app f U V).symm
  exact @Functor.map_isIso _ _ _ _ _ _
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab) (f.app (U.ι ''ᵁ V)) hfapp

/-- If no member of the cover other than the `i`-th meets `U`, then the projection from the product
of the direct images to the `i`-th one becomes an isomorphism after restriction to `U`. -/
private theorem isIso_restrict_pi_π_of_preimage_eq_bot {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (L : ∀ i, (Z i).Modules)
    (i : ι) (U : X.Opens) (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (Pi.π (fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) i)) := by
  have : PreservesLimits (Scheme.Modules.restrictFunctor U.ι) :=
    restrictFunctor_preservesLimits U.ι
  exact isIso_map_pi_of_isZero _ _ i fun j hj =>
    restrict_pushforward_isZero_of_preimage_eq_bot (f j) U (hzero j hj) (L j)

/-- If `f i ∣_ U` is an isomorphism, no other member of the cover meets `U`, and `s i` trivializes
`L i` over `f i ⁻¹ᵁ W`, then `closedCoverSection Z f L s` is an isomorphism over `U ⊓ W`. -/
public theorem isIso_closedCoverSection_over {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections)
    (i : ι) (U W : X.Opens) [IsIso (f i ∣_ U)]
    (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((closedCoverSection Z f L s).over (U ⊓ W)) := by
  let A := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)
  let R := Scheme.Modules.restrictFunctor U.ι
  have hp := isIso_restrict_pi_π_of_preimage_eq_bot Z f L i U hzero
  have hover {M N : X.Modules} (a : M ⟶ N) (h : IsIso (R.map a)) : IsIso (a.over (U ⊓ W)) := by
    have := (isIso_restrict_iff_over _ _).mp h
    exact isIso_over_of_le _ inf_le_left
  have hp' := hover _ hp
  have hu' := hover _ (isIso_restrict_unitToPushforward (f i) U)
  have hs' : IsIso (((Scheme.Modules.pushforward (f i)).map
      ((L i).unitHomEquiv.symm (s i))).over (U ⊓ W)) := by
    apply (isIso_over_iff_app _ _).mpr
    intro V hV
    apply (isIso_over_iff_app ((L i).unitHomEquiv.symm (s i)) (f i ⁻¹ᵁ W)).mp
      inferInstance
    exact Scheme.Hom.preimage_mono _ (hV.trans inf_le_right)
  have he : closedCoverSection Z f L s ≫ Pi.π A i =
      SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (f i)).map ((L i).unitHomEquiv.symm (s i)) :=
    (Pi.lift_comp_π (f := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)) _ i).trans
      (unitHomEquiv_symm_pushforwardSections (f i) (L i) (s i))
  have he' := congrArg (fun a => a.over (U ⊓ W)) he
  change (closedCoverSection Z f L s).over (U ⊓ W) ≫ (Pi.π A i).over (U ⊓ W) =
    (SheafOfModules.unitToPushforwardObjUnit (f i).toRingCatSheafHom).over (U ⊓ W) ≫
      ((Scheme.Modules.pushforward (f i)).map
        ((L i).unitHomEquiv.symm (s i))).over (U ⊓ W) at he'
  have hi : IsIso ((closedCoverSection Z f L s).over (U ⊓ W) ≫
      (Pi.π A i).over (U ⊓ W)) :=
    Eq.mpr (congrArg IsIso he') (IsIso.comp_isIso' hu' hs')
  exact (isIso_comp_right_iff _ _).mp hi

/-- If `f ∣_ U` is an isomorphism, then `(f ⁻¹ᵁ U).ι ≫ f` is an open immersion. -/
private theorem isOpenImmersion_restrict_ι_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  infer_instance

/-- If `f i ∣_ U` is an isomorphism, no other member of the cover meets `U`, and `s i` trivializes
`L i` over `f i ⁻¹ᵁ W`, then `patchedClosedCoverComparison Z f L s W i` becomes an isomorphism
after restriction to `f i ⁻¹ᵁ U`. -/
public theorem patchedClosedCoverComparison_isIso_of_single_component
    {ι : Type v} [Finite ι] [Small.{u} ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections) (W U : X.Opens) (i : ι)
    [IsIso (f i ∣_ U)] (hzero : ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥)
    [IsIso (((L i).unitHomEquiv.symm (s i)).over (f i ⁻¹ᵁ W))] :
    IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ U).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
  let A := fun j => (Scheme.Modules.pushforward (f j)).obj (L j)
  let R := Scheme.Modules.restrictFunctor U.ι
  have hp := isIso_restrict_pi_π_of_preimage_eq_bot Z f L i U hzero
  have ha := isIso_closedCoverSection_over Z f L s i U W hzero
  have hf := isIso_restrict_replaceOnOpen_fst (closedCoverSection Z f L s) U W
  let b : patchedClosedCoverModule Z f L s W ⟶ (Scheme.Modules.pushforward (f i)).obj (L i) :=
    pullback.fst _ _ ≫ Pi.π A i
  have hb : IsIso (R.map b) := by dsimp only [b]; rw [Functor.map_comp]; infer_instance
  have hb' : IsIso (b.over U) := (isIso_restrict_iff_over _ _).mp hb
  let g := (f i ⁻¹ᵁ U).ι
  have := isOpenImmersion_restrict_ι_comp (f i) U
  have : IsIso ((Scheme.Modules.restrictFunctor (g ≫ f i)).map b) := by
    apply isIso_restrict_of_image_le b _ U
    rintro x ⟨y, rfl⟩
    exact y.2
  exact isIso_restrict_adjoint_of_open_comp (f i) g
    (f i).isClosedEmbedding.injective _ (L i) b

/-- If the restriction of `M` along an open immersion `k : T ⟶ X` is isomorphic to the restriction
of an invertible module `L` along an open immersion `g : T ⟶ Y`, then `M` is trivial on an open
neighbourhood of `k z`, for every `z : T`. -/
public theorem exists_trivialization_of_local_comparison {X Y T : Scheme.{u}}
    (k : T ⟶ X) (g : T ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion g]
    (M : X.Modules) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (e : M.restrict k ≅ L.restrict g) (z : T) :
    ∃ U : X.Opens, k z ∈ U ∧ Nonempty
      (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨V₀, hz, ⟨e₀⟩⟩ := exists_open_trivialization_of_invertible Y L (g z)
  let V := g ⁻¹ᵁ V₀
  let h := g ∣_ V₀
  let eL : L.restrict V₀.ι ≅ SheafOfModules.unit V₀.toScheme.ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv V₀).app L).symm ≪≫
      (Scheme.Modules.overEquiv V₀).functor.mapIso e₀
  let eS : (L.restrict g).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorComp V.ι g).app L).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι g V₀).symm).app L ≪≫
      (Scheme.Modules.restrictFunctorComp h V₀.ι).app L ≪≫
      (Scheme.Modules.restrictFunctor h).mapIso eL ≪≫ Scheme.Modules.restrictUnitIso h
  let l := V.ι ≫ k
  let el : M.restrict l ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorComp V.ι k).app M ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso e ≪≫ eS
  let U := l.opensRange
  let eU : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorCongr l.isoOpensRange_inv_comp).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp l.isoOpensRange.inv l).app M ≪≫
      (Scheme.Modules.restrictFunctor l.isoOpensRange.inv).mapIso el ≪≫
      Scheme.Modules.restrictUnitIso l.isoOpensRange.inv
  exact ⟨U, ⟨⟨z, hz⟩, rfl⟩, ⟨eU⟩⟩

/-- Sections nonvanishing along the pairwise intersections can be glued along
with the invertible sheaves. -/
@[stacks 09NE "existence with prescribed sections"]
public theorem exists_invertible_with_sections_of_closed_cover_discrete_intersections
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X]
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    (L : ∀ i, (Z i).Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (Z i).toRingedSpace) (L i) (s i)) :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
      (t : M.sections),
      ∀ i, ∃ e : (modulePullback (f i).toLRSHom.toShHom).obj M ≅ L i,
        e.hom.val.app (op ⊤)
          (((modulePullbackPushforwardAdjunction (f i).toLRSHom.toShHom).unit.app M).val.app
            (op ⊤) (t.eval (op ⊤))) = (s i).eval (op ⊤) := by
  classical
  have : Small.{u} ι := inferInstance
  obtain ⟨W, hW, htrivial⟩ := exists_open_all_sections_trivial X Z f L s hs
  let M := patchedClosedCoverModule Z f L s W
  let t := patchedClosedCoverSection Z f L s W
  have hWiso (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (f i ⁻¹ᵁ W).ι).map
      (patchedClosedCoverComparison Z f L s W i)) := by
    have := htrivial i
    exact patchedClosedCoverComparison_isIso_restrict Z f L s W i
  have hcomparison (i : ι) : IsIso (patchedClosedCoverComparison Z f L s W i) := by
    apply isIso_of_pointwise_restrict
    intro z
    by_cases hz : f i z ∈ W
    · exact ⟨f i ⁻¹ᵁ W, hz, hWiso i⟩
    · obtain ⟨j, U, hxU, hj, hzero⟩ :=
        exists_open_neighborhood_isIso_component_of_not_overlap X Z f hcover
          (fun h => hz (hW h))
      have he : i = j := by
        by_contra hij
        have hzi : z ∈ f i ⁻¹ᵁ U := hxU
        rw [hzero i hij] at hzi
        exact hzi
      subst j
      have := htrivial i
      exact ⟨f i ⁻¹ᵁ U, hxU,
        patchedClosedCoverComparison_isIso_of_single_component Z f L s W U i hzero⟩
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M := by
    apply isInvertible_of_pointwise_restrictIsoUnit
    intro x
    by_cases hx : x ∈ W
    · exact ⟨W, hx, ⟨patchedClosedCoverModule_restrictIsoUnit Z f L s W⟩⟩
    · obtain ⟨i, U, hxU, hi, hzero⟩ :=
        exists_open_neighborhood_isIso_component_of_not_overlap X Z f hcover
          (fun h => hx (hW h))
      let g := (f i ⁻¹ᵁ U).ι
      let k := g ≫ f i
      have : IsOpenImmersion k := isOpenImmersion_restrict_ι_comp (f i) U
      let e : M.restrict k ≅ (L i).restrict g :=
        (Scheme.Modules.restrictFunctorIsoPullback k).app M ≪≫
          ((Scheme.Modules.pullbackComp g (f i)).app M).symm ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback g).app
            ((Scheme.Modules.pullback (f i)).obj M)).symm ≪≫
          (Scheme.Modules.restrictFunctor g).mapIso
            (asIso (patchedClosedCoverComparison Z f L s W i))
      obtain ⟨z, hz⟩ := (f i ∣_ U).surjective ⟨x, hxU⟩
      have hkz : k z = x :=
        (morphismRestrict_base_coe (f i) U z).symm.trans (congrArg U.ι hz)
      simpa only [hkz] using exists_trivialization_of_local_comparison k g M (L i) e z
  exact ⟨M, hM, t, fun i =>
    ⟨@asIso _ _ _ _ _ (hcomparison i),
      patchedClosedCoverComparison_section Z f L s W i⟩⟩
end StacksTag09NE

end
