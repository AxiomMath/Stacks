module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct image along a finite morphism on dimension layers of coherent modules

Let `(S, δ)` be a base situation with a dimension function and let `π : X ⟶ Y` be a finite
morphism of schemes locally of finite type over `S`. Direct image along `π` is an exact functor
`Coh(X) ⟶ Coh(Y)`, it does not raise the delta-dimension of the support, so it restricts to the
subcategories `Coh_{≤k}` cut out by that bound, and it therefore induces homomorphisms on the
Grothendieck groups of those categories and of the dimension layers `Coh_{≤k}/Coh_{≤k-1}`. The
cycle class homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)` commutes with these maps and
with proper pushforward of cycles.

## Main definitions

* `Stacks.Chow.finitePushforwardCoherent` — the functor `π_* : Coh(X) ⥤ Coh(Y)`.
* `Stacks.Chow.finitePushforwardDimLE` — its restriction `Coh_{≤k}(X) ⥤ Coh_{≤k}(Y)`.
* `Stacks.Chow.finitePushforwardCoherentHom` and `Stacks.Chow.finitePushforwardDimLEHom` — the
  induced homomorphisms `K₀(Coh(X)) → K₀(Coh(Y))` and `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(Y))`.
* `Stacks.Chow.dimensionLayerFinitePushforwardHom` — the induced homomorphism
  `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))`.

## Main results

* `Stacks.Chow.shortExact_map_finitePushforwardCoherent` and
  `Stacks.Chow.shortExact_map_finitePushforwardDimLE` — exactness of the two functors.
* `Stacks.Chow.coherentModulesDimLE_finitePushforward` — the direct image of a coherent module
  whose support has delta-dimension at most `k` again has support of delta-dimension at most `k`.
* `Stacks.Chow.dimensionLayerFinitePushforwardHom_of` — the homomorphism on the Grothendieck
  group of a layer sends the class of a module to the class of its direct image.
* `Stacks.Chow.properPushforwardHom_comp_dimensionLayerCycleHom` — the square formed by the cycle
  class homomorphisms for `X` and for `Y`, the homomorphism on the Grothendieck groups of the
  layers, and proper pushforward of `k`-cycles, commutes.
* `Stacks.Chow.dimensionLayerFinitePushforwardHom_comp_cycleDimensionLayerHom` and
  `Stacks.Chow.dimensionLayerFinitePushforwardHom_cycleDimensionLayerHom` — the same square read
  with the arrows `Z_k ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` in place of the cycle class homomorphisms
  commutes as well, for `Y` Noetherian.

## References

* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 02MV](https://stacks.math.columbia.edu/tag/02MV)
* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-! ### Direct image along a finite morphism on coherent modules -/

section Coherent

variable (π : X ⟶ Y) [IsFinite π] [IsLocallyNoetherian Y]

/-- Direct image along a finite morphism to a locally Noetherian scheme, as a functor on coherent
modules. -/
@[stacks 0FDR "the functor `π_* : Coh(X) ⥤ Coh(Y)`"]
def finitePushforwardCoherent :
    Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  ObjectProperty.lift _
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward π)
    fun F ↦
      have : _root_.SheafOfModules.IsCoherent F.obj :=
        AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
          π F.obj)

/-- The underlying module of the direct image of a coherent module is its direct image. -/
theorem finitePushforwardCoherent_obj_obj
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((finitePushforwardCoherent π).obj F).obj = (Scheme.Modules.pushforward π).obj F.obj :=
  rfl

/-- Direct image along a finite morphism is left exact on coherent modules. -/
instance preservesFiniteLimits_finitePushforwardCoherent :
    PreservesFiniteLimits (finitePushforwardCoherent π) := by
  have hι : PreservesFiniteLimits (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι :=
    inferInstance
  have hpush : PreservesFiniteLimits (Scheme.Modules.pushforward π) := inferInstance
  have : PreservesFiniteLimits (finitePushforwardCoherent π ⋙
      (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι (Scheme.Modules.pushforward π)
      hι hpush
  have : (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms (ObjectProperty.fullyFaithfulι _)
  exact preservesFiniteLimits_of_reflects_of_preserves (finitePushforwardCoherent π)
    (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι

/-- Direct image along a finite morphism carries an epimorphism of coherent modules to an
epimorphism. -/
instance preservesEpimorphisms_finitePushforwardCoherent :
    (finitePushforwardCoherent π).PreservesEpimorphisms where
  preserves {A B} q hq := by
    have _hA : _root_.SheafOfModules.IsCoherent
        ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj A) :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent A.property
    have _hB : _root_.SheafOfModules.IsCoherent
        ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj B) :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent B.property
    have hqA : ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj A).IsQuasicoherent :=
      isQuasicoherent_of_isCoherent _
    have hqB : ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.obj B).IsQuasicoherent :=
      isQuasicoherent_of_isCoherent _
    have hι : (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.PreservesEpimorphisms :=
      ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _
    have hpush : Epi ((Scheme.Modules.pushforward π).map
        ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.map q)) :=
      @epi_pushforward_map_of_isAffineHom _ _ π _ _ _ hqA hqB
        ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι.map q) (hι.preserves q)
    have hrefl : (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι.ReflectsEpimorphisms :=
      Functor.reflectsEpimorphisms_of_faithful _
    exact (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf).ι.epi_of_epi_map
      (f := (finitePushforwardCoherent π).map q) hpush

/-- Direct image along a finite morphism is additive on coherent modules. -/
instance additive_finitePushforwardCoherent : (finitePushforwardCoherent π).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Direct image along a finite morphism is right exact on coherent modules. -/
instance preservesFiniteColimits_finitePushforwardCoherent :
    PreservesFiniteColimits (finitePushforwardCoherent π) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (finitePushforwardCoherent π)).2 fun S hS ↦
      ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
          (finitePushforwardCoherent π)).1 inferInstance S hS).1,
        have := hS.epi_g
        inferInstance⟩

/-- Direct image along a finite morphism carries a short exact sequence of coherent modules to a
short exact sequence. -/
@[stacks 0FDR "`π_*` is an exact functor on coherent sheaves"]
theorem shortExact_map_finitePushforwardCoherent
    ⦃S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)⦄
    (hS : S.ShortExact) : (S.map (finitePushforwardCoherent π)).ShortExact :=
  hS.map_of_exact (finitePushforwardCoherent π)

/-- The homomorphism `K₀(Coh(X)) → K₀(Coh(Y))` induced by direct image along a finite
morphism. -/
@[stacks 0FDR "the induced homomorphism `K₀(Coh(X)) → K₀(Coh(Y))`"]
def finitePushforwardCoherentHom :
    GrothendieckGroup (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) →+
      GrothendieckGroup (Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf) :=
  GrothendieckGroup.map (finitePushforwardCoherent π)
    (shortExact_map_finitePushforwardCoherent π)

/-- The homomorphism on Grothendieck groups sends the class of a coherent module to the class of
its direct image. -/
theorem finitePushforwardCoherentHom_of
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    finitePushforwardCoherentHom π (GrothendieckGroup.of F) =
      GrothendieckGroup.of ((finitePushforwardCoherent π).obj F) :=
  GrothendieckGroup.map_of _ _ F

end Coherent

/-! ### Direct image on the subcategories of bounded support dimension -/

/-- The direct image along a finite morphism of a coherent module whose support has
delta-dimension at most `k` again has support of delta-dimension at most `k`. -/
@[stacks 0FDR "`π_*` sends `Coh_{≤k}(X)` into `Coh_{≤k}(Y)`"]
theorem coherentModulesDimLE_finitePushforward (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : coherentModulesDimLE C sX k F) :
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    coherentModulesDimLE C sY k ((finitePushforwardCoherent π).obj F) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hc : _root_.SheafOfModules.IsCoherent F.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  have hp : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward π).obj F.obj) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite π F.obj
  exact schemeDeltaDimension_reducedSupport_pushforward_le C sX sY π hπ F.obj hF

/-- The restriction of `π_*` to the coherent modules whose support has delta-dimension at most
`k`. -/
@[stacks 0FDR "the functor `π_* : Coh_{≤k}(X) ⥤ Coh_{≤k}(Y)`"]
def finitePushforwardDimLE (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π] (hπ : π ≫ sY = sX)
    (k : ℤ) : CoherentModulesDimLE C sX k ⥤ CoherentModulesDimLE C sY k :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  ObjectProperty.lift _ ((coherentModulesDimLE C sX k).ι ⋙ finitePushforwardCoherent π)
    fun F ↦ coherentModulesDimLE_finitePushforward C sX sY π hπ k F.obj F.property

/-- The underlying module of the direct image of a module of bounded support dimension is its
direct image. -/
theorem finitePushforwardDimLE_obj_obj_obj (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) (F : CoherentModulesDimLE C sX k) :
    ((finitePushforwardDimLE C sX sY π hπ k).obj F).obj.obj =
      (Scheme.Modules.pushforward π).obj F.obj.obj :=
  rfl

/-- Direct image along a finite morphism is left exact on the coherent modules of support
dimension at most `k`. -/
instance preservesFiniteLimits_finitePushforwardDimLE (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    PreservesFiniteLimits (finitePushforwardDimLE C sX sY π hπ k) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : PreservesFiniteLimits (finitePushforwardDimLE C sX sY π hπ k ⋙
      (coherentModulesDimLE C sY k).ι) :=
    comp_preservesFiniteLimits (coherentModulesDimLE C sX k).ι (finitePushforwardCoherent π)
  have : (coherentModulesDimLE C sY k).ι.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms (ObjectProperty.fullyFaithfulι _)
  exact preservesFiniteLimits_of_reflects_of_preserves (finitePushforwardDimLE C sX sY π hπ k)
    (coherentModulesDimLE C sY k).ι

/-- Direct image along a finite morphism is right exact on the coherent modules of support
dimension at most `k`. -/
instance preservesFiniteColimits_finitePushforwardDimLE (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    PreservesFiniteColimits (finitePushforwardDimLE C sX sY π hπ k) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : PreservesFiniteColimits (finitePushforwardDimLE C sX sY π hπ k ⋙
      (coherentModulesDimLE C sY k).ι) :=
    comp_preservesFiniteColimits (coherentModulesDimLE C sX k).ι (finitePushforwardCoherent π)
  have : (coherentModulesDimLE C sY k).ι.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms (ObjectProperty.fullyFaithfulι _)
  exact preservesFiniteColimits_of_reflects_of_preserves (finitePushforwardDimLE C sX sY π hπ k)
    (coherentModulesDimLE C sY k).ι

/-- Direct image along a finite morphism carries a short exact sequence of coherent modules of
support dimension at most `k` to a short exact sequence. -/
@[stacks 0FDR "`π_*` is exact on `Coh_{≤k}`"]
theorem shortExact_map_finitePushforwardDimLE (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) ⦃S : ShortComplex (CoherentModulesDimLE C sX k)⦄
    (hS : S.ShortExact) : (S.map (finitePushforwardDimLE C sX sY π hπ k)).ShortExact :=
  hS.map_of_exact (finitePushforwardDimLE C sX sY π hπ k)

/-- The homomorphism `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(Y))` induced by direct image along a finite
morphism. -/
@[stacks 0FDR "the induced homomorphism `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(Y))`"]
def finitePushforwardDimLEHom (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π] (hπ : π ≫ sY = sX)
    (k : ℤ) :
    GrothendieckGroup (CoherentModulesDimLE C sX k) →+
      GrothendieckGroup (CoherentModulesDimLE C sY k) :=
  GrothendieckGroup.map (finitePushforwardDimLE C sX sY π hπ k)
    (shortExact_map_finitePushforwardDimLE C sX sY π hπ k)

/-- The homomorphism on Grothendieck groups sends the class of a module of support dimension at
most `k` to the class of its direct image. -/
theorem finitePushforwardDimLEHom_of (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) (F : CoherentModulesDimLE C sX k) :
    finitePushforwardDimLEHom C sX sY π hπ k (GrothendieckGroup.of F) =
      GrothendieckGroup.of ((finitePushforwardDimLE C sX sY π hπ k).obj F) :=
  GrothendieckGroup.map_of _ _ F

/-! ### The induced homomorphism on the Grothendieck group of a dimension layer -/

/-- The composite `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(Y)) → K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))`. -/
def dimensionLayerFinitePushforwardAux (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    GrothendieckGroup (CoherentModulesDimLE C sX k) →+
      GrothendieckGroup (coherentDimensionQuotient C sY (k - 1) k) :=
  (GrothendieckGroup.map (lowerDimensionClass C sY (k - 1) k).isoModSerre.Q
        (shortExact_map_q_lowerDimensionClass C sY k)).comp
    (finitePushforwardDimLEHom C sX sY π hπ k)

/-- The composite `K₀(Coh_{≤k}(X)) → K₀(Coh_{≤k}(Y)) → K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))` kills the
image of `K₀(Coh_{≤k-1}(X))`. -/
theorem dimensionLayerFinitePushforwardAux_comp_map_ι (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    (dimensionLayerFinitePushforwardAux C sX sY π hπ k).comp
        (GrothendieckGroup.map (lowerDimensionClass C sX (k - 1) k).ι
          (shortExact_map_ι_lowerDimensionClass C sX k)) = 0 := by
  refine GrothendieckGroup.hom_ext fun G ↦ ?_
  rw [AddMonoidHom.comp_apply, GrothendieckGroup.map_of, ObjectProperty.ι_obj,
    dimensionLayerFinitePushforwardAux, AddMonoidHom.comp_apply, finitePushforwardDimLEHom_of,
    GrothendieckGroup.map_of, AddMonoidHom.zero_apply]
  exact GrothendieckGroup.of_eq_zero_of_isZero
    ((ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (lowerDimensionClass C sY (k - 1) k).isoModSerre.Q (lowerDimensionClass C sY (k - 1) k) _).2
      (coherentModulesDimLE_finitePushforward C sX sY π hπ (k - 1) G.obj.obj G.property))

/-- The homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))` induced by
direct image along a finite morphism. -/
@[stacks 0FDR
  "the induced homomorphism `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))`"]
def dimensionLayerFinitePushforwardHom (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    GrothendieckGroup (coherentDimensionQuotient C sX (k - 1) k) →+
      GrothendieckGroup (coherentDimensionQuotient C sY (k - 1) k) :=
  (QuotientAddGroup.lift _ (dimensionLayerFinitePushforwardAux C sX sY π hπ k)
        ((AddMonoidHom.range_le_ker_iff _ _).2
          (dimensionLayerFinitePushforwardAux_comp_map_ι C sX sY π hπ k))).comp
    (dimensionLayerGrothendieckGroupEquiv C sX k).symm.toAddMonoidHom

/-- The homomorphism on the Grothendieck groups of the layers sends the class of the image of a
module `F` of `Coh_{≤k}(X)` to the class of the image of `π_* F`. -/
@[stacks 0FDR "the induced homomorphism on a layer sends `[F]` to `[π_* F]`"]
theorem dimensionLayerFinitePushforwardHom_of (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) (F : CoherentModulesDimLE C sX k) :
    dimensionLayerFinitePushforwardHom C sX sY π hπ k
        (GrothendieckGroup.of ((lowerDimensionClass C sX (k - 1) k).isoModSerre.Q.obj F)) =
      GrothendieckGroup.of ((lowerDimensionClass C sY (k - 1) k).isoModSerre.Q.obj
        ((finitePushforwardDimLE C sX sY π hπ k).obj F)) := by
  have h : (dimensionLayerGrothendieckGroupEquiv C sX k).symm
      (GrothendieckGroup.of ((lowerDimensionClass C sX (k - 1) k).isoModSerre.Q.obj F)) =
      QuotientAddGroup.mk (GrothendieckGroup.of F) :=
    ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv_symm_of_obj _ _ _ _ F
  rw [dimensionLayerFinitePushforwardHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    h, QuotientAddGroup.lift_mk, dimensionLayerFinitePushforwardAux, AddMonoidHom.comp_apply,
    finitePushforwardDimLEHom_of, GrothendieckGroup.map_of]

/-! ### Commutativity with the cycle class homomorphism -/

/-- The cycle class homomorphism `K₀(Coh_{≤k}/Coh_{≤k-1}) ⟶ Z_k` commutes with direct image
along a finite morphism on the source and proper pushforward of `k`-cycles on the target. -/
@[stacks 0FDR "commutativity of the right-hand square of the diagram"]
theorem properPushforwardHom_comp_dimensionLayerCycleHom (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π]
    (hπ : π ≫ sY = sX) (k : ℤ) :
    (properPushforwardHom C sX sY π hπ k).comp (dimensionLayerCycleHom C sX k) =
      (dimensionLayerCycleHom C sY k).comp
        (dimensionLayerFinitePushforwardHom C sX sY π hπ k) := by
  have hLN : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine (AddMonoidHom.cancel_right
    (ObjectProperty.SerreClassLocalization.grothendieckGroup_map_surjective
      (lowerDimensionClass C sX (k - 1) k).isoModSerre.Q (lowerDimensionClass C sX (k - 1) k)
      (shortExact_map_q_lowerDimensionClass C sX k))).1 (GrothendieckGroup.hom_ext fun F ↦ ?_)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, GrothendieckGroup.map_of, dimensionLayerCycleHom_of,
    dimensionLayerFinitePushforwardHom_of, dimensionLayerCycleHom_of, properPushforwardHom_apply]
  have hc : _root_.SheafOfModules.IsCoherent F.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  have hp : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward π).obj F.obj.obj) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite π
      F.obj.obj
  exact properPushforward_cycleAssociatedToCoherentSheaf C sX sY π hπ F.obj.obj k F.property

/-- For `Y` Noetherian, the homomorphism `Z_k ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` commutes with proper
pushforward of `k`-cycles on the source and direct image along the finite morphism `π` on the
target. -/
@[stacks 0FDR "commutativity of the left-hand square of the diagram, for `Y` Noetherian"]
theorem dimensionLayerFinitePushforwardHom_comp_cycleDimensionLayerHom (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (π : X ⟶ Y) [IsFinite π] [IsNoetherian Y] (hπ : π ≫ sY = sX) (k : ℤ) :
    (dimensionLayerFinitePushforwardHom C sX sY π hπ k).comp (cycleDimensionLayerHom C sX k) =
      (cycleDimensionLayerHom C sY k).comp (properPushforwardHom C sX sY π hπ k) := by
  refine AddMonoidHom.ext fun c ↦ ?_
  have hsq := DFunLike.congr_fun
    (properPushforwardHom_comp_dimensionLayerCycleHom C sX sY π hπ k)
    (cycleDimensionLayerHom C sX k c)
  have hid := DFunLike.congr_fun (cycleDimensionLayerHom_comp_dimensionLayerCycleHom C sY k)
    (dimensionLayerFinitePushforwardHom C sX sY π hπ k (cycleDimensionLayerHom C sX k c))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hsq hid ⊢
  rw [← hid, ← hsq, dimensionLayerCycleHom_cycleDimensionLayerHom]

/-- For `Y` Noetherian, the element of the Grothendieck group of the layer over `Y` attached to
the proper pushforward of a `k`-cycle `c` on `X` is the direct image along `π` of the element
attached to `c`. -/
@[stacks 0FDR "the left-hand square of the diagram on a cycle, for `Y` Noetherian"]
theorem dimensionLayerFinitePushforwardHom_cycleDimensionLayerHom (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (π : X ⟶ Y) [IsFinite π] [IsNoetherian Y] (hπ : π ≫ sY = sX) (k : ℤ)
    (c : CycleGroup C sX k) :
    dimensionLayerFinitePushforwardHom C sX sY π hπ k (cycleDimensionLayerHom C sX k c) =
      cycleDimensionLayerHom C sY k (properPushforwardHom C sX sY π hπ k c) :=
  DFunLike.congr_fun
    (dimensionLayerFinitePushforwardHom_comp_cycleDimensionLayerHom C sX sY π hπ k) c

end Stacks.Chow

end
