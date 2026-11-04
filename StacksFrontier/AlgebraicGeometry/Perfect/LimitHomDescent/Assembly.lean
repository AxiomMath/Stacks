module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.Restrict
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineSystem
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineObjects
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.MappingConeApproximation.ShiftLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Stacks 09RE for a directed system of schemes affine over a base

Let `B` be a quasi-compact and quasi-separated scheme and let `T_j ⟶ B` be a directed system of
schemes affine over `B` with limit `T`. For objects `E` and `K` of `D(𝒪_B)`, the group
`Hom(Lk^*E, Lk^*K)` is the filtered colimit of the `Hom(Lk_j^*E, Lk_j^*K)` if either `E` is
perfect and `K` lies in `D_QCoh(𝒪_B)`, or `E` is pseudo-coherent and `K` lies in `D_QCoh(𝒪_B)` and
has finite Tor dimension.

## Main results

* `Stacks.LimitHomDescent.SchemeSystem.isColim_of_isPerfect`: the first case.
* `Stacks.LimitHomDescent.SchemeSystem.isColim_of_isPseudoCoherent`: the second case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe d v u

namespace Stacks.LimitHomDescent

/-! ### The hypotheses of Stacks 09RE along an open immersion and under shifts -/

section Transfer

variable {V W : Scheme.{u}} (j : V ⟶ W)

/-- The cohomology sheaves of the derived pullback along an open immersion of an object with
quasi-coherent cohomology are quasi-coherent. -/
theorem isQuasicoherent_homology_pb [IsOpenImmersion j] (K : DMod W)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor W.Modules n).obj K).IsQuasicoherent)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor V.Modules n).obj ((pb j).obj K)).IsQuasicoherent := by
  have : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion j
  have : PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  exact (SheafOfModules.isQuasicoherent V.ringCatSheaf).prop_of_iso
    (derivedHomologyMapIso (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) K n ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso
        ((SpecField.derivedPullbackMapDerivedIso j.toLRSHom.toShHom).app K).symm)
    (Stacks.Modules.isQuasicoherent_pullback j _ (hK n))

/-- The derived pullback of a perfect object is perfect. -/
theorem isPerfect_pb (E : DMod W)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := V.toRingedSpace) ((pb j).obj E) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback j.toLRSHom.toShHom E hE

/-- The derived pullback of a pseudo-coherent object is pseudo-coherent. -/
theorem isPseudoCoherent_pb (E : DMod W)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := W.toRingedSpace) E) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := V.toRingedSpace)
      ((pb j).obj E) :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := V.toRingedSpace) _).2
    (DerivedFibreBetti.isPseudoCoherent_derivedPullback j E
      ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := W.toRingedSpace) E).1 hE))

/-- The derived pullback of an object of finite Tor dimension has finite Tor dimension. -/
theorem hasFiniteTorDimension_pb (E : DMod W)
    (hE : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension W.toRingedSpace E) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension V.toRingedSpace ((pb j).obj E) := by
  obtain ⟨a, b, h⟩ := hE
  exact ⟨a, b, Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
    j.toLRSHom.toShHom E a b h⟩

/-- A shift of a pseudo-coherent object is pseudo-coherent. -/
theorem isPseudoCoherent_shift {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u} X)]
    {E : DerivedCategory (StrictlyPerfect.OXMod.{u} X)}
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E) (m : ℤ) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) (E⟦m⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨K⟦m⟧, fun n => ?_, ⟨(DerivedCategory.Q.commShiftIso m).app K ≪≫
    (shiftFunctor _ m).mapIso e⟩⟩
  have h := RingedSpace.isPseudoCoherentComplexFrom_shift (hK (n + m)) m
  rwa [add_sub_cancel_right] at h

end Transfer

namespace SchemeSystem

variable {B : Scheme.{u}} {J : Type v} [Preorder J] (S : SchemeSystem.{v, u} B J)

/-! ### The inverse system and its cone -/

/-- The stages of the system, as a functor `Jᵒᵖ ⥤ Scheme`. -/
def diagram : Jᵒᵖ ⥤ Scheme.{u} where
  obj j := S.stage j.unop
  map f := S.transition (leOfHom f.unop)
  map_id j := S.transition_refl j.unop
  map_comp f g := (S.transition_comp (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The vertex of the system with its projections, as a cone over `S.diagram`. -/
def cone : Cone S.diagram where
  pt := S.limit
  π :=
    { app j := S.proj j.unop
      naturality _ _ f := (Category.id_comp _).trans (S.proj_transition (leOfHom f.unop)).symm }

/-- The inclusions of the stages of the restriction to an open `U` of the base. -/
def restrictDiagramι (U : B.Opens) : (S.restrict U).diagram ⟶ S.diagram where
  app j := (S.toBase j.unop ⁻¹ᵁ U).ι
  naturality _ _ _ := Scheme.Hom.resLE_comp_ι _ _

/-- The inclusion of the vertex of the restriction to an open `U` of the base, as a morphism of
cones. -/
def restrictConeι (U : B.Opens) :
    (Cone.postcompose (S.restrictDiagramι U)).obj (S.restrict U).cone ⟶ S.cone where
  hom := (S.limitToBase ⁻¹ᵁ U).ι
  w _ := (Scheme.Hom.resLE_comp_ι _ _).symm

/-- The inclusion of the vertex of the restriction to an open `U` of the base is an open
immersion. -/
instance (U : B.Opens) : IsOpenImmersion (S.restrictConeι U).hom :=
  inferInstanceAs (IsOpenImmersion (S.limitToBase ⁻¹ᵁ U).ι)

/-- The inclusion of each stage of the restriction to an open `U` of the base is an open
immersion. -/
instance (U : B.Opens) (j : Jᵒᵖ) : IsOpenImmersion ((S.restrictDiagramι U).app j) :=
  inferInstanceAs (IsOpenImmersion (S.toBase j.unop ⁻¹ᵁ U).ι)

/-- The preimage under the projection `S.proj j` of the preimage of an open `U` of the base in the
stage `j` is the preimage of `U` in the vertex. -/
theorem proj_preimage_opensRange (U : B.Opens) (j : J) :
    S.proj j ⁻¹ᵁ (S.toBase j ⁻¹ᵁ U).ι.opensRange = (S.limitToBase ⁻¹ᵁ U).ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
    S.proj_toBase]

/-- **The restriction of a limit to an open of the base is a limit.** -/
def isLimitRestrict [IsDirected J (· ≤ ·)] [Nonempty J] (hS : IsLimit S.cone) (U : B.Opens) :
    IsLimit (S.restrict U).cone := by
  have : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfIsPullbackOfIsConnected (S.restrictDiagramι U) (S.restrict U).cone S.cone
    (S.restrictConeι U)
    (fun j => IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (S.proj_preimage_opensRange U j.unop))
    hS

/-! ### Stacks 09RE for a system affine over a quasi-compact and quasi-separated base -/

section Main

variable {B : Scheme.{u}} {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  (S : SchemeSystem.{u, u} B J) (hS : IsLimit S.cone) [∀ j, IsAffineHom (S.toBase j)]

include hS in
/-- Over an affine open `U` of the base, the ring of sections of the vertex is the filtered
colimit of the rings of sections of the stages. -/
theorem isStagesColimit_restrict {U : B.Opens} (hU : IsAffineOpen U) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : (S.restrict U).ringSystem.A i) =>
        (S.restrict U).ringSystem.β h x)
      (fun j (x : (S.restrict U).ringSystem.A j) => (S.restrict U).ringSystem.γ j x) := by
  have : ∀ j : Jᵒᵖ, IsAffine ((S.restrict U).diagram.obj j) := fun j =>
    hU.preimage (S.toBase j.unop)
  exact isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed (S.restrict U).diagram
    (S.restrict U).cone (S.isLimitRestrict hS U)

include hS in
/-- **Stacks 09RE, the perfect case, for a system affine over the base.** -/
theorem isColim_of_isPerfect [CompactSpace B] [QuasiSeparatedSpace B] (E K : DMod B)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := B.toRingedSpace) E)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor B.Modules n).obj K).IsQuasicoherent) :
    S.IsColim E K := by
  refine S.isColim_of_isAffineOpen E K fun U hU m => ?_
  have : IsAffine U.toScheme := hU
  have : ∀ j, IsAffine ((S.restrict U).stage j) := fun j => hU.preimage (S.toBase j)
  have : ∀ j : Jᵒᵖ, IsAffine ((S.restrict U).diagram.obj j) := fun j =>
    hU.preimage (S.toBase j.unop)
  have : IsAffine (S.restrict U).limit := Scheme.isAffine_of_isLimit _ (S.isLimitRestrict hS U)
  refine ((S.restrict U).isColim_iff_ringSystem _ _).2 ?_
  exact (S.restrict U).ringSystem.isColim_of_isPerfect (S.isStagesColimit_restrict hS hU) _ _
    (isPerfect_pb _ _ (isPerfect_pb _ _
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hE m)))
    (isQuasicoherent_homology_pb _ _ (isQuasicoherent_homology_pb _ _ hK))

include hS in
/-- **Stacks 09RE, the pseudo-coherent case, for a system affine over the base.** -/
theorem isColim_of_isPseudoCoherent [CompactSpace B] [QuasiSeparatedSpace B] (E K : DMod B)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
      (X := B.toRingedSpace) E)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor B.Modules n).obj K).IsQuasicoherent)
    (hKt : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension B.toRingedSpace K) :
    S.IsColim E K := by
  refine S.isColim_of_isAffineOpen E K fun U hU m => ?_
  have : IsAffine U.toScheme := hU
  have : ∀ j, IsAffine ((S.restrict U).stage j) := fun j => hU.preimage (S.toBase j)
  have : ∀ j : Jᵒᵖ, IsAffine ((S.restrict U).diagram.obj j) := fun j =>
    hU.preimage (S.toBase j.unop)
  have : IsAffine (S.restrict U).limit := Scheme.isAffine_of_isLimit _ (S.isLimitRestrict hS U)
  refine ((S.restrict U).isColim_iff_ringSystem _ _).2 ?_
  exact (S.restrict U).ringSystem.isColim_of_isPseudoCoherent (S.isStagesColimit_restrict hS hU)
    _ _ (isPseudoCoherent_pb _ _ (isPseudoCoherent_pb _ _ (isPseudoCoherent_shift hE m)))
    (isQuasicoherent_homology_pb _ _ (isQuasicoherent_homology_pb _ _ hK))
    (hasFiniteTorDimension_pb _ _ (hasFiniteTorDimension_pb _ _ hKt))

end Main

end SchemeSystem

end Stacks.LimitHomDescent

end
