module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Base change of a one-step dévissage

A one-step dévissage of `F/X/S` over `s` is carried by an arbitrary morphism of pointed
schemes `(S', s') ⟶ (S, s)` with `S'` affine to a one-step dévissage of `F'/X'/S'` over `s'`,
where `X'`, `Z'`, `Y'` are the base changes of `X`, `Z`, `Y` and `F'`, `G'` are the pullbacks
of `F`, `G`.

All the structural properties involved — affineness of a fibre product of affines, and
stability under base change of closed immersions, of morphisms of finite presentation, of
finite morphisms, of smooth morphisms and of morphisms with geometrically irreducible fibres —
are already available; the two substantial points are that the direct image along the finite
morphism `i` commutes with base change, and that the dimension of the support of the module on
the distinguished fibre does not change. The latter is deduced here from the invariance of the
*local* dimension of a fibre under base change.

## Main definitions

* `AlgebraicGeometry.OneStepDevissage.BaseChangeData`: the base-changed dévissage together
  with the comparison morphisms to the original schemes and the cartesian squares they sit in.
* `AlgebraicGeometry.OneStepDevissage.baseChange`: the construction of that data.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_isPullback`: the dimension of a fibre of a
  morphism locally of finite type is unchanged by base change.
* `AlgebraicGeometry.topologicalKrullDim_supp_fiber_eq_of_isPullback`: the dimension of the
  support of the restriction of a module to a fibre is unchanged by base change, provided the
  support of the pulled-back module is the preimage of the support.

## Implementation notes

The new source scheme and its module are the chosen pullbacks `X ×_S S'` and
`(pr_X)^* F`; the remaining two schemes and their maps are pinned down only up to canonical
isomorphism, by the three cartesian squares recorded in
`AlgebraicGeometry.OneStepDevissage.BaseChangeData`. The module on the new closed subscheme is
literally the pullback of the old one.

The dimension statement for a whole fibre is obtained from the pointwise one by writing the
dimension of a space as the supremum of its local dimensions: the map from the fibre of the
base change to the fibre of the original morphism preserves local dimensions and is surjective
on points, so the two suprema agree. Surjectivity is
`AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`.

For the support, the support of a finite-type module is closed, so it carries the reduced
induced closed subscheme structure; base changing that closed subscheme turns the comparison
of supports into a comparison of fibres of two morphisms to a one-point base, which is the
previous paragraph.

## References

* [Stacks Project, Tag 05H7](https://stacks.math.columbia.edu/tag/05H7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section FibreDimension

/-- The local dimension of the fibre of `q` over `s` at the point represented by `x` is the
local dimension of the fibre of `q` through `x` at `x`. -/
private theorem topologicalKrullDimAt_fiberHomeo_symm_eq_asFiber {A B : Scheme.{u}} (q : A ⟶ B)
    (s : B) (x : A) (hx : q x = s) :
    topologicalKrullDimAt ↥(q.fiber s) ((q.fiberHomeo s).symm ⟨x, hx⟩) =
      topologicalKrullDimAt ↥(q.fiber (q x)) (q.asFiber x) := by
  rw [topologicalKrullDimAt_fiber_eq_preimage q s, Homeomorph.apply_symm_apply,
    topologicalKrullDimAt_fiber_asFiber_eq_preimage q x]
  exact topologicalKrullDimAt_preimage_congr (q : A → B) hx.symm x hx rfl

/-- The dimension of a fibre of a morphism locally of finite type is unchanged by base change:
in a cartesian square with `f` locally of finite type, the fibre of `f'` over `s'` has the same
dimension as the fibre of `f` over the image of `s'`. -/
theorem topologicalKrullDim_fiber_eq_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (s' : S') :
    topologicalKrullDim ↥(f'.fiber s') = topologicalKrullDim ↥(f.fiber (g s')) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim, topologicalKrullDim_eq_iSup_localKrullDim]
  simp only [← topologicalKrullDimAt_eq_localKrullDim]
  have hs : ∀ {A B : Scheme.{u}} (q : A ⟶ B) (t : B),
      (⨆ w : ↥(q.fiber t), topologicalKrullDimAt ↥(q.fiber t) w) =
        ⨆ w : (q : A → B) ⁻¹' {t},
          topologicalKrullDimAt ↥(q.fiber t) ((q.fiberHomeo t).symm w) :=
    fun q t => Equiv.iSup_congr (q.fiberHomeo t) fun _ => by simp
  rw [hs f' s', hs f (g s')]
  refine le_antisymm (iSup_le fun w' => ?_) (iSup_le fun w => ?_)
  · have hw' : f' w'.1 = s' := Set.mem_singleton_iff.mp w'.2
    have hcomm : f (g' w'.1) = g s' := by
      simpa [hw'] using congrArg (fun k : X' ⟶ S => k w'.1) h.w
    refine le_iSup_of_le (⟨g' w'.1, hcomm⟩ : (f : X → S) ⁻¹' {g s'}) (le_of_eq ?_)
    rw [topologicalKrullDimAt_fiberHomeo_symm_eq_asFiber f' s' w'.1 hw',
      topologicalKrullDimAt_fiberHomeo_symm_eq_asFiber f (g s') (g' w'.1) hcomm]
    exact topologicalKrullDimAt_fiber_eq_of_isPullback h w'.1
  · have hw : f w.1 = g s' := Set.mem_singleton_iff.mp w.2
    obtain ⟨x', hx', hs'⟩ := Scheme.exists_preimage_of_isPullback h w.1 s' hw
    have hx's : f' x' = s' := by simpa using hs'
    refine le_iSup_of_le (⟨x', hx's⟩ : (f' : X' → S') ⁻¹' {s'}) (le_of_eq ?_)
    rw [topologicalKrullDimAt_fiberHomeo_symm_eq_asFiber f (g s') w.1 hw,
      topologicalKrullDimAt_fiberHomeo_symm_eq_asFiber f' s' x' hx's,
      topologicalKrullDimAt_fiber_eq_of_isPullback h x', hx']

/-- Over a one-point base, the dimension of the support of a finite-type module is unchanged
by base change, provided the support of the pulled-back module is the preimage of the support.
-/
private theorem topologicalKrullDim_supp_eq_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g)
    (hf : LocallyOfFiniteType f) {F : X.Modules} {F' : X'.Modules}
    [F.IsFiniteType] [F'.IsFiniteType]
    (hSupp : SheafOfModules.supp F' = ⇑g' ⁻¹' SheafOfModules.supp F)
    (s' : S') [Subsingleton S] [Subsingleton S'] :
    topologicalKrullDim (SheafOfModules.supp F') =
      topologicalKrullDim (SheafOfModules.supp F) := by
  have := hf
  let I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩
  let i : I.subscheme ⟶ X := I.subschemeι
  let pZ : pullback i g' ⟶ I.subscheme := pullback.fst i g'
  let i' : pullback i g' ⟶ X' := pullback.snd i g'
  have hiRange : Set.range ⇑i = SheafOfModules.supp F := by
    show Set.range ⇑I.subschemeι = _
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hi'Range : Set.range ⇑i' = SheafOfModules.supp F' := by
    show Set.range ⇑(pullback.snd i g') = _
    rw [Scheme.Pullback.range_snd, hiRange, ← hSupp]
  have : IsClosedImmersion i' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback i g')
      inferInstance
  have : LocallyOfFiniteType (i ≫ f) := inferInstance
  have hZ : IsPullback pZ (i' ≫ f') (i ≫ f) g :=
    (IsPullback.of_hasPullback i g').paste_vert h
  have hrange : ∀ {A Y : Scheme.{u}} (j : A ⟶ Y) [IsClosedImmersion j] (T : Set Y),
      Set.range ⇑j = T → topologicalKrullDim T = topologicalKrullDim A := fun j _ T hT =>
    (IsHomeomorph.topologicalKrullDim_eq _
      (j.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hT)).isHomeomorph).symm
  have hfib : ∀ {A B : Scheme.{u}} (q : A ⟶ B) (t : B) [Subsingleton B],
      topologicalKrullDim ↥(q.fiber t) = topologicalKrullDim A := fun {A B} q t _ =>
    IsHomeomorph.topologicalKrullDim_eq _ ((q.fiberHomeo t).trans
      ((Homeomorph.setCongr (show (q : A → B) ⁻¹' {t} = Set.univ from
        Set.eq_univ_of_forall fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))).trans
          (Homeomorph.Set.univ A))).isHomeomorph
  calc topologicalKrullDim (SheafOfModules.supp F')
      = topologicalKrullDim ↥((i' ≫ f').fiber s') :=
        (hrange i' _ hi'Range).trans (hfib _ s').symm
    _ = topologicalKrullDim ↥((i ≫ f).fiber (g s')) :=
        topologicalKrullDim_fiber_eq_of_isPullback hZ s'
    _ = topologicalKrullDim (SheafOfModules.supp F) :=
        (hfib _ _).trans (hrange i _ hiRange).symm

/-- The dimension of the support of the restriction of a finite-type module to a fibre is
unchanged by base change, provided the support of the pulled-back module is the preimage of the
support. -/
theorem topologicalKrullDim_supp_fiber_eq_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType]
    (F' : X'.Modules) [F'.IsFiniteType]
    (hSupp : SheafOfModules.supp F' = ⇑g' ⁻¹' SheafOfModules.supp F) (s' : S') :
    topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι s')).obj F')) =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F)) := by
  let q : f'.fiber s' ⟶ f.fiber (g s') :=
    pullback.map f' (S'.fromSpecResidueField s') f (S.fromSpecResidueField (g s'))
      g' (Spec.map (g.residueFieldMap s')) g h.w.symm (by simp)
  have hmap : q ≫ f.fiberι (g s') = f'.fiberι s' ≫ g' := pullback.lift_fst _ _ _
  have hft₀ : ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (f.fiberι (g s')).toLRSHom.toShHom F
  have hft₀' : ((Scheme.Modules.pullback (f'.fiberι s')).obj F').IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (f'.fiberι s').toLRSHom.toShHom F'
  have hSupp₀ : SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι s')).obj F') =
      ⇑q ⁻¹' SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F) := by
    rw [Stacks.Modules.supp_pullback (f'.fiberι s') F',
      Stacks.Modules.supp_pullback (f.fiberι (g s')) F, hSupp]
    ext w
    have hw := congrArg (fun k : f'.fiber s' ⟶ X => k w) hmap
    show ((f'.fiberι s' ≫ g') w ∈ SheafOfModules.supp F) ↔
      ((q ≫ f.fiberι (g s')) w ∈ SheafOfModules.supp F)
    rw [hw]
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (g s')) := by
    show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g s')))
    infer_instance
  exact @topologicalKrullDim_supp_eq_of_isPullback _ _ _ _ _ _ _ _
    (isPullback_fiberToSpecResidueField_of_isPullback h s') hft
    ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F)
    ((Scheme.Modules.pullback (f'.fiberι s')).obj F') hft₀ hft₀' hSupp₀
    (IsLocalRing.closedPoint (S'.residueField s')) _ _

end FibreDimension

namespace OneStepDevissage

/-- The base change of a one-step dévissage of `F/X/S` over `s` along a morphism of pointed
schemes `(S', s') ⟶ (S, s)` with `S'` affine: a one-step dévissage of the pullback of `F` to
`X ×_S S'` over `s'`, together with the morphisms to the original closed subscheme and smooth
scheme and the cartesian squares exhibiting the four schemes as base changes. -/
structure BaseChangeData {X S S' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (s : S) (s' : S') (h : S' ⟶ S) (hs : h s' = s)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] [IsAffine S']
    (D : OneStepDevissage f F s) where
  /-- The base change of `f` is again locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType (pullback.snd f h)
  /-- The pullback of `F` is again quasi-coherent. -/
  quasicoherent : ((Scheme.Modules.pullback (pullback.fst f h)).obj F).IsQuasicoherent
  /-- The pullback of `F` is again of finite type. -/
  finiteType : ((Scheme.Modules.pullback (pullback.fst f h)).obj F).IsFiniteType
  /-- The base-changed dévissage. -/
  devissage :
    letI := locallyOfFiniteType
    letI := quasicoherent
    letI := finiteType
    OneStepDevissage (pullback.snd f h)
      ((Scheme.Modules.pullback (pullback.fst f h)).obj F) s'
  /-- The projection of the new smooth scheme to the old one. -/
  pY : devissage.Y ⟶ D.Y
  /-- The projection of the new closed subscheme to the old one. -/
  pZ : devissage.Z ⟶ D.Z
  /-- The smooth scheme is the base change of the old one. -/
  y_square : IsPullback pY devissage.g D.g h
  /-- The closed subscheme is the base change of the old one over the new source. -/
  x_square : IsPullback pZ devissage.i D.i (pullback.fst f h)
  /-- The closed subscheme is the base change of the old one over the new smooth scheme. -/
  z_square : IsPullback pZ devissage.π D.π pY
  /-- The module on the new closed subscheme is the pullback of the old one. -/
  module_eq : devissage.G = (Scheme.Modules.pullback pZ).obj D.G

/-- **Stacks Project, Tag 05H7.** A one-step dévissage and all its presenting data persist
under base change to a pointed affine scheme. -/
@[stacks 05H7]
def baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (s : S) (s' : S') (h : S' ⟶ S) (hs : h s' = s)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] [IsAffine S']
    (D : OneStepDevissage f F s) :
    BaseChangeData f F s s' h hs D := by
  let pX : pullback f h ⟶ X := pullback.fst f h
  let f' : pullback f h ⟶ S' := pullback.snd f h
  let pY : pullback D.g h ⟶ D.Y := pullback.fst D.g h
  let g' : pullback D.g h ⟶ S' := pullback.snd D.g h
  let pZ : pullback D.π pY ⟶ D.Z := pullback.fst D.π pY
  let π' : pullback D.π pY ⟶ pullback D.g h := pullback.snd D.π pY
  have hY : IsPullback pY g' D.g h := IsPullback.of_hasPullback D.g h
  have hZ : IsPullback pZ π' D.π pY := IsPullback.of_hasPullback D.π pY
  have hX : IsPullback pX f' f h := IsPullback.of_hasPullback f h
  have hover : (pZ ≫ D.i) ≫ f = (π' ≫ g') ≫ h := by
    simp only [Category.assoc, D.over_base]
    rw [← Category.assoc, hZ.w, Category.assoc, hY.w]
  let i' : pullback D.π pY ⟶ pullback f h := pullback.lift (pZ ≫ D.i) (π' ≫ g') hover
  have htop : π' ≫ g' = i' ≫ f' := (pullback.lift_snd _ _ _).symm
  have hcomp : IsPullback pZ (i' ≫ f') (D.i ≫ f) h := by
    rw [← htop, D.over_base]
    exact hZ.paste_vert hY
  have hxi : i' ≫ pX = pZ ≫ D.i := pullback.lift_fst _ _ _
  have hXsquare : IsPullback pZ i' D.i pX := (hX.paste_vert_iff hxi.symm).1 hcomp
  haveI : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback hX (P := @LocallyOfFiniteType) inferInstance
  haveI : ((Scheme.Modules.pullback pX).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ pX.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  haveI : ((Scheme.Modules.pullback pX).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType pX.toLRSHom.toShHom F
  haveI : D.G.IsQuasicoherent := D.quasi_coherent_G
  haveI : D.G.IsFiniteType := D.finite_type_G
  haveI : ((Scheme.Modules.pullback pZ).obj D.G).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ pZ.toLRSHom.toShHom D.G
      D.quasi_coherent_G
  haveI : ((Scheme.Modules.pullback pZ).obj D.G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType pZ.toLRSHom.toShHom D.G
  haveI : Smooth D.g := D.smooth
  haveI : LocallyOfFiniteType D.g := inferInstance
  haveI : LocallyOfFiniteType g' :=
    MorphismProperty.of_isPullback hY (P := @LocallyOfFiniteType) inferInstance
  haveI : IsAffine X := D.affine_X
  haveI : IsAffine S := D.affine_S
  haveI : IsAffine D.Z := D.affine_Z
  haveI : IsAffine D.Y := D.affine_Y
  haveI : IsClosedImmersion D.i := D.closed_immersion
  haveI : IsAffineHom D.i := inferInstance
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hXsquare D.G
  exact
    { locallyOfFiniteType := inferInstance
      quasicoherent := inferInstance
      finiteType := inferInstance
      devissage :=
        { Z := pullback D.π pY
          Y := pullback D.g h
          i := i'
          π := π'
          g := g'
          G := (Scheme.Modules.pullback pZ).obj D.G
          quasi_coherent_G := inferInstance
          finite_type_G := inferInstance
          over_base := htop.symm
          affine_X := inferInstance
          affine_S := inferInstance
          affine_Z := inferInstance
          affine_Y := inferInstance
          closed_immersion :=
            MorphismProperty.IsStableUnderBaseChange.of_isPullback hXsquare D.closed_immersion
          finite_presentation :=
            ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hXsquare
                D.finite_presentation.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hXsquare
                D.finite_presentation.2.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hXsquare
                D.finite_presentation.2.2⟩
          module_iso := (Scheme.Modules.pullback pX).mapIso D.module_iso ≪≫
            asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
              hXsquare.w).app D.G)
          finite := MorphismProperty.IsStableUnderBaseChange.of_isPullback hZ D.finite
          smooth := MorphismProperty.IsStableUnderBaseChange.of_isPullback hY D.smooth
          geometrically_irreducible :=
            MorphismProperty.IsStableUnderBaseChange.of_isPullback hY
              D.geometrically_irreducible
          fiber_dimension := fun t' => by
            change topologicalKrullDim ↥(g'.fiber t') =
              topologicalKrullDim (SheafOfModules.supp
                ((Scheme.Modules.pullback (f'.fiberι s')).obj
                  ((Scheme.Modules.pullback pX).obj F)))
            rw [topologicalKrullDim_fiber_eq_of_isPullback hY t',
              topologicalKrullDim_supp_fiber_eq_of_isPullback hX F _
                (Stacks.Modules.supp_pullback pX F) s', hs]
            exact D.fiber_dimension (h t') }
      pY := pY
      pZ := pZ
      y_square := hY
      x_square := hXsquare
      z_square := hZ
      module_eq := rfl }

end OneStepDevissage

end AlgebraicGeometry

end
