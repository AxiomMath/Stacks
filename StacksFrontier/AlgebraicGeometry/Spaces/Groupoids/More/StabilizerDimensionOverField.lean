module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.ConstantDimensionOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.BaseFieldUniqueness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.GlobalSections

/-!
# The dimension of a groupoid over a field and of its stabilizer

Let `G` be a groupoid in algebraic spaces over a base algebraic space whose space of objects is
the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and assume the source
and the target of `G` are locally of finite type. Then the space of arrows of `G` and the
stabilizer of `G` have the same dimension.

## Main results

* `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer`: over a field the arrow
  space and the stabilizer have the same dimension.
* `AlgebraicGeometry.GroupoidOverField.dimension_arrows_eq_dimension_stabilizer`: the same, for a
  groupoid in the situation of Stacks 06DY.

## References

* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06DY](https://stacks.math.columbia.edu/tag/06DY)
* [Stacks Project, Tag 06FD](https://stacks.math.columbia.edu/tag/06FD)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 04MK](https://stacks.math.columbia.edu/tag/04MK)
* [Stacks Project, Tag 04MI](https://stacks.math.columbia.edu/tag/04MI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_stabilizerDimensionOverField
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Two maps to a field spectrum agreeing at a point -/

/-- If two algebra structures on a ring over the same base have the same integral closure as a
subring, then every element in the image of one structure map is integral for the other. -/
private theorem isIntegral_of_toSubring_eq {k A : Type u} [CommRing k] [CommRing A]
    (iA iB : Algebra k A)
    (h : @Subalgebra.toSubring k A _ _ iA (@integralClosure k A _ _ iA) =
      @Subalgebra.toSubring k A _ _ iB (@integralClosure k A _ _ iB))
    (c : k) :
    @_root_.IsIntegral k A _ _ iB (@algebraMap k A _ _ iA c) := by
  have h1 : @algebraMap k A _ _ iA c ∈
      @Subalgebra.toSubring k A _ _ iA (@integralClosure k A _ _ iA) :=
    @RingHom.isIntegralElem_map k A _ _ (@algebraMap k A _ _ iA) c
  rw [h] at h1
  exact h1

/-- Two morphisms locally of finite type from a reduced connected scheme to the spectrum of a
field which agree on a field-valued point of the source are equal. -/
private theorem eq_of_field_point
    {k L : Type u} [Field k] [Field L] {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of k)) (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = q ≫ g)
    [_root_.AlgebraicGeometry.LocallyOfFiniteType f]
    [_root_.AlgebraicGeometry.LocallyOfFiniteType g]
    [ConnectedSpace X] [IsReduced X] : f = g := by
  let ψf : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let ψg : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  let ev : Γ(X, ⊤) →+* L := (q.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom
  have hIntf := isIntegral_of_toSubring_eq ψf.toAlgebra ψg.toAlgebra
    (_root_.AlgebraicGeometry.integralClosure_baseField_toSubring_eq k k X f g)
  have hIntg := isIntegral_of_toSubring_eq ψg.toAlgebra ψg.toAlgebra rfl
  let instB : Algebra k Γ(X, ⊤) := ψg.toAlgebra
  let Ig : Subalgebra k Γ(X, ⊤) := @integralClosure k Γ(X, ⊤) _ _ instB
  have hfield : IsField (↥Ig) :=
    _root_.AlgebraicGeometry.integralClosure_globalSections_isField k X g
  let : Field Ig := hfield.toField
  let evG : Ig →+* L := ev.comp Ig.val
  have hevG : Function.Injective evG := RingHom.injective evG
  have hg_in (c : k) : ψg c ∈ Ig := hIntg c
  have hf_in (c : k) : ψf c ∈ Ig := hIntf c
  have hEval : ev.comp ψf = ev.comp ψg := by
    have happ : f.appTop ≫ q.appTop = g.appTop ≫ q.appTop := by
      simpa only [← Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hq
    have happR : q.appTop.hom.comp f.appTop.hom = q.appTop.hom.comp g.appTop.hom :=
      congrArg CommRingCat.Hom.hom happ
    ext c
    exact congrArg (fun h : Γ(Spec (.of k), ⊤) →+* Γ(Spec (.of L), ⊤) =>
      (Scheme.ΓSpecIso (.of L)).hom.hom
        (h ((Scheme.ΓSpecIso (.of k)).inv.hom c))) happR
  have hψeq : ψf = ψg := by
    ext c
    have hev : evG ⟨ψf c, hf_in c⟩ = evG ⟨ψg c, hg_in c⟩ :=
      congrArg (fun h : k →+* L => h c) hEval
    exact congrArg Subtype.val (hevG hev)
  exact _root_.AlgebraicGeometry.ext_to_Spec (CommRingCat.Hom.ext hψeq)

/-! ### The reduced induced structure on a closed subset -/

/-- A morphism from the spectrum of a field hitting a point of a closed subset factors through
the reduced induced closed subscheme on that subset. -/
private theorem fieldMap_factors_reducedClosedSubscheme
    {L : Type u} [Field L] {X : Scheme.{u}} (f : Spec (.of L) ⟶ X)
    (x : X) (hx : f (IsLocalRing.closedPoint L) = x) (Z : Closeds X)
    (hxZ : x ∈ Z) :
    ∃ s : Spec (.of L) ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      s ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f := by
  have hrange : Set.range f = {x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint L := Subsingleton.elim _ _
      simp [hx, hz]
    · intro hy
      subst y
      exact ⟨IsLocalRing.closedPoint L, hx⟩
  have hI : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range f]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    show closure (Set.range f) ⊆ (Z : Set X)
    rw [hrange]
    exact closure_minimal (Set.singleton_subset_iff.mpr hxZ) Z.2
  have hIker : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ f.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hI
  exact ⟨_root_.AlgebraicGeometry.IsClosedImmersion.lift
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι f hIker,
    _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _⟩

/-! ### Preliminaries on étale charts -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being étale, pulled back along the functor to schemes, is multiplicative. -/
private theorem isMultiplicative_inverseImage_etale
    {D : Type*} [Category D] (T : D ⥤ Scheme.{u}) :
    (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        T).IsMultiplicative := by
  refine { toContainsIdentities := ?_, toIsStableUnderComposition := ?_ }
  · exact ⟨fun X => by
      show _root_.AlgebraicGeometry.Etale (T.map (𝟙 X))
      rw [T.map_id]
      infer_instance⟩
  · exact ⟨fun f g hf hg => by
      show _root_.AlgebraicGeometry.Etale (T.map (f ≫ g))
      rw [T.map_comp]
      let : _root_.AlgebraicGeometry.Etale (T.map f) := hf
      let : _root_.AlgebraicGeometry.Etale (T.map g) := hg
      exact _root_.AlgebraicGeometry.Etale.etale_comp (T.map f) (T.map g)⟩

/-- An isomorphism of presheaves is an étale chart morphism. -/
private theorem inverseImageEtale_presheaf_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : F ⟶ G) [IsIso b] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda b, ?_⟩
  intro A D g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  let : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  show _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- The dimension of a scheme over `S`, read as an algebraic space, is the Krull dimension of
the scheme. -/
private theorem dimension_schemeSpace (U : BigFppfOver B S hS) :
    dimension B S hS (_root_.AlgebraicGeometry.schemeSpace U).obj
      (_root_.AlgebraicGeometry.schemeSpace U).property =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  let F := yoneda.obj (C := BigFppfOver B S hS) U
  have hid : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (𝟙 F) :=
    inverseImageEtale_presheaf_of_isIso B S hS (𝟙 F)
  have hd (p : FieldValuedPoint B S hS F) :
      dimensionAtPoint B S hS F (_root_.AlgebraicGeometry.schemeSpace U).property
          (p.class B S hS F) =
        topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p) :=
    dimensionAtPoint_eq_of_etale_chart B S hS F
      (_root_.AlgebraicGeometry.schemeSpace U).property _ U (𝟙 F) hid p (by rfl)
  have hs : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) =
      ⨆ x : (BigFppfOver.toScheme B S hS).obj U,
        topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) x := by
    simp only [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    exact TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim _
  show (⨆ q : points B S hS F,
    dimensionAtPoint B S hS F (_root_.AlgebraicGeometry.schemeSpace U).property q) = _
  rw [hs]
  refine le_antisymm (iSup_le fun q => ?_) (iSup_le fun x => ?_)
  · obtain ⟨p, rfl⟩ := Quot.exists_rep q
    rw [hd]
    exact le_iSup _ _
  · have hqc : QuasiCompact
        (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x) := by
      rw [quasiCompact_iff_forall_isAffineOpen]
      intro V hV
      exact (Set.toFinite
        (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x ⁻¹'
          (V : Set ((BigFppfOver.toScheme B S hS).obj U)))).isCompact
    have hsize := (Scheme.size_le_of_mono_quasiCompact
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x)).trans_lt U.left.property
    let fx : B.obj hsize ⟶ U.left := B.inclusion.preimage
      (X := B.obj hsize) (Y := U.left)
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x)
    let W : BigFppfOver B S hS := Over.mk (fx ≫ U.hom)
    let fU : W ⟶ U := Over.homMk fx
    let p : FieldValuedPoint B S hS F :=
      { carrier := ((BigFppfOver.toScheme B S hS).obj U).residueField x
        contained := hsize
        toBase := B.inclusion.map (fx ≫ U.hom)
        value := yonedaEquiv (yoneda.map fU) }
    refine le_trans ?_ (le_iSup
      (fun q : points B S hS F =>
        dimensionAtPoint B S hS F (_root_.AlgebraicGeometry.schemeSpace U).property q)
      (p.class B S hS F))
    rw [hd p]
    have hpoint : schemePoint B S hS U p = x := by
      show (B.inclusion.map (B.inclusion.preimage
        (X := B.obj hsize) (Y := U.left)
        (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x))) _ = x
      rw [B.inclusion.map_preimage]
      exact Scheme.fromSpecResidueField_apply x _
    exact le_of_eq (congrArg
      (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)) hpoint).symm

/-! ### Separatedness of the object space and the stabilizer as a closed subspace -/

/-- A morphism of presheaves out of the presheaf represented by the spectrum of a field over the
base is separated. -/
private theorem isSeparated_of_eq_yoneda_field {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : F = yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (f : F ⟶ H) :
    IsSeparated B S hS f := by
  subst hF
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  let O : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal O := Over.mkIdTerminal
  let hTO : IsTerminal (yoneda.obj O) := hT.isTerminalObj yoneda
  let g : H ⟶ yoneda.obj O := hTO.from H
  let π : V ⟶ O := Over.homMk V.hom (Category.comp_id V.hom)
  have hsepY : IsSeparated B S hS (yoneda.map π) :=
    (isSeparated_yoneda_map_iff B S hS π).2 (by
      show _root_.AlgebraicGeometry.IsSeparated structureMap
      exact _root_.AlgebraicGeometry.isSeparated_of_injective structureMap
        (fun x y _ => Subsingleton.elim _ _))
  refine isSeparated_of_comp B S hS f g ?_
  rw [hTO.hom_ext (f ≫ g) (yoneda.map π)]
  exact hsepY

/-- In the situation of Stacks 06DY the projection of the stabilizer to the arrow space is a
closed immersion. -/
private theorem isClosedImmersion_stabilizerArrow {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    IsClosedImmersion B S hS (GroupoidInAlgebraicSpaces.stabilizerArrow G) := by
  have hsep : IsSeparated B S hS G.objectsToBase.hom :=
    isSeparated_of_eq_yoneda_field B S hS hk structureMap hU G.objectsToBase.hom
  have hdiag : IsClosedImmersion B S hS (GroupoidInAlgebraicSpaces.diagonal G).hom := by
    show IsClosedImmersion B S hS (pullback.diagonal G.objectsToBase.hom)
    exact hsep
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (GroupoidInAlgebraicSpaces.sourceTarget G) (GroupoidInAlgebraicSpaces.diagonal G)
  show IsClosedImmersion B S hS
    (pullback.fst (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (GroupoidInAlgebraicSpaces.diagonal G).hom)
  exact isClosedImmersion_of_isPullback B S hS hpb.flip hdiag

/-- The stabilizer has dimension at most that of the arrow space. -/
private theorem dimension_stabilizer_le_arrows {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    dimension B S hS (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj
      (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property ≤
    dimension B S hS G.arrows.obj G.arrows.property := by
  let i : (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj ⟶ G.arrows.obj :=
    pullback.fst (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (GroupoidInAlgebraicSpaces.diagonal G).hom
  have hi : IsClosedImmersion B S hS i :=
    isClosedImmersion_stabilizerArrow B S hS hk structureMap G hU
  have himm : IsImmersion B S hS i := by
    refine ⟨hi.1, ?_⟩
    intro A' D g fst snd hpb
    have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map snd) := hi.2 g fst snd hpb
    let : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := hclosed
    show _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  have hmono : Mono i := mono_of_isImmersion B S hS himm
  have hlft : IsLocallyOfFiniteType B S hS i :=
    isLocallyOfFiniteType_of_isImmersion B S hS i himm
  have hqf : IsLocallyQuasiFinite B S hS i :=
    isLocallyQuasiFinite_of_mono B S hS
      (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property G.arrows.property i hmono hlft
  exact dimension_le_of_isLocallyQuasiFinite B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property G.arrows.property i hqf

/-! ### The identity arrow and the dimension there -/

/-- The single point of the object space, as a section over the field spectrum. -/
private noncomputable def objectPoint {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    G.objects.obj.obj (Opposite.op (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :=
  (eqToHom hU.symm).app (Opposite.op (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (yonedaEquiv (𝟙 (yoneda.obj
      (show BigFppfOver B S hS from Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))))

/-- The identity arrow at the single point of the object space. -/
private noncomputable def identityArrowSection {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    G.arrows.obj.obj (Opposite.op (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :=
  G.toGroupoidInFunctors.identity
    (Opposite.op (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (objectPoint B S hS hk structureMap G hU)

/-- The identity arrow at the single point of the object space, as a field-valued point of the
arrow space. -/
private noncomputable def identityArrowFieldPoint {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    FieldValuedPoint B S hS G.arrows.obj where
  carrier := k
  field := inferInstance
  contained := hk
  toBase := structureMap
  value := identityArrowSection B S hS hk structureMap G hU

private theorem identityArrowFieldPoint_value {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    (identityArrowFieldPoint B S hS hk structureMap G hU).value =
      identityArrowSection B S hS hk structureMap G hU := rfl

/-- The point of the arrow space given by the identity arrow at the single point of the object
space. -/
private noncomputable def identityArrowPoint {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS))) :
    points B S hS G.arrows.obj :=
  (identityArrowFieldPoint B S hS hk structureMap G hU).class B S hS G.arrows.obj

/-- Both composites of an étale chart of the arrow space with the source and with the target are
morphisms of the site to the field spectrum which are locally of finite type. -/
private theorem chart_source_target_locallyOfFiniteType
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (V : BigFppfOver B S hS) (hU : G.objects.obj = yoneda.obj V)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ G.arrows.obj)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom) :
    ∃ fs ft : U ⟶ V,
      _root_.AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map fs) ∧
      _root_.AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ft) ∧
      yoneda.map fs = a ≫ G.source.hom ≫ eqToHom hU ∧
        yoneda.map ft = a ≫ G.target.hom ≫ eqToHom hU := by
  let b : yoneda.obj V ⟶ G.objects.obj := eqToHom hU.symm
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b := by
    let : IsIso b := ⟨eqToHom hU, by simp [b], by simp [b]⟩
    exact inverseImageEtale_presheaf_of_isIso B S hS b
  have key (m : G.arrows.obj ⟶ G.objects.obj)
      (hm : IsLocallyOfFiniteType B S hS m) :
      ∃ f : U ⟶ V, _root_.AlgebraicGeometry.LocallyOfFiniteType
        ((BigFppfOver.toScheme B S hS).map f) ∧ yoneda.map f = a ≫ m ≫ eqToHom hU := by
    refine ⟨yoneda.preimage (a ≫ m ≫ eqToHom hU), hm U V a b _ ha hb ?_, yoneda.map_preimage _⟩
    rw [yoneda.map_preimage]
    simp [b]
  obtain ⟨fs, hfs, hfs_map⟩ := key _ hs
  obtain ⟨ft, hft, hft_map⟩ := key _ ht
  exact ⟨fs, ft, hfs, hft, hfs_map, hft_map⟩

/-- The dimension of the arrow space at the identity arrow is at most the dimension of the
stabilizer. -/
private theorem identityPoint_dimension_le_stabilizer {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom) :
    dimensionAtPoint B S hS G.arrows.obj G.arrows.property
        (identityArrowPoint B S hS hk structureMap G hU) ≤
      dimension B S hS (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj
        (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property := by
  classical
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  let T := BigFppfOver.toScheme B S hS
  let pid : FieldValuedPoint B S hS G.arrows.obj :=
    identityArrowFieldPoint B S hS hk structureMap G hU
  let x : G.objects.obj.obj (Opposite.op V) := objectPoint B S hS hk structureMap G hU
  have hpidvalue : pid.value = G.toGroupoidInFunctors.identity (Opposite.op V) x :=
    identityArrowFieldPoint_value B S hS hk structureMap G hU
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS G.arrows.obj
    G.arrows.property (identityArrowPoint B S hS hk structureMap G hU)
  obtain ⟨fs, ft, hfs, hft, hfs_map, hft_map⟩ :=
    chart_source_target_locallyOfFiniteType B S hS G V hU U a ha hs ht
  let : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map fs) := hfs
  let : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map ft) := hft
  let r₀ := schemePoint B S hS U p
  obtain ⟨Z, hZ, hrZ, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
      k (T.obj U) (T.map fs) r₀
  have hclass : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) =
      pid.class B S hS G.arrows.obj := hp
  obtain ⟨r, hrp, hrid⟩ := (FieldValuedPoint.class_eq_class_iff B S hS G.arrows.obj
    (FieldValuedPoint.map B S hS (yoneda.obj U) a p) pid).1 hclass
  obtain ⟨ι, hι⟩ := hrp
  obtain ⟨j, hj⟩ := hrid
  let qU : r.siteObject ⟶ U := ι ≫ p.value
  let pr : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := r.carrier, field := r.field, contained := r.contained,
      toBase := r.toBase, value := qU }
  have hqPoint : (T.map qU) (IsLocalRing.closedPoint r.carrier) = r₀ :=
    schemePoint_eq_of_dominates B S hS U (p := pr) (q := p) ⟨ι, rfl⟩
  let Zc : Closeds (T.obj U) := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let I : (T.obj U).IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Zc
  let Xc := I.subscheme
  have hrange : Set.range I.subschemeι.base = Z :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Zc
  have hembZ : Topology.IsEmbedding I.subschemeι.base :=
    _root_.AlgebraicGeometry.IsPreimmersion.isEmbedding I.subschemeι
  have hirrXc : IrreducibleSpace Xc :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme (T.obj U) I (by rw [hrange]; exact hZ.1)
  have : ConnectedSpace Xc := inferInstance
  have : IsReduced Xc := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Zc
  obtain ⟨s, hsFactor⟩ :=
    fieldMap_factors_reducedClosedSubscheme (T.map qU) r₀ hqPoint Zc hrZ
  change s ≫ I.subschemeι = T.map qU at hsFactor
  let : Groupoid (G.objects.obj.obj (Opposite.op V)) :=
    G.toGroupoidInFunctors.evaluationGroupoid (Opposite.op V)
  have hsourceId : G.source.hom.app (Opposite.op V) pid.value = x := by
    rw [hpidvalue]
    exact (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op V) x x (𝟙 x)).2.1
  have htargetId : G.target.hom.app (Opposite.op V) pid.value = x := by
    rw [hpidvalue]
    exact (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op V) x x (𝟙 x)).2.2
  have hR (m : G.arrows.obj ⟶ G.objects.obj) (hm : m.app (Opposite.op V) pid.value = x) :
      m.app (Opposite.op r.siteObject) r.value = G.objects.obj.map j.op x := by
    rw [← hj, m.naturality_apply j.op pid.value]
    exact congrArg (G.objects.obj.map j.op) hm
  have hsourceR := hR _ hsourceId
  have htargetR := hR _ htargetId
  have hsourceTargetValue : G.source.hom.app (Opposite.op r.siteObject) r.value =
      G.target.hom.app (Opposite.op r.siteObject) r.value := by
    rw [hsourceR, htargetR]
  have hchart : yoneda.map qU ≫ a = yonedaEquiv.symm r.value := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
    exact (a.naturality_apply ι.op p.value).trans hι
  have hsourceMapEq : yoneda.map qU ≫ a ≫ G.source.hom ≫ eqToHom hU =
      yoneda.map qU ≫ a ≫ G.target.hom ≫ eqToHom hU := by
    apply yonedaEquiv.injective
    show yonedaEquiv ((yoneda.map qU ≫ a) ≫ (G.source.hom ≫ eqToHom hU)) =
      yonedaEquiv ((yoneda.map qU ≫ a) ≫ (G.target.hom ≫ eqToHom hU))
    simp only [hchart, yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact congrArg (fun y => (eqToHom hU).app (Opposite.op r.siteObject) y) hsourceTargetValue
  have hqUmaps : qU ≫ fs = qU ≫ ft := by
    apply Functor.map_injective yoneda
    calc yoneda.map (qU ≫ fs) = yoneda.map qU ≫ yoneda.map fs := yoneda.map_comp _ _
      _ = yoneda.map qU ≫ (a ≫ G.source.hom ≫ eqToHom hU) :=
        congrArg (fun φ => yoneda.map qU ≫ φ) hfs_map
      _ = yoneda.map qU ≫ (a ≫ G.target.hom ≫ eqToHom hU) := hsourceMapEq
      _ = yoneda.map qU ≫ yoneda.map ft := congrArg (fun φ => yoneda.map qU ≫ φ) hft_map.symm
      _ = yoneda.map (qU ≫ ft) := (yoneda.map_comp _ _).symm
  let fX : Xc ⟶ Spec (.of k) := I.subschemeι ≫ T.map fs
  let gX : Xc ⟶ Spec (.of k) := I.subschemeι ≫ T.map ft
  have hqeq : s ≫ fX = s ≫ gX := by
    show s ≫ I.subschemeι ≫ T.map fs = s ≫ I.subschemeι ≫ T.map ft
    simpa only [Functor.map_comp, ← Category.assoc, hsFactor] using T.congr_map hqUmaps
  have hfg : fX = gX := by
    let : _root_.AlgebraicGeometry.LocallyOfFiniteType fX := by
      dsimp only [fX]; infer_instance
    let : _root_.AlgebraicGeometry.LocallyOfFiniteType gX := by
      dsimp only [gX]; infer_instance
    exact eq_of_field_point fX gX s hqeq
  have hxsize : B.Contains Xc :=
    (Scheme.size_le_of_mono_quasiCompact I.subschemeι).trans_lt U.left.property
  let zInU : B.obj hxsize ⟶ U.left :=
    B.inclusion.preimage (X := B.obj hxsize) (Y := U.left) I.subschemeι
  let Zobj : BigFppfOver B S hS := Over.mk (zInU ≫ U.hom)
  let zU : Zobj ⟶ U := Over.homMk zInU (by simp [Zobj])
  have hzUmap : T.map zU = I.subschemeι := by
    show B.inclusion.map
      (B.inclusion.preimage (X := B.obj hxsize) (Y := U.left) I.subschemeι) = I.subschemeι
    rw [B.inclusion.map_preimage]
  have hsiteeq : zU ≫ fs = zU ≫ ft := by
    apply Functor.map_injective T
    simpa only [Functor.map_comp, hzUmap] using hfg
  let Zspace : AlgebraicSpaces B S hS := _root_.AlgebraicGeometry.schemeSpace Zobj
  let zArrow : Zspace ⟶ G.arrows := ObjectProperty.homMk (yoneda.map zU ≫ a)
  let b : yoneda.obj V ⟶ G.objects.obj := eqToHom hU.symm
  let zObject : Zspace ⟶ G.objects := ObjectProperty.homMk (yoneda.map (zU ≫ fs) ≫ b)
  have he : eqToHom hU ≫ b = 𝟙 G.objects.obj := by simp [b]
  have htarget : zArrow.hom ≫ G.target.hom = zObject.hom := by
    show yoneda.map zU ≫ a ≫ G.target.hom = yoneda.map (zU ≫ fs) ≫ b
    rw [hsiteeq, Functor.map_comp, hft_map]
    simp only [Category.assoc, he, Category.comp_id]
  have hsource : zArrow.hom ≫ G.source.hom = zObject.hom := by
    show yoneda.map zU ≫ a ≫ G.source.hom = yoneda.map (zU ≫ fs) ≫ b
    rw [Functor.map_comp, hfs_map]
    simp only [Category.assoc, he, Category.comp_id]
  let i : (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj ⟶ G.arrows.obj :=
    pullback.fst (GroupoidInAlgebraicSpaces.sourceTarget G).hom
      (GroupoidInAlgebraicSpaces.diagonal G).hom
  let iSpace : GroupoidInAlgebraicSpaces.stabilizerOverBase G ⟶ G.arrows :=
    ObjectProperty.homMk i
  have hpull : zArrow.hom ≫ (GroupoidInAlgebraicSpaces.sourceTarget G).hom =
      zObject.hom ≫ (GroupoidInAlgebraicSpaces.diagonal G).hom := by
    show zArrow.hom ≫ pullback.lift G.target.hom G.source.hom _ =
      zObject.hom ≫ pullback.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj) _
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, pullback.lift_fst, Category.comp_id] using htarget
    · simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using hsource
  let qStab : Zspace ⟶ GroupoidInAlgebraicSpaces.stabilizerOverBase G :=
    ObjectProperty.homMk (pullback.lift zArrow.hom zObject.hom hpull)
  have hfactor : qStab.hom ≫ iSpace.hom = zArrow.hom := pullback.lift_fst _ _ _
  have hiClosed : IsClosedImmersion B S hS i :=
    isClosedImmersion_stabilizerArrow B S hS hk structureMap G hU
  have hrep : yoneda.relativelyRepresentable iSpace.hom := hiClosed.1
  let W := hrep.pullback a
  let wStab : _root_.AlgebraicGeometry.schemeSpace W ⟶
      GroupoidInAlgebraicSpaces.stabilizerOverBase G := ObjectProperty.homMk (hrep.fst a)
  have hWClosed : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (hrep.snd a)) :=
    hiClosed.2 a (hrep.fst a) (hrep.snd a) (hrep.isPullback a)
  let aSpace : _root_.AlgebraicGeometry.schemeSpace U ⟶ G.arrows := ObjectProperty.homMk a
  have haSpaceEtale : IsEtale B S hS aSpace.hom := by
    let E : MorphismProperty (BigFppfOver B S hS) :=
      MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
    change E.relative yoneda a at ha
    intro D φ hφ
    change E.relative yoneda φ at hφ
    have : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : E.IsMultiplicative := isMultiplicative_inverseImage_etale T
    have : E.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
    have : (E.relative yoneda).IsMultiplicative := MorphismProperty.relative_isMultiplicative E
    exact MorphismProperty.comp_mem (E.relative yoneda) φ a hφ ha
  have hWPullback : IsPullback (_root_.AlgebraicGeometry.schemeSpaceMap (hrep.snd a))
      wStab aSpace iSpace := by
    apply IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS))
    exact (hrep.isPullback a).flip
  have hWEtale : IsEtale B S hS wStab.hom :=
    isEtale_of_isPullback B S hS (_root_.AlgebraicGeometry.schemeSpaceMap (hrep.snd a))
      wStab aSpace iSpace hWPullback haSpaceEtale
  have hWQF : IsLocallyQuasiFinite B S hS wStab.hom :=
    isLocallyQuasiFinite_of_isEtale B S hS
      (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property hWEtale
  let c : Zobj ⟶ W := hrep.lift qStab.hom zU hfactor
  have hcU : c ≫ hrep.snd a = zU := hrep.lift_snd qStab.hom zU hfactor
  have hcClosed : _root_.AlgebraicGeometry.IsClosedImmersion (T.map c) := by
    have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
        (T.map c ≫ T.map (hrep.snd a)) := by
      rw [← Functor.map_comp, hcU, hzUmap]
      infer_instance
    let : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (hrep.snd a)) := hWClosed
    exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion (T.map c)
      (T.map (hrep.snd a))
  let cSpace : _root_.AlgebraicGeometry.schemeSpace Zobj ⟶
    _root_.AlgebraicGeometry.schemeSpace W := _root_.AlgebraicGeometry.schemeSpaceMap c
  have hcQF : IsLocallyQuasiFinite B S hS cSpace.hom := by
    show HoldsOnEveryEtaleChart B S hS
      ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (yoneda.map c)
    refine (holdsOnEveryEtaleChart_iff_representable B S hS _
      locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
      (yoneda.map c)).2 ?_
    let : _root_.AlgebraicGeometry.IsClosedImmersion (T.map c) := hcClosed
    let eZ := yoneda.preimageIso (yoneda.obj Zobj).reprW
    let eW := yoneda.preimageIso (yoneda.obj W).reprW
    simp only [Functor.preimage_comp, Functor.preimage_map]
    show _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map (eZ.hom ≫ c ≫ eW.inv)) ∧
      _root_.AlgebraicGeometry.LocallyQuasiFinite (T.map (eZ.hom ≫ c ≫ eW.inv))
    simp only [Functor.map_comp]
    have hclosed' : _root_.AlgebraicGeometry.IsClosedImmersion
        (T.map eZ.hom ≫ T.map c ≫ T.map eW.inv) := by
      let : _root_.AlgebraicGeometry.IsClosedImmersion (T.map eZ.hom) := inferInstance
      let : _root_.AlgebraicGeometry.IsClosedImmersion (T.map eW.inv) := inferInstance
      let : _root_.AlgebraicGeometry.IsClosedImmersion (T.map eZ.hom ≫ T.map c) :=
        _root_.AlgebraicGeometry.IsClosedImmersion.comp _ _
      exact _root_.AlgebraicGeometry.IsClosedImmersion.comp _ _
    have hfinite : _root_.AlgebraicGeometry.IsFinite
        (T.map eZ.hom ≫ T.map c ≫ T.map eW.inv) :=
      ((_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mp hclosed').1
    refine ⟨((_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp
        hfinite).2, ?_⟩
    let : _root_.AlgebraicGeometry.IsFinite
      (T.map eZ.hom ≫ T.map c ≫ T.map eW.inv) := hfinite
    exact _root_.AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite _
  have htotalQF := isLocallyQuasiFinite_comp B S hS
    (_root_.AlgebraicGeometry.schemeSpace Zobj).property
    (_root_.AlgebraicGeometry.schemeSpace W).property
    (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property cSpace.hom wStab.hom hcQF hWQF
  have hdimle := dimension_le_of_isLocallyQuasiFinite B S hS
    (_root_.AlgebraicGeometry.schemeSpace Zobj).property
    (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property (cSpace ≫ wStab).hom htotalQF
  have hdimSub : topologicalKrullDim Xc = topologicalKrullDim ↥Z :=
    IsHomeomorph.topologicalKrullDim_eq _
      (hembZ.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
  have hpDim := dimensionAtPoint_eq_of_etale_chart B S hS G.arrows.obj G.arrows.property
    (identityArrowPoint B S hS hk structureMap G hU) U a ha p hp
  calc dimensionAtPoint B S hS G.arrows.obj G.arrows.property
        (identityArrowPoint B S hS hk structureMap G hU)
      = topologicalKrullDimAt (T.obj U) r₀ := hpDim
    _ = topologicalKrullDim ↥Z := hZdim.symm
    _ = topologicalKrullDim Xc := hdimSub.symm
    _ = dimension B S hS (_root_.AlgebraicGeometry.schemeSpace Zobj).obj
          (_root_.AlgebraicGeometry.schemeSpace Zobj).property :=
        (dimension_schemeSpace B S hS Zobj).symm
    _ ≤ dimension B S hS (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj
          (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property := hdimle

/-- Let `G` be a groupoid in algebraic spaces over `S` whose space of objects
is the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and whose source
and target are locally of finite type. Then the space of arrows of `G` and the stabilizer of `G`
have the same dimension. -/
@[stacks 06FF]
theorem dimension_arrows_eq_dimension_stabilizer {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_eq : G.objects = _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom) :
    dimension B S hS G.arrows.obj G.arrows.property =
      dimension B S hS (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj
        (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property := by
  have hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)) :=
    congrArg (fun Z : AlgebraicSpaces B S hS => Z.obj) objects_eq
  have hid : dimension B S hS G.arrows.obj G.arrows.property =
      dimensionAtPoint B S hS G.arrows.obj G.arrows.property
        (identityArrowPoint B S hS hk structureMap G hU) :=
    dimension_eq_dimensionAtPoint B S hS hk structureMap G objects_eq hs ht _
  rw [hid]
  refine le_antisymm
    (identityPoint_dimension_le_stabilizer B S hS hk structureMap G hU hs ht) ?_
  rw [← hid]
  exact dimension_stabilizer_le_arrows B S hS hk structureMap G hU

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidOverField

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS}

/-- **Stacks 06FF** in the situation of Stacks 06DY: the space of arrows of a groupoid in
algebraic spaces over a field whose source and target are locally of finite type has the same
dimension as the stabilizer. -/
theorem dimension_arrows_eq_dimension_stabilizer (G : GroupoidOverField B S hS A)
    (hs : Space.IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : Space.IsLocallyOfFiniteType B S hS G.target.hom) :
    Space.dimension B S hS G.arrows.obj G.arrows.property =
      Space.dimension B S hS
        (GroupoidInAlgebraicSpaces.stabilizerOverBase G.groupoid).obj
        (GroupoidInAlgebraicSpaces.stabilizerOverBase G.groupoid).property :=
  Space.dimension_arrows_eq_dimension_stabilizer B S hS G.containsSpec G.structureMap
    G.groupoid G.objects_eq hs ht

end AlgebraicGeometry.GroupoidOverField

end
