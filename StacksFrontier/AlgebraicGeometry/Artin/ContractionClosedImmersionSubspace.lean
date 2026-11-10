module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# The closed subspace cut out by the ideal sheaf of a contraction

The ideal sheaf `AlgebraicGeometry.Artin.ContractionSituation.ClosedImmersionData.idealSheaf`
on `S` cuts out a closed subscheme of `S`, hence a closed subspace `X` of the terminal presheaf.
This file constructs `X` and reads its points: over an affine object `V` mapping to the chart of
an affine open `U`, `V` lies in `X` exactly when the ring map `Γ(S, U) → Γ(V)` kills the ideal
attached to `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation.ClosedImmersionData

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {c : ContractionSituation B S hS} (h : ClosedImmersionData c)

/-- The object `S` of the site over `S`. -/
abbrev baseObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- There is an object `R` of the site with a closed immersion `R ⟶ baseObj` whose kernel is
the ideal sheaf `idealSheaf`. -/
theorem exists_closedImmersion :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ baseObj (hS := hS)),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        ((BigFppfOver.toScheme B S hS).map j).ker = h.idealSheaf :=
  Space.exists_closedImmersion_ker_eq B S hS baseObj h.idealSheaf

/-- The closed subscheme `X ⊆ S` cut out by the ideal sheaf. -/
noncomputable def closedObj : BigFppfOver B S hS := h.exists_closedImmersion.choose

/-- The closed immersion `X ⟶ S` of the closed subscheme `closedObj`. -/
noncomputable def closedHom : h.closedObj ⟶ baseObj (hS := hS) :=
  h.exists_closedImmersion.choose_spec.choose

/-- The morphism `closedHom` is a closed immersion of schemes. -/
theorem isClosedImmersion_closedHom :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h.closedHom) :=
  h.exists_closedImmersion.choose_spec.choose_spec.1

/-- The kernel of `closedHom` is the ideal sheaf `idealSheaf`. -/
theorem ker_closedHom : ((BigFppfOver.toScheme B S hS).map h.closedHom).ker = h.idealSheaf :=
  h.exists_closedImmersion.choose_spec.choose_spec.2

/-- `X` as a subfunctor of the terminal presheaf. -/
noncomputable def subspace : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  Subfunctor.range (yoneda.map h.closedHom ≫ terminal.from (yoneda.obj baseObj))

/-- The structure morphism of an object of the site, as a morphism to `baseObj`. -/
def toBase (V : BigFppfOver B S hS) : V ⟶ baseObj (hS := hS) := Over.homMk V.hom

/-- **An object of the site lies in `X` exactly when its structure morphism kills the ideal
sheaf.** -/
theorem nonempty_subspace_iff (V : BigFppfOver B S hS) :
    Nonempty (h.subspace.toFunctor.obj (Opposite.op V)) ↔
      h.idealSheaf ≤ ((BigFppfOver.toScheme B S hS).map (toBase V)).ker := by
  rw [← h.ker_closedHom, ← Space.mem_range_yoneda_map_iff B S hS h.closedHom
    h.isClosedImmersion_closedHom]
  constructor
  · rintro ⟨⟨t, r, -⟩⟩
    refine ⟨r, ?_⟩
    change r ≫ h.closedHom = toBase V
    apply Over.OverMorphism.ext
    have h1 := Over.w (r ≫ h.closedHom)
    simp only [baseObj, Over.mk_hom] at h1
    simpa [toBase] using h1
  · rintro ⟨r, -⟩
    exact ⟨⟨_, r, rfl⟩⟩

/-- The subfunctor `subspace` is a closed subspace of the terminal presheaf. -/
theorem isClosedSubspace_subspace : Space.IsClosedSubspace B S hS h.subspace := by
  have hj : Space.IsClosedImmersion B S hS (yoneda.map h.closedHom) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) h.closedHom).2 h.isClosedImmersion_closedHom
  have hiso : IsIso (terminal.from (yoneda.obj (baseObj (hS := hS)))) :=
    ⟨⟨(Over.mkIdTerminal.isTerminalObj yoneda _).from _,
      (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _, terminal.hom_ext _ _⟩⟩
  exact Space.isClosedSubspace_range_of_isClosedImmersion B S hS _
    (isAlgebraicSpace_yoneda B S hS _)
    (Space.isClosedImmersion_comp B S hS _ _ hj (Space.isClosedImmersion_of_isIso B S hS _))

/-- The open immersion of the chart of `U` into `S`, typed on the chart's underlying scheme. -/
noncomputable def chartToS (U : S.affineOpens) :
    (BigFppfOver.toScheme B S hS).obj (chartOf (hS := hS) U) ⟶ S :=
  (Stacks.RelativeProj.isAffineOpen U).fromSpec

/-- The morphism `chartToS U` is an open immersion. -/
instance (U : S.affineOpens) : IsOpenImmersion (chartToS (hS := hS) U) :=
  inferInstanceAs (IsOpenImmersion (Stacks.RelativeProj.isAffineOpen U).fromSpec)

/-- The structure morphism of `V` factors as the morphism `v` to the chart of `U` followed by
`chartToS U`. -/
theorem toScheme_map_toBase {U : S.affineOpens} {V : BigFppfOver B S hS}
    (v : V ⟶ chartOf (hS := hS) U) :
    (BigFppfOver.toScheme B S hS).map (toBase V) =
      (BigFppfOver.toScheme B S hS).map v ≫ chartToS U := by
  have := congrArg (fun φ => B.inclusion.map φ) (Over.w v)
  simp only [Functor.map_comp] at this
  exact this.symm

/-- The image of `Spec Γ(S, U) ⟶ S` is the affine open `U`. -/
theorem image_top_fromSpec (U : S.affineOpens) :
    (Stacks.RelativeProj.isAffineOpen U).fromSpec ''ᵁ ⊤ = (U : S.Opens) := by
  rw [Scheme.Hom.image_top_eq_opensRange, IsAffineOpen.opensRange_fromSpec]

/-- The presheaf of a scheme sends any endomorphism of `⊤` to the identity. -/
private theorem presheaf_map_top_op (X : Scheme.{u})
    (g : Opposite.op (⊤ : X.Opens) ⟶ Opposite.op ⊤) :
    X.presheaf.map g = 𝟙 _ := by
  rw [show g = 𝟙 _ from Quiver.Hom.unop_inj (Subsingleton.elim _ _),
    CategoryTheory.Functor.map_id]

/-- The comparison of the two identifications of `Γ(Spec Γ(S, U), ⊤)` with `Γ(S, U)`. -/
theorem appIso_hom_res (U : S.affineOpens) (a : Γ(S, U)) :
    ((Stacks.RelativeProj.isAffineOpen U).fromSpec.appIso ⊤).hom
        (S.presheaf.map (eqToHom (image_top_fromSpec U)).op a) =
      (Scheme.ΓSpecIso Γ(S, U)).inv a := by
  rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (S.presheaf.map _), Scheme.Hom.naturality, CommRingCat.comp_apply,
    IsAffineOpen.fromSpec_app_self_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  rw [presheaf_map_top_op]
  rfl

/-- **The points of `X` over an affine chart.** An affine object `V` with a morphism `v` to the
chart of an affine open `U` lies in `X` exactly when `v` kills the ideal attached to `U`. -/
theorem kills_iff (U : S.affineOpens) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U) :
    h.idealSheaf ≤ ((BigFppfOver.toScheme B S hS).map (toBase V)).ker ↔
      c.intrinsicIdeal h.Z U ≤ RingHom.ker (FormalSpace.chartRing v) := by
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map v) := inferInstance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartOf (hS := hS) U)) :=
    inferInstanceAs (IsAffine (Spec Γ(S, U)))
  rw [toScheme_map_toBase v, Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.ker_of_isAffine]
  set K := RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom
  have key : ∀ I : ((BigFppfOver.toScheme B S hS).obj (chartOf (hS := hS) U)).IdealSheafData,
      I ≤ Scheme.IdealSheafData.ofIdealTop K ↔ I.ideal ⟨⊤, isAffineOpen_top _⟩ ≤ K := by
    intro I
    have htop : (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top _⟩ = K := by
      rw [Scheme.IdealSheafData.ofIdealTop_ideal]
      change K.map (((BigFppfOver.toScheme B S hS).obj (chartOf (hS := hS) U)).presheaf.map
        (homOfLE le_top).op).hom = K
      rw [presheaf_map_top_op]
      exact Ideal.map_id K
    constructor
    · intro hI
      exact (hI ⟨⊤, isAffineOpen_top _⟩).trans htop.le
    · intro hI
      exact Scheme.IdealSheafData.le_of_isAffine (hI.trans htop.ge)
  rw [key, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let res := S.presheaf.map (eqToHom (image_top_fromSpec U)).op
  have hres : Function.Bijective res := ConcreteCategory.bijective_of_isIso res
  have hU'' : h.idealSheaf.ideal ⟨chartToS (hS := hS) U ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion _⟩ = (h.idealSheaf.ideal U).map res.hom :=
    (Scheme.IdealSheafData.map_ideal' (U := ⟨chartToS (hS := hS) U ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion _⟩) (V := U) h.idealSheaf
      (eqToHom (image_top_fromSpec U)).op).symm
  have hφ : ∀ a : Γ(S, U), ((chartToS (hS := hS) U).appIso ⊤).inv
      ((Scheme.ΓSpecIso Γ(S, U)).inv a) = res a := fun a => by
    have := congrArg ((Stacks.RelativeProj.isAffineOpen U).fromSpec.appIso ⊤).inv
      (appIso_hom_res U a)
    rw [Iso.hom_inv_id_apply] at this
    exact this.symm
  rw [hU'']
  constructor
  · intro hL a ha
    have hx : (Scheme.ΓSpecIso Γ(S, U)).inv a ∈ ((c.intrinsicIdeal h.Z U).map res.hom).comap
        ((chartToS (hS := hS) U).appIso ⊤).inv.hom := by
      refine Ideal.mem_comap.2 ?_
      have := Ideal.mem_map_of_mem res.hom ha
      rw [← hφ a] at this
      exact this
    exact hL hx
  · intro hR x hx
    replace hx := Ideal.mem_comap.1 hx
    have hinv : (Scheme.ΓSpecIso Γ(S, U)).inv ((Scheme.ΓSpecIso Γ(S, U)).hom x) = x :=
      Iso.hom_inv_id_apply _ x
    have hφx : ((chartToS (hS := hS) U).appIso ⊤).inv x = res ((Scheme.ΓSpecIso Γ(S, U)).hom x) :=
      (congrArg (((chartToS (hS := hS) U).appIso ⊤).inv).hom hinv.symm).trans (hφ _)
    rw [hφx] at hx
    have hmem : (Scheme.ΓSpecIso Γ(S, U)).hom x ∈ h.idealSheaf.ideal U := by
      have e := Ideal.comap_map_of_bijective res.hom hres (I := h.idealSheaf.ideal U)
      rw [← e]
      exact Ideal.mem_comap.2 hx
    have h0 := RingHom.mem_ker.1 (hR hmem)
    apply RingHom.mem_ker.2
    exact (congrArg (((BigFppfOver.toScheme B S hS).map v).appTop).hom hinv).symm.trans h0

end AlgebraicGeometry.Artin.ContractionSituation.ClosedImmersionData
