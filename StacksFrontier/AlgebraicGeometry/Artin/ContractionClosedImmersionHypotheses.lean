module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionSubspace
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase

/-!
# The closed subspace of Stacks 0GHE has the right open part and completion

Let `X ⊆ S` be the closed subspace cut out by the glued ideal sheaf
(`AlgebraicGeometry.Artin.ContractionSituation.ClosedImmersionData.subspace`). This file checks
the hypotheses of `AlgebraicGeometry.Artin.ContractionSituation.solution_of_isClosedSubspace`
for `X`: `X' → S` factors through `X`, `X ∩ (S ∖ Z)` is the image of `U'`, and there are
morphisms in both directions between `W` and the completion `X_{/T}`.

All the sheaves in sight have subsingleton values, so each statement is a statement about which
objects of the site carry a section, and it is checked locally: on the affine opens of an object
lying over affine opens of `S` ("to find `X` is clearly a local question on `S`"), where the
four point properties of the ideal `J_U` and the Krull argument apply.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Local nonemptiness of subsingleton sheaves -/

/-- A sheaf with subsingleton values has a section over an object as soon as it has one over
every member of a covering sieve. -/
theorem nonempty_of_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hsub : ∀ V, Subsingleton (F.obj V)) {V : BigFppfOver B S hS} (R : Sieve V)
    (hR : R ∈ BigFppfOver.topology B S hS V)
    (h : ∀ ⦃V' : BigFppfOver B S hS⦄ (g : V' ⟶ V), R g → Nonempty (F.obj (Opposite.op V'))) :
    Nonempty (F.obj (Opposite.op V)) := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 hF R hR
  let x : Presieve.FamilyOfElements F R.arrows := fun _ g hg => (h g hg).some
  have hxc : x.Compatible := fun _ _ _ _ _ _ _ _ _ _ => (hsub _).elim _ _
  exact ⟨(hsheaf x hxc).choose⟩

/-- A sheaf with subsingleton values has a section over an object as soon as it has one over
every affine open of it lying over an affine open of `S`. -/
theorem nonempty_of_affineSubordinateCover {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hsub : ∀ V, Subsingleton (F.obj V)) (V : BigFppfOver B S hS)
    (h : ∀ i : (BigFppfOver.affineSubordinateCover B S hS V).I₀,
      Nonempty (F.obj (Opposite.op ((BigFppfOver.affineSubordinateCover B S hS V).X i)))) :
    Nonempty (F.obj (Opposite.op V)) := by
  refine nonempty_of_mem_topology hF hsub _
    (BigFppfOver.mem_topology_sieve₀_affineSubordinateCover B S hS V) ?_
  rintro V' _ ⟨_, k, _, ⟨i⟩, rfl⟩
  exact ⟨F.map k.op (h i).some⟩

/-- A morphism of sheaves into a sheaf with subsingleton values exists as soon as the target
has a section wherever the source has one. -/
theorem nonempty_hom_of_nonempty {F G : Sheaf (BigFppfOver.topology B S hS) (Type w)}
    (hsub : ∀ V, Subsingleton (G.obj.obj V))
    (h : ∀ V, F.obj.obj V → Nonempty (G.obj.obj V)) : Nonempty (F ⟶ G) :=
  ⟨ObjectProperty.homMk
    { app := fun V => ↾fun x => (h V x).some
      naturality := fun _ _ _ => by ext; exact (hsub _).elim _ _ }⟩

/-- The source of a monomorphism of presheaves has subsingleton values where the target does. -/
private theorem subsingleton_obj_of_mono_app {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (f : F ⟶ G) [Mono f] (V : (BigFppfOver B S hS)ᵒᵖ) [Subsingleton (G.obj V)] :
    Subsingleton (F.obj V) :=
  ((mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance V)).subsingleton

/-- A sheaf with a monomorphism to the completion `S_{/Z}` has subsingleton values. -/
theorem subsingleton_obj_of_mono_completionSheaf_terminal
    {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (w : W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z) [Mono w]
    (V : (BigFppfOver B S hS)ᵒᵖ) : Subsingleton (W.obj.obj V) := by
  let j := w ≫ Space.completionSheafInclusion B S hS _ Z
  have := Space.mono_completionSheafInclusion B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z
  have : Mono j := mono_comp _ _
  have : Mono j.hom := (sheafToPresheaf _ _).map_mono j
  let e := (BigFppfOver.topology B S hS).isoSheafify
    (isSheaf_terminal_comp_uliftFunctor (B := B) (S := S) (hS := hS))
  have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) V
  have : Subsingleton (((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⋙ uliftFunctor.{u + 1}).obj V) :=
    ⟨fun a b => ULift.ext (Subsingleton.elim _ _)⟩
  have : Subsingleton ((Space.sheafifiedULift B S hS
      (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))).obj.obj V) :=
    Equiv.subsingleton (e.app V).symm.toEquiv
  exact subsingleton_obj_of_mono_app j.hom V

/-! ### Points of objects of the site in `|S|` -/

/-- Restricting along a morphism of the site shrinks the image in `|S|`. -/
theorem range_pointsMap_terminal_subset {V' V : BigFppfOver B S hS} (g : V' ⟶ V) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V') (terminal.from (yoneda.obj V'))) ⊆
      Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨Space.pointsMap B S hS _ (yoneda.map g) p, ?_⟩
  rw [← Function.comp_apply (f := Space.pointsMap B S hS _ (terminal.from (yoneda.obj V))),
    ← Space.pointsMap_comp]
  congr 1
  exact terminal.hom_ext _ _

/-- The image in `|S|` of the points of a section of a presheaf over `S`. -/
theorem pointsMap_terminal_pointsMap {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : P ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {V : BigFppfOver B S hS} (x : P.obj (Opposite.op V))
    (p : Space.points B S hS (yoneda.obj V)) :
    Space.pointsMap B S hS P φ
        (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x) p) =
      Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V)) p := by
  rw [← Function.comp_apply (f := Space.pointsMap B S hS P φ),
    ← Space.pointsMap_comp]
  congr 1
  exact terminal.hom_ext _ _

/-- A section of the completion `X_{/T}` exists, locally, only over objects carrying a section
of `X` with points in `T`. -/
theorem exists_cover_of_completionSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS X)) {V : BigFppfOver B S hS}
    (s : (Space.completionSheaf B S hS X T).obj.obj (Opposite.op V)) :
    ∃ R : Sieve V, R ∈ BigFppfOver.topology B S hS V ∧
      ∀ ⦃V' : BigFppfOver B S hS⦄ (g : V' ⟶ V), R g →
        ∃ x : X.obj (Opposite.op V'),
          Set.range (Space.pointsMap B S hS (yoneda.obj V') (yonedaEquiv.symm x)) ⊆ T := by
  let P := (Space.completionSubfunctor B S hS X T).toFunctor
  refine ⟨Presheaf.imageSieve ((BigFppfOver.topology B S hS).toSheafify P) s,
    Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify P) s, ?_⟩
  rintro V' g ⟨t, -⟩
  exact ⟨t.1.down, (Space.hasImageIn_iff_range_subset B S hS T _ _).1 t.2⟩

/-- A section of `X` with points in `T` gives a section of the completion `X_{/T}`. -/
theorem nonempty_completionSheaf_of_range_subset {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (Space.points B S hS X)} {V : BigFppfOver B S hS} (x : X.obj (Opposite.op V))
    (hx : Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x)) ⊆ T) :
    Nonempty ((Space.completionSheaf B S hS X T).obj.obj (Opposite.op V)) :=
  ⟨((BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS X T).toFunctor).app (Opposite.op V)
    ⟨ULift.up x, (Space.hasImageIn_iff_range_subset B S hS T _ _).2 hx⟩⟩

/-- A subfunctor of the terminal presheaf contains every section over an object over which it
has a section. -/
theorem mem_of_nonempty (G : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    {V : (BigFppfOver B S hS)ᵒᵖ} (s : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj V)
    (h : Nonempty (G.toFunctor.obj V)) : s ∈ G.obj V := by
  obtain ⟨y⟩ := h
  have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) V
  rw [Subsingleton.elim s y.1]
  exact y.2

/-! ### Affine opens lying over affine opens of `S` -/

/-- An object of the site whose image lies in an affine open `U` of `S` has its image in the
range of the open immersion of the chart of `U` into `S`. -/
theorem range_subset_range_chartToS (U : S.affineOpens) (V : BigFppfOver B S hS)
    (hV : Set.range V.hom.hom ⊆ ((U : S.Opens) : Set S)) :
    Set.range V.hom.hom ⊆ Set.range (ClosedImmersionData.chartToS (hS := hS) U) := fun x hx => by
  have hxU : x ∈ ((U : S.Opens) : Set S) := hV hx
  rwa [← (Stacks.RelativeProj.isAffineOpen U).range_fromSpec] at hxU

/-- An object of the site whose image lies in an affine open `U` of `S` maps to the chart
of `U`. -/
noncomputable def chartLift (U : S.affineOpens) (V : BigFppfOver B S hS)
    (hV : Set.range V.hom.hom ⊆ ((U : S.Opens) : Set S)) : V ⟶ chartOf (hS := hS) U :=
  Over.homMk (U := V) (V := chartOf (hS := hS) U)
    (ObjectProperty.homMk (X := V.left) (Y := (chartOf (hS := hS) U).left)
      (IsOpenImmersion.lift (ClosedImmersionData.chartToS U)
      V.hom.hom (range_subset_range_chartToS U V hV)))
    (by apply ObjectProperty.hom_ext; exact IsOpenImmersion.lift_fac _ _ _)

section Member

variable (V : BigFppfOver B S hS) (i : (BigFppfOver.affineSubordinateCover B S hS V).I₀)

/-- Each member of the affine subordinate cover of an object is affine. -/
instance isAffine_affineSubordinateCover_X :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigFppfOver.affineSubordinateCover B S hS V).X i)) :=
  i.down.1.2

/-- Each member of the affine subordinate cover of an object has its image in the affine open
of `S` attached to it. -/
theorem range_affineSubordinateCover_X_hom_subset :
    Set.range ((BigFppfOver.affineSubordinateCover B S hS V).X i).hom.hom ⊆
      ((i.down.2.1 : S.affineOpens) : Set S) := by
  rintro _ ⟨y, rfl⟩
  exact i.down.2.2 y.2

/-- The morphism from a member of the affine subordinate cover to the chart of its affine open
of `S`. -/
noncomputable def memberChart :
    (BigFppfOver.affineSubordinateCover B S hS V).X i ⟶ chartOf (hS := hS) i.down.2.1 :=
  chartLift _ _ (range_affineSubordinateCover_X_hom_subset V i)

end Member

/-- A section of a presheaf over `S` has its points in the inverse image of `Z` exactly when
its object lies over `Z`. -/
theorem range_subset_preimage_iff {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : P ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    {V : BigFppfOver B S hS} (x : P.obj (Opposite.op V)) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x)) ⊆
        Space.pointsMap B S hS P φ ⁻¹' Z ↔
      Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆ Z := by
  constructor
  · rintro hx _ ⟨p, rfl⟩
    simpa only [Set.mem_preimage, pointsMap_terminal_pointsMap] using hx ⟨p, rfl⟩
  · rintro hV _ ⟨p, rfl⟩
    rw [Set.mem_preimage, pointsMap_terminal_pointsMap]
    exact hV ⟨p, rfl⟩

namespace ClosedImmersionData

variable {c : ContractionSituation B S hS} (h : ClosedImmersionData c)

/-! ### The sheaves in sight have subsingleton values -/

/-- The closed subspace `X` is a sheaf. -/
theorem isSheaf_subspace :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) h.subspace.toFunctor :=
  h.isClosedSubspace_subspace.1.isSheaf

/-- The closed subspace `X` has subsingleton values. -/
theorem subsingleton_subspace (V : (BigFppfOver B S hS)ᵒᵖ) :
    Subsingleton (h.subspace.toFunctor.obj V) :=
  subsingleton_subfunctor_terminal_obj _ V

/-- The open subspace `U'` of `X'` is a sheaf. -/
theorem isSheaf_U' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) c.U'.toFunctor :=
  Space.isSheaf_openSubspaceOfPoints B S hS c.isAlgebraicSpace_X'.isSheaf _

include h in
/-- The open subspace `U'` of `X'` has subsingleton values. -/
theorem subsingleton_U' (V : (BigFppfOver B S hS)ᵒᵖ) : Subsingleton (c.U'.toFunctor.obj V) := by
  have hmono : Mono (h.u ≫ (Space.openSubspaceOfPoints B S hS _ h.Zᶜ).ι) := by
    have := Space.mono_of_isClosedImmersion B S hS h.u h.hu
    infer_instance
  have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) V
  exact subsingleton_obj_of_mono_app (h.u ≫ (Space.openSubspaceOfPoints B S hS _ h.Zᶜ).ι) V

include h in
/-- The formal space `W` has subsingleton values. -/
theorem subsingleton_W (V : (BigFppfOver B S hS)ᵒᵖ) : Subsingleton (c.W.obj.obj V) :=
  have := FormalSpace.mono_of_isClosedImmersion B S hS h.w h.hw
  subsingleton_obj_of_mono_completionSheaf_terminal h.Z h.w V

/-- The set `T = X ∩ Z` of points of `X`. -/
abbrev subspaceT : Set (Space.points B S hS h.subspace.toFunctor) :=
  Space.pointsMap B S hS h.subspace.toFunctor h.subspace.ι ⁻¹' h.Z

/-- The completion `X_{/T}` of `X` along `T = X ∩ Z` has subsingleton values. -/
theorem subsingleton_completion (V : (BigFppfOver B S hS)ᵒᵖ) :
    Subsingleton ((Space.completionSheaf B S hS h.subspace.toFunctor h.subspaceT).obj.obj V) :=
  have := FormalSpace.mono_of_isClosedImmersion B S hS _
    (FormalSpace.isClosedImmersion_completionSheafMap B S hS h.isClosedSubspace_subspace.1
      (Space.isAlgebraicSpace_terminal B S hS) h.subspace.ι h.Z h.isClosedSubspace_subspace.2)
  subsingleton_obj_of_mono_completionSheaf_terminal h.Z
    (Space.completionSheafMap B S hS h.subspace.ι h.Z) V

/-! ### Points over affine charts -/

/-- A good affine point over a chart lies in `X`. -/
theorem nonempty_subspace_of_isGoodPoint (U : S.affineOpens) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U)
    (hg : c.IsGoodPoint h.Z V) : Nonempty (h.subspace.toFunctor.obj (Opposite.op V)) :=
  (h.nonempty_subspace_iff V).2 ((h.kills_iff U v).2 fun a ha =>
    RingHom.mem_ker.2 ((mem_intrinsicIdeal_iff c h.Z U a).1 ha V v hg))

/-- An affine point of `X` over a chart kills `J_U`. -/
theorem chartIdeal_le_ker_of_subspace (U : S.affineOpens) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U)
    (hx : Nonempty (h.subspace.toFunctor.obj (Opposite.op V))) :
    h.chartIdeal U ≤ RingHom.ker (FormalSpace.chartRing v) :=
  (h.chartIdeal_le_intrinsicIdeal U).trans ((h.kills_iff U v).1 ((h.nonempty_subspace_iff V).1 hx))

/-- An affine point over a chart avoids `Z` exactly when it makes `I_U` the unit ideal. -/
theorem range_subset_compl_iff (U : S.affineOpens) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ chartOf (hS := hS) U) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆ h.Zᶜ ↔
      (h.zIdeal U).map (FormalSpace.chartRing v) = ⊤ := by
  rw [← FormalSpace.range_subset_compl_zeroLocusPoints_iff, h.zIdeal_spec U]
  rw [show terminal.from (yoneda.obj V) =
      yoneda.map v ≫ terminal.from (yoneda.obj (chartOf (hS := hS) U)) from terminal.hom_ext _ _,
    Space.pointsMap_comp, Set.range_comp, Set.image_subset_iff, Set.preimage_compl]

/-- A section of `X'` over an object lying over `Z` has its points in `T'`. -/
theorem range_subset_T' {V : BigFppfOver B S hS} (x : c.X'.obj (Opposite.op V))
    (hV : Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆
      h.Z) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x)) ⊆ c.T' := by
  rw [← h.hT']
  exact (range_subset_preimage_iff _ h.Z x).2 hV

/-- A section of `X'` over an object avoiding `Z` lies in `U'`. -/
theorem mem_U' {V : BigFppfOver B S hS} (x : c.X'.obj (Opposite.op V))
    (hV : Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆
      h.Zᶜ) :
    x ∈ c.U'.obj (Opposite.op V) := by
  change Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x)) ⊆ c.T'ᶜ
  rw [← h.hT', ← Set.preimage_compl]
  exact (range_subset_preimage_iff _ h.Zᶜ x).2 hV

/-- An object lying over `Z` with a section of `X'` carries a section of `W`, through `g`. -/
theorem nonempty_W_of_X' {V : BigFppfOver B S hS} (x : c.X'.obj (Opposite.op V))
    (hV : Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆
      h.Z) :
    Nonempty (c.W.obj.obj (Opposite.op V)) := by
  obtain ⟨s⟩ := nonempty_completionSheaf_of_range_subset x (h.range_subset_T' x hV)
  exact ⟨c.g.hom.app _ s⟩

/-! ### An affine object as a chart over itself -/

section SelfChart

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- An affine object `V` of the site as the chart `Spec Γ(V)`. -/
noncomputable abbrev selfChart : BigFppfOver B S hS :=
  FormalSpace.affineOver B S hS (Space.contains_specGammaTop_obj B S hS V)
    (((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom)

/-- The isomorphism `Spec Γ(V) ⟶ V`, as a morphism of the site. -/
noncomputable def selfChartHom : selfChart V ⟶ V :=
  Over.homMk (U := selfChart V) (V := V)
    (ObjectProperty.homMk (X := (selfChart V).left) (Y := V.left)
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv)
    (by apply ObjectProperty.hom_ext; rfl)

/-- On global sections, `selfChartHom V` is the inverse of the isomorphism
`Γ(Spec Γ(V)) ≅ Γ(V)`. -/
theorem selfChartHom_appTop (y : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (selfChartHom V)).appTop y =
      (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)).inv y := by
  let X := (BigFppfOver.toScheme B S hS).obj V
  change X.isoSpec.inv.appTop y = _
  have h1 : (Scheme.ΓSpecIso Γ(X, ⊤)).hom ≫ X.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
      show X.isoSpec.inv ≫ X.toSpecΓ = 𝟙 _ from X.isoSpec.inv_hom_id, Scheme.Hom.id_appTop]
  rw [(Iso.hom_comp_eq_id _).1 h1]

/-- The chart ring map of `t ≫ selfChartHom V ≫ v` is the composite of those of `v` and `t`. -/
theorem chartRing_comp_selfChartHom {U : S.affineOpens} (v : V ⟶ chartOf (hS := hS) U)
    {V' : BigFppfOver B S hS} (t : V' ⟶ selfChart V) (a : Γ(S, U)) :
    FormalSpace.chartRing (t ≫ selfChartHom V ≫ v) a =
      FormalSpace.chartRing t (FormalSpace.chartRing v a) := by
  rw [← Category.assoc, FormalSpace.chartRing_comp, Functor.map_comp, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, selfChartHom_appTop]
  rfl

end SelfChart

/-- **`X'` lies in `X` over Noetherian affine charts.** An affine object `V` with Noetherian
ring of functions, a map to the chart of an affine open `U` and a section of `X'` lies in `X`:
an element `a` of the ideal attached to `U` maps to an element of `Γ(V)` which vanishes on
every good point over `Spec Γ(V)` — the localizations at elements of `I_U` are points of `U'`,
the quotients by powers of `I_U` are points of `X'_{/T'}` hence of `W` through `g` — so it
vanishes by the Krull argument. -/
theorem nonempty_subspace_of_isAffine_of_X' (U : S.affineOpens) (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (v : V ⟶ chartOf (hS := hS) U) (x : c.X'.obj (Opposite.op V)) :
    Nonempty (h.subspace.toFunctor.obj (Opposite.op V)) := by
  refine (h.nonempty_subspace_iff V).2 ((h.kills_iff U v).2 fun a ha => ?_)
  rw [RingHom.mem_ker]
  let φ := selfChartHom V
  let ρ := FormalSpace.chartRing v
  have hcomp : ∀ {V' : BigFppfOver B S hS} (t : V' ⟶ selfChart V),
      FormalSpace.chartRing (t ≫ φ ≫ v) = (FormalSpace.chartRing t).comp ρ := fun t =>
    RingHom.ext fun b => chartRing_comp_selfChartHom V v t b
  have hZpts : ∀ (V' : BigFppfOver B S hS) (t : V' ⟶ selfChart V) (n : ℕ),
      ((h.zIdeal U).map ρ) ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing t) →
        Set.range (Space.pointsMap B S hS (yoneda.obj V') (terminal.from (yoneda.obj V'))) ⊆
          h.Z := by
    intro V' t n ht
    refine h.range_subset_of_pow_le U (t ≫ φ ≫ v) n fun b hb => ?_
    rw [hcomp, RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker]
    apply ht
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  have hmem := mem_of_forall_isGoodPoint c h.Z (hA := Space.contains_specGammaTop_obj B S hS V)
    (f := ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom)
    ((h.zIdeal U).map ρ) ⊥ hZpts
    (fun V' _ t _ ht => by
      have hmap : (h.zIdeal U).map (FormalSpace.chartRing (t ≫ φ ≫ v)) = ⊤ := by
        rwa [hcomp, ← Ideal.map_map]
      exact ⟨⟨c.X'.map (t ≫ φ).op x,
        h.mem_U' _ ((h.range_subset_compl_iff U (t ≫ φ ≫ v)).2 hmap)⟩⟩)
    (fun V' t n _ ht => h.nonempty_W_of_X' (c.X'.map (t ≫ φ).op x) (hZpts V' t n ht))
    (ρ a)
    (fun V' _ t hg => by
      have := (mem_intrinsicIdeal_iff c h.Z U a).1 ha V' (t ≫ φ ≫ v) hg
      rwa [hcomp, RingHom.comp_apply] at this)
  exact (Submodule.mem_bot _).1 hmem

/-! ### The four hypotheses of `solution_of_isClosedSubspace` -/

/-- **`X' → S` factors through `X`.** -/
theorem range_le_subspace : Subfunctor.range (terminal.from c.X') ≤ h.subspace := by
  obtain ⟨Ua, fa, hsurj, het⟩ := c.isAlgebraicSpace_X'.exists_atlas
  have := Space.isLocallySurjective_of_surjective_etale B S hS fa hsurj het
  have hN : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj Ua) :=
    c.isLocallyNoetherian_of_isLocallyOfFiniteType_base c.isLocallyOfFiniteType_X' Ua fa
      (Space.isEtale_of_presheaf_etale B S hS het)
  have hUa : Nonempty (h.subspace.toFunctor.obj (Opposite.op Ua)) := by
    refine nonempty_of_affineSubordinateCover h.isSheaf_subspace h.subsingleton_subspace Ua
      fun i => ?_
    have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
        ((BigFppfOver.affineSubordinateCover B S hS Ua).f i)) :=
      inferInstanceAs (IsOpenImmersion (i.down.1.1.ι))
    have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
        ((BigFppfOver.affineSubordinateCover B S hS Ua).X i)) :=
      isLocallyNoetherian_of_isOpenImmersion
        ((BigFppfOver.toScheme B S hS).map ((BigFppfOver.affineSubordinateCover B S hS Ua).f i))
    have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj
        ((BigFppfOver.affineSubordinateCover B S hS Ua).X i), ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    exact h.nonempty_subspace_of_isAffine_of_X' _ _ (memberChart Ua i)
      (c.X'.map ((BigFppfOver.affineSubordinateCover B S hS Ua).f i).op (yonedaEquiv fa))
  rintro ⟨V⟩ s ⟨x, rfl⟩
  apply mem_of_nonempty
  refine nonempty_of_mem_topology h.isSheaf_subspace h.subsingleton_subspace _
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) fa x) ?_
  rintro V' g ⟨t, -⟩
  exact ⟨h.subspace.toFunctor.map t.op hUa.some⟩

/-- **`X ∩ (S ∖ Z)` is the image of `U'`.** -/
theorem subspace_inf_compl :
    h.subspace ⊓ Space.openSubspaceOfPoints B S hS _ h.Zᶜ =
      Subfunctor.range (h.u ≫ (Space.openSubspaceOfPoints B S hS _ h.Zᶜ).ι) := by
  refine Subfunctor.ext (funext fun V => Set.ext fun s => ?_)
  induction V using Opposite.rec with
  | op V =>
  constructor
  · rintro ⟨hsX, hsZ⟩
    have hV : Set.range (Space.pointsMap B S hS (yoneda.obj V)
        (terminal.from (yoneda.obj V))) ⊆ h.Zᶜ := by
      have hsZ' : Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm s)) ⊆
          h.Zᶜ := hsZ
      rwa [show yonedaEquiv.symm s = terminal.from (yoneda.obj V) from terminal.hom_ext _ _]
        at hsZ'
    have hU' : Nonempty (c.U'.toFunctor.obj (Opposite.op V)) := by
      refine nonempty_of_affineSubordinateCover (isSheaf_U' (c := c)) h.subsingleton_U' V
        fun i => ?_
      let fi := (BigFppfOver.affineSubordinateCover B S hS V).f i
      let v := memberChart V i
      exact (h.chartIdeal_props _).1 _ v
        (h.chartIdeal_le_ker_of_subspace _ v ⟨h.subspace.toFunctor.map fi.op ⟨s, hsX⟩⟩)
        ((h.range_subset_compl_iff _ v).1 ((range_pointsMap_terminal_subset fi).trans hV))
    obtain ⟨y⟩ := hU'
    have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) (Opposite.op V)
    exact ⟨y, Subsingleton.elim _ _⟩
  · rintro ⟨y, rfl⟩
    refine ⟨mem_of_nonempty _ _ ?_, (h.u.app _ y).2⟩
    exact nonempty_of_affineSubordinateCover h.isSheaf_subspace h.subsingleton_subspace V
      fun i => h.nonempty_subspace_of_isGoodPoint _ (memberChart V i)
        (Or.inl ⟨c.U'.toFunctor.map ((BigFppfOver.affineSubordinateCover B S hS V).f i).op y⟩)

/-- **`W` maps to `X_{/T}`.** -/
theorem nonempty_hom_W_completion :
    Nonempty (c.W ⟶ Space.completionSheaf B S hS h.subspace.toFunctor h.subspaceT) := by
  refine nonempty_hom_of_nonempty h.subsingleton_completion fun V w0 => ?_
  induction V using Opposite.rec with
  | op V =>
  obtain ⟨R, hR, hRZ⟩ := exists_cover_of_completionSheaf _ h.Z (h.w.hom.app _ w0)
  refine nonempty_of_mem_topology (Space.completionSheaf B S hS _ h.subspaceT).property
    h.subsingleton_completion R hR fun V' g hg => ?_
  obtain ⟨x0, hx0⟩ := hRZ g hg
  have hV' : Set.range (Space.pointsMap B S hS (yoneda.obj V')
      (terminal.from (yoneda.obj V'))) ⊆ h.Z := by
    rwa [show yonedaEquiv.symm x0 = terminal.from (yoneda.obj V') from terminal.hom_ext _ _]
      at hx0
  refine nonempty_of_affineSubordinateCover
    (Space.completionSheaf B S hS _ h.subspaceT).property h.subsingleton_completion V'
    fun i => ?_
  let fi := (BigFppfOver.affineSubordinateCover B S hS V').f i
  have hViZ := (range_pointsMap_terminal_subset fi).trans hV'
  obtain ⟨xi⟩ := h.nonempty_subspace_of_isGoodPoint _ (memberChart V' i)
    (Or.inr ⟨⟨c.W.obj.map (fi ≫ g).op w0⟩, hViZ⟩)
  exact nonempty_completionSheaf_of_range_subset xi
    ((range_subset_preimage_iff h.subspace.ι h.Z xi).2 hViZ)

/-- **`X_{/T}` maps to `W`.** -/
theorem nonempty_hom_completion_W :
    Nonempty (Space.completionSheaf B S hS h.subspace.toFunctor h.subspaceT ⟶ c.W) := by
  refine nonempty_hom_of_nonempty h.subsingleton_W fun V σ => ?_
  induction V using Opposite.rec with
  | op V =>
  obtain ⟨R, hR, hRT⟩ := exists_cover_of_completionSheaf _ _ σ
  refine nonempty_of_mem_topology c.W.property h.subsingleton_W R hR fun V' g hg => ?_
  obtain ⟨x0, hx0⟩ := hRT g hg
  have hV' := (range_subset_preimage_iff h.subspace.ι h.Z x0).1 hx0
  refine nonempty_of_affineSubordinateCover c.W.property h.subsingleton_W V' fun i => ?_
  let fi := (BigFppfOver.affineSubordinateCover B S hS V').f i
  let v := memberChart V' i
  obtain ⟨n, hn⟩ := h.exists_pow_le_of_range_subset _ v
    ((range_pointsMap_terminal_subset fi).trans hV')
  exact (h.chartIdeal_props _).2.2.1 _ v n
    (h.chartIdeal_le_ker_of_subspace _ v ⟨h.subspace.toFunctor.map fi.op x0⟩) hn

end ClosedImmersionData

end AlgebraicGeometry.Artin.ContractionSituation
