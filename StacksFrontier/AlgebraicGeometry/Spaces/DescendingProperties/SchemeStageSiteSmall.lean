module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenSubspaceOfRepr
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations

/-!
# Being a scheme descends to a finite stage, under the site-containment hypothesis

Stacks 07SR in the form whose hypothesis is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`:
if the limit of a directed system of quasi-compact and quasi-separated algebraic spaces with affine
transition maps is a scheme, then so is some stage.

## Main results

In namespace `AlgebraicGeometry.Space`:

* `exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_isSiteSmall`: an open subspace
  of a stage whose inverse image in the limit is affine is affine at some later stage, for a system
  small for the site.
* `DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`: if the limit is a scheme
  then so is some stage, for a system small for the site.
* `exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_siteContainsBaseChangeLimits`:
  the first statement under `SiteContainsBaseChangeLimits`.
* `DescentSituation.exists_isRepresentable_system_obj_of_siteContainsBaseChangeLimits`:
  Stacks 07SR, the second statement under `SiteContainsBaseChangeLimits`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The appeal to Stacks 07SQ -/

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **An open subspace of a stage with affine inverse image in the limit is affine at some later
stage.** Let `D` be a directed inverse system of quasi-compact and quasi-separated algebraic spaces
over `S` with affine transition morphisms, small for the site in the sense of `IsSiteSmall`, let
`V` be a quasi-compact open subspace of the stage `i₀`, and suppose the inverse image of `V` in
`limit D` is an affine algebraic space. Then the inverse image of `V` in the stage `j` is affine
for some `j ≥ i₀`. -/
theorem exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_isSiteSmall
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (hb : IsSiteSmall B S hS D) (i₀ : I) (V : Subfunctor (D.obj (op i₀)))
    (hV : IsOpenSubspace B S hS V) (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hW : IsAffineSpace B S hS (V.preimage (limit.π D (op i₀))).toFunctor) :
    ∃ (j : I) (hj : i₀ ≤ j),
      IsAffineSpace B S hS (V.preimage (D.map (homOfLE hj).op)).toFunctor := by
  classical
  have _ : Nonempty I := ⟨i₀⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have _ : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have _ : IsDirected (LimitTail I i₀) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i₀).functor ⋙ Over.forget (op i₀)
  have _ : G.Initial := by dsimp only [G]; infer_instance
  let cg : Cone (G ⋙ D) := (limit.cone D).whisker G
  have hcg : IsLimit cg :=
    (Functor.Initial.isLimitWhiskerEquiv G (limit.cone D)).symm (limit.isLimit D)
  let τ : (G ⋙ D) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (D.obj (op i₀)) :=
    { app := fun j => D.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ => D.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, cg.π.app j ≫ τ.app j = limit.π D (op i₀) := fun j =>
    limit.w D (homOfLE j.unop.2).op
  have hpre : ∀ j, IsOpenSubspace B S hS (V.preimage (τ.app j)) := fun j =>
    isOpenSubspace_preimage B S hS (τ.app j) V (hD (op i₀)) (hD (G.obj j)) hV
  have hfrom : ∀ j, IsAffineHom B S hS (V.fromPreimage (τ.app j)) := fun j =>
    isAffineHom_of_isPullback' B S hS (Subfunctor.isPullback_fromPreimage V (τ.app j)).flip
      (hAffine (homOfLE j.unop.2).op)
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV.1 (hQs (op i₀))
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hV.2)))
  have hbE : IsSiteSmall B S hS (Subfunctor.preimageDiagram τ V) := by
    rcases hb with ⟨hSize, _⟩ | hmono
    · exact .of_lt_cof_op (((Cardinal.mk_subtype_le _).trans
        (Cardinal.mk_congr (Opposite.equivToOpposite (α := I))).le).trans_lt hSize)
    refine .of_mono ?_
    intro a b φ
    have _ : Mono ((G ⋙ D).map φ) := hmono (G.map φ)
    exact (Subfunctor.isPullback_preimageDiagram_map τ V φ).mono_fst_of_mono
  let E : DescentSituation B S hS hZ (LimitTail I i₀) :=
    { system := Subfunctor.preimageDiagram τ V
      algebraicSpace := fun j => (hpre (op j)).1
      transition_affine := fun {_ _} φ =>
        isAffineHom_of_isPullback' B S hS
          (Subfunctor.isPullback_preimageDiagram_map τ V φ).flip (hAffine (G.map φ))
      quasiCompact := fun j =>
        isQuasiCompactSpace_source_of_isQuasiCompact B S hS hV.1 hVqc
          (isQuasiCompact_of_isAffineHom' B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      quasiSeparated := fun j =>
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hpre (op j)).1 hVqs
          (isQuasiSeparated_of_isAffineHom B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      limitCone := Subfunctor.preimageCone τ V hσ
      isLimit := Subfunctor.isLimitPreimageCone τ V hσ hcg
      limitAlgebraicSpace := hW.isAlgebraicSpace
      base := ⟨i₀, le_rfl⟩ }
  obtain ⟨j, -, hj⟩ := E.exists_isAffineSpace_system_obj_of_isSiteSmall hbE hW
  exact ⟨j.1, j.2, hj⟩

/-! ### Stacks 07SR -/

namespace DescentSituation

variable {B S hS hZ}

/-- **Stacks 07SR.** In the situation of Stacks 084R — a directed inverse system of quasi-compact
and quasi-separated algebraic spaces over `S` with affine transition morphisms, together with a
chosen limit `X` — if `X` is a scheme then there is a stage `X_i` which is a scheme, provided the
system is small for the site in the sense of `IsSiteSmall`: its index set has cardinality below the
cofinality of the site's size cutoff, or its transition morphisms are monomorphisms. -/
theorem exists_isRepresentable_system_obj_of_isSiteSmall {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hb : IsSiteSmall B S hS D.system)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, (D.system.obj (op i)).IsRepresentable := by
  classical
  have _ : Nonempty I := ⟨D.base⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.system.obj a) := fun a =>
    D.algebraicSpace a.unop
  have hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.system.map f) := fun f =>
    D.transition_affine f
  have hQc : ∀ a : Iᵒᵖ, IsQuasiCompactSpace B S hS (D.system.obj a) := fun a =>
    D.quasiCompact a.unop
  have hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.system.obj a) := fun a =>
    D.quasiSeparated a.unop
  let e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  have _ : D.limitCone.pt.IsRepresentable := hX
  have _ : (limit D.system).IsRepresentable := isRepresentable_of_natIso _ e
  have key : ∀ x : points B S hS (limit D.system), ∃ a : Iᵒᵖ,
      pointsMap B S hS (limit D.system) (limit.π D.system a) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.system.obj a)).toFunctor
          (schematicLocus B S hS (D.system.obj a)).ι) := by
    intro x
    obtain ⟨U, hU⟩ := exists_affineOpen_mem_openSubspaceOfRepr B S hS x
    set W : Subfunctor (limit D.system) :=
      openSubspaceOfRepr B S hS (limit D.system) U.1 with hWdef
    have hWopen : IsOpenSubspace B S hS W := isOpenSubspace_openSubspaceOfRepr B S hS U.1
    have hWaff : IsAffineSpace B S hS W.toFunctor := isAffineSpace_openSubspaceOfRepr B S hS U
    obtain ⟨b, V, hV, hVqc, hVpre⟩ :=
      exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isSiteSmall
        B S hS D.system hb hD hAffine W hWopen hWaff.isQuasiCompactSpace
    obtain ⟨j, hj, hjaff⟩ :=
      exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_isSiteSmall
        B S hS hZ D.system hD hAffine hQs hb b.unop V hV hVqc (by rw [hVpre]; exact hWaff)
    set P : Subfunctor (D.system.obj (op j)) :=
      V.preimage (D.system.map (homOfLE hj).op) with hPdef
    have hjrep : P.toFunctor.IsRepresentable := by
      obtain ⟨T, -, ⟨eT⟩⟩ := hjaff
      exact isRepresentable_of_natIso (yoneda.obj T) eT.symm
    refine ⟨op j, range_pointsMap_ι_le_schematicLocus B S hS P
      (isOpenSubspace_preimage B S hS _ V (hD _) (hD _) hV) hjrep ?_⟩
    have hcomp : P.preimage (limit.π D.system (op j)) = W := by
      rw [hPdef, ← Subfunctor.preimage_comp, limit.w D.system (homOfLE hj).op, hVpre]
    have hx : x ∈ Set.range (pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
        (P.preimage (limit.π D.system (op j))).ι) := by
      rw [hcomp]; exact hU
    obtain ⟨y, rfl⟩ := hx
    refine ⟨pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j))) y, ?_⟩
    change (pointsMap B S hS P.toFunctor P.ι ∘
        pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j)))) y =
      (pointsMap B S hS (limit D.system) (limit.π D.system (op j)) ∘
        pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
          (P.preimage (limit.π D.system (op j))).ι) y
    rw [← pointsMap_comp, ← pointsMap_comp, Subfunctor.fromPreimage_ι]
  obtain ⟨a, ha⟩ :=
    exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_isSiteSmall B S hS D.system
      hb hD hAffine hQc key
  exact ⟨a.unop, ha⟩

end DescentSituation

/-! ### Stacks 07SR under the chapter's standing convention -/

/-- **An open subspace of a stage with affine inverse image in the limit is affine at some later
stage, under the chapter's standing convention.** Let `D` be a directed inverse system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms and
chosen limit cone `c`, satisfying the convention `SiteContainsBaseChangeLimits` of Section 70.2
(tag 07SD), let `V` be a quasi-compact open subspace of the stage `i₀`, and suppose the inverse
image of `V` in the limit is an affine algebraic space. Then the inverse image of `V` in the stage
`j` is affine for some `j ≥ i₀`. -/
theorem
    exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_siteContainsBaseChangeLimits
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (hc : IsLimit c)
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.obj a))
    (hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.map f))
    (hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj a))
    (i₀ : I) (V : Subfunctor (D.obj (op i₀)))
    (hV : IsOpenSubspace B S hS V) (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hW : IsAffineSpace B S hS (V.preimage (c.π.app (op i₀))).toFunctor) :
    ∃ (j : I) (hj : i₀ ≤ j),
      IsAffineSpace B S hS (V.preimage (D.map (homOfLE hj).op)).toFunctor := by
  classical
  have _ : Nonempty I := ⟨i₀⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have _ : Nonempty (LimitTail I i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have _ : IsDirected (LimitTail I i₀) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i₀)ᵒᵖ ⥤ Iᵒᵖ := limitTailForget i₀
  have _ : G.Initial := by dsimp only [G, limitTailForget]; infer_instance
  let cg : Cone (G ⋙ D) := c.whisker G
  have hcg : IsLimit cg := (Functor.Initial.isLimitWhiskerEquiv G c).symm hc
  let τ : (G ⋙ D) ⟶ (Functor.const ((LimitTail I i₀)ᵒᵖ)).obj (D.obj (op i₀)) :=
    { app := fun j => D.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ op i₀ => D.map x) (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, cg.π.app j ≫ τ.app j = c.π.app (op i₀) := fun j =>
    c.w (homOfLE j.unop.2).op
  have hpre : ∀ j, IsOpenSubspace B S hS (V.preimage (τ.app j)) := fun j =>
    isOpenSubspace_preimage B S hS (τ.app j) V (hD (op i₀)) (hD (G.obj j)) hV
  have hfrom : ∀ j, IsAffineHom B S hS (V.fromPreimage (τ.app j)) := fun j =>
    isAffineHom_of_isPullback' B S hS (Subfunctor.isPullback_fromPreimage V (τ.app j)).flip
      (hAffine (homOfLE j.unop.2).op)
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV.1 (hQs (op i₀))
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hV.2)))
  let E : DescentSituation B S hS hZ (LimitTail I i₀) :=
    { system := Subfunctor.preimageDiagram τ V
      algebraicSpace := fun j => (hpre (op j)).1
      transition_affine := fun {_ _} φ =>
        isAffineHom_of_isPullback' B S hS
          (Subfunctor.isPullback_preimageDiagram_map τ V φ).flip (hAffine (G.map φ))
      quasiCompact := fun j =>
        isQuasiCompactSpace_source_of_isQuasiCompact B S hS hV.1 hVqc
          (isQuasiCompact_of_isAffineHom' B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      quasiSeparated := fun j =>
        isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hpre (op j)).1 hVqs
          (isQuasiSeparated_of_isAffineHom B S hS (V.fromPreimage (τ.app (op j)))
            (hpre (op j)).1 hV.1 (hfrom (op j)))
      limitCone := Subfunctor.preimageCone τ V hσ
      isLimit := Subfunctor.isLimitPreimageCone τ V hσ hcg
      limitAlgebraicSpace := hW.isAlgebraicSpace
      base := ⟨i₀, le_rfl⟩ }
  have hconvE : SiteContainsBaseChangeLimits B S hS E.system :=
    SiteContainsBaseChangeLimits.preimageDiagram G τ V hAffine hconv
  obtain ⟨j, -, hj⟩ := E.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits hconvE hW
  exact ⟨j.1, j.2, hj⟩

namespace DescentSituation

variable {B S hS hZ}

/-- In the situation of Stacks 084R — a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over `S` with affine transition morphisms, together with a chosen
limit `X`, under the convention of Section 70.2 (tag 07SD) that the rings the chapter forms have
their spectra in the big fppf site — if `X` is a scheme then there is a stage `X_i` which is a
scheme. Nothing is asked of the index set beyond directedness. -/
@[stacks 07SR]
theorem exists_isRepresentable_system_obj_of_siteContainsBaseChangeLimits {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, (D.system.obj (op i)).IsRepresentable := by
  classical
  have _ : Nonempty I := ⟨D.base⟩
  have _ : IsCofiltered Iᵒᵖ := inferInstance
  have hD : ∀ a : Iᵒᵖ, IsAlgebraicSpace B S hS (D.system.obj a) := fun a =>
    D.algebraicSpace a.unop
  have hAffine : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsAffineHom B S hS (D.system.map f) := fun f =>
    D.transition_affine f
  have hQc : ∀ a : Iᵒᵖ, IsQuasiCompactSpace B S hS (D.system.obj a) := fun a =>
    D.quasiCompact a.unop
  have hQs : ∀ a : Iᵒᵖ, IsAbsolutelyQuasiSeparated B S hS hZ (D.system.obj a) := fun a =>
    D.quasiSeparated a.unop
  let e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  have hlim : IsAlgebraicSpace B S hS (limit D.system) := D.limitAlgebraicSpace.of_iso e
  have _ : D.limitCone.pt.IsRepresentable := hX
  have _ : (limit D.system).IsRepresentable := isRepresentable_of_natIso _ e
  have key : ∀ x : points B S hS (limit D.system), ∃ a : Iᵒᵖ,
      pointsMap B S hS (limit D.system) (limit.π D.system a) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.system.obj a)).toFunctor
          (schematicLocus B S hS (D.system.obj a)).ι) := by
    intro x
    obtain ⟨U, hU⟩ := exists_affineOpen_mem_openSubspaceOfRepr B S hS x
    set W : Subfunctor (limit D.system) :=
      openSubspaceOfRepr B S hS (limit D.system) U.1 with hWdef
    have hWopen : IsOpenSubspace B S hS W := isOpenSubspace_openSubspaceOfRepr B S hS U.1
    have hWaff : IsAffineSpace B S hS W.toFunctor := isAffineSpace_openSubspaceOfRepr B S hS U
    obtain ⟨b, V, hV, hVqc, hVpre⟩ :=
      exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_siteContainsBaseChangeLimits
        B S hS D.system hconv hlim hD hAffine W hWopen hWaff.isQuasiCompactSpace
    obtain ⟨j, hj, hjaff⟩ :=
      exists_isAffineSpace_preimage_of_isAffineSpace_preimage_limit_of_siteContainsBaseChangeLimits
        B S hS hZ D.system (limit.cone D.system) (limit.isLimit D.system) hconv hD hAffine hQs
        b.unop V hV hVqc (by rw [limit.cone_π, hVpre]; exact hWaff)
    set P : Subfunctor (D.system.obj (op j)) :=
      V.preimage (D.system.map (homOfLE hj).op) with hPdef
    have hjrep : P.toFunctor.IsRepresentable := by
      obtain ⟨T, -, ⟨eT⟩⟩ := hjaff
      exact isRepresentable_of_natIso (yoneda.obj T) eT.symm
    refine ⟨op j, range_pointsMap_ι_le_schematicLocus B S hS P
      (isOpenSubspace_preimage B S hS _ V (hD _) (hD _) hV) hjrep ?_⟩
    have hcomp : P.preimage (limit.π D.system (op j)) = W := by
      rw [hPdef, ← Subfunctor.preimage_comp, limit.w D.system (homOfLE hj).op, hVpre]
    have hx : x ∈ Set.range (pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
        (P.preimage (limit.π D.system (op j))).ι) := by
      rw [hcomp]; exact hU
    obtain ⟨y, rfl⟩ := hx
    refine ⟨pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j))) y, ?_⟩
    change (pointsMap B S hS P.toFunctor P.ι ∘
        pointsMap B S hS _ (P.fromPreimage (limit.π D.system (op j)))) y =
      (pointsMap B S hS (limit D.system) (limit.π D.system (op j)) ∘
        pointsMap B S hS (P.preimage (limit.π D.system (op j))).toFunctor
          (P.preimage (limit.π D.system (op j))).ι) y
    rw [← pointsMap_comp, ← pointsMap_comp, Subfunctor.fromPreimage_ι]
  obtain ⟨a, ha⟩ :=
    exists_isRepresentable_obj_of_forall_mem_schematicLocus_of_siteContainsBaseChangeLimits
      B S hS D.system hconv hlim hD hAffine hQc key
  exact ⟨a.unop, ha⟩

end DescentSituation

end AlgebraicGeometry.Space

end
