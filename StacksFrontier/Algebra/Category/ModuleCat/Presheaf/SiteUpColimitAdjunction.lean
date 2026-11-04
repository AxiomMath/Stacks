module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit

/-!
# The adjunction `u_p ⊣ u^p` on presheaves of modules

Let `u : D ⥤ C` be a representably flat functor of small categories and let `O` be a presheaf
of rings on `D`.  `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit` builds the
functor `u_p : PresheafOfModules O ⥤ PresheafOfModules (u_p O)` from the colimit formula
`(u_p G)(U) = colim_{(V, φ) ∈ I^u_U} G(V)` of Stacks 00VC, and reduces the source's
`f^{-1}F = (u_p F)^#` (the step the proof of Stacks 05VD turns on) to the single statement

  `upModuleFunctor u O ⊣ PresheafOfModules.pushforward (ringUnit u O)`,

which it takes as a *hypothesis* of `Stacks.ModuleUp.pullbackIsoUpModuleFunctor`.  This file
proves that adjunction, so that the identification of Mathlib's abstract module-level
pullback with the colimit formula becomes unconditional.

## Main definitions

* `Stacks.ModuleUp.homEquiv`: the bijection `(u_p G ⟶ M) ≃ (G ⟶ u^p M)`.
* `Stacks.ModuleUp.upModuleAdjunction`: **the adjunction**.
* `Stacks.ModuleUp.pullbackIsoUpModuleFunctorOfColimit`:
  `PresheafOfModules.pullback (ringUnit u O) ≅ upModuleFunctor u O`, i.e.
  `pullbackIsoUpModuleFunctor` with its hypothesis discharged.

## Main results

* `Stacks.ModuleUp.ringGerm_eq_unit_comp_map` and
  `Stacks.ModuleUp.abGerm_eq_unit_comp_map`: **the germ map factors through the
  Kan-extension unit** — the germ at an index `(V, φ : U ⟶ u V)` of `I^u_U` is the unit over
  `u V` followed by the restriction map along `φ`.  Everything else rests on these.
* `Stacks.ModuleUp.descHom_abGerm`: the descent formula, `Ψ_U([V, y]) = φ^* (g_V(y))`.
* `Stacks.ModuleUp.descHom_smul`: the descent of an `O`-semilinear map is `u_p O`-linear.

## Implementation notes

**The two halves of the adjunction are the two linearity checks**, exactly as the
implementation notes of `SiteUpColimit` predicted.  Forward: the hom-bijection of the
abelian-group-level Kan-extension adjunction `Functor.lanAdjunction` sends a `u_p O`-linear
`f` to `germ ↦ f ∘ unit`, which is `O`-semilinear by `upModule_unit_smul`.  Backward: the
descent `Ψ` of an `O`-semilinear `g` is `u_p O`-linear because a scalar `r : (u_p O)(U)` and
a section `x : (u_p G)(U)` are germs at a *common* index by `germ_jointly_surjective₂` — this
is where the directedness of `(I^u_U)ᵒᵖ`, i.e. `[RepresentablyFlat u]`, is used — and there
`r • x` is the germ of `a • s` by `germ_smul`, on which `Ψ` is computed by `descHom_abGerm`.
No hypothesis is added: `[RepresentablyFlat u]` is already carried by `upModuleFunctor`.

**The germ factorization.**  `abGerm_eq_unit_comp_map` is the one piece of new geometry.  The
colimit injection at `(V, φ)` is the injection at the unit index `(V, 𝟙 (u V))` followed by
the colimit reindexing `colimit.pre` along `CostructuredArrow.map φ`, which lands at
`(V, 𝟙 ≫ φ)` rather than at `(V, φ)`; the two indices are joined by the morphism
`CostructuredArrow.homMk (𝟙 V)` of `I^u_U`, so `colimit.w` identifies the injections without
any `eqToHom`.  That is `ι_costructuredArrowMap_mk_id`.

**One spelling per statement, pinned by a `def`'s result type.**  This file meets a *fourth*
spelling crossing beyond the three `SiteUpColimit` documents, and it is the same cure.
`Ab` is an `abbrev` for `AddCommGrpCat`, and `PresheafOfModules.presheaf` is valued in
`Cᵒᵖ ⥤ Ab` while `upAb`/`underlyingAb` are valued in `Cᵒᵖ ⥤ AddCommGrpCat`; a composite that
mixes them elaborates (defeq is checked) and is then invisible to `rw [Category.assoc]`,
whose failure message names a pattern that is plainly present in the goal.  The same happens
for the two instance paths `Functor.category.toQuiver` and `catToReflQuiver.toQuiver` of
`Quiver (Cᵒᵖ ⥤ AddCommGrpCat)`.  The `def`s `abIota`, `abIotaMmod`, `toAbHom`, `toAbBack`,
`toAbMap`, `toAbMapRing`, `descHom`, `fwdPresheafHom` and `backApp` carry ascribed result
types at one spelling each, and every statement mentions only those; a type *ascription*
`(e : T)` does **not** work, as `back_app_smul` demonstrated before it became `backApp_smul`.
`backApp` is the instance-search case rather than the `rw` case: the scalar-restricted
spelling `((pushforward (ringUnit u O)).obj M).obj V` is one at which the
`(u_p O)(u V)`-module structure is not found at all.

## References

* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModuleUp

universe v₁ u₁ w

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

section Factorization

variable (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- `colimit.ι_pre` at the pinned `CostructuredArrow.proj` spelling of `pbRingPre`. -/
lemma ι_pbRingPre {U V : Cᵒᵖ} (i : U ⟶ V) (c : CostructuredArrow u.op U) :
    colimit.ι (CostructuredArrow.proj u.op U ⋙ O) c ≫ pbRingPre u O i
      = colimit.ι (CostructuredArrow.proj u.op V ⋙ O) ((CostructuredArrow.map i).obj c) :=
  colimit.ι_pre (CostructuredArrow.proj u.op V ⋙ O) (CostructuredArrow.map i) c

/-- The colimit injection `G(V) ⟶ colim_{I^u_U} G` at an index `(V, φ)`, **with its source
ascribed at the `underlyingAb` spelling**.  Written `colimit.ι (proj u.op U ⋙ G.presheaf) c`
its source is `(CostructuredArrow.proj u.op U ⋙ G.presheaf).obj c`, whose ambient category
is `Ab` rather than `AddCommGrpCat`; the two are definitionally equal but the resulting
`Quiver.Hom` applications are not syntactically equal, so a composite that mixes them
elaborates and is then invisible to `rw [Category.assoc]`.  This is the same
`def`-with-ascribed-result-type cure as the three spelling crossings of
`Stacks.ModuleUp.SiteUpColimit`, applied to a fourth one. -/
noncomputable def abIota {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    (underlyingAb O G).obj c.left ⟶ colimit (CostructuredArrow.proj u.op U ⋙ G.presheaf) :=
  colimit.ι (CostructuredArrow.proj u.op U ⋙ G.presheaf) c

/-- The colimit injection into the colimit over the *double opposite* index, with its source
ascribed at the `underlyingAb` spelling, for the same reason as `abIota`. -/
noncomputable def abIotaMmod {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    (underlyingAb O G).obj c.left ⟶ colimit (pbMmod u O G U).presheaf :=
  colimit.ι (pbMmod u O G U).presheaf (idx u c)

omit [RepresentablyFlat u] in
/-- `ι_pbAbColimIso_hom` at the pinned spellings. -/
lemma abIotaMmod_pbAbColimIso {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    abIotaMmod u O G c ≫ (pbAbColimIso u O G U).hom = abIota u O G c :=
  ι_pbAbColimIso_hom u O G U (idx u c)

omit [RepresentablyFlat u] in
/-- The abelian-group analogue of `ι_pbRingPre`, at the pinned `abIota` spelling. -/
lemma abIota_pbAbPre {U V : Cᵒᵖ} (i : U ⟶ V) (c : CostructuredArrow u.op U) :
    abIota u O G c ≫ pbAbPre u O G i = abIota u O G ((CostructuredArrow.map i).obj c) :=
  colimit.ι_pre (CostructuredArrow.proj u.op V ⋙ G.presheaf) (CostructuredArrow.map i) c

omit [RepresentablyFlat u] in
/-- Reindexing the unit index `(V, 𝟙 (u V))` along `φ : u V ⟶ U` produces the index
`(V, φ)` up to the identity morphism of `I^u_U`, so the two colimit injections agree. -/
lemma ι_costructuredArrowMap_mk_id {H : Type u₁} [Category.{v₁} H] (P : Dᵒᵖ ⥤ H)
    {U : Cᵒᵖ} (c : CostructuredArrow u.op U)
    [HasColimit (CostructuredArrow.proj u.op U ⋙ P)] :
    colimit.ι (CostructuredArrow.proj u.op U ⋙ P)
        ((CostructuredArrow.map c.hom).obj
          (CostructuredArrow.mk (Y := c.left) (𝟙 (u.op.obj c.left))))
      = colimit.ι (CostructuredArrow.proj u.op U ⋙ P) c := by
  have hw := colimit.w (CostructuredArrow.proj u.op U ⋙ P)
    (CostructuredArrow.homMk (f' := c) (𝟙 c.left) (by simp) :
      (CostructuredArrow.map c.hom).obj
        (CostructuredArrow.mk (Y := c.left) (𝟙 (u.op.obj c.left))) ⟶ c)
  rw [show (CostructuredArrow.proj u.op U ⋙ P).map
      (CostructuredArrow.homMk (f' := c) (𝟙 c.left) (by simp) :
        (CostructuredArrow.map c.hom).obj
          (CostructuredArrow.mk (Y := c.left) (𝟙 (u.op.obj c.left))) ⟶ c)
      = 𝟙 _ from P.map_id _] at hw
  exact hw.symm.trans (Category.id_comp _)

/-- The Kan-extension unit is the colimit injection at the unit index, at the pinned
`upRingObjIso` spelling. -/
lemma ι_upRingObjIso_unit (V : Dᵒᵖ) :
    colimit.ι (CostructuredArrow.proj u.op (u.op.obj V) ⋙ O)
        (CostructuredArrow.mk (Y := V) (𝟙 (u.op.obj V))) ≫
        (upRingObjIso u O (u.op.obj V)).hom
      = upRingUnit u O V :=
  Stacks.PresheafOfModules.Pullback.leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit u.op O V

omit [RepresentablyFlat u] in
/-- The abelian-group analogue of `ι_upRingObjIso_unit`, at the pinned `abIota` spelling. -/
lemma abIota_upAbObjIso_unit (V : Dᵒᵖ) :
    abIota u O G (CostructuredArrow.mk (Y := V) (𝟙 (u.op.obj V))) ≫
        (upAbObjIso u O G (u.op.obj V)).hom
      = upAbUnit u (underlyingAb O G) V :=
  Stacks.PresheafOfModules.Pullback.leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit u.op
    G.presheaf V

omit [RepresentablyFlat u] in
/-- `ι_costructuredArrowMap_mk_id` at the pinned `abIota` spelling. -/
lemma abIota_costructuredArrowMap_mk_id {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    abIota u O G
        ((CostructuredArrow.map c.hom).obj
          (CostructuredArrow.mk (Y := c.left) (𝟙 (u.op.obj c.left))))
      = abIota u O G c :=
  ι_costructuredArrowMap_mk_id u G.presheaf c

/-- The germ map at an index, through the pinned `upRingObjIso` spelling. -/
lemma ringGerm_eq_ι {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    ringGerm u O c
      = colimit.ι (CostructuredArrow.proj u.op U ⋙ O) c ≫ (upRingObjIso u O U).hom := by
  rw [ringGerm, pbRingIso, Iso.trans_hom, ← Category.assoc, ι_pbRingColimIso_hom]

omit [RepresentablyFlat u] in
/-- The abelian-group analogue of `ringGerm_eq_ι`, at the pinned `abIota` spelling. -/
lemma abGerm_eq_abIota {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    abGerm u O G c = abIota u O G c ≫ (upAbObjIso u O G U).hom := by
  calc abGerm u O G c
      = abIotaMmod u O G c ≫
          ((pbAbColimIso u O G U).hom ≫ (upAbObjIso u O G U).hom) := rfl
    _ = (abIotaMmod u O G c ≫ (pbAbColimIso u O G U).hom) ≫
          (upAbObjIso u O G U).hom := (Category.assoc _ _ _).symm
    _ = abIota u O G c ≫ (upAbObjIso u O G U).hom := by rw [abIotaMmod_pbAbColimIso]

/-- **The germ map factors through the Kan-extension unit.**  The germ `O(V) ⟶ (u_p O)(U)`
at an index `(V, φ : U ⟶ u V)` of `I^u_U` is the unit `O(V) ⟶ (u_p O)(u V)` followed by the
restriction map of `u_p O` along `φ`. -/
theorem ringGerm_eq_unit_comp_map {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    ringGerm u O c = upRingUnit u O c.left ≫ (upRing u O).map c.hom := by
  have hpre : (upRingObjIso u O (u.op.obj c.left)).hom ≫ (upRing u O).map c.hom
      = pbRingPre u O c.hom ≫ (upRingObjIso u O U).hom := by
    rw [← upRingObjIso_hom_map_inv u O c.hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← ι_upRingObjIso_unit u O c.left, Category.assoc, hpre, ← Category.assoc,
    ι_pbRingPre, ι_costructuredArrowMap_mk_id, ringGerm_eq_ι]

omit [RepresentablyFlat u] in
/-- The abelian-group analogue of `ringGerm_eq_unit_comp_map`. -/
theorem abGerm_eq_unit_comp_map {U : Cᵒᵖ} (c : CostructuredArrow u.op U) :
    abGerm u O G c
      = upAbUnit u (underlyingAb O G) c.left ≫ (upAb u (underlyingAb O G)).map c.hom := by
  have hpre : (upAbObjIso u O G (u.op.obj c.left)).hom ≫
        (upAb u (underlyingAb O G)).map c.hom
      = pbAbPre u O G c.hom ≫ (upAbObjIso u O G U).hom := by
    rw [← upAbObjIso_hom_map_inv u O G c.hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← abIota_upAbObjIso_unit u O G c.left, Category.assoc, hpre, ← Category.assoc,
    abIota_pbAbPre, abIota_costructuredArrowMap_mk_id, abGerm_eq_abIota]

/-- Elementwise form of `ringGerm_eq_unit_comp_map`. -/
theorem ringGerm_apply {U : Cᵒᵖ} (c : CostructuredArrow u.op U) (a : O.obj c.left) :
    ringGerm u O c a = (upRing u O).map c.hom (upRingUnit u O c.left a) :=
  ConcreteCategory.congr_hom (ringGerm_eq_unit_comp_map u O c) a

omit [RepresentablyFlat u] in
/-- Elementwise form of `abGerm_eq_unit_comp_map`. -/
theorem abGerm_apply {U : Cᵒᵖ} (c : CostructuredArrow u.op U) (m : G.obj c.left) :
    abGerm u O G c m
      = (upAb u (underlyingAb O G)).map c.hom (upAbUnit u (underlyingAb O G) c.left m) :=
  ConcreteCategory.congr_hom (abGerm_eq_unit_comp_map u O G c) m

end Factorization

section Adjunction

variable (O : Dᵒᵖ ⥤ RingCat.{w})

/-- The hom-equivalence of the abelian-group-level Kan-extension adjunction
`u_p ⊣ u^p`, **with its source ascribed at the `upAb`/`underlyingAb` spellings**. -/
noncomputable def upAbHomEquiv (G : PresheafOfModules.{w} O)
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (upAb u (underlyingAb O G) ⟶ M) ≃ (underlyingAb O G ⟶ u.op ⋙ M) :=
  (u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv (underlyingAb O G) M

omit [RepresentablyFlat u] in
/-- The forward direction of `upAbHomEquiv` is "precompose with the Kan-extension unit". -/
lemma upAbHomEquiv_app (G : PresheafOfModules.{w} O) (M : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (β : upAb u (underlyingAb O G) ⟶ M) (V : Dᵒᵖ) :
    (upAbHomEquiv u O G M β).app V
      = upAbUnit u (underlyingAb O G) V ≫ β.app (u.op.obj V) := by
  have h : upAbHomEquiv u O G M β
      = (u.op.lanAdjunction AddCommGrpCat.{w}).unit.app (underlyingAb O G) ≫
          ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj u.op).map β := rfl
  rw [Functor.lanAdjunction_unit] at h
  rw [h]
  rfl

omit [RepresentablyFlat u] in
/-- The defining property of the inverse of `upAbHomEquiv`: it is the unique descent of
`ψ` along the Kan-extension unit. -/
lemma upAbHomEquiv_symm_unit (G : PresheafOfModules.{w} O) (M : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (ψ : underlyingAb O G ⟶ u.op ⋙ M) (V : Dᵒᵖ) :
    upAbUnit u (underlyingAb O G) V ≫ ((upAbHomEquiv u O G M).symm ψ).app (u.op.obj V)
      = ψ.app V := by
  rw [← upAbHomEquiv_app, Equiv.apply_symm_apply]

omit [RepresentablyFlat u] in
/-- Elementwise form of `upAbHomEquiv_app`. -/
lemma upAbHomEquiv_apply (G : PresheafOfModules.{w} O) (M : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (β : upAb u (underlyingAb O G) ⟶ M) (V : Dᵒᵖ) (m : (underlyingAb O G).obj V) :
    (upAbHomEquiv u O G M β).app V m
      = β.app (u.op.obj V) (upAbUnit u (underlyingAb O G) V m) :=
  ConcreteCategory.congr_hom (upAbHomEquiv_app u O G M β V) m

omit [RepresentablyFlat u] in
/-- Elementwise form of `upAbHomEquiv_symm_unit`. -/
lemma upAbHomEquiv_symm_apply_unit (G : PresheafOfModules.{w} O)
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (ψ : underlyingAb O G ⟶ u.op ⋙ M) (V : Dᵒᵖ)
    (m : (underlyingAb O G).obj V) :
    ((upAbHomEquiv u O G M).symm ψ).app (u.op.obj V)
        (upAbUnit u (underlyingAb O G) V m)
      = ψ.app V m :=
  ConcreteCategory.congr_hom (upAbHomEquiv_symm_unit u O G M ψ V) m

/-- `ringUnit` is the sectionwise ring unit. -/
lemma ringUnit_app (V : Dᵒᵖ) : (ringUnit u O).app V = upRingUnit u O V := rfl

omit [RepresentablyFlat u] in
/-- Naturality of `upAbHomEquiv` in the target: the Kan-extension adjunction's. -/
lemma upAbHomEquiv_naturality_right (G : PresheafOfModules.{w} O)
    (M M' : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (β : upAb u (underlyingAb O G) ⟶ M) (γ : M ⟶ M') :
    upAbHomEquiv u O G M' (β ≫ γ)
      = upAbHomEquiv u O G M β ≫
          ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj u.op).map γ :=
  (u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv_naturality_right β γ

omit [RepresentablyFlat u] in
/-- Naturality of the inverse of `upAbHomEquiv` in the source. -/
lemma upAbHomEquiv_symm_naturality_left {G' G : PresheafOfModules.{w} O}
    (ff : underlyingAb O G' ⟶ underlyingAb O G) (M : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (ψ : underlyingAb O G ⟶ u.op ⋙ M) :
    (upAbHomEquiv u O G' M).symm (ff ≫ ψ)
      = u.op.lan.map ff ≫ (upAbHomEquiv u O G M).symm ψ :=
  (u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv_naturality_left_symm ff ψ

/-- A morphism of presheaves of modules built by `homMk` has the given underlying morphism
of presheaves of abelian groups. -/
lemma toPresheaf_map_homMk {R : Cᵒᵖ ⥤ RingCat.{w}} {M₁ M₂ : PresheafOfModules.{w} R}
    (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : ∀ (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    (PresheafOfModules.toPresheaf R).map (PresheafOfModules.homMk φ hφ) = φ := rfl

variable (G : PresheafOfModules.{w} O) (M : PresheafOfModules.{w} (upRing u O))

/-- The underlying morphism of presheaves of abelian groups of a morphism out of `u_p G`,
**with its source ascribed at the `upAb` spelling**. -/
noncomputable def toAbHom (f : (upModuleFunctor u O).obj G ⟶ M) :
    upAb u (underlyingAb O G) ⟶ M.presheaf :=
  (PresheafOfModules.toPresheaf (upRing u O)).map f

/-- The components of `toAbHom` are those of `f`. -/
lemma toAbHom_apply (f : (upModuleFunctor u O).obj G ⟶ M) (U : Cᵒᵖ)
    (x : (upAb u (underlyingAb O G)).obj U) :
    (toAbHom u O G M f).app U x = f.app U x := rfl

/-- The underlying morphism of presheaves of abelian groups of a morphism into the
pushforward, **with its target ascribed at the `u.op ⋙ _` spelling**. -/
noncomputable def toAbBack
    (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) :
    underlyingAb O G ⟶ u.op ⋙ M.presheaf :=
  (PresheafOfModules.toPresheaf O).map g

/-- The components of `toAbBack` are those of `g`. -/
lemma toAbBack_apply (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M)
    (V : Dᵒᵖ) (y : G.obj V) :
    (toAbBack u O G M g).app V y = g.app V y := rfl

/-- **The descent of an `O`-semilinear map along the Kan-extension unit.** -/
noncomputable def descHom (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) :
    upAb u (underlyingAb O G) ⟶ M.presheaf :=
  (upAbHomEquiv u O G M.presheaf).symm (toAbBack u O G M g)

/-- `descHom` is the inverse of `upAbHomEquiv` applied to `toAbBack`. -/
lemma descHom_eq (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) :
    descHom u O G M g = (upAbHomEquiv u O G M.presheaf).symm (toAbBack u O G M g) := rfl

/-- The component of `g` at `V`, **with its result type ascribed at the `M(u V)` spelling**
rather than the scalar-restricted one `((pushforward (ringUnit u O)).obj M).obj V`, at which
the `(u_p O)(u V)`-module instance is not found by synthesis. -/
noncomputable def backApp
    (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) (V : Dᵒᵖ)
    (y : G.obj V) : M.obj (u.op.obj V) :=
  g.app V y

/-- Semilinearity of `g`, at the pinned `backApp` spelling. -/
lemma backApp_smul (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M)
    (V : Dᵒᵖ) (a : O.obj V) (y : G.obj V) :
    backApp u O G M g V (a • y) = upRingUnit u O V a • backApp u O G M g V y :=
  (g.app V).hom.map_smul a y

/-- The descent restricts to `g` along the Kan-extension unit. -/
lemma descHom_unit (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M)
    (V : Dᵒᵖ) (y : G.obj V) :
    (descHom u O G M g).app (u.op.obj V) (upAbUnit u (underlyingAb O G) V y)
      = backApp u O G M g V y :=
  upAbHomEquiv_symm_apply_unit u O G M.presheaf (toAbBack u O G M g) V y

/-- **The descent formula on germs.**  The descent of `g` sends the germ of `y` at an index
`(V, φ)` to the restriction along `φ` of `g_V(y)`.  This is the formula the linearity check
turns on, and it is what `abGerm_eq_unit_comp_map` supplies. -/
lemma descHom_abGerm (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M)
    {U : Cᵒᵖ} (c : CostructuredArrow u.op U) (y : G.obj c.left) :
    (descHom u O G M g).app U (abGerm u O G c y)
      = M.map c.hom (backApp u O G M g c.left y) := by
  have hnat := ConcreteCategory.congr_hom ((descHom u O G M g).naturality c.hom)
    (upAbUnit u (underlyingAb O G) c.left y)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [abGerm_apply, hnat, descHom_unit]
  rfl

/-- **Backward linearity.**  The descent of an `O`-semilinear map is `u_p O`-linear.

This is where the directedness of `(I^u_U)ᵒᵖ` enters: by `germ_jointly_surjective₂` a scalar
of `(u_p O)(U)` and a section of `(u_p G)(U)` are germs at a *common* index, where the action
is the germwise one of `germ_smul`. -/
lemma descHom_smul (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M)
    (U : Cᵒᵖ) (r : (upRing u O).obj U) (x : (upAb u (underlyingAb O G)).obj U) :
    letI := upModule u O G U
    (descHom u O G M g).app U (r • x) = r • (descHom u O G M g).app U x := by
  let := upModule u O G U
  obtain ⟨c, a, s₀, ha, hs₀⟩ := germ_jointly_surjective₂ u O G r x
  obtain ⟨s, hs⟩ : ∃ s : G.obj c.left, abGerm u O G c s = x := ⟨s₀, hs₀⟩
  subst ha
  subst hs
  rw [← germ_smul u O G c a s, descHom_abGerm, descHom_abGerm, backApp_smul,
    PresheafOfModules.map_smul, ← ringGerm_apply]
  rfl

/-- The `O`-semilinear map underlying the forward direction of the hom-equivalence, **with
its type ascribed at the spelling `PresheafOfModules.homMk` demands**. -/
noncomputable def fwdPresheafHom (f : (upModuleFunctor u O).obj G ⟶ M) :
    G.presheaf ⟶ ((PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M).presheaf :=
  upAbHomEquiv u O G M.presheaf (toAbHom u O G M f)

/-- `fwdPresheafHom` is `upAbHomEquiv` applied to `toAbHom`. -/
lemma fwdPresheafHom_eq (f : (upModuleFunctor u O).obj G ⟶ M) :
    fwdPresheafHom u O G M f = upAbHomEquiv u O G M.presheaf (toAbHom u O G M f) := rfl

/-- `fwdPresheafHom f` sends a section `m` of `G` over `V` to the value of `f` on the image of
`m` under the Kan-extension unit. -/
lemma fwdPresheafHom_apply (f : (upModuleFunctor u O).obj G ⟶ M) (V : Dᵒᵖ) (m : G.obj V) :
    (fwdPresheafHom u O G M f).app V m
      = f.app (u.op.obj V) (upAbUnit u (underlyingAb O G) V m) :=
  upAbHomEquiv_apply u O G M.presheaf (toAbHom u O G M f) V m

/-- The forward map of the hom-equivalence: precomposition with the Kan-extension unit.
Its `O`-semilinearity is `upModule_unit_smul`. -/
noncomputable def homEquivFwd (f : (upModuleFunctor u O).obj G ⟶ M) :
    G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M :=
  PresheafOfModules.homMk (fwdPresheafHom u O G M f)
    (fun V a m => by
      let := upModule u O G (u.op.obj V)
      rw [fwdPresheafHom_apply, fwdPresheafHom_apply,
        show upAbUnit u (underlyingAb O G) V (a • m)
            = upRingUnit u O V a • upAbUnit u (underlyingAb O G) V m from
          upModule_unit_smul u O G V a m]
      exact (f.app (u.op.obj V)).hom.map_smul _ _)

/-- The inverse map of the hom-equivalence: the Kan-extension descent, which is
`u_p O`-linear by `descHom_smul`. -/
noncomputable def homEquivBwd
    (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) :
    (upModuleFunctor u O).obj G ⟶ M :=
  PresheafOfModules.homMk (descHom u O G M g) (fun U r x => descHom_smul u O G M g U r x)

/-- The underlying morphism of abelian presheaves of `homEquivFwd f` is `fwdPresheafHom f`. -/
lemma toAbBack_homEquivFwd (f : (upModuleFunctor u O).obj G ⟶ M) :
    toAbBack u O G M (homEquivFwd u O G M f) = fwdPresheafHom u O G M f :=
  toPresheaf_map_homMk _ _

/-- The underlying morphism of abelian presheaves of `homEquivBwd g` is `descHom g`. -/
lemma toAbHom_homEquivBwd
    (g : G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) :
    toAbHom u O G M (homEquivBwd u O G M g) = descHom u O G M g :=
  toPresheaf_map_homMk _ _

/-- **The hom-equivalence** `(u_p G ⟶ M) ≃ (G ⟶ u^p M)`. -/
noncomputable def homEquiv :
    ((upModuleFunctor u O).obj G ⟶ M) ≃
      (G ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj M) where
  toFun := homEquivFwd u O G M
  invFun := homEquivBwd u O G M
  left_inv f := (PresheafOfModules.toPresheaf (upRing u O)).map_injective (by
    change toAbHom u O G M (homEquivBwd u O G M (homEquivFwd u O G M f)) = toAbHom u O G M f
    rw [toAbHom_homEquivBwd, descHom_eq, toAbBack_homEquivFwd, fwdPresheafHom_eq,
      Equiv.symm_apply_apply])
  right_inv g := (PresheafOfModules.toPresheaf O).map_injective (by
    change toAbBack u O G M (homEquivFwd u O G M (homEquivBwd u O G M g)) = toAbBack u O G M g
    rw [toAbBack_homEquivFwd, fwdPresheafHom_eq, toAbHom_homEquivBwd, descHom_eq,
      Equiv.apply_symm_apply])

/-- The underlying morphism of presheaves of abelian groups of a morphism of presheaves of
`O`-modules, **with its type ascribed at the `underlyingAb` spelling**. -/
noncomputable def toAbMap {G₁ G₂ : PresheafOfModules.{w} O} (f : G₁ ⟶ G₂) :
    underlyingAb O G₁ ⟶ underlyingAb O G₂ :=
  (PresheafOfModules.toPresheaf O).map f

/-- `toAbBack` of a composite `f ≫ g` is `toAbMap f ≫ toAbBack g`. -/
lemma toAbBack_comp {G₁ G₂ : PresheafOfModules.{w} O}
    {N : PresheafOfModules.{w} (upRing u O)} (f : G₁ ⟶ G₂)
    (g : G₂ ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj N) :
    toAbBack u O G₁ N (f ≫ g) = toAbMap O f ≫ toAbBack u O G₂ N g :=
  (PresheafOfModules.toPresheaf O).map_comp f g

/-- `toAbHom` of `u_p f ≫ h` is the left Kan extension of `toAbMap f` followed by
`toAbHom h`. -/
lemma toAbHom_upModuleFunctor_comp {G₁ G₂ : PresheafOfModules.{w} O}
    {N : PresheafOfModules.{w} (upRing u O)} (f : G₁ ⟶ G₂)
    (h : (upModuleFunctor u O).obj G₂ ⟶ N) :
    toAbHom u O G₁ N ((upModuleFunctor u O).map f ≫ h)
      = u.op.lan.map (toAbMap O f) ≫ toAbHom u O G₂ N h :=
  (PresheafOfModules.toPresheaf (upRing u O)).map_comp _ h

/-- The underlying morphism of presheaves of abelian groups of a morphism of presheaves of
`u_p O`-modules, **with its type ascribed at the `presheaf` spelling**. -/
noncomputable def toAbMapRing {N₁ N₂ : PresheafOfModules.{w} (upRing u O)} (g : N₁ ⟶ N₂) :
    N₁.presheaf ⟶ N₂.presheaf :=
  (PresheafOfModules.toPresheaf (upRing u O)).map g

/-- `toAbHom` of a composite `f ≫ g` is `toAbHom f ≫ toAbMapRing g`. -/
lemma toAbHom_comp {G₁ : PresheafOfModules.{w} O}
    {N₁ N₂ : PresheafOfModules.{w} (upRing u O)}
    (f : (upModuleFunctor u O).obj G₁ ⟶ N₁) (g : N₁ ⟶ N₂) :
    toAbHom u O G₁ N₂ (f ≫ g)
      = toAbHom u O G₁ N₁ f ≫ toAbMapRing u O g :=
  (PresheafOfModules.toPresheaf (upRing u O)).map_comp f g

/-- `toAbBack` of `h` followed by the pushforward of `g` is `toAbBack h` whiskered with
`toAbMapRing g`. -/
lemma toAbBack_comp_right {G₁ : PresheafOfModules.{w} O}
    {N₁ N₂ : PresheafOfModules.{w} (upRing u O)}
    (h : G₁ ⟶ (PresheafOfModules.pushforward.{w} (ringUnit u O)).obj N₁) (g : N₁ ⟶ N₂) :
    toAbBack u O G₁ N₂ (h ≫ (PresheafOfModules.pushforward.{w} (ringUnit u O)).map g)
      = toAbBack u O G₁ N₁ h ≫
          ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj u.op).map
            (toAbMapRing u O g) :=
  (PresheafOfModules.toPresheaf O).map_comp h _

/-- `upAbHomEquiv_naturality_right` at the spellings the module-level proof produces. -/
lemma upAbHomEquiv_naturality_right' (G₁ : PresheafOfModules.{w} O)
    {N₁ N₂ : PresheafOfModules.{w} (upRing u O)}
    (β : upAb u (underlyingAb O G₁) ⟶ N₁.presheaf) (g : N₁ ⟶ N₂) :
    upAbHomEquiv u O G₁ N₂.presheaf (β ≫ toAbMapRing u O g)
      = upAbHomEquiv u O G₁ N₁.presheaf β ≫
          ((Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj u.op).map
            (toAbMapRing u O g) :=
  (u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv_naturality_right β _

/-- **The adjunction `u_p ⊣ u^p` on presheaves of modules.**

This is the statement the identification `f^{-1}F = (u_p F)^#` of Stacks 05VD was reduced to
by `Stacks.ModuleUp.pullbackIsoUpModuleFunctor`, which took it as a hypothesis.  Its two
non-formal halves are the two linearity checks: `upModule_unit_smul` for the forward
direction, and `descHom_smul` — i.e. `germ_jointly_surjective₂` together with `germ_smul` and
the descent formula `descHom_abGerm` — for the backward one. -/
noncomputable def upModuleAdjunction :
    upModuleFunctor u O ⊣ PresheafOfModules.pushforward.{w} (ringUnit u O) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G₁ N₁ => homEquiv u O G₁ N₁
      homEquiv_naturality_left_symm := fun {G₁ G₂ N₁} f g =>
        (PresheafOfModules.toPresheaf (upRing u O)).map_injective (by
          change toAbHom u O G₁ N₁ (homEquivBwd u O G₁ N₁ (f ≫ g))
            = toAbHom u O G₁ N₁ ((upModuleFunctor u O).map f ≫ homEquivBwd u O G₂ N₁ g)
          rw [toAbHom_upModuleFunctor_comp, toAbHom_homEquivBwd, toAbHom_homEquivBwd,
            descHom_eq, descHom_eq, toAbBack_comp, upAbHomEquiv_symm_naturality_left])
      homEquiv_naturality_right := fun {G₁ N₁ N₂} f g =>
        (PresheafOfModules.toPresheaf O).map_injective (by
          change toAbBack u O G₁ N₂ (homEquivFwd u O G₁ N₂ (f ≫ g))
            = toAbBack u O G₁ N₂ (homEquivFwd u O G₁ N₁ f ≫
                (PresheafOfModules.pushforward.{w} (ringUnit u O)).map g)
          rw [toAbBack_comp_right, toAbBack_homEquivFwd, toAbBack_homEquivFwd,
            fwdPresheafHom_eq, fwdPresheafHom_eq, toAbHom_comp,
            upAbHomEquiv_naturality_right']) }

/-- **`f^{-1}F = (u_p F)^#` in the colimit spelling.**  With the adjunction in hand,
`pullbackIsoUpModuleFunctor` becomes unconditional: Mathlib's abstract module-level pullback
along the Kan-extension unit *is* the source's colimit formula `u_p`. -/
noncomputable def pullbackIsoUpModuleFunctorOfColimit :
    PresheafOfModules.pullback.{w} (ringUnit u O) ≅ upModuleFunctor u O :=
  pullbackIsoUpModuleFunctor u O (upModuleAdjunction u O)

end Adjunction

end Stacks.ModuleUp
