module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompSeparated
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekDirectSums
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportOpen
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion
public import StacksFrontier.AlgebraicGeometry.Etale.SupportTransport
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Surjectivity of `(f_!F)_ȳ ⟶ H⁰_c(X_ȳ, F)` from proper base change in degree zero

Let `f : X ⟶ Y` be separated and locally of finite type in a big étale site, `F` an abelian
sheaf on the small étale site of `X`, and `ȳ` a geometric point of `Y` whose spectrum lies in
the site. This file reduces the surjectivity of the canonical map
`(f_!F)_ȳ ⟶ H⁰_c(X_ȳ, F|_{X_ȳ})` of Stacks 0F76 to proper base change in degree `0`, following
the proof of the source.

A compactly supported section `t` on `X_ȳ` has quasi-compact support, so it is supported in the
geometric fibre `X'_ȳ` of a quasi-compact open `X' ⊆ X` lying over an affine open `Y₀ ⊆ Y`
through which `ȳ` factors. Nagata's compactification theorem (Stacks 0F41) gives an open
immersion `j̄ : X' ⟶ X̄` and a proper `X̄ ⟶ Y₀`. On `X'_ȳ` the restriction of `t` is a compactly
supported section of `F|_{X'}`, which extends by zero (Stacks 0F74) to a section of
`j̄_!(F|_{X'})` on `X̄_ȳ`; by proper base change it comes from a section `s` of `j̄_!(F|_{X'})`
over the base change of an étale neighbourhood `N` of the lift of `ȳ`. Such a section is a
section of `F` over `X' ×_{Y₀} N` with support closed in `X̄ ×_{Y₀} N`, hence proper over `N`;
extending it by zero to `X ×_Y N` (Stacks 0F53) gives a section of `f_!F` whose germ maps to
`t`.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekStalkToCompactSections_surjective_of_properBaseChange` —
  the surjectivity half of Stacks 0F76, granted proper base change in degree `0`.
* `AlgebraicGeometry.SmallEtale.exists_fShriekStalkToCompactSections_eq_of_compactification` —
  the reduction to a compactification of a quasi-compact open over an affine open.
* `AlgebraicGeometry.SmallEtale.openRestrictionProperSupportIso` — for an open immersion `j`,
  the inverse image `j⁻¹(j_!F)` of the proper-support direct image is `F`.

## Implementation notes

The comparison of the section `t` with the section produced from `s` is made on `X'_ȳ`, where
both sides are inverse images of `F|_{X'}`: a global section supported inside an open
subscheme is determined by its restriction there
(`AlgebraicGeometry.SmallEtale.eq_of_restrictGlobal_eq`). Everything else is the calculus of
pulling sections back along composites (`pullbackSectionAlongHom_comp_arrow`), and a single
equality of lifts into an iterated base change, `compactificationLift_eq`, checked on the two
projections of fibre products.

## References

* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F74](https://stacks.math.columbia.edu/tag/0F74)
* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

section OpenExtension

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
  (F : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v})

/-- For an open immersion, the base change of the post-composite of a test object projects
isomorphically back onto it. -/
instance isIso_pullbackFst_openPostcompose (W : SmallEtale B X'.obj X'.property) :
    IsIso (B.inclusion.map (pullback.fst ((openPostcompose B j).obj W).obj.hom j)) := by
  have h := openPostcomposeAdjunction_unit_left_fst B j W
  have : IsIso ((openPostcomposeAdjunction B j).unit.app W) := inferInstance
  have hU : IsIso ((openPostcomposeAdjunction B j).unit.app W).hom.left := by
    have : IsIso ((SmallEtale.inclusion B X'.obj X'.property).map
      ((openPostcomposeAdjunction B j).unit.app W)) := inferInstance
    exact (inferInstance : IsIso ((Over.forget _).map ((SmallEtale.inclusion B X'.obj
      X'.property).map ((openPostcomposeAdjunction B j).unit.app W))))
  have : IsIso (pullback.fst ((openPostcompose B j).obj W).obj.hom j) := by
    rw [← IsIso.inv_eq_of_hom_inv_id h]
    exact @IsIso.inv_isIso _ _ _ _ _ hU
  infer_instance

/-- Restricting the proper-support direct image along an open immersion `j` back to the open
subscheme, read on the direct image along post-composition: a section over the post-composite
of a test object `W` is a section over `W ×_X X'` with proper support, and restricting it along
the unit `W ⟶ W ×_X X'` gives a section over `W`. -/
def openRestrictionProperSupportMap :
    ((openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X'.obj X'.property) (SmallEtale.topology B X.obj X.property)).obj
        ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) ⟶ F :=
  ⟨{ app W := (properSupportSheafInclusion B j F).hom.app (op ((openPostcompose B j).obj W.unop))
        ≫ F.obj.map ((openPostcomposeAdjunction B j).unit.app W.unop).op
     naturality W₁ W₂ g := by
        refine ConcreteCategory.hom_ext _ _ fun a => ?_
        have h2 := (openPostcomposeAdjunction B j).unit.naturality g.unop
        change F.obj.map ((openPostcomposeAdjunction B j).unit.app W₂.unop).op
            (F.obj.map ((smallEtaleBaseChange B j).map ((openPostcompose B j).map g.unop)).op a.1) =
          F.obj.map g (F.obj.map ((openPostcomposeAdjunction B j).unit.app W₁.unop).op a.1)
        exact (ConcreteCategory.congr_hom (F.obj.map_comp _ _) a.1).symm.trans
          ((congrArg (fun m => F.obj.map m.op a.1) h2.symm).trans
            (ConcreteCategory.congr_hom (F.obj.map_comp _ _) a.1)) }⟩

/-- The restriction map of `j_! F` to the open subscheme is an isomorphism: on a test object `W`
it is restriction along the isomorphism `W ⟶ W ×_X X'`, and a section over `W ×_X X'` always has
support proper over the post-composite of `W`. -/
instance isIso_openRestrictionProperSupportMap :
    IsIso (openRestrictionProperSupportMap B j F) := by
  have hW : ∀ W : (SmallEtale B X'.obj X'.property)ᵒᵖ,
      IsIso ((openRestrictionProperSupportMap B j F).hom.app W) := by
    intro W
    let V := (openPostcompose B j).obj W.unop
    let u := (openPostcomposeAdjunction B j).unit.app W.unop
    have hu : IsIso u := inferInstance
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun h => ?_⟩
    · apply Subtype.ext
      have hinj : Function.Injective (F.obj.map u.op) :=
        ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstance : IsIso (F.obj.map u.op))).1
      exact hinj hab
    · let σ := F.obj.map (inv u).op h
      have hσ : properSupportSections B j F V σ := by
        change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫
          B.inclusion.map (pullback.fst ((openPostcompose B j).obj W.unop).obj.hom j))
        have := isIso_pullbackFst_openPostcompose B j W.unop
        have : IsProper (B.inclusion.map (pullback.fst ((openPostcompose B j).obj W.unop).obj.hom
          j)) := inferInstance
        infer_instance
      refine ⟨⟨σ, hσ⟩, ?_⟩
      change F.obj.map u.op (F.obj.map (inv u).op h) = h
      rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
        F.obj.map_id]
      rfl
  have : IsIso (openRestrictionProperSupportMap B j F).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map (openRestrictionProperSupportMap B j F)) :=
    inferInstanceAs (IsIso (openRestrictionProperSupportMap B j F).hom)
  exact isIso_of_reflects_iso (openRestrictionProperSupportMap B j F) (sheafToPresheaf _ _)

/-- **The restriction of an extension by zero along an open immersion is the original sheaf.**
For an open immersion `j : X' ⟶ X`, the inverse image along `j` of the proper-support direct
image `j_! F` is `F`. -/
def openRestrictionProperSupportIso :
    (abPullback.{u, v} B j).obj ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) ≅ F :=
  ((openRestrictionIso.{u, v} B j).app _).symm ≪≫ asIso (openRestrictionProperSupportMap B j F)

/-- The identification `j⁻¹ j_! F ≅ F` carries the pullback of a section `s` of `j_! F` over a
test object `V` of `X` to the section of `F` over `V ×_X X'` underlying `s`. -/
theorem openRestrictionProperSupportIso_unit (V : SmallEtale B X.obj X.property)
    (s : ((properSupportFunctor.{u, max (u + 1) v} B j).obj F).obj.obj (op V)) :
    (openRestrictionProperSupportIso B j F).hom.hom.app (op ((smallEtaleBaseChange B j).obj V))
        (abPullbackUnit.{u, v} B j ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) V s) =
      properSupportSection B j F V s := by
  have h1 := openRestrictionIso_unit_app.{u, v} B j
    ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) V s
  show ((openRestrictionProperSupportMap B j F).hom.app (op ((smallEtaleBaseChange B j).obj V)))
      (((openRestrictionIso.{u, v} B j).inv.app ((properSupportFunctor.{u, max (u + 1) v} B j).obj
          F)).hom.app (op ((smallEtaleBaseChange B j).obj V))
        (abPullbackUnit.{u, v} B j ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) V s)) = _
  have h2 : ((openRestrictionIso.{u, v} B j).inv.app ((properSupportFunctor.{u, max (u + 1) v} B
      j).obj F)).hom.app
        (op ((smallEtaleBaseChange B j).obj V)) (abPullbackUnit.{u, v} B j
            ((properSupportFunctor.{u, max (u + 1) v} B j).obj F) V s) =
      ((properSupportFunctor.{u, max (u + 1) v} B j).obj F).obj.map
        ((openPostcomposeAdjunction B j).counit.app V).op s := by
    refine (congrArg (ConcreteCategory.hom (((openRestrictionIso.{u, v} B j).inv.app
      ((properSupportFunctor.{u, max (u + 1) v} B j).obj F)).hom.app
        (op ((smallEtaleBaseChange B j).obj V)))) h1.symm).trans ?_
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
      (op ((smallEtaleBaseChange B j).obj V))) ((openRestrictionIso.{u, v} B j).hom_inv_id_app
        ((properSupportFunctor.{u, max (u + 1) v} B j).obj F))) _
  rw [h2]
  show F.obj.map ((openPostcomposeAdjunction B j).unit.app
      ((smallEtaleBaseChange B j).obj V)).op
    (F.obj.map ((smallEtaleBaseChange B j).map ((openPostcomposeAdjunction B j).counit.app V)).op
      (properSupportSection B j F V s)) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    (openPostcomposeAdjunction B j).right_triangle_components V]
  exact ConcreteCategory.congr_hom (F.obj.map_id _) _

end OpenExtension

section Natural

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S)

/-- Pulling sections back is natural in the abelian sheaf. -/
theorem pullbackSectionAlongHom_natural
    {F₁ F₂ : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F₁ ⟶ F₂) (W : SmallEtale B S.obj S.property) (R : SmallEtale B T.obj T.property)
    (a : R ⟶ (smallEtaleBaseChange B p).obj W) (x : F₁.obj.obj (op W)) :
    ((abPullback.{u, v} B p).map φ).hom.app (op R)
        (pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F₁ W R a x) =
      pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F₂ W R a (φ.hom.app (op W) x) := by
  have hu := ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.hom.app (op W))
    (((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.naturality φ)) x
  have hn := ConcreteCategory.congr_hom (((abPullback.{u, v} B p).map φ).hom.naturality a.op)
    ((((smallEtaleBaseChange B p).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F₁).hom.app (op W) x)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply,
    Functor.id_map, Functor.comp_map] at hu hn
  exact hn.trans ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hu.symm))

end Natural

section OpenRestrict

variable (k : Type u) [Field k] (B : BigEtaleSite.{u}) {Z' Z : B.Scheme} (m : Z' ⟶ Z)
  [IsOpenImmersion (B.inclusion.map m)]
  (H : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v})

/-- The restriction of a global section along an open immersion `m`, as a global section of the
inverse image. -/
abbrev restrictGlobal (x : H.obj.obj (op (SmallEtale.final B Z.obj Z.property))) :
    ((abPullback.{u, v} B m).obj H).obj.obj (op (SmallEtale.final B Z'.obj Z'.property)) :=
  pullbackSectionAlongHom B m AddCommGrpCat.{max (u + 1) v} H (SmallEtale.final B _ _)
    (SmallEtale.final B _ _) (baseChangeFinalIso B m).inv x

/-- Extension by zero along an open immersion (Stacks 0F74) followed by restriction back is the
identity. -/
theorem restrictGlobal_openInclusion (g : Z.obj ⟶ Spec (.of k)) [IsSeparated g]
    [LocallyOfFiniteType g]
    (s : compactlySupportedSections k Z'.obj (B.inclusion.map m ≫ g) B Z'.property
      ((abPullback.{u, v} B m).obj H)) :
    restrictGlobal B m H ((compactlySupportedSections_openInclusion k B m g H).1 s).1 = s.1 := by
  have hc := ((compactlySupportedSections_openInclusion k B m g H).2.2 s).1
  show ((abPullback.{u, v} B m).obj H).obj.map (baseChangeFinalIso B m).inv.op
      (abPullbackUnit.{u, v} B m H (SmallEtale.final B _ _)
        ((compactlySupportedSections_openInclusion k B m g H).1 s).1) = s.1
  refine (congrArg _ hc.symm).trans ?_
  have h1 : (baseChangeFinalIso B m).inv ≫ (SmallEtale.finalIsTerminal B Z'.obj Z'.property).from
      ((smallEtaleBaseChange B m).obj (SmallEtale.final B Z.obj Z.property)) = 𝟙 _ :=
    (SmallEtale.finalIsTerminal B Z'.obj Z'.property).hom_ext _ _
  refine (ConcreteCategory.congr_hom (((abPullback.{u, v} B m).obj H).obj.map_comp _ _)
      s.1).symm.trans
    ?_
  rw [← op_comp, h1]
  exact ConcreteCategory.congr_hom (((abPullback.{u, v} B m).obj H).obj.map_id _) _

/-- The first projection of the base change of the final object along `p` is the second
projection followed by `p`. -/
private theorem fst_final_eq_snd_comp {S T : B.Scheme} (p : T ⟶ S) :
    pullback.fst (SmallEtale.final B S.obj S.property).obj.hom p =
      pullback.snd (SmallEtale.final B S.obj S.property).obj.hom p ≫ p :=
  (Category.comp_id _).symm.trans pullback.condition

omit [IsOpenImmersion (B.inclusion.map m)] in
/-- The image of the projection of the base change of the final object along an open immersion
is the image of the open immersion. -/
theorem range_pullbackFst_final :
    Set.range (B.inclusion.map (pullback.fst (SmallEtale.final B Z.obj Z.property).obj.hom
        m)).base =
      Set.range (B.inclusion.map m).base := by
  have hiso' : IsIso (B.inclusion.map (pullback.snd (SmallEtale.final B Z.obj Z.property).obj.hom
      m)) := (inferInstance : IsIso ((SmallEtale.toScheme B Z'.obj Z'.property).map
        (baseChangeFinalIso B m).hom))
  have hc' : B.inclusion.map (pullback.fst (SmallEtale.final B Z.obj Z.property).obj.hom m) =
      B.inclusion.map (pullback.snd (SmallEtale.final B Z.obj Z.property).obj.hom m) ≫
        B.inclusion.map m := by
    rw [← Functor.map_comp, ← fst_final_eq_snd_comp B m]
    rfl
  rw [hc']
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (B.inclusion.map (pullback.snd (SmallEtale.final B Z.obj Z.property).obj.hom m)).base).2 w
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (congrArg _ hz)⟩

/-- A global section supported inside an open subscheme is determined by its restriction
there. -/
theorem eq_of_restrictGlobal_eq (x z : H.obj.obj (op (SmallEtale.final B Z.obj Z.property)))
    (hx : supportSection B Z.obj Z.property H (SmallEtale.final B _ _) x ⊆
      Set.range (B.inclusion.map m).base)
    (hz : supportSection B Z.obj Z.property H (SmallEtale.final B _ _) z ⊆
      Set.range (B.inclusion.map m).base)
    (h : restrictGlobal B m H x = restrictGlobal B m H z) : x = z := by
  let e := (openPostcomposeAdjunction B m).counit.app (SmallEtale.final B Z.obj Z.property)
  have he : (SmallEtale.toScheme B Z.obj Z.property).map e =
      B.inclusion.map (pullback.fst (SmallEtale.final B Z.obj Z.property).obj.hom m) :=
    openPostcomposeAdjunction_counit_toScheme B m _
  have : IsOpenImmersion ((SmallEtale.toScheme B Z.obj Z.property).map e) := by
    rw [he]
    exact MorphismProperty.of_isPullback ((IsPullback.of_hasPullback
      (SmallEtale.final B Z.obj Z.property).obj.hom m).flip.map B.inclusion) inferInstance
  have hr : Set.range ((SmallEtale.toScheme B Z.obj Z.property).map e).base =
      Set.range (B.inclusion.map m).base := by
    rw [he]
    exact range_pullbackFst_final B m
  refine eq_of_map_eq_of_supportSection_subset B _ _ H e x z (hr ▸ hx) (hr ▸ hz) ?_
  have hu : ∀ w : H.obj.obj (op (SmallEtale.final B Z.obj Z.property)),
      restrictGlobal B m H w = ((abPullback.{u, v} B m).obj H).obj.map
        (baseChangeFinalIso B m).inv.op (((openRestrictionIso.{u, v} B m).hom.app H).hom.app
          (op ((smallEtaleBaseChange B m).obj (SmallEtale.final B _ _))) (H.obj.map e.op w)) := by
    intro w
    rw [openRestrictionIso_unit_app]
    rfl
  rw [hu, hu] at h
  have hinj1 : Function.Injective (((abPullback.{u, v} B m).obj H).obj.map
      (baseChangeFinalIso B m).inv.op) :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hinj2 : Function.Injective (((openRestrictionIso.{u, v} B m).hom.app H).hom.app
      (op ((smallEtaleBaseChange B m).obj (SmallEtale.final B _ _)))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj2 (hinj1 h)

end OpenRestrict

section Projections

variable (B : BigEtaleSite.{u})

/-- If an isomorphism of the small étale site carries `b` to `a` on underlying schemes, its
inverse carries `a` to `b`. -/
private theorem inv_hom_left_comp {S : B.Scheme} {U V : SmallEtale B S.obj S.property}
    (e : U ≅ V) {Z : B.Scheme} (a : U.obj.left ⟶ Z) (b : V.obj.left ⟶ Z)
    (h : e.hom.hom.left ≫ b = a) : e.inv.hom.left ≫ a = b := by
  rw [← h, ← Category.assoc, ← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom,
    e.inv_hom_id]
  simp

/-- The inverse of the factored composition comparison of small étale base changes, followed by
the two projections, is the projection of the base change along the composite. -/
theorem factoredCompIso_inv_app_fst {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app W).hom.left ≫
        pullback.fst ((smallEtaleBaseChange B g).obj W).obj.hom f ≫ pullback.fst W.obj.hom g =
      pullback.fst W.obj.hom fg :=
  inv_hom_left_comp B ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).app W) _ _
    (smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg W)

/-- The composition comparison of small étale base changes carries the projection of the base
change along the composite to the composite of the two projections. -/
alias compIso_hom_app_fst :=
  AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_compIso_hom_app_left_fst

/-- The inverse of `AlgebraicGeometry.SmallEtale.baseChangeFinalIso` followed by the projection to
the base is the morphism along which one base changes. -/
theorem baseChangeFinalIso_inv_fst {S T : B.Scheme} (m : T ⟶ S) :
    (baseChangeFinalIso B m).inv.hom.left ≫
        pullback.fst (SmallEtale.final B S.obj S.property).obj.hom m = m := by
  have hw : (baseChangeFinalIso B m).inv.hom.left ≫
      pullback.snd (SmallEtale.final B S.obj S.property).obj.hom m = 𝟙 _ :=
    Over.w (baseChangeFinalIso B m).inv.hom
  refine (congrArg (_ ≫ ·) (fst_final_eq_snd_comp B m)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ m) hw).trans (Category.id_comp _)

/-- Two morphisms into an étale base change agree when their projections agree with a common
morphism. -/
theorem baseChangeObj_hom_ext' {X' X : B.Scheme} (p : X' ⟶ X) {T : SmallEtale B X'.obj X'.property}
    {W : SmallEtale B X.obj X.property} {a b : T ⟶ (smallEtaleBaseChange B p).obj W}
    (m : T.obj.left ⟶ W.obj.left) (ha : a.hom.left ≫ pullback.fst W.obj.hom p = m)
    (hb : b.hom.left ≫ pullback.fst W.obj.hom p = m) : a = b :=
  baseChangeObj_hom_ext B p (ha.trans hb.symm)

/-- A morphism from the final object into the base change of `W` along `p`, followed by the
projection to `W` and the structure morphism of `W`, is `p`. -/
theorem final_baseChange_fst_hom {O S : B.Scheme} (p : O ⟶ S) (W : SmallEtale B S.obj S.property)
    (γ : SmallEtale.final B O.obj O.property ⟶ (smallEtaleBaseChange B p).obj W) :
    γ.hom.left ≫ pullback.fst W.obj.hom p ≫ W.obj.hom = p := by
  have hw : γ.hom.left ≫ pullback.snd W.obj.hom p = 𝟙 _ := Over.w γ.hom
  exact (congrArg (_ ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ p) hw).trans (Category.id_comp _)))

/-- `AlgebraicGeometry.SmallEtale.final_baseChange_fst_hom` for the base change of a base change,
with the structure morphism written as the second projection. -/
theorem final_baseChange_fst_snd {O S T : B.Scheme} (p : O ⟶ S) (g : S ⟶ T)
    (N : SmallEtale B T.obj T.property)
    (γ : SmallEtale.final B O.obj O.property ⟶
      (smallEtaleBaseChange B p).obj ((smallEtaleBaseChange B g).obj N)) :
    (γ.hom.left ≫ pullback.fst ((smallEtaleBaseChange B g).obj N).obj.hom p) ≫
      pullback.snd N.obj.hom g = p :=
  (Category.assoc _ _ _).trans (final_baseChange_fst_hom B p _ γ)

/-- A morphism of the small étale site commutes with the structure morphisms. -/
theorem over_w_left {S : B.Scheme} {U V : SmallEtale B S.obj S.property} (a : U ⟶ V) :
    a.hom.left ≫ V.obj.hom = U.obj.hom :=
  Over.w a.hom

end Projections

section ChainAux

variable {C : Type*} [Category C]

/-- A bookkeeping identity for a composite of seven arrows followed by two projections, used to
compare two lifts into a base change. -/
private theorem lift_chain_aux {O A₁ A₂ A₃ A₄ A₅ A₆ A₇ Wl Bj Bp Wp Nl Xy K : C}
    (x₀ : O ⟶ A₁) (x₁ : A₁ ⟶ A₂) (x₂ : A₂ ⟶ A₃) (x₃ : A₃ ⟶ A₄) (x₄ : A₄ ⟶ A₅) (x₅ : A₅ ⟶ A₆)
    (x₆ : A₆ ⟶ A₇) (P : A₇ ⟶ Wl) (Q : Wl ⟶ Nl) (R₁ : A₆ ⟶ Bj) (R₁' : A₅ ⟶ Bj) (R₂ : Bj ⟶ Wl)
    (R₃ : A₄ ⟶ Bp) (c : Bp ⟶ Bj) (S₁ : Bp ⟶ Wp) (S₂ : Wp ⟶ Nl) (T : A₃ ⟶ Wp) (m : O ⟶ Xy)
    (g : Xy ⟶ Wp) (st : Xy ⟶ K) (nb : K ⟶ Nl) (st₀ : O ⟶ K)
    (sA : x₆ ≫ P = R₁ ≫ R₂) (sB : x₅ ≫ R₁ = R₁') (sC : x₄ ≫ R₁' = R₃ ≫ c)
    (sD : c ≫ R₂ ≫ Q = S₁ ≫ S₂) (sE : x₃ ≫ R₃ ≫ S₁ = T) (sF : x₀ ≫ x₁ ≫ x₂ ≫ T = m ≫ g)
    (sG : g ≫ S₂ = st ≫ nb) (sH : m ≫ st = st₀) :
    x₀ ≫ x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ ≫ x₆ ≫ P ≫ Q = st₀ ≫ nb := by
  rw [reassoc_of% sA, reassoc_of% sB, reassoc_of% sC, sD, reassoc_of% sE, reassoc_of% sF, sG,
    reassoc_of% sH]

end ChainAux

section Compactification

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (y : GeometricPoint Y.obj) (hy : B.Contains y.source)
  {Y₀ X' Xb : B.Scheme} (i₀ : Y₀ ⟶ Y) [IsOpenImmersion (B.inclusion.map i₀)]
  (j' : X' ⟶ X) [IsOpenImmersion (B.inclusion.map j')] (f' : X' ⟶ Y₀) (hf' : f' ≫ i₀ = j' ≫ f)
  (jb : X' ⟶ Xb) [IsOpenImmersion (B.inclusion.map jb)] (fb : Xb ⟶ Y₀) (hfb : jb ≫ fb = f')
  (y₀ : y.source ⟶ Y₀.obj) (hy₀ : y₀ ≫ B.inclusion.map i₀ = y.hom)

/-- The lift to `Y₀` of the geometric point `ȳ` of `Y`. -/
abbrev liftedGeometricPoint : GeometricPoint Y₀.obj := ⟨y.residueField, y₀⟩

include hy₀ in
omit [IsOpenImmersion (B.inclusion.map i₀)] in
/-- The lift of `ȳ` to `Y₀`, followed by the open immersion `Y₀ ⟶ Y`, is `ȳ`. -/
theorem geometricPointHom_lifted :
    geometricPointHom B (liftedGeometricPoint B y y₀) hy ≫ i₀ = geometricPointHom B y hy :=
  ObjectProperty.hom_ext _ hy₀

/-- The open immersion `X'_ȳ ⟶ X_ȳ` of geometric fibres. -/
def openFibreMap :
    geometricFibreObj B f' (liftedGeometricPoint B y y₀) hy ⟶ geometricFibreObj B f y hy :=
  pullback.lift (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫
      j') (geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy) (by
    rw [Category.assoc, ← hf', ← Category.assoc, pullback.condition, Category.assoc,
      geometricPointHom_lifted B y hy i₀ y₀ hy₀])

omit [IsOpenImmersion (B.inclusion.map i₀)] [IsOpenImmersion (B.inclusion.map j')] in
/-- The open immersion `X'_ȳ ⟶ X_ȳ` lies over `X' ⟶ X`. -/
theorem openFibreMap_proj :
    openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀ ≫ geometricFibreProj B f y hy =
      geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j' :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion (B.inclusion.map i₀)] [IsOpenImmersion (B.inclusion.map j')] in
/-- The open immersion `X'_ȳ ⟶ X_ȳ` lies over the spectrum of the residue field. -/
theorem openFibreMap_struct :
    openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀ ≫ geometricFibreStruct B f y hy =
      geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy :=
  pullback.lift_snd _ _ _

omit [IsOpenImmersion (B.inclusion.map j')] in
/-- `X'_ȳ` is the inverse image of `X'` in `X_ȳ`. -/
theorem isPullback_openFibreMap :
    IsPullback (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀) (geometricFibreProj B f'
        (liftedGeometricPoint B y y₀) hy)
      (geometricFibreProj B f y hy) j' := by
  have hO := (IsPullback.of_hasPullback f' (geometricPointHom B (liftedGeometricPoint B y y₀) hy))
  have hOut : IsPullback (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)
      (geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy) (j' ≫ f)
      (geometricPointHom B y hy) := by
    rw [← hf', ← geometricPointHom_lifted B y hy i₀ y₀ hy₀]
    exact isPullback_comp_mono hO i₀
  refine IsPullback.of_right ?_ (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀)
    (IsPullback.of_hasPullback f (geometricPointHom B y hy)).flip
  rw [openFibreMap_struct]
  exact hOut.flip

/-- The open immersion `X'_ȳ ⟶ X̄_ȳ` of geometric fibres. -/
def compFibreMap :
    geometricFibreObj B f' (liftedGeometricPoint B y y₀) hy ⟶
      geometricFibreObj B fb (liftedGeometricPoint B y y₀) hy :=
  pullback.lift (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫
      jb) (geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy) (by
    rw [Category.assoc, hfb, pullback.condition])

omit [IsOpenImmersion (B.inclusion.map jb)] in
/-- The open immersion `X'_ȳ ⟶ X̄_ȳ` lies over `X' ⟶ X̄`. -/
theorem compFibreMap_proj :
    compFibreMap B y hy f' jb fb hfb y₀ ≫ geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy =
      geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion (B.inclusion.map jb)] in
/-- The open immersion `X'_ȳ ⟶ X̄_ȳ` lies over the spectrum of the residue field. -/
theorem compFibreMap_struct :
    compFibreMap B y hy f' jb fb hfb y₀ ≫ geometricFibreStruct B fb (liftedGeometricPoint B y
        y₀) hy =
      geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy :=
  pullback.lift_snd _ _ _

omit [IsOpenImmersion (B.inclusion.map jb)] in
/-- `X'_ȳ` is the inverse image of `X'` in `X̄_ȳ`. -/
theorem isPullback_compFibreMap :
    IsPullback (compFibreMap B y hy f' jb fb hfb y₀) (geometricFibreProj B f'
        (liftedGeometricPoint B y y₀) hy)
      (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy) jb := by
  have hO := (IsPullback.of_hasPullback f' (geometricPointHom B (liftedGeometricPoint B y y₀) hy))
  have hO' : IsPullback (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)
      (geometricFibreStruct B f' (liftedGeometricPoint B y y₀) hy) (jb ≫ fb)
      (geometricPointHom B (liftedGeometricPoint B y y₀) hy) := by
    rw [hfb]
    exact hO
  refine IsPullback.of_right ?_ (compFibreMap_proj B y hy f' jb fb hfb y₀)
    (IsPullback.of_hasPullback fb (geometricPointHom B (liftedGeometricPoint B y y₀) hy)).flip
  rw [compFibreMap_struct]
  exact hO'.flip

/-- `X'_ȳ ⟶ X_ȳ` is an open immersion, being a base change of `X' ⟶ X`. -/
instance isOpenImmersion_openFibreMap :
    IsOpenImmersion (B.inclusion.map (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)) :=
  MorphismProperty.of_isPullback ((isPullback_openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀).flip.map
    B.inclusion) inferInstance

/-- `X'_ȳ ⟶ X̄_ȳ` is an open immersion, being a base change of `X' ⟶ X̄`. -/
instance isOpenImmersion_compFibreMap :
    IsOpenImmersion (B.inclusion.map (compFibreMap B y hy f' jb fb hfb y₀)) :=
  MorphismProperty.of_isPullback ((isPullback_compFibreMap B y hy f' jb fb hfb y₀).flip.map
    B.inclusion) inferInstance

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The extension by zero `j̄_!(F|_{X'})` to the compactification `X̄` of the restriction of `F`
to the open subscheme `X'`. -/
abbrev compactificationSheaf :
    Sheaf (SmallEtale.topology B Xb.obj Xb.property) AddCommGrpCat.{max (u + 1) v} :=
  (properSupportFunctor.{u, max (u + 1) v} B jb).obj ((abPullback.{u, v} B j').obj F)

/-- On the geometric fibre `X'_ȳ`, the inverse image of `F` through `X_ȳ` is the inverse image of
`F|_{X'}` along `X'_ȳ ⟶ X'`. -/
def fibreComparisonF :
    (abPullback.{u, v} B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).obj
        ((abPullback.{u, v} B (geometricFibreProj B f y hy)).obj F) ≅
      (abPullback.{u, v} B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).obj
        ((abPullback.{u, v} B j').obj F) :=
  (smallEtaleSheafPullbackFactoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
      (geometricFibreProj B f y hy) (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j')
      (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀) AddCommGrpCat.{max (u + 1) v}).app F ≪≫
    ((smallEtaleSheafPullbackFactoredCompIso B _ X' X
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl
      AddCommGrpCat.{max (u + 1) v}).app F).symm

/-- On the geometric fibre `X'_ȳ`, the inverse image of `F|_{X'}` along `X'_ȳ ⟶ X'` is the
inverse image of `j̄_!(F|_{X'})` through `X̄_ȳ`. -/
def fibreComparisonG :
    (abPullback.{u, v} B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).obj
        ((abPullback.{u, v} B j').obj F) ≅
      (abPullback.{u, v} B (compFibreMap B y hy f' jb fb hfb y₀)).obj
        ((abPullback.{u, v} B (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)).obj
          (compactificationSheaf B j' jb F)) :=
  (abPullback.{u, v} B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).mapIso
      (openRestrictionProperSupportIso B jb ((abPullback.{u, v} B j').obj F)).symm ≪≫
    (smallEtaleSheafPullbackFactoredCompIso B _ X' Xb
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) jb
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb) rfl
      AddCommGrpCat.{max (u + 1) v}).app (compactificationSheaf B j' jb F) ≪≫
    ((smallEtaleSheafPullbackFactoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
      (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
      (compFibreMap_proj B y hy f' jb fb hfb y₀) AddCommGrpCat.{max (u + 1) v}).app
      (compactificationSheaf B j' jb F)).symm

/-- The comparison, on the geometric fibre `X'_ȳ`, of the inverse image of `F` through `X_ȳ`
with the inverse image of `j̄_!(F|_{X'})` through `X̄_ȳ`: both are inverse images of `F|_{X'}`
along `X'_ȳ ⟶ X'`. -/
abbrev fibreComparison :
    (abPullback.{u, v} B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).obj
        ((abPullback.{u, v} B (geometricFibreProj B f y hy)).obj F) ⟶
      (abPullback.{u, v} B (compFibreMap B y hy f' jb fb hfb y₀)).obj
        ((abPullback.{u, v} B (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)).obj
          (compactificationSheaf B j' jb F)) :=
  (fibreComparisonF B f y hy i₀ j' f' hf' y₀ hy₀ F).hom ≫
    (fibreComparisonG B y hy j' f' jb fb hfb y₀ F).hom

/-- The comparison `fibreComparisonF` on the restriction to `X'_ȳ` of the pullback to `X_ȳ` of a
section `x` of `F` over `X_V`: it is the pullback along `X'_ȳ ⟶ X'` of the restriction of `x`
to `X'_V`. -/
theorem fibreComparisonF_restrict (M : (geometricPointFiber B Y.obj Y.property y).Elements)
    (x : F.obj.obj (op ((smallEtaleBaseChange B f).obj M.1))) :
    (fibreComparisonF B f y hy i₀ j' f' hf' y₀ hy₀ F).hom.hom.app (op (SmallEtale.final B _ _))
        (restrictGlobal B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
          ((abPullback.{u, v} B (geometricFibreProj B f y hy)).obj F)
          (geometricFibreRestriction B f y hy F M x)) =
      pullbackSectionAlongHom B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)
        AddCommGrpCat.{max (u + 1) v} ((abPullback.{u, v} B j').obj F)
        ((smallEtaleBaseChange B j').obj ((smallEtaleBaseChange B f).obj M.1))
        (SmallEtale.final B _ _)
        ((baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).inv ≫
          (smallEtaleBaseChange B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).map
            (geometricFibreLift B f y hy M) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
            (geometricFibreProj B f y hy)
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j')
            (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀)).hom.app
              ((smallEtaleBaseChange B f).obj M.1) ≫
          (smallEtaleBaseChange_factoredCompIso B _ X' X
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl).inv.app
              ((smallEtaleBaseChange B f).obj M.1))
        (abPullbackUnit.{u, v} B j' F ((smallEtaleBaseChange B f).obj M.1) x) := by
  have h1 := pullbackSectionAlongHom_comp_arrow.{u, v} B
    (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀) (geometricFibreProj B f y hy)
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j')
    (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀) F ((smallEtaleBaseChange B f).obj M.1)
    (SmallEtale.final B _ _) (geometricFibreLift B f y hy M) (SmallEtale.final B _ _)
    (baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).inv x
  have h2 := pullbackSectionAlongHom_comp_arrow.{u, v} B
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl F
    ((smallEtaleBaseChange B f).obj M.1) _ (𝟙 _) (SmallEtale.final B _ _)
    ((baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).inv ≫
          (smallEtaleBaseChange B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).map
            (geometricFibreLift B f y hy M) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
            (geometricFibreProj B f y hy)
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j')
            (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀)).hom.app
              ((smallEtaleBaseChange B f).obj M.1) ≫
          (smallEtaleBaseChange_factoredCompIso B _ X' X
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl).inv.app
              ((smallEtaleBaseChange B f).obj M.1)) x
  rw [pullbackSectionAlongHom_id] at h2
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] at h2
  show ((smallEtaleSheafPullbackFactoredCompIso B _ X' X
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl
      AddCommGrpCat.{max (u + 1) v}).inv.app F).hom.app _
    (((smallEtaleSheafPullbackFactoredCompIso B _ _ X _ _ _
      (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀) AddCommGrpCat.{max (u + 1) v}).hom.app
        F).hom.app _ _) = _
  refine (congrArg _ h1).trans ((congrArg _ h2.symm).trans ?_)
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (SmallEtale.final B _ _)))
    (Iso.hom_inv_id_app (smallEtaleSheafPullbackFactoredCompIso B _ X' X
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) j'
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') rfl
      AddCommGrpCat.{max (u + 1) v}) F)) _

omit [IsOpenImmersion (B.inclusion.map j')] in
/-- The comparison `fibreComparisonG` on the pullback along `X'_ȳ ⟶ X'` of the section of
`F|_{X'}` underlying a section `s` of `j̄_!(F|_{X'})`: it is the pullback of `s` along
`X'_ȳ ⟶ X' ⟶ X̄`, read through `X̄_ȳ`. -/
theorem fibreComparisonG_pullback (W : SmallEtale B Xb.obj Xb.property)
    (γ : SmallEtale.final B (geometricFibreObj B f' (liftedGeometricPoint B y y₀) hy).obj
        (geometricFibreObj B f' (liftedGeometricPoint B y y₀) hy).property ⟶
      (smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).obj
        ((smallEtaleBaseChange B jb).obj W))
    (s : (compactificationSheaf B j' jb F).obj.obj (op W)) :
    (fibreComparisonG B y hy j' f' jb fb hfb y₀ F).hom.hom.app (op (SmallEtale.final B _ _))
        (pullbackSectionAlongHom B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)
          AddCommGrpCat.{max (u + 1) v} ((abPullback.{u, v} B j').obj F)
          ((smallEtaleBaseChange B jb).obj W) (SmallEtale.final B _ _) γ
          (properSupportSection B jb ((abPullback.{u, v} B j').obj F) W s)) =
      ((smallEtaleSheafPullbackFactoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
        (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
        (compFibreMap_proj B y hy f' jb fb hfb y₀) AddCommGrpCat.{max (u + 1) v}).inv.app
          (compactificationSheaf B j' jb F)).hom.app (op (SmallEtale.final B _ _))
        (pullbackSectionAlongHom B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
          AddCommGrpCat.{max (u + 1) v} (compactificationSheaf B j' jb F) W
          (SmallEtale.final B _ _)
          (γ ≫ (smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
              hy)).map
              (𝟙 _) ≫
            (smallEtaleBaseChange_factoredCompIso B _ X' Xb
              (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) jb
              (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫
                  jb) rfl).hom.app W) s) := by
  have hη : (openRestrictionProperSupportIso B jb ((abPullback.{u, v} B j').obj F)).inv.hom.app
      (op ((smallEtaleBaseChange B jb).obj W))
      (properSupportSection B jb ((abPullback.{u, v} B j').obj F) W s) =
      pullbackSectionAlongHom B jb AddCommGrpCat.{max (u + 1) v} (compactificationSheaf B j' jb F)
        W ((smallEtaleBaseChange B jb).obj W) (𝟙 _) s := by
    rw [pullbackSectionAlongHom_id, ← openRestrictionProperSupportIso_unit B jb _ W s]
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
      (op ((smallEtaleBaseChange B jb).obj W)))
      (Iso.hom_inv_id (openRestrictionProperSupportIso B jb ((abPullback.{u, v} B j').obj F)))) _
  have h4 := pullbackSectionAlongHom_comp_arrow.{u, v} B
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) jb
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb) rfl
    (compactificationSheaf B j' jb F) W _ (𝟙 _) (SmallEtale.final B _ _) γ s
  show ((smallEtaleSheafPullbackFactoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
      (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
      (compFibreMap_proj B y hy f' jb fb hfb y₀) AddCommGrpCat.{max (u + 1) v}).inv.app
        (compactificationSheaf B j' jb F)).hom.app _
    (((smallEtaleSheafPullbackFactoredCompIso B _ X' Xb
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) jb
      (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb) rfl
      AddCommGrpCat.{max (u + 1) v}).hom.app (compactificationSheaf B j' jb F)).hom.app _
      (((abPullback.{u, v} B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).map
        (openRestrictionProperSupportIso B jb ((abPullback.{u, v} B j').obj F)).inv).hom.app _
        (pullbackSectionAlongHom B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)
          AddCommGrpCat.{max (u + 1) v} ((abPullback.{u, v} B j').obj F)
          ((smallEtaleBaseChange B jb).obj W) (SmallEtale.final B _ _) γ
          (properSupportSection B jb ((abPullback.{u, v} B j').obj F) W s)))) = _
  rw [pullbackSectionAlongHom_natural, hη]
  exact congrArg _ h4

omit [IsOpenImmersion (B.inclusion.map j')] in
/-- The restriction to `X'_ȳ` of the pullback to `X̄_ȳ` of a section `s` of `j̄_!(F|_{X'})`, read
through the comparison of iterated inverse images: the pullback of `s` along
`X'_ȳ ⟶ X' ⟶ X̄`. -/
theorem restrict_compFibre
    (M : (geometricPointFiber B Y₀.obj Y₀.property (liftedGeometricPoint B y y₀)).Elements)
    (s : (compactificationSheaf B j' jb F).obj.obj (op ((smallEtaleBaseChange B fb).obj M.1))) :
    ((smallEtaleSheafPullbackFactoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
        (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
        (compFibreMap_proj B y hy f' jb fb hfb y₀) AddCommGrpCat.{max (u + 1) v}).hom.app
          (compactificationSheaf B j' jb F)).hom.app (op (SmallEtale.final B _ _))
        (restrictGlobal B (compFibreMap B y hy f' jb fb hfb y₀)
          ((abPullback.{u, v} B (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)).obj
            (compactificationSheaf B j' jb F))
          (geometricFibreRestriction B fb (liftedGeometricPoint B y y₀) hy
            (compactificationSheaf B j' jb F) M s)) =
      pullbackSectionAlongHom B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
        AddCommGrpCat.{max (u + 1) v} (compactificationSheaf B j' jb F)
        ((smallEtaleBaseChange B fb).obj M.1) (SmallEtale.final B _ _)
        ((baseChangeFinalIso B (compFibreMap B y hy f' jb fb hfb y₀)).inv ≫
          (smallEtaleBaseChange B (compFibreMap B y hy f' jb fb hfb y₀)).map
            (geometricFibreLift B fb (liftedGeometricPoint B y y₀) hy M) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
            (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
            (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
            (compFibreMap_proj B y hy f' jb fb hfb y₀)).hom.app
              ((smallEtaleBaseChange B fb).obj M.1)) s :=
  pullbackSectionAlongHom_comp_arrow.{u, v} B (compFibreMap B y hy f' jb fb hfb y₀)
    (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
    (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb)
    (compFibreMap_proj B y hy f' jb fb hfb y₀) (compactificationSheaf B j' jb F)
    ((smallEtaleBaseChange B fb).obj M.1) (SmallEtale.final B _ _)
    (geometricFibreLift B fb (liftedGeometricPoint B y y₀) hy M) (SmallEtale.final B _ _)
    (baseChangeFinalIso B (compFibreMap B y hy f' jb fb hfb y₀)).inv s

include hy₀ in
/-- An étale neighbourhood of the lift of `ȳ` to `Y₀`, viewed as an étale neighbourhood of `ȳ`
in `Y`. -/
def compNeighborhood
    (N : (geometricPointFiber B Y₀.obj Y₀.property (liftedGeometricPoint B y y₀)).Elements) :
    (geometricPointFiber B Y.obj Y.property y).Elements :=
  Functor.elementsMk _ ((openPostcompose B i₀).obj N.obj) ⟨N.val.1, by
    change N.val.1 ≫ B.inclusion.map (N.obj.obj.hom ≫ i₀) = y.hom
    rw [Functor.map_comp, ← Category.assoc, N.val.2]
    exact hy₀⟩

include hf' in
/-- The two base changes of an étale neighbourhood `N` of the lift of `ȳ` to `Y₀`: along
`X' ⟶ Y₀`, and, viewing `N` over `Y`, along `X' ⟶ X ⟶ Y`. They agree because `Y₀ ⟶ Y` is a
monomorphism. -/
def neighborhoodIso (N : SmallEtale B Y₀.obj Y₀.property) :
    (smallEtaleBaseChange B f').obj N ≅
      (smallEtaleBaseChange B (j' ≫ f)).obj ((openPostcompose B i₀).obj N) := by
  have hm : Mono i₀ := mono_openImmersion B i₀
  have sq : IsPullback (pullback.fst N.obj.hom f') (pullback.snd N.obj.hom f')
      (N.obj.hom ≫ i₀) (j' ≫ f) := by
    rw [← hf']
    exact isPullback_comp_mono (IsPullback.of_hasPullback N.obj.hom f') i₀
  exact (BigEtaleOver.IsEtaleOver B X'.obj X'.property).fullyFaithfulι.preimageIso
    (Over.isoMk (sq.isoIsPullback _ _ (IsPullback.of_hasPullback (N.obj.hom ≫ i₀) (j' ≫ f)))
      (sq.isoIsPullback_hom_snd _ _ _))

omit [IsOpenImmersion (B.inclusion.map j')] in
/-- `AlgebraicGeometry.SmallEtale.neighborhoodIso` lies over `N`. -/
theorem neighborhoodIso_hom_fst (N : SmallEtale B Y₀.obj Y₀.property) :
    (neighborhoodIso B f i₀ j' f' hf' N).hom.hom.left ≫
        pullback.fst ((openPostcompose B i₀).obj N).obj.hom (j' ≫ f) =
      pullback.fst N.obj.hom f' :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

omit [IsOpenImmersion (B.inclusion.map j')] in
/-- `AlgebraicGeometry.SmallEtale.neighborhoodIso` lies over `X'`. -/
theorem neighborhoodIso_hom_snd (N : SmallEtale B Y₀.obj Y₀.property) :
    (neighborhoodIso B f i₀ j' f' hf' N).hom.hom.left ≫
        pullback.snd ((openPostcompose B i₀).obj N).obj.hom (j' ≫ f) =
      pullback.snd N.obj.hom f' :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The composite `p⁻¹ (g⁻¹ W) ⟶ (p ≫ g)⁻¹ W` of the base change of a lift `γ` along `p` with the
factored composition comparison, followed by the projection to `W`, is `p` followed by the
projection of `γ`. -/
private theorem baseChangeLift_comp_fst {T G X₀ : B.Scheme} {p : T ⟶ G} {g : G ⟶ X₀}
    {h : T ⟶ X₀} (hp : p ≫ g = h) {W : SmallEtale B X₀.obj X₀.property}
    (γ : SmallEtale.final B G.obj G.property ⟶ (smallEtaleBaseChange B g).obj W) :
    (baseChangeFinalIso B p).inv.hom.left ≫ ((smallEtaleBaseChange B p).map γ).hom.left ≫
      ((smallEtaleBaseChange_factoredCompIso B _ _ X₀ p g h hp).hom.app W).hom.left ≫
        pullback.fst W.obj.hom h = p ≫ γ.hom.left ≫ pullback.fst W.obj.hom g := by
  have e1 := baseChangeObjProjection_naturality B p γ
  simp only [baseChangeObjProjection] at e1
  exact (congrArg (_ ≫ _ ≫ ·) (smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ X₀ p g h
    hp W)).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) e1).trans (Category.assoc _ _ _)))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (baseChangeFinalIso_inv_fst B p))))

include hfb hy₀ in
omit [IsOpenImmersion (B.inclusion.map j')] [IsOpenImmersion (B.inclusion.map jb)] in
/-- The lift equality behind the comparison of the two ways of reading a section of
`j̄_!(F|_{X'})` over the base change of `N` on `X'_ȳ`. -/
theorem compactificationLift_eq
    (N : (geometricPointFiber B Y₀.obj Y₀.property (liftedGeometricPoint B y y₀)).Elements) :
    (((baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).inv ≫
        (smallEtaleBaseChange B (openFibreMap B f y hy i₀ j' f' hf' y₀
            hy₀)).map (geometricFibreLift B f y hy (compNeighborhood B y i₀ y₀ hy₀ N)) ≫
        (smallEtaleBaseChange_factoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
            (geometricFibreProj B f y hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') (openFibreMap_proj B f y
            hy i₀ j' f' hf' y₀ hy₀)).hom.app ((smallEtaleBaseChange B f).obj (compNeighborhood B y
                i₀ y₀ hy₀ N).1) ≫ (smallEtaleBaseChange_factoredCompIso B _ X' X
                    (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
                        hy) j' (geometricFibreProj B f' (liftedGeometricPoint B y
                            y₀) hy ≫ j') rfl).inv.app ((smallEtaleBaseChange B f).obj
                                (compNeighborhood B y i₀ y₀ hy₀ N).1)) ≫
      (smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
          hy)).map ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app (compNeighborhood B y
              i₀ y₀ hy₀ N).1 ≫
        ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫ ((smallEtaleBaseChange_factoredCompIso B
            X' Xb Y₀ jb fb f' hfb).app N.1).symm).hom)) ≫
      (smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).map (𝟙
          _) ≫ (smallEtaleBaseChange_factoredCompIso B _ X' Xb (geometricFibreProj B f'
              (liftedGeometricPoint B y y₀) hy) jb (geometricFibreProj B f' (liftedGeometricPoint
                  B y y₀) hy ≫ jb) rfl).hom.app ((smallEtaleBaseChange B fb).obj N.1) =
    (baseChangeFinalIso B (compFibreMap B y hy f' jb fb hfb y₀)).inv ≫
      (smallEtaleBaseChange B (compFibreMap B y hy f' jb fb hfb y₀)).map (geometricFibreLift B fb
          (liftedGeometricPoint B y y₀) hy N) ≫
      (smallEtaleBaseChange_factoredCompIso B _ _ Xb (compFibreMap B y hy f' jb fb hfb y₀)
          (geometricFibreProj B fb (liftedGeometricPoint B y y₀) hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ jb) (compFibreMap_proj B y hy
            f' jb fb hfb y₀)).hom.app ((smallEtaleBaseChange B fb).obj N.1) := by
  -- the right-hand side
  have hR := (baseChangeLift_comp_fst B (compFibreMap_proj B y hy f' jb fb hfb y₀)
    (geometricFibreLift B fb (liftedGeometricPoint B y y₀) hy N)).trans
    (congrArg (compFibreMap B y hy f' jb fb hfb y₀ ≫ ·)
      (geometricFibreLift_proj B fb (liftedGeometricPoint B y y₀) hy N))
  -- the left-hand side: the prefix through `X_ȳ`
  have hP := (baseChangeLift_comp_fst B (openFibreMap_proj B f y hy i₀ j' f' hf' y₀ hy₀)
    (geometricFibreLift B f y hy (compNeighborhood B y i₀ y₀ hy₀ N))).trans
    (congrArg (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀ ≫ ·)
      (geometricFibreLift_proj B f y hy (compNeighborhood B y i₀ y₀ hy₀ N)))
  have hPs : ((baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).inv ≫
      (smallEtaleBaseChange B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).map (geometricFibreLift
          B f y hy (compNeighborhood B y i₀ y₀ hy₀ N)) ≫
      (smallEtaleBaseChange_factoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
          (geometricFibreProj B f y hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') (openFibreMap_proj B f y
            hy i₀ j' f' hf' y₀ hy₀)).hom.app ((smallEtaleBaseChange B f).obj (compNeighborhood B y
                i₀ y₀ hy₀ N).1)).hom.left ≫ pullback.snd ((smallEtaleBaseChange B f).obj
                    (compNeighborhood B y i₀ y₀ hy₀
                        N).1).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫
                            j') = 𝟙 _ :=
    over_w_left B _
  -- the remaining facts about the left-hand side
  have g1 := smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ X' Xb (geometricFibreProj B f'
      (liftedGeometricPoint B y y₀) hy) jb (geometricFibreProj B f' (liftedGeometricPoint B y
          y₀) hy ≫ jb) rfl
    ((smallEtaleBaseChange B fb).obj N.1)
  have g2 := factoredCompIso_inv_app_fst B (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
      hy) j' (geometricFibreProj B f' (liftedGeometricPoint B y
          y₀) hy ≫ j') rfl ((smallEtaleBaseChange B f).obj (compNeighborhood B y i₀ y₀ hy₀ N).1)
  have g3 := factoredCompIso_inv_app_fst B jb fb f' hfb N.1
  have g4 := inv_hom_left_comp B _ _ _ (neighborhoodIso_hom_fst B f i₀ j' f' hf' N.1)
  have g5 := compIso_hom_app_fst B j' f ((compNeighborhood B y i₀ y₀ hy₀ N).1)
  have g6 := geometricFibreToNeighborhood_fst B f y hy (compNeighborhood B y i₀ y₀ hy₀ N)
  have g7 := geometricFibreToNeighborhood_fst B fb (liftedGeometricPoint B y y₀) hy N
  have g8 := openFibreMap_struct B f y hy i₀ j' f' hf' y₀ hy₀
  have g9 := compFibreMap_struct B y hy f' jb fb hfb y₀
  refine baseChangeObj_hom_ext' B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫
      jb) ((compFibreMap B y hy f' jb fb hfb
          y₀) ≫ geometricFibreToNeighborhood B fb (liftedGeometricPoint B y y₀) hy N)
    ?_ ?_
  · apply pullback.hom_ext
    · have n2 := baseChangeObjProjection_naturality B (geometricFibreProj B f'
        (liftedGeometricPoint B y y₀) hy)
        ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app (compNeighborhood B y i₀ y₀ hy₀
            N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app N.1).symm).hom)
      have n1 := baseChangeObjProjection_naturality B (geometricFibreProj B f'
          (liftedGeometricPoint B y y₀) hy)
        (𝟙 ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj N.1)))
      simp only [baseChangeObjProjection] at n1 n2
      -- Step A--C
      have sB : ((smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
          hy)).map (𝟙 ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj
              N.1)))).hom.left ≫ pullback.fst ((smallEtaleBaseChange B jb).obj
                  ((smallEtaleBaseChange B fb).obj
                      N.1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) ≫
                          pullback.fst ((smallEtaleBaseChange B fb).obj
                              N.1).obj.hom jb ≫ pullback.fst N.1.obj.hom fb = pullback.fst
                                  ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B
                                      fb).obj N.1)).obj.hom (geometricFibreProj B f'
                                          (liftedGeometricPoint B y
                                              y₀) hy) ≫ pullback.fst ((smallEtaleBaseChange B
                                                  fb).obj N.1).obj.hom jb ≫ pullback.fst
                                                      N.1.obj.hom fb :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst ((smallEtaleBaseChange B
            fb).obj N.1).obj.hom jb ≫ pullback.fst N.1.obj.hom fb) n1).trans
          ((Category.assoc _ _ _).trans (congrArg (pullback.fst ((smallEtaleBaseChange B jb).obj
              ((smallEtaleBaseChange B fb).obj
                  N.1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) ≫ ·)
                      (Category.id_comp _))))
      have sC : ((smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
          hy)).map ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app (compNeighborhood B y
              i₀ y₀ hy₀ N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app
                N.1).symm).hom)).hom.left ≫ pullback.fst ((smallEtaleBaseChange B jb).obj
                    ((smallEtaleBaseChange B fb).obj
                        N.1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy) ≫
                            pullback.fst ((smallEtaleBaseChange B fb).obj
                                N.1).obj.hom jb ≫ pullback.fst N.1.obj.hom fb = pullback.fst
                                    ((smallEtaleBaseChange B j').obj ((smallEtaleBaseChange B
                                        f).obj (compNeighborhood B y i₀ y₀ hy₀ N).1)).obj.hom
                                            (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
                                                hy) ≫ ((smallEtaleBaseChange_compIso B X' X Y j'
                                                    f).val.hom.app (compNeighborhood B y i₀ y₀ hy₀
                                                        N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app
                N.1).symm).hom).hom.left ≫ pullback.fst ((smallEtaleBaseChange B fb).obj
                    N.1).obj.hom jb ≫ pullback.fst N.1.obj.hom fb :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst ((smallEtaleBaseChange B
            fb).obj N.1).obj.hom jb ≫ pullback.fst N.1.obj.hom fb) n2).trans
          (Category.assoc _ _ _))
      have sD : ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app (compNeighborhood B y i₀
          y₀ hy₀ N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app
                N.1).symm).hom).hom.left ≫
          pullback.fst ((smallEtaleBaseChange B fb).obj N.1).obj.hom jb ≫
            pullback.fst N.1.obj.hom fb =
          pullback.fst ((smallEtaleBaseChange B f).obj (compNeighborhood B y i₀ y₀ hy₀
              N).1).obj.hom j' ≫
            pullback.fst (compNeighborhood B y i₀ y₀ hy₀ N).1.obj.hom f :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) g3).trans g4))).trans g5)
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
      refine (lift_chain_aux (baseChangeFinalIso B (openFibreMap B f y hy i₀ j' f' hf' y₀
          hy₀)).inv.hom.left
        ((smallEtaleBaseChange B (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).map
            (geometricFibreLift B f y hy (compNeighborhood B y i₀ y₀ hy₀ N))).hom.left
        ((smallEtaleBaseChange_factoredCompIso B _ _ X (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
            (geometricFibreProj B f y hy)
        (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j') (openFibreMap_proj B f y
            hy i₀ j' f' hf' y₀ hy₀)).hom.app ((smallEtaleBaseChange B f).obj (compNeighborhood B y
                i₀ y₀ hy₀ N).1)).hom.left ((smallEtaleBaseChange_factoredCompIso B _ X' X
                    (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
                        hy) j' (geometricFibreProj B f' (liftedGeometricPoint B y
                            y₀) hy ≫ j') rfl).inv.app ((smallEtaleBaseChange B f).obj
                                (compNeighborhood B y i₀ y₀ hy₀ N).1)).hom.left
        ((smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).map
            ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app (compNeighborhood B y i₀ y₀
                hy₀ N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app
                N.1).symm).hom)).hom.left
        ((smallEtaleBaseChange B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy)).map
            (𝟙 ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj N.1)))).hom.left
        ((smallEtaleBaseChange_factoredCompIso B _ X' Xb (geometricFibreProj B f'
            (liftedGeometricPoint B y y₀) hy) jb (geometricFibreProj B f' (liftedGeometricPoint B
                y y₀) hy ≫ jb) rfl).hom.app ((smallEtaleBaseChange B fb).obj N.1)).hom.left
        (pullback.fst ((smallEtaleBaseChange B fb).obj N.1).obj.hom (geometricFibreProj B f'
            (liftedGeometricPoint B y y₀) hy ≫ jb)) (pullback.fst N.1.obj.hom fb)
        (pullback.fst ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj
            N.1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy))
                (pullback.fst ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj
                    N.1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy))
        (pullback.fst ((smallEtaleBaseChange B fb).obj N.1).obj.hom jb) (pullback.fst
            ((smallEtaleBaseChange B j').obj ((smallEtaleBaseChange B f).obj (compNeighborhood B y
                i₀ y₀ hy₀ N).1)).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀)
                    hy)) ((smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app
                        (compNeighborhood B y i₀ y₀ hy₀ N).1 ≫
          ((neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
            ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app
                N.1).symm).hom).hom.left
        (pullback.fst ((smallEtaleBaseChange B f).obj (compNeighborhood B y i₀ y₀ hy₀
            N).1).obj.hom j') (pullback.fst (compNeighborhood B y i₀ y₀ hy₀ N).1.obj.hom f)
        (pullback.fst ((smallEtaleBaseChange B f).obj (compNeighborhood B y i₀ y₀ hy₀
            N).1).obj.hom (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy ≫ j'))
                (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)
        (geometricFibreToNeighborhood B f y hy (compNeighborhood B y i₀ y₀ hy₀
            N)) (geometricFibreStruct B f y hy)
        (neighborhoodPointHom B y hy (compNeighborhood B y i₀ y₀ hy₀ N)) (geometricFibreStruct B
            f' (liftedGeometricPoint B y y₀) hy)
        g1 (n1.trans (Category.comp_id _)) n2 sD g2 hP g6 g8).trans ?_
      exact (congrArg (· ≫ _) g9.symm).trans ((Category.assoc _ _ _).trans
        (congrArg ((compFibreMap B y hy f' jb fb hfb y₀) ≫ ·) g7.symm))
    · exact (final_baseChange_fst_snd B (geometricFibreProj B f' (liftedGeometricPoint B y y₀) hy
        ≫ jb) fb N.1 _).trans
        ((compFibreMap_proj B y hy f' jb fb hfb y₀).symm.trans
          ((congrArg ((compFibreMap B y hy f' jb fb hfb y₀) ≫ ·) (geometricFibreToNeighborhood_snd
              B fb (liftedGeometricPoint B y y₀) hy N)).symm.trans
            (Category.assoc _ _ _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans hR)

include hfb in
omit [IsOpenImmersion (B.inclusion.map j')] in
/-- Transporting a section of `j̄_!(F|_{X'})` over the base change of `N` to `X' ×_Y N` gives a
section with support proper over `N`, since `X̄` is proper over `Y₀`. -/
theorem properSupportSections_compactification [IsProper (B.inclusion.map fb)]
    [LocallyOfFiniteType (B.inclusion.map (j' ≫ f))]
    (Nw : SmallEtale B Y₀.obj Y₀.property)
    (s : (compactificationSheaf B j' jb F).obj.obj (op ((smallEtaleBaseChange B fb).obj Nw))) :
    properSupportSections B (j' ≫ f) ((abPullback.{u, v} B j').obj F)
      ((openPostcompose B i₀).obj Nw)
      (((abPullback.{u, v} B j').obj F).obj.map ((neighborhoodIso B f i₀ j' f' hf' Nw).symm ≪≫
        ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app Nw).symm).hom.op
          s.1) := by
  let H := (abPullback.{u, v} B j').obj F
  let φ := (neighborhoodIso B f i₀ j' f' hf' Nw).symm ≪≫
    ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app Nw).symm
  let P₁ := B.inclusion.map (baseChangeObjProjection B jb ((smallEtaleBaseChange B fb).obj Nw))
  let P₂ := B.inclusion.map (baseChangeObjProjection B fb Nw)
  have h₂ : IsProper P₂ :=
    MorphismProperty.of_isPullback ((isPullback_baseChangeObjProjection B fb Nw).flip.map
        B.inclusion)
      inferInstance
  have h₁ : LocallyOfFiniteType P₁ :=
    locallyOfFiniteType_baseChangeProjection B jb ((smallEtaleBaseChange B fb).obj Nw)
  have : LocallyOfFiniteType (P₁ ≫ P₂) := inferInstance
  have hs : IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (zeroOpen B X'.obj X'.property H ((smallEtaleBaseChange B jb).obj
        ((smallEtaleBaseChange B fb).obj Nw)) s.1).compl).subschemeι ≫ P₁) := s.2
  have hZ : IsProperOver (P₁ ≫ P₂) (zeroOpen B X'.obj X'.property H
      ((smallEtaleBaseChange B jb).obj ((smallEtaleBaseChange B fb).obj Nw)) s.1).compl := by
    show IsProper (_ ≫ P₁ ≫ P₂)
    rw [← Category.assoc]
    infer_instance
  have hφ : φ.hom.hom.left ≫ baseChangeObjProjection B jb ((smallEtaleBaseChange B fb).obj Nw) ≫
      baseChangeObjProjection B fb Nw =
      pullback.fst ((openPostcompose B i₀).obj Nw).obj.hom (j' ≫ f) := by
    have g3 := factoredCompIso_inv_app_fst B jb fb f' hfb Nw
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) g3).trans
      (inv_hom_left_comp B _ _ _ (neighborhoodIso_hom_fst B f i₀ j' f' hf' Nw)))
  have he : ((SmallEtale.toScheme B X'.obj X'.property).mapIso φ).hom ≫ (P₁ ≫ P₂) =
      B.inclusion.map (pullback.fst ((openPostcompose B i₀).obj Nw).obj.hom (j' ≫ f)) :=
    (congrArg (B.inclusion.map φ.hom.hom.left ≫ ·) (B.inclusion.map_comp _ _).symm).trans
      ((B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hφ))
  have hT := isProperOver_preimage_of_iso ((SmallEtale.toScheme B X'.obj X'.property).mapIso φ)
    _ _ he _ hZ
  have hZeq : (zeroOpen B X'.obj X'.property H ((smallEtaleBaseChange B (j' ≫ f)).obj
      ((openPostcompose B i₀).obj Nw)) (H.obj.map φ.hom.op s.1)).compl =
      (zeroOpen B X'.obj X'.property H ((smallEtaleBaseChange B jb).obj
        ((smallEtaleBaseChange B fb).obj Nw)) s.1).compl.preimage
        ((SmallEtale.toScheme B X'.obj X'.property).mapIso φ).hom.continuous := by
    apply TopologicalSpace.Closeds.ext
    exact supportSection_map B X'.obj X'.property H _ _ φ.hom s.1
  have : LocallyOfFiniteType (B.inclusion.map (pullback.fst ((openPostcompose B i₀).obj Nw).obj.hom
      (j' ≫ f))) := locallyOfFiniteType_baseChangeProjection B (j' ≫ f) _
  show IsProperOver (B.inclusion.map (pullback.fst ((openPostcompose B i₀).obj Nw).obj.hom
    (j' ≫ f))) _
  rw [hZeq]
  exact hT

include hfb in
/-- **The reduction of Stacks 0F76 surjectivity to a compactification.** Suppose that `X'` is an
open subscheme of `X` mapping into an open subscheme `Y₀` of `Y` through which `ȳ` factors, that
`X' ⟶ Y₀` factors as an open immersion into `X̄` followed by a proper `X̄ ⟶ Y₀`, and that
compactly supported sections of `j̄_!(F|_{X'})` on the geometric fibre of `X̄ ⟶ Y₀` come from
étale neighbourhoods (proper base change in degree `0`). Then every compactly supported section
of `F` on `X_ȳ` supported in `X'_ȳ` lies in the image of `(f_!F)_ȳ`. -/
theorem exists_fShriekStalkToCompactSections_eq_of_compactification
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    [IsProper (B.inclusion.map fb)]
    (hPBC : ∀ t' : geometricFibreSections B fb (liftedGeometricPoint B y y₀) hy
        (compactificationSheaf B j' jb F),
      ∃ (N : (geometricPointFiber B Y₀.obj Y₀.property (liftedGeometricPoint B y y₀)).Elements)
        (s : (compactificationSheaf B j' jb F).obj.obj (op ((smallEtaleBaseChange B fb).obj N.1))),
        geometricFibreRestriction B fb (liftedGeometricPoint B y y₀) hy
          (compactificationSheaf B j' jb F) N s = t')
    (t : geometricFibreCompactSections B f y hy F)
    (ht : supportSection B (geometricFibreObj B f y hy).obj (geometricFibreObj B f y hy).property
        (geometricFibreSheaf B f y hy F) (SmallEtale.final B _ _) t.1 ⊆
      Set.range (B.inclusion.map (openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀)).base) :
    ∃ g, fShriekStalkToCompactSections B f y hy F g = t := by
  have : LocallyOfFiniteType (B.inclusion.map f') := by
    rw [← hfb, Functor.map_comp]; infer_instance
  have : IsSeparated (B.inclusion.map fb) := inferInstance
  have : LocallyOfFiniteType (B.inclusion.map fb) := inferInstance
  let y' := liftedGeometricPoint B y y₀
  let k := y.residueField
  let mO := openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀
  let jQ := compFibreMap B y hy f' jb fb hfb y₀
  let G := compactificationSheaf B j' jb F
  let Fy := geometricFibreSheaf B f y hy F
  let GQ := geometricFibreSheaf B fb y' hy G
  have : IsSeparated (B.inclusion.map (geometricFibreStruct B fb y' hy)) :=
    isSeparated_geometricFibreStruct B fb y' hy
  have : LocallyOfFiniteType (B.inclusion.map (geometricFibreStruct B fb y' hy)) :=
    locallyOfFiniteType_geometricFibreStruct B fb y' hy
  have : LocallyOfFiniteType (B.inclusion.map jQ ≫
      B.inclusion.map (geometricFibreStruct B fb y' hy)) := inferInstance
  -- Step 1: restrict `t` to `X'_ȳ` (Stacks 0F74).
  obtain ⟨t₁, ht₁⟩ := (exists_compactlySupportedSections_openInclusion_eq k B mO
    (B.inclusion.map (geometricFibreStruct B f y hy)) Fy t).2 ht
  -- Step 2: transport to `j̄_!(F|_{X'})` and extend by zero to `X̄_ȳ` (Stacks 0F74).
  let Ψ := fibreComparison B f y hy i₀ j' f' hf' jb fb hfb y₀ hy₀ F
  have hstr : B.inclusion.map mO ≫ B.inclusion.map (geometricFibreStruct B f y hy) =
      B.inclusion.map jQ ≫ B.inclusion.map (geometricFibreStruct B fb y' hy) := by
    rw [← Functor.map_comp, ← Functor.map_comp, openFibreMap_struct, compFibreMap_struct]
  have ht₂ : Ψ.hom.app (op (SmallEtale.final B _ _)) t₁.1 ∈
      compactlySupportedSections k (geometricFibreObj B f' y' hy).obj
        (B.inclusion.map jQ ≫ B.inclusion.map (geometricFibreStruct B fb y' hy)) B
        (geometricFibreObj B f' y' hy).property ((abPullback.{u, v} B jQ).obj GQ) := by
    have h := t₁.2
    rw [mem_compactlySupportedSections] at h ⊢
    have hs : zeroOpen B _ _ ((abPullback.{u, v} B jQ).obj GQ) (SmallEtale.final B _ _)
        (Ψ.hom.app (op (SmallEtale.final B _ _)) t₁.1) =
        zeroOpen B _ _ ((abPullback.{u, v} B mO).obj Fy) (SmallEtale.final B _ _) t₁.1 :=
      zeroOpen_sheafIso B _ _ (asIso Ψ) _ t₁.1
    rw [hs]
    show IsProper (_ ≫ _)
    rw [← hstr]
    exact h
  let t₂ : compactlySupportedSections k (geometricFibreObj B f' y' hy).obj
      (B.inclusion.map jQ ≫ B.inclusion.map (geometricFibreStruct B fb y' hy)) B
      (geometricFibreObj B f' y' hy).property ((abPullback.{u, v} B jQ).obj GQ) := ⟨_, ht₂⟩
  let t' := (compactlySupportedSections_openInclusion k B jQ
    (B.inclusion.map (geometricFibreStruct B fb y' hy)) GQ).1 t₂
  -- Step 3: proper base change.
  obtain ⟨N, s, hs⟩ := hPBC t'.1
  -- Step 4: the section of `f_!F` over the neighbourhood `N` viewed over `Y`.
  let N' := compNeighborhood B y i₀ y₀ hy₀ N
  let V' := N'.1
  let W := (smallEtaleBaseChange B fb).obj N.1
  let F' := (abPullback.{u, v} B j').obj F
  let φN : (smallEtaleBaseChange B (j' ≫ f)).obj V' ≅ (smallEtaleBaseChange B jb).obj W :=
    (neighborhoodIso B f i₀ j' f' hf' N.1).symm ≪≫
      ((smallEtaleBaseChange_factoredCompIso B X' Xb Y₀ jb fb f' hfb).app N.1).symm
  have : LocallyOfFiniteType (B.inclusion.map (j' ≫ f)) := by
    rw [Functor.map_comp]; infer_instance
  have hσ' : properSupportSections B (j' ≫ f) F' V' (F'.obj.map φN.hom.op s.1) :=
    properSupportSections_compactification B f i₀ j' f' hf' jb fb hfb F N.1 s
  let σ' : (properSupportSheaf B (j' ≫ f) F').obj.obj (op V') := ⟨_, hσ'⟩
  let α := (openInclusionShriekMap B j' f F).1
  let a := α.hom.app (op V') σ'
  refine ⟨etaleGerm B Y.obj Y.property y _ N'.1 N'.2 a, Subtype.ext ?_⟩
  refine (fShriekStalkToCompactSections_germ B f y hy F N' a).trans ?_
  -- Step 5: compare on `X'_ȳ`.
  let σa := (properSupportSheafInclusion B f F).hom.app (op N'.1) a
  have hres_t : restrictGlobal B mO Fy t.1 = t₁.1 := by
    rw [← ht₁]
    exact restrictGlobal_openInclusion k B mO Fy
      (B.inclusion.map (geometricFibreStruct B f y hy)) t₁
  have hres_t' : restrictGlobal B jQ GQ t'.1 = Ψ.hom.app _ t₁.1 :=
    restrictGlobal_openInclusion k B jQ GQ (B.inclusion.map (geometricFibreStruct B fb y' hy)) t₂
  have hKEY : Ψ.hom.app (op (SmallEtale.final B _ _))
      (restrictGlobal B mO Fy (geometricFibreRestriction B f y hy F N' σa)) =
      restrictGlobal B jQ GQ (geometricFibreRestriction B fb y' hy G N s) := by
    let W' := (smallEtaleBaseChange B f).obj V'
    let ℓ₁ := (baseChangeFinalIso B mO).inv ≫ (smallEtaleBaseChange B mO).map
        (geometricFibreLift B f y hy N') ≫
      (smallEtaleBaseChange_factoredCompIso B _ _ X mO (geometricFibreProj B f y hy)
        (geometricFibreProj B f' y' hy ≫ j') (openFibreMap_proj B f y hy i₀ j' f' hf' y₀
            hy₀)).hom.app
          W' ≫
      (smallEtaleBaseChange_factoredCompIso B _ X' X (geometricFibreProj B f' y' hy) j'
        (geometricFibreProj B f' y' hy ≫ j') rfl).inv.app W'
    let c := (smallEtaleBaseChange_compIso B X' X Y j' f).val.hom.app V' ≫ φN.hom
    have hchar := ((openInclusionShriekMap B j' f F).2.2 V' σ').1
    have h1 := fibreComparisonF_restrict B f y hy i₀ j' f' hf' y₀ hy₀ F N' σa
    have hlift : (ℓ₁ ≫ (smallEtaleBaseChange B (geometricFibreProj B f' y' hy)).map c) ≫
        (smallEtaleBaseChange B (geometricFibreProj B f' y' hy)).map (𝟙 _) ≫
          (smallEtaleBaseChange_factoredCompIso B _ X' Xb (geometricFibreProj B f' y' hy) jb
            (geometricFibreProj B f' y' hy ≫ jb) rfl).hom.app W =
        (baseChangeFinalIso B jQ).inv ≫ (smallEtaleBaseChange B jQ).map
          (geometricFibreLift B fb y' hy N) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ Xb jQ (geometricFibreProj B fb y' hy)
            (geometricFibreProj B f' y' hy ≫ jb) (compFibreMap_proj B y hy f' jb fb hfb y₀)).hom.app
              W := by
      exact compactificationLift_eq B f y hy i₀ j' f' hf' jb fb hfb y₀ hy₀ N
    have h2 := fibreComparisonG_pullback B y hy j' f' jb fb hfb y₀ F W
      (ℓ₁ ≫ (smallEtaleBaseChange B (geometricFibreProj B f' y' hy)).map c) s
    have h3 := restrict_compFibre B y hy j' f' jb fb hfb y₀ F N s
    have hu : abPullbackUnit.{u, v} B j' F W' σa = F'.obj.map c.op s.1 := by
      refine hchar.symm.trans ?_
      exact (ConcreteCategory.congr_hom (F'.obj.map_comp _ _) _).symm
    have hstep : pullbackSectionAlongHom B (geometricFibreProj B f' y' hy)
        AddCommGrpCat.{max (u + 1) v} F' ((smallEtaleBaseChange B j').obj W')
        (SmallEtale.final B _ _) ℓ₁ (abPullbackUnit.{u, v} B j' F W' σa) =
        pullbackSectionAlongHom B (geometricFibreProj B f' y' hy)
        AddCommGrpCat.{max (u + 1) v} F' ((smallEtaleBaseChange B jb).obj W)
        (SmallEtale.final B _ _) (ℓ₁ ≫ (smallEtaleBaseChange B (geometricFibreProj B f' y'
            hy)).map c)
        s.1 := by
      rw [hu, pullbackSectionAlongHom_map]
    show (fibreComparisonG B y hy j' f' jb fb hfb y₀ F).hom.hom.app _
      ((fibreComparisonF B f y hy i₀ j' f' hf' y₀ hy₀ F).hom.hom.app _
        (restrictGlobal B mO Fy (geometricFibreRestriction B f y hy F N' σa))) = _
    refine (congrArg _ (h1.trans hstep)).trans ?_
    refine h2.trans ?_
    rw [hlift]
    refine Eq.trans ?_ (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
      (op (SmallEtale.final B _ _))) ((smallEtaleSheafPullbackFactoredCompIso B _ _ Xb jQ
        (geometricFibreProj B fb y' hy) (geometricFibreProj B f' y' hy ≫ jb)
        (compFibreMap_proj B y hy f' jb fb hfb y₀) AddCommGrpCat.{max (u + 1) v}).hom_inv_id_app
          G)) _)
    exact congrArg _ h3.symm
  have hsupp : supportSection B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property Fy (SmallEtale.final B _ _)
      (geometricFibreRestriction B f y hy F N' σa) ⊆ Set.range (B.inclusion.map mO).base := by
    have hchar2 := ((openInclusionShriekMap B j' f F).2.2 V' σ').2
    have hsub := supportSection_pullbackSectionAlongHom_subset.{u, v} B (geometricFibreProj B f y
        hy)
      F ((smallEtaleBaseChange B f).obj V') (SmallEtale.final B _ _) (geometricFibreLift B f y hy
          N')
      σa
    have hrange := range_eq_preimage_range_of_isPullback
      ((isPullback_openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀).map B.inclusion)
    intro z hz
    have hz' := hsub hz
    show z ∈ Set.range (B.inclusion.map mO).base
    rw [hrange]
    rw [Set.mem_preimage] at hz'
    obtain ⟨u, -, hu⟩ := (Set.ext_iff.1 hchar2 _).1 hz'
    have e1 : (SmallEtale.toScheme B _ _).map (geometricFibreLift B f y hy N') ≫
        B.inclusion.map (baseChangeObjProjection B (geometricFibreProj B f y hy)
          ((smallEtaleBaseChange B f).obj V')) =
        B.inclusion.map (geometricFibreToNeighborhood B f y hy N') :=
      (B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (geometricFibreLift_proj B f y hy N'))
    have e2 : B.inclusion.map (geometricFibreToNeighborhood B f y hy N') ≫
        B.inclusion.map (pullback.snd V'.obj.hom f) = B.inclusion.map (geometricFibreProj B f y
            hy) :=
      (B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (geometricFibreToNeighborhood_snd B f y hy N'))
    have e3 : B.inclusion.map (pullback.fst ((smallEtaleBaseChange B f).obj V').obj.hom j') ≫
        B.inclusion.map (pullback.snd V'.obj.hom f) =
        B.inclusion.map (pullback.snd ((smallEtaleBaseChange B f).obj V').obj.hom j') ≫
          B.inclusion.map j' :=
      (B.inclusion.map_comp _ _).symm.trans ((congrArg B.inclusion.map pullback.condition).trans
        (B.inclusion.map_comp _ _))
    refine ⟨(B.inclusion.map (pullback.snd ((smallEtaleBaseChange B f).obj V').obj.hom j')).base u,
      ?_⟩
    have k1 := congrArg (fun m => m.base u) e3
    have k2 := congrArg (fun m => m.base z) e2
    have k3 := congrArg (fun m => m.base z) e1
    have k4 := congrArg (B.inclusion.map (pullback.snd V'.obj.hom f)).base hu
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at k1 k2 k3
    exact k1.symm.trans (k4.trans ((congrArg _ k3).trans k2))
  refine eq_of_restrictGlobal_eq B mO Fy _ _ hsupp ht ?_
  have hinj : Function.Injective (Ψ.hom.app (op (SmallEtale.final B
      (geometricFibreObj B f' y' hy).obj (geometricFibreObj B f' y' hy).property))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  rw [hKEY, hs, hres_t', hres_t]

end Compactification

/-- **The surjectivity half of Stacks 0F76, reduced to proper base change in degree `0`.** Let
`f : X ⟶ Y` be separated and locally of finite type and let `ȳ` be a geometric point of `Y` whose
spectrum lies in the site. Suppose that for every proper morphism `f' : X' ⟶ Y'` of the site,
every compactly supported section on a geometric fibre of `f'` comes from an étale
neighbourhood (proper base change in degree `0`). Then the canonical map
`(f_!F)_ȳ ⟶ H⁰_c(X_ȳ, F|_{X_ȳ})` is surjective.

As in the proof of the source, a compactly supported section on `X_ȳ` is supported inside the
geometric fibre of a quasi-compact open `X' ⊆ X` lying over an affine open `Y₀ ⊆ Y` through
which `ȳ` factors; Nagata's compactification theorem (Stacks 0F41) embeds `X' ⟶ Y₀` into a
proper `X̄ ⟶ Y₀`, and the section is produced through the extension by zero of `F|_{X'}` to `X̄`
(`AlgebraicGeometry.SmallEtale.exists_fShriekStalkToCompactSections_eq_of_compactification`). -/
theorem fShriekStalkToCompactSections_surjective_of_properBaseChange (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] (y : GeometricPoint Y.obj)
    (hy : B.Contains y.source)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (hPBC : ∀ {X' Y' : B.Scheme} (f' : X' ⟶ Y') [IsProper (B.inclusion.map f')]
      (y' : GeometricPoint Y'.obj) (hy' : B.Contains y'.source)
      (F' : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v})
      (t : geometricFibreSections B f' y' hy' F'),
      ∃ (N : (geometricPointFiber B Y'.obj Y'.property y').Elements)
        (s : F'.obj.obj (op ((smallEtaleBaseChange B f').obj N.1))),
        geometricFibreRestriction B f' y' hy' F' N s = t) :
    Function.Surjective (fShriekStalkToCompactSections B f y hy F) := by
  intro t
  let p := geometricFibreProj B f y hy
  let st := geometricFibreStruct B f y hy
  have : CompactSpace (B.inclusion.obj (B.obj y.source hy)) :=
    (inferInstance : CompactSpace y.source)
  -- the support of `t` and its image in `X` are quasi-compact
  have hT : IsCompact (supportSection B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property (geometricFibreSheaf B f y hy F)
      (SmallEtale.final B _ _) t.1) :=
    isCompact_of_isProperOver (B.inclusion.map st) _ t.2
  let K := (B.inclusion.map p).base '' supportSection B (geometricFibreObj B f y hy).obj
      (geometricFibreObj B f y hy).property (geometricFibreSheaf B f y hy F)
      (SmallEtale.final B _ _) t.1
  have hK : IsCompact K := hT.image (B.inclusion.map p).base.hom.continuous
  -- an affine open of `Y` through which `ȳ` factors
  let y0pt := y.hom.base default
  obtain ⟨Y0, hY0a, hy0, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y0pt) trivial
  have hpt : ∀ a : y.source, y.hom.base a = y0pt := fun a => by
    rw [Subsingleton.elim a default]
  have hKY : K ⊆ (B.inclusion.map f).base ⁻¹' (Y0 : Set Y.obj) := by
    rintro _ ⟨z, -, rfl⟩
    have hc := congrArg (fun m => m.base z) (congrArg B.inclusion.map
      (pullback.condition : p ≫ f = st ≫ geometricPointHom B y hy))
    simp only [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app] at hc
    show (B.inclusion.map f).base ((B.inclusion.map p).base z) ∈ (Y0 : Set Y.obj)
    rw [hc]
    exact (hpt _).symm ▸ hy0
  -- a quasi-compact open of `X` containing the image of the support, lying over `Y₀`
  obtain ⟨Wset, hWc, hWo, hKW, hWY⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between hK
    (Y0.isOpen.preimage (B.inclusion.map f).base.hom.continuous) hKY
  let U : X.obj.Opens := ⟨Wset, hWo⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp hWc
  have : AlgebraicGeometry.IsAffine (Y0 : Scheme.{u}) := hY0a
  have hXU : B.Contains (U : Scheme.{u}) :=
    (Scheme.size_le_of_locallyOfFiniteType U.ι).trans_lt X.property
  have hY0 : B.Contains (Y0 : Scheme.{u}) :=
    (Scheme.size_le_of_locallyOfFiniteType Y0.ι).trans_lt Y.property
  let X' := B.obj (U : Scheme.{u}) hXU
  let Y₀ := B.obj (Y0 : Scheme.{u}) hY0
  let j' : X' ⟶ X := ObjectProperty.homMk U.ι
  let i₀ : Y₀ ⟶ Y := ObjectProperty.homMk Y0.ι
  have : IsOpenImmersion (B.inclusion.map j') := (inferInstance : IsOpenImmersion U.ι)
  have : IsOpenImmersion (B.inclusion.map i₀) := (inferInstance : IsOpenImmersion Y0.ι)
  have hrange : Set.range (U.ι ≫ B.inclusion.map f).base ⊆ Set.range Y0.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWY x.2
  let g := IsOpenImmersion.lift Y0.ι (U.ι ≫ B.inclusion.map f) hrange
  have hg : g ≫ Y0.ι = U.ι ≫ B.inclusion.map f := IsOpenImmersion.lift_fac _ _ _
  let f' : X' ⟶ Y₀ := ObjectProperty.homMk g
  have hf' : f' ≫ i₀ = j' ≫ f := ObjectProperty.hom_ext _ hg
  -- Nagata's compactification of `X' ⟶ Y₀`
  have : IsSeparated g := by
    have : IsSeparated (g ≫ Y0.ι) := by rw [hg]; infer_instance
    exact IsSeparated.of_comp g Y0.ι
  have : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ Y0.ι) := by rw [hg]; infer_instance
    exact locallyOfFiniteType_of_comp g Y0.ι
  obtain ⟨jc, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace g
  have hjf : jc.immersion ≫ jc.toBase = g := Over.w jc.obj.hom
  have : CompactSpace jc.space := QuasiCompact.compactSpace_of_compactSpace jc.toBase
  have hXb : B.Contains jc.space :=
    (Scheme.size_le_of_locallyOfFiniteType jc.toBase).trans_lt hY0
  let Xb := B.obj jc.space hXb
  let jb : X' ⟶ Xb := ObjectProperty.homMk jc.immersion
  let fb : Xb ⟶ Y₀ := ObjectProperty.homMk jc.toBase
  have : IsOpenImmersion (B.inclusion.map jb) := (inferInstance : IsOpenImmersion jc.immersion)
  have : IsProper (B.inclusion.map fb) := (inferInstance : IsProper jc.toBase)
  have hfb : jb ≫ fb = f' := ObjectProperty.hom_ext _ hjf
  -- the lift of `ȳ` to `Y₀`
  have hyr : Set.range y.hom.base ⊆ Set.range Y0.ι.base := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι, hpt a]
    exact hy0
  let y₀ := IsOpenImmersion.lift Y0.ι y.hom hyr
  have hy₀ : y₀ ≫ B.inclusion.map i₀ = y.hom := IsOpenImmersion.lift_fac _ _ _
  have key := exists_fShriekStalkToCompactSections_eq_of_compactification B f y hy i₀ j' f' hf'
    jb fb hfb y₀ hy₀ F (hPBC fb (liftedGeometricPoint B y y₀) hy (compactificationSheaf B j' jb F))
  refine key t (fun z hz => ?_)
  have hr := range_eq_preimage_range_of_isPullback
    ((isPullback_openFibreMap B f y hy i₀ j' f' hf' y₀ hy₀).map B.inclusion)
  have hzU : (B.inclusion.map p).base z ∈ Set.range (B.inclusion.map j').base := by
    show (B.inclusion.map p).base z ∈ Set.range U.ι.base
    rw [Scheme.Opens.range_ι]
    exact hKW ⟨z, hz, rfl⟩
  exact (Set.ext_iff.1 hr z).2 hzU

end AlgebraicGeometry.SmallEtale

end
