module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Descent of morphisms through a limit of affine schemes into a quasi-coherent module

Let `D` be a cofiltered diagram of affine schemes with limit cone `c`, let `F` be a sheaf of
modules of finite presentation on a stage `D.obj i` and let `G` be a **quasi-coherent** sheaf of
modules there.  Then a morphism between the pullbacks of `F` and `G` to the limit is, through the
canonical identifications, the pullback of a morphism at a later stage, and two morphisms
`F ⟶ G` whose pullbacks to the limit agree have equal pullbacks at a later stage.

These are the affine cases of [Stacks Project, Tag 01ZR] (2) and (3) with the hypothesis on the
target weakened from finite presentation to quasi-coherence.  The tag states both clauses for two
modules of finite presentation, which is what its colimit-of-categories reading needs; but its
proof, and the proofs of the affine case,
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine` and
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine`, use finiteness only of
the source: the reduction is to Algebra, Lemma 05LI, parts (1) and (3), whose target module is
arbitrary.  The weaker hypothesis is what Stacks 08K4 needs, where the target `𝒢` of the relative
Hom functor is only quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.AffineTilde.exists_iso_tildeOf_of_isQuasicoherent`: a quasi-coherent
  module on an affine scheme is the module associated to a module of global sections.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isAffine_of_isQuasicoherent`:
  the faithfulness clause, Tag 01ZR (3), with a quasi-coherent target.
* `Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_descend_of_isQuasicoherent`: the
  canonical equation of `Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_descend` for two
  quasi-coherent modules.
* `ModuleLimits.exists_map_of_pullback_canonical_of_isAffine_of_isQuasicoherent`:
  the fullness clause, Tag 01ZR (2), with the canonical identification and a quasi-coherent
  target.

## Implementation notes

The proofs are those of the finitely presented case.  The target enters only through the
quasi-coherence of its pullbacks, which is
`Stacks.Modules.isQuasicoherent_pullback` (Stacks 01BG), and through its being the module
associated to its global sections, which for a quasi-coherent module on a spectrum is
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.AffineTilde

/-- Every quasi-coherent sheaf of modules on an affine scheme is the module associated to a module
of global sections. -/
theorem exists_iso_tildeOf_of_isQuasicoherent (X : Scheme.{u}) [IsAffine X] (F : X.Modules)
    [hF : F.IsQuasicoherent] :
    ∃ M : ModuleCat.{u} Γ(X, ⊤), Nonempty ((tildeOf X).obj M ≅ F) := by
  let F' : (Spec Γ(X, ⊤)).Modules := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  have hqc : F'.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback _ F hF
  have hiso : IsIso (Scheme.Modules.fromTildeΓ F') :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ F' hqc
  let M : ModuleCat.{u} Γ(X, ⊤) := moduleSpecΓFunctor.obj F'
  let eF' : (tilde.functor Γ(X, ⊤)).obj M ≅ F' :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F') hiso
  refine ⟨M, ⟨?_⟩⟩
  refine (Scheme.Modules.pullback X.isoSpec.hom).mapIso eF' ≪≫ ?_
  exact (Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app F ≪≫
    (Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app F ≪≫
    (Scheme.Modules.pullbackId X).app F

end Stacks.AlgebraicGeometry.AffineTilde

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Stacks.AlgebraicGeometry.AffineTilde Stacks.ModuleCat
  Stacks.AlgebraicGeometry.SectionsBaseChange

/-- Two parallel maps of modules of global sections on an affine scheme `Y` become equal under
`Stacks.AlgebraicGeometry.AffineTilde.tildeOf` followed by pullback along a morphism `p : W ⟶ Y`
of affine schemes exactly when they become equal under base change along `p` on global sections.
Both directions are the naturality of
`Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIso` in the module argument, which turns the
pullback of `M~` into the tilde of the base change, together with the faithfulness of `tildeOf`. -/
private theorem pullback_map_tildeOf_map_eq_iff {W Y : Scheme.{u}} [IsAffine W] [IsAffine Y]
    (p : W ⟶ Y) {M N : ModuleCat.{u} Γ(Y, ⊤)} (v₁ v₂ : M ⟶ N) :
    (Scheme.Modules.pullback p).map ((tildeOf Y).map v₁)
          = (Scheme.Modules.pullback p).map ((tildeOf Y).map v₂)
      ↔ (ModuleCat.extendScalars (Scheme.Hom.appTop p).hom).map v₁
          = (ModuleCat.extendScalars (Scheme.Hom.appTop p).hom).map v₂ := by
  rw [← cancel_mono (tildeOfPullbackIsoApp p N).hom, tildeOfPullbackIsoApp_naturality p v₁,
    tildeOfPullbackIsoApp_naturality p v₂, cancel_epi (tildeOfPullbackIsoApp p M).hom]
  exact ⟨fun hv => (tildeOf W).map_injective hv, fun hv => by rw [hv]⟩

/-- The global sections of the stages over `i` of a cofiltered limit of affine schemes form a
filtered colimit with apex the global sections of the limit. -/
private theorem isColimit_mapCocone_whisker_op {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)] (i : I) :
    Nonempty (IsColimit (Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op)) := by
  have hl : IsLimit (c.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have : ∀ j : (Over i)ᵒᵖ, IsAffine ((Over.forget i ⋙ D).op.obj j).unop := by
    intro j; dsimp; infer_instance
  exact ⟨isColimitOfPreserves Scheme.Γ hl.op⟩

/-- The transition maps and the legs of the colimit of global sections over `i` are compatible
with the maps from the global sections of `D.obj i`. -/
private theorem appTop_compat_whisker_op {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) :
    (∀ {l m : (Over i)ᵒᵖ} (e : l ⟶ m) (x : Γ(D.obj i, ⊤)),
      ((Over.forget i ⋙ D).op ⋙ Scheme.Γ).map e ((D.map l.unop.hom).appTop x)
        = (D.map m.unop.hom).appTop x) ∧
    ∀ (l : (Over i)ᵒᵖ) (x : Γ(D.obj i, ⊤)),
      (Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op).ι.app l
          ((D.map l.unop.hom).appTop x) = (c.π.app i).appTop x := by
  refine ⟨fun {l m} e x => ?_, fun l x => ?_⟩
  · change (D.map e.unop.left).appTop ((D.map l.unop.hom).appTop x) = (D.map m.unop.hom).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← D.map_comp, Over.w e.unop]
  · change (c.π.app l.unop.left).appTop ((D.map l.unop.hom).appTop x) = (c.π.app i).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w l.unop.hom]

section Faithfulness

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]

include hc in
/-- **Stacks Project, Tag 01ZR (3)** for a cofiltered diagram of affine schemes, with a
quasi-coherent target: two morphisms from a module of finite presentation to a quasi-coherent
module on a stage whose pullbacks to the limit agree already have equal pullbacks to a later
stage. -/
theorem exists_pullback_map_eq_of_isAffine_of_isQuasicoherent (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsQuasicoherent]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Scheme.Modules.pullback (D.map e)).map ψ₁ =
        (Scheme.Modules.pullback (D.map e)).map ψ₂ := by
  classical
  obtain ⟨M, hM, ⟨eF⟩⟩ := exists_iso_tildeOf (D.obj i) F
  obtain ⟨N, ⟨eG⟩⟩ := exists_iso_tildeOf_of_isQuasicoherent (D.obj i) G
  set T := tildeOf (D.obj i) with hT
  set v₁ : M ⟶ N := T.preimage (eF.hom ≫ ψ₁ ≫ eG.inv) with hv₁
  set v₂ : M ⟶ N := T.preimage (eF.hom ≫ ψ₂ ≫ eG.inv) with hv₂
  have hTv₁ : T.map v₁ = eF.hom ≫ ψ₁ ≫ eG.inv := T.map_preimage _
  have hTv₂ : T.map v₂ = eF.hom ≫ ψ₂ ≫ eG.inv := T.map_preimage _
  have key : (Scheme.Modules.pullback (c.π.app i)).map (T.map v₁) =
      (Scheme.Modules.pullback (c.π.app i)).map (T.map v₂) := by
    rw [hTv₁, hTv₂]; simp only [Functor.map_comp, h]
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have key2 : (ModuleCat.extendScalars (Scheme.Hom.appTop (c.π.app i)).hom).map v₁ =
      (ModuleCat.extendScalars (Scheme.Hom.appTop (c.π.app i)).hom).map v₂ :=
    (pullback_map_tildeOf_map_eq_iff (W := c.pt) (Y := D.obj i) (c.π.app i) v₁ v₂).mp key
  -- the global sections of the stages over `i` form a filtered colimit with apex `Γ(c.pt, ⊤)`
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget i ⋙ D).op ⋙ Scheme.Γ with hE
  set d : Cocone E := Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op with hddef
  obtain ⟨hd⟩ := isColimit_mapCocone_whisker_op D c hc i
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (E.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := ((c.π.app i).appTop).hom.toAlgebra
  obtain ⟨ha, haR⟩ := appTop_compat_whisker_op D c i
  -- descend the equality at the ring level
  have hfin : Module.Finite Γ(D.obj i, ⊤) M := by have := hM; infer_instance
  have hbc : LinearMap.baseChange d.pt v₁.hom = LinearMap.baseChange d.pt v₂.hom :=
    ModuleCat.hom_ext_iff.mp key2
  obtain ⟨l, hl⟩ :=
    Stacks.RingFilteredColimits.exists_baseChange_eq haR ha hd M N v₁.hom v₂.hom hbc
  refine ⟨l.unop.left, l.unop.hom, ?_⟩
  have step : (Scheme.Modules.pullback (D.map l.unop.hom)).map (T.map v₁) =
      (Scheme.Modules.pullback (D.map l.unop.hom)).map (T.map v₂) :=
    (pullback_map_tildeOf_map_eq_iff (W := D.obj l.unop.left) (Y := D.obj i)
      (D.map l.unop.hom) v₁ v₂).mpr (ModuleCat.hom_ext hl)
  rw [hTv₁, hTv₂] at step
  simp only [Functor.map_comp] at step
  rw [← cancel_epi ((Scheme.Modules.pullback (D.map l.unop.hom)).map eF.hom),
    ← cancel_mono ((Scheme.Modules.pullback (D.map l.unop.hom)).map eG.inv)]
  simpa using step

end Faithfulness

/-! ### The canonical equation for quasi-coherent modules -/

/-- **The canonical equation, for two quasi-coherent modules.**  A morphism at the intermediate
stage whose map of global sections is the base change of a map `ul` of modules has the property
that its pullback to `W` becomes the given morphism `φ` under the canonical identifications, as
soon as `ul` and `φ` are compatible in the sense the colimit of rings produces.  This is
`Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_descend` with finite presentation of the
two modules weakened to quasi-coherence, which is all its proof uses. -/
theorem canonical_eq_of_descend_of_isQuasicoherent {W Z X : Scheme.{u}} [IsAffine W]
    [IsAffine Z] [IsAffine X] (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]
    [((Scheme.Modules.pullback g).obj G).IsQuasicoherent]
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    (φj : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤)) ⟶
        (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤)))
    (hφj : (bcTop g F).hom ≫ appTopHom φj = ul ≫ (bcTop g G).hom)
    (hu : (ModuleCat.extendScalars (Scheme.Hom.appTop q).hom).map ul ≫
          (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
              (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
              (ModuleCat.of Γ(X, ⊤) ↑Γ(G, ⊤))).hom ≫ (bcTop pi G).hom
        = (cancelIsoApp (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom
              (Scheme.Hom.appTop pi).hom (hp_triangle q g pi hpi)
              (ModuleCat.of Γ(X, ⊤) ↑Γ(F, ⊤))).hom ≫ (bcTop pi F).hom ≫ appTopHom φ) :
    (Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G
      = canHom q g pi hpi F ≫ φ := by
  have hqcsrc : ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback g).obj F)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback q _ inferInstance
  have hqctgt : ((Scheme.Modules.pullback pi).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback pi G inferInstance
  have key : (xiTop q g F).hom ≫
        appTopHom ((Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G)
      = (xiTop q g F).hom ≫ appTopHom (canHom q g pi hpi F ≫ φ) := by
    rw [appTopHom_comp, appTopHom_comp,
      reassoc_of% (xiTop_comp_map q g F G φj ul hφj),
      xiTop_comp_canHom q g pi hpi G, hu,
      reassoc_of% (xiTop_comp_canHom q g pi hpi F)]
  have h2 : appTopHom ((Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi G)
      = appTopHom (canHom q g pi hpi F ≫ φ) := (cancel_epi (xiTop q g F).hom).mp key
  exact hom_ext_of_app_top (fun z => congrArg (fun k => (ConcreteCategory.hom k) z) h2)

/-! ### Tag 01ZR (2) for a cofiltered diagram of affine schemes, into a quasi-coherent module -/

section Fullness

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]

include hc in
/-- **Stacks Project, Tag 01ZR (2)** for a cofiltered diagram of affine schemes, with the
canonical identification and a quasi-coherent target: a morphism from the pullback to the limit
of a module of finite presentation on a stage to the pullback of a quasi-coherent module there is,
after passing to a later stage, the base change of a morphism there, the base change being taken
through `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr`. -/
theorem exists_map_of_pullback_canonical_of_isAffine_of_isQuasicoherent (i : I)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsQuasicoherent]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hqF : F.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation F
  -- the global sections of the stages over `i` form a filtered colimit with apex `Γ(c.pt, ⊤)`
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget i ⋙ D).op ⋙ Scheme.Γ with hE
  set d : Cocone E := Scheme.Γ.mapCocone (c.whisker (Over.forget i)).op with hddef
  obtain ⟨hd⟩ := isColimit_mapCocone_whisker_op D c hc i
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (E.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := ((c.π.app i).appTop).hom.toAlgebra
  obtain ⟨ha, haR⟩ := appTop_compat_whisker_op D c i
  -- descend the map of global sections
  let pii : c.pt ⟶ D.obj i := c.π.app i
  have hMfp : Module.FinitePresentation Γ(D.obj i, ⊤) ↑Γ(F, ⊤) := finitePresentation_sectionsTop F
  let u : (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop pii).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤)) :=
    (bcTop pii F).hom ≫ appTopHom φ ≫ (bcTop pii G).inv
  obtain ⟨l, ul, hul⟩ := Stacks.RingFilteredColimits.exists_descend_rTensor haR ha hd
    ↑Γ(F, ⊤) ↑Γ(G, ⊤) u.hom
  -- the stage
  let j := l.unop.left
  let e : j ⟶ i := l.unop.hom
  let g : D.obj j ⟶ D.obj i := D.map e
  let qq : c.pt ⟶ D.obj j := c.π.app j
  have hpi : qq ≫ g = pii := c.w e
  have hqcgF : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback g F hqF
  have hqcgG : ((Scheme.Modules.pullback g).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback g G inferInstance
  let ulM0 := ModuleCat.ofHom ul
  let ulM : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤)) := ulM0
  let vj := (bcTop g F).inv ≫ ulM ≫ (bcTop g G).hom
  obtain ⟨φj, hφj0⟩ := exists_hom_app_top_eq (X := D.obj j)
    (F := (Scheme.Modules.pullback g).obj F) (G := (Scheme.Modules.pullback g).obj G) vj.hom
  refine ⟨j, e, φj, ?_⟩
  -- the two inputs of `canonical_eq_of_descend_of_isQuasicoherent`
  have hφj : (bcTop g F).hom ≫ appTopHom φj = ulM ≫ (bcTop g G).hom := by
    have h1 : appTopHom φj = vj := ModuleCat.hom_ext (LinearMap.ext fun a => hφj0 a)
    rw [h1]
    change (bcTop g F).hom ≫ (bcTop g F).inv ≫ ulM ≫ (bcTop g G).hom = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hE : u ≫ (bcTop pii G).hom = (bcTop pii F).hom ≫ appTopHom φ := by
    change ((bcTop pii F).hom ≫ appTopHom φ ≫ (bcTop pii G).inv) ≫ (bcTop pii G).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hf : ∀ β : Γ(D.obj j, ⊤), Stacks.RingFilteredColimits.legAlgHom haR l β
      = (Scheme.Hom.appTop qq).hom β := fun _ => rfl
  have hul' : ∀ y : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
        (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)),
      u (LinearMap.rTensor (↑Γ(F, ⊤))
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap y)
        = LinearMap.rTensor (↑Γ(G, ⊤))
          (Stacks.RingFilteredColimits.legAlgHom haR l).toLinearMap (ulM y) := hul
  have hD := Stacks.ModuleCat.extendScalars_map_comp_cancelIsoApp
    (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop qq).hom
    (Scheme.Hom.appTop pii).hom (hp_triangle qq g pii hpi)
    (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤)) (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤))
    (Stacks.RingFilteredColimits.legAlgHom haR l) hf u ulM hul'
  have hu : (ModuleCat.extendScalars (Scheme.Hom.appTop qq).hom).map ulM ≫
        (Stacks.ModuleCat.cancelIsoApp (Scheme.Hom.appTop g).hom
            (Scheme.Hom.appTop qq).hom (Scheme.Hom.appTop pii).hom
            (hp_triangle qq g pii hpi)
            (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(G, ⊤))).hom ≫ (bcTop pii G).hom
      = (Stacks.ModuleCat.cancelIsoApp (Scheme.Hom.appTop g).hom
            (Scheme.Hom.appTop qq).hom (Scheme.Hom.appTop pii).hom
            (hp_triangle qq g pii hpi)
            (ModuleCat.of Γ(D.obj i, ⊤) ↑Γ(F, ⊤))).hom ≫
          (bcTop pii F).hom ≫ appTopHom φ := by
    rw [reassoc_of% hD, hE]
  exact canonical_eq_of_descend_of_isQuasicoherent qq g pii hpi F G φ φj ulM hφj hu

end Fullness

end Stacks.AlgebraicGeometry.ModuleLimits

end
