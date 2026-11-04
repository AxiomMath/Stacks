module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Maps of sheaves glue

Stacks tag 04TQ. Let `(C, J)` be a site and `A` a target category for sheaf values. For
`U : C` the slice site `C/U` is the over category `Over U` with the localized topology
`J.over U`, and the restriction `F|_{C/U}` of a sheaf `F : Sheaf J A` is
`(J.overPullback A U).obj F`, the sheaf pullback along `Over.forget U`. For a finer slice
`g : V ⟶ U` a further restriction `J.overMapPullback A g` is available, and the two agree
up to the coherence isomorphism `overPullbackOverMapPullbackIso`; `restrictHomAlong`
transports a map of restricted sheaves along `g` using it.

Given a covering `{ f i : U i ⟶ U }` in `J`, a family of maps
`φ i : F|_{C/U i} ⟶ G|_{C/U i}` agreeing on the overlaps `C/(U i ×_U U j)` glues to a
unique `ψ : F|_{C/U} ⟶ G|_{C/U}` restricting to each `φ i`; equivalently, restriction is
a bijection from `Hom(F|_{C/U}, G|_{C/U})` onto the compatible families. Overlaps are read
literally as `Limits.pullback (f i) (f j)` under `[HasPullbacks C]`, which agrees with the
slice-site phrasing whenever those fibre products exist.

## Main results

* `maps_of_sheaves_glue`: the `∃!` form of the gluing statement, assembled from
  `glued_existence` (whose glued map is `psi`, built by amalgamating over the pullback of
  the cover along each slice object) and `glued_uniqueness` (separatedness of `G`).
* `maps_of_sheaves_glue_bijective`: the bijection form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology Limits

namespace Stacks.SheafMapGluing

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable {A : Type*} [Category A]

/-- **Definition 3 (compatibility of restrictions).**
For `g : X ⟶ Y` in `C`, restricting a sheaf to the slice site `C/Y` and then further
to `C/X` (along the slice functor `Over.map g`) agrees naturally with restricting
directly to `C/X`.  This is the natural isomorphism
`(-)|_{C/Y}|_{C/X} ≅ (-)|_{C/X}`. -/
noncomputable def overPullbackOverMapPullbackIso {X Y : C} (g : X ⟶ Y) :
    J.overPullback A Y ⋙ J.overMapPullback A g ≅ J.overPullback A X :=
  haveI : (Over.map g ⋙ Over.forget Y).IsContinuous (J.over X) J :=
    Functor.isContinuous_comp (Over.map g) (Over.forget Y) (J.over X) (J.over Y) J
  (Functor.sheafPushforwardContinuousComp (Over.map g) (Over.forget Y) A
      (J.over X) (J.over Y) J) ≪≫
    Functor.sheafPushforwardContinuousIso (Over.mapForget g) A (J.over X) J

/-- The type of maps between the restrictions `F|_{C/X}` and `G|_{C/X}` of two sheaves
`F, G` to the slice site `C/X`. -/
abbrev RestrictedHom (F G : Sheaf J A) (X : C) : Type _ :=
  (J.overPullback A X).obj F ⟶ (J.overPullback A X).obj G

/-- Restrict a map of restricted sheaves over `Z` further along `g : W ⟶ Z`, i.e. the
restriction `φ|_{C/W}` of `φ : F|_{C/Z} ⟶ G|_{C/Z}` to the finer slice `C/W`.
It is `(J.overMapPullback A g).map φ` transported along the compatibility isomorphism
so as to land in `RestrictedHom J F G W`. -/
noncomputable def restrictHomAlong {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) : RestrictedHom J F G W :=
  ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv ≫
    (J.overMapPullback A g).map φ ≫ ((overPullbackOverMapPullbackIso J g (A := A)).app G).hom

/-- **Component formula for `restrictHomAlong`.**  The value of the restricted hom
`restrictHomAlong J g F G φ` at an object `b : (Over W)ᵒᵖ` is the conjugate (by the
component of the coherence iso `overPullbackOverMapPullbackIso J g`) of the value of `φ`
at `(Over.map g).obj b.unop`.  This holds *definitionally* after unfolding
`restrictHomAlong`, `overMapPullback` and `sheafPushforwardContinuous` on components
(the relevant Mathlib simp lemma is `Functor.sheafPushforwardContinuous_map_hom_app`).
This is the workhorse for the descent argument: it relates the components of a glued map
on the slice `C/W` to those of `φ` on the larger slice `C/Z`. -/
theorem restrictHomAlong_app {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) (b : (Over W)ᵒᵖ) :
    (restrictHomAlong J g F G φ).hom.app b =
      ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv.hom.app b ≫
      φ.hom.app (Opposite.op ((Over.map g).obj (Opposite.unop b))) ≫
      ((overPullbackOverMapPullbackIso J g (A := A)).app G).hom.hom.app b := by
  dsimp only [restrictHomAlong]
  rfl

/-- The inverse coherence-iso component is the identity. -/
theorem iso_inv_app_id {X Y : C} (g : X ⟶ Y) (F : Sheaf J A) (b : (Over X)ᵒᵖ) :
    ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv.hom.app b = 𝟙 _ := by
  have hid : (Over.mapForget g).hom.app (Opposite.unop b) = 𝟙 _ :=
    Eq.symm (eq_of_comp_right_eq fun {Z} => congrFun rfl)
  have : (Over.map g ⋙ Over.forget Y).IsContinuous (J.over X) J :=
    Functor.isContinuous_comp (Over.map g) (Over.forget Y) (J.over X) (J.over Y) J
  have hcomp : (((Over.map g).sheafPushforwardContinuousComp (Over.forget Y) A
      (J.over X) (J.over Y) J).inv.app F).hom
      = 𝟙 ((Over.map g ⋙ Over.forget Y).op ⋙ F.obj) := rfl
  have hnt : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapForget g).hom A
        (J.over X) J).app F).hom
      = Functor.whiskerRight (NatTrans.op (Over.mapForget g).hom) F.obj := rfl
  simp only [overPullbackOverMapPullbackIso, Iso.app_inv, Iso.trans_inv, NatTrans.comp_app,
    Functor.sheafPushforwardContinuousIso_inv, ObjectProperty.FullSubcategory.comp_hom, hnt, hcomp]
  erw [Category.comp_id]
  simp only [Functor.whiskerRight_app, NatTrans.op_app, hid]
  exact F.obj.map_id _

/-- The forward coherence-iso component is the identity. -/
theorem iso_hom_app_id {X Y : C} (g : X ⟶ Y) (F : Sheaf J A) (b : (Over X)ᵒᵖ) :
    ((overPullbackOverMapPullbackIso J g (A := A)).app F).hom.hom.app b = 𝟙 _ := by
  have : (Over.map g ⋙ Over.forget Y).IsContinuous (J.over X) J :=
    Functor.isContinuous_comp (Over.map g) (Over.forget Y) (J.over X) (J.over Y) J
  have hid : (Over.mapForget g).inv.app (Opposite.unop b) = 𝟙 _ :=
    Eq.symm (eq_of_comp_right_eq fun {Z} => congrFun rfl)
  have hcomp : (((Over.map g).sheafPushforwardContinuousComp (Over.forget Y) A
      (J.over X) (J.over Y) J).hom.app F).hom
      = 𝟙 ((Over.map g ⋙ Over.forget Y).op ⋙ F.obj) := rfl
  have hnt : ((Functor.sheafPushforwardContinuousNatTrans (Over.mapForget g).inv A
        (J.over X) J).app F).hom
      = Functor.whiskerRight (NatTrans.op (Over.mapForget g).inv) F.obj := rfl
  simp only [overPullbackOverMapPullbackIso, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuousIso_hom, ObjectProperty.FullSubcategory.comp_hom, hnt, hcomp]
  erw [Category.id_comp]
  simp only [Functor.whiskerRight_app, NatTrans.op_app, hid]
  exact F.obj.map_id _

/-- **Coherence (inv-component triangle).**  The inverse of the compatibility iso
`overPullbackOverMapPullbackIso` at the composite `g ≫ h`, evaluated at `F`, factors as
the iso at `g`, the `overMapPullback A g`-image of the iso at `h`, and the comparison
`overMapPullbackComp J A g h` (which compares `overMapPullback A h ⋙ overMapPullback A g`
with `overMapPullback A (g ≫ h)`).  This is the unit-coherence/triangle identity for the
pseudofunctor `g ↦ overPullbackOverMapPullbackIso J g`.

Proved componentwise: every coherence iso involved acts as the identity on components
(`iso_inv_app_id` and `overMapPullbackComp_inv_app_hom_app`), so both sides reduce to the
identity. -/
theorem overPullbackOverMapPullbackIso_inv_comp {V W Z : C} (g : W ⟶ V) (h : V ⟶ Z)
    (F : Sheaf J A) :
    ((overPullbackOverMapPullbackIso J (g ≫ h) (A := A)).app F).inv =
      ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv ≫
        (J.overMapPullback A g).map ((overPullbackOverMapPullbackIso J h (A := A)).app F).inv ≫
          ((GrothendieckTopology.overMapPullbackComp J A g h).app
            ((J.overPullback A Z).obj F)).inv := by
  apply Sheaf.hom_ext
  ext x
  have hmap : ((J.overMapPullback A g).map
        ((overPullbackOverMapPullbackIso J h (A := A)).app F).inv).hom.app x
      = ((overPullbackOverMapPullbackIso J h (A := A)).app F).inv.hom.app
        (Opposite.op ((Over.map g).obj (Opposite.unop x))) := rfl
  have hmapcomp : (((GrothendieckTopology.overMapPullbackComp J A g h).app
        ((J.overPullback A Z).obj F)).inv).hom.app x
      = 𝟙 _ := by
    simp only [Iso.app_inv, GrothendieckTopology.overMapPullbackComp_inv_app_hom_app]
    exact F.obj.map_id _
  rw [iso_inv_app_id]
  show _ = ((((overPullbackOverMapPullbackIso J g (A := A)).app F).inv).hom.app x) ≫
    (((J.overMapPullback A g).map
        ((overPullbackOverMapPullbackIso J h (A := A)).app F).inv).hom.app x) ≫
    ((((GrothendieckTopology.overMapPullbackComp J A g h).app
        ((J.overPullback A Z).obj F)).inv).hom.app x)
  rw [iso_inv_app_id, hmap, iso_inv_app_id, hmapcomp]
  erw [Category.id_comp, Category.id_comp]
  rfl

/-- **Coherence (hom-component triangle).**  Dual of `overPullbackOverMapPullbackIso_inv_comp`
for the forward direction, proved by the same componentwise reduction: each coherence iso
is the identity on components (`iso_hom_app_id`,
`overMapPullbackComp_hom_app_hom_app`). -/
theorem overPullbackOverMapPullbackIso_comp_hom {V W Z : C} (g : W ⟶ V) (h : V ⟶ Z)
    (F : Sheaf J A) :
    ((overPullbackOverMapPullbackIso J (g ≫ h) (A := A)).app F).hom =
      ((GrothendieckTopology.overMapPullbackComp J A g h).app
            ((J.overPullback A Z).obj F)).hom ≫
        (J.overMapPullback A g).map ((overPullbackOverMapPullbackIso J h (A := A)).app F).hom ≫
          ((overPullbackOverMapPullbackIso J g (A := A)).app F).hom := by
  apply Sheaf.hom_ext
  ext x
  have hmap : ((J.overMapPullback A g).map
        ((overPullbackOverMapPullbackIso J h (A := A)).app F).hom).hom.app x
      = ((overPullbackOverMapPullbackIso J h (A := A)).app F).hom.hom.app
        (Opposite.op ((Over.map g).obj (Opposite.unop x))) := rfl
  have hmapcomp : (((GrothendieckTopology.overMapPullbackComp J A g h).app
        ((J.overPullback A Z).obj F)).hom).hom.app x
      = 𝟙 _ := by
    simp only [Iso.app_hom, GrothendieckTopology.overMapPullbackComp_hom_app_hom_app]
    exact F.obj.map_id _
  rw [iso_hom_app_id]
  show _ = (((GrothendieckTopology.overMapPullbackComp J A g h).app
        ((J.overPullback A Z).obj F)).hom).hom.app x ≫
    (((J.overMapPullback A g).map
        ((overPullbackOverMapPullbackIso J h (A := A)).app F).hom).hom.app x) ≫
    ((((overPullbackOverMapPullbackIso J g (A := A)).app F).hom).hom.app x)
  rw [hmapcomp, hmap, iso_hom_app_id, iso_hom_app_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

/-- Naturality of a restricted hom `φ` along the slice morphism `Over.homMk g`. -/
private theorem app_comp_map_eq {X : C} {F G : Sheaf J A} (φ : RestrictedHom J F G X)
    (b : (Over X)ᵒᵖ) {Y : C} (g : Y ⟶ b.unop.left) :
    φ.hom.app b ≫ G.obj.map g.op
      = F.obj.map g.op ≫ φ.hom.app (Opposite.op (Over.mk (g ≫ b.unop.hom))) :=
  (φ.hom.naturality (Over.homMk g : Over.mk (g ≫ b.unop.hom) ⟶ b.unop).op).symm

variable [HasPullbacks C] (F G : Sheaf J A) (U : C)
variable {I : Type*} (Ui : I → C) (f : ∀ i, Ui i ⟶ U)

/-- A family `φ i : F|_{C/U i} ⟶ G|_{C/U i}` is *compatible on overlaps* if for all
`i, j` the two restrictions of `φ i` and `φ j` to the overlap slice `C/(U i ×_U U j)`
coincide, where the overlap is the fiber product `pullback (f i) (f j)` with its two
projections. -/
def CompatibleOnOverlaps (φ : ∀ i, RestrictedHom J F G (Ui i)) : Prop :=
  ∀ i j, restrictHomAlong J (pullback.fst (f i) (f j)) F G (φ i)
       = restrictHomAlong J (pullback.snd (f i) (f j)) F G (φ j)

omit [HasPullbacks C] in
/-- **Uniqueness / locality of glued maps.**  Two maps of restricted sheaves
`ψ₁ ψ₂ : F|_{C/U} ⟶ G|_{C/U}` that have the *same* restriction to each slice `C/U i`
of a covering `{ f i : U i ⟶ U }` are equal.

This is the separatedness half of the gluing statement: a morphism of sheaves is
determined locally on a cover.  The proof reduces to componentwise equality via
`Sheaf.hom_ext`, then fixes an object `a : V ⟶ U` of `Over U` and works in the
type-valued sheaf `W ↦ Hom_A(F.val (op V), G.val (op W))`, which is separated for the
pullback of the cover along `a`.  Naturality of each `ψₖ` moves the component over `V`
onto the patch where the hypothesis applies, and `restrictHomAlong_app` cancels the
conjugating coherence isos. -/
@[ega "0 3.3.2" "Uniqueness clause"]
theorem glued_uniqueness
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (ψ₁ ψ₂ : RestrictedHom J F G U)
    (h : ∀ i, restrictHomAlong J (f i) F G ψ₁ = restrictHomAlong J (f i) F G ψ₂) :
    ψ₁ = ψ₂ := by
  -- The key local statement extracted from `h` via `restrictHomAlong_app`:
  -- on the image objects `(Over.map (f i)).obj (Over.mk e)` the two components agree,
  -- the conjugating coherence isos cancelling.
  have key : ∀ (i : I) (Y : C) (e : Y ⟶ Ui i),
      ψ₁.hom.app (Opposite.op ((Over.map (f i)).obj (Over.mk e)))
        = ψ₂.hom.app (Opposite.op ((Over.map (f i)).obj (Over.mk e))) := by
    intro i Y e
    have hcomp := congrArg
      (fun (m : RestrictedHom J F G (Ui i)) => m.hom.app (Opposite.op (Over.mk e))) (h i)
    simp only [restrictHomAlong_app] at hcomp
    have h2 := (cancel_epi
      (((overPullbackOverMapPullbackIso J (f i) (A := A)).app F).inv.hom.app
        (Opposite.op (Over.mk e)))).mp hcomp
    exact (cancel_mono
      (((overPullbackOverMapPullbackIso J (f i) (A := A)).app G).hom.hom.app
        (Opposite.op (Over.mk e)))).mp h2
  -- Reduce to componentwise equality of the underlying presheaf maps.
  apply Sheaf.hom_ext
  ext a
  -- Work in the type-valued sheaf `G.obj ⋙ coyoneda.obj (op E)` over `V := a.unop.left`,
  -- using separatedness for the pulled-back covering sieve.
  have hsep := ((G.property (F.obj.obj (Opposite.op a.unop.left))).isSheafFor
    (Sieve.pullback a.unop.hom (Sieve.generate (Presieve.ofArrows Ui f))).arrows
    (by rw [Sieve.generate_sieve]; exact J.pullback_stable a.unop.hom hcov)).isSeparatedFor
  apply hsep.ext
  intro Y g hg
  show ψ₁.hom.app a ≫ G.obj.map g.op = ψ₂.hom.app a ≫ G.obj.map g.op
  -- Naturality of `ψₖ.hom` along the slice morphism `g` reduces both sides to the
  -- component over `Over.mk (g ≫ a.unop.hom)`.
  rw [app_comp_map_eq J ψ₁ a g, app_comp_map_eq J ψ₂ a g]
  congr 1
  -- `g` lies in the pulled-back sieve, hence `g ≫ a.unop.hom` factors through some `f i`.
  rw [Sieve.pullback_apply] at hg
  obtain ⟨Wmid, e, p, hp, hfact⟩ := hg
  obtain ⟨i⟩ := hp
  -- `hfact : e ≫ f i = g ≫ a.unop.hom`; rewrite and conclude by `key`.
  rw [← hfact]
  exact key i _ e

omit [HasPullbacks C] in
/-- Simplified component formula: the coherence isos act as identities. -/
theorem restrictHomAlong_app' {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) (b : (Over W)ᵒᵖ) :
    (restrictHomAlong J g F G φ).hom.app b =
      φ.hom.app (Opposite.op ((Over.map g).obj (Opposite.unop b))) := by
  rw [restrictHomAlong_app, iso_inv_app_id, iso_hom_app_id]
  erw [Category.id_comp, Category.comp_id]

omit [HasPullbacks C] in
/-- Composition law for restriction of restricted homs:
restricting along `h : V ⟶ Z` and then along `g : W ⟶ V` equals restricting along
the composite `g ≫ h`. -/
theorem restrictHomAlong_comp {V W Z : C} (g : W ⟶ V) (h : V ⟶ Z)
    (F G : Sheaf J A) (φ : RestrictedHom J F G Z) :
    restrictHomAlong J g F G (restrictHomAlong J h F G φ)
      = restrictHomAlong J (g ≫ h) F G φ := by
  apply Sheaf.hom_ext
  ext x
  have hobj : ((Over.map h).obj ((Over.map g).obj (Opposite.unop x)))
      = ((Over.map (g ≫ h)).obj (Opposite.unop x)) := by
    apply Comma.ext <;> simp [Over.map, Comma.mapRight, Category.assoc]
  simp only [restrictHomAlong_app']
  exact eq_of_heq (congr_arg_heq (fun y => φ.hom.app y) (congrArg Opposite.op hobj))

/-- Component-level compatibility extracted from `CompatibleOnOverlaps`. -/
theorem compat_key (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ)
    (i j : I) (W : C) (e : W ⟶ pullback (f i) (f j)) :
    (φ i).hom.app (Opposite.op (Over.mk (e ≫ pullback.fst (f i) (f j))))
      = (φ j).hom.app (Opposite.op (Over.mk (e ≫ pullback.snd (f i) (f j)))) := by
  have hcomp := congrArg
    (fun (m : RestrictedHom J F G (pullback (f i) (f j))) => m.hom.app (Opposite.op (Over.mk e)))
    (hφ i j)
  simp only [restrictHomAlong_app'] at hcomp
  exact hcomp

/-- Naturality of a component of `φ i` against precomposition. -/
theorem core (φ : ∀ i, RestrictedHom J F G (Ui i)) (a : (Over U)ᵒᵖ) (W : C) (i : I)
    (p : W ⟶ pullback (f i) a.unop.hom) :
    (F.obj.map (pullback.snd (f i) a.unop.hom).op ≫
        (φ i).hom.app (Opposite.op (Over.mk (pullback.fst (f i) a.unop.hom)))) ≫ G.obj.map p.op
    = F.obj.map (p ≫ pullback.snd (f i) a.unop.hom).op ≫
        (φ i).hom.app (Opposite.op (Over.mk (p ≫ pullback.fst (f i) a.unop.hom))) := by
  rw [op_comp, F.obj.map_comp]
  erw [Category.assoc, Category.assoc]
  congr 1
  exact app_comp_map_eq J (φ i) (Opposite.op (Over.mk (pullback.fst (f i) a.unop.hom))) p

/-- The local family `(x_a i)` is compatible, so it can be amalgamated. -/
theorem family_compat (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) (a : (Over U)ᵒᵖ) :
    ∀ ⦃W : C⦄ ⦃i j : I⦄ (p : W ⟶ pullback (f i) a.unop.hom) (q : W ⟶ pullback (f j) a.unop.hom),
      p ≫ pullback.snd (f i) a.unop.hom = q ≫ pullback.snd (f j) a.unop.hom →
      (F.obj.map (pullback.snd (f i) a.unop.hom).op ≫
          (φ i).hom.app (Opposite.op (Over.mk (pullback.fst (f i) a.unop.hom)))) ≫ G.obj.map p.op
        = (F.obj.map (pullback.snd (f j) a.unop.hom).op ≫
          (φ j).hom.app (Opposite.op (Over.mk (pullback.fst (f j)
              a.unop.hom)))) ≫ G.obj.map q.op := by
  intro W i j p q hpq
  rw [core J F G U Ui f φ a W i p, core J F G U Ui f φ a W j q]
  have hcond : (p ≫ pullback.fst (f i) a.unop.hom) ≫ f i = (q ≫ pullback.fst (f j)
      a.unop.hom) ≫ f j := by
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition,
        ← Category.assoc, ← Category.assoc, hpq]
  set e : W ⟶ pullback (f i) (f j) := pullback.lift (p ≫ pullback.fst (f i) a.unop.hom)
    (q ≫ pullback.fst (f j) a.unop.hom) hcond with he
  have hk := compat_key J F G U Ui f φ hφ i j W e
  rw [pullback.lift_fst, pullback.lift_snd] at hk
  rw [hk]
  congr 2
  exact congrArg Opposite.op hpq

/-- Pulling back the `ofArrows` cover along `k` is the `ofArrows` cover of the pullbacks. -/
theorem pullback_ofArrows_eq {S V : C} (X : I → C) (g : ∀ i, X i ⟶ S) (k : V ⟶ S) :
    Sieve.ofArrows (fun i => pullback (g i) k) (fun i => pullback.snd (g i) k)
      = Sieve.pullback k (Sieve.ofArrows X g) := by
  ext W gg
  simp only [Sieve.ofArrows, Sieve.pullback_apply, Sieve.generate_apply]
  constructor
  · rintro ⟨Wmid, e, p, ⟨i⟩, hfact⟩
    exact ⟨X i, e ≫ pullback.fst (g i) k, g i, ⟨i⟩, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hfact]⟩
  · rintro ⟨Wmid, e, p, ⟨i⟩, hfact⟩
    exact ⟨pullback (g i) k, pullback.lift e gg (by simpa using hfact),
      pullback.snd (g i) k, ⟨i⟩, pullback.lift_snd _ _ _⟩

/-- The pulled-back cover of `a.left` is a covering sieve. -/
theorem hcovV (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U) (a : (Over U)ᵒᵖ) :
    Sieve.ofArrows (fun i => pullback (f i) a.unop.hom) (fun i => pullback.snd (f i)
        a.unop.hom) ∈ J a.unop.left := by
  rw [pullback_ofArrows_eq Ui f a.unop.hom]
  exact J.pullback_stable a.unop.hom hcov

/-- Two maps into `G` at `a` agreeing on every patch of the pulled-back cover are equal. -/
private theorem hom_ext_of_pullback_snd (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (a : (Over U)ᵒᵖ) {X : A}
    {s t : X ⟶ G.obj.obj (Opposite.op a.unop.left)}
    (h : ∀ i, s ≫ G.obj.map (pullback.snd (f i) a.unop.hom).op
      = t ≫ G.obj.map (pullback.snd (f i) a.unop.hom).op) : s = t := by
  refine ((G.property X).isSheafFor _
    (hcovV J U Ui f hcov a)).isSeparatedFor.ext (t₁ := s) (t₂ := t) ?_
  rintro Y g ⟨i⟩
  exact h i

/-- The local family `(x_a i)` to be amalgamated to give the component of `ψ` at `a`. -/
noncomputable def xfam (φ : ∀ i, RestrictedHom J F G (Ui i)) (a : (Over U)ᵒᵖ) (i : I) :
    F.obj.obj (Opposite.op a.unop.left) ⟶ G.obj.obj (Opposite.op (pullback (f i) a.unop.hom)) :=
  F.obj.map (pullback.snd (f i) a.unop.hom).op ≫
    (φ i).hom.app (Opposite.op (Over.mk (pullback.fst (f i) a.unop.hom)))

/-- The component of the glued map `ψ` at an object `a` of the slice site. -/
noncomputable def psiapp (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ)
    (a : (Over U)ᵒᵖ) :
    F.obj.obj (Opposite.op a.unop.left) ⟶ G.obj.obj (Opposite.op a.unop.left) :=
  G.property.amalgamateOfArrows (fun i => pullback.snd (f i) a.unop.hom) (hcovV J U Ui f hcov a)
    (xfam J F G U Ui f φ a) (family_compat J F G U Ui f φ hφ a)

/-- Defining property of `psiapp`: restricting to the `i`-patch recovers the family element. -/
theorem psiapp_spec (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ)
    (a : (Over U)ᵒᵖ) (i : I) :
    psiapp J F G U Ui f hcov φ hφ a ≫ G.obj.map (pullback.snd (f i) a.unop.hom).op
      = xfam J F G U Ui f φ a i := by
  apply G.property.amalgamateOfArrows_map

/-- Naturality of `psiapp`, proved by separatedness of the value sheaf. -/
theorem psiapp_nat (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ)
    (a a' : (Over U)ᵒᵖ) (t : a ⟶ a') :
    psiapp J F G U Ui f hcov φ hφ a ≫ G.obj.map (t.unop.left.op)
      = F.obj.map (t.unop.left.op) ≫ psiapp J F G U Ui f hcov φ hφ a' := by
  set s : a'.unop.left ⟶ a.unop.left := t.unop.left with hs
  have hsq : s ≫ a.unop.hom = a'.unop.hom := t.unop.w
  have key : ∀ (i : I),
      (psiapp J F G U Ui f hcov φ hφ a ≫ G.obj.map s.op) ≫
          G.obj.map (pullback.snd (f i) a'.unop.hom).op
        = (F.obj.map s.op ≫ psiapp J F G U Ui f hcov φ hφ a') ≫
          G.obj.map (pullback.snd (f i) a'.unop.hom).op := by
    intro i
    have hm : (pullback.snd (f i) a'.unop.hom ≫ s) ≫ a.unop.hom = pullback.fst (f
        i) a'.unop.hom ≫ f i := by
      rw [Category.assoc, hsq, pullback.condition]
    set m : pullback (f i) a'.unop.hom ⟶ pullback (f i) a.unop.hom :=
      pullback.lift (pullback.fst (f i) a'.unop.hom) (pullback.snd (f i) a'.unop.hom ≫ s) hm.symm
          with hmdef
    have hm_fst : m ≫ pullback.fst (f i) a.unop.hom = pullback.fst (f i) a'.unop.hom :=
      pullback.lift_fst _ _ _
    have hm_snd : m ≫ pullback.snd (f i) a.unop.hom = pullback.snd (f i) a'.unop.hom ≫ s :=
      pullback.lift_snd _ _ _
    have hR : (F.obj.map s.op ≫ psiapp J F G U Ui f hcov φ hφ a') ≫
          G.obj.map (pullback.snd (f i) a'.unop.hom).op
        = F.obj.map (m ≫ pullback.snd (f i) a.unop.hom).op ≫
          (φ i).hom.app (Opposite.op (Over.mk (m ≫ pullback.fst (f i) a.unop.hom))) := by
      rw [hm_snd, hm_fst, Category.assoc, psiapp_spec J F G U Ui f hcov φ hφ a' i, xfam]
      erw [← Category.assoc, ← F.obj.map_comp, ← op_comp]
      rfl
    have hL : (psiapp J F G U Ui f hcov φ hφ a ≫ G.obj.map s.op) ≫
          G.obj.map (pullback.snd (f i) a'.unop.hom).op
        = F.obj.map (m ≫ pullback.snd (f i) a.unop.hom).op ≫
          (φ i).hom.app (Opposite.op (Over.mk (m ≫ pullback.fst (f i) a.unop.hom))) := by
      have hgmap : G.obj.map s.op ≫ G.obj.map (pullback.snd (f i) a'.unop.hom).op
          = G.obj.map (pullback.snd (f i) a.unop.hom).op ≫ G.obj.map m.op := by
        rw [← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp, hm_snd]
      rw [Category.assoc, hgmap, ← Category.assoc,
          psiapp_spec J F G U Ui f hcov φ hφ a i, xfam]
      exact core J F G U Ui f φ a (pullback (f i) a'.unop.hom) i m
    rw [hL, hR]
  exact hom_ext_of_pullback_snd J G U Ui f hcov a' key

/-- The underlying natural transformation of the glued map `ψ`. -/
noncomputable def psihom (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ) :
    ((J.overPullback A U).obj F).obj ⟶ ((J.overPullback A U).obj G).obj where
  app a := psiapp J F G U Ui f hcov φ hφ a
  naturality := by
    intro a a' t
    exact (psiapp_nat J F G U Ui f hcov φ hφ a a' t).symm

/-- The glued map `ψ : F|_{C/U} ⟶ G|_{C/U}`. -/
noncomputable def psi (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ) :
    RestrictedHom J F G U :=
  ⟨psihom J F G U Ui f hcov φ hφ⟩

/-- The glued map restricts to `φ i` on each slice `C/U i`. -/
theorem psi_restrict (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i)) (hφ : CompatibleOnOverlaps J F G U Ui f φ) (i : I) :
    restrictHomAlong J (f i) F G (psi J F G U Ui f hcov φ hφ) = φ i := by
  apply Sheaf.hom_ext
  ext b
  rw [restrictHomAlong_app']
  set c : (Over U)ᵒᵖ := Opposite.op ((Over.map (f i)).obj b.unop) with hc
  show psiapp J F G U Ui f hcov φ hφ c = (φ i).hom.app b
  have hchom : c.unop.hom = b.unop.hom ≫ f i := rfl
  refine hom_ext_of_pullback_snd J G U Ui f hcov c (fun j => ?_)
  rw [psiapp_spec J F G U Ui f hcov φ hφ c j, xfam]
  erw [app_comp_map_eq J (φ i) b (pullback.snd (f j) c.unop.hom)]
  congr 1
  have hcond : (pullback.snd (f j) c.unop.hom ≫ b.unop.hom) ≫ f i
      = pullback.fst (f j) c.unop.hom ≫ f j := by
    rw [Category.assoc]
    exact pullback.condition.symm
  set e : pullback (f j) c.unop.hom ⟶ pullback (f i) (f j) :=
    pullback.lift (pullback.snd (f j) c.unop.hom ≫ b.unop.hom) (pullback.fst (f j) c.unop.hom)
        hcond with he
  have he_fst : e ≫ pullback.fst (f i) (f j) = pullback.snd (f j) c.unop.hom ≫ b.unop.hom :=
    pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd (f i) (f j) = pullback.fst (f j) c.unop.hom :=
    pullback.lift_snd _ _ _
  have hk := compat_key J F G U Ui f φ hφ i j (pullback (f j) c.unop.hom) e
  rw [he_fst, he_snd] at hk
  rw [hk]


/-- **Existence of the glued map.**  Given a covering `{ f i : U i ⟶ U }` and a family
`φ i : F|_{C/U i} ⟶ G|_{C/U i}` compatible on overlaps, there exists a map
`ψ : F|_{C/U} ⟶ G|_{C/U}` whose restriction to each slice `C/U i` is `φ i`.

The witness is `psi`: over each object `a : V ⟶ U` of `Over U` the pulled-back cover
`{ pullback (f i) a ⟶ V }` is a covering sieve of `V` (`hcovV`), the family `xfam` of
values of the `φ i` on its patches is compatible (`family_compat`, from
`CompatibleOnOverlaps` and `pullback.condition`), and amalgamating it in the type-valued
sheaf `W ↦ Hom_A(F.val (op V), G.val (op W))` gives the component `psiapp`.  Naturality
(`psiapp_nat`) and the restriction identity (`psi_restrict`) both follow from
separatedness of that sheaf together with the defining property `psiapp_spec`. -/
theorem glued_existence
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) :
    ∃ ψ : RestrictedHom J F G U, ∀ i, restrictHomAlong J (f i) F G ψ = φ i :=
  ⟨psi J F G U Ui f hcov φ hφ, fun i => psi_restrict J F G U Ui f hcov φ hφ i⟩

/-- **Stacks 04TQ — Maps of sheaves glue (existence and uniqueness).**

Let `(C, J)` be a site with fiber products, `A` the target category of sheaf values,
`F, G : Sheaf J A`, and let `{ f i : U i → U }` be a covering of `U` in `J`.  Then any
family of maps of restricted sheaves `φ i : F|_{C/U i} ⟶ G|_{C/U i}` that is compatible
on the overlaps `C/(U i ×_U U j)` glues to a unique map `φ : F|_{C/U} ⟶ G|_{C/U}` whose
restriction to each `C/U i` is `φ i`. -/
@[stacks 04TQ]
theorem maps_of_sheaves_glue
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) :
    ∃! ψ : RestrictedHom J F G U, ∀ i, restrictHomAlong J (f i) F G ψ = φ i := by
  -- Existence + uniqueness assembled from the two descent lemmas above.
  obtain ⟨ψ, hψ⟩ := glued_existence J F G U Ui f hcov φ hφ
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  -- `ψ'` and `ψ` restrict to the same family `φ`, hence are equal by locality.
  exact glued_uniqueness J F G U Ui f hcov ψ' ψ (fun i => by rw [hψ' i, hψ i])

/-- The restriction map always produces a compatible family: for any
`ψ : F|_{C/U} ⟶ G|_{C/U}`, the family `(ψ|_{C/U i})_i` is compatible on overlaps. -/
theorem restrictionFamily_compatible (ψ : RestrictedHom J F G U) :
    CompatibleOnOverlaps J F G U Ui f (fun i => restrictHomAlong J (f i) F G ψ) := by
  intro i j
  rw [restrictHomAlong_comp, restrictHomAlong_comp, pullback.condition]

/-- **Stacks 04TQ — bijection form.**

The restriction map sending `φ : F|_{C/U} ⟶ G|_{C/U}` to the compatible family of its
restrictions `(φ|_{C/U i})_i` is a bijection onto the set of compatible families. -/
theorem maps_of_sheaves_glue_bijective
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U) :
    Function.Bijective
      (fun (ψ : RestrictedHom J F G U) =>
        (⟨fun i => restrictHomAlong J (f i) F G ψ,
            restrictionFamily_compatible J F G U Ui f ψ⟩ :
          { φ : ∀ i, RestrictedHom J F G (Ui i) // CompatibleOnOverlaps J F G U Ui f φ })) := by
  constructor
  · -- Injectivity: two maps with the same restrictions agree, by `glued_uniqueness`.
    intro ψ₁ ψ₂ h
    exact glued_uniqueness J F G U Ui f hcov ψ₁ ψ₂ (congrFun (congrArg Subtype.val h))
  · -- Surjectivity: existence in `maps_of_sheaves_glue`.
    rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ, -⟩ := maps_of_sheaves_glue J F G U Ui f hcov φ hφ
    exact ⟨ψ, Subtype.ext (funext hψ)⟩

end Stacks.SheafMapGluing
