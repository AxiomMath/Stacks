module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitPostcompSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpenImmersionGluing
public import StacksFrontier.CategoryTheory.Filtered.FiniteEqualizerGerms
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitInverseImageSystem

/-!
# Germs of sections over the levels of an étale inverse system with affine transitions

Let `I` be a directed set with a least element `⊥`, let `(X_i)` be an inverse system of schemes
over `I` whose transition morphisms are affine and étale, let `X = lim X_i` and let `F` be a sheaf
of sets on the small étale site of `X_⊥`. Write `F(X_i)` for the sections of `F` over the étale
`X_⊥`-scheme `X_i`. This file proves that the maps `F(X_i) ⟶ Γ(X, f⁻¹F)` (unit of the inverse
image along `f : X ⟶ X_⊥`, then restriction along `X ⟶ X_i ×_{X_⊥} X`) exhibit `Γ(X, f⁻¹F)` as
the filtered colimit of the `F(X_i)`, as soon as `X_⊥` is covered by finitely many objects of the
small affine étale site of `X_⊥` with open immersion structure maps whose pairwise overlaps are
covered by such objects.

The proof applies Stacks 09YN on the sites of Stacks 0EYL over each member and each overlap of
the cover (`Stacks.EtaleCohomology.LimitSiteBridge.sections_colimit_levelOf`), reads the abstract
maps as restriction of sections (`levelψOf_postcomp`, `limitιOf_postcomp`), and glues along the
cover (`Stacks.Germs.colimit_of_finite_equalizer`).

## Main definitions

* `pc`, `wh`: the base change to `X_i` of a member of the cover, and `X_i` itself, as étale
  `X_⊥`-schemes; `pcMap`, `whMap` the transitions; `toWh` the inclusions.
* `wholeSections`: the maps `F(X_i) ⟶ Γ(X, f⁻¹F)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology Stacks.WeakSites.PullbackSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  {hc : IsLimit c}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)]

variable (D c B hD hX hc) in
/-- The level of the system carrying `X_i`. -/
@[no_expose]
def Lv (i : I) : (sys D c B hD hX hc).I := (op i : Iᵒᵖ)

variable (D c B hD hX hc) in
/-- The arrow of the system to the bottom level. -/
abbrev fr (i : I) : Lv D c B hD hX hc i ⟶ bottom D c B hD hX hc :=
  (bottom_isTerminal D c B hD hX hc).from _

variable (D c B hD hX hc) in
/-- The arrow of the system attached to `i ≤ j`. -/
@[no_expose]
def arr {i j : I} (d : i ≤ j) : Lv D c B hD hX hc j ⟶ Lv D c B hD hX hc i :=
  (homOfLE d).op

/-- The base change to `X_i` of an object `Y` of the bottom level, as an étale `X_⊥`-scheme. -/
abbrev pc (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale :=
  (smallEtalePostcomp (toBottom D c B hD hX hc (Lv D c B hD hX hc i))).obj
    ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).obj
      (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y))

variable (D c B hD hX hc) in
/-- `X_i` itself, as an étale `X_⊥`-scheme. -/
abbrev wh (i : I) : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale :=
  (smallEtalePostcomp (toBottom D c B hD hX hc (Lv D c B hD hX hc i))).obj
    (Scheme.Etale.mk (𝟙 (lvl D c B hD hX hc (Lv D c B hD hX hc i))))

/-- The structure morphism of the base change to `X_i` of an object of the bottom level. -/
abbrev str (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (pc i Y).left ⟶ lvl D c B hD hX hc (Lv D c B hD hX hc i) :=
  ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).obj
      (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)).hom

/-- The projection of the base change to `X_i` onto the object of the bottom level. -/
abbrev prj (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (pc i Y).left ⟶ ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj Y).left :=
  ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (fr D c B hD hX hc i)).app Y

/-- The base change of `Y` to `X_i` is the fibre product of `Y` and `X_i` over `X_⊥`, with
projections `prj` and `str`. -/
theorem isPullback_prj_str (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    IsPullback (prj i Y) (str i Y)
      ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj Y).hom
      (toBottom D c B hD hX hc (Lv D c B hD hX hc i)) :=
  (affineEtaleSiteColimit D c B hD hX hc).transition_isPullback _ Y

/-- The inclusion of the base change of `Y` into `X_i`. -/
def toWh (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    pc i Y ⟶ wh D c B hD hX hc i :=
  (smallEtalePostcomp (toBottom D c B hD hX hc (Lv D c B hD hX hc i))).map
    (MorphismProperty.Over.homMk (str i Y) (Category.comp_id _) trivial)

/-- The underlying morphism of schemes of `toWh i Y` is the structure morphism `str i Y`. -/
theorem toWh_left (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (toWh i Y).left = str i Y :=
  rfl

variable (D c B hD hX hc) in
/-- The transition `X_j ⟶ X_i`, as a morphism of étale `X_⊥`-schemes. -/
def whMap {i j : I} (d : i ≤ j) : wh D c B hD hX hc j ⟶ wh D c B hD hX hc i :=
  MorphismProperty.Over.homMk (lvlMap D c B hD hX hc (arr D c B hD hX hc d)) (by
    exact (congrArg (lvlMap D c B hD hX hc (arr D c B hD hX hc d) ≫ ·) (Category.id_comp _)).trans
      ((toBottom_comp _).symm.trans (Category.id_comp _).symm)) trivial

/-- The transition between the base changes of `Y` to `X_j` and to `X_i`. -/
def pcMap {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    pc j Y ⟶ pc i Y :=
  eqToHom (congrArg (fun Y' => (smallEtalePostcomp (toBottom D c B hD hX hc
      (Lv D c B hD hX hc j))).obj ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc j)).obj Y'))
      (u_from_obj (arr D c B hD hX hc d) Y).symm) ≫
    levelProj (arr D c B hD hX hc d) (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)

omit [OrderBot I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- For equal objects `Y₁ = Y₂` of a level, the identification of the underlying schemes of their
images in the small étale site commutes with the structure morphisms. -/
theorem eqToHom_comp_levelToEtale_hom {j : (sys D c B hD hX hc).I}
    {Y₁ Y₂ : (sys D c B hD hX hc).C j} (h : Y₁ = Y₂) :
    eqToHom (congrArg (fun Y' => ((levelToEtale D c B hD hX hc j).obj Y').left) h) ≫
      ((levelToEtale D c B hD hX hc j).obj Y₂).hom =
        ((levelToEtale D c B hD hX hc j).obj Y₁).hom := by
  subst h
  exact Category.id_comp _

/-- The transition of base changes is compatible with the structure morphisms. -/
theorem pcMap_left_str {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (pcMap d Y).left ≫ str i Y = str j Y ≫ lvlMap D c B hD hX hc (arr D c B hD hX hc d) := by
  have hw := ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback
    (arr D c B hD hX hc d) (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)).w
  have he := eqToHom_comp_levelToEtale_hom (u_from_obj (arr D c B hD hX hc d) Y).symm
  have hl := levelProj_left (arr D c B hD hX hc d)
    (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)
  have hpc : (pcMap d Y).left = eqToHom (congrArg (fun Y' => ((levelToEtale D c B hD hX hc
      (Lv D c B hD hX hc j)).obj Y').left) (u_from_obj (arr D c B hD hX hc d) Y).symm) ≫
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (arr D c B hD hX hc d)).app
        (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y) := by
    rw [pcMap, etale_comp_left, etale_eqToHom_left, hl]
    rfl
  exact (congrArg (· ≫ str i Y) hpc).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hw).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) he))))

/-- The transition of base changes is compatible with the projections. -/
theorem pcMap_left_prj {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (pcMap d Y).left ≫ prj i Y = prj j Y := by
  have h := levelProj_comp_levelProjBot (arr D c B hD hX hc d) Y
  have h2 : pcMap d Y ≫ levelProjBot (Lv D c B hD hX hc i) Y =
      levelProjBot (Lv D c B hD hX hc j) Y := by
    rw [pcMap, Category.assoc, h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h3 := congrArg (fun m => m.left) h2
  rw [etale_comp_left, levelProjBot_left, levelProjBot_left] at h3
  exact h3

/-- Two morphisms into the base change of `Y` to `X_i` are equal if their composites with `prj` and
with `str` agree. -/
theorem pc_hom_ext (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    {V : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale} (f g : V ⟶ pc i Y)
    (h₁ : f.left ≫ prj i Y = g.left ≫ prj i Y) (h₂ : f.left ≫ str i Y = g.left ≫ str i Y) :
    f = g :=
  MorphismProperty.Over.Hom.ext ((isPullback_prj_str i Y).hom_ext h₁ h₂)

/-! ### The limit side -/

/-- The base change to the limit of an object `Y` of the bottom level. -/
abbrev pcT (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) : c.pt.Etale :=
  (limitToEtale D c B hX).obj ((toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).obj Y)

/-- The projection of the base change to the limit onto the object of the bottom level. -/
abbrev prjT (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (pcT Y).left ⟶ ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj Y).left :=
  ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst (bottom D c B hD hX hc)).app Y

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The base change of `Y` to the limit is the fibre product of `Y` and the limit over `X_⊥`. -/
theorem isPullback_prjT (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    IsPullback (prjT Y) (pcT Y).hom
      ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj Y).hom
      (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) :=
  (affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback _ Y

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- For equal objects `Z₁ = Z₂` of the limit site, the identification of the underlying schemes of
their images in the small étale site commutes with the structure morphisms. -/
theorem eqToHom_comp_limitToEtale_hom {Z₁ Z₂ : limitSite D c B hX} (h : Z₁ = Z₂) :
    eqToHom (congrArg (fun Z => ((limitToEtale D c B hX).obj Z).left) h) ≫
      ((limitToEtale D c B hX).obj Z₂).hom = ((limitToEtale D c B hX).obj Z₁).hom := by
  subst h
  exact Category.id_comp _

/-- The morphism from the base change of `Y` to the limit into the base change to the limit of the
base change of `Y` to `X_i`. -/
def lam (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    pcT Y ⟶ (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj (pc i Y) :=
  (limitToEtale D c B hX).map (eqToHom (toLimitSmall_transition_obj (Lv D c B hD hX hc i) Y).symm) ≫
    limitLift (Lv D c B hD hX hc i) (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)

/-- The underlying morphism of schemes of `lam i Y`. -/
theorem lam_left (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (lam i Y).left = eqToHom (congrArg (fun Z => ((limitToEtale D c B hX).obj Z).left)
      (toLimitSmall_transition_obj (Lv D c B hD hX hc i) Y).symm) ≫
      (limitLift (Lv D c B hD hX hc i)
        (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)).left := by
  rw [lam, etale_comp_left, eqToHom_map, etale_eqToHom_left]

/-- Composing `lam i Y` with the first projection and `prj i Y` gives `prjT Y`. -/
theorem lam_left_fst_prj (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (lam i Y).left ≫ pullback.fst (pc i Y).hom (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) ≫
      prj i Y = prjT Y := by
  have h1 := limitLift_left_fst (Lv D c B hD hX hc i)
    (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)
  have h2 := (affineEtaleSiteColimit D c B hD hX hc).toLimitFst_transition (fr D c B hD hX hc i) Y
  rw [lam_left, Category.assoc]
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ prj i Y) h1))).trans ?_
  refine Eq.trans ?_ h2.symm
  simp only [Functor.comp_map, eqToHom_map]
  rfl

/-- Composing `lam i Y` with the first projection and `str i Y` gives the structure morphism of the
base change of `Y` to the limit followed by the projection to `X_i`. -/
theorem lam_left_fst_str (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (lam i Y).left ≫ pullback.fst (pc i Y).hom (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) ≫
      str i Y = (pcT Y).hom ≫ lvlπ D c B hD hX hc (Lv D c B hD hX hc i) := by
  have h1 := limitLift_left_fst (Lv D c B hD hX hc i)
    (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)
  have h2 := ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback (Lv D c B hD hX hc i)
    (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)).w
  have h3 :=
    eqToHom_comp_limitToEtale_hom (toLimitSmall_transition_obj (Lv D c B hD hX hc i) Y).symm
  rw [lam_left, Category.assoc]
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ str i Y) h1))).trans ?_
  exact (congrArg (_ ≫ ·) h2).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3))

/-! ### Morphism identities at the levels -/

omit [OrderBot I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The transition `X_k ⟶ X_i` is the composite of the transitions `X_k ⟶ X_j ⟶ X_i`. -/
theorem lvlMap_arr_trans {i j k : I} (d : i ≤ j) (e : j ≤ k) :
    lvlMap D c B hD hX hc (arr D c B hD hX hc (d.trans e)) =
      lvlMap D c B hD hX hc (arr D c B hD hX hc e) ≫
        lvlMap D c B hD hX hc (arr D c B hD hX hc d) := by
  rw [← lvlMap_comp]
  rfl

/-- The transitions of base changes compose: `pcMap` for `i ≤ j ≤ k` is the composite of the
transitions for `j ≤ k` and `i ≤ j`. -/
theorem pcMap_trans {i j k : I} (d : i ≤ j) (e : j ≤ k)
    (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    pcMap (d.trans e) Y = pcMap e Y ≫ pcMap d Y := by
  apply pc_hom_ext
  · rw [pcMap_left_prj, etale_comp_left, Category.assoc, pcMap_left_prj, pcMap_left_prj]
  · rw [pcMap_left_str, etale_comp_left, Category.assoc, pcMap_left_str,
      reassoc_of% (pcMap_left_str e Y), lvlMap_arr_trans]

/-- The inclusions `toWh` commute with the transitions `pcMap` and `whMap`. -/
theorem pcMap_toWh {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    pcMap d Y ≫ toWh i Y = toWh j Y ≫ whMap D c B hD hX hc d :=
  MorphismProperty.Over.Hom.ext (pcMap_left_str d Y)

/-- The base change to `X_i` of a morphism of the bottom level. -/
abbrev pcHom (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)} (g : Y ⟶ Y') :
    pc i Y ⟶ pc i Y' :=
  (smallEtalePostcomp (toBottom D c B hD hX hc (Lv D c B hD hX hc i))).map
    ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).map
      (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).map g))

/-- The base change of a morphism of the bottom level is compatible with the structure
morphisms. -/
theorem pcHom_left_str (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)}
    (g : Y ⟶ Y') : (pcHom i g).left ≫ str i Y' = str i Y :=
  MorphismProperty.Over.w ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).map
    (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).map g))

/-- The base change of a morphism `g` of the bottom level is compatible with the projections and
`g`. -/
theorem pcHom_left_prj (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)}
    (g : Y ⟶ Y') : (pcHom i g).left ≫ prj i Y' =
      prj i Y ≫ ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).map g).left :=
  ((affineEtaleSiteColimit D c B hD hX hc).transitionFst (fr D c B hD hX hc i)).naturality g

/-- The base change of a morphism of the bottom level commutes with the inclusions into `X_i`. -/
theorem pcHom_toWh (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)}
    (g : Y ⟶ Y') : pcHom i g ≫ toWh i Y' = toWh i Y :=
  MorphismProperty.Over.Hom.ext (pcHom_left_str i g)

/-- The transitions of base changes are natural in the object of the bottom level. -/
theorem pcMap_pcHom {i j : I} (d : i ≤ j) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)}
    (g : Y ⟶ Y') : pcMap d Y ≫ pcHom i g = pcHom j g ≫ pcMap d Y' := by
  apply pc_hom_ext
  · rw [etale_comp_left, etale_comp_left, Category.assoc, Category.assoc, pcHom_left_prj,
      reassoc_of% (pcMap_left_prj d Y), pcMap_left_prj, pcHom_left_prj]
  · rw [etale_comp_left, etale_comp_left, Category.assoc, Category.assoc, pcHom_left_str,
      pcMap_left_str, pcMap_left_str, reassoc_of% (pcHom_left_str j g)]

/-! ### Morphism identities at the limit -/

variable (D c B hD hX hc) in
/-- The final object of the small étale site of the limit. -/
abbrev unitT : c.pt.Etale := Scheme.Etale.mk (𝟙 c.pt)

/-- The inclusion of the base change of `Y` to the limit into the limit. -/
def toWT (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) : pcT Y ⟶ unitT D c :=
  MorphismProperty.Over.homMk (pcT Y).hom (Category.comp_id _) trivial

variable (D c B hD hX hc) in
/-- The morphism from the limit to the base change of `X_i` to the limit, induced by the
projection. -/
def sig (i : I) : unitT D c ⟶
    (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj
      (wh D c B hD hX hc i) :=
  smallEtaleBaseChangeLift (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) (wh D c B hD hX hc i)
    (lvlπ D c B hD hX hc (Lv D c B hD hX hc i))
    ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (lvlπ_comp (fr D c B hD hX hc i)).symm)

/-- Composing `sig i` with the first projection gives the projection from the limit to `X_i`. -/
theorem sig_left_fst (i : I) :
    (sig D c B hD hX hc i).left ≫ pullback.fst (wh D c B hD hX hc i).hom
      (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) = lvlπ D c B hD hX hc (Lv D c B hD hX hc i) :=
  pullback.lift_fst _ _ _

/-- `lam i Y` followed by the base change of `toWh i Y` equals `toWT Y` followed by `sig i`. -/
theorem lam_toWh (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    lam i Y ≫ (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map (toWh i Y) =
      toWT Y ≫ sig D c B hD hX hc i := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ?_
  refine ((congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ (toWh i Y))).trans ?_).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (sig_left_fst i))).symm
  exact (Category.assoc _ _ _).symm.trans (lam_left_fst_str i Y)

/-- The morphisms `lam` are compatible with the transitions of base changes. -/
theorem lam_pcMap {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    lam j Y ≫ (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map (pcMap d Y) =
      lam i Y := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ (pcMap d Y))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  apply (isPullback_prj_str i Y).hom_ext
  · exact (congrArg (_ ≫ ·) (pcMap_left_prj d Y)).trans ((Category.assoc _ _ _).trans
      ((lam_left_fst_prj j Y).trans ((Category.assoc _ _ _).trans (lam_left_fst_prj i Y)).symm))
  · refine (congrArg (_ ≫ ·) (pcMap_left_str d Y)).trans ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (· ≫ _) ((Category.assoc _ _ _).trans (lam_left_fst_str j Y))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (lvlπ_comp (arr D c B hD hX hc d)).symm).trans ?_
    exact ((Category.assoc _ _ _).trans (lam_left_fst_str i Y)).symm

/-- The base change to the limit of a morphism of the bottom level. -/
abbrev pcTHom {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)} (g : Y ⟶ Y') :
    pcT Y ⟶ pcT Y' :=
  (limitToEtale D c B hX).map ((toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).map g)

/-- The morphisms `lam` are natural in the object of the bottom level. -/
theorem lam_pcHom (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)} (g : Y ⟶ Y') :
    lam i Y ≫ (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map (pcHom i g) =
      pcTHom g ≫ lam i Y' := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ (pcHom i g))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  apply (isPullback_prj_str i Y').hom_ext
  · refine (congrArg (_ ≫ ·) (pcHom_left_prj i g)).trans ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (· ≫ _) ((Category.assoc _ _ _).trans (lam_left_fst_prj i Y))).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (lam_left_fst_prj i Y')).symm)
    exact (((affineEtaleSiteColimit D c B hD hX hc).toLimitFst
      (bottom D c B hD hX hc)).naturality g).symm
  · refine (congrArg (_ ≫ ·) (pcHom_left_str i g)).trans ?_
    refine ((Category.assoc _ _ _).trans (lam_left_fst_str i Y)).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (lam_left_fst_str i Y')).symm)
    exact (congrArg (· ≫ _) (MorphismProperty.Over.w (pcTHom g)).symm).trans (Category.assoc _ _ _)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The base change to the limit of a morphism of the bottom level commutes with the inclusions
into the limit. -/
theorem pcTHom_toWT {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)} (g : Y ⟶ Y') :
    pcTHom g ≫ toWT Y' = toWT Y :=
  MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w (pcTHom g))

/-! ### Sections -/

variable (F : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology
  (Type (max u v + 1)))

variable (D c B hD hX hc) in
/-- The unit of the inverse image along `f : X ⟶ X_⊥`, over an étale `X_⊥`-scheme `V`. -/
def unitAt (V : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale) :
    F.obj.obj (op V) ⟶ ((limitL D c B hD hX hc).obj F).obj.obj
      (op ((smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj V)) :=
  ((limitAdj D c B hD hX hc).unit.app F).hom.app (op V)

variable (D c B hD hX hc) in
/-- **The restriction maps `F(X_i) ⟶ Γ(X, f⁻¹F)`**: the unit of the inverse image along
`f : X ⟶ X_⊥` over `X_i`, restricted along the morphism `X ⟶ X_i ×_{X_⊥} X` given by the
projection. -/
def wholeSections (i : I) :
    F.obj.obj (op (wh D c B hD hX hc i)) ⟶
      ((limitL D c B hD hX hc).obj F).obj.obj (op (unitT D c)) :=
  unitAt D c B hD hX hc F (wh D c B hD hX hc i) ≫
    ((limitL D c B hD hX hc).obj F).obj.map (sig D c B hD hX hc i).op

/-- The map `limitρOf` at the level `X_i` and the object `Y` is the unit of the inverse image over
the base change of `Y` to `X_i`, followed by restriction along `lam i Y`. -/
theorem limitρOf_postcomp (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (y : F.obj.obj (op (pc i Y))) :
    limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y y =
      ((limitL D c B hD hX hc).obj F).obj.map (lam i Y).op
        (unitAt D c B hD hX hc F (pc i Y) y) := by
  simp only [limitρOf, limitιOf_postcomp, limitιPost, lam, op_comp, Functor.map_comp]
  rfl

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- Naturality of `unitAt` in the étale `X_⊥`-scheme, applied to a section. -/
theorem unit_naturality_apply {V V' : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale}
    (m : V ⟶ V') (y : F.obj.obj (op V')) :
    unitAt D c B hD hX hc F V (F.obj.map m.op y) =
      ((limitL D c B hD hX hc).obj F).obj.map
        ((smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map m).op
        (unitAt D c B hD hX hc F V' y) :=
  ConcreteCategory.congr_hom (((limitAdj D c B hD hX hc).unit.app F).hom.naturality m.op) y

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- Restricting a section of `f⁻¹F` along `g` and then along `f` is restricting along `f ≫ g`. -/
theorem map_comp_apply' {V₁ V₂ V₃ : c.pt.Etale} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (y : ((limitL D c B hD hX hc).obj F).obj.obj (op V₃)) :
    ((limitL D c B hD hX hc).obj F).obj.map f.op (((limitL D c B hD hX hc).obj F).obj.map g.op y) =
      ((limitL D c B hD hX hc).obj F).obj.map (f ≫ g).op y :=
  (((limitL D c B hD hX hc).obj F).obj.map_comp_apply g.op f.op y).symm

/-- Applying `limitρOf` to the restriction of a section over `X_i` gives the restriction along
`toWT Y` of its image under `wholeSections`. -/
theorem ρ_toWh (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (x : F.obj.obj (op (wh D c B hD hX hc i))) :
    limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y (F.obj.map (toWh i Y).op x) =
      ((limitL D c B hD hX hc).obj F).obj.map (toWT Y).op (wholeSections D c B hD hX hc F i x) := by
  rw [limitρOf_postcomp, unit_naturality_apply, map_comp_apply', lam_toWh, wholeSections]
  exact (map_comp_apply' F _ _ _).symm

/-- The maps `limitρOf` are compatible with the transitions of base changes. -/
theorem ρ_pcMap {i j : I} (d : i ≤ j) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (y : F.obj.obj (op (pc i Y))) :
    limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc j) Y (F.obj.map (pcMap d Y).op y) =
      limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y y := by
  rw [limitρOf_postcomp, unit_naturality_apply, map_comp_apply', lam_pcMap, limitρOf_postcomp]

/-- The maps `limitρOf` are natural in the object of the bottom level. -/
theorem ρ_pcHom (i : I) {Y Y' : (sys D c B hD hX hc).C (bottom D c B hD hX hc)} (g : Y ⟶ Y')
    (y : F.obj.obj (op (pc i Y'))) :
    limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y (F.obj.map (pcHom i g).op y) =
      ((limitL D c B hD hX hc).obj F).obj.map (pcTHom g).op
        (limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
          (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y' y) := by
  rw [limitρOf_postcomp, unit_naturality_apply, map_comp_apply', lam_pcHom, limitρOf_postcomp,
    map_comp_apply']

/-- Every section of `f⁻¹F` over the base change of `Y` to the limit is the image under
`limitρOf` of a section over the base change of `Y` to some `X_i`. -/
theorem ρ_surj (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (s : ((limitL D c B hD hX hc).obj F).obj.obj (op (pcT Y))) :
    ∃ (i : I) (y : F.obj.obj (op (pc i Y))),
      limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y y = s := by
  obtain ⟨j, a, t, ht⟩ := (sections_colimit_levelOf (postcompL D c B hD hX hc)
    (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F
    (bottom D c B hD hX hc) Y).1 s
  obtain ⟨i⟩ := j
  obtain rfl : a = fr D c B hD hX hc i := (bottom_isTerminal D c B hD hX hc).hom_ext _ _
  exact ⟨i, t, ht⟩

/-- Two sections over the base change of `Y` to `X_i` with the same image under `limitρOf` agree
after restriction to the base change of `Y` to some `X_j`, `j ≥ i`. -/
theorem ρ_inj (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) (i : I)
    (y y' : F.obj.obj (op (pc i Y)))
    (h : limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y y =
      limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
        (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) Y y') :
    ∃ (j : I) (d : i ≤ j), F.obj.map (pcMap d Y).op y = F.obj.map (pcMap d Y).op y' := by
  obtain ⟨k, b, hb⟩ := (sections_colimit_levelOf (postcompL D c B hD hX hc)
    (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F
    (bottom D c B hD hX hc) Y).2 (Lv D c B hD hX hc i) (fr D c B hD hX hc i) y y' h
  obtain ⟨j⟩ := k
  have d : i ≤ j := leOfHom b.unop
  obtain rfl : b = arr D c B hD hX hc d := Subsingleton.elim (α := (op j : Iᵒᵖ) ⟶ op i) _ _
  refine ⟨j, d, ?_⟩
  have hb' : (levelψOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F
      (i := Lv D c B hD hX hc i) (j := Lv D c B hD hX hc j) (arr D c B hD hX hc d)).app
        (op (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)) y =
      (levelψOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F
      (i := Lv D c B hD hX hc i) (j := Lv D c B hD hX hc j) (arr D c B hD hX hc d)).app
        (op (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y)) y' := hb
  rw [levelψOf_postcomp] at hb'
  replace hb := hb' 
  have e := congrArg (F.obj.map (eqToHom (congrArg (fun Y' => (smallEtalePostcomp
      (toBottom D c B hD hX hc (Lv D c B hD hX hc j))).obj
      ((levelToEtale D c B hD hX hc (Lv D c B hD hX hc j)).obj Y'))
      (u_from_obj (arr D c B hD hX hc d) Y).symm)).op) hb
  simp only [levelψPost] at e
  simp only [pcMap, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact e

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- Restricting a section of `F` along `g` and then along `f` is restricting along `f ≫ g`. -/
theorem sheaf_map_comp_apply {V₁ V₂ V₃ : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale}
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (y : F.obj.obj (op V₃)) :
    F.obj.map f.op (F.obj.map g.op y) = F.obj.map (f ≫ g).op y :=
  (F.obj.map_comp_apply g.op f.op y).symm

/-- **Stacks 09YQ in degree zero for sheaves of sets, along a finite open cover of `X_⊥`.** If
`X_⊥` is covered by finitely many objects of its small affine étale site with open immersion
structure maps, whose pairwise overlaps are covered by such objects, then the maps
`F(X_i) ⟶ Γ(X, f⁻¹F)` exhibit `Γ(X, f⁻¹F)` as the filtered colimit of the `F(X_i)`. -/
theorem wholeSections_colimit {K O : Type*} [Finite K] [Finite O] (src tgt : O → K)
    (Ym : K → (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (Yo : O → (sys D c B hD hX hc).C (bottom D c B hD hX hc))
    (o₁ : ∀ o, Yo o ⟶ Ym (src o)) (o₂ : ∀ o, Yo o ⟶ Ym (tgt o))
    [hYm : ∀ k, IsOpenImmersion
      ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Ym k)).hom]
    [hYo : ∀ o, IsOpenImmersion
      ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Yo o)).hom]
    (hcov : ∀ x : lvl D c B hD hX hc (bottom D c B hD hX hc), ∃ k,
      x ∈ Set.range ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Ym k)).hom.base)
    (hov : ∀ k l,
      Set.range ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Ym k)).hom.base ∩
        Set.range ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Ym l)).hom.base ⊆
      ⋃ (o : O) (_ : src o = k ∧ tgt o = l),
        Set.range ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (Yo o)).hom.base) :
    (∀ s : ((limitL D c B hD hX hc).obj F).obj.obj (op (unitT D c)),
        ∃ (i : I) (x : F.obj.obj (op (wh D c B hD hX hc i))),
          wholeSections D c B hD hX hc F i x = s) ∧
      ∀ (i : I) (x x' : F.obj.obj (op (wh D c B hD hX hc i))),
        wholeSections D c B hD hX hc F i x = wholeSections D c B hD hX hc F i x' →
          ∃ (j : I) (d : i ≤ j), F.obj.map (whMap D c B hD hX hc d).op x =
            F.obj.map (whMap D c B hD hX hc d).op x' := by
  have key : ∀ {P S T Z : Scheme.{max u v}} {a : P ⟶ S} {b : P ⟶ T} {f : S ⟶ Z} {g : T ⟶ Z},
      IsPullback a b f g → ∀ [IsOpenImmersion f],
        IsOpenImmersion b ∧ ∀ t, t ∈ Set.range b.base ↔ g.base t ∈ Set.range f.base :=
    fun h _ => ⟨MorphismProperty.of_isPullback (P := @IsOpenImmersion) h inferInstance,
      mem_range_snd_iff_of_isPullback h⟩
  let toWh' : ∀ (i : I) (Y : (sys D c B hD hX hc).C (bottom D c B hD hX hc)),
      (levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).obj
          (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj Y) ⟶
        Scheme.Etale.mk (𝟙 (lvl D c B hD hX hc (Lv D c B hD hX hc i))) := fun i Y =>
    MorphismProperty.Over.homMk (str i Y) (Category.comp_id _) trivial
  have : ∀ i k, IsOpenImmersion (toWh' i (Ym k)).left := fun i k =>
    (key (isPullback_prj_str i (Ym k))).1
  have : ∀ k, IsOpenImmersion (toWT (Ym k)).left := fun k => (key (isPullback_prjT (Ym k))).1
  have hcovL : ∀ (i : I)
      (t : (Scheme.Etale.mk (𝟙 (lvl D c B hD hX hc (Lv D c B hD hX hc i)))).left),
      ∃ k, t ∈ Set.range (toWh' i (Ym k)).left.base := fun i t => by
    obtain ⟨k, hk⟩ := hcov ((toBottom D c B hD hX hc (Lv D c B hD hX hc i)).base t)
    exact ⟨k, ((key (isPullback_prj_str i (Ym k))).2 t).2 hk⟩
  have hcovT : ∀ t : (unitT D c).left, ∃ k, t ∈ Set.range (toWT (Ym k)).left.base := fun t => by
    obtain ⟨k, hk⟩ := hcov ((lvlπ D c B hD hX hc (bottom D c B hD hX hc)).base t)
    exact ⟨k, ((key (isPullback_prjT (Ym k))).2 t).2 hk⟩
  refine Stacks.Germs.colimit_of_finite_equalizer src tgt
    (E := fun i => F.obj.obj (op (wh D c B hD hX hc i)))
    (P := fun i k => F.obj.obj (op (pc i (Ym k))))
    (Q := fun i o => F.obj.obj (op (pc i (Yo o))))
    (fun i k => F.obj.map (toWh i (Ym k)).op) (fun i o => F.obj.map (pcHom i (o₁ o)).op)
    (fun i o => F.obj.map (pcHom i (o₂ o)).op)
    (fun k => ((limitL D c B hD hX hc).obj F).obj.map (toWT (Ym k)).op)
    (fun o => ((limitL D c B hD hX hc).obj F).obj.map (pcTHom (o₁ o)).op)
    (fun o => ((limitL D c B hD hX hc).obj F).obj.map (pcTHom (o₂ o)).op)
    (fun d => F.obj.map (whMap D c B hD hX hc d).op) (fun d k => F.obj.map (pcMap d (Ym k)).op)
    (fun d o => F.obj.map (pcMap d (Yo o)).op)
    (fun i => wholeSections D c B hD hX hc F i)
    (fun i k => limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
      (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) (Ym k))
    (fun i o => limitρOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
      (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F (fr D c B hD hX hc i) (Yo o))
    ?sep ?glue ?sepw ?cocycle ?htP ?htQ ?hrE ?hq₁ ?hq₂ ?hτPt ?hτPr ?hτQ₁ ?hτQ₂ ?surj ?inj ?injQ
  case sep =>
    intro i x y h
    exact etaleSheaf_sep_of_openImmersion ((postcompL D c B hD hX hc (Lv D c B hD hX hc i)).obj F)
      _ (fun k => toWh' i (Ym k)) (hcovL i) x y h
  case glue =>
    intro i z hz
    exact etaleSheaf_glue_of_openImmersion ((postcompL D c B hD hX hc (Lv D c B hD hX hc i)).obj F)
      _ (fun k => toWh' i (Ym k)) (hcovL i) src tgt
      (fun o => (levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).obj
        (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).obj (Yo o)))
      (fun o => (levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).map
        (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).map (o₁ o)))
      (fun o => (levelToEtale D c B hD hX hc (Lv D c B hD hX hc i)).map
        (((sys D c B hD hX hc).u (fr D c B hD hX hc i)).map (o₂ o)))
      (fun o => MorphismProperty.Over.Hom.ext
        ((pcHom_left_str i (o₁ o)).trans (pcHom_left_str i (o₂ o)).symm))
      (fun o => (congrArg (fun m : _ ⟶ lvl D c B hD hX hc (Lv D c B hD hX hc i) =>
          IsOpenImmersion m) (pcHom_left_str i (o₁ o))).mpr (key (isPullback_prj_str i (Yo o))).1)
      (fun k l t ht => by
        obtain ⟨o, ho, hto⟩ := Set.mem_iUnion₂.1
          (hov k l ⟨((key (isPullback_prj_str i (Ym k))).2 t).1 ht.1,
            ((key (isPullback_prj_str i (Ym l))).2 t).1 ht.2⟩)
        refine Set.mem_iUnion₂.2 ⟨o, ho, ?_⟩
        exact (congrArg (fun m : _ ⟶ lvl D c B hD hX hc (Lv D c B hD hX hc i) =>
          t ∈ Set.range m.base) (pcHom_left_str i (o₁ o))).mpr
          (((key (isPullback_prj_str i (Yo o))).2 t).2 hto))
      z hz
  case sepw =>
    intro x y h
    exact etaleSheaf_sep_of_openImmersion ((limitL D c B hD hX hc).obj F) _
      (fun k => toWT (Ym k)) hcovT x y h
  case cocycle =>
    intro x o
    simp only [map_comp_apply', pcTHom_toWT]
  case htP =>
    intro i j k d e a y
    rw [sheaf_map_comp_apply, ← pcMap_trans]
  case htQ =>
    intro i j k d e o y
    rw [sheaf_map_comp_apply, ← pcMap_trans]
  case hrE =>
    intro i j d a x
    simp only [sheaf_map_comp_apply, pcMap_toWh]
  case hq₁ =>
    intro i j d o y
    simp only [sheaf_map_comp_apply, pcMap_pcHom]
  case hq₂ =>
    intro i j d o y
    simp only [sheaf_map_comp_apply, pcMap_pcHom]
  case hτPt => intro i j d a y; exact ρ_pcMap F d (Ym a) y
  case hτPr => intro i a x; exact ρ_toWh F i (Ym a) x
  case hτQ₁ => intro i o y; exact ρ_pcHom F i (o₁ o) y
  case hτQ₂ => intro i o y; exact ρ_pcHom F i (o₂ o) y
  case surj => intro a s; exact ρ_surj F (Ym a) s
  case inj => intro i a y y' h; exact ρ_inj F (Ym a) i y y' h
  case injQ => intro i o y y' h; exact ρ_inj F (Yo o) i y y' h

/-! ### Affine opens of `X_⊥` as objects of the bottom level -/


variable (D c B hD hX hc) in
/-- An affine open of `X_⊥`, as an object of the bottom level of the system. -/
def openObj (U : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens) (hU : IsAffineOpen U) :
    (sys D c B hD hX hc).C (bottom D c B hD hX hc) :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv (bottom D c B hD hX hc)).inverse.obj
    (QcqsLimitCohomology.objOfAffineOpen B _ (hD _) U hU)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The structure morphism of the object of the small affine étale site attached to an affine open
`U` is the inclusion `U.ι`. -/
theorem affineToEtale_objOfAffineOpen_hom (U : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens)
    (hU : IsAffineOpen U) :
    ((affineToEtale B _ (hD _)).obj (QcqsLimitCohomology.objOfAffineOpen B _ (hD _) U hU)).hom =
      U.ι :=
  QcqsLimitCohomology.structMap_objOfAffineOpen B _ (hD _) U hU

/-- The object attached to an affine open is that open, up to isomorphism in the small étale
site. -/
def openObjIso (U : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens) (hU : IsAffineOpen U) :
    (levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj (openObj D c B hD hX hc U hU) ≅
      (affineToEtale B _ (hD _)).obj (QcqsLimitCohomology.objOfAffineOpen B _ (hD _) U hU) :=
  (affineToEtale B _ (hD _)).mapIso
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv (bottom D c B hD hX hc)).counitIso.app
      (QcqsLimitCohomology.objOfAffineOpen B _ (hD _) U hU))

/-- The structure morphism of the object attached to an affine open is an open immersion. -/
instance openObj_isOpenImmersion (U : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens)
    (hU : IsAffineOpen U) :
    IsOpenImmersion ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj
      (openObj D c B hD hX hc U hU)).hom :=
  isOpenImmersion_hom_of_iso (openObjIso U hU)
    ((congrArg (fun m : _ ⟶ lvl D c B hD hX hc (bottom D c B hD hX hc) => IsOpenImmersion m)
      (affineToEtale_objOfAffineOpen_hom U hU)).mpr (inferInstanceAs (IsOpenImmersion U.ι)))

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The image of the structure morphism of the object attached to an affine open `U` is `U`. -/
theorem range_openObj (U : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens)
    (hU : IsAffineOpen U) :
    Set.range ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj
      (openObj D c B hD hX hc U hU)).hom.base =
        (U : Set (lvl D c B hD hX hc (bottom D c B hD hX hc))) := by
  rw [range_hom_of_iso (openObjIso U hU)]
  exact (congrArg (fun m : _ ⟶ lvl D c B hD hX hc (bottom D c B hD hX hc) => Set.range m.base)
    (affineToEtale_objOfAffineOpen_hom U hU)).trans (Scheme.Opens.range_ι U)

/-- The inclusion of affine opens `V ≤ U` of `X_⊥`, as a morphism of the bottom level. -/
def openHom {U V : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) : openObj D c B hD hX hc V hV ⟶ openObj D c B hD hX hc U hU :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv (bottom D c B hD hX hc)).inverse.map
    ((affineToEtale B _ (hD _)).preimage (MorphismProperty.Over.homMk
      ((lvl D c B hD hX hc (bottom D c B hD hX hc)).homOfLE h)
      ((congrArg (_ ≫ ·) (affineToEtale_objOfAffineOpen_hom U hU)).trans
        (((lvl D c B hD hX hc (bottom D c B hD hX hc)).homOfLE_ι h).trans
          (affineToEtale_objOfAffineOpen_hom V hV).symm)) trivial))

/-- **Stacks 09YQ in degree zero for sheaves of sets, for a quasi-compact and quasi-separated
`X_⊥`.** The maps `F(X_i) ⟶ Γ(X, f⁻¹F)` exhibit `Γ(X, f⁻¹F)` as the filtered colimit of the
`F(X_i)`: every global section of `f⁻¹F` comes from some `X_i`, and two sections over `X_i` with
the same image agree on some `X_j`, `j ≥ i`. -/
theorem wholeSections_colimit_of_qcqs [CompactSpace (lvl D c B hD hX hc (bottom D c B hD hX hc))]
    [QuasiSeparatedSpace (lvl D c B hD hX hc (bottom D c B hD hX hc))] :
    (∀ s : ((limitL D c B hD hX hc).obj F).obj.obj (op (unitT D c)),
        ∃ (i : I) (x : F.obj.obj (op (wh D c B hD hX hc i))),
          wholeSections D c B hD hX hc F i x = s) ∧
      ∀ (i : I) (x x' : F.obj.obj (op (wh D c B hD hX hc i))),
        wholeSections D c B hD hX hc F i x = wholeSections D c B hD hX hc F i x' →
          ∃ (j : I) (d : i ≤ j), F.obj.map (whMap D c B hD hX hc d).op x =
            F.obj.map (whMap D c B hD hX hc d).op x' := by
  classical
  obtain ⟨K, hK, U, hUaff, -, hUcov⟩ := exists_finite_affine_cover
    (⊤ : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Opens) isCompact_univ
  have hint : ∀ kl : K × K, IsCompact ((U kl.1 ⊓ U kl.2 : (lvl D c B hD hX hc
      (bottom D c B hD hX hc)).Opens) : Set (lvl D c B hD hX hc (bottom D c B hD hX hc))) :=
    fun kl => (hUaff kl.1).isCompact.inter_of_isOpen (hUaff kl.2).isCompact (U kl.1).isOpen
      (U kl.2).isOpen
  choose ι hι V hVaff hVle hVcov using fun kl : K × K => exists_finite_affine_cover _ (hint kl)
  let O := Σ kl : K × K, ι kl
  have : Finite O := inferInstance
  exact wholeSections_colimit F (O := O) (fun o => o.1.1) (fun o => o.1.2)
    (fun k => openObj D c B hD hX hc (U k) (hUaff k))
    (fun o => openObj D c B hD hX hc (V o.1 o.2) (hVaff o.1 o.2))
    (fun o => openHom _ _ ((hVle o.1 o.2).trans inf_le_left))
    (fun o => openHom _ _ ((hVle o.1 o.2).trans inf_le_right))
    (fun x => by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hUcov (Set.mem_univ x))
      refine ⟨k, ?_⟩
      rw [range_openObj (U k) (hUaff k)]
      exact hk)
    (fun k l x hx => by
      rw [range_openObj, range_openObj] at hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (hVcov (k, l) hx)
      refine Set.mem_iUnion₂.2 ⟨⟨(k, l), m⟩, ⟨rfl, rfl⟩, ?_⟩
      rw [range_openObj (V (k, l) m) (hVaff (k, l) m)]
      exact hm)

/-! ### Reading the levels back in the original system -/

omit [OrderBot I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The scheme at the level `Lv i` is `X_i`. -/
theorem lvl_Lv (i : I) : lvl D c B hD hX hc (Lv D c B hD hX hc i) = D.obj (op i) := by
  show D.obj (op i) = D.obj (op i)
  rfl

omit [OrderBot I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The transition of the system attached to `i ≤ j` is the transition `X_j ⟶ X_i` of `D`. -/
theorem lvlMap_arr {i j : I} (d : i ≤ j) :
    lvlMap D c B hD hX hc (arr D c B hD hX hc d) =
      eqToHom (lvl_Lv j) ≫ D.map (homOfLE d).op ≫ eqToHom (lvl_Lv i).symm := by
  show D.map (homOfLE d).op = 𝟙 _ ≫ D.map (homOfLE d).op ≫ 𝟙 _
  simp

omit [OrderBot I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The projection of the system to the level `Lv i` is the limit projection `X ⟶ X_i`. -/
theorem lvlπ_Lv (i : I) :
    lvlπ D c B hD hX hc (Lv D c B hD hX hc i) = c.π.app (op i) ≫ eqToHom (lvl_Lv i).symm := by
  show c.π.app (op i) = c.π.app (op i) ≫ 𝟙 _
  simp

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The morphism from the level `Lv i` to the bottom level is the transition `X_i ⟶ X_⊥` of `D`. -/
theorem toBottom_Lv (i : I) :
    toBottom D c B hD hX hc (Lv D c B hD hX hc i) ≫ eqToHom (lvl_bottom D c B hD hX hc) =
      eqToHom (lvl_Lv i) ≫ D.map (homOfLE (bot_le : ⊥ ≤ i)).op := by
  show D.map (homOfLE (bot_le : ⊥ ≤ i)).op ≫ 𝟙 _ = 𝟙 _ ≫ D.map (homOfLE (bot_le : ⊥ ≤ i)).op
  simp

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The projection of the system to the bottom level is the limit projection `X ⟶ X_⊥`. -/
theorem lvlπ_bottom :
    lvlπ D c B hD hX hc (bottom D c B hD hX hc) ≫ eqToHom (lvl_bottom D c B hD hX hc) =
      c.π.app (op ⊥) := by
  show c.π.app (op ⊥) ≫ 𝟙 _ = c.π.app (op ⊥)
  simp

end Stacks.EtaleCohomology.LimitSiteBridge
