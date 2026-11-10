module

public import
StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumExactSequence

/-!
# The gluing isomorphism over the double fibre product

## Main definitions

* `AlgebraicGeometry.gluingIsoPullbackFstSnd`: for a cover `Y` of `T₀` agreeing with a cover `V` of
  `U` over the preimage of `U`, an isomorphism between the two base changes of `Y` to `T₀ ×_B T₀`,
  when base change along the preimage of `U` in `T₀ ×_B T₀` is fully faithful.
* `AlgebraicGeometry.pullbackMorphismRestrictIsoPreimage`: the identification of `f⁻¹U ×_U f⁻¹U`
  with the preimage of `U` in `T₀ ×_B T₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### The gluing isomorphism over the double fibre product -/

/-! #### Generalized points of base-changed covers -/

/-- The generalized point of a base-changed finite étale cover with the given two components:
`CategoryTheory.Limits.pullback.lift` at the type of the base-changed object. -/
def finiteEtaleBaseChangeLift {S T : Scheme.{u}} (u : S ⟶ T) (A : FiniteEtaleOver T)
    {Z' : Scheme.{u}} (p : Z' ⟶ A.left) (z : Z' ⟶ S) (hp : p ≫ A.hom = z ≫ u) :
    Z' ⟶ ((finiteEtaleBaseChange u).obj A).left :=
  pullback.lift p z hp

/-- The point of a base change built from its components projects to the point of the cover. -/
@[simp]
lemma finiteEtaleBaseChangeLift_comp_proj {S T : Scheme.{u}} (u : S ⟶ T) (A : FiniteEtaleOver T)
    {Z' : Scheme.{u}} (p : Z' ⟶ A.left) (z : Z' ⟶ S) (hp : p ≫ A.hom = z ≫ u) :
    finiteEtaleBaseChangeLift u A p z hp ≫ finiteEtaleBaseChangeProj u A = p :=
  pullback.lift_fst _ _ _

/-- The point of a base change built from its components lies over the point of the base. -/
@[simp]
lemma finiteEtaleBaseChangeLift_comp_hom {S T : Scheme.{u}} (u : S ⟶ T) (A : FiniteEtaleOver T)
    {Z' : Scheme.{u}} (p : Z' ⟶ A.left) (z : Z' ⟶ S) (hp : p ≫ A.hom = z ≫ u) :
    finiteEtaleBaseChangeLift u A p z hp ≫ ((finiteEtaleBaseChange u).obj A).hom = z :=
  pullback.lift_snd _ _ _

/-- A generalized point of a base change depends on its two components, not on the proof that
one lies over the other. -/
lemma finiteEtaleBaseChangeLift_congr {S T : Scheme.{u}} (u : S ⟶ T) (A : FiniteEtaleOver T)
    {Z' : Scheme.{u}} (p : Z' ⟶ A.left) {z z' : Z' ⟶ S} (hz : z = z')
    (hp : p ≫ A.hom = z ≫ u) (hp' : p ≫ A.hom = z' ≫ u) :
    finiteEtaleBaseChangeLift u A p z hp = finiteEtaleBaseChangeLift u A p z' hp' := by
  subst hz; rfl

/-- The generalized point of a twice base-changed finite étale cover with the given point of `A`
and point of the innermost base. -/
def finiteEtaleBaseChangeLift₂ {S S' T : Scheme.{u}} (j : S ⟶ S') (c : S' ⟶ T)
    (A : FiniteEtaleOver T) {Z' : Scheme.{u}} (u : Z' ⟶ A.left) (w : Z' ⟶ S)
    (hu : u ≫ A.hom = (w ≫ j) ≫ c) :
    Z' ⟶ ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj A)).left :=
  finiteEtaleBaseChangeLift j _ (finiteEtaleBaseChangeLift c A u (w ≫ j) hu) w
    (finiteEtaleBaseChangeLift_comp_hom _ _ _ _ _)

/-- The point of a twofold base change built from its components projects to the point of the
intermediate base change. -/
@[simp]
lemma finiteEtaleBaseChangeLift₂_comp_proj {S S' T : Scheme.{u}} (j : S ⟶ S') (c : S' ⟶ T)
    (A : FiniteEtaleOver T) {Z' : Scheme.{u}} (u : Z' ⟶ A.left) (w : Z' ⟶ S)
    (hu : u ≫ A.hom = (w ≫ j) ≫ c) :
    finiteEtaleBaseChangeLift₂ j c A u w hu ≫
        finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange c).obj A) =
      finiteEtaleBaseChangeLift c A u (w ≫ j) hu :=
  finiteEtaleBaseChangeLift_comp_proj _ _ _ _ _

/-- The point of a twofold base change built from its components projects to the point of the
cover. -/
@[simp]
lemma finiteEtaleBaseChangeLift₂_comp_proj_proj {S S' T : Scheme.{u}} (j : S ⟶ S') (c : S' ⟶ T)
    (A : FiniteEtaleOver T) {Z' : Scheme.{u}} (u : Z' ⟶ A.left) (w : Z' ⟶ S)
    (hu : u ≫ A.hom = (w ≫ j) ≫ c) :
    finiteEtaleBaseChangeLift₂ j c A u w hu ≫
        finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange c).obj A) ≫
        finiteEtaleBaseChangeProj c A = u := by
  rw [finiteEtaleBaseChangeLift₂, ← Category.assoc, finiteEtaleBaseChangeLift_comp_proj,
    finiteEtaleBaseChangeLift_comp_proj]

/-- The point of a twofold base change built from its components lies over the point of the
innermost base. -/
@[simp]
lemma finiteEtaleBaseChangeLift₂_comp_hom {S S' T : Scheme.{u}} (j : S ⟶ S') (c : S' ⟶ T)
    (A : FiniteEtaleOver T) {Z' : Scheme.{u}} (u : Z' ⟶ A.left) (w : Z' ⟶ S)
    (hu : u ≫ A.hom = (w ≫ j) ≫ c) :
    finiteEtaleBaseChangeLift₂ j c A u w hu ≫
        ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj A)).hom = w :=
  finiteEtaleBaseChangeLift_comp_hom _ _ _ _ _

/-- A generalized point of a twice base-changed cover is determined by its components. -/
lemma finiteEtaleBaseChangeLift₂_eq {S S' T : Scheme.{u}} (j : S ⟶ S') (c : S' ⟶ T)
    (A : FiniteEtaleOver T) {Z' : Scheme.{u}}
    (m : Z' ⟶ ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj A)).left)
    (u : Z' ⟶ A.left) (w : Z' ⟶ S) (hu : u ≫ A.hom = (w ≫ j) ≫ c)
    (hm₁ : m ≫ finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange c).obj A) ≫
      finiteEtaleBaseChangeProj c A = u)
    (hm₂ : m ≫ ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj A)).hom = w) :
    m = finiteEtaleBaseChangeLift₂ j c A u w hu := by
  refine finiteEtaleBaseChangeProj_hom_ext j ((finiteEtaleBaseChange c).obj A) ?_ ?_
  · refine finiteEtaleBaseChangeProj_hom_ext c A ?_ ?_
    · rw [finiteEtaleBaseChangeLift₂_comp_proj, finiteEtaleBaseChangeLift_comp_proj,
        Category.assoc, hm₁]
    · rw [finiteEtaleBaseChangeLift₂_comp_proj, finiteEtaleBaseChangeLift_comp_hom,
        Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc, hm₂]
  · rw [finiteEtaleBaseChangeLift₂_comp_hom, hm₂]

/-- The inverse of the composition comparison isomorphism is also compatible with the
projections to the original cover. -/
lemma finiteEtaleBaseChangeComp_inv_app_left_proj {S T T' : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ T')
    (fg : S ⟶ T') (hfg : fg = f ≫ g) (A : FiniteEtaleOver T') :
    ((finiteEtaleBaseChangeComp f g fg hfg).inv.app A).left ≫ finiteEtaleBaseChangeProj fg A =
      finiteEtaleBaseChangeProj f ((finiteEtaleBaseChange g).obj A) ≫
        finiteEtaleBaseChangeProj g A := by
  have hid : ((finiteEtaleBaseChangeComp f g fg hfg).inv.app A).left ≫
      ((finiteEtaleBaseChangeComp f g fg hfg).hom.app A).left = 𝟙 _ := by
    rw [← MorphismProperty.Comma.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]
    rfl
  rw [← finiteEtaleBaseChangeComp_hom_app_left_proj f g fg hfg A, ← Category.assoc, hid,
    Category.id_comp]

/-- Base change along equal morphisms, compared as functors by `eqToIso`, is compatible with the
projections to the original cover. -/
lemma eqToIso_finiteEtaleBaseChange_app_left_proj {S T : Scheme.{u}} {n₁ n₂ : S ⟶ T}
    (hn : n₁ = n₂) (A : FiniteEtaleOver T) :
    ((eqToIso (congrArg finiteEtaleBaseChange hn)).app A).hom.left ≫
        finiteEtaleBaseChangeProj n₂ A = finiteEtaleBaseChangeProj n₁ A := by
  subst hn
  exact Category.id_comp _

/-- Base change along equal morphisms, compared objectwise by `eqToIso`, is compatible with the
projections to the original cover. -/
lemma eqToIso_finiteEtaleBaseChange_obj_left_proj {S T : Scheme.{u}} {n₁ n₂ : S ⟶ T}
    (hn : n₁ = n₂) (A : FiniteEtaleOver T) :
    (eqToIso (congrArg (fun k => (finiteEtaleBaseChange k).obj A) hn)).hom.left ≫
        finiteEtaleBaseChangeProj n₂ A = finiteEtaleBaseChangeProj n₁ A := by
  subst hn
  exact Category.id_comp _

/-- Base change along equal morphisms, compared objectwise by `eqToIso`, lies over the base. -/
lemma eqToIso_finiteEtaleBaseChange_obj_left_comp_hom {S T : Scheme.{u}} {n₁ n₂ : S ⟶ T}
    (hn : n₁ = n₂) (A : FiniteEtaleOver T) :
    (eqToIso (congrArg (fun k => (finiteEtaleBaseChange k).obj A) hn)).hom.left ≫
        ((finiteEtaleBaseChange n₂).obj A).hom = ((finiteEtaleBaseChange n₁).obj A).hom :=
  MorphismProperty.Over.w _

/-- For `j ≫ p = r ≫ s`, base change along `p` followed by base change along `j` is isomorphic to
base change along `s` followed by base change along `r`. -/
def finiteEtaleBaseChangeFactorIso {A A' C D : Scheme.{u}} (j : A ⟶ A') (p : A' ⟶ C)
    (r : A ⟶ D) (s : D ⟶ C) (h : j ≫ p = r ≫ s) :
    finiteEtaleBaseChange p ⋙ finiteEtaleBaseChange j ≅
      finiteEtaleBaseChange s ⋙ finiteEtaleBaseChange r :=
  (finiteEtaleBaseChangeComp j p (j ≫ p) rfl).symm ≪≫
    eqToIso (congrArg finiteEtaleBaseChange h) ≪≫
    finiteEtaleBaseChangeComp r s (r ≫ s) rfl

/-- The comparison isomorphism of a factorization, written out as a composite of its three
stages. -/
lemma finiteEtaleBaseChangeFactorIso_app_hom_left {A A' C D : Scheme.{u}} (j : A ⟶ A')
    (p : A' ⟶ C) (r : A ⟶ D) (s : D ⟶ C) (h : j ≫ p = r ≫ s) (Y : FiniteEtaleOver C) :
    ((finiteEtaleBaseChangeFactorIso j p r s h).app Y).hom.left =
      ((finiteEtaleBaseChangeComp j p (j ≫ p) rfl).inv.app Y).left ≫
        ((eqToIso (congrArg finiteEtaleBaseChange h)).app Y).hom.left ≫
        ((finiteEtaleBaseChangeComp r s (r ≫ s) rfl).hom.app Y).left := rfl

/-- The comparison isomorphism of a factorization commutes with the projections of the two iterated
base changes to `Y`. -/
lemma finiteEtaleBaseChangeFactorIso_app_hom_left_proj_proj {A A' C D : Scheme.{u}} (j : A ⟶ A')
    (p : A' ⟶ C) (r : A ⟶ D) (s : D ⟶ C) (h : j ≫ p = r ≫ s) (Y : FiniteEtaleOver C) :
    ((finiteEtaleBaseChangeFactorIso j p r s h).app Y).hom.left ≫
        finiteEtaleBaseChangeProj r ((finiteEtaleBaseChange s).obj Y) ≫
        finiteEtaleBaseChangeProj s Y =
      finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange p).obj Y) ≫
        finiteEtaleBaseChangeProj p Y := by
  rw [finiteEtaleBaseChangeFactorIso_app_hom_left, Category.assoc, Category.assoc,
    finiteEtaleBaseChangeComp_hom_app_left_proj,
    eqToIso_finiteEtaleBaseChange_app_left_proj h,
    finiteEtaleBaseChangeComp_inv_app_left_proj]

/-- The comparison isomorphism of a factorization lies over the base. -/
lemma finiteEtaleBaseChangeFactorIso_app_hom_left_comp_hom {A A' C D : Scheme.{u}} (j : A ⟶ A')
    (p : A' ⟶ C) (r : A ⟶ D) (s : D ⟶ C) (h : j ≫ p = r ≫ s) (Y : FiniteEtaleOver C) :
    ((finiteEtaleBaseChangeFactorIso j p r s h).app Y).hom.left ≫
        ((finiteEtaleBaseChange r).obj ((finiteEtaleBaseChange s).obj Y)).hom =
      ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange p).obj Y)).hom :=
  MorphismProperty.Over.w _

/-- The comparison isomorphism of a factorization on generalized points: it leaves the point of the
cover and the point of the base unchanged. -/
lemma finiteEtaleBaseChangeLift₂_comp_factorIso {A A' C D : Scheme.{u}} (j : A ⟶ A')
    (p : A' ⟶ C) (r : A ⟶ D) (s : D ⟶ C) (h : j ≫ p = r ≫ s) (Y : FiniteEtaleOver C)
    {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (w : Z' ⟶ A) (hu : u ≫ Y.hom = (w ≫ j) ≫ p)
    (hu' : u ≫ Y.hom = (w ≫ r) ≫ s) :
    finiteEtaleBaseChangeLift₂ j p Y u w hu ≫
        ((finiteEtaleBaseChangeFactorIso j p r s h).app Y).hom.left =
      finiteEtaleBaseChangeLift₂ r s Y u w hu' := by
  refine finiteEtaleBaseChangeProj_hom_ext r ((finiteEtaleBaseChange s).obj Y) ?_ ?_
  · refine finiteEtaleBaseChangeProj_hom_ext s Y ?_ ?_
    · simp only [Category.assoc, finiteEtaleBaseChangeFactorIso_app_hom_left_proj_proj,
        finiteEtaleBaseChangeLift₂_comp_proj_proj]
    · simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
      simp only [← Category.assoc, finiteEtaleBaseChangeFactorIso_app_hom_left_comp_hom,
        finiteEtaleBaseChangeLift₂_comp_hom]
  · simp only [Category.assoc, finiteEtaleBaseChangeFactorIso_app_hom_left_comp_hom,
      finiteEtaleBaseChangeLift₂_comp_hom]

/-! #### Transport of generalized points along the identification -/

section Transport

variable {T₀ Z U₀ : Scheme.{u}} {g : Z ⟶ T₀} {h : Z ⟶ U₀} {Y : FiniteEtaleOver T₀}
  {V : FiniteEtaleOver U₀}
  (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)

/-- Transport of a generalized point along an identification of two base changes: given
`ε : g ^* Y ≅ h ^* V` and a point `u` of `Y` lying over a point `z` of the common source of `g` and
`h`, the corresponding point of `V`. -/
def transportPoint {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (z : Z' ⟶ Z)
    (hu : u ≫ Y.hom = z ≫ g) : Z' ⟶ V.left :=
  finiteEtaleBaseChangeLift g Y u z hu ≫ ε.hom.left ≫ finiteEtaleBaseChangeProj h V

/-- Transport of a generalized point in the other direction, along the inverse of `ε`. -/
def transportPointSymm {Z' : Scheme.{u}} (p : Z' ⟶ V.left) (z : Z' ⟶ Z)
    (hp : p ≫ V.hom = z ≫ h) : Z' ⟶ Y.left :=
  finiteEtaleBaseChangeLift h V p z hp ≫ ε.inv.left ≫ finiteEtaleBaseChangeProj g Y

/-- The transported point lies over the image of the base point. -/
lemma transportPoint_comp_hom {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (z : Z' ⟶ Z)
    (hu : u ≫ Y.hom = z ≫ g) : transportPoint ε u z hu ≫ V.hom = z ≫ h := by
  have hw : ε.hom.left ≫ ((finiteEtaleBaseChange h).obj V).hom =
      ((finiteEtaleBaseChange g).obj Y).hom := MorphismProperty.Over.w ε.hom
  rw [transportPoint]
  slice_lhs 3 4 => rw [finiteEtaleBaseChangeProj_comp_hom]
  slice_lhs 2 3 => rw [hw]
  slice_lhs 1 2 => rw [finiteEtaleBaseChangeLift_comp_hom]

/-- The point transported in the other direction lies over the image of the base point. -/
lemma transportPointSymm_comp_hom {Z' : Scheme.{u}} (p : Z' ⟶ V.left) (z : Z' ⟶ Z)
    (hp : p ≫ V.hom = z ≫ h) : transportPointSymm ε p z hp ≫ Y.hom = z ≫ g :=
  transportPoint_comp_hom ε.symm p z hp

/-- Transport depends on its two points, not on the proof that one lies over the other. -/
lemma transportPoint_congr {Z' : Scheme.{u}} {u u' : Z' ⟶ Y.left} {z z' : Z' ⟶ Z} (huu : u = u')
    (hzz : z = z') (hu : u ≫ Y.hom = z ≫ g) (hu' : u' ≫ Y.hom = z' ≫ g) :
    transportPoint ε u z hu = transportPoint ε u' z' hu' := by
  subst huu; subst hzz; rfl

/-- Transport in the other direction depends on its two points, not on the proof that one lies
over the other. -/
lemma transportPointSymm_congr {Z' : Scheme.{u}} {p p' : Z' ⟶ V.left} {z z' : Z' ⟶ Z}
    (hpp : p = p') (hzz : z = z') (hp : p ≫ V.hom = z ≫ h) (hp' : p' ≫ V.hom = z' ≫ h) :
    transportPointSymm ε p z hp = transportPointSymm ε p' z' hp' :=
  transportPoint_congr ε.symm hpp hzz hp hp'

/-- Transporting a point and transporting it back gives the point. -/
lemma transportPointSymm_transportPoint {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (z : Z' ⟶ Z)
    (hu : u ≫ Y.hom = z ≫ g) (hv : transportPoint ε u z hu ≫ V.hom = z ≫ h) :
    transportPointSymm ε (transportPoint ε u z hu) z hv = u := by
  have key : finiteEtaleBaseChangeLift h V (transportPoint ε u z hu) z hv =
      finiteEtaleBaseChangeLift g Y u z hu ≫ ε.hom.left := by
    refine finiteEtaleBaseChangeProj_hom_ext h V ?_ ?_
    · rw [finiteEtaleBaseChangeLift_comp_proj, transportPoint, Category.assoc]
    · rw [finiteEtaleBaseChangeLift_comp_hom, Category.assoc, MorphismProperty.Over.w,
        finiteEtaleBaseChangeLift_comp_hom]
  rw [transportPointSymm, key, Category.assoc]
  slice_lhs 2 3 => rw [← MorphismProperty.Comma.comp_left, ε.hom_inv_id, finiteEtaleOver_id_left]
  rw [Category.id_comp, finiteEtaleBaseChangeLift_comp_proj]

/-- Transporting a point back and transporting it again gives the point. -/
lemma transportPoint_transportPointSymm {Z' : Scheme.{u}} (p : Z' ⟶ V.left) (z : Z' ⟶ Z)
    (hp : p ≫ V.hom = z ≫ h) (hq : transportPointSymm ε p z hp ≫ Y.hom = z ≫ g) :
    transportPoint ε (transportPointSymm ε p z hp) z hq = p :=
  transportPointSymm_transportPoint ε.symm p z hp hq

/-- Transport commutes with change of test scheme. -/
lemma comp_transportPoint {Z' Z'' : Scheme.{u}} (k : Z'' ⟶ Z') (u : Z' ⟶ Y.left) (z : Z' ⟶ Z)
    (hu : u ≫ Y.hom = z ≫ g) (hu' : (k ≫ u) ≫ Y.hom = (k ≫ z) ≫ g) :
    k ≫ transportPoint ε u z hu = transportPoint ε (k ≫ u) (k ≫ z) hu' := by
  have hk : k ≫ finiteEtaleBaseChangeLift g Y u z hu
      = finiteEtaleBaseChangeLift g Y (k ≫ u) (k ≫ z) hu' := by
    refine finiteEtaleBaseChangeProj_hom_ext g Y ?_ ?_
    · rw [Category.assoc, finiteEtaleBaseChangeLift_comp_proj,
        finiteEtaleBaseChangeLift_comp_proj]
    · rw [Category.assoc, finiteEtaleBaseChangeLift_comp_hom, finiteEtaleBaseChangeLift_comp_hom]
  rw [transportPoint, transportPoint, ← Category.assoc, hk]

/-- Applying `ε` to a generalized point of `g ^* Y` and projecting to `V` is transport of its two
components. -/
lemma comp_left_proj_eq_transportPoint {Z' : Scheme.{u}}
    (m : Z' ⟶ ((finiteEtaleBaseChange g).obj Y).left)
    (hm : (m ≫ finiteEtaleBaseChangeProj g Y) ≫ Y.hom
      = (m ≫ ((finiteEtaleBaseChange g).obj Y).hom) ≫ g) :
    m ≫ ε.hom.left ≫ finiteEtaleBaseChangeProj h V =
      transportPoint ε (m ≫ finiteEtaleBaseChangeProj g Y)
        (m ≫ ((finiteEtaleBaseChange g).obj Y).hom) hm := by
  rw [transportPoint, finiteEtaleBaseChangeProj_hom_ext g Y
    (finiteEtaleBaseChangeLift_comp_proj _ _ _ _ _)
    (finiteEtaleBaseChangeLift_comp_hom _ _ _ _ _)]

end Transport

/-! #### The two legs of the gluing isomorphism -/

section Leg

variable {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T) (c : T ⟶ T₀) (g : Z ⟶ T₀) (h : Z ⟶ U₀)
  (r : W ⟶ Z) (hc : j ≫ c = r ≫ g) (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
  (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)

/-- For `j ≫ c = r ≫ g`, the isomorphism between the base change of `Y` along `c` and then `j` and
the base change of `V` along `r ≫ h` induced by `ε`. -/
def restrictedGluingLeg :
    (finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj Y) ≅
      (finiteEtaleBaseChange (r ≫ h)).obj V :=
  (finiteEtaleBaseChangeFactorIso j c r g hc).app Y ≪≫ (finiteEtaleBaseChange r).mapIso ε ≪≫
    ((finiteEtaleBaseChangeComp r h (r ≫ h) rfl).app V).symm

/-- The leg, written out as a composite of its three stages. -/
lemma restrictedGluingLeg_hom_left :
    (restrictedGluingLeg j c g h r hc Y V ε).hom.left =
      ((finiteEtaleBaseChangeFactorIso j c r g hc).app Y).hom.left ≫
        ((finiteEtaleBaseChange r).map ε.hom).left ≫
        ((finiteEtaleBaseChangeComp r h (r ≫ h) rfl).inv.app V).left := rfl

/-- The leg lies over `W`. -/
lemma restrictedGluingLeg_hom_left_comp_hom :
    (restrictedGluingLeg j c g h r hc Y V ε).hom.left ≫
        ((finiteEtaleBaseChange (r ≫ h)).obj V).hom =
      ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj Y)).hom :=
  MorphismProperty.Over.w _

/-- The inverse of the leg lies over `W`. -/
lemma restrictedGluingLeg_inv_left_comp_hom :
    (restrictedGluingLeg j c g h r hc Y V ε).inv.left ≫
        ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange c).obj Y)).hom =
      ((finiteEtaleBaseChange (r ≫ h)).obj V).hom :=
  MorphismProperty.Over.w _

/-- On generalized points, the leg is transport along `ε`. -/
lemma restrictedGluingLeg_hom_left_proj {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (w : Z' ⟶ W)
    (hu : u ≫ Y.hom = (w ≫ j) ≫ c) (hu' : u ≫ Y.hom = (w ≫ r) ≫ g) :
    finiteEtaleBaseChangeLift₂ j c Y u w hu ≫ (restrictedGluingLeg j c g h r hc Y V ε).hom.left ≫
        finiteEtaleBaseChangeProj (r ≫ h) V = transportPoint ε u (w ≫ r) hu' := by
  rw [restrictedGluingLeg_hom_left]
  slice_lhs 1 2 => rw [finiteEtaleBaseChangeLift₂_comp_factorIso j c r g hc Y u w hu hu']
  slice_lhs 3 4 => rw [finiteEtaleBaseChangeComp_inv_app_left_proj]
  slice_lhs 2 3 => rw [finiteEtaleBaseChangeProj_naturality]
  rw [transportPoint]
  slice_lhs 1 2 => rw [finiteEtaleBaseChangeLift₂_comp_proj]
  rw [Category.assoc]

end Leg

/-- For `j ≫ a = r₁ ≫ g`, `j ≫ b = r₂ ≫ g` and `r₁ ≫ h = r₂ ≫ h`, the isomorphism between the base
changes of `Y` to `W` along `a` and along `b` given by identifying both, via `ε`, with the base
change of `V` along `r₁ ≫ h = r₂ ≫ h`. -/
def restrictedGluingIso {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T) (a b : T ⟶ T₀) (g : Z ⟶ T₀)
    (h : Z ⟶ U₀) (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g)
    (hr : r₁ ≫ h = r₂ ≫ h) (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V) :
    (finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange a).obj Y) ≅
      (finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange b).obj Y) :=
  restrictedGluingLeg j a g h r₁ ha Y V ε ≪≫
    eqToIso (congrArg (fun k => (finiteEtaleBaseChange k).obj V) hr) ≪≫
    (restrictedGluingLeg j b g h r₂ hb Y V ε).symm

/-! #### The restricted gluing isomorphism on generalized points -/

section Cocycle

variable {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T) (a b : T ⟶ T₀) (g : Z ⟶ T₀) (h : Z ⟶ U₀)
  (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g) (hr : r₁ ≫ h = r₂ ≫ h)
  (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
  (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)

/-- The restricted gluing isomorphism, written as one leg followed by the inverse of the
other. -/
lemma restrictedGluingIso_hom_left :
    (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε).hom.left =
      (restrictedGluingLeg j a g h r₁ ha Y V ε).hom.left ≫
        (eqToIso (congrArg (fun k => (finiteEtaleBaseChange k).obj V) hr)).hom.left ≫
        (restrictedGluingLeg j b g h r₂ hb Y V ε).inv.left := rfl

/-- The restricted gluing isomorphism followed by the second leg is the first leg. -/
lemma restrictedGluingIso_hom_left_comp_leg :
    (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε).hom.left ≫
        (restrictedGluingLeg j b g h r₂ hb Y V ε).hom.left =
      (restrictedGluingLeg j a g h r₁ ha Y V ε).hom.left ≫
        (eqToIso (congrArg (fun k => (finiteEtaleBaseChange k).obj V) hr)).hom.left := by
  rw [restrictedGluingIso_hom_left]
  slice_lhs 3 4 => rw [← MorphismProperty.Comma.comp_left,
    (restrictedGluingLeg j b g h r₂ hb Y V ε).inv_hom_id, finiteEtaleOver_id_left]
  rw [Category.comp_id]

/-- On generalized points, the restricted gluing isomorphism carries a point of the base change of
`Y` along `a`, over a point `w` of `W`, to the point of the base change along `b` obtained by
transporting to `V` over `w ≫ r₁` and transporting back over `w ≫ r₂`. -/
lemma restrictedGluingIso_hom_left_proj_proj {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (w : Z' ⟶ W)
    (hu : u ≫ Y.hom = (w ≫ j) ≫ a) (hu₁ : u ≫ Y.hom = (w ≫ r₁) ≫ g)
    (hp : transportPoint ε u (w ≫ r₁) hu₁ ≫ V.hom = (w ≫ r₂) ≫ h) :
    finiteEtaleBaseChangeLift₂ j a Y u w hu ≫
        (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε).hom.left ≫
        finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange b).obj Y) ≫
        finiteEtaleBaseChangeProj b Y =
      transportPointSymm ε (transportPoint ε u (w ≫ r₁) hu₁) (w ≫ r₂) hp := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = finiteEtaleBaseChangeLift₂ j a Y u w hu ≫
      (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε).hom.left := ⟨_, rfl⟩
  have hmhom : m ≫ ((finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange b).obj Y)).hom = w := by
    rw [hmdef, Category.assoc, MorphismProperty.Over.w, finiteEtaleBaseChangeLift₂_comp_hom]
  obtain ⟨u', hu'def⟩ : ∃ u', u' = m ≫
      finiteEtaleBaseChangeProj j ((finiteEtaleBaseChange b).obj Y) ≫
      finiteEtaleBaseChangeProj b Y := ⟨_, rfl⟩
  have hu'b : u' ≫ Y.hom = (w ≫ j) ≫ b := by
    rw [hu'def]
    slice_lhs 3 4 => rw [finiteEtaleBaseChangeProj_comp_hom]
    slice_lhs 2 3 => rw [finiteEtaleBaseChangeProj_comp_hom]
    slice_lhs 1 2 => rw [hmhom]
  have hu'g : u' ≫ Y.hom = (w ≫ r₂) ≫ g := by
    rw [hu'b, Category.assoc, hb, Category.assoc]
  have hmeq : m = finiteEtaleBaseChangeLift₂ j b Y u' w hu'b :=
    finiteEtaleBaseChangeLift₂_eq j b Y m u' w hu'b hu'def.symm hmhom
  have hlegb := restrictedGluingLeg_hom_left_proj j b g h r₂ hb Y V ε u' w hu'b hu'g
  have hlega := restrictedGluingLeg_hom_left_proj j a g h r₁ ha Y V ε u w hu hu₁
  have hkey : transportPoint ε u' (w ≫ r₂) hu'g = transportPoint ε u (w ≫ r₁) hu₁ := by
    rw [← hlegb, ← hlega, ← hmeq, hmdef]
    slice_lhs 2 3 => rw [restrictedGluingIso_hom_left_comp_leg]
    slice_lhs 3 4 => rw [eqToIso_finiteEtaleBaseChange_obj_left_proj hr V]
  rw [← Category.assoc, ← hmdef, ← hu'def,
    show u' = transportPointSymm ε (transportPoint ε u' (w ≫ r₂) hu'g) (w ≫ r₂)
      (transportPoint_comp_hom ε u' (w ≫ r₂) hu'g) from
    (transportPointSymm_transportPoint ε u' (w ≫ r₂) hu'g _).symm]
  exact transportPointSymm_congr ε hkey rfl _ hp

end Cocycle

/-- The isomorphism of the two base changes of `Y` to `T` whose base change along `j` is
`AlgebraicGeometry.restrictedGluingIso`, when base change along `j` is fully faithful. -/
def gluingIsoOfFullyFaithful {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T) (a b : T ⟶ T₀) (g : Z ⟶ T₀)
    (h : Z ⟶ U₀) (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g)
    (hr : r₁ ≫ h = r₂ ≫ h) (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)
    (hff : (finiteEtaleBaseChange j).FullyFaithful) :
    (finiteEtaleBaseChange a).obj Y ≅ (finiteEtaleBaseChange b).obj Y :=
  hff.preimageIso (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε)

/-- The base change of `AlgebraicGeometry.gluingIsoOfFullyFaithful` along `j` is
`AlgebraicGeometry.restrictedGluingIso`. -/
lemma map_gluingIsoOfFullyFaithful_hom {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T) (a b : T ⟶ T₀)
    (g : Z ⟶ T₀) (h : Z ⟶ U₀) (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g)
    (hr : r₁ ≫ h = r₂ ≫ h) (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)
    (hff : (finiteEtaleBaseChange j).FullyFaithful) :
    (finiteEtaleBaseChange j).map
        (gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff).hom =
      (restrictedGluingIso j a b g h r₁ r₂ ha hb hr Y V ε).hom :=
  hff.map_preimage _

/-- On generalized points of `W`, the isomorphism `AlgebraicGeometry.gluingIsoOfFullyFaithful`
carries a point `u` of `Y` over `w ≫ j ≫ a` to the point obtained by transporting `u` to `V` over
`w ≫ r₁` and transporting it back over `w ≫ r₂`. -/
lemma gluingIsoOfFullyFaithful_hom_left_proj {W T T₀ Z U₀ : Scheme.{u}} (j : W ⟶ T)
    (a b : T ⟶ T₀) (g : Z ⟶ T₀) (h : Z ⟶ U₀) (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g)
    (hb : j ≫ b = r₂ ≫ g) (hr : r₁ ≫ h = r₂ ≫ h) (Y : FiniteEtaleOver T₀)
    (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)
    (hff : (finiteEtaleBaseChange j).FullyFaithful)
    {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (w : Z' ⟶ W) (hu : u ≫ Y.hom = (w ≫ j) ≫ a)
    (hu₁ : u ≫ Y.hom = (w ≫ r₁) ≫ g)
    (hp : transportPoint ε u (w ≫ r₁) hu₁ ≫ V.hom = (w ≫ r₂) ≫ h) :
    finiteEtaleBaseChangeLift a Y u (w ≫ j) hu ≫
        (gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff).hom.left ≫
        finiteEtaleBaseChangeProj b Y =
      transportPointSymm ε (transportPoint ε u (w ≫ r₁) hu₁) (w ≫ r₂) hp := by
  have hnat := finiteEtaleBaseChangeProj_naturality j
    (gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff).hom
  rw [map_gluingIsoOfFullyFaithful_hom] at hnat
  rw [← finiteEtaleBaseChangeLift₂_comp_proj j a Y u w hu]
  slice_lhs 2 3 => rw [← hnat]
  exact restrictedGluingIso_hom_left_proj_proj j a b g h r₁ r₂ ha hb hr Y V ε u w hu hu₁ hp

/-- On generalized points of `W`, the isomorphism `AlgebraicGeometry.gluingIsoOfFullyFaithful`
carries a point `u` of `Y` to a point whose transport to `V` over `w ≫ r₂` is the transport of `u`
over `w ≫ r₁`: it is an isomorphism over `V`. -/
lemma transportPoint_gluingIsoOfFullyFaithful_hom_left_proj {W T T₀ Z U₀ : Scheme.{u}}
    (j : W ⟶ T) (a b : T ⟶ T₀) (g : Z ⟶ T₀) (h : Z ⟶ U₀) (r₁ r₂ : W ⟶ Z)
    (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g) (hr : r₁ ≫ h = r₂ ≫ h)
    (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)
    (hff : (finiteEtaleBaseChange j).FullyFaithful)
    {Z' : Scheme.{u}} (u : Z' ⟶ Y.left) (w : Z' ⟶ W) (hu : u ≫ Y.hom = (w ≫ j) ≫ a)
    (hu₁ : u ≫ Y.hom = (w ≫ r₁) ≫ g)
    (hp : transportPoint ε u (w ≫ r₁) hu₁ ≫ V.hom = (w ≫ r₂) ≫ h)
    (hu₂ : (finiteEtaleBaseChangeLift a Y u (w ≫ j) hu ≫
        (gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff).hom.left ≫
        finiteEtaleBaseChangeProj b Y) ≫ Y.hom = (w ≫ r₂) ≫ g) :
    transportPoint ε (finiteEtaleBaseChangeLift a Y u (w ≫ j) hu ≫
          (gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff).hom.left ≫
          finiteEtaleBaseChangeProj b Y) (w ≫ r₂) hu₂ =
      transportPoint ε u (w ≫ r₁) hu₁ := by
  rw [transportPoint_congr ε
      (gluingIsoOfFullyFaithful_hom_left_proj j a b g h r₁ r₂ ha hb hr Y V ε hff u w hu hu₁ hp)
      rfl hu₂ (transportPointSymm_comp_hom ε _ _ hp),
    transportPoint_transportPointSymm]

/-- The existence form of `AlgebraicGeometry.gluingIsoOfFullyFaithful`. -/
theorem nonempty_iso_finiteEtaleBaseChange_of_fullyFaithful {W T T₀ Z U₀ : Scheme.{u}}
    (j : W ⟶ T) (a b : T ⟶ T₀) (g : Z ⟶ T₀) (h : Z ⟶ U₀)
    (r₁ r₂ : W ⟶ Z) (ha : j ≫ a = r₁ ≫ g) (hb : j ≫ b = r₂ ≫ g) (hr : r₁ ≫ h = r₂ ≫ h)
    (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U₀)
    (ε : (finiteEtaleBaseChange g).obj Y ≅ (finiteEtaleBaseChange h).obj V)
    (hff : Nonempty (finiteEtaleBaseChange j).FullyFaithful) :
    Nonempty ((finiteEtaleBaseChange a).obj Y ≅ (finiteEtaleBaseChange b).obj Y) :=
  ⟨gluingIsoOfFullyFaithful j a b g h r₁ r₂ ha hb hr Y V ε hff.some⟩

/-! #### The two projections restricted to the preimage of the open -/

section Projections

variable {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (U : B.Opens)

/-- The preimage of `U` in `T₀ ×_B T₀` is the preimage, under the first projection, of the
preimage of `U` in `T₀`. -/
lemma preimage_fst_comp_le : (pullback.fst f f ≫ f) ⁻¹ᵁ U ≤ pullback.fst f f ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  le_of_eq rfl

/-- The preimage of `U` in `T₀ ×_B T₀` is also the preimage, under the second projection, of the
preimage of `U` in `T₀`, the two projections agreeing after composition with `f`. -/
lemma preimage_fst_comp_le_snd : (pullback.fst f f ≫ f) ⁻¹ᵁ U ≤ pullback.snd f f ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  le_of_eq (by rw [show pullback.fst f f ≫ f = pullback.snd f f ≫ f from pullback.condition]; rfl)

/-- The first projection of `T₀ ×_B T₀`, restricted to the preimage of `U`. -/
def resFstPreimage : ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  (pullback.fst f f).resLE (f ⁻¹ᵁ U) _ (preimage_fst_comp_le f U)

/-- The second projection of `T₀ ×_B T₀`, restricted to the preimage of `U`. -/
def resSndPreimage : ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  (pullback.snd f f).resLE (f ⁻¹ᵁ U) _ (preimage_fst_comp_le_snd f U)

/-- The restricted first projection is the first projection. -/
lemma resFstPreimage_comp_ι :
    ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι ≫ pullback.fst f f = resFstPreimage f U ≫ (f ⁻¹ᵁ U).ι :=
  (Scheme.Hom.resLE_comp_ι _ (preimage_fst_comp_le f U)).symm

/-- The restricted second projection is the second projection. -/
lemma resSndPreimage_comp_ι :
    ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι ≫ pullback.snd f f = resSndPreimage f U ≫ (f ⁻¹ᵁ U).ι :=
  (Scheme.Hom.resLE_comp_ι _ (preimage_fst_comp_le_snd f U)).symm

/-- The preimage of an open along a composite, as a preimage along the composite. -/
lemma preimage_preimage_of_comp_eq {X Y B : Scheme.{u}} {p : X ⟶ Y} {q : Y ⟶ B} {s : X ⟶ B}
    (hs : p ≫ q = s) (U : B.Opens) : p ⁻¹ᵁ (q ⁻¹ᵁ U) = s ⁻¹ᵁ U := by
  subst hs; rfl

/-- If `ι ≫ c₁ = ρ₁ ≫ m` and `ι ≫ c₂ = ρ₂ ≫ m` with `m` a monomorphism, two morphisms `w`, `w'`
with `w ≫ ι ≫ c₁ = w' ≫ ι ≫ c₂` satisfy `w ≫ ρ₁ = w' ≫ ρ₂`. -/
lemma comp_eq_of_comp_ι_eq {A A' C D : Scheme.{u}} {ι : A ⟶ A'} {m : C ⟶ D} [Mono m]
    {ρ₁ ρ₂ : A ⟶ C} {c₁ c₂ : A' ⟶ D} (h₁ : ι ≫ c₁ = ρ₁ ≫ m) (h₂ : ι ≫ c₂ = ρ₂ ≫ m)
    {Z : Scheme.{u}} (w w' : Z ⟶ A) (hw : w ≫ ι ≫ c₁ = w' ≫ ι ≫ c₂) :
    w ≫ ρ₁ = w' ≫ ρ₂ := by
  rwa [← cancel_mono m, Category.assoc, Category.assoc, ← h₁, ← h₂]

/-- The two restricted projections agree after composition with `f ∣_ U`. -/
lemma resFstPreimage_comp_morphismRestrict :
    resFstPreimage f U ≫ (f ∣_ U) = resSndPreimage f U ≫ (f ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, ← Category.assoc, ← resFstPreimage_comp_ι, ← resSndPreimage_comp_ι,
    Category.assoc, Category.assoc,
    show pullback.fst f f ≫ f = pullback.snd f f ≫ f from pullback.condition]

/-! #### The preimage of `U` as the self-fibre product of the preimage over `U` -/

/-- The comparison morphism `f⁻¹U ×_U f⁻¹U ⟶ T₀ ×_B T₀` induced by the inclusion of `f⁻¹U`. -/
def toPullbackOfMorphismRestrict : pullback (f ∣_ U) (f ∣_ U) ⟶ pullback f f :=
  pullback.lift (pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι)
    (pullback.snd (f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι f U, ← Category.assoc,
        ← Category.assoc, pullback.condition])

/-- The comparison morphism commutes with the first projections. -/
lemma toPullbackOfMorphismRestrict_fst :
    toPullbackOfMorphismRestrict f U ≫ pullback.fst f f =
      pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := pullback.lift_fst _ _ _

/-- The comparison morphism commutes with the second projections. -/
lemma toPullbackOfMorphismRestrict_snd :
    toPullbackOfMorphismRestrict f U ≫ pullback.snd f f =
      pullback.snd (f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := pullback.lift_snd _ _ _

/-- The comparison morphism lies over `U`. -/
lemma toPullbackOfMorphismRestrict_comp :
    toPullbackOfMorphismRestrict f U ≫ (pullback.fst f f ≫ f) =
      (pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ∣_ U)) ≫ U.ι := by
  rw [← Category.assoc, toPullbackOfMorphismRestrict_fst, Category.assoc, Category.assoc,
    morphismRestrict_ι f U]

/-- The self-fibre product of `f⁻¹U` over `U` is isomorphic to the preimage of `U` in `T₀ ×_B T₀`;
the inverse is the pair of restricted projections. -/
def pullbackMorphismRestrictIsoPreimage :
    pullback (f ∣_ U) (f ∣_ U) ≅ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme where
  hom := (isPullback_morphismRestrict (pullback.fst f f ≫ f) U).lift
    (pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ∣_ U)) (toPullbackOfMorphismRestrict f U)
    (toPullbackOfMorphismRestrict_comp f U).symm
  inv := pullback.lift (resFstPreimage f U) (resSndPreimage f U)
    (resFstPreimage_comp_morphismRestrict f U)
  hom_inv_id := by
    have h1 := (isPullback_morphismRestrict (pullback.fst f f ≫ f) U).lift_snd
      (pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ∣_ U)) (toPullbackOfMorphismRestrict f U)
      (toPullbackOfMorphismRestrict_comp f U).symm
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp,
        ← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, ← resFstPreimage_comp_ι f U,
        ← Category.assoc, h1, toPullbackOfMorphismRestrict_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp,
        ← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, ← resSndPreimage_comp_ι f U,
        ← Category.assoc, h1, toPullbackOfMorphismRestrict_snd]
  inv_hom_id := by
    have h1 := (isPullback_morphismRestrict (pullback.fst f f ≫ f) U).lift_snd
      (pullback.fst (f ∣_ U) (f ∣_ U) ≫ (f ∣_ U)) (toPullbackOfMorphismRestrict f U)
      (toPullbackOfMorphismRestrict_comp f U).symm
    rw [← cancel_mono ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι, Category.assoc, h1, Category.id_comp]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, toPullbackOfMorphismRestrict_fst, ← Category.assoc,
        pullback.lift_fst, ← resFstPreimage_comp_ι f U]
    · rw [Category.assoc, toPullbackOfMorphismRestrict_snd, ← Category.assoc,
        pullback.lift_snd, ← resSndPreimage_comp_ι f U]

/-- The identification carries the inclusion of the preimage of `U` to the comparison
morphism. -/
lemma pullbackMorphismRestrictIsoPreimage_hom_comp_ι :
    (pullbackMorphismRestrictIsoPreimage f U).hom ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι =
      toPullbackOfMorphismRestrict f U :=
  (isPullback_morphismRestrict (pullback.fst f f ≫ f) U).lift_snd _ _ _

/-- The identification carries the restricted first projection to the first projection. -/
lemma pullbackMorphismRestrictIsoPreimage_hom_comp_resFst :
    (pullbackMorphismRestrictIsoPreimage f U).hom ≫ resFstPreimage f U =
      pullback.fst (f ∣_ U) (f ∣_ U) := by
  rw [← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, ← resFstPreimage_comp_ι f U, ← Category.assoc,
    pullbackMorphismRestrictIsoPreimage_hom_comp_ι, toPullbackOfMorphismRestrict_fst]

/-- The identification carries the restricted second projection to the second projection. -/
lemma pullbackMorphismRestrictIsoPreimage_hom_comp_resSnd :
    (pullbackMorphismRestrictIsoPreimage f U).hom ≫ resSndPreimage f U =
      pullback.snd (f ∣_ U) (f ∣_ U) := by
  rw [← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, ← resSndPreimage_comp_ι f U, ← Category.assoc,
    pullbackMorphismRestrictIsoPreimage_hom_comp_ι, toPullbackOfMorphismRestrict_snd]

/-- The inverse identification carries the two projections to the two restricted
projections. -/
lemma pullbackMorphismRestrictIsoPreimage_inv :
    (pullbackMorphismRestrictIsoPreimage f U).inv =
      pullback.lift (resFstPreimage f U) (resSndPreimage f U)
        (resFstPreimage_comp_morphismRestrict f U) := rfl

end Projections

/-- Let `f : T₀ ⟶ B` be a morphism, `U` an open of `B`, `Y` a finite étale cover of `T₀` and `V`
one of `U`, with `ε` identifying the restriction of `Y` to `f ⁻¹ᵁ U` with the base change of `V`.
If base change of finite étale covers along the inclusion of the preimage of `U` in `T₀ ×_B T₀` is
fully faithful, this is the isomorphism between the base changes of `Y` along the two projections
of `T₀ ×_B T₀` given by `AlgebraicGeometry.gluingIsoOfFullyFaithful`. -/
def gluingIsoPullbackFstSnd {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (U : B.Opens)
    (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U.toScheme)
    (ε : (finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y ≅ (finiteEtaleBaseChange (f ∣_ U)).obj V)
    (hff : (finiteEtaleBaseChange ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι).FullyFaithful) :
    (finiteEtaleBaseChange (pullback.fst f f)).obj Y ≅
      (finiteEtaleBaseChange (pullback.snd f f)).obj Y :=
  gluingIsoOfFullyFaithful ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι (pullback.fst f f)
    (pullback.snd f f) (f ⁻¹ᵁ U).ι (f ∣_ U) (resFstPreimage f U) (resSndPreimage f U)
    (resFstPreimage_comp_ι f U) (resSndPreimage_comp_ι f U)
    (resFstPreimage_comp_morphismRestrict f U) Y V ε hff

/-- The existence form of `AlgebraicGeometry.gluingIsoPullbackFstSnd`. -/
theorem nonempty_iso_finiteEtaleBaseChange_pullback_fst_snd
    {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (U : B.Opens)
    (Y : FiniteEtaleOver T₀) (V : FiniteEtaleOver U.toScheme)
    (ε : (finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y ≅ (finiteEtaleBaseChange (f ∣_ U)).obj V)
    (hff : Nonempty (finiteEtaleBaseChange
      ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι).FullyFaithful) :
    Nonempty ((finiteEtaleBaseChange (pullback.fst f f)).obj Y ≅
      (finiteEtaleBaseChange (pullback.snd f f)).obj Y) :=
  ⟨gluingIsoPullbackFstSnd f U Y V ε hff.some⟩
/-- The underlying isomorphism of schemes of an isomorphism of finite étale covers. -/
def finiteEtaleOverLeftIso {T : Scheme.{u}} {A A' : FiniteEtaleOver T} (φ : A ≅ A') :
    A.left ≅ A'.left :=
  (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso φ

/-! ### The gluing isomorphism in pullback form -/

namespace DescentDatum

variable {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (Y : FiniteEtaleOver T₀)
  (φ : (finiteEtaleBaseChange (pullback.fst f f)).obj Y ≅
    (finiteEtaleBaseChange (pullback.snd f f)).obj Y)

/-- An isomorphism between the two base changes of `Y` to `T₀ ×_B T₀`, read on the literal fibre
products `Y ×_{T₀} (T₀ ×_B T₀)`. -/
def fstSndLeftIso :
    pullback Y.hom (pullback.fst f f) ≅ pullback Y.hom (pullback.snd f f) :=
  finiteEtaleOverLeftIso φ

/-- The isomorphism `Y ×_B T₀ ≅ T₀ ×_B Y` of fibre products over `B` induced by an isomorphism
between the two base changes of `Y` to `T₀ ×_B T₀`, through the pullback-pasting isomorphisms. -/
def gluingPullbackIsoOfFstSndIso : pullback (Y.hom ≫ f) f ≅ pullback f (Y.hom ≫ f) :=
  (pullbackRightPullbackFstIso f f Y.hom).symm ≪≫ fstSndLeftIso f Y φ ≪≫
    pullbackSymmetry Y.hom (pullback.snd f f) ≪≫ pullbackLeftPullbackSndIso f f Y.hom

/-- The gluing isomorphism in pullback form, written out as a composite. -/
lemma gluingPullbackIsoOfFstSndIso_hom :
    (gluingPullbackIsoOfFstSndIso f Y φ).hom =
      (pullbackRightPullbackFstIso f f Y.hom).inv ≫ (fstSndLeftIso f Y φ).hom ≫
        (pullbackSymmetry Y.hom (pullback.snd f f)).hom ≫
        (pullbackLeftPullbackSndIso f f Y.hom).hom := rfl

/-- The gluing isomorphism in pullback form lies over `T₀ ×_B T₀`: it carries the projection to
`T₀` of the second factor to the projection of the first factor composed with the structure map
of `Y`. -/
lemma gluingPullbackIsoOfFstSndIso_hom_fst :
    (gluingPullbackIsoOfFstSndIso f Y φ).hom ≫ pullback.fst f (Y.hom ≫ f) =
      pullback.fst (Y.hom ≫ f) f ≫ Y.hom := by
  have hw : (fstSndLeftIso f Y φ).hom ≫ pullback.snd Y.hom (pullback.snd f f) =
      pullback.snd Y.hom (pullback.fst f f) := MorphismProperty.Over.w φ.hom
  rw [gluingPullbackIsoOfFstSndIso_hom]
  simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [← Category.assoc (fstSndLeftIso f Y φ).hom, hw,
    pullbackRightPullbackFstIso_inv_snd_fst]

/-- The gluing isomorphism in pullback form lies over `T₀ ×_B T₀`: it carries the projection of
the second factor composed with the structure map of `Y` to the projection to `T₀` of the first
factor. -/
lemma gluingPullbackIsoOfFstSndIso_hom_snd :
    (gluingPullbackIsoOfFstSndIso f Y φ).hom ≫ pullback.snd f (Y.hom ≫ f) ≫ Y.hom =
      pullback.snd (Y.hom ≫ f) f := by
  have hw : (fstSndLeftIso f Y φ).hom ≫ pullback.snd Y.hom (pullback.snd f f) =
      pullback.snd Y.hom (pullback.fst f f) := MorphismProperty.Over.w φ.hom
  rw [gluingPullbackIsoOfFstSndIso_hom]
  simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  rw [show pullback.fst Y.hom (pullback.snd f f) ≫ Y.hom =
      pullback.snd Y.hom (pullback.snd f f) ≫ pullback.snd f f from pullback.condition,
    ← Category.assoc (fstSndLeftIso f Y φ).hom, hw,
    pullbackRightPullbackFstIso_inv_snd_snd]

end DescentDatum

end AlgebraicGeometry

end
