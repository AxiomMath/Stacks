module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineStagesPerfectHomDescent

/-!
# Descending isomorphisms of perfect objects in Situation 09RH

When morphisms between pullbacks of perfect objects descend in the sense of
`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`, an isomorphism between the
pullbacks to the limit of two perfect objects at a stage `i` is the pullback of an isomorphism at
some finite stage `k ≥ i`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq`: the isomorphism
  `Lf^* ∘ Lg^* ≅ Lp^*` for `f ≫ g = p`.
* `AlgebraicGeometry.Space.DescentSituation.raiseStageHom`: a morphism at the stage `k` raised to
  a stage `m ≥ k`.
* `AlgebraicGeometry.Space.DescentSituation.limitStageHom`: a morphism at the stage `k` read at the
  limit.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle`: the cocycle
  identity for `Lf^* ∘ Lg^* ≅ Lp^*`.

* `AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend.exists_iso`: an isomorphism
  `Lfᵢ^*Eᵢ ≅ Lfᵢ^*Kᵢ` of the pullbacks of perfect objects is the pullback of an isomorphism
  `Lf_{ki}^*Eᵢ ≅ Lf_{ki}^*Kᵢ` at some stage `k ≥ i`.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

section Generic

variable {C D : Type*} [Category* C] [Category* D]

private theorem conj_comp (F : C ⥤ D) {X Y Z : C} {a b c : D} (e₁ : F.obj X ≅ a)
    (e₂ : F.obj Y ≅ b) (e₃ : F.obj Z ≅ c) (x : X ⟶ Y) (y : Y ⟶ Z) :
    e₁.inv ≫ F.map (x ≫ y) ≫ e₃.hom =
      (e₁.inv ≫ F.map x ≫ e₂.hom) ≫ (e₂.inv ≫ F.map y ≫ e₃.hom) := by
  simp

private theorem conj_id (F : C ⥤ D) {X : C} {a : D} (e : F.obj X ≅ a) :
    e.inv ≫ F.map (𝟙 X) ≫ e.hom = 𝟙 a := by
  simp

private theorem map_eq_of_conj_eq (F : C ⥤ D) {X Y : C} {a b : D} (e₁ : F.obj X ≅ a)
    (e₂ : F.obj Y ≅ b) {x y : X ⟶ Y}
    (h : e₁.inv ≫ F.map x ≫ e₂.hom = e₁.inv ≫ F.map y ≫ e₂.hom) : F.map x = F.map y := by
  simpa using h

/-- **Conjugation is compatible with raising.** If `Fm.map tX.hom ≫ sX.hom = rX.hom ≫ qX.hom`
for `X = E, K` and `r` is natural at `x`, then `Fm.map (tE.inv ≫ T.map x ≫ tK.hom)` conjugated
by `s` is `Fk.map x` conjugated by `q`. This is the computation behind raising a morphism of the
stages of Situation 09RH twice, or to a stage and then to the limit. -/
theorem conj_raise {C' : Type*} [Category* C'] (Fm : C ⥤ D) (Fk : C' ⥤ D) (T : C' ⥤ C)
    {XE XK : C'} {YE YK : C} {aE aK : D} (tE : T.obj XE ≅ YE) (tK : T.obj XK ≅ YK)
    (sE : Fm.obj YE ≅ aE) (sK : Fm.obj YK ≅ aK) (rE : Fm.obj (T.obj XE) ≅ Fk.obj XE)
    (rK : Fm.obj (T.obj XK) ≅ Fk.obj XK) (qE : Fk.obj XE ≅ aE) (qK : Fk.obj XK ≅ aK)
    (hE : Fm.map tE.hom ≫ sE.hom = rE.hom ≫ qE.hom) (hK : Fm.map tK.hom ≫ sK.hom = rK.hom ≫ qK.hom)
    (x : XE ⟶ XK) (hn : Fm.map (T.map x) ≫ rK.hom = rE.hom ≫ Fk.map x) :
    sE.inv ≫ Fm.map (tE.inv ≫ T.map x ≫ tK.hom) ≫ sK.hom = qE.inv ≫ Fk.map x ≫ qK.hom := by
  have hE' : sE.inv ≫ Fm.map tE.inv = qE.inv ≫ rE.inv := by
    simpa using congrArg Iso.inv (Iso.ext (α := Fm.mapIso tE ≪≫ sE) (β := rE ≪≫ qE)
      (by simpa using hE))
  simp only [Functor.map_comp, Category.assoc]
  rw [hK, reassoc_of% hn, reassoc_of% hE', Iso.inv_hom_id_assoc]

end Generic

section CompOfEq

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z W : AlgebraicSpaces B S hS}

/-- The isomorphism `Lf^* Lg^* E ≅ Lp^* E` for `f ≫ g = p`, on the models of the spaces-étale
sites: `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso` followed by the
identification of `L(f ≫ g)^*` with `Lp^*`. -/
def spacesEtaleModelDerivedPullbackCompIsoOfEq (f : X ⟶ Y) (g : Y ⟶ Z) {p : X ⟶ Z}
    (hp : f ≫ g = p)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Z).O))) :
    (derivedPullback (spacesEtaleModelHom B S hS f)).obj
        ((derivedPullback (spacesEtaleModelHom B S hS g)).obj E) ≅
      (derivedPullback (spacesEtaleModelHom B S hS p)).obj E :=
  (spacesEtaleModelDerivedPullbackCompIso B S hS f g).app E ≪≫
    eqToIso (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj E) hp)

/-- `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq` is natural. -/
theorem spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {p : X ⟶ Z} (hp : f ≫ g = p)
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Z).O))} (e : E ⟶ E') :
    (derivedPullback (spacesEtaleModelHom B S hS f)).map
        ((derivedPullback (spacesEtaleModelHom B S hS g)).map e) ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f g hp E').hom =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f g hp E).hom ≫
        (derivedPullback (spacesEtaleModelHom B S hS p)).map e := by
  subst hp
  simp only [spacesEtaleModelDerivedPullbackCompIsoOfEq, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.naturality e

/-- The cocycle identity for
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq`: for `f ≫ g = p`,
`g ≫ h = q` and `p ≫ h = f ≫ q = r`, the two identifications of `Lf^* Lg^* Lh^*` with `Lr^*`
agree. -/
theorem spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    {p : X ⟶ Z} {q : Y ⟶ W} {r : X ⟶ W} (hp : f ≫ g = p) (hq : g ≫ h = q) (hr : p ≫ h = r)
    (hr' : f ≫ q = r)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O))) :
    (derivedPullback (spacesEtaleModelHom B S hS f)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS g h hq E).hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f q hr' E).hom =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f g hp
          ((derivedPullback (spacesEtaleModelHom B S hS h)).obj E)).hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS p h hr E).hom := by
  subst hp hq hr
  have h₁ := congrArg (fun α => α.app E)
    (spacesEtaleModelDerivedPullbackCompIso_assoc B S hS f g h)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h₁
  simp only [spacesEtaleModelDerivedPullbackCompIsoOfEq, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact h₁.symm

end CompOfEq

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The identification `Lf_{mk}^* ∘ Lf_{ki}^* ≅ Lf_{mi}^*` of the derived pullbacks along the
transition morphisms, for `i ≤ k ≤ m`. -/
def stageTransitionDerivedPullbackIso {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))) :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hkm).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj
        ((derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E) ≅
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE (hik.trans hkm)).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E :=
  spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS _ _
    (ObjectProperty.hom_ext _ (by
      change D.system.map (homOfLE hkm).op ≫ D.system.map (homOfLE hik).op = _
      rw [← D.system.map_comp]
      rfl)) E

/-- The comparisons with the limit are compatible with the transitions:
`Lf_m^*(Lf_{mk}^* Lf_{ki}^* E ≅ Lf_{mi}^* E)` followed by `Lf_m^* Lf_{mi}^* ≅ Lfᵢ^*` is
`Lf_m^* Lf_{mk}^* ≅ Lf_k^*` followed by `Lf_k^* Lf_{ki}^* ≅ Lfᵢ^*`. -/
theorem stageProjectionDerivedPullbackIso_cocycle {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))) :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op m)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op m), D.algebraicSpace m⟩ : AlgebraicSpaces B S hS)))).map
        (D.stageTransitionDerivedPullbackIso hik hkm E).hom ≫
        (D.stageProjectionDerivedPullbackIso (hik.trans hkm) E).hom =
        (D.stageProjectionDerivedPullbackIso hkm ((derivedPullback
        (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E)).hom ≫
        (D.stageProjectionDerivedPullbackIso hik E).hom := by
  refine spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS _ _ _ ?_ ?_ ?_ ?_ E
  all_goals exact ObjectProperty.hom_ext _ (D.limitCone.w _)

/-- A morphism `Lf_{ki}^*E ⟶ Lf_{ki}^*K` at the stage `k`, raised to the stage `m ≥ k` and read
as a morphism `Lf_{mi}^*E ⟶ Lf_{mi}^*K`. -/
def raiseStageHom {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K) :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE (hik.trans hkm)).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE (hik.trans hkm)).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K :=
  (D.stageTransitionDerivedPullbackIso hik hkm E).inv ≫ (derivedPullback (spacesEtaleModelHom B S hS
      (ObjectProperty.homMk (D.system.map (homOfLE hkm).op) : (⟨D.system.obj (op _),
          D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op
              _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).map x ≫
    (D.stageTransitionDerivedPullbackIso hik hkm K).hom

/-- `AlgebraicGeometry.Space.DescentSituation.raiseStageHom` preserves composition. -/
theorem raiseStageHom_comp {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    {E K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K)
        (y : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj L) :
    D.raiseStageHom hik hkm (x ≫ y) = D.raiseStageHom hik hkm x ≫ D.raiseStageHom hik hkm y :=
  conj_comp _ _ _ _ x y

/-- `AlgebraicGeometry.Space.DescentSituation.raiseStageHom` preserves identities. -/
theorem raiseStageHom_id {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))) :
    D.raiseStageHom hik hkm (𝟙 ((derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk
        (D.system.map (homOfLE hik).op) : (⟨D.system.obj (op _), D.algebraicSpace _⟩ :
            AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op _), D.algebraicSpace
                _⟩ : AlgebraicSpaces B S hS)))).obj E)) = 𝟙 _ :=
  conj_id _ _

/-- A morphism `Lf_{ki}^*E ⟶ Lf_{ki}^*K` at the stage `k`, read at the limit as a morphism
`Lfᵢ^*E ⟶ Lfᵢ^*K` through the comparisons
`AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso`. -/
def limitStageHom {i k : I} (hik : i ≤ k)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K) :
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS)))).obj K :=
  (D.stageProjectionDerivedPullbackIso hik E).inv ≫ (derivedPullback (spacesEtaleModelHom B S hS
      (ObjectProperty.homMk (D.limitCone.π.app (op k)) : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op k), D.algebraicSpace
              k⟩ : AlgebraicSpaces B S hS)))).map x ≫
    (D.stageProjectionDerivedPullbackIso hik K).hom

/-- `AlgebraicGeometry.Space.DescentSituation.limitStageHom` preserves composition. -/
theorem limitStageHom_comp {i k : I} (hik : i ≤ k)
    {E K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K)
        (y : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj L) :
    D.limitStageHom hik (x ≫ y) = D.limitStageHom hik x ≫ D.limitStageHom hik y :=
  conj_comp _ _ _ _ x y

/-- `AlgebraicGeometry.Space.DescentSituation.limitStageHom` preserves identities. -/
theorem limitStageHom_id {i k : I} (hik : i ≤ k)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))) :
    D.limitStageHom hik (𝟙 ((derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk
        (D.system.map (homOfLE hik).op) : (⟨D.system.obj (op _), D.algebraicSpace _⟩ :
            AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op _), D.algebraicSpace
                _⟩ : AlgebraicSpaces B S hS)))).obj E)) = 𝟙 _ :=
  conj_id _ _

/-- Raising a morphism to a later stage does not change it at the limit. -/
theorem limitStageHom_raiseStageHom {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K) :
    D.limitStageHom (hik.trans hkm) (D.raiseStageHom hik hkm x) = D.limitStageHom hik x :=
  conj_raise _ _ _ _ _ _ _ _ _ _ _ (D.stageProjectionDerivedPullbackIso_cocycle hik hkm E)
    (D.stageProjectionDerivedPullbackIso_cocycle hik hkm K) x
    (D.stageProjectionDerivedPullbackIso_hom_naturality hkm x)

/-- The limit reading of a morphism at a stage determines its image under the pullback to the
limit. -/
theorem map_eq_of_limitStageHom_eq {i k : I} (hik : i ≤ k)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    {x y : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K}
    (hxy : D.limitStageHom hik x = D.limitStageHom hik y) :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op k)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS)))).map x =
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op k)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS)))).map y :=
  map_eq_of_conj_eq _ _ _ hxy

/-- Two morphisms at a stage `k ≥ i` between pullbacks of perfect objects with the same limit
reading agree after raising to some later stage. -/
theorem PerfectHomsDescend.exists_raiseStageHom_eq (hFF : D.PerfectHomsDescend) {i k : I}
    (hi : D.base ≤ i) (hik : i ≤ k)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (hE : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect E)
    (hK : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect K)
    {x y : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K}
    (hxy : D.limitStageHom hik x = D.limitStageHom hik y) :
    ∃ (m : I) (hkm : k ≤ m), D.raiseStageHom hik hkm x = D.raiseStageHom hik hkm y := by
  obtain ⟨m, hkm, hm⟩ := (hFF k (hi.trans hik) _ _
    (isPerfect_derivedPullback_spacesEtaleModelHom _ E hE)
    (isPerfect_derivedPullback_spacesEtaleModelHom _ K hK)).2 x y
    (D.map_eq_of_limitStageHom_eq hik hxy)
  exact ⟨m, hkm, by simp only [raiseStageHom, hm]⟩

/-- Two morphisms `a : Lf_{ki}^*E ⟶ Lf_{ki}^*K`, `b : Lf_{ki}^*K ⟶ Lf_{ki}^*E` of pullbacks of
perfect objects that are inverse at the limit are inverse after raising to some later stage. -/
private theorem PerfectHomsDescend.exists_raiseStageHom_comp_eq_id (hFF : D.PerfectHomsDescend)
    {i k : I} (hi : D.base ≤ i) (hik : i ≤ k)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (hE : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect E)
    (a : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K)
    (b : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E)
    (h : D.limitStageHom hik a ≫ D.limitStageHom hik b = 𝟙 _) :
    ∃ (m : I) (hkm : k ≤ m), D.raiseStageHom hik hkm a ≫ D.raiseStageHom hik hkm b = 𝟙 _ := by
  obtain ⟨m, hkm, hm⟩ := hFF.exists_raiseStageHom_eq D hi hik hE hE
    (x := a ≫ b) (y := 𝟙 _) (by rw [D.limitStageHom_comp, h, D.limitStageHom_id])
  exact ⟨m, hkm, by rw [← D.raiseStageHom_comp, hm, D.raiseStageHom_id]⟩

/-- If morphisms of perfect objects descend in the situation, then every isomorphism
`Lfᵢ^*E ≅ Lfᵢ^*K` of the pullbacks of perfect objects `E`, `K` at a stage `i ≥ 0` is, through the
comparisons `AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso`, the
pullback of an isomorphism `Lf_{ki}^*E ≅ Lf_{ki}^*K` at some stage `k ≥ i`. -/
theorem PerfectHomsDescend.exists_iso (hFF : D.PerfectHomsDescend) {i : I} (hi : D.base ≤ i)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (hE : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect E)
    (hK : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect K)
    (φ : (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS)))).obj E ≅
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS)))).obj K) :
    ∃ (k : I) (hik : i ≤ k) (ψ : (derivedPullback
        (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj E ≅
        (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op _), D.algebraicSpace _⟩ : AlgebraicSpaces B S hS)))).obj K),
        D.limitStageHom hik ψ.hom = φ.hom := by
  obtain ⟨j₁, h₁, ψ₁, hψ₁⟩ := (hFF i hi E K hE hK).1 φ.hom
  obtain ⟨j₂, h₂, ψ₂, hψ₂⟩ := (hFF i hi K E hK hE).1 φ.inv
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j₁ j₂
  have hik : i ≤ k := h₁.trans hk₁
  let a := D.raiseStageHom h₁ hk₁ ψ₁
  let b := D.raiseStageHom h₂ hk₂ ψ₂
  have ha : D.limitStageHom hik a = φ.hom :=
    (D.limitStageHom_raiseStageHom h₁ hk₁ ψ₁).trans hψ₁.symm
  have hb : D.limitStageHom hik b = φ.inv :=
    (D.limitStageHom_raiseStageHom h₂ hk₂ ψ₂).trans hψ₂.symm
  obtain ⟨m, hkm, hm⟩ := hFF.exists_raiseStageHom_comp_eq_id D hi hik hE a b
    ((congrArg₂ (· ≫ ·) ha hb).trans φ.hom_inv_id)
  obtain ⟨n, hmn, hn⟩ := hFF.exists_raiseStageHom_comp_eq_id D hi (hik.trans hkm) hK
    (D.raiseStageHom hik hkm b) (D.raiseStageHom hik hkm a)
    ((congrArg₂ (· ≫ ·) ((D.limitStageHom_raiseStageHom hik hkm b).trans hb)
      ((D.limitStageHom_raiseStageHom hik hkm a).trans ha)).trans φ.inv_hom_id)
  refine ⟨n, (hik.trans hkm).trans hmn,
    ⟨D.raiseStageHom (hik.trans hkm) hmn (D.raiseStageHom hik hkm a),
      D.raiseStageHom (hik.trans hkm) hmn (D.raiseStageHom hik hkm b), ?_, hn⟩, ?_⟩
  · rw [← D.raiseStageHom_comp, hm, D.raiseStageHom_id]
  · exact (D.limitStageHom_raiseStageHom _ hmn _).trans
      ((D.limitStageHom_raiseStageHom hik hkm a).trans ha)

end DescentSituation

end AlgebraicGeometry.Space

end
