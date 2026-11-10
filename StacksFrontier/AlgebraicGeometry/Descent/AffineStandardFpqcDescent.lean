module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.DescentIso
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent for affine morphisms along a flat surjection of affine schemes

Let `a : X ⟶ S` be a surjective flat morphism of affine schemes, so that `Γ(S) → Γ(X)` is a
faithfully flat ring map, and let `(V, φ)` be a descent datum relative to `a` whose structure
morphism `V ⟶ X` is affine. Then the datum is effective: there is a scheme `U` over `S` with
`(V, φ) ≅ (X ×_S U, can)` as descent data.

## Main results

* `AlgebraicGeometry.comp_isoSpec_hom_SpecMap_congr`: two morphisms out of an affine scheme into
  an affine scheme `V` agree after the morphism `V ⟶ Spec C` attached to a ring map `C ⟶ Γ(V)`
  as soon as the two composite ring maps agree.
* `AlgebraicGeometry.DescentData.comp_gluingPullbackIso_inv_fst`: the inverse gluing action
  evaluated at a generalised point of `X ×_S V`.
* `AlgebraicGeometry.DescentData.actInv_eq_act`: the inverse gluing action *is* the gluing
  action, with its two arguments exchanged.
* `AlgebraicGeometry.DescentData.isoOfIsPullback_of_actInvariant`: two descent data relative to
  one morphism are isomorphic as soon as the underlying scheme of the first is the fibre product
  presented by the second and the comparison morphism is invariant for the gluing action.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_surjective_of_flat`: **effective
  descent for affine morphisms along a flat surjection of affine schemes.** A descent datum
  relative to a surjective flat morphism of affine schemes whose structure morphism is affine is
  effective.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two morphisms out of an affine scheme `T` into an affine scheme `V`, followed by the morphism
`V ⟶ Spec C` attached to a ring map `p : C ⟶ Γ(V)`, agree as soon as the two composite ring maps
`C ⟶ Γ(V) ⟶ Γ(T)` agree. -/
theorem comp_isoSpec_hom_SpecMap_congr {T V : Scheme.{u}} [IsAffine T] [IsAffine V]
    {C : CommRingCat.{u}} (p : C ⟶ Γ(V, ⊤)) {h₁ h₂ : T ⟶ V}
    (h : p ≫ h₁.appTop = p ≫ h₂.appTop) :
    h₁ ≫ V.isoSpec.hom ≫ Spec.map p = h₂ ≫ V.isoSpec.hom ≫ Spec.map p := by
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, ← Category.assoc,
    ← Scheme.isoSpec_hom_naturality, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, h]

namespace DescentData

variable {S X : Scheme.{u}} {a : X ⟶ S} (D : DescentData (fun _ : Unit ↦ a))

/-- The inverse gluing action of a descent datum relative to a single morphism, evaluated at a
generalised point of `X ×_S V` given by its two components. -/
theorem comp_gluingPullbackIso_inv_fst {T : Scheme.{u}}
    (t : T ⟶ pullback a ((D.obj ()).hom ≫ a)) :
    t ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a =
      D.actInv (t ≫ pullback.fst a ((D.obj ()).hom ≫ a))
        (t ≫ pullback.snd a ((D.obj ()).hom ≫ a))
        (by simp only [Category.assoc]; rw [pullback.condition]) := by
  rw [actInv]
  congr 1
  apply pullback.hom_ext <;> simp

/-- **The inverse gluing action is the gluing action.** For a descent datum relative to a single
morphism, the point that `φ⁻¹` attaches to `(x, v)` is the translate `act v x` of `v` to the
fibre over `x`. -/
theorem actInv_eq_act {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ (D.obj ()).left)
    (h : x ≫ a = v ≫ (D.obj ()).hom ≫ a) :
    D.actInv x v h = D.act v x h.symm := by
  have hw : D.actInv x v h ≫ (D.obj ()).hom = x := D.actInv_hom x v h
  have hstr : D.actInv x v h ≫ (D.obj ()).hom ≫ a = (v ≫ (D.obj ()).hom) ≫ a :=
    D.actInv_structure x v h
  have hinv : D.act (D.actInv x v h) (v ≫ (D.obj ()).hom) hstr = v := D.act_actInv x v h
  have hxy : (v ≫ (D.obj ()).hom) ≫ a = x ≫ a := (Category.assoc _ _ _).trans h.symm
  have hcc := D.act_act (D.actInv x v h) (v ≫ (D.obj ()).hom) x hstr hxy
  have hL : D.act (D.act (D.actInv x v h) (v ≫ (D.obj ()).hom) hstr) x
      (D.act_structure (D.actInv x v h) (v ≫ (D.obj ()).hom) x hstr hxy) =
      D.act v x h.symm := D.act_congr hinv rfl
  have hR : D.act (D.actInv x v h) x (hstr.trans hxy) = D.actInv x v h :=
    (D.act_congr rfl hw.symm).trans (D.act_self (D.actInv x v h))
  exact hR.symm.trans (hcc.symm.trans hL)

/-- **The cocycle identity for the inverse gluing action.** Let `ω₁, ω₂` present an object over
`X ×_S (X ×_S V)`, let `l` be the morphism to `X ×_S V` with components `ω₁` and the action of
`ω₂`, and let `l'` be the one with components `ω₁` and the projection of `ω₂`. Then `l` and `l'`
have the same action. -/
theorem actInv_cocycle {W : Scheme.{u}} (ω₁ : W ⟶ X)
    (ω₂ : W ⟶ pullback a ((D.obj ()).hom ≫ a))
    (hω : ω₁ ≫ a = ω₂ ≫ pullback.fst a ((D.obj ()).hom ≫ a) ≫ a)
    (l l' : W ⟶ pullback a ((D.obj ()).hom ≫ a))
    (hl₁ : l ≫ pullback.fst a ((D.obj ()).hom ≫ a) = ω₁)
    (hl₂ : l ≫ pullback.snd a ((D.obj ()).hom ≫ a) =
      ω₂ ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a)
    (hl₁' : l' ≫ pullback.fst a ((D.obj ()).hom ≫ a) = ω₁)
    (hl₂' : l' ≫ pullback.snd a ((D.obj ()).hom ≫ a) =
      ω₂ ≫ pullback.snd a ((D.obj ()).hom ≫ a)) :
    l ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a =
      l' ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a := by
  have key : ∀ t : W ⟶ pullback a ((D.obj ()).hom ≫ a),
      t ≫ (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a =
        D.act (t ≫ pullback.snd a ((D.obj ()).hom ≫ a)) (t ≫ pullback.fst a ((D.obj ()).hom ≫ a))
          (by simp only [Category.assoc, pullback.condition]) := fun t ↦ by
    rw [D.comp_gluingPullbackIso_inv_fst t, D.actInv_eq_act]
  have hxz : (ω₂ ≫ pullback.fst a ((D.obj ()).hom ≫ a)) ≫ a = ω₁ ≫ a := by
    simpa only [Category.assoc] using hω.symm
  have hmid : (ω₂ ≫ (D.gluingPullbackIso () ()).inv ≫
      pullback.fst ((D.obj ()).hom ≫ a) a) ≫ (D.obj ()).hom ≫ a = ω₁ ≫ a := by
    rw [key]
    exact D.act_structure _ _ _ _ hxz
  rw [key l, key l']
  exact (D.act_congr (h' := hmid) hl₂ hl₁).trans
    ((D.act_act_of (hwy := hmid) (key ω₂) rfl hxz).trans (D.act_congr hl₂'.symm hl₁'.symm))

/-- **Recognising a descent datum as a given one.** Let `D` and `E` be descent data relative to
`a : X ⟶ S`, let `u : Uo ⟶ S`, and suppose the underlying scheme of `E` is identified with the
fibre product `Uo ×_S X` by `ι`, compatibly with the structure morphism, in such a way that the
gluing action of `E` does not move the coordinate in `Uo`. If the underlying scheme of `D` is
also a fibre product of `u` and `a`, by a morphism `toU` invariant for the gluing action of `D`,
then `D` and `E` are isomorphic as descent data. -/
def isoOfIsPullback_of_actInvariant {E : DescentData (fun _ : Unit ↦ a)}
    {Uo : Scheme.{u}} {u : Uo ⟶ S} (ι : (E.obj ()).left ≅ pullback u a)
    (hιsnd : ι.hom ≫ pullback.snd u a = (E.obj ()).hom)
    (hEact : E.actOn ≫ ι.hom ≫ pullback.fst u a =
      pullback.fst ((E.obj ()).hom ≫ a) a ≫ ι.hom ≫ pullback.fst u a)
    {toU : (D.obj ()).left ⟶ Uo} (hpb : IsPullback toU (D.obj ()).hom u a)
    (hinv : D.actOn ≫ toU = pullback.fst ((D.obj ()).hom ≫ a) a ≫ toU) :
    D ≅ E := by
  have hmk : (hpb.isoPullback ≪≫ ι.symm).hom ≫ (E.obj ()).hom = (D.obj ()).hom := by
    rw [Iso.trans_hom, Iso.symm_hom, ← hιsnd, Category.assoc, Iso.inv_hom_id_assoc,
      hpb.isoPullback_hom_snd]
  have hleft : (Over.isoMk (hpb.isoPullback ≪≫ ι.symm) hmk).hom.left =
      (hpb.isoPullback ≪≫ ι.symm).hom := rfl
  have hel : ∀ {Z : Scheme.{u}} (g : pullback u a ⟶ Z),
      (Over.isoMk (hpb.isoPullback ≪≫ ι.symm) hmk).hom.left ≫ ι.hom ≫ g =
        hpb.isoPullback.hom ≫ g := by
    intro Z g
    rw [hleft, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  refine isoOfActOn (D := D) (E := E) (Over.isoMk (hpb.isoPullback ≪≫ ι.symm) hmk) ?_
  rw [← cancel_mono ι.hom]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rwa [hel (pullback.fst u a), hpb.isoPullback_hom_fst, hEact,
      actOnMap_fst_assoc, hel (pullback.fst u a), hpb.isoPullback_hom_fst]
  · simp only [Category.assoc]
    rw [hel (pullback.snd u a), hpb.isoPullback_hom_snd, actOn_hom, hιsnd, actOn_hom,
      actOnMap_snd]

end DescentData

namespace DescentDatum

open DescentData

variable {S X : Scheme.{u}} [IsAffine S] [IsAffine X] {a : X ⟶ S}

/-- Effectivity of a descent datum of affine schemes from the descended ring: given a ring `C`
under `Γ(S)` and over `Γ(V)` which presents `Γ(V)` as the pushout, and whose image in `Γ(V)` is
invariant for the gluing action, the datum is effective. -/
private theorem isEffective_of_isPushout (D : DescentDatum a) [IsAffine (D.obj ()).left]
    [IsAffine (pullback ((D.obj ()).hom ≫ a) a)] {C : CommRingCat.{u}} (k : Γ(S, ⊤) ⟶ C)
    (p : C ⟶ Γ((D.obj ()).left, ⊤))
    (hinv : p ≫ D.actOn.appTop = p ≫ (pullback.fst ((D.obj ()).hom ≫ a) a).appTop)
    (po : IsPushout a.appTop k (D.obj ()).hom.appTop p) :
    DescentData.IsEffective D := by
  set U : Over S := Over.mk (Spec.map k ≫ S.isoSpec.inv) with hU
  set P := DescentData.pullbackFunctor (𝟙 S) a (𝟙 S) a (by simp) with hP
  set T := (DescentData.trivialFunctor S).obj U with hT
  have hUhom : U.hom = Spec.map k ≫ S.isoSpec.inv := rfl
  have hpb : IsPullback (((D.obj ()).left).isoSpec.hom ≫ Spec.map p) (D.obj ()).hom U.hom a := by
    refine (isPullback_SpecMap_of_isPushout a.appTop k (D.obj ()).hom.appTop p po).flip.of_iso'
      ((D.obj ()).left).isoSpec (Iso.refl (Spec C)) X.isoSpec S.isoSpec ?_
      (Scheme.isoSpec_hom_naturality (D.obj ()).hom) ?_
      (Scheme.isoSpec_hom_naturality a)
    · rw [Iso.refl_hom, Category.comp_id]
    · rw [Iso.refl_hom, Category.id_comp, hUhom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
  have : IsIso (P.objIso T).hom.left :=
    inferInstanceAs (IsIso ((Over.forget X).map (P.objIso T).hom))
  have hιsnd : (asIso (P.objIso T).hom.left).hom ≫ pullback.snd U.hom a =
      ((P.functor.obj T).obj ()).hom := P.objIso_hom_left_snd T
  have hEact : (P.functor.obj T).actOn ≫
      (asIso (P.objIso T).hom.left).hom ≫ pullback.fst U.hom a =
      pullback.fst (((P.functor.obj T).obj ()).hom ≫ a) a ≫
        (asIso (P.objIso T).hom.left).hom ≫ pullback.fst U.hom a := by
    simpa only [DescentData.actOn, asIso_hom, Category.assoc] using
      DescentData.canonical_gluingPullbackIso_hom_snd_fst a P U
  exact ⟨U, ⟨(D.isoOfIsPullback_of_actInvariant (asIso (P.objIso T).hom.left) hιsnd hEact hpb
    (comp_isoSpec_hom_SpecMap_congr p hinv)).symm⟩⟩

/-- **Effective descent for affine morphisms along a flat surjection of affine schemes.** Let
`a : X ⟶ S` be a surjective flat morphism of affine schemes and let `D` be a descent datum
relative to `a` whose structure morphism `V ⟶ X` is affine. Then `D` is effective: there is a
scheme `U` over `S` whose canonical descent datum relative to `a` is isomorphic to `D`. -/
@[sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "special case"]
theorem isEffective_of_isAffineHom_of_surjective_of_flat (hsurj : Surjective a) (hflat : Flat a)
    (D : DescentDatum a) (haff : IsAffineHom (D.obj ()).hom) :
    DescentData.IsEffective D := by
  have := haff
  have : IsAffine (D.obj ()).left := isAffine_of_isAffineHom (f := (D.obj ()).hom)
  have sq₁ : IsPullback (pullback.fst ((D.obj ()).hom ≫ a) a)
      (pullback.snd ((D.obj ()).hom ≫ a) a) ((D.obj ()).hom ≫ a) a :=
    IsPullback.of_hasPullback _ _
  have sq₂ : IsPullback (pullback.fst a ((D.obj ()).hom ≫ a))
      (pullback.snd a ((D.obj ()).hom ≫ a)) a ((D.obj ()).hom ≫ a) :=
    IsPullback.of_hasPullback _ _
  have sq₃ : IsPullback (pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a))
      (pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a)) a
      (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) :=
    IsPullback.of_hasPullback _ _
  have : IsAffine (pullback ((D.obj ()).hom ≫ a) a) := IsAffine.of_isPullback sq₁
  have hs₁ : ((D.gluingPullbackIso () ()).inv ≫
      pullback.fst ((D.obj ()).hom ≫ a) a) ≫ (D.obj ()).hom =
      pullback.fst a ((D.obj ()).hom ≫ a) :=
    (Category.assoc _ _ _).trans D.gluingPullbackIso_inv_fst
  have hcond : pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫ a =
      pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫
        pullback.fst a ((D.obj ()).hom ≫ a) ≫ a := pullback.condition
  have hlw : pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫ a =
      (pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫
        (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a) ≫
          (D.obj ()).hom ≫ a := by
    simpa only [Category.assoc, D.gluingPullbackIso_inv_fst_assoc] using hcond
  have hlw' : pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫ a =
      (pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫
        pullback.snd a ((D.obj ()).hom ≫ a)) ≫ (D.obj ()).hom ≫ a := by
    rwa [Category.assoc, ← pullback.condition]
  have hcoc : (pullback.lift (f := a) (g := (D.obj ()).hom ≫ a)
        (pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a))
        (pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫
          (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a) hlw) ≫
      ((D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a) =
      (pullback.lift (f := a) (g := (D.obj ()).hom ≫ a)
        (pullback.fst a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a))
        (pullback.snd a (pullback.fst a ((D.obj ()).hom ≫ a) ≫ a) ≫
          pullback.snd a ((D.obj ()).hom ≫ a)) hlw') ≫
      ((D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a) :=
    D.actInv_cocycle _ _ hcond _ _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨C, k, p, -, hinvar, po⟩ :=
    exists_descentPushout_of_isPullback hsurj hflat sq₁ sq₂ sq₃
      (s := (D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a)
      (φ := D.gluingPullbackIso () ()) hs₁ rfl D.gluingPullbackIso_inv_snd
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hcoc
  have h₁ : (pullback.fst ((D.obj ()).hom ≫ a) a).appTop =
      ((D.gluingPullbackIso () ()).inv ≫ pullback.fst ((D.obj ()).hom ≫ a) a).appTop ≫
        (D.gluingPullbackIso () ()).hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id_assoc]
  have h₂ : D.actOn.appTop = (pullback.snd a ((D.obj ()).hom ≫ a)).appTop ≫
      (D.gluingPullbackIso () ()).hom.appTop := by
    rw [← Scheme.Hom.comp_appTop]
    rfl
  refine isEffective_of_isPushout D k p ?_ po
  rw [h₁, h₂]
  simp only [← Category.assoc]
  rw [hinvar]

end DescentDatum

end AlgebraicGeometry

end

end
