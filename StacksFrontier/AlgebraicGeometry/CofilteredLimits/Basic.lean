module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Existence of cofiltered limits of schemes with affine transition morphisms

A cofiltered diagram of schemes whose transition morphisms are affine has a limit in the
category of schemes. Over each affine open `U` of a base scheme `S`, the limit of the affine
schemes `F k ×_S U` exists, and these local limits glue to a limit of `F`.

## Main results

* `AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom`: a cofiltered diagram of schemes
  with affine transition morphisms has a limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace CofilteredLimit

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- Limits of diagrams of affine schemes exist: the limit is the spectrum of the colimit of the
coordinate rings. -/
lemma hasLimit_of_isAffine {J : Type u} [Category.{u} J] (G : J ⥤ Scheme.{u})
    [∀ j, IsAffine (G.obj j)] : HasLimit G := by
  let e : G ⟶ (G ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := G.whiskerLeft ΓSpec.adjunction.unit
  have (j : J) : IsIso (e.app j) := IsAffine.affine
  have : IsIso e := NatIso.isIso_of_isIso_app e
  exact ⟨_, (IsLimit.postcomposeInvEquiv (asIso e) _).symm
    (isLimitOfPreserves Scheme.Spec (limit.isLimit (G ⋙ Scheme.Γ.rightOp)))⟩

/-- A function on a cofiltered category that is preserved by every morphism is constant. -/
private theorem eq_of_forall_map {J : Type u} [Category.{u} J] [IsCofiltered J] {α : Type*}
    (φ : J → α) (h : ∀ {i j : J}, (i ⟶ j) → φ i = φ j) (i j : J) : φ i = φ j :=
  have := IsCofilteredOrEmpty.isPreconnected J
  constant_of_preserves_morphisms φ (fun _ _ f ↦ h f) i j

variable {K : Type u} [Category.{u} K] {S : Scheme.{u}} {F : K ⥤ Scheme.{u}}
  (p : ∀ k, F.obj k ⟶ S) (hp : ∀ {k l : K} (f : k ⟶ l), F.map f ≫ p l = p k)

section

include hp

/-- The transition morphism `F k ×_S U ⟶ F l ×_S U` induced by `f : k ⟶ l`. -/
noncomputable def pbMap (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    pullback (p k) U.1.ι ⟶ pullback (p l) U.1.ι :=
  pullback.lift (pullback.fst _ _ ≫ F.map f) (pullback.snd _ _) (by
    rw [Category.assoc, hp f, pullback.condition])

/-- The first projection of `F l ×_S U` composed with `pbMap` is the first projection of
`F k ×_S U` followed by `F.map f`. -/
@[reassoc (attr := simp)]
lemma pbMap_fst (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    pbMap p hp U f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.map f :=
  pullback.lift_fst _ _ _

/-- The morphism `pbMap` commutes with the second projections to `U`. -/
@[reassoc (attr := simp)]
lemma pbMap_snd (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    pbMap p hp U f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- Given a diagram `F` of schemes over a fixed scheme `S` and an affine open `U` of `S`, this is
the diagram `k ↦ F k ×_S U` of the pullbacks of the `F k` along `U`. -/
noncomputable def pbDiagram (U : S.affineOpens) : K ⥤ Scheme.{u} where
  obj k := pullback (p k) U.1.ι
  map f := pbMap p hp U f
  map_id k := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

/-- The object of `pbDiagram` at `k` is `F k ×_S U`. -/
@[simp]
lemma pbDiagram_obj (U : S.affineOpens) (k : K) :
    (pbDiagram p hp U).obj k = pullback (p k) U.1.ι := rfl

/-- The morphism of `pbDiagram` at `f` is `pbMap f`. -/
@[simp]
lemma pbDiagram_map (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    (pbDiagram p hp U).map f = pbMap p hp U f := rfl

end

/-- The inclusion `F k ×_S U ⟶ F k ×_S V` for affine opens `U ≤ V` of `S`. -/
noncomputable def pbRes {U V : S.affineOpens} (h : U ≤ V) (k : K) :
    pullback (p k) U.1.ι ⟶ pullback (p k) V.1.ι :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ S.homOfLE h) (by
    rw [Category.assoc, Scheme.homOfLE_ι, pullback.condition])

/-- The morphism `pbRes` commutes with the first projections to `F k`. -/
@[reassoc (attr := simp)]
lemma pbRes_fst {U V : S.affineOpens} (h : U ≤ V) (k : K) :
    pbRes p h k ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `F k ×_S V` composed with `pbRes` is the second projection of
`F k ×_S U` followed by the inclusion `U ⟶ V`. -/
@[reassoc (attr := simp)]
lemma pbRes_snd {U V : S.affineOpens} (h : U ≤ V) (k : K) :
    pbRes p h k ≫ pullback.snd _ _ = pullback.snd _ _ ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

variable [∀ k, IsAffineHom (p k)]

/-- For an affine morphism `p k` and an affine open `U` of `S`, the scheme `F k ×_S U` is
affine. -/
instance (U : S.affineOpens) (k : K) : IsAffine (pullback (p k) U.1.ι) := by
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  exact inferInstanceAs (IsAffine (pullback _ _))

include hp in
/-- The diagram `k ↦ F k ×_S U` of affine schemes has a limit. -/
instance (U : S.affineOpens) : HasLimit (pbDiagram p hp U) := by
  have (k : K) : IsAffine ((pbDiagram p hp U).obj k) :=
    inferInstanceAs (IsAffine (pullback (p k) U.1.ι))
  exact hasLimit_of_isAffine _

/-! ### Projections to and lifts into the limits `lim_k (F k ×_S U)` -/

omit [∀ k, IsAffineHom (p k)] in
/-- The morphism `pbRes` attached to `U ≤ U` is the identity. -/
@[simp]
lemma pbRes_rfl (U : S.affineOpens) (k : K) : pbRes p (le_refl U) k = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

omit [∀ k, IsAffineHom (p k)] in
/-- The morphisms `pbRes` for `U ≤ V` and `V ≤ W` compose to `pbRes` for `U ≤ W`. -/
@[reassoc (attr := simp)]
lemma pbRes_pbRes {U V W : S.affineOpens} (h : U ≤ V) (h' : V ≤ W) (k : K) :
    pbRes p h k ≫ pbRes p h' k = pbRes p (h.trans h') k := by
  apply pullback.hom_ext <;> simp

omit [∀ k, IsAffineHom (p k)] in
/-- The morphisms `pbRes` commute with the transition morphisms `pbMap`. -/
lemma pbRes_pbMap {U V : S.affineOpens} (h : U ≤ V) {k l : K} (f : k ⟶ l) :
    pbRes p h k ≫ pbMap p hp V f = pbMap p hp U f ≫ pbRes p h l := by
  apply pullback.hom_ext <;> simp

section

include hp

/-- The `k`-th projection out of `lim_k (F k ×_S U)`. -/
noncomputable def pbπ (U : S.affineOpens) (k : K) :
    limit (pbDiagram p hp U) ⟶ pullback (p k) U.1.ι :=
  limit.π (pbDiagram p hp U) k

/-- The projections `pbπ` are compatible with the transition morphisms `pbMap`. -/
@[reassoc]
lemma pbMap_pbπ (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    pbπ p hp U k ≫ pbMap p hp U f = pbπ p hp U l :=
  limit.w (pbDiagram p hp U) f

/-- Two morphisms into `lim_k (F k ×_S U)` that agree after every projection `pbπ` are equal. -/
lemma pbπ_hom_ext {U : S.affineOpens} {Z : Scheme.{u}}
    {a b : Z ⟶ limit (pbDiagram p hp U)}
    (w : ∀ k, a ≫ pbπ p hp U k = b ≫ pbπ p hp U k) : a = b :=
  limit.hom_ext w

/-- The morphism into `lim_k (F k ×_S U)` determined by a compatible family. -/
noncomputable def pbLift (U : S.affineOpens) {Z : Scheme.{u}}
    (q : ∀ k, Z ⟶ pullback (p k) U.1.ι)
    (hq : ∀ {k l : K} (f : k ⟶ l), q k ≫ pbMap p hp U f = q l) :
    Z ⟶ limit (pbDiagram p hp U) :=
  limit.lift (pbDiagram p hp U) { pt := Z, π := { app := q, naturality := by simp [hq] } }

/-- The lift `pbLift q` followed by the projection `pbπ k` is `q k`. -/
@[reassoc (attr := simp)]
lemma pbLift_pbπ (U : S.affineOpens) {Z : Scheme.{u}}
    (q : ∀ k, Z ⟶ pullback (p k) U.1.ι)
    (hq : ∀ {k l : K} (f : k ⟶ l), q k ≫ pbMap p hp U f = q l) (k : K) :
    pbLift p hp U q hq ≫ pbπ p hp U k = q k :=
  limit.lift_π _ _

/-- The family `pbπ U k ≫ pbRes h k` is compatible with the transition morphisms of the
diagram `k ↦ F k ×_S V`. -/
lemma pbResLimit_aux {U V : S.affineOpens} (h : U ≤ V) {k l : K} (f : k ⟶ l) :
    (pbπ p hp U k ≫ pbRes p h k) ≫ pbMap p hp V f = pbπ p hp U l ≫ pbRes p h l := by
  rw [Category.assoc, pbRes_pbMap p hp h f, ← Category.assoc, pbMap_pbπ]

/-- The transition morphism `lim_k (F k ×_S U) ⟶ lim_k (F k ×_S V)` for affine opens
`U ≤ V` of `S`. -/
noncomputable def pbResLimit {U V : S.affineOpens} (h : U ≤ V) :
    limit (pbDiagram p hp U) ⟶ limit (pbDiagram p hp V) :=
  pbLift p hp V (fun k ↦ pbπ p hp U k ≫ pbRes p h k) (pbResLimit_aux p hp h)

/-- The morphism `pbResLimit h` followed by `pbπ V k` is `pbπ U k ≫ pbRes h k`. -/
@[reassoc (attr := simp)]
lemma pbResLimit_pbπ {U V : S.affineOpens} (h : U ≤ V) (k : K) :
    pbResLimit p hp h ≫ pbπ p hp V k = pbπ p hp U k ≫ pbRes p h k :=
  pbLift_pbπ p hp V _ (pbResLimit_aux p hp h) k

/-- The functor `U ↦ lim_k (F k ×_S U)` on the affine opens of `S`. -/
@[simps obj]
noncomputable def pbLimitFunctor : S.affineOpens ⥤ Scheme.{u} where
  obj U := limit (pbDiagram p hp U)
  map {U V} h := pbResLimit p hp (leOfHom h)
  map_id U := by
    refine pbπ_hom_ext p hp fun k ↦ ?_
    simp
  map_comp {U V W} h h' := by
    refine pbπ_hom_ext p hp fun k ↦ ?_
    simp

end

/-! ### The structure morphism to the base -/

variable [IsCofiltered K]

include hp

/-- For `K` cofiltered, the composite of `pbπ U k` with the projection to `U` does not depend
on `k`. -/
lemma pbπ_snd_eq (U : S.affineOpens) (k l : K) :
    pbπ p hp U k ≫ pullback.snd _ _ = pbπ p hp U l ≫ pullback.snd _ _ := by
  refine eq_of_forall_map (fun k ↦ pbπ p hp U k ≫ pullback.snd _ _) (fun f ↦ ?_) k l
  simp [← pbMap_pbπ p hp U f]

/-- The structure morphism `lim_k (F k ×_S U) ⟶ U`. -/
noncomputable def pbLimitHom (U : S.affineOpens) :
    limit (pbDiagram p hp U) ⟶ (U.1 : Scheme.{u}) :=
  pbπ p hp U (Nonempty.some IsCofiltered.nonempty) ≫ pullback.snd _ _

/-- The composite of `pbπ U k` with the projection to `U` is `pbLimitHom U`. -/
@[reassoc (attr := simp)]
lemma pbπ_snd (U : S.affineOpens) (k : K) :
    pbπ p hp U k ≫ pullback.snd _ _ = pbLimitHom p hp U :=
  pbπ_snd_eq p hp U k _

/-- The structure morphisms `pbLimitHom` commute with `pbResLimit h` and the inclusion
`U ⟶ V`. -/
@[reassoc (attr := simp)]
lemma pbResLimit_pbLimitHom {U V : S.affineOpens} (h : U ≤ V) :
    pbResLimit p hp h ≫ pbLimitHom p hp V = pbLimitHom p hp U ≫ S.homOfLE h := by
  rw [← pbπ_snd p hp V (Nonempty.some (IsCofiltered.nonempty (C := K))),
    pbResLimit_pbπ_assoc, pbRes_snd, ← Category.assoc, pbπ_snd]

/-! ### The universal property of `lim_k (F k ×_S U)` -/

/-- The projection `lim_k (F k ×_S U) ⟶ F k`. -/
noncomputable def pbρ (U : S.affineOpens) (k : K) :
    limit (pbDiagram p hp U) ⟶ F.obj k :=
  pbπ p hp U k ≫ pullback.fst _ _

/-- The projection `pbρ U k` followed by `p k` equals `pbLimitHom U` followed by the inclusion
of `U` into `S`. -/
@[reassoc (attr := simp)]
lemma pbρ_comp (U : S.affineOpens) (k : K) :
    pbρ p hp U k ≫ p k = pbLimitHom p hp U ≫ U.1.ι := by
  rw [pbρ, Category.assoc, pullback.condition, ← Category.assoc, pbπ_snd]

omit [IsCofiltered K] in
/-- The projections `pbρ U k` are compatible with the morphisms of `F`. -/
@[reassoc (attr := simp)]
lemma pbρ_map (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    pbρ p hp U k ≫ F.map f = pbρ p hp U l := by
  rw [pbρ, pbρ, Category.assoc, ← pbMap_fst p hp U f, ← Category.assoc, pbMap_pbπ]

omit [IsCofiltered K] in
/-- The morphism `pbResLimit h` commutes with the projections `pbρ` to `F k`. -/
@[reassoc (attr := simp)]
lemma pbResLimit_pbρ {U V : S.affineOpens} (h : U ≤ V) (k : K) :
    pbResLimit p hp h ≫ pbρ p hp V k = pbρ p hp U k := by
  rw [pbρ, pbρ, ← Category.assoc, pbResLimit_pbπ, Category.assoc, pbRes_fst]

/-- Two morphisms into `lim_k (F k ×_S U)` that agree after every projection `pbρ` and after
`pbLimitHom` are equal. -/
lemma pb_hom_ext {U : S.affineOpens} {Z : Scheme.{u}}
    {a b : Z ⟶ limit (pbDiagram p hp U)}
    (h₁ : ∀ k, a ≫ pbρ p hp U k = b ≫ pbρ p hp U k)
    (h₂ : a ≫ pbLimitHom p hp U = b ≫ pbLimitHom p hp U) : a = b := by
  refine pbπ_hom_ext p hp fun k ↦ pullback.hom_ext ?_ ?_
  · simpa [pbρ] using h₁ k
  · simpa [pbπ_snd_assoc] using h₂

omit [IsCofiltered K] [∀ k, IsAffineHom (p k)] in
/-- The morphisms `pullback.lift (r k) t` into `F k ×_S U` are compatible with the transition
morphisms `pbMap`. -/
lemma pbUniv_aux (U : S.affineOpens) {Z : Scheme.{u}} (r : ∀ k, Z ⟶ F.obj k)
    (t : Z ⟶ (U.1 : Scheme.{u})) (hr : ∀ {k l : K} (f : k ⟶ l), r k ≫ F.map f = r l)
    (ht : ∀ k, r k ≫ p k = t ≫ U.1.ι) {k l : K} (f : k ⟶ l) :
    pullback.lift (r k) t (ht k) ≫ pbMap p hp U f = pullback.lift (r l) t (ht l) := by
  apply pullback.hom_ext <;> simp [hr]

/-- The morphism into `lim_k (F k ×_S U)` determined by a compatible family of morphisms to the
`F k` together with a morphism to `U`. -/
noncomputable def pbUniv (U : S.affineOpens) {Z : Scheme.{u}} (r : ∀ k, Z ⟶ F.obj k)
    (t : Z ⟶ (U.1 : Scheme.{u})) (hr : ∀ {k l : K} (f : k ⟶ l), r k ≫ F.map f = r l)
    (ht : ∀ k, r k ≫ p k = t ≫ U.1.ι) :
    Z ⟶ limit (pbDiagram p hp U) :=
  pbLift p hp U (fun k ↦ pullback.lift (r k) t (ht k)) (pbUniv_aux p hp U r t hr ht)

omit [IsCofiltered K] in
/-- The morphism `pbUniv r t` followed by `pbπ U k` is `pullback.lift (r k) t`. -/
@[reassoc]
lemma pbUniv_pbπ (U : S.affineOpens) {Z : Scheme.{u}} (r : ∀ k, Z ⟶ F.obj k)
    (t : Z ⟶ (U.1 : Scheme.{u})) (hr : ∀ {k l : K} (f : k ⟶ l), r k ≫ F.map f = r l)
    (ht : ∀ k, r k ≫ p k = t ≫ U.1.ι) (k : K) :
    pbUniv p hp U r t hr ht ≫ pbπ p hp U k = pullback.lift (r k) t (ht k) :=
  pbLift_pbπ p hp U (fun k ↦ pullback.lift (r k) t (ht k)) (pbUniv_aux p hp U r t hr ht) k

omit [IsCofiltered K] in
/-- The morphism `pbUniv r t` followed by `pbρ U k` is `r k`. -/
@[reassoc (attr := simp)]
lemma pbUniv_pbρ (U : S.affineOpens) {Z : Scheme.{u}} (r : ∀ k, Z ⟶ F.obj k)
    (t : Z ⟶ (U.1 : Scheme.{u})) (hr : ∀ {k l : K} (f : k ⟶ l), r k ≫ F.map f = r l)
    (ht : ∀ k, r k ≫ p k = t ≫ U.1.ι) (k : K) :
    pbUniv p hp U r t hr ht ≫ pbρ p hp U k = r k := by
  rw [pbρ, ← Category.assoc, pbUniv_pbπ, pullback.lift_fst]

/-- The morphism `pbUniv r t` followed by `pbLimitHom U` is `t`. -/
@[reassoc (attr := simp)]
lemma pbUniv_pbLimitHom (U : S.affineOpens) {Z : Scheme.{u}} (r : ∀ k, Z ⟶ F.obj k)
    (t : Z ⟶ (U.1 : Scheme.{u})) (hr : ∀ {k l : K} (f : k ⟶ l), r k ≫ F.map f = r l)
    (ht : ∀ k, r k ≫ p k = t ≫ U.1.ι) :
    pbUniv p hp U r t hr ht ≫ pbLimitHom p hp U = t := by
  rw [← pbπ_snd p hp U (Nonempty.some (IsCofiltered.nonempty (C := K))), ← Category.assoc,
    pbUniv_pbπ, pullback.lift_snd]

/-! ### The squares over an inclusion of affine opens are pullbacks -/

/-- For affine opens `U ≤ V` of `S`, the square relating `lim (F ×_S U)` and `lim (F ×_S V)`
over `U ⟶ V` is a pullback square. -/
lemma isPullback_pbResLimit {U V : S.affineOpens} (h : U ≤ V) :
    IsPullback (pbResLimit p hp h) (pbLimitHom p hp U) (pbLimitHom p hp V) (S.homOfLE h) := by
  have key : ∀ (s : PullbackCone (pbLimitHom p hp V) (S.homOfLE h)) (k : K),
      (s.fst ≫ pbρ p hp V k) ≫ p k = s.snd ≫ U.1.ι := by
    intro s k
    rw [Category.assoc, pbρ_comp, s.condition_assoc, Scheme.homOfLE_ι]
  refine ⟨⟨pbResLimit_pbLimitHom p hp h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ pbUniv p hp U (fun k ↦ s.fst ≫ pbρ p hp V k) s.snd (fun f ↦ by simp) (key s))
    (fun s ↦ ?_) (fun s ↦ pbUniv_pbLimitHom _ _ _ _ _ _ _) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · exact pb_hom_ext p hp (fun k ↦ by simp) (by simp [s.condition])
  · exact pb_hom_ext p hp (fun k ↦ by simp [← h₁]) (by simp [h₂])

/-! ### Gluing the local limits -/

/-- The poset of affine opens of `S` is a thin quiver. -/
local instance isThin_affineOpens : Quiver.IsThin S.affineOpens := fun _ _ ↦ inferInstance

/-- The relative gluing datum over the cover of `S` by all of its affine opens, which assigns
to an affine open `U` the scheme `lim_k (F k ×_S U)`. -/
noncomputable def gluingData : Scheme.Cover.RelativeGluingData S.directedAffineCover where
  functor := pbLimitFunctor p hp
  natTrans :=
    { app := fun U ↦ pbLimitHom p hp U
      naturality := fun _ _ h ↦ pbResLimit_pbLimitHom p hp (leOfHom h) }
  equifibered := fun {_ _} h ↦ isPullback_pbResLimit p hp (leOfHom h)

/-- The inclusion of `lim_k (F k ×_S U)` as a member of the open cover of the glued scheme. -/
noncomputable def gluedι (U : S.affineOpens) :
    limit (pbDiagram p hp U) ⟶ (gluingData p hp).glued :=
  colimit.ι (gluingData p hp).functor U

/-- The inclusions `gluedι` into the glued scheme are compatible with `pbResLimit h`. -/
@[reassoc (attr := simp)]
lemma pbResLimit_gluedι {U V : S.affineOpens} (h : U ≤ V) :
    pbResLimit p hp h ≫ gluedι p hp V = gluedι p hp U :=
  colimit.w (gluingData p hp).functor (homOfLE h)

/-- The inclusion of `lim_k (F k ×_S U)` into the glued scheme is the base change of `U ⊆ S`
along the structure morphism of the glued scheme. -/
lemma isPullback_gluedι (U : S.affineOpens) :
    IsPullback (pbLimitHom p hp U) (gluedι p hp U) U.1.ι (gluingData p hp).toBase :=
  (gluingData p hp).isPullback_natTrans_ι_toBase U

/-- Two morphisms out of the glued scheme that agree after every inclusion `gluedι U` are
equal. -/
lemma gluedι_hom_ext {Z : Scheme.{u}} {a b : (gluingData p hp).glued ⟶ Z}
    (w : ∀ U, gluedι p hp U ≫ a = gluedι p hp U ≫ b) : a = b :=
  (gluingData p hp).cover.hom_ext a b w

/-- The projections `pbρ U k` are compatible with the transition morphisms of the open cover of
the glued scheme. -/
lemma gluedπ_aux (k : K) {U V : S.affineOpens} (h : U ⟶ V) :
    (gluingData p hp).cover.trans h ≫ pbρ p hp V k = pbρ p hp U k :=
  pbResLimit_pbρ p hp (leOfHom h) k

/-- The projection from the glued scheme to `F k`. -/
noncomputable def gluedπ (k : K) : (gluingData p hp).glued ⟶ F.obj k :=
  (gluingData p hp).cover.glueMorphismsOfLocallyDirected
    (fun U ↦ pbρ p hp U k) (gluedπ_aux p hp k)

/-- The restriction of `gluedπ k` to `lim_k (F k ×_S U)` is `pbρ U k`. -/
@[reassoc (attr := simp)]
lemma gluedι_gluedπ (U : S.affineOpens) (k : K) :
    gluedι p hp U ≫ gluedπ p hp k = pbρ p hp U k :=
  (gluingData p hp).cover.map_glueMorphismsOfLocallyDirected
    (fun U ↦ pbρ p hp U k) (gluedπ_aux p hp k) U

/-- The projections `gluedπ k` are compatible with the morphisms of `F`. -/
@[reassoc (attr := simp)]
lemma gluedπ_map {k l : K} (f : k ⟶ l) : gluedπ p hp k ≫ F.map f = gluedπ p hp l := by
  refine gluedι_hom_ext p hp fun U ↦ ?_
  rw [← Category.assoc, gluedι_gluedπ, pbρ_map, gluedι_gluedπ]

/-- The projection `gluedπ k` followed by `p k` is the structure morphism of the glued scheme
to `S`. -/
@[reassoc]
lemma gluedπ_comp (k : K) : gluedπ p hp k ≫ p k = (gluingData p hp).toBase := by
  refine gluedι_hom_ext p hp fun U ↦ ?_
  rw [← Category.assoc, gluedι_gluedπ, pbρ_comp]
  exact ((gluingData p hp).ι_toBase U).symm

/-- The cone over `F` with vertex the glued scheme. -/
noncomputable def gluedCone : Cone F where
  pt := (gluingData p hp).glued
  π :=
    { app := gluedπ p hp
      naturality := fun _ _ f ↦ by simp }

/-! ### The glued scheme is the limit -/

omit [∀ k, IsAffineHom (p k)] in
/-- The morphism to `S` induced by a cone over `F`. -/
noncomputable def coneBase (s : Cone F) : s.pt ⟶ S :=
  s.π.app (Nonempty.some IsCofiltered.nonempty) ≫ p _

omit [∀ k, IsAffineHom (p k)] in
/-- For a cone `s` over `F`, each composite `s.π.app k ≫ p k` is `coneBase p s`. -/
lemma cone_π_comp (s : Cone F) (k : K) : s.π.app k ≫ p k = coneBase p s := by
  refine eq_of_forall_map (fun k ↦ s.π.app k ≫ p k) (fun f ↦ ?_) _ _
  rw [← s.w f, Category.assoc, hp f]

section ConeCover

omit hp [∀ k, IsAffineHom (p k)]

variable (s : Cone F)

/-- The cover of the vertex of a cone by the preimages of the affine opens of `S`. -/
noncomputable def coneCover : s.pt.OpenCover :=
  S.directedAffineCover.pullback₁ (coneBase p s)

/-- The index set of the cone cover is the category of affine opens of `S`. -/
instance : Category.{u} (coneCover p s).I₀ := inferInstanceAs (Category S.affineOpens)

/-- The cone cover is locally directed. -/
noncomputable instance : (coneCover p s).LocallyDirected :=
  inferInstanceAs
    (Scheme.Cover.LocallyDirected (S.directedAffineCover.pullback₁ (coneBase p s)))

/-- The inclusion of a member of the cone cover into the vertex of the cone. -/
noncomputable def coneCoverFst (U : S.affineOpens) :
    pullback (coneBase p s) U.1.ι ⟶ s.pt :=
  pullback.fst _ _

/-- The projection from a member of the cone cover to the corresponding affine open of `S`. -/
noncomputable def coneCoverSnd (U : S.affineOpens) :
    pullback (coneBase p s) U.1.ι ⟶ (U.1 : Scheme.{u}) :=
  pullback.snd _ _

/-- The transition morphism of the cone cover attached to an inclusion of affine opens. -/
noncomputable def coneCoverTrans {U V : S.affineOpens} (h : U ≤ V) :
    pullback (coneBase p s) U.1.ι ⟶ pullback (coneBase p s) V.1.ι :=
  pullback.map _ _ _ _ (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

/-- The inclusion of the member of the cone cover indexed by `U` is `coneCoverFst p s U`. -/
lemma coneCover_f_eq (U : S.affineOpens) : (coneCover p s).f U = coneCoverFst p s U := rfl

/-- The transition morphism of the cone cover attached to `h : U ⟶ V` is `coneCoverTrans`. -/
lemma coneCover_trans_eq {U V : S.affineOpens} (h : U ⟶ V) :
    (coneCover p s).trans h = coneCoverTrans p s (leOfHom h) := rfl

/-- The pullback square defining the member of the cone cover indexed by `U` commutes. -/
@[reassoc]
lemma coneCoverFst_comp (U : S.affineOpens) :
    coneCoverFst p s U ≫ coneBase p s = coneCoverSnd p s U ≫ U.1.ι :=
  pullback.condition

/-- The transition morphism `coneCoverTrans h` commutes with the inclusions into `s.pt`. -/
@[reassoc (attr := simp)]
lemma coneCoverTrans_fst {U V : S.affineOpens} (h : U ≤ V) :
    coneCoverTrans p s h ≫ coneCoverFst p s V = coneCoverFst p s U := by
  simp [coneCoverTrans, coneCoverFst]

/-- The transition morphism `coneCoverTrans h` commutes with the projections to the affine opens
and the inclusion `U ⟶ V`. -/
@[reassoc (attr := simp)]
lemma coneCoverTrans_snd {U V : S.affineOpens} (h : U ≤ V) :
    coneCoverTrans p s h ≫ coneCoverSnd p s V = coneCoverSnd p s U ≫ S.homOfLE h := by
  simp [coneCoverTrans, coneCoverSnd]

end ConeCover

omit hp [∀ k, IsAffineHom (p k)] in
/-- The restrictions of the cone `s` to a member of the cone cover are compatible with the
morphisms of `F`. -/
lemma coneLocal_hr (s : Cone F) (U : S.affineOpens) {k l : K} (f : k ⟶ l) :
    (coneCoverFst p s U ≫ s.π.app k) ≫ F.map f = coneCoverFst p s U ≫ s.π.app l := by
  rw [Category.assoc, s.w f]

omit [∀ k, IsAffineHom (p k)] in
/-- The restriction of `s.π.app k` to the member of the cone cover indexed by `U`, followed by
`p k`, equals `coneCoverSnd p s U` followed by the inclusion of `U` into `S`. -/
lemma coneLocal_ht (s : Cone F) (U : S.affineOpens) (k : K) :
    (coneCoverFst p s U ≫ s.π.app k) ≫ p k = coneCoverSnd p s U ≫ U.1.ι := by
  rw [Category.assoc, cone_π_comp p hp s k, coneCoverFst_comp]

/-- The local comparison morphism from a member of the cone cover to the local limit. -/
noncomputable def coneLocal (s : Cone F) (U : S.affineOpens) :
    pullback (coneBase p s) U.1.ι ⟶ limit (pbDiagram p hp U) :=
  pbUniv p hp U (fun k ↦ coneCoverFst p s U ≫ s.π.app k) (coneCoverSnd p s U)
    (coneLocal_hr p s U) (coneLocal_ht p hp s U)

/-- The morphism `coneLocal s U` followed by `pbρ U k` is the restriction of `s.π.app k`. -/
@[reassoc (attr := simp)]
lemma coneLocal_pbρ (s : Cone F) (U : S.affineOpens) (k : K) :
    coneLocal p hp s U ≫ pbρ p hp U k = coneCoverFst p s U ≫ s.π.app k :=
  pbUniv_pbρ p hp U _ _ (coneLocal_hr p s U) (coneLocal_ht p hp s U) k

/-- The morphism `coneLocal s U` followed by `pbLimitHom U` is `coneCoverSnd p s U`. -/
@[reassoc (attr := simp)]
lemma coneLocal_pbLimitHom (s : Cone F) (U : S.affineOpens) :
    coneLocal p hp s U ≫ pbLimitHom p hp U = coneCoverSnd p s U :=
  pbUniv_pbLimitHom p hp U _ _ (coneLocal_hr p s U) (coneLocal_ht p hp s U)

/-- The morphisms `coneLocal s U ≫ gluedι U` are compatible with the transition morphisms of
the cone cover. -/
lemma coneDesc_aux (s : Cone F) {U V : S.affineOpens} (h : U ⟶ V) :
    coneCoverTrans p s (leOfHom h) ≫ (coneLocal p hp s V ≫ gluedι p hp V)
      = coneLocal p hp s U ≫ gluedι p hp U := by
  rw [← pbResLimit_gluedι p hp (leOfHom h), ← Category.assoc, ← Category.assoc]
  congr 1
  refine pb_hom_ext p hp (fun k ↦ ?_) ?_
  · rw [Category.assoc, coneLocal_pbρ, Category.assoc, pbResLimit_pbρ, coneLocal_pbρ,
      ← Category.assoc, coneCoverTrans_fst]
  · rw [Category.assoc, coneLocal_pbLimitHom, Category.assoc, pbResLimit_pbLimitHom,
      ← Category.assoc, coneLocal_pbLimitHom, coneCoverTrans_snd]

/-- The comparison morphism from the vertex of a cone to the glued scheme. -/
noncomputable def coneDesc (s : Cone F) : s.pt ⟶ (gluingData p hp).glued :=
  (coneCover p s).glueMorphismsOfLocallyDirected
    (fun U ↦ coneLocal p hp s U ≫ gluedι p hp U) (coneDesc_aux p hp s)

/-- The restriction of `coneDesc s` to the member of the cone cover indexed by `U` is
`coneLocal s U ≫ gluedι U`. -/
@[reassoc (attr := simp)]
lemma coneCoverFst_coneDesc (s : Cone F) (U : S.affineOpens) :
    coneCoverFst p s U ≫ coneDesc p hp s = coneLocal p hp s U ≫ gluedι p hp U :=
  (coneCover p s).map_glueMorphismsOfLocallyDirected
    (fun U ↦ coneLocal p hp s U ≫ gluedι p hp U) (coneDesc_aux p hp s) U

/-- A morphism from the vertex of a cone `s` to the glued scheme whose composites with the
projections `gluedπ k` are `s.π.app k` is `coneDesc s`. -/
lemma coneDesc_unique (s : Cone F) (m : s.pt ⟶ (gluingData p hp).glued)
    (hm : ∀ k, m ≫ gluedπ p hp k = s.π.app k) : m = coneDesc p hp s := by
  have hbase : m ≫ (gluingData p hp).toBase = coneBase p s := by
    rw [← gluedπ_comp p hp (Nonempty.some (IsCofiltered.nonempty (C := K))), ← Category.assoc,
      hm, cone_π_comp p hp s]
  refine Scheme.Cover.hom_ext (coneCover p s) _ _ fun (U : S.affineOpens) ↦ ?_
  show coneCoverFst p s U ≫ m = coneCoverFst p s U ≫ coneDesc p hp s
  rw [coneCoverFst_coneDesc]
  have hsq := isPullback_gluedι p hp U
  have hw : coneCoverSnd p s U ≫ U.1.ι
      = (coneCoverFst p s U ≫ m) ≫ (gluingData p hp).toBase := by
    rw [Category.assoc, hbase, coneCoverFst_comp]
  have heq : hsq.lift _ _ hw = coneLocal p hp s U := by
    refine pb_hom_ext p hp (fun k ↦ ?_) ?_
    · rw [coneLocal_pbρ, ← gluedι_gluedπ p hp U k, ← Category.assoc, hsq.lift_snd,
        Category.assoc, hm k]
    · rw [hsq.lift_fst, coneLocal_pbLimitHom]
  rw [← heq, hsq.lift_snd]

/-- The glued scheme is a limit of `F`. -/
noncomputable def isLimitGluedCone : IsLimit (gluedCone p hp) where
  lift s := coneDesc p hp s
  fac s k := by
    refine Scheme.Cover.hom_ext (coneCover p s) _ _ fun (U : S.affineOpens) ↦ ?_
    change coneCoverFst p s U ≫ coneDesc p hp s ≫ gluedπ p hp k
      = coneCoverFst p s U ≫ s.π.app k
    rw [← Category.assoc, coneCoverFst_coneDesc, Category.assoc, gluedι_gluedπ, coneLocal_pbρ]
  uniq s m hm := coneDesc_unique p hp s m hm

/-- A cofiltered diagram `F` of schemes equipped with a natural family of affine morphisms to a
fixed scheme `S` has a limit. -/
lemma hasLimit_of_isAffineHom_of_isCofiltered : HasLimit F :=
  ⟨_, isLimitGluedCone p hp⟩

end CofilteredLimit

open CofilteredLimit in
/-- **Limits of inverse systems with affine transition morphisms.** A cofiltered diagram of
schemes whose transition morphisms are affine has a limit in the category of schemes.

The limit is constructed by gluing, over the affine opens `U` of a fixed stage `D i₀`, the
affine schemes `lim_j (D j ×_{D i₀} U)`; see
`AlgebraicGeometry.CofilteredLimit.hasLimit_of_isAffineHom_of_isCofiltered`. -/
@[stacks 01YX "existence", instance, sga "4 VII 5.1" "existence of lim"]
theorem hasLimit_of_isCofiltered_of_isAffineHom
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] : HasLimit D := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : HasLimit (Over.forget i₀ ⋙ D) :=
    hasLimit_of_isAffineHom_of_isCofiltered (F := Over.forget i₀ ⋙ D)
      (fun j ↦ D.map j.hom) (fun {k l} f ↦ by
        show D.map f.left ≫ D.map l.hom = D.map k.hom
        rw [← D.map_comp, Over.w f])
  exact Functor.Initial.hasLimit_of_comp (Over.forget i₀)

/-! ### The remaining assertions of tag 01YX

Parts (1) and (2) of the Stacks lemma -- that every limit projection is affine, and that the
inverse image of an open subscheme under a projection is the limit of the corresponding inverse
images -- are already proved in Mathlib, for an arbitrary limiting cone. -/

add_to_stacks 01YX "part (1)" AlgebraicGeometry.isAffineHom_π_app
add_to_ega "IV 8.13.4" "partial" AlgebraicGeometry.isAffineHom_π_app
add_to_stacks 01YX "part (2)" AlgebraicGeometry.isLimitOpensCone

/-! ### Section 01YV

Lemma 01YX is the construction of the limit that section 01YV announces, together with the two
properties of it that the section records. -/

add_to_stacks 01YV "the construction of the limit of an inverse system of schemes whose \
transition morphisms are affine (Lemma 01YX)"
  AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom
add_to_stacks 01YV "the projections of the limit are affine (Lemma 01YX (1))"
  AlgebraicGeometry.isAffineHom_π_app
add_to_stacks 01YV "the inverse image of an open subscheme under a projection is the limit of \
its inverse images (Lemma 01YX (2))" AlgebraicGeometry.isLimitOpensCone

end AlgebraicGeometry
