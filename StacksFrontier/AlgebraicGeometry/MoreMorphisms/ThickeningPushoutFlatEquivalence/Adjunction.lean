module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence.GluingFunctor

/-!
# The adjunction between the comparison functor and the gluing functor

The unit `Stacks.Pushout.gluingUnitApp` from a module on `V'` to the glued module of its
comparison triple, the overlap comparisons `Stacks.Pushout.targetOverlap` and
`Stacks.Pushout.ambientOverlap`, the transposition `Stacks.Pushout.tripleHomEquiv`, and the
adjunction `Stacks.Pushout.baseChangeTripleAdjunction` of [Stacks Project, Tag 08KU] together
with its unit and counit.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
  (g : V' ⟶ pushout i f)

/-! ### The unit -/

/-- Transport of a pushforward along the reflexivity of a morphism is the identity. -/
theorem pushforwardCongr_rfl_app {A B : Scheme.{u}} (p : A ⟶ B) (N : A.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : p = p)).hom.app N = 𝟙 _ := by
  ext U x
  simp

/-- Transports of pushforwards along equalities of morphisms compose. -/
theorem pushforwardCongr_trans_app {A B : Scheme.{u}} {p q r : A ⟶ B}
    (h₁ : p = q) (h₂ : q = r) (N : A.Modules) :
    (Scheme.Modules.pushforwardCongr h₁).hom.app N ≫
        (Scheme.Modules.pushforwardCongr h₂).hom.app N =
      (Scheme.Modules.pushforwardCongr (h₁.trans h₂)).hom.app N := by
  subst h₁ h₂
  rw [pushforwardCongr_rfl_app, Category.comp_id]

/-- The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` read through the comparison of the two pullbacks and
the comparison of the two pushforwards. -/
theorem unit_pushforward_comp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
            ((Scheme.Modules.pullback q).obj M)) ≫
        (Scheme.Modules.pushforwardComp p q).hom.app
          ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app M ≫
        (Scheme.Modules.pushforward (p ≫ q)).map
          ((Scheme.Modules.pullbackComp p q).inv.app M) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q))
    (Scheme.Modules.pullbackComp p q).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  rw [← h]
  simp only [CategoryTheory.Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj]

/-- The unit of `f^* ⊣ f_*` is compatible with transport along an equality of morphisms. -/
theorem unit_congr {A B : Scheme.{u}} {p q : A ⟶ B} (h : p = q) (M : B.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map ((Scheme.Modules.pullbackCongr h).hom.app M) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback q).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M := by
  subst h
  have h2 : (Scheme.Modules.pullbackCongr (rfl : p = p)).hom.app M = 𝟙 _ := by
    ext U x
    simp [Scheme.Modules.pullbackCongr]
  rw [pushforwardCongr_rfl_app, h2, CategoryTheory.Functor.map_id]
  simp

/-- Transport of a pullback along the reflexivity of a morphism is the identity. -/
theorem pullbackCongr_rfl_app {A B : Scheme.{u}} (p : A ⟶ B) (N : B.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : p = p)).hom.app N = 𝟙 _ := by
  ext U x
  simp [Scheme.Modules.pullbackCongr]

/-- Transports of pullbacks along equalities of morphisms compose. -/
theorem pullbackCongr_trans_app {A B : Scheme.{u}} {p q r : A ⟶ B}
    (h₁ : p = q) (h₂ : q = r) (N : B.Modules) :
    (Scheme.Modules.pullbackCongr h₁).hom.app N ≫
        (Scheme.Modules.pullbackCongr h₂).hom.app N =
      (Scheme.Modules.pullbackCongr (h₁.trans h₂)).hom.app N := by
  subst h₁ h₂
  rw [pullbackCongr_rfl_app, Category.comp_id]

/-- The inverse transport of a pullback along reflexivity is the identity. -/
theorem pullbackCongr_rfl_inv_app {A B : Scheme.{u}} (p : A ⟶ B) (N : B.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : p = p)).inv.app N = 𝟙 _ := by
  ext U x
  simp [Scheme.Modules.pullbackCongr]

/-- Transport of a pullback along a symmetric equality is the inverse transport. -/
theorem pullbackCongr_symm_app {A B : Scheme.{u}} {p q : A ⟶ B} (h : p = q)
    (N : B.Modules) :
    (Scheme.Modules.pullbackCongr h.symm).hom.app N =
      (Scheme.Modules.pullbackCongr h).inv.app N := by
  subst h
  rw [pullbackCongr_rfl_app, pullbackCongr_rfl_inv_app]

/-- Pushing the unit of
`p^* ⊣ p_*` forward along `q` and transporting along `p ≫ q = r` is the unit of `r^* ⊣ r_*`
followed by the two canonical comparisons of pullbacks. -/
@[reassoc]
theorem unit_pushforward_congr {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    {r : A ⟶ C} (h : p ≫ q = r) (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
            ((Scheme.Modules.pullback q).obj M)) ≫
        (Scheme.Modules.pushforwardComp p q).hom.app
          ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M)) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app
          ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M ≫
        (Scheme.Modules.pushforward r).map
          ((Scheme.Modules.pullbackCongr h).inv.app M ≫
            (Scheme.Modules.pullbackComp p q).inv.app M) := by
  have h1 := unit_pushforward_comp p q M
  have h2 := (Scheme.Modules.pushforwardCongr h).hom.naturality
    ((Scheme.Modules.pullbackComp p q).inv.app M)
  simp only [Functor.comp_obj] at h2
  have hu := unit_congr h M
  have hn := (Scheme.Modules.pushforwardCongr h).hom.naturality
    ((Scheme.Modules.pullbackCongr h).hom.app M)
  rw [hn] at hu
  have h4 : (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app M ≫
      (Scheme.Modules.pushforwardCongr h).hom.app
        ((Scheme.Modules.pullback (p ≫ q)).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M ≫
        (Scheme.Modules.pushforward r).map ((Scheme.Modules.pullbackCongr h).inv.app M) := by
    rw [← hu, Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app M ≫
          (Scheme.Modules.pushforward (p ≫ q)).map
            ((Scheme.Modules.pullbackComp p q).inv.app M)) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app
          ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj M)) := by
      rw [← h1]; simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).unit.app M ≫
        (Scheme.Modules.pushforwardCongr h).hom.app
            ((Scheme.Modules.pullback (p ≫ q)).obj M) ≫
          (Scheme.Modules.pushforward r).map
            ((Scheme.Modules.pullbackComp p q).inv.app M) := by
      rw [Category.assoc, h2]
    _ = _ := by
      rw [← Category.assoc, h4, Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- The canonical overlap comparison absorbs the two transports coming from the factorisations
`U ⟶ V ⟶ V'` and `U ⟶ U' ⟶ V'` of `U ⟶ V'`. -/
theorem pullbackCongr_comp_overlapComparison (M : V'.Modules) :
    ((Scheme.Modules.pullbackCongr (commonToTarget_comp_restriction i f g)).inv.app M ≫
        (Scheme.Modules.pullbackComp (commonToTarget i f g)
          (targetRestriction i f g)).inv.app M) ≫ ((overlapComparison i f g).app M).hom =
      (Scheme.Modules.pullbackCongr (commonToAmbient_comp_restriction i f g)).inv.app M ≫
        (Scheme.Modules.pullbackComp (commonToAmbient i f g)
          (ambientRestriction i f g)).inv.app M := by
  have e1 : (Scheme.Modules.pullbackCongr (commonToTarget_comp_restriction i f g)).hom.app M ≫
      (Scheme.Modules.pullbackCongr (commonToAmbient_comp_restriction i f g)).inv.app M =
      (Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g)).hom.app M := by
    rw [← pullbackCongr_symm_app (commonToAmbient_comp_restriction i f g),
      pullbackCongr_trans_app]
  have key : (Scheme.Modules.pullbackCongr (commonToTarget_comp_restriction i f g)).inv.app M ≫
      (Scheme.Modules.pullbackCongr (commonToTarget_comp_targetRestriction i f g)).hom.app M =
      (Scheme.Modules.pullbackCongr (commonToAmbient_comp_restriction i f g)).inv.app M := by
    rw [← e1, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simp only [overlapComparison, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, key]

/-- The two units of the restrictions to `V` and to `U'` agree after mapping into the
pushforward of the common restriction. -/
theorem unit_glueTargetNat_eq_unit_glueAmbientNat (hi : Stacks.Thickenings.IsThickening i)
    [IsAffineHom f] (M : V'.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).unit.app M ≫
        (glueTargetNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).unit.app M ≫
        (glueAmbientNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M) := by
  have hU := unit_pushforward_congr (commonToAmbient i f g) (ambientRestriction i f g)
    (commonToAmbient_comp_restriction i f g) M
  dsimp only [glueTargetNat, glueAmbientNat, targetUnitNat, ambientUnitNat,
    baseChangeTripleFunctor, tripleTarget, tripleAmbient, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_obj]
  simp only [Category.assoc]
  rw [unit_pushforward_congr_assoc (commonToTarget i f g) (targetRestriction i f g)
    (commonToTarget_comp_restriction i f g) M, hU, ← CategoryTheory.Functor.map_comp,
    pullbackCongr_comp_overlapComparison i f g M]

/-- The first projection of the glued module is natural. -/
theorem tripleGluingFunctor_map_fst {T T' : GluingTriple i f g} (φ : T ⟶ T') :
    (tripleGluingFunctor i f g).map φ ≫
        pullback.fst ((glueTargetNat i f g).app T') ((glueAmbientNat i f g).app T') =
      pullback.fst ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) ≫
        (glueTargetFunctor i f g).map φ :=
  pullback.lift_fst _ _ _

/-- The second projection of the glued module is natural. -/
theorem tripleGluingFunctor_map_snd {T T' : GluingTriple i f g} (φ : T ⟶ T') :
    (tripleGluingFunctor i f g).map φ ≫
        pullback.snd ((glueTargetNat i f g).app T') ((glueAmbientNat i f g).app T') =
      pullback.snd ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T) ≫
        (glueAmbientFunctor i f g).map φ :=
  pullback.lift_snd _ _ _

/-- The map from a module on `V'` to the fibre product of the pushforwards of its two
restrictions, given by the two units of `(V ⟶ V')^* ⊣ (V ⟶ V')_*` and
`(U' ⟶ V')^* ⊣ (U' ⟶ V')_*`. -/
noncomputable def gluingUnitApp (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]
    (M : V'.Modules) :
    M ⟶ (tripleGluingFunctor i f g).obj ((baseChangeTripleFunctor i f hi g).obj M) :=
  pullback.lift _ _ (unit_glueTargetNat_eq_unit_glueAmbientNat i f g hi M)

/-- The first component of `Stacks.Pushout.gluingUnitApp` is the unit for `V ⟶ V'`. -/
theorem gluingUnitApp_fst (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]
    (M : V'.Modules) :
    gluingUnitApp i f g hi M ≫
        pullback.fst ((glueTargetNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))
          ((glueAmbientNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).unit.app M :=
  pullback.lift_fst _ _ _

/-- The second component of `Stacks.Pushout.gluingUnitApp` is the unit for `U' ⟶ V'`. -/
theorem gluingUnitApp_snd (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]
    (M : V'.Modules) :
    gluingUnitApp i f g hi M ≫
        pullback.snd ((glueTargetNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M))
          ((glueAmbientNat i f g).app ((baseChangeTripleFunctor i f hi g).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).unit.app M :=
  pullback.lift_snd _ _ _

/-! ### The overlap comparisons and the transposition -/

/-- The canonical comparison from the restriction of `M` to `U` through `V'` to its restriction
through `V`. -/
noncomputable def targetOverlap (M : V'.Modules) :
    (Scheme.Modules.pullback (commonRestriction i f g)).obj M ⟶
      (Scheme.Modules.pullback (commonToTarget i f g)).obj
        ((Scheme.Modules.pullback (targetRestriction i f g)).obj M) :=
  (Scheme.Modules.pullbackCongr (commonToTarget_comp_restriction i f g)).inv.app M ≫
    (Scheme.Modules.pullbackComp (commonToTarget i f g)
      (targetRestriction i f g)).inv.app M

/-- The canonical comparison from the restriction of `M` to `U` through `V'` to its restriction
through `U'`. -/
noncomputable def ambientOverlap (M : V'.Modules) :
    (Scheme.Modules.pullback (commonRestriction i f g)).obj M ⟶
      (Scheme.Modules.pullback (commonToAmbient i f g)).obj
        ((Scheme.Modules.pullback (ambientRestriction i f g)).obj M) :=
  (Scheme.Modules.pullbackCongr (commonToAmbient_comp_restriction i f g)).inv.app M ≫
    (Scheme.Modules.pullbackComp (commonToAmbient i f g)
      (ambientRestriction i f g)).inv.app M

/-- `Stacks.Pushout.targetOverlap` is an isomorphism. -/
instance isIso_targetOverlap (M : V'.Modules) : IsIso (targetOverlap i f g M) := by
  dsimp only [targetOverlap]
  infer_instance

/-- `Stacks.Pushout.ambientOverlap` is an isomorphism. -/
instance isIso_ambientOverlap (M : V'.Modules) : IsIso (ambientOverlap i f g M) := by
  dsimp only [ambientOverlap]
  infer_instance

/-- `Stacks.Pushout.targetOverlap` followed by the overlap comparison of Tag 08KU is
`Stacks.Pushout.ambientOverlap`. -/
theorem targetOverlap_comp_overlapComparison (M : V'.Modules) :
    targetOverlap i f g M ≫ ((overlapComparison i f g).app M).hom =
      ambientOverlap i f g M :=
  pullbackCongr_comp_overlapComparison i f g M

/-- The transpose of `a` along `q`, followed by the unit of `p^* ⊣ p_*` pushed forward along `q`,
is the transpose along `r = p ≫ q` of the two comparisons of pullbacks followed by `p^* a`. -/
private theorem unit_comp_pushforward_unit {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C)
    {r : A ⟶ C} (h : p ≫ q = r) (M : C.Modules) {G : B.Modules}
    (a : (Scheme.Modules.pullback q).obj M ⟶ G) :
    (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M ≫
        (Scheme.Modules.pushforward q).map a ≫
        (Functor.whiskerRight (Scheme.Modules.pullbackPushforwardAdjunction p).unit
            (Scheme.Modules.pushforward q) ≫
          Functor.whiskerLeft (Scheme.Modules.pullback p)
            ((Scheme.Modules.pushforwardComp p q).hom ≫
              (Scheme.Modules.pushforwardCongr h).hom)).app G =
      (Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M ≫
        (Scheme.Modules.pushforward r).map
          (((Scheme.Modules.pullbackCongr h).inv.app M ≫
              (Scheme.Modules.pullbackComp p q).inv.app M) ≫
            (Scheme.Modules.pullback p).map a) := by
  rw [NatTrans.naturality]
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.comp_map, Functor.comp_obj]
  simp only [Category.assoc]
  rw [unit_pushforward_congr_assoc p q h M, ← CategoryTheory.Functor.map_comp]
  rfl

/-- The transpose of `a` along the restriction to `V`, followed by
`Stacks.Pushout.targetUnitNat`, is the transpose along `U ⟶ V'` of `Stacks.Pushout.targetOverlap`
followed by the restriction of `a` to `U`. -/
@[reassoc]
theorem unit_comp_targetUnitNat (M : V'.Modules)
    {G : (pullback (pushout.inr i f) g).Modules}
    (a : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ⟶ G) :
    (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).unit.app M ≫
        (Scheme.Modules.pushforward (targetRestriction i f g)).map a ≫
        (targetUnitNat i f g).app G =
      (Scheme.Modules.pullbackPushforwardAdjunction (commonRestriction i f g)).unit.app M ≫
        (Scheme.Modules.pushforward (commonRestriction i f g)).map
          (targetOverlap i f g M ≫ (Scheme.Modules.pullback (commonToTarget i f g)).map a) := by
  exact unit_comp_pushforward_unit (commonToTarget i f g) (targetRestriction i f g)
    (commonToTarget_comp_restriction i f g) M _

/-- The transpose of `b` along the restriction to `U'`, followed by
`Stacks.Pushout.ambientUnitNat`, is the transpose along `U ⟶ V'` of
`Stacks.Pushout.ambientOverlap` followed by the restriction of `b` to `U`. -/
@[reassoc]
theorem unit_comp_ambientUnitNat (M : V'.Modules)
    {F : (pullback (pushout.inl i f) g).Modules}
    (b : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ⟶ F) :
    (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).unit.app M ≫
        (Scheme.Modules.pushforward (ambientRestriction i f g)).map b ≫
        (ambientUnitNat i f g).app F =
      (Scheme.Modules.pullbackPushforwardAdjunction (commonRestriction i f g)).unit.app M ≫
        (Scheme.Modules.pushforward (commonRestriction i f g)).map
          (ambientOverlap i f g M ≫
            (Scheme.Modules.pullback (commonToAmbient i f g)).map b) := by
  exact unit_comp_pushforward_unit (commonToAmbient i f g) (ambientRestriction i f g)
    (commonToAmbient_comp_restriction i f g) M _

/-- Two morphisms of triples with the same two components are equal. -/
theorem gluingTripleHom_ext {T T' : GluingTriple i f g} {φ ψ : T ⟶ T'}
    (ht : GluingTripleHom.target φ = GluingTripleHom.target ψ)
    (ha : GluingTripleHom.ambient φ = GluingTripleHom.ambient ψ) : φ = ψ := by
  change GluingTripleHom T T' at φ
  change GluingTripleHom T T' at ψ
  cases φ with
  | mk a b c =>
    cases ψ with
    | mk a' b' c' =>
      cases ht
      cases ha
      rfl

/-- The component of `Stacks.Pushout.glueTargetNat` at a triple. -/
theorem glueTargetNat_app (T : GluingTriple i f g) :
    (glueTargetNat i f g).app T =
      (targetUnitNat i f g).app T.target ≫
        (Scheme.Modules.pushforward (commonRestriction i f g)).map T.comparison.hom :=
  rfl

/-- The component of `Stacks.Pushout.glueAmbientNat` at a triple. -/
theorem glueAmbientNat_app (T : GluingTriple i f g) :
    (glueAmbientNat i f g).app T = (ambientUnitNat i f g).app T.ambient :=
  rfl

variable (hi : Stacks.Thickenings.IsThickening i) [IsAffineHom f]

omit [IsAffineHom f] in
/-- Two morphisms out of the restrictions of `M` to `V` and to `U'` agree on `U` through the
comparison of a triple if and only if their transposes agree after mapping into the pushforward of
the common restriction. -/
theorem homEquiv_glue_condition (M : V'.Modules) (T : GluingTriple i f g)
    (a : (Scheme.Modules.pullback (targetRestriction i f g)).obj M ⟶ T.target)
    (b : (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ⟶ T.ambient) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv
            M T.target a ≫ (glueTargetNat i f g).app T =
          (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv
            M T.ambient b ≫ (glueAmbientNat i f g).app T) ↔
      (Scheme.Modules.pullback (commonToTarget i f g)).map a ≫ T.comparison.hom =
        ((overlapComparison i f g).app M).hom ≫
          (Scheme.Modules.pullback (commonToAmbient i f g)).map b := by
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv
        M T.target a ≫ (glueTargetNat i f g).app T =
      (Scheme.Modules.pullbackPushforwardAdjunction (commonRestriction i f g)).homEquiv M _
        ((targetOverlap i f g M ≫
          (Scheme.Modules.pullback (commonToTarget i f g)).map a) ≫ T.comparison.hom) := by
    rw [CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Adjunction.homEquiv_unit,
      glueTargetNat_app, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    exact unit_comp_targetUnitNat_assoc i f g M a _
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv
        M T.ambient b ≫ (glueAmbientNat i f g).app T =
      (Scheme.Modules.pullbackPushforwardAdjunction (commonRestriction i f g)).homEquiv M _
        (ambientOverlap i f g M ≫
          (Scheme.Modules.pullback (commonToAmbient i f g)).map b) := by
    rw [CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Adjunction.homEquiv_unit,
      glueAmbientNat_app]
    exact unit_comp_ambientUnitNat i f g M b
  rw [h1, h2, Equiv.apply_eq_iff_eq, ← targetOverlap_comp_overlapComparison i f g M,
    Category.assoc, Category.assoc]
  have : Epi (targetOverlap i f g M) := IsIso.epi_of_iso _
  rw [cancel_epi]

/-- The transpose of the first projection of the glued module: a morphism from `M` into the glued
module of `T` restricts to a morphism on `V`. -/
noncomputable abbrev glueProjTarget (M : V'.Modules) (T : GluingTriple i f g)
    (h : M ⟶ pullback ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)) :
    (Scheme.Modules.pullback (targetRestriction i f g)).obj M ⟶ T.target :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv
    M T.target).symm (h ≫ pullback.fst _ _)

/-- The transpose of the second projection of the glued module: a morphism from `M` into the
glued module of `T` restricts to a morphism on `U'`. -/
noncomputable abbrev glueProjAmbient (M : V'.Modules) (T : GluingTriple i f g)
    (h : M ⟶ pullback ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)) :
    (Scheme.Modules.pullback (ambientRestriction i f g)).obj M ⟶ T.ambient :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv
    M T.ambient).symm (h ≫ pullback.snd _ _)

omit [IsAffineHom f] in
/-- The two transposed projections of the glued module agree on `U` through the comparison of the
triple. -/
theorem glueProj_comm (M : V'.Modules) (T : GluingTriple i f g)
    (h : M ⟶ pullback ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)) :
    (Scheme.Modules.pullback (commonToTarget i f g)).map (glueProjTarget i f g M T h) ≫
        T.comparison.hom =
      ((overlapComparison i f g).app M).hom ≫
        (Scheme.Modules.pullback (commonToAmbient i f g)).map
          (glueProjAmbient i f g M T h) :=
  (homEquiv_glue_condition i f g M T _ _).mp (by
    dsimp only [glueProjTarget, glueProjAmbient]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.assoc, Category.assoc,
      pullback.condition])

/-- A morphism of triples out of the comparison triple of `M` is the same thing as a morphism from
`M` into the glued module. -/
noncomputable def tripleHomEquiv (M : V'.Modules) (T : GluingTriple i f g) :
    ((baseChangeTripleFunctor i f hi g).obj M ⟶ T) ≃
      (M ⟶ pullback ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)) where
  toFun φ := pullback.lift
      ((Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv
        M T.target (GluingTripleHom.target φ))
      ((Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv
        M T.ambient (GluingTripleHom.ambient φ))
      ((homEquiv_glue_condition i f g M T (GluingTripleHom.target φ)
        (GluingTripleHom.ambient φ)).mpr (GluingTripleHom.comm φ))
  invFun h :=
    { target := glueProjTarget i f g M T h
      ambient := glueProjAmbient i f g M T h
      comm := glueProj_comm i f g M T h }
  left_inv φ := by
    refine gluingTripleHom_ext i f g ?_ ?_
    · dsimp only [glueProjTarget]
      rw [pullback.lift_fst]
      exact Equiv.symm_apply_apply _ _
    · dsimp only [glueProjAmbient]
      rw [pullback.lift_snd]
      exact Equiv.symm_apply_apply _ _
  right_inv h := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      exact Equiv.apply_symm_apply _ _
    · rw [pullback.lift_snd]
      exact Equiv.apply_symm_apply _ _

/-- The comparison functor of [Stacks Project, Tag 08KU] is left adjoint to the gluing functor,
with transposition `Stacks.Pushout.tripleHomEquiv`. -/
noncomputable def baseChangeTripleAdjunction :
    baseChangeTripleFunctor i f hi g ⊣ tripleGluingFunctor i f g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T ↦ tripleHomEquiv i f g hi M T
      homEquiv_naturality_left_symm := fun {M' M T} u h ↦ by
        refine gluingTripleHom_ext i f g ?_ ?_
        · change ((Scheme.Modules.pullbackPushforwardAdjunction
              (targetRestriction i f g)).homEquiv M' T.target).symm
                ((u ≫ h) ≫ pullback.fst _ _) =
              (Scheme.Modules.pullback (targetRestriction i f g)).map u ≫
                ((Scheme.Modules.pullbackPushforwardAdjunction
                  (targetRestriction i f g)).homEquiv M T.target).symm (h ≫ pullback.fst _ _)
          exact (congrArg (fun z ↦ ((Scheme.Modules.pullbackPushforwardAdjunction
              (targetRestriction i f g)).homEquiv M' T.target).symm z)
            (Category.assoc u h (pullback.fst ((glueTargetNat i f g).app T)
              ((glueAmbientNat i f g).app T)))).trans
            (CategoryTheory.Adjunction.homEquiv_naturality_left_symm _ u _)
        · change ((Scheme.Modules.pullbackPushforwardAdjunction
              (ambientRestriction i f g)).homEquiv M' T.ambient).symm
                ((u ≫ h) ≫ pullback.snd _ _) =
              (Scheme.Modules.pullback (ambientRestriction i f g)).map u ≫
                ((Scheme.Modules.pullbackPushforwardAdjunction
                  (ambientRestriction i f g)).homEquiv M T.ambient).symm (h ≫ pullback.snd _ _)
          exact (congrArg (fun z ↦ ((Scheme.Modules.pullbackPushforwardAdjunction
              (ambientRestriction i f g)).homEquiv M' T.ambient).symm z)
            (Category.assoc u h (pullback.snd ((glueTargetNat i f g).app T)
              ((glueAmbientNat i f g).app T)))).trans
            (CategoryTheory.Adjunction.homEquiv_naturality_left_symm _ u _)
      homEquiv_naturality_right := fun {M T T'} φ ψ ↦ by
        refine pullback.hom_ext ?_ ?_
        · calc (tripleHomEquiv i f g hi M T') (φ ≫ ψ) ≫
                  pullback.fst ((glueTargetNat i f g).app T') ((glueAmbientNat i f g).app T')
              = (Scheme.Modules.pullbackPushforwardAdjunction
                  (targetRestriction i f g)).homEquiv M T'.target
                    (GluingTripleHom.target (φ ≫ ψ)) := pullback.lift_fst _ _ _
            _ = (Scheme.Modules.pullbackPushforwardAdjunction
                  (targetRestriction i f g)).homEquiv M T.target
                    (GluingTripleHom.target φ) ≫
                  (Scheme.Modules.pushforward (targetRestriction i f g)).map
                    (GluingTripleHom.target ψ) :=
                (Scheme.Modules.pullbackPushforwardAdjunction
                  (targetRestriction i f g)).homEquiv_naturality_right _ _
            _ = ((tripleHomEquiv i f g hi M T) φ ≫
                  pullback.fst ((glueTargetNat i f g).app T)
                    ((glueAmbientNat i f g).app T)) ≫ (glueTargetFunctor i f g).map ψ :=
                congrArg (fun z ↦ z ≫ (glueTargetFunctor i f g).map ψ)
                  (pullback.lift_fst _ _ _).symm
            _ = (tripleHomEquiv i f g hi M T) φ ≫
                  (pullback.fst ((glueTargetNat i f g).app T)
                    ((glueAmbientNat i f g).app T) ≫ (glueTargetFunctor i f g).map ψ) :=
                Category.assoc _ _ _
            _ = (tripleHomEquiv i f g hi M T) φ ≫
                  ((tripleGluingFunctor i f g).map ψ ≫
                    pullback.fst ((glueTargetNat i f g).app T')
                      ((glueAmbientNat i f g).app T')) :=
                congrArg (fun z ↦ (tripleHomEquiv i f g hi M T) φ ≫ z)
                  (tripleGluingFunctor_map_fst i f g ψ).symm
            _ = _ := (Category.assoc _ _ _).symm
        · calc (tripleHomEquiv i f g hi M T') (φ ≫ ψ) ≫
                  pullback.snd ((glueTargetNat i f g).app T') ((glueAmbientNat i f g).app T')
              = (Scheme.Modules.pullbackPushforwardAdjunction
                  (ambientRestriction i f g)).homEquiv M T'.ambient
                    (GluingTripleHom.ambient (φ ≫ ψ)) := pullback.lift_snd _ _ _
            _ = (Scheme.Modules.pullbackPushforwardAdjunction
                  (ambientRestriction i f g)).homEquiv M T.ambient
                    (GluingTripleHom.ambient φ) ≫
                  (Scheme.Modules.pushforward (ambientRestriction i f g)).map
                    (GluingTripleHom.ambient ψ) :=
                (Scheme.Modules.pullbackPushforwardAdjunction
                  (ambientRestriction i f g)).homEquiv_naturality_right _ _
            _ = ((tripleHomEquiv i f g hi M T) φ ≫
                  pullback.snd ((glueTargetNat i f g).app T)
                    ((glueAmbientNat i f g).app T)) ≫ (glueAmbientFunctor i f g).map ψ :=
                congrArg (fun z ↦ z ≫ (glueAmbientFunctor i f g).map ψ)
                  (pullback.lift_snd _ _ _).symm
            _ = (tripleHomEquiv i f g hi M T) φ ≫
                  (pullback.snd ((glueTargetNat i f g).app T)
                    ((glueAmbientNat i f g).app T) ≫ (glueAmbientFunctor i f g).map ψ) :=
                Category.assoc _ _ _
            _ = (tripleHomEquiv i f g hi M T) φ ≫
                  ((tripleGluingFunctor i f g).map ψ ≫
                    pullback.snd ((glueTargetNat i f g).app T')
                      ((glueAmbientNat i f g).app T')) :=
                congrArg (fun z ↦ (tripleHomEquiv i f g hi M T) φ ≫ z)
                  (tripleGluingFunctor_map_snd i f g ψ).symm
            _ = _ := (Category.assoc _ _ _).symm }

omit [IsAffineHom f] in
/-- The transpose of the identity of a comparison triple, on the component over `V`, is the unit
of `(V ⟶ V')^* ⊣ (V ⟶ V')_*`. -/
private theorem homEquiv_id_target (M : V'.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv M
        ((Scheme.Modules.pullback (targetRestriction i f g)).obj M)
        (𝟙 ((Scheme.Modules.pullback (targetRestriction i f g)).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).unit.app M :=
  Adjunction.homEquiv_id _ M

omit [IsAffineHom f] in
/-- The transpose of the identity of a comparison triple, on the component over `U'`, is the unit
of `(U' ⟶ V')^* ⊣ (U' ⟶ V')_*`. -/
private theorem homEquiv_id_ambient (M : V'.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv M
        ((Scheme.Modules.pullback (ambientRestriction i f g)).obj M)
        (𝟙 ((Scheme.Modules.pullback (ambientRestriction i f g)).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).unit.app M :=
  Adjunction.homEquiv_id _ M

/-- The unit of `Stacks.Pushout.baseChangeTripleAdjunction` is `Stacks.Pushout.gluingUnitApp`. -/
theorem baseChangeTripleAdjunction_unit_app (M : V'.Modules) :
    (baseChangeTripleAdjunction i f g hi).unit.app M = gluingUnitApp i f g hi M := by
  have h : (baseChangeTripleAdjunction i f g hi).unit.app M =
      tripleHomEquiv i f g hi M ((baseChangeTripleFunctor i f hi g).obj M) (𝟙 _) :=
    CategoryTheory.Adjunction.mkOfHomEquiv_unit_app _ _
  rw [h]
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans
      ((homEquiv_id_target i f g M).trans (gluingUnitApp_fst i f g hi M).symm)
  · exact (pullback.lift_snd _ _ _).trans
      ((homEquiv_id_ambient i f g M).trans (gluingUnitApp_snd i f g hi M).symm)

/-- The component over `V` of the counit of `Stacks.Pushout.baseChangeTripleAdjunction` is the
transpose of the first projection of the glued module. -/
theorem baseChangeTripleAdjunction_counit_app_target (T : GluingTriple i f g) :
    GluingTripleHom.target ((baseChangeTripleAdjunction i f g hi).counit.app T) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (targetRestriction i f g)).homEquiv
        ((tripleGluingFunctor i f g).obj T) T.target).symm (pullback.fst _ _) := by
  have h : (baseChangeTripleAdjunction i f g hi).counit.app T =
      (tripleHomEquiv i f g hi ((tripleGluingFunctor i f g).obj T) T).symm (𝟙 _) :=
    CategoryTheory.Adjunction.mkOfHomEquiv_counit_app _ _
  rw [h]
  change glueProjTarget i f g _ T (𝟙 _) = _
  dsimp only [glueProjTarget]
  rw [Category.id_comp]
  rfl

/-- The component over `U'` of the counit of `Stacks.Pushout.baseChangeTripleAdjunction` is the
transpose of the second projection of the glued module. -/
theorem baseChangeTripleAdjunction_counit_app_ambient (T : GluingTriple i f g) :
    GluingTripleHom.ambient ((baseChangeTripleAdjunction i f g hi).counit.app T) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (ambientRestriction i f g)).homEquiv
        ((tripleGluingFunctor i f g).obj T) T.ambient).symm (pullback.snd _ _) := by
  have h : (baseChangeTripleAdjunction i f g hi).counit.app T =
      (tripleHomEquiv i f g hi ((tripleGluingFunctor i f g).obj T) T).symm (𝟙 _) :=
    CategoryTheory.Adjunction.mkOfHomEquiv_counit_app _ _
  rw [h]
  change glueProjAmbient i f g _ T (𝟙 _) = _
  dsimp only [glueProjAmbient]
  rw [Category.id_comp]
  rfl

end Stacks.Pushout

end
