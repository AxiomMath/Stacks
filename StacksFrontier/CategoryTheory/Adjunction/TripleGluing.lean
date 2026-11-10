module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Gluing along two restrictions with a common overlap

Let `𝒱'`, `𝒱`, `𝒰'`, `𝒰` be categories with "restriction" functors `pV : 𝒱' ⥤ 𝒱`,
`pA : 𝒱' ⥤ 𝒰'`, `pT : 𝒱 ⥤ 𝒰`, `pC : 𝒰' ⥤ 𝒰`, each with a right adjoint, and an isomorphism
`c : pV ⋙ pT ≅ pA ⋙ pC` of the two restrictions to the overlap. A *triple* is an object `G` of
`𝒱`, an object `F` of `𝒰'` and an isomorphism `pT G ≅ pC F`. Restricting an object of `𝒱'` gives a
triple (`CategoryTheory.TripleGluing.restrictFunctor`), and this functor has a right adjoint,
the fibre product `qV G ×_{qV qT pC F} qA F` (`CategoryTheory.TripleGluing.glueFunctor`), where
the two maps to the common target are the units composed with the comparison of the right
adjoints conjugate to `c`.

This is the formal half of Stacks 08KU / 08KV: modules on `V'` versus triples of modules on `V`
and `U'` glued along `U`, the restriction functors being pullbacks of modules and their right
adjoints pushforwards.

## References

* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TripleGluing

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒱' : Type u₁} [Category.{v₁} 𝒱'] {𝒱 : Type u₂} [Category.{v₂} 𝒱]
  {𝒰' : Type u₃} [Category.{v₃} 𝒰'] {𝒰 : Type u₄} [Category.{v₄} 𝒰]
  {pV : 𝒱' ⥤ 𝒱} {qV : 𝒱 ⥤ 𝒱'} (aV : pV ⊣ qV)
  {pA : 𝒱' ⥤ 𝒰'} {qA : 𝒰' ⥤ 𝒱'} (aA : pA ⊣ qA)
  {pT : 𝒱 ⥤ 𝒰} {qT : 𝒰 ⥤ 𝒱} (aT : pT ⊣ qT)
  {pC : 𝒰' ⥤ 𝒰} {qC : 𝒰 ⥤ 𝒰'} (aC : pC ⊣ qC)
  (c : pV ⋙ pT ≅ pA ⋙ pC)

variable (pT pC) in
/-- A triple: an object `G` of `𝒱`, an object `F` of `𝒰'`, and an isomorphism of their
restrictions to the overlap. -/
structure Triple where
  /-- The object of `𝒱`. -/
  target : 𝒱
  /-- The object of `𝒰'`. -/
  ambient : 𝒰'
  /-- The comparison on the overlap. -/
  comparison : pT.obj target ≅ pC.obj ambient

/-- A morphism of triples: two morphisms compatible with the comparisons. -/
@[ext]
structure TripleHom (A B : Triple pT pC) where
  /-- The morphism in `𝒱`. -/
  target : A.target ⟶ B.target
  /-- The morphism in `𝒰'`. -/
  ambient : A.ambient ⟶ B.ambient
  /-- Compatibility with the comparisons. -/
  comm : pT.map target ≫ B.comparison.hom = A.comparison.hom ≫ pC.map ambient

attribute [reassoc] TripleHom.comm

/-- Triples form a category, with composition and identities taken componentwise. -/
instance : Category (Triple pT pC) where
  Hom := TripleHom
  id A := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp φ ψ := ⟨φ.target ≫ ψ.target, φ.ambient ≫ ψ.ambient, by
    simp only [Functor.map_comp, Category.assoc, ψ.comm, φ.comm_assoc]⟩

/-- The `𝒱`-component of the identity of a triple is the identity. -/
@[simp] lemma id_target (A : Triple pT pC) : TripleHom.target (𝟙 A) = 𝟙 _ := rfl
/-- The `𝒰'`-component of the identity of a triple is the identity. -/
@[simp] lemma id_ambient (A : Triple pT pC) : TripleHom.ambient (𝟙 A) = 𝟙 _ := rfl
/-- The `𝒱`-component of a composite of morphisms of triples is the composite of the
`𝒱`-components. -/
@[simp] lemma comp_target {A B D : Triple pT pC} (φ : A ⟶ B) (ψ : B ⟶ D) :
    TripleHom.target (φ ≫ ψ) = φ.target ≫ ψ.target := rfl
/-- The `𝒰'`-component of a composite of morphisms of triples is the composite of the
`𝒰'`-components. -/
@[simp] lemma comp_ambient {A B D : Triple pT pC} (φ : A ⟶ B) (ψ : B ⟶ D) :
    TripleHom.ambient (φ ≫ ψ) = φ.ambient ≫ ψ.ambient := rfl

/-- Two morphisms of triples are equal when their `𝒱`- and `𝒰'`-components are. -/
@[ext]
lemma hom_ext {A B : Triple pT pC} {φ ψ : A ⟶ B} (h₁ : φ.target = ψ.target)
    (h₂ : φ.ambient = ψ.ambient) : φ = ψ := TripleHom.ext h₁ h₂

/-- A morphism of triples is an isomorphism as soon as both its components are. -/
lemma isIso_of_isIso_components {A B : Triple pT pC} (φ : A ⟶ B) [IsIso φ.target]
    [IsIso φ.ambient] : IsIso φ :=
  ⟨⟨inv φ.target, inv φ.ambient, by
      rw [← cancel_mono (pC.map φ.ambient), Category.assoc, Category.assoc, ← φ.comm,
        ← pT.map_comp_assoc, IsIso.inv_hom_id, pT.map_id, Category.id_comp, ← pC.map_comp,
        IsIso.inv_hom_id, pC.map_id, Category.comp_id]⟩,
    by ext <;> simp, by ext <;> simp⟩

/-- **The restriction functor**: an object of `𝒱'` goes to its two restrictions and the
comparison `c` on the overlap. -/
@[simps]
def restrictFunctor : 𝒱' ⥤ Triple pT pC where
  obj M := ⟨pV.obj M, pA.obj M, c.app M⟩
  map φ := ⟨pV.map φ, pA.map φ, c.hom.naturality φ⟩

/-- The comparison of the two composite right adjoints, conjugate to `c`. -/
noncomputable def rightComparison : qC ⋙ qA ≅ qT ⋙ qV :=
  conjugateIsoEquiv (aA.comp aC) (aV.comp aT) c

variable {Q : 𝒰 ⥤ 𝒱'} (ε : qT ⋙ qV ≅ Q)

variable {aV aA c} in
/-- The map from the pushed-forward target into the common pushforward `Q`, a functor
identified with `qT ⋙ qV` by `ε`. -/
noncomputable def targetMap (T : Triple pT pC) :
    qV.obj T.target ⟶ Q.obj (pC.obj T.ambient) :=
  qV.map (aT.unit.app T.target ≫ qT.map T.comparison.hom) ≫ ε.hom.app (pC.obj T.ambient)

variable {aV aA aT c ε} in
/-- The map from the pushed-forward ambient object into the common pushforward `Q`, through a
comparison `s : qC ⋙ qA ⟶ Q` (in practice the conjugate of `c` followed by `ε`, see
`CategoryTheory.TripleGluing.rightComparison`). -/
noncomputable def ambientMap (s : qC ⋙ qA ⟶ Q) (T : Triple pT pC) :
    qA.obj T.ambient ⟶ Q.obj (pC.obj T.ambient) :=
  qA.map (aC.unit.app T.ambient) ≫ s.app (pC.obj T.ambient)

variable [HasPullbacks 𝒱'] (s : qC ⋙ qA ⟶ Q)

/-- **The gluing functor**, the fibre product `qV G ×_{Q (pC F)} qA F`. -/
noncomputable abbrev glueFunctor : Triple pT pC ⥤ 𝒱' where
  obj T := pullback (targetMap aT ε T) (ambientMap (aC := aC) s T)
  map {T T'} φ := pullback.map _ _ _ _ (qV.map φ.target) (qA.map φ.ambient)
    (Q.map (pC.map φ.ambient))
    (by
      simp only [targetMap, Category.assoc]
      rw [← ε.hom.naturality, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [Functor.comp_map, ← qV.map_comp, Category.assoc, ← qT.map_comp]
      congr 1
      rw [← φ.comm, qT.map_comp, aT.unit_naturality_assoc])
    (by
      simp only [ambientMap, Category.assoc]
      rw [← qA.map_comp_assoc, ← aC.unit_naturality]
      simp only [qA.map_comp, Category.assoc]
      congr 1
      exact (s.naturality (pC.map φ.ambient)).symm)
  map_id T := by
    refine pullback.hom_ext (f := targetMap aT ε T) (g := ambientMap (aC := aC) s T) ?_ ?_ <;>
      simp
  map_comp {T₁ T₂ T₃} φ ψ := by
    refine pullback.hom_ext (f := targetMap aT ε T₃) (g := ambientMap (aC := aC) s T₃) ?_ ?_
    · simp only [comp_target, Functor.map_comp, pullback.lift_fst, Category.assoc,
        pullback.lift_fst_assoc]
    · simp only [comp_ambient, Functor.map_comp, pullback.lift_snd, Category.assoc,
        pullback.lift_snd_assoc]

/-- The first projection of the glued object of a triple. -/
noncomputable abbrev glueFst (T : Triple pT pC) :
    (glueFunctor aT aC ε s).obj T ⟶ qV.obj T.target :=
  pullback.fst _ _

/-- The second projection of the glued object of a triple. -/
noncomputable abbrev glueSnd (T : Triple pT pC) :
    (glueFunctor aT aC ε s).obj T ⟶ qA.obj T.ambient :=
  pullback.snd _ _

/-- The glued object of a triple is the fibre product of its two maps to the common target. -/
lemma isPullback_glue (T : Triple pT pC) :
    IsPullback (glueFst aT aC ε s T) (glueSnd aT aC ε s T) (targetMap aT ε T)
      (ambientMap (aC := aC) s T) :=
  IsPullback.of_hasPullback _ _

/-- The image under `glueFunctor` of a morphism of triples, followed by the first projection,
is the first projection followed by `qV` applied to the `𝒱`-component. -/
@[reassoc (attr := simp)]
lemma glueFunctor_map_fst {T T' : Triple pT pC} (φ : T ⟶ T') :
    (glueFunctor aT aC ε s).map φ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ qV.map φ.target :=
  pullback.lift_fst _ _ _

/-- The image under `glueFunctor` of a morphism of triples, followed by the second projection,
is the second projection followed by `qA` applied to the `𝒰'`-component. -/
@[reassoc (attr := simp)]
lemma glueFunctor_map_snd {T T' : Triple pT pC} (φ : T ⟶ T') :
    (glueFunctor aT aC ε s).map φ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ qA.map φ.ambient :=
  pullback.lift_snd _ _ _

omit [HasPullbacks 𝒱'] in
/-- The defining property of the conjugate comparison, on transposes. -/
lemma homEquiv_comp_rightComparison {M : 𝒱'} {E : 𝒰} (y : pC.obj (pA.obj M) ⟶ E) :
    (aV.comp aT).homEquiv M E (c.hom.app M ≫ y) =
      (aA.comp aC).homEquiv M E y ≫ (rightComparison aV aA aT aC c).hom.app E := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (rightComparison aV aA aT aC c).hom.naturality, ← Category.assoc]
  have := unit_conjugateEquiv (aA.comp aC) (aV.comp aT) c.hom M
  simp only [rightComparison, conjugateIsoEquiv_apply_hom] at this ⊢
  rw [this, Category.assoc, ← Functor.map_comp]

omit [HasPullbacks 𝒱'] in
/-- The transpose of `α : pV M ⟶ G` under `aV`, followed by `targetMap`, is the transpose of
`pT α` composed with the comparison under `aV.comp aT`, followed by `ε`. -/
lemma homEquiv_targetMap {M : 𝒱'} (T : Triple pT pC) (α : pV.obj M ⟶ T.target) :
    aV.homEquiv M T.target α ≫ targetMap aT ε T =
      (aV.comp aT).homEquiv M _ (pT.map α ≫ T.comparison.hom) ≫ ε.hom.app _ := by
  simp only [targetMap, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.assoc,
    ← qV.map_comp_assoc, Functor.comp_map, qT.map_comp]
  congr 2
  rw [← Category.assoc, ← aT.unit_naturality, Category.assoc]

omit [HasPullbacks 𝒱'] in
/-- The transpose of `β : pA M ⟶ F` under `aA`, followed by `ambientMap`, is the transpose of
`pC β` under `aA.comp aC`, followed by `s`. -/
lemma homEquiv_ambientMap {M : 𝒱'} (T : Triple pT pC) (β : pA.obj M ⟶ T.ambient) :
    aA.homEquiv M T.ambient β ≫ ambientMap (aC := aC) s T =
      (aA.comp aC).homEquiv M _ (pC.map β) ≫ s.app (pC.obj T.ambient) := by
  simp only [ambientMap, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.assoc,
    ← qA.map_comp_assoc, Functor.comp_map]
  congr 2
  exact congrArg qA.map (aC.unit_naturality β).symm

variable {s} (hs : s = (rightComparison aV aA aT aC c).hom ≫ ε.hom)
include hs

/-- The transposition of morphisms of triples out of a restriction. -/
noncomputable def homEquiv (M : 𝒱') (T : Triple pT pC) :
    ((restrictFunctor c).obj M ⟶ T) ≃
      (M ⟶ pullback (targetMap aT ε T) (ambientMap (aC := aC) s T)) where
  toFun φ := pullback.lift (aV.homEquiv _ _ φ.target) (aA.homEquiv _ _ φ.ambient) (by
    have h1 := homEquiv_targetMap aV aT ε T φ.target
    have h2 := homEquiv_ambientMap aA aC s T φ.ambient
    have h3 := homEquiv_comp_rightComparison aV aA aT aC c (M := M) (pC.map φ.ambient)
    have hc : pT.map φ.target ≫ T.comparison.hom = c.hom.app M ≫ pC.map φ.ambient := φ.comm
    have hsapp : s.app (pC.obj T.ambient) =
        (rightComparison aV aA aT aC c).hom.app (pC.obj T.ambient) ≫
          ε.hom.app (pC.obj T.ambient) := by
      rw [hs, NatTrans.comp_app]
    calc aV.homEquiv _ _ φ.target ≫ targetMap aT ε T
        = (aV.comp aT).homEquiv M _ (pT.map φ.target ≫ T.comparison.hom) ≫
            ε.hom.app (pC.obj T.ambient) := h1
      _ = (aV.comp aT).homEquiv M _ (c.hom.app M ≫ pC.map φ.ambient) ≫
            ε.hom.app (pC.obj T.ambient) :=
          congrArg (fun z => (aV.comp aT).homEquiv M _ z ≫ ε.hom.app (pC.obj T.ambient)) hc
      _ = (aA.comp aC).homEquiv M _ (pC.map φ.ambient) ≫
            (rightComparison aV aA aT aC c).hom.app (pC.obj T.ambient) ≫
              ε.hom.app (pC.obj T.ambient) := by rw [h3, Category.assoc]
      _ = aA.homEquiv _ _ φ.ambient ≫ ambientMap (aC := aC) s T := by rw [h2, hsapp])
  invFun m :=
    { target := (aV.homEquiv _ _).symm (m ≫ pullback.fst _ _)
      ambient := (aA.homEquiv _ _).symm (m ≫ pullback.snd _ _)
      comm := by
        apply ((aV.comp aT).homEquiv _ _).injective
        refine (cancel_mono (ε.hom.app (pC.obj T.ambient))).1 ?_
        have h1 := homEquiv_targetMap aV aT ε T ((aV.homEquiv _ _).symm (m ≫ pullback.fst _ _))
        have h2 := homEquiv_ambientMap aA aC s T
          ((aA.homEquiv _ _).symm (m ≫ pullback.snd _ _))
        have h3 := homEquiv_comp_rightComparison aV aA aT aC c (M := M)
          (pC.map ((aA.homEquiv _ _).symm (m ≫ pullback.snd (targetMap aT ε T)
            (ambientMap (aC := aC) s T))))
        rw [Equiv.apply_symm_apply] at h1 h2
        have h4 : (m ≫ pullback.fst (targetMap aT ε T) (ambientMap (aC := aC) s T)) ≫
            targetMap aT ε T = (m ≫ pullback.snd (targetMap aT ε T)
              (ambientMap (aC := aC) s T)) ≫ ambientMap (aC := aC) s T := by
          rw [Category.assoc, Category.assoc, pullback.condition]
        have hsapp : s.app (pC.obj T.ambient) =
            (rightComparison aV aA aT aC c).hom.app (pC.obj T.ambient) ≫
              ε.hom.app (pC.obj T.ambient) := by
          rw [hs, NatTrans.comp_app]
        refine h1.symm.trans (h4.trans (h2.trans ?_))
        rw [hsapp, ← Category.assoc]
        exact congrArg (· ≫ ε.hom.app (pC.obj T.ambient)) h3.symm }
  left_inv φ := by
    ext
    · simp only [pullback.lift_fst]
      exact (aV.homEquiv M T.target).symm_apply_apply φ.target
    · simp only [pullback.lift_snd]
      exact (aA.homEquiv M T.ambient).symm_apply_apply φ.ambient
  right_inv m := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Equiv.apply_symm_apply]
    · simp only [pullback.lift_snd, Equiv.apply_symm_apply]

/-- The first projection of the transpose of a morphism of triples is the transpose under `aV`
of its `𝒱`-component. -/
@[simp] lemma homEquiv_apply_fst (M : 𝒱') (T : Triple pT pC)
    (φ : (restrictFunctor c).obj M ⟶ T) :
    homEquiv aV aA aT aC c ε hs M T φ ≫ pullback.fst _ _ = aV.homEquiv _ _ φ.target :=
  pullback.lift_fst _ _ _

/-- The second projection of the transpose of a morphism of triples is the transpose under
`aA` of its `𝒰'`-component. -/
@[simp] lemma homEquiv_apply_snd (M : 𝒱') (T : Triple pT pC)
    (φ : (restrictFunctor c).obj M ⟶ T) :
    homEquiv aV aA aT aC c ε hs M T φ ≫ pullback.snd _ _ = aA.homEquiv _ _ φ.ambient :=
  pullback.lift_snd _ _ _

/-- The `𝒱`-component of the inverse transpose of `m` is the inverse transpose under `aV` of
its first projection. -/
@[simp] lemma homEquiv_symm_apply_target (M : 𝒱') (T : Triple pT pC)
    (m : M ⟶ pullback (targetMap aT ε T) (ambientMap (aC := aC) s T)) :
    ((homEquiv aV aA aT aC c ε hs M T).symm m).target =
      (aV.homEquiv _ _).symm (m ≫ pullback.fst _ _) :=
  rfl

/-- The `𝒰'`-component of the inverse transpose of `m` is the inverse transpose under `aA` of
its second projection. -/
@[simp] lemma homEquiv_symm_apply_ambient (M : 𝒱') (T : Triple pT pC)
    (m : M ⟶ pullback (targetMap aT ε T) (ambientMap (aC := aC) s T)) :
    ((homEquiv aV aA aT aC c ε hs M T).symm m).ambient =
      (aA.homEquiv _ _).symm (m ≫ pullback.snd _ _) :=
  rfl

/-- **The gluing functor is right adjoint to restriction.** -/
noncomputable def adjunction : restrictFunctor c ⊣ glueFunctor aT aC ε s :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv aV aA aT aC c ε hs
      homEquiv_naturality_left_symm := by
        intro M M' T f g
        ext
        · change (aV.homEquiv _ _).symm ((f ≫ g) ≫ pullback.fst _ _) =
            pV.map f ≫ (aV.homEquiv _ _).symm (g ≫ pullback.fst _ _)
          exact (congrArg (aV.homEquiv _ _).symm (Category.assoc _ _ _)).trans
            (aV.homEquiv_naturality_left_symm _ _)
        · change (aA.homEquiv _ _).symm ((f ≫ g) ≫ pullback.snd _ _) =
            pA.map f ≫ (aA.homEquiv _ _).symm (g ≫ pullback.snd _ _)
          exact (congrArg (aA.homEquiv _ _).symm (Category.assoc _ _ _)).trans
            (aA.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right := by
        intro M T T' φ ψ
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, glueFunctor_map_fst, homEquiv_apply_fst, ← Category.assoc,
            homEquiv_apply_fst, comp_target]
          exact aV.homEquiv_naturality_right _ _
        · rw [Category.assoc, glueFunctor_map_snd, homEquiv_apply_snd, ← Category.assoc,
            homEquiv_apply_snd, comp_ambient]
          exact aA.homEquiv_naturality_right _ _ }

/-- The unit of `adjunction` followed by the first projection is the unit of `aV`. -/
@[reassoc (attr := simp)]
lemma adjunction_unit_app_fst (M : 𝒱') :
    (adjunction aV aA aT aC c ε hs).unit.app M ≫ pullback.fst _ _ = aV.unit.app M := by
  change homEquiv aV aA aT aC c ε hs M _ (𝟙 _) ≫ pullback.fst _ _ = _
  rw [homEquiv_apply_fst]
  exact aV.homEquiv_id M

/-- The unit of `adjunction` followed by the second projection is the unit of `aA`. -/
@[reassoc (attr := simp)]
lemma adjunction_unit_app_snd (M : 𝒱') :
    (adjunction aV aA aT aC c ε hs).unit.app M ≫ pullback.snd _ _ = aA.unit.app M := by
  change homEquiv aV aA aT aC c ε hs M _ (𝟙 _) ≫ pullback.snd _ _ = _
  rw [homEquiv_apply_snd]
  exact aA.homEquiv_id M

/-- The `𝒱`-component of the counit of `adjunction` is `pV` of the first projection followed
by the counit of `aV`. -/
@[simp]
lemma adjunction_counit_app_target (T : Triple pT pC) :
    ((adjunction aV aA aT aC c ε hs).counit.app T).target =
      pV.map (pullback.fst _ _) ≫ aV.counit.app T.target := by
  change ((homEquiv aV aA aT aC c ε hs _ T).symm (𝟙 _)).target = _
  rw [homEquiv_symm_apply_target, Category.id_comp]
  exact aV.homEquiv_counit _ _ _

/-- The `𝒰'`-component of the counit of `adjunction` is `pA` of the second projection
followed by the counit of `aA`. -/
@[simp]
lemma adjunction_counit_app_ambient (T : Triple pT pC) :
    ((adjunction aV aA aT aC c ε hs).counit.app T).ambient =
      pA.map (pullback.snd _ _) ≫ aA.counit.app T.ambient := by
  change ((homEquiv aV aA aT aC c ε hs _ T).symm (𝟙 _)).ambient = _
  rw [homEquiv_symm_apply_ambient, Category.id_comp]
  exact aA.homEquiv_counit _ _ _

end CategoryTheory.TripleGluing

end
