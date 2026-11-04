module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence
public import StacksFrontier.Deformation.FormalObject.Unit

/-!
# Hom categories and completion (Stacks 06HA)

Completion of a category cofibered in groupoids is left adjoint, on hom categories,
to restriction from complete local algebras to Artinian local algebras.  This file sets up
the two functors between the hom categories and reduces the equivalence to a pair of
comparison isomorphisms; those are built in
`StacksFrontier.Deformation.FormalObject.HomEquivalenceUnit` and
`StacksFrontier.Deformation.FormalObject.HomEquivalenceCounit`, and assembled in
`StacksFrontier.Deformation.FormalObject.HomEquivalenceMain`.

## Main definitions

* `unitBasedFunctor`: the unit of Tag 06HA, viewed as a functor over the category of
  complete local algebras.
* `completionHomForward`: a morphism out of a restricted cofibered category is sent to the
  unit followed by the completion of that morphism.
* `completionHomInverse`: a morphism into a completion is sent to its restriction along the
  inclusion of Artinian local algebras, followed by the comparison functor of Tag 06SJ.
* `CompletionHomEquivalence` records the equivalence of hom categories, including the
  canonical formulas for both directions.

## Main results

* `completionHomEquivalenceOfIsos`: a natural isomorphism `𝟭 ≅ Φ ⋙ Ψ` together with one
  `Ψ ⋙ Φ ≅ 𝟭` assembles `completionHomForward` and `completionHomInverse` into the
  equivalence of hom categories of **Stacks 06HA**, with every canonical formula holding
  on the nose.

## References

* [Stacks Project, Tag 06HA](https://stacks.math.columbia.edu/tag/06HA)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

/-- The unit, viewed as a functor over the category of complete local algebras. -/
public noncomputable def unitBasedFunctor
    (hq : IsCofiberedInGroupoids q) :
    BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor
        (FormalObject.projection (p := Restriction.projection (p := q)))) where
  toFunctor := (completionUnit q hq).functor
  w := (completionUnit q hq).comp_projection

/-- Pull back a morphism into the completion along the inclusion of Artinian algebras. -/
public noncomputable def restrictedPullbackMap
    (hp : IsCofiberedInGroupoids p)
    (ψ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))) :
    Restriction q ⥤
      CategoricalPullback (restrictionCompletionEquivalence p hp).inclusion
        (FormalObject.projection (p := p)) where
  obj X :=
    { fst := X.base
      snd := ψ.obj X.obj
      iso := eqToIso (X.obj_eq.symm.trans (ψ.w_obj X.obj).symm) }
  map {X Y} f :=
    { fst := f.base
      snd := ψ.map f.obj
      w := by
        have hwX : (ψ.obj X.obj).base = q.obj X.obj := ψ.w_obj X.obj
        have hwY : (ψ.obj Y.obj).base = q.obj Y.obj := ψ.w_obj Y.obj
        have key : artinianToComplete.map f.base =
            eqToHom X.obj_eq.symm ≫ q.map f.obj ≫ eqToHom Y.obj_eq := by
          rw [← f.comm]; simp
        have hpsi : (ψ.map f.obj).base =
            eqToHom hwX ≫ q.map f.obj ≫ eqToHom hwY.symm :=
          Functor.congr_hom ψ.w f.obj
        change artinianToComplete.map f.base ≫
            eqToHom (Y.obj_eq.symm.trans hwY.symm) =
          eqToHom (X.obj_eq.symm.trans hwX.symm) ≫ (ψ.map f.obj).base
        rw [hpsi, key]
        simp [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] }
  map_id X := CategoricalPullback.hom_ext rfl (ψ.map_id X.obj)
  map_comp f g := CategoricalPullback.hom_ext rfl (ψ.map_comp f.obj g.obj)

/-- The restriction of a morphism into the completion, as a functor over the category of
Artinian local algebras. -/
public noncomputable def restrictedPullbackBasedFunctor
    (hp : IsCofiberedInGroupoids p)
    (ψ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))) :
    BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor
        (CategoricalPullback.π₁ (restrictionCompletionEquivalence p hp).inclusion
          (FormalObject.projection (p := p)))) where
  toFunctor := restrictedPullbackMap p q hp ψ
  w := rfl

/-- The comparison functor of Tag 06SJ, as a functor over the category of Artinian local
algebras. -/
public noncomputable def canBasedFunctor (hp : IsCofiberedInGroupoids p) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (CategoricalPullback.π₁ (restrictionCompletionEquivalence p hp).inclusion
          (FormalObject.projection (p := p))))
      (BasedCategory.ofFunctor p) where
  toFunctor := (restrictionCompletionEquivalence p hp).can
  w := restrictionCompletionEquivalence_can_comp_eq p hp

/-- The base map of a component of a based natural transformation is the transport
along the two displayed equalities. -/
public theorem basedNatTrans_app_over {𝒮 : Type*} [Category 𝒮]
    {𝒳 𝒴 : BasedCategory 𝒮} {A B : 𝒳 ⥤ᵇ 𝒴} (t : A ⟶ B) (a : 𝒳.obj) :
    𝒴.p.map (t.toNatTrans.app a) =
      eqToHom (A.w_obj a) ≫ eqToHom (B.w_obj a).symm := by
  have := t.isHomLift' a
  simpa using IsHomLift.fac' 𝒴.p (𝟙 (𝒳.p.obj a)) (t.toNatTrans.app a)

/-- On a two-morphism, restriction along the inclusion of Artinian algebras acts by the
identity on the Artinian base and by the given transformation upstairs. -/
public noncomputable def restrictedPullbackNatTrans
    (hp : IsCofiberedInGroupoids p)
    {ψ χ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))} (t : ψ ⟶ χ) :
    restrictedPullbackBasedFunctor p q hp ψ ⟶ restrictedPullbackBasedFunctor p q hp χ where
  toNatTrans :=
    { app := fun X =>
        { fst := 𝟙 X.base
          snd := t.toNatTrans.app X.obj
          w := by
            have hwψ : (ψ.obj X.obj).base = q.obj X.obj := ψ.w_obj X.obj
            have hwχ : (χ.obj X.obj).base = q.obj X.obj := χ.w_obj X.obj
            have hbase : (t.toNatTrans.app X.obj).base =
                eqToHom hwψ ≫ eqToHom hwχ.symm := basedNatTrans_app_over t X.obj
            change artinianToComplete.map (𝟙 X.base) ≫
                eqToHom (X.obj_eq.symm.trans hwχ.symm) =
              eqToHom (X.obj_eq.symm.trans hwψ.symm) ≫ (t.toNatTrans.app X.obj).base
            rw [hbase]
            simp [eqToHom_trans] }
      naturality := fun X Y f => by
        apply CategoricalPullback.hom_ext
        · change f.base ≫ 𝟙 Y.base = 𝟙 X.base ≫ f.base
          simp
        · change ψ.map f.obj ≫ t.toNatTrans.app Y.obj =
            t.toNatTrans.app X.obj ≫ χ.map f.obj
          exact t.toNatTrans.naturality f.obj }
  isHomLift' := fun X => by
    refine IsHomLift.of_fac'
      (p := CategoricalPullback.π₁ (restrictionCompletionEquivalence p hp).inclusion
        (FormalObject.projection (p := p))) _ _ rfl rfl ?_
    simp only [Category.id_comp]
    rfl

/-- The Artinian component of a restricted two-morphism is the identity. -/
@[simp]
public theorem restrictedPullbackNatTrans_app_fst (hp : IsCofiberedInGroupoids p)
    {ψ χ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))} (t : ψ ⟶ χ)
    (X : Restriction q) :
    ((restrictedPullbackNatTrans p q hp t).toNatTrans.app X).fst = 𝟙 X.base := rfl

/-- The formal-object component of a restricted two-morphism is the original one. -/
@[simp]
public theorem restrictedPullbackNatTrans_app_snd (hp : IsCofiberedInGroupoids p)
    {ψ χ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))} (t : ψ ⟶ χ)
    (X : Restriction q) :
    ((restrictedPullbackNatTrans p q hp t).toNatTrans.app X).snd =
      t.toNatTrans.app X.obj := rfl

/-- Restriction of two-morphisms preserves identities. -/
public theorem restrictedPullbackNatTrans_id (hp : IsCofiberedInGroupoids p)
    (ψ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))) :
    restrictedPullbackNatTrans p q hp (𝟙 ψ) =
      𝟙 (restrictedPullbackBasedFunctor p q hp ψ) := by
  ext X
  rfl

/-- Restriction of two-morphisms preserves composition. -/
public theorem restrictedPullbackNatTrans_comp (hp : IsCofiberedInGroupoids p)
    {ψ χ ω : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))}
    (t : ψ ⟶ χ) (s : χ ⟶ ω) :
    restrictedPullbackNatTrans p q hp (t ≫ s) =
      restrictedPullbackNatTrans p q hp t ≫ restrictedPullbackNatTrans p q hp s := by
  ext X
  exact CategoricalPullback.hom_ext (Category.id_comp _).symm rfl

/-- Restriction followed by the comparison of Tag 06SJ, as a functor on hom categories. -/
public noncomputable def completionHomInverse (hp : IsCofiberedInGroupoids p) :
    BasedFunctor (BasedCategory.ofFunctor q)
        (BasedCategory.ofFunctor (FormalObject.projection (p := p))) ⥤
      BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
        (BasedCategory.ofFunctor p) where
  obj ψ := (restrictedPullbackBasedFunctor p q hp ψ).comp (canBasedFunctor p hp)
  map t := BasedCategory.whiskerRight (restrictedPullbackNatTrans p q hp t)
    (canBasedFunctor p hp)
  map_id ψ := by
    rw [restrictedPullbackNatTrans_id]
    ext X
    exact (restrictionCompletionEquivalence p hp).can.map_id _
  map_comp t s := by
    rw [restrictedPullbackNatTrans_comp]
    ext X
    exact (restrictionCompletionEquivalence p hp).can.map_comp _ _

end

/-! ### Functoriality of completion on two-morphisms -/

section
open CategoryTheory

universe u v w uA vA uB vB

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
variable {a : A ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
  {b : B ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Transporting a composite along equalities of its endpoints may be split as a composite of
the two transported factors, inserting a cancelling pair of `eqToHom`s in the middle. -/
private theorem eqToHom_comp_split {C : Type*} [Category C] {a₀ a₁ b₀ b₁ c₀ c₁ : C}
    (h₁ : a₀ = a₁) (h₂ : b₀ = b₁) (h₃ : c₁ = c₀) (f : a₁ ⟶ b₁) (g : b₁ ⟶ c₁) :
    eqToHom h₁ ≫ (f ≫ g) ≫ eqToHom h₃ =
      (eqToHom h₁ ≫ f ≫ eqToHom h₂.symm) ≫ eqToHom h₂ ≫ g ≫ eqToHom h₃ := by
  subst h₁; subst h₂; subst h₃; simp

/-- Transporting an endomorphism that is the identity along an equality of objects gives the
identity.  The hypothesis `hf` is kept separate so that the caller can discharge it by `rfl`,
which sees through `BasedCategory.ofFunctor` where `simp` does not. -/
private theorem eqToHom_comp_cancel {C : Type*} [Category C] {x y : C} (h : x = y)
    (f : y ⟶ y) (hf : f = 𝟙 y) :
    eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 x := by
  subst h; rw [hf]; simp

/-- A morphism equals the transport of a heterogeneously equal one along equalities of the
endpoints.  The hypothesis is an `HEq`, so the caller discharges it by `HEq.refl`, whose
unification sees through `BasedCategory.ofFunctor`; `simp` does not. -/
private theorem eq_eqToHom_comp_comp {C : Type*} [Category C] {x y z w : C}
    (h₁ : x = y) (h₂ : z = w) {f : x ⟶ w} {g : y ⟶ z} (hfg : HEq f g) :
    f = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by
  cases h₁; cases h₂; simpa using eq_of_heq hfg

/-- Cancel endomorphisms that are definitionally the identity on either side of an equation.
The two identity hypotheses are kept separate so that the caller can discharge them by `rfl`. -/
private theorem comp_eq_comp_of_id {C : Type*} [Category C] {x y : C} {f g : x ⟶ y}
    {e₁ : y ⟶ y} {e₂ : x ⟶ x} (he₁ : e₁ = 𝟙 y) (he₂ : e₂ = 𝟙 x) (h : f = g) :
    f ≫ e₁ = e₂ ≫ g := by
  subst he₁; subst he₂; subst h; simp

/-- Two composable transports agree with the transport along the composite equality, stated
with the composite proof as a separate argument so that the endpoints are supplied by the
caller rather than matched by `simp`. -/
private theorem eqToHom_trans_eq {C : Type*} [Category C] {x y z : C} (h₁ : x = y) (h₂ : y = z)
    (h₃ : x = z) : eqToHom h₁ ≫ eqToHom h₂ = eqToHom h₃ := by
  cases h₁; cases h₂; simp

/-- The image under a functor of an endomorphism that is definitionally the identity may be
cancelled from a composite. -/
private theorem map_id_comp {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {x : C} {e : x ⟶ x} (he : e = 𝟙 x) {w : D} (r : P.obj x ⟶ w) :
    P.map e ≫ r = r := by
  subst he; simp

/-- The level-`n` component of the identity two-morphism of a completed functor is the
identity.  Stated as a lemma because the objects of the completion are reached through
`BasedCategory.ofFunctor`, which `simp` and `rfl` do not unfold. -/
private theorem completionMap_id_app_level
    (φ : BasedFunctor (BasedCategory.ofFunctor a) (BasedCategory.ofFunctor b))
    (X : FormalObject a) (n : ℕ) :
    ((𝟙 (completionMap φ) : completionMap φ ⟶ completionMap φ).toNatTrans.app X).app n =
      𝟙 (((completionMap φ).obj X).level n) :=
  rfl

end

/-! ### The forward direction -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

/-- The unit followed by completion of a morphism: the forward direction of Tag 06HA. -/
public noncomputable def completionHomForward (hq : IsCofiberedInGroupoids q) :
    BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
        (BasedCategory.ofFunctor p) ⥤
      BasedFunctor (BasedCategory.ofFunctor q)
        (BasedCategory.ofFunctor (FormalObject.projection (p := p))) where
  obj φ := (unitBasedFunctor q hq).comp (completionMap φ)
  map t := BasedCategory.whiskerLeft (unitBasedFunctor q hq) (completionNatTrans t)
  map_id φ := by
    rw [completionNatTrans_id]
    apply BasedNatTrans.homCategory.ext
    apply NatTrans.ext
    funext X
    rfl
  map_comp t s := by
    rw [completionNatTrans_comp]
    apply BasedNatTrans.homCategory.ext
    apply NatTrans.ext
    funext X
    rfl

/-- An equivalence between morphisms out of a restricted cofibered category and
morphisms into the completion. The forward formula is the unit followed by
completion of a morphism. The inverse formula is restriction followed by the
canonical comparison of Tag 06SJ. -/
public structure CompletionHomEquivalence
    (hp : IsCofiberedInGroupoids p)
    (hq : IsCofiberedInGroupoids q) where
  /-- The equivalence of the two hom categories. -/
  equiv :
    BasedFunctor
        (BasedCategory.ofFunctor (Restriction.projection (p := q)))
        (BasedCategory.ofFunctor p) ≌
      BasedFunctor (BasedCategory.ofFunctor q)
        (BasedCategory.ofFunctor (FormalObject.projection (p := p)))
  /-- The forward functor has the stipulated formula. -/
  forward : ∀ φ,
    equiv.functor.obj φ = (unitBasedFunctor q hq).comp (completionMap φ)
  /-- On a natural transformation, the forward functor applies completion levelwise
  after the unit, with the transports specified by `forward`. -/
  forward_map : ∀ {φ ψ} (t : φ ⟶ ψ) (X : G),
    (equiv.functor.map t).toNatTrans.app X =
      eqToHom (congrArg (fun f => f.obj X) (forward φ)) ≫
        (completionNatTrans t).toNatTrans.app
          ((completionUnit q hq).functor.obj X) ≫
        eqToHom (congrArg (fun f => f.obj X) (forward ψ)).symm
  /-- Pull back a morphism into the completion along the inclusion of Artinian
  algebras, before applying the canonical comparison. -/
  restrictedMap :
    (ψ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))) →
      Restriction q ⥤
        CategoricalPullback
          (restrictionCompletionEquivalence p hp).inclusion
          (FormalObject.projection (p := p))
  /-- The pullback has the Artinian base of the restricted source object. -/
  restrictedMap_fst : ∀ ψ X, ((restrictedMap ψ).obj X).fst = X.base
  /-- The pullback has the image of the original object under the morphism. -/
  restrictedMap_snd : ∀ ψ X, ((restrictedMap ψ).obj X).snd = ψ.obj X.obj
  /-- On arrows, restriction retains the Artinian base arrow. -/
  restrictedMap_arrow_fst : ∀ ψ {X Y : Restriction q} (f : X ⟶ Y),
    ((restrictedMap ψ).map f).fst =
      eqToHom (restrictedMap_fst ψ X) ≫ f.base ≫
        eqToHom (restrictedMap_fst ψ Y).symm
  /-- On arrows, restriction applies the original morphism upstairs. -/
  restrictedMap_arrow_snd : ∀ ψ {X Y : Restriction q} (f : X ⟶ Y),
    ((restrictedMap ψ).map f).snd =
      eqToHom (restrictedMap_snd ψ X) ≫ ψ.map f.obj ≫
        eqToHom (restrictedMap_snd ψ Y).symm
  /-- Restriction also acts on natural transformations. -/
  restrictedMap_map : ∀ {ψ χ} (_t : ψ ⟶ χ),
    restrictedMap ψ ⟶ restrictedMap χ
  /-- On the Artinian base this transformation is the identity. -/
  restrictedMap_map_fst : ∀ {ψ χ} (t : ψ ⟶ χ) (X : Restriction q),
    ((restrictedMap_map t).app X).fst =
      eqToHom (restrictedMap_fst ψ X) ≫
        eqToHom (restrictedMap_fst χ X).symm
  /-- On formal objects it is the given transformation. -/
  restrictedMap_map_snd : ∀ {ψ χ} (t : ψ ⟶ χ) (X : Restriction q),
    ((restrictedMap_map t).app X).snd =
      eqToHom (restrictedMap_snd ψ X) ≫ t.toNatTrans.app X.obj ≫
        eqToHom (restrictedMap_snd χ X).symm
  /-- The inverse is naturally isomorphic to restriction followed by `can`. -/
  inverseIso : ∀ ψ,
    (equiv.inverse.obj ψ).toFunctor ≅
      restrictedMap ψ ⋙ (restrictionCompletionEquivalence p hp).can
  /-- Relative to the canonical base comparison of Tag 06SJ, the inverse
  isomorphism is based: every component lies over the identity of the
  Artinian base. -/
  inverseIso_over : ∀ ψ (X : Restriction q),
    p.map ((inverseIso ψ).hom.app X) ≫
        (restrictionCompletionEquivalence p hp).canOver.hom.app
          ((restrictedMap ψ).obj X) ≫
        eqToHom (restrictedMap_fst ψ X) =
      eqToHom ((equiv.inverse.obj ψ).w_obj X)
  /-- The preceding isomorphism is natural in the morphism being restricted. -/
  inverse_map : ∀ {ψ χ} (t : ψ ⟶ χ) (X : Restriction q),
    (equiv.inverse.map t).toNatTrans.app X ≫ (inverseIso χ).hom.app X =
      (inverseIso ψ).hom.app X ≫
        (restrictionCompletionEquivalence p hp).can.map
          ((restrictedMap_map t).app X)

/-- **Stacks Project, Tag 06HA (hom equivalence), reduced to the two comparison
isomorphisms.**  Given a natural isomorphism from the identity to `Φ ⋙ Ψ` and one from
`Ψ ⋙ Φ` to the identity, the pair `(Φ, Ψ)` assembles into the equivalence of hom
categories, and all the canonical formulas of `CompletionHomEquivalence` hold on the
nose. -/
public noncomputable def completionHomEquivalenceOfIsos
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (unit : Functor.id _ ≅
      completionHomForward p q hq ⋙ completionHomInverse p q hp)
    (counit : completionHomInverse p q hp ⋙ completionHomForward p q hq ≅
      Functor.id _) :
    CompletionHomEquivalence p q hp hq where
  equiv := CategoryTheory.Equivalence.mk (completionHomForward p q hq)
    (completionHomInverse p q hp) unit counit
  forward _ := rfl
  forward_map _ _ := by exact eq_eqToHom_comp_comp _ _ (HEq.refl _)
  restrictedMap ψ := restrictedPullbackMap p q hp ψ
  restrictedMap_fst _ _ := rfl
  restrictedMap_snd _ _ := rfl
  restrictedMap_arrow_fst _ _ _ _ := by exact eq_eqToHom_comp_comp _ _ (HEq.refl _)
  restrictedMap_arrow_snd _ _ _ _ := by exact eq_eqToHom_comp_comp _ _ (HEq.refl _)
  restrictedMap_map t := (restrictedPullbackNatTrans p q hp t).toNatTrans
  restrictedMap_map_fst _ _ := rfl
  restrictedMap_map_snd _ _ := by exact eq_eqToHom_comp_comp _ _ (HEq.refl _)
  inverseIso _ := Iso.refl _
  inverseIso_over ψ X := by
    simp only [Iso.refl_hom]
    refine (map_id_comp p rfl _).trans ?_
    rw [restrictionCompletionEquivalence_canOver_hom_app p hp
      ((restrictedPullbackMap p q hp ψ).obj X)
      (((restrictedPullbackBasedFunctor p q hp ψ).comp (canBasedFunctor p hp)).w_obj X)]
    exact eqToHom_trans_eq _ _ _
  inverse_map _ _ := by
    simp only [Iso.refl_hom]
    exact comp_eq_comp_of_id rfl rfl rfl


end

end Deformation

end
