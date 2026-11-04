module

public import StacksFrontier.CategoryTheory.RelativeInertia
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The inertia square is a 2-fibre product (Stacks 04Z6)

Fix a category `C`, fibred categories `p : S ⥤ C` and `p' : S' ⥤ C` over `C`, and a
1-morphism `F : S ⥤ S'` of fibred categories over `C` (so `F ⋙ p' = p` and `F` preserves
strongly cartesian morphisms). Stacks 04Z6 (Lemma 4.34.3) says that the square
```
  I_{S/S'} --c--> I_S
     |             |
  F∘π |            | I_F
     v             v
     S' ---e---> I_{S'}
```
is a 2-fibre product in the (2,1)-category of fibred categories over `C`.

Here `c` is the comparison functor `(x, α) ↦ (x, α)`, `I_F` the functoriality functor
`(x, α) ↦ (F x, F α)`, and `e` the neutral section `x' ↦ (x', id)`. The statement is
rendered by comparing with the *explicit* 2-fibre product of categories over `C`
(`CategoryTheory.TwoFibreProductOver`, the construction of Stacks 0040): the canonical
comparison 1-morphism `Θ` from `I_{S/S'}` to `S' ×_{e, I_{S'}, I_F} I_S` is an equivalence
**over `C`**, meaning that its quasi-inverse, unit and counit are all over `C` as well.
That is what `IsEquivalenceOver` records, with the functor `Θ` an explicit parameter, so
that a term of that type certifies the *given* comparison functor rather than merely the
existence of some equivalence.

The relative inertia is the canonical `CategoryTheory.RelativeInertia` of Stacks 034I;
composition is diagrammatic, so the Stacks condition `β ∘ φ = φ ∘ α` on morphisms of the
inertia is its `comm` field `φ ≫ β = α ≫ φ`. That `Θ` is an equivalence over `C` is in fact
purely formal — `Θ` is fully faithful and essentially surjective by construction — so the
fibred hypotheses are not needed for the proof; they are kept because they are the
hypotheses of the source, which makes the statement no weaker.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₃} [Category.{v₃} S']

/-! ## Equivalences over `C`

An equivalence of categories **over `C`** between `q : A ⥤ C` and `r : B ⥤ C` is an
equivalence of categories whose underlying functor is a given, fixed functor `G : A ⥤ B`
and whose data — functor, quasi-inverse, unit and counit — are all over `C`. Concretely it
is a quasi-inverse `inverse : B ⥤ A` together with unit and counit isomorphisms exhibiting
an adjoint equivalence, such that `G ⋙ r = q`, `inverse ⋙ q = r`, and every component of
the unit and counit lies over an identity of `C`, i.e. is a 2-morphism in the
(2,1)-category of categories over `C`.

This is deliberately *not* Mathlib's `BasedCategory`-flavoured notion: the functor `G` is a
parameter of the structure rather than being packaged inside an opaque `A ≌ B`, which is
what lets the main statement below be about the specific comparison functor `Θ`. -/

section EquivalenceOver

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- The witness that a *given* functor `G : A ⥤ B` is an equivalence of categories over
`C`, where `q : A ⥤ C` and `r : B ⥤ C` are the structure functors. -/
structure IsEquivalenceOver (q : A ⥤ C) (r : B ⥤ C) (G : A ⥤ B) where
  /-- The quasi-inverse functor. -/
  inverse : B ⥤ A
  /-- The unit isomorphism `𝟭 A ≅ G ⋙ inverse`. -/
  unitIso : 𝟭 A ≅ G ⋙ inverse
  /-- The counit isomorphism `inverse ⋙ G ≅ 𝟭 B`. -/
  counitIso : inverse ⋙ G ≅ 𝟭 B
  /-- The triangle identity making this an adjoint equivalence. -/
  functor_unitIso_comp : ∀ X : A,
    G.map (unitIso.hom.app X) ≫ counitIso.hom.app (G.obj X) = 𝟙 (G.obj X)
  /-- The given functor `G` is over `C`. -/
  functor_over : G ⋙ r = q
  /-- The quasi-inverse is over `C`. -/
  inverse_over : inverse ⋙ q = r
  /-- Each unit component lies over an identity of `C`. -/
  unit_over : ∀ X : A, q.map (unitIso.hom.app X) = eqToHom (by
    have h1 : q.obj X = r.obj (G.obj X) := (Functor.congr_obj functor_over X).symm
    have h2 : r.obj (G.obj X) = q.obj (inverse.obj (G.obj X)) :=
      (Functor.congr_obj inverse_over (G.obj X)).symm
    exact h1.trans h2)
  /-- Each counit component lies over an identity of `C`. -/
  counit_over : ∀ Y : B, r.map (counitIso.hom.app Y) = eqToHom (by
    have h1 : r.obj (G.obj (inverse.obj Y)) = q.obj (inverse.obj Y) :=
      Functor.congr_obj functor_over (inverse.obj Y)
    have h2 : q.obj (inverse.obj Y) = r.obj Y := Functor.congr_obj inverse_over Y
    exact h1.trans h2)

/-- An `IsEquivalenceOver` witness in particular exhibits the given functor `G` as an
equivalence of categories. -/
lemma IsEquivalenceOver.isEquivalence {q : A ⥤ C} {r : B ⥤ C} {G : A ⥤ B}
    (E : IsEquivalenceOver q r G) : G.IsEquivalence :=
  (CategoryTheory.Equivalence.mk' G E.inverse E.unitIso E.counitIso
    E.functor_unitIso_comp).isEquivalence_functor

end EquivalenceOver

namespace RelativeInertia

/-- The structure functor `I_S ⥤ C` of the inertia of a category over `C`,
`(x, α) ↦ p x`. -/
abbrev toBase (p : S ⥤ C) : RelativeInertia p ⥤ C := RelativeInertia.π p ⋙ p

/-! ## The four 1-morphisms of the square -/

variable (p : S ⥤ C) (p' : S' ⥤ C) (F : S ⥤ S') (hF : F ⋙ p' = p)

/-- The comparison 1-morphism `c : I_{S/S'} ⥤ I_S`, `(x, α) ↦ (x, α)`. It is well defined
because `F α = id` and `p' ∘ F = p` force `α` to lie over an identity. -/
@[simps]
def comparison : RelativeInertia F ⥤ RelativeInertia p where
  obj A := ⟨A.obj, A.auto, by
    have h := Functor.congr_hom hF.symm A.auto.hom
    have hid : (F ⋙ p').map A.auto.hom = 𝟙 ((F ⋙ p').obj A.obj) := by
      simp [A.cond]
    rw [h, hid]
    simp⟩
  map {A B} φ := ⟨φ.hom, φ.comm⟩

/-- The functoriality 1-morphism `I_F : I_S ⥤ I_{S'}`, `(x, α) ↦ (F x, F α)`. -/
@[simps]
def functoriality : RelativeInertia p ⥤ RelativeInertia p' where
  obj A := ⟨F.obj A.obj, F.mapIso A.auto, by
    have h := Functor.congr_hom hF A.auto.hom
    simp only [Functor.comp_map] at h
    rw [Functor.mapIso_hom, h, A.cond]
    simp⟩
  map {A B} φ := ⟨F.map φ.hom, by
    simpa using congrArg F.map φ.comm⟩
  map_id A := by
    apply RelativeInertiaHom.ext
    simp
  map_comp f g := by
    apply RelativeInertiaHom.ext
    simp

/-! The neutral section `e : S' ⥤ I_{S'}`, `x' ↦ (x', id)`, `ψ ↦ ψ` is
`CategoryTheory.RelativeInertia.neutralSection`, in
`StacksFrontier.CategoryTheory.RelativeInertia`; that it is a 1-morphism over `C`, i.e.
`e ⋙ toBase p' = p'`, is `RelativeInertia.neutralSection_comp_relativeInertiaStruct`. -/

/-- The functoriality 1-morphism is a 1-morphism over `C`. -/
lemma functoriality_comp_toBase :
    (functoriality p p' F hF) ⋙ toBase p' = toBase p :=
  Functor.ext (fun A => Functor.congr_obj hF A.obj) (fun _ _ φ => Functor.congr_hom hF φ.hom)

/-! ## The explicit 2-fibre product and the comparison 1-morphism `Θ` -/

/-- The explicit 2-fibre product `S' ×_{e, I_{S'}, I_F} I_S` of categories over `C`
appearing in the statement. -/
abbrev FibreProduct : Type _ :=
  TwoFibreProductOver p' (toBase p) (toBase p') (neutralSection p') (functoriality p p' F hF)

/-- The structure functor of `S' ×_{e, I_{S'}, I_F} I_S` to `C`, `(U, x', (x, α), f) ↦ U`. -/
abbrev FibreProduct.structureFunctor : FibreProduct p p' F hF ⥤ C :=
  TwoFibreProductOver.structureFunctor p' (toBase p) (toBase p') (neutralSection p')
    (functoriality p p' F hF)

/-- The first projection `pr₁ : S' ×_{I_{S'}} I_S ⥤ S'`. -/
abbrev FibreProduct.fst : FibreProduct p p' F hF ⥤ S' :=
  TwoFibreProductOver.fst p' (toBase p) (toBase p') (neutralSection p')
    (functoriality p p' F hF)

/-- The second projection `pr₂ : S' ×_{I_{S'}} I_S ⥤ I_S`. -/
abbrev FibreProduct.snd : FibreProduct p p' F hF ⥤ RelativeInertia p :=
  TwoFibreProductOver.snd p' (toBase p) (toBase p') (neutralSection p')
    (functoriality p p' F hF)

/-- The object equality witnessing 2-commutativity of the square: `e (F x) = (F x, id)`
equals `I_F (c (x, α)) = (F x, F α)`, because `F α = id`. -/
lemma toFibreProduct_obj_eq (A : RelativeInertia F) :
    (neutralSection p').obj (F.obj A.obj)
      = (functoriality p p' F hF).obj ((comparison p p' F hF).obj A) :=
  RelativeInertia.obj_ext rfl (by simp [A.cond, neutralSection])

/-- The canonical comparison 1-morphism `Θ : I_{S/S'} ⥤ S' ×_{e, I_{S'}, I_F} I_S` given by
the universal property of the 2-fibre product: `(x, α) ↦ (p x, F x, (x, α), id)` on objects
and `φ ↦ (F φ, φ)` on morphisms. -/
@[simps]
def toFibreProduct : RelativeInertia F ⥤ FibreProduct p p' F hF where
  obj A :=
    { base := p.obj A.obj
      x := F.obj A.obj
      y := (comparison p p' F hF).obj A
      hx := congrFun (congrArg Functor.obj hF) A.obj
      hy := rfl
      iso := eqToIso (toFibreProduct_obj_eq p p' F hF A)
      vertical := by
        simp only [eqToIso.hom]
        exact IsHomLift.eqToHom_domain_lift_id (toFibreProduct_obj_eq p p' F hF A)
          (congrFun (congrArg Functor.obj hF) A.obj) }
  map {A B} φ :=
    { hbase := p.map φ.hom
      a := F.map φ.hom
      b := (comparison p p' F hF).map φ
      ha := Functor.isHomLift_map_of_comp_eq hF (p.map φ.hom) φ.hom
      hb := (RelativeInertia.isHomLift_π_comp_iff (p := p) (p.map φ.hom)
        ((comparison p p' F hF).map φ)).mpr (by simp)
      w := by
        apply RelativeInertiaHom.ext
        simp only [functoriality_map_hom, comparison_map_hom, neutralSection_map_hom,
          eqToIso.hom, RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom]
        simp }
  map_id A := by
    apply TwoFibreProductOver.Hom.ext'
    · simp
    · apply RelativeInertiaHom.ext
      simp
  map_comp f g := by
    apply TwoFibreProductOver.Hom.ext'
    · simp
    · apply RelativeInertiaHom.ext
      simp

/-- `Θ` is a 1-morphism over `C`: it commutes with the structure functors, that of the
2-fibre product being `(U, x', (x, α), f) ↦ U` and that of `I_{S/S'}` being `π ⋙ p`. -/
lemma toFibreProduct_comp_structureFunctor :
    (toFibreProduct p p' F hF) ⋙ FibreProduct.structureFunctor p p' F hF
      = RelativeInertia.π F ⋙ p := by
  refine CategoryTheory.Functor.ext (fun A => rfl) (fun A B φ => ?_)
  simp

/-! ## The quasi-inverse of `Θ` and the equivalence -/

/-- **The linchpin.** For an object `P = (U, x', (x, α), f)` of the explicit 2-fibre
product, the automorphism `α` of `x` satisfies `F α = id`.

The gluing datum `f : e(x') ≅ I_F (x, α)` is an isomorphism of `I_{S'}`, so its `comm`
field reads `f.hom = f.hom ≫ F α`, and `f.hom` is a split monomorphism because `f` is an
isomorphism; cancelling gives `F α = id`. -/
lemma map_auto_eq_id (P : FibreProduct p p' F hF) :
    F.map P.y.auto.hom = 𝟙 (F.obj P.y.obj) := by
  -- The underlying morphisms of the gluing datum, with their endpoints spelled `P.x` and
  -- `F.obj P.y.obj` rather than as objects of the inertia, so that the cancellation below is
  -- an identity between morphisms of `S'` whose types agree on the nose.
  obtain ⟨e, einv, hinv_id, hcomm⟩ :
      ∃ (e : P.x ⟶ F.obj P.y.obj) (einv : F.obj P.y.obj ⟶ P.x),
        einv ≫ e = 𝟙 (F.obj P.y.obj) ∧ e ≫ F.map P.y.auto.hom = 𝟙 P.x ≫ e :=
    ⟨P.iso.hom.hom, P.iso.inv.hom, congrArg RelativeInertiaHom.hom P.iso.inv_hom_id,
      P.iso.hom.comm⟩
  simpa [reassoc_of% hinv_id, hinv_id] using congrArg (einv ≫ ·) hcomm

/-- The quasi-inverse `S' ×_{e, I_{S'}, I_F} I_S ⥤ I_{S/S'}` of `Θ`: forget `x'` and the
gluing datum and keep `(x, α)`, which is an object of the relative inertia by
`map_auto_eq_id`. On morphisms, take the second component. -/
def fromFibreProduct : FibreProduct p p' F hF ⥤ RelativeInertia F where
  obj P := ⟨P.y.obj, P.y.auto, map_auto_eq_id p p' F hF P⟩
  map {P Q} u := ⟨u.b.hom, u.b.comm⟩
  map_id P := by
    apply RelativeInertiaHom.ext
    simp
  map_comp u w := by
    apply RelativeInertiaHom.ext
    simp

/-- The quasi-inverse is a 1-morphism over `C`. -/
lemma fromFibreProduct_comp_struct :
    (fromFibreProduct p p' F hF) ⋙ (RelativeInertia.π F ⋙ p)
      = FibreProduct.structureFunctor p p' F hF := by
  refine CategoryTheory.Functor.ext (fun P => P.hy) (fun P Q u => ?_)
  have := u.hb
  exact IsHomLift.fac' (toBase p) u.hbase u.b

/-- The unit isomorphism `𝟭 ≅ Θ ⋙ Θ⁻¹`. It is the identity: `(Θ ⋙ Θ⁻¹)(x, α)` is
`(x, α)` again, the condition field being a proposition. -/
def fibreProductUnitIso :
    𝟭 (RelativeInertia F) ≅ toFibreProduct p p' F hF ⋙ fromFibreProduct p p' F hF := by
  refine NatIso.ofComponents (fun A => Iso.refl _) ?_
  intro A B φ; apply RelativeInertiaHom.ext
  simp [toFibreProduct, fromFibreProduct, comparison]

/-- The gluing datum of an object of the explicit 2-fibre product is vertical: its
underlying morphism of `S'` is the canonical transport isomorphism between the two objects
of `S'` lying over the base. -/
lemma fibreProduct_iso_obj_eq (P : FibreProduct p p' F hF) :
    p'.obj P.x = p'.obj (F.obj P.y.obj) :=
  P.hx.trans (P.hy.symm.trans (Functor.congr_obj hF P.y.obj).symm)

/-- The gluing datum lies over an identity, so its underlying morphism of `S'` is the
transport isomorphism of `fibreProduct_iso_obj_eq`. -/
lemma fibreProduct_map_iso_hom (P : FibreProduct p p' F hF) :
    p'.map P.iso.hom.hom = eqToHom (fibreProduct_iso_obj_eq p p' F hF P) := by
  have := (RelativeInertia.isHomLift_π_comp_iff (p := p') (𝟙 P.base) P.iso.hom).mp P.vertical
  rw [IsHomLift.fac' p' (𝟙 P.base) P.iso.hom.hom]
  simp

/-- The inverse of the gluing datum is vertical as well. -/
lemma fibreProduct_map_iso_inv (P : FibreProduct p p' F hF) :
    p'.map P.iso.inv.hom = eqToHom (fibreProduct_iso_obj_eq p p' F hF P).symm := by
  have hih := congrArg RelativeInertiaHom.hom P.iso.inv_hom_id
  simp only [RelativeInertia.comp_hom, RelativeInertia.id_hom] at hih
  have e0 : p'.map P.iso.inv.hom ≫ p'.map P.iso.hom.hom = 𝟙 _ := by
    rw [← p'.map_comp, hih, p'.map_id]
  rwa [fibreProduct_map_iso_hom, comp_eqToHom_iff, Category.id_comp] at e0

/-- The counit isomorphism `Θ⁻¹ ⋙ Θ ≅ 𝟭`. At `P = (U, x', (x, α), f)` it is the pair
`(f⁻¹, id)`: the underlying `S'`-isomorphism of the gluing datum in the first component and
the identity of `(x, α)` in the second. -/
def fibreProductCounitIso :
    fromFibreProduct p p' F hF ⋙ toFibreProduct p p' F hF ≅ 𝟭 (FibreProduct p p' F hF) :=
  NatIso.ofComponents
    (fun P =>
      { hom :=
          { hbase := eqToHom P.hy
            a := P.iso.inv.hom
            b := 𝟙 P.y
            ha := by
              refine IsHomLift.of_fac' p' (eqToHom P.hy) P.iso.inv.hom
                (Functor.congr_obj hF P.y.obj) P.hx ?_
              rw [fibreProduct_map_iso_inv]
              simp
            hb := IsHomLift.id_lift_eqToHom_domain P.hy rfl
            w := by
              apply RelativeInertiaHom.ext
              have hF1 : F.map (𝟙 P.y.obj) = 𝟙 (F.obj P.y.obj) := F.map_id P.y.obj
              simp only [Functor.comp_obj, Functor.id_obj, comp_hom, neutralSection_map_hom,
                toFibreProduct_obj_iso, eqToIso.hom, RelativeInertiaHom.eqToHom_hom, eqToHom_refl,
                functoriality_map_hom, id_hom, hF1, Category.id_comp]
              exact congrArg RelativeInertiaHom.hom P.iso.inv_hom_id }
        inv :=
          { hbase := eqToHom P.hy.symm
            a := P.iso.hom.hom
            b := 𝟙 P.y
            ha := by
              refine IsHomLift.of_fac' p' (eqToHom P.hy.symm) P.iso.hom.hom P.hx
                (Functor.congr_obj hF P.y.obj) ?_
              rw [fibreProduct_map_iso_hom]
              simp
            hb := IsHomLift.id_lift_eqToHom_domain P.hy.symm P.hy
            w := by
              apply RelativeInertiaHom.ext
              simp [neutralSection] }
        hom_inv_id := by
          apply TwoFibreProductOver.Hom.ext'
          · exact congrArg RelativeInertiaHom.hom P.iso.inv_hom_id
          · exact Category.comp_id (𝟙 P.y)
        inv_hom_id := by
          apply TwoFibreProductOver.Hom.ext'
          · exact congrArg RelativeInertiaHom.hom P.iso.hom_inv_id
          · apply RelativeInertiaHom.ext
            simp [fromFibreProduct] })
    (by
      intro P Q u
      apply TwoFibreProductOver.Hom.ext'
      · -- The `S'`-component. Inverting the naturality square `u.w` is an identity between
        -- morphisms of the inertia `I_{S'}`, where all the endpoints already agree; reading off
        -- underlying morphisms of `S'` then gives the required identity.
        have key : (functoriality p p' F hF).map u.b ≫ Q.iso.inv
            = P.iso.inv ≫ (neutralSection p').map u.a := by
          rw [Iso.comp_inv_eq, Category.assoc, u.w, Iso.inv_hom_id_assoc]
        exact congrArg RelativeInertiaHom.hom key
      · -- The `I_S`-component: both sides are `u.b` composed with an identity of `I_S`.
        exact (Category.comp_id u.b).trans (Category.id_comp u.b).symm)

/-- The triangle identity for `Θ ⊣ Θ⁻¹`. Since the unit is the identity, it reduces to the
counit component at `Θ X` being the identity, which holds because there the gluing datum
is the identity. -/
lemma fibreProduct_unitIso_comp (X : RelativeInertia F) :
    (toFibreProduct p p' F hF).map ((fibreProductUnitIso p p' F hF).hom.app X)
      ≫ (fibreProductCounitIso p p' F hF).hom.app ((toFibreProduct p p' F hF).obj X)
      = 𝟙 ((toFibreProduct p p' F hF).obj X) := by
  have hu : (fibreProductUnitIso p p' F hF).hom.app X = 𝟙 X := by
    simp
    rfl
  rw [hu]
  have hm : (toFibreProduct p p' F hF).map (𝟙 X) = eqToHom rfl :=
    (toFibreProduct p p' F hF).map_id X
  rw [hm, eqToHom_refl]
  apply TwoFibreProductOver.Hom.ext'
  · simp only [TwoFibreProductOver.id_a, fibreProductCounitIso,
      NatIso.ofComponents_hom_app, toFibreProduct_obj_iso, eqToIso.inv,
      RelativeInertiaHom.eqToHom_hom, Functor.id_obj, Functor.comp_obj, eqToHom_refl,
      Category.id_comp]
    rfl
  · simp only [TwoFibreProductOver.comp_b, TwoFibreProductOver.id_b, fibreProductCounitIso,
      NatIso.ofComponents_hom_app]
    simp

/-- Every unit component lies over an identity of `C`: the unit is the identity natural
isomorphism. -/
lemma fibreProductUnit_over (X : RelativeInertia F) :
    (RelativeInertia.π F ⋙ p).map ((fibreProductUnitIso p p' F hF).hom.app X) = eqToHom (by
      have h1 : (RelativeInertia.π F ⋙ p).obj X
          = (FibreProduct.structureFunctor p p' F hF).obj ((toFibreProduct p p' F hF).obj X) :=
        (Functor.congr_obj (toFibreProduct_comp_structureFunctor p p' F hF) X).symm
      have h2 : (FibreProduct.structureFunctor p p' F hF).obj ((toFibreProduct p p' F hF).obj X)
          = (RelativeInertia.π F ⋙ p).obj
              ((fromFibreProduct p p' F hF).obj ((toFibreProduct p p' F hF).obj X)) :=
        (Functor.congr_obj (fromFibreProduct_comp_struct p p' F hF)
          ((toFibreProduct p p' F hF).obj X)).symm
      exact h1.trans h2) := by
  simp only [fibreProductUnitIso, NatIso.ofComponents_hom_app, Iso.refl_hom]
  have hpi : (RelativeInertia.π F ⋙ p).map (𝟙 ((𝟭 (RelativeInertia F)).obj X)) = eqToHom rfl :=
    (RelativeInertia.π F ⋙ p).map_id _
  rw [hpi]

/-- Every counit component lies over an identity of `C`: its base component is the identity
of the base object, since the gluing datum is vertical. -/
lemma fibreProductCounit_over (Y : FibreProduct p p' F hF) :
    (FibreProduct.structureFunctor p p' F hF).map
        ((fibreProductCounitIso p p' F hF).hom.app Y) = eqToHom (by
      have h1 : (FibreProduct.structureFunctor p p' F hF).obj
            ((toFibreProduct p p' F hF).obj ((fromFibreProduct p p' F hF).obj Y))
          = (RelativeInertia.π F ⋙ p).obj ((fromFibreProduct p p' F hF).obj Y) :=
        Functor.congr_obj (toFibreProduct_comp_structureFunctor p p' F hF)
          ((fromFibreProduct p p' F hF).obj Y)
      have h2 : (RelativeInertia.π F ⋙ p).obj ((fromFibreProduct p p' F hF).obj Y)
          = (FibreProduct.structureFunctor p p' F hF).obj Y :=
        Functor.congr_obj (fromFibreProduct_comp_struct p p' F hF) Y
      exact h1.trans h2) := by
  simp [fibreProductCounitIso, NatIso.ofComponents_hom_app,
    TwoFibreProductOver.structureFunctor_map]

/-! ## Main statement -/

variable [hpfib : p.IsFibered] [hp'fib : p'.IsFibered]
  (hFone : Functor.IsFibredOneMorphism p p' F)

-- The fibred hypotheses are hypotheses of the source, so they are kept in the statement even
-- though the proof does not need them; see the module docstring.
set_option linter.unusedSectionVars false in
include hpfib hp'fib hFone hF in
/-- **Stacks 04Z6.** The 2-commutative square
```
  I_{S/S'} --c--> I_S
     |             |
  F∘π |            | I_F
     v             v
     S' ---e---> I_{S'}
```
is a 2-fibre product in the (2,1)-category of fibred categories over `C`: the canonical
comparison 1-morphism `Θ` to the explicit 2-fibre product `S' ×_{e, I_{S'}, I_F} I_S` is an
equivalence of categories **over `C`**.

The witness produced has `Θ` itself as its underlying functor, so the statement is about
the given comparison functor with its prescribed action on objects and morphisms, and not
merely about the existence of some equivalence. -/
@[stacks 04Z6]
theorem isEquivalenceOver_toFibreProduct :
    Nonempty (IsEquivalenceOver (RelativeInertia.π F ⋙ p)
      (FibreProduct.structureFunctor p p' F hF) (toFibreProduct p p' F hF)) :=
  ⟨{ inverse := fromFibreProduct p p' F hF
     unitIso := fibreProductUnitIso p p' F hF
     counitIso := fibreProductCounitIso p p' F hF
     functor_unitIso_comp := fibreProduct_unitIso_comp p p' F hF
     functor_over := toFibreProduct_comp_structureFunctor p p' F hF
     inverse_over := fromFibreProduct_comp_struct p p' F hF
     unit_over := fibreProductUnit_over p p' F hF
     counit_over := fibreProductCounit_over p p' F hF }⟩

include hpfib hp'fib hFone hF in
/-- Consequence of Stacks 04Z6: the comparison functor `Θ` is an equivalence of the
underlying categories. -/
@[stacks 04Z6]
theorem toFibreProduct_isEquivalence :
    (toFibreProduct p p' F hF).IsEquivalence := by
  obtain ⟨E⟩ := isEquivalenceOver_toFibreProduct p p' F hF hFone
  exact E.isEquivalence

/-- **Stacks 04Z6, the square.** The 2-commutativity of the square is witnessed by a
natural isomorphism over `C`, `I_F ∘ c ≅ e ∘ (F ∘ π)`. On an object `(x, α)` both
composites are `(F x, id)`, since `F α = id`, so the canonical 2-isomorphism is the
identity. -/
@[stacks 04Z6]
def squareTwoCommutes :
    (comparison p p' F hF) ⋙ (functoriality p p' F hF)
      ≅ (RelativeInertia.π F ⋙ F) ⋙ (neutralSection p') :=
  NatIso.ofComponents
    (fun A => eqToIso (toFibreProduct_obj_eq p p' F hF A).symm)
    (by
      intro A B φ
      apply RelativeInertiaHom.ext
      simp only [Functor.comp_map, functoriality_map_hom, comparison_map_hom,
        neutralSection_map_hom, RelativeInertia.π_map, eqToIso.hom, RelativeInertia.comp_hom,
        RelativeInertiaHom.eqToHom_hom]
      simp)

end RelativeInertia

end CategoryTheory
