module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaMonomorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The inertia comparison of a cartesian square

Fix a category `C`. For a morphism `F : X ⥤ Y` over `C` the inertia square of Stacks 06R5 is
compared with the 2-fibre product by `CategoryTheory.inertiaPullbackComparison`, and 06R5 says
that comparison is an equivalence over `C` when `F` is fully faithful. This file isolates the
part of that statement which survives base change: in a cartesian square

```
T --H--> Y
|        |
K        G
|        |
v        v
X --F--> Z
```

over `C` — cartesian in the sense that the comparison `T ⥤ X ×_Z Y` is fully faithful — the
inertia comparison of `H` is an equivalence over `C` as soon as the inertia comparison of `F`
is.

Everything is formal, and the reason is visible in the two intermediate statements: the
inertia comparison of `F` being an equivalence says exactly that `F` *reflects* the commuting
square defining a morphism of relative inertia, and *lifts* automorphisms lying over an
identity. Both properties transfer across a cartesian square componentwise.

## Main results

* `CategoryTheory.inertiaPullbackComparison_reflects_comm`: a full inertia comparison reflects
  the commuting square of a morphism of relative inertia.
* `CategoryTheory.inertiaPullbackComparison_exists_aut`: an essentially surjective inertia
  comparison lifts a vertical automorphism of the target to one of the source.
* `CategoryTheory.nonempty_isEquivalenceOver_of_forall_verticalObjPreimage`: a fully faithful
  morphism over `C` all of whose objectwise preimages are reached by a *vertical* isomorphism
  is an equivalence over `C`.
* `CategoryTheory.nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts`:
  conversely, reflecting commuting squares and lifting vertical automorphisms is enough for the
  inertia comparison to be an equivalence over `C`.
* `CategoryTheory.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange`: the inertia
  comparison is an equivalence over `C` after a cartesian base change.
* `CategoryTheory.RelativeInertia.isEquivalenceOver_toBaseChangeFibreProduct`: the comparison
  1-morphism `Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'` of the left square of [Stacks, Tag 06PQ] is an
  equivalence over `C`, where `X' = X ×_Y Y'`.
* `CategoryTheory.RelativeInertia.exists_baseChangeComparison`: the same statement in the
  `∃ Θ, (prescribed action of Θ) ∧ (equivalence over C)` shape, which is what
  `StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChangeCounterexample` shows to be false
  without the hypothesis `hF`.

## Implementation notes

`CategoryTheory.IsEquivalenceOver` certifies the *given* comparison functor together with the
verticality of its unit and counit, so an equivalence has to be produced with its quasi-inverse
in hand; `CategoryTheory.Functor.quasiInverseOfChoice` builds one from a choice of preimages,
and `nonempty_isEquivalenceOver_of_forall_verticalObjPreimage` is that construction with the
verticality bookkeeping discharged.

As in `StacksFrontier.CategoryTheory.FiberedCategory.InertiaMonomorphism`, the structure functors
`CategoryTheory.RelativeInertia.π` and `CategoryTheory.TwoFibreProductOver.structureFunctor` are
made locally `implicit_reducible`: they are semireducible definitions that merely re-project a
field, and the `eqToHom` coherence goals below are discharged by `simp`/`rw`, whose `kabstract`
works at that transparency.
-/

@[expose] public section

open CategoryTheory

universe uC vC uX vX uY vY uZ vZ uT vT

namespace CategoryTheory

section Comparison

attribute [local implicit_reducible] RelativeInertia.π TwoFibreProductOver.structureFunctor

variable {C : Type uC} [Category.{vC} C]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)

/-- A functor sends the conjugate `e.inv ≫ f ≫ e.hom` of an endomorphism killed by it to an
identity. -/
private theorem map_inv_comp_comp_hom_eq_id {D : Type*} [Category D] {E : Type*} [Category E]
    (p : D ⥤ E) {a b : D} (e : a ≅ b) (f : a ⟶ a) (hf : p.map f = 𝟙 _) :
    p.map (e.inv ≫ f ≫ e.hom) = 𝟙 _ := by
  rw [p.map_comp, p.map_comp, hf, Category.id_comp, ← p.map_comp, e.inv_hom_id, p.map_id]

/-- A **full** inertia comparison reflects the commuting square of a morphism of relative
inertia: if a morphism of `X` conjugates the images of two automorphisms into one another, it
already conjugates the automorphisms themselves. -/
theorem inertiaPullbackComparison_reflects_comm
    [(inertiaPullbackComparison pX pY F hF).Full]
    (A B : RelativeInertia pX) (m : A.obj ⟶ B.obj)
    (hm : F.map m ≫ F.map B.auto.asIso.hom = F.map A.auto.asIso.hom ≫ F.map m) :
    m ≫ B.auto.asIso.hom = A.auto.asIso.hom ≫ m := by
  let cmp := inertiaPullbackComparison pX pY F hF
  let a : (cmp.obj A).x ⟶ (cmp.obj B).x := ⟨F.map m, hm⟩
  let z : cmp.obj A ⟶ cmp.obj B :=
    { hbase := pX.map m
      a := a
      b := m
      ha := (RelativeInertia.isHomLift_π_comp_iff _ _).mpr
        (Functor.isHomLift_map_of_comp_eq hF (pX.map m) m)
      hb := IsHomLift.map pX m
      w := by
        change F.map m ≫ 𝟙 _ = 𝟙 _ ≫ F.map m
        simp }
  obtain ⟨n, hn⟩ := cmp.map_surjective z
  have he : n.hom = m := congrArg TwoFibreProductOver.Hom.b hn
  simpa [he] using n.comm

/-- An **essentially surjective** inertia comparison lifts automorphisms: an automorphism of
`F x` lying over an identity of `C` is the image of an automorphism of `x` lying over an
identity. -/
theorem inertiaPullbackComparison_exists_aut
    [(inertiaPullbackComparison pX pY F hF).EssSurj]
    (x : X) (β : Aut (F.obj x)) (hβ : pY.map β.asIso.hom = 𝟙 _) :
    ∃ α : Aut x, pX.map α.asIso.hom = 𝟙 _ ∧ F.map α.asIso.hom = β.asIso.hom := by
  let cmp := inertiaPullbackComparison pX pY F hF
  let Q : TwoFibreProductOver (RelativeInertia.toBase pY) pX pY
      (RelativeInertia.π pY) F :=
    { base := pX.obj x
      x := ⟨F.obj x, β, hβ⟩
      y := x
      hx := Functor.congr_obj hF x
      hy := rfl
      iso := Iso.refl _
      vertical := IsHomLift.id (Functor.congr_obj hF x) }
  let A := cmp.objPreimage Q
  let e := cmp.objObjPreimageIso Q
  let b : A.obj ≅ x := (TwoFibreProductOver.snd _ _ _ _ _).mapIso e
  refine ⟨Aut.of (b.symm ≪≫ A.auto.asIso ≪≫ b), ?_, ?_⟩
  · exact map_inv_comp_comp_hom_eq_id pX b A.auto.asIso.hom A.cond
  · have he : e.hom.a.hom = F.map e.hom.b := by
      have he := e.hom.w
      change e.hom.a.hom ≫ 𝟙 _ = 𝟙 _ ≫ F.map e.hom.b at he
      simpa using he
    have hc : F.map e.hom.b ≫ β.asIso.hom = F.map A.auto.asIso.hom ≫ F.map e.hom.b := by
      have hc := e.hom.a.comm
      change e.hom.a.hom ≫ β.asIso.hom = F.map A.auto.asIso.hom ≫ e.hom.a.hom at hc
      rwa [he] at hc
    change F.map (b.inv ≫ A.auto.asIso.hom ≫ b.hom) = β.asIso.hom
    have hc' : F.map b.hom ≫ β.asIso.hom = F.map A.auto.asIso.hom ≫ F.map b.hom := hc
    rw [F.map_comp, F.map_comp, ← hc']
    simp

end Comparison

section EquivalenceOver

attribute [local implicit_reducible] Functor.quasiInverseOfChoice

variable {C : Type uC} [Category.{vC} C]
  {A : Type uX} [Category.{vX} A] {D : Type uY} [Category.{vY} D]

/-- **A fully faithful morphism over `C` with vertical objectwise preimages is an equivalence
over `C`.** If every object `y` of `D` admits an object `x` of `A` over the same object of `C`
and an isomorphism `y ≅ K x` lying over an identity, then the quasi-inverse determined by that
choice, together with its unit and counit, is again over `C`. -/
theorem nonempty_isEquivalenceOver_of_forall_verticalObjPreimage
    (p : A ⥤ C) (q : D ⥤ C) (K : A ⥤ D) (hK : K ⋙ q = p) [K.Full] [K.Faithful]
    (h : ∀ y, ∃ (x : A) (hx : p.obj x = q.obj y) (e : y ≅ K.obj x),
      q.map e.hom = eqToHom ((Functor.congr_obj hK x).trans hx).symm) :
    Nonempty (IsEquivalenceOver p q K) := by
  classical
  choose x hx e he using h
  have hei (y) : q.map (e y).inv =
      eqToHom ((Functor.congr_obj hK (x y)).trans (hx y)) := by
    have hIso : q.mapIso (e y) =
        eqToIso ((Functor.congr_obj hK (x y)).trans (hx y)).symm := Iso.ext (he y)
    exact congrArg Iso.inv hIso
  have hG : Functor.quasiInverseOfChoice K x e ⋙ p = q := by
    refine CategoryTheory.Functor.ext hx fun a b m => ?_
    rw [Functor.comp_map, Functor.map_eq_of_comp_eq p q K hK,
      Functor.map_quasiInverseOfChoice_map]
    simp only [Functor.map_comp, hei, he]
    simp
  refine ⟨{ inverse := Functor.quasiInverseOfChoice K x e
            unitIso := (Functor.quasiInverseOfChoiceUnitIso K x e).symm
            counitIso := Functor.quasiInverseOfChoiceCounitIso K x e
            functor_over := hK
            inverse_over := hG
            functor_unitIso_comp := ?_
            unit_over := ?_
            counit_over := ?_ }⟩
  · intro a
    change K.map (((Functor.FullyFaithful.ofFullyFaithful K).preimageIso
      (e (K.obj a))).hom) ≫ (e (K.obj a)).inv = 𝟙 _
    simp [Functor.FullyFaithful.preimageIso]
  · intro a
    change p.map ((Functor.FullyFaithful.ofFullyFaithful K).preimageIso (e (K.obj a))).hom = _
    have hθ : K.map ((Functor.FullyFaithful.ofFullyFaithful K).preimageIso
        (e (K.obj a))).hom = (e (K.obj a)).hom :=
      (Functor.FullyFaithful.ofFullyFaithful K).map_preimage _
    rw [Functor.map_eq_of_comp_eq p q K hK, hθ, he]
    simp
  · intro y
    exact hei y

end EquivalenceOver

section Criterion

attribute [local implicit_reducible] RelativeInertia.π TwoFibreProductOver.structureFunctor

variable {C : Type uC} [Category.{vC} C]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)

/-- **Reflecting commuting squares and lifting vertical automorphisms makes the inertia
comparison an equivalence over `C`.** This is the converse packaging of
`inertiaPullbackComparison_reflects_comm` and `inertiaPullbackComparison_exists_aut`, and it is
how those two properties are transported across a cartesian square. -/
theorem nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts
    (hR : ∀ (A B : RelativeInertia pX) (m : A.obj ⟶ B.obj),
      F.map m ≫ F.map B.auto.asIso.hom = F.map A.auto.asIso.hom ≫ F.map m →
      m ≫ B.auto.asIso.hom = A.auto.asIso.hom ≫ m)
    (hL : ∀ (x : X) (β : Aut (F.obj x)), pY.map β.asIso.hom = 𝟙 _ →
      ∃ α : Aut x, pX.map α.asIso.hom = 𝟙 _ ∧ F.map α.asIso.hom = β.asIso.hom) :
    Nonempty (IsEquivalenceOver (RelativeInertia.toBase pX)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
        (RelativeInertia.π pY) F)
      (inertiaPullbackComparison pX pY F hF)) := by
  let cmp := inertiaPullbackComparison pX pY F hF
  let q := TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
    (RelativeInertia.π pY) F
  have hcmp : cmp ⋙ q = RelativeInertia.toBase pX := rfl
  have : cmp.Faithful := ⟨fun h => RelativeInertiaHom.ext
    (congrArg TwoFibreProductOver.Hom.b h)⟩
  have : cmp.Full := ⟨fun {A B} m => by
    have he : m.a.hom = F.map m.b := by
      have he := m.w
      change m.a.hom ≫ 𝟙 _ = 𝟙 _ ≫ F.map m.b at he
      simpa using he
    have hc := m.a.comm
    have hc' : F.map m.b ≫ (F.mapIso B.auto.asIso).hom =
        (F.mapIso A.auto.asIso).hom ≫ F.map m.b := by
      simpa [he, cmp, inertiaPullbackComparison, RelativeInertia.functoriality] using hc
    have hcomm := hR A B m.b hc'
    refine ⟨⟨m.b, hcomm⟩, TwoFibreProductOver.Hom.ext' ?_ rfl⟩
    exact RelativeInertiaHom.ext he.symm⟩
  apply nonempty_isEquivalenceOver_of_forall_verticalObjPreimage
    (RelativeInertia.toBase pX) q cmp hcmp
  intro Q
  let β : Aut (F.obj Q.y) := Aut.of (Q.iso.symm ≪≫ Q.x.auto.asIso ≪≫ Q.iso)
  have hβ : pY.map β.asIso.hom = 𝟙 _ :=
    map_inv_comp_comp_hom_eq_id pY Q.iso Q.x.auto.asIso.hom Q.x.cond
  obtain ⟨α, hα, hαF⟩ := hL Q.y β hβ
  let A : RelativeInertia pX := ⟨Q.y, α, hα⟩
  let a : Q.x ⟶ (cmp.obj A).x :=
    { hom := Q.iso.hom
      comm := by
        change Q.iso.hom ≫ F.map α.asIso.hom = Q.x.auto.asIso.hom ≫ Q.iso.hom
        rw [hαF]
        change Q.iso.hom ≫ Q.iso.inv ≫ Q.x.auto.asIso.hom ≫ Q.iso.hom =
          Q.x.auto.asIso.hom ≫ Q.iso.hom
        simp }
  let m : Q ⟶ cmp.obj A :=
    { hbase := eqToHom Q.hy.symm
      a := a
      b := 𝟙 Q.y
      ha := by
        apply (RelativeInertia.isHomLift_π_comp_iff _ _).mpr
        have := Q.vertical
        apply IsHomLift.of_fac' pY (eqToHom Q.hy.symm) Q.iso.hom Q.hx
          (Functor.congr_obj hF Q.y)
        rw [IsHomLift.fac' pY (𝟙 Q.base) Q.iso.hom]
        simp
      hb := IsHomLift.id_lift_eqToHom_domain Q.hy.symm Q.hy
      w := by
        change Q.iso.hom ≫ 𝟙 _ = Q.iso.hom ≫ F.map (𝟙 Q.y)
        simp }
  let ea : Q.x ≅ (cmp.obj A).x :=
    { hom := a
      inv := ⟨Q.iso.inv, by
        change Q.iso.inv ≫ Q.x.auto.asIso.hom = F.map α.asIso.hom ≫ Q.iso.inv
        rw [hαF]
        change Q.iso.inv ≫ Q.x.auto.asIso.hom =
          (Q.iso.inv ≫ Q.x.auto.asIso.hom ≫ Q.iso.hom) ≫ Q.iso.inv
        simp⟩
      hom_inv_id := RelativeInertiaHom.ext Q.iso.hom_inv_id
      inv_hom_id := RelativeInertiaHom.ext Q.iso.inv_hom_id }
  have hma : IsIso m.a := ea.isIso_hom
  have hmb : IsIso m.b := by change IsIso (𝟙 Q.y); infer_instance
  have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m hma hmb
  exact ⟨A, Q.hy, asIso m, rfl⟩

end Criterion

section BaseChange

attribute [local implicit_reducible] RelativeInertia.π TwoFibreProductOver.structureFunctor

variable {C : Type uC} [Category.{vC} C]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  {Z : Type uZ} [Category.{vZ} Z] {T : Type uT} [Category.{vT} T]

/-- **The inertia comparison is an equivalence over `C` after a cartesian base change.** Given a
square of morphisms over `C` filled by a vertical isomorphism `t`, whose comparison to the
2-fibre product `X ×_Z Y` is fully faithful, the inertia comparison of `H : T ⥤ Y` is an
equivalence over `C` as soon as that of `F : X ⥤ Z` is.

Reflecting the commuting square and lifting a vertical automorphism are each checked
componentwise: the `Y`-component is given, and the `X`-component comes from the hypothesis on
`F` transported along `t`. -/
theorem nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C) (pT : T ⥤ C)
    (F : X ⥤ Z) (G : Y ⥤ Z) (H : T ⥤ Y) (K : T ⥤ X)
    (hF : F ⋙ pZ = pX) (hG : G ⋙ pZ = pY)
    (hH : H ⋙ pY = pT) (hK : K ⋙ pX = pT)
    (t : H ⋙ G ≅ K ⋙ F)
    (ht : ∀ x, pZ.IsHomLift (𝟙 (pT.obj x)) (t.hom.app x))
    (hJ : (TwoFibreProductOver.lift pY pX pZ G F pT H K hH hK t ht).FullyFaithful)
    (hf : (inertiaPullbackComparison pX pZ F hF).IsEquivalence) :
    Nonempty (IsEquivalenceOver (RelativeInertia.toBase pT)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pT pY
        (RelativeInertia.π pY) H)
      (inertiaPullbackComparison pT pY H hH)) := by
  have := hf
  let J := TwoFibreProductOver.lift pY pX pZ G F pT H K hH hK t ht
  apply nonempty_inertiaPullbackComparison_isEquivalenceOver_of_reflects_lifts pT pY H hH
  · intro A B m hm
    apply hJ.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    apply TwoFibreProductOver.Hom.ext'
    · exact hm
    · change K.map m ≫ K.map B.auto.asIso.hom = K.map A.auto.asIso.hom ≫ K.map m
      apply inertiaPullbackComparison_reflects_comm pX pZ F hF
        ((RelativeInertia.functoriality pT pX K hK).obj A)
        ((RelativeInertia.functoriality pT pX K hK).obj B)
      change F.map (K.map m) ≫ F.map (K.map B.auto.asIso.hom) =
        F.map (K.map A.auto.asIso.hom) ≫ F.map (K.map m)
      simp only [← F.map_comp, ← K.map_comp]
      change (K ⋙ F).map (m ≫ B.auto.asIso.hom) = (K ⋙ F).map (A.auto.asIso.hom ≫ m)
      apply (cancel_epi (t.hom.app A.obj)).mp
      rw [← t.hom.naturality, ← t.hom.naturality]
      have he : (H ⋙ G).map (m ≫ B.auto.asIso.hom) = (H ⋙ G).map (A.auto.asIso.hom ≫ m) := by
        simpa only [Functor.comp_map, Functor.map_comp] using congrArg G.map hm
      rw [he]
  · intro x β hβ
    let γ : Aut (F.obj (K.obj x)) := Aut.of ((t.app x).symm ≪≫ G.mapIso β.asIso ≪≫ t.app x)
    have hγ : pZ.map γ.asIso.hom = 𝟙 _ := by
      have hGβ : pZ.map (G.map β.asIso.hom) = 𝟙 (pZ.obj ((H ⋙ G).obj x)) := by
        have he := Functor.congr_hom hG β.asIso.hom
        simpa [hβ] using he
      exact map_inv_comp_comp_hom_eq_id pZ (t.app x) (G.map β.asIso.hom) hGβ
    obtain ⟨α, hα, hαF⟩ := inertiaPullbackComparison_exists_aut pX pZ F hF (K.obj x) γ hγ
    let m : J.obj x ⟶ J.obj x :=
      { hbase := 𝟙 (pT.obj x)
        a := β.asIso.hom
        b := α.asIso.hom
        ha := by
          apply IsHomLift.of_fac' pY _ _ (Functor.congr_obj hH x) (Functor.congr_obj hH x)
          simp [hβ]
        hb := by
          apply IsHomLift.of_fac' pX _ _ (Functor.congr_obj hK x) (Functor.congr_obj hK x)
          simp [hα]
        w := by
          change G.map β.asIso.hom ≫ (t.app x).hom = (t.app x).hom ≫ F.map α.asIso.hom
          rw [hαF]
          change G.map β.asIso.hom ≫ (t.app x).hom =
            (t.app x).hom ≫ (t.app x).inv ≫ G.map β.asIso.hom ≫ (t.app x).hom
          simp }
    have hma : IsIso m.a := β.asIso.isIso_hom
    have hmb : IsIso m.b := α.asIso.isIso_hom
    have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m hma hmb
    have hδ : J.map (hJ.preimageIso (asIso m)).hom = m := hJ.map_preimage _
    exact ⟨Aut.of (hJ.preimageIso (asIso m)), congrArg TwoFibreProductOver.Hom.hbase hδ,
      congrArg TwoFibreProductOver.Hom.a hδ⟩

end BaseChange

/-! ### Relative inertia commutes with base change ([Stacks, Tag 06PQ], left square)

For `F : X ⥤ Y` and `G : Y' ⥤ Y` over `C`, write `X' = X ×_Y Y'`. The canonical
comparison `Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'` is an equivalence over `C`, which is the
left square of [Stacks, Tag 06PQ] read in the (2,1)-category of categories over `C`.

The hypothesis `hF : F ⋙ pY = pX` — that `F` is a 1-morphism of categories over `C`,
which is part of the data of [Stacks, Tag 0040] — is what makes the conjugated
automorphism `δ⁻¹ ∘ α ∘ δ` vertical, and hence what makes the quasi-inverse exist. It
cannot be dropped: `CategoryTheory.RelativeInertia.not_baseChangeComparisonStatement`
refutes the hypothesis-free form. -/

namespace RelativeInertia

universe uY' vY'

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y' : Type uY'} [Category.{vY'} Y']
variable {Y : Type uY} [Category.{vY} Y]

/-! ## An extensionality lemma for the relative inertia

`CategoryTheory.RelativeInertia.obj_ext` compares the automorphisms across a transport by
the equality of the underlying objects. When the two underlying objects are *definitionally*
equal — which is the case for the round trip of the comparison below — the transports are
identities, but not syntactically, and every `simp` and `rw` on the transported statement
stalls. This variant takes the comparison as a `HEq` instead. -/

/-- Two objects of the relative inertia are equal as soon as their underlying objects are
equal and their automorphisms agree over that equality. -/
lemma obj_ext_heq {S : Type*} [Category S] {S' : Type*} [Category S'] {F : S ⥤ S'}
    {A B : RelativeInertia F} (ho : A.obj = B.obj) (ha : HEq A.auto.asIso.hom B.auto.asIso.hom) :
    A = B := by
  obtain ⟨ao, aa, ac⟩ := A; obtain ⟨bo, ba, bc⟩ := B
  simp only at ho; subst ho
  congr 1
  exact Aut.isoEquiv.injective (Iso.ext (eq_of_heq ha))

/-! ## The two categories of the left square -/

section Defs

variable (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (G : Y' ⥤ Y)

/-- The relative inertia `I_{X'/Y'}` of the base change `X' = X ×_Y Y'` relative to its
second projection `π' : X' ⥤ Y'`. -/
abbrev BaseChangeInertia : Type _ :=
  RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G)

/-- The 2-fibre product `I_{X/Y} ×_X X'` of categories over `C`, the target of the
comparison 1-morphism of the left square of Stacks 06PQ. -/
abbrev BaseChangeFibreProduct : Type _ :=
  TwoFibreProductOver (RelativeInertia.π F ⋙ pX)
    (TwoFibreProductOver.structureFunctor pX pY' pY F G) pX
    (RelativeInertia.π F) (TwoFibreProductOver.fst pX pY' pY F G)

/-- The structure functor `I_{X/Y} ×_X X' ⥤ C`. -/
abbrev BaseChangeFibreProduct.structureFunctor :
    BaseChangeFibreProduct pX pY' pY F G ⥤ C :=
  TwoFibreProductOver.structureFunctor (RelativeInertia.π F ⋙ pX)
    (TwoFibreProductOver.structureFunctor pX pY' pY F G) pX
    (RelativeInertia.π F) (TwoFibreProductOver.fst pX pY' pY F G)

/-! ## The comparison 1-morphism `Θ` -/

/-- For an object `(x', α')` of `I_{X'/Y'}`, the `X`-component of the automorphism `α'` is
an automorphism of the `X`-component of `x'`, since `α'` is an automorphism of `x'` and
composition in `X ×_Y Y'` is componentwise. -/
@[simps]
def baseChangeAutoX (A : BaseChangeInertia pX pY' pY F G) : Aut A.obj.x :=
  Aut.of
  { hom := A.auto.asIso.hom.a
    inv := A.auto.asIso.inv.a
    hom_inv_id := by
      have h : (A.auto.asIso.hom ≫ A.auto.asIso.inv).a = (𝟙 A.obj : A.obj ⟶ A.obj).a := by
        rw [A.auto.asIso.hom_inv_id]
      exact h.trans (by simp)
    inv_hom_id := by
      have h : (A.auto.asIso.inv ≫ A.auto.asIso.hom).a = (𝟙 A.obj : A.obj ⟶ A.obj).a := by
        rw [A.auto.asIso.inv_hom_id]
      exact h.trans (by simp) }

/-- **The linchpin of Stacks 06PQ.** For an object `(x', α')` of `I_{X'/Y'}` the
`X`-component `α` of `α'` satisfies `F α = id`.

The condition `π'(α') = id` says that the `Y'`-component of `α'` is the identity, so the
compatibility condition of a morphism of the 2-fibre product reads `F α ∘ β = β ∘ id = β`
with `β` the gluing isomorphism of `x'`; cancelling `β` gives `F α = id`. -/
lemma map_baseChangeAutoX_eq_id (A : BaseChangeInertia pX pY' pY F G) :
    F.map A.auto.asIso.hom.a = 𝟙 (F.obj A.obj.x) := by
  have hb : A.auto.asIso.hom.b = 𝟙 A.obj.y := A.cond
  have hw := A.auto.asIso.hom.w
  rw [hb, G.map_id, Category.comp_id] at hw
  rw [← cancel_mono A.obj.iso.hom, hw, Category.id_comp]

/-- The canonical comparison 1-morphism `Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'`. On objects it
sends `((U, x, y', β), (α, id))` to `(U, (x, α), (U, x, y', β), id)`, and on morphisms it
sends `φ` to the pair consisting of the `X`-component of `φ` and `φ` itself. -/
def toBaseChangeFibreProduct :
    BaseChangeInertia pX pY' pY F G ⥤ BaseChangeFibreProduct pX pY' pY F G where
  obj A :=
    { base := A.obj.base
      x := ⟨A.obj.x, baseChangeAutoX pX pY' pY F G A, map_baseChangeAutoX_eq_id pX pY' pY F G A⟩
      y := A.obj
      hx := A.obj.hx
      hy := rfl
      iso := Iso.refl _
      vertical := IsHomLift.id A.obj.hx }
  map {A B} φ :=
    { hbase := φ.hom.hbase
      a :=
        { hom := φ.hom.a
          comm := by
            have h : (φ.hom ≫ B.auto.asIso.hom).a = (A.auto.asIso.hom ≫ φ.hom).a := by rw [φ.comm]
            exact (show φ.hom.a ≫ B.auto.asIso.hom.a = A.auto.asIso.hom.a ≫ φ.hom.a by
              simpa using h) }
      b := φ.hom
      ha := (RelativeInertia.isHomLift_π_comp_iff (p := pX) φ.hom.hbase _).mpr φ.hom.ha
      hb := IsHomLift.of_fac' _ φ.hom.hbase φ.hom rfl rfl
        (show φ.hom.hbase = 𝟙 _ ≫ φ.hom.hbase ≫ 𝟙 _ by simp)
      w := show φ.hom.a ≫ 𝟙 B.obj.x = 𝟙 A.obj.x ≫ φ.hom.a by simp }
  map_id A := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact RelativeInertiaHom.ext (show (𝟙 A.obj : A.obj ⟶ A.obj).a = 𝟙 A.obj.x by simp)
    · exact (rfl : (𝟙 A.obj : A.obj ⟶ A.obj) = 𝟙 A.obj)
  map_comp f g := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact RelativeInertiaHom.ext (show (f.hom ≫ g.hom).a = f.hom.a ≫ g.hom.a by simp)
    · exact (rfl : (f ≫ g).hom = f.hom ≫ g.hom)

/-! ### The action of `Θ`, as `rfl`-lemmas

These give the projections of `Θ` their canonical spelling, which is what lets `simp` work
with the dependently typed fields of the 2-fibre product further down. -/

variable {pX pY' pY F G}

/-- The base object of `Θ (x', α')` is the base object of `x'`. -/
@[simp] lemma toBaseChangeFibreProduct_obj_base (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).base = A.obj.base := rfl

/-- The underlying object of the `I_{X/Y}`-component of `Θ (x', α')` is the `X`-component
of `x'`. -/
@[simp] lemma toBaseChangeFibreProduct_obj_x_obj (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).x.obj = A.obj.x := rfl

/-- The automorphism of the `I_{X/Y}`-component of `Θ (x', α')` is the `X`-component of
`α'`. -/
@[simp] lemma toBaseChangeFibreProduct_obj_x_auto_hom
    (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).x.auto.asIso.hom = A.auto.asIso.hom.a := rfl

/-- The inverse automorphism of the `I_{X/Y}`-component of `Θ (x', α')`. -/
@[simp] lemma toBaseChangeFibreProduct_obj_x_auto_inv
    (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).x.auto.asIso.inv = A.auto.asIso.inv.a := rfl

/-- The `X'`-component of `Θ (x', α')` is `x'`. -/
@[simp] lemma toBaseChangeFibreProduct_obj_y (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).y = A.obj := rfl

/-- The gluing datum of `Θ (x', α')` is the identity. -/
@[simp] lemma toBaseChangeFibreProduct_obj_iso_hom
    (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).iso.hom = 𝟙 A.obj.x := rfl

/-- The inverse gluing datum of `Θ (x', α')` is the identity. -/
@[simp] lemma toBaseChangeFibreProduct_obj_iso_inv
    (A : BaseChangeInertia pX pY' pY F G) :
    ((toBaseChangeFibreProduct pX pY' pY F G).obj A).iso.inv = 𝟙 A.obj.x := rfl

/-- The base morphism of `Θ φ`. -/
@[simp] lemma toBaseChangeFibreProduct_map_hbase
    {A B : BaseChangeInertia pX pY' pY F G} (φ : A ⟶ B) :
    ((toBaseChangeFibreProduct pX pY' pY F G).map φ).hbase = φ.hom.hbase := rfl

/-- The `I_{X/Y}`-component of `Θ φ` is the `X`-component of `φ`. -/
@[simp] lemma toBaseChangeFibreProduct_map_a_hom
    {A B : BaseChangeInertia pX pY' pY F G} (φ : A ⟶ B) :
    ((toBaseChangeFibreProduct pX pY' pY F G).map φ).a.hom = φ.hom.a := rfl

/-- The `X'`-component of `Θ φ` is `φ` itself. -/
@[simp] lemma toBaseChangeFibreProduct_map_b
    {A B : BaseChangeInertia pX pY' pY F G} (φ : A ⟶ B) :
    ((toBaseChangeFibreProduct pX pY' pY F G).map φ).b = φ.hom := rfl

variable (pX pY' pY F G)

/-- `Θ` is a 1-morphism over `C`. -/
lemma toBaseChangeFibreProduct_comp_structureFunctor :
    toBaseChangeFibreProduct pX pY' pY F G ⋙
        BaseChangeFibreProduct.structureFunctor pX pY' pY F G
      = RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
          TwoFibreProductOver.structureFunctor pX pY' pY F G :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ φ =>
    show φ.hom.hbase = 𝟙 _ ≫ φ.hom.hbase ≫ 𝟙 _ by simp)

end Defs

/-! ## Verticality

The one place where `hF : F ⋙ pY = pX` is used. -/

section Vertical

variable {pX : X ⥤ C} {pY : Y ⥤ C} {F : X ⥤ Y}

/-- If `F` is a 1-morphism of categories over `C`, an endomorphism killed by `F` is
vertical: `F γ = id` implies `pX γ = id`. -/
lemma map_eq_id_of_comp_eq (hF : F ⋙ pY = pX) {x : X} (γ : x ⟶ x)
    (hγ : F.map γ = 𝟙 (F.obj x)) : pX.map γ = 𝟙 (pX.obj x) := by
  rw [Functor.congr_hom hF.symm γ]
  simp [hγ]

end Vertical

/-! ## The quasi-inverse of `Θ` -/

section Inverse

variable (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (G : Y' ⥤ Y)

/-- The gluing isomorphism `δ : x ≅ x'_X` of an object `P = (U, (x, α), x', δ)` of
`I_{X/Y} ×_X X'`, with its endpoints spelled as the underlying object of the
`I_{X/Y}`-component and the `X`-component of the `X'`-component of `P`.

This is `P.iso` with its type rewritten. The structure field has type
`(π F).obj P.x ≅ (fst …).obj P.y`, which is the same type, but the difference in spelling
makes the composites below not type-correct at `instances` transparency, which in turn
breaks every `rw` and `simp` that would touch them. -/
def glue (P : BaseChangeFibreProduct pX pY' pY F G) : P.x.obj ≅ P.y.x where
  hom := P.iso.hom
  inv := P.iso.inv
  hom_inv_id := P.iso.hom_inv_id
  inv_hom_id := P.iso.inv_hom_id

variable {pX pY' pY F G}

/-- The gluing isomorphism is vertical over the base. -/
lemma glue_vertical (P : BaseChangeFibreProduct pX pY' pY F G) :
    pX.IsHomLift (𝟙 P.base) (glue pX pY' pY F G P).hom :=
  P.vertical

/-- The two components of a morphism of `I_{X/Y} ×_X X'` are compatible with the gluing
isomorphisms: this is the `w` field, with the endpoints respelled. -/
lemma glue_w {P Q : BaseChangeFibreProduct pX pY' pY F G} (u : P ⟶ Q) :
    u.a.hom ≫ (glue pX pY' pY F G Q).hom = (glue pX pY' pY F G P).hom ≫ u.b.a :=
  u.w

variable (pX pY' pY F G)

/-- The endomorphism `(δ⁻¹ ∘ γ ∘ δ, id)` of the object `x'` of `X ×_Y Y'`, attached to an
object `P = (U, (x, α), x', δ)` of `I_{X/Y} ×_X X'` and an endomorphism `γ` of `x` which is
killed by `F` and vertical. -/
@[simps]
def conjugateHom (P : BaseChangeFibreProduct pX pY' pY F G) (γ : P.x.obj ⟶ P.x.obj)
    (hγ : F.map γ = 𝟙 (F.obj P.x.obj)) (hv : pX.map γ = 𝟙 (pX.obj P.x.obj)) :
    P.y ⟶ P.y where
  hbase := 𝟙 P.y.base
  a := (glue pX pY' pY F G P).inv ≫ γ ≫ (glue pX pY' pY F G P).hom
  b := 𝟙 P.y.y
  ha := by
    refine IsHomLift.of_fac' pX (𝟙 P.y.base) _ P.y.hx P.y.hx ?_
    rw [pX.map_comp, pX.map_comp, hv, Category.id_comp, ← pX.map_comp,
      (glue pX pY' pY F G P).inv_hom_id, pX.map_id]
    simp
  hb := IsHomLift.id P.y.hy
  w := by
    rw [F.map_comp, F.map_comp, hγ, Category.id_comp, ← F.map_comp,
      (glue pX pY' pY F G P).inv_hom_id, F.map_id, Category.id_comp, G.map_id,
      Category.comp_id]

/-- The automorphism `(δ⁻¹ ∘ α ∘ δ, id)` of `x'` attached to an object
`P = (U, (x, α), x', δ)` of `I_{X/Y} ×_X X'`. -/
@[simps]
def conjugateAuto (hF : F ⋙ pY = pX) (P : BaseChangeFibreProduct pX pY' pY F G) :
    Aut P.y :=
  Aut.of
  { hom := conjugateHom pX pY' pY F G P P.x.auto.asIso.hom P.x.cond
      (map_eq_id_of_comp_eq hF _ P.x.cond)
    inv := conjugateHom pX pY' pY F G P P.x.auto.asIso.inv P.x.cond_inv
      (map_eq_id_of_comp_eq hF _ P.x.cond_inv)
    hom_inv_id := by
      have h : P.x.auto.asIso.hom ≫ P.x.auto.asIso.inv = 𝟙 P.x.obj := P.x.auto.asIso.hom_inv_id
      refine TwoFibreProductOver.Hom.ext' ?_ ?_ <;> simp [reassoc_of% h]
    inv_hom_id := by
      have h : P.x.auto.asIso.inv ≫ P.x.auto.asIso.hom = 𝟙 P.x.obj := P.x.auto.asIso.inv_hom_id
      refine TwoFibreProductOver.Hom.ext' ?_ ?_ <;> simp [reassoc_of% h] }

/-- The quasi-inverse `I_{X/Y} ×_X X' ⥤ I_{X'/Y'}` of `Θ`: send `(U, (x, α), x', δ)` to
`(x', (δ⁻¹ ∘ α ∘ δ, id))`, and a morphism to its `X'`-component. -/
def fromBaseChangeFibreProduct (hF : F ⋙ pY = pX) :
    BaseChangeFibreProduct pX pY' pY F G ⥤ BaseChangeInertia pX pY' pY F G where
  obj P := ⟨P.y, conjugateAuto pX pY' pY F G hF P, rfl⟩
  map {P Q} u :=
    { hom := u.b
      comm := by
        refine TwoFibreProductOver.Hom.ext' ?_ ?_
        · have hb : u.b.a =
              (glue pX pY' pY F G P).inv ≫ u.a.hom ≫ (glue pX pY' pY F G Q).hom := by
            rw [glue_w u, Iso.inv_hom_id_assoc]
          have hcomm : u.a.hom ≫ Q.x.auto.asIso.hom = P.x.auto.asIso.hom ≫ u.a.hom := u.a.comm
          refine (show u.b.a ≫ ((glue pX pY' pY F G Q).inv ≫ Q.x.auto.asIso.hom
                ≫ (glue pX pY' pY F G Q).hom)
              = ((glue pX pY' pY F G P).inv ≫ P.x.auto.asIso.hom
                ≫ (glue pX pY' pY F G P).hom) ≫ u.b.a from ?_).trans (by simp)
          rw [hb]
          simp [reassoc_of% hcomm]
        · simp }
  map_id P := RelativeInertiaHom.ext (rfl : (𝟙 P : P ⟶ P).b = 𝟙 P.y)
  map_comp u v := RelativeInertiaHom.ext (rfl : (u ≫ v).b = u.b ≫ v.b)

variable {pX pY' pY F G}

/-- The underlying object of `Θ⁻¹ P` is the `X'`-component of `P`. -/
@[simp] lemma fromBaseChangeFibreProduct_obj_obj (hF : F ⋙ pY = pX)
    (P : BaseChangeFibreProduct pX pY' pY F G) :
    ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P).obj = P.y := rfl

/-- The automorphism of `Θ⁻¹ P` is the conjugated automorphism. -/
@[simp] lemma fromBaseChangeFibreProduct_obj_auto (hF : F ⋙ pY = pX)
    (P : BaseChangeFibreProduct pX pY' pY F G) :
    ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P).auto
      = conjugateAuto pX pY' pY F G hF P := rfl

/-- `Θ⁻¹` takes the `X'`-component on morphisms. -/
@[simp] lemma fromBaseChangeFibreProduct_map_hom (hF : F ⋙ pY = pX)
    {P Q : BaseChangeFibreProduct pX pY' pY F G} (u : P ⟶ Q) :
    ((fromBaseChangeFibreProduct pX pY' pY F G hF).map u).hom = u.b := rfl

/-- The quasi-inverse is a 1-morphism over `C`. -/
lemma fromBaseChangeFibreProduct_comp_structureFunctor (hF : F ⋙ pY = pX) :
    fromBaseChangeFibreProduct pX pY' pY F G hF ⋙
        (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
          TwoFibreProductOver.structureFunctor pX pY' pY F G)
      = BaseChangeFibreProduct.structureFunctor pX pY' pY F G := by
  refine CategoryTheory.Functor.ext (fun P => P.hy) (fun P Q u => ?_)
  have := u.hb
  exact IsHomLift.fac' (TwoFibreProductOver.structureFunctor pX pY' pY F G) u.hbase u.b

/-! ## Unit and counit -/

/-- The conjugated automorphism of `Θ (x', α')` is `α'` again: the gluing datum of
`Θ (x', α')` is the identity, so the conjugation is trivial on the `X`-component, and the
`Y'`-component of `α'` is the identity by the defining condition of `I_{X'/Y'}`. -/
lemma conjugateAuto_toBaseChangeFibreProduct (hF : F ⋙ pY = pX)
    (A : BaseChangeInertia pX pY' pY F G) :
    (conjugateAuto pX pY' pY F G hF
        ((toBaseChangeFibreProduct pX pY' pY F G).obj A)).asIso.hom = A.auto.asIso.hom := by
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · exact (show (glue pX pY' pY F G ((toBaseChangeFibreProduct pX pY' pY F G).obj A)).inv
        ≫ ((toBaseChangeFibreProduct pX pY' pY F G).obj A).x.auto.asIso.hom
        ≫ (glue pX pY' pY F G ((toBaseChangeFibreProduct pX pY' pY F G).obj A)).hom
      = A.auto.asIso.hom.a by simp [glue])
  · exact (show (𝟙 A.obj.y : A.obj.y ⟶ A.obj.y) = A.auto.asIso.hom.b from A.cond.symm)

/-- `Θ⁻¹ ∘ Θ` is the identity functor: the round trip rebuilds `(x', α')` from `x'` and the
`X`-component of `α'`, the `Y'`-component of `α'` having been the identity to begin with and
the base component of a morphism of `X ×_Y Y'` being determined by its components. -/
lemma toBaseChangeFibreProduct_comp_fromBaseChangeFibreProduct (hF : F ⋙ pY = pX) :
    𝟭 (BaseChangeInertia pX pY' pY F G)
      = toBaseChangeFibreProduct pX pY' pY F G ⋙
          fromBaseChangeFibreProduct pX pY' pY F G hF := by
  refine CategoryTheory.Functor.ext (fun A => ?_) (fun A B φ => ?_)
  · exact obj_ext_heq rfl
      (heq_of_eq (conjugateAuto_toBaseChangeFibreProduct hF A).symm)
  · refine RelativeInertiaHom.ext ?_
    simp only [Functor.id_map, RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom]
    exact (show φ.hom = 𝟙 A.obj ≫ φ.hom ≫ 𝟙 B.obj by simp)

/-- The unit isomorphism `𝟭 ≅ Θ ⋙ Θ⁻¹`. -/
def baseChangeUnitIso (hF : F ⋙ pY = pX) :
    𝟭 (BaseChangeInertia pX pY' pY F G) ≅
      toBaseChangeFibreProduct pX pY' pY F G ⋙
        fromBaseChangeFibreProduct pX pY' pY F G hF :=
  eqToIso (toBaseChangeFibreProduct_comp_fromBaseChangeFibreProduct hF)

/-- The counit isomorphism `Θ⁻¹ ⋙ Θ ≅ 𝟭`. At `P = (U, (x, α), x', δ)` it is the pair
`(δ⁻¹, id)`: the inverse gluing isomorphism in the `I_{X/Y}`-component and the identity of
`x'` in the `X'`-component. -/
def baseChangeCounitIso (hF : F ⋙ pY = pX) :
    fromBaseChangeFibreProduct pX pY' pY F G hF ⋙
        toBaseChangeFibreProduct pX pY' pY F G
      ≅ 𝟭 (BaseChangeFibreProduct pX pY' pY F G) :=
  NatIso.ofComponents
    (fun P =>
      { hom :=
          { hbase := eqToHom P.hy
            a :=
              { hom := (glue pX pY' pY F G P).inv
                comm := by simp }
            b := 𝟙 P.y
            ha := by
              refine (RelativeInertia.isHomLift_π_comp_iff (p := pX) (eqToHom P.hy) _).mpr ?_
              have hv := glue_vertical P
              have hinv : pX.IsHomLift (𝟙 P.base) (glue pX pY' pY F G P).inv := inferInstance
              have h := (IsHomLift.lift_eqToHom_comp_iff pX (𝟙 P.base)
                (glue pX pY' pY F G P).inv P.hy).mpr hinv
              simpa using h
            hb := IsHomLift.id_lift_eqToHom_domain P.hy rfl
            w := show (glue pX pY' pY F G P).inv ≫ (glue pX pY' pY F G P).hom
                = 𝟙 P.y.x ≫ 𝟙 P.y.x by simp }
        inv :=
          { hbase := eqToHom P.hy.symm
            a :=
              { hom := (glue pX pY' pY F G P).hom
                comm := by simp }
            b := 𝟙 P.y
            ha := by
              refine (RelativeInertia.isHomLift_π_comp_iff (p := pX)
                (eqToHom P.hy.symm) _).mpr ?_
              have hv := glue_vertical P
              have h := (IsHomLift.lift_comp_eqToHom_iff pX (𝟙 P.base)
                (glue pX pY' pY F G P).hom P.hy.symm).mpr hv
              simpa using h
            hb := IsHomLift.id_lift_eqToHom_domain P.hy.symm P.hy
            w := show (glue pX pY' pY F G P).hom ≫ 𝟙 P.y.x
                = (glue pX pY' pY F G P).hom ≫ 𝟙 P.y.x from rfl }
        hom_inv_id := by
          refine TwoFibreProductOver.Hom.ext' ?_ ?_
          · exact RelativeInertiaHom.ext
              (show (glue pX pY' pY F G P).inv ≫ (glue pX pY' pY F G P).hom
                = 𝟙 P.y.x by simp)
          · exact (show 𝟙 P.y ≫ 𝟙 P.y = 𝟙 P.y by simp)
        inv_hom_id := by
          refine TwoFibreProductOver.Hom.ext' ?_ ?_
          · exact RelativeInertiaHom.ext
              (show (glue pX pY' pY F G P).hom ≫ (glue pX pY' pY F G P).inv
                = 𝟙 P.x.obj by simp)
          · exact (show 𝟙 P.y ≫ 𝟙 P.y = 𝟙 P.y by simp) })
    (by
      intro P Q u
      refine TwoFibreProductOver.Hom.ext' ?_ ?_
      · refine RelativeInertiaHom.ext ?_
        refine (show u.b.a ≫ (glue pX pY' pY F G Q).inv
            = (glue pX pY' pY F G P).inv ≫ u.a.hom from ?_)
        rw [Iso.comp_inv_eq, Category.assoc, glue_w u, Iso.inv_hom_id_assoc]
      · exact (show u.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ u.b by simp))

/-- The triangle identity for `Θ ⊣ Θ⁻¹`. The unit is an `eqToHom`, hence an identity up to
transport, and the counit component at `Θ A` is an identity because the gluing datum of
`Θ A` is the identity. -/
lemma baseChange_unitIso_comp (hF : F ⋙ pY = pX)
    (A : BaseChangeInertia pX pY' pY F G) :
    (toBaseChangeFibreProduct pX pY' pY F G).map ((baseChangeUnitIso hF).hom.app A) ≫
        (baseChangeCounitIso hF).hom.app
          ((toBaseChangeFibreProduct pX pY' pY F G).obj A)
      = 𝟙 ((toBaseChangeFibreProduct pX pY' pY F G).obj A) := by
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · refine RelativeInertiaHom.ext ?_
    simp [baseChangeUnitIso, baseChangeCounitIso, glue]
    rfl
  · simp [baseChangeUnitIso, baseChangeCounitIso]
    rfl

/-- Every unit component lies over an identity of `C`. -/
lemma baseChangeUnit_over (hF : F ⋙ pY = pX) (A : BaseChangeInertia pX pY' pY F G) :
    (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
        TwoFibreProductOver.structureFunctor pX pY' pY F G).map
      ((baseChangeUnitIso hF).hom.app A) = eqToHom (by
        have h1 : (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
              TwoFibreProductOver.structureFunctor pX pY' pY F G).obj A
            = (BaseChangeFibreProduct.structureFunctor pX pY' pY F G).obj
                ((toBaseChangeFibreProduct pX pY' pY F G).obj A) :=
          (Functor.congr_obj
            (toBaseChangeFibreProduct_comp_structureFunctor pX pY' pY F G) A).symm
        have h2 : (BaseChangeFibreProduct.structureFunctor pX pY' pY F G).obj
              ((toBaseChangeFibreProduct pX pY' pY F G).obj A)
            = (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
                TwoFibreProductOver.structureFunctor pX pY' pY F G).obj
              ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj
                ((toBaseChangeFibreProduct pX pY' pY F G).obj A)) :=
          (Functor.congr_obj
            (fromBaseChangeFibreProduct_comp_structureFunctor hF)
            ((toBaseChangeFibreProduct pX pY' pY F G).obj A)).symm
        exact h1.trans h2) := by
  simp [baseChangeUnitIso]
  rfl

/-- Every counit component lies over an identity of `C`: its base component is the
canonical transport isomorphism of the base objects. -/
lemma baseChangeCounit_over (hF : F ⋙ pY = pX)
    (P : BaseChangeFibreProduct pX pY' pY F G) :
    (BaseChangeFibreProduct.structureFunctor pX pY' pY F G).map
      ((baseChangeCounitIso hF).hom.app P) = eqToHom (by
        have h1 : (BaseChangeFibreProduct.structureFunctor pX pY' pY F G).obj
              ((toBaseChangeFibreProduct pX pY' pY F G).obj
                ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P))
            = (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
                TwoFibreProductOver.structureFunctor pX pY' pY F G).obj
              ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P) :=
          Functor.congr_obj
            (toBaseChangeFibreProduct_comp_structureFunctor pX pY' pY F G)
            ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P)
        have h2 : (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
              TwoFibreProductOver.structureFunctor pX pY' pY F G).obj
              ((fromBaseChangeFibreProduct pX pY' pY F G hF).obj P)
            = (BaseChangeFibreProduct.structureFunctor pX pY' pY F G).obj P :=
          Functor.congr_obj (fromBaseChangeFibreProduct_comp_structureFunctor hF) P
        exact h1.trans h2) := by
  simp [baseChangeCounitIso]
  rfl

/-! ## Main statements -/

/-- **Stacks 06PQ, left square, over a base category.** The canonical comparison
1-morphism `Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'` is an equivalence of categories **over `C`**,
where `X' = X ×_Y Y'`. Equivalently, the left square of Stacks 06PQ is a 2-fibre product
square in the (2,1)-category of categories over `C`.

The hypothesis `hF : F ⋙ pY = pX` says that `F` is a 1-morphism of categories over `C`; it
is necessary, see the module docstring. -/
theorem isEquivalenceOver_toBaseChangeFibreProduct (hF : F ⋙ pY = pX) :
    Nonempty (IsEquivalenceOver
      (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
        TwoFibreProductOver.structureFunctor pX pY' pY F G)
      (BaseChangeFibreProduct.structureFunctor pX pY' pY F G)
      (toBaseChangeFibreProduct pX pY' pY F G)) :=
  ⟨{ inverse := fromBaseChangeFibreProduct pX pY' pY F G hF
     unitIso := baseChangeUnitIso hF
     counitIso := baseChangeCounitIso hF
     functor_unitIso_comp := baseChange_unitIso_comp hF
     functor_over := toBaseChangeFibreProduct_comp_structureFunctor pX pY' pY F G
     inverse_over := fromBaseChangeFibreProduct_comp_structureFunctor hF
     unit_over := baseChangeUnit_over hF
     counit_over := baseChangeCounit_over hF }⟩

/-- Consequence: the comparison functor `Θ` is an equivalence of the underlying
categories. -/
theorem toBaseChangeFibreProduct_isEquivalence (hF : F ⋙ pY = pX) :
    (toBaseChangeFibreProduct pX pY' pY F G).IsEquivalence :=
  (isEquivalenceOver_toBaseChangeFibreProduct (pY' := pY') (G := G) hF).some.isEquivalence

end Inverse

/-- **Stacks 06PQ, left square**, in the existential shape, with the
necessary hypothesis `hF : F ⋙ pY = pX` included: there is a comparison 1-morphism
`Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'` whose action on objects, automorphisms, gluing datum and
morphisms is the canonical one, and which is an equivalence over `C`. -/
theorem exists_baseChangeComparison (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (G : Y' ⥤ Y) (hF : F ⋙ pY = pX) :
    ∃ Θ : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G) ⥤
        BaseChangeFibreProduct pX pY' pY F G,
      (∀ A : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G),
        (Θ.obj A).x.obj = A.obj.x ∧
        HEq (Θ.obj A).x.auto.asIso.hom A.auto.asIso.hom.a ∧
        (Θ.obj A).y = A.obj ∧
        HEq (Θ.obj A).iso.hom (𝟙 A.obj.x)) ∧
      (∀ {A B : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G)} (φ : A ⟶ B),
        HEq (Θ.map φ).a.hom φ.hom.a ∧
        HEq (Θ.map φ).b φ.hom) ∧
      Nonempty (IsEquivalenceOver
        (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
          TwoFibreProductOver.structureFunctor pX pY' pY F G)
        (TwoFibreProductOver.structureFunctor (RelativeInertia.π F ⋙ pX)
          (TwoFibreProductOver.structureFunctor pX pY' pY F G) pX
          (RelativeInertia.π F) (TwoFibreProductOver.fst pX pY' pY F G)) Θ) :=
  ⟨toBaseChangeFibreProduct pX pY' pY F G,
    fun _ => ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩,
    fun _ => ⟨HEq.rfl, HEq.rfl⟩,
    isEquivalenceOver_toBaseChangeFibreProduct hF⟩

end RelativeInertia

end CategoryTheory

end
