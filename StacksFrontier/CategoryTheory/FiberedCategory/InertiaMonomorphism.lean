module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare

/-!
# The inertia of a fully faithful morphism is a base change (Stacks 06R5)

Fix a category `C` and categories `pX : X ⥤ C` and `pY : Y ⥤ C` over it, and let
`F : X ⥤ Y` be a morphism over `C`, so `F ⋙ pY = pX`. Stacks 06R5 says that when `F` is a
monomorphism of algebraic stacks the square with rows `I_X → I_Y` and `X → Y` is cartesian,
that is, `I_X` is the 2-fibre product `I_Y ×_Y X`. A monomorphism of algebraic stacks is
fully faithful, and full faithfulness is all the argument uses, so that is the hypothesis
taken here: the statement is more general than the source's and therefore no weaker.

As in the companion Stacks 04Z6 (`InertiaSquare.lean`), the assertion is rendered by
comparing with the *explicit* 2-fibre product of categories over `C`
(`CategoryTheory.TwoFibreProductOver`): the canonical comparison functor
`inertiaPullbackComparison` from `I_X` to `I_Y ×_Y X` is an equivalence **over `C`**, with
quasi-inverse, unit and counit all over `C`. That is what `IsEquivalenceOver` records, and
it certifies the *given* comparison functor rather than the bare existence of some
equivalence.

The quasi-inverse sends an object of the 2-fibre product — a point `y` of `X`, a point `x`
of `Y` carrying an automorphism `α` over the identity, and a vertical isomorphism
`ι : x ≅ F y` — to the automorphism of `y` whose image under `F` is `ι⁻¹ ≫ α ≫ ι`. Full
faithfulness is used exactly twice: to take that preimage, and to check its naturality.

## Main definitions

* `CategoryTheory.inertiaPullbackComparison`: the canonical functor from `I_X` to the
  2-fibre product of `I_Y` with `X` over `Y`.

## Main results

* `CategoryTheory.inertiaPullbackComparison_isEquivalenceOver`: **Stacks 06R5**. That
  comparison functor is an equivalence over `C`.

## References

* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
-/

@[expose] public section

open CategoryTheory

universe uC vC uX vX uY vY

namespace CategoryTheory

/- The two structure functors of this square are semireducible `def`s whose unfolding the
`eqToHom` bookkeeping below depends on:

* `RelativeInertia.π` sends `(x, α)` to `x`, so `(RelativeInertia.π p).obj A` and `A.obj` are
  the same object only after it is unfolded. The coherence goals produced by
  `Functor.ext`/`IsHomLift` are `eqToHom` composites whose proofs are `rfl` exactly then;
* `TwoFibreProductOver.structureFunctor` likewise sends `P` to `P.base`.

Both are needed at `implicit` transparency rather than merely at default transparency,
because the goals are discharged by `simp`/`rw`, whose `kabstract` works at that level.
Naming the two definitions here is what replaces a file-scope
`backward.isDefEq.respectTransparency`, which widened defeq for every definition in scope. -/
attribute [local implicit_reducible] RelativeInertia.π
  TwoFibreProductOver.structureFunctor

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]
variable (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
  (hF : F ⋙ pY = pX)

/-- The canonical comparison from `I_X` to `I_Y ×_Y X` over `C`. -/
public def inertiaPullbackComparison :
    RelativeInertia pX ⥤
      TwoFibreProductOver (RelativeInertia.toBase pY) pX pY
        (RelativeInertia.π pY) F where
  obj A :=
    { base := pX.obj A.obj
      x := (RelativeInertia.functoriality pX pY F hF).obj A
      y := A.obj
      hx := Functor.congr_obj (RelativeInertia.functoriality_comp_toBase pX pY F hF) A
      hy := rfl
      iso := Iso.refl (F.obj A.obj)
      vertical := by
        change pY.IsHomLift (𝟙 (pX.obj A.obj)) (𝟙 (F.obj A.obj))
        exact IsHomLift.id (Functor.congr_obj hF A.obj) }
  map {A B} φ :=
    { hbase := pX.map φ.hom
      a := (RelativeInertia.functoriality pX pY F hF).map φ
      b := φ.hom
      ha := (RelativeInertia.isHomLift_π_comp_iff (p := pY)
          (pX.map φ.hom) ((RelativeInertia.functoriality pX pY F hF).map φ)).mpr
        (Functor.isHomLift_map_of_comp_eq hF (pX.map φ.hom) φ.hom)
      hb := IsHomLift.map pX φ.hom
      w := by simp [RelativeInertia.functoriality] }
  map_id A := by apply TwoFibreProductOver.Hom.ext' <;> simp
  map_comp φ ψ := by apply TwoFibreProductOver.Hom.ext' <;> simp

private abbrev inertiaPullbackProduct
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) :=
  TwoFibreProductOver (RelativeInertia.toBase pY) pX pY (RelativeInertia.π pY) F

private noncomputable def inertiaPullbackTransportedAuto
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (P : inertiaPullbackProduct pX pY F) : Aut (F.obj P.y) :=
  let e : P.x.obj ≅ F.obj P.y := P.iso
  let α : P.x.obj ≅ P.x.obj := P.x.auto
  e.symm ≪≫ α ≪≫ e

/-- The conjugated automorphism, in terms of the data it is built from. Rewriting with this
named equation is what lets the calculations below be done on `P.iso` and `P.x.auto`
themselves: unfolding the definition instead leaves the vertical isomorphism at its own
type `(RelativeInertia.π pY).obj P.x ≅ F.obj P.y`, against which the `Iso` simp set does not
fire even though that type is `P.x.obj ≅ F.obj P.y`. -/
private lemma inertiaPullbackTransportedAuto_hom
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (P : inertiaPullbackProduct pX pY F) :
    (inertiaPullbackTransportedAuto pX pY F P).hom =
      P.iso.inv ≫ P.x.auto.hom ≫ P.iso.hom := rfl

private noncomputable def inertiaPullbackAuto
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (hFF : F.FullyFaithful) (P : inertiaPullbackProduct pX pY F) : Aut P.y :=
  hFF.preimageIso (inertiaPullbackTransportedAuto pX pY F P)

private lemma inertiaPullbackAuto_map
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (hFF : F.FullyFaithful) (P : inertiaPullbackProduct pX pY F) :
    F.map (inertiaPullbackAuto pX pY F hFF P).hom =
      (inertiaPullbackTransportedAuto pX pY F P).hom := by
  simp [inertiaPullbackAuto, Functor.FullyFaithful.preimageIso]

private lemma inertiaPullbackAuto_cond
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) (P : inertiaPullbackProduct pX pY F) :
    pX.map (inertiaPullbackAuto pX pY F hFF P).hom = 𝟙 (pX.obj P.y) := by
  cases hF
  let β : P.y ≅ P.y := inertiaPullbackAuto (F ⋙ pY) pY F hFF P
  have hx : pY.obj P.x.obj = P.base := by simpa using P.hx
  have hy : pY.obj (F.obj P.y) = P.base := by simpa using P.hy
  let hbase : pY.obj P.x.obj = pY.obj (F.obj P.y) := hx.trans hy.symm
  let _ : pY.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hhom : pY.map P.iso.hom = eqToHom hbase := by
    rw [IsHomLift.fac' pY (𝟙 P.base) P.iso.hom]
    simp [hy]
  have hmapIso : pY.mapIso P.iso = eqToIso hbase := Iso.ext hhom
  have hinv : pY.map P.iso.inv = (eqToIso hbase).inv := by
    simpa only [Functor.mapIso_inv] using congrArg Iso.inv hmapIso
  have hβmap : F.map β.hom = (inertiaPullbackTransportedAuto (F ⋙ pY) pY F P).hom := by
    simpa [β] using inertiaPullbackAuto_map (F ⋙ pY) pY F hFF P
  have hconjmap : pY.map (inertiaPullbackTransportedAuto (F ⋙ pY) pY F P).hom =
      𝟙 (pY.obj (F.obj P.y)) := by
    dsimp [inertiaPullbackTransportedAuto]
    let e : P.x.obj ≅ F.obj P.y := by simpa using P.iso
    let α : P.x.obj ≅ P.x.obj := P.x.auto
    have hhinv : pY.map e.inv = (eqToIso hbase).inv := by simpa [e] using hinv
    have hhhom : pY.map e.hom = eqToHom hbase := by simpa [e] using hhom
    calc
      pY.map (e.symm ≪≫ α ≪≫ e).hom =
          pY.map e.inv ≫ pY.map α.hom ≫ pY.map e.hom := by simp [Functor.map_comp]
      _ = 𝟙 (pY.obj (F.obj P.y)) := by
        rw [hhinv, hhhom]
        have hαcond : pY.map α.hom = 𝟙 (pY.obj P.x.obj) := by
          simpa [α] using P.x.cond
        rw [hαcond]
        simp [hbase, hy]
  exact (congrArg pY.map hβmap).trans hconjmap

/-- The commutation of a morphism of the 2-fibre product with the vertical isomorphisms,
with the isomorphisms inverted. -/
private lemma inertiaPullbackHom_map_comp_iso_inv
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) {P Q : inertiaPullbackProduct pX pY F}
    (u : P ⟶ Q) : F.map u.b ≫ Q.iso.inv = P.iso.inv ≫ u.a.hom := by
  have hw : u.a.hom ≫ Q.iso.hom = P.iso.hom ≫ F.map u.b := by simpa using u.w
  rw [Iso.comp_inv_eq, Category.assoc, hw, Iso.inv_hom_id_assoc]

private lemma inertiaPullbackAuto_naturality
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (_hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) {P Q : inertiaPullbackProduct pX pY F} (u : P ⟶ Q) :
    u.b ≫ (inertiaPullbackAuto pX pY F hFF Q).hom =
      (inertiaPullbackAuto pX pY F hFF P).hom ≫ u.b := by
  apply hFF.map_injective
  have hw : u.a.hom ≫ Q.iso.hom = P.iso.hom ≫ F.map u.b := by simpa using u.w
  rw [Functor.map_comp, Functor.map_comp, inertiaPullbackAuto_map pX pY F hFF Q,
    inertiaPullbackAuto_map pX pY F hFF P, inertiaPullbackTransportedAuto_hom,
    inertiaPullbackTransportedAuto_hom, reassoc_of% inertiaPullbackHom_map_comp_iso_inv pX pY F u,
    reassoc_of% u.a.comm, hw]
  simp only [Category.assoc]

private noncomputable def inertiaPullbackInverse
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) : inertiaPullbackProduct pX pY F ⥤ RelativeInertia pX where
  obj P := ⟨P.y, inertiaPullbackAuto pX pY F hFF P,
    inertiaPullbackAuto_cond pX pY F hF hFF P⟩
  map {P Q} u := ⟨u.b, inertiaPullbackAuto_naturality pX pY F hF hFF u⟩
  map_id P := by apply RelativeInertiaHom.ext; simp
  map_comp u v := by apply RelativeInertiaHom.ext; simp

/- Everything from here on compares the round trip `comparison ⋙ inverse` with the identity,
so the coherence goals are `eqToHom`s and `eqToIso`s whose proofs are `rfl` only once the
comparison and its quasi-inverse are unfolded to their `obj`/`map` fields. Those four
definitions are named here, rather than widening defeq for the whole file. -/
attribute [local implicit_reducible] inertiaPullbackComparison inertiaPullbackInverse
  inertiaPullbackTransportedAuto inertiaPullbackAuto

private lemma inertiaPullbackInverse_compare_auto_hom
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) (A : RelativeInertia pX) :
    ((inertiaPullbackInverse pX pY F hF hFF).obj
      ((inertiaPullbackComparison pX pY F hF).obj A)).auto.hom = A.auto.hom := by
  cases A with
  | mk x α hα =>
    dsimp [inertiaPullbackInverse]
    apply hFF.map_injective
    rw [inertiaPullbackAuto_map pX pY F hFF
      ((inertiaPullbackComparison pX pY F hF).obj
        ({ obj := x, auto := α, cond := hα } : RelativeInertia pX))]
    simp [inertiaPullbackTransportedAuto_hom, inertiaPullbackComparison,
      RelativeInertia.functoriality]
    rfl

private lemma inertiaPullbackInverse_compare_obj_eq
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) (A : RelativeInertia pX) :
    (inertiaPullbackInverse pX pY F hF hFF).obj
        ((inertiaPullbackComparison pX pY F hF).obj A) = A := by
  cases A with
  | mk x α hα =>
    dsimp [inertiaPullbackInverse, inertiaPullbackComparison]
    exact RelativeInertia.obj_ext (F := pX)
      (A := (inertiaPullbackInverse pX pY F hF hFF).obj
        ((inertiaPullbackComparison pX pY F hF).obj
          ({ obj := x, auto := α, cond := hα } : RelativeInertia pX)))
      (B := ({ obj := x, auto := α, cond := hα } : RelativeInertia pX)) rfl
      (by simpa using (inertiaPullbackInverse_compare_auto_hom pX pY F hF hFF
        ({ obj := x, auto := α, cond := hα } : RelativeInertia pX)))

private noncomputable def inertiaPullbackUnitIso
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) :
    𝟭 (RelativeInertia pX) ≅
      inertiaPullbackComparison pX pY F hF ⋙ inertiaPullbackInverse pX pY F hF hFF :=
  NatIso.ofComponents
    (fun A => eqToIso (inertiaPullbackInverse_compare_obj_eq pX pY F hF hFF A).symm)
    (by
      intro A B f
      apply RelativeInertiaHom.ext
      simp [inertiaPullbackInverse, inertiaPullbackComparison])

/-- The unit component is the identity on underlying objects: the comparison and its
quasi-inverse agree on objects, so the `eqToIso` witnessing that has identity underlying
morphism. Naming this equation is what lets the triangle identity below be checked without
reducing the `eqToHom` through both functors. -/
private lemma inertiaPullbackUnitIso_hom_app_hom
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) (A : RelativeInertia pX) :
    ((inertiaPullbackUnitIso pX pY F hF hFF).hom.app A).hom = 𝟙 A.obj := by
  rw [show (inertiaPullbackUnitIso pX pY F hF hFF).hom.app A =
      eqToHom (inertiaPullbackInverse_compare_obj_eq pX pY F hF hFF A).symm from rfl,
    RelativeInertiaHom.eqToHom_hom]
  exact eqToHom_refl A.obj _

private lemma inertiaPullbackComparison_comp_structureFunctor
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX) :
    inertiaPullbackComparison pX pY F hF ⋙
      TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
        (RelativeInertia.π pY) F = RelativeInertia.toBase pX := by
  refine CategoryTheory.Functor.ext (fun A => rfl) (fun A B f => ?_)
  simp [inertiaPullbackComparison, TwoFibreProductOver.structureFunctor_map]

private lemma inertiaPullbackInverse_comp_structureFunctor
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) :
    inertiaPullbackInverse pX pY F hF hFF ⋙ RelativeInertia.toBase pX =
      TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
        (RelativeInertia.π pY) F := by
  refine CategoryTheory.Functor.ext (fun P => P.hy) (fun P Q u => ?_)
  have := u.hb
  exact IsHomLift.fac' pX u.hbase u.b

private noncomputable def inertiaPullbackCounitIso
    {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ pY = pX)
    (hFF : F.FullyFaithful) :
    inertiaPullbackInverse pX pY F hF hFF ⋙ inertiaPullbackComparison pX pY F hF ≅
      𝟭 (inertiaPullbackProduct pX pY F) := by
  let inv := inertiaPullbackInverse pX pY F hF hFF
  let cmp := inertiaPullbackComparison pX pY F hF
  refine NatIso.ofComponents (fun P => ?_) ?_
  · let a : (cmp.obj (inv.obj P)).x ⟶ P.x :=
      { hom := P.iso.inv
        comm := by
          change P.iso.inv ≫ P.x.auto.hom =
            F.map (inertiaPullbackAuto pX pY F hFF P).hom ≫ P.iso.inv
          rw [inertiaPullbackAuto_map pX pY F hFF P,
            inertiaPullbackTransportedAuto_hom]
          simp }
    let b : (cmp.obj (inv.obj P)).y ⟶ P.y := 𝟙 P.y
    let w₁ : (cmp.obj (inv.obj P)) ⟶ P :=
      { hbase := eqToHom P.hy
        a := a
        b := b
        ha := by
          apply (RelativeInertia.isHomLift_π_comp_iff (p := pY)
            (eqToHom P.hy) a).mpr
          let _ : pY.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
          let _ : pY.IsHomLift (𝟙 P.base) P.iso.inv :=
            IsHomLift.lift_id_inv pY P.base P.iso
          apply IsHomLift.of_fac' pY (eqToHom P.hy) P.iso.inv
            (by simpa using (Functor.congr_obj hF P.y))
            (by simpa using P.hx)
          rw [IsHomLift.fac' pY (𝟙 P.base) P.iso.inv]
          simp
        hb := IsHomLift.id_lift_eqToHom_codomain P.hy P.hy
        w := by simp [a, b, cmp, inertiaPullbackComparison, inv,
          inertiaPullbackInverse, RelativeInertia.functoriality] }
    let a' : P.x ⟶ (cmp.obj (inv.obj P)).x :=
      { hom := P.iso.hom
        comm := by
          change P.iso.hom ≫ F.map (inertiaPullbackAuto pX pY F hFF P).hom =
            P.x.auto.hom ≫ P.iso.hom
          rw [inertiaPullbackAuto_map pX pY F hFF P,
            inertiaPullbackTransportedAuto_hom]
          simp }
    let b' : P.y ⟶ (cmp.obj (inv.obj P)).y := 𝟙 P.y
    let w₂ : P ⟶ (cmp.obj (inv.obj P)) :=
      { hbase := eqToHom P.hy.symm
        a := a'
        b := b'
        ha := by
          apply (RelativeInertia.isHomLift_π_comp_iff (p := pY)
            (eqToHom P.hy.symm) a').mpr
          let _ : pY.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
          apply IsHomLift.of_fac' pY (eqToHom P.hy.symm) P.iso.hom
            (by simpa using P.hx)
            (by simpa using (Functor.congr_obj hF P.y))
          rw [IsHomLift.fac' pY (𝟙 P.base) P.iso.hom]
          simp
        hb := IsHomLift.id_lift_eqToHom_domain P.hy.symm P.hy
        w := by simp [a', b', cmp, inertiaPullbackComparison, inv,
          inertiaPullbackInverse, RelativeInertia.functoriality] }
    refine ⟨w₁, w₂, ?_, ?_⟩
    · apply TwoFibreProductOver.Hom.ext'
      · apply RelativeInertiaHom.ext
        simp only [Functor.comp_obj, Functor.id_obj, RelativeInertia.π_obj,
          TwoFibreProductOver.comp_a, RelativeInertia.comp_hom, TwoFibreProductOver.id_a,
          RelativeInertia.id_hom, w₁, a, w₂, a']
        -- The identity left over is the one of `F.obj P.y`, spelled through the comparison's
        -- `x`-component; `Iso.inv_hom_id` is it, and `exact` identifies the two spellings.
        exact P.iso.inv_hom_id
      · change (𝟙 P.y) ≫ (𝟙 P.y) = 𝟙 P.y
        simp
    · apply TwoFibreProductOver.Hom.ext'
      · apply RelativeInertiaHom.ext
        simp only [Functor.id_obj, Functor.comp_obj, RelativeInertia.π_obj,
          TwoFibreProductOver.comp_a, RelativeInertia.comp_hom, TwoFibreProductOver.id_a,
          RelativeInertia.id_hom, w₂, a', w₁, a]
        exact P.iso.hom_inv_id
      · change (𝟙 P.y) ≫ (𝟙 P.y) = 𝟙 P.y
        simp
  · intro P Q u
    apply TwoFibreProductOver.Hom.ext'
    · apply RelativeInertiaHom.ext
      exact inertiaPullbackHom_map_comp_iso_inv pX pY F u
    · change u.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ u.b
      simp

/-- For a fully faithful morphism, the inertia square is a 2-fibre product
over the base, with its canonical comparison functor and vertical coherence. -/
@[stacks 06R5]
public theorem inertiaPullbackComparison_isEquivalenceOver
    (hFF : F.FullyFaithful) :
    Nonempty (IsEquivalenceOver (RelativeInertia.toBase pX)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
        (RelativeInertia.π pY) F)
      (inertiaPullbackComparison pX pY F hF)) := by
  let inv := inertiaPullbackInverse pX pY F hF hFF
  let cmp := inertiaPullbackComparison pX pY F hF
  let q := RelativeInertia.toBase pX
  let r := TwoFibreProductOver.structureFunctor (RelativeInertia.toBase pY) pX pY
    (RelativeInertia.π pY) F
  let unit := inertiaPullbackUnitIso pX pY F hF hFF
  let counit := inertiaPullbackCounitIso pX pY F hF hFF
  refine ⟨{
    inverse := inv
    unitIso := unit
    counitIso := counit
    functor_unitIso_comp := ?_
    functor_over := inertiaPullbackComparison_comp_structureFunctor pX pY F hF
    inverse_over := inertiaPullbackInverse_comp_structureFunctor pX pY F hF hFF
    unit_over := ?_
    counit_over := ?_
  }⟩
  · intro A
    apply TwoFibreProductOver.Hom.ext'
    · apply RelativeInertiaHom.ext
      simp [unit, counit, inertiaPullbackUnitIso_hom_app_hom, inertiaPullbackCounitIso,
        inertiaPullbackInverse, inertiaPullbackComparison,
        RelativeInertia.functoriality]
    · simp [unit, counit, inertiaPullbackUnitIso, inertiaPullbackCounitIso,
        inertiaPullbackInverse, inertiaPullbackComparison]
  · intro A
    simp [unit, inertiaPullbackUnitIso]
  · intro P
    simp [counit, inertiaPullbackCounitIso,
      TwoFibreProductOver.structureFunctor_map]

end CategoryTheory

end
