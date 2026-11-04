module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Base change of a representable 1-morphism

A representable 1-morphism `F : 𝒳 ⥤ 𝒴` of categories over a base category stays representable
after base change along any 1-morphism `G : 𝒵 ⥤ 𝒴` over that base: the first projection
`𝒵 ×_𝒴 𝒳 ⥤ 𝒵` is representable.

The proof is the one in the source. For a 1-morphism `H : 𝒞/U ⥤ 𝒵` over the base, the iterated
2-fibre product `(𝒞/U) ×_𝒵 (𝒵 ×_𝒴 𝒳)` is identified with `(𝒞/U) ×_𝒴 𝒳` computed along the
composite `H ⋙ G`, by functors in both directions built from the universal property of the
2-fibre product; the two composites are isomorphic over `𝒞/U`. Representability of `F` at
`H ⋙ G` therefore transfers to the base-changed projection.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_fst_twoFibreProductOver`: the first
  projection off the
  2-fibre product is representable when the 1-morphism being based-changed is.

## Implementation notes

The statement is made for categories over an arbitrary base category. The source's fppf site
and categories fibred in groupoids are a special case; the base-change argument uses only
functors over the base.

## References

* [Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT)
-/

open CategoryTheory

namespace Stacks.RepresentableMorphism

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

attribute [local implicit_reducible] TwoFibreProductOver.fst TwoFibreProductOver.snd
  TwoFibreProductOver.structureFunctor TwoFibreProductOver.lift

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒵 : Type u₄} [Category.{v₄} 𝒵]

private noncomputable def baseChangeTestToOriginal
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴) (_hF : F ⋙ p𝒴 = p𝒳) (_hG : G ⋙ p𝒴 = p𝒵)
    (U : 𝒞) (H : Over U ⥤ 𝒵) (hH : H ⋙ p𝒵 = Over.forget U) :
    TwoFibreProductOver (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F ⥤
    TwoFibreProductOver (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F) := by
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let fstA := TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let sndA := TwoFibreProductOver.snd (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let pA := TwoFibreProductOver.structureFunctor (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let h₃ : fstA ⋙ Over.forget U = pA := by simpa [fstA, pA] using
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.forget U) (p𝒴 := p𝒳)
      (p𝒮 := p𝒴) (F := H ⋙ G) (G := F))
  let h₁ : (fstA ⋙ H) ⋙ p𝒵 = pA := by
    calc
      (fstA ⋙ H) ⋙ p𝒵 = fstA ⋙ (H ⋙ p𝒵) := by simp [Functor.assoc]
      _ = fstA ⋙ Over.forget U := by rw [hH]
      _ = pA := h₃
  let h₂ : sndA ⋙ p𝒳 = pA := by
    simpa [sndA, pA] using
      (TwoFibreProductOver.snd_comp_eq (p𝒳 := Over.forget U) (p𝒴 := p𝒳)
        (p𝒮 := p𝒴) (F := H ⋙ G) (G := F))
  let tA : (fstA ⋙ H) ⋙ G ≅ sndA ⋙ F :=
    NatIso.ofComponents (fun a => a.iso) (by
      intro a b f
      change G.map (H.map f.a) ≫ b.iso.hom = a.iso.hom ≫ F.map f.b
      exact f.w)
  let htA : ∀ a, p𝒴.IsHomLift (𝟙 (pA.obj a)) (tA.hom.app a) := by
    intro a
    change p𝒴.IsHomLift (𝟙 a.base) a.iso.hom
    exact a.vertical
  let K := TwoFibreProductOver.lift p𝒵 p𝒳 p𝒴 G F pA (fstA ⋙ H) sndA h₁ h₂ tA htA
  let h₄ : K ⋙ pW = pA := by
    simpa [K, pW] using
      (TwoFibreProductOver.lift_comp_structureFunctor (p𝒳 := p𝒵) (p𝒴 := p𝒳)
        (p𝒮 := p𝒴) (F := G) (G := F) (pW := pA) (H := fstA ⋙ H)
        (K := sndA) (hH := h₁) (hK := h₂) (t := tA) (ht := htA))
  let tB : fstA ⋙ H ≅ K ⋙ fstW :=
    Iso.refl _
  let htB : ∀ a, p𝒵.IsHomLift (𝟙 (pA.obj a)) (tB.hom.app a) := by
    intro a
    have hbase : p𝒵.obj (H.obj (fstA.obj a)) = pA.obj a := by
      simpa [Functor.comp_obj, fstA, pA] using
        (congrArg (fun k : Over U ⥤ 𝒞 => k.obj (fstA.obj a)) hH).trans a.hx
    change p𝒵.IsHomLift (𝟙 (pA.obj a)) (𝟙 (H.obj (fstA.obj a)))
    exact IsHomLift.id hbase
  exact TwoFibreProductOver.lift (Over.forget U) pW p𝒵 H fstW pA
    fstA K h₃ h₄ tB htB

private noncomputable def baseChangeTestFromOriginal
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴) (_hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (U : 𝒞) (H : Over U ⥤ 𝒵) (_hH : H ⋙ p𝒵 = Over.forget U) :
    TwoFibreProductOver (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F) ⥤
    TwoFibreProductOver (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F := by
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let sndW := TwoFibreProductOver.snd p𝒵 p𝒳 p𝒴 G F
  let fstB := TwoFibreProductOver.fst (Over.forget U) pW p𝒵 H fstW
  let sndB := TwoFibreProductOver.snd (Over.forget U) pW p𝒵 H fstW
  let pB := TwoFibreProductOver.structureFunctor (Over.forget U) pW p𝒵 H fstW
  let h₁ : fstB ⋙ Over.forget U = pB := by
    simpa [fstB, pB] using
      (TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.forget U) (p𝒴 := pW)
        (p𝒮 := p𝒵) (F := H) (G := fstW))
  let h₂ : (sndB ⋙ sndW) ⋙ p𝒳 = pB := by
    calc
      (sndB ⋙ sndW) ⋙ p𝒳 = sndB ⋙ (sndW ⋙ p𝒳) := by simp [Functor.assoc]
      _ = sndB ⋙ pW := by
        rw [TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒵) (p𝒴 := p𝒳)
          (p𝒮 := p𝒴) (F := G) (G := F)]
      _ = pB := by simpa [sndB, pB] using
        (TwoFibreProductOver.snd_comp_eq (p𝒳 := Over.forget U)
          (p𝒴 := pW) (p𝒮 := p𝒵) (F := H) (G := fstW))
  let tB₀ : fstB ⋙ H ⋙ G ≅ sndB ⋙ fstW ⋙ G :=
    Functor.isoWhiskerRight
      (TwoFibreProductOver.psiIso (p𝒳 := Over.forget U) (p𝒴 := pW)
        (p𝒮 := p𝒵) (F := H) (G := fstW)) G
  let tB₁ : sndB ⋙ fstW ⋙ G ≅ sndB ⋙ sndW ⋙ F :=
    Functor.isoWhiskerLeft sndB (TwoFibreProductOver.psiIso p𝒵 p𝒳 p𝒴 G F)
  let tB : fstB ⋙ (H ⋙ G) ≅ (sndB ⋙ sndW) ⋙ F := tB₀.trans tB₁
  let htB : ∀ b, p𝒴.IsHomLift (𝟙 (pB.obj b)) (tB.hom.app b) := by
    intro b
    have hβ₀ : p𝒵.IsHomLift (𝟙 (pB.obj b))
        ((TwoFibreProductOver.psiIso (p𝒳 := Over.forget U) (p𝒴 := pW)
          (p𝒮 := p𝒵) (F := H) (G := fstW)).hom.app b) := by
      change p𝒵.IsHomLift (𝟙 b.base) b.iso.hom
      exact TwoFibreProductOver.psiIso_hom_vertical b
    have hβ : p𝒴.IsHomLift (𝟙 (pB.obj b)) (tB₀.hom.app b) := by
      have hmap := Functor.isHomLift_map_of_comp_eq hG (𝟙 (pB.obj b))
        ((TwoFibreProductOver.psiIso (p𝒳 := Over.forget U) (p𝒴 := pW)
          (p𝒮 := p𝒵) (F := H) (G := fstW)).hom.app b)
      simpa [tB₀, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using hmap
    have hψ : p𝒴.IsHomLift (𝟙 (pB.obj b)) (tB₁.hom.app b) := by
      have hbase : (sndB.obj b).base = pB.obj b := by
        change b.y.base = b.base
        exact b.hy
      rw [← hbase]
      simpa [tB₁] using TwoFibreProductOver.psiIso_hom_vertical (sndB.obj b)
    simpa [tB, Iso.trans_hom] using
      (IsHomLift.comp p𝒴 (𝟙 (pB.obj b)) (𝟙 (pB.obj b))
        (tB₀.hom.app b) (tB₁.hom.app b))
  exact TwoFibreProductOver.lift (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F pB
    fstB (sndB ⋙ sndW) h₁ h₂ tB htB

attribute [local implicit_reducible] baseChangeTestToOriginal baseChangeTestFromOriginal

private theorem baseChangeTestToOriginal_compIso
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (U : 𝒞) (H : Over U ⥤ 𝒵) (hH : H ⋙ p𝒵 = Over.forget U) :
    ∃ i : baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ⋙
      baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ≅
      𝟭 (TwoFibreProductOver (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F),
      Functor.IsVerticalNatTrans
        (TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F) i.hom := by
  let A := TwoFibreProductOver (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let fstA := TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let sndA := TwoFibreProductOver.snd (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let pA := TwoFibreProductOver.structureFunctor (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  have h₁ : (e ⋙ d) ⋙ fstA = fstA := rfl
  let a : (e ⋙ d) ⋙ fstA ≅ fstA := Iso.refl _
  let b : (e ⋙ d) ⋙ sndA ≅ sndA := Iso.refl _
  have ha : ∀ x, (Over.forget U).IsHomLift (𝟙 (pA.obj x)) (a.hom.app x) := by
    intro x
    show (Over.forget U).IsHomLift (𝟙 x.base) (𝟙 x.x)
    exact IsHomLift.id x.hx
  have hb : ∀ x, p𝒳.IsHomLift (𝟙 (pA.obj x)) (b.hom.app x) := by
    intro x
    show p𝒳.IsHomLift (𝟙 x.base) (𝟙 x.y)
    exact IsHomLift.id x.hy
  have hab : Functor.whiskerRight a.hom (H ⋙ G) ≫
      (TwoFibreProductOver.psiIso (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F).hom =
      Functor.whiskerLeft (e ⋙ d)
        (TwoFibreProductOver.psiIso (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F).hom ≫
      Functor.whiskerRight b.hom F := by
    ext x
    simp [a, b, e, d, baseChangeTestToOriginal, baseChangeTestFromOriginal,
      TwoFibreProductOver.lift, TwoFibreProductOver.fst, TwoFibreProductOver.snd,
      TwoFibreProductOver.structureFunctor, fstA, sndA]
  let iso : e ⋙ d ≅ 𝟭 A := TwoFibreProductOver.liftIso (p𝒳 := Over.forget U) (p𝒴 := p𝒳) (p𝒮 := p𝒴)
      (F := H ⋙ G) (G := F) (pW := pA) (H := fstA) (K := sndA)
      (t := TwoFibreProductOver.psiIso (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F)
      (ht := fun x => TwoFibreProductOver.psiIso_hom_vertical x)
      (γ := e ⋙ d) a b ha hb hab
      (hH := TwoFibreProductOver.fst_comp_eq (p𝒳 := Over.forget U) (p𝒴 := p𝒳)
        (p𝒮 := p𝒴) (F := H ⋙ G) (G := F))
      (hK := TwoFibreProductOver.snd_comp_eq (p𝒳 := Over.forget U) (p𝒴 := p𝒳)
        (p𝒮 := p𝒴) (F := H ⋙ G) (G := F))
  refine ⟨iso, fun x => ?_⟩
  apply (IsHomLift.id_iff_exists_eqToHom fstA (iso.hom.app x)).2
  have hx := congrArg (fun k : A ⥤ Over U => k.obj x) h₁
  refine ⟨hx, ?_⟩
  show (iso.hom.app x).a = eqToHom hx
  simp [iso, a, b, TwoFibreProductOver.liftIso, TwoFibreProductOver.fst,
    TwoFibreProductOver.lift]

section FromOriginal

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
  (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
  (U : 𝒞) (H : Over U ⥤ 𝒵) (hH : H ⋙ p𝒵 = Over.forget U)

private noncomputable def baseChangeTestFromOriginal_sndHom
    (b : TwoFibreProductOver (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)) :
    (TwoFibreProductOver.snd (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)).obj
      ((baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ⋙
        baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH).obj b) ⟶
    (TwoFibreProductOver.snd (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)).obj b := by
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let fstB := TwoFibreProductOver.fst (Over.forget U) pW p𝒵 H fstW
  let sndB := TwoFibreProductOver.snd (Over.forget U) pW p𝒵 H fstW
  let pB := TwoFibreProductOver.structureFunctor (Over.forget U) pW p𝒵 H fstW
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let q := d ⋙ e
  let z := sndB.obj (q.obj b)
  have hz : z.base = b.base := rfl
  have hby : b.y.base = b.base := by simpa [pW] using b.hy
  have hbase : z.base = b.y.base := hz.trans hby.symm
  have hyy : z.y = b.y.y := rfl
  have hziso : z.iso.hom = G.map b.iso.hom ≫ b.y.iso.hom := by
    simp [z, q, d, e, baseChangeTestFromOriginal, baseChangeTestToOriginal,
      TwoFibreProductOver.lift, TwoFibreProductOver.fst,
      TwoFibreProductOver.snd, TwoFibreProductOver.structureFunctor,
      sndB, pW, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.trans_hom]
  let f := eqToHom hbase
  have ha : p𝒵.IsHomLift f b.iso.hom := by
    apply IsHomLift.of_fac' p𝒵 f b.iso.hom z.hx b.y.hx
    have : p𝒵.IsHomLift (𝟙 b.base) b.iso.hom := b.vertical
    have hv := IsHomLift.fac' p𝒵 (𝟙 b.base) b.iso.hom
    simpa [f, hbase, hz, hby, z, q, d, e, baseChangeTestFromOriginal,
      baseChangeTestToOriginal, TwoFibreProductOver.lift,
      TwoFibreProductOver.fst, TwoFibreProductOver.snd,
      TwoFibreProductOver.structureFunctor, fstB, sndB, pB, pW]
      using hv
  let g := eqToHom hyy
  have hb : p𝒳.IsHomLift f g := by
    apply IsHomLift.of_fac' p𝒳 f g z.hy b.y.hy
    simp [f, g]
  exact {
    hbase := f
    a := b.iso.hom
    b := g
    ha := ha
    hb := hb
    w := by
      change G.map b.iso.hom ≫ b.y.iso.hom = z.iso.hom ≫ F.map g
      rw [hziso]
      simp [g]
  }

attribute [local implicit_reducible] baseChangeTestFromOriginal_sndHom

private noncomputable def baseChangeTestFromOriginal_sndIso :
    (baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ⋙
        baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH) ⋙
      TwoFibreProductOver.snd (Over.forget U)
        (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
        (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F) ≅
    TwoFibreProductOver.snd (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F) := by
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let B := TwoFibreProductOver (Over.forget U) pW p𝒵 H fstW
  let sndB := TwoFibreProductOver.snd (Over.forget U) pW p𝒵 H fstW
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let q := d ⋙ e
  let wHom (b : B) := baseChangeTestFromOriginal_sndHom p𝒳 p𝒴 p𝒵 F G hF hG U H hH b
  have hwIso (b : B) : IsIso (wHom b) := by
    have : IsIso (wHom b).hbase := by
      dsimp only [wHom, baseChangeTestFromOriginal_sndHom]; infer_instance
    have : IsIso (wHom b).a := ⟨b.iso.inv, b.iso.hom_inv_id, b.iso.inv_hom_id⟩
    have : IsIso (wHom b).b := by
      dsimp only [wHom, baseChangeTestFromOriginal_sndHom]; infer_instance
    exact TwoFibreProductOver.isIso_of_isIso_components p𝒵 p𝒳 p𝒴 G F
      (wHom b) (by infer_instance) (by infer_instance)
  exact NatIso.ofComponents (fun b => asIso (wHom b)) (by
    intro b c f
    apply TwoFibreProductOver.Hom.ext'
    · change H.map f.a ≫ c.iso.hom = b.iso.hom ≫ fstW.map f.b
      exact f.w
    · suffices h : (sndB.map (q.map f)).b = (sndB.map f).b by
        simpa [wHom, baseChangeTestFromOriginal_sndHom, d, e, baseChangeTestFromOriginal,
          baseChangeTestToOriginal, TwoFibreProductOver.lift, TwoFibreProductOver.fst,
          TwoFibreProductOver.snd, TwoFibreProductOver.structureFunctor,
          TwoFibreProductOver.snd_map, Functor.comp_map] using h
      rfl)

attribute [local implicit_reducible] baseChangeTestFromOriginal_sndIso

private noncomputable def baseChangeTestFromOriginal_compHom
    (b : TwoFibreProductOver (Over.forget U)
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)) :
    (baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ⋙
      baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH).obj b ⟶ b := by
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let sndB := TwoFibreProductOver.snd (Over.forget U) pW p𝒵 H fstW
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let q := d ⋙ e
  let wIso := baseChangeTestFromOriginal_sndIso p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  exact {
    hbase := 𝟙 b.base
    a := 𝟙 b.x
    b := wIso.hom.app b
    ha := IsHomLift.id b.hx
    hb := by
      let z := sndB.obj (q.obj b)
      have hz : z.base = b.base := rfl
      have hby : (sndB.obj b).base = b.base := by simpa [pW, sndB] using b.hy
      have hmap : pW.map (wIso.hom.app b) = eqToHom (hz.trans hby.symm) := by
        change (wIso.hom.app b).hbase = _
        simp [wIso, baseChangeTestFromOriginal_sndIso, baseChangeTestFromOriginal_sndHom]
      apply IsHomLift.of_fac' pW (𝟙 b.base) (wIso.hom.app b) hz hby
      rw [hmap]
      simp
    w := by
      change H.map (𝟙 b.x) ≫ b.iso.hom = (q.obj b).iso.hom ≫ fstW.map (wIso.hom.app b)
      simp [wIso, baseChangeTestFromOriginal_sndIso, baseChangeTestFromOriginal_sndHom, q, d,
        e, baseChangeTestFromOriginal, baseChangeTestToOriginal, TwoFibreProductOver.lift,
        TwoFibreProductOver.fst, TwoFibreProductOver.snd,
        TwoFibreProductOver.structureFunctor, fstW]
  }

end FromOriginal

attribute [local implicit_reducible] baseChangeTestFromOriginal_compHom

private theorem baseChangeTestFromOriginal_compIso
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (U : 𝒞) (H : Over U ⥤ 𝒵) (hH : H ⋙ p𝒵 = Over.forget U) :
    ∃ i : baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ⋙
      baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH ≅
      𝟭 (TwoFibreProductOver (Over.forget U)
        (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
        (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)),
      Functor.IsVerticalNatTrans
        (TwoFibreProductOver.fst (Over.forget U)
          (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
          (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)) i.hom := by
  let fstW := TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F
  let pW := TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F
  let B := TwoFibreProductOver (Over.forget U) pW p𝒵 H fstW
  let fstB := TwoFibreProductOver.fst (Over.forget U) pW p𝒵 H fstW
  let sndB := TwoFibreProductOver.snd (Over.forget U) pW p𝒵 H fstW
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let q := d ⋙ e
  let wIso := baseChangeTestFromOriginal_sndIso p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let qHom (b : B) : q.obj b ⟶ b :=
    baseChangeTestFromOriginal_compHom p𝒳 p𝒴 p𝒵 F G hF hG U H hH b
  have hqIso (b : B) : IsIso (qHom b) := by
    have : IsIso (𝟙 b.x) := by infer_instance
    have : IsIso (wIso.hom.app b) :=
      ⟨(wIso.app b).inv, (wIso.app b).hom_inv_id, (wIso.app b).inv_hom_id⟩
    exact TwoFibreProductOver.isIso_of_isIso_components
      (Over.forget U) pW p𝒵 H fstW (qHom b)
      (by dsimp [qHom, baseChangeTestFromOriginal_compHom]; infer_instance)
      (by dsimp [qHom, baseChangeTestFromOriginal_compHom]; infer_instance)
  have hprojB : q ⋙ fstB = fstB := rfl
  let iso : q ≅ 𝟭 B := NatIso.ofComponents (fun b =>
    let := hqIso b; asIso (qHom b)) (by
    intro b c f
    apply TwoFibreProductOver.Hom.ext'
    · show (q.map f).a ≫ 𝟙 c.x = 𝟙 b.x ≫ f.a
      refine (Category.comp_id ((q.map f).a)).trans (Eq.trans ?_ (Category.id_comp f.a).symm)
      simpa [Functor.comp_map, fstB, TwoFibreProductOver.fst] using Functor.congr_hom hprojB f
    · simpa [qHom, wIso, q, d, e, baseChangeTestFromOriginal_compHom, Functor.comp_map, sndB,
        TwoFibreProductOver.snd] using wIso.hom.naturality f)
  refine ⟨iso, fun b => ?_⟩
  apply (IsHomLift.id_iff_exists_eqToHom fstB (iso.hom.app b)).2
  have hb := congrArg (fun k : B ⥤ Over U => k.obj b) hprojB
  refine ⟨hb, ?_⟩
  show (iso.hom.app b).a = eqToHom hb
  simp [iso, qHom, baseChangeTestFromOriginal_compHom, q, d, e, baseChangeTestFromOriginal,
    baseChangeTestToOriginal, TwoFibreProductOver.lift, TwoFibreProductOver.fst,
    TwoFibreProductOver.snd, TwoFibreProductOver.structureFunctor, fstB]

private theorem isCartesianFunctorStrict_of_comp_eq {𝒮 : Type*} [Category 𝒮]
    {𝒮' : Type*} [Category 𝒮'] {p : 𝒮 ⥤ 𝒞} {q : 𝒮' ⥤ 𝒞} {F : 𝒮 ⥤ 𝒮'}
    (hq : q.IsFiberedInGroupoids) (h : F ⋙ q = p) : IsCartesianFunctorStrict p q F := by
  refine ⟨h, ?_⟩
  intro R S a b f φ _ _
  have := Functor.isHomLift_map_of_comp_eq h f φ
  have := hq.isStronglyCartesian_homLift f (F.map φ)
  infer_instance

private theorem isFibredEquivalence_of_isEquivalence {𝒮 : Type*} [Category 𝒮]
    {𝒮' : Type*} [Category 𝒮'] {p : 𝒮 ⥤ 𝒞} {q : 𝒮' ⥤ 𝒞} {F : 𝒮 ⥤ 𝒮'}
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hF : F ⋙ q = p)
    (he : F.IsEquivalence) : IsFibredEquivalence p q F := by
  obtain ⟨G, hG, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p q hp hq F hF he
  refine ⟨isCartesianFunctorStrict_of_comp_eq hq hF, G,
    isCartesianFunctorStrict_of_comp_eq hp hG, ⟨ε, fun x => ?_⟩, ⟨η, fun x => ?_⟩⟩
  · have := hε x
    exact ⟨_, by simpa using IsHomLift.fac' q (𝟙 (q.obj x)) (ε.hom.app x)⟩
  · have := hη x
    exact ⟨_, by simpa using IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.app x)⟩

/-- **Stacks Project, Tag 02ZT.** The projection to `𝒵` from the 2-fibre
product `𝒵 ×_𝒴 𝒳` is representable when `𝒳 ⥤ 𝒴` is representable. -/
@[stacks 02ZT]
public theorem isRepresentableMorphism_fst_twoFibreProductOver
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (hrep : Stacks.RepresentableMorphism.IsRepresentableMorphism p𝒳 p𝒴 F) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
      (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵
      (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F) := by
  intro U H hH
  have hcomp : (H ⋙ G) ⋙ p𝒴 = Over.forget U := by
    rwa [Functor.assoc, hG]
  let fstA := TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (H ⋙ G) F
  let fstB := TwoFibreProductOver.fst (Over.forget U)
    (TwoFibreProductOver.structureFunctor p𝒵 p𝒳 p𝒴 G F) p𝒵 H
    (TwoFibreProductOver.fst p𝒵 p𝒳 p𝒴 G F)
  let e := baseChangeTestToOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  let d := baseChangeTestFromOriginal p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  obtain ⟨isoAD, hIsoAD⟩ :=
    baseChangeTestToOriginal_compIso p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  obtain ⟨isoBD, hIsoBD⟩ :=
    baseChangeTestFromOriginal_compIso p𝒳 p𝒴 p𝒵 F G hF hG U H hH
  have hd : d ⋙ fstA = fstB := rfl
  have he : e ⋙ fstB = fstA := rfl
  have hrepA := hrep U (H ⋙ G) hcomp
  have hA : fstA.IsFiberedInGroupoids :=
    (Stacks.RepresentableMorphism.isFiberedInSetoids_of_isRepresentableCFG fstA
      hrepA).isFiberedInGroupoids
  have hB : fstB.IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver he ⟨d, hd, isoAD, isoBD, hIsoAD, hIsoBD⟩ hA
  have hD : IsFibredEquivalence fstB fstA d :=
    ⟨isCartesianFunctorStrict_of_comp_eq hA hd, e, isCartesianFunctorStrict_of_comp_eq hB he,
      ⟨isoAD, fun a => (IsHomLift.id_iff_exists_eqToHom fstA (isoAD.hom.app a)).1 (hIsoAD a)⟩,
      ⟨isoBD, fun b => (IsHomLift.id_iff_exists_eqToHom fstB (isoBD.hom.app b)).1 (hIsoBD b)⟩⟩
  obtain ⟨X, E, hEA⟩ := hrepA
  obtain ⟨backD, _, ⟨ηD, _⟩, ⟨εD, _⟩⟩ := hD.exists_inverse
  have : d.IsEquivalence :=
    (CategoryTheory.Equivalence.mk d backD εD.symm ηD).isEquivalence_functor
  have : E.IsEquivalence := SliceEquivalence.isEquivalence_of_isEquivalenceOver fstA X E hEA
  let FE := d ⋙ E
  have hFE : FE ⋙ Over.forget X = fstB := by
    dsimp [FE]
    rwa [Functor.assoc, hEA.isCartesianFunctor.comm]
  have : FE.IsEquivalence := Functor.isEquivalence_trans d E
  exact ⟨X, FE, isFibredEquivalence_of_isEquivalence hB
    (StacksRepresentableCFG.over_isFiberedInSetoids X).isFiberedInGroupoids hFE this⟩

end Stacks.RepresentableMorphism
