module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibreSetoid
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonArrows
import all StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence

/-!
# Condition (RS*) for the fibres of the diagonal

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `V` be an
object of that site and let `y` be an object of `𝒳 × 𝒳` over `V`, given as a 1-morphism
`(Sch/V)_{fppf} ⟶ 𝒳 × 𝒳`. The 2-fibre product `𝒲 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`, with its
first projection to `(Sch/V)_{fppf}`, is fibred in setoids: its objects over `T` are the
isomorphisms `y₁|_T ⟶ y₂|_T`, recorded by `CategoryTheory.TwoFibreProductOver.sectOf`. If `𝒳`
satisfies (RS*), so does `𝒲`, as a category over the big fppf site of `V`.

The proof reads (RS*) for `𝒲` on arrows
(`Deformation.Artin.FiberSquare.isEquivalence_of_faithful`): gluing two objects of `𝒲` over the
corners `V'` and `W'` of a square is gluing the two morphisms `y₁ ⟶ y₂` over those corners, which
is the fullness of the comparison functor of `𝒳` at the image of the square in the site of `S`;
and two objects over the fourth corner with the same restrictions name morphisms with the same
restrictions, which then agree by its faithfulness.

## Main results

* `Deformation.Artin.satisfiesRSStar_diagonalFibre`: (RS*) for `𝒲` over the site of `V`.

## Implementation notes

A square of the big affine fppf site of `V` is sent to one of `S` by postcomposition with the
structure morphism of `V` (`CategoryTheory.Over.map`), which changes neither the schemes nor the
morphisms of schemes, so the hypotheses of (RS*) transfer unchanged.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0CXQ](https://stacks.math.columbia.edu/tag/0CXQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

section General

variable {𝒞 : Type*} [Category 𝒞] {X : Type*} [Category X] {𝒯 : Type*} [Category 𝒯]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y : 𝒯 ⥤ Prod' p}

/-- A component of `Y` maps a morphism equal, up to identifications of its ends, to `k` to a
morphism lying over the image of `k`. -/
theorem isHomLift_map_of_eq (Y₀ : 𝒯 ⥤ X) (h₀ : Y₀ ⋙ p = p𝒯) {R T a b : 𝒯} (k : R ⟶ T)
    (g : a ⟶ b) (ha : a = R) (hb : b = T) (hg : g = eqToHom ha ≫ k ≫ eqToHom hb.symm) :
    p.IsHomLift (p𝒯.map k) (Y₀.map g) := by
  subst ha hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  rw [hg]
  exact VertHom.isHomLift_map h₀ k

/-- A morphism lying over an identification of two objects is vertical. -/
theorem isHomLift_id_of_eqToHom (p : X ⥤ 𝒞) {R T : 𝒞} (h : R = T) {a b : X}
    (φ : a ⟶ b) [p.IsHomLift (eqToHom h) φ] : p.IsHomLift (𝟙 R) φ :=
  (IsHomLift.lift_comp_eqToHom_iff p (𝟙 R) φ h).mp (by simpa using ‹p.IsHomLift (eqToHom h) φ›)

/-- Naturality of `sectOf` along a morphism `u`, followed by a further morphism `m`. -/
private theorem map_comp_sectOf_comp {A B : TwoFibreProductOver p𝒯 p (ProdP p) Y (Diag p)}
    (u : A ⟶ B) {c : X} (m : (Y₂' Y).obj B.x ⟶ c) :
    (Y₁' Y).map u.a ≫ sectOf B ≫ m = sectOf A ≫ (Y₂' Y).map u.a ≫ m := by
  rw [← Category.assoc, ← sectOf_naturality, Category.assoc]

end General

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))
  (V : AlgebraicGeometry.BigFppfOver B S hS)
  (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
  (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

/-- The square of the big affine fppf site of `S` underlying a square of that of `V`. -/
abbrev affineToBase : AlgebraicGeometry.BigAffineFppf B V.left.1 V.left.2 ⥤
    AlgebraicGeometry.BigAffineFppf B S hS :=
  (AlgebraicGeometry.IsAffineOver B S hS).lift
    (AlgebraicGeometry.BigAffineFppf.inclusion B V.left.1 V.left.2 ⋙ Over.map V.hom)
    (fun T => (inferInstance : IsAffine
      ((AlgebraicGeometry.BigAffineFppf.toScheme B V.left.1 V.left.2).obj T)))

include hy in
/-- **(RS\*) for the fibres of the diagonal.** If `𝒳` satisfies (RS*), then the 2-fibre product
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`, over the big fppf site of `V`, satisfies (RS*). -/
theorem satisfiesRSStar_diagonalFibre
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    SatisfiesRSStar B V.left.1 V.left.2
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
      (AlgebraicGeometry.Stack.fst_isFiberedInGroupoids_overMap V.hom 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
        𝒳.isFiberedInGroupoids (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).w) := by
  intro U' V' W' Z' f g i j h hpull hsurj hker
  let p := 𝒳.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : p.IsFibered := hp.isFibered
  let q := TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
    (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
  have hq : q.IsFiberedInGroupoids :=
    AlgebraicGeometry.Stack.fst_isFiberedInGroupoids_overMap V.hom 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
      (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
      𝒳.isFiberedInGroupoids (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).w
  have : q.Faithful := faithful_fst
  let : q.IsFibered := hq.isFibered
  let ι := AlgebraicGeometry.BigAffineFppf.inclusion B V.left.1 V.left.2
  let ιS := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let φ := affineToBase B S hS V
  -- (RS*) for `𝒳` at the image of the square
  have hS' := hRS (φ.obj U') (φ.obj V') (φ.obj W') (φ.obj Z') (φ.map f) (φ.map g) (φ.map i)
    (φ.map j) (by rw [← φ.map_comp, ← φ.map_comp, h]) hpull hsurj hker
  let cS := Functor.chosenPullbacks p
  have hwS : ιS.map (φ.map f) ≫ ιS.map (φ.map i) = ιS.map (φ.map g) ≫ ιS.map (φ.map j) := by
    simpa only [Functor.map_comp] using congrArg ιS.map (show φ.map f ≫ φ.map i =
      φ.map g ≫ φ.map j by rw [← φ.map_comp, ← φ.map_comp, h])
  have : (fiberSquareComparison p cS (ιS.map (φ.map f)) (ιS.map (φ.map g))
      (ιS.map (φ.map i)) (ιS.map (φ.map j)) hwS).IsEquivalence := hS'
  have hY₁ : Y₁' y ⋙ p = Over.map V.hom := h1' hy
  have hY₂ : Y₂' y ⋙ p = Over.map V.hom := h2' hy
  refine FiberSquare.isEquivalence_of_faithful q _ _ _ _ _ _ hq ?_ ?_
  · -- gluing
    intro x a b α β hα hβ
    have hxa : α.a = eqToHom x.2 ≫ ι.map f ≫ eqToHom a.2.symm := IsHomLift.fac' q (ι.map f) α
    have hxb : β.a = eqToHom x.2 ≫ ι.map g ≫ eqToHom b.2.symm := IsHomLift.fac' q (ι.map g) β
    let i'' : a.1.x ⟶ ι.obj Z' := eqToHom a.2 ≫ ι.map i
    let j'' : b.1.x ⟶ ι.obj Z' := eqToHom b.2 ≫ ι.map j
    have hhZ : ιS.obj (φ.obj Z') = p.obj ((Y₂' y).obj (ι.obj Z')) :=
      (Functor.congr_obj hY₂ _).symm
    let sZ : p.Fiber (ιS.obj (φ.obj Z')) := ⟨(Y₁' y).obj (ι.obj Z'), Functor.congr_obj hY₁ _⟩
    let xS : p.Fiber (ιS.obj (φ.obj U')) :=
      ⟨(Y₁' y).obj x.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ x.2)⟩
    let aS : p.Fiber (ιS.obj (φ.obj V')) :=
      ⟨(Y₁' y).obj a.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ a.2)⟩
    let bS : p.Fiber (ιS.obj (φ.obj W')) :=
      ⟨(Y₁' y).obj b.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ b.2)⟩
    have : p.IsHomLift (ιS.map (φ.map f)) ((Y₁' y).map α.a) :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map f) α.a x.2 a.2 hxa
    have : p.IsHomLift (ιS.map (φ.map g)) ((Y₁' y).map β.a) :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map g) β.a x.2 b.2 hxb
    have : p.IsHomLift (ιS.map (φ.map i)) ((Y₁' y).map i'') :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map i) i'' a.2 rfl (by simp [i''])
    have : p.IsHomLift (ιS.map (φ.map j)) ((Y₁' y).map j'') :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map j) j'' b.2 rfl (by simp [j''])
    have : p.IsHomLift (ιS.map (φ.map i)) ((Y₂' y).map i'') :=
      isHomLift_map_of_eq (Y₂' y) hY₂ (ι.map i) i'' a.2 rfl (by simp [i''])
    have : p.IsHomLift (ιS.map (φ.map j)) ((Y₂' y).map j'') :=
      isHomLift_map_of_eq (Y₂' y) hY₂ (ι.map j) j'' b.2 rfl (by simp [j''])
    have : p.IsHomLift (𝟙 ((Over.map V.hom).obj a.1.x)) (sectOf a.1) := isHomLift_sectOf hy a.1
    have : p.IsHomLift (𝟙 ((Over.map V.hom).obj b.1.x)) (sectOf b.1) := isHomLift_sectOf hy b.1
    have : p.IsHomLift (ιS.map (φ.map i)) (sectOf a.1 ≫ (Y₂' y).map i'') :=
      CategoryTheory.IsHomLift.comp_lift_id_left' p ((Over.map V.hom).obj a.1.x) (sectOf a.1)
        _ _
    have : p.IsHomLift (ιS.map (φ.map j)) (sectOf b.1 ≫ (Y₂' y).map j'') :=
      CategoryTheory.IsHomLift.comp_lift_id_left' p ((Over.map V.hom).obj b.1.x) (sectOf b.1)
        _ _
    have hsq : α.a ≫ i'' = β.a ≫ j'' := by
      rw [hxa, hxb]
      simp only [i'', j'', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← ι.map_comp, ← ι.map_comp, h]
    obtain ⟨γ, hγ, hγi, hγj⟩ := fiberSquareComparison_pointed_arrow_exists p cS (ιS.map (φ.map f))
      (ιS.map (φ.map g)) (ιS.map (φ.map i)) (ιS.map (φ.map j)) hwS hp
      (s := sZ) (b := (Y₂' y).obj (ι.obj Z')) (eqToHom hhZ) xS aS bS
      ((Y₁' y).map α.a) ((Y₁' y).map β.a) ((Y₁' y).map i'') ((Y₁' y).map j'')
      (sectOf a.1 ≫ (Y₂' y).map i'') (sectOf b.1 ≫ (Y₂' y).map j'')
      (by rw [← Functor.map_comp, ← Functor.map_comp, hsq])
      (by rw [map_comp_sectOf_comp α, map_comp_sectOf_comp β, ← Functor.map_comp,
        ← Functor.map_comp, hsq])
    have hγv : p.IsHomLift (𝟙 ((Over.map V.hom).obj (ι.obj Z'))) γ :=
      isHomLift_id_of_eqToHom p hhZ γ
    let t := objOf hy (ι.obj Z') ⟨γ, hγv⟩ hp
    have ht : sectOf t = γ := sectOf_objOf hy (ι.obj Z') ⟨γ, hγv⟩ hp
    obtain ⟨γa, hγa⟩ := exists_hom_of_sectOf hp hy (A := a.1) (B := t) i''
      (by rw [ht]; exact hγi.symm)
    obtain ⟨δb, hδb⟩ := exists_hom_of_sectOf hp hy (A := b.1) (B := t) j''
      (by rw [ht]; exact hγj.symm)
    refine ⟨⟨t, rfl⟩, γa, δb, ?_, ?_⟩
    · exact IsHomLift.of_fac' q _ _ a.2 rfl (by
        change γa.a = eqToHom a.2 ≫ ι.map i ≫ 𝟙 _
        rw [hγa, Category.comp_id])
    · exact IsHomLift.of_fac' q _ _ b.2 rfl (by
        change δb.a = eqToHom b.2 ≫ ι.map j ≫ 𝟙 _
        rw [hδb, Category.comp_id])
  · -- separation
    intro s t a b r r' s₂ s₂' hr hr' hs₂ hs₂'
    have hfr : r.a = eqToHom a.2 ≫ ι.map i ≫ eqToHom s.2.symm := IsHomLift.fac' q (ι.map i) r
    have hfr' : r'.a = eqToHom a.2 ≫ ι.map i ≫ eqToHom t.2.symm := IsHomLift.fac' q (ι.map i) r'
    have hfs : s₂.a = eqToHom b.2 ≫ ι.map j ≫ eqToHom s.2.symm := IsHomLift.fac' q (ι.map j) s₂
    have hfs' : s₂'.a = eqToHom b.2 ≫ ι.map j ≫ eqToHom t.2.symm :=
      IsHomLift.fac' q (ι.map j) s₂'
    let e : s.1.x ⟶ t.1.x := eqToHom (s.2.trans t.2.symm)
    let sS : p.Fiber (ιS.obj (φ.obj Z')) :=
      ⟨(Y₁' y).obj s.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ s.2)⟩
    let aS : p.Fiber (ιS.obj (φ.obj V')) :=
      ⟨(Y₁' y).obj a.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ a.2)⟩
    let bS : p.Fiber (ιS.obj (φ.obj W')) :=
      ⟨(Y₁' y).obj b.1.x, (Functor.congr_obj hY₁ _).trans (congrArg _ b.2)⟩
    have : p.IsHomLift (ιS.map (φ.map i)) ((Y₁' y).map r.a) :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map i) r.a a.2 s.2 hfr
    have : p.IsHomLift (ιS.map (φ.map j)) ((Y₁' y).map s₂.a) :=
      isHomLift_map_of_eq (Y₁' y) hY₁ (ι.map j) s₂.a b.2 s.2 hfs
    have hhe : ιS.obj (φ.obj Z') = p.obj ((Y₂' y).obj t.1.x) :=
      ((Functor.congr_obj hY₂ _).trans (congrArg _ t.2)).symm
    have : p.IsHomLift (𝟙 ((Over.map V.hom).obj s.1.x)) (sectOf s.1) := isHomLift_sectOf hy s.1
    have : p.IsHomLift (𝟙 ((Over.map V.hom).obj t.1.x)) (sectOf t.1) := isHomLift_sectOf hy t.1
    have : p.IsHomLift ((Over.map V.hom).map e) ((Y₂' y).map e) := VertHom.isHomLift_map hY₂ e
    have : p.IsHomLift ((Over.map V.hom).map e) ((Y₁' y).map e) := VertHom.isHomLift_map hY₁ e
    have hme : (Over.map V.hom).map e = eqToHom (congrArg _ (s.2.trans t.2.symm)) := by
      simp [e, eqToHom_map]
    haveI hα : p.IsHomLift (eqToHom hhe) (sectOf s.1 ≫ (Y₂' y).map e) := by
      have h₃ : p.IsHomLift (𝟙 ((Over.map V.hom).obj s.1.x) ≫ (Over.map V.hom).map e)
          (sectOf s.1 ≫ (Y₂' y).map e) := inferInstance
      refine IsHomLift.of_fac' p _ _ sS.2 rfl ?_
      rw [IsHomLift.fac' p (𝟙 ((Over.map V.hom).obj s.1.x) ≫ (Over.map V.hom).map e)
        (sectOf s.1 ≫ (Y₂' y).map e)]
      simp [hme]
    haveI hβ : p.IsHomLift (eqToHom hhe) ((Y₁' y).map e ≫ sectOf t.1) := by
      have h₃ : p.IsHomLift ((Over.map V.hom).map e ≫ 𝟙 ((Over.map V.hom).obj t.1.x))
          ((Y₁' y).map e ≫ sectOf t.1) := inferInstance
      refine IsHomLift.of_fac' p _ _ sS.2 rfl ?_
      rw [IsHomLift.fac' p ((Over.map V.hom).map e ≫ 𝟙 ((Over.map V.hom).obj t.1.x))
        ((Y₁' y).map e ≫ sectOf t.1)]
      simp [hme]
    have hre : r.a ≫ e = r'.a := by
      rw [hfr, hfr']
      simp [e]
    have hse : s₂.a ≫ e = s₂'.a := by
      rw [hfs, hfs']
      simp [e]
    have heq := fiberSquareComparison_arrow_ext p cS (ιS.map (φ.map f)) (ιS.map (φ.map g))
      (ιS.map (φ.map i)) (ιS.map (φ.map j)) hwS hp (s := sS) (eqToHom hhe) aS bS
      ((Y₁' y).map r.a) ((Y₁' y).map s₂.a) (α := sectOf s.1 ≫ (Y₂' y).map e)
      (β := (Y₁' y).map e ≫ sectOf t.1)
      (by rw [map_comp_sectOf_comp r, ← Functor.map_comp, hre, sectOf_naturality r', ← hre,
        Functor.map_comp, Category.assoc])
      (by rw [map_comp_sectOf_comp s₂, ← Functor.map_comp, hse, sectOf_naturality s₂', ← hse,
        Functor.map_comp, Category.assoc])
    obtain ⟨u, hu⟩ := exists_hom_of_sectOf hp hy (A := s.1) (B := t.1) e heq
    exact ⟨⟨u, IsHomLift.of_fac' q _ _ s.2 t.2 (by
      change u.a = _
      rw [hu]
      simp [e])⟩⟩

end Deformation.Artin

end
