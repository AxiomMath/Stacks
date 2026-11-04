module

public import Mathlib.CategoryTheory.Triangulated.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.AdmissibleNullHomotopy
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeMorphism

/-!
# Homotopy equivalences in morphisms of cone triangles

In a differential graded category with cones, a morphism between the triangles attached to two
closed degree-zero arrows is an isomorphism on the cones as soon as it is an isomorphism on the
sources and on the targets in the homotopy category.

## Main definitions

* `DGCategory.coneTriangle`: the triangle `x ⟶ y ⟶ c(f) ⟶ x[1]` in the homotopy category.

## Main results

* `DGCategory.isIso_cone_of_isIso_source_target`: the cone analogue of the third-isomorphism
  theorem for morphisms of triangles.

## References

* [Stacks Project, Tag 09QT](https://stacks.math.columbia.edu/tag/09QT)
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe u v w

open CategoryTheory


variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- The cone triangle of a closed degree-zero morphism in the homotopy category, for a shift
additive on objects only up to isomorphism. -/
public def ConeSituationIso.coneTriangle (S : ConeSituationIso A)
    {x y : A.Obj} (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := S.shift.kShift
    Pretriangulated.Triangle A.K := by
  letI : HasShift A.K ℤ := S.shift.kShift
  let E := S.coneSequence f
  have h : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj x =
      (S.shift.shiftFunctor (1 : ℤ)).obj x :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
  exact Pretriangulated.Triangle.mk
    (Quotient.mk (A.homotopySetoid x y) f)
    (Quotient.mk (A.homotopySetoid y (S.cone f)) E.a)
    ((Quotient.mk (A.homotopySetoid (S.cone f) ((S.shift.shiftFunctor 1).obj x))
      E.b) ≫ eqToHom h.symm)


/-- The cone triangle of a closed degree-zero morphism in the homotopy category. -/
public def coneTriangle (S : ConeSituation A)
    {x y : A.Obj} (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := S.shift.kShift
    Pretriangulated.Triangle A.K :=
  S.toConeSituationIso.coneTriangle f

private theorem isIso_third_of_id_first_second
    (S : ConeSituationIso A) {x y : A.Obj} (f : A.Cocycle x y)
    (τ : letI : HasShift A.K ℤ := S.shift.kShift
      S.coneTriangle f ⟶ S.coneTriangle f) :
    letI : HasShift A.K ℤ := S.shift.kShift
    τ.hom₁ = 𝟙 _ → τ.hom₂ = 𝟙 _ → IsIso τ.hom₃ := by
  let _ : HasShift A.K ℤ := S.shift.kShift
  intro h₁ h₂
  let E := S.coneSequence f
  let T := S.coneTriangle f
  let xK : A.K := T.obj₁
  let yK : A.K := T.obj₂
  let cK : A.K := T.obj₃
  let zK : A.K := (S.shift.shiftFunctor 1).onK.obj xK
  let _ : AddCommGroup (A.Hom (S.cone f) (S.cone f) 0) :=
    DGCategory.addCommGroup A _ _ _
  let _ : AddCommGroup (A.Hom (S.cone f) (S.cone f) 1) :=
    DGCategory.addCommGroup A _ _ _
  let _ : AddCommGroup (A.Hom (S.cone f) (S.cone f) (0 + 1)) :=
    DGCategory.addCommGroup A _ _ _
  let _ : AddCommGroup (A.Hom (S.cone f) (S.cone f) (-1)) :=
    DGCategory.addCommGroup A _ _ _
  let _ : Module R (A.Hom (S.cone f) (S.cone f) 0) := DGCategory.module A _ _ _
  let _ : Module R (A.Hom (S.cone f) (S.cone f) 1) := DGCategory.module A _ _ _
  let _ : Module R (A.Hom (S.cone f) (S.cone f) (0 + 1)) := DGCategory.module A _ _ _
  let _ : Module R (A.Hom (S.cone f) (S.cone f) (-1)) := DGCategory.module A _ _ _
  let c : A.Cocycle (S.cone f) (S.cone f) := Quotient.out τ.hom₃
  let ι : A.Cocycle (S.cone f) (S.cone f) := ⟨A.id (S.cone f), A.d_id (S.cone f)⟩
  have h00 : (0 : ℤ) + 0 = 0 := by omega
  have hdneg {p q : A.Obj} {n : ℤ} (g : A.Hom p q n) : A.d (-g) = -A.d g := by
    rw [show -g = (-1 : R) • g by rw [neg_one_smul], A.d_smul, neg_one_smul]
  have hsub_closed (a b : A.Cocycle (S.cone f) (S.cone f)) : A.d (a.1 - b.1) = 0 := by
    rw [sub_eq_add_neg, A.d_add, hdneg, a.2, b.2]
    simp
  let e : A.Cocycle (S.cone f) (S.cone f) := ⟨c.1 - ι.1, hsub_closed c ι⟩
  have h : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj xK = zK := by
    show (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj xK =
      ((S.shift.shiftFunctor 1).onK).obj xK
    exact congrArg (fun F : A.K ⥤ A.K => F.obj xK) (S.shift.kShift_functor 1)
  let qA : yK ⟶ cK := Quotient.mk (A.homotopySetoid y (S.cone f)) E.a
  let qB : cK ⟶ zK :=
    Quotient.mk (A.homotopySetoid (S.cone f) ((S.shift.shiftFunctor 1).obj x)) E.b
  let qC : cK ⟶ cK := Quotient.mk (A.homotopySetoid (S.cone f) (S.cone f)) c
  have hc : qC = τ.hom₃ := Quotient.out_eq _
  have hmor₂ : T.mor₂ = qA := rfl
  have hmor₃ : T.mor₃ = qB ≫ eqToHom h.symm := rfl
  have hleft₀ : A.Homotopic (A.compCocycle c E.a) E.a := Quotient.exact (by
    show qA ≫ qC = qA
    rw [hc]
    have hcomm := τ.comm₂
    change T.mor₂ ≫ τ.hom₃ = τ.hom₂ ≫ T.mor₂ at hcomm
    simpa [hmor₂, h₂] using hcomm)
  have hrightK : qC ≫ qB = qB := by
    have hcomm := τ.comm₃
    change T.mor₃ ≫ τ.hom₁⟦1⟧' = τ.hom₃ ≫ T.mor₃ at hcomm
    rw [h₁, (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map_id, Category.comp_id, hmor₃,
      ← Category.assoc, cancel_mono] at hcomm
    rw [hc, ← hcomm]
  have hright₀ : A.Homotopic (A.compCocycle E.b c) E.b :=
    Quotient.exact (show qC ≫ qB = qB from hrightK)
  have hzero {p q : A.Obj} (u v w : A.Cocycle p q) (hw : w.1 = u.1 - v.1)
      (huv : A.Homotopic u v) : A.Homotopic w ⟨0, A.d_zero⟩ := by
    obtain ⟨g, hg⟩ := huv
    refine ⟨g, ?_⟩
    change w.1 - 0 = A.d' (show (-1 : ℤ) + 1 = 0 by omega) g
    rwa [hw, sub_zero]
  have hleft : A.Homotopic (A.compCocycle e E.a) ⟨0, A.d_zero⟩ :=
    hzero (A.compCocycle c E.a) E.a _
      (by
        change A.comp h00 e.1 E.a.1 = A.comp h00 c.1 E.a.1 - E.a.1
        rw [show e.1 = c.1 - ι.1 by rfl, A.comp_sub_left h00, A.id_comp]) hleft₀
  have hright : A.Homotopic (A.compCocycle E.b e) ⟨0, A.d_zero⟩ :=
    hzero (A.compCocycle E.b c) E.b _
      (by
        change A.comp h00 E.b.1 e.1 = A.comp h00 E.b.1 c.1 - E.b.1
        rw [show e.1 = c.1 - ι.1 by rfl, A.comp_sub_right h00, A.comp_id]) hright₀
  have hnil : A.Homotopic (A.compCocycle e e) ⟨0, A.d_zero⟩ :=
    comp_homotopic_zero_of_gradedSplitShortExact E e e hright hleft
  let r : A.Cocycle (S.cone f) (S.cone f) :=
    ⟨ι.1 - (A.compCocycle e e).1, hsub_closed ι (A.compCocycle e e)⟩
  have hnil' : A.Homotopic r ι := by
    obtain ⟨g, hg⟩ := hnil
    refine ⟨-g, ?_⟩
    show (ι.1 - (A.compCocycle e e).1) - ι.1 =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-g)
    simp only [DGCategory.d', hdneg] at hg ⊢
    rw [← hg]
    simp
  let d : A.Cocycle (S.cone f) (S.cone f) := ⟨ι.1 - e.1, hsub_closed ι e⟩
  have hee : A.comp h00 e.1 e.1 = A.comp h00 c.1 c.1 - c.1 - c.1 + ι.1 := by
    show A.comp h00 (c.1 - ι.1) (c.1 - ι.1) = _
    rw [A.comp_sub_left h00, A.comp_sub_right h00, A.comp_sub_right h00,
      A.comp_id, A.id_comp, A.id_comp]
    abel
  have hcalc₁ : A.comp h00 d.1 c.1 = ι.1 - A.comp h00 e.1 e.1 := by
    show A.comp h00 (ι.1 - e.1) c.1 = _
    rw [A.comp_sub_left h00, A.id_comp, show e.1 = c.1 - ι.1 by rfl,
      A.comp_sub_left h00, A.id_comp, hee]
    abel
  have hcalc₂ : A.comp h00 c.1 d.1 = ι.1 - A.comp h00 e.1 e.1 := by
    show A.comp h00 c.1 (ι.1 - e.1) = _
    rw [A.comp_sub_right h00, A.comp_id, show e.1 = c.1 - ι.1 by rfl,
      A.comp_sub_right h00, A.comp_id, hee]
    abel
  let qd : cK ⟶ cK := Quotient.mk _ d
  have hinvK (a b : A.Cocycle (S.cone f) (S.cone f))
      (hab : A.comp h00 a.1 b.1 = ι.1 - A.comp h00 e.1 e.1) :
      Quotient.mk (A.homotopySetoid (S.cone f) (S.cone f)) b ≫
        Quotient.mk (A.homotopySetoid (S.cone f) (S.cone f)) a = 𝟙 cK := by
    change A.compK (Quotient.mk _ a) (Quotient.mk _ b) =
      Quotient.mk (A.homotopySetoid (S.cone f) (S.cone f)) ι
    rw [DGCategory.compK, Quotient.map₂_mk]
    have : A.Homotopic (A.compCocycle a b) ι := by
      convert hnil' using 1
      exact Subtype.ext hab
    exact Quotient.sound this
  have hinv₁K : qd ≫ τ.hom₃ = 𝟙 cK := by
    rw [← hc]
    exact hinvK c d hcalc₂
  have hinv₂K : τ.hom₃ ≫ qd = 𝟙 cK := by
    rw [← hc]
    exact hinvK d c hcalc₁
  exact ⟨qd, hinv₂K, hinv₁K⟩

private theorem isIso_of_isIso_composites {C : Type u} [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    [IsIso (f ≫ g)] [IsIso (g ≫ f)] : IsIso f := by
  have : IsSplitMono f := IsSplitMono.mk' ⟨g ≫ inv (f ≫ g), by rw [← Category.assoc,
    IsIso.hom_inv_id]⟩
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨inv (g ≫ f) ≫ g, by rw [Category.assoc,
    IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi f

/-- For a shift additive on objects only up to isomorphism: in a morphism of cone triangles,
homotopy equivalences on the source and target induce a homotopy equivalence on the cones. -/
public theorem ConeSituationIso.isIso_cone_of_isIso_source_target
    (S : ConeSituationIso A)
    {x₁ y₁ x₂ y₂ : A.Obj} (f₁ : A.Cocycle x₁ y₁) (f₂ : A.Cocycle x₂ y₂)
    (φ :
      letI : HasShift A.K ℤ := S.shift.kShift
      S.coneTriangle f₁ ⟶ S.coneTriangle f₂) :
    letI : HasShift A.K ℤ := S.shift.kShift
    IsIso φ.hom₁ → IsIso φ.hom₂ → IsIso φ.hom₃ := by
  let _ : HasShift A.K ℤ := S.shift.kShift
  intro h₁ h₂
  let _ : Category A.K := DGCategory.instCategoryK A
  let T₁ := S.coneTriangle f₁
  let T₂ := S.coneTriangle f₂
  let aInv : A.Cocycle x₂ x₁ := Quotient.out (inv φ.hom₁)
  let bInv : A.Cocycle y₂ y₁ := Quotient.out (inv φ.hom₂)
  let qf₁ : T₁.obj₁ ⟶ T₁.obj₂ := Quotient.mk _ f₁
  let qf₂ : T₂.obj₁ ⟶ T₂.obj₂ := Quotient.mk _ f₂
  let qaInv : T₂.obj₁ ⟶ T₁.obj₁ := Quotient.mk _ aInv
  let qbInv : T₂.obj₂ ⟶ T₁.obj₂ := Quotient.mk _ bInv
  have hqaInv : qaInv = inv φ.hom₁ := Quotient.out_eq _
  have hqbInv : qbInv = inv φ.hom₂ := Quotient.out_eq _
  have hφcomm : φ.hom₁ ≫ qf₂ = qf₁ ≫ φ.hom₂ := φ.comm₁.symm
  have hcommInv : A.compK qbInv qf₂ = A.compK qf₁ qaInv := by
    show qf₂ ≫ qbInv = qaInv ≫ qf₁
    rw [hqaInv, hqbInv, IsIso.eq_inv_comp, ← Category.assoc, hφcomm, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  obtain ⟨cInv, hcInv₁, hcInv₂⟩ :=
    exists_coneTriangleMorphism S f₂ f₁ aInv bInv hcommInv
  let qcInv : T₂.obj₃ ⟶ T₁.obj₃ := Quotient.mk _ cInv
  let ψ : T₂ ⟶ T₁ := Pretriangulated.Triangle.homMk T₂ T₁ qaInv qbInv qcInv
    hcommInv hcInv₁
    (by
      let F := CategoryTheory.shiftFunctor A.K (1 : ℤ)
      let G := (S.shift.shiftFunctor 1).onK
      have hfun : F = G := S.shift.kShift_functor 1
      have h₂ : F.obj T₂.obj₁ = G.obj T₂.obj₁ :=
        congrArg (fun H : A.K ⥤ A.K => H.obj T₂.obj₁) hfun
      have h₁ : F.obj T₁.obj₁ = G.obj T₁.obj₁ :=
        congrArg (fun H : A.K ⥤ A.K => H.obj T₁.obj₁) hfun
      let qB₂ : T₂.obj₃ ⟶ G.obj T₂.obj₁ :=
        Quotient.mk _ (S.coneSequence f₂).b
      let qB₁ : T₁.obj₃ ⟶ G.obj T₁.obj₁ :=
        Quotient.mk _ (S.coneSequence f₁).b
      have hGmap : G.map qaInv =
          Quotient.mk _ ((S.shift.shiftFunctor 1).mapCocycle aInv) := by
        dsimp [DGCategory.K] at qaInv
        show (S.shift.shiftFunctor 1).mapHomotopyClass
          (Quotient.mk (A.homotopySetoid x₂ x₁) aInv) = _
        dsimp [DGCategory.DGFunctor.mapHomotopyClass]
        rfl
      have hcore : qB₂ ≫ G.map qaInv = qcInv ≫ qB₁ := by
        rw [hGmap]
        show A.compK (Quotient.mk _ ((S.shift.shiftFunctor 1).mapCocycle aInv))
            (Quotient.mk _ (S.coneSequence f₂).b) =
          A.compK (Quotient.mk _ (S.coneSequence f₁).b) (Quotient.mk _ cInv)
        exact hcInv₂.symm
      have htransport : eqToHom h₂.symm ≫ F.map qaInv =
          G.map qaInv ≫ eqToHom h₁.symm := by
        have hh := CategoryTheory.Functor.congr_hom hfun qaInv
        simpa [Category.assoc] using congrArg (fun m => eqToHom h₂.symm ≫ m) hh
      show (qB₂ ≫ eqToHom h₂.symm) ≫ F.map qaInv =
        qcInv ≫ (qB₁ ≫ eqToHom h₁.symm)
      rw [Category.assoc, htransport, ← Category.assoc, hcore, Category.assoc])
  have htop₁ : (φ ≫ ψ).hom₁ = 𝟙 T₁.obj₁ := by
    rw [CategoryTheory.Pretriangulated.comp_hom₁]
    show φ.hom₁ ≫ qaInv = _
    simp [hqaInv, T₁]
  have htop₂ : (φ ≫ ψ).hom₂ = 𝟙 T₁.obj₂ := by
    rw [CategoryTheory.Pretriangulated.comp_hom₂]
    show φ.hom₂ ≫ qbInv = _
    simp [hqbInv, T₁]
  have hbottom₁ : (ψ ≫ φ).hom₁ = 𝟙 T₂.obj₁ := by
    rw [CategoryTheory.Pretriangulated.comp_hom₁]
    show qaInv ≫ φ.hom₁ = _
    simp [hqaInv]
  have hbottom₂ : (ψ ≫ φ).hom₂ = 𝟙 T₂.obj₂ := by
    rw [CategoryTheory.Pretriangulated.comp_hom₂]
    show qbInv ≫ φ.hom₂ = _
    simp [hqbInv]
  have : IsIso (φ.hom₃ ≫ ψ.hom₃) := by
    rw [← CategoryTheory.Pretriangulated.comp_hom₃]
    exact isIso_third_of_id_first_second S f₁ (φ ≫ ψ) htop₁ htop₂
  have : IsIso (ψ.hom₃ ≫ φ.hom₃) := by
    rw [← CategoryTheory.Pretriangulated.comp_hom₃]
    exact isIso_third_of_id_first_second S f₂ (ψ ≫ φ) hbottom₁ hbottom₂
  exact isIso_of_isIso_composites φ.hom₃ ψ.hom₃


/-- In a morphism of cone triangles, homotopy equivalences on the source and target
induce a homotopy equivalence on the cones. -/
@[stacks 09QT]
public theorem isIso_cone_of_isIso_source_target
    (S : ConeSituation A)
    {x₁ y₁ x₂ y₂ : A.Obj} (f₁ : A.Cocycle x₁ y₁) (f₂ : A.Cocycle x₂ y₂)
    (φ :
      letI : HasShift A.K ℤ := S.shift.kShift
      coneTriangle S f₁ ⟶ coneTriangle S f₂) :
    letI : HasShift A.K ℤ := S.shift.kShift
    IsIso φ.hom₁ → IsIso φ.hom₂ → IsIso φ.hom₃ :=
  ConeSituationIso.isIso_cone_of_isIso_source_target S.toConeSituationIso f₁ f₂ φ
end DGCategory
