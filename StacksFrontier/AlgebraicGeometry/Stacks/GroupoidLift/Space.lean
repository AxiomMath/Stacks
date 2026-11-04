module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.FirstOrder

/-!
# The groupoid of a formally étale chart, and the lifting step for spaces

Let `X` be a functor on the `κ`-small `A'`-algebras with a formally étale chart
`a : Hom(P, -) → X`. Pairs of points of `P` with the same image under `a` form a groupoid in
presheaves, whose source map is formally smooth and whose identities give a formally étale chart
of its arrows. If a point `ū` of `P` over `C' ⧸ I C'` has two equal images under the two maps of
the Čech nerve, then a lift `u` of `ū` over `C'` may be chosen with the same property.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.chartGroupoid`: the groupoid of pairs of points of `P`
  with the same image under the chart.
* `AlgebraicGeometry.Stack.GroupoidLift.idtChart`: its identities, as a chart of its arrows.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.chartGroupoid_srcFormallySmooth`: for a formally étale
  chart, the source map of the groupoid is formally smooth.
* `AlgebraicGeometry.Stack.GroupoidLift.idtChart_isFormallyEtale`: for a formally étale chart,
  the identities form a formally étale chart.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_chart`: a point `ū` of `P` over
  `C' ⧸ I C'` with equal images in the Čech nerve has a lift over `C'` with the same property.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_chart_of_isSheaf`: for a functor with the
  sheaf condition along `A' → C'` and separated along its reduction, a point over `A' ⧸ I` which
  comes from the chart over `C' ⧸ I C'` lifts to a point over `A'`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
  {X : SmallAlg A' κ ⥤ Type u} {P : Type u} [CommRing P] [Algebra A' P]

/-- The presheaf of pairs of points of `P` with the same image under the chart. -/
def chartArr (a : Chart X P) : SmallAlg A' κ ⥤ Type u where
  obj C := {p : (P →ₐ[A'] C.obj) × (P →ₐ[A'] C.obj) // a.app C p.1 = a.app C p.2}
  map h := TypeCat.ofHom fun p ↦ ⟨(h.hom.hom.comp p.1.1, h.hom.hom.comp p.1.2), by
    rw [← a.natural, ← a.natural, p.2]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Two pairs in `chartArr a` are equal if their components are. -/
theorem chartArr_ext (a : Chart X P) {C : SmallAlg A' κ} {p p' : (chartArr a).obj C}
    (h₁ : p.1.1 = p'.1.1) (h₂ : p.1.2 = p'.1.2) : p = p' :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- The groupoid of a chart: the pairs of points of `P` with the same image under the chart. -/
def chartGroupoid (a : Chart X P) : Groupoid A' κ P where
  arr := chartArr a
  src p := p.1.1
  tgt p := p.1.2
  idt w := ⟨(w, w), rfl⟩
  comp g f h := ⟨(f.1.1, g.1.2), f.2.trans ((congrArg (a.app _) h).symm.trans g.2)⟩
  inv g := ⟨(g.1.2, g.1.1), g.2.symm⟩
  src_map _ _ := rfl
  tgt_map _ _ := rfl
  idt_map _ _ := rfl
  comp_map _ _ _ _ := rfl
  inv_map _ _ := rfl
  src_idt _ := rfl
  tgt_idt _ := rfl
  src_comp _ _ _ := rfl
  tgt_comp _ _ _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_idt _ := rfl
  idt_comp _ := rfl
  comp_inv _ := chartArr_ext a rfl rfl
  inv_comp _ := chartArr_ext a rfl rfl
  assoc _ _ _ _ _ := rfl

variable {a : Chart X P}

/-- Two arrows of the groupoid of a chart are equal if their sources and targets are. -/
theorem chartGroupoid_ext {C : SmallAlg A' κ} {g g' : (chartGroupoid a).arr.obj C}
    (h₁ : (chartGroupoid a).src g = (chartGroupoid a).src g')
    (h₂ : (chartGroupoid a).tgt g = (chartGroupoid a).tgt g') : g = g' :=
  chartArr_ext a h₁ h₂

/-- The source map of the groupoid of a formally étale chart is formally smooth. -/
theorem chartGroupoid_srcFormallySmooth (ha : a.IsFormallyEtale) :
    (chartGroupoid a).SrcFormallySmooth := by
  intro C' C e r ℓ hℓ
  have hX : X.map e.q (a.app C' ℓ) = a.app C r.1.2 := by
    rw [a.natural]
    exact (congrArg (a.app C) hℓ).trans r.2
  obtain ⟨m, ⟨hm, hma⟩, -⟩ := ha C' C e.q e.surj e.sq r.1.2 (a.app C' ℓ) hX
  exact ⟨⟨(ℓ, m), hma.symm⟩, chartArr_ext a hℓ hm, rfl⟩

/-- The identities of the groupoid of a chart, as a chart of its arrows. -/
def idtChart (a : Chart X P) : Chart (chartGroupoid a).arr P where
  app _ v := (chartGroupoid a).idt v
  natural _ _ := rfl

/-- The identities of the groupoid of a formally étale chart form a formally étale chart. -/
theorem idtChart_isFormallyEtale (ha : a.IsFormallyEtale) : (idtChart a).IsFormallyEtale := by
  intro R Q q hq hsq c z hz
  have h₁ : q.hom.hom.comp z.1.1 = c := congrArg (fun p : (chartArr a).obj Q ↦ p.1.1) hz
  have h₂ : q.hom.hom.comp z.1.2 = c := congrArg (fun p : (chartArr a).obj Q ↦ p.1.2) hz
  have hX : X.map q (a.app R z.1.1) = a.app Q c := by rw [a.natural, h₁]
  have heq : z.1.2 = z.1.1 :=
    (ha R Q q hq hsq c (a.app R z.1.1) hX).unique ⟨h₂, z.2.symm⟩ ⟨h₁, rfl⟩
  exact ⟨z.1.1, ⟨h₁, chartArr_ext a rfl heq.symm⟩,
    fun ℓ ⟨_, hℓ⟩ ↦ congrArg (fun p : (chartArr a).obj R ↦ p.1.1) hℓ⟩

variable (hκ : Cardinal.aleph0 < κ) {C' : Type u} [CommRing C'] [Algebra A' C']
  (hC : Cardinal.mk C' < κ) {I : Ideal A'} (hI : I ^ 2 = ⊥)

omit [CommRing P] [Algebra A' P] in
/-- If `codeg 0 ∘ f` is the identity, then reducing `f` and then `codeg 0` fixes a point `ubar` of
the reduction of `C'`. -/
theorem redMap_codeg_comp {Q : Type u} [CommRing Q] [Algebra A' Q] (f : C' →ₐ[A'] cech A' C' 1)
    (ubar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
    (hf : (codeg A' C' 0).comp f = AlgHom.id A' _) :
    (redMap I (N := nerve (A' := A') hκ C' hC 1) (N' := nerve (A' := A') hκ C' hC 0)
      (codeg A' C' 0)).comp ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) f).comp ubar) = ubar := by
  rw [← AlgHom.comp_assoc, redMap_comp, hf, redMap_id]
  rfl

omit [CommRing P] [Algebra A' P] in
/-- If `f₁ ∘ g₁ = f₂ ∘ g₂` as maps of the Čech nerve, then their reductions agree after composing
with a point `ubar` of the reduction of `C'`. -/
theorem redMap_comp_comp_eq {Q : Type u} [CommRing Q] [Algebra A' Q] {n m : ℕ}
    (f₁ f₂ : cech A' C' n →ₐ[A'] cech A' C' m) (g₁ g₂ : C' →ₐ[A'] cech A' C' n)
    (ubar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj) (h : f₁.comp g₁ = f₂.comp g₂) :
    (redMap I (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m) f₁).comp
      ((redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n) g₁).comp
        ubar) =
    (redMap I (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m) f₂).comp
      ((redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n) g₂).comp
        ubar) := by
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, redMap_comp, redMap_comp, h]

/-- The nerve datum of a point of `P` over `C' ⧸ I C'` whose two images in the Čech nerve
agree under the chart. -/
noncomputable def chartNerveDatum [Algebra.FormallySmooth A' P]
    (ubar : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
    (hx : a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC 1)
      (v₀ A' C' 1)).comp ubar) = a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).comp ubar)) :
    NerveDatum hκ C' hC I hI (chartGroupoid a) where
  ubar := ubar
  u₀ := Algebra.FormallySmooth.lift (I.map (algebraMap A' C')) ⟨2, by
      rw [Ideal.zero_eq_bot, ← Ideal.map_pow, hI, Ideal.map_bot]⟩ ubar
  u₀_lift := AlgHom.ext (Algebra.FormallySmooth.mk_lift _ _ _)
  rbar := ⟨(_, _), hx⟩
  src_rbar := rfl
  tgt_rbar := rfl
  norm_rbar := chartGroupoid_ext (redMap_codeg_comp hκ hC _ ubar (codeg_comp_face_one 0))
    (redMap_codeg_comp hκ hC _ ubar (codeg_comp_vₗ 0))

/-- **The lifting step for a formally étale chart.** Let `C'` be faithfully flat over `A'` and
let `ū` be a point of `P` over `C' ⧸ I C'` whose images along the two maps `C' ⇉ C' ⊗ C'` agree
under the chart. Then `ū` has a lift `u` over `C'` whose images along the two maps agree. -/
theorem exists_lift_of_chart (ha : a.IsFormallyEtale) [Algebra.FormallySmooth A' P]
    [Algebra.FiniteType A' P] [Module.FaithfullyFlat A' C']
    (ubar : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
    (hx : a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC 1)
      (v₀ A' C' 1)).comp ubar) = a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).comp ubar)) :
    ∃ u : P →ₐ[A'] C', (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = ubar ∧
      a.app (nerve (A' := A') hκ C' hC 1) ((v₀ A' C' 1).comp u) =
        a.app (nerve (A' := A') hκ C' hC 1) ((vₗ A' C' 1).comp u) := by
  let D := chartNerveDatum hκ hC hI ubar hx
  have hcoc : D.IsCocycle :=
    ⟨redMap_comp_comp_eq hκ hC _ _ _ _ ubar (AlgHom.ext fun _ ↦ rfl), chartGroupoid_ext
      (redMap_comp_comp_eq hκ hC _ _ _ _ ubar
        ((face_succ_comp_v₀ 1 1).trans (face_succ_comp_v₀ 1 0).symm))
      (redMap_comp_comp_eq hκ hC _ _ _ _ ubar
        ((face_comp_vₗ 1 0 (by decide)).trans (face_comp_vₗ 1 1 (by decide)).symm))⟩
  obtain ⟨u, hu, r, -, hs, ht⟩ := D.exists_lift_arrow (chartGroupoid_srcFormallySmooth ha)
    (b := idtChart a) (idtChart_isFormallyEtale ha) (sV := AlgHom.id A' P)
    (tV := AlgHom.id A' P) (fun _ v ↦ (AlgHom.comp_id v).symm) (fun _ v ↦ (AlgHom.comp_id v).symm)
    ubar D.u₀ D.u₀_lift rfl hcoc
  refine ⟨u, hu, ?_⟩
  rw [← show (chartGroupoid a).src r = (v₀ A' C' 1).comp u from hs,
    ← show (chartGroupoid a).tgt r = (vₗ A' C' 1).comp u from ht]
  exact r.2

/-- `A'` as a `κ`-small `A'`-algebra. -/
abbrev baseAlg (hA : Cardinal.mk A' < κ) : SmallAlg A' κ := SmallAlg.mk A' hA

/-- The structure map `A' → C'` as a map of the nerve. -/
abbrev baseMap (hA : Cardinal.mk A' < κ) :
    baseAlg hA ⟶ nerve (A' := A') hκ C' hC 0 :=
  SmallAlg.homMk (Algebra.ofId A' C')

/-- The structure map `A' → C'` as a map of thickenings. -/
abbrev baseThk (hA : Cardinal.mk A' < κ) :
    SqZero.Hom (thk I hI (baseAlg hA)) (thk I hI (nerve (A' := A') hκ C' hC 0)) :=
  thkHom I hI (N := baseAlg hA) (N' := nerve (A' := A') hκ C' hC 0) (Algebra.ofId A' C')

omit [CommRing P] [Algebra A' P] in
/-- A point of `X` over `A' ⧸ I`, pulled back to `C' ⧸ I C'`, has equal images along the two maps
of the reduced Čech nerve. -/
theorem map_baseMap_v₀_eq_vₗ (hA : Cardinal.mk A' < κ) (x : X.obj (red I (baseAlg hA))) :
    X.map (SmallAlg.homMk (redMap I (N := nerve (A' := A') hκ C' hC 0)
      (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)))
        (X.map (baseThk hκ hC hI hA).bot x) =
    X.map (SmallAlg.homMk (redMap I (N := nerve (A' := A') hκ C' hC 0)
      (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)))
        (X.map (baseThk hκ hC hI hA).bot x) := by
  have h : (baseThk hκ hC hI hA).bot ≫ SmallAlg.homMk (redMap I
      (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)) =
      (baseThk hκ hC hI hA).bot ≫ SmallAlg.homMk (redMap I
        (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)) := by
    show SmallAlg.homMk (redMap I (N := baseAlg hA) (N' := nerve (A' := A') hκ C' hC 0)
      (Algebra.ofId A' C')) ≫ _ = SmallAlg.homMk (redMap I (N := baseAlg hA)
        (N' := nerve (A' := A') hκ C' hC 0) (Algebra.ofId A' C')) ≫ _
    rw [SmallAlg.homMk_comp, SmallAlg.homMk_comp, redMap_comp, redMap_comp]
    exact congrArg (fun f ↦ SmallAlg.homMk (redMap I f)) (Subsingleton.elim _ _)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, h]

/-- **The lifting step for a sheaf with a formally étale chart.** Let `X` be a functor on the
`κ`-small `A'`-algebras satisfying the sheaf condition for the faithfully flat `A' → C'` and
separated for its reduction `A' ⧸ I → C' ⧸ I C'`, with a formally étale chart by a formally
smooth `A'`-algebra `P` of finite type. If a point `x` of `X` over `A' ⧸ I` comes from `P` over
`C' ⧸ I C'`, then `x` lifts to a point of `X` over `A'`. -/
theorem exists_lift_of_chart_of_isSheaf (ha : a.IsFormallyEtale) [Algebra.FormallySmooth A' P]
    [Algebra.FiniteType A' P] [Module.FaithfullyFlat A' C'] (hA : Cardinal.mk A' < κ)
    (hsheaf : ∀ z : X.obj (nerve (A' := A') hκ C' hC 0),
      X.map (SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
        (R' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)) z =
        X.map (SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
          (R' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)) z →
        ∃ x' : X.obj (baseAlg hA), X.map (baseMap hκ hC hA) x' = z)
    (hsep : ∀ x₁ x₂ : X.obj (red I (baseAlg hA)),
      X.map (baseThk hκ hC hI hA).bot x₁ =
        X.map (baseThk hκ hC hI hA).bot x₂ → x₁ = x₂)
    (x : X.obj (red I (baseAlg hA)))
    (ubar : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
    (hubar : a.app _ ubar = X.map (baseThk hκ hC hI hA).bot x) :
    ∃ x' : X.obj (baseAlg hA), X.map (thk I hI (baseAlg hA)).q x' = x := by
  have hx : a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0)
      (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)).comp ubar) =
      a.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).comp ubar) := by
    rw [← SmallAlg.homMk_hom (redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)),
      ← SmallAlg.homMk_hom (redMap I (N := nerve (A' := A') hκ C' hC 0)
        (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)), ← a.natural, ← a.natural, hubar]
    exact map_baseMap_v₀_eq_vₗ hκ hC hI hA x
  obtain ⟨u, hu, huv⟩ := exists_lift_of_chart hκ hC hI ha ubar hx
  obtain ⟨x', hx'⟩ := hsheaf (a.app _ u) (by rwa [a.natural, a.natural])
  refine ⟨x', hsep _ _ ?_⟩
  have hx'' : X.map (baseThk hκ hC hI hA).top x' = a.app _ u := hx'
  rw [← FunctorToTypes.map_comp_apply, ← (baseThk hκ hC hI hA).w,
    FunctorToTypes.map_comp_apply, hx'', ← hubar, a.natural, hu]

end AlgebraicGeometry.Stack.GroupoidLift

end
