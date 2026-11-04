module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Deformation.Artin.Infinitesimal.OverLiftClasses
public import StacksFrontier.Deformation.Artin.Obstruction.TangentPullback
public import StacksFrontier.RingTheory.Kaehler.ChartDerivationBaseChange

/-!
# The tangent spaces of an affine chart

Let `S` be a scheme, `j : Spec Λ → S` a monomorphism (an affine open of `S`, say) and `P` a
`Λ`-algebra, so that `U = Spec P` is a scheme over `S`. Regard `U` as a category fibred in
groupoids over the big fppf site of `S` through the slice `Sch/U`, as in
`AlgebraicGeometry.Stack.schemeFibredCategory`. For a point `x : Spec A → U` over `S` and an
`A`-module `M`, the isomorphism classes of lifts of `x` to `Spec A[M]` are the derivations
`chartDer Λ u M` of `P` along the ring map `u : P → A` of `x`: a lift is an arrow
`Spec A[M] → Spec P` over `S` restricting to `x`, that is a ring map `P → A[M]` over `Λ` lifting
`u`, that is `a ↦ (u a, D a)` for a derivation `D`.

This is the identification `T_x(M) = Hom_A(x^*Ω_{X/S}, M)` of the third paragraph of the proof
of Stacks 0DNT, at an affine chart over an affine open of `S`.

## Main definitions

* `Deformation.Artin.affineChart` — `Spec P` as an object of the big fppf site over `S`.
* `Deformation.Artin.chartPoint` — the ring map `P → A` of a point `x : Spec A → Spec P`.
* `Deformation.Artin.chartLiftEquiv` — the arrows `Spec A[M] → Spec P` over `S` restricting to
  `x` are the derivations `chartDer Λ u M`.
* `Deformation.Artin.chartLiftClassEquiv` — the lift classes of `x` over `A[M]` are the
  derivations `chartDer Λ u M`.
* `Deformation.Artin.chartTangentLinearEquiv` — for any tangent functor `T_x`
  (`Deformation.Artin.TangentFunctorData`), the identification `T_x(M) ≅ chartDer Λ u M` is
  `A`-linear.

## Main results

* `Deformation.Artin.chartLiftClassEquiv_pullback`,
  `Deformation.Artin.chartLiftClassEquiv_liftClassPullback` — under the identification, pullback
  of lift classes along a module map, and along the map of Stacks 07YA, is composition of
  derivations.
* `Deformation.Artin.exists_chartTangent_flatBaseChange` — **Stacks 0DNT at an affine chart**:
  for `P` of finite presentation over `Λ` and a flat `A → C`, the map of Stacks 07YA induces a
  `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)`.

The general statement of Stacks 0DNT reduces to this one through the first two paragraphs of
its proof (the sheaf property of Stacks 0DNS, the smooth atlas, the exact sequence of
Stacks 0DNN) and the reduction of an algebraic space to its affine étale charts; none of these
reductions is in this file, so no `@[stacks 0DNT]` is attached here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StacksDraft.ChartDerivation

namespace Deformation.Artin

universe u

section AffineChart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Λ P : Type u) [CommRing Λ] [CommRing P] [Algebra Λ P] (hP : B.Contains (Spec (.of P)))
  (j : Spec (.of Λ) ⟶ S)

/-- The affine scheme `Spec P`, over `S` through `Spec P → Spec Λ → S`, as an object of the big
fppf site over `S`. -/
public def affineChart : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ j) :
    B.obj hP ⟶ B.obj hS)

variable {Λ P hP j} {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {x : Over (affineChart (hS := hS) Λ P hP j)}
  (hx : (Over.forget _).obj x = algebraOver A B S hS toS hA)

/-- The ring map `P → A` of a point `x : Spec A → Spec P`. -/
public def chartPoint : P →+* A :=
  (Spec.preimage (R := .of P) (S := .of A)
    ((BigFppfOver.toScheme B S hS).map (eqToHom hx.symm ≫ x.hom))).hom

/-- `Spec` of the ring map `chartPoint hx : P → A` recovers the point `x`. -/
public theorem specMap_chartPoint :
    Spec.map (CommRingCat.ofHom (chartPoint hx)) =
      (BigFppfOver.toScheme B S hS).map (eqToHom hx.symm ≫ x.hom) :=
  Spec.map_preimage _

/-- A point of the chart lies over `S`. -/
public theorem specMap_chartPoint_comp :
    Spec.map (CommRingCat.ofHom (chartPoint hx)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ j = toS := by
  rw [specMap_chartPoint]
  exact congrArg (BigFppfSite.inclusion B).map (Over.w (eqToHom hx.symm ≫ x.hom))

variable (M : SiteModule A B)

/-- The ring map `P → A[M]` of an arrow `Spec A[M] → Spec P`. -/
public def chartLiftRing (g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j) :
    P →+* TrivSqZeroExt A M.obj :=
  (Spec.preimage (R := .of P) (S := squareZeroRing A M.obj)
    ((BigFppfOver.toScheme B S hS).map g)).hom

/-- `Spec` of the ring map `chartLiftRing M g : P → A[M]` recovers the arrow `g`. -/
public theorem specMap_chartLiftRing (g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j) :
    Spec.map (CommRingCat.ofHom (chartLiftRing M g)) = (BigFppfOver.toScheme B S hS).map g :=
  Spec.map_preimage _

/-- A ring map whose `Spec` is the composite of the `Spec`s of two ring maps is their composite. -/
private theorem eq_comp_of_specMap_eq_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (F : R →+* T) (g : R →+* S) (h : S →+* T)
    (H : Spec.map (CommRingCat.ofHom F) =
      Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom g)) : F = h.comp g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom F)
    (a₂ := CommRingCat.ofHom g ≫ CommRingCat.ofHom h) (by rw [H, Spec.map_comp]))

include hx in
/-- The ring map of a lift lifts the ring map of the point. -/
public theorem chartLiftRing_fst {g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j}
    (hg : squareZeroArrow A B S hS toS hA M ≫ g = eqToHom hx.symm ≫ x.hom) (a : P) :
    (chartLiftRing M g a).fst = chartPoint hx a := by
  exact (DFunLike.congr_fun (eq_comp_of_specMap_eq_comp (chartPoint hx) (chartLiftRing M g)
    (TrivSqZeroExt.fstHom A A M.obj).toRingHom (by
      rw [specMap_chartPoint, specMap_chartLiftRing, ← hg, Functor.map_comp]; rfl)) a).symm

include hx in
/-- The ring map of a lift is a map of `Λ`-algebras. -/
public theorem chartLiftRing_algebraMap [Mono j]
    (g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j) (c : Λ) :
    chartLiftRing M g (algebraMap Λ P c) =
      TrivSqZeroExt.inl (chartPoint hx (algebraMap Λ P c)) := by
  have h : CommRingCat.ofHom (algebraMap Λ P) ≫ CommRingCat.ofHom (chartLiftRing M g) =
      CommRingCat.ofHom (algebraMap Λ P) ≫ CommRingCat.ofHom (chartPoint hx) ≫
        CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) := by
    apply Spec.map_injective
    rw [← cancel_mono j]
    simp only [Spec.map_comp, Category.assoc]
    rw [specMap_chartLiftRing, specMap_chartPoint_comp hx]
    exact congrArg (BigFppfSite.inclusion B).map (Over.w g)
  exact congrArg (fun r : CommRingCat.of Λ ⟶ squareZeroRing A M.obj => r.hom c) h

include hx in
/-- The derivation of a lift: the second component of its ring map. -/
public def chartLiftDer [Mono j] {g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j}
    (hg : squareZeroArrow A B S hS toS hA M ≫ g = eqToHom hx.symm ≫ x.hom) :
    chartDer Λ (chartPoint hx) M.obj :=
  ⟨{ toFun := fun a => (chartLiftRing M g a).snd
     map_zero' := by simp
     map_add' := fun a b => by simp },
    fun a b => by
      change (chartLiftRing M g (a * b)).snd = chartPoint hx a • (chartLiftRing M g b).snd +
        chartPoint hx b • (chartLiftRing M g a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, chartLiftRing_fst hx M hg, chartLiftRing_fst hx M hg,
        op_smul_eq_smul],
    fun c => by
      change (chartLiftRing M g (algebraMap Λ P c)).snd = 0
      rw [chartLiftRing_algebraMap hx M g c, TrivSqZeroExt.snd_inl]⟩

/-- The ring map `P → A[M]`, `a ↦ (u a, D a)`, of a derivation along `u`. -/
public def chartRingOfDer (D : chartDer Λ (chartPoint hx) M.obj) :
    P →+* TrivSqZeroExt A M.obj where
  toFun a := (chartPoint hx a, (D : P →+ M.obj) a)
  map_one' := by
    have h := chartDer_leibniz D 1 1
    simp only [mul_one, map_one, one_smul] at h
    nth_rewrite 1 [← add_zero ((D : P →+ M.obj) 1)] at h
    exact TrivSqZeroExt.ext (map_one _) (add_left_cancel h).symm
  map_mul' a b := by
    refine TrivSqZeroExt.ext (map_mul _ a b) ?_
    change (D : P →+ M.obj) (a * b) =
      chartPoint hx a • (D : P →+ M.obj) b + MulOpposite.op (chartPoint hx b) • (D : P →+ M.obj) a
    rw [op_smul_eq_smul, chartDer_leibniz]
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero _)
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (map_add _ a b)

/-- `chartRingOfDer hx M D` sends `a` to `(u a, D a)`. -/
@[simp]
public theorem chartRingOfDer_apply (D : chartDer Λ (chartPoint hx) M.obj) (a : P) :
    chartRingOfDer hx M D a = (chartPoint hx a, (D : P →+ M.obj) a) := rfl

/-- The arrow `Spec A[M] → Spec P` over `S` of a derivation along the point. -/
public def chartHomOfDer (D : chartDer Λ (chartPoint hx) M.obj) :
    squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (chartRingOfDer hx M D))) :
      B.obj M.property ⟶ B.obj hP) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (chartRingOfDer hx M D)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ j) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS
    have h : CommRingCat.ofHom (algebraMap Λ P) ≫ CommRingCat.ofHom (chartRingOfDer hx M D) =
        CommRingCat.ofHom (algebraMap Λ P) ≫ CommRingCat.ofHom (chartPoint hx) ≫
          CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) := by
      ext c
      · rfl
      · change (D : P →+ M.obj) (algebraMap Λ P c) = 0
        exact chartDer_algebraMap D c
    calc Spec.map (CommRingCat.ofHom (chartRingOfDer hx M D)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ j)
        = Spec.map (CommRingCat.ofHom (algebraMap Λ P) ≫
            CommRingCat.ofHom (chartRingOfDer hx M D)) ≫ j := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ P) ≫ CommRingCat.ofHom (chartPoint hx) ≫
            CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ j := by rw [h]
      _ = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫
            (Spec.map (CommRingCat.ofHom (chartPoint hx)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap Λ P)) ≫ j) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS := by
          rw [specMap_chartPoint_comp hx])

/-- The ring map of the arrow `chartHomOfDer hx M D` is `chartRingOfDer hx M D`. -/
public theorem chartLiftRing_chartHomOfDer (D : chartDer Λ (chartPoint hx) M.obj) :
    chartLiftRing M (chartHomOfDer hx M D) = chartRingOfDer hx M D := by
  change (Spec.preimage (Spec.map (CommRingCat.ofHom (chartRingOfDer hx M D)))).hom = _
  rw [Spec.preimage_map]
  rfl

/-- The arrow `chartHomOfDer hx M D` restricts to the point `x` along `Spec A ⟶ Spec A[M]`:
it is a lift of `x`. -/
public theorem squareZeroArrow_comp_chartHomOfDer (D : chartDer Λ (chartPoint hx) M.obj) :
    squareZeroArrow A B S hS toS hA M ≫ chartHomOfDer hx M D = eqToHom hx.symm ≫ x.hom := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (chartRingOfDer hx M D)) =
    (BigFppfOver.toScheme B S hS).map (eqToHom hx.symm ≫ x.hom)
  rw [← specMap_chartPoint hx, ← Spec.map_comp]
  rfl

/-- **The lifts of a point of an affine chart are derivations.** The arrows
`Spec A[M] → Spec P` over `S` restricting to `x : Spec A → Spec P` are the `Λ`-derivations of
`P` along the ring map of `x`. -/
public def chartLiftEquiv [Mono j] :
    { g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j //
        squareZeroArrow A B S hS toS hA M ≫ g = eqToHom hx.symm ≫ x.hom } ≃
      chartDer Λ (chartPoint hx) M.obj where
  toFun g := chartLiftDer hx M g.2
  invFun D := ⟨chartHomOfDer hx M D, squareZeroArrow_comp_chartHomOfDer hx M D⟩
  left_inv g := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (chartRingOfDer hx M (chartLiftDer hx M g.2))) =
      (BigFppfOver.toScheme B S hS).map g.1
    rw [← specMap_chartLiftRing]
    congr 2
    ext a
    · exact (chartLiftRing_fst hx M g.2 a).symm
    · rfl
  right_inv D := by
    ext a
    change (chartLiftRing M (chartHomOfDer hx M D) a).snd = _
    rw [chartLiftRing_chartHomOfDer]
    rfl

/-- **The lift classes of a point of an affine chart are derivations.** -/
public def chartLiftClassEquiv [Mono j] :
    squareZeroLiftClasses A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx M ≃
      chartDer Λ (chartPoint hx) M.obj :=
  (overLiftClassEquiv _ hx _).trans (chartLiftEquiv hx M)

/-- The derivation attached to the class of a lift `t` is the second component of the ring map
`P → A[M]` of `t`. -/
public theorem chartLiftClassEquiv_mk [Mono j]
    (t : (Under.post (Over.forget (affineChart (hS := hS) Λ P hP j))).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))) :
    ((chartLiftClassEquiv hx M (Quotient.mk _ t) : chartDer Λ (chartPoint hx) M.obj) :
        P →+ M.obj) =
      { toFun := fun a => (chartLiftRing M (overLiftHom _ hx _ t) a).snd
        map_zero' := by simp
        map_add' := fun a b => by simp } := rfl

end AffineChart

/-! ### Naturality of the identification -/

section Naturality

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ P : Type u} [CommRing Λ] [CommRing P] [Algebra Λ P] {hP : B.Contains (Spec (.of P))}
  {j : Spec (.of Λ) ⟶ S}

/-- Composing an arrow into the chart with a morphism of trivial square-zero extensions composes
the ring maps. -/
public theorem chartLiftRing_comp {A C : Type u} [CommRing A] [CommRing C]
    {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S} {M : SiteModule A B}
    {N : SiteModule C B} (D : squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M)
    (ρ : TrivSqZeroExt A M.obj →+* TrivSqZeroExt C N.obj)
    (hD : (BigFppfOver.toScheme B S hS).map D = Spec.map (CommRingCat.ofHom ρ))
    (g : squareZeroOver A B S hS toS M ⟶ affineChart Λ P hP j) :
    chartLiftRing N (D ≫ g) = ρ.comp (chartLiftRing M g) := by
  refine eq_comp_of_specMap_eq_comp _ _ _ ?_
  rw [specMap_chartLiftRing, specMap_chartLiftRing, ← hD, Functor.map_comp]
  rfl

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {x : Over (affineChart (hS := hS) Λ P hP j)}
  (hx : (Over.forget _).obj x = algebraOver A B S hS toS hA) [Mono j]

/-- **The identification is natural in the coefficient module.** The pullback of a lift class
along a module map `f : M ⟶ M'` corresponds to the composite `f ∘ D` of its derivation. -/
public theorem chartLiftClassEquiv_pullback {M M' : SiteModule A B} (f : M ⟶ M')
    {a : squareZeroLiftClasses A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx M}
    {b : squareZeroLiftClasses A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx M'}
    (h : IsPullbackOfSquareZeroLift A B S hS toS hA (Over.forget _) x hx f a b) (c : P) :
    ((chartLiftClassEquiv hx M' b : chartDer Λ (chartPoint hx) M'.obj) : P →+ M'.obj) c =
      f.hom.hom (((chartLiftClassEquiv hx M a : chartDer Λ (chartPoint hx) M.obj) :
        P →+ M.obj) c) := by
  obtain ⟨a', b', rfl, rfl, φ, hφ, -⟩ := h
  have hlift := overLiftHom_eq_comp_of_isHomLift _ hx _ hx (squareZeroOverMap A B S hS toS f) a'
    b' φ hφ.toIsHomLift
  change (chartLiftRing M' (overLiftHom _ hx _ b') c).snd =
    f.hom.hom (chartLiftRing M (overLiftHom _ hx _ a') c).snd
  rw [hlift, chartLiftRing_comp (squareZeroOverMap A B S hS toS f)
    (TrivSqZeroExt.map f.hom.hom).toRingHom rfl]
  exact TrivSqZeroExt.snd_map f.hom.hom _

variable (F : TangentFunctorData A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx)

/-- The identification of the tangent module of a point of the chart with its derivations. -/
public def chartTangentEquiv (M : SiteModule A B) :
    ↥(F.functor.obj M) ≃ chartDer Λ (chartPoint hx) M.obj :=
  (F.liftEquiv M).trans (chartLiftClassEquiv hx M)

/-- **`chartTangentEquiv` is natural in the coefficient module**: for `f : M ⟶ M'` the
derivation of `F.functor.map f z` is `f` composed with the derivation of `z`. -/
public theorem chartTangentEquiv_map {M M' : SiteModule A B} (f : M ⟶ M')
    (z : ↥(F.functor.obj M)) (c : P) :
    ((chartTangentEquiv hx F M' (F.functor.map f z) : chartDer Λ (chartPoint hx) M'.obj) :
        P →+ M'.obj) c =
      f.hom.hom (((chartTangentEquiv hx F M z : chartDer Λ (chartPoint hx) M.obj) :
        P →+ M.obj) c) :=
  chartLiftClassEquiv_pullback hx f (F.liftEquiv_natural f z) c

/-- **The identification of tangent vectors with derivations is linear.** -/
public def chartTangentLinearEquiv (M : SiteModule A B) :
    ↥(F.functor.obj M) ≃ₗ[A] chartDer Λ (chartPoint hx) M.obj where
  toEquiv := chartTangentEquiv hx F M
  map_add' z₁ z₂ := by
    have := F.additive
    have := F.linear
    set i₁ := siteModuleInl A B hA M M
    set i₂ := siteModuleInr A B hA M M
    set q₁ := siteModuleFst A B hA M M
    set q₂ := siteModuleSnd A B hA M M
    set z := F.functor.map i₁ z₁ + F.functor.map i₂ z₂ with hz
    have hproj (j' : M ⟶ siteModuleProd A B hA M M) (k : siteModuleProd A B hA M M ⟶ M)
        (hjk : j' ≫ k = 𝟙 M) (y : ↥(F.functor.obj M)) :
        F.functor.map k (F.functor.map j' y) = y := by
      simpa using congrArg (fun e => e y) (congrArg F.functor.map hjk)
    have hzero (j' : M ⟶ siteModuleProd A B hA M M) (k : siteModuleProd A B hA M M ⟶ M)
        (hjk : j' ≫ k = 0) (y : ↥(F.functor.obj M)) :
        F.functor.map k (F.functor.map j' y) = 0 := by
      simpa using congrArg (fun e => e y) (congrArg F.functor.map hjk)
    have hz₁ : F.functor.map q₁ z = z₁ := by
      rw [hz, map_add, hproj i₁ q₁ (siteModuleInl_comp_fst A B hA M M) z₁,
        hzero i₂ q₁ (siteModuleInr_comp_fst A B hA M M) z₂, add_zero]
    have hz₂ : F.functor.map q₂ z = z₂ := by
      rw [hz, map_add, hzero i₁ q₂ (siteModuleInl_comp_snd A B hA M M) z₁,
        hproj i₂ q₂ (siteModuleInr_comp_snd A B hA M M) z₂, zero_add]
    have hsum : F.functor.map (q₁ + q₂) z = z₁ + z₂ := by
      rw [F.functor.map_add]
      change F.functor.map q₁ z + F.functor.map q₂ z = z₁ + z₂
      rw [hz₁, hz₂]
    ext c
    change ((chartTangentEquiv hx F M (z₁ + z₂) : chartDer Λ (chartPoint hx) M.obj) :
        P →+ M.obj) c =
      ((chartTangentEquiv hx F M z₁ : chartDer Λ (chartPoint hx) M.obj) : P →+ M.obj) c +
        ((chartTangentEquiv hx F M z₂ : chartDer Λ (chartPoint hx) M.obj) : P →+ M.obj) c
    rw [← hsum, ← hz₁, ← hz₂, chartTangentEquiv_map, chartTangentEquiv_map,
      chartTangentEquiv_map]
    rfl
  map_smul' a z := by
    have := F.additive
    have := F.linear
    have hF : F.functor.map (a • (𝟙 M)) z = a • z := by
      rw [Functor.map_smul, F.functor.map_id]
      rfl
    ext c
    change ((chartTangentEquiv hx F M (a • z) : chartDer Λ (chartPoint hx) M.obj) :
        P →+ M.obj) c =
      a • ((chartTangentEquiv hx F M z : chartDer Λ (chartPoint hx) M.obj) : P →+ M.obj) c
    rw [← hF, chartTangentEquiv_map]
    rfl

/-- The linear equivalence `chartTangentLinearEquiv hx F M` is `chartTangentEquiv hx F M`. -/
@[simp]
public theorem chartTangentLinearEquiv_apply (M : SiteModule A B) (z : ↥(F.functor.obj M)) :
    chartTangentLinearEquiv hx F M z = chartTangentEquiv hx F M z := rfl

end Naturality

/-! ### The map of Stacks 07YA at a chart, and flat base change -/

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ P : Type u} [CommRing Λ] [CommRing P] [Algebra Λ P] {hP : B.Contains (Spec (.of P))}
  {j : Spec (.of Λ) ⟶ S} [Mono j]
  {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)
  {x y : Over (affineChart (hS := hS) Λ P hP j)}
  (hx : (Over.forget _).obj x = algebraOver A B S hS toS hA)
  (hy : (Over.forget _).obj y = algebraOver C B S hS toSC hC)
  (φ : y ⟶ x)
  (hφ : (Over.forget _).IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ)

omit [Mono j] in
include hφ in
/-- The ring map of the restriction of a point along `A ⟶ C` is the composite with `A ⟶ C`. -/
public theorem chartPoint_of_isHomLift : chartPoint hy = f.comp (chartPoint hx) := by
  have hfac := IsHomLift.fac' (Over.forget _) (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ
  have hw := Over.w φ
  change φ.left = _ at hfac
  rw [hfac] at hw
  refine eq_comp_of_specMap_eq_comp _ _ _ ?_
  rw [specMap_chartPoint, specMap_chartPoint, ← hw]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.map_comp]
  rfl

/-- **The map of Stacks 07YA at a chart is composition of derivations.** The pullback of a lift
class along `Spec C[N] ⟶ Spec A[M]` corresponds to the composite `ψ ∘ D` of its derivation. -/
public theorem chartLiftClassEquiv_liftClassPullback {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : squareZeroLiftClasses A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx M)
    (c : P) :
    ((chartLiftClassEquiv hy N
        (liftClassPullback f hf (Functor.IsFiberedInGroupoids.over_forget _) φ hφ ψ a) :
        chartDer Λ (chartPoint hy) N.obj) : P →+ N.obj) c =
      ψ (((chartLiftClassEquiv hx M a : chartDer Λ (chartPoint hx) M.obj) : P →+ M.obj) c) := by
  obtain ⟨u', v', rfl, hv, ρ, hρ, -⟩ := exists_cartesian_underFiberClassPullback
    (Over.forget _) (Functor.IsFiberedInGroupoids.over_forget _) (tangentPullbackBase f hf ψ)
    (tangentPullbackBase_square f hf ψ) φ hφ (hy := hy) a
  change ((chartLiftClassEquiv hy N (underFiberClassPullback (Over.forget _)
    (Functor.IsFiberedInGroupoids.over_forget _) (tangentPullbackBase f hf ψ)
    (tangentPullbackBase_square f hf ψ) φ hφ (Quotient.mk _ u')) :
      chartDer Λ (chartPoint hy) N.obj) : P →+ N.obj) c = _
  rw [← hv]
  change (chartLiftRing N (overLiftHom _ hy _ v') c).snd =
    ψ (chartLiftRing M (overLiftHom _ hx _ u') c).snd
  rw [overLiftHom_eq_comp_of_isHomLift _ hx _ hy (tangentPullbackBase f hf ψ) u' v' ρ
    hρ.toIsHomLift, chartLiftRing_comp (tangentPullbackBase f hf ψ)
    (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ)) rfl]
  rfl

end BaseChange

/-! ### Flat base change at a chart -/

section FlatBaseChange

open scoped TensorProduct

/-- The map `M → N`, `m ↦ 1 ⊗ m`, of coefficients attached to an identification of `N` with
`C ⊗_A M`, as a morphism of `A`-modules into the restriction of scalars of `N`. -/
public def baseChangeCoeff {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C} (hMN : (C ⊗[A] M) ≃ₗ[C] N) :
    M ⟶ (ModuleCat.restrictScalars (algebraMap A C)).obj N :=
  ModuleCat.ofHom (X := M) (Y := ↑((ModuleCat.restrictScalars (algebraMap A C)).obj N))
    { toFun := fun m => (hMN (1 ⊗ₜ m) : N)
      map_add' := fun m m' => by
        change hMN (1 ⊗ₜ (m + m')) = hMN (1 ⊗ₜ m) + hMN (1 ⊗ₜ m')
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a m => by
        change hMN (1 ⊗ₜ (a • m)) = algebraMap A C a • hMN (1 ⊗ₜ m)
        rw [← map_smul, TensorProduct.tmul_smul, algebraMap_smul] }

/-- `baseChangeCoeff hMN` sends `m` to `hMN (1 ⊗ₜ m)`. -/
@[simp]
public theorem baseChangeCoeff_apply {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C} (hMN : (C ⊗[A] M) ≃ₗ[C] N) (m : M) :
    (baseChangeCoeff hMN).hom m = (hMN (1 ⊗ₜ m) : N) := rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ P : Type u} [CommRing Λ] [CommRing P] [Algebra Λ P] {hP : B.Contains (Spec (.of P))}
  {j : Spec (.of Λ) ⟶ S} [Mono j]
  {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  (hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC)
  {x y : Over (affineChart (hS := hS) Λ P hP j)}
  (hx : (Over.forget _).obj x = algebraOver A B S hS toS hA)
  (hy : (Over.forget _).obj y = algebraOver C B S hS toSC hC)
  (φ : y ⟶ x)
  (hφ : (Over.forget _).IsHomLift
    (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ)
  (F : TangentFunctorData A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx)
  (G : TangentFunctorData C B S hS toSC hC (Over.forget (affineChart Λ P hP j)) y hy)

/-- **Stacks 0DNT at an affine chart.** Let `Spec P` be of finite presentation over an affine
`Spec Λ → S` embedded by a monomorphism, regarded as a category fibred in groupoids over the big
fppf site of `S`. Let `A → C` be a flat homomorphism of `S`-algebras, `x` a point of `Spec P`
over `Spec A` and `y = x|_{Spec C}`. For an `A`-module `M` and `N` identified with `C ⊗_A M`
there is a `C`-linear isomorphism `C ⊗_A T_x(M) ≅ T_y(N)` sending `1 ⊗ t` to the image of `t`
under the map of Stacks 07YA. -/
public theorem exists_chartTangent_flatBaseChange [Module.Flat A C]
    [Algebra.FinitePresentation Λ P] (M : SiteModule A B) (N : SiteModule C B)
    (hMN : (C ⊗[A] M.obj) ≃ₗ[C] N.obj) :
    ∃ e : (C ⊗[A] ↥(F.functor.obj M)) ≃ₗ[C] ↥(G.functor.obj N),
      ∀ t, e (1 ⊗ₜ t) = tangentPullbackHom (algebraMap A C) hf
        (Functor.IsFiberedInGroupoids.over_forget _) φ hφ F G (baseChangeCoeff hMN) t := by
  have hyx := chartPoint_of_isHomLift (algebraMap A C) hf hx hy φ hφ
  let : Algebra P A := (chartPoint hx).toAlgebra
  let : Module P M.obj := Module.compHom M.obj (chartPoint hx)
  have : IsScalarTower P A M.obj := ⟨fun p a m => by
    change ((chartPoint hx) p * a) • m = (chartPoint hx) p • a • m
    rw [mul_smul]⟩
  let : Module Λ M.obj := Module.compHom M.obj ((chartPoint hx).comp (algebraMap Λ P))
  have : IsScalarTower Λ P M.obj := ⟨fun c p m => by
    change (chartPoint hx) (c • p) • m = (chartPoint hx) (algebraMap Λ P c) • (chartPoint hx) p • m
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let : Algebra P C := (chartPoint hy).toAlgebra
  have : IsScalarTower P A C := IsScalarTower.of_algebraMap_eq (fun p => by
    change (chartPoint hy) p = algebraMap A C ((chartPoint hx) p)
    rw [hyx]
    rfl)
  let : Module P N.obj := Module.compHom N.obj (chartPoint hy)
  have : IsScalarTower P C N.obj := ⟨fun p c n => by
    change ((chartPoint hy) p * c) • n = (chartPoint hy) p • c • n
    rw [mul_smul]⟩
  let : Module Λ N.obj := Module.compHom N.obj ((chartPoint hy).comp (algebraMap Λ P))
  have : IsScalarTower Λ P N.obj := ⟨fun c p n => by
    change (chartPoint hy) (c • p) • n = (chartPoint hy) (algebraMap Λ P c) • (chartPoint hy) p • n
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  obtain ⟨e₂, he₂⟩ := exists_chartDer_flatBaseChange Λ P A C M.obj N.obj hMN
  let e₁ : (C ⊗[A] ↥(F.functor.obj M)) ≃ₗ[C] (C ⊗[A] chartDer Λ (chartPoint hx) M.obj) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
      (chartTangentLinearEquiv hx F M)
  refine ⟨e₁.trans (e₂.trans (chartTangentLinearEquiv hy G N).symm), fun t => ?_⟩
  apply (chartTangentLinearEquiv hy G N).injective
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext c
  have h₁ : e₁ (1 ⊗ₜ t) = 1 ⊗ₜ chartTangentLinearEquiv hx F M t :=
    TensorProduct.AlgebraTensorModule.congr_tmul _ _ 1 t
  rw [h₁, he₂]
  change _ = ((chartLiftClassEquiv hy N (G.liftEquiv N
    (tangentPullbackFun (algebraMap A C) hf (Functor.IsFiberedInGroupoids.over_forget _) φ hφ
      F G (baseChangeCoeff hMN) t)) : chartDer Λ (chartPoint hy) N.obj) : P →+ N.obj) c
  rw [liftEquiv_tangentPullbackFun, chartLiftClassEquiv_liftClassPullback]
  rfl

end FlatBaseChange

/-! ### The tangent functor of a point of an affine chart -/

section ChartTangentFunctor

/-- Composition of the derivations of a chart with a linear map of coefficient modules. -/
public def chartDerMap {Λ P A : Type*} [CommRing Λ] [CommRing P] [CommRing A] [Algebra Λ P]
    {u : P →+* A} {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) : chartDer Λ u M →ₗ[A] chartDer Λ u N where
  toFun D := ⟨(f.toAddMonoidHom).comp (D : P →+ M), fun a b => by
      simp [chartDer_leibniz D a b], fun c => by simp [chartDer_algebraMap D c]⟩
  map_add' D E := by
    ext a
    simp
  map_smul' r D := by
    ext a
    simp

/-- `chartDerMap f D` is the composite `f ∘ D`. -/
@[simp]
public theorem chartDerMap_apply {Λ P A : Type*} [CommRing Λ] [CommRing P] [CommRing A]
    [Algebra Λ P] {u : P →+* A} {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : M →ₗ[A] N) (D : chartDer Λ u M) (a : P) :
    ((chartDerMap f D : chartDer Λ u N) : P →+ N) a = f ((D : P →+ M) a) := rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ P : Type u} [CommRing Λ] [CommRing P] [Algebra Λ P] {hP : B.Contains (Spec (.of P))}
  {j : Spec (.of Λ) ⟶ S} [Mono j]
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : Over (affineChart (hS := hS) Λ P hP j)}
  (hx : (Over.forget _).obj x = algebraOver A B S hS toS hA)

/-- The derivations of the chart along the point `x`, as an `A`-linear functor of the coefficient
module. -/
public def chartDerFunctor : SiteModule A B ⥤ ModuleCat.{u + 1} A where
  obj M := ModuleCat.of A (ULift.{u + 1} (chartDer Λ (chartPoint hx) M.obj))
  map f := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    chartDerMap (Λ := Λ) (u := chartPoint hx) f.hom.hom ∘ₗ ULift.moduleEquiv.toLinearMap)
  map_id M := by
    ext ⟨D⟩
    rfl
  map_comp f g := by
    ext ⟨D⟩
    rfl

/-- The derivation functor `chartDerFunctor hx` is additive. -/
public instance chartDerFunctor_additive : (chartDerFunctor hx).Additive where
  map_add {M N f g} := by
    ext ⟨D⟩
    rfl

/-- The derivation functor `chartDerFunctor hx` is `A`-linear. -/
public instance chartDerFunctor_linear : (chartDerFunctor hx).Linear A where
  map_smul {M N} f r := by
    ext ⟨D⟩
    rfl

/-- **The tangent functor of a point of an affine chart**: the derivations of the chart along the
point, identified with the lift classes by `Deformation.Artin.chartLiftClassEquiv`. -/
public def chartTangentFunctorData :
    TangentFunctorData A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx where
  functor := chartDerFunctor hx
  liftEquiv M := Equiv.ulift.trans (chartLiftClassEquiv hx M).symm
  naturality {M N} f z := by
    obtain ⟨b, hb, hb'⟩ := exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift A B S hS
      toS hA (Over.forget _) x hx (Functor.IsFiberedInGroupoids.over_forget _) f
      ((Equiv.ulift.trans (chartLiftClassEquiv hx M).symm) z)
    have hbz : b = (Equiv.ulift.trans (chartLiftClassEquiv hx N).symm)
        ((chartDerFunctor hx).map f z) := by
      apply (chartLiftClassEquiv hx N).injective
      ext c
      rw [chartLiftClassEquiv_pullback hx f hb' c]
      refine (congrArg (fun D : chartDer Λ (chartPoint hx) M.obj => f.hom.hom ((D : P →+ M.obj) c))
        ((chartLiftClassEquiv hx M).apply_symm_apply z.down)).trans (Eq.trans ?_
          (congrArg (fun D : chartDer Λ (chartPoint hx) N.obj => (D : P →+ N.obj) c)
            ((chartLiftClassEquiv hx N).apply_symm_apply _).symm))
      rfl
    exact hbz ▸ hb
  liftEquiv_natural {M N} f z := by
    obtain ⟨b, -, hb'⟩ := exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift A B S hS
      toS hA (Over.forget _) x hx (Functor.IsFiberedInGroupoids.over_forget _) f
      ((Equiv.ulift.trans (chartLiftClassEquiv hx M).symm) z)
    have hbz : b = (Equiv.ulift.trans (chartLiftClassEquiv hx N).symm)
        ((chartDerFunctor hx).map f z) := by
      apply (chartLiftClassEquiv hx N).injective
      ext c
      rw [chartLiftClassEquiv_pullback hx f hb' c]
      refine (congrArg (fun D : chartDer Λ (chartPoint hx) M.obj => f.hom.hom ((D : P →+ M.obj) c))
        ((chartLiftClassEquiv hx M).apply_symm_apply z.down)).trans (Eq.trans ?_
          (congrArg (fun D : chartDer Λ (chartPoint hx) N.obj => (D : P →+ N.obj) c)
            ((chartLiftClassEquiv hx N).apply_symm_apply _).symm))
      rfl
    exact hbz ▸ hb'

/-- A point of an affine chart has a tangent functor. -/
public theorem nonempty_chartTangentFunctorData :
    Nonempty (TangentFunctorData A B S hS toS hA (Over.forget (affineChart Λ P hP j)) x hx) :=
  ⟨chartTangentFunctorData hx⟩

end ChartTangentFunctor

end Deformation.Artin

end
