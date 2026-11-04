module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoverGeometricLifts
public import StacksFrontier.Algebra.Module.Projective.Determinant.InducedCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients

/-!
# The local factor of a finite direct image

Let `f : X ⟶ Y` be a finite morphism of a big étale site, `G` a sheaf of `Λ`-modules on `X_étale`
and `y` a point of `Y` with finite residue field. The stalk of `f_* G` at the geometric point
`ȳ` is the product of the stalks of `G` at the lifts of `ȳ`; the geometric Frobenius of `ȳ`
permutes the lifts, the lifts over a point `x` above `y` forming one orbit of length
`[κ(x) : κ(y)]`, and going once around that orbit is the geometric Frobenius of `x`. Hence

`det(1 - π_y T ^ d | (f_* G)_ȳ) = ∏_{x ↦ y} det(1 - π_x T ^ (d [κ(x) : κ(y)]) | G_x̄)`.

This file proves this identity for the canonical maps of stalks of Tag 04FN along the geometric
Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (Λ : Type) [CommRing Λ]
  (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ)) (y : Y.1)

/-- The stalk map along a morphism of geometric points with identity underlying morphism is the
identity. -/
public theorem geometricPointStalkMap_app_eq_id {S : Scheme.{u}} (hS : B.Contains S)
    {s : GeometricPoint S} (a : GeometricPoint.Hom s s) (ha : a.hom = 𝟙 _)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    (geometricPointStalkMap B S hS a (ModuleCat.{u + 1} Λ)).app P = 𝟙 _ := by
  refine colimit.hom_ext fun U => ?_
  have hU : (neighborhoodFunctor B S hS a).op.obj U = U := by
    refine congrArg op (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    show a.hom ≫ U.unop.2.1 = U.unop.2.1
    rw [ha, Category.id_comp]
  refine (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P)
    (neighborhoodFunctor B S hS a).op U).trans (Eq.trans ?_ (Category.comp_id _).symm)
  let D := (CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P
  refine Eq.trans ?_ (colimit.w D (eqToHom hU.symm))
  simp only [D, eqToHom_map]
  exact (Category.id_comp _).symm

/-- The Galois point morphism of `σ ^ k` at `ȳ`. -/
public abbrev galoisPow
    (σ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (k : ℕ) :
    GeometricPoint.Hom (geometricPointAt Y.1 y) (geometricPointAt Y.1 y) :=
  galoisPointHom (AlgebraicClosure (Y.1.residueField y)) (σ ^ k) (Y.1.fromSpecResidueField y)

/-- The stalk map along `σ ^ k` is the `k`-th power of the stalk map along `σ`. -/
public theorem geometricPointStalkMap_galoisPow
    (σ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y))
    (P : (SmallEtale B Y.1 Y.property)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (k : ℕ) :
    ((geometricPointStalkMap B Y.1 Y.property (galoisPow B y σ k) (ModuleCat.{u + 1} Λ)).app
        P).hom =
      ((geometricPointStalkMap B Y.1 Y.property (galoisPow B y σ 1) (ModuleCat.{u + 1} Λ)).app
        P).hom ^ k := by
  induction k with
  | zero =>
    rw [geometricPointStalkMap_app_eq_id B Λ Y.property _ (by
      show Spec.map (CommRingCat.ofHom (σ ^ 0).toAlgHom.toRingHom) = 𝟙 _
      rw [pow_zero]
      exact Spec.map_id _), pow_zero]
    rfl
  | succ k ih =>
    have h : galoisPow B y σ (k + 1) = (galoisPow B y σ 1).comp (galoisPow B y σ k) := by
      rw [galoisPointHom_comp, pow_one, ← pow_succ']
    rw [h, geometricPointStalkMap_comp, NatTrans.comp_app, ModuleCat.hom_comp, ih, pow_succ']
    rfl

/-- The stalk map along a morphism of geometric points whose underlying morphism is invertible is
bijective. -/
public theorem geometricPointStalkMap_app_bijective {S : Scheme.{u}} (hS : B.Contains S)
    {s t : GeometricPoint S} (a : GeometricPoint.Hom s t) (g : t.source ⟶ s.source)
    (hag : a.hom ≫ g = 𝟙 _) (hga : g ≫ a.hom = 𝟙 _)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    Function.Bijective ((geometricPointStalkMap B S hS a (ModuleCat.{u + 1} Λ)).app P).hom := by
  let b : GeometricPoint.Hom t s :=
    ⟨g, by rw [← a.comm, ← Category.assoc, hga, Category.id_comp]⟩
  have e1 := geometricPointStalkMap_app_eq_id B Λ hS (a.comp b) hag P
  have e2 := geometricPointStalkMap_app_eq_id B Λ hS (b.comp a) hga P
  rw [geometricPointStalkMap_comp, NatTrans.comp_app] at e1 e2
  have k1 : ∀ z, ((geometricPointStalkMap B S hS a (ModuleCat.{u + 1} Λ)).app P).hom
      (((geometricPointStalkMap B S hS b (ModuleCat.{u + 1} Λ)).app P).hom z) = z := fun z => by
    simpa using congrArg (fun φ => φ.hom z) e1
  have k2 : ∀ z, ((geometricPointStalkMap B S hS b (ModuleCat.{u + 1} Λ)).app P).hom
      (((geometricPointStalkMap B S hS a (ModuleCat.{u + 1} Λ)).app P).hom z) = z := fun z => by
    simpa using congrArg (fun φ => φ.hom z) e2
  exact ⟨Function.LeftInverse.injective k2, Function.RightInverse.surjective k1⟩

/-- The morphism of geometric points attached to the identity automorphism has identity underlying
morphism. -/
public theorem galoisPointHom_one_hom {k : Type u} [Field k] {S : Scheme.{u}} (K : Type u) [Field K]
    [IsAlgClosed K] [Algebra k K] (s : Spec (.of k) ⟶ S) :
    (galoisPointHom K (1 : K ≃ₐ[k] K) s).hom = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (1 : K ≃ₐ[k] K).toAlgHom.toRingHom) = 𝟙 _
  rw [show CommRingCat.ofHom (1 : K ≃ₐ[k] K).toAlgHom.toRingHom = 𝟙 _ from rfl, Spec.map_id]

/-- The underlying morphisms of the morphisms of geometric points attached to `τ` and `τ⁻¹` are
inverse. -/
public theorem galoisPointHom_hom_comp_inv {k : Type u} [Field k] {S : Scheme.{u}} (K : Type u)
    [Field K] [IsAlgClosed K] [Algebra k K] (s : Spec (.of k) ⟶ S) (τ : K ≃ₐ[k] K) :
    (galoisPointHom K τ s).hom ≫ (galoisPointHom K τ⁻¹ s).hom = 𝟙 _ := by
  have h := congrArg GeometricPoint.Hom.hom (galoisPointHom_comp K s τ τ⁻¹)
  rw [mul_inv_cancel] at h
  exact h.trans (galoisPointHom_one_hom K s)

/-- The underlying morphisms of the morphisms of geometric points attached to `τ⁻¹` and `τ` are
inverse. -/
public theorem galoisPointHom_hom_inv_comp {k : Type u} [Field k] {S : Scheme.{u}} (K : Type u)
    [Field K] [IsAlgClosed K] [Algebra k K] (s : Spec (.of k) ⟶ S) (τ : K ≃ₐ[k] K) :
    (galoisPointHom K τ⁻¹ s).hom ≫ (galoisPointHom K τ s).hom = 𝟙 _ := by
  have h := congrArg GeometricPoint.Hom.hom (galoisPointHom_comp K s τ⁻¹ τ)
  rw [inv_mul_cancel] at h
  exact h.trans (galoisPointHom_one_hom K s)

/-- The morphism of schemes underlying `f`. -/
public abbrev fS : X.1 ⟶ Y.1 := B.inclusion.map f

section Stalk

variable [IsFinite (fS B f)]

/-- The stalk of `f_* G` at the geometric point `ȳ` at `y`. -/
public abbrev pushforwardStalkAt : ModuleCat.{u + 1} Λ :=
  etaleStalk (A := ModuleCat.{u + 1} Λ) B Y.1 Y.property (geometricPointAt Y.1 y)
    (moduleDirectImage B f Λ G).obj

/-- The stalk of `G` at a lift of `ȳ`. -/
public abbrev liftStalk (ℓ : PointLifts (fS B f) y) : ModuleCat.{u + 1} Λ :=
  etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property
    (geometricPointLift (fS B f) (geometricPointAt Y.1 y) ℓ) G.obj

/-- **The stalk of `f_* G` at `ȳ` is the product of the stalks of `G` at the lifts of `ȳ`**, as
`Λ`-modules. -/
public def pushforwardStalkEquiv :
    pushforwardStalkAt B f Λ G y ≃ₗ[Λ] (∀ ℓ : PointLifts (fS B f) y, liftStalk B f Λ G y ℓ) :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun ℓ => (finitePushforwardModuleStalkComponent B f (geometricPointAt Y.1 y) Λ G
      ℓ).hom)
    (finitePushforwardModuleStalkComponent_bijective B f (geometricPointAt Y.1 y) Λ G)

/-- The component of `pushforwardStalkEquiv` at a lift `ℓ` is the stalk component map at `ℓ`. -/
public theorem pushforwardStalkEquiv_apply (z : pushforwardStalkAt B f Λ G y)
    (ℓ : PointLifts (fS B f) y) :
    pushforwardStalkEquiv B f Λ G y z ℓ =
      (finitePushforwardModuleStalkComponent B f (geometricPointAt Y.1 y) Λ G ℓ).hom z :=
  rfl

variable (σ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
  AlgebraicClosure (Y.1.residueField y))

/-- The stalk map of `f_* G` along `σ`. -/
public abbrev pushforwardStalkGalois :
    pushforwardStalkAt B f Λ G y →ₗ[Λ] pushforwardStalkAt B f Λ G y :=
  ((geometricPointStalkMap B Y.1 Y.property (galoisPow B y σ 1) (ModuleCat.{u + 1} Λ)).app
    (moduleDirectImage B f Λ G).obj).hom

/-- The components of the powers of the stalk map along `σ`. -/
public theorem pushforwardStalkEquiv_galois_pow (k : ℕ) (ℓ' ℓ'' : PointLifts (fS B f) y)
    (h : (galoisPow B y σ k).hom ≫ ℓ''.1 = ℓ'.1) (z : pushforwardStalkAt B f Λ G y) :
    pushforwardStalkEquiv B f Λ G y ((pushforwardStalkGalois B f Λ G y σ ^ k) z) ℓ' =
      ((geometricPointStalkMap B X.1 X.property
        (GeometricLifts.homOfComm B f (galoisPow B y σ k) ℓ' ℓ'' h) (ModuleCat.{u + 1} Λ)).app
          G.obj).hom (pushforwardStalkEquiv B f Λ G y z ℓ'') := by
  have h1 : (pushforwardStalkGalois B f Λ G y σ ^ k) z =
      ((geometricPointStalkMap B Y.1 Y.property (galoisPow B y σ k) (ModuleCat.{u + 1} Λ)).app
        (moduleDirectImage B f Λ G).obj).hom z := by
    rw [geometricPointStalkMap_galoisPow B Λ y σ (moduleDirectImage B f Λ G).obj k]
    rfl
  rw [h1]
  exact ConcreteCategory.congr_hom
    (geometricPointStalkMap_comp_finitePushforwardModuleStalkComponent B f Λ G
      (galoisPow B y σ k) ℓ' ℓ'' h) z

/-- The action of an automorphism of `κ(y)‾` on the lifts of `ȳ`. -/
public def liftAct
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    PointLifts (fS B f) y :=
  ⟨(galoisPointHom (AlgebraicClosure (Y.1.residueField y)) τ (Y.1.fromSpecResidueField y)).hom ≫
    ℓ.1, by
    rw [Category.assoc, ℓ.2]
    exact (galoisPointHom (AlgebraicClosure (Y.1.residueField y)) τ
      (Y.1.fromSpecResidueField y)).comm⟩

omit [IsFinite (fS B f)] in
/-- Acting on the lifts by `τ'` and then by `τ` is acting by `τ * τ'`. -/
public theorem liftAct_mul
    (τ τ' : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    liftAct B f y τ (liftAct B f y τ' ℓ) = liftAct B f y (τ * τ') ℓ := by
  apply Subtype.ext
  show _ ≫ _ ≫ _ = _
  rw [← Category.assoc]
  show ((galoisPointHom _ τ _).comp (galoisPointHom _ τ' _)).hom ≫ ℓ.1 = _
  rw [galoisPointHom_comp]
  rfl

omit [IsFinite (fS B f)] in
/-- The identity automorphism acts trivially on the lifts. -/
public theorem liftAct_one (ℓ : PointLifts (fS B f) y) :
    liftAct B f y 1 ℓ = ℓ := by
  apply Subtype.ext
  exact (congrArg (· ≫ ℓ.1) (galoisPointHom_one_hom _ _)).trans (Category.id_comp _)

omit [IsFinite (fS B f)] in
/-- The action on lifts through embeddings. -/
public theorem liftAct_liftOfEmbedding
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (x : {x : X.1 // (fS B f) x = y})
    (ι : FiberEmbeddings (fS B f) y x) :
    liftAct B f y τ (liftOfEmbedding (fS B f) y x ι) =
      liftOfEmbedding (fS B f) y x (FiberEmbeddings.comp (fS B f) y x τ ι) :=
  Subtype.ext (galoisPointHom_comp_liftOfEmbedding (fS B f) y x τ ι)

/-- The stalk map `G_ℓ → G_{τ ℓ}` along the automorphism `τ` of `ȳ`. -/
public abbrev liftStalkMap
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    liftStalk B f Λ G y ℓ →ₗ[Λ] liftStalk B f Λ G y (liftAct B f y τ ℓ) :=
  ((geometricPointStalkMap B X.1 X.property
    (GeometricLifts.homOfComm B f
      (galoisPointHom (AlgebraicClosure (Y.1.residueField y)) τ (Y.1.fromSpecResidueField y))
      (liftAct B f y τ ℓ) ℓ rfl) (ModuleCat.{u + 1} Λ)).app G.obj).hom

omit [IsFinite (fS B f)] in
/-- The stalk map along an automorphism of `ȳ` is bijective. -/
public theorem liftStalkMap_bijective
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    Function.Bijective (liftStalkMap B f Λ G y τ ℓ) :=
  geometricPointStalkMap_app_bijective B Λ X.property _
    (galoisPointHom (AlgebraicClosure (Y.1.residueField y))
      (τ⁻¹ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
        AlgebraicClosure (Y.1.residueField y)) (Y.1.fromSpecResidueField y)).hom
    (galoisPointHom_hom_comp_inv _ _ τ) (galoisPointHom_hom_inv_comp _ _ τ) G.obj

/-- The stalk map along an automorphism of `ȳ`, as a linear equivalence. -/
public def liftStalkMapEquiv
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    liftStalk B f Λ G y ℓ ≃ₗ[Λ] liftStalk B f Λ G y (liftAct B f y τ ℓ) :=
  LinearEquiv.ofBijective _ (liftStalkMap_bijective B f Λ G y τ ℓ)

omit [IsFinite (fS B f)] in
/-- Acting on a lift by `τ⁻¹` and then by `τ` gives back the lift. -/
public theorem liftAct_inv_liftAct
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (ℓ : PointLifts (fS B f) y) :
    liftAct B f y τ (liftAct B f y τ⁻¹ ℓ) = ℓ := by
  rw [liftAct_mul, mul_inv_cancel, liftAct_one]

omit [IsFinite (fS B f)] in
/-- The action of an automorphism `τ` on the lifts is injective. -/
public theorem liftAct_injective
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) :
    Function.Injective (liftAct B f y τ) := by
  intro ℓ ℓ' h
  have := congrArg (liftAct B f y τ⁻¹) h
  rwa [liftAct_mul, liftAct_mul, inv_mul_cancel, liftAct_one, liftAct_one] at this

/-- The inclusion of the stalk at the lift `ℓ` into the stalk of `f_* G`. -/
public def liftInclusion (ℓ : PointLifts (fS B f) y) :
    liftStalk B f Λ G y ℓ →ₗ[Λ] pushforwardStalkAt B f Λ G y :=
  letI := Classical.decEq (PointLifts (fS B f) y)
  (pushforwardStalkEquiv B f Λ G y).symm.toLinearMap ∘ₗ
    LinearMap.single Λ (fun ℓ => liftStalk B f Λ G y ℓ) ℓ

/-- Under `pushforwardStalkEquiv`, the inclusion of `v` at the lift `ℓ` is the family that is `v`
at `ℓ` and zero elsewhere. -/
public theorem pushforwardStalkEquiv_liftInclusion (ℓ : PointLifts (fS B f) y)
    (v : liftStalk B f Λ G y ℓ) :
    pushforwardStalkEquiv B f Λ G y (liftInclusion B f Λ G y ℓ v) =
      letI := Classical.decEq (PointLifts (fS B f) y)
      Pi.single ℓ v := by
  simp [liftInclusion]

/-- The component at `ℓ'` of `Φ ^ i` applied to the inclusion of a vector at `ℓ` vanishes unless
`ℓ' = σ ^ i ℓ`. -/
public theorem pushforwardStalkEquiv_pow_liftInclusion_of_ne (i : ℕ) (ℓ ℓ' : PointLifts (fS B f) y)
    (v : liftStalk B f Λ G y ℓ) (hne : ℓ' ≠ liftAct B f y (σ ^ i) ℓ) :
    pushforwardStalkEquiv B f Λ G y ((pushforwardStalkGalois B f Λ G y σ ^ i)
      (liftInclusion B f Λ G y ℓ v)) ℓ' = 0 := by
  let := Classical.decEq (PointLifts (fS B f) y)
  have h : (galoisPow B y σ i).hom ≫ (liftAct B f y (σ ^ i)⁻¹ ℓ').1 = ℓ'.1 :=
    congrArg Subtype.val (liftAct_inv_liftAct B f y (σ ^ i) ℓ')
  rw [pushforwardStalkEquiv_galois_pow B f Λ G y σ i ℓ' _ h, pushforwardStalkEquiv_liftInclusion]
  have hne' : liftAct B f y (σ ^ i)⁻¹ ℓ' ≠ ℓ := fun h' => hne (by rw [← h', liftAct_inv_liftAct])
  exact (congrArg _ (Pi.single_eq_of_ne (M := fun ℓ => ↥(liftStalk B f Λ G y ℓ)) hne' v)).trans
    (map_zero _)

/-- The component at `σ ^ i ℓ` of `Φ ^ i` applied to the inclusion of a vector at `ℓ` is the stalk
map along `σ ^ i`. -/
public theorem pushforwardStalkEquiv_pow_liftInclusion_self (i : ℕ) (ℓ : PointLifts (fS B f) y)
    (v : liftStalk B f Λ G y ℓ) :
    pushforwardStalkEquiv B f Λ G y ((pushforwardStalkGalois B f Λ G y σ ^ i)
      (liftInclusion B f Λ G y ℓ v)) (liftAct B f y (σ ^ i) ℓ) =
      liftStalkMap B f Λ G y (σ ^ i) ℓ v := by
  let := Classical.decEq (PointLifts (fS B f) y)
  rw [pushforwardStalkEquiv_galois_pow B f Λ G y σ i _ ℓ rfl, pushforwardStalkEquiv_liftInclusion]
  exact congrArg _ (Pi.single_eq_same (M := fun ℓ => ↥(liftStalk B f Λ G y ℓ)) ℓ v)

/-! ### The orbits of the Frobenius on the lifts -/

section Orbits

variable [Finite (Y.1.residueField y)]
  (hres : ∀ x : {x : X.1 // (fS B f) x = y}, Finite (X.1.residueField x.1))

include hres in
omit [IsFinite (fS B f)] in
/-- A point over `y` has an embedding of its residue field into `κ(y)‾`. -/
public theorem nonempty_fiberEmbeddings (x : {x : X.1 // (fS B f) x = y}) :
    Nonempty (FiberEmbeddings (fS B f) y x) := by
  let := fiberResidueAlgebra (fS B f) y x
  have := hres x
  have : Module.Finite (Y.1.residueField y) (X.1.residueField x.1) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (Y.1.residueField y) (X.1.residueField x.1) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact ⟨IsAlgClosed.lift⟩

/-- A chosen lift of `ȳ` over a point `x` above `y`. -/
public def baseLift (x : {x : X.1 // (fS B f) x = y}) :
    PointLifts (fS B f) y :=
  liftOfEmbedding (fS B f) y x (Classical.choice (nonempty_fiberEmbeddings B f y hres x))

/-- The residue degree `[κ(x) : κ(y)]` of a point `x` above `y`. -/
public def fiberDegree (x : {x : X.1 // (fS B f) x = y}) : ℕ :=
  letI := fiberResidueAlgebra (fS B f) y x
  Module.finrank (Y.1.residueField y) (X.1.residueField x.1)

omit [IsFinite (fS B f)] in
/-- The geometric Frobenius of `κ(y)` satisfies the hypothesis of the orbit lemmas. -/
public theorem residueGeometricFrobenius_symm_apply_card
    (z : AlgebraicClosure (Y.1.residueField y)) :
    letI : Fintype (Y.1.residueField y) := Fintype.ofFinite _
    (residueGeometricFrobenius Y.1 y).symm z = z ^ Fintype.card (Y.1.residueField y) := by
  let : Fintype (Y.1.residueField y) := Fintype.ofFinite _
  rw [residueGeometricFrobenius_symm_apply, Nat.card_eq_fintype_card]

omit [IsFinite (fS B f)] in
/-- The Frobenius orbit of the base lift. -/
public theorem liftAct_pow_baseLift (x : {x : X.1 // (fS B f) x = y}) (k : ℕ) :
    liftAct B f y (residueGeometricFrobenius Y.1 y ^ k) (baseLift B f y hres x) =
      liftOfEmbedding (fS B f) y x (FiberEmbeddings.comp (fS B f) y x
        (residueGeometricFrobenius Y.1 y ^ k)
        (Classical.choice (nonempty_fiberEmbeddings B f y hres x))) :=
  liftAct_liftOfEmbedding B f y _ x _

omit [IsFinite (fS B f)] in
/-- **Going once around the orbit**: `σ ^ [κ(x) : κ(y)]` fixes the base lift. -/
public theorem liftAct_pow_fiberDegree_baseLift (x : {x : X.1 // (fS B f) x = y}) :
    liftAct B f y (residueGeometricFrobenius Y.1 y ^ fiberDegree B f y x) (baseLift B f y hres x) =
      baseLift B f y hres x := by
  let := fiberResidueAlgebra (fS B f) y x
  let : Fintype (Y.1.residueField y) := Fintype.ofFinite _
  have := hres x
  rw [liftAct_pow_baseLift]
  congr 1
  exact pow_finrank_comp_eq (residueGeometricFrobenius Y.1 y)
    (residueGeometricFrobenius_symm_apply_card B y) _

omit [IsFinite (fS B f)] in
/-- The lifts in the orbit of the base lift over `x` pass through `x`. -/
public theorem liftAct_baseLift_apply
    (τ : AlgebraicClosure (Y.1.residueField y) ≃ₐ[Y.1.residueField y]
      AlgebraicClosure (Y.1.residueField y)) (x : {x : X.1 // (fS B f) x = y})
    (s : (geometricPointAt Y.1 y).source) :
    (liftAct B f y τ (baseLift B f y hres x)).1 s = x.1 := by
  rw [baseLift, liftAct_liftOfEmbedding]
  exact liftOfEmbedding_apply _ _ _ _ s

omit [IsFinite (fS B f)] [Finite (Y.1.residueField y)] in
include hres in
/-- The residue degree of a point over `y` is positive. -/
public theorem fiberDegree_pos (x : {x : X.1 // (fS B f) x = y}) : 0 < fiberDegree B f y x := by
  let := fiberResidueAlgebra (fS B f) y x
  have := hres x
  have : Module.Finite (Y.1.residueField y) (X.1.residueField x.1) := Module.Finite.of_finite
  exact Module.finrank_pos

omit [IsFinite (fS B f)] in
/-- **The Frobenius orbits of the base lifts are disjoint and of length `[κ(x) : κ(y)]`.** -/
public theorem eq_of_liftAct_pow_baseLift_eq {x x' : {x : X.1 // (fS B f) x = y}} {i j : ℕ}
    (hi : i < fiberDegree B f y x) (hj : j < fiberDegree B f y x')
    (h : liftAct B f y (residueGeometricFrobenius Y.1 y ^ i) (baseLift B f y hres x) =
      liftAct B f y (residueGeometricFrobenius Y.1 y ^ j) (baseLift B f y hres x')) :
    x = x' ∧ i = j := by
  obtain ⟨s⟩ : Nonempty (geometricPointAt Y.1 y).source := inferInstance
  obtain rfl : x = x' := Subtype.ext ((liftAct_baseLift_apply B f y hres _ x s).symm.trans
    ((congrArg (fun ℓ : PointLifts (fS B f) y => ℓ.1 s) h).trans
      (liftAct_baseLift_apply B f y hres _ x' s)))
  refine ⟨rfl, ?_⟩
  let := fiberResidueAlgebra (fS B f) y x
  let : Fintype (Y.1.residueField y) := Fintype.ofFinite _
  have := hres x
  rw [liftAct_pow_baseLift, liftAct_pow_baseLift] at h
  exact congrArg Fin.val ((bijective_pow_comp (residueGeometricFrobenius Y.1 y)
    (residueGeometricFrobenius_symm_apply_card B y)
    (Classical.choice (nonempty_fiberEmbeddings B f y hres x))).1
    (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (liftOfEmbedding_injective (fS B f) y x h))

omit [IsFinite (fS B f)] in
/-- **The Frobenius orbits of the base lifts cover all lifts.** -/
public theorem exists_liftAct_pow_baseLift (ℓ : PointLifts (fS B f) y) :
    ∃ x : {x : X.1 // (fS B f) x = y}, ∃ i < fiberDegree B f y x,
      liftAct B f y (residueGeometricFrobenius Y.1 y ^ i) (baseLift B f y hres x) = ℓ := by
  obtain ⟨x, ι, rfl⟩ := exists_liftOfEmbedding (fS B f) y ℓ
  let := fiberResidueAlgebra (fS B f) y x
  let : Fintype (Y.1.residueField y) := Fintype.ofFinite _
  have := hres x
  obtain ⟨k, hk⟩ := (bijective_pow_comp (residueGeometricFrobenius Y.1 y)
    (residueGeometricFrobenius_symm_apply_card B y)
    (Classical.choice (nonempty_fiberEmbeddings B f y hres x))).2 ι
  refine ⟨x, k, k.2, ?_⟩
  rw [liftAct_pow_baseLift]
  exact congrArg _ hk

include hres in
/-- The fibre of a finite morphism over a point with finite residue field is finite. -/
public theorem finite_fiber : Finite {x : X.1 // (fS B f) x = y} := by
  have : Finite (PointLifts (fS B f) y) :=
    finite_geometricPointLifts (fS B f) (geometricPointAt Y.1 y)
  refine Finite.of_injective (baseLift B f y hres) fun x x' h => ?_
  refine (eq_of_liftAct_pow_baseLift_eq B f y hres (i := 0) (j := 0) (fiberDegree_pos B f y hres x)
    (fiberDegree_pos B f y hres x') ?_).1
  rwa [pow_zero, liftAct_one, liftAct_one]

end Orbits

omit [IsFinite (fS B f)] in
/-- **The residue fields of a finite morphism are finite extensions**: a point over a point with
finite residue field has finite residue field. -/
public theorem finite_residueField_of_isFinite [LocallyQuasiFinite (fS B f)]
    [Finite (Y.1.residueField y)] (x : {x : X.1 // (fS B f) x = y}) :
    Finite (X.1.residueField x.1) := by
  have hfx : Finite (Y.1.residueField ((fS B f) x.1)) := by
    rw [x.2]
    infer_instance
  let m := ((fS B f).residueFieldMap x.1).hom
  let : Algebra (Y.1.residueField ((fS B f) x.1)) (X.1.residueField x.1) := m.toAlgebra
  have hm : m.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := (Y.1.residue ((fS B f) x.1)).hom)
    rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      IsLocalRing.residue_surjective)).comp ((fS B f).quasiFiniteAt x.1)
  have : Algebra.QuasiFinite (Y.1.residueField ((fS B f) x.1)) (X.1.residueField x.1) := hm
  have : Module.Finite (Y.1.residueField ((fS B f) x.1)) (X.1.residueField x.1) := .of_quasiFinite
  exact Module.finite_of_finite (Y.1.residueField ((fS B f) x.1))

/-! ### Finite projective stalks of `f_* G` -/

/-- The stalk of `f_* G` at a geometric point is the product of the stalks of `G` at its lifts. -/
private theorem nonempty_linearEquiv_pi_liftStalks (s : GeometricPoint Y.1) :
    Nonempty (((etaleModuleStalkFunctor.{u, u + 1, 0} B Y Λ s).obj
      (moduleDirectImage B f Λ G)) ≃ₗ[Λ]
      ∀ ℓ : {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom},
        etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointLift (fS B f) s ℓ)
          G.obj) :=
  ⟨LinearEquiv.ofBijective
    (LinearMap.pi fun ℓ => (finitePushforwardModuleStalkComponent B f s Λ G ℓ).hom)
    (finitePushforwardModuleStalkComponent_bijective B f s Λ G)⟩

/-- **The stalks of `f_* G` are finite** when those of `G` are. -/
public theorem finite_etaleModuleStalk_moduleDirectImage
    (hfin : ∀ s : GeometricPoint X.1,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
    (s : GeometricPoint Y.1) :
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Y Λ s).obj
      (moduleDirectImage B f Λ G)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_pi_liftStalks B f Λ G s
  have : Finite {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom} := finite_geometricPointLifts _ s
  have : ∀ ℓ : {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom}, Module.Finite Λ
      (etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointLift (fS B f) s ℓ)
        G.obj) := fun ℓ => hfin _
  exact Module.Finite.equiv e.symm

/-- **The stalks of `f_* G` are projective** when those of `G` are. -/
public theorem projective_etaleModuleStalk_moduleDirectImage
    (hproj : ∀ s : GeometricPoint X.1,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
    (s : GeometricPoint Y.1) :
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Y Λ s).obj
      (moduleDirectImage B f Λ G)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_pi_liftStalks B f Λ G s
  have : Finite {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom} := finite_geometricPointLifts _ s
  let : Fintype {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom} := Fintype.ofFinite _
  have : ∀ ℓ : {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom}, Module.Projective Λ
      (etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointLift (fS B f) s ℓ)
        G.obj) := fun ℓ => hproj _
  have := ProjectiveDeterminant.projective_pi (R := Λ)
    (V := fun ℓ : {g : s.source ⟶ X.1 // g ≫ fS B f = s.hom} =>
      etaleStalk (A := ModuleCat.{u + 1} Λ) B X.1 X.property (geometricPointLift (fS B f) s ℓ)
        G.obj)
  exact Module.Projective.of_equiv e.symm

/-! ### The cyclic decomposition of the Frobenius of `f_* G` -/

section Cyclic

variable [Finite (Y.1.residueField y)]
  (hres : ∀ x : {x : X.1 // (fS B f) x = y}, Finite (X.1.residueField x.1))

/-- `[κ(x) : κ(y)] - 1`, the length of the orbit over `x` minus one. -/
public abbrev orbitLength (x : {x : X.1 // (fS B f) x = y}) : ℕ := fiberDegree B f y x - 1

omit [IsFinite (fS B f)] [Finite (Y.1.residueField y)] in
include hres in
/-- `orbitLength x + 1` is the residue degree `[κ(x) : κ(y)]`. -/
public theorem orbitLength_add_one (x : {x : X.1 // (fS B f) x = y}) :
    orbitLength B f y x + 1 = fiberDegree B f y x :=
  Nat.sub_add_cancel (fiberDegree_pos B f y hres x)

/-- **The return map** at the base lift over `x`: the stalk map along `σ_y ^ [κ(x) : κ(y)]`, which
fixes the base lift. -/
public def returnMap (x : {x : X.1 // (fS B f) x = y}) :
    liftStalk B f Λ G y (baseLift B f y hres x) →ₗ[Λ] liftStalk B f Λ G y (baseLift B f y hres x) :=
  ((geometricPointStalkMap B X.1 X.property
    (GeometricLifts.homOfComm B f
      (galoisPow B y (residueGeometricFrobenius Y.1 y) (fiberDegree B f y x))
      (baseLift B f y hres x) (baseLift B f y hres x)
      (congrArg Subtype.val (liftAct_pow_fiberDegree_baseLift B f y hres x)))
    (ModuleCat.{u + 1} Λ)).app G.obj).hom

/-- Going once around the orbit over `x` is the return map. -/
public theorem pow_comp_liftInclusion_baseLift (x : {x : X.1 // (fS B f) x = y}) :
    (pushforwardStalkGalois B f Λ G y (residueGeometricFrobenius Y.1 y) ^
        (orbitLength B f y x + 1)) ∘ₗ liftInclusion B f Λ G y (baseLift B f y hres x) =
      liftInclusion B f Λ G y (baseLift B f y hres x) ∘ₗ returnMap B f Λ G y hres x := by
  let := Classical.decEq (PointLifts (fS B f) y)
  rw [orbitLength_add_one B f y hres x]
  refine LinearMap.ext fun v => ?_
  apply (pushforwardStalkEquiv B f Λ G y).injective
  funext ℓ'
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pushforwardStalkEquiv_liftInclusion]
  by_cases hℓ : ℓ' = baseLift B f y hres x
  · subst hℓ
    rw [pushforwardStalkEquiv_galois_pow B f Λ G y _ _ _ _
      (congrArg Subtype.val (liftAct_pow_fiberDegree_baseLift B f y hres x)),
      pushforwardStalkEquiv_liftInclusion]
    rw [Pi.single_eq_same, Pi.single_eq_same]
    rfl
  · have hne : ℓ' ≠ liftAct B f y (residueGeometricFrobenius Y.1 y ^ fiberDegree B f y x)
        (baseLift B f y hres x) := by
      rwa [liftAct_pow_fiberDegree_baseLift]
    rw [pushforwardStalkEquiv_pow_liftInclusion_of_ne B f Λ G y _ _ _ _ _ hne]
    exact (Pi.single_eq_of_ne (M := fun ℓ => ↥(liftStalk B f Λ G y ℓ)) hℓ _).symm

/-- **The components of the cyclic map**: at the lift `σ ^ i (base x)`, the sum
`∑_{x', i'} Φ ^ i' (w_{x', i'})` is the stalk map along `σ ^ i` applied to `w_{x, i}`. -/
public theorem pushforwardStalkEquiv_cyclicSum
    (w : ∀ x : {x : X.1 // (fS B f) x = y}, Fin (orbitLength B f y x + 1) →
      liftStalk B f Λ G y (baseLift B f y hres x))
    (x₀ : {x : X.1 // (fS B f) x = y}) (i₀ : Fin (orbitLength B f y x₀ + 1)) :
    letI : Fintype {x : X.1 // (fS B f) x = y} := @Fintype.ofFinite _ (finite_fiber B f y hres)
    pushforwardStalkEquiv B f Λ G y (∑ x, ∑ i : Fin (orbitLength B f y x + 1),
        (pushforwardStalkGalois B f Λ G y (residueGeometricFrobenius Y.1 y) ^ (i : ℕ))
          (liftInclusion B f Λ G y (baseLift B f y hres x) (w x i)))
        (liftAct B f y (residueGeometricFrobenius Y.1 y ^ (i₀ : ℕ)) (baseLift B f y hres x₀)) =
      liftStalkMap B f Λ G y (residueGeometricFrobenius Y.1 y ^ (i₀ : ℕ)) (baseLift B f y hres x₀)
        (w x₀ i₀) := by
  let : Fintype {x : X.1 // (fS B f) x = y} := @Fintype.ofFinite _ (finite_fiber B f y hres)
  have hlt : ∀ (x : {x : X.1 // (fS B f) x = y}) (i : Fin (orbitLength B f y x + 1)),
      (i : ℕ) < fiberDegree B f y x := fun x i =>
    lt_of_lt_of_eq i.2 (orbitLength_add_one B f y hres x)
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single x₀]
  · rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i₀]
    · exact pushforwardStalkEquiv_pow_liftInclusion_self B f Λ G y _ _ _ _
    · intro i _ hi
      exact pushforwardStalkEquiv_pow_liftInclusion_of_ne B f Λ G y _ _ _ _ _ fun h =>
        hi (Fin.ext (eq_of_liftAct_pow_baseLift_eq B f y hres (hlt _ _) (hlt _ _) h).2.symm)
    · exact fun h => absurd (Finset.mem_univ _) h
  · intro x _ hx
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ =>
      pushforwardStalkEquiv_pow_liftInclusion_of_ne B f Λ G y _ _ _ _ _ fun h =>
        hx (eq_of_liftAct_pow_baseLift_eq B f y hres (hlt _ _) (hlt _ _) h).1.symm
  · exact fun h => absurd (Finset.mem_univ _) h

include hres in
/-- **The local factor of a finite direct image.** The geometric Frobenius of `ȳ` on
`(f_* G)_ȳ = ∏_ℓ G_ℓ` decomposes along the orbits of the lifts:
`det(1 - Φ T ^ d | (f_* G)_ȳ) = ∏_{x ↦ y} det(1 - ψ_x T ^ (d [κ(x) : κ(y)]) | G_{x̄})`,
with `ψ_x` the return map at the base lift over `x`. -/
public theorem charSeries_pushforwardStalkGalois
    (hfin : ∀ s : GeometricPoint X.1,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G))
    (hproj : ∀ s : GeometricPoint X.1,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj G)) (d : ℕ) :
    letI : Fintype {x : X.1 // (fS B f) x = y} := @Fintype.ofFinite _ (finite_fiber B f y hres)
    haveI : Module.Finite Λ (pushforwardStalkAt B f Λ G y) :=
      finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _
    haveI : Module.Projective Λ (pushforwardStalkAt B f Λ G y) :=
      projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _
    haveI : ∀ x : {x : X.1 // (fS B f) x = y},
        Module.Finite Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := fun _ => hfin _
    haveI : ∀ x : {x : X.1 // (fS B f) x = y},
        Module.Projective Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := fun _ => hproj _
    ProjectiveDeterminant.charSeries
        (pushforwardStalkGalois B f Λ G y (residueGeometricFrobenius Y.1 y)) d =
      ∏ x, ProjectiveDeterminant.charSeries (returnMap B f Λ G y hres x)
        (d * fiberDegree B f y x) := by
  let : Fintype {x : X.1 // (fS B f) x = y} := @Fintype.ofFinite _ (finite_fiber B f y hres)
  have : Module.Finite Λ (pushforwardStalkAt B f Λ G y) :=
    finite_etaleModuleStalk_moduleDirectImage B f Λ G hfin _
  have : Module.Projective Λ (pushforwardStalkAt B f Λ G y) :=
    projective_etaleModuleStalk_moduleDirectImage B f Λ G hproj _
  have : ∀ x : {x : X.1 // (fS B f) x = y},
      Module.Finite Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := fun _ => hfin _
  have : ∀ x : {x : X.1 // (fS B f) x = y},
      Module.Projective Λ (liftStalk B f Λ G y (baseLift B f y hres x)) := fun _ => hproj _
  have hbij : Function.Bijective (ProjectiveDeterminant.cyclicMap
      (fun x => liftStalk B f Λ G y (baseLift B f y hres x))
      (pushforwardStalkGalois B f Λ G y (residueGeometricFrobenius Y.1 y))
      (orbitLength B f y) (fun x => liftInclusion B f Λ G y (baseLift B f y hres x))) := by
    refine ⟨fun w w' h => ?_, fun z => ?_⟩
    · funext x i
      apply (liftStalkMap_bijective B f Λ G y (residueGeometricFrobenius Y.1 y ^ (i : ℕ))
        (baseLift B f y hres x)).1
      have h1 := congrArg (fun z => pushforwardStalkEquiv B f Λ G y z
        (liftAct B f y (residueGeometricFrobenius Y.1 y ^ (i : ℕ)) (baseLift B f y hres x))) h
      simp only [ProjectiveDeterminant.cyclicMap_apply] at h1
      exact (pushforwardStalkEquiv_cyclicSum B f Λ G y hres w x i).symm.trans
        (h1.trans (pushforwardStalkEquiv_cyclicSum B f Λ G y hres w' x i))
    · refine ⟨fun x i => (liftStalkMapEquiv B f Λ G y (residueGeometricFrobenius Y.1 y ^ (i : ℕ))
        (baseLift B f y hres x)).symm (pushforwardStalkEquiv B f Λ G y z
          (liftAct B f y (residueGeometricFrobenius Y.1 y ^ (i : ℕ)) (baseLift B f y hres x))), ?_⟩
      apply (pushforwardStalkEquiv B f Λ G y).injective
      funext ℓ
      obtain ⟨x, i, hi, rfl⟩ := exists_liftAct_pow_baseLift B f y hres ℓ
      rw [ProjectiveDeterminant.cyclicMap_apply]
      exact (pushforwardStalkEquiv_cyclicSum B f Λ G y hres _ x
        ⟨i, by rwa [orbitLength_add_one B f y hres x]⟩).trans
          ((liftStalkMapEquiv B f Λ G y _ _).apply_symm_apply _)
  rw [ProjectiveDeterminant.charSeries_eq_prod_of_cyclicMap_bijective _ _ _ _
    (returnMap B f Λ G y hres) (pow_comp_liftInclusion_baseLift B f Λ G y hres) hbij d]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [orbitLength_add_one B f y hres x]

end Cyclic

end Stalk

end Stacks.EtaleCohomology

end
