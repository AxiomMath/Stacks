module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartModBridge
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality

/-!
# The tangent module of a chart point is the module of the groupoid of the chart

With the notation of `Deformation.Artin.ChartLift`, let `w : P → C` be a point of a chart and
`M` a `C`-module. The trivial square-zero extension `C[M] → C` is a thickening of small
`A'`-algebras (`Deformation.Artin.ChartLift.sqzE`), and `Spec C[M]` as an object of the site
through `T'` is the object `squareZeroOver C M` of the tangent functor of Stacks 07Y9. So the
lift classes of `ξ w` to `C[M]` of the tangent functor are the lift classes of the chart
(`Deformation.Artin.ChartLift.sqzLiftClassesEquiv`).

Composing with `Deformation.Artin.ChartLift.bijective_modToLiftClasses`, any realization of the
tangent functor at `ξ w` is identified with the modules `Mod w` of the groupoid of the chart,
and the identification is semilinear along `C → C[M]` because it is natural in `M`
(`Deformation.Artin.ChartLift.tangentToMod`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent
open AlgebraicGeometry.Stack.GroupoidLift.StackChart

namespace Deformation.Artin.ChartLift

universe u v

section Sqz

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}

/-- The `A'`-algebra structure of `C[M]` through `C`. -/
abbrev sqzAlgebra (C : Type u) [CommRing C] [Algebra A' C] (M : ModuleCat.{u} C) :
    Algebra A' (TrivSqZeroExt C M) :=
  ((TrivSqZeroExt.inlHom C M).comp (algebraMap A' C)).toAlgebra

/-- `C[M]` as a small `A'`-algebra. -/
def sqzAlg (C : SmallAlg A' κ) (M : ModuleCat.{u} C.obj)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ) : SmallAlg A' κ :=
  ⟨@CommAlgCat.of A' _ (TrivSqZeroExt C.obj M) _ (sqzAlgebra C.obj M), hM⟩

/-- The first projection `C[M] → C`, as a map of small `A'`-algebras. -/
def sqzFst (C : SmallAlg A' κ) (M : ModuleCat.{u} C.obj)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ) : sqzAlg C M hM ⟶ C :=
  SmallAlg.homMk
    { (TrivSqZeroExt.fstHom C.obj C.obj M).toRingHom with commutes' := fun _ ↦ rfl }

/-- The inclusion `C → C[M]`, as a map of `A'`-algebras. -/
def sqzInl (C : SmallAlg A' κ) (M : ModuleCat.{u} C.obj)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ) : C.obj →ₐ[A'] (sqzAlg C M hM).obj :=
  { TrivSqZeroExt.inlHom C.obj M with commutes' := fun _ ↦ rfl }

/-- The map `C[M] → C[N]` of a module map, as a map of small `A'`-algebras. -/
def sqzMap (C : SmallAlg A' κ) {M N : ModuleCat.{u} C.obj} (f : M ⟶ N)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ)
    (hN : Cardinal.mk (TrivSqZeroExt C.obj N) < κ) : sqzAlg C M hM ⟶ sqzAlg C N hN :=
  SmallAlg.homMk
    { (TrivSqZeroExt.map f.hom).toRingHom with
      commutes' := fun a ↦ by
        change TrivSqZeroExt.map f.hom (TrivSqZeroExt.inl _) = TrivSqZeroExt.inl _
        exact TrivSqZeroExt.map_inl _ _ }

/-- The map `C[M] → C[N]` of a module map sends `(c, 0) + y` to `(c, 0) + f(y)`. -/
theorem sqzMap_inl_add (C : SmallAlg A' κ) {M N : ModuleCat.{u} C.obj} (f : M ⟶ N)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ)
    (hN : Cardinal.mk (TrivSqZeroExt C.obj N) < κ) (c : C.obj) (y : (sqzAlg C M hM).obj) :
    (sqzMap C f hM hN).hom.hom (sqzInl C M hM c + y) =
      sqzInl C N hN c + (sqzMap C f hM hN).hom.hom y := by
  rw [_root_.map_add]
  congr 1
  exact TrivSqZeroExt.map_inl f.hom c

/-- On an element `y` with `y.fst = 0`, `TrivSqZeroExt.map` is additive in the linear map. -/
theorem tsze_map_add_apply {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} (φ ψ : M →ₗ[R] N)
    (y : TrivSqZeroExt R M) (hy : y.fst = 0) :
    TrivSqZeroExt.map (φ + ψ) y = TrivSqZeroExt.map φ y + TrivSqZeroExt.map ψ y := by
  ext
  · simp [hy]
  · simp

/-- On an element `y` with `y.fst = 0`, `TrivSqZeroExt.map (c • id)` is multiplication by
`(c, 0)`. -/
theorem tsze_map_smul_apply {R : Type u} [CommRing R] {M : ModuleCat.{u} R} (c : R)
    (y : TrivSqZeroExt R M) (hy : y.fst = 0) :
    TrivSqZeroExt.map (c • LinearMap.id) y = TrivSqZeroExt.inl c * y := by
  ext
  · simp [hy]
  · simp [hy]

/-- **The trivial square-zero extension `C[M] → C`** as a thickening of small algebras. -/
def sqzE (C : SmallAlg A' κ) (M : ModuleCat.{u} C.obj)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ) : SqZero (sqzAlg C M hM) C where
  q := sqzFst C M hM
  surj c := ⟨(TrivSqZeroExt.inl c : TrivSqZeroExt C.obj M), rfl⟩
  sq := TrivSqZeroExt.kerIdeal_sq C.obj M

/-- The map of thickenings `C[M] → C[N]` over the identity of `C`. -/
def sqzHom (C : SmallAlg A' κ) {M N : ModuleCat.{u} C.obj} (f : M ⟶ N)
    (hM : Cardinal.mk (TrivSqZeroExt C.obj M) < κ)
    (hN : Cardinal.mk (TrivSqZeroExt C.obj N) < κ) : SqZero.Hom (sqzE C M hM) (sqzE C N hN) where
  top := sqzMap C f hM hN
  bot := 𝟙 C
  w := by
    ext z
    exact TrivSqZeroExt.fst_map f.hom z

end Sqz

/-! ### Transport of lifts along an equality of bases -/

section Transport

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (p : 𝒞 ⥤ 𝒟)

/-- `p.IsHomLift` transported along equal bases and heterogeneously equal arrows. -/
theorem isHomLift_of_heq {R R' T T' : 𝒟} (hR : R = R') (hT : T = T') {f : R ⟶ T}
    {g : R' ⟶ T'} (h : HEq f g) {x y : 𝒞} {φ : x ⟶ y} (hf : p.IsHomLift f φ) :
    p.IsHomLift g φ := by
  subst hR hT
  cases h
  exact hf

/-- `p.IsStronglyCartesian` transported along equal bases and heterogeneously equal arrows. -/
theorem isStronglyCartesian_of_heq {R R' T T' : 𝒟} (hR : R = R') (hT : T = T') {f : R ⟶ T}
    {g : R' ⟶ T'} (h : HEq f g) {x y : 𝒞} {φ : x ⟶ y} (hf : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian g φ := by
  subst hR hT
  cases h
  exact hf

/-- Heterogeneously equal arrows out of `R` give equal objects of `Under R`. -/
theorem under_mk_eq_of_heq {R T T' : 𝒟} (hT : T = T') {f : R ⟶ T} {g : R ⟶ T'}
    (h : HEq f g) : Under.mk f = Under.mk g := by
  subst hT
  cases h
  rfl

/-- Precomposition preserves heterogeneous equality of arrows with equal targets. -/
theorem comp_heq_comp {R R' T T' : 𝒟} (hT : T = T') (k : R' ⟶ R) {f : R ⟶ T} {g : R ⟶ T'}
    (h : HEq f g) : HEq (k ≫ f) (k ≫ g) := by
  subst hT
  cases h
  rfl

/-- Isomorphism classes of objects of equal fibres of `Under.post p`. -/
def classesCongr {x : 𝒞} {u v : Under (p.obj x)} (h : u = v) :
    Quotient (isIsomorphicSetoid ((Under.post p).Fiber u)) ≃
      Quotient (isIsomorphicSetoid ((Under.post p).Fiber v)) where
  toFun := Quotient.map (fun t ↦ ⟨t.1, t.2.trans h⟩) (by subst h; exact fun _ _ hst ↦ hst)
  invFun := Quotient.map (fun t ↦ ⟨t.1, t.2.trans h.symm⟩) (by subst h; exact fun _ _ hst ↦ hst)
  left_inv := fun c ↦ by induction c using Quotient.ind; rfl
  right_inv := fun c ↦ by induction c using Quotient.ind; rfl

end Transport

/-! ### `Spec C[M]` in the site -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- `C[M]` is small (of cardinality `< B.cutoff`) for a site module `M`. -/
theorem card_sqz_lt {C : SmallAlg (ringOf B S hS T') B.cutoff} (M : SiteModule C.obj B) :
    Cardinal.mk (TrivSqZeroExt C.obj M.obj) < B.cutoff := by
  have hM : (Spec (squareZeroRing C.obj M.obj)).size < B.cutoff := M.property
  rw [Scheme.size_Spec] at hM
  exact lt_of_le_of_lt (le_max_right _ _) hM

variable (C : SmallAlg (ringOf B S hS T') B.cutoff)

/-- The structure morphism `Spec C → S` through `T'`. -/
abbrev toSOf : Spec (.of C.obj) ⟶ S := specToBase C ≫ B.inclusion.map T'.hom

/-- `C[M]` for a site module `M`. -/
abbrev sqzAlgOf (M : SiteModule C.obj B) : SmallAlg (ringOf B S hS T') B.cutoff :=
  sqzAlg C M.obj (card_sqz_lt M)

/-- The thickening `C[M] → C` for a site module `M`. -/
abbrev sqzEOf (M : SiteModule C.obj B) : SqZero (sqzAlgOf C M) C :=
  sqzE C M.obj (card_sqz_lt M)

/-- The object `Spec C` of the site, as an algebra over `S`, is `specOver C`. -/
theorem algebraOver_eq_specOver :
    algebraOver C.obj B S hS (toSOf C) (contains_spec C) = specOver C := rfl

/-- The object `Spec C[M]` of the site is `specOver C[M]`. -/
theorem squareZeroOver_eq_specOver (M : SiteModule C.obj B) :
    squareZeroOver C.obj B S hS (toSOf C) M = specOver (sqzAlgOf C M) := by
  have h : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom C.obj M.obj)) ≫ toSOf C =
      specToBase (sqzAlgOf C M) ≫ B.inclusion.map T'.hom := by
    rw [← Category.assoc]
    congr 1
    exact specMap_comp_specToBase (SmallAlg.homMk (sqzInl C M.obj (card_sqz_lt M)))
  exact congrArg (fun g ↦ (Over.mk (ObjectProperty.homMk g :
    B.obj (contains_spec (sqzAlgOf C M)) ⟶ B.obj hS) : BigFppfOver B S hS)) h

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Two morphisms of `BigFppfOver B S hS` between equal objects are heterogeneously equal if their
images in schemes are. -/
theorem hom_heq_of_toScheme {X X' Y Y' : BigFppfOver B S hS} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : HEq ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g)) :
    HEq f g := by
  subst hX hY
  exact heq_of_eq (Over.OverMorphism.ext (B.inclusion.map_injective (eq_of_heq h)))

/-- The map `Spec C[N] → Spec C[M]` of a map of site modules is, up to the identifications
`squareZeroOver_eq_specOver`, the map `specOverMap` of `C[M] → C[N]`. -/
theorem squareZeroOverMap_heq {M N : SiteModule C.obj B} (f : M ⟶ N) :
    HEq (squareZeroOverMap C.obj B S hS (toSOf C) f)
      (specOverMap (sqzMap C f.hom (card_sqz_lt M) (card_sqz_lt N))) := by
  have h₁ : ((BigFppfOver.toScheme B S hS).map (squareZeroOverMap C.obj B S hS (toSOf C) f) :
      Spec (squareZeroRing C.obj N.obj) ⟶ Spec (squareZeroRing C.obj M.obj)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) := rfl
  have h₂ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) =
      ((BigFppfOver.toScheme B S hS).map
        (specOverMap (sqzMap C f.hom (card_sqz_lt M) (card_sqz_lt N))) :
          Spec (squareZeroRing C.obj N.obj) ⟶ Spec (squareZeroRing C.obj M.obj)) := rfl
  exact hom_heq_of_toScheme (squareZeroOver_eq_specOver C N) (squareZeroOver_eq_specOver C M)
    ((heq_of_eq h₁).trans (heq_of_eq h₂))

/-- The arrow `Spec C → Spec C[M]` is, up to the identifications of
`squareZeroOver_eq_specOver`, the map `specOverMap` of the projection `C[M] → C`. -/
theorem squareZeroArrow_heq (M : SiteModule C.obj B) :
    HEq (squareZeroArrow C.obj B S hS (toSOf C) (contains_spec C) M)
      (specOverMap (sqzEOf C M).q) := by
  have h₁ : ((BigFppfOver.toScheme B S hS).map
      (squareZeroArrow C.obj B S hS (toSOf C) (contains_spec C) M) :
        Spec (.of C.obj) ⟶ Spec (squareZeroRing C.obj M.obj)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C.obj C.obj M.obj).toRingHom) := rfl
  have h₂ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C.obj C.obj M.obj).toRingHom) =
      ((BigFppfOver.toScheme B S hS).map (specOverMap (sqzEOf C M).q) :
        Spec (.of C.obj) ⟶ Spec (squareZeroRing C.obj M.obj)) := rfl
  exact hom_heq_of_toScheme (algebraOver_eq_specOver C) (squareZeroOver_eq_specOver C M)
    ((heq_of_eq h₁).trans (heq_of_eq h₂))

end Site

/-- Two vectors of an additive functor on the site modules at `M` are the two projections of one
vector at `M × M`, whose image under the sum of the projections is their sum. -/
theorem exists_sum_siteModuleProd {A : Type u} [CommRing A] {B : BigFppfSite.{u}}
    (hA : B.Contains (Spec (.of A))) (Fu : SiteModule A B ⥤ ModuleCat.{v} A)
    [Fu.Additive] {M : SiteModule A B} (z₁ z₂ : (Fu.obj M : Type v)) :
    ∃ z : (Fu.obj (siteModuleProd A B hA M M) : Type v),
      Fu.map (siteModuleFst A B hA M M) z = z₁ ∧ Fu.map (siteModuleSnd A B hA M M) z = z₂ ∧
        Fu.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) z = z₁ + z₂ := by
  have hcomp (j' : M ⟶ siteModuleProd A B hA M M) (k : siteModuleProd A B hA M M ⟶ M)
      (y : (Fu.obj M : Type v)) : Fu.map k (Fu.map j' y) = Fu.map (j' ≫ k) y := by
    rw [Fu.map_comp]
    rfl
  have h₁ : Fu.map (siteModuleFst A B hA M M) (Fu.map (siteModuleInl A B hA M M) z₁ +
      Fu.map (siteModuleInr A B hA M M) z₂) = z₁ := by
    simp [hcomp, siteModuleInl_comp_fst, siteModuleInr_comp_fst]
  have h₂ : Fu.map (siteModuleSnd A B hA M M) (Fu.map (siteModuleInl A B hA M M) z₁ +
      Fu.map (siteModuleInr A B hA M M) z₂) = z₂ := by
    simp [hcomp, siteModuleInl_comp_snd, siteModuleInr_comp_snd]
  refine ⟨_, h₁, h₂, ?_⟩
  rw [Fu.map_add]
  change Fu.map (siteModuleFst A B hA M M) _ + Fu.map (siteModuleSnd A B hA M M) _ = _
  rw [h₁, h₂]

/-! ### Lift classes of the tangent functor at a chart point -/

section Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)
  {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj)

/-- The transition `trans a ι h u` along equal maps `h = h'`, up to an `eqToHom`. -/
theorem trans_congr {C₁ D₁ : SmallAlg (ringOf B S hS T') B.cutoff} {h h' : C₁ ⟶ D₁} (hh : h = h')
    (u : P.obj →ₐ[ringOf B S hS T'] C₁.obj) :
    trans a ι h u = eqToHom (by rw [hh]) ≫ trans a ι h' u := by
  subst hh
  simp

/-- A map of thickenings carries the lift of `ξ w` of a lift `ℓ` to the lift of `g ∘ ℓ`, along
the cartesian arrow `ξ (g ∘ ℓ) ⟶ ξ ℓ`. -/
theorem liftArrow_comp_trans {C₁ C₂ : SmallAlg (ringOf B S hS T') B.cutoff} {e₁ : SqZero C₁ C}
    {e₂ : SqZero C₂ C} (g : C₁ ⟶ C₂) (hg : g ≫ e₂.q = e₁.q)
    (ℓ : P.obj →ₐ[ringOf B S hS T'] C₁.obj) (hℓ : e₁.q.hom.hom.comp ℓ = w)
    (hℓ' : e₂.q.hom.hom.comp (g.hom.hom.comp ℓ) = w) :
    liftArrow (a := a) (ι := ι) (e := e₂) (g.hom.hom.comp ℓ) hℓ' ≫ trans a ι g ℓ =
      liftArrow (a := a) (ι := ι) (e := e₁) ℓ hℓ := by
  subst hℓ
  simp only [liftArrow, Category.assoc]
  rw [← trans_comp, trans_congr a ι hg]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (eqToHom_trans _ _))

variable (M : SiteModule C.obj B)

/-- The base point `C → C[M]` composed with `w`. -/
abbrev ℓ₀ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj :=
  (sqzInl C M.obj (card_sqz_lt M)).comp w

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The base point `ℓ₀ = (w, 0)` is a lift of `w` to `C[M]`. -/
theorem ℓ₀_reduce : (sqzEOf C M).q.hom.hom.comp (ℓ₀ w M) = w := by
  ext
  rfl

/-- **The lift classes of the tangent functor at `ξ w` are the lift classes of the chart.** -/
def sqzLiftClassesEquiv :
    squareZeroLiftClasses C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
      (ξ_obj a ι w) M ≃ liftClasses a ι (sqzEOf C M) w :=
  classesCongr 𝒳.val.p (under_mk_eq_of_heq (squareZeroOver_eq_specOver C M)
    (comp_heq_comp (squareZeroOver_eq_specOver C M) (eqToHom (ξ_obj a ι w))
      (squareZeroArrow_heq C M)))

/-- The lift of `ξ w` to `C[M]`, in the sense of the tangent functor, of a lift of `w`. -/
def sqzLift (ℓ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj)
    (hℓ : (sqzEOf C M).q.hom.hom.comp ℓ = w) :
    (Under.post 𝒳.val.p).Fiber (Under.mk (eqToHom (ξ_obj a ι w) ≫
      squareZeroArrow C.obj B S hS (toSOf C) (contains_spec C) M)) :=
  underFiberObjMk 𝒳.val.p (ξ_obj a ι w) _ (liftArrow (a := a) (ι := ι) ℓ hℓ)
    (isHomLift_of_heq 𝒳.val.p rfl (squareZeroOver_eq_specOver C M).symm
      (squareZeroArrow_heq C M).symm (liftArrow_isHomLift ℓ hℓ))

/-- `sqzLiftClassesEquiv` sends the class of `sqzLift ℓ` to the class of the chart lift of `ℓ`. -/
theorem sqzLiftClassesEquiv_mk (ℓ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj)
    (hℓ : (sqzEOf C M).q.hom.hom.comp ℓ = w) :
    sqzLiftClassesEquiv a ι w M (Quotient.mk _ (sqzLift a ι w M ℓ hℓ)) =
      Quotient.mk _ (lift (a := a) (ι := ι) ℓ hℓ) := rfl

variable {a ι w}

variable (hrel : ∀ (M : SiteModule C.obj B) {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj},
    (sqzEOf C M).q.hom.hom.comp ℓ₁ = w → (sqzEOf C M).q.hom.hom.comp ℓ₂ = w →
      (Rel (stackGroupoid a ι) (sqzEOf C M) w ℓ₁ ℓ₂ ↔ ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈
        AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) (sqzEOf C M) w))
  (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
  (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')
  (F : TangentFunctorData C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
    (ξ_obj a ι w))

/-- **The tangent module at a chart point is the module of the groupoid of the chart**:
`T_{ξ w}(M) ≃ Mod (C[M] → C) w`, through the lift classes. -/
def tangentToMod : (F.functor.obj M : Type _) ≃ Mod (stackGroupoid a ι) (sqzEOf C M) w :=
  (F.liftEquiv M).trans ((sqzLiftClassesEquiv a ι w M).trans
    (Equiv.ofBijective _ (bijective_modToLiftClasses (ℓ₀ w M) (ℓ₀_reduce w M) (hrel M) ha hι)).symm)

/-- If `tangentToMod` sends `z` to the class of a derivation `D`, then the lift class of `z` is
that of the lift `ℓ₀ + D`. -/
theorem liftEquiv_eq_of_tangentToMod {z : (F.functor.obj M : Type _)}
    {D : P.obj →ₗ[ringOf B S hS T'] (sqzAlgOf C M).obj} (hD : D ∈ Der (sqzEOf C M) w)
    (h : tangentToMod M hrel ha hι F z = mkMod D hD) :
    F.liftEquiv M z = Quotient.mk _ (sqzLift a ι w M (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))
      (addLift_reduce D hD (ℓ₀ w M) (ℓ₀_reduce w M))) := by
  have h' := congrArg (Equiv.ofBijective _
    (bijective_modToLiftClasses (ℓ₀ w M) (ℓ₀_reduce w M) (hrel M) ha hι)) h
  simp only [tangentToMod, Equiv.trans_apply, Equiv.apply_symm_apply] at h'
  rw [← (sqzLiftClassesEquiv a ι w M).symm_apply_apply (F.liftEquiv M z), h']
  rfl

/-- If the lift class of `z` is that of the lift `ℓ`, then `tangentToMod` sends `z` to the class
of the derivation `ℓ - ℓ₀`. -/
theorem tangentToMod_of_liftEquiv {z : (F.functor.obj M : Type _)}
    {ℓ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj} (hℓ : (sqzEOf C M).q.hom.hom.comp ℓ = w)
    (h : F.liftEquiv M z = Quotient.mk _ (sqzLift a ι w M ℓ hℓ)) :
    tangentToMod M hrel ha hι F z =
      mkMod (ℓ.toLinearMap - (ℓ₀ w M).toLinearMap) (sub_mem_Der (ℓ₀_reduce w M) hℓ) := by
  rw [tangentToMod, Equiv.trans_apply, Equiv.trans_apply, h]
  refine (Equiv.symm_apply_eq _).mpr ?_
  change Quotient.mk _ (lift (a := a) (ι := ι) ℓ hℓ) =
    modToLiftClasses (ℓ₀ w M) (ℓ₀_reduce w M) (hrel M) (mkMod _ _)
  rw [modToLiftClasses_mk]
  congr 2
  exact eq_addLift (ℓ₀_reduce w M) hℓ

/-! ### Naturality in the module and linearity -/

section Natural

variable {M N : SiteModule C.obj B} (f : M ⟶ N)

/-- The map of thickenings `C[M] → C[N]` of a map of site modules. -/
abbrev sqzHomOf : SqZero.Hom (sqzEOf C M) (sqzEOf C N) :=
  sqzHom C f.hom (card_sqz_lt M) (card_sqz_lt N)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The map of thickenings `C[M] → C[N]` is the identity on the base `C`. -/
theorem sqzHom_bot_comp : (sqzHomOf f).bot.hom.hom.comp w = w := rfl

variable (a ι w) in
/-- **A chart lift pulls back to the chart lift of its image** along `C[M] → C[N]`. -/
theorem isPullback_sqzLift (ℓ : P.obj →ₐ[ringOf B S hS T'] (sqzAlgOf C M).obj)
    (hℓ : (sqzEOf C M).q.hom.hom.comp ℓ = w)
    (hℓ' : (sqzEOf C N).q.hom.hom.comp ((sqzHomOf f).top.hom.hom.comp ℓ) = w) :
    IsPullbackOfSquareZeroLift C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p (ξ a ι w)
      (ξ_obj a ι w) f (Quotient.mk _ (sqzLift a ι w M ℓ hℓ))
      (Quotient.mk _ (sqzLift a ι w N _ hℓ')) := by
  refine ⟨sqzLift a ι w M ℓ hℓ, sqzLift a ι w N _ hℓ', rfl, rfl,
    trans a ι (sqzHomOf f).top ℓ, ?_, ?_⟩
  · exact isStronglyCartesian_of_heq 𝒳.val.p (squareZeroOver_eq_specOver C N).symm
      (squareZeroOver_eq_specOver C M).symm (squareZeroOverMap_heq C f).symm
      (trans_isStronglyCartesian a ι _ ℓ)
  · exact liftArrow_comp_trans a ι w (sqzHomOf f).top (by
      rw [(sqzHomOf f).w]; exact Category.comp_id _) ℓ hℓ hℓ'

/-- `modMap` of `C[M] → C[N]` on the class of a derivation `D`: the class of
`f ∘ (ℓ₀ + D) - ℓ₀`. -/
theorem modMap_sqzHom_mk (D : P.obj →ₗ[ringOf B S hS T'] (sqzAlgOf C M).obj)
    (hD : D ∈ Der (sqzEOf C M) w) :
    modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f) (mkMod D hD) =
      mkMod (((sqzHomOf f).top.hom.hom.comp (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))).toLinearMap -
        (ℓ₀ w N).toLinearMap) (sub_mem_Der (ℓ₀_reduce w N)
          (by rw [SqZero.Hom.w_comp, addLift_reduce]; rfl)) := by
  rw [modMap_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ ?_))
  simp only [postcomp_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    addLift_apply]
  exact Eq.symm ((congrArg (· - (sqzInl C N.obj (card_sqz_lt N)) (w x))
    (sqzMap_inl_add C f.hom (card_sqz_lt M) (card_sqz_lt N) (w x) (D x))).trans
      (add_sub_cancel_left _ _))

variable (M) in
include hrel ha hι in
/-- **The identification `T_{ξ w}(M) ≃ Mod w` is natural in `M`.** -/
theorem tangentToMod_map (z : (F.functor.obj M : Type _)) :
    tangentToMod N hrel ha hι F (F.functor.map f z) =
      modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f)
        (tangentToMod M hrel ha hι F z) := by
  suffices key : ∀ m, tangentToMod M hrel ha hι F z = m →
      tangentToMod N hrel ha hι F (F.functor.map f z) =
        modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f) m from
    key _ rfl
  intro m hm
  induction m using Submodule.Quotient.induction_on with
  | H D' =>
  obtain ⟨D, hD⟩ := D'
  have hL := liftEquiv_eq_of_tangentToMod M hrel ha hι F hD hm
  have hℓ' : (sqzEOf C N).q.hom.hom.comp ((sqzHomOf f).top.hom.hom.comp
      (addLift D hD (ℓ₀ w M) (ℓ₀_reduce w M))) = w := by
    rw [SqZero.Hom.w_comp, addLift_reduce]; rfl
  have hu := isPullbackOfSquareZeroLift_unique C.obj B S hS (toSOf C) (contains_spec C) 𝒳.val.p
    (ξ a ι w) (ξ_obj a ι w) 𝒳.property f (hL ▸ F.liftEquiv_natural f z)
    (isPullback_sqzLift a ι w f _ (addLift_reduce D hD (ℓ₀ w M) (ℓ₀_reduce w M)) hℓ')
  exact (tangentToMod_of_liftEquiv N hrel ha hι F hℓ' hu).trans (modMap_sqzHom_mk f D hD).symm

/-- `modMap` of `C[M] → C[N]` is additive in the map of site modules. -/
theorem modMap_sqzHom_add (g : M ⟶ N) (m : Mod (stackGroupoid a ι) (sqzEOf C M) w) :
    modMap (G := stackGroupoid a ι) (sqzHomOf (f + g)) (sqzHom_bot_comp (w := w) (f + g)) m =
      modMap (G := stackGroupoid a ι) (sqzHomOf f) (sqzHom_bot_comp (w := w) f) m +
        modMap (G := stackGroupoid a ι) (sqzHomOf g) (sqzHom_bot_comp (w := w) g) m := by
  induction m using Submodule.Quotient.induction_on with
  | H D' =>
  obtain ⟨D, hD⟩ := D'
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ ?_))).trans
    (Submodule.Quotient.mk_add _)
  exact tsze_map_add_apply f.hom.hom g.hom.hom (D x) (hD.1 x)

/-- `modMap` of `C[M] → C[M]` induced by `c • 𝟙 M` is multiplication by `(c, 0)`. -/
theorem modMap_sqzHom_smul (c : C.obj) (m : Mod (stackGroupoid a ι) (sqzEOf C M) w) :
    modMap (G := stackGroupoid a ι) (sqzHomOf (c • 𝟙 M)) (sqzHom_bot_comp (w := w) (c • 𝟙 M)) m =
      sqzInl C M.obj (card_sqz_lt M) c • m := by
  induction m using Submodule.Quotient.induction_on with
  | H D' =>
  obtain ⟨D, hD⟩ := D'
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ ?_))).trans
    (Submodule.Quotient.mk_smul _ _ _)
  exact tsze_map_smul_apply c (D x) (hD.1 x)

end Natural

include hrel ha hι in
/-- **The identification of the tangent module at a chart point with `Mod w` is additive.** -/
theorem tangentToMod_add (z₁ z₂ : (F.functor.obj M : Type _)) :
    tangentToMod M hrel ha hι F (z₁ + z₂) =
      tangentToMod M hrel ha hι F z₁ + tangentToMod M hrel ha hι F z₂ := by
  have := F.additive
  refine (exists_sum_siteModuleProd (contains_spec C) F.functor z₁ z₂).elim fun z hz ↦ ?_
  have e (f : siteModuleProd C.obj B (contains_spec C) M M ⟶ M) :=
    tangentToMod_map (hrel := hrel) (ha := ha) (hι := hι) (F := F)
      (M := siteModuleProd C.obj B (contains_spec C) M M) f z
  have e₃ := modMap_sqzHom_add (a := a) (ι := ι) (w := w)
    (siteModuleFst C.obj B (contains_spec C) M M) (siteModuleSnd C.obj B (contains_spec C) M M)
    (tangentToMod (siteModuleProd C.obj B (contains_spec C) M M) hrel ha hι F z)
  exact (congrArg (tangentToMod M hrel ha hι F) hz.2.2.symm).trans ((e _).trans (e₃.trans
    (congrArg₂ (· + ·) ((congrArg (tangentToMod M hrel ha hι F) hz.1.symm).trans (e _)).symm
      ((congrArg (tangentToMod M hrel ha hι F) hz.2.1.symm).trans (e _)).symm)))

include hrel ha hι in
/-- **The identification of the tangent module at a chart point with `Mod w` is semilinear**
along `C → C[M]`. -/
theorem tangentToMod_smul (c : C.obj) (z : (F.functor.obj M : Type _)) :
    tangentToMod M hrel ha hι F (c • z) =
      sqzInl C M.obj (card_sqz_lt M) c • tangentToMod M hrel ha hι F z := by
  have := F.additive
  have := F.linear
  have hF : F.functor.map (c • (𝟙 M)) z = c • z := by
    rw [Functor.map_smul, F.functor.map_id]
    rfl
  rw [← hF, tangentToMod_map, modMap_sqzHom_smul]

end Bridge

end Deformation.Artin.ChartLift

end
