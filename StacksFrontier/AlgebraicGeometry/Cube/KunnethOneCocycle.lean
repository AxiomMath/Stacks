module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.LinearAlgebra.TensorProduct.DoubleCechDegreeOne

/-!
# Künneth injectivity in degree one, as explicit cocycles

Let `X` and `Y` be proper geometrically integral schemes over a field `K` with `K`-points `x` and
`y`, and let `Q` be a fibre product `X ×_K Y` (any cartesian square). For finite affine open
covers `U` of `X` and `V` of `Y`, `Q` is covered by the boxes `W (a, b) = U_a × V_b`. This file
proves that a Čech `1`-cocycle of `𝒪_Q` for that cover whose restrictions to the two faces
`X × {y}` and `{x} × Y` are coboundaries is a coboundary: the injectivity of
`H¹(X ×_K Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` used by [Stacks, Tag 0BF3] (cf. [Stacks, Tag 0BED]).

## Main results

* `AlgebraicGeometry.Cube.kunneth_bijective`: for affine opens `A ⊆ X` and `B ⊆ Y`,
  `Γ(A) ⊗_K Γ(B) → Γ(A × B)`, `s ⊗ t ↦ p^* s · q^* t`, is bijective.
* `AlgebraicGeometry.Cube.exists_coboundary_of_faces`: the degree-one statement above.

## Implementation notes

The cover of `Q` by boxes and its intersections are boxes of intersections, and on each of them
the sections are a tensor product (`kunneth_bijective`, from
`AlgebraicGeometry.isPushout_appLE_of_isPullback`). Through these identifications the Čech
`1`-cocycle becomes a degree-one cocycle of the double complex `C(U) ⊗ C(V)` of `K`-vector
spaces, and `Stacks.DoubleCech.exists_eq_coboundary` applies: its two inputs on `X` and `Y` are
`Γ(X, 𝒪) = K = Γ(Y, 𝒪)` (Tag 0BUG, `exists_eq_algebraMap_of_compatible`), and its two face
conditions are the hypotheses, read through `pullA_faceX_kunneth` and `pullA_faceY_kunneth`.

Sections over an open are wrapped as `AlgebraicGeometry.Cube.Sec t U`, a synonym of `Γ(T, U)`
carrying the `K`-algebra structure of the structure morphism `t`, so that tensor products over
`K` of sections make sense without local instances.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry.Cube

variable {K : Type u} [Field K] {X Y Q : Scheme.{u}}

/-- The product `pX⁻¹ U ∩ pY⁻¹ V` of an open of `X` and an open of `Y` inside `Q`. -/
noncomputable def box (pX : Q ⟶ X) (pY : Q ⟶ Y) (U : X.Opens) (V : Y.Opens) : Q.Opens :=
  pX ⁻¹ᵁ U ⊓ pY ⁻¹ᵁ V

/-- The open `W (a, b) = pX⁻¹ U_a ∩ pY⁻¹ V_b` of `Q` for families of opens `U` and `V`. -/
noncomputable def W (pX : Q ⟶ X) (pY : Q ⟶ Y) {I J : Type*} (U : I → X.Opens)
    (V : J → Y.Opens) (s : I × J) : Q.Opens :=
  box pX pY (U s.1) (V s.2)

/-- A box lies over its first factor. -/
theorem box_le_fst (pX : Q ⟶ X) (pY : Q ⟶ Y) (U : X.Opens) (V : Y.Opens) :
    box pX pY U V ≤ pX ⁻¹ᵁ U :=
  inf_le_left

/-- A box lies over its second factor. -/
theorem box_le_snd (pX : Q ⟶ X) (pY : Q ⟶ Y) (U : X.Opens) (V : Y.Opens) :
    box pX pY U V ≤ pY ⁻¹ᵁ V :=
  inf_le_right

/-- Restriction of sections of a scheme along an inclusion of opens. -/
abbrev res {T : Scheme.{u}} {A B : T.Opens} (h : B ≤ A) (s : Γ(T, A)) : Γ(T, B) :=
  (T.presheaf.map (homOfLE h).op).hom s

/-- Restricting twice is restricting once. -/
theorem res_res {T : Scheme.{u}} {A B C : T.Opens} (h : B ≤ A) (h' : C ≤ B) (s : Γ(T, A)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction along an equality of opens is injective. -/
theorem res_injective_of_eq {T : Scheme.{u}} {A B : T.Opens} (h : B ≤ A) (e : A = B) :
    Function.Injective (res h : Γ(T, A) → Γ(T, B)) := by
  subst e
  intro s t hst
  simpa [res] using hst

/-- The sections of a `K`-scheme over an open, as a `K`-algebra through its structure morphism. -/
def Sec {T : Scheme.{u}} (_t : T ⟶ Spec (.of K)) (U : T.Opens) : Type u := Γ(T, U)

section Sec

variable {T : Scheme.{u}} (t : T ⟶ Spec (.of K))

/-- `Sec t U` is the commutative ring `Γ(T, U)`. -/
instance (U : T.Opens) : CommRing (Sec t U) := inferInstanceAs (CommRing Γ(T, U))

/-- The structure map `K → Γ(T, U)`. -/
noncomputable def structMap (U : T.Opens) : K →+* Γ(T, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ t.appLE ⊤ U (by simp)).hom

/-- The `K`-algebra structure of `Sec t U` given by the structure morphism. -/
noncomputable instance (U : T.Opens) : Algebra K (Sec t U) := (structMap t U).toAlgebra

/-- The structure map of `Sec t U` is `structMap t U`. -/
theorem algebraMap_sec (U : T.Opens) (k : K) :
    algebraMap K (Sec t U) k = structMap t U k := rfl

/-- Restriction of sections, as a map of `K`-algebras. -/
noncomputable def resA {A B : T.Opens} (h : B ≤ A) : Sec t A →ₐ[K] Sec t B where
  toRingHom := (T.presheaf.map (homOfLE h).op).hom
  commutes' k := by
    change (T.presheaf.map (homOfLE h).op).hom
      (((Scheme.ΓSpecIso (.of K)).inv ≫ t.appLE ⊤ A _).hom k) = _
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]
    rfl

/-- `resA` is restriction of sections. -/
theorem resA_apply {A B : T.Opens} (h : B ≤ A) (s : Sec t A) :
    resA t h s = res (T := T) h s := rfl

/-- Pulling back sections along a morphism over `K`, as a map of `K`-algebras. -/
noncomputable def pullA {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (φ : T' ⟶ T)
    (hφ : φ ≫ t = t') {A : T.Opens} {B : T'.Opens} (h : B ≤ φ ⁻¹ᵁ A) :
    Sec t A →ₐ[K] Sec t' B where
  toRingHom := (φ.appLE A B h).hom
  commutes' k := by
    subst hφ
    change (φ.appLE A B h).hom (((Scheme.ΓSpecIso (.of K)).inv ≫ t.appLE ⊤ A _).hom k) = _
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE]
    rfl

/-- `pullA` is the map on sections of the morphism. -/
theorem pullA_apply {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (φ : T' ⟶ T)
    (hφ : φ ≫ t = t') {A : T.Opens} {B : T'.Opens} (h : B ≤ φ ⁻¹ᵁ A) (s : Sec t A) :
    pullA t t' φ hφ h s = (φ.appLE A B h).hom s := rfl

/-- Pulling back commutes with restriction. -/
theorem pullA_resA {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (φ : T' ⟶ T)
    (hφ : φ ≫ t = t') {A A' : T.Opens} {B B' : T'.Opens} (hA : A' ≤ A) (hB : B' ≤ B)
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A') (s : Sec t A) :
    pullA t t' φ hφ h' (resA t hA s) = resA t' hB (pullA t t' φ hφ h s) := by
  change (T.presheaf.map (homOfLE hA).op ≫ φ.appLE A' B' h').hom s =
    (φ.appLE A B h ≫ T'.presheaf.map (homOfLE hB).op).hom s
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- Restricting twice is restricting once. -/
theorem resA_resA {A B C : T.Opens} (h : B ≤ A) (h' : C ≤ B) (s : Sec t A) :
    resA t h' (resA t h s) = resA t (h'.trans h) s :=
  res_res h h' s

end Sec

section Helpers

variable {T : Scheme.{u}} (t : T ⟶ Spec (.of K))

/-- Restriction to the same open is the identity. -/
theorem resA_refl {A : T.Opens} (s : Sec t A) : resA t (le_refl A) s = s := by
  change (T.presheaf.map (𝟙 (Opposite.op A))).hom s = s
  rw [T.presheaf.map_id]
  rfl

/-- Restriction to the same open is the identity algebra map. -/
private theorem resA_refl_eq_id {A : T.Opens} : resA t (le_refl A) = AlgHom.id K _ :=
  AlgHom.ext (resA_refl t)

/-- Pulling back along equal morphisms gives the same sections. -/
theorem pullA_congr {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) {φ φ' : T' ⟶ T}
    (hφ : φ ≫ t = t') (e : φ = φ') {A : T.Opens} {B : T'.Opens} (h : B ≤ φ ⁻¹ᵁ A)
    (s : Sec t A) :
    pullA t t' φ hφ h s = pullA t t' φ' (e ▸ hφ) (e ▸ h) s := by
  subst e
  rfl

/-- Pulling back along the identity is restriction. -/
theorem pullA_id {A B : T.Opens} (h : B ≤ (𝟙 T) ⁻¹ᵁ A) (s : Sec t A) :
    pullA t t (𝟙 T) (Category.id_comp t) h s = resA t h s :=
  rfl

/-- Pulling back twice is pulling back along the composite. -/
theorem pullA_pullA {T' T'' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (t'' : T'' ⟶ Spec (.of K))
    (φ : T' ⟶ T) (ψ : T'' ⟶ T') (hφ : φ ≫ t = t') (hψ : ψ ≫ t' = t'') {A : T.Opens}
    {B : T'.Opens} {C : T''.Opens} (h : B ≤ φ ⁻¹ᵁ A) (h' : C ≤ ψ ⁻¹ᵁ B) (s : Sec t A) :
    pullA t' t'' ψ hψ h' (pullA t t' φ hφ h s) =
      pullA t t'' (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ])
        (h'.trans ((TopologicalSpace.Opens.map ψ.base).map (homOfLE h)).le) s := by
  change (φ.appLE A B h ≫ ψ.appLE B C h').hom s = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Pulling back preserves the constants `K`. -/
theorem pullA_algebraMap {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (φ : T' ⟶ T)
    (hφ : φ ≫ t = t') {A : T.Opens} {B : T'.Opens} (h : B ≤ φ ⁻¹ᵁ A) (k : K) :
    pullA t t' φ hφ h (algebraMap K _ k) = algebraMap K _ k :=
  (pullA t t' φ hφ h).commutes k

/-- On a separated `K`-scheme the intersection of two affine opens is affine. -/
theorem isAffineOpen_inf [IsSeparated t] {A B : T.Opens} (hA : IsAffineOpen A)
    (hB : IsAffineOpen B) : IsAffineOpen (A ⊓ B) :=
  (isAffineHom_diagonal_iff (f := t)).mp inferInstance ⊤ (isAffineOpen_top _) A (by simp) B
    (by simp) hA hB

/-- **A compatible family of sections of a proper geometrically integral `K`-scheme over an open
cover is a constant.** It glues to a global section, and the global sections are `K`
(Tag 0BUG). -/
theorem exists_eq_algebraMap_of_compatible [IsProper t] [GeometricallyIntegral t] {I : Type*}
    (A : I → T.Opens) (hA : (⊤ : T.Opens) = ⨆ i, A i) (e : ∀ i, Sec t (A i))
    (h : ∀ i j, resA t (inf_le_left : A i ⊓ A j ≤ A i) (e i) = resA t inf_le_right (e j)) :
    ∃ k : K, ∀ i, e i = algebraMap K _ k := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf A ⊤
    (fun i => homOfLE le_top) hA.le e (fun i j => h i j)
  have := isIso_globalSections_of_geometricallyIntegral K t
  obtain ⟨k, hk⟩ :=
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of K)).inv ≫ t.appTop)).2 s
  refine ⟨k, fun i => ?_⟩
  rw [← hs i, ← hk]
  rfl

/-- The identification `Γ(Spec K, 𝒪) = K`, as a map of `K`-algebras. -/
noncomputable def evalSpec : Sec (𝟙 (Spec (.of K))) ⊤ →ₐ[K] K where
  toRingHom := (Scheme.ΓSpecIso (.of K)).hom.hom
  commutes' k := by
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).presheaf.map (𝟙 _) ≫
      (Scheme.ΓSpecIso (.of K)).hom).hom k = k
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
    rfl

/-- Every section of `Spec K` is the constant it evaluates to. -/
theorem algebraMap_evalSpec (w : Sec (𝟙 (Spec (.of K))) ⊤) :
    algebraMap K _ (evalSpec w) = w := by
  change ((Scheme.ΓSpecIso (.of K)).hom ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec (.of K)).presheaf.map (𝟙 _)).hom w = w
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id]
  rfl

/-- Evaluation of sections at a `K`-point. -/
noncomputable def evalAt (x : Spec (.of K) ⟶ T) (hx : x ≫ t = 𝟙 _) {A : T.Opens}
    (hA : ⊤ ≤ x ⁻¹ᵁ A) : Sec t A →ₐ[K] K :=
  evalSpec.comp (pullA t (𝟙 _) x hx hA)

/-- Pulling back along `T' ⟶ Spec K ⟶ T` through a `K`-point is evaluation at the point. -/
theorem pullA_comp_point {T' : Scheme.{u}} (t' : T' ⟶ Spec (.of K)) (x : Spec (.of K) ⟶ T)
    (hx : x ≫ t = 𝟙 _) {A : T.Opens} (hA : ⊤ ≤ x ⁻¹ᵁ A) {B : T'.Opens}
    (h : B ≤ (t' ≫ x) ⁻¹ᵁ A) (s : Sec t A) :
    pullA t t' (t' ≫ x) (by rw [Category.assoc, hx, Category.comp_id]) h s =
      algebraMap K _ (evalAt t x hx hA s) := by
  have := pullA_pullA t (𝟙 _) t' x t' hx (Category.comp_id t') (C := B) hA (by simp) s
  rw [← pullA_congr _ _ _ rfl] at this
  rw [← this, evalAt, AlgHom.comp_apply, ← pullA_algebraMap (𝟙 _) t' t' (Category.comp_id t')
    (show B ≤ t' ⁻¹ᵁ ⊤ by simp), algebraMap_evalSpec]

end Helpers

section Cech

variable {T : Scheme.{u}} (t : T ⟶ Spec (.of K)) {I : Type*} (U : I → T.Opens)

/-- The Čech differential `C⁰ → C¹` of `𝒪` on a family of opens. -/
noncomputable def cechD₀ : (∀ a, Sec t (U a)) →ₗ[K] ∀ p : I × I, Sec t (U p.1 ⊓ U p.2) :=
  LinearMap.pi fun p => (resA t (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)).toLinearMap ∘ₗ
    LinearMap.proj p.2 - (resA t (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).toLinearMap ∘ₗ
    LinearMap.proj p.1

/-- The Čech differential `C¹ → C²` of `𝒪` on a family of opens. -/
noncomputable def cechD₁ : (∀ p : I × I, Sec t (U p.1 ⊓ U p.2)) →ₗ[K]
    ∀ q : I × I × I, Sec t (U q.1 ⊓ U q.2.1 ⊓ U q.2.2) :=
  LinearMap.pi fun q =>
    (resA t (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.2.1 ⊓ U q.2.2)).toLinearMap ∘ₗ
        LinearMap.proj (q.2.1, q.2.2) -
      (resA t (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.1 ⊓ U q.2.2)).toLinearMap ∘ₗ
        LinearMap.proj (q.1, q.2.2) +
      (resA t (inf_le_left : U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.1 ⊓ U q.2.1)).toLinearMap ∘ₗ
        LinearMap.proj (q.1, q.2.1)

/-- A component of `cechD₀`. -/
theorem proj_comp_cechD₀ (p : I × I) :
    LinearMap.proj p ∘ₗ cechD₀ t U =
      (resA t (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)).toLinearMap ∘ₗ LinearMap.proj p.2 -
        (resA t (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).toLinearMap ∘ₗ LinearMap.proj p.1 :=
  rfl

/-- A component of `cechD₁`. -/
theorem proj_comp_cechD₁ (q : I × I × I) :
    LinearMap.proj q ∘ₗ cechD₁ t U =
      (resA t (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.2.1 ⊓ U q.2.2)).toLinearMap ∘ₗ
          LinearMap.proj (q.2.1, q.2.2) -
        (resA t (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.1 ⊓ U q.2.2)).toLinearMap ∘ₗ
          LinearMap.proj (q.1, q.2.2) +
        (resA t (inf_le_left : U q.1 ⊓ U q.2.1 ⊓ U q.2.2 ≤ U q.1 ⊓ U q.2.1)).toLinearMap ∘ₗ
          LinearMap.proj (q.1, q.2.1) :=
  rfl

/-- The Čech differentials compose to zero. -/
theorem cechD₁_comp_cechD₀ : cechD₁ t U ∘ₗ cechD₀ t U = 0 := by
  refine LinearMap.ext fun e => funext fun q => ?_
  simp only [cechD₁, cechD₀, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.coe_proj, Function.eval, AlgHom.toLinearMap_apply,
    map_sub, resA_resA, LinearMap.zero_apply, Pi.zero_apply]
  abel

/-- The constant family `1` is a Čech `0`-cocycle. -/
theorem cechD₀_one : cechD₀ t U (fun _ => 1) = 0 := by
  funext p
  simp [cechD₀]

/-- On a proper geometrically integral `K`-scheme, a Čech `0`-cocycle for an open cover is a
constant. -/
theorem exists_eq_smul_of_cechD₀_eq_zero [IsProper t] [GeometricallyIntegral t]
    (hU : (⊤ : T.Opens) = ⨆ a, U a) (e : ∀ a, Sec t (U a)) (he : cechD₀ t U e = 0) :
    ∃ k : K, e = k • fun _ => 1 := by
  obtain ⟨k, hk⟩ := exists_eq_algebraMap_of_compatible t U hU e fun a a' => by
    have := congrFun he (a, a')
    simp only [cechD₀, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.coe_proj, Function.eval, AlgHom.toLinearMap_apply, Pi.zero_apply,
      sub_eq_zero] at this
    exact this.symm
  exact ⟨k, funext fun a => by simp [hk a, Algebra.smul_def]⟩

/-- A Čech `1`-cocycle identity restricts to any smaller open. -/
theorem resA_cocycle_of_le {ι : Type*} {A : ι → T.Opens} {c : ∀ s s', Sec t (A s ⊓ A s')}
    (hc : ∀ s s' r, resA t (inf_le_left : A s ⊓ A s' ⊓ A r ≤ _) (c s s') +
        resA t (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c s' r) =
      resA t (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c s r))
    (s s' r : ι) (O : T.Opens) (hO : O ≤ A s ⊓ A s' ⊓ A r) :
    resA t (hO.trans inf_le_left) (c s s') +
        resA t (hO.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (c s' r) =
      resA t (hO.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (c s r) := by
  have := congrArg (resA t hO) (hc s s' r)
  rwa [map_add, resA_resA, resA_resA, resA_resA] at this

end Cech

section Square

variable {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {pX : Q ⟶ X} {pY : Q ⟶ Y}

/-- **The Künneth map on a box**, followed by restriction to an open `O` of the box:
`s ⊗ t ↦ (p^* s · q^* t)|_O`. -/
noncomputable def kunneth (hw : pX ≫ f = pY ≫ g) (U : X.Opens) (V : Y.Opens) (O : Q.Opens)
    (hO : O ≤ box pX pY U V) : Sec f U ⊗[K] Sec g V →ₐ[K] Sec (pX ≫ f) O :=
  Algebra.TensorProduct.lift
    (pullA f (pX ≫ f) pX rfl (hO.trans (box_le_fst pX pY U V)))
    (pullA g (pX ≫ f) pY hw.symm
      (hO.trans (box_le_snd pX pY U V)))
    fun _ _ => Commute.all _ _

/-- The Künneth map on a pure tensor. -/
theorem kunneth_tmul (hw : pX ≫ f = pY ≫ g) (U : X.Opens) (V : Y.Opens) (O : Q.Opens)
    (hO : O ≤ box pX pY U V) (s : Sec f U) (t : Sec g V) :
    kunneth hw U V O hO (s ⊗ₜ t) =
      pullA f (pX ≫ f) pX rfl (hO.trans (box_le_fst pX pY U V)) s *
        pullA g (pX ≫ f) pY hw.symm
          (hO.trans (box_le_snd pX pY U V)) t :=
  rfl

/-- **Naturality of the Künneth map** in restrictions. -/
theorem kunneth_map (hw : pX ≫ f = pY ≫ g) {U U' : X.Opens} {V V' : Y.Opens} {O O' : Q.Opens}
    (hO : O ≤ box pX pY U V) (hO' : O' ≤ box pX pY U' V') (hU : U' ≤ U) (hV : V' ≤ V)
    (h : O' ≤ O) (z : Sec f U ⊗[K] Sec g V) :
    kunneth hw U' V' O' hO' (Algebra.TensorProduct.map (resA f hU) (resA g hV) z) =
      resA (pX ≫ f) h (kunneth hw U V O hO z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
    rw [Algebra.TensorProduct.map_tmul, kunneth_tmul, kunneth_tmul, map_mul, pullA_resA _ _ _ _
      hU h, pullA_resA _ _ _ _ hV h]

/-- **The Künneth map is bijective on a product of affine opens.** -/
theorem kunneth_bijective (hsq : IsPullback pX pY f g) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (O : Q.Opens) (hO : O = box pX pY U V) :
    Function.Bijective (kunneth hsq.w U V O hO.le) := by
  have hw := hsq.w
  let : Algebra (Sec f U) (Sec (pX ≫ f) O) :=
    (pullA f (pX ≫ f) pX rfl (hO.le.trans (box_le_fst pX pY U V))).toAlgebra
  let : Algebra (Sec g V) (Sec (pX ≫ f) O) :=
    (pullA g (pX ≫ f) pY hw.symm
      (hO.le.trans (box_le_snd pX pY U V))).toAlgebra
  have : IsScalarTower K (Sec f U) (Sec (pX ≫ f) O) :=
    IsScalarTower.of_algebraMap_eq fun k =>
      ((pullA f (pX ≫ f) pX rfl _).commutes k).symm
  have : IsScalarTower K (Sec g V) (Sec (pX ≫ f) O) :=
    IsScalarTower.of_algebraMap_eq fun k =>
      ((pullA g (pX ≫ f) pY hw.symm _).commutes k).symm
  have H := isPushout_appLE_of_isPullback hsq
    (isAffineOpen_top (Spec (.of K))) hU (by simp) hV (by simp) hO
  have H' : IsPushout (CommRingCat.ofHom (algebraMap K (Sec f U)))
      (CommRingCat.ofHom (algebraMap K (Sec g V)))
      (CommRingCat.ofHom (algebraMap (Sec f U) (Sec (pX ≫ f) O)))
      (CommRingCat.ofHom (algebraMap (Sec g V) (Sec (pX ≫ f) O))) :=
    H.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by ext; simp [algebraMap_sec, structMap]; rfl)
      (by ext; simp [algebraMap_sec, structMap]; rfl)
      (by ext; rfl) (by ext; rfl)
  have : Algebra.IsPushout K (Sec f U) (Sec g V) (Sec (pX ≫ f) O) :=
    (CommRingCat.isPushout_iff_isPushout (R := K) (R' := Sec f U) (S := Sec g V)
      (S' := Sec (pX ≫ f) O)).mp H'
  have heq : ⇑(kunneth hsq.w U V O hO.le) =
      ⇑(Algebra.IsPushout.equiv K (Sec f U) (Sec g V) (Sec (pX ≫ f) O)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s t => rw [Algebra.IsPushout.equiv_tmul]; rfl
  rw [heq]
  exact (Algebra.IsPushout.equiv K (Sec f U) (Sec g V) (Sec (pX ≫ f) O)).bijective

section Faces

variable (hsq : IsPullback pX pY f g)

/-- The face `X ≅ X × {y}` of `Q = X ×_K Y` through a `K`-point `y` of `Y`. -/
noncomputable def faceX (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) : X ⟶ Q :=
  hsq.lift (𝟙 X) (f ≫ y) (by rw [Category.id_comp, Category.assoc, hy, Category.comp_id])

/-- The face `Y ≅ {x} × Y` of `Q = X ×_K Y` through a `K`-point `x` of `X`. -/
noncomputable def faceY (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) : Y ⟶ Q :=
  hsq.lift (g ≫ x) (𝟙 Y) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id])

/-- The face `X × {y}` is a section of the first projection. -/
theorem faceX_fst (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) : faceX hsq y hy ≫ pX = 𝟙 X :=
  hsq.lift_fst _ _ _

/-- The face `X × {y}` maps to `Y` through `y`. -/
theorem faceX_snd (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) : faceX hsq y hy ≫ pY = f ≫ y :=
  hsq.lift_snd _ _ _

/-- The face `{x} × Y` maps to `X` through `x`. -/
theorem faceY_fst (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) : faceY hsq x hx ≫ pX = g ≫ x :=
  hsq.lift_fst _ _ _

/-- The face `{x} × Y` is a section of the second projection. -/
theorem faceY_snd (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) : faceY hsq x hx ≫ pY = 𝟙 Y :=
  hsq.lift_snd _ _ _

/-- The face `X × {y}` is a morphism over `K`. -/
theorem faceX_pr (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) : faceX hsq y hy ≫ pX ≫ f = f := by
  rw [← Category.assoc, faceX_fst, Category.id_comp]

/-- The face `{x} × Y` is a morphism over `K`. -/
theorem faceY_pr (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) : faceY hsq x hx ≫ pX ≫ f = g := by
  rw [← Category.assoc, faceY_fst, Category.assoc, hx, Category.comp_id]

/-- The face `X × {y}` meets a box `A × B` with `y ∈ B` in `A`. -/
theorem le_faceX_preimage (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) {A : X.Opens}
    {B : Y.Opens} (hB : Set.range y ⊆ B) : A ≤ faceX hsq y hy ⁻¹ᵁ box pX pY A B := by
  intro p hp
  refine ⟨?_, ?_⟩
  · change (faceX hsq y hy ≫ pX) p ∈ A
    rw [faceX_fst hsq]
    exact hp
  · change (faceX hsq y hy ≫ pY) p ∈ B
    rw [faceX_snd hsq]
    exact hB ⟨_, rfl⟩

/-- The face `{x} × Y` meets a box `A × B` with `x ∈ A` in `B`. -/
theorem le_faceY_preimage (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) {A : X.Opens}
    {B : Y.Opens} (hA : Set.range x ⊆ A) : B ≤ faceY hsq x hx ⁻¹ᵁ box pX pY A B := by
  intro p hp
  refine ⟨?_, ?_⟩
  · change (faceY hsq x hx ≫ pX) p ∈ A
    rw [faceY_fst hsq]
    exact hA ⟨_, rfl⟩
  · change (faceY hsq x hx ≫ pY) p ∈ B
    rw [faceY_snd hsq]
    exact hp

/-- A `K`-point lands in an open containing its image. -/
theorem top_le_preimage_of_range {T : Scheme.{u}} (x : Spec (.of K) ⟶ T) {A : T.Opens}
    (hA : Set.range x ⊆ A) : ⊤ ≤ x ⁻¹ᵁ A :=
  fun p _ => hA ⟨p, rfl⟩

/-- **The Künneth map restricted to the face `X × {y}`** is evaluation of the second factor
at `y`. -/
theorem pullA_faceX_kunneth (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) {A A' : X.Opens}
    {B : Y.Opens} (hB : Set.range y ⊆ B) {O : Q.Opens} (hO : O ≤ box pX pY A B)
    (hA' : A' ≤ faceX hsq y hy ⁻¹ᵁ O) (hA'A : A' ≤ A) (z : Sec f A ⊗[K] Sec g B) :
    pullA (pX ≫ f) f (faceX hsq y hy) (faceX_pr hsq y hy) hA' (kunneth hsq.w A B O hO z) =
      resA f hA'A (TensorProduct.rid K _
        (LinearMap.lTensor _ (evalAt g y hy (top_le_preimage_of_range y hB)).toLinearMap z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s t =>
    rw [kunneth_tmul, map_mul, pullA_pullA, pullA_pullA,
      pullA_congr _ _ _ (faceX_fst hsq y hy), pullA_id,
      pullA_congr _ _ _ (faceX_snd hsq y hy),
      pullA_comp_point g f y hy (top_le_preimage_of_range y hB)]
    simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.rid_tmul,
      Algebra.smul_def, AlgHom.commutes, map_mul]
    exact mul_comm (G := Sec f A') _ _

/-- **The Künneth map restricted to the face `{x} × Y`** is evaluation of the first factor
at `x`. -/
theorem pullA_faceY_kunneth (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) {A : X.Opens}
    {B B' : Y.Opens} (hA : Set.range x ⊆ A) {O : Q.Opens} (hO : O ≤ box pX pY A B)
    (hB' : B' ≤ faceY hsq x hx ⁻¹ᵁ O) (hB'B : B' ≤ B) (z : Sec f A ⊗[K] Sec g B) :
    pullA (pX ≫ f) g (faceY hsq x hx) (faceY_pr hsq x hx) hB' (kunneth hsq.w A B O hO z) =
      resA g hB'B (TensorProduct.lid K _
        (LinearMap.rTensor _ (evalAt f x hx (top_le_preimage_of_range x hA)).toLinearMap z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s t =>
    rw [kunneth_tmul, map_mul, pullA_pullA, pullA_pullA,
      pullA_congr _ _ _ (faceY_fst hsq x hx),
      pullA_comp_point f g x hx (top_le_preimage_of_range x hA),
      pullA_congr _ _ _ (faceY_snd hsq x hx), pullA_id]
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.lid_tmul,
      Algebra.smul_def, AlgHom.commutes, map_mul]
    rfl

end Faces

section Families

/-- **The Künneth map on a family of boxes**: `(∏ᵢ Γ(Aᵢ)) ⊗ Γ(B) → ∏ᵢ Γ(Oᵢ)`. -/
noncomputable def kunnethPi (hw : pX ≫ f = pY ≫ g) {ι : Type*} (A : ι → X.Opens) (B : Y.Opens)
    (O : ι → Q.Opens) (hO : ∀ i, O i ≤ box pX pY (A i) B) :
    (∀ i, Sec f (A i)) ⊗[K] Sec g B →ₗ[K] ∀ i, Sec (pX ≫ f) (O i) :=
  LinearMap.pi fun i => (kunneth hw (A i) B (O i) (hO i)).toLinearMap ∘ₗ
    LinearMap.rTensor _ (LinearMap.proj i)

/-- The components of `kunnethPi` are Künneth maps. -/
theorem kunnethPi_apply (hw : pX ≫ f = pY ≫ g) {ι : Type*} (A : ι → X.Opens) (B : Y.Opens)
    (O : ι → Q.Opens) (hO : ∀ i, O i ≤ box pX pY (A i) B)
    (z : (∀ i, Sec f (A i)) ⊗[K] Sec g B) (i : ι) :
    kunnethPi hw A B O hO z i =
      kunneth hw (A i) B (O i) (hO i) (LinearMap.rTensor _ (LinearMap.proj i) z) :=
  rfl

/-- **The family Künneth map is bijective** on a finite family of products of affine opens. -/
theorem kunnethPi_bijective (hsq : IsPullback pX pY f g) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → X.Opens)
    (B : Y.Opens) (O : ι → Q.Opens) (hA : ∀ i, IsAffineOpen (A i))
    (hB : IsAffineOpen B) (hO : ∀ i, O i = box pX pY (A i) B) :
    Function.Bijective (kunnethPi hsq.w A B O fun i => (hO i).le) := by
  let e : ∀ i, (Sec f (A i) ⊗[K] Sec g B) ≃ₗ[K] Sec (pX ≫ f) (O i) := fun i =>
    LinearEquiv.ofBijective (kunneth hsq.w (A i) B (O i) (hO i).le).toLinearMap
      (kunneth_bijective hsq (hA i) hB (O i) (hO i))
  have : kunnethPi hsq.w A B O (fun i => (hO i).le) =
      ((LinearEquiv.piCongrRight e).toLinearMap ∘ₗ (TensorProduct.piLeft ..).toLinearMap) := by
    apply TensorProduct.ext'
    intro m n
    funext i
    simp [kunnethPi_apply, e]
    rfl
  rw [this]
  exact ((TensorProduct.piLeft ..).trans (LinearEquiv.piCongrRight e)).bijective

/-- The Künneth map is natural in restriction along the first factor. -/
theorem kunneth_rTensor (hw : pX ≫ f = pY ≫ g) {A A' : X.Opens} {B : Y.Opens} {O O' : Q.Opens}
    (hO : O ≤ box pX pY A B) (hO' : O' ≤ box pX pY A' B) (hA : A' ≤ A) (h : O' ≤ O)
    (w : Sec f A ⊗[K] Sec g B) :
    kunneth hw A' B O' hO' (LinearMap.rTensor _ (resA f hA).toLinearMap w) =
      resA (pX ≫ f) h (kunneth hw A B O hO w) := by
  have := kunneth_map hw hO hO' hA (le_refl B) h w
  rwa [resA_refl_eq_id] at this

/-- The Künneth map is natural in restriction along the second factor. -/
theorem kunneth_lTensor (hw : pX ≫ f = pY ≫ g) {A : X.Opens} {B B' : Y.Opens} {O O' : Q.Opens}
    (hO : O ≤ box pX pY A B) (hO' : O' ≤ box pX pY A B') (hB : B' ≤ B) (h : O' ≤ O)
    (w : Sec f A ⊗[K] Sec g B) :
    kunneth hw A B' O' hO' (LinearMap.lTensor _ (resA g hB).toLinearMap w) =
      resA (pX ≫ f) h (kunneth hw A B O hO w) := by
  have := kunneth_map hw hO hO' (le_refl A) hB h w
  rwa [resA_refl_eq_id] at this

end Families

section Components

/-- A component of `kunnethPi` after a restriction of one factor of the first product. -/
theorem kunnethPi_rTensor_comp (hw : pX ≫ f = pY ≫ g) {ι : Type*} (A : ι → X.Opens) (B : Y.Opens)
    (O : ι → Q.Opens) (hO : ∀ i, O i ≤ box pX pY (A i) B) {A' : X.Opens}
    {O' : Q.Opens} (hO' : O' ≤ box pX pY A' B) (i : ι) (hA : A' ≤ A i)
    (h : O' ≤ O i) (z : (∀ i, Sec f (A i)) ⊗[K] Sec g B) :
    kunneth hw A' B O' hO'
        (LinearMap.rTensor _ ((resA f hA).toLinearMap ∘ₗ LinearMap.proj i) z) =
      resA (pX ≫ f) h (kunnethPi hw A B O hO z i) := by
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, kunneth_rTensor hw (hO i) hO' hA h,
    kunnethPi_apply]

/-- `kunnethPi` turns the Čech differential `cechD₀` of the first factor into the difference of
restrictions. -/
theorem kunnethPi_rTensor_cechD₀ (hw : pX ≫ f = pY ≫ g) {I : Type*} (U : I → X.Opens)
    {B : Y.Opens} (A' : I × I → Q.Opens) (hA' : ∀ p, A' p ≤ box pX pY (U p.1 ⊓ U p.2) B)
    (O : I → Q.Opens) (hO : ∀ a, O a ≤ box pX pY (U a) B)
    (h₂ : ∀ p, A' p ≤ O p.2) (h₁ : ∀ p, A' p ≤ O p.1) (z : (∀ a, Sec f (U a)) ⊗[K] Sec g B)
    (p : I × I) :
    kunnethPi hw (fun p : I × I => U p.1 ⊓ U p.2) B A' hA'
        (LinearMap.rTensor _ (cechD₀ f U) z) p =
      resA (pX ≫ f) (h₂ p) (kunnethPi hw U B O hO z p.2) -
        resA (pX ≫ f) (h₁ p) (kunnethPi hw U B O hO z p.1) := by
  rw [kunnethPi_apply, ← LinearMap.comp_apply (LinearMap.rTensor _ (LinearMap.proj p)),
    ← LinearMap.rTensor_comp, proj_comp_cechD₀, LinearMap.rTensor_sub, LinearMap.sub_apply,
    map_sub, kunnethPi_rTensor_comp hw U B O hO (hA' p) p.2 _ (h₂ p),
    kunnethPi_rTensor_comp hw U B O hO (hA' p) p.1 _ (h₁ p)]

/-- `kunnethPi` turns the Čech differential `cechD₁` of the first factor into the alternating sum
of restrictions. -/
theorem kunnethPi_rTensor_cechD₁ (hw : pX ≫ f = pY ≫ g) {I : Type*} (U : I → X.Opens)
    {B : Y.Opens} (A'' : I × I × I → Q.Opens)
    (hA'' : ∀ q, A'' q ≤ box pX pY (U q.1 ⊓ U q.2.1 ⊓ U q.2.2) B)
    (O : I × I → Q.Opens) (hO : ∀ p, O p ≤ box pX pY (U p.1 ⊓ U p.2) B)
    (h₁ : ∀ q, A'' q ≤ O (q.2.1, q.2.2)) (h₂ : ∀ q, A'' q ≤ O (q.1, q.2.2))
    (h₃ : ∀ q, A'' q ≤ O (q.1, q.2.1))
    (z : (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g B) (q : I × I × I) :
    kunnethPi hw (fun q : I × I × I => U q.1 ⊓ U q.2.1 ⊓ U q.2.2) B A'' hA''
        (LinearMap.rTensor _ (cechD₁ f U) z) q =
      resA (pX ≫ f) (h₁ q) (kunnethPi hw (fun p : I × I => U p.1 ⊓ U p.2) B O hO z
          (q.2.1, q.2.2)) -
        resA (pX ≫ f) (h₂ q) (kunnethPi hw (fun p : I × I => U p.1 ⊓ U p.2) B O hO z
          (q.1, q.2.2)) +
        resA (pX ≫ f) (h₃ q) (kunnethPi hw (fun p : I × I => U p.1 ⊓ U p.2) B O hO z
          (q.1, q.2.1)) := by
  rw [kunnethPi_apply, ← LinearMap.comp_apply (LinearMap.rTensor _ (LinearMap.proj q)),
    ← LinearMap.rTensor_comp, proj_comp_cechD₁, LinearMap.rTensor_add, LinearMap.rTensor_sub,
    LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub,
    kunnethPi_rTensor_comp hw _ B O hO (hA'' q) (q.2.1, q.2.2) _ (h₁ q),
    kunnethPi_rTensor_comp hw _ B O hO (hA'' q) (q.1, q.2.2) _ (h₂ q),
    kunnethPi_rTensor_comp hw _ B O hO (hA'' q) (q.1, q.2.1) _ (h₃ q)]

/-- `kunnethPi` is natural in restriction along the second factor. -/
theorem kunnethPi_lTensor (hw : pX ≫ f = pY ≫ g) {ι : Type*} (A : ι → X.Opens) {B B' : Y.Opens}
    (O O' : ι → Q.Opens) (hO : ∀ i, O i ≤ box pX pY (A i) B)
    (hO' : ∀ i, O' i ≤ box pX pY (A i) B') (hB : B' ≤ B) (h : ∀ i, O' i ≤ O i)
    (z : (∀ i, Sec f (A i)) ⊗[K] Sec g B) (i : ι) :
    kunnethPi hw A B' O' hO' (LinearMap.lTensor _ (resA g hB).toLinearMap z) i =
      resA (pX ≫ f) (h i) (kunnethPi hw A B O hO z i) := by
  rw [kunnethPi_apply, Stacks.DoubleCech.rTensor_lTensor_apply,
    kunneth_lTensor hw (hO i) (hO' i) hB (h i), kunnethPi_apply]

/-- Components of `rid ∘ lTensor` on a product. -/
theorem rid_lTensor_apply {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] {N : Type*} [AddCommGroup N] [Module K N] (ev : N →ₗ[K] K)
    (z : (∀ i, M i) ⊗[K] N) (i : ι) :
    TensorProduct.rid K _ (LinearMap.lTensor _ ev z) i =
      TensorProduct.rid K _
        (LinearMap.lTensor _ ev (LinearMap.rTensor _ (LinearMap.proj i) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, Pi.add_apply, hz, hz']
  | tmul m n => simp

/-- The intersection of two opens `W` is a box. -/
theorem W_inf_W {I J : Type*} (U : I → X.Opens) (V : J → Y.Opens) (s t : I × J) :
    W pX pY U V s ⊓ W pX pY U V t = box pX pY (U s.1 ⊓ U t.1) (V s.2 ⊓ V t.2) := by
  simp only [W, box, Scheme.Hom.preimage_inf]
  ac_rfl

/-- The face `X × {y}` meets `W (a, b₀) ∩ W (a', b₀)` in `U a ∩ U a'` when `y ∈ V b₀`. -/
theorem le_faceX_preimage_W (hsq : IsPullback pX pY f g) {y : Spec (.of K) ⟶ Y}
    (hy : y ≫ g = 𝟙 _) {I J : Type*}
    (U : I → X.Opens) (V : J → Y.Opens) {b₀ : J} (hyb : Set.range y ⊆ V b₀) (a a' : I) :
    U a ⊓ U a' ≤ faceX hsq y hy ⁻¹ᵁ (W pX pY U V (a, b₀) ⊓ W pX pY U V (a', b₀)) := by
  rw [W_inf_W, inf_idem]
  exact le_faceX_preimage hsq y hy hyb

/-- The face `{x} × Y` meets `W (a₀, b) ∩ W (a₀, b')` in `V b ∩ V b'` when `x ∈ U a₀`. -/
theorem le_faceY_preimage_W (hsq : IsPullback pX pY f g) {x : Spec (.of K) ⟶ X}
    (hx : x ≫ f = 𝟙 _) {I J : Type*}
    (U : I → X.Opens) (V : J → Y.Opens) {a₀ : I} (hxa : Set.range x ⊆ U a₀) (b b' : J) :
    V b ⊓ V b' ≤ faceY hsq x hx ⁻¹ᵁ (W pX pY U V (a₀, b) ⊓ W pX pY U V (a₀, b')) := by
  rw [W_inf_W, inf_idem]
  exact le_faceY_preimage hsq x hx hxa

end Components

/-- Prove an equality of finite intersections of the opens `W` and boxes pointwise. -/
macro "opens_eq" : tactic => `(tactic| (
  simp only [W, box, Scheme.Hom.preimage_inf]
  ext p
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
  tauto))

/-- Prove an inclusion of finite intersections of the opens `W` and boxes pointwise. -/
macro "opens_le" : tactic => `(tactic| (
  rw [SetLike.le_def]
  intro p hp
  simp only [W, box, Scheme.Hom.preimage_inf, TopologicalSpace.Opens.mem_inf] at hp ⊢
  tauto))

section Boxes

variable {I J : Type*} (U : I → X.Opens) (V : J → Y.Opens)

/-- Two opens `W` with the same second index meet in a box. -/
theorem W_inf_W_snd (b : J) (p : I × I) :
    W pX pY U V (p.1, b) ⊓ W pX pY U V (p.2, b) = box pX pY (U p.1 ⊓ U p.2) (V b) := by
  opens_eq

/-- Two opens `W` with the same first index meet in a box. -/
theorem W_inf_W_fst (a : I) (b b' : J) :
    W pX pY U V (a, b) ⊓ W pX pY U V (a, b') = box pX pY (U a) (V b ⊓ V b') := by
  opens_eq

/-- Three opens `W` with the same second index meet in a box. -/
theorem W_inf_W_inf_W_snd (b : J) (q : I × I × I) :
    W pX pY U V (q.1, b) ⊓ W pX pY U V (q.2.1, b) ⊓ W pX pY U V (q.2.2, b) =
      box pX pY (U q.1 ⊓ U q.2.1 ⊓ U q.2.2) (V b) := by
  opens_eq

/-- The four opens `W` over `{p.1, p.2} × {b, b'}` meet in a box. -/
theorem W_inf_W_inf_W_inf_W (b b' : J) (p : I × I) :
    W pX pY U V (p.1, b) ⊓ W pX pY U V (p.2, b) ⊓ W pX pY U V (p.1, b') ⊓
      W pX pY U V (p.2, b') = box pX pY (U p.1 ⊓ U p.2) (V b ⊓ V b') := by
  opens_eq

end Boxes

end Square

section Main

section Steps

variable {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {pX : Q ⟶ X} {pY : Q ⟶ Y}
  (hsq : IsPullback pX pY f g) {I J : Type*} (U : I → X.Opens) (V : J → Y.Opens)

/-- The Künneth components over `V b` of a Čech `1`-cocycle are killed by `cechD₁`. -/
theorem rTensor_cechD₁_eq_zero [Fintype I] [DecidableEq I] [IsSeparated f]
    (hUa : ∀ a, IsAffineOpen (U a)) {b : J} (hVb : IsAffineOpen (V b))
    {c : ∀ s t : I × J, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t)}
    (hc : ∀ s t r,
      resA (pX ≫ f) (inf_le_left : W pX pY U V s ⊓ W pX pY U V t ⊓ W pX pY U V r ≤ _) (c s t) +
        resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c t r) =
      resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c s r))
    {z : (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g (V b)}
    (hz : kunnethPi hsq.w (fun p : I × I => U p.1 ⊓ U p.2) (V b)
      (fun p => W pX pY U V (p.1, b) ⊓ W pX pY U V (p.2, b))
      (fun p => (W_inf_W_snd U V b p).le) z = fun p : I × I => c (p.1, b) (p.2, b)) :
    LinearMap.rTensor _ (cechD₁ f U) z = 0 := by
  apply (kunnethPi_bijective hsq (fun q : I × I × I => U q.1 ⊓ U q.2.1 ⊓ U q.2.2) (V b) _
    (fun q => isAffineOpen_inf f (isAffineOpen_inf f (hUa q.1) (hUa q.2.1)) (hUa q.2.2)) hVb
    (W_inf_W_inf_W_snd U V b)).1
  rw [map_zero]
  funext q
  rw [kunnethPi_rTensor_cechD₁ hsq.w U _ (fun q => (W_inf_W_inf_W_snd U V b q).le) _
      (fun p => (W_inf_W_snd U V b p).le)
      (fun _ => le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (fun _ => le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ => inf_le_left), hz]
  simp only [Pi.zero_apply]
  linear_combination hc (q.1, b) (q.2.1, b) (q.2.2, b)

/-- The Künneth components of a Čech `1`-cocycle over `V b`, `V b'` and `V b ∩ V b'` satisfy the
mixed cocycle condition of the double complex. -/
theorem lTensor_sub_lTensor_eq_rTensor_cechD₀ [Fintype I] [DecidableEq I] [IsSeparated f]
    (hUa : ∀ a, IsAffineOpen (U a)) {b b' : J} (hVbb' : IsAffineOpen (V b ⊓ V b'))
    {c : ∀ s t : I × J, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t)}
    (hc : ∀ s t r,
      resA (pX ≫ f) (inf_le_left : W pX pY U V s ⊓ W pX pY U V t ⊓ W pX pY U V r ≤ _) (c s t) +
        resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c t r) =
      resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c s r))
    {z : (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g (V b)}
    {z' : (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g (V b')}
    {w : (∀ a, Sec f (U a)) ⊗[K] Sec g (V b ⊓ V b')}
    (hz : kunnethPi hsq.w (fun p : I × I => U p.1 ⊓ U p.2) (V b)
      (fun p => W pX pY U V (p.1, b) ⊓ W pX pY U V (p.2, b))
      (fun p => (W_inf_W_snd U V b p).le) z = fun p : I × I => c (p.1, b) (p.2, b))
    (hz' : kunnethPi hsq.w (fun p : I × I => U p.1 ⊓ U p.2) (V b')
      (fun p => W pX pY U V (p.1, b') ⊓ W pX pY U V (p.2, b'))
      (fun p => (W_inf_W_snd U V b' p).le) z' = fun p : I × I => c (p.1, b') (p.2, b'))
    (hw : kunnethPi hsq.w U (V b ⊓ V b') (fun a => W pX pY U V (a, b) ⊓ W pX pY U V (a, b'))
      (fun a => (W_inf_W_fst U V a b b').le) w = fun a => c (a, b) (a, b')) :
    LinearMap.lTensor _ (resA g (inf_le_right : V b ⊓ V b' ≤ V b')).toLinearMap z' -
        LinearMap.lTensor _ (resA g (inf_le_left : V b ⊓ V b' ≤ V b)).toLinearMap z =
      LinearMap.rTensor _ (cechD₀ f U) w := by
  apply (kunnethPi_bijective hsq (fun p : I × I => U p.1 ⊓ U p.2) (V b ⊓ V b') _
    (fun p => isAffineOpen_inf f (hUa p.1) (hUa p.2)) hVbb' (W_inf_W_inf_W_inf_W U V b b')).1
  funext p
  rw [map_sub, Pi.sub_apply,
    kunnethPi_lTensor hsq.w (fun p : I × I => U p.1 ⊓ U p.2) _ _
      (fun p => (W_inf_W_snd U V b' p).le) (fun p => (W_inf_W_inf_W_inf_W U V b b' p).le)
      inf_le_right (fun p => le_inf (inf_le_left.trans inf_le_right) inf_le_right),
    kunnethPi_lTensor hsq.w (fun p : I × I => U p.1 ⊓ U p.2) _ _
      (fun p => (W_inf_W_snd U V b p).le) (fun p => (W_inf_W_inf_W_inf_W U V b b' p).le)
      inf_le_left (fun p => inf_le_left.trans inf_le_left),
    kunnethPi_rTensor_cechD₀ hsq.w U _ (fun p => (W_inf_W_inf_W_inf_W U V b b' p).le) _
      (fun a => (W_inf_W_fst U V a b b').le) (fun p => by opens_le) (fun p => by opens_le),
    hz, hz', hw]
  linear_combination
    resA_cocycle_of_le (pX ≫ f) hc (p.1, b) (p.1, b') (p.2, b') (W pX pY U V (p.1, b) ⊓
      W pX pY U V (p.2, b) ⊓ W pX pY U V (p.1, b') ⊓ W pX pY U V (p.2, b')) (by opens_le) -
    resA_cocycle_of_le (pX ≫ f) hc (p.1, b) (p.2, b) (p.2, b') (W pX pY U V (p.1, b) ⊓
      W pX pY U V (p.2, b) ⊓ W pX pY U V (p.1, b') ⊓ W pX pY U V (p.2, b')) (by opens_le)

/-- A Čech `1`-cocycle whose restriction to the face `X × {y}` is a coboundary has Künneth
components over `V b₀` whose evaluation at `y` is a `cechD₀`-coboundary. -/
theorem exists_lTensor_evalAt_eq_rTensor_cechD₀ (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    {b₀ : J} (hyb : Set.range y ⊆ V b₀)
    {c : ∀ s t : I × J, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t)}
    (hX : ∃ e : ∀ a, Γ(X, U a), ∀ a a',
      ((faceX hsq y hy).appLE _ (U a ⊓ U a') (le_faceX_preimage_W hsq hy U V hyb a a')).hom
          (c (a, b₀) (a', b₀)) = res inf_le_right (e a') - res inf_le_left (e a))
    {z : (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g (V b₀)}
    (hz : kunnethPi hsq.w (fun p : I × I => U p.1 ⊓ U p.2) (V b₀)
      (fun p => W pX pY U V (p.1, b₀) ⊓ W pX pY U V (p.2, b₀))
      (fun p => (W_inf_W_snd U V b₀ p).le) z = fun p : I × I => c (p.1, b₀) (p.2, b₀)) :
    ∃ eX : (∀ a, Sec f (U a)) ⊗[K] K,
      LinearMap.lTensor _ (evalAt g y hy (top_le_preimage_of_range y hyb)).toLinearMap z =
        LinearMap.rTensor K (cechD₀ f U) eX := by
  obtain ⟨e, he⟩ := hX
  let e₀ : ∀ a, Sec f (U a) := e
  refine ⟨e₀ ⊗ₜ 1, (TensorProduct.rid K _).injective ?_⟩
  rw [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, one_smul]
  funext p
  rw [rid_lTensor_apply]
  have hk : kunneth hsq.w (U p.1 ⊓ U p.2) (V b₀) _ (W_inf_W_snd U V b₀ p).le
      (LinearMap.rTensor _ (LinearMap.proj p) z) = c (p.1, b₀) (p.2, b₀) :=
    congrFun hz p
  have hF := pullA_faceX_kunneth hsq y hy hyb (W_inf_W_snd U V b₀ p).le
    (le_faceX_preimage_W hsq hy U V hyb p.1 p.2) le_rfl
    (LinearMap.rTensor _ (LinearMap.proj p) z)
  rw [resA_refl, hk] at hF
  rw [← hF]
  exact he p.1 p.2

/-- A Čech `1`-cocycle whose restriction to the face `{x} × Y` is a coboundary has Künneth
components over `V b ∩ V b'` whose evaluation at `x` is a Čech coboundary on `Y`. -/
theorem exists_lid_rTensor_evalAt_eq (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) {a₀ : I}
    (hxa : Set.range x ⊆ U a₀)
    {c : ∀ s t : I × J, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t)}
    (hY : ∃ e : ∀ b, Γ(Y, V b), ∀ b b',
      ((faceY hsq x hx).appLE _ (V b ⊓ V b') (le_faceY_preimage_W hsq hx U V hxa b b')).hom
          (c (a₀, b) (a₀, b')) = res inf_le_right (e b') - res inf_le_left (e b))
    {w : ∀ b b', (∀ a, Sec f (U a)) ⊗[K] Sec g (V b ⊓ V b')}
    (hw : ∀ b b', kunnethPi hsq.w U (V b ⊓ V b')
      (fun a => W pX pY U V (a, b) ⊓ W pX pY U V (a, b'))
      (fun a => (W_inf_W_fst U V a b b').le) (w b b') = fun a => c (a, b) (a, b')) :
    ∃ eY : ∀ b, Sec g (V b), ∀ b b',
      TensorProduct.lid K _ (LinearMap.rTensor _
          ((evalAt f x hx (top_le_preimage_of_range x hxa)).toLinearMap ∘ₗ
            LinearMap.proj a₀) (w b b')) =
        (resA g (inf_le_right : V b ⊓ V b' ≤ V b')).toLinearMap (eY b') -
          (resA g (inf_le_left : V b ⊓ V b' ≤ V b)).toLinearMap (eY b) := by
  obtain ⟨e, he⟩ := hY
  refine ⟨e, fun b b' => ?_⟩
  have hk : kunneth hsq.w (U a₀) (V b ⊓ V b') _ (W_inf_W_fst U V a₀ b b').le
      (LinearMap.rTensor _ (LinearMap.proj a₀) (w b b')) = c (a₀, b) (a₀, b') :=
    congrFun (hw b b') a₀
  have hF := pullA_faceY_kunneth hsq x hx hxa (W_inf_W_fst U V a₀ b b').le
    (le_faceY_preimage_W hsq hx U V hxa b b') le_rfl
    (LinearMap.rTensor _ (LinearMap.proj a₀) (w b b'))
  rw [resA_refl, hk] at hF
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, ← hF]
  exact he b b'

/-- A Čech `1`-cocycle whose Künneth components are the coboundary of a `0`-cochain `E` of the
double complex is a coboundary. -/
theorem exists_coboundary_of_kunnethPi_eq
    {c : ∀ s t : I × J, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t)}
    (hc : ∀ s t r,
      resA (pX ≫ f) (inf_le_left : W pX pY U V s ⊓ W pX pY U V t ⊓ W pX pY U V r ≤ _) (c s t) +
        resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c t r) =
      resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c s r))
    {c₁₀ : ∀ b, (∀ p : I × I, Sec f (U p.1 ⊓ U p.2)) ⊗[K] Sec g (V b)}
    {c₀₁ : ∀ b b', (∀ a, Sec f (U a)) ⊗[K] Sec g (V b ⊓ V b')}
    (hc₁₀ : ∀ b, kunnethPi hsq.w (fun p : I × I => U p.1 ⊓ U p.2) (V b)
      (fun p => W pX pY U V (p.1, b) ⊓ W pX pY U V (p.2, b))
      (fun p => (W_inf_W_snd U V b p).le) (c₁₀ b) = fun p : I × I => c (p.1, b) (p.2, b))
    (hc₀₁ : ∀ b b', kunnethPi hsq.w U (V b ⊓ V b')
      (fun a => W pX pY U V (a, b) ⊓ W pX pY U V (a, b'))
      (fun a => (W_inf_W_fst U V a b b').le) (c₀₁ b b') = fun a => c (a, b) (a, b'))
    (hE : ∃ E : ∀ b, (∀ a, Sec f (U a)) ⊗[K] Sec g (V b),
      (∀ b, c₁₀ b = LinearMap.rTensor _ (cechD₀ f U) (E b)) ∧ ∀ b b',
        c₀₁ b b' = LinearMap.lTensor _ (resA g (inf_le_right : V b ⊓ V b' ≤ V b')).toLinearMap
            (E b') -
          LinearMap.lTensor _ (resA g (inf_le_left : V b ⊓ V b' ≤ V b)).toLinearMap (E b)) :
    ∃ e : ∀ s : I × J, Sec (pX ≫ f) (W pX pY U V s),
      ∀ s t, c s t = resA (pX ≫ f) inf_le_right (e t) - resA (pX ≫ f) inf_le_left (e s) := by
  obtain ⟨E, hE₁, hE₂⟩ := hE
  let e' : ∀ s : I × J, Sec (pX ≫ f) (W pX pY U V s) := fun s =>
    kunnethPi hsq.w U (V s.2) (fun a => W pX pY U V (a, s.2)) (fun a => le_rfl) (E s.2) s.1
  have hh : ∀ b a a', c (a, b) (a', b) =
      resA (pX ≫ f) inf_le_right (e' (a', b)) - resA (pX ≫ f) inf_le_left (e' (a, b)) := by
    intro b a a'
    rw [← congrFun (hc₁₀ b) (a, a'), hE₁ b]
    exact kunnethPi_rTensor_cechD₀ hsq.w U _ (fun p => (W_inf_W_snd U V b p).le)
      (fun a => W pX pY U V (a, b)) (fun a => le_rfl) (fun p => inf_le_right)
      (fun p => inf_le_left) (E b) (a, a')
  have hv : ∀ a b b', c (a, b) (a, b') =
      resA (pX ≫ f) inf_le_right (e' (a, b')) - resA (pX ≫ f) inf_le_left (e' (a, b)) := by
    intro a b b'
    rw [← congrFun (hc₀₁ b b') a, hE₂ b b', map_sub, Pi.sub_apply,
      kunnethPi_lTensor hsq.w U (fun a => W pX pY U V (a, b')) _ (fun a => le_rfl)
        (fun a => (W_inf_W_fst U V a b b').le) inf_le_right (fun a => inf_le_right),
      kunnethPi_lTensor hsq.w U (fun a => W pX pY U V (a, b)) _ (fun a => le_rfl)
        (fun a => (W_inf_W_fst U V a b b').le) inf_le_left (fun a => inf_le_left)]
  refine ⟨e', ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  have := resA_cocycle_of_le (pX ≫ f) hc (a, b) (a', b) (a', b')
    (W pX pY U V (a, b) ⊓ W pX pY U V (a', b')) (by opens_le)
  rw [hh b a a', hv a' b b', map_sub, map_sub, resA_resA, resA_resA, resA_resA, resA_resA,
    resA_refl] at this
  rw [← this]
  abel

end Steps

/-- **Künneth injectivity in degree one, as explicit cocycles.** Let `X` and `Y` be proper
geometrically integral schemes over a field `K`, with `K`-points `x` and `y`, and let `U` and `V`
be finite affine open covers of `X` and `Y`. A Čech `1`-cocycle `c` of `𝒪` on `X ×_K Y` for the
cover by the boxes `W (a, b) = U_a × V_b` whose restrictions to the two faces `X × {y}` and
`{x} × Y` are coboundaries is itself a coboundary. This is the injectivity of
`H¹(X ×_K Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` used by [Stacks, Tag 0BF3] (cf. [Stacks, Tag 0BED]).

Restrictions are `AlgebraicGeometry.Cube.res`; the pullback of a section to a face is `appLE`
along `faceX hsq y hy : X ⟶ X ×_K Y` and `faceY hsq x hx : Y ⟶ X ×_K Y`. -/
theorem exists_coboundary_of_faces {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)}
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    {pX : Q ⟶ X} {pY : Q ⟶ Y} (hsq : IsPullback pX pY f g)
    (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    {I J : Type u} [Finite I] [Finite J] (U : I → X.Opens) (V : J → Y.Opens)
    (hUa : ∀ a, IsAffineOpen (U a)) (hVa : ∀ b, IsAffineOpen (V b))
    (hU : (⊤ : X.Opens) = ⨆ a, U a) (hV : (⊤ : Y.Opens) = ⨆ b, V b)
    (a₀ : I) (hxa : Set.range x ⊆ U a₀) (b₀ : J) (hyb : Set.range y ⊆ V b₀)
    (c : ∀ s t : I × J, Γ(Q, W pX pY U V s ⊓ W pX pY U V t))
    (hc : ∀ s t r,
      res (B := W pX pY U V s ⊓ W pX pY U V t ⊓ W pX pY U V r) inf_le_left (c s t) +
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c t r) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c s r))
    (hX : ∃ e : ∀ a, Γ(X, U a), ∀ a a',
      ((faceX hsq y hy).appLE _ (U a ⊓ U a') (le_faceX_preimage_W hsq hy U V hyb a a')).hom
          (c (a, b₀) (a', b₀)) = res inf_le_right (e a') - res inf_le_left (e a))
    (hY : ∃ e : ∀ b, Γ(Y, V b), ∀ b b',
      ((faceY hsq x hx).appLE _ (V b ⊓ V b') (le_faceY_preimage_W hsq hx U V hxa b b')).hom
          (c (a₀, b) (a₀, b')) = res inf_le_right (e b') - res inf_le_left (e b)) :
    ∃ e : ∀ s : I × J, Γ(Q, W pX pY U V s),
      ∀ s t, c s t = res inf_le_right (e t) - res inf_le_left (e s) := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  let c' : ∀ s t, Sec (pX ≫ f) (W pX pY U V s ⊓ W pX pY U V t) := c
  have hcA : ∀ s t r,
      resA (pX ≫ f) (inf_le_left : W pX pY U V s ⊓ W pX pY U V t ⊓ W pX pY U V r ≤ _) (c' s t) +
        resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c' t r) =
      resA (pX ≫ f) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c' s r) := hc
  have hVV : ∀ b b', IsAffineOpen (V b ⊓ V b') := fun b b' =>
    isAffineOpen_inf g (hVa b) (hVa b')
  choose c₁₀ hc₁₀ using fun b => (kunnethPi_bijective hsq (fun p : I × I => U p.1 ⊓ U p.2) (V b)
    _ (fun p => isAffineOpen_inf f (hUa p.1) (hUa p.2)) (hVa b) (W_inf_W_snd U V b)).2
      fun p => c' (p.1, b) (p.2, b)
  choose c₀₁ hc₀₁ using fun b b' => (kunnethPi_bijective hsq U (V b ⊓ V b') _ hUa (hVV b b')
    fun a => W_inf_W_fst U V a b b').2 fun a => c' (a, b) (a, b')
  let incl : ∀ b, K →ₗ[K] Sec g (V b) := fun b => Algebra.linearMap K (Sec g (V b))
  let s₀ : ∀ b b', Sec g (V b) →ₗ[K] Sec g (V b ⊓ V b') := fun b b' =>
    (resA g (inf_le_left : V b ⊓ V b' ≤ V b)).toLinearMap
  let s₁ : ∀ b b', Sec g (V b') →ₗ[K] Sec g (V b ⊓ V b') := fun b b' =>
    (resA g (inf_le_right : V b ⊓ V b' ≤ V b')).toLinearMap
  have hcompat : ∀ b b', s₀ b b' ∘ₗ incl b = s₁ b b' ∘ₗ incl b' := fun b b' => by
    ext
    simp [s₀, s₁, incl]
  let evY : Sec g (V b₀) →ₗ[K] K := (evalAt g y hy (top_le_preimage_of_range y hyb)).toLinearMap
  have hevY : evY ∘ₗ incl b₀ = LinearMap.id := by
    ext
    simp [evY, incl]
  exact exists_coboundary_of_kunnethPi_eq hsq U V hcA hc₁₀ hc₀₁ <|
    Stacks.DoubleCech.exists_eq_coboundary (cechD₁_comp_cechD₀ f U) (fun _ => 1)
      (cechD₀_one f U) (exists_eq_smul_of_cechD₀_eq_zero f U hU)
      ((evalAt f x hx (top_le_preimage_of_range x hxa)).toLinearMap ∘ₗ LinearMap.proj a₀)
      (by simp) hcompat (exists_eq_algebraMap_of_compatible g V hV) b₀ evY hevY c₁₀ c₀₁
      (fun b => rTensor_cechD₁_eq_zero hsq U V hUa (hVa b) hcA (hc₁₀ b))
      (fun b b' => lTensor_sub_lTensor_eq_rTensor_cechD₀ hsq U V hUa (hVV b b') hcA (hc₁₀ b)
        (hc₁₀ b') (hc₀₁ b b'))
      (exists_lTensor_evalAt_eq_rTensor_cechD₀ hsq U V y hy hyb hX (hc₁₀ b₀))
      (exists_lid_rTensor_evalAt_eq hsq U V x hx hxa hY hc₀₁)

end Main

end AlgebraicGeometry.Cube

end
