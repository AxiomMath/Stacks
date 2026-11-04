module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Transport

/-!
# Gluing infinitesimal lifts through a formally étale chart

Let `Φ` be a formally étale chart `R` of a functor `X` on a class `P` of `A'`-algebras, see
`Stacks.ChartGlue.FormallyEtaleChart`. Consider an infinitesimal lifting problem for `X`: a
square-zero surjection `O → Ō` of algebras of `P` and a point `x` of `X` over `Ō`, to be lifted to
a point over `O`. Suppose given a cover `O → B₁` with its two- and threefold "fibre products"
`B₂`, `B₃` (in the application `B₁ = B'`, `B₂ = B' ⊗ B'`, `B₃ = B' ⊗ B' ⊗ B'` for a faithfully flat
étale `A'`-algebra `B'`), compatible square-zero surjections `B_n → B̄_n` lying over `O → Ō`, a
frame `ū : R → B̄₁` of the restriction of `x` to `B̄₁`, and a lift `u' : R → B₁` of `ū`.

The point `⟨u'⟩` of `X` over `B₁` lifts `x|_{B̄₁}`; it descends to `O` exactly when its two
restrictions to `B₂` agree. This file measures the failure by a derivation `D` along the second
frame `p₂ ∘ u'` of `B₂`, computes how `D` changes when `u'` is moved by a derivation `θ`, and
proves that `D` satisfies a cocycle identity over `B₃`. Consequently, if every such cocycle is a
coboundary — which is a vanishing of first Čech cohomology, proved separately — then the lifting
problem has a solution.

## Main definitions

* `Stacks.ChartGlue.CechCover`: the data of the cover and its square-zero quotients.
* `Stacks.ChartGlue.CechCover.lift₂`: the lift over `B₂`, through the reduction of the second
  frame, of the first restriction of `⟨u'⟩`.
* `Stacks.ChartGlue.CechCover.defect`: the derivation `D`.

## Main results

* `Stacks.ChartGlue.CechCover.defect_moved`: the change of `D` under `u' ↦ u' + θ`.
* `Stacks.ChartGlue.CechCover.defect_cocycle`: the cocycle identity over `B₃`.
* `Stacks.ChartGlue.CechCover.exists_lift_of_coboundary`: **the gluing.** If `D` is the twisted
  coboundary of a derivation `θ`, the point `x` lifts to `O`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.ChartGlue

variable {A' : Type u} [CommRing A'] {P : ObjectProperty (CommAlgCat.{u} A')}
  {X : P.FullSubcategory ⥤ Type v} {R : Type u} [CommRing R] [Algebra A' R]

/-- The algebra map underlying a morphism of the full subcategory of algebras. -/
abbrev ah {C D : P.FullSubcategory} (f : C ⟶ D) : C.obj →ₐ[A'] D.obj := f.hom.hom

/-- `ah` takes composition of morphisms to composition of algebra maps. -/
lemma ah_comp {C D E : P.FullSubcategory} (f : C ⟶ D) (g : D ⟶ E) :
    ah (f ≫ g) = (ah g).comp (ah f) := rfl

/-- A commutative square of morphisms gives equal values of the two composite algebra maps. -/
lemma ah_comm {C D D' E : P.FullSubcategory} {f : C ⟶ D} {g : D ⟶ E} {f' : C ⟶ D'}
    {g' : D' ⟶ E} (h : f ≫ g = f' ≫ g') (c : C.obj) : ah g (ah f c) = ah g' (ah f' c) :=
  congrArg (fun φ : C.obj →ₐ[A'] E.obj ↦ φ c) (congrArg ah h)

/-- The restriction of an algebra map to kernels of compatible surjections, as a semilinear map
of the kernels. -/
def kerMap {C Cb D Db : P.FullSubcategory} (πC : C ⟶ Cb) (πD : D ⟶ Db) (f : C ⟶ D) (fb : Cb ⟶ Db)
    (h : f ≫ πD = πC ≫ fb) :
    RingHom.ker (ah πC) →ₛₗ[((ah f : C.obj →ₐ[A'] D.obj) : C.obj →+* D.obj)]
      RingHom.ker (ah πD) where
  toFun j := ⟨ah f j, by
    rw [RingHom.mem_ker]
    have := congrArg (fun φ : C.obj →ₐ[A'] Db.obj ↦ φ j) (congrArg ah h)
    simp only [ah_comp, AlgHom.comp_apply] at this
    rw [this, show (ah πC) j = 0 from j.2, map_zero]⟩
  map_add' a b := Subtype.ext (map_add (ah f) _ _)
  map_smul' c a := Subtype.ext (by simp)

/-- `kerMap` is the restriction of `ah f` to the kernels. -/
@[simp] lemma coe_kerMap {C Cb D Db : P.FullSubcategory} (πC : C ⟶ Cb) (πD : D ⟶ Db) (f : C ⟶ D)
    (fb : Cb ⟶ Db) (h : f ≫ πD = πC ≫ fb) (j : RingHom.ker (ah πC)) :
    (kerMap πC πD f fb h j : D.obj) = ah f j := rfl

/-- **Recasting** a derivation with values in a square-zero ideal `J` along a second algebra map
which agrees with the first modulo `J`. -/
def DerAlong.recast {C : Type u} [CommRing C] [Algebra A' C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    {w w' : R →ₐ[A'] C} (h : ∀ r, w r - w' r ∈ J) (δ : DerAlong w J) : DerAlong w' J :=
  ⟨δ, δ.map_add, δ.map_algebraMap, fun r s ↦ by
    have key : ∀ (a : R) (j : J), w a • j = w' a • j := fun a j ↦ by
      apply Subtype.ext
      have h0 : (w a - w' a) * j = 0 := by
        rw [← Ideal.mem_bot, ← hJ, pow_two]
        exact Ideal.mul_mem_mul (h a) j.2
      simp only [Submodule.coe_smul, smul_eq_mul]
      linear_combination h0
    rw [δ.leibniz, key, key]⟩

/-- The recast derivation has the same values as the original. -/
@[simp] lemma DerAlong.recast_apply {C : Type u} [CommRing C] [Algebra A' C] (J : Ideal C)
    (hJ : J ^ 2 = ⊥) {w w' : R →ₐ[A'] C} (h : ∀ r, w r - w' r ∈ J) (δ : DerAlong w J) (r : R) :
    δ.recast J hJ h r = δ r := rfl

variable (P) in
/-- The data of a cover of an infinitesimal lifting problem: a square-zero surjection `O → Ō`
of algebras of `P`, a cover `O → B₁` with two maps `B₁ → B₂` and three maps `B₂ → B₃`
satisfying the simplicial identities, and compatible square-zero surjections `B_n → B̄_n`. -/
structure CechCover where
  /-- The algebra `O` to which the point is to be lifted. -/
  O : P.FullSubcategory
  /-- The square-zero quotient `Ō` of `O`. -/
  O' : P.FullSubcategory
  /-- The cover `B₁` of `O`. -/
  B₁ : P.FullSubcategory
  /-- The square-zero quotient `B̄₁` of `B₁`. -/
  B₁' : P.FullSubcategory
  /-- The twofold fibre product `B₂`. -/
  B₂ : P.FullSubcategory
  /-- The square-zero quotient `B̄₂` of `B₂`. -/
  B₂' : P.FullSubcategory
  /-- The threefold fibre product `B₃`. -/
  B₃ : P.FullSubcategory
  /-- The square-zero quotient `B̄₃` of `B₃`. -/
  B₃' : P.FullSubcategory
  /-- The surjection `O → Ō`. -/
  πO : O ⟶ O'
  /-- The surjection `B₁ → B̄₁`. -/
  π₁ : B₁ ⟶ B₁'
  /-- The surjection `B₂ → B̄₂`. -/
  π₂ : B₂ ⟶ B₂'
  /-- The surjection `B₃ → B̄₃`. -/
  π₃ : B₃ ⟶ B₃'
  /-- The cover `O → B₁`. -/
  ι : O ⟶ B₁
  /-- The reduced cover `Ō → B̄₁`. -/
  ι' : O' ⟶ B₁'
  /-- The first map `B₁ → B₂`. -/
  p₁ : B₁ ⟶ B₂
  /-- The second map `B₁ → B₂`. -/
  p₂ : B₁ ⟶ B₂
  /-- The first map `B̄₁ → B̄₂`. -/
  p₁' : B₁' ⟶ B₂'
  /-- The second map `B̄₁ → B̄₂`. -/
  p₂' : B₁' ⟶ B₂'
  /-- The map `B₂ → B₃` onto the first and second factors. -/
  q₁₂ : B₂ ⟶ B₃
  /-- The map `B₂ → B₃` onto the second and third factors. -/
  q₂₃ : B₂ ⟶ B₃
  /-- The map `B₂ → B₃` onto the first and third factors. -/
  q₁₃ : B₂ ⟶ B₃
  /-- The map `B̄₂ → B̄₃` onto the first and second factors. -/
  q₁₂' : B₂' ⟶ B₃'
  /-- The map `B̄₂ → B̄₃` onto the second and third factors. -/
  q₂₃' : B₂' ⟶ B₃'
  /-- The map `B̄₂ → B̄₃` onto the first and third factors. -/
  q₁₃' : B₂' ⟶ B₃'
  ι_π : ι ≫ π₁ = πO ≫ ι'
  p₁_π : p₁ ≫ π₂ = π₁ ≫ p₁'
  p₂_π : p₂ ≫ π₂ = π₁ ≫ p₂'
  q₁₂_π : q₁₂ ≫ π₃ = π₂ ≫ q₁₂'
  q₂₃_π : q₂₃ ≫ π₃ = π₂ ≫ q₂₃'
  q₁₃_π : q₁₃ ≫ π₃ = π₂ ≫ q₁₃'
  ι_p : ι ≫ p₁ = ι ≫ p₂
  ι_p' : ι' ≫ p₁' = ι' ≫ p₂'
  p₁_q₁₂ : p₁ ≫ q₁₂ = p₁ ≫ q₁₃
  p₂_q₁₂ : p₂ ≫ q₁₂ = p₁ ≫ q₂₃
  p₂_q₂₃ : p₂ ≫ q₂₃ = p₂ ≫ q₁₃
  p₁_q₁₂' : p₁' ≫ q₁₂' = p₁' ≫ q₁₃'
  p₂_q₁₂' : p₂' ≫ q₁₂' = p₁' ≫ q₂₃'
  p₂_q₂₃' : p₂' ≫ q₂₃' = p₂' ≫ q₁₃'
  π₁_surj : Function.Surjective (ah π₁)
  π₂_surj : Function.Surjective (ah π₂)
  π₃_surj : Function.Surjective (ah π₃)
  π₁_sq : RingHom.ker (ah π₁) ^ 2 = ⊥
  π₂_sq : RingHom.ker (ah π₂) ^ 2 = ⊥
  π₃_sq : RingHom.ker (ah π₃) ^ 2 = ⊥
  /-- The trivial extension of `B₂` by the kernel of `B₂ → B̄₂` lies in `P`. -/
  hJ₂ : P (CommAlgCat.of A' (TrivExt B₂.obj (RingHom.ker (ah π₂))))
  /-- The trivial extension of `B₃` by the kernel of `B₃ → B̄₃` lies in `P`. -/
  hJ₃ : P (CommAlgCat.of A' (TrivExt B₃.obj (RingHom.ker (ah π₃))))

namespace CechCover

variable (Φ : FormallyEtaleChart P X R) (K : CechCover P) (x : X.obj K.O')
  (ū : R →ₐ[A'] K.B₁'.obj) (hū : Φ.pt K.B₁' ū = X.map K.ι' x)

/-- The kernel of `B₁ → B̄₁`. -/
abbrev J₁ := RingHom.ker (ah K.π₁)
/-- The kernel of `B₂ → B̄₂`. -/
abbrev J₂ := RingHom.ker (ah K.π₂)
/-- The kernel of `B₃ → B̄₃`. -/
abbrev J₃ := RingHom.ker (ah K.π₃)

include hū in
/-- The two reductions of `x` to `B̄₂` agree, so the two reductions of the frame `ū` are frames of
one point. -/
lemma pt_p₁'_eq_pt_p₂' :
    Φ.pt K.B₂' ((ah K.p₁').comp ū) = Φ.pt K.B₂' ((ah K.p₂').comp ū) := by
  rw [Φ.pt_comp, Φ.pt_comp, hū, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, K.ι_p']

variable {Φ K x ū}
variable (u' : R →ₐ[A'] K.B₁.obj) (hu' : (ah K.π₁).comp u' = ū)

/-- The first frame of `B₂`, `p₁ ∘ u'`. -/
abbrev v₁ : R →ₐ[A'] K.B₂.obj := (ah K.p₁).comp u'
/-- The second frame of `B₂`, `p₂ ∘ u'`. -/
abbrev v₂ : R →ₐ[A'] K.B₂.obj := (ah K.p₂).comp u'

include hu' in
/-- The first frame of `B₂` reduces to `p₁' ∘ ū`. -/
lemma π₂_v₁ : (ah K.π₂).comp (v₁ u') = (ah K.p₁').comp ū := by
  rw [← hu', ← AlgHom.comp_assoc, ← ah_comp, K.p₁_π]; rfl

include hu' in
/-- The second frame of `B₂` reduces to `p₂' ∘ ū`. -/
lemma π₂_v₂ : (ah K.π₂).comp (v₂ u') = (ah K.p₂').comp ū := by
  rw [← hu', ← AlgHom.comp_assoc, ← ah_comp, K.p₂_π]; rfl

include hū hu' in
/-- The lift over `B₂` of the point `⟨p₁ ∘ u'⟩` through the second reduced frame. -/
theorem existsUnique_lift₂ :
    ∃! w : R →ₐ[A'] K.B₂.obj, (ah K.π₂).comp w = (ah K.p₂').comp ū ∧
      Φ.pt K.B₂ w = Φ.pt K.B₂ (v₁ u') := by
  refine Φ.existsUnique_lift K.π₂ K.π₂_surj K.π₂_sq _ _ ?_
  rw [← Φ.pt_comp, π₂_v₁ u' hu']
  exact (pt_p₁'_eq_pt_p₂' Φ K x ū hū).symm

/-- The lift over `B₂` of the point `⟨p₁ ∘ u'⟩` through the second reduced frame. -/
noncomputable def lift₂ : R →ₐ[A'] K.B₂.obj :=
  (existsUnique_lift₂ hū u' hu').exists.choose

/-- The lift `lift₂` reduces to `p₂' ∘ ū`. -/
lemma π₂_lift₂ : (ah K.π₂).comp (lift₂ hū u' hu') = (ah K.p₂').comp ū :=
  (existsUnique_lift₂ hū u' hu').exists.choose_spec.1

/-- The lift `lift₂` is a frame of the point `⟨p₁ ∘ u'⟩`. -/
lemma pt_lift₂ : Φ.pt K.B₂ (lift₂ hū u' hu') = Φ.pt K.B₂ (v₁ u') :=
  (existsUnique_lift₂ hū u' hu').exists.choose_spec.2

/-- A frame over `B₂` reducing to `p₂' ∘ ū` and representing `⟨p₁ ∘ u'⟩` is `lift₂`. -/
lemma lift₂_unique (w : R →ₐ[A'] K.B₂.obj) (h₁ : (ah K.π₂).comp w = (ah K.p₂').comp ū)
    (h₂ : Φ.pt K.B₂ w = Φ.pt K.B₂ (v₁ u')) : w = lift₂ hū u' hu' :=
  (existsUnique_lift₂ hū u' hu').unique ⟨h₁, h₂⟩ ⟨π₂_lift₂ hū u' hu', pt_lift₂ hū u' hu'⟩

/-- The lift `lift₂` agrees with the second frame `p₂ ∘ u'` modulo the kernel of `B₂ → B̄₂`. -/
lemma lift₂_sub_v₂_mem (r : R) : lift₂ hū u' hu' r - v₂ u' r ∈ K.J₂ := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  have h₁ := congrArg (fun φ : R →ₐ[A'] K.B₂'.obj ↦ φ r) (π₂_lift₂ hū u' hu')
  have h₂ := congrArg (fun φ : R →ₐ[A'] K.B₂'.obj ↦ φ r) (π₂_v₂ u' hu')
  exact h₁.trans h₂.symm

/-- **The defect** of the point `⟨u'⟩`: the difference over `B₂` between the lift of its first
restriction through the second reduced frame and the second frame itself. It vanishes exactly
when the two restrictions of `⟨u'⟩` agree. -/
noncomputable def defect : DerAlong (v₂ u') K.J₂ :=
  DerAlong.ofDiff K.J₂ K.π₂_sq _ _ (lift₂_sub_v₂_mem hū u' hu')

/-- The value of the defect at `r` is `lift₂ r - (p₂ ∘ u') r`. -/
lemma coe_defect_apply (r : R) :
    (defect hū u' hu' r : K.B₂.obj) = lift₂ hū u' hu' r - v₂ u' r := rfl

/-- The two restrictions of `⟨u'⟩` to `B₂` agree when the defect vanishes. -/
lemma map_p₁_eq_map_p₂_of_defect (h : ∀ r, (defect hū u' hu' r : K.B₂.obj) = 0) :
    X.map K.p₁ (Φ.pt K.B₁ u') = X.map K.p₂ (Φ.pt K.B₁ u') := by
  have hw : lift₂ hū u' hu' = v₂ u' := AlgHom.ext fun r ↦ sub_eq_zero.1 (h r)
  rw [← Φ.pt_comp, ← Φ.pt_comp]
  exact (pt_lift₂ hū u' hu').symm.trans (congrArg _ hw)

/-- The frame `p₁ ∘ u'` and the lift `lift₂` are frames of one point of `X` over `B₂`. -/
lemma pt_v₁_eq_pt_lift₂ : Φ.pt K.B₂ (v₁ u') = Φ.pt K.B₂ (lift₂ hū u' hu') :=
  (pt_lift₂ hū u' hu').symm

/-- The kernel map `J₁ → J₂` along `p₁`. -/
abbrev kerP₁ := kerMap K.π₁ K.π₂ K.p₁ K.p₁' K.p₁_π
/-- The kernel map `J₁ → J₂` along `p₂`. -/
abbrev kerP₂ := kerMap K.π₁ K.π₂ K.p₂ K.p₂' K.p₂_π

/-- Moving the lift `u'` of `ū` by a derivation with values in `J₁`. -/
noncomputable abbrev moved (θ : DerAlong u' K.J₁) : R →ₐ[A'] K.B₁.obj :=
  DerAlong.addHom K.J₁ K.π₁_sq θ

/-- Adding a derivation with values in the kernel of `π` does not change the reduction mod `π`. -/
private lemma comp_addHom_of_ker {C D : P.FullSubcategory} (π : C ⟶ D)
    (hJ : RingHom.ker (ah π) ^ 2 = ⊥) {w : R →ₐ[A'] C.obj} (δ : DerAlong w (RingHom.ker (ah π))) :
    (ah π).comp (DerAlong.addHom _ hJ δ) = (ah π).comp w :=
  AlgHom.ext fun r ↦ by
    simp only [AlgHom.comp_apply, DerAlong.addHom_apply, map_add,
      show (ah π) (δ r) = 0 from (δ r).2, add_zero]

include hu' in
/-- The moved lift `u' + θ` is again a lift of `ū`. -/
lemma π₁_moved (θ : DerAlong u' K.J₁) : (ah K.π₁).comp (moved u' θ) = ū := by
  rw [← hu']
  exact comp_addHom_of_ker K.π₁ K.π₁_sq θ

/-- **The change of the defect under `u' ↦ u' + θ`.** -/
theorem defect_moved (θ : DerAlong u' K.J₁) (r : R) :
    (defect hū (moved u' θ) (π₁_moved u' hu' θ) r : K.B₂.obj) =
      defect hū u' hu' r +
        Φ.transportFun K.hJ₂ (pt_v₁_eq_pt_lift₂ hū u' hu') (θ.map (ah K.p₁) (kerP₁ (K := K))) r -
        θ.map (ah K.p₂) (kerP₂ (K := K)) r := by
  set φ := Φ.transportFun K.hJ₂ (pt_v₁_eq_pt_lift₂ hū u' hu') (θ.map (ah K.p₁) (kerP₁ (K := K)))
  have hv₁ : v₁ (moved u' θ) = DerAlong.addHom K.J₂ K.π₂_sq (θ.map (ah K.p₁) (kerP₁ (K := K))) :=
    AlgHom.ext fun r ↦ by simp [map_add]
  have hlift : lift₂ hū (moved u' θ) (π₁_moved u' hu' θ) =
      DerAlong.addHom K.J₂ K.π₂_sq φ := by
    symm
    refine lift₂_unique hū (moved u' θ) (π₁_moved u' hu' θ) _ ?_ ?_
    · rw [← π₂_lift₂ hū u' hu']
      exact comp_addHom_of_ker K.π₂ K.π₂_sq φ
    · rw [hv₁]
      exact (Φ.pt_addHom_transportFun K.J₂ K.π₂_sq K.hJ₂ _ _).symm
  rw [coe_defect_apply, hlift, DerAlong.addHom_apply, coe_defect_apply]
  simp only [v₂, moved, AlgHom.comp_apply, DerAlong.addHom_apply, map_add,
    DerAlong.map_apply, coe_kerMap]
  abel

/-- **The gluing.** If the lift `u'` can be moved by a derivation `θ` whose twisted coboundary is
the defect, then the point `x` lifts to `O`. -/
theorem exists_lift_of_coboundary
    (hglue : ∀ z : X.obj K.B₁, X.map K.p₁ z = X.map K.p₂ z → ∃ z₀ : X.obj K.O, X.map K.ι z₀ = z)
    (hsep : ∀ y₁ y₂ : X.obj K.O', X.map K.ι' y₁ = X.map K.ι' y₂ → y₁ = y₂)
    (θ : DerAlong u' K.J₁)
    (hθ : ∀ r, (θ.map (ah K.p₂) (kerP₂ (K := K)) r : K.B₂.obj) -
      Φ.transportFun K.hJ₂ (pt_v₁_eq_pt_lift₂ hū u' hu') (θ.map (ah K.p₁) (kerP₁ (K := K))) r =
        defect hū u' hu' r) :
    ∃ z : X.obj K.O, X.map K.πO z = x := by
  have h0 : ∀ r, (defect hū (moved u' θ) (π₁_moved u' hu' θ) r : K.B₂.obj) = 0 := fun r ↦ by
    rw [defect_moved hū u' hu' θ r, ← hθ r]
    abel
  obtain ⟨z₀, hz₀⟩ := hglue _ (map_p₁_eq_map_p₂_of_defect hū _ _ h0)
  refine ⟨z₀, hsep _ _ ?_⟩
  rw [← FunctorToTypes.map_comp_apply, ← K.ι_π, FunctorToTypes.map_comp_apply, hz₀, ← Φ.pt_comp,
    π₁_moved u' hu' θ, hū]

/-- The kernel map `J₂ → J₃` along `q₁₂`. -/
abbrev kerQ₁₂ := kerMap K.π₂ K.π₃ K.q₁₂ K.q₁₂' K.q₁₂_π
/-- The kernel map `J₂ → J₃` along `q₂₃`. -/
abbrev kerQ₂₃ := kerMap K.π₂ K.π₃ K.q₂₃ K.q₂₃' K.q₂₃_π
/-- The kernel map `J₂ → J₃` along `q₁₃`. -/
abbrev kerQ₁₃ := kerMap K.π₂ K.π₃ K.q₁₃ K.q₁₃' K.q₁₃_π

/-- The identity `q₁₂ ∘ p₂ ∘ u' = q₂₃ ∘ p₁ ∘ u'` of frames over `B₃`. -/
lemma q₁₂_v₂ : (ah K.q₁₂).comp (v₂ u') = (ah K.q₂₃).comp (v₁ u') := by
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, ← ah_comp, ← ah_comp, K.p₂_q₁₂]

/-- The frames `q₂₃ ∘ p₁ ∘ u'` and `q₂₃ ∘ lift₂` represent one point of `X` over `B₃`. -/
lemma pt_q₂₃_v₁_eq : Φ.pt K.B₃ ((ah K.q₂₃).comp (v₁ u')) =
    Φ.pt K.B₃ ((ah K.q₂₃).comp (lift₂ hū u' hu')) := by
  rw [Φ.pt_comp K.q₂₃ (v₁ u'), Φ.pt_comp K.q₂₃ (lift₂ hū u' hu'), pt_lift₂]

/-- **The cocycle identity of the defect over `B₃`.** -/
theorem defect_cocycle (r : R) :
    ah K.q₁₃ (defect hū u' hu' r) = ah K.q₂₃ (defect hū u' hu' r) +
      Φ.transportFun K.hJ₃ (pt_q₂₃_v₁_eq hū u' hu')
        (((defect hū u' hu').map (ah K.q₁₂) (kerQ₁₂ (K := K))).cast (q₁₂_v₂ u')) r := by
  set D₁₂ := ((defect hū u' hu').map (ah K.q₁₂) (kerQ₁₂ (K := K))).cast (q₁₂_v₂ u')
  set T := Φ.transportFun K.hJ₃ (pt_q₂₃_v₁_eq hū u' hu') D₁₂
  have hq₁₂ : (ah K.q₁₂).comp (lift₂ hū u' hu') = DerAlong.addHom K.J₃ K.π₃_sq D₁₂ :=
    AlgHom.ext fun r ↦ by
      have := congrArg (fun φ : R →ₐ[A'] K.B₃.obj ↦ φ r) (q₁₂_v₂ u')
      simp only [AlgHom.comp_apply] at this
      simp only [AlgHom.comp_apply, DerAlong.addHom_apply, D₁₂, DerAlong.cast_apply,
        DerAlong.map_apply, coe_kerMap, coe_defect_apply, map_sub, ← this]
      abel
  have hv₁ : (ah K.π₃).comp ((ah K.q₁₃).comp (v₁ u')) = (ah K.q₁₃').comp ((ah K.p₁').comp ū) :=
    AlgHom.ext fun r ↦ by
      rw [← hu']
      simp only [AlgHom.comp_apply, ah_comm K.q₁₃_π, ah_comm K.p₁_π]
  have hlift : (ah K.π₃).comp ((ah K.q₁₃).comp (lift₂ hū u' hu')) =
      (ah K.q₁₃').comp ((ah K.p₂').comp ū) := AlgHom.ext fun r ↦ by
    have := congrArg (fun φ : R →ₐ[A'] K.B₂'.obj ↦ ah K.q₁₃' (φ r)) (π₂_lift₂ hū u' hu')
    simp only [AlgHom.comp_apply] at this ⊢
    rw [ah_comm K.q₁₃_π, this]
  have hpt : Φ.pt K.B₃' ((ah K.q₁₃').comp ((ah K.p₂').comp ū)) =
      X.map K.π₃ (Φ.pt K.B₃ ((ah K.q₁₃).comp (v₁ u'))) := by
    rw [← Φ.pt_comp, hv₁, Φ.pt_comp K.q₁₃' ((ah K.p₁').comp ū),
      Φ.pt_comp K.q₁₃' ((ah K.p₂').comp ū), pt_p₁'_eq_pt_p₂' Φ K x ū hū]
  have hπ : ∀ w : R →ₐ[A'] K.B₃.obj, (ah K.π₃).comp w = (ah K.q₁₃').comp ((ah K.p₂').comp ū) →
      Φ.pt K.B₃ w = Φ.pt K.B₃ ((ah K.q₁₃).comp (v₁ u')) →
      w = (ah K.q₁₃).comp (lift₂ hū u' hu') := by
    intro w h₁ h₂
    have hl := Φ.existsUnique_lift K.π₃ K.π₃_surj K.π₃_sq (Φ.pt K.B₃ ((ah K.q₁₃).comp (v₁ u')))
      ((ah K.q₁₃').comp ((ah K.p₂').comp ū)) hpt
    refine hl.unique ⟨h₁, h₂⟩ ⟨hlift, ?_⟩
    rw [Φ.pt_comp K.q₁₃ (lift₂ hū u' hu'), Φ.pt_comp K.q₁₃ (v₁ u'), pt_lift₂]
  have hkey : DerAlong.addHom K.J₃ K.π₃_sq T = (ah K.q₁₃).comp (lift₂ hū u' hu') := by
    refine hπ _ ?_ ?_
    · refine (comp_addHom_of_ker K.π₃ K.π₃_sq T).trans (AlgHom.ext fun r ↦ ?_)
      have h₁ := congrArg (fun φ : R →ₐ[A'] K.B₂'.obj ↦ ah K.q₂₃' (φ r)) (π₂_lift₂ hū u' hu')
      simp only [AlgHom.comp_apply] at h₁ ⊢
      rw [ah_comm K.q₂₃_π, h₁, ah_comm K.p₂_q₂₃']
    · have e₁ : Φ.pt K.B₃ ((ah K.q₁₂).comp (lift₂ hū u' hu')) =
          Φ.pt K.B₃ ((ah K.q₁₃).comp (v₁ u')) := by
        rw [Φ.pt_comp K.q₁₂ (lift₂ hū u' hu'), pt_lift₂, ← Φ.pt_comp]
        exact congrArg (Φ.pt K.B₃) (AlgHom.ext fun r ↦ ah_comm K.p₁_q₁₂ (u' r))
      rw [← Φ.pt_addHom_transportFun K.J₃ K.π₃_sq K.hJ₃, ← hq₁₂, e₁]
  have hv : (ah K.q₁₃).comp (v₂ u') = (ah K.q₂₃).comp (v₂ u') := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, ← ah_comp, ← ah_comp, K.p₂_q₂₃]
  have h₁ := congrArg (fun φ : R →ₐ[A'] K.B₃.obj ↦ φ r) hkey
  have h₂ := congrArg (fun φ : R →ₐ[A'] K.B₃.obj ↦ φ r) hv
  simp only [AlgHom.comp_apply, DerAlong.addHom_apply] at h₁ h₂
  rw [coe_defect_apply, map_sub, map_sub, ← h₁]
  show _ - ah K.q₁₃ (v₂ u' r) = _
  rw [show ah K.q₁₃ (v₂ u' r) = ah K.q₂₃ (v₂ u' r) from h₂]
  abel

end CechCover

end Stacks.ChartGlue

end
