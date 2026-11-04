module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsDescent

/-!
# Base change of the bijection between sections and invertible quotients

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `ℰ` an `𝒪_X`-module, and `π : P ⟶ X`,
`π' : P' ⟶ X'` morphisms whose points at schemes represent the invertible quotients of the
pullbacks of `ℰ` and of `g^*ℰ`.  The identification `x'^* g^* ℰ ≅ (g ∘ x')^* ℰ` at every scheme
point `x'` of `X'` gives a morphism `b : P' ⟶ P` over `g`, and the bijections between sections and
invertible quotients of `AlgebraicGeometry.Space.sectionsEquivOfPointsEquiv` commute with base
change along `g`: a section of `π'` lying over a section of `π` corresponds to the pullback of the
invertible quotient the latter corresponds to.

## Main definitions

* `AlgebraicGeometry.Space.baseChangePointOfPointsEquiv`: the point of `P` over `g ∘ x'` attached
  to a point of `P'` over `x'`.
* `AlgebraicGeometry.Space.baseChangeHomOfPointsEquiv`: the morphism `b : P' ⟶ P` over `g`.

## Main results

* `AlgebraicGeometry.Space.baseChangeHomOfPointsEquiv_comp`: `b ≫ π = π' ≫ g`.
* `AlgebraicGeometry.Space.sectionsEquivOfPointsEquiv_baseChange`: the base-change compatibility
  of the bijection.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2)
  {P P' : AlgebraicSpaces B S hS} (π : P ⟶ X) (π' : P' ⟶ X')
  (e : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
    {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x} ≃
      InvertibleQuotientClass (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom x)).obj E))
  (he : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
    (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x}),
    e T' (yoneda.map h ≫ x) ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp π.hom h u⟩ =
      invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).app E).symm (e T x u))
  (e' : ∀ (T : BigFppfOver B S hS) (x' : yoneda.obj T ⟶ X'.1),
    {u : yoneda.obj T ⟶ P'.1 // u ≫ π'.hom = x'} ≃
      InvertibleQuotientClass (yonedaSpace B S hS T)
        ((modulePullback B S hS (pointHom x')).obj ((modulePullback B S hS g).obj E)))
  (he' : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (x' : yoneda.obj T ⟶ X'.1)
    (u : {u : yoneda.obj T ⟶ P'.1 // u ≫ π'.hom = x'}),
    e' T' (yoneda.map h ≫ x') ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp π'.hom h u⟩ =
      invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x')).app
          ((modulePullback B S hS g).obj E)).symm (e' T x' u))

/-- The identification `(g ∘ x')^* ℰ ≅ x'^* g^* ℰ` at a scheme point `x'` of `X'`. -/
abbrev pointCompIso (T : BigFppfOver B S hS) (x' : yoneda.obj T ⟶ X'.1) :
    (modulePullback B S hS (pointHom (x' ≫ g.hom))).obj E ≅
      (modulePullback B S hS (pointHom x')).obj ((modulePullback B S hS g).obj E) :=
  ((modulePullbackCompIso B S hS (pointHom x') g).app E).symm

/-- **The point of `P` over `g ∘ x'` attached to a point of `P'` over `x'`**: the one
corresponding to the same invertible quotient, read through `x'^* g^* ℰ ≅ (g ∘ x')^* ℰ`. -/
def baseChangePointOfPointsEquiv (T : BigFppfOver B S hS) (x' : yoneda.obj T ⟶ X'.1)
    (v : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = x'}) :
    {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x' ≫ g.hom} :=
  (e T (x' ≫ g.hom)).symm (invertibleQuotientTransportClass (pointCompIso g E T x') (e' T x' v))

/-- The point of `P` attached to a point of `P'` depends only on the point, not on the spelling of
the point of `X'` it lies over. -/
theorem baseChangePointOfPointsEquiv_congr (T : BigFppfOver B S hS) {x₁ x₂ : yoneda.obj T ⟶ X'.1}
    (hx : x₁ = x₂) (v₁ : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = x₁})
    (v₂ : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = x₂}) (hv : v₁.1 = v₂.1) :
    (baseChangePointOfPointsEquiv g E π π' e e' T x₁ v₁).1 =
      (baseChangePointOfPointsEquiv g E π π' e e' T x₂ v₂).1 := by
  subst hx
  obtain rfl : v₁ = v₂ := Subtype.ext hv
  rfl

/-- The associativity coherence of the composition comparison of Stacks 03LU, with the two
composites given under other names: the identifications along those names are carried by
morphisms `ε₁`, `ε₂`, `ε₃` that are the canonical ones. -/
theorem modulePullbackCompIso_assoc_inv_app_of_eq {W Y Y' Y'' : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'') (ab : W ⟶ Y') (hab : a ≫ b = ab) (bc : Y ⟶ Y'')
    (hbc : b ≫ c = bc) (M : Modules.{u, u} B S hS Y''.1 Y''.2)
    (ε₁ : (modulePullback B S hS bc).obj M ⟶ (modulePullback B S hS (b ≫ c)).obj M)
    (hε₁ : ε₁ = eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M) hbc.symm))
    (ε₂ : (modulePullback B S hS (a ≫ bc)).obj M ⟶ (modulePullback B S hS (ab ≫ c)).obj M)
    (hε₂ : ε₂ = eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M)
      (by rw [← hab, ← hbc, Category.assoc])))
    (ε₃ : (modulePullback B S hS ab).obj ((modulePullback B S hS c).obj M) ⟶
      (modulePullback B S hS (a ≫ b)).obj ((modulePullback B S hS c).obj M))
    (hε₃ : ε₃ = eqToHom (congrArg (fun k => (modulePullback B S hS k).obj
      ((modulePullback B S hS c).obj M)) hab.symm)) :
    (modulePullbackCompIso B S hS a bc).inv.app M ≫
        (modulePullback B S hS a).map (ε₁ ≫ (modulePullbackCompIso B S hS b c).inv.app M) =
      ε₂ ≫ (modulePullbackCompIso B S hS ab c).inv.app M ≫ ε₃ ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) := by
  subst hab hbc hε₁ hε₂ hε₃
  simp only [eqToHom_refl, Category.id_comp]
  exact (modulePullbackCompIso_assoc_inv_app B S hS a b c M).symm

/-- The comparison of pullbacks along a scheme point and along a morphism of test objects, in the
two orders: the associativity coherence of Stacks 03LU at `(yoneda h, x', g)`. -/
theorem pointCompIso_natural (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (x' : yoneda.obj T ⟶ X'.1) (x'' : yoneda.obj T' ⟶ X'.1) (hx : yoneda.map h ≫ x' = x'')
    (h₁ : (modulePullback B S hS (pointHom (x'' ≫ g.hom))).obj E =
      (modulePullback B S hS (pointHom (yoneda.map h ≫ x' ≫ g.hom))).obj E)
    (h₂ : (modulePullback B S hS (pointHom x'')).obj ((modulePullback B S hS g).obj E) =
      (modulePullback B S hS (pointHom (yoneda.map h ≫ x'))).obj ((modulePullback B S hS g).obj E))
    (z : InvertibleQuotientClass (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom x')).obj ((modulePullback B S hS g).obj E))) :
    invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        (eqToIso h₁ ≪≫ ((modulePullbackCompIso B S hS (yonedaSpaceMap h)
          (pointHom (x' ≫ g.hom))).app E).symm)
        (invertibleQuotientTransportClass (pointCompIso g E T x') z) =
      invertibleQuotientTransportClass (pointCompIso g E T' x'')
        (invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
          (eqToIso h₂ ≪≫ ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x')).app
            ((modulePullback B S hS g).obj E)).symm) z) := by
  subst hx
  rw [invertibleQuotientBaseChangeClass_transportClass,
    invertibleQuotientTransportClass_baseChangeClass]
  refine congrArg (fun i => invertibleQuotientBaseChangeClass (yonedaSpaceMap h) i z) (Iso.ext ?_)
  show eqToHom h₁ ≫ (modulePullbackCompIso B S hS (yonedaSpaceMap h)
      (pointHom (x' ≫ g.hom))).inv.app E ≫
      (modulePullback B S hS (yonedaSpaceMap h)).map
        ((modulePullbackCompIso B S hS (pointHom x') g).inv.app E) =
    (modulePullbackCompIso B S hS (pointHom (yoneda.map h ≫ x')) g).inv.app E ≫ eqToHom h₂ ≫
      (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x')).inv.app
        ((modulePullback B S hS g).obj E)
  rw [show eqToHom h₁ = 𝟙 _ from rfl, show eqToHom h₂ = 𝟙 _ from rfl]
  have key := modulePullbackCompIso_assoc_inv_app_of_eq (yonedaSpaceMap h) (pointHom x') g
    (pointHom (yoneda.map h ≫ x')) rfl (pointHom (x' ≫ g.hom)) rfl E (𝟙 _) rfl (𝟙 _) rfl
    (𝟙 _) rfl
  simp only [Category.id_comp] at key ⊢
  exact key

/-- Restricting along `h : T' ⟶ T` commutes with the correspondence between a point `u` of `P` and
a point `v` of `P'` whose classes agree after transport along `x'^* g^* ℰ ≅ (g ∘ x')^* ℰ`. -/
private theorem restrict_transport_e'_eq_e
    (he : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)
      (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x}),
      e T' (yoneda.map h ≫ x) ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp π.hom h u⟩ =
        invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
          ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).app E).symm (e T x u))
    (he' : ∀ (T T' : BigFppfOver B S hS) (h : T' ⟶ T) (x' : yoneda.obj T ⟶ X'.1)
      (u : {u : yoneda.obj T ⟶ P'.1 // u ≫ π'.hom = x'}),
      e' T' (yoneda.map h ≫ x') ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp π'.hom h u⟩ =
        invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
          ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x')).app
            ((modulePullback B S hS g).obj E)).symm (e' T x' u))
    (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (x' : yoneda.obj T ⟶ X'.1) (x'' : yoneda.obj T' ⟶ X'.1) (hx : yoneda.map h ≫ x' = x'')
    (u : {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x' ≫ g.hom})
    (v : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = x'})
    (huv : invertibleQuotientTransportClass (pointCompIso g E T x') (e' T x' v) =
      e T (x' ≫ g.hom) u) :
    e T' (x'' ≫ g.hom) ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp_of_eq π.hom h
        (by rw [← hx, Category.assoc]) u⟩ =
      invertibleQuotientTransportClass (pointCompIso g E T' x'')
        (e' T' x'' ⟨yoneda.map h ≫ v.1, yoneda_map_comp_point_comp_of_eq π'.hom h hx v⟩) := by
  subst hx
  rw [pointsEquiv_natural_of_eq X E π e he T T' h (x' ≫ g.hom) _ (Category.assoc _ _ _).symm u,
    ← huv, pointsEquiv_natural_of_eq X' ((modulePullback B S hS g).obj E) π' e' he' T T' h x' _
      rfl v]
  exact pointCompIso_natural g E T T' h x' _ rfl rfl rfl _

include he he' in
/-- The point of `P` attached to a point `v` of `P'` is natural in the test object: its restriction
along `h : T' ⟶ T` is the point attached to the restriction of `v`. -/
theorem baseChangePointOfPointsEquiv_natural (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (v : yoneda.obj T ⟶ P'.1) :
    (baseChangePointOfPointsEquiv g E π π' e e' T' ((yoneda.map h ≫ v) ≫ π'.hom)
      ⟨yoneda.map h ≫ v, rfl⟩).1 =
      yoneda.map h ≫ (baseChangePointOfPointsEquiv g E π π' e e' T (v ≫ π'.hom) ⟨v, rfl⟩).1 :=
  congrArg Subtype.val ((Equiv.symm_apply_eq _).2 (restrict_transport_e'_eq_e g E π π' e e' he he'
    T T' h (v ≫ π'.hom) _ (Category.assoc _ _ _).symm _ ⟨v, rfl⟩
    (Equiv.apply_symm_apply _ _).symm).symm)

/-- **The morphism `P' ⟶ P` over `g`**, sending a point of `P'` to the point of `P` corresponding
to the same invertible quotient. -/
def baseChangeHomOfPointsEquiv : P' ⟶ P :=
  ObjectProperty.homMk (homOfPoints
    (fun T v => (baseChangePointOfPointsEquiv g E π π' e e' T (v ≫ π'.hom) ⟨v, rfl⟩).1)
    fun T T' h v => baseChangePointOfPointsEquiv_natural g E π π' e he e' he' T T' h v)

/-- The composite of a point `v` of `P'` with `b : P' ⟶ P` is the point of `P` attached to `v`. -/
theorem comp_baseChangeHomOfPointsEquiv_hom (T : BigFppfOver B S hS) (v : yoneda.obj T ⟶ P'.1) :
    v ≫ (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom =
      (baseChangePointOfPointsEquiv g E π π' e e' T (v ≫ π'.hom) ⟨v, rfl⟩).1 :=
  comp_homOfPoints
    (fun T v => (baseChangePointOfPointsEquiv g E π π' e e' T (v ≫ π'.hom) ⟨v, rfl⟩).1)
    (fun T T' h v => baseChangePointOfPointsEquiv_natural g E π π' e he e' he' T T' h v) T v

/-- The morphism `b : P' ⟶ P` lies over `g`: `b ≫ π = π' ≫ g`. -/
theorem baseChangeHomOfPointsEquiv_comp :
    baseChangeHomOfPointsEquiv g E π π' e he e' he' ≫ π = π' ≫ g := by
  ext1
  refine hom_ext_yoneda fun T v => ?_
  show v ≫ (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom ≫ π.hom =
    v ≫ π'.hom ≫ g.hom
  rw [← Category.assoc, comp_baseChangeHomOfPointsEquiv_hom,
    (baseChangePointOfPointsEquiv g E π π' e e' T (v ≫ π'.hom) ⟨v, rfl⟩).2, Category.assoc]

/-- **The bijection between sections and invertible quotients commutes with base change**: a
section `σ'` of `π'` lying over a section `σ` of `π` along `b : P' ⟶ P` corresponds to the pullback
along `g` of the class `σ` corresponds to. -/
theorem sectionsEquivOfPointsEquiv_baseChange (σ : {σ : X ⟶ P // σ ≫ π = 𝟙 X})
    (σ' : {σ' : X' ⟶ P' // σ' ≫ π' = 𝟙 X'})
    (comm : σ'.1 ≫ baseChangeHomOfPointsEquiv g E π π' e he e' he' = g ≫ σ.1) :
    sectionsEquivOfPointsEquiv X' ((modulePullback B S hS g).obj E) π' e' he' σ' =
      invertibleQuotientBaseChangeClass g (Iso.refl _)
        (sectionsEquivOfPointsEquiv X E π e he σ) := by
  rw [sectionsEquivOfPointsEquiv_eq_iff]
  intro T x'
  have hσ := (sectionsEquivOfPointsEquiv_eq_iff X E π e he σ _).1 rfl T (x' ≫ g.hom)
  have hb := comp_baseChangeHomOfPointsEquiv_hom g E π π' e he e' he' T (x' ≫ σ'.1.hom)
  have hcomm : (x' ≫ σ'.1.hom) ≫ (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom =
      (x' ≫ g.hom) ≫ σ.1.hom := by
    rw [Category.assoc, ← InducedCategory.comp_hom, comm, Category.assoc]; rfl
  refine invertibleQuotientTransportClass_injective (pointCompIso g E T x') ?_
  rw [invertibleQuotientTransportClass_baseChangeClass, invertibleQuotientBaseChangeClass_comp]
  have hpt : (⟨(x' ≫ g.hom) ≫ σ.1.hom,
      comp_section_comp π.hom (x' ≫ g.hom) (congrArg InducedCategory.Hom.hom σ.2)⟩ :
        {u : yoneda.obj T ⟶ P.1 // u ≫ π.hom = x' ≫ g.hom}) =
      baseChangePointOfPointsEquiv g E π π' e e' T x' ⟨x' ≫ σ'.1.hom,
        comp_section_comp π'.hom x' (congrArg InducedCategory.Hom.hom σ'.2)⟩ :=
    Subtype.ext (hcomm.symm.trans (hb.trans (baseChangePointOfPointsEquiv_congr g E π π' e e' T
      (comp_section_comp π'.hom x' (congrArg InducedCategory.Hom.hom σ'.2)) _ _ rfl)))
  rw [hpt, baseChangePointOfPointsEquiv, Equiv.apply_symm_apply] at hσ
  rw [hσ]
  refine congrArg (fun i => invertibleQuotientBaseChangeClass (pointHom (x' ≫ g.hom)) i
    (sectionsEquivOfPointsEquiv X E π e he σ)) (Iso.ext ?_)
  simp

/-! ### The square is cartesian -/

section Cartesian

variable (s : Limits.PullbackCone π.hom g.hom)

/-- The point of `P'` over `y ≫ s.snd` attached to a point `y` of the vertex of a cone over
`P ⟶ X ⟵ X'`: the one corresponding to the class of the point `y ≫ s.fst` of `P`. -/
def liftPointOfPointsEquiv (T : BigFppfOver B S hS) (y : yoneda.obj T ⟶ s.pt) :
    {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = y ≫ s.snd} :=
  (e' T (y ≫ s.snd)).symm (invertibleQuotientTransportClass (pointCompIso g E T (y ≫ s.snd)).symm
    (e T ((y ≫ s.snd) ≫ g.hom) ⟨y ≫ s.fst, (Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) s.condition).trans (Category.assoc _ _ _).symm)⟩))

/-- The invertible quotient class of the point `liftPointOfPointsEquiv` of `P'`, transported along
`x'^* g^* ℰ ≅ (g ∘ x')^* ℰ`, is the class of the point `y ≫ s.fst` of `P`. -/
theorem transport_e'_liftPointOfPointsEquiv (T : BigFppfOver B S hS) (y : yoneda.obj T ⟶ s.pt) :
    invertibleQuotientTransportClass (pointCompIso g E T (y ≫ s.snd))
        (e' T (y ≫ s.snd) (liftPointOfPointsEquiv g E π π' e e' s T y)) =
      e T ((y ≫ s.snd) ≫ g.hom) ⟨y ≫ s.fst, (Category.assoc _ _ _).trans
        ((congrArg (y ≫ ·) s.condition).trans (Category.assoc _ _ _).symm)⟩ := by
  rw [liftPointOfPointsEquiv, Equiv.apply_symm_apply, invertibleQuotientTransportClass_trans,
    Iso.self_symm_id, invertibleQuotientTransportClass_refl]

include he he' in
/-- The point of `P'` attached to a point `y` of the cone vertex is natural in the test object: its
restriction along `h : T' ⟶ T` is the point attached to the restriction of `y`. -/
theorem liftPointOfPointsEquiv_natural (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (y : yoneda.obj T ⟶ s.pt) :
    (liftPointOfPointsEquiv g E π π' e e' s T' (yoneda.map h ≫ y)).1 =
      yoneda.map h ≫ (liftPointOfPointsEquiv g E π π' e e' s T y).1 := by
  have h1 := restrict_transport_e'_eq_e g E π π' e e' he he' T T' h (y ≫ s.snd) _
    (Category.assoc _ _ _).symm _ (liftPointOfPointsEquiv g E π π' e e' s T y)
    (transport_e'_liftPointOfPointsEquiv g E π π' e e' s T y)
  have h2 := transport_e'_liftPointOfPointsEquiv g E π π' e e' s T' (yoneda.map h ≫ y)
  exact congrArg Subtype.val ((e' T' _).injective (invertibleQuotientTransportClass_injective _
    (h2.trans (congrArg (e T' _) (Subtype.ext (Category.assoc _ _ _))) |>.trans h1)))

/-- The morphism from the vertex of a cone over `P ⟶ X ⟵ X'` to `P'`. -/
def liftOfPointsEquiv : s.pt ⟶ P'.1 :=
  homOfPoints (fun T y => (liftPointOfPointsEquiv g E π π' e e' s T y).1)
    fun T T' h y => liftPointOfPointsEquiv_natural g E π π' e he e' he' s T T' h y

/-- The composite of a point `y` of the cone vertex with `liftOfPointsEquiv` is the point of `P'`
attached to `y`. -/
theorem comp_liftOfPointsEquiv (T : BigFppfOver B S hS) (y : yoneda.obj T ⟶ s.pt) :
    y ≫ liftOfPointsEquiv g E π π' e he e' he' s =
      (liftPointOfPointsEquiv g E π π' e e' s T y).1 :=
  comp_homOfPoints (fun T y => (liftPointOfPointsEquiv g E π π' e e' s T y).1)
    (fun T T' h y => liftPointOfPointsEquiv_natural g E π π' e he e' he' s T T' h y) T y

/-- The value of `b : P' ⟶ P` at a point of `P'` lying over a given point of `X'`. -/
theorem comp_baseChangeHomOfPointsEquiv_hom' (T : BigFppfOver B S hS) (x' : yoneda.obj T ⟶ X'.1)
    (v : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = x'}) :
    v.1 ≫ (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom =
      (baseChangePointOfPointsEquiv g E π π' e e' T x' v).1 :=
  (comp_baseChangeHomOfPointsEquiv_hom g E π π' e he e' he' T v.1).trans
    (baseChangePointOfPointsEquiv_congr g E π π' e e' T v.2 _ _ rfl)

/-- **The square `P' ⟶ P`, `P' ⟶ X'`, `P ⟶ X`, `X' ⟶ X` is cartesian**: `P' = X' ×_X P`. -/
theorem isPullback_baseChangeHomOfPointsEquiv :
    IsPullback (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom π'.hom π.hom g.hom := by
  have w : (baseChangeHomOfPointsEquiv g E π π' e he e' he').hom ≫ π.hom = π'.hom ≫ g.hom :=
    congrArg InducedCategory.Hom.hom (baseChangeHomOfPointsEquiv_comp g E π π' e he e' he')
  refine IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk w
    (fun s => liftOfPointsEquiv g E π π' e he e' he' s) (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_))
  · refine hom_ext_yoneda fun T y => ?_
    rw [← Category.assoc, comp_liftOfPointsEquiv,
      comp_baseChangeHomOfPointsEquiv_hom' g E π π' e he e' he' T (y ≫ s.snd),
      baseChangePointOfPointsEquiv, transport_e'_liftPointOfPointsEquiv g E π π' e e' s T y,
      Equiv.symm_apply_apply]
  · refine hom_ext_yoneda fun T y => ?_
    rw [← Category.assoc, comp_liftOfPointsEquiv]
    exact (liftPointOfPointsEquiv g E π π' e e' s T y).2
  · refine hom_ext_yoneda fun T y => ?_
    rw [comp_liftOfPointsEquiv]
    have hv : (y ≫ m) ≫ π'.hom = y ≫ s.snd := by rw [Category.assoc, hm₂]
    have hb := comp_baseChangeHomOfPointsEquiv_hom' g E π π' e he e' he' T (y ≫ s.snd)
      ⟨y ≫ m, hv⟩
    rw [Category.assoc, hm₁] at hb
    have hbp : baseChangePointOfPointsEquiv g E π π' e e' T (y ≫ s.snd) ⟨y ≫ m, hv⟩ =
        ⟨y ≫ s.fst, (Category.assoc _ _ _).trans
          ((congrArg (y ≫ ·) s.condition).trans (Category.assoc _ _ _).symm)⟩ :=
      Subtype.ext hb.symm
    have key : (⟨y ≫ m, hv⟩ : {v : yoneda.obj T ⟶ P'.1 // v ≫ π'.hom = y ≫ s.snd}) =
        liftPointOfPointsEquiv g E π π' e e' s T y := by
      rw [liftPointOfPointsEquiv, Equiv.eq_symm_apply]
      refine invertibleQuotientTransportClass_injective (pointCompIso g E T (y ≫ s.snd)) ?_
      rw [invertibleQuotientTransportClass_trans, Iso.self_symm_id,
        invertibleQuotientTransportClass_refl, ← hbp, baseChangePointOfPointsEquiv,
        Equiv.apply_symm_apply]
    exact congrArg Subtype.val key

end Cartesian

end AlgebraicGeometry.Space

end
