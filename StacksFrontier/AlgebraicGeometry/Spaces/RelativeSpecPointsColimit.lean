module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPoints

/-!
# The functor of points of the relative spectrum turns colimits of algebras into limits

Let `X` be an algebraic space over a scheme `S` and let `𝒜` be a sheaf of commutative
`𝒪_X`-algebras on its small étale site.  A point of the relative spectrum `\underline{Spec}_X(𝒜)`
with values in `T` is a point `x ∈ X(T)` together with a morphism of `𝒪_X`-algebras
`𝒜 ⟶ x_* 𝒪_T` (`AlgebraicGeometry.Space.relativeSpecPoints`).  Precomposition with a morphism of
algebras makes this presheaf contravariantly functorial in `𝒜`, and since a morphism out of a
colimit is a compatible family of morphisms out of its members, the functor so obtained carries a
colimit of algebras over a connected index to a limit of presheaves.  Connectedness is what makes
the underlying points of `X` of a compatible family agree.

This is the step `X = lim X_i` of the source's proofs of Stacks 09YC and Stacks 0GUM: there `X` is
the relative spectrum of `f_* 𝒪_X`, the stages are the relative spectra of the members of a
directed colimit presentation `f_* 𝒪_X = colim 𝒜ᵢ`, and no cardinality bound on the index is
needed, because the limit is computed on points.

## Main definitions

* `AlgebraicGeometry.Space.RelativeSpecPoint.comap`: precomposition of a point of the relative
  spectrum with a morphism of algebras.
* `AlgebraicGeometry.Space.relativeSpecPointsMap`: the induced morphism of presheaves, and
  `AlgebraicGeometry.Space.relativeSpecPointsFunctor` the functor
  `𝒜 ↦ \underline{Spec}_X(𝒜)` out of the opposite of the category of algebra sheaves.

## Main results

* `AlgebraicGeometry.Space.relativeSpecPointsMap_comp_π`: the morphism induced by a morphism of
  algebras lies over `X`.
* `AlgebraicGeometry.Space.isLimitMapConeRelativeSpecPointsFunctor`: the functor of points of
  the relative spectrum carries a colimit of algebra sheaves over a connected index to a limit of
  presheaves on the big fppf site.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-! ### Precomposition with a morphism of algebras -/

section Comap

variable {B S hS}

/-- **A point of the relative spectrum of `𝒜₂`, precomposed with a morphism `a : 𝒜₁ ⟶ 𝒜₂`**: the
point of `X` is kept, and the morphism `𝒜₂ ⟶ x_* 𝒪_T` becomes `a ≫ -`. -/
def RelativeSpecPoint.comap {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂)
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A₂ T) :
    RelativeSpecPoint B S hS A₁ T :=
  ⟨p.pt, a ≫ p.hom⟩

/-- Precomposition with a morphism of algebras keeps the underlying point of `X`. -/
@[simp]
theorem RelativeSpecPoint.comap_pt {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂)
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A₂ T) : (p.comap a).pt = p.pt :=
  rfl

/-- Precomposing the point `(x, α)` with `a` gives the point `(x, a ≫ α)`. -/
theorem RelativeSpecPoint.comap_mk {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂)
    {T : BigFppfOver B S hS} (x : X.1.obj (op T))
    (α : A₂ ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) :
    (⟨x, α⟩ : RelativeSpecPoint B S hS A₂ T).comap a = ⟨x, a ≫ α⟩ :=
  rfl

/-- The morphism of algebras of a precomposed point `p.comap a` is `a ≫ p.hom`. -/
theorem RelativeSpecPoint.comap_hom {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂)
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A₂ T) :
    (p.comap a).hom = a ≫ p.hom :=
  rfl

/-- Precomposition with the identity morphism of algebras is the identity. -/
@[simp]
theorem RelativeSpecPoint.comap_id {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A T) : p.comap (𝟙 A) = p := by
  obtain ⟨x, α⟩ := p
  simp only [RelativeSpecPoint.comap, Category.id_comp]

/-- Precomposition with a composite `a ≫ b` is precomposition with `b` followed by precomposition
with `a`. -/
theorem RelativeSpecPoint.comap_comp {A₁ A₂ A₃ : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A₃ T) :
    p.comap (a ≫ b) = (p.comap b).comap a := by
  obtain ⟨x, α⟩ := p
  simp only [RelativeSpecPoint.comap, Category.assoc]

/-- Precomposition with a morphism of algebras commutes with the composite with a map of direct
images.  Stated over arbitrary objects of `CategoryTheory.Over X`, where the kernel checks it at
once; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPoints`. -/
theorem compPushforwardAlgebraMap_comp_left {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (a : A₁ ⟶ A₂) {P Q : Over X} (α : A₂ ⟶ pushforwardAlgebra B S hS P) (f : Q ⟶ P) :
    compPushforwardAlgebraMap B S hS (a ≫ α) f = a ≫ compPushforwardAlgebraMap B S hS α f := by
  rw [compPushforwardAlgebraMap_def, compPushforwardAlgebraMap_def, Category.assoc]

/-- A point of the relative spectrum whose morphism of algebras is a composite
`compPushforwardAlgebraMap (a ≫ α) f`, rewritten as `a ≫ compPushforwardAlgebraMap α f`; stated
for a variable point and a variable morphism over `X`, so that the kernel never compares the two
composites at concrete objects. -/
theorem RelativeSpecPoint.mk_compPushforwardAlgebraMap_comp_left
    {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂) {T : BigFppfOver B S hS}
    {y : X.1.obj (op T)} {P : Over X} (α : A₂ ⟶ pushforwardAlgebra B S hS P)
    (f : specPointOver B S hS T y ⟶ P) :
    (⟨y, compPushforwardAlgebraMap B S hS (a ≫ α) f⟩ : RelativeSpecPoint B S hS A₁ T) =
      ⟨y, a ≫ compPushforwardAlgebraMap B S hS α f⟩ := by
  rw [compPushforwardAlgebraMap_comp_left]

/-- Precomposition with a morphism of algebras commutes with the pullback of points along a
morphism of the site. -/
theorem RelativeSpecPoint.map_comap {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (p : RelativeSpecPoint B S hS A₂ T) :
    (p.comap a).map B S hS g = (p.map B S hS g).comap a := by
  obtain ⟨x, α⟩ := p
  rw [RelativeSpecPoint.comap_mk, RelativeSpecPoint.map_mk, RelativeSpecPoint.map_mk,
    RelativeSpecPoint.comap_mk]
  exact RelativeSpecPoint.mk_compPushforwardAlgebraMap_comp_left a α (specPointOverMap B S hS g x)

/-- Two points of the relative spectrum with the same underlying point of `X` are equal as soon
as their morphisms of algebras are. -/
theorem RelativeSpecPoint.ext_of_pt_eq {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} {x : X.1.obj (op T)}
    {α β : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)}
    (h : (⟨x, α⟩ : RelativeSpecPoint B S hS A T) = ⟨x, β⟩) : α = β :=
  eq_of_heq (RelativeSpecPoint.mk.inj h).2

/-- Every point of the relative spectrum whose underlying point of `X` is `x` is of the form
`(x, β)`. -/
theorem RelativeSpecPoint.exists_eq_mk {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} (p : RelativeSpecPoint B S hS A T) {x : X.1.obj (op T)}
    (h : p.pt = x) :
    ∃ β : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x), p = ⟨x, β⟩ := by
  obtain ⟨y, α⟩ := p
  subst h
  exact ⟨α, rfl⟩

/-- If `p = (x, α)` and `p.comap f = (x, γ)`, then `f ≫ α = γ`. -/
private theorem comp_eq_of_comap_eq_mk {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {T : BigFppfOver B S hS} {p : RelativeSpecPoint B S hS A₂ T} {x : X.1.obj (op T)}
    {α : A₂ ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)} (hp : p = ⟨x, α⟩)
    {f : A₁ ⟶ A₂} {γ : A₁ ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)}
    (h : p.comap f = ⟨x, γ⟩) : f ≫ α = γ :=
  RelativeSpecPoint.ext_of_pt_eq ((congrArg (RelativeSpecPoint.comap f) hp.symm).trans h)

end Comap

/-! ### Functoriality of the relative spectrum in the algebra -/

section Functoriality

/-- **The morphism of relative spectra induced by a morphism of algebras** `a : 𝒜₁ ⟶ 𝒜₂`: it
sends a point `(x, α)` of `\underline{Spec}_X(𝒜₂)` to the point `(x, a ≫ α)` of
`\underline{Spec}_X(𝒜₁)`. -/
def relativeSpecPointsMap {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂) :
    relativeSpecPoints B S hS A₂ ⟶ relativeSpecPoints B S hS A₁ where
  app T := ↾fun p => (relativeSpecPointsEquiv B S hS A₁ T.unop).symm
    ((relativeSpecPointsEquiv B S hS A₂ T.unop p).comap a)
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply (relativeSpecPointsEquiv B S hS A₁ T'.unop).injective
    have h₁ := relativeSpecPointsEquiv_map B S hS A₁ g.unop
      ((relativeSpecPointsEquiv B S hS A₁ T.unop).symm
        ((relativeSpecPointsEquiv B S hS A₂ T.unop p).comap a))
    rw [Equiv.apply_symm_apply] at h₁
    change relativeSpecPointsEquiv B S hS A₁ T'.unop
        ((relativeSpecPointsEquiv B S hS A₁ T'.unop).symm
          ((relativeSpecPointsEquiv B S hS A₂ T'.unop
            ((relativeSpecPoints B S hS A₂).map g.unop.op p)).comap a)) =
      relativeSpecPointsEquiv B S hS A₁ T'.unop ((relativeSpecPoints B S hS A₁).map g.unop.op
        ((relativeSpecPointsEquiv B S hS A₁ T.unop).symm
          ((relativeSpecPointsEquiv B S hS A₂ T.unop p).comap a)))
    rw [Equiv.apply_symm_apply, h₁, relativeSpecPointsEquiv_map B S hS A₂ g.unop p,
      RelativeSpecPoint.map_comap]

/-- The values of `AlgebraicGeometry.Space.relativeSpecPointsMap` on points. -/
theorem relativeSpecPointsEquiv_relativeSpecPointsMap_app
    {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2} (a : A₁ ⟶ A₂) (T : BigFppfOver B S hS)
    (p : (relativeSpecPoints B S hS A₂).obj (op T)) :
    relativeSpecPointsEquiv B S hS A₁ T ((relativeSpecPointsMap B S hS a).app (op T) p) =
      (relativeSpecPointsEquiv B S hS A₂ T p).comap a :=
  Equiv.apply_symm_apply _ _

/-- **The morphism of relative spectra induced by a morphism of algebras lies over `X`.** -/
@[reassoc (attr := simp)]
theorem relativeSpecPointsMap_comp_π {A₁ A₂ : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (a : A₁ ⟶ A₂) :
    relativeSpecPointsMap B S hS a ≫ relativeSpecPointsπ B S hS A₁ =
      relativeSpecPointsπ B S hS A₂ := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun p => ?_)
  change (relativeSpecPointsπ B S hS A₁).app T ((relativeSpecPointsMap B S hS a).app T p) =
    (relativeSpecPointsπ B S hS A₂).app T p
  exact (relativeSpecPointsπ_app B S hS A₁ T.unop _).trans
    ((congrArg RelativeSpecPoint.pt
      (relativeSpecPointsEquiv_relativeSpecPointsMap_app B S hS a T.unop p)).trans
      (relativeSpecPointsπ_app B S hS A₂ T.unop p).symm)

/-- The morphism of relative spectra induced by the identity of an algebra is the identity. -/
theorem relativeSpecPointsMap_id (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    relativeSpecPointsMap B S hS (𝟙 A) = 𝟙 _ := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun p => ?_)
  apply (relativeSpecPointsEquiv B S hS A T.unop).injective
  exact (relativeSpecPointsEquiv_relativeSpecPointsMap_app B S hS (𝟙 A) T.unop p).trans
    (RelativeSpecPoint.comap_id _)

/-- The morphism of relative spectra induced by a composite `a ≫ b` of morphisms of algebras is the
composite of the morphisms induced by `b` and by `a`. -/
theorem relativeSpecPointsMap_comp {A₁ A₂ A₃ : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) :
    relativeSpecPointsMap B S hS (a ≫ b) =
      relativeSpecPointsMap B S hS b ≫ relativeSpecPointsMap B S hS a := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun p => ?_)
  apply (relativeSpecPointsEquiv B S hS A₁ T.unop).injective
  change relativeSpecPointsEquiv B S hS A₁ T.unop ((relativeSpecPointsMap B S hS (a ≫ b)).app T p) =
    relativeSpecPointsEquiv B S hS A₁ T.unop ((relativeSpecPointsMap B S hS a).app T
      ((relativeSpecPointsMap B S hS b).app T p))
  rw [relativeSpecPointsEquiv_relativeSpecPointsMap_app,
    relativeSpecPointsEquiv_relativeSpecPointsMap_app,
    relativeSpecPointsEquiv_relativeSpecPointsMap_app, RelativeSpecPoint.comap_comp]

variable (X) in
/-- **The relative spectrum as a functor of the algebra**, `𝒜 ↦ \underline{Spec}_X(𝒜)`, out of
the opposite of the category of algebra sheaves on `X` into the presheaves on the big fppf
site. -/
@[simps]
def relativeSpecPointsFunctor :
    (AlgebraSheaf.{u, u} B S hS X.1 X.2)ᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj A := relativeSpecPoints B S hS A.unop
  map a := relativeSpecPointsMap B S hS a.unop
  map_id A := relativeSpecPointsMap_id B S hS A.unop
  map_comp a b := relativeSpecPointsMap_comp B S hS b.unop a.unop

end Functoriality

/-! ### Colimits of algebras go to limits of relative spectra -/

section Limit

variable {J : Type*} [Category J] {D : J ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2}

/-- **The relative spectrum carries a colimit of algebras over a connected index to a limit of
presheaves**, evaluated at one object `T` of the site: a compatible family of points
`(xⱼ, αⱼ : 𝒜ⱼ ⟶ (xⱼ)_* 𝒪_T)` has one underlying point `x` of `X`, since the index is connected and
the transition maps keep the point, and then the `αⱼ` form a cocone, whose descent along the
colimit is the unique point of the relative spectrum of the colimit lying over the family. -/
theorem nonempty_isLimit_evaluation_mapCone_relativeSpecPointsFunctor [IsConnected J]
    {c : Cocone D} (hc : IsColimit c) (T : BigFppfOver B S hS) :
    Nonempty (IsLimit (((evaluation _ (Type u)).obj (op T)).mapCone
      ((relativeSpecPointsFunctor B S hS X).mapCone c.op))) := by
  classical
  rw [Types.isLimit_iff]
  intro s hs
  let q : ∀ j : J, RelativeSpecPoint B S hS (D.obj j) T := fun j =>
    relativeSpecPointsEquiv B S hS (D.obj j) T (s (op j))
  have hq : ∀ {j k : J} (φ : j ⟶ k), (q k).comap (D.map φ) = q j := fun φ =>
    (relativeSpecPointsEquiv_relativeSpecPointsMap_app B S hS (D.map φ) T _).symm.trans
      (congrArg _ (hs φ.op))
  have hpt : ∀ j k : J, (q j).pt = (q k).pt :=
    constant_of_preserves_morphisms (fun j => (q j).pt) fun _ _ φ =>
      (congrArg RelativeSpecPoint.pt (hq φ)).symm
  let j₀ : J := Classical.arbitrary J
  let x : X.1.obj (op T) := (q j₀).pt
  choose β hβ using fun j : J => (q j).exists_eq_mk (hpt j j₀)
  have hβnat : ∀ {j k : J} (φ : j ⟶ k), D.map φ ≫ β k = β j := fun {_ k} φ =>
    comp_eq_of_comap_eq_mk (hβ k) ((hq φ).trans (hβ _))
  let γ : Cocone D :=
    { pt := pushforwardAlgebra B S hS (specPointOver B S hS T x)
      ι := { app := β
             naturality := fun j k φ => (hβnat φ).trans (Category.comp_id _).symm } }
  have hval : ∀ (y : (relativeSpecPoints B S hS c.pt).obj (op T)) (j : J),
      relativeSpecPointsEquiv B S hS (D.obj j) T
          ((((evaluation _ (Type u)).obj (op T)).mapCone
            ((relativeSpecPointsFunctor B S hS X).mapCone c.op)).π.app (op j) y) =
        (relativeSpecPointsEquiv B S hS c.pt T y).comap (c.ι.app j) :=
    fun y j => relativeSpecPointsEquiv_relativeSpecPointsMap_app B S hS (c.ι.app j) T y
  refine ⟨(relativeSpecPointsEquiv B S hS c.pt T).symm ⟨x, hc.desc γ⟩, ?_, ?_⟩
  · rintro ⟨j⟩
    apply (relativeSpecPointsEquiv B S hS (D.obj j) T).injective
    rw [hval, Equiv.apply_symm_apply]
    change (⟨x, c.ι.app j ≫ hc.desc γ⟩ : RelativeSpecPoint B S hS (D.obj j) T) = q j
    rw [hc.fac γ j, hβ j]
  · intro (y : (relativeSpecPoints B S hS c.pt).obj (op T)) hy
    apply (relativeSpecPointsEquiv B S hS c.pt T).injective
    rw [Equiv.apply_symm_apply]
    have hy' : ∀ j : J, (relativeSpecPointsEquiv B S hS c.pt T y).comap (c.ι.app j) = q j :=
      fun j => (hval y j).symm.trans (congrArg _ (hy (op j)))
    have hypt : (relativeSpecPointsEquiv B S hS c.pt T y).pt = x := by
      rw [← RelativeSpecPoint.comap_pt (c.ι.app j₀), hy' j₀]
    obtain ⟨α, hα⟩ := (relativeSpecPointsEquiv B S hS c.pt T y).exists_eq_mk hypt
    rw [hα]
    congr 1
    refine hc.hom_ext fun j => ?_
    rw [hc.fac γ j]
    exact comp_eq_of_comap_eq_mk hα ((hy' j).trans (hβ j))

/-- **The functor of points of the relative spectrum carries a colimit of algebra sheaves over a
connected index to a limit of presheaves on the big fppf site.**  Limits of presheaves are
computed objectwise, and objectwise this is
`AlgebraicGeometry.Space.nonempty_isLimit_evaluation_mapCone_relativeSpecPointsFunctor`. -/
def isLimitMapConeRelativeSpecPointsFunctor [IsConnected J] {c : Cocone D} (hc : IsColimit c) :
    IsLimit ((relativeSpecPointsFunctor B S hS X).mapCone c.op) :=
  evaluationJointlyReflectsLimits _ fun T =>
    (nonempty_isLimit_evaluation_mapCone_relativeSpecPointsFunctor B S hS hc T.unop).some

end Limit

end AlgebraicGeometry.Space

end
