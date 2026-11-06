module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraOverOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecChartEval
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecPointsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalProperty

/-!
# A space affine over `Y` is the relative spectrum of its direct image, on points

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S`.  A point of `X` with
values in `T` lying over `y ∈ Y(T)` is a morphism `T ⟶ X` over `Y`, and by the universal property
of a space affine over `Y` (`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`) those are
the morphisms of `𝒪_Y`-algebras `f_* 𝒪_X ⟶ y_* 𝒪_T`.  So `X` is, as a presheaf over `Y`, the
functor of points `AlgebraicGeometry.Space.relativeSpecPoints` of `f_* 𝒪_X`.

This is the identification `X = \underline{Spec}_Y(f_* 𝒪_X)` the source's proof of Stacks 0GUM
starts from; combined with `AlgebraicGeometry.Space.isLimitMapConeRelativeSpecPointsFunctor` it
writes `X` as the limit of the relative spectra of a colimit presentation of `f_* 𝒪_X`, and with
`AlgebraicGeometry.Space.bijective_comp_pushforwardAlgebra_of_isIsoOver` it identifies the
preimages of `V` when the presentation is an isomorphism over `V`.

## Main definitions

* `AlgebraicGeometry.Space.pointHomOver`: a point `x ∈ X(T)` over `y`, as a morphism over `Y`.
* `AlgebraicGeometry.Space.toRelativeSpecPoints`: the morphism `X ⟶ \underline{Spec}_Y(f_* 𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.toRelativeSpecPoints_comp_π`: it lies over `Y`.
* `AlgebraicGeometry.Space.isIso_toRelativeSpecPoints`: it is an isomorphism when `f` is affine.
* `AlgebraicGeometry.Space.isPullback_relativeSpecPointsMap_of_isIsoOver`: the relative spectra of
  two algebras which agree over `V` have the same preimage of `V`.
* `AlgebraicGeometry.Space.isLimit_toRelativeSpecPointsCone_and_isPullback`: for `f` affine and a
  colimit presentation `f_* 𝒪_X = colim 𝒜ⱼ` over a connected index whose comparisons are
  isomorphisms over `V`, `X` is the limit of the relative spectra of the stages, over `Y`, with
  cartesian squares over `V`.  This is the geometric half of the source's proof of Stacks 0GUM;
  what it leaves to the algebra half is the presentation, and to Stacks 081W that the stages are
  algebraic spaces finite and of finite presentation over `Y`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### Points of `X` as morphisms over `Y` -/

/-- **A point `x ∈ X(T)` lying over `y ∈ Y(T)`, as a morphism over `Y`** from `T` with the point
`y` to `X` with `f`. -/
def pointHomOver {T : BigFppfOver B S hS} (x : X.1.obj (op T)) (y : Y.1.obj (op T))
    (hx : f.hom.app (op T) x = y) : specPointOver B S hS T y ⟶ Over.mk f :=
  Over.homMk (ObjectProperty.homMk (yonedaEquiv.symm x)) (by
    refine ObjectProperty.hom_ext _ ?_
    change yonedaEquiv.symm x ≫ f.hom = yonedaEquiv.symm y
    rw [yonedaEquiv_symm_naturality_right, hx])

/-- The underlying morphism `T ⟶ X` of the morphism over `Y` attached to a point `x ∈ X(T)` is
the Yoneda morphism of `x`. -/
@[simp]
theorem pointHomOver_left_hom {T : BigFppfOver B S hS} (x : X.1.obj (op T)) (y : Y.1.obj (op T))
    (hx : f.hom.app (op T) x = y) :
    (pointHomOver B S hS f x y hx).left.hom = yonedaEquiv.symm x :=
  rfl

/-- Every morphism over `Y` from `T` with the point `y` to `X` is the morphism of a point. -/
theorem eq_pointHomOver {T : BigFppfOver B S hS} {y : Y.1.obj (op T)}
    (k : specPointOver B S hS T y ⟶ Over.mk f) :
    ∃ hx : f.hom.app (op T) (yonedaEquiv k.left.hom) = y,
      k = pointHomOver B S hS f (yonedaEquiv k.left.hom) y hx := by
  have hw : k.left.hom ≫ f.hom = yonedaEquiv.symm y :=
    congrArg (fun m => m.hom) (Over.w k)
  refine ⟨?_, ?_⟩
  · rw [← yonedaEquiv_comp, hw, Equiv.apply_symm_apply]
  · refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    exact (Equiv.symm_apply_apply _ _).symm

/-! ### The morphism to the relative spectrum of the direct image -/

/-- The point of the relative spectrum of `f_* 𝒪_X` attached to a point `x ∈ X(T)`: its image
`f(x)` with the direct-image map of `x` as a morphism over `Y`. -/
def toRelativeSpecPoint {T : BigFppfOver B S hS} (x : X.1.obj (op T)) :
    RelativeSpecPoint B S hS (pushforwardAlgebra B S hS (Over.mk f)) T :=
  ⟨f.hom.app (op T) x, compPushforwardAlgebraMap B S hS (𝟙 _)
    (pointHomOver B S hS f x (f.hom.app (op T) x) rfl)⟩

/-- The point attached to `x`, read with an arbitrary name `y` for `f(x)`. -/
theorem toRelativeSpecPoint_eq {T : BigFppfOver B S hS} (x : X.1.obj (op T))
    (y : Y.1.obj (op T)) (hx : f.hom.app (op T) x = y) :
    toRelativeSpecPoint B S hS f x =
      ⟨y, compPushforwardAlgebraMap B S hS (𝟙 _) (pointHomOver B S hS f x y hx)⟩ :=
  RelativeSpecPoint.mk_comp_eq B S hS (𝟙 _) hx _ _ rfl

/-- The point of the relative spectrum attached to the restriction of `x` along `g : T' ⟶ T` is
the restriction along `g` of the point attached to `x`. -/
theorem toRelativeSpecPoint_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : X.1.obj (op T)) :
    toRelativeSpecPoint B S hS f (X.1.map g.op x) =
      (toRelativeSpecPoint B S hS f x).map B S hS g := by
  show _ = (⟨Y.1.map g.op (f.hom.app (op T) x), compPushforwardAlgebraMap B S hS
    (compPushforwardAlgebraMap B S hS (𝟙 _) (pointHomOver B S hS f x (f.hom.app (op T) x) rfl))
    (specPointOverMap B S hS g (f.hom.app (op T) x))⟩ :
      RelativeSpecPoint B S hS (pushforwardAlgebra B S hS (Over.mk f)) T')
  rw [← compPushforwardAlgebraMap_comp]
  refine RelativeSpecPoint.mk_comp_eq B S hS (𝟙 _)
    (NatTrans.naturality_apply f.hom g.op x) _ _ ?_
  refine ObjectProperty.hom_ext _ ?_
  show yonedaEquiv.symm (X.1.map g.op x) = yoneda.map g ≫ yonedaEquiv.symm x
  rw [yonedaEquiv_symm_naturality_left]

/-- **The morphism `X ⟶ \underline{Spec}_Y(f_* 𝒪_X)`** sending a point of `X` to its image in `Y`
with its direct-image map. -/
def toRelativeSpecPoints :
    X.1 ⟶ relativeSpecPoints B S hS (pushforwardAlgebra B S hS (Over.mk f)) where
  app T := ↾fun x => (relativeSpecPointsEquiv B S hS _ T.unop).symm
    (toRelativeSpecPoint B S hS f x)
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (relativeSpecPointsEquiv B S hS _ T'.unop).injective
    change relativeSpecPointsEquiv B S hS _ T'.unop ((relativeSpecPointsEquiv B S hS _ T'.unop).symm
        (toRelativeSpecPoint B S hS f (X.1.map g.unop.op x))) =
      relativeSpecPointsEquiv B S hS _ T'.unop ((relativeSpecPoints B S hS _).map g.unop.op
        ((relativeSpecPointsEquiv B S hS _ T.unop).symm (toRelativeSpecPoint B S hS f x)))
    rw [relativeSpecPointsEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      toRelativeSpecPoint_map]

/-- The morphism `AlgebraicGeometry.Space.toRelativeSpecPoints` sends a point `x ∈ X(T)` to the
point of the relative spectrum attached to `x`. -/
theorem relativeSpecPointsEquiv_toRelativeSpecPoints_app (T : BigFppfOver B S hS)
    (x : X.1.obj (op T)) :
    relativeSpecPointsEquiv B S hS _ T ((toRelativeSpecPoints B S hS f).app (op T) x) =
      toRelativeSpecPoint B S hS f x :=
  Equiv.apply_symm_apply _ _

/-- **The morphism to the relative spectrum lies over `Y`.** -/
@[reassoc (attr := simp)]
theorem toRelativeSpecPoints_comp_π :
    toRelativeSpecPoints B S hS f ≫ relativeSpecPointsπ B S hS _ = f.hom := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
  show (relativeSpecPointsπ B S hS _).app T ((toRelativeSpecPoints B S hS f).app T x) =
    f.hom.app T x
  rw [relativeSpecPointsπ_app, relativeSpecPointsEquiv_toRelativeSpecPoints_app]
  rfl

/-- For `X` affine over `Y`, a morphism over `Y` into `X` is determined by its direct-image map
composed with the identity; stated over a variable object of `CategoryTheory.Over Y`, so that the
kernel does not unfold the composite at a concrete one. -/
theorem eq_of_compPushforwardAlgebraMap_eq (hf : IsAffineHom B S hS f.hom) {P : Over Y}
    (k₁ k₂ : P ⟶ Over.mk f)
    (h : compPushforwardAlgebraMap B S hS (𝟙 _) k₁ = compPushforwardAlgebraMap B S hS (𝟙 _) k₂) :
    k₁ = k₂ := by
  rw [compPushforwardAlgebraMap_def, compPushforwardAlgebraMap_def, Category.id_comp,
    Category.id_comp] at h
  exact eq_of_pushforwardAlgebraMap_eq B S hS ⟨Over.mk f, hf⟩ h

/-- For `X` affine over `Y`, every morphism of algebras `f_* 𝒪_X ⟶ P_* 𝒪_P` is the direct-image
map of a morphism over `Y`, composed with the identity. -/
theorem compPushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm
    (Z : AffineOver B S hS Y) {P : Over Y}
    (α : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS P) :
    compPushforwardAlgebraMap B S hS (𝟙 _)
      ((overHomEquivPushforwardAlgebraHom B S hS P Z).symm α) = α := by
  rw [compPushforwardAlgebraMap_def, Category.id_comp,
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm]

variable {f} in
/-- **For an affine morphism `f`, `X` is the relative spectrum of `f_* 𝒪_X`**: the morphism
`AlgebraicGeometry.Space.toRelativeSpecPoints` is an isomorphism of presheaves.  At a point
`y ∈ Y(T)` this is the universal property
`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom` of the space `X` affine over `Y`. -/
theorem isIso_toRelativeSpecPoints (hf : IsAffineHom B S hS f.hom) :
    IsIso (toRelativeSpecPoints B S hS f) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun T => ?_
  obtain ⟨T⟩ := T
  rw [isIso_iff_bijective]
  refine ⟨fun x₁ x₂ h => ?_, fun p => ?_⟩
  · have h' := congrArg (relativeSpecPointsEquiv B S hS _ T) h
    change relativeSpecPointsEquiv B S hS _ T ((toRelativeSpecPoints B S hS f).app (op T) x₁) =
      relativeSpecPointsEquiv B S hS _ T ((toRelativeSpecPoints B S hS f).app (op T) x₂) at h'
    rw [relativeSpecPointsEquiv_toRelativeSpecPoints_app,
      relativeSpecPointsEquiv_toRelativeSpecPoints_app] at h'
    have hpt : f.hom.app (op T) x₁ = f.hom.app (op T) x₂ := congrArg RelativeSpecPoint.pt h'
    rw [toRelativeSpecPoint_eq B S hS f x₁ _ hpt] at h'
    have hk := eq_of_compPushforwardAlgebraMap_eq B S hS f hf _ _
      (RelativeSpecPoint.ext_of_pt_eq h')
    have h₁ := congrArg (fun k => yonedaEquiv k.left.hom) hk
    exact (Equiv.apply_symm_apply yonedaEquiv x₁).symm.trans
      (h₁.trans (Equiv.apply_symm_apply yonedaEquiv x₂))
  · have hsurj : ∀ q : RelativeSpecPoint B S hS (pushforwardAlgebra B S hS (Over.mk f)) T,
        ∃ x, toRelativeSpecPoint B S hS f x = q := by
      rintro ⟨y, α⟩
      obtain ⟨hx, hk⟩ := eq_pointHomOver B S hS f
        ((overHomEquivPushforwardAlgebraHom B S hS (specPointOver B S hS T y)
          ⟨Over.mk f, hf⟩).symm α)
      refine ⟨_, (toRelativeSpecPoint_eq B S hS f _ _ hx).trans ?_⟩
      rw [← hk, compPushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B S hS
        ⟨Over.mk f, hf⟩ α]
    obtain ⟨x, hx⟩ := hsurj (relativeSpecPointsEquiv B S hS _ T p)
    refine ⟨x, (relativeSpecPointsEquiv B S hS _ T).injective ?_⟩
    rw [relativeSpecPointsEquiv_toRelativeSpecPoints_app, hx]

/-! ### The preimage of an open subspace -/

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_IntegralFiniteSystemFixedOnOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_IntegralFiniteSystemFixedOnOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Preimage

variable {B S hS} {Z₁ Z₂ Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism over `Y` which is bijective on the points lying over `V` identifies the preimages
of `V`**: the square formed by `Z₂ ×_Y V ⟶ Z₂ ⟶ Z₁`, `Z₂ ×_Y V ⟶ V` and the structure morphisms
of `Z₁` and `V` is cartesian. -/
theorem isPullback_pullbackFst_comp_of_existsUnique (π₁ : Z₁ ⟶ Y') (π₂ : Z₂ ⟶ Y') (q : Z₂ ⟶ Z₁)
    (hq : q ≫ π₁ = π₂) (V : Subfunctor Y')
    (huniq : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (z₁ : Z₁.obj T), π₁.app T z₁ ∈ V.obj T →
      ∃! z₂ : Z₂.obj T, q.app T z₂ = z₁) :
    IsPullback (pullback.fst π₂ V.ι ≫ q) (pullback.snd π₂ V.ι) π₁ V.ι := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  have hb := (IsPullback.of_hasPullback π₂ V.ι).map ((evaluation _ (Type u)).obj T)
  rw [Types.isPullback_iff] at hb ⊢
  obtain ⟨w, inj₀, ex₀⟩ := hb
  have inj : ∀ x y : (Limits.pullback π₂ V.ι).obj T,
      (pullback.fst π₂ V.ι).app T x = (pullback.fst π₂ V.ι).app T y ∧
        (pullback.snd π₂ V.ι).app T x = (pullback.snd π₂ V.ι).app T y → x = y := inj₀
  have ex : ∀ (z : Z₂.obj T) (v : V.toFunctor.obj T), π₂.app T z = V.ι.app T v →
      ∃ x, (pullback.fst π₂ V.ι).app T x = z ∧ (pullback.snd π₂ V.ι).app T x = v := ex₀
  have hq' : ∀ z, π₁.app T (q.app T z) = π₂.app T z := fun z =>
    congrArg (fun k => k.app T z) hq
  have w' : ∀ x, π₂.app T ((pullback.fst π₂ V.ι).app T x) =
      V.ι.app T ((pullback.snd π₂ V.ι).app T x) := fun x => congrArg (fun k => k x) w
  refine ⟨?_, fun x y ⟨h₁, h₂⟩ => ?_, fun z₁ v h => ?_⟩
  · ext x
    exact (hq' _).trans (w' x)
  · change q.app T ((pullback.fst π₂ V.ι).app T x) = q.app T ((pullback.fst π₂ V.ι).app T y) at h₁
    have hmem : π₁.app T (q.app T ((pullback.fst π₂ V.ι).app T x)) ∈ V.obj T := by
      rw [hq', w']
      exact ((pullback.snd π₂ V.ι).app T x).2
    obtain ⟨z₂, -, hz₂⟩ := huniq T _ hmem
    exact inj x y ⟨(hz₂ _ rfl).trans (hz₂ _ h₁.symm).symm, h₂⟩
  · change π₁.app T z₁ = V.ι.app T v at h
    obtain ⟨z₂, hz₂, -⟩ := huniq T z₁ (h ▸ v.2)
    obtain ⟨x, hx₁, hx₂⟩ := ex z₂ v (by rw [← hq', hz₂, h])
    refine ⟨x, ?_, hx₂⟩
    show q.app T ((pullback.fst π₂ V.ι).app T x) = z₁
    rw [hx₁, hz₂]

end Preimage

/-! ### Relative spectra of algebras which agree over `V` -/

section IsoOver

variable {B S hS} {V : Subfunctor Y.1} (hV : IsOpenImmersion B S hS V.ι)

/-- A point `x ∈ Y(T)` lying in `V`, as a morphism `T ⟶ V`. -/
theorem specPointOver_factors {T : BigFppfOver B S hS} {x : Y.1.obj (op T)}
    (hx : x ∈ V.obj (op T)) :
    (yonedaEquiv.symm (⟨x, hx⟩ : V.toFunctor.obj (op T)) : yoneda.obj T ⟶ V.toFunctor) ≫ V.ι =
      (specPointOver B S hS T x).hom.hom :=
  yonedaEquiv_symm_naturality_right T V.ι _

include hV in
/-- **Precomposition with an isomorphism over `V` is a bijection on the points of the relative
spectra lying over `V`.** -/
theorem existsUnique_comap_of_isIsoOver {A₁ A₂ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    {a : A₁ ⟶ A₂} (ha : AlgebraSheaf.IsIsoOver V a) {T : BigFppfOver B S hS}
    (p : RelativeSpecPoint B S hS A₁ T) (hp : p.pt ∈ V.obj (op T)) :
    ∃! p₂ : RelativeSpecPoint B S hS A₂ T, p₂.comap a = p := by
  obtain ⟨x, α⟩ := p
  have hbij := bijective_comp_pushforwardAlgebra_of_isIsoOver hV
    (relativelyRepresentable_specPointOver B S hS T x) _ (specPointOver_factors hp) ha
  obtain ⟨β, hβ⟩ := hbij.2 α
  refine ⟨⟨x, β⟩, congrArg (RelativeSpecPoint.mk x) hβ, ?_⟩
  rintro ⟨x', β'⟩ h
  have hx : x' = x := congrArg RelativeSpecPoint.pt h
  subst hx
  have h' := RelativeSpecPoint.ext_of_pt_eq h
  exact congrArg (RelativeSpecPoint.mk x') (hbij.1 (h'.trans hβ.symm))

include hV in
/-- **The relative spectra of two algebras which agree over `V` have the same preimage of `V`**:
for `a : 𝒜₁ ⟶ 𝒜₂` an isomorphism over `V`, the square formed by
`Spec(𝒜₂) ×_Y V ⟶ Spec(𝒜₂) ⟶ Spec(𝒜₁)` and the open immersion `V ⟶ Y` is cartesian. -/
theorem isPullback_relativeSpecPointsMap_of_isIsoOver {A₁ A₂ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    {a : A₁ ⟶ A₂} (ha : AlgebraSheaf.IsIsoOver V a) :
    IsPullback (pullback.fst (relativeSpecPointsπ B S hS A₂) V.ι ≫ relativeSpecPointsMap B S hS a)
      (pullback.snd (relativeSpecPointsπ B S hS A₂) V.ι) (relativeSpecPointsπ B S hS A₁) V.ι := by
  refine isPullback_pullbackFst_comp_of_existsUnique _ _ _
    (relativeSpecPointsMap_comp_π B S hS a) V fun T z₁ hz₁ => ?_
  obtain ⟨T⟩ := T
  rw [relativeSpecPointsπ_app] at hz₁
  obtain ⟨p₂, hp₂, huniq⟩ := existsUnique_comap_of_isIsoOver hV ha _ hz₁
  refine ⟨(relativeSpecPointsEquiv B S hS A₂ T).symm p₂, ?_, fun z₂ hz₂ => ?_⟩
  · apply (relativeSpecPointsEquiv B S hS A₁ T).injective
    rw [relativeSpecPointsEquiv_relativeSpecPointsMap_app, Equiv.apply_symm_apply, hp₂]
  · apply (relativeSpecPointsEquiv B S hS A₂ T).injective
    rw [Equiv.apply_symm_apply]
    refine huniq _ (show RelativeSpecPoint.comap a _ = _ from ?_)
    rw [← relativeSpecPointsEquiv_relativeSpecPointsMap_app, hz₂]

end IsoOver

/-! ### The integral morphism as a limit, unchanged over `V` -/

section Assembly

variable {V : Subfunctor Y.1} (hV : IsOpenImmersion B S hS V.ι)

include hV in
/-- **The points of `X` over `V` are the points of the relative spectrum of a stage**: for
`a : 𝒜 ⟶ f_* 𝒪_X` an isomorphism over `V` and `f` affine, the composite
`X ⟶ Spec(f_* 𝒪_X) ⟶ Spec(𝒜)` is bijective on the points lying over `V`. -/
theorem existsUnique_toRelativeSpecPoints_comp_app (hf : IsAffineHom B S hS f.hom)
    {A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} {a : A ⟶ pushforwardAlgebra B S hS (Over.mk f)}
    (ha : AlgebraSheaf.IsIsoOver V a) (T : BigFppfOver B S hS)
    (z : (relativeSpecPoints B S hS A).obj (op T))
    (hz : (relativeSpecPointsπ B S hS A).app (op T) z ∈ V.obj (op T)) :
    ∃! x : X.1.obj (op T),
      (toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS a).app (op T) x = z := by
  have := isIso_toRelativeSpecPoints B S hS hf
  have hbij : Function.Bijective ((toRelativeSpecPoints B S hS f).app (op T)) :=
    (isIso_iff_bijective _).1 inferInstance
  rw [relativeSpecPointsπ_app] at hz
  obtain ⟨p₂, hp₂, huniq⟩ := existsUnique_comap_of_isIsoOver hV ha _ hz
  obtain ⟨x, hx⟩ := hbij.2 ((relativeSpecPointsEquiv B S hS _ T).symm p₂)
  have key : ∀ x' : X.1.obj (op T),
      (toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS a).app (op T) x' = z ↔
        relativeSpecPointsEquiv B S hS _ T ((toRelativeSpecPoints B S hS f).app (op T) x') =
          p₂ := by
    refine fun x' => ⟨fun h => ?_, fun h => ?_⟩
    · refine huniq _ (show RelativeSpecPoint.comap a _ = _ from ?_)
      rw [← relativeSpecPointsEquiv_relativeSpecPointsMap_app]
      exact congrArg _ h
    · apply (relativeSpecPointsEquiv B S hS A T).injective
      show relativeSpecPointsEquiv B S hS A T ((relativeSpecPointsMap B S hS a).app (op T)
        ((toRelativeSpecPoints B S hS f).app (op T) x')) = _
      rw [relativeSpecPointsEquiv_relativeSpecPointsMap_app, h, hp₂]
  refine ⟨x, (key x).2 (by rw [hx, Equiv.apply_symm_apply]), fun x' hx' => hbij.1 ?_⟩
  rw [hx]
  apply (relativeSpecPointsEquiv B S hS _ T).injective
  rw [Equiv.apply_symm_apply]
  exact (key x').1 hx'

variable {J : Type*} [Category J] [IsConnected J]
    {D : J ⥤ AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (ι : D ⟶ (Functor.const J).obj (pushforwardAlgebra B S hS (Over.mk f)))

/-- The cone over the relative spectra of the stages with vertex `X`. -/
def toRelativeSpecPointsCone : Cone (D.op ⋙ relativeSpecPointsFunctor B S hS Y) where
  pt := X.1
  π :=
    { app := fun j => toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS (ι.app j.unop)
      naturality := fun j k φ => by
        have h : D.map φ.unop ≫ ι.app j.unop = ι.app k.unop := by
          simp
        change 𝟙 _ ≫ toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS (ι.app k.unop) =
          (toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS (ι.app j.unop)) ≫
            relativeSpecPointsMap B S hS (D.map φ.unop)
        rw [Category.id_comp, Category.assoc, ← relativeSpecPointsMap_comp, h] }

include hV in
/-- **The source's proof of Stacks 0GUM, after its algebra step**: for `f : X ⟶ Y` affine, `V` an
open subspace of `Y`, and a colimit presentation `f_* 𝒪_X = colim 𝒜ⱼ` over a connected index whose
comparisons `𝒜ⱼ ⟶ f_* 𝒪_X` are isomorphisms over `V`, the space `X` is the limit of the relative
spectra `X_j = Spec(𝒜ⱼ)` of the stages, compatibly with the maps to `Y`, and every square formed by
`X ×_Y V ⟶ X ⟶ X_j`, `X ×_Y V ⟶ V`, `X_j ⟶ Y` and `V ⟶ Y` is cartesian. -/
theorem isLimit_toRelativeSpecPointsCone_and_isPullback (hf : IsAffineHom B S hS f.hom)
    (hι : IsColimit (Cocone.mk _ ι)) (hiso : ∀ j, AlgebraSheaf.IsIsoOver V (ι.app j)) :
    Nonempty (IsLimit (toRelativeSpecPointsCone B S hS f ι)) ∧
      (∀ j, (toRelativeSpecPointsCone B S hS f ι).π.app (op j) ≫
          relativeSpecPointsπ B S hS (D.obj j) = f.hom) ∧
      ∀ j, IsPullback (pullback.fst f.hom V.ι ≫ (toRelativeSpecPointsCone B S hS f ι).π.app (op j))
        (pullback.snd f.hom V.ι) (relativeSpecPointsπ B S hS (D.obj j)) V.ι := by
  have := isIso_toRelativeSpecPoints B S hS hf
  have hcomp : ∀ j, (toRelativeSpecPoints B S hS f ≫ relativeSpecPointsMap B S hS (ι.app j)) ≫
      relativeSpecPointsπ B S hS (D.obj j) = f.hom := fun j => by
    rw [Category.assoc, relativeSpecPointsMap_comp_π, toRelativeSpecPoints_comp_π]
  refine ⟨⟨(isLimitMapConeRelativeSpecPointsFunctor B S hS hι).ofIsoLimit
    (Cone.ext (asIso (toRelativeSpecPoints B S hS f)).symm fun j => ?_)⟩, hcomp,
    fun j => ?_⟩
  · show relativeSpecPointsMap B S hS (ι.app j.unop) =
      inv (toRelativeSpecPoints B S hS f) ≫ toRelativeSpecPoints B S hS f ≫
        relativeSpecPointsMap B S hS (ι.app j.unop)
    rw [IsIso.inv_hom_id_assoc]
  · refine isPullback_pullbackFst_comp_of_existsUnique _ _ _ (hcomp j) V fun T z hz => ?_
    obtain ⟨T⟩ := T
    exact existsUnique_toRelativeSpecPoints_comp_app B S hS f hV hf (hiso j) T z hz

end Assembly

end AlgebraicGeometry.Space

end
