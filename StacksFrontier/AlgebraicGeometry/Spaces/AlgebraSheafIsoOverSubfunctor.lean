module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubalgebras

/-!
# Morphisms of algebra sheaves which are isomorphisms over a subspace

A morphism of algebra sheaves on an algebraic space is an isomorphism over a subfunctor `V` of
the space when it is an isomorphism on the sections over every affine étale chart factoring
through `V`; this is the condition `𝒜ᵢ|_V = 𝒜|_V` of [Stacks, Tag 0GUM]. This file develops the
basic calculus of this condition and shows that precomposition with such a morphism is a
bijection onto the morphisms into an algebra sheaf which only sees `V`.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver`: a morphism of algebra sheaves is an
  isomorphism on the sections over every affine étale chart which factors through a given
  subfunctor `V` of the space.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isIsoOver_of_bijective` and
  `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.bijective`: being an isomorphism over `V` is
  exactly bijectivity of the sections over every affine étale chart factoring through `V`.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.id`,
  `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.comp` and
  `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.of_comp`: the identity is an isomorphism over
  `V`, the condition is stable under composition, and it is left-cancellable.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.mono_subfunctor`: the condition is antitone in
  `V`.
* `AlgebraicGeometry.Space.AlgebraSheaf.IsIsoOver.of_subobject_le`: the condition is upward closed
  among subobjects.
* `AlgebraicGeometry.Space.AlgebraSheaf.bijective_comp_of_gluesOn`: given, for every chart `U`,
  a presieve `R U` of charts on which `a : 𝒜₁ ⟶ 𝒜₂` is bijective, stable under composition with
  morphisms of charts, precomposition with `a` is a bijection onto the morphisms `𝒜₁ ⟶ 𝒢` for
  every algebra sheaf `𝒢` which is separated along `R` and glues along it
  (`AlgebraicGeometry.Space.AlgebraSheaf.IsSeparatedOn` and
  `AlgebraicGeometry.Space.AlgebraSheaf.GluesOn`).
* `AlgebraicGeometry.Space.AlgebraSheaf.bijective_comp_of_isIsoOver`: the case of the affine
  charts factoring through `V`: if `a` is an isomorphism over `V`, precomposition with `a` is a
  bijection onto the morphisms into every algebra sheaf which is a sheaf for the affine charts
  through `V` above each chart.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

/-- A morphism of algebra sheaves on `F` is an *isomorphism over* a subfunctor `V` of `F` when
it is an isomorphism on the sections over every affine étale chart of `F` which factors through
`V`. -/
def IsIsoOver {A₁ A₂ : AlgebraSheaf.{u, u} B S hS F hF} (V : Subfunctor F)
    (a : A₁ ⟶ A₂) : Prop :=
  ∀ U : SmallEtale B S hS F,
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
      Subfunctor.range U.obj.hom ≤ V →
        IsIso (a.right.hom.app (op U))

/-- **Bijectivity of the sections over the charts in `V` gives an isomorphism over `V`.** -/
theorem isIsoOver_of_bijective {A₁ A₂ : AlgebraSheaf.{u, u} B S hS F hF} {V : Subfunctor F}
    {a : A₁ ⟶ A₂}
    (h : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Subfunctor.range U.obj.hom ≤ V →
          Function.Bijective ((a.right.hom.app (op U)).hom)) :
    IsIsoOver V a := fun U hU hUV =>
  (ConcreteCategory.isIso_iff_bijective (a.right.hom.app (op U))).2 (h U hU hUV)

/-- **An isomorphism over `V` is bijective on the sections over the charts in `V`.** -/
theorem IsIsoOver.bijective {A₁ A₂ : AlgebraSheaf.{u, u} B S hS F hF} {V : Subfunctor F}
    {a : A₁ ⟶ A₂} (ha : IsIsoOver V a) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hUV : Subfunctor.range U.obj.hom ≤ V) :
    Function.Bijective ((a.right.hom.app (op U)).hom) :=
  have := ha U hU hUV
  ConcreteCategory.bijective_of_isIso (a.right.hom.app (op U))

/-- The identity is an isomorphism over every subfunctor. -/
theorem IsIsoOver.id (A : AlgebraSheaf.{u, u} B S hS F hF) (V : Subfunctor F) :
    IsIsoOver V (𝟙 A) := by
  intro U _ _
  have h : (𝟙 A : A ⟶ A).right.hom.app (op U) = 𝟙 (A.right.obj.obj (op U)) := rfl
  rw [h]
  infer_instance

/-- Isomorphisms over `V` are stable under composition. -/
theorem IsIsoOver.comp {A₁ A₂ A₃ : AlgebraSheaf.{u, u} B S hS F hF} {V : Subfunctor F}
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} (ha : IsIsoOver V a) (hb : IsIsoOver V b) :
    IsIsoOver V (a ≫ b) := by
  intro U hU hUV
  have := ha U hU hUV
  have := hb U hU hUV
  have h : (a ≫ b).right.hom.app (op U) =
      a.right.hom.app (op U) ≫ b.right.hom.app (op U) := rfl
  rw [h]
  infer_instance

/-- If `a ≫ b` and `b` are isomorphisms over `V`, so is `a`. -/
theorem IsIsoOver.of_comp {A₁ A₂ A₃ : AlgebraSheaf.{u, u} B S hS F hF}
    {V : Subfunctor F} {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃}
    (hab : IsIsoOver V (a ≫ b)) (hb : IsIsoOver V b) :
    IsIsoOver V a := by
  intro U hU hUV
  have := hb U hU hUV
  have : IsIso (a.right.hom.app (op U) ≫ b.right.hom.app (op U)) := hab U hU hUV
  exact IsIso.of_isIso_comp_right _ (b.right.hom.app (op U))

/-- Being an isomorphism over a subfunctor is antitone in that subfunctor. -/
theorem IsIsoOver.mono_subfunctor {A₁ A₂ : AlgebraSheaf.{u, u} B S hS F hF}
    {V V' : Subfunctor F} {a : A₁ ⟶ A₂} (hVV' : V ≤ V') (ha : IsIsoOver V' a) :
    IsIsoOver V a := fun U hU hUV => ha U hU (hUV.trans hVV')

/-- **Agreeing with `𝒜` over `V` is upward closed among the subobjects of `𝒜`.**  If the
inclusion of `C₀` into `𝒜` is an isomorphism over `V` and `C₀ ≤ C`, the inclusion of `C` is an
isomorphism over `V` too. -/
theorem IsIsoOver.of_subobject_le {A : AlgebraSheaf.{u, u} B S hS F hF} {V : Subfunctor F}
    {C₀ C : Subobject A} (hle : C₀ ≤ C) (h₀ : IsIsoOver V C₀.arrow) :
    IsIsoOver V C.arrow := by
  refine isIsoOver_of_bijective fun U hU hUV => ⟨injective_subobject_arrow_app C (op U), ?_⟩
  intro x
  obtain ⟨y, hy⟩ := (h₀.bijective U hU hUV).2 x
  refine ⟨((Subobject.ofLE _ _ hle).right.hom.app (op U)).hom y, ?_⟩
  calc (C.arrow.right.hom.app (op U)).hom
        (((Subobject.ofLE _ _ hle).right.hom.app (op U)).hom y)
      = ((Subobject.ofLE _ _ hle ≫ C.arrow).right.hom.app (op U)).hom y := rfl
    _ = (C₀.arrow.right.hom.app (op U)).hom y := by rw [Subobject.ofLE_arrow hle]
    _ = x := hy


/-! ### Morphisms into an algebra sheaf that only sees a family of charts -/

section Precomposition

variable {A₁ A₂ G : AlgebraSheaf.{u, u} B S hS F hF}

/-- `a` applied to the restriction of a section of `𝒜₁` is the restriction of `a` applied to it. -/
theorem app_map_apply (a : A₁ ⟶ A₂) {U W : SmallEtale B S hS F} (f : W ⟶ U)
    (t : A₁.right.obj.obj (op U)) :
    (a.right.hom.app (op W)).hom ((A₁.right.obj.map f.op).hom t) =
      (A₂.right.obj.map f.op).hom ((a.right.hom.app (op U)).hom t) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← NatTrans.naturality]

/-- **An algebra sheaf `𝒢` is separated for a family `R` of presieves**: a section over a chart
`U` is determined by its restrictions to the members of `R U`. -/
def IsSeparatedOn (G : AlgebraSheaf.{u, u} B S hS F hF)
    (R : ∀ U : SmallEtale B S hS F, Presieve U) : Prop :=
  ∀ (U : SmallEtale B S hS F) (s t : G.right.obj.obj (op U)),
    (∀ ⦃W : SmallEtale B S hS F⦄ (f : W ⟶ U), R U f →
      (G.right.obj.map f.op).hom s = (G.right.obj.map f.op).hom t) → s = t

/-- **An algebra sheaf `𝒢` glues along a family `R` of presieves**: a family of sections over the
members of `R U`, compatible along every pair of morphisms of charts, is the family of
restrictions of a section over `U`. -/
def GluesOn (G : AlgebraSheaf.{u, u} B S hS F hF)
    (R : ∀ U : SmallEtale B S hS F, Presieve U) : Prop :=
  ∀ (U : SmallEtale B S hS F)
    (x : ∀ ⦃W : SmallEtale B S hS F⦄ (f : W ⟶ U), R U f → G.right.obj.obj (op W)),
    (∀ ⦃W₁ W₂ Z : SmallEtale B S hS F⦄ (g₁ : Z ⟶ W₁) (g₂ : Z ⟶ W₂) (f₁ : W₁ ⟶ U)
      (f₂ : W₂ ⟶ U) (h₁ : R U f₁) (h₂ : R U f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        (G.right.obj.map g₁.op).hom (x f₁ h₁) = (G.right.obj.map g₂.op).hom (x f₂ h₂)) →
    ∃ s : G.right.obj.obj (op U), ∀ ⦃W : SmallEtale B S hS F⦄ (f : W ⟶ U) (hf : R U f),
      (G.right.obj.map f.op).hom s = x f hf

/-- Restricting twice is restricting along the composite. -/
theorem map_map_apply (A : AlgebraSheaf.{u, u} B S hS F hF) {U W Z : SmallEtale B S hS F}
    (f : W ⟶ U) (g : Z ⟶ W) (x : A.right.obj.obj (op U)) :
    (A.right.obj.map g.op).hom ((A.right.obj.map f.op).hom x) =
      (A.right.obj.map (g ≫ f).op).hom x := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

/-- Morphisms into a separated algebra sheaf agreeing after restriction to the members of `R U`
are equal. -/
private theorem hom_ext_of_isSeparatedOn {A : AlgebraSheaf.{u, u} B S hS F hF}
    {R : ∀ U : SmallEtale B S hS F, Presieve U} (hsep : G.IsSeparatedOn R) {φ ψ : A ⟶ G}
    (h : ∀ (U : SmallEtale B S hS F) (s : A.right.obj.obj (op U)) ⦃W : SmallEtale B S hS F⦄
      (f : W ⟶ U), R U f → (G.right.obj.map f.op).hom ((φ.right.hom.app (op U)).hom s) =
        (G.right.obj.map f.op).hom ((ψ.right.hom.app (op U)).hom s)) :
    φ = ψ := by
  refine Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
  obtain ⟨U⟩ := U
  exact CommRingCat.hom_ext (RingHom.ext fun s => hsep U _ _ fun W f hf => h U s f hf)

/-- For `χ : 𝒜₁ ⟶ 𝒢` and a chart `W` on whose sections `a : 𝒜₁ ⟶ 𝒜₂` is bijective, the ring
map from the sections of `𝒜₂` over `W` to those of `𝒢` sending `s` to `χ(a⁻¹(s))`. -/
noncomputable def precompValue (a : A₁ ⟶ A₂) (χ : A₁ ⟶ G) {W : SmallEtale B S hS F}
    (hW : Function.Bijective (a.right.hom.app (op W)).hom) :
    A₂.right.obj.obj (op W) →+* G.right.obj.obj (op W) :=
  (χ.right.hom.app (op W)).hom.comp (RingEquiv.ofBijective _ hW).symm.toRingHom

/-- `precompValue a χ hW` sends `a(t)` to `χ(t)`. -/
theorem precompValue_app (a : A₁ ⟶ A₂) (χ : A₁ ⟶ G) {W : SmallEtale B S hS F}
    (hW : Function.Bijective (a.right.hom.app (op W)).hom) (t : A₁.right.obj.obj (op W)) :
    precompValue a χ hW ((a.right.hom.app (op W)).hom t) = (χ.right.hom.app (op W)).hom t :=
  congrArg (χ.right.hom.app (op W)).hom ((RingEquiv.ofBijective _ hW).symm_apply_apply t)

/-- `precompValue` commutes with restriction along a morphism of charts `h : W' ⟶ W`. -/
theorem map_precompValue (a : A₁ ⟶ A₂) (χ : A₁ ⟶ G) {W W' : SmallEtale B S hS F}
    (hW : Function.Bijective (a.right.hom.app (op W)).hom)
    (hW' : Function.Bijective (a.right.hom.app (op W')).hom) (h : W' ⟶ W)
    (s : A₂.right.obj.obj (op W)) :
    (G.right.obj.map h.op).hom (precompValue a χ hW s) =
      precompValue a χ hW' ((A₂.right.obj.map h.op).hom s) := by
  obtain ⟨t, rfl⟩ := hW.2 s
  rw [precompValue_app, ← app_map_apply, ← app_map_apply a, precompValue_app]

variable (R : ∀ U : SmallEtale B S hS F, Presieve U)

/-- **Precomposition with a morphism of algebra sheaves which is bijective on a family of charts
is a bijection onto the morphisms into an algebra sheaf which only sees those charts.**

For every chart `U`, `R U` is a presieve of charts on whose sections `a : 𝒜₁ ⟶ 𝒜₂` is bijective,
and the family is stable under composition with morphisms of charts; `𝒢` is separated and glues
along `R`.  Then `φ ↦ a ≫ φ` is a bijection from the morphisms `𝒜₂ ⟶ 𝒢` onto the morphisms
`𝒜₁ ⟶ 𝒢`. -/
theorem bijective_comp_of_gluesOn
    (hR : ∀ ⦃U U' W : SmallEtale B S hS F⦄ (k : U' ⟶ U) (f : W ⟶ U'), R U' f → R U (f ≫ k))
    (a : A₁ ⟶ A₂)
    (ha : ∀ ⦃U W : SmallEtale B S hS F⦄ (f : W ⟶ U), R U f →
      Function.Bijective (a.right.hom.app (op W)).hom)
    (hsep : G.IsSeparatedOn R) (hglue : G.GluesOn R) :
    Function.Bijective (fun φ : A₂ ⟶ G => a ≫ φ) := by
  classical
  refine ⟨fun φ ψ hφψ => ?_, fun χ => ?_⟩
  · refine hom_ext_of_isSeparatedOn hsep fun U s W f hf => ?_
    obtain ⟨t, ht⟩ := (ha f hf).2 ((A₂.right.obj.map f.op).hom s)
    have hχ : ∀ θ : A₂ ⟶ G, (G.right.obj.map f.op).hom ((θ.right.hom.app (op U)).hom s) =
        ((a ≫ θ).right.hom.app (op W)).hom t := by
      intro θ
      change _ = (θ.right.hom.app (op W)).hom ((a.right.hom.app (op W)).hom t)
      rw [ht, app_map_apply]
    rw [hχ φ, hχ ψ, show a ≫ φ = a ≫ ψ from hφψ]
  · have hcompat : ∀ (U : SmallEtale B S hS F) (s : A₂.right.obj.obj (op U))
        ⦃W₁ W₂ Z : SmallEtale B S hS F⦄ (g₁ : Z ⟶ W₁) (g₂ : Z ⟶ W₂) (f₁ : W₁ ⟶ U)
        (f₂ : W₂ ⟶ U) (h₁ : R U f₁) (h₂ : R U f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
          (G.right.obj.map g₁.op).hom
              (precompValue a χ (ha f₁ h₁) ((A₂.right.obj.map f₁.op).hom s)) =
            (G.right.obj.map g₂.op).hom
              (precompValue a χ (ha f₂ h₂) ((A₂.right.obj.map f₂.op).hom s)) := by
      intro U s W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
      refine hsep Z _ _ fun W'' k hk => ?_
      rw [map_map_apply, map_map_apply, map_precompValue a χ _ (ha k hk),
        map_precompValue a χ _ (ha k hk), map_map_apply, map_map_apply, Category.assoc,
        Category.assoc, hcomm]
    choose glue hglue' using fun U s => hglue U
      (fun W f hf => precompValue a χ (ha f hf) ((A₂.right.obj.map f.op).hom s)) (hcompat U s)
    have hres : ∀ (U : SmallEtale B S hS F) (s) {W : SmallEtale B S hS F} (f : W ⟶ U)
        (hf : R U f), (G.right.obj.map f.op).hom (glue U s) =
          precompValue a χ (ha f hf) ((A₂.right.obj.map f.op).hom s) :=
      fun U s _ f hf => hglue' U s f hf
    let φU : ∀ U : SmallEtale B S hS F, A₂.right.obj.obj (op U) →+* G.right.obj.obj (op U) :=
      fun U =>
        { toFun := glue U
          map_one' := hsep U _ _ fun W f hf => by
            rw [hres U 1 f hf, map_one, map_one, map_one]
          map_mul' := fun s₁ s₂ => hsep U _ _ fun W f hf => by
            rw [map_mul, hres U _ f hf, hres U _ f hf, hres U _ f hf, map_mul, map_mul]
          map_zero' := hsep U _ _ fun W f hf => by
            rw [hres U 0 f hf, map_zero, map_zero, map_zero]
          map_add' := fun s₁ s₂ => hsep U _ _ fun W f hf => by
            rw [map_add, hres U _ f hf, hres U _ f hf, hres U _ f hf, map_add, map_add] }
    have hφU : ∀ (U : SmallEtale B S hS F) (s) {W : SmallEtale B S hS F} (f : W ⟶ U)
        (hf : R U f), (G.right.obj.map f.op).hom (φU U s) =
          precompValue a χ (ha f hf) ((A₂.right.obj.map f.op).hom s) := hres
    let φ : A₂.right ⟶ G.right :=
      ⟨{ app := fun U => CommRingCat.ofHom (φU U.unop)
         naturality := fun U U' k => by
           obtain ⟨U⟩ := U
           obtain ⟨U'⟩ := U'
           obtain ⟨k⟩ := k
           refine CommRingCat.hom_ext (RingHom.ext fun s => hsep U' _ _ fun W f hf => ?_)
           change (G.right.obj.map f.op).hom (φU U' ((A₂.right.obj.map k.op).hom s)) =
             (G.right.obj.map f.op).hom ((G.right.obj.map k.op).hom (φU U s))
           rw [map_map_apply, hφU U' _ f hf, hφU U s (f ≫ k) (hR k f hf), map_map_apply] }⟩
    refine ⟨⟨φ, fun U r => ?_⟩, ?_⟩
    · obtain ⟨U⟩ := U
      refine hsep U _ _ fun W f hf => ?_
      change (G.right.obj.map f.op).hom (φU U (A₂.algebraMap (op U) r)) =
        (G.right.obj.map f.op).hom (G.algebraMap (op U) r)
      rw [hφU U _ f hf, G.algebraMap_natural, A₂.algebraMap_natural, ← a.comm (op W),
        precompValue_app, χ.comm]
    · refine hom_ext_of_isSeparatedOn hsep fun U t W f hf => ?_
      change (G.right.obj.map f.op).hom (φU U ((a.right.hom.app (op U)).hom t)) =
        (G.right.obj.map f.op).hom ((χ.right.hom.app (op U)).hom t)
      rw [hφU U _ f hf, ← app_map_apply, precompValue_app, app_map_apply]

end Precomposition

/-- The presieve of the affine étale charts over `U` which factor through `V`. -/
def affineChartsOver (V : Subfunctor F) (U : SmallEtale B S hS F) : Presieve U :=
  fun W _ => IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
    Subfunctor.range W.obj.hom ≤ V

/-- **Precomposition with an isomorphism over `V` is a bijection onto the morphisms into an
algebra sheaf which only sees `V`**: one which is separated and glues along the presieves of the
affine charts factoring through `V`. -/
theorem bijective_comp_of_isIsoOver {A₁ A₂ G : AlgebraSheaf.{u, u} B S hS F hF}
    {V : Subfunctor F} {a : A₁ ⟶ A₂} (ha : IsIsoOver V a)
    (hsep : G.IsSeparatedOn (affineChartsOver V)) (hglue : G.GluesOn (affineChartsOver V)) :
    Function.Bijective (fun φ : A₂ ⟶ G => a ≫ φ) :=
  bijective_comp_of_gluesOn (affineChartsOver V) (fun _ _ _ _ _ hf => hf) a
    (fun _ W _ hf => ha.bijective W hf.1 hf.2) hsep hglue

end AlgebraSheaf

end AlgebraicGeometry.Space

end
