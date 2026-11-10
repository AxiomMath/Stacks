module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# The relative spectrum over an affine base

Let `X` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The
relative spectrum of `A` is described by the functor sending a test scheme `T` to the set of
pairs `(f, φ)` consisting of a morphism `f : T ⟶ X` and an `𝒪_X`-algebra morphism
`φ : A ⟶ f_* 𝒪_T`. This file proves that when `X` is affine this functor is represented by the
spectrum of the ring `A(X)` of global sections of `A`.

## Main definitions

* `Stacks.RelativeSpec.RelativeSpecPair` is the set of pairs `(f, φ)` over a test scheme and
  `Stacks.RelativeSpec.relativeSpecFunctor` is the functor of such pairs; this is the functor
  in the displayed equation of [Stacks, Tag 01LR].
* `Stacks.RelativeSpec.affineHomEquiv` identifies morphisms into an affine scheme with ring
  maps on global sections.
* `Stacks.RelativeSpec.pairEquivRingHom` is the bijection carrying the content of Tag 01LT.

## Main results

* `Stacks.RelativeSpec.relativeSpecFunctor_representableBy` is Tag 01LT: over an affine base
  the functor of relative-spectrum pairs is represented by `Spec A(X)`.

## Implementation notes

The content is the bijection `pairEquivRingHom`, between the pairs `(f, φ)` over `T` and the
ring maps `A(X) ⟶ Γ(T, ⊤)`; it is then composed with the Spec-Γ adjunction in the form
`specHomEquiv`.

Both directions of that bijection rest on one localization fact. Since `A` is quasi-coherent
and `X` is affine, the restriction map `A(X) ⟶ A(X_a)` to a basic open exhibits `A(X_a)` as the
localization of `A(X)` away from the image of `a`: this is
`AlgebraSheaf.isLocalization_sections_basicOpen`, obtained from
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` through
`isLocalizedModule_iff_isLocalization`. Consequently a morphism `A ⟶ f_* 𝒪_T` is determined by
its component on global sections (`AlgebraSheaf.sheafHom_ext`), and conversely a ring map
`χ : A(X) ⟶ Γ(T, ⊤)` compatible with `f` extends to one: on the basic open `X_a` the composite
of `χ` with restriction to `f⁻¹ X_a` sends the image of `a` to a unit, because
`f⁻¹ X_a = T_{f^♯ a}`, so it factors uniquely through the localization `A(X_a)`. These
components are natural in `a`, and `TopCat.Sheaf.restrictHomEquivHom` extends them from the
basis of basic opens to all opens.

Recovering the component on global sections from the components on basic opens uses
`X.basicOpen 1 = ⊤`: the restriction `Γ(T, ⊤) ⟶ Γ(T, f⁻¹ X_1)` is then an isomorphism, with
inverse the restriction in the other direction, so it can be cancelled.

## References

* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01LT](https://stacks.math.columbia.edu/tag/01LT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeSpec

variable {X T : Scheme.{u}}

/-! ### Restriction maps in a presheaf on a preorder -/

section Restriction

variable {P : Type*} [Preorder P] {C : Type*} [Category C] (F : Pᵒᵖ ⥤ C)

/-- A presheaf on a preorder sends the restriction from an element to itself to the identity. -/
theorem map_homOfLE_self {U : P} (h : U ≤ U) : F.map (homOfLE h).op = 𝟙 _ := by
  rw [show (homOfLE h : U ⟶ U) = 𝟙 U from rfl, op_id, F.map_id]

/-- In a presheaf on a preorder, the composite of two restriction maps is the restriction map
along the composite inequality. -/
@[reassoc]
theorem map_homOfLE_comp {U V W : P} (h₁ : W ≤ V) (h₂ : V ≤ U) :
    F.map (homOfLE h₂).op ≫ F.map (homOfLE h₁).op = F.map (homOfLE (h₁.trans h₂)).op := by
  rw [← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- In a presheaf on a preorder, restricting from `U` to `V` and back along `V ≤ U` and `U ≤ V`
is the identity. -/
theorem map_homOfLE_comp_self {U V : P} (h₁ : U ≤ V) (h₂ : V ≤ U) :
    F.map (homOfLE h₂).op ≫ F.map (homOfLE h₁).op = 𝟙 (F.obj (op U)) := by
  rw [map_homOfLE_comp, map_homOfLE_self]

end Restriction

/-- Taking the preimage of opens along a morphism of schemes is monotone. -/
theorem preimage_mono (f : T ⟶ X) {U V : X.Opens} (h : U ≤ V) : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V :=
  fun _ hx ↦ h hx

/-- The restriction of a global section to an open contained in its basic open is a unit. -/
theorem isUnit_res_of_le_basicOpen (T : Scheme.{u}) (r : Γ(T, ⊤)) {V : T.Opens}
    (hV : V ≤ T.basicOpen r) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) r) := by
  rw [← map_homOfLE_comp T.presheaf hV (T.basicOpen_le r), ConcreteCategory.comp_apply]
  exact IsUnit.map (ConcreteCategory.hom (T.presheaf.map (homOfLE hV).op))
    (T.toRingedSpace.isUnit_res_basicOpen r)

/-- Two ring maps out of the sections of the structure sheaf over a basic open of an affine
scheme which agree after restriction from the global sections are equal. -/
theorem presheaf_basicOpen_hom_ext [IsAffine X] (a : Γ(X, ⊤)) {P : CommRingCat.{u}}
    {ψ₁ ψ₂ : Γ(X, X.basicOpen a) ⟶ P}
    (h : X.presheaf.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op ≫ ψ₁
      = X.presheaf.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op ≫ ψ₂) : ψ₁ = ψ₂ := by
  let _i := (isAffineOpen_top X).isLocalization_basicOpen a
  exact CommRingCat.hom_ext
    (IsLocalization.ringHom_ext (Submonoid.powers a) (congrArg CommRingCat.Hom.hom h))

/-! ### Morphisms into an affine scheme -/

/-- The component on global sections of the inverse of the canonical isomorphism
`X ≅ Spec Γ(X, ⊤)` of an affine scheme. -/
theorem isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
    ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  rfl

/-- For a ring map `ρ : Γ(X, ⊤) ⟶ Γ(T, ⊤)` into the global sections of `T`, with `X` affine, the
morphism `T ⟶ Spec Γ(T, ⊤) ⟶ Spec Γ(X, ⊤) ≅ X` induced by `ρ` has component `ρ` on global
sections. -/
theorem appTop_toSpecΓ_comp_specMap (T : Scheme.{u}) {X : Scheme.{u}} [IsAffine X]
    (ρ : Γ(X, ⊤) ⟶ Γ(T, ⊤)) :
    (T.toSpecΓ ≫ Spec.map ρ ≫ X.isoSpec.inv).appTop = ρ := by
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, isoSpec_inv_appTop, Iso.inv_hom_id_assoc]

/-- Morphisms of schemes `T ⟶ X` into an affine scheme `X` are the same thing as ring maps
`Γ(X, ⊤) ⟶ Γ(T, ⊤)` on global sections. -/
noncomputable def affineHomEquiv (X T : Scheme.{u}) [IsAffine X] :
    (T ⟶ X) ≃ (Γ(X, ⊤) ⟶ Γ(T, ⊤)) where
  toFun f := f.appTop
  invFun ρ := T.toSpecΓ ≫ Spec.map ρ ≫ X.isoSpec.inv
  left_inv f := ext_of_isAffine (appTop_toSpecΓ_comp_specMap T f.appTop)
  right_inv ρ := appTop_toSpecΓ_comp_specMap T ρ

/-- The equivalence `affineHomEquiv` sends a morphism to its component on global sections. -/
@[simp]
theorem affineHomEquiv_apply [IsAffine X] (f : T ⟶ X) : affineHomEquiv X T f = f.appTop := rfl

/-- The morphism associated by `affineHomEquiv` to a ring map `ρ` has component `ρ` on global
sections. -/
@[simp]
theorem affineHomEquiv_symm_appTop [IsAffine X] (ρ : Γ(X, ⊤) ⟶ Γ(T, ⊤)) :
    ((affineHomEquiv X T).symm ρ).appTop = ρ :=
  (affineHomEquiv X T).apply_symm_apply ρ

/-- Morphisms into the spectrum of a ring are the same thing as ring maps into the global
sections. -/
noncomputable def specHomEquiv (B : CommRingCat.{u}) (T : Scheme.{u}) :
    (T ⟶ Spec B) ≃ (B ⟶ Γ(T, ⊤)) :=
  (affineHomEquiv (Spec B) T).trans
    { toFun ρ := (Scheme.ΓSpecIso B).inv ≫ ρ
      invFun χ := (Scheme.ΓSpecIso B).hom ≫ χ
      left_inv ρ := by
        change (Scheme.ΓSpecIso B).hom ≫ (Scheme.ΓSpecIso B).inv ≫ ρ = ρ
        rw [Iso.hom_inv_id_assoc]
      right_inv χ := by
        change (Scheme.ΓSpecIso B).inv ≫ (Scheme.ΓSpecIso B).hom ≫ χ = χ
        rw [Iso.inv_hom_id_assoc] }

/-- The equivalence `specHomEquiv` sends a morphism `a : T ⟶ Spec B` to the composite of
`B ≅ Γ(Spec B, ⊤)` with the component of `a` on global sections. -/
@[simp]
theorem specHomEquiv_apply (B : CommRingCat.{u}) {T : Scheme.{u}} (a : T ⟶ Spec B) :
    specHomEquiv B T a = (Scheme.ΓSpecIso B).inv ≫ a.appTop := rfl

/-! ### Sections of a quasi-coherent algebra over a basic open -/

namespace AlgebraSheaf

variable (A : AlgebraSheaf.{u} X)

/-- The restriction map from the global sections of an algebra sheaf to its sections over an
open. -/
noncomputable abbrev res (U : X.Opens) : A.sections ⊤ ⟶ A.sections U :=
  A.right.obj.map (homOfLE (le_top : U ≤ ⊤)).op

/-- The structure map of an algebra sheaf on global sections. -/
noncomputable abbrev unitTop : Γ(X, ⊤) ⟶ A.sections ⊤ := A.hom.hom.app (op ⊤)

/-- For a quasi-coherent algebra sheaf over an affine scheme, the sections over the basic open
of `a` are the localization of the global sections away from the image of `a`. -/
@[ega "I 9.6.2" "partial"]
theorem isLocalization_sections_basicOpen [A.IsQuasicoherent] [IsAffine X] (a : Γ(X, ⊤)) :
    letI := A.algebraSections ⊤
    letI := A.algebraRestrict (le_top : X.basicOpen a ≤ ⊤)
    letI := A.algebraSectionsOfLE (le_top : X.basicOpen a ≤ ⊤)
    letI := A.isScalarTower_restrict (le_top : X.basicOpen a ≤ ⊤)
    IsLocalization.Away (A.unitTop.hom a) (A.sections (X.basicOpen a)) := by
  let _i1 := A.algebraSections ⊤
  let _i2 := A.algebraRestrict (le_top : X.basicOpen a ≤ ⊤)
  let _i3 := A.algebraSectionsOfLE (le_top : X.basicOpen a ≤ ⊤)
  let _i4 := A.isScalarTower_restrict (le_top : X.basicOpen a ≤ ⊤)
  have key : IsLocalizedModule.Away a
      (IsScalarTower.toAlgHom Γ(X, ⊤) (A.sections ⊤) (A.sections (X.basicOpen a))).toLinearMap :=
    isLocalizedModule_restrictₗ (AlgebraSheaf.underlyingModule A) (isAffineOpen_top X) a
      (rfl : X.basicOpen a = X.basicOpen a) le_top
  have e : Submonoid.powers (A.unitTop.hom a)
      = Algebra.algebraMapSubmonoid (A.sections ⊤) (Submonoid.powers a) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    rfl
  change IsLocalization (Submonoid.powers (A.unitTop.hom a)) _
  rw [e]
  exact isLocalizedModule_iff_isLocalization.mp key

/-- Two ring maps out of the sections of a quasi-coherent algebra over a basic open which agree
after restriction from the global sections are equal. -/
theorem sections_basicOpen_hom_ext [A.IsQuasicoherent] [IsAffine X] (a : Γ(X, ⊤))
    {P : CommRingCat.{u}} {ψ₁ ψ₂ : A.sections (X.basicOpen a) ⟶ P}
    (h : A.res (X.basicOpen a) ≫ ψ₁ = A.res (X.basicOpen a) ≫ ψ₂) : ψ₁ = ψ₂ := by
  let _i1 := A.algebraSections ⊤
  let _i2 := A.algebraRestrict (le_top : X.basicOpen a ≤ ⊤)
  let _i3 := A.algebraSectionsOfLE (le_top : X.basicOpen a ≤ ⊤)
  let _i4 := A.isScalarTower_restrict (le_top : X.basicOpen a ≤ ⊤)
  let _i5 := A.isLocalization_sections_basicOpen a
  refine CommRingCat.hom_ext (IsLocalization.ringHom_ext
    (Submonoid.powers (A.unitTop.hom a)) ?_)
  exact congrArg CommRingCat.Hom.hom h

/-- The map out of the sections over a basic open induced by a ring map on global sections which
sends the image of `a` to a unit. -/
noncomputable def sectionsLift [A.IsQuasicoherent] [IsAffine X] (a : Γ(X, ⊤))
    {P : CommRingCat.{u}} (g : A.sections ⊤ ⟶ P) (hg : IsUnit (g.hom (A.unitTop.hom a))) :
    A.sections (X.basicOpen a) ⟶ P :=
  letI := A.algebraSections ⊤
  letI := A.algebraRestrict (le_top : X.basicOpen a ≤ ⊤)
  letI := A.algebraSectionsOfLE (le_top : X.basicOpen a ≤ ⊤)
  letI := A.isScalarTower_restrict (le_top : X.basicOpen a ≤ ⊤)
  letI := A.isLocalization_sections_basicOpen a
  CommRingCat.ofHom (IsLocalization.Away.lift (A.unitTop.hom a) hg)

/-- The map `sectionsLift a g hg` composed after restriction from the global sections is `g`. -/
@[simp]
theorem res_comp_sectionsLift [A.IsQuasicoherent] [IsAffine X] (a : Γ(X, ⊤))
    {P : CommRingCat.{u}} (g : A.sections ⊤ ⟶ P) (hg : IsUnit (g.hom (A.unitTop.hom a))) :
    A.res (X.basicOpen a) ≫ A.sectionsLift a g hg = g := by
  let _i1 := A.algebraSections ⊤
  let _i2 := A.algebraRestrict (le_top : X.basicOpen a ≤ ⊤)
  let _i3 := A.algebraSectionsOfLE (le_top : X.basicOpen a ≤ ⊤)
  let _i4 := A.isScalarTower_restrict (le_top : X.basicOpen a ≤ ⊤)
  let _i5 := A.isLocalization_sections_basicOpen a
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact IsLocalization.Away.lift_eq (A.unitTop.hom a) hg x

end AlgebraSheaf

/-! ### The functor of relative-spectrum pairs -/

/-- A pair `(f, φ)` consisting of a morphism of schemes `f : T ⟶ X` and a morphism
`φ : A ⟶ f_* 𝒪_T` of sheaves of `𝒪_X`-algebras. -/
abbrev RelativeSpecPair (s : RelativeSpecSituation.{u}) (T : Scheme.{u}) :=
  Σ f : T ⟶ s.base, Under.mk s.algebra.hom.hom ⟶ Under.mk f.c

/-- Pull a relative-spectrum pair back along a morphism of test schemes. -/
noncomputable def RelativeSpecPair.pullback {s : RelativeSpecSituation.{u}} {T T' : Scheme.{u}}
    (a : T' ⟶ T) : RelativeSpecPair s T → RelativeSpecPair s T' := fun p ↦
  ⟨a ≫ p.1, p.2 ≫ Under.homMk
    ((TopCat.Presheaf.pushforward CommRingCat p.1.base).map a.c) (by rfl)⟩

/-- The pullback of a relative-spectrum pair, componentwise: the base morphism is composed with
the morphism of test schemes, and the algebra morphism is composed with the pushforward of its
comorphism. -/
lemma RelativeSpecPair.pullback_eq {s : RelativeSpecSituation.{u}} {T T' : Scheme.{u}}
    (a : T' ⟶ T) (p : RelativeSpecPair s T) :
    RelativeSpecPair.pullback a p =
      ⟨a ≫ p.1, p.2 ≫ Under.homMk
        ((TopCat.Presheaf.pushforward CommRingCat p.1.base).map a.c) (by rfl)⟩ :=
  rfl

/-- The contravariant functor sending a test scheme `T` to the pairs
`(f : T ⟶ X, φ : A ⟶ f_* 𝒪_T)` and a morphism of test schemes to pullback of such pairs. -/
@[stacks 01LR]
noncomputable def relativeSpecFunctor (s : RelativeSpecSituation.{u}) :
    Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := RelativeSpecPair s T.unop
  map a := ↾RelativeSpecPair.pullback (s := s) a.unop
  map_id T := by aesop_cat
  map_comp a b := by aesop_cat

/-! ### Morphisms out of a quasi-coherent algebra over an affine base -/

/-- Two morphisms of presheaves of rings on `X` which agree on global sections agree on a basic
open `X_a`, provided maps out of the sections over `X_a` are determined by restriction from the
global sections. -/
private theorem app_basicOpen_eq_of_app_top_eq {F G : X.Opensᵒᵖ ⥤ CommRingCat.{u}} (α β : F ⟶ G)
    (a : Γ(X, ⊤))
    (hext : ∀ {P : CommRingCat.{u}} {ψ₁ ψ₂ : F.obj (op (X.basicOpen a)) ⟶ P},
      F.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op ≫ ψ₁
        = F.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op ≫ ψ₂ → ψ₁ = ψ₂)
    (h : α.app (op ⊤) = β.app (op ⊤)) : α.app (op (X.basicOpen a)) = β.app (op (X.basicOpen a)) :=
  hext <| (α.naturality (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op).trans <|
    (congrArg (· ≫ G.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op) h).trans
      (β.naturality (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op).symm

namespace AlgebraSheaf

variable (A : AlgebraSheaf.{u} X) [A.IsQuasicoherent] [IsAffine X] {T : Scheme.{u}}

/-- The pushforward `f_* 𝒪_T` of the structure sheaf along a morphism of schemes, as a sheaf of
commutative rings on the target. -/
noncomputable abbrev pushforwardSheaf (f : T ⟶ X) :=
  (TopCat.Sheaf.pushforward CommRingCat f.base).obj T.sheaf

/-- A morphism of sheaves `A ⟶ f_* 𝒪_T` out of a quasi-coherent algebra over an affine base is
determined by its component on global sections. -/
theorem sheafHom_ext (f : T ⟶ X)
    {ψ₁ ψ₂ : A.right.obj ⟶ (TopCat.Presheaf.pushforward CommRingCat f.base).obj T.presheaf}
    (h : ψ₁.app (op ⊤) = ψ₂.app (op ⊤)) : ψ₁ = ψ₂ := by
  exact TopCat.Sheaf.hom_ext A.right.obj (pushforwardSheaf f) (isBasis_basicOpen X) fun a ↦
    app_basicOpen_eq_of_app_top_eq ψ₁ ψ₂ a (A.sections_basicOpen_hom_ext a) h

section

variable (f : T ⟶ X) (χ : A.sections ⊤ ⟶ Γ(T, ⊤))

omit [A.IsQuasicoherent] [IsAffine X] in
/-- If `χ` is compatible with `f` on global sections, then the composite of `χ` with restriction
to `f⁻¹ X_a` sends the image of `a` to a unit. -/
theorem isUnit_comp_res (hf : A.unitTop ≫ χ = f.appTop) (a : Γ(X, ⊤)) :
    IsUnit ((χ ≫ T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op).hom
      (A.unitTop.hom a)) := by
  have h : (χ ≫ T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op).hom
      (A.unitTop.hom a)
      = (T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op) (f.appTop a) := by
    rw [← hf]; rfl
  rw [h]
  exact isUnit_res_of_le_basicOpen T (f.appTop a) (Scheme.preimage_basicOpen f a).le

variable (hχ : A.unitTop ≫ χ = f.appTop)

/-- The component over the basic open of `a` of the morphism of sheaves of algebras
`A ⟶ f_* 𝒪_T` determined by a ring map `χ` on global sections. -/
noncomputable def basisComp (a : Γ(X, ⊤)) :
    A.sections (X.basicOpen a) ⟶ Γ(T, f ⁻¹ᵁ X.basicOpen a) :=
  A.sectionsLift a (χ ≫ T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op)
    (A.isUnit_comp_res f χ hχ a)

/-- The component `basisComp f χ hχ a` composed after restriction from the global sections is
the composite of `χ` with restriction to `f⁻¹ X_a`. -/
@[simp]
theorem res_comp_basisComp (a : Γ(X, ⊤)) :
    A.res (X.basicOpen a) ≫ A.basisComp f χ hχ a
      = χ ≫ T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen a ≤ ⊤)).op :=
  A.res_comp_sectionsLift a _ (A.isUnit_comp_res f χ hχ a)

/-- The components `basisComp` commute with restriction along an inclusion of basic opens
`X_b ≤ X_a`. -/
theorem basisComp_naturality' {a b : Γ(X, ⊤)} (h : X.basicOpen b ≤ X.basicOpen a) :
    A.right.obj.map (homOfLE h).op ≫ A.basisComp f χ hχ b
      = A.basisComp f χ hχ a ≫ T.presheaf.map (homOfLE (preimage_mono f h)).op := by
  refine A.sections_basicOpen_hom_ext a ?_
  simp only [← Category.assoc]
  rw [map_homOfLE_comp, A.res_comp_basisComp f χ hχ b, A.res_comp_basisComp f χ hχ a,
    Category.assoc, map_homOfLE_comp]

/-- The components `basisComp` commute with restriction along a morphism of basic opens
`X_b ⟶ X_a`. -/
theorem basisComp_naturality {a b : Γ(X, ⊤)} (u : X.basicOpen b ⟶ X.basicOpen a) :
    A.right.obj.map u.op ≫ A.basisComp f χ hχ b
      = A.basisComp f χ hχ a ≫ T.presheaf.map ((Opens.map f.base).map u).op :=
  A.basisComp_naturality' f χ hχ (leOfHom u)

/-- The morphism of sheaves of algebras `A ⟶ f_* 𝒪_T` determined by a ring map `χ` on global
sections which is compatible with `f`. -/
noncomputable def sheafHomOfRingHom :
    A.right.obj ⟶ (TopCat.Presheaf.pushforward CommRingCat f.base).obj T.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom A.right.obj (pushforwardSheaf f) (isBasis_basicOpen X)
    { app := fun a ↦ A.basisComp f χ hχ a.unop
      naturality := fun _ _ φ ↦ A.basisComp_naturality f χ hχ φ.unop.hom }

/-- The component of `sheafHomOfRingHom` over the basic open of `a` is `basisComp f χ hχ a`. -/
theorem sheafHomOfRingHom_app (a : Γ(X, ⊤)) :
    (A.sheafHomOfRingHom f χ hχ).app (op (X.basicOpen a)) = A.basisComp f χ hχ a :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ a

/-- The component of `sheafHomOfRingHom f χ hχ` on global sections is `χ`. -/
@[simp]
theorem sheafHomOfRingHom_app_top : (A.sheafHomOfRingHom f χ hχ).app (op ⊤) = χ := by
  have hb1 : X.basicOpen (1 : Γ(X, ⊤)) = ⊤ := X.basicOpen_one
  have h1 : (⊤ : T.Opens) ≤ f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) := le_of_eq (by rw [hb1]; rfl)
  have hrr : T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op ≫
      T.presheaf.map (homOfLE h1).op = 𝟙 Γ(T, ⊤) := map_homOfLE_comp_self _ _ _
  have hrr' : T.presheaf.map (homOfLE h1).op ≫
      T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op
      = 𝟙 Γ(T, f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤))) := map_homOfLE_comp_self _ _ _
  have : IsIso (T.presheaf.map
      (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op) := ⟨⟨_, hrr, hrr'⟩⟩
  have hnat : A.res (X.basicOpen (1 : Γ(X, ⊤))) ≫
      (A.sheafHomOfRingHom f χ hχ).app (op (X.basicOpen (1 : Γ(X, ⊤))))
      = (A.sheafHomOfRingHom f χ hχ).app (op ⊤) ≫
        T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op :=
    (A.sheafHomOfRingHom f χ hχ).naturality
      (homOfLE (le_top : X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op
  have hnat2 : χ ≫ T.presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op
      = (A.sheafHomOfRingHom f χ hχ).app (op ⊤) ≫
        T.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op :=
    Eq.trans (Eq.trans (A.res_comp_basisComp f χ hχ 1).symm
      (congrArg (fun k ↦ A.res (X.basicOpen (1 : Γ(X, ⊤))) ≫ k)
        (A.sheafHomOfRingHom_app f χ hχ 1).symm)) hnat
  exact ((cancel_mono _).mp hnat2).symm

/-- The morphism `sheafHomOfRingHom f χ hχ` is a morphism of `𝒪_X`-algebras: its composite with
the structure map `𝒪_X ⟶ A` is the comorphism `f^♯ : 𝒪_X ⟶ f_* 𝒪_T`. -/
theorem hom_comp_sheafHomOfRingHom : A.hom.hom ≫ A.sheafHomOfRingHom f χ hχ = f.c := by
  refine TopCat.Sheaf.hom_ext X.presheaf (pushforwardSheaf f) (isBasis_basicOpen X) fun a ↦
    app_basicOpen_eq_of_app_top_eq _ _ a (presheaf_basicOpen_hom_ext a) ?_
  rw [NatTrans.comp_app, A.sheafHomOfRingHom_app_top]
  exact hχ

end

end AlgebraSheaf

/-! ### Representability of the relative spectrum over an affine base -/

/-- The pair over `T` built from a morphism `f : T ⟶ X` and a compatible ring map on global
sections. -/
noncomputable def pairOfRingHom (s : RelativeSpecSituation.{u}) [IsAffine s.base]
    {T : Scheme.{u}} (f : T ⟶ s.base) (χ : s.algebra.sections ⊤ ⟶ Γ(T, ⊤))
    (hχ : s.algebra.unitTop ≫ χ = f.appTop) : RelativeSpecPair s T :=
  ⟨f, Under.homMk (s.algebra.sheafHomOfRingHom f χ hχ)
    (s.algebra.hom_comp_sheafHomOfRingHom f χ hχ)⟩

/-- The pair `pairOfRingHom s f χ hχ` depends on `f` only up to equality. -/
theorem pairOfRingHom_congr (s : RelativeSpecSituation.{u}) [IsAffine s.base] {T : Scheme.{u}}
    {f f' : T ⟶ s.base} (h : f = f') (χ : s.algebra.sections ⊤ ⟶ Γ(T, ⊤))
    (hχ : s.algebra.unitTop ≫ χ = f.appTop) (hχ' : s.algebra.unitTop ≫ χ = f'.appTop) :
    pairOfRingHom s f χ hχ = pairOfRingHom s f' χ hχ' := by subst h; rfl

/-- The compatibility of the component on global sections of a relative-spectrum pair with the
underlying morphism of schemes. -/
theorem relativeSpecPair_w (s : RelativeSpecSituation.{u}) {T : Scheme.{u}}
    (p : RelativeSpecPair s T) :
    s.algebra.unitTop ≫ p.2.right.app (op ⊤) = p.1.appTop :=
  congrArg (fun α ↦ NatTrans.app α (op ⊤)) (Under.w p.2)

/-- Every relative-spectrum pair over an affine base is the pair built from its underlying
morphism and its component on global sections. -/
theorem pairOfRingHom_eq (s : RelativeSpecSituation.{u}) [IsAffine s.base] {T : Scheme.{u}}
    (p : RelativeSpecPair s T) :
    pairOfRingHom s p.1 (p.2.right.app (op ⊤)) (relativeSpecPair_w s p) = p := by
  obtain ⟨f, φ⟩ := p
  refine congrArg (Sigma.mk f) ?_
  ext1
  exact s.algebra.sheafHom_ext f
    (s.algebra.sheafHomOfRingHom_app_top f _ (relativeSpecPair_w s ⟨f, φ⟩))

/-- For an affine base, the relative-spectrum pairs over a test scheme `T` are in bijection with
the ring maps from the global sections of the algebra to `Γ(T, ⊤)`. -/
noncomputable def pairEquivRingHom (s : RelativeSpecSituation.{u}) [IsAffine s.base]
    (T : Scheme.{u}) : RelativeSpecPair s T ≃ (s.algebra.sections ⊤ ⟶ Γ(T, ⊤)) where
  toFun p := p.2.right.app (op ⊤)
  invFun χ := pairOfRingHom s ((affineHomEquiv s.base T).symm (s.algebra.unitTop ≫ χ)) χ
    (affineHomEquiv_symm_appTop (s.algebra.unitTop ≫ χ)).symm
  left_inv p := by
    refine Eq.trans (pairOfRingHom_congr s ?_ _ _ (relativeSpecPair_w s p))
      (pairOfRingHom_eq s p)
    exact (congrArg (affineHomEquiv s.base T).symm (relativeSpecPair_w s p)).trans
      ((affineHomEquiv s.base T).symm_apply_apply p.1)
  right_inv χ := s.algebra.sheafHomOfRingHom_app_top _ χ _

/-- The bijection `pairEquivRingHom` sends a pair to the component on global sections of its
algebra morphism. -/
@[simp]
theorem pairEquivRingHom_apply (s : RelativeSpecSituation.{u}) [IsAffine s.base]
    {T : Scheme.{u}} (p : RelativeSpecPair s T) :
    pairEquivRingHom s T p = p.2.right.app (op ⊤) := rfl

/-- Under `pairEquivRingHom`, pulling back a pair along `a : T' ⟶ T` corresponds to composing the
ring map with the component of `a` on global sections. -/
theorem pullback_pairEquivRingHom_symm (s : RelativeSpecSituation.{u}) [IsAffine s.base]
    {T T' : Scheme.{u}} (a : T' ⟶ T) (χ : s.algebra.sections ⊤ ⟶ Γ(T, ⊤)) :
    RelativeSpecPair.pullback a ((pairEquivRingHom s T).symm χ)
      = (pairEquivRingHom s T').symm (χ ≫ a.appTop) := by
  refine (pairEquivRingHom s T').injective ?_
  rw [Equiv.apply_symm_apply, pairEquivRingHom_apply]
  change ((pairEquivRingHom s T).symm χ).2.right.app (op ⊤) ≫ a.c.app (op ⊤) = χ ≫ a.appTop
  rw [show ((pairEquivRingHom s T).symm χ).2.right.app (op ⊤) = χ from
    (pairEquivRingHom s T).apply_symm_apply χ]
  rfl

/-- If the base is affine, the functor of relative-spectrum pairs associated to a quasi-coherent
algebra is represented by the spectrum of the algebra's ring of global sections. -/
@[stacks 01LT]
theorem relativeSpecFunctor_representableBy (s : RelativeSpecSituation.{u}) [IsAffine s.base] :
    Nonempty ((relativeSpecFunctor s).RepresentableBy
      (Spec (s.algebra.right.obj.obj (.op (⊤ : s.base.Opens))))) :=
  ⟨{ homEquiv {T} := (specHomEquiv _ T).trans (pairEquivRingHom s T).symm
     homEquiv_comp {T T'} a g := by
       change (pairEquivRingHom s T).symm ((Scheme.ΓSpecIso _).inv ≫ (a ≫ g).appTop)
         = RelativeSpecPair.pullback a
             ((pairEquivRingHom s T').symm ((Scheme.ΓSpecIso _).inv ≫ g.appTop))
       rw [pullback_pairEquivRingHom_symm, Scheme.Hom.comp_appTop, Category.assoc] }⟩

end Stacks.RelativeSpec

end
