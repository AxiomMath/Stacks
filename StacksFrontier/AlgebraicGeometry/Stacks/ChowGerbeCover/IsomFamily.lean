module

public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpaceRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionCover

/-!
# Natural families of isomorphisms between two points of an algebraic stack

Let `x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points of an algebraic stack. A section of the
isomorphism sheaf `Isom_𝒳(x₁, x₂)` of Stacks 06PP over the identity of `Z` is the same thing as a
family of isomorphisms `x₁(z) ≅ x₂(z)`, one for every point `z` of `Z` over a scheme of the site,
compatible with restriction. The proof of [Stacks, Tag 0CQ7] produces such sections (Stacks 0CQ6
and Stacks 0CPI) and glues 1-morphisms along them, which consumes them as families; this file
records the dictionary and the operations on families.

## Main definitions

* `AlgebraicGeometry.Stack.IsomFamily`: a natural family of isomorphisms `x₁(z) ≅ x₂(z)`.
* `AlgebraicGeometry.Stack.IsomFamily.toSection` and
  `AlgebraicGeometry.Stack.IsomFamily.ofSection`: the two directions of the dictionary with
  sections of `Isom_𝒳(x₁, x₂)`.
* `AlgebraicGeometry.Stack.IsomFamily.comp`, `.symm`, `.refl` and `.restrict`: composition,
  inverses, identities and restriction along a morphism of algebraic spaces.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **A natural family of isomorphisms between two points `x₁, x₂ : Z ⟶ 𝒳`:** a morphism
`x₁(z) ⟶ x₂(z)` of the fibre category over `T` (necessarily an isomorphism) for every point `z`
of `Z` over `T`, compatible with restriction along the morphisms of the site. -/
def IsomFamily (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) : Type _ :=
  {φ : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj T),
      pointFiber B S hS Z hZ x₁ T.unop z ⟶ pointFiber B S hS Z hZ x₂ T.unop z //
    ∀ {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ} (g : T₁ ⟶ T₂) (z : Z.obj T₁),
      pointRestrict B S hS Z hZ x₁ x₂ g z (Z.map g z) rfl (φ T₁ z) = φ T₂ (Z.map g z)}

namespace IsomFamily

variable {B S hS Z hZ}

/-- The compatibility of a family with restriction, at an arbitrary name of the restricted
point. -/
theorem pointRestrict_eq {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) {T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ} (g : T₁ ⟶ T₂)
    (z : Z.obj T₁) (z' : Z.obj T₂) (hz : z' = Z.map g z) :
    pointRestrict B S hS Z hZ x₁ x₂ g z z' hz (φ.1 T₁ z) = φ.1 T₂ z' := by
  subst hz
  exact φ.2 g z

/-- Two families are equal when they agree at every point. -/
theorem ext {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    {φ ψ : IsomFamily B S hS Z hZ x₁ x₂} (h : ∀ T z, φ.1 T z = ψ.1 T z) : φ = ψ :=
  Subtype.ext (funext fun T => funext fun z => h T z)

/-- The section of `Isom_𝒳(x₁, x₂)` named by a natural family of isomorphisms. -/
noncomputable def toSection {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) : Z ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂ where
  app T := ↾fun z => ⟨z, ⟨φ.1 T z, isIso_fiberHom B S hS 𝒳 _⟩⟩
  naturality T₁ T₂ g := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    change (⟨Z.map g z, ⟨φ.1 T₂ (Z.map g z), _⟩⟩ : isomSection B S hS Z hZ x₁ x₂ T₂) =
      ⟨Z.map g z, ⟨pointRestrict B S hS Z hZ x₁ x₂ g z (Z.map g z) rfl (φ.1 T₁ z), _⟩⟩
    rw [isomSection_mk_eq_iff]
    exact (φ.2 g z).symm

/-- The section named by a family sends a point `z` to a point over `z` itself. -/
@[simp] theorem toSection_app_fst {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) (T : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj T) :
    (φ.toSection.app T z).1 = z :=
  rfl

/-- The section named by a family lies over the identity of `Z`. -/
theorem toSection_proj {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) :
    φ.toSection ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = 𝟙 Z := by
  ext T z
  rfl

/-- A section `s` of `Isom_𝒳(x₁, x₂)` over the identity of `Z` names a point of `Z` over each
point `z`, equal to `z`. -/
theorem section_app_fst {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (s : Z ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = 𝟙 Z)
    (T : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj T) : (s.app T z).1 = z := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hs T) z

/-- The natural family of isomorphisms named by a section of `Isom_𝒳(x₁, x₂)` over the identity
of `Z`. -/
noncomputable def ofSection {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (s : Z ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = 𝟙 Z) :
    IsomFamily B S hS Z hZ x₁ x₂ :=
  ⟨fun T z => pointHomCongr B S hS Z hZ x₁ x₂ (section_app_fst s hs T z) (s.app T z).2.1,
    fun {T₁ T₂} g z => by
      have hnat : s.app T₂ (Z.map g z) = isomSectionRestrict B S hS Z hZ x₁ x₂ g (s.app T₁ z)
          (Z.map g (s.app T₁ z).1) rfl := by
        have := ConcreteCategory.congr_hom (s.naturality g) z
        exact this
      rw [pointRestrict_pointHomCongr B S hS Z hZ x₁ x₂ g (section_app_fst s hs T₁ z)
        (Z.map g z) rfl (by rw [section_app_fst s hs T₁ z])]
      have key : ∀ (t : isomSection B S hS Z hZ x₁ x₂ T₂)
          (ht : t = isomSectionRestrict B S hS Z hZ x₁ x₂ g (s.app T₁ z)
            (Z.map g (s.app T₁ z).1) rfl) (h : t.1 = Z.map g z),
          pointRestrict B S hS Z hZ x₁ x₂ g (s.app T₁ z).1 (Z.map g z)
              (by rw [section_app_fst s hs T₁ z]) (s.app T₁ z).2.1 =
            pointHomCongr B S hS Z hZ x₁ x₂ h t.2.1 := by
        intro t ht h
        subst ht
        exact (pointHomCongr_pointRestrict B S hS Z hZ x₁ x₂ g _ rfl _ h _).symm
      exact key _ hnat _⟩

/-- The section named by the family of a section `s` is `s`. -/
theorem toSection_ofSection {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (s : Z ⟶ isomSpaceOverSpace B S hS Z hZ x₁ x₂)
    (hs : s ≫ isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ = 𝟙 Z) :
    (ofSection s hs).toSection = s := by
  ext T z
  exact isomSection_eq_of_pointHomCongr B S hS Z hZ x₁ x₂ _ _ z rfl
    (section_app_fst s hs T z) rfl

/-- The family named by the section of a family `φ` is `φ`. -/
theorem ofSection_toSection {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) :
    ofSection φ.toSection φ.toSection_proj = φ :=
  ext fun T z => pointHomCongr_eq B S hS Z hZ x₁ x₂
    (section_app_fst φ.toSection φ.toSection_proj T z) (φ.1 T z)

/-- A family is determined by the section it names. -/
theorem toSection_injective {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    {φ ψ : IsomFamily B S hS Z hZ x₁ x₂} (h : φ.toSection = ψ.toSection) : φ = ψ := by
  rw [← ofSection_toSection φ, ← ofSection_toSection ψ]
  congr 1

/-- Two families agree after precomposing their sections with `r : Z' ⟶ Z` exactly when they
agree at every point of `Z` coming from `Z'`. -/
theorem comp_toSection_eq_iff {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : Z' ⟶ Z)
    {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳} (φ ψ : IsomFamily B S hS Z hZ x₁ x₂) :
    r ≫ φ.toSection = r ≫ ψ.toSection ↔ ∀ T z', φ.1 T (r.app T z') = ψ.1 T (r.app T z') := by
  refine ⟨fun h T z' => ?_, fun h => ?_⟩
  · have := congrFun (congrArg (fun m => (m.app T : Z'.obj T → _)) h) z'
    exact (isomSection_mk_eq_iff B S hS Z hZ x₁ x₂ _ _ _).1 this
  · ext T z'
    exact (isomSection_mk_eq_iff B S hS Z hZ x₁ x₂ _ _ _).2 (h T z')

/-- The identity family. -/
noncomputable def refl (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsomFamily B S hS Z hZ x x :=
  ⟨fun _ _ => 𝟙 _, fun g z => pointRestrict_id_hom B S hS Z hZ x g z _ rfl⟩

/-- The composite of two families. -/
noncomputable def comp {x₁ x₂ x₃ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) (ψ : IsomFamily B S hS Z hZ x₂ x₃) :
    IsomFamily B S hS Z hZ x₁ x₃ :=
  ⟨fun T z => φ.1 T z ≫ ψ.1 T z, fun g z => by
    rw [pointRestrict_comp_hom, φ.2, ψ.2]⟩

/-- The inverse family. -/
noncomputable def symm {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) : IsomFamily B S hS Z hZ x₂ x₁ :=
  ⟨fun T z => haveI := isIso_fiberHom B S hS 𝒳 (φ.1 T z); CategoryTheory.inv (φ.1 T z),
    fun g z => by
      have := isIso_fiberHom B S hS 𝒳 (φ.1 _ z)
      rw [pointRestrict_inv]
      congr 1
      exact φ.2 g z⟩

/-- The composite of two families is computed pointwise. -/
@[simp] theorem comp_apply {x₁ x₂ x₃ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) (ψ : IsomFamily B S hS Z hZ x₂ x₃) (T z) :
    (φ.comp ψ).1 T z = φ.1 T z ≫ ψ.1 T z :=
  rfl

/-- The inverse of a family, followed by the family, is the identity family. -/
theorem symm_comp {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) : φ.symm.comp φ = refl x₂ :=
  ext fun T z => by
    have := isIso_fiberHom B S hS 𝒳 (φ.1 T z)
    exact IsIso.inv_hom_id _

/-- A family, followed by its inverse, is the identity family. -/
theorem comp_symm {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (φ : IsomFamily B S hS Z hZ x₁ x₂) : φ.comp φ.symm = refl x₁ :=
  ext fun T z => by
    have := isIso_fiberHom B S hS 𝒳 (φ.1 T z)
    exact IsIso.hom_inv_id _

/-- The restriction of a family along a morphism `r : Z' ⟶ Z` of algebraic spaces. -/
noncomputable def restrict {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : IsAlgebraicSpace B S hS Z') (r : Z' ⟶ Z)
    {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳} (φ : IsomFamily B S hS Z hZ x₁ x₂) :
    IsomFamily B S hS Z' hZ' (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ r ≫ x₁)
      (algebraicSpaceStackMap.{u, w} B S hS hZ' hZ r ≫ x₂) :=
  ⟨fun T z => φ.1 T (r.app T z), fun {T₁ T₂} g z =>
    φ.pointRestrict_eq g (r.app T₁ z) (r.app T₂ (Z'.map g z)) (by
      have := ConcreteCategory.congr_hom (r.naturality g) z
      exact this)⟩

/-- The restriction of a family along `r` is the family read at the images under `r`. -/
@[simp] theorem restrict_apply {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : IsAlgebraicSpace B S hS Z') (r : Z' ⟶ Z)
    {x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳} (φ : IsomFamily B S hS Z hZ x₁ x₂)
    (T z) : (φ.restrict hZ' r).1 T z = φ.1 T (r.app T z) :=
  rfl

end IsomFamily

end AlgebraicGeometry.Stack

end
