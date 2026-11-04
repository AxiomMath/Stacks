module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleOver
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The image subsheaf: universal property, restriction to a slice site, and finite type

Let `J` be a Grothendieck topology on a category `C`, let `R : Sheaf J RingCat` be a sheaf of
rings and let `φ : ℰ ⟶ ℱ` be a morphism of sheaves of `R`-modules. Its image subsheaf
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ`, a `SheafOfModules.Submodule ℱ`, consists
of the sections of `ℱ` which locally lie in the range of `φ`, and `φ` factors through it by
`Stacks.SheafOfModules.ImageSubsheaf.toImage`. This file proves its universal property, its
invariance under an automorphism of the structure sheaf when the target is the structure sheaf,
its behaviour under restriction to a slice site, and its finite type.

## Main results

* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le`: the image is the least submodule of
  the target containing the values of `φ`.
* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le_iff` and
  `Stacks.SheafOfModules.ImageSubsheaf.exists_factorThru_iff_imageSubmodule_le`: the same
  universal property as an iff, in the membership spelling and in the spelling that names the
  factorisation — `φ` factors through a submodule exactly when that submodule contains the
  image.
* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_eq_sheafifySubmodule`: the image is the
  closure `Stacks.SheafOfModules.sheafifySubmodule` of the pointwise range.
* `Stacks.SheafOfModules.ImageSubsheaf.mem_of_hom_unit` and
  `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso`: a submodule of the structure
  sheaf is stable under every endomorphism of the structure sheaf, so the image of a morphism into
  the structure sheaf is unchanged by composing with an automorphism of the structure sheaf,
  `Im (φ ≫ θ) = Im φ`.
* `Stacks.SheafOfModules.ImageSubsheaf.over_imageSubmodule`: the image commutes with restriction
  to a slice site, `(Im φ)|_V = Im (φ|_V)`.
* `Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_toImage` and
  `Stacks.SheafOfModules.ImageSubsheaf.epi_toImage`: the factorisation of `φ` through its image
  is locally surjective, hence an epimorphism, with no hypothesis on the site.
* `Stacks.SheafOfModules.ImageSubsheaf.isFiniteType_imageSubmodule`: the image of a morphism out
  of a sheaf of modules of finite type is of finite type.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u u' t

namespace Stacks.SheafOfModules.ImageSubsheaf

/-! ### The universal property -/

section Universal

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{t} R}

/-- The image subsheaf of `φ` contains the pointwise range of `φ`. -/
theorem rangeSubmodule_le_imageSubmodule (f : M ⟶ N) :
    rangeSubmodule f ≤ (imageSubmodule f).toSubmodule := by
  rintro X s ⟨m, hm⟩
  exact hm ▸ apply_mem_imageSubmodule f m

/-- The image subsheaf is the least submodule of the target containing the values of `φ`. -/
theorem imageSubmodule_le (f : M ⟶ N) {P : N.Submodule}
    (h : ∀ (X : Cᵒᵖ) (m : M.val.obj X), f.val.app X m ∈ P.obj X) :
    imageSubmodule f ≤ P := by
  intro X s hs
  refine P.isSheaf s (J.superset_covering ?_ hs)
  rintro V g ⟨m, hm⟩
  have h2 := h (op V) m
  rwa [hm] at h2

/-- The universal property of the image subsheaf as an iff: a submodule of the target contains
the image exactly when it contains every value of `φ`. -/
theorem imageSubmodule_le_iff (f : M ⟶ N) {P : N.Submodule} :
    imageSubmodule f ≤ P ↔ ∀ (X : Cᵒᵖ) (m : M.val.obj X), f.val.app X m ∈ P.obj X :=
  ⟨fun h X m ↦ h X (apply_mem_imageSubmodule f m), imageSubmodule_le f⟩

/-- The image subsheaf is the least submodule of the target through which `φ` factors: `φ`
factors through a submodule exactly when that submodule contains the image. -/
theorem exists_factorThru_iff_imageSubmodule_le (f : M ⟶ N) {P : N.Submodule} :
    (∃ g : M ⟶ P.toSheafOfModules, g ≫ P.ι = f) ↔ imageSubmodule f ≤ P := by
  refine ⟨fun ⟨g, hg⟩ ↦ imageSubmodule_le f fun X m ↦ ?_, fun h ↦ ?_⟩
  · have : f.val.app X m = (g.val.app X m).1 := by rw [← hg]; rfl
    exact this ▸ (g.val.app X m).2
  · have h' := (imageSubmodule_le_iff f).1 h
    exact ⟨P.factorThru f h', P.factorThru_ι f h'⟩

/-- The image subsheaf is the closure `Stacks.SheafOfModules.sheafifySubmodule` of the
pointwise range: the least submodule with local membership containing the range. -/
theorem imageSubmodule_eq_sheafifySubmodule (f : M ⟶ N) :
    imageSubmodule f = Stacks.SheafOfModules.sheafifySubmodule (rangeSubmodule f) :=
  le_antisymm
    (imageSubmodule_le f fun X m ↦
      Stacks.SheafOfModules.le_sheafifySubmodule (rangeSubmodule f) X ⟨m, rfl⟩)
    (Stacks.SheafOfModules.sheafifySubmodule_le (rangeSubmodule_le_imageSubmodule f))

/-- The image subsheaf is unchanged by precomposition with an isomorphism. -/
theorem imageSubmodule_iso_hom_comp {M' : SheafOfModules.{t} R} (e : M' ≅ M) (f : M ⟶ N) :
    imageSubmodule (e.hom ≫ f) = imageSubmodule f := by
  refine le_antisymm (imageSubmodule_le _ fun X m ↦ apply_mem_imageSubmodule f _)
    (imageSubmodule_le f fun X m ↦ ?_)
  have h : (e.hom ≫ f).val.app X (e.inv.val.app X m) = f.val.app X m :=
    congr(f.val.app X $(congr($(e.inv_hom_id).val.app X m)))
  exact h ▸ apply_mem_imageSubmodule (e.hom ≫ f) _

end Universal

/-! ### The image of a map into the structure sheaf, up to an automorphism of the target -/

section Unit

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)] {M : SheafOfModules.{u} R}

open scoped IsMulCommutative

/-- A submodule of the structure sheaf `𝒪` is stable under every endomorphism of `𝒪` as a sheaf
of modules over itself. -/
theorem mem_of_hom_unit {P : (SheafOfModules.unit R).Submodule}
    (θ : SheafOfModules.unit R ⟶ SheafOfModules.unit R) {X : Cᵒᵖ}
    (x : R.obj.obj X) (hx : x ∈ P.toSubmodule.obj X) :
    θ.val.app X x ∈ P.toSubmodule.obj X := by
  obtain ⟨u, hu⟩ : ∃ u : R.obj.obj X, u = 1 := ⟨1, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : R.obj.obj X, θ.val.app X u = l := ⟨_, rfl⟩
  have hl' : (θ.val.app X u : R.obj.obj X) = l := hl
  have h1 : (x • u : R.obj.obj X) = x := by rw [hu, smul_eq_mul, mul_one]
  have hsm : θ.val.app X ((x • u : R.obj.obj X)) = x • θ.val.app X u :=
    (θ.val.app X).hom.map_smul x u
  have h3 : (x • l : R.obj.obj X) = l • x := by rw [smul_eq_mul, smul_eq_mul, mul_comm]
  have h2 : θ.val.app X x = l • x :=
    (congrArg (fun z : R.obj.obj X => θ.val.app X z) h1.symm).trans
      (hsm.trans ((congrArg (fun z : R.obj.obj X => (x • z : R.obj.obj X)) hl').trans h3))
  rw [h2]
  exact (P.toSubmodule.obj X).smul_mem l hx

/-- Composing with an automorphism of the structure sheaf does not change the image subsheaf:
for a morphism `φ : ℰ ⟶ 𝒪` and an isomorphism `θ : 𝒪 ≅ 𝒪` of sheaves of modules,
`Im (φ ≫ θ) = Im φ`. -/
theorem imageSubmodule_comp_unitIso (φ : M ⟶ SheafOfModules.unit R)
    (θ : SheafOfModules.unit R ≅ SheafOfModules.unit R) :
    imageSubmodule (φ ≫ θ.hom) = imageSubmodule φ := by
  refine le_antisymm (imageSubmodule_le _ fun X m ↦ ?_) (imageSubmodule_le φ fun X m ↦ ?_)
  · exact mem_of_hom_unit θ.hom _ (apply_mem_imageSubmodule φ m)
  · have e : (φ ≫ θ.hom) ≫ θ.inv = φ := by
      rw [Category.assoc, θ.hom_inv_id, Category.comp_id]
    have h := mem_of_hom_unit (P := imageSubmodule (φ ≫ θ.hom)) θ.inv
      ((φ ≫ θ.hom).val.app X m) (apply_mem_imageSubmodule (φ ≫ θ.hom) m)
    rwa [show θ.inv.val.app X ((φ ≫ θ.hom).val.app X m) = φ.val.app X m from
      congr($(e).val.app X m)] at h

end Unit

/-! ### Restriction to a slice site -/

section Over

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{t} R}

/-- The image subsheaf commutes with restriction to a slice site: `(Im φ)|_V = Im (φ|_V)` as
submodules of `ℱ|_V`. -/
theorem over_imageSubmodule (f : M ⟶ N) (V : C) :
    (imageSubmodule f).over V = imageSubmodule (f.over V) := by
  apply le_antisymm
  · intro W s hs
    refine (J.over V).superset_covering ?_ (J.overEquiv_symm_mem_over (unop W) _ hs)
    intro W' g hg
    exact (Sieve.overEquiv_symm_iff _ g).mp hg
  · intro W s hs
    refine (imageSubmodule f).isSheaf s (J.superset_covering ?_ ((J.mem_over_iff _).mp hs))
    intro Z g hg
    obtain ⟨m, hm⟩ := (Sieve.overEquiv_iff _ g).mp hg
    exact rangeSubmodule_le_imageSubmodule f (op Z) ⟨m, hm⟩

/-- `Stacks.SheafOfModules.ImageSubsheaf.over_imageSubmodule` on the associated sheaves of
modules. -/
theorem over_toSheafOfModules_imageSubmodule (f : M ⟶ N) (V : C) :
    (imageSubmodule f).toSheafOfModules.over V =
      (imageSubmodule (f.over V)).toSheafOfModules := by
  rw [← over_imageSubmodule f V, SheafOfModules.Submodule.over_toSheafOfModules]

end Over

/-! ### The factorisation through the image is an epimorphism -/

section Epi

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{t} R}

/-- The factorisation of `φ` through its image subsheaf is locally surjective. -/
theorem isLocallySurjective_toImage (f : M ⟶ N) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (toImage f).val) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ s.2
    rintro V g ⟨m, hm⟩
    exact ⟨m, Subtype.ext hm⟩

/-- The factorisation of `φ` through its image subsheaf is an epimorphism. -/
instance epi_toImage (f : M ⟶ N) : Epi (toImage f) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ (isLocallySurjective_toImage f)

end Epi

/-! ### Finite type of the image -/

section FiniteType

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- The image subsheaf of a morphism out of a sheaf of modules of finite type is of finite
type. -/
@[ega "0 5.2.1" "more general"]
theorem isFiniteType_imageSubmodule (f : M ⟶ N) (hM : M.IsFiniteType) :
    (imageSubmodule f).toSheafOfModules.IsFiniteType :=
  Stacks.SheafOfModules.SliceFinite.isFiniteType_of_epi (toImage f) hM

/-- The image subsheaf of a morphism out of a sheaf of modules of finite type is of finite
type. -/
instance isFiniteType_imageSubmodule_of_instance (f : M ⟶ N) [M.IsFiniteType] :
    (imageSubmodule f).toSheafOfModules.IsFiniteType :=
  isFiniteType_imageSubmodule f inferInstance

end FiniteType

end Stacks.SheafOfModules.ImageSubsheaf

end
