module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom

/-!
# Rank-one dual bases from a single generating section

Let `𝒪` be a presheaf of commutative rings on a site whose underlying presheaf of rings is a
sheaf, let `L` be a sheaf of `𝒪`-modules and let `e` be a section of `L` over an object `U`.
If, over every object `V` of the slice site `C/U`, the map `c ↦ c • e|_V` from the sections of
`𝒪` to the sections of `L` is bijective, then `e` is a basis of the free rank-one module
`L|_U`: the dual coordinate is the inverse of that map, and it is automatically compatible
with the restriction maps.

This file packages that as `Stacks.SheafOfModules.DualBasisOne.ofSmulBijective`, which turns
the bijectivity hypothesis — a statement about one module of sections at a time — into the
`Stacks.SheafOfModules.DualBasisOne` data, whose dual coordinate is a morphism of presheaves of
modules on the whole slice site.

## Main definitions

* `Stacks.SheafOfModules.resAlong` and `Stacks.SheafOfModules.resRingAlong`: the restriction
  maps of `L` and of `𝒪` along a morphism of the site, with their result types pinned down.
* `Stacks.SheafOfModules.smulSectionMap`: multiplication `c ↦ c • x` by a section `x` of `L`,
  as a linear map out of the sections of `𝒪`.
* `Stacks.SheafOfModules.coordOfSmulBijective`: its inverse, when it is bijective.
* `Stacks.SheafOfModules.dualCoordOfSmulBijective`: the resulting section of the dual `L^∨`.
* `Stacks.SheafOfModules.DualBasisOne.ofSmulBijective`: the rank-one dual basis.

## Implementation notes

The restriction maps are named because their Mathlib spellings land in restriction-of-scalars
copies of the target: `L.val.map φ` has codomain
`(ModuleCat.restrictScalars _).obj (L.val.obj _)`, which has the same carrier as
`L.val.obj _` but is not syntactically equal to it, so a goal stated with the raw spelling is
rejected as not type-correct at `implicit` transparency as soon as a rewrite exposes it.
`resAlong` and `resRingAlong` fix the target spelling once, exactly as
`Stacks.SheafOfModules.resSection` and `resRing` do for the slice site. For the same reason the
naturality of the dual coordinate is proved as the standalone lemma
`coordOfSmulBijective_naturality`, whose section argument carries the pinned type, rather than
inside the construction of the morphism, where the argument introduced by `Hom.mk` carries the
slice-site spelling.

Only the *bijectivity* of multiplication by `e` is assumed, and the construction uses both
halves: surjectivity produces the coordinate and injectivity makes it unique, which is what
forces the coordinate to commute with restriction.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- The restriction of a section of `L` along a morphism `φ : B ⟶ A` of the site, with its
result type pinned to `L.val.obj (op B)`. -/
def resAlong {A B : C} (φ : B ⟶ A) (x : L.val.obj (op A)) : L.val.obj (op B) :=
  (L.val.map φ.op).hom x

/-- The restriction of a section of the structure sheaf along a morphism `φ : B ⟶ A` of the
site, with its result type pinned down. -/
def resRingAlong {A B : C} (φ : B ⟶ A)
    (c : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A)) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op B) :=
  ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.map φ.op).hom c

/-- Restriction is semilinear: it carries `c • x` to the restriction of `c` acting on the
restriction of `x`. -/
lemma resAlong_smul {A B : C} (φ : B ⟶ A)
    (c : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A)) (x :
      L.val.obj (op A)) :
    resAlong (L := L) φ (c • x) = resRingAlong (𝒪 := 𝒪) (h𝒪 := h𝒪) φ c • resAlong φ x :=
  PresheafOfModules.map_smul L.val φ.op c x

/-- Restricting twice is restricting along the composite. -/
lemma resAlong_comp {A B D : C} (φ : B ⟶ A) (ψ : A ⟶ D) (x : L.val.obj (op D)) :
    resAlong (L := L) φ (resAlong ψ x) = resAlong (φ ≫ ψ) x :=
  (PresheafOfModules.map_comp_apply L.val ψ.op φ.op x).symm

/-- `resSection` is restriction along the structure morphism of the slice object. -/
lemma resSection_eq_resAlong {U : C} (V : (Over U)ᵒᵖ) (x : L.val.obj (op U)) :
    resSection (L := L) V x = resAlong V.unop.hom x := rfl

/-- Restricting a section of `L` from `U` to a slice object `V` and then along a morphism
`V ⟶ W` of the slice site is restricting it to `W`. -/
lemma resAlong_resSection {U : C} {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : L.val.obj (op U)) :
    resAlong (L := L) f.unop.left (resSection V x) = resSection W x := by
  rw [resSection_eq_resAlong, resSection_eq_resAlong, resAlong_comp, Over.w f.unop]

/-- Multiplication by a section `x` of `L` over `A`, as a linear map from the sections of the
structure sheaf over `A` to the sections of `L` over `A`. It is bijective exactly when `x` is a
basis of a free rank-one module of sections. -/
def smulSectionMap {A : C} (x : L.val.obj (op A)) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A) →ₗ[
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A)] L.val.obj (op
        A) :=
  LinearMap.toSpanSingleton _ _ x

/-- `smulSectionMap x` is multiplication by `x`, on the nose. -/
lemma smulSectionMap_apply {A : C} (x : L.val.obj (op A))
    (c : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A)) :
    smulSectionMap x c = c • x := rfl

/-- The coordinate of a section with respect to a section `x` of `L` by which multiplication is
bijective: the inverse of `Stacks.SheafOfModules.smulSectionMap`. -/
def coordOfSmulBijective {A : C} (x : L.val.obj (op A))
    (h : Function.Bijective (smulSectionMap x)) :
    L.val.obj (op A) ≃ₗ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
      A)]
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op A) :=
  (LinearEquiv.ofBijective _ h).symm

/-- The defining property of the coordinate: it is the factor expressing a section as a
multiple of `x`. -/
lemma coordOfSmulBijective_smul {A : C} (x : L.val.obj (op A))
    (h : Function.Bijective (smulSectionMap x)) (y : L.val.obj (op A)) :
    coordOfSmulBijective x h y • x = y :=
  (LinearEquiv.ofBijective (smulSectionMap x) h).apply_symm_apply y

/-- **The coordinate commutes with the restriction maps.** Restricting a section and taking its
coordinate with respect to the restricted generator gives the restriction of its coordinate,
because both are the unique factor expressing the restricted section as a multiple of the
restricted generator. -/
lemma coordOfSmulBijective_naturality {U : C} {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (e : L.val.obj (op U))
    (hV : Function.Bijective (smulSectionMap (resSection (L := L) V e)))
    (hW : Function.Bijective (smulSectionMap (resSection (L := L) W e)))
    (g : L.val.obj (op V.unop.left)) :
    coordOfSmulBijective (resSection W e) hW (resAlong f.unop.left g) =
      resRingAlong (𝒪 := 𝒪) (h𝒪 := h𝒪) f.unop.left
        (coordOfSmulBijective (resSection V e) hV g) := by
  refine hW.injective ?_
  rw [smulSectionMap_apply, smulSectionMap_apply, coordOfSmulBijective_smul,
    ← resAlong_resSection f e, ← resAlong_smul, coordOfSmulBijective_smul]

/-- **The dual coordinate of a generating section**, as a section of the dual `L^∨` over `U`:
the family of coordinate maps of `Stacks.SheafOfModules.coordOfSmulBijective`, which
`coordOfSmulBijective_naturality` assembles into a morphism of presheaves of modules on the
slice site `C/U`. -/
def dualCoordOfSmulBijective (U : C) (e : L.val.obj (op U))
    (h : ∀ V : (Over U)ᵒᵖ, Function.Bijective (smulSectionMap (resSection (L := L) V e))) :
    (dualSheaf 𝒪 h𝒪 L).val.obj (op U) := by
  refine PresheafOfModules.Hom.mk (fun V => ?_) ?_
  · change L.val.obj (op V.unop.left) ⟶
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val.obj
        (op V.unop.left)
    exact ModuleCat.ofHom (coordOfSmulBijective _ (h V)).toLinearMap
  · intro V W f
    exact ModuleCat.hom_ext
      (LinearMap.ext fun g => coordOfSmulBijective_naturality f e (h V) (h W) g)

/-- The components of `dualCoordOfSmulBijective` are the coordinate maps it is built from. -/
@[simp]
lemma dualApp_dualCoordOfSmulBijective {U : C} (e : L.val.obj (op U))
    (h : ∀ V : (Over U)ᵒᵖ, Function.Bijective (smulSectionMap (resSection (L := L) V e)))
    (V : (Over U)ᵒᵖ) (g : L.val.obj (op V.unop.left)) :
    dualApp (dualCoordOfSmulBijective U e h) V g =
      coordOfSmulBijective (resSection V e) (h V) g := rfl

namespace DualBasisOne

/-- **A section by which multiplication is bijective over the whole slice site is a rank-one
basis.** This is the form of local freeness of rank one that
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne` consumes, produced from the bijectivity of
multiplication by a single section — a statement about one module of sections at a time, with
no morphism of presheaves to construct by hand. -/
def ofSmulBijective (U : C) (e : L.val.obj (op U))
    (h : ∀ V : (Over U)ᵒᵖ, Function.Bijective (smulSectionMap (resSection (L := L) V e))) :
    DualBasisOne 𝒪 h𝒪 L U where
  e := e
  lam := dualCoordOfSmulBijective U e h
  span V g := by
    rw [dualApp_dualCoordOfSmulBijective]
    exact coordOfSmulBijective_smul _ (h V) g
  eval_self := by
    rw [← dualApp_self, dualApp_dualCoordOfSmulBijective]
    refine (h _).injective ?_
    rw [smulSectionMap_apply, smulSectionMap_apply, one_smul, coordOfSmulBijective_smul,
      resSection_self]

/-- The basis section of `DualBasisOne.ofSmulBijective` is the section it was built from. -/
@[simp]
lemma ofSmulBijective_e (U : C) (e : L.val.obj (op U))
    (h : ∀ V : (Over U)ᵒᵖ, Function.Bijective (smulSectionMap (resSection (L := L) V e))) :
    (ofSmulBijective U e h).e = e := rfl

end DualBasisOne

end Stacks.SheafOfModules

end
