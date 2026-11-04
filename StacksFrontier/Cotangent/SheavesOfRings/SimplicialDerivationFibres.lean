module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreRestrictionBridge
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.ResolutionAugmentationEpi

/-!
# A derivation of `𝒫` on `Δ × C` is a compatible family of derivations of the `P_n`

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it
and let `P_•` be the standard resolution of `ℬ` over `𝒜`, read on `Δ × C` as the sheaf of
commutative rings `𝒫` over `π^{-1}𝒜` with augmentation `ε : 𝒫 ⟶ π^{-1}ℬ`. For a sheaf of
`π^{-1}ℬ`-modules `𝒩` on `Δ × C`, this file identifies

`Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`

with the families of `𝒜`-derivations `d_n ∈ Der_𝒜(P_n, i_n^{-1}𝒩)`, one in each simplicial
degree, that are compatible with the maps of the standard resolution.

## Main definitions

* `CategoryTheory.Sheaf.simplicialDerivations`: the type on the left.
* `CategoryTheory.Sheaf.simplicialDerivationFibre`: the degree-`n` member of the family a
  derivation on `Δ × C` gives.
* `CategoryTheory.Sheaf.simplicialDerivationOfFamily`: the derivation on `Δ × C` a compatible
  family gives.

## Main results

* `CategoryTheory.Sheaf.simplicialDerivationFibre_naturality`: the family a derivation on
  `Δ × C` gives is compatible.
* `CategoryTheory.Sheaf.simplicialDerivationFibre_simplicialDerivationOfFamily` and
  `CategoryTheory.Sheaf.simplicialDerivationOfFamily_simplicialDerivationFibre`: the two
  constructions are mutually inverse.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex
  and the base-changed simplicial module.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), a simplicial module as a
  sheaf of modules on `Δ × C`.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SimplicialModules (projection projectionTopology projectionRing projectionCommRing
  fibreInclusion fibreRestrictionMod fibrewiseModMap augmentationCommRingMap)

universe u

/-! ### Restriction along a factored morphism

Restriction along a composite `g ≫ h` is restriction along `g` followed by restriction along `h`,
for a functor into a concrete category and for a presheaf of modules. -/

namespace CategoryTheory

universe w₁ v₁ u₁ v₂ u₂

/-- The restriction of a section along a morphism that factors is the two restrictions in turn. -/
theorem Functor.map_apply_of_comp_eq {D' : Type u₁} [Category.{v₁} D']
    {A' : Type u₂} [Category.{v₂} A'] {FA : A' → A' → Type*} {CA : A' → Type w₁}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w₁} A' FA]
    (P : D' ⥤ A') {X Z Y : D'} (g : X ⟶ Z) (h : Z ⟶ Y) (F : X ⟶ Y) (hF : g ≫ h = F)
    (x : ToType (P.obj X)) :
    ConcreteCategory.hom (P.map F) x =
      ConcreteCategory.hom (P.map h) (ConcreteCategory.hom (P.map g) x) :=
  hF ▸ Functor.map_comp_apply P g h x

/-- The restriction of a section of a presheaf of modules along a morphism that factors is the
two restrictions in turn. -/
theorem PresheafOfModules.map_apply_of_comp_eq {D' : Type u₁} [Category.{v₁} D']
    {R : D'ᵒᵖ ⥤ RingCat.{w₁}} (M : PresheafOfModules.{w₁} R) {X Z Y : D'ᵒᵖ}
    (g : X ⟶ Z) (h : Z ⟶ Y) (F : X ⟶ Y) (hF : g ≫ h = F) (x : M.obj X) :
    M.map F x = M.map h (M.map g x) :=
  hF ▸ M.map_comp_apply g h x

end CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- `ε : 𝒫 ⟶ π^{-1}ℬ`, the augmentation of the standard resolution read on `Δ × C`. -/
abbrev simplicialAugmentation : simplicialResolution J f ⟶ projectionCommRing J B :=
  augmentationCommRingMap J (resolutionCommAugmentation J f)

/-- The `π^{-1}𝒜`-derivations of `𝒫` valued in a sheaf of `π^{-1}ℬ`-modules, read as a sheaf of
`𝒫`-modules along the augmentation. -/
abbrev simplicialDerivations
    (N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))) :=
  ((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).obj N).val.Derivation'
    (simplicialBaseMap J f).hom

variable {J f}
variable {N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}

/-- The sections of `𝒫` over `(n, U)` restricted along `(𝟙_n, ψ)` are the sections of `P_n` over
`U` restricted along `ψ`. -/
theorem simplicialResolution_map_prodSnd (n : SimplexCategory) {U V : C} (ψ : V ⟶ U)
    (x : ((sheafToPresheaf (projectionTopology C J) CommRingCat.{u}).obj
      (simplicialResolution J f)).obj (op (n, U))) :
    (((sheafToPresheaf (projectionTopology C J) CommRingCat.{u}).obj
        (simplicialResolution J f)).map (CategoryTheory.Prod.mkHom (𝟙 n) ψ).op) x =
      ((resolutionTerm J f (op n)).obj.map ψ.op) x := by
  change ((resolutionTerm J f (op n)).obj.map ψ.op)
      ((((resolutionCommRing J f).map (𝟙 (op n))).hom.app (op U)) x) = _
  rw [(resolutionCommRing J f).map_id]
  rfl

/-- The sections of `𝒫` restricted along `(α, 𝟙)` are the structure map of the standard
resolution at `α`. -/
theorem simplicialResolution_map_prodFst {m n : SimplexCategory} (α : m ⟶ n) (U : C)
    (x : ((sheafToPresheaf (projectionTopology C J) CommRingCat.{u}).obj
      (simplicialResolution J f)).obj (op (n, U))) :
    (((sheafToPresheaf (projectionTopology C J) CommRingCat.{u}).obj
        (simplicialResolution J f)).map (CategoryTheory.Prod.mkHom α (𝟙 U)).op) x =
      (((resolutionCommRing J f).map α.op).hom.app (op U)) x := by
  change (((resolutionCommRing J f).obj (op m)).obj.map (𝟙 (op U)))
      ((((resolutionCommRing J f).map α.op).hom.app (op U)) x) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The degree-`n` member of the family of derivations a derivation on `Δ × C` gives.** A
`π^{-1}𝒜`-derivation of `𝒫` valued in `ε_*𝒩`, read in the simplicial degree `n`, is an
`𝒜`-derivation of `P_n` valued in the restriction `i_n^{-1}𝒩`. -/
def simplicialDerivationFibre (n : SimplexCategoryᵒᵖ) (d : simplicialDerivations J f N) :
    resolutionDerivations J f n
      ((fibreRestrictionMod C J (targetRing J (B := B)) n.unop).obj N) where
  d {Y} := d.d (X := op (n.unop, Y.unop))
  d_mul {Y} a b := d.d_mul (X := op (n.unop, Y.unop)) a b
  d_map {Y Z} g x :=
    (congrArg (fun z => d.d (X := op (n.unop, Z.unop)) z)
      (simplicialResolution_map_prodSnd n.unop g.unop x).symm).trans
      (d.d_map (X := op (n.unop, Y.unop)) (Y := op (n.unop, Z.unop))
        (CategoryTheory.Prod.mkHom (𝟙 n.unop) g.unop).op x)
  d_app {Y} a := d.d_app (X := op (n.unop, Y.unop)) a

/-- On sections over `U`, the degree-`n` member `simplicialDerivationFibre n d` is the derivation
`d` at the object `(n, U)` of `Δ × C`. -/
@[simp]
theorem simplicialDerivationFibre_d (n : SimplexCategoryᵒᵖ) (d : simplicialDerivations J f N)
    (U : Cᵒᵖ) (x : ((resolutionCommRing J f).obj n).obj.obj U) :
    (simplicialDerivationFibre n d).d x = d.d (X := op (n.unop, U.unop)) x :=
  rfl

/-- **The family a derivation on `Δ × C` gives is compatible with the standard resolution.** -/
theorem simplicialDerivationFibre_naturality (d : simplicialDerivations J f N)
    {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (U : Cᵒᵖ)
    (x : ((resolutionCommRing J f).obj m).obj.obj U) :
    (simplicialDerivationFibre n d).d ((((resolutionCommRing J f).map α).hom.app U) x) =
      ((fibrewiseModMap C J (targetRing J (B := B)) α).app N).val.app U
        ((simplicialDerivationFibre m d).d x) :=
  (congrArg (fun z => d.d (X := op (n.unop, U.unop)) z)
    (simplicialResolution_map_prodFst α.unop U.unop x).symm).trans
    (d.d_map (X := op (m.unop, U.unop)) (Y := op (n.unop, U.unop))
      (CategoryTheory.Prod.mkHom α.unop (𝟙 U.unop)).op x)

/-- **The derivation on `Δ × C` a compatible family of degreewise derivations gives.** -/
def simplicialDerivationOfFamily
    (dn : ∀ n : SimplexCategoryᵒᵖ, resolutionDerivations J f n
      ((fibreRestrictionMod C J (targetRing J (B := B)) n.unop).obj N))
    (hdn : ∀ {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (U : Cᵒᵖ)
      (x : ((resolutionCommRing J f).obj m).obj.obj U),
      (dn n).d ((((resolutionCommRing J f).map α).hom.app U) x) =
        ((fibrewiseModMap C J (targetRing J (B := B)) α).app N).val.app U ((dn m).d x)) :
    simplicialDerivations J f N where
  d {X} := (dn (op X.unop.1)).d (X := op X.unop.2)
  d_mul {X} a b := (dn (op X.unop.1)).d_mul (X := op X.unop.2) a b
  d_map {X Y} F x := by
    have hfac : (CategoryTheory.Prod.mkHom (𝟙 X.unop.1) (F.unop.2) :
          ((X.unop.1, Y.unop.2) : SimplexCategory × C) ⟶ X.unop).op ≫
        (CategoryTheory.Prod.mkHom (F.unop.1) (𝟙 Y.unop.2) :
          Y.unop ⟶ ((X.unop.1, Y.unop.2) : SimplexCategory × C)).op = F :=
      congrArg Quiver.Hom.op (Prod.ext (Category.comp_id _) (Category.id_comp _))
    refine Eq.trans ?_ (PresheafOfModules.map_apply_of_comp_eq
      (((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).obj N).val) _ _ F hfac
      ((dn (op X.unop.1)).d (X := op X.unop.2) x)).symm
    rw [Functor.map_apply_of_comp_eq _ _ _ F hfac x,
      simplicialResolution_map_prodFst F.unop.1 Y.unop.2]
    refine Eq.trans (hdn ((F.unop.1).op) (op Y.unop.2) _) ?_
    rw [simplicialResolution_map_prodSnd X.unop.1 F.unop.2 x,
      (dn (op X.unop.1)).d_map (F.unop.2).op x]
    rfl
  d_app {X} a := (dn (op X.unop.1)).d_app (X := op X.unop.2) a

/-- **The family of a derivation determines it**: assembling the degreewise members of the family
a derivation on `Δ × C` gives returns that derivation. -/
theorem simplicialDerivationOfFamily_simplicialDerivationFibre
    (d : simplicialDerivations J f N) :
    simplicialDerivationOfFamily (fun n => simplicialDerivationFibre n d)
        (fun _ _ _ => simplicialDerivationFibre_naturality d _ _ _) = d :=
  rfl

/-- **The degreewise members of the derivation a compatible family gives are that family.** -/
theorem simplicialDerivationFibre_simplicialDerivationOfFamily
    (dn : ∀ n : SimplexCategoryᵒᵖ, resolutionDerivations J f n
      ((fibreRestrictionMod C J (targetRing J (B := B)) n.unop).obj N))
    (hdn : ∀ {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (U : Cᵒᵖ)
      (x : ((resolutionCommRing J f).obj m).obj.obj U),
      (dn n).d ((((resolutionCommRing J f).map α).hom.app U) x) =
        ((fibrewiseModMap C J (targetRing J (B := B)) α).app N).val.app U ((dn m).d x))
    (n : SimplexCategoryᵒᵖ) :
    simplicialDerivationFibre n (simplicialDerivationOfFamily dn hdn) = dn n :=
  rfl

end CategoryTheory.Sheaf

end
