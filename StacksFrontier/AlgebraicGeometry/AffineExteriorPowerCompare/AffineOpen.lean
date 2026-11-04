module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.QuasicoherentNatural
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullbackNatural
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exterior powers of a quasi-coherent module on an affine open, on sections

`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso` identifies the global sections of
`⋀ⁿ F` on `Spec R` with `⋀ⁿ_R Γ(Spec R, F)`.  **This file states the same identification for an
affine open `U` of an arbitrary scheme `X`:**

`Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)`,

for `F` quasi-coherent, and proves it natural in `F`.

## Main definitions

* `Stacks.AffineExteriorPower.exteriorPowerCongr`: the exterior power of a linear equivalence.
* `Stacks.AffineExteriorPower.pullbackFromSpecΓIso`: the global sections over `Spec Γ(X, U)` of
  the inverse image of `F` along `U`'s own `Spec` are `Γ(F, U)`.
* `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso`: **the comparison
  `Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)`** for `F` quasi-coherent on an affine open `U` of an
  arbitrary scheme.

## Main results

* `Stacks.AffineExteriorPower.pullbackFromSpecΓIso_natural`: naturality of the first comparison.
* `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_natural`: **naturality of the
  comparison in `F`**, against an arbitrary unital homomorphism of exterior algebras extending a
  morphism `φ : F ⟶ G` on the degree-one generators.
* `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_conj_pieceMap`: conjugating the
  degree-`n` component of the canonical induced homomorphism by the two comparisons gives
  `exteriorPower.map n` of the map `φ` induces on sections over `U`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open SheafOfModules.GradedAlgebra (IsExteriorAlgebra SquareZero UnitalHom)

universe u

namespace Stacks.AffineExteriorPower

/-! ### The exterior power of a linear equivalence -/

/-- The degree-`n` exterior power of a linear equivalence. -/
def exteriorPowerCongr {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ) :
    ⋀[R]^n M ≃ₗ[R] ⋀[R]^n N where
  toFun := exteriorPower.map n e.toLinearMap
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := exteriorPower.map n e.symm.toLinearMap
  left_inv x := by simp [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  right_inv x := by simp [← LinearMap.comp_apply, ← exteriorPower.map_comp]

/-- `Stacks.AffineExteriorPower.exteriorPowerCongr e n` acts as `exteriorPower.map n e`. -/
@[simp] theorem exteriorPowerCongr_apply {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (n : ℕ)
    (x : ⋀[R]^n M) : exteriorPowerCongr e n x = exteriorPower.map n e.toLinearMap x := rfl

/-! ### The sections over an affine open as global sections on its spectrum -/

variable {X : Scheme.{u}} {U : X.Opens}

/-- **The sections of a module over an affine open are the global sections of its restriction
to `Spec Γ(X, U)`.** -/
def restrictΓIso (F : X.Modules) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor hU.fromSpec).obj F) ≅
      ModuleCat.of Γ(X, U) Γ(F, U) :=
  (Stacks.Modules.restrictFromSpecSectionsEquiv F hU).toModuleIso

/-- The comparison `Stacks.AffineExteriorPower.restrictΓIso` is natural in the module. -/
theorem restrictΓIso_natural {F G : X.Modules} (φ : F ⟶ G) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.fromSpec).map φ) ≫
        (restrictΓIso G hU).hom =
      (restrictΓIso F hU).hom ≫ ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ U) := by
  ext x
  exact (congr($(φ.mapPresheaf.naturality
    (eqToHom (Stacks.Modules.image_top_fromSpec hU).symm).op) x)).symm

/-- **The sections of a module over an affine open are the global sections of its inverse image
along `Spec Γ(X, U) ⟶ X`.** -/
def pullbackFromSpecΓIso (F : X.Modules) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj F) ≅
      ModuleCat.of Γ(X, U) Γ(F, U) :=
  moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F).symm ≪≫
    restrictΓIso F hU

/-- The forward map of `Stacks.AffineExteriorPower.pullbackFromSpecΓIso` is the composite of its
two factors. -/
theorem pullbackFromSpecΓIso_hom (F : X.Modules) (hU : IsAffineOpen U) :
    (pullbackFromSpecΓIso F hU).hom =
      moduleSpecΓFunctor.map
          ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.app F) ≫
        (restrictΓIso F hU).hom :=
  rfl

/-- **The comparison of `Stacks.AffineExteriorPower.pullbackFromSpecΓIso` is natural in the
module.** -/
theorem pullbackFromSpecΓIso_natural {F G : X.Modules} (φ : F ⟶ G) (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map φ) ≫
        (pullbackFromSpecΓIso G hU).hom =
      (pullbackFromSpecΓIso F hU).hom ≫
        ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ U) := by
  rw [pullbackFromSpecΓIso_hom, pullbackFromSpecΓIso_hom, ← Functor.map_comp_assoc,
    (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).inv.naturality φ,
    Functor.map_comp_assoc, restrictΓIso_natural φ hU, Category.assoc]

/-! ### The exterior power comparison on an affine open -/

/-- The degree-`n` piece of a sheaf of graded algebras on a scheme, read as a sheaf of modules on
that scheme. -/
abbrev pieceModules (E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)) (n : ℤ) :
    X.Modules :=
  E.piece n

/-- The inverse image of a quasi-coherent module along `Spec Γ(X, U) ⟶ X` is quasi-coherent. -/
instance isQuasicoherent_pullback_fromSpec (F : X.Modules) [F.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    ((Scheme.Modules.pullback hU.fromSpec).obj F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _

section ExteriorPower

variable (F : X.Modules) (hU : IsAffineOpen U)

/-- The inverse image along `Spec Γ(X, U) ⟶ X` of the degree-`n` piece of an exterior algebra of
`F` is the degree-`n` exterior power of the inverse image of `F`. -/
def exteriorPowerFromSpecIso
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (n : ℤ) :
    (Scheme.Modules.pullback hU.fromSpec).obj (E.piece n) ≅
      Scheme.Modules.exteriorPower ((Scheme.Modules.pullback hU.fromSpec).obj F) n :=
  Stacks.PullbackExteriorAlgebra.pieceIso hU.fromSpec.toLRSHom.toShHom E hE
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).1
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n

/-- The isomorphism `Stacks.AffineExteriorPower.exteriorPowerFromSpecIso` is natural in the
module. -/
theorem exteriorPowerFromSpecIso_natural {G : X.Modules}
    {E E' : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    {gen' : G ⟶ E'.piece 1} (hE : IsExteriorAlgebra E gen) (hE' : IsExteriorAlgebra E' gen')
    {φ : F ⟶ G} (u : UnitalHom E E') (hu : gen ≫ u.app 1 = φ ≫ gen')
    (v : UnitalHom (Scheme.Modules.exteriorAlgebra
        ((Scheme.Modules.pullback hU.fromSpec).obj F))
      (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback hU.fromSpec).obj G)))
    (hv : Scheme.Modules.exteriorGenerator
        ((Scheme.Modules.pullback hU.fromSpec).obj F) ≫ v.app 1 =
      (Scheme.Modules.pullback hU.fromSpec).map φ ≫
        Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback hU.fromSpec).obj G))
    (n : ℤ) :
    (Scheme.Modules.pullback hU.fromSpec).map (u.app n) ≫
        (exteriorPowerFromSpecIso G hU hE' n).hom =
      (exteriorPowerFromSpecIso F hU hE n).hom ≫ v.app n :=
  Stacks.PullbackExteriorAlgebra.pieceIso_natural hU.fromSpec.toLRSHom.toShHom hE hE'
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) u hu v hv n

variable [F.IsQuasicoherent]

/-- **The sections over an affine open of the degree-`n` piece of an exterior algebra of a
quasi-coherent module are the degree-`n` exterior power of its sections**:

`Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)`. -/
@[ega "IV 16.6.1" "partial"]
def affineOpenExteriorPowerΓIso
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (n : ℕ) :
    ModuleCat.of Γ(X, U) Γ(pieceModules E (n : ℤ), U) ≅
      ModuleCat.of Γ(X, U) (⋀[Γ(X, U)]^n Γ(F, U)) :=
  (pullbackFromSpecΓIso (E.piece (n : ℤ)) hU).symm ≪≫
    moduleSpecΓFunctor.mapIso (exteriorPowerFromSpecIso F hU hE (n : ℤ)) ≪≫
    quasicoherentExteriorPowerΓIso ((Scheme.Modules.pullback hU.fromSpec).obj F)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n ≪≫
    (exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n).toModuleIso

/-- The three factors of `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso` that follow
the comparison of sections, as a single isomorphism. -/
def affineOpenExteriorPowerΓIsoTail
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (n : ℕ) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj (E.piece (n : ℤ))) ≅
      ModuleCat.of Γ(X, U) (⋀[Γ(X, U)]^n Γ(F, U)) :=
  moduleSpecΓFunctor.mapIso (exteriorPowerFromSpecIso F hU hE (n : ℤ)) ≪≫
    quasicoherentExteriorPowerΓIso ((Scheme.Modules.pullback hU.fromSpec).obj F)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n ≪≫
    (exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n).toModuleIso

/-- The forward map of `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso` is the inverse of
the comparison of sections followed by
`Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIsoTail`. -/
theorem affineOpenExteriorPowerΓIso_hom
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (n : ℕ) :
    (affineOpenExteriorPowerΓIso F hU hE n).hom =
      (pullbackFromSpecΓIso (E.piece (n : ℤ)) hU).inv ≫
        (affineOpenExteriorPowerΓIsoTail F hU hE n).hom :=
  rfl

/-- The forward map of `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIsoTail` is the
composite of its three factors. -/
theorem affineOpenExteriorPowerΓIsoTail_hom
    {E : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (n : ℕ) :
    (affineOpenExteriorPowerΓIsoTail F hU hE n).hom =
      moduleSpecΓFunctor.map (exteriorPowerFromSpecIso F hU hE (n : ℤ)).hom ≫
        (quasicoherentExteriorPowerΓIso ((Scheme.Modules.pullback hU.fromSpec).obj F)
            (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n).hom ≫
          (exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n).toModuleIso.hom :=
  rfl

end ExteriorPower

/-! ### Naturality -/

section Natural

variable {F G : X.Modules} (hU : IsAffineOpen U) [F.IsQuasicoherent] [G.IsQuasicoherent]
  {E E' : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
  {gen' : G ⟶ E'.piece 1} (hE : IsExteriorAlgebra E gen) (hE' : IsExteriorAlgebra E' gen')
  {φ : F ⟶ G} (u : UnitalHom E E') (hu : gen ≫ u.app 1 = φ ≫ gen')

omit [SheafOfModules.IsQuasicoherent F] [SheafOfModules.IsQuasicoherent G] in
/-- The exterior power of the comparison of sections is natural. -/
theorem exteriorPowerCongr_pullbackFromSpecΓIso_natural (n : ℕ) :
    ModuleCat.ofHom (exteriorPower.map n
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map φ)).hom) ≫
        (exteriorPowerCongr (pullbackFromSpecΓIso G hU).toLinearEquiv n).toModuleIso.hom =
      (exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n).toModuleIso.hom ≫
        ModuleCat.ofHom (exteriorPower.map n (Scheme.Modules.sectionsLinearMap φ U)) := by
  have hlin := congrArg ModuleCat.Hom.hom (pullbackFromSpecΓIso_natural φ hU)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hlin
  refine ModuleCat.hom_ext ?_
  show exteriorPower.map n _ ∘ₗ exteriorPower.map n _ =
    exteriorPower.map n _ ∘ₗ exteriorPower.map n _
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
  exact congrArg (fun L => exteriorPower.map n L) hlin

include hu in
/-- **The naturality square for the three factors of the comparison that follow the comparison
of sections.** -/
theorem affineOpenExteriorPowerΓIsoTail_natural (n : ℕ) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map (u.app (n : ℤ))) ≫
        (affineOpenExteriorPowerΓIsoTail G hU hE' n).hom =
      (affineOpenExteriorPowerΓIsoTail F hU hE n).hom ≫
        ModuleCat.ofHom (exteriorPower.map n (Scheme.Modules.sectionsLinearMap φ U)) := by
  set v := (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      ((Scheme.Modules.pullback hU.fromSpec).obj F)).map
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
        ((Scheme.Modules.pullback hU.fromSpec).obj G))
      ((Scheme.Modules.pullback hU.fromSpec).map φ) with hvdef
  have hv : Scheme.Modules.exteriorGenerator
        ((Scheme.Modules.pullback hU.fromSpec).obj F) ≫ v.app 1 =
      (Scheme.Modules.pullback hU.fromSpec).map φ ≫
        Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback hU.fromSpec).obj G) :=
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).map_app_one _ _
  have h01CI : moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback hU.fromSpec).map (u.app (n : ℤ))) ≫
      moduleSpecΓFunctor.map (exteriorPowerFromSpecIso G hU hE' (n : ℤ)).hom =
      moduleSpecΓFunctor.map (exteriorPowerFromSpecIso F hU hE (n : ℤ)).hom ≫
        moduleSpecΓFunctor.map (v.app (n : ℤ)) := by
    rw [← Functor.map_comp, exteriorPowerFromSpecIso_natural F hU hE hE' u hu v hv (n : ℤ)]
    exact Functor.map_comp _ _ _
  have hqc := Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_natural
    ((Scheme.Modules.pullback hU.fromSpec).map φ)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) v hv n
  simp only [affineOpenExteriorPowerΓIsoTail_hom, Category.assoc]
  rw [reassoc_of% h01CI, reassoc_of% hqc,
    exteriorPowerCongr_pullbackFromSpecΓIso_natural hU n]

include hu in
/-- **The comparison `Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)` is natural in `F`.**  Against a unital
homomorphism `u : E ⟶ E'` of exterior algebras extending `φ : F ⟶ G` on the degree-one
generators, the sections over `U` of its degree-`n` component become
`exteriorPower.map n` of the sections of `φ`. -/
theorem affineOpenExteriorPowerΓIso_natural (n : ℕ) :
    ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap (M := pieceModules E (n : ℤ))
          (N := pieceModules E' (n : ℤ)) (u.app (n : ℤ)) U) ≫
        (affineOpenExteriorPowerΓIso G hU hE' n).hom =
      (affineOpenExteriorPowerΓIso F hU hE n).hom ≫
        ModuleCat.ofHom (exteriorPower.map n (Scheme.Modules.sectionsLinearMap φ U)) := by
  have hA : ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap (M := pieceModules E (n : ℤ))
          (N := pieceModules E' (n : ℤ)) (u.app (n : ℤ)) U) ≫
        (pullbackFromSpecΓIso (pieceModules E' (n : ℤ)) hU).inv =
      (pullbackFromSpecΓIso (pieceModules E (n : ℤ)) hU).inv ≫
        moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback hU.fromSpec).map (u.app (n : ℤ))) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      pullbackFromSpecΓIso_natural (u.app (n : ℤ)) hU, Iso.inv_hom_id_assoc]
  rw [affineOpenExteriorPowerΓIso_hom, affineOpenExteriorPowerΓIso_hom, ← Category.assoc, hA,
    Category.assoc, affineOpenExteriorPowerΓIsoTail_natural hU hE hE' u hu n, Category.assoc]

/-- **Conjugating the degree-`n` component of the canonical induced homomorphism of exterior
algebras by the two comparisons gives `exteriorPower.map n` of the map on sections.** -/
theorem affineOpenExteriorPowerΓIso_conj_pieceMap (n : ℕ) :
    ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap (M := pieceModules E (n : ℤ))
          (N := pieceModules E' (n : ℤ)) (hE.pieceMap hE' φ (n : ℤ)) U) ≫
        (affineOpenExteriorPowerΓIso G hU hE' n).hom =
      (affineOpenExteriorPowerΓIso F hU hE n).hom ≫
        ModuleCat.ofHom (exteriorPower.map n (Scheme.Modules.sectionsLinearMap φ U)) :=
  affineOpenExteriorPowerΓIso_natural hU hE hE' (hE.map hE' φ) (hE.map_app_one hE' φ) n

end Natural

end Stacks.AffineExteriorPower

end
