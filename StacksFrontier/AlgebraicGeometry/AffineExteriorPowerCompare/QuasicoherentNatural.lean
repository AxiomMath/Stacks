module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Natural
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.Quasicoherent

/-!
# Naturality of the affine exterior-power comparison for quasi-coherent modules

`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso` identifies the global sections of the
`n`-th exterior power of a quasi-coherent module `F` on `Spec R` with `⋀ⁿ_R Γ(Spec R, F)`.
**This file proves that identification natural in `F`, over a fixed ring `R`**: for a morphism
`φ : F ⟶ G` of quasi-coherent modules and a unital homomorphism of exterior algebras extending
`φ` on the degree-one generators, the square commutes.

In particular, the global sections of the degree-`n` component of the homomorphism of exterior
algebras that the universal property produces from `φ` *are* `exteriorPower.map n` of the map `φ`
induces on global sections, read through the two comparisons.

This is naturality in the module, for a fixed ring. It is not base change along a ring map
`R ⟶ R'`, which is a different statement.

## Main results

* `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_naturality`: **the comparison between two
  graded algebras universal for the same property is natural**, against any pair of unital
  homomorphisms extending one morphism of the generating sheaves of modules.
* `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_natural`: **the naturality square
  for `quasicoherentExteriorPowerΓIso`**, against an arbitrary unital homomorphism of exterior
  algebras extending `φ`.
* `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_conj_pieceMap` and
  `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_conj_desc`: **conjugating the
  degree-`n` component of the canonical induced homomorphism by the two comparisons gives
  `exteriorPower.map n` of the map on global sections.**

## Implementation notes

The hypothesis on the homomorphism of algebras is the shape of
`Stacks.AffineExteriorPower.tildeExteriorPowerIso_natural`: an arbitrary
`SheafOfModules.GradedAlgebra.UnitalHom` agreeing with `φ` on the degree-one generators. The
universal property makes such a homomorphism unique, so this is no weaker than stating the
square for the canonical one, and it lets a consumer holding a homomorphism obtained some other
way apply the square without first identifying it with the canonical one.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineBaseChangeLocality (tildeΓIso)

universe t a v₁ u₁ u

namespace SheafOfModules.GradedAlgebra.IsUniversal

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{a} R} {A E A' E' : GradedAlgebra.{t, a} R}
  {P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop}
  {Q : ∀ B : GradedAlgebra.{t, a} R, (N ⟶ B.piece 1) → Prop}
  {ιA : M ⟶ A.piece 1} {ιE : M ⟶ E.piece 1} {ιA' : N ⟶ A'.piece 1} {ιE' : N ⟶ E'.piece 1}

/-- The canonical comparison of a universal graded algebra with itself is the identity: the
`desc` of its own generator is the identity homomorphism. -/
theorem pieceIso_self (hA : IsUniversal P A ιA) (n : ℤ) :
    hA.pieceIso hA n = Iso.refl (A.piece n) :=
  Iso.ext (congrArg (fun k : UnitalHom A A => k.app n) (hA.eq_id (hA.desc_extends A ιA hA.1)))

/-- **The canonical comparison between two graded algebras universal for the same property is
natural.** Let `A`, `E` both be universal for `P` over `M` and `A'`, `E'` both universal for `Q`
over `N`. A morphism `u : M ⟶ N` together with unital homomorphisms `h : A ⟶ A'` and
`g : E ⟶ E'` extending it on the degree-one generators makes the degree-`n` square

`A.piece n ⟶ E.piece n ⟶ E'.piece n = A.piece n ⟶ A'.piece n ⟶ E'.piece n`

commute, the horizontal maps being the canonical comparisons. -/
theorem pieceIso_naturality (hA : IsUniversal P A ιA) (hE : IsUniversal P E ιE)
    (hA' : IsUniversal Q A' ιA') (hE' : IsUniversal Q E' ιE') {u : M ⟶ N}
    (hu : P E' (u ≫ ιE')) {h : UnitalHom A A'} {g : UnitalHom E E'}
    (hh : ιA ≫ h.app 1 = u ≫ ιA') (hg : ιE ≫ g.app 1 = u ≫ ιE') (n : ℤ) :
    (hA.pieceIso hE n).hom ≫ g.app n = h.app n ≫ (hA'.pieceIso hE' n).hom := by
  have key : (hA.desc E ιE hE.1).comp g = h.comp (hA'.desc E' ιE' hE'.1) := by
    refine hA.hom_ext hu ?_ ?_
    · rw [UnitalHom.comp_app, ← Category.assoc, hA.desc_extends, hg]
    · rw [UnitalHom.comp_app, ← Category.assoc, hh, Category.assoc, hA'.desc_extends]
  simpa using congrArg (fun k : UnitalHom A E' => k.app n) key

end SheafOfModules.GradedAlgebra.IsUniversal

namespace Stacks.AffineExteriorPower

open SheafOfModules.GradedAlgebra (IsExteriorAlgebra SquareZero UnitalHom)

variable {R : CommRingCat.{u}} {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-! ### The associated sheaf of the global sections, naturally -/

/-- A quasi-coherent module on an affine scheme is the associated sheaf of its global sections,
naturally in the module: the isomorphisms
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso` commute with `φ` and the associated
sheaf of `Γ(φ)`. -/
theorem tildeΓIso_hom_naturality (φ : F ⟶ G) :
    tilde.map (moduleSpecΓFunctor.map φ) ≫ (tildeΓIso G).hom = (tildeΓIso F).hom ≫ φ :=
  Scheme.Modules.fromTildeΓNatTrans.naturality φ

/-! ### Factoring the quasi-coherent comparison through the one for `Γ(F)~` -/

/-- The exterior algebra of a quasi-coherent module `F`, read as an exterior algebra of the
associated sheaf `Γ(F)~` of its global sections. -/
theorem isExteriorAlgebra_tildeΓ {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf}
    {gen : F ⟶ E.piece 1} (hE : E.IsExteriorAlgebra gen) :
    IsExteriorAlgebra E ((tildeΓIso F).hom ≫ gen) :=
  hE.comp_iso (tildeΓIso F).hom (tildeΓIso F).isIso_hom

/-- The comparison of the exterior algebra `E` of `F` with the chosen exterior algebra of
`Γ(F)~`, in degree `n`. -/
noncomputable def tildeΓPieceIso {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf}
    {gen : F ⟶ E.piece 1} (hE : E.IsExteriorAlgebra gen) (n : ℕ) :
    (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exteriorPower n ≅ E.piece (n : ℤ) :=
  SheafOfModules.GradedAlgebra.IsUniversal.pieceIso
    (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.isUniversal
    (isExteriorAlgebra_tildeΓ hE).isUniversal (n : ℤ)

/-- **The quasi-coherent comparison factors through the comparison for `Γ(F)~`.** Written on the
inverses: identifying `⋀ⁿ_R Γ(F)` with the global sections of the degree-`n` piece of `E` is
identifying it with the global sections of the chosen exterior power of `Γ(F)~`, followed by the
global sections of the comparison of exterior algebras. -/
theorem quasicoherentExteriorPowerΓIso_inv_eq
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen) (n : ℕ) :
    (quasicoherentExteriorPowerΓIso F hE n).inv =
      (exteriorPowerΓIso (moduleSpecΓFunctor.obj F)
            (specTildeAlgebras R (moduleSpecΓFunctor.obj F)) n).inv ≫
        moduleSpecΓFunctor.map (tildeΓPieceIso hE n).hom := by
  have hself : (SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraIso
        (specTildeAlgebras R (moduleSpecΓFunctor.obj F))
        (specTildeAlgebras R (moduleSpecΓFunctor.obj F)) (n : ℤ)).hom =
      𝟙 ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exteriorPower n) :=
    congrArg Iso.hom (SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_self
      (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.isUniversal
      (n : ℤ))
  have hcomp := (congrArg (fun k => (AlgebraicGeometry.tildeExteriorPowerIso R
    (moduleSpecΓFunctor.obj F) n).hom ≫ k) hself).trans (Category.comp_id _)
  have hmc := moduleSpecΓFunctor.map_comp
    (AlgebraicGeometry.tildeExteriorPowerIso R (moduleSpecΓFunctor.obj F) n).hom
    (tildeΓPieceIso hE n).hom
  have h2 : (exteriorPowerΓIso (moduleSpecΓFunctor.obj F)
          (specTildeAlgebras R (moduleSpecΓFunctor.obj F)) n).inv =
      (tilde.toTildeΓNatIso.app (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))).hom ≫
        moduleSpecΓFunctor.map
          (AlgebraicGeometry.tildeExteriorPowerIso R (moduleSpecΓFunctor.obj F) n).hom :=
    (exteriorPowerΓIso_inv _ _ n).trans
      (congrArg (fun k => (tilde.toTildeΓNatIso.app
          (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))).hom ≫
        moduleSpecΓFunctor.map k)
        ((tildeExteriorPowerIso_hom (moduleSpecΓFunctor.obj F)
          (specTildeAlgebras R (moduleSpecΓFunctor.obj F)) n).trans hcomp))
  refine Eq.trans (congrArg (fun k => (tilde.toTildeΓNatIso.app
    (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))).hom ≫ k) hmc) ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ moduleSpecΓFunctor.map (tildeΓPieceIso hE n).hom) h2.symm)

/-! ### Naturality -/

/-- The naturality square of
`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso` in the orientation its inverse
composes in: the inverse of `Γ(Spec R, ⋀ⁿ F) ≅ ⋀ⁿ_R Γ(Spec R, F)` intertwines
`⋀ⁿ(Γ(φ))` with the global sections of the degree-`n` component of `g`. -/
theorem quasicoherentExteriorPowerΓIso_inv_natural (φ : F ⟶ G)
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen)
    {E' : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen' : G ⟶ E'.piece 1}
    (hE' : E'.IsExteriorAlgebra gen') (g : UnitalHom E E')
    (hg : gen ≫ g.app 1 = φ ≫ gen') (n : ℕ) :
    ModuleCat.ofHom (R := R)
          (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))
          (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj G)))
          (exteriorPower.map n (moduleSpecΓFunctor.map φ).hom) ≫
        (quasicoherentExteriorPowerΓIso G hE' n).inv =
      (quasicoherentExteriorPowerΓIso F hE n).inv ≫
        moduleSpecΓFunctor.map (g.app (n : ℤ)) := by
  have hsheaf := exteriorPowerΓIso_inv_natural (moduleSpecΓFunctor.map φ) n
    (specTildeAlgebras R (moduleSpecΓFunctor.obj F))
    (specTildeAlgebras R (moduleSpecΓFunctor.obj G))
    ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.map
      (specTildeAlgebras R (moduleSpecΓFunctor.obj G)).exterior_isExteriorAlgebra
      (tilde.map (moduleSpecΓFunctor.map φ)))
    ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.map_app_one
      (specTildeAlgebras R (moduleSpecΓFunctor.obj G)).exterior_isExteriorAlgebra
      (tilde.map (moduleSpecΓFunctor.map φ)))
  have hpiece : (tildeΓPieceIso hE n).hom ≫ g.app (n : ℤ) =
      ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.map
          (specTildeAlgebras R (moduleSpecΓFunctor.obj G)).exterior_isExteriorAlgebra
          (tilde.map (moduleSpecΓFunctor.map φ))).app (n : ℤ) ≫
        (tildeΓPieceIso hE' n).hom :=
    SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_naturality
      (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.isUniversal
      (isExteriorAlgebra_tildeΓ hE).isUniversal
      (specTildeAlgebras R (moduleSpecΓFunctor.obj G)).exterior_isExteriorAlgebra.isUniversal
      (isExteriorAlgebra_tildeΓ hE').isUniversal
      ((isExteriorAlgebra_tildeΓ hE').1.comp (tilde.map (moduleSpecΓFunctor.map φ)))
      ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.map_app_one
        (specTildeAlgebras R (moduleSpecΓFunctor.obj G)).exterior_isExteriorAlgebra
        (tilde.map (moduleSpecΓFunctor.map φ)))
      ((Category.assoc _ _ _).trans
        (((congrArg (fun k => (tildeΓIso F).hom ≫ k) hg).trans
            (Category.assoc _ _ _).symm).trans
          ((congrArg (fun k => k ≫ gen') (tildeΓIso_hom_naturality φ).symm).trans
            (Category.assoc _ _ _))))
      (n : ℤ)
  have hmid := ((moduleSpecΓFunctor.map_comp _ _).symm.trans
    (congrArg moduleSpecΓFunctor.map hpiece.symm)).trans (moduleSpecΓFunctor.map_comp _ _)
  rw [quasicoherentExteriorPowerΓIso_inv_eq, quasicoherentExteriorPowerΓIso_inv_eq,
    Category.assoc, ← hmid, ← Category.assoc, hsheaf, Category.assoc]

/-- **The exterior-power assertion of Tag 01I8 for a quasi-coherent module is natural on global
sections.** For a morphism `φ : F ⟶ G` of quasi-coherent modules on `Spec R` and a unital
homomorphism `g` of exterior algebras of `F` and `G` extending `φ` on the degree-one generators,
applying `g` in degree `n` on global sections and then identifying with `⋀ⁿ_R Γ(G)` is the same
as identifying with `⋀ⁿ_R Γ(F)` and then applying `⋀ⁿ(Γ(φ))`. -/
theorem quasicoherentExteriorPowerΓIso_natural (φ : F ⟶ G)
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen)
    {E' : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen' : G ⟶ E'.piece 1}
    (hE' : E'.IsExteriorAlgebra gen') (g : UnitalHom E E')
    (hg : gen ≫ g.app 1 = φ ≫ gen') (n : ℕ) :
    moduleSpecΓFunctor.map (g.app (n : ℤ)) ≫
        (quasicoherentExteriorPowerΓIso G hE' n).hom =
      (quasicoherentExteriorPowerΓIso F hE n).hom ≫ ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))
        (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj G)))
        (exteriorPower.map n (moduleSpecΓFunctor.map φ).hom) := by
  rw [(Iso.inv_comp_eq _).mp
      (quasicoherentExteriorPowerΓIso_inv_natural φ hE hE' g hg n).symm,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Conjugating by the comparisons -/

/-- **Conjugating by the two comparisons turns the global sections of a degree-`n` `desc`-map
into `exteriorPower.map n` of its degree-one part.** If `g : E ⟶ E'` is a unital homomorphism of
exterior algebras extending `φ : F ⟶ G` on the degree-one generators, then reading
`Γ(Spec R, g_n)` through `Γ(Spec R, ⋀ⁿ F) ≅ ⋀ⁿ_R Γ(Spec R, F)` and
`Γ(Spec R, ⋀ⁿ G) ≅ ⋀ⁿ_R Γ(Spec R, G)` gives exactly `⋀ⁿ(Γ(φ))`. -/
theorem quasicoherentExteriorPowerΓIso_conj (φ : F ⟶ G)
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen)
    {E' : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen' : G ⟶ E'.piece 1}
    (hE' : E'.IsExteriorAlgebra gen') (g : UnitalHom E E')
    (hg : gen ≫ g.app 1 = φ ≫ gen') (n : ℕ) :
    (quasicoherentExteriorPowerΓIso F hE n).inv ≫
        moduleSpecΓFunctor.map (g.app (n : ℤ)) ≫
          (quasicoherentExteriorPowerΓIso G hE' n).hom =
      ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))
        (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj G)))
        (exteriorPower.map n (moduleSpecΓFunctor.map φ).hom) := by
  rw [quasicoherentExteriorPowerΓIso_natural φ hE hE' g hg n, Iso.inv_hom_id_assoc]

/-- **The global sections of the degree-`n` `desc`-map are `exteriorPower.map n` of the map on
global sections.** This is
`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_conj` for the homomorphism
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.desc` produces from the square-zero degree-one
generator `φ ≫ gen'` of `E'` indexed by `F`. -/
theorem quasicoherentExteriorPowerΓIso_conj_desc (φ : F ⟶ G)
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen)
    {E' : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen' : G ⟶ E'.piece 1}
    (hE' : E'.IsExteriorAlgebra gen') (hsq : SquareZero (φ ≫ gen')) (n : ℕ) :
    (quasicoherentExteriorPowerΓIso F hE n).inv ≫
        moduleSpecΓFunctor.map ((hE.desc E' (φ ≫ gen') hsq).app (n : ℤ)) ≫
          (quasicoherentExteriorPowerΓIso G hE' n).hom =
      ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))
        (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj G)))
        (exteriorPower.map n (moduleSpecΓFunctor.map φ).hom) :=
  quasicoherentExteriorPowerΓIso_conj φ hE hE' _ (hE.desc_extends E' (φ ≫ gen') hsq) n

/-- **The global sections of the canonical degree-`n` map induced by `φ` are
`exteriorPower.map n` of the map `φ` induces on global sections.** This is
`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_conj_desc` for the canonical
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap`, the degree-`n` component of the
homomorphism of exterior algebras that the universal property produces from `φ`. -/
theorem quasicoherentExteriorPowerΓIso_conj_pieceMap (φ : F ⟶ G)
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen)
    {E' : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen' : G ⟶ E'.piece 1}
    (hE' : E'.IsExteriorAlgebra gen') (n : ℕ) :
    (quasicoherentExteriorPowerΓIso F hE n).inv ≫
        moduleSpecΓFunctor.map (hE.pieceMap hE' φ (n : ℤ)) ≫
          (quasicoherentExteriorPowerΓIso G hE' n).hom =
      ModuleCat.ofHom (R := R)
        (X := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj F)))
        (Y := ModuleCat.of ↥R ↥(⋀[↥R]^n ↥(moduleSpecΓFunctor.obj G)))
        (exteriorPower.map n (moduleSpecΓFunctor.map φ).hom) :=
  quasicoherentExteriorPowerΓIso_conj_desc φ hE hE' (hE'.1.comp φ) n

end Stacks.AffineExteriorPower

end
