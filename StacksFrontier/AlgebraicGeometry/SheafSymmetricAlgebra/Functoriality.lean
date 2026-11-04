module

public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the symmetric algebra of a module on a scheme

A morphism `u : E₁ ⟶ E₂` of modules induces a homomorphism `Sym(E₁) ⟶ Sym(E₂)` of their
symmetric algebras. This file builds it, first sectionwise on an arbitrary site and then, after
the degreewise sheafification, as a homomorphism of the sheaf-level graded `𝒪_X`-algebras that
the relative Proj construction consumes.

## Main definitions

* `Stacks.SymGraded.siteGradedPieceMap`: the sectionwise degree-`n` map
  `Sym^n(E₁) ⟶ Sym^n(E₂)` of presheaves of modules.
* `Stacks.SymGraded.schemeSymAlgebraHom`: the induced homomorphism
  `Sym(E₁) ⟶ Sym(E₂)` of sheaves of graded algebras on a scheme.
* `Stacks.SymGraded.schemeSheafGradedAlgebraHom`: **the same as a
  `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom`**, the input of Tag
  07ZG's relative Proj morphism.

## Main results

* `Stacks.SymGraded.siteGradedPieceMap_siteMul` and
  `Stacks.SymGraded.siteGradedPieceMap_siteOne`: the sectionwise map is multiplicative and
  unital.
* `Stacks.SymGraded.schemeSymAlgebraHom_app_one`: the sheafified homomorphism is unital, which
  `Stacks.GradedAlgebra.sheafifyGradedHom` does not record.

## Implementation notes

The only new mathematics is the sectionwise map: it is `Stacks.SymGraded.gradedMapₛₗ` along the
identity ring homomorphism, and its naturality is two applications of
`SymmetricAlgebra.mapₛₗ_eq_comp` through the common composite
`Γ(E₁, U) → Γ(E₂, U) → Γ(E₂, V)`, the two factorizations of which agree by the naturality of
`u`. Multiplicativity and unitality are `Stacks.SymGraded.gradedMapₛₗ_symMulₗ` and
`Stacks.SymGraded.gradedMapₛₗ_oneG`.

Everything after that is already in the library: the transport across the degreewise
sheafification is `Stacks.GradedAlgebra.sheafifyGradedHom`, and the bridge to
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` is definitional, by
`Stacks.SymGraded.schemeSheafGradedAlgebra_piece` and
`Stacks.SymGraded.schemeSheafGradedAlgebra_mul_app`.

`Stacks.GradedAlgebra.sheafifyGradedHom` asks only for multiplicativity, so the unit law has to
be proved separately; it is the naturality of the sheafification unit applied to the sectionwise
unit.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)

## Not done here

No tag attribute is attached: the functoriality of the symmetric algebra is an input of the tags
that use it, not a clause of one. Nothing is said about the universal property of the symmetric
algebra, nor about surjectivity of the induced map on homogeneous sections, which is the separate
hypothesis `Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.SymGraded

universe v u w

/-! ### The sectionwise map -/

section Presheaf

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)} (u : F ⟶ G)

/-- **The sectionwise map of symmetric algebras commutes with restriction.** Both composites
`Sym(Γ(F, X)) → Sym(Γ(G, Y))` are the base change of the symmetric algebra along the one
semilinear map `Γ(F, X) → Γ(G, Y)`, which has the two factorizations the naturality of `u`
identifies. -/
public theorem mapₛₗ_app_comm {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (z : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    SymmetricAlgebra.mapₛₗ (RingHom.id _) (ModuleCat.Hom.hom (u.app Y))
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) z) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (G.restrictₛₗ f)
        (SymmetricAlgebra.mapₛₗ (RingHom.id _) (ModuleCat.Hom.hom (u.app X)) z) := by
  have hnat : ∀ m : F.obj X,
      ModuleCat.Hom.hom (u.app Y) (F.restrictₛₗ f m) =
        G.restrictₛₗ f (ModuleCat.Hom.hom (u.app X) m) :=
    fun m => PresheafOfModules.naturality_apply u f m
  have h1 := SymmetricAlgebra.mapₛₗ_eq_comp (ModuleCat.Hom.hom (u.app X)) (G.restrictₛₗ f)
    ((G.restrictₛₗ f).comp (ModuleCat.Hom.hom (u.app X))) (fun _ => rfl) (fun _ => rfl) z
  have h2 := SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (ModuleCat.Hom.hom (u.app Y))
    ((G.restrictₛₗ f).comp (ModuleCat.Hom.hom (u.app X))) (fun _ => rfl)
    (fun m => (hnat m).symm) z
  exact h2.symm.trans h1

/-- **The degree-`n` piece of the sectionwise symmetric algebra is functorial in the module.**
A morphism `u : F ⟶ G` of presheaves of modules induces `Sym^n(F) ⟶ Sym^n(G)`, sectionwise
`Stacks.SymGraded.gradedMapₛₗ` along the identity ring homomorphism. -/
public def siteGradedPieceMap (n : ℤ) : siteGradedPiece F n ⟶ siteGradedPiece G n where
  app X := ModuleCat.ofHom (gradedMapₛₗ n (RingHom.id _) (ModuleCat.Hom.hom (u.app X)))
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    Subtype.ext (mapₛₗ_app_comm u f x.val))

/-- On sections over `X`, the degree-`n` map induced by `u` is `SymmetricAlgebra.mapₛₗ` of the
map `u.app X` on sections, applied to the underlying element of the symmetric algebra. -/
@[simp]
public theorem siteGradedPieceMap_app_val (n : ℤ) (X : Cᵒᵖ)
    (x : (siteGradedPiece F n).obj X) :
    (PresheafOfModules.Hom.app (siteGradedPieceMap u n) X x).val =
      SymmetricAlgebra.mapₛₗ (RingHom.id _) (ModuleCat.Hom.hom (u.app X)) x.val := rfl

/-- The sectionwise map is multiplicative for the graded multiplication. -/
public theorem siteGradedPieceMap_siteMul (i j : ℤ) (X : Cᵒᵖ)
    (x : (siteGradedPiece F i).obj X) (y : (siteGradedPiece F j).obj X) :
    PresheafOfModules.Hom.app (siteGradedPieceMap u (i + j)) X ((siteMul F i j).app X x y) =
      (siteMul G i j).app X (PresheafOfModules.Hom.app (siteGradedPieceMap u i) X x)
        (PresheafOfModules.Hom.app (siteGradedPieceMap u j) X y) :=
  Subtype.ext (map_mul (SymmetricAlgebra.mapₛₗ (RingHom.id _)
    (ModuleCat.Hom.hom (u.app X))) x.val y.val)

/-- The sectionwise map carries the unit to the unit. -/
public theorem siteGradedPieceMap_siteOne (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (siteGradedPieceMap u 0) X ((siteOne F).eval X) =
      (siteOne G).eval X :=
  Subtype.ext (map_one (SymmetricAlgebra.mapₛₗ (RingHom.id _)
    (ModuleCat.Hom.hom (u.app X))))

end Presheaf

/-! ### The homomorphism of sheaves of graded algebras -/

section Scheme

variable {X : Scheme.{u}} {E₁ E₂ : X.Modules} (u : E₁ ⟶ E₂)

/-- **The symmetric algebra of a module on a scheme is functorial in the module.** The
degreewise sheafification of the sectionwise map, as a homomorphism of sheaves of graded
`𝒪_X`-algebras. -/
@[ega "II 1.7.4" "special case"]
public def schemeSymAlgebraHom :
    Scheme.Modules.symmetricAlgebra X E₁ ⟶ Scheme.Modules.symmetricAlgebra X E₂ :=
  (sitePresheafAlgebra E₁.val).sheafifyGradedHom (𝟙 X.ringCatSheaf.obj)
    (sitePresheafAlgebra E₂.val) (siteGradedPieceMap u.val)
    (siteGradedPieceMap_siteMul u.val)

/-- The degree-`n` component of `schemeSymAlgebraHom u` is the sheafification of the degree-`n`
sectionwise map `siteGradedPieceMap u.val n`. -/
public theorem schemeSymAlgebraHom_app (n : ℤ) :
    (schemeSymAlgebraHom u).app n =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (siteGradedPieceMap u.val n) := rfl

/-- **The induced homomorphism is unital.** `Stacks.GradedAlgebra.sheafifyGradedHom` records only
multiplicativity; the unit law is the naturality of the sheafification unit applied to the
sectionwise unit. -/
public theorem schemeSymAlgebraHom_app_one (U : (Opens X.carrier)ᵒᵖ) :
    ((schemeSymAlgebraHom u).app 0).val.app U
        ((Scheme.Modules.symmetricAlgebra X E₁).one.eval U) =
      (Scheme.Modules.symmetricAlgebra X E₂).one.eval U := by
  have h := PresheafOfModules.unit_naturality_apply (α := 𝟙 X.ringCatSheaf.obj)
    (siteGradedPieceMap u.val 0) U ((sitePresheafAlgebra E₁.val).one.eval U)
  exact h.trans (congrArg
    (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E₂.val 0)) U)
    (siteGradedPieceMap_siteOne u.val U))

/-- **Functoriality of the sheafified symmetric algebra, in the form the relative Proj
construction consumes.** A morphism `u : E₁ ⟶ E₂` of modules whose symmetric algebras have
quasi-coherent homogeneous pieces induces a homomorphism of the sheaf-level graded
`𝒪_X`-algebras `Sym(E₁) ⟶ Sym(E₂)`, which is the input of Tag 07ZG's open `U(ψ)` and its
morphism of relative projective spectra. -/
public def schemeSheafGradedAlgebraHom (hqc₁ : IsQuasicoherentPieces E₁)
    (hqc₂ : IsQuasicoherentPieces E₂) :
    SheafGradedAlgebraHom (schemeSheafGradedAlgebra E₁ hqc₁)
      (schemeSheafGradedAlgebra E₂ hqc₂) where
  app n := (schemeSymAlgebraHom u).app n
  app_mul i j U a b := (schemeSymAlgebraHom u).map_mul i j (op U) a b
  app_one U := schemeSymAlgebraHom_app_one u (op U)

/-- The degree-`n` component of `schemeSheafGradedAlgebraHom u hqc₁ hqc₂` is the degree-`n`
component of `schemeSymAlgebraHom u`. -/
public theorem schemeSheafGradedAlgebraHom_app (hqc₁ : IsQuasicoherentPieces E₁)
    (hqc₂ : IsQuasicoherentPieces E₂) (n : ℤ) :
    (schemeSheafGradedAlgebraHom u hqc₁ hqc₂).app n = (schemeSymAlgebraHom u).app n := rfl

end Scheme

end Stacks.SymGraded

end
