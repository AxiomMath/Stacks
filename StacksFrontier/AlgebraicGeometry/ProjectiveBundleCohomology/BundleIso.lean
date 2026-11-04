module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Statement
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial

/-!
# The projective bundle of an isomorphic module

An isomorphism `φ : E ≅ E'` of `𝒪_S`-modules induces an isomorphism of graded algebras
`Sym(φ) : Sym(E) ≅ Sym(E')`, and hence an isomorphism `𝐏(E') ≅ 𝐏(E)` of projective bundles over
`S`, which over the chart of an affine open `U` of `S` is `Proj` of the isomorphism of graded rings
of sections `Γ(U, Sym(E)) ≅ Γ(U, Sym(E'))`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.symHom`: `Sym(φ)` for a morphism
  `φ : E ⟶ E'`, as a homomorphism of graded algebras.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleMap`: the morphism `𝐏(E') ⟶ 𝐏(E)`
  induced by an isomorphism `E ≅ E'`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleIso`: the same as an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleMap_comp_toBase`: it is a morphism
  over `S`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.chart_comp_bundleMap`: its description on
  the charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} {E E' E'' : S.Modules} {r : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E r)
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' r)
  (hfree'' : Scheme.Modules.IsFiniteLocallyFreeOfRank E'' r)

/-- **`Sym(φ) : Sym(E) ⟶ Sym(E')`** for a morphism `φ : E ⟶ E'`, as a homomorphism of the graded
algebras of the projective bundles. -/
public def symHom (φ : E ⟶ E') :
    SheafGradedAlgebraHom (bundleAlgebra E hfree) (bundleAlgebra E' hfree') where
  app n := (Scheme.Modules.symmetricAlgebraUnitalHom S φ).app n
  app_mul i j U a b := (Scheme.Modules.symmetricAlgebraUnitalHom S φ).map_mul i j (op U) a b
  app_one U := (Scheme.Modules.symmetricAlgebraUnitalHom S φ).map_one (op U)

/-- `Sym` is functorial: in each degree, `Sym(φ)` followed by `Sym(φ')` is `Sym(φ ≫ φ')`. -/
public theorem symHom_app_comp (φ : E ⟶ E') (φ' : E' ⟶ E'') (n : ℤ) :
    (symHom hfree hfree' φ).app n ≫ (symHom hfree' hfree'' φ').app n =
      (symHom hfree hfree'' (φ ≫ φ')).app n :=
  (congrArg (fun f => SheafOfModules.GradedAlgebra.UnitalHom.app f n)
    (Scheme.Modules.symmetricAlgebraUnitalHom_comp S φ φ')).symm

/-- `Sym(𝟙 E)` is the identity in each degree. -/
public theorem symHom_app_id (n : ℤ) : (symHom hfree hfree (𝟙 E)).app n = 𝟙 _ :=
  congrArg (fun f => SheafOfModules.GradedAlgebra.UnitalHom.app f n)
    (Scheme.Modules.symmetricAlgebraUnitalHom_id S (F := E))

/-- `Sym(e)` is an isomorphism in every degree for an isomorphism `e`. -/
public instance isIso_symHom_app (e : E ≅ E') (n : ℤ) : IsIso ((symHom hfree hfree' e.hom).app n) :=
  ⟨(symHom hfree' hfree e.inv).app n,
    by rw [symHom_app_comp, e.hom_inv_id, symHom_app_id],
    by rw [symHom_app_comp, e.inv_hom_id, symHom_app_id]⟩

/-- On homogeneous sections of degree `k` over `U`, `Sym(φ)` followed by `Sym(φ')` is
`Sym(φ ≫ φ')`. -/
public theorem symHom_sectionPieceHom_comp (φ : E ⟶ E') (φ' : E' ⟶ E'') (U : S.Opens) (k : ℕ)
    (a : (bundleAlgebra E hfree).sectionPieces U k) :
    (symHom hfree' hfree'' φ').sectionPieceHom U k ((symHom hfree hfree' φ).sectionPieceHom U k a) =
      (symHom hfree hfree'' (φ ≫ φ')).sectionPieceHom U k a := by
  simp only [SheafGradedAlgebraHom.sectionPieceHom_apply]
  rw [← symHom_app_comp hfree hfree' hfree'' φ φ' (k : ℤ)]
  rfl

/-- On the graded ring of sections over `U`, `Sym(φ)` followed by `Sym(φ')` is `Sym(φ ≫ φ')`. -/
public theorem symHom_sectionHom_comp (φ : E ⟶ E') (φ' : E' ⟶ E'') (U : S.Opens)
    (x : (bundleAlgebra E hfree).sectionRing U) :
    (symHom hfree' hfree'' φ').sectionHom U ((symHom hfree hfree' φ).sectionHom U x) =
      (symHom hfree hfree'' (φ ≫ φ')).sectionHom U x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a =>
    rw [SheafGradedAlgebraHom.sectionHom_of, SheafGradedAlgebraHom.sectionHom_of,
      SheafGradedAlgebraHom.sectionHom_of, symHom_sectionPieceHom_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `Sym(𝟙 E)` is the identity on homogeneous sections of degree `k` over `U`. -/
private theorem symHom_sectionPieceHom_id (U : S.Opens) (k : ℕ)
    (a : (bundleAlgebra E hfree).sectionPieces U k) :
    (symHom hfree hfree (𝟙 E)).sectionPieceHom U k a = a := by
  simp only [SheafGradedAlgebraHom.sectionPieceHom_apply]
  rw [symHom_app_id hfree (k : ℤ)]
  rfl

/-- `Sym(𝟙 E)` is the identity on the graded ring of sections over `U`. -/
public theorem symHom_sectionHom_id (U : S.Opens) (x : (bundleAlgebra E hfree).sectionRing U) :
    (symHom hfree hfree (𝟙 E)).sectionHom U x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a =>
    rw [SheafGradedAlgebraHom.sectionHom_of, symHom_sectionPieceHom_id]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `Sym(e)` is surjective on homogeneous sections for an isomorphism `e`. -/
public theorem surjectiveOnAffineSections_symHom (e : E ≅ E') :
    SurjectiveOnAffineSections (symHom hfree hfree' e.hom) := fun U _ k b =>
  ⟨(symHom hfree' hfree e.inv).sectionPieceHom U k b, by
    rw [symHom_sectionPieceHom_comp, e.inv_hom_id, symHom_sectionPieceHom_id]⟩

/-- **The morphism of projective bundles `𝐏(E') ⟶ 𝐏(E)` induced by an isomorphism
`e : E ≅ E'`.** -/
public def bundleMap (e : E ≅ E') :
    (relativeProj (bundleAlgebra E' hfree')).scheme ⟶
      (relativeProj (bundleAlgebra E hfree)).scheme :=
  map (surjectiveOnAffineSections_symHom hfree hfree' e)

/-- **The morphism of projective bundles is over `S`.** -/
@[reassoc]
public theorem bundleMap_comp_toBase (e : E ≅ E') :
    bundleMap hfree hfree' e ≫ (relativeProj (bundleAlgebra E hfree)).toBase =
      (relativeProj (bundleAlgebra E' hfree')).toBase :=
  map_comp_toBase _

/-- On the chart over an affine open `U` of `S`, the morphism of projective bundles is `Proj` of
`Γ(U, Sym(e)) : Γ(U, Sym(E)) ≅ Γ(U, Sym(E'))`. -/
@[reassoc]
public theorem chart_comp_bundleMap (e : E ≅ E') (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeProj (bundleAlgebra E' hfree')).chart U hU ≫ bundleMap hfree hfree' e =
      Proj.map ((symHom hfree hfree' e.hom).sectionHom U)
          (irrelevant_le_map_sectionHom (surjectiveOnAffineSections_symHom hfree hfree' e) hU) ≫
        (relativeProj (bundleAlgebra E hfree)).chart U hU := by
  rw [bundleMap, chart_comp_map, chartMap_eq_map]

/-- The morphism `𝐏(E) ⟶ 𝐏(E')` induced by `e.symm`, followed by the morphism `𝐏(E') ⟶ 𝐏(E)`
induced by `e`, is the identity of `𝐏(E)`. -/
public theorem bundleMap_comp_bundleMap (e : E ≅ E') :
    bundleMap hfree' hfree e.symm ≫ bundleMap hfree hfree' e = 𝟙 _ := by
  refine colimit.hom_ext
    (F := (RelativeProjGlue.relativeGluingData (bundleAlgebra E hfree).toGradedAlgebra).functor)
    fun V => ?_
  show (relativeProj (bundleAlgebra E hfree)).chart V.toOpens V.2 ≫ _ =
    (relativeProj (bundleAlgebra E hfree)).chart V.toOpens V.2 ≫ 𝟙 _
  rw [chart_comp_bundleMap_assoc, chart_comp_bundleMap, ← Category.assoc, Category.comp_id,
    ← Proj.map_comp]
  · conv_rhs => rw [← Category.id_comp ((relativeProj (bundleAlgebra E hfree)).chart _ _)]
    congr 1
    have h : ((symHom hfree' hfree e.symm.hom).sectionHom V.toOpens).comp
        ((symHom hfree hfree' e.hom).sectionHom V.toOpens) = GradedRingHom.id _ :=
      GradedRingHom.ext fun x => (symHom_sectionHom_comp hfree hfree' hfree e.hom e.inv _ x).trans
        (by rw [e.hom_inv_id]; exact symHom_sectionHom_id hfree _ x)
    convert Proj.map_id (𝒜 := (bundleAlgebra E hfree).grading V.toOpens)

/-- **The isomorphism of projective bundles `𝐏(E') ≅ 𝐏(E)` over `S` induced by `e : E ≅ E'`.** -/
public def bundleIso (e : E ≅ E') :
    (relativeProj (bundleAlgebra E' hfree')).scheme ≅
      (relativeProj (bundleAlgebra E hfree)).scheme where
  hom := bundleMap hfree hfree' e
  inv := bundleMap hfree' hfree e.symm
  hom_inv_id := by simpa using bundleMap_comp_bundleMap hfree' hfree e.symm
  inv_hom_id := bundleMap_comp_bundleMap hfree hfree' e

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
