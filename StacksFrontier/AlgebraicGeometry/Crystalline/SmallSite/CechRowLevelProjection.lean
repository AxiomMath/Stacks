module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialTotalRowZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9

/-!
# The projection of a Čech row onto one level

Fix a global crystalline situation `(p, (S, I, γ), X)`, a cosimplicial system `T(n)_e` of objects
of `Cris(X/S)` and a complex `K^•` of abelian sheaves on `Cris(X/S)`.  The row `b` of the Čech
complex of cosimplicial groups of `K^•` (`...SmallSite.cechCosimplicialComplex`) is the complex
`a ↦ lim_e K^a(T(b)_e)`.  This module constructs its projection onto the sections of `K^•` over a
single level `T(b)_e`,

`lim_e K^•(T(b)_e) ⟶ K^•(T(b)_e)`,

as a morphism of complexes (`cechRowLevelProjection`), proves that it carries the coprojection
`lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` of the Čech rows to the restriction of sections of `K^•`
along `T(b)_e ⟶ T(0)_e` (`cosimplicialRowCoprojection_comp_cechRowLevelProjection`), and that it
is an isomorphism as soon as every limit projection of the terms is one
(`isIso_cechRowLevelProjection`).

Nothing here says when the limit projections are isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
  (K : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ)

/-- The sections over an object `B` of `Cris(X/S)` of a complex of abelian sheaves, as a complex
of abelian groups. -/
abbrev sectionsComplexAt (B : CrystallineThickening S) : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op B)).mapHomologicalComplex _).obj K

/-- The restriction of sections of a complex of abelian sheaves along a morphism `k : B ⟶ B'` of
`Cris(X/S)`, as a morphism of complexes `K^•(B') ⟶ K^•(B)`. -/
abbrev sectionsComplexRestrict {B B' : CrystallineThickening S} (k : B ⟶ B') :
    sectionsComplexAt K B' ⟶ sectionsComplexAt K B :=
  (NatTrans.mapHomologicalComplex (Functor.whiskerLeft
    (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
      ((evaluation _ _).map k.op)) (ComplexShape.up ℕ)).app K

/-- **The projection of the row `b` of the Čech complex onto the level `e`**:
`lim_e K^•(T(b)_e) ⟶ K^•(T(b)_e)`, the limit projection in every degree. -/
def cechRowLevelProjection (b e : ℕ) :
    cosimplicialRowComplex ((cechCosimplicialComplex T).obj K) b ⟶
      sectionsComplexAt K ((T.obj (op ⦋b⦌)).obj e) where
  f a := limit.π ((T.obj (op ⦋b⦌)).op ⋙ (K.X a).obj) (op e)
  comm' a a' _ := (levelLimitFunctor_map_π (T.obj (op ⦋b⦌)) ((K.d a a').hom) (op e)).symm

/-- The degree-`a` component of the projection is the limit projection. -/
theorem cechRowLevelProjection_f (b e a : ℕ) :
    (cechRowLevelProjection T K b e).f a =
      limit.π ((T.obj (op ⦋b⦌)).op ⋙ (K.X a).obj) (op e) := rfl

/-- **The projections carry the coprojections of the Čech rows to restrictions of sections**:
the coprojection `lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` followed by the projection to the level
`e` is the projection to the level `e` followed by the restriction along `T(b)_e ⟶ T(0)_e`. -/
theorem cosimplicialRowCoprojection_comp_cechRowLevelProjection (b e : ℕ) :
    cosimplicialRowCoprojection ((cechCosimplicialComplex T).obj K) b ≫
        cechRowLevelProjection T K b e =
      cechRowLevelProjection T K 0 e ≫
        sectionsComplexRestrict K ((T.map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0).op).app e) := by
  ext a : 1
  exact limMap_π _ _

/-- **The projection of a Čech row onto a level is an isomorphism** as soon as every limit
projection `lim_e K^a(T(b)_e) ⟶ K^a(T(b)_e)` is one. -/
theorem isIso_cechRowLevelProjection (b e : ℕ)
    (h : ∀ a, IsIso (limit.π ((T.obj (op ⦋b⦌)).op ⋙ (K.X a).obj) (op e))) :
    IsIso (cechRowLevelProjection T K b e) := by
  have : ∀ a, IsIso ((cechRowLevelProjection T K b e).f a) := h
  exact HomologicalComplex.Hom.isIso_of_components _

end Crystalline.GlobalCrystallineSituation.SmallSite

end
