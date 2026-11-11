module

public import StacksFrontier.Algebra.Homology.AcyclicMappingConeQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9

/-!
# A quasi-isomorphism of complexes of sheaves induces quasi-isomorphisms of the Čech rows

Fix a global crystalline situation `(p, (S, I, γ), X)` and a cosimplicial system `T(b)_e` of
objects of the small crystalline site `Cris(X/S)`, carried as a
`CategoryTheory.SimplicialObject (ℕ ⥤ CrystallineThickening S)`, whose tower maps are
monomorphisms (`HasAffineMonoLevels`).  Let `φ : K^• ⟶ J^•` be a quasi-isomorphism of
`ℕ`-indexed complexes of abelian sheaves, with `J^•` termwise injective and `K^•` termwise
acyclic at the level objects (`VanishingOnLevels07Q9`) with surjective restriction maps along the
towers (`HasSurjectiveLevelTransitions`).  This file proves that for every Čech degree `b` the map

`(a ↦ lim_e K^a(T(b)_e)) ⟶ (a ↦ lim_e J^a(T(b)_e))`

— the row `b` of the map of complexes of cosimplicial groups induced by `φ` — is a
quasi-isomorphism (`quasiIso_cosimplicialRowMap_cechCosimplicialComplex_map`).

The proof has two steps.

* **Over one object.**  For an object `A` of `Cris(X/S)` at which every `K^a` has vanishing higher
  cohomology, the sections over `A` carry `φ` to a quasi-isomorphism
  (`quasiIso_sectionsFunctorOver_map`), and carry the mapping cone `C` of `φ` (extended by zero to
  `ℤ`) to an acyclic complex (`acyclic_sectionsFunctorOver_mappingCone`).  This is
  `Stacks.RightDerivedComp.quasiIso_mapHomologicalComplex_map_of_acyclic` for the sections
  functor, whose right derived functors are the cohomology of the localized site
  (`overCohomologyIsoRightDerivedSections`); injective sheaves are acyclic.
* **Along the towers.**  The towers `e ↦ C^n(T(b)_e)` are Mittag-Leffler, `C^n` being
  `K^{n+1} ⊕ J^n` and both summands having surjective transition maps (for `J` by injectivity,
  `hasSurjectiveLevelTransitions_of_injective`), and each level `e ↦ C^•(T(b)_e)` is acyclic by
  the first step.  [Stacks, Tag 070E], on the four-term windows of the complex of towers
  (`Stacks.TowerAcyclicity.acyclic_mapHomologicalComplex_lim`), makes `lim_e C^•(T(b)_e)`
  acyclic; it is the mapping cone of the row map, which is therefore a quasi-isomorphism.

Everything is proved; there are no hypotheses beyond those of the statements.

## Main results

* `Stacks.TowerAcyclicity.acyclic_mapHomologicalComplex_lim`: the limit of a `ℤ`-indexed complex
  of towers of abelian groups, Mittag-Leffler termwise and acyclic at each level, is acyclic.
* `Crystalline.GlobalCrystallineSituation.SmallSite.quasiIso_sectionsFunctorOver_map`: the
  sections over an object `A` carry `φ` to a quasi-isomorphism when the higher cohomology of the
  `K^a` over `A` vanishes and the `J^a` are injective.
* `quasiIso_cosimplicialRowMap_cechCosimplicialComplex_map` (in the same namespace): the row
  maps of the Čech complex of `φ` are quasi-isomorphisms.

## References

* [Stacks Project, Tag 070E](https://stacks.math.columbia.edu/tag/070E)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

noncomputable section

namespace Stacks.TowerAcyclicity

universe v

/-- **The limit of a complex of towers of abelian groups which is Mittag-Leffler termwise and
acyclic at each level is acyclic.**  In each degree `n` this is [Stacks, Tag 070E] on the window
`X^{n-2} → X^{n-1} → X^n → X^{n+1}` (`isZero_homology_window`): the first two towers are
Mittag-Leffler and the homology at `X^{n-1}` and at `X^n` vanishes at each level. -/
theorem acyclic_mapHomologicalComplex_lim (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ)
    (hML : ∀ n, (X.X n ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler)
    (hz : ∀ e : ℕᵒᵖ, ((((evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X).Acyclic) :
    (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X).Acyclic := by
  have hzero (i j k : ℤ) : ∀ e, (X.d i j).app e ≫ (X.d j k).app e = 0 := fun e => by
    rw [← NatTrans.comp_app, X.d_comp_d, NatTrans.app_zero]
  have hw (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) (e : ℕᵒᵖ) :
      IsZero ((invSystemShortComplex (X.d i j) (X.d j k) (hzero i j k) e).homology) := by
    have h := hz e j
    rw [HomologicalComplex.exactAt_iff' _ i j k ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjk), ShortComplex.exact_iff_isZero_homology] at h
    exact h
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)
    ((ComplexShape.up ℤ).prev_eq' (show n - 1 + 1 = n by omega))
    ((ComplexShape.up ℤ).next_eq' rfl), ShortComplex.exact_iff_isZero_homology]
  exact isZero_homology_window (X.d (n - 2) (n - 1)) (X.d (n - 1) n) (X.d n (n + 1))
    (hzero _ _ _) (hzero _ _ _) (hML _) (hML _) (hw _ _ _ (by omega) (by omega))
    (hw _ _ _ (by omega) rfl)

/-- A tower of abelian groups which is a zero object of the functor category is
Mittag-Leffler. -/
theorem isMittagLeffler_of_isZero (A : ℕᵒᵖ ⥤ AddCommGrpCat.{v}) (h : IsZero A) :
    (A ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler :=
  isMittagLeffler_of_surjective_succ A fun e _ =>
    have := AddCommGrpCat.subsingleton_of_isZero (h.obj (op e))
    ⟨0, Subsingleton.elim _ _⟩

end Stacks.TowerAcyclicity

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **The tower of sections `F ↦ (e ↦ F(T_e))`** along a tower `T` of objects of `Cris(X/S)`, as
a functor of the abelian sheaf `F`; on objects it is `levelTower T F`. -/
abbrev levelTowerFunctor (T : ℕ ⥤ CrystallineThickening S) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj T.op

/-- **Over an object at which the `K^a` have vanishing higher cohomology, the sections carry the
mapping cone of `φ : K^• ⟶ J^•` (extended by zero to `ℤ`) to an acyclic complex**, for `φ` a
quasi-isomorphism and `J^•` termwise injective.  The right derived functors of the sections over
`A` are the cohomology of `Cris(X/S)/A` (`overCohomologyIsoRightDerivedSections`), so the terms
of `K^•` and of `J^•` are acyclic for the sections, and
`Stacks.RightDerivedComp.acyclic_map_mappingCone_extendMap` applies. -/
theorem acyclic_sectionsFunctorOver_mappingCone (A : CrystallineThickening S)
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ J)
    [QuasiIso φ] [∀ a, Injective (J.X a)]
    (hK : ∀ a n, 0 < n →
      IsZero ((overCohomologyFunctor S A n).obj ((restrictToOver S A).obj (K.X a)))) :
    (((sectionsFunctorOver S A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))).Acyclic :=
  Stacks.RightDerivedComp.acyclic_map_mappingCone_extendMap _ φ
    (fun a n hn => (hK a n hn).of_iso (overCohomologyIsoRightDerivedSections S A (K.X a) n).symm)
    (fun _ => Stacks.RightDerivedComp.acyclic_of_injective _ _)

/-- **The sections over an object carry a quasi-isomorphism `φ : K^• ⟶ J^•` to a
quasi-isomorphism** `K^•(A) ⟶ J^•(A)`, when `J^•` is termwise injective and the higher cohomology
`H^n(Cris(X/S)/A, K^a|_A)` vanishes for all `a` and all `n > 0`. -/
theorem quasiIso_sectionsFunctorOver_map (A : CrystallineThickening S)
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ J)
    [QuasiIso φ] [∀ a, Injective (J.X a)]
    (hK : ∀ a n, 0 < n →
      IsZero ((overCohomologyFunctor S A n).obj ((restrictToOver S A).obj (K.X a)))) :
    QuasiIso (((sectionsFunctorOver S A).mapHomologicalComplex _).map φ) :=
  HomologicalComplex.quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone _ φ
    (acyclic_sectionsFunctorOver_mappingCone A φ hK)

/-- **The Čech rows of a quasi-isomorphism are quasi-isomorphisms**: for `φ : K^• ⟶ J^•` a
quasi-isomorphism of complexes of abelian sheaves with `J^•` termwise injective and `K^•`
termwise acyclic at the level objects of `T` with surjective transition maps along its towers,
the map of complexes

`(a ↦ lim_e K^a(T(b)_e)) ⟶ (a ↦ lim_e J^a(T(b)_e))`

is a quasi-isomorphism for every Čech degree `b`.  Over each level object the sections of the
mapping cone are acyclic (`acyclic_sectionsFunctorOver_mappingCone`); its terms
`K^{n+1} ⊕ J^n` give Mittag-Leffler towers, so by [Stacks, Tag 070E]
(`Stacks.TowerAcyclicity.acyclic_mapHomologicalComplex_lim`) the limit over the levels of the
cone, which is the mapping cone of the row map, is acyclic. -/
theorem quasiIso_cosimplicialRowMap_cechCosimplicialComplex_map
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)} (hT : HasAffineMonoLevels T)
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ} (φ : K ⟶ J)
    [QuasiIso φ] [∀ a, Injective (J.X a)]
    (hK : ∀ a, VanishingOnLevels07Q9 T (K.X a))
    (hKs : ∀ a, HasSurjectiveLevelTransitions T (K.X a)) (b : ℕ) :
    QuasiIso (Crystalline.cosimplicialRowMap ((cechCosimplicialComplex T).map φ) b) := by
  let G := levelTowerFunctor (T.obj (op ⦋b⦌))
  let C := CochainComplex.mappingCone
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  have hP : ∀ {X Y : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}, (X ≅ Y) →
      (G.obj X ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler →
        (G.obj Y ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler :=
    fun e h => isMittagLeffler_of_epi (G.map e.hom) h
  have hP0 : ∀ X : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}, IsZero X →
      (G.obj X ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler :=
    fun X h => Stacks.TowerAcyclicity.isMittagLeffler_of_isZero _ (G.map_isZero h)
  have hML : ∀ n, (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X n ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler :=
    CochainComplex.mappingCone.prop_X
      (fun X => (G.obj X ⋙ CategoryTheory.forget _).IsMittagLeffler) hP
      (fun X Y hX hY => isMittagLeffler_of_shortExact _
        ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map G).shortExact hX hY) _
      (HomologicalComplex.prop_extend_X _ hP hP0 K (fun a =>
        Stacks.TowerAcyclicity.isMittagLeffler_of_surjective_succ _ (hKs a b)) _)
      (HomologicalComplex.prop_extend_X _ hP hP0 J (fun a =>
        Stacks.TowerAcyclicity.isMittagLeffler_of_surjective_succ _
          (hasSurjectiveLevelTransitions_of_injective hT (J.X a) b)) _)
  have hz : ∀ e : ℕᵒᵖ, ((((evaluation ℕᵒᵖ AddCommGrpCat.{u + 1}).obj e).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).Acyclic :=
    fun e => acyclic_sectionsFunctorOver_mappingCone ((T.obj (op ⦋b⦌)).obj e.unop) φ
      (fun a n hn => hK a b e.unop n hn)
  exact HomologicalComplex.quasiIso_mapHomologicalComplex_map_of_acyclic_mappingCone (G ⋙ lim) φ
    (Stacks.TowerAcyclicity.acyclic_mapHomologicalComplex_lim _ hML hz)

end Crystalline.GlobalCrystallineSituation.SmallSite
