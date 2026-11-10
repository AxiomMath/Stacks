module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence

/-!
# Cohomology of derived global sections on an affine scheme

Let `R` be a commutative ring and let `E` be an object of `D_QCoh(𝒪_{Spec R})`. The cohomology of
the derived global sections of `E` is the global sections of the cohomology of `E`:
`Hⁿ(RΓ(Spec R, E)) ≅ Γ(Spec R, Hⁿ(E))`, naturally in `E`. In degree zero this is the
degree-zero statement of [Stacks, Tag 06Z0]; the statement in every degree costs nothing more and
is what is proved. The *normalization* of that isomorphism on global cycles — that the composite

```
Γ(Spec R, Z⁰(K)) ⟶ H⁰(Γ(Spec R, K)) ⟶ H⁰(RΓ(Spec R, Q K)) ⟶ Γ(Spec R, H⁰(Q K)) ⟶
  Γ(Spec R, H⁰(K))
```

is `Γ(Spec R, -)` applied to `K.homologyπ 0` — is proved here too, and it is the clause of the tag
that pins the isomorphism down: the first map is an epimorphism, so no other isomorphism satisfies
it.

## Main definitions

* `AlgebraicGeometry.tildeCompGlobalSectionsOverIso` — `Γ(Spec R, N^~) ≅ N`, as an isomorphism of
  functors `ModuleCat R ⥤ ModuleCat R`.
* `AlgebraicGeometry.tildeHomologyIso` — `Hⁿ(M̃^•) ≅ (Hⁿ M^•)^~`, the exactness of `(-)^~` read on
  the cohomology of a complex.
* `AlgebraicGeometry.tildeHomologyGlobalSectionsIso` — `Γ(Spec R, Hⁿ(M̃^•)) ≅ Hⁿ(M^•)`, naturally
  in the complex `M^•`; this is the complex-level computation the derived statement is lifted from.
* `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso` —
  `Γ(Spec R, Hⁿ(M^~)) ≅ Hⁿ(M)` for an object `M` of `D(R)`.
* `AlgebraicGeometry.globalSectionsHomologyComparison` — the composite whose normalization is the
  content of the degree-zero clause of [Stacks, Tag 06Z0]: a map
  `Hⁿ(Γ(Spec R, K)) ⟶ Γ(Spec R, Hⁿ(K))` for a complex `K` with quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso` —
  `Hⁿ(RΓ(Spec R, -)) ≅ Γ(Spec R, Hⁿ(-))` on `D_QCoh(𝒪_{Spec R})`.
* `AlgebraicGeometry.derivedGlobalSectionsHomologyZeroIso` — the same in degree zero, which is the
  degree-zero statement of [Stacks, Tag 06Z0].
* `AlgebraicGeometry.globalSectionsHomologyComparison_eq` — **the normalization**: the comparison
  above is the canonical comparison of the left exact functor `Γ(Spec R, -)` with cohomology,
  `Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`.
* `AlgebraicGeometry.globalSectionsCyclesToHomology_comp_derivedGlobalSectionsHomologyZeroIso` —
  **Stacks 06Z0**, the canonical degree-zero comparison: the normalization read on global cycles.
* `AlgebraicGeometry.homologyDerivedGlobalSectionsQuasicoherentObjIso` — the objectwise form.

## Implementation notes

**How the normalization is proved.** It is *not* a consequence of the isomorphism:
`AlgebraicGeometry.globalSectionsCyclesToHomology` is an epimorphism — it is the canonical
isomorphism `Γ(Z⁰(K)) ≅ Z⁰(Γ(K))`, left exactness of `Γ(Spec R, -)` giving that, followed by the
epimorphism `HomologicalComplex.homologyπ` — so the normalization *determines* the isomorphism,
and establishing it means identifying the one built from the adjunction with the canonical
comparison of a left exact functor with cohomology. That canonical comparison is
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`, and the identification is
`AlgebraicGeometry.globalSectionsHomologyComparison_eq`, proved in two steps.

*The computation at a complex of the form `M̃^•`.* There the isomorphism is pinned by the
normalization of the adjunction, `(AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction R).2`:
its unit is the degreewise sheafification–sections unit followed by the comparison
`Q(Γ(X, -)) ⟶ RΓ(X, Q(-))`, so composing the degree-`n` comparison with `Hⁿ` of the derived unit
cancels that comparison outright and leaves the complex-level isomorphism
`AlgebraicGeometry.tildeHomologyGlobalSectionsIso`. Nothing here needs the comparison
`Q(Γ(X, M̃^•)) ⟶ RΓ(X, Q(M̃^•))` to be invertible — the derived unit is cancelled on the *left*,
where it is an isomorphism because the degreewise unit is.

*The reduction of an arbitrary complex to that case.* For a complex `K` with quasi-coherent
cohomology the degreewise sheafification–sections counit `(Γ(X, K)^•)^~ ⟶ K`
(`AlgebraicGeometry.tildeComplexCounit`) is a morphism from a complex of the first kind, and
`Γ(X, -)` carries it to an isomorphism of complexes — degreewise `Γ(X, ε)` is split by the unit,
and the unit of `AlgebraicGeometry.tilde.adjunction` is invertible, so `Γ(X, ε)` is invertible
(`AlgebraicGeometry.isIso_map_counit`). Both the comparison and the canonical comparison are
natural in the complex, so the identity transfers. The counit is *not* a quasi-isomorphism in
general and is not claimed to be: only `Γ(X, -)` of it is used.

**Degree `n` rather than degree `0`.** Nothing in the argument sees the degree, so everything is
stated in every degree and the degree-zero clause of the tag is the specialization
`AlgebraicGeometry.derivedGlobalSectionsHomologyZeroIso`.

**Spellings.** `AlgebraicGeometry.moduleSpecΓFunctor` and
`AlgebraicGeometry.globalSectionsOver (𝟙 (Spec R))` are equal, but the defeq is expensive to check
in nested positions, so `AlgebraicGeometry.tildeGlobalSectionsUnit` and
`AlgebraicGeometry.tildeGlobalSectionsComplexUnitApp` name the unit of
`AlgebraicGeometry.tilde.adjunction` at the spelling the cycles and homology comparisons use, and
`AlgebraicGeometry.tildeComplexCounit` is stated at the `moduleSpecΓFunctor` spelling, where the
counit needs no transport at all.

**The complex-level comparison.** `Stacks.Cohomology.RightDerivedCoEdge.mapCycles` and
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology` are the canonical comparisons
`F(Zⁿ K) ⟶ Zⁿ(F K)` and `Hⁿ(F K) ⟶ F(Hⁿ K)` for a left exact `F`. They were stated there only for
`ℕ`-indexed cochain complexes and are generalized to an arbitrary complex shape for this file;
`Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology`, that the second is invertible
when `F` is exact, is added there as well. No second copy of either is introduced here.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry
open Stacks.Cohomology.RightDerivedCoEdge

universe w₁ w₂ u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-! ### The sheafification–sections unit and counit -/

/-- **The sheafification–sections unit** of `AlgebraicGeometry.tilde.adjunction`, with global
sections spelled through the identity of `Spec R`: `M ⟶ Γ(Spec R, M̃)`.

`AlgebraicGeometry.moduleSpecΓFunctor` and `AlgebraicGeometry.globalSectionsOver (𝟙 (Spec R))` are
equal, so this *is* the unit; naming it fixes the spelling of its codomain, which is what lets it
be composed with the cycles and homology comparisons for `Γ(Spec R, -)`. -/
def tildeGlobalSectionsUnit (P : ModuleCat.{u} R) :
    P ⟶ (globalSectionsOver (𝟙 (Spec R))).obj ((tilde.functor R).obj P) :=
  (tilde.adjunction (R := R)).unit.app P

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- The sheafification–sections unit is natural. -/
@[reassoc]
lemma tildeGlobalSectionsUnit_naturality {P P' : ModuleCat.{u} R} (f : P ⟶ P') :
    tildeGlobalSectionsUnit R P ≫
        (globalSectionsOver (𝟙 (Spec R))).map ((tilde.functor R).map f) =
      f ≫ tildeGlobalSectionsUnit R P' :=
  ((tilde.adjunction (R := R)).unit.naturality f).symm

/-- **Global sections of the sheaf associated to a module is the module**, as an isomorphism of
functors `ModuleCat R ⥤ ModuleCat R`. This is the unit of
`AlgebraicGeometry.tilde.adjunction`, which is invertible. -/
def tildeCompGlobalSectionsOverIso :
    tilde.functor R ⋙ globalSectionsOver (𝟙 (Spec R)) ≅ 𝟭 (ModuleCat.{u} R) :=
  (asIso (tilde.adjunction (R := R)).unit).symm

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- The inverse of `AlgebraicGeometry.tildeCompGlobalSectionsOverIso` at a module `P` is the
sheafification–sections unit `P ⟶ Γ(Spec R, P̃)`. -/
@[simp]
lemma tildeCompGlobalSectionsOverIso_inv_app (P : ModuleCat.{u} R) :
    (tildeCompGlobalSectionsOverIso R).inv.app P = tildeGlobalSectionsUnit R P := rfl

/-- **Global sections of `Γ(Spec R, -)` applied to the sheafification–sections counit is
invertible.** For a sheaf of `𝒪_{Spec R}`-modules `𝓖` the map
`Γ(Spec R, Γ(Spec R, 𝓖)^~) ⟶ Γ(Spec R, 𝓖)` is an isomorphism: the unit splits it, and the unit is
invertible. The counit itself is *not* invertible unless `𝓖` is quasi-coherent. -/
instance isIso_map_counit (G : (Spec R).Modules) :
    IsIso ((globalSectionsOver (𝟙 (Spec R))).map ((tilde.adjunction (R := R)).counit.app G)) := by
  have h2 := (tilde.adjunction (R := R)).right_triangle_components G
  have h3 : IsIso ((moduleSpecΓFunctor (R := R)).map
      ((tilde.adjunction (R := R)).counit.app G)) := by
    have h4 : IsIso ((tilde.adjunction (R := R)).unit.app
        ((moduleSpecΓFunctor (R := R)).obj G) ≫
        (moduleSpecΓFunctor (R := R)).map ((tilde.adjunction (R := R)).counit.app G)) := by
      rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_left
      ((tilde.adjunction (R := R)).unit.app ((moduleSpecΓFunctor (R := R)).obj G)) _
  exact h3

/-- **The degreewise sheafification–sections counit** of a complex of `𝒪_{Spec R}`-modules:
`(Γ(Spec R, K)^•)^~ ⟶ K`. -/
def tildeComplexCounit (K : CochainComplex (Spec R).Modules ℤ) :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      K where
  f i := (tilde.adjunction (R := R)).counit.app (K.X i)
  comm' i j _ := ((tilde.adjunction (R := R)).counit.naturality (K.d i j)).symm

/-- **Global sections carries the degreewise counit to an isomorphism of complexes**, by
`AlgebraicGeometry.isIso_map_counit` in each degree. -/
instance isIso_map_tildeComplexCounit (K : CochainComplex (Spec R).Modules ℤ) :
    IsIso (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (tildeComplexCounit R K)) := by
  have h : ∀ i : ℤ, IsIso ((((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (tildeComplexCounit R K)).f i) := fun i =>
    inferInstanceAs (IsIso ((globalSectionsOver (𝟙 (Spec R))).map
      ((tilde.adjunction (R := R)).counit.app (K.X i))))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The degreewise sheafification–sections unit of a complex of `R`-modules, with global sections
spelled through the identity of `Spec R`; see `AlgebraicGeometry.tildeGlobalSectionsUnit` for why
the spelling is named. -/
def tildeGlobalSectionsComplexUnitApp (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    N ⟶ ((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :=
  (tildeGlobalSectionsComplexUnit R).app N

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- In degree `i`, the degreewise unit of a complex `N` is the unit at `N.X i`. -/
lemma tildeGlobalSectionsComplexUnitApp_f (N : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (tildeGlobalSectionsComplexUnitApp R N).f i = tildeGlobalSectionsUnit R (N.X i) := by
  simp only [tildeGlobalSectionsComplexUnitApp, tildeGlobalSectionsComplexUnit, NatTrans.comp_app,
    HomologicalComplex.comp_f, moduleSpecΓIsoGlobalSectionsOver,
    Functor.mapHomologicalComplexIdIso, Functor.mapHomologicalComplexCompIso,
    NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplex_obj_X, Functor.id_obj,
    NatIso.ofComponents_inv_app, HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv,
    Functor.comp_obj, Iso.refl_hom, NatIso.mapHomologicalComplex_inv_app_f, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  exact Category.comp_id _

/-- The degreewise sheafification–sections unit of a complex of `R`-modules is an isomorphism
of complexes. -/
instance isIso_tildeGlobalSectionsComplexUnitApp (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (tildeGlobalSectionsComplexUnitApp R N) :=
  inferInstanceAs (IsIso ((tildeGlobalSectionsComplexUnit R).app N))

omit [HasDerivedCategory.{w₁} (Spec R).Modules] in
/-- The image in `D(R)` of `AlgebraicGeometry.tildeGlobalSectionsComplexUnitApp` is that of
`AlgebraicGeometry.tildeGlobalSectionsComplexUnit` at `N`. -/
lemma Q_map_tildeGlobalSectionsComplexUnitApp (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.map (tildeGlobalSectionsComplexUnitApp R N) =
      DerivedCategory.Q.map ((tildeGlobalSectionsComplexUnit R).app N) := rfl

/-! ### The complex-level computation -/

/-- **`(-)^~` commutes with cohomology**: `Hⁿ(M̃^•) ≅ (Hⁿ M^•)^~`. This is
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology` for the exact functor `(-)^~`. -/
def tildeHomologyIso (N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).homology n ≅
      (tilde.functor R).obj (N.homology n) :=
  asIso (homologyToMapHomology (tilde.functor R) N n)

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- The cycles comparisons of `(-)^~` and of `Γ(Spec R, -)` compose to the degreewise unit. -/
lemma tildeGlobalSectionsUnit_cycles (N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tildeGlobalSectionsUnit R (N.cycles n) ≫
        (globalSectionsOver (𝟙 (Spec R))).map (mapCycles (tilde.functor R) N n) ≫
          mapCycles (globalSectionsOver (𝟙 (Spec R)))
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n =
      HomologicalComplex.cyclesMap (tildeGlobalSectionsComplexUnitApp R N) n := by
  rw [← cancel_mono ((((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((tilde.functor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)).iCycles n), Category.assoc, Category.assoc,
    mapCycles_i, ← Functor.map_comp, mapCycles_i, HomologicalComplex.cyclesMap_i,
    tildeGlobalSectionsComplexUnitApp_f]
  exact tildeGlobalSectionsUnit_naturality R (N.iCycles n)

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- The unit at the degree-`n` cycles of `N` is the map induced on cycles by the degreewise unit,
followed by the inverses of the cycles comparisons of `Γ(Spec R, -)` and of `(-)^~`. -/
lemma tildeGlobalSectionsUnit_cycles_eq (N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tildeGlobalSectionsUnit R (N.cycles n) =
      HomologicalComplex.cyclesMap (tildeGlobalSectionsComplexUnitApp R N) n ≫
        (mapCyclesIso (globalSectionsOver (𝟙 (Spec R)))
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n).inv ≫
        (globalSectionsOver (𝟙 (Spec R))).map (mapCyclesIso (tilde.functor R) N n).inv := by
  rw [← tildeGlobalSectionsUnit_cycles R N n]
  simp only [mapCyclesIso, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- **The homology comparisons of `(-)^~` and of `Γ(Spec R, -)` compose to the unit.** On the
degree-`n` cohomology of a complex `M^•` of `R`-modules, the degreewise unit followed by the
canonical comparison `Hⁿ(Γ(Spec R, M̃^•)) ⟶ Γ(Spec R, Hⁿ(M̃^•))` and by `Γ(Spec R, -)` of
`AlgebraicGeometry.tildeHomologyIso` is the unit at `Hⁿ(M^•)`.

Both sides are maps out of `Hⁿ(M^•)`, so it is enough to check them on cycles, where the
statement is the corresponding one for the cycles comparisons,
`AlgebraicGeometry.tildeGlobalSectionsUnit_cycles`. -/
lemma tildeGlobalSectionsUnit_homology_eq (N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    HomologicalComplex.homologyMap (tildeGlobalSectionsComplexUnitApp R N) n ≫
        homologyToMapHomology (globalSectionsOver (𝟙 (Spec R)))
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n ≫
        (globalSectionsOver (𝟙 (Spec R))).map (tildeHomologyIso R N n).hom =
      tildeGlobalSectionsUnit R (N.homology n) := by
  refine (cancel_epi (N.homologyπ n)).mp ?_
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_comp_homologyToMapHomology_assoc, ← Functor.map_comp,
    show (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).homologyπ n ≫
        (tildeHomologyIso R N n).hom =
      (mapCyclesIso (tilde.functor R) N n).inv ≫ (tilde.functor R).map (N.homologyπ n) from
      homologyπ_comp_homologyToMapHomology (tilde.functor R) N n,
    Functor.map_comp, ← tildeGlobalSectionsUnit_naturality R (N.homologyπ n),
    tildeGlobalSectionsUnit_cycles_eq R N n]
  simp only [Category.assoc]

/-- **`Γ(Spec R, Hⁿ(M̃^•)) ≅ Hⁿ(M^•)`**, naturally in the complex `M^•` of `R`-modules: the
cohomology sheaf is `(Hⁿ M^•)^~` because `(-)^~` is exact, and global sections of that is
`Hⁿ(M^•)`. -/
def tildeHomologyGlobalSectionsIso (n : ℤ) :
    (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.up ℤ) n ⋙
          globalSectionsOver (𝟙 (Spec R)) ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n :=
  NatIso.ofComponents
    (fun N => (globalSectionsOver (𝟙 (Spec R))).mapIso (tildeHomologyIso R N n) ≪≫
      (tildeCompGlobalSectionsOverIso R).app (N.homology n))
    (fun {N₁ N₂} φ => by
      have h1 := homologyToMapHomology_naturality (tilde.functor R) φ n
      have h2 := (tildeCompGlobalSectionsOverIso R).hom.naturality
        (HomologicalComplex.homologyMap φ n)
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h2
      change (globalSectionsOver (𝟙 (Spec R))).map
            (HomologicalComplex.homologyMap (((tilde.functor R).mapHomologicalComplex
              (ComplexShape.up ℤ)).map φ) n) ≫
            ((globalSectionsOver (𝟙 (Spec R))).map
                (homologyToMapHomology (tilde.functor R) N₂ n) ≫
              (tildeCompGlobalSectionsOverIso R).hom.app (N₂.homology n)) =
          ((globalSectionsOver (𝟙 (Spec R))).map
                (homologyToMapHomology (tilde.functor R) N₁ n) ≫
              (tildeCompGlobalSectionsOverIso R).hom.app (N₁.homology n)) ≫
            HomologicalComplex.homologyMap φ n
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h1,
        CategoryTheory.Functor.map_comp, Category.assoc, h2, ← Category.assoc])

omit [HasDerivedCategory.{w₁} (Spec R).Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} R)] in
/-- The inverse of `AlgebraicGeometry.tildeHomologyGlobalSectionsIso` at `N` is the unit at
`Hⁿ(N)` followed by `Γ(Spec R, -)` of the inverse of `AlgebraicGeometry.tildeHomologyIso`. -/
lemma tildeHomologyGlobalSectionsIso_inv_app (n : ℤ) (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tildeHomologyGlobalSectionsIso R n).inv.app N =
      tildeGlobalSectionsUnit R (N.homology n) ≫
        (globalSectionsOver (𝟙 (Spec R))).map (tildeHomologyIso R N n).inv := by
  rfl

/-! ### The computation at an object of `D(R)` -/

/-- `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso` composed with the localization
functor, which is the shape `CategoryTheory.Localization.liftNatIso` consumes. -/
def derivedTildeCompHomologyGlobalSectionsIsoAux (n : ℤ) :
    DerivedCategory.Q ⋙ (derivedTilde R ⋙
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
            (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
          DerivedCategory.homologyFunctor (Spec R).Modules n ⋙
            globalSectionsOver (𝟙 (Spec R)))) ≅
      DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n :=
  Functor.isoWhiskerLeft DerivedCategory.Q (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedTildeFactors R)
      (DerivedCategory.homologyFunctor (Spec R).Modules n ⋙ globalSectionsOver (𝟙 (Spec R))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors (Spec R).Modules n)
          (globalSectionsOver (𝟙 (Spec R)))) ≪≫
    tildeHomologyGlobalSectionsIso R n ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).symm

/-- The component of `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIsoAux` at a
complex `N`, as a composite of the factorization isomorphisms and
`AlgebraicGeometry.tildeHomologyGlobalSectionsIso`. -/
lemma derivedTildeCompHomologyGlobalSectionsIsoAux_hom_app (n : ℤ)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTildeCompHomologyGlobalSectionsIsoAux R n).hom.app N =
      (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
            ((derivedTildeFactors R).hom.app N)) ≫
        (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
        (tildeHomologyGlobalSectionsIso R n).hom.app N ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.app N := by
  simp [derivedTildeCompHomologyGlobalSectionsIsoAux]

/-- **The cohomology of derived global sections at an object of the form `M^~`.** For an object
`M` of `D(R)` the global sections of the degree-`n` cohomology sheaf of `M^~` is `Hⁿ(M)`.

Both sides invert quasi-isomorphisms, so this is
`AlgebraicGeometry.tildeHomologyGlobalSectionsIso` descended along the localization
`CategoryTheory.DerivedCategory.Q`. No cohomology vanishing is involved: derived global sections
does not appear, only the cohomology sheaves of `M^~`. -/
def derivedTildeCompHomologyGlobalSectionsIso (n : ℤ) :
    derivedTilde R ⋙ ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
      DerivedCategory.homologyFunctor (Spec R).Modules n ⋙
        globalSectionsOver (𝟙 (Spec R))) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) n :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (derivedTilde R ⋙
      ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
        DerivedCategory.homologyFunctor (Spec R).Modules n ⋙
          globalSectionsOver (𝟙 (Spec R)))))
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n) _ _
    (h₁ := Localization.Lifting.compLeft _ _ _) (h₂ := Localization.Lifting.compLeft _ _ _)
    (derivedTildeCompHomologyGlobalSectionsIsoAux R n)

/-- At the image of a complex `N` in `D(R)`,
`AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso` is
`AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIsoAux` at `N`. -/
lemma derivedTildeCompHomologyGlobalSectionsIso_hom_app_Q (n : ℤ)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedTildeCompHomologyGlobalSectionsIso R n).hom.app (DerivedCategory.Q.obj N) =
      (derivedTildeCompHomologyGlobalSectionsIsoAux R n).hom.app N := by
  simp [derivedTildeCompHomologyGlobalSectionsIso]

/-- **The cohomology of derived global sections on an affine scheme.** For an object `E` of
`D_QCoh(𝒪_{Spec R})` the degree-`n` cohomology of `RΓ(Spec R, E)` is the module of global sections
of the degree-`n` cohomology sheaf of `E`, naturally in `E`:
`Hⁿ(RΓ(Spec R, E)) ≅ Γ(Spec R, Hⁿ(E))`.

The counit of `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is invertible, derived
sheafification being an equivalence, so `E` may be replaced by `RΓ(Spec R, E)^~`; there the
assertion is `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso`. -/
def derivedGlobalSectionsQuasicoherentCompHomologyIso (n : ℤ) :
    derivedGlobalSectionsQuasicoherent R ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ≅
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
        DerivedCategory.homologyFunctor (Spec R).Modules n ⋙
          globalSectionsOver (𝟙 (Spec R)) :=
  Functor.isoWhiskerLeft (derivedGlobalSectionsQuasicoherent R)
      (derivedTildeCompHomologyGlobalSectionsIso R n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (derivedTildeQuasicoherentAdjunction R).counit) _ ≪≫
    Functor.leftUnitor _

/-- The component of `AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso` at
`E` is the inverse of `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso` at
`RΓ(Spec R, E)` followed by `Γ(Spec R, Hⁿ(-))` of the counit of
`AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` at `E`. -/
lemma derivedGlobalSectionsQuasicoherentCompHomologyIso_hom_app (n : ℤ)
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.app E =
      (derivedTildeCompHomologyGlobalSectionsIso R n).inv.app
          ((derivedGlobalSectionsQuasicoherent R).obj E) ≫
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
            DerivedCategory.homologyFunctor (Spec R).Modules n ⋙
              globalSectionsOver (𝟙 (Spec R))).map
          ((derivedTildeQuasicoherentAdjunction R).counit.app E) := by
  simp [derivedGlobalSectionsQuasicoherentCompHomologyIso]

/-- The unit of `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` is the unit of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction`: the restriction is along fully faithful
functors whose comparison isomorphisms are unitors. -/
lemma derivedTildeQuasicoherentAdjunction_unit_app (M : DerivedCategory (ModuleCat.{u} R)) :
    (derivedTildeQuasicoherentAdjunction R).unit.app M =
      (derivedTildeGlobalSectionsAdjunction R).val.unit.app M := by
  have key : (Adjunction.restrictFullyFaithful (derivedTildeGlobalSectionsAdjunction R).val
        (Functor.FullyFaithful.id _)
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι)
        (Functor.leftUnitor _) (Functor.rightUnitor _).symm).unit.app M =
      (derivedTildeGlobalSectionsAdjunction R).val.unit.app M := by
    have h := Adjunction.map_restrictFullyFaithful_unit_app
      (derivedTildeGlobalSectionsAdjunction R).val (Functor.FullyFaithful.id _)
      ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι)
      (Functor.leftUnitor _) (Functor.rightUnitor _).symm M
    simp only [Functor.id_map, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Iso.symm_hom] at h
    simpa using h
  exact key

/-- **The degree-`n` comparison at an object of the form `M^~`, read through the derived unit.**
Composing with `Hⁿ` of the unit of `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction`
recovers `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso`; this is the triangle
identity of the adjunction and needs neither the unit nor the counit to be invertible. -/
lemma homologyFunctor_map_unit_comp_derivedGlobalSectionsQuasicoherentCompHomologyIso (n : ℤ)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((derivedTildeQuasicoherentAdjunction R).unit.app M) ≫
        (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.app
          ((derivedTilde R).obj M) =
      (derivedTildeCompHomologyGlobalSectionsIso R n).inv.app M := by
  have hnat := (derivedTildeCompHomologyGlobalSectionsIso R n).inv.naturality
    ((derivedTildeQuasicoherentAdjunction R).unit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [derivedGlobalSectionsQuasicoherentCompHomologyIso_hom_app, ← Category.assoc, hnat,
    Category.assoc]
  dsimp only [Functor.comp_map, Functor.id_obj]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, Adjunction.left_triangle_components]
  simp

/-- **Stacks 06Z0, degree-zero cohomology.** On an affine scheme the degree-zero cohomology of
derived global sections is the global sections of the degree-zero cohomology sheaf:
`H⁰(RΓ(Spec R, E)) ≅ Γ(Spec R, H⁰(E))` for `E` in `D_QCoh(𝒪_{Spec R})`, naturally in `E`.

This is `AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso` in degree zero. Its
normalization on global cycles, which pins it down uniquely, is
`AlgebraicGeometry.globalSectionsCyclesToHomology_comp_derivedGlobalSectionsHomologyZeroIso`. -/
@[stacks 06Z0 "degree-zero cohomology"]
def derivedGlobalSectionsHomologyZeroIso :
    derivedGlobalSectionsQuasicoherent R ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 ≅
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
        DerivedCategory.homologyFunctor (Spec R).Modules 0 ⋙
          globalSectionsOver (𝟙 (Spec R)) :=
  derivedGlobalSectionsQuasicoherentCompHomologyIso R 0

/-- The objectwise form of
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso`:
`Hⁿ(RΓ(Spec R, E)) ≅ Γ(Spec R, Hⁿ(E))` for a single object `E` of `D_QCoh(𝒪_{Spec R})`. -/
def homologyDerivedGlobalSectionsQuasicoherentObjIso (n : ℤ)
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((derivedGlobalSectionsQuasicoherent R).obj E) ≅
      (globalSectionsOver (𝟙 (Spec R))).obj
        ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E.obj) :=
  (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).app E

/-! ### The normalization -/

/-- Sheafification of a complex of `R`-modules has quasi-coherent cohomology. -/
lemma derivedQuasicoherent_Q_obj_mapHomologicalComplex_tilde
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :=
  fun n => (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso ((derivedTildeFactors R).app N))
    (((derivedTilde R).obj (DerivedCategory.Q.obj N)).2 n)

/-- **The comparison whose normalization is the content of the degree-zero clause of Stacks
06Z0.** For a complex `K` of `𝒪_{Spec R}`-modules with quasi-coherent cohomology, the composite
`Hⁿ(Γ(Spec R, K)) ≅ Hⁿ(Q(Γ(Spec R, K))) ⟶ Hⁿ(RΓ(Spec R, Q K)) ≅ Γ(Spec R, Hⁿ(Q K)) ≅
Γ(Spec R, Hⁿ(K))` built from `AlgebraicGeometry.globalSectionsComplexComparison` and the
degree-`n` isomorphism. -/
def globalSectionsHomologyComparison (n : ℤ) (K : CochainComplex (Spec R).Modules ℤ)
    (hK : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj K)) :
    (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology n ⟶
      (globalSectionsOver (𝟙 (Spec R))).obj (K.homology n) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.app
      (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
      (globalSectionsComplexComparison (𝟙 (Spec R)) K) ≫
    (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.app
      ⟨DerivedCategory.Q.obj K, hK⟩ ≫
    (globalSectionsOver (𝟙 (Spec R))).map
      ((DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app K)

/-- `AlgebraicGeometry.globalSectionsHomologyComparison` is natural in the complex. -/
lemma globalSectionsHomologyComparison_naturality (n : ℤ)
    {K L : CochainComplex (Spec R).Modules ℤ}
    (hK : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj K))
    (hL : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj L))
    (φ : K ⟶ L) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
          (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) ≫ globalSectionsHomologyComparison R n L hL =
      globalSectionsHomologyComparison R n K hK ≫
        (globalSectionsOver (𝟙 (Spec R))).map (HomologicalComplex.homologyMap φ n) := by
  let ψ : (⟨DerivedCategory.Q.obj K, hK⟩ :
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) ⟶
      ⟨DerivedCategory.Q.obj L, hL⟩ := ObjectProperty.homMk (DerivedCategory.Q.map φ)
  have a3 := (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.naturality ψ
  dsimp only [derivedGlobalSectionsQuasicoherent, Functor.comp_obj, Functor.comp_map] at a3
  rw [show (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.map ψ =
      DerivedCategory.Q.map φ from rfl] at a3
  have a1 : (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.app
        (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.app
          (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (DerivedCategory.Q.map (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.naturality _
  have a2 : DerivedCategory.Q.map (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) ≫ globalSectionsComplexComparison (𝟙 (Spec R)) L =
      globalSectionsComplexComparison (𝟙 (Spec R)) K ≫
        (derivedGlobalSectionsOver (𝟙 (Spec R))).map (DerivedCategory.Q.map φ) := by
    have h := (globalSectionsComplexComparisonNatTrans (𝟙 (Spec R))).naturality φ
    rw [globalSectionsComplexComparisonNatTrans_app,
      globalSectionsComplexComparisonNatTrans_app] at h
    exact h
  have a4 : (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
            (DerivedCategory.Q.map φ)) ≫
        (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app L) =
      (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app K) ≫
        (globalSectionsOver (𝟙 (Spec R))).map (HomologicalComplex.homologyMap φ n) := by
    rw [← CategoryTheory.Functor.map_comp,
      show (DerivedCategory.homologyFunctor (Spec R).Modules n).map (DerivedCategory.Q.map φ) ≫
          (DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app L =
        (DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app K ≫
          HomologicalComplex.homologyMap φ n from
        (DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.naturality φ]
    exact (globalSectionsOver (𝟙 (Spec R))).map_comp _ _
  simp only [globalSectionsHomologyComparison]
  erw [Category.assoc, Category.assoc, Category.assoc, reassoc_of% a1, ← Functor.map_comp_assoc,
    a2, Functor.map_comp_assoc, reassoc_of% a3, a4]
  rfl

/-- **The normalization at a complex of the form `M̃^•`.** There the comparison is the canonical
comparison of the left exact functor `Γ(Spec R, -)` with cohomology.

The derived unit is invertible at `Q(M^•)` because the degreewise unit is, so it may be cancelled
on the left; the normalization of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` then replaces the derived unit by the
degreewise one followed by `AlgebraicGeometry.globalSectionsComplexComparison`, which cancels the
comparison appearing in the statement, and what is left is
`AlgebraicGeometry.tildeGlobalSectionsUnit_homology_eq`. -/
lemma globalSectionsHomologyComparison_tilde (n : ℤ) (N : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) :
    globalSectionsHomologyComparison R n
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) h =
      homologyToMapHomology (globalSectionsOver (𝟙 (Spec R)))
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n := by
  rw [← cancel_epi (HomologicalComplex.homologyMap (tildeGlobalSectionsComplexUnitApp R N) n)]
  let e : (derivedTilde R).obj (DerivedCategory.Q.obj N) ⟶
      (⟨DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N), h⟩ :
        (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :=
    ObjectProperty.homMk ((derivedTildeFactors R).hom.app N)
  have hιe : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.map e =
      (derivedTildeFactors R).hom.app N := rfl
  have hRHS : HomologicalComplex.homologyMap (tildeGlobalSectionsComplexUnitApp R N) n ≫
        homologyToMapHomology (globalSectionsOver (𝟙 (Spec R)))
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) n =
      tildeGlobalSectionsUnit R (N.homology n) ≫
        (globalSectionsOver (𝟙 (Spec R))).map (tildeHomologyIso R N n).inv := by
    rw [← tildeGlobalSectionsUnit_homology_eq R N n]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hθ := (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.naturality e
  dsimp only [derivedGlobalSectionsQuasicoherent, Functor.comp_obj, Functor.comp_map] at hθ
  rw [hιe] at hθ
  have hun := homologyFunctor_map_unit_comp_derivedGlobalSectionsQuasicoherentCompHomologyIso
    R n (DerivedCategory.Q.obj N)
  rw [derivedTildeQuasicoherentAdjunction_unit_app] at hun
  have hnorm := (derivedTildeGlobalSectionsAdjunction R).2 N
  have hAD : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((derivedTildeGlobalSectionsAdjunction R).val.unit.app (DerivedCategory.Q.obj N)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((derivedGlobalSectionsOver (𝟙 (Spec R))).map
            ((derivedTildeFactors R).hom.app N)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (DerivedCategory.Q.map (tildeGlobalSectionsComplexUnitApp R N)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (globalSectionsComplexComparison (𝟙 (Spec R))
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) := by
    rw [← CategoryTheory.Functor.map_comp, hnorm, CategoryTheory.Functor.map_comp,
      ← Q_map_tildeGlobalSectionsComplexUnitApp]
  have h2 : (derivedTildeCompHomologyGlobalSectionsIso R n).inv.app
          (DerivedCategory.Q.obj N) ≫
        (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
            ((derivedTildeFactors R).hom.app N)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (DerivedCategory.Q.map (tildeGlobalSectionsComplexUnitApp R N)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (globalSectionsComplexComparison (𝟙 (Spec R))
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
        (derivedGlobalSectionsQuasicoherentCompHomologyIso R n).hom.app
          ⟨DerivedCategory.Q.obj
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N), h⟩ := by
    rw [← hun, Category.assoc]
    refine (congrArg (_ ≫ ·) hθ.symm).trans ?_
    exact (reassoc_of% hAD) _
  have step2 : (derivedTildeCompHomologyGlobalSectionsIso R n).inv.app
        (DerivedCategory.Q.obj N) ≫
        ((globalSectionsOver (𝟙 (Spec R))).map
            ((DerivedCategory.homologyFunctor (Spec R).Modules n).map
              ((derivedTildeFactors R).hom.app N)) ≫
          (globalSectionsOver (𝟙 (Spec R))).map
            ((DerivedCategory.homologyFunctorFactors (Spec R).Modules n).hom.app
              (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app N ≫
        (tildeHomologyGlobalSectionsIso R n).inv.app N := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom,
      derivedTildeCompHomologyGlobalSectionsIso_hom_app_Q,
      derivedTildeCompHomologyGlobalSectionsIsoAux_hom_app]
    simp
  have h1 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.naturality
    (tildeGlobalSectionsComplexUnitApp R N)
  dsimp only [Functor.comp_obj, Functor.comp_map, HomologicalComplex.homologyFunctor_obj,
    HomologicalComplex.homologyFunctor_map] at h1
  have key : HomologicalComplex.homologyMap (tildeGlobalSectionsComplexUnitApp R N) n ≫
      globalSectionsHomologyComparison R n
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) h =
      (tildeHomologyGlobalSectionsIso R n).inv.app N := by
    simp only [globalSectionsHomologyComparison]
    erw [Category.assoc, Category.assoc, Category.assoc, reassoc_of% h1, ← reassoc_of% h2, step2]
    exact Iso.inv_hom_id_app_assoc _ _ _
  rw [hRHS, key, tildeHomologyGlobalSectionsIso_inv_app]

/-- **The normalization of the degree-`n` isomorphism.** For every complex `K` of
`𝒪_{Spec R}`-modules with quasi-coherent cohomology,
`AlgebraicGeometry.globalSectionsHomologyComparison` is the canonical comparison
`Hⁿ(Γ(Spec R, K)) ⟶ Γ(Spec R, Hⁿ(K))` of the left exact functor `Γ(Spec R, -)` with cohomology.

The degreewise sheafification–sections counit `(Γ(Spec R, K)^•)^~ ⟶ K` is carried by
`Γ(Spec R, -)` to an isomorphism of complexes, and both comparisons are natural, so the statement
follows from `AlgebraicGeometry.globalSectionsHomologyComparison_tilde` at
`N = Γ(Spec R, K)^•`. -/
lemma globalSectionsHomologyComparison_eq (n : ℤ) (K : CochainComplex (Spec R).Modules ℤ)
    (hK : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj K)) :
    globalSectionsHomologyComparison R n K hK =
      homologyToMapHomology (globalSectionsOver (𝟙 (Spec R))) K n := by
  have hqc := derivedQuasicoherent_Q_obj_mapHomologicalComplex_tilde R
    (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hnat := globalSectionsHomologyComparison_naturality R n hqc hK (tildeComplexCounit R K)
  have hA := globalSectionsHomologyComparison_tilde R n
    (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hqc
  have hcnat := homologyToMapHomology_naturality (globalSectionsOver (𝟙 (Spec R)))
    (tildeComplexCounit R K) n
  rw [← cancel_epi (HomologicalComplex.homologyMap
    (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (tildeComplexCounit R K)) n), hcnat, ← hA]
  exact hnat

/-- `AlgebraicGeometry.globalSectionsCyclesToHomology` is the cycles comparison of the left exact
functor `Γ(Spec R, -)` followed by the projection onto homology. -/
lemma globalSectionsCyclesToHomology_eq {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    globalSectionsCyclesToHomology f K n =
      mapCycles (globalSectionsOver f) K n ≫
        (((globalSectionsOver f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homologyπ n := by
  simp only [globalSectionsCyclesToHomology]
  congr 1

/-- **Stacks 06Z0, the canonical degree-zero comparison.** The degree-zero identification
`H⁰(RΓ(Spec R, E)) ≅ Γ(Spec R, H⁰(E))` of
`AlgebraicGeometry.derivedGlobalSectionsHomologyZeroIso` sends a global cycle of a complex `K`
with quasi-coherent cohomology to its section of the degree-zero cohomology sheaf: the composite
`Γ(Spec R, Z⁰(K)) ⟶ H⁰(Γ(Spec R, K)) ⟶ H⁰(RΓ(Spec R, Q K)) ⟶ Γ(Spec R, H⁰(Q K)) ⟶
Γ(Spec R, H⁰(K))` is `Γ(Spec R, -)` applied to `K.homologyπ 0`.

Together with naturality this characterizes the isomorphism:
`AlgebraicGeometry.globalSectionsCyclesToHomology` is an epimorphism, being the isomorphism
`Γ(Z⁰(K)) ≅ Z⁰(Γ(K))` followed by `HomologicalComplex.homologyπ`. The content is
`AlgebraicGeometry.globalSectionsHomologyComparison_eq`. -/
@[stacks 06Z0 "canonical degree-zero comparison"]
theorem globalSectionsCyclesToHomology_comp_derivedGlobalSectionsHomologyZeroIso
    (K : CochainComplex (Spec R).Modules ℤ)
    (hK : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) (DerivedCategory.Q.obj K)) :
    globalSectionsCyclesToHomology (𝟙 (Spec R)) K 0 ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).inv.app
          (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
          (globalSectionsComplexComparison (𝟙 (Spec R)) K) ≫
        (derivedGlobalSectionsHomologyZeroIso R).hom.app ⟨DerivedCategory.Q.obj K, hK⟩ ≫
        (globalSectionsOver (𝟙 (Spec R))).map
          ((DerivedCategory.homologyFunctorFactors (Spec R).Modules 0).hom.app K) =
      (globalSectionsOver (𝟙 (Spec R))).map (K.homologyπ 0) := by
  change globalSectionsCyclesToHomology (𝟙 (Spec R)) K 0 ≫
    globalSectionsHomologyComparison R 0 K hK = _
  rw [globalSectionsCyclesToHomology_eq, globalSectionsHomologyComparison_eq, Category.assoc]
  exact mapCycles_comp_homologyπ_comp_homologyToMapHomology _ _ _

end AlgebraicGeometry

end
