module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorSide

/-!
# Localizing the two transposes of the chain-level change-of-rings comparison

`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso` is an equation
between maps of cochain complexes `P ⊗_R K ⟶ I`: the transpose over [stacks 0GMT] of the inverse
monoidality isomorphism of degreewise extension of scalars followed by the uncurrying of a map
`s : A ⊗_R P ⟶ Hom^•_A(A ⊗_R K, J)`, followed by a map `q : J|_R ⟶ I`, equals the uncurrying of
the transpose of `s` followed by
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`.  Two transposes occur in it: the
extension–restriction transpose of [stacks 0GMT], twice, and the tensor–Hom transpose of
[stacks 0A63], once over `R` and once over `A`.

Both transposes have derived-category counterparts, and this file localizes the equation: it
records the two transposes as statements about the localization functor and then transports the
chain equation across them.

* The transpose of [stacks 0GMT] localizes *unconditionally*.  The unit of
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` at the class of a
  complex, composed with the comparison of the chosen model with degreewise extension of scalars,
  is the localized degreewise unit
  (`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`).
* The transpose of [stacks 0A63] localizes at a K-flat Hom-source and a K-injective target, by
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`.  Over `A` the Hom-source
  is `A ⊗_R K`, which is K-flat whenever `K` is, by
  `CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`.

## Main results

* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_Q_map` —
  **the transpose of [stacks 0GMT] on a localized chain map**: the transpose of
  `comparison.app X ≫ Q.map g` is the localization of the degreewise transpose of `g`, read
  through `CategoryTheory.Functor.mapDerivedCategoryFactors`.  Unconditional.
* `Stacks.DerivedHom.BaseChangeIso.homEquiv_uncurry_extendScalars` — the transpose of
  [stacks 0A63] over `A` at the extension of scalars of a K-flat complex.
* `Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_comp_eq_of_uncurry_eq` — **the localization**:
  a chain equation of the shape of
  `Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso` becomes an
  equation in the derived category between the transpose of [stacks 0GMT] of the localized left
  argument and the transpose of [stacks 0A63] of the localized right one.
* `Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_derived` — that localization at the
  chain equation itself.
* `Stacks.DerivedHom.BaseChangeIso.exists_chainRep_homEquiv_uncurry_extendScalars` — every
  morphism of the derived category into the internal Hom of the two extensions of scalars is the
  localization of a chain map, the Hom complex being K-injective.
* `Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_derived_of_hom` — **the comparison
  at an arbitrary derived morphism**.
* `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_homComplex` — the
  representative model comparison `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`,
  written in terms of the localized chain map
  `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`.

## References

* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CochainComplex.DerivedExtensionScalars

universe uR uA uM wR wA

/-- **The transpose of [stacks 0GMT] on a localized chain map.**  Let `F` be a total left derived
model of extension of scalars along `f : R → A`, with comparison `comparison` to degreewise
extension of scalars.  For a chain map `g : A ⊗_R X ⟶ W`, the adjoint transpose of
`comparison.app X ≫ Q.map g` under `derivedExtensionScalarsAdjunction` is the localization of the
degreewise transpose of `g` under the extension–restriction adjunction on cochain complexes, read
through `CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
public theorem derivedExtensionScalarsAdjunction_homEquiv_Q_map
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (W : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (g : ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X ⟶ W),
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv
        (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj W)
        (comparison.app X ≫ DerivedCategory.Q.map g) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv X W g) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
          W := by
  let _ : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let _ : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  let _ : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let _ : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF X W g
  have hnat := ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
    f).mapDerivedCategoryFactors.inv.naturality g)
  dsimp only [Functor.comp_map] at hnat
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    derivedExtensionScalarsAdjunction_unit_app.{uR, uA, uM} f F comparison X, Category.assoc,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hnat]

end CochainComplex.DerivedExtensionScalars

namespace Stacks.DerivedHom.BaseChangeIso

open CochainComplex.ExtendScalars CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

universe u wR wA

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)] [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

/-- Extension of scalars along `f` is an additive functor. -/
local instance extendScalarsAdditive' : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of
scalars. -/
local instance extendScalarsLeftAdjoint' :
    (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint

/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of
scalars. -/
local instance restrictScalarsRightAdjoint' :
    (ModuleCat.restrictScalars.{u, u, u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isRightAdjoint

/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance restrictScalarsLeftAdjoint' :
    (ModuleCat.restrictScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).isLeftAdjoint

omit [HasDerivedCategory.{wR} (ModuleCat.{u} R)] in
/-- **The transpose of [stacks 0A63] over `A` at an extension of scalars.**  This is
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` with the Hom-source taken
to be the degreewise extension of scalars `A ⊗_R K` of a K-flat complex of `R`-modules, which is
K-flat over `A` by `CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`. -/
public theorem homEquiv_uncurry_extendScalars
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (s : (mapCochainComplex f).obj P ⟶
      CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J) :
    DerivedInternalHom.Model.homEquiv
        (DerivedCategory.Q.obj ((mapCochainComplex f).obj P))
        (DerivedCategory.Q.obj ((mapCochainComplex f).obj K)) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.map s ≫
          ((DerivedInternalHom.Model.adjunction A).homIso
            ((mapCochainComplex f).obj K) J).inv) =
      ((DerivedInternalHom.Model.adjunction A).tensorIso ((mapCochainComplex f).obj P)
            ((mapCochainComplex f).obj K)
            (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K hK)).hom ≫
        DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry s) :=
  DerivedInternalHom.Model.homEquiv_map_uncurry _ _ _ _ s

omit [HasDerivedCategory.{wR} (ModuleCat.{u} R)] in
/-- **Every derived morphism into the internal Hom of the two extensions of scalars comes from a
chain map, and its transpose is the localized uncurrying.**  Here `K` is K-flat over `R` and `J`
is K-injective over `A`. -/
public theorem exists_chainRep_homEquiv_uncurry_extendScalars
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (v : DerivedCategory.Q.obj ((mapCochainComplex f).obj P) ⟶
      (DerivedInternalHom.Model.hom A).obj
        (Opposite.op (DerivedCategory.Q.obj ((mapCochainComplex f).obj K)),
          DerivedCategory.Q.obj J)) :
    ∃ s : (mapCochainComplex f).obj P ⟶
        CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J,
      v = DerivedCategory.Q.map s ≫
          ((DerivedInternalHom.Model.adjunction A).homIso
            ((mapCochainComplex f).obj K) J).inv ∧
        DerivedInternalHom.Model.homEquiv
            (DerivedCategory.Q.obj ((mapCochainComplex f).obj P))
            (DerivedCategory.Q.obj ((mapCochainComplex f).obj K)) (DerivedCategory.Q.obj J) v =
          ((DerivedInternalHom.Model.adjunction A).tensorIso ((mapCochainComplex f).obj P)
              ((mapCochainComplex f).obj K)
              (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K hK)).hom ≫
            DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry s) := by
  let : (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J).IsKInjective :=
    StacksDraft.DerivedHom.homComplex_isKInjective_of_kFlat ((mapCochainComplex f).obj K) J
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K hK)
  obtain ⟨s, hs⟩ := StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective
    ((mapCochainComplex f).obj P)
    (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J)
    (v ≫ ((DerivedInternalHom.Model.adjunction A).homIso
      ((mapCochainComplex f).obj K) J).hom)
  have hv : v = DerivedCategory.Q.map s ≫
      ((DerivedInternalHom.Model.adjunction A).homIso
        ((mapCochainComplex f).obj K) J).inv := by
    rw [hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨s, hv, ?_⟩
  rw [hv]
  exact homEquiv_uncurry_extendScalars f P K hK J s

/-- The transpose of `comparison.app X ≫ Q.map g`, read into `D(R)` and followed by the localization
of `q`, is the localization of the degreewise transpose of `g` followed by `q`. -/
private theorem homEquiv_Q_map_comp_factors_hom
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (W : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X ⟶ W)
    (q : ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W ⟶ I) :
    (derivedExtensionScalarsAdjunction.{u, u, u} f F comparison).homEquiv
            (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj W)
            (comparison.app X ≫ DerivedCategory.Q.map g) ≫
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app W ≫
            DerivedCategory.Q.map q =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv X W g ≫ q) := by
  rw [derivedExtensionScalarsAdjunction_homEquiv_Q_map.{u, u, u} f F comparison X W g,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

/-- **The localization of a chain equation across the two transposes.**  Let `g : A ⊗_R (P ⊗_R K)
⟶ W` and `t : P ⟶ Hom^•_R(K, I)` be maps of complexes, with `K` K-flat and `I` K-injective, and
let `q : W|_R ⟶ I`.  If the degreewise transpose of `g` over [stacks 0GMT], followed by `q`, is
the uncurrying of `t`, then the transpose of `comparison.app (P ⊗ K) ≫ Q.map g` over
[stacks 0GMT] in the derived category, read into `D(R)` and followed by `q`, is the transpose of
`Q.map t` over [stacks 0A63]. -/
public theorem homEquiv_Q_map_comp_eq_of_uncurry_eq
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (W : CochainComplex (ModuleCat.{u} A) ℤ)
    (g : ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (P ⊗ K) ⟶ W)
    (q : ((ModuleCat.restrictScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W ⟶ I)
    (t : P ⟶ CochainComplex.HomComplexR R K I)
    (h : ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv (P ⊗ K) W g ≫ q =
      DerivedInternalHom.Model.uncurry t) :
    (derivedExtensionScalarsAdjunction.{u, u, u} f F comparison).homEquiv
            (DerivedCategory.Q.obj (P ⊗ K)) (DerivedCategory.Q.obj W)
            (comparison.app (P ⊗ K) ≫ DerivedCategory.Q.map g) ≫
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app W ≫
            DerivedCategory.Q.map q =
      ((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).inv ≫
        DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj I)
          (DerivedCategory.Q.map t ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).inv) := by
  rw [DerivedInternalHom.Model.homEquiv_map_uncurry P K I hK t, ← h,
    homEquiv_Q_map_comp_factors_hom f F comparison, Iso.inv_hom_id_assoc]

/-- **The chain-level change-of-rings comparison, localized.**  This is
`Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_comp_eq_of_uncurry_eq` at the chain equation
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso`: the transpose
over [stacks 0GMT] of the comparison `comparison.app (P ⊗ K)` followed by the localized inverse
monoidality isomorphism of degreewise extension of scalars and the uncurrying of `s`, read into
`D(R)` and followed by `q`, is the transpose over [stacks 0A63] of the localized transpose of `s`
followed by `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`. -/
public theorem homComplexChangeOfRingsMap_derived
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (s : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj P ⟶
      CochainComplex.HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) :
    (derivedExtensionScalarsAdjunction.{u, u, u} f F comparison).homEquiv
            (DerivedCategory.Q.obj (P ⊗ K)) (DerivedCategory.Q.obj J)
            (comparison.app (P ⊗ K) ≫
              DerivedCategory.Q.map ((extendScalarsMonoidalIso f P K).inv ≫
                DerivedInternalHom.Model.uncurry s)) ≫
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app J ≫
            DerivedCategory.Q.map q =
      ((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).inv ≫
        DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj I)
          (DerivedCategory.Q.map
              (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
                    (ComplexShape.up ℤ)).homEquiv P
                  (CochainComplex.HomComplexR A
                    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) s ≫
                Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).inv) :=
  homEquiv_Q_map_comp_eq_of_uncurry_eq f F comparison P K hK I J _ q _
    (homComplexChangeOfRingsMap_uncurry_monoidalIso f P K J I q s)

/-- **The localized change-of-rings comparison at an arbitrary derived morphism.**  This is
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_derived` at an arbitrary morphism `v`
of the derived category out of the class of `A (x)_R P` into the internal Hom of the classes of
`A (x)_R K` and `J`, in place of a localized chain map `s`. -/
public theorem homComplexChangeOfRingsMap_derived_of_hom
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : CochainComplex.KFlat.{u, u} K)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (v : DerivedCategory.Q.obj ((mapCochainComplex f).obj P) ⟶
      (DerivedInternalHom.Model.hom A).obj
        (Opposite.op (DerivedCategory.Q.obj ((mapCochainComplex f).obj K)),
          DerivedCategory.Q.obj J)) :
    (derivedExtensionScalarsAdjunction.{u, u, u} f F comparison).homEquiv
            (DerivedCategory.Q.obj (P ⊗ K)) (DerivedCategory.Q.obj J)
            (comparison.app (P ⊗ K) ≫
              DerivedCategory.Q.map (extendScalarsMonoidalIso f P K).inv ≫
                ((DerivedInternalHom.Model.adjunction A).tensorIso ((mapCochainComplex f).obj P)
                    ((mapCochainComplex f).obj K)
                    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u}
                      f K hK)).inv ≫
                  DerivedInternalHom.Model.homEquiv
                    (DerivedCategory.Q.obj ((mapCochainComplex f).obj P))
                    (DerivedCategory.Q.obj ((mapCochainComplex f).obj K))
                    (DerivedCategory.Q.obj J) v) ≫
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app J ≫
            DerivedCategory.Q.map q =
      ((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).inv ≫
        DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj I)
          ((derivedExtensionScalarsAdjunction.{u, u, u} f F comparison).homEquiv
                (DerivedCategory.Q.obj P)
                (DerivedCategory.Q.obj (CochainComplex.HomComplexR A
                  ((mapCochainComplex f).obj K) J))
                (comparison.app P ≫ v ≫
                  ((DerivedInternalHom.Model.adjunction A).homIso
                    ((mapCochainComplex f).obj K) J).hom) ≫
              (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app
                  (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J) ≫
                DerivedCategory.Q.map
                  (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).inv) := by
  obtain ⟨s, hv, hu⟩ := exists_chainRep_homEquiv_uncurry_extendScalars f P K hK J v
  have key := homComplexChangeOfRingsMap_derived f F comparison P K hK J I q s
  rw [Functor.map_comp] at key
  have hB := derivedExtensionScalarsAdjunction_homEquiv_Q_map.{u, u, u} f F comparison P
    (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J) s
  rw [hu, ← Category.assoc
      (((DerivedInternalHom.Model.adjunction A).tensorIso ((mapCochainComplex f).obj P)
        ((mapCochainComplex f).obj K)
        (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f K hK)).inv),
    Iso.inv_hom_id, Category.id_comp, hv, Category.assoc, Iso.inv_hom_id, Category.comp_id, hB,
    Category.assoc, ← Category.assoc
      ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.inv.app
        (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J))]
  simp only [Iso.inv_hom_id_app, Category.id_comp]
  rw [← Category.assoc (DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv P
          (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J) s)),
    ← DerivedCategory.Q.map_comp
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv P
          (CochainComplex.HomComplexR A ((mapCochainComplex f).obj K) J) s)
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q)]
  exact key

end Stacks.DerivedHom.BaseChangeIso

section StandardModels

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedHom.BaseChangeIso

universe u

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The representative model comparison of [stacks 0E1W] is the localized chain-level
change-of-rings map, conjugated by the two representations.**  At a K-flat `K`, K-injective `J`
and `I` and a quasi-isomorphism `q`, `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`
is written in terms of the localization of
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`. -/
public theorem derivedHomChangeOfRingsModelIso_hom_eq_homComplex
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    (hK : CochainComplex.KFlat.{u, u} K) :
    letI : IsIso (α.app K) :=
      BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F α K hK
    letI := BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK).hom =
      (BaseChange.homModelIso K I (Iso.refl _)
          ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
            @asIso _ _ _ _ (DerivedCategory.Q.map q)
              ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        inv (DerivedCategory.Q.map
            (BaseChange.homComplexChangeOfRingsMap.{u, u, u} f K J I q)) ≫
          ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app
              (CochainComplex.HomComplexR A
                ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)).inv ≫
            (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
              (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
                (asIso (α.app K)) (Iso.refl _)).inv :=
  (BaseChange.modelRestrictScalarsNatIso_hom_app f F α K J I q hK).symm.trans
    (BaseChange.modelRestrictScalarsNatIso_hom_app_eq_homComplex f F α K J I q hK)

end Stacks.DerivedHom.BaseChangeIso

end StandardModels

end
