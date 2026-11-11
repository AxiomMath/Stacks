module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.RingTheory.Tor.BaseChangeOfUniverse

/-!
# The change-of-rings map on `Tor` and flat base change

Let `R → R'` be a homomorphism of commutative rings and let `M`, `N` be `R`-modules. Write
`M' = M ⊗_R R'` and `N' = N ⊗_R R'`. There is a natural `R`-linear map

`Tor_i^R(M, N) ⟶ Tor_i^{R'}(M', N')`

(Stacks, Section 00M7, item (2)), and hence, `Tor_i^{R'}(M', N')` being an `R'`-module, a natural
`R'`-linear map

`Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M', N')`.

Neither needs any hypothesis on `R → R'`. When `R'` is flat over `R` the second one is an
isomorphism (Stacks 00M8).

## Main definitions

* `torBaseChangeMap`: the `R`-linear change-of-rings map
  `Tor_i^R(M, N) ⟶ Tor_i^{R'}(M', N')` of Stacks 00M7 (2), for an arbitrary `R → R'`.
* `torBaseChangeComparison`: its `R'`-linear extension
  `Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M', N')`.

## Main results

* `isIso_torBaseChangeComparison`: **Stacks 00M8**, the comparison is an isomorphism when `R'`
  is flat over `R`.
* `torBaseChangeComparison_eq`: for flat `R'` the comparison is the morphism obtained by base
  changing a projective resolution of `N`.

## Implementation notes

Let `P` be the chosen projective resolution of `N` over `R` and `Q` the chosen projective
resolution of `N'` over `R'`. The unit `N ⟶ N'` of the extension-restriction adjunction lifts to a
chain map `P ⟶ Q` of `R`-modules (`Q` read over `R`), by
`CategoryTheory.ProjectiveResolution.lift'`, which only needs the target to be a resolution: in
degree `k` it is `p ↦ ψ(p)`. Tensoring with `M` and using `m ⊗ q ↦ (1 ⊗ m) ⊗ q` gives the chain map
`M ⊗_R P ⟶ M' ⊗_{R'} Q` whose map on homology is the change-of-rings map. It is built here as the
composite of the degreewise unit, the monoidal comparison of extension of scalars and the adjoint
`P ⊗_R R' ⟶ Q` of the lift, so that no element-level computation is needed. Restriction of
scalars is exact, so homology of `Q` read over `R` is the homology over `R'` read over `R`.

For flat `R'`, `P ⊗_R R'` is itself a projective resolution of `N'`, the adjoint lift is a homotopy
equivalence, and extension of scalars commutes with homology; this identifies the comparison with
a composite of isomorphisms.

## References

* [Stacks, Section 00M7](https://stacks.math.columbia.edu/tag/00M7)
* [Stacks, Tag 00M8](https://stacks.math.columbia.edu/tag/00M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

/-! ### Homology of the unit of an adjunction of exact functors -/

section Adjunction

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]

/-- Let `adj : L ⊣ G` be an adjunction of additive functors preserving homology, `K` a homological
complex in `C` and `g : L(K) ⟶ K'` a chain map. Then the map on homology of the adjoint chain map
`K ⟶ G(K')`, read through the comparison of `G` with homology, is the adjoint of the map on
homology of `g`, read through the comparison of `L` with homology. -/
@[reassoc]
theorem homologyFunctor_map_unit_comp_mapHomologicalComplexHomologyIso {L : C ⥤ D} {G : D ⥤ C}
    [L.Additive] [G.Additive] [L.PreservesHomology] [G.PreservesHomology] (adj : L ⊣ G)
    {ι : Type*} (c : ComplexShape ι) (i : ι) (K : HomologicalComplex C c)
    {K' : HomologicalComplex D c} (g : (L.mapHomologicalComplex c).obj K ⟶ K') :
    (HomologicalComplex.homologyFunctor C c i).map
          ((NatTrans.mapHomologicalComplex adj.unit c).app K ≫
            (G.mapHomologicalComplex c).map g) ≫
        (G.mapHomologicalComplexHomologyIso c i).hom.app K' =
      adj.unit.app ((HomologicalComplex.homologyFunctor C c i).obj K) ≫
        G.map ((L.mapHomologicalComplexHomologyIso c i).inv.app K ≫
          (HomologicalComplex.homologyFunctor D c i).map g) := by
  have : (L ⋙ G).PreservesHomology := Functor.preservesHomology_comp L G
  set S := (HomologicalComplex.shortComplexFunctor C c i).obj K with hS
  have hid : (S.mapHomologyIso (𝟭 C)).hom = CategoryStruct.id S.homology := by
    have hsq : (S.mapHomologyIso (𝟭 C)).hom
        = (S.mapHomologyIso (𝟭 C)).hom ≫ (S.mapHomologyIso (𝟭 C)).hom :=
      ShortComplex.mapHomologyIso_comp_hom S (𝟭 C) (𝟭 C)
    exact ((cancel_epi (S.mapHomologyIso (𝟭 C)).hom).mp
      ((Category.comp_id _).trans hsq)).symm
  have key : ShortComplex.homologyMap (S.mapNatTrans adj.unit) =
      (S.mapHomologyIso (𝟭 C)).hom ≫ adj.unit.app S.homology ≫
        (S.mapHomologyIso (L ⋙ G)).inv :=
    ShortComplex.homologyMap_mapNatTrans S adj.unit
  have hcomp : (S.mapHomologyIso (L ⋙ G)).hom =
      ((S.map L).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso L).hom :=
    ShortComplex.mapHomologyIso_comp_hom S L G
  have hgoal : ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫
      (S.mapHomologyIso (L ⋙ G)).hom = adj.unit.app S.homology := by
    rw [key, hid]
    simp
  rw [hcomp] at hgoal
  have h0 : (HomologicalComplex.homologyFunctor C c i).map
          ((NatTrans.mapHomologicalComplex adj.unit c).app K) ≫
        (G.mapHomologicalComplexHomologyIso c i).hom.app ((L.mapHomologicalComplex c).obj K) ≫
          G.map ((L.mapHomologicalComplexHomologyIso c i).hom.app K) =
      adj.unit.app ((HomologicalComplex.homologyFunctor C c i).obj K) :=
    hgoal
  have h1 : (HomologicalComplex.homologyFunctor C c i).map
          ((NatTrans.mapHomologicalComplex adj.unit c).app K) ≫
        (G.mapHomologicalComplexHomologyIso c i).hom.app ((L.mapHomologicalComplex c).obj K) =
      adj.unit.app ((HomologicalComplex.homologyFunctor C c i).obj K) ≫
        G.map ((L.mapHomologicalComplexHomologyIso c i).inv.app K) :=
    (Iso.eq_comp_inv (G.mapIso ((L.mapHomologicalComplexHomologyIso c i).app K))).mpr
      ((Category.assoc _ _ _).trans h0)
  have hn : (HomologicalComplex.homologyFunctor C c i).map ((G.mapHomologicalComplex c).map g) ≫
        (G.mapHomologicalComplexHomologyIso c i).hom.app K' =
      (G.mapHomologicalComplexHomologyIso c i).hom.app ((L.mapHomologicalComplex c).obj K) ≫
        G.map ((HomologicalComplex.homologyFunctor D c i).map g) :=
    (G.mapHomologicalComplexHomologyIso c i).hom.naturality g
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc, h1, Category.assoc,
    ← G.map_comp]

end Adjunction

/-! ### The change-of-rings map -/

section ChangeOfRings

universe u

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Restriction of scalars along `R → R'` preserves homology, being exact. -/
local instance (priority := 3000) :
    (ModuleCat.restrictScalars.{u} (algebraMap R R')).PreservesHomology :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{u} (algebraMap R R'))).out 2 3).mp
    (ModuleCat.restrictScalars_map_exact (algebraMap R R'))

variable (R') in
/-- The lift of the unit `N ⟶ N ⊗_R R'` to a chain map from the chosen projective resolution of
`N` over `R` to the chosen projective resolution of `N ⊗_R R'` over `R'`, read over `R`. No
hypothesis on `R → R'` is needed: the target is a resolution, which is all
`CategoryTheory.ProjectiveResolution.lift'` asks for. -/
noncomputable def torBaseChangeResolutionLift (N : ModuleCat.{u} R) :
    (ProjectiveResolution.of N).complex ⟶
      ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex :=
  ProjectiveResolution.lift' ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app N)
    (ProjectiveResolution.of N)
    ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapAugmentation
      (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).π)

variable (R') in
/-- The `R'`-linear adjoint `P ⊗_R R' ⟶ Q` of `torBaseChangeResolutionLift`, where `P` and `Q` are
the chosen projective resolutions of `N` and of `N ⊗_R R'`. -/
noncomputable def torBaseChangeResolutionLiftAdj (N : ModuleCat.{u} R) :
    ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex ⟶
      (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex :=
  ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (torBaseChangeResolutionLift R' N) ≫
    (NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).counit
      (ComplexShape.down ℕ)).app
        (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex

variable (R') in
/-- The chain map `(M ⊗_R P) ⊗_R R' ⟶ (M ⊗_R R') ⊗_{R'} Q` of `R'`-modules,
`(m ⊗ p) ⊗ r ↦ r • ((1 ⊗ m) ⊗ ψ(p))`: the monoidal comparison of extension of scalars followed by
the adjoint lift `torBaseChangeResolutionLiftAdj`. Here `P` and `Q` are the chosen projective
resolutions of `N` and of `N ⊗_R R'`. -/
noncomputable def torBaseChangeComplexMap (M N : ModuleCat.{u} R) :
    ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of N).complex) ⟶
      ((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex :=
  (NatIso.mapHomologicalComplex (torBaseChangeTensorIsoOfUniverse (S' := R') M)
      (ComplexShape.down ℕ)).hom.app (ProjectiveResolution.of N).complex ≫
    ((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (torBaseChangeResolutionLiftAdj R' N)

variable (R') in
/-- The chain map `M ⊗_R P ⟶ (M ⊗_R R') ⊗_{R'} Q` of `R`-modules, `m ⊗ p ↦ (1 ⊗ m) ⊗ ψ(p)`, which
computes the change-of-rings map on `Tor`: the adjoint of `torBaseChangeComplexMap`. Here `P` and
`Q` are the chosen projective resolutions of `N` and of `N ⊗_R R'` and `ψ` is
`torBaseChangeResolutionLift`. -/
noncomputable def torBaseChangeChainMap (M N : ModuleCat.{u} R) :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of N).complex ⟶
      ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        (((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of
            ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex) :=
  (NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit
      (ComplexShape.down ℕ)).app
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of N).complex) ≫
    ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (torBaseChangeComplexMap R' M N)

variable (R') in
/-- **The change-of-rings map on `Tor`** (Stacks, Section 00M7, item (2)). For an arbitrary
homomorphism of commutative rings `R → R'` and `R`-modules `M`, `N`, the natural `R`-linear map
`Tor_i^R(M, N) ⟶ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')`, the target read as an `R`-module. It is induced
on homology by `torBaseChangeChainMap`, `m ⊗ p ↦ (1 ⊗ m) ⊗ ψ(p)`. -/
noncomputable def torBaseChangeMap (i : ℕ) (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) i).obj M).obj N ⟶
      (ModuleCat.restrictScalars.{u} (algebraMap R R')).obj
        (((Tor (ModuleCat.{u} R') i).obj ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).obj
          ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)) :=
  ((ProjectiveResolution.of N).isoLeftDerivedObj (tensorLeft M) i).hom ≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
      (torBaseChangeChainMap R' M N) ≫
      ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapHomologicalComplexHomologyIso
          (ComplexShape.down ℕ) i).hom.app
        (((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex) ≫
        (ModuleCat.restrictScalars.{u} (algebraMap R R')).map
          ((ProjectiveResolution.of
            ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).isoLeftDerivedObj
            (tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)) i).inv

variable (R') in
/-- **The base-change map on `Tor`.** For an arbitrary homomorphism of commutative rings
`R → R'` and `R`-modules `M`, `N`, the natural `R'`-linear map
`Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')`: the `R'`-linear extension of the
change-of-rings map `torBaseChangeMap` of Stacks 00M7 (2). -/
noncomputable def torBaseChangeComparison (i : ℕ) (M N : ModuleCat.{u} R) :
    (torBaseChangeOfUniverse (S := R) (S' := R')).obj (((Tor (ModuleCat.{u} R) i).obj M).obj N) ⟶
      ((Tor (ModuleCat.{u} R') i).obj ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).obj
        ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _).symm
    (torBaseChangeMap R' i M N)

/-- The change-of-rings map is the adjoint of the base-change map. -/
theorem torBaseChangeMap_eq (i : ℕ) (M N : ModuleCat.{u} R) :
    torBaseChangeMap R' i M N =
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app _ ≫
        (ModuleCat.restrictScalars.{u} (algebraMap R R')).map (torBaseChangeComparison R' i M N) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _).apply_symm_apply
    (torBaseChangeMap R' i M N) |>.symm.trans
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv_unit _ _ _)

/-! ### Flat base change -/

/-- For flat `R'`, the adjoint lift `P ⊗_R R' ⟶ Q` is compatible with the augmentations of the
two projective resolutions of `N ⊗_R R'`. -/
theorem torBaseChangeResolutionLiftAdj_comp_π [Module.Flat R R'] (N : ModuleCat.{u} R) :
    torBaseChangeResolutionLiftAdj R' N ≫
        (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).π =
      (((torBaseChangeOfUniverse (S := R) (S' := R')).mapProjectiveResolution
        (ProjectiveResolution.of N)).π :
          ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex ⟶ _) := by
  have hl : (torBaseChangeResolutionLift R' N).f 0 ≫
      (ModuleCat.restrictScalars.{u} (algebraMap R R')).map
        ((ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).π.f 0) =
      (ProjectiveResolution.of N).π.f 0 ≫
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app N := by
    have h := ProjectiveResolution.lift'_commutes_zero
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app N)
      (ProjectiveResolution.of N)
      ((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapAugmentation
        (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).π)
    rw [Functor.mapAugmentation_f_zero] at h
    exact h
  have hπ0 : ((torBaseChangeOfUniverse (S := R) (S' := R')).mapProjectiveResolution
        (ProjectiveResolution.of N)).π.f 0 =
      (torBaseChangeOfUniverse (S := R) (S' := R')).map ((ProjectiveResolution.of N).π.f 0) :=
    Functor.mapAugmentation_f_zero _ (ProjectiveResolution.of N).π
  have htri : ∀ {X : ModuleCat.{u} R} (x : X ⟶ N),
      (torBaseChangeOfUniverse (S := R) (S' := R')).map
          (x ≫ (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app N) ≫
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).counit.app
          ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N) =
      (torBaseChangeOfUniverse (S := R) (S' := R')).map x := by
    intro X x
    rw [CategoryTheory.Functor.map_comp, Category.assoc, Adjunction.left_triangle_components,
      Category.comp_id]
  have h0 : (torBaseChangeResolutionLiftAdj R' N).f 0 ≫
      (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).π.f 0 =
      (torBaseChangeOfUniverse (S := R) (S' := R')).map ((ProjectiveResolution.of N).π.f 0) := by
    rw [torBaseChangeResolutionLiftAdj, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Category.assoc,
      ← Adjunction.counit_naturality, ← CategoryTheory.Functor.map_comp_assoc, hl]
    exact htri _
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, hπ0]
  exact h0

/-- For flat `R'`, the adjoint lift `P ⊗_R R' ⟶ Q` induces isomorphisms on the homology of its
image under any additive functor: `P ⊗_R R'` is then a projective resolution of `N ⊗_R R'`. -/
theorem isIso_homologyFunctor_map_torBaseChangeResolutionLiftAdj [Module.Flat R R']
    (N : ModuleCat.{u} R) (F : ModuleCat.{u} R' ⥤ ModuleCat.{u} R') [F.Additive] (i : ℕ) :
    IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (torBaseChangeResolutionLiftAdj R' N))) := by
  let eP := (torBaseChangeOfUniverse (S := R) (S' := R')).mapProjectiveResolution
    (ProjectiveResolution.of N)
  let Q := ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)
  let π' : ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex ⟶
        (ChainComplex.single₀ _).obj ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N) :=
    eP.π
  have : QuasiIso π' := eP.quasiIso
  have : ∀ n, Projective ((((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex).X n) := eP.projective
  let θ : Q.complex ⟶ ((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (ProjectiveResolution.of N).complex :=
    ProjectiveResolution.lift (𝟙 _) Q eP
  have hθ : θ ≫ π' = Q.π :=
    (ProjectiveResolution.lift_commutes (𝟙 _) Q eP).trans
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id])
  have hψ : torBaseChangeResolutionLiftAdj R' N ≫ Q.π = π' :=
    torBaseChangeResolutionLiftAdj_comp_π (R' := R') N
  have h1 := ProjectiveResolution.homologyMap_map_eq_of_comp_eq π' F
    (torBaseChangeResolutionLiftAdj R' N ≫ θ) (𝟙 _)
    (by rw [Category.assoc, hθ, hψ, Category.id_comp]) i
  have h2 := ProjectiveResolution.homologyMap_map_eq_of_comp_eq Q.π F
    (θ ≫ torBaseChangeResolutionLiftAdj R' N) (𝟙 _)
    (by rw [Category.assoc, hψ, hθ, Category.id_comp]) i
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at h1 h2
  exact ⟨⟨(HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map θ), h1, h2⟩⟩

/-- For flat `R'`, the base-change map on `Tor` is the composite
`Tor_i^R(M, N) ⊗_R R' ≅ H_i(M ⊗_R P) ⊗_R R' ≅ H_i((M ⊗_R P) ⊗_R R') ⟶ H_i(M' ⊗_{R'} Q)
≅ Tor_i^{R'}(M', N')`, whose third arrow is induced by `torBaseChangeComplexMap`. -/
theorem torBaseChangeComparison_eq [Module.Flat R R'] (i : ℕ) (M N : ModuleCat.{u} R) :
    torBaseChangeComparison R' i M N =
      (torBaseChangeOfUniverse (S := R) (S' := R')).map
          ((ProjectiveResolution.of N).isoLeftDerivedObj (tensorLeft M) i).hom ≫
        (((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplexHomologyIso
            (ComplexShape.down ℕ) i).inv.app
          (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (ProjectiveResolution.of N).complex) ≫
          (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
            (torBaseChangeComplexMap R' M N)) ≫
          ((ProjectiveResolution.of
            ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).isoLeftDerivedObj
            (tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)) i).inv := by
  have habs : ∀ {A B W : ModuleCat.{u} R} {Y Z : ModuleCat.{u} R'} (a : A ⟶ B) (h₁ : B ⟶ W)
      (h₂ : W ⟶ (ModuleCat.restrictScalars.{u} (algebraMap R R')).obj Y)
      (j : (torBaseChangeOfUniverse (S := R) (S' := R')).obj B ⟶ Y) (c : Y ⟶ Z),
      h₁ ≫ h₂ = (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app B ≫
        (ModuleCat.restrictScalars.{u} (algebraMap R R')).map j →
      a ≫ h₁ ≫ h₂ ≫ (ModuleCat.restrictScalars.{u} (algebraMap R R')).map c =
        (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app A ≫
          (ModuleCat.restrictScalars.{u} (algebraMap R R')).map
            ((torBaseChangeOfUniverse (S := R) (S' := R')).map a ≫ j ≫ c) := by
    intro A B W Y Z a h₁ h₂ j c hk
    have hn := (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.naturality a
    rw [← Category.assoc h₁ h₂, hk, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, ← Category.assoc a,
      ← Category.assoc ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).unit.app A)]
    exact congrArg (· ≫ _) hn
  have hk := homologyFunctor_map_unit_comp_mapHomologicalComplexHomologyIso
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')) (ComplexShape.down ℕ) i
    (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (ProjectiveResolution.of N).complex) (torBaseChangeComplexMap R' M N)
  have hΦ := habs ((ProjectiveResolution.of N).isoLeftDerivedObj (tensorLeft M) i).hom
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
      (torBaseChangeChainMap R' M N))
    (((ModuleCat.restrictScalars.{u} (algebraMap R R')).mapHomologicalComplexHomologyIso
          (ComplexShape.down ℕ) i).hom.app
        (((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).complex))
    _
    ((ProjectiveResolution.of
      ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).isoLeftDerivedObj
      (tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)) i).inv hk
  exact ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _).symm_apply_eq.mpr
    (hΦ.trans ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv_unit _ _ _).symm)

variable (R') in
/-- **Flat base change for `Tor`** (Stacks 00M8). Let `R → R'` be a flat homomorphism of
commutative rings and let `M`, `N` be `R`-modules. Then for every `i` the natural `R'`-linear map
`Tor_i^R(M, N) ⊗_R R' ⟶ Tor_i^{R'}(M ⊗_R R', N ⊗_R R')`, the `R'`-linear extension of the
change-of-rings map of Stacks 00M7 (2), is an isomorphism.

The map `torBaseChangeComparison` is defined for every `R → R'`, from `torBaseChangeMap`;
flatness is used only here. -/
@[stacks 00M8]
theorem isIso_torBaseChangeComparison [Module.Flat R R'] (i : ℕ) (M N : ModuleCat.{u} R) :
    IsIso (torBaseChangeComparison R' i M N) := by
  have := isIso_homologyFunctor_map_torBaseChangeResolutionLiftAdj (R' := R') N
    (tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)) i
  have e1 : (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
        (torBaseChangeComplexMap R' M N) =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
          ((NatIso.mapHomologicalComplex (torBaseChangeTensorIsoOfUniverse (S' := R') M)
            (ComplexShape.down ℕ)).hom.app (ProjectiveResolution.of N).complex) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
          (((tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (torBaseChangeResolutionLiftAdj R' N)) :=
    CategoryTheory.Functor.map_comp _ _ _
  have : IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).map
      (torBaseChangeComplexMap R' M N)) := by
    rw [e1]
    infer_instance
  rw [torBaseChangeComparison_eq]
  refine IsIso.comp_isIso' (Functor.map_isIso _ _)
    (IsIso.comp_isIso' (IsIso.comp_isIso' ?_ this) (Iso.isIso_inv
      ((ProjectiveResolution.of
        ((torBaseChangeOfUniverse (S := R) (S' := R')).obj N)).isoLeftDerivedObj
        (tensorLeft ((torBaseChangeOfUniverse (S := R) (S' := R')).obj M)) i)))
  exact Iso.isIso_inv
    (((torBaseChangeOfUniverse (S := R) (S' := R')).mapHomologicalComplexHomologyIso
      (ComplexShape.down ℕ) i).app
        (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (ProjectiveResolution.of N).complex))

end ChangeOfRings
