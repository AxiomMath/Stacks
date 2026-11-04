module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# The top-degree trace of a global class under base change

Let `p : Y ⟶ B` and `c ∈ Ext²(Λ_Y, Λ_Y)`, `Λ = ℤ/N`, and let `g' : Y' ⟶ Y`. The inverse image is
exact and monoidal, so it carries the action of `c` on a sheaf `F` with flat fibres to the action
of the pulled back class `c' = g'⁻¹ c` on `g'⁻¹ F`
(`Stacks.EtaleCohomology.TopTrace.inverseImage_classHom`). With the mate description of the base
change map this is what compares the trace of `c` along `p` with the trace of `c'` along the base
change of `p`, in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main definitions

* `Stacks.EtaleCohomology.TopTrace.pullClass`: `c' = g'⁻¹ c`.

## Main results

* `Stacks.EtaleCohomology.TopTrace.inverseImage_classHom`: `g'⁻¹(c · F) = c' · g'⁻¹F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {N : ℕ} {Y Y' : Scheme.{u}} (g' : Y' ⟶ Y)

/-- The pull-back `g'⁻¹ c ∈ Ext²(Λ_{Y'}, Λ_{Y'})` of a class `c ∈ Ext²(Λ_Y, Λ_Y)`. -/
def pullClass (c : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) (𝟙_ _) 2) :
    Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y')) (𝟙_ _) 2 :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  Stacks.ExtUnitAction.mapClass (etaleModuleInverseImage.{u, 0} (ZMod N) g') c

variable (c : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) (𝟙_ _) 2)

/-- **The inverse image carries the action of `c` to the action of `g'⁻¹ c`**, read in the
derived categories of abelian sheaves: `g'⁻¹(c · F) = c' · g'⁻¹F` under `g'⁻¹(U F)[0] ≅
U(g'⁻¹F)[0]`. -/
theorem inverseImage_classHom (F : EtaleModules.{u, 0} (ZMod N) Y) (hF : FlatFibres F) :
    (etaleAbelianDerivedInverseImage.{u, 0} g').map (classHom c F hF) ≫
        ((etaleAbelianDerivedInverseImage.{u, 0} g').commShiftIso ((2 : ℕ) : ℤ)).hom.app _ ≫
          ((inverseImageSingleIso g' F).hom)⟦((2 : ℕ) : ℤ)⟧' =
      (inverseImageSingleIso g' F).hom ≫ classHom (pullClass g' c) _ (hF.inverseImage g') := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  obtain ⟨_, _, _⟩ := hF.exact
  obtain ⟨_, _, _⟩ := (hF.inverseImage g').exact
  set e := Stacks.ExtUnitAction.action c F with he
  -- the action under `g'⁻¹` is the action of `g'⁻¹ c`
  have h1 : e.mapExactFunctor (etaleModuleInverseImage.{u, 0} (ZMod N) g') =
      Stacks.ExtUnitAction.action (pullClass g' c)
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g').obj F) :=
    Stacks.ExtUnitAction.mapExactFunctor_action _ c F
  -- `U ⋙ g'⁻¹ ≅ g'⁻¹ ⋙ U`
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) g').hom F 2 e
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor, h1] at key
  have key' := congrArg Ext.hom key
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at key'
  have hmap := Ext.mapExactFunctor_hom (etaleAbelianInverseImage.{u, 0} g')
    (e.mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N)))
  have hcomm : (etaleAbelianDerivedInverseImage.{u, 0} g').map
        (e.mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N))).hom ≫
        ((etaleAbelianDerivedInverseImage.{u, 0} g').commShiftIso ((2 : ℕ) : ℤ)).hom.app _ ≫
          (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).hom.app _)⟦
            ((2 : ℕ) : ℤ)⟧' =
      ((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        ((e.mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N))).mapExactFunctor
          (etaleAbelianInverseImage.{u, 0} g')).hom := by
    rw [hmap, ShiftedHom.map]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [classHom, inverseImageSingleIso, inverseImageSingleNatIso, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  rw [Functor.map_comp, reassoc_of% hcomm, ← key', Category.assoc]

/-! ### The edge map under base change -/

section Square

variable {B B' : Scheme.{u}} (p : Y ⟶ B) (g : B' ⟶ B) (p' : Y' ⟶ B') (h : g' ≫ p = p' ≫ g)

/-- The comparison of the two composite inverse images of sheaves of modules around the square
`g' ≫ p = p' ≫ g`. -/
def moduleSquareIso :
    etaleModuleInverseImage.{u, 0} (ZMod N) p ⋙ etaleModuleInverseImage.{u, 0} (ZMod N) g' ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) g ⋙ etaleModuleInverseImage.{u, 0} (ZMod N) p' :=
  (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) g' p).symm ≪≫
    eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod N)) h) ≪≫
    etaleModuleInverseImageCompIso.{u, 0} (ZMod N) p' g

/-- `g'⁻¹ p⁻¹ A ≅ p'⁻¹ g⁻¹ A`. -/
def moduleSquareIsoApp (A : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleModuleInverseImage.{u, 0} (ZMod N) g').obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A) ≅
      (etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A) :=
  (moduleSquareIso g' p g p' h).app A

/-- The isomorphism `p'⁻¹ g⁻¹ (U A)[0] ≅ U(p'⁻¹ g⁻¹ A)[0]` going around the square through `Y`:
the comparison of composite inverse images of abelian sheaves, then `p⁻¹` and `g'⁻¹` past `U`. -/
def squareSingleIsoAround (A : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleAbelianDerivedInverseImage.{u, 0} p').obj ((etaleAbelianDerivedInverseImage.{u, 0} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y' (ZMod N)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A))) :=
  (etaleAbelianDerivedInverseImageCompIso'.{u, 0} p' g (g' ≫ p) h).symm.app _ ≪≫
    (etaleAbelianDerivedInverseImageCompIso'.{u, 0} g' p (g' ≫ p) rfl).app _ ≪≫
    (etaleAbelianDerivedInverseImage.{u, 0} g').mapIso (inverseImageSingleIso p A) ≪≫
    inverseImageSingleIso g' _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((etaleModuleUnderlyingAbelian Y' (ZMod N)).mapIso (moduleSquareIsoApp g' p g p' h A))

/-- The same isomorphism going around the square through `B'`. -/
def squareSingleIsoDirect (A : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleAbelianDerivedInverseImage.{u, 0} p').obj ((etaleAbelianDerivedInverseImage.{u, 0} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y' (ZMod N)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A))) :=
  (etaleAbelianDerivedInverseImage.{u, 0} p').mapIso (inverseImageSingleIso g A) ≪≫
    inverseImageSingleIso p' _

/-- The correction of the target of the base-changed edge map: `g'⁻¹` past the shift and past `U`,
the comparison of composite inverse images, and an automorphism `z`. -/
def edgeTargetIso (A : EtaleModules.{u, 0} (ZMod N) B)
    (z : (etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A) ≅
      (etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A)) :
    (etaleAbelianDerivedInverseImage.{u, 0} g').obj (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)))⟦((2 : ℕ) : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y' (ZMod N)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A))))⟦((2 : ℕ) : ℤ)⟧ :=
  ((etaleAbelianDerivedInverseImage.{u, 0} g').commShiftIso ((2 : ℕ) : ℤ)).app _ ≪≫
    (shiftFunctor _ ((2 : ℕ) : ℤ)).mapIso (inverseImageSingleIso g' _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((etaleModuleUnderlyingAbelian Y' (ZMod N)).mapIso (moduleSquareIsoApp g' p g p' h A)) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((etaleModuleUnderlyingAbelian Y' (ZMod N)).mapIso z.symm))

include h in
/-- **The edge map under base change.** For a commutative square `g' ≫ p = p' ≫ g` and `A` with
flat fibres, `g⁻¹` of the edge map of `c` at `A`, followed by the base change map and a
correction of the target, is the edge map of `g'⁻¹ c` at `g⁻¹ A`. -/
theorem exists_edgeHom_baseChange (A : EtaleModules.{u, 0} (ZMod N) B) (hA : FlatFibres A) :
    ∃ z, (etaleAbelianDerivedInverseImage.{u, 0} g).map (edgeHom p c A (hA.inverseImage p)) ≫
        (etaleAbelianDerivedBaseChange.{u, 0} p g g' p' ((rfl : g' ≫ p = g' ≫ p).symm.trans h)).app
          _ ≫ (etaleAbelianDerivedDirectImage.{u, 0} p').map (edgeTargetIso g' p g p' h A z).hom =
      (inverseImageSingleIso g A).hom ≫
        edgeHom p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p') := by
  let ζ := (squareSingleIsoDirect g p' A).inv ≫ (squareSingleIsoAround g' p g p' h A).hom
  let z := (Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful Y' N).preimageIso
    ((DerivedCategory.singleFunctor _ 0).preimageIso (asIso ζ))
  have hz : (DerivedCategory.singleFunctor _ 0).map
      ((etaleModuleUnderlyingAbelian Y' (ZMod N)).map z.hom) = ζ := by
    simp [z]
  refine ⟨z, ?_⟩
  have hF : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A) := hA.inverseImage p
  have hM : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A)) := (hA.inverseImage g).inverseImage p'
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, 0} p g g' p' (g' ≫ p) rfl h, edgeHom, edgeHom,
    ← Category.assoc, CategoryTheory.map_homEquiv_comp_mateEquiv_app,
    ← Adjunction.homEquiv_naturality_right]
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_left (etaleAbelianDerivedAdjunction.{u, 0} p')
    (inverseImageSingleIso g A).hom _)
  congr 1
  have hAround : ∀ {W} (k : (DerivedCategory.singleFunctor _ 0).obj
      ((etaleModuleUnderlyingAbelian Y' (ZMod N)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p').obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj A))) ⟶ W),
      (etaleAbelianDerivedSquare.{u, 0} p g g' p' (g' ≫ p) rfl h).app _ ≫
        (etaleAbelianDerivedInverseImage.{u, 0} g').map (inverseImageSingleIso p A).hom ≫
          (inverseImageSingleIso g' _).hom ≫ (DerivedCategory.singleFunctor _ 0).map
            ((etaleModuleUnderlyingAbelian Y' (ZMod N)).map
              (moduleSquareIsoApp g' p g p' h A).hom) ≫ k =
      (squareSingleIsoDirect g p' A).hom ≫ (DerivedCategory.singleFunctor _ 0).map
        ((etaleModuleUnderlyingAbelian Y' (ZMod N)).map z.hom) ≫ k := by
    intro W k
    rw [hz]
    simp only [ζ, Iso.hom_inv_id_assoc, squareSingleIsoAround, etaleAbelianDerivedSquare,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      TwoSquare.mk, NatTrans.comp_app]
  simp only [edgeTargetIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.symm_hom]
  rw [reassoc_of% inverseImage_classHom g' c _ hF,
    ← reassoc_of% classHom_naturality (pullClass g' c) (hF.inverseImage g') hM
      (moduleSquareIsoApp g' p g p' h A).hom,
    hAround, reassoc_of% classHom_naturality (pullClass g' c) hM hM z.hom]
  simp only [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id,
    squareSingleIsoDirect, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]

/-- The shifted sheaf `U F[0]⟦2⟧` of a sheaf of `ℤ/N`-modules has torsion cohomology sheaves. -/
theorem torsionCohomologyProperty_shift_single (hN : N ≠ 0) {Z : Scheme.{u}}
    (F : EtaleModules.{u, 0} (ZMod N) Z) :
    Stacks.Torsion.torsionCohomologyProperty.{u + 1} Z.smallEtaleTopology
      (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Z (ZMod N)).obj F))⟦((2 : ℕ) : ℤ)⟧) := by
  have h := Stacks.Torsion.torsionCohomologyProperty_singleFunctor
    (hF := torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero (ZMod N) N
      (Nat.pos_of_ne_zero hN) (ZMod.natCast_self N) F)
  intro i
  exact (Stacks.Torsion.torsionSheafProperty.{u + 1} Z.smallEtaleTopology).prop_of_iso
    ((((DerivedCategory.homologyFunctor _ 0).shiftIso ((2 : ℕ) : ℤ) i (2 + i) rfl).app _).symm)
    (h (2 + i))

include h in
/-- **The edge map is invertible after base change when the base-changed edge map is**: for a
cartesian square with `p` proper and `A` with flat fibres, `g⁻¹ Θ_A` is invertible as soon as
the edge map of `g'⁻¹ c` at `g⁻¹ A` is (proper base change, Tag 0DDE). -/
theorem isIso_inverseImage_edge [IsProper p] (hN : N ≠ 0) (sq : IsPullback g' p' p g)
    (A : EtaleModules.{u, 0} (ZMod N) B) (hA : FlatFibres A)
    (hA' : IsIso (edge p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p'))) :
    IsIso ((etaleAbelianInverseImage.{u, 0} g).map (edge p c A (hA.inverseImage p))) := by
  obtain ⟨z, hz⟩ := exists_edgeHom_baseChange g' c p g p' h A hA
  have : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} p g g' p'
      ((rfl : g' ≫ p = g' ≫ p).symm.trans h)).app (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)))⟦((2 : ℕ) : ℤ)⟧)) :=
    isIso_etaleAbelianDerivedBaseChange_of_isProper p sq _ (-2)
      (DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega))
      (torsionCohomologyProperty_shift_single hN _)
  -- `H⁰` of the base-changed derived edge map is invertible
  have h1 : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (edgeHom p' (pullClass g' c) _ ((hA.inverseImage g).inverseImage p'))) := by
    unfold edge at hA'
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hA'
  have h2 := congrArg (DerivedCategory.homologyFunctor _ 0).map hz
  simp only [Functor.map_comp] at h2
  have h3 : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((etaleAbelianDerivedInverseImage.{u, 0} g).map (edgeHom p c A (hA.inverseImage p)))) := by
    have : IsIso ((DerivedCategory.homologyFunctor _ 0).map
        ((etaleAbelianDerivedInverseImage.{u, 0} g).map (edgeHom p c A (hA.inverseImage p))) ≫
        (DerivedCategory.homologyFunctor _ 0).map ((etaleAbelianDerivedBaseChange.{u, 0} p g g' p'
          ((rfl : g' ≫ p = g' ≫ p).symm.trans h)).app _) ≫
        (DerivedCategory.homologyFunctor _ 0).map ((etaleAbelianDerivedDirectImage.{u, 0} p').map
          (edgeTargetIso g' p g p' h A z).hom)) := by
      rw [h2]
      infer_instance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  -- `g⁻¹ ∘ H⁰ ≅ H⁰ ∘ g⁻¹`
  have hnat := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (etaleAbelianInverseImage.{u, 0} g) 0).hom.naturality (edgeHom p c A (hA.inverseImage p))
  simp only [Functor.comp_map] at hnat
  have h4 : IsIso ((etaleAbelianInverseImage.{u, 0} g).map
      ((DerivedCategory.homologyFunctor _ 0).map (edgeHom p c A (hA.inverseImage p)))) :=
    IsIso.of_isIso_fac_left hnat.symm
  have := IsIso.comp_isIso (f := (etaleAbelianInverseImage.{u, 0} g).map
      (singleHomologyZeroIso ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A)).hom)
    (h := (etaleAbelianInverseImage.{u, 0} g).map
      ((DerivedCategory.homologyFunctor _ 0).map (edgeHom p c A (hA.inverseImage p))))
  rwa [← Functor.map_comp] at this

end Square

end Stacks.EtaleCohomology.TopTrace
