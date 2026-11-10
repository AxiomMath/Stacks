module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.PowerTorsionGlobalSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.Perfect.PowerTorsionAffineSheaf

/-!
# Power-torsion morphism groups and restriction along an open immersion of schemes

Let `g : X ⟶ Y` be an open immersion of schemes and let `f ∈ Γ(Y, 𝒪_Y)`. The derived restriction
functor `Stacks.Duality.OpenImmersion.derivedRestrict g` is semilinear for the pair of scalars `f`
and `g^*f`: `(f • φ)|_X = (g^*f) • (φ|_X)`. Consequently power torsion of morphism groups in the
derived category can be transported along an isomorphism of schemes.

## Main results

* `Stacks.DerivedQCoh.derivedRestrict_map_globalScalar_smul`: derived restriction along an
  open immersion of schemes is semilinear over `g^* : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.
* `Stacks.DerivedQCoh.homPowerTorsion_of_derivedRestrict`: if every morphism out of the shifted
  restriction of `E` along an isomorphism of schemes into the restriction of `F` is killed by a
  power of the restricted section, then every morphism `E⟦n⟧ ⟶ F` is killed by a power of `f`.
* `Stacks.Koszul.PowerLift.HomPowerTorsion.of_iso_target`: the property only depends on the
  isomorphism class of the target.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08EF](https://stacks.math.columbia.edu/tag/08EF)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SiteModules
open Stacks.ExtensionByZero
open Stacks.Duality.OpenImmersion (derivedRestrict)
open scoped IsMulCommutative

universe u

namespace Stacks.Koszul.PowerLift

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]

/-- Power torsion of the morphisms from `X` to `E` only depends on the isomorphism class of
`E`. -/
public theorem HomPowerTorsion.of_iso_target {g : R} {X E E' : C} (e : E ≅ E')
    (h : HomPowerTorsion g X E) : HomPowerTorsion g X E' := by
  intro φ
  obtain ⟨k, hk⟩ := h (φ ≫ e.inv)
  refine ⟨k, (cancel_mono e.inv).1 ?_⟩
  rw [Linear.smul_comp, hk, zero_comp]

end Stacks.Koszul.PowerLift

namespace Stacks.DerivedQCoh

open Stacks.Koszul.PowerLift

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictFunctor

/-- Equal scalars act equally. -/
private theorem smul_congr_scalar {R : Type*} [Ring R] (M : Type*) [AddCommGroup M]
    [Module R M] {r s : R} (h : r = s) (x : M) : r • x = s • x := by rw [h]

/-! ### The scalar: restriction of a global section along an open immersion -/

/-- Restricting a section of `𝒪_Y` over the whole space to the image `g(V)` of an open of `X`
and then transporting it to `Γ(X, V)` is restricting its pullback `g^*f` to `V`. -/
public theorem map_top_comp_appIso_hom {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (V : X.Opens) :
    Y.presheaf.map (isTerminalTop.from (g ''ᵁ V)).op ≫ (g.appIso V).hom =
      g.appTop ≫ X.presheaf.map (isTerminalTop.from V).op := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

/-- The global scalar of `f` read over the image `g(V)` is the global scalar of `g^*f` read over
`V`, transported along `(g.appIso V).inv`. -/
public theorem globalScalar_val_image {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (f : Γ(Y, ⊤)) (V : X.Opens) :
    (globalScalar Y.ringCatSheaf f).val (op (g ''ᵁ V)) =
      (g.appIso V).inv ((globalScalar X.ringCatSheaf (g.appTop f)).val (op V)) := by
  have h : (g.appIso V).hom (Y.presheaf.map (isTerminalTop.from (g ''ᵁ V)).op f) =
      X.presheaf.map (isTerminalTop.from V).op (g.appTop f) := by
    rw [← CommRingCat.comp_apply, map_top_comp_appIso_hom g V, CommRingCat.comp_apply]
  change Y.presheaf.map (isTerminalTop.from (g ''ᵁ V)).op f =
    (g.appIso V).inv (X.presheaf.map (isTerminalTop.from V).op (g.appTop f))
  rw [← h, ← CommRingCat.comp_apply, (g.appIso V).hom_inv_id, CommRingCat.id_apply]

/-! ### Semilinearity, on modules and then on the derived category -/

/-- Restriction of modules along an open immersion is semilinear at a global scalar:
restricting multiplication by `f` is multiplication by `g^*f`. -/
public theorem restrictFunctor_map_globalSmul {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (f : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor g).map
        (globalSmul Y.ringCatSheaf (globalScalar Y.ringCatSheaf f) M) =
      globalSmul X.ringCatSheaf (globalScalar X.ringCatSheaf (g.appTop f))
        ((Scheme.Modules.restrictFunctor g).obj M) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  exact smul_congr_scalar
    ↥((show SheafOfModules.{u} Y.ringCatSheaf from M).val.obj (op (g ''ᵁ V)))
    (globalScalar_val_image g f V) m

/-- `Stacks.DerivedQCoh.restrictFunctor_map_globalSmul` written with scalar endomorphisms. -/
public theorem restrictFunctor_map_globalScalar_smul_id {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (f : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor g).map (globalScalar Y.ringCatSheaf f • 𝟙 M) =
      globalScalar X.ringCatSheaf (g.appTop f) •
        𝟙 ((Scheme.Modules.restrictFunctor g).obj M) := by
  have h₁ : globalScalar Y.ringCatSheaf f • 𝟙 M =
      globalSmul Y.ringCatSheaf (globalScalar Y.ringCatSheaf f) M :=
    (globalSmul_eq_smul_id Y.ringCatSheaf (globalScalar Y.ringCatSheaf f) M).symm
  have h₂ : globalSmul X.ringCatSheaf (globalScalar X.ringCatSheaf (g.appTop f))
      ((Scheme.Modules.restrictFunctor g).obj M) =
      globalScalar X.ringCatSheaf (g.appTop f) •
        𝟙 ((Scheme.Modules.restrictFunctor g).obj M) :=
    globalSmul_eq_smul_id X.ringCatSheaf (globalScalar X.ringCatSheaf (g.appTop f))
      ((Scheme.Modules.restrictFunctor g).obj M)
  rw [h₁, restrictFunctor_map_globalSmul, h₂]

/-- Restriction along an open immersion is semilinear degreewise on complexes. -/
public theorem mapHomologicalComplex_restrictFunctor_globalScalar_smul_id {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] (f : Γ(Y, ⊤)) (K : CochainComplex Y.Modules ℤ) :
    ((Scheme.Modules.restrictFunctor g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (globalScalar Y.ringCatSheaf f • 𝟙 K) =
      globalScalar X.ringCatSheaf (g.appTop f) • 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun i => by
    simpa using restrictFunctor_map_globalScalar_smul_id g f (K.X i)

/-- Derived restriction takes the scalar endomorphism of an object in the image of the
localization functor to the scalar endomorphism of the pulled-back section. -/
public theorem derivedRestrict_map_globalScalar_smul_id_Q {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (f : Γ(Y, ⊤)) (K : CochainComplex Y.Modules ℤ) :
    (derivedRestrict g).map (globalScalar Y.ringCatSheaf f • 𝟙 (DerivedCategory.Q.obj K)) =
      globalScalar X.ringCatSheaf (g.appTop f) •
        𝟙 ((derivedRestrict g).obj (DerivedCategory.Q.obj K)) := by
  have hQ1 : DerivedCategory.Q.map (globalScalar Y.ringCatSheaf f • 𝟙 K) =
      globalScalar Y.ringCatSheaf f • 𝟙 (DerivedCategory.Q.obj K) := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  have hQ2 : DerivedCategory.Q.map (globalScalar X.ringCatSheaf (g.appTop f) •
      𝟙 (((Scheme.Modules.restrictFunctor g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) =
      globalScalar X.ringCatSheaf (g.appTop f) • 𝟙 _ := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  have hnat := (Scheme.Modules.restrictFunctor g).mapDerivedCategoryFactors_hom_naturality
    (globalScalar Y.ringCatSheaf f • 𝟙 K)
  rw [mapHomologicalComplex_restrictFunctor_globalScalar_smul_id, hQ1, hQ2,
    Linear.comp_smul] at hnat
  refine (cancel_mono
    ((Scheme.Modules.restrictFunctor g).mapDerivedCategoryFactors.hom.app K)).1 ?_
  rw [hnat, Linear.smul_comp, Category.id_comp]
  exact congrArg (fun z => globalScalar X.ringCatSheaf (g.appTop f) • z) (Category.comp_id _)

/-- Derived restriction takes the scalar endomorphism of any object to the scalar endomorphism
of the pulled-back section. -/
public theorem derivedRestrict_map_globalScalar_smul_id {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (f : Γ(Y, ⊤)) (M : DerivedCategory Y.Modules) :
    (derivedRestrict g).map (globalScalar Y.ringCatSheaf f • 𝟙 M) =
      globalScalar X.ringCatSheaf (g.appTop f) • 𝟙 ((derivedRestrict g).obj M) := by
  let e := DerivedCategory.Q.objObjPreimageIso M
  rw [← smul_id_conj e, Functor.map_comp, Functor.map_comp,
    derivedRestrict_map_globalScalar_smul_id_Q]
  exact smul_id_conj ((derivedRestrict g).mapIso e) _

/-- Derived restriction along an open immersion of schemes is semilinear over the pullback
map `g^* : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` on global sections: `(f • φ)|_X = (g^*f) • (φ|_X)`. -/
public theorem derivedRestrict_map_globalScalar_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (f : Γ(Y, ⊤)) {M N : DerivedCategory Y.Modules} (φ : M ⟶ N) :
    (derivedRestrict g).map (globalScalar Y.ringCatSheaf f • φ) =
      globalScalar X.ringCatSheaf (g.appTop f) • (derivedRestrict g).map φ := by
  have := derivedRestrict_map_globalScalar_smul_id g f M =≫ (derivedRestrict g).map φ
  rwa [← Functor.map_comp, Linear.smul_comp, Linear.smul_comp, Category.id_comp,
    Category.id_comp] at this

/-! ### Transport of power torsion along an isomorphism of schemes -/

/-- Let `e : A ≅ B` be an isomorphism of schemes, `f` a section of `𝒪_A` over the whole space
and `E`, `F` objects of `D(𝒪_A)`. If on `B` every morphism from the `n`-th shift of the
restriction of `E` into the restriction of `F` is annihilated by a power of the restricted section
`e.inv^*f`, then on `A` every morphism `E⟦n⟧ ⟶ F` is annihilated by a power of `f`. -/
public theorem homPowerTorsion_of_derivedRestrict {A B : Scheme.{u}} (e : A ≅ B)
    (f : Γ(A, ⊤)) (E F : DerivedCategory A.Modules) (n : ℤ)
    (h : HomPowerTorsion (globalScalar B.ringCatSheaf (e.inv.appTop f))
      (((derivedRestrict e.inv).obj E)⟦n⟧) ((derivedRestrict e.inv).obj F)) :
    HomPowerTorsion (globalScalar A.ringCatSheaf f) (E⟦n⟧) F := by
  have := derivedRestrict_faithful e
  intro φ
  obtain ⟨k, hk⟩ := h ((((derivedRestrict e.inv).commShiftIso n).app E).inv ≫
    (derivedRestrict e.inv).map φ)
  have hp : e.inv.appTop (f ^ k) = (e.inv.appTop f) ^ k := map_pow _ f k
  have hb : globalScalar B.ringCatSheaf (e.inv.appTop (f ^ k)) =
      globalScalar B.ringCatSheaf (e.inv.appTop f) ^ k :=
    (congrArg (globalScalar B.ringCatSheaf) hp).trans
      (globalScalar_pow B.ringCatSheaf (e.inv.appTop f) k)
  have hzero : globalScalar B.ringCatSheaf (e.inv.appTop (f ^ k)) •
      (derivedRestrict e.inv).map φ = 0 := by
    refine (cancel_epi ((((derivedRestrict e.inv).commShiftIso n).app E).inv)).1
      (Eq.trans ?_ comp_zero.symm)
    refine (Linear.comp_smul _ _ _ _ _ _).trans ?_
    exact (congrArg (fun s => s • ((((derivedRestrict e.inv).commShiftIso n).app E).inv ≫
      (derivedRestrict e.inv).map φ)) hb).trans hk
  refine ⟨k, (derivedRestrict e.inv).map_injective ?_⟩
  calc (derivedRestrict e.inv).map (globalScalar A.ringCatSheaf f ^ k • φ)
      = (derivedRestrict e.inv).map (globalScalar A.ringCatSheaf (f ^ k) • φ) :=
        congrArg (derivedRestrict e.inv).map
          (congrArg (fun s => s • φ) (globalScalar_pow A.ringCatSheaf f k).symm)
    _ = globalScalar B.ringCatSheaf (e.inv.appTop (f ^ k)) • (derivedRestrict e.inv).map φ :=
        derivedRestrict_map_globalScalar_smul e.inv (f ^ k) φ
    _ = 0 := hzero
    _ = (derivedRestrict e.inv).map 0 := (CategoryTheory.Functor.map_zero _ _ _).symm

/-! ### Examples at `Spec ℤ` -/

section Witness

private abbrev specInt : Scheme.{0} := Spec (CommRingCat.of ℤ)

private abbrev unitSingle : DerivedCategory specInt.Modules :=
  (DerivedCategory.singleFunctor specInt.Modules 0).obj
    (SheafOfModules.unit specInt.ringCatSheaf)

example :
    (derivedRestrict (𝟙 specInt)).map (globalScalar specInt.ringCatSheaf 2 • 𝟙 unitSingle) =
      globalScalar specInt.ringCatSheaf ((𝟙 specInt : specInt ⟶ specInt).appTop 2) •
        (derivedRestrict (𝟙 specInt)).map (𝟙 unitSingle) :=
  derivedRestrict_map_globalScalar_smul (𝟙 specInt) 2 (𝟙 unitSingle)

example :
    HomPowerTorsion (globalScalar specInt.ringCatSheaf 0) (unitSingle⟦(0 : ℤ)⟧) unitSingle :=
  homPowerTorsion_of_derivedRestrict (Iso.refl specInt) 0 unitSingle unitSingle 0
    (fun φ => ⟨1, by
      rw [pow_one, show globalScalar specInt.ringCatSheaf ((Iso.refl specInt).inv.appTop 0) = 0
        from map_zero (globalScalarHom specInt.ringCatSheaf), zero_smul]⟩)

end Witness

end Stacks.DerivedQCoh

end
