module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentConservative
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.Homology.CyclesShortComplex

/-!
# The left derived lower shriek of modules from a simplicial component, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Lower shriek `g_{n!} : Mod(O_n) ⥤ Mod(O)` from the degree-`n` component is exact when
the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are flat (Stacks 0D74), and then it induces a
functor of derived categories directly. Without flatness it is only right exact, and this file
constructs its total left derived functor `Lg_{n!} : D(O_n) ⥤ D(O)`, left adjoint to the derived
restriction `g_n^* : D(O) ⥤ D(O_n)`, with no hypothesis on `O`.

The resolving class is that of the K-flat complexes with flat terms (Stacks 06YS). The input is
that `g_{n!}` keeps the cycles sequences of an acyclic such complex short exact: the restriction
of `g_{n!}` to a degree `m` is the finite direct sum over `φ : [n] ⟶ [m]` of the transition
pullbacks `f_φ^*` (Stacks 0D72 (6)), each of which keeps a short exact sequence with flat third
term short exact (Stacks 0G6R), and the restrictions to the degrees detect monomorphisms.

## Main definitions

* `SimplicialSiteSituation.componentModulesLowerShriek`: `g_{n!}` between the module categories
  of the component and total ringed topoi.
* `SimplicialSiteSituation.componentModuleLowerShriekLeftDerived`: `Lg_{n!}`.
* `SimplicialSiteSituation.componentModuleLowerShriekLeftDerivedAdjunction`: the adjunction
  `Lg_{n!} ⊣ g_n^*` on unbounded derived categories.

## Main results

* `Functor.mono_map_of_iso_biproduct`: a functor presented as a finite direct sum of functors
  carries a morphism to a monomorphism when every summand does.
* `SimplicialSiteSituation.componentModulesLowerShriek_invertsQuasiIso`: `g_{n!}` inverts the
  quasi-isomorphisms between K-flat complexes with flat terms.
* `SimplicialSiteSituation.isIso_componentModuleLowerShriekLeftDerivedComparison_app`: `Lg_{n!}`
  is computed degreewise on K-flat complexes with flat terms.
* `SimplicialSiteSituation.componentModuleLowerShriekLeftDerivedAdjunction_unit_fac`: the unit
  of the derived adjunction is induced by the unit of `g_{n!} ⊣ g_n^*`.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.Functor

/-- **A functor presented as a finite direct sum carries a morphism to a monomorphism as soon as
every summand does.** If `G ≅ ⨁ F` and each `F i` carries `u` to a monomorphism, then so does
`G`: a map `h` with `h ≫ G.map u = 0` has every projection `h ≫ π_i` killed by the monomorphism
`F_i.map u`, and `h` is the sum of those projections followed by the inclusions. -/
theorem mono_map_of_iso_biproduct {A B : Type*} [Category* A] [Category* B] [Preadditive B]
    {ι : Type} [Fintype ι] {G : A ⥤ B} {F : ι → A ⥤ B} [HasBiproduct F] (e : G ≅ ⨁ F)
    {X Y : A} (u : X ⟶ Y) (hu : ∀ i, Mono ((F i).map u)) : Mono (G.map u) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} h hh => ?_
  have key : ∀ i, h ≫ (e.hom ≫ biproduct.π F i).app X = 0 := fun i => by
    have := hu i
    rw [← cancel_mono ((F i).map u), Category.assoc, ← NatTrans.naturality,
      ← Category.assoc, hh, zero_comp, zero_comp]
  have htot : h = ∑ i, (h ≫ (e.hom ≫ biproduct.π F i).app X) ≫
      (biproduct.ι F i ≫ e.inv).app X := by
    calc h = h ≫ (e.hom ≫ (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ e.inv).app X := by
          rw [biproduct.total, Category.id_comp, e.hom_inv_id, NatTrans.id_app, Category.comp_id]
      _ = _ := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, NatTrans.comp_app,
            NatTrans.app_sum, Category.assoc]
  rw [htot]
  exact Finset.sum_eq_zero fun i _ => by rw [key i, zero_comp]

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- Lower shriek `g_{n!}` of sheaves of modules from the degree-`n` component, read between the
modules of the component and the total ringed topoi. -/
abbrev componentModulesLowerShriek (n : SimplexCategory) :
    (S.componentRingedTopos O n).Modules ⥤ (S.totalRingedTopos O).Modules :=
  S.componentModuleLowerShriek (S.totalRingSheaf O) n

/-- The adjunction `g_{n!} ⊣ g_n^*` of Stacks 0D72, read between the modules of the component and
the total ringed topoi. -/
def componentModulesLowerShriekAdjunction (n : SimplexCategory) :
    S.componentModulesLowerShriek O n ⊣ S.componentModulesRestriction O n :=
  S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n

/-- Lower shriek `g_{n!}` from the degree-`n` component is additive. -/
instance componentModulesLowerShriek_additive (n : SimplexCategory) :
    (S.componentModulesLowerShriek O n).Additive :=
  (S.componentModulesLowerShriekAdjunction O n).left_adjoint_additive

/-- Lower shriek `g_{n!}` from the degree-`n` component preserves finite colimits. -/
instance componentModulesLowerShriek_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (S.componentModulesLowerShriek O n) :=
  letI : PreservesColimitsOfSize.{0, 0} (S.componentModulesLowerShriek O n) :=
    (S.componentModulesLowerShriekAdjunction O n).leftAdjoint_preservesColimits
  inferInstance

/-- **`g_{n!}` carries a morphism to a monomorphism when every transition pullback out of degree
`n` does.** The restriction of `g_{n!}` to a degree `m` is the direct sum of the transition
pullbacks along the simplex maps `[n] ⟶ [m]` (Stacks 0D72 (6)), and the restrictions to the
degrees detect monomorphisms. -/
theorem mono_componentModulesLowerShriek_map (n : SimplexCategory)
    {M N : (S.componentRingedTopos O n).Modules} (v : M ⟶ N)
    (hv : ∀ (m : SimplexCategory) (φ : n ⟶ m), Mono ((S.transitionPullbackModules' O φ).map v)) :
    Mono ((S.componentModulesLowerShriek O n).map v) := by
  refine (mono_iff_forall_mono_componentModuleRestriction S (S.totalRingSheaf O) _).2
    fun m => ?_
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) m)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact Functor.mono_map_of_iso_biproduct (S.moduleSumFormulaBiproduct O n m) v (hv m)

/-- **`g_{n!}` keeps a short exact sequence with flat third term short exact.** It is right
exact, being a left adjoint, so it keeps the cokernel; and the transition pullbacks keep the
first map a monomorphism by Stacks 0G6R, which `g_{n!}` inherits. -/
theorem shortExact_map_componentModulesLowerShriek (n : SimplexCategory)
    (T : ShortComplex (S.componentRingedTopos O n).Modules) (hT : T.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.componentRingedTopos O n).O) T.X₃) :
    (T.map (S.componentModulesLowerShriek O n)).ShortExact := by
  have : Mono (T.map (S.componentModulesLowerShriek O n)).f :=
    S.mono_componentModulesLowerShriek_map O n T.f fun m φ =>
      (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.shortExact_map_pullbackModules
        (S.transitionRingedToposHom O φ) T hT hflat).mono_f
  have : Epi ((S.componentModulesLowerShriek O n).map T.g) := by
    have := hT.epi_g
    infer_instance
  have : Epi (T.map (S.componentModulesLowerShriek O n)).g := ‹_›
  exact ⟨ShortComplex.exact_of_g_is_cokernel _
    (Limits.isColimitCoforkMapOfIsColimit' (S.componentModulesLowerShriek O n) T.zero
      hT.gIsCokernel)⟩

/-- **`g_{n!}` carries an acyclic K-flat complex with flat terms to an acyclic complex.** Its
cycles are flat by Stacks 0G7C, so `g_{n!}` keeps its cycles sequences short exact, and a complex
whose cycles sequences stay short exact has acyclic image. -/
theorem acyclic_componentModulesLowerShriek_mapHomologicalComplex (n : SimplexCategory)
    (K : CochainComplex (S.componentRingedTopos O n).Modules ℤ)
    (hK : S.componentKFlat O n ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (hKac : K.Acyclic) :
    (((S.componentModulesLowerShriek O n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K).Acyclic := by
  have : ∀ K₁ K₂ : CochainComplex (S.componentRingedTopos O n).Modules ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
        (ComplexShape.up ℤ) :=
    fun K₁ K₂ => Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u}
      (S.componentRingedTopos O n).O K₁ K₂
  exact CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact _ K fun _ j hij =>
    S.shortExact_map_componentModulesLowerShriek O n _
      (HomologicalComplex.cyclesShortComplex_shortExact K hij (hKac j))
      (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat (S.componentRingedTopos O n) K
        hKac ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor
          (S.componentRingedTopos O n).O K).2 hK.1) hK.2 j)

/-- A morphism in the homotopy category is a quasi-isomorphism iff the third vertex of a
distinguished triangle on it is acyclic. -/
private theorem quasiIso_iff_mem_subcategoryAcyclic {C : Type*} [Category* C] [Abelian C]
    (T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    HomotopyCategory.quasiIso C (ComplexShape.up ℤ) T.mor₁ ↔
      HomotopyCategory.subcategoryAcyclic C T.obj₃ := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _ hT

/-- **`g_{n!}` inverts the quasi-isomorphisms between K-flat complexes with flat terms.** The
cone of such a quasi-isomorphism is acyclic and again K-flat with flat terms, so its image under
`g_{n!}` is acyclic, and the conclusion is read off the image of the mapping-cone triangle under
the triangulated functor `K(g_{n!})`. -/
theorem componentModulesLowerShriek_invertsQuasiIso (n : SimplexCategory)
    {K M : HomotopyCategory (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ)}
    (s : K ⟶ M) (hs : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) s)
    (hK : S.componentKFlat O n K) (hM : S.componentKFlat O n M) :
    IsIso (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).map s) := by
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨M₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : K₀ ⟶ M₀,
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀ = s :=
    ⟨Quot.out s, HomotopyCategory.quotient_map_out s⟩
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished s₀
  have hacyc : (CochainComplex.mappingCone s₀).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact (quasiIso_iff_mem_subcategoryAcyclic _ hT).1 hs
  have himage := S.acyclic_componentModulesLowerShriek_mapHomologicalComplex O n _
    (Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone s₀ hK hM) hacyc
  have hFT := ((S.componentModulesLowerShriek O n).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_distinguished _ hT
  have h3 : HomotopyCategory.subcategoryAcyclic (S.totalRingedTopos O).Modules
      (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone s₀))) :=
    ObjectProperty.prop_of_iso _
      ((((S.componentModulesLowerShriek O n).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app (CochainComplex.mappingCone s₀)).symm)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 himage)
  have hq : HomotopyCategory.quasiIso (S.totalRingedTopos O).Modules (ComplexShape.up ℤ)
      (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀)) := by
    exact (quasiIso_iff_mem_subcategoryAcyclic _ hFT).2 h3
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso (S.totalRingedTopos O).Modules (ComplexShape.up ℤ)) _ hq

/-- Degreewise `g_{n!}` followed by localization has a pointwise left derived functor: the
K-flat complexes with flat terms resolve every complex and their quasi-isomorphisms are
inverted. -/
theorem componentModulesLowerShriek_hasPointwiseLeftDerivedFunctor (n : SimplexCategory) :
    ((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions _
    (S.componentKFlat O n) (S.hasResolutions_componentKFlat O n) _
    (S.componentModulesLowerShriek_invertsQuasiIso O n)

/-- **The left derived lower shriek `Lg_{n!} : D(O_n) ⥤ D(O)`**, with no flatness hypothesis:
the total left derived functor of degreewise `g_{n!}` followed by localization. -/
def componentModuleLowerShriekLeftDerived (n : SimplexCategory) :
    DerivedCategory (S.componentRingedTopos O n).Modules ⥤
      DerivedCategory (S.totalRingedTopos O).Modules :=
  letI := S.componentModulesLowerShriek_hasPointwiseLeftDerivedFunctor O n
  ((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))

/-- The canonical comparison `Lg_{n!} ⟶ g_{n!}` from the left derived lower shriek to degreewise
lower shriek. -/
def componentModuleLowerShriekLeftDerivedComparison (n : SimplexCategory) :
    DerivedCategory.Qh ⋙ S.componentModuleLowerShriekLeftDerived O n ⟶
      (S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  letI := S.componentModulesLowerShriek_hasPointwiseLeftDerivedFunctor O n
  ((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))

/-- `Lg_{n!}`, with the comparison `Lg_{n!} ⟶ g_{n!}`, is a left derived functor of degreewise
`g_{n!}` followed by localization with respect to the quasi-isomorphisms. -/
instance isLeftDerivedFunctor_componentModuleLowerShriekLeftDerived (n : SimplexCategory) :
    (S.componentModuleLowerShriekLeftDerived O n).IsLeftDerivedFunctor
      (S.componentModuleLowerShriekLeftDerivedComparison O n)
      (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ)) := by
  let := S.componentModulesLowerShriek_hasPointwiseLeftDerivedFunctor O n
  delta componentModuleLowerShriekLeftDerived componentModuleLowerShriekLeftDerivedComparison
  infer_instance

/-- **`Lg_{n!}` is computed degreewise on K-flat complexes with flat terms.** -/
theorem isIso_componentModuleLowerShriekLeftDerivedComparison_app (n : SimplexCategory)
    (K : HomotopyCategory (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))
    (hK : S.componentKFlat O n K) :
    IsIso ((S.componentModuleLowerShriekLeftDerivedComparison O n).app K) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions _ (S.componentKFlat O n)
    (S.hasResolutions_componentKFlat O n) _
    (S.componentModulesLowerShriek_invertsQuasiIso O n)
    DerivedCategory.Qh _ _ K hK

/-- **The derived adjunction `Lg_{n!} ⊣ g_n^*`**, with no flatness hypothesis. Restriction to a
component is exact, and `Lg_{n!}` is computed by resolutions, so the adjunction `g_{n!} ⊣ g_n^*`
of Stacks 0D72 descends to the unbounded derived categories. -/
def componentModuleLowerShriekLeftDerivedAdjunction (n : SimplexCategory) :
    S.componentModuleLowerShriekLeftDerived O n ⊣ S.derivedComponentModuleRestriction O n :=
  Adjunction.derivedMapDerivedCategoryOfResolutions (S.componentModulesLowerShriekAdjunction O n)
    (S.componentKFlat O n) (S.hasResolutions_componentKFlat O n)
    (fun s hs hK hM => S.componentModulesLowerShriek_invertsQuasiIso O n s hs hK hM)

/-- **The unit of `Lg_{n!} ⊣ g_n^*` is induced by the unit of `g_{n!} ⊣ g_n^*`**: at the image of
a complex `M`, followed by `g_n^*` of the comparison of `Lg_{n!}`, it is the image of the
degreewise unit followed by the comparison of the derived restriction. -/
theorem componentModuleLowerShriekLeftDerivedAdjunction_unit_fac (n : SimplexCategory)
    (M : HomotopyCategory (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ)) :
    (S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app (DerivedCategory.Qh.obj M) ≫
        (S.derivedComponentModuleRestriction O n).map
          ((S.componentModuleLowerShriekLeftDerivedComparison O n).app M) =
      DerivedCategory.Qh.map
          (((S.componentModulesLowerShriekAdjunction O n).mapHomotopyCategoryAdjunction
            (ComplexShape.up ℤ)).unit.app M) ≫
        (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.inv.app
          (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  let := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (S.componentModulesRestriction O n)
  let := Functor.isRightDerivedFunctor_mapDerivedCategory_comp_of_exact
    (S.componentModulesRestriction O n) (S.componentModuleLowerShriekLeftDerived O n)
  let := LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions
    (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))
    (S.componentKFlat O n) (S.hasResolutions_componentKFlat O n)
    ((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (S.componentModulesLowerShriek_invertsQuasiIso O n)
    DerivedCategory.Qh _ (S.componentModuleLowerShriekLeftDerivedComparison O n)
    (S.componentModulesRestriction O n).mapDerivedCategory
  ((S.componentModulesLowerShriekAdjunction O n).mapHomotopyCategoryAdjunction
    (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (S.componentRingedTopos O n).Modules (ComplexShape.up ℤ))
    (S.componentModuleLowerShriekLeftDerivedComparison O n)
    (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.inv M

end CategoryTheory.SimplicialSiteSituation

end
