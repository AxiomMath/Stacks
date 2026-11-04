module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionAdjunctSquareDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionUnitor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleLiftConstruction

/-!
# Lifting a morphism of simplicial systems of derived modules (Stacks 0D9S)

Let `S` be a simplicial-site situation (Stacks 09WE) and let `O` be a sheaf of commutative rings
on its total site. Stacks 0D9S says that, over flat structure-sheaf transitions, a morphism
`{K_n ⟶ K'_n}` between the simplicial systems of the derived category of modules associated with
two objects `K`, `K'` of `D(O)` comes from a morphism `K ⟶ K'`, provided `K` is cartesian and
`Hom(K_i[i - 1], K'_i) = 0` for `i > 1`.

The source proves this exactly as the abelian Stacks 0D9K, using the Postnikov system of
Stacks 0D9Q in place of that of Stacks 0D9I, and the proof has two halves.

*The construction* produces a morphism `γ : K ⟶ K'` realising the given morphism in simplicial
degree zero. It runs through the Postnikov system of `- ⊗^L_O K` attached to a resolution of the
structure sheaf (Stacks 0D9B), the identification `Xₙ = g_{n!}Kₙ` of Stacks 0D9E (2) — where
flatness and cartesianness are spent — and the vanishing hypothesis, which lets a map out of the
bottom term `X₀` that is killed by the differential `X₁ ⟶ X₀` propagate up the tower. It is
`CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponentModuleRestriction_zero_eq`
below; the two computations the source omits are carried out in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleLiftConstruction.lean`.

*The identification of the components.* The source then says "since `K` is cartesian, this
easily gives that `{γ_n}` is the map of simplicial systems we started out with". That step is
`CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian`:
every simplicial degree is reached from degree zero by a vertex `⦋0⦌ ⟶ n`, along which the
transition of a cartesian system is invertible, so a morphism of systems out of a cartesian system
is determined by its degree-zero component.

## Main results

* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian`:
  a morphism of simplicial systems of the derived category of modules whose source is cartesian
  is determined by its component in degree zero.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSystemMap`: the morphism of associated
  simplicial systems induced by a morphism of `D(O)`.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_derivedComponentModuleRestriction_zero_eq`:
  the degree-zero realisation.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_of_cartesian`: **Stacks 0D9S**.

## Implementation notes

*The vertex is the constant map.* `SimplexCategory.const` supplies `⦋0⦌ ⟶ n` in every degree at
once, which is what makes the reduction to degree zero uniform; the same device is used in
`CategoryTheory.SimplicialSiteSituation.moduleSystem_naturality_of_vertex_compatibility`.

*Both cases of Situation 09WE at once.* The statement is made for an arbitrary
`CategoryTheory.SimplicialSiteSituation`, whose `case` field is the sum of the two cases. The
inputs that are proved case by case — the leg equation of Stacks 0D72 (6) and hence Stacks 0D9E (2)
— are available at that level as
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq` and
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`. The derived pullbacks
`Lf_φ^*` that the notion of a simplicial system is phrased in exist by the instance
`CategoryTheory.SimplicialSiteSituation.hasLeftDerivedFunctor_transitionPullbackOnHomotopy`, so no
hypothesis of that kind is carried.

## References

* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe v u


namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **A morphism of simplicial systems of the derived category of modules out of a cartesian
system is determined by its component in degree zero.** Every simplicial degree `n` carries a
vertex `ψ : ⦋0⦌ ⟶ n`, whose transition `T_ψ` is invertible because `T` is cartesian; the
naturality square of a morphism of systems against `ψ` then expresses its component in degree
`n` in terms of its component in degree zero. -/
theorem SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian
    {T V : SimplicialDerivedModuleSystem S O} (hT : T.Cartesian)
    (f g : SimplicialDerivedModuleSystem.Hom T V)
    (h₀ : f.app ⦋0⦌ = g.app ⦋0⦌) (n : SimplexCategory) : f.app n = g.app n := by
  have hψ : IsIso (T.map (SimplexCategory.const ⦋0⦌ n 0)) := hT _
  refine (cancel_epi (T.map (SimplexCategory.const ⦋0⦌ n 0))).1 ?_
  rw [f.naturality, g.naturality, h₀]

/-- The morphism of associated simplicial systems of the derived category of modules induced by
a morphism of `D(O)`: its component in degree `n` is the restriction `Lg_n^*γ`, and its
compatibility with the transitions is the naturality of the derived transition of Stacks 0D9P. -/
def derivedModuleSystemMap {K K' : DerivedCategory (S.totalRingedTopos O).Modules} (γ : K ⟶ K') :
    SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K') where
  app n := (S.derivedComponentModuleRestriction O n).map γ
  naturality φ := ((S.derivedComponentModuleTransition O φ).naturality γ).symm

/-- The vanishing of `E ≫ ε` in the first omitted computation, over abstract morphisms: the
counit transposes `θ` back to the projection map followed by `h`, the projection map cancels
against its inverse, and what is left is the differential followed by `h`. -/
private theorem comp_counit_eq_zero {D : Type*} [Category D] [Preadditive D]
    {X₁ T₀ X₀ G₀ F₀ K : D} (d : X₁ ⟶ T₀) (tc : T₀ ⟶ X₀) (einv : X₀ ⟶ G₀) (ehom : G₀ ⟶ X₀)
    (Fθ : G₀ ⟶ F₀) (ε : F₀ ⟶ K) (h : X₀ ⟶ K) (hc : Fθ ≫ ε = ehom ≫ h)
    (hi : einv ≫ ehom = 𝟙 X₀) (hz : d ≫ tc ≫ h = 0) :
    (d ≫ tc ≫ einv ≫ Fθ) ≫ ε = 0 := by
  rw [Category.assoc, Category.assoc, Category.assoc, hc, ← Category.assoc einv, hi,
    Category.id_comp, hz]

/-- The transpose of a vanishing composite, followed by a further map, is the transpose of
zero. -/
private theorem homEquiv_comp_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [G.PreservesZeroMorphisms]
    (adj : F ⊣ G) {X : C} {Y Z W : D} (x : F.obj X ⟶ Y) (y : Y ⟶ Z) (hx : x ≫ y = 0)
    (g : G.obj Z ⟶ G.obj W) : adj.homEquiv X Z (x ≫ y) ≫ g = adj.homEquiv X W 0 := by
  rw [hx, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, G.map_zero, G.map_zero, comp_zero,
    zero_comp, comp_zero]

/-- A vanishing composite, reassociated. -/
private theorem assoc_four_eq_zero {D : Type*} [Category D] [Preadditive D] {A B C E F Z : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F) (e : F ⟶ Z)
    (h : (a ≫ b ≫ c ≫ d) ≫ e = 0) : a ≫ b ≫ c ≫ d ≫ e = 0 := by
  simpa only [Category.assoc] using h

/-- Cancelling three invertible factors common to two composites. -/
private theorem cancel_three_of_eq {D : Type*} [Category D] {P A B C K K' : D}
    {c : P ⟶ K} {a : P ⟶ A} {b : A ⟶ B} {t : B ⟶ C} {h : C ⟶ K} {γ : K ⟶ K'} {β : C ⟶ K'}
    (hc : c = a ≫ b ≫ t ≫ h) (hγ : c ≫ γ = a ≫ b ≫ t ≫ β) (ha : IsIso a) (hb : IsIso b)
    (ht : IsIso t) : h ≫ γ = β := by
  subst hc
  simp only [Category.assoc] at hγ
  exact (cancel_epi t).1 ((cancel_epi b).1 ((cancel_epi a).1 hγ))

attribute [local instance] derivedComponentModuleRestriction_additive

/-- **The first half of the proof of Stacks 0D9S: a morphism `K ⟶ K'` agreeing with the given
morphism of simplicial systems in degree zero.** Over flat structure-sheaf transitions, for a
cartesian `K` with `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, every morphism `f` of the associated
simplicial systems is realised in degree zero by some `γ : K ⟶ K'`.

The construction is the source's, through the Postnikov system of Stacks 0D9Q for `- ⊗^L_O K`;
the module docstring of
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleLiftConstruction.lean`
describes how the two computations the source omits are carried out. -/
theorem exists_hom_derivedComponentModuleRestriction_zero_eq
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ (m n : SimplexCategory) (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) :
    ∃ γ : K ⟶ K', (S.derivedComponentModuleRestriction O ⦋0⦌).map γ = f.app ⦋0⦌ := by
  obtain ⟨D, hD⟩ := exists_simplicialModuleResolutionActual_homEquiv_augmentation S
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)
  let : (S.moduleResolutionTensorFunctor O K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).commShift_left K
  let : (S.moduleResolutionTensorFunctor O K).IsTriangulated :=
    isTriangulated_derivedTensorRight O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  have hproj : ∀ n, IsIso (S.moduleProjection O n (hflat n) K) :=
    (S.isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence O
      (S.moduleSumFormulaLegEq O) hflat (S.derivedModuleSumFormulaSummand O hflat)
      (S.transitionTensorCoherence O) (S.transitionUnitorCoherence O) K).1 hK
  -- The two adjunctions, the projection maps as isomorphisms, and `θ`.
  let adj₀ := S.componentModuleLowerShriekDerivedAdjunction O ⦋0⦌ (hflat ⦋0⦌)
  let adj₁ := S.componentModuleLowerShriekDerivedAdjunction O ⦋1⦌ (hflat ⦋1⦌)
  let e₀ := @asIso _ _ _ _ (S.moduleProjection O ⦋0⦌ (hflat ⦋0⦌) K) (hproj ⦋0⦌)
  let e₁ : (S.componentModuleLowerShriekDerived O ⦋1⦌ (hflat ⦋1⦌)).obj
      ((S.derivedComponentModuleRestriction O ⦋1⦌).obj K) ≅
      (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) :=
    @asIso _ _ _ _ (S.moduleProjection O ⦋1⦌ (hflat ⦋1⦌) K) (hproj ⦋1⦌) ≪≫
      (S.moduleResolutionTensorTermCanonicalIso O D K 1).symm
  let h := S.moduleResolutionTensorAugmentation O D K
  let θ := (adj₀.homEquiv _ K) (e₀.hom ≫ h)
  have hθ : IsIso θ :=
    S.isIso_homEquiv_moduleProjection_comp_of_homEquiv_eq_id O ⦋0⦌ (hflat ⦋0⦌)
      (moduleResolutionLowerShriekAugmentation D) hD K
  let b := e₀.inv ≫ (adj₀.homEquiv _ K').symm (θ ≫ f.app ⦋0⦌)
  -- The first omitted computation: `X₁ ⟶ X₀ ⟶ K'` vanishes.
  have hb : (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
      (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b =
      (0 : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶ K') := by
    have hcounit : (S.componentModuleLowerShriekDerived O ⦋0⦌ (hflat ⦋0⦌)).map θ ≫
        adj₀.counit.app K = e₀.hom ≫ h :=
      (adj₀.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
    let E : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶
        (S.componentModuleLowerShriekDerived O ⦋0⦌ (hflat ⦋0⦌)).obj
          ((S.derivedComponentModuleRestriction O ⦋0⦌).obj K) :=
      (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
        (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ e₀.inv ≫
          (S.componentModuleLowerShriekDerived O ⦋0⦌ (hflat ⦋0⦌)).map θ
    have hE : E ≫ adj₀.counit.app K = 0 :=
      comp_counit_eq_zero (D := DerivedCategory (S.totalRingedTopos O).Modules) _ _ _ _ _ _ _
        hcounit e₀.inv_hom_id (S.termDiff_comp_moduleResolutionTensorAugmentation O D K)
    have hE' : (e₁.hom ≫ E) ≫ (adj₀.homEquiv _ K').symm (f.app ⦋0⦌) = 0 := by
      refine (adj₁.homEquiv _ K').injective ?_
      refine (adj₁.homEquiv_naturality_right _ _).trans ?_
      refine (congrArg (fun k => (adj₁.homEquiv _ _) (e₁.hom ≫ E) ≫ k)
        (S.derivedComponentModuleRestriction_map_homEquiv_symm hflat
          (S.derivedModuleSumFormulaSummand O hflat) f ⦋0⦌ ⦋1⦌)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun k => k ≫ f.app ⦋1⦌)
        (adj₁.homEquiv_naturality_right (e₁.hom ≫ E) (adj₀.counit.app K)).symm).trans ?_
      exact homEquiv_comp_comp_eq_zero adj₁ _ _
        ((Category.assoc _ _ _).trans ((congrArg (fun k => e₁.hom ≫ k) hE).trans comp_zero)) _
    have hE'' : E ≫ (adj₀.homEquiv _ K').symm (f.app ⦋0⦌) = 0 :=
      (e₁.cancel_iso_hom_left _ _).1 ((Category.assoc _ _ _).symm.trans (hE'.trans comp_zero.symm))
    exact (congrArg (fun k => (S.moduleResolutionTensorFunctor O K).map
        (moduleResolutionTermDiff D 0) ≫ (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫
          e₀.inv ≫ k) (adj₀.homEquiv_naturality_left_symm θ (f.app ⦋0⦌))).trans
      (assoc_four_eq_zero _ _ _ _ _ hE'')
  obtain ⟨γ, hγ⟩ := S.exists_hom_of_moduleResolution_termDiff_comp_eq_zero O D K K'
    (fun _ _ φ => hflat _ _ φ) (fun i => hproj ⦋i⦌) hHom
    (S.isHomotopyColimitWith_moduleResolutionTensorSystem O D K) b hb
  refine ⟨γ, ?_⟩
  -- The second omitted computation: the bottom coprojection is the augmentation.
  have hγ' : h ≫ γ = b :=
    cancel_three_of_eq (S.moduleResolutionTensorCoprojection_zero O D K) hγ
      (Iso.isIso_hom ((S.moduleResolutionTensorFunctor O K).mapIso
        (StacksDraft.BrutalPostnikov.totAtTowerIso (moduleResolutionComplex D)
          (-((1 : ℕ) : ℤ)) (by simp)).symm))
      (Iso.isIso_hom ((S.moduleResolutionTensorFunctor O K).mapIso
        (@asIso _ _ _ _ (moduleResolutionTotProj D 0)
          (StacksDraft.BrutalPostnikov.isIso_totProj_zero (moduleResolutionComplex D)))))
      (Iso.isIso_hom _)
  have hkey : θ ≫ (S.derivedComponentModuleRestriction O ⦋0⦌).map γ = θ ≫ f.app ⦋0⦌ :=
    ((adj₀.homEquiv_naturality_right (e₀.hom ≫ h) γ).symm.trans
      (congrArg (adj₀.homEquiv _ K') ((Category.assoc _ _ _).trans
        ((congrArg (fun k => e₀.hom ≫ k) hγ').trans (e₀.hom_inv_id_assoc _))))).trans
      (Equiv.apply_symm_apply _ _)
  exact (cancel_epi θ).1 hkey

/-- **Stacks 0D9S.** In Situation 09WE, let `O` be a sheaf of rings on the total site and let
`K`, `K'` be objects of `D(O)`. Assume

1. the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are flat,
2. `K` is cartesian, and
3. `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`.

Then any morphism `{K_n ⟶ K'_n}` between the associated simplicial systems of the derived
category of modules comes from a morphism `K ⟶ K'` in `D(O)`.

The situation `S` is an arbitrary term of `CategoryTheory.SimplicialSiteSituation`, so both cases
of Situation 09WE are covered. The proof is the source's: the Postnikov system of Stacks 0D9Q
produces a morphism agreeing with the given one in degree zero
(`exists_hom_derivedComponentModuleRestriction_zero_eq`), and cartesianness of `K` makes it agree
in every degree (`SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian`). -/
@[stacks 0D9S]
theorem exists_hom_of_cartesian
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ (m n : SimplexCategory) (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) :
    ∃ γ : K ⟶ K', ∀ i : SimplexCategory,
      (S.derivedComponentModuleRestriction O i).map γ = f.app i := by
  obtain ⟨γ, hγ⟩ := S.exists_hom_derivedComponentModuleRestriction_zero_eq O K K' hflat hK hHom f
  exact ⟨γ, fun i => SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian S O
    (S.derivedModuleSystem_cartesian O K hK) (S.derivedModuleSystemMap O γ) f hγ i⟩

end CategoryTheory.SimplicialSiteSituation

end
