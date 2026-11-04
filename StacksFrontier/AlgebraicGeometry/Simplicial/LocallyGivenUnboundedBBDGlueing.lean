module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenBBDGlueing
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenLocalSerrePullback
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded BBD glueing lemma

This file proves **Stacks 0DCC**. In Situation 0DC9, assume `C` has equalizers and fibre
products, that there is a morphism of sites `f : C ⟶ D` given by a continuous functor
`u : D ⥤ C` commuting with equalizers and fibre products, with `B` a full subcategory of `D` whose
objects cover every object of `D` and `u : B ⥤ C` the restriction of `u`, that all negative
self-exts of the `E_U` vanish, and that there are weak Serre subcategories `A_U ⊂ Mod(O_U)` for
all objects `U` of `C` satisfying 0DC2, 0DC3 and 0DC4 with `E_U ∈ D_{A_U}(O_U)`. Then there is a
solution, unique up to unique isomorphism.

## The argument

The argument is that of Stacks 0DCB, with Stacks 0DC7 in place of Stacks 0DA2. A
hypercovering `L` of `D` by objects of `B` with `L_0 = {U}_{U ∈ B}` and `L_1` containing the
arrows of `B` gives the hypercovering `K = u(L)` of `C` (Stacks 0DAX, 0DAY); Stacks 0DCA glues the
`E_{U_{n,i}}` to a cartesian object `E` of `D(O)` on `(C/K)_total`. Its cohomology modules are
cartesian (Stacks 0D7L), so `H^q(E) = a^*N_q` (Stacks 0D9Z), and `N_q` lies in `A` because its
restrictions to the `U_{0,j}` are those of `H^q(E)`, which are `H^q(E_{U_{0,j}})`
(`AlgebraicGeometry.RingedSite.LocallyGiven.overFunctor_mem_of_homology_iso_pullback`) and the
`U_{0,j}` cover (0DC2, 0DC3). So `E` lies in `D_{A_total}(O)` and Stacks 0DC7 gives `F` in
`D_A(O_C)` with `La^*F ≅ E`
(`CategoryTheory.SimplicialSemiRepresentable.exists_derivedPullback_iso_of_cartesian_homology`).
The identifications `ρ_U` and their compatibility are read off `L_0` and `L_1` exactly as in the
proof of Stacks 0DCB, and uniqueness is that of Stacks 0DCB
(`AlgebraicGeometry.RingedSite.LocallyGiven.existsUnique_compatibleIso_of_hypercovering`), which
uses no boundedness.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.nonempty_solution_of_hypercovering_localSerre`: the
  existence half, given the hypercovering `u(L)` of the proof.
* `AlgebraicGeometry.RingedSite.LocallyGiven.exists_unique_solution_localSerre`: **Stacks 0DCC**.

## References

* [Stacks Project, Tag 0DCC](https://stacks.math.columbia.edu/tag/0DCC)
* [Stacks Project, Tag 0DCB](https://stacks.math.columbia.edu/tag/0DCB)
* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.CohomologicalDescent Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent
  RingedSite.overFunctor_preservesFiniteLimits' RingedSite.overFunctor_preservesFiniteColimits'

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category

section Main

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (PC : Pretopology C)
  (O : Sheaf PC.toGrothendieck CommRingCat.{u})
  (G : LocallyGiven.{0, u, u, u, u, u} (pretopologyRingedSite PC O))
  (L : SimplicialObject (FormalCoproduct.{u} G.B))
  (c : ∀ U : G.B, (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋0⦌))
  (T : LocalSerreFamily.{u} (pretopologyRingedSite PC O))

/-- **Existence in Stacks 0DCC**, given the hypercovering `u(L)` of the proof: the glued object
`E` of Stacks 0DCA has its cohomology in `A_total`, so it is `La^*F` for an `F` in `D_A(O_C)` by
Stacks 0DC7, and `F` with the identifications read off `L_0` and `L_1` is a solution. -/
theorem nonempty_solution_of_hypercovering_localSerre
    (hc : ∀ {U V : G.B} (a : U ⟶ V), ∃ e : (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋1⦌),
      e ≫ L.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl G.B).map a ≫ c V ∧
        e ≫ L.map (SimplexCategory.δ 1).op = c U)
    (Y : HypercoveringOfTerminal.{u} PC) (hY : Y.toSimplicialObject = G.image L)
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} (pretopologyRingedSite PC O) (G.u.obj U)) t).obj
        (G.obj U) ⟶ G.obj U, g = 0)
    (hA : ∀ (U : G.B) (q : ℤ), T.A (G.u.obj U)
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).over (G.u.obj U))) q).obj (G.obj U))) :
    Nonempty G.Solution := by
  obtain ⟨K', a₀, a₁, a₂, a₃⟩ := Y
  dsimp only at hY
  subst hY
  let Y : HypercoveringOfTerminal.{u} PC := ⟨G.image L, a₀, a₁, a₂, a₃⟩
  obtain ⟨⟨E, hE, ⟨σ⟩⟩, -⟩ := G.exists_unique_cartesian_summandIdentification L hneg
  obtain ⟨F, -, ⟨ε⟩⟩ := exists_structurePullback_iso_of_cartesian_homology PC O Y T E
    (fun q ↦ by convert G.homology_isModuleFiberTransitionIso L hE q using 1)
    (fun q N e j ↦ G.overFunctor_mem_of_homology_iso_pullback L T hA E σ q N e.symm ⦋0⦌ j)
  exact G.nonempty_solution_of_structurePullback_iso L c hc σ ε

end Main

section UnboundedBBD

/-- The unbounded BBD glueing lemma. In Situation 0DC9 — a ringed site `(C, O_C)`, a category
`B` with a functor `u : B ⥤ C`, objects `E_U` of `D(O_{u(U)})` and isomorphisms
`ρ_a : E_U|_{C/u(V)} ⟶ E_V` satisfying the cocycle condition — assume

1. `C` has equalizers and fibre products;
2. there is a morphism of sites `f : C ⟶ D` given by a continuous functor `u : D ⥤ C` (here
   `f`, with `IsMorphismOfSites`), such that `D` has equalizers and fibre products and `u`
   commutes with them, `B` is a full subcategory of `D` (a fully faithful `i : B ⥤ D`) with
   `u : B ⥤ C` the restriction of `u` (`i ⋙ f = G.u`), and every object of `D` has a covering
   whose members are objects of `B`;
3. all negative self-exts of `E_U` in `D(O_{u(U)})` are zero, that is, every map
   `E_U[t] ⟶ E_U` with `t > 0` vanishes;
4. there are weak Serre subcategories `A_U ⊂ Mod(O_U)` for all objects `U` of `C` satisfying
   conditions 0DC2, 0DC3 and 0DC4 (`T : LocalSerreFamily X`);
5. `E_U ∈ D_{A_U}(O_U)`: every cohomology module of `E_U` lies in `A_{u(U)}`.

Then there exists a solution `(E, ρ_U)`, and it is unique up to unique isomorphism: between two
solutions there is exactly one isomorphism compatible with their identifications `ρ_U`. -/
@[stacks 0DCC]
theorem exists_unique_solution_localSerre {X : RingedSite.{u, u, u}} [HasEqualizers X.C]
    [HasPullbacks X.C] (G : LocallyGiven.{0, u, u, u, u, u} X)
    {D : Type u} [SmallCategory D] [HasEqualizers D] [HasPullbacks D] (P : Pretopology D)
    (f : D ⥤ X.C) [IsMorphismOfSites.{u} f P.toGrothendieck X.J]
    [PreservesLimitsOfShape WalkingParallelPair f] [PreservesLimitsOfShape WalkingCospan f]
    (i : G.B ⥤ D) [i.Full] [i.Faithful] (hi : i ⋙ f = G.u)
    (hcover : ∀ V : D, ∃ (ι : Type u) (U : ι → G.B) (g : ∀ k, i.obj (U k) ⟶ V),
      Presieve.ofArrows (fun k ↦ i.obj (U k)) g ∈ P V)
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} X (G.u.obj U)) t).obj (G.obj U) ⟶ G.obj U,
        g = 0)
    (T : LocalSerreFamily.{u} X)
    (hA : ∀ (U : G.B) (q : ℤ), T.A (G.u.obj U)
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U))) q).obj (G.obj U))) :
    Nonempty G.Solution ∧
      ∀ S S' : G.Solution, ∃! e : S.obj ≅ S'.obj, Solution.IsCompatibleIso G e := by
  obtain ⟨C, J, O⟩ := X
  have : HasPullbacks C := ‹HasPullbacks _›
  have : HasEqualizers C := ‹HasEqualizers _›
  revert O
  obtain ⟨PC, hPC⟩ : ∃ PC : Pretopology C, PC.toGrothendieck = J :=
    ⟨J.toPretopology, (Pretopology.gi (C := C)).l_u_eq J⟩
  subst hPC
  intro O _ _ G f _ _ _ i _ _ hi hcover hneg T hA
  obtain ⟨L, H, hH, c, hc⟩ := exists_hypercoveringOfTerminal_fullSubcategory P i
    (Functor.FullyFaithful.ofFullyFaithful i) hcover
  obtain ⟨Y, hY⟩ := exists_hypercovering_of_map PC P f H
  have hYL : Y.toSimplicialObject = G.image L := by
    rw [hY, hH, LocallyGiven.image, ← hi]
    rfl
  exact ⟨nonempty_solution_of_hypercovering_localSerre PC O G L c T hc Y hYL hneg hA,
    existsUnique_compatibleIso_of_hypercovering PC O G L c Y hYL hneg⟩

end UnboundedBBD

end AlgebraicGeometry.RingedSite.LocallyGiven

end
