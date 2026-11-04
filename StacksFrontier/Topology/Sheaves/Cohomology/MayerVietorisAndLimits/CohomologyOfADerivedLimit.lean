module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.AcyclicCoveringFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HypercohomologyOverAcyclicOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a derived inverse limit over a basis of acyclic opens

Let `(X, 𝒪_X)` be a ringed space, let `(K_n)` be an inverse system of objects of `D(𝒪_X)` with
derived limit `L`, and let `B` be a basis of the topology of `X`. If over every member `U` of
`B` the cohomology sheaves of the `K_n` are acyclic, so that `H^p(U, H^q(K_n)) = 0` for `p > 0`,
and the inverse systems `H^0(U, H^q(K_n))` have vanishing `R¹ lim`, then cohomology commutes with
the derived limit: `H^q(L) = lim H^q(K_n)` for every `q`.

## Main results

* `Stacks.Cohomology.DerivedLimits.cohomology_isLimit_of_isDerivedLimit_of_isBasis`: the canonical
  cone on the degree-`q` cohomology sheaves, whose legs are induced by the structural maps of the
  derived-limit triangle, is a limit cone.

## Implementation notes

The statement for a ringed site is Stacks 0A09; it is available on a covering family of objects
of the site, with the hypercohomology comparison of Stacks 0BKZ as an explicit hypothesis. Both
inputs are present at a ringed space: the opens of `X` with the open-cover topology are a site
whose sheaves of modules are the `𝒪_X`-modules, a basis of the topology is a covering family of
objects, and the hypercohomology comparison over a basic open is Stacks 0BKT.

The derived limit enters as a structural map together with its distinguished triangle rather than
through the predicate `CategoryTheory.Pretriangulated.IsDerivedLimit`, so that the limit cone
produced is the one whose legs are the given structural maps; a derived limit is unique only up
to non-unique isomorphism, so this is strictly more informative than naming some limit cone.

Cohomology over an open is the right derived functor of the module-valued sections functor, as in
Tag 0BKT, while the inverse systems whose `R¹ lim` must vanish are systems of abelian groups, as
`Rlim.firstDerivedLimit` is; the underlying abelian group of a module is zero exactly when the
module is, so neither choice changes the content of a hypothesis.

## References

* [Stacks Project, Tag 0BKU](https://stacks.math.columbia.edu/tag/0BKU)
* [Stacks Project, Tag 0A09](https://stacks.math.columbia.edu/tag/0A09)
* [Stacks Project, Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SpaceInverseSystems (ringedSiteOfSpace basis_hasEnoughObjects)

namespace Stacks.Cohomology.DerivedLimits

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

variable (X : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (structureSheafRing X))]

/-- **Stacks Project, Tag 0BKU.** Let `(K_n)` be an inverse system of objects of `D(𝒪_X)` and let
`L` be a derived limit of it, exhibited by the structural map `p` and its distinguished triangle.
If on a basis `B` of the topology the cohomology sheaves of the `K_n` are acyclic and the inverse
systems of their sections have vanishing `R¹ lim`, then for every `q` the degree-`q` cohomology
sheaf of `L` is the inverse limit of the degree-`q` cohomology sheaves of the `K_n`, through the
maps induced by `p`. -/
@[stacks 0BKU]
theorem cohomology_isLimit_of_isDerivedLimit_of_isBasis
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    [hprod : HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (hacyclic : ∀ U ∈ B, ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      IsZero (((SheafOfModules.evaluation (structureSheafRing X) (op U)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q).obj
          (K.obj ⟨n⟩))))
    (hlimOne : ∀ U ∈ B, ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q ⋙
          SheafOfModules.evaluation (structureSheafRing X) (op U) ⋙
            forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) AddCommGrpCat.{u})))
    (q : ℤ) :
    ∃ τ : (Functor.const ℕᵒᵖ).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q).obj L) ⟶
        K ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q,
      (∀ n : ℕ, τ.app ⟨n⟩ =
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q).map
          (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      Nonempty (IsLimit (Cone.mk _ τ)) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X)
  -- The structure sheaf of the site of opens of `X` is the sheaf of rings of `X` itself, but
  -- the two spellings are not interchangeable for instance synthesis.
  have _ : @HasProduct ℕ
      (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteOfSpace X).O))) _
      (fun n : ℕ ↦ K.obj ⟨n⟩) := hprod
  have hedge : ∀ U, U ∈ B → ∀ (m : ℤ) (n : ℕ),
      IsIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteOfSpace X).O) U m).app (K.obj ⟨n⟩)) :=
    fun U hU m n ↦
      Stacks.Cohomology.AcyclicOpen.isIso_hypercohomologyEdge_app_of_isBasis X (K.obj ⟨n⟩) B hB
        (fun V hV r hr i ↦ hacyclic V hV i n r hr) U hU m
  obtain ⟨a, b, c, ha, hb, _, _⟩ :=
    Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram
      (ringedSiteOfSpace X) K L p hL q
  have hbIso : IsIso b :=
    Stacks.Cohomology.DerivedLimitAcyclic.isIso_cohomologyLimitComparison
      (ringedSiteOfSpace X) K L p hL (fun U ↦ U ∈ B) (basis_hasEnoughObjects X B hB) hedge
      (fun U hU m ↦ hlimOne U hU m) q a b ha hb
  refine ⟨(Functor.const ℕᵒᵖ).map b ≫
    (limit.cone (K ⋙ DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) q)).π, fun n ↦ hb n, ?_⟩
  exact ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (asIso b).symm fun n ↦
    (IsIso.inv_hom_id_assoc b (limit.π _ n)).symm)⟩

end Stacks.Cohomology.DerivedLimits

end
