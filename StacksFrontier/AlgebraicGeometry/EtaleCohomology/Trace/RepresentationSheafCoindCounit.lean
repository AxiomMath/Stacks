module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCoinduced

/-!
# The sum map `Coind_H M ⟶ M`, and maps out of `ℱ_{Coind_H M}` through the trace

Let `G` be a compact group, `H` an open subgroup and `M` a finite `Λ`-module with a continuous
`G`-action. The coinduced module `Coind_H M` is the module of functions `G ⧸ H → M` with
`(g • f)(x) = g • f(g⁻¹ • x)` (`Stacks.GroupCohomology.finiteTypeContinuousModuleCoind`). Summing
over the finitely many cosets is a `G`-equivariant surjection

`Σ : Coind_H M ⟶ M`, `f ↦ Σ_{x ∈ G ⧸ H} f(x)`,

natural in `M`. It is the map along which homological δ-functors on these modules are
coeffaced.

On the sheaf side, let `φ : V ⟶ X` be finite étale with `H` the image of `π₁(V, v)`, so that
`ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M` (`AlgebraicGeometry.representationSheafCoindIso`). The direct
image `φ_*` is also a *left* adjoint of `φ^*`
(`Stacks.EtaleCohomology.etaleModuleDirectImageInverseImageAdj`, Tag 03S7), with counit the
trace `φ_* φ^* ⟶ id`. Hence every map out of `ℱ_{Coind_H M}`, in particular `ℱ_Σ`, factors
through the trace.

## Main definitions

* `Stacks.ContinuousCohomology.coindSum` — `Σ : Coind_H M ⟶ M` on all continuous modules.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindSum` — the same on finite modules.

## Main results

* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindSum_naturality`.
* `Stacks.GroupCohomology.epi_finiteTypeContinuousModuleCoindSum` — `Σ` is an epimorphism; the
  functions supported on the trivial coset give a section.
* `AlgebraicGeometry.representationSheafCoind_map_eq_comp_counit` — every map
  `f : ℱ_{Coind_H M} ⟶ N` is `ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M ⟶ φ_* φ^* N ⟶ N`, the last map being the
  counit (trace) of `φ_* ⊣ φ^*`.
* `AlgebraicGeometry.representationSheaf_map_coindSum_eq_comp_counit` — the case `f = ℱ_Σ`.

## Implementation notes

The factorization is formal: it holds for any map out of `φ_* G` and any left adjoint `φ_*`, and
it does not identify the middle map `φ_* φ^* ℱ_M ⟶ φ_* φ^* ℱ_M`. What it gives is the
inclusion of images used for coeffaceability: the image of `ℱ_Σ` under any functor lies in the
image of the trace.

The stronger identity `(representationSheafCoindIso M).inv ≫ ℱ_Σ = counit`, with no middle map,
is *not* formal. An adjunction `φ_* ⊣ φ^*` determines its counit only up to a natural
automorphism of `φ^*`. On representations these automorphisms are `Nat(res, res)`, which contains
every central unit of `Λ`. So the identity depends on how the base adjunction is built:
extension by zero read through `AlgebraicGeometry.moduleExtensionByZeroIsoPushforward`, then
transported to Mathlib's site. Proving it needs a description on sections of the comparison
`AlgebraicGeometry.representationSheafCoindComparison`, through Tags 0DV5 and 0DV6. That
description is not established here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (V : OpenSubgroup G)

/-- The sum `f ↦ Σ_{x ∈ G ⧸ V} f(x)` over the finitely many cosets, as a linear map. -/
def coindSumLinearMap (A : Type w) [AddCommGroup A] [Module R A] :
    (G ⧸ (V : Subgroup G) → A) →ₗ[R] A :=
  letI : Fintype (G ⧸ (V : Subgroup G)) := Fintype.ofFinite _
  ∑ x, LinearMap.proj x

/-- `coindSumLinearMap R V A f` is the finite sum `∑ᶠ x, f x` of the values of `f`. -/
lemma coindSumLinearMap_apply (A : Type w) [AddCommGroup A] [Module R A]
    (f : G ⧸ (V : Subgroup G) → A) : coindSumLinearMap R V A f = ∑ᶠ x, f x := by
  let : Fintype (G ⧸ (V : Subgroup G)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  unfold coindSumLinearMap
  rw [LinearMap.sum_apply]
  rfl

/-- **The sum map `Coind_V M ⟶ M`**, `f ↦ Σ_{x ∈ G ⧸ V} f(x)`. It is `G`-equivariant because
the action of `g` permutes the cosets. -/
def coindSum (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    (coind.{u, v, w} R V).obj M ⟶ M :=
  (Stacks.GroupCohomology.homEquiv R G ((coind.{u, v, w} R V).obj M) M).symm
    ⟨coindSumLinearMap R V M.obj.obj.V, fun g f ↦ by
      change coindSumLinearMap R V M.obj.obj.V (fun x ↦ (M.obj.obj.ρ g).hom (f (g⁻¹ • x))) =
        (M.obj.obj.ρ g).hom (coindSumLinearMap R V M.obj.obj.V f)
      exact (coindSumLinearMap_apply R V _ _).trans
        ((finsum_comp_equiv (MulAction.toPerm g⁻¹) (f := fun x ↦ (M.obj.obj.ρ g).hom (f x))).trans
          ((map_finsum (M.obj.obj.ρ g).hom (Set.toFinite _)).symm.trans
            (congrArg (fun y ↦ (M.obj.obj.ρ g).hom y) (coindSumLinearMap_apply R V _ f).symm)))⟩

/-- The sum map `coindSum R V M` sends `f : G ⧸ V → M` to `∑ᶠ x, f x`. -/
lemma coindSum_apply (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
    (f : G ⧸ (V : Subgroup G) → M.obj.obj.V) :
    (coindSum.{u, v, w} R V M).hom.hom.hom.hom f = ∑ᶠ x, f x :=
  coindSumLinearMap_apply R V M.obj.obj.V f

/-- The sum map `coindSum R V` is natural: for `φ : M ⟶ N`, `Coind_V φ ≫ Σ_N = Σ_M ≫ φ`. -/
@[reassoc]
lemma coindSum_naturality {M N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (φ : M ⟶ N) : (coind R V).map φ ≫ coindSum.{u, v, w} R V N = coindSum R V M ≫ φ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  show coindSumLinearMap R V N.obj.obj.V (fun x ↦ φ.hom.hom.hom.hom (f x)) =
    φ.hom.hom.hom.hom (coindSumLinearMap R V M.obj.obj.V f)
  exact (coindSumLinearMap_apply R V _ _).trans
    ((map_finsum φ.hom.hom.hom.hom (Set.toFinite _)).symm.trans
      (congrArg (fun y ↦ φ.hom.hom.hom.hom y) (coindSumLinearMap_apply R V _ f).symm))

/-- The function supported on the trivial coset sums to its value there. -/
lemma coindSum_apply_single [DecidableEq (G ⧸ (V : Subgroup G))]
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (m : M.obj.obj.V) :
    (coindSum.{u, v, w} R V M).hom.hom.hom.hom
      (Pi.single ((1 : G) : G ⧸ (V : Subgroup G)) m) = m := by
  let : Fintype (G ⧸ (V : Subgroup G)) := Fintype.ofFinite _
  rw [coindSum_apply, finsum_eq_sum_of_fintype]
  exact Finset.sum_pi_single' _ _ _ |>.trans (if_pos (Finset.mem_univ _))

/-- **The sum map is an epimorphism.** -/
instance epi_coindSum (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    Epi (coindSum.{u, v, w} R V M) :=
  (epi_iff_surjective R _).2 fun m ↦ by
    classical exact ⟨_, coindSum_apply_single R V M m⟩

end Stacks.ContinuousCohomology

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (H : OpenSubgroup G)

/-- **The sum map `Coind_H M ⟶ M`** of finite `R`-modules with a continuous `G`-action,
`f ↦ Σ_{x ∈ G ⧸ H} f(x)`. -/
def finiteTypeContinuousModuleCoindSum (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    (finiteTypeContinuousModuleCoind R H).obj M ⟶ M :=
  ObjectProperty.homMk (coindSum.{u, v, 0} R H M.obj)

/-- The sum map `finiteTypeContinuousModuleCoindSum R H M` sends `f : G ⧸ H → M` to
`∑ᶠ x, f x`. -/
lemma finiteTypeContinuousModuleCoindSum_apply
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G)
    (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :
    (finiteTypeContinuousModuleCoindSum R H M).hom.hom.hom.hom f = ∑ᶠ x, f x :=
  coindSum_apply.{u, v, 0} R H M.obj f

/-- The sum map `finiteTypeContinuousModuleCoindSum R H` is natural: for `a : M ⟶ N`,
`Coind_H a ≫ Σ_N = Σ_M ≫ a`. -/
@[reassoc]
lemma finiteTypeContinuousModuleCoindSum_naturality
    {M N : FiniteTypeContinuousModule.{u, v, max u v} R G} (a : M ⟶ N) :
    (finiteTypeContinuousModuleCoind R H).map a ≫ finiteTypeContinuousModuleCoindSum R H N =
      finiteTypeContinuousModuleCoindSum R H M ≫ a :=
  ObjectProperty.hom_ext _ (coindSum_naturality.{u, v, 0} R H a.hom)

/-- **The sum map `Coind_H M ⟶ M` as a natural transformation.** -/
def finiteTypeContinuousModuleCoindSumNatTrans :
    finiteTypeContinuousModuleCoind R H ⟶ 𝟭 (FiniteTypeContinuousModule.{u, v, max u v} R G) where
  app := finiteTypeContinuousModuleCoindSum R H
  naturality _ _ a := finiteTypeContinuousModuleCoindSum_naturality R H a

/-- **The sum map `Coind_H M ⟶ M` is an epimorphism**: the functions supported on the trivial
coset give a section of the underlying linear map. -/
instance epi_finiteTypeContinuousModuleCoindSum
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    Epi (finiteTypeContinuousModuleCoindSum R H M) :=
  (finiteTypeContinuousModuleι.{u, v, max u v} R G).epi_of_epi_map
    (inferInstanceAs (Epi (coindSum.{u, v, 0} R H M.obj)))

end Stacks.GroupCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) {X V : B.Scheme} (φ : V ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace V.1] (Λ : Type) [Ring Λ] [Finite Λ] (v : GeometricPoint V.1)
  (H : OpenSubgroup (EtaleFundamentalGroup X.1 (v.map φ.hom)))
  (hφ : ∀ g, etaleFundamentalGroupMap φ.hom v g ∈ H)
  (hH : ∀ h ∈ H, ∃ g, etaleFundamentalGroupMap φ.hom v g = h) [IsFinite φ.hom] [Etale φ.hom]

/-- **Every map out of `ℱ_{Coind_H M}` factors through the trace.** For `φ : V ⟶ X` finite
étale and `H` the image of `π₁(V, v)`, a map `f : ℱ_{Coind_H M} ⟶ N` is the composite of
`ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M` (`AlgebraicGeometry.representationSheafCoindIso`), the direct image
`φ_* β` of the map `β : φ^* ℱ_M ⟶ φ^* N` adjoint to `f`, and the counit `φ_* φ^* N ⟶ N` of
`φ_* ⊣ φ^*` (`Stacks.EtaleCohomology.etaleModuleDirectImageInverseImageAdj`), which is the trace.
This is formal and does not identify `β`; see the module docstring. -/
theorem representationSheafCoind_map_eq_comp_counit
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom)))
    {N : EtaleModules.{u, 0} Λ X.1}
    (f : (representationSheaf B X (v.map φ.hom) Λ).obj
      ((finiteTypeContinuousModuleCoind Λ H).obj M) ⟶ N) :
    f = (representationSheafCoindIso B φ Λ v H hφ hH).hom.app M ≫
      (etaleModuleDirectImage.{u, 0} Λ φ.hom).map
        ((etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _
          ((representationSheafCoindIso B φ Λ v H hφ hH).inv.app M ≫ f)) ≫
      (etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).counit.app N := by
  have h := ((etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).homEquiv_counit
    (g := (etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _
      ((representationSheafCoindIso B φ Λ v H hφ hH).inv.app M ≫ f))).symm
  rw [Equiv.symm_apply_apply] at h
  rw [h, Iso.hom_inv_id_app_assoc]

/-- **`ℱ` of the sum map factors through the trace**: `ℱ_Σ : ℱ_{Coind_H M} ⟶ ℱ_M` is
`ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M ⟶ φ_* φ^* ℱ_M ⟶ ℱ_M`, the last map being the counit of `φ_* ⊣ φ^*`.
So the image of `ℱ_Σ` under any functor lies in the image of the trace. -/
theorem representationSheaf_map_coindSum_eq_comp_counit
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom))) :
    (representationSheaf B X (v.map φ.hom) Λ).map (finiteTypeContinuousModuleCoindSum Λ H M) =
      (representationSheafCoindIso B φ Λ v H hφ hH).hom.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ φ.hom).map
          ((etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _
            ((representationSheafCoindIso B φ Λ v H hφ hH).inv.app M ≫
              (representationSheaf B X (v.map φ.hom) Λ).map
                (finiteTypeContinuousModuleCoindSum Λ H M))) ≫
        (etaleModuleDirectImageInverseImageAdj.{u, 0} Λ φ.hom).counit.app _ :=
  representationSheafCoind_map_eq_comp_counit B φ Λ v H hφ hH M _

end AlgebraicGeometry

end
