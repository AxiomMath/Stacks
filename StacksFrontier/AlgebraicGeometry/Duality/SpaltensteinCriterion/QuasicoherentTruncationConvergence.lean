module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceAcyclicCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.InverseSystemsOnASpace
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower

/-!
# A complex with quasi-coherent cohomology is the derived limit of its lower truncations

Let `X` be a scheme and let `E` be an object of the unbounded derived category of
`𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent. The canonical map from `E` to
the derived inverse limit of the tower of canonical truncations `n ↦ τ_{≥ -n} E` is an
isomorphism.

The proof feeds Serre vanishing on an affine open into the local convergence criterion for a
ringed site (Stacks 0D6P): the affine opens of `X` form a basis, so every open of `X` is covered
by affine opens, and on an affine open the higher cohomology of a quasi-coherent module vanishes.

## Main definitions

* `AlgebraicGeometry.evaluationCompForgetIsoSections` — the comparison between the two readings
  of sections over an open, as a module over the functions on that open and as an abelian group.

## Main results

* `AlgebraicGeometry.isZero_evaluationRightDerived_of_isAffineOpen` — Serre vanishing
  (Stacks 01XB) in the module-valued form the site criterion asks for.
* `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower` — **Stacks 08D3**: the canonical map
  to a derived limit of the tower of lower truncations is an isomorphism.

## Implementation notes

The site of a scheme is the ringed site of its underlying ringed space, and
`AlgebraicGeometry.Scheme.Modules` is by definition `SheafOfModules` of its sheaf of rings, so
the site criterion applies with no transport.

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of the convergence
criterion. The statement is about the derived category of `𝒪_X`-modules and says the same thing
at any model, but the criterion is available only at this one.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

variable (X : Scheme.{u})

/-- Sections over an open of a scheme, as an abelian group, are the sections as a module over
the functions on that open with the module structure forgotten. -/
def evaluationCompForgetIsoSections (U : X.Opens) :
    SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat.{u} ≅
      secF X.ringCatSheaf U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- **Serre vanishing, in the module-valued form.** The positive-degree right derived functors
of sections over an affine open, as modules over the functions on that open, vanish on a
quasi-coherent `𝒪_X`-module ([Stacks, Tag 01XB]). -/
alias isZero_evaluationRightDerived_of_isAffineOpen :=
  isZero_rightDerived_evaluation_of_isAffineOpen

/-- **Stacks 08D3.** A complex of `𝒪_X`-modules on a scheme whose cohomology sheaves are all
quasi-coherent is canonically isomorphic to the derived inverse limit of the tower of its
canonical lower truncations `n ↦ τ_{≥ -n} E`.

The derived limit is presented by a distinguished triangle whose second map is the canonical
difference of the projections, and the map `c` is pinned down by the requirement that its
composites with the projections are the canonical truncation maps; the conclusion is that this
map is invertible. -/
@[stacks 08D3]
theorem isIso_to_isDerivedLimit_truncGETower
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩) ⟶
      L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} X.ringCatSheaf) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} X.ringCatSheaf) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
    X.ringCatSheaf E (fun U ↦ U ∈ X.affineOpens)
    (Stacks.Cohomology.SpaceInverseSystems.basis_hasEnoughObjects X.toRingedSpace
      X.affineOpens X.isBasis_affineOpens)
    (fun V hV r hr q ↦
      have : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) q).obj E).IsQuasicoherent := hE q
      isZero_evaluationRightDerived_of_isAffineOpen X _ V hV r hr)
    L c p δ hL hc

end AlgebraicGeometry

end
