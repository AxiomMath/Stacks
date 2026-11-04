module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteConstantRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SplitCoverFiber
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers

/-!
# The value of the fundamental group dictionary on a constant sheaf

Let `X` be a connected scheme belonging to a big étale site, let `x` be a geometric point of it
and let `ι` be a finite index type. This file computes the value of the dictionary of
Stacks 0DV5 (1) on the constant sheaf of sets with value `ι`: it is `ι` with the trivial action
of `π₁(X, x)`.

The computation is the composite of the three legs the dictionary is built from. Under Stacks
03RV the constant sheaf on `ι` is represented by the split cover `∐_{i : ι} X`, which is
`Stacks.EtaleCohomology.constantSheafIsoSheafifiedYonedaSplitObj`; the finite object of the site
it names is carried to `Stacks.FundamentalGroup.splitCover` by the comparison with the finite
étale covers, on the nose. Under Stacks 0BND (1) the cover goes to its geometric fibre with the
action of the natural automorphisms of the fibre functor, and that fibre is `ι` with the trivial
action by `Stacks.FundamentalGroup.splitCoverFiberEquiv` and
`Stacks.FundamentalGroup.smul_eq_self_splitCover`. The change of universe conjugates the action
by a bijection and so preserves triviality.

## Main definitions

* `AlgebraicGeometry.splitFiniteSmallEtaleObject`: the split cover as a finite object of the
  small étale site.
* `AlgebraicGeometry.constantSheafFiniteLocallyConstant`: the constant sheaf on a finite set, as
  an object of the category of finite locally constant sheaves of sets.
* `AlgebraicGeometry.finiteEtaleOfConstantSheafIso`: **Stacks 03RV on a constant sheaf** — the
  finite étale cover attached to the constant sheaf on `ι` is the split cover.

## Main results

* `AlgebraicGeometry.rho_eq_one_finiteLocallyConstantSetsEquivalence_constantSheaf`: **Stacks
  0DV5 (1) on a constant sheaf** — the action is trivial.
* `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceConstantSheafEquiv`: and the underlying
  finite set is `ι`.

## Implementation notes

Triviality of an action is stated as `ρ σ = 1` rather than by exhibiting an isomorphism with a
constructed trivial object: the statement is then invariant under isomorphism of continuous
actions, `CategoryTheory.contAction_rho_eq_one_of_iso`, which is how it is transported along the
three legs, and no object has to be built to compare with.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped FintypeCatDiscrete

universe w u

namespace CategoryTheory

/-- The underlying isomorphism of finite sets of an isomorphism of continuous actions. -/
def contActionIsoV {G : Type*} [Group G] [TopologicalSpace G]
    {A A' : ContAction FintypeCat.{w} G} (e : A ≅ A') : A.obj.V ≅ A'.obj.V where
  hom := e.hom.1.hom
  inv := e.inv.1.hom
  hom_inv_id := congrArg (fun k : A ⟶ A ↦ k.1.hom) e.hom_inv_id
  inv_hom_id := congrArg (fun k : A' ⟶ A' ↦ k.1.hom) e.inv_hom_id

/-- Triviality of a continuous action is invariant under isomorphism. -/
theorem contAction_rho_eq_one_of_iso {G : Type*} [Group G] [TopologicalSpace G]
    {A A' : ContAction FintypeCat.{w} G} (e : A ≅ A')
    (h : ∀ σ : G, A.obj.ρ σ = 1) (σ : G) : A'.obj.ρ σ = 1 := by
  have hcomm : e.hom.1.hom = e.hom.1.hom ≫ A'.obj.ρ σ := by
    have hc := e.hom.1.comm σ
    rw [h σ] at hc
    simpa using hc
  have hfin : A'.obj.ρ σ = 𝟙 A'.obj.V :=
    (cancel_epi (contActionIsoV e).hom).1 (by rw [Category.comp_id]; exact hcomm.symm)
  simpa using hfin

/-- Triviality of a continuous action survives the change of universe. -/
theorem rho_eq_one_contActionUniverseEquivalence {G : Type*} [Group G] [TopologicalSpace G]
    (A : ContAction FintypeCat.{u} G) (h : ∀ σ : G, A.obj.ρ σ = 1) (σ : G) :
    ((contActionUniverseEquivalence.{u, w} G).functor.obj A).obj.ρ σ = 1 := by
  have he : ((contActionUniverseEquivalence.{u, w} G).functor.obj A).obj.ρ σ =
      FintypeCat.uSwitch.{u, w}.map (A.obj.ρ σ) := rfl
  rw [he, h σ]
  exact FintypeCat.uSwitch.{u, w}.map_id A.obj.V

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.ConstantSheaf Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ι : Type u) [Finite ι]

/-- The split cover, as a finite object of the small étale site of `X`. -/
def splitFiniteSmallEtaleObject : (finiteSmallEtaleObjects B X).FullSubcategory :=
  ⟨splitObj B X.2 ι, isFinite_hom_splitObj B X.2 ι⟩

/-- The finite étale cover named by the split object of the site is the split cover. -/
theorem finiteEtaleFromSmallEtale_splitFiniteSmallEtaleObject :
    (finiteEtaleFromSmallEtale B X).obj (splitFiniteSmallEtaleObject B X ι) =
      Stacks.FundamentalGroup.splitCover X.1 ι :=
  rfl

/-- The constant sheaf on a finite set, as a finite locally constant sheaf of sets. -/
def constantSheafFiniteLocallyConstant : FiniteLocallyConstantSheaf B X :=
  ⟨(constantSheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))).obj (ULift.{u + 1} ι),
    isFiniteLocallyConstant_of_finiteEtaleRepresentable B X _
      ⟨splitObj B X.2 ι, isFinite_hom_splitObj B X.2 ι,
        ⟨constantSheafIsoSheafifiedYonedaSplitObj B X.2 ι⟩⟩⟩

/-- The sheaf represented by the split object of the site is the constant sheaf. -/
def constantSheafFiniteLocallyConstantIso :
    (finiteSmallEtaleToFiniteLocallyConstant B X).obj (splitFiniteSmallEtaleObject B X ι) ≅
      constantSheafFiniteLocallyConstant B X ι :=
  ObjectProperty.isoMk _ (constantSheafIsoSheafifiedYonedaSplitObj B X.2 ι).symm

/-- **Stacks Project, Tag 03RV on a constant sheaf.** The finite étale cover of `X` attached to
the constant sheaf of sets with value a finite set `ι` is the split cover `∐_{i : ι} X`. -/
def finiteEtaleOfConstantSheafIso :
    (finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj
        (constantSheafFiniteLocallyConstant B X ι) ≅
      Stacks.FundamentalGroup.splitCover X.1 ι :=
  (finiteEtaleSiteEquivalence B X).functor.mapIso
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse.mapIso
        (constantSheafFiniteLocallyConstantIso B X ι).symm ≪≫
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.unitIso.app
        (splitFiniteSmallEtaleObject B X ι)).symm) ≪≫
    eqToIso (finiteEtaleFromSmallEtale_splitFiniteSmallEtaleObject B X ι)

variable [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **The étale fundamental group acts trivially on the finite continuous set attached by
Stacks 0BND (1) to a split cover.** -/
theorem rho_eq_one_finiteEtaleEquivalence_splitCover (σ : EtaleFundamentalGroup X.1 x) :
    ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).functor.obj
      (Stacks.FundamentalGroup.splitCover X.1 ι)).obj.ρ σ = 1 := by
  apply FintypeCat.hom_ext
  intro y
  have h := finiteEtaleEquivalenceOfIsGaloisCategory_action X.1 x
    (Stacks.FundamentalGroup.splitCover X.1 ι) σ y
  exact h.trans (Stacks.FundamentalGroup.smul_eq_self_splitCover x ι σ y)

/-- **Stacks Project, Tag 0DV5 (1) on a constant sheaf: the action.** The finite continuous
`π₁(X, x)`-set attached to the constant sheaf of sets with value a finite set carries the
trivial action. -/
theorem rho_eq_one_finiteLocallyConstantSetsEquivalence_constantSheaf
    (σ : EtaleFundamentalGroup X.1 x) :
    ((finiteLocallyConstantSetsEquivalence B X x).functor.obj
      (constantSheafFiniteLocallyConstant B X ι)).obj.ρ σ = 1 :=
  rho_eq_one_contActionUniverseEquivalence _
    (contAction_rho_eq_one_of_iso
      ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).functor.mapIso
        (finiteEtaleOfConstantSheafIso B X ι)).symm
      (rho_eq_one_finiteEtaleEquivalence_splitCover B X ι x)) σ

/-- **Stacks Project, Tag 0DV5 (1) on a constant sheaf: the underlying set.** The finite
continuous `π₁(X, x)`-set attached to the constant sheaf of sets with value a finite set has
that set as its underlying set. -/
def finiteLocallyConstantSetsEquivalenceConstantSheafEquiv :
    ((finiteLocallyConstantSetsEquivalence B X x).functor.obj
      (constantSheafFiniteLocallyConstant B X ι)).obj.V ≃ ι :=
  (FintypeCat.equivEquivIso.symm (contActionIsoV
    ((contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup X.1 x)).functor.mapIso
      ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).functor.mapIso
        (finiteEtaleOfConstantSheafIso B X ι))))).trans
    ((FintypeCat.uSwitchEquiv _).trans (Stacks.FundamentalGroup.splitCoverFiberEquiv x ι))

end AlgebraicGeometry

end
