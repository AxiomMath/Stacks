module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.IdealActionVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Derived tensor products with a module killed by a sheaf of ideals

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals, `K` an object of `D(O)` and `G` a sheaf
of `O`-modules killed by `I`. Then an upper cohomological bound for `K ⊗^L_O O/I` is an upper
cohomological bound for `K ⊗^L_O G`.

## Main results

* `Stacks.DerivedCategory.IsBoundedAboveBy.of_isSplitMono`: a retract of an object bounded above
  is bounded above.
* `Stacks.Sites.isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero`: an upper bound for
  `K ⊗^L_O O/I` bounds `K ⊗^L_O G` for every sheaf of modules `G` killed by `I`.

## Implementation notes

A module `G` killed by `I` makes `G[0]` a retract of `(O/I)[0] ⊗^L_O G[0]`, because the short
exact sequence `0 → I → O → O/I → 0` tensored with `G[0]` is a distinguished triangle whose
first map vanishes. Tensoring on the left with `K` preserves that retraction, and associativity
of the derived tensor product rewrites the ambient object as `(K ⊗^L_O O/I) ⊗^L_O G[0]`. Since
`G[0]` lies in `D^{≤ 0}` and the derived tensor product is right t-exact, the latter inherits the
bound of `K ⊗^L_O O/I`, and so therefore does its retract `K ⊗^L_O G[0]`.

The hypothesis "`G` is killed by `I`" is used in the form in which the retraction is available:
the vanishing of the ordinary map `I ⊗_O G ⟶ O ⊗_O G`, which under `O ⊗_O G ≅ G` is the
multiplication `a ⊗ g ↦ a · g`.

All the site universes are equal, as they are for the associativity of the derived tensor product
and for its right t-exactness; the universe of the derived category stays independent.

Sheaves of ideals on a ringed site are the submodules of its free rank-one sheaf of modules, so
naming their type requires the structure sheaf to be readable as a sheaf of not necessarily
commutative rings. That holds for every ringed site and is supplied here as a section-local
instance; it is needed only to write the type of a sheaf of ideals down.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **A retract of an object bounded above is bounded above.** Cohomology takes a split
monomorphism to a split monomorphism, and a retract of a zero object is zero. -/
theorem IsBoundedAboveBy.of_isSplitMono {E E' : _root_.DerivedCategory A} (f : E ⟶ E')
    [IsSplitMono f] {b : ℤ} (h : IsBoundedAboveBy E' b) : IsBoundedAboveBy E b := by
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  have h0 : (_root_.DerivedCategory.homologyFunctor A n).map (f ≫ retraction f) = 0 := by
    rw [Functor.map_comp,
      (h n hn).eq_of_tgt ((_root_.DerivedCategory.homologyFunctor A n).map f) 0, zero_comp]
  rw [IsSplitMono.id] at h0
  simpa using h0

end Stacks.DerivedCategory

namespace Stacks.Sites

variable {X : RingedSite.{u, u, u}}

/-- The structure sheaf of a ringed site read as a sheaf of not necessarily commutative rings. -/
local instance instHasSheafComposeForget₂RingCat :
    X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  X.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (I : IdealSubsheaf.{u, u, u} X.O)
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (K : RingedSite.DerivedModules.{u, u, u, d} X)

/-- **An upper bound for `K ⊗^L_O O/I` bounds `K ⊗^L_O G` for every sheaf of modules `G` killed
by `I`.** Such a `G`, placed in degree zero, is a retract of `(O/I)[0] ⊗^L_O G[0]`, which after
tensoring with `K` and reassociating is `(K ⊗^L_O O/I) ⊗^L_O G[0]`; the latter carries the bound
of `K ⊗^L_O O/I` because `G[0]` lies in `D^{≤ 0}`. -/
theorem isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero
    (G : RingedSite.Modules.{u, u, u} X) (b : ℤ)
    (hQ : Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj
          (cokernel I.ι))) b)
    (hG : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app G = 0) :
    Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj G)) b := by
  have hsplit := isSplitMono_unitTensorSingleIso_inv_comp T I G hG
  have hb : Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj ((T.tensor.obj K).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj
            (cokernel I.ι)))).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj G)) b := by
    have h := Stacks.SheafOfModules.DerivedTensorProduct.isBoundedAboveBy_tensor T hQ
      ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj G) 0).2
          inferInstance)
    rwa [add_zero] at h
  exact Stacks.DerivedCategory.IsBoundedAboveBy.of_isSplitMono
    ((T.tensor.obj K).map ((T.unitTensorSingleIso G).inv ≫
        (T.tensor.map ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).map
          (cokernel.π I.ι))).app
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj G)) ≫
      (T.associator K
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj (cokernel I.ι))
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} X) 0).obj G)).inv) hb

end Stacks.Sites

end
