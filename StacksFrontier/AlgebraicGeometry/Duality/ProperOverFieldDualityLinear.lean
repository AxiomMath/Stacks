module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedLinear
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.SectionsOverBaseLinear
public import StacksCore.Tactic.StacksAttribute

/-!
# Duality over a field as an isomorphism of `k`-vector spaces

Clause (4) of [Stacks, Tag 0BS2] is proved in
`StacksFrontier/AlgebraicGeometry/Duality/ProperOverFieldDuality.lean` as an isomorphism of
*abelian groups*

  `Ext^i_X(K, ω_X^•) ≃+ Hom_k(H^{-i}(X, K), k)`.

**That form carries no dimension count.** An additive injection into `k` bounds no dimension
over `k`: for `k = ℚ(t)` the group `k ⊕ k` is isomorphic to `k` as an abelian group, both being
`ℚ`-vector spaces of the same infinite dimension. Every finite-dimensionality consequence of
duality — `dim_k H¹(X, ω_X) = 1` of Section [Stacks, Tag 0B5B], for instance — therefore needs
the identification upgraded to an isomorphism of `k`-vector spaces. This file does that.

## The `k`-structure, and where the work is

Both sides are `k`-modules already. The right-hand side is a morphism group of `ModuleCat k`.
The left-hand side is a morphism group of `D(𝒪_X)`, and `𝒪_X` acting on its modules through a
ring map `k ⟶ Γ(X, 𝒪_X)` makes `X.Modules` a `k`-linear category
(`AlgebraicGeometry.Scheme.linearOfRingHom`), which Mathlib's
`CategoryTheory.Linear (DerivedCategory C)` carries to `D(𝒪_X)`.

What is missing is that the two match, and `Stacks.Duality.dualityAddEquivZero_apply` says
exactly what that takes: the identification is `u ↦ H^0(X, u) ≫ trace`, so its `k`-linearity
reduces to `RΓ(X, -) : D(𝒪_X) ⥤ D(k)` being a `k`-linear functor. Mathlib carries `k`-linearity
to a derived functor only for an *exact* functor, and `RΓ(X, -)` is not exact; the transport
along the universal property of a total right derived functor is
`CategoryTheory.Functor.linear_of_isRightDerivedFunctor` of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedLinear.lean`, and this file applies it
to `AlgebraicGeometry.derivedGlobalSectionsOver`, whose underlying
`AlgebraicGeometry.globalSectionsOver` is `k`-linear by
`Stacks.LocalCohomology.sectionsOverBase_linear`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.linearOverBase` — sheaves of modules on a scheme over `A`
  form an `A`-linear category, at the structure map `Stacks.LocalCohomology.baseScalars`.
* `Stacks.Duality.dualityLinearEquivZero` — the duality in degree zero as a `k`-linear
  equivalence, `Hom_{D(𝒪_X)}(K, ω_X^•) ≃ₗ[k] Hom_k(H^0(X, K), k)`.
* `Stacks.Duality.extDualityLinearEquiv` — **clause (4) of [Stacks, Tag 0BS2] as a `k`-linear
  equivalence**, `Ext^i_X(K, ω_X^•) ≃ₗ[k] Hom_k(H^{-i}(X, K), k)`.
* `Stacks.Duality.derivedCohomologyOverFieldDualLinearEquiv` — its target rewritten as the
  `k`-linear functionals on `AlgebraicGeometry.cohomologyOverField`, which is the shape a
  dimension count consumes.

## Main results

* `AlgebraicGeometry.globalSectionsOver_linear_linearOverBase` and
  `AlgebraicGeometry.derivedGlobalSectionsOver_linear` — global sections over the base and their
  total right derived functor are `A`-linear.
* `Stacks.Duality.derivedCohomologyOverField_map_smul_id` — `H^n(X, -)` of multiplication by a
  scalar is multiplication by that scalar.
* `Stacks.Duality.dualityAddEquivZero_smul` and `Stacks.Duality.extDualityAddEquiv_smul` — the
  two identifications of clause (4) commute with the action of `k`.

## Implementation notes

*How the scalar is moved across.* The duality is natural in `K`
(`Stacks.Duality.extDualityAddEquiv_naturality`) and `a • α = (a • 𝟙) ≫ α` in any `R`-linear
category, so naturality at `g = a • 𝟙` turns the scalar on the left into `H^{-i}(X, a • 𝟙)` on
the right, which is `a • 𝟙` because `RΓ(X, -)` and `H^{-i}` are `k`-linear. Nothing about the
four steps the duality composes is needed, only its naturality.

*The `k`-linear structure is a hypothesis, not an instance.* `Linear k X.Modules` cannot be an
instance: the base ring is not determined by the scheme. The statements below therefore take
`[CategoryTheory.Linear k X.Modules]` together with
`[CategoryTheory.Functor.Linear k (AlgebraicGeometry.globalSectionsOver f)]`, the second pinning
the first to the structure morphism; a consumer discharges both with
`AlgebraicGeometry.Scheme.Modules.linearOverBase` and
`AlgebraicGeometry.globalSectionsOver_linear_linearOverBase`, which is the same pattern as
`Stacks.LocalCohomology.sectionsOverBase_linear`.

*`appLE` against `appTop`.* `AlgebraicGeometry.globalSectionsOver` restricts scalars along
`f.appTop` while `Stacks.LocalCohomology.sectionsOverBase` — and hence
`Stacks.LocalCohomology.baseScalars`, the ring map the `A`-linear structure is taken at — uses
`f.appLE ⊤ ⊤`. The two are equal by `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` but not
definitionally, so `AlgebraicGeometry.sectionsOverBase_eq_globalSectionsOver` is that equality
transported to the two functors.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

universe w₁ w₂ u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **Sheaves of modules on a scheme over `A` form an `A`-linear category**, at the structure
map `Stacks.LocalCohomology.baseScalars` along which `A`-linear global sections restrict
scalars. This is `AlgebraicGeometry.Scheme.linearOfRingHom` at that ring map, named so that the
`A`-linear structure used here and by `Stacks.LocalCohomology.sectionsOverBase_linear` is one
and the same. -/
@[instance_reducible]
def Scheme.Modules.linearOverBase : Linear A X.Modules :=
  Scheme.linearOfRingHom X A (Stacks.LocalCohomology.baseScalars A f)

/-- **`A`-linear global sections and sections over the base are the same functor.** Both are
evaluation on the whole space followed by restriction of scalars along the structure map; the
two spellings of that map, `f.appTop` and `f.appLE ⊤ ⊤`, are equal by
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app`. -/
theorem sectionsOverBase_eq_globalSectionsOver :
    Stacks.LocalCohomology.sectionsOverBase.{u, u} A f = globalSectionsOver f :=
  congrArg
    (fun G => _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙ G)
    (congrArg (fun φ => ModuleCat.restrictScalars φ)
      (congrArg (fun m => CommRingCat.Hom.hom m)
        (congrArg (fun m => (Scheme.ΓSpecIso (.of A)).inv ≫ m)
          (Scheme.Hom.appLE_eq_app f (U := ⊤)))))

/-- **`A`-linear global sections is an `A`-linear functor**: a scalar acts on a sheaf of modules
by multiplication by its image in `Γ(X, 𝒪_X)`, and on global sections by that image itself. This
is `Stacks.LocalCohomology.sectionsOverBase_linear` read through
`AlgebraicGeometry.sectionsOverBase_eq_globalSectionsOver`. -/
theorem globalSectionsOver_linear_linearOverBase :
    letI := Scheme.Modules.linearOverBase f
    Functor.Linear A (globalSectionsOver f) :=
  let := Scheme.Modules.linearOverBase f
  sectionsOverBase_eq_globalSectionsOver f ▸
    Stacks.LocalCohomology.sectionsOverBase_linear.{u, u} A f

/-- **Unbounded derived global sections over the base is an `A`-linear functor.** It is the
total right derived functor of `AlgebraicGeometry.globalSectionsOver` along `DerivedCategory.Qh`,
both of which are `A`-linear, so this is
`CategoryTheory.Functor.linear_of_isRightDerivedFunctor`. No exactness of global sections is
involved. -/
instance derivedGlobalSectionsOver_linear [HasDerivedCategory.{w₁} X.Modules]
    [HasDerivedCategory.{w₂} (ModuleCat.{u} A)] [Linear A X.Modules]
    [Functor.Linear A (globalSectionsOver f)] :
    Functor.Linear A (derivedGlobalSectionsOver f) :=
  Functor.linear_of_isRightDerivedFunctor A
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)

end AlgebraicGeometry

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [QuasiCompact f] [QuasiSeparated f] [Linear k X.Modules]
  [Functor.Linear k (globalSectionsOver f)]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **Hypercohomology of multiplication by a scalar is multiplication by that scalar.** Both
`RΓ(X, -)` and `H^n` are `k`-linear, so the composite sends `a • 𝟙` to `a • 𝟙`. -/
theorem derivedCohomologyOverField_map_smul_id (K : DerivedCategory X.Modules) (n : ℤ) (a : k) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
        ((derivedGlobalSectionsOver f).map (a • 𝟙 K)) =
      a • 𝟙 (derivedCohomologyOverField f K n) :=
  (Functor.linear_iff k (derivedGlobalSectionsOver f ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} k) n)).1 inferInstance K a

/-- **The degree-zero duality commutes with the action of `k`.** Writing `a • u` as
`(a • 𝟙) ≫ u` and applying `Stacks.Duality.dualityAddEquivZero_naturality` turns the scalar into
`H^0(X, a • 𝟙)`, which is `a • 𝟙` by
`Stacks.Duality.derivedCohomologyOverField_map_smul_id`. -/
theorem dualityAddEquivZero_smul (K : quasiCoherentDerivedCategory X) (a : k)
    (u : K.obj ⟶ (dualizingComplexOverField f).obj) :
    dualityAddEquivZero f K (a • u) = a • dualityAddEquivZero f K u := by
  have h : a • u = (a • 𝟙 K.obj) ≫ u := by rw [Linear.smul_comp, Category.id_comp]
  rw [h, dualityAddEquivZero_naturality, derivedCohomologyOverField_map_smul_id,
    Linear.smul_comp, Category.id_comp]

/-- **The duality in degree zero as an isomorphism of `k`-vector spaces:**

  `Hom_{D(𝒪_X)}(K, ω_X^•) ≃ₗ[k] Hom_k(H^0(X, K), k)`

for `K` with quasi-coherent cohomology. This is `Stacks.Duality.dualityAddEquivZero` together
with `Stacks.Duality.dualityAddEquivZero_smul`. -/
def dualityLinearEquivZero (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ (dualizingComplexOverField f).obj) ≃ₗ[k]
      (derivedCohomologyOverField f K.obj 0 ⟶ ModuleCat.of k k) where
  __ := dualityAddEquivZero f K
  map_smul' := dualityAddEquivZero_smul f K

/-- **The duality in degree `i` commutes with the action of `k`**, by the same argument as
`Stacks.Duality.dualityAddEquivZero_smul`: `Ext^i_X(K, ω_X^•)` is a morphism group of `D(𝒪_X)`,
so `a • α = (a • 𝟙) ≫ α`, and `Stacks.Duality.extDualityAddEquiv_naturality` moves the scalar
across. -/
theorem extDualityAddEquiv_smul (K : quasiCoherentDerivedCategory X) (i : ℤ) (a : k)
    (α : DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i) :
    extDualityAddEquiv f K i (a • α) = a • extDualityAddEquiv f K i α := by
  have h : a • α = (a • 𝟙 K.obj) ≫ α := by rw [Linear.smul_comp, Category.id_comp]
  rw [h, extDualityAddEquiv_naturality, derivedCohomologyOverField_map_smul_id,
    Linear.smul_comp, Category.id_comp]

/-- **[Stacks, Tag 0BS2], clause (4), as an isomorphism of `k`-vector spaces.** For a
quasi-compact quasi-separated morphism `f : X ⟶ Spec k` and every object `K` of `D_QCoh(𝒪_X)`,

  `Ext^i_X(K, ω_X^•) ≃ₗ[k] Hom_k(H^{-i}(X, K), k)`,

where `ω_X^• = f^×(𝒪_{Spec k})` is the dualizing complex. This is
`Stacks.Duality.extDualityAddEquiv` together with
`Stacks.Duality.extDualityAddEquiv_smul`; the `k`-structure on the left is the one `X.Modules`
carries over the base, and the `k`-linearity is what makes the identification count dimensions
over `k`. -/
@[stacks 0BS2 "clause (4) as an isomorphism of k-vector spaces for the k-linear structure \
over the base, which is what makes it count dimensions over k"]
def extDualityLinearEquiv (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i ≃ₗ[k]
      (derivedCohomologyOverField f K.obj (-i) ⟶ ModuleCat.of k k) where
  __ := extDualityAddEquiv f K i
  map_smul' := extDualityAddEquiv_smul f K i

/-- **The `k`-linear functionals on `Hⁿ(X, ℱ)`, as a `k`-linear equivalence with the morphism
group clause (4) of [Stacks, Tag 0BS2] delivers.** This is
`Stacks.Duality.derivedCohomologyOverFieldDualAddEquiv` as an isomorphism of `k`-vector spaces,
which is the form in which a dimension count consumes the target of clause (4): composed with
`Stacks.Duality.extDualityLinearEquiv` it reads `Ext^i_X(ℱ[0], ω_X^•)` as the `k`-linear dual of
`AlgebraicGeometry.cohomologyOverField k f ℱ n`.

The two steps are the `k`-linear comparison `Hⁿ(X, ℱ) ≃ₗ[k] H^n(X, ℱ[0])` of
`Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField`, which the morphism
group is reindexed along, and `ModuleCat.homLinearEquiv`. The degree is taken as an integer `m`
together with `hm : m = n`, as for the additive form, so that the `-i` of clause (4) can be
matched against the `ℕ`-indexed degree of `AlgebraicGeometry.cohomologyOverField` without
transporting anything. -/
def derivedCohomologyOverFieldDualLinearEquiv (F : X.Modules) (n : ℕ) (m : ℤ) (hm : m = n) :
    (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) m ⟶
        ModuleCat.of k k) ≃ₗ[k] (cohomologyOverField k f F n →ₗ[k] k) := by
  subst hm
  exact (ModuleCat.homLinearEquiv (R := k)).trans (LinearEquiv.arrowCongr
    (cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f F n).symm
    (LinearEquiv.refl k k))

end Stacks.Duality

end
