module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# Global sections over a field: functoriality, finiteness, and the codimension of a kernel

`AlgebraicGeometry.globalSectionsOverField k f F` is `Γ(X, ℱ)` regarded as a `k`-vector space,
for `X` a scheme over `k`.  It was introduced as a bare object: there was no induced map on it,
and no finite-dimensionality statement.  Both are one step from results the tree already has, and
both are needed as soon as one wants to *count* sections — for instance to say that the sections
of `ℒ^{⊗ d}` vanishing on a closed subscheme form a subspace of large codimension, which is the
selection step of [Stacks, Tag 0FD8].

## Main results

* `AlgebraicGeometry.globalSectionsOverFieldMap`: the `k`-linear map induced by a morphism of
  modules, with `globalSectionsOverFieldMap_apply` evaluating it as `φ.app ⊤`.  Functoriality is
  not recorded: `globalSectionsOverField` is an object-level definition, and the two equations
  would have to be proved past the spelling of `X.ringCatSheaf` that
  `CategoryTheory.Functor.map_comp` cannot see through.
* `AlgebraicGeometry.finiteDimensional_globalSectionsOverField`: the global sections of a
  coherent module on a proper scheme over a field are finite-dimensional.
* `AlgebraicGeometry.finrank_ker_globalSectionsOverFieldMap_add`: for a surjective map, the
  dimension of the kernel plus the dimension of the target is the dimension of the source — so a
  large target forces a large codimension for the kernel.
* `AlgebraicGeometry.le_finrank_ker_globalSectionsOverFieldMap`: that statement in the form a
  codimension argument consumes.

## Implementation notes

`AlgebraicGeometry.globalSectionsOverField` is `ModuleCat.restrictScalars` of
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, exactly as
`AlgebraicGeometry.cohomologyOverField` is of its right derived functor, so the induced map is
the image of `φ` under that composite and `globalSectionsOverFieldMap_apply` is `rfl`.

Finite-dimensionality is `AlgebraicGeometry.cohomologyOverFieldZeroIso` — the degree-zero
cohomology is the global sections — together with
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`, transported along the
`k`-linear equivalence underlying that isomorphism.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The `k`-linear map on global sections induced by a morphism of `𝒪_X`-modules.** -/
def globalSectionsOverFieldMap {F G : X.Modules} (φ : F ⟶ G) :
    globalSectionsOverField k f F ⟶ globalSectionsOverField k f G :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map φ)

/-- The map `globalSectionsOverFieldMap k f φ` sends a global section `x` to `φ.app ⊤ x`. -/
@[simp] theorem globalSectionsOverFieldMap_apply {F G : X.Modules} (φ : F ⟶ G)
    (x : globalSectionsOverField k f F) :
    globalSectionsOverFieldMap k f φ x = φ.app ⊤ x := rfl

/-- **The global sections of a coherent module on a proper scheme over a field form a
finite-dimensional vector space.** -/
instance finiteDimensional_globalSectionsOverField [IsProper f] (F : X.Modules) [F.IsCoherent] :
    FiniteDimensional k (globalSectionsOverField k f F) :=
  haveI := finiteDimensional_cohomologyOverField_of_isProper k f F 0
  (cohomologyOverFieldZeroIso k f F).toLinearEquiv.finiteDimensional

/-! ### The codimension of the kernel

For a surjective `k`-linear map between finite-dimensional spaces, the codimension of the kernel
is the dimension of the target.  This is what turns "the restriction map to a closed subscheme is
onto, and the subscheme has many sections" into "the sections vanishing on it have large
codimension". -/

variable {k}

/-- **Rank-nullity for the map induced on global sections.**  For a surjective `φ.app ⊤`, the
dimension of the kernel plus the dimension of the target is the dimension of the source. -/
theorem finrank_ker_globalSectionsOverFieldMap_add {F G : X.Modules}
    [FiniteDimensional k (globalSectionsOverField k f F)] (φ : F ⟶ G)
    (hφ : Function.Surjective (globalSectionsOverFieldMap k f φ)) :
    Module.finrank k (LinearMap.ker (globalSectionsOverFieldMap k f φ).hom) +
        Module.finrank k (globalSectionsOverField k f G) =
      Module.finrank k (globalSectionsOverField k f F) := by
  have hrange : Module.finrank k
      (LinearMap.range (globalSectionsOverFieldMap k f φ).hom) =
      Module.finrank k (globalSectionsOverField k f G) := by
    rw [LinearMap.range_eq_top.2 hφ]
    exact finrank_top k (globalSectionsOverField k f G)
  have h := (globalSectionsOverFieldMap k f φ).hom.finrank_range_add_finrank_ker
  omega

/-- **A surjection onto a space of dimension at least `c` has a kernel of codimension at least
`c`.**  This is the shape `Stacks.LinearAlgebra.exists_notMem_biUnion` consumes. -/
theorem le_finrank_ker_globalSectionsOverFieldMap {F G : X.Modules}
    [FiniteDimensional k (globalSectionsOverField k f F)] (φ : F ⟶ G)
    (hφ : Function.Surjective (globalSectionsOverFieldMap k f φ)) (c : ℕ)
    (hc : c ≤ Module.finrank k (globalSectionsOverField k f G)) :
    c + Module.finrank k (LinearMap.ker (globalSectionsOverFieldMap k f φ).hom) ≤
      Module.finrank k (globalSectionsOverField k f F) := by
  have h := finrank_ker_globalSectionsOverFieldMap_add f φ hφ
  omega

end AlgebraicGeometry

end
