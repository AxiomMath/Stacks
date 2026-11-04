module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.Algebra.DGA.Cone

/-!
# The mapping cone sequence is admissible short exact

For a homomorphism `f : K ⟶ L` of right differential graded modules, the canonical inclusion
`L ⟶ C(f)` and projection `C(f) ⟶ K[1]` form a short exact sequence which is split as a
sequence of graded modules: the splittings are the two direct-sum coordinate maps of
`C(f) ≅ L ⊕ K`, which respect the grading and the right action but not the differential. Hence
the cone sequence is one of the admissible short exact sequences, and its associated triangle in
the homotopy category is the rotated cone triangle, whose connecting arrow is the shift of the
original homomorphism.

## Main definitions

* `DifferentialGradedModule.mappingConeGradedFst`: the first coordinate of the cone, as a map of
  graded modules; it retracts the cone inclusion.
* `DifferentialGradedModule.mappingConeGradedInr`: the second coordinate injection, as a map of
  graded modules; it is a section of the cone projection.
* `DifferentialGradedModule.mappingConeCompatibleSplittings`: the two coordinate maps, as a
  compatible pair of graded splittings of the cone sequence.

## Main results

* `DifferentialGradedModule.mappingCone_isAdmissibleShortExact`: the cone sequence of `f` is an
  admissible short exact sequence.
* `DifferentialGradedModule.associatedTriangle_mappingCone_eq`: its associated triangle is the
  displayed triangle `L → C(f) → K[1]` whose last arrow is `f[1]`.

## Implementation notes

The two coordinate maps are *not* homomorphisms of differential graded modules — that is exactly
why the cone sequence is only *admissibly* exact — so they are built as `GradedHom`s. They are
defined on the direct-sum model `L ⊕ K` of the cone, whose right action is the product action;
compatibility with the right action is unavailable from the coordinate equivalence of
`Cone`, which is only linear over the base ring.

## References

* [Stacks Project, Tag 09KB](https://stacks.math.columbia.edu/tag/09KB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {K L : DifferentialGradedModule A}

/-- The coordinates of the cone are the identity on its direct-sum model. -/
theorem mappingCone_coordinates_apply (f : K ⟶ L) (x : (coneModule f).M) :
    (cone f).coordinates x = x := rfl

/-- The first direct-sum coordinate of the mapping cone of `f`, as a map of graded modules. It
does not commute with the differentials. -/
noncomputable def mappingConeGradedFst (f : K ⟶ L) : GradedHom (coneModule f) L where
  toFun := LinearMap.fst R L.M K.M
  map_smul _ _ := rfl
  map_grading n x hx := (((cone f).grading_iff n x).mp hx).1

/-- The first coordinate map sends a point of the cone to the first component of its
coordinates. -/
@[simp] theorem mappingConeGradedFst_apply (f : K ⟶ L) (x : (coneModule f).M) :
    (mappingConeGradedFst f).toFun x = ((cone f).coordinates x).1 := rfl

/-- The second direct-sum coordinate injection into the mapping cone of `f`, as a map of graded
modules from the shift `K[1]`. It does not commute with the differentials. -/
noncomputable def mappingConeGradedInr (f : K ⟶ L) :
    GradedHom (shift K 1) (coneModule f) where
  toFun := LinearMap.inr R L.M K.M
  map_smul := by
    intro x a
    change ((0 : L.M), MulOpposite.op a • x) = MulOpposite.op a • ((0 : L.M), x)
    rw [Prod.smul_mk, smul_zero]
  map_grading n x hx := ((cone f).grading_iff n _).mpr ⟨(L.grading n).zero_mem, hx⟩

/-- The second coordinate injection sends `x` to the point of the cone with coordinates
`(0, x)`. -/
@[simp] theorem mappingConeGradedInr_coordinates (f : K ⟶ L) (x : (shift K 1).M) :
    (cone f).coordinates ((mappingConeGradedInr f).toFun x) = (0, x) := rfl

/-- The first coordinate map retracts the cone inclusion. -/
theorem mappingConeGradedFst_mappingConeInclusion (f : K ⟶ L) (x : L.M) :
    (mappingConeGradedFst f).toFun ((coneInclusion f).toFun x) = x := by
  rw [mappingConeGradedFst_apply, (cone f).inclusion_coordinates]

/-- The second coordinate injection is a section of the cone projection. -/
theorem mappingConeProjection_mappingConeGradedInr (f : K ⟶ L) (x : (shift K 1).M) :
    (coneProjection f).toFun ((mappingConeGradedInr f).toFun x) = x := by
  rw [(cone f).projection_apply, mappingConeGradedInr_coordinates]

/-- The composite of the cone inclusion with the cone projection vanishes. -/
theorem mappingConeProjection_mappingConeInclusion (f : K ⟶ L) (x : L.M) :
    (coneProjection f).toFun ((coneInclusion f).toFun x) = 0 := by
  rw [(cone f).projection_apply, (cone f).inclusion_coordinates]

/-- The cone sequence `L ⟶ C(f) ⟶ K[1]` of a homomorphism of differential graded modules is an
admissible short exact sequence. -/
@[stacks 09KB "the admissible short exact sequence"]
theorem mappingCone_isAdmissibleShortExact (f : K ⟶ L) :
    IsAdmissibleShortExact (coneInclusion f) (coneProjection f) where
  injective x y hxy := by
    simpa only [mappingConeGradedFst_mappingConeInclusion] using
      congrArg (mappingConeGradedFst f).toFun hxy
  surjective := fun x =>
    ⟨(mappingConeGradedInr f).toFun x, mappingConeProjection_mappingConeGradedInr f x⟩
  exact := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact LinearMap.mem_ker.mpr (mappingConeProjection_mappingConeInclusion f y)
    · intro hx
      refine ⟨(mappingConeGradedFst f).toFun x, (cone f).coordinates.injective ?_⟩
      rw [(cone f).inclusion_coordinates, mappingConeGradedFst_apply]
      exact Prod.ext rfl
        (((cone f).projection_apply x).symm.trans (LinearMap.mem_ker.mp hx)).symm
  admissibleMono := ⟨mappingConeGradedFst f, mappingConeGradedFst_mappingConeInclusion f⟩
  admissibleEpi := ⟨mappingConeGradedInr f, mappingConeProjection_mappingConeGradedInr f⟩

/-- The two coordinate maps of the cone form a compatible pair of graded splittings of its
sequence: the kernel of the first projection is the image of the second injection. -/
noncomputable def mappingConeCompatibleSplittings (f : K ⟶ L) :
    CompatibleSplittings A (coneInclusion f) (coneProjection f) where
  s := mappingConeGradedInr f
  π := mappingConeGradedFst f
  hs := mappingConeProjection_mappingConeGradedInr f
  hπ := mappingConeGradedFst_mappingConeInclusion f
  hker := by
    ext x
    constructor
    · intro hx
      refine ⟨((cone f).coordinates x).2, (cone f).coordinates.injective ?_⟩
      rw [mappingConeGradedInr_coordinates]
      exact Prod.ext (LinearMap.mem_ker.mp hx).symm rfl
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, mappingConeGradedFst_apply, mappingConeGradedInr_coordinates]

/-- The triangle of the cone sequence of `f` is the displayed triangle `L → C(f) → K[1]` whose
connecting arrow is the shift `f[1]` of `f`. -/
@[stacks 09KB "the associated triangle"]
theorem associatedTriangle_mappingCone_eq (f : K ⟶ L)
    (h : IsAdmissibleShortExact (coneInclusion f) (coneProjection f)) :
    Pretriangulated.Triangle.mk
      ((toHomotopyCategory A).map (coneInclusion f))
      ((toHomotopyCategory A).map (coneProjection f))
      ((toHomotopyCategory A).map (shiftMap f 1) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift (homotopyRel A) ℤ L 1).symm) =
      associatedTriangle A (coneInclusion f) (coneProjection f) h := by
  let c := mappingConeCompatibleSplittings f
  have hδ : (connectingHom (coneInclusion f) (coneProjection f) h
      c.s c.π c.hs c.hπ c.hker).val = shiftMap f 1 := by
    apply Hom.ext
    ext x
    rw [(connectingHom (coneInclusion f) (coneProjection f) h
      c.s c.π c.hs c.hπ c.hker).property x]
    show (((cone f).coordinates
      ((coneModule f).d ((mappingConeGradedInr f).toFun x)))).1 = f.toFun x
    rw [(cone f).differential, mappingConeGradedInr_coordinates]
    simp
  refine Eq.trans ?_ (associatedTriangleOfSplittings_eq A (coneInclusion f) (coneProjection f) h c)
  simp only [associatedTriangleOfSplittings]
  rw [hδ]

end DifferentialGradedModule
