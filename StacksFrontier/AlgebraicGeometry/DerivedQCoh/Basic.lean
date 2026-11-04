module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasiCoherentAbelian

/-!
# The derived category of quasi-coherent modules on an affine scheme

Stacks 06Z0 asserts that for `X = Spec A` the three functors in the triangle
`D(QCoh(𝒪_X)) → D_QCoh(𝒪_X) → D(A) → D(QCoh(𝒪_X))` are equivalences of triangulated
categories, the last one being `M ↦ M^~` and the middle one `RΓ(X, -)`.

This file supplies the third edge, `D(A) ≌ D(QCoh(𝒪_X))`. Mathlib's
`AlgebraicGeometry.tildeEquiv` is the equivalence of *abelian* categories between `A`-modules and
quasi-coherent `𝒪_{Spec A}`-modules; combined with
`Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` it gives the equivalence of derived
categories. The abelian structure on `QCoh(𝒪_{Spec A})` that makes the right-hand side exist is
`Stacks.DerivedQCoh.abelianQuasiCoherent`.

The predicate defining `D_QCoh(𝒪_X)` as a subcategory of `D(𝒪_X)` is `Stacks.DerivedQCoh.IsDQCoh`.
It is stated for an arbitrary sheaf of rings rather than for a scheme so that it reads the same
whichever of the repository's `rfl`-equal spellings of the structure sheaf of rings is in play.

## Main definitions

* `Stacks.DerivedQCoh.IsDQCoh` is the condition on an object of `D(𝒪_X)` that all its cohomology
  sheaves be quasi-coherent, i.e. membership in `D_QCoh(𝒪_X)`.
* `Stacks.DerivedQCoh.derivedTildeEquiv` is the equivalence
  `D(A) ≌ D(QCoh(𝒪_{Spec A}))` of Stacks 06Z0.
* `Stacks.DerivedQCoh.derivedQCohι` is the functor `D(QCoh(𝒪_{Spec A})) ⥤ D(𝒪_{Spec A})` induced
  by the inclusion of the quasi-coherent modules; this is the functor (06VT) of Stacks 06Z0 at an
  affine scheme.

## Main results

* `Stacks.DerivedQCoh.derivedTildeEquiv` — the `~` edge of the triangle of Stacks 06Z0.
* `Stacks.DerivedQCoh.isDQCoh_of_iso`: `IsDQCoh` only depends on the isomorphism class.
* `Stacks.DerivedQCoh.isDQCoh_Q_obj`: a cochain complex of quasi-coherent modules lands in
  `D_QCoh(𝒪_X)`.
* `Stacks.DerivedQCoh.preservesFiniteLimits_ι_of_finiteProducts` and
  `Stacks.DerivedQCoh.preservesFiniteColimits_ι_of_finiteProducts`: the inclusion of an abelian
  full subcategory is exact.

## Implementation notes

`Stacks.DerivedQCoh.tildeEquiv_functor_additive` is needed because
`AlgebraicGeometry.tildeEquiv.functor` is `CategoryTheory.ObjectProperty.lift` of
`AlgebraicGeometry.tilde.functor`, and instance search does not see through that to the known
additivity of the latter. The cure is the standard one for a full subcategory: additivity
descends along the faithful inclusion, by
`CategoryTheory.Functor.additive_of_comp_faithful`.

Whether `Stacks.DerivedQCoh.derivedQCohι` is fully faithful with essential image the objects
satisfying `IsDQCoh` is Stacks 06VT at an affine scheme and is *not* proved here; neither is the
identification of the quasi-inverse of `derivedTildeEquiv` with `RΓ(X, -)`, which needs a genuine
right derived functor of global sections.

## References

* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Section 36.3 (06VT)](https://stacks.math.columbia.edu/tag/06VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry

universe w w' u u₁ v₁ u₂ v₂ u₃

namespace Stacks.DerivedQCoh

section Subcategory

variable {A : Type u₂} [Category.{v₂} A] [Abelian A] (P : ObjectProperty A) [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]

/-- The inclusion of an abelian full subcategory closed under kernels, cokernels and finite
products preserves finite limits. -/
theorem preservesFiniteLimits_ι_of_finiteProducts : PreservesFiniteLimits P.ι := by
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) P.ι :=
    fun f ↦ P.preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The inclusion of an abelian full subcategory closed under kernels, cokernels and finite
products preserves finite colimits. -/
theorem preservesFiniteColimits_ι_of_finiteProducts : PreservesFiniteColimits P.ι := by
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) P.ι :=
    fun f ↦ P.preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

omit [P.ContainsZero] [P.IsClosedUnderFiniteProducts] in
/-- A complex all of whose terms lie in a full subcategory closed under kernels, cokernels and
isomorphisms has all its cohomology objects in that subcategory. -/
theorem prop_homology [P.IsClosedUnderIsomorphisms] {ι : Type u₃} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (hK : ∀ j, P (K.X j)) (i : ι) : P (K.homology i) := by
  have hker : P (kernel (K.sc i).g) := P.prop_kernel _ (hK _) (hK _)
  exact P.prop_of_iso (ShortComplex.homologyIsoCokernelLift (K.sc i)).symm
    (P.prop_cokernel _ (hK _) hker)

end Subcategory

section IsDQCoh

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (SheafOfModules.{u} R)]

/-- An object of the derived category of `𝒪_X`-modules lies in `D_QCoh(𝒪_X)` when all of its
cohomology sheaves are quasi-coherent. -/
def IsDQCoh (E : DerivedCategory (SheafOfModules.{u} R)) : Prop :=
  ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u} R) i).obj E).IsQuasicoherent

omit [HasBinaryProducts C] in
/-- Membership in `D_QCoh(𝒪_X)` depends only on the isomorphism class, the cohomology sheaves
being functorial. -/
theorem isDQCoh_of_iso {E E' : DerivedCategory (SheafOfModules.{u} R)} (e : E ≅ E')
    (h : IsDQCoh E) : IsDQCoh E' := fun i ↦
  (SheafOfModules.isQuasicoherent R).prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} R) i).mapIso e) (h i)

omit [HasBinaryProducts C] in
/-- A cochain complex of quasi-coherent modules defines an object of `D_QCoh(𝒪_X)`. This is how
objects of `D_QCoh(𝒪_X)` are produced: the cohomology sheaves of such a complex are quasi-coherent
because the quasi-coherent modules are closed under kernels and cokernels. -/
theorem isDQCoh_Q_obj [(SheafOfModules.isQuasicoherent R).IsClosedUnderKernels]
    [(SheafOfModules.isQuasicoherent R).IsClosedUnderCokernels]
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (hK : ∀ j, (K.X j).IsQuasicoherent) :
    IsDQCoh (DerivedCategory.Q.obj K) := fun i ↦
  (SheafOfModules.isQuasicoherent R).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R) i).app K).symm)
    (prop_homology (SheafOfModules.isQuasicoherent R) K hK i)

end IsDQCoh

section Affine

variable (R : CommRingCat.{u})

/-- `AlgebraicGeometry.tildeEquiv.functor` is additive. It is
`CategoryTheory.ObjectProperty.lift` of `AlgebraicGeometry.tilde.functor`, whose additivity
Mathlib knows, and additivity descends along the faithful inclusion of the full subcategory. -/
instance tildeEquiv_functor_additive : (tildeEquiv (R := R)).functor.Additive := by
  have h : ((tildeEquiv (R := R)).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).Additive :=
    Functor.additive_of_iso (F := tilde.functor R) (Iso.refl _)
  exact Functor.additive_of_comp_faithful _
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w'}
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory]

/-- **Stacks Project, Tag 06Z0 (the tilde edge).** For `X = Spec A` the functor `M ↦ M^~` is an
equivalence of triangulated categories from `D(A)` to `D(QCoh(𝒪_X))`. This is the arrow labelled
`~` in the triangle of Stacks 06Z0; the other two edges, the functor (06VT) and `RΓ(X, -)`, are
not treated here.

The underlying functor is `AlgebraicGeometry.tildeEquiv.functor.mapDerivedCategory`, by
definition. -/
@[stacks 06Z0 "the tilde edge: D(A) ≌ D(QCoh(𝒪_X))"]
def derivedTildeEquiv : DerivedCategory (ModuleCat.{u} R) ≌
    DerivedCategory (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  Equivalence.mapDerivedCategory (tildeEquiv (R := R))

/-- The functor underlying `Stacks.DerivedQCoh.derivedTildeEquiv` is the one induced on derived
categories by `AlgebraicGeometry.tildeEquiv.functor`. -/
@[simp]
lemma derivedTildeEquiv_functor :
    (derivedTildeEquiv R).functor = (tildeEquiv (R := R)).functor.mapDerivedCategory :=
  rfl

/-- The inverse of `Stacks.DerivedQCoh.derivedTildeEquiv` is the one induced on derived categories
by `AlgebraicGeometry.tildeEquiv.inverse`, that is by `M ↦ Γ(X, M)`. -/
@[simp]
lemma derivedTildeEquiv_inverse :
    (derivedTildeEquiv R).inverse = (tildeEquiv (R := R)).inverse.mapDerivedCategory :=
  rfl

/-- `Stacks.DerivedQCoh.derivedTildeEquiv` is compatible with the shift, so it is an equivalence
of triangulated and not merely of additive categories. -/
instance : (derivedTildeEquiv R).functor.CommShift ℤ :=
  inferInstanceAs ((tildeEquiv (R := R)).functor.mapDerivedCategory.CommShift ℤ)

/-- `Stacks.DerivedQCoh.derivedTildeEquiv` is a triangulated functor. -/
instance : (derivedTildeEquiv R).functor.IsTriangulated :=
  inferInstanceAs ((tildeEquiv (R := R)).functor.mapDerivedCategory.IsTriangulated)

/-- The inclusion of the quasi-coherent `𝒪_{Spec R}`-modules into all of them is left exact. -/
instance preservesFiniteLimits_ι_isQuasicoherent : PreservesFiniteLimits
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  preservesFiniteLimits_ι_of_finiteProducts _

/-- The inclusion of the quasi-coherent `𝒪_{Spec R}`-modules into all of them is right exact. -/
instance preservesFiniteColimits_ι_isQuasicoherent : PreservesFiniteColimits
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  preservesFiniteColimits_ι_of_finiteProducts _

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (Spec R).ringCatSheaf)]

/-- The functor `D(QCoh(𝒪_{Spec R})) ⥤ D(𝒪_{Spec R})` induced by the inclusion of the
quasi-coherent modules, which is exact. This is the functor labelled (06VT) in the triangle of
Stacks 06Z0, specialised to an affine scheme. -/
def derivedQCohι :
    DerivedCategory (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Spec R).ringCatSheaf) :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).mapDerivedCategory

/-- `Stacks.DerivedQCoh.derivedQCohι` commutes with the shift. -/
instance : (derivedQCohι R).CommShift ℤ :=
  inferInstanceAs
    ((ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf)).mapDerivedCategory.CommShift ℤ)

/-- `Stacks.DerivedQCoh.derivedQCohι` is a triangulated functor. -/
instance : (derivedQCohι R).IsTriangulated :=
  inferInstanceAs
    ((ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf)).mapDerivedCategory.IsTriangulated)

end Affine

end Stacks.DerivedQCoh

end
