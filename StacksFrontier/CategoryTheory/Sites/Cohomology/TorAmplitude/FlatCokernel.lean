module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatCokernel
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The lowest cokernel of a bounded above flat complex of Tor amplitude in `[a, b]`

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)`, and let `E` be a
bounded above complex of flat `O`-modules whose image in `D(O)` has Tor amplitude in `[a, b]`.
Then the cokernel of the differential `E^{a-1} ⟶ E^a` is a flat `O`-module. This is the step
which, applied to a flat resolution, produces a *bounded* flat representative of an object of
Tor amplitude in `[a, b]`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.exactAt_rowComplex_of_hasTorAmplitude`: below `a`
  the termwise tensor complex `p ↦ E^p ⊗_O F` is exact, for every `O`-module `F`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude`: the cokernel
  of `d^{a-1}` is flat.

## Implementation notes

The mathematical content is Lazard-style: for every `O`-module `F` the complex `E^• ⊗_O F` is
exact in degrees `< a`, because the degree-`i` cohomology of `E ⊗^L_O F[0]` is computed by that
complex — `E` being K-flat, by Stacks 06YQ — and vanishes by the Tor-amplitude hypothesis.
Exactness at `a - 1` says that the three-term complex
`E^{a-2} ⊗ F ⟶ E^{a-1} ⊗ F ⟶ E^a ⊗ F` is exact for every `F`, and that is exactly what makes
`- ⊗_O Coker(d^{a-1})` preserve monomorphisms. Preserving monomorphisms plus right exactness
gives exactness, by
`CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels`.

The diagram chase behind that step,
`Stacks.Cohomology.TorAmplitude.FlatCokernel.preservesMonomorphisms_tensor_cokernel`, and the
identification of `Tot(E ⊗_O F[0])` with the termwise complex,
`CochainComplex.KFlatBifunctor.totalSingleIso`, are both stated for an arbitrary abelian
category and an arbitrary bifunctor, so nothing is reproved here: the ringed-space form of this
theorem and this one are two applications of the same two lemmas.

Flatness is exactness of tensoring on the *right*, while the functors above tensor on the left;
the two are exchanged by the braiding `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.

All four universes are free: the site's objects and morphisms, the sections of the structure
sheaf and of the modules, and the derived category's own hom universe. That is possible because
Tor amplitude is stated against a given derived tensor product datum `T` rather than against a
canonical choice, whose construction is only available on a diagonal.

## References

* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

-- The sections universe `w` is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]

/-- **A K-flat complex of Tor amplitude in `[a, b]` has exact termwise tensor products below
`a`.** The degree-`i` cohomology of `K ⊗^L_O F[0]` is the degree-`i` cohomology of
`Tot(K ⊗_O F[0])`, because `K` is K-flat, and that total complex is the termwise complex
`p ↦ K^p ⊗_O F`. -/
theorem exactAt_rowComplex_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} X)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (a b i : ℤ)
    (hKflat : IsKFlat X.O K)
    (hamp : HasTorAmplitude T (DerivedCategory.Q.obj K) a b)
    (F : RingedSite.Modules.{u, v, w} X) (hi : i < a) :
    (CochainComplex.KFlatBifunctor.rowComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F).ExactAt i := by
  let F₀ := (HomologicalComplex.single (RingedSite.Modules.{u, v, w} X)
    (ComplexShape.up ℤ) 0).obj F
  let L := ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj F₀
  have hExact : L.ExactAt i := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have e : L.homology i ≅
        (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
          ((T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj F₀)) :=
      ((DerivedCategory.homologyFunctorFactors
          (RingedSite.Modules.{u, v, w} X) i).app L).symm ≪≫
        (DerivedCategory.homologyFunctor
            (RingedSite.Modules.{u, v, w} X) i).mapIso
          (T.comparisonLeft K F₀ hKflat).symm
    exact (hamp F i fun h => not_le.2 hi h.1).of_iso e
  exact hExact.of_iso
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F)

/-- **Stacks 08G0.** The cokernel of the differential into the lowest degree of the
Tor-amplitude interval of a bounded above complex of flat `O`-modules is a flat `O`-module.

The complex is K-flat by Stacks 06YQ, so the Tor-amplitude hypothesis makes the three-term
complex `K^{a-2} ⊗ F ⟶ K^{a-1} ⊗ F ⟶ K^a ⊗ F` exact for every `O`-module `F`. Hence
`Coker(d^{a-1}) ⊗ -` preserves monomorphisms, and being right exact as well it is exact. -/
@[stacks 08G0 "variant: Tor amplitude measured against a derived tensor product datum `T` on \
D(O); the tag is \
Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude_canonical"]
theorem isFlat_cokernel_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} X)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (a b : ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K.X i))
    (hamp : HasTorAmplitude T (DerivedCategory.Q.obj K) a b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O)
      (cokernel (K.d (a - 1) a)) := by
  let T' := Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O
  let S := K.sc' (a - 2) (a - 1) a
  have _ : ∀ M, PreservesFiniteColimits (T'.obj M) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X.O
  have _ : ∀ M, PreservesFiniteColimits (T'.flip.obj M) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj X.O
  have _ : PreservesFiniteLimits (T'.obj S.X₂) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.O (hflat (a - 1))).1
  have _ : PreservesFiniteLimits (T'.obj S.X₃) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.O (hflat a)).1
  have hS (M : RingedSite.Modules.{u, v, w} X) : (S.map (T'.flip.obj M)).Exact :=
    (HomologicalComplex.exactAt_iff' _ (a - 2) (a - 1) a
      ((ComplexShape.up ℤ).prev_eq' (show a - 2 + 1 = a - 1 by omega))
      ((ComplexShape.up ℤ).next_eq' (show a - 1 + 1 = a by omega))).1
      (exactAt_rowComplex_of_hasTorAmplitude T K a b (a - 1)
        (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O K hbound hflat) hamp M
        (by omega))
  have _ := Stacks.Cohomology.TorAmplitude.FlatCokernel.preservesMonomorphisms_tensor_cokernel
    T' S hS
  have _ : ∀ {M N : RingedSite.Modules.{u, v, w} X} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (T'.obj (cokernel S.g)) := fun _ =>
    ((Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X.O
      (cokernel S.g)).preservesFiniteColimits WalkingParallelPair).preservesColimit
  have _ := Functor.preservesHomology_of_preservesMonos_and_cokernels (T'.obj (cokernel S.g))
  have _ : ∀ {M N : RingedSite.Modules.{u, v, w} X} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (T'.obj (cokernel S.g)) :=
    fun f => Functor.PreservesHomology.preservesKernel _ f
  have h : exactFunctor _ _ (T'.obj (cokernel S.g)) := by
    rw [exactFunctor_iff]
    exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _, inferInstance⟩
  exact Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip X.O _
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).app (cokernel S.g)) h)

end Stacks.SheafOfModules.DerivedTensorProduct

end
