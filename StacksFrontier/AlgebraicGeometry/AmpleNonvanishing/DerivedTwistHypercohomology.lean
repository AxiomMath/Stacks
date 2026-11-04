module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CycleHypercohomology

/-!
# A cocycle in the twist makes the twisted hypercohomology nonzero

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `H` a complex of `𝒪_X`-modules. A global
section of the degree-`p` cycles of the termwise twist `p ↦ H^p ⊗_{𝒪_X} L` whose class in the
cohomology sheaf `H^p(H ⊗ L)` is nonzero makes the derived hypercohomology

`H^p(X, Q(H) ⊗^𝐋_{𝒪_X} L[0])`

nonzero.

## Main definitions

* `Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIsoStandard`:
  `K ⊗^𝐋_{𝒪_X} L[0] ≅ Q(p ↦ K^p ⊗_{𝒪_X} L)` at the **standard** model of the derived category.

## Main results

* `Stacks.AmpleNonvanishing.not_isZero_hypercohomology_derivedTensorSingle_of_cycleHom`: a global
  section of the degree-`p` cycles of the termwise twist with nonzero class makes
  `H^p(X, K ⊗^𝐋 L[0])` nonzero.

## Implementation notes

**Why the derived twist is rebuilt here.**
`Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIso` is the same isomorphism at the
*locally small* model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is what
instance search finds in its file; the hypercohomology identification of [Stacks, Tag 08JA] that
the conclusion of [Stacks, Tag 0BQR] is stated through exists only at
`CategoryTheory.HasDerivedCategory.standard`, and a morphism of one model cannot be composed with
a morphism of the other. The derived tensor product of [Stacks, Tag 06YH] carries a *free*
`HasDerivedCategory` binder (`Stacks.Cohomology.TorAmplitude.derTensor`), so its `comparisonRight`
field is available at the standard model verbatim, and the second half of the composite —
`Stacks.AmpleNonvanishing.totalTensorSingleTermwiseIso` — mentions no derived category at all.
So the only thing re-read at the standard model is the one-sided K-flat comparison, with the same
K-flatness input `Stacks.AmpleNonvanishing.kFlat_single_of_isInvertibleModule`.

**The spelling of the derived tensor product.** `Stacks.Duality.derivedTensor X` is an
abbreviation for `(Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor` whose type is
written over `X.Modules`; writing it that way in a statement sends instance search for
`HasDerivedCategory X.Modules` to the *global* locally small instance even with
`CategoryTheory.HasDerivedCategory.standard` installed at priority 10000, and the resulting
`Iso.{u, u+1}` cannot receive the `Iso.{u+1, u+1}` that `comparisonRight` produces. So the derived
tensor product is written out as `derTensor` at the single spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, which is also the spelling the K-flatness
predicate, the total tensor complex and `Stacks.AmpleNonvanishing.termwiseTwist` are stated at.

**The spelling of the unit, and why `≠ 0` depends on it.** The domain of `ψ` is written
`SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)`, the same sheaf of rings
the twist itself is stated over, and *not*
`Stacks.SheafOfModules.structureSheaf X.toRingedSpace.sheaf`, which is the spelling
`Stacks.SheafOfModules.not_isZero_homology_derivedModuleGlobalSections_of_cycleHom` uses. The two
sheaves of rings are definitionally equal, so the statement elaborates either way and the
morphism is passed to that lemma unchanged. But `Tensor.ringSheaf` is a plain `def` while
`structureSheaf` is a reducible abbreviation, and instance search unfolds neither: with the two
spellings mixed, the category instance of the morphism type comes from the twist and the object
from the unit, and `AddCommGroup (M ⟶ N)` can be matched against the pair only by unfolding
`Tensor.ringSheaf`. The numeral `0` of `ψ ≫ homologyπ p ≠ 0` is then rejected for want of
`OfNat _ 0`. Writing both at `Tensor.ringSheaf` removes the mismatch.

For the same reason the cocycle condition fed to that lemma is a term and not a `rw`: its
expected type reads the differential and the inclusion of cycles at the `structureSheaf`
spelling while `Stacks.AmpleNonvanishing.termwiseTwist` carries the other one, so the composition
operators in the goal are not syntactically equal and `rw [Category.assoc]` reports that it
cannot find `(f ≫ g) ≫ h`. `Category.assoc` applied as a term is elaborated at default
transparency, where the two meet.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.AmpleNonvanishing

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived twist by an invertible module is the termwise twist**, at the standard model of
the derived category. This is
`Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIso` re-read at the model the
hypercohomology identification of [Stacks, Tag 08JA] lives at; see the implementation notes. -/
def derivedTensorSingleInvertibleTermwiseIsoStandard (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (K : Stacks.Duality.TensorComplex X) :
    (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj
          (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
            (ComplexShape.up ℤ) 0).obj L))) ≅
      DerivedCategory.Q.obj (termwiseTwist X L K) :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonRight K _
      (kFlat_single_of_isInvertibleModule X L) ≪≫
    DerivedCategory.Q.mapIso (totalTensorSingleTermwiseIso X L K)

/-- **A cocycle in the twist makes the twisted hypercohomology nonzero.** Let `L` be an invertible
`𝒪_X`-module, `H` a complex of `𝒪_X`-modules, `Z` an object of `D(𝒪_X)` isomorphic to the class of
`H`, and `ψ : 𝒪_X ⟶ Z^p(H ⊗ L)` a global section of the degree-`p` cycles of the termwise twist
whose class `ψ ≫ homologyπ p` in the `p`-th cohomology sheaf of the twist is nonzero. Then

`H^p(X, Z ⊗^𝐋_{𝒪_X} L[0]) ≠ 0`. -/
theorem not_isZero_hypercohomology_derivedTensorSingle_of_cycleHom
    (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (H : Stacks.Duality.TensorComplex X) (p : ℤ)
    (Z : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf))
    (eZ : Z ≅ DerivedCategory.Q.obj H)
    (ψ : _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⟶
      (termwiseTwist X L H).cycles p)
    (hψ : ψ ≫ (termwiseTwist X L H).homologyπ p ≠ 0) :
    ¬ IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
      ((derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf)).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj Z).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
              (ComplexShape.up ℤ) 0).obj L))))) :=
  Stacks.SheafOfModules.not_isZero_homology_derivedModuleGlobalSections_of_cycleHom
    X.toRingedSpace.sheaf (termwiseTwist X L H) p ψ hψ
    (fun k _ => (Category.assoc _ _ _).trans
      ((congrArg (fun z => ψ ≫ z)
        ((termwiseTwist X L H).iCycles_d p k)).trans comp_zero)) _
    (((((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor).mapIso eZ).app
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
            (ComplexShape.up ℤ) 0).obj L)) ≪≫
      derivedTensorSingleInvertibleTermwiseIsoStandard X L H).symm)

end Stacks.AmpleNonvanishing

end
