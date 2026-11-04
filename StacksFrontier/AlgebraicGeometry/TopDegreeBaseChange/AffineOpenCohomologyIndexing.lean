module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The cohomology over an affine open in the indexing conclusion (b) is stated at

`AffineOpenSectionsCohomology.lean` computes both ends of the canonical map `γ⁺` of
[Stacks, Tag 0EX3] (c) over a compatible pair of affine opens, and the module it computes them
into is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomology`, the degree-`d` cohomology of
the restriction of the coefficient to `f⁻¹(V)`. That module is built from the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus`, because [Stacks, Tag 01XK] and [Stacks, Tag 01E5] are
stated there. Conclusion (b), on the other hand, is stated about
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeCohomology`, which is built from
the `ℕ`-indexed `CategoryTheory.Functor.rightDerived` through
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.qcohCohomology` — the indexing
`Stacks.EilenbergWatts.iso` runs in.

So the two ends of `γ⁺` and the module conclusion (b) tensors with are not the same object, and
nothing identified them. They differ in exactly two ways, and this file removes both: the
indexing of the right derived functors, crossed by `Stacks.DerivedIndexing.rightDerivedIso`, and
the restriction of scalars — `affineOpenCohomology` restricts along `(f ∣_ V)^♯` and
`topDegreeCohomology` along `algebraMap Γ(V, ⊤) Γ(f'⁻¹(V), ⊤)` for the algebra structure
`Stacks.Cohomology.AffineBase.baseSectionsAlgebra` of the scheme over the affine base — and those
two ring maps are **equal**, not merely isomorphic.

## Main definitions

* `…TopDegreeBaseChange.affineOpenCohomologyNat`: the `ℕ`-indexed reading of
  `affineOpenCohomology`.

## Main results

* `…TopDegreeBaseChange.affineOpenCohomologyNatIso`: the two indexings of the cohomology over an
  affine open of the target agree.
* `Stacks.Cohomology.AffineBase.baseRingToSections_isoSpec_top`: for an affine `Z` and a
  morphism `g : P ⟶ Z`, the base scalars of `P` over `Spec Γ(Z, ⊤)` are `g^♯` itself.
* `…TopDegreeBaseChangeSituation.restrictBase_appTop_eq_algebraMap`: hence, for an affine open
  `V` of the base of a top-degree base-change situation, **the scalars of the restricted
  situation are restricted along `(f' ∣_ V)^♯`** — the ring map `affineOpenCohomology` uses.

## Implementation notes

*Why the ring maps are equal and not merely isomorphic.* `baseSectionsAlgebra` is restriction
along `Stacks.Cohomology.AffineBase.baseRingToSections`, which for
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase` is
`(Scheme.ΓSpecIso (.of Γ(V, ⊤))).inv ≫ ((f' ∣_ V) ≫ V.isoSpec.hom).appTop` read at `⊤`; the
`ΓSpecIso` cancels against `AlgebraicGeometry.Scheme.toSpecΓ_appTop`, leaving `(f' ∣_ V).appTop`.

*Where the two results are composed.* `AffineOpenCohomologyTopDegree.lean` composes them into the
single isomorphism
`…TopDegreeBaseChange.affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology`:
`affineOpenCohomology S.f' V F' S.d` is `topDegreeCohomology` of the situation restricted to `V`,
read over `Γ(Y', V)`. The transport that identifies the two objects is `eqToIso` of a `congrArg`
in the ring map, formed in **term mode**. Reaching the same identification by rewriting does not
work, and that is worth recording: the two abbreviations do not expose their restrictions of
scalars to `rw`, and forcing them open with `simp only` leaves a goal whose type-correctness
fails at `implicit` transparency, because `X.ringCatSheaf` and
`Sheaf (Opens.grothendieckTopology X) RingCat` are two spellings of one thing. A `congrArg` asks
for neither, because the function it is applied to fixes every spelling except the ring map, and
the equality fed to it is an equality of ring maps.

The one thing that does have to be supplied by hand there is the membership proof of the full
subcategory: `SheafOfModules.isQuasicoherent` at the spelling
`((S.restrictBase V).affineBaseOver).left.ringCatSheaf` is not found by instance search, and is
supplied as `inferInstance` ascribed to the type at the `(S.f' ⁻¹ᵁ V : Scheme)` spelling — the
directory's recorded cure that an application crosses a definitional gap where an instance binder
does not.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The `ℕ`-indexed reading of `affineOpenCohomology`.** The degree-`d` cohomology of the
restriction of `F` to `f⁻¹(V)` as a module over `Γ(Y, V)`, with the cohomology taken at Mathlib's
`ℕ`-indexed `CategoryTheory.Functor.rightDerived` — the indexing conclusion (b) of
[Stacks, Tag 0EX3] is stated in. -/
abbrev affineOpenCohomologyNat {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules)
    (d : ℕ) : ModuleCat Γ(Y, V) :=
  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
    ((ModuleCat.restrictScalars (f ∣_ V).appTop.hom).obj
      (((moduleGlobalSections (f ⁻¹ᵁ V : Scheme)).rightDerived d).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))

/-- **The two indexings of the cohomology over an affine open of the target agree.** This is
`Stacks.DerivedIndexing.rightDerivedIso` at the global sections functor of `f⁻¹(V)`, carried
through the two restrictions of scalars that make the cohomology a module over the functions on
the open. -/
def affineOpenCohomologyNatIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules)
    (d : ℕ) : affineOpenCohomologyNat f V F d ≅ affineOpenCohomology f V F d :=
  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapIso
    ((ModuleCat.restrictScalars (f ∣_ V).appTop.hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso
          (moduleGlobalSections (f ⁻¹ᵁ V : Scheme)) d).app
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

namespace Stacks.Cohomology.AffineBase

/-- **The base scalars of a scheme over the spectrum of the functions on an affine target.** For
an affine scheme `Z` and a morphism `g : P ⟶ Z`, read as a scheme over `Spec Γ(Z, ⊤)` through
`AlgebraicGeometry.Scheme.isoSpec`, the ring map
`Stacks.Cohomology.AffineBase.baseRingToSections` at the open `⊤` is `g^♯` itself: the
`Scheme.ΓSpecIso` it is built from cancels against
`AlgebraicGeometry.Scheme.toSpecΓ_appTop`. -/
theorem baseRingToSections_isoSpec_top {P Z : Scheme.{u}} [IsAffine Z] (g : P ⟶ Z) :
    baseRingToSections Γ(Z, ⊤) (Over.mk (g ≫ Z.isoSpec.hom)) (op ⊤) = g.appTop.hom := by
  have hmap : P.ringCatSheaf.obj.map (TopologicalSpace.Opens.leTop (⊤ : P.Opens)).op = 𝟙 _ := by
    rw [show TopologicalSpace.Opens.leTop (⊤ : P.Opens) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  ext r
  simp [baseRingToSections, hmap, Scheme.isoSpec, CommRingCat.of_carrier]
  rfl

end Stacks.Cohomology.AffineBase

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable (S : TopDegreeBaseChangeSituation.{u}) (V : S.Y'.Opens) [IsAffine (V : Scheme)]

/-- **The scalars of the restricted situation are restricted along `(f' ∣_ V)^♯`.** The base of
`S.restrictBase V` is the affine open `V`, so its structure morphism over `Spec Γ(V, ⊤)` is
`(f' ∣_ V) ≫ V.isoSpec.hom` and `baseRingToSections_isoSpec_top` applies. This is what makes the
cohomology module `affineOpenCohomology` and the module
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeCohomology` that conclusion (b)
of [Stacks, Tag 0EX3] tensors with differ by a restriction of scalars along one and the same ring
map. -/
theorem restrictBase_appTop_eq_algebraMap :
    algebraMap (S.restrictBase V).affineBaseRing
        Γ(((S.restrictBase V).affineBaseOver).left, ⊤) = (S.f' ∣_ V).appTop.hom :=
  baseRingToSections_isoSpec_top (S.f' ∣_ V)

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

end
