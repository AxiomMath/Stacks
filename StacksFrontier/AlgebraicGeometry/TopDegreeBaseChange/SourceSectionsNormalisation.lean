module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology

/-!
# The source of `γ⁺` on sections: the normalisation at `1 ⊗ x`

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.sourceSectionsIsoTensor` computes the module of
sections of the source `h^* R^d f'_* F'` of the canonical map `γ⁺` of [Stacks, Tag 0EX3] (c) over
an affine open `W` of `Y''` lying inside `h⁻¹(V)` for an affine open `V` of `Y'`: it is the base
change along `Γ(Y', V) ⟶ Γ(Y'', W)` of the degree-`d` cohomology `H^d(f'⁻¹(V), F'|)`.

This file names its two factors. The point of doing so is the normalisation
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` carried by the second of them:
the pure tensor `1 ⊗ x` goes to the **pullback of the section** of `R^d f'_* F'` over `V` that
[Stacks, Tag 01XK] attaches to the cohomology class `x`, in the sense of
`AlgebraicGeometry.Scheme.Modules.pullbackSection`. Together with
`AlgebraicGeometry.Scheme.Modules.pullbackSection_homEquiv` that is what turns a statement about
`γ⁺` on sections into a statement about its adjoint transpose, an ordinary morphism of modules on
`Y'`: the base change is generated over `Γ(Y'', W)` by the elements `1 ⊗ x`, and on those `γ⁺` is
its transpose.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomologyIsoSectionsOf`:
  [Stacks, Tag 01XK] over an affine open of the target, with the finiteness of the morphism, the
  affineness of the open and the quasi-coherence of the module as **explicit** arguments.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sourceSectionsIsoTensor_inv_eq`: the inverse of
  `sourceSectionsIsoTensor`, with its two factors named.

## Implementation notes

*Why the explicit-hypothesis form of 01XK is needed.*
`affineOpenCohomologyIsoSections` takes the finiteness of `f`, the affineness of `V` and the
quasi-coherence of `F` as instance binders, and in a situation none of the three is an instance:
`quasiCompact_f'` and `quasiSeparated_f'` are theorems, the affineness of the open comes as a
hypothesis `IsAffineOpen V`, and the quasi-coherence of `R^d f'_* F'` is [Stacks, Tag 01XJ].
`sourceSectionsIsoTensor` discharges all three inside its own body with `have`s, which is fine
for a `def` but not for a *statement* about it: the statement is elaborated before any tactic
runs, and the three fail to synthesize. `affineOpenCohomologyIsoSectionsOf` takes them in
argument position instead. This is the same cure `targetSectionsIsoCohomology` records for
`hqc` and `hqs`.

*`sourceSectionsIsoTensor_inv_eq` is `rfl`, and is an equality of **morphisms**.*
`Iso.trans`, `Iso.symm` and `Functor.mapIso` all compute their `inv` field on the nose, so the
inverse of
`A.symm ≪≫ B.mapIso C.symm` is `B.map C.hom ≫ A.hom` definitionally. Naming it as a separate
theorem keeps the unfolding out of any consumer. Stating the same identity applied to an
**element** instead is not an option, and this is worth recording because every route to it was
tried and each fails differently: the element-level `rfl` hits `maximum recursion depth`; so does
a `show` of the unfolded composite applied to `1 ⊗ x`; `CategoryTheory.ConcreteCategory.congr_hom`
of the morphism-level identity produces the right hypothesis but `refine h.trans ?_` against it
again hits `maximum recursion depth`; and rewriting the goal with the morphism-level identity
reports the two sheaf spellings, `S.X'.ringCatSheaf` at `TopCat.Sheaf RingCat` against
`Sheaf (Opens.grothendieckTopology _) RingCat`. What every one of these has in common is that the
`Module.compHom` instance on the base change has to be reconciled in the presence of a concrete
element. At the level of morphisms the `rfl` below is instantaneous. A consumer that needs the
value on `1 ⊗ x` should get there with
`ModuleCat.ExtendScalars.hom_ext_one_tmul`, which produces the pure tensor inside a goal where
the module structure is already fixed, and then `ModuleCat.ExtendScalars.map_tmul`.

*No `@[stacks 0EX3]` attribute is placed.* This is a computation of one of the two ends of the
canonical map whose invertibility is conclusion (c), not a conclusion of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 01XK] over an affine open of the target, with explicit hypotheses.** The same
isomorphism as `affineOpenCohomologyIsoSections`, with the finiteness of `f`, the affineness of
`V` and the quasi-coherence of `F` taken in argument position, so that it can appear in the
statement of a lemma about a situation, where none of the three is an instance. -/
def affineOpenCohomologyIsoSectionsOf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f) {V : Y.Opens} (hV : IsAffineOpen V)
    (F : X.Modules) (hF : F.IsQuasicoherent) (d : ℕ) :
    affineOpenCohomology f V F d ≅
      ModuleCat.of Γ(Y, V)
        Γ(((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).obj F, V) :=
  have := hqc
  have := hqs
  have : IsAffine (V : Scheme) := hV
  have := hF
  affineOpenCohomologyIsoSections f V F d

variable {X'' Y'' : Scheme.{u}}

/-- The inverse of `sourceSectionsIsoTensor`, with its two factors named: the base change of
[Stacks, Tag 01XK] over the affine open, followed by the base-change comparison of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
theorem sourceSectionsIsoTensor_inv_eq
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] (h : Y'' ⟶ S.Y')
    {V : S.Y'.Opens} (hV : IsAffineOpen V)
    {W : Y''.Opens} (hW : IsAffineOpen W) (hWV : W ≤ h ⁻¹ᵁ V)
    (hqcoh : (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
      F').IsQuasicoherent) :
    (sourceSectionsIsoTensor S F' h hV hW hWV).inv =
      (ModuleCat.extendScalars (h.appLE V W hWV).hom).map
          (affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f' hV F'
            inferInstance S.d).hom ≫
        (@affinePullbackSectionsBaseChangeIso _ _ h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') hqcoh V hV W hW
          hWV).hom :=
  rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
