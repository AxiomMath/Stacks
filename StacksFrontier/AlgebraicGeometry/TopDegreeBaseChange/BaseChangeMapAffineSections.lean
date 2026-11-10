module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# The ends of the base-change map of [Stacks, Tag 0EX3] (c) over an affine open

`BaseChangeMapSections.lean` reduces conclusion (c) of [Stacks, Tag 0EX3] to the bijectivity of

> `Γ(W, γ⁺) : Γ(W, h^* R^d f'_* F') ⟶ Γ(W, R^d f''_* (h')^* F')`

for the affine opens `W` of `Y''` lying over an affine open `V` of `Y'`
(`isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`). The source proves that
by computing both of those modules as top-degree cohomology groups and comparing them by
conclusion (b). Computing them needs [Stacks, Tag 01XK] — *the cohomology of a quasi-coherent
module is the global sections of its higher direct image* — over an affine **open** of the
target, whereas the library's form of that tag,
`Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward`, is stated for
a morphism whose target is an affine **scheme**.

This file supplies the open form, by composing that tag with the restriction comparison of
[Stacks, Tag 01E5], and reads it at the two ends of `γ⁺`. The restriction comparison is the
scheme-level, `ℤ`-indexed
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, so no transport
between the two models of `Rf_*` intervenes: both ends of `γ⁺` are already stated at
`CategoryTheory.Functor.rightDerivedPlus`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineOpenCohomologyIsoSectionsRightDerivedPlus`:
  **[Stacks, Tag 01XK] over an affine open of the target.** For a quasi-compact quasi-separated
  `f : X ⟶ Y`, an affine open `V` of `Y` and a quasi-coherent module `F` on `X`, the degree-`d`
  cohomology `H^d(f⁻¹(V), F|_{f⁻¹(V)})` is the module of sections of `R^d f_* F` over `V`. The
  target `Y` of `f` carries **no** hypothesis.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sourceCohomologyIsoSections_topDirectImage`: the
  factor of the source of `γ⁺` over the affine open `V` of `Y'`, computed: the sections of
  `R^d f'_* F'` over `V` are `H^d(f'⁻¹(V), F'|)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.targetCohomologyIsoSections_topDirectImage`: the
  target of `γ⁺`, computed over the affine open `W` of `Y''`: the sections of
  `R^d f''_* ((h')^* F')` over `W` are `H^d(f''⁻¹(W), ((h')^* F')|)`.

## Implementation notes

*Which spelling of the sections.* The two results are stated with the sections of a module `N` on
`Y` over `V` written as the global sections of its restriction,
`(moduleGlobalSections ↑V).obj ((Scheme.Modules.restrictFunctor V.ι).obj N)`, and not as
`N.val.app (op V)`. The two carriers are the same abelian group — `Γ(N.restrict V.ι, ⊤)` is
`Γ(N, V.ι ''ᵁ ⊤)` and `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` — but their
*module* structures sit over the two rings `Γ(V, ⊤)` and `Γ(Y, V)`, which are again the same ring
only up to the restriction map `AlgebraicGeometry.Scheme.Opens.topIso` along the propositional
equality `V.ι ''ᵁ ⊤ = V`. The restriction spelling is the one the comparison of [Stacks, Tag 01E5]
produces, and keeping it means no transport along that equality appears here; see *What is not
proved* for the one place where the other spelling is needed.

## What is not proved

Conclusion (c) of [Stacks, Tag 0EX3]. With the two computations above, what remains of it is
three steps, and **only the last of them is conclusion (b)**; in particular (c) does not follow
from (b) alone, which is what a previous reading of this directory assumed.

* *The change of spelling of the sections.* `γ⁺` is met on sections as
  `(topDirectImageBaseChangeMapPlus …).val.app (op W)`, a map of `Γ(Y'', W)`-modules, while the
  two computations above are stated at the restriction spelling. Bridging them is the transport
  along `W.ι ''ᵁ ⊤ = W`, semilinear over `AlgebraicGeometry.Scheme.Opens.topIso`; the additive
  half is `M.presheaf.map (eqToHom W.ι_image_top).op` conjugated as in
  `topReading` (`TensorComparisonSections.lean`), the semilinearity is
  `AlgebraicGeometry.Scheme.Modules.map_smul`, the two scalar actions agree on the nose by
  `AlgebraicGeometry.Scheme.Opens.ι_appIso`, and the pattern to follow is
  `AlgebraicGeometry.affineSectionsLinearEquiv`
  (`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/AffineSections.lean`), which does the same
  job for `IsAffineOpen.fromSpec` in place of `V.ι`.

  What that bridge costs is one definitional identification which
  this module system does not perform: the `Γ(V, ⊤)`-module structure on the global sections of a
  restriction as `moduleGlobalSections` produces it — through
  `SheafOfModules.evaluation V.ringCatSheaf (op ⊤)` — against Mathlib's
  `Module Γ(X, V.ι ''ᵁ ⊤) Γ(M, V.ι ''ᵁ ⊤)`, which is `(M.val.obj (op (V.ι ''ᵁ ⊤))).isModule`. The
  two are the same structure, but a scalar equation stated at one of them is rejected at the
  other with *the following definitions were not unfolded because their definition is not
  exposed*, so neither `ModuleCat.restrictScalars` along the ring map nor `Module.compHom` of it
  gives a `Γ(X, V)`-linear map out of those sections: the `map_smul'` field does not typecheck in
  either direction. What is needed first is a `rfl`-lemma identifying the two module
  structures — the analogue, for `moduleGlobalSections`, of
  `AlgebraicGeometry.Scheme.Modules.restrictAppIso` being `Iso.refl` at the level of the
  underlying groups. Raising transparency is not a route: the definitions are not merely
  semireducible but unexposed.
* *The source of `γ⁺` as a tensor product.* `Γ(W, h^* R^d f'_* F')` is
  `Γ(W, ⊤) ⊗_{Γ(V, ⊤)} Γ(V, R^d f'_* F')`, and this is **proved**:
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
  (`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`) is exactly that statement for a
  quasi-coherent module and a compatible pair of affine opens, with
  `…affinePullbackSectionsBaseChangeIso_one_tmul` normalising it. It is stated in the
  `Γ(N, V)` spelling, so it consumes the bridge of the previous item.
* *The comparison of the two cohomology groups.* After the two items above, (c) over `W` is the
  assertion that `γ⁺` carries
  `H^d(f'⁻¹(V), F'|) ⊗_{Γ(V, ⊤)} Γ(W, ⊤)` to `H^d(f''⁻¹(W), ((h')^* F')|)`. Conclusion (b)
  supplies the left-hand side: it is `Φ(Γ(W, ⊤))` for the Eilenberg-Watts functor
  `Φ = M ↦ H^d(f'⁻¹(V), F'| ⊗ (f' ∣_ V)^* M~)` of
  `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase`, and that identification
  is unconditional — `…restrictBaseTopDegreeTensorCohomologyLinearEquiv` in
  `EilenbergWattsUnitor.lean`. What (b) does not supply in any form is the identification
  of `Φ(Γ(W, ⊤))` with `H^d(f''⁻¹(W), ((h')^* F')|)`: that is the source's own two further
  steps, *"since `h'` is affine"*. **Both of those steps are in this tree.** The Leray comparison
  `H^d(X'', (h')^* F') = H^d(X', h'_* (h')^* F')`
  along an affine morphism is `…TopDegreeBaseChange.cohomologyPullbackIsoPushforward`
  (`BaseChangeAffineLeray.lean`), [Stacks, Tag 089W] itself and not merely the vanishing of
  [Stacks, Tag 01XC]; the projection formula `h'_* (h')^* F' = F' ⊗ (f')^* R''~` is
  `…TopDegreeBaseChange.pushforwardPullbackTensorIso`
  (`BaseChangeAffineProjectionFormula.lean`); and the two are composed over a compatible pair of
  affine opens, in the tensor order (b) is stated in, as
  `…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens`
  (`BaseChangeAffineOpenTensorCohomology.lean`). What remains is still not a consequence of (b):
  it is the identification of `γ⁺` itself with that composite.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 01XK] over an affine open of the target.** For a quasi-compact and
quasi-separated morphism `f : X ⟶ Y` of schemes, an affine open `V` of `Y` and a quasi-coherent
module `F` on `X`, the degree-`d` cohomology of the restriction of `F` to `f⁻¹(V)` is the module
of sections of `R^d f_* F` over `V`, as modules over `Γ(V, ⊤)`.

The library's form of the tag asks the target of the morphism to be an affine *scheme*; here `Y`
carries no hypothesis at all and only the open `V` is affine. The two are related by the
restriction comparison of [Stacks, Tag 01E5]: the tag applies to `f ∣_ V`, whose target is the
affine scheme `V`, and computes the cohomology of `F|_{f⁻¹(V)}` as the global sections of
`R^d (f ∣_ V)_* (F|_{f⁻¹(V)})`, which
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` identifies with
the restriction of `R^d f_* F` to `V`. -/
def affineOpenCohomologyIsoSectionsRightDerivedPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) [IsAffine (V : Scheme)]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ) :
    (ModuleCat.restrictScalars (f ∣_ V).appTop.hom).obj
        (((moduleGlobalSections (f ⁻¹ᵁ V : Scheme)).rightDerivedPlus (d : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≅
      (moduleGlobalSections (V : Scheme)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).obj F)) :=
  (cohomologyIsoGlobalSectionsRightDerivedPushforward (f ∣_ V) (d : ℤ)).app
      ⟨(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F, inferInstance⟩ ≪≫
    (moduleGlobalSections (V : Scheme)).mapIso (rightDerivedPlusRestrictObjIso f V d F)

variable {X'' Y'' : Scheme.{u}}

/-- **The `V`-factor of the source of `γ⁺`, computed.** The source of the canonical map of
[Stacks, Tag 0EX3] (c) is the pullback along `h` of `R^d f'_* F'`, and its sections over an
affine open `W` of `Y''` lying over an affine open `V` of `Y'` are built from the sections of
`R^d f'_* F'` over `V` (see the *What is not proved* note of this module). Those are the
top-degree cohomology of `F'` over `f'⁻¹(V)`.

This is `affineOpenCohomologyIsoSectionsRightDerivedPlus` at the base-changed morphism of the
situation; the finiteness hypotheses are the ones the situation carries. -/
def sourceCohomologyIsoSections_topDirectImage
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] (V : S.Y'.Opens) [IsAffine (V : Scheme)] :
    (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).obj
        (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) ≅
      (moduleGlobalSections (V : Scheme)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')) :=
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  affineOpenCohomologyIsoSectionsRightDerivedPlus S.f' V F' S.d

/-- **The target of `γ⁺`, computed over an affine open of `Y''`.** The target of the canonical
map of [Stacks, Tag 0EX3] (c) is `R^d f''_* ((h')^* F')`, and its sections over an affine open
`W` of `Y''` are the top-degree cohomology of `(h')^* F'` over `f''⁻¹(W)`.

The coefficient is quasi-coherent by [Stacks, Tag 01BG], and the finiteness of `f''` is taken as
an explicit argument, as in `isQuasicoherent_target_topDirectImageBaseChangeMapPlus`, so that a
consumer whose morphism is only definitionally the one in hand can supply it in argument
position. -/
def targetCohomologyIsoSections_topDirectImage
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    (W : Y''.Opens) [IsAffine (W : Scheme)] :
    (ModuleCat.restrictScalars (f'' ∣_ W).appTop.hom).obj
        (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
            ((Scheme.Modules.pullback h').obj F'))) ≅
      (moduleGlobalSections (W : Scheme)).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'))) :=
  have := hqc
  have := hqs
  have := AffineBaseChange.isQuasicoherent_pullback h' F'
  affineOpenCohomologyIsoSectionsRightDerivedPlus f'' W
    ((Scheme.Modules.pullback h').obj F') S.d

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
