module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChangeConormal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalCompatibility
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeTowerConormal
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange

/-!
# The excess conormal sheaf of a base change lies in the kernel of the first arrow

Let `g' ≫ f = f' ≫ g` be a cartesian square of schemes and `f = h ∘ i` a factorization of `f`
with `i : X ⟶ P` an immersion and `h : P ⟶ Y` smooth, with base change `f' = h' ∘ i'` through
`P' = P ×_Y Y'` (`Stacks.Chow.SmoothFactorization.baseChange`). The proof of Stacks 0FV9 compares
the two rows

```
(g')^*𝒞_{X/P} ---(g')^*δ---> (g')^*i^*Ω_{P/Y}
      |                             |
      c                             θ
      v                             v
  𝒞_{X'/P'} -------δ'-------> i'^*Ω_{P'/Y'}
```

where `δ`, `δ'` are the first arrows of the conormal sequences of [Stacks Project, Tag 01UZ],
`c` is the surjection of [Stacks Project, Tag 0473] and `θ` is induced by the identification
`p^*Ω_{P/Y} ≅ Ω_{P'/Y'}` of [Stacks Project, Tag 01V0]. This file proves that the square commutes
and that `θ` is an isomorphism, and deduces that the kernel of `c` — the excess conormal sheaf
`Stacks.Chow.SmoothFactorization.baseChangeExcessConormal` — lies in the kernel of `(g')^*δ`.

## Main results

* `Stacks.Chow.SmoothFactorization.baseChangeConormalMap_comp_conormalDifferential`: the square
  commutes.
* `Stacks.Chow.SmoothFactorization.isIso_baseChangeDifferentialsMap`: its right-hand edge is an
  isomorphism.
* `Stacks.Chow.SmoothFactorization.kernel_ι_baseChangeConormalMap_comp_conormalDifferential`:
  the excess conormal sheaf is killed by the pulled-back first arrow.
* `Stacks.Chow.SmoothFactorization.kernelConormalDifferentialιCompIso`: consequently it is the
  kernel of the restriction of `c` to the kernel of `(g')^*δ`.
* `Stacks.Chow.SmoothFactorization.kernelTwoStepPullbackConormalDifferentialIso`: the kernel of
  `(g')^*δ` in the two-step model of the pullback, which is the target of
  `Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso`, is the kernel of
  `(g')^*δ` in the model `c` is stated with.
* `Stacks.Chow.SmoothFactorization.kernelHomologyMapNegOneBaseChangeMapIso`: the sheaf
  `𝒞 = Ker(H^{-1}((g')^*NL_{X/Y}) ⟶ H^{-1}(NL_{X'/Y'}))` of [Stacks Project, Tag 0FV9], for the
  base change map of [Stacks Project, Tag 0FV5], is the excess conormal sheaf.
* `Stacks.Chow.isFiniteLocallyFree_kernel_homologyMap_baseChangeMapOfComparison`: **the first
  assertion of [Stacks Project, Tag 0FV9]**: for `f` and `f'` local complete intersection
  morphisms and the Gysin map existing for `f`, the sheaf `𝒞` is finite locally free.

## Implementation notes

The first arrow `δ` lives on the presentation of the conormal sheaf through the sectionwise ideal
of the closed factor of `i`, and `c` on the presentation through the categorical kernel; the two
are compared through `Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge`, as in
`Stacks.ConormalSequenceRight.immersionConormalSheafMap_comp_conormalDifferential`.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 0FV1](https://stacks.math.columbia.edu/tag/0FV1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

namespace SmoothFactorization

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

/-- The map `θ : (g')^*i^*Ω_{P/Y} ⟶ i'^*Ω_{P'/Y'}` of the base-changed factorization, induced by
the canonical map `p^*Ω_{P/Y} ⟶ Ω_{P'/Y'}` of the projection `p : P' ⟶ P`. -/
noncomputable abbrev baseChangeDifferentialsMap (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) :
    (Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pullback F.imm).obj (Scheme.Hom.relativeDifferentials F.proj)) ⟶
      (Scheme.Modules.pullback (F.baseChange hsq).imm).obj
        (Scheme.Hom.relativeDifferentials (F.baseChange hsq).proj) :=
  Stacks.ConormalSequenceRight.pullbackSquareDifferentialsMap F.imm (F.baseChange hsq).imm g'
    (pullback.fst F.proj g) (F.baseChangeImm_fst hsq.w) F.proj (pullback.snd F.proj g) g
    pullback.condition

/-- **The two first arrows are compatible with base change.** The map
`c : (g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` followed by the first arrow of `i'` is the pullback of the first
arrow of `i` followed by `θ`. -/
theorem baseChangeConormalMap_comp_conormalDifferential (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) :
    (F.baseChangeConormalMap hsq ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge (F.baseChange hsq).imm).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential (F.baseChange hsq).imm
            (F.baseChange hsq).proj :
        (Scheme.Modules.pullback g').obj (Stacks.Conormal.conormalSheaf F.imm) ⟶ _) =
      (Scheme.Modules.pullback g').map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj) ≫
        F.baseChangeDifferentialsMap hsq :=
  Stacks.ConormalSequenceRight.immersionConormalSheafMap_comp_conormalDifferential F.imm
    (F.baseChange hsq).imm g' (pullback.fst F.proj g) (F.baseChangeImm_fst hsq.w) F.proj
    (pullback.snd F.proj g) g pullback.condition

/-- **The right-hand edge is an isomorphism**: the canonical map `p^*Ω_{P/Y} ⟶ Ω_{P'/Y'}` is an
isomorphism because `P' = P ×_Y Y'` (Stacks 01V0), and the other factors of `θ` are the
pseudofunctoriality isomorphisms of the pullback. -/
theorem isIso_baseChangeDifferentialsMap (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) : IsIso (F.baseChangeDifferentialsMap hsq) :=
  (((Scheme.Modules.pullbackComp g' F.imm).app _) ≪≫
    ((Scheme.Modules.pullbackCongr (F.baseChangeImm_fst hsq.w).symm).app _) ≪≫
    ((Scheme.Modules.pullbackComp (F.baseChange hsq).imm (pullback.fst F.proj g)).app _).symm ≪≫
    (Scheme.Modules.pullback (F.baseChange hsq).imm).mapIso
      (@asIso _ _ _ _ (Scheme.Hom.relativeDifferentialsMap (pullback.fst F.proj g) F.proj
        (pullback.snd F.proj g) g pullback.condition)
        (Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback (pullback.fst F.proj g)
          (pullback.snd F.proj g) F.proj g (IsPullback.of_hasPullback F.proj g)))).isIso_hom

/-- **The excess conormal sheaf is killed by the pulled-back first arrow.** The kernel of
`c : (g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` is contained in the kernel of `(g')^*δ`: on it,
`(g')^*δ ≫ θ = c ≫ δ'` vanishes, and `θ` is an isomorphism. -/
theorem kernel_ι_baseChangeConormalMap_comp_conormalDifferential (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) :
    (kernel.ι (F.baseChangeConormalMap hsq) ≫
        (Scheme.Modules.pullback g').map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj) :
        F.baseChangeExcessConormal hsq ⟶ _) = 0 := by
  have := F.isIso_baseChangeDifferentialsMap hsq
  refine (cancel_mono (F.baseChangeDifferentialsMap hsq)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => kernel.ι (F.baseChangeConormalMap hsq) ≫ t)
    (F.baseChangeConormalMap_comp_conormalDifferential hsq).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _) (kernel.condition (F.baseChangeConormalMap hsq))).trans ?_
  exact zero_comp.trans zero_comp.symm

/-- **The excess conormal sheaf is the kernel of `c` restricted to the kernel of the pulled-back
first arrow** `(g')^*δ : (g')^*𝒞_{X/P} ⟶ (g')^*i^*Ω_{P/Y}`. -/
noncomputable def kernelConormalDifferentialιCompIso (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) :
    kernel (kernel.ι ((Scheme.Modules.pullback g').map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj)) ≫
        F.baseChangeConormalMap hsq) ≅
      F.baseChangeExcessConormal hsq :=
  Stacks.NaiveCotangentPulledImmersion.kernelιCompIsoOfKernelιComp _ _
    (F.kernel_ι_baseChangeConormalMap_comp_conormalDifferential hsq)

/-- The pullback along `g'` of the first arrow of `i`, in the two-step model of the pullback
that `Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso` is stated with, is
the pullback of the first arrow read on the categorical presentation of the conormal sheaf,
conjugated by isomorphisms. -/
theorem twoStepPullback_map_conormalDifferential (F : SmoothFactorization f) (g' : X' ⟶ X) :
    (twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj) =
      (((modulePullbackIsoTwoStep g'.toLRSHom.toShHom).app _).symm ≪≫
          (modulePullback g'.toLRSHom.toShHom).mapIso
            (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm)).hom ≫
        (modulePullback g'.toLRSHom.toShHom).map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm).inv ≫
            Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj) ≫
        ((modulePullbackIsoTwoStep g'.toLRSHom.toShHom).app _).symm.inv :=
  Stacks.NaiveCotangentPulledImmersion.map_eq_conj_of_iso _ _ _

/-- **The kernel of the pulled-back first arrow, in the two models.** The target of
`Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso` is the kernel of the
pullback along `g'` of the first arrow of `i` read on the categorical presentation of the
conormal sheaf. -/
noncomputable def kernelTwoStepPullbackConormalDifferentialIso (F : SmoothFactorization f)
    (g' : X' ⟶ X) :
    kernel ((twoStepPullback g'.toLRSHom.toShHom).map
        (Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj)) ≅
      kernel ((modulePullback g'.toLRSHom.toShHom).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge F.imm).inv ≫
          Stacks.ConormalSequenceRight.conormalDifferential F.imm F.proj)) :=
  Stacks.NaiveCotangentPulledImmersion.kernelTwoStepPullbackIso F.imm F.proj g'

/-- **The sheaf `𝒞` of [Stacks Project, Tag 0FV9] is the excess conormal sheaf.** For a
cartesian square `g' ≫ f = f' ≫ g` and a factorization `f = h ∘ i` through a smooth morphism,
the kernel of the map `H^{-1}((g')^*NL_{X/Y}) ⟶ H^{-1}(NL_{X'/Y'})` induced by the base change
map of [Stacks Project, Tag 0FV5] is the kernel of `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}`: through the
identifications of [Stacks Project, Tag 0FV4] the map on `H^{-1}` is the restriction of
`(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` to the kernel of `(g')^*δ`
(`Stacks.NaiveCotangentPulledImmersion.homologyMap_negOne_baseChangeMapOfComparison`), whose
kernel is the excess conormal sheaf (`kernelConormalDifferentialιCompIso`). -/
noncomputable def kernelHomologyMapNegOneBaseChangeMapIso (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) :
    kernel (HomologicalComplex.homologyMap
        (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) (-1)) ≅
      F.baseChangeExcessConormal hsq :=
  Stacks.NaiveCotangentPulledImmersion.kernelHomologyMapNegOneBaseChangeIso F.imm F.proj
      (F.baseChange hsq).imm (F.baseChange hsq).proj g' (pullback.fst F.proj g) g F.imm_proj
      (F.baseChange hsq).imm_proj (F.isPullback_baseChange hsq).flip.w hsq.w pullback.condition
      (Stacks.Smooth.formallySmoothScheme_of_smooth F.proj)
      (Stacks.Smooth.formallySmoothScheme_of_smooth (F.baseChange hsq).proj) ≪≫
    F.kernelConormalDifferentialιCompIso hsq

end SmoothFactorization

/-- **The sheaf `𝒞` of [Stacks Project, Tag 0FV9] is finite locally free.** For a cartesian
square `g' ≫ f = f' ≫ g` of schemes with `f` and `f'` local complete intersection morphisms and
the Gysin map existing for `f`, the kernel `𝒞` of the map
`H^{-1}((g')^*NL_{X/Y}) ⟶ H^{-1}(NL_{X'/Y'})` induced by the base change map of
[Stacks Project, Tag 0FV5] is a finite locally free `𝒪_{X'}`-module: choosing a factorization
of `f` through a smooth morphism, it is the excess conormal sheaf
(`SmoothFactorization.kernelHomologyMapNegOneBaseChangeMapIso`), the kernel of a surjection of
finite locally free modules. -/
theorem isFiniteLocallyFree_kernel_homologyMap_baseChangeMapOfComparison
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (hf : IsLocalCompleteIntersectionMorphism f) (hf' : IsLocalCompleteIntersectionMorphism f')
    (hG : GysinMapExists f) (hsq : IsPullback g' f' f g) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (kernel (HomologicalComplex.homologyMap
        (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
          (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) (-1))) := by
  obtain ⟨F⟩ := (gysinMapExists_iff_nonempty f).1 hG
  exact Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso
      (F.kernelHomologyMapNegOneBaseChangeMapIso hsq).symm
      (h := (F.isFiniteLocallyFree_baseChangeExcessConormal hsq hf hf'))

end Stacks.Chow

end
