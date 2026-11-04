module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedTransportComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRegularImmersionExcess
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinMapComposition
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChangeExcessNaiveCotangent

/-!
# The Gysin map of a local complete intersection morphism under base change

Let `(S, δ)` be as in Situation 02QL and let

```
X' --g'--→ X
|          |
f'         f
↓          ↓
Y' --g---→ Y
```

be a cartesian square of schemes locally of finite type over `S`, with `f` and `f'` local complete
intersection morphisms and the Gysin map of Stacks 0FF3 existing for `f`. Then the sheaf
`𝒞 = Ker(H^{-1}((g')^*NL_{X/Y}) ⟶ H^{-1}(NL_{X'/Y'}))` is a finite locally free `𝒪_{X'}`-module,
the Gysin map exists for `f'`, and

  `res(f^!) = c_top(𝒞^∨) ∘ (f')^!`   in `A^*(X' ⟶ Y')^∧`.

The restriction `res(f^!)` lives on the chosen fibre product `X ×_Y Y'`; it is carried to the given
`X'` along the canonical isomorphism `X ×_Y Y' ≅ X'` (`Stacks.Chow.completedBivariantTransport`).

## Main results

* `SmoothFactorization.completedBivariantTransport_completedBivariantRestriction_gysinMap`:
  for a factorization `F : f = h ∘ i` through a smooth `P`, its base change `F'`, and any finite
  locally free `𝒦` isomorphic to the kernel of `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}`,
  `res(F^!) = c_top(𝒦^∨) ∘ (F')^!`.
* `Stacks.Chow.completedBivariantTransport_completedBivariantRestriction_lciGysinMap`: `𝒞` is
  finite locally free, the Gysin map exists for `f'`, and `res(f^!) = c_top(𝒞^∨) ∘ (f')^!`.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV7](https://stacks.math.columbia.edu/tag/0FV7)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y} [LocallyOfFiniteType f]
  [LocallyOfFiniteType f'] [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hf' : f' ≫ (g ≫ sY) = sX') (hsq : IsPullback g' f' f g)

/-- The four schemes `X`, `Y`, `X'`, `Y'` of the square are locally Noetherian. -/
private theorem isLocallyNoetherian_quadruple (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (sX' : X' ⟶ C.S)
    (g : Y' ⟶ Y) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sX']
    [LocallyOfFiniteType g] :
    IsLocallyNoetherian X ∧ IsLocallyNoetherian Y ∧ IsLocallyNoetherian X' ∧
      IsLocallyNoetherian Y' :=
  ⟨LocallyOfFiniteType.isLocallyNoetherian sX, LocallyOfFiniteType.isLocallyNoetherian sY,
    LocallyOfFiniteType.isLocallyNoetherian sX',
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)⟩

/-- **The restriction of the Gysin map of a factorization, with excess.** For a cartesian square
`g' ≫ f = f' ≫ g` of schemes locally of finite type over the base with `f` and `f'` local complete
intersection morphisms, a factorization `F : f = h ∘ i` through a smooth morphism and its base
change `F' : f' = h' ∘ i'` (`Stacks.Chow.SmoothFactorization.baseChange`), and a finite locally
free `𝒦` isomorphic to the kernel of `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}`,

  `res(i^! ∘ h^*) = c_top(𝒦^∨) ∘ (i')^! ∘ (h')^*`

in `A^*(X' ⟶ Y')^∧`, the restriction being carried from `X ×_Y Y'` to `X'`. -/
theorem SmoothFactorization.completedBivariantTransport_completedBivariantRestriction_gysinMap
    (F : SmoothFactorization f) (hlf : IsLocalCompleteIntersectionMorphism f)
    (hlf' : IsLocalCompleteIntersectionMorphism f') (𝒦 : X'.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒦] (e : 𝒦 ≅ F.baseChangeExcessConormal hsq) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
    haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf 𝒦) :=
      isFiniteLocallyFree_dualSheaf_of_schemeOpens 𝒦 inferInstance
    completedBivariantTransport C (pullback.fst f g ≫ sX) sX' (g ≫ sY) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) f' hf' hsq.isoPullback.symm
        hsq.isoPullback_inv_snd
        (completedBivariantRestrictionViaSequence C sX sY f hf g (F.gysinMap C sX sY hf hlf)) =
      completedBivariantGroup.copy C (Category.id_comp f') _ hf'
        (completedBivariantCompositeOfInvertible C sX' sX' (g ≫ sY) (𝟙 X') f'
          (Category.id_comp sX') hf' (topChernClassOfInvertible C sX' (dualSheaf 𝒦))
          ((F.baseChange hsq).gysinMap C sX' (g ≫ sY) hf' hlf')) := by
  obtain ⟨P, i, h, _, _, rfl⟩ := F
  obtain ⟨_, _, _, _⟩ := isLocallyNoetherian_quadruple C sX sY sX' g
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sY)
  have : IsLocallyNoetherian (pullback h g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst h g ≫ h ≫ sY)
  have : IsLocallyNoetherian (pullback (i ≫ h) g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ h) g ≫ sX)
  have : IsLocallyNoetherian (pullback i (pullback.fst h g)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i (pullback.fst h g) ≫ sX)
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf 𝒦) :=
    isFiniteLocallyFree_dualSheaf_of_schemeOpens 𝒦 inferInstance
  set F : SmoothFactorization (i ≫ h) := ⟨P, i, h, inferInstance, inferInstance, rfl⟩ with hF
  have : IsLocallyNoetherian (F.baseChange hsq).ambient := ‹IsLocallyNoetherian (pullback h g)›
  have : IsLocallyNoetherian F.ambient := ‹IsLocallyNoetherian P›
  have : IsImmersion (F.baseChangeImm hsq.w) := F.isImmersion_baseChangeImm hsq
  have hiF : i ≫ (h ≫ sY) = sX := hf
  have hri : IsRegularImmersion i := F.isRegularImmersion hlf
  have hri' : IsRegularImmersion (F.baseChangeImm hsq.w) :=
    (F.baseChange hsq).isRegularImmersion hlf'
  have sq : IsPullback (F.baseChangeImm hsq.w) g' (pullback.fst h g) i :=
    (F.isPullback_baseChange hsq).flip
  have hi'p : F.baseChangeImm hsq.w ≫ pullback.fst h g = g' ≫ i := F.baseChangeImm_fst hsq.w
  have hi'h : F.baseChangeImm hsq.w ≫ pullback.snd h g = f' := F.baseChangeImm_snd hsq.w
  have hi'₂ : F.baseChangeImm hsq.w ≫ (pullback.fst h g ≫ (h ≫ sY)) = sX' := by
    rw [pullback.condition_assoc, ← Category.assoc, hi'h, hf']
  have h1 := completedBivariantRestriction_completedBivariantCompositeOfInvertible C sX (h ≫ sY) sY
    i h hiF rfl g (completedVirtualNormalGysinClassOfImmersion C sX (h ≫ sY) i hiF
      (VirtualNormalBundle.ofIsRegularImmersion i hri))
    (completedFlatPullbackOfSmooth C (h ≫ sY) sY h rfl)
  have h2 := completedBivariantRestriction_completedFlatPullbackOfSmooth C (h ≫ sY) sY h rfl g
  have h3 := completedBivariantTransport_completedBivariantRestriction_ofIsRegularImmersion C sX
    (h ≫ sY) i hiF (pullback.fst h g) (F.baseChangeImm hsq.w) g' sq sX' hi'₂ hri hri' 𝒦 e
  have hiso :
      pullbackRightPullbackFstIso h g i ≪≫ hsq.isoPullback.symm = sq.flip.isoPullback.symm := by
    ext
    refine hsq.hom_ext ?_ ?_
    · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst,
        pullbackRightPullbackFstIso_hom_fst, Iso.symm_hom, IsPullback.isoPullback_inv_fst]
    · have hr : sq.flip.isoPullback.inv ≫ f' =
          pullback.snd i (pullback.fst h g) ≫ pullback.snd h g := by
        calc _ = sq.flip.isoPullback.inv ≫ F.baseChangeImm hsq.w ≫ pullback.snd h g := by
              rw [hi'h]
          _ = _ := by rw [← Category.assoc, IsPullback.isoPullback_inv_snd]
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd,
        pullbackRightPullbackFstIso_hom_snd, Iso.symm_hom, hr]
  have e1 : (F.gysinMap C sX sY hf hlf) =
      completedBivariantCompositeOfInvertible C sX (h ≫ sY) sY i h hiF rfl
        (completedVirtualNormalGysinClassOfImmersion C sX (h ≫ sY) i hiF
          (VirtualNormalBundle.ofIsRegularImmersion i hri))
        (completedFlatPullbackOfSmooth C (h ≫ sY) sY h rfl) := rfl
  rw [e1, h1, h2, completedBivariantTransport_completedBivariantTransport]
  have hθ' : sq.flip.isoPullback.symm.hom ≫ (F.baseChangeImm hsq.w ≫ pullback.snd h g) =
      pullback.snd i (pullback.fst h g) ≫ pullback.snd h g := by
    rw [Iso.symm_hom, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  refine eq_of_heq ((completedBivariantTransport_heq_congr C
    (hu' := comp_comp_structureMorphism_eq hi'₂
      (pullbackSnd_comp_structureMorphism_eq C (h ≫ sY) sY h rfl g))
    (hθ' := hθ') hi'h.symm hiso _).trans ?_)
  rw [completedBivariantTransport_completedBivariantCompositeOfInvertible C
    (pullback.fst i (pullback.fst h g) ≫ sX) sX' (pullback.fst h g ≫ (h ≫ sY)) (g ≫ sY)
    (pullback.snd i (pullback.fst h g)) _ (F.baseChangeImm hsq.w) hi'₂ (pullback.snd h g) _
    sq.flip.isoPullback.symm sq.flip.isoPullback_inv_snd, h3]
  have hmid : pullback.fst h g ≫ (h ≫ sY) = pullback.snd h g ≫ (g ≫ sY) :=
    pullback.condition_assoc sY
  refine HEq.trans (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl
    (Category.id_comp _).symm rfl (completedBivariantGroup.copy_heq C _ _ _ _) HEq.rfl) ?_
  refine (completedBivariantCompositeOfInvertible_assoc C _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (completedBivariantGroup.copy_heq C _ _ _ _).symm
  refine completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl rfl hi'h HEq.rfl ?_
  refine HEq.trans ?_ (completedBivariantGroup.copy_heq C _ _ _ _).symm
  exact completedBivariantCompositeOfInvertible_heq_congr C rfl hmid rfl rfl rfl
    (completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr C hmid rfl hri' _)
    (completedFlatPullbackOfSmooth_heq_congr C hmid rfl)

/-- Let `g' ≫ f = f' ≫ g` be a cartesian square of schemes locally of finite type over the base,
with `f` and `f'` local complete intersection morphisms and the Gysin map of Stacks 0FF3 existing
for `f`. Then the sheaf

  `𝒞 = Ker(H^{-1}((g')^*NL_{X/Y}) ⟶ H^{-1}(NL_{X'/Y'}))`,

for the base change map of Stacks 0FV5, is a finite locally free `𝒪_{X'}`-module, the Gysin map
exists for `f'`, and

  `res(f^!) = c_top(𝒞^∨) ∘ (f')^!`   in `A^*(X' ⟶ Y')^∧`,

for the Gysin maps of Stacks 0FF3, the restriction of Stacks 0F9Z (carried from the chosen fibre
product `X ×_Y Y'` to `X'` along the canonical isomorphism), the top Chern class of Stacks 0FA4
and the composition of Stacks 0FE0 (a class for `𝟙 ≫ f'`). -/
@[stacks 0FV9 "the whole lemma: for a cartesian square of schemes locally of finite type over S \
with f, f' local complete intersection morphisms and the Gysin map existing for f, the kernel C \
of H^{-1}((g')^*NL_{X/Y}) → H^{-1}(NL_{X'/Y'}) is finite locally free, the Gysin map exists for \
f', and res(f^!) = c_top(C^∨) ∘ (f')^! in A^*(X' → Y')^∧"]
theorem completedBivariantTransport_completedBivariantRestriction_lciGysinMap
    (hlf : IsLocalCompleteIntersectionMorphism f) (hlf' : IsLocalCompleteIntersectionMorphism f')
    (hG : GysinMapExists f) :
    ∃ hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (kernel (HomologicalComplex.homologyMap
          (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
            (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
            (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) (-1))),
      ∃ hG' : GysinMapExists f',
        haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
        haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
        haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
        haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
        haveI : IsLocallyNoetherian (pullback f g) :=
          LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
        haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf (kernel
            (HomologicalComplex.homologyMap
              (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
                (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
                (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w))
              (-1)))) :=
          isFiniteLocallyFree_dualSheaf_of_schemeOpens _ hC
        completedBivariantTransport C (pullback.fst f g ≫ sX) sX' (g ≫ sY) (pullback.snd f g)
            (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) f' hf' hsq.isoPullback.symm
            hsq.isoPullback_inv_snd
            (completedBivariantRestrictionViaSequence C sX sY f hf g
              (lciGysinMap C sX sY hf hlf hG)) =
          completedBivariantGroup.copy C (Category.id_comp f') _ hf'
            (completedBivariantCompositeOfInvertible C sX' sX' (g ≫ sY) (𝟙 X') f'
              (Category.id_comp sX') hf'
              (topChernClassOfInvertible C sX' (dualSheaf (kernel (HomologicalComplex.homologyMap
                (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
                  (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
                  (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w))
                (-1)))))
              (lciGysinMap C sX' (g ≫ sY) hf' hlf' hG')) := by
  have hC := isFiniteLocallyFree_kernel_homologyMap_baseChangeMapOfComparison hlf hlf' hG hsq
  refine ⟨hC, GysinMapExists.of_isPullback hsq hG, ?_⟩
  obtain ⟨F⟩ := (gysinMapExists_iff_nonempty f).1 hG
  obtain ⟨_, _, _, _⟩ := isLocallyNoetherian_quadruple C sX sY sX' g
  rw [← F.gysinMap_eq_lciGysinMap C sX sY hf hlf hG,
    ← (F.baseChange hsq).gysinMap_eq_lciGysinMap C sX' (g ≫ sY) hf' hlf']
  exact @SmoothFactorization.completedBivariantTransport_completedBivariantRestriction_gysinMap C
    X Y X' Y' sX _ sY _ sX' _ f f' g' g _ _ _ hf hf' hsq F hlf hlf' _ hC
    (F.kernelHomologyMapNegOneBaseChangeMapIso hsq)

end Stacks.Chow

end
