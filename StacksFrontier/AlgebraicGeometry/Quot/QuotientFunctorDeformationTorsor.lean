module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorObstruction
public import StacksFrontier.Deformation.ToposThickening.QuotientLiftDeformationTorsor

/-!
# Deformations of quotients (Stacks 0CZV)

In Situation 082M with `F` flat over `B`, let `T ⊂ T'` be a first order thickening of schemes over
`B` with ideal sheaf `𝒥`, and let `x ∈ Q_{F/X/B}(T)` be given by `0 ⟶ 𝒦 ⟶ F_T ⟶ 𝒬 ⟶ 0`. Remark
0CZV asserts that when the obstruction `o_x(T')` of Remark 0CZU vanishes, the set of lifts
`x' ∈ Q_{F/X/B}(T')` of `x` is a principal homogeneous space under
`Hom_{𝒪_{X_T}}(𝒦, 𝒬 ⊗_{𝒪_T} 𝒥)`, where `𝒬 ⊗_{𝒪_T} 𝒥 = 𝒬 ⊗ f_T^*𝒥`, the map `φ` acting on a lift
`𝒦'` by `𝒦' ↦ 𝒦'_φ`, the subsheaf of the sections `s` of `F_{T'}` whose image in `F_T` is a
section `k` of `𝒦` and whose image in `𝒬' = F_{T'}/𝒦'` is `φ(k) ∈ 𝒬 ⊗ 𝒥 ⊂ 𝒬'`.

The thickening `X_T ⊂ X_{T'}` and its relative square place this in the setting of ringed topoi,
where it is `Deformation.ToposThickening.exists_addTorsor_quotientLift_of_nonempty`. The lifts in
`Q_{F/X/B}(T')` are the topos lifts
(`AlgebraicGeometry.Space.QuotientSituation.isQuotientLift_obstructionKernel_iff`), and the group
is transported along `F_T ≅ F_{T'}|_{X_T}` and the identification of the two pullbacks of the
ideal (`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`).

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.deformationGroup`: the group
  `Hom_{𝒪_{X_T}}(𝒦, 𝒬 ⊗_{𝒪_T} 𝒥)` of the remark, read on the relative square, and
  `AlgebraicGeometry.Space.QuotientSituation.deformationGroupEquiv`, its identification with the
  morphisms `𝒦 ⟶ 𝒬 ⊗ f_T^*𝒥` on `X_T`.
* `AlgebraicGeometry.Space.QuotientSituation.quotientLiftAction`: the action `𝒦' ↦ 𝒦'_φ`.
* `AlgebraicGeometry.Space.QuotientSituation.exists_addTorsor_quotientLifts`: when the
  obstruction vanishes, the lifts form a principal homogeneous space under the group.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- Morphisms out of a subobject `K ⊂ A`, read on its image under a monomorphism `f : A ⟶ B` and
with the target changed along an isomorphism `κ : M ≅ N`, as an isomorphism of groups: `g` is sent
to `g ≫ κ.hom` precomposed with the identification of `f(K)` with `K`. -/
noncomputable def Subobject.mapHomAddEquiv {A B : C} (f : A ⟶ B) [Mono f] (K : Subobject A)
    {M N : C} (κ : M ≅ N) : ((K : C) ⟶ M) ≃+ (((Subobject.map f).obj K : C) ⟶ N) where
  toEquiv := (Subobject.isoOfEqMk _ (K.arrow ≫ f) (by
    conv_lhs => rw [← Subobject.mk_arrow K]
    exact Subobject.map_mk _ _)).symm.homCongr κ
  map_add' g g' := by
    simp only [Equiv.toFun_as_coe, Iso.homCongr_apply, Iso.symm_inv, Preadditive.add_comp,
      Preadditive.comp_add]

end CategoryTheory

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
-- The import closure carries sheafification instances at a free module universe, on which the
-- instance searches below stall.
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
-- The groups of morphisms are `SheafOfModules.instAddCommGroupHom`, as in the statements of the
-- topos layer, rather than those of the abelian structure above.
attribute [local instance 7000] SheafOfModules.instPreadditive
attribute [local instance 8000] SheafOfModules.instAddCommGroupHom
attribute [-instance] CategoryTheory.IsGrothendieckAbelian.hasExt

universe e u

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)
  {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The group
`Hom_{𝒪_{X_T}}(𝒦, 𝒬 ⊗_{𝒪_T} 𝒥)`, with `𝒬 ⊗_{𝒪_T} 𝒥 = 𝒬 ⊗ f_T^*𝒥` for the ideal `𝒥` of
`T ⊂ T'`, is the group `Hom(𝒦, 𝒬 ⊗ f̃^*𝒥̃)` of the relative square, transported along
`F_T ≅ F_{T'}|_{X_T}` and the identification of the two pullbacks of the ideal. -/
noncomputable def deformationGroupEquiv (K : Subobject (D.baseChangeModule T)) :
    @Quiver.Hom (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O)) _
      (Subobject.underlying.obj K)
      ((baseIdealTensor.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
          (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
          (smallEtaleRingedToposHom B S hS (D.projection T))
          (D.testSchemeFirstOrderThickening h hh)).obj (D.quotientModule T K)) ≃+
    @Quiver.Hom (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O)) _
      (Subobject.underlying.obj (D.obstructionKernel h K))
      ((baseIdealTensor.{u, u + 1, u, u, u + 1, u, u, u + 1, u} (D.relativeSquareThickening h)
          (D.relativeSquareLeft h) (D.relativeSquareThickeningFirstOrderThickening h hh)).obj
          (cokernel (D.obstructionKernel h K).arrow)) :=
  Subobject.mapHomAddEquiv (D.restrictBaseChangeModuleIso h).inv K
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedTopos B S hS (D.space T)).O).obj (D.quotientModule T K)).mapIso
        (D.relativeSquareBasePullbackIdealIso h hh).symm) ≪≫
      (baseIdealTensor.{u, u + 1, u, u, u + 1, u, u, u + 1, u} (D.relativeSquareThickening h)
        (D.relativeSquareLeft h) (D.relativeSquareThickeningFirstOrderThickening h hh)).mapIso
        (D.obstructionKernelCokernelIso h K).symm)

variable [HasExt.{e} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (D.space T)).O))]

/-- The group `Hom_{𝒪_{X_T}}(𝒦, 𝒬 ⊗_{𝒪_T} 𝒥)` of Stacks 0CZV, read on the relative square: the
morphisms from `𝒦` to `𝒬 ⊗ f̃^*𝒥̃`, with `𝒦` and `𝒬` read on `F_{T'}|_{X_T}` and `f̃^*𝒥̃ ≅ f_T^*𝒥`
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`). It is identified
with the group `Hom(𝒦, 𝒬 ⊗ f_T^*𝒥)` on `X_T` itself by
`AlgebraicGeometry.Space.QuotientSituation.deformationGroupEquiv`. -/
def deformationGroup (K : Subobject (D.baseChangeModule T)) : Type (u + 1) :=
  quotientLiftGroup.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (D.relativeSquareThickeningFirstOrderThickening h hh) (D.baseChangeModule T')
    (D.obstructionKernel h K)

/-- The abelian group structure on `deformationGroup`, that of the group of morphisms
`𝒦 ⟶ 𝒬 ⊗ f̃^*𝒥̃`. -/
noncomputable instance (K : Subobject (D.baseChangeModule T)) :
    AddCommGroup (D.deformationGroup h hh K) :=
  inferInstanceAs (AddCommGroup (quotientLiftGroup.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (D.relativeSquareThickeningFirstOrderThickening h hh) (D.baseChangeModule T')
    (D.obstructionKernel h K)))

/-- The lifts `x' ∈ Q_{F/X/B}(T')` of `x ∈ Q_{F/X/B}(T)`, given by `K ⊂ F_T`. -/
abbrev quotientLifts (K : Subobject (D.baseChangeModule T)) : Type (u + 1) :=
  {K' : Subobject (D.baseChangeModule T') // K' ∈ D.quotients T' ∧ D.quotientPullback h K' = K}

include hF hh in
/-- The lift `𝒦'_φ` of the remark of Stacks 0CZV: for a lift `x'` of `x`, given by
`𝒦' ⊂ F_{T'}` with `𝒬' = F_{T'}/𝒦'`, and `φ : 𝒦 ⟶ 𝒬 ⊗_{𝒪_T} 𝒥`, the subsheaf of the sections `s`
of `F_{T'}` whose image in `F_T` is a section `k` of `𝒦` and whose image in `𝒬'` is `φ(k)`, read in
`𝒬'` through the inclusion `𝒬 ⊗ 𝒥 ⊂ 𝒬'` of the remark's diagram
(`Deformation.ToposThickening.quotientLiftDeformation`). -/
noncomputable def quotientLiftAction {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) (φ : D.deformationGroup h hh K) (K' : D.quotientLifts h K) :
    Subobject (D.baseChangeModule T') :=
  quotientLiftDeformation.{u, u + 1, u, u, u + 1, u, u + 1, u, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (D.relativeSquareThickening h) (D.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareThickeningFirstOrderThickening h hh) (D.relativeSquare_comm h)
    (D.baseChangeModule T') (D.obstructionKernel h K) (D.isStrict_relativeSquare h hh)
    (D.isFlat_baseChangeModule_relBaseRight hF T')
    ((D.isQuotientLift_obstructionKernel_iff hF h hh hK K'.val).2 K'.property) φ

include hF hh in
/-- In Situation 082M with `F` flat over `B`, let
`T ⊂ T'` be a first order thickening of schemes over `B` with ideal sheaf `𝒥`, and let
`x ∈ Q_{F/X/B}(T)` be given by `0 ⟶ 𝒦 ⟶ F_T ⟶ 𝒬 ⟶ 0` (`K ∈ D.quotients T`). If the obstruction
`o_x(T')` of Remark 0CZU vanishes (`D.quotientObstruction hF h hh K = 0`), the set of lifts
`x' ∈ Q_{F/X/B}(T')` of `x` (`D.quotientLifts h K`: the `K' ∈ D.quotients T'` with
`D.quotientPullback h K' = K`) is a principal homogeneous space under
`Hom_{𝒪_{X_T}}(𝒦, 𝒬 ⊗_{𝒪_T} 𝒥)` (`D.deformationGroup h hh K`), with the action of the remark:
`φ` sends `𝒦'` to `𝒦'_φ` (`D.quotientLiftAction hF h hh hK φ K'`). -/
@[stacks 0CZV]
theorem exists_addTorsor_quotientLifts {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.quotients T) (ho : D.quotientObstruction.{e} hF h hh K = 0) :
    ∃ Tor : AddTorsor (D.deformationGroup h hh K) (D.quotientLifts h K),
      ∀ (φ : D.deformationGroup h hh K) (K' : D.quotientLifts h K),
        (Tor.vadd φ K').val = D.quotientLiftAction hF h hh hK φ K' := by
  have hex : ∃ K' ∈ D.quotients T', D.quotientPullback h K' = K :=
    (D.quotientObstruction_eq_zero_iff hF h hh hK).1 ho
  have key := exists_addTorsor_quotientLift_of_nonempty
    (smallEtaleRingedToposHom B S hS (D.relativeMap h)) (D.relativeSquareThickening h)
    (D.relativeSquareLeft h) (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
    (D.relativeMapFirstOrderThickening h hh) (D.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquare_comm h) (D.baseChangeModule T') (D.obstructionKernel h K)
    (D.isStrict_relativeSquare h hh) (D.isFlat_baseChangeModule_relBaseRight hF T')
    (D.isFlatOverBase_obstructionKernel h hh hK)
    ⟨⟨hex.choose, (D.isQuotientLift_obstructionKernel_iff hF h hh hK hex.choose).2
      hex.choose_spec⟩⟩
  exact ⟨@addTorsorCongr _ _ _ _ _ _ key.choose
    { toEquiv := Equiv.refl _, map_add' := fun _ _ => rfl }
    (Equiv.subtypeEquivRight fun K' => (D.isQuotientLift_obstructionKernel_iff hF h hh hK K').symm),
    fun φ K' => key.choose_spec _ _⟩

end AlgebraicGeometry.Space.QuotientSituation

end
