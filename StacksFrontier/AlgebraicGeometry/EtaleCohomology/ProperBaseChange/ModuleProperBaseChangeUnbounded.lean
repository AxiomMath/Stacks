module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.TermwiseAcyclicComputesRightDerived
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageUnboundedLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
import StacksCore.Tactic.StacksAttribute

/-!
# Proper base change for unbounded complexes with torsion coefficients

Let `f : X ⟶ Y` be a proper morphism of schemes, `g : Y' ⟶ Y` a morphism, `X' = Y' ×_Y X` with
projections `f' : X' ⟶ Y'` and `g' : X' ⟶ X`, and let `Λ` be a ring in which some positive
integer `n` is zero — `ℤ/nℤ`, for instance. For every object `E` of the **unbounded** derived
category `D(X_étale, Λ)` the base change map `g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` is an
isomorphism. This is [Stacks, Tag 0F0C].

The proof is the source's. Represent `E` by a K-injective complex `I` with injective terms
(Stacks 079P). Then `Rf_* E` is computed by `f_* I`, and the base change map at `E` is invertible
as soon as the degreewise comparison `g^{-1} f_* I ⟶ f'_* (g')^{-1} I` is an isomorphism of
complexes and `(g')^{-1} I` computes `Rf'_*`.

* In each degree the comparison is invertible, and `(g')^{-1} I^m` is acyclic for `f'_*`: this
  is the proper base change theorem ([Stacks, Tag 095T]) at the underlying abelian sheaf of
  `I^m`, which is torsion and acyclic for `f_*` ([Stacks, Tag 03FD]), transported along
  forgetting the module structure.
* `(g')^{-1} I` computes `Rf'_*`. This is étale local on `Y'`, so `Y'` may be replaced by an
  affine open `V`; over a quasi-compact base the fibre dimensions of the proper morphism
  `X'_V ⟶ V` are bounded ([Stacks, Tag 0A3V]), so `(f'_V)_*` has finite cohomological dimension
  on sheaves of `Λ`-modules ([Stacks, Tag 095U]), and a complex of acyclic objects for a functor
  of finite cohomological dimension computes its unbounded right derived functor ([Stacks, Tag
  07K7]). The terms of the restriction of `(g')^{-1} I` to `X'_V` are again inverse images of
  injectives along the base change of `f` to `V`, hence acyclic by the first point.

## Main results

All of these are in the `Stacks.EtaleCohomology` namespace.

* `isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper`: **[Stacks, Tag 0F0C]**.
* `isIso_etaleModuleDerivedBaseChangeUnbounded_of_cohomologyCommutesWithBaseChange`: the same in
  an arbitrary coefficient universe, given proper base change for torsion abelian sheaves along
  `f` and finite cohomological dimension of proper direct images in that universe.
* `isIso_etaleModuleBaseChange_app_of_injective` and
  `isZero_rightDerived_etaleModuleDirectImage_inverseImage_of_injective`: proper base change at an
  injective sheaf of `Λ`-modules, in degree zero and in positive degrees.
* `isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_inverseImage_of_injective`: the inverse
  image of a complex of injectives computes `Rf'_*`.

## Implementation notes

*The coefficients.* The source takes `Λ = ℤ/nℤ`. Only the vanishing of `n` in `Λ` is used,
through the fact that every sheaf of `Λ`-modules is then torsion, so the statement is made for a
commutative ring `Λ : Type` with `n = 0` in `Λ` for some `n > 0`. The universe of `Λ` is the
universe of the abelian proper base change theorem it reduces to, whose coefficients are
`AddCommGrpCat.{u + 1}`.

*Spelling.* The statements here are in the coefficient universe `w`, the name the forgetful
comparisons of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange` and the
abelian proper base change theorem are stated with, and the instances switched off below are
switched off for the same reason as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange`:
the kernel compares terms elaborated in different files cheaply only when universe levels and
instance arguments are spelled alike. The base change map and the units of the derived direct
images are defined with the universe named `r`; they are reached through
`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_injective`, whose
hypotheses are stated object by object, which is the form in which the kernel reconciles the two
spellings within its budget.

## References

* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/- The abelian proper base change statements this file instantiates find the sheafification of
abelian presheaves on small étale sites through
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` and the additivity of direct image as
`Stacks.EtaleCohomology.additive_etaleAbelianDirectImage`; the two instances switched off here
would give the terms built in this file different (propositionally equal) instance arguments,
which the kernel can only compare by unfolding, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange`. -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
attribute [-instance] Stacks.EtaleCohomology.etaleAbelianDirectImage_additive
attribute [-instance] AlgebraicGeometry.RingedSite.moduleHasSheafify
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale
  Stacks.EtaleCohomology.hasWeakSheafifyOverEtale

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-! ### Torsion coefficients -/

/-- If a positive integer `n` vanishes in `Λ`, every sheaf of `Λ`-modules on `X_étale` has a
torsion underlying abelian sheaf: every section is killed by `n`. -/
theorem torsionSheafProperty_etaleModuleForgetUniv_obj (Λ : Type w) [Ring Λ]
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) {X : Scheme.{u}} (M : EtaleModules.{u, w} Λ X) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, w} Λ X).obj M) := by
  obtain ⟨n, hn, hΛ⟩ := hΛ
  intro V x
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W φ _ ↦ ⟨n, hn, ?_⟩⟩
  show n • (M.obj.map φ.op).hom x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

/-! ### Forgetting the module structure -/

section Forget

variable (Λ : Type w) [Ring Λ]

/-- **Higher direct images of sheaves of `Λ`-modules forget to higher direct images of abelian
sheaves**: `U(R^p f_* M) ≅ R^p f_*(U M)`, `U` forgetting the module structure. Forgetting is
exact, commutes with direct image on the nose, and carries injective sheaves of modules to
abelian sheaves acyclic for direct image ([Stacks, Tag 03FD]). This is
`Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso` in an arbitrary coefficient
universe. -/
def etaleModuleForgetRightDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : EtaleModules.{u, w} Λ X) (p : ℕ) :
    (etaleModuleForgetAb.{u, w} Λ Y).obj
        (((etaleModuleDirectImage.{u, w} Λ f).rightDerived p).obj M) ≅
      ((etaleAbelianDirectImage.{u, w} f).rightDerived p).obj
        ((etaleModuleForgetAb.{u, w} Λ X).obj M) :=
  have : (etaleModuleForgetAb.{u, w} Λ Y).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Stacks.DerivedFunctor.rightDerivedEvaluationIso (etaleModuleDirectImage.{u, w} Λ f)
      (etaleModuleForgetAb.{u, w} Λ Y) M p ≪≫
    (Stacks.DerivedFunctor.rightDerivedIso
        (etaleModuleForgetDirectImageIso.{u, w} Λ f).symm p).app M ≪≫
    (Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
      (etaleModuleForgetAb.{u, w} Λ X) (etaleAbelianDirectImage.{u, w} f)
      (fun I _ ↦ rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj.{u, w} Λ f I)
      p).app M

/-- A sheaf of `Λ`-modules is zero if its underlying abelian sheaf is. -/
theorem isZero_of_isZero_etaleModuleForgetUniv_obj {X : Scheme.{u}} (M : EtaleModules.{u, w} Λ X)
    (h : IsZero ((etaleModuleForgetAb.{u, w} Λ X).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact (etaleModuleForgetAb.{u, w} Λ X).map_injective (by simpa using h.eq_of_src _ _)

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)

/-- **Forgetting the module structure reflects invertibility of the underived base change
comparison**: it carries the module comparison at `M` to the abelian one at the underlying
abelian sheaf of `M`, up to isomorphisms
(`Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange`). -/
theorem isIso_etaleModuleBaseChange_app_of_isIso_forget (M : EtaleModules.{u, w} Λ X)
    (h : IsIso ((etaleAbelianBaseChange.{u, w} f g g' f' sq.w).app
      ((etaleModuleForgetAb.{u, w} Λ X).obj M))) :
    IsIso ((etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm).app M) := by
  have hP := etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange.{u, w} Λ f f' g g'
    sq.w M
  have h₂ : IsIso ((etaleAbelianDirectImage.{u, w} f').map
      ((etaleModuleForgetInverseImageIso.{u, w} Λ g').hom.app M)) :=
    ((etaleAbelianDirectImage.{u, w} f').mapIso
      ((etaleModuleForgetInverseImageIso.{u, w} Λ g').app M)).isIso_hom
  have : IsIso ((etaleModuleForgetInverseImageIso.{u, w} Λ g).hom.app
        ((etaleModuleDirectImage.{u, w} Λ f).obj M) ≫
      (etaleModuleForgetAb.{u, w} Λ Y').map
        ((etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm).app M)) := by
    rw [hP]
    exact IsIso.comp_isIso' h h₂
  have : IsIso ((etaleModuleForgetAb.{u, w} Λ Y').map
      ((etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm).app M)) :=
    IsIso.of_isIso_comp_left ((etaleModuleForgetInverseImageIso.{u, w} Λ g).hom.app
        ((etaleModuleDirectImage.{u, w} Λ f).obj M)) _
  exact isIso_of_reflects_iso _ (etaleModuleForgetAb.{u, w} Λ Y')

end Forget

/-! ### Proper base change at an injective sheaf of modules -/

section Injective

variable (Λ : Type w) [Ring Λ] (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
  {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (hpbc : CohomologyCommutesWithBaseChange.{u, w} f)
  {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  (sq : IsPullback g' f' f g) (I : EtaleModules.{u, w} Λ X) [Injective I]

/-- The underlying abelian sheaf of an injective sheaf of `Λ`-modules has no higher direct
images ([Stacks, Tag 03FD]), read on the cohomology sheaves of `Rf_*`. -/
theorem isZero_homology_etaleAbelianDerivedDirectImage_forget_of_injective (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) q).obj
      ((etaleAbelianDerivedDirectImage.{u, w} f).obj
        ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) 0).obj
          ((etaleModuleForgetAb.{u, w} Λ X).obj I)))) :=
  (rightAcyclic_etaleAbelianDirectImage_iff.{u, w} f _).1
    (rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj.{u, w} Λ f I) q hq

include hΛ hpbc sq in
/-- At the underlying abelian sheaf `G` of an injective sheaf of `Λ`-modules, the higher
cohomology sheaves of `Rf'_* (g')^{-1} G` vanish: by proper base change for `f`
([Stacks, Tag 095T]) they are `g^{-1}` of those of `Rf_* G`, which vanish because `G` is acyclic
for `f_*` ([Stacks, Tag 03FD]). -/
theorem isZero_homology_etaleAbelianDirectImage_inverseImage_forget_of_injective
    (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) q).obj
      ((etaleAbelianDerivedDirectImage.{u, w} f').obj
        ((etaleAbelianDerivedInverseImage.{u, w} g').obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}) 0).obj
            ((etaleModuleForgetAb.{u, w} Λ X).obj I))))) :=
  have := hpbc g g' f' sq _ (torsionSheafProperty_etaleModuleForgetUniv_obj Λ hΛ I)
  isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso f g g' f' sq.w _ q
    (isZero_homology_etaleAbelianDerivedDirectImage_forget_of_injective Λ f I q hq)

include hΛ hpbc sq in
/-- **The underived base change comparison is invertible at an injective sheaf of modules**
(proper base change in degree zero, [Stacks, Tag 095T]). Forgetting the module structure carries
it to the abelian comparison at the underlying abelian sheaf `G`, which is invertible because the
derived base change map at `G` is and neither `G` nor `(g')^{-1} G` has higher direct images. -/
theorem isIso_etaleModuleBaseChange_app_of_injective :
    IsIso ((etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm).app I) :=
  isIso_etaleModuleBaseChange_app_of_isIso_forget Λ f sq I
    ((isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic f g g' f' sq.w _
      (isZero_homology_etaleAbelianDerivedDirectImage_forget_of_injective Λ f I)
      (isZero_homology_etaleAbelianDirectImage_inverseImage_forget_of_injective Λ hΛ f hpbc sq
        I)).1
      (hpbc g g' f' sq _ (torsionSheafProperty_etaleModuleForgetUniv_obj Λ hΛ I)))

include hΛ hpbc sq in
/-- **The inverse image of an injective sheaf of modules is acyclic for `f'_*`.** Forgetting the
module structure, `R^p f'_*` of it is `R^p f'_*` of the inverse image of the underlying abelian
sheaf of the injective, which vanishes for `p > 0` by proper base change. -/
theorem isZero_rightDerived_etaleModuleDirectImage_inverseImage_of_injective (p : ℕ)
    (hp : 0 < p) :
    IsZero (((etaleModuleDirectImage.{u, w} Λ f').rightDerived p).obj
      ((etaleModuleInverseImage.{u, w} Λ g').obj I)) := by
  have hac : (etaleAbelianDirectImage.{u, w} f').rightAcyclic
      ((etaleAbelianInverseImage.{u, w} g').obj ((etaleModuleForgetAb.{u, w} Λ X).obj I)) :=
    (rightAcyclic_etaleAbelianDirectImage_iff.{u, w} f' _).2 fun q hq ↦
      (isZero_homology_etaleAbelianDirectImage_inverseImage_forget_of_injective Λ hΛ f hpbc sq I q
        hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
          ((etaleAbelianDerivedDirectImage.{u, w} f').mapIso
            (((etaleAbelianInverseImage.{u, w} g').mapDerivedCategorySingleFunctor 0).app
              ((etaleModuleForgetAb.{u, w} Λ X).obj I)).symm))
  have h₀ := (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).1 hac p hp
  refine isZero_of_isZero_etaleModuleForgetUniv_obj Λ _ ?_
  exact h₀.of_iso (etaleModuleForgetRightDerivedIso Λ f' _ p ≪≫
    ((etaleAbelianDirectImage.{u, w} f').rightDerived p).mapIso
      ((etaleModuleForgetInverseImageIso.{u, w} Λ g').app I).symm)

end Injective

/-! ### The inverse image of a complex of injectives computes `Rf'_*` -/

section Acyclic

variable (Λ : Type w) [Ring Λ] (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
  {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  (hpbc : CohomologyCommutesWithBaseChange.{u, w} f)
  (hcd : ∀ ⦃T S : Scheme.{u}⦄ (h : T ⟶ S) [IsProper h] [CompactSpace S], ∃ N : ℕ,
    ∀ G : EtaleModules.{u, w} Λ T, IsZero (((etaleModuleDirectImage Λ h).rightDerived N).obj G))
  {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)

include hΛ hpbc hcd sq in
/-- **The inverse image of a complex of injective sheaves of `Λ`-modules computes `Rf'_*`.**
Let `I` be a cochain complex of injective sheaves of `Λ`-modules on `X_étale`. The question is
étale local on `Y'`
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover`), so `Y'`
may be replaced by an affine open `V`, with `f'_V : X'_V ⟶ V` the base change of `f'`. There
`(f'_V)_*` has finite cohomological dimension (`hcd`: the fibre dimensions of `f'_V` are bounded,
[Stacks, Tag 0A3V], and [Stacks, Tag 095U] applies), and the terms of the restriction of
`(g')^{-1} I` to `X'_V` are inverse images of injectives along the base change of `f` to `V`,
hence acyclic for `(f'_V)_*` by proper base change. A complex of acyclic objects for a functor
of finite cohomological dimension computes its right derived functor ([Stacks, Tag 07K7]). -/
theorem isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_inverseImage_of_injective
    (I : CochainComplex (EtaleModules.{u, w} Λ X) ℤ) [∀ k, Injective (I.X k)] :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit Λ f').app
      (((etaleModuleInverseImage Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have : IsProper f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  let 𝒰 := Y'.affineCover
  refine isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_cover Λ f' (fun i ↦ 𝒰.f i)
    (coversTop_smallEtaleObj_of_jointlySurjective _ fun y ↦ ⟨𝒰.idx y, 𝒰.covers y⟩)
    (fun i ↦ pullback.fst (𝒰.f i) f') (fun i ↦ pullback.snd (𝒰.f i) f')
    (fun i ↦ IsPullback.of_hasPullback _ _) _ fun i ↦ ?_
  have := AlgebraicGeometry.Scheme.Etale.etale_of_isPullback_snd
    (IsPullback.of_hasPullback (𝒰.f i) f')
  have : CompactSpace (𝒰.X i) := inferInstanceAs (CompactSpace (Spec _))
  obtain ⟨N, hN⟩ := hcd (pullback.fst (𝒰.f i) f')
  refine Functor.isIso_app_of_rightAcyclic_of_isZero_rightDerived _ N hN _ _ _ fun k p hp ↦ ?_
  exact (isZero_rightDerived_etaleModuleDirectImage_inverseImage_of_injective Λ hΛ f hpbc
    ((IsPullback.of_hasPullback (𝒰.f i) f').flip.paste_horiz sq)
    (I.X k) p hp).of_iso (((etaleModuleDirectImage Λ (pullback.fst (𝒰.f i) f')).rightDerived
      p).mapIso ((etaleModuleInverseImageRestrictionIso Λ (pullback.snd (𝒰.f i) f')).symm.app
        ((etaleModuleInverseImage Λ g').obj (I.X k)) ≪≫
      (etaleModuleInverseImageCompIso Λ (pullback.snd (𝒰.f i) f') g').symm.app (I.X k)))

end Acyclic

/-! ### Stacks 0F0C -/

section Main

variable (Λ : Type w) [CommRing Λ] (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
  {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  (hpbc : CohomologyCommutesWithBaseChange.{u, w} f)
  (hcd : ∀ ⦃T S : Scheme.{u}⦄ (h : T ⟶ S) [IsProper h] [CompactSpace S], ∃ N : ℕ,
    ∀ G : EtaleModules.{u, w} Λ T, IsZero (((etaleModuleDirectImage Λ h).rightDerived N).obj G))
  {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)

include hΛ hpbc hcd in
/-- **Proper base change on `D(X_étale, Λ)`, in every coefficient universe**, given the two inputs
that depend on the coefficient universe: proper base change for torsion abelian sheaves along
`f` (`hpbc`, [Stacks, Tag 095T]) and finite cohomological dimension of proper direct images
over quasi-compact bases (`hcd`, [Stacks, Tags 0A3V and 095U]). Every object of `D(X_étale, Λ)`
is represented by a K-injective complex of injectives `I` ([Stacks, Tag 079P]); the underived
comparison is invertible at each term of `I`, and `(g')^{-1} I` computes `Rf'_*`
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isKInjective`). -/
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_of_cohomologyCommutesWithBaseChange :
    IsIso (etaleModuleDerivedBaseChangeUnbounded Λ f g g' f' sq.w) := by
  have hE : ∀ E : DerivedCategory (EtaleModules.{u, w} Λ X),
      IsIso ((etaleModuleDerivedBaseChangeUnbounded Λ f g g' f' sq.w).app E) := by
    intro E
    have := Localization.essSurj DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, w} Λ X) (ComplexShape.up ℤ))
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) (Y := E)
      (self := inferInstance)
    let I := (Stacks.Injectives.kInjectiveResolutionFunctor (EtaleModules.{u, w} Λ X)).obj K
    have : IsIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion (EtaleModules.{u, w} Λ X)).app K)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    let e' : DerivedCategory.Q.obj I ≅ E :=
      (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion
        (EtaleModules.{u, w} Λ X)).app K))).symm ≪≫ e
    refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
    exact isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_injective Λ f g g' f' sq.w I
      inferInstance (fun M _ ↦ isIso_etaleModuleBaseChange_app_of_injective Λ hΛ f hpbc sq M)
      (isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_inverseImage_of_injective Λ hΛ f hpbc
        hcd sq I)
  exact NatIso.isIso_of_isIso_app _

end Main

section FiniteCohomologicalDimension

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`QuasiCompact ?f`, ...) match every goal and send instance search through
-- `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- **Finite cohomological dimension of proper direct images over a quasi-compact base**, for
sheaves of `Λ`-modules with `n = 0` in `Λ` for some `n > 0`: a proper morphism to a
quasi-compact scheme has fibres of bounded dimension ([Stacks, Tag 0A3V]), so its higher direct
images vanish above twice that bound ([Stacks, Tag 095U]). -/
@[sga "4½ Th_finitude 1.3" "special case"]
theorem exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper (Λ : Type) [Ring Λ]
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) ⦃T S : Scheme.{u}⦄ (h : T ⟶ S) [IsProper h]
    [CompactSpace S] :
    ∃ N : ℕ, ∀ G : EtaleModules Λ T,
      IsZero (((etaleModuleDirectImage Λ h).rightDerived N).obj G) := by
  have : LocallyOfFiniteType h := IsProper.toLocallyOfFiniteType
  have : UniversallyClosed h := IsProper.toUniversallyClosed
  have : QuasiCompact h := inferInstance
  obtain ⟨d, hd⟩ := AlgebraicGeometry.exists_topologicalKrullDim_fiber_le h
  exact ⟨2 * d + 1, fun G ↦ isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ h d hd G
    (torsionSheafProperty_etaleModuleForgetUniv_obj Λ hΛ G) _ (by omega)⟩

end FiniteCohomologicalDimension

/-- **Stacks Project, Tag 0F0C.** Let `f : X ⟶ Y` be a proper morphism of schemes, `g : Y' ⟶ Y`
a morphism of schemes, and `X' = Y' ×_Y X`, given as a cartesian square `sq` with projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`. Let `Λ` be a commutative ring in which some integer `n ≥ 1` is
zero — for instance `ℤ/nℤ`. Then for every object `E` of the unbounded derived category
`D(X_étale, Λ)` the base change map `g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` of [Stacks, Tag 0A2A]
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`) is an isomorphism. -/
@[stacks 0F0C "for every commutative ring Λ with n = 0 in Λ for some n ≥ 1, which contains the
source's Λ = ℤ/nℤ", sga "4 XVII 4.3.2" "special case"]
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper (Λ : Type) [CommRing Λ]
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (EtaleModules Λ X)) :
    IsIso ((etaleModuleDerivedBaseChangeUnbounded Λ f g g' f' sq.w).app E) :=
  have := isIso_etaleModuleDerivedBaseChangeUnbounded_of_cohomologyCommutesWithBaseChange Λ hΛ f
    (cohomologyCommutesWithBaseChange_of_isProper f)
    (exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ hΛ) sq
  inferInstance

end Stacks.EtaleCohomology

end
