module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SiteEquivalenceCohomology

/-!
# Cohomology of an algebraic space over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Y` be an algebraic space over `S`
together with a morphism `φ : Y ⟶ W` to the representable algebraic space of `W`. By Stacks
04SG, `Y` is the lower-shriek extension `Λ_h Y'` of an algebraic space `Y'` over `W`,
`AlgebraicGeometry.Space.spaceOverSmallerBase`. The two are the same space seen over two bases,
and this file shows that their cohomology is the same:

* their small étale sites are equivalent, with the same underlying schemes, so that their
  structure sheaves correspond on the nose;
* the categories of modules are therefore equivalent, by
  `AlgebraicGeometry.Space.smallerBaseModulesEquivalence`;
* the cohomology of a module on `Y` is that of the corresponding module on `Y'`, and the
  structure of `W`-module that `φ` puts on the former is the one the structure morphism of `Y'`
  puts on the latter.

For `W = Spec k` the spectrum of a field this says that the Euler characteristic of a module on
`Y`, computed along `φ` (`AlgebraicGeometry.Space.eulerCharacteristicAlong`), is the alternating
sum of the dimensions of the cohomology of the corresponding module on the algebraic space `Y'`
over `Spec k`: the alternating sum that `AlgebraicGeometry.Space.eulerCharacteristic` (Stacks
0DN1) takes for a proper `Y'`.

## Main definitions

* `AlgebraicGeometry.Space.spaceOverSmallerBase`: the algebraic space `Y'` over `W` with
  `Λ_h Y' ≅ Y` over `W`, the quasi-inverse of Stacks 04SG.
* `AlgebraicGeometry.Space.relocalizeSpaceOverSmallerBaseIso`: the identification `Λ_h Y' ≅ Y`.
* `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence`: the small étale sites of `Y'` and
  of `Y` are equivalent.
* `AlgebraicGeometry.Space.smallerBaseModulesEquivalence`: the module categories of `Y` and `Y'`
  are equivalent.
* `AlgebraicGeometry.Space.smallerBaseCohomologyIso`: the cohomology of a module on `Y`, as a
  module over `Γ(W, 𝒪_W)` along `φ`, is the cohomology over the base `W` of the corresponding
  module on `Y'`.

## Main results

* `AlgebraicGeometry.Space.relocalizeSpaceOverSmallerBaseIso_hom_comp`: the identification
  `Λ_h Y' ≅ Y` is one over `W`.
* `AlgebraicGeometry.Space.eulerCharacteristicAlong_eq_finsum_spaceOverSmallerBase`: **the
  Euler characteristic along `Y ⟶ Spec k` is the alternating sum of the dimensions of the
  cohomology over `Spec k` of the corresponding module on `Y'`.**

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) (Y : AlgebraicSpaces B S hS) (φ : Y.1 ⟶ yoneda.obj (Over.mk h))

/-! ### The space over the smaller base -/

/-- **The algebraic space over `W` underlying an algebraic space `Y` over `S` with a morphism
`φ : Y ⟶ W`**: the image of `(Y, φ)` under the quasi-inverse of the equivalence of Stacks
04SG. -/
def spaceOverSmallerBase : AlgebraicSpaces B W hW :=
  (spacesOverSmallerBaseEquivalence B W S hW hS h).inverse.obj ⟨Over.mk φ, Y.2⟩

/-- The lower-shriek extension of `AlgebraicGeometry.Space.spaceOverSmallerBase` is `Y` again:
the counit of the equivalence of Stacks 04SG, read through the identification of its functor
with the lower-shriek extension. -/
def relocalizeSpaceOverSmallerBaseIso :
    (OverShriek.relocalizePresheafFunctor h).obj (spaceOverSmallerBase B W S hW hS h Y φ).1 ≅
      Y.1 :=
  ((smallerBasePresheafForgetIso B W S hW hS h).app
      (spaceOverSmallerBase B W S hW hS h Y φ).1).symm ≪≫
    (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso
      ((spacesOverSmallerBaseEquivalence B W S hW hS h).counitIso.app ⟨Over.mk φ, Y.2⟩))

/-- **The identification `Λ_h Y' ≅ Y` is one over `W`**: followed by `φ` it is the structural
morphism of the lower-shriek extension, which reads off the factorization through `W`. -/
theorem relocalizeSpaceOverSmallerBaseIso_hom_comp :
    (relocalizeSpaceOverSmallerBaseIso B W S hW hS h Y φ).hom ≫ φ =
      OverShriek.relocalizeToYoneda h (spaceOverSmallerBase B W S hW hS h Y φ).1 := by
  have hw := Over.w ((ObjectProperty.ι _).map
      ((spacesOverSmallerBaseEquivalence B W S hW hS h).counitIso.hom.app ⟨Over.mk φ, Y.2⟩))
  rw [← relocalizeToYoneda_eq B W S hW hS h (spaceOverSmallerBase B W S hW hS h Y φ)]
  simp only [relocalizeSpaceOverSmallerBaseIso]
  exact congrArg (fun k => (smallerBasePresheafForgetIso B W S hW hS h).inv.app
    (spaceOverSmallerBase B W S hW hS h Y φ).1 ≫ k) hw

/-- **The small étale sites of `Y'` and of `Y` are equivalent**, by an equivalence which does
not change the underlying scheme of a chart: the equivalence of the small étale sites of `Y'`
and of its lower-shriek extension, followed by the one induced by the identification
`Λ_h Y' ≅ Y`. -/
def smallerBaseSmallEtaleEquivalence :
    SmallEtale B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1 ≌ SmallEtale B S hS Y.1 :=
  (SmallEtale.relocalizeEquivalence B W S hW hS h (spaceOverSmallerBase B W S hW hS h Y φ).1).trans
    (SmallEtale.congr B S hS (relocalizeSpaceOverSmallerBaseIso B W S hW hS h Y φ))

/-- The functor of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence` is continuous for
the étale topologies on the small étale sites of `Y'` and of `Y`. -/
instance smallerBaseSmallEtaleEquivalence_functor_isContinuous :
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor.IsContinuous
      (SmallEtale.topology B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1)
      (SmallEtale.topology B S hS Y.1) :=
  have := SmallEtale.congr_functor_isContinuous B S hS
    (relocalizeSpaceOverSmallerBaseIso B W S hW hS h Y φ)
  Functor.isContinuous_comp _ _ _
    (SmallEtale.topology B S hS
      ((OverShriek.relocalizePresheafFunctor h).obj (spaceOverSmallerBase B W S hW hS h Y φ).1)) _

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence` is continuous for
the étale topologies on the small étale sites of `Y` and of `Y'`. -/
instance smallerBaseSmallEtaleEquivalence_inverse_isContinuous :
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).inverse.IsContinuous
      (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1) :=
  have : (SmallEtale.congr B S hS
      (relocalizeSpaceOverSmallerBaseIso B W S hW hS h Y φ)).inverse.IsContinuous
      (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS
        ((OverShriek.relocalizePresheafFunctor h).obj
          (spaceOverSmallerBase B W S hW hS h Y φ).1)) :=
    Functor.isContinuous_iff_coverPreserving.2 (SmallEtale.congr_inverse_coverPreserving B S hS _)
  Functor.isContinuous_comp _ _ _
    (SmallEtale.topology B S hS
      ((OverShriek.relocalizePresheafFunctor h).obj (spaceOverSmallerBase B W S hW hS h Y φ).1)) _

/-- **The modules on `Y` and on `Y'` are the same**: transport along the equivalence of small
étale sites `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence`, which carries the
structure sheaf of `Y` to that of `Y'` on the nose. -/
def smallerBaseModulesEquivalence :
    Modules.{u, m} B S hS Y.1 Y.2 ≌
      Modules.{u, m} B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2 :=
  @Stacks.SheafOfModules.reindexEquivalence.{u, m} _ _ _ _
    (smallEtaleRingedSite B S hS Y.1 Y.2).J
    (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).J
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ)
    (smallerBaseSmallEtaleEquivalence_functor_isContinuous B W S hW hS h Y φ)
    (smallerBaseSmallEtaleEquivalence_inverse_isContinuous B W S hW hS h Y φ)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)

/-- **A chart of `Y'`, read as a chart of `Y`, maps to `W` by its structure morphism**: the
morphism `U ⟶ W` that `φ` induces on the chart of `Y` attached to a chart `U` of `Y'` is the
structure morphism of `U` as a scheme over `W`. -/
theorem chartToScheme_smallerBaseSmallEtaleEquivalence_functor_obj
    (U : SmallEtale B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1) :
    chartToScheme B S hS Y.1 φ
        ((smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor.obj U) =
      relocalizeOverHom B W S hW hS h
        ((SmallEtale.toOver B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1).obj U) := by
  apply Yoneda.fullyFaithful.map_injective
  rw [chartToScheme, Functor.FullyFaithful.map_preimage]
  refine Eq.trans ?_ (relocalizeChart_comp_relocalizeToYoneda B W S hW hS h U.obj.hom)
  rw [← relocalizeSpaceOverSmallerBaseIso_hom_comp B W S hW hS h Y φ]
  rfl

/-- The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})` restricting global functions along the
equivalence of small étale sites; it is bijective, by
`Stacks.Cohomology.SiteModules.bijective_reindexGlobalSectionRingHom`. -/
abbrev smallerBaseGlobalSectionRingHom :
    Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) →+*
      Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
            (spaceOverSmallerBase B W S hW hS h Y φ).2).O)) :=
  @Stacks.Cohomology.SiteModules.reindexGlobalSectionRingHom _ _ _ _
    (smallEtaleRingedSite B S hS Y.1 Y.2).J
    (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).J
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ)
    (smallerBaseSmallEtaleEquivalence_functor_isContinuous B W S hW hS h Y φ)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))

/-- **The cohomology of a module on `Y` is that of the corresponding module on `Y'`**, as modules
over `Γ(Y, 𝒪_Y)`, the latter along `AlgebraicGeometry.Space.smallerBaseGlobalSectionRingHom`. -/
def smallerBaseGlobalModuleCohomologyIso (M : Modules.{u, max (u + 1) m} B S hS Y.1 Y.2) (i : ℕ) :
    (Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) i).obj
          M ≅
      (ModuleCat.restrictScalars (smallerBaseGlobalSectionRingHom B W S hW hS h Y φ)).obj
        ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, m}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
              (spaceOverSmallerBase B W S hW hS h Y φ).2).O)) i).obj
          ((smallerBaseModulesEquivalence.{u, max (u + 1) m} B W S hW hS h Y φ).functor.obj M)) :=
  @Stacks.Cohomology.SiteModules.reindexGlobalModuleCohomologyIso.{u + 1, u, u, m} _ _ _ _
    (smallEtaleRingedSite B S hS Y.1 Y.2).J
    (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).J
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ)
    (smallerBaseSmallEtaleEquivalence_functor_isContinuous B W S hW hS h Y φ)
    (smallerBaseSmallEtaleEquivalence_inverse_isContinuous B W S hW hS h Y φ)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) M i

/-! ### Cohomology over an affine smaller base -/

section Affine

variable (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A))) (g : B.obj hA ⟶ B.obj hS)
  (φA : Y.1 ⟶ yoneda.obj (Over.mk g))

/-- The ring map `A ⟶ Γ(Y, 𝒪_Y)` that a morphism `φ : Y ⟶ Spec A` induces on global functions,
`A = Γ(Spec A, 𝒪)` being read through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
abbrev smallerBaseRingHom :
    A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
  (globalSectionsRingHom B S hS Y.1 Y.2 φA).comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- **The `A`-module structure that `φ : Y ⟶ Spec A` puts on global functions of `Y` is the one
the structure morphism of `Y'` puts on those of `Y'`**: restricting along the equivalence of
small étale sites intertwines `AlgebraicGeometry.Space.smallerBaseRingHom` with
`AlgebraicGeometry.Space.baseRingHom`. -/
theorem reindexGlobalSectionRingHom_comp_smallerBaseRingHom :
    (smallerBaseGlobalSectionRingHom B _ S hA hS g Y φA).comp
      (smallerBaseRingHom B S hS Y A hA g φA) =
    baseRingHom A B hA (spaceOverSmallerBase B _ S hA hS g Y φA).1
      (spaceOverSmallerBase B _ S hA hS g Y φA).2 := by
  ext a U
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS Y.1 φA
      ((smallerBaseSmallEtaleEquivalence B _ S hA hS g Y φA).functor.obj U.unop))).op).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a) = _
  refine (congrArg (fun (k : _ ⟶ Over.mk g) =>
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a))
    (chartToScheme_smallerBaseSmallEtaleEquivalence_functor_obj B _ S hA hS g Y φA
      (U.unop : SmallEtale B (Spec (.of A)) hA
        (spaceOverSmallerBase B _ S hA hS g Y φA).1))).trans ?_
  rfl

/-- **The cohomology of a module on `Y`, as an `A`-module along `φ : Y ⟶ Spec A`, is the
cohomology over the base `Spec A` of the corresponding module on `Y'`.** -/
def smallerBaseCohomologyIso (M : Modules.{u, max (u + 1) m} B S hS Y.1 Y.2) (i : ℕ) :
    (ModuleCat.restrictScalars (smallerBaseRingHom B S hS Y A hA g φA)).obj
        ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, m}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) i).obj
            M) ≅
      cohomologyOverBase.{u, m} A B hA (spaceOverSmallerBase B _ S hA hS g Y φA).1
        (spaceOverSmallerBase B _ S hA hS g Y φA).2
        ((smallerBaseModulesEquivalence.{u, max (u + 1) m} B _ S hA hS g Y φA).functor.obj M) i :=
  (ModuleCat.restrictScalars (smallerBaseRingHom B S hS Y A hA g φA)).mapIso
      (smallerBaseGlobalModuleCohomologyIso.{u, m} B _ S hA hS g Y φA M i) ≪≫
    (ModuleCat.restrictScalarsComp'App (smallerBaseRingHom B S hS Y A hA g φA)
      (smallerBaseGlobalSectionRingHom B _ S hA hS g Y φA) _
      (reindexGlobalSectionRingHom_comp_smallerBaseRingHom B S hS Y A hA g φA).symm _).symm

end Affine

/-! ### The Euler characteristic over a field -/

section Field

variable (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (g : B.obj hk ⟶ B.obj hS)
  (φk : Y.1 ⟶ yoneda.obj (Over.mk g))

/-- **The Euler characteristic of a module on `Y` along `φ : Y ⟶ Spec k` is computed on the
algebraic space `Y'` over `Spec k`**: it is the alternating sum of the `k`-dimensions of the
cohomology over the base `Spec k` of the corresponding module on `Y'`, the sum which
`AlgebraicGeometry.Space.eulerCharacteristic` (Stacks 0DN1) takes for a proper `Y'`. -/
theorem eulerCharacteristicAlong_eq_finsum_spaceOverSmallerBase
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    eulerCharacteristicAlong B S hS Y.1 Y.2 k (smallerBaseRingHom B S hS Y k hk g φk) M =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k
        (cohomologyOverBase.{u, u + 1} k B hk (spaceOverSmallerBase B _ S hk hS g Y φk).1
          (spaceOverSmallerBase B _ S hk hS g Y φk).2
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
            ((smallerBaseModulesEquivalence.{u, u} B _ S hk hS g Y φk).functor.obj M)) i) : ℤ) := by
  unfold eulerCharacteristicAlong
  refine finsum_congr fun i => ?_
  congr 2
  exact (smallerBaseCohomologyIso.{u, u + 1} B S hS Y k hk g φk
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} M) i).toLinearEquiv.finrank_eq

end Field

end AlgebraicGeometry.Space

end
