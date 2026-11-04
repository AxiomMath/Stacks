module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap

/-!
# The vanishing condition of Stacks 0A4B (2)

For a morphism of schemes `f : X ⟶ Y`, condition (2) of
[Stacks, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B) asks that for every prime `ℓ`,
every injective sheaf of `ℤ/ℓℤ`-modules `I` on `X_étale` and every cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
the higher direct images `R^q f'_* (g')^{-1} I` vanish for `q > 0`. Lemma 0A4B says that for
proper `f` this is equivalent to cohomology commuting with base change for `f`. This file states
the condition, proves the implication (1) ⟹ (2), and collects the facts about injective sheaves
of `ℤ/nℤ`-modules that the converse uses.

## Main definitions

All names are in the namespace `Stacks.EtaleCohomology`.

* `HigherDirectImagesVanishOnInjectives` — condition (2).

## Main results

* `isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective` — the underlying
  abelian sheaf of an injective sheaf of `ℤ/ℓℤ`-modules has no higher direct images, read in the
  unbounded derived category ([Stacks, Tag 03FD]).
* `torsionSheafProperty_toSheaf_zmod` — the underlying abelian sheaf of a sheaf of `ℤ/ℓℤ`-modules,
  `ℓ > 0`, is torsion.
* `exists_mono_toSheaf_injective` — an abelian sheaf killed by `n` embeds in the underlying
  abelian sheaf of an injective sheaf of `ℤ/nℤ`-modules.
* `isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg` — both sides of a base change map
  have no cohomology in negative degrees at a sheaf in degree zero.
* `CohomologyCommutesWithBaseChange.higherDirectImagesVanishOnInjectives` — the implication
  (1) ⟹ (2).

## Implementation notes

A sheaf of `ℤ/ℓℤ`-modules is a sheaf of modules over the constant sheaf of rings
`Stacks.Cohomology.ZModSheaf.zmodRingSheaf`, and `(g')⁻¹ I` is the inverse image of its
underlying abelian sheaf `SheafOfModules.toSheaf`, at exactly the coefficient universe of
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, v}`. The higher direct images are
those of abelian sheaves: `R^q f'_*` is the `q`-th cohomology sheaf of the unbounded derived direct
image evaluated at the sheaf placed in degree zero. The source's `R^q` could equally be read in
sheaves of `ℤ/ℓℤ`-modules; the two readings agree by
[Stacks, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD).

## References

* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **Condition (2) of [Stacks, Tag 0A4B]** for `f : X ⟶ Y`: for every prime `ℓ`, every
injective sheaf `I` of `ℤ/ℓℤ`-modules on `X_étale`, every cartesian square with `X' = Y' ×_Y X`
and every `q > 0`, the higher direct image `R^q f'_* (g')^{-1} I` vanishes. -/
public def HigherDirectImagesVanishOnInjectives {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime →
    ∀ (I : SheafOfModules.{max (u + 1) v}
        (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology ℓ)), Injective I →
    ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g →
    ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f').obj
          ((etaleAbelianDerivedInverseImage.{u, v} g').obj
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
              ((SheafOfModules.toSheaf _).obj I)))))

section Torsion

variable {X : Scheme.{u}}

/-- **An abelian sheaf on `X_étale` killed by `n` embeds in the underlying abelian sheaf of an
injective sheaf of `ℤ/nℤ`-modules**, at the coefficients `AddCommGrpCat.{u + 1}` of the proper
base change development. Being killed by `n`, it is the underlying sheaf of a sheaf
of `ℤ/nℤ`-modules (`Stacks.Cohomology.ZModSheaf.torsionSheafToModules`), and sheaves of modules
on the small étale site have enough injectives. -/
public theorem exists_mono_toSheaf_injective (n : ℕ)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : n • 𝟙 A = 0) :
    ∃ (J : SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} X.smallEtaleTopology n)) (_ : Injective J)
      (i : A ⟶ (SheafOfModules.toSheaf _).obj J), Mono i := by
  have hA' : ∀ (U : X.Etale) (x : A.obj.obj (Opposite.op U)), (n : ℤ) • x = 0 := by
    intro U x
    refine (zsmul_id_eq_zero_iff A n).1 ?_ (Opposite.op U) x
    rw [natCast_zsmul]
    exact hA
  have : EnoughInjectives (SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} X.smallEtaleTopology n)) :=
    enoughInjectives_etaleZModModules X (n : ℤ)
  exact ⟨Injective.under _, Injective.injective_under _,
    torsionEtaleInjectiveEmbedding A hA', mono_torsionEtaleInjectiveEmbedding A hA'⟩

end Torsion

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0A4B].** If cohomology commutes with base change
for `f`, then the base change map identifies `R^q f'_* (g')⁻¹ I` with `g⁻¹ R^q f_* I`, which is
zero for `q > 0` because `I` is acyclic for the direct image. -/
public theorem CohomologyCommutesWithBaseChange.higherDirectImagesVanishOnInjectives
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : CohomologyCommutesWithBaseChange.{u, v} f) :
    HigherDirectImagesVanishOnInjectives.{u, v} f := by
  intro ℓ hℓ I hI X' Y' g g' f' sq q hq
  have := hf g g' f' sq _ (torsionSheafProperty_toSheaf_zmod hℓ.pos I)
  exact isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso f g g' f' sq.w _ q
    (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective f ℓ I q hq)

end Stacks.EtaleCohomology

end
