module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Cohomology commutes with base change, tested on injective sheaves of `ℤ/ℓℤ`-modules

Let `f : X ⟶ Y` be a proper morphism of schemes. [Stacks, Tag 0A4B] says that cohomology
commutes with base change for `f` (`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange`)
if and only if, for every prime `ℓ`, every injective sheaf `I` of `ℤ/ℓℤ`-modules on `X_étale` and
every cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

the higher direct images `R^q f'_* (g')⁻¹ I` vanish for `q > 0`. This file states that second
condition, `Stacks.EtaleCohomology.InjectiveBaseChangeAcyclic`, and proves the implication
(1) ⟹ (2).

## Main definitions

* `InjectiveBaseChangeAcyclic` — condition (2) of Tag 0A4B.
* `InjectiveBaseChangeIso` — the base change map is invertible at the injective sheaves of
  `ℤ/ℓℤ`-modules, the intermediate condition of the proof.

## Main results

* `isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective` — the underlying
  abelian sheaf of an injective sheaf of `ℤ/ℓℤ`-modules has no higher direct images, read in the
  unbounded derived category ([Stacks, Tag 03FD]).
* `torsionSheafProperty_toSheaf_zmod` — the underlying abelian sheaf of a sheaf of
  `ℤ/ℓℤ`-modules, `ℓ > 0`, is torsion.
* `CohomologyCommutesWithBaseChange.injectiveBaseChangeAcyclic` — the implication (1) ⟹ (2).

## Implementation notes

A sheaf of `ℤ/ℓℤ`-modules is a sheaf of modules over the constant sheaf of rings
`Stacks.Cohomology.ZModSheaf.zmodRingSheaf`, and `(g')⁻¹ I` is the inverse image of its
underlying abelian sheaf `SheafOfModules.toSheaf`; this is the reading of the source, where the
inverse image of a sheaf of `ℤ/ℓℤ`-modules is computed on underlying abelian sheaves. The
higher direct image `R^q f'_*` is the degree-`q` cohomology sheaf of the unbounded derived direct
image `etaleAbelianDerivedDirectImage`, the functor in which
`CohomologyCommutesWithBaseChange` is phrased; it agrees with the classical right derived
functor by `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.

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

/-- **Condition (2) of [Stacks, Tag 0A4B]** for a morphism of schemes `f : X ⟶ Y`: for every
prime `ℓ`, every injective sheaf `I` of `ℤ/ℓℤ`-modules on `X_étale`, every cartesian square
`g' ≫ f = f' ≫ g` with `X' = Y' ×_Y X` and every `q > 0`, the higher direct image
`R^q f'_* (g')⁻¹ I` vanishes. -/
public def InjectiveBaseChangeAcyclic {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
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

/-- **Base change at injective sheaves of `ℤ/ℓℤ`-modules**, an intermediate condition in the proof
of [Stacks, Tag 0A4B]: for every prime `ℓ`, every injective sheaf `I` of `ℤ/ℓℤ`-modules on
`X_étale` and every cartesian square `g' ≫ f = f' ≫ g` with `X' = Y' ×_Y X`, the base change map
`g⁻¹ Rf_* I ⟶ Rf'_* (g')⁻¹ I` is an isomorphism. -/
public def InjectiveBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime →
    ∀ (I : SheafOfModules.{max (u + 1) v}
        (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology ℓ)), Injective I →
    ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g),
      IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w
        ((SheafOfModules.toSheaf _).obj I))

/-- **The higher direct images of an injective sheaf of `ℤ/ℓℤ`-modules vanish**, read in the
unbounded derived category: `H^q(Rf_*(I[0])) = 0` for `q > 0`. The underlying abelian sheaf of
`I` need not be injective, but it is acyclic for the direct image ([Stacks, Tag 03FD]), and the
degree-`q` cohomology of `Rf_*(I[0])` is the classical `R^q f_* I`. -/
public theorem isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) (ℓ : ℕ)
    (I : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology ℓ))
    [Injective I] (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
              ((SheafOfModules.toSheaf _).obj I)))) := by
  have : HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, v}
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = ((p + 1 : ℕ) : ℤ) := ⟨q.toNat - 1, by omega⟩
  exact IsZero.of_iso
    (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{v}
      Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange f) _ I p)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
      (etaleAbelianDerivedDirectImageUnit.{u, v} f)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective (p + 1)).app _)

/-- **The underlying abelian sheaf of a sheaf of `ℤ/ℓℤ`-modules is torsion**, for `ℓ > 0`: its
sections are annihilated by `ℓ`. -/
public theorem torsionSheafProperty_toSheaf_zmod {X : Scheme.{u}} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (M : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology ℓ)) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((SheafOfModules.toSheaf _).obj M) := fun U _ ↦
  ⟨⊤, X.smallEtaleTopology.top_mem U, fun _ _ _ ↦
    ⟨ℓ, hℓ, nsmul_toSheaf_eq_zero.{max (u + 1) v, max (u + 1) v} _ ℓ M _ _⟩⟩

/-- **Vanishing transported across an invertible base change map.** If the base change map of a
commutative square is invertible at an abelian sheaf `G` and `H^q(Rf_* G[0])` vanishes, then so
does `H^q(Rf'_* (g')⁻¹ G[0])`: it is `H^q(g⁻¹ Rf_* G[0]) = g⁻¹ H^q(Rf_* G[0])`. -/
public theorem isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (h : g' ≫ f = f' ≫ g) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G)] (q : ℤ)
    (hG : IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G)))) :
    IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f').obj
          ((etaleAbelianDerivedInverseImage.{u, v} g').obj
            ((DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj G)))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    (asIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h G))).symm
  exact IsZero.of_iso (Functor.map_isZero (etaleAbelianInverseImage.{u, v} g) hG)
    ((Stacks.DerivedFunctor.derivedHomologyIso (etaleAbelianInverseImage.{u, v} g) q).app _)

/-- **Base change at injective sheaves of `ℤ/ℓℤ`-modules forces condition (2) of
[Stacks, Tag 0A4B].** If the base change map is invertible at every injective sheaf of
`ℤ/ℓℤ`-modules, the higher direct images `R^q f'_* (g')⁻¹ I` are `g⁻¹ R^q f_* I`, which vanish in
positive degrees ([Stacks, Tag 03FD]). -/
public theorem InjectiveBaseChangeIso.injectiveBaseChangeAcyclic {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : InjectiveBaseChangeIso.{u, v} f) :
    InjectiveBaseChangeAcyclic.{u, v} f := by
  intro ℓ hℓ I hI X' Y' g g' f' sq q hq
  have := hf ℓ hℓ I hI g g' f' sq
  exact isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso f g g' f' sq.w _ q
    (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective f ℓ I q hq)

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0A4B].** If cohomology commutes with base change
for `f`, then the base change map identifies `R^q f'_* (g')⁻¹ I` with `g⁻¹ R^q f_* I`, which is
zero for `q > 0` because `I` is acyclic for the direct image. -/
public theorem CohomologyCommutesWithBaseChange.injectiveBaseChangeAcyclic {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : CohomologyCommutesWithBaseChange.{u, v} f) :
    InjectiveBaseChangeAcyclic.{u, v} f :=
  InjectiveBaseChangeIso.injectiveBaseChangeAcyclic fun ℓ hℓ I _ _ _ g g' f' sq ↦
    hf g g' f' sq _ (torsionSheafProperty_toSheaf_zmod (ℓ := ℓ) hℓ.pos I)

end Stacks.EtaleCohomology

end
