module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.HomotopyComputesMaps
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor

/-!
# The corepresentability input of Tag 0D6J on the small étale site

For `T` an additive functor on abelian sheaves of the small étale site which is corepresented by
a *sectionwise torsion-free* sheaf `A₀`, the right-derived unit of `T` is invertible at the
abelian complex underlying any K-injective complex of sheaves of `Λ`-modules.

This is the hinge of the first diagram of [Stacks, Tag 0GL6]: it is the one place where the
torsion-free dévissage of [Stacks, Tag 0D6J] is actually used.  Everything above it -- the
direct-image unit, and the comparison of the two derived direct images -- is an instantiation of
generic machinery that already exists at full generality in the library.

## Main results

* `Stacks.EtaleCohomology.isTorsionFree_single`
* `Stacks.EtaleCohomology.qh_map_bijective_single_of_isKInjective`
* `Stacks.EtaleCohomology.rightDerivedUnit_isIso_of_isKInjective`

## Implementation notes

The corepresenting sheaf is required to be sectionwise torsion free, and that is what makes the
argument go: extension of coefficients is exact on a resolution by such sheaves, so maps out of
the single complex on `A₀` are computed in the homotopy category
(`Stacks.EtaleCohomology.qh_map_bijective_of_isLE_of_isTorsionFree`), which is exactly the
hypothesis `Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable`
consumes.  The shifts are handled by transporting that bijectivity along the shift isomorphism
of the forgetful functor, as `DerivedLowerShriek.qh_map_bijective_of_iso` is designed for.

**Where to look when a site-level result does not fit.**  Four times in this chain a tagged
site-level theorem has turned out to be stated for a `SmallCategory` site, or with the site's
object and hom universes collapsed to one, or with the coefficient universe pinned to the
site's -- and the small étale site is excluded by each, being large, only essentially small, and
carrying sheaves at a module universe strictly above its own.  Four times the *generic* section
of the very same file has been public, smallness-free and at independent universes.  So the
expectation to carry is: when a tagged site-level theorem does not fit, look in its own file for
the generic section it was specialised from -- the specialisation is usually what collapsed, and
the general form is usually public.  `Stacks.Cohomology.ForgetModule`'s `section General` versus
its `section Pushforward` (`RingedSite.{u, u, u}`) is the cleanest instance.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **A single complex on a sectionwise torsion-free sheaf has sectionwise torsion-free terms.**
In the degree carrying the sheaf this is the identity; in every other degree the term is zero,
and the zero map out of it is a mono. -/
theorem isTorsionFree_single (F : EtaleAbelianSheaves.{u, r} X)
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)) (n i : ℤ) :
    ∀ V, Module.IsTorsionFree ℤ
      ((((CochainComplex.singleFunctor (EtaleAbelianSheaves.{u, r} X) n).obj F).X i).obj.obj
        V) := by
  obtain ⟨f, hf⟩ : ∃ f : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F, Mono f := by
    by_cases hi : i = n
    · subst i
      exact ⟨(HomologicalComplex.singleObjXSelf (.up ℤ) n F).hom, inferInstance⟩
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) n F i hi
      exact ⟨0, ⟨fun _ _ _ => hz.eq_of_tgt _ _⟩⟩
  exact ModuleSheafCohomology.isTorsionFree_of_mono _ f hF

/-- **Maps out of a sectionwise torsion-free single complex into the abelian complex underlying a
K-injective complex of `Λ`-modules are computed in the homotopy category**, in every shift.  This
is `qh_map_bijective_of_isLE_of_isTorsionFree` at a single complex, transported across the
shift. -/
theorem qh_map_bijective_single_of_isKInjective (A₀ : EtaleAbelianSheaves.{u, r} X)
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).obj
            ((CochainComplex.singleFunctor (EtaleAbelianSheaves.{u, r} X) 0).obj A₀) ⟶
          (HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).obj
            ((((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomologicalComplex
              (.up ℤ)).obj I)⟦n⟧)) → _) := by
  let : (I⟦n⟧).IsKInjective := inferInstance
  have hbij := qh_map_bijective_of_isLE_of_isTorsionFree.{u, r} Λ X
    ((CochainComplex.singleFunctor (EtaleAbelianSheaves.{u, r} X) 0).obj A₀) 0
    (isTorsionFree_single.{u, r} X A₀ hA₀ 0) (I⟦n⟧)
  exact Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).mapIso
      (((etaleModuleForgetToAbelian.{u, r} Λ X).mapCochainComplexShiftIso n).app I)) hbij

/-- **The right-derived unit of a corepresented additive functor is invertible at the abelian
complex underlying a K-injective complex of `Λ`-modules**, provided the corepresenting sheaf is
sectionwise torsion free.  This is the corepresentability input of [Stacks, Tag 0D6J] on the
small étale site. -/
theorem rightDerivedUnit_isIso_of_isKInjective
    (T : EtaleAbelianSheaves.{u, r} X ⥤ AddCommGrpCat.{max (u + 1) r}) [T.Additive]
    (A₀ : EtaleAbelianSheaves.{u, r} X)
    (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (RT : DerivedCategory (EtaleAbelianSheaves.{u, r} X) ⥤
      DerivedCategory AddCommGrpCat.{max (u + 1) r})
    (α : T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleAbelianSheaves.{u, r} X) (.up ℤ))]
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)).obj
      (((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).obj I))) :=
  Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable T A₀ e RT α _
    (qh_map_bijective_single_of_isKInjective.{u, r} Λ X A₀ hA₀ I)

end Stacks.EtaleCohomology

end
