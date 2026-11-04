module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequatorVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianSheaves
public import StacksFrontier.Algebra.Homology.DerivedCategory.HasRightDerivedFunctorPlus

/-!
# Right acyclicity of the affine-section functor at an adequate module

Let `B` be a chosen big `τ`-site over a scheme `S` and let `𝓕` be an adequate `𝒪`-module on it.
The affine-section functor `𝓕 ↦ F_{𝓕, A}` of `Stacks.Adequate.affineSectionsFunctor` is right
acyclic at `𝓕`: all its positive right derived functors vanish there. This follows from
[Stacks, Tags 06YK and 06VM].

## Main results

* `Stacks.Adequate.isZero_rightDerived_toSheafSections_of_isAdequate` — the positive right
  derived functors of "take the underlying abelian sheaf, then its sections over an affine
  object" vanish at an adequate `𝒪`-module. This is [Stacks, Tag 06VM] (3) composed with the
  comparison of [Stacks, Tag 03FD].
* `Stacks.Adequate.affineSectionsAcyclic_of_isAdequate` —
  `Stacks.Adequate.AffineSectionsAcyclic` holds at an adequate `𝒪`-module, with no hypothesis
  beyond adequacy.

## Implementation notes

The affine-section functor is `SheafOfModules.forget` followed by a pushforward, and the
pushforward is a precomposition followed by a restriction of scalars, so evaluating it at an
algebra `X` of the site is evaluating the sheaf at the affine object
`V = (affineSpecOver B A f).obj X` and restricting scalars along `Stacks.Adequate.affineRingMap`.
Both of those identifications hold by `rfl`, and restriction of scalars and the forgetful functor
to abelian groups are exact, so `Stacks.Cohomology.DerivedForget.rightDerivedCompIso` moves the
derived functor across them. The forgetful functor to abelian groups is faithful but not full, so
the passage back from a vanishing of abelian groups to a vanishing of modules is
`isZero_of_isZero_map` rather than Mathlib's
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero`.

What is left after that is the comparison of module-valued with abelian cohomology over an
object, [Stacks, Tag 03FD]. It is **not** taken from the forms of that tag indexed by a small
site or by a ringed site: a chosen big site has its objects one universe above its morphisms and
carries no `AlgebraicGeometry.RingedSite` structure. Instead the comparison is assembled from
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`, whose universes are free and
whose only input is that the underlying abelian sheaf of an injective sheaf of modules is
acyclic for sections. That acyclicity is
`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, stated with the ring universe and the
module universe independent, applied to the free abelian sheaf on the object, which is
sectionwise torsion free because free abelian groups are. The corepresentation that turns `Ext`
out of that sheaf into derived sections is, in `Stacks.Cohomology.FreeYonedaUnivLE`,
`nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`, whose coefficient universe
need only dominate the morphisms of the site, not its objects. This is what makes the statements
below hold at the module universe `max u m` of [Stacks, Tag 06ZU] rather than only at `u`.

The `attribute [-instance]` guard is needed because the ambient-universe instances on sheaves of
modules have their module universe written as a `max` of four universe variables, which
`max u m` does not match syntactically; left in place they leave the universes of the statements
below unsolved. The instances that do apply are Mathlib's, to which they unfold.

`EnoughInjectives` for the sheaves of modules at the module universe `max u m` is an instance
argument, exactly as it is for `Stacks.Adequate.isZero_rightDerived_adequator`; it is not
available from `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`, which collapses the
ring universe onto the module universe, and the structure sheaf of a chosen big site is valued in
`RingCat.{u}`. At module universe `u` it is the global instance
`Stacks.Adequate.BigSite.enoughInjectives_sheafOfModules`.

## References

* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06YK](https://stacks.math.columbia.edu/tag/06YK)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.FreeYonedaUnivLE

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u m

namespace Stacks.Adequate

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
private lemma isZero_of_isZero_map {A : Type*} [Category* A] {D : Type*} [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms D] (G : A ⥤ D) [G.PreservesZeroMorphisms]
    [G.Faithful] {X : A} (h : IsZero (G.obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact G.zero_of_map_zero _ ((G.map_id X).trans h)

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
  [EnoughInjectives (SheafOfModules.{max u m} B.structureSheaf)]

/-- **The derived abelian sections of an adequate `𝒪`-module over an affine object vanish in
positive degrees, computed in sheaves of modules.** For an affine object `V` of a chosen big
`τ`-site and an adequate `𝒪`-module `𝓕`, the positive right derived functors of
`SheafOfModules.toSheaf ⋙ (sections over V)` vanish at `𝓕`. This is [Stacks, Tag 06VM] (3)
composed with the comparison of [Stacks, Tag 03FD]. -/
public theorem isZero_rightDerived_toSheafSections_of_isAdequate (V : B.category)
    [IsAffine V.left.obj] (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F)
    (k : ℕ) (hk : 0 < k) :
    IsZero (((SheafOfModules.toSheaf.{max u m} B.structureSheaf ⋙
      (sheafSections B.topology AddCommGrpCat.{max u m}).obj (op V)).rightDerived k).obj F) := by
  have hes := B.essentiallySmall_category_max.{u, m}
  have hGA : IsGrothendieckAbelian.{max u m}
      (Sheaf B.topology AddCommGrpCat.{max u m}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u m} _ _
  set Fn := SheafOfModules.toSheaf.{max u m} B.structureSheaf
  set G := (sheafSections B.topology AddCommGrpCat.{max u m}).obj (op V)
  have hzero : ∀ (Y : Sheaf B.topology AddCommGrpCat.{max u m}) (q : ℕ),
      Subsingleton (Ext.{max u m} ((freeYoneda.{m} B.topology).obj V) Y q) →
      IsZero ((G.rightDerived q).obj Y) := by
    intro Y q h
    obtain ⟨e⟩ :=
      nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{m} B.topology V q
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h).of_iso (e.app Y).symm
  have htf : ∀ W, Module.IsTorsionFree ℤ
      (((freeYoneda.{m} B.topology).obj V).obj.obj W) := by
    apply ModuleSheafCohomology.isTorsionFree_sheafify
    exact fun W ↦ (Module.Flat.isTorsionFree :
      Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{m} (W.unop ⟶ V))))
  have hac : ∀ I : SheafOfModules.{max u m} B.structureSheaf, Injective I →
      G.rightAcyclic (Fn.obj I) := by
    intro I hI
    rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived]
    intro q hq
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
    exact hzero _ _ (subsingleton_of_forall_eq 0
      (Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree B.topology B.structureSheaf I _ htf p))
  exact (B.isZero_rightDerived_sections_of_isAdequate.{u, m} F hF V k hk).of_iso
    ((Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic Fn G hac k).app F)

/-- **The affine-section functor is right acyclic at an adequate `𝒪`-module.** For a chosen big
`τ`-site `B` over `S`, an `A`-point `f : Spec A ⟶ S` and an adequate `𝒪`-module `𝓕`, every
positive right derived functor of `Stacks.Adequate.affineSectionsFunctor B A f` vanishes at `𝓕`.
-/
public theorem affineSectionsAcyclic_of_isAdequate (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) :
    AffineSectionsAcyclic.{u, m} B A f F := by
  refine affineSectionsAcyclic_of_sections.{u, m} B A f F fun k hk X ↦ ?_
  let V : B.category := (affineSpecOver B A f).obj X.unop
  let T := SheafOfModules.forget.{max u m} B.structureSheaf ⋙
    PresheafOfModules.evaluation.{max u m} B.structureSheaf.obj (op V)
  let G := forget₂ (ModuleCat.{max u m} (B.structureSheaf.obj.obj (op V))) AddCommGrpCat.{max u m}
  let rs := ModuleCat.restrictScalars.{max u m} ((affineRingMap B A f).app X).hom
  have : T.Additive := ⟨rfl⟩
  have hTzero : IsZero ((T.rightDerived k).obj F) :=
    isZero_of_isZero_map G
      ((isZero_rightDerived_toSheafSections_of_isAdequate.{u, m} B V F hF k hk).of_iso
        ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso T G k).app F))
  exact (Functor.map_isZero rs hTzero).of_iso
    ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso T rs k).app F).symm

end Stacks.Adequate

end
