module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Collapse of cohomology along a direct image with vanishing higher direct images

Let `f : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed topoi and `F` an `O_C`-module
whose higher direct images vanish. Then the cohomology of `F` on the source agrees with the
cohomology of `f_*F` on the target, in every degree.

## Main results

* `Stacks.Cohomology.Leray.nonempty_cohomologyIso_pushforward`: part (1) of Stacks 0733, the
  identification `H^p(C, F) = H^p(D, f_*F)` when the higher direct images of `F` vanish.
* `Stacks.Cohomology.Leray.nonempty_cohomologyIso_globalSections_higherDirectImage`: part (2) of
  Stacks 0733, the identification `H^q(C, F) = H^0(D, R^q f_* F)` when the higher direct images of
  `F` have no higher cohomology on the target.

## Implementation notes

Both sides of the source's equalities are modules, over `Γ(C, O_C)` on the left and `Γ(D, O_D)`
on the right. The comparison is an isomorphism of `Γ(D, O_D)`-modules after restricting the
scalars of the left hand side along the ring map `Γ(D, O_D) ⟶ Γ(C, O_C)` induced by the structure
morphism of `f`, which is
`Stacks.Cohomology.SiteModules.globalSectionsRingHom`.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology.Leray

universe u

/-- Additivity of the global sections of sheaves of modules over the structure sheaf of a ringed
topos, pinned at the shape the statements below take it in.

`Stacks.Cohomology.SiteModules.globalSectionsFunctor_additive` is stated for an opaque sheaf of
rings `R`, and the module category it lands in is read off the projection `R.obj`. Since
`Stacks.SheafOfModules.Tensor.ringSheaf Z.O` is a reducible abbreviation for a `Sheaf`
constructor application, that projection reduces away here and instance search no longer matches
the general instance. Naming it at the reduced shape is what keeps it available; the proof is the
general instance itself. -/
local instance additive_globalSectionsFunctor (Z : RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] :
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).Additive :=
  globalSectionsFunctor_additive _

section Helpers

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  (f : RingedToposHom X Y)

/-- Stacks 072Z, in the form the collapse isomorphisms below consume. -/
lemma isTotallyAcyclic_pushforward_injective
    [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasSheafify Y.J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hZ : Injective Z) :
    Stacks.Cohomology.IsTotallyAcyclic Y.J
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        ((pushforwardModules f).obj Z)) :=
  Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective f Z

/-- Restriction of scalars along the comparison of global section rings preserves homology: it is
exact, being both a left and a right adjoint. -/
lemma preservesHomology_restrictScalars
    [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (ModuleCat.restrictScalars (globalSectionsRingHom f)).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

end Helpers

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [PreservesFiniteLimits
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u}
    (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))]
  [((globalSectionsFunctor.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  (f : RingedToposHom X Y)
  [PreservesFiniteLimits (pushforwardModules f)]

/-- A sheaf of modules whose underlying abelian sheaf is totally acyclic has vanishing higher
right derived global sections, in Mathlib's `ℕ`-indexing. This is part (3) of Stacks 0731 read
through the comparison of the two indexings of right acyclicity. -/
lemma acyclic_globalSections_of_isTotallyAcyclic
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D} (R : Sheaf K RingCat.{u})
    (M : SheafOfModules.{u} R) [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    [EnoughInjectives (SheafOfModules.{u} R)]
    [PreservesFiniteLimits (globalSectionsFunctor.{u, u, u, u} R)]
    [HasDerivedCategory.{u} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (RingCat.sectionsSubring R.obj))]
    [((globalSectionsFunctor.{u, u, u, u} R).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} R))]
    (hM : Stacks.Cohomology.IsTotallyAcyclic K ((SheafOfModules.toSheaf R).obj M)) :
    Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u, u, u, u} R) M :=
  (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ M).1
    (Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections R M hM)

/-- If every higher direct image of `F` vanishes and `f_*` carries injectives to objects acyclic
for global sections on the target, the cohomology of `F` computed as the derived functor of
`Γ(D, f_* −)` is the cohomology of `f_*F` on the target.

The comparison is the one computed by applying `f_*` to an injective resolution `I` of `F`: the
vanishing makes `f_*I` a resolution of `f_*F`, and the acyclicity of its terms makes it compute
the cohomology of `f_*F` as well. -/
noncomputable def cohomologyIsoOfVanishingHigherDirectImagesAux
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (I : InjectiveResolution F)
    (hF : ∀ q, 0 < q → IsZero (((pushforwardModules f).rightDerived q).obj F))
    (hacyclic : ∀ q, Stacks.RightDerivedComp.acyclic
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((Stacks.RightDerivedComp.mapCocomplex (pushforwardModules f) I).X q))
    (p : ℕ) :
    ((pushforwardModules f ⋙
        globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).rightDerived p).obj F ≅
      ((globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).rightDerived p).obj
        ((pushforwardModules f).obj F) :=
  have : QuasiIso (Stacks.RightDerivedComp.mapι (pushforwardModules f) I) :=
    Stacks.RightDerivedComp.quasiIso_mapι (pushforwardModules f) I hF
  I.isoRightDerivedObj (pushforwardModules f ⋙
      globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) p ≪≫
    (Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (Stacks.RightDerivedComp.mapι (pushforwardModules f) I) hacyclic p).symm

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [PreservesFiniteLimits (pushforwardModules f)] in
/-- Stacks 072Z makes every term of the direct image of an injective resolution acyclic for
global sections on the target: the terms are direct images of injective modules. -/
lemma acyclic_mapCocomplex_X
    (h072Z : ∀ Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), Injective Z →
      Stacks.Cohomology.IsTotallyAcyclic Y.J
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((pushforwardModules f).obj Z)))
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (I : InjectiveResolution F) (q : ℕ) :
    Stacks.RightDerivedComp.acyclic
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((Stacks.RightDerivedComp.mapCocomplex (pushforwardModules f) I).X q) :=
  acyclic_globalSections_of_isTotallyAcyclic _ _ (h072Z _ (I.injective q))

/-- **Part (1) of Stacks 0733**, with the acyclicity input of Stacks 072Z as a hypothesis.
If every higher direct image of `F` vanishes, the cohomology of `F` on the source — computed as
the derived functor of `Γ(D, f_* −)` — is the cohomology of `f_*F` on the target. -/
noncomputable def cohomologyIsoOfVanishingHigherDirectImages
    (h072Z : ∀ Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), Injective Z →
      Stacks.Cohomology.IsTotallyAcyclic Y.J
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((pushforwardModules f).obj Z)))
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ q, 0 < q → IsZero (((pushforwardModules f).rightDerived q).obj F))
    (p : ℕ) :
    ((pushforwardModules f ⋙
        globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).rightDerived p).obj F ≅
      (globalModuleCohomology.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) p).obj
        ((pushforwardModules f).obj F) :=
  cohomologyIsoOfVanishingHigherDirectImagesAux f F (injectiveResolution F) hF
    (acyclic_mapCocomplex_X f h072Z (injectiveResolution F)) p

/-- **Part (2) of Stacks 0733**, with the acyclicity input of Stacks 072Z as a hypothesis.
If the higher direct images of `F` all have vanishing higher cohomology on the target, then the
cohomology of `F` on the source — computed as the derived functor of `Γ(D, f_* −)` — is the
module of global sections of the corresponding higher direct image.

The direct image of an injective resolution of `F` has `R^q f_* F` for cohomology and acyclic
terms, so the hypothesis makes both its terms and its cohomology acyclic for global sections and
the comparison of `H^n(Γ(D, −))` with `Γ(D, H^n(−))` is an isomorphism. -/
noncomputable def cohomologyIsoGlobalSectionsHigherDirectImage
    (h072Z : ∀ Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), Injective Z →
      Stacks.Cohomology.IsTotallyAcyclic Y.J
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((pushforwardModules f).obj Z)))
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hcoh : ∀ q, Stacks.RightDerivedComp.acyclic
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (((pushforwardModules f).rightDerived q).obj F))
    (n : ℕ) :
    ((pushforwardModules f ⋙
        globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).rightDerived n).obj F ≅
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (((pushforwardModules f).rightDerived n).obj F) :=
  (injectiveResolution F).isoRightDerivedObj (pushforwardModules f ⋙
      globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (Stacks.RightDerivedComp.mapCocomplex (pushforwardModules f) (injectiveResolution F))
      (acyclic_mapCocomplex_X f h072Z (injectiveResolution F))
      (fun q => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
        ((injectiveResolution F).isoRightDerivedObj (pushforwardModules f) q) (hcoh q)) n ≪≫
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapIso
      ((injectiveResolution F).isoRightDerivedObj (pushforwardModules f) n).symm

/-- **Stacks 0733, part (1).** Let `f : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed
topoi and `F` an `O_C`-module. If `R^q f_* F = 0` for `q > 0`, then
`H^p(C, F) = H^p(D, f_* F)` for all `p`, as modules over `Γ(D, O_D)` once the scalars of the left
hand side are restricted along the comparison `Γ(D, O_D) ⟶ Γ(C, O_C)` of global section rings. -/
@[stacks 0733 "part (1)", sga "4½ Arcata 2.3.5" "H^p(X,F)=H^p(Y,f_*F)"]
theorem nonempty_cohomologyIso_pushforward
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ q, 0 < q → IsZero (((pushforwardModules f).rightDerived q).obj F))
    (p : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (globalSectionsRingHom f)).obj
        ((globalModuleCohomology.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) p).obj F) ≅
      (globalModuleCohomology.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) p).obj
        ((pushforwardModules f).obj F)) :=
  have := preservesHomology_restrictScalars f
  have ⟨w⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ModuleCat.restrictScalars (globalSectionsRingHom f)) p F
  ⟨w ≪≫ ((ModuleSheafCohomology.rightDerivedIso (globalSectionsPushforwardIso f) p).app F).symm ≪≫
    cohomologyIsoOfVanishingHigherDirectImages f (isTotallyAcyclic_pushforward_injective f) F hF p⟩

omit [PreservesFiniteLimits (pushforwardModules f)] in
/-- **Stacks 0733, part (2).** Let `f : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed
topoi and `F` an `O_C`-module. If `H^p(D, R^q f_* F) = 0` for all `q` and all `p > 0`, then
`H^q(C, F) = H^0(D, R^q f_* F)` for all `q`, again after restricting the scalars of the left hand
side along the comparison of global section rings. Degree-zero cohomology on the target is the
module of global sections, by
`Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso`. -/
@[stacks 0733 "part (2)"]
theorem nonempty_cohomologyIso_globalSections_higherDirectImage
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hcoh : ∀ q p, 0 < p →
      IsZero ((globalModuleCohomology.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) p).obj
        (((pushforwardModules f).rightDerived q).obj F)))
    (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (globalSectionsRingHom f)).obj
        ((globalModuleCohomology.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) n).obj F) ≅
      (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (((pushforwardModules f).rightDerived n).obj F)) :=
  have := preservesHomology_restrictScalars f
  have ⟨w⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ModuleCat.restrictScalars (globalSectionsRingHom f)) n F
  ⟨w ≪≫ ((ModuleSheafCohomology.rightDerivedIso (globalSectionsPushforwardIso f) n).app F).symm ≪≫
    cohomologyIsoGlobalSectionsHigherDirectImage f (isTotallyAcyclic_pushforward_injective f) F
      hcoh n⟩

end Stacks.Cohomology.Leray

end
