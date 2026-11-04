module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.LongExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafInjectiveVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.EffaceabilityInput
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of a sheaf of modules on a site and of its underlying abelian sheaf

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between small sites, let `O_𝒞` and `O_𝒟` be sheaves of
rings on them and let `φ : O_𝒟 ⟶ u_* O_𝒞` be a morphism of sheaves of rings, so that there is a
direct image `f_*^mod : Mod(O_𝒞) ⥤ Mod(O_𝒟)` of sheaves of modules alongside the direct image
`f_*^ab : Ab(𝒞) ⥤ Ab(𝒟)` of abelian sheaves. This file proves that the forgetful functor to
abelian sheaves commutes with passing to higher direct images:

`R^p f_*^mod (-) ⋙ forget ≅ forget ⋙ R^p f_*^ab (-)`,

i.e. `(f_*^mod).rightDerived p ⋙ toSheaf ≅ toSheaf ⋙ (f_*^ab).rightDerived p`, naturally in the
module sheaf, normalized in degree zero by the canonical maps to the zeroth right derived
functors.

It is proved twice: for small sites, where the sheafification and injectivity hypotheses are
automatic, and in the namespace `AnySite` for sites whose objects need not be small, where they
are supplied by `Stacks.Cohomology.HigherDirectImageDelta.hasSheafify_addCommGrpCat`,
`Stacks.Cohomology.HigherDirectImageDelta.enoughInjectives_sheaf_addCommGrpCat` and
`Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits`. The small étale
site of a scheme is of the second kind, its objects forming a type one universe above its
morphisms.

## Main definitions

* `Stacks.Cohomology.SiteModulePushforward.pushforwardCompToSheafIso`: pushing modules forward and
  then forgetting *is* forgetting and then pushing abelian sheaves forward; the two functors are
  definitionally equal.
* `Stacks.Cohomology.SiteModulePushforward.toSheafDelta` and
  `Stacks.Cohomology.SiteModulePushforward.compositeDelta`: the two cohomological δ-functors
  `Mod(O_𝒞) ⥤ Ab(𝒟)` being compared, `F ↦ R^p f_*^ab (F_ab)` and `F ↦ R^p(forget ⋙ f_*^ab)(F)`.
* `Stacks.Cohomology.SiteModulePushforward.toSheafCompRightDerivedIso`: the forgetful functor
  commutes with deriving the abelian direct image,
  `forget ⋙ R^p f_*^ab ≅ R^p(forget ⋙ f_*^ab)`.
* `Stacks.Cohomology.SiteModulePushforward.rightDerivedPushforwardToSheafIso`: **the comparison
  itself**, `R^p f_*^mod ⋙ forget ≅ forget ⋙ R^p f_*^ab`.
* `Stacks.Cohomology.SiteModulePushforward.AnySite.rightDerivedPushforwardToSheafIso` and the
  δ-functors it is built from: the same comparison for sites whose objects need not be small.

## Main results

* `Stacks.Cohomology.SiteModulePushforward.isUniversal_toSheafDelta` and
  `Stacks.Cohomology.SiteModulePushforward.isUniversal_compositeDelta`: both δ-functors are
  universal, which is what makes the comparison exist and be unique.
* `Stacks.Cohomology.SiteModulePushforward.toSheafCompRightDerivedIso_zero`: in degree zero the
  comparison of the forgetful functor with derivation is the canonical identification
  `deltaZeroIso` of the two underived functors, which is what pins it down: by [Stacks, Tag 010U]
  an isomorphism of universal δ-functors is determined by its degree-zero component.
* `Stacks.Cohomology.SiteModulePushforward.AnySite.isUniversal_toSheafDelta` and the other
  statements in that namespace: the same, without smallness of the two sites.

## Implementation notes

**The two halves.** The comparison factors as

`R^p f_*^mod ⋙ forget ≅ R^p(f_*^mod ⋙ forget) = R^p(forget ⋙ f_*^ab) ≅ forget ⋙ R^p f_*^ab`.

The first isomorphism is `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, an exact
functor commuting with right derivation, applied to the exact forgetful functor
`SheafOfModules.toSheaf`; the middle equality is `pushforwardCompToSheafIso`, which holds by
`Iso.refl`. The third is the content of this file.

**Why the third isomorphism needs an argument.** Both of its sides are cohomological δ-functors
on `Mod(O_𝒞)` — the right-hand one by
`Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageDeltaFunctor` precomposed with the
exact functor `SheafOfModules.toSheaf`, the left-hand one as the right derived functors of a
single additive functor — and they agree in degree zero because both pushforwards are left exact.
Both are universal ([Stacks, Tag 010S]), so [Stacks, Tag 010U] identifies them. Universality of
the right-hand side is where the work is: by [Stacks, Tag 010T] it needs `R^(q+1) f_*^ab` to kill
the underlying abelian sheaf of an injective module sheaf, which is *not* automatic — the
underlying abelian sheaf of an injective module sheaf is not an injective abelian sheaf — and is
`Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_higherDirectImage_toSheaf_succ`, the
higher-direct-image form of the acyclicity behind [Stacks, Tag 03FD].

**Relation to the tagged statements, and why nothing here is tagged.** Three nearby tags state
something close to this, and none of them states it.

* [Stacks, Tag 03FD] is the agreement of the two *cohomologies* `H^i(𝒞, -)` and `H^i(U, -)` of an
  `O`-module and of its underlying abelian sheaf. Its statement mentions no direct image, and it
  is already carried by `ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`. Only the
  acyclicity inside its proof is reused here.
* [Stacks, Tag 01F1] part (2) is the agreement of the two higher direct images for a morphism of
  *ringed spaces*, already carried by
  `Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso`. What
  is proved here is the site-level statement of which that is the topological-space case.
* [Stacks, Tag 0D6J] part (3) is the site-level statement, but for `Rf_*` of an unbounded complex
  in the derived category of `O_𝒞`, not for the `ℕ`-indexed `R^p f_*` of a single module sheaf.
  What is below is a consequence of it, not it.

So the declarations here are deliberately untagged.

**Route.** The ringed-space proof goes through [Stacks, Tag 015M] and the derived category; the
δ-functor route used here is shorter, as it only needs the universal δ-functor of the higher
direct images.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 010S](https://stacks.math.columbia.edu/tag/010S)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SiteModulePushforward

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  (u : D ⥤ C) [u.IsContinuous J K]
  (OC : Sheaf K RingCat.{u}) (OD : Sheaf J RingCat.{u})
  (φ : OD ⟶ (u.sheafPushforwardContinuous RingCat.{u} J K).obj OC)

/-- **Pushing sheaves of modules forward and then forgetting is forgetting and then pushing
abelian sheaves forward.** The two functors are definitionally equal: the direct image of
sheaves of modules is the direct image of the underlying presheaf of modules followed by
restriction of scalars, so the underlying presheaf of abelian groups of `f_* M` is literally
`V ↦ M(u(V))`, which is the direct image of the underlying abelian sheaf of `M`. -/
@[sga "4 IV 11.2.3" "special case", sga "4 IV 13.2.3" "partial"]
def pushforwardCompToSheafIso :
    SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.toSheaf.{u} OD ≅
      SheafOfModules.toSheaf.{u} OC ⋙ u.sheafPushforwardContinuous AddCommGrpCat.{u} J K :=
  Iso.refl _

/-- **The δ-functor `F ↦ R^p f_*^ab (F_ab)`** on sheaves of `O_𝒞`-modules: the universal
δ-functor of the higher direct images of abelian sheaves, precomposed with the exact forgetful
functor to abelian sheaves. -/
@[sga "4 XII 3.1" "special case"]
def toSheafDelta : DeltaFunctor (SheafOfModules.{u} OC) (Sheaf J AddCommGrpCat.{u}) :=
  (Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageDeltaFunctor J K
    AddCommGrpCat.{u} u).precomp (SheafOfModules.toSheaf.{u} OC)

/-- The degree-`p` component of `toSheafDelta` is `forget ⋙ R^p f_*^ab`. -/
@[simp]
theorem toSheafDelta_functor (p : ℕ) :
    (toSheafDelta J K u OC).functor p = SheafOfModules.toSheaf.{u} OC ⋙
      (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived p :=
  rfl

/-- **The δ-functor `F ↦ R^p (forget ⋙ f_*^ab)(F)`** on sheaves of `O_𝒞`-modules: the right
derived functors of the single additive functor `Mod(O_𝒞) ⥤ Ab(𝒟)` sending a module sheaf to the
direct image of its underlying abelian sheaf. -/
def compositeDelta : DeltaFunctor (SheafOfModules.{u} OC) (Sheaf J AddCommGrpCat.{u}) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (SheafOfModules.toSheaf.{u} OC ⋙ u.sheafPushforwardContinuous AddCommGrpCat.{u} J K)

/-- The degree-`p` component of `compositeDelta` is `R^p(forget ⋙ f_*^ab)`. -/
@[simp]
theorem compositeDelta_functor (p : ℕ) :
    (compositeDelta J K u OC).functor p = (SheafOfModules.toSheaf.{u} OC ⋙
      u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived p :=
  rfl

/-- **`toSheafDelta` is universal** ([Stacks, Tag 010S]). By [Stacks, Tag 010T] it suffices that
`R^(q+1) f_*^ab` kill the underlying abelian sheaf of an injective sheaf of `O_𝒞`-modules, which
is the higher-direct-image form of the acyclicity behind [Stacks, Tag 03FD]. -/
theorem isUniversal_toSheafDelta : (toSheafDelta J K u OC).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun q I _ ↦
    Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_higherDirectImage_toSheaf_succ
      J K u OC I q

/-- **`compositeDelta` is universal** ([Stacks, Tag 010S]): the higher right derived functors of
any additive functor vanish on injective objects. -/
theorem isUniversal_compositeDelta : (compositeDelta J K u OC).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun q I _ ↦
    Functor.isZero_rightDerived_obj_injective_succ _ q I

/-- The two δ-functors agree in degree zero: both direct images are left exact, so both zeroth
right derived functors are canonically the underived functor `F ↦ (f_* F_ab)`. -/
def deltaZeroIso : (toSheafDelta J K u OC).functor 0 ≅ (compositeDelta J K u OC).functor 0 :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} OC)
      (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerivedZeroIsoSelf ≪≫
    (SheafOfModules.toSheaf.{u} OC ⋙
      u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerivedZeroIsoSelf.symm

/-- **The two δ-functors are isomorphic** ([Stacks, Tag 010U]): both are universal and they agree
in degree zero, and the isomorphism extending `deltaZeroIso` is unique. -/
def deltaIso : toSheafDelta J K u OC ≅ compositeDelta J K u OC :=
  haveI := isUniversal_toSheafDelta J K u OC
  haveI := isUniversal_compositeDelta J K u OC
  DeltaFunctor.IsUniversal.isoOfIso (deltaZeroIso J K u OC)

/-- **The forgetful functor to abelian sheaves commutes with deriving the abelian direct image**:
`forget ⋙ R^p f_*^ab ≅ R^p(forget ⋙ f_*^ab)`. This is the degree-`p` component of `deltaIso`. -/
def toSheafCompRightDerivedIso (p : ℕ) :
    SheafOfModules.toSheaf.{u} OC ⋙
        (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived p ≅
      (SheafOfModules.toSheaf.{u} OC ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived p :=
  CategoryTheory.DeltaFunctor.appIso (deltaIso J K u OC) p

/-- **The higher direct images of a sheaf of modules on a site and of its underlying abelian
sheaf agree.** For a continuous functor `u : 𝒟 ⥤ 𝒞` between small sites and a morphism of sheaves
of rings `φ : O_𝒟 ⟶ u_* O_𝒞`, deriving the direct image in sheaves of modules and then forgetting
the module structure agrees, naturally in the module sheaf, with forgetting first and deriving the
direct image of abelian sheaves.

This is the site-level form of [Stacks, Tag 01F1] part (2); the source states that part for a
morphism of ringed spaces. -/
@[ega "0 12.2.1" "partial"]
def rightDerivedPushforwardToSheafIso (p : ℕ) :
    (SheafOfModules.pushforward.{u} φ).rightDerived p ⋙ SheafOfModules.toSheaf.{u} OD ≅
      SheafOfModules.toSheaf.{u} OC ⋙
        (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).rightDerived p :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (SheafOfModules.pushforward.{u} φ) (SheafOfModules.toSheaf.{u} OD)
      (SheafOfModules.toSheaf.{u} OC ⋙ u.sheafPushforwardContinuous AddCommGrpCat.{u} J K)
      (pushforwardCompToSheafIso J K u OC OD φ) p ≪≫
    (toSheafCompRightDerivedIso J K u OC p).symm

/-- The comparison in degree zero is the canonical one: it intertwines the degree-zero component
of `deltaZeroIso` with the two canonical maps from the underived functors. -/
theorem toSheafCompRightDerivedIso_zero :
    toSheafCompRightDerivedIso J K u OC 0 = deltaZeroIso J K u OC := by
  have := isUniversal_toSheafDelta J K u OC
  have := isUniversal_compositeDelta J K u OC
  exact Iso.ext (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (deltaZeroIso J K u OC))

/-! ### The comparison on a site whose objects need not be small

The declarations above require `[SmallCategory 𝒞]` and `[SmallCategory 𝒟]`, which the small étale
site of a scheme does not satisfy, its objects forming a type one universe above its morphisms.
The repetition below removes that hypothesis: the two sites have objects in `Type u₁` and
morphisms in `Type v₁`, the coefficients are `AddCommGrpCat.{max u₁ v₁}`, and the sheafification
and injectivity facts that smallness supplies are the theorems
`Stacks.Cohomology.HigherDirectImageDelta.hasSheafify_addCommGrpCat`,
`Stacks.Cohomology.HigherDirectImageDelta.enoughInjectives_sheaf_addCommGrpCat` and
`Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits`, installed here as local
instances. The acyclicity input is
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`. The one
surviving hypothesis is the existence of `Ext` for abelian sheaves on the source site, which is
`Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp` but cannot be an instance, its universe
being undetermined by its type. -/

namespace AnySite

universe v₁ u₁

attribute [local instance] Stacks.Cohomology.HigherDirectImageDelta.hasSheafify_addCommGrpCat
  Stacks.Cohomology.HigherDirectImageDelta.enoughInjectives_sheaf_addCommGrpCat
  Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits

section ToSheaf

universe w ww

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  (u : D ⥤ C) [u.IsContinuous J K]
  (OC : Sheaf K RingCat.{ww}) (OD : Sheaf J RingCat.{ww})
  (φ : OD ⟶ (u.sheafPushforwardContinuous RingCat.{ww} J K).obj OC)

/-- **Pushing sheaves of modules forward and then forgetting is forgetting and then pushing
abelian sheaves forward**, on a site whose objects need not be small. The two functors are
definitionally equal, for the reason given in
`Stacks.Cohomology.SiteModulePushforward.pushforwardCompToSheafIso`. At the universe `max u₁ v₁`
this isomorphism is `pushforwardCompToSheafIso` below.

Neither the ring universe `ww` nor the module universe `w` is tied to the universes of the site:
no sheafification, injectivity or exactness input appears in the proof, which is `Iso.refl`. The
derived-functor comparisons below do need `max u₁ v₁` at both, and use
`pushforwardCompToSheafIso`; the small étale site of an algebraic space, whose objects are one
universe above its morphisms and whose structure sheaf and modules live at the lower one, needs
the free form. -/
def pushforwardCompToSheafIso' :
    SheafOfModules.pushforward.{w} φ ⋙ SheafOfModules.toSheaf.{w} OD ≅
      SheafOfModules.toSheaf.{w} OC ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  Iso.refl _

end ToSheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  (u : D ⥤ C) [u.IsContinuous J K]
  (OC : Sheaf K RingCat.{max u₁ v₁}) (OD : Sheaf J RingCat.{max u₁ v₁})
  (φ : OD ⟶ (u.sheafPushforwardContinuous RingCat.{max u₁ v₁} J K).obj OC)

/-- **Pushing sheaves of modules forward and then forgetting is forgetting and then pushing
abelian sheaves forward**, on a site whose objects need not be small. The two functors are
definitionally equal, for the reason given in
`Stacks.Cohomology.SiteModulePushforward.pushforwardCompToSheafIso`. -/
def pushforwardCompToSheafIso :
    SheafOfModules.pushforward.{max u₁ v₁} φ ⋙ SheafOfModules.toSheaf.{max u₁ v₁} OD ≅
      SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K :=
  Iso.refl _

/-- **The δ-functor `F ↦ R^p f_*^ab (F_ab)`** on sheaves of `O_𝒞`-modules, on a site whose objects
need not be small: the universal δ-functor of the higher direct images of abelian sheaves,
precomposed with the exact forgetful functor to abelian sheaves. -/
@[sga "4 XII 3.1" "special case"]
def toSheafDelta : DeltaFunctor (SheafOfModules.{max u₁ v₁} OC)
    (Sheaf J AddCommGrpCat.{max u₁ v₁}) :=
  (Stacks.Cohomology.HigherDirectImageDelta.higherDirectImageDeltaFunctor J K
    AddCommGrpCat.{max u₁ v₁} u).precomp (SheafOfModules.toSheaf.{max u₁ v₁} OC)

/-- The degree-`p` component of `toSheafDelta` is `forget ⋙ R^p f_*^ab`. -/
@[simp]
theorem toSheafDelta_functor (p : ℕ) :
    (toSheafDelta J K u OC).functor p = SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerived p :=
  rfl

/-- **The δ-functor `F ↦ R^p (forget ⋙ f_*^ab)(F)`** on sheaves of `O_𝒞`-modules, on a site whose
objects need not be small: the right derived functors of the single additive functor sending a
module sheaf to the direct image of its underlying abelian sheaf. -/
def compositeDelta : DeltaFunctor (SheafOfModules.{max u₁ v₁} OC)
    (Sheaf J AddCommGrpCat.{max u₁ v₁}) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
      u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K)

/-- The degree-`p` component of `compositeDelta` is `R^p(forget ⋙ f_*^ab)`. -/
@[simp]
theorem compositeDelta_functor (p : ℕ) :
    (compositeDelta J K u OC).functor p = (SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
      u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerived p :=
  rfl

variable [HasExt.{max u₁ v₁} (Sheaf K AddCommGrpCat.{max u₁ v₁})]

/-- **`toSheafDelta` is universal** ([Stacks, Tag 010S]). By [Stacks, Tag 010T] it suffices that
`R^(q+1) f_*^ab` kill the underlying abelian sheaf of an injective sheaf of `O_𝒞`-modules, which
is `Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`. -/
theorem isUniversal_toSheafDelta : (toSheafDelta J K u OC).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun q I _ ↦
    Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{v₁}
      J K u OC I q

omit [HasExt.{max u₁ v₁} (Sheaf K AddCommGrpCat.{max u₁ v₁})] in
/-- **`compositeDelta` is universal** ([Stacks, Tag 010S]): the higher right derived functors of
any additive functor vanish on injective objects. -/
theorem isUniversal_compositeDelta : (compositeDelta J K u OC).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun q I _ ↦
    Functor.isZero_rightDerived_obj_injective_succ _ q I

omit [HasExt.{max u₁ v₁} (Sheaf K AddCommGrpCat.{max u₁ v₁})] in
/-- The two δ-functors agree in degree zero: both direct images are left exact, so both zeroth
right derived functors are canonically the underived functor `F ↦ (f_* F_ab)`. -/
def deltaZeroIso : (toSheafDelta J K u OC).functor 0 ≅ (compositeDelta J K u OC).functor 0 :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{max u₁ v₁} OC)
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerivedZeroIsoSelf ≪≫
    (SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
      u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerivedZeroIsoSelf.symm

/-- **The two δ-functors are isomorphic** ([Stacks, Tag 010U]): both are universal and they agree
in degree zero, and the isomorphism extending `deltaZeroIso` is unique. -/
def deltaIso : toSheafDelta J K u OC ≅ compositeDelta J K u OC :=
  have := isUniversal_toSheafDelta J K u OC
  have := isUniversal_compositeDelta J K u OC
  DeltaFunctor.IsUniversal.isoOfIso (deltaZeroIso J K u OC)

/-- **The forgetful functor to abelian sheaves commutes with deriving the abelian direct image**,
on a site whose objects need not be small: `forget ⋙ R^p f_*^ab ≅ R^p(forget ⋙ f_*^ab)`. -/
def toSheafCompRightDerivedIso (p : ℕ) :
    SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
        (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerived p ≅
      (SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerived p :=
  CategoryTheory.DeltaFunctor.appIso (deltaIso J K u OC) p

/-- **The higher direct images of a sheaf of modules and of its underlying abelian sheaf agree**,
on a site whose objects need not be small. Deriving the direct image in sheaves of modules and
then forgetting the module structure agrees, naturally in the module sheaf, with forgetting first
and deriving the direct image of abelian sheaves. -/
def rightDerivedPushforwardToSheafIso (p : ℕ) :
    (SheafOfModules.pushforward.{max u₁ v₁} φ).rightDerived p ⋙
        SheafOfModules.toSheaf.{max u₁ v₁} OD ≅
      SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
        (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K).rightDerived p :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (SheafOfModules.pushforward.{max u₁ v₁} φ) (SheafOfModules.toSheaf.{max u₁ v₁} OD)
      (SheafOfModules.toSheaf.{max u₁ v₁} OC ⋙
        u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁} J K)
      (pushforwardCompToSheafIso J K u OC OD φ) p ≪≫
    (toSheafCompRightDerivedIso J K u OC p).symm

/-- The comparison in degree zero is the canonical one: it intertwines the degree-zero component
of `deltaZeroIso` with the two canonical maps from the underived functors. -/
theorem toSheafCompRightDerivedIso_zero :
    toSheafCompRightDerivedIso J K u OC 0 = deltaZeroIso J K u OC := by
  have := isUniversal_toSheafDelta J K u OC
  have := isUniversal_compositeDelta J K u OC
  exact Iso.ext (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (deltaZeroIso J K u OC))

end AnySite

end Stacks.Cohomology.SiteModulePushforward

end
