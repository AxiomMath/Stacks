module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective

/-!
# The direct image of an injective module is totally acyclic, over a site whose objects are large

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and let `I` be an injective
sheaf of `𝒪_C`-modules.  **Stacks 072Z** says that the sheaf of abelian groups underlying the
direct image `f_*I` is totally acyclic: its cohomology over every sheaf of sets on `D` vanishes
in positive degrees.  `Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective` is
that statement for a *source* ringed topos whose three universes are equal.  This file removes
that restriction: the source site's objects may lie above its morphisms and its sheaves, as they
do on the small étale site of an algebraic space, whose objects are the étale charts.

Nothing in the mathematics changes.  The one step that forced the equality of universes was
`ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree`, and the restriction there is an
artefact of how it was written; see the implementation notes.

## Main results

* `Stacks.Cohomology.ext_eq_zero_of_isTorsionFree_largeSite`: `Ext` out of a sectionwise
  torsion-free abelian sheaf into the abelian sheaf underlying an injective module vanishes in
  positive degree, on a site whose objects need not lie at the universe of its sheaves.
* `Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective_largeSource`:
  **Stacks 072Z** with the source ringed topos's three universes unconstrained.
* `Stacks.Cohomology.isZero_sheafH'_pushforwardModules_of_injective`: the same conclusion read
  through `CategoryTheory.Sheaf.H'`, the `Ext`-style sheaf cohomology over an object of the
  target site, which is the shape the module-valued vanishing results of this development
  consume.

## Implementation notes

*Why the universes were tied together, and why they need not be.*
`ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree` is stated in the `SiteTensor` section of
`StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparison.lean`, whose
coefficient universe is `max u r m` for a site with objects in `Type u` and a sheaf of rings
with sections in `Type r`.  The `max u` is what rules out a module universe below the universe
of the objects.  It is there for the *other* declarations of that section —
`tensorSheafHomIso` and `globalSectionsRepresentation`, where `preadditiveCoyoneda` takes values
in the hom-groups of `Sheaf J Ab.{w}`, which lie in `Type (max u w)`.  The `Ext`-vanishing
itself passes through none of that: its ingredients are the dévissage
`ModuleSheafCohomology.ext_eq_zero_of_resolving`, the torsion-freeness lemmas
`isTorsionFree_of_mono` and `exists_isTorsionFree_epi`, and the extension-of-scalars adjunction
`tensorPresheaf`/`tensorPresheafLift`/`tensorPresheafUnit`, and every one of those is stated with
the site's object universe free.  So the vanishing is reproved below at coefficients
`max r m`, with the object universe unconstrained, by the same proof.  The universe of the
`Ext`-groups is a free variable as well, where before it was pinned to the site's one universe.

*What is reused and what is restated.*  Five of the steps of Stacks 072Z between the
torsion-freeness lemmas and the conclusion — `exists_extension_of_ext_one_eq_zero`,
`isTorsionFree_abelianInverseImage`, `isTorsionFree_freeAbelianSheaf`,
`naturalTransformationAddHom` and `abelianSheafNatTransOfUnderlying` — state their own universes
and so already hold at the generality wanted here; they are taken from
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/PushforwardOfAnInjective.lean`, the
private ones by `import all`, rather than reproved.  The sixth, the comparison
`pushforwardModulesAbelianIso` of the two direct images, is stated there for a source whose
three universes are equal, and is restated below as `pushforwardModulesAbelianIsoLargeSource`
with all six universes free.  What remains here is what genuinely changes:
the two steps between `tensorPresheaf` and the vanishing
(`mono_tensorPresheafMap_of_shortExact` and `exists_extension_of_isTorsionFree`), and the one
declaration that the source topos's universes enter
(`ext_eq_zero_of_abelianPushforward`).
Apart from universe ascriptions the proofs are the originals,
with one exception: `exists_extension_of_isTorsionFree` builds its extension as a chain of
`congrArg`s instead of by `rw`.  Its original rewrites the composite
`tensorPresheafUnit ≫ (PresheafOfModules.toPresheaf R).map g`, whose type is correct only after
`PresheafOfModules.toPresheaf` and `SheafOfModules.toSheaf` are unfolded, so `rw` cannot
typecheck the motive it abstracts; the chain below never abstracts one.

*The shape of `Sheaf.H'`.*  `CategoryTheory.Sheaf.H'` is formed at the morphism universe of the
site — its coefficients are `AddCommGrpCat.{v}` for a `Category.{v}`-site — so the last section
below asks the target ringed topos for sheaves at that universe.  The source keeps all three of
its universes free.  Passing from total acyclicity to `Sheaf.H'` is instantiating acyclicity at
the sheafification of `yoneda.obj V` and then moving across
`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`, which inverts the unit of
sheafification: the free abelian sheaf of a presheaf of sets only depends on its sheafification.

## References

* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 21.13.1 (Tag 072Y)](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Lemma 50.6.3 (Tag 08EX)](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Stacks.Topos.AbelianPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules)
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace Stacks.Cohomology

universe m r u v x w w' v' u'

/-! ### `Ext`-vanishing against a torsion-free sheaf, over a site with large objects -/

section Tensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max r m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max r m})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max r m})]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{max r m})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max r m})] in
/-- Tensoring a short exact sequence with sectionwise torsion-free quotient preserves the
inclusion on the underlying presheaves.  This is
`ModuleSheafCohomology.Univ.mono_tensorPresheafMap_of_shortExact`, which is private to its module,
with the site's object universe unconstrained. -/
private lemma mono_tensorPresheafMap_of_shortExact
    (R : Cᵒᵖ ⥤ RingCat.{r}) (S : ShortComplex (Sheaf J AddCommGrpCat.{max r m}))
    (hS : S.ShortExact) (hP : ∀ Z, Module.IsTorsionFree ℤ (S.X₃.obj.obj Z)) :
    Mono (ModuleSheafCohomology.Univ.tensorPresheafMap.{m} R S.f.hom) := by
  have := hS.mono_f
  apply PresheafOfModules.mono_of_injective
  intro Z
  have := hP Z
  let E := sheafToPresheaf J AddCommGrpCat.{max r m} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max r m}).obj Z
  exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
    (S.f.hom.app Z).hom.toIntLinearMap (S.g.hom.app Z).hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp
      ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
        inferInstance S hS).1) (R.obj Z)

omit [HasExt.{x} (Sheaf J AddCommGrpCat.{max r m})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max r m})] in
/-- Maps to the underlying abelian sheaf of an injective module sheaf extend across short exact
sequences with sectionwise torsion-free quotient. -/
private lemma exists_extension_of_isTorsionFree
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max r m} R) [Injective I]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max r m})) (hS : S.ShortExact)
    (hP : ∀ Z, Module.IsTorsionFree ℤ (S.X₃.obj.obj Z))
    (f : S.X₁ ⟶ (SheafOfModules.toSheaf R).obj I) :
    ∃ g : S.X₂ ⟶ (SheafOfModules.toSheaf R).obj I, S.f ≫ g = f := by
  have : Injective I.val := ModuleSheafCohomology.Univ.injective_forget_obj R I
  have := mono_tensorPresheafMap_of_shortExact.{m} J R.obj S hS hP
  obtain ⟨φ, hφ⟩ : ∃ φ, ModuleSheafCohomology.Univ.tensorPresheafMap R.obj S.f.hom ≫ φ =
      ModuleSheafCohomology.Univ.tensorPresheafLift R.obj f.hom :=
    ⟨_, Injective.comp_factorThru _ _⟩
  refine ⟨⟨ModuleSheafCohomology.Univ.tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map φ⟩, Sheaf.hom_ext ?_⟩
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (PresheafOfModules.toPresheaf R.obj).map φ)
      (ModuleSheafCohomology.Univ.tensorPresheafUnit_naturality R.obj S.f.hom)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (ModuleSheafCohomology.Univ.tensorPresheafUnit R.obj S.X₁.obj ≫ ·) ?_).trans
          (ModuleSheafCohomology.Univ.tensorPresheafUnit_comp_lift R.obj f.hom))))
  exact ((PresheafOfModules.toPresheaf R.obj).map_comp _ _).symm.trans
    (congrArg (PresheafOfModules.toPresheaf R.obj).map hφ)

/-- **The underlying abelian sheaf of an injective module sheaf is `Ext`-acyclic against every
sectionwise torsion-free sheaf**, on a site whose objects need not lie at the universe of its
sheaves.

This is `ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree` with the universe `u` of the
objects of the site removed from the universe of the coefficients, and with the universe of the
`Ext`-groups a free variable.  The proof is the original: the dévissage of
`ModuleSheafCohomology.ext_eq_zero_of_resolving` over the sectionwise torsion-free sheaves
reduces the claim to degree one, where it is the extension problem solved by
`exists_extension_of_isTorsionFree`. -/
theorem ext_eq_zero_of_isTorsionFree_largeSite
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max r m} R) [Injective I]
    (T : Sheaf J AddCommGrpCat.{max r m})
    (hT : ∀ Z, Module.IsTorsionFree ℤ (T.obj.obj Z))
    (n : ℕ) (e : Ext.{x} T ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_resolving
    (fun F : Sheaf J AddCommGrpCat.{max r m} => ∀ Z, Module.IsTorsionFree ℤ (F.obj.obj Z))
    (fun f _ hG => ModuleSheafCohomology.isTorsionFree_of_mono J f hG)
    (ModuleSheafCohomology.exists_isTorsionFree_epi J) ((SheafOfModules.toSheaf R).obj I)
    (ModuleSheafCohomology.ext_one_eq_zero_of_extension _ _
      (exists_extension_of_isTorsionFree.{m} J R I)) n T hT e

end Tensor

/-! ### Stacks 072Z with the source's universes unconstrained -/

section Acyclicity

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

variable [HasSheafify Y.J AddCommGrpCat.{w'}] [HasExt.{x} (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{x} (Sheaf X.J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  (I : SheafOfModules.{w} (ringSheaf X.O)) [hI : Injective I]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- `Ext` out of a sectionwise torsion-free abelian sheaf into the direct image of the abelian
sheaf underlying an injective module vanishes in positive degree.

The source ringed topos is ascribed `RingedTopos.{v, u, w}` in the statement: that is the whole
difference from `Stacks.Cohomology.ext_eq_zero_of_abelianPushforward` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/PushforwardOfAnInjective.lean`, which
reads the same but is stated for a source whose three universes are equal.  Writing the
universes here rather than leaving them to the ambient `variable` keeps the two statements
distinguishable where a reader sees them.

The dévissage of `ModuleSheafCohomology.ext_eq_zero_of_resolving` over the sectionwise
torsion-free sheaves on the target reduces this to degree one, where the adjunction
`f⁻¹ ⊣ f_*` of abelian sheaves carries the extension problem to the source topos; there the
inverse image, being exact, has produced another short exact sequence with torsion-free third
term, and `ext_eq_zero_of_isTorsionFree_largeSite` splits it. -/
private lemma ext_eq_zero_of_abelianPushforward (T : Sheaf Y.J AddCommGrpCat.{w'})
    (hT : ∀ U, Module.IsTorsionFree ℤ (T.obj.obj U)) (n : ℕ)
    (a : Ext.{x} T ((abelianPushforward (X : RingedTopos.{v, u, w}).J f.toToposHom).obj
      ((SheafOfModules.toSheaf (ringSheaf X.O)).obj I)) (n + 1)) : a = 0 := by
  let adj := abelianInverseImageAdjPushforward X.J f.toToposHom
  refine ModuleSheafCohomology.ext_eq_zero_of_resolving
    (fun G : Sheaf Y.J AddCommGrpCat.{w'} => ∀ U, Module.IsTorsionFree ℤ (G.obj.obj U))
    (fun m _ hH => ModuleSheafCohomology.isTorsionFree_of_mono Y.J m hH)
    (ModuleSheafCohomology.exists_isTorsionFree_epi Y.J) _
    (ModuleSheafCohomology.ext_one_eq_zero_of_extension _ _ fun S hS hP m => ?_) n T hT a
  obtain ⟨g, hg⟩ := exists_extension_of_ext_one_eq_zero
    (ShortComplex.ShortExact.map_of_exact hS (Sites.abelianInverseImage f.toToposHom)) _
    (fun e => ext_eq_zero_of_isTorsionFree_largeSite.{w} X.J _ I _
      (isTorsionFree_abelianInverseImage f.toToposHom S.X₃ hP) 0 e)
    ((adj.homEquiv _ _).symm m)
  have hg' : (Sites.abelianInverseImage f.toToposHom).map S.f ≫ g =
    (adj.homEquiv _ _).symm m := hg
  exact ⟨adj.homEquiv _ _ g, by
    rw [← adj.homEquiv_naturality_left, hg', Equiv.apply_symm_apply]⟩

/-- The direct image of sheaves of modules along a morphism of ringed topoi, followed by
forgetting the module structure, is forgetting the module structure followed by the direct image
of abelian sheaves: both have the direct image of the underlying sheaf of sets underlying them,
on the nose.  This is `Stacks.Cohomology.pushforwardModulesAbelianIso` with the source ringed
topos's object, morphism and section universes unrelated. -/
def pushforwardModulesAbelianIsoLargeSource :
    pushforwardModules f ⋙ SheafOfModules.toSheaf (ringSheaf Y.O) ≅
      SheafOfModules.toSheaf (ringSheaf (X : RingedTopos.{v, u, w}).O) ⋙
        abelianPushforward X.J f.toToposHom := by
  have : HasBinaryBiproducts (SheafOfModules.{w} (ringSheaf X.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : HasZeroObject (Sheaf Y.J AddCommGrpCat.{w'}) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf X.J AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have : (Sites.abelianInverseImage f.toToposHom).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : (Sites.abelianInverseImage f.toToposHom).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (abelianPushforward X.J f.toToposHom).Additive :=
    (abelianInverseImageAdjPushforward X.J f.toToposHom).right_adjoint_additive
  exact abelianSheafNatIsoOfUnderlying Y.J _ _ (Iso.refl _)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **Stacks 072Z with the source ringed topos's universes unconstrained.**  The sheaf of
abelian groups underlying the direct image of an injective sheaf of modules along a morphism of
ringed topoi is totally acyclic: its cohomology over every sheaf of sets on the target vanishes
in positive degrees.

`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective` is this statement for a
source whose three universes are equal.  Here the source site's objects, morphisms and sections
lie at three unrelated universes, which is the seating of the small étale site of an algebraic
space. -/
@[stacks 072Z "the source ringed topos's object, morphism and section universes unrelated"]
theorem isTotallyAcyclic_pushforwardModules_of_injective_largeSource :
    Stacks.Cohomology.IsTotallyAcyclic Y.J
      ((SheafOfModules.toSheaf (ringSheaf Y.O)).obj
        ((pushforwardModules f).obj I)) := by
  intro K p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact subsingleton_ext_of_iso_right ((pushforwardModulesAbelianIsoLargeSource f).app I) (n + 1)
    (subsingleton_of_forall_eq 0 fun a ↦
      ext_eq_zero_of_abelianPushforward f I _ (isTorsionFree_freeAbelianSheaf Y.J K) n a)

end Acyclicity


section SheafCohomology

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{w', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasExt.{x} (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{x} (Sheaf X.J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  [HasSheafify Y.J (Type w')]
  (I : SheafOfModules.{w} (ringSheaf X.O)) [hI : Injective I]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **Stacks 072Z read through `CategoryTheory.Sheaf.H'`.**  The `Ext`-style sheaf cohomology of
the abelian sheaf underlying the direct image of an injective module vanishes over every object
of the target site, in every positive degree.

Total acyclicity is vanishing over every sheaf of *sets*; this is its value at the
sheafification of `yoneda.obj V`, moved to the free abelian sheaf of `yoneda.obj V` itself by
`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`.  The target ringed topos has its
sheaves at the morphism universe of its site, because that is where `Sheaf.H'` is formed. -/
theorem isZero_sheafH'_pushforwardModules_of_injective (V : Y.C) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{x, w', u'} ((SheafOfModules.toSheaf (ringSheaf Y.O)).obj
      ((pushforwardModules f).obj I)) p V) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have := Presheaf.isIso_freeAbelianSheaf_map_of_W Y.J
    (toSheafify Y.J (yoneda.obj V)) (Y.J.W_toSheafify _)
  exact Stacks.Cohomology.subsingleton_ext_of_iso
    (asIso ((Presheaf.freeAbelianSheaf Y.J).map (toSheafify Y.J (yoneda.obj V)))) p
    (isTotallyAcyclic_pushforwardModules_of_injective_largeSource f I
      ((presheafToSheaf Y.J (Type w')).obj (yoneda.obj V)) p hp)

end SheafCohomology

end Stacks.Cohomology

end
