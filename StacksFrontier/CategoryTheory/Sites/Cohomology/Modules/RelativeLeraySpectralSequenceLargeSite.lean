module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardLargeSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RelativeLeraySpectralSequence
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage

/-!
# The relative Leray spectral sequence, over ringed topoi whose universes are unrelated

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi and let `F^•` be a bounded below complex of `O_C`-modules.  **Stacks 0734** gives a
spectral sequence

`E_2^{p,q} = R^p g_*(R^q f_*(F^•))  ⟹  R^{p+q}(g ∘ f)_*(F^•)`.

`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence` is that statement for three ringed
topoi whose object, morphism and section universes are all equal.  This file removes that
restriction: each of the three sites may have its objects above its morphisms and its sheaves, as
they are on the small étale site of an algebraic space, whose objects are the étale charts.

Nothing in the mathematics changes.  The equality of universes was forced by exactly one step,
and the restriction there is an artefact of how it was written; see the implementation notes.

## Main results

* `Stacks.Cohomology.isTotallyAcyclic_of_injective_largeSite`: an injective sheaf of modules has
  totally acyclic underlying abelian sheaf, on a site whose objects need not lie at the universe
  of its sheaves.
* `Stacks.Cohomology.splitEpi_moduleSheafFunctor_largeSite`: a short exact sequence of sheaves of
  modules with totally acyclic kernel splits on the underlying sheaves of sets, over such a site.
* `Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic_largeSite`: **part (4)
  of Stacks 0731** with the universes of both ringed topoi unconstrained.
* `Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite`:
  the direct image along `f` of an injective `O_C`-module is right acyclic for the direct image
  along `g`, at unrelated universes.
* `Stacks.Cohomology.Leray.derivedPushforwardCompIso_largeSite`: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` as
  an isomorphism of functors `D⁺(Mod(O_C)) ⥤ D⁺(Mod(O_E))`.
* `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_largeSite`: **Stacks 0734** with
  the three ringed topoi's object, morphism and section universes unrelated.

## Functoriality in `F` is not covered

Stacks 0734 ends by asserting that its spectral sequence is *functorial in `F`*.  **That clause
is absent here, and the tag below carries a qualifier recording it**, exactly as it does on
`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`.  What the statement gives is the
existence of the spectral sequence, the identification of its second page and its convergence,
for each object of `D⁺(Mod(O_C))` separately.

The obstruction is in the engine, and freeing the universes does not touch it: the Grothendieck
spectral sequence of a composition,
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]), is an existence statement whose proof chooses a bounded below complex
representing `Rf_*(F^•)` and a Cartan–Eilenberg resolution of it, neither choice being natural in
`F^•`.  What *is* natural is the identification of the abutment, and that is supplied by
`derivedPushforwardCompIso_largeSite` below, an isomorphism of *functors* on `D⁺(Mod(O_C))`.

## Implementation notes

*Which step tied the universes together, and why it need not.*  The chain behind
`exists_relativeLeraySpectralSequence` has three links: the relative spectral sequence with its
acyclicity input assumed
(`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_of_rightAcyclic`), part (4) of
Stacks 0731 (`Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic`), and
Stacks 072Z (`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`).  Only one
place in the whole chain needs the universes equal, and it is the same place that needed them for
Stacks 072Z: `ModuleSheafCohomology.Univ.ext_eq_zero_of_isTorsionFree`, whose coefficient universe
is `max u r m` for a site with objects in `Type u`, and which enters here through
`Stacks.Cohomology.isTotallyAcyclic_of_injective` — the statement that an injective module is
totally acyclic, which is the first condition of the adapted-class criterion of Stacks 05T8 that
part (4) runs.  The `max u` is there for the *other* declarations of that `Ext`-vanishing's
section, and
`Stacks.Cohomology.ext_eq_zero_of_isTorsionFree_largeSite` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardLargeSource` already
reproves the vanishing without it.  Everything else in the chain is universe-polymorphic where it
stands: `Stacks.Cohomology.IsTotallyAcyclic`,
`CategoryTheory.Presheaf.freeAbelianSheafAdj`, `SheafOfModules.instAbelian`,
`Stacks.Sheaves.RingedToposModules.pushforwardModules` with its adjunction and its additivity,
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`,
`CategoryTheory.Functor.le_rightAcyclic` and
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`.  So the three
`{u, u, u}` seatings of the chain are inherited bookkeeping, not mathematics.

*What is copied.*  Of the four steps of part (4) of Stacks 0731, two
(`subsingleton_ext_of_shortExact`, `exists_lift_of_shortExact`) are private to
`StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage` and are
reached by `import all`; the other two are stated only at equal universes and are reproved
below.  Apart from universe ascriptions the proofs are the originals.  The same holds for the
body of `exists_relativeLeraySpectralSequence_of_rightAcyclic`, whose filtration bookkeeping is
repeated verbatim at the freed seating.

*Enough injectives.*  On a small site with its sheaves at the site's own universe, enough
injective sheaves of modules and injective resolutions of abelian sheaves come for free from
Grothendieck abelianness, and the statements of part (4) in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage` use that.
At unrelated universes they are instance arguments here, which is what
`exists_relativeLeraySpectralSequence` already does for the sheaves of modules; the small étale
site of an algebraic space supplies all of them.

## References

* [Stacks Project, Lemma 21.14.7 (Tag 0734)](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 13.15.6 (Tag 05T8)](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Lemma 21.14.1 (Tag 0720)](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace Stacks.Cohomology

universe x w w' w'' v u v' u' v'' u'' t t' t''

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance 5000] SheafOfModules.instAbelian

/-! ### The class of totally acyclic modules, over a site with large objects -/

section Devissage

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{x} (Sheaf J AddCommGrpCat.{w})]

/-- Total acyclicity passes from the kernel and the middle term of a short exact sequence of
abelian sheaves to its quotient, on a site whose objects need not lie at the universe of its
sheaves.  This is `Stacks.Cohomology.isTotallyAcyclic_of_shortExact` with the site's object and
morphism universes unconstrained. -/
theorem isTotallyAcyclic_of_shortExact_largeSite
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic.{x} J S.X₁) (h₂ : IsTotallyAcyclic.{x} J S.X₂) :
    IsTotallyAcyclic.{x} J S.X₃ := fun K p hp ↦
  subsingleton_ext_of_shortExact _ hS p (h₁ K (p + 1) (by lia)) (h₂ K p hp)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]

/-- **An injective sheaf of modules has totally acyclic underlying abelian sheaf**, on a site
whose objects need not lie at the universe of its sheaves.  Cohomology over a sheaf of sets is
`Ext` out of the free abelian sheaf it generates, that sheaf is sectionwise torsion free, and
`Ext` out of a sectionwise torsion-free abelian sheaf into the abelian sheaf underlying an
injective module vanishes in positive degree.

This is `Stacks.Cohomology.isTotallyAcyclic_of_injective` with the site's object and morphism
universes removed from the universe of its sheaves.  The vanishing it rests on is
`Stacks.Cohomology.ext_eq_zero_of_isTorsionFree_largeSite`, which already has the universe of
the `Ext`-groups free, so the change of universe that the original performs with
`CategoryTheory.Abelian.Ext.chgUniv` is not needed. -/
theorem isTotallyAcyclic_of_injective_largeSite
    (R : Sheaf J RingCat.{w}) (I : SheafOfModules.{w} R) [Injective I] :
    IsTotallyAcyclic.{x} J ((SheafOfModules.toSheaf R).obj I) := by
  intro K p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hTF : ∀ U, Module.IsTorsionFree ℤ
      (((Presheaf.freeAbelianSheaf J).obj K.obj).obj.obj U) := fun U ↦
    ModuleSheafCohomology.isTorsionFree_sheafify J (K.obj ⋙ AddCommGrpCat.free) (fun V ↦ by
      change Module.IsTorsionFree ℤ (FreeAbelianGroup (K.obj.obj V))
      exact Module.Flat.isTorsionFree) U
  have h := ext_eq_zero_of_isTorsionFree_largeSite.{w} J R I _ hTF n
  exact ⟨fun a b ↦ (h a).trans (h b).symm⟩

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- **A short exact sequence of sheaves of modules whose kernel has totally acyclic underlying
abelian sheaf splits after passing to the underlying sheaves of sets**, on a site whose objects
need not lie at the universe of its sheaves.  A splitting is a map from the underlying sheaf of
sets of the third term to that of the second; by the free abelian sheaf adjunction such maps are
maps of abelian sheaves out of the free abelian sheaf generated by it, and total acyclicity of
the kernel makes `Ext^1` out of that free abelian sheaf vanish, so the identity lifts across the
epimorphism.

This is `Stacks.Cohomology.splitEpi_moduleSheafFunctor` with the site's object and morphism
universes unconstrained. -/
lemma splitEpi_moduleSheafFunctor_largeSite (R : Sheaf J RingCat.{w})
    (S : ShortComplex (SheafOfModules.{w} R)) (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic.{x} J ((SheafOfModules.toSheaf R).obj S.X₁)) :
    Nonempty (SplitEpi ((Sheaf.moduleSheafFunctor R).map S.g)) := by
  let toAb := SheafOfModules.toSheaf.{w} R
  let forgetAb := sheafCompose J (forget AddCommGrpCat.{w})
  let K : Sheaf J (Type w) := forgetAb.obj (toAb.obj S.X₃)
  let adj := Presheaf.freeAbelianSheafAdj.{w} J
  let a : (Presheaf.freeAbelianSheaf J).obj K.obj ⟶ toAb.obj S.X₃ :=
    (adj.homEquiv K.obj (toAb.obj S.X₃)).symm (𝟙 K.obj)
  obtain ⟨b, hb⟩ := exists_lift_of_shortExact
    ((Presheaf.freeAbelianSheaf J).obj K.obj) (hS.map_of_exact toAb) (h₁ K 1 le_rfl) a
  refine ⟨⟨⟨adj.homEquiv K.obj (toAb.obj S.X₂) b⟩, ?_⟩⟩
  apply Sheaf.hom_ext
  change adj.homEquiv K.obj (toAb.obj S.X₂) b ≫
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ Presheaf.forgetAbelian).map (toAb.map S.g) = 𝟙 K.obj
  rw [← adj.homEquiv_naturality_right]
  change adj.homEquiv K.obj (toAb.obj S.X₃) (b ≫ (S.map toAb).g) = 𝟙 K.obj
  rw [hb]
  exact (adj.homEquiv K.obj (toAb.obj S.X₃)).apply_symm_apply (𝟙 K.obj)

end Devissage

/-! ### Part (4) of Stacks 0731 with both ringed topoi's universes unconstrained -/

section DirectImage

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasExt.{x} (Sheaf X.J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf X.O))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf X.O))] in
/-- The direct image of a short exact sequence of sheaves of modules whose kernel has totally
acyclic underlying abelian sheaf is short exact.  Left exactness of the direct image is the
adjunction `f^* ⊣ f_*` of Stacks 03D7, and the quotient map stays epimorphic because the
sequence splits on the underlying sheaves of sets, where every functor preserves split
epimorphisms.  This is the private `shortExact_map_pushforwardModules` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage`, with both
ringed topoi's universes unconstrained. -/
private lemma shortExact_map_pushforwardModules_largeSite
    (S : ShortComplex (SheafOfModules.{w} (ringSheaf X.O))) (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic.{x} X.J
      ((SheafOfModules.toSheaf (ringSheaf X.O)).obj S.X₁)) :
    (S.map (pushforwardModules f)).ShortExact := by
  have : PreservesLimitsOfSize.{0, 0} (pushforwardModules f) :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      f).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (pushforwardModules f) := inferInstance
  obtain ⟨hexact, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (pushforwardModules f)).mp inferInstance S hS
  obtain ⟨hsplit⟩ :=
    splitEpi_moduleSheafFunctor_largeSite X.J (ringSheaf X.O) S hS h₁
  have hepi : Epi (f.toToposHom.pushforward.map
      ((Sheaf.moduleSheafFunctor (ringSheaf X.O)).map S.g)) :=
    (hsplit.map f.toToposHom.pushforward).epi
  have hepi' : Epi ((Sheaf.moduleSheafFunctor (ringSheaf Y.O)).map
      ((pushforwardModules f).map S.g)) := hepi
  refine ShortComplex.ShortExact.mk' hexact hmono ⟨fun {P} a b hab ↦ ?_⟩
  refine hom_ext_moduleSheafFunctor ((cancel_epi
    ((Sheaf.moduleSheafFunctor (ringSheaf Y.O)).map
      ((pushforwardModules f).map S.g))).mp ?_)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ hab

variable [HasDerivedCategory.{t} (SheafOfModules.{w} (ringSheaf X.O))]
  [HasDerivedCategory.{t'} (SheafOfModules.{w'} (ringSheaf Y.O))]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasExt.{x} (Sheaf X.J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  [HasDerivedCategory.{t} (SheafOfModules.{w} (ringSheaf X.O))] in
/-- **The direct image of modules has a right derived functor**, over ringed topoi whose
universes are unrelated.  Sheaves of modules on the source have enough injectives, so every
object of `K⁺` of them has a pointwise right derived functor for any functor out of it; speaking
of right acyclicity for `f_*` therefore needs no existence hypothesis beyond that.

The functor is passed to `HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso`
explicitly: left to unification, the same instance exhausts the heartbeat budget. -/
theorem hasRightDerivedFunctor_pushforwardModules_largeSite :
    ((pushforwardModules f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} (ringSheaf X.O))) :=
  have := HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
    ((pushforwardModules f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
  inferInstance

attribute [local instance] hasRightDerivedFunctor_pushforwardModules_largeSite

/-- **Stacks 0731, part (4), with both ringed topoi's universes unconstrained.**  A sheaf of
modules whose underlying abelian sheaf is totally acyclic is right acyclic for the direct image
along a morphism of ringed topoi.

`Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic` is this statement for
two ringed topoi whose three universes are equal.  Here each site's objects, morphisms and
sections lie at three unrelated universes, which is the seating of the small étale site of an
algebraic space.  The proof is the original one: the totally acyclic modules form a class
adapted to `f_*` in the sense of Stacks 05T8, and Stacks 05T8 says that every object of an
adapted class is acyclic. -/
@[stacks 0731 "part (4): direct images, with the two ringed topoi's object, morphism and section
  universes unrelated"]
theorem rightAcyclic_pushforwardModules_of_isTotallyAcyclic_largeSite
    (N : SheafOfModules.{w} (ringSheaf X.O))
    (hN : IsTotallyAcyclic.{x} X.J
      ((SheafOfModules.toSheaf (ringSheaf X.O)).obj N)) :
    (pushforwardModules f).rightAcyclic N :=
  Functor.le_rightAcyclic (pushforwardModules f)
    (fun M ↦ IsTotallyAcyclic.{x} X.J
      ((SheafOfModules.toSheaf (ringSheaf X.O)).obj M))
    (fun M ↦ ⟨Injective.under M,
      isTotallyAcyclic_of_injective_largeSite X.J (ringSheaf X.O) (Injective.under M),
      Injective.ι M, inferInstance⟩)
    (fun S hS h₁ h₂ ↦ ⟨isTotallyAcyclic_of_shortExact_largeSite X.J
        (hS.map_of_exact (SheafOfModules.toSheaf (ringSheaf X.O))) h₁ h₂,
      shortExact_map_pushforwardModules_largeSite f S hS h₁⟩) N hN

end DirectImage

namespace Leray

/-! ### Stacks 0734 with the three ringed topoi's universes unconstrained -/

section Relative

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasExt.{x} (Sheaf X.J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf X.J AddCommGrpCat.{w})]
  [HasExt.{x} (Sheaf Y.J AddCommGrpCat.{w'})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{w'})]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w'} (ringSheaf Y.O))]
  [HasDerivedCategory.{t} (SheafOfModules.{w} (ringSheaf X.O))]
  [HasDerivedCategory.{t'} (SheafOfModules.{w'} (ringSheaf Y.O))]
  [HasDerivedCategory.{t''} (SheafOfModules.{w''} (ringSheaf Z.O))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)

omit [EnoughInjectives (SheafOfModules.{w} (ringSheaf X.O))]
  [HasDerivedCategory.{t} (SheafOfModules.{w} (ringSheaf X.O))] in
/-- **The direct image along `f` of an injective `O_C`-module is right acyclic for the direct
image along `g`**, over ringed topoi whose universes are unrelated.  The direct image of an
injective module is totally acyclic
(Stacks 072Z,
`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective_largeSource`) and a module
with totally acyclic underlying abelian sheaf is right acyclic for a direct image
(Stacks 0731 part (4),
`Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic_largeSite`).  This is the
acyclicity hypothesis of the Grothendieck spectral sequence of the composition
`(g ∘ f)_* = g_* ∘ f_*`. -/
@[ega "0 12.2.4" "more general"]
theorem rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite
    (I : SheafOfModules.{w} (ringSheaf X.O)) (hI : Injective I) :
    (pushforwardModules g).rightAcyclic ((pushforwardModules f).obj I) :=
  have := hI
  rightAcyclic_pushforwardModules_of_isTotallyAcyclic_largeSite g _
    (isTotallyAcyclic_pushforwardModules_of_injective_largeSource f I)

variable (gf : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ gf.toToposHom.pushforward)
  (hτ : fSharpSetComp f g ≫ τ.hom.app (Sheaf.ringSheaf (ringSheaf X.O)) =
    fSharpSet gf)

include τ hτ in
/-- **The derived direct image of a composite is the composite of the derived direct images**,
`R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`, as an isomorphism of functors `D⁺(Mod(O_C)) ⥤ D⁺(Mod(O_E))`, over
ringed topoi whose universes are unrelated.

This is [Stacks, Tag 015M] applied to `(g ∘ f)_* = g_* ∘ f_*`, whose acyclicity hypothesis is
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite`;
the comparison `τ` identifies the right derived functor of the composite functor with that of
`gf_*`, right derivation only seeing a functor up to isomorphism.

It is the relative analogue of the identification `RΓ(C, F) = RΓ(D, Rf_*F)` of Stacks 08J6, and
it is the part of the content of [Stacks, Tag 0734] that is functorial in the object of
`D⁺(Mod(O_C))`: it identifies the object the relative Leray spectral sequence converges to
functorially.  It is *not* functoriality of that spectral sequence; see the section
"Functoriality in `F` is not covered" in the module documentation. -/
def derivedPushforwardCompIso_largeSite :
    (pushforwardModules gf).rightDerivedFunctorPlus ≅
      (pushforwardModules f).rightDerivedFunctorPlus ⋙
        (pushforwardModules g).rightDerivedFunctorPlus :=
  haveI := hasRightDerivedFunctor_pushforwardModules_largeSite f
  haveI := hasRightDerivedFunctor_pushforwardModules_largeSite g
  haveI := hasRightDerivedFunctor_pushforwardModules_largeSite gf
  (Functor.rightDerivedFunctorPlusNatIso (pushforwardModulesCompIso f g gf τ hτ)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _
      (rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite f g)

include τ hτ in
/-- **Stacks 0734, the relative Leray spectral sequence, with the three ringed topoi's object,
morphism and section universes unrelated.**  Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and
`g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed topoi, let `g ∘ f` be presented as
their composite by a comparison `τ` of the geometric direct images, and let `F^•` be an object
of `D⁺(Mod(O_C))`.  There is a spectral sequence with

`E_2^{p,q} = R^p g_*(R^q f_*(F^•))`

converging to `R^{p+q}(g ∘ f)_*(F^•)`.

`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence` is this statement for three
ringed topoi whose three universes are equal.  Here each site's objects may lie above its
morphisms and its sheaves, as they do on the small étale site of an algebraic space.  The
acyclicity input is
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite`,
i.e. Stacks 072Z followed by part (4) of Stacks 0731; the statement is for a bounded below
complex, which is the "version for bounded below complexes" the source also asserts, the
single-module case being the image of a module placed in degree zero.

The tag carries a qualifier because the source additionally asserts that the spectral sequence
is **functorial in `F`**, and that clause is outside this statement: it produces a spectral
sequence for one object of `D⁺(Mod(O_C))` at a time.  See the section "Functoriality in `F` is
not covered" in the module documentation for what the obstruction is and for
`Stacks.Cohomology.Leray.derivedPushforwardCompIso_largeSite`, the natural identification of the
abutment, which is the part of the clause that is available. -/
@[stacks 0734 "the spectral sequence, its second page and its convergence, for a bounded below
  complex, with the three ringed topoi's object, morphism and section universes unrelated; the
  functoriality in F is not covered",
  ega "0 12.2.4",
  sga "4 V 5.4",
  sga "4 V 5.3" "more general",
  sga "4½ Arcata 2.3.4" "more general"]
theorem exists_relativeLeraySpectralSequence_largeSite
    (K : DerivedCategory.Plus (SheafOfModules.{w} (ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence (SheafOfModules.{w''} (ringSheaf Z.O)) 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((pushforwardModules g).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{w'} (ringSheaf Y.O)) q).obj
              ((pushforwardModules f).rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{w''} (ringSheaf Z.O)) n).obj
            ((pushforwardModules gf).rightDerivedFunctorPlus.obj K)) := by
  have := hasRightDerivedFunctor_pushforwardModules_largeSite f
  have := hasRightDerivedFunctor_pushforwardModules_largeSite g
  have := hasRightDerivedFunctor_pushforwardModules_largeSite gf
  have : HasBinaryProducts (SheafOfModules.{w''} (ringSheaf Z.O)) :=
    HasFiniteLimits.out (Discrete WalkingPair)
  have : HasBinaryBiproducts (SheafOfModules.{w''} (ringSheaf Z.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryCoproducts (SheafOfModules.{w''} (ringSheaf Z.O)) :=
    hasBinaryCoproducts_of_hasBinaryBiproducts
  obtain ⟨L, hL, hfin, hmain⟩ :=
    Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp (pushforwardModules f)
      (pushforwardModules g)
      (rightAcyclic_pushforwardModules_pushforward_of_injective_largeSite f g) K
  let Fil : ∀ (_p n : ℤ), Subobject (L.X.X n) := fun p n =>
    Subobject.mk ((L.filtration.ι.app (Opposite.op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (L.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (L.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (L.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1))
  let FH : ∀ (n _p : ℤ), Subobject (L.X.homology n) := fun n p =>
    imageSubobject (HomologicalComplex.homologyMap (L.filtration.ι.app (Opposite.op p)) n)
  obtain ⟨E, hE, h2, -, -, -, -⟩ := hmain Fil (fun _ _ => rfl) Zc (fun _ _ _ => rfl)
    Dc (fun _ _ _ => rfl) FH (fun _ _ => rfl)
  refine ⟨E, h2, ?_⟩
  refine (CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite L Fil (fun _ _ => rfl)
    Zc (fun _ _ _ => rfl) Dc (fun _ _ _ => rfl) E hE hfin).of_nonempty_iso fun n => ?_
  exact ⟨(hL n).some ≪≫
    ((DerivedCategory.Plus.homologyFunctor
      (SheafOfModules.{w''} (ringSheaf Z.O)) n).mapIso
        ((Functor.rightDerivedFunctorPlusNatIso
          (pushforwardModulesCompIso f g gf τ hτ)).app K))⟩

end Relative

end Leray

end Stacks.Cohomology

end
