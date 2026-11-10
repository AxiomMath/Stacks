module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.LeraySpectralSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Leray spectral sequence

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi and let `F^•` be a bounded below complex of `O_C`-modules, i.e. an object of
`D⁺(Mod(O_C))`. There is a spectral sequence

`E_2^{p,q} = R^p g_*(R^q f_*(F^•))  ⟹  R^{p+q}(g ∘ f)_*(F^•)`,

and the derived direct image of the composite is the composite of the derived direct images,
`R(g ∘ f)_* ≅ Rg_* ∘ Rf_*`, as an isomorphism of functors on `D⁺(Mod(O_C))`.

`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_of_rightAcyclic` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/LeraySpectralSequence.lean` already
produces the spectral sequence, but carries the acyclicity input of its source's proof — part
(4) of Stacks 0731, applied to the totally acyclic direct image `f_*I` of Stacks 072Z — as a
hypothesis. That hypothesis is discharged here: part (4) is
`Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic` and Stacks 072Z is
`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`, so the direct image along
`f` of an injective `O_C`-module is right acyclic for the direct image along `g` and nothing
need be assumed.

## Main definitions

* `Stacks.Cohomology.Leray.derivedPushforwardCompIso`: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` as an
  isomorphism of functors `D⁺(Mod(O_C)) ⥤ D⁺(Mod(O_E))`, the relative analogue of the
  identification of Stacks 08J6.

## Main results

* `Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective`: the
  direct image along `f` of an injective `O_C`-module is right acyclic for the direct image
  along `g`. This is Stacks 072Z followed by part (4) of Stacks 0731, and it is the hypothesis
  of the Grothendieck spectral sequence.
* `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`: the relative Leray spectral
  sequence of a single bounded below complex, with second page `R^p g_*(R^q f_*(F^•))` abutting
  to `R^{p+q}(g ∘ f)_*(F^•)`, with no acyclicity hypothesis.

## Where Stacks 0734 is proved

Stacks 0734 ends by asserting that its spectral sequence is *functorial in `F`*, and an
existence statement cannot express that: `exists_relativeLeraySpectralSequence` produces a
spectral sequence for each object of `D⁺(Mod(O_C))` separately and relates the spectral
sequences of two objects by nothing at all. The tag is therefore carried by
`Stacks.Cohomology.Leray.relativeLeraySpectralSequence` and
`Stacks.Cohomology.Leray.relativeLeraySpectralSequencePlus` of the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RelativeLeraySpectralSequenceFunctorial`,
which construct the spectral sequence as a *functor* of the module, respectively of the bounded
below complex, together with the natural identification of its second page and a functorial
finite filtered abutment.

The statement here is not a step towards those: it goes through
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]), whose proof chooses a bounded below complex representing `Rf_*(F^•)` and a
Cartan-Eilenberg resolution of it, neither choice being natural in `F^•`. The functorial
construction takes an independent route, through the truncation spectral object of the
`t`-structure on `D⁺(Mod(O_D))` read in a functor category; see
`StacksFrontier/Algebra/Homology/DerivedCategory/GrothendieckSpectralSequenceFunctorial.lean`. What
the two share is the acyclicity input, which is
`rightAcyclic_pushforwardModules_pushforward_of_injective` below.

Independently of either, `derivedPushforwardCompIso` identifies the abutment naturally:
it is an isomorphism of *functors* `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` on `D⁺(Mod(O_C))`.

## Implementation notes

The spectral sequence is quoted verbatim from
`exists_relativeLeraySpectralSequence_of_rightAcyclic`, which is applied to the acyclicity now
available; nothing of its proof is repeated. The composite `g ∘ f` is presented, as there, by a
third morphism `gf` together with a comparison `τ` of the geometric direct images carrying the
composite structure map to that of `gf`, because a morphism of ringed topoi has an abstract
direct image and the direct image of a composite is only canonically isomorphic to the
composite of the direct images.

The three ringed topoi have all of their universes equal, as in
`exists_relativeLeraySpectralSequence_of_rightAcyclic` and in part (4) of Stacks 0731.

## References

* [Stacks Project, Lemma 21.14.7 (Tag 0734)](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology.Leray

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Relative

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The direct image along `f` of an injective `O_C`-module is right acyclic for the direct
image along `g`. The direct image of an injective module is totally acyclic
(Stacks 072Z, `Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`) and a
module with totally acyclic underlying abelian sheaf is right acyclic for a direct image
(Stacks 0731 part (4),
`Stacks.Cohomology.rightAcyclic_pushforwardModules_of_isTotallyAcyclic`). This is the
acyclicity hypothesis of the Grothendieck spectral sequence of the composition
`(g ∘ f)_* = g_* ∘ f_*`. -/
@[ega "0 12.2.4" "more general"]
theorem rightAcyclic_pushforwardModules_pushforward_of_injective
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hI : Injective I) :
    (pushforwardModules g).rightAcyclic ((pushforwardModules f).obj I) :=
  have := hI
  rightAcyclic_pushforwardModules_of_isTotallyAcyclic g _
    (isTotallyAcyclic_pushforwardModules_of_injective f I)

variable (gf : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ gf.toToposHom.pushforward)
  (hτ : fSharpSetComp f g ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
    fSharpSet gf)

include τ hτ in
/-- **The derived direct image of a composite is the composite of the derived direct images**,
`R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`, as an isomorphism of functors `D⁺(Mod(O_C)) ⥤ D⁺(Mod(O_E))`. This
is [Stacks, Tag 015M] applied to `(g ∘ f)_* = g_* ∘ f_*`, whose acyclicity hypothesis is
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective`; the
comparison `τ` identifies the right derived functor of the composite functor with that of
`gf_*`, right derivation only seeing a functor up to isomorphism.

It is the relative analogue of the identification `RΓ(C, F) = RΓ(D, Rf_*F)` of Stacks 08J6: it
identifies the object the relative Leray spectral sequence converges to, functorially in the
object of `D⁺(Mod(O_C))`. -/
def derivedPushforwardCompIso :
    (pushforwardModules gf).rightDerivedFunctorPlus ≅
      (pushforwardModules f).rightDerivedFunctorPlus ⋙
        (pushforwardModules g).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusNatIso (pushforwardModulesCompIso f g gf τ hτ)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _
      (rightAcyclic_pushforwardModules_pushforward_of_injective f g)

include τ hτ in
/-- **The relative Leray spectral sequence of a single bounded below complex.** Let
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `g ∘ f` be presented as their composite by a comparison `τ` of the geometric direct
images, and let `F^•` be an object of `D⁺(Mod(O_C))`. There is a spectral sequence with

`E_2^{p,q} = R^p g_*(R^q f_*(F^•))`

converging to `R^{p+q}(g ∘ f)_*(F^•)`.

This is
`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_of_rightAcyclic` with its
acyclicity hypothesis discharged by
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective`, i.e. by
Stacks 072Z followed by part (4) of Stacks 0731.

[Stacks, Tag 0734] asks in addition that the spectral sequence be *functorial in `F`*, which an
existential cannot say; the tag is carried by
`Stacks.Cohomology.Leray.relativeLeraySpectralSequence` and
`Stacks.Cohomology.Leray.relativeLeraySpectralSequencePlus`, which construct it as a functor.
See "Where Stacks 0734 is proved" in the module documentation. -/
@[sga "4 V 5.3" "more general", sga "4½ Th_finitude 1.3" "more general"]
theorem exists_relativeLeraySpectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((pushforwardModules g).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj
              ((pushforwardModules f).rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) n).obj
            ((pushforwardModules gf).rightDerivedFunctorPlus.obj K)) :=
  exists_relativeLeraySpectralSequence_of_rightAcyclic f g gf τ hτ
    (rightAcyclic_pushforwardModules_pushforward_of_injective f g) K

end Relative

end Stacks.Cohomology.Leray

end
