module

public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RelativeLeraySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Leray spectral sequence, functorially in the module

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi. There is a spectral sequence

`E_2^{p,q} = R^p g_*(R^q f_* F)  ⟹  R^{p+q}(g ∘ f)_* F`,

**functorial in the `O_C`-module `F`**, and a version of it for bounded below complexes of
`O_C`-modules. That is the whole of [Stacks, Tag 0734], and
`Stacks.Cohomology.Leray.relativeLeraySpectralSequenceComp` and
`Stacks.Cohomology.Leray.relativeLeraySpectralSequencePlusComp` carry the tag between them.

Functoriality is not a decoration here: it is what the source asserts and what an existence
statement cannot express. `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`
produces a spectral sequence for one object of `D⁺(Mod(O_C))` at a time, with nothing relating
the spectral sequences of two objects, because the proof of [Stacks, Tag 015N] it rests on
chooses a bounded below complex representing `Rf_*F` and a Cartan-Eilenberg resolution of it,
neither choice being natural in `F`. The constructions below are built instead from the
truncation spectral object of the `t`-structure on `D⁺(Mod(O_D))`, read as a single spectral
object of a functor category; see
`StacksFrontier/Algebra/Homology/DerivedCategory/GrothendieckSpectralSequenceFunctorial.lean`, of
which this file is the application to the direct images of a composable pair of morphisms of
ringed topoi.

## Main definitions

* `Stacks.Cohomology.Leray.RelativeLeraySpectralSequenceData`: the data the tag asks for in the
  case of a module -- a functor from `O_C`-modules to first-quadrant `E₂` cohomological
  spectral sequences of `O_E`-modules, a natural identification of its second page with
  `R^p g_* ∘ R^q f_*`, and a functorial finite filtered abutment by `R^n (g ∘ f)_*`.
* `Stacks.Cohomology.Leray.RelativeLeraySpectralSequencePlusData`: the same for a bounded below
  complex, the spectral sequence being supported in the right half plane and its abutment being
  `H^n(R(g ∘ f)_*)`.

## Main results

* `Stacks.Cohomology.Leray.relativeLeraySpectralSequenceComp`: **[Stacks, Tag 0734] for a
  module**, the spectral sequence with its second page and its filtered abutment, functorially
  in the module, for the canonical composite of two morphisms of ringed topoi.
* `Stacks.Cohomology.Leray.relativeLeraySpectralSequencePlusComp`: **[Stacks, Tag 0734] for a
  bounded below complex**, which is the "version for bounded below complexes" the source also
  asserts.
* `Stacks.Cohomology.Leray.relativeLeraySpectralSequence` and
  `Stacks.Cohomology.Leray.relativeLeraySpectralSequencePlus`: the same two constructions for a
  composite presented by a comparison of the geometric direct images, which is the form the
  small etale ringed topoi of algebraic spaces need.

## Implementation notes

The acyclicity hypothesis of [Stacks, Tag 015M] -- that the direct image along `f` of an
injective `O_C`-module is right acyclic for the direct image along `g` -- is discharged, not
assumed: it is
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective`, i.e.
[Stacks, Tag 072Z] followed by part (4) of [Stacks, Tag 0731].

The two constructions come in two forms. The general one presents the composite `g ∘ f`, as
`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence` does, by a third morphism `gf`
together with a comparison `τ` of the geometric direct images carrying the composite structure
map to that of `gf`: the direct image of a composite of morphisms of ringed topoi in a concrete
situation -- a composite of morphisms of algebraic spaces, say -- is only canonically isomorphic
to the composite of the direct images. The abutment is then transported from `R(g_* ∘ f_*)` to
`R(gf)_*` along `τ`, which is the single place `τ` is used.

For morphisms of ringed topoi in the sense of [Stacks, Tag 01D3] those data are canonical: the
composite is `AlgebraicGeometry.RingedToposHom.comp` and `τ` is the identity, by
`fSharpSetComp_comp_eq`. The two tagged declarations are that specialisation, so they take no
hypothesis beyond the two morphisms.

The three ringed topoi have all of their universes equal, as in
`Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence` and in part (4) of
[Stacks, Tag 0731].

## References

* [Stacks Project, Lemma 21.14.7 (Tag 0734)](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology.Leray

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Functorial

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
  (gf : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)

/-- **The data [Stacks, Tag 0734] asks for in the case of a module.** A spectral sequence of
`O_E`-modules depending *functorially* on the `O_C`-module, its second page identified with
`R^p g_*(R^q f_* -)` as an isomorphism of functors, and a functorial finite filtered abutment
whose underlying object is `R^n(g ∘ f)_*`. -/
structure RelativeLeraySpectralSequenceData where
  /-- The spectral sequence, functorial in the module. -/
  sequence : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
    E₂CohomologicalSpectralSequenceNat (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  /-- Its natural second-page identification `E_2^{p,q} ≅ R^p g_*(R^q f_* -)`. -/
  pageTwoIso (p q : ℕ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (pushforwardModules f).rightDerived q ⋙ (pushforwardModules g).rightDerived p
  /-- Its functorial filtered abutment by the higher direct images of the composite. -/
  abutment : FunctorialFirstQuadrantAbutsTo sequence
    (fun n => (pushforwardModules gf).rightDerived n)

/-- **The data [Stacks, Tag 0734] asks for in the case of a bounded below complex.** A spectral
sequence of `O_E`-modules depending *functorially* on the object of `D⁺(Mod(O_C))`, its second
page identified with `R^p g_*(H^q(Rf_* -))` as an isomorphism of functors, the vanishing of
that page in the left half plane, and a functorial finite filtered abutment whose underlying
object is `H^n(R(g ∘ f)_*)`. -/
structure RelativeLeraySpectralSequencePlusData where
  /-- The spectral sequence, functorial in the bounded below complex. -/
  sequence : DerivedCategory.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    E₂CohomologicalSpectralSequence (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  /-- Its natural second-page identification `E_2^{p,q} ≅ R^p g_*(H^q(Rf_* -))`. -/
  pageTwoIso (p : ℕ) (q : ℤ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), q) ≅
      (pushforwardModules f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q ⋙ (pushforwardModules g).rightDerived p
  /-- The second page is supported in nonnegative first degree. -/
  pageTwo_isZero
      (K : DerivedCategory.Plus (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (p q : ℤ)
      (hp : p < 0) :
    IsZero ((sequence.obj K).page 2 |>.X (p, q))
  /-- Its functorial filtered abutment by the cohomology of the derived direct image of the
  composite. -/
  abutment : FunctorialRightHalfPlaneAbutsTo sequence
    (fun n => (pushforwardModules gf).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) n)

variable (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ gf.toToposHom.pushforward)
  (hτ : fSharpSetComp f g ≫ τ.hom.app (Sheaf.ringSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
    fSharpSet gf)

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The acyclicity hypothesis of [Stacks, Tag 015M] for the pair `f_*`, `g_*`, in the form the
functorial Grothendieck construction consumes. This is
`Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective`, i.e.
[Stacks, Tag 072Z] followed by part (4) of [Stacks, Tag 0731], and nothing is assumed. -/
theorem rightAcyclic_pushforwardModules_of_injective_forall :
    ∀ I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), Injective I →
      (pushforwardModules g).rightAcyclic ((pushforwardModules f).obj I) :=
  fun I hI => rightAcyclic_pushforwardModules_pushforward_of_injective f g I hI

include τ hτ in
/-- **[Stacks, Tag 0734] for a module: the relative Leray spectral sequence, functorial in the
module.** Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be
morphisms of ringed topoi, with the composite presented by `gf` and the comparison `τ`. There
is a functor from `O_C`-modules to spectral sequences of `O_E`-modules whose second page is
naturally `R^p g_*(R^q f_* F)` and which abuts, by a functorial finite filtration, to
`R^{p+q}(g ∘ f)_* F`.

The acyclicity hypothesis of [Stacks, Tag 015M] is discharged by
`rightAcyclic_pushforwardModules_of_injective_forall`; the abutment is transported from
`R^n(g_* ∘ f_*)` to `R^n (gf)_*` along `τ`. -/
@[sga "4 V 5.3" "more general"]
def relativeLeraySpectralSequence : RelativeLeraySpectralSequenceData f g gf where
  sequence := Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceNatFunctor
    (pushforwardModules f) (pushforwardModules g)
  pageTwoIso p q := Stacks.Cohomology.Grothendieck.natPageTwoIso
    (pushforwardModules f) (pushforwardModules g) p q
  abutment :=
    (Stacks.Cohomology.Grothendieck.natAbutment (pushforwardModules f) (pushforwardModules g)
      (rightAcyclic_pushforwardModules_of_injective_forall f g)).ofIsoAbutment
      (fun n => Functor.rightDerivedIsoOfNatIso
        (pushforwardModulesCompIso f g gf τ hτ) n)

include τ hτ in
/-- **[Stacks, Tag 0734] for a bounded below complex: the relative Leray spectral sequence,
functorial in the complex.** This is the "version for bounded below complexes of
`O_C`-modules" the source asserts alongside the module case: a functor from `D⁺(Mod(O_C))` to
spectral sequences of `O_E`-modules whose second page is naturally `R^p g_*(H^q(Rf_* K))`,
vanishes in the left half plane, and which abuts, by a functorial finite filtration, to
`H^{p+q}(R(g ∘ f)_* K)`.

As in the module case the acyclicity hypothesis of [Stacks, Tag 015M] is discharged by
`rightAcyclic_pushforwardModules_of_injective_forall`, and the abutment is transported along
`τ`. -/
def relativeLeraySpectralSequencePlus : RelativeLeraySpectralSequencePlusData f g gf where
  sequence := Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceFunctor
    (pushforwardModules f) (pushforwardModules g)
  pageTwoIso p q := Stacks.Cohomology.Grothendieck.plusPageTwoIso
    (pushforwardModules f) (pushforwardModules g) p q
  pageTwo_isZero K p q hp :=
    Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceFunctor_pageTwo_isZero
      (pushforwardModules f) (pushforwardModules g) K p q hp
  abutment := Stacks.Cohomology.Grothendieck.abutsToChangeAbutmentPlus
    (Stacks.Cohomology.Grothendieck.plusAbutment (pushforwardModules f) (pushforwardModules g)
      (rightAcyclic_pushforwardModules_of_injective_forall f g))
    (fun n => Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusNatIso (pushforwardModulesCompIso f g gf τ hτ))
      (DerivedCategory.Plus.homologyFunctor _ n))

end Functorial

section Composite

/-! ### The canonical composite

A morphism of ringed topoi in the sense of [Stacks, Tag 01D3] is the two-field datum
`AlgebraicGeometry.RingedToposHom`, and those do compose
(`AlgebraicGeometry.RingedToposHom.comp`, part (3) of that tag), with the direct image of the
composite *equal* to the composite of the direct images. For such a pair the presentation data
`gf`, `τ`, `hτ` above are supplied canonically -- `gf` is the composite, `τ` is the identity --
so the two constructions take no hypothesis beyond the two morphisms themselves. -/

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
  (f : AlgebraicGeometry.RingedToposHom X Y)
  (g : AlgebraicGeometry.RingedToposHom Y Z)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))] in
/-- For the composite of two morphisms of ringed topoi the comparison of the geometric direct
images is the identity, and it carries the composite structure map to the structure map of the
composite. That last fact is part (3) of [Stacks, Tag 01D3],
`AlgebraicGeometry.RingedToposHom.comp_fSharp_forget`, read through
`AlgebraicGeometry.RingedToposHom.ringFsharp_forget`. -/
theorem fSharpSetComp_comp_eq :
    fSharpSetComp f.toRingedToposModulesHom g.toRingedToposModulesHom ≫
        (Iso.refl (f.toRingedToposModulesHom.toToposHom.pushforward ⋙
          g.toRingedToposModulesHom.toToposHom.pushforward)).hom.app
            (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet (g.comp f).toRingedToposModulesHom := by
  rw [Iso.refl_hom, NatTrans.id_app, Category.comp_id, fSharpSetComp,
    show fSharpSet g.toRingedToposModulesHom = Z.forgetRing.map g.fSharp from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget g,
    show fSharpSet f.toRingedToposModulesHom = Y.forgetRing.map f.fSharp from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget f,
    show fSharpSet (g.comp f).toRingedToposModulesHom =
        Z.forgetRing.map (g.comp f).fSharp from
      AlgebraicGeometry.RingedToposHom.ringFsharp_forget (g.comp f)]
  exact (AlgebraicGeometry.RingedToposHom.comp_fSharp_forget g f).symm

/-- **[Stacks, Tag 0734] for a module.** Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and
`g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed topoi and let `F` be an
`O_C`-module. There is a spectral sequence with

`E_2^{p,q} = R^p g_*(R^q f_* F)`

converging to `R^{p+q}(g ∘ f)_* F`, **functorial in `F`**: the spectral sequence is a functor
of `F`, its second-page identification is an isomorphism of functors, and the finite filtration
of the abutment together with the identification of its graded pieces with the terms of the
infinity page is natural in `F`.

This is `relativeLeraySpectralSequence` for the canonical composite of `f` and `g`
(part (3) of [Stacks, Tag 01D3]), for which the comparison of direct images is the identity. -/
@[stacks 0734 "the spectral sequence for a module, functorial in the module, with its second
  page R^p g_*(R^q f_* F) and its functorial filtered abutment on R^{p+q}(g ∘ f)_* F",
  sga "4 V 5.3" "more general",
  sga "4½ Arcata 2.3.3" "more general",
  sga "4½ Th_finitude 1.3" "more general"]
def relativeLeraySpectralSequenceComp :
    RelativeLeraySpectralSequenceData f.toRingedToposModulesHom g.toRingedToposModulesHom
      (g.comp f).toRingedToposModulesHom :=
  relativeLeraySpectralSequence f.toRingedToposModulesHom g.toRingedToposModulesHom
    (g.comp f).toRingedToposModulesHom (Iso.refl _) (fSharpSetComp_comp_eq f g)

/-- **[Stacks, Tag 0734] for a bounded below complex**, the "version for bounded below
complexes of `O_C`-modules" the source asserts alongside the module case. For `f` and `g` as
above and `K` an object of `D⁺(Mod(O_C))` there is a spectral sequence with

`E_2^{p,q} = R^p g_*(H^q(Rf_* K))`

converging to `H^{p+q}(R(g ∘ f)_* K)`, **functorial in `K`** in the same three senses.

This is `relativeLeraySpectralSequencePlus` for the canonical composite of `f` and `g`. -/
@[stacks 0734 "the version for bounded below complexes of modules, functorial in the complex,
  with its second page R^p g_*(H^q(Rf_* K)) and its functorial filtered abutment on
  H^{p+q}(R(g ∘ f)_* K)", ega "0 12.2.4", sga "4 V 5.4"]
def relativeLeraySpectralSequencePlusComp :
    RelativeLeraySpectralSequencePlusData f.toRingedToposModulesHom
      g.toRingedToposModulesHom (g.comp f).toRingedToposModulesHom :=
  relativeLeraySpectralSequencePlus f.toRingedToposModulesHom g.toRingedToposModulesHom
    (g.comp f).toRingedToposModulesHom (Iso.refl _) (fSharpSetComp_comp_eq f g)

end Composite

end Stacks.Cohomology.Leray

end
