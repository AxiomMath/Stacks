module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.LerayCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray spectral sequence of a morphism of ringed topoi

Let `f : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed topoi. Global sections on the
source factor as `Γ(C, -) = Γ(D, -) ∘ f_*`, and the direct image of an injective module is
acyclic for `Γ(D, -)`; so the Grothendieck spectral sequence of a composition of right derived
functors applies and gives, for every bounded below complex `F^•` of `O_C`-modules, a spectral
sequence

`E_2^{p,q} = H^p(D, R^q f_*(F^•))  ⟹  H^{p+q}(C, F^•)`.

Both the acyclicity input and the factorisation are already proved in this development: the
direct image of an injective module is totally acyclic (Stacks 072Z,
`Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective`) and a totally acyclic
module is right acyclic for global sections (Stacks 0731 part (3),
`Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections`), while the factorisation is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardForgetIso`. What is added here is the
assembly: the identification `RΓ(C, -) ≅ RΓ(D, -) ∘ Rf_*` of Stacks 08J6, and the spectral
sequence of Stacks 0732 obtained from
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`.

## Main definitions

* `Stacks.Cohomology.Leray.globalSectionsAb`: global sections of sheaves of modules on a ringed
  topos read in abelian groups, i.e. the functor of Stacks 071H with its scalars forgotten.
* `Stacks.Cohomology.Leray.derivedGlobalSectionsPushforwardIso`: **Stacks 08J6**, the
  identification `RΓ(C, F) = RΓ(D, Rf_*F)` as an isomorphism of functors
  `D⁺(Mod(O_C)) ⥤ D⁺(Ab)`.

## Main results

* `Stacks.Cohomology.Leray.rightAcyclic_globalSectionsAb_pushforward_of_injective`: the direct
  image of an injective `O_C`-module is right acyclic for global sections on the target. This
  is Stacks 072Z followed by Stacks 0731 part (3), read in abelian groups; it is the hypothesis
  of the Grothendieck spectral sequence.
* `Stacks.Cohomology.Leray.exists_leraySpectralSequence`: **Stacks 0732, the Leray spectral
  sequence**, with second page `H^p(D, R^q f_*(F^•))` abutting to `H^{p+q}(C, F^•)`.
* `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_of_rightAcyclic`: the relative
  spectral sequence `R^p g_*(R^q f_*(F^•)) ⟹ R^{p+q}(g ∘ f)_*(F^•)`, with the acyclicity input
  of part (4) of Stacks 0731 carried as a hypothesis. This does **not** prove Stacks 0734 and
  is untagged; see the section "Omitted" below.

## Reading the statements

Cohomology is read in abelian groups throughout: `H^p(C, -)` is the degree-`p` right derived
functor of `globalSectionsAb`, and the hypercohomology of a bounded below complex is the
degree-`n` cohomology of `RΓ`, i.e. of `Functor.rightDerivedFunctorPlus` of that functor. The
reason for forgetting the scalars is that the source's own statement cannot carry them
coherently: its second page `H^p(D, R^q f_*(F^•))` consists of modules over `Γ(D, O_D)` and its
abutment `H^{p+q}(C, F^•)` of modules over `Γ(C, O_C)`, two different rings, so a spectral
sequence in a single abelian category containing both has to be taken either in abelian groups
or in `Γ(D, O_D)`-modules after restricting the scalars of the abutment — compare
`Stacks.Cohomology.Leray.nonempty_cohomologyIso_pushforward`, which takes the second option for
Stacks 0733. Forgetting the scalars is the option that names nothing but the source's own
objects, and that is why it is taken here. Each tag therefore carries a qualifier recording it.

"There is a spectral sequence converging to `H^{p+q}`" is
`CategoryTheory.SpectralSequence.AbutsTo`, the convergence clause used throughout the
development: the spectral sequence has an infinity page everywhere, and the terms
`E_∞^{p,n-p}` are the graded pieces of a finite decreasing filtration of `H^n`.

## Omitted

* **Stacks 0734, the relative Leray spectral sequence**, is not proved here. Its hypothesis is
  part (4) of Stacks 0731 — a totally acyclic sheaf is right acyclic for a direct image — which
  is not available in this development (see the implementation notes of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicGlobalSections.lean`,
  where only part (3) is proved), and 0734 additionally asserts that its spectral sequence is
  functorial in the sheaf, which the existential Grothendieck spectral sequence of
  [Stacks, Tag 015N] does not provide. See
  `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence_of_rightAcyclic` below, which
  is the relative spectral sequence with that acyclicity carried as a hypothesis and the
  functoriality clause absent; it is deliberately left untagged.
* Parts (1), (2) and (4) of Stacks 0731 and the flat case Stacks 0730 are not touched here.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Cohomology.SiteModules

namespace Stacks.Cohomology.Leray

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Global sections read in abelian groups -/

section GlobalSectionsAb

variable (X : RingedTopos.{u, u, u})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Global sections of sheaves of modules on a ringed topos, read in abelian groups: the functor
of Stacks 071H followed by the forgetful functor to abelian groups. By
`Stacks.Cohomology.globalSectionsUnderlyingIso` this is the functor of global sections of the
underlying abelian sheaf, so its right derived functors are the cohomology groups
`H^p(C, -)`. -/
abbrev globalSectionsAb :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ AddCommGrpCat.{u} :=
  globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    forget₂
      (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      AddCommGrpCat.{u}

end GlobalSectionsAb

/-! ### The shared assembly of the spectral sequence -/

/-- The Grothendieck spectral sequence of `G ∘ F` at `K` abuts to any graded object `H` isomorphic
to the cohomology of `R(G ∘ F)(K)`. -/
private theorem exists_spectralSequence_abutsTo_comp
    {A B C : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory.{u} A] [HasDerivedCategory.{u} B]
    [HasDerivedCategory.{u} C] [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (K : DerivedCategory.Plus A)
    (H : ℤ → C)
    (e : ∀ n, Nonempty ((DerivedCategory.Plus.homologyFunctor C n).obj
      ((F ⋙ G).rightDerivedFunctorPlus.obj K) ≅ H n)) :
    ∃ E : CohomologicalSpectralSequence C 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        (G.rightDerivedPlus p).obj ((DerivedCategory.Plus.homologyFunctor B q).obj
          (F.rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E H := by
  obtain ⟨L, hL, hfin, hmain⟩ :=
    Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp F G hFG K
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
  exact (CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite L Fil (fun _ _ => rfl)
    Zc (fun _ _ _ => rfl) Dc (fun _ _ _ => rfl) E hE hfin).of_nonempty_iso fun n =>
      ⟨(hL n).some ≪≫ (e n).some⟩

/-! ### The acyclicity hypothesis -/

section Setup

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
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{u} AddCommGrpCat.{u}]
  [HasDerivedCategory.{u}
    (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))]
  [((globalSectionsFunctor.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **The direct image of an injective module is right acyclic for global sections on the
target**, read in abelian groups. This is the hypothesis of the Grothendieck spectral sequence
for the composition `Γ(C, -) = Γ(D, -) ∘ f_*`, and it is the conjunction of the two lemmas the
source cites: the direct image of an injective module is totally acyclic (Stacks 072Z) and a
totally acyclic module is right acyclic for global sections (Stacks 0731 part (3)).

Forgetting the scalars is harmless because it preserves homology, so the higher right derived
functors of `Γ(D, -)` and of `globalSectionsAb Y` vanish at the same objects. -/
@[ega "0 12.2.4" "special case"]
lemma rightAcyclic_globalSectionsAb_pushforward_of_injective
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hZ : Injective Z) :
    (globalSectionsAb Y).rightAcyclic ((pushforwardModules f).obj Z) := by
  have hmod : (globalSectionsFunctor.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).rightAcyclic ((pushforwardModules f).obj Z) :=
    Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections _ _
      (isTotallyAcyclic_pushforward_injective f Z hZ)
  rw [Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived] at hmod ⊢
  intro p hp
  obtain ⟨w⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsFunctor.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (forget₂
      (ModuleCat.{u} (RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))
      AddCommGrpCat.{u}) p ((pushforwardModules f).obj Z)
  exact IsZero.of_iso (Functor.map_isZero _ (hmod p hp)) w.symm

/-! ### Stacks 08J6 -/

/-- The right derived functor of the composition `Γ(D, -) ∘ f_*` is the derived functor of
global sections on the source: `R(Γ(D, -) ∘ f_*) ≅ RΓ(C, -)`. This is the factorisation
`Γ(C, -) = Γ(D, -) ∘ f_*` of `globalSectionsPushforwardForgetIso` carried through right
derivation, which only sees a functor up to isomorphism. -/
def derivedGlobalSectionsCompPushforwardIso :
    (pushforwardModules f ⋙ globalSectionsAb Y).rightDerivedFunctorPlus ≅
      (globalSectionsAb X).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusNatIso (globalSectionsPushforwardForgetIso f)

/-- **Stacks 08J6**, read in abelian groups: `RΓ(C, F) = RΓ(D, Rf_*F)`.

The source's remark observes that [Stacks, Tag 015M] applies to the composition
`Γ(C, -) = Γ(D, -) ∘ f_*`, because the direct image of an injective module is totally acyclic
(Stacks 072Z) and a totally acyclic module is acyclic for global sections (Stacks 0731). This
is that application: the canonical map `R(Γ(D, -) ∘ f_*) ⟶ RΓ(D, -) ∘ Rf_*` is invertible, and
`Γ(C, -) ≅ Γ(D, -) ∘ f_*` carries the left hand side to `RΓ(C, -)`. The statement is an
isomorphism of functors on `D⁺(Mod(O_C))`, so it holds in particular at a single module placed
in degree zero, which is the form the remark displays. -/
@[stacks 08J6 "the identification RΓ(D, Rf_*F) = RΓ(C, F), read in abelian groups"]
def derivedGlobalSectionsPushforwardIso :
    (globalSectionsAb X).rightDerivedFunctorPlus ≅
      (pushforwardModules f).rightDerivedFunctorPlus ⋙
        (globalSectionsAb Y).rightDerivedFunctorPlus :=
  (derivedGlobalSectionsCompPushforwardIso f).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _
      (rightAcyclic_globalSectionsAb_pushforward_of_injective f)

/-! ### Stacks 0732 -/

/-- **Stacks 0732, the Leray spectral sequence**, read in abelian groups. Let
`f : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed topoi and `F^•` a bounded below
complex of `O_C`-modules, i.e. an object of `D⁺(Mod(O_C))`. There is a spectral sequence with

`E_2^{p,q} = H^p(D, R^q f_*(F^•))`

converging to `H^{p+q}(C, F^•)`.

This is the Grothendieck spectral sequence
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]) of the composition `Γ(C, -) = Γ(D, -) ∘ f_*`, whose hypothesis is
`Stacks.Cohomology.Leray.rightAcyclic_globalSectionsAb_pushforward_of_injective`; its abutment
`H^n(R(Γ(D, -) ∘ f_*)(F^•))` is identified with `H^n(C, F^•)` by
`Stacks.Cohomology.Leray.derivedGlobalSectionsPushforwardIso`, and convergence is read off the
degreewise finiteness of the filtration of the total complex by
`CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`. -/
@[stacks 0732 "read in abelian groups",
  ega "0 12.2.4" "special case",
  sga "4 V 5.3" "more general",
  sga "4 VII 1.5" "more general",
  sga "4½ Arcata 2.3.3" "more general"]
theorem exists_leraySpectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((globalSectionsAb Y).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj
              ((pushforwardModules f).rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
          ((globalSectionsAb X).rightDerivedFunctorPlus.obj K)) := by
  exact exists_spectralSequence_abutsTo_comp (pushforwardModules f) (globalSectionsAb Y)
    (rightAcyclic_globalSectionsAb_pushforward_of_injective f) K _ fun n =>
      ⟨(DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
        ((derivedGlobalSectionsCompPushforwardIso f).app K)⟩

end Setup

/-! ### The relative spectral sequence of Stacks 0734, with its acyclicity input assumed -/

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
  (gf : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ : f.toToposHom.pushforward ⋙ g.toToposHom.pushforward ≅ gf.toToposHom.pushforward)
  (hτ : fSharpSetComp f g ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet gf)

include τ hτ in
/-- **The relative Leray spectral sequence of [Stacks, Tag 0734], with the acyclicity input of
part (4) of Stacks 0731 carried as a hypothesis.** Let `f : (Sh(C), O_C) → (Sh(D), O_D)` and
`g : (Sh(D), O_D) → (Sh(E), O_E)` be morphisms of ringed topoi, `g ∘ f` a third morphism
presented as their composite by a comparison `τ` of the geometric direct images, and `F^•` an
object of `D⁺(Mod(O_C))`. If the direct image along `f` of every injective `O_C`-module is
right acyclic for the direct image along `g`, there is a spectral sequence with

`E_2^{p,q} = R^p g_*(R^q f_*(F^•))`

converging to `R^{p+q}(g ∘ f)_*(F^•)`.

**This is deliberately not tagged 0734, for two independent reasons.**

* The hypothesis `hacyclic` is a cited lemma of the source's proof, namely part (4) of
  Stacks 0731 applied to the totally acyclic sheaf `f_*I` of Stacks 072Z. Part (4) is not
  available in this development: the source proves it by replacing the morphism of ringed topoi
  by a morphism of ringed *sites* and reading off the higher direct images, and neither
  ingredient is present. Carrying it as a hypothesis means this statement does not prove the
  tag.
* Stacks 0734 asserts in addition that the spectral sequence is **functorial in `F`**. This
  statement produces a spectral sequence for one object of `D⁺(Mod(O_C))` at a time and nothing
  relates the sequences attached to two objects, so the functoriality clause is not proved
  either. The functorial form of an abutment is
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`; the Grothendieck spectral sequence
  this is built from,
  `CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`, is existential
  and supplies no such data.

What *is* proved is the second page and the abutment, for a bounded below complex — which is
the "version for bounded below complexes" the source also asserts, the single-module case being
the image of a module placed in degree zero. -/
@[sga "2 VIII 3.1" "more general", sga "4½ Th_finitude 1.3" "more general"]
theorem exists_relativeLeraySpectralSequence_of_rightAcyclic
    (hacyclic : ∀ I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), Injective I →
      (pushforwardModules g).rightAcyclic ((pushforwardModules f).obj I))
    (K : DerivedCategory.Plus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((pushforwardModules g).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj
              ((pushforwardModules f).rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) n).obj
            ((pushforwardModules gf).rightDerivedFunctorPlus.obj K)) := by
  exact exists_spectralSequence_abutsTo_comp (pushforwardModules f) (pushforwardModules g)
    hacyclic K _ fun n =>
      ⟨(DerivedCategory.Plus.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) n).mapIso
          ((Functor.rightDerivedFunctorPlusNatIso
            (pushforwardModulesCompIso f g gf τ hτ)).app K)⟩

end Relative

end Stacks.Cohomology.Leray

end
