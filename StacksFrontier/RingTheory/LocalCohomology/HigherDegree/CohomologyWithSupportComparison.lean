module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.InjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.TorsionAcyclic
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.Finiteness
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology on the complement of a zero locus is local cohomology, shifted

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `Z = V(I)` and let
`U = X ∖ Z`. For an `A`-module `M` this file proves the comparison of Stacks 0DWR above degree
zero **as an isomorphism of `A`-modules**:

`H^p(U, M̃) ≅ H^{p+1}_Z(M)`  for `p ≥ 1`,

with `H^{p+1}_Z(M)` the local cohomology of `M` with support in the closed set `V(I)`, i.e. the
degree-`p+1` cohomology of the total right derived functor of the `V(I)`-supported sections of a
module.

Two halves of the statement are already available separately and are combined here.

* The long exact cohomology sequence of the closed subset `Z` gives
  `H^p(U, M̃) ≅ H^{p+1}_Z(X, M̃)` for `p ≥ 1`, where `H^•_Z(X, -)` is the right derived functor of
  the sections of a sheaf of modules on `X` with support in `Z`
  (`Stacks.LocalCohomologySequence.nonempty_iso_complementCohomology`). That comparison needs no
  hypothesis on `I` at all.
* The identification of `H^•_Z(X, M̃)` with the algebraic local cohomology of `M` is Stacks 0A6T,
  and is a Leray-type degreewise comparison for the composite `M ↦ Γ_Z(X, M̃)`: its two inputs are
  exactness of `M ↦ M̃`, which holds always, and right acyclicity of `Ẽ` for `Γ_Z(X, -)` for every
  injective `A`-module `E`.

The second input is what this file supplies for an arbitrary ideal of a Noetherian ring. For an
injective module `E` the cohomology `H^n_Z(X, Ẽ)` vanishes in every positive degree:

* in degrees `n ≥ 2` because `H^n_Z(X, Ẽ) ≅ H^{n-1}(U, Ẽ)` and the latter vanishes, which is the
  vanishing form of Stacks 0DWR above degree zero together with the vanishing of the algebraic
  local cohomology `H^i_{V(I)}(E)` of an injective module in degrees `i ≠ 0`;
* in degree `1` because the sequence ends `Γ(X, Ẽ) ⟶ Γ(U, Ẽ) ⟶ H¹_Z(X, Ẽ) ⟶ 0` and the first map
  is surjective, which is the four-term sequence of Stacks 0DWR in low degrees read with
  `H¹_{V(I)}(E) = 0`.

Both of those use that the algebraic local cohomology of an injective module vanishes outside
degree zero. That statement is available for the model built from the `V(I)`-supported sections,
and transfers to the coreflection model of Stacks 0A6Q in which the comparison of Stacks 0DWR is
phrased because the two models agree over a Noetherian ring, which is Stacks 0955.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule` — over a
  Noetherian ring the supported-sections model and the coreflection model of local cohomology
  agree degreewise.
* `Stacks.LocalCohomology.localCohomologyWithSupportInIsoRightDerived` — the degree-`n` local
  cohomology of a module placed in degree zero is the classical `n`-th right derived functor of
  `V(I)`-supported sections.
* `Stacks.LocalCohomologySequence.cohomologyWithSupportTildeIso` — **Stacks 0A6T degreewise, for
  an arbitrary ideal of a Noetherian ring**: the cohomology of `X` with support in `V(I)` of `M̃`,
  read as an `A`-module, is the algebraic local cohomology of `M`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_injective` — the local cohomology of an
  injective module vanishes outside degree zero.
* `Stacks.LocalCohomologySequence.isZero_complementCohomology_tilde_of_injective` — the
  cohomology of `Ẽ` on `U` vanishes in positive degrees for an injective module `E`.
* `Stacks.LocalCohomologySequence.surjective_tilde_presheaf_map_of_injective` — restriction of
  global sections of `Ẽ` to `U` is surjective for an injective module `E`.
* `Stacks.LocalCohomologySequence.isZero_cohomologyWithSupport_tilde_of_injective` and
  `Stacks.LocalCohomologySequence.rightAcyclic_sectionsWithSupport_tilde_of_injective` — **the
  sheaf attached to an injective module is acyclic for sections with support in `V(I)`**, for an
  arbitrary ideal of a Noetherian ring.
* `Stacks.LocalCohomologySequence.nonempty_complementCohomologyBase_iso_localCohomology`
  — **Stacks 0DWR above degree zero, as an isomorphism of `A`-modules.**
* `Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology`
  — its finiteness consequence, in every degree `p ≥ 0`: for a finite module `M` the `A`-module
  `H^p(U, M̃)` is finite exactly when `H^{p+1}_{V(I)}(M)` is.

## Implementation notes

The module universe equals the ring universe. That is forced by the vanishing form of Stacks
0DWR, which is available only there, and it costs the intended consumers nothing: the finiteness
statements are about finite modules over a Noetherian ring.

Two definitionally equal copies of the supported-sections model occur in the library, one in
`Module` and one in `Stacks.LocalCohomology`; the Leray comparison of Stacks 0A6T is stated at
the first and local cohomology with support at the second, and the composites below rely on
their agreement rather than on a transport.

`Stacks.Cohomology.rightDerivedSingleIso` is a private declaration of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence`, reached by
`import all`. It may be named in proofs but not in an exposed definition body, so the definition
whose body uses it carries `@[no_expose]`; its statement is the public one and consumers still get
the isomorphism.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this development;
it is already baked into the types of the local cohomology objects below. Nothing here mentions a
coproduct or a product of a derived category, which is where the standard model would make a
statement vacuous.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.LocalCohomology

/-- **The two models of local cohomology agree degreewise over a Noetherian ring.** The
degree-`i` local cohomology with support in the closed set `V(I)`, computed as the total right
derived functor of `V(I)`-supported sections, is the degree-`i` local cohomology in the
coreflection model of Stacks 0A6Q. The comparison is the canonical map of Stacks 0A6U, which is
invertible over a Noetherian ring by Stacks 0955. -/
def localCohomologyWithSupportInIsoLocalCohomologyModule (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (i : ℤ) :
    localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i ≅
      localCohomologyModule A I hI M i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (@asIso _ _ _ _ ((compareSectionsWithSupportLocalCohomology.{u, u} A I hI).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
      (isIso_compareSectionsWithSupportLocalCohomology_app.{u, u} A I hI _))

/-- **The local cohomology of an injective module vanishes outside degree zero.** For an
injective `A`-module `E` over a Noetherian ring and a finitely generated ideal `I`, the module
`H^i_I(E)` is zero for every `i ≠ 0`: an injective module placed in degree zero is a K-injective
complex, so its derived supported sections are the supported sections of `E` placed in degree
zero. The statement is transported to the coreflection model along the comparison of Stacks
0955. -/
theorem isZero_localCohomologyModule_of_injective (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (E : ModuleCat.{u} A)
    [CategoryTheory.Injective E] (i : ℤ) (hi : i ≠ 0) :
    IsZero (localCohomologyModule A I hI E i) :=
  (isZero_localCohomologyWithSupportIn_of_injective.{u, u}
    (PrimeSpectrum.zeroLocus (I : Set A)) E i hi).of_iso
      (localCohomologyWithSupportInIsoLocalCohomologyModule A I hI E i).symm

/-- **Local cohomology is the classical right derived functor of supported sections.** The
degree-`n` local cohomology with support in `T` of a module placed in degree zero is the value at
that module of Mathlib's `n`-th right derived functor of `T`-supported sections. Both are
computed by an injective resolution, and the comparison is the one attached to the total right
derived functor by its universal property. -/
@[no_expose]
def localCohomologyWithSupportInIsoRightDerived (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{u} A) (n : ℕ) :
    localCohomologyWithSupportIn.{u, u} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (n : ℤ) ≅
      ((sectionsWithSupportInFunctor.{u, u} A T).rightDerived n).obj M :=
  letI : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  Stacks.Cohomology.rightDerivedSingleIso (sectionsWithSupportInFunctor.{u, u} A T)
    (derivedSectionsWithSupportIn.{u, u} A T) (derivedSectionsWithSupportInUnit.{u, u} A T)
    (fun K ↦ by
      obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨J, q, hJ, hq⟩)
    M n

end Stacks.LocalCohomology

namespace Stacks.LocalCohomologySequence

open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

variable {A : CommRingCat.{u}}

/-- **The cohomology of `Ẽ` on `U = X ∖ V(I)` vanishes in positive degrees for an injective
module `E`.** The abelian-group-valued cohomology of the open complement is the forgetful image
of the module-valued right derived functor of sections over it, and forgetting the module
structure is faithful, so it reflects zero objects. In the module-valued form the vanishing is
the vanishing form of Stacks 0DWR above degree zero, which turns `H^n(U, Ẽ) = 0` into
`H^{n+1}_I(E) = 0`; the latter holds because `E` is injective. -/
theorem isZero_complementCohomology_tilde_of_injective [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E]
    (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((complementCohomology I n).obj (tildeSheaf E)) := by
  refine isZero_of_faithful (forget₂ (GlobalModules (Spec A).toRingedSpace) AddCommGrpCat.{u}) ?_
  refine IsZero.of_iso ?_ ((complementCohomologyForgetIso I n).app (tildeSheaf E))
  have key : IsZero (((SheafOfModules.evaluation (Spec A).ringCatSheaf
      (op (Stacks.LocalCohomology.complementZeroLocus A I))).rightDerived n).obj
        (Stacks.LocalCohomology.associatedSheaf A E)) :=
    (Stacks.LocalCohomology.isZero_rightDerived_complement_iff_isZero_localCohomologyModule
        I hI E n hn).2
      (Stacks.LocalCohomology.isZero_localCohomologyModule_of_injective A I hI E _ (by omega))
  exact (Stacks.LocalCohomology.isZero_hgroup_iff_isZero_rightDerived (Spec A).ringCatSheaf
    (Stacks.LocalCohomology.complementZeroLocus A I) n (tildeSheaf E)).2 key

/-- **Every section of `Ẽ` on `U = X ∖ V(I)` is the restriction of a module element**, for an
injective module `E`. The four-term exact sequence of Stacks 0DWR in low degrees ends
`M ⟶ Γ(U, M̃|U) ⟶ H¹_I(M) ⟶ 0`, and the last term vanishes for an injective module, so the first
map is surjective. -/
theorem surjective_restrictionToComplement_of_injective [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    Function.Surjective (Stacks.LocalCohomology.restrictionToComplement
      (Stacks.LocalCohomology.localizationTriangleData A I hI) E
      (Stacks.LocalCohomology.complementTilde A I E) (Iso.refl _)) := by
  obtain ⟨-, -, hexact, -⟩ := Stacks.LocalCohomology.exact_lowDegreeSequence A I hI E
    (Stacks.LocalCohomology.complementTilde A I E) (Iso.refl _)
  intro t
  refine (hexact t).1 ?_
  have hz := Stacks.LocalCohomology.isZero_localCohomologyModule_of_injective A I hI E 1
    one_ne_zero
  have : Subsingleton (Stacks.LocalCohomology.localCohomologyModule A I hI E 1) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact Subsingleton.elim _ _

/-- **Restriction of the global sections of `Ẽ` to `U = X ∖ V(I)` is surjective**, for an
injective module `E` over a Noetherian ring and a finitely generated ideal `I`. A section on `U`
is the image of a module element `m`, and the family which is `m/1` at every point of the whole
spectrum is a global section restricting to it. -/
theorem surjective_tilde_presheaf_map_of_injective [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    Function.Surjective (((tilde E).val.presheaf.map
      (homOfLE (le_top : Stacks.LocalCohomology.complementZeroLocus A I ≤ ⊤)).op).hom) := by
  intro s
  let e := (Stacks.LocalCohomology.sectionsOnAffineComplementIso I).app
    (Stacks.LocalCohomology.associatedSheaf A E)
  obtain ⟨m, hm⟩ := surjective_restrictionToComplement_of_injective I hI E (e.inv.hom s)
  have hinv := e.inv_hom_id_apply s
  refine ⟨⟨fun x ↦ LocalizedModule.mk m 1, fun x ↦ ⟨⊤, trivial, 𝟙 _, m, 1,
      fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩, ?_⟩
  rw [← hinv, ← hm, Stacks.LocalCohomology.restrictionToComplement_apply]
  apply Subtype.ext
  rfl

/-- The restriction transformation of the cohomology sequence of `V(I)` is an epimorphism at
`Ẽ` for an injective module `E` over a Noetherian ring: it is the restriction of sections from
the whole spectrum to the open complement, which is surjective. -/
theorem epi_restrictionToComplement_tilde_of_injective [IsNoetherianRing A] (I : Ideal A)
    (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    Epi ((restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
      (isClosed_zeroLocusSubset _)).app (tildeSheaf E)) := by
  rw [ModuleCat.epi_iff_surjective]
  exact surjective_tilde_presheaf_map_of_injective I hI E

/-- The degree-zero restriction map of the cohomology sequence of `V(I)` is an epimorphism at
`Ẽ` for an injective module `E` over a Noetherian ring. Sections over the open complement form a
left exact functor, so the canonical transformation to its degree-zero right derived functor is
invertible, and the claim follows from surjectivity of the restriction on sections. -/
theorem epi_complementRestriction_zero_tilde_of_injective [IsNoetherianRing A] (I : Ideal A)
    (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    Epi ((complementRestriction I 0).app (tildeSheaf E)) := by
  have hsq := NatTrans.congr_app
    (ModuleSheafCohomology.toRightDerivedZero_naturality_functor
      (restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset _))) (tildeSheaf E)
  simp only [NatTrans.comp_app] at hsq
  have := epi_restrictionToComplement_tilde_of_injective I hI E
  have hcomp : Epi ((SheafOfModules.evaluation
      (structureSheafRing (Spec A).toRingedSpace)
        (op ⊤)).toRightDerivedZero.app (tildeSheaf E) ≫
      (complementRestriction I 0).app (tildeSheaf E)) := by
    rw [← hsq]
    exact epi_comp _ _
  exact epi_of_epi ((SheafOfModules.evaluation
    (structureSheafRing (Spec A).toRingedSpace)
      (op ⊤)).toRightDerivedZero.app (tildeSheaf E)) _

/-- **The cohomology with support in `V(I)` of `Ẽ` vanishes in positive degrees**, for an
injective module `E` over a Noetherian ring and a finitely generated ideal `I`. In degree one the
cohomology sequence of the vanishing locus ends with an epimorphism onto `H¹_Z(X, Ẽ)` which is
also zero, because the map before it is an epimorphism; in degrees two and above the sequence
identifies `H^{p+1}_Z(X, Ẽ)` with `H^p(U, Ẽ)`, which vanishes. -/
theorem isZero_cohomologyWithSupport_tilde_of_injective [IsNoetherianRing A] (I : Ideal A)
    (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] (n : ℕ) (hn : 0 < n) :
    IsZero ((cohomologyWithSupport I n).obj (tildeSheaf E)) := by
  match n, hn with
  | 1, _ =>
    obtain ⟨delta, -, hexact, hepi, -⟩ := exact_cohomologyWithSupport_sequence I E
    have := epi_complementRestriction_zero_tilde_of_injective I hI E
    have hzero : (complementRestriction I 0).app (tildeSheaf E) ≫
        (delta 0).app (tildeSheaf E) = 0 := hexact.toIsComplex.zero 1
    have hd : (delta 0).app (tildeSheaf E) = 0 := zero_of_epi_comp _ hzero
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    have := hepi
    apply (cancel_epi ((delta 0).app (tildeSheaf E))).1
    simp [hd]
  | (p + 2), _ =>
    obtain ⟨e⟩ := nonempty_iso_complementCohomology I E (p + 1) p.succ_pos
    exact IsZero.of_iso (isZero_complementCohomology_tilde_of_injective I hI E (p + 1)
      (by omega)) e.symm

/-- **The sheaf attached to an injective module is right acyclic for sections with support in a
vanishing locus.** Sections with support are left exact, so right acyclicity is the vanishing of
all higher right derived functors, and that is the previous statement. This is the input to the
Leray comparison of Stacks 0A6T which the principal case of that tag obtained from affineness of
the complement. -/
theorem rightAcyclic_sectionsWithSupport_tilde_of_injective [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    (sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
      (isClosed_zeroLocusSubset _)).rightAcyclic ((tildeSheafFunctor A).obj E) := by
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  exact isZero_cohomologyWithSupport_tilde_of_injective I hI E p hp

/-- **Stacks 0A6T degreewise, for an arbitrary ideal of a Noetherian ring.** Let `A` be a
Noetherian ring, `I ⊆ A` a finitely generated ideal, `X = Spec A` and `Z = V(I)`. For an
`A`-module `M` the cohomology of `X` with support in `Z` of the sheaf `M̃`, read as an `A`-module,
is the algebraic local cohomology `H^n_Z(M)` of `M` in every degree `n`.

The two inputs of the Leray-type degreewise comparison for the composite `M ↦ Γ_Z(X, M̃)` are
right acyclicity of `Ẽ` for `Γ_Z(X, -)` at every injective `E`, and exactness of `M ↦ M̃`, which
makes every module right acyclic for it. -/
def cohomologyWithSupportTildeIso [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (globalToBase A).obj ((cohomologyWithSupport I n).obj (tildeSheaf M)) ≅
      ((Stacks.LocalCohomology.sectionsWithSupportInFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))).rightDerived n).obj M :=
  (globalToBase A).mapIso
      (Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso (tildeSheafFunctor A)
        (sectionsWithSupport (Spec A).toRingedSpace
          (zeroLocusSubset I) (isClosed_zeroLocusSubset _))
        (fun E hE => have := hE; rightAcyclic_sectionsWithSupport_tilde_of_injective I hI E)
        M (rightAcyclic_tildeSheafFunctor M) n).symm ≪≫
    (rightDerivedSectionsWithSupportTildeIso
      (PrimeSpectrum.zeroLocus (I : Set A))
      (isClosed_zeroLocusSubset I) n).app M

/-- The cohomology with support in `V(I)` of `M̃`, read as an `A`-module, is isomorphic to the
local cohomology `H^n_{V(I)}(M)`. -/
private theorem nonempty_cohomologyWithSupport_iso_localCohomology [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    Nonempty ((globalToBase A).obj ((cohomologyWithSupport I n).obj (tildeSheaf M)) ≅
      Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (n : ℤ)) :=
  ⟨cohomologyWithSupportTildeIso I (Ideal.fg_of_isNoetherianRing I) M n ≪≫
    (Stacks.LocalCohomology.localCohomologyWithSupportInIsoRightDerived A
      (PrimeSpectrum.zeroLocus (I : Set A)) M n).symm⟩

/-- **Stacks 0DWR above degree zero, as an isomorphism of `A`-modules.** Let `A` be a Noetherian
ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `Z = V(I)` and let `U = X ∖ Z`. For an
`A`-module `M` and every `p ≥ 1` the `A`-module `H^p(U, M̃)` is the local cohomology
`H^{p+1}_Z(M)` of `M` with support in `V(I)`.

Both sides are `A`-modules and the isomorphism is `A`-linear, which is what distinguishes this
statement from the vanishing form of the same comparison. The connecting map of the long exact
cohomology sequence of `Z` identifies `H^p(U, M̃)` with the cohomology with support
`H^{p+1}_Z(X, M̃)`, and Stacks 0A6T identifies the latter with the algebraic local cohomology of
`M`.

The source only asserts that the two modules are isomorphic, so the result is stated as
nonemptiness of the type of isomorphisms. The tag itself is registered on
`Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule`, which
needs only `I` finitely generated and holds for every `F` with `F ≅ M̃|_U`. -/
@[ega "III 1.1.10" "H^p(U)≅H^{p+1}_Z, p≥1",
  sga "2 II Corollary4" "(4.3), Noetherian", sga "2 III 3.13" "identification H^i_Y(X"]
theorem nonempty_complementCohomologyBase_iso_localCohomology
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ) (hp : 1 ≤ p) :
    Nonempty (complementCohomologyBase I M p ≅
      Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((p + 1 : ℕ) : ℤ)) := by
  obtain ⟨e⟩ := nonempty_iso_complementCohomology I M p hp
  obtain ⟨e'⟩ := nonempty_cohomologyWithSupport_iso_localCohomology I M (p + 1)
  exact ⟨(globalToBase A).mapIso e ≪≫ e'⟩

/-- **The finiteness consequence of Stacks 0DWR, in every degree.** For a finite module `M` over
a Noetherian ring the `A`-module `H^p(U, M̃)` on `U = Spec A ∖ V(I)` is finite exactly when the
local cohomology `H^{p+1}_{V(I)}(M)` is, for every `p ≥ 0`.

In degree zero this is the four-term exact sequence of Stacks 0DWR, which presents `Γ(U, M̃)` as
an extension of `H¹_{V(I)}(M)` by a quotient of `M`; in degrees above zero it is the isomorphism
above.

This is **Stacks 0BK0 (3), the equivalence of (b) and (c)**, for an arbitrary ideal `I` of a
Noetherian ring `A` (the tag's own hypothesis on `A`, not an additional one) and every `p ≥ 0`:
no finite generation of `I` beyond what `A` Noetherian already gives, and no restriction to a
principal ideal, is needed. -/
@[stacks 0BK0 "(3), (b) ⟺ (c)"]
theorem finite_complementCohomologyBase_iff_finite_localCohomology
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) :
    Module.Finite A (complementCohomologyBase I M p) ↔
      Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((p + 1 : ℕ) : ℤ)) := by
  rw [finite_complementCohomologyBase_iff I M p]
  obtain ⟨e⟩ := nonempty_cohomologyWithSupport_iso_localCohomology I M (p + 1)
  exact ⟨fun _ ↦ Module.Finite.equiv e.toLinearEquiv,
    fun _ ↦ Module.Finite.equiv e.symm.toLinearEquiv⟩

end Stacks.LocalCohomologySequence

end
