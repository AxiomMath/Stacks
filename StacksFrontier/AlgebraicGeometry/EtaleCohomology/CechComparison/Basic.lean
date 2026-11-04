module

public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedOfDegreeZeroViaDeltaFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroOfASheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech-to-cohomology spectral sequence: Stacks 03OW

Let `C` be a site, let `𝒰 = {U_i → U}` be a covering of an object `U` and let `F` be an abelian
sheaf on `C`.  [Stacks, Tag 03OW] asserts that there is a spectral sequence

```
E₂^{p,q} = Ȟ^p(𝒰, H^q(F))  ⟹  H^{p+q}(U, F),
```

where `H^q(F)` is the abelian presheaf `V ↦ H^q(V, F)`.  [Stacks, Tag 03OX] records what the
proof is: this is the Grothendieck spectral sequence of the composition

```
Ab(C) --i--> PAb(C) --Ȟ⁰(𝒰,-)--> Ab
```

of the inclusion of abelian sheaves into abelian presheaves with degree-zero Čech cohomology,
and that is exactly how it is built here.  The three inputs are all results of chapter
21 in the library and none of them is reproved:

* the Grothendieck spectral sequence itself, with its second page and its abutment, is
  `CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp`
  ([Stacks, Tag 015N] and the convergence clause of [Stacks, Tag 01F2]);
* its acyclicity hypothesis — `Ȟ⁰(𝒰, -)`-acyclicity of `i(I)` for an injective abelian sheaf
  `I` — is assembled below from [Stacks, Tag 03AW] (positive-degree Čech cohomology of an
  injective abelian sheaf vanishes,
  `Stacks.CechSite.injective_sheaf_cechCohomology_isZero`) and [Stacks, Tag 03AU] (Čech
  cohomology is the right derived functor of its degree-zero part,
  `Stacks.CechSite.cechCohomologyIsoRightDerivedPlus`);
* the second page is turned into Čech cohomology of the cohomology presheaves by the same
  [Stacks, Tag 03AU] comparison together with the objectwise half of [Stacks, Tag 03AY]
  (`Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf`), which identifies `R^q i(F)` with
  Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`, i.e. with the presheaf `H^q(F)` of the
  statement.

## Main definitions

* `Stacks.CechComparison.sheafIncl`, `Stacks.CechComparison.cechZeroFunctor`: the two functors
  `i` and `Ȟ⁰(𝒰, -)` whose composition [Stacks, Tag 03OX] names.
* `Stacks.CechComparison.rightDerivedPlus_sheafToPresheaf_obj_iso_cohomologyPresheaf`:
  `R^q i(F) ≅ H^q(F)`, the `ℤ`-indexed form of the objectwise half of [Stacks, Tag 03AY].

## Main results

* `Stacks.CechComparison.rightAcyclic_cechCohomologyZero_sheafToPresheaf_obj`: the underlying
  presheaf of an injective abelian sheaf is right acyclic for `Ȟ⁰(𝒰, -)`.
* `Stacks.CechComparison.exists_cechToCohomology_spectralSequence`: the spectral sequence of
  [Stacks, Tag 03OW], with its second page as the Grothendieck spectral sequence produces it.
* `Stacks.CechComparison.exists_cechToCohomology_spectralSequence_pageTwo`: the same spectral
  sequence with its second page identified as `Ȟ^p(𝒰, H^q(F))`, which is the second page
  [Stacks, Tag 03OW] states.
* `Stacks.CechComparison.nonempty_cechZeroFunctor_sheafToPresheaf_obj_iso_sections`: the
  composite `Ȟ⁰(𝒰, -) ∘ i` is, at each abelian sheaf, the sections over the covered object.
  This is the objectwise half of the abutment identification, and what it leaves open is
  exactly the naturality discussed below.

## Implementation notes

**What is proved and what is not.**  The abutment produced here is
`R^{p+q}(Ȟ⁰(𝒰, -) ∘ i)(F)`, the cohomology of the right derived functor of the composite,
and not literally `H^{p+q}(U, F)`.  Identifying the two needs the degree-zero Čech comparison
`i ⋙ Ȟ⁰(𝒰, -) ≅ i ⋙ (evaluation at U)` **as a natural isomorphism of functors on abelian
sheaves**, and that is not available: [Stacks, Tag 03AW] degree zero is available only objectwise
and only as a `Nonempty`, namely `Stacks.CechSite.cechCohomology_zero_iso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/DegreeZeroOfASheaf.lean`, whose proof goes through
`Stacks.CechSite.cechCohomologyZeroEquiv`, for which no naturality in the presheaf is proved.
The tag is therefore placed with the clause `"the spectral sequence and its second page"` and
not on the abutment identification.

**The engine quantifies over presentations.** [Stacks, Tag 015N] produces a filtered complex
and then, for every presentation `(Fil, Z, D)` of its filtration in the sense of
[Stacks, Tag 012M], a spectral sequence.  The canonical presentation is supplied here, so the
spectral sequence below is the one attached to that canonical choice.

**Universes.** The site is small and the covering index type lies in the same universe, which is
the universe in which the coverings of the topology themselves live:
`CategoryTheory.GrothendieckTopology.Cover.preOneHypercover` of a cover of a small site is a
`CategoryTheory.PreZeroHypercover.{u}`.  This is also what lets the statements here compose with
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CechComparison/Locality.lean`.  The coefficient
universe is then the single universe `u`, which is what
`Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf` is stated at.

**Instances.** `EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{u})` is not found by instance search
even for a small site, so it is registered here from
`Stacks.CechSite.presheafEnoughInjectives` ([Stacks, Tag 01DK]); with all universes pinned to
`u` this causes none of the universe-unification trouble that
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/RightDerivedOfDegreeZeroViaDeltaFunctors.lean`
records for the general shape.
`PreservesFiniteLimits (Ȟ⁰(𝒰, -))` is likewise rebuilt from the public
`Stacks.Cohomology.CechDerived.preservesFiniteLimits_functor_zero`, because
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/RightDerivedOfDegreeZeroViaDeltaFunctors.lean`
registers it only as a `local instance`.

## References

* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
* [Stacks Project, Tag 03OX](https://stacks.math.columbia.edu/tag/03OX)
* [Stacks Project, Tag 03AZ](https://stacks.math.columbia.edu/tag/03AZ)
* [Stacks Project, Tag 03AU](https://stacks.math.columbia.edu/tag/03AU)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CechComparison

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks 01DK, as an instance.** Abelian presheaves on a small site have enough injectives.
This is `Stacks.CechSite.presheafEnoughInjectives` with all its universes pinned to the
universe of the site; instance search does not find it unaided. -/
instance enoughInjectives_presheaf {C : Type u} [SmallCategory C] :
    EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  Stacks.CechSite.presheafEnoughInjectives.{u, u, u} (C := C)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] {U : C}
  (E : PreZeroHypercover.{u} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- The inclusion `i : Ab(C) ⥤ PAb(C)` of abelian sheaves into abelian presheaves, the first
functor of the composition whose Grothendieck spectral sequence is [Stacks, Tag 03OW]. -/
noncomputable abbrev sheafIncl : Sheaf J AddCommGrpCat.{u} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  sheafToPresheaf J AddCommGrpCat.{u}

/-- Degree-zero Čech cohomology `Ȟ⁰(𝒰, -) : PAb(C) ⥤ Ab` of the covering family `𝒰 = E`, the
second functor of the composition whose Grothendieck spectral sequence is [Stacks, Tag 03OW].
This is `Stacks.CechSite.cechCohomologyZeroFunctor` at the universes of a small site. -/
noncomputable abbrev cechZeroFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  Stacks.CechSite.cechCohomologyZeroFunctor.{u, u, u, u} E

/-- Degree-zero Čech cohomology is left exact: this is the degree-zero part of the Čech
cohomology δ-functor of [Stacks, Tag 03AR], and the degree-zero part of any cohomological
δ-functor preserves finite limits. -/
instance preservesFiniteLimits_cechZeroFunctor :
    PreservesFiniteLimits (cechZeroFunctor E) :=
  Stacks.Cohomology.CechDerived.preservesFiniteLimits_functor_zero _

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **The acyclicity input of [Stacks, Tag 03OW]**, from [Stacks, Tag 03AW] and
[Stacks, Tag 03AU].  The underlying abelian presheaf `i(I)` of an injective abelian sheaf `I` is
right acyclic for `Ȟ⁰(𝒰, -)`: by [Stacks, Tag 015C] right acyclicity for a left exact functor is
the vanishing of all its higher right derived functors, those are Čech cohomology by
[Stacks, Tag 03AU], and positive-degree Čech cohomology of an injective abelian sheaf vanishes
by [Stacks, Tag 03AW].

This is the hypothesis `hFG` of the Grothendieck spectral sequence of [Stacks, Tag 015N], and
it is the only thing [Stacks, Tag 03OW] needs beyond that general machinery. -/
theorem rightAcyclic_cechCohomologyZero_sheafToPresheaf_obj
    (I : Sheaf J AddCommGrpCat.{u}) [Injective I] :
    (cechZeroFunctor E).rightAcyclic ((sheafIncl J).obj I) := by
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (cechZeroFunctor E) _).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = ((m + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  exact IsZero.of_iso
    (Stacks.CechSite.injective_sheaf_cechCohomology_isZero.{u, u, u, u} E I (m + 1) m.succ_pos)
    ((Stacks.CechSite.cechCohomologyIsoRightDerivedPlus.{u, u, u, u} E (m + 1)).app I.obj).symm

/-- **Stacks 03AY, objectwise, in the `ℤ`-indexed form.**  The value at an abelian sheaf `F` of
the `q`-th right derived functor of the inclusion `i : Ab(C) ⥤ PAb(C)` is the cohomology
presheaf `H^q(F) : V ↦ H^q(V, F)`.

This is `Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf` composed with the comparison
of the two indexings of the right derived functors; it is what turns the second page of the
Grothendieck spectral sequence into the second page [Stacks, Tag 03OW] states. -/
noncomputable def rightDerivedPlus_sheafToPresheaf_obj_iso_cohomologyPresheaf
    (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
    ((sheafIncl J).rightDerivedPlus (q : ℤ)).obj F ≅ F.cohomologyPresheaf q :=
  ((Stacks.DerivedIndexing.rightDerivedIso (sheafIncl J) q).app F).symm ≪≫
    Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf J F q

/-- **Stacks Project, Tag 03OW, the spectral sequence.**  For a covering family `𝒰 = E` of an
object `U` of a site `C` and an abelian sheaf `F`, the Grothendieck spectral sequence of the
composition `Ab(C) --i--> PAb(C) --Ȟ⁰(𝒰,-)--> Ab` of [Stacks, Tag 03OX]: a cohomological
spectral sequence with

```
E₂^{p,q} ≅ R^p Ȟ⁰(𝒰, R^q i(F))
```

which abuts to `R^{p+q}(Ȟ⁰(𝒰, -) ∘ i)(F)`.

The second page is identified in the shape [Stacks, Tag 03OW] states it in
`exists_cechToCohomology_spectralSequence_pageTwo`. -/
theorem exists_cechToCohomology_spectralSequence (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ S : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℤ, Nonempty ((S.page 2 zero_le_two).X (p, q) ≅
        ((cechZeroFunctor E).rightDerivedPlus p).obj
          (((sheafIncl J).rightDerivedPlus q).obj F))) ∧
      SpectralSequence.AbutsTo S
        (fun n => (((sheafIncl J) ⋙ cechZeroFunctor E).rightDerivedPlus n).obj F) := by
  obtain ⟨K, hrest⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
    (sheafIncl J) (cechZeroFunctor E)
    (fun I hI => by
      have := hI
      exact rightAcyclic_cechCohomologyZero_sheafToPresheaf_obj J E I)
    ((DerivedCategory.Plus.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).obj F)
  obtain ⟨S, -, hE₂, habuts⟩ :=
    hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  exact ⟨S, hE₂, habuts⟩

/-- **Stacks Project, Tag 03OW: the Čech-to-cohomology spectral sequence, with its second
page.**  For a covering family `𝒰 = E` of an object `U` of a site `C` and an abelian sheaf `F`
there is a cohomological spectral sequence whose second page is

```
E₂^{p,q} ≅ Ȟ^p(𝒰, H^q(F)),
```

the Čech cohomology of the covering with coefficients in the cohomology presheaves
`H^q(F) : V ↦ H^q(V, F)`, and which abuts to `R^{p+q}(Ȟ⁰(𝒰, -) ∘ i)(F)`.

The abutment is the cohomology of the right derived functor of the composite
`Ȟ⁰(𝒰, -) ∘ i`, which is the group [Stacks, Tag 03OW] calls `H^{p+q}(U, F)`; the identification
of the two is **not** part of this statement, which is why the tag carries a clause.  See the
implementation notes of this file. -/
@[stacks 03OW "the spectral sequence and its second page",
  sga "4 V 7.4.0" "Čech covering case",
  sga "4 V 3.2" "R = sieve of a family"]
theorem exists_cechToCohomology_spectralSequence_pageTwo (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ S : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℕ, Nonempty ((S.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        Stacks.CechSite.cechCohomology E (F.cohomologyPresheaf q) p)) ∧
      SpectralSequence.AbutsTo S
        (fun n => (((sheafIncl J) ⋙ cechZeroFunctor E).rightDerivedPlus n).obj F) := by
  obtain ⟨S, hE₂, habuts⟩ := exists_cechToCohomology_spectralSequence J E F
  refine ⟨S, fun p q => ?_, habuts⟩
  obtain ⟨e⟩ := hE₂ (p : ℤ) (q : ℤ)
  refine ⟨e ≪≫ ?_⟩
  refine ((Stacks.CechSite.cechCohomologyIsoRightDerivedPlus.{u, u, u, u} E p).app
    (((sheafIncl J).rightDerivedPlus (q : ℤ)).obj F)).symm ≪≫ ?_
  exact (Stacks.CechSite.cechComplexFunctor E ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
    (rightDerivedPlus_sheafToPresheaf_obj_iso_cohomologyPresheaf J F q)

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **The abutment of [Stacks, Tag 03OW], objectwise in degree zero.**  For a covering family
`𝒰 = E` of `U` the composite `Ȟ⁰(𝒰, -) ∘ i` agrees, at every abelian sheaf `F`, with the
sections of `F` over `U`.  This is [Stacks, Tag 03AW] degree zero
(`Stacks.CechSite.cechCohomology_zero_iso`) read through the identification of the degree-zero
part of the Čech δ-functor of [Stacks, Tag 03AR] with degree-zero Čech cohomology.

This pins down precisely what is still owed for the abutment of
`exists_cechToCohomology_spectralSequence_pageTwo` to read `H^{p+q}(U, F)`: the composite
`i ⋙ Ȟ⁰(𝒰, -)` is objectwise the sections functor `F ↦ F(U)`, and what is missing is that the
comparison is **natural** in `F`, which is what would let the right derived functors of the two
be identified.  The isomorphism here is `Nonempty` because
`Stacks.CechSite.cechCohomology_zero_iso` is: it is produced from
`Stacks.CechSite.cechCohomologyZeroEquiv`, for which no naturality in the presheaf is proved. -/
theorem nonempty_cechZeroFunctor_sheafToPresheaf_obj_iso_sections
    (hE : E.sieve₀ ∈ J U) (F : Sheaf J AddCommGrpCat.{u}) :
    Nonempty (((sheafIncl J) ⋙ cechZeroFunctor E).obj F ≅ F.obj.obj (op U)) := by
  obtain ⟨e⟩ := Stacks.CechSite.cechCohomology_zero_iso.{u, u, u, u} J E hE F
  exact ⟨(eqToIso ((Stacks.CechSite.cechCohomologyDeltaFunctor.{u, u, u, u} E).2 0)).app F.obj
    ≪≫ e⟩

end Stacks.CechComparison

end
