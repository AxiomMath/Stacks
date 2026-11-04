module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiHomAmalgamation
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

/-!
# Descent of quasi-coherent sheaves along an open covering

Stacks 023E is the Zariski case of Stacks 023T: for an open covering `S = ⋃ U i` every descent
datum on quasi-coherent sheaves for the family `U i → S` is effective, and *moreover* the functor
from the quasi-coherent `𝒪_S`-modules to the descent data for that family is fully faithful.

The `moreover` half is proved here with no hypothesis, for an arbitrary Zariski covering family.
It is the Zariski prestack property of the pullback pseudofunctor,
`AlgebraicGeometry.isPrestackFor_zariski`, carried across the two inclusions of full
subcategories by `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful`.

The effectivity half is reduced to a single statement about *arbitrary* sheaves of modules, named
`AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens`: that
`CategoryTheory.Pseudofunctor.toDescentData` of the pullback pseudofunctor is essentially
surjective for every covering by open subschemes.  The reduction needs the other input of the
source's proof — that being quasi-coherent is a local property, Modules Definition 01BE — which
is proved here as `AlgebraicGeometry.isQuasicoherent_of_zariskiCovering`.  The named statement
`AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens` is proved, by gluing, in
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleDescentEffective.lean`, which also carries
the resulting unconditional effectivity assertion.

## Main results

* `AlgebraicGeometry.isQuasicoherent_of_restrict_openCover`: a sheaf of modules whose restrictions
  to the members of an open covering by open subschemes are quasi-coherent is quasi-coherent.
* `AlgebraicGeometry.isQuasicoherent_of_zariskiCovering`: the same for an arbitrary Zariski
  covering family, phrased with pullback — **quasi-coherence descends along an open covering**.
* `AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor_zariski`: **Stacks 023E, the
  `moreover` assertion** — for every Zariski covering family the functor from the quasi-coherent
  `𝒪_S`-modules to the descent data is fully faithful, with no hypothesis.
* `AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens`: the object-level Zariski stack property
  of the pullback pseudofunctor, as a named `Prop`; it is proved by gluing, downstream of this
  file, as `AlgebraicGeometry.zariskiEssSurjToDescentDataOpens`.
* `AlgebraicGeometry.essSurj_toDescentData_zariski`: that one statement, which is about a covering
  by open subschemes indexed in `Type u`, already gives essential surjectivity for an arbitrary
  Zariski covering family in an arbitrary index universe.
* `AlgebraicGeometry.isEffective_of_zariskiEssSurjToDescentDataOpens`: **the effectivity assertion
  of Stacks 023E over that one statement alone** — every quasi-coherent descent datum for a
  Zariski covering family is effective.

## Implementation notes

Locality of quasi-coherence is proved through
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`, which wants an open
covering of `S` whose members carry a global presentation of the restricted module.  The covering
used is the family of affine opens of `S` that are contained in some member of the given covering;
these cover `S` because the affine opens are a basis, and on each of them the restriction of the
module is a restriction of an already quasi-coherent restriction, so
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec` manufactures the
presentation.

A general Zariski covering family is reduced to a covering by open subschemes through
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`: the pullback of a module along `f i` and along the
inclusion of the open range of `f i` differ by pullback along an isomorphism, and pullback
preserves quasi-coherence (Stacks 01BG, `Stacks.Modules.isQuasicoherent_pullback`).

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

/-- Open subsets of a scheme such that every point lies in one of them have supremum `⊤`. -/
private theorem iSup_eq_top_of_forall_exists_mem {S : Scheme.{u}} {ι : Sort*} (W : ι → S.Opens)
    (h : ∀ x : S, ∃ i, x ∈ W i) : ⨆ i, W i = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr (h x)

/-- A Zariski covering family consists of open immersions whose ranges cover the scheme. -/
private theorem isOpenImmersion_and_exists_mem_range_of_mem_zariskiPrecoverage {S : Scheme.{u}}
    {I : Type*} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) :
    (∀ x : S, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, IsOpenImmersion (f i) := by
  simpa using hf

/-- **Quasi-coherence is a local property, Modules Definition 01BE.**  A sheaf of modules on a
scheme whose restrictions to the members of a covering by open subschemes are quasi-coherent is
quasi-coherent.

The covering fed to `Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`
is the family of affine opens contained in some member, which covers because the affine opens are
a basis. -/
public theorem isQuasicoherent_of_restrict_openCover {S : Scheme.{u}} (M : S.Modules)
    {ι : Type*} (W : ι → S.Opens) (hW : ⨆ i, W i = ⊤)
    (h : ∀ i, (M.restrict (W i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations M
    (fun V : {U : S.Opens // IsAffineOpen U ∧ ∃ i, U ≤ W i} ↦ (V : S.Opens)) ?_ fun V ↦ ?_
  · refine iSup_eq_top_of_forall_exists_mem _ fun x ↦ ?_
    have hx : x ∈ (⨆ i, W i) := hW ▸ trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hi
    exact ⟨⟨U, hU, i, hUW⟩, hxU⟩
  · obtain ⟨U, hU, hiW⟩ := V
    have hq : (M.restrict U.ι).IsQuasicoherent := by
      obtain ⟨i, hUi⟩ := hiW
      have h2 : ((M.restrict (W i).ι).restrict (S.homOfLE hUi)).IsQuasicoherent :=
        have := h i; inferInstance
      exact Stacks.Descent.isQuasicoherent_of_iso
        (((Scheme.Modules.restrictFunctorComp (S.homOfLE hUi) (W i).ι).app M).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr (S.homOfLE_ι hUi)).app M) h2
    exact (Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec
      hU.isoSpec _).some

/-- **Quasi-coherence descends along an open covering.**  If the pullbacks of a sheaf of modules
`M` on `S` to the members of a Zariski covering family of `S` are quasi-coherent, then `M` is
quasi-coherent.  This is the second input of the source's proof of Stacks 023E, the locality of
quasi-coherence of Modules Definition 01BE.

A member `f i : X i ⟶ S` of the family is the inclusion of its open range composed with an
isomorphism, so the pullback along the inclusion is a pullback of the pullback along `f i`, and
pullback preserves quasi-coherence by Stacks 01BG. -/
public theorem isQuasicoherent_of_zariskiCovering {S : Scheme.{u}} {I : Type*}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) (M : S.Modules)
    (h : ∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) : M.IsQuasicoherent := by
  have hu := isOpenImmersion_and_exists_mem_range_of_mem_zariskiPrecoverage hf
  have := hu.2
  refine isQuasicoherent_of_restrict_openCover M (fun i ↦ (f i).opensRange) ?_ fun i ↦ ?_
  · exact iSup_eq_top_of_forall_exists_mem _ hu.1
  · refine Stacks.Descent.isQuasicoherent_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback ((f i).opensRange).ι).app M).symm ?_
    refine Stacks.Descent.isQuasicoherent_of_iso
      ((Scheme.Modules.pullbackComp (f i).isoOpensRange.inv (f i)).app M ≪≫
        (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp (f i))).app M) ?_
    exact Stacks.Modules.isQuasicoherent_pullback (f i).isoOpensRange.inv _ (h i)

/-- **Stacks 023E, the `moreover` assertion, with no hypothesis.**  For every Zariski covering
family of a scheme `S` the functor from the quasi-coherent `𝒪_S`-modules to the descent data for
that family is fully faithful.

Stacks 023E makes two assertions in one statement — that every descent datum on quasi-coherent
sheaves for an open covering is **effective**, and *moreover* that this functor is **fully
faithful**; this declaration is the second.  The first is `AlgebraicGeometry.isEffective_zariski`,
in `StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleDescentEffective.lean`. -/
public theorem nonempty_fullyFaithful_canonicalDescentFunctor_zariski {S : Scheme.{u}}
    {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful
    ((Pseudofunctor.isPrestackFor_ofArrows_iff modulePullbackPseudofunctor f).mp
      (isPrestackFor_zariski S _ hf)).some

/-- **The object-level Zariski stack property**: for a covering of a scheme by open subschemes,
indexed in the scheme's own universe, `CategoryTheory.Pseudofunctor.toDescentData` of the pullback
pseudofunctor of sheaves of modules is essentially surjective.  This is the Zariski stack property
of `AlgebraicGeometry.modulePullbackPseudofunctor` at the level of objects; its morphism-level
counterpart is `AlgebraicGeometry.isPrestack_zariski`.

It is a statement about *arbitrary* sheaves of modules, hence strictly stronger than the
effectivity assertion of Stacks 023E, which is about quasi-coherent ones.  Its mathematical
content is the gluing of sheaves of modules along an open covering, which is
`Stacks.SheafOfModules.ModulesGlueData.glued` together with
`Stacks.SheafOfModules.ModulesGlueData.chartIso`.  The shape is exactly the one that glueing
datum has: a covering by open subschemes, indexed in `Type u`.  Passing from it to an arbitrary
Zariski covering family — a family of open immersions, jointly surjective, indexed in any
universe — is `AlgebraicGeometry.essSurj_toDescentData_zariski`.

It is stated here as a named `Prop` because the gluing that proves it is built on top of this
file; the proof is `AlgebraicGeometry.zariskiEssSurjToDescentDataOpens`, in
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleDescentEffective.lean`. -/
public abbrev ZariskiEssSurjToDescentDataOpens : Prop :=
  ∀ {S : Scheme.{u}} {ι : Type u} (W : ι → S.Opens), ⨆ i, W i = ⊤ →
    (modulePullbackPseudofunctor.toDescentData fun i ↦ (W i).ι).EssSurj

/-- The sieve generated by a family of open immersions is the sieve generated by the inclusions
of the open ranges that occur, *reindexed by those opens themselves*.  Reindexing this way puts
the index type in the universe of the scheme, which is what a glueing datum needs. -/
public lemma sieve_generate_opensRangeSet {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)] :
    Sieve.generate (Presieve.ofArrows X f) =
      Sieve.generate (Presieve.ofArrows
        (fun V : {V : S.Opens // ∃ i, (f i).opensRange = V} ↦ (V.1).toScheme)
        (fun V ↦ (V.1).ι)) := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro Y g ⟨i⟩
    exact ⟨_, (f i).isoOpensRange.hom, _,
      Presieve.ofArrows.mk (⟨(f i).opensRange, i, rfl⟩ :
        {V : S.Opens // ∃ i, (f i).opensRange = V}),
      Scheme.Hom.isoOpensRange_hom_ι (f i)⟩
  · rw [Sieve.generate_le_iff]
    rintro Y g ⟨V⟩
    obtain ⟨V, i, rfl⟩ := V
    exact ⟨_, (f i).isoOpensRange.inv, _, Presieve.ofArrows.mk i,
      Scheme.Hom.isoOpensRange_inv_comp (f i)⟩

/-- **From a covering by open subschemes to an arbitrary Zariski covering family.**  Granting
`AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens`, the functor
`CategoryTheory.Pseudofunctor.toDescentData` of the pullback pseudofunctor is essentially
surjective for *every* Zariski covering family, in every index universe.

The open ranges of the family, reindexed by the opens themselves, are a covering by open
subschemes indexed in `Type u` generating the same sieve
(`AlgebraicGeometry.sieve_generate_opensRangeSet`).  For it the functor is an equivalence —
essentially surjective by hypothesis, fully faithful by
`AlgebraicGeometry.isPrestackFor_zariski` — and being an equivalence depends only on the
generated sieve, by `CategoryTheory.Pseudofunctor.isStackFor_iff_of_sieve_eq`. -/
public theorem essSurj_toDescentData_zariski (hess : ZariskiEssSurjToDescentDataOpens.{u})
    {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) :
    (modulePullbackPseudofunctor.toDescentData f).EssSurj := by
  have hu := isOpenImmersion_and_exists_mem_range_of_mem_zariskiPrecoverage hf
  have := hu.2
  have hmem : ∀ x : S, ∃ V : {V : S.Opens // ∃ i, (f i).opensRange = V}, x ∈ V.1 := fun x ↦ by
    obtain ⟨i, hi⟩ := hu.1 x
    exact ⟨⟨(f i).opensRange, i, rfl⟩, hi⟩
  have hcov : ⨆ V : {V : S.Opens // ∃ i, (f i).opensRange = V}, V.1 = ⊤ :=
    iSup_eq_top_of_forall_exists_mem _ hmem
  have hpre : Presieve.ofArrows
      (fun V : {V : S.Opens // ∃ i, (f i).opensRange = V} ↦ (V.1).toScheme)
      (fun V ↦ (V.1).ι) ∈ Scheme.zariskiPrecoverage.{u} S := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun V ↦ inferInstance⟩
    obtain ⟨V, hV⟩ := hmem x
    obtain ⟨y, hy⟩ : x ∈ Set.range (V.1).ι.base := by rw [(V.1).range_ι]; exact hV
    exact ⟨V, y, hy⟩
  have hff := ((Pseudofunctor.isPrestackFor_ofArrows_iff modulePullbackPseudofunctor
    (fun V : {V : S.Opens // ∃ i, (f i).opensRange = V} ↦ (V.1).ι)).mp
      (isPrestackFor_zariski S _ hpre)).some
  have hEq : (modulePullbackPseudofunctor.toDescentData
      (fun V : {V : S.Opens // ∃ i, (f i).opensRange = V} ↦ (V.1).ι)).IsEquivalence :=
    { faithful := hff.faithful
      full := hff.full
      essSurj := hess (fun V : {V : S.Opens // ∃ i, (f i).opensRange = V} ↦ V.1) hcov }
  exact ((Pseudofunctor.isStackFor_ofArrows_iff modulePullbackPseudofunctor f).mp
    ((Pseudofunctor.isStackFor_iff_of_sieve_eq modulePullbackPseudofunctor
        (sieve_generate_opensRangeSet f)).mpr
      ((Pseudofunctor.isStackFor_ofArrows_iff modulePullbackPseudofunctor _).mpr hEq))).essSurj

/-- **The effectivity assertion of Stacks 023E, over
`AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens` alone.**  If
`CategoryTheory.Pseudofunctor.toDescentData` of the pullback pseudofunctor is essentially
surjective for every covering of a scheme by open subschemes indexed in the scheme's own
universe, then every quasi-coherent descent datum for an arbitrary Zariski covering family is
effective.

The descent of quasi-coherence that `Stacks.Descent.isEffective_of_essSurj` asks for is supplied
unconditionally by `AlgebraicGeometry.isQuasicoherent_of_zariskiCovering`, and the passage to an
arbitrary covering family by `AlgebraicGeometry.essSurj_toDescentData_zariski`, so this is the
whole assertion over that one hypothesis.  The hypothesis is discharged in
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleDescentEffective.lean`, and the
unconditional form is `AlgebraicGeometry.isEffective_zariski` there. -/
public theorem isEffective_of_zariskiEssSurjToDescentDataOpens
    (hess : ZariskiEssSurjToDescentDataOpens.{u}) {S : Scheme.{u}} {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S)
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  have := essSurj_toDescentData_zariski hess f hf
  Stacks.Descent.isEffective_of_essSurj
    (fun M hM ↦ isQuasicoherent_of_zariskiCovering f hf M hM) D

end AlgebraicGeometry

end
