module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeAbelianDegreewise
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology

/-!
# Naming the comparison map, and [Stacks, Tag 07MU] transported along a named one

`SmallSite/BaseChangeAbelianDegreewise.lean` reduces [Stacks, Tag 07MU] to the conjunction of
`...SmallSite.NegativeDegreeVanishing07MU` and the assertion that one explicit map of abelian
groups

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(Cris(X/S), abelianSheaf F)`

— namely `...SmallSite.abelianBaseChangeCohomologyMap` — is an isomorphism for every `j : ℕ`, and
records that the de Rham computation [Stacks, Tag 07LG] **cannot discharge that assertion in the
shape in which it is stated**.  The reason is not a universe or a hypothesis mismatch: the target
of the degree-`j` clause is already *literally* the object `(cohomologyFunctor S j).obj
(abelianSheaf F)` that [Stacks, Tag 07LG] computes.  The reason is that
`...SmallSite.Computes07LG` concludes

`Nonempty (H^j(M ⊗^∧_D Ω^*_D) ≅ (cohomologyFunctor S j).obj (abelianSheaf F))`,

the *mere existence* of an isomorphism, and the existence of an isomorphism between two groups
says nothing whatever about whether a **given** map between them is one.  That `Nonempty` is not
an accident of `Computes07LG`: it is inherited from `...SmallSite.ComputesCohomology`, the
conclusion of [Stacks, Tag 07JN], which is `Nonempty`-valued for the same reason, and the chain
that proves [Stacks, Tag 07JN] passes through `Nonempty` at every step
(`...SmallSite.Cech.IsCompletedSiteComparison` and
`...SmallSite.nonempty_addEquiv_sheafH_homology_sectionsComplex`).

This module supplies the shape that *can* discharge it, and measures exactly what the new shape
costs.  Four things are done.

## Comparison systems as carried data

For the conclusion of [Stacks, Tag 07JN] and for [Stacks, Tag 07LG] alike, the fix is to carry
the comparison as **data** — a family of maps — and to assert invertibility of the carried
family, which is the idiom `...SmallSite.BaseChangeMap07MT` and
`...SmallSite.IsBaseChangeIso07MU` already use for the base change map (07MT) itself.  So

* `ComputesCohomologyMaps` is the type of families `γ j : H^j(M(•)) ⟶ H^j(Cris(X/S), F)` and
  `ComputesCohomologyVia` asserts that every `γ j` is an isomorphism;
* `Computes07LGMaps`, `Computes07LGIsos` and `Computes07LGVia` are the same three things for the
  de Rham complex of [Stacks, Tag 07LG].

`computesCohomology_iff_exists_computesCohomologyVia` and
`computes07LG_iff_exists_computes07LGVia` are the measurement: the predicate as the library
states it is *equivalent* to the existence of a carried family all of whose members are
isomorphisms.  So nothing is weakened and nothing is strengthened by moving to the carried shape
— what changes is that a **particular** family is named, and that is precisely the extra
information the degreewise form of [Stacks, Tag 07MU] needs and the `Nonempty` form does not
supply.  The two directions are `computesCohomology_of_computesCohomologyVia` and
`computes07LG_of_computes07LGVia`, and the converses go by choosing one isomorphism per degree.

What the carried shape buys over the `Nonempty` one is visible in
`computes07LGMapsComp`: two named comparison systems **compose** to a named comparison system,
and `computes07LGVia_computes07LGMapsComp` says the composite is invertible as soon as both
factors are.  This is the step that `Nonempty` destroys — one can compose two mere existences
into a mere existence, but the resulting map is then no longer any particular map, so it cannot
be compared with `abelianBaseChangeCohomologyMap`.  `computes07LGMapsComp` is the map-naming
form of `...SmallSite.computes07LG_of_sectionsComplexHomologyIso`, which composes the de Rham
comparison with [Stacks, Tag 07JN] and loses the map.

## The comparison of [Stacks, Tag 07JN] is canonical, not assumed

The `Nonempty`s of the chain quoted above sit only at the boundaries between the predicates,
and every isomorphism between those boundaries is a named `def`.  Each boundary now carries a
family-of-maps form beside its predicate, and composing them gives
`...SmallSite.computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison`, the comparison of
[Stacks, Tag 07JN] as a **map**, invertible in every degree under the tag's own two hypotheses
and nothing else.  So for the system `(X, T(n)_e, δ(n))` the existential of
`computesCohomology_iff_exists_computesCohomologyVia` is *discharged* —
`computesCohomologyVia_wholeSpaceSystem_of_isSurjectiveComparison` and
`exists_computesCohomologyVia_wholeSpaceSystem_of_isSurjectiveComparison` — and a consumer that
must recognise a given map as the comparison no longer has to assume one.

`computes07LGMapsOfSectionsComplexHom` is `computes07LGMapsComp` with its 07JN factor supplied
from that canonical family, so the only comparison [Stacks, Tag 07LG] still has to carry is the
double-complex one, `hcomp` of `...SmallSite.computes07LG_of_sectionsComplexHomologyIso`.

## [Stacks, Tag 07MU] transported along a named comparison system

Nothing about the transport is special to the de Rham complex, so it is done once for an
arbitrary family of objects `D : ℕ → AddCommGrpCat.{u + 1}` and an arbitrary named family of
isomorphisms `Γ j : D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)`:

* `transportedBaseChangeCohomologyMap` is `abelianBaseChangeCohomologyMap` read into `D j`
  through `Γ`;
* `TransportedDegreewiseBaseChangeIso07MU` is the resulting form of the tag;
* `isBaseChangeIso07MU_iff_transportedDegreewise` is an **iff** with
  `...SmallSite.IsBaseChangeIso07MU` — so the transport is not a weakening, the seven conditions
  are passed through unchanged, and no hypothesis is added.

## [Stacks, Tag 07MU] in de Rham cohomology

`DeRhamDegreewiseBaseChangeIso07MU` is that transported form at `D j` the degree-`j` cohomology
of `M ⊗^∧_D Ω^*_D` and `Γ` a carried comparison system for [Stacks, Tag 07LG], and
`isBaseChangeIso07MU_iff_deRhamDegreewise` is its **iff** with the tag.  This is step four of the
source's Hints made statable: the degree-`j` clause of [Stacks, Tag 07MU] becomes the assertion
that the base change map (07MT) is an isomorphism *on de Rham cohomology*, which is where the
source's computation happens.

## [Stacks, Tag 07MU] in the cosimplicial complex of [Stacks, Tag 07JN]

The last section does the same with a comparison system that is **not** carried.  Unlike
[Stacks, Tag 07LG], [Stacks, Tag 07JN] is proved —
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` carries
`@[stacks 07JN]` — so `wholeSpaceSystemCohomologyIso` extracts a named comparison from a proved
theorem, and `isBaseChangeIso07MU_iff_cosimplicialDegreewise` is an **iff** between the tag and
the assertion that the base change map (07MT) is an isomorphism onto the cohomology of the
source's own complex `M(0) → M(1) → M(2) → ⋯`.  Its hypotheses beyond the tag's are the
hypotheses of [Stacks, Tag 07JN] and nothing else.

That extraction also shows exactly where the obstruction now sits.  The comparison is a choice
out of a `Nonempty`, which is enough to state the clause and not enough to prove it; and making
it canonical is a *construction*, not a proof obligation, because every isomorphism in the chain
behind [Stacks, Tag 07JN] is already a named `def`:
`Crystalline.sheafHAddEquivPushforward_of_surjective`,
`...SmallSite.completedChaoticSheafOfPresheafIsoPushforward`,
`...SmallSite.sectionsComplexIsoPowerCechComplex` and, at the root,
`Stacks.Cohomology.nonempty_addEquiv_sheafH_homology_powerCechComplex` (which carries
`@[stacks 07JM]` and whose proof is an explicit composite of named isomorphisms).  It is only the
predicates between them that discard the name.

## What is and is not proved

[Stacks, Tag 07MU] is **not** proved here and no `@[stacks 07MU]` attribute is placed; nor is
[Stacks, Tag 07LG] proved, and no `@[stacks 07LG]` attribute is placed.  What is proved is that
the tag, transported along *any* named comparison system, is the same statement as the tag.

The hypotheses of the last two sections beyond those of `...SmallSite.IsBaseChangeIso07MU` are
**delimiters and are not removable here**, and each is recorded:

* `Γ`, a named comparison system of [Stacks, Tag 07LG] — the whole point of that section, and
  the thing `computes07LG_iff_exists_computes07LGVia` shows [Stacks, Tag 07LG] does not supply
  while remaining equivalent to its existence.  The cosimplicial section carries no such datum;
* `hF`, quasi-coherence of `F` on `Cris(X/S)` for the de Rham section and local
  quasi-coherence together with `CohomologyRestriction.IsSurjectiveComparison` for the
  cosimplicial one, needed to index a comparison system at `F`.  The seven conditions of the tag
  assume quasi-coherence of `F'` on `Cris(X'/S')`, not of `F` on `Cris(X/S)`; in the source `F`
  is the pullback of `F'` and quasi-coherence descends along it, but this library has no such
  descent, so the hypothesis is carried;
* `[IsAffine S.X]`, `[IsAffine S.S.scheme]` and `hp`, the standing hypotheses of
  [Stacks, Tag 07JN] which `...SmallSite.Computes07LG` carries too and which cannot be dropped
  from it (see its docstring).  They are the affine case the source's Mayer–Vietoris step
  reduces to, and that step still cannot be stated here:
  `Crystalline.GlobalCrystallineSituation.restrict` exists but nothing compares
  `...SmallSite.moduleULiftDerivedGlobalSections` across a restriction, so a carried
  `...SmallSite.BaseChangeMap07MT` has no restriction to an open.

The transport section itself carries none of these: its only datum beyond the tag's is `Γ`.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
-/

@[expose] public section

universe u uI wS wS' wA wA'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

namespace Crystalline

open DividedPowers

namespace GlobalCrystallineSituation.SmallSite

noncomputable section

/-! ### The conclusion of [Stacks, Tag 07JN] with its comparison map named -/

section Affine

variable {S : GlobalCrystallineSituation.{u}}

/-- **The type of a comparison system for the conclusion of [Stacks, Tag 07JN]**: a family of
maps `H^j(M(0) → M(1) → ⋯) ⟶ H^j(Cris(X/S), F)`, one for each degree.

`...SmallSite.ComputesCohomology` asserts that each of these two groups is *isomorphic* to the
other, which names no map.  A term of this type is a named map in each degree, and
`ComputesCohomologyVia` is the assertion about it that the tag's conclusion amounts to. -/
abbrev ComputesCohomologyMaps (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ∀ j : ℕ, (sectionsComplex T F.obj).homology j ⟶ (cohomologyFunctor S j).obj F

/-- **The conclusion of [Stacks, Tag 07JN] *via* a named comparison system**: the carried family
`γ` is an isomorphism in every degree.

This is `...SmallSite.ComputesCohomology` with the existential quantifier over isomorphisms
replaced by a carried family, in the idiom of `...SmallSite.IsBaseChangeIso07MU`.  It is not
stronger than the tag's conclusion as a statement *about the pair* `(T, F)` —
`computesCohomology_iff_exists_computesCohomologyVia` — but it is a statement about `γ`, and that
is what makes it usable against a given map. -/
def ComputesCohomologyVia (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (γ : ComputesCohomologyMaps T F) : Prop :=
  ∀ j : ℕ, IsIso (γ j)

/-- The isomorphism of degree `j` named by an invertible comparison system. -/
def ComputesCohomologyVia.iso {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} {γ : ComputesCohomologyMaps T F}
    (hγ : ComputesCohomologyVia T F γ) (j : ℕ) :
    (sectionsComplex T F.obj).homology j ≅ (cohomologyFunctor S j).obj F :=
  haveI := hγ j
  asIso (γ j)

/-- **A named invertible comparison system gives the conclusion of [Stacks, Tag 07JN]**: forget
the maps and keep the isomorphisms. -/
theorem computesCohomology_of_computesCohomologyVia
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} {γ : ComputesCohomologyMaps T F}
    (hγ : ComputesCohomologyVia T F γ) : ComputesCohomology T F :=
  fun j => ⟨hγ.iso j⟩

/-- **The conclusion of [Stacks, Tag 07JN] is exactly the existence of a named invertible
comparison system.**  So passing to the carried shape neither weakens nor strengthens the
statement about `(T, F)`; what it adds is a name for the map, which an existential over
isomorphisms cannot provide and which is what a statement about a *given* map needs. -/
theorem computesCohomology_iff_exists_computesCohomologyVia
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ComputesCohomology T F ↔
      ∃ γ : ComputesCohomologyMaps T F, ComputesCohomologyVia T F γ :=
  ⟨fun h => ⟨fun j => (h j).some.hom, fun j => (h j).some.isIso_hom⟩,
    fun ⟨_, hγ⟩ => computesCohomology_of_computesCohomologyVia hγ⟩

/-- **[Stacks, Tag 07JN] holds *via* the canonical comparison system.**  Under the tag's own two
hypotheses on the coefficient sheaf, the named map
`...SmallSite.computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison` — the composite of
the named isomorphisms of the Čech engine, the two transports and the Leray degeneration — is an
isomorphism in every degree.

This is what the carried shape was introduced for.  Before the comparison had a name,
`computesCohomology_iff_exists_computesCohomologyVia` could only say that the tag's conclusion
*amounts to* the existence of such a system; the system itself had to be assumed by any consumer
wanting to speak about a given map.  Here the existential is discharged. -/
theorem computesCohomologyVia_wholeSpaceSystem_of_isSurjectiveComparison
    [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    ComputesCohomologyVia (wholeSpaceSystem S hp) (abelianSheaf F)
      (computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F hF hM) :=
  isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F hF hM

/-- **The existential of `computesCohomology_iff_exists_computesCohomologyVia` is discharged for
the system and the coefficient sheaves of [Stacks, Tag 07JN].**  A consumer no longer has to
carry a comparison system for the tag as a hypothesis: there is one, and it is canonical. -/
theorem exists_computesCohomologyVia_wholeSpaceSystem_of_isSurjectiveComparison
    [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    ∃ γ : ComputesCohomologyMaps (wholeSpaceSystem S hp) (abelianSheaf F),
      ComputesCohomologyVia (wholeSpaceSystem S hp) (abelianSheaf F) γ :=
  ⟨_, computesCohomologyVia_wholeSpaceSystem_of_isSurjectiveComparison hp F hF hM⟩

end Affine

/-! ### [Stacks, Tag 07LG] with its comparison map named -/

section DeRham

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)
  (hsq : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero p Dr Om wedge deRham
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib)

/-- **The degree-`j` cohomology of the complex `M ⊗^∧_D Ω^*_D` of [Stacks, Tag 07LG]**, lifted to
the universe `u + 1` in which the crystalline cohomology of the chapter lives.  This is the
source of the comparison `...SmallSite.Computes07LG` speaks about, named so that maps into and
out of it can be written down. -/
def crystalDeRhamCohomology (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) (j : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
    ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
      (hsq F hF)).homology j)

/-- **The type of a comparison system for [Stacks, Tag 07LG]**: for each coefficient sheaf
satisfying the tag's hypothesis and each degree, a map

`H^j(M ⊗^∧_D Ω^*_D) ⟶ H^j(Cris(X/S), abelianSheaf F)`.

`...SmallSite.Computes07LG` asserts these two groups to be isomorphic and names no map. -/
abbrev Computes07LGMaps :=
  ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
    crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ⟶
      (cohomologyFunctor S j).obj (abelianSheaf F)

/-- **The type of a comparison system of [Stacks, Tag 07LG] whose members are isomorphisms**,
carried as data rather than asserted to exist.  `computes07LGIsosOfVia` builds one from an
invertible `Computes07LGMaps`, and `computes07LGMapsOfIsos` goes back. -/
abbrev Computes07LGIsos :=
  ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
    crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ≅
      (cohomologyFunctor S j).obj (abelianSheaf F)

/-- **[Stacks, Tag 07LG] *via* a named comparison system**: the carried family `γ` is an
isomorphism for every coefficient sheaf satisfying the tag's hypothesis and every degree.

By `computes07LG_iff_exists_computes07LGVia` this is equivalent, as a statement about the de Rham
data, to `...SmallSite.Computes07LG` itself; the difference is that it is a statement *about* a
named family, which is what the degreewise form of [Stacks, Tag 07MU] can consume and what the
`Nonempty` of the tag cannot provide. -/
def Computes07LGVia
    (γ : Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq) : Prop :=
  ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
    IsIso (γ F hF j)

/-- The underlying maps of a carried family of isomorphisms, and they are invertible by
construction: `computes07LGVia_computes07LGMapsOfIsos`. -/
def computes07LGMapsOfIsos
    (Γ : Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq) :
    Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  fun F hF j => (Γ F hF j).hom

/-- The maps underlying a carried family of isomorphisms are isomorphisms. -/
theorem computes07LGVia_computes07LGMapsOfIsos
    (Γ : Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq) :
    Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
      (computes07LGMapsOfIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq Γ) :=
  fun F hF j => (Γ F hF j).isIso_hom

/-- A named comparison system all of whose members are isomorphisms, read as a carried family of
isomorphisms. -/
def computes07LGIsosOfVia
    {γ : Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq}
    (hγ : Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq γ) :
    Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  fun F hF j =>
    haveI := hγ F hF j
    asIso (γ F hF j)

/-- **A named invertible comparison system gives [Stacks, Tag 07LG]**: forget the maps and keep
the isomorphisms. -/
theorem computes07LG_of_computes07LGVia
    {γ : Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq}
    (hγ : Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq γ) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  fun F hF j => ⟨computes07LGIsosOfVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
    hγ F hF j⟩

/-- **[Stacks, Tag 07LG] is exactly the existence of a named invertible comparison system.**

This is the measurement that the module exists to make.  The tag as the library states it is
`Nonempty`-valued, and this says that asking for it is asking for a carried family of maps all of
which are isomorphisms — no more and no less.  So replacing the tag by `Computes07LGVia` of a
carried `γ` weakens nothing and strengthens nothing about the de Rham data; what it changes is
that the comparison has a *name*, and a statement about a given map — such as the degree-`j`
clause of `...SmallSite.AbelianDegreewiseBaseChangeIso07MU`, or
`...SmallSite.DegreewiseBaseChangeIso07MU` before it — can only be discharged by a named one. -/
theorem computes07LG_iff_exists_computes07LGVia :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq ↔
      ∃ γ : Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq,
        Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq γ :=
  ⟨fun h => ⟨fun F hF j => (h F hF j).some.hom, fun F hF j => (h F hF j).some.isIso_hom⟩,
    fun ⟨_, hγ⟩ =>
      computes07LG_of_computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq hγ⟩

/-- **Two named comparison systems compose to a named one.**  Given a named comparison `δ` of the
de Rham complex of [Stacks, Tag 07LG] with the complex `M(0) → M(1) → ⋯` of
[Stacks, Tag 07JN], and a named comparison `γ` of the latter with crystalline cohomology, the
composite is a named comparison system for [Stacks, Tag 07LG].

**This is what the carried shape buys.**  The same composition at the level of the library's
`Nonempty` predicates is `...SmallSite.computes07LG_of_sectionsComplexHomologyIso`, and there the
resulting isomorphism is no particular map, so it cannot be compared with
`...SmallSite.abelianBaseChangeCohomologyMap`.  Here it can:
`computes07LGVia_computes07LGMapsComp` gives the invertibility of the composite from the
invertibility of the factors, and the composite is a map one can name. -/
def computes07LGMapsComp
    (δ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ⟶
        (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)
    (γ : ∀ F : SheafOfModules.{u} (structureSheaf S),
      ComputesCohomologyMaps (wholeSpaceSystem S hp) (abelianSheaf F)) :
    Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  fun F hF j => δ F hF j ≫ γ F j

/-- **The composite of two invertible named comparison systems is invertible.** -/
theorem computes07LGVia_computes07LGMapsComp
    (δ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ⟶
        (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)
    (γ : ∀ F : SheafOfModules.{u} (structureSheaf S),
      ComputesCohomologyMaps (wholeSpaceSystem S hp) (abelianSheaf F))
    (hδ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      IsIso (δ F hF j))
    (hγ : ∀ F : SheafOfModules.{u} (structureSheaf S),
      ComputesCohomologyVia (wholeSpaceSystem S hp) (abelianSheaf F) (γ F)) :
    Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
      (computes07LGMapsComp S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq δ γ) := by
  intro F hF j
  have := hδ F hF j
  have := hγ F j
  exact IsIso.comp_isIso

/-- **The comparison system of [Stacks, Tag 07LG] built on the canonical comparison of
[Stacks, Tag 07JN].**  This is `computes07LGMapsComp` with its second factor supplied rather
than assumed: given the bridges `hlqc` and `hsurj` from quasi-coherence on the site to the two
hypotheses of [Stacks, Tag 07JN], the named comparison
`...SmallSite.computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison` is available at
every coefficient sheaf, so only the double-complex comparison `δ` of
`...SmallSite.computes07LG_of_sectionsComplexHomologyIso` has to be carried.

That hypothesis `δ` is the one step this naming does *not* supply: in
`computes07LG_of_sectionsComplexHomologyIso` it appears as a hypothesis `Nonempty`, and here as
a named family taken as a hypothesis.  Everything after it is now a map with a name. -/
noncomputable def computes07LGMapsOfSectionsComplexHom
    (hlqc : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      IsLocallyQuasiCoherent F)
    (hsurj : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CohomologyRestriction.IsSurjectiveComparison F.val)
    (δ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ⟶
        (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j) :
    Computes07LGMaps S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  fun F hF j => δ F hF j ≫
    computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F (hlqc F hF)
      (hsurj F hF) j

/-- **That system is invertible as soon as the double-complex comparison is.**  The second
factor is an isomorphism by
`...SmallSite.isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison`, with
nothing assumed; so [Stacks, Tag 07LG] *via* a named system reduces to the single step the
source proves with the two spectral sequences of the double complex. -/
theorem computes07LGVia_computes07LGMapsOfSectionsComplexHom
    (hlqc : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      IsLocallyQuasiCoherent F)
    (hsurj : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CohomologyRestriction.IsSurjectiveComparison F.val)
    (δ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j ⟶
        (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)
    (hδ : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ),
      IsIso (δ F hF j)) :
    Computes07LGVia S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
      (computes07LGMapsOfSectionsComplexHom S A Dr g Om der p dx wedge deRham hleib hp R h07IT
        hsq hlqc hsurj δ) := by
  intro F hF j
  have := hδ F hF j
  have := isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F
    (hlqc F hF) (hsurj F hF) j
  exact IsIso.comp_isIso

end DeRham

/-! ### [Stacks, Tag 07MU] transported along a named comparison system -/

section Transport

variable {S S' : GlobalCrystallineSituation.{u}} [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The base change map (07MT) in degree `j`, read into a carried family of objects.**

`...SmallSite.abelianBaseChangeCohomologyMap` goes into `H^j(Cris(X/S), abelianSheaf F)`.  Given
a named family of isomorphisms `Γ j : D j ≅ H^j(Cris(X/S), abelianSheaf F)` — the shape a
comparison system of [Stacks, Tag 07LG] has, by `Computes07LGIsos` — this is the same map read
into `D j`.  It is the given `φ` and nothing else. -/
def transportedBaseChangeCohomologyMap (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) (j : ℕ) :
    (forgetBaseAction S).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
          (derivedBaseChangeTensorGlobalSections f F')) ⟶
      D j :=
  abelianBaseChangeCohomologyMap f φ j ≫ (Γ j).inv

/-- **Transporting the degree-`j` clause along a named comparison system changes nothing.**  The
transported map differs from `...SmallSite.abelianBaseChangeCohomologyMap` by an isomorphism, so
one is invertible exactly when the other is. -/
theorem isIso_transportedBaseChangeCohomologyMap_iff (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) (j : ℕ) :
    IsIso (transportedBaseChangeCohomologyMap f φ Γ j) ↔
      IsIso (abelianBaseChangeCohomologyMap f φ j) := by
  rw [transportedBaseChangeCohomologyMap, isIso_comp_right_iff]

/-- **[Stacks, Tag 07MU] transported along a named comparison system**: under the seven conditions
of the remark, the base change map (07MT) induces an isomorphism

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ D j`

for every `j : ℕ`, and `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology in negative degrees.

The hypothesis block is that of `...SmallSite.IsBaseChangeIso07MU`, condition for condition and
in the same order, and `isBaseChangeIso07MU_iff_transportedDegreewise` is the machine check that
this is the tag.  The only datum beyond the tag's is the carried `Γ`; no condition is added. -/
def TransportedDegreewiseBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) : Prop :=
  IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
    F'.IsQuasicoherentOnSite → IsSheafCrystal F' →
      QuasiCompact S'.toClosedFiber → QuasiSeparated S'.toClosedFiber →
        IsPullback g S.toClosedFiber S'.toClosedFiber
            (DividedPowerScheme.closedFiberMap f) →
          IsFlatModule S' F' →
            AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber →
              AlgebraicGeometry.TorIndependent S'.toClosedFiber
                  (DividedPowerScheme.closedFiberMap f) →
                (∀ j : ℕ, IsIso (transportedBaseChangeCohomologyMap f φ Γ j)) ∧
                  ∀ n : ℤ, n < 0 →
                    IsZero ((DerivedCategory.homologyFunctor
                        (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).obj
                      (derivedBaseChangeTensorGlobalSections f F'))

/-- **The abelian degreewise form of [Stacks, Tag 07MU] and its transport along a named
comparison system are the same statement.**  Degree by degree the two clauses differ by the
isomorphism `Γ j`, which can neither create nor destroy invertibility, and the negative-degree
clause is untouched. -/
theorem abelianDegreewiseBaseChangeIso07MU_iff_transported (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) :
    AbelianDegreewiseBaseChangeIso07MU f g F' F φ ↔
      TransportedDegreewiseBaseChangeIso07MU f g F' F φ Γ := by
  simp only [AbelianDegreewiseBaseChangeIso07MU, TransportedDegreewiseBaseChangeIso07MU,
    isIso_transportedBaseChangeCohomologyMap_iff]

/-- **[Stacks, Tag 07MU] is its transport along any named comparison system, and nothing else.**

Composing `...SmallSite.isBaseChangeIso07MU_iff_abelianDegreewise` with
`abelianDegreewiseBaseChangeIso07MU_iff_transported`.  So the whole content of the tag is that
the base change map (07MT) is an isomorphism onto a *named* model `D j` of
`H^j(Cris(X/S), abelianSheaf F)` in every degree `j : ℕ`, together with the negative-degree
vanishing; and the choice of named model is free.  This is not a proof of the tag — see the
module documentation. -/
theorem isBaseChangeIso07MU_iff_transportedDegreewise (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) {D : ℕ → AddCommGrpCat.{u + 1}}
    (Γ : ∀ j : ℕ, D j ≅ (cohomologyFunctor S j).obj (abelianSheaf F)) :
    IsBaseChangeIso07MU f g F' F φ ↔
      TransportedDegreewiseBaseChangeIso07MU f g F' F φ Γ :=
  (isBaseChangeIso07MU_iff_abelianDegreewise f g F' F φ).trans
    (abelianDegreewiseBaseChangeIso07MU_iff_transported f g F' F φ Γ)

end Transport

/-! ### [Stacks, Tag 07MU] in the de Rham cohomology of [Stacks, Tag 07LG] -/

section DeRhamTransport

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)
  (hsq : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero p Dr Om wedge deRham
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib)
  {S' : GlobalCrystallineSituation.{u}} [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The base change map (07MT) in degree `j`, as a map into de Rham cohomology**

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(M ⊗^∧_D Ω^*_D)`,

for `Γ` a carried comparison system of [Stacks, Tag 07LG].  This is
`transportedBaseChangeCohomologyMap` at the de Rham model of
`H^j(Cris(X/S), abelianSheaf F)`. -/
def deRhamBaseChangeCohomologyMap
    (Γ : Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq)
    (f : S.S ⟶ S'.S) {F' : SheafOfModules.{u} (structureSheaf S')}
    {F : SheafOfModules.{u} (structureSheaf S)} (φ : BaseChangeMap07MT f F' F)
    (hF : F.IsQuasicoherentOnSite) (j : ℕ) :
    (forgetBaseAction S).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
          (derivedBaseChangeTensorGlobalSections f F')) ⟶
      crystalDeRhamCohomology S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq F hF j :=
  transportedBaseChangeCohomologyMap f φ (fun j => Γ F hF j) j

/-- **[Stacks, Tag 07MU] in the de Rham cohomology of [Stacks, Tag 07LG]**: under the seven
conditions of the remark, the base change map (07MT) induces an isomorphism

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(M ⊗^∧_D Ω^*_D)`

for every `j : ℕ`, and `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology in negative degrees.

This is step four of the source's Hints written down: the target of the degree-`j` clause is now
the cohomology of the complex the source computes with.  The hypothesis block is that of
`...SmallSite.IsBaseChangeIso07MU`, condition for condition and in the same order, and
`isBaseChangeIso07MU_iff_deRhamDegreewise` is the machine check that this is the tag; the data
beyond the tag's are the carried comparison system `Γ`, the quasi-coherence `hF` needed to index
it at `F`, and the affine standing hypotheses of [Stacks, Tag 07JN], all of them delimiters
recorded in the module documentation. -/
def DeRhamDegreewiseBaseChangeIso07MU
    (Γ : Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq)
    (f : S.S ⟶ S'.S) (gX : S.X ⟶ S'.X) (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S)) (φ : BaseChangeMap07MT f F' F)
    (hF : F.IsQuasicoherentOnSite) : Prop :=
  TransportedDegreewiseBaseChangeIso07MU f gX F' F φ (fun j => Γ F hF j)

/-- **[Stacks, Tag 07MU] is the de Rham degreewise statement, and nothing else.**

The transport of the tag along a carried comparison system of [Stacks, Tag 07LG] is the tag, by
`isBaseChangeIso07MU_iff_transportedDegreewise`.  So the whole content of [Stacks, Tag 07MU],
once a comparison system for [Stacks, Tag 07LG] is named, is that the base change map (07MT) is
an isomorphism onto the de Rham cohomology of `M ⊗^∧_D Ω^*_D` in every degree `j : ℕ`, together
with the negative-degree vanishing of `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A`.

**This is not a proof of the tag.**  What it measures is that the obstruction recorded in
`SmallSite/BaseChangeAbelianDegreewise.lean` — that [Stacks, Tag 07LG] as stated cannot discharge
the degree-`j` clause — is removed by naming the comparison and by nothing else:
`computes07LG_iff_exists_computes07LGVia` shows that naming it neither weakens nor strengthens
[Stacks, Tag 07LG], and here the named version meets the tag exactly. -/
theorem isBaseChangeIso07MU_iff_deRhamDegreewise
    (Γ : Computes07LGIsos S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq)
    (f : S.S ⟶ S'.S) (gX : S.X ⟶ S'.X) (F' : SheafOfModules.{u} (structureSheaf S'))
    (F : SheafOfModules.{u} (structureSheaf S)) (φ : BaseChangeMap07MT f F' F)
    (hF : F.IsQuasicoherentOnSite) :
    IsBaseChangeIso07MU f gX F' F φ ↔
      DeRhamDegreewiseBaseChangeIso07MU S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
        Γ f gX F' F φ hF :=
  isBaseChangeIso07MU_iff_transportedDegreewise f gX F' F φ (fun j => Γ F hF j)

end DeRhamTransport

/-! ### [Stacks, Tag 07MU] in the cosimplicial complex of [Stacks, Tag 07JN] -/

section CosimplicialTransport

variable {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **A named comparison system for the complex `M(0) → M(1) → M(2) → ⋯`, from the proved
[Stacks, Tag 07JN].**

Unlike `Computes07LGIsos`, this is not carried: it is extracted from
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison`, which is proved and
carries `@[stacks 07JN]`.  The extraction is a choice — the tag's conclusion is
`Nonempty`-valued, so it determines no particular isomorphism — and that is exactly the point of
this module: a choice is enough to *state* the degree-`j` clause of [Stacks, Tag 07MU] against
the source's complex (`isBaseChangeIso07MU_iff_cosimplicialDegreewise` below holds for any named
system at all), and it is not enough to *prove* it, which would need the comparison to be
compatible with change of divided power base and so to be canonical. -/
def wholeSpaceSystemCohomologyIso (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  (computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison hp F hF hM j).some

/-- **[Stacks, Tag 07MU] in the cohomology of the complex `M(0) → M(1) → M(2) → ⋯`**: under the
seven conditions of the remark, the base change map (07MT) induces an isomorphism

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(M(0) → M(1) → M(2) → ⋯)`

for every `j : ℕ`, and `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology in negative degrees.

This is `TransportedDegreewiseBaseChangeIso07MU` along the comparison system of
`wholeSpaceSystemCohomologyIso`, so the model of `H^j(Cris(X/S), abelianSheaf F)` it is stated
against comes from a **proved** tag and not from a carried hypothesis.  The hypotheses beyond
those of `...SmallSite.IsBaseChangeIso07MU` are exactly the hypotheses of
[Stacks, Tag 07JN] — `[IsAffine S.X]`, `[IsAffine S.S.scheme]`, `hp`, `hF` and `hM`, all of them
named propositions of this library — and they are delimiters: they are what makes the comparison
exist at all, and the affine ones are the case the source's Mayer–Vietoris step reduces to, which
cannot yet be stated here. -/
def CosimplicialDegreewiseBaseChangeIso07MU (f : S.S ⟶ S'.S) (gX : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) : Prop :=
  TransportedDegreewiseBaseChangeIso07MU f gX F' F φ
    (wholeSpaceSystemCohomologyIso hp F hF hM)

/-- **[Stacks, Tag 07MU] is the cosimplicial degreewise statement, and nothing else.**

An instance of `isBaseChangeIso07MU_iff_transportedDegreewise` at the comparison system that
[Stacks, Tag 07JN] provides.  So, over an affine situation and for a coefficient sheaf
satisfying the two hypotheses of that tag, the whole content of [Stacks, Tag 07MU] is that the
base change map (07MT) is an isomorphism onto the cohomology of the source's own complex
`M(0) → M(1) → M(2) → ⋯` in every degree `j : ℕ`, together with the negative-degree vanishing.

**This is not a proof of [Stacks, Tag 07MU]**, and it is where the obstruction is now located
precisely: the comparison of `wholeSpaceSystemCohomologyIso` is a choice out of a
`Nonempty`, so no square involving it commutes by anything proved here, and the degree-`j` clause
is a statement about a given map.  Making the comparison canonical is a construction and not a
proof obligation — every isomorphism in the chain that proves [Stacks, Tag 07JN] is already a
named `def` (down to `Stacks.Cohomology.nonempty_addEquiv_sheafH_homology_powerCechComplex`,
which carries `@[stacks 07JM]` and whose proof is an explicit composite), and it is only the
predicates between them that discard the name. -/
theorem isBaseChangeIso07MU_iff_cosimplicialDegreewise (f : S.S ⟶ S'.S) (gX : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    IsBaseChangeIso07MU f gX F' F φ ↔
      CosimplicialDegreewiseBaseChangeIso07MU hp f gX F' F φ hF hM :=
  isBaseChangeIso07MU_iff_transportedDegreewise f gX F' F φ
    (wholeSpaceSystemCohomologyIso hp F hF hM)

end CosimplicialTransport

end

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
