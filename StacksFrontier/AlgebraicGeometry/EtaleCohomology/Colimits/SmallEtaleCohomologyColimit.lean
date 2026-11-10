module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystems
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# Étale cohomology of a directed limit of schemes, on the small étale sites (Stacks 09YQ)

Let `I` be a directed set, let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, let `c` be a limit cone with vertex
`X = lim X_i`, let `(F_i, φ_a)` be a system of abelian sheaves on the small étale sites of the
`X_i` in the sense of [Stacks, Tag 0EZL] — `Stacks.EtaleCohomology.EtaleSheafSystem` — and let
`𝒢` on the small étale site of `X` present `colim f_i^{-1}F_i`, with legs
`ι_i : f_i^{-1}F_i ⟶ 𝒢`. [Stacks, Tag 09YQ] (Étale Cohomology, Lemma 59.51.3) asserts that
`H^p(X, 𝒢)` is the filtered colimit of the `H^p(X_i, F_i)` for every `p ≥ 0`.

This file states that assertion on the **small étale sites** — the mainstream étale cohomology
`CategoryTheory.Sheaf.H` of this library, not the right-derived sections on the small *affine*
étale sites of `Stacks.EtaleCohomology.QcqsLimitCohomology` — and carries out the **dimension
shift**: the reduction of the statement in every degree to the degree-zero statement together
with a vanishing statement in positive degrees for systems of injectives.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyMapTo` — the map on étale cohomology attached to a
  morphism of schemes `k : Y ⟶ X` together with a map `u : k^{-1}A ⟶ B`: restriction along `k`
  (`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`) followed by the map induced on
  `Sheaf.H` by `u`. Both the cocone legs and the diagram maps of Stacks 09YQ are of this shape,
  and every naturality statement below is proved once, for it.
* `Stacks.EtaleCohomology.systemPullbackIsoInverseImage` — the comparison between the two
  inverse-image functors this development uses on abelian étale sheaves (see the implementation
  notes).
* `Stacks.EtaleCohomology.etaleCohomologyTransition` — the map
  `H^p(X_j, F_j) → H^p(X_i, F_i)` of the cohomology diagram of a system, along a transition
  `a : i ⟶ j` of the index.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg` — the cocone leg
  `H^p(X_i, F_i) → H^p(X, 𝒢)`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit` — **the statement of
  Stacks 09YQ in one degree**: the legs are jointly surjective, and a class killed by its leg is
  killed by a transition.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage` — the dévissage datum of the
  source's proof: an embedding of a system into a system of injectives, its quotient, and the
  induced short exact sequence on the limit.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyMapTo_comp_mk₀` and
  `Stacks.EtaleCohomology.etaleCohomologyMapTo_comp_extClass` — these maps commute with the maps
  induced by a morphism of sheaves and with the connecting map of a short exact sequence. They are
  the two naturality statements that make the long exact sequences of the levels and of the limit
  into one ladder, and they are read off the corresponding statements for restriction,
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_mk₀` and
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_extClass`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`
  — **the dimension shift.** Given the degree-zero statement for every presented system, the
  vanishing of `H^q(X, 𝒢)` for `q > 0` whenever the system is pointwise injective, and a dévissage
  datum for every presented system, the statement of Stacks 09YQ holds in every degree.

## What is a hypothesis here, and why

This file is internal machinery: the theorem it proves has hypotheses, and the tagged statement of
Stacks 09YQ — which must have none — is assembled elsewhere, once they are discharged. The
hypotheses are of three kinds.

*The two inputs being proved in parallel.* `H0` is the degree-zero statement, which is the
sections statement of [Stacks, Tag 09YN] transported to the small étale sites through the Čech
step of [Stacks, Tag 09YQ]; `HV` is the vanishing of `H^q(X, colim f_j^{-1}G_j)` in positive
degrees for a system `(G_j)` of injective abelian sheaves, which is where quasi-compactness and
quasi-separatedness of the levels, the affineness of the transitions and
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_smallEtaleSections_qcqs` ([Stacks, Tag
0739] on the small étale site) enter. Neither is proved here, and neither is needed for the
induction: the induction is exactly the implication this file supplies.

*The dévissage.* `Hdev` is [Stacks, Tag 0EXZ] — every system of abelian sheaves embeds in a
system of pointwise injective ones — together with the exactness of the formation of the limit
sheaf, which turns the levelwise short exact sequences into one on `X`. Tag 0EXZ is in this
library, as
`InverseSystemOfSites.AbelianSheafSystem.exists_mono_to_pointwise_injective` and
`InverseSystemOfFiniteSites.AbelianSheafSystem.exists_mono_to_pointwise_injective`, but for a
system of abelian sheaves on an `InverseSystemOfSites`, whose covering sieves are required to be
finitely generated ([Stacks, Tag 00VH]). The small étale site of a scheme is not such a site —
its coverings are arbitrary jointly surjective families of étale morphisms — so an
`EtaleSheafSystem` is not an instance of that notion and the library's Tag 0EXZ does not apply to
it. Carrying the construction of its proof across is a development in its own right, and it is a
hypothesis here rather than a hole in a proof.

**What `Hdev` now costs is that levelwise statement and nothing else.**
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage`, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleDevissage.lean`, builds a
`Devissage` for every presented system from
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasPointwiseInjectiveEmbeddings` — Tag 0EXZ for
systems on these sites, stated levelwise. The rest of the datum, which the paragraph above does
not separate out, is supplied there: the quotient system is the levelwise cokernel
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.quotientSystem`); the two colimit presentations
the datum demands of `mid` and `quot` exist by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_isColimitPresentation`; and the short
exact sequence on the limit comes from
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.mono_of_pointwise_mono`, the exactness of
filtered colimits. The device making the last two available is that a system, though not a
functor, *is* a functor into the Karoubi envelope of the sheaf category on the limit — see
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleKaroubiColimit.lean`, which
also shows that the identity law this structure omits costs nothing where the colimit is concerned.

*The cocone laws.* `PresentedSystem` carries two laws, `transition_comp` and `leg_transition`:
the transition maps on cohomology compose, and the legs are compatible with them. These are what
makes the data a cocone over a filtered diagram at all, and the colimit statement does not even
mean anything without them. They are fields rather than lemmas because the structure is stated
before they are available: deducing them from the cocycle condition of the system and from
`Cone.w` needs the composition law for restriction, `k₁^{-1}k₂^{-1} ≅ (k₂ ∘ k₁)^{-1}` transported
to `Ext` and matched against the constant-sheaf comparison of
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`, and
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` carries naturality statements in the sheaf
but no composition law in the morphism.

**Both laws are now proved**, for every system with a colimit presentation, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtalePresentedSystem.lean`: the
composition law is `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp`, which is exactly
the missing step, and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.presentedSystemOfIsColimitPresentation` builds
the `PresentedSystem`. So the quantifier `∀ E : PresentedSystem P` below is not a restriction on
the systems the dimension shift reaches.

*The presentation predicate.* `P` is the "`𝒢` is `colim f_i^{-1}F_i` with legs `ι`" condition,
carried as a parameter rather than defined. The source's hypothesis is a colimit of *sheaves* on
the limit site, and writing it down asks for the diagram `i ↦ f_i^{-1}F_i` as a functor on `I`,
which is exactly what is unavailable (see the implementation notes). Leaving it abstract costs
nothing: `H0` and `HV` are assumed only for systems satisfying it, the dévissage is required to
produce systems satisfying it, and a consumer instantiates `P` with whatever form of the
presentation hypothesis it has. Without it the theorem would be vacuous, `H0` being false for an
arbitrary `𝒢`.

## Implementation notes

**The colimit statement is elementwise.** `IsCohomologyColimit` says that the legs are jointly
surjective and that a class killed by its leg is killed by some transition. For a filtered index
category and coefficients in abelian groups that is precisely the assertion that the cocone is a
colimit cocone — it is how `CategoryTheory.Limits.Concrete` characterises filtered colimits of
abelian groups — so nothing is weakened. It is stated this way because the literal
`CategoryTheory.Limits.IsColimit` needs the cohomology groups to form a *functor* on `I`, and
they do not, on the nose: `EtaleSheafSystem` follows the source in imposing only the cocycle
condition and not the identity law (see
`Stacks.EtaleCohomology.directImageSystem_map_id`, which proves the identity law for the one
system of the development that satisfies it), and in any case base change along `𝟙 X` is the
functor `U ↦ U ×_X X` on the small étale site and not the identity functor, so
`etaleCohomologyTransition` at an identity index is not the identity map. This is the same
obstruction that made the weak-system form of [Stacks, Tag 09YP] in
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean` carry its
diagram as a *field* pinned by equations rather than construct it; there the strictness fields of
`InverseSystemOfFiniteSites` and the `map_id` field of its `AbelianSheafSystem` supply what is
missing, and the small étale sites have neither.

**Two inverse images.** `Stacks.EtaleCohomology.systemPullback`, which `EtaleSheafSystem` carries
its transitions along, is `CategoryTheory.Functor.sheafPullback` — the left adjoint of the direct
image, taken abstractly. `Stacks.EtaleCohomology.etaleAbelianInverseImage`, which the restriction
map on cohomology is built from, is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` — the same functor constructed as
a left Kan extension followed by sheafification, which is the form in which its left exactness is
available. `systemPullbackIsoInverseImage` is Mathlib's comparison
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso` between them, named here, and
`systemTransitionMap` is the transition of a system read through it.

**`conePi`.** The source of `c.π.app i` is `((Functor.const Iᵒᵖ).obj c.pt).obj i`, which is
`c.pt` definitionally but not at the transparency instance search uses, so the `HasSheafify` and
`HasExt` instances for the small étale site of `c.pt` are not found and the `Ext` machinery dies
in the signature on a `synthInstance` timeout. `conePi` is the projection with its source written
as `c.pt`, and it is used throughout instead.

**Universes.** Everything is at the coefficient universe `AddCommGrpCat.{u + 1}` and the `Ext`
universe `u + 1` for schemes in `Scheme.{u}`, which is the convention of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CohomologicalDimensionLimits.lean` and the first
universe in which the small étale site of a scheme has sheafification. Note that
`CategoryTheory.Sheaf.H'` is unusable on this site: Mathlib defines it only at the *hom* universe
of the site, which is `u`.

No `@[stacks]` attribute is placed. The statement of Tag 09YQ is here, but what is proved is the
implication from its two inputs; the tag goes on the theorem that discharges them.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-! ### The cohomology map attached to a morphism of schemes and a map of sheaves -/

section MapTo

variable {X Y : Scheme.{u}} (k : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The map on étale cohomology attached to a morphism of schemes and a map of sheaves.** Given
`k : Y ⟶ X`, an abelian sheaf `A` on the small étale site of `X`, one `B` on that of `Y` and a map
`w : k^{-1}A ⟶ B`, this is restriction along `k` followed by the map induced on cohomology by `w`.

Both ingredients of the cohomology cocone of [Stacks, Tag 09YQ] are of this shape: a leg is the
case `k = f_i` and `w = ι_i`, and a diagram map is the case `k = f_{ji}` and `w` the transition of
the system. Stating the naturality of the construction once, here, is what lets the dimension
shift treat the two uniformly. -/
def etaleCohomologyMapTo {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B) (p : ℕ) :
    Sheaf.H.{u + 1, u + 1} A p →+ Sheaf.H.{u + 1, u + 1} B p :=
  (Sheaf.H.map w p).comp (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p)

/-- The defining formula: the class is restricted along `k` and then composed with `w`. -/
theorem etaleCohomologyMapTo_apply {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k w p x =
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p x).comp (Ext.mk₀ w) (add_zero p) :=
  rfl

/-- **Naturality in the sheaf.** A square `k^{-1}φ ≫ w_B = w_A ≫ ψ` of sheaves gives a square of
the induced maps on cohomology. With `k` a projection of the limit cone this says that the cocone
legs commute with a morphism of systems, and with `k` a transition morphism that the diagram maps
do. -/
theorem etaleCohomologyMapTo_comp_mk₀
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : A ⟶ B)
    {A' B' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (wA : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ A')
    (wB : (etaleAbelianInverseImage.{u, u + 1} k).obj B ⟶ B') (ψ : A' ⟶ B')
    (hcomm : (etaleAbelianInverseImage.{u, u + 1} k).map φ ≫ wB = wA ≫ ψ) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k wB p (Sheaf.H.map φ p x) =
      Sheaf.H.map ψ p (etaleCohomologyMapTo k wA p x) := by
  rw [Sheaf.H.map_apply, etaleCohomologyMapTo_apply, etaleCohomologyMapTo_apply,
    Sheaf.H.map_apply, etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1},
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, hcomm]

/-- **Naturality in the connecting map.** A morphism from the inverse image of a short exact
sequence of abelian sheaves on `X` to a short exact sequence on `Y` makes these maps a morphism of
the two long exact sequences: they commute with the connecting maps. This is the engine of the
dimension shift. -/
theorem etaleCohomologyMapTo_comp_extClass
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    {T : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hT : T.ShortExact)
    (w : S.map (etaleAbelianInverseImage.{u, u + 1} k) ⟶ T)
    (p q : ℕ) (hpq : p + 1 = q) (z : Sheaf.H.{u + 1, u + 1} S.X₃ p) :
    etaleCohomologyMapTo k w.τ₁ q (z.comp hS.extClass hpq) =
      (etaleCohomologyMapTo k w.τ₃ p z).comp hT.extClass hpq := by
  rw [etaleCohomologyMapTo_apply, etaleCohomologyMapTo_apply,
    etaleCohomologyRestrictionMap_comp_extClass.{u, u + 1, u + 1} k hS p q hpq z,
    Ext.comp_assoc _ _ _ hpq (add_zero 1) (by omega),
    ShortComplex.ShortExact.extClass_naturality
      (hS.map_of_exact (etaleAbelianInverseImage.{u, u + 1} k)) hT w,
    ← Ext.comp_assoc _ _ _ (add_zero p) (zero_add 1) (by omega)]

end MapTo

/-! ### The transition maps of a system -/

section Transition

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]

/-- **The two inverse images agree.** `Stacks.EtaleCohomology.systemPullback`, the abstract left
adjoint of the direct image along a transition, is identified with
`Stacks.EtaleCohomology.etaleAbelianInverseImage`, its construction as a left Kan extension
followed by sheafification. This is Mathlib's comparison of left adjoints, named here because a
system of sheaves carries its transitions along the first and the restriction map on cohomology is
built from the second. -/
def systemPullbackIsoInverseImage {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullback D AddCommGrpCat.{u + 1} a ≅
      etaleAbelianInverseImage.{u, u + 1} (D.map a) :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange (D.map a))
    AddCommGrpCat.{u + 1} (smallEtaleTopology (D.obj j)) (smallEtaleTopology (D.obj i))

end Transition

section TransitionMaps

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]

/-- The transition map of a system of abelian étale sheaves, read as a map out of
`Stacks.EtaleCohomology.etaleAbelianInverseImage` rather than out of
`Stacks.EtaleCohomology.systemPullback`. -/
def systemTransitionMap (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj (F.obj j) ⟶ F.obj i :=
  (systemPullbackIsoInverseImage D a).inv.app (F.obj j) ≫ F.map a

/-- **The maps of the cohomology diagram of a system.** Along a transition `a : i ⟶ j` of the
index, the map `H^p(X_j, F_j) → H^p(X_i, F_i)`: restrict along the transition morphism
`D.map a : X_i ⟶ X_j` and then apply the transition of the system. -/
def etaleCohomologyTransition (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) (p : ℕ) :
    Sheaf.H.{u + 1, u + 1} (F.obj j) p →+ Sheaf.H.{u + 1, u + 1} (F.obj i) p :=
  etaleCohomologyMapTo (D.map a) (systemTransitionMap F a) p

end TransitionMaps

/-! ### Presented systems and the colimit statement -/

namespace SmallEtaleLimitCohomology

/-- **The projection of a cone to a level**, with its source written as `c.pt` rather than as
`((Functor.const Iᵒᵖ).obj c.pt).obj i`. The two are definitionally equal, but not at the
transparency typeclass inference uses, so with the second spelling the `HasSheafify` and `HasExt`
instances for the small étale site of the limit are not found and the signatures below fail on a
`synthInstance` timeout. -/
def conePi {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D) (i : Iᵒᵖ) :
    c.pt ⟶ D.obj i :=
  c.π.app i

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D}
  [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **A system of abelian sheaves on the small étale sites of the levels, presented on the
limit.** The data of [Stacks, Tag 09YQ]: a system `sys` in the sense of [Stacks, Tag 0EZL], a
sheaf `sheaf` on the small étale site of the limit, legs `ι_i : f_i^{-1}F_i ⟶ sheaf`, the
hypothesis `P` that these exhibit `sheaf` as `colim f_i^{-1}F_i`, and the two laws making the
induced maps on cohomology a cocone over a filtered diagram.

`P` is a parameter rather than a definition, and the two laws are fields rather than lemmas; the
module docstring says why for each. -/
structure PresentedSystem
    (P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop)
    where
  /-- The system of abelian sheaves on the small étale sites of the levels. -/
  sys : EtaleSheafSystem D AddCommGrpCat.{u + 1}
  /-- The abelian sheaf on the small étale site of the limit. -/
  sheaf : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}
  /-- The map to it from the inverse image of the sheaf at each level. -/
  ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (sys.obj i) ⟶ sheaf
  /-- The sheaf on the limit, with these legs, presents the colimit of the system. -/
  pres : P sys sheaf ι
  /-- **The cocycle law on cohomology**: the maps of the cohomology diagram compose. -/
  transition_comp : ∀ {i j k : Iᵒᵖ} (b : i ⟶ j) (a : j ⟶ k) (p : ℕ)
      (x : Sheaf.H.{u + 1, u + 1} (sys.obj k) p),
    etaleCohomologyTransition sys b p (etaleCohomologyTransition sys a p x) =
      etaleCohomologyTransition sys (b ≫ a) p x
  /-- **The cocone law**: the leg at a level factors every earlier leg through the diagram map. -/
  leg_transition : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℕ)
      (x : Sheaf.H.{u + 1, u + 1} (sys.obj j) p),
    etaleCohomologyMapTo (conePi c i) (ι i) p (etaleCohomologyTransition sys a p x) =
      etaleCohomologyMapTo (conePi c j) (ι j) p x

variable {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-- **The cocone leg.** The map `H^p(X_i, F_i) → H^p(X, 𝒢)`: restrict along the projection
`f_i : X ⟶ X_i` of the limit cone and then apply the leg `ι_i` of the presentation. -/
def PresentedSystem.leg (E : PresentedSystem P) (i : Iᵒᵖ) (p : ℕ) :
    Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p →+ Sheaf.H.{u + 1, u + 1} E.sheaf p :=
  etaleCohomologyMapTo (conePi c i) (E.ι i) p

/-- The cocone law of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg_transition`, written with
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`. -/
theorem PresentedSystem.leg_comp_transition (E : PresentedSystem P) {i j : Iᵒᵖ} (a : i ⟶ j)
    (p : ℕ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj j) p) :
    E.leg i p (etaleCohomologyTransition E.sys a p x) = E.leg j p x :=
  E.leg_transition a p x

/-- **The statement of [Stacks, Tag 09YQ] in degree `p`**: the cohomology `H^p(X, 𝒢)` of the
limit is the filtered colimit of the `H^p(X_i, F_i)` along the cocone of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`. The two clauses are joint
surjectivity of the legs and the vanishing, at some later level, of a class killed by its leg;
for a filtered index and abelian coefficients they are exactly the assertion that the cocone is a
colimit cocone. See the module docstring on why the statement is in this form rather than as a
`CategoryTheory.Limits.IsColimit`. -/
structure IsCohomologyColimit (E : PresentedSystem P) (p : ℕ) : Prop where
  /-- Every class on the limit comes from a level. -/
  exists_leg_eq : ∀ y : Sheaf.H.{u + 1, u + 1} E.sheaf p,
    ∃ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p), E.leg i p x = y
  /-- A class at a level whose image on the limit vanishes already vanishes at a later level. -/
  exists_transition_eq_zero : ∀ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p),
    E.leg i p x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), etaleCohomologyTransition E.sys a p x = 0

/-- **The dévissage datum of the source's proof of [Stacks, Tag 09YQ].** A presented system `E`
embeds levelwise in a presented system `mid` whose sheaf at every level is injective, with
quotient a presented system `quot`; the three sheaves on the limit form a short exact sequence
too, compatibly with the legs and with the transitions.

This is [Stacks, Tag 0EXZ] for systems on the small étale sites together with the exactness of
the passage to the limit sheaf. It is a hypothesis of the dimension shift; the module docstring
says why the library's form of Tag 0EXZ does not supply it. -/
structure Devissage (E : PresentedSystem P) where
  /-- A presented system whose sheaf at every level is injective. -/
  mid : PresentedSystem P
  /-- The quotient presented system. -/
  quot : PresentedSystem P
  /-- Every sheaf of the middle system is injective. -/
  injective : ∀ i : Iᵒᵖ, Injective (mid.sys.obj i)
  /-- The embedding of the given system into the injective one, at each level. -/
  f : ∀ i : Iᵒᵖ, E.sys.obj i ⟶ mid.sys.obj i
  /-- The projection onto the quotient system, at each level. -/
  g : ∀ i : Iᵒᵖ, mid.sys.obj i ⟶ quot.sys.obj i
  /-- The composite of the two vanishes at each level. -/
  wf : ∀ i : Iᵒᵖ, f i ≫ g i = 0
  /-- At each level the two maps form a short exact sequence of abelian étale sheaves. -/
  shortExact : ∀ i : Iᵒᵖ, (ShortComplex.mk (f i) (g i) (wf i)).ShortExact
  /-- The induced embedding of the sheaves on the limit. -/
  φ : E.sheaf ⟶ mid.sheaf
  /-- The induced projection of the sheaves on the limit. -/
  ψ : mid.sheaf ⟶ quot.sheaf
  /-- The composite of the two vanishes. -/
  wφ : φ ≫ ψ = 0
  /-- The two maps form a short exact sequence of abelian sheaves on the limit. -/
  shortExact' : (ShortComplex.mk φ ψ wφ).ShortExact
  /-- The legs are compatible with the embedding. -/
  ι_f : ∀ i : Iᵒᵖ,
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (f i) ≫ mid.ι i = E.ι i ≫ φ
  /-- The legs are compatible with the projection. -/
  ι_g : ∀ i : Iᵒᵖ,
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (g i) ≫ quot.ι i = mid.ι i ≫ ψ
  /-- The transitions are compatible with the embedding: it is a morphism of systems. -/
  map_f : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (f j) ≫ systemTransitionMap mid.sys a =
      systemTransitionMap E.sys a ≫ f i
  /-- The transitions are compatible with the projection: it is a morphism of systems. -/
  map_g : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (g j) ≫ systemTransitionMap quot.sys a =
      systemTransitionMap mid.sys a ≫ g i

namespace Devissage

variable {E : PresentedSystem P} (d : Devissage E)

/-- The short exact sequence of abelian étale sheaves at a level. -/
abbrev S (i : Iᵒᵖ) : ShortComplex (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (d.f i) (d.g i) (d.wf i)

/-- The short exact sequence of abelian sheaves on the limit. -/
abbrev T : ShortComplex (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk d.φ d.ψ d.wφ

/-- The legs, as a morphism from the inverse image of the sequence at a level to the sequence on
the limit. -/
def legHom (i : Iᵒᵖ) :
    (d.S i).map (etaleAbelianInverseImage.{u, u + 1} (conePi c i)) ⟶ d.T where
  τ₁ := E.ι i
  τ₂ := d.mid.ι i
  τ₃ := d.quot.ι i
  comm₁₂ := (d.ι_f i).symm
  comm₂₃ := (d.ι_g i).symm

/-- The transitions, as a morphism from the inverse image of the sequence at a level to the
sequence at a later level. -/
def transHom {i j : Iᵒᵖ} (a : i ⟶ j) :
    (d.S j).map (etaleAbelianInverseImage.{u, u + 1} (D.map a)) ⟶ d.S i where
  τ₁ := systemTransitionMap E.sys a
  τ₂ := systemTransitionMap d.mid.sys a
  τ₃ := systemTransitionMap d.quot.sys a
  comm₁₂ := (d.map_f a).symm
  comm₂₃ := (d.map_g a).symm

/-- **The legs commute with the connecting maps**: the ladder of long exact sequences from the
levels to the limit. -/
theorem leg_extClass (i : Iᵒᵖ) (p q : ℕ) (hpq : p + 1 = q)
    (z : Sheaf.H.{u + 1, u + 1} (d.quot.sys.obj i) p) :
    E.leg i q (z.comp (d.shortExact i).extClass hpq) =
      (d.quot.leg i p z).comp d.shortExact'.extClass hpq :=
  etaleCohomologyMapTo_comp_extClass (conePi c i) (d.shortExact i) d.shortExact'
    (d.legHom i) p q hpq z

/-- **The transitions commute with the connecting maps**: the ladder of long exact sequences along
the index. -/
theorem transition_extClass {i j : Iᵒᵖ} (a : j ⟶ i) (p q : ℕ) (hpq : p + 1 = q)
    (z : Sheaf.H.{u + 1, u + 1} (d.quot.sys.obj i) p) :
    etaleCohomologyTransition E.sys a q (z.comp (d.shortExact i).extClass hpq) =
      (etaleCohomologyTransition d.quot.sys a p z).comp (d.shortExact j).extClass hpq :=
  etaleCohomologyMapTo_comp_extClass (D.map a) (d.shortExact i) (d.shortExact j)
    (d.transHom a) p q hpq z

/-- The legs commute with the projection onto the quotient system. -/
theorem leg_map_g (i : Iᵒᵖ) (p : ℕ) (x : Sheaf.H.{u + 1, u + 1} (d.mid.sys.obj i) p) :
    d.quot.leg i p (Sheaf.H.map (d.g i) p x) = Sheaf.H.map d.ψ p (d.mid.leg i p x) :=
  etaleCohomologyMapTo_comp_mk₀ (conePi c i) (d.g i) (d.mid.ι i) (d.quot.ι i) d.ψ (d.ι_g i) p x

/-- The transitions commute with the projection onto the quotient system. -/
theorem transition_map_g {i j : Iᵒᵖ} (a : j ⟶ i) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (d.mid.sys.obj i) p) :
    etaleCohomologyTransition d.quot.sys a p (Sheaf.H.map (d.g i) p x) =
      Sheaf.H.map (d.g j) p (etaleCohomologyTransition d.mid.sys a p x) :=
  etaleCohomologyMapTo_comp_mk₀ (D.map a) (d.g i) (systemTransitionMap d.mid.sys a)
    (systemTransitionMap d.quot.sys a) (d.g j) (d.map_g a) p x

/-- The connecting map kills the image of the middle term of the sequence — the composite of two
consecutive maps of the long exact sequence. -/
theorem extClass_map_g (i : Iᵒᵖ) (p q : ℕ) (hpq : p + 1 = q)
    (x : Sheaf.H.{u + 1, u + 1} (d.mid.sys.obj i) p) :
    (Sheaf.H.map (d.g i) p x).comp (d.shortExact i).extClass hpq = 0 := by
  rw [Sheaf.H.map_apply, Ext.comp_assoc _ _ _ (add_zero p) (zero_add 1) (by omega),
    (d.shortExact i).comp_extClass, Ext.comp_zero]

end Devissage

/-- **The dimension shift for [Stacks, Tag 09YQ] on the small étale sites.** Let `I` be directed.
Assume

* `H0`, the degree-zero statement for every presented system;
* `HV`, the vanishing of `H^q(X, colim f_i^{-1}G_i)` for `q > 0` whenever every `G_i` is an
  injective abelian sheaf;
* `Hdev`, a dévissage datum for every presented system.

Then the statement of Stacks 09YQ holds in every degree `p`.

This is the source's argument. Embed the system `F` in a pointwise injective system `G` with
quotient `Q`. At every level `H^q(X_i, G_i)` vanishes for `q > 0` because `G_i` is injective, and
on the limit `H^q(X, 𝒢_G)` vanishes for `q > 0` by `HV`, so the connecting maps
`H^p(Q_i) → H^{p+1}(F_i)` and `H^p(𝒢_Q) → H^{p+1}(𝒢_F)` are surjective, and compatible with the
legs and the transitions by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage.leg_extClass` and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.Devissage.transition_extClass`. Surjectivity of
the legs in degree `p + 1` for `F` therefore follows from surjectivity in degree `p` for `Q`, and
the separatedness clause likewise — except in the one degree where the middle term survives: for
`p = 0` a class of `H^0(𝒢_Q)` killed by the connecting map is the image of a class of
`H^0(𝒢_G)`, which by `H0` for `G` comes from a level, and the two are compared at a common later
level, which is where directedness of `I` is used. That is the dévissage of the source, and it is
the only place where the degree-zero statement for the *injective* system is needed. -/
theorem isCohomologyColimit_of_degreeZero_of_vanishing [IsDirected I (· ≤ ·)]
    (H0 : ∀ E : PresentedSystem P, IsCohomologyColimit E 0)
    (HV : ∀ E : PresentedSystem P, (∀ i : Iᵒᵖ, Injective (E.sys.obj i)) →
      ∀ p : ℕ, 0 < p → Subsingleton (Sheaf.H.{u + 1, u + 1} E.sheaf p))
    (Hdev : ∀ E : PresentedSystem P, Nonempty (Devissage E))
    (p : ℕ) (E : PresentedSystem P) : IsCohomologyColimit E p := by
  induction p generalizing E with
  | zero => exact H0 E
  | succ p ih =>
    obtain ⟨d⟩ := Hdev E
    refine ⟨fun y ↦ ?_, fun i x hx ↦ ?_⟩
    · have := HV d.mid d.injective (p + 1) p.succ_pos
      obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ _ d.shortExact' y
        (Subsingleton.elim _ _) (rfl : p + 1 = p + 1)
      obtain ⟨i, x, hx⟩ := (ih d.quot).exists_leg_eq z
      exact ⟨i, x.comp (d.shortExact i).extClass rfl, by
        rw [d.leg_extClass i p (p + 1) rfl x, hx, hz]⟩
    · have := d.injective i
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₁ _ (d.shortExact i) x
        (Subsingleton.elim _ _) (rfl : p + 1 = p + 1)
      have hz0 : (d.quot.leg i p w).comp d.shortExact'.extClass rfl = 0 := by
        rw [← d.leg_extClass i p (p + 1) rfl w, hw, hx]
      obtain ⟨v, hv⟩ := Ext.covariant_sequence_exact₃ _ d.shortExact' (d.quot.leg i p w)
        (rfl : p + 1 = p + 1) hz0
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · -- degree zero: the chase through the global sections of the injective system
        obtain ⟨j₀, t, ht⟩ := (H0 d.mid).exists_leg_eq v
        obtain ⟨m, hm1, hm2⟩ := directed_of (· ≤ ·) i.unop j₀.unop
        refine
          (fun (b : (Opposite.op m : Iᵒᵖ) ⟶ i) (b' : (Opposite.op m : Iᵒᵖ) ⟶ j₀) => ?_)
            (Quiver.Hom.op (homOfLE hm1)) (Quiver.Hom.op (homOfLE hm2))
        have hv' : Sheaf.H.map d.ψ 0 v = d.quot.leg i 0 w := hv
        have key : d.quot.leg (Opposite.op m) 0
            (etaleCohomologyTransition d.quot.sys b 0 w -
              etaleCohomologyTransition d.quot.sys b' 0 (Sheaf.H.map (d.g j₀) 0 t)) = 0 := by
          rw [map_sub, d.quot.leg_comp_transition b 0 w, d.quot.leg_comp_transition b' 0 _,
            d.leg_map_g j₀ 0 t, ht, hv', sub_self]
        obtain ⟨m', e, he⟩ :=
          (H0 d.quot).exists_transition_eq_zero (Opposite.op m) _ key
        rw [map_sub, sub_eq_zero] at he
        refine ⟨m', e ≫ b, ?_⟩
        rw [← hw, d.transition_extClass (e ≫ b) 0 1 rfl w,
          ← d.quot.transition_comp e b 0 w, he, d.quot.transition_comp e b' 0 _,
          d.transition_map_g (e ≫ b') 0 t, d.extClass_map_g m' 0 1 rfl]
      · -- positive degree: the middle term already vanishes on the limit
        have := HV d.mid d.injective p hp
        have hw0 : d.quot.leg i p w = 0 := by
          rw [← hv, Subsingleton.elim v 0, Ext.zero_comp]
        obtain ⟨j, a, ha⟩ := (ih d.quot).exists_transition_eq_zero i w hw0
        exact ⟨j, a, by
          rw [← hw, d.transition_extClass a p (p + 1) rfl w, ha, Ext.zero_comp]⟩

end SmallEtaleLimitCohomology

end Stacks.EtaleCohomology

end
