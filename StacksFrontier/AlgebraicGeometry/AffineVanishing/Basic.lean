module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Devissage
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Vanishing of higher cohomology from Čech vanishing on a basis

Let `X` be a ringed space, `Bas` a basis for its topology, and `Cov` a set of open coverings by
members of `Bas` whose finite intersections again lie in `Bas`, cofinal among the coverings of
every member of `Bas`. [Stacks, Tag 01EW] asserts that an `𝒪_X`-module `F` with vanishing
positive-degree Čech cohomology for every covering in `Cov` has `Hᵖ(U, F) = 0` for all `p > 0`
and all `U ∈ Bas`.

This file writes the vocabulary of that statement in library terms and carries out the parts of
the source's proof that can be done at this pin: the dévissage along an embedding `F → I` into an
injective module, and the long exact sequence of Čech cohomology that makes the quotient `I/F`
Čech-acyclic again. **No tag attribute is attached:** tag 01EW belongs to the cohomology
chapters and may be carried elsewhere in the tree.

What remains is stated as four hypotheses, listed in the implementation notes. Three of them are
the first half of the source's proof — [Stacks, Tag 01EP], [Stacks, Tag 01EU] and its degreewise
form — and the fourth is the long exact cohomology sequence for Mathlib's `ℕ`-indexed right
derived functors. None exists in Mathlib or in this repository at this pin.

## Main results

* `Stacks.CohomologyVanishing.higherCohomology_isZero_of_gaps`: **the conclusion of
  [Stacks, Tag 01EW]**, `Hᵖ(U, F) = 0` for `p > 0` and `U ∈ Bas`, from four explicitly named
  hypotheses, each the statement of a lemma that does not exist at this pin.
* `Stacks.CohomologyVanishing.higherCohomology_isZero_of_cechDevissage`: the same with the last
  three bundled as the source's dévissage step.
* `Stacks.CohomologyVanishing.isZero_homology_X₃_of_shortExact`: the long exact sequence step,
  for cochain complexes in any abelian category.
* `Stacks.CohomologyVanishing.hasVanishingHigherCech_X₃`: Čech acyclicity passes to the quotient.
* `Stacks.CohomologyVanishing.cechDevissageStep_of`: the dévissage step from its three
  ingredients.

## Main definitions

* `Stacks.CohomologyVanishing.OpenCover`, `Stacks.CohomologyVanishing.OpenCover.Refines`: a small
  family of opens covering a specified open, and refinement of such families.
* `Stacks.CohomologyVanishing.cechFunctor`,
  `Stacks.CohomologyVanishing.CechCohomologyIsZero`,
  `Stacks.CohomologyVanishing.HasVanishingHigherCech`: the Čech complex of a cover with
  coefficients in a sheaf of modules, vanishing of its cohomology in one degree, and vanishing in
  all positive degrees for all coverings of a given set.
* `Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`,
  `Stacks.CohomologyVanishing.CechAcyclicInjectives`,
  `Stacks.CohomologyVanishing.CechShortExact`,
  `Stacks.CohomologyVanishing.CechDevissageStep`: the hypotheses, one definition each.

## Implementation notes

**Cohomology indexing.** `Hⁿ(U, F)` is `Hgroup R U n F`, the `ℕ`-indexed Mathlib right derived
functor `CategoryTheory.Functor.rightDerived` of sections over `U`, as `Hgroup` is set up for
Stacks Tag 01E3 and as this tag's statement reads. The `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean` is *not* used
below; everything here is about the `ℕ`-indexed theory.

Results *do* transfer between the two indexings. `Stacks.DerivedIndexing.rightDerivedIso` is the
comparison `F.rightDerived n ≅ F.rightDerivedPlus (n : ℤ)`, with `isZero_rightDerived_obj_iff` and
`isZero_rightDerivedPlus_obj_iff` carrying vanishing both ways. So a `ℤ`-indexed input may be used
to discharge an `ℕ`-indexed obligation and conversely.

**The four hypotheses, and why they are hypotheses.**

* `IsCohomologyDeltaFunctor R U D` says that the cohomological δ-functor `D` (Stacks 010Q,
  `CategoryTheory.DeltaFunctor`) has degree-zero part `Γ(U, -)` and positive-degree parts the
  `Hⁿ(U, -)`. Equivalently: the long exact cohomology sequence over `U`. Mathlib's `ℕ`-indexed
  `Functor.rightDerived` has **no** long exact sequence at this pin — the only construction in
  the repository, `Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal` (Stacks 05TE),
  produces one for the `ℤ`-indexed `rightDerivedPlus`, and bridging the two indexings is exactly
  the missing comparison just mentioned.
* `CechAcyclicInjectives R Cov` is [Stacks, Tag 01EP].
* `CechShortExact R Cov` is the degreewise form of [Stacks, Tag 01EU] over the opens occurring in
  the Čech complexes, plus exactness of products in `AddCommGrpCat`.
* The surjectivity `Γ(V, I) → Γ(V, Q)` over the basis opens is [Stacks, Tag 01EU] itself.

**On the hypotheses of the source that are absent here.** The source's `Bas` is a basis, the
members of `Cov` are coverings by members of `Bas` closed under the finite intersections
occurring in their Čech complexes, and the coverings in `Cov` are cofinal among the coverings of
each member of `Bas`. Those three hypotheses are what one uses to *prove* the four above; once
those are hypothesized the three are not needed, so they do not appear. Dropping them makes the
theorems below strictly stronger than Tag 01EW, never weaker: any instance of the source's
statement is obtained from them by supplying the four hypotheses. `OpenCover.Refines` is defined
here, unused, because cofinality is the natural way to state them.

**The `HasProducts.{u} AddCommGrpCat.{w}` assumption.** `cechComplexFunctor` forms a product
indexed by `Fin (p + 1) → V.ι`, and `V.ι : Type u` while the coefficients live in
`AddCommGrpCat.{w}`, `w` the module universe. The instance holds whenever `u ≤ w`; it is carried
explicitly only because the module universe is kept independent of the universe of `X` (this tag's
own statement instead lets unification force the module universe to be at least `u`).

**Positional instance arguments.** None are needed in this file; the `Epi` transport along the
degree-zero natural isomorphism is done by an explicit factorization rather than by asking
instance synthesis to see through `Hfunctor`.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01EV](https://stacks.math.columbia.edu/tag/01EV)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.CohomologyVanishing

/-- A small family of open subsets whose supremum is a specified open subset. -/
structure OpenCover (X : Type u) [TopologicalSpace X] where
  /-- The indexing type of the cover. -/
  ι : Type u
  /-- The open subset being covered. -/
  carrier : Opens X
  /-- The members of the cover. -/
  obj : ι → Opens X
  /-- The covering condition. -/
  iSup_eq : ⨆ i, obj i = carrier

namespace OpenCover

variable {X : Type u} [TopologicalSpace X]

/-- `V.Refines U` means that `V` and `U` cover the same open and every member of `V` is
contained in a member of `U`. -/
def Refines (V U : OpenCover X) : Prop :=
  V.carrier = U.carrier ∧ ∀ j, ∃ i, V.obj j ≤ U.obj i

/-- Every cover refines itself. -/
lemma Refines.rfl (U : OpenCover X) : U.Refines U :=
  ⟨Eq.refl _, fun j ↦ ⟨j, le_refl _⟩⟩

/-- Refinement is transitive. -/
lemma Refines.trans {W V U : OpenCover X} (hWV : W.Refines V) (hVU : V.Refines U) :
    W.Refines U :=
  ⟨hWV.1.trans hVU.1, fun j ↦
    let ⟨i, hi⟩ := hWV.2 j
    let ⟨k, hk⟩ := hVU.2 i
    ⟨k, hi.trans hk⟩⟩

end OpenCover

/-- **The third term of a short exact sequence of cochain complexes has vanishing
positive-degree cohomology** as soon as the first two do. For `p > 0` the connecting morphism
`Hᵖ(X₃) ⟶ Hᵖ⁺¹(X₁)` is an isomorphism because `Hᵖ(X₂)` and `Hᵖ⁺¹(X₂)` vanish, and `Hᵖ⁺¹(X₁)`
vanishes. This is the Čech long exact sequence step of the proof of [Stacks, Tag 01EW],
isolated from the Čech complex. -/
theorem isZero_homology_X₃_of_shortExact {C : Type*} [Category C] [Abelian C]
    {T : ShortComplex (CochainComplex C ℕ)} (hT : T.ShortExact)
    (h₁ : ∀ q : ℕ, 0 < q → IsZero (T.X₁.homology q))
    (h₂ : ∀ q : ℕ, 0 < q → IsZero (T.X₂.homology q)) (p : ℕ) (hp : 0 < p) :
    IsZero (T.X₃.homology p) :=
  IsZero.of_iso (h₁ (p + 1) p.succ_pos)
    (hT.δIso p (p + 1) rfl (h₂ p hp) (h₂ (p + 1) p.succ_pos))

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat) [HasProducts.{u} AddCommGrpCat.{w}]

/-- The Čech complex of an open cover, with coefficients in a sheaf of modules: the Čech complex
of the underlying presheaf of abelian groups. -/
noncomputable def cechFunctor (V : OpenCover X) :
    SheafOfModules.{w} R ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  SheafOfModules.toSheaf R ⋙ sheafToPresheaf _ _ ⋙ cechComplexFunctor V.obj

/-- Vanishing in degree `n` of the Čech cohomology of an open cover with coefficients in a
sheaf of modules. -/
def CechCohomologyIsZero (F : SheafOfModules.{w} R) (V : OpenCover X) (n : ℕ) : Prop :=
  IsZero (((cechFunctor R V).obj F).homology n)

/-- `CechCohomologyIsZero` spelled out: the degree-`n` homology of Mathlib's Čech complex of the
underlying abelian-group presheaf is zero. -/
lemma cechCohomologyIsZero_iff (F : SheafOfModules.{w} R) (V : OpenCover X) (n : ℕ) :
    CechCohomologyIsZero R F V n ↔
      IsZero (((cechComplexFunctor V.obj).obj
        ((SheafOfModules.toSheaf R).obj F).obj).homology n) :=
  Iff.rfl

/-- A sheaf of modules has vanishing higher Čech cohomology for a set `Cov` of open coverings if
`Ȟᵖ(V, F) = 0` for every `V ∈ Cov` and every `p > 0`. -/
def HasVanishingHigherCech (Cov : Set (OpenCover X)) (F : SheafOfModules.{w} R) : Prop :=
  ∀ V ∈ Cov, ∀ p : ℕ, 0 < p → CechCohomologyIsZero R F V p

/-- **[Stacks, Tag 01EP] in the form used here:** an injective `𝒪_X`-module has vanishing
positive-degree Čech cohomology for every covering in `Cov`. -/
def CechAcyclicInjectives (Cov : Set (OpenCover X)) : Prop :=
  ∀ I : SheafOfModules.{w} R, Injective I → HasVanishingHigherCech R Cov I

/-- **Degreewise exactness of the Čech complex:** the Čech complexes of a short exact sequence of
`𝒪_X`-modules again form a short exact sequence, for every covering in `Cov`.

For a covering whose members and whose finite intersections lie in the basis this is the
degreewise statement `0 → F(V_{i₀…i_p}) → I(V_{i₀…i_p}) → Q(V_{i₀…i_p}) → 0`, i.e.
[Stacks, Tag 01EU] over each of those opens, together with exactness of products in
`AddCommGrpCat`. The short exact sequence of complexes is required only to *have* the Čech
complexes as its three terms, so that no compatibility of `cechFunctor` with zero morphisms is
needed to state it. -/
def CechShortExact (Cov : Set (OpenCover X)) : Prop :=
  ∀ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact → ∀ V ∈ Cov,
    ∃ T : ShortComplex (CochainComplex AddCommGrpCat.{w} ℕ), T.ShortExact ∧
      T.X₁ = (cechFunctor R V).obj S.X₁ ∧ T.X₂ = (cechFunctor R V).obj S.X₂ ∧
      T.X₃ = (cechFunctor R V).obj S.X₃

/-- **Čech acyclicity passes to the quotient.** In a short exact sequence of `𝒪_X`-modules whose
first two terms have vanishing positive-degree Čech cohomology for `Cov`, so has the third. This
is the step of the proof of [Stacks, Tag 01EW] that runs the long exact sequence of Čech
cohomology. -/
theorem hasVanishingHigherCech_X₃ {Cov : Set (OpenCover X)} (hSE : CechShortExact R Cov)
    (S : ShortComplex (SheafOfModules.{w} R)) (hS : S.ShortExact)
    (h₁ : HasVanishingHigherCech R Cov S.X₁) (h₂ : HasVanishingHigherCech R Cov S.X₂) :
    HasVanishingHigherCech R Cov S.X₃ := by
  intro V hV p hp
  obtain ⟨T, hT, e₁, e₂, e₃⟩ := hSE S hS V hV
  change IsZero (((cechFunctor R V).obj S.X₃).homology p)
  rw [← e₃]
  refine isZero_homology_X₃_of_shortExact hT (fun q hq ↦ ?_) (fun q hq ↦ ?_) p hp
  · rw [e₁]; exact h₁ V hV q hq
  · rw [e₂]; exact h₂ V hV q hq

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]

/-- **First hypothesis of `higherCohomology_isZero_of_cechDevissage`: the long exact cohomology
sequence over a fixed open `U`.** A cohomological δ-functor (Stacks 010Q) on `𝒪_X`-modules whose
degree-zero part is `Γ(U, -)` and whose positive-degree parts are the cohomology functors
`Hⁿ(U, -)`.

This does not exist at this pin for Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`;
see the implementation notes of this file. -/
structure IsCohomologyDeltaFunctor (U : Opens X)
    (D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat) where
  /-- The degree-zero part of `D` is sections over `U`. -/
  isoZero : D.functor 0 ≅ secF R U
  /-- The positive-degree parts of `D` are the cohomology functors over `U`. -/
  isoSucc : ∀ m : ℕ, D.functor (m + 1) ≅ Hfunctor R U (m + 1)

/-- **Second hypothesis of `higherCohomology_isZero_of_cechDevissage`: the dévissage step.**
Every `𝒪_X`-module `G` with vanishing higher Čech cohomology for `Cov` fits in a short exact
sequence `0 → G → I → Q → 0` with `I` injective, such that `Γ(V, I) → Γ(V, Q)` is surjective for
every `V ∈ Bas` and such that `Q` again has vanishing higher Čech cohomology for `Cov`.

This is the first half of the proof of [Stacks, Tag 01EW]: the embedding comes from
`EnoughInjectives`, the surjectivity on sections from [Stacks, Tag 01EU], and the Čech acyclicity
of `Q` from that surjectivity together with [Stacks, Tag 01EP] and the long exact sequence of
Čech cohomology. None of the three is available at this pin. -/
def CechDevissageStep (Bas : Set (Opens X)) (Cov : Set (OpenCover X))
    (G : SheafOfModules.{w} R) : Prop :=
  HasVanishingHigherCech R Cov G →
    ∃ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact ∧ S.X₁ = G ∧ Injective S.X₂ ∧
      (∀ V ∈ Bas, Epi ((secF R V).map S.g)) ∧ HasVanishingHigherCech R Cov S.X₃

/-- **The dévissage step of [Stacks, Tag 01EW] from its three ingredients.** Čech acyclicity of
injective modules ([Stacks, Tag 01EP]), degreewise exactness of the Čech complexes of a short
exact sequence ([Stacks, Tag 01EU] over the basis opens), and surjectivity on sections over the
basis opens ([Stacks, Tag 01EU]) together give `CechDevissageStep`. The embedding into an
injective module is `CategoryTheory.Injective.ι`. -/
theorem cechDevissageStep_of {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    (hinj : CechAcyclicInjectives R Cov) (hSE : CechShortExact R Cov)
    (hsec : ∀ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact →
      ∀ V ∈ Bas, Epi ((secF R V).map S.g))
    (G : SheafOfModules.{w} R) : CechDevissageStep R Bas Cov G := by
  intro hG
  have hSX : (ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι G)))
      (Injective.ι_mono G) inferInstance
  refine ⟨_, hSX, rfl, Injective.injective_under G, hsec _ hSX, ?_⟩
  exact hasVanishingHigherCech_X₃ R hSE _ hSX hG (hinj _ (Injective.injective_under G))

/-- **The conclusion of [Stacks, Tag 01EW].** Let `F` be an `𝒪_X`-module with vanishing higher
Čech cohomology for every covering in `Cov`. Then `Hⁿ(U, F) = 0` for every `n > 0` and every
`U ∈ Bas`, given the long exact cohomology sequence over `U` (`CohomologyDeltaFunctor`) and the
dévissage step of the source's proof (`CechDevissageStep`).

The source's hypotheses on `Bas` and `Cov` — basis, closure under the intersections of the Čech
complexes, cofinality — are what one uses to establish `CechDevissageStep`, and are therefore
absent here; see the implementation notes. -/
theorem higherCohomology_isZero_of_cechDevissage {Bas : Set (Opens X)}
    {Cov : Set (OpenCover X)} {U : Opens X}
    {D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat}
    (hD : IsCohomologyDeltaFunctor R U D)
    (hstep : ∀ G : SheafOfModules.{w} R, CechDevissageStep R Bas Cov G) (hU : U ∈ Bas)
    (F : SheafOfModules.{w} R) (hF : HasVanishingHigherCech R Cov F) (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup R U n F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  refine IsZero.of_iso ?_ ((hD.isoSucc m).app F).symm
  refine isZero_obj_succ_of_injective_devissage D ?_ (HasVanishingHigherCech R Cov) ?_ m F hF
  · intro k I hI
    have := hI
    exact IsZero.of_iso (Functor.isZero_rightDerived_obj_injective_succ (secF R U) k I)
      ((hD.isoSucc k).app I)
  · intro G hG
    obtain ⟨S, hS, hX₁, hinj, hepi, hQ⟩ := hstep G hG
    refine ⟨S, hS, hX₁, hinj, ?_, hQ⟩
    have key : (D.functor 0).map S.g =
        (hD.isoZero.hom.app S.X₂ ≫ (secF R U).map S.g) ≫ hD.isoZero.inv.app S.X₃ := by
      rw [← hD.isoZero.hom.naturality S.g, Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
    have := hepi U hU
    rw [key]
    infer_instance

/-- **[Stacks, Tag 01EW] reduced to four named statements.** Let `F` be an `𝒪_X`-module with
vanishing positive-degree Čech cohomology for every covering in `Cov`. Then `Hⁿ(U, F) = 0` for
every `n > 0` and every `U ∈ Bas`, given

1. a cohomological δ-functor realizing the cohomology over `U` (`IsCohomologyDeltaFunctor`, i.e.
   the long exact cohomology sequence);
2. Čech acyclicity of injective modules (`CechAcyclicInjectives`, [Stacks, Tag 01EP]);
3. short exactness of the Čech complexes of a short exact sequence (`CechShortExact`,
   [Stacks, Tag 01EU] degreewise);
4. surjectivity on sections over the basis opens ([Stacks, Tag 01EU]).

These four are what the source's hypotheses on `Bas` and `Cov` — basis, closure under the
intersections of the Čech complexes, cofinality — are used for; they are therefore the whole
remaining content of the tag, and none of them is available at this pin. -/
theorem higherCohomology_isZero_of_gaps {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    {U : Opens X} {D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat}
    (hD : IsCohomologyDeltaFunctor R U D) (hinj : CechAcyclicInjectives R Cov)
    (hSE : CechShortExact R Cov)
    (hsec : ∀ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact →
      ∀ V ∈ Bas, Epi ((secF R V).map S.g))
    (hU : U ∈ Bas) (F : SheafOfModules.{w} R) (hF : HasVanishingHigherCech R Cov F)
    (n : ℕ) (hn : 0 < n) : IsZero (Hgroup R U n F) :=
  higherCohomology_isZero_of_cechDevissage R hD (cechDevissageStep_of R hinj hSE hsec) hU F hF
    n hn

end Stacks.CohomologyVanishing
