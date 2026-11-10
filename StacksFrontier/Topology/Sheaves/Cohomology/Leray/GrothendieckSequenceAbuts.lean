module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectConvergence
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectFunctor
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialSpectralObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.ModuleSheafSpectralSequence
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Grothendieck spectral sequence abuts to the cohomology of the composite

[Stacks, Tag 015N] produces, for additive functors `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` with `F(I)` right
acyclic for `G` at every injective `I`, and for every `X` in `D⁺(𝒜)`, a filtered complex `K` of
`𝒞` with `H^n(K) ≅ H^n(R(G ∘ F)(X))` and a spectral sequence `E` with
`E_2^{p,q} ≅ R^pG(H^q(RF(X)))`.  Its convergence conclusions are the raw equalities (012S) and
(012T) of [Stacks, Tag 012W] together with finiteness of the filtration induced on cohomology.

This file converts those into the single clause a consumer of a spectral sequence usually wants:
that `E` **abuts** to `H^*(K)` in the sense of
`CategoryTheory.SpectralSequence.AbutsTo` -- there is a finite decreasing filtration of each
`H^n(K)` whose graded pieces are the terms `E_∞^{p,n-p}` of the infinity page.  This is the
convergence clause of [Stacks, Tag 01F2] for the spectral sequence of [Stacks, Tag 015N].

The conversion is `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`, whose only hypothesis
beyond the `(Fil, Z, D, E, hE)` presentation is that the filtration of `K` be finite in each
degree.  [Stacks, Tag 015N] records exactly that as a conclusion, its `K` being the second
total filtration of `G(I)` for a Cartan-Eilenberg resolution `I`, which is degreewise finite by
`HomologicalComplex₂.isDegreewiseFinite_totalFiltration₂`.  So no hypothesis is added here: the
abutment clause is available on the same hypotheses as [Stacks, Tag 015N] itself.

## Main results

* `CategoryTheory.Functor.exists_abutsTo_spectralSequence_rightDerivedFunctorPlus_comp`: the
  Grothendieck spectral sequence `R^pG(H^q(RF(X))) ⇒ H^{p+q}(R(G ∘ F)(X))`, with its second page
  identified and with the statement that it abuts to `H^*(K)`.
* `CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp`: **the same with
  the abutment stated on `H^*(R(G ∘ F)(X))` itself**, the filtered complex `K` no longer
  occurring in the abutment family.
* `Stacks.Cohomology.LerayModules.exists_abutsTo_leray`: **the Leray spectral sequence of a
  morphism of ringed spaces abuts to the hypercohomology of the source**, with scalars
  restricted along `f`, in the indexing [Stacks, Tag 01F2] asks for.
* `CategoryTheory.Abelian.SpectralObject.abutsTo_spectralSequence'` and
  `CategoryTheory.Abelian.SpectralObject.abutsTo_spectralSequenceFunctor_obj`: the convergence
  theorem of `StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectConvergence` packaged
  as `CategoryTheory.SpectralSequence.AbutsTo`, for the value of the spectral sequence functor.
* `Stacks.Cohomology.LerayTruncation.abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj`:
  **the spectral sequence of the truncation tower of `RG` abuts to `H^*(RG(K))`**, for a *named*
  spectral sequence rather than an existentially quantified one.
* `Stacks.Cohomology.LerayModules.abutsTo_lerayCohomologySpectralObject`: the same for the Leray
  spectral object of a morphism of ringed spaces.

## Implementation notes

* Two forms of the abutment are given.  The first is stated for `fun n => K.X.homology n`, the
  cohomology of the filtered complex itself, with the identification of that with
  `H^n(R(G ∘ F)(X))` carried alongside, exactly as in [Stacks, Tag 015N].  The second transports
  it onto `fun n => H^n(R(G ∘ F)(X))` along those identifications, by
  `CategoryTheory.SpectralSequence.AbutsTo.of_nonempty_iso`: moving the witnessing filtration
  across an isomorphism of its ambient object needs `Subobject.mapIsoToOrderIso` together with
  compatibility of `Subobject.ofLE` and `Subobject.map`, which is
  `CategoryTheory.Subobject.ofLE_map_comp_mapObjIso_hom`.
* That transport is abstract in the spectral sequence, so it applies verbatim to a sequence
  produced by a functor `D⁺(𝒜) ⥤ E₂CohomologicalSpectralSequence 𝒞` -- the shape in which
  [Stacks, Tag 01F2] states its convergence clause -- and not only to the `E` obtained here.
* The presentation data `Fil`, `Z` and `D` are universally quantified, as in
  [Stacks, Tag 015N], so a consumer which has already fixed a presentation can use it; the
  fourth datum `FH` of [Stacks, Tag 015N], the filtration induced on cohomology, is not
  quantified because abutment does not refer to it -- the filtration witnessing abutment is
  `CochainComplex.Filtered.inducedFiltrationStep`, chosen inside the proof.
* Two routes to convergence appear here.  The first, in
  `CategoryTheory.Functor.exists_abutsTo_spectralSequence_rightDerivedFunctorPlus_comp`, goes
  through the filtered complex of [Stacks, Tag 015N] and so can only produce an *existentially
  quantified* spectral sequence.  The second, from
  `StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectConvergence`, proves convergence
  directly for the spectral sequence of a bounded spectral object, which names the spectral
  sequence: it is the value of a functor.  The two spectral sequences are not identified here --
  that would be a comparison theorem -- and neither is needed for the other.
* The spectral sequence is a `CohomologicalSpectralSequence 𝒞 0`.  A consumer whose spectral
  sequence starts at the second page, as [Stacks, Tag 01F2] does, transports the conclusion
  along `CategoryTheory.SpectralSequence.AbutsTo.shiftStart`.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]

/-- **The Grothendieck spectral sequence abuts to the cohomology of the composite.**  In the
situation of [Stacks, Tag 015N] -- `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` additive between abelian
categories with enough injectives, `F(I)` right acyclic for `G` at every injective `I` of `𝒜`,
and `X` an object of `D⁺(𝒜)` -- there is a filtered complex `K` of `𝒞` with
`H^n(K) ≅ H^n(R(G ∘ F)(X))` for all `n` such that, for every presentation `(Fil, Z, D)` as in
[Stacks, Tag 012M], the resulting spectral sequence `E` has `E_2^{p,q} ≅ R^pG(H^q(RF(X)))` and
**abuts** to `H^*(K)`: some finite decreasing filtration of each `H^n(K)` has the terms
`E_∞^{p,n-p}` of the infinity page as its graded pieces.

This is the convergence clause of [Stacks, Tag 01F2] for the spectral sequence of
[Stacks, Tag 015N].  It carries no hypothesis beyond those of [Stacks, Tag 015N]: the input of
`CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite` is degreewise finiteness of the
filtration of `K`, which [Stacks, Tag 015N] concludes. -/
@[sga "4 VII 1.5" "more general",
  sga "4½ Arcata 2.3.3" "more general",
  sga "4½ Arcata 2.3.4" "more general"]
theorem exists_abutsTo_spectralSequence_rightDerivedFunctorPlus_comp (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [EnoughInjectives A] [EnoughInjectives B]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (X : DerivedCategory.Plus A) :
    ∃ K : CochainComplex.Filtered C,
      (∀ n : ℤ, Nonempty (K.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor C n).obj
          ((F ⋙ G).rightDerivedFunctorPlus.obj X))) ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))),
      ∃ (E : CohomologicalSpectralSequence C 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          (G.rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj (F.rightDerivedFunctorPlus.obj X)))) ∧
        SpectralSequence.AbutsTo E (fun n => K.X.homology n) := by
  obtain ⟨K, hK, hfin, hrest⟩ := exists_spectralSequence_rightDerivedFunctorPlus_comp F G hFG X
  refine ⟨K, hK, fun Fil hFil Z hZ D hD => ?_⟩
  obtain ⟨E, e, hE₂, -, -, -, -⟩ := hrest Fil hFil Z hZ D hD
    (fun n p => imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (fun _ _ => rfl)
  exact ⟨E, e, hE₂,
    CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite K Fil hFil Z hZ D hD E e hfin⟩

/-- **The Grothendieck spectral sequence abuts to `H^*(R(G ∘ F)(X))`.**  This is
`exists_abutsTo_spectralSequence_rightDerivedFunctorPlus_comp` with the abutment family moved off
the auxiliary filtered complex `K` and onto the cohomology of the composite right derived functor,
along the identifications `H^n(K) ≅ H^n(R(G ∘ F)(X))` that [Stacks, Tag 015N] supplies.

This is the convention a consumer of [Stacks, Tag 01F2] asks for: the abutment family no longer
mentions `K`, so it is determined by `F`, `G` and `X` alone.  No hypothesis is added -- the
transport is `CategoryTheory.SpectralSequence.AbutsTo.of_nonempty_iso`, which needs exactly the
degreewise nonempty isomorphism types [Stacks, Tag 015N] concludes and no compatibility between
the identifications at two degrees. -/
@[sga "4 V 0.3" "(ii) ⇒ (i)",
  sga "4½ Arcata 2.3.3" "more general",
  sga "4½ Arcata 2.3.4" "more general"]
theorem exists_abutsTo_homology_rightDerivedFunctorPlus_comp (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [EnoughInjectives A] [EnoughInjectives B]
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (X : DerivedCategory.Plus A) :
    ∃ K : CochainComplex.Filtered C,
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))),
      ∃ (E : CohomologicalSpectralSequence C 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          (G.rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj (F.rightDerivedFunctorPlus.obj X)))) ∧
        SpectralSequence.AbutsTo E (fun n =>
          (DerivedCategory.Plus.homologyFunctor C n).obj
            ((F ⋙ G).rightDerivedFunctorPlus.obj X)) := by
  obtain ⟨K, hK, hrest⟩ :=
    exists_abutsTo_spectralSequence_rightDerivedFunctorPlus_comp F G hFG X
  refine ⟨K, fun Fil hFil Z hZ D hD => ?_⟩
  obtain ⟨E, e, hE₂, habuts⟩ := hrest Fil hFil Z hZ D hD
  exact ⟨E, e, hE₂, habuts.of_nonempty_iso hK⟩

end CategoryTheory.Functor


namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- **The spectral sequence of a bounded spectral object abuts to `n ↦ H^n(⊥ ≤ ⊤)`.**  This is
`CategoryTheory.Abelian.SpectralObject.abutsTo_spectralSequence` packaged as
`CategoryTheory.SpectralSequence.AbutsTo`: the two statements are the same conjunction.

Unlike `Stacks.Cohomology.LerayModules.exists_abutsTo_leray`, which quantifies the spectral
sequence existentially because its witness is built from a Cartan-Eilenberg resolution, this
names the abutting spectral sequence: it is the value at `X` of the functor
`CategoryTheory.Abelian.SpectralObject.spectralSequenceFunctor coreE₂Cohomological`.  So a
consumer such as [Stacks, Tag 01F2], whose convergence clause is about the value of a *chosen*
functor `D⁺(𝒜) ⥤ E₂CohomologicalSpectralSequence 𝒞`, is served by this and not by the
existential -- provided its spectral object is bounded. -/
theorem abutsTo_spectralSequence' (X : SpectralObject D EInt) [X.IsBounded] :
    SpectralSequence.AbutsTo (X.spectralSequence coreE₂Cohomological) X.abutment :=
  X.abutsTo_spectralSequence

/-- **The abutment clause for the spectral sequence functor.**  The spectral sequence of a
bounded spectral object `X` abuts to `n ↦ H^n(⊥ ≤ ⊤)` when it is read as the value at `X` of
`spectralSequenceFunctor coreE₂Cohomological`, the form in which the convergence of a
functorially produced spectral sequence is stated. -/
theorem abutsTo_spectralSequenceFunctor_obj (X : SpectralObject D EInt) [X.IsBounded] :
    SpectralSequence.AbutsTo
      ((E₂SpectralSequenceFunctor D).obj X) X.abutment :=
  X.abutsTo_spectralSequence

end CategoryTheory.Abelian.SpectralObject

namespace Stacks.Cohomology.LerayTruncation

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] commShiftRightDerivedFunctorPlus isTriangulatedRightDerivedFunctorPlus

section Generic

variable {B : Type u} {C : Type u'} [Category.{v} B] [Category.{v'} C] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w'} C]

/-- **The cohomology spectral object of a left `t`-exact triangulated functor is bounded.**  For
`Φ : D⁺(ℬ) ⥤ D⁺(𝒞)` which moves cohomology to the right -- `Y` concentrated in degrees `≥ m`
implies `Φ(Y)` concentrated in degrees `≥ m` -- and `K` in `D⁺(ℬ)`, the spectral object
`cohomologySpectralObjectFunctor Φ` at `K` is bounded in the sense of
`CategoryTheory.Abelian.SpectralObject.IsBounded`.

The two bounds come from the two sides of `K`'s truncation tower.  Below: `K` lies in degrees
`≥ m` for some `m` because it is an object of `D⁺(ℬ)`, so `τ^{<j} K` is zero for `j ≤ m`
(`isZero_eTruncLT_obj_obj`) and `H^n(Φ(τ^{≥i} τ^{<j} K))` vanishes for every `i`.  Above:
`τ^{≥i} Z` lies in degrees `≥ n + 1` whenever `n + 1 ≤ i` (`isGE_eTruncGE_obj_obj`), hence so
does its image under `Φ`, and `H^n` of an object in degrees `≥ n + 1` vanishes. -/
lemma isBounded_cohomologySpectralObjectFunctor_obj
    (Φ : DerivedCategory.Plus B ⥤ DerivedCategory.Plus C) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : ∀ (Y : DerivedCategory.Plus B) (m : ℤ), DerivedCategory.Plus.IsGE Y m →
      DerivedCategory.Plus.IsGE (Φ.obj Y) m)
    (K : DerivedCategory.Plus B) :
    ((cohomologySpectralObjectFunctor Φ).obj K).IsBounded where
  exists_isZero_of_le n := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, DerivedCategory.Plus.IsGE K m :=
      ⟨K.2.choose, (DerivedCategory.Plus.isGE_ι_obj_iff _ _).1 K.2.choose_spec⟩
    refine ⟨m, fun i j hij hj ↦ ?_⟩
    change IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      (Φ.obj ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj K))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
      (DerivedCategory.Plus.TStructure.t.isZero_eTruncLT_obj_obj K m j hj)))
  exists_isZero_of_ge n := by
    refine ⟨n + 1, fun i j hij hi ↦ ?_⟩
    change IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      (Φ.obj ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj K))))
    have h₁ : DerivedCategory.Plus.IsGE
        ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
          ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj K)) (n + 1) :=
      DerivedCategory.Plus.TStructure.t.isGE_eTruncGE_obj_obj (n + 1) i hi _
    have := hΦ _ _ h₁
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ (n + 1) n (by lia)

/-- **The cohomology spectral object of a right derived functor is bounded.**  A right derived
functor is left `t`-exact -- `CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`, which is
[Stacks, Tag 05TC](1) -- so no hypothesis beyond additivity of `G` and enough injectives in its
source is needed. -/
lemma isBounded_cohomologySpectralObjectFunctor_rightDerivedFunctorPlus_obj
    (G : B ⥤ C) [G.Additive] [EnoughInjectives B] (K : DerivedCategory.Plus B) :
    ((cohomologySpectralObjectFunctor G.rightDerivedFunctorPlus).obj K).IsBounded :=
  isBounded_cohomologySpectralObjectFunctor_obj _
    (fun Y m hm ↦ have := hm; Functor.isGE_rightDerivedFunctorPlus_obj G Y m) K

/-- **The spectral sequence of the truncation tower of `RG` abuts to `H^*(RG(K))`.**  For `G`
additive with enough injectives in its source and `K` in `D⁺(ℬ)`, the `E₂`-cohomological
spectral sequence attached to the spectral object `cohomologySpectralObjectFunctor
G.rightDerivedFunctorPlus` at `K` abuts to `n ↦ H^n(RG(K))`.

This is the convergence clause for the **chosen** spectral sequence -- the value at that
spectral object of the functor
`CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceFunctor` -- and not for an
existentially quantified one, which is what distinguishes it from
`Stacks.Cohomology.LerayModules.exists_abutsTo_leray`.  Its abutment family is the one asked
for on the nose: `cohomologySpectralObjectFunctor`'s `H^n(⊥ ≤ ⊤)` **is**
`H^n(RG(K))`, because `τ^{<⊤}` and `τ^{≥⊥}` are the identity. -/
theorem abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj
    (G : B ⥤ C) [G.Additive] [EnoughInjectives B] (K : DerivedCategory.Plus B) :
    SpectralSequence.AbutsTo
      ((Abelian.SpectralObject.E₂SpectralSequenceFunctor C).obj
        ((cohomologySpectralObjectFunctor G.rightDerivedFunctorPlus).obj K))
      (fun n : ℤ ↦ (DerivedCategory.Plus.homologyFunctor C n).obj
        (G.rightDerivedFunctorPlus.obj K)) :=
  have := isBounded_cohomologySpectralObjectFunctor_rightDerivedFunctorPlus_obj G K
  Abelian.SpectralObject.abutsTo_spectralSequenceFunctor_obj _

end Generic

end Stacks.Cohomology.LerayTruncation

namespace Stacks.Cohomology.LerayModules

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard

-- The cheap instance deriving pointwise right derivability from `EnoughInjectives` is given
-- precedence over the one that would set about proving termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Abelianness of sheaves of modules and additivity of sections and of the direct image are not
-- instances in scope here; these lines enable them rather than restate them.
attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  evaluationAdditive Stacks.Cohomology.DerivedPushforwardSections.modulePushforward_additive

/-- **The Leray spectral sequence abuts to the hypercohomology of the source.**  For a morphism
of ringed spaces `f : X ⟶ Y` and `K` in `D⁺(Mod(𝒪_X))`, some `E₂` spectral sequence of
`Γ(Y, 𝒪_Y)`-modules abuts to `H^n(X, K)` with scalars restricted along `f`, in exactly the
indexing [Stacks, Tag 01F2] states its convergence clause in: the composite of the right derived
functor of sections over `f^{-1}(⊤)` with the right derived restriction of scalars along
`Γ(Y, 𝒪_Y) ⟶ Γ(f^{-1}(⊤), 𝒪_X)`.

This is `CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp` for the
composition `Γ(X, -) = Γ(Y, -) ∘ f_*`, whose acyclicity hypothesis is
`Stacks.Cohomology.DerivedPushforwardSections.rightAcyclic_modulePushforward_obj`
([Stacks, Tag 01EX] part (2) at `⊤`), moved onto that indexing by
`CategoryTheory.SpectralSequence.AbutsTo.of_iso` along
`Stacks.Cohomology.LerayModules.abutmentIso`, and read from the second page by
`CategoryTheory.SpectralSequence.AbutsTo.shiftStart`.

It is the convergence clause of [Stacks, Tag 01F2] up to functoriality: the spectral sequence is
existentially quantified here, whereas [Stacks, Tag 01F2] asks for a functor
`D⁺(Mod(𝒪_X)) ⥤ E₂CohomologicalSpectralSequence (ModuleCat Γ(Y, 𝒪_Y))` and for the abutment of
its value at `K`; that form is `abutsTo_lerayCohomologySpectralObject`. -/
theorem exists_abutsTo_leray {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ E : E₂CohomologicalSpectralSequence
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier)))),
      SpectralSequence.AbutsTo E (fun n : ℤ =>
        (DerivedCategory.Plus.homologyFunctor _ n).obj
          (((SheafOfModules.evaluation (structureSheafRing X)
                (op ((opensMap f).obj (⊤ : Opens Y.carrier)))).rightDerivedFunctorPlus ⋙
              (ModuleCat.restrictScalars
                ((structureSheafHom f).hom.app
                  (op (⊤ : Opens Y.carrier))).hom).rightDerivedFunctorPlus).obj K)) := by
  obtain ⟨L, hrest⟩ :=
    CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
      (modulePushforward f)
      (SheafOfModules.evaluation (structureSheafRing Y) (op (⊤ : Opens Y.carrier)))
      (rightAcyclic_modulePushforward_obj f ⊤) K
  obtain ⟨E, -, -, habuts⟩ := hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  exact ⟨E.shiftStart zero_le_two,
    (habuts.of_iso fun n =>
      (DerivedCategory.Plus.homologyFunctor _ n).mapIso ((abutmentIso f).app K)).shiftStart
        zero_le_two⟩

/-- **The Leray spectral sequence of the truncation tower abuts to the hypercohomology of the
source.**  For a morphism of ringed spaces `f : X ⟶ Y` and `K` in `D⁺(Mod(𝒪_X))`, the
`E₂`-cohomological spectral sequence attached to
`Stacks.Cohomology.LerayTruncation.lerayCohomologySpectralObject f` at `K` -- whose second page
is `H^{p+q}(RΓ(Y, τ^{≥q} τ^{<q+1} Rf_* K))` by
`Stacks.Cohomology.LerayTruncation.lerayPageTwoXIso` -- abuts to `n ↦ H^n(RΓ(Y, Rf_* K))`.

Unlike `exists_abutsTo_leray`, the spectral sequence here is **not** existentially quantified:
it is the value at `(lerayCohomologySpectralObject f).obj K` of the functor
`CategoryTheory.Abelian.SpectralObject.E₂SpectralSequenceFunctor`, which is the chosen functor
of the convergence clause of [Stacks, Tag 01F2].  This is
`Stacks.Cohomology.LerayTruncation.abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj`
for `G = Γ(Y, -)` at the object `Rf_* K`, the spectral object being that composite by
definition. -/
theorem abutsTo_lerayCohomologySpectralObject {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    SpectralSequence.AbutsTo
      ((Abelian.SpectralObject.E₂SpectralSequenceFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op (⊤ : Opens Y.carrier))))).obj
        ((Stacks.Cohomology.LerayTruncation.lerayCohomologySpectralObject f).obj K))
      (fun n : ℤ ↦ (DerivedCategory.Plus.homologyFunctor _ n).obj
        ((SheafOfModules.evaluation (structureSheafRing Y)
            (op (⊤ : Opens Y.carrier))).rightDerivedFunctorPlus.obj
          ((modulePushforward f).rightDerivedFunctorPlus.obj K))) :=
  Stacks.Cohomology.LerayTruncation.abutsTo_spectralSequence_cohomologySpectralObjectFunctor_obj
    _ _

end Stacks.Cohomology.LerayModules

end
