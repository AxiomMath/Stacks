module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# The affine crystalline site is a dense subsite of the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  Among the objects `(U, T, δ)` of the
small crystalline site `Cris(X/S)` are those for which both the thickened scheme `U` and its
ambient divided power scheme `T` are affine.  They span a full subcategory `AffineCris(X/S)`,
which [Stacks, Tag 07JK] endows with the coverings it inherits from `Cris(X/S)`: a family of
morphisms of `AffineCris(X/S)` covers exactly when it covers in `Cris(X/S)`.

This file constructs that site and proves that the inclusion
`AffineCris(X/S) ⥤ Cris(X/S)` is a **special cocontinuous functor** in the sense of
[Stacks, Tag 03CG], which is the first reduction in the proof of [Stacks, Tag 07JK].  As a
consequence the two sites have the same topos: restriction along the inclusion is an equivalence
`Sh(AffineCris(X/S)) ≌ Sh(Cris(X/S))`, in sets and in abelian groups.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `IsAffineObject` — the property cutting out the subcategory: the thickened scheme and its
  ambient divided power scheme are both affine.
* `AffineCrystallineThickening` — the objects of `AffineCris(X/S)`, the full subcategory of
  `Cris(X/S)` they span, and `affineι` the inclusion `AffineCris(X/S) ⥤ Cris(X/S)`.
* `AffineCrystallineThickening.restrictOpen` — the restriction of an object of `Cris(X/S)` to an
  affine open of its ambient scheme, which is an object of `AffineCris(X/S)`, with the morphism
  `AffineCrystallineThickening.restrictOpenHom` and the family
  `AffineCrystallineThickening.restrictOpenCover`.
* `AffineCrystallineThickening.IsZariskiCovering` — a covering family of `AffineCris(X/S)`: one
  whose image in `Cris(X/S)` is a Zariski covering family.
* `affinePrecoverage`, `affineTopology` — the coverings inherited from `Cris(X/S)` and the
  topology they generate.
* `affineSheafEquiv`, `affineToposEquiv`, `affineAbelianSheafEquiv` — the equivalence of sheaf
  categories, of topoi, and of categories of abelian sheaves, induced by the inclusion.

## Main results

* `AffineCrystallineThickening.isZariskiCovering_restrictOpenCover` — the restrictions of an
  object of `AffineCris(X/S)` to a family of affine opens covering its ambient scheme form a
  covering family of `AffineCris(X/S)`.
* `CrystallineThickening.exists_affineRefinement` — every open cover of the ambient scheme of an
  object of `Cris(X/S)` is refined by a cover by affine opens; this is what makes
  `AffineCris(X/S)` dense.
* `affineι_isCoverDense` — **`AffineCris(X/S)` is cover-dense in `Cris(X/S)`**: every object of
  `Cris(X/S)` is covered by affine ones.
* `affineι_isCocontinuous` — **the inclusion is cocontinuous**: a covering sieve of an affine
  object in `Cris(X/S)` pulls back to a covering sieve of `AffineCris(X/S)`.
* `affineTopology_eq_restrictedTopology` — the inherited topology is the topology restricted
  from `Cris(X/S)` along the inclusion, which is what turns cover density into the dense-subsite
  property.
* `affineι_isSpecialCocontinuous` — **the inclusion `AffineCris(X/S) ⥤ Cris(X/S)` is a special
  cocontinuous functor**, [Stacks, Tag 03CG].

## What is and is not proved

What is proved is the first reduction in the proof of [Stacks, Tag 07JK]: the inclusion of the
affine crystalline site into the small crystalline site is a special cocontinuous functor, so
the two sites have the same topos and the same categories of sheaves.  No tag attribute is
placed in this file, because the comparison [Stacks, Tag 07JK] asserts —
`H^j(𝒞, F|_𝒞) ≅ H^j(Cris(X/S), F)` for the chaotic subsite `𝒞` of thickenings of the whole space
and a locally quasi-coherent `F` — takes more than this reduction.  It is assembled, and carries
the tag, as `...SmallSite.chaoticCohomologyComparisonIso` of
`SmallSite/ChaoticComparison.lean`; what it adds to this file is, in the order the source's proof
uses it:

1. That the objects of the chaotic subsite `𝒞` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ChaoticSubsite.lean` are
   objects of `AffineCris(X/S)` when `X` is affine.  One half is `isAffineObject_of_isAffine`
   below; the other half, that the ambient scheme `T` of a thickening of an affine `U` is
   affine, is [Stacks, Tag 06AD] and is available unconditionally as
   `Stacks.Thickenings.isAffine_of_isThickening`, with the crystalline specialisation
   `Crystalline.SchemeThickening.isAffine_target`.
2. The morphism of ringed sites attached to the inclusion `𝒞 ⊆ AffineCris(X/S)`, whose comma
   categories are nonempty and connected.  Nonemptiness is where the affineness of `X` and `S`
   enters: an object `(U, T, δ)` of `AffineCris(X/S)` admits a morphism to a divided power
   thickening of the whole of `X`, which for affine `X` is the divided power envelope of a
   polynomial presentation of `X`.
3. The vanishing `R^p f_* F = 0` for `p > 0` along that morphism, which by the source reduces to
   [Stacks, Tag 07JJ] over the objects of `AffineCris(X/S)`; the fragment over a single affine
   object is
   `Crystalline.GlobalCrystallineSituation.SmallSite.isZero_cohomology_restriction_of_isAffine`
   and the shape the comparison consumes is `...SmallSite.vanishing07JJ_abelianSheaf`.
4. That the equivalence of abelian sheaf categories identifies the cohomology groups `H^j` on the
   two sites, which is `...SmallSite.affineCohomologyIso` of
   `SmallSite/AffineSubsiteCohomology.lean`.

## Implementation notes

The subcategory is `CategoryTheory.ObjectProperty.FullSubcategory` of `CrystallineThickening S`,
as `Cris(X/S)` is itself a full subcategory of `CRIS(X/S)`, so an object of `AffineCris(X/S)`
carries its underlying object of `Cris(X/S)` in the field `obj` and that one its underlying
object of `CRIS(X/S)` in `obj.obj`.  The property is stated as the conjunction of the
affineness of `U` and of `T`, as the source states it; `isAffineObject_of_isAffine` records that
the affineness of `T` alone suffices, the immersion `U ⟶ T` being a closed immersion and
therefore an affine morphism.

Cocontinuity is the substantial half.  It is proved by induction over the saturation that
generates the topology of `Cris(X/S)`, in the form `restrictCoverage_toGrothendieck`: the
topology is generated by the *coverage* of families of restrictions of an object to an open cover
of its ambient scheme, so the induction has only the three cases of
`CategoryTheory.Coverage.Saturate` and the covering families in the base case are already
families of restrictions.  Refining such a family by affine opens and factoring the refined
restrictions through the members of the original family — the universal property
`CrystallineThickening.exists_comp_restrictOpenHom_eq` — is then the whole argument.  The index
type of the refinement is the points of the ambient scheme, lifted to the universe `u + 1` that
a covering family of the crystalline site indexes over.

The dense-subsite property is obtained as in the Zariski case
(`AlgebraicGeometry.SmallAffineZariski.inclusion_isSpecialCocontinuous`, [Stacks, Tag 0F1B]):
cover density gives it for the restricted topology of
`CategoryTheory.Functor.restrictedTopology`, and `affineTopology_eq_restrictedTopology`
identifies the inherited topology with that one, cocontinuity supplying the inclusion that
monotonicity of `Precoverage.toGrothendieck` does not.

## References

* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The property cutting out the subcategory `AffineCris(X/S)` of [Stacks, Tag 07JK]: both the
thickened scheme `U` and its ambient divided power scheme `T` of an object `(U, T, δ)` of
`Cris(X/S)` are affine. -/
abbrev IsAffineObject : ObjectProperty (CrystallineThickening S) :=
  fun A ↦ IsAffine A.obj.thickening.source ∧ IsAffine A.obj.thickening.target.scheme

/-- **An object of `Cris(X/S)` with affine ambient scheme is an object of `AffineCris(X/S)`.**
The thickened scheme `U` sits in `T` by a closed immersion, which is an affine morphism, so `U`
is affine as soon as `T` is.  The converse implication is [Stacks, Tag 06AD], available as
`Crystalline.SchemeThickening.isAffine_target`. -/
theorem isAffineObject_of_isAffine (A : CrystallineThickening S)
    [IsAffine A.obj.thickening.target.scheme] : IsAffineObject S A :=
  ⟨isAffine_of_isAffineHom A.obj.thickening.immersion, inferInstance⟩

/-- **The category `AffineCris(X/S)` of [Stacks, Tag 07JK]**: the full subcategory of the small
crystalline site `Cris(X/S)` on the objects `(U, T, δ)` with `U` and `T` affine. -/
abbrev AffineCrystallineThickening (S : GlobalCrystallineSituation.{u}) :=
  (IsAffineObject S).FullSubcategory

/-- The inclusion `AffineCris(X/S) ⥤ Cris(X/S)` of the affine objects into the small crystalline
site. -/
abbrev affineι : AffineCrystallineThickening S ⥤ CrystallineThickening S :=
  (IsAffineObject S).ι

/-- The inclusion `AffineCris(X/S) ⥤ Cris(X/S)` is fully faithful, being the inclusion of a full
subcategory. -/
abbrev fullyFaithfulAffineι : (affineι S).FullyFaithful :=
  (IsAffineObject S).fullyFaithfulι

namespace AffineCrystallineThickening

variable {S}

/-- **The restriction of an object of `Cris(X/S)` to an affine open of its ambient scheme is an
object of `AffineCris(X/S)`.**  Its ambient scheme is that affine open, and its thickened scheme
is the preimage of that open, affine because the immersion is a closed immersion. -/
noncomputable def restrictOpen (A : CrystallineThickening S)
    {V : A.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    AffineCrystallineThickening S :=
  ⟨A.restrictOpen V,
    haveI : IsAffine (A.restrictOpen V).obj.thickening.target.scheme := hV
    isAffineObject_of_isAffine S (A.restrictOpen V)⟩

/-- The underlying object of `Cris(X/S)` of `restrictOpen A hV` is the restriction
`A.restrictOpen V`. -/
@[simp]
theorem restrictOpen_obj (A : CrystallineThickening S)
    {V : A.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    (restrictOpen A hV).obj = A.restrictOpen V := rfl

/-- The structure morphism of the restriction of an object of `AffineCris(X/S)` to an affine open
of its ambient scheme, as a morphism of `AffineCris(X/S)`. -/
noncomputable def restrictOpenHom (A : AffineCrystallineThickening S)
    {V : A.obj.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    restrictOpen A.obj hV ⟶ A :=
  ObjectProperty.homMk (A.obj.restrictOpenHom V)

/-- The underlying morphism of `Cris(X/S)` of `restrictOpenHom A hV` is the structure morphism
`A.obj.restrictOpenHom V`. -/
@[simp]
theorem restrictOpenHom_hom (A : AffineCrystallineThickening S)
    {V : A.obj.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    (restrictOpenHom A hV).hom = A.obj.restrictOpenHom V := rfl

/-- The family of restrictions of an object of `AffineCris(X/S)` to a family of affine opens of
its ambient scheme. -/
noncomputable def restrictOpenCover (A : AffineCrystallineThickening S) {I : Type (u + 1)}
    (V : I → A.obj.obj.thickening.target.scheme.Opens) (hV : ∀ i, IsAffineOpen (V i)) :
    PreZeroHypercover.{u + 1} A where
  I₀ := I
  X i := restrictOpen A.obj (hV i)
  f i := restrictOpenHom A (hV i)

/-- **A covering family of `AffineCris(X/S)`**, as [Stacks, Tag 07JK] prescribes: a family of
morphisms of `AffineCris(X/S)` whose image in `Cris(X/S)` is a Zariski covering family, that is,
whose squares are Cartesian and whose ambient schemes form a Zariski covering. -/
abbrev IsZariskiCovering {B : AffineCrystallineThickening S}
    (E : PreZeroHypercover.{u + 1} B) : Prop :=
  CrystallineThickening.IsZariskiCovering (E.map (affineι S))

/-- **The restrictions of an object of `AffineCris(X/S)` to a family of affine opens covering its
ambient scheme form a covering family of `AffineCris(X/S)`.**  Its image in `Cris(X/S)` is the
family of restrictions of the underlying object. -/
theorem isZariskiCovering_restrictOpenCover (A : AffineCrystallineThickening S)
    {I : Type (u + 1)} (V : I → A.obj.obj.thickening.target.scheme.Opens)
    (hV : ∀ i, IsAffineOpen (V i))
    (hcov : ∀ x : A.obj.obj.thickening.target.scheme, ∃ i, x ∈ V i) :
    IsZariskiCovering (restrictOpenCover A V hV) :=
  CrystallineThickening.isZariskiCovering_restrictOpenCover A.obj V hcov

end AffineCrystallineThickening

/-- The precoverage of `AffineCris(X/S)` whose covering presieves are those presented by a
covering family of `AffineCris(X/S)`. -/
def affinePrecoverage (S : GlobalCrystallineSituation.{u}) :
    Precoverage (AffineCrystallineThickening S) where
  coverings B := {R | ∃ E : PreZeroHypercover.{u + 1} B, R = E.presieve₀ ∧
    AffineCrystallineThickening.IsZariskiCovering E}

/-- A presieve is covering for `affinePrecoverage` exactly when some covering family of
`AffineCris(X/S)` presents it. -/
theorem mem_affinePrecoverage_iff (S : GlobalCrystallineSituation.{u})
    {B : AffineCrystallineThickening S} {R : Presieve B} :
    R ∈ affinePrecoverage S B ↔
      ∃ E : PreZeroHypercover.{u + 1} B, R = E.presieve₀ ∧
        AffineCrystallineThickening.IsZariskiCovering E :=
  Iff.rfl

/-- **The affine crystalline site `AffineCris(X/S)` of [Stacks, Tag 07JK]**: the full subcategory
of `Cris(X/S)` on the objects with `U` and `T` affine, with the topology generated by the families
that cover in `Cris(X/S)`. -/
abbrev affineTopology (S : GlobalCrystallineSituation.{u}) :
    GrothendieckTopology (AffineCrystallineThickening S) :=
  (affinePrecoverage S).toGrothendieck

/-- **Every covering family of `AffineCris(X/S)` covers in the affine crystalline site.** -/
theorem affineZariskiCovering_mem_affineTopology (S : GlobalCrystallineSituation.{u})
    {B : AffineCrystallineThickening S} (E : PreZeroHypercover.{u + 1} B)
    (hE : AffineCrystallineThickening.IsZariskiCovering E) :
    Sieve.generate E.presieve₀ ∈ affineTopology S B :=
  (affinePrecoverage S).generate_mem_toGrothendieck ⟨E, rfl, hE⟩

variable {S}

namespace CrystallineThickening

/-- **A morphism of `Cris(X/S)` whose ambient scheme maps an open `W` into an open `V` restricts
to a morphism from the restriction to `W` to the restriction to `V`**, compatibly with the two
structure morphisms.  This is the universal property
`CrystallineThickening.exists_comp_restrictOpenHom_eq` applied to the composite of the structure
morphism of the restriction to `W` with the given morphism. -/
theorem exists_comp_restrictOpenHom_eq_of_le {A B : CrystallineThickening S} (g : A ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens)
    (W : A.obj.thickening.target.scheme.Opens)
    (hW : W ≤ g.hom.targetHom.hom ⁻¹ᵁ V) :
    ∃ p : A.restrictOpen W ⟶ B.restrictOpen V,
      p ≫ B.restrictOpenHom V = A.restrictOpenHom W ≫ g :=
  CrystallineThickening.exists_comp_restrictOpenHom_eq V (A.restrictOpenHom W ≫ g)
    fun x ↦ hW (show W.toScheme from x).2

/-- **Every open cover of the ambient scheme of an object of `Cris(X/S)` is refined by a cover by
affine opens.**  The refinement is indexed by the points of the ambient scheme: around each point
an affine open contained in a member of the given cover, the affine opens being a basis. -/
theorem exists_affineRefinement (A : CrystallineThickening S) {I : Type (u + 1)}
    (V : I → A.obj.thickening.target.scheme.Opens)
    (hcov : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i) :
    ∃ W : ULift.{u + 1} A.obj.thickening.target.scheme →
        A.obj.thickening.target.scheme.Opens,
      (∀ j, IsAffineOpen (W j)) ∧ (∀ x, ∃ j, x ∈ W j) ∧ (∀ j, ∃ i, W j ≤ V i) := by
  classical
  have hx : ∀ x : A.obj.thickening.target.scheme,
      ∃ W : A.obj.thickening.target.scheme.Opens, IsAffineOpen W ∧ x ∈ W ∧ ∃ i, W ≤ V i := by
    intro x
    obtain ⟨i, hi⟩ := hcov x
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨W, hW, hxW, i, hWV⟩
  choose W hWaff hWmem hWle using hx
  exact ⟨fun j ↦ W j.down, fun j ↦ hWaff j.down, fun x ↦ ⟨ULift.up x, hWmem x⟩,
    fun j ↦ hWle j.down⟩

end CrystallineThickening

/-- **`AffineCris(X/S)` is cover-dense in `Cris(X/S)`**: the morphisms out of affine objects
generate a covering sieve of every object of `Cris(X/S)`.  The restrictions of an object to a
cover of its ambient scheme by affine opens are affine objects and cover it. -/
theorem affineι_isCoverDense (S : GlobalCrystallineSituation.{u}) :
    (affineι S).IsCoverDense (smallTopology S) := by
  refine ⟨fun B ↦ ?_⟩
  obtain ⟨W, hW, hcov, -⟩ := CrystallineThickening.exists_affineRefinement B
    (fun _ : PUnit.{u + 2} ↦ ⊤) fun x ↦ ⟨⟨⟩, trivial⟩
  refine (smallTopology S).superset_covering ?_
    (smallZariskiCovering_mem_smallTopology S _
      (CrystallineThickening.isZariskiCovering_restrictOpenCover B W hcov))
  rw [Sieve.generate_le_iff]
  rintro Z k ⟨i⟩
  exact Presieve.in_coverByImage (affineι S)
    (show (affineι S).obj (AffineCrystallineThickening.restrictOpen B (hW i)) ⟶ B from
      B.restrictOpenHom (W i))

/-- **The inclusion `AffineCris(X/S) ⥤ Cris(X/S)` is cocontinuous**: a covering sieve of an
affine object in the small crystalline site pulls back to a covering sieve of the affine
crystalline site.

The topology of `Cris(X/S)` is generated by the coverage of families of restrictions of an object
to an open cover of its ambient scheme, `restrictCoverage_toGrothendieck`, so it is enough to
treat such a family: refine it by affine opens and factor each refined restriction through the
member of the family that contains it. -/
theorem affineι_isCocontinuous (S : GlobalCrystallineSituation.{u}) :
    (affineι S).IsCocontinuous (affineTopology S) (smallTopology S) := by
  have hSat : ∀ {B : CrystallineThickening S} {R : Sieve B},
      Coverage.Saturate (restrictCoverage S) B R →
      ∀ (A : AffineCrystallineThickening S) (g : (affineι S).obj A ⟶ B),
        (R.pullback g).functorPullback (affineι S) ∈ affineTopology S A := by
    intro B R hR
    induction hR with
    | of B P hP =>
      intro A g
      obtain ⟨I, V, hVcov, rfl⟩ := hP
      obtain ⟨W, hWaff, hWcov, hWle⟩ :=
        CrystallineThickening.exists_affineRefinement A.obj
          (fun i ↦ g.hom.targetHom.hom ⁻¹ᵁ V i)
          fun x ↦ hVcov (g.hom.targetHom.hom.base x)
      refine (affineTopology S).superset_covering ?_
        (affineZariskiCovering_mem_affineTopology S _
          (AffineCrystallineThickening.isZariskiCovering_restrictOpenCover A W hWaff hWcov))
      rw [Sieve.generate_le_iff]
      rintro Z k ⟨j⟩
      obtain ⟨i, hi⟩ := hWle j
      obtain ⟨p, hp⟩ :=
        CrystallineThickening.exists_comp_restrictOpenHom_eq_of_le g (V i) (W j) hi
      exact ⟨B.restrictOpen (V i), p, B.restrictOpenHom (V i), ⟨i⟩, hp⟩
    | top B =>
      intro A g
      exact (affineTopology S).superset_covering (fun Z k _ ↦ trivial)
        ((affineTopology S).top_mem A)
    | transitive B R Q hR hQ ihR ihQ =>
      intro A g
      refine (affineTopology S).transitive (ihR A g) _ fun A₁ h hh ↦ ?_
      rw [← Sieve.functorPullback_pullback]
      simpa [← Sieve.pullback_comp, Category.assoc] using ihQ hh A₁ (𝟙 _)
  refine ⟨fun {A R} hR ↦ ?_⟩
  rw [← restrictCoverage_toGrothendieck] at hR
  simpa using hSat (Coverage.mem_toGrothendieck.mp hR) A (𝟙 _)

/-- **The coverings `AffineCris(X/S)` inherits from `Cris(X/S)` generate the topology restricted
from `Cris(X/S)` along the inclusion.**  One inclusion is monotonicity of the generated topology,
since a covering family of `AffineCris(X/S)` covers in `Cris(X/S)` by definition; the other is
cocontinuity, a sieve whose image covers being the pullback of that image. -/
theorem affineTopology_eq_restrictedTopology (S : GlobalCrystallineSituation.{u}) :
    affineTopology S = (affineι S).restrictedTopology (smallTopology S) := by
  have := affineι_isCoverDense S
  have := affineι_isCocontinuous S
  have hPmap : affinePrecoverage S ≤ ((smallTopology S).toPrecoverage).comap (affineι S) := by
    intro A R hR
    obtain ⟨E, rfl, hE⟩ := hR
    rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map,
      GrothendieckTopology.mem_toPrecoverage_iff]
    exact smallZariskiCovering_mem_smallTopology S (E.map (affineι S)) hE
  refine le_antisymm (Precoverage.toGrothendieck_monotone hPmap) fun A R hR ↦ ?_
  have hpull := Functor.cover_lift (G := affineι S) (J := affineTopology S)
    (K := smallTopology S)
    ((Functor.mem_restrictedTopology_iff (G := affineι S) (K := smallTopology S)).mp hR)
  rwa [Sieve.functorPullback_functorPushforward_eq] at hpull

/-- **The inclusion `AffineCris(X/S) ⥤ Cris(X/S)` is a special cocontinuous functor**,
[Stacks, Tag 03CG]: it is cocontinuous and exhibits the affine crystalline site as a dense
subsite of the small crystalline site.  This is the first reduction in the proof of
[Stacks, Tag 07JK], and its dense-subsite half is the equivalence of topoi
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, recorded below as `affineToposEquiv`. -/
theorem affineι_isSpecialCocontinuous (S : GlobalCrystallineSituation.{u}) :
    IsSpecialCocontinuous (affineTopology S) (smallTopology S) (affineι S) := by
  have := affineι_isCoverDense S
  have := affineι_isCocontinuous S
  refine ⟨inferInstance, ?_⟩
  rw [affineTopology_eq_restrictedTopology]
  infer_instance

/-- The inclusion exhibits `AffineCris(X/S)` as a dense subsite of `Cris(X/S)`, the second half
of `affineι_isSpecialCocontinuous`, as an instance. -/
instance instIsDenseSubsiteAffineι (S : GlobalCrystallineSituation.{u}) :
    (affineι S).IsDenseSubsite (affineTopology S) (smallTopology S) :=
  (affineι_isSpecialCocontinuous S).2

/-- The inclusion is cocontinuous, the first half of `affineι_isSpecialCocontinuous`, as an
instance. -/
instance instIsCocontinuousAffineι (S : GlobalCrystallineSituation.{u}) :
    (affineι S).IsCocontinuous (affineTopology S) (smallTopology S) :=
  affineι_isCocontinuous S

/-- **Restriction along the inclusion is an equivalence of sheaf categories**,
`Sh(AffineCris(X/S)) ≌ Sh(Cris(X/S))`: the affine crystalline site and the small crystalline site
have the same sheaves.  This is the conclusion of [Stacks, Tag 03A0] carried by
`affineι_isSpecialCocontinuous`. -/
noncomputable def affineSheafEquiv (S : GlobalCrystallineSituation.{u}) (A : Type*)
    [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X (affineι S).op) A] :
    Sheaf (affineTopology S) A ≌ Sheaf (smallTopology S) A :=
  Functor.IsDenseSubsite.sheafEquiv (affineTopology S) (smallTopology S) (affineι S) A

/-- **The topos of the affine crystalline site is the crystalline topos `(X/S)_cris`.** -/
noncomputable def affineToposEquiv (S : GlobalCrystallineSituation.{u}) :
    Sheaf (affineTopology S) (Type (u + 1)) ≌ smallTopos S :=
  affineSheafEquiv S (Type (u + 1))

/-- **Abelian sheaves on the affine crystalline site are abelian sheaves on the small crystalline
site**, at the coefficient universe `u + 1` at which the cohomology of `Cris(X/S)` is defined in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Cohomology.lean`. -/
noncomputable def affineAbelianSheafEquiv (S : GlobalCrystallineSituation.{u}) :
    Sheaf (affineTopology S) AddCommGrpCat.{u + 1} ≌
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  affineSheafEquiv S AddCommGrpCat.{u + 1}

end Crystalline.GlobalCrystallineSituation.SmallSite

end
