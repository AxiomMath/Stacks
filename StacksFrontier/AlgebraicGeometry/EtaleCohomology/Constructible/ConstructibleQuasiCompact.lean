module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleObjectStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.JointlySurjectiveFamilyFaithful
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A constructible sheaf of sets is a quasi-compact object

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site. A constructible sheaf
of sets on the small étale site of `X` is a quasi-compact object of the topos, and consequently
receives an epimorphism from a finite coproduct of sheaves represented by quasi-compact and
quasi-separated objects of the site. The latter is the surjection half of Stacks 09Y9.

## Main results

All declarations below are in the namespace `AlgebraicGeometry`.

* `exists_finite_representable_epi_of_isConstructibleSetSheaf` — **the surjection half of Stacks
  09Y9**, with no hypothesis beyond quasi-compactness and quasi-separatedness of `X`.
* `isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`
  — **both directions of Stacks 09Y9**, likewise with no hypothesis beyond quasi-compactness and
  quasi-separatedness of `X`.

## Implementation notes

Quasi-compactness of a sheaf may be checked after inverse image along the members of a *finite*
jointly surjective family of morphisms of the site, those inverse images being jointly faithful
by Stacks 03PU and exact. The library already obtains such a family from a constructible
stratification, but only by making the inverse image to each stratum *representable*, which for
a merely finite locally constant sheaf needs effective descent of representability along an
étale covering — Stacks 0245 in the shape
`Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability`, which the library does not
prove.

Descent is not needed, because the family may be refined. Each stratum is quasi-compact, and on
it the inverse image is finite locally constant, so it becomes representable by an object with
finite structure morphism on some covering of the stratum — this is
`Stacks.EtaleCohomology.exists_cover_finiteEtaleRepresentable_final`, which is unconditional.
Refining that covering by affine objects and extracting a finite subfamily, which quasi-compactness
of the stratum and openness of the image of an étale morphism permit, yields a finite family on
each member of which the inverse image *is* representable: it is the base change to the affine
object of the representing object over the covering member, a finite morphism over an affine
scheme and therefore a quasi-compact object of the site. Composing with the immersions of the
strata gives one finite jointly surjective family over `X`.

The two isomorphisms that move the sheaf along the two steps of the refinement are Stacks 021J,
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso`, and Stacks 04D3 at the sheafified `ULift`
Yoneda embedding, `CategoryTheory.Sheaf.sheafifiedYonedaCompSheafPullbackIso`.

## References

* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 2000] Sheaf.instHasFiniteColimits

/-- A morphism of the small étale category of `P` to the final object is the structure morphism
of its source. -/
private theorem smallEtale_hom_left_to_final (B : BigEtaleSite.{u}) (P : B.Scheme)
    (V : SmallEtale B P.obj P.property)
    (g : V ⟶ SmallEtale.final B P.obj P.property) :
    g.hom.left = V.obj.hom := by
  have hw := Over.w g.hom
  simp only [SmallEtale.final, Over.mk_hom] at hw
  exact hw

/-- Every finite type is the image of a surjection from some `Fin n`. -/
private theorem exists_fin_surjective (ι : Type*) [Finite ι] :
    ∃ (n : ℕ) (e : Fin n → ι), Function.Surjective e := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨n, e.symm, e.symm.surjective⟩

/-- **A covering of a quasi-compact object is refined by a finite family of affine objects.**
Given a covering family `{Y l ⟶ P}` of the final object of the small étale category of a
quasi-compact `P`, there are finitely many affine objects of that category, each equipped with a
morphism to a member of the given family, whose structure morphisms are jointly surjective onto
`P`. -/
private theorem exists_finite_affine_refinement
    (B : BigEtaleSite.{u}) (P : B.Scheme) [CompactSpace P.obj]
    {I : Type (u + 1)} (Y : I → SmallEtale B P.obj P.property)
    (f : ∀ l, Y l ⟶ SmallEtale.final B P.obj P.property)
    (hcov : Sieve.ofArrows Y f ∈
      SmallEtale.topology B P.obj P.property (SmallEtale.final B P.obj P.property)) :
    ∃ (k : ℕ) (V : Fin k → SmallEtale B P.obj P.property) (l : Fin k → I)
      (_ : ∀ j, V j ⟶ Y (l j)),
      (∀ j, IsAffine ((SmallEtale.toScheme B P.obj P.property).obj (V j))) ∧
      ∀ p : B.inclusion.obj (B.obj P.obj P.property), ∃ j : Fin k,
        p ∈ Set.range (B.inclusion.map (V j).obj.hom) := by
  classical
  let T := SmallEtale.toScheme B P.obj P.property
  let points := ULift.{u + 1, u} P.obj
  have key : ∀ p : points, ∃ (l : I) (V : SmallEtale B P.obj P.property)
      (_ : V ⟶ Y l) (q : T.obj V), IsAffine (T.obj V) ∧
        (B.inclusion.map V.obj.hom) q = p.down := by
    intro p
    obtain ⟨V₀, arrow₀, harrow₀, pre₀, hpre₀⟩ := smallEtale_coveringSieve_pointwise B P
      (Precoverage.mem_toGrothendieck_iff.mp hcov) p.down
    obtain ⟨l₀, factor₀, rfl⟩ := (Sieve.mem_ofArrows_iff Y f arrow₀).mp harrow₀
    obtain ⟨IA, W, arrowsW, hcovW, haffW⟩ := exists_affine_cover_smallEtale B P (Y l₀)
    obtain ⟨V₁, arrow₁, harrow₁, pre₁, hpre₁⟩ := smallEtale_coveringSieve_pointwise B P
      (Precoverage.mem_toGrothendieck_iff.mp hcovW) (T.map factor₀ pre₀)
    obtain ⟨μ, factor₁, rfl⟩ := (Sieve.mem_ofArrows_iff W arrowsW arrow₁).mp harrow₁
    refine ⟨l₀, W μ, arrowsW μ, T.map factor₁ pre₁, haffW μ, ?_⟩
    have h₁ : T.map (arrowsW μ) (T.map factor₁ pre₁) = T.map factor₀ pre₀ := by
      rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    rw [← smallEtale_hom_left_to_final B P (W μ) (arrowsW μ ≫ f l₀)]
    show T.map (arrowsW μ ≫ f l₀) (T.map factor₁ pre₁) = p.down
    rwa [Functor.map_comp, Scheme.Hom.comp_apply, h₁, ← Scheme.Hom.comp_apply,
      ← Functor.map_comp]
  choose l V a q haffine hpoint using key
  have hopen : ∀ p : points, IsOpen (Set.range (B.inclusion.map (V p).obj.hom)) := by
    intro p
    simpa using (B.inclusion.map (V p).obj.hom).isOpenMap _ isOpen_univ
  have hcoverage : (Set.univ : Set (B.inclusion.obj (B.obj P.obj P.property))) ⊆
      ⋃ p : points, Set.range (B.inclusion.map (V p).obj.hom) :=
    fun p _ => Set.mem_iUnion.mpr ⟨⟨p⟩, q ⟨p⟩, hpoint ⟨p⟩⟩
  obtain ⟨selected, hselected⟩ :=
    (@isCompact_univ _ _ (inferInstanceAs (CompactSpace P.obj))).elim_finite_subcover
    (fun p : points => Set.range (B.inclusion.map (V p).obj.hom)) hopen hcoverage
  obtain ⟨n, e, he⟩ := exists_fin_surjective selected
  refine ⟨n, fun j => V (e j : points), fun j => l (e j : points),
    fun j => a (e j : points), fun j => haffine (e j : points), fun p => ?_⟩
  obtain ⟨chosen, hchosen, hmem⟩ := Set.mem_iUnion₂.mp (hselected (Set.mem_univ p))
  obtain ⟨j, rfl⟩ : ∃ j, (e j : points) = chosen :=
    (he ⟨chosen, hchosen⟩).imp fun _ => congrArg Subtype.val
  exact ⟨j, hmem⟩

/-- **Over an affine object mapping into a member of a trivializing covering, the inverse image
of the sheaf is quasi-compact.** The inverse image along the structure morphism factors through
the inverse image along the member, where the sheaf is represented by an object with finite
structure morphism; base-changing that object to the affine gives a finite object over an affine
scheme, hence a quasi-compact one. -/
private theorem isQuasiCompact_pullback_of_affine_refinement
    (B : BigEtaleSite.{u}) (P : B.Scheme)
    (G : Sheaf (SmallEtale.topology B P.obj P.property) (Type (u + 1)))
    (Y V : SmallEtale B P.obj P.property) (a : V ⟶ Y)
    (haff : IsAffine ((SmallEtale.toScheme B P.obj P.property).obj V))
    (U : SmallEtale B Y.obj.left.obj Y.obj.left.property)
    (hU : IsFinite (B.inclusion.map U.obj.hom))
    (e : ((smallEtaleBaseChange B Y.obj.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B P.obj P.property)
        (SmallEtale.topology B Y.obj.left.obj Y.obj.left.property)).obj G ≅
      (Sheaf.sheafifiedYoneda
        (SmallEtale.topology B Y.obj.left.obj Y.obj.left.property)).obj U) :
    Sheaf.IsQuasiCompact
      (((smallEtaleBaseChange B V.obj.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B P.obj P.property)
        (SmallEtale.topology B V.obj.left.obj V.obj.left.property)).obj G) := by
  rw [show V.obj.hom = a.hom.left ≫ Y.obj.hom from (Over.w a.hom).symm]
  let pullbackA := (smallEtaleBaseChange B a.hom.left).sheafPullback (Type (u + 1))
    (SmallEtale.topology B Y.obj.left.obj Y.obj.left.property)
    (SmallEtale.topology B V.obj.left.obj V.obj.left.property)
  let U' := (smallEtaleBaseChange B a.hom.left).obj U
  let eComp := smallEtaleSheafPullbackCompIso B V.obj.left Y.obj.left P a.hom.left Y.obj.hom
    (Type (u + 1))
  let eRep := (Sheaf.sheafifiedYonedaCompSheafPullbackIso (smallEtaleBaseChange B a.hom.left)
    (SmallEtale.topology B Y.obj.left.obj Y.obj.left.property)
    (SmallEtale.topology B V.obj.left.obj V.obj.left.property)).app U
  have htotal : (((smallEtaleBaseChange B (a.hom.left ≫ Y.obj.hom)).sheafPullback
      (Type (u + 1)) (SmallEtale.topology B P.obj P.property)
      (SmallEtale.topology B V.obj.left.obj V.obj.left.property)).obj G) ≅
      (Sheaf.sheafifiedYoneda
        (SmallEtale.topology B V.obj.left.obj V.obj.left.property)).obj U' :=
    (eComp.app G).symm ≪≫ pullbackA.mapIso e ≪≫ eRep
  have hfin : IsFinite (B.inclusion.map U'.obj.hom) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback U.obj.hom a.hom.left).map B.inclusion) hU
  have haffV : IsAffine (B.inclusion.obj V.obj.left) := haff
  have hcompV : CompactSpace (B.inclusion.obj V.obj.left) := inferInstance
  have hcompU : CompactSpace
      ((SmallEtale.toScheme B V.obj.left.obj V.obj.left.property).obj U') :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map U'.obj.hom)
  exact isQuasiCompact_of_iso _ htotal.symm
    ((GrothendieckTopology.isQuasiCompactObject_iff_isQuasiCompact_sheafifiedYoneda _ _).mp
      (smallEtale_isQuasiCompactObject B V.obj.left U'))

/-- **Quasi-compactness of a sheaf of sets may be checked after inverse image along the members
of a finite jointly surjective family**, the inverse images along such a family being jointly
faithful and exact. -/
private theorem isQuasiCompact_of_finite_family
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (hjf : ∀ {k : ℕ} (Y : Fin k → B.Scheme) (inclusions : ∀ i, Y i ⟶ X),
      (∀ x : X.obj, ∃ (i : Fin k) (y : (Y i).obj),
        (B.inclusion.map (inclusions i)) y = x) →
      JointlyFaithful (fun i =>
        (smallEtaleBaseChange B (inclusions i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (Y i).obj (Y i).property)))
    {k : ℕ} (Z : Fin k → B.Scheme) (g : ∀ i, Z i ⟶ X)
    (hsurj : ∀ x : X.obj, ∃ (i : Fin k) (y : (Z i).obj),
      (B.inclusion.map (g i)) y = x)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hqc : ∀ i, Sheaf.IsQuasiCompact
      (((smallEtaleBaseChange B (g i)).sheafPullback (Type (u + 1))
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (Z i).obj (Z i).property)).obj F)) :
    Sheaf.IsQuasiCompact F := by
  let restriction := fun i : Fin k =>
    (smallEtaleBaseChange B (g i)).sheafPullback (Type (u + 1))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (Z i).obj (Z i).property)
  have : ∀ i, PreservesColimitsOfSize.{u + 1, u + 1} (restriction i) := fun i =>
    ((smallEtaleBaseChange B (g i)).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (Z i).obj (Z i).property)).leftAdjoint_preservesColimits
  exact isQuasiCompact_of_jointlyFaithful_restrictions
    (SmallEtale.topology B X.obj X.property)
    (fun i => SmallEtale.topology B (Z i).obj (Z i).property) restriction (hjf Z g hsurj) F hqc

/-- The same with an arbitrary finite index type. -/
private theorem isQuasiCompact_of_fintype_family
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (hjf : ∀ {k : ℕ} (Y : Fin k → B.Scheme) (inclusions : ∀ i, Y i ⟶ X),
      (∀ x : X.obj, ∃ (i : Fin k) (y : (Y i).obj),
        (B.inclusion.map (inclusions i)) y = x) →
      JointlyFaithful (fun i =>
        (smallEtaleBaseChange B (inclusions i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (Y i).obj (Y i).property)))
    {ι : Type*} [Finite ι] (Z : ι → B.Scheme) (g : ∀ i, Z i ⟶ X)
    (hsurj : ∀ x : X.obj, ∃ (i : ι) (y : (Z i).obj), (B.inclusion.map (g i)) y = x)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hqc : ∀ i, Sheaf.IsQuasiCompact
      (((smallEtaleBaseChange B (g i)).sheafPullback (Type (u + 1))
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (Z i).obj (Z i).property)).obj F)) :
    Sheaf.IsQuasiCompact F := by
  obtain ⟨n, e, he⟩ := exists_fin_surjective ι
  refine isQuasiCompact_of_finite_family B X hjf (fun j => Z (e j)) (fun j => g (e j)) ?_ F
    (fun j => hqc (e j))
  intro x
  obtain ⟨i, hi⟩ := hsurj x
  obtain ⟨j, rfl⟩ := he i
  exact ⟨j, hi⟩

/-- **Stacks 09Y9, the quasi-compactness step, with no descent hypothesis.** A constructible
sheaf of sets on the small étale site of a quasi-compact and quasi-separated scheme is a
quasi-compact object of the topos.

Quasi-compactness may be checked after inverse image along a finite jointly surjective family of
morphisms of the site, and such a family is available with no appeal to descent: each stratum of
a constructible stratification is quasi-compact, the inverse image of the sheaf to it is finite
locally constant, hence becomes representable by a finite étale object on a covering, and that
covering is refined by finitely many affine objects which still cover the stratum. -/
private theorem isQuasiCompact_of_isConstructibleSetSheaf_unconditional
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hjf : ∀ {k : ℕ} (Y : Fin k → B.Scheme) (inclusions : ∀ i, Y i ⟶ X),
      (∀ x : X.obj, ∃ (i : Fin k) (y : (Y i).obj),
        (B.inclusion.map (inclusions i)) y = x) →
      JointlyFaithful (fun i =>
        (smallEtaleBaseChange B (inclusions i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (Y i).obj (Y i).property)))
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) : Sheaf.IsQuasiCompact F := by
  classical
  obtain ⟨strat, hstrat⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B X F).mp hF
  have key : ∀ i : Fin strat.n, ∃ (k : ℕ) (V : Fin k → SmallEtale B
      (strat.piece i).obj (strat.piece i).property),
      (∀ p : B.inclusion.obj (B.obj (strat.piece i).obj (strat.piece i).property),
        ∃ j, p ∈ Set.range (B.inclusion.map (V j).obj.hom)) ∧
      ∀ j, Sheaf.IsQuasiCompact
        (((smallEtaleBaseChange B ((V j).obj.hom ≫ strat.inclusion i)).sheafPullback
          (Type (u + 1)) (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (V j).obj.left.obj (V j).obj.left.property)).obj F) := by
    intro i
    have hcompP : CompactSpace (strat.piece i).obj :=
      compactSpace_constructibleStratification_piece B X strat i
    have hfl := hstrat i
    obtain ⟨I, Y, f, hcovI, hrep⟩ :=
      Stacks.EtaleCohomology.exists_cover_finiteEtaleRepresentable_final B (strat.piece i)
        (((smallEtaleBaseChange B (strat.inclusion i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (strat.piece i).obj (strat.piece i).property)).obj F)
    obtain ⟨k, V, l, a, haff, hsurjP⟩ :=
      exists_finite_affine_refinement B (strat.piece i) Y f hcovI
    refine ⟨k, V, hsurjP, fun j => ?_⟩
    obtain ⟨U, hU, ⟨e⟩⟩ := hrep (l j)
    exact isQuasiCompact_of_iso _
      ((smallEtaleSheafPullbackCompIso B (V j).obj.left (strat.piece i) X (V j).obj.hom
        (strat.inclusion i) (Type (u + 1))).app F)
      (isQuasiCompact_pullback_of_affine_refinement B (strat.piece i)
        (((smallEtaleBaseChange B (strat.inclusion i)).sheafPullback (Type (u + 1))
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (strat.piece i).obj (strat.piece i).property)).obj F)
        (Y (l j)) (V j) (a j) (haff j) U hU e)
  choose k V hsurjP hqcP using key
  refine isQuasiCompact_of_fintype_family B X hjf
    (ι := (i : Fin strat.n) × Fin (k i))
    (fun c => (V c.1 c.2).obj.left) (fun c => (V c.1 c.2).obj.hom ≫ strat.inclusion c.1)
    ?_ F (fun c => hqcP c.1 c.2)
  intro x
  have hpoint : x ∈ ⋃ i, Set.range (B.inclusion.map (strat.inclusion i)).base := by
    rw [← strat.covers]
    trivial
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hpoint
  obtain ⟨j, w, hw⟩ := hsurjP i z
  refine ⟨⟨i, j⟩, w, ?_⟩
  rwa [Functor.map_comp, Scheme.Hom.comp_apply, hw]

/-- **Stacks 09Y9, the surjection half.** A constructible sheaf of sets on the small étale site
of a quasi-compact and quasi-separated scheme receives an epimorphism from a finite coproduct of
sheaves represented by quasi-compact and quasi-separated objects of the site.

This is `AlgebraicGeometry.isQuasiCompact_of_isConstructibleSetSheaf_unconditional` followed by
the presentation of a quasi-compact sheaf by finitely many affine representables; both the
conservativity of geometric points and the finite affine covering it uses are theorems of the
library, so nothing is assumed. -/
@[stacks 09Y9 "the surjection half: a constructible sheaf of sets on a quasi-compact \
quasi-separated scheme is the target of an epimorphism from a finite coproduct of sheaves \
represented by quasi-compact quasi-separated objects"]
public theorem exists_finite_representable_epi_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i)) ∧
        QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i))) ∧
      ∃ p : (∐ fun i ↦ (Sheaf.sheafifiedYoneda
        (SmallEtale.topology B X.obj X.property)).obj (U i)) ⟶ F, Epi p :=
  exists_finite_affineRepresentable_epi_of_isQuasiCompact B X F
    (isQuasiCompact_of_isConstructibleSetSheaf_unconditional B X
      (fun Y inclusions hs => jointlyFaithful_smallEtaleSetPullback B X Y inclusions hs) F hF)

/-- **Stacks Project, Tag 09Y9.** On a quasi-compact and quasi-separated scheme the
constructible sheaves of sets on the small étale site are exactly the sheaves admitting a
coequalizer presentation by finite coproducts of sheaves represented by quasi-compact and
quasi-separated étale objects.

Nothing beyond quasi-compactness and quasi-separatedness of `X` is assumed. Stacks 03S0 is
`AlgebraicGeometry.etaleFiniteStratificationExists` and the conservativity of geometric points of
Stacks 03PU is `AlgebraicGeometry.jointlyFaithful_smallEtaleSetPullback`, both theorems of the
library. Stacks 0245 is not used at all: the quasi-compactness step is
`AlgebraicGeometry.isQuasiCompact_of_isConstructibleSetSheaf_unconditional` above, which refines
the covering produced by étale-local representability instead of descending along it. -/
@[stacks 09Y9 "both directions", sga "4 IX 2.7", sga "4 IX 2.7.1" "Sufficiency"]
public theorem
    isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      HasFiniteQCSRepresentableCoequalizerPresentation B X F := by
  have hstrat : ∀ U : SmallEtale B X.obj X.property,
      CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj U) →
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj U) →
      HasFiniteEtaleStratification B X U := fun U hc hq =>
    etaleFiniteStratificationExists B X U inferInstance inferInstance ⟨hc, hq⟩
  constructor
  · intro hF
    have hgen : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)),
        IsConstructibleSetSheaf B X G →
          ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
            (∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i)) ∧
              QuasiSeparatedSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i))) ∧
            let : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property)
                (Type (u + 1))) := CategoryTheory.Sheaf.instHasFiniteColimits
            let : HasColimitsOfShape (Discrete (Fin n))
                (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
              HasFiniteColimits.out _
            ∃ p : (∐ fun i =>
              (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U i))
                ⟶ G, Epi p :=
      exists_finite_representable_epi_of_isConstructibleSetSheaf B X
    obtain ⟨n, U, hU, p, hp⟩ := hgen F hF
    have hsource := isConstructibleSetSheaf_colimit B X
      (Discrete.functor fun i =>
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U i))
      (isConstructibleSetSheaf_sigma_sheafifiedYoneda B X hstrat U hU)
    have hkernelPair : IsConstructibleSetSheaf B X (pullback p p) := by
      apply isConstructibleSetSheaf_limit
      intro vertex
      cases vertex with
      | none => exact hF
      | some vertex => cases vertex <;> exact hsource
    obtain ⟨m, V, hV, q, hq⟩ := hgen (pullback p p) hkernelPair
    exact ⟨n, m, U, V, hU, hV, q ≫ pullback.fst p p, q ≫ pullback.snd p p,
      coequalizer_kernelPair_epi_comp_iso p q⟩
  · rintro ⟨n, m, U, V, hU, hV, f, g, ⟨e⟩⟩
    refine isConstructibleSetSheaf_congr B X e
      (isConstructibleSetSheaf_colimit B X (parallelPair f g) ?_)
    rintro (_ | _)
    · exact isConstructibleSetSheaf_colimit B X
        (Discrete.functor fun j =>
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (V j))
        (isConstructibleSetSheaf_sigma_sheafifiedYoneda B X hstrat V hV)
    · exact isConstructibleSetSheaf_colimit B X
        (Discrete.functor fun i =>
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U i))
        (isConstructibleSetSheaf_sigma_sheafifiedYoneda B X hstrat U hU)

end AlgebraicGeometry

end
