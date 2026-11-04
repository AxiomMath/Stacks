module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.StandardForm.Descent
public import StacksCore.Tactic.StacksAttribute

/-!
# Source locality from descent along morphisms in standard form

The affine descent hypothesis of the smooth, syntomic and étale cases of Tag 036H — condition
(4) of that lemma — only has to be checked along the morphisms in *standard* form. That is, a
property of morphisms of schemes which is Zariski local on the source and on the target and is
preserved by precomposition with smooth (respectively syntomic, respectively étale) morphisms
is local on the source for the smooth (respectively syntomic, respectively étale) topology as
soon as it descends along surjective **standard smooth** (respectively **standard syntomic**,
respectively **standard étale**) morphisms of affine schemes.

## Main results

* `AlgebraicGeometry.affine_descent_of_standardRefinement` is the criterion the three cases
  share, stated for an arbitrary topology and an arbitrary class of descent morphisms: it
  upgrades descent along surjective morphisms in standard form to descent along arbitrary
  surjective morphisms of the topology, between affine schemes.
* `AlgebraicGeometry.isLocalAtSource_smooth_of_standard_descent`,
  `AlgebraicGeometry.isLocalAtSource_syntomic_of_standard_descent` and
  `AlgebraicGeometry.isLocalAtSource_etale_of_standard_descent` are the three cases.
* `AlgebraicGeometry.isLocalAtSource_of_standard_descent` is **Stacks 036I**, the conjunction of
  the three.

## Implementation notes

The three statements are obtained from the corresponding cases of Tag 036H —
`AlgebraicGeometry.isLocalAtSource_smooth_of_affine_descent`,
`AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent` and
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent` — by feeding them an affine descent
hypothesis manufactured from the standard one. That manufacturing step is
`affine_descent_of_standardRefinement` and is where all the work is: given a surjective
`Q`-morphism `g : X' ⟶ X` of affine schemes with `P (g ≫ f)`, refine the one-member
`Q`-covering `{g}` of `X`, through open immersions, by a covering of `X` by affine schemes whose
structure morphisms are in standard form. Such a refinement is Tag 0222 for the smooth
topology, Tag 0228 for the syntomic one and
`AlgebraicGeometry.exists_affine_standardEtale_refinement` for the étale one.

A morphism in standard form need not be surjective, and the disjoint union of a family of
morphisms in standard form is not in standard form, so — unlike the general affine descent
criteria for these topologies — the proof cannot replace the refinement by the single morphism
out of the coproduct of the refining family. Instead the open image of each refining morphism
`V.f j` is covered by affine opens `D` of `X`, over each of which the base change
`pullback.fst D.ι (V.f j)` is a *surjective* morphism in standard form between affine schemes.
Its composite with `D.ι ≫ f` is `pullback.snd D.ι (V.f j) ≫ V.f j ≫ f`, which `P` satisfies
because `pullback.snd D.ι (V.f j)` is an open immersion, so the standard descent hypothesis
yields `P (D.ι ≫ f)`; the chosen affine opens cover `X`, and Zariski locality on the source
assembles `P f`.

## References

* [Stacks Project, Tag 036I](https://stacks.math.columbia.edu/tag/036I)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 0222](https://stacks.math.columbia.edu/tag/0222)
* [Stacks Project, Tag 0228](https://stacks.math.columbia.edu/tag/0228)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Descent along surjective `R`-morphisms of affine schemes upgrades to descent along
surjective `Q`-morphisms of affine schemes, for a property `P` that is Zariski local on the
source, provided `R` is stable under base change between affine schemes, consists of open maps,
and every `Q`-covering of an affine scheme is refined through open immersions by a covering by
affine schemes with structure morphisms in `R`.

This is the engine behind the three cases of Tag 036I: taking `R` to be the morphisms in
standard form, it says that condition (4) of Tag 036H only has to be checked along morphisms in
standard form. -/
theorem affine_descent_of_standardRefinement (P Q R : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P]
    (hdesc : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → R g → P (g ≫ f) → P f)
    (hRbase : ∀ {U S W : Scheme.{u}} [IsAffine U] [IsAffine S] [IsAffine W]
      (g : U ⟶ S) (w : W ⟶ S), R g → R (pullback.fst w g))
    (hRopen : ∀ {U S : Scheme.{u}} [IsAffine U] [IsAffine S]
      (g : U ⟶ S), R g → IsOpenMap g)
    (hrefine : ∀ {T : Scheme.{u}} [IsAffine T] (W : T.Cover.{u} (Scheme.precoverage Q)),
      ∃ (V : T.Cover.{u} (Scheme.precoverage Q))
        (r : V.toPreZeroHypercover.Hom W.toPreZeroHypercover),
        (∀ j, IsAffine (V.X j)) ∧ (∀ j, R (V.f j)) ∧
          ∀ j, IsOpenImmersion (r.h₀ j))
    {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
    (g : X' ⟶ X) (f : X ⟶ Y) (hgsurj : Surjective g) (hgQ : Q g) (hgf : P (g ≫ f)) : P f := by
  let W : X.Cover.{u} (Scheme.precoverage Q) :=
    Scheme.Cover.mkOfCovers (P := Q) PUnit.{u + 1} (fun _ ↦ X') (fun _ ↦ g)
      (fun x ↦ ⟨⟨⟩, ((surjective_iff g).mp hgsurj x).choose,
        ((surjective_iff g).mp hgsurj x).choose_spec⟩) (fun _ ↦ hgQ)
  obtain ⟨V, r, hVaffine, hVR, hVopen⟩ := hrefine W
  choose e he hef using fun j : V.I₀ ↦
    (⟨r.h₀ j, hVopen j, r.w₀ j⟩ :
      ∃ e : V.X j ⟶ X', IsOpenImmersion e ∧ e ≫ g = V.f j)
  have hVP (j : V.I₀) : P (V.f j ≫ f) := by
    have : IsOpenImmersion (e j) := he j
    rw [← hef j, Category.assoc]
    exact IsZariskiLocalAtSource.comp hgf (e j)
  let O (j : V.I₀) : X.Opens := by
    have : IsAffine (V.X j) := hVaffine j
    exact ⟨Set.range (V.f j).base, (hRopen (V.f j) (hVR j)).isOpen_range⟩
  have hO (x : X) : x ∈ O (V.idx x) := V.covers x
  choose D hDaffine hxD hDle using fun x : X ↦
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := O (V.idx x)) (hO x)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P) (f := f) D ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    simpa only [TopologicalSpace.Opens.mem_iSup] using ⟨x, hxD x⟩
  · have : IsAffine (D x).toScheme := hDaffine x
    have : IsAffine (V.X (V.idx x)) := hVaffine (V.idx x)
    have hsurj : Surjective (pullback.fst (D x).ι (V.f (V.idx x))) := by
      rw [surjective_iff]
      intro a
      obtain ⟨y, hy⟩ := hDle x a.property
      obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback (D x).ι (V.f (V.idx x))) a y hy.symm
      exact ⟨z, hz⟩
    have hcomp : P (pullback.fst (D x).ι (V.f (V.idx x)) ≫ (D x).ι ≫ f) := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
      exact IsZariskiLocalAtSource.comp (hVP (V.idx x))
        (pullback.snd (D x).ι (V.f (V.idx x)))
    exact hdesc _ _ hsurj (hRbase (V.f (V.idx x)) (D x).ι (hVR (V.idx x))) hcomp

/-- Descent along surjective `Q`-morphisms of affine schemes follows from descent along the
surjective morphisms of affine schemes satisfying an affine predicate `Std`, when `Std` is
stable under base change, consists of open maps, and every `Q`-covering of an affine scheme is
refined by a covering by affine schemes with `Std` structure morphisms. -/
private theorem affine_descent_of_standard (P Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P]
    (Std : ∀ {A B : Scheme.{u}} [IsAffine A] [IsAffine B], (A ⟶ B) → Prop)
    (hdesc : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Std g → P (g ≫ f) → P f)
    (hbase : ∀ {U S W : Scheme.{u}} [IsAffine U] [IsAffine S] [IsAffine W]
      (g : U ⟶ S) (w : W ⟶ S), Std g → Std (pullback.fst w g))
    (hopen : ∀ {U S : Scheme.{u}} [IsAffine U] [IsAffine S] (g : U ⟶ S), Std g → IsOpenMap g)
    (hrefine : ∀ {T : Scheme.{u}} [IsAffine T] (W : T.Cover.{u} (Scheme.precoverage Q)),
      ∃ (V : T.Cover.{u} (Scheme.precoverage Q))
        (r : V.toPreZeroHypercover.Hom W.toPreZeroHypercover),
        (∀ j, IsAffine (V.X j)) ∧ (∀ j (_ : IsAffine (V.X j)) (_ : IsAffine T), Std (V.f j)) ∧
          ∀ j, IsOpenImmersion (r.h₀ j))
    {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
    (g : X' ⟶ X) (f : X ⟶ Y) (hgsurj : Surjective g) (hgQ : Q g) (hgf : P (g ≫ f)) : P f :=
  affine_descent_of_standardRefinement P Q
    (fun {A B} g ↦ ∀ (_ : IsAffine A) (_ : IsAffine B), Std g)
    (fun {_ _ _} _ _ _ g f hgs hg hgf ↦ hdesc g f hgs (hg inferInstance inferInstance) hgf)
    (fun {_ _ _} _ _ _ g w hg _ _ ↦ hbase g w (hg inferInstance inferInstance))
    (fun {_ _} _ _ g hg ↦ hopen g (hg inferInstance inferInstance)) hrefine g f hgsurj hgQ hgf

/-- **Stacks Project, Tag 036I, smooth case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, and which is preserved by precomposition with
smooth morphisms, is smooth local on the source as soon as it descends along surjective
*standard smooth* morphisms of affine schemes.

This strengthens condition (4) of the smooth case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_smooth_of_affine_descent`, where descent is assumed along
every surjective smooth morphism of affine schemes. -/
theorem isLocalAtSource_smooth_of_standard_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Smooth.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardSmooth g → P (g ≫ f) → P f) :
    P.IsLocalAtSource (Scheme.precoverage (@Smooth.{u})) := by
  refine isLocalAtSource_smooth_of_affine_descent P
    (affine_descent_of_standard P (@Smooth.{u}) @IsStandardSmooth hAffine
      isStandardSmooth_pullback_fst
      (fun {_ _} _ _ g hg ↦ ?_) (fun {_} _ W ↦ ?_))
  · have : Smooth g :=
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
        (RingHom.IsStandardSmooth.smooth hg)
    exact g.isOpenMap
  · obtain ⟨V, r, -, hstd, hopen⟩ := exists_finite_affine_standardSmooth_refinement W
    exact ⟨V.cover, r, fun j ↦ inferInstanceAs (IsAffine (Spec (V.X j))),
      fun j _ _ ↦ hstd j, hopen⟩

/-- **Stacks Project, Tag 036I, syntomic case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, and which is preserved by precomposition with
syntomic morphisms, is syntomic local on the source as soon as it descends along surjective
*standard syntomic* morphisms of affine schemes.

This strengthens condition (4) of the syntomic case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent`, where descent is assumed along
every surjective syntomic morphism of affine schemes. -/
theorem isLocalAtSource_syntomic_of_standard_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Syntomic.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardSyntomic g → P (g ≫ f) → P f) :
    P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u})) := by
  refine isLocalAtSource_syntomic_of_affine_descent P
    (affine_descent_of_standard P (@Syntomic.{u}) @IsStandardSyntomic hAffine
      isStandardSyntomic_pullback_fst
      (fun {_ _} _ _ g hg ↦ ?_) (fun {_} _ W ↦ ?_))
  · have : UniversallyOpen g :=
      universallyOpen_of_syntomic
        (syntomic_of_standardSyntomic hg)
    exact g.isOpenMap
  · have hcover : IsSyntomicCovering W.X W.f := by
      obtain ⟨hcov, hsyn⟩ :=
        (Scheme.presieve₀_mem_precoverage_iff W.toPreZeroHypercover).mp W.mem₀
      exact ⟨hsyn, Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_iUnion.mpr (hcov x)⟩
    obtain ⟨V, r, -, hstd, hopen⟩ :=
      exists_finite_affine_standardSyntomic_refinement W.toPreZeroHypercover hcover
    exact ⟨V.cover, r, fun j ↦ inferInstanceAs (IsAffine (Spec (V.X j))),
      fun j _ _ ↦ hstd j, hopen⟩

/-- **Stacks Project, Tag 036I, étale case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, and which is preserved by precomposition with
étale morphisms, is étale local on the source as soon as it descends along surjective *standard
étale* morphisms of affine schemes.

This strengthens condition (4) of the étale case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, where descent is assumed along
every surjective étale morphism of affine schemes. -/
theorem isLocalAtSource_etale_of_standard_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Etale.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardEtale g → P (g ≫ f) → P f) :
    P.IsLocalAtSource Scheme.etalePrecoverage := by
  refine isLocalAtSource_etale_of_affine_descent P
    (affine_descent_of_standard P (@Etale.{u}) @IsStandardEtale hAffine
      isStandardEtale_pullback_fst
      (fun {U S} _ _ g hg ↦ ?_) (fun {_} _ W ↦ ?_))
  · let : Algebra Γ(S, ⊤) Γ(U, ⊤) := g.appTop.hom.toAlgebra
    let : Algebra.IsStandardEtale Γ(S, ⊤) Γ(U, ⊤) := hg
    have hring : g.appTop.hom.Etale :=
      RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale _ _)
    have : Etale g := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2 hring
    exact g.isOpenMap
  · exact exists_affine_standardEtale_refinement W

/-- **Stacks Project, Tag 036I.** In condition (4) of Tag 036H one may assume that the morphism
is a (surjective) *standard smooth* morphism when `τ = smooth`, a (surjective) *standard
syntomic* morphism when `τ = syntomic`, and a (surjective) *standard étale* morphism when
`τ = étale`.

The three conjuncts are the statements of the smooth, syntomic and étale cases of Tag 036H with
condition (4) so strengthened; they are
`AlgebraicGeometry.isLocalAtSource_smooth_of_standard_descent`,
`AlgebraicGeometry.isLocalAtSource_syntomic_of_standard_descent` and
`AlgebraicGeometry.isLocalAtSource_etale_of_standard_descent`. -/
@[stacks 036I]
theorem isLocalAtSource_of_standard_descent :
    (∀ (P : MorphismProperty Scheme.{u}) [P.RespectsLeft (@Smooth.{u})]
        [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P],
        (∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
          (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardSmooth g → P (g ≫ f) → P f) →
        P.IsLocalAtSource (Scheme.precoverage (@Smooth.{u}))) ∧
      (∀ (P : MorphismProperty Scheme.{u}) [P.RespectsLeft (@Syntomic.{u})]
        [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P],
        (∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
          (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardSyntomic g → P (g ≫ f) → P f) →
        P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))) ∧
      ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsLeft (@Etale.{u})]
        [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P],
        (∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
          (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → IsStandardEtale g → P (g ≫ f) → P f) →
        P.IsLocalAtSource Scheme.etalePrecoverage :=
  ⟨fun P _ _ _ ↦ isLocalAtSource_smooth_of_standard_descent P,
    fun P _ _ _ ↦ isLocalAtSource_syntomic_of_standard_descent P,
    fun P _ _ _ ↦ isLocalAtSource_etale_of_standard_descent P⟩

end AlgebraicGeometry

end
