module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.ClauseThree.GenericStalkInput
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FinitePresentationThickening
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Invariant affine neighbourhoods of finitely many generic orbits

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` finite and of finite
presentation and `U` quasi-separated, and let `u₁, …, u_m` be points of `U` whose orbits consist
of generic points of irreducible components of `U`. [Stacks, Tag 0ABC] produces `R`-invariant
subschemes `V' ⊆ V ⊆ U` with the `u_i` in `V'`, with `V` open in `U`, with `V'` and `V` affine,
with `V' ⊆ V` a thickening of finite presentation, and with the source and target of the
restricted groupoid finite locally free over `V'`.

That is what this file proves, with nothing assumed beyond the hypotheses of the tag. The one
external input is [Stacks, Tag 06AD] — *a thickening of an affine scheme is affine* — which is
proved in this repository as `Stacks.Thickenings.isAffine_of_isThickening`. See the
implementation notes.

The same construction with `U` locally Noetherian instead, and `s` and `t` merely finite, is
[Stacks, Tag 0ABD]; there the thickening is no longer claimed to be of finite presentation, and
nothing at all is carried, because on a locally Noetherian scheme the affineness of `V` follows
from [Stacks, Tag 01YQ].

## Main results

* `AlgebraicGeometry.exists_invariant_affine_open_of_finite_generic_orbits`: for a groupoid
  scheme with finite locally free source and target on a quasi-separated object scheme, finitely
  many points whose orbits consist of generic points of irreducible components have a common
  invariant affine open neighbourhood. No hypothesis is carried.
* `AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening'`:
  [Stacks, Tag 0ABC], with no hypothesis beyond its own. It is
  `AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening`, the same
  statement with [Stacks, Tag 06AD] carried as the hypothesis `H06AD`, with that hypothesis
  discharged by `Stacks.Thickenings.forall_isAffine_of_isThickening`.
* `AlgebraicGeometry.exists_invariant_affine_finiteLocallyFree_thickening_of_isLocallyNoetherian`:
  [Stacks, Tag 0ABD], with no hypothesis beyond its own.
* `AlgebraicGeometry.mem_of_mem_closure_of_mem_genericPoints`: on a locally Noetherian scheme a
  generic point of an irreducible component lying in the closure of an open subset lies in that
  open subset.

## Implementation notes

The construction follows the source. [Stacks, Tag 0ABA]
(`AlgebraicGeometry.layerUnionOpen`, `AlgebraicGeometry.layerThickening`,
`AlgebraicGeometry.layerThickeningInclusion`) supplies an invariant open `W` of the object scheme
together with an invariant closed thickening `W' ⊆ W` of finite presentation
([Stacks, Tag 0ABB], `AlgebraicGeometry.finitePresentation_layerThickeningInclusion`) over which
the restricted groupoid has finite locally free structure maps, and
`AlgebraicGeometry.mem_layerUnionOpen_of_orbit_subset_genericPoints` puts the given points in
`W`. The groupoid is restricted to `W'`, where
`AlgebraicGeometry.exists_invariant_affine_open_of_finite_generic_orbits` — which is
[Stacks, Tag 03JE] applied orbit by orbit, after separating the finitely many orbits into
pairwise disjoint affine opens with [Stacks, Tag 01ZV] — produces an invariant affine open of
`W'` containing the points. That open is `V'`; the open `V` of `W` matching it under the
homeomorphism of the thickening is the sought `V`, and it is cut out of `W` by no condition
other than being the matching open, so it is a thickening of `V'` of finite presentation.

**Where 06AD enters.** The one step not supplied by the construction above is that `V` is
affine. It is an open of `W` whose intersection with `W'` is the affine `V'`, so `V' ⊆ V` is a
thickening of an affine scheme, and its affineness is exactly [Stacks, Tag 06AD]. That tag is
proved in this repository as `Stacks.Thickenings.isAffine_of_isThickening`: a thickening is a
closed immersion, hence finite, and it is surjective, so this is the affineness of the target of
a finite surjective morphism with affine source ([Stacks, Tag 01ZT], [Stacks, Tag 04EX]).

`AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_isThickening` is the one place where 06AD
is used: it transports an affine open of the closed subscheme of a thickening to an affine open
of the ambient scheme with that preimage. It takes 06AD as the universally quantified hypothesis
`H06AD`, as does
`AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening` built on it;
`Stacks.Thickenings.forall_isAffine_of_isThickening` discharges it, which is what
`AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening'`, the form
carrying the tag, does.

**The locally Noetherian variant.** Under local Noetherianity of the object scheme nothing has to
be carried, and the finite presentation of the source map is not needed either. The two steps that
used it are replaced as follows. For the affineness of `V`, the thickening `V' ⊆ V` is a finite
surjective morphism onto a Noetherian scheme from an affine one, so [Stacks, Tag 01YQ]
(`Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective`) applies; this is
`AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_isThickening_of_isLocallyNoetherian`. For
the membership of the given points in `W`, the saturated closure of `W` is everything
(`AlgebraicGeometry.saturation_closure_layerUnion_eq_univ`), so some point of the orbit lies in
the closure of `W`; being a generic point of an irreducible component it then lies in `W` itself,
by `AlgebraicGeometry.mem_of_mem_closure_of_mem_genericPoints`, and invariance of `W` carries this
back to the given point. That topological step is where local Noetherianity enters: it makes every
open subset locally constructible, and a locally constructible subset not containing a generic
point of an irreducible component is avoided by a neighbourhood of it ([Stacks, Tag 0AAW]).

## References

* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 01ZV](https://stacks.math.columbia.edu/tag/01ZV)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0AAW](https://stacks.math.columbia.edu/tag/0AAW)
* [Stacks Project, Tag 0ABA](https://stacks.math.columbia.edu/tag/0ABA)
* [Stacks Project, Tag 0ABB](https://stacks.math.columbia.edu/tag/0ABB)
* [Stacks Project, Tag 0ABC](https://stacks.math.columbia.edu/tag/0ABC)
* [Stacks Project, Tag 0ABD](https://stacks.math.columbia.edu/tag/0ABD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

open scoped Set.Notation
open Stacks.Thickenings

universe u v

namespace AlgebraicGeometry

/-- The open of the ambient scheme matching an open of a thickening has that preimage, and the
restriction of the thickening over it is surjective. -/
private lemma exists_opens_preimage_eq_and_surjective {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) (V : X.Opens) :
    ∃ U : X'.Opens, i ⁻¹ᵁ U = V ∧ Function.Surjective (i ∣_ U) := by
  let : IsClosedImmersion i := hi.1
  let H : X ≃ₜ X' := hi.1.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hi.2
  have hpre : i ⁻¹ᵁ H.opensCongr V = V := by
    ext y
    change H.symm (i y) ∈ V ↔ y ∈ V
    rw [show H.symm (i y) = y from H.symm_apply_apply y]
  refine ⟨H.opensCongr V, hpre, ?_⟩
  intro z
  obtain ⟨y, hy⟩ := hi.2 z.1
  have hyU : y ∈ i ⁻¹ᵁ H.opensCongr V := by
    change i y ∈ H.opensCongr V
    simpa [hy] using z.2
  let y' : (i ⁻¹ᵁ H.opensCongr V).toScheme := ⟨y, hyU⟩
  refine ⟨y', ?_⟩
  apply Subtype.ext
  rw [morphismRestrict_base_coe]
  exact hy

/-- **An affine open of the closed subscheme of a thickening comes from an affine open of the
ambient scheme.** The open is the one matching it under the homeomorphism of the thickening; that
it is affine is [Stacks, Tag 06AD], carried here as the hypothesis `H06AD`. -/
theorem exists_isAffineOpen_preimage_eq_of_isThickening {X X' : Scheme.{u}}
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {i : X ⟶ X'} (hi : IsThickening i) {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ U : X'.Opens, IsAffineOpen U ∧ i ⁻¹ᵁ U = V := by
  obtain ⟨U, hpre, hsurj⟩ := exists_opens_preimage_eq_and_surjective hi V
  let : IsClosedImmersion i := hi.1
  refine ⟨U, ?_, hpre⟩
  exact H06AD _ _ (i ∣_ U) ⟨inferInstance, hsurj⟩ (by rw [hpre]; exact hV)

private def orbitOf {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (x : G.objects.left) : Set G.objects.left :=
  G.target.left.base '' (G.source.left.base ⁻¹' ({x} : Set G.objects.left))

private lemma orbitOf_finite {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (x : G.objects.left) : (orbitOf G x).Finite := by
  exact (G.source.left.finite_preimage_singleton x).image G.target.left.base

private lemma source_inverse_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (r : G.arrows.left) :
    G.source.left.base (G.inverse.left.base r) = G.target.left.base r := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base r) G.source_inverse

private lemma target_inverse_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (r : G.arrows.left) :
    G.target.left.base (G.inverse.left.base r) = G.source.left.base r := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base r) G.target_inverse

private lemma source_identity_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (x : G.objects.left) :
    G.source.left.base (G.identity.left.base x) = x := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base x) G.source_identity

private lemma target_identity_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (x : G.objects.left) :
    G.target.left.base (G.identity.left.base x) = x := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
    congrArg (fun f => f.left.base x) G.target_identity

private lemma over_eqToHom_apply_symm {S : Scheme} {X Y : Over S} (e : X = Y)
    (y : Y.left) :
    (eqToHom e).left ((eqToHom e.symm).left y) = y := by
  cases e
  rfl

private lemma exists_comp_point {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (a b : G.arrows.left)
    (hab : G.source.left.base a = G.target.left.base b) :
    ∃ c : G.arrows.left,
      G.source.left.base c = G.source.left.base b ∧
      G.target.left.base c = G.target.left.base a := by
  let T : Over S := Over.mk
    (pullback.fst G.source.left G.target.left ≫ G.source.left ≫ G.objects.hom)
  let u : T ⟶ G.arrows := Over.homMk (pullback.fst G.source.left G.target.left) (by
    dsimp [T]
    calc
      pullback.fst G.source.left G.target.left ≫ G.arrows.hom =
          pullback.fst G.source.left G.target.left ≫
            (G.source.left ≫ G.objects.hom) :=
        congrArg (fun k => pullback.fst G.source.left G.target.left ≫ k) G.source.w.symm
      _ = pullback.fst G.source.left G.target.left ≫ G.source.left ≫ G.objects.hom := by
        simp)
  let v : T ⟶ G.arrows := Over.homMk (pullback.snd G.source.left G.target.left) (by
    dsimp [T]
    calc
      pullback.snd G.source.left G.target.left ≫ G.arrows.hom =
          pullback.snd G.source.left G.target.left ≫
            (G.target.left ≫ G.objects.hom) :=
        congrArg (fun k => pullback.snd G.source.left G.target.left ≫ k) G.target.w.symm
      _ = pullback.fst G.source.left G.target.left ≫ G.source.left ≫ G.objects.hom := by
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun k => k ≫ G.objects.hom) pullback.condition.symm)
  have huv : u ≫ G.source = v ≫ G.target := by
    apply Over.OverMorphism.ext
    change pullback.fst G.source.left G.target.left ≫ G.source.left =
      pullback.snd G.source.left G.target.left ≫ G.target.left
    exact pullback.condition
  let l : T ⟶ pullback G.source G.target := pullback.lift u v huv
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  let q : (pullback G.source G.target).left := l.left p
  have hq₁ : (pullback.fst G.source G.target).left q = a := by
    have hproj := congrArg (fun f : T ⟶ G.arrows => f.left p) (pullback.lift_fst u v huv)
    exact hproj.trans hp₁
  have hq₂ : (pullback.snd G.source G.target).left q = b := by
    have hproj := congrArg (fun f : T ⟶ G.arrows => f.left p) (pullback.lift_snd u v huv)
    exact hproj.trans hp₂
  refine ⟨G.comp.left q, ?_, ?_⟩
  · have hs := congrArg (fun f => f.left.base q) G.source_comp
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hq₂] using hs
  · have ht := congrArg (fun f => f.left.base q) G.target_comp
    simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hq₁] using ht

/-- Arrows with the same target are related by an arrow whose target is the source of the first
and whose source is the source of the second. -/
private lemma exists_comp_point_of_target_eq {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (a r : G.arrows.left)
    (hat : G.target.left.base a = G.target.left.base r) :
    ∃ c : G.arrows.left, G.source.left.base c = G.source.left.base r ∧
      G.target.left.base c = G.source.left.base a := by
  obtain ⟨c, hcs, hct⟩ := exists_comp_point G (G.inverse.left.base a) r (by
    rw [source_inverse_apply]
    exact hat)
  exact ⟨c, hcs, by simpa [target_inverse_apply] using hct⟩

private lemma orbitOf_eq_of_intersects {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (x y : G.objects.left)
    (h : (orbitOf G x ∩ orbitOf G y).Nonempty) : orbitOf G x = orbitOf G y := by
  classical
  obtain ⟨z, hxz, hyz⟩ := h
  rcases hxz with ⟨a, hax, haz⟩
  rcases hyz with ⟨b, hby, hbz⟩
  obtain ⟨c, hcy, hcx⟩ := exists_comp_point_of_target_eq G a b (haz.trans hbz.symm)
  have hax' : G.source.left.base a = x := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hax
  have hby' : G.source.left.base b = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hby
  have hcx' : G.target.left.base c = x := hcx.trans hax'
  have hcy' : G.source.left.base c = y := by rw [hcy, hby']
  apply Set.Subset.antisymm
  · intro q hq
    rcases hq with ⟨d, hdx, hdq⟩
    have hdx' : G.source.left.base d = x := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hdx
    obtain ⟨e, hey, heq⟩ := exists_comp_point G d c (by rw [hdx', hcx'])
    exact ⟨e, hey.trans hcy', heq.trans hdq⟩
  · intro q hq
    rcases hq with ⟨d, hdy, hdq⟩
    have hdy' : G.source.left.base d = y := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hdy
    obtain ⟨e, hex, heq⟩ := exists_comp_point G d (G.inverse.left.base c) (by
      calc
        G.source.left.base d = y := hdy'
        _ = G.source.left.base c := hcy'.symm
        _ = G.target.left.base (G.inverse.left.base c) :=
          (target_inverse_apply G c).symm)
    refine ⟨e, ?_, heq.trans hdq⟩
    calc
      G.source.left.base e = G.source.left.base (G.inverse.left.base c) := hex
      _ = G.target.left.base c := source_inverse_apply G c
      _ = x := hcx'

private def orbitUnion {S : Scheme.{u}} {ι : Type v}
    (G : Stacks.Groupoids.GroupoidScheme S) (x : ι → G.objects.left) :
    Set G.objects.left := ⋃ i, orbitOf G (x i)

private lemma orbitUnion_finite {S : Scheme.{u}} {ι : Type v}
    [Finite ι] (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.source.left]
    (x : ι → G.objects.left) : (orbitUnion G x).Finite := by
  exact Set.finite_iUnion fun i => orbitOf_finite G (x i)

private lemma mem_iSup_opens {X : Scheme.{u}}
    {ι : Type v} (U : ι → X.Opens) (x : X) :
    x ∈ (⨆ i, U i) ↔ ∃ i, x ∈ U i := by
  change x ∈ ((⨆ i, U i : X.Opens) : Set X) ↔ ∃ i, x ∈ U i
  rw [TopologicalSpace.Opens.coe_iSup]
  change x ∈ ⋃ i : ι, (U i : Set X) ↔ ∃ i : ι, x ∈ (U i : Set X)
  simp only [Set.mem_iUnion]

/-- A point of the orbit union is a generic point of an irreducible component. -/
private lemma exists_component_of_mem_orbitUnion {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {ι : Type v} (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    (p : {y // y ∈ orbitUnion G x}) :
    ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint p.1 Z := by
  obtain ⟨i, r, hrs, hrt⟩ := Set.mem_iUnion.mp p.2
  exact hx i p.1 ⟨r, hrs, hrt⟩

private theorem exists_pairwise_disjoint_affine_orbit_neighborhoods
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [QuasiSeparatedSpace G.objects.left] [IsFinite G.source.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
      (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ V : {y // y ∈ orbitUnion G x} → G.objects.left.Opens,
      (∀ p, IsAffineOpen (V p)) ∧ (∀ p, p.1 ∈ V p) ∧
      Pairwise (fun p q => Disjoint (V p) (V q)) ∧
      IsAffineOpen (⨆ p, V p) := by
  classical
  let P := {y : G.objects.left // y ∈ orbitUnion G x}
  let : Finite P := (orbitUnion_finite G x).to_subtype
  choose Z hZ hη using exists_component_of_mem_orbitUnion G x hx
  have hZinj : Function.Injective Z := by
    intro p q hpq
    apply Subtype.ext
    exact (hη p).eq (hpq ▸ hη q)
  obtain ⟨V, hVaff, hVp, hVdisj, hVunion⟩ :=
    AlgebraicGeometry.exists_pairwise_disjoint_affine_opens_of_generic_points
      Z hZ hZinj (fun p : P => p.1) hη
  exact ⟨V, hVaff, hVp, hVdisj, hVunion⟩

private theorem exists_generic_point_component_open {X : Scheme.{u}}
    (W : X.Opens) (y : X) (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (hη : IsGenericPoint y Z) (hy : y ∈ W) :
    ∃ Z' ∈ irreducibleComponents W.toScheme,
      IsGenericPoint (⟨y, hy⟩ : W.toScheme) Z' := by
  let y' : W.toScheme := ⟨y, hy⟩
  let Z' : Set W.toScheme := Subtype.val ⁻¹' Z
  have hgen : IsGenericPoint y' Z' := by
    rw [isGenericPoint_def]
    ext p
    change p ∈ closure ({y'} : Set W.toScheme) ↔ p.1 ∈ Z
    have hclosure : p ∈ closure ({y'} : Set W.toScheme) ↔
        (fun q : W.toScheme => q.1) p ∈
          closure ((fun q : W.toScheme => q.1) '' ({y'} : Set W.toScheme)) := by
      exact closure_subtype
    rw [hclosure]
    simp only [Set.image_singleton]
    change p.1 ∈ closure ({y} : Set X) ↔ p.1 ∈ Z
    rw [hη.def]
  refine ⟨Z', ?_, hgen⟩
  refine ⟨hgen.isIrreducible, ?_⟩
  intro C hC hZ'C
  have hZsubset : Z ⊆ closure (Subtype.val '' C) := by
    rw [← hη.def]
    apply closure_mono
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact ⟨y', hZ'C hgen.mem, rfl⟩
  have hCimage : IsIrreducible (Subtype.val '' C) :=
    hC.image Subtype.val continuous_subtype_val.continuousOn
  have hmax : closure (Subtype.val '' C) ⊆ Z :=
    hZ.2 hCimage.closure hZsubset
  intro p hp
  change p.1 ∈ Z
  have hp' : p.1 ∈ closure (Subtype.val '' C) :=
    subset_closure ⟨p, hp, rfl⟩
  exact hmax hp'

private theorem exists_affine_open_of_generic_points_in_open {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (W : X.Opens) {ι : Type v} [Finite ι]
    (η : ι → X) (Z : ι → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hη : ∀ i, IsGenericPoint (η i) (Z i))
    (hηinj : Function.Injective η)
    (hW : ∀ i, η i ∈ W) :
    ∃ V : W.toScheme.Opens, IsAffineOpen V ∧
      ∀ i, (⟨η i, hW i⟩ : W.toScheme) ∈ V := by
  let Z' : ι → Set W.toScheme := fun i =>
    Classical.choose (exists_generic_point_component_open W (η i) (Z i) (hZ i)
      (hη i) (hW i))
  have hZ' : ∀ i, Z' i ∈ irreducibleComponents W.toScheme := by
    intro i
    exact (Classical.choose_spec (exists_generic_point_component_open W (η i) (Z i)
      (hZ i) (hη i) (hW i))).1
  have hη' : ∀ i, IsGenericPoint (⟨η i, hW i⟩ : W.toScheme) (Z' i) := by
    intro i
    exact (Classical.choose_spec (exists_generic_point_component_open W (η i) (Z i)
      (hZ i) (hη i) (hW i))).2
  have hZ'inj : Function.Injective Z' := by
    intro i j hij
    have hpoint : (⟨η i, hW i⟩ : W.toScheme) = ⟨η j, hW j⟩ :=
      (hη' i).eq (by simpa [hij] using hη' j)
    have hval : η i = η j := congrArg (fun p : W.toScheme => p.1) hpoint
    exact hηinj hval
  let : QuasiSeparatedSpace W.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding W.2.isOpenEmbedding_subtypeVal
  obtain ⟨V, hVaff, hVmem⟩ :=
    AlgebraicGeometry.exists_affine_open_containing_generic_points
      Z' hZ' hZ'inj (fun i => (⟨η i, hW i⟩ : W.toScheme)) hη'
  exact ⟨V, hVaff, hVmem⟩

private theorem exists_affine_open_containing_orbit_union_in_open
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [QuasiSeparatedSpace G.objects.left] [IsFinite G.source.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    (W : G.objects.left.Opens)
    (hW : ∀ y, y ∈ orbitUnion G x → y ∈ W) :
    ∃ V : W.toScheme.Opens, IsAffineOpen V ∧
      ∀ y hy, (⟨y, hW y hy⟩ : W.toScheme) ∈ V := by
  classical
  let P := {y : G.objects.left // y ∈ orbitUnion G x}
  let : Finite P := (orbitUnion_finite G x).to_subtype
  choose Z hZ hη using exists_component_of_mem_orbitUnion G x hx
  have hinj : Function.Injective (fun p : P => p.1) := fun _ _ h => Subtype.ext h
  obtain ⟨V, hVaff, hVmem⟩ := exists_affine_open_of_generic_points_in_open
    W (fun p : P => p.1) Z hZ hη hinj (fun p => hW p.1 p.2)
  refine ⟨V, hVaff, ?_⟩
  intro y hy
  exact hVmem ⟨y, hy⟩

private def invariantOpenInside {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.target.left]
    (W : G.objects.left.Opens) :
    G.objects.left.Opens :=
    ⟨(G.target.left.base '' (G.source.left.base ⁻¹' ((W : Set G.objects.left)ᶜ)))ᶜ,
    by
      have hclosed : IsClosed
          (G.target.left.base '' (G.source.left.base ⁻¹' ((W : Set G.objects.left)ᶜ))) := by
        exact G.target.left.isClosedMap _
          ((isClosed_compl_iff.mpr W.2).preimage G.source.left.continuous)
      exact hclosed.isOpen_compl⟩

private lemma invariantOpenInside_le {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.target.left]
    (W : G.objects.left.Opens) :
    invariantOpenInside G W ≤ W := by
  intro x hx
  change x ∉ G.target.left.base ''
    (G.source.left.base ⁻¹' ((W : Set G.objects.left)ᶜ)) at hx
  by_contra hxW
  apply hx
  refine ⟨G.identity.left.base x, ?_, target_identity_apply G x⟩
  change G.source.left.base (G.identity.left.base x) ∉ (W : Set G.objects.left)
  simpa [source_identity_apply G x] using hxW

private lemma invariantOpenInside_orbit {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.target.left]
    (W : G.objects.left.Opens)
    (x : G.objects.left)
    (hx : ∀ r : G.arrows.left,
      G.source.left.base r = x → G.target.left.base r ∈ W) :
    ∀ r : G.arrows.left, G.source.left.base r = x →
      G.target.left.base r ∈ invariantOpenInside G W := by
  intro r hrs
  change G.target.left.base r ∉
    G.target.left.base '' (G.source.left.base ⁻¹' ((W : Set G.objects.left)ᶜ))
  rintro ⟨a, ha, hat⟩
  obtain ⟨c, hcs, hct⟩ := exists_comp_point_of_target_eq G a r hat
  exact ha (hct ▸ hx c (hcs.trans hrs))

private lemma invariantOpenInside_isInvariant {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsFinite G.target.left]
    (W : G.objects.left.Opens) :
    Stacks.Groupoids.IsInvariantOpen G (invariantOpenInside G W) := by
  intro r hr
  change G.target.left.base r ∉
    G.target.left.base '' (G.source.left.base ⁻¹' ((W : Set G.objects.left)ᶜ))
  rintro ⟨a, ha, hat⟩
  obtain ⟨c, hcs, hct⟩ := exists_comp_point_of_target_eq G a r hat
  apply hr
  refine ⟨G.inverse.left.base c, ?_, ?_⟩
  · change G.source.left.base (G.inverse.left.base c) ∉ (W : Set G.objects.left)
    simpa [source_inverse_apply, hct] using ha
  · exact (target_inverse_apply G c).trans hcs

private lemma source_preimage_eq_target_preimage {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (U : G.objects.left.Opens)
    (hU : Stacks.Groupoids.IsInvariantOpen G U) :
    G.source.left ⁻¹ᵁ U = G.target.left ⁻¹ᵁ U := by
  ext r
  change G.source.left.base r ∈ (U : Set G.objects.left) ↔
    G.target.left.base r ∈ (U : Set G.objects.left)
  constructor
  · exact hU r
  · intro ht
    have hinv : G.source.left.base (G.inverse.left.base r) ∈ U := by
      change G.target.left.base r ∈ U at ht
      rw [source_inverse_apply]
      exact ht
    have h := hU (G.inverse.left.base r) hinv
    change G.target.left.base (G.inverse.left.base r) ∈ (U : Set G.objects.left) at h
    simpa only [target_inverse_apply] using h

private lemma isPullback_over_left {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left := by
  have h := IsPullback.of_isLimit_cone
    (isLimitOfPreserves (Over.forget S) (pullback.isLimit f g))
  simpa using h

private lemma isIso_snd_of_subobject_eq {C : Type*} [Category C]
    {D A B X : C} {a : D ⟶ A} {b : D ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    [Mono f] [Mono g] (h : IsPullback a b f g)
    (he : Subobject.mk f = Subobject.mk g) : IsIso b := by
  let e := Subobject.isoOfMkEqMk g f he.symm
  have he' : e.hom ≫ f = g := Subobject.ofMkLEMk_comp _
  let k : B ⟶ D := h.lift e.hom (𝟙 _) (by simpa using he')
  have hk : k ≫ b = 𝟙 _ := h.lift_snd _ _ _
  have hbk : b ≫ k = 𝟙 _ := by
    apply h.hom_ext
    · apply (cancel_mono f).mp
      simp only [Category.assoc, Category.id_comp, h.w, ← Category.assoc k b, hk]
    · simp [Category.assoc, hk]
  exact ⟨⟨k, hbk, hk⟩⟩

private lemma restriction_pullback_of_invariant {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {T : Over S} (g : T ⟶ G.objects)
    [Mono g.left] (hg : Stacks.Groupoids.IsInvariantMonomorphism G g.left) :
    IsPullback (restrictionArrowsToArrows G g).left
      (restrictionSource G g).left G.source.left g.left ∧
    IsPullback (restrictionArrowsToArrows G g).left
      (restrictionTarget G g).left G.target.left g.left := by
  let pt := pullback.snd g G.target
  let ps := pullback.fst G.source g
  have ht := isPullback_over_left g G.target
  have hs := isPullback_over_left G.source g
  have hd := isPullback_over_left pt ps
  let : Mono pt.left := ht.mono_snd_of_mono
  let : Mono ps.left := hs.mono_fst_of_mono
  have he : Subobject.mk pt.left = Subobject.mk ps.left := by
    rw [← Subobject.pullback_obj_mk ht, ← Subobject.pullback_obj_mk hs.flip]
    exact hg
  let : IsIso (pullback.snd pt ps).left := isIso_snd_of_subobject_eq hd he
  let : IsIso (pullback.fst pt ps).left := isIso_snd_of_subobject_eq hd.flip he.symm
  constructor
  · have htop : IsPullback (pullback.snd pt ps).left
        (restrictionArrowsToArrows G g).left ps.left (𝟙 _) :=
      IsPullback.of_horiz_isIso_mono ⟨by
        change _ = ((pullback.fst pt ps).left ≫ pt.left) ≫ 𝟙 _
        simpa only [Category.comp_id] using hd.w.symm⟩
    exact (htop.paste_horiz hs.flip).flip
  · have htop : IsPullback (pullback.fst pt ps).left
        (restrictionArrowsToArrows G g).left pt.left (𝟙 _) :=
      IsPullback.of_horiz_isIso_mono ⟨by
        change _ = ((pullback.fst pt ps).left ≫ pt.left) ≫ 𝟙 _
        rw [Category.comp_id]⟩
    exact (htop.paste_horiz ht).flip

private lemma invariantOpen_mono {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (U : G.objects.left.Opens) (hU : Stacks.Groupoids.IsInvariantOpen G U) :
    Stacks.Groupoids.IsInvariantMonomorphism G U.ι := by
  rw [Stacks.Groupoids.IsInvariantMonomorphism,
    Subobject.pullback_obj_mk (IsPullback.of_hasPullback G.target.left U.ι).flip,
    Subobject.pullback_obj_mk (IsPullback.of_hasPullback G.source.left U.ι).flip]
  apply Subobject.mk_eq_mk_of_comm _ _
    (IsOpenImmersion.isoOfRangeEq _ _ ?_) (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
  simp only [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
  change ((G.target.left ⁻¹ᵁ U : G.arrows.left.Opens) : Set G.arrows.left) =
    ((G.source.left ⁻¹ᵁ U : G.arrows.left.Opens) : Set G.arrows.left)
  exact congrArg (fun O : G.arrows.left.Opens => (O : Set G.arrows.left))
    (source_preimage_eq_target_preimage G U hU).symm

private lemma restriction_groupoid_pullback {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {T : Over S} (g : T ⟶ G.objects)
    [Mono g.left] (hg : Stacks.Groupoids.IsInvariantMonomorphism G g.left)
    (R : GroupoidScheme.Restriction G g) :
    IsPullback R.hom.mapArrows.left R.groupoid.source.left
      G.source.left R.hom.mapObjects.left ∧
    IsPullback R.hom.mapArrows.left R.groupoid.target.left
      G.target.left R.hom.mapObjects.left := by
  have h := restriction_pullback_of_invariant G g hg
  let ea := (Over.forget S).mapIso (eqToIso R.arrows_eq)
  let eo := (Over.forget S).mapIso (eqToIso R.objects_eq)
  constructor
  · apply h.1.of_iso' ea (Iso.refl _) eo (Iso.refl _)
    · simp [ea, R.mapArrows_eq]
    · simp [ea, eo, R.source_eq]
    · simp
    · simp [eo, R.mapObjects_eq]
  · apply h.2.of_iso' ea (Iso.refl _) eo (Iso.refl _)
    · simp [ea, R.mapArrows_eq]
    · simp [ea, eo, R.target_eq]
    · simp
    · simp [eo, R.mapObjects_eq]

private lemma invariant_image_of_pullback {S : Scheme.{u}}
    {H G : Stacks.Groupoids.GroupoidScheme S} (F : Stacks.Groupoids.GroupoidScheme.Hom H G)
    (hs : IsPullback F.mapArrows.left H.source.left G.source.left F.mapObjects.left)
    {A : Set H.objects.left} (hA : Stacks.Groupoids.IsInvariantSet H A) :
    Stacks.Groupoids.IsInvariantSet G (F.mapObjects.left '' A) := by
  intro r hr
  obtain ⟨x, hx, hrx⟩ := hr
  obtain ⟨q, hq, hqx⟩ := Scheme.exists_preimage_of_isPullback hs r x hrx.symm
  refine ⟨H.target.left q, hA q (hqx.symm ▸ hx), ?_⟩
  have h := congrArg (fun f => f.left q) F.map_target
  simpa [hq] using h.symm

private lemma invariant_comp_of_pullbacks {S : Scheme.{u}}
    {H G : Stacks.Groupoids.GroupoidScheme S} (F : Stacks.Groupoids.GroupoidScheme.Hom H G)
    [Mono F.mapObjects.left] [Mono F.mapArrows.left]
    (hs : IsPullback F.mapArrows.left H.source.left G.source.left F.mapObjects.left)
    (ht : IsPullback F.mapArrows.left H.target.left G.target.left F.mapObjects.left)
    {T : Scheme.{u}} (k : T ⟶ H.objects.left) [Mono k]
    (hk : Stacks.Groupoids.IsInvariantMonomorphism H k) :
    Stacks.Groupoids.IsInvariantMonomorphism G (k ≫ F.mapObjects.left) := by
  change (Subobject.pullback G.target.left).obj (Subobject.mk _) =
    (Subobject.pullback G.source.left).obj (Subobject.mk _)
  rw [← Subobject.map_mk]
  rw [← Subobject.map_pullback ht.flip.w ht.flip.isLimit,
    ← Subobject.map_pullback hs.flip.w hs.flip.isLimit, hk]

private lemma finiteLocallyFree_restriction_open {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (U : G.objects.left.Opens) (hU : Stacks.Groupoids.IsInvariantOpen G U)
    (R : GroupoidScheme.Restriction G
      (Over.homMk U.ι : Over.mk (U.ι ≫ G.objects.hom) ⟶ G.objects)) :
    Stacks.Morphisms.IsFiniteLocallyFree R.groupoid.source.left ∧
    Stacks.Morphisms.IsFiniteLocallyFree R.groupoid.target.left := by
  have h := restriction_groupoid_pullback G _ (invariantOpen_mono G U hU) R
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback h.1 inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h.2 inferInstance⟩

private theorem genericPointComponent_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {x : X} {Z : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hη : IsGenericPoint x Z) :
    ∃ Z' ∈ irreducibleComponents Y, IsGenericPoint (e x) Z' := by
  let Z' := e '' Z
  have hZclosed : IsClosed Z := hη.isClosed
  have hη' : IsGenericPoint (e x) Z' := by
    rw [isGenericPoint_def]
    calc
      closure ({e x} : Set Y) = closure (e '' ({x} : Set X)) := by
        simp
      _ = closure (e '' closure ({x} : Set X)) := by
        rw [← closure_image_closure e.continuous]
      _ = closure (e '' Z) := by rw [hη.def]
      _ = e '' Z := (e.isClosedMap _ hZclosed).closure_eq
      _ = Z' := rfl
  refine ⟨Z', ?_, hη'⟩
  refine ⟨hη'.isIrreducible, ?_⟩
  intro C hC hZ'C
  have hCimage : IsIrreducible (e.symm '' C) :=
    hC.image e.symm e.symm.continuous.continuousOn
  have hsub : Z ⊆ e.symm '' C := by
    intro z hz
    have hez : e z ∈ Z' := ⟨z, hz, rfl⟩
    exact ⟨e z, hZ'C hez, by simp⟩
  have hmax := hZ.2 hCimage hsub
  intro y hy
  exact ⟨e.symm y, hmax ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

private theorem finiteLocallyFree_pullback_comp {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (k : W ⟶ Z)
    (hf : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f i)) :
    Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f (k ≫ i)) := by
  let e := pullbackLeftPullbackSndIso f i k
  have he : e.hom ≫ pullback.snd f (k ≫ i) = pullback.snd (pullback.snd f i) k := by
    exact pullbackLeftPullbackSndIso_hom_snd f i k
  let eArrow : Arrow.mk (pullback.snd (pullback.snd f i) k) ≅
      Arrow.mk (pullback.snd f (k ≫ i)) :=
    Arrow.isoMk e (Iso.refl _) he
  have hbase : Stacks.Morphisms.IsFiniteLocallyFree
      (pullback.snd (pullback.snd f i) k) := by
    let : MorphismProperty.IsStableUnderBaseChange
        (@Stacks.Morphisms.IsFiniteLocallyFree) :=
      Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f i) k) hf
  let : MorphismProperty.RespectsIso
      (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff
    @Stacks.Morphisms.IsFiniteLocallyFree eArrow).mp hbase

private lemma finiteLocallyFree_of_pullback_factor {R A U C C' A' : Scheme.{u}}
    {a : A ⟶ R} {s : A ⟶ C} {f : R ⟶ U} {j : C ⟶ U}
    {a' : A' ⟶ R} {s' : A' ⟶ C'} {j' : C' ⟶ U}
    (h : IsPullback a s f j) (h' : IsPullback a' s' f j')
    (k : C' ⟶ C) (hk : k ≫ j = j') (hf : Stacks.Morphisms.IsFiniteLocallyFree s) :
    Stacks.Morphisms.IsFiniteLocallyFree s' := by
  let : MorphismProperty.RespectsIso @Stacks.Morphisms.IsFiniteLocallyFree :=
    Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.respectsIso
  have hb : Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f j) := by
    rw [← h.isoPullback_hom_snd] at hf
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @Stacks.Morphisms.IsFiniteLocallyFree) _ _).mp hf
  have hb' := finiteLocallyFree_pullback_comp f j k hb
  rw [hk] at hb'
  rw [← h'.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @Stacks.Morphisms.IsFiniteLocallyFree) _ _).mpr hb'

private lemma exists_invariant_affine_open_within_of_generic_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [QuasiSeparatedSpace G.objects.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (x : G.objects.left)
    (hx : ∀ y, (∃ r : G.arrows.left, G.source.left r = x ∧ G.target.left r = y) →
      ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    (W : G.objects.left.Opens)
    (hW : ∀ r : G.arrows.left, G.source.left r = x → G.target.left r ∈ W) :
    ∃ V : G.objects.left.Opens, IsAffineOpen V ∧ x ∈ V ∧
      Stacks.Groupoids.IsInvariantOpen G V ∧ V ≤ W := by
  classical
  let : IsFinite G.source.left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      inferInstance).1
  let : IsFinite G.target.left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      inferInstance).1
  let B := invariantOpenInside G W
  have hB := invariantOpenInside_isInvariant G W
  have hBx : x ∈ B := by
    have h := invariantOpenInside_orbit G W x hW (G.identity.left x)
      (source_identity_apply G x)
    simpa only [target_identity_apply] using h
  have hBO : ∀ y, y ∈ orbitUnion G (fun _ : Unit => x) → y ∈ B := by
    intro y hy
    obtain ⟨i, r, hr, rfl⟩ := Set.mem_iUnion.mp hy
    exact invariantOpenInside_orbit G W x hW r hr
  obtain ⟨A, hA, hAmem⟩ := exists_affine_open_containing_orbit_union_in_open G
    (fun _ : Unit => x) (fun _ => hx) B hBO
  let g : Over.mk (B.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk B.ι
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  let H := R.groupoid
  let eo := (Over.forget S).mapIso (eqToIso R.objects_eq)
  have hf := finiteLocallyFree_restriction_open G B hB R
  let : Stacks.Morphisms.IsFiniteLocallyFree H.source.left := hf.1
  let : Stacks.Morphisms.IsFiniteLocallyFree H.target.left := hf.2
  let y : H.objects.left := eo.inv ⟨x, hBx⟩
  have hobj : R.hom.mapObjects.left = eo.hom ≫ B.ι := by
    rw [R.mapObjects_eq]
    rfl
  have hy : R.hom.mapObjects.left y = x := by
    rw [hobj]
    change (eo.hom (eo.inv ⟨x, hBx⟩)).1 = x
    exact congrArg Subtype.val (over_eqToHom_apply_symm R.objects_eq ⟨x, hBx⟩)
  obtain ⟨N, hN, hyN, hNi⟩ :=
    AlgebraicGeometry.GroupoidScheme.exists_invariant_affine_open_of_orbit_subset_affine H y
      ⟨eo.hom ⁻¹ᵁ A, hA.preimage _, by
        intro r hr
        have hs : G.source.left (R.hom.mapArrows.left r) = x := by
          have h := congrArg (fun f => f.left r) R.hom.map_source
          change G.source.left (R.hom.mapArrows.left r) =
            R.hom.mapObjects.left (H.source.left r) at h
          rw [hr, hy] at h
          exact h
        have ht : G.target.left (R.hom.mapArrows.left r) =
            R.hom.mapObjects.left (H.target.left r) :=
          congrArg (fun f => f.left r) R.hom.map_target
        have hm : G.target.left (R.hom.mapArrows.left r) ∈
            orbitUnion G (fun _ : Unit => x) := Set.mem_iUnion.mpr ⟨(), _, hs, rfl⟩
        have ha := hAmem _ hm
        change eo.hom (H.target.left r) ∈ A
        have hp : eo.hom (H.target.left r) =
            ⟨G.target.left (R.hom.mapArrows.left r), hBO _ hm⟩ := by
          apply Subtype.ext
          exact (congrArg (fun f : H.objects.left ⟶ G.objects.left =>
            f (H.target.left r)) hobj).symm.trans ht.symm
        exact hp.symm ▸ ha⟩
  let n : N.toScheme ⟶ G.objects.left := N.ι ≫ R.hom.mapObjects.left
  let : IsOpenImmersion R.hom.mapObjects.left := by rw [hobj]; infer_instance
  let : IsAffine N.toScheme := hN
  refine ⟨n.opensRange, isAffineOpen_opensRange n, ?_, ?_, ?_⟩
  · exact ⟨⟨y, hyN⟩, hy⟩
  · have hs := (restriction_groupoid_pullback G g (invariantOpen_mono G B hB) R).1
    have hi := invariant_image_of_pullback R.hom hs hNi
    convert hi using 1
    ext z
    change (∃ a : N.toScheme, n a = z) ↔ ∃ a, a ∈ N ∧ R.hom.mapObjects.left a = z
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a.1, a.2, ha⟩
    · rintro ⟨a, ha, hz⟩; exact ⟨⟨a, ha⟩, hz⟩
  · rintro z ⟨a, rfl⟩
    apply invariantOpenInside_le G W
    change R.hom.mapObjects.left a.1 ∈ B
    rw [hobj]
    exact (eo.hom a.1).2

/-- **Finitely many generic orbits lie in one invariant affine open.** For a groupoid scheme with
finite locally free source and target over a quasi-separated object scheme, finitely many points
whose orbits consist of generic points of irreducible components of the object scheme have a
common invariant affine open neighbourhood.

The orbits are finite, pairwise equal or disjoint, and consist of generic points, so
[Stacks, Tag 01ZV] separates them into pairwise disjoint affine opens; [Stacks, Tag 03JE] then
produces an invariant affine open around each orbit inside its own one, and the disjoint union
of those is affine and invariant. Nothing is assumed beyond the hypotheses. -/
theorem exists_invariant_affine_open_of_finite_generic_orbits
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [QuasiSeparatedSpace G.objects.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ V : G.objects.left.Opens,
      IsAffineOpen V ∧ Stacks.Groupoids.IsInvariantOpen G V ∧
        ∀ i, x i ∈ V := by
  classical
  let OrbitClasses : Set (Set G.objects.left) :=
    Set.range (fun i : ι => orbitOf G (x i))
  let : IsFinite G.source.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      G.source.left).mp inferInstance |>.1
  let Q := {O : Set G.objects.left // O ∈ OrbitClasses}
  let : Finite Q := (Set.finite_range (fun i : ι => orbitOf G (x i))).to_subtype
  let rep (q : Q) : ι := Classical.choose (Set.mem_range.mp q.2)
  have hrep (q : Q) : orbitOf G (x (rep q)) = q.1 :=
    Classical.choose_spec (Set.mem_range.mp q.2)
  let P := {y : G.objects.left // y ∈ orbitUnion G x}
  let : Finite P := (orbitUnion_finite G x).to_subtype
  obtain ⟨N, hNaff, hNmem, hNdisj, _⟩ :=
    exists_pairwise_disjoint_affine_orbit_neighborhoods G x hx
  let Pts (q : Q) := {y : G.objects.left // y ∈ q.1}
  have hOrbitFinite (q : Q) : q.1.Finite := by
    rw [← hrep q]
    exact orbitOf_finite G (x (rep q))
  let toP (q : Q) (y : Pts q) : P := ⟨y.1, by
    change y.1 ∈ ⋃ i, orbitOf G (x i)
    exact Set.mem_iUnion.mpr ⟨rep q, by simpa only [hrep q] using y.2⟩⟩
  let W (q : Q) : G.objects.left.Opens := ⨆ y : Pts q, N (toP q y)
  have hWaff (q : Q) : IsAffineOpen (W q) := by
    let : Finite (Pts q) := (hOrbitFinite q).to_subtype
    apply IsAffineOpen.iSup_of_disjoint
    · intro y
      exact hNaff _
    · intro y z hyz
      apply hNdisj
      intro heq
      apply hyz
      exact Subtype.ext (congrArg (fun p : P => p.1) heq)
  have hWdisj : Pairwise (fun q q' : Q => Disjoint (W q) (W q')) := by
    intro q q' hneq
    rw [← TopologicalSpace.Opens.coe_disjoint]
    apply Set.disjoint_left.2
    intro y hy hy'
    simp only [W, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hy hy'
    rcases hy with ⟨p, hp⟩
    rcases hy' with ⟨p', hp'⟩
    have hsame : toP q p = toP q' p' := by
      by_contra hne
      have hd := hNdisj hne
      have hdset : Disjoint (N (toP q p) : Set G.objects.left)
          (N (toP q' p') : Set G.objects.left) := by
        simpa only [← TopologicalSpace.Opens.coe_disjoint] using hd
      exact (Set.disjoint_left.mp hdset hp) hp'
    have hpoint : p.1 = p'.1 := congrArg Subtype.val hsame
    have hint : (q.1 ∩ q'.1).Nonempty := by
      exact ⟨p.1, p.2, hpoint ▸ p'.2⟩
    have heq : q.1 = q'.1 := by
      have hint' :
          (orbitOf G (x (rep q)) ∩ orbitOf G (x (rep q'))).Nonempty := by
        simpa [hrep q, hrep q'] using hint
      exact (hrep q).symm.trans
        ((orbitOf_eq_of_intersects G (x (rep q)) (x (rep q')) hint').trans (hrep q'))
    exact hneq (Subtype.ext heq)
  have hWorbit (q : Q) (r : G.arrows.left)
      (hr : G.source.left.base r = x (rep q)) :
      G.target.left.base r ∈ W q := by
    have hyO : G.target.left.base r ∈ q.1 := by
      simpa only [hrep q] using
        (show G.target.left.base r ∈ orbitOf G (x (rep q)) from
          ⟨r, by simp [hr], rfl⟩)
    have hyP : G.target.left.base r ∈ orbitUnion G x := by
      change G.target.left.base r ∈ ⋃ i, orbitOf G (x i)
      exact Set.mem_iUnion.mpr ⟨rep q, by simpa only [hrep q] using hyO⟩
    exact (mem_iSup_opens (fun y : Pts q => N (toP q y)) _).2
      ⟨⟨G.target.left.base r, hyO⟩,
        hNmem (toP q ⟨G.target.left.base r, hyO⟩)⟩
  choose V hVaff hVrep hVinv hVsub using fun q =>
    exists_invariant_affine_open_within_of_generic_orbit
      G (x (rep q)) (hx (rep q)) (W q) (hWorbit q)
  have hVorbit (q : Q) (y : G.objects.left) (hy : y ∈ q.1) : y ∈ V q := by
    rw [← hrep q] at hy
    rcases hy with ⟨r, hrs, rfl⟩
    exact hVinv q r (hrs ▸ hVrep q)
  have hVdisj : Pairwise (fun q q' : Q => Disjoint (V q) (V q')) := by
    intro q q' hneq
    exact (hWdisj hneq).mono (hVsub q) (hVsub q')
  let U : G.objects.left.Opens := ⨆ q, V q
  have hUaff : IsAffineOpen U := IsAffineOpen.iSup_of_disjoint hVaff hVdisj
  have hUinv : Stacks.Groupoids.IsInvariantOpen G U := by
    intro r hr
    obtain ⟨q, hq⟩ := (mem_iSup_opens V (G.source.left.base r)).mp hr
    exact (mem_iSup_opens V (G.target.left.base r)).mpr ⟨q, hVinv q r hq⟩
  have hxi (i : ι) : x i ∈ U := by
    let q : Q := ⟨orbitOf G (x i), ⟨i, rfl⟩⟩
    apply (mem_iSup_opens V (x i)).mpr
    refine ⟨q, hVorbit q (x i) ?_⟩
    refine ⟨G.identity.left.base (x i), ?_, ?_⟩
    · change G.source.left.base (G.identity.left.base (x i)) = x i
      exact source_identity_apply G (x i)
    · exact target_identity_apply G (x i)
  exact ⟨U, hUaff, hUinv, hxi⟩

/-- The common construction behind Tags 0ABC and 0ABD: given that the points lie in the layer
union, and that affine opens of the layer thickening come from affine opens of the layer union,
the invariant affine open and its thickening exist. -/
private theorem exists_invariant_affine_open_thickening_of_affine_preimage
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [QuasiSeparatedSpace G.objects.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z)
    (hxiOpen : ∀ i, x i ∈ layerUnionOpen G)
    (haff : ∀ {C : (layerThickening G).Opens}, IsAffineOpen C →
      ∃ U : (layerUnionOpen G).toScheme.Opens, IsAffineOpen U ∧
        layerThickeningInclusion G ⁻¹ᵁ U = C) :
    ∃ (V : G.objects.left.Opens) (Z : V.toScheme.IdealSheafData),
      (∀ i, x i ∈ Set.range (Z.subschemeι ≫ V.ι)) ∧
      Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧
      Stacks.Groupoids.IsInvariantMonomorphism G (Z.subschemeι ≫ V.ι) ∧
      IsAffine Z.subscheme ∧
      IsThickening Z.subschemeι ∧
      (FinitePresentation (layerThickeningInclusion G) → FinitePresentation Z.subschemeι) ∧
      (let U' : Over S := Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom)
       let g : U' ⟶ G.objects := Over.homMk (Z.subschemeι ≫ V.ι) (by rfl)
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.source.left ∧
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.target.left) := by
  classical
  let UC : Over S := Over.mk
    ((layerThickeningInclusion G) ≫ (layerUnionOpen G).ι ≫ G.objects.hom)
  let gC : UC ⟶ G.objects :=
    Over.homMk ((layerThickeningInclusion G) ≫ (layerUnionOpen G).ι) (by rfl)
  have : Mono gC.left := by
    change Mono ((layerThickeningInclusion G) ≫ (layerUnionOpen G).ι)
    infer_instance
  have hflfS : Stacks.Morphisms.IsFiniteLocallyFree (restrictionSource G gC).left :=
    restrictionSource_mem_of_isInvariantMonomorphism G gC
      (isInvariantMonomorphism_layerThickeningInclusion G)
      (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      (finiteLocallyFree_pullback_source_layerThickening G)
  have hflfT : Stacks.Morphisms.IsFiniteLocallyFree (restrictionTarget G gC).left :=
    restrictionTarget_mem_of_restrictionSource_mem G gC
      (@Stacks.Morphisms.IsFiniteLocallyFree : MorphismProperty Scheme.{u}) hflfS
  let RC := AlgebraicGeometry.GroupoidScheme.restrict G gC
  let HC := RC.groupoid
  let : MorphismProperty.RespectsIso @Stacks.Morphisms.IsFiniteLocallyFree :=
    Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange.respectsIso
  let : IsIso (eqToHom RC.arrows_eq).left := by
    change IsIso ((Over.forget S).map (eqToHom RC.arrows_eq))
    infer_instance
  let : IsIso (eqToHom RC.objects_eq.symm).left := by
    change IsIso ((Over.forget S).map (eqToHom RC.objects_eq.symm))
    infer_instance
  let : IsIso (eqToHom RC.objects_eq).left := by
    change IsIso ((Over.forget S).map (eqToHom RC.objects_eq))
    infer_instance
  have hHC : ∀ s : restrictionArrows G gC ⟶ UC, Stacks.Morphisms.IsFiniteLocallyFree s.left →
      Stacks.Morphisms.IsFiniteLocallyFree
        (eqToHom RC.arrows_eq ≫ s ≫ eqToHom RC.objects_eq.symm).left := fun s hs =>
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @Stacks.Morphisms.IsFiniteLocallyFree) (eqToHom RC.arrows_eq).left _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso
        (P := @Stacks.Morphisms.IsFiniteLocallyFree) _ (eqToHom RC.objects_eq.symm).left).mpr hs)
  have hHCsource : Stacks.Morphisms.IsFiniteLocallyFree HC.source.left := by
    rw [RC.source_eq]
    exact hHC _ hflfS
  have hHCtarget : Stacks.Morphisms.IsFiniteLocallyFree HC.target.left := by
    rw [RC.target_eq]
    exact hHC _ hflfT
  let : Stacks.Morphisms.IsFiniteLocallyFree HC.source.left := hHCsource
  let : Stacks.Morphisms.IsFiniteLocallyFree HC.target.left := hHCtarget
  let eC : (layerThickening G) ≃ₜ (layerUnionOpen G).toScheme :=
    (isThickening_layerThickeningInclusion
        G).1.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
      (isThickening_layerThickeningInclusion G).2
  let : QuasiSeparatedSpace (layerUnionOpen G).toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding (layerUnionOpen G).ι.isOpenEmbedding
  let e0 : HC.objects.left ≃ₜ (layerThickening G) :=
    (eqToHom RC.objects_eq).left.homeomorph
  let e : HC.objects.left ≃ₜ (layerUnionOpen G).toScheme := e0.trans eC
  let : QuasiSeparatedSpace HC.objects.left :=
    (quasiSeparatedSpace_congr e).mpr inferInstance
  let xC : ι → (layerThickening G) := fun i => eC.symm ⟨x i, hxiOpen i⟩
  let xHC : ι → HC.objects.left := fun i =>
    (eqToHom RC.objects_eq.symm).left.base (xC i)
  have hxHC : ∀ i y, (∃ r : HC.arrows.left,
      HC.source.left r = xHC i ∧ HC.target.left r = y) →
        ∃ Z ∈ irreducibleComponents HC.objects.left, IsGenericPoint y Z := by
    intro i y ⟨r, hsr, htr⟩
    let q := RC.hom.mapArrows.left.base r
    have hsourceMap : G.source.left.base q =
        RC.hom.mapObjects.left.base (HC.source.left.base r) := by
      have hm := congrArg (fun f : HC.arrows ⟶ G.objects => f.left.base r)
        RC.hom.map_source
      simpa [q, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hm
    have htargetMap : G.target.left.base q =
        RC.hom.mapObjects.left.base (HC.target.left.base r) := by
      have hm := congrArg (fun f : HC.arrows ⟶ G.objects => f.left.base r)
        RC.hom.map_target
      simpa [q, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hm
    have hsourceC : (eqToHom RC.objects_eq).left.base (HC.source.left.base r) = xC i := by
      have hs := congrArg (fun z => (eqToHom RC.objects_eq).left.base z) hsr
      change _ = (eqToHom RC.objects_eq).left.base (xHC i) at hs
      have hcancel := over_eqToHom_apply_symm RC.objects_eq (xC i)
      rw [hcancel] at hs
      exact hs
    have hsourceObj : RC.hom.mapObjects.left.base (HC.source.left.base r) = x i := by
      rw [RC.mapObjects_eq]
      change ((layerThickeningInclusion G) ≫ (layerUnionOpen G).ι).base
        ((eqToHom RC.objects_eq).left.base (HC.source.left.base r)) = x i
      have hopen := congrArg eC hsourceC
      have hxE : eC (xC i) = ⟨x i, hxiOpen i⟩ := eC.apply_symm_apply _
      have hsubpoint := hopen.trans hxE
      have hval := congrArg Subtype.val hsubpoint
      change ((layerThickeningInclusion G) ((eqToHom RC.objects_eq).left.base
        (HC.source.left.base r))).1 = x i
      change ((layerThickeningInclusion G) ((eqToHom RC.objects_eq).left.base
        (HC.source.left.base r))).1 = x i at hval
      exact hval
    let yC := (eqToHom RC.objects_eq).left.base (HC.target.left.base r)
    let yOpen : (layerUnionOpen G).toScheme := (layerThickeningInclusion G) yC
    have htargetObj : RC.hom.mapObjects.left.base (HC.target.left.base r) = yOpen.1 := by
      rw [RC.mapObjects_eq]
      change ((layerThickeningInclusion G) ≫ (layerUnionOpen G).ι).base
        yC = ((layerThickeningInclusion G) yC).1
      change ((layerThickeningInclusion G) yC).1 = ((layerThickeningInclusion G) yC).1
      rfl
    have htargetAmbient : G.target.left.base q = yOpen.1 :=
      htargetMap.trans htargetObj
    obtain ⟨Z, hZ, hη⟩ := hx i yOpen.1
      ⟨q, hsourceMap.trans hsourceObj, htargetAmbient⟩
    obtain ⟨Zopen, hZopen, hηopen⟩ :=
      exists_generic_point_component_open (layerUnionOpen G) yOpen.1 Z hZ hη yOpen.2
    have he : e (HC.target.left.base r) = yOpen := by
      apply Subtype.ext
      rfl
    obtain ⟨Z', hZ', hη'⟩ := genericPointComponent_of_homeomorph e.symm hZopen hηopen
    refine ⟨Z', hZ', ?_⟩
    have hy : e.symm yOpen = HC.target.left.base r := by
      rw [← he]
      exact e.symm_apply_apply _
    have hy' : e.symm yOpen = y := hy.trans htr
    rw [← hy']
    exact hη'
  obtain ⟨VHC, hVHCaff, hVHCinv, hxHCV⟩ :=
    exists_invariant_affine_open_of_finite_generic_orbits HC xHC hxHC
  let : IsAffine VHC.toScheme := hVHCaff
  let cMap : VHC.toScheme ⟶ (layerThickening G) :=
    VHC.ι ≫ (eqToHom RC.objects_eq).left
  let Copen : (layerThickening G).Opens := cMap.opensRange
  let : IsOpenImmersion cMap := inferInstance
  have hCopenAff : IsAffineOpen Copen := isAffineOpen_opensRange cMap
  obtain ⟨Vopen, hVopenAff, hpre⟩ :=
    haff hCopenAff
  let : IsAffine Vopen.toScheme := hVopenAff
  let vMap : Vopen.toScheme ⟶ G.objects.left := Vopen.ι ≫ (layerUnionOpen G).ι
  let V : G.objects.left.Opens := vMap.opensRange
  let : IsOpenImmersion vMap := inferInstance
  have hVaff : IsAffineOpen V := isAffineOpen_opensRange vMap
  have hxiVOpen (i : ι) : (⟨x i, hxiOpen i⟩ : (layerUnionOpen G).toScheme) ∈ Vopen := by
    have hCmem : xC i ∈ Copen := by
      refine ⟨⟨xHC i, hxHCV i⟩, ?_⟩
      exact over_eqToHom_apply_symm RC.objects_eq (xC i)
    have hpre' : xC i ∈ (layerThickeningInclusion G) ⁻¹ᵁ Vopen := by rw [hpre]; exact hCmem
    have hmem : (layerThickeningInclusion G) (xC i) ∈ Vopen := hpre'
    change eC (xC i) ∈ Vopen at hmem
    exact (eC.apply_symm_apply ⟨x i, hxiOpen i⟩) ▸ hmem
  have hxiV (i : ι) : x i ∈ V := by
    change x i ∈ Set.range vMap.base
    refine ⟨⟨⟨x i, hxiOpen i⟩, hxiVOpen i⟩, ?_⟩
    rfl
  let : IsClosedImmersion (layerThickeningInclusion G) :=
    (isThickening_layerThickeningInclusion G).1
  let : Mono gC.left := inferInstance
  have hRC := restriction_groupoid_pullback G gC
    (isInvariantMonomorphism_layerThickeningInclusion G) RC
  let eo := (Over.forget S).mapIso (eqToIso RC.objects_eq)
  have hobj : RC.hom.mapObjects.left =
      eo.hom ≫ (layerThickeningInclusion G) ≫ (layerUnionOpen G).ι := by
    rw [RC.mapObjects_eq]
    rfl
  let : Mono RC.hom.mapObjects.left := by rw [hobj]; infer_instance
  let : Mono RC.hom.mapArrows.left := hRC.1.mono_fst_of_mono
  have hVimage : (V : Set G.objects.left) =
      RC.hom.mapObjects.left '' (VHC : Set HC.objects.left) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := (isThickening_layerThickeningInclusion G).2 a.1
      have hcC : c ∈ Copen := by
        rw [← hpre]
        change (layerThickeningInclusion G) c ∈ Vopen
        rw [hc]
        exact a.2
      obtain ⟨n, hn⟩ := hcC
      refine ⟨n.1, n.2, ?_⟩
      rw [hobj]
      change ((layerThickeningInclusion G) (eo.hom n.1)).1 = a.1.1
      change eo.hom n.1 = c at hn
      rw [hn, hc]
    · rintro ⟨y, hy, rfl⟩
      have hcC : eo.hom y ∈ Copen := ⟨⟨y, hy⟩, rfl⟩
      have hcV : (layerThickeningInclusion G) (eo.hom y) ∈ Vopen := by
        change eo.hom y ∈ (layerThickeningInclusion G) ⁻¹ᵁ Vopen
        rw [hpre]
        exact hcC
      refine ⟨⟨(layerThickeningInclusion G) (eo.hom y), hcV⟩, ?_⟩
      rw [hobj]
      rfl
  have hVinv : Stacks.Groupoids.IsInvariantOpen G V := by
    change Stacks.Groupoids.IsInvariantSet G (V : Set G.objects.left)
    rw [hVimage]
    exact invariant_image_of_pullback RC.hom hRC.1 hVHCinv
  let Dopen := (layerThickeningInclusion G) ⁻¹ᵁ Vopen
  let k : Dopen.toScheme ⟶ HC.objects.left := Dopen.ι ≫ eo.inv
  have hkRange : Set.range k = Set.range VHC.ι := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      have hcC : c.1 ∈ Copen := by rw [← hpre]; exact c.2
      obtain ⟨n, hn⟩ := hcC
      refine ⟨n, ?_⟩
      change n.1 = eo.inv c.1
      change eo.hom n.1 = c.1 at hn
      rw [← hn]
      exact (over_eqToHom_apply_symm RC.objects_eq.symm n.1).symm
    · rintro ⟨n, rfl⟩
      have hcC : eo.hom n.1 ∈ Copen := ⟨n, rfl⟩
      have hcD : eo.hom n.1 ∈ Dopen :=
        Eq.mpr (congrArg (fun O : (layerThickening G).Opens => eo.hom n.1 ∈ O) hpre) hcC
      refine ⟨⟨eo.hom n.1, hcD⟩, ?_⟩
      exact over_eqToHom_apply_symm RC.objects_eq.symm n.1
  have hkInv : Stacks.Groupoids.IsInvariantMonomorphism HC k := by
    have heq := Subobject.mk_eq_mk_of_comm k VHC.ι
      (IsOpenImmersion.isoOfRangeEq k VHC.ι hkRange)
      (IsOpenImmersion.isoOfRangeEq_hom_fac k VHC.ι hkRange)
    change (Subobject.pullback HC.target.left).obj (Subobject.mk k) =
      (Subobject.pullback HC.source.left).obj (Subobject.mk k)
    rw [heq]
    exact invariantOpen_mono HC VHC hVHCinv
  let f : Dopen.toScheme ⟶ V.toScheme :=
    ((layerThickeningInclusion G) ∣_ Vopen) ≫ vMap.isoOpensRange.hom
  let : IsClosedImmersion f := inferInstance
  have hfSurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := vMap.isoOpensRange.hom.homeomorph.surjective z
    obtain ⟨c, hc⟩ := (isThickening_layerThickeningInclusion G).2 a.1
    have hcD : c ∈ Dopen := by change (layerThickeningInclusion G) c ∈ Vopen; rw [hc]; exact a.2
    refine ⟨⟨c, hcD⟩, ?_⟩
    have hca : ((layerThickeningInclusion G) ∣_ Vopen) (⟨c, hcD⟩ : Dopen.toScheme) = a := by
      apply Subtype.ext
      have hr := congrArg (fun t : Dopen.toScheme ⟶ (layerUnionOpen G).toScheme =>
        t ⟨c, hcD⟩) (morphismRestrict_ι (layerThickeningInclusion G) Vopen)
      exact hr.trans hc
    change vMap.isoOpensRange.hom (((layerThickeningInclusion G) ∣_ Vopen) ⟨c, hcD⟩) = z
    exact (congrArg vMap.isoOpensRange.hom hca).trans ha
  let Z : V.toScheme.IdealSheafData := f.ker
  let ez : Dopen.toScheme ≅ Z.subscheme := asIso f.toImage
  let kz : Z.subscheme ⟶ HC.objects.left := ez.inv ≫ k
  have hkComp : k ≫ RC.hom.mapObjects.left = f ≫ V.ι := by
    rw [hobj]
    dsimp only [k, f]
    simp only [Category.assoc, eo.inv_hom_id_assoc]
    have hv : vMap.isoOpensRange.hom ≫ V.ι = vMap :=
      Scheme.Hom.isoOpensRange_hom_ι vMap
    rw [hv]
    exact (morphismRestrict_ι_assoc (layerThickeningInclusion G) Vopen (layerUnionOpen G).ι).symm
  have hzComp : kz ≫ RC.hom.mapObjects.left = Z.subschemeι ≫ V.ι := by
    change ez.inv ≫ k ≫ RC.hom.mapObjects.left = _
    rw [hkComp]
    have hez : ez.inv ≫ f = Z.subschemeι := by
      rw [← f.toImage_imageι]
      exact ez.inv_hom_id_assoc _
    rw [← Category.assoc, hez]
  have hkzInv : Stacks.Groupoids.IsInvariantMonomorphism HC kz := by
    have heq := Subobject.mk_eq_mk_of_comm kz k ez.symm rfl
    change (Subobject.pullback HC.target.left).obj (Subobject.mk kz) =
      (Subobject.pullback HC.source.left).obj (Subobject.mk kz)
    rw [heq]
    exact hkInv
  have hzInv : Stacks.Groupoids.IsInvariantMonomorphism G (Z.subschemeι ≫ V.ι) := by
    have h := invariant_comp_of_pullbacks RC.hom hRC.1 hRC.2 kz hkzInv
    simpa only [hzComp] using h
  have hzSurj : Function.Surjective Z.subschemeι := by
    intro z
    obtain ⟨d, hd⟩ := hfSurj z
    refine ⟨ez.hom d, ?_⟩
    have h := congrArg (fun t : Dopen.toScheme ⟶ V.toScheme => t d) f.toImage_imageι
    exact h.trans hd
  have hzFP : FinitePresentation (layerThickeningInclusion G) →
      FinitePresentation Z.subschemeι := by
    intro hp
    have hez : Z.subschemeι = ez.inv ≫ f := by
      rw [← f.toImage_imageι]
      exact (ez.inv_hom_id_assoc _).symm
    let : LocallyOfFinitePresentation (layerThickeningInclusion G) := hp.1
    let : LocallyOfFinitePresentation f := inferInstance
    refine ⟨?_, inferInstance, inferInstance⟩
    rw [hez]
    infer_instance
  let : IsAffine V.toScheme := hVaff
  refine ⟨V, Z, ?_, hVinv, hVaff, hzInv, isAffine_of_isAffineHom Z.subschemeι,
    ⟨inferInstance, hzSurj⟩, hzFP, ?_⟩
  · intro i
    obtain ⟨z, hz⟩ := hzSurj ⟨x i, hxiV i⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · let gz : Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom) ⟶ G.objects :=
      Over.homMk (Z.subschemeι ≫ V.ι)
    let Rz := AlgebraicGeometry.GroupoidScheme.restrict G gz
    have hz := restriction_groupoid_pullback G gz hzInv Rz
    let eoZ := (Over.forget S).mapIso (eqToIso Rz.objects_eq)
    have hfactor : (eoZ.hom ≫ kz) ≫ RC.hom.mapObjects.left = Rz.hom.mapObjects.left := by
      rw [Category.assoc, hzComp, Rz.mapObjects_eq]
      rfl
    exact ⟨finiteLocallyFree_of_pullback_factor hRC.1 hz.1 _ hfactor hHCsource,
      finiteLocallyFree_of_pullback_factor hRC.2 hz.2 _ hfactor hHCtarget⟩

/-- **[Stacks, Tag 0ABC], granted [Stacks, Tag 06AD].** Let `G` be a groupoid scheme whose source
and target are finite and of finite presentation, with quasi-separated object scheme, and let
`x : ι → U` be finitely many points whose orbits consist of generic points of irreducible
components of the object scheme. Then there is an invariant affine open `V` of the object scheme
and an ideal sheaf `Z` on it such that the closed subscheme `V(Z)` is an affine invariant
thickening of finite presentation inside `V` containing the images of the `x i`, over which the
source and target of the restricted groupoid are finite locally free.

The hypothesis `H06AD` is [Stacks, Tag 06AD] — a thickening of an affine scheme is affine — and
is the only thing assumed; it enters once, through
`AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_isThickening`. It is discharged by
`Stacks.Thickenings.forall_isAffine_of_isThickening` in
`AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening'`, which is
where the tag attribute sits. -/
theorem exists_invariant_affine_open_with_finiteLocallyFree_thickening
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left)
    (_ht : FinitePresentation G.target.left)
    [QuasiSeparatedSpace G.objects.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ (V : G.objects.left.Opens) (Z : V.toScheme.IdealSheafData),
      (∀ i, x i ∈ Set.range (Z.subschemeι ≫ V.ι)) ∧
      Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧
      Stacks.Groupoids.IsInvariantMonomorphism G (Z.subschemeι ≫ V.ι) ∧
      IsAffine Z.subscheme ∧
      IsThickening Z.subschemeι ∧
      FinitePresentation Z.subschemeι ∧
      (let U' : Over S := Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom)
       let g : U' ⟶ G.objects := Over.homMk (Z.subschemeι ≫ V.ι) (by rfl)
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.source.left ∧
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.target.left) := by
  classical
  have hxiOpen (i : ι) : x i ∈ layerUnionOpen G := by
    refine AlgebraicGeometry.mem_layerUnionOpen_of_orbit_subset_genericPoints G hs (x i) ?_
    intro y hy
    rcases hx i y hy with ⟨Z, hZ, hη⟩
    change closure ({y} : Set G.objects.left) ∈ irreducibleComponents G.objects.left
    rw [hη.def]
    exact hZ
  obtain ⟨V, Z, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ :=
    exists_invariant_affine_open_thickening_of_affine_preimage G x hx hxiOpen fun hC =>
      exists_isAffineOpen_preimage_eq_of_isThickening H06AD
        (isThickening_layerThickeningInclusion G) hC
  exact ⟨V, Z, h₁, h₂, h₃, h₄, h₅, h₆,
    h₇ (AlgebraicGeometry.finitePresentation_layerThickeningInclusion G hs), h₈⟩

/-- **[Stacks, Tag 0ABC].** Let `G` be a groupoid scheme whose source and target are finite and
of finite presentation, with quasi-separated object scheme, and let `x : ι → U` be finitely many
points whose orbits consist of generic points of irreducible components of the object scheme.
Then there is an invariant affine open `V` of the object scheme and an ideal sheaf `Z` on it such
that the closed subscheme `V(Z)` is an affine invariant thickening of finite presentation inside
`V` containing the images of the `x i`, over which the source and target of the restricted
groupoid are finite locally free.

Nothing is assumed beyond the hypotheses of the tag. This is
`AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening`, which carries
[Stacks, Tag 06AD] as the hypothesis `H06AD`, with that hypothesis discharged by
`Stacks.Thickenings.forall_isAffine_of_isThickening`, the library's 06AD. -/
@[stacks 0ABC]
theorem exists_invariant_affine_open_with_finiteLocallyFree_thickening'
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left)
    (ht : FinitePresentation G.target.left)
    [QuasiSeparatedSpace G.objects.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ (V : G.objects.left.Opens) (Z : V.toScheme.IdealSheafData),
      (∀ i, x i ∈ Set.range (Z.subschemeι ≫ V.ι)) ∧
      Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧
      Stacks.Groupoids.IsInvariantMonomorphism G (Z.subschemeι ≫ V.ι) ∧
      IsAffine Z.subscheme ∧
      IsThickening Z.subschemeι ∧
      FinitePresentation Z.subschemeι ∧
      (let U' : Over S := Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom)
       let g : U' ⟶ G.objects := Over.homMk (Z.subschemeι ≫ V.ι) (by rfl)
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.source.left ∧
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.target.left) :=
  exists_invariant_affine_open_with_finiteLocallyFree_thickening
    Stacks.Thickenings.forall_isAffine_of_isThickening G hs ht x hx

/-- **An open subset of a locally Noetherian scheme is locally constructible.** Each point has an
affine open neighbourhood whose ring of sections is Noetherian, hence a Noetherian underlying
space, and in a Noetherian space every subset is retrocompact. -/
theorem isLocallyConstructible_of_isOpen {X : Scheme.{u}} [IsLocallyNoetherian X] {W : Set X}
    (hW : IsOpen W) : Topology.IsLocallyConstructible W := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  refine ⟨U, U.isOpen.mem_nhds hxU, U.isOpen, ?_⟩
  have hring : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hnoeth : TopologicalSpace.NoetherianSpace (U : Set X) :=
    noetherianSpace_of_isAffineOpen U hU
  have hretro : IsRetrocompact ((U : Set X) ↓∩ W) := fun _ _ _ =>
    TopologicalSpace.NoetherianSpace.isCompact _
  exact hretro.isConstructible (hW.preimage continuous_subtype_val)

/-- **On a locally Noetherian scheme, a generic point of an irreducible component lying in the
closure of an open subset lies in that open subset.** The open subset is locally constructible, so
if it did not contain the point it would be avoided by a neighbourhood of it
([Stacks, Tag 0AAW]), contradicting that the point is in its closure. -/
theorem mem_of_mem_closure_of_mem_genericPoints {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W : X.Opens) {η : X} (hη : η ∈ genericPoints X)
    (hclosure : η ∈ closure (W : Set X)) : η ∈ W := by
  by_contra hne
  have hcompl : (W : Set X)ᶜ ∈ nhds η :=
    compl_mem_nhds_of_isLocallyConstructible_of_mem_genericPoints
      (isLocallyConstructible_of_isOpen W.isOpen) hη hne
  obtain ⟨y, hy, hyW⟩ := mem_closure_iff_nhds.mp hclosure _ hcompl
  exact hy hyW

/-- **An affine open of the closed subscheme of a thickening of a locally Noetherian scheme comes
from an affine open of the ambient scheme.** The open is the one matching it under the
homeomorphism of the thickening; it is affine because the thickening restricts to a finite
surjective morphism from an affine scheme onto it, and that open is Noetherian, so
[Stacks, Tag 01YQ] applies. -/
theorem exists_isAffineOpen_preimage_eq_of_isThickening_of_isLocallyNoetherian
    {X X' : Scheme.{u}} [IsLocallyNoetherian X'] {i : X ⟶ X'} (hi : IsThickening i)
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ U : X'.Opens, IsAffineOpen U ∧ i ⁻¹ᵁ U = V := by
  obtain ⟨U', hpre, hsurj⟩ := exists_opens_preimage_eq_and_surjective hi V
  let : IsClosedImmersion i := hi.1
  refine ⟨U', ?_, hpre⟩
  let : IsFinite (i ∣_ U') := ((IsClosedImmersion.iff_isFinite_and_mono _).mp inferInstance).1
  let : Surjective (i ∣_ U') := ⟨hsurj⟩
  let : IsAffine (i ⁻¹ᵁ U' : X.Opens).toScheme := by rw [hpre]; exact hV
  let : CompactSpace U'.toScheme := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ.mpr hsurj]
    exact isCompact_range (by fun_prop)
  let : IsNoetherian U'.toScheme := ⟨⟩
  exact Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective (i ∣_ U')

/-- **[Stacks, Tag 0ABD].** Let `G` be a groupoid scheme whose source and target are finite, with
locally Noetherian object scheme, and let `x : ι → U` be finitely many points whose orbits consist
of generic points of irreducible components of the object scheme. Then there is an invariant
affine open `V` of the object scheme and an ideal sheaf `Z` on it such that the closed subscheme
`V(Z)` is an affine invariant thickening inside `V` containing the images of the `x i`, over which
the source and target of the restricted groupoid are finite locally free.

Nothing is assumed beyond the hypotheses: the affineness of `V` comes from [Stacks, Tag 01YQ]
through
`AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_isThickening_of_isLocallyNoetherian`. -/
@[stacks 0ABD]
theorem exists_invariant_affine_finiteLocallyFree_thickening_of_isLocallyNoetherian
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [IsLocallyNoetherian G.objects.left]
    {ι : Type v} [Finite ι] (x : ι → G.objects.left)
    (hx : ∀ i y, (∃ r : G.arrows.left,
      G.source.left r = x i ∧ G.target.left r = y) →
        ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ (V : G.objects.left.Opens) (Z : V.toScheme.IdealSheafData),
      (∀ i, x i ∈ Set.range (Z.subschemeι ≫ V.ι)) ∧
      Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧
      Stacks.Groupoids.IsInvariantMonomorphism G (Z.subschemeι ≫ V.ι) ∧
      IsAffine Z.subscheme ∧
      IsThickening Z.subschemeι ∧
      (let U' : Over S := Over.mk (Z.subschemeι ≫ V.ι ≫ G.objects.hom)
       let g : U' ⟶ G.objects := Over.homMk (Z.subschemeι ≫ V.ι) (by rfl)
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.source.left ∧
       Stacks.Morphisms.IsFiniteLocallyFree
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.target.left) := by
  classical
  have hxiOpen (i : ι) : x i ∈ layerUnionOpen G := by
    have hmem : x i ∈ arrowSaturation G
        (closure (layerUnionOpen G : Set G.objects.left)) := by
      rw [saturation_closure_layerUnion_eq_univ G]
      trivial
    obtain ⟨r, hrs, hrt⟩ := hmem
    have hrs' : G.source.left.base r ∈ closure (layerUnionOpen G : Set G.objects.left) := hrs
    obtain ⟨Z, hZ, hη⟩ := hx i (G.source.left.base r)
      ⟨G.inverse.left.base r, by rw [source_inverse_apply]; exact hrt,
        target_inverse_apply G r⟩
    have hgen : G.source.left.base r ∈ genericPoints G.objects.left := by
      change closure ({G.source.left.base r} : Set G.objects.left) ∈
        irreducibleComponents G.objects.left
      rw [hη.def]
      exact hZ
    exact hrt ▸ layerUnion_invariant G r
      (mem_of_mem_closure_of_mem_genericPoints (layerUnionOpen G) hgen hrs')
  obtain ⟨V, Z, h₁, h₂, h₃, h₄, h₅, h₆, -, h₈⟩ :=
    exists_invariant_affine_open_thickening_of_affine_preimage G x hx hxiOpen fun hC =>
      exists_isAffineOpen_preimage_eq_of_isThickening_of_isLocallyNoetherian
        (isThickening_layerThickeningInclusion G) hC
  exact ⟨V, Z, h₁, h₂, h₃, h₄, h₅, h₆, h₈⟩

end AlgebraicGeometry

end
