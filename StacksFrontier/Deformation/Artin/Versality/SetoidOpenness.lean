module

public import StacksFrontier.AlgebraicGeometry.Properties.MaximalPoints
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickeningSequence
public import StacksFrontier.Deformation.Artin.Versality.SetoidGeneralization

/-!
# Openness of versality for categories fibred in setoids

Let `𝒳` be a category fibred in setoids over the big fppf site of a locally Noetherian scheme
`S`, satisfying (RS*), whose agreement loci are schemes locally of finite type, in which objects
descend along first-order thickenings to finite type, and in which towers of first-order
thickenings of affine schemes over suitable affine opens of `S` are effective. Then `𝒳`
satisfies openness of versality.

This is Stacks 0CXU for categories fibred in setoids, with the proof of the source. Let `x` over
`U` be versal at `u₀` and suppose versality fails at finite type points arbitrarily close to
`u₀`. After shrinking, `U` is affine and lies over an affine open of `S`. The set `E` of finite
type points at which `x` is not versal has `u₀` in its closure, and by Stacks 0G2K (in the form
`Deformation.Artin.isVersalAt_of_specializes_of_faithful`) no point of `E` specializes to `u₀`.
Stacks 0G2F and Stacks 0G2R give a sequence `u₁, u₂, …` in `E`, without specializations among
its members, with `u₀` in its closure; Stacks 0G2S gives a tower `x ⟶ x₁ ⟶ x₂ ⟶ …` over
first-order thickenings without local retractions at the `uₙ`; effectivity and descent give an
object `ξ'` over a first-order thickening `U ⟶ U'` of finite type receiving the tower, and the
smoothness of the agreement locus of `x` and `ξ'` at the image of `u₀` produces a retraction over
a neighbourhood of `u₀`, which contains some `uₙ`: a contradiction.

## Main definitions

* `Deformation.Artin.HasEffectiveThickeningTowers`: towers of first-order thickenings of an
  affine scheme of finite type lying over a given kind of affine open of `S` are effective.

## Main results

* `Deformation.Artin.exists_open_restriction_square`: the restriction of an object to an open
  subscheme, and the pullback square it forms with an arrow into that object.
* `Deformation.Artin.isOpenVersality_of_faithful`: Stacks 0CXU for categories fibred in setoids.

## Implementation notes

The source shrinks `U` so that `Z ⟶ U'` is smooth along the image of `U` and then extends a
section over all of `U'` by Stacks 04AM. Here a section over a neighbourhood of the image of
`u₀` suffices: the neighbourhood contains some `uₙ`, at which Stacks 0G2S forbids a retraction.

Effectivity is asked only for towers over affine opens of `S` singled out by a predicate
`good` which covers `S`. This is the form in which strong formal effectiveness is available for
2-fibre products with a scheme `V`, where both `S` and `V` must be shrunk to affines.

The conclusion is the body of `Deformation.Artin.IsOpenVersality` of Stacks 07XQ written out,
since `p ⋙ Over.post B.inclusion` is not fibred in groupoids over all schemes over `S`.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2S](https://stacks.math.columbia.edu/tag/0G2S)
* [Stacks Project, Tag 0G2F](https://stacks.math.columbia.edu/tag/0G2F)
* [Stacks Project, Tag 0G2R](https://stacks.math.columbia.edu/tag/0G2R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE

namespace Deformation.Artin

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- *Effectivity of towers of first-order thickenings.* For an object `x` over an affine scheme
`U` locally of finite type over `S` whose image lies in an open `W` of `S` with `good W`, every
tower `x ⟶ x₁ ⟶ x₂ ⟶ …` over first-order thickenings `U ⟶ Uₙ`, whose steps `Uₙ ⟶ Uₙ₊₁`
are closed immersions, has a cocone `xₙ ⟶ ξ` such that
`U ⟶ U₁ ⟶ T` is again a first-order thickening, `T` being the scheme under `ξ`. -/
abbrev HasEffectiveThickeningTowers (good : S.Opens → Prop) : Prop :=
  ∀ (x : F) (xs : ℕ → F) (step : ∀ n, xs n ⟶ xs (n + 1)) (fromX : ∀ n, x ⟶ xs n),
    (∀ n, fromX (n + 1) = fromX n ≫ step n) →
    IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)) →
    LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) →
    (∃ W : S.Opens, good W ∧ Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S)) →
    (∀ n, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX (n + 1))))) →
    (∀ n, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step (n + 1))))) →
    ∃ (ξ : F) (ι : ∀ n, xs (n + 1) ⟶ ξ), (∀ n, step (n + 1) ≫ ι (n + 1) = ι n) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX 1 ≫ ι 0)))

/-- The structure morphism of the source of an arrow factors through the structure morphism of
its target. -/
private theorem toScheme_map_comp_inclusion_map_hom {x Y : F} (f : x ⟶ Y) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map f) ≫
      B.inclusion.map (p.obj Y).hom = B.inclusion.map (p.obj x).hom := by
  have h := congrArg B.inclusion.map (Over.w (p.map f))
  rw [B.inclusion.map_comp] at h
  exact h

/-- A lift of an open immersion `j` is an open immersion with the same range, and agrees with `j`
up to the identification of the objects. -/
private theorem toScheme_map_lift_of_isOpenImmersion {y Y : F}
    {W : AlgebraicGeometry.BigFppfOver B S hS} (j : W ⟶ p.obj Y) (r : y ⟶ Y) [p.IsHomLift j r]
    [IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)] :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r) =
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
          (IsHomLift.domain_eq p j r)) ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j ∧
      IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)) ∧
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)).base =
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j).base := by
  have h : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r) =
      eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (IsHomLift.domain_eq p j r)) ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j := by
    rw [IsHomLift.fac' p j r]
    simp
  refine ⟨h, ?_⟩
  rw [h]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr,
    Set.image_univ]
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- **Restriction to an open and the resulting pullback square.** For an arrow `f : x ⟶ Y` and
an open `O` of the scheme under `Y`, there are an arrow `r : y ⟶ Y` over an open immersion with
image `O` and arrows `t : z ⟶ x`, `s : z ⟶ y` with `t ≫ f = s ≫ r` lying over a pullback
square. -/
theorem exists_open_restriction_square (hp : p.IsFiberedInGroupoids) {x Y : F} (f : x ⟶ Y)
    (O : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj Y)).Opens) :
    ∃ (y : F) (r : y ⟶ Y) (z : F) (t : z ⟶ x) (s : z ⟶ y),
      IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)) ∧
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)).base =
        (O : Set _) ∧
      t ≫ f = s ≫ r ∧
      IsPullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map t))
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map s))
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map f))
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)) := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hOc : B.Contains O := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion O.ι)
    (p.obj Y).left.2
  let W := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj Y) hOc O.ι
  let j : W ⟶ p.obj Y := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj Y) hOc O.ι
  obtain ⟨y, r, hr⟩ := hp.exists_lift j Y rfl
  have hy : p.obj y = W := IsHomLift.domain_eq p j r
  have : IsOpenImmersion (V.map j) := inferInstanceAs (IsOpenImmersion O.ι)
  obtain ⟨hrV, hopen, hrange⟩ := toScheme_map_lift_of_isOpenImmersion B S hS p j r
  let f₀ := V.map (p.map f)
  let Pop : (V.obj (p.obj x)).Opens := f₀ ⁻¹ᵁ O
  have hPc : B.Contains Pop :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion Pop.ι) (p.obj x).left.2
  let P := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hPc Pop.ι
  let ta : P ⟶ p.obj x :=
    AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hPc Pop.ι
  have hfS := toScheme_map_comp_inclusion_map_hom B S hS p f
  let g : P ⟶ W := Over.homMk (ObjectProperty.homMk (f₀ ∣_ O)) (by
    apply ObjectProperty.hom_ext
    show (f₀ ∣_ O) ≫ O.ι ≫ B.inclusion.map (p.obj Y).hom =
      Pop.ι ≫ B.inclusion.map (p.obj x).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hfS])
  have hsq : ta ≫ p.map f = g ≫ j := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (morphismRestrict_ι f₀ O).symm
  obtain ⟨z, t, ht⟩ := hp.exists_lift ta x rfl
  have hz : p.obj z = P := IsHomLift.domain_eq p ta t
  have : p.IsStronglyCartesian j r := hp.isStronglyCartesian_homLift j r
  have : p.IsHomLift (p.map f) f := inferInstance
  let s : z ⟶ y := Functor.IsStronglyCartesian.map p j r hsq (t ≫ f)
  have hs : s ≫ r = t ≫ f := Functor.IsStronglyCartesian.fac p j r hsq (t ≫ f)
  have hsl : p.IsHomLift g s := inferInstance
  have htV : V.map (p.map t) = eqToHom (congrArg V.obj hz) ≫ V.map ta := by
    rw [IsHomLift.fac' p ta t]
    simp [eqToHom_map]
  have hsV : V.map (p.map s) = eqToHom (congrArg V.obj hz) ≫ V.map g ≫
      eqToHom (congrArg V.obj hy).symm := by
    rw [IsHomLift.fac' p g s]
    simp [eqToHom_map]
  refine ⟨y, r, z, t, s, hopen, hrange.trans O.range_ι, hs.symm, ?_⟩
  rw [htV, hsV, hrV]
  have key : ∀ {X₁ Y₁ : Scheme.{u}} (e : X₁ = Y₁) {P₁ A₁ Z₁ : Scheme.{u}} {a : P₁ ⟶ A₁}
      {b : P₁ ⟶ Y₁} {k : A₁ ⟶ Z₁} {l : Y₁ ⟶ Z₁}, IsPullback a b k l →
      IsPullback a (b ≫ eqToHom e.symm) k (eqToHom e ≫ l) := by
    rintro _ _ rfl _ _ _ _ _ _ _ H
    simpa using H
  simp only [← Category.assoc]
  refine key _ (isPullback_eqToHom_comp _ ?_)
  exact (isPullback_morphismRestrict f₀ O).flip

/-- A morphism from an affine scheme to a locally Noetherian scheme whose image lies in an
affine open is quasi-compact. -/
theorem quasiCompact_of_range_subset_isAffineOpen {X Y : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) {G : Y.Opens} (hG : IsAffineOpen G)
    (hf : Set.range f.base ⊆ (G : Set Y)) : QuasiCompact f := by
  have : IsAffine G := hG
  rw [← IsOpenImmersion.lift_fac G.ι f (by rwa [Scheme.Opens.range_ι])]
  infer_instance

/-- In a scheme, no point of a finite set specializing to no point of it can have `u₀` in its
closure unless it specializes to `u₀`. -/
theorem exists_specializes_of_mem_closure_of_finite {X : Type*} [TopologicalSpace X]
    {E : Set X} (hE : E.Finite) {u₀ : X} (h : u₀ ∈ closure E) : ∃ e ∈ E, e ⤳ u₀ := by
  have hEq : E = ⋃ e ∈ E, ({e} : Set X) := (Set.biUnion_of_singleton E).symm
  rw [hEq, hE.closure_biUnion] at h
  obtain ⟨e, he, hmem⟩ := Set.mem_iUnion₂.mp h
  exact ⟨e, he, specializes_iff_mem_closure.mpr hmem⟩

/-- **A countable sequence of non-versal points accumulating at `u₀`.** In a Noetherian scheme,
if `u₀` lies in the closure of a set `E` none of whose points specializes to `u₀`, there is an
injective sequence of points of `E`, with no specialization between distinct members, whose
closure contains `u₀`. -/
theorem exists_seq_of_mem_closure (X : Scheme.{u}) [IsNoetherian X] {E : Set X} {u₀ : X}
    (hcl : u₀ ∈ closure E) (hgen : ∀ e ∈ E, ¬ e ⤳ u₀) :
    ∃ v : ℕ → X, (∀ n, v n ∈ E) ∧ (∀ n m, n ≠ m → ¬ v n ⤳ v m) ∧
      u₀ ∈ closure (Set.range v) := by
  classical
  have hinf : ∀ E' ⊆ E, u₀ ∈ closure E' → E'.Infinite := by
    intro E' hE' hmem hfin
    obtain ⟨e, he, hspec⟩ := exists_specializes_of_mem_closure_of_finite hfin hmem
    exact hgen e (hE' he) hspec
  -- the reduced closed subscheme on the closure of `E`
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure E, isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let ι := I.subschemeι
  have hrange : Set.range ι.base = closure E := by
    show Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian ι
  have : CompactSpace I.subscheme := ι.isClosedEmbedding.compactSpace
  have : IsNoetherian I.subscheme := {}
  let T : Set I.subscheme := ι.base ⁻¹' E
  have hET : ι.base '' T = E :=
    Set.image_preimage_eq_of_subset (hrange ▸ subset_closure)
  have hTdense : Dense T := by
    rw [dense_iff_closure_eq]
    apply Set.image_injective.mpr ι.isClosedEmbedding.injective
    rw [← ι.isClosedEmbedding.closure_image_eq, hET, Set.image_univ, hrange]
  have hTinf : T.Infinite := by
    intro hT
    exact hinf E le_rfl hcl (hET ▸ hT.image _)
  obtain ⟨E₀, hE₀T, hE₀c, hE₀d⟩ := exists_countable_dense_subset I.subscheme T hTinf hTdense
  let E₁ := ι.base '' E₀
  have hE₁E : E₁ ⊆ E := by
    rintro _ ⟨t, ht, rfl⟩
    exact hE₀T ht
  have hcl₁ : u₀ ∈ closure E₁ := by
    rw [ι.isClosedEmbedding.closure_image_eq, dense_iff_closure_eq.mp hE₀d, Set.image_univ,
      hrange]
    exact hcl
  let M := maximalPoints E₁
  have hME : M ⊆ E := fun m hm => hE₁E hm.1
  have hclM : u₀ ∈ closure M := by
    rw [closure_maximalPoints X E₁]
    exact hcl₁
  have hMc : M.Countable := (hE₀c.image _).mono fun m hm => hm.1
  have hMinf : M.Infinite := hinf M hME hclM
  have : Countable M := hMc.to_subtype
  have : Infinite M := hMinf.to_subtype
  obtain ⟨e⟩ : Nonempty (M ≃ ℕ) := nonempty_equiv_of_countable
  refine ⟨fun n => (e.symm n).1, fun n => hME (e.symm n).2, ?_, ?_⟩
  · intro n m hnm hspec
    apply hnm
    apply e.symm.injective
    exact Subtype.ext (specialization_eq_of_mem_maximalPoints (e.symm n).2 (e.symm m).2 hspec)
  · have hrv : Set.range (fun n => (e.symm n).1) = M := by
      ext m
      constructor
      · rintro ⟨n, rfl⟩
        exact (e.symm n).2
      · intro hm
        exact ⟨e ⟨m, hm⟩, by simp⟩
    rw [hrv]
    exact hclM

/-- **Stacks 0CXU for categories fibred in setoids, the affine case.** Let `x` lie over an
affine scheme `U` locally of finite type over `S`, with image in an affine open `G` of `S`
satisfying `good`. If `x` is versal at `u₀`, then `x` is versal at every finite type point of
an open neighbourhood of `u₀`. -/
theorem exists_open_isVersalAt_of_faithful_of_isAffine (hp : p.IsFiberedInGroupoids)
    [p.Faithful] [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hZ : HasAgreementLoci B S hS p) (hD : HasThickeningDescent B S hS p)
    (good : S.Opens → Prop) (heff : HasEffectiveThickeningTowers B S hS p good) (x : F)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (G : S.Opens) (hG : good G) (hGaff : IsAffineOpen G)
    (hxG : Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (G : Set S))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)).Opens, u₀ ∈ W ∧
      ∀ u ∈ W, IsFiniteTypePoint u →
        IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u x
          rfl := by
  classical
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let X := V.obj (p.obj x)
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj x).hom)
  have : IsNoetherian X := {}
  have : LocallyOfFiniteType (q.obj x).hom :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
  have : IsAffine (q.obj x).left :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : IsAffine (B.inclusion.obj (p.obj x).left) :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : QuasiCompact (q.obj x).hom :=
    quasiCompact_of_range_subset_isAffineOpen (B.inclusion.map (p.obj x).hom) hGaff hxG
  have hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S) := ⟨G, hGaff, hxG⟩
  by_contra hcon
  push Not at hcon
  let E : Set X := {u | IsFiniteTypePoint u ∧ ¬ IsVersalAt (q.obj x) q u x rfl}
  have hgen : ∀ e ∈ E, ¬ e ⤳ u₀ := fun e he hspec =>
    he.2 (isVersalAt_of_specializes_of_faithful B S hS p hp hRS hZ hD x hW he.1 hspec hvers)
  have hcl : u₀ ∈ closure E := by
    rw [mem_closure_iff]
    intro O hO hu₀O
    obtain ⟨u, hu, hft, hnv⟩ := hcon ⟨O, hO⟩ hu₀O
    exact ⟨u, hu, hft, hnv⟩
  obtain ⟨v, hvE, hinc, hclv⟩ := exists_seq_of_mem_closure X hcl hgen
  -- the tower of Stacks 0G2S at the points `v n`
  obtain ⟨xs, step, fromX, -, -, hfromS, hprops⟩ :=
    exists_sequence_firstOrderThickenings_without_localRetraction B S hS p hp hRS (q.obj x) x
      rfl v (fun n => (hvE n).1) hinc (fun n => (hvE n).2)
  have hthick : ∀ n, Stacks.Thickenings.IsFirstOrderThickening
      (V.map (p.map (fromX (n + 1)))) := fun n => by
    have h := (hprops n).1
    simp only [eqToHom_refl, Category.id_comp] at h
    exact h
  have hstep : ∀ n, IsClosedImmersion (V.map (p.map (step (n + 1)))) := by
    intro n
    have hepi := (hprops (n + 1)).2.1.1
    let i := V.map (p.map (step (n + 1)))
    let j₁ := V.map (p.map (fromX (n + 1)))
    let j₂ := V.map (p.map (fromX (n + 2)))
    have hj : j₂ = j₁ ≫ i := by
      show V.map (p.map (fromX (n + 2))) = _
      rw [hfromS (n + 1), Functor.map_comp, Functor.map_comp]
    have h₁ : IsHomeomorph j₁.base := by
      have := (hthick n).1
      exact isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨j₁.isClosedEmbedding.isEmbedding, (hthick n).isThickening.2⟩
    have h₂ : Topology.IsClosedEmbedding j₂.base := by
      have := (hthick (n + 1)).1
      exact j₂.isClosedEmbedding
    let e := h₁.homeomorph
    have hie : (i.base : _ → _) = j₂.base ∘ e.symm := by
      funext y
      have hy : j₁.base (e.symm y) = y := e.apply_symm_apply y
      conv_lhs => rw [← hy]
      show (j₁ ≫ i).base (e.symm y) = _
      rw [← hj]
      rfl
    exact isClosedImmersion_of_epi_unitToPushforwardObjUnit
      i ⟨hie ▸ h₂.comp e.symm.isClosedEmbedding, hepi⟩
  obtain ⟨ξ, ι, hι, hthick₁⟩ := heff x xs step fromX hfromS inferInstance inferInstance
    ⟨G, hG, hxG⟩ hthick hstep
  have hcomp : ∀ n, fromX (n + 1) ≫ ι n = fromX 1 ≫ ι 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hfromS (n + 1), Category.assoc, hι n, ih]
  -- descent and the local retraction
  obtain ⟨ξ', e, -, hlft', hthick'⟩ := hD ξ (p.obj x) (p.map (fromX 1 ≫ ι 0)) inferInstance
    inferInstance hthick₁ hW
  obtain ⟨Z, π, π', hlocus, hπ'⟩ := hZ x ξ' inferInstance hlft'
  have : IsLocallyNoetherian (V.obj (p.obj ξ')) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj ξ').hom)
  obtain ⟨O', hO'₀, hO'⟩ := exists_open_localRetraction_comp B S hS p hp x ξ ξ' Z π π' hlocus
    (fromX 1 ≫ ι 0) e (by rwa [Functor.map_comp, Functor.map_comp]) u₀ hvers
  -- a point of the sequence inside the neighbourhood
  let OU : X.Opens := (V.map (p.map ((fromX 1 ≫ ι 0) ≫ e))) ⁻¹ᵁ O'
  obtain ⟨_, hmO, ⟨n, rfl⟩⟩ := mem_closure_iff.mp hclv OU OU.isOpen hO'₀
  obtain ⟨y, rW, z, t, s, hopen, hrange, hts, hpb⟩ := exists_open_restriction_square B S hS p hp
    (fromX (n + 1)) ((V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O')
  have hmem : (V.map (p.map (fromX (n + 1)))).base (v n) ∈
      (V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O' := by
    show (V.map (p.map (ι n ≫ e))).base ((V.map (p.map (fromX (n + 1)))).base (v n)) ∈ O'
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      hcomp n]
    exact hmO
  obtain ⟨β, hβ⟩ := hO' y (rW ≫ ι n) (by
    rintro _ ⟨a, rfl⟩
    rw [Category.assoc, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply]
    have ha : (V.map (p.map rW)).base a ∈ Set.range (V.map (p.map rW)).base := ⟨a, rfl⟩
    rw [hrange] at ha
    exact ha)
  have hpt : ∃ z' : (q.obj y).left, (q.map rW).left z' =
      (eqToHom (congrArg Over.left (rfl : q.obj x = q.obj x)).symm ≫
        (q.map (fromX (n + 1))).left) (v n) := by
    have h : (V.map (p.map (fromX (n + 1)))).base (v n) ∈ Set.range (V.map (p.map rW)).base := by
      rw [hrange]
      exact hmem
    obtain ⟨z', hz'⟩ := h
    refine ⟨z', ?_⟩
    simp only [eqToHom_refl, Category.id_comp]
    exact hz'
  exact (hprops n).2.2 y rW hopen hpt z t s hpb ⟨β, hβ z t s (by
    rw [← hcomp n, ← Category.assoc, hts, Category.assoc]), hts⟩

/-- **Stacks 0CXU for categories fibred in setoids.** Let `𝒳` be fibred in setoids over the big
fppf site of a locally Noetherian scheme `S`, satisfying (RS*), with agreement loci locally of
finite type, descent along first-order thickenings, and effective towers of first-order
thickenings over the opens of a family `good` of affine opens covering `S`. Then `𝒳` satisfies
openness of versality: if `x` over a scheme `U` locally of finite type over `S` is versal at a
finite type point `u₀`, it is versal at every finite type point of an open neighbourhood of
`u₀`. -/
theorem isOpenVersality_of_faithful (hp : p.IsFiberedInGroupoids) [p.Faithful]
    [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hZ : HasAgreementLoci B S hS p) (hD : HasThickeningDescent B S hS p)
    (good : S.Opens → Prop) (hgood : ∀ s : S, ∃ G : S.Opens, good G ∧ IsAffineOpen G ∧ s ∈ G)
    (heff : HasEffectiveThickeningTowers B S hS p good) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  classical
  intro U hU x hx u₀ _ hvers
  subst hx
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let fS := B.inclusion.map (p.obj x).hom
  obtain ⟨G, hG, hGaff, hu₀G⟩ := hgood (fS.base u₀)
  obtain ⟨U₁, hU₁aff, hu₀U₁, hU₁G⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.obj (p.obj x)) (U := fS ⁻¹ᵁ G) (x := u₀) hu₀G
  have hU₁c : B.Contains U₁ :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U₁.ι) (p.obj x).left.2
  let T₁ := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hU₁c U₁.ι
  let j₁ : T₁ ⟶ p.obj x := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hU₁c U₁.ι
  obtain ⟨x₁, ρ, hρ⟩ := hp.exists_lift j₁ x rfl
  have hx₁ : p.obj x₁ = T₁ := IsHomLift.domain_eq p j₁ ρ
  let jρ := V.map (p.map ρ)
  have : IsOpenImmersion (V.map j₁) := inferInstanceAs (IsOpenImmersion U₁.ι)
  obtain ⟨-, hopen, hrange⟩ := toScheme_map_lift_of_isOpenImmersion B S hS p j₁ ρ
  have : IsOpenImmersion jρ := hopen
  have : IsAffine (V.obj T₁) := hU₁aff
  have : IsAffine (V.obj (p.obj x₁)) := IsAffine.of_isIso (eqToHom (congrArg V.obj hx₁))
  have hS₁ : B.inclusion.map (p.obj x₁).hom = jρ ≫ fS :=
    (toScheme_map_comp_inclusion_map_hom B S hS p ρ).symm
  have : LocallyOfFiniteType fS := hU
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x₁).hom) := by
    rw [hS₁]
    infer_instance
  have hrange₁ : Set.range jρ.base = (U₁ : Set _) := hrange.trans U₁.range_ι
  have hjρU : ∀ t, jρ.base t ∈ (U₁ : Set _) := fun t => hrange₁ ▸ ⟨t, rfl⟩
  have hx₁G : Set.range (B.inclusion.map (p.obj x₁).hom).base ⊆ (G : Set S) := by
    rintro _ ⟨t, rfl⟩
    rw [hS₁, Scheme.Hom.comp_apply]
    exact hU₁G (hjρU t)
  -- versality at a point of `U₁` is versality at its image in `U`
  have hiff : ∀ t : V.obj (p.obj x₁),
      IsVersalAt (q.obj x₁) q t x₁ rfl ↔ IsVersalAt (q.obj x) q (jρ.base t) x rfl := by
    intro t
    refine isVersalAt_iff_restrict B S hS p hp hGaff.fromSpec rfl rfl ρ jρ ‹_›
      (by simp only [schemeMap, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) t ?_ ?_
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      show fS.base (((q.obj x).left.fromSpecResidueField (jρ.base t)).base k) ∈ G
      have hk : ((q.obj x).left.fromSpecResidueField (jρ.base t)).base k = jρ.base t := by
        have := Scheme.range_fromSpecResidueField (X := (q.obj x).left) (jρ.base t)
        exact (Set.ext_iff.mp this _).mp ⟨k, rfl⟩
      rw [hk]
      exact hU₁G (hjρU t)
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      show (B.inclusion.map (p.obj x₁).hom).base
        (((q.obj x₁).left.fromSpecResidueField t).base k) ∈ G
      exact hx₁G ⟨_, rfl⟩
  obtain ⟨u₀', hu₀'⟩ : u₀ ∈ Set.range jρ.base := hrange₁ ▸ hu₀U₁
  obtain ⟨W₁, hu₀W₁, hW₁⟩ := exists_open_isVersalAt_of_faithful_of_isAffine B S hS p hp hRS hZ
    hD good heff x₁ G hG hGaff hx₁G u₀' ((hiff u₀').mpr (by rw [hu₀']; exact hvers))
  refine ⟨jρ.opensFunctor.obj W₁, ⟨u₀', hu₀W₁, hu₀'⟩, ?_⟩
  rintro _ ⟨t, htW, rfl⟩ hft
  exact (hiff t).mp (hW₁ t htW (isFiniteTypePoint_of_isOpenImmersion jρ t hft))

end Deformation.Artin

end
