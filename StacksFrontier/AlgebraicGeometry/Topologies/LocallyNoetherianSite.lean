module

public import StacksFrontier.AlgebraicGeometry.Topologies.LocallyNoetherianObjects

/-!
# The site of locally Noetherian schemes over a base

Let `τ` be one of the five topologies Zariski, étale, smooth, syntomic and fppf, let `B` be a big
`τ`-site and let `S` be a scheme of `B`. The big site `(Sch/S)_τ` is the slice
`Over (base B S hS)` with the coverings `AlgebraicGeometry.BigSite.IsOverCovering`, the families
over `S` whose underlying family is a covering of `B`. Stacks 0GE1 studies the full subcategory
`(Noetherian/S)` on the objects whose underlying scheme is locally Noetherian, endowed with the
coverings of `(Sch/S)_τ` all of whose objects are locally Noetherian, and lists five facts about
it. This file proves all five, uniformly in `τ`, and bundles them in
`AlgebraicGeometry.BigSite.NoetherianOver.closure_isSite_isContinuous_isCocontinuous`.

## Main definitions

* `AlgebraicGeometry.BigSite.IsOverCovering`: the coverings of `(Sch/S)_τ`.
* `AlgebraicGeometry.BigSite.locallyNoetherianOver`: the locally Noetherian objects of
  `(Sch/S)_τ`, as an object property.
* `AlgebraicGeometry.BigSite.NoetherianOver`: the full subcategory `(Noetherian/S)`, with its
  inclusion `NoetherianOver.ι`, its coverings `NoetherianOver.IsCovering`, their coverage
  `NoetherianOver.coverage`, and the Grothendieck
  topology `NoetherianOver.topology` they generate: the site `(Noetherian/S)_τ`.

## Main results

* `AlgebraicGeometry.BigSite.NoetherianOver.hasPullback_and_preservesLimit`: part (2), the fibre
  product along a morphism locally of finite type exists in `(Noetherian/S)` and agrees with the
  one in `(Sch/S)`.
* `AlgebraicGeometry.BigSite.isLocallyNoetherian_of_isOverCovering`: part (3).
* `AlgebraicGeometry.BigSite.NoetherianOver.isSite`: part (4).
* `AlgebraicGeometry.BigSite.NoetherianOver.isContinuous_ι`,
  `AlgebraicGeometry.BigSite.NoetherianOver.isCocontinuous_ι` and the covering-level statements
  `NoetherianOver.isOverCovering_map_ι`, `NoetherianOver.preservesLimit_cospan_ι`,
  `NoetherianOver.exists_isCovering_map_ι`: part (5).
* `AlgebraicGeometry.BigSite.NoetherianOver.closure_isSite_isContinuous_isCocontinuous`: all five
  parts together.

## Implementation notes

The source assumes `S` locally Noetherian, which none of the five parts uses: every statement
here holds for any scheme `S` of the big site.

Continuity and cocontinuity are proved in two forms: Stacks' own (Sites, Definitions 00WU and
00XJ), on covering families, and Mathlib's `CategoryTheory.Functor.IsContinuous` and
`CategoryTheory.Functor.IsCocontinuous` for the generated topologies. The subcategory does not
have all fibre products (Stacks 0GE2), so continuity for the Grothendieck topologies is proved
directly from the sheaf condition on covering families, testing compatibility on the fibre
products of two members of a covering, which lie in the subcategory by part (2).

## References

* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigSite

universe u

variable {τ : CoveringTopology} (B : BigSite.{u} τ) (S : Scheme.{u}) (hS : S.size < cutoff τ B)

/-- The coverings of the big site `(Sch/S)_τ`: the families of morphisms over `S` whose
underlying family is a covering of the big site `B`. -/
def IsOverCovering (E : Covering.{u + 1, u, u + 1} (Over (base B S hS))) : Prop :=
  isCovering τ B ⟨E.1.left, E.2.map (Over.forget (base B S hS))⟩

/-- The objects of `(Sch/S)_τ` whose underlying scheme is locally Noetherian. -/
def locallyNoetherianOver : ObjectProperty (Over (base B S hS)) :=
  fun X => IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj X.left)

/-- The full subcategory `(Noetherian/S)` of `(Sch/S)_τ` on the locally Noetherian objects. -/
abbrev NoetherianOver := (locallyNoetherianOver B S hS).FullSubcategory

namespace NoetherianOver

/-- The inclusion functor `(Noetherian/S) ⥤ (Sch/S)`. -/
abbrev ι : NoetherianOver B S hS ⥤ Over (base B S hS) := ObjectProperty.ι _

/-- The coverings of `(Noetherian/S)_τ`: the coverings of `(Sch/S)_τ` whose objects are in
`(Noetherian/S)`. -/
def IsCovering (E : Covering.{u + 1, u, u + 1} (NoetherianOver B S hS)) : Prop :=
  IsOverCovering B S hS ⟨(ι B S hS).obj E.1, E.2.map (ι B S hS)⟩

end NoetherianOver

variable {B S hS}

/-- A morphism of a covering family of `(Sch/S)_τ` is locally of finite type. -/
private theorem locallyOfFiniteType_of_isOverCovering
    {E : Covering.{u + 1, u, u + 1} (Over (base B S hS))} (hE : IsOverCovering B S hS E)
    (i : E.2.I₀) : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map (E.2.f i).left) :=
  coveringMorphismProperty_le_locallyOfFiniteType τ _
    (coveringMorphismProperty_of_isCovering B (𝒰 := ⟨E.1.left, E.2.map (Over.forget _)⟩) hE i)

/-- A covering sieve of a big site contains the presieve of one of its chosen covering
families. -/
private theorem exists_isCovering_le {X : siteCategory B} {R : Sieve X}
    (hR : R ∈ siteTopology τ B X) :
    ∃ E : PreZeroHypercover.{u + 1} X, isCovering τ B ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  cases τ with
  | zariski => exact exists_covering_refining_sieve _ B.precoverage id (siteCoverings_isSite _ B) hR
  | smooth => exact exists_covering_refining_sieve _ B.precoverage id (siteCoverings_isSite _ B) hR
  | etale =>
      exact exists_covering_refining_sieve _ B.precoverage (fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩)
        (siteCoverings_isSite _ B) hR
  | syntomic =>
      exact exists_covering_refining_sieve _ B.precoverage (fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩)
        (siteCoverings_isSite _ B) hR
  | fppf =>
      exact exists_covering_refining_sieve _ B.precoverage (fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩)
        (siteCoverings_isSite _ B) hR

/-- The sieve generated by a covering of `(Sch/S)_τ` is a covering sieve of `(Sch/S)_τ`. -/
theorem generate_mem_overTopology {X : Over (base B S hS)} {E : PreZeroHypercover.{u + 1} X}
    (hE : IsOverCovering B S hS ⟨X, E⟩) :
    Sieve.generate E.presieve₀ ∈ overTopology τ B S hS X := by
  rw [overTopology_eq_over, GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv X (Sieve.ofArrows E.X E.f) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  exact generate_mem_siteTopology τ B (E.map (Over.forget _)) hE

/-- **Stacks 0GE1 (3).** If `{Xᵢ ⟶ X}` is a covering of `(Sch/S)_τ` and `X` is locally
Noetherian, then every `Xᵢ` is locally Noetherian. -/
theorem isLocallyNoetherian_of_isOverCovering
    {E : Covering.{u + 1, u, u + 1} (Over (base B S hS))} (hE : IsOverCovering B S hS E)
    (hX : locallyNoetherianOver B S hS E.1) (i : E.2.I₀) :
    locallyNoetherianOver B S hS (E.2.X i) :=
  isLocallyNoetherian_of_isCovering B (𝒰 := ⟨E.1.left, E.2.map (Over.forget _)⟩) hE hX i

namespace NoetherianOver

/-- The pullback in `(Sch/S)` of a morphism of `(Noetherian/S)` locally of finite type, as an
object of `(Noetherian/S)`. -/
private noncomputable def pullbackObj {X Y Z : NoetherianOver B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.hom.left)) :
    NoetherianOver B S hS :=
  ⟨pullback ((ι B S hS).map f) ((ι B S hS).map g),
    isLocallyNoetherian_of_isPullback_over B S hS
      (IsPullback.of_hasPullback ((ι B S hS).map f) ((ι B S hS).map g)) hf Z.property⟩

/-- The pullback square in `(Sch/S)` lifted to `(Noetherian/S)`. -/
private theorem isPullback_pullbackObj {X Y Z : NoetherianOver B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.hom.left)) :
    IsPullback (ObjectProperty.homMk (pullback.fst _ _) : pullbackObj f g hf ⟶ X)
      (ObjectProperty.homMk (pullback.snd _ _) : pullbackObj f g hf ⟶ Z) f g :=
  IsPullback.of_map (ι B S hS)
    ((ι B S hS).map_injective (by simp only [Functor.map_comp]; exact pullback.condition))
    (IsPullback.of_hasPullback ((ι B S hS).map f) ((ι B S hS).map g))

/-- **Stacks 0GE1 (2).** For morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` of `(Noetherian/S)` with `f`
locally of finite type, the fibre product `X ×_Y Z` exists in `(Noetherian/S)` and agrees with
the fibre product in `(Sch/S)`: the inclusion preserves it. -/
theorem hasPullback_and_preservesLimit {X Y Z : NoetherianOver B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.hom.left)) :
    HasPullback f g ∧ PreservesLimit (cospan f g) (ι B S hS) := by
  have h := isPullback_pullbackObj f g hf
  refine ⟨h.hasPullback, preservesLimit_of_preserves_limit_cone h.isLimit ?_⟩
  exact (PullbackCone.isLimitMapConeEquiv h.cone (ι B S hS)).symm
    (IsPullback.of_hasPullback ((ι B S hS).map f) ((ι B S hS).map g)).isLimit

/-- A pullback square of underlying morphisms lifts to a pullback square in the slice. -/
private theorem isPullback_overHomMk {C : Type*} [Category C] {T : C} {A U V : Over T}
    (f : A ⟶ U) (g : V ⟶ U) {P : C} {π₁ : P ⟶ A.left} {π₂ : P ⟶ V.left}
    (h : IsPullback π₁ π₂ f.left g.left) (w : π₁ ≫ A.hom = π₂ ≫ V.hom) :
    IsPullback (Over.homMk π₁ w : Over.mk (π₂ ≫ V.hom) ⟶ A)
      (Over.homMk π₂ : Over.mk (π₂ ≫ V.hom) ⟶ V) f g :=
  IsPullback.of_map_of_faithful (Over.forget T) h

variable (B S hS) in
/-- **Stacks 0GE1 (4).** The coverings of `(Sch/S)_τ` whose objects are locally Noetherian
satisfy the axioms of a site on `(Noetherian/S)`. -/
theorem isSite : IsSite (IsCovering B S hS) := by
  have hB := siteCoverings_isSite τ B
  let K := ι B S hS ⋙ Over.forget (base B S hS)
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact hB.1 (K.map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    simpa [IsCovering, IsOverCovering, PreZeroHypercover.map, PreZeroHypercover.bind,
      PreZeroHypercover.pushforward] using
      hB.2.1 _ h𝒰 _ h𝒱 (fun i => congrArg K.obj (h i))
  · intro 𝒰 h𝒰 V g
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ := hB.2.2 ⟨K.obj 𝒰.1, 𝒰.2.map K⟩ h𝒰 V.obj.left g.hom.left
    have hpb' (i : 𝒰.2.I₀) : IsPullback (p₁ i) (p₂ i) (𝒰.2.f i).hom.left g.hom.left := hpb i
    have hQ (i : 𝒰.2.I₀) : IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj (P i)) := by
      have : IsLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).obj V.obj.left) :=
        V.property
      have := coveringMorphismProperty_le_locallyOfFiniteType τ _
        (coveringMorphismProperty_of_isCovering B (𝒰 := ⟨V.obj.left, ⟨𝒰.2.I₀, P, p₂⟩⟩) hcov i)
      exact LocallyOfFiniteType.isLocallyNoetherian ((schemeBelowInclusion (cutoff τ B)).map (p₂ i))
    have hw (i : 𝒰.2.I₀) : p₁ i ≫ (𝒰.2.X i).obj.hom = p₂ i ≫ V.obj.hom := by
      calc p₁ i ≫ (𝒰.2.X i).obj.hom = p₁ i ≫ ((𝒰.2.f i).hom.left ≫ 𝒰.1.obj.hom) :=
            congrArg _ (Over.w (𝒰.2.f i).hom).symm
        _ = p₂ i ≫ (g.hom.left ≫ 𝒰.1.obj.hom) := by
            simp only [← Category.assoc]
            exact (hpb' i).w =≫ _
        _ = p₂ i ≫ V.obj.hom := congrArg _ (Over.w g.hom)
    let Q (i : 𝒰.2.I₀) : NoetherianOver B S hS := ⟨Over.mk (p₂ i ≫ V.obj.hom), hQ i⟩
    let q₁ (i : 𝒰.2.I₀) : Q i ⟶ 𝒰.2.X i :=
      ObjectProperty.homMk (Over.homMk (p₁ i) (hw i))
    let q₂ (i : 𝒰.2.I₀) : Q i ⟶ V := ObjectProperty.homMk (Over.homMk (p₂ i) rfl)
    exact ⟨Q, q₁, q₂, fun i => IsPullback.of_map_of_faithful (ι B S hS)
      (isPullback_overHomMk _ _ (hpb' i) (hw i)), hcov⟩

variable (B S hS) in
/-- The coverage of `(Noetherian/S)_τ`: the presieves of its covering families. That these are
stable under base change is the base change axiom of `NoetherianOver.isSite`. -/
def coverage : Coverage (NoetherianOver B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X, IsCovering B S hS ⟨X, E⟩ ∧
    R = E.presieve₀}
  pullback X Y f R hR := by
    obtain ⟨E, hE, rfl⟩ := hR
    obtain ⟨P, p₁, p₂, hpb, hcov⟩ := (isSite B S hS).2.2 ⟨X, E⟩ hE Y f
    exact ⟨_, ⟨⟨E.I₀, P, p₂⟩, hcov, rfl⟩, fun Z g ⟨i⟩ => ⟨E.X i, p₁ i, E.f i, ⟨i⟩, (hpb i).w⟩⟩

variable (B S hS) in
/-- The Grothendieck topology of the site `(Noetherian/S)_τ`, generated by its coverings. -/
abbrev topology : GrothendieckTopology (NoetherianOver B S hS) :=
  (coverage B S hS).toGrothendieck

/-- **Stacks 0GE1 (5), the inclusion maps coverings to coverings.** The image under
`(Noetherian/S) ⥤ (Sch/S)` of a covering of `(Noetherian/S)_τ` is a covering of `(Sch/S)_τ`. -/
theorem isOverCovering_map_ι {E : Covering.{u + 1, u, u + 1} (NoetherianOver B S hS)}
    (hE : IsCovering B S hS E) :
    IsOverCovering B S hS ⟨(ι B S hS).obj E.1, E.2.map (ι B S hS)⟩ :=
  hE

/-- **Stacks 0GE1 (5), the inclusion preserves the fibre products of a covering.** For a
covering `{Xᵢ ⟶ X}` of `(Noetherian/S)_τ` and a morphism `T ⟶ X` of `(Noetherian/S)`, the
fibre product `Xᵢ ×_X T` exists in `(Noetherian/S)` and the inclusion into `(Sch/S)` preserves
it. -/
theorem preservesLimit_cospan_ι {E : Covering.{u + 1, u, u + 1} (NoetherianOver B S hS)}
    (hE : IsCovering B S hS E) (i : E.2.I₀) {T : NoetherianOver B S hS} (g : T ⟶ E.1) :
    HasPullback (E.2.f i) g ∧ PreservesLimit (cospan (E.2.f i) g) (ι B S hS) :=
  hasPullback_and_preservesLimit _ g (locallyOfFiniteType_of_isOverCovering hE i)

/-- The covering of `(Noetherian/S)_τ` with the same members as a covering of `(Sch/S)_τ` of a
locally Noetherian object. -/
private def liftCovering {X : NoetherianOver B S hS}
    (F : PreZeroHypercover.{u + 1} ((ι B S hS).obj X))
    (hF : IsOverCovering B S hS ⟨_, F⟩) : PreZeroHypercover.{u + 1} X where
  I₀ := F.I₀
  X i := ⟨F.X i, isLocallyNoetherian_of_isOverCovering hF X.property i⟩
  f i := ObjectProperty.homMk (F.f i)

/-- **Stacks 0GE1 (5), the inclusion is cocontinuous on coverings.** Every covering of
`(Sch/S)_τ` of an object of `(Noetherian/S)` is refined by the image of a covering of
`(Noetherian/S)_τ`. -/
theorem exists_isCovering_map_ι {X : NoetherianOver B S hS}
    (F : PreZeroHypercover.{u + 1} ((ι B S hS).obj X)) (hF : IsOverCovering B S hS ⟨_, F⟩) :
    ∃ E : PreZeroHypercover.{u + 1} X, IsCovering B S hS ⟨X, E⟩ ∧
      Nonempty ((E.map (ι B S hS)).Hom F) :=
  ⟨liftCovering F hF, hF, ⟨{ s₀ := id, h₀ := fun _ => 𝟙 _, w₀ := fun _ => Category.id_comp _ }⟩⟩

/-- The presieve of a covering of `(Noetherian/S)_τ` has pairwise fibre products. -/
instance hasPairwisePullbacks_presieve₀ {X : NoetherianOver B S hS}
    {E : PreZeroHypercover.{u + 1} X} [Fact (IsCovering B S hS ⟨X, E⟩)] :
    E.presieve₀.HasPairwisePullbacks where
  has_pullbacks := by
    rintro _ _ _ ⟨i⟩ _ _
    exact (preservesLimit_cospan_ι (Fact.out : IsCovering B S hS ⟨X, E⟩) i _).1

/-- The inclusion preserves the pairwise fibre products of a covering of `(Noetherian/S)_τ`. -/
instance preservesPairwisePullbacks_presieve₀ {X : NoetherianOver B S hS}
    {E : PreZeroHypercover.{u + 1} X} [Fact (IsCovering B S hS ⟨X, E⟩)] :
    (ι B S hS).PreservesPairwisePullbacks E.presieve₀ where
  preservesLimit := by
    rintro _ _ _ _ ⟨i⟩ _
    exact (preservesLimit_cospan_ι (Fact.out : IsCovering B S hS ⟨X, E⟩) i _).2

/-- **Stacks 0GE1 (5), continuity.** The inclusion `(Noetherian/S)_τ ⥤ (Sch/S)_τ` is
continuous: restriction along it carries sheaves to sheaves. -/
instance isContinuous_ι :
    (ι B S hS).IsContinuous (topology B S hS) (overTopology τ B S hS) where
  op_comp_isSheaf_of_types := fun ⟨G, H⟩ => by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [Presieve.isSheaf_coverage]
    rintro X _ ⟨E, hE, rfl⟩
    have : Fact (IsCovering B S hS ⟨X, E⟩) := ⟨hE⟩
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks, PreZeroHypercover.presieve₀,
      Presieve.map_ofArrows, Presieve.isSheafFor_iff_generate]
    exact H _ (generate_mem_overTopology (E := E.map (ι B S hS)) hE)

/-- **Stacks 0GE1 (5), cocontinuity.** The inclusion `(Noetherian/S)_τ ⥤ (Sch/S)_τ` is
cocontinuous: a covering sieve of `(Sch/S)_τ` on an object of `(Noetherian/S)` pulls back to a
covering sieve of `(Noetherian/S)_τ`. -/
instance isCocontinuous_ι :
    (ι B S hS).IsCocontinuous (topology B S hS) (overTopology τ B S hS) where
  cover_lift {X R} hR := by
    rw [overTopology_eq_over, GrothendieckTopology.mem_over_iff] at hR
    obtain ⟨E, hE, hle⟩ := exists_isCovering_le hR
    let F : PreZeroHypercover.{u + 1} ((ι B S hS).obj X) :=
      ⟨E.I₀, fun i => Over.mk (E.f i ≫ ((ι B S hS).obj X).hom), fun i => Over.homMk (E.f i)⟩
    have hF : IsOverCovering B S hS ⟨_, F⟩ := hE
    refine (coverage B S hS).mem_toGrothendieck_sieves_of_superset ?_
      ⟨liftCovering F hF, hF, rfl⟩
    rintro _ _ ⟨i⟩
    exact (Sieve.overEquiv_iff _ _).mp (hle _ _ ⟨i⟩)

variable (B S hS) in
/-- **Stacks 0GE1.** Let `τ` be one of the topologies Zariski, étale, smooth, syntomic and fppf,
let `B` be a big `τ`-site and `S` a scheme of `B`, and let `(Noetherian/S)` be the full
subcategory of `(Sch/S)` on the locally Noetherian objects.
1. If `f : X ⟶ Y` is a morphism of `(Sch/S)` locally of finite type with `Y` locally
   Noetherian, then `X` is locally Noetherian.
2. For morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` of `(Noetherian/S)` with `f` locally of finite
   type, the fibre product `X ×_Y Z` exists in `(Noetherian/S)` and agrees with the fibre
   product in `(Sch/S)`.
3. The members of a covering of `(Sch/S)_τ` of a locally Noetherian object are locally
   Noetherian.
4. The coverings of `(Sch/S)_τ` whose objects lie in `(Noetherian/S)` make `(Noetherian/S)` a
   site, `(Noetherian/S)_τ`.
5. The inclusion `(Noetherian/S)_τ ⥤ (Sch/S)_τ` is fully faithful, continuous and cocontinuous:
   it carries coverings to coverings and preserves the fibre products of their members, every
   covering of `(Sch/S)_τ` of an object of `(Noetherian/S)` is refined by the image of a
   covering of `(Noetherian/S)_τ`, and on the generated topologies it is
   `Functor.IsContinuous` and `Functor.IsCocontinuous`.

The source assumes `S` locally Noetherian; the statement holds without it. -/
@[stacks 0GE1 "all five parts, for each of the topologies Zariski, étale, smooth, syntomic, fppf"]
theorem closure_isSite_isContinuous_isCocontinuous :
    (∀ {X Y : Over (base B S hS)} (f : X ⟶ Y), locallyNoetherianOver B S hS Y →
      LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.left) →
        locallyNoetherianOver B S hS X) ∧
    (∀ {X Y Z : NoetherianOver B S hS} (f : X ⟶ Y) (g : Z ⟶ Y),
      LocallyOfFiniteType ((schemeBelowInclusion (cutoff τ B)).map f.hom.left) →
        HasPullback f g ∧ PreservesLimit (cospan f g) (ι B S hS)) ∧
    (∀ E : Covering.{u + 1, u, u + 1} (Over (base B S hS)), IsOverCovering B S hS E →
      locallyNoetherianOver B S hS E.1 → ∀ i, locallyNoetherianOver B S hS (E.2.X i)) ∧
    IsSite (IsCovering B S hS) ∧
    ((ι B S hS).Full ∧ (ι B S hS).Faithful ∧
      (∀ E : Covering.{u + 1, u, u + 1} (NoetherianOver B S hS), IsCovering B S hS E →
        IsOverCovering B S hS ⟨(ι B S hS).obj E.1, E.2.map (ι B S hS)⟩ ∧
        ∀ (i : E.2.I₀) {T : NoetherianOver B S hS} (g : T ⟶ E.1),
          HasPullback (E.2.f i) g ∧ PreservesLimit (cospan (E.2.f i) g) (ι B S hS)) ∧
      (∀ (X : NoetherianOver B S hS) (F : PreZeroHypercover.{u + 1} ((ι B S hS).obj X)),
        IsOverCovering B S hS ⟨_, F⟩ → ∃ E : PreZeroHypercover.{u + 1} X,
          IsCovering B S hS ⟨X, E⟩ ∧ Nonempty ((E.map (ι B S hS)).Hom F)) ∧
      (ι B S hS).IsContinuous (topology B S hS) (overTopology τ B S hS) ∧
      (ι B S hS).IsCocontinuous (topology B S hS) (overTopology τ B S hS)) :=
  ⟨fun f hY hf => isLocallyNoetherian_of_locallyOfFiniteType_over B S hS f hY hf,
    fun f g hf => hasPullback_and_preservesLimit f g hf,
    fun _ hE hX i => isLocallyNoetherian_of_isOverCovering hE hX i,
    isSite B S hS,
    inferInstance, inferInstance,
    fun _ hE => ⟨isOverCovering_map_ι hE, fun i _ g => preservesLimit_cospan_ι hE i g⟩,
    fun _ F hF => exists_isCovering_map_ι F hF,
    inferInstance, inferInstance⟩

end NoetherianOver

end AlgebraicGeometry.BigSite

end
