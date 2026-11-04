module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.FullSubcategorySite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transporting refinability of covering sieves

`CategoryTheory.GrothendieckTopology.IsRefinableBy J Q S` says that the covering sieve `S`
contains a covering family all of whose members satisfy `Q`. For the site of a category fibred in
groupoids over a localized big site (Stacks 06TP) that property has to be transported twice, and
each step is recorded here.

* `CategoryTheory.GrothendieckTopology.isRefinableBy_over`: from a site `(𝒞, J)` to the localized
  site `(Over X, J.over X)`, with `Q` replaced by its inverse image under `Over.forget X`. A
  covering sieve of `V : Over X` corresponds, under `CategoryTheory.Sieve.overEquiv`, to a
  covering sieve of `V.left`, and a `Q`-morphism of that sieve is the image of the `Q`-morphism
  `Over.homMk` of the sieve upstairs.

* `CategoryTheory.Functor.isRefinableBy_inheritedTopology`: from a site `(𝒞, J)` to the site
  `p.inheritedTopology J` (Stacks 06NV) of a fibred category `p : 𝒮 ⥤ 𝒞` all of whose morphisms
  are strongly cartesian — a category fibred in groupoids, Stacks 003V. Here `Q` is again replaced
  by its inverse image, and the content is that a covering family of `𝒮` whose image merely
  *generates* a covering sieve of `𝒞` can be refined by one whose members are cartesian lifts of
  `Q`-morphisms: refine the image downstairs by a `Q`-family, lift each of its members through the
  factorisation it has through the given family, and compose.

Both are stated so that they feed `CategoryTheory.ObjectProperty.isContinuous_ι_inheritedTopology`
and `CategoryTheory.ObjectProperty.isCocontinuous_ι_inheritedTopology`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- The inverse image of a morphism property stable under base change along a functor preserving
fibre products is again stable under base change. (Mathlib already has the corresponding
instances for `MorphismProperty.ContainsIdentities` and
`MorphismProperty.IsStableUnderComposition`, which need no hypothesis on the functor.) -/
@[sga "4 IV 9.1.7" "c)"]
instance MorphismProperty.isStableUnderBaseChange_inverseImage (Q : MorphismProperty 𝒞)
    [Q.IsStableUnderBaseChange] (F : 𝒮 ⥤ 𝒞) [PreservesLimitsOfShape WalkingCospan F] :
    (Q.inverseImage F).IsStableUnderBaseChange where
  of_isPullback sq hg := Q.of_isPullback (sq.map F) hg

/-! ### Fibre products in a category fibred in groupoids -/

section Fibered

variable (p : 𝒮 ⥤ 𝒞) [p.IsFibered] [HasPullbacks 𝒞]
  (hcart : ∀ {a b : 𝒮} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f)

include hcart

/-- In a fibred category all of whose morphisms are strongly cartesian over their images — a
category fibred in groupoids (Stacks 003V) — *any* two morphisms with a common target have a
fibre product, as soon as the base has all fibre products. This is Stacks 06N5 with its
cartesianness hypothesis discharged. -/
lemma Functor.hasPullback_of_forall_isStronglyCartesian {a b c : 𝒮} (g : b ⟶ a) (f : c ⟶ a) :
    HasPullback g f := by
  have := hcart g
  exact Functor.IsFibered.hasPullback_of_isStronglyCartesian p g f

/-- In a fibred category all of whose morphisms are strongly cartesian over their images, the
inverse image of a morphism property stable under base change is stable under base change: the
structure functor carries a fibre product square to a fibre product square (Stacks 06N5). -/
lemma Functor.isStableUnderBaseChange_inverseImage (Q : MorphismProperty 𝒞)
    [Q.IsStableUnderBaseChange] : (Q.inverseImage p).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f _ _ _} sq hg :=
    Q.of_isPullback (p.map_isPullback_of_isPullback (hcart f) _ sq) hg

end Fibered

/-! ### Localization at an object -/

/-- A sieve is refinable by `Q` as soon as the `Q`-morphisms in it generate a covering sieve. -/
private lemma isRefinableBy_of_generate_mem {C : Type*} [Category C] {J : GrothendieckTopology C}
    {Q : MorphismProperty C} {X : C} {S : Sieve X}
    (h : Sieve.generate (fun ⦃_⦄ k ↦ Q k ∧ S.arrows k) ∈ J X) : J.IsRefinableBy Q S :=
  ⟨_, fun _ _ hk ↦ hk.2, fun _ _ hk ↦ hk.1, h⟩

/-- **Refinability transported to a localized site.** If every `J`-covering sieve of `𝒞` is
refined by a covering family of `Q`-morphisms, then every covering sieve of `Over X` for
`J.over X` is refined by a covering family of morphisms whose underlying morphism of `𝒞`
satisfies `Q`.

The covering sieves of `J.over X` are, by definition, those whose image under
`CategoryTheory.Sieve.overEquiv` covers downstairs; and a morphism `h` of `𝒞` lies in that image
precisely when the morphism `Over.homMk h` of `Over X` lies in the sieve upstairs
(`CategoryTheory.Sieve.overEquiv_iff`), so a `Q`-refinement downstairs is the image of one
upstairs. -/
theorem GrothendieckTopology.isRefinableBy_over (J : GrothendieckTopology 𝒞)
    (Q : MorphismProperty 𝒞) (X : 𝒞)
    (hJQ : ∀ ⦃Y : 𝒞⦄ (S : Sieve Y), S ∈ J Y → J.IsRefinableBy Q S)
    ⦃V : Over X⦄ (T : Sieve V) (hT : T ∈ (J.over X) V) :
    (J.over X).IsRefinableBy (Q.inverseImage (Over.forget X)) T := by
  obtain ⟨R, hRle, hRQ, hRJ⟩ := hJQ _ ((J.mem_over_iff T).1 hT)
  refine isRefinableBy_of_generate_mem (Q := Q.inverseImage (Over.forget X)) ?_
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ hRJ
  rw [Sieve.generate_le_iff]
  intro W h hh
  rw [Sieve.overEquiv_iff]
  exact Sieve.le_generate _ _ _ ⟨hRQ h hh, (Sieve.overEquiv_iff T h).1 (hRle _ _ hh)⟩

/-! ### The site inherited by a fibred category -/

/-- The factorisation recorded by `CategoryTheory.Functor.IsHomLift`, with the codomain of the
base morphism literally the image of the codomain: if `φ : a ⟶ b` lies over `f : R ⟶ p.obj b`,
then `p.map φ` is `f` preceded by the identification of `p.obj a` with `R`. -/
private lemma map_eq_eqToHom_comp (p : 𝒮 ⥤ 𝒞) {R : 𝒞} {a b : 𝒮}
    (f : R ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ] :
    p.map φ = eqToHom (IsHomLift.domain_eq p f φ) ≫ f := by
  simpa using IsHomLift.fac' p f φ

/-- **Refinability transported to the site inherited by a category fibred in groupoids.** Let
`p : 𝒮 ⥤ 𝒞` be a fibred category in which every morphism is strongly cartesian over its image —
a category fibred in groupoids (Stacks 003V) — over a site `(𝒞, J)` with all fibre products, and
suppose every `J`-covering sieve is refined by a covering family of `Q`-morphisms. Then every
covering sieve of `p.inheritedTopology J` (Stacks 06NV) is refined by a covering family of
morphisms whose image satisfies `Q`.

The generating covering families of `p.inheritedTopology J` are the families whose image
*generates* a covering sieve downstairs, so their own members need not lie over `Q`-morphisms;
the refinement is obtained by taking a `Q`-refinement `R₀` downstairs, factoring each member of
`R₀` through the image of a member of the given family, and lifting the factor cartesianly. The
composite lies over the `Q`-morphism up to the identification of its source, whence the
`eqToHom` bookkeeping below. -/
theorem Functor.isRefinableBy_inheritedTopology (p : 𝒮 ⥤ 𝒞) [p.IsFibered] [HasPullbacks 𝒞]
    (hcart : ∀ {a b : 𝒮} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f)
    (J : GrothendieckTopology 𝒞) (Q : MorphismProperty 𝒞)
    [Q.ContainsIdentities] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (hJQ : ∀ ⦃Y : 𝒞⦄ (S : Sieve Y), S ∈ J Y → J.IsRefinableBy Q S)
    ⦃x : 𝒮⦄ (S : Sieve x) (hS : S ∈ p.inheritedTopology J x) :
    (p.inheritedTopology J).IsRefinableBy (Q.inverseImage p) S := by
  have hbc := p.isStableUnderBaseChange_inverseImage hcart Q
  refine Precoverage.isRefinableBy_of_mem_toGrothendieck
    (fun _ _ _ g f _ ↦ p.hasPullback_of_forall_isStronglyCartesian hcart g f) ?_ S hS
  intro y R hR
  obtain ⟨R₀, hR₀le, hR₀Q, hR₀J⟩ := hJQ _ ((J.mem_toPrecoverage_iff _).1 hR.2)
  refine isRefinableBy_of_generate_mem (Q := Q.inverseImage p) ?_
  refine Precoverage.generate_mem_toGrothendieck ⟨fun _ g _ ↦ hcart g, ?_⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  refine J.superset_covering ?_ hR₀J
  rw [Sieve.generate_le_iff]
  intro V h hh
  obtain ⟨W, i, e, he, hie⟩ := hR₀le _ _ hh
  obtain ⟨hg⟩ := he
  rename_i z g
  obtain ⟨w, u, hu⟩ := Functor.IsFibered.exists_isStronglyCartesian p (Y := z) i
  have := hu
  have hdom : p.obj w = V := IsHomLift.domain_eq p i u
  have hmapu : p.map u = eqToHom hdom ≫ i := map_eq_eqToHom_comp p i u
  have hmap : p.map (u ≫ g) = eqToHom hdom ≫ h := by
    rw [p.map_comp, hmapu, Category.assoc, hie]
  have hmem : (Q.inverseImage p) (u ≫ g) ∧ (Sieve.generate R).arrows (u ≫ g) := by
    refine ⟨?_, (Sieve.generate R).downward_closed (Sieve.le_generate _ _ _ hg) u⟩
    rw [MorphismProperty.inverseImage_iff, hmap]
    exact Q.comp_mem _ _ (MorphismProperty.ContainsIdentities.eqToHom Q hdom) (hR₀Q h hh)
  exact ⟨p.obj w, eqToHom hdom.symm, p.map (u ≫ g), Presieve.map_map hmem, by
    rw [hmap]; simp⟩

end CategoryTheory

end
