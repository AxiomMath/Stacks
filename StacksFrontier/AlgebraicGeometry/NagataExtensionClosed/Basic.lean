module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.NormalClosure
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.NagataExtensionClosed.Inputs
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataValuativeCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The essentially-finite-type extension test forces closedness

Over a Nagata base, a quasi-compact morphism between schemes locally of finite type which
satisfies the essentially-finite-type extension test is closed, and stays closed after
adjoining finitely many affine coordinates.

This is the implication left unproved by
`Stacks.AlgebraicGeometry.NagataValuativeCriterion`, where it is named
`ExtensionImpliesClosedAffineSpaceBaseChange`; that named hypothesis is discharged here.

## Main results

* `isClosedMap_of_extension`: the extension test forces `f` itself to be closed.
* `extensionImpliesClosedAffineSpaceBaseChange`: the extension test forces every
  finite-dimensional affine-space base change of `f` to be closed, i.e. the named implication
  of the reduction module is true.
* `universallyClosed_tfae_essentiallyFiniteType_of_closedAffineSpaceBaseChange`: the three
  conditions of Stacks 0GWV are equivalent, given only the converse implication of Stacks 05JX.

## Implementation notes

The argument is the source's.  Suppose a closed `Z` has non-closed image `E = f '' Z`.  Both
`Z` and `E` are constructible because the spaces are Noetherian, so `closure E \ E` is a
nonempty constructible set and meets some open subspace of the target in a point closed in
that subspace.  Working on a Nagata affine open `Spec R` around that point, the point `y` is
specialized to by a point `t ∈ E` which it *covers*, by stability of constructibly-closed sets
under specialization in a spectral space.  Over the residue field at `t` one chooses a closed
point of the fibre meeting `Z`; the Nagata hypothesis makes the integral closure of `R / t` in
the resulting finite residue extension module-finite, hence a Noetherian normal domain `B` with
a finite map `Spec B ⟶ Spec R` hitting `y`.  That exhibits a one-dimensional normal integral
finite-type test curve, and the extension test produces a point of `Z` over `y`, contradicting
`y ∉ E`.

Two elaboration constraints shape the proof.  The extension test of the reduction module
is stated with `let`-bindings, so it is applied in term position and never `intro`'d: an
`intro` turns each binding into a let-bound free variable whose `IsDomain` field typeclass
synthesis will not unfold.  And the dimension-one hypothesis is converted to `Order.coheight`
exactly once, in `exists_open_punctured_subset` and `ringKrullDim_stalk_eq_one_of_covBy`, so
that the rest of the argument never mentions Krull dimension.

## References

* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.NagataExtensionClosed

open NagataValuativeCriterion

/-! ### Stability of the extension test under base change -/

/-- The extension test is inherited by any base change of `f`: a test diagram for `f'` maps to
one for `f`, and the lift obtained for `f` pairs with the given lower morphism to give a lift
into the pullback. -/
theorem extension_of_isPullback
    {S X Y X' Y' : Scheme.{u}} (hY : Y ⟶ S) (f : X ⟶ Y)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (hpull : IsPullback f' a b f) :
    HasEssentiallyFiniteTypeValuativeExtension f' (b ≫ hY) := by
  dsimp only [HasEssentiallyFiniteTypeValuativeExtension] at hext ⊢
  intro C p hp hpc hn hi c hc hd q v hq hv hdom g hg
  obtain ⟨l, hl, hlg⟩ := hext C p hp hpc hn hi c hc hd (q ≫ b) (v ≫ a)
    (by simpa only [Category.assoc] using hq)
    (by rw [Category.assoc, ← hpull.w, ← Category.assoc, hv, Category.assoc])
    hdom g hg
  have hcomp : (C.fromSpecStalk c ≫ q) ≫ b = l ≫ f := by
    simpa only [Category.assoc] using hl.symm
  refine ⟨hpull.lift (C.fromSpecStalk c ≫ q) l hcomp, hpull.lift_fst .., ?_⟩
  apply hpull.hom_ext
  · simp only [Category.assoc, hpull.lift_fst]
    rw [← Category.assoc, ← hg, Category.assoc, ← hv]
  · simpa only [Category.assoc, hpull.lift_snd] using hlg

/-- The extension test passes to the base change along the projection of an affine space over
the target. -/
theorem extension_of_affineSpace
    {S X Y : Scheme.{u}} (hY : Y ⟶ S) (f : X ⟶ Y)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY) (n : ℕ) :
    HasEssentiallyFiniteTypeValuativeExtension
      (AffineSpace.map (ULift.{u} (Fin n)) f)
      ((AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) ≫ hY) :=
  extension_of_isPullback hY f hext _ _ _ (AffineSpace.isPullback_map f)

/-! ### Propagating membership of a closed set from the generic point -/

/-- A morphism out of an integral scheme sending the generic point into a closed set sends
every point into it, by stability of a closed set under specialization. -/
theorem map_mem_closed_of_genericPoint_mem
    {C X : Scheme.{u}} [IsIntegral C] (a : C ⟶ X)
    (Z : Set X) (hZ : IsClosed Z)
    (hη : a (genericPoint C) ∈ Z) :
    ∀ c : C, a c ∈ Z := by
  intro c
  have hspec : Specializes (genericPoint C) c :=
    (genericPoint_spec C).specializes (Set.mem_univ c)
  have hspecX : Specializes (a.base.hom (genericPoint C)) (a.base.hom c) :=
    a.base.hom.map_specializes hspec
  exact hZ.stableUnderSpecialization hspecX hη

/-- The spectrum of the fraction field maps its generic point to the generic point. -/
private theorem spec_map_fractionRing_genericPoint (A : Type u) [CommRing A] [IsDomain A] :
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
      (genericPoint (Spec (.of (FractionRing A)))) = genericPoint (Spec (.of A)) := by
  apply PrimeSpectrum.ext
  rw [genericPoint_eq_bot_of_affine (.of (FractionRing A)), genericPoint_eq_bot_of_affine (.of A)]
  change Ideal.comap (algebraMap A (FractionRing A)) ⊥ = ⊥
  ext x
  simp

/-- The lift supplied by the extension test carries the closed point of the test local ring into
any closed set containing the image of the generic morphism, because the closed point is a
specialization of the generic point of the test local ring. -/
theorem extension_closedPoint_mem
    {S X Y C : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (p : C ⟶ S) (hp : LocallyOfFiniteType p) (hpc : QuasiCompact p)
    (hnormal : IsNormal C) (hintegral : IsIntegral C)
    (c : C) (hc : IsClosed ({c} : Set C))
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1)
    (U : C.Opens) (hU : U = ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩)
    (q : C ⟶ Y) (a : U.toScheme ⟶ X)
    (hq : q ≫ hY = p) (hcomm : a ≫ f = U.ι ≫ q)
    (hdom : IsDomain (C.presheaf.stalk c))
    (g : Spec (.of (FractionRing (C.presheaf.stalk c))) ⟶ U.toScheme)
    (hg : g ≫ U.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
        C.fromSpecStalk c)
    (Z : Set X) (hZ : IsClosed Z)
    (hgenZ : ∀ z, (g ≫ a) z ∈ Z) :
    ∃ l : Spec (.of (C.presheaf.stalk c)) ⟶ X,
      l ≫ f = C.fromSpecStalk c ≫ q ∧
        l (IsLocalRing.closedPoint (C.presheaf.stalk c)) ∈ Z := by
  let A := C.presheaf.stalk c
  let K := FractionRing A
  subst U
  let i : Spec (.of K) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : IsDomain A := hdom
  obtain ⟨l, hl, hgen⟩ := hext C p hp hpc hnormal hintegral c hc hdim q a hq hcomm hdom g hg
  have hiη : i (genericPoint (Spec (.of K))) = genericPoint (Spec (.of A)) :=
    spec_map_fractionRing_genericPoint A
  have hηZ : l (genericPoint (Spec (.of A))) ∈ Z := by
    have heq : l.base.hom (genericPoint (Spec (.of A))) =
        (g ≫ a).base.hom (genericPoint (Spec (.of K))) := by
      calc
        l.base.hom (genericPoint (Spec (.of A))) =
            l.base.hom (i (genericPoint (Spec (.of K)))) := by rw [hiη]
        _ = (i ≫ l).base.hom (genericPoint (Spec (.of K))) := rfl
        _ = (g ≫ a).base.hom (genericPoint (Spec (.of K))) :=
          congrArg (fun m : Spec (.of K) ⟶ X => m.base.hom (genericPoint (Spec (.of K)))) hgen
    change l.base.hom (genericPoint (Spec (.of A))) ∈ Z
    rw [heq]
    exact hgenZ _
  exact ⟨l, hl, map_mem_closed_of_genericPoint_mem l Z hZ hηZ _⟩

/-! ### Shrinking the domain of definition to a punctured neighbourhood -/

/-- On an integral Noetherian scheme, a closed point whose local ring has dimension one has
an open neighbourhood whose puncture lies in any given open containing the generic point.  The
dimension hypothesis is what makes every point strictly between the two equal to one of them. -/
theorem exists_open_punctured_subset
    {C : Scheme.{u}} [IsIntegral C] [NoetherianSpace C]
    (c : C) (hc : IsClosed ({c} : Set C))
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1)
    (U : C.Opens) (hη : genericPoint C ∈ U) (hcU : c ∉ U) :
    ∃ V : C.Opens, c ∈ V ∧ (V : Set C) \ {c} ⊆ U := by
  have hheight : Order.coheight c = 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  have hgen : ∀ z, z ∉ U → z ⤳ c → z = c := by
    intro z hz hzc
    by_contra hne
    have hcz : c < z := ⟨hzc, fun h ↦ hne (hzc.antisymm h).eq⟩
    have hzη : z < genericPoint C :=
      ⟨genericPoint_specializes z, fun h ↦
        hz ((h.antisymm (genericPoint_specializes z)).eq ▸ hη)⟩
    have h₁ := Order.coheight_add_one_le hzη
    have h₂ := Order.coheight_add_one_le hcz
    rw [hheight] at h₂
    have h₃ : (1 : ℕ∞) ≤ Order.coheight z := le_trans (by simp) h₁
    have : (2 : ℕ∞) ≤ 1 := (add_le_add h₃ (le_refl (1 : ℕ∞))).trans h₂
    norm_num at this
  obtain ⟨V, hV, hcV, hVU⟩ := exists_open_punctured_subset_of_specializes
    c hc U U.isOpen hcU hgen
  exact ⟨⟨V, hV⟩, hcV, hVU⟩

/-- On an integral scheme the canonical morphism from the spectrum of a local ring sends the
generic point to the generic point. -/
@[ega "I 7.2.8" "Case 1°"]
theorem fromSpecStalk_genericPoint
    {C : Scheme.{u}} [IsIntegral C] (c : C) :
    C.fromSpecStalk c (genericPoint (Spec (C.presheaf.stalk c))) = genericPoint C := by
  have hη : genericPoint C ∈ Set.range (C.fromSpecStalk c) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes c
  obtain ⟨z, hz⟩ := hη
  have h := (genericPoint_specializes z).map (C.fromSpecStalk c).continuous
  rw [hz] at h
  exact (h.antisymm (genericPoint_specializes _)).eq

/-- On an integral scheme the generic morphism of a local ring — the spectrum of its fraction
field mapping to the scheme — lands on the generic point. -/
theorem fractionRing_fromSpecStalk_apply
    {C : Scheme.{u}} [IsIntegral C] (c : C)
    (z : Spec (.of (FractionRing (C.presheaf.stalk c)))) :
    (Spec.map (CommRingCat.ofHom
      (algebraMap (C.presheaf.stalk c) (FractionRing (C.presheaf.stalk c)))) ≫
        C.fromSpecStalk c) z = genericPoint C := by
  have hz : z = genericPoint (Spec (.of (FractionRing (C.presheaf.stalk c)))) :=
    Subsingleton.elim _ _
  rw [hz]
  change C.fromSpecStalk c _ = _
  rw [← fromSpecStalk_genericPoint c]
  congr 1
  exact spec_map_fractionRing_genericPoint _

/-- A point whose image under an injective continuous map is closed is closed. -/
private theorem isClosed_singleton_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (hinj : Function.Injective f) {x : X}
    (h : IsClosed ({f x} : Set Y)) : IsClosed ({x} : Set X) := by
  convert h.preimage hf using 1
  ext z
  exact hinj.eq_iff.symm

/-- A partial morphism to `X` over `Y` defined on an open containing the generic point of a
one-dimensional normal integral test curve, whose values lie in a closed `Z`, forces the image
of the closed point under the lower morphism to lie in `f '' Z`.  If the closed point is already
in the domain of definition there is nothing to prove; if not, the domain is shrunk to the
puncture of a neighbourhood, where the extension test applies. -/
theorem image_mem_of_partialMap
    {S X Y C : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (p : C ⟶ S) [LocallyOfFiniteType p]
    [IsNormal C] [IsIntegral C] [NoetherianSpace C]
    (c : C) (hc : IsClosed ({c} : Set C))
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1)
    (q : C ⟶ Y) (hq : q ≫ hY = p)
    (W : C.Opens) (hη : genericPoint C ∈ W)
    (a : W.toScheme ⟶ X) (ha : a ≫ f = W.ι ≫ q)
    (Z : Set X) (hZ : IsClosed Z) (haZ : ∀ z, a z ∈ Z) :
    q c ∈ f '' Z := by
  classical
  by_cases hcW : c ∈ W
  · refine ⟨a ⟨c, hcW⟩, haZ _, ?_⟩
    exact congrArg (fun k : W.toScheme ⟶ Y ↦ k ⟨c, hcW⟩) ha
  obtain ⟨V, hcV, hVW⟩ := exists_open_punctured_subset c hc hdim W hη hcW
  let c' : V.toScheme := ⟨c, hcV⟩
  have : Nonempty V := ⟨c'⟩
  have : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set C)
  have hc' : IsClosed ({c'} : Set V.toScheme) :=
    isClosed_singleton_of_injective V.ι.continuous V.ι.isOpenEmbedding.injective hc
  have hdim' : ringKrullDim (V.toScheme.presheaf.stalk c') = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (V.stalkIso c').commRingCatIsoToRingEquiv]
    exact hdim
  let U : V.toScheme.Opens := ⟨({c'} : Set V.toScheme)ᶜ, hc'.isOpen_compl⟩
  have hrange : Set.range (U.ι ≫ V.ι) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hVW ⟨z.1.2, fun h ↦ z.2 (Subtype.ext h)⟩
  let j : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U.ι ≫ V.ι) hrange
  have hj : j ≫ W.ι = U.ι ≫ V.ι := IsOpenImmersion.lift_fac _ _ _
  have hjaf : (j ≫ a) ≫ f = U.ι ≫ (V.ι ≫ q) := by
    rw [Category.assoc, ha, ← Category.assoc, hj, Category.assoc]
  have hηU : genericPoint V.toScheme ∈ U := by
    intro h
    have hgen := genericPoint_eq_of_isOpenImmersion V.ι
    rw [h] at hgen
    change c = genericPoint C at hgen
    exact hcW (hgen ▸ hη)
  let A := V.toScheme.presheaf.stalk c'
  let i : Spec (.of (FractionRing A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  let k := i ≫ V.toScheme.fromSpecStalk c'
  have hk : Set.range k ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (fractionRing_fromSpecStalk_apply c' z) ▸ hηU
  let g := IsOpenImmersion.lift U.ι k hk
  have hg : g ≫ U.ι = i ≫ V.toScheme.fromSpecStalk c' :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨l, hl, hlZ⟩ := extension_closedPoint_mem f hY hext
    (V.ι ≫ p) inferInstance inferInstance inferInstance inferInstance
    c' hc' hdim' U rfl (V.ι ≫ q) (j ≫ a)
    (by simp only [Category.assoc, hq]) hjaf inferInstance g hg Z hZ
    (fun z ↦ haZ (j (g z)))
  refine ⟨l (IsLocalRing.closedPoint A), hlZ, ?_⟩
  have h := congrArg (fun k : Spec (.of A) ⟶ Y ↦ k (IsLocalRing.closedPoint A)) hl
  change f (l (IsLocalRing.closedPoint A)) =
    q (V.ι (V.toScheme.fromSpecStalk c' (IsLocalRing.closedPoint A))) at h
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact h

/-! ### Producing a one-dimensional test curve -/

/-- A morphism with discrete fibres is injective on specializations inside a fibre. -/
theorem eq_of_specializes_of_eq_of_locallyQuasiFinite
    {C Y : Scheme.{u}} (q : C ⟶ Y) [LocallyQuasiFinite q]
    {c d : C} (hcd : c ⤳ d) (hq : q c = q d) : c = d := by
  let F := q ⁻¹' {q d}
  have : DiscreteTopology F :=
    isDiscrete_iff_discreteTopology.mp (q.isDiscrete_preimage_singleton (q d))
  let c' : F := ⟨c, hq⟩
  let d' : F := ⟨d, rfl⟩
  have h : c' ⤳ d' := Topology.IsInducing.subtypeVal.specializes_iff.mp hcd
  exact congrArg Subtype.val (specializes_iff_eq.mp h)

/-- If a morphism with discrete fibres out of an integral scheme sends a point `c` to a point
covered by the image of the generic point, then the local ring at `c` has dimension one: the
covering relation and discreteness of the fibres force every point strictly above `c` to be the
generic point. -/
theorem ringKrullDim_stalk_eq_one_of_covBy
    {C Y : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Y) [LocallyQuasiFinite q] (c : C)
    (hcov : q c ⋖ q (genericPoint C)) :
    ringKrullDim (C.presheaf.stalk c) = 1 := by
  let : PartialOrder Y :=
    { (inferInstance : Preorder Y) with
      le_antisymm := fun a b hab hba ↦ (Specializes.antisymm hba hab).eq }
  have hmax : IsMax (genericPoint C) := fun z _ ↦ genericPoint_specializes z
  have hη : Order.coheight (genericPoint C) = 0 := Order.coheight_eq_zero.mpr hmax
  have hcz : c < genericPoint C := by
    refine ⟨genericPoint_specializes c, ?_⟩
    intro h
    exact hcov.lt.not_ge (h.map q.continuous)
  have hgen : ∀ z, c < z → z = genericPoint C := by
    intro z hcz
    have h₁ : q c ≤ q z := hcz.1.map q.continuous
    have h₂ : q z ≤ q (genericPoint C) := (genericPoint_specializes z).map q.continuous
    rcases hcov.eq_or_eq h₁ h₂ with h | h
    · have hzc : z = c := eq_of_specializes_of_eq_of_locallyQuasiFinite q hcz.1 h
      exact False.elim (hcz.ne hzc.symm)
    · exact eq_of_specializes_of_eq_of_locallyQuasiFinite q
        (genericPoint_specializes z) h.symm |>.symm
  have hle : Order.coheight c ≤ 1 := by
    apply Order.coheight_le_coe_iff.mpr
    intro z hz
    rw [hgen z hz, hη]
    norm_num
  have hge := Order.coheight_add_one_le hcz
  rw [hη, zero_add] at hge
  rw [ringKrullDim_stalk_eq_coheight, le_antisymm hle hge]
  rfl

/-- The version of `image_mem_of_partialMap` whose input is a morphism from the spectrum of the
function field, rather than a partial morphism: Mathlib's `Scheme.PartialMap.ofFromSpecStalk`
turns the former into the latter. -/
theorem image_mem_of_fromFunctionField
    {S X Y C : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hY : Y ⟶ S) (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (p : C ⟶ S) [LocallyOfFiniteType p]
    [IsNormal C] [IsIntegral C] [NoetherianSpace C]
    (c : C) (hc : IsClosed ({c} : Set C))
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1)
    (q : C ⟶ Y) (hq : q ≫ hY = p)
    (φ : Spec C.functionField ⟶ X)
    (hφ : φ ≫ f = C.fromSpecStalk (genericPoint C) ≫ q)
    (Z : Set X) (hZ : IsClosed Z) (hφZ : ∀ z, φ z ∈ Z) :
    q c ∈ f '' Z := by
  let r := Scheme.PartialMap.ofFromSpecStalk q f φ hφ
  have hη : genericPoint C ∈ r.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk ..
  have hr : r.fromSpecStalkOfMem hη = φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk ..
  have : Nonempty r.domain := ⟨⟨genericPoint C, hη⟩⟩
  let j := r.domain.fromSpecStalkOfMem (genericPoint C) hη
  let z := genericPoint (Spec C.functionField)
  have hj : j z = genericPoint r.domain.toScheme := by
    apply r.domain.ι.isOpenEmbedding.injective
    have h := congrArg (fun k : Spec C.functionField ⟶ C ↦ k z)
      (Scheme.Opens.fromSpecStalkOfMem_ι r.domain (genericPoint C) hη)
    change r.domain.ι (j z) = C.fromSpecStalk (genericPoint C) z at h
    rw [fromSpecStalk_genericPoint] at h
    exact h.trans (genericPoint_eq_of_isOpenImmersion r.domain.ι).symm
  have hηZ : r.hom (genericPoint r.domain.toScheme) ∈ Z := by
    rw [← hj]
    have h := congrArg (fun k : Spec C.functionField ⟶ X ↦ k z) hr
    change r.hom (j z) = φ z at h
    rw [h]
    exact hφZ z
  exact image_mem_of_partialMap f hY hext p c hc hdim q hq r.domain hη r.hom
    (Scheme.PartialMap.ofFromSpecStalk_comp ..) Z hZ
    (map_mem_closed_of_genericPoint_mem r.hom Z hZ hηZ)

/-- The test curve in the affine case: `Spec B` for a Noetherian normal domain `B` with
fraction field `K`, carrying a morphism with discrete fibres to `Y` under which a closed point
`c` goes to a point covered by the image of the generic point. -/
theorem image_mem_of_fractionRing
    {S X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hY : Y ⟶ S) (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (B K : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Field K] [Algebra B K] [IsFractionRing B K]
    (q : Spec (.of B) ⟶ Y) [LocallyQuasiFinite q]
    [LocallyOfFiniteType (q ≫ hY)]
    (c : Spec (.of B)) (hc : IsClosed ({c} : Set (Spec (.of B))))
    (hcov : q c ⋖ q (genericPoint (Spec (.of B))))
    (φ : Spec (.of K) ⟶ X)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B K)) ≫ q)
    (Z : Set X) (hZ : IsClosed Z) (hφZ : ∀ z, φ z ∈ Z) :
    q c ∈ f '' Z := by
  let C := Spec (.of B)
  have : IsNormal C := _root_.AlgebraicGeometry.isNormal_spec_of_isIntegrallyClosed B
  let : Algebra B C.functionField := instAlgebraCarrierFunctionFieldSpec (.of B)
  have : IsFractionRing B C.functionField := functionField_isFractionRing_of_affine (.of B)
  let e : K ≃ₐ[B] C.functionField :=
    IsLocalization.algEquiv (nonZeroDivisors B) K C.functionField
  let j := Spec.map (CommRingCat.ofHom e.toRingHom)
  have hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap B K)) =
      C.fromSpecStalk (genericPoint C) := by
    rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
    apply congrArg Spec.map
    ext b
    exact e.commutes b
  have hφ' : (j ≫ φ) ≫ f = C.fromSpecStalk (genericPoint C) ≫ q := by
    rw [Category.assoc, hφ, ← Category.assoc, hj]
  exact image_mem_of_fromFunctionField f hY hext (q ≫ hY) c hc
    (ringKrullDim_stalk_eq_one_of_covBy q c hcov) q rfl (j ≫ φ) hφ'
    Z hZ (fun z ↦ hφZ (j z))

/-- A Japanese domain has module-finite integral closure in any finite extension of any
field of fractions of it, not only in extensions of the chosen model `FractionRing`. -/
theorem finite_integralClosure_of_japanese
    {R K L : Type u} [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Module.Finite K L] (hR : IsJapaneseRing R) :
    Module.Finite R (integralClosure R L) := by
  let e : FractionRing R ≃ₐ[R] K := IsLocalization.algEquiv (nonZeroDivisors R) _ _
  let : Algebra (FractionRing R) K := e.toRingHom.toAlgebra
  let : Algebra (FractionRing R) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap R L a = algebraMap K L (e (algebraMap R (FractionRing R) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower (FractionRing R) K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite (FractionRing R) K :=
    Module.Finite.of_surjective (Algebra.linearMap (FractionRing R) K) e.surjective
  have : Module.Finite (FractionRing R) L := Module.Finite.trans K L
  exact hR.finite L

/-- The Nagata step: given a closed point `y` covered by a point `t` of the base, and a
morphism to `X` from a finite extension `K` of the residue field at `t` whose image lies in a
closed `Z`, the point `y` lies in `f '' Z`.  The integral closure `B` of `R / t` in `K` is
module-finite by the Nagata hypothesis, so `Spec B ⟶ Spec R` is finite and surjects onto the
closure of `t`; a closed point of `Spec B` over `y` gives the test curve. -/
theorem image_mem_of_finite_residue_extension
    {S X : Scheme.{u}} (R : CommRingCat.{u})
    (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    (hY : Spec R ⟶ S) [LocallyOfFiniteType hY]
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (hR : IsNagataRing R) (t y : Spec R) [t.asIdeal.IsPrime]
    (hy : IsClosed ({y} : Set (Spec R))) (hcov : y ⋖ t)
    (K : Type u) [Field K] [Algebra t.asIdeal.ResidueField K]
    [Module.Finite t.asIdeal.ResidueField K]
    (φ : Spec (.of K) ⟶ X)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap t.asIdeal.ResidueField K).comp (algebraMap R t.asIdeal.ResidueField))))
    (Z : Set X) (hZ : IsClosed Z) (hφZ : ∀ z, φ z ∈ Z) :
    y ∈ f '' Z := by
  let A := R ⧸ t.asIdeal
  let k := t.asIdeal.ResidueField
  let : Algebra A K := ((algebraMap k K).comp (algebraMap A k)).toAlgebra
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let B := integralClosure A K
  have : Module.Finite A B :=
    finite_integralClosure_of_japanese (K := k) (hR.isJapaneseRing_quotient t.asIdeal)
  have : IsNoetherianRing R := hR.isNoetherianRing
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension k
  have : IsFractionRing B K := integralClosure.isFractionRing_of_finite_extension k K
  let q₀ : R →+* B := (algebraMap A B).comp (Ideal.Quotient.mk t.asIdeal)
  let q : Spec (.of B) ⟶ Spec R := Spec.map (CommRingCat.ofHom q₀)
  have hqfin : q₀.Finite := (RingHom.finite_algebraMap.mpr inferInstance).comp
    (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective))
  have : IsFinite q := (IsFinite.SpecMap_iff _).mpr hqfin
  have hqη : q (genericPoint (Spec (.of B))) = t := by
    apply PrimeSpectrum.ext
    rw [genericPoint_eq_bot_of_affine]
    change RingHom.ker q₀ = t.asIdeal
    ext r
    change algebraMap A B (Ideal.Quotient.mk t.asIdeal r) = 0 ↔ r ∈ t.asIdeal
    have hinj : Function.Injective (algebraMap A B) := by
      intro a b hab
      apply IsFractionRing.injective A k
      apply (algebraMap k K).injective
      have h := congrArg (algebraMap B K) hab
      simpa only [← IsScalarTower.algebraMap_apply] using h
    rw [map_eq_zero_iff _ hinj]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hyt : t ⤳ y := hcov.le
  have hyq : y ∈ Set.range q := q.isClosedMap.isClosed_range.stableUnderSpecialization
    hyt ⟨_, hqη⟩
  obtain ⟨c, hcq, hc⟩ := (hy.preimage q.continuous).exists_closed_singleton hyq
  change q c = y at hcq
  have hgen : Spec.map (CommRingCat.ofHom (algebraMap B K)) ≫ q = φ ≫ f := by
    rw [hφ, ← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    change algebraMap B K (algebraMap A B (Ideal.Quotient.mk t.asIdeal r)) = _
    rw [← IsScalarTower.algebraMap_apply]
    change algebraMap k K (algebraMap A k (Ideal.Quotient.mk t.asIdeal r)) = _
    rw [Ideal.algebraMap_quotient_residueField_mk]
    rfl
  have h := image_mem_of_fractionRing f hY hext B K q c hc
    (by simpa only [hcq, hqη] using hcov) φ hgen.symm Z hZ hφZ
  simpa only [hcq] using h

/-- The covering step over a Nagata affine base: if `t` lies in `f '' Z` and `y` covers it,
then `y` lies in `f '' Z`.  A closed point of the fibre of `f` over `t` meeting the preimage of
`Z` gives a finite extension of the residue field at `t`, which the previous lemma handles. -/
theorem image_mem_of_covBy
    {S X : Scheme.{u}} (R : CommRingCat.{u})
    (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    (hY : Spec R ⟶ S) [LocallyOfFiniteType hY]
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY)
    (hR : IsNagataRing R) (t y : Spec R)
    (hy : IsClosed ({y} : Set (Spec R))) (hcov : y ⋖ t)
    (Z : Set X) (hZ : IsClosed Z) (ht : t ∈ f '' Z) :
    y ∈ f '' Z := by
  let F := f.fiber t
  let j := f.fiberι t
  let g := f.fiberToSpecResidueField t
  have : LocallyOfFiniteType g := by
    dsimp [g, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]; infer_instance
  have : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian g
  have hne : (j ⁻¹' Z).Nonempty := by
    obtain ⟨x, hx, hxt⟩ := ht
    have hxj : x ∈ Set.range j := by
      rw [Scheme.Hom.range_fiberι]
      exact hxt
    obtain ⟨z, hz⟩ := hxj
    exact ⟨z, by change j z ∈ Z; rw [hz]; exact hx⟩
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints_of_isClosed F hne
    (hZ.preimage j.continuous)
  let K := F.residueField z
  let v := F.fromSpecResidueField z
  have : IsClosedImmersion v := IsClosedImmersion.of_isPreimmersion v (by
    rw [Scheme.range_fromSpecResidueField]; exact hz)
  let α : (Spec R).residueField t ⟶ K := Spec.preimage (v ≫ g)
  have hα : LocallyOfFiniteType (Spec.map α) := by
    rw [Spec.map_preimage]; infer_instance
  have hαft : α.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hα
  have hαfin : α.hom.Finite := by
    let := α.hom.toAlgebra
    have : Algebra.FiniteType ((Spec R).residueField t) K := hαft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have : t.asIdeal.IsPrime := t.isPrime
  let β := (Scheme.Spec.residueFieldIso R t).inv ≫ α
  let : Algebra t.asIdeal.ResidueField K := β.hom.toAlgebra
  have : Module.Finite t.asIdeal.ResidueField K := hαfin.comp
    (RingHom.Finite.of_surjective _
      (Scheme.Spec.residueFieldIso R t).symm.commRingCatIsoToRingEquiv.surjective)
  refine image_mem_of_finite_residue_extension R f hY hext hR t y hy hcov K (v ≫ j) ?_ Z hZ ?_
  · change (v ≫ j) ≫ f = Spec.map (CommRingCat.ofHom
      (β.hom.comp (algebraMap R t.asIdeal.ResidueField)))
    change (v ≫ j) ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap R t.asIdeal.ResidueField) ≫ β)
    simp only [Spec.map_comp, β, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    rw [show Spec.map α = v ≫ g from Spec.map_preimage _]
    simpa only [Category.assoc, j, g] using congrArg (fun k ↦ v ≫ k) (f.fiber_fac t)
  · intro w
    change j (v w) ∈ Z
    rw [Scheme.fromSpecResidueField_apply]
    exact hzZ

/-- In the spectrum of a Noetherian ring, a point in the closure of a constructible set but not
in it is covered by a point of the set.  Constructible sets are closed in the constructible
topology of a spectral space, so some point of the set specializes to `y`; the punctured
spectrum of the local ring at `y` is Jacobson, so a closed point of it inside the preimage of
the set is immediately below `y`. -/
@[sga "3 XV 3.3" "special case"]
theorem exists_covBy_mem_of_mem_closure
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    {E : Set (Spec R)} (hE : Topology.IsConstructible E)
    (y : Spec R) (hy : y ∈ closure E) (hyE : y ∉ E) :
    ∃ t ∈ E, y ⋖ t := by
  have : SpectralSpace (Spec R) := inferInstanceAs (SpectralSpace (PrimeSpectrum R))
  have hEc : @IsClosed (Spec R) (constructibleTopology (Spec R)) E := by
    have ho : @IsOpen (Spec R) (constructibleTopology (Spec R)) Eᶜ := by
      rw [constructibleTopology_eq_generateFrom_isConstructible]
      exact TopologicalSpace.isOpen_generateFrom_of_mem hE.compl
    simpa only [compl_compl] using
      (@IsOpen.isClosed_compl (Spec R) (constructibleTopology (Spec R)) Eᶜ ho)
  obtain ⟨x, hxE, hxy⟩ :=
    mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology hEc hy
  let A := (Spec R).presheaf.stalk y
  let m := IsLocalRing.closedPoint A
  let jj := (Spec R).fromSpecStalk y
  let U : (Spec (.of A)).Opens :=
    ⟨{m}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩
  have hUjac : JacobsonSpace U := PrimeSpectrum.jacobsonSpace_compl_closedPoint A
  have hpre : Topology.IsConstructible (jj ⁻¹' E) := hE.preimage jj.continuous
    (fun s hs _ ↦ (NoetherianSpace.isCompact _).isRetrocompact (hs.preimage jj.continuous))
  have hEU : Topology.IsConstructible (U.ι ⁻¹' (jj ⁻¹' E)) :=
    hpre.preimage_of_isOpenEmbedding U.ι.isOpenEmbedding
  have hxj : x ∈ Set.range jj := by rw [Scheme.range_fromSpecStalk]; exact hxy
  obtain ⟨x', hx'⟩ := hxj
  have hxU : x' ∈ U := by
    intro h
    have : x = y := by rw [← hx', h]; exact Scheme.fromSpecStalk_closedPoint
    exact hyE (this ▸ hxE)
  have hne : (U.ι ⁻¹' (jj ⁻¹' E)).Nonempty :=
    ⟨⟨x', hxU⟩, by change jj x' ∈ E; rw [hx']; exact hxE⟩
  obtain ⟨t, htE, htc⟩ := exists_closedPoint_mem_of_isConstructible hEU hne
  have hjm : jj m = y := Scheme.fromSpecStalk_closedPoint
  have hty : jj t.1 ⤳ y :=
    ((IsLocalRing.specializes_closedPoint t.1).map jj.continuous).trans (specializes_of_eq hjm)
  have hne' : jj t.1 ≠ y := by
    intro h
    exact hyE (h ▸ htE)
  refine ⟨jj t.1, htE, ⟨⟨hty, ?_⟩, ?_⟩⟩
  · intro h
    exact hne' (hty.antisymm h).eq
  · intro z hyz hzt
    have hzj : z ∈ Set.range jj := by rw [Scheme.range_fromSpecStalk]; exact hyz.le
    obtain ⟨z', hz'⟩ := hzj
    have hzU : z' ∈ U := by
      intro h
      have hzy : z = y := by rw [← hz', h]; exact hjm
      exact hyz.ne hzy.symm
    have htz : t ⤳ (⟨z', hzU⟩ : U) :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp
        (jj.isEmbedding.isInducing.specializes_iff.mp (hz'.symm ▸ hzt.le))
    have hzeq : (⟨z', hzU⟩ : U) = t := htc.stableUnderSpecialization htz rfl
    have : z = jj t.1 := by rw [← hz', ← congrArg Subtype.val hzeq]
    exact hzt.ne this

/-- The image of a closed set under a morphism is the image of its preimage along a base
change, computed on points. -/
theorem preimage_image_pullback
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (Z : Set X) :
    g ⁻¹' (f '' Z) =
      Limits.pullback.snd f g '' (Limits.pullback.fst f g ⁻¹' Z) := by
  ext t
  constructor
  · rintro ⟨x, hx, hxt⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x t hxt
    exact ⟨z, by change Limits.pullback.fst f g z ∈ Z; rw [hz₁]; exact hx, hz₂⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Limits.pullback.fst f g z, hz, ?_⟩
    exact congrArg (fun k : Limits.pullback f g ⟶ Y ↦ k z)
      (Limits.pullback.condition (f := f) (g := g))

/-! ### Closedness -/

/-- Closed sets of a Noetherian space are constructible. -/
private theorem isConstructible_of_isClosed {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    {s : Set X} (hs : IsClosed s) : Topology.IsConstructible s := by
  simpa only [compl_compl] using
    ((NoetherianSpace.isCompact sᶜ).isConstructible hs.isOpen_compl).compl

/-- The extension test forces `f` to be closed when the target has Noetherian and
quasi-separated underlying space.  If the image of a closed `Z` were not closed, the nonempty
constructible set `closure (f '' Z) \ f '' Z` would meet an open subspace in a point closed
there; passing to a Nagata affine open around it, the covering step contradicts that. -/
theorem isClosedMap_of_extension_of_noetherianSpace
    {S X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : Y ⟶ S) [LocallyOfFiniteType hY] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [QuasiSeparatedSpace Y]
    (hNag : IsNagataScheme Y)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY) : IsClosedMap f := by
  intro Z hZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  let E := f '' Z
  have hE : Topology.IsConstructible E := f.isConstructible_image (isConstructible_of_isClosed hZ)
  by_contra hclosed
  have hne : (closure E \ E).Nonempty := by
    by_contra hn
    exact hclosed (isClosed_of_closure_subset
      (Set.sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hn)))
  have hBc : Topology.IsConstructible (closure E \ E) :=
    (isConstructible_of_isClosed isClosed_closure).sdiff hE
  obtain ⟨U₀, x, hx, hxc⟩ := exists_open_closedPoint_mem hBc hne
  let U : Y.Opens := U₀
  let x' : U.toScheme := x
  change IsClosed ({x'} : Set U.toScheme) at hxc
  have hNU : IsNagataScheme U.toScheme := isNagataScheme_of_locallyOfFiniteType U.ι hNag
  obtain ⟨W, hxW, hW⟩ := hNU x'
  let R := Γ(U.toScheme, W.1)
  let a : Spec R ⟶ U.toScheme := W.2.fromSpec
  let g : Spec R ⟶ Y := a ≫ U.ι
  have : IsOpenImmersion a := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion g := by dsimp [g]; infer_instance
  have hxrange : x' ∈ Set.range a := W.2.range_fromSpec.symm ▸ hxW
  obtain ⟨y, hy⟩ := hxrange
  have hyg : g y = x.1 := congrArg U.ι hy
  have hyclosed : IsClosed ({y} : Set (Spec R)) :=
    isClosed_singleton_of_injective a.continuous a.isOpenEmbedding.injective (hy ▸ hxc)
  have : IsNoetherianRing R := hW.isNoetherianRing
  have hyE : y ∉ g ⁻¹' E := by
    change g y ∉ E
    rw [hyg]
    exact hx.2
  have hycl : y ∈ closure (g ⁻¹' E) :=
    g.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage
      (by change g y ∈ closure E; rw [hyg]; exact hx.1)
  have hEg : Topology.IsConstructible (g ⁻¹' E) :=
    hE.preimage_of_isOpenEmbedding g.isOpenEmbedding
  obtain ⟨t, ht, hcov⟩ := exists_covBy_mem_of_mem_closure R hEg y hycl hyE
  let f' := Limits.pullback.snd f g
  let j := Limits.pullback.fst f g
  have hext' : HasEssentiallyFiniteTypeValuativeExtension f' (g ≫ hY) :=
    extension_of_isPullback hY f hext f' j g (IsPullback.of_hasPullback f g).flip
  have hEq : g ⁻¹' E = f' '' (j ⁻¹' Z) := preimage_image_pullback f g Z
  have hh := image_mem_of_covBy R f' (g ≫ hY) hext' hW t y hyclosed hcov
    (j ⁻¹' Z) (hZ.preimage j.continuous) (hEq ▸ ht)
  exact hyE (hEq.symm ▸ hh)

/-- The extension test forces `f` to be closed.  Closedness is local on the target, so the
previous lemma applies after restricting to the affine opens of `Y`, which are Noetherian and
quasi-separated and remain Nagata. -/
theorem isClosedMap_of_extension
    {S X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : Y ⟶ S) [LocallyOfFiniteType hY] [IsLocallyNoetherian Y]
    (hNag : IsNagataScheme Y)
    (hext : HasEssentiallyFiniteTypeValuativeExtension f hY) : IsClosedMap f := by
  have hcover : IsOpenCover (fun U : Y.affineOpens ↦ U.1) := by
    apply IsOpenCover.of_sets (fun U ↦ U.1.isOpen)
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨⟨U, hU⟩, hyU⟩
  apply hcover.isClosedMap_iff_restrictPreimage.mpr
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherian U.1.toScheme := ⟨⟩
  have h := isClosedMap_of_extension_of_noetherianSpace (f ∣_ U.1) (U.1.ι ≫ hY)
    (isNagataScheme_of_locallyOfFiniteType U.1.ι hNag)
    (extension_of_isPullback hY f hext (f ∣_ U.1) (f ⁻¹ᵁ U.1).ι U.1.ι
      (isPullback_morphismRestrict f U.1))
  change IsClosedMap (f ∣_ U.1).base at h
  rwa [morphismRestrict_base] at h

/-- The named implication of the reduction module is true: over a Nagata base, the
essentially-finite-type extension test forces every finite-dimensional affine-space base change
of `f` to be closed.  This is the content of Stacks 0GWV. -/
theorem extensionImpliesClosedAffineSpaceBaseChange :
    ExtensionImpliesClosedAffineSpaceBaseChange.{u} := by
  intro S X Y hX hY f hf hS hfX hfY hfc hext n
  have := hfX
  have := hfY
  have := hfc
  have : IsLocallyNoetherian S := isLocallyNoetherian_of_isNagataScheme hS
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp_eq hY f hf
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian hY
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin n)) f) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (AffineSpace.isPullback_map f).flip inferInstance
  have : QuasiCompact (AffineSpace.map (ULift.{u} (Fin n)) f) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (AffineSpace.isPullback_map f).flip inferInstance
  let hY' := (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) ≫ hY
  have : LocallyOfFiniteType hY' := by dsimp [hY']; infer_instance
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin n)) Y) :=
    LocallyOfFiniteType.isLocallyNoetherian hY'
  exact isClosedMap_of_extension (AffineSpace.map (ULift.{u} (Fin n)) f) hY'
    (isNagataScheme_of_locallyOfFiniteType hY' hS)
    (extension_of_affineSpace hY f hext n)

/-- **Stacks Project, Tag 0GWV**, with only the converse implication of Stacks 05JX left as a
hypothesis.  Universal closedness, closedness of all finite-dimensional affine-space base
changes, and the normal finite-type one-dimensional extension test are equivalent, given `h₂₁`,
which is Stacks 05JX (3) implies (1).

No Stacks tag is attached, and none is attachable: the source states the equivalence as a
single assertion, so its covering set is that one assertion, and `h₂₁` is a hypothesis the
source does not have. -/
theorem universallyClosed_tfae_essentiallyFiniteType_of_closedAffineSpaceBaseChange
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] [QuasiCompact f]
    (h₂₁ : ClosedAffineSpaceBaseChangeImpliesUniversallyClosed.{u}) :
    List.TFAE
      [UniversallyClosed f,
       ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f),
       HasEssentiallyFiniteTypeValuativeExtension f hY] :=
  universallyClosed_tfae_essentiallyFiniteType_of_converses hX hY f hf hS h₂₁
    extensionImpliesClosedAffineSpaceBaseChange

end Stacks.AlgebraicGeometry.NagataExtensionClosed
