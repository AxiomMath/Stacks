module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BirationalGenus
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.NoEmbeddedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Alteration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.FiniteNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Resolution of a one-dimensional integral Noetherian scheme

For a one-dimensional integral Noetherian scheme `Y` the following are equivalent: `Y` admits an
alteration by a regular scheme; `Y` admits a resolution of singularities; `Y` becomes regular
after a finite sequence of blowups at closed points; and the normalization `Y^ν → Y` is finite.

## Main results

* `AlgebraicGeometry.resolveCurve_tfae` is the four-term equivalence, [Stacks, Tag 0BI4].
* `AlgebraicGeometry.exists_pointBlowupChain_isRegular_of_isResolution` is its substantial
  implication: a resolution of a one-dimensional integral Noetherian scheme is dominated by a
  finite chain of blowups at closed points which is itself regular.

## Implementation notes

The finite sequence of blowups is `Stacks.ResolutionOfSurfaces.PointBlowupChain` with every
point of `Y` allowed as a centre; the normalization is `AlgebraicGeometry.Scheme.normalization`,
whose hypothesis — that quasi-compact opens have finitely many irreducible components — holds on
a Noetherian scheme and is a proposition, so the morphism it names is unambiguous.

Three places depart from the source's argument.

The implication (1) ⇒ (4) is [Stacks, Tag 0BGG], whose proof needs the coherence of the
pushforward along a proper morphism, [Stacks, Tag 02O6]. The library's form of Tag 0BGG,
`AlgebraicGeometry.normalization_isFinite_of_regular_alteration`, is unconditional and applies
here as it stands. In dimension one that input is not needed at all, because [Stacks, Tag 0AB7]
already makes a proper generically quasi-finite morphism *finite*, and for a finite morphism the
step is immediate; what is used below is therefore the special case
`AlgebraicGeometry.normalization_isFinite_of_isFinite_regular_alteration`, whose proof keeps
this file off the coherence development.

The source's proof that (1), (2) and (4) imply (3) builds the chain `Y_i` by recursion and stops
it with the ascending chain condition of [Stacks, Tag 01Y8]. Here the recursion is replaced by
one maximality statement: among all factorizations of the resolution through a point blowup
chain, choose one whose images `Γ(Y_i, ·) → Γ(X, ·)` on a fixed finite affine cover of `Y` are
maximal. Such a factorization exists because the module of sections of `X` over the preimage of
an affine open is finite over a Noetherian ring, hence Noetherian, and the cover is finite. At a
maximal factorization every closed point is an effective Cartier divisor, since otherwise
blowing it up would enlarge the image; and that makes the factorization regular.

Finally, the stabilizing step uses that a *regular* one-dimensional integral Noetherian scheme
maps to the blowup of any ideal with proper support, by the universal property
[Stacks, Tag 0806]: on such a scheme every ideal sheaf with proper support is an effective
Cartier divisor, by [Stacks, Tag 0BXH].

## References

* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0BXH](https://stacks.math.columbia.edu/tag/0BXH)
-/

@[expose] public noncomputable section

open CategoryTheory Order Stacks.ResolutionOfSurfaces TopologicalSpace Stacks.Topology.Dimension

universe u

namespace AlgebraicGeometry

/-- The generic point of an integral scheme of dimension one is not closed. -/
private theorem not_isClosed_genericPoint_of_topologicalKrullDim_eq_one {Y : Scheme.{u}}
    [IsIntegral Y] (hYdim : topologicalKrullDim Y = 1) :
    ¬ IsClosed ({genericPoint Y} : Set Y) := by
  intro hclosed
  have hsingle : ({genericPoint Y} : Set Y) = Set.univ := by
    rw [← genericPoint_closure (α := Y), hclosed.closure_eq]
  have : Subsingleton Y := ⟨fun x y =>
    ((Set.mem_singleton_iff.mp (hsingle ▸ Set.mem_univ x)).trans
      (Set.mem_singleton_iff.mp (hsingle ▸ Set.mem_univ y)).symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (X := Y)
  rw [hYdim] at h0
  norm_num at h0

/-! ### Chains of blowups at closed points -/


/-- An isomorphism of integral schemes is birational. -/
theorem isBirational_of_isIso {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsIso f] : IsBirational f := by
  have : IsIso (f.stalkMap (genericPoint A)) :=
    ((isIso_iff_isIso_stalkMap f).mp inferInstance).2 _
  exact isBirational_of_isIso_stalkMap_genericPoint f

/-- The reduced closed point is a nonzero ideal sheaf, as soon as the ambient scheme carries a
proper birational morphism to an integral scheme of dimension one: otherwise the point would be
the generic point, whose image would then be a closed generic point downstairs. -/
private theorem vanishingIdeal_singleton_ne_bot {Y W : Scheme.{u}} [IsIntegral Y] [IsIntegral W]
    (hYdim : topologicalKrullDim Y = 1) (h : W ⟶ Y) [IsProper h] (hb : IsBirational h)
    (w : W) (hw : IsClosed ({w} : Set W)) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) ≠ ⊥ := by
  intro hbot
  have huniv : (Set.univ : Set W) = {w} := by
    rw [← supportSet_vanishingIdeal_singleton hw, hbot]
    rfl
  have hwη : w = genericPoint W := by
    have : genericPoint W ∈ ({w} : Set W) := huniv ▸ Set.mem_univ _
    exact (Set.mem_singleton_iff.mp this).symm
  have hmap : h (genericPoint W) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral h).out 1 2).mp hb.isDominant
  refine not_isClosed_genericPoint_of_topologicalKrullDim_eq_one hYdim ?_
  have himg : IsClosed (h '' ({w} : Set W)) := h.isClosedMap _ hw
  rwa [Set.image_singleton, hwη, hmap] at himg

/-- **A chain of blowups at closed points over a one-dimensional integral Noetherian scheme is a
modification**: its source is Noetherian and integral and the composite morphism is proper and
birational. -/
theorem pointBlowupChain_properties {Y W : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    (hYdim : topologicalKrullDim Y = 1) {h : W ⟶ Y}
    (hc : PointBlowupChain Y Set.univ W h) :
    IsNoetherian W ∧ IsIntegral W ∧ IsProper h ∧ IsBirational h := by
  induction hc with
  | refl =>
      exact ⟨inferInstance, inferInstance, inferInstance, isBirational_of_isIso (𝟙 Y)⟩
  | @step W h hh w hw _ ih =>
      obtain ⟨hWn, hWi, hWp, hWb⟩ := ih
      have : IsNoetherian W := hWn
      have : IsIntegral W := hWi
      have : IsProper h := hWp
      have hJ : Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) ≠ ⊥ :=
        vanishingIdeal_singleton_ne_bot hYdim h hWb w hw
      have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) :=
        isIntegral_blowUp _ hJ
      have hbb : IsBirational
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) :=
        isBirational_blowUpToBase _ hJ
      exact ⟨isNoetherian_of_isProper_over_noetherian
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))),
        inferInstance, inferInstance, hbb.comp hWb⟩

/-! ### Effective Cartier divisors on a regular curve -/

/-- **On a regular one-dimensional integral Noetherian scheme every ideal sheaf with proper
support is an effective Cartier divisor.** The support is then a finite set of closed points, so
the closed subscheme it cuts out has no embedded points and each of its components has
codimension one. -/
theorem isEffectiveCartierDivisor_of_isRegular_of_support_ne_univ {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) (hreg : IsRegular X)
    (I : X.IdealSheafData) (hproper : (I.support : Set X) ≠ Set.univ) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  have hclosed : ∀ x : I.subscheme, IsClosed ({I.subschemeι x} : Set X) := fun x =>
    isClosed_singleton_of_mem_of_ne_univ hdim I.support.isClosed hproper x.property
  refine isEffectiveCartierDivisor_of_codimension_one I ?_ ?_ (Or.inr hreg)
  · intro x hx
    obtain ⟨-, y, -, hyx, hne⟩ := hx
    have hspec : I.subschemeι y ⤳ I.subschemeι x := hyx.map I.subschemeι.continuous
    rw [specializes_iff_mem_closure, (hclosed y).closure_eq, Set.mem_singleton_iff] at hspec
    exact hne (I.subschemeι.isClosedEmbedding.injective hspec).symm
  · intro Z hZ x hx
    let a := IrreducibleCloseds.closureSingleton (I.subschemeι x)
    let b : IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hab : a < b := by
      refine lt_of_le_of_ne (show a ≤ b from Set.subset_univ _) fun heq => ?_
      have h : closure ({I.subschemeι x} : Set X) = Set.univ := congrArg SetLike.coe heq
      exact hproper (Set.eq_univ_of_univ_subset (h ▸
        closure_minimal (Set.singleton_subset_iff.mpr x.property) I.support.isClosed))
    have hup : (codimension a : WithBot ℕ∞) ≤ 1 := (coheight_le_krullDim a).trans hdim
    have hlo : (1 : ℕ∞) ≤ codimension a := by
      let p : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ a).snoc b hab
      have hhead : p.head = a := rfl
      have hlen : p.length = 1 := rfl
      have h := Order.length_le_coheight_head (p := p)
      rw [codimension_eq_coheight]
      simpa only [hlen, Nat.cast_one, hhead] using h
    exact le_antisymm (by exact_mod_cast hup) hlo

/-- The inverse image of an ideal with proper support along a dominant morphism again has
proper support. -/
private theorem comap_support_ne_univ {X Z : Scheme.{u}} (I : X.IdealSheafData) (f : Z ⟶ X)
    [IsDominant f] (hproper : (I.support : Set X) ≠ Set.univ) :
    ((I.comap f).support : Set Z) ≠ Set.univ := by
  intro htop
  refine hproper (Set.eq_univ_of_univ_subset ?_)
  have hrange : Set.range (f : Z → X) ⊆ (I.support : Set X) := by
    rintro x ⟨z, rfl⟩
    have hz : z ∈ ((I.comap f).support : Set Z) := htop ▸ Set.mem_univ z
    rwa [Scheme.IdealSheafData.support_comap] at hz
  calc
    (Set.univ : Set X) = closure (Set.range (f : Z → X)) := f.denseRange.closure_eq.symm
    _ ⊆ (I.support : Set X) := closure_minimal hrange I.support.isClosed

/-- **A dominant morphism from a regular one-dimensional integral Noetherian scheme factors
through the blowup of any ideal with proper support**, by the universal property of blowing up,
[Stacks, Tag 0806]. -/
theorem exists_lift_blowUpToBase_of_isRegular {X Z : Scheme.{u}} [IsNoetherian Z] [IsIntegral Z]
    (hdim : topologicalKrullDim Z ≤ 1) (hreg : IsRegular Z) (I : X.IdealSheafData) (f : Z ⟶ X)
    [IsDominant f] (hproper : (I.support : Set X) ≠ Set.univ) :
    ∃ g : Z ⟶ blowUp I, g ≫ blowUpToBase I = f := by
  obtain ⟨_, ⟨hterminal⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  have hI' : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) :=
    isEffectiveCartierDivisor_of_isRegular_of_support_ne_univ hdim hreg (I.comap f)
      (comap_support_ne_univ I f hproper)
  let Z' : Stacks.Blowup.CartierOver I := ⟨Over.mk f, hI'⟩
  exact ⟨(CategoryTheory.Limits.IsTerminal.from hterminal Z').hom.left,
    (CategoryTheory.Limits.IsTerminal.from hterminal Z').hom.w⟩

/-! ### A regularity criterion -/

/-- **A one-dimensional integral Noetherian scheme all of whose closed points are effective
Cartier divisors is regular.** At a closed point the maximal ideal is then principal, so the
local ring is a field or a discrete valuation ring; either way it is a normal domain, and a
normal scheme of dimension at most one is regular by [Stacks, Tag 0BX2]. -/
theorem isRegular_of_forall_isEffectiveCartierDivisor_vanishingIdeal {Y : Scheme.{u}}
    [IsIntegral Y] [IsNoetherian Y] (hdim : topologicalKrullDim Y ≤ 1)
    (hpoints : ∀ (y : Y) (hy : IsClosed ({y} : Set Y)),
      Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) :
    IsRegular Y := by
  have hn : IsNormal Y := by
    refine (isNormal_iff_stalk_normal Y).mpr fun y => ⟨inferInstance, ?_⟩
    by_cases hy : y = genericPoint Y
    · subst hy
      exact inferInstanceAs (IsIntegrallyClosed Y.functionField)
    · have hproper : closure ({y} : Set Y) ≠ Set.univ := fun he =>
        hy ((show IsGenericPoint y Set.univ from he).eq (genericPoint_spec Y))
      have hclosed : IsClosed ({y} : Set Y) :=
        isClosed_singleton_of_mem_of_ne_univ hdim isClosed_closure hproper
          (subset_closure (Set.mem_singleton y))
      have hp := isPrincipal_maximalIdeal_stalk_of_isEffectiveCartierDivisor hclosed
        (hpoints y hclosed)
      by_cases hf : IsField (Y.presheaf.stalk y)
      · let : Field (Y.presheaf.stalk y) := hf.toField
        exact inferInstanceAs (IsIntegrallyClosed (Y.presheaf.stalk y))
      · let : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
          ((IsDiscreteValuationRing.TFAE (Y.presheaf.stalk y) hf).out 1 5).mpr hp
        exact inferInstanceAs (IsIntegrallyClosed (Y.presheaf.stalk y))
  exact isRegular_of_isNormal_of_topologicalKrullDim_le_one Y hdim

/-! ### Images of sections -/

section Sections

variable {S : Scheme.{u}}

/-- The map on sections over the preimage of an open of the base induced by a morphism over the
base. -/
private def sectionMap (U : S.Opens) {A B : Over S} (g : A ⟶ B) :
    Γ(B.left, B.hom ⁻¹ᵁ U) ⟶ Γ(A.left, A.hom ⁻¹ᵁ U) :=
  g.left.appLE _ _ (by rw [← Scheme.Hom.comp_preimage, Over.w g])

private lemma sectionMap_comm (U : S.Opens) {A B : Over S} (g : A ⟶ B) :
    B.hom.app U ≫ sectionMap U g = A.hom.app U := by
  have h : (g.left ≫ B.hom).appLE U (A.hom ⁻¹ᵁ U)
      (by rw [Over.w g]) = A.hom.app U := by
    simp only [Over.w g, Scheme.Hom.appLE_eq_app]
  rw [← h]
  exact (Scheme.Hom.comp_appLE g.left B.hom U (A.hom ⁻¹ᵁ U) _).symm

private lemma sectionMap_comp (U : S.Opens) {A B C : Over S} (g : A ⟶ B) (h : B ⟶ C) :
    sectionMap U (g ≫ h) = sectionMap U h ≫ sectionMap U g := by
  dsimp only [sectionMap]
  rw [Scheme.Hom.appLE_comp_appLE]
  congr 1

/-- The map on sections as a map of modules over the sections of the base. -/
private def sectionLinearMap (U : S.Opens) {A B : Over S} (g : A ⟶ B) :
    letI := (A.hom.app U).hom.toAlgebra
    letI := (B.hom.app U).hom.toAlgebra
    Γ(B.left, B.hom ⁻¹ᵁ U) →ₗ[Γ(S, U)] Γ(A.left, A.hom ⁻¹ᵁ U) := by
  letI := (A.hom.app U).hom.toAlgebra
  letI := (B.hom.app U).hom.toAlgebra
  exact (show Γ(B.left, B.hom ⁻¹ᵁ U) →ₐ[Γ(S, U)] Γ(A.left, A.hom ⁻¹ᵁ U) from
    { (sectionMap U g).hom with
      commutes' := fun r => ConcreteCategory.congr_hom (sectionMap_comm U g) r }).toLinearMap

/-- A property of the map on sections is equivalent to the same property of the map `app` of
the underlying morphism. -/
private lemma sectionMap_iff_app (U : S.Opens) {A B : Over S} (g : A ⟶ B)
    (P : ∀ {R T : CommRingCat.{u}} (_ : R ⟶ T), Prop) :
    P (sectionMap U g) ↔ P (g.left.app (B.hom ⁻¹ᵁ U)) := by
  have he : A.hom ⁻¹ᵁ U = g.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w g]
  dsimp only [sectionMap]
  rw [g.left.appLE_congr _ rfl he P]
  simp only [Scheme.Hom.appLE_eq_app]

private lemma sectionMap_injective (U : S.Opens) {A B : Over S} (g : A ⟶ B) [IsReduced B.left]
    [IsDominant g.left] [QuasiCompact g.left] : Function.Injective (sectionMap U g) := by
  have := IsSchemeTheoreticallyDominant.of_isDominant g.left
  exact (sectionMap_iff_app U g fun f => Function.Injective f).mpr
    (g.left.app_injective (B.hom ⁻¹ᵁ U))

/-- The image of the sections of `B` inside the sections of `A`, over the preimage of an open of
the base. -/
private def sectionImage (U : S.Opens) {A B : Over S} (g : A ⟶ B) :
    letI := (A.hom.app U).hom.toAlgebra
    Submodule Γ(S, U) Γ(A.left, A.hom ⁻¹ᵁ U) := by
  letI := (A.hom.app U).hom.toAlgebra
  letI := (B.hom.app U).hom.toAlgebra
  exact (sectionLinearMap U g).range

private lemma sectionImage_comp_le (U : S.Opens) {A B C : Over S} (g : A ⟶ B) (h : B ⟶ C) :
    sectionImage U (g ≫ h) ≤ sectionImage U g := by
  rintro x ⟨y, rfl⟩
  exact ⟨sectionMap U h y, (ConcreteCategory.congr_hom (sectionMap_comp U g h) y).symm⟩

private lemma sectionMap_surjective_of_sectionImage_eq (U : S.Opens) {A B C : Over S}
    (g : A ⟶ B) (h : B ⟶ C) (hinj : Function.Injective (sectionMap U g))
    (heq : sectionImage U (g ≫ h) = sectionImage U g) :
    Function.Surjective (sectionMap U h) := by
  intro x
  have hx : sectionMap U g x ∈ sectionImage U (g ≫ h) := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, hinj ?_⟩
  change (sectionMap U (g ≫ h)) y = sectionMap U g x at hy
  rwa [sectionMap_comp] at hy

private lemma isIso_of_sectionMap_bijective {ι : Type*} (U : ι → S.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤) {A B : Over S} (g : A ⟶ B)
    [IsAffineHom B.hom] [IsAffineHom g.left]
    (hg : ∀ i, Function.Bijective (sectionMap (U i) g)) : IsIso g.left := by
  have hcover' : (⨆ i, B.hom ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  rw [← MorphismProperty.isomorphisms.iff]
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i => B.hom ⁻¹ᵁ U i) hcover').mpr fun i => ?_
  rw [MorphismProperty.isomorphisms.iff,
    isIso_morphismRestrict_iff_isIso_app _ ((hU i).preimage B.hom)]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((sectionMap_iff_app (U i) g fun f => Function.Bijective f).mp (hg i))

/-- Among a nonempty family of morphisms out of a fixed finite scheme over a locally Noetherian
base there is one whose images of sections, on a fixed finite family of affine opens, cannot be
properly enlarged. -/
private lemma exists_maximal_sectionImage {X : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsFinite f] {ι : Type*} [Finite ι] (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i))
    {α : Type*} [Nonempty α] (B : α → Over S) (g : ∀ a, Over.mk f ⟶ B a) :
    ∃ a, ∀ b, (∀ i, sectionImage (U i) (g a) ≤ sectionImage (U i) (g b)) →
      ∀ i, sectionImage (U i) (g a) = sectionImage (U i) (g b) := by
  classical
  let R (i : ι) := Γ(S, U i)
  let M (i : ι) := Γ(X, f ⁻¹ᵁ U i)
  let algebraInst (i : ι) : Algebra (R i) (M i) := (f.app (U i)).hom.toAlgebra
  have noetherianInst (i : ι) : IsNoetherianRing (R i) :=
    IsLocallyNoetherian.component_noetherian ⟨U i, hU i⟩
  have finiteInst (i : ι) : Module.Finite (R i) (M i) := f.finite_app (U i) (hU i)
  let v : α → ∀ i, (Submodule (R i) (M i))ᵒᵈ :=
    fun a i => OrderDual.toDual (sectionImage (U i) (g a))
  obtain ⟨-, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := ∀ i, (Submodule (R i) (M i))ᵒᵈ)).has_min
    (Set.range v) ⟨v (Classical.arbitrary α), Classical.arbitrary α, rfl⟩
  refine ⟨a, fun b hab i => ?_⟩
  have hle : v b ≤ v a := fun i => hab i
  have heq : v b = v a := eq_of_le_of_not_lt hle (hmin (v b) ⟨b, rfl⟩)
  exact (congrFun heq i).symm

end Sections

/-! ### A resolution is dominated by a chain of point blowups -/

/-- A factorization of a morphism through a chain of blowups at closed points. -/
private structure ResolutionFactorization {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The intermediate scheme, as an object over `Y`. -/
  obj : Over Y
  /-- The chain of blowups at closed points producing it. -/
  chain : PointBlowupChain Y Set.univ obj.left obj.hom
  /-- The factorization of `f` through it. -/
  lift : Over.mk f ⟶ obj
  /-- The factorization is birational. -/
  birational : IsBirational lift.left

private lemma resolutionFactorization_properties {X Y : Scheme.{u}} [IsIntegral Y]
    [IsNoetherian Y] (hYdim : topologicalKrullDim Y = 1) {f : X ⟶ Y} [IsFinite f]
    (a : ResolutionFactorization f) :
    IsNoetherian a.obj.left ∧ IsIntegral a.obj.left ∧ IsFinite a.obj.hom ∧
      IsFinite a.lift.left := by
  obtain ⟨hN, hI, hP, hB⟩ := pointBlowupChain_properties hYdim a.chain
  have := hI
  have := hP
  have : IsFinite a.obj.hom :=
    isFinite_of_isProper_of_isBirational a.obj.hom hB (le_of_eq hYdim)
  have hcomp : IsFinite (a.lift.left ≫ a.obj.hom) := by
    rw [Over.w a.lift]
    exact inferInstanceAs (IsFinite f)
  exact ⟨hN, hI, inferInstance, IsFinite.of_comp a.lift.left a.obj.hom⟩

/-- **A resolution of a one-dimensional integral Noetherian scheme is dominated by a regular
chain of blowups at closed points.** This is the substantial implication of [Stacks, Tag 0BI4],
(2) ⇒ (3). -/
theorem exists_pointBlowupChain_isRegular_of_isResolution {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hf : IsBirational f) (hYdim : topologicalKrullDim Y = 1) (hreg : IsRegular X) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Y), PointBlowupChain Y Set.univ W g ∧ IsRegular W := by
  classical
  have hXsrc : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral X)
  have : Nonempty (ResolutionFactorization f) :=
    ⟨{ obj := Over.mk (𝟙 Y)
       chain := .refl
       lift := Over.homMk f (by simp)
       birational := hf }⟩
  let 𝒰 := Y.affineCover.finiteSubcover
  let U (i : 𝒰.I₀) : Y.Opens := (𝒰.f i).opensRange
  have hU (i : 𝒰.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (𝒰.X i) := by
      dsimp only [𝒰, Scheme.OpenCover.finiteSubcover]
      infer_instance
    exact isAffineOpen_opensRange (𝒰.f i)
  have hcover : iSup U = ⊤ := 𝒰.iSup_opensRange
  obtain ⟨a, ha⟩ := exists_maximal_sectionImage f U hU
    (fun a : ResolutionFactorization f => a.obj) (fun a => a.lift)
  obtain ⟨hN, hI, hF, hL⟩ := resolutionFactorization_properties hYdim a
  have := hN
  have := hI
  have := hF
  have := hL
  have hdimW : topologicalKrullDim a.obj.left ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom a.obj.hom).trans (le_of_eq hYdim)
  refine ⟨a.obj.left, a.obj.hom, a.chain, ?_⟩
  refine isRegular_of_forall_isEffectiveCartierDivisor_vanishingIdeal hdimW fun y hy => ?_
  set J : a.obj.left.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds a.obj.left) with hJdef
  have hJ : J ≠ ⊥ := vanishingIdeal_singleton_ne_bot hYdim a.obj.hom
    (pointBlowupChain_properties hYdim a.chain).2.2.2 y hy
  have : IsIntegral (blowUp J) := isIntegral_blowUp J hJ
  have hbb : IsBirational (blowUpToBase J) := isBirational_blowUpToBase J hJ
  have hdomLift : IsDominant a.lift.left := a.birational.isDominant
  have hXdim : topologicalKrullDim X ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom f).trans (le_of_eq hYdim)
  have hsupp : (J.support : Set a.obj.left) ≠ Set.univ := by
    intro he
    refine genericPoint_notMem_supportSet J hJ ?_
    show genericPoint a.obj.left ∈ (J.support : Set a.obj.left)
    rw [he]
    trivial
  obtain ⟨l, hl⟩ := exists_lift_blowUpToBase_of_isRegular hXdim hreg J a.lift.left hsupp
  let a' : ResolutionFactorization f :=
    { obj := Over.mk (blowUpToBase J ≫ a.obj.hom)
      chain := a.chain.step y hy (Set.mem_univ _)
      lift := Over.homMk l (by
        show l ≫ (blowUpToBase J ≫ a.obj.hom) = f
        rw [← Category.assoc, hl]
        exact Over.w a.lift)
      birational := isBirational_of_comp_blowUpToBase J hJ l (by rw [hl]; exact a.birational) }
  let k : a'.obj ⟶ a.obj := Over.homMk (blowUpToBase J) rfl
  have hfac : a'.lift ≫ k = a.lift := by
    ext
    exact hl
  have heq (i : 𝒰.I₀) : sectionImage (U i) (a'.lift ≫ k) = sectionImage (U i) a'.lift := by
    rw [hfac]
    exact ha a' (fun i => by rw [← hfac]; exact sectionImage_comp_le (U i) a'.lift k) i
  obtain ⟨hN', hI', hF', hL'⟩ := resolutionFactorization_properties hYdim a'
  have := hN'
  have := hI'
  have := hF'
  have := hL'
  have hkfin : IsFinite k.left := by
    have : IsFinite (k.left ≫ a.obj.hom) := hF'
    exact IsFinite.of_comp k.left a.obj.hom
  have hdomLift' : IsDominant a'.lift.left := a'.birational.isDominant
  have hdomk : IsDominant k.left := hbb.isDominant
  have hkiso : IsIso k.left := isIso_of_sectionMap_bijective U hU hcover k fun i =>
    ⟨sectionMap_injective (U i) k,
      sectionMap_surjective_of_sectionImage_eq (U i) a'.lift k
        (sectionMap_injective (U i) a'.lift) (heq i)⟩
  have : IsIso (blowUpToBase J) := hkiso
  exact isEffectiveCartierDivisor_of_isIso_blowUpToBase J

/-! ### An alteration of a curve is finite -/

/-- **An alteration of a locally Noetherian integral scheme of dimension at most one is
finite.** An alteration is finite over a nonempty open of the target, hence quasi-finite at the
generic point of its source, so [Stacks, Tag 0AB7] makes it finite over a neighbourhood of every
point of the target; finiteness is Zariski local on the target. -/
theorem isFinite_of_isAlteration_of_topologicalKrullDim_le_one {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : IsAlteration f)
    (hY : topologicalKrullDim Y ≤ 1) : IsFinite f := by
  have : IsProper f := hf.1
  have : IsIntegral X := hf.2.2.1
  obtain ⟨U, hUne, hUfin⟩ := hf.2.2.2
  have : IsFinite (f ∣_ U) := hUfin
  have hgen : f (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp hf.2.1
  have hηY : genericPoint Y ∈ U :=
    (genericPoint_spec Y).mem_open_set_iff U.2 |>.mpr (by simpa using hUne)
  have hηU : genericPoint X ∈ f ⁻¹ᵁ U := by
    show f (genericPoint X) ∈ U
    rwa [hgen]
  have hqf : quasiFiniteAt f (genericPoint X) := by
    constructor
    · obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f (genericPoint X))) isOpen_univ
      obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        hxW (f ⁻¹ᵁ W).2
      exact ⟨⟨W, hW⟩, ⟨V, hV⟩, hxV, hVW, f.finiteType_appLE hW hV hVW⟩
    · have h2 : ((f ∣_ U) ≫ U.ι).QuasiFiniteAt (⟨genericPoint X, hηU⟩ : (f ⁻¹ᵁ U)) :=
        (Scheme.Hom.quasiFiniteAt_comp_iff (f := f ∣_ U) (g := U.ι)).mpr
          ((f ∣_ U).quasiFiniteAt _)
      have h1 : ((f ⁻¹ᵁ U).ι ≫ f).QuasiFiniteAt (⟨genericPoint X, hηU⟩ : (f ⁻¹ᵁ U)) := by
        rwa [← morphismRestrict_ι f U]
      have h3 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
        (f := (f ⁻¹ᵁ U).ι) (g := f)).mp h1
      simpa only [Scheme.Opens.ι_apply] using h3
  have key : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
    intro y
    have hstalk : ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
      rw [ringKrullDim_stalk_eq_coheight]
      calc (coheight y : WithBot ℕ∞)
          ≤ topologicalKrullDim (Y : Type u) := by
            rw [topologicalKrullDim,
              krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (Y : Type u)))]
            exact coheight_le_krullDim y
        _ ≤ 1 := hY
    refine exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one f y hstalk
      (Or.inr (Or.inr (Or.inl fun η hη => ?_)))
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
    subst hη
    exact hqf
  have hzl : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict key

/-! ### The equivalence -/

/-- **Stacks Project, Tag 0BI4.** For a one-dimensional integral Noetherian scheme `Y` the
following are equivalent: there is an alteration `X → Y` with `X` regular; there is a resolution
of singularities of `Y`; there is a finite sequence of blowups in closed points
`Y_n → … → Y_1 → Y` with `Y_n` regular; and the normalization `Y^ν → Y` is finite. -/
@[stacks 0BI4, ega "IV 7.9.1" "more general"]
theorem resolveCurve_tfae (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hYdim : topologicalKrullDim Y = 1) :
    List.TFAE [
      ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsAlteration f ∧ IsRegular X,
      ∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f,
      ∃ (X : Scheme.{u}) (f : X ⟶ Y), PointBlowupChain Y Set.univ X f ∧ IsRegular X,
      IsFinite (Scheme.normalization Y
        finite_irreducibleComponents_isCompactOpen_of_isNoetherian)] := by
  classical
  set hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  tfae_have 1 → 4 := by
    rintro ⟨X, f, hf, hreg⟩
    have : IsProper f := hf.1
    have : IsIntegral X := hf.2.2.1
    have : IsNoetherian X := isNoetherian_of_isProper_over_noetherian f
    have hdom : IsDominant f := hf.2.1
    have : IsFinite f :=
      isFinite_of_isAlteration_of_topologicalKrullDim_le_one f hf (le_of_eq hYdim)
    exact normalization_isFinite_of_isFinite_regular_alteration Y X f hf hreg
  tfae_have 4 → 2 := by
    intro hfinite
    refine ⟨Y.normalizationScheme hY, Scheme.normalization Y hY, ⟨?_, ?_, inferInstance⟩, ?_⟩
    · exact Scheme.isBirational_normalization Y hY
    · have : IsFinite (Scheme.normalization Y hY) := hfinite
      infer_instance
    · have : IsFinite (Scheme.normalization Y hY) := hfinite
      have : IsLocallyNoetherian (Y.normalizationScheme hY) :=
        LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization Y hY)
      have hNdim : topologicalKrullDim (Y.normalizationScheme hY) = 1 := by
        rw [topologicalKrullDim_eq_of_isIntegralHom_of_surjective (Scheme.normalization Y hY),
          hYdim]
      have : IsNormal (Y.normalizationScheme hY) := Scheme.isNormal_normalizationScheme Y hY
      exact isRegular_of_isNormal_of_topologicalKrullDim_le_one _ (le_of_eq hNdim)
  tfae_have 2 → 1 := by
    rintro ⟨X, f, hmod, hreg⟩
    have : IsProper f := hmod.2.1
    have : IsIntegral X := hmod.2.2
    have hdom : IsDominant f := hmod.1.isDominant
    have hfin (Z : Scheme.{u}) [IsIntegral Z] : Finite (irreducibleComponents Z) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    obtain ⟨V, hVdense, hViso⟩ :=
      exists_dense_open_isIso_morphismRestrict_of_isBirational f hmod.1
        (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
    obtain ⟨y, hy⟩ := hVdense.nonempty
    refine ⟨X, f, ⟨inferInstance, hdom, inferInstance, V, ⟨⟨y, hy⟩⟩, ?_⟩, hreg⟩
    have : IsIso (f ∣_ V) := hViso
    infer_instance
  tfae_have 2 → 3 := by
    rintro ⟨X, f, hmod, hreg⟩
    have : IsProper f := hmod.2.1
    have : IsIntegral X := hmod.2.2
    have : IsNoetherian X := isNoetherian_of_isProper_over_noetherian f
    have : IsFinite f := isFinite_of_isProper_of_isBirational f hmod.1 (le_of_eq hYdim)
    exact exists_pointBlowupChain_isRegular_of_isResolution f hmod.1 hYdim hreg
  tfae_have 3 → 2 := by
    rintro ⟨X, f, hchain, hreg⟩
    obtain ⟨-, hI, hP, hB⟩ := pointBlowupChain_properties hYdim hchain
    exact ⟨X, f, ⟨hB, hP, hI⟩, hreg⟩
  tfae_finish

end AlgebraicGeometry

end
