module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SeparatedAffineComplement
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Ample
public import StacksFrontier.AlgebraicGeometry.PicardGroup.RationalEquivalenceNormalVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An ample invertible sheaf on an irreducible smooth group scheme

Let `k` be an algebraically closed field and `G` a quasi-compact, irreducible, smooth group scheme
over `k`. Then `G` carries an ample invertible sheaf. This is the third paragraph of the proof of
[Stacks, Tag 0BF7], the divisor-and-norm argument, to which the first two paragraphs reduce the
tag.

## Main results

* `AlgebraicGeometry.exists_isAmple_of_smooth_of_irreducibleSpace`: a quasi-compact, irreducible,
  smooth group scheme over an algebraically closed field has an ample invertible sheaf.
* `AlgebraicGeometry.exists_section_nonvanishingLocus_eq_of_isAffineOpen`: on an irreducible
  Noetherian separated scheme with factorial local rings every nonempty affine open is the
  nonvanishing locus of a global section of an invertible module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_chart`: a scheme smooth over a field has a nonempty
  open which is finite locally free over an open of affine space.
* `AlgebraicGeometry.exists_isAmple_of_sections_over_affineSpace`: the ampleness criterion that
  closes the argument, through [Stacks, Tag 0BEH].

## The argument

Write `G` for the group scheme and `m` for its multiplication. The local rings of `G` are regular
([Stacks, Tag 056S]) hence factorial ([Stacks, Tag 0AG0]), and `G` is separated
([Stacks, Tag 047L]), so a nonempty affine open `U` is the complement of an effective Cartier
divisor `D` ([Stacks, Tag 0BCW]); the canonical section `s` of `𝒪_G(D)` has nonvanishing locus
exactly `U`.

An étale map from a nonempty open of `G` to `𝐀^d_k` ([Stacks, Tag 054L]) is finite over a dense
open of the target ([Stacks, Tag 03I1]); restricting, one gets a nonempty open `W` of `G` and a
finite locally free `π : W → V` onto an open `V ⊆ 𝐀^d_k`. Pull `s` back along
`G × W → G × G → G`, `(g, w) ↦ g w`, and take its norm ([Stacks, Tag 0BCZ]) along the finite
locally free `1 × π : G × W → G × V`. The result is a section `τ` of an invertible module `ℳ` on
`G × V` which is nonvanishing at `y` exactly when `s` is nonvanishing at `m(z)` for every point
`z` over `y`.

For a rational point `v` of `V` the restriction of `τ` to `G × v` does not vanish at a closed
point `g` as soon as every `w` over `v` has `g w ∈ U`. Such a `v` exists: the set of `w` with
`g w ∈ U` is a nonempty open of the irreducible `W`, so it contains the generic point of `W`, and
since the fibres of `π` are discrete, the closed set of `w` with `g w ∉ U` misses the fibre of some
`v` in the image of `π`. The nonvanishing locus of that restriction lies inside `U w₀⁻¹` for one
rational `w₀` over `v`, so it is affine. Finally all the restrictions `ℳ|_{G × v}` are
isomorphic by [Stacks, Tag 0BEH], `G` being a normal variety, so the restricted sections are
sections of one invertible module with affine nonvanishing loci covering the closed points, hence
covering `G`; that module is ample.

The source realises the norm of the pulled-back divisor through the closed image
`(1 × π)(𝒟)` and [Stacks, Tag 0AGA], and mentions the norm route in a footnote; the norm route is
the one taken here.

## References

* [Stacks Project, Tag 0BF7](https://stacks.math.columbia.edu/tag/0BF7)
* [Stacks Project, Tag 0BCW](https://stacks.math.columbia.edu/tag/0BCW)
* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 0BEH](https://stacks.math.columbia.edu/tag/0BEH)
* [Stacks Project, Tag 054L](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Tag 03I1](https://stacks.math.columbia.edu/tag/03I1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

open Stacks.PicardGroup

/-- On an irreducible Noetherian separated scheme with factorial local rings, every nonempty
affine open is the nonvanishing locus of a global section of an invertible module: the canonical
section of `𝒪_X(D)` for the effective Cartier divisor `D` of [Stacks, Tag 0BCW] cutting it out. -/
theorem exists_section_nonvanishingLocus_eq_of_isAffineOpen (X : Scheme.{u}) [IsNoetherian X]
    [Scheme.IsSeparated X] [IrreducibleSpace X]
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ (M : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X M) (s : Γ(M, ⊤)),
      Stacks.Ample.nonvanishingLocus M s = U := by
  obtain ⟨I, hI, hUI⟩ :=
    exists_effectiveCartierDivisor_compl_affineOpen_of_preirreducible X U hU hne hUFD
  have : Stacks.Divisors.IsEffectiveCartierDivisor I := hI
  let M : X.Modules := Stacks.Divisors.invertibleSheaf I
  have hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
    Stacks.Divisors.stacksIsInvertible_invertibleSheaf I
  refine ⟨M, (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hM,
    Stacks.NonvanishingSpelling.sectionsEquiv X M (Stacks.Divisors.canonicalSections I), ?_⟩
  exact (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq X M
    (Stacks.Divisors.canonicalSections I)).symm.trans
      ((Stacks.Divisors.nonvanishingLocus_canonicalSections I).trans hUI.symm)

/-- A scheme smooth over a field has factorial local rings: they are regular by
[Stacks, Tag 056S], hence unique factorization domains by [Stacks, Tag 0AG0]. -/
@[ega "IV 21.11.1" "special case",
  sga "2 XI 3.13" "special case",
  sga "6 X 7.8" "special case",
  sga "7 VIII 6.5.1" "special case",
  sga "7 VIII 7.2" "special case"]
theorem uniqueFactorizationMonoid_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  have hreg := ((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field f)
  have := hreg.2 x
  exact IsRegularLocalRing.uniqueFactorizationMonoid _

/-- A scheme smooth over a field is normal. -/
theorem isNormal_of_smooth_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] : IsNormal X := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  exact isNormal_of_smooth f

/-- Left translation by a global point of a group scheme, as an automorphism. -/
@[ega "IV 17.12.7", sga "3 VIIA 7.2.2" "partial"]
noncomputable def leftTranslationAut {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p : 𝟙_ (Over B) ⟶ G) : G ≅ G where
  hom := leftTranslation G p
  inv := leftTranslation G p⁻¹
  hom_inv_id := by
    rw [leftTranslation_comp, inv_mul_cancel]
    simp [leftTranslation]
  inv_hom_id := by
    rw [leftTranslation_comp, mul_inv_cancel]
    simp [leftTranslation]

/-- **The étale chart of the proof of [Stacks, Tag 0BF7].** A scheme smooth over a field, with a
chosen point `x₀`, has a nonempty open subscheme `W` and an open `V` of affine space over the
field such that `W` is finite locally free over `V`: an étale map from an affine neighbourhood of
`x₀` to affine space ([Stacks, Tag 054L]) is finite over a dense open of the target
([Stacks, Tag 03I1]), and its restriction there is finite, flat and of finite presentation. -/
theorem exists_isFiniteLocallyFree_chart (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x₀ : X) :
    ∃ (d : ℕ) (V : (𝔸(ULift.{u} (Fin d); Spec (.of K))).Opens) (W : Scheme.{u}) (j : W ⟶ X)
      (π : W ⟶ V.toScheme), IsOpenImmersion j ∧ Nonempty W ∧
        Stacks.Morphisms.IsFiniteLocallyFree π ∧ π ≫ openAffineSpaceOver K V = j ≫ f := by
  obtain ⟨d, U, hU, hx₀, hUV, π, hπ, hcomp⟩ := exists_affine_open_etale_affineSpace f x₀ ⊤
    (isAffineOpen_top _) trivial (InfinitesimalLifting.smoothAt_of_smooth f x₀)
  let e : 𝔸(ULift.{u} (Fin d); (⊤ : (Spec (.of K)).Opens).toScheme) ≅
      𝔸(ULift.{u} (Fin d); Spec (.of K)) :=
    { hom := AffineSpace.map _ (Scheme.topIso _).hom
      inv := AffineSpace.map _ (Scheme.topIso _).inv
      hom_inv_id := by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]
      inv_hom_id := by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id] }
  let π₁ : U.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (.of K)) := π ≫ e.hom
  have : Etale π := hπ
  have : Etale π₁ := by
    have : IsIso e.hom := Iso.isIso_hom e
    have : Etale e.hom := inferInstance
    show Etale (π ≫ e.hom)
    infer_instance
  have hπ₁ : π₁ ≫ (𝔸(ULift.{u} (Fin d); Spec (.of K)) ↘ Spec (.of K)) = U.ι ≫ f := by
    simp only [π₁, e, Category.assoc, AffineSpace.map_over]
    rw [← Category.assoc, hcomp, Scheme.topIso_hom, Scheme.Hom.resLE_comp_ι]
  have : IsAffine U.toScheme := hU
  obtain ⟨V, hVd, hVf⟩ := exists_dense_open_isFinite_of_quasiFinite π₁
  refine ⟨d, V, (π₁ ⁻¹ᵁ V).toScheme, (π₁ ⁻¹ᵁ V).ι ≫ U.ι, π₁ ∣_ V, inferInstance, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyV⟩ := hVd.inter_open_nonempty _ π₁.isOpenMap.isOpen_range
      ⟨π₁ ⟨x₀, hx₀⟩, ⟨x₀, hx₀⟩, rfl⟩
    obtain ⟨u, rfl⟩ := hy
    exact ⟨⟨u, hyV⟩⟩
  · rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    exact ⟨hVf, inferInstance, inferInstance⟩
  · rw [openAffineSpaceOver, ← Category.assoc, morphismRestrict_ι, Category.assoc, hπ₁,
      Category.assoc]

/-- The nonvanishing open of a section is the preimage of that of another if their nonvanishing
loci correspond. -/
private theorem nonvanishingOpen_eq_preimage {X Y : Scheme.{u}} (g : X ⟶ Y) (L : X.Modules)
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule Y M]
    (s : Γ(L, ⊤)) (σ : Γ(M, ⊤))
    (h : Stacks.Ample.nonvanishingLocus L s = g ⁻¹' Stacks.Ample.nonvanishingLocus M σ) :
    Stacks.NonvanishingOpen.nonvanishingOpen X L s =
      g ⁻¹ᵁ Stacks.NonvanishingOpen.nonvanishingOpen Y M σ :=
  TopologicalSpace.Opens.ext h

/-- **The ampleness criterion closing the proof of [Stacks, Tag 0BF7].** Let `X` be a normal
variety over `k`, `V ⊆ 𝔸^n_k` an open with a `k`-rational point `p₀`, and `σ` a global section
of an invertible module `ℳ` on `X ×_k V`. If every closed point `x` of `X` has a `k`-rational
point `p` of `V` such that the restriction of `σ` to `X × p` does not vanish at `x` and has affine
nonvanishing locus, then `X` carries an ample invertible module, namely `ℳ|_{X × p₀}`.

The restrictions `ℳ|_{X × p}` are all isomorphic to `ℳ|_{X × p₀}` by [Stacks, Tag 0BEH], so each
restricted section becomes a section of that one module with the same nonvanishing locus; and a
point of `X` lies in an affine nonvanishing locus as soon as a closed point it specializes to
does. -/
theorem exists_isAmple_of_sections_over_affineSpace (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [IsVariety k f] [IsNormal X] {n : Type u} [Finite n] (V : (𝔸(n; Spec (.of k))).Opens)
    (M : (pullback f (openAffineSpaceOver k V)).Modules)
    [hM : Stacks.Ample.IsInvertibleModule _ M] (σ : Γ(M, ⊤))
    (p₀ : Spec (.of k) ⟶ V.toScheme) (hp₀ : p₀ ≫ openAffineSpaceOver k V = 𝟙 _)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∃ (p : Spec (.of k) ⟶ V.toScheme)
      (hp : p ≫ openAffineSpaceOver k V = 𝟙 _),
      sectionOfPoint f p hp x ∈ Stacks.NonvanishingOpen.nonvanishingOpen _ M σ ∧
        IsAffineOpen (sectionOfPoint f p hp ⁻¹ᵁ Stacks.NonvanishingOpen.nonvanishingOpen _ M σ)) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L), @Stacks.Ample.IsAmple X L hL := by
  have hMs : Stacks.SheafOfModules.IsInvertible _ _ M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hM
  -- the restriction of `ℳ` to `X × p`, in the pullback spelling of [Stacks, Tag 0H78]
  let R : ∀ (p : Spec (.of k) ⟶ V.toScheme) (_ : p ≫ openAffineSpaceOver k V = 𝟙 _),
      X.Modules := fun p hp =>
    (RingedSpaceModuleAdjunction.modulePullback
      (sectionOfPoint f p hp).toLRSHom.toShHom).obj M
  have hR : ∀ p hp, Stacks.Ample.IsInvertibleModule X (R p hp) := fun p hp =>
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf _ M)
  -- all restrictions are isomorphic, by [Stacks, Tag 0BEH]
  have hiso : ∀ p hp, Nonempty (R p hp ≅ R p₀ hp₀) := fun p hp => by
    obtain ⟨e⟩ := nonempty_iso_pullback_sectionOfPoint_of_finite k f V p p₀ hp hp₀ M
    exact ⟨((Stacks.ProjectiveBundleQuotients.pullbackIso _).app M).symm ≪≫ e ≪≫
      (Stacks.ProjectiveBundleQuotients.pullbackIso _).app M⟩
  let := hR p₀ hp₀
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨R p₀ hp₀, hR p₀ hp₀, ?_⟩
  refine Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus _ fun x => ?_
  obtain ⟨g, hgx, hgc⟩ := nonempty_inter_closedPoints_of_isClosed X
    (Set.singleton_nonempty x).closure isClosed_closure
  obtain ⟨p, hp, hgp, haff⟩ := h g hgc
  obtain ⟨e⟩ := hiso p hp
  let := hR p hp
  let s : Γ(R p₀ hp₀, ⊤) := e.hom.app ⊤
    (Stacks.NonvanishingPullback.pullbackGlobalSection (sectionOfPoint f p hp) M σ)
  have hs : Stacks.Ample.nonvanishingLocus (R p₀ hp₀) s =
      (sectionOfPoint f p hp) ⁻¹' Stacks.Ample.nonvanishingLocus M σ :=
    (Stacks.Ample.nonvanishingLocus_congr e _).trans
      (Stacks.NonvanishingPullback.preimage_nonvanishingLocus _ M σ).symm
  have hopen : Stacks.NonvanishingOpen.nonvanishingOpen X (R p₀ hp₀) s =
      sectionOfPoint f p hp ⁻¹ᵁ Stacks.NonvanishingOpen.nonvanishingOpen _ M σ :=
    nonvanishingOpen_eq_preimage _ _ _ _ _ hs
  refine ⟨s, ?_, hopen ▸ haff⟩
  have hgs : g ∈ (Stacks.NonvanishingOpen.nonvanishingOpen X (R p₀ hp₀) s : Set X) := by
    rw [hopen]; exact hgp
  have hxs := (specializes_iff_mem_closure.mpr hgx).mem_open
    (Stacks.NonvanishingOpen.nonvanishingOpen X (R p₀ hp₀) s).isOpen hgs
  rwa [Stacks.NonvanishingOpen.coe_nonvanishingOpen] at hxs

/-- A point of a fibre product `X ×_S W` lying over a section `a` of `X ⟶ S` is the image of its
second coordinate under the section `W ⟶ X ×_S W` attached to `a`. -/
theorem eq_lift_snd_of_fst_mem_range {X W S : Scheme.{u}} (f : X ⟶ S) (q : W ⟶ S) (a : S ⟶ X)
    (ha : a ≫ f = 𝟙 S) (z : ↥(pullback f q)) (hz : pullback.fst f q z ∈ Set.range a) :
    z = (pullback.lift (f := f) (g := q) (q ≫ a) (𝟙 W) (by simp [ha])) (pullback.snd f q z) := by
  let sec := pullback.lift (f := f) (g := q) (q ≫ a) (𝟙 W) (by simp [ha])
  have h1 : sec ≫ pullback.snd f q = 𝟙 W := pullback.lift_snd _ _ _
  have hsq : IsPullback sec q (pullback.fst f q) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f q) (h₂₂ := f) (v₁₃ := q) ?_ ?_
      (IsPullback.of_hasPullback f q).flip
    · rw [h1, ha]
      exact IsPullback.of_id_fst
    · exact pullback.lift_fst _ _ _
  obtain ⟨s, hs⟩ := hz
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hsq z s hs.symm
  subst hw
  have h2 : pullback.snd f q (sec w) = w := by
    rw [← Scheme.Hom.comp_apply, h1]; rfl
  rw [h2]

/-- A locally quasi-finite morphism carries a non-closed point to a non-closed point: a point in
the fibre over a closed point is closed, since its specializations lie in that discrete fibre. -/
theorem isClosed_singleton_of_isClosed_singleton_image {W V : Scheme.{u}} (π : W ⟶ V)
    [LocallyQuasiFinite π] {w : W} (hw : IsClosed ({π w} : Set V)) : IsClosed ({w} : Set W) := by
  refine closure_subset_iff_isClosed.mp fun w' hw' => ?_
  have hsp : w ⤳ w' := specializes_iff_mem_closure.mpr hw'
  have hπ : π w' = π w := by
    have := (hsp.map π.continuous)
    exact (hw.closure_subset (specializes_iff_mem_closure.mp this))
  exact Set.mem_singleton_iff.mpr
    ((π.isDiscrete_preimage_singleton (π w)).eq_of_specializes hsp rfl hπ).symm

/-- Over an algebraically closed field, two rational points of a scheme locally of finite type
through the same point agree. -/
theorem eq_of_comp_eq_id_of_apply_eq {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] (p q : Spec (.of K) ⟶ Y)
    (hp : p ≫ g = 𝟙 _) (hq : q ≫ g = 𝟙 _) (t : Spec (.of K)) (h : p t = q t) : p = q := by
  have ht : t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  subst ht
  have := (pointEquivClosedPoint g).injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩)
    (Subtype.ext h)
  exact congrArg Subtype.val this

/-- **The divisor-and-norm argument of [Stacks, Tag 0BF7].** A quasi-compact, irreducible, smooth
group scheme over an algebraically closed field carries an ample invertible sheaf. See the module
documentation for the argument. -/
theorem exists_isAmple_of_smooth_of_irreducibleSpace (K : Type u) [Field K] [IsAlgClosed K]
    (H : Grp (Over (Spec (.of K)))) [Smooth H.X.hom] [QuasiCompact H.X.hom]
    [IrreducibleSpace H.X.left] :
    ∃ (L : H.X.left.Modules) (hL : Stacks.Ample.IsInvertibleModule H.X.left L),
      @Stacks.Ample.IsAmple H.X.left L hL := by
  let : GrpObj H.X := H.grp
  -- the scheme `H` is a normal variety with factorial local rings
  have : H.X.left.IsSeparated := isSeparated_of_groupScheme_over_field H
  have : IsSeparated H.X.hom := by
    have : IsSeparated (H.X.hom ≫ terminal.from (Spec (.of K))) := by
      rw [Subsingleton.elim (H.X.hom ≫ terminal.from _) (terminal.from H.X.left)]
      exact Scheme.IsSeparated.isSeparated_terminal_from
    exact IsSeparated.of_comp H.X.hom (terminal.from _)
  have : IsNormal H.X.left := isNormal_of_smooth_over_field H.X.hom
  have : IsIntegral H.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : CompactSpace H.X.left := QuasiCompact.compactSpace_of_compactSpace H.X.hom
  have : IsNoetherian H.X.left := ⟨⟩
  have : IsVariety K H.X.hom := {}
  have hUFD := uniqueFactorizationMonoid_stalk_of_smooth H.X.hom
  -- the étale chart and the affine open with its divisor
  obtain ⟨x₀⟩ : Nonempty H.X.left := inferInstance
  obtain ⟨d, V, W, j, π, hj, hW, hπ, hπj⟩ := exists_isFiniteLocallyFree_chart K H.X.hom x₀
  obtain ⟨U, hU, hx₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₀) (U := ⊤) trivial
  obtain ⟨M, hM, s, hs⟩ :=
    exists_section_nonvanishingLocus_eq_of_isAffineOpen H.X.left hUFD U hU ⟨x₀, hx₀U⟩
  -- the family of translates of the divisor, over `H ×_k W`
  let qW : W ⟶ Spec (.of K) := j ≫ H.X.hom
  let qV : V.toScheme ⟶ Spec (.of K) := openAffineSpaceOver K V
  have hπq : π ≫ qV = qW := hπj
  let F : pullback H.X.hom qW ⟶ pullback H.X.hom qV :=
    pullback.map _ _ _ _ (𝟙 _) π (𝟙 _) (by simp) (by simp [hπq])
  let PO : Over (Spec (.of K)) := Over.mk (pullback.fst H.X.hom qW ≫ H.X.hom)
  let a₁ : PO ⟶ H.X := Over.homMk (pullback.fst H.X.hom qW) rfl
  let a₂ : PO ⟶ H.X := Over.homMk (pullback.snd H.X.hom qW ≫ j)
    (by simp [PO, pullback.condition, qW])
  let μW : pullback H.X.hom qW ⟶ H.X.left := (lift a₁ a₂ ≫ μ[H.X]).left
  have hFfst : F ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hFsnd : F ≫ pullback.snd _ _ = pullback.snd _ _ ≫ π := pullback.lift_snd _ _ _
  have hsq : IsPullback F (pullback.snd _ _) (pullback.snd _ _) π := by
    refine IsPullback.of_right (h₁₂ := pullback.fst H.X.hom qV) (h₂₂ := qV)
      (v₁₃ := H.X.hom) ?_ hFsnd (IsPullback.of_hasPullback H.X.hom qV)
    rw [hFfst, hπq]
    exact IsPullback.of_hasPullback H.X.hom qW
  have : Stacks.Morphisms.IsFiniteLocallyFree F :=
    MorphismProperty.of_isPullback hsq.flip hπ
  have : IsFinite F :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation F).mp
      this).1
  -- the norm of the pulled-back canonical section
  let A : (pullback H.X.hom qW).Modules :=
    (RingedSpaceModuleAdjunction.modulePullback μW.toLRSHom.toShHom).obj M
  let σ : Γ(A, ⊤) := Stacks.NonvanishingPullback.pullbackGlobalSection μW M s
  let Nm := (Stacks.Norm.finiteLocallyFreeNorm F).toMorphismNormMap
  let NA := Stacks.Divisors.normInvertible F Nm A
  let τ := Stacks.Divisors.normGlobalSection F Nm A σ
  have hτ : ∀ y, y ∈ Stacks.Ample.nonvanishingLocus NA τ ↔
      ∀ z, F z = y → μW z ∈ (U : Set H.X.left) := by
    intro y
    rw [Stacks.Divisors.mem_nonvanishingLocus_normGlobalSection_iff]
    refine forall_congr' fun z => imp_congr_right fun _ => ?_
    exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff μW M s z).trans
      (by rw [hs])
  have : Stacks.Ample.IsInvertibleModule _ NA := inferInstance
  -- the translation formulas
  have hρ : ∀ (b : Spec (.of K) ⟶ W) (hb : b ≫ qW = 𝟙 _),
      sectionOfPoint H.X.hom b hb ≫ μW =
        (GrpObj.mulRight (Over.homMk (b ≫ j) (by simpa [qW] using hb) :
          𝟙_ (Over (Spec (.of K))) ⟶ H.X)).hom.left := by
    intro b hb
    let s' : H.X ⟶ PO := Over.homMk (sectionOfPoint H.X.hom b hb)
      (by simp [PO, ← Category.assoc, sectionOfPoint_fst])
    have h1 : s' ≫ a₁ = 𝟙 H.X := by
      ext; simp [s', a₁, sectionOfPoint_fst]
    have h2 : s' ≫ a₂ = toUnit H.X ≫ Over.homMk (b ≫ j) (by simpa [qW] using hb) := by
      ext; simp [s', a₂, ← Category.assoc, sectionOfPoint_snd]
    have h3 : s' ≫ lift a₁ a₂ ≫ μ[H.X] = (GrpObj.mulRight
        (Over.homMk (b ≫ j) (by simpa [qW] using hb) :
          𝟙_ (Over (Spec (.of K))) ⟶ H.X)).hom := by
      rw [GrpObj.mulRight_hom, ← Category.assoc, comp_lift, h1, h2]
    exact congrArg Over.Hom.left h3
  have hlam : ∀ (a : Spec (.of K) ⟶ H.X.left) (ha : a ≫ H.X.hom = 𝟙 _),
      pullback.lift (f := H.X.hom) (g := qW) (qW ≫ a) (𝟙 W) (by simp [ha]) ≫ μW =
        j ≫ (leftTranslationAut H.X (Over.homMk a (by simpa using ha))).hom.left := by
    intro a ha
    let jO : Over.mk qW ⟶ H.X := Over.homMk j rfl
    let s' : Over.mk qW ⟶ PO := Over.homMk (pullback.lift (qW ≫ a) (𝟙 W) (by simp [ha]))
      (by
        show pullback.lift (f := H.X.hom) (g := qW) (qW ≫ a) (𝟙 W) _ ≫
          pullback.fst H.X.hom qW ≫ H.X.hom = qW
        rw [pullback.lift_fst_assoc, Category.assoc, ha, Category.comp_id])
    have h1 : s' ≫ a₁ = jO ≫ toUnit H.X ≫ Over.homMk a (by simpa using ha) := by
      ext
      show pullback.lift (f := H.X.hom) (g := qW) (qW ≫ a) (𝟙 W) _ ≫
        pullback.fst H.X.hom qW = j ≫ H.X.hom ≫ a
      rw [pullback.lift_fst, Category.assoc]
    have h2 : s' ≫ a₂ = jO ≫ 𝟙 H.X := by
      ext
      show pullback.lift (f := H.X.hom) (g := qW) (qW ≫ a) (𝟙 W) _ ≫
        pullback.snd H.X.hom qW ≫ j = j ≫ 𝟙 _
      rw [pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
    have h3 : s' ≫ lift a₁ a₂ ≫ μ[H.X] =
        jO ≫ (leftTranslationAut H.X (Over.homMk a (by simpa using ha))).hom := by
      show _ = jO ≫ leftTranslation H.X _
      rw [leftTranslation, Hom.mul_def, ← Category.assoc, comp_lift, h1, h2, ← comp_lift,
        Category.assoc]
    exact congrArg Over.Hom.left h3
  -- `V` has a rational point
  have : LocallyOfFiniteType qV := by
    simp only [qV, openAffineSpaceOver]; infer_instance
  have : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace qV
  obtain ⟨w₁⟩ := hW
  have : Nonempty V.toScheme := ⟨π w₁⟩
  obtain ⟨v₀, -, hv₀⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := V.toScheme))
    isClosed_univ.isLocallyClosed
  refine exists_isAmple_of_sections_over_affineSpace K H.X.hom V NA τ
    (pointOfClosedPoint qV v₀ hv₀) (pointOfClosedPoint_comp _ _ _) fun x hx => ?_
  -- a closed point `x`, its left translate, and a rational point of `V` adapted to it
  let a := pointOfClosedPoint H.X.hom x hx
  have ha : a ≫ H.X.hom = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let lt := leftTranslationAut H.X (Over.homMk a (by simpa using ha))
  have hlt : IsIso lt.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso lt).hom)
  let W' : Set W := j ⁻¹' (lt.hom.left ⁻¹' (U : Set H.X.left))
  have hW'o : IsOpen W' := (U.isOpen.preimage lt.hom.left.continuous).preimage j.continuous
  have : Nonempty W := ⟨w₁⟩
  have : IrreducibleSpace W := j.isOpenEmbedding.irreducibleSpace
  have hW'ne : W'.Nonempty := by
    obtain ⟨y, hy⟩ := (lt.hom.left.homeomorph.surjective x₀ : ∃ y, _)
    obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter
      (U.isOpen.preimage lt.hom.left.continuous) j.isOpenEmbedding.isOpenMap.isOpen_range
      ⟨y, by change lt.hom.left y ∈ U; rw [show lt.hom.left y = x₀ from hy]; exact hx₀U⟩
      ⟨j w₁, w₁, rfl⟩
    obtain ⟨w, rfl⟩ := hz2
    exact ⟨w, hz1⟩
  have hξ : genericPoint W ∈ W' :=
    ((genericPoint_spec W).mem_open_set_iff hW'o).mpr (by simpa using hW'ne)
  let T : Set V.toScheme := Set.range π \ π '' W'ᶜ
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation π).mp hπ
  have hTo : IsOpen T :=
    π.isOpenMap.isOpen_range.sdiff (π.isClosedMap _ hW'o.isClosed_compl)
  have hTne : T.Nonempty := by
    refine ⟨π (genericPoint W), ⟨_, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzξ⟩
    have := (π.isDiscrete_preimage_singleton (π z)).eq_of_specializes
      (genericPoint_specializes z) hzξ.symm rfl
    exact hz (this ▸ hξ)
  obtain ⟨v, hvT, hvc⟩ := nonempty_inter_closedPoints hTne hTo.isLocallyClosed
  let p := pointOfClosedPoint qV v hvc
  have hp : p ≫ qV = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hpv : ∀ t, p t = v := pointOfClosedPoint_apply _ _ _
  refine ⟨p, hp, ?_, ?_⟩
  · -- the restricted section does not vanish at `x`
    show sectionOfPoint H.X.hom p hp x ∈
      (Stacks.NonvanishingOpen.nonvanishingOpen _ NA τ : Set _)
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, hτ]
    intro z hz
    have hfst : pullback.fst H.X.hom qW z = x := by
      have h1 := congrArg (pullback.fst H.X.hom qV) hz
      rwa [← Scheme.Hom.comp_apply, hFfst, ← Scheme.Hom.comp_apply, sectionOfPoint_fst] at h1
    have hsnd : π (pullback.snd H.X.hom qW z) = v := by
      have e1 : (F ≫ pullback.snd H.X.hom qV) z = π (pullback.snd H.X.hom qW z) := by
        rw [hFsnd, Scheme.Hom.comp_apply]
      have e2 : (sectionOfPoint H.X.hom p hp ≫ pullback.snd H.X.hom qV) x = v := by
        rw [sectionOfPoint_snd, Scheme.Hom.comp_apply, hpv]
      rw [Scheme.Hom.comp_apply] at e1 e2
      rw [← e1, hz, e2]
    have hw : pullback.snd H.X.hom qW z ∈ W' := by
      by_contra h
      exact hvT.2 ⟨_, h, hsnd⟩
    rw [eq_lift_snd_of_fst_mem_range H.X.hom qW a ha z
      ⟨H.X.hom x, by rw [hfst]; exact pointOfClosedPoint_apply _ _ _ _⟩,
      ← Scheme.Hom.comp_apply, hlam a ha]
    exact hw
  · -- the nonvanishing locus is contained in a translate of `U`, hence is affine
    obtain ⟨w₀, hw₀⟩ := hvT.1
    have hw₀c : IsClosed ({w₀} : Set W) :=
      isClosed_singleton_of_isClosed_singleton_image π (by rw [hw₀]; exact hvc)
    have : LocallyOfFiniteType qW := inferInstance
    let b := pointOfClosedPoint qW w₀ hw₀c
    have hb : b ≫ qW = 𝟙 _ := pointOfClosedPoint_comp _ _ _
    have hbp : b ≫ π = p := by
      refine eq_of_comp_eq_id_of_apply_eq qV _ _ (by rw [Category.assoc, hπq, hb]) hp
        (H.X.hom x) ?_
      rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hw₀, hpv]
    have hFι : sectionOfPoint H.X.hom b hb ≫ F = sectionOfPoint H.X.hom p hp := by
      apply pullback.hom_ext
      · rw [Category.assoc, hFfst, sectionOfPoint_fst, sectionOfPoint_fst]
      · rw [Category.assoc, hFsnd, ← Category.assoc, sectionOfPoint_snd, sectionOfPoint_snd,
          Category.assoc, hbp]
    let ρ := GrpObj.mulRight (Over.homMk (b ≫ j) (by simpa [qW] using hb) :
      𝟙_ (Over (Spec (.of K))) ⟶ H.X)
    have hρiso : IsIso ρ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso ρ).hom)
    have hsub : (sectionOfPoint H.X.hom p hp ⁻¹ᵁ
        Stacks.NonvanishingOpen.nonvanishingOpen _ NA τ) ≤ ρ.hom.left ⁻¹ᵁ U := by
      intro y hy
      have hy' : sectionOfPoint H.X.hom p hp y ∈ Stacks.Ample.nonvanishingLocus NA τ := by
        rw [← Stacks.NonvanishingOpen.coe_nonvanishingOpen]; exact hy
      have := (hτ _).mp hy' (sectionOfPoint H.X.hom b hb y)
        (by rw [← Scheme.Hom.comp_apply, hFι])
      rwa [← Scheme.Hom.comp_apply, hρ b hb] at this
    have hVaff : IsAffineOpen (ρ.hom.left ⁻¹ᵁ U) := hU.preimage _
    let Sg := sectionOfPoint H.X.hom p hp
    let A' : H.X.left.Modules :=
      (RingedSpaceModuleAdjunction.modulePullback Sg.toLRSHom.toShHom).obj NA
    let σ' := Stacks.NonvanishingPullback.pullbackGlobalSection Sg NA τ
    have heq : Sg ⁻¹ᵁ Stacks.NonvanishingOpen.nonvanishingOpen _ NA τ =
        Stacks.NonvanishingOpen.nonvanishingOpen _ A' σ' :=
      (nonvanishingOpen_eq_preimage _ _ _ _ _
        (Stacks.NonvanishingPullback.preimage_nonvanishingLocus _ NA τ).symm).symm
    have := Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen A' σ' hVaff
    rwa [← heq, inf_eq_right.mpr hsub] at this

end AlgebraicGeometry

end
