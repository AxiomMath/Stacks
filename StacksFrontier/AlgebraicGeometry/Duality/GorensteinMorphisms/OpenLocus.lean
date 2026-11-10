module

public import StacksFrontier.AlgebraicGeometry.Discriminant.GorensteinLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.Dualizing.RelativeExistence
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion

/-!
# Openness of the Gorenstein locus

For a flat morphism of schemes locally of finite presentation, the set of points of the source at
which the morphism is Gorenstein is open.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_iff_of_comp_eq`: Gorensteinness at a point is
  unchanged by restricting source and target along open immersions.
* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_iff_of_flat_of_comp_eq`: for an `S`-morphism `g` to
  a scheme smooth over `S`, flat at a point, Gorensteinness of `g` there is that of the structure
  morphism of its source.
* `AlgebraicGeometry.Scheme.Hom.isOpen_setOf_isGorensteinAt_of_locallyQuasiFinite`: the locus
  is open for a flat, locally quasi-finite morphism locally of finite type to a locally
  Noetherian scheme.
* `AlgebraicGeometry.Scheme.Hom.isOpen_setOf_isGorensteinAt`: the locus is open for a flat
  morphism locally of finite presentation.

## Implementation notes

No upper shriek functor is used. For a flat quasi-finite morphism of Noetherian rings the locus is
the set of primes at which the relative dualizing module is invertible
(`Stacks.Discriminant.isOpen_setOf_isGorensteinLocalRing_fiber`). Over a locally Noetherian base a
Gorenstein point is Cohen–Macaulay, so by [Stacks, Tag 0BUU] it has a neighbourhood with a flat
locally quasi-finite morphism to affine space over the base, and there the two loci agree by
[Stacks, Tag 0C11]. A general base is reduced to a Noetherian one by writing an affine chart as a
base change of a flat morphism of finite presentation between Noetherian rings
(`Dualizing.exists_noetherianFlatModel`); the locus commutes with arbitrary base change
[Stacks, Tag 0E0Q].

## References

* [Stacks Project, Tag 0C09](https://stacks.math.columbia.edu/tag/0C09)
* [Stacks Project, Tag 0C11](https://stacks.math.columbia.edu/tag/0C11)
* [Stacks Project, Tag 0E0Q](https://stacks.math.columbia.edu/tag/0E0Q)
* [Stacks Project, Tag 0BUU](https://stacks.math.columbia.edu/tag/0BUU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Gorensteinness at a point depends only on the morphism, not on how it is written. -/
theorem isGorensteinAt_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ y : Y, IsLocallyNoetherian (g.fiber y)) (x : X) :
    IsGorensteinAt f hf x ↔ IsGorensteinAt g hg x := by
  subst h
  rfl

/-- Precomposing with an open immersion does not change Gorensteinness at a point. -/
theorem isGorensteinAt_comp_iff_of_isOpenImmersion_left {X Y Z : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Z)
    (hf : ∀ z : Z, IsLocallyNoetherian (f.fiber z))
    (hif : ∀ z : Z, IsLocallyNoetherian ((i ≫ f).fiber z)) (x : X) :
    IsGorensteinAt (i ≫ f) hif x ↔ IsGorensteinAt f hf (i x) := by
  have hs := syntomic_of_isOpenImmersion i
  have hi := isLocallyNoetherian_fiber_of_syntomic hs
  exact ⟨fun h => isGorensteinAt_right_of_comp i f hi hf hif x h (Flat.stalkMap i x),
    fun h => isGorensteinAt_comp i f hi hf hif x (isGorenstein_of_syntomic i hs x) h⟩

/-- Postcomposing with an open immersion does not change Gorensteinness at a point. -/
theorem isGorensteinAt_comp_iff_of_isOpenImmersion_right {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hfj : ∀ z : Z, IsLocallyNoetherian ((f ≫ j).fiber z)) (x : X) :
    IsGorensteinAt (f ≫ j) hfj x ↔ IsGorensteinAt f hf x := by
  have hs := syntomic_of_isOpenImmersion j
  have hj := isLocallyNoetherian_fiber_of_syntomic hs
  exact ⟨fun h => isGorensteinAt_left_of_comp f j hf hj hfj x h
      ((flatAt_postcomp_openImmersion_iff f j x).mpr h.1),
    fun h => isGorensteinAt_comp f j hf hj hfj x h (isGorenstein_of_syntomic j hs _)⟩

/-- Gorensteinness at a point is unchanged by restricting source and target along open
immersions: if `i ≫ f = g ≫ j` with `i` and `j` open immersions, then `f` is Gorenstein at `i x`
exactly when `g` is Gorenstein at `x`. -/
theorem isGorensteinAt_iff_of_comp_eq {X Y X' Y' : Scheme.{u}}
    (i : X' ⟶ X) [IsOpenImmersion i] (j : Y' ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ Y) (g : X' ⟶ Y') (w : i ≫ f = g ≫ j)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ y : Y', IsLocallyNoetherian (g.fiber y))
    (hif : ∀ y : Y, IsLocallyNoetherian ((i ≫ f).fiber y)) (x : X') :
    IsGorensteinAt f hf (i x) ↔ IsGorensteinAt g hg x := by
  have hgj : ∀ y : Y, IsLocallyNoetherian ((g ≫ j).fiber y) := w ▸ hif
  rw [← isGorensteinAt_comp_iff_of_isOpenImmersion_left i f hf hif x,
    isGorensteinAt_congr w hif hgj x, isGorensteinAt_comp_iff_of_isOpenImmersion_right g j hg hgj x]

/-- A flat morphism `Spec B → Spec R` is Gorenstein at a prime `q` of `B` exactly when the
localization of the fibre algebra `κ(q ∩ R) ⊗_R B` at the prime corresponding to `q` is
Gorenstein. -/
theorem isGorensteinAt_specMap_iff {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B]
    (hf : ∀ y, IsLocallyNoetherian ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber y))
    (q : PrimeSpectrum B)
    [IsNoetherianRing (Localization.AtPrime (affineFiberPoint (R := R) q).asIdeal)] :
    IsGorensteinAt (Spec.map (CommRingCat.ofHom (algebraMap R B))) hf q ↔
      Dualizing.IsGorensteinLocalRing
        (Localization.AtPrime (affineFiberPoint (R := R) q).asIdeal) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have := hf (f q)
  have he := Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (affineFiberStalkRingEquiv (R := R) (T := B) q)
  exact ⟨fun h => he.mp h.2, fun h => ⟨Flat.stalkMap f q, he.mpr h⟩⟩

/-- If an open map `φ` pulls a set `A` back to an open set `B`, then `A` contains an open
neighbourhood of every point `φ z` of `A`. -/
private theorem exists_isOpen_subset_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {φ : Y → X} (hφ : IsOpenMap φ) {A : Set X} {B : Set Y} (hB : IsOpen B)
    (h : ∀ z, φ z ∈ A ↔ z ∈ B) {z : Y} (hz : φ z ∈ A) :
    ∃ t ⊆ A, IsOpen t ∧ φ z ∈ t :=
  ⟨φ '' B, by rintro _ ⟨z', hz', rfl⟩; exact (h z').mpr hz', hφ _ hB, z, (h z).mp hz, rfl⟩

/-- **The Gorenstein locus of a flat locally quasi-finite morphism is open.** Let `g : Y ⟶ T` be
flat, locally of finite type and locally quasi-finite, with `T` locally Noetherian. The set of
points at which `g` is Gorenstein is open. -/
theorem isOpen_setOf_isGorensteinAt_of_locallyQuasiFinite {Y T : Scheme.{u}} (g : Y ⟶ T)
    [Flat g] [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsLocallyNoetherian T] :
    IsOpen {y : Y | IsGorensteinAt g (isLocallyNoetherian_fiber_of_locallyOfFiniteType g) y} := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyV (g ⁻¹ᵁ V).isOpen
  replace hV : IsAffineOpen V := hV
  replace hU : IsAffineOpen U := hU
  let R : Type u := Γ(T, V)
  let B : Type u := Γ(Y, U)
  let : Algebra R B := (g.appLE V U hUV).hom.toAlgebra
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Algebra.FiniteType R B :=
    HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have : Algebra.QuasiFinite R B :=
    HasRingHomProperty.appLE @LocallyQuasiFinite g inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have : Module.Flat R B := HasRingHomProperty.appLE @Flat g inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  let f' : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : LocallyOfFiniteType f' :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let hf' := isLocallyNoetherian_fiber_of_locallyOfFiniteType f'
  have hopen : IsOpen {z : Spec (.of B) | IsGorensteinAt f' hf' z} := by
    have hset : {z : Spec (.of B) | IsGorensteinAt f' hf' z} =
        {q : PrimeSpectrum B | Dualizing.IsGorensteinLocalRing
          (Localization.AtPrime (affineFiberPoint (R := R) q).asIdeal)} := by
      ext q
      exact isGorensteinAt_specMap_iff hf' q
    rw [hset]
    exact Stacks.Discriminant.isOpen_setOf_isGorensteinLocalRing_fiber
      (fun q => (PrimeSpectrum.comap (algebraMap R B) q).asIdeal)
      (fun q => (affineFiberPoint (R := R) q).asIdeal) affineFiberPoint_comap
  have w : hU.fromSpec ≫ g = f' ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g hV hU hUV).symm
  have hpt (z : Spec (.of B)) :
      IsGorensteinAt g (isLocallyNoetherian_fiber_of_locallyOfFiniteType g) (hU.fromSpec z) ↔
        IsGorensteinAt f' hf' z :=
    isGorensteinAt_iff_of_comp_eq hU.fromSpec hV.fromSpec g f' w _ hf'
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType _) z
  obtain ⟨z, rfl⟩ : y ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  exact exists_isOpen_subset_of_isOpenMap hU.fromSpec.isOpenEmbedding.isOpenMap hopen hpt hy

/-- For an `S`-morphism `g : U ⟶ P` to a scheme `P` smooth over `S` which is flat at `x`, the
morphism `g` is Gorenstein at `x` exactly when the structure morphism `U ⟶ S` is. -/
theorem isGorensteinAt_iff_of_flat_of_comp_eq {U P S : Scheme.{u}} (g : U ⟶ P) (p : P ⟶ S)
    [Smooth p] (h : U ⟶ S) (w : g ≫ p = h)
    (hg : ∀ y : P, IsLocallyNoetherian (g.fiber y))
    (hh : ∀ s : S, IsLocallyNoetherian (h.fiber s)) (x : U)
    (hflat : IsFlatAt g.toLRSHom.toShHom x) :
    IsGorensteinAt g hg x ↔ IsGorensteinAt h hh x := by
  have hs := syntomic_of_smooth p
  have hp := isLocallyNoetherian_fiber_of_syntomic hs
  have hgp : ∀ s : S, IsLocallyNoetherian ((g ≫ p).fiber s) := w ▸ hh
  exact ⟨fun hG => (isGorensteinAt_congr w hgp hh x).mp
      (isGorensteinAt_comp g p hg hp hgp x hG (isGorenstein_of_syntomic p hs _)),
    fun hH => isGorensteinAt_left_of_comp g p hg hp hgp x
      ((isGorensteinAt_congr w hgp hh x).mpr hH) hflat⟩

/-- **The Gorenstein locus over a locally Noetherian base is open.** For a flat morphism `f`
locally of finite presentation to a locally Noetherian scheme, the set of points at which `f` is
Gorenstein is open. -/
theorem isOpen_setOf_isGorensteinAt_of_isLocallyNoetherian {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S] :
    IsOpen {x : X | IsGorensteinAt f
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let hf := isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f
  have hCM := isCohenMacaulayAt_of_isGorensteinAt f hf hx
  obtain ⟨n, hn⟩ := exists_nat_topologicalKrullDimAt_fiber f x
  obtain ⟨U, hxU, g, hfac, ⟨hlft, hlqf⟩, hflat⟩ :=
    ((isCohenMacaulayAt_tfae f x n hn).out 1 3).mp hCM
  have := hlft
  have := hlqf
  have := hflat
  let P := AffineSpace (ULift.{u} (Fin n)) S
  have : Smooth (P ↘ S) := smooth_affineSpace_over _ S
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  have hopen := isOpen_setOf_isGorensteinAt_of_locallyQuasiFinite g
  have hpt (z : U.toScheme) :
      IsGorensteinAt g (isLocallyNoetherian_fiber_of_locallyOfFiniteType g) z ↔
        IsGorensteinAt f hf (U.ι z) :=
    (isGorensteinAt_iff_of_flat_of_comp_eq g (P ↘ S) (U.ι ≫ f) hfac _
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z
        (Flat.stalkMap g z)).trans
      (isGorensteinAt_comp_iff_of_isOpenImmersion_left U.ι f hf _ z)
  exact exists_isOpen_subset_of_isOpenMap (z := ⟨x, hxU⟩) U.ι.isOpenEmbedding.isOpenMap hopen
    (fun z => (hpt z).symm) hx

/-- Openness of the Gorenstein locus of `Spec A → Spec R` for a flat ring map of finite
presentation, by reduction to a Noetherian model and invariance under base change. -/
theorem isOpen_setOf_isGorensteinAt_specMap {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (hf : ∀ y, IsLocallyNoetherian ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber y)) :
    IsOpen {z : Spec (.of A) |
      IsGorensteinAt (Spec.map (CommRingCat.ofHom (algebraMap R A))) hf z} := by
  obtain ⟨R₁, A₁, _, _, _, _, _, _, _, _, ⟨e⟩⟩ := Dualizing.exists_noetherianFlatModel R A
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap R₁ A₁))
  let g₀ := Spec.map (CommRingCat.ofHom (algebraMap R₁ R))
  have : Flat f₀ := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation f₀ :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have h₀ := isOpen_setOf_isGorensteinAt_of_isLocallyNoetherian f₀
  let : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
  have : IsIso (CommRingCat.ofHom (e.toRingEquiv : A₁ ⊗[R₁] R →+* A)) :=
    (RingEquiv.toCommRingCatIso e.toRingEquiv).isIso_hom
  let ι : Spec (.of A) ⟶ pullback f₀ g₀ :=
    Spec.map (CommRingCat.ofHom (e.toRingEquiv : A₁ ⊗[R₁] R →+* A)) ≫
      (pullbackSpecIso R₁ A₁ R).inv
  have hsnd : ι ≫ pullback.snd f₀ g₀ = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    simp only [ι, f₀, g₀, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext e.commutes
  let hs := isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (pullback.snd f₀ g₀)
  have hset : {z : Spec (.of A) |
      IsGorensteinAt (Spec.map (CommRingCat.ofHom (algebraMap R A))) hf z} =
      (fun z => pullback.fst f₀ g₀ (ι z)) ⁻¹' {x | IsGorensteinAt f₀
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f₀) x} := by
    ext z
    have hbc := congrArg (ι z ∈ ·)
      (setOf_isGorensteinAt_pullback_eq_preimage f₀ g₀
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f₀) hs)
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, eq_iff_iff] at hbc ⊢
    rw [← hbc, ← isGorensteinAt_comp_iff_of_isOpenImmersion_left ι (pullback.snd f₀ g₀) hs
      (hsnd ▸ hf) z]
    exact isGorensteinAt_congr hsnd.symm hf _ z
  rw [hset]
  exact h₀.preimage ((pullback.fst f₀ g₀).continuous.comp ι.continuous)

/-- **Stacks Project, Tag 0C09, last assertion.** For a flat morphism of schemes `f : X ⟶ S`
locally of finite presentation, the set of points of `X` at which `f` is Gorenstein is open. -/
@[stacks 0C09 "the set of points where f is Gorenstein is open in X"]
theorem isOpen_setOf_isGorensteinAt {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] :
    IsOpen {x : X | IsGorensteinAt f
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  replace hV : IsAffineOpen V := hV
  replace hU : IsAffineOpen U := hU
  let R : Type u := Γ(S, V)
  let A : Type u := Γ(X, U)
  let : Algebra R A := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FinitePresentation R A :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have : Module.Flat R A := HasRingHomProperty.appLE @Flat f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  let f' : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : LocallyOfFinitePresentation f' :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let hf' := isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f'
  have hopen := isOpen_setOf_isGorensteinAt_specMap (R := R) (A := A) hf'
  have w : hU.fromSpec ≫ f = f' ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm
  have hpt (z : Spec (.of A)) :
      IsGorensteinAt f (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f)
          (hU.fromSpec z) ↔ IsGorensteinAt f' hf' z :=
    isGorensteinAt_iff_of_comp_eq hU.fromSpec hV.fromSpec f f' w _ hf'
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z
  obtain ⟨z, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  exact exists_isOpen_subset_of_isOpenMap hU.fromSpec.isOpenEmbedding.isOpenMap hopen hpt hx

/-- **Openness of the Gorenstein locus, without flatness.** For a morphism `f` locally of finite
presentation the set of points at which `f` is Gorenstein is open: it lies in the open flat locus
of `f`, on which `f` restricts to a flat morphism. -/
theorem isOpen_setOf_isGorensteinAt_of_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    IsOpen {x : X | IsGorensteinAt f
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) x} := by
  let W : X.Opens := ⟨{x | IsFlatAt f.toLRSHom.toShHom x}, isOpen_setOf_isFlatAt f⟩
  have : Flat (W.ι ≫ f) := (Flat.iff_flat_stalkMap _).mpr fun z =>
    (flatAt_precomp_openImmersion_iff W.ι f z).mp z.2
  have hopen := isOpen_setOf_isGorensteinAt (W.ι ≫ f)
  have hpt (z : W.toScheme) :
      IsGorensteinAt (W.ι ≫ f) (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z ↔
        IsGorensteinAt f (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f) (W.ι z) :=
    isGorensteinAt_comp_iff_of_isOpenImmersion_left W.ι f
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f)
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact exists_isOpen_subset_of_isOpenMap (z := ⟨x, hx.1⟩) W.ι.isOpenEmbedding.isOpenMap hopen
    (fun z => (hpt z).symm) hx

end AlgebraicGeometry.Scheme.Hom
