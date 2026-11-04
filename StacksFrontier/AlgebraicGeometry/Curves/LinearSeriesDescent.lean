module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.SectionSelection
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical
import all StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
import all StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# Descending a linear series along a nonconstant morphism of proper curves

Let `k` be a field, let `X` and `Y` be proper curves over `k` and let `g : X ⟶ Y` be a
nonconstant morphism over `k` of degree `m`. Let `ℒ` be an invertible `𝒪_X`-module with `r + 1`
global sections `s₀, …, s_r` generating its stalks whose classes in `H⁰(X, ℒ)` are `k`-linearly
independent, and suppose the morphism `φ_{(ℒ, s)} : X ⟶ ℙʳ_k` they define factors as `g ≫ ψ`
for a morphism `ψ : Y ⟶ ℙʳ_k` over `k`. Then `𝒩 := ψ ^* 𝒪(1)` is an invertible module on `Y`
whose degree `d'` satisfies `m · d' = deg ℒ`, and `𝒩` carries an `(r + 1)`-dimensional space of
global sections: a `𝔤^r_{d'}` on `Y` in the sense of [Stacks, Tag 0CCN].

The proof is in three steps. The pinned twist comparison of [Stacks, Tag 01ND] at the canonical
morphism gives `φ_{(ℒ, s)} ^* 𝒪(1) ≅ ℒ` carrying the pulled-back homogeneous coordinates to the
`sᵢ`; composing it with the comparison `g ^* ψ ^* ≅ (g ≫ ψ)^*` of pullback functors turns it into
an isomorphism `g ^* 𝒩 ≅ ℒ` carrying the pullbacks along `g` of the coordinate sections of `𝒩` to
the `sᵢ`. The degree formula of [Stacks, Tag 0AYZ] then reads `deg ℒ = m · deg 𝒩`, and
`deg ℒ ≥ 0` by part (1) of [Stacks, Tag 0B40] since `s₀ ≠ 0`, so `deg 𝒩 ≥ 0` because `m ≥ 1`.
Finally the pullback map on global sections is `k`-linear, so the classes of the coordinate
sections of `𝒩` are linearly independent in `H⁰(Y, 𝒩)` because their images in `H⁰(X, ℒ)` are;
their span is the required space of sections.

## Main results

* `AlgebraicGeometry.exists_linearSeries_of_comp_eq_toProjectiveSpaceOver`: a generating,
  linearly independent family of sections of an invertible module on `X` whose canonical morphism
  to `ℙʳ_k` factors through `g : X ⟶ Y` produces a linear series of dimension `r` on `Y` whose
  degree `d'` satisfies `m · d' = deg ℒ`, where `m = deg(X/Y)`.

## Implementation notes

**The degree of `𝒩` is produced as a natural number.** `AlgebraicGeometry.LinearSeries` records
the degree as a natural number, while `AlgebraicGeometry.invertibleCurveDegree` is an integer, so
the statement asserts the existence of a `d' : ℕ` with `m · d' = deg ℒ` together with a
`𝔤^r_{d'}`; nonnegativity of `deg 𝒩` is what makes such a `d'` exist, and it comes from
nonnegativity of `deg ℒ` and `m ≥ 1`.

**Linear independence is stated cohomologically.** `Γ(ℒ, ⊤)` carries no `Module k` instance, so
the hypothesis and the conclusion both speak of `AlgebraicGeometry.cohomologyOverField` in degree
zero, a `k`-vector space on the nose, with
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` moving a global section to its class.
The `k`-linear map that transports independence from `Y` to `X` is
`Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField` conjugated by
`AlgebraicGeometry.cohomologyOverFieldZeroIso` and followed by
`AlgebraicGeometry.cohomologyOverFieldMap` at the comparison isomorphism; on elements it is
`AlgebraicGeometry.pullbackGlobalSections` followed by the comparison, which is where the
factorization hypothesis enters.

**Two spellings of the pullback of a global section occur.**
`AlgebraicGeometry.pullbackSectionTop` is the unit of the pullback-pushforward adjunction read on
`⊤` and `AlgebraicGeometry.pullbackGlobalSections` post-composes it with the restriction along
`f ⁻¹ᵁ ⊤ = ⊤`; they agree by
`AlgebraicGeometry.pullbackGlobalSections_eq_pullbackSectionTop`. The twist comparison is pinned
in the first spelling and the `k`-linear pullback map acts in the second, so both appear.

**The binder `_hψ`.** The morphism `ψ` is asked to be a morphism over `k`, which is how
[Stacks, Tag 01ND] presents a morphism to `ℙʳ_k` and how the source states this step. The degree
formula and the comparison on `X` are established from the factorization `g ≫ ψ = φ_{(ℒ, s)}`
alone, so the underscore records that the argument does not read that hypothesis, while the
statement keeps it.

**The degree hypotheses on the dimension are interchangeable.**
[Stacks, Tag 0AYZ] states the degrees at
`le_of_eq (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one …)` while the linear series is
stated at an arbitrary proof of `topologicalKrullDim X ≤ 1`. The two are proofs of the same
proposition, so the degrees are the same term; the calculation below passes between them by
definitional equality rather than by rewriting.

## References

* [Stacks Project, Tag 0CCN](https://stacks.math.columbia.edu/tag/0CCN)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample (IsInvertibleModule)
open Stacks.AmpleProjectiveImmersion (twistingSheafAtUniverse projectiveSpaceTwistingSheaf)
open Stacks.ProjectiveFromSections (GeneratesStalks toProjectiveSpaceOver)
open Stacks.TwistPullbackPinned (coordGlobalSection)

universe u

namespace AlgebraicGeometry

/-! ### The homogeneous coordinates as global sections of `𝒪(1)` on `ℙʳ_S` -/

/-- The `j`-th homogeneous coordinate as a global section of `𝒪(1)` on `ℙʳ_S`. The hyperplane
sheaf of `ℙʳ_S` is the pullback of the one on the integral model `ℙʳ_ℤ`, and the coordinate
`Stacks.TwistPullbackPinned.coordGlobalSection` is pulled back along that morphism. -/
private def twistCoordSection (r : ℕ) (S : Scheme.{u}) (j : Fin (r + 1)) :
    Γ(projectiveSpaceTwistingSheaf r S, ⊤) :=
  pullbackSectionTop (projectiveSpaceOver.toIntegralAtUniverse r S)
    (twistingSheafAtUniverse.{u} r) (coordGlobalSection.{u} r j)

/-! ### Transporting a pinned comparison along a factorization -/

/-- **A pinned comparison at a composite is a pinned comparison after one pullback.** Given
`g ≫ ψ = φ` and an isomorphism `θ₀ : φ ^* 𝒲 ≅ ℒ` carrying the pullbacks along `φ` of a family
`u` of global sections of `𝒲` to a family `s` of global sections of `ℒ`, the canonical
isomorphism `g ^* ψ ^* ≅ (g ≫ ψ)^*` of pullback functors turns `θ₀` into an isomorphism
`g ^* ψ ^* 𝒲 ≅ ℒ` carrying the pullback along `g` of the pullback along `ψ` of `u` to `s`. -/
private theorem exists_iso_pullback_pullback_of_comp_eq {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (ψ : Y ⟶ Z) (φ : X ⟶ Z) (hfac : g ≫ ψ = φ) (W : Z.Modules) {L : X.Modules}
    (θ₀ : (Scheme.Modules.pullback φ).obj W ≅ L) {ι : Type*} (u : ι → Γ(W, ⊤))
    (s : ι → Γ(L, ⊤)) (hθ₀ : ∀ j, θ₀.hom.app ⊤ (pullbackSectionTop φ W (u j)) = s j) :
    ∃ θ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback ψ).obj W) ≅ L,
      ∀ j, θ.hom.app ⊤ (pullbackGlobalSections g ((Scheme.Modules.pullback ψ).obj W)
          (pullbackSectionTop ψ W (u j))) = s j := by
  refine ⟨(Scheme.Modules.pullbackComp g ψ).app W ≪≫
      (Scheme.Modules.pullbackCongr hfac).app W ≪≫ θ₀, fun j => ?_⟩
  rw [← pullbackGlobalSections_eq_pullbackSectionTop ψ W (u j)]
  calc ((Scheme.Modules.pullbackComp g ψ).app W ≪≫
          (Scheme.Modules.pullbackCongr hfac).app W ≪≫ θ₀).hom.app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback ψ).obj W)
          (pullbackGlobalSections ψ W (u j)))
      = θ₀.hom.app ⊤ (((Scheme.Modules.pullbackCongr hfac).hom.app W).app ⊤
          (((Scheme.Modules.pullbackComp g ψ).hom.app W).app ⊤
            (pullbackGlobalSections g ((Scheme.Modules.pullback ψ).obj W)
              (pullbackGlobalSections ψ W (u j))))) := rfl
    _ = s j := by
        rw [SectionsEqualizer.pullbackGlobalSections_comp,
          SectionsEqualizer.pullbackGlobalSections_congr,
          pullbackGlobalSections_eq_pullbackSectionTop]
        exact hθ₀ j

/-! ### The `k`-linear comparison of spaces of sections -/

/-- **Pulling back global sections along `g` and comparing, as a `k`-linear map on degree-zero
cohomology.** Degree-zero cohomology over the base field is the global sections
(`AlgebraicGeometry.cohomologyOverFieldZeroIso`), pulling back global sections along `g` is
`k`-linear (`Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField`), and an isomorphism
`g ^* ℰ ≅ ℒ` induces a `k`-linear map on cohomology
(`AlgebraicGeometry.cohomologyOverFieldMap`). -/
private def cohomologyPullbackCompMap (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (E : Y.Modules) {L : X.Modules}
    (θ : (Scheme.Modules.pullback g).obj E ≅ L) :
    cohomologyOverField k pY E 0 →ₗ[k] cohomologyOverField k (g ≫ pY) L 0 :=
  (cohomologyOverFieldMap k (g ≫ pY) θ.hom 0).hom ∘ₗ
    (cohomologyOverFieldZeroIso k (g ≫ pY) ((Scheme.Modules.pullback g).obj E)).inv.hom ∘ₗ
      Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField k pY g E ∘ₗ
        (cohomologyOverFieldZeroIso k pY E).hom.hom

/-- **A pinned comparison carries the classes of the pulled-back sections to the classes of the
pinning sections.** The bijection `H⁰ ≃ Γ(-, ⊤)` intertwines
`AlgebraicGeometry.cohomologyOverFieldMap` at `θ` with `θ` on sections, and the two outer factors
of `AlgebraicGeometry.cohomologyPullbackCompMap` are that bijection and its inverse. -/
private theorem cohomologyPullbackCompMap_apply (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (E : Y.Modules) {L : X.Modules}
    (θ : (Scheme.Modules.pullback g).obj E ≅ L) (t : Γ(E, ⊤)) :
    cohomologyPullbackCompMap k pY g E θ
        ((cohomologyOverFieldZeroEquivSections k pY E).symm t) =
      (cohomologyOverFieldZeroEquivSections k (g ≫ pY) L).symm
        (θ.hom.app ⊤ (pullbackGlobalSections g E t)) := by
  refine ((cohomologyOverFieldZeroEquivSections k (g ≫ pY) L).eq_symm_apply).mpr ?_
  have h1 : (cohomologyOverFieldZeroIso k pY E).hom.hom
      ((cohomologyOverFieldZeroEquivSections k pY E).symm t) = t :=
    (cohomologyOverFieldZeroEquivSections k pY E).apply_symm_apply t
  have h2 : (cohomologyOverFieldZeroEquivSections k (g ≫ pY)
        ((Scheme.Modules.pullback g).obj E))
      ((cohomologyOverFieldZeroIso k (g ≫ pY) ((Scheme.Modules.pullback g).obj E)).inv.hom
        (Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField k pY g E t)) =
      pullbackGlobalSections g E t :=
    (cohomologyOverFieldZeroEquivSections k (g ≫ pY)
      ((Scheme.Modules.pullback g).obj E)).apply_symm_apply _
  calc (cohomologyOverFieldZeroEquivSections k (g ≫ pY) L)
        (cohomologyPullbackCompMap k pY g E θ
          ((cohomologyOverFieldZeroEquivSections k pY E).symm t))
      = θ.hom.app ⊤ ((cohomologyOverFieldZeroEquivSections k (g ≫ pY)
          ((Scheme.Modules.pullback g).obj E))
            ((cohomologyOverFieldZeroIso k (g ≫ pY)
              ((Scheme.Modules.pullback g).obj E)).inv.hom
              (Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField k pY g E
                ((cohomologyOverFieldZeroIso k pY E).hom.hom
                  ((cohomologyOverFieldZeroEquivSections k pY E).symm t))))) :=
        cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k (g ≫ pY) θ.hom _
    _ = θ.hom.app ⊤ (pullbackGlobalSections g E t) := by rw [h1, h2]

/-- **Linear independence descends along a pinned comparison.** If the classes of the sections
`s` of `ℒ` are `k`-linearly independent and `θ : g ^* ℰ ≅ ℒ` carries the pullbacks along `g` of
sections `t` of `ℰ` to `s`, then the classes of `t` are `k`-linearly independent: they are
carried to the classes of `s` by the `k`-linear map
`AlgebraicGeometry.cohomologyPullbackCompMap`. -/
private theorem linearIndependent_cohomology_of_pinned {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (E : Y.Modules) {L : X.Modules}
    (θ : (Scheme.Modules.pullback g).obj E ≅ L) {ι : Type*} (t : ι → Γ(E, ⊤))
    (s : ι → Γ(L, ⊤)) (hpin : ∀ j, θ.hom.app ⊤ (pullbackGlobalSections g E (t j)) = s j)
    (hli : LinearIndependent k fun j =>
      (cohomologyOverFieldZeroEquivSections k (g ≫ pY) L).symm (s j)) :
    LinearIndependent k fun j => (cohomologyOverFieldZeroEquivSections k pY E).symm (t j) := by
  refine LinearIndependent.of_comp (cohomologyPullbackCompMap k pY g E θ) ?_
  have hfun : (cohomologyPullbackCompMap k pY g E θ ∘
        fun j => (cohomologyOverFieldZeroEquivSections k pY E).symm (t j)) =
      fun j => (cohomologyOverFieldZeroEquivSections k (g ≫ pY) L).symm (s j) :=
    funext fun j =>
      (cohomologyPullbackCompMap_apply k pY g E θ (t j)).trans (congrArg _ (hpin j))
  rwa [hfun]

/-! ### The degree of the descended module -/

/-- **The degree formula of [Stacks, Tag 0AYZ] at an invertible module and its pullback.** For a
nonconstant morphism `g : X ⟶ Y` of proper curves over `k` of degree `m` and an invertible
`𝒪_Y`-module `ℰ` with `g ^* ℰ ≅ ℒ`, one has `m · deg ℰ = deg ℒ`: an invertible module is finite
locally free of rank one, the degree is an isomorphism invariant, and the two notions of degree
agree at rank one. -/
private theorem mul_invertibleCurveDegree_of_iso_pullback {k : Type u} [Field k]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsProper pX] [IsCurve k pY] [IsProper pY]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (g : X ⟶ Y) (hg : g ≫ pY = pX) (hgnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (m : ℕ)
    (hm : @degreeOver X Y g inferInstance inferInstance
      (locallyOfFiniteType_of_isCurve_comp k pX pY g hg)
      (isDominant_of_not_constant k pX pY g hgnc) = m)
    (E : Y.Modules) [IsInvertibleModule Y E] {L : X.Modules} [IsInvertibleModule X L]
    (θ : (Scheme.Modules.pullback g).obj E ≅ L) :
    (m : ℤ) * @invertibleCurveDegree k _ Y pY _ hdimY E inferInstance =
      @invertibleCurveDegree k _ X pX _ hdimX L inferInstance := by
  have : IsInvertibleModule X ((Scheme.Modules.pullback g).obj E) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g E
  calc (m : ℤ) * @invertibleCurveDegree k _ Y pY _ hdimY E inferInstance
      = (m : ℤ) * curveDegree k pY hdimY E 1 := by
        rw [invertibleCurveDegree_eq_curveDegree_one]
    _ = curveDegree k pX hdimX ((Scheme.Modules.pullback g).obj E) 1 := by
        rw [← hm]
        exact (curveDegree_pullback_eq_degreeOver_mul k pX pY g hg hgnc E 1).symm
    _ = curveDegree k pX hdimX L 1 := curveDegree_eq_of_iso k pX hdimX 1 θ
    _ = @invertibleCurveDegree k _ X pX _ hdimX L inferInstance :=
        (invertibleCurveDegree_eq_curveDegree_one k pX hdimX L).symm

/-! ### A linear series descends along a nonconstant morphism of proper curves -/

/-- **A generating linearly independent family whose canonical morphism factors through `g`
descends to a linear series.** Let `k` be a field, let `X` and `Y` be proper curves over `k` and
let `g : X ⟶ Y` be a nonconstant morphism over `k` of degree `m ≥ 1`. Let `ℒ` be an invertible
`𝒪_X`-module with `r + 1` global sections `s` generating its stalks whose classes in `H⁰(X, ℒ)`
are `k`-linearly independent, and let `ψ : Y ⟶ ℙʳ_k` be a morphism over `k` with
`g ≫ ψ = φ_{(ℒ, s)}`. Then `ψ ^* 𝒪(1)` is invertible of some degree `d' : ℕ` with
`m · d' = deg ℒ`, and it carries an `(r + 1)`-dimensional space of global sections: a
`𝔤^r_{d'}` on `Y` in the sense of [Stacks, Tag 0CCN].

The space of sections is the span of the classes of the pullbacks along `ψ` of the homogeneous
coordinates; those classes are linearly independent because the pinned comparison
`g ^* ψ ^* 𝒪(1) ≅ ℒ` carries their pullbacks along `g` to the `sᵢ`. -/
theorem exists_linearSeries_of_comp_eq_toProjectiveSpaceOver {k : Type u} [Field k]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsProper pX] [IsCurve k pY] [IsProper pY]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (g : X ⟶ Y) (hg : g ≫ pY = pX) (hgnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)
    (m : ℕ)
    (hm : @degreeOver X Y g inferInstance inferInstance
      (locallyOfFiniteType_of_isCurve_comp k pX pY g hg)
      (isDominant_of_not_constant k pX pY g hgnc) = m)
    (hm1 : 1 ≤ m)
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {r : ℕ}
    (s : Fin (r + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    (hli : LinearIndependent k fun j =>
      (AlgebraicGeometry.cohomologyOverFieldZeroEquivSections k pX L).symm (s j))
    (ψ : Y ⟶ projectiveSpaceOver r (Spec (.of k)))
    (_hψ : ψ ≫ (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) = pY)
    (hfac : g ≫ ψ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs pX) :
    ∃ d' : ℕ, (m * d' : ℤ) = @invertibleCurveDegree k _ X pX _ hdimX L inferInstance ∧
      Nonempty (LinearSeries k pY hdimY d' r) := by
  classical
  obtain ⟨θ₀, hθ₀⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver s hs pX
  obtain ⟨θ, hθ⟩ := exists_iso_pullback_pullback_of_comp_eq g ψ
    (toProjectiveSpaceOver s hs pX) hfac (projectiveSpaceTwistingSheaf r (Spec (.of k))) θ₀
    (twistCoordSection r (Spec (.of k))) s hθ₀
  have hdeg := mul_invertibleCurveDegree_of_iso_pullback pX pY hdimX hdimY g hg hgnc m hm
    ((Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf r (Spec (.of k)))) θ
  have hs0 : s 0 ≠ 0 := by
    intro h0
    refine hli.ne_zero 0 ?_
    rw [h0]
    exact (Equiv.symm_apply_eq _).mpr (cohomologyOverFieldZeroEquivSections_zero k pX L).symm
  have hLrs : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := ‹_›
  have hdegL : 0 ≤ @invertibleCurveDegree k _ X pX _ hdimX L inferInstance := by
    refine invertibleCurveDegree_nonneg_of_eval_top_ne_zero k pX hdimX L
      (hL := hLrs) (Stacks.PresheafOfModules.sectionOfTop L.val (s 0)) ?_
    rw [show (Stacks.PresheafOfModules.sectionOfTop L.val (s 0)).eval (op ⊤) = s 0 from
      Stacks.PresheafOfModules.sectionOfTop_val_top L.val (s 0)]
    exact hs0
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm1
  have hdegN : 0 ≤ @invertibleCurveDegree k _ Y pY _ hdimY
      ((Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))))
      inferInstance := by
    by_contra hneg
    exact hdegL.not_gt (hdeg ▸ mul_neg_of_pos_of_neg hmpos (not_le.mp hneg))
  obtain ⟨d', hd'⟩ := Int.eq_ofNat_of_zero_le hdegN
  have hli' : LinearIndependent k fun j =>
      (cohomologyOverFieldZeroEquivSections k (g ≫ pY) L).symm (s j) := by
    rwa [hg]
  have hc := linearIndependent_cohomology_of_pinned pY g
    ((Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf r (Spec (.of k)))) θ
    (fun j => pullbackSectionTop ψ (projectiveSpaceTwistingSheaf r (Spec (.of k)))
      (twistCoordSection r (Spec (.of k)) j)) s hθ hli'
  refine ⟨d', ?_, ⟨⟨_, inferInstance, hd', Submodule.span k (Set.range fun j =>
      (cohomologyOverFieldZeroEquivSections k pY ((Scheme.Modules.pullback ψ).obj
        (projectiveSpaceTwistingSheaf r (Spec (.of k))))).symm
          (pullbackSectionTop ψ (projectiveSpaceTwistingSheaf r (Spec (.of k)))
            (twistCoordSection r (Spec (.of k)) j))),
    by rw [finrank_span_eq_card hc]; simp⟩⟩⟩
  rwa [← hd']

end AlgebraicGeometry

end
