module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.CompleteLocal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
import StacksFrontier.Homology.PseudoCoherent.Relative.Composition

/-!
# Flattening over a Noetherian complete local base

Let `S = Spec A` be the spectrum of a Noetherian complete local ring with closed point `s`, let
`f : X ⟶ S` be a morphism of finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite
type. There is a closed subscheme `Z ⊆ S` such that for every morphism of pointed schemes
`(T, t) ⟶ (S, s)` the module `F_T` is flat over `T` at every point of the fibre `X_t` exactly
when `Spec(𝒪_{T,t}) ⟶ S` factors through `Z`. This is the case `E = X_s` of Lemma 05PI, and
Remark 052G explains that it has a proof by elementary algebra: reduce to `X` affine by a finite
affine open cover, and in the affine case take for `Z` the closed subscheme cut out by the least
flattening ideal of More on Algebra, Lemma 0526, whose universal property is Lemma 0528.

## Main results

* `AlgebraicGeometry.exists_idealSheafData_forall_isFlatOverAt_iff_of_isAdicComplete`: the
  closed subscheme `Z` of Remark 052G.

## Implementation notes

The proof follows the remark. A finite affine open cover `Spec S_i ⟶ X` reduces flatness along
the whole fibre `X_t` to flatness along the fibres of the charts. Flat base change along
`Spec(𝒪_{T,t}) ⟶ T` (Tag 047C) replaces the pointed scheme `(T, t)` by the spectrum of the local
ring `R' = 𝒪_{T,t}` with its closed point, where the base change of the chart is
`Spec(S_i ⊗_A R')` and the pulled back module is the sheaf associated to
`(S_i ⊗_A R') ⊗_{S_i} M_i`. Flatness at the points over the closed point is then the algebraic
condition `Module.FlatAlongZeroLocus`, which by Lemma 0528 holds exactly when the least flattening
ideal `I_i` of the chart dies in `R'`. The closed subscheme is cut out by the sum of the `I_i`.

The closed subscheme is represented by its ideal sheaf, and a pointed morphism by a morphism
`g : T ⟶ Spec A` together with a point `t` mapping to the closed point. Since every point of the
fibre `X_t` maps into `X_s`, the condition for `E = X_s` quantifies over all points of `X_t`.

## References

* [Stacks Project, Tag 052G](https://stacks.math.columbia.edu/tag/052G)
* [Stacks Project, Tag 05PI](https://stacks.math.columbia.edu/tag/05PI)
* [Stacks Project, Tag 0528](https://stacks.math.columbia.edu/tag/0528)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace AlgebraicGeometry

/-- Relative flatness of a pulled-back module at a point is unchanged by precomposing with a
morphism which is flat at that point. -/
private lemma isFlatOverAt_pullback_iff_of_comp {X X₁ X₂ T : Scheme.{u}} (j : X₁ ⟶ X₂)
    (p₂ : X₂ ⟶ T) (q₂ : X₂ ⟶ X) (p₁ : X₁ ⟶ T) (q₁ : X₁ ⟶ X) (hp : j ≫ p₂ = p₁)
    (hq : j ≫ q₂ = q₁) (F : X.Modules) (x : X₁) (hj : IsFlatAt j.toLRSHom.toShHom x) :
    IsFlatOverAt p₂.toLRSHom.toShHom ((Scheme.Modules.pullback q₂).obj F) (j x) ↔
      IsFlatOverAt p₁.toLRSHom.toShHom ((Scheme.Modules.pullback q₁).obj F) x := by
  subst hp hq
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt j p₂ _ x hj).trans
    (ElementaryEtaleFlatness.flatOverAt_iff_of_iso (j ≫ p₂)
      ((Scheme.Modules.pullbackComp j q₂).app F) x)

/-- Flatness of the pulled-back module along the fibre over a point does not depend on the
choice of the pullback square. -/
private lemma forall_isFlatOverAt_iff_of_isPullback {X S T P P' : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {q : P ⟶ X} {p : P ⟶ T} {q' : P' ⟶ X} {p' : P' ⟶ T}
    (h : IsPullback q p f g) (h' : IsPullback q' p' f g) (F : X.Modules) (t : T) :
    (∀ y : P, p y = t →
        IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) y) ↔
      (∀ y : P', p' y = t →
        IsFlatOverAt p'.toLRSHom.toShHom ((Scheme.Modules.pullback q').obj F) y) := by
  let e := h.isoIsPullback _ _ h'
  have hp : e.hom ≫ p' = p := h.isoIsPullback_hom_snd _ _ h'
  have hq : e.hom ≫ q' = q := h.isoIsPullback_hom_fst _ _ h'
  have key (y : P) :
      IsFlatOverAt p'.toLRSHom.toShHom ((Scheme.Modules.pullback q').obj F) (e.hom y) ↔
        IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) y :=
    isFlatOverAt_pullback_iff_of_comp e.hom p' q' p q hp hq F y (Flat.stalkMap e.hom y)
  refine ⟨fun H y' hy' => ?_,
    fun H y hy => (key y).mp (H _ (by rw [← Scheme.Hom.comp_apply, hp, hy]))⟩
  have hy : e.hom (e.inv y') = y' := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rw [← hy, key]
  exact H _ (by rw [← hp, Scheme.Hom.comp_apply, hy, hy'])

/-- Flatness along the part of a fibre lying over an open subscheme `W` of the source is
flatness along the fibre of the restriction to `W`. -/
private lemma forall_isFlatOverAt_range_iff {X S T W P P' : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {q : P ⟶ X} {p : P ⟶ T} (h : IsPullback q p f g) (u : W ⟶ X)
    [IsOpenImmersion u] {q' : P' ⟶ W} {p' : P' ⟶ T} (h' : IsPullback q' p' (u ≫ f) g)
    (F : X.Modules) (t : T) :
    (∀ y : P, p y = t → q y ∈ Set.range u →
        IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) y) ↔
      (∀ y : P', p' y = t → IsFlatOverAt p'.toLRSHom.toShHom
        ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback u).obj F)) y) := by
  have h₀ : IsPullback (pullback.fst u q) (pullback.snd u q ≫ p) (u ≫ f) g :=
    (IsPullback.of_hasPullback u q).paste_vert h
  refine Iff.trans ?_ (forall_isFlatOverAt_iff_of_isPullback h₀ h' _ t)
  let v := pullback.snd u q
  have key (w : (pullback u q : Scheme.{u})) :
      IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) (v w) ↔
        IsFlatOverAt (v ≫ p).toLRSHom.toShHom ((Scheme.Modules.pullback (pullback.fst u q)).obj
          ((Scheme.Modules.pullback u).obj F)) w :=
    (isFlatOverAt_pullback_iff_of_comp v p q (v ≫ p) (pullback.fst u q ≫ u) rfl
      pullback.condition.symm F w (Flat.stalkMap v w)).trans
      (ElementaryEtaleFlatness.flatOverAt_iff_of_iso (v ≫ p)
        ((Scheme.Modules.pullbackComp (pullback.fst u q) u).app F).symm w)
  refine ⟨fun H w hw => (key w).mp (H _ hw ?_), fun H y hy hyu => ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  · obtain ⟨w, rfl⟩ : y ∈ Set.range v := by rwa [IsOpenImmersion.range_pullbackSnd]
    exact (key w).mpr (H w hy)

/-- Flatness along the fibre over `t` is unchanged by a flat base change `T' ⟶ T` at a point
`t'` over `t`. -/
private lemma forall_isFlatOverAt_iff_of_flat_baseChange {X S T T' P P' : Scheme.{u}}
    {f : X ⟶ S} {g : T ⟶ S} {q : P ⟶ X} {p : P ⟶ T} (h : IsPullback q p f g) (ι : T' ⟶ T)
    [Flat ι] {q' : P' ⟶ X} {p' : P' ⟶ T'} (h' : IsPullback q' p' f (ι ≫ g))
    (F : X.Modules) [F.IsQuasicoherent] (t : T) (t' : T') (ht : ι t' = t) :
    (∀ y : P, p y = t →
        IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) y) ↔
      (∀ y : P', p' y = t' →
        IsFlatOverAt p'.toLRSHom.toShHom ((Scheme.Modules.pullback q').obj F) y) := by
  have h₁ : IsPullback (pullback.fst p ι) (pullback.snd p ι) p ι := IsPullback.of_hasPullback p ι
  have h₀ : IsPullback (pullback.fst p ι ≫ q) (pullback.snd p ι) f (ι ≫ g) :=
    h₁.paste_horiz h
  refine Iff.trans ?_ (forall_isFlatOverAt_iff_of_isPullback h₀ h' F t')
  have key (y : (pullback p ι : Scheme.{u})) :
      IsFlatOverAt (pullback.snd p ι).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst p ι ≫ q)).obj F) y ↔
        IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F)
          (pullback.fst p ι y) := by
    refine (ElementaryEtaleFlatness.flatOverAt_iff_of_iso _
      ((Scheme.Modules.pullbackComp (pullback.fst p ι) q).app F).symm y).trans ?_
    have hqc : ((Scheme.Modules.pullback q).obj F).IsQuasicoherent :=
      Stacks.Modules.isQuasicoherent_pullback q F inferInstance
    exact ⟨@isFlatOverAt_of_modulePullback _ _ _ _ _ _ _ _ h₁ ((Scheme.Modules.pullback q).obj F)
      hqc y (Flat.stalkMap ι _),
      @modulePullback_isFlatOverAt_of_isFlatOverAt _ _ _ _ _ _ _ _ h₁
        ((Scheme.Modules.pullback q).obj F) hqc y⟩
  refine ⟨fun H y hy => (key y).mpr (H _ ?_), fun H y hy => ?_⟩
  · rw [← Scheme.Hom.comp_apply, h₁.w, Scheme.Hom.comp_apply, hy, ht]
  · obtain ⟨z, hz₁, hz₂⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := p) (g := ι) y t' (hy.trans ht.symm)
    rw [← hz₁]
    exact (key z).mp (H z hz₂)

/-- The square of spectra attached to a tensor product of algebras is a pullback square. -/
private lemma isPullback_SpecMap_tensorProduct (A S R' : Type u) [CommRing A] [CommRing S]
    [CommRing R'] [Algebra A S] [Algebra A R'] :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] R'))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R'))))
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (Spec.map (CommRingCat.ofHom (algebraMap A R'))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A S R')

/-- **The affine case.** For an `A`-algebra `S`, an `S`-module `M` and a local `A`-algebra
`R'`, the module associated to `(S ⊗_A R') ⊗_S M` on `Spec(S ⊗_A R')` is flat over `Spec R'`
at every point over the closed point exactly when `(S ⊗_A R') ⊗_S M` is flat over `R'` along the
primes over the maximal ideal. -/
private lemma forall_isFlatOverAt_tensorProduct_iff (A R' : Type u) [CommRing A] [CommRing R']
    [IsLocalRing R'] (S : CommRingCat.{u}) [Algebra A S] [Algebra A R'] (M : ModuleCat.{u} S) :
    (∀ z : PrimeSpectrum (S ⊗[A] R'),
        Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R'))) z =
          IsLocalRing.closedPoint R' →
        IsFlatOverAt (Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R')))).toLRSHom.toShHom
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] R'))))).obj
            (tilde M)) z) ↔
      Module.FlatAlongZeroLocus R' (S ⊗[A] R') (IsLocalRing.maximalIdeal R')
        ((S ⊗[A] R') ⊗[S] M) := by
  have hpt (z : PrimeSpectrum (S ⊗[A] R')) :
      Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R'))) z =
          IsLocalRing.closedPoint R' ↔
        (IsLocalRing.maximalIdeal R').map (algebraMap R' (S ⊗[A] R')) ≤ z.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    show PrimeSpectrum.comap (algebraMap R' (S ⊗[A] R')) z = IsLocalRing.closedPoint R' ↔ _
    rw [PrimeSpectrum.ext_iff]
    show z.asIdeal.comap (algebraMap R' (S ⊗[A] R')) = IsLocalRing.maximalIdeal R' ↔ _
    exact ⟨fun hz => hz.ge, fun hz =>
      le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ z.isPrime.ne_top)) hz⟩
  have hfl (z : PrimeSpectrum (S ⊗[A] R')) :
      IsFlatOverAt (Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R')))).toLRSHom.toShHom
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] R'))))).obj
            (tilde M)) z ↔
        Module.Flat R' (LocalizedModule.AtPrime z.asIdeal ((S ⊗[A] R') ⊗[S] M)) := by
    let e := (pullbackTildeIso S (CommRingCat.of (S ⊗[A] R'))
        (CommRingCat.ofHom (algebraMap S (S ⊗[A] R')))).app M ≪≫
      (tilde.functor _).mapIso (PseudoCoherence.extendScalarsAlgebraMapObjIso M)
    exact (ElementaryEtaleFlatness.flatOverAt_iff_of_iso _ e z).trans
      (isFlatOverAt_spec_tilde_iff_flat_localizedModule
        (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R')))
        (ModuleCat.of (CommRingCat.of (S ⊗[A] R')) ((S ⊗[A] R') ⊗[S] M)) rfl z)
  exact ⟨fun H q _ hq => (hfl ⟨q, inferInstance⟩).mp (H ⟨q, inferInstance⟩ ((hpt _).mpr hq)),
    fun H z hz => (hfl z).mpr (H z.asIdeal ((hpt z).mp hz))⟩

/-- A morphism from an affine scheme `Spec R` to `Spec A` factors through the closed subscheme
cut out by an ideal `K` of `A` exactly when the corresponding ring map kills `K`. -/
private lemma exists_factorization_ofIdealTop_iff (A R : Type u) [CommRing A] [CommRing R]
    (φ : CommRingCat.of A ⟶ CommRingCat.of R) (K : Ideal A) :
    (∃ h : Spec (.of R) ⟶ (Scheme.IdealSheafData.ofIdealTop
          (K.map (Scheme.ΓSpecIso (.of A)).inv.hom)).subscheme,
        h ≫ (Scheme.IdealSheafData.ofIdealTop
          (K.map (Scheme.ΓSpecIso (.of A)).inv.hom)).subschemeι = Spec.map φ) ↔
      K.map φ.hom = ⊥ := by
  set Z := Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso (.of A)).inv.hom)
  have h₁ : (∃ h : Spec (.of R) ⟶ Z.subscheme, h ≫ Z.subschemeι = Spec.map φ) ↔
      Z ≤ (Spec.map φ).ker := by
    refine ⟨fun ⟨h, hh⟩ => by simpa [← hh] using Scheme.Hom.le_ker_comp h Z.subschemeι,
      fun hle => ⟨(Spec.map φ).toImage ≫ Scheme.IdealSheafData.inclusion hle, by simp⟩⟩
  have h₂ : (Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom =
      (Scheme.ΓSpecIso (.of R)).inv.hom.comp φ.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_inv_naturality]
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
  rw [h₁, Scheme.ker_of_isAffine,
    show Z ≤ Scheme.IdealSheafData.ofIdealTop (RingHom.ker (Spec.map φ).appTop.hom) ↔
        K.map (Scheme.ΓSpecIso (.of A)).inv.hom ≤ RingHom.ker (Spec.map φ).appTop.hom from
      (Scheme.IdealSheafData.equivOfIsAffine (X := Spec (.of A))).symm.toOrderIso.le_iff_le,
    Ideal.map_le_iff_le_comap, RingHom.comap_ker, h₂, RingHom.ker_comp_of_injective _ hinj,
    Ideal.map_eq_bot_iff_le_ker]

/-- **One affine chart.** For an affine open `Spec S ⟶ X` of a scheme of finite type over a
Noetherian complete local ring `A`, the least flattening ideal `I` of the chart detects flatness
along the part of the fibre lying over the chart, after any pointed base change. -/
private lemma exists_ideal_forall_isFlatOverAt_range_iff (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (S : CommRingCat.{u}) (u : Spec S ⟶ X) [IsOpenImmersion u] :
    ∃ I : Ideal A, ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)) (t : T),
      g t = IsLocalRing.closedPoint A →
      ((∀ y : (pullback f g : Scheme.{u}), pullback.snd f g y = t →
          pullback.fst f g y ∈ Set.range u →
          IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
            ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
        I.map (Spec.preimage (T.fromSpecStalk t ≫ g)).hom = ⊥) := by
  let α : CommRingCat.of A ⟶ S := Spec.preimage (u ≫ f)
  let : Algebra A S := α.hom.toAlgebra
  have hα : Spec.map (CommRingCat.ofHom (algebraMap A S)) = u ≫ f := Spec.map_preimage _
  have hft : Algebra.FiniteType A S := by
    have : LocallyOfFiniteType (Spec.map α) := by
      rw [Spec.map_preimage]
      infer_instance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp this
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  let G : (Spec S).Modules := (Scheme.Modules.pullback u).obj F
  let M : ModuleCat.{u} S := moduleSpecΓFunctor.obj G
  let eG : G ≅ tilde M := (asIso G.fromTildeΓ).symm
  have : Module.Finite S M :=
    (tilde_isFiniteType_iff M).mp (Stacks.SheafOfModules.isFiniteType_of_iso eG)
  obtain ⟨I, -, hIflat, hImin⟩ := Module.exists_least_flattening_ideal A S M
  refine ⟨I, fun T g t ht => ?_⟩
  let R' : Type u := T.presheaf.stalk t
  let ι : Spec (.of R') ⟶ T := T.fromSpecStalk t
  let φ : CommRingCat.of A ⟶ CommRingCat.of R' := Spec.preimage (ι ≫ g)
  let : Algebra A R' := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A R')) = ι ≫ g := Spec.map_preimage _
  have hloc : IsLocalHom (algebraMap A R') := by
    rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
    have h₁ : g (ι (IsLocalRing.closedPoint R')) = IsLocalRing.closedPoint A := by
      rw [Scheme.fromSpecStalk_closedPoint, ht]
    have h₂ : Spec.map (CommRingCat.ofHom (algebraMap A R')) (IsLocalRing.closedPoint R') =
        g (ι (IsLocalRing.closedPoint R')) := by
      rw [hφ]
      rfl
    exact h₂.trans h₁
  have : Flat ι := flat_fromSpecStalk T t
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] R'))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (S ⊗[A] R')))) (u ≫ f) (ι ≫ g) := by
    rw [← hα, ← hφ]
    exact isPullback_SpecMap_tensorProduct A S R'
  refine (forall_isFlatOverAt_range_iff (IsPullback.of_hasPullback f g) u
    (IsPullback.of_hasPullback (u ≫ f) g) F t).trans ?_
  refine (forall_isFlatOverAt_iff_of_flat_baseChange (IsPullback.of_hasPullback (u ≫ f) g) ι
    hsq G t (IsLocalRing.closedPoint R') Scheme.fromSpecStalk_closedPoint).trans ?_
  refine Iff.trans ?_ ((forall_isFlatOverAt_tensorProduct_iff A R' S M).trans
    (Module.flatAlongZeroLocus_baseChange_iff_map_eq_bot_of_finiteType A S M I hIflat hImin R'))
  exact forall_congr' fun z => imp_congr_right fun _ =>
    ElementaryEtaleFlatness.flatOverAt_iff_of_iso _
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[A] R'))))).mapIso
        eG) z

/-- **Stacks Project, Tag 052G.** Let `S = Spec A` be the spectrum of a Noetherian complete local
ring with closed point `s`, let `f : X ⟶ S` be of finite type and let `F` be a quasi-coherent
`𝒪_X`-module of finite type. Then the closed subscheme `Z ⊆ S` of Lemma 05PI for `E = X_s`
exists: for every morphism of pointed schemes `(T, t) ⟶ (S, s)`, the pulled back module `F_T` is
flat over `T` at every point of the fibre `X_t` if and only if `Spec(𝒪_{T,t}) ⟶ S` factors
through `Z`. As the remark explains, the proof is elementary: a finite affine open cover reduces
to `X` affine, where `Z` is cut out by the least flattening ideal of More on Algebra, Lemma 0526,
whose universal property is Lemma 0528. -/
@[stacks 052G "the closed subscheme of Lemma 05PI for E = X_s over a Noetherian complete local
base, constructed from finite affine charts and Lemma 0528"]
theorem exists_idealSheafData_forall_isFlatOverAt_iff_of_isAdicComplete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ Z : (Spec (.of A)).IdealSheafData,
      ∀ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)) (t : T),
        g t = IsLocalRing.closedPoint A →
        ((∀ y : (pullback f g : Scheme.{u}), pullback.snd f g y = t →
            IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
              ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
          ∃ h : Spec (T.presheaf.stalk t) ⟶ Z.subscheme,
            h ≫ Z.subschemeι = T.fromSpecStalk t ≫ g) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒱 := X.affineOpenCover
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i : 𝒱.I₀ => Set.range (𝒱.f i))
    (fun i => (𝒱.f i).isOpenEmbedding.isOpen_range)
    (fun x _ => Set.mem_iUnion.mpr ⟨𝒱.idx x, 𝒱.covers x⟩)
  choose I hI using fun i : 𝒱.I₀ => exists_ideal_forall_isFlatOverAt_range_iff A f F (𝒱.X i) (𝒱.f i)
  refine ⟨Scheme.IdealSheafData.ofIdealTop
    ((⨆ i ∈ s, I i).map (Scheme.ΓSpecIso (.of A)).inv.hom), fun T g t ht => ?_⟩
  rw [← Spec.map_preimage (T.fromSpecStalk t ≫ g), exists_factorization_ofIdealTop_iff]
  have hcover : (∀ y : (pullback f g : Scheme.{u}), pullback.snd f g y = t →
        IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y) ↔
      ∀ i ∈ s, ∀ y : (pullback f g : Scheme.{u}), pullback.snd f g y = t →
        pullback.fst f g y ∈ Set.range (𝒱.f i) →
        IsFlatOverAt (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) y := by
    refine ⟨fun H i _ y hy _ => H y hy, fun H y hy => ?_⟩
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (pullback.fst f g y)))
    exact H i hi y hy hyi
  rw [hcover, Ideal.map_iSup, iSup_eq_bot]
  refine forall_congr' fun i => ?_
  rw [Ideal.map_iSup, iSup_eq_bot]
  exact forall_congr' fun _ => hI i T g t ht

end AlgebraicGeometry
