module

public import StacksFrontier.AlgebraicGeometry.Size.DiscreteValuativeCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedEtaleFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness

/-!
# The Noetherian valuative criterion for properness of a morphism of algebraic spaces

A morphism of algebraic spaces over `S` which is of finite type and quasi-separated, whose
target is locally Noetherian, and for which every valuative square over a *discrete* valuation
ring has exactly one dotted arrow, is proper.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isQuasiSeparated_of_discreteValuativeCriterion`:
  **Stacks 0ARK**.
* `AlgebraicGeometry.Space.universallyClosed_pullback_fst_of_chowCover`: the affine Noetherian
  base case, with the proper surjective scheme cover of Chow's lemma taken as data.

## Implementation notes

Separatedness is **Stacks 0ARJ**, so only universal closedness is at issue, and by
**Stacks 03IT** it may be tested on a family of étale charts of the target covering its points.
A locally Noetherian algebraic space has such a family whose members are spectra of Noetherian
rings, so the target may be taken to be the presheaf represented by a chart `Spec A` with `A`
Noetherian.

Over such a chart the weak form of Chow's lemma, **Stacks 089J**, supplies a scheme `X'` in the
site together with a proper surjective morphism to the base change of the source; by
**Stacks 08AJ** it is enough that `X' ⟶ Spec A` be universally closed, and that morphism is a
morphism of *schemes*, so the discrete valuative criterion of **Stacks 05JY** applies to it.
Its hypothesis is checked exactly as the source checks it: a valuative square for `X' ⟶ Spec A`
composes to one for the given morphism, whose dotted arrow exists by assumption, and that arrow
is lifted back through the proper morphism `X' ⟶ X ×_Y Spec A` by the valuative criterion of
properness, **Stacks 0A40**. The spectra occurring in the square are objects of the chosen big
site throughout, which is what
`AlgebraicGeometry.universallyClosed_of_contained_discreteValuativeCriterion` asks for.

Universal closedness of `X' ⟶ Spec A` is transferred from schemes to algebraic spaces through
**Stacks 03XD**, the morphism of presheaves being representable. Local finite type of
`X' ⟶ Spec A` is read off the composite `X' ⟶ X ×_Y Spec A ⟶ Spec A`, and quasi-compactness
from the H-quasi-projectivity that Chow's lemma provides.

## References

* [Stacks Project, Tag 0ARK](https://stacks.math.columbia.edu/tag/0ARK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Core

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A valuative square for the scheme morphism underlying `ψ` has a dotted arrow once its bottom
edge, read in the site, lifts to the fibre product compatibly with `p`, the morphism `p` being
proper. -/
theorem hasLift_of_pullback_lift_of_chowCover
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S) {f : X ⟶ Y}
    {φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y} (hXT : IsAlgebraicSpace B S hS (pullback φ f))
    {X' : BigFppfOver B S hS} {ψ : X' ⟶ siteObject B S hS hA a}
    {p : yoneda.obj X' ⟶ pullback φ f} (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (D : _root_.AlgebraicGeometry.ValuativeCommSq ((BigFppfOver.toScheme B S hS).map ψ))
    (hR : B.Contains (Spec (.of D.R))) (hK : B.Contains (Spec (.of D.K)))
    (aT : siteObject B S hS hR (D.i₂ ≫ a) ⟶ siteObject B S hS hA a)
    (k : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
      X')
    (haT : (BigFppfOver.toScheme B S hS).map aT = D.i₂)
    (hk : (BigFppfOver.toScheme B S hS).map k = D.i₁)
    (c : yoneda.obj (siteObject B S hS hR (D.i₂ ≫ a)) ⟶ pullback φ f)
    (hcfst : c ≫ pullback.fst φ f = yoneda.map aT)
    (hcι : yoneda.map (Over.homMk (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) : B.obj hK ⟶ B.obj hR) :
      siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
        siteObject B S hS hR (D.i₂ ≫ a)) ≫ c = yoneda.map k ≫ p) :
    D.commSq.HasLift := by
  let ι : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
      siteObject B S hS hR (D.i₂ ≫ a) :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) : B.obj hK ⟶ B.obj hR)
  let q₂ : ValuativeSquare p :=
    { R := D.R
      K := D.K
      ring_mem := hR
      field_mem := hK
      base := D.i₂ ≫ a
      generic := yoneda.map k
      special := c
      comm := hcι.symm }
  obtain ⟨M⟩ := ((isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated
    (isAlgebraicSpace_yoneda B S hS X') hXT p hp.2.1
    (isQuasiSeparated_of_isSeparated B S hS hp.1)).mp hp q₂).1
  let m : siteObject B S hS hR (D.i₂ ≫ a) ⟶ X' := yoneda.preimage M.map
  have hm : yoneda.map m = M.map := yoneda.map_preimage _
  have hmψ : m ≫ ψ = aT := by
    apply Yoneda.fullyFaithful.map_injective (F := yoneda)
    rw [yoneda.map_comp, hm, ← hpψ, ← Category.assoc, M.special_comm, hcfst]
  have hmι : ι ≫ m = k := by
    apply Yoneda.fullyFaithful.map_injective (F := yoneda)
    rw [yoneda.map_comp, hm]
    exact M.generic_comm
  refine ⟨⟨(BigFppfOver.toScheme B S hS).map m, ?_, ?_⟩⟩
  · change (BigFppfOver.toScheme B S hS).map ι ≫ (BigFppfOver.toScheme B S hS).map m = D.i₁
    rw [← Functor.map_comp, hmι, hk]
  · change (BigFppfOver.toScheme B S hS).map m ≫ (BigFppfOver.toScheme B S hS).map ψ = D.i₂
    rw [← Functor.map_comp, hmψ, haT]

/-- A valuative square over a discrete valuation ring for the scheme morphism underlying `ψ`,
whose edges are read in the site as `aT` and `k`, has a dotted arrow: composing with `p` and the
second projection gives a valuative square for `f`, whose dotted arrow lifts to the fibre
product. -/
theorem hasLift_of_valuativeSquare_lift_of_chowCover
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S) {f : X ⟶ Y}
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Nonempty q.Lift)
    {φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y} (hXT : IsAlgebraicSpace B S hS (pullback φ f))
    {X' : BigFppfOver B S hS} {ψ : X' ⟶ siteObject B S hS hA a}
    {p : yoneda.obj X' ⟶ pullback φ f} (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (D : _root_.AlgebraicGeometry.ValuativeCommSq ((BigFppfOver.toScheme B S hS).map ψ))
    (hDVR : IsDiscreteValuationRing D.R)
    (hR : B.Contains (Spec (.of D.R))) (hK : B.Contains (Spec (.of D.K)))
    (aT : siteObject B S hS hR (D.i₂ ≫ a) ⟶ siteObject B S hS hA a)
    (k : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
      X')
    (haT : (BigFppfOver.toScheme B S hS).map aT = D.i₂)
    (hk : (BigFppfOver.toScheme B S hS).map k = D.i₁)
    (hιaT : (Over.homMk (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) : B.obj hK ⟶ B.obj hR) :
      siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
        siteObject B S hS hR (D.i₂ ≫ a)) ≫ aT = k ≫ ψ) :
    D.commSq.HasLift := by
  let q₁ : ValuativeSquare f :=
    { R := D.R
      K := D.K
      ring_mem := hR
      field_mem := hK
      base := D.i₂ ≫ a
      generic := yoneda.map k ≫ p ≫ pullback.snd φ f
      special := yoneda.map aT ≫ φ
      comm := by
        calc (yoneda.map k ≫ p ≫ pullback.snd φ f) ≫ f
            = yoneda.map k ≫ p ≫ pullback.fst φ f ≫ φ := by
              rw [Category.assoc, Category.assoc, ← pullback.condition]
          _ = yoneda.map (k ≫ ψ) ≫ φ := by
              rw [← Category.assoc p, hpψ, ← Category.assoc (yoneda.map k), ← yoneda.map_comp]
          _ = yoneda.map (_ ≫ aT) ≫ φ := by rw [hιaT]
          _ = _ := by rw [yoneda.map_comp, Category.assoc] }
  obtain ⟨L⟩ := hlift q₁ hDVR
  let c : yoneda.obj (siteObject B S hS hR (D.i₂ ≫ a)) ⟶ pullback φ f :=
    pullback.lift (yoneda.map aT) L.map L.special_comm.symm
  have hcfst : c ≫ pullback.fst φ f = yoneda.map aT := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd φ f = L.map := pullback.lift_snd _ _ _
  refine hasLift_of_pullback_lift_of_chowCover B S hS A hA a hXT hp hpψ D hR hK aT k haT hk c
    hcfst (pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, hcfst, ← yoneda.map_comp, hιaT, yoneda.map_comp, Category.assoc, hpψ]
  · rw [Category.assoc, hcsnd, L.generic_comm]
    rfl

/-- The scheme morphism underlying `ψ` satisfies the discrete valuative lifting criterion for
valuative squares whose spectra lie in the site. -/
theorem hasLift_toScheme_map_of_chowCover
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S) {f : X ⟶ Y}
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Nonempty q.Lift)
    {φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y} (hXT : IsAlgebraicSpace B S hS (pullback φ f))
    {X' : BigFppfOver B S hS} {ψ : X' ⟶ siteObject B S hS hA a}
    {p : yoneda.obj X' ⟶ pullback φ f} (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (D : _root_.AlgebraicGeometry.ValuativeCommSq ((BigFppfOver.toScheme B S hS).map ψ))
    (hDVR : IsDiscreteValuationRing D.R)
    (hR : B.Contains (Spec (.of D.R))) (hK : B.Contains (Spec (.of D.K))) :
    D.commSq.HasLift := by
  have hX'hom : (B.inclusion).map X'.hom = (BigFppfOver.toScheme B S hS).map ψ ≫ a := by
    conv_lhs => rw [← Over.w ψ]
    exact (B.inclusion).map_comp _ _
  let k : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a) ⟶
      X' :=
    Over.homMk (ObjectProperty.homMk D.i₁ : B.obj hK ⟶ X'.left) (by
      apply ObjectProperty.hom_ext
      change D.i₁ ≫ (B.inclusion).map X'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a
      rw [hX'hom, ← Category.assoc D.i₁, D.commSq.w, Category.assoc])
  refine hasLift_of_valuativeSquare_lift_of_chowCover B S hS A hA a hlift hXT hp hpψ D hDVR hR hK
    (Over.homMk (ObjectProperty.homMk D.i₂ : B.obj hR ⟶ B.obj hA) rfl) k rfl rfl ?_
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ =
    D.i₁ ≫ (BigFppfOver.toScheme B S hS).map ψ
  exact D.commSq.w.symm

/-- **The affine Noetherian base case of Stacks 0ARK, with the Chow cover taken as data.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` of finite type, every valuative
square of which over a discrete valuation ring has a dotted arrow, and let `φ` be a morphism to
`Y` from the presheaf represented by a chart whose underlying scheme is the spectrum of a
Noetherian ring. If the base change of `f` along `φ` receives a proper surjective morphism `p`
from the presheaf represented by an object `X'` of the site, over that chart, and the scheme
morphism underlying `X' ⟶ Spec A` is quasi-compact, then the base change of `f` along `φ` is
universally closed.

The valuative squares of the scheme morphism `X' ⟶ Spec A` are turned into valuative squares of
`f` by composing with `p` and with the second projection; the assumed dotted arrow of the
latter, paired with the bottom edge, is a morphism to the fibre product, and the valuative
criterion of properness for `p` (Stacks 0A40) lifts it through `p`. That is the hypothesis of
`AlgebraicGeometry.universallyClosed_of_contained_discreteValuativeCriterion`, which gives
universal closedness of `X' ⟶ Spec A`; Stacks 03XD carries it back to algebraic spaces and
Stacks 08AJ pushes it down along the surjection `p`. -/
theorem universallyClosed_pullback_fst_of_chowCover
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    [IsLocallyNoetherian (Spec A)]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f)
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R → Nonempty q.Lift)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y)
    (X' : BigFppfOver B S hS) (ψ : X' ⟶ siteObject B S hS hA a)
    (p : yoneda.obj X' ⟶ pullback φ f)
    (hp : IsProper B S hS p) (hpsurj : IsSurjective B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (hqc : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map ψ)) :
    UniversallyClosed B S hS (pullback.fst φ f) := by
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS hA a)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec A))
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (siteObject B S hS hA a)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  have hXT : IsAlgebraicSpace B S hS (pullback φ f) :=
    isAlgebraicSpace_pullback B S hS φ f hT hX hY
  have hlftSpace : IsLocallyOfFiniteType B S hS (yoneda.map ψ) := by
    rw [← hpψ]
    exact isLocallyOfFiniteType_comp B S hS hX' hXT hT p (pullback.fst φ f) hp.2.1.1
      (IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback φ f) hX hY hft).1
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map ψ) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS ψ).mp hlftSpace
  have hucSpace : UniversallyClosed B S hS (p ≫ pullback.fst φ f) := by
    rw [hpψ]
    exact universallyClosed_yoneda_map B S hS ψ
      (_root_.AlgebraicGeometry.universallyClosed_of_contained_discreteValuativeCriterion
        B _ X'.left.2 fun D hDVR hR hK ↦
          hasLift_toScheme_map_of_chowCover B S hS A hA a hlift hXT hp hpψ D hDVR hR hK)
  exact universallyClosed_of_isSurjective_comp B S hS hX' hXT hT p (pullback.fst φ f)
    hucSpace hpsurj

/-- **An H-quasi-projective morphism of schemes is quasi-compact**, being a quasi-compact
immersion followed by the structure morphism of a relative projective space. -/
theorem quasiCompact_of_isHQuasiProjective {V W : Scheme.{u}} {χ : V ⟶ W}
    (h : IsHQuasiProjective χ) : _root_.AlgebraicGeometry.QuasiCompact χ := by
  obtain ⟨n, i, _, _, rfl⟩ := h
  infer_instance

/-- **Stacks 0ARK.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `Y`
locally Noetherian. If `f` is of finite type and quasi-separated, and every valuative square
for `f` whose valuation ring is a discrete valuation ring has exactly one dotted arrow, then
`f` is proper. -/
@[stacks 0ARK]
theorem isProper_of_isQuasiSeparated_of_discreteValuativeCriterion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      Nonempty q.Lift ∧ Subsingleton q.Lift) :
    IsProper B S hS f := by
  have hsep : IsSeparated B S hS f :=
    isSeparated_of_isQuasiSeparated_of_discreteValuativeUniqueness B S hS hX hY f hNoeth
      hft.1 hqs (fun q hq ↦ (hlift q hq).2)
  refine ⟨hsep, hft, ?_⟩
  obtain ⟨I, A, hA, a, φ, -, hLocNoeth, hEtale, hCover⟩ :=
    exists_spec_isLocallyNoetherian_etale_covering_family B S hS hY hNoeth
  refine universallyClosed_of_etale_covering_family B S hS hY f
    (fun i ↦ siteObject B S hS (hA i) (a i)) φ hEtale hCover fun i ↦ ?_
  have := hLocNoeth i
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (siteObject B S hS (hA i) (a i))) :=
    isAlgebraicSpace_yoneda B S hS _
  have hXT : IsAlgebraicSpace B S hS (pullback (φ i) f) :=
    isAlgebraicSpace_pullback B S hS (φ i) f hT hX hY
  have hsepT : IsSeparated B S hS (pullback.fst (φ i) f) :=
    isSeparated_pullback_fst_of_snd B S hS f (φ i)
      (isSeparated_pullback B S hS f (φ i) hsep)
  have hftT : IsFiniteType B S hS (pullback.fst (φ i) f) :=
    IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback (φ i) f) hX hY hft
  obtain ⟨X', ψ, p, hp, hpsurj, hpψ, hqp⟩ :=
    exists_chowSchemeCover_over_spec B S hS (A i) (hA i) (a i) hXT
      (pullback.fst (φ i) f) hsepT hftT
  exact universallyClosed_pullback_fst_of_chowCover B S hS (A i) (hA i) (a i) hX hY f hft
    (fun q hq ↦ (hlift q hq).1) (φ i) X' ψ p hp hpsurj hpψ
    (quasiCompact_of_isHQuasiProjective hqp)

end Core

end AlgebraicGeometry.Space

end
