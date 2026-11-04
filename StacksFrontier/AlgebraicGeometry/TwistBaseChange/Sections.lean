module

public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.Fibre
public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Basic

/-!
# The comparison on sections of the twists, for a graded localization away from degree zero

Let `ψ : 𝒜 →+*ᵍ ℬ` exhibit `B` as a localization of `A` away from an element `g` of degree `0`,
let `U(ψ) ⊆ Proj ℬ` be the domain of definition of the induced morphism and
`mapHom : U(ψ) ⟶ Proj 𝒜` that morphism. This file treats
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`, the comparison on sections of the
`n`-th twists, over an open of `Proj 𝒜`: it is injective when the open lies inside the range of
`mapHom`, and it is surjective near every point of the image.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistBaseChange.indexMap`: the reindexing of points that the
  comparison on sections performs.
* `Stacks.AlgebraicGeometry.TwistBaseChange.FractionLift`: the property that homogeneous
  fractions lift along `ψ` at every point of `U(ψ)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistBaseChange.surjective_indexMap`: the reindexing is surjective
  on an open contained in the range of `mapHom`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.injective_twistSection`: the comparison on sections
  is injective over an open contained in the range.
* `Stacks.AlgebraicGeometry.TwistBaseChange.fractionLift_of_isLocalizationAway`: a graded
  localization away from a degree-zero element lifts fractions.
* `Stacks.AlgebraicGeometry.TwistBaseChange.exists_fractionSection_eq`: near the image of a point
  of `U(ψ)`, a section of the `n`-th twist on `Proj ℬ` is the comparison of a section of the
  `n`-th twist on `Proj 𝒜`.

## Implementation notes

Sections of a twisting sheaf over an open are families of homogeneous fractions indexed by the
points of that open, so the comparison on sections is the fibre comparison applied pointwise
after the reindexing `indexMap`. The fibre at a point depends on the point, so a value cannot be
transported along an equality of points by `congrArg`; instead `Function.Surjective.forall`
turns a statement about every point of the open into one about every point of `U(ψ)` over it,
where both sides are indexed by the same term.

The opens are spelled `Opens (ProjectiveSpectrum.top 𝒜)` in `exists_fractionSection_eq` and
`(AlgebraicGeometry.Proj 𝒜).Opens` in the others: the two are interchangeable only through the
local `implicit_reducible` attributes, and
`Stacks.AlgebraicGeometry.ProjTwistEpi.fractionSection_val` rewrites only at the first. For the
same reason the conclusion of `exists_fractionSection_eq` is written with the anonymous
constructor `⟨basePoint …, liftPt_mem …⟩` rather than with `indexMap`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistEpi
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.TwistBaseChange

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### Reindexing the points -/

/-- The reindexing of points: a point of `Proj ℬ` lying over an open `U` of `Proj 𝒜`, read as a
point of `U` through the induced morphism. -/
public def indexMap (ψ : 𝒜 →+*ᵍ ℬ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) : ↥U :=
  ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩

/-- The comparison on sections, written with `indexMap`. -/
public theorem twistSection_val' (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 n).val.obj (.op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    (twistSection 𝒜 ℬ ψ n U a).1 z =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) (a.1 (indexMap 𝒜 ℬ ψ U z)) := rfl

/-- Every point of an open of `Proj 𝒜` contained in the range of the induced morphism is the
image of a point of `U(ψ)` lying over that open. -/
public theorem surjective_indexMap (ψ : 𝒜 →+*ᵍ ℬ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (hU : (U : Set (AlgebraicGeometry.Proj 𝒜)) ⊆ Set.range (mapHom 𝒜 ℬ ψ).base) :
    Function.Surjective (indexMap 𝒜 ℬ ψ U) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hU hx
  have hyU : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U := show (mapHom 𝒜 ℬ ψ).base y ∈ U from hy ▸ hx
  refine ⟨⟨(y.1 : AlgebraicGeometry.Proj ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyU⟩, ?_⟩
  refine Subtype.ext ?_
  show basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ _) = x
  have hlift : liftPt 𝒜 ℬ ψ
      (⟨(y.1 : AlgebraicGeometry.Proj ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyU⟩ :
        ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) = y := Subtype.ext rfl
  rwa [hlift]

/-! ### Injectivity on sections -/

/-- The comparison on sections of the `n`-th twists is injective over an open of `Proj 𝒜`
contained in the range of the induced morphism. -/
public theorem injective_twistSection (ψ : 𝒜 →+*ᵍ ℬ) (g : A) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (hU : (U : Set (AlgebraicGeometry.Proj 𝒜)) ⊆ Set.range (mapHom 𝒜 ℬ ψ).base) :
    Function.Injective (twistSection 𝒜 ℬ ψ n U) := by
  intro a a' haa
  refine Subtype.ext (funext ?_)
  refine (surjective_indexMap 𝒜 ℬ ψ U hU).forall.mpr fun z => ?_
  have hz : (twistSection 𝒜 ℬ ψ n U a).1 z = (twistSection 𝒜 ℬ ψ n U a').1 z :=
    congrFun (congrArg Subtype.val haa) z
  rw [twistSection_val', twistSection_val'] at hz
  exact (bijective_twistFibreMap 𝒜 ℬ ψ g halg (liftPt 𝒜 ℬ ψ z)).1 hz

/-! ### Local surjectivity on sections -/

/-- At every point of `U(ψ)`, a homogeneous fraction `b / s` of twisted degree `K` over `ℬ` whose
denominator does not vanish at that point is the `ψ`-image of a homogeneous fraction `β / c` of
the same twisted degree `K` over `𝒜` whose denominator does not vanish there either. -/
public def FractionLift (ψ : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∀ (y : (mapDomain 𝒜 ℬ ψ).toScheme) (m : ℤ) (K : ℕ) (b s : B),
    b ∈ twistGrading (S := B) ℬ m (K : ℤ) → s ∈ ℬ K →
    s ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal →
    ∃ β c : A, β ∈ twistGrading (S := A) 𝒜 m (K : ℤ) ∧ c ∈ 𝒜 K ∧
      ψ c ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal ∧ s * ψ β = ψ c * b

/-- A graded localization away from a degree-zero element lifts fractions. -/
public theorem fractionLift_of_isLocalizationAway (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0)
    [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    FractionLift 𝒜 ℬ ψ := by
  intro y m K b s hb hs hsy
  obtain ⟨β, c, p, hβ, hc, hcs, hfrac⟩ := exists_fraction_lift 𝒜 ℬ ψ hg halg m K hb hs
  refine ⟨β, c, hβ, hc, ?_, hfrac⟩
  rw [hcs]
  exact notMem_of_isUnit_mul ((isUnit_of_isLocalizationAway 𝒜 ℬ ψ g halg).pow p) hsy

/-- If fractions lift along `ψ` and `mapHom` is inducing, then near the image of any point of
`U(ψ)`, a section of the `n`-th twist on `Proj ℬ` over the image of `mapHom ⁻¹ᵁ U` is the
comparison of a section of the `n`-th twist on `Proj 𝒜`. -/
public theorem exists_fractionSection_eq (ψ : 𝒜 →+*ᵍ ℬ) (hlift : FractionLift 𝒜 ℬ ψ)
    (hind : Topology.IsInducing (mapHom 𝒜 ℬ ψ).base) (n : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf ℬ n).val.obj
      (.op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))))
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) (hyU : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) :
    ∃ V : Opens (ProjectiveSpectrum.top 𝒜), V ≤ U ∧ (mapHom 𝒜 ℬ ψ).base y ∈ V ∧
      ∃ s : (twistingSheaf 𝒜 n).val.obj (.op V),
        ∀ (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V)))
          (hz : (z.1 : AlgebraicGeometry.Proj ℬ) ∈
            (mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)),
          twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
              (s.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) =
            t.1 ⟨(z.1 : AlgebraicGeometry.Proj ℬ), hz⟩ := by
  obtain ⟨V₀, hz₀V₀, i₀, k, b, s₀, hb, hs₀, hns₀, heq⟩ :=
    t.2 ⟨(y.1 : AlgebraicGeometry.Proj ℬ), mem_image_of_mem 𝒜 ℬ ψ y hyU⟩
  have hs₀y : s₀ ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal :=
    hns₀ ⟨(y.1 : AlgebraicGeometry.Proj ℬ), hz₀V₀⟩
  obtain ⟨β, c, hβ, hc, hψc, hfrac⟩ := hlift y n k b s₀ hb hs₀ hs₀y
  have hcnm : c ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal :=
    notMem_base_of_notMem 𝒜 ℬ ψ hc y hψc
  obtain ⟨W₀, hW₀⟩ := exists_preimage_opens_of_isInducing (mapHom 𝒜 ℬ ψ) hind
    ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V₀)
  have hyW₀ : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ W₀ := by rw [hW₀]; exact hz₀V₀
  have hnv : ∀ w : (W₀ ⊓ U ⊓ Proj.basicOpen 𝒜 c : Opens (ProjectiveSpectrum.top 𝒜)),
      c ∉ w.1.asHomogeneousIdeal := fun w => (Proj.mem_basicOpen 𝒜 c w.1).mp w.2.2
  refine ⟨W₀ ⊓ U ⊓ Proj.basicOpen 𝒜 c, inf_le_left.trans inf_le_right,
    ⟨⟨hyW₀, hyU⟩, (Proj.mem_basicOpen 𝒜 c _).mpr hcnm⟩,
    fractionSection 𝒜 n hβ hc hnv, fun z hz => ?_⟩
  have hzV₀ : (z.1 : AlgebraicGeometry.Proj ℬ) ∈ V₀ := by
    obtain ⟨wz, hwz, hwe⟩ := z.2
    have hw : wz ∈ (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ V₀ := by rw [← hW₀]; exact hwz.1.1
    exact hwe ▸ hw
  have hψcz : ψ c ∉ (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal :=
    notMem_of_notMem 𝒜 ℬ ψ hc (liftPt 𝒜 ℬ ψ z)
      (hnv ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)
  rw [fractionSection_val, twistFibreMap_mk 𝒜 ℬ ψ _ β c _ hψcz]
  refine Eq.trans ?_ (heq ⟨(z.1 : AlgebraicGeometry.Proj ℬ), hzV₀⟩).symm
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul]
  show s₀ • ψ β = ψ c • b
  rw [smul_eq_mul, smul_eq_mul]
  exact hfrac

end Stacks.AlgebraicGeometry.TwistBaseChange

end
