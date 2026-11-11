module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.ChartIndependence
public import StacksFrontier.Deformation.Artin.FormalObject.Versal

/-!
# Versality of a formal object does not depend on the affine open

Let `ξ = (R, ξ_n, f_n)` be a formal object of a category fibred in groupoids over the big fppf
site of `S`. Its versality (**Stacks 0CXJ**) is versality of the formal object it defines in the
predeformation category `𝓕_{𝒳,k,x₀}` over `𝒞_Λ`, for an affine open `Spec Λ ⊆ S` through which
the closed point of `Spec R` factors (**Stacks 07T2**). The source notes that `𝒞_Λ`, up to
canonical equivalence, does not depend on that affine open. This file proves the consequence for
versality: for two affine opens, the chart-change functor of predeformation categories carries
the formal object defined by `ξ` over the first to the one defined over the second, and it
preserves versality, so the two versality predicates agree.

## Main results

* `Deformation.Artin.FormalObject.exists_affineOpen_factorization`: the structure morphism of
  `Spec R` factors through some affine open of `S`.
* `Deformation.Artin.FormalObject.chartChange_predeformationFormalObject`: the chart change of the
  formal object defined by `ξ` over one affine open is the one defined over the other.
* `Deformation.Artin.FormalObject.isVersal_iff_of_isOpenImmersion`: versality relative to an
  affine open does not depend on the affine open.
* `Deformation.Artin.FormalObject.isVersalOverScheme_iff`,
  `Deformation.Artin.FormalObject.isVersalOverScheme_iff_forall`: **Stacks 0CXJ** is versality
  relative to any given affine open, equivalently to all of them.

## References

* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- Two objects of `CompleteLocalAlgCat` on one carrier, with equal algebra structures and the same
underlying map of residue-field identifications, are equal. -/
private theorem completeLocalAlgCat_mk_eq {Λ k R : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [CommRing R] (hR : IsNoetherianCompleteLocalRing R) (a b : Algebra Λ R)
    (ea : letI := a; letI := hR.isLocal; ResidueField R ≃ₐ[Λ] k)
    (eb : letI := b; letI := hR.isLocal; ResidueField R ≃ₐ[Λ] k)
    (hab : a = b) (he : ∀ x, ea x = eb x) :
    (CompleteLocalAlgCat.mk R (algebra := a) hR ea : CompleteLocalAlgCat.{u, u, u} Λ k) =
      CompleteLocalAlgCat.mk R (algebra := b) hR eb := by
  subst hab
  have : ea = eb := AlgEquiv.ext he
  subst this
  rfl

/-- `rebaseCompleteLocalAlgebra` depends only on the ring map. -/
private theorem rebaseCompleteLocalAlgebra_congr'
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k] [Algebra Λ k] [Algebra Λ' k]
    (A : CompleteLocalAlgCat.{u, u, u} Λ k) (g h : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a)
    (hh : ∀ a : Λ', A.residueEquiv (residue A (h a)) = algebraMap Λ' k a)
    (e : g = h) : rebaseCompleteLocalAlgebra A g hg = rebaseCompleteLocalAlgebra A h hh := by
  subst e
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- **The structure morphism of a formal object factors through an affine open.** For a formal
object `ξ`, there are an affine open `iΛ : Spec Λ ⟶ S` of `S` and a `Λ`-algebra structure on the
complete local base `R` of `ξ` such that `Spec R ⟶ S` is `Spec R ⟶ Spec Λ ⟶ S`. -/
theorem FormalObject.exists_affineOpen_factorization (ξ : FormalObject B S hS p) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (iΛ : Spec (.of Λ) ⟶ S) (_ : IsOpenImmersion iΛ)
      (_ : Algebra Λ ξ.base.R),
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS := by
  let i := S.affineOpenCover.idx (ξ.base.toS (closedPoint ξ.base.R))
  let Λ := (S.affineOpenCover.X i : Type u)
  let iΛ : Spec (.of Λ) ⟶ S := S.affineOpenCover.f i
  have hcov : ξ.base.toS (closedPoint ξ.base.R) ∈ iΛ.opensRange :=
    S.affineOpenCover.covers _
  have hrange : Set.range ξ.base.toS ⊆ Set.range iΛ := by
    have h := Scheme.preimage_eq_top_of_closedPoint_mem ξ.base.toS hcov
    rintro _ ⟨a, rfl⟩
    change a ∈ ξ.base.toS ⁻¹ᵁ iΛ.opensRange
    rw [h]
    trivial
  let l := IsOpenImmersion.lift iΛ ξ.base.toS hrange
  let g : CommRingCat.of Λ ⟶ CommRingCat.of ξ.base.R := Spec.preimage l
  refine ⟨Λ, inferInstance, iΛ, inferInstance, g.hom.toAlgebra, ?_⟩
  change Spec.map (CommRingCat.ofHom g.hom) ≫ iΛ = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac iΛ ξ.base.toS hrange

section ChartChange

variable (ξ : FormalObject B S hS p)
  {Λ Λ' : Type u} [CommRing Λ] [CommRing Λ'] [Algebra Λ ξ.base.R] [Algebra Λ' ξ.base.R]
  (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ']
  (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
  (hR' : Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ.base.R)) ≫ iΛ' = ξ.base.toS)

/-- The complete local base of `ξ` over `Λ`, rebased to `Λ'` along the structure map of `R`, is
its complete local base over `Λ'`. -/
private theorem rebase_completeLocalBase :
    rebaseCompleteLocalAlgebra (ξ.completeLocalBase Λ) (algebraMap Λ' ξ.base.R)
        (fun _ => rfl) = ξ.completeLocalBase Λ' :=
  completeLocalAlgCat_mk_eq (R := ξ.base.R) _ _ _ _ _
    (Algebra.algebra_ext _ _ fun _ => rfl) (fun _ => rfl)

include hR hR' in
/-- The open rebase of the complete local base of `ξ` over `Λ` is its complete local base over
`Λ'`. -/
private theorem completeOpenRebase_completeLocalBase
    (hc : Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' (ResidueField ξ.base.R))) ≫ iΛ') :
    completeOpenRebase iΛ iΛ' inferInstance hc (ξ.completeLocalBase Λ) =
      ξ.completeLocalBase Λ' := by
  have hg : (completeLocalOpenLift_data iΛ iΛ' inferInstance hc
      (ξ.completeLocalBase Λ)).choose = algebraMap Λ' ξ.base.R := by
    have h := (completeLocalOpenLift_data iΛ iΛ' inferInstance hc
      (ξ.completeLocalBase Λ)).choose_spec.2
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective ((cancel_mono iΛ').mp (h.trans (hR.trans hR'.symm))))
  exact (rebaseCompleteLocalAlgebra_congr' _ _ _ _ (fun _ => rfl) hg).trans
    (rebase_completeLocalBase ξ)

include hR' in
/-- **The chart change of the formal object defined by `ξ`.** For two morphisms
`Spec Λ ⟶ S` and `Spec Λ' ⟶ S` through which the structure morphism of `ξ` factors, the second
an open immersion, the chart-change functor of predeformation categories carries the formal
object defined by `ξ` over `𝒞_Λ` to the one defined over `𝒞_{Λ'}`. -/
theorem FormalObject.chartChange_predeformationFormalObject :
    (chartChangeFormalFunctor iΛ iΛ' inferInstance (p ⋙ Over.post B.inclusion) (ξ.level 0)
        (ξ.basePoint Λ iΛ hR) (ξ.basePoint Λ' iΛ' hR')).obj
      (ξ.predeformationFormalObject Λ iΛ hR) = ξ.predeformationFormalObject Λ' iΛ' hR' := by
  let q := p ⋙ Over.post B.inclusion
  let hx₀ := ξ.basePoint Λ iΛ hR
  let hx₀' := ξ.basePoint Λ' iΛ' hR'
  let hc := closedPointCharts_eq iΛ iΛ' q (ξ.level 0) hx₀ hx₀'
  let C := predeformationCategory iΛ q (ξ.level 0) hx₀
  let C' := predeformationCategory iΛ' q (ξ.level 0) hx₀'
  let G := chartChangePredeformationFunctor iΛ iΛ' inferInstance q (ξ.level 0) hx₀ hx₀'
  have hlevel : ∀ n, G.obj (ξ.predeformationLevel Λ iΛ hR n) =
      ξ.predeformationLevel Λ' iΛ' hR' n := by
    intro n
    apply C'.objects.injective
    refine (chartChange_objects iΛ iΛ' inferInstance q (ξ.level 0) hx₀ hx₀'
      (ξ.predeformationLevel Λ iΛ hR n)).trans ?_
    change rebaseDeformationObject iΛ iΛ' inferInstance q (ξ.level 0) hx₀ hx₀'
        (ξ.predeformationLevel Λ iΛ hR n) = ξ.predeformationLevel Λ' iΛ' hR' n
    apply deformationObject_ext
    · refine (rebaseDeformationObject_algebra_eq_canonical iΛ iΛ' inferInstance q (ξ.level 0)
        hx₀ hx₀' (ξ.predeformationLevel Λ iΛ hR n)).trans ?_
      refine (rebaseArtinianCanonical_truncation iΛ iΛ' inferInstance hc
        (ξ.completeLocalBase Λ) (algebraMap Λ' ξ.base.R) (fun _ => rfl)
        (hR.trans hR'.symm) n).trans ?_
      exact congrArg (fun A => AdicTruncation.obj A n) (rebase_completeLocalBase ξ)
    · rfl
    · rfl
  refine Deformation.FormalObject.ext ?_ hlevel ?_
  · exact completeOpenRebase_completeLocalBase ξ iΛ iΛ' hR hR' hc
  · intro n
    apply (C'.morphisms _ _).injective
    apply deformationMorphism_ext_arrow
    refine (chartChange_arrow iΛ iΛ' inferInstance q (ξ.level 0) hx₀ hx₀'
      (ξ.predeformationTransition Λ iΛ hR n)).trans ?_
    have e : ∀ {a b : C'.carrier} (h : a = b), (C'.morphisms a b (eqToHom h)).arrow =
        eqToHom (congrArg (fun z => (C'.objects z).point) h).symm := by
      intro a b h
      cases h
      exact C'.reversed_identity a
    rw [C'.reversed_composition, C'.reversed_composition, e]
    refine Eq.trans ?_ (congrArg (fun t => _ ≫ t) (e (hlevel (n + 1)))).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    rfl

end ChartChange

section Independence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (ξ : FormalObject B S hS p)

/-- Versality relative to one affine open gives versality relative to another. -/
private theorem FormalObject.isVersal_of_isOpenImmersion
    {Λ Λ' : Type u} [CommRing Λ] [CommRing Λ'] [Algebra Λ ξ.base.R] [Algebra Λ' ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ]
    [IsOpenImmersion iΛ']
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hR' : Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ.base.R)) ≫ iΛ' = ξ.base.toS)
    (h : FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR) :
    FormalObject.IsVersal B S hS p hp ξ Λ' iΛ' hR' := by
  have hv := isVersal_chartChange iΛ iΛ' inferInstance inferInstance
    (p ⋙ Over.post B.inclusion) (ξ.level 0) (ξ.basePoint Λ iΛ hR) (ξ.basePoint Λ' iΛ' hR')
    (predeformationCategory_isPredeformationCategory B hS iΛ p (ξ.level 0)
      (ξ.basePoint Λ iΛ hR) hp).cofibered
    (predeformationCategory_isPredeformationCategory B hS iΛ' p (ξ.level 0)
      (ξ.basePoint Λ' iΛ' hR') hp).cofibered
    (ξ.predeformationFormalObject Λ iΛ hR) h
  rw [ξ.chartChange_predeformationFormalObject iΛ iΛ' hR hR'] at hv
  exact hv

/-- **Versality does not depend on the affine open.** For two affine opens `Spec Λ ⊆ S` and
`Spec Λ' ⊆ S` through which the structure morphism of `ξ` factors, `ξ` is versal relative to
`Λ` exactly when it is versal relative to `Λ'`. This is the independence of the choice of the
affine open in **Stacks 07T2**, read on the versality of **Stacks 0CXJ**. -/
theorem FormalObject.isVersal_iff_of_isOpenImmersion
    {Λ Λ' : Type u} [CommRing Λ] [CommRing Λ'] [Algebra Λ ξ.base.R] [Algebra Λ' ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S) [IsOpenImmersion iΛ]
    [IsOpenImmersion iΛ']
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hR' : Spec.map (CommRingCat.ofHom (algebraMap Λ' ξ.base.R)) ≫ iΛ' = ξ.base.toS) :
    FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR ↔
      FormalObject.IsVersal B S hS p hp ξ Λ' iΛ' hR' :=
  ⟨FormalObject.isVersal_of_isOpenImmersion B S hS p hp ξ iΛ iΛ' hR hR',
    FormalObject.isVersal_of_isOpenImmersion B S hS p hp ξ iΛ' iΛ hR' hR⟩

/-- **Stacks 0CXJ** is versality relative to any given affine open `Spec Λ ⊆ S` through which
the structure morphism of `ξ` factors. -/
theorem FormalObject.isVersalOverScheme_iff
    {Λ : Type u} [CommRing Λ] [Algebra Λ ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS) :
    FormalObject.IsVersalOverScheme B S hS p hp ξ ↔
      FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR := by
  constructor
  · rintro ⟨Λ', _, iΛ', _, _, hR', h⟩
    exact (FormalObject.isVersal_iff_of_isOpenImmersion B S hS p hp ξ iΛ' iΛ hR' hR).mp h
  · intro h
    exact ⟨Λ, inferInstance, iΛ, inferInstance, inferInstance, hR, h⟩

/-- **Stacks 0CXJ** is versality relative to every affine open `Spec Λ ⊆ S` through which the
structure morphism of `ξ` factors. -/
theorem FormalObject.isVersalOverScheme_iff_forall :
    FormalObject.IsVersalOverScheme B S hS p hp ξ ↔
      ∀ (Λ : Type u) (_ : CommRing Λ) (iΛ : Spec (.of Λ) ⟶ S) (_ : IsOpenImmersion iΛ)
        (_ : Algebra Λ ξ.base.R)
        (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS),
        FormalObject.IsVersal B S hS p hp ξ Λ iΛ hR := by
  constructor
  · intro h Λ _ iΛ _ _ hR
    exact (FormalObject.isVersalOverScheme_iff B S hS p hp ξ iΛ hR).mp h
  · intro h
    obtain ⟨Λ, _, iΛ, _, _, hR⟩ := ξ.exists_affineOpen_factorization
    exact ⟨Λ, inferInstance, iΛ, inferInstance, inferInstance, hR, h Λ _ iΛ ‹_› _ hR⟩

end Independence

end Deformation.Artin

end
