module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient

/-!
# Detecting essential surjections modulo squares of the maximal ideal

A surjection `f : B → A` of `𝒞_Λ` is essential exactly when the morphism it induces on the
quotients by the squares of the maximal ideals is essential, and exactly when the morphism it
induces on the quotients by `m_Λ · + m²` is essential (Stacks 06S5). Here `m_Λ` is the kernel
of the fixed map `Λ → k`.

Both equivalences come from one argument, applied to the two assignments of an ideal
`Q A ⊆ m_A` to each object. Forwards, a morphism `g : C → B` whose composite with the induced
map is surjective is handled by pulling `g` back along the projection `B → B/Q B`: the pullback
exists because that projection is surjective, its first projection is surjective, and the
induced map out of the pullback is surjective, so essentiality of `f` applies. Backwards, one
only needs that surjectivity of the induced map implies surjectivity of the original, which is
the cotangent-space criterion for surjectivity.

## Main results

* `Deformation.ArtinianLocalAlgCat.essentialSurjection_iff_mod_maximalIdeal_sq`: essentiality
  is detected modulo `m²`.
* `Deformation.ArtinianLocalAlgCat.essentialSurjection_iff_mod_relative_maximalIdeal_sq`:
  essentiality is detected on the relative cotangent quotient.
* `Deformation.ArtinianLocalAlgCat.baseKernel_map_le_maximalIdeal`: the image of `m_Λ` lies in
  the maximal ideal of any object.
* `Deformation.ArtinianLocalAlgCat.relativeCotangentIdeal_le_maximalIdeal` and
  `Deformation.ArtinianLocalAlgCat.relativeCotangentIdeal_le_comap`: the hypotheses needed to
  form the relative quotient and the morphism between two of them.

## Implementation notes

All quotient objects are the literal ideal quotients of
`StacksFrontier.Deformation.BaseCategory.IdealQuotient`, not arbitrary presentations, so the
statements say something about a specific object rather than about one chosen up to
isomorphism. The step from surjectivity of an induced quotient map back to surjectivity of the
original morphism is where the two cases differ: modulo `m²` it is the cotangent criterion
directly, and modulo `m_Λ · + m²` it is that criterion composed with the comparison of the
absolute and relative cotangent spaces.

## References

* [Stacks Project, Tag 06S5](https://stacks.math.columbia.edu/tag/06S5)
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

section
open CategoryTheory IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The ideal `m_Λ A + m_A²`, whose quotient out of `m_A` is the relative cotangent space. -/
private def relativeCotangentIdeal (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : Ideal A :=
  (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2

/-- The image of the base residue kernel lies in the maximal ideal of any object. -/
theorem baseKernel_map_le_maximalIdeal (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) ≤ maximalIdeal A := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, ← ker_residue, RingHom.mem_ker]
  apply A.residueEquiv.injective
  calc
    A.residueEquiv (residue A (algebraMap Λ A r)) = algebraMap Λ k r := by
      rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact A.residueEquiv.commutes r
    _ = 0 := hr
    _ = A.residueEquiv 0 := by simp

/-- The ideal of the relative cotangent quotient is contained in the maximal ideal. -/
theorem relativeCotangentIdeal_le_maximalIdeal (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2 ≤
      maximalIdeal A :=
  add_le (baseKernel_map_le_maximalIdeal A) (Ideal.pow_le_self two_ne_zero)

/-- The square of the maximal ideal is preserved by morphisms. -/
private theorem maximalIdeal_sq_le_comap {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    maximalIdeal B ^ 2 ≤ (maximalIdeal A ^ 2).comap f.hom := by
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le f.hom.toRingHom) _

/-- The ideal defining the relative quotient is preserved by morphisms. -/
theorem relativeCotangentIdeal_le_comap
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ B) + maximalIdeal B ^ 2 ≤
      ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) +
        maximalIdeal A ^ 2).comap f.hom := by
  apply add_le
  · rw [← Ideal.map_le_iff_le_comap]
    change ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ B)).map f.hom.toRingHom ≤ _
    calc
      _ = (RingHom.ker (algebraMap Λ k)).map
          (f.hom.toRingHom.comp (algebraMap Λ B)) := Ideal.map_map _ _
      _ = (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) := by
        congr 1
        exact RingHom.ext f.hom.commutes
      _ ≤ _ := le_sup_left
  · exact (maximalIdeal_sq_le_comap f).trans (Ideal.comap_mono le_sup_right)

/-- The preimage of the maximal ideal under a morphism is the maximal ideal. -/
private theorem comap_maximalIdeal_eq {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    (maximalIdeal A).comap f.hom = maximalIdeal B := by
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  exact maximalIdeal_comap f.hom.toRingHom

/-- If an induced quotient map is surjective, every element of `m_A` is congruent modulo the
target ideal to the image of an element of `m_B`. -/
private theorem exists_maximalIdeal_lift_of_idealQuotientMap_surjective
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) {QB : Ideal B} {QA : Ideal A}
    (hB : QB ≤ maximalIdeal B) (hA : QA ≤ maximalIdeal A) (hmap : QB ≤ QA.comap f.hom)
    (hf : Function.Surjective (idealQuotientMap f QB QA hB hA hmap).hom)
    {a : A} (ha : a ∈ maximalIdeal A) :
    ∃ b : B, b ∈ maximalIdeal B ∧ f.hom b - a ∈ QA := by
  obtain ⟨x, hx⟩ := hf (Ideal.Quotient.mk QA a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hdiff : f.hom b - a ∈ QA := Ideal.Quotient.eq.mp hx
  refine ⟨b, ?_, hdiff⟩
  rw [← comap_maximalIdeal_eq f, Ideal.mem_comap, ← sub_add_cancel (f.hom b) a]
  exact add_mem (hA hdiff) ha

/-- Surjectivity of the morphism induced on the relative cotangent quotients implies
surjectivity of the morphism itself. -/
private theorem idealQuotientMap_relative_surjective_implies_surjective
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hB : relativeCotangentIdeal B ≤ maximalIdeal B)
    (hA : relativeCotangentIdeal A ≤ maximalIdeal A)
    (hmap : relativeCotangentIdeal B ≤ (relativeCotangentIdeal A).comap f.hom)
    (hf : Function.Surjective
      (idealQuotientMap f (relativeCotangentIdeal B) (relativeCotangentIdeal A)
        hB hA hmap).hom) :
    Function.Surjective f.hom := by
  have hrel : Function.Surjective (relativeCotangentSpaceMap f) := by
    intro z
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (relativeCotangentSubmodule A) z
    obtain ⟨b, hb, hdiff⟩ :=
      exists_maximalIdeal_lift_of_idealQuotientMap_surjective f hB hA hmap hf a.2
    refine ⟨Submodule.mkQ (relativeCotangentSubmodule B) ⟨b, hb⟩, ?_⟩
    change Submodule.mkQ (relativeCotangentSubmodule A)
        (maximalIdealMap f ⟨b, hb⟩) = Submodule.mkQ _ ⟨a, a.2⟩
    exact (Submodule.Quotient.eq _).mpr hdiff
  exact (surjective_iff_cotangentSpaceMap_surjective f).2
    ((cotangentSpaceMap_surjective_iff_relativeCotangentSpaceMap_surjective f).2 hrel)

/-- Surjectivity of the morphism induced modulo the squares of the maximal ideals implies
surjectivity of the morphism itself. -/
private theorem idealQuotientMap_maximalSq_surjective_implies_surjective
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hB : maximalIdeal B ^ 2 ≤ maximalIdeal B)
    (hA : maximalIdeal A ^ 2 ≤ maximalIdeal A)
    (hmap : maximalIdeal B ^ 2 ≤ (maximalIdeal A ^ 2).comap f.hom)
    (hf : Function.Surjective
      (idealQuotientMap f (maximalIdeal B ^ 2) (maximalIdeal A ^ 2) hB hA hmap).hom) :
    Function.Surjective f.hom := by
  have hcot : Function.Surjective (Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) f.hom
      (comap_maximalIdeal_eq f).ge) := by
    intro z
    obtain ⟨a, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
    obtain ⟨b, hb, hdiff⟩ :=
      exists_maximalIdeal_lift_of_idealQuotientMap_surjective f hB hA hmap hf a.2
    refine ⟨(maximalIdeal B).toCotangent ⟨b, hb⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    exact (maximalIdeal A).toCotangent_eq.mpr hdiff
  exact (surjective_iff_cotangentSpaceMap_surjective f).2 hcot

private theorem isEssentialSurjection_idealQuotientMap_of_isEssentialSurjection
    (Q : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k, Ideal A)
    (hQ : ∀ A, Q A ≤ maximalIdeal A)
    (hQmap : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Q B ≤ (Q A).comap f.hom)
    (hLift : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Function.Surjective (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)).hom →
        Function.Surjective f.hom)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : IsEssentialSurjection f) :
    IsEssentialSurjection (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)) := by
  let qf := idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)
  let qB := idealQuotientProjection B (Q B) (hQ B)
  let qA := idealQuotientProjection A (Q A) (hQ A)
  refine ⟨idealQuotientMap_surjective f (Q B) (Q A) (hQ B) (hQ A) (hQmap f) hf.1,
    fun {C} g hg => ?_⟩
  have hqBsurj : Function.Surjective qB.hom := Ideal.Quotient.mk_surjective
  let pObj := pullbackObj_of_surjective g qB (Or.inr hqBsurj)
  let qP := idealQuotientProjection pObj (Q pObj) (hQ pObj)
  let pC := pullbackFst_of_surjective g qB (Or.inr hqBsurj)
  let pB := pullbackSnd_of_surjective g qB (Or.inr hqBsurj)
  have hpb := isPullback_of_surjective g qB (Or.inr hqBsurj)
  have hpC : Function.Surjective pC.hom := by
    rw [pullbackFst_of_surjective_hom]
    exact AlgHom.surjective_pullbackFst_of_surjective g.hom qB.hom
      Ideal.Quotient.mk_surjective
  have hqAcomp : qB ≫ qf = f ≫ qA :=
    idealQuotientProjection_comp_idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)
  let r := idealQuotientMap (pB ≫ f) (Q pObj) (Q A) (hQ pObj) (hQ A) (hQmap (pB ≫ f))
  have hrEq : qP ≫ r = pC ≫ g ≫ qf := by
    rw [(idealQuotientProjection_comp_idealQuotientMap (pB ≫ f) (Q pObj) (Q A)
      (hQ pObj) (hQ A) (hQmap (pB ≫ f)) : qP ≫ r = (pB ≫ f) ≫ qA), Category.assoc,
      ← hqAcomp, ← Category.assoc, ← hpb.w, Category.assoc]
  have hr : Function.Surjective r.hom := by
    intro y
    obtain ⟨z, rfl⟩ := hg y
    obtain ⟨x, rfl⟩ := hpC z
    exact ⟨qP.hom x, congrArg (fun t => t.hom x) hrEq⟩
  intro y
  obtain ⟨b, hb⟩ := hqBsurj y
  obtain ⟨x, hx⟩ := hf.2 pB (hLift (pB ≫ f) hr) b
  refine ⟨pC.hom x, ?_⟩
  have hw' : g.hom (pC.hom x) = qB.hom (pB.hom x) := by
    simpa only [comp_hom, AlgHom.comp_apply] using congrArg (fun t => t.hom x) hpb.w
  rw [hw', hx, hb]

private theorem isEssentialSurjection_of_isEssentialSurjection_idealQuotientMap
    (Q : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k, Ideal A)
    (hQ : ∀ A, Q A ≤ maximalIdeal A)
    (hQmap : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Q B ≤ (Q A).comap f.hom)
    (hLift : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Function.Surjective (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)).hom →
        Function.Surjective f.hom)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hq : IsEssentialSurjection (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f))) :
    IsEssentialSurjection f := by
  refine ⟨hLift f hq.1, fun {C} g hg => ?_⟩
  let qg := idealQuotientMap g (Q C) (Q B) (hQ C) (hQ B) (hQmap g)
  have heq : qg ≫ idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f) =
      idealQuotientMap (g ≫ f) (Q C) (Q A) (hQ C) (hQ A) (hQmap (g ≫ f)) := by
    apply hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  refine hLift g (hq.2 qg ?_)
  rw [heq]
  exact idealQuotientMap_surjective (g ≫ f) (Q C) (Q A) (hQ C) (hQ A) (hQmap (g ≫ f)) hg

/-- The common argument for both criteria: for any assignment `Q` of an ideal inside the
maximal ideal to each object which is preserved by morphisms and for which surjectivity of the
induced quotient map implies surjectivity, essentiality of a morphism is equivalent to
essentiality of the induced morphism of quotients. -/
private theorem isEssentialSurjection_iff_idealQuotientMap
    (Q : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k, Ideal A)
    (hQ : ∀ A, Q A ≤ maximalIdeal A)
    (hQmap : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Q B ≤ (Q A).comap f.hom)
    (hLift : ∀ {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A),
      Function.Surjective (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)).hom →
        Function.Surjective f.hom)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔
      IsEssentialSurjection (idealQuotientMap f (Q B) (Q A) (hQ B) (hQ A) (hQmap f)) :=
  ⟨isEssentialSurjection_idealQuotientMap_of_isEssentialSurjection Q hQ hQmap hLift f,
    isEssentialSurjection_of_isEssentialSurjection_idealQuotientMap Q hQ hQmap hLift f⟩

/-- Essential surjectivity is detected modulo the maximal-ideal squares. -/
@[stacks 06S5 "conditions (1) and (2)"]
theorem essentialSurjection_iff_mod_maximalIdeal_sq
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    let IB := maximalIdeal B ^ 2
    let IA := maximalIdeal A ^ 2
    let hB : IB ≤ maximalIdeal B := Ideal.pow_le_self (by omega : 2 ≠ 0)
    let hA : IA ≤ maximalIdeal A := Ideal.pow_le_self (by omega : 2 ≠ 0)
    let hmap : IB ≤ IA.comap f.hom := by
      let _ : IsLocalHom f.hom.toRingHom := f.isLocal
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (map_maximalIdeal_le f.hom.toRingHom) _
    IsEssentialSurjection f ↔
    IsEssentialSurjection (idealQuotientMap f IB IA hB hA hmap) :=
  isEssentialSurjection_iff_idealQuotientMap (fun A => maximalIdeal A ^ 2)
    (fun _ => Ideal.pow_le_self two_ne_zero) maximalIdeal_sq_le_comap
    (fun g hg => idealQuotientMap_maximalSq_surjective_implies_surjective g
      (Ideal.pow_le_self two_ne_zero) (Ideal.pow_le_self two_ne_zero)
      (maximalIdeal_sq_le_comap g) hg) f

/-- Essential surjectivity is detected on the relative cotangent quotient. -/
@[stacks 06S5 "conditions (1) and (3)"]
theorem essentialSurjection_iff_mod_relative_maximalIdeal_sq
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔
      IsEssentialSurjection
        (idealQuotientMap f
          ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ B) + maximalIdeal B ^ 2)
          ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2)
          (relativeCotangentIdeal_le_maximalIdeal B)
          (relativeCotangentIdeal_le_maximalIdeal A)
          (relativeCotangentIdeal_le_comap f)) :=
  isEssentialSurjection_iff_idealQuotientMap relativeCotangentIdeal
    relativeCotangentIdeal_le_maximalIdeal relativeCotangentIdeal_le_comap
    (fun g hg => idealQuotientMap_relative_surjective_implies_surjective g
      (relativeCotangentIdeal_le_maximalIdeal _) (relativeCotangentIdeal_le_maximalIdeal _)
      (relativeCotangentIdeal_le_comap g) hg) f

end

end ArtinianLocalAlgCat

end Deformation

end
