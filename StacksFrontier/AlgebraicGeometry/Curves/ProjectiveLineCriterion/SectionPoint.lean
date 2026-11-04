module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A section of a smooth separated scheme over a field gives a normal rational point

Let `f : X ⟶ Spec k` be separated and let `s : Spec k ⟶ X` be a section, `s ≫ f = 𝟙`. The image
`z` of the point of `Spec k` is a closed point of `X` (a section of a separated morphism is a
closed immersion) whose residue field is `k` (the composite `k → κ(z) → k` is the identity). If
`f` is smooth, the local ring of `X` at `z` is regular, hence normal. So `X` satisfies the point
condition of item (8) of [Stacks, Tag 0C6U] with a single point of residue degree `1`.

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.isClosed_singleton_of_section`
* `AlgebraicGeometry.ProjectiveLineCriterion.finrank_residueField_of_section`
* `AlgebraicGeometry.ProjectiveLineCriterion.isNormalRing_stalk_of_smooth`
* `AlgebraicGeometry.ProjectiveLineCriterion.normalRationalPoint_of_section`
* `AlgebraicGeometry.ProjectiveLineCriterion.exists_normalPoints_gcd_eq_one_of_section`

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The image of a section of a separated scheme over a field is a closed point.** -/
@[sga "1 II 4.17" "special case"]
theorem isClosed_singleton_of_section [IsSeparated f] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) (p : Spec (.of k)) : IsClosed ({s p} : Set X) := by
  have := Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section f s hs
  have hr : Set.range s = {s p} := by
    ext y
    refine ⟨?_, fun hy => ⟨p, hy.symm⟩⟩
    rintro ⟨q, rfl⟩
    rw [Subsingleton.elim q p]
    rfl
  rw [← hr]
  exact s.isClosedEmbedding.isClosed_range

/-- **The image of a section of a scheme over a field is a rational point**: its residue field
has degree one over `k`. The structure map `k → κ(s p)` followed by the residue field map
`κ(s p) → κ(p) = k` of the section is the identity, so `k → κ(s p)` is surjective. -/
theorem finrank_residueField_of_section (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (p : Spec (.of k)) :
    letI : Algebra k (X.residueField (s p)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (s p)).hom.toAlgebra
    Module.finrank k (X.residueField (s p)) = 1 := by
  let : Algebra k (X.residueField (s p)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (s p)).hom.toAlgebra
  -- `c ↦ c(p)` is surjective onto `κ(p)`
  have hSpec : Function.Surjective (fun c : k =>
      (Spec (.of k)).Γevaluation p ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := by
    have hmax : p.asIdeal.IsMaximal := by
      have := p.isPrime
      rw [show p.asIdeal = ⊥ from Ideal.eq_bot_of_prime _]; exact Ideal.bot_isMaximal
    intro y
    obtain ⟨c, hc⟩ := Ideal.algebraMap_residueField_surjective p.asIdeal
      ((Scheme.Spec.residueFieldIso (.of k) p).hom y)
    refine ⟨c, ?_⟩
    have h := ConcreteCategory.congr_hom (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) p) c
    change (Scheme.Spec.residueFieldIso (.of k) p).inv (algebraMap k _ c) = _ at h
    rw [hc, Iso.hom_inv_id_apply] at h
    exact h.symm
  -- and it factors through `κ(s p)`
  have hnat : ∀ c : k, (s.residueFieldMap p).hom (algebraMap k (X.residueField (s p)) c) =
      (Spec (.of k)).Γevaluation p ((Scheme.ΓSpecIso (.of k)).inv.hom c) := by
    intro c
    rw [RingHom.algebraMap_toAlgebra]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    have hid : ∀ a, s.appTop.hom (f.appTop.hom a) = a := fun a => by
      have := ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop s f) a
      rw [hs, Scheme.Hom.id_appTop] at this
      exact this.symm
    rw [Scheme.Γevaluation_naturality_apply (f := s) p, hid]
  have hsurj : Function.Surjective (algebraMap k (X.residueField (s p))) := by
    intro y
    obtain ⟨c, hc⟩ := hSpec ((s.residueFieldMap p).hom y)
    refine ⟨c, (s.residueFieldMap p).hom.injective ?_⟩
    rw [hnat]; exact hc
  have e : k ≃ₐ[k] X.residueField (s p) :=
    AlgEquiv.ofBijective (Algebra.ofId k _) ⟨(algebraMap k _).injective, hsurj⟩
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **The local rings of a scheme smooth over a field are normal**: they are regular local rings,
hence integrally closed domains. -/
theorem isNormalRing_stalk_of_smooth [Smooth f] (x : X) :
    IsNormalRing (X.presheaf.stalk x) := by
  have := isRegularLocalRing_stalk_of_smooth_over_field f x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  exact IsNormalRing.of_isIntegrallyClosed _

/-- **A section of a separated scheme over `k` with normal local rings gives a normal rational
closed point**: the image `s p` is closed, `𝒪_{X, s p}` is normal and `[κ(s p) : k] = 1`. -/
theorem normalRationalPoint_of_section_of_isNormalRing [IsSeparated f]
    (hnorm : ∀ x : X, IsNormalRing (X.presheaf.stalk x)) (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) (p : Spec (.of k)) :
    IsClosed ({s p} : Set X) ∧ IsNormalRing (X.presheaf.stalk (s p)) ∧
      letI : Algebra k (X.residueField (s p)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (s p)).hom.toAlgebra
      Module.finrank k (X.residueField (s p)) = 1 :=
  ⟨isClosed_singleton_of_section f s hs p, hnorm _, finrank_residueField_of_section f s hs p⟩

/-- **A section of a smooth separated scheme over `k` gives a normal rational closed point**:
the image `s p` is closed, `𝒪_{X, s p}` is normal and `[κ(s p) : k] = 1`. -/
theorem normalRationalPoint_of_section [IsSeparated f] [Smooth f] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) (p : Spec (.of k)) :
    IsClosed ({s p} : Set X) ∧ IsNormalRing (X.presheaf.stalk (s p)) ∧
      letI : Algebra k (X.residueField (s p)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (s p)).hom.toAlgebra
      Module.finrank k (X.residueField (s p)) = 1 :=
  normalRationalPoint_of_section_of_isNormalRing f (isNormalRing_stalk_of_smooth f) s hs p

/-- **The point condition of item (8) of [Stacks, Tag 0C6U] from a section**: a separated scheme
over `k` whose local rings are normal and which has a section has finitely many (one) closed
points with normal local rings whose residue degrees have greatest common divisor `1`. -/
theorem exists_normalPoints_gcd_eq_one_of_section_of_isNormalRing [IsSeparated f]
    (hnorm : ∀ x : X, IsNormalRing (X.presheaf.stalk x)) (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
      (∀ i, IsNormalRing (X.presheaf.stalk (x i))) ∧
      Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
        Module.finrank k (X.residueField (x i))) = 1 := by
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨hcl, hn, hdeg⟩ := normalRationalPoint_of_section_of_isNormalRing f hnorm s hs p
  refine ⟨1, fun _ => s p, fun _ => hcl, fun _ => hn, ?_⟩
  simp only [Finset.univ_unique, Finset.gcd_singleton]
  rw [hdeg]
  rfl

/-- **The point condition of item (8) of [Stacks, Tag 0C6U] from a section of a smooth separated
scheme over `k`.** -/
theorem exists_normalPoints_gcd_eq_one_of_section [IsSeparated f] [Smooth f]
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
      (∀ i, IsNormalRing (X.presheaf.stalk (x i))) ∧
      Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
        Module.finrank k (X.residueField (x i))) = 1 :=
  exists_normalPoints_gcd_eq_one_of_section_of_isNormalRing f (isNormalRing_stalk_of_smooth f) s hs

end AlgebraicGeometry.ProjectiveLineCriterion

end
