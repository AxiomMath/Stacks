module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinOpenness
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem

/-!
# The thickenings of a complete local base as a limit of affine schemes

For a Noetherian complete local ring `A` over `S` (a `Deformation.Artin.FormalBase S`), `Spec A`
is presented as the limit of its infinitesimal thickenings `Spec A / 𝔪ⁿ⁺¹`.

## Main definitions

* `Deformation.Artin.FormalBase.ringSystem`: the inverse system `n ↦ A / 𝔪ⁿ⁺¹` of `A`-algebras.
* `Deformation.Artin.FormalBase.ringCone`: the cone of quotient maps `A ⟶ A / 𝔪ⁿ⁺¹`.
* `Deformation.Artin.truncationDiagram`: the thickenings and their inclusions, in the big fppf
  site of `S`.
* `Deformation.Artin.truncationCocone`: the maps of the thickenings to `Spec A`.

## Main results

* `Deformation.Artin.FormalBase.isLimitRingCone`: `A` is the limit of the quotients `A / 𝔪ⁿ⁺¹`.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.formalEffective_of_quotients`: effectivity of
  formal objects for a model of the Quot presheaf follows from effectivity of compatible families
  of quotients.

These are the inputs of the effectivity statements for towers of thickenings, used for axiom [4]
of Stacks 0CZW.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing AlgebraicGeometry

universe u

namespace Deformation.Artin

namespace FormalBase

variable {S : Scheme.{u}} (A : FormalBase S)

/-- The inverse system of `A`-algebras `n ↦ A / 𝔪ⁿ⁺¹`. -/
abbrev ringSystem : ℕᵒᵖ ⥤ CommAlgCat.{u} A.R :=
  powQuotientDiagram A.R (maximalIdeal A.R)

/-- The cone of quotient maps `A ⟶ A / 𝔪ⁿ⁺¹`. -/
def ringCone : Cone A.ringSystem where
  pt := .of A.R A.R
  π :=
    { app n := CommAlgCat.ofHom (Ideal.Quotient.mkₐ A.R (maximalIdeal A.R ^ (n.unop + 1)))
      naturality _ _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl) }

/-- **A complete local ring is the limit of its quotients by the powers of its maximal ideal.** -/
def isLimitRingCone : IsLimit A.ringCone := by
  haveI : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
  let I := maximalIdeal A.R
  let fam : ∀ s : Cone A.ringSystem, ∀ n : ℕ, s.pt →ₐ[A.R] A.R ⧸ I ^ n := fun s n =>
    (Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (s.π.app (op n)).hom
  have hw : ∀ (s : Cone A.ringSystem) {m n : ℕ} (hle : m ≤ n) (x : s.pt),
      (A.ringSystem.map (homOfLE hle).op).hom ((s.π.app (op n)).hom x) = (s.π.app (op m)).hom x :=
    fun s m n hle x => congrArg (fun φ => CommAlgCat.Hom.hom φ x) (s.w (homOfLE hle).op)
  have hfam : ∀ s : Cone A.ringSystem, ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right hle)).comp (fam s n) = fam s m := by
    intro s m n hle
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((s.π.app (op n)).hom x)
    have hm : (s.π.app (op m)).hom x = Ideal.Quotient.mk _ y := by
      rw [← hw s hle x, ← hy]
      rfl
    change Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right hle)
        (Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right (Nat.le_succ n))
          ((s.π.app (op n)).hom x)) =
      Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right (Nat.le_succ m)) ((s.π.app (op m)).hom x)
    rw [← hy, hm]
    rfl
  have hlift : ∀ (s : Cone A.ringSystem) (n : ℕ) (x : s.pt),
      Ideal.Quotient.mk (I ^ (n + 1)) (IsAdicComplete.liftAlgHom I (fam s) (hfam s) x) =
        (s.π.app (op n)).hom x := by
    intro s n x
    have h := IsAdicComplete.mk_liftAlgHom I (fam s) (hfam s) (n + 1) x
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective ((s.π.app (op (n + 1))).hom x)
    have hn : (s.π.app (op n)).hom x = Ideal.Quotient.mk _ y := by
      rw [← hw s (Nat.le_succ n) x, ← hy]
      rfl
    refine h.trans ?_
    change Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      ((s.π.app (op (n + 1))).hom x) = _
    rw [← hy, hn]
    rfl
  refine
    { lift := fun s => CommAlgCat.ofHom (IsAdicComplete.liftAlgHom I (fam s) (hfam s))
      fac := fun s n => CommAlgCat.hom_ext (AlgHom.ext fun x => hlift s n.unop x)
      uniq := fun s g hg => ?_ }
  let g' : s.pt →ₐ[A.R] A.R := g.hom
  have hg' : ∀ (n : ℕ) (x : s.pt), Ideal.Quotient.mk (I ^ (n + 1)) (g' x) =
      (s.π.app (op n)).hom x := fun n x =>
    congrArg (fun φ => CommAlgCat.Hom.hom φ x) (hg (op n))
  have e : g' = IsAdicComplete.liftAlgHom I (fam s) (hfam s) := by
    refine IsAdicComplete.algHom_ext I fun n => AlgHom.ext fun x => ?_
    change Ideal.Quotient.mk (I ^ n) (g' x) =
      Ideal.Quotient.mk (I ^ n) (IsAdicComplete.liftAlgHom I (fam s) (hfam s) x)
    rw [IsAdicComplete.mk_liftAlgHom I (fam s) (hfam s) n x]
    change _ = Ideal.Quotient.factorₐ A.R (Ideal.pow_le_pow_right (Nat.le_succ n))
      ((s.π.app (op n)).hom x)
    rw [← hg' n x]
    rfl
  exact CommAlgCat.hom_ext e

end FormalBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (A : FormalBase S)
  (hA : B.Contains (Spec (.of A.R))) (contains : ∀ n, B.Contains (A.truncation n))

/-- The infinitesimal thickenings of a complete local base and their inclusions, as a diagram in
the big fppf site of `S`. -/
abbrev truncationDiagram : ℕ ⥤ BigFppfOver B S hS :=
  Functor.ofSequence (truncationOverSucc B S hS A contains)

/-- The maps of the infinitesimal thickenings to the complete local base, as a cocone. -/
def truncationCocone : Cocone (truncationDiagram B S hS A contains) where
  pt := baseOver B S hS A hA
  ι := NatTrans.ofSequence (fun n => restrictionToBase B S hS A hA contains n) fun n => by
    simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    exact restrictionToBase_succ B S hS A hA contains n

/-- The component of `truncationCocone` at `n` is the map of the `n`-th thickening to the base. -/
theorem truncationCocone_ι_app (n : ℕ) :
    (truncationCocone B S hS A hA contains).ι.app n = restrictionToBase B S hS A hA contains n :=
  rfl

/-- The identification of the thickenings with the spectra of the levels of the ring system. -/
def truncationIso (n : ℕ) : (BigFppfOver.toScheme B S hS).obj
    ((truncationDiagram B S hS A contains).obj n) ≅ Spec (.of (A.ringSystem.obj (.op n))) :=
  Iso.refl _

/-- The identification of the base with the spectrum of the limit of the ring system. -/
def truncationLimitIso : (BigFppfOver.toScheme B S hS).obj
    (truncationCocone B S hS A hA contains).pt ≅ Spec (.of A.ringCone.pt) :=
  Iso.refl _

/-- Under `truncationIso` and `truncationLimitIso`, the map of the `n`-th thickening to the base is
the spectrum of the quotient map `A ⟶ A / 𝔪ⁿ⁺¹`. -/
theorem truncationLimitIso_spec (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map ((truncationCocone B S hS A hA contains).ι.app n) ≫
        (truncationLimitIso B S hS A hA contains).hom =
      (truncationIso B S hS A contains n).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (A.ringCone.π.app (.op n)).hom.toRingHom).op :=
  rfl

/-- The structure maps of the thickenings to `Spec A`, as a cocone of schemes. -/
def truncationSchemeCocone :
    Cocone (truncationDiagram B S hS A contains ⋙ BigFppfOver.toScheme B S hS) where
  pt := Spec (.of A.R)
  ι := NatTrans.ofSequence (fun n => adicThickeningι A.R (maximalIdeal A.R) n) fun n => by
    simp only [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    exact adicThickeningSucc_ι A.R (maximalIdeal A.R) n

/-- Under `truncationIso`, the inclusion of thickenings indexed by `i ⟶ j` is the spectrum of the
transition map `A / 𝔪ʲ⁺¹ ⟶ A / 𝔪ⁱ⁺¹` of the ring system. -/
theorem truncationIso_spec {i j : ℕ} (f : i ⟶ j) :
    (BigFppfOver.toScheme B S hS).map ((truncationDiagram B S hS A contains).map f) ≫
        (truncationIso B S hS A contains j).hom =
      (truncationIso B S hS A contains i).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (A.ringSystem.map f.op).hom.toRingHom).op := by
  let ι' : Spec (.of (A.ringSystem.obj (op j))) ⟶ Spec (.of A.R) :=
    Spec.map (CommRingCat.ofHom (A.ringCone.π.app (op j)).hom.toRingHom)
  have : IsClosedImmersion ι' :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← cancel_mono ι']
  have h₁ := (truncationSchemeCocone B S hS A contains).ι.naturality f
  simp only [Functor.const_obj_map, Functor.comp_map] at h₁
  have h₂ : A.ringCone.π.app (op i) = A.ringCone.π.app (op j) ≫ A.ringSystem.map f.op := by
    simp
  change (BigFppfOver.toScheme B S hS).map ((truncationDiagram B S hS A contains).map f) ≫
      adicThickeningι A.R (maximalIdeal A.R) j =
    Scheme.Spec.map (CommRingCat.ofHom (A.ringSystem.map f.op).hom.toRingHom).op ≫ ι'
  refine h₁.trans ?_
  change Spec.map (CommRingCat.ofHom (A.ringCone.π.app (op i)).hom.toRingHom) = _
  rw [h₂]
  change Spec.map (CommRingCat.ofHom (A.ringCone.π.app (op j)).hom.toRingHom ≫
    CommRingCat.ofHom (A.ringSystem.map f.op).hom.toRingHom) = _
  rw [Spec.map_comp]
  rfl

end Deformation.Artin

namespace AlgebraicGeometry.Space

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Effectivity of formal objects for a model of the Quot presheaf, from quotients.** Over a base
with a unique point over every scheme of the site, if every compatible family of quotients over
the thickenings `Spec A / 𝔪ⁿ⁺¹` of a complete local base is the family of pullbacks of one
quotient over `Spec A`, then compatible families of sections of the model over the thickenings
come from one section over `Spec A`. -/
theorem QuotSitePresheafModel.formalEffective_of_quotients {D : QuotSituation B S hS}
    (M : QuotSitePresheafModel D)
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    (A : FormalBase S) (contains : ∀ n, B.Contains (A.truncation n))
    (hA : B.Contains (Spec (.of A.R)))
    (hquot : ∀ K : ∀ n, D.properlySupportedQuotients
        (D.testOver ι (truncationOver B S hS A contains n)),
      (∀ n, D.quotientPullback (D.testHom ι (truncationOverSucc B S hS A contains n))
          (K (n + 1)).1 = (K n).1) →
        ∃ Kl : D.properlySupportedQuotients (D.testOver ι (baseOver B S hS A hA)),
          ∀ n, D.quotientPullback (D.testHom ι (restrictionToBase B S hS A hA contains n)) Kl.1 =
            (K n).1)
    (t : ∀ n, M.presheaf.obj (op (truncationOver B S hS A contains n)))
    (ht : ∀ n, M.presheaf.map (truncationOverSucc B S hS A contains n).op (t (n + 1)) = t n) :
    ∃ x : M.presheaf.obj (op (baseOver B S hS A hA)),
      ∀ n, M.presheaf.map (restrictionToBase B S hS A hA contains n).op x = t n := by
  choose K hK using fun n => M.exists_ofQuot ι (t n)
  obtain ⟨Kl, hKl⟩ := hquot K fun n => (M.map_eq_iff ι _ _ _ _ _ (hK (n + 1)) (hK n)).1 (ht n)
  obtain ⟨ξ, hξ⟩ := M.exists_of_ofQuot ι Kl
  exact ⟨ξ, fun n => (M.map_eq_iff ι _ _ _ _ _ hξ (hK n)).2 (hKl n)⟩

end AlgebraicGeometry.Space
