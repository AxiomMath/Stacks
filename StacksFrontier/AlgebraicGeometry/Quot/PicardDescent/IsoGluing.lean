module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Reading

/-!
# Gluing isomorphisms of quasi-coherent modules along an fpqc covering

Let `(e i : Z i ⟶ W)` be an fpqc covering of algebraic spaces and let `M`, `N` be quasi-coherent
`𝒪_W`-modules. A family of isomorphisms `w i : (e i)^*M ≅ (e i)^*N` whose readings agree on the
overlaps glues to an isomorphism `M ≅ N` with inverse image `w i` along every member.

The overlaps are given as cartesian squares `Q i j ⟶ Z i, Q i j ⟶ Z j` over `W`, not necessarily
the chosen fibre products, and the agreement of the readings is asked there; it then holds on
the chosen fibre products, which is the pairwise condition of Stacks 04W3.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_congr_left`: the reading depends on the
  morphism read along only.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_iso_of_readIso_eq`: isomorphisms of the
  inverse images whose readings agree on the overlaps glue to an isomorphism `M ≅ N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The reading depends on the morphism read along only, and not on its presentation. -/
theorem readIso_congr_left {Z W Y₁ Y₂ : AlgebraicSpaces B S hS} {c c' : Z ⟶ W} (e : c = c')
    {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂} {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁)
    (h₂ : c ≫ a₂ = v₂) (h₁' : c' ≫ a₁ = v₁) (h₂' : c' ≫ a₂ = v₂)
    {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2} {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2}
    (θ : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂) :
    readIso c h₁ h₂ θ = readIso c' h₁' h₂' θ := by
  subst e
  rfl

variable {I : Type v} {W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}

/-- The pairwise condition of Stacks 04W3 for a family of isomorphisms of inverse images is the
agreement of their readings on the chosen fibre products. -/
theorem isPairwiseCompatible_of_readIso_eq (e : ∀ i, Z i ⟶ W)
    {M N : Modules.{u, u} B S hS W.1 W.2}
    (w : ∀ i, (modulePullback B S hS (e i)).obj M ≅ (modulePullback B S hS (e i)).obj N)
    (hw : ∀ i j, readIso (pairFst B S hS Z e i j) rfl rfl (w i) =
      readIso (pairSnd B S hS Z e i j) (pair_condition B S hS Z e i j).symm
        (pair_condition B S hS Z e i j).symm (w j)) :
    IsPairwiseCompatible B S hS Z e fun i => (w i).hom := by
  intro i j
  rw [canonicalComparison_eq_pullbackComparison B S hS _ _ _ _ _ _ rfl
      (pair_condition B S hS Z e i j).symm N,
    canonicalComparison_eq_pullbackComparison B S hS _ _ _ _ _ _ rfl
      (pair_condition B S hS Z e i j).symm M]
  have h' := congrArg (fun φ => (pullbackComparison B S hS (pairFst B S hS Z e i j) (e i)
      (pairFst B S hS Z e i j ≫ e i) rfl M).inv ≫ φ.hom ≫ (pullbackComparison B S hS
        (pairSnd B S hS Z e i j) (e j) (pairFst B S hS Z e i j ≫ e i)
        (pair_condition B S hS Z e i j).symm N).hom) (hw i j)
  simp only [readIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] at h'
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using h'

/-- The agreement of readings on cartesian overlaps gives the agreement on the chosen fibre
products. -/
theorem readIso_pair_eq_of_readIso_eq (e : ∀ i, Z i ⟶ W) {M N : Modules.{u, u} B S hS W.1 W.2}
    (w : ∀ i, (modulePullback B S hS (e i)).obj M ≅ (modulePullback B S hS (e i)).obj N)
    (Q : I → I → AlgebraicSpaces B S hS) (q₁ : ∀ i j, Q i j ⟶ Z i) (q₂ : ∀ i j, Q i j ⟶ Z j)
    (hQ : ∀ i j, IsPullback (q₁ i j) (q₂ i j) (e i) (e j))
    (hw : ∀ i j, readIso (q₁ i j) rfl rfl (w i) =
      readIso (q₂ i j) (hQ i j).w.symm (hQ i j).w.symm (w j)) (i j : I) :
    readIso (pairFst B S hS Z e i j) rfl rfl (w i) =
      readIso (pairSnd B S hS Z e i j) (pair_condition B S hS Z e i j).symm
        (pair_condition B S hS Z e i j).symm (w j) := by
  have hd₁ : (hQ i j).lift (pairFst B S hS Z e i j) (pairSnd B S hS Z e i j)
      (pair_condition B S hS Z e i j) ≫ q₁ i j = pairFst B S hS Z e i j := (hQ i j).lift_fst _ _ _
  have hd₂ : (hQ i j).lift (pairFst B S hS Z e i j) (pairSnd B S hS Z e i j)
      (pair_condition B S hS Z e i j) ≫ q₂ i j = pairSnd B S hS Z e i j := (hQ i j).lift_snd _ _ _
  rw [readIso_congr_left hd₁.symm _ _ (by rw [hd₁]) (by rw [hd₁]),
    ← readIso_readIso _ (q₁ i j) rfl rfl (by rw [← Category.assoc, hd₁])
      (by rw [← Category.assoc, hd₁]),
    hw i j, readIso_readIso _ (q₂ i j), readIso_congr_left hd₂]

/-- Isomorphisms of inverse images with readings agreeing on cartesian overlaps are the inverse
images of a morphism. -/
private theorem exists_hom_of_readIso_eq (e : ∀ i, Z i ⟶ W)
    (he : IsFpqcCovering B S hS fun i => (e i).hom) {M N : Modules.{u, u} B S hS W.1 W.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ i, (modulePullback B S hS (e i)).obj M ≅ (modulePullback B S hS (e i)).obj N)
    (Q : I → I → AlgebraicSpaces B S hS) (q₁ : ∀ i j, Q i j ⟶ Z i) (q₂ : ∀ i j, Q i j ⟶ Z j)
    (hQ : ∀ i j, IsPullback (q₁ i j) (q₂ i j) (e i) (e j))
    (hw : ∀ i j, readIso (q₁ i j) rfl rfl (w i) =
      readIso (q₂ i j) (hQ i j).w.symm (hQ i j).w.symm (w j)) :
    ∃ φ : M ⟶ N, ∀ i, (modulePullback B S hS (e i)).map φ = (w i).hom :=
  exists_modulePullback_map_eq_of_isFpqcCovering B S hS (reprFpqcHomSurjective.{u, v} B S hS)
    Z e he (fun i => (w i).hom)
    (isPairwiseCompatible_of_readIso_eq e w (readIso_pair_eq_of_readIso_eq e w Q q₁ q₂ hQ hw))
    hM hN

/-- **Isomorphisms of quasi-coherent modules glue along an fpqc covering of algebraic spaces.**
A family `w i : (e i)^*M ≅ (e i)^*N` of isomorphisms of the inverse images of two quasi-coherent
modules whose readings agree on cartesian overlaps `Q i j` is the family of inverse images of an
isomorphism `M ≅ N`. -/
theorem exists_iso_of_readIso_eq (e : ∀ i, Z i ⟶ W)
    (he : IsFpqcCovering B S hS fun i => (e i).hom) {M N : Modules.{u, u} B S hS W.1 W.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ i, (modulePullback B S hS (e i)).obj M ≅ (modulePullback B S hS (e i)).obj N)
    (Q : I → I → AlgebraicSpaces B S hS) (q₁ : ∀ i j, Q i j ⟶ Z i) (q₂ : ∀ i j, Q i j ⟶ Z j)
    (hQ : ∀ i j, IsPullback (q₁ i j) (q₂ i j) (e i) (e j))
    (hw : ∀ i j, readIso (q₁ i j) rfl rfl (w i) =
      readIso (q₂ i j) (hQ i j).w.symm (hQ i j).w.symm (w j)) :
    ∃ φ : M ≅ N, ∀ i, (modulePullback B S hS (e i)).mapIso φ = w i := by
  have hw' : ∀ i j, readIso (q₁ i j) rfl rfl (w i).symm =
      readIso (q₂ i j) (hQ i j).w.symm (hQ i j).w.symm (w j).symm := fun i j => by
    rw [← readIso_symm, ← readIso_symm, hw i j]
  obtain ⟨φ, hφ⟩ := exists_hom_of_readIso_eq e he hM hN w Q q₁ q₂ hQ hw
  obtain ⟨ψ, hψ⟩ := exists_hom_of_readIso_eq e he hN hM (fun i => (w i).symm) Q q₁ q₂ hQ hw'
  have h₁ : φ ≫ ψ = 𝟙 M := modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective.{u, v} B S hS) Z e he _ _ fun i => by
      rw [CategoryTheory.Functor.map_comp, hφ i, hψ i, CategoryTheory.Functor.map_id]
      exact (w i).hom_inv_id
  have h₂ : ψ ≫ φ = 𝟙 N := modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective.{u, v} B S hS) Z e he _ _ fun i => by
      rw [CategoryTheory.Functor.map_comp, hφ i, hψ i, CategoryTheory.Functor.map_id]
      exact (w i).inv_hom_id
  exact ⟨⟨φ, ψ, h₁, h₂⟩, fun i => Iso.ext (hφ i)⟩

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
