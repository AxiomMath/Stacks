module

public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Finite free resolutions of bounded-above complexes with finite cohomology

Over a Noetherian ring `A`, a complex of `A`-modules vanishing above degree `b` whose cohomology
modules are finite receives a quasi-isomorphism from a complex of finite free `A`-modules which
also vanishes above degree `b`. This is the chain-level form of the pseudo-coherence of such a
complex (Stacks 066E together with Stacks 064T): the derived-category representative given by
pseudo-coherence lifts to a morphism of complexes because a bounded-above complex of projective
modules is K-projective.

## Main results

* `Stacks.FlatBaseChangeHom.exists_quasiIso_finiteFree_of_isStrictlyLE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FlatBaseChangeHom

/-- **A complex over a Noetherian ring vanishing above degree `b` with finite cohomology receives
a quasi-isomorphism from a complex of finite free modules vanishing above degree `b`.** -/
theorem exists_quasiIso_finiteFree_of_isStrictlyLE {A : Type u} [CommRing A]
    [IsNoetherianRing A] (E : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Finite A (E.homology i)) :
    ∃ (Q : CochainComplex (ModuleCat.{u} A) ℤ) (h : Q ⟶ E),
      (∀ i, Module.Finite A (Q.X i) ∧ Module.Free A (Q.X i)) ∧ Q.IsStrictlyLE b ∧
        QuasiIso h := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  have hH : ∀ i, (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Q.obj E) ≅ E.homology i := fun i =>
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app E
  have hvan : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Q.obj E)) := fun i hi =>
    (E.isZero_of_isLE b i hi).of_iso (hH i)
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj E) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (DerivedCategory.Q.obj E) 0 A).2.1).2
      ⟨⟨b, hvan⟩, fun i => Module.Finite.equiv (hH i).symm.toLinearEquiv⟩
  obtain ⟨Q, α, hQ, hQle, hα⟩ :=
    StacksDraft.PseudoCoherence.exists_finiteFree_representative_le _ b hpc hvan
  have : ∀ n, Projective (Q.X n) := fun n => by
    have := (hQ n).1
    have := (hQ n).2
    infer_instance
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q b
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨γ, hγ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective Q
    ((HomotopyCategory.quotient _ _).obj E)).2 (e.hom.app Q ≫ α ≫ e.inv.app E)
  obtain ⟨h, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective γ
  refine ⟨Q, h, hQ, hQle, ?_⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have hQh : DerivedCategory.Q.map h = e.inv.app Q ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map h) ≫ e.hom.app E := by
    rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]
  rw [hQh, hγ]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]
  infer_instance

end Stacks.FlatBaseChangeHom

end
