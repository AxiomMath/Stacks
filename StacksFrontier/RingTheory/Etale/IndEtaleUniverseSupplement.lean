module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse

/-!
# The factorization property of ind-étale algebras

If `B` is ind-étale over `A`, every `A`-algebra map into `B` from a finitely presented
`A`-algebra factors through an étale `A`-algebra (Lemma 07C3).

## Main results

* `StacksDraft.IndEtale.exists_etale_factorization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft

/-- **Lemma 07C3 for an ind-étale algebra.** If `B` is ind-étale over `A`, then every
`A`-algebra map into `B` from a finitely presented `A`-algebra factors through an étale
`A`-algebra. -/
theorem IndEtale.exists_etale_factorization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hB : IndEtale A B) (C : Type u) [CommRing C] [Algebra A C]
    [Algebra.FinitePresentation A C] (f : C →ₐ[A] B) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
      Algebra.Etale A E ∧ ∃ (g : C →ₐ[A] E) (h : E →ₐ[A] B), h.comp g = f := by
  have H := indEtale_iff.mp hB
  rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _
      (fun (C : Under (CommRingCat.of A)) (h : CommRingCat.etale.underObj C) =>
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).2.2)] at H
  obtain ⟨E, g, h, he, het⟩ := H
    (Under.mk (CommRingCat.ofHom (algebraMap A C)))
    (show (algebraMap A C).FinitePresentation from
      RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext x; exact f.commutes x))
  let := E.hom.hom.toAlgebra
  refine ⟨E.right, inferInstance, inferInstance, RingHom.etale_algebraMap.mp het,
    ⟨g.right.hom, fun x => congr($(Under.w g).hom x)⟩,
    ⟨h.right.hom, fun x => congr($(Under.w h).hom x)⟩, ?_⟩
  ext x
  exact congr($(congrArg Under.Hom.right he).hom x)

end StacksDraft

end
