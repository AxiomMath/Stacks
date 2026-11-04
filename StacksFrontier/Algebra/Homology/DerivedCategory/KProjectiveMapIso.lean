module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Additive functors carry isomorphic K-projective complexes to isomorphic complexes

Two K-projective complexes which are isomorphic in the derived category are homotopy equivalent:
morphisms in the derived category out of a K-projective complex are morphisms in the homotopy
category. An additive functor `Φ` preserves homotopies, so the complexes `Φ(K)` and `Φ(L)` are
homotopy equivalent, hence isomorphic in the derived category of the target, although `Φ` need
not be exact.

This is used for bounded complexes of finite projective modules, which are K-projective
(`CochainComplex.isKProjective_of_projective`), and for a right exact functor `Φ` such as
`M ↦ 𝒪_X ⊗_A M`.

## Main results

* `CochainComplex.IsKProjective.nonempty_Q_obj_mapHomologicalComplex_iso`.
-/

@[expose] public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKProjective

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- **An additive functor carries K-projective complexes isomorphic in `D(C)` to complexes
isomorphic in `D(D)`**: such complexes are homotopy equivalent, and an additive functor preserves
homotopy equivalences. -/
theorem nonempty_Q_obj_mapHomologicalComplex_iso (Φ : C ⥤ D) [Φ.Additive]
    (K L : CochainComplex C ℤ) [K.IsKProjective] [L.IsKProjective] (e : Q.obj K ≅ Q.obj L) :
    Nonempty (Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) := by
  obtain ⟨f, hf⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).2
    ((quotientCompQhIso C).hom.app K ≫ e.hom ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, hg⟩ := (Qh_map_bijective L ((HomotopyCategory.quotient _ _).obj K)).2
    ((quotientCompQhIso C).hom.app L ≫ e.inv ≫ (quotientCompQhIso C).inv.app K)
  have hfg : f ≫ g = 𝟙 _ := (Qh_map_bijective K _).1 (by simp [hf, hg])
  have hgf : g ≫ f = 𝟙 _ := (Qh_map_bijective L _).1 (by simp [hf, hg])
  exact ⟨(quotientCompQhIso D).symm.app _ ≪≫
    Qh.mapIso ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso ⟨f, g, hfg, hgf⟩) ≪≫
      (quotientCompQhIso D).app _⟩

end CochainComplex.IsKProjective
