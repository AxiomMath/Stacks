module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage

/-!
# Restriction for a direct image along an integral morphism with acyclic fibres

Let `i : Z ⟶ X` be a morphism of schemes, `g : Y ⟶ X` an integral morphism and
`Y' = Y ×_X Z`, with projections `i' : Y' ⟶ Y` and `g' : Y' ⟶ Z`. For an abelian sheaf `H` on
`Y_étale` whose cohomology in a positive degree `q` vanishes on `Y`, and the cohomology of whose
inverse image vanishes on `Y'` in degree `q`, the restriction map
`H^q(X, g_* H) → H^q(Z, (g_* H)|_Z)` is bijective: both groups vanish. Indeed
`H^q(X, g_* H) = H^q(Y, H)` (the higher direct images of an integral morphism vanish) and
`(g_* H)|_Z = g'_*(H|_{Y'})` (base change for an integral morphism, Stacks 0EYP), so that
`H^q(Z, (g_* H)|_Z) = H^q(Y', H|_{Y'})`.

This is the computation the source performs in the proof of Stacks Lemma 09ZE for the sheaves
`f_* M`, where the vanishing comes from Stacks Lemma 09ZD.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_iso`: cohomology of isomorphic sheaves.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_of_subsingleton`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- Vanishing of a cohomology group is invariant under isomorphism of the coefficient sheaf. -/
theorem subsingleton_sheafH_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} F q)) : Subsingleton (Sheaf.H.{u + 1} G q) := by
  have hl : Function.LeftInverse (Sheaf.H.map e.hom q) (Sheaf.H.map e.inv q) := fun x => by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_apply, Abelian.Ext.comp_mk₀_id]
  exact hl.injective.subsingleton

/-- Vanishing of cohomology transfers from a sheaf on `Y` to its direct image along an integral
morphism `g : Y ⟶ X`. -/
theorem subsingleton_sheafH_directImage {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIntegralHom g]
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} H q)) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} g).obj H) q) :=
  (etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} g H q).injective.subsingleton

/-- **Restriction is bijective for a direct image with acyclic fibres.** Let `g : Y ⟶ X` be
integral and let `Y'` be the fibre product of `g` and `i : Z ⟶ X`, with projections `g'` and
`i'`. If `H^q(Y, H) = 0` and `H^q(Y', i'^{-1} H) = 0` then restriction
`H^q(X, g_* H) → H^q(Z, i^{-1} g_* H)` is bijective, both groups being zero. -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_of_subsingleton
    {X Y Z Y' : Scheme.{u}} (i : Z ⟶ X) (g : Y ⟶ X) (g' : Y' ⟶ Z) (i' : Y' ⟶ Y)
    (sq : IsPullback g' i' i g) [IsIntegralHom g]
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h₁ : Subsingleton (Sheaf.H.{u + 1} H q))
    (h₂ : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i').obj H) q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i
      ((etaleAbelianDirectImage.{u, 0} g).obj H) q) := by
  have : IsIntegralHom g' := MorphismProperty.of_isPullback sq.flip ‹_›
  have hX := subsingleton_sheafH_directImage g H q h₁
  have hBC : IsIso (smallEtaleBaseChangeAb i g g' i' sq.w) :=
    isIso_smallEtaleBaseChangeAb_of_isIntegralHom i g g' i' sq
  let eZ : (etaleAbelianInverseImage.{u, 0} i).obj ((etaleAbelianDirectImage.{u, 0} g).obj H) ≅
      (etaleAbelianDirectImage.{u, 0} g').obj ((etaleAbelianInverseImage.{u, 0} i').obj H) :=
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange i)
        AddCommGrpCat.{u + 1} X.smallEtaleTopology Z.smallEtaleTopology).app _).symm ≪≫
      (asIso (smallEtaleBaseChangeAb i g g' i' sq.w)).app H ≪≫
      (etaleAbelianDirectImage.{u, 0} g').mapIso
        ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange i')
          AddCommGrpCat.{u + 1} Y.smallEtaleTopology Y'.smallEtaleTopology).app H)
  have hZ := subsingleton_sheafH_iso eZ.symm q (subsingleton_sheafH_directImage g' _ q h₂)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Stacks.EtaleCohomology
