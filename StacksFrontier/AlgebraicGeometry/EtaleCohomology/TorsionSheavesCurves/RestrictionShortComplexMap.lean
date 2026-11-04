module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage

/-!
# Restriction and connecting maps along a morphism of short exact sequences

Let `π : X ⟶ Y` be a morphism of schemes, `S` a short exact sequence of abelian sheaves on `Y_ét`
and `S'` one on `X_ét`. A morphism of short complexes `π⁻¹ S ⟶ S'` — equivalently, by adjunction,
a morphism `S ⟶ π_* S'` — makes restriction along `π` compatible with the two connecting maps:
for `x ∈ H^q(Y, S₃)` the restriction of its coboundary, moved to `H^{q+1}(X, S'₁)`, is the
coboundary of the restriction of `x` moved to `H^q(X, S'₃)`.

This is `Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass` for an arbitrary morphism of
short exact sequences in place of the Kummer comparison.

## Main definitions

* `Stacks.EtaleCohomology.inverseImageShortComplexHom`: the morphism `π⁻¹ S ⟶ S'` adjoint to a
  morphism `S ⟶ π_* S'`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_extClass_of_hom`: the coboundary square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- **The morphism `π⁻¹ S ⟶ S'` adjoint to a morphism of short complexes `S ⟶ π_* S'`**: each
component is the adjoint transpose under `π⁻¹ ⊣ π_*`. -/
def inverseImageShortComplexHom
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    {S' : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : S ⟶ S'.map (etaleAbelianDirectImage.{u, v} π)) :
    S.map (etaleAbelianInverseImage.{u, v} π) ⟶ S' where
  τ₁ := ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm φ.τ₁
  τ₂ := ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm φ.τ₂
  τ₃ := ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm φ.τ₃
  comm₁₂ :=
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv_naturality_right_symm
        φ.τ₁ S'.f).symm.trans
      ((congrArg ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm
          φ.comm₁₂).trans
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv_naturality_left_symm S.f φ.τ₂))
  comm₂₃ :=
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv_naturality_right_symm
        φ.τ₂ S'.g).symm.trans
      ((congrArg ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm
          φ.comm₂₃).trans
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv_naturality_left_symm S.g φ.τ₃))

/-- **The coboundary square for a morphism `ψ : π⁻¹ S ⟶ S'` of short exact sequences.** For
`x ∈ H^q(Y, S₃)`, restricting its coboundary along `π` and moving it along `ψ₁` gives the
coboundary in the sequence `S'` of the restriction of `x` moved along `ψ₃`. -/
theorem etaleCohomologyRestrictionMap_extClass_of_hom
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    {S' : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (hS' : S'.ShortExact)
    (ψ : S.map (etaleAbelianInverseImage.{u, v} π) ⟶ S')
    (q r : ℕ) (hqr : q + 1 = r) (x : Sheaf.H.{w} S.X₃ q) :
    Sheaf.H.map ψ.τ₁ r (etaleCohomologyRestrictionMap.{u, v, w} π S.X₁ r (x.comp hS.extClass hqr)) =
      (Sheaf.H.map ψ.τ₃ q (etaleCohomologyRestrictionMap.{u, v, w} π S.X₃ q x)).comp
        hS'.extClass hqr := by
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply,
    etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} π hS q r hqr x]
  refine (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ hqr).trans ?_
  refine (congrArg (fun z => (etaleCohomologyRestrictionMap.{u, v, w} π S.X₃ q x).comp z hqr)
    (ShortComplex.ShortExact.extClass_naturality
      (hS.map_of_exact (etaleAbelianInverseImage.{u, v} π)) hS' ψ)).trans ?_
  exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ hqr).symm

end Stacks.EtaleCohomology

end
