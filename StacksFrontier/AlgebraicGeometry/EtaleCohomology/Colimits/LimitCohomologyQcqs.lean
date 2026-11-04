module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitRestrictSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange

/-!
# Stacks 09YQ for quasi-compact and quasi-separated levels

Let `(X_i)` be a directed inverse system of schemes with affine transition morphisms, with a least
index `⊥`, and let `X = lim X_i`. For an open `W ⊆ X_⊥` the base changes `W_i = X_i ×_{X_⊥} W`
form a system of the same kind with limit `X ×_{X_⊥} W`. This file proves that the comparison
`colim_i H^m(X_i, f_i⁻¹G) → H^m(X, f⁻¹G)` is an isomorphism for every abelian sheaf `G` on `X_⊥`
when `X_⊥` is quasi-compact and quasi-separated, by the induction principle of Stacks 08DR: the
affine case is `Stacks.EtaleCohomology.LimitSiteBridge`, and the Mayer–Vietoris step uses the
short exact sequence `0 → j_{U∩V!}ℤ → j_{U!}ℤ ⊕ j_{V!}ℤ → ℤ → 0` of a cover by two opens, the
five lemma, and the identification of `Ext^m_{X_i}(f_i⁻¹ j_!ℤ, f_i⁻¹G)` with the cohomology of
`W_i`, which is compatible with the transition maps by the coherence of inverse images.

## Main definitions

* `Stacks.EtaleCohomology.LimitExt.restrictSystem`: the system `(X_i ×_{X_⊥} W)_i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse


section OpenRestriction

/-- The adjunction `j_! ⊣ j⁻¹` for an étale `j`, with `j⁻¹` the inverse image. -/
def extAdj {W S : Scheme.{u}} (ι : W ⟶ S) [Etale ι] :
    extensionByZero.{u, 0} ι ⊣ etaleAbelianInverseImage.{u, 0} ι :=
  (extensionByZeroAdj.{u, 0} ι).ofNatIsoRight (etaleAbelianInverseImageRestrictionIso.{u, 0} ι).symm

/-- The base changed unit-type map stays an isomorphism on adjoints. -/
theorem isIso_restrictBase_adjoint {S W X W' : Scheme.{u}} (ι : W ⟶ S) [IsOpenImmersion ι]
    (g : X ⟶ S) (e : W' ⟶ W) (j' : W' ⟶ X) (sq : IsPullback j' e g ι) [IsOpenImmersion j']
    {Q : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η)) :
    IsIso (((extAdj j').homEquiv _ _).symm ((etaleAbelianInverseImage.{u, 0} e).map η ≫
      (K e ι (e ≫ ι) rfl).inv.app Q ≫ (K j' g (e ≫ ι) sq.w.symm).hom.app Q)) := by
  have hbc := isIso_etaleAbelianBaseChange_of_isOpenImmersion.{u, 0} g ι j' e sq
  rw [etaleAbelianBaseChange_eq_mateEquiv.{u, 0} g ι j' e sq.w (e ≫ ι) sq.w.symm rfl] at hbc
  exact Stacks.ExtTransport.isIso_homEquiv_symm_of_isIso_map
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} e) (extAdj ι) (extAdj j')
    (K e ι (e ≫ ι) rfl).symm (K j' g (e ≫ ι) sq.w.symm).symm hbc η hη

/-- **Restriction to an open of the base is bijective on `Ext` out of an extension by zero.** For
an open immersion `ι : W ⟶ S`, a cartesian square `W' = X ×_S W` and `η : A ⟶ ι⁻¹Q` whose adjoint
`ι_! A ⟶ Q` is invertible, `restrictBase` is a bijection
`Ext^n(g⁻¹Q, g⁻¹G) ≃ Ext^n(e⁻¹A, e⁻¹(ι⁻¹G))`. -/
theorem bijective_restrictBase {S W X W' : Scheme.{u}} (ι : W ⟶ S) [IsOpenImmersion ι]
    (g : X ⟶ S) (e : W' ⟶ W) (j' : W' ⟶ X) (sq : IsPullback j' e g ι) [IsOpenImmersion j']
    {Q : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η)) (n : ℕ) :
    Function.Bijective (restrictBase (G := G) ι g e j' (e ≫ ι) rfl sq.w.symm η n) := by
  have hiso := isIso_restrictBase_adjoint ι g e j' sq η hη
  have hb := Stacks.ExtTransport.bijective_transport_of_isIso (extAdj j') _ hiso
    ((etaleAbelianInverseImage.{u, 0} g).obj G) n
  have hfac : (restrictBase (G := G) ι g e j' (e ≫ ι) rfl sq.w.symm η n : _ → _) =
      (Stacks.ExtTransport.sandwich (𝟙 _) ((K j' g (e ≫ ι) sq.w.symm).inv.app G ≫
        (K e ι (e ≫ ι) rfl).hom.app G) n) ∘
      (Stacks.ExtTransport.transport (etaleAbelianInverseImage.{u, 0} j')
        ((etaleAbelianInverseImage.{u, 0} e).map η ≫ (K e ι (e ≫ ι) rfl).inv.app Q ≫
          (K j' g (e ≫ ι) sq.w.symm).hom.app Q) (𝟙 _) n) := by
    funext x
    simp only [Function.comp_apply, restrictBase, Stacks.ExtTransport.sandwich_transport,
      Category.id_comp]
  rw [hfac]
  exact (Stacks.ExtTransport.sandwich_bijective _ _ n).comp hb

end OpenRestriction

end Stacks.EtaleCohomology.LimitExt
