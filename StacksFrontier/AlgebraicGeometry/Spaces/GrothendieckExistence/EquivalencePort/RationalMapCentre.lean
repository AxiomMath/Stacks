module

public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ProjectiveExtensionCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.AffineOfAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsBaseChange.Basic

namespace Stacks.ProjectiveExtension.C1573
end Stacks.ProjectiveExtension.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The centre of a rational map to projective space on an algebraic space

Let `φ : V ⟶ X` be a surjective étale atlas of an algebraic space by an affine scheme, with
relation `R = V ×_X V`. A rational map to projective space on `X` is read on the atlas as an open
`U ⊆ V`, an ideal `I` of global functions on `V` whose basic opens cover `U`, and regular
functions `g₀, …, gₘ` on `U`; the centre `𝒥 = centreSheaf U I g`, that is
`Stacks.ProjectiveExtension.C1573.centreSheaf`, is then an ideal sheaf on
`V`. If its two pullbacks to `R` agree, it descends to a closed subspace of `X`.

## Main results

* `AlgebraicGeometry.Space.C1573.isInvariantSubscheme_centreSheaf`: the centre is invariant under
  the relation as soon as the data of the rational map agree on the relation.
* `Stacks.ProjectiveExtension.C1573.map_centre_appTop`: the centre commutes with flat base change
  of affine schemes.
* `AlgebraicGeometry.Space.C1573.exists_closedSubspace_preimage_eq_centreSheaf`: the descended
  centre is a closed subspace of `X`, whose preimage on the atlas is the centre.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.ProjectiveExtension

open _root_.Stacks.ProjectiveExtension.C1573 _root_.AlgebraicGeometry.C1573
variable {V Y : Scheme.{u}} [IsAffine V] [IsAffine Y] (U : V.Opens) (I : Ideal Γ(V, ⊤)) {m : ℕ}
  (g : Fin (m + 1) → Γ(V, U))

/-- **The centre commutes with flat base change of affine schemes.** Let `p : Y ⟶ V` be a flat
morphism of affine schemes and let `U ⊆ V` be quasi-compact and quasi-separated. Then the centre
of `[g₀ : ⋯ : gₘ]` extends along `p` to the centre of the pulled back rational map on `p⁻¹(U)`. -/
theorem C1573.map_centre_appTop (p : Y ⟶ V) [Flat p] (hU : IsCompact (U : Set V))
    (hU' : IsQuasiSeparated (U : Set V)) :
    (centre (restr U) I g).map p.appTop.hom =
      centre (restr (p ⁻¹ᵁ U)) (I.map p.appTop.hom) (fun l => p.app U (g l)) := by
  -- the pushout square of sections, by flat base change over a qcqs open
  have hiso := AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_id_snd (f := p)) (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U)
    (by simp) (by simp) (by simp) (isAffineOpen_top V) (isAffineOpen_top Y) hU hU'
  have hpo := (AlgebraicGeometry.isIso_pushoutSection_iff ..).mp hiso
  have e1 : ∀ (Z : Scheme.{u}) (W : Z.Opens) (h : W ≤ (𝟙 Z : Z ⟶ Z) ⁻¹ᵁ ⊤),
      Scheme.Hom.appLE (𝟙 Z) ⊤ W h = Z.presheaf.map (homOfLE le_top).op := fun Z W h => by
    simp [Scheme.Hom.appLE]
  have e2 : p.appLE ⊤ ⊤ (by simp) = p.appTop :=
    Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top p _
  have e3 : p.appLE U (p ⁻¹ᵁ U) (by simp) = p.app U := Scheme.Hom.appLE_eq_app p
  rw [e1, e2, e3, e1] at hpo
  let : Algebra Γ(V, ⊤) Γ(V, U) := (restr U).toAlgebra
  let : Algebra Γ(V, ⊤) Γ(Y, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(Y, p ⁻¹ᵁ U) := (restr (p ⁻¹ᵁ U)).toAlgebra
  let : Algebra Γ(V, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  let : Algebra Γ(V, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
    (p.appTop ≫ Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  have h1 : IsScalarTower Γ(V, ⊤) Γ(Y, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun z => rfl
  have h2 : IsScalarTower Γ(V, ⊤) Γ(V, U) Γ(Y, p ⁻¹ᵁ U) := by
    refine .of_algebraMap_eq fun z => ?_
    change (p.appTop ≫ Y.presheaf.map (homOfLE le_top).op) z =
      (V.presheaf.map (homOfLE le_top).op ≫ p.app U) z
    rw [Scheme.Hom.appTop, Scheme.Hom.naturality]
    rfl
  have hflat : Module.Flat Γ(V, ⊤) Γ(Y, ⊤) := by
    have := p.flat_appLE (isAffineOpen_top V) (isAffineOpen_top Y) (by simp)
    rwa [e2] at this
  have hAP : Algebra.IsPushout Γ(V, ⊤) Γ(Y, ⊤) Γ(V, U) Γ(Y, p ⁻¹ᵁ U) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact hpo.flip
  exact map_centre hAP.out I g

omit [IsAffine Y] in
/-- Transport of the centre along an equality of opens. -/
theorem C1573.centre_congr_opens {W W' : Y.Opens} (h : W = W') (J : Ideal Γ(Y, ⊤))
    (k : Fin (m + 1) → Γ(Y, W)) :
    centre (restr W) J k =
      centre (restr W') J (fun l => Y.presheaf.map (eqToHom h.symm).op (k l)) := by
  subst h
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The two extensions of the centre along flat morphisms agree** as soon as the data of the
rational map do: the preimages of `U`, the extensions of `I`, and the pulled back functions. -/
theorem C1573.map_centre_appTop_eq (p q : Y ⟶ V) [Flat p] [Flat q] (hU : IsCompact (U : Set V))
    (hU' : IsQuasiSeparated (U : Set V)) (hpq : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
    (hI : I.map p.appTop.hom = I.map q.appTop.hom)
    (hg : ∀ l, Y.presheaf.map (eqToHom hpq.symm).op (p.app U (g l)) = q.app U (g l)) :
    (centre (restr U) I g).map p.appTop.hom = (centre (restr U) I g).map q.appTop.hom := by
  rw [map_centre_appTop U I g p hU hU', map_centre_appTop U I g q hU hU',
    centre_congr_opens hpq, hI]
  exact congrArg _ (funext hg)

end Stacks.ProjectiveExtension

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Centre

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
  {φ : yoneda.obj U ⟶ X}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))]
  (U₀ : ((BigFppfOver.toScheme B S hS).obj U).Opens)
  (I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) {m : ℕ}
  (g₀ : Fin (m + 1) → Γ((BigFppfOver.toScheme B S hS).obj U, U₀))

include he in
/-- **The centre of a rational map on an affine atlas is invariant under the relation** when the
data of the rational map are: the two preimages of the open, the two extensions of the ideal and
the two pullbacks of the functions agree on the relation. -/
theorem C1573.isInvariantSubscheme_centreSheaf
    (hU : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hU' : _root_.IsQuasiSeparated (U₀ : Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hpq : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀ =
      (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀)
    (hI : I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).appTop.hom =
      I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).appTop.hom)
    (hg : ∀ l, ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)).presheaf.map
        (eqToHom hpq.symm).op
        (((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).app U₀ (g₀ l)) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).app U₀ (g₀ l)) :
    IsInvariantSubscheme B S hS hs
      (Subobject.mk (Stacks.ProjectiveExtension.C1573.centreSheaf U₀ I₀ g₀).subschemeι) := by
  have := etale_atlasRelationSource B S hS hs he
  have := etale_atlasRelationTarget B S hS hs he
  exact isInvariantSubscheme_ofIdealTop B S hS hs _
    (Stacks.ProjectiveExtension.C1573.map_centre_appTop_eq U₀ I₀ g₀ _ _ hU hU' hpq hI hg)

include he in
/-- **The centre of a rational map on an affine atlas descends to a closed subspace** whose
preimage on the atlas is the centre, under the compatibility hypotheses of
`AlgebraicGeometry.Space.C1573.isInvariantSubscheme_centreSheaf`. -/
theorem C1573.exists_closedSubspace_preimage_eq_centreSheaf (hX : IsAlgebraicSpace B S hS X)
    (hU : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hU' : _root_.IsQuasiSeparated (U₀ : Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hpq : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀ =
      (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀)
    (hI : I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).appTop.hom =
      I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).appTop.hom)
    (hg : ∀ l, ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)).presheaf.map
        (eqToHom hpq.symm).op
        (((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).app U₀ (g₀ l)) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).app U₀ (g₀ l)) :
    ∃ Z : ClosedSubspaces B S hS X, Z.1.preimage φ =
      subschemePoints B S hS
        (Subobject.mk (Stacks.ProjectiveExtension.C1573.centreSheaf U₀ I₀ g₀).subschemeι) := by
  have hinv := isInvariantSubscheme_centreSheaf hs he U₀ I₀ g₀ hU hU' hpq hI hg
  refine ⟨⟨invariantSubspace B S hS φ _,
    isClosedSubspace_invariantSubspace_subschemeι B S hS ⟨X, hX⟩ hs he _ hinv⟩, ?_⟩
  exact preimage_invariantSubspace B S hS hs _ hinv

end Centre

end AlgebraicGeometry.Space

end
