module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalRankTwo

/-!
# The pullback of the twist of a projective bundle

Let `γ : X' ⟶ X` be a morphism of schemes, `ℰ`, `ℰ'` quasi-coherent modules on `X`, `X'` and
`u : γ^*ℰ ⟶ ℰ'` an epimorphism. Let `h : 𝐏(ℰ') ⟶ 𝐏(ℰ)` be a morphism over `γ` which, over a
cover of `X'` by affine charts, is the `Proj` of a graded map sending a degree-one generator `x`
to the image of `x` under `u`. Then `h^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`, by the unique isomorphism
identifying the pulled-back tautological quotient of `ℰ` with the tautological quotient of `ℰ'`
precomposed with `u`.

## Main results

* `Stacks.Chow.GenuineChern.existsUnique_twistIso`: the unique isomorphism over `π'^*γ^*ℰ`.
* `Stacks.Chow.GenuineChern.twistPullbackIso` and
  `Stacks.Chow.GenuineChern.twistQuotientPullback_comp_twistPullbackIso`: the isomorphism and
  its defining property.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue Stacks.SymGraded

universe u

namespace Stacks.Chow.GenuineChern

variable {X X' : Scheme.{u}} (γ : X' ⟶ X) {E : X.Modules} {E' : X'.Modules}
  (hqc : IsQuasicoherentPieces E) (hqc' : IsQuasicoherentPieces E') [E.IsQuasicoherent]
  [E'.IsQuasicoherent]
  (u : (Scheme.Modules.pullback γ).obj E ⟶ E') [Epi u]
  (h : (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  (hh : h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)
  (hchart : ∀ x' : X', ∃ (U' : X'.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens)
    (hU : IsAffineOpen U) (hUU' : U' ≤ γ ⁻¹ᵁ U)
    (φ : (schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ
      (schemeSheafGradedAlgebra E' hqc').grading U')
    (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E' hqc').grading U') ≤
      (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U)).map φ),
    (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫ h =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ∧
      ∀ x : Γ(E, U),
        φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) =
          DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U')
              (E'.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
                  (op U) x))))

/-- The pulled-back tautological quotient `π'^*γ^*ℰ ⟶ h^*𝒪(1)` is an epimorphism. -/
instance epi_twistQuotientPullback : Epi (twistQuotientPullback γ hqc hqc' h hh) := by
  have := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E hqc
  unfold twistQuotientPullback
  infer_instance

include γ in
/-- The tautological quotient of `ℰ'` precomposed with `u` is an epimorphism. -/
instance epi_twistQuotientTarget : Epi (twistQuotientTarget γ hqc' u) := by
  have := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E' hqc'
  unfold twistQuotientTarget
  infer_instance

include hchart in
/-- **The pullback of the twist**: there is a unique isomorphism `h^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`
carrying the pulled-back tautological quotient of `ℰ` to the tautological quotient of `ℰ'`
precomposed with `u`. -/
theorem existsUnique_twistIso :
    ∃! φ : (Scheme.Modules.pullback h).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc',
      twistQuotientPullback γ hqc hqc' h hh ≫ φ.hom = twistQuotientTarget γ hqc' u := by
  choose U' hU' hx U hU hUU' φ hφ hc hdeg using hchart
  refine existsUnique_iso_of_pullback
    (fun x' => (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart (U' x') (hU' x'))
    ?_ _ _
    (Stacks.RelativeProj.isInvertible_pullback_obj h _
      (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E hqc))
    (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E' hqc') fun x' =>
      exists_chart_factorization γ hqc hqc' u h hh (hU' x') (hU x') (hUU' x') (φ x') (hφ x')
        (hc x') (hdeg x')
  refine top_le_iff.mp fun y _ => ?_
  have hy : y ∈ (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ
      U' ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase y) :=
    hx _
  rw [← chart_image_top _ _ (hU' _), Scheme.Hom.image_top_eq_opensRange] at hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hy⟩

/-- The isomorphism `h^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)` of `existsUnique_twistIso`. -/
def twistPullbackIso :
    (Scheme.Modules.pullback h).obj (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc' :=
  (existsUnique_twistIso γ hqc hqc' u h hh hchart).exists.choose

/-- The isomorphism `twistPullbackIso` carries the pulled-back tautological quotient of `ℰ` to
the tautological quotient of `ℰ'` precomposed with `u`. -/
@[reassoc]
theorem twistQuotientPullback_comp_twistPullbackIso :
    twistQuotientPullback γ hqc hqc' h hh ≫ (twistPullbackIso γ hqc hqc' u h hh hchart).hom =
      twistQuotientTarget γ hqc' u :=
  (existsUnique_twistIso γ hqc hqc' u h hh hchart).exists.choose_spec

end Stacks.Chow.GenuineChern

end
