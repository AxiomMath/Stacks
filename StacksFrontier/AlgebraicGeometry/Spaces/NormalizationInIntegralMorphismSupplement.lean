module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInIntegralMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions

/-!
# Normalization of an algebraic space in an integral morphism

For an integral morphism `f : Y ⟶ X` of algebraic spaces, the normalization of `X` in `Y` is
canonically isomorphic to `Y` over `X`.

## Main definitions

* `AlgebraicGeometry.Space.normalizationInIsoOfIsIntegralHom'`: the isomorphism between the
  normalization of `X` in `Y` and `Y`, over `X`.

## Main results

* `AlgebraicGeometry.Space.normalizationInIsoOfIsIntegralHom_w'`: composing this isomorphism
  with `f` gives the normalization morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : AffineAlgebraAntiEquivalence B S hS) {X Y : AlgebraicSpaces B S hS}

/-- For an integral morphism `f : Y ⟶ X` of algebraic spaces, the normalization `X' ⟶ X` of `X`
in `Y` is canonically isomorphic to `Y` over `X`. -/
@[stacks 0825]
def normalizationInIsoOfIsIntegralHom' (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    (normalizationIn B S hS E f hqc').obj ≅ Over.mk f :=
  have hint : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral :=
    isIntegral_pushforwardAlgebra_of_universallyClosed B S hS f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS Y.2 X.2 f.hom).1 hf).2
  have haff : IsAffineHom B S hS (Over.mk f).hom.hom :=
    ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS Y.2 X.2 f.hom).1 hf).1
  have hmono : Mono (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))) :=
    ⟨fun g h hgh => AlgebraSheaf.Hom.ext
      ((cancel_mono (AlgebraSheaf.integralClosureInclusion
        (pushforwardAlgebra B S hS (Over.mk f))).right).1
        (by rw [← AlgebraSheaf.comp_right, ← AlgebraSheaf.comp_right, hgh]))⟩
  have hiso : IsIso (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))) := by
    obtain ⟨ψ, hψ, -⟩ := AlgebraSheaf.existsUnique_hom_integralClosureSheaf
      (𝟙 (pushforwardAlgebra B S hS (Over.mk f))) hint
    refine ⟨ψ, ?_, hψ⟩
    rw [← cancel_mono (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))), Category.assoc, hψ, Category.comp_id,
      Category.id_comp]
  (ObjectProperty.ι _).mapIso
    (show normalizationIn B S hS E f hqc' ≅ (⟨Over.mk f, haff⟩ : AffineOver B S hS X) from
      Iso.unop
        ((E.equivalence X).unitIso.app (op (⟨Over.mk f, haff⟩ : AffineOver B S hS X)) ≪≫
          (E.equivalence X).inverse.mapIso
            ((E.pushforwardIso X).app (op (⟨Over.mk f, haff⟩ : AffineOver B S hS X)) ≪≫
              ObjectProperty.isoMk
                (P := (AlgebraSheaf.IsQuasicoherent :
                  ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2)))
                (E.pushforward_obj X ⟨Over.mk f, haff⟩ ≪≫
                  (asIso (AlgebraSheaf.integralClosureInclusion
                    (pushforwardAlgebra B S hS (Over.mk f)))).symm))))

/-- The identification of the normalization of `X` in `Y` with `Y` is over `X`: composing it
with `f` gives the normalization morphism `ν : X' ⟶ X`. -/
theorem normalizationInIsoOfIsIntegralHom_w' (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent) :
    (normalizationInIsoOfIsIntegralHom' B S hS E f hf hqc').hom.left ≫ f =
      (normalizationIn B S hS E f hqc').obj.hom :=
  Over.w _

end AlgebraicGeometry.Space

end
