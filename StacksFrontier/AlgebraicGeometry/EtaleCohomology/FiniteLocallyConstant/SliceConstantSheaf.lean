module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Recognizing the restriction of a sheafified presheaf as a constant sheaf

Let `J` be a Grothendieck topology on `C`, let `V` be an object of `C` and let `P` be a
presheaf of types on `C`. The restriction of the sheafification of `P` to the localized site
`C/V` is a constant sheaf as soon as some constant presheaf on `C/V` maps to the restriction
of `P` by a map which is locally bijective for the localized topology: sheafification turns a
locally bijective map into an isomorphism, and the restriction of a sheafification is already
a sheaf, so no second sheafification intervenes.

This is the mechanism behind the local constancy of a representable sheaf on the small étale
site: on a member of a trivializing covering, the finitely many sections of the representing
object give a map from a finite constant presheaf which is locally bijective.

Nothing here is specific to schemes.

## Main results

* `Stacks.ConstantSheaf.presheafToSheafObjIso` — a locally bijective map from a presheaf to a
  sheaf identifies the sheafification of the source with the target.
* `Stacks.ConstantSheaf.constantSheafObjIsoOverPullback` — the criterion above: a locally
  bijective map from a constant presheaf on `C/V` to the restriction of `P` identifies the
  constant sheaf with the restriction of the sheafification of `P`.

## Implementation notes

Restriction along `Over.forget V` is `Functor.whiskerLeft (Over.forget V).op` on presheaves
and `GrothendieckTopology.overPullback` on sheaves; the two agree on underlying presheaves by
definition. Local injectivity and local surjectivity transfer from `J` to `J.over V` along
this restriction because the sections of a restricted presheaf are literally the sections of
the original, and a covering sieve of `V.left` corresponds to a covering sieve of the
localized site under `Sieve.overEquiv`.

Local bijectivity is passed as explicit hypotheses rather than instances: at the point of use
the morphism is a composite built by hand, and instance synthesis for such a composite is
brittle.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (V : C)

section Transfer

variable {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)

/-- Local injectivity is inherited by the restriction to a localized site: the equalizer sieve
of two sections of the restricted presheaf is the sieve of `C/V` corresponding to the
equalizer sieve of the same two sections of `P`. -/
public instance isLocallyInjective_whiskerLeft_overForget
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective (J.over V) (Functor.whiskerLeft (Over.forget V).op f) where
  equalizerSieve_mem _ _ h :=
    J.overEquiv_symm_mem_over _ _ (Presheaf.equalizerSieve_mem J f _ _ h)

/-- Local surjectivity is inherited by the restriction to a localized site: the image sieve of
a section of the restricted presheaf is the sieve of `C/V` corresponding to the image sieve of
the same section of `Q`. -/
public instance isLocallySurjective_whiskerLeft_overForget
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective (J.over V) (Functor.whiskerLeft (Over.forget V).op f) where
  imageSieve_mem s := J.overEquiv_symm_mem_over _ _ (Presheaf.imageSieve_mem J f s)

end Transfer

/-- A locally bijective morphism from a presheaf of types to the underlying presheaf of a
sheaf identifies the sheafification of the source with that sheaf. -/
public def presheafToSheafObjIso {P : Cᵒᵖ ⥤ Type max u v} {Q : Sheaf J (Type max u v)}
    (ψ : P ⟶ Q.obj) (hinj : Presheaf.IsLocallyInjective J ψ)
    (hsurj : Presheaf.IsLocallySurjective J ψ) :
    (presheafToSheaf J (Type max u v)).obj P ≅ Q := by
  have := hinj
  have := hsurj
  have hfac : toSheafify J P ≫ sheafifyLift J ψ Q.property = ψ := toSheafify_sheafifyLift J ψ _
  have hinj' : Presheaf.IsLocallyInjective J (sheafifyLift J ψ Q.property) := by
    rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P), hfac]
    infer_instance
  have hsurj' : Presheaf.IsLocallySurjective J (sheafifyLift J ψ Q.property) := by
    rw [← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P), hfac]
    infer_instance
  have : IsIso (ObjectProperty.homMk (sheafifyLift J ψ Q.property) :
      (presheafToSheaf J (Type max u v)).obj P ⟶ Q) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hinj', hsurj'⟩
  exact asIso (ObjectProperty.homMk (sheafifyLift J ψ Q.property))

/-- **The constancy criterion.** If a constant presheaf on the localized site `C/V` maps
locally bijectively to the restriction of a presheaf `P`, then the restriction to `C/V` of the
sheafification of `P` is the constant sheaf with the same value. -/
public def constantSheafObjIsoOverPullback {E : Type max u v} {P : Cᵒᵖ ⥤ Type max u v}
    (φ : (Functor.const (Over V)ᵒᵖ).obj E ⟶ (Over.forget V).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective (J.over V) φ)
    (hsurj : Presheaf.IsLocallySurjective (J.over V) φ) :
    (constantSheaf (J.over V) (Type max u v)).obj E ≅
      (J.overPullback (Type max u v) V).obj
        ((presheafToSheaf J (Type max u v)).obj P) := by
  have := hinj
  have := hsurj
  have h₁ : Presheaf.IsLocallyInjective (J.over V)
      (φ ≫ Functor.whiskerLeft (Over.forget V).op (toSheafify J P)) := inferInstance
  have h₂ : Presheaf.IsLocallySurjective (J.over V)
      (φ ≫ Functor.whiskerLeft (Over.forget V).op (toSheafify J P)) := inferInstance
  exact presheafToSheafObjIso (J.over V)
    (Q := (J.overPullback (Type max u v) V).obj
      ((presheafToSheaf J (Type max u v)).obj P))
    (φ ≫ Functor.whiskerLeft (Over.forget V).op (toSheafify J P)) h₁ h₂

end Stacks.ConstantSheaf
