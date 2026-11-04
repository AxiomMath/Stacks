module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeRelativeSpec
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraInclusion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The punctured cone in the cone, as relative spectra of twist algebras

Let `A` be a nonnegatively graded ring, `P = Proj A`, `X = Spec A`, let `π : L ⟶ P` be the cone
of the truncation algebra `B`, `σ : L ⟶ X` its structure morphism and `U = X ∖ V(A₊)`. With
`L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` and `U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`, the inclusion
`⨁_{m ≥ 0} 𝒪_P(m) ↪ ⨁_{m ∈ ℤ} 𝒪_P(m)` of algebras induces a morphism
`Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L`. This file shows that it is the open immersion of the punctured
cone in the cone, and that the square

  `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L`,
  `U ⟶ X`,

with left vertical the identification
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIsoOpenU` and right
vertical `σ`, commutes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.openUInLOver`: the open immersion of the punctured
  cone in the cone, as a morphism over `P`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeRelativeSpecTwistAlgebra`: the morphism
  `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` of relative spectra over `P` induced by
  the inclusion of the two twist algebras.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneProjIsoRelativeSpecTwistAlgebra`:
  `L = Proj B ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` as an isomorphism of schemes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIsoTwistAlgebraViaDirectImage`:
  `L ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` over `P`, as the presentation of `L` as the relative spectrum
  of `π_* 𝒪_L` composed with the comparison of `π_* 𝒪_L` with the twist algebra.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeProj`: the morphism
  `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Proj B` of schemes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIsoOpenUOver`:
  `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` as an isomorphism of schemes over `X`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeProjOverSpecA`:
  `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L` as a morphism of schemes over `X`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneProjIsoRelativeSpecTwistAlgebra_hom_comp`: the
  identification `L ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` of schemes is one over `P`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIsoTwistAlgebraViaDirectImage_eq`:
  the identification through `π_* 𝒪_L` is
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeRelativeSpecTwistAlgebra_comp`: the
  morphism of relative spectra is the open immersion `U ⟶ L`, as morphisms over `P`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeRelativeSpecTwistAlgebra_left_eq`: the
  same identification between morphisms of schemes.
* `isOpenImmersion_puncturedToConeRelativeSpecTwistAlgebra_left`, in the same namespace: the
  morphism of relative spectra is an open immersion of schemes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.opensRange_puncturedToConeRelativeSpecTwistAlgebra_left`:
  its image in `L` is the punctured cone `U ⊆ L`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeRelativeSpecTwistAlgebra_left_comp`:
  the square over `X` commutes, as morphisms of schemes.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedToConeProj_comp_toSpecA`: the same square
  with the top arrow read into the cone `Proj B`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local instance] ProjAndSpec.isAffineHom_pi ProjAndSpec.isAffineHom_pi_restrict

/-- The open immersion of the punctured cone in the cone, as a morphism over `P = Proj A`. -/
def openUInLOver :
    Over.mk ((openUInL 𝒜).ι ≫ pi 𝒜) ⟶ Over.mk (pi 𝒜) :=
  Over.homMk (openUInL 𝒜).ι rfl

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` over `P = Proj A`
induced by the inclusion `⨁_{m ≥ 0} 𝒪_P(m) ↪ ⨁_{m ∈ ℤ} 𝒪_P(m)` of
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegToIntegerTwistAlgebraSheafHom`. -/
@[stacks 0EKG "the top-left arrow of the diagram, the morphism of relative spectra over P \
induced by the inclusion of the nonnegative twist algebra in the integral one"]
def puncturedToConeRelativeSpecTwistAlgebra :
    Over.mk (relativeSpecToBase (integerTwistAlgebraSheaf 𝒜)) ⟶
      Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜)) :=
  relativeSpecMapOfAlgebraHom (nonnegTwistAlgebraSheaf 𝒜) (integerTwistAlgebraSheaf 𝒜)
    (nonnegToIntegerTwistAlgebraSheafHom 𝒜)

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` is the open immersion
of the punctured cone in the cone, under the two presentations `L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`
and `U = Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m))`, as morphisms over `P = Proj A`. -/
@[stacks 0EKG "the top-left arrow of the diagram is the open immersion of the punctured cone in \
the cone, under the two presentations as relative spectra, as morphisms over P"]
theorem puncturedToConeRelativeSpecTwistAlgebra_comp :
    puncturedToConeRelativeSpecTwistAlgebra 𝒜 ≫ (coneRelativeSpecTwistAlgebraIso 𝒜).inv =
      (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).inv ≫ openUInLOver 𝒜 := by
  refine eq_of_pushforwardAlgebraMap_eq ?_
  have hsq := nonnegToIntegerTwistAlgebraSheafHom_comp_puncturedConeAlgebraSheafIso 𝒜
  have hcancel : nonnegToIntegerTwistAlgebraSheafHom 𝒜 =
      nonnegToIntegerTwistAlgebraSheafHom 𝒜 ≫ (puncturedConeAlgebraSheafIso 𝒜).hom ≫
        (puncturedConeAlgebraSheafIso 𝒜).inv := by
    rw [Iso.hom_inv_id, Category.comp_id]
  have hincl : nonnegToIntegerTwistAlgebraSheafHom 𝒜 =
      (coneAlgebraSheafIso 𝒜).hom ≫ coneToPuncturedConeAlgebra (truncationConeData 𝒜) ≫
        (puncturedConeAlgebraSheafIso 𝒜).inv :=
    hcancel.trans (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun φ => φ ≫ (puncturedConeAlgebraSheafIso 𝒜).inv) hsq)
        (Category.assoc _ _ _)))
  have hopen : pushforwardAlgebraMap (openUInLOver 𝒜) =
      coneToPuncturedConeAlgebra (truncationConeData 𝒜) :=
    Category.comp_id _
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_comp, hopen,
    coneRelativeSpecTwistAlgebraIso_inv, puncturedConeRelativeSpecTwistAlgebraIso_inv,
    puncturedToConeRelativeSpecTwistAlgebra,
    pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso,
    pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso,
    pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom, hincl]
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact Category.assoc _ _ _

/-- Reading `puncturedToConeRelativeSpecTwistAlgebra_comp` on the underlying schemes. -/
private theorem puncturedToConeRelativeSpecTwistAlgebra_left_comp_openUInL :
    (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
        (coneRelativeSpecTwistAlgebraIso 𝒜).inv.left =
      (puncturedConeRelativeSpecTwistAlgebraIso 𝒜).inv.left ≫ (openUInL 𝒜).ι :=
  congrArg (fun φ => (Over.forget (AlgebraicGeometry.Proj 𝒜)).map φ)
    (puncturedToConeRelativeSpecTwistAlgebra_comp 𝒜)

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m)) = L` followed by the
structure morphism `σ : L ⟶ X` is the identification `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` of
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeRelativeSpecTwistAlgebraIsoOpenU` followed
by the inclusion `U ⟶ X`. -/
@[stacks 0EKG "the left square of the diagram commutes: the top-left arrow followed by L → X is \
the left identification with U followed by the inclusion of U in X", ega "II 8.6.2" "special case"]
theorem puncturedToConeRelativeSpecTwistAlgebra_left_comp :
    (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
        (coneRelativeSpecTwistAlgebraIso 𝒜).inv.left ≫ toSpecA 𝒜 =
      (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ (ProjAndSpec.openU 𝒜).ι := by
  refine Eq.trans ?_ (puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom_comp_ι 𝒜).symm
  rw [Functor.mapIso_inv, Over.forget_map, ← Category.assoc,
    puncturedToConeRelativeSpecTwistAlgebra_left_comp_openUInL, Category.assoc]

/-! ### The cone as a relative spectrum, read on schemes -/

/-- The cone `L = Proj B` of the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` is, as a scheme, the
relative spectrum over `P = Proj A` of the algebra of nonnegative twists. -/
@[stacks 0EKG "L = Proj B is, as a scheme, the relative spectrum over P of the nonnegative \
twist algebra"]
def coneProjIsoRelativeSpecTwistAlgebra :
    AlgebraicGeometry.Proj (grading 𝒜) ≅
      Stacks.AffineAlgebraEquivalence.relativeSpec (nonnegTwistAlgebraSheaf 𝒜) :=
  (Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso (coneRelativeSpecTwistAlgebraIso 𝒜)

/-- The identification `L = Proj B ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` is one over `P`: followed by the
structure morphism of the relative spectrum it is the cone projection `π : L ⟶ P`. -/
@[stacks 0EKG "the identification of L = Proj B with the relative spectrum of the nonnegative \
twist algebra is one over P, as morphisms of schemes"]
theorem coneProjIsoRelativeSpecTwistAlgebra_hom_comp :
    (coneProjIsoRelativeSpecTwistAlgebra 𝒜).hom ≫
        relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜) =
      pi 𝒜 :=
  coneRelativeSpecTwistAlgebraIso_hom_left_comp 𝒜

/-! ### The cone as a relative spectrum by way of the direct image `π_* 𝒪_L` -/

section ViaDirectImage

attribute [local instance] isQuasicoherent_pushforwardAlgebra

/-- `L ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` over `P`, as the presentation of the cone as the relative
spectrum of its direct-image algebra `π_* 𝒪_L`
(`Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecIso`) followed by the comparison
`Stacks.AlgebraicGeometry.ProjConeTwist.coneAlgebraSheafIso` of `π_* 𝒪_L` with the algebra of
nonnegative twists. -/
@[stacks 0EKG "L is, over P, the relative spectrum of the nonnegative twist algebra by the route \
of the diagram: the presentation of L as the relative spectrum of pi_* O_L composed with the \
comparison of pi_* O_L with the direct sum of the twists O_P(m) over m at least 0",
  ega "II 8.7.3" "partial"]
def coneRelativeSpecIsoTwistAlgebraViaDirectImage :
    Over.mk (pi 𝒜) ≅ Over.mk (relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜)) :=
  coneRelativeSpecIso (truncationConeData 𝒜) ≪≫
    relativeSpecIsoOfAlgebraIso (relativeSpecToBase (pushforwardAlgebra (pi 𝒜)))
      (nonnegTwistAlgebraSheaf 𝒜)
      (pushforwardAlgebraIso (pushforwardAlgebra (pi 𝒜)) ≪≫ (coneAlgebraSheafIso 𝒜).symm)

/-- The identification of `L` with `Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` through `π_* 𝒪_L` is
`Stacks.AlgebraicGeometry.ProjConeTwist.coneRelativeSpecTwistAlgebraIso`. -/
@[stacks 0EKG "the route through pi_* O_L is the one-step identification of L with the relative \
spectrum of the nonnegative twist algebra"]
theorem coneRelativeSpecIsoTwistAlgebraViaDirectImage_eq :
    coneRelativeSpecIsoTwistAlgebraViaDirectImage 𝒜 = coneRelativeSpecTwistAlgebraIso 𝒜 := by
  refine Iso.ext (eq_of_pushforwardAlgebraMap_eq ?_)
  have hhom : (coneRelativeSpecIsoTwistAlgebraViaDirectImage 𝒜).hom =
      (coneRelativeSpecIso (truncationConeData 𝒜)).hom ≫
        (relativeSpecIsoOfAlgebraIso (relativeSpecToBase (pushforwardAlgebra (pi 𝒜)))
          (nonnegTwistAlgebraSheaf 𝒜)
          (pushforwardAlgebraIso (pushforwardAlgebra (pi 𝒜)) ≪≫
            (coneAlgebraSheafIso 𝒜).symm)).hom := rfl
  rw [hhom, pushforwardAlgebraMap_comp, coneRelativeSpecIso_hom,
    relativeSpecIsoOfAlgebraIso_hom, coneRelativeSpecTwistAlgebraIso_hom]
  simp only [pushforwardAlgebraMap_toRelativeSpecOfAlgebraIso, Iso.trans_inv, Iso.refl_inv,
    Category.assoc, Category.comp_id, Iso.inv_hom_id]

end ViaDirectImage

/-! ### The morphism of relative spectra is an open immersion of schemes -/

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` of schemes followed by
the identification `Spec_P(⨁_{m ≥ 0} 𝒪_P(m)) ≅ L` is the identification
`Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` followed by the open immersion `U ⟶ L`. -/
theorem puncturedToConeRelativeSpecTwistAlgebra_left_comp_inv :
    (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
        (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv =
      ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
          (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv ≫ (openUInL 𝒜).ι :=
  puncturedToConeRelativeSpecTwistAlgebra_left_comp_openUInL 𝒜

/-- As a morphism of schemes, `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` is the
identification `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U`, then the open immersion `U ⟶ L`, then the
identification `L ≅ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`. -/
@[stacks 0EKG "the top-left arrow of the diagram, as a morphism of schemes, is the open \
immersion of the punctured cone in L conjugated by the two relative-spectrum identifications"]
theorem puncturedToConeRelativeSpecTwistAlgebra_left_eq :
    (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left =
      ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
            (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv ≫
        (openUInL 𝒜).ι ≫ (coneProjIsoRelativeSpecTwistAlgebra 𝒜).hom := by
  rw [← Category.assoc, ← puncturedToConeRelativeSpecTwistAlgebra_left_comp_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` is an open immersion of
schemes. -/
@[stacks 0EKG "the top-left arrow of the diagram is an open immersion of schemes"]
instance isOpenImmersion_puncturedToConeRelativeSpecTwistAlgebra_left :
    IsOpenImmersion (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left := by
  have : IsOpenImmersion (((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
      (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv) := IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (coneProjIsoRelativeSpecTwistAlgebra 𝒜).hom :=
    IsOpenImmersion.of_isIso _
  rw [puncturedToConeRelativeSpecTwistAlgebra_left_eq]
  infer_instance

/-- Read through the identification of `L = Proj B` with `Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`, the
morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L` has image the punctured cone
`Stacks.AlgebraicGeometry.ProjAndSpecTruncation.openUInL`. -/
@[stacks 0EKG "the image in L = Proj B of the top-left arrow of the diagram, read through the \
identification of L with the relative spectrum, is the open punctured cone"]
theorem opensRange_puncturedToConeRelativeSpecTwistAlgebra_left :
    ((puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
        (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv).opensRange = openUInL 𝒜 := by
  have hrange : (((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
        (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv ≫ (openUInL 𝒜).ι).opensRange =
      openUInL 𝒜 := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  refine Eq.trans (TopologicalSpace.Opens.ext ?_) hrange
  exact congrArg (fun φ => Set.range φ.base)
    (puncturedToConeRelativeSpecTwistAlgebra_left_comp_inv 𝒜)

/-! ### The left square in the category of schemes over `X` -/

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Proj B` of schemes: the morphism of relative
spectra over `P` read on underlying schemes, followed by the identification
`Spec_P(⨁_{m ≥ 0} 𝒪_P(m)) ≅ Proj B` of
`Stacks.AlgebraicGeometry.ProjConeTwist.coneProjIsoRelativeSpecTwistAlgebra`. -/
@[stacks 0EKG "the top-left arrow of the diagram as a morphism of schemes whose target is the \
cone L = Proj B"]
def puncturedToConeProj :
    Stacks.AffineAlgebraEquivalence.relativeSpec (integerTwistAlgebraSheaf 𝒜) ⟶
      AlgebraicGeometry.Proj (grading 𝒜) :=
  (puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
    (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Proj B` is an open immersion. -/
instance isOpenImmersion_puncturedToConeProj :
    IsOpenImmersion (puncturedToConeProj 𝒜) :=
  letI : IsOpenImmersion (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv :=
    IsOpenImmersion.of_isIso _
  inferInstanceAs (IsOpenImmersion ((puncturedToConeRelativeSpecTwistAlgebra 𝒜).left ≫
    (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv))

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Proj B` followed by the structure morphism
`σ : L ⟶ X` is the identification with `U` followed by the inclusion `U ⟶ X`. -/
@[ega "II 8.6.2" "special case"]
theorem puncturedToConeProj_comp_toSpecA :
    puncturedToConeProj 𝒜 ≫ toSpecA 𝒜 =
      (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ (ProjAndSpec.openU 𝒜).ι :=
  Eq.trans (Category.assoc _ _ _) (puncturedToConeRelativeSpecTwistAlgebra_left_comp 𝒜)

/-- The identification `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` as an isomorphism of schemes over
`X = Spec A`, the source lying over `X` by the morphism to `L` followed by `σ : L ⟶ X` and the
target by the inclusion `U ⟶ X`. -/
@[stacks 0EKG "the left square as an isomorphism over X: the left identification of Spec_P of \
the integer twist algebra with U is an isomorphism of schemes over X, its source lying over X by \
the top-left arrow followed by L → X",
  ega "II 8.12.5" "special case",
  ega "II 8.6.2" "special case"]
def puncturedConeRelativeSpecTwistAlgebraIsoOpenUOver :
    Over.mk (puncturedToConeProj 𝒜 ≫ toSpecA 𝒜) ≅ Over.mk (ProjAndSpec.openU 𝒜).ι :=
  Over.isoMk (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜)
    (puncturedToConeProj_comp_toSpecA 𝒜).symm

/-- The morphism `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Proj B` as a morphism of schemes over
`X = Spec A`, the source lying over `X` by the identification with `U` followed by the inclusion
`U ⟶ X` and the cone by `σ : L ⟶ X`. -/
@[stacks 0EKG "the left square as a morphism over X: the top-left arrow of the diagram is a \
morphism of schemes over X, its source lying over X by the left identification with U followed \
by the inclusion of U in X"]
def puncturedToConeProjOverSpecA :
    Over.mk ((puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫
        (ProjAndSpec.openU 𝒜).ι) ⟶
      Over.mk (toSpecA 𝒜) :=
  Over.homMk (puncturedToConeProj 𝒜) (puncturedToConeProj_comp_toSpecA 𝒜)

end Stacks.AlgebraicGeometry.ProjConeTwist

end
