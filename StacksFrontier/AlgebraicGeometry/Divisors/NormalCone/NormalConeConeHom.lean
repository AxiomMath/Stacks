module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraConeHom
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.AlgebraHomComparison

/-!
# The normal cone is a closed subcone of the normal bundle

Let `i : Z ⟶ X` be an immersion of schemes, with normal cone `C_ZX = Spec_Z(𝒞_{Z/X,*})` and
normal bundle `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))` (Tag 0636). Divisors, Equation 0637 says that the
canonical surjection `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of graded algebras of Tag 0632 defines a
canonical **closed immersion `C_ZX ⟶ N_ZX` of cones over `Z`**. This file assembles that
statement:

* the morphism is `Stacks.Conormal.normalConeToNormalBundle`, the relative spectrum of the
  canonical map of algebra sheaves;
* it is a closed immersion, `Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle`, because
  that map is locally surjective;
* it is a morphism of cones over `Z` in the sense of Tag 062R from the cone
  `Stacks.Conormal.normalConeCone` to the vector bundle `Stacks.Conormal.normalBundleVectorBundle`,
  with graded part the canonical map `Stacks.Conormal.conormalSymmetricHom`: this is
  `Stacks.Conormal.normalConeToNormalBundleConeHom` below.

## Main definitions

* `Stacks.Conormal.normalConeToNormalBundleConeHom`: **`C_ZX ⟶ N_ZX` as a morphism of cones over
  `Z`.**

## Main results

* `Stacks.Conormal.normalConeToNormalBundleConeHom_f`: its morphism of total spaces is
  `Stacks.Conormal.normalConeToNormalBundle`.
* `Stacks.Conormal.isClosedImmersion_normalConeToNormalBundle_and_coneHom`: **Divisors,
  Equation 0637**, all of it.

## References

* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The canonical morphism `C_ZX ⟶ N_ZX` as a morphism of cones over `Z`**, in the sense of
Tag 062R: the relative spectrum of the canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of graded
algebras of Tag 0632, whose pullback on functions realizes that map on every homogeneous piece. -/
def normalConeToNormalBundleConeHom :
    AbstractCone.Hom (normalConeCone i) (normalBundleVectorBundle i).toAbstractCone :=
  haveI : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Stacks.RelativeSpec.gradedAlgebraSheaf Z (conormalAlgebra i).algebra
        (conormalAlgebra i).mul_comm_int) :=
    isQuasicoherent_conormalAlgebraSheaf i
  haveI := AbstractCone.isQuasicoherent_gradedAlgebraSheaf_symmetricAlgebra Z
    (conormalSheafDegreeOne i)
  GradedAlgebraCone.coneHom Z (Scheme.Modules.symmetricAlgebra_mul_comm Z
      (conormalSheafDegreeOne i)) (conormalAlgebra i).mul_comm_int (conormalSymmetricHom i)
    (Scheme.Modules.symmetricAlgebraPieceZeroIso Z (conormalSheafDegreeOne i))
    (AbstractCone.symmetricAlgebraPieceZeroIso_hom_one Z (conormalSheafDegreeOne i))
    (fun n hn => Scheme.Modules.isZero_symmetricAlgebra_piece Z (conormalSheafDegreeOne i) n hn)
    (conormalPieceZeroIso i) (conormalPieceZeroIso_hom_one i) (conormalAlgebra i).negative_isZero

/-- The morphism of total spaces of the morphism of cones `C_ZX ⟶ N_ZX` is the canonical
morphism `Stacks.Conormal.normalConeToNormalBundle`. -/
theorem normalConeToNormalBundleConeHom_f :
    (normalConeToNormalBundleConeHom i).f = normalConeToNormalBundle i :=
  (Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i)).symm

/-- The graded part of the morphism of cones `C_ZX ⟶ N_ZX` is the canonical map
`Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Tag 0632. -/
theorem normalConeToNormalBundleConeHom_graded :
    (normalConeToNormalBundleConeHom i).graded = (conormalSymmetricHom i).toHom :=
  rfl

/-- **Stacks Project, Tag 0637.** **The canonical surjection `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of
graded algebras defines a canonical closed immersion `C_ZX ⟶ N_ZX` of cones over `Z`.** The
morphism `Stacks.Conormal.normalConeToNormalBundle`, the relative spectrum of that surjection, is
a closed immersion, and it is the morphism of total spaces of a morphism of cones over `Z` from
the normal cone `Stacks.Conormal.normalConeCone` to the normal bundle
`Stacks.Conormal.normalBundleVectorBundle` whose graded part is the surjection. -/
@[stacks 0637 "the canonical closed immersion C_ZX → N_ZX of cones over Z"]
theorem isClosedImmersion_normalConeToNormalBundle_and_coneHom :
    IsClosedImmersion (normalConeToNormalBundle i) ∧
      ∃ φ : AbstractCone.Hom (normalConeCone i) (normalBundleVectorBundle i).toAbstractCone,
        φ.f = normalConeToNormalBundle i ∧ φ.graded = (conormalSymmetricHom i).toHom :=
  ⟨inferInstance, normalConeToNormalBundleConeHom i, normalConeToNormalBundleConeHom_f i,
    normalConeToNormalBundleConeHom_graded i⟩

end Stacks.Conormal

end
