module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The preimage of the square of a quasi-compact neighbourhood of a closed set

Let `Z ⊆ |X|` be closed and `V ⊆ X` an open subspace whose points contain `Z`, so that the open
complement of `Z` and `V` form an elementary distinguished square of `X` (Stacks 08GM). For a
morphism `g' : X' ⟶ X` of algebraic spaces the preimages `|g'|⁻¹(Z)` and `g'⁻¹(V)` form the
corresponding square of `X'`, and the étale member `g'⁻¹(V)` of that square is the fibre product
`V ×_X X'`.

## Main results

* `AlgebraicGeometry.Space.isElementaryDistinguishedSquare_openSubspaceOfPoints_preimage`: the
  square of `X'`.
* `AlgebraicGeometry.Space.edsComplementPoints_preimage`: its closed complement is `|g'|⁻¹(Z)`.
* `AlgebraicGeometry.Space.edsEtalePreimageHom` and
  `AlgebraicGeometry.Space.isPullback_edsEtalePreimageHom`: `g'⁻¹(V) = V ×_X X'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- **The preimage square.** If `Z ⊆ |X|` is closed and contained in the points of the open
subspace `V`, then for `g' : X' ⟶ X` the open complement of `|g'|⁻¹(Z)` and `g'⁻¹(V)` form an
elementary distinguished square of `X'`. -/
theorem isElementaryDistinguishedSquare_openSubspaceOfPoints_preimage (g' : X' ⟶ X)
    (Z : Set (points B S hS X.1))
    (hZ : IsClosed Z) (V : Subfunctor X.1) (hV : IsOpenSubspace B S hS V)
    (hZV : Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    IsElementaryDistinguishedSquare B S hS X'.2
      (openSubspaceOfPoints B S hS X'.1 (pointsMap B S hS X'.1 g'.hom ⁻¹' Z)ᶜ)
      (V.preimage g'.hom).ι :=
  isElementaryDistinguishedSquare_openSubspaceOfPoints B S hS X'.2 _
    (hZ.preimage (continuous_pointsMap B S hS g'.hom)) _
    (isOpenSubspace_preimage B S hS g'.hom V X.2 X'.2 hV)
    ((Set.preimage_mono hZV).trans_eq (range_pointsMap_preimage_ι B S hS g'.hom V).symm)

/-- The closed complement of the open member of the preimage square is `|g'|⁻¹(Z)`. -/
theorem edsComplementPoints_preimage (g' : X' ⟶ X) (Z : Set (points B S hS X.1)) :
    edsComplementPoints B S hS
        (openSubspaceOfPoints B S hS X'.1 (pointsMap B S hS X'.1 g'.hom ⁻¹' Z)ᶜ) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' Z := by
  rw [edsComplementPoints, range_pointsMap_ι_openSubspaceOfPoints, compl_compl]

variable {Uo : Subfunctor X.1} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo V.ι) (g' : X' ⟶ X)
  {Uo' : Subfunctor X'.1}
  (hsq' : IsElementaryDistinguishedSquare B S hS X'.2 Uo' (V.preimage g'.hom).ι)

/-- The morphism `g'⁻¹(V) ⟶ V` of the étale members of the two squares. -/
def edsEtalePreimageHom : edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq :=
  ObjectProperty.homMk (V.fromPreimage g'.hom)

/-- **The étale member of the preimage square is the fibre product `V ×_X X'`.** -/
theorem isPullback_edsEtalePreimageHom :
    IsPullback (edsEtalePreimageHom hsq g' hsq') (edsEtaleHom B S hS hsq')
      (edsEtaleHom B S hS hsq) g' :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
    (Subfunctor.isPullback_preimage g'.hom V)

end AlgebraicGeometry.Space

end
