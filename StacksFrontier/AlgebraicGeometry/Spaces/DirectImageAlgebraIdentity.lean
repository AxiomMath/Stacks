module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage

/-!
# The direct image of the structure sheaf along an identity, as an algebra

For an algebraic space `Y`, the direct image of `𝒪_Y` along the identity of `Y` is isomorphic to
`𝒪_Y` as an `𝒪_Y`-algebra.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.ofHomIsoOfHomId`: an invertible algebra structure map
  presents its target as the unit algebra.
* `AlgebraicGeometry.Space.pushforwardAlgebraUnitIso`: the isomorphism `(𝟙_Y)_* 𝒪_Y ≅ 𝒪_Y` of
  `𝒪_Y`-algebras.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

/-- An invertible algebra structure map presents its target as the unit algebra: if
`φ : 𝒪_F ⟶ R` is an isomorphism of sheaves of commutative rings, then `R` with `φ` as its
structure map is isomorphic, as an `𝒪_F`-algebra, to `𝒪_F` with the identity. -/
def ofHomIsoOfHomId {R : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}}
    (φ : structureSheaf B S hS F hF ≅ R) :
    AlgebraSheaf.ofHom (hF := hF) φ.hom ≅
      AlgebraSheaf.ofHom (hF := hF) (𝟙 (structureSheaf B S hS F hF)) where
  hom :=
    { right := φ.inv
      comm := fun U r => by
        change ConcreteCategory.hom ((φ.hom ≫ φ.inv).hom.app U) r = _
        rw [φ.hom_inv_id]
        rfl }
  inv :=
    { right := φ.hom
      comm := fun _ _ => rfl }
  hom_inv_id := AlgebraSheaf.Hom.ext φ.inv_hom_id
  inv_hom_id := AlgebraSheaf.Hom.ext φ.hom_inv_id

end AlgebraSheaf

/-- The direct image of `𝒪_Y` along the identity of an algebraic space `Y` is `𝒪_Y`, as an
`𝒪_Y`-algebra. -/
def pushforwardAlgebraUnitIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) :
    pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y :=
  haveI := isIso_fSharp_id B S hS Y
  AlgebraSheaf.ofHomIsoOfHomId (asIso (smallEtaleRingedToposHom B S hS (𝟙 Y)).fSharp)

end AlgebraicGeometry.Space

end
