module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfPrincipalHomogeneousSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsToPrincipal

/-!
# The equivalence `G-Torsors ≌ G-Principal`

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over
`B`. The categories `G-Torsors` of Stacks 04UR and `G-Principal` of Stacks 04UN differ only in
the topology for which an object's total space is required to be locally trivial: fppf for the
first, fpqc for the second. An fppf covering is an fpqc covering, so the canonical functor
`G-Torsors ⥤ G-Principal` exists unconditionally, and when `G ⟶ B` is flat and locally of
finite presentation a principal homogeneous space is already an fppf torsor, so that functor is
an equivalence. This is the last clause of **Stacks 0CQJ**.

The canonical functor, the fact that a principal homogeneous space under such a `G` is an fppf
torsor, and the equivalence *over the big fppf site of `S`* are
`AlgebraicGeometry.Space.FppfTorsors.toPrincipal`,
`AlgebraicGeometry.Space.isFppfTorsor_of_isPrincipalHomogeneousSpace` and
`AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverPrincipal`. This module adds what they
leave implicit: the quasi-inverse as a *functor*, and the equivalence of the underlying
categories.

## Main definitions

* `AlgebraicGeometry.Space.principalToFppfTorsors`: the quasi-inverse functor
  `G-Principal ⥤ G-Torsors`, for `G ⟶ B` flat and locally of finite presentation.
* `AlgebraicGeometry.Space.fppfTorsorsEquivPrincipal`: **Stacks 0CQJ**, the last clause — for
  `G ⟶ B` flat and locally of finite presentation the canonical functor
  `G-Torsors ⥤ G-Principal` is an equivalence of categories.

## Implementation notes

`AlgebraicGeometry.Space.TorsorsFor` carries the trivializing covering property as an argument,
and `G-Torsors` and `G-Principal` are two of its values. They therefore share their objects'
data, their morphisms, their composition and their projection to the site, and differ only in
the proposition an object carries about its total space. Both comparison functors are
accordingly the identity on all of that data, and the unit and counit of the equivalence are
identities, which is why the equivalence of underlying categories recorded here refines to the
equivalence over the site recorded on
`AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverPrincipal`.

The object map of the quasi-inverse is `AlgebraicGeometry.Space.FppfTorsors.ofPrincipal`, which
already supplies the flatness and local finite presentation of the acting group `G_U` of an
object as base changes of those properties of `G ⟶ B`; only the action on morphisms is added
here.

## References

* [Stacks Project, Tag 0CQJ](https://stacks.math.columbia.edu/tag/0CQJ)
* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/- The canonical functor `G-Torsors ⥤ G-Principal`, which an fppf covering being an fpqc
covering supplies unconditionally. -/
add_to_stacks 0CQJ "the functor G-Torsors ⥤ G-Principal"
  AlgebraicGeometry.Space.FppfTorsors.toPrincipal

/-- The quasi-inverse of the canonical functor `G-Torsors ⥤ G-Principal`, for `G ⟶ B` flat and
locally of finite presentation: a principal homogeneous space is then an fppf torsor, with every
datum of the object and both components of a morphism unchanged. -/
def principalToFppfTorsors (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (hflat : IsFlat 𝒞 S hS G.obj.X.hom)
    (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom) :
    PrincipalHomogeneousSpaces hB G ⥤ FppfTorsors hB G where
  obj T := FppfTorsors.ofPrincipal hB G hflat hlfp T
  map φ :=
    { base := φ.base
      comp_sec := φ.comp_sec
      map := φ.map
      isPullback := φ.isPullback
      smul_comp := φ.smul_comp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The quasi-inverse functor `G-Principal ⥤ G-Torsors` lies over the big fppf site of `S`. -/
theorem principalToFppfTorsors_comp_projection (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (hflat : IsFlat 𝒞 S hS G.obj.X.hom)
    (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom) :
    principalToFppfTorsors hB G hflat hlfp ⋙ FppfTorsors.projection hB G =
      PrincipalHomogeneousSpaces.projection hB G :=
  rfl

/-- **Stacks 0CQJ.** For `G ⟶ B` flat and locally of finite presentation the canonical functor
`G-Torsors ⥤ G-Principal` is an equivalence of categories, with quasi-inverse the functor
reading a principal homogeneous space as an fppf torsor and with identity unit and counit. -/
@[stacks 0CQJ "G-Torsors ≌ G-Principal, for G ⟶ B flat and locally of finite presentation"]
def fppfTorsorsEquivPrincipal (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (hflat : IsFlat 𝒞 S hS G.obj.X.hom)
    (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom) :
    FppfTorsors hB G ≌ PrincipalHomogeneousSpaces hB G where
  functor := FppfTorsors.toPrincipal hB G
  inverse := principalToFppfTorsors hB G hflat hlfp
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl
  functor_unitIso_comp _ := rfl

end AlgebraicGeometry.Space

end
