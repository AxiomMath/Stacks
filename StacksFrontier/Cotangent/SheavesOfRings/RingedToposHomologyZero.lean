module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Cotangent.SheavesOfRings.HomologyZero
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposCotangentComplex

/-!
# The zeroth homology of the cotangent complex of a morphism of ringed topoi

For a morphism of ringed topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` the zeroth homology of
the cotangent complex `L_f` is the sheaf of relative differentials `Ω_f`, both being formed from
the inverse-image form `f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map.

The same inverse-image form is what names the three notions attached to such a morphism: a
`Y`-derivation of `𝒪_C` is an `f♯`-derivation, the sheaf of differentials `Ω_{X/Y} = Ω_f` is
the module of differentials of `f♯`, and it carries a universal `Y`-derivation `d_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.Derivation`: a `Y`-derivation of `𝒪_C` with values in a
  sheaf of `𝒪_C`-modules.
* `AlgebraicGeometry.RingedToposHom.differentials` is `Ω_f = Ω_{X/Y}`.
* `AlgebraicGeometry.RingedToposHom.universalDerivation` is `d_{X/Y}`.

## Main results

* `AlgebraicGeometry.RingedToposHom.existsUnique_descDerivation`: `d_{X/Y}` is universal, that
  is, every `Y`-derivation factors through it by a unique morphism of sheaves of modules.
* `AlgebraicGeometry.RingedToposHom.cotangentComplex_homologyZeroIso`: `H⁰(L_f) = Ω_f`.

## Implementation notes

The source states an equality of sheaves of modules; the sheaf of relative differentials is a
corepresenting object, so the identification is stated as an isomorphism in the category of
modules over the structure sheaf of the source.

Nothing about derivations is rebuilt here: the three definitions are the ones of the module of
differentials of a morphism of sheaves of commutative rings on a site, read at the morphism
`f♯ : f⁻¹𝒪_D ⟶ 𝒪_C`, which is exactly what the source prescribes.

## References

* [Stacks Project, Tag 08V0](https://stacks.math.columbia.edu/tag/08V0)
* [Stacks Project, Tag 04BQ](https://stacks.math.columbia.edu/tag/04BQ), the sheaf of
  differentials of a morphism of ringed topoi, and
  [Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of differentials it is
  read off from.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- **Stacks 04BQ, part (1).** A `Y`-derivation `D : 𝒪_C ⟶ F` with values in a sheaf `F` of
`𝒪_C`-modules, for a morphism of ringed topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`: by
definition an `f♯`-derivation, that is, a derivation of `𝒪_C` relative to the inverse-image
form `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map. -/
@[stacks 04BQ "a Y-derivation is an f♯-derivation", ega "IV 16.5.1" "more general"]
abbrev Derivation (F : Sheaf.targetModules.{u, v, w} X.J X.O) :=
  F.val.Derivation' f.fSharpInverseImage.hom

/-- **Stacks 04BQ, part (2).** The sheaf of differentials `Ω_{X/Y} = Ω_f = Ω_{𝒪_C/f⁻¹𝒪_D}` of a
morphism of ringed topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`: the sheaf of differentials of
the inverse-image form `f⁻¹𝒪_D ⟶ 𝒪_C` of its structure map, a sheaf of `𝒪_C`-modules on the
source site. -/
@[stacks 04BQ "the sheaf of differentials"]
noncomputable abbrev differentials : Sheaf.targetModules.{u, v, w} X.J X.O :=
  moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w}
    ((inverseImageCommRingFunctor f.toToposHom).obj Y.O) X.O f.fSharpInverseImage

/-- **Stacks 04BQ.** The universal `Y`-derivation `d_{X/Y} : 𝒪_C ⟶ Ω_{X/Y}` that the sheaf of
differentials comes equipped with: the universal derivation of the inverse-image form of the
structure map. -/
@[stacks 04BQ "the universal Y-derivation d_{X/Y}"]
noncomputable def universalDerivation : f.Derivation f.differentials :=
  universalDerivationOfSite.{v, u, max u v w, max u v w}
    ((inverseImageCommRingFunctor f.toToposHom).obj Y.O) X.O f.fSharpInverseImage

/-- **Stacks 04BQ.** `d_{X/Y}` is universal among `Y`-derivations: every `Y`-derivation with
values in a sheaf of `𝒪_C`-modules factors through it by a unique morphism of sheaves of
modules. -/
@[stacks 04BQ "universality of d_{X/Y}"]
theorem existsUnique_descDerivation (F : Sheaf.targetModules.{u, v, w} X.J X.O)
    (D : f.Derivation F) :
    ∃! g : f.differentials ⟶ F, (f.universalDerivation).postcomp g.val = D :=
  _root_.AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{v, u, max u v w,
    max u v w} ((inverseImageCommRingFunctor f.toToposHom).obj Y.O) X.O f.fSharpInverseImage F D

/-- **Stacks 08V0.** The zeroth homology of the cotangent complex of a morphism of ringed topoi
is its sheaf of relative differentials: `H⁰(L_f) = Ω_f`. -/
@[stacks 08V0]
noncomputable def cotangentComplex_homologyZeroIso :
    (f.cotangentComplex).homology 0 ≅ f.differentials :=
  Sheaf.cotangentComplex_homologyZeroIso.{u, v, w} X.J f.fSharpInverseImage

end AlgebraicGeometry.RingedToposHom

end
