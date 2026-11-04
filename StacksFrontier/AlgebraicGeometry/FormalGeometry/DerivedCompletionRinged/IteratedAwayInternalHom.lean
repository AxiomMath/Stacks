module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsComposition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayBaseChange

/-!
# Internal Hom out of two localizations, one after the other

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. For every sheaf of
`𝒪`-modules `H`,

`SheafHom_{𝒪_g}((𝒪_g)_f, SheafHom_𝒪(𝒪_g, H)) = SheafHom_𝒪(𝒪_{f g}, H)`,

the two sides being identified along `AlgebraicGeometry.RingedSite.awaySheafMulIso`, the
isomorphism `𝒪_{f g} ≅ (𝒪_g)_f` of sheaves of rings. This is the displayed identity in the proof
of Stacks Tag 0996(3), where `SheafHom_𝒪(𝒪_f, -)` is read on the `𝒪_g`-module
`SheafHom_𝒪(𝒪_g, H)`, hence as `SheafHom_{𝒪_g}((𝒪_g)_f, -)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayIteratedCoextendIso`: **the identity above**, as an
  isomorphism of functors on sheaves of modules.

## Implementation notes

Nothing about localization enters: the identity is the composition law
`Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsCompIso` for coextension of scalars,
applied to the two factorizations
`𝒪 ⟶ 𝒪_g ⟶ (𝒪_g)_f` and `𝒪 ⟶ 𝒪_{f g} ⟶ (𝒪_g)_f` of one and the same map, which agree by
`AlgebraicGeometry.RingedSite.toAwaySheaf_comp_awayMulToAwayAway`. The last factor
`SheafHom_{𝒪_{f g}}((𝒪_g)_f, -)` is the transport along `awaySheafMulIso`, an equivalence of
categories of modules by
`Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsEquivalence`.

Nothing here carries a `stacks` attribute: the identity is a step inside the proof of Tag
0996(3), not one of that tag's three clauses.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.SheafOfModules.CoextendScalars

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]

/-- A morphism of the structure sheaves of ringed sites, read as a morphism of sheaves of
not necessarily commutative rings, which is the form coextension of scalars takes. -/
abbrev forgetCommRingHom {R S : Sheaf X.J CommRingCat.{u}} (φ : R ⟶ S) :
    (sheafCompose X.J (forget₂ CommRingCat RingCat.{u})).obj R ⟶
      (sheafCompose X.J (forget₂ CommRingCat RingCat.{u})).obj S :=
  (sheafCompose X.J (forget₂ CommRingCat RingCat.{u})).map φ

/-- Inverting `g` and then `f` is inverting `f g`, read on the two factorizations of the
canonical map `𝒪 ⟶ (𝒪_g)_f` through `𝒪_g` and through `𝒪_{f g}`. -/
theorem forgetCommRingHom_toAwayAway
    (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    forgetCommRingHom X (toAwaySheaf g) ≫ forgetCommRingHom X (toAwayAwaySheaf X f g) =
      forgetCommRingHom X (toAwaySheaf (mulGlobalSection X f g)) ≫
        forgetCommRingHom X (awaySheafMulIso X f g).hom := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (sheafCompose X.J (forget₂ CommRingCat RingCat.{u})).map
    (toAwaySheaf_comp_awayMulToAwayAway X f g).symm

/-- **`SheafHom_𝒪(𝒪_f, SheafHom_𝒪(𝒪_g, H)) = SheafHom_𝒪(𝒪_{f g}, H)`.** Internal Hom out of
`𝒪_g` followed by internal Hom out of `(𝒪_g)_f` is internal Hom out of `𝒪_{f g}`, transported
along the identification `𝒪_{f g} ≅ (𝒪_g)_f` of sheaves of rings. This is the identity used in
the proof of Stacks Tag 0996(3). -/
def awayIteratedCoextendIso
    (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    coextendScalars.{u} (forgetCommRingHom X (toAwaySheaf g)) ⋙
        coextendScalars.{u} (forgetCommRingHom X (toAwayAwaySheaf X f g)) ≅
      coextendScalars.{u} (forgetCommRingHom X (toAwaySheaf (mulGlobalSection X f g))) ⋙
        coextendScalars.{u} (forgetCommRingHom X (awaySheafMulIso X f g).hom) :=
  (sheafCoextendScalarsCompIso (forgetCommRingHom X (toAwaySheaf g))
      (forgetCommRingHom X (toAwayAwaySheaf X f g))).symm ≪≫
    eqToIso (congrArg coextendScalars.{u} (forgetCommRingHom_toAwayAway X f g)) ≪≫
    sheafCoextendScalarsCompIso
      (forgetCommRingHom X (toAwaySheaf (mulGlobalSection X f g)))
      (forgetCommRingHom X (awaySheafMulIso X f g).hom)

end AlgebraicGeometry.RingedSite

end
