module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens

/-!
# Forgetting the thickening of a small crystalline object

Fix a global crystalline situation `(p, (S, I, γ), X)`.  An object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` is a divided power thickening of `X` relative to `(S, I, γ)` whose
structure map `U ⟶ X` is an open immersion, so `U` is itself an object of the small Zariski site
`X_Zar` of `X`.  Forgetting the ambient divided power scheme and its divided powers is therefore a
functor `Cris(X/S) ⟶ X_Zar`, `(U, T, δ) ↦ U`.

Two forms of `X_Zar` are considered. Inside a chosen big Zariski site containing `X`, the small
Zariski site of `X` is the full subcategory `AlgebraicGeometry.SmallZariski` of the schemes over
`X` whose structure morphism is an open immersion; `forgetToZariski` is the functor into it,
`(U, T, δ) ↦ (U ⟶ X)`. The small Zariski site of `X` is also the lattice `X.Opens` of open
subsets of the space of `X`; `forgetToOpens` is the functor `(U, T, δ) ↦ U` which reads `U` as the
open image of `U ⟶ X`. The two agree under the comparison `AlgebraicGeometry.smallZariskiToOpens`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.forgetToZariski` — the functor `Cris(X/S) ⥤ X_Zar`
  sending `(U, T, δ)` to the open immersion `U ⟶ X`, inside a chosen big Zariski site.
* `Crystalline.GlobalCrystallineSituation.forgetToOpens` — the same functor read in the lattice
  of opens of `X`, sending `(U, T, δ)` to the open image of `U ⟶ X`.

## Main results

* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.isOpenImmersion_toX` — the
  structure map to `X` of an object of `Cris(X/S)` is an open immersion, as an instance.
* `Crystalline.GlobalCrystallineSituation.forgetToZariski_comp_smallZariskiToOpens` — the two
  readings of the forgetful functor agree under the identification of the small Zariski site of
  `X` with the opens of `X`.

## References

* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}}

/-- The structure map to `X` of an object of `Cris(X/S)` is an open immersion. -/
instance isOpenImmersion_toX (A : CrystallineThickening S) : IsOpenImmersion A.obj.toX :=
  A.property

end CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} {B : BigZariskiSite.{u}} {hX : B.Contains S.X}

/-- The functor `Cris(X/S) ⥤ X_Zar`, `(U, T, δ) ↦ (U ⟶ X)`, into the small Zariski site of `X`
taken inside a big Zariski site containing `X`. A morphism is sent to its component on the
thickened schemes. -/
def forgetToZariski (S : GlobalCrystallineSituation.{u}) (B : BigZariskiSite.{u})
    (hX : B.Contains S.X) : CrystallineThickening S ⥤ SmallZariski B S.X hX where
  obj A :=
    ⟨Over.mk (⟨A.obj.toX⟩ :
        (⟨A.obj.thickening.source,
          Scheme.size_lt_of_isOpenImmersion A.obj.toX hX⟩ : B.Schemes) ⟶ ⟨S.X, hX⟩),
      A.property⟩
  map {A C} f :=
    ObjectProperty.homMk (Over.homMk (⟨f.hom.sourceHom⟩ :
      (⟨A.obj.thickening.source,
          Scheme.size_lt_of_isOpenImmersion A.obj.toX hX⟩ : B.Schemes) ⟶
        ⟨C.obj.thickening.source, Scheme.size_lt_of_isOpenImmersion C.obj.toX hX⟩)
      (InducedCategory.hom_ext f.hom.toX_naturality))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the thickening of a small crystalline object keeps the thickened scheme. -/
@[simp]
theorem forgetToZariski_obj_scheme (A : CrystallineThickening S) :
    (SmallZariski.toScheme B S.X hX).obj ((forgetToZariski S B hX).obj A) =
      A.obj.thickening.source :=
  rfl

/-- The structure morphism of the image of a small crystalline object under
`Crystalline.GlobalCrystallineSituation.forgetToZariski` is its structure map to `X`. -/
@[simp]
theorem forgetToZariski_obj_structureMorphism (A : CrystallineThickening S) :
    smallZariskiOpenImmersion B S.X hX ((forgetToZariski S B hX).obj A) = A.obj.toX :=
  rfl

/-- `Crystalline.GlobalCrystallineSituation.forgetToZariski` sends a morphism to its component on
the thickened schemes. -/
@[simp]
theorem forgetToZariski_map_scheme {A C : CrystallineThickening S} (f : A ⟶ C) :
    (SmallZariski.toScheme B S.X hX).map ((forgetToZariski S B hX).map f) = f.hom.sourceHom :=
  rfl

/-- The functor `Cris(X/S) ⥤ X.Opens` sending an object `(U, T, δ)` to the open image of its
structure map `U ⟶ X`, and a morphism to the resulting inclusion of opens. -/
def forgetToOpens (S : GlobalCrystallineSituation.{u}) :
    CrystallineThickening S ⥤ S.X.Opens where
  obj A := A.obj.toX.opensRange
  map {A C} f := homOfLE (by
    change Set.range A.obj.toX ⊆ Set.range C.obj.toX
    rw [← f.hom.toX_naturality]
    rintro _ ⟨x, rfl⟩
    exact ⟨f.hom.sourceHom x, (Scheme.Hom.comp_apply _ _ x).symm⟩)

/-- The image of a small crystalline object under
`Crystalline.GlobalCrystallineSituation.forgetToOpens` is the open image of its structure map
to `X`. -/
@[simp]
theorem forgetToOpens_obj (A : CrystallineThickening S) :
    (forgetToOpens S).obj A = A.obj.toX.opensRange :=
  rfl

/-- Composing `Crystalline.GlobalCrystallineSituation.forgetToZariski` with the open-image
comparison `AlgebraicGeometry.smallZariskiToOpens` gives
`Crystalline.GlobalCrystallineSituation.forgetToOpens`. -/
theorem forgetToZariski_comp_smallZariskiToOpens (S : GlobalCrystallineSituation.{u})
    (B : BigZariskiSite.{u}) (hX : B.Contains S.X) :
    forgetToZariski S B hX ⋙ smallZariskiToOpens B S.X hX = forgetToOpens S :=
  rfl

end Crystalline.GlobalCrystallineSituation

end
