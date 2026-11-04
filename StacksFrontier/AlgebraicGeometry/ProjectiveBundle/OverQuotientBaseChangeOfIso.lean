module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotientBaseChange

/-!
# The quotient carried along the base change of projective bundles, for isomorphisms

Let `g : X ⟶ Y` be a morphism of schemes, `E` a quasi-coherent `𝒪_Y`-module and `E' ≅ g^*E`.
`Stacks.RelativeProj.TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange` compares the
quotient carried by `h ≫ b`, for `b : 𝐏(E') ⟶ 𝐏(E)` the base-change morphism, with the quotient
carried by `h` for the base-changed datum, given a compatibility of the identifications stated on
their underlying morphisms.  This file restates it with the compatibility stated for the
isomorphisms themselves, the form in which the comparison of fibres over two algebraic spaces in
the conormal clause of Stacks 0B4I produces it.

## Main results

* `Stacks.RelativeProj.TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange_of_iso`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

namespace TautologicalDatum

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- `TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange` with the compatibility of the
identifications stated for the isomorphisms. -/
theorem overQuotient_comp_projectiveBundleBaseChange_of_iso (D : TautologicalDatum Y E)
    {T : Scheme.{u}} {f : T ⟶ X} {f₂ : T ⟶ Y} (hf : f ≫ g = f₂) (F' : T.Modules)
    [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj E')
    (hF₂ : F' ≅ (Scheme.Modules.pullback f₂).obj E)
    (hcompat : hF₂ = hF ≪≫ (Scheme.Modules.pullback f).mapIso hE ≪≫
      (Scheme.Modules.pullbackComp f g).app E ≪≫ (Scheme.Modules.pullbackCongr hf).app E)
    (h : T ⟶ projectiveBundle X E') (hh : h ≫ projectiveBundleToBase X E' = f)
    (hh₂ : (h ≫ projectiveBundleBaseChange g E E' hE) ≫ projectiveBundleToBase Y E = f₂) :
    (D.overQuotient F' hF₂ (h ≫ projectiveBundleBaseChange g E E' hE) hh₂).IsEquivalent
      ((D.baseChange g E E' hE).overQuotient F' hF h hh) :=
  overQuotient_comp_projectiveBundleBaseChange g E E' hE D hf F' hF hF₂ (congrArg Iso.hom hcompat)
    h hh hh₂

end TautologicalDatum

end Stacks.RelativeProj

end
