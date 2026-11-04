module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTower
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubobjectSite
public import StacksFrontier.CategoryTheory.Sites.OpenMapFunctorSubsite
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSliceSheaf

/-!
# The two topoi of [Stacks, Tag 07KL] are slices

Let `X' ⊂ X` and `S' ⊂ S` be open subschemes with `X'` mapping into `S'`, let `G = h_{X'}` be
the sheaf on the small Zariski site of `X` represented by the open image of `X'`, and let
`F = u_{X/S}^{-1} G`.  Clause (d) of [Stacks, Tag 07KL] asserts that the square of
`Crystalline.GlobalCrystallineSituation.smallChangeBaseZariskiSquare` is obtained from
`u_{X/S}` by the localization of [Stacks, Tag 04H1].  Two of the three things that asserts are
proved here: that `Sh(X'_Zar)` is the slice `Sh(X_Zar)/G`, and that `(X'/S')_cris` is the slice
`(X/S)_cris/F`, in both cases with the equivalence given by restriction along the comparison
functor of sites.  The third — that the square so obtained is the localization square, and that
the two horizontal arrows are the localization morphisms `j_G` and `j_F` — is in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectLocalization.lean`, which
completes clause (d).

Both are instances of one statement,
`CategoryTheory.Stacks.Topos.Subterminal.sliceEquivalence`: a fully faithful continuous functor
of sites whose essential image is the support of a sheaf with subsingleton values exhibits the
smaller topos as the slice of the larger one at that sheaf.  That is [Stacks, Tag 0791] for a
subterminal sheaf, and it is used here rather than 0791 itself because 0791 is available only
for sheaves valued in the universe of the morphisms of the site, which is `Type u` for both
sites here, while both topoi take values in `Type (u + 1)`.

Below, the comparison functor is `IsOpenMap.functor` of `g`, the direct image of opens — not
`Over.forget` of the open `g(X')`.  That is the functor for which the square of sites commutes
on the nose, by `Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens`.
Above, it is change of divided power base, and there the hypothesis
`Crystalline.DividedPowerScheme.IsInducedOpen` on `f` is needed and cannot be dropped: without
it change of base is not essentially surjective onto the subcategory that `F` cuts out, the
factorization `T ⟶ S'` of an object lying over `X'` being a morphism of divided power schemes
only when the divided power structure of `S'` is induced from that of `S`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.openSubobjectSheaf` — the sheaf `F`, in the spelling
  in which it is a restriction rather than a sheafification.
* `Crystalline.GlobalCrystallineSituation.smallChangeBaseSliceEquivalence` —
  `(X'/S')_cris` is `(X/S)_cris/F`.
* `Crystalline.GlobalCrystallineSituation.opensSliceEquivalence` —
  `Sh(X'_Zar)` is `Sh(X_Zar)/G`.
* `Crystalline.GlobalCrystallineSituation.zariskiInverseImageOpenSubobjectSheafIso` — `F` is
  `u_{X/S}^{-1} G`.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  [IsOpenImmersion g]

/-- The sheaf `F = u_{X/S}^{-1} h_{X'}` of clause (d) of [Stacks, Tag 07KL], in the spelling in
which it is a restriction rather than a sheafification. -/
def openSubobjectSheaf (S S' : GlobalCrystallineSituation.{u}) (g : S.X ⟶ S'.X)
    [IsOpenImmersion g] : smallTopos S' :=
  ⟨(forgetToOpens S').op ⋙ opensRepr g.opensRange,
    isSheaf_forgetToOpensOpCompOpensRepr g.opensRange⟩

/-- **[Stacks, Tag 07KL], the crystalline half of clause (d).**  The crystalline topos of
`X'/S'` is the slice of the crystalline topos of `X/S` at `F = u_{X/S}^{-1} h_{X'}`, and the
equivalence is restriction along change of divided power base.

This is the identification `Cris(X/S)/u_{X/S}^{-1}h_{X'} = Cris(X'/S')` that the source's proof
makes, read at the level of topoi. -/
@[stacks 07KL "clause (d), the identification of (X'/S')_cris with the slice of (X/S)_cris at \
  F = u_{X/S}^{-1}h_{X'}.  That the square so obtained is the localization square of Stacks \
  04H1 is smallChangeBaseLocalizationSquare in SmallSite/OpenSubobjectLocalization.lean"]
def smallChangeBaseSliceEquivalence [IsOpenImmersion f.hom]
    (hf : DividedPowerScheme.IsInducedOpen f) :
    smallTopos S ≌ Over (openSubobjectSheaf S S' g) :=
  Stacks.Topos.Subterminal.sliceEquivalence
    (j := smallChangeBase S S' f g h)
    (fun B hB ↦ (nonempty_forgetToOpensOpCompOpensRepr_iff_essImage (h := h) hf B).mp hB)
    (nonempty_forgetToOpensOpCompOpensRepr_smallChangeBase (h := h))
    (isSheaf_forgetToOpensOpCompOpensRepr g.opensRange)
    (mem_smallTopology_iff_functorPushforward_mem (h := h))

section Zariski

variable (S S' : GlobalCrystallineSituation.{u}) (g : S.X ⟶ S'.X) [IsOpenImmersion g]

/-- **[Stacks, Tag 07KL], the Zariski half of clause (d).**  The small Zariski topos of `X'` is
the slice of the small Zariski topos of `X` at the sheaf `h_{X'}` represented by the open image
of `X'`, and the equivalence is restriction along the direct image of opens.

This is the source's "it is clear that `Sh(X'_Zar)` is the localization `Sh(X_Zar)/h_{X'}`".
No hypothesis on the divided power bases enters: this half is about the spaces alone. -/
@[stacks 07KL "clause (d), the identification of Sh(X'_Zar) with the slice of Sh(X_Zar) at \
  h_{X'}.  That the square so obtained is the localization square of Stacks 04H1 is \
  smallChangeBaseLocalizationSquare in SmallSite/OpenSubobjectLocalization.lean"]
def opensSliceEquivalence :
    Sheaf (Opens.grothendieckTopology S.X.carrier) (Type (u + 1)) ≌
      Over (opensReprSheaf (S := S') g.opensRange) :=
  haveI hgemb : Topology.IsOpenEmbedding g.base := g.isOpenEmbedding
  haveI hg : IsOpenMap g.base := hgemb.isOpenMap
  haveI := StacksOpenMapSite.full_functor hgemb
  haveI := hgemb.functor_isContinuous
  Stacks.Topos.Subterminal.sliceEquivalence
    (j := IsOpenMap.functor hg)
    (fun V hV ↦ (StacksOpenMapSite.essImage_functor_iff hg V).mpr
      ((nonempty_opensRepr_obj_iff (S := S') g.opensRange V).mp hV))
    (fun _ ↦ (nonempty_opensRepr_obj_iff (S := S') g.opensRange _).mpr
      (fun _ ⟨y, _, hy⟩ ↦ ⟨y, hy⟩))
    (isSheaf_opensRepr (S := S') g.opensRange)
    (StacksOpenMapSite.mem_grothendieckTopology_iff_functorPushforward_mem hgemb)

end Zariski

/-- **The sheaf of clause (d) is the inverse image of `h_{X'}`.**  The two spellings of `F`
differ by the sheafification in `CategoryTheory.Functor.sheafPullbackCocontinuous`, which is
trivial here because the restriction along the forgetful functor is already a sheaf. -/
def zariskiInverseImageOpenSubobjectSheafIso :
    (zariskiToposMorphism S').inverseImage.obj (opensReprSheaf g.opensRange) ≅
      openSubobjectSheaf S S' g :=
  zariskiInverseImageOpensReprIso g.opensRange

end Crystalline.GlobalCrystallineSituation

end
