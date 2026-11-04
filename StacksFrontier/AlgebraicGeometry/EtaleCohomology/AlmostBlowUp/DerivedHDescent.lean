module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DescentForACoarserTopology
import StacksCore.Tactic.StacksAttribute

/-!
# Almost blowup squares and the h topology

Let `B` be a big h site containing a scheme `S`, so that the big h category over `S` carries the
h topology `J`, and let `J' ≤ J` be a coarser topology on the same category — the fppf topology
in the source, since an fppf covering is an h covering. A sheaf of rings `𝒪` for `J` is then
also a sheaf of rings for `J'`, and the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})` whose derived direct image is `Rε_*`.

For an almost blowup square

```
E ⟶ X'
↓     ↓
Z ⟶  X
```

in the big h category over `S` — a finitely presented closed centre `Z ⊆ X`, a proper finitely
presented modification `b : X' ⟶ X` which is the blowup of the centre away from its supported
sections, and the exceptional subscheme `E = Z ×_X X'` — Stacks 0EWN says that the canonical
Mayer–Vietoris comparison `c^K_{X,Z,X',E}` of Stacks 0F16 is a quasi-isomorphism for every
object `K` of `D(𝒪_{J'})` in the essential image of `Rε_*`.

## Main results

* `AlgebraicGeometry.isPushout_sheafifiedYoneda_of_almostBlowUpSquare_bigH`: the h sheafified
  representables of an almost blowup square form a pushout square, `h_X^# = h_Z^# ∐_{h_E^#}
  h_{X'}^#`. This is the first hypothesis of Stacks 0F19.
* `AlgebraicGeometry.isCSquareIso_of_essImage_almostBlowUpSquare_bigH`: **Stacks 0EWN.**

## Implementation notes

The proof is the source's: the two hypotheses of Stacks 0F19 are checked and that lemma is
applied. The pushout hypothesis is Stacks 0EVD, in the form
`AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`: a square of sheafified representables
is a pushout exactly when every sheaf of sets sends it to a pullback square of sets, by
`CategoryTheory.Square.isPushout_iff_op_map_yoneda_isPullback` together with Yoneda's lemma for
sheaves of sets. The monomorphism hypothesis holds because `E ⟶ X'` is a monomorphism, being the
base change of the closed immersion `Z ⟶ X`, and because the sheafified Yoneda embedding carries
monomorphisms to monomorphisms.

The coarser topology is taken to be an arbitrary one, with the proof that it is coarser as a
hypothesis, rather than fixed to be the fppf topology: the argument uses nothing about `J'`
beyond `J' ≤ J`, which is how the source can quote Stacks 0F19 verbatim. The square is presented
as in `AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`, by an object of
`CategoryTheory.Square` whose vertices are, in order, the exceptional subscheme, the
modification, the centre and the base, together with an ideal sheaf on the base, the almost
blowup hypothesis, an identification of the centre with the closed subscheme it cuts out, and
the requirement that the square of underlying schemes be cartesian.

`Rε_*` is taken as an arbitrary right derived functor of `ε_*` with its unit `η`, as in
`Stacks.Cohomology.MayerVietoris.isCSquareIso_ofLe_of_isPushout`, so that the statement is about
the essential image of any of them.

## References

* [Stacks Project, Tag 0EWN](https://stacks.math.columbia.edu/tag/0EWN)
* [Stacks Project, Tag 0F19](https://stacks.math.columbia.edu/tag/0F19)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **The big h site over a scheme, as a ringed site.** The big h category over `S` with its h
topology and a chosen sheaf of commutative rings. -/
abbrev bigHRingedSite (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r}) : RingedSite.{u + 1, u, r} where
  C := BigHOver B S hS
  J := BigHOver.topology B S hS
  O := O

/-- **`h_X^# = h_Z^# ∐_{h_E^#} h_{X'}^#` for an almost blowup square.** The h sheafified
representables of an almost blowup square in the big h category over `S` form a pushout square
of sheaves of sets. This is the first hypothesis of Stacks 0F19.

A square of sheaves of sets is a pushout square exactly when applying `Hom(-, F)` to its
opposite gives a pullback square of sets for every sheaf `F`, and by Yoneda's lemma for sheaves
of sets that square of sets is the square of restriction maps of `F` along the original square.
Stacks 0EVD says it is cartesian. -/
theorem isPushout_sheafifiedYoneda_of_almostBlowUpSquare_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (sq : Square (BigHOver B S hS))
    (I : ((BigHOver.toScheme B S hS).obj sq.X₄).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map sq.f₂₄))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map sq.f₃₄) ≅ Over.mk I.subschemeι))
    (hSquare : (sq.map (BigHOver.toScheme B S hS)).IsPullback) :
    (sq.map (Sheaf.sheafifiedYoneda (BigHOver.topology B S hS))).IsPushout := by
  set J := BigHOver.topology B S hS
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro F
  refine (Square.IsPullback.iff_of_iso (Square.isoMk
    (sq₁ := (sq.map (Sheaf.sheafifiedYoneda J)).op.map (yoneda.obj F))
    (sq₂ := sq.op.map F.obj)
    (Equiv.toIso (Sheaf.sectionEquiv J)) (Equiv.toIso (Sheaf.sectionEquiv J))
    (Equiv.toIso (Sheaf.sectionEquiv J)) (Equiv.toIso (Sheaf.sectionEquiv J))
    ?_ ?_ ?_ ?_)).mpr
    (isPullback_of_almostBlowUpSquare_bigH B S hS F.obj F.property
      sq.f₂₄ sq.f₃₄ sq.f₁₂ sq.f₁₃ I hb hZ hSquare.flip).flip <;>
    (ext α; exact Sheaf.sectionEquiv_map_comp J _ α)

/-- **The exceptional subscheme of an almost blowup square is a subobject of the modification.**
The centre is a closed subscheme of the base, hence a monomorphism, and the exceptional
subscheme is its base change along the modification. -/
theorem mono_exceptional_of_isPullback_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (sq : Square (BigHOver B S hS))
    (I : ((BigHOver.toScheme B S hS).obj sq.X₄).IdealSheafData)
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map sq.f₃₄) ≅ Over.mk I.subschemeι))
    (hSquare : (sq.map (BigHOver.toScheme B S hS)).IsPullback) :
    Mono sq.f₁₂ := by
  have hz : Mono ((BigHOver.toScheme B S hS).map sq.f₃₄) := by
    obtain ⟨e⟩ := hZ
    have hiso : IsIso e.hom.left :=
      (Over.forget ((BigHOver.toScheme B S hS).obj sq.X₄)).map_isIso e.hom
    have heq : e.hom.left ≫ I.subschemeι = (BigHOver.toScheme B S hS).map sq.f₃₄ := Over.w e.hom
    rw [← heq]
    have : IsClosedImmersion I.subschemeι := inferInstance
    infer_instance
  have hz' : Mono (sq.map (BigHOver.toScheme B S hS)).f₃₄ := hz
  exact (BigHOver.toScheme B S hS).mono_of_mono_map hSquare.mono_f₁₂

/-- **Stacks 0EWN.** Let `J' ≤ J` be a topology coarser than the h topology on the big h
category over `S` — the fppf topology in the source — and let `𝒪` be a sheaf of rings for the h
topology, so that the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. Then for every almost blowup square in the big h category
over `S` and every object `K` of `D(𝒪_{J'})` in the essential image of the derived direct image
`Rε_*`, the canonical Mayer–Vietoris comparison `c^K_{X,Z,X',E}` of Stacks 0F16 for the coarser
topology is an isomorphism, i.e. a quasi-isomorphism of complexes of abelian groups.

The h sheafified representables of the square form a pushout square by Stacks 0EVD, and
`h_E^# ⟶ h_{X'}^#` is a monomorphism because `E ⟶ X'` is one, so Stacks 0F19 applies. -/
@[stacks 0EWN]
theorem isCSquareIso_of_essImage_almostBlowUpSquare_bigH
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r})
    {J' : GrothendieckTopology (BigHOver B S hS)} (hJ : J' ≤ BigHOver.topology B S hS)
    [HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{v}]
    [(BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [UnivLE.{u + 1, v}] [UnivLE.{u, v}] [UnivLE.{r, v}]
    (Rε : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (Stacks.Sites.CoarserTopology.modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
        (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (hK : Rε.essImage K)
    (sq : Square (BigHOver B S hS))
    (I : ((BigHOver.toScheme B S hS).obj sq.X₄).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map sq.f₂₄))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map sq.f₃₄) ≅ Over.mk I.subschemeι))
    (hSquare : (sq.map (BigHOver.toScheme B S hS)).IsPullback) :
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
        sq).IsCSquareIso K :=
  Stacks.Cohomology.MayerVietoris.isCSquareIso_ofLe_of_isPushout.{u + 1, v, u, r}
    (S := bigHRingedSite B S hS O) (J' := J') hJ sq
    (isPushout_sheafifiedYoneda_of_almostBlowUpSquare_bigH B S hS sq I hb hZ hSquare)
    (have := mono_exceptional_of_isPullback_bigH B S hS sq I hZ hSquare
     Sheaf.mono_sheafifiedYoneda_map sq.f₁₂)
    Rε η K hK

end AlgebraicGeometry

end
