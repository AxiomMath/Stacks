module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A 1-morphism of represented stacks is DM and quasi-DM (Stacks 04YW, 050N)

Let `S` be a scheme contained in a big fppf site `B` and let `a : 𝒜 ⟶ 𝒞` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` whose source and target are
represented, in the sense of **Stacks 04SV**, by the Yoneda presheaves of two objects `V` and `W`
of the site, in such a way that the induced morphism of representing presheaves of
**Stacks 04SW** is `yoneda.map k` for a morphism `k : V ⟶ W` of the site. Then a condition of
Properties of Stacks, Section **04XB** on the relative diagonal `Δ_a` reduces to the
corresponding property of the *scheme* diagonal of `k`.

The reduction has three steps. First, the representing morphism of `Δ_a` is the diagonal of
`yoneda.map k`: the square of representing morphisms of a 2-fibre product is cartesian
(**Stacks 04SD** for represented stacks,
`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`) and `Δ_a` is a
section of both of its projections, so its representing morphism is the unique such section of
the cartesian square. Second, `CategoryTheory.yoneda` preserves fibre products, so the fibre
product `V ×_W V` formed *in the site* also presents that square, and the diagonal is therefore
`yoneda.map (Δ_k)`; the condition of Stacks 04XB for it is, by
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, the property of
`yoneda.map (Δ_k)` as a morphism of algebraic spaces over `S`. Third, the forgetful functor to
schemes preserves fibre products too, so the morphism of schemes underlying `Δ_k` is the scheme
diagonal of the morphism of schemes underlying `k`, which is an **immersion** (**Stacks 01KJ**,
`AlgebraicGeometry.IsImmersion.instDiagonalScheme`).

Both separation axioms of **Stacks 04YW** whose Stacks 04XB condition is read on étale charts are
then immediate, because an immersion of schemes is unramified (**Stacks 02HE** applied to a
monomorphism locally of finite type) and locally quasi-finite: *a 1-morphism of algebraic stacks
over `S` whose source and target are represented by objects of the site is DM and quasi-DM.*

The point of this is the one input the source's proof of **Stacks 050N**, parts (1) and (2),
needs and which the implications from the absolute axioms do not: the structure morphism over
`Spec(ℤ)` of the view of the stack represented by `S` — whose relative diagonal is `Δ_{S/ℤ}` — is
DM and quasi-DM. The morphism `k` is then the unique morphism of the big fppf site of `Spec(ℤ)`
to its terminal object, so no computation of a representing morphism is needed at all
(`CategoryTheory.Limits.IsTerminal.hom_ext`), and the morphism of schemes underlying it is the
structure morphism of `S` over `Spec(ℤ)` (`CategoryTheory.Over.mkIdTerminal_from_left`). With
**Stacks 050L**, parts (5) and (6), that gives the converse halves of Stacks 050N, parts (1)
and (2).

## Main definitions

* `AlgebraicGeometry.Stack.viewOverIntSchemeStackEquivalenceOver`: the stack represented by `S`,
  viewed over `Spec(ℤ)` by **Stacks 04X6**, is represented by the Yoneda presheaf of the object
  `S ⟶ Spec(ℤ)` of the big fppf site of `Spec(ℤ)`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal`: the
  reduction described above, uniformly in the property.
* `AlgebraicGeometry.Stack.isImmersion_toScheme_map_diagonal`: the morphism of schemes underlying
  the diagonal of a morphism of the site is an immersion.
* `AlgebraicGeometry.Stack.isUnramified_yoneda_map_diagonal` and
  `AlgebraicGeometry.Stack.isLocallyQuasiFinite_yoneda_map_diagonal`: that diagonal is unramified
  and locally quasi-finite as a morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.isDM_of_representingMap_eq_yoneda_map` and
  `AlgebraicGeometry.Stack.isQuasiDM_of_representingMap_eq_yoneda_map`: a 1-morphism of algebraic
  stacks over `S` between represented stacks, induced by a morphism of the site, is DM and
  quasi-DM.
* `AlgebraicGeometry.Stack.isDMOver_viewOverInt_schemeStack` and
  `AlgebraicGeometry.Stack.isQuasiDMOver_viewOverInt_schemeStack`: the stack represented by `S`,
  viewed over `Spec(ℤ)`, is DM and quasi-DM over `Spec(ℤ)`.
* `AlgebraicGeometry.Stack.isDMAbs_of_isDMOver` and
  `AlgebraicGeometry.Stack.isQuasiDMAbs_of_isQuasiDMOver`: the converse halves of
  **Stacks 050N**, parts (1) and (2).

## Implementation notes

**The two converses carry no tag here.** Parts (1) and (2) of Stacks 050N are biconditionals and
a tag lands only with its full covering set; the implications from the absolute axioms are
`AlgebraicGeometry.Stack.isDMOver_of_isDMAbs` and
`AlgebraicGeometry.Stack.isQuasiDMOver_of_isQuasiDMAbs`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase`, and the tags belong on the two
biconditionals assembled from both halves.

**Both instance hypotheses of `AlgebraicGeometry.Stack.HasRelativeProperty` are available at
unramifiedness**, so the bridge of Stacks 04XB can be used through the abbreviation rather than
through a hand-written quantifier: stability under base change is
`AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange` and locality at the target for the
fppf precoverage is the fpqc statement **Stacks 042A**
(`AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc`) transported along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`. Both are available at
unramifiedness, so the longhand quantifier in `AlgebraicGeometry.Stack.HasEtaleChartProperty`
(`StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase`) is not forced; the longhand
condition is the same proposition.

**No computation identifies the representing morphism of a structure morphism.** The target of
the structure morphism over `Spec(ℤ)` is the stack represented by the terminal object of the big
fppf site of `Spec(ℤ)`; `CategoryTheory.yoneda` preserves the terminal object, so the presheaf
representing that target is terminal and there is exactly one morphism of presheaves into it.
That is what the hypothesis `hk` is discharged by below.

**Why the source needs its own representing equivalence.** The structure functor of the view of
`AlgebraicGeometry.Stack.schemeStack` at the identity object is
`Over.forget (Over.mk (𝟙 S)) ⋙ Over.map g`, which is neither a slice forgetful functor nor a
relocalization functor on the nose. `CategoryTheory.Over.mapId_eq` turns `Over.map (𝟙 S)` into
the identity, and **Stacks 03EH**
(`CategoryTheory.PresheafOfCategories.overMapForgetEquivalenceOver`) identifies that composite
with `Over.map g`, which is the category of elements of the Yoneda presheaf of `S ⟶ Spec(ℤ)`
(`CategoryTheory.PresheafOfCategories.overMapElementsEquivalenceOver`).

**An inlined one-liner.** The derivation of unramifiedness of an immersion of schemes from
**Stacks 02HE** (`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified`)
is `private` in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Unramified.lean`, so that one
line
is repeated inside `AlgebraicGeometry.Stack.isUnramified_yoneda_map_diagonal` rather than reused.

**No tag is claimed.** Stacks 04YW is tagged on `AlgebraicGeometry.Stack.IsDM` and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`, Stacks 01KJ on Mathlib's instance for the
scheme diagonal, Stacks 06CQ and 03XM on the space-level statements that an immersion of
algebraic spaces is unramified, resp. locally quasi-finite, and Stacks 050N on the biconditionals
these results complete. What is proved here is the conventions step of Stacks 04XB for
represented stacks, read at a relative diagonal, which the source performs inside a proof.

## References

* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XM](https://stacks.math.columbia.edu/tag/03XM)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 042A](https://stacks.math.columbia.edu/tag/042A)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06CQ](https://stacks.math.columbia.edu/tag/06CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A condition of Stacks 04XB on the relative diagonal of a 1-morphism of represented stacks
is the property of the scheme diagonal.** Let `a : 𝒜 ⟶ 𝒞` be a 1-morphism of categories fibred
in groupoids over the big fppf site of `S`, representable by algebraic spaces, whose source and
target are represented by the Yoneda presheaves of objects `V` and `W` of the site in such a way
that the induced morphism of representing presheaves of **Stacks 04SW** is `yoneda.map k` for a
morphism `k : V ⟶ W`. If the property `P` holds for the Yoneda image of the diagonal of `k`,
formed in the site, then `Δ_a` satisfies the condition of **Stacks 04XB** at `P`.

The representing morphism of `Δ_a` is a section of both projections of the cartesian square of
representing morphisms of the 2-fibre product (**Stacks 04SD** for represented stacks), and
`CategoryTheory.yoneda` carries the fibre product `V ×_W V` of the site to a second cartesian
square on the same cospan, so the two squares are identified and the section becomes
`yoneda.map (Δ_k)`. The bridge
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` then reads the condition
of Stacks 04XB as `P` for that morphism of algebraic spaces. -/
theorem hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (V W : BigFppfOver B S hS)
    (eV : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p)
    (k : V ⟶ W)
    (hk : representingMap B S hS 𝒜 𝒞 (yoneda.obj V) (yoneda.obj W) eV eW a = yoneda.map k)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a).hom)
    (hP : P (ObjectProperty.homMk (yoneda.map (pullback.diagonal k)) :
      (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (pullback k k), isAlgebraicSpace_yoneda B S hS (pullback k k)⟩)) :
    HasRelativeProperty.{u, u, u + 1} B S hS P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a) hΔ := by
  classical
  have _ : (twoFibreProductStructureFunctor B S hS 𝒜 𝒜 𝒞 a a).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a a).pt.property.isFibered
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒞 𝒜 𝒜
    a.hom a.hom ha ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, ⟨eV⟩⟩
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a) hΔ (yoneda.obj V) T
    (isAlgebraicSpace_yoneda B S hS V) hT eV eT).2 ?_
  have hsq0 := isPullback_representingMap_twoFibreProductSquare B S hS 𝒜 𝒜 𝒞
    (yoneda.obj V) (yoneda.obj V) (yoneda.obj W) eV eV eW a a T eT
  rw [hk] at hsq0
  have hsq : IsPullback
      (representingMap B S hS (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom) 𝒜 T (yoneda.obj V)
        eT eV (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a a).fst)
      (representingMap B S hS (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom) 𝒜 T (yoneda.obj V)
        eT eV (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a a).snd)
      (yoneda.map k) (yoneda.map k) := hsq0
  have hsq1 : IsPullback (yoneda.map (pullback.fst k k)) (yoneda.map (pullback.snd k k))
      (yoneda.map k) (yoneda.map k) :=
    (IsPullback.of_hasPullback k k).map yoneda
  have hd : ∀ g : twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom ⟶ 𝒜,
      relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a ≫ g = 𝟙 𝒜 →
      representingMap B S hS 𝒜 (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom)
        (yoneda.obj V) T eV eT (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a) ≫
      representingMap B S hS (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom) 𝒜 T (yoneda.obj V)
        eT eV g = 𝟙 (yoneda.obj V) := fun g hg => by
    rw [← representingMap_comp (ℬ := twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom) B S hS
      (yoneda.obj V) T (yoneda.obj V) eV eT eV
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a) g, hg]
    exact representingMap_id B S hS 𝒜 (yoneda.obj V) eV
  have hdiag : representingMap B S hS 𝒜 (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom)
        (yoneda.obj V) T eV eT (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a) ≫
      (hsq.isoIsPullback _ _ hsq1).hom = yoneda.map (pullback.diagonal k) := by
    refine hsq1.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst,
        hd (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a a).fst rfl,
        ← yoneda.map_comp, pullback.diagonal_fst, yoneda.map_id]
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd,
        hd (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a a).snd rfl,
        ← yoneda.map_comp, pullback.diagonal_snd, yoneda.map_id]
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let hiso : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj (pullback k k), isAlgebraicSpace_yoneda B S hS (pullback k k)⟩ :=
    ObjectProperty.isoMk _ (hsq.isoIsPullback _ _ hsq1)
  have hfinal : (ObjectProperty.homMk (representingMap B S hS 𝒜
          (twoFibreProduct B S hS 𝒞 𝒜 𝒜 a.hom a.hom) (yoneda.obj V) T eV eT
          (relativeDiagonal.{u, u, u + 1} B S hS 𝒜 𝒞 a)) :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨T, hT⟩) ≫ hiso.hom =
      ObjectProperty.homMk (yoneda.map (pullback.diagonal k)) := by
    apply ObjectProperty.hom_ext
    exact hdiag
  rwa [← MorphismProperty.cancel_right_of_respectsIso P _ hiso.hom, hfinal]

/-- **The morphism of schemes underlying the diagonal of a morphism of the big fppf site of `S`
is an immersion.** The forgetful functor to schemes preserves fibre products, so it carries the
diagonal of `k` to the diagonal of the morphism of schemes underlying `k`, up to the comparison
isomorphism of the two fibre products; that diagonal is an immersion by **Stacks 01KJ**. -/
@[ega "IV 16.3.1" "special case"]
theorem isImmersion_toScheme_map_diagonal {V W : BigFppfOver B S hS} (k : V ⟶ W) :
    _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.diagonal k)) := by
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst k k))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd k k))
      ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map k) :=
    (IsPullback.of_hasPullback k k).map _
  have hcomp : (BigFppfOver.toScheme B S hS).map (pullback.diagonal k) ≫ hsq.isoPullback.hom =
      pullback.diagonal ((BigFppfOver.toScheme B S hS).map k) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id, pullback.diagonal_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id, pullback.diagonal_snd]
  rw [show (BigFppfOver.toScheme B S hS).map (pullback.diagonal k) =
      pullback.diagonal ((BigFppfOver.toScheme B S hS).map k) ≫ hsq.isoPullback.inv by
    rw [← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **The diagonal of a morphism of the big fppf site of `S` is unramified** as a morphism of
algebraic spaces over `S`, in the sense of **Stacks 03ZH**, part (1).

Unramifiedness is étale local on the source and target, so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` reads the condition for the
Yoneda image of a morphism of the site as the condition for the underlying morphism of schemes;
and an immersion of schemes is a monomorphism locally of finite type, hence unramified by
**Stacks 02HE**. -/
theorem isUnramified_yoneda_map_diagonal {V W : BigFppfOver B S hS} (k : V ⟶ W) :
    Space.IsUnramified B S hS (yoneda.map (pullback.diagonal k)) := by
  have _ := isImmersion_toScheme_map_diagonal B S hS k
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    unramified_isEtaleLocalOnSourceAndTarget (pullback.diagonal k)).2
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified _).2
      ⟨inferInstance, inferInstance⟩)

/-- **The diagonal of a morphism of the big fppf site of `S` is locally quasi-finite** as a
morphism of algebraic spaces over `S`, in the sense of **Stacks 03XJ**, part (1).

The same argument as for unramifiedness, at the property "locally of finite type and locally
quasi-finite" of morphisms of schemes, which an immersion has. -/
theorem isLocallyQuasiFinite_yoneda_map_diagonal {V W : BigFppfOver B S hS} (k : V ⟶ W) :
    Space.IsLocallyQuasiFinite B S hS (yoneda.map (pullback.diagonal k)) := by
  have _ := isImmersion_toScheme_map_diagonal B S hS k
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    (pullback.diagonal k)).2 ⟨inferInstance, inferInstance⟩

/-- **A 1-morphism of algebraic stacks over `S` between represented stacks, induced by a
morphism of the site, is DM.** If `𝒳` and `𝒴` are represented by the Yoneda presheaves of objects
`V` and `W` of the site and the morphism of representing presheaves induced by `f` is
`yoneda.map k`, then the relative diagonal `Δ_f` is unramified in the sense of **Stacks 04XB**,
because it is the Yoneda image of the diagonal of `k` and that is an immersion.

Representability of `f` by algebraic spaces is automatic: its source is represented by an
algebraic space and its target is an algebraic stack
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`). -/
theorem isDM_of_representingMap_eq_yoneda_map {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (V W : BigFppfOver B S hS)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p)
    (k : V ⟶ W)
    (hk : representingMap B S hS 𝒳.val 𝒴.val (yoneda.obj V) (yoneda.obj W) eV eW f.hom =
      yoneda.map k) :
    IsDM B S hS f := by
  have _ : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have _ : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  exact hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B S hS
    (Space.unramifiedMorphismProperty B S hS) f.hom
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, ⟨eV⟩⟩ f.hom)
    V W eV eW k hk
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isUnramified_yoneda_map_diagonal B S hS k)

/-- **A 1-morphism of algebraic stacks over `S` between represented stacks, induced by a
morphism of the site, is quasi-DM.** The same argument as for the DM condition, at local
quasi-finiteness of the relative diagonal in place of unramifiedness. -/
theorem isQuasiDM_of_representingMap_eq_yoneda_map {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (V W : BigFppfOver B S hS)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p)
    (k : V ⟶ W)
    (hk : representingMap B S hS 𝒳.val 𝒴.val (yoneda.obj V) (yoneda.obj W) eV eW f.hom =
      yoneda.map k) :
    AlgebraicStacks.IsQuasiDM B S hS f := by
  have _ : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
    Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
  have _ : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B S hS
    (Space.locallyQuasiFiniteProperty B S hS) f.hom
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V, ⟨eV⟩⟩ f.hom)
    V W eV eW k hk
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isLocallyQuasiFinite_yoneda_map_diagonal B S hS k)

/-- **The stack represented by `S`, viewed over `Spec(ℤ)`, is represented by the Yoneda presheaf
of the object `S ⟶ Spec(ℤ)` of the big fppf site of `Spec(ℤ)`.**

The structure functor of that view is `Over.forget (Over.mk (𝟙 S)) ⋙ Over.map g` for the unique
`g : S ⟶ Spec(ℤ)` of the site. **Stacks 03EH** identifies the first factor with `Over.map (𝟙 S)`,
which is the identity by `CategoryTheory.Over.mapId_eq`, and `Over.map g` is the category of
elements of the Yoneda presheaf of `S ⟶ Spec(ℤ)`. -/
noncomputable def viewOverIntSchemeStackEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (viewOverInt.{u, w, w'} B S hS
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))).val.val.p
      (presheafOfCategories (yoneda.obj (Over.mk (toIntObject B S hS)) ⋙ typeToCat)).p :=
  ((PresheafOfCategories.overMapForgetEquivalenceOver (𝟙 (B.obj hS))).compRight
      (Over.map (toIntObject B S hS))).symm.trans
    ((PresheafOfCategories.overMapElementsEquivalenceOver (toIntObject B S hS)).ofEq
      (by rw [Over.mapId_eq, Functor.id_comp]))

/-- **The stack represented by `S` is DM over `Spec(ℤ)`**, that is, `Δ_{S/ℤ}` is unramified in
the sense of **Stacks 04XB**.

Both the source and the target of the structure morphism over `Spec(ℤ)` are represented by
objects of the big fppf site of `Spec(ℤ)` — the source by `S ⟶ Spec(ℤ)` and the target by the
terminal object — and the morphism of representing presheaves is the unique morphism to a
terminal presheaf, hence the Yoneda image of the unique morphism of the site to its terminal
object. So `AlgebraicGeometry.Stack.isDM_of_representingMap_eq_yoneda_map` applies.

This is the input the converse halves of **Stacks 050N**, parts (1) and (2), need: they run the
composition of **Stacks 050K** along `𝒳 ⟶ S ⟶ Spec(ℤ)`, and composition — unlike the
cancellation of Stacks 050M, which is what the implications from the absolute axioms use —
requires the axiom for the second factor. -/
theorem isDMOver_viewOverInt_schemeStack :
    IsDMOver B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))) :=
  isDM_of_representingMap_eq_yoneda_map B _ (contains_specULiftZ B)
    (structureMorphism B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
    (Over.mk (toIntObject B S hS)) (Over.mk (𝟙 (B.obj (contains_specULiftZ B))))
    (viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (Over.mkIdTerminal.from (Over.mk (toIntObject B S hS)))
    ((Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _)

/-- **The stack represented by `S` is quasi-DM over `Spec(ℤ)`**, that is, `Δ_{S/ℤ}` is locally
quasi-finite in the sense of **Stacks 04XB**. The same argument as for the DM condition. -/
theorem isQuasiDMOver_viewOverInt_schemeStack :
    IsQuasiDMOver B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))) :=
  isQuasiDM_of_representingMap_eq_yoneda_map B _ (contains_specULiftZ B)
    (structureMorphism B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
    (Over.mk (toIntObject B S hS)) (Over.mk (𝟙 (B.obj (contains_specULiftZ B))))
    (viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (Over.mkIdTerminal.from (Over.mk (toIntObject B S hS)))
    ((Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _)

/-- **Stacks 050N, part (1), the implication to the absolute axiom.** If an algebraic stack `𝒳`
over `S` is DM over `S`, then it is DM.

The structure morphism of `𝒳` over `Spec(ℤ)` is the view of the structure morphism of `𝒳` over
`S`, followed by the structure morphism over `Spec(ℤ)` of the view of the stack represented by
`S`. Part (5) of **Stacks 050L** is exactly that composition read on objects: it takes the
absolute axiom for the target of a 1-morphism together with the axiom for the 1-morphism, and the
axiom for the 1-morphism here is the hypothesis, while the absolute axiom for the stack
represented by `S` is `AlgebraicGeometry.Stack.isDMOver_viewOverInt_schemeStack`.

**This is one direction of a biconditional, and it carries no tag.** The other direction is
`AlgebraicGeometry.Stack.isDMOver_of_isDMAbs`. -/
theorem isDMAbs_of_isDMOver (𝒵 : AlgebraicStacks.{u, w} B S hS) (h : IsDMOver B S hS 𝒵) :
    IsDMAbs.{u, w, w'} B S hS 𝒵 :=
  isDMAbs_of_isDM B S hS (structureMorphism B S hS 𝒵)
    (isDMOver_viewOverInt_schemeStack.{u, w, w'} B S hS) h

/-- **Stacks 050N, part (2), the implication to the absolute axiom.** If an algebraic stack `𝒳`
over `S` is quasi-DM over `S`, then it is quasi-DM.

The same argument as part (1), with part (6) of **Stacks 050L** in place of part (5) and
`AlgebraicGeometry.Stack.isQuasiDMOver_viewOverInt_schemeStack` in place of the DM statement for
the stack represented by `S`.

**This is one direction of a biconditional, and it carries no tag.** The other direction is
`AlgebraicGeometry.Stack.isQuasiDMOver_of_isQuasiDMAbs`. -/
theorem isQuasiDMAbs_of_isQuasiDMOver (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsQuasiDMOver B S hS 𝒵) : IsQuasiDMAbs.{u, w, w'} B S hS 𝒵 :=
  isQuasiDMAbs_of_isQuasiDM B S hS (structureMorphism B S hS 𝒵)
    (isQuasiDMOver_viewOverInt_schemeStack.{u, w, w'} B S hS) h

end AlgebraicGeometry.Stack

end
