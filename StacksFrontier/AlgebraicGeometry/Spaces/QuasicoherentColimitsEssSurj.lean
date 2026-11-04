module

public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian

/-!
# The colimit clause of Stacks 03M1 on two module-free propositions of Descent

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03M1
asserts six closure properties of the quasi-coherent `𝒪_F`-modules inside all `𝒪_F`-modules; this
file is about clause (2), closure under arbitrary colimits.

That clause is already proved in this tree, in the shape the tag states and at a free module
universe, but conditional on hypotheses of two kinds, and only one kind is a proposition of
Descent, Chapter 35:

* `AlgebraicGeometry.Space.isQuasicoherent_colimit` carries `hsum`, clause (1) of the *same* tag,
  and `hcoker`, the cokernel half of clause (3) of the *same* tag;
* `AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX` trades `hsum` for `h03DX`, one
  implication of Descent, Proposition 03DX(2), and still carries `hcoker`.

So in both shapes part of the residue of clause (2) is another unproved clause of Stacks 03M1
itself.  **This file removes that self-reference: clause (2) is stated below on exactly the two
propositions in which no module and no morphism of `F` occurs, both clauses of results of
Descent, Chapter 35**, which are the same two that
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj` reduces clauses (3) and (4) to:

* `hEss`, essential surjectivity of the functor `M ↦ Mᵃ` of Tag 03DU on the quasi-coherent
  modules of the slice of the small étale site of `F` at an affine chart.  By
  `Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj` it is the whole
  residue of `h03DX`.
* `h03DW`, surjectivity on the sections over an affine chart of every epimorphism of
  `𝒪_F`-modules whose kernel is cartesian on affine charts.  It is Descent, Proposition 03DW for
  a cartesian, hence quasi-coherent, kernel.

Nothing mathematical happens here: every result below is a composition of theorems already in the library, and
the file introduces no definition, structure, class or instance.

## Main results

* `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW`:
  **quasi-coherence of `𝒪_F`-modules is closed under cokernels, on `hEss` and `h03DW`**, in the
  `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` shape.  This is the shape five files of
  this development carry as an undischarged hypothesis; see the implementation notes.
* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essSurj_of_h03DW`:
  closure of quasi-coherence under colimits of a given shape, on `hEss` and `h03DW`.
* `AlgebraicGeometry.Space.isQuasicoherent_colimit_of_essSurj_of_h03DW`: **clause (2) of
  Stacks 03M1 for one diagram, on `hEss` and `h03DW`.**

## Implementation notes

**No `@[stacks]` attribute is claimed.**  Every statement below is conditional on two unproved
propositions of Descent, Chapter 35, so the covering set of Stacks 03M1 is still empty and the tag
stands at none of its six clauses.  The convention — a conditional statement carries no tag — is
that of `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimits`,
`StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian` and
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj`.

**The two hypotheses are written out at every use rather than named**, which is this tree's
practice for `h03DT`, `h03DX` and `h03DW`: naming them would create a second spelling of a tag of
Descent.  They agree with the binders of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW`, which is where they
are consumed.

**Neither hypothesis is vacuous.**  `hEss` has the attainability witness
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_self` and is the essential
surjectivity half of Descent, Proposition 03DX(2); `h03DW` has the witness
`AlgebraicGeometry.Space.surjective_val_app_of_isSplitEpi` and is Descent, Proposition 03DW
applied to a kernel which is cartesian on affine charts, hence quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  The side condition
on the kernel in `h03DW` may **not** be dropped: quantified over all epimorphisms the statement is
false, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite` record.

**What the cokernel statement discharges.**  The
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` shape of quasi-coherence occurs as an
undischarged hypothesis of
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure`
(`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck`), of
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_isCartesian`
(`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite`), of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_image`
(`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects`, whose statements of
Stacks 0829 take it from `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`),
and of the colimit statements composed here.  No other statement of the library concludes it; the
kernel analogue `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite`, and this is its cokernel
counterpart, which needs `h03DW` in addition because a cokernel of sheaves of modules is the
sheafification of the cokernel of presheaves and its sections over a chart are therefore not the
cokernel of the sections.

**The module universe is the universe `u` of the schemes**, and it is forced three times
over, all three reasons being recorded by the files composed: the statements name `CategoryTheory.Limits.cokernel`, so the category of
modules has to have cokernels, which at this site holds at `m := u`; the sections of
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` lie in `Type u` by construction, so
`hEss` is not statable at another module universe; and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, which
`AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX` routes through, is stated there.  The
shape of the diagram keeps its own two independent universes, as in the source.

**The coproduct hypothesis is not the tag's, and it bounds the shape universes.**
`HasCoproducts.{max w w'}` on the category of `𝒪_F`-modules is an added hypothesis which clause
(2) of Stacks 03M1 does not carry; it comes from the route through
`AlgebraicGeometry.Space.isQuasicoherent_colimit`, which presents a colimit as a cokernel of a map
between two coproducts of the terms of the diagram.  It is satisfied when `max w w'` is at most
`u`: a coproduct of sheaves of modules is the sheafification of the objectwise direct sum, whose
sections over an object lie in `Type (max w w' u)`, and the sections of an `𝒪_F`-module here lie
in `Type u`.  That universe arithmetic gives no reason to expect the hypothesis beyond
`max w w' ≤ u`, so the statements below should be read as covering the shapes whose objects and
morphisms are at most as large as the schemes, with the two shape universes still independent of
each other.  The source's own proof of
clause (2) does not need it — it restricts to an étale chart and cites the case of schemes,
Descent, Lemma 0GNB(2) — but that route needs 0GNB, which has no site in either tree under any of
the four attribute forms, and it needs restriction to a slice to preserve colimits, which
`Stacks.SheafOfModules.overFunctor_preservesColimits` supplies only at module universes of the
shape `max (u + 1) t`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Quasi-coherence of `𝒪_F`-modules is closed under cokernels, on essential surjectivity of
`(-)ᵃ` and on Stacks 03DW.**

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW` in the shape
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels`, which is the shape in which
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure`,
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` and
`AlgebraicGeometry.Space.isQuasicoherent_colimit` ask for the cokernel half of clause (3) of
Stacks 03M1: the small étale site of an algebraic space over `Scheme.{u}` has objects in
`Type (u + 1)`, morphisms in `Type u` and a `CommRingCat.{u}`-valued structure sheaf.

Those three consumers state the hypothesis at a *free* module universe `m`, so this
discharges them at `m := u` and not in general; only
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects` asks for it at `u`
already.

It is the cokernel counterpart of
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves`, and like it transports the
canonical cokernel to the vertex of an arbitrary colimiting cokernel cofork, which is what the
class asks about, along `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`. -/
theorem isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hφ⟩
    have h₁ : SheafOfModules.IsQuasicoherentOnSite _ := hφ.1
    have h₂ : SheafOfModules.IsQuasicoherentOnSite _ := hφ.2
    exact ObjectProperty.prop_of_iso _
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hk)
      (isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW φ hEss h03DW)

/-- **Clause (2) of Stacks 03M1 as a closure property of the quasi-coherent `𝒪_F`-modules, on
essential surjectivity of `(-)ᵃ` and on Stacks 03DW.**  Quasi-coherence of `𝒪_F`-modules is closed
under colimits of a given shape, whose objects and morphisms live in independent universes as in
the source.

This is `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves` with its
direct-sum hypothesis supplied by
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX` and its
cokernel hypothesis by
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW`, the
`h03DX` of the former coming from `hEss` through
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`.

It discharges the hypothesis `hfc` of
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure`, for an arbitrary
shape rather than only a filtered one. -/
theorem isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essSurj_of_h03DW (K : Type w)
    [Category.{w'} K] [HasCoproducts.{max w w'} (Modules.{u, u} B S hS F hF)]
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_quasicoherentSheaves B S hS F hF K
    (fun I => isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX B S hS F hF
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj B S hS F hF hEss) I)
    (isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW B S hS F hF hEss h03DW)

/-- **Clause (2) of Stacks 03M1, on essential surjectivity of `(-)ᵃ` and on Stacks 03DW.**  A
colimit of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

Both remaining hypotheses are propositions of Descent, Chapter 35 in which no module and no
morphism of `F` occurs, and neither is a clause of Stacks 03M1: that is what this statement adds
to `AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX`, whose `hcoker` is the cokernel half
of clause (3) of the same tag.  It is not a gain in strength and is not claimed as one — `hEss`
implies that theorem's `h03DX` and the pair implies its `hcoker`, so the hypotheses here imply its
hypotheses and this statement is formally **weaker** than it.

The shape of the diagram has its objects and its morphisms in independent universes, as in the
source.  `HasCoproducts.{max w w'}` is an added hypothesis which the source does not carry; see
the implementation notes. -/
theorem isQuasicoherent_colimit_of_essSurj_of_h03DW {K : Type w} [Category.{w'} K]
    [HasCoproducts.{max w w'} (Modules.{u, u} B S hS F hF)]
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))
    (D : K ⥤ Modules.{u, u} B S hS F hF) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (Limits.colimit D).IsQuasicoherentOnSite :=
  haveI := isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essSurj_of_h03DW B S hS F hF K
    hEss h03DW
  ObjectProperty.prop_colimit _ D hD

end AlgebraicGeometry.Space

end
