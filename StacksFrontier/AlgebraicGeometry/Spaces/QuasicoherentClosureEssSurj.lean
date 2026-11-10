module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectSums

/-!
# The kernel and direct sum clauses of Stacks 03M1, and Stacks 077V(1), on one module-free input

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03M1
asserts six closure properties of the quasi-coherent `𝒪_F`-modules.  Four of them are proved in
this tree conditionally, and until now they did not rest on the same hypotheses:

* clause (2) and clause (4), and the cokernel half of clause (3), rest on two propositions of
  Descent, Chapter 35 in which no module and no morphism of `F` occurs — `hEss`, the
  essential-surjectivity clause of Descent, Proposition 03DX(2), and `h03DW`, the uniform form of
  Descent, Proposition 03DW.  See
  `StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj` and
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj`;
* clause (1) and the kernel half of clause (3) rest instead on `h03DX`, Descent,
  Proposition 03DX(2) itself, carried in its equivalence spelling at a free module universe.  See
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`.

**This file puts the second pair on `hEss` as well**, so that after it the four clauses this tree
has reached are conditional on `hEss` alone where no cohomological input is needed — clause (1),
the kernel half of clause (3), and the left term of clause (4) — and on `hEss` together with
`h03DW` otherwise.  No further content of the Stacks project is owed by any of them; what some of
them do carry beyond those two is an instance hypothesis about the ambient category, namely the
existence of the coproduct or of the colimit whose quasi-coherence is asserted, and each of those
is recorded where it occurs.

It then discharges two of the three hypotheses that Stacks 077V, part (1) carries beyond the
closure properties of Stacks 03M1.  `CategoryTheory.LocallySmall.{u}` of the `𝒪_F`-modules at
module universe `u` is proved **outright**, from essential smallness of the small étale site of
`F` (Stacks 03G0); the implementation notes of
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` record it as "the
one hypothesis here that is a universe condition rather than mathematics", and it is now not a
hypothesis at all.  The closure under colimits of every shape is supplied from `hEss` and
`h03DW`.  What remains of Stacks 077V(1) beyond those two propositions is a separator on the
quasi-coherent modules, Stacks 03M3 and 077U.

## Main results

* `AlgebraicGeometry.Space.locallySmall_modules_smallEtale`: **the `𝒪_F`-modules at module
  universe `u` are locally small at `u`, unconditionally.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_essSurj`: the kernel half of clause (3)
  of Stacks 03M1, on `hEss` alone.
* `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_of_essSurj`: the same in the
  shape `CategoryTheory.ObjectProperty.IsClosedUnderKernels`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_essSurj` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_essSurj`: clause (1) of Stacks 03M1, for
  an arbitrary colimiting cofan and for the chosen coproduct, on `hEss` alone.
* `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_essSurj_of_h03DW`:
  **Stacks 077V, part (1) in its Grothendieck abelian form, on `hEss`, `h03DW` and a separator.**

## Implementation notes

**No definition, structure, class or instance is introduced.**  Every result but the first is a
composition of existing theorems; the first is Mathlib's transport of Grothendieck abelianness along
the equivalence with the small model, through
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`.

**These statements are formally weaker than the ones they compose, and that is not hidden.**  Axis
by axis, against `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX`: `hEss` implies their `h03DX`, by
`SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj`, so the antecedent here
is harder to satisfy and the implication therefore weaker; and the module universe drops from free
to `u`, which restricts the conclusion and so weakens it again. No gain in strength is claimed in
either place. What is gained is that a single cited proposition of Descent serves four clauses of
Stacks 03M1 rather than two, with no adapter at any of them. This is the convention of
`AlgebraicGeometry.Space.isQuasicoherent_colimit_of_essSurj_of_h03DW`, which records the same
relation to its own predecessor.

**Local smallness is a theorem and not an instance, and the reason is a unification hazard.**  An
`CategoryTheory.EssentiallySmall.{u}` instance stated at the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite B S hS F hF).C` hijacks the implicit category
argument of `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` away
from the reduced spelling `AlgebraicGeometry.Space.SmallEtale`, and breaks
`AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`.  So the
essential smallness is introduced inside the proof below by `change` onto the reduced spelling
followed by instance search — which is what
`AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone` already does —
and local smallness is left for consumers to supply with `have`.

**Why the two closure classes remain instance binders of the last result although `hEss` and
`h03DW` imply them.**  `CategoryTheory.IsGrothendieckAbelian.{u}` of the quasi-coherent modules
mentions `CategoryTheory.Abelian` of them in its own type, and that instance is synthesized from
the closure classes; they therefore have to be in scope before the statement elaborates, and a
`have` inside the proof is too late.  With them supplied by `have` the statement does
not elaborate, failing to synthesize
`CategoryTheory.Abelian (AlgebraicGeometry.Space.QuasicoherentSheaves B S hS F hF)`.  Both are
available from the two hypotheses, by
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_of_essSurj` below and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW`, so a
consumer holding `hEss` and `h03DW` owes nothing further for them.

**Neither hypothesis is introduced here, and what is known about the inhabitation of each is
stated exactly.**  Both are copied verbatim from the statements that already carry them, so no
second spelling of a tag of Descent is created.  For `h03DW` the conclusion is attained
unconditionally by the split epimorphisms,
`AlgebraicGeometry.Space.surjective_val_app_of_isSplitEpi`, and the affine charts it quantifies
over do carry covering families, by
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_covering`.  For `hEss` the position is
weaker and should not be overstated: its body is satisfiable at an affine chart *granted the sheaf
condition of Tag 03DT there*, by
`AlgebraicGeometry.Space.SmallEtale.exists_quasicoherent_sliceAssociatedModule_iso`, whose own
hypothesis `hsh` is that sheaf condition and is not proved in this tree; and its conclusion is
attainable with no hypothesis at all for a module already of the form `Mᵃ`, by
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_self`.  So neither witness is
an unconditional inhabitation of `hEss` itself.

The side condition on the kernel inside `h03DW` may not be dropped: quantified over all
epimorphisms the statement is false, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite` record.

**No `@[stacks]` attribute is claimed.**  Every statement below but the first is conditional on at
least one proposition of Descent, Chapter 35 which has no declaration in either library tree under
any of the attribute forms, so the covering set of Stacks 03M1 is still empty and the tag stands
at none of its six clauses; and the first is a set-theoretic fact about a module category, not a
clause of any of the tags cited here.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 077U](https://stacks.math.columbia.edu/tag/077U)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Local smallness of the modules at the universe of the schemes -/

/-- **The `𝒪_F`-modules at module universe `u` are locally small at `u`.**  This is
unconditional.

The small étale site of an algebraic space over `Scheme.{u}` has its objects in `Type (u + 1)`,
so a hom type of modules on it is not a priori a type of `Type u`; but the site is essentially
small at `u` by Stacks 03G0, and `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`
transports Grothendieck abelianness, hence local smallness, from the small model.

This discharges the hypothesis `[CategoryTheory.LocallySmall.{m} _]` of
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` at `m := u`, the
one module universe at which that file records it as not automatic.  It is deliberately not
registered as an instance; see the implementation notes. -/
theorem locallySmall_modules_smallEtale : LocallySmall.{u} (Modules.{u, u} B S hS F hF) :=
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  (SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).locallySmall

/-! ### The kernel half of clause (3) -/

/-- **The kernel half of clause (3) of Stacks 03M1, on essential surjectivity of `(-)ᵃ`.**  The
kernel of a morphism of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

`hEss` is the essential-surjectivity clause of Descent, Proposition 03DX(2) at an affine chart
`Y` of `F`: every quasi-coherent module on the slice of the small étale site of `F` at `Y` is
isomorphic to the module `Mᵃ` of Tag 03DU of a quasi-coherent module `M` on the scheme underlying
`Y`.  It mentions no module of `F`, so one instance of it serves every morphism, and it is the
same hypothesis as in `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact_of_essSurj`.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` with its `h03DX`
supplied by `SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj`. No
cohomological input occurs: sections of sheaves of modules are left exact, which is exactly what a
kernel needs. -/
theorem isQuasicoherentOnSite_kernel_of_essSurj {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (φ : M ⟶ N)
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀)) :
    (kernel φ).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_kernel_of_isCartesian B S hS F hF φ
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj B S hS F hF hEss)

/-- **Quasi-coherence of `𝒪_F`-modules is closed under kernels, on essential surjectivity of
`(-)ᵃ`.**

This is `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` with its `h03DX`
supplied from `hEss`, in the shape
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` in which
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` ask for it.  It is
the kernel counterpart of
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves_of_essSurj_of_h03DW`, and
unlike it needs no instance of Stacks 03DW. -/
theorem isClosedUnderKernels_quasicoherentSheaves_of_essSurj
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀)) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels :=
  isClosedUnderKernels_quasicoherentSheaves B S hS F hF
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj B S hS F hF hEss)

/-! ### Clause (1), arbitrary direct sums -/

/-- **Clause (1) of Stacks 03M1 for an arbitrary colimiting cofan, on essential surjectivity of
`(-)ᵃ`.**  The vertex of a colimiting cofan on a family of quasi-coherent `𝒪_F`-modules is
quasi-coherent.

The index type is arbitrary and its universe is independent of the universe of the schemes.  No
refinement of coverings is involved, which a route through global presentations could not avoid:
a Grothendieck topology is closed under binary intersections only, so infinitely many coverings
have no common refinement.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX` with its
`h03DX` supplied from `hEss`; the geometric content is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_coproduct`, which is unconditional. -/
theorem isQuasicoherentOnSite_of_isColimit_cofan_of_essSurj
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    {ι : Type w} {G : ι → Modules.{u, u} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX B S hS F hF
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj B S hS F hF hEss) c hc hG

/-- **Clause (1) of Stacks 03M1, on essential surjectivity of `(-)ᵃ`.**  A direct sum of
quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_essSurj` at the
chosen coproduct, through `CategoryTheory.Limits.coproductIsCoproduct`; it is the shape in
which the clause is stated.  The coproduct is left as a hypothesis rather than
synthesized, exactly as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX`, so no universe bound on the index
type is written into the statement. -/
theorem isQuasicoherentOnSite_sigma_of_essSurj
    (hEss : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∀ P : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), P.IsQuasicoherentOnSite →
        ∃ (M₀ : (chartScheme Y).Modules) (_ : M₀.IsQuasicoherent)
          (hM₀ : Presheaf.IsSheaf ((topology B S hS F).over Y)
            (Stacks.Sites.associatedPresheaf (chartScheme Y) M₀
              (sliceToOver B S hS F Y))),
          Nonempty (P ≅ sliceAssociatedModule B S hS F hF Y M₀ hM₀))
    {ι : Type w} (G : ι → Modules.{u, u} B S hS F hF) [HasCoproduct G]
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    (∐ G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_sigma_of_h03DX B S hS F hF
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_of_essSurj B S hS F hF hEss) G hG

/-! ### Stacks 077V, part (1) -/

/-- **Stacks 077V, part (1), in its Grothendieck abelian form, on essential surjectivity of
`(-)ᵃ`, on Stacks 03DW and on a separator.**  The quasi-coherent `𝒪_F`-modules on an algebraic
space form a Grothendieck abelian category at the universe of the schemes.

This is `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` with two
of its hypotheses discharged: local smallness of the ambient module category, by
`AlgebraicGeometry.Space.locallySmall_modules_smallEtale`, and closure under filtered colimits,
by `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essSurj_of_h03DW`
— which gives it for an arbitrary shape and not only a filtered one.

The two closure hypotheses that remain are instance binders because the conclusion's type needs
them; both follow from `hEss` and `h03DW`, and the implementation notes say how.  The separator is
Stacks 03M3 and 077U and is not addressed here. -/
theorem quasicoherentSheaves_isGrothendieckAbelian_of_essSurj_of_h03DW
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]
    [HasSeparator (QuasicoherentSheaves.{u, u} B S hS F hF)]
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
    IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  have := locallySmall_modules_smallEtale B S hS F hF
  quasicoherentSheaves_isGrothendieckAbelian_of_closure B S hS F hF
    fun K _ _ => isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essSurj_of_h03DW
      B S hS F hF K hEss h03DW

end AlgebraicGeometry.Space

end
