module

public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionDisjointUnion

/-!
# The separated étale atlas, and the reduction of Stacks 0APL to Stacks 0APK

The proof of Stacks 0APL carried out in
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionDisjointUnion` and
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle` needs, besides Stacks 0AP9
and Stacks 0APK, one *surjective* étale chart of the algebraic space whose underlying scheme is
separated. Stacks 0AP9 is proved as
`AlgebraicGeometry.isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite`, and this file
supplies the chart: Stacks 03FX gives a surjective étale chart whose underlying scheme is a
disjoint union of affine schemes, and a disjoint union of affine schemes is a separated scheme
by `AlgebraicGeometry.Scheme.isSeparated_sigma_of_isAffine`.

What is then left of Stacks 0APL is Stacks 0APK together with one size obligation, and the
final theorem of this file says exactly that, machine-checkably. The size obligation is that
the scheme which Stacks 0APK descends be an object of the size-bounded site; it is not part of
the tag, and it is named in the implementation notes below rather than left implicit.

## Main results

* `AlgebraicGeometry.IsAlgebraicSpace.exists_isSeparated_etale_surjective_atlas`: **an algebraic
  space over `S` admits a surjective étale chart whose underlying scheme is separated.**
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent`: **Stacks 0APL
  with Stacks 0APK, plus a size bound, as its only hypothesis.** An algebraic space over `S` is
  a sheaf for the fpqc topology of the big fppf category over `S`, given effectivity — inside
  the size-bounded site — of each of the descent data which the middle paragraph of the source
  constructs along an fpqc covering of one morphism.

## Implementation notes

The chart produced by Stacks 03FX,
`AlgebraicGeometry.Space.exists_etale_surjective_coproduct_affine_cover`, comes with an
*isomorphism* `∐ Y ≅ U` rather than an equality, because the object of the site is built from
the coproduct; separatedness is transported along it by
`AlgebraicGeometry.Scheme.isSeparated_of_iso`. The index type of the family of affines is
arbitrary — no finiteness and no quasi-compactness of the space is assumed — which is why
`AlgebraicGeometry.Scheme.isSeparated_sigma` is proved for an arbitrary index type rather than
only for a finite one: the source's appeal to "a finite disjoint union of affines is affine" is
replaced by separatedness of an arbitrary disjoint union, which is all that Stacks 03FZ needs.

The hypothesis `hAPK` is reproduced verbatim from
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isIndQuasiAffineHom_of_isEffectiveFpqcDescent`;
see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle` for why it is stated at the
descent datum the paragraph constructs rather than at the general notion of a descent datum.

Three things about `hAPK` are worth stating here rather than leaving to the reader to check
against the tag, since a carried hypothesis that does not match the tag it names is not
discharged by proving that tag. First, the morphism `f` along which descent is asserted to be
effective carries the fpqc-covering condition — surjective, flat and quasi-compact — which is
exactly the hypothesis Stacks 0APK makes on its covering family. Second, `W` is demanded as an
object of the size-bounded site while Stacks 0APK produces a bare scheme, so a size bound for
the descended scheme is folded in on top of the tag; the descended `w` is surjective and étale,
so that bound is in reach of the existing size calculus, but it is an obligation and is not
part of Stacks 0APK.

Third, and this one makes the hypothesis *weaker* rather than stronger: both ends of `f` are
demanded affine. The first paragraph of the source delivers that affineness for free, and
carrying it matters for the route to the tag. The proof of Stacks 0APK begins by citing
Stacks 02W3 — a property of morphisms stable under base change and under disjoint union
satisfies fpqc descent as soon as it does for a single surjective flat morphism of affines —
and uses it for nothing but that reduction. The first paragraph having already reduced to a
single morphism of affine objects, what `hAPK` asks for is the case Stacks 02W3 reduces to, so
Stacks 02W3 lies off the route from this statement to Stacks 0APL.

**No declaration here is tagged.** Stacks 03FX is tagged in
`StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings`, the chart statement
below is not a statement the source makes, and Stacks 0APL belongs on the unconditional sheaf
statement, which is still out of reach: Stacks 0APK is absent from the repository.

## References

* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace IsAlgebraicSpace

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An algebraic space over `S` admits a surjective étale chart whose underlying scheme is
separated.**

Stacks 03FX supplies a surjective étale chart whose underlying scheme is isomorphic to a
disjoint union of affine schemes; such a disjoint union is separated by
`AlgebraicGeometry.Scheme.isSeparated_sigma_of_isAffine`, and separatedness transports along the
isomorphism. The clause of Stacks 03FX saying that each summand maps into an affine open of the
base is not used. -/
theorem exists_isSeparated_etale_surjective_atlas (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ F),
      Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u := by
  obtain ⟨U, u, I, Y, e, hus, hue, haff, -⟩ :=
    Space.exists_etale_surjective_coproduct_affine_cover B S hS F hF
  exact ⟨U, u, Scheme.isSeparated_of_iso e (Scheme.isSeparated_sigma_of_isAffine Y haff),
    hus, hue⟩

/-- **Stacks 0APL with Stacks 0APK, plus a size bound, as its only hypothesis.** An algebraic
space over `S` is a sheaf for the fpqc topology of the big fppf category over `S` as soon as
each of the descent data which the middle paragraph of the source constructs, along an fpqc
covering consisting of a single morphism of the site, is effective inside the site.

This is
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isIndQuasiAffineHom_of_isEffectiveFpqcDescent`
with its chart hypotheses discharged by
`AlgebraicGeometry.IsAlgebraicSpace.exists_isSeparated_etale_surjective_atlas`. It proves no new
mathematics; it records, machine-checkably, what the residue of Stacks 0APL is, and it is the
statement a prover who discharges that residue should apply.

The residue is Stacks 0APK and nothing else geometric — the chart and Stacks 0AP9, which used
to stand beside it, are both discharged — together with one size obligation, namely that the
scheme Stacks 0APK descends be an object of the size-bounded site. Moreover `hAPK` asks for
Stacks 0APK only along a single morphism of *affine* objects, which is the case the proof of
that tag reduces to by Stacks 02W3; see the implementation notes of this module. Nothing here
needs `B.cutoff.IsRegular`, and no regularity or cofinality hypothesis on the cutoff is
introduced. -/
theorem isSheaf_fpqc_of_isEffectiveFpqcDescent (hF : IsAlgebraicSpace B S hS F)
    (hAPK : ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ (U V : BigFppfOver B S hS) (u : yoneda.obj U ⟶ F) (q : V ⟶ U) (p : V ⟶ T')
      (c : yoneda.obj T' ⟶ F), IsPullback (yoneda.map q) (yoneda.map p) u c →
      Surjective ((BigFppfOver.toScheme B S hS).map p) →
      Etale ((BigFppfOver.toScheme B S hS).map p) →
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) →
      IsIndQuasiAffineHom ((BigFppfOver.toScheme B S hS).map p) →
      yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (α : pullback f w ≅ V),
        α.hom ≫ p = pullback.fst f w ∧
        pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
          pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  obtain ⟨U, u, hUsep, hus, hue⟩ := hF.exists_isSeparated_etale_surjective_atlas
  exact hF.isSheaf_fpqc_of_isIndQuasiAffineHom_of_isEffectiveFpqcDescent hUsep hus hue hAPK

end IsAlgebraicSpace

end AlgebraicGeometry

end
