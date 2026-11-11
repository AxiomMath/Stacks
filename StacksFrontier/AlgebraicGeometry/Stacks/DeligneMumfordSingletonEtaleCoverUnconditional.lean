module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSingletonEtaleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleFlatUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SingletonDMFieldEtaleCover

/-!
# A reduced one-point DM stack is covered étale-ly by the spectrum of a field (Stacks 06N0), proved

Let `𝒵` be a DM, locally Noetherian, reduced algebraic stack over `S` whose point space `|𝒵|` is
a singleton. **Stacks 06N0** says there are a field `k` and a surjective étale 1-morphism
`Spec k ⟶ 𝒵`.

`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSingletonEtaleCover` defines the hypothesis
`AlgebraicGeometry.Stack.IsReducedLocallyNoetherianSingletonDM` and the conclusion
`AlgebraicGeometry.Stack.HasSurjectiveEtaleFieldSpectrumCover`. This module proves the tag,
as `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional`.

## The route

The source's first step is **Stacks 06MP**, part (1) ⟹ (2), that is
`…hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian` of the
`AlgebraicGeometry.Stack` namespace: reducedness, local Noetherianity and the one-point space
produce a surjective, flat, locally finitely presented 1-morphism `ξ : Spec k ⟶ 𝒵`. Everything
after it is `…exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover` in
`StacksFrontier.AlgebraicGeometry.Stacks.SingletonDMFieldEtaleCover`: the groupoid
`(U, R, s, t, c)` of that flat presentation, with `U = Spec k` and `R = U ×_𝒵 U`, is divided by
the open and closed subgroupoid `P ⊆ R` through the identity, the quotient `U̅ = Spec k₀` is the
spectrum of the field of invariants, and `U̅ ⟶ 𝒵` is étale.

Surjectivity of `U̅ ⟶ 𝒵` is read off the point space, as in the source: `|𝒵|` is a singleton and
the algebraic stack of the spectrum of a field has a point, by
`AlgebraicGeometry.Stack.nonempty_points_fieldSpectrumStack`.

That last step follows the source's steps 6 and 8 rather than its **Stacks 04XD** reading. The
divided groupoid is the restriction of the descended groupoid `(U̅, R̅, s̄, t̄, c̄)` along the
finite locally free surjection `U ⟶ U̅`, so `[U/R] ⟶ [U̅/R̅]` is an equivalence by
**Stacks 046T**; `[U/R] ⟶ 𝒵` is an equivalence by **Stacks 04WY**; and `s̄` is étale, so the
projection `S_{U̅} ⟶ [U̅/R̅]` of **Stacks 044R** is étale by **Stacks 04M9**, which transports to
`U̅ ⟶ 𝒵` across those two equivalences by **Stacks 0457**.

DM-ness enters exactly twice, both times at the division: through **Stacks 050H** part (4) it
makes the stabilizer unramified, hence the arrow space zero-dimensional and `R` a scheme, and
through part (5) it makes the pre-relation locally quasi-finite. Étaleness of `s̄` is
**Stacks 047W** at unramifiedness,
`Stacks.Groupoids.GroupoidScheme.etale_source_of_flat_of_isOpenImmersion_identity`, rather than
the computation `Ω_{R̅/U̅} = 0` of **Stacks 04R9** the source uses. It is turned into DM-ness over
`S`, which is what the division consumes, by **Stacks 050N** part (1),
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_iff_isDMOver`.

## Main results

* `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_of_isUnramified`: a second route
  to the conclusion, from an unramified locally finitely presented field-valued point — étaleness
  by **Stacks 0CJ1**, part (2) ⟹ (1), flatness by the flatness half of **Stacks 06MM** through
  `AlgebraicGeometry.Stack.isFlat_of_isReducedWithUniquePoint`.
* `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional`: **Stacks 06N0**.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04R9](https://stacks.math.columbia.edu/tag/04R9)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
* [Stacks Project, Tag 0CJ1](https://stacks.math.columbia.edu/tag/0CJ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The reduction of Stacks 06N0 to one clause.** Under the hypotheses of **Stacks 06N0**, a
field spectrum carrying a 1-morphism to `𝒵` which is locally of finite presentation and
unramified gives the conclusion of Stacks 06N0.

The three clauses of the conclusion come out separately. Surjectivity needs only that `|𝒵|` is a
subsingleton while the algebraic stack of the spectrum of a field has a point. Flatness is the
flatness half of **Stacks 06MM**, through
`AlgebraicGeometry.Stack.isFlat_of_isReducedWithUniquePoint`: reducedness and the one-point
space already force *every* field-valued point of `𝒵` to be flat. Étaleness is then
**Stacks 0CJ1**, part (2) ⟹ (1).

DM-ness is not used here. It is the hypothesis under which the source *produces* such a point,
by dividing the groupoid of a flat presentation by the open subgroupoid through the identity;
that production is `…exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover`, and it is
the route `AlgebraicGeometry.Stack.hasSurjectiveEtaleFieldSpectrumCover_unconditional` takes. -/
theorem hasSurjectiveEtaleFieldSpectrumCover_of_isUnramified
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (hred : IsReducedStack B S hS 𝒵)
    (hne : Nonempty (AlgebraicStacks.points B S hS 𝒵))
    (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒵))
    (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hunr : IsUnramified B S hS f) :
    HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵 := by
  have hflat := isFlat_of_isReducedWithUniquePoint.{u, w} B S hS 𝒵 ⟨hred, hne, hsub⟩ F f
  obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F
  exact ⟨F, f, fun _ => ⟨p, Subsingleton.elim _ _⟩,
    AlgebraicStacks.isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified.{u, w}
      B S hS f hlfp hflat hunr⟩

/-- **Stacks 06N0.** A DM, locally Noetherian, reduced algebraic stack whose point space is a
singleton admits a field `k` and a surjective étale 1-morphism `Spec k ⟶ 𝒵`.

The field-valued point is produced in two steps. **Stacks 06MP**, part (1) ⟹ (2), gives a
surjective, flat, locally finitely presented `ξ : Spec k ⟶ 𝒵`; and
`AlgebraicGeometry.Stack.exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover` divides
the groupoid of that flat presentation by the open subgroupoid through the identity and returns
an étale 1-morphism out of the spectrum of the field of invariants. Surjectivity of that
1-morphism is read off the point space: `|𝒵|` is a subsingleton and the algebraic stack of the
spectrum of a field has a point. The DM hypothesis is used at the division, in the absolute form
of **Stacks 050D** part (5), turned into DM-ness over `S` by **Stacks 050N** part (1). -/
@[stacks 06N0 "a DM, locally Noetherian, reduced algebraic stack with a singleton point space \
admits a surjective etale 1-morphism from the spectrum of a field. The field-valued point comes \
in two steps: Stacks 06MP (1) => (2) supplies a surjective, flat, locally finitely presented \
xi : Spec k -> Z, and the groupoid (U, R, s, t, c) of that flat presentation, with U = Spec k \
and R = U x_Z U, is divided by the open and closed subgroupoid P through the identity, whose \
quotient U_bar = Spec k_0 is the spectrum of the field of invariants. The division is \
exists_division_identityArrowOpens_etale_pointGroupoid, on the four conclusions of Stacks 04S4 \
in exists_division; it is run at the de-realization of the self-intersection groupoid, whose \
object and arrow spaces are representable by isRepresentable_objects_pointGroupoid_fieldSpectrum \
and isRepresentable_arrows_pointGroupoid_fieldSpectrum, the latter being condition (2) of \
Stacks 06LZ read on the base site at the dimension bound \
dimension_relation_le_zero_fieldSpectrum, i.e. Stacks 06FF against quasi-DM-ness \
through Stacks 050H part (5). Etaleness of U_bar -> Z follows the source's steps 6 and 8 rather \
than its Stacks 04XD reading: the divided groupoid is the restriction of the descended groupoid \
(U_bar, R_bar, s_bar, t_bar, c_bar) along the finite locally free surjection U -> U_bar, so \
[U/R] -> [U_bar/R_bar] is an equivalence by Stacks 046T \
(nonempty_isEquivalenceOver_quotientStackMap_realizationHom, whose clause (1) is full \
faithfulness of the evaluations of the descent morphism and whose clause (2) is that its map on \
objects is an fppf covering), [U/R] -> Z is an equivalence by Stacks 04WY \
(nonempty_isEquivalenceOver_canonicalMap), and s_bar is etale by \
Division.etale_descended_source, which is Stacks 047W at unramifiedness through \
etale_source_of_flat_of_isOpenImmersion_identity rather than the computation of \
Omega_{R_bar/U_bar} that Stacks 04R9 gives the source. Stacks 04M9 then makes the projection \
S_{U_bar} -> [U_bar/R_bar] of Stacks 044R etale \
(isRelativelyEtale_quotientStackProjection_realization), and two instances of Stacks 0457 move \
that verdict across the equivalence with Z and down the universe lift of the source, giving \
quotientProjectionSchemeStackMap, which is etale in the sense of Stacks 0CIL by \
isEtale_of_isRelativelyEtale. DM-ness enters at the division, in the absolute form \
of Stacks 050D part (5), turned into DM-ness over S by Stacks 050N part (1)"]
theorem hasSurjectiveEtaleFieldSpectrumCover_unconditional
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : IsReducedLocallyNoetherianSingletonDM.{u, w} B S hS hZ 𝒵) :
    HasSurjectiveEtaleFieldSpectrumCover.{u, w} B S hS 𝒵 := by
  obtain ⟨hDM, hnoeth, hred, hne, hsub⟩ := h𝒵
  obtain ⟨F, ξ, hlfp, hsurj, hflat⟩ :=
    hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian.{u, w}
      B S hS 𝒵 ⟨⟨hred, hne, hsub⟩, hnoeth⟩
  obtain ⟨F₀, f, he⟩ :=
    exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover.{u, w} B S hS hZ 𝒵
      ((AlgebraicStacks.isAbsolutelyDM_iff_isDMOver.{u, w} B S hS hZ 𝒵).mp hDM)
      F ξ hsurj hflat hlfp
  obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F₀
  exact ⟨F₀, f, fun _ => ⟨p, Subsingleton.elim _ _⟩, he⟩

end AlgebraicGeometry.Stack

end
