module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperFactorsClosedFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLocal

/-!
# The closed fibre of a scheme over a local ring, and restriction of étale cohomology to it

Let `A` be a local ring and `f : X ⟶ Spec A` a morphism of schemes. Its *closed fibre* is the
fibre over the closed point of `Spec A`, that is the pullback of `f` along
`Spec κ(A) ⟶ Spec A`. This file gives that scheme and its inclusion into `X` names, records that
the inclusion is a closed immersion and that the closed fibre inherits properness, and builds the
canonical restriction map on étale cohomology with constant coefficients,

`H^q(X, M) ⟶ H^q(X₀, M)`,

out of the inverse-image machinery of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction`.

The map is canonical, with no choices: it is the action of the exact inverse-image functor on
`Ext` out of the constant sheaf `ℤ`, transported along the two canonical identifications of the
inverse image of a constant sheaf with the constant sheaf, each of which is unique because both
functors involved are left adjoint to evaluation at the final object of the site.

## Main definitions

* `Stacks.EtaleCohomology.closedFibre` and `Stacks.EtaleCohomology.closedFibreInclusion` — the
  closed fibre of a morphism to the spectrum of a local ring, and its inclusion into the source.
* `Stacks.EtaleCohomology.closedFibreProjection` — the structure morphism of the closed fibre
  over the residue field.
* `Stacks.EtaleCohomology.etaleConstantSheaf` — the constant abelian sheaf on the small étale
  site.
* `Stacks.EtaleCohomology.etaleConstantCohomologyRestriction` — the canonical restriction map on
  étale cohomology with constant coefficients.

## Main results

* `Stacks.EtaleCohomology.isPullback_closedFibre` — the defining cartesian square, so that
  nothing below needs to unfold the definition of the closed fibre.
* `Stacks.EtaleCohomology.isClosedImmersion_closedFibreInclusion` and
  `Stacks.EtaleCohomology.isProper_closedFibreProjection` — the inclusion is a closed immersion,
  and the closed fibre of a proper scheme is proper over the residue field.
* `Stacks.EtaleCohomology.etaleConstantCohomologyRestriction_apply` — the defining formula for
  restriction.
* `Stacks.EtaleCohomology.bijective_etaleConstantCohomologyRestriction_iff` — restriction is
  bijective exactly when the inverse-image map on `Ext` out of the constant sheaf `ℤ` is.
* `Stacks.EtaleCohomology.bijective_etaleConstantCohomologyRestriction_one` — the same
  equivalence read at `q = 1` under the hypotheses of Stacks 0A5G.

## Stacks 0A5G

For `A` henselian local, `X` proper over `A` and `M` a finite abelian group, Stacks 0A5G is the
assertion that `etaleConstantCohomologyRestriction A f M 1` is bijective. Its proof reads a class
in `H^1` as the isomorphism class of an `M`-torsor on the small étale site (Stacks 03AJ), reads
such a torsor as a scheme finite étale over `X` carrying a free transitive `M`-action (Stacks
03RV), and matches the finite étale covers of `X` with those of the closed fibre (Stacks 0A48).

Each of those three steps is available here only with an input of its own: essential surjectivity
on finite étale covers in
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_closedFibre_of_essSurj`, effective descent
of representability in
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`, and
bijectivity of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` on global sections for
the injectivity half. What the three produce together is one `Ext`-level statement: that the
exact inverse-image functor along the closed-fibre inclusion is bijective on `Ext^1` out of the
constant sheaf `ℤ`.

What is proved here is the reduction of the tag to that statement, in every degree and for every
morphism to the spectrum of a local ring:
`Stacks.EtaleCohomology.bijective_etaleConstantCohomologyRestriction_iff` identifies bijectivity
of restriction with bijectivity of the `Ext`-level map, the two differing by composition with
the two constant-sheaf comparison isomorphisms. The geometry that would make the `Ext`-level
statement true in degree one — properness, henselianity, finiteness of `M` — is not used in that
reduction and is not supplied here.

## Implementation notes

The four `HasSheafify` and `HasExt` side-conditions are hypotheses rather than instances, and
cannot be discharged. Mathlib's `HasSheafify` and `Abelian` instances for the small étale site
cover coefficients in `AddCommGrpCat.{u}` and `AddCommGrpCat.{u + 1}` only, whereas the étale
inverse-image functor needs coefficients in `AddCommGrpCat.{max (u + 1) v}` for the pointwise
left Kan extension to exist — the reason recorded in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction`. Restricting the
coefficient universe would discharge the two `HasSheafify` hypotheses but not the two `HasExt`
ones: `HasExt` for a category of sheaves needs the localized hom types of its derived category to
be small, and Mathlib provides no such instance for this site at any coefficient universe.

The closed fibre is a plain definition rather than an abbreviation, so `isPullback_closedFibre`
is provided as its interface; the morphisms out of it are the two pullback projections, which is
the de facto convention of the surrounding files.

## References

* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

section ClosedFibre

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The closed point of `Spec A` for a local ring `A`, as the morphism
`Spec κ(A) ⟶ Spec A` induced by the quotient by the maximal ideal. -/
def residueFieldPoint :
    Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))

/-- The closed fibre of a morphism `f : X ⟶ Spec A` to the spectrum of a local ring: the fibre
`X ×_{Spec A} Spec κ(A)` of `f` over the closed point. -/
def closedFibre {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) : Scheme.{u} :=
  pullback f (residueFieldPoint A)

/-- The inclusion of the closed fibre into `X`, that is the first projection of the defining
pullback square. -/
def closedFibreInclusion {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) : closedFibre A f ⟶ X :=
  pullback.fst f (residueFieldPoint A)

/-- The structure morphism of the closed fibre over the residue field, that is the second
projection of the defining pullback square. -/
def closedFibreProjection {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    closedFibre A f ⟶ Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) :=
  pullback.snd f (residueFieldPoint A)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The defining cartesian square of the closed fibre.** This is the interface to the
definition: nothing below unfolds `Stacks.EtaleCohomology.closedFibre` itself. -/
theorem isPullback_closedFibre :
    IsPullback (closedFibreInclusion A f) (closedFibreProjection A f) f (residueFieldPoint A) :=
  IsPullback.of_hasPullback f (residueFieldPoint A)

/-- The closed point of the spectrum of a local ring is a closed immersion. -/
theorem isClosedImmersion_residueFieldPoint : IsClosedImmersion (residueFieldPoint A) :=
  isClosedImmersion_specMap_quotientMk A (IsLocalRing.maximalIdeal A)

/-- The inclusion of the closed fibre is a closed immersion, being a base change of the closed
point of `Spec A`. -/
theorem isClosedImmersion_closedFibreInclusion :
    IsClosedImmersion (closedFibreInclusion A f) :=
  have := isClosedImmersion_residueFieldPoint A
  inferInstanceAs (IsClosedImmersion (pullback.fst f (residueFieldPoint A)))

/-- The closed fibre of a proper scheme over `Spec A` is proper over the residue field, being a
base change of `f`. -/
theorem isProper_closedFibreProjection [IsProper f] : IsProper (closedFibreProjection A f) :=
  inferInstanceAs (IsProper (pullback.snd f (residueFieldPoint A)))

end ClosedFibre

section Restriction

/-- The constant abelian sheaf with values in `M` on the small étale site of `Y`. The coefficients
are lifted to the universe in which the étale inverse-image functor is available. -/
abbrev etaleConstantSheaf (Y : Scheme.{u}) (M : Type v) [AddCommGroup M]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift.{u + 1, v} M))

variable (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (M : Type v) [AddCommGroup M] (q : ℕ)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction of étale cohomology with constant coefficients to the closed fibre.** The
canonical map `H^q(X, M) ⟶ H^q(X₀, M)`: the action of the exact étale inverse-image functor on
`Ext` out of the constant sheaf `ℤ`, composed with the canonical identification of the inverse
image of the constant sheaf on `M` with the constant sheaf on `M`.

Stacks 0A5G is the assertion that this map is bijective in degree `q = 1` when `A` is henselian,
`f` is proper and `M` is finite. -/
def etaleConstantCohomologyRestriction :
    Sheaf.H.{w} (etaleConstantSheaf.{u, v} X M) q →+
      Sheaf.H.{w} (etaleConstantSheaf.{u, v} (closedFibre A f) M) q :=
  ((Abelian.Ext.mk₀
        ((etaleAbelianInverseImageConstantIso.{u, v} (closedFibreInclusion A f)).app
          (AddCommGrpCat.of (ULift.{u + 1, v} M))).hom).postcomp _ (add_zero q)).comp
    (etaleCohomologyRestrictionMap.{u, v, w} (closedFibreInclusion A f)
      (etaleConstantSheaf.{u, v} X M) q)

/-- Restriction to the closed fibre is the map on `Ext` induced by the exact inverse-image
functor, transported along the two canonical constant-sheaf comparisons. -/
theorem etaleConstantCohomologyRestriction_apply
    (x : Sheaf.H.{w} (etaleConstantSheaf.{u, v} X M) q) :
    etaleConstantCohomologyRestriction.{u, v, w} A f M q x =
      ((Abelian.Ext.mk₀
          ((etaleAbelianInverseImageConstantIso.{u, v}
            (closedFibreInclusion A f)).app
              (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (x.mapExactFunctor
          (etaleAbelianInverseImage.{u, v} (closedFibreInclusion A f))) (Nat.zero_add q)).comp
        (Abelian.Ext.mk₀
          ((etaleAbelianInverseImageConstantIso.{u, v} (closedFibreInclusion A f)).app
            (AddCommGrpCat.of (ULift.{u + 1, v} M))).hom) (add_zero q) := rfl

end Restriction

section ExtComparison

universe u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]

/-- Postcomposing `Ext`-classes with an isomorphism is a bijection, the inverse being
postcomposition with the inverse isomorphism. -/
private lemma bijective_extPostcomp_of_iso (P : C) {Y Z : C} (e : Y ≅ Z) (n : ℕ) :
    Function.Bijective ((Abelian.Ext.mk₀ e.hom).postcomp P (add_zero n)) := by
  have := Functor.map_isIso (Abelian.extFunctorObj.{w} P n) e.hom
  exact ConcreteCategory.bijective_of_isIso ((Abelian.extFunctorObj.{w} P n).map e.hom)

/-- Precomposing `Ext`-classes with an isomorphism is a bijection, the inverse being
precomposition with the inverse isomorphism. -/
private lemma bijective_extPrecomp_of_iso {Y Z : C} (e : Y ≅ Z) (P : C) (n : ℕ) :
    Function.Bijective ((Abelian.Ext.mk₀ e.hom).precomp P (zero_add n)) := by
  have := Functor.map_isIso (Abelian.extFunctor.{w} n) e.hom.op
  exact ConcreteCategory.bijective_of_isIso (((Abelian.extFunctor.{w} n).map e.hom.op).app P)

end ExtComparison

section Stacks0A5G

variable (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (M : Type v) [AddCommGroup M] (q : ℕ)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 0A5G reduced to an `Ext` computation.** Restriction to the closed fibre is bijective
in degree `q` exactly when the étale inverse-image functor along the closed-fibre inclusion is
bijective on `Ext^q` out of the constant sheaf `ℤ`: the two maps differ by composition with the
two canonical constant-sheaf comparison isomorphisms, and composing with an isomorphism is
bijective on `Ext`.

Nothing here is special to a proper morphism over a henselian local ring, and nothing here
computes either side. What Stacks 0A5G asserts is that in degree one the right-hand side holds
when `A` is henselian local, `f` is proper and `M` is finite; that is the geometric content, and
it rests on Stacks 03AJ, 03RV, 0A48 and 0A0C. -/
@[stacks 0A5G "the reduction of the tag to an Ext computation, in every degree q: the canonical \
map H^q(X, M) -> H^q(X_0, M) is bijective if and only if etale inverse image along the \
closed-fibre inclusion is bijective on Ext^q out of the constant sheaf Z. The geometric content \
of the tag -- that this holds in degree one for a proper morphism over a henselian local ring -- \
is not proved here. The inputs the source's degree-one argument needs ARE available: Stacks 03AJ \
as Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1, Stacks 03RV as \
AlgebraicGeometry.finiteLocallyConstantFiniteEtaleEquivalence, and Stacks 0A48 as \
AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing. What is \
missing is the bridge between them: no result transports an Ext^1 or Sheaf.H map along a CHANGE \
OF SITE into torsor language -- torsorIsoClassesEquivH1_naturality is naturality in the \
coefficient sheaf on a fixed site -- and the restriction map here lives on Mathlib's \
Scheme.smallEtaleTopology while 03RV lives on SmallEtale.topology of a BigEtaleSite, with no \
comparison. Nor does anything say that a torsor under a finite constant sheaf is finite locally \
constant"]
theorem bijective_etaleConstantCohomologyRestriction_iff :
    Function.Bijective (etaleConstantCohomologyRestriction.{u, v, w} A f M q) ↔
      Function.Bijective
        ((etaleAbelianInverseImage.{u, v} (closedFibreInclusion A f)).mapExtAddHom.{w, w}
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ)))
          (etaleConstantSheaf.{u, v} X M) q) := by
  dsimp only [etaleConstantCohomologyRestriction, etaleCohomologyRestrictionMap,
    AddMonoidHom.coe_comp]
  exact ((bijective_extPostcomp_of_iso _
      ((etaleAbelianInverseImageConstantIso.{u, v} (closedFibreInclusion A f)).app
        (AddCommGrpCat.of (ULift.{u + 1, v} M))) q).of_comp_iff' _).trans
    ((bijective_extPrecomp_of_iso
      ((etaleAbelianInverseImageConstantIso.{u, v} (closedFibreInclusion A f)).app
        (AddCommGrpCat.of (ULift ℤ))).symm _ q).of_comp_iff' _)

end Stacks0A5G

section Stacks0A5GMain

variable (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (M : Type v) [AddCommGroup M]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf (closedFibre A f).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Restriction `H^1_ét(X, M) ⟶ H^1_ét(X₀, M)` to the closed fibre is bijective whenever the
exact étale inverse-image functor along the closed-fibre inclusion is bijective on `Ext^1` out of
the constant sheaf `ℤ`, for `A` henselian local, `X` proper over `A` and `M` a finite abelian
group.

The hypothesis `hExt` is the `Ext`-level form of the conclusion: by
`Stacks.EtaleCohomology.bijective_etaleConstantCohomologyRestriction_iff` the two are equivalent,
differing only by the two constant-sheaf comparison isomorphisms. So this is a restatement of
that equivalence at `q = 1` under the hypotheses of Stacks 0A5G, not a proof of it; henselianity
of `A`, properness of `f` and finiteness of `M` are unused here and enter only in the geometry
that would discharge `hExt`. -/
theorem bijective_etaleConstantCohomologyRestriction_one [IsProper f] [Finite M]
    (hExt : Function.Bijective
      ((etaleAbelianInverseImage.{u, v} (closedFibreInclusion A f)).mapExtAddHom.{w, w}
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ)))
        (etaleConstantSheaf.{u, v} X M) 1)) :
    Function.Bijective (etaleConstantCohomologyRestriction.{u, v, w} A f M 1) :=
  (bijective_etaleConstantCohomologyRestriction_iff.{u, v, w} A f M 1).2 hExt

end Stacks0A5GMain

end Stacks.EtaleCohomology

end
