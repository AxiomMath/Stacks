module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# The functor of quotients is a sheaf on the big fppf site of the base scheme (Stacks 082P)

In Situation 082M a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site is given together with a quasi-coherent `𝒪_X`-module `F`.  Stacks 082N reads the
assignment

`T ↦ Q_{F/X/Y}(T) = {quotients F_T ⟶ Q with Q quasi-coherent and flat over T}`

as a functor on the test schemes *over `Y`*, and that is
`AlgebraicGeometry.Space.QuotientSituation.quotientsFunctor`.  The source, however, regards
`Q_{F/X/Y}` as a presheaf on the big fppf site of `S`: its value at a scheme `U` over `S` is
the set of **pairs** `(h, Q)` consisting of a morphism `h : U ⟶ Y` and a quotient of `F_U` for
the test scheme `(U, h)`.  Stacks 082P is the statement that this presheaf, and its
finite-presentation subpresheaf, satisfy the sheaf condition.

This file builds that presheaf — the *total* presheaf of the functor of quotients over the
base scheme — and reduces its sheaf condition to two inputs: the sheaf condition for the
target algebraic space `Y`, which is part of Stacks 025Y and is therefore available, and the
descent of quotients along coverings of a single test scheme, which is carried as a
hypothesis.  Stacks 082P itself is proved, for the functor on test schemes over `Y` and the fpqc
topology, in the namespace `AlgebraicGeometry.Space.QuotientSituation` as
`isSheafFor_quotientsFunctor_of_isFpqcCovering` and
`isSheafFor_finitePresentationQuotientsFunctor_of_isFpqcCovering`
in `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorFpqcSheaf.lean`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.testAt`: the test scheme over `Y` attached to a
  morphism `h : U ⟶ Y` out of a scheme of the big fppf site, together with its restriction
  `testAtRestrict` along a morphism of schemes and the induced morphisms `testAtMap`,
  `testAtMap'` of test schemes.
* `AlgebraicGeometry.Space.QuotientSituation.TotalQuotient`: a morphism `h : U ⟶ Y` bundled
  with a quotient of `F_U` over the test scheme `(U, h)` — the elements of the total presheaf.
* `AlgebraicGeometry.Space.QuotientSituation.totalQuotientFunctor`: the total presheaf of a
  pullback-stable condition on quotients, a presheaf on the big fppf site of `S`.
* `AlgebraicGeometry.Space.QuotientSituation.totalQuotientsFunctor`: **Stacks 082P**,
  `Q_{F/X/Y}` as a presheaf on the big fppf site of `S`.
* `AlgebraicGeometry.Space.QuotientSituation.totalFinitePresentationQuotientsFunctor`:
  **Stacks 082P**, `Q^{fp}_{F/X/Y}` as a presheaf on the big fppf site of `S`.
* `AlgebraicGeometry.Space.QuotientSituation.QuotientsSeparatedForCoverings` and
  `AlgebraicGeometry.Space.QuotientSituation.QuotientsGlueAlongCoverings`: the two halves of
  the descent of quotients along a covering of a test scheme, carried as hypotheses.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.isSheaf_totalQuotientFunctor`: **the reduction.**
  The total presheaf is an fppf sheaf as soon as the quotients over a fixed test scheme are
  separated for and glue along the coverings of that test scheme.  The sheaf condition for the
  morphisms `h : U ⟶ Y` is *proved* here, from the sheaf condition for `Y`.
* `AlgebraicGeometry.Space.QuotientSituation.TotalQuotient.toQuotientsFunctorObj`: the
  quotient half of an element of the total presheaf, read as an element of the value of the
  functor of quotients of Stacks 082N at the test scheme of its structure morphism, so the
  presheaf here really is the total presheaf of that functor.

## Implementation notes

**The total presheaf is built without transport.**  The naive construction of
`U ↦ Σ (h : U ⟶ Y), Q_{F/X/Y}(U, h)` runs into the dependence of the second component on the
first: the module `F_{(U,h)}` lives on the fibre product `X ×_Y U` formed along `h`, so the
restriction of a pair along `g : V ⟶ U` lands over the test scheme of
`schemeSpaceFunctor.map g ≫ h`, and the two functor laws then compare subobjects of modules on
*equal but not syntactically identical* algebraic spaces.  Here that comparison never arises,
because the test scheme of a restricted pair is spelled as `testAt (map g ≫ h)` rather than as
a base change of `testAt h`: with that spelling the identity law and the composition law of
`schemeSpaceFunctor` hold definitionally — `map (𝟙 U) ≫ h` reduces to `h` and
`map (g ≫ k) ≫ h` reduces to `map g ≫ (map k ≫ h)` — so the test schemes on the two sides of
each functor law are the *same* object and the laws are
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback_id` and
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback_comp` with nothing in between.
A quotient is carried in a structure rather than in a `Sigma` type so that its three fields can
be addressed by name; the one place where a quotient has to be read at a *propositionally*
equal structure morphism is `AlgebraicGeometry.Space.QuotientSituation.TotalQuotient.kerAt`,
used in the sheaf proof where the glued morphism `U ⟶ Y` is only known to agree with the given
ones after the fact, and every lemma about it is proved by substituting that equality away.

**What the sheaf condition needs, and which half is proved here.**  A compatible family of
pairs `(h_i, Q_i)` for a covering of `U` has two components.  The morphisms `h_i : U_i ⟶ Y`
form a compatible family of sections of `Y`, which has a unique amalgamation `h : U ⟶ Y`
because an algebraic space is an fppf sheaf — the first clause of Stacks 025Y, available as
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf`.  That half is proved here, through the Yoneda
identification of `Hom(U, Y)` with the sections of `Y` over `U`.  The quotients `Q_i` then all
live over restrictions of the *single* test scheme `(U, h)`, and amalgamating them is descent
of quasi-coherent quotients along the covering `{X_{U_i} ⟶ X_U}` of Topologies on Spaces,
Lemma 73.9.3 — the content of Remark 08IU, which the source cites and which is
`AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering`.  The reduction here states
the separatedness and the glueing of quotients as the two predicates
`AlgebraicGeometry.Space.QuotientSituation.QuotientsSeparatedForCoverings` and
`AlgebraicGeometry.Space.QuotientSituation.QuotientsGlueAlongCoverings`; both are proved for the
quotients of Situation 082M in `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorFpqcSheaf.lean`
(`AlgebraicGeometry.Space.QuotientSituation.quotientsSeparatedForCoverings_quotients` and
`AlgebraicGeometry.Space.QuotientSituation.quotientsGlueAlongCoverings_quotients`).

**The topology.**  The source states the sheaf condition for the fpqc topology, which is
stronger than the fppf condition because the fppf coverings are fpqc coverings.  The statements
below are for `AlgebraicGeometry.BigFppfOver.topology`, the fppf topology of the big fppf site
over `S`, which is the site on which `Q_{F/X/Y}` is a presheaf at all and the topology in which
`Y` is a sheaf; the hypotheses are stated for the same coverings, so a consumer that has fpqc
descent of quotients gets the fppf statement immediately.

**The flatness and quasi-coherence inputs are those of Stacks 082N.**  The total presheaf
exists for the same reason the functor of Stacks 082N does, and carries the same three
hypotheses: the pseudofunctoriality of the inverse images of Stacks 03LU, the preservation of
flatness over the base by base change (Stacks 05VW), and the preservation of quasi-coherence
(Stacks 03GA), with the preservation of finite presentation added for the subpresheaf.

## References

* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 082N](https://stacks.math.columbia.edu/tag/082N)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0CZL](https://stacks.math.columbia.edu/tag/0CZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Test schemes attached to a morphism of the big fppf site -/

/-- The test scheme over `Y` attached to a morphism `h` from a scheme of the big fppf site of
`S`, read as a morphism of algebraic spaces. -/
abbrev testAt {U : BigFppfOver B S hS} (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    SchemesOver D.Y :=
  CostructuredArrow.mk h

/-- The test scheme of `h` restricted along a morphism `g : V ⟶ U` of the big fppf site: the
test scheme of the composite `V ⟶ U ⟶ Y`. -/
abbrev testAtRestrict {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) : SchemesOver D.Y :=
  D.testAt ((schemeSpaceFunctor B S hS).map g ≫ h)

/-- The morphism of test schemes over `Y` induced by a morphism `g : V ⟶ U` of the big fppf
site. -/
abbrev testAtMap {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) : D.testAtRestrict g h ⟶ D.testAt h :=
  CostructuredArrow.homMk g rfl

/-- The morphism of test schemes induced by `k : W ⟶ V` between two restrictions of the test
scheme of `h`.  The composition law of `schemeSpaceFunctor` holds definitionally, so this is
literally `AlgebraicGeometry.Space.QuotientSituation.testAtMap` of `k` over the restricted
morphism. -/
abbrev testAtMap' {W V U : BigFppfOver B S hS} (k : W ⟶ V) (g : V ⟶ U)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.testAtRestrict (k ≫ g) h ⟶ D.testAtRestrict g h :=
  D.testAtMap k ((schemeSpaceFunctor B S hS).map g ≫ h)

/-- The morphism of test schemes induced by a composite is the composite of the induced
morphisms. -/
theorem testAtMap_comp {W V U : BigFppfOver B S hS} (k : W ⟶ V) (g : V ⟶ U)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    D.testAtMap (k ≫ g) h = D.testAtMap' k g h ≫ D.testAtMap g h :=
  rfl

/-! ### The elements of the total presheaf -/

/-- An element of the total presheaf of the functor of quotients at a scheme `U` of the big
fppf site of `S`: a morphism `h : U ⟶ Y`, making `U` a test scheme, together with a quotient of
`F_U` over that test scheme — the source's pair `(h, Q)`.

The condition on the quotient is a parameter, so that the construction serves both
`Q_{F/X/Y}` and its finite-presentation subpresheaf. -/
structure TotalQuotient (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (U : BigFppfOver B S hS) where
  /-- The structure morphism `U ⟶ Y` making `U` a test scheme. -/
  hom : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y
  /-- The kernel of the quotient of `F_U` over that test scheme. -/
  ker : Subobject (D.baseChangeModule (D.testAt hom))
  /-- The quotient satisfies the condition. -/
  mem : ker ∈ Q (D.testAt hom)

namespace TotalQuotient

variable {D} {Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))}

/-- The kernel of an element of the total presheaf, read over the test scheme of a structure
morphism equal to its own.  This is the only transport in the file; every lemma about it is
proved by substituting the equality away. -/
def kerAt {U : BigFppfOver B S hS} (q : D.TotalQuotient Q U)
    {h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e : q.hom = h) :
    Subobject (D.baseChangeModule (D.testAt h)) :=
  cast (congrArg (fun k ↦ Subobject (D.baseChangeModule (D.testAt k))) e) q.ker

/-- Along `rfl`, the transported kernel is the kernel itself. -/
@[simp]
theorem kerAt_rfl {U : BigFppfOver B S hS} (q : D.TotalQuotient Q U) : q.kerAt rfl = q.ker :=
  rfl

/-- Two elements of the total presheaf with the same structure morphism and the same kernel
are equal. -/
theorem mk_eq_mk {U : BigFppfOver B S hS} {h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y}
    {K K' : Subobject (D.baseChangeModule (D.testAt h))} (e : K = K')
    (hK : K ∈ Q (D.testAt h)) (hK' : K' ∈ Q (D.testAt h)) :
    (⟨h, K, hK⟩ : D.TotalQuotient Q U) = ⟨h, K', hK'⟩ := by
  subst e; rfl

/-- The transported kernel satisfies the condition again. -/
theorem kerAt_mem {U : BigFppfOver B S hS} (q : D.TotalQuotient Q U)
    {h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e : q.hom = h) :
    q.kerAt e ∈ Q (D.testAt h) := by
  subst e; exact q.mem

/-- Equal elements of the total presheaf have equal transported kernels. -/
theorem kerAt_congr {U : BigFppfOver B S hS} {q q' : D.TotalQuotient Q U} (eq : q = q')
    {h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e : q.hom = h) (e' : q'.hom = h) :
    q.kerAt e = q'.kerAt e' := by
  subst eq; rfl

/-- An element of the total presheaf is determined by its structure morphism and its kernel. -/
theorem mk_eq {U : BigFppfOver B S hS} (q : D.TotalQuotient Q U)
    {h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e : q.hom = h)
    {K : Subobject (D.baseChangeModule (D.testAt h))} (hK : K ∈ Q (D.testAt h))
    (hk : K = q.kerAt e) : (⟨h, K, hK⟩ : D.TotalQuotient Q U) = q := by
  subst hk; subst e; rfl

end TotalQuotient

/-! ### The total presheaf -/

/-- The total presheaf over the base scheme `S` of a pullback-stable condition `Q` on quotients:
its value at a scheme `U` of the big fppf site of `S` is the set of pairs consisting of a
morphism `h : U ⟶ Y` and a quotient of `F_U` over the test scheme `(U, h)` satisfying `Q`, and
its action on `g : V ⟶ U` restricts the morphism and pulls back the quotient.

The two functor laws are the two functor laws of pullback of quotients, with no transport in
between: the test scheme of the restriction of `h` along `g` is spelled as the test scheme of
`map g ≫ h`, and the identity and composition laws of `schemeSpaceFunctor` hold
definitionally. -/
def totalQuotientFunctor (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T') :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj U := D.TotalQuotient Q U.unop
  map {_ _} g := ↾fun q ↦
    { hom := (schemeSpaceFunctor B S hS).map g.unop ≫ q.hom
      ker := D.quotientPullback (D.testAtMap g.unop q.hom) q.ker
      mem := hQ _ _ q.mem }
  map_id _ := congrArg TypeCat.ofHom (funext fun q ↦
    TotalQuotient.mk_eq_mk (D.quotientPullback_id hc (D.testAt q.hom) q.ker) _ q.mem)
  map_comp {_ _ _} g k := congrArg TypeCat.ofHom (funext fun q ↦
    TotalQuotient.mk_eq_mk
      ((congrArg (fun m ↦ D.quotientPullback m q.ker)
          (D.testAtMap_comp k.unop g.unop q.hom)).trans
        (D.quotientPullback_comp hc (D.testAtMap' k.unop g.unop q.hom)
          (D.testAtMap g.unop q.hom) q.ker)) _ _)

variable (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')

/-- The structure morphism of a restriction is the restricted structure morphism. -/
@[simp]
theorem totalQuotientFunctor_map_hom {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (q : D.TotalQuotient Q U) :
    ((D.totalQuotientFunctor hc Q hQ).map g.op q).hom =
      (schemeSpaceFunctor B S hS).map g ≫ q.hom :=
  rfl

/-- The kernel of a restriction is the pullback of the kernel along the induced morphism of
test schemes. -/
@[simp]
theorem totalQuotientFunctor_map_ker {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (q : D.TotalQuotient Q U) :
    ((D.totalQuotientFunctor hc Q hQ).map g.op q).ker =
      D.quotientPullback (D.testAtMap g q.hom) q.ker :=
  rfl

/-- Pulling back a transported kernel is transporting the pulled-back kernel. -/
theorem quotientPullback_kerAt {V W : BigFppfOver B S hS} (k : W ⟶ V)
    (q : D.TotalQuotient Q V) {h : (schemeSpaceFunctor B S hS).obj V ⟶ D.Y} (e : q.hom = h) :
    D.quotientPullback (D.testAtMap k h) (q.kerAt e) =
      ((D.totalQuotientFunctor hc Q hQ).map k.op q).kerAt
        (congrArg (fun m ↦ (schemeSpaceFunctor B S hS).map k ≫ m) e) := by
  subst e; rfl

/-! ### The descent of quotients along a covering of a test scheme -/

/-- **The faithfulness clause of Stacks 04W8 for the coverings of a test scheme**, carried as a
hypothesis: a quotient of `F_U` over a test scheme `(U, h)` is determined by its pullbacks to
the members of an fppf covering of `U`.

In the source this is part of the bijection of Remark 08IU, whose inverse is fppf descent of
quasi-coherent modules.  A consumer discharges it from the faithfulness clause of Stacks 04W8
for the covering `{X_{U_i} ⟶ X_U}`. -/
def QuotientsSeparatedForCoverings
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))) : Prop :=
  ∀ ⦃U : BigFppfOver B S hS⦄ (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) (R : Sieve U),
    R ∈ BigFppfOver.topology B S hS U →
      ∀ K₀ K₁ : Subobject (D.baseChangeModule (D.testAt h)),
        K₀ ∈ Q (D.testAt h) → K₁ ∈ Q (D.testAt h) →
        (∀ (V : BigFppfOver B S hS) (g : V ⟶ U), R.arrows g →
          D.quotientPullback (D.testAtMap g h) K₀ =
            D.quotientPullback (D.testAtMap g h) K₁) →
        K₀ = K₁

/-- **The effectivity clause of Remark 08IU for the coverings of a test scheme**, carried as a
hypothesis: a family of quotients of the `F_{U_i}` for an fppf covering of a test scheme
`(U, h)`, agreeing after further pullback, comes from a quotient of `F_U`.

This is the half of the bijection of Remark 08IU whose inverse is fppf descent of
quasi-coherent modules.  It is discharged from the fullness and the effectivity of descent along
the covering `{X_{U_i} ⟶ X_U}` together with the two inputs the source cites for the
conditions, Morphisms of Spaces, Lemma 67.31.5 for flatness over the base and Descent on Spaces,
Lemma 74.6.2 for finite presentation; for the quotients of Situation 082M this is
`AlgebraicGeometry.Space.QuotientSituation.quotientsGlueAlongCoverings_quotients` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorFpqcSheaf.lean`. -/
def QuotientsGlueAlongCoverings
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))) : Prop :=
  ∀ ⦃U : BigFppfOver B S hS⦄ (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) (R : Sieve U),
    R ∈ BigFppfOver.topology B S hS U →
      ∀ K : ∀ (V : BigFppfOver B S hS) (g : V ⟶ U), R.arrows g →
          Subobject (D.baseChangeModule (D.testAtRestrict g h)),
        (∀ (V : BigFppfOver B S hS) (g : V ⟶ U) (hg : R.arrows g),
          K V g hg ∈ Q (D.testAtRestrict g h)) →
        (∀ (W V : BigFppfOver B S hS) (k : W ⟶ V) (g : V ⟶ U) (hg : R.arrows g),
          D.quotientPullback (D.testAtMap' k g h) (K V g hg) =
            K W (k ≫ g) (R.downward_closed hg k)) →
        ∃ K₀ : Subobject (D.baseChangeModule (D.testAt h)), K₀ ∈ Q (D.testAt h) ∧
          ∀ (V : BigFppfOver B S hS) (g : V ⟶ U) (hg : R.arrows g),
            D.quotientPullback (D.testAtMap g h) K₀ = K V g hg

/-! ### The sheaf condition -/

/-- **The reduction of the sheaf condition for the total presheaf to the descent of quotients
over a fixed test scheme.**  The total presheaf of a pullback-stable condition on quotients is
an fppf sheaf on the big fppf site of `S` as soon as the quotients over a test scheme are
separated for and glue along the fppf coverings of that test scheme.

The clause of the sheaf condition concerning the structure morphisms `U ⟶ Y` is proved here
rather than assumed: a compatible family of them is a compatible family of sections of `Y`
under the Yoneda identification, and `Y` is an fppf sheaf because it is an algebraic space,
which is the first clause of Stacks 025Y. -/
theorem isSheaf_totalQuotientFunctor (hsep : D.QuotientsSeparatedForCoverings Q)
    (hglue : D.QuotientsGlueAlongCoverings Q) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.totalQuotientFunctor hc Q hQ) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR x hx
  have hxs := hx.to_sieveCompatible
  -- The structure morphisms form a compatible family of sections of `Y`.
  have hycomp : Presieve.FamilyOfElements.Compatible
      (fun ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ U) (hg : R.arrows g) ↦
        yonedaEquiv (x g hg).hom.hom) := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hw
    exact (yonedaEquiv_naturality (x f₁ h₁).hom.hom g₁).trans
      ((congrArg (fun q ↦ yonedaEquiv (TotalQuotient.hom q).hom) (hx g₁ g₂ h₁ h₂ hw)).trans
        (yonedaEquiv_naturality (x f₂ h₂).hom.hom g₂).symm)
  obtain ⟨y, hy, hyu⟩ :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 D.Y.property.isSheaf R hR) _ hycomp
  -- The amalgamated structure morphism.
  set hU : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y := ObjectProperty.homMk (yonedaEquiv.symm y)
    with hUdef
  have hgh : ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ U) (hg : R.arrows g),
      (x g hg).hom = (schemeSpaceFunctor B S hS).map g ≫ hU := by
    intro V g hg
    refine ObjectProperty.hom_ext _ ?_
    have e : ((schemeSpaceFunctor B S hS).map g ≫ hU).hom =
        yonedaEquiv.symm (D.Y.obj.map g.op y) :=
      yonedaEquiv_symm_naturality_left g D.Y.obj y
    rw [e, hy g hg]
    exact (Equiv.symm_apply_apply yonedaEquiv (x g hg).hom.hom).symm
  -- The quotients now all live over restrictions of the single test scheme `(U, hU)`.
  have hKmem : ∀ (V : BigFppfOver B S hS) (g : V ⟶ U) (hg : R.arrows g),
      (x g hg).kerAt (hgh g hg) ∈ Q (D.testAtRestrict g hU) :=
    fun _ g hg ↦ (x g hg).kerAt_mem _
  have hKcomp : ∀ (W V : BigFppfOver B S hS) (k : W ⟶ V) (g : V ⟶ U) (hg : R.arrows g),
      D.quotientPullback (D.testAtMap' k g hU) ((x g hg).kerAt (hgh g hg)) =
        (x (k ≫ g) (R.downward_closed hg k)).kerAt (hgh (k ≫ g) (R.downward_closed hg k)) := by
    intro W V k g hg
    exact (D.quotientPullback_kerAt hc Q hQ k (x g hg) (hgh g hg)).trans
      (TotalQuotient.kerAt_congr (hxs g k hg).symm _
        (hgh (k ≫ g) (R.downward_closed hg k)))
  obtain ⟨K₀, hK₀mem, hK₀⟩ :=
    hglue hU R hR (fun _ g hg ↦ (x g hg).kerAt (hgh g hg)) hKmem hKcomp
  refine ⟨⟨hU, K₀, hK₀mem⟩, fun V g hg ↦ ?_, fun t ht ↦ ?_⟩
  · exact TotalQuotient.mk_eq (x g hg) (hgh g hg) _ (hK₀ V g hg)
  -- Uniqueness: the structure morphism first, then the quotient.
  · have hth : t.hom = hU := by
      refine ObjectProperty.hom_ext _ ?_
      have hya : yonedaEquiv t.hom.hom = y :=
        hyu _ fun V g hg ↦ (yonedaEquiv_naturality t.hom.hom g).trans
          (congrArg (fun q ↦ yonedaEquiv (TotalQuotient.hom q).hom) (ht g hg))
      exact (Equiv.symm_apply_apply yonedaEquiv t.hom.hom).symm.trans
        (congrArg yonedaEquiv.symm hya)
    refine (TotalQuotient.mk_eq t hth hK₀mem ?_).symm
    refine (hsep hU R hR (t.kerAt hth) K₀ (t.kerAt_mem hth) hK₀mem fun V g hg ↦ ?_).symm
    exact ((D.quotientPullback_kerAt hc Q hQ g t hth).trans
      (TotalQuotient.kerAt_congr (ht g hg) _ (hgh g hg))).trans (hK₀ V g hg).symm

/-! ### The two presheaves of the source -/

/-- **Stacks 082P.**  `Q_{F/X/Y}` as a presheaf on the big fppf site of `S`: its value at a
scheme `U` over `S` is the set of pairs `(h, Q)` consisting of a morphism `h : U ⟶ Y` and a
quotient of `F_U`, quasi-coherent and flat over `U`, for the test scheme `(U, h)`. -/
def totalQuotientsFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  D.totalQuotientFunctor hc D.quotients fun m K hK ↦
    D.quotientPullback_mem_quotients' m K hK

/-- **Stacks 082P.**  `Q^{fp}_{F/X/Y}` as a presheaf on the big fppf site of `S`: the
subpresheaf of pairs whose quotient is of finite presentation. -/
def totalFinitePresentationQuotientsFunctor
    (hfp : D.PullbackPreservesFinitePresentation) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  D.totalQuotientFunctor hc D.finitePresentationQuotients fun m K hK ↦
    ⟨D.quotientPullback_mem_quotients' m K hK.1,
      SheafOfModules.IsFinitePresentationOnSite.of_iso (D.quotientPullbackCokernelIso m K).symm
        (hfp m (D.quotientModule _ K) hK.2)⟩

/-- The quotient half of an element of the total presheaf is an element of the value of the
functor of quotients of Stacks 082N at the test scheme of its structure morphism: the presheaf
above really is the total presheaf of that functor. -/
def TotalQuotient.toQuotientsFunctorObj
    {U : BigFppfOver B S hS} (q : D.TotalQuotient D.quotients U) :
    D.quotientsFunctor.obj (op (D.testAt q.hom)) :=
  ⟨q.ker, q.mem⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
