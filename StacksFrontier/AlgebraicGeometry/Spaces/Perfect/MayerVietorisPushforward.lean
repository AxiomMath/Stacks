module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
import StacksCore.Tactic.StacksAttribute

/-!
# Mayer–Vietoris for direct images along an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection, write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ X` and `j_{Y,*}` for the direct image.  Stacks 08GW says
that a sheaf of `𝒪_X`-modules `F` sits in a short exact sequence

`0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P ⟶ 0`

and that an object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished
triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{P,*}E|_P ⟶ E[1]`.

This is the *direct image* statement, not the extension-by-zero statement of Stacks 08GV; the
two are adjoint to one another, and that adjunction is how part (1) is obtained here.

## Main definitions

* `CategoryTheory.PushforwardMayerVietoris.conjugateUnit`: for an adjunction `Ψ ⊣ Φ` of
  endofunctors, the natural map `𝟭 ⟶ Φ` conjugate to a natural map `Ψ ⟶ 𝟭`.  For
  `Ψ = j_!((-)|_Y)` and `Φ = j_{Y,*}((-)|_Y)` it turns the counit `j_{Y!}F|_Y ⟶ F` of Stacks
  08GV into the canonical map `F ⟶ j_{Y,*}F|_Y`.
* `CategoryTheory.PushforwardMayerVietoris.unitCochainMap`: a natural map `𝟭 ⟶ Φ` applied
  degreewise to a cochain complex.
* `AlgebraicGeometry.Space.edsRestrictPushOpen`, `…edsRestrictPushEtale`,
  `…edsRestrictPushInter`: the three functors `F ↦ j_{Y,*}(F|_Y)` of the square, and
  `AlgebraicGeometry.Space.edsAdjOpen`, `…edsAdjEtale`, `…edsAdjInter`: the three adjunctions
  `(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU, whose units are the canonical maps `F ⟶ j_{Y,*}F|_Y`.
* `CategoryTheory.PushforwardMayerVietoris.rightDerivedObjIsoOfKInjective` and
  `…exists_isKInjective_representative_of_universe`: Stacks 070K and Stacks 079P, repeated at
  unrestricted universes (see the implementation notes).

## Main results

* `CategoryTheory.PushforwardMayerVietoris.conjugateUnit_comp_counit`: the conjugate of the
  counit of `s ⊣ r`, taken for the composite adjunction `r ⋙ s ⊣ r ⋙ p`, is the unit of
  `r ⊣ p`.  This is what identifies the first map of the direct-image sequence with the
  canonical one.
* `CategoryTheory.PushforwardMayerVietoris.exact_and_mono_conjugate`: granted the
  extension-by-zero short exact sequence of Stacks 08GV part (1), the Mayer–Vietoris complex of
  the conjugate direct-image maps is exact at its first two spots.
* `CategoryTheory.PushforwardMayerVietoris.mem_distTriang_unitBiprod_of_natural_shortExact`:
  the homological passage from part (1) to part (2) — a natural short exact sequence
  `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` of additive endofunctors gives, at every cochain
  complex, a distinguished triangle.  *No exactness of the functors is assumed*, which is what
  the direct images need.
* `CategoryTheory.PushforwardMayerVietoris.epi_conjugate`: **the surjectivity on the right**,
  in the abstract form.  Granted the extension-by-zero short exact sequence at every object, the
  Mayer–Vietoris map `Φ_U F ⊕ Φ_V F ⟶ Φ_P F` is an epimorphism for every `F`, in any abelian
  category with enough injectives.  This is the step the source takes with Stacks 01FW, and it
  discharges the hypothesis `hepi`.
* `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris`: Stacks 08GW part (1) for an
  elementary distinguished square, for an arbitrary choice of the two comparisons out of the
  intersection, granted part (1) of Stacks 08GV and the surjectivity on the right.
* `AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietoris` and
  `…epi_edsRestrictPushMayerVietorisComparison`: the surjectivity on the right for the modules on
  an algebraic space — from part (1) of Stacks 08GV, and then with that discharged too.
* `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisComparison`: Stacks 08GW
  part (1), at the two comparisons `AlgebraicGeometry.Space.edsShriekOpenComparison` and
  `AlgebraicGeometry.Space.edsShriekEtaleComparison` of the square, **with nothing granted** —
  for an arbitrary choice of the extension-by-zero data, which is what keeps the tag off it.
* `AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`: the right
  derived functor of an additive endofunctor of the `𝒪_X`-modules exists, which exhibits
  inhabitants for the derived-functor hypotheses of the next items.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris`:
  Stacks 08GW part (2) for an elementary distinguished square, granted part (1).
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisComparison`:
  Stacks 08GW part (2), at the two comparisons of the square, **with nothing granted** — for
  arbitrary right derived functors and with the maps of the triangle existentially quantified,
  which is what keeps the tag off it.

The two declarations that **carry Stacks 08GW** are in the sibling
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag`; see *Where Stacks
08GW is registered, and why not here* below.

## Implementation notes

*Part (1) is the adjoint of Stacks 08GV part (1), and that is how it is proved.*  The source
proves part (1) by applying `Hom_{𝒪_X}(-, F)` to the extension-by-zero sequence

`0 ⟶ j_{P!}𝒪_P ⟶ j_{U!}𝒪_U ⊕ j_{V!}𝒪_V ⟶ 𝒪_X ⟶ 0`

of Stacks 08GV part (1) and identifying `𝓗om(j_{Y!}𝒪_Y, F)` with `j_{Y,*}(F|_Y)`.  At the level
of hom-*groups* that identification is free: `j_{Y!}((-)|_Y)` is left adjoint to
`j_{Y,*}((-)|_Y)`, being the composite of `j_{Y!} ⊣ (-)|_Y` with `(-)|_Y ⊣ j_{Y,*}`, so
`Hom(j_{Y!}G|_Y, F) ≅ Hom(G, j_{Y,*}F|_Y)` naturally.  Running the source's argument through
that adjunction gives the *kernel* half of part (1) unconditionally from Stacks 08GV part (1),
and it also pins the two comparison maps into `j_{P,*}F|_P`: they are the images of 08GV's two
maps under `CategoryTheory.conjugateEquiv`, not arbitrary transformations compatible with the
units.

*The surjectivity on the right needs no site, and is proved.*  This is the one step the
adjunction does not hand over, and it is where the source leaves the hom-group level: it reduces
to `W = X` by Stacks 08GN, applies `Hom_{𝒪_X}(-, F)` to the sequence above, and observes that
the obstruction to lifting a section lies in `Ext^1_{𝒪_X}(𝒪_X, F) = H^1(X, F)` (Stacks 03F1) and
dies on an étale covering by Stacks 01FW, which is harmless because the conclusion it is after
is local surjectivity.  `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` does it without
any of that.  The reason it can is that *epimorphy of a map is itself a statement that survives
precomposition with an epimorphism*: a map is an epimorphism exactly when some epimorphism
factors through it, so only one map onto `Φ_P F` has to be lifted — the identity, and only after
precomposition with an epimorphism of our choosing.  The obstruction to lifting the identity is
the class in `Ext^1(Φ_P F, F)` represented, after embedding `F` in an injective object `I`, by a
map `Φ_P F ⟶ I/F`; pulling back along the epimorphism `I ⟶ I/F` kills it, and the pullback
projection is the epimorphism we are allowed to precompose with.  So the covering of the source's
argument is replaced by a single pullback, the whole thing lives in an arbitrary abelian category
with enough injectives, and the small étale site — in particular the *sheaf-level* internal hom
`𝓗om_{𝒪_X}(j_{Y!}𝒪_Y, F) ≅ j_{Y,*}(F|_Y)`, which the library does not carry — never enters.

*Extension by zero enters as data.*  As in `StacksDraft.AlgebraicGeometry.Spaces.Perfect.`
`MayerVietoris` and in Stacks 08HA, `j_{Y!}` is not constructed but is given by a functor
together with an adjunction exhibiting it as a left adjoint of restriction, which pins it up to
a unique compatible isomorphism.  The *direct image* `j_{Y,*}` is not data: it is
`AlgebraicGeometry.Space.modulePushforward`, and the adjunction `(-)|_Y ⊣ j_{Y,*}` is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`, the reading of Stacks 03LU through the
identification of Stacks 03LV.  So the whole conclusion of part (1) is stated in terms of
existing objects; `j_{Y!}` appears only in the hypotheses it is needed for.

*Part (2) is the source's proof, and needs no exactness.*  Unlike `j_{Y!}((-)|_Y)`, the functor
`j_{Y,*}((-)|_Y)` is not exact, so part (2) cannot be read off part (1) by applying the functors
degreewise to an arbitrary representative of `E` — this is exactly the difference from Stacks
08GV part (2).  The source instead represents `E` by a K-injective complex `I`, which is Stacks
079P (`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`); on such a complex any
right derived functor is computed by the functor itself, which is Stacks 070K
(`CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso`
`_isKInjective`); and the triangle is then the one attached by Stacks 014Z and 0152 to the short
exact sequence of cochain complexes that part (1) gives degreewise
(`DerivedCategory.triangleOfSES_distinguished`).  The source's appeal to Stacks 08FI — that
restriction preserves K-injectivity — is needed only to split `Rj_{Y,*}((-)|_Y)` into
`Rj_{Y,*}` after the exact `(-)|_Y`; it is not needed here, because `R_Y` is taken to be a right
derived functor of the composite, and the K-injective resolutions of Stacks 079P compute that
composite directly.  A caller holding `Rj_{Y,*}` and wanting to feed `Rj_{Y,*} ∘ (-)|_Y` as
`R_Y` can do so through `AlgebraicGeometry.Space.isKInjective_etaleModulePullback`, the
form of Stacks 08FI at this site.

*The derived functors are arbitrary choices here.*  As in
`AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso` (Stacks 08GE), the three
functors `R_U`, `R_V`, `R_P` are arguments together with the natural transformations exhibiting
them as right derived functors, so the result applies to whichever model of `Rj_{Y,*}((-)|_Y)`
a caller has.  The statement that carries Stacks 08GW part (2) does *not* quantify over them:
it takes the chosen `CategoryTheory.Functor.totalRightDerived`, which exists by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`, and is
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`
of `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag`.

*Why Stacks 070K and 079P are repeated here.*  `CategoryTheory.rightDerivedObjIso` and
`CategoryTheory.exists_isKInjective_representative` are stated for a category whose objects lie
one universe above its morphisms.  `AlgebraicGeometry.Space.Modules.{u, u}` is not of that
shape — its objects and its morphisms both land in `Type (u + 1)` — so the two statements are
repeated with unrestricted universes.  Their proofs are unchanged; every input they use is
universe-polymorphic already.

*The adjoint-transpose characterisation of a conjugate is reused, not repeated.*  That
`adj₁.homEquiv c X f ≫ (conjugateEquiv adj₁ adj₂ α).app X = adj₂.homEquiv c X (α.app c ≫ f)`
is `CategoryTheory.homEquiv_comp_conjugateEquiv`, already in the repository at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InternalHomMapLeftConjugate.lean`; it is the only
thing taken from that chain, and it is what the whole of part (1) runs on.  What is added here
is the special case `conjugateUnit` for a map `Ψ ⟶ 𝟭`, where the second adjunction is the
identity, together with its own transpose characterisation.

*Why the two comparison maps are written out.*  An `abbrev` for
`conjugateEquiv ((edsAdjOpen …).comp adjU) ((edsAdjInter …).comp adjP) a` makes the unification
of the geometric statement against the abstract lemmas exceed the recursion limit, while the
same statement with the term written out unifies immediately.  The conjugates are therefore
spelled out in the statements rather than abbreviated.

### Where Stacks 08GW is registered, and why not here

**No declaration in this module carries Stacks 08GW.**  The two attributes are in the sibling
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag`, on

* part (1): `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisLowerShriek`,
* part (2):
  `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`,

which are the two unqualified statements of this module instantiated so that nothing at all is
quantified over beyond the square: extension by zero is
`AlgebraicGeometry.Space.etaleModuleLowerShriek` with its adjunction, as in Stacks 08GV, and
the three right derived functors are the chosen `CategoryTheory.Functor.totalRightDerived`,
which exist by `AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`.
Part (2) there also states the *canonical* triangle — the derived units of the adjunctions
`(-)|_Y ⊣ j_{Y,*}` and the derived transformations of the two comparisons of part (1) — with
only the connecting map existentially quantified.

*What the statements of this module still quantify over.*  All of them take the three
extension-by-zero functors `j_{Y!}` with the adjunctions exhibiting them as left adjoints of
restriction, and the derived forms also take the three right derived functors with their
comparisons; part (2) here asserts only the *existence* of maps making a triangle with those
three terms distinguished.  Nothing *mathematical* is assumed — part (1) of Stacks 08GV is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris` and is discharged, and the
surjectivity on the right, the hypothesis `hepi` of the variants below, is
`AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietorisComparison` — but the quantifiers are
real, and an existential over the maps of the triangle is weaker than the tag.  Hence the
registrations live in the sibling module and these forms are kept unregistered, each because it
is the one that applies to a model of `j_{Y!}` or of `Rj_{Y,*}((-)|_Y)` other than the library's
own.

*The unregistered variants.*  Six variants are kept as theorems: part (1) and part (2)
granted `hMV`, part (1) of Stacks 08GV; the same two at the comparisons of the square, granted
`hepi`; and the two unqualified forms of this module, with the extension-by-zero and
derived-functor quantifiers.  None of them is registered.

*The argument that discharges `hepi` is not the source's.*  The source
kills the obstruction class in `Ext^1_{𝒪_X}(𝒪_X, F) = H^1(X, F)` only after an étale covering,
by Stacks 01FW, which it can afford because what it is proving is local surjectivity of a map of
sheaves.  `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` instead uses that epimorphy is
*already* a statement up to precomposition with an epimorphism: `h` is an epimorphism as soon as
some epimorphism factors through it, so it suffices to lift the identity of `Φ_P F` after
precomposing with an epimorphism of our choosing, and `Ext^1(-, F)` is effaceable — in an abelian
category with enough injectives every class dies after precomposition with a suitable
epimorphism, namely the projection of the pullback of `I ⟶ I/F` along the map `Φ_P F ⟶ I/F` that
represents the class.  So no site, no cohomology, no covering, and no sheaf-level internal hom:
the only thing the modules on an algebraic space contribute beyond part (1) of Stacks 08GV is
enough injectives, which they have by
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`.

*What this makes unnecessary.*  The étale-local route
would need: a module-level form of the spaces-étale
extension and of its sections (upgrading the set-level
`AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso_obj`), covering-sieve forms of
the two geometric facts that `{U ⟶ X, V ⟶ X}` covers `X` and that `V ×_X V` is covered by its
diagonal together with its part over `U`, and a bridge identifying the two
`CategoryTheory.conjugateEquiv` comparisons with restriction of sections along the projections of
the square.  None of that is needed for Stacks 08GW, and none of it is in the library.  The
obstruction on that route — that the chart description of
`AlgebraicGeometry.Space.modulePushforward` exists only for a *representable* morphism, and that
`AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` does not supply representability — is
real, and is simply not on the path.

*The injective case is a special case, not a substitute.*
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisRelative.lean`) proves part (1) at an
injective `F` directly, by splitting the right-hand map with
`CategoryTheory.Injective.factorThru`, and the derived consumers Stacks 08JK and Stacks 0CRS are
unconditional through it.  It is still the cheaper statement to apply when `F` is injective,
and `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` is that same argument with the
injective object interposed rather than assumed.

Nothing of either part is missing.  For part (1): the vanishing of the composite, the exactness
at the first two spots and the surjectivity on the right are all proved.  For part (2): the
K-injective resolution (Stacks 079P), the computation of a right derived functor on it (Stacks
070K) and the triangle of a short exact sequence of cochain complexes (Stacks 014Z, Stacks 0152)
are all proved, and part (1) is fed to it from this file.

## References

* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 03F1](https://stacks.math.columbia.edu/tag/03F1)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/
@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.PushforwardMayerVietoris

/-! ### The unit of a right adjoint conjugate to a counit-style map -/

section Conjugate

variable {A : Type*} [Category* A] {Ψ Φ : A ⥤ A}

/-- The natural map `𝟭 ⟶ Φ` conjugate, under an adjunction `Ψ ⊣ Φ`, to a natural map
`Ψ ⟶ 𝟭`. -/
def conjugateUnit (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) : 𝟭 A ⟶ Φ :=
  conjugateEquiv Adjunction.id adj c

/-- The component of the conjugate unit at `M` is the unit of the adjunction at `M` followed by
`Φ` applied to `c.app M`. -/
lemma conjugateUnit_app (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) (M : A) :
    (conjugateUnit adj c).app M = adj.unit.app M ≫ Φ.map (c.app M) := by
  simp [conjugateUnit]

/-- For an adjunction `Ψ ⊣ Φ` and `c : Ψ ⟶ 𝟭`, the adjoint transpose of `c.app G ≫ ψ` is
`ψ` followed by the conjugate unit. -/
lemma homEquiv_comp_conjugateUnit (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) {G F : A} (ψ : G ⟶ F) :
    adj.homEquiv G F (c.app G ≫ ψ) = ψ ≫ (conjugateUnit adj c).app F := by
  rw [Adjunction.homEquiv_unit, Φ.map_comp, ← Category.assoc, ← conjugateUnit_app]
  exact ((conjugateUnit adj c).naturality ψ).symm

/-- The adjoint transpose of `c.app F` is the component at `F` of the conjugate unit. -/
lemma homEquiv_conjugateUnit_app (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) (F : A) :
    adj.homEquiv F F (c.app F) = (conjugateUnit adj c).app F := by
  simpa using homEquiv_comp_conjugateUnit adj c (𝟙 F)

/-- The adjoint transpose of the zero morphism is zero, when the right adjoint preserves zero
morphisms. -/
lemma homEquiv_zero [HasZeroMorphisms A] (adj : Ψ ⊣ Φ) [Φ.PreservesZeroMorphisms]
    (G F : A) : adj.homEquiv G F 0 = 0 := by
  simp [Adjunction.homEquiv_unit]

/-- **The adjoint transpose of a difference is the difference of the transposes**, when the
right adjoint is additive.  This is what lets the Mayer–Vietoris map out of a biproduct be
transposed in one piece. -/
lemma homEquiv_sub [Preadditive A] (adj : Ψ ⊣ Φ) [Φ.Additive] {G F : A}
    (f g : Ψ.obj G ⟶ F) :
    adj.homEquiv G F (f - g) = adj.homEquiv G F f - adj.homEquiv G F g := by
  simp [Adjunction.homEquiv_unit, Φ.map_sub, Preadditive.comp_sub]

/-- The conjugate unit followed by a conjugate comparison is the transpose of the comparison
followed by the map `c`. -/
private lemma conjugateUnit_app_comp_conjugateEquiv_app {Ψ' Φ' : A ⥤ A} (adj : Ψ ⊣ Φ)
    (adj' : Ψ' ⊣ Φ') (c : Ψ ⟶ 𝟭 A) (α : Ψ' ⟶ Ψ) (F : A) :
    (conjugateUnit adj c).app F ≫ (conjugateEquiv adj adj' α).app F =
      adj'.homEquiv F F (α.app F ≫ c.app F) := by
  rw [← homEquiv_conjugateUnit_app adj c F,
    homEquiv_comp_conjugateEquiv adj adj' α F F (c.app F)]

/-- A map killed by the conjugate unit is killed by `c` on the left. -/
private lemma comp_eq_zero_of_comp_conjugateUnit_app_eq_zero [HasZeroMorphisms A]
    [Φ.PreservesZeroMorphisms] (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) {G F : A} (ψ : G ⟶ F)
    (h : ψ ≫ (conjugateUnit adj c).app F = 0) : c.app G ≫ ψ = 0 :=
  (adj.homEquiv G F).injective (by rw [homEquiv_comp_conjugateUnit, h, homEquiv_zero])

/-- A map `l` whose composite with `c` is the inverse transpose of `k` satisfies
`l ≫ conjugateUnit = k`. -/
private lemma comp_conjugateUnit_app_eq_of_comp_eq (adj : Ψ ⊣ Φ) (c : Ψ ⟶ 𝟭 A) {G F : A}
    (k : G ⟶ Φ.obj F) (l : G ⟶ F) (h : c.app G ≫ l = (adj.homEquiv G F).symm k) :
    l ≫ (conjugateUnit adj c).app F = k := by
  rw [← homEquiv_comp_conjugateUnit, h, Equiv.apply_symm_apply]

/-- The conjugate unit of the counit of `s ⊣ r`, taken for the composite adjunction
`r ⋙ s ⊣ r ⋙ p` of `r ⊣ p` and `s ⊣ r`, is the unit of `r ⊣ p`.

For `r` restriction along an étale morphism, `s` extension by zero and `p` the direct image,
this says that the map `F ⟶ j_*(F|_U)` produced by conjugating the counit `j_!(F|_U) ⟶ F` is
the canonical one, the unit of `(-)|_U ⊣ j_*`. -/
lemma conjugateUnit_comp_counit {D : Type*} [Category* D]
    {r : A ⥤ D} {p : D ⥤ A} {s : D ⥤ A} (adjL : r ⊣ p) (adjS : s ⊣ r) :
    conjugateUnit (adjL.comp adjS) adjS.counit = adjL.unit := by
  ext M
  rw [conjugateUnit_app]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj, Category.assoc,
    ← p.map_comp, Adjunction.right_triangle_components, Functor.map_id, Category.comp_id]

end Conjugate

/-! ### From the extension-by-zero sequence to the direct-image sequence -/

section Dualize

section Additive

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
  {ΨU ΨV ΨP ΦU ΦV ΦP : A ⥤ A}
  (adjU : ΨU ⊣ ΦU) (adjV : ΨV ⊣ ΦV) (adjP : ΨP ⊣ ΦP)
  (cU : ΨU ⟶ 𝟭 A) (cV : ΨV ⟶ 𝟭 A) (α : ΨP ⟶ ΨU) (β : ΨP ⟶ ΨV)
  (hz : ∀ M, biprod.lift (α.app M) (-(β.app M)) ≫
    biprod.desc (cU.app M) (cV.app M) = 0)

/-- `(a, -b)` followed by `(f, g)` vanishes iff `a ≫ f = b ≫ g`. -/
private lemma lift_neg_comp_desc_eq_zero_iff {X Y Z W : A} (a : X ⟶ Y) (b : X ⟶ Z) (f : Y ⟶ W)
    (g : Z ⟶ W) : biprod.lift a (-b) ≫ biprod.desc f g = 0 ↔ a ≫ f = b ≫ g := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero]

include hz in
/-- The two extension-by-zero maps out of the intersection agree after composing with the two
counits, as the vanishing of the Mayer–Vietoris composite says. -/
lemma comp_counit_eq (M : A) : α.app M ≫ cU.app M = β.app M ≫ cV.app M := by
  exact (lift_neg_comp_desc_eq_zero_iff _ _ _ _).mp (hz M)

include hz in
/-- The Mayer–Vietoris composite of the conjugate maps vanishes: this is the statement that
`F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P` is a complex. -/
lemma zero_conjugate (F : A) :
    biprod.lift ((conjugateUnit adjU cU).app F) ((conjugateUnit adjV cV).app F) ≫
        biprod.desc ((conjugateEquiv adjU adjP α).app F)
          (-((conjugateEquiv adjV adjP β).app F)) = 0 := by
  rw [biprod.lift_desc, Preadditive.comp_neg, conjugateUnit_app_comp_conjugateEquiv_app,
    conjugateUnit_app_comp_conjugateEquiv_app, comp_counit_eq cU cV α β hz F]
  simp

include hz in
/-- `CategoryTheory.PushforwardMayerVietoris.zero_conjugate` for a first map presented up to an
equation with the conjugate units. -/
lemma zero_conjugate_of_eq (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV)
    (hηU : ηU = conjugateUnit adjU cU) (hηV : ηV = conjugateUnit adjV cV) (F : A) :
    biprod.lift (ηU.app F) (ηV.app F) ≫
      biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F)) = 0 := by
  subst hηU hηV
  exact zero_conjugate adjU adjV adjP cU cV α β hz F

end Additive

variable {A : Type u} [Category.{v} A] [Abelian A]
  {ΨU ΨV ΨP ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (adjU : ΨU ⊣ ΦU) (adjV : ΨV ⊣ ΦV) (adjP : ΨP ⊣ ΦP)
  (cU : ΨU ⟶ 𝟭 A) (cV : ΨV ⟶ 𝟭 A) (α : ΨP ⟶ ΨU) (β : ΨP ⟶ ΨV)
  (hz : ∀ M, biprod.lift (α.app M) (-(β.app M)) ≫
    biprod.desc (cU.app M) (cV.app M) = 0)
  (hGV : ∀ M, (ShortComplex.mk (biprod.lift (α.app M) (-(β.app M)))
  (biprod.desc (cU.app M) (cV.app M)) (hz M)).ShortExact)

include hz hGV in
/-- **The canonical map `F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V` is a monomorphism**, granted the
extension-by-zero short exact sequence: the surjection
`j_{U!}G|_U ⊕ j_{V!}G|_V ⟶ G` of that sequence kills anything the pair of conjugate units
kills. -/
lemma mono_conjugateUnit_lift (F : A) :
    Mono (biprod.lift ((conjugateUnit adjU cU).app F) ((conjugateUnit adjV cV).app F)) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro G ψ hψ
  have hU : ψ ≫ (conjugateUnit adjU cU).app F = 0 := by
    simpa using congrArg (fun t => t ≫ biprod.fst) hψ
  have hV : ψ ≫ (conjugateUnit adjV cV).app F = 0 := by
    simpa using congrArg (fun t => t ≫ biprod.snd) hψ
  have hd : biprod.desc (cU.app G) (cV.app G) ≫ ψ = 0 := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      simp [comp_eq_zero_of_comp_conjugateUnit_app_eq_zero _ _ _ hU,
        comp_eq_zero_of_comp_conjugateUnit_app_eq_zero _ _ _ hV]
  have := (hGV G).epi_g
  exact zero_of_epi_comp (biprod.desc (cU.app G) (cV.app G)) hd

omit [ΦP.Additive] in
include hz hGV in
/-- **Stacks 08GW part (1) minus its surjectivity**, in the abstract form.  Granted the
extension-by-zero short exact sequence of Stacks 08GV part (1) for every object, the
Mayer–Vietoris complex of the conjugate direct-image maps is exact at its first two spots:
`F` is the kernel of `j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P`.

The third spot — surjectivity onto `j_{P,*}F|_P` — is the obstruction that the source kills
étale locally with Stacks 01FW.  It is the hypothesis `hepi` of
`CategoryTheory.PushforwardMayerVietoris.shortExact_conjugate`, and it is *proved* from the same
inputs as this lemma in `CategoryTheory.PushforwardMayerVietoris.epi_conjugate`, which needs
only that the ambient category have enough injectives. -/
lemma exact_and_mono_conjugate (F : A) :
    (ShortComplex.mk
        (biprod.lift ((conjugateUnit adjU cU).app F) ((conjugateUnit adjV cV).app F))
        (biprod.desc ((conjugateEquiv adjU adjP α).app F)
          (-((conjugateEquiv adjV adjP β).app F)))
        (zero_conjugate adjU adjV adjP cU cV α β hz F)).Exact ∧
      Mono (biprod.lift ((conjugateUnit adjU cU).app F)
        ((conjugateUnit adjV cV).app F)) := by
  have hmono := mono_conjugateUnit_lift adjU adjV cU cV α β hz hGV F
  refine (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).mpr ⟨?_⟩
  refine KernelFork.IsLimit.ofι' _ _ (fun {G} k hk => ?_)
  -- the two components of `k`, and the hypothesis they satisfy
  have hkey : (k ≫ biprod.fst) ≫ (conjugateEquiv adjU adjP α).app F =
      (k ≫ biprod.snd) ≫ (conjugateEquiv adjV adjP β).app F := by
    refine sub_eq_zero.mp ?_
    simpa [biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg, sub_eq_add_neg]
      using hk
  -- transpose them across the adjunctions
  set φU := (adjU.homEquiv G F).symm (k ≫ biprod.fst) with hφU
  set φV := (adjV.homEquiv G F).symm (k ≫ biprod.snd) with hφV
  have hφ : α.app G ≫ φU = β.app G ≫ φV := by
    refine (adjP.homEquiv G F).injective ?_
    rw [← homEquiv_comp_conjugateEquiv adjU adjP α G F φU,
      ← homEquiv_comp_conjugateEquiv adjV adjP β G F φV,
      hφU, hφV, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hkey
  -- descend along the extension-by-zero sequence
  have hz0 : biprod.lift (α.app G) (-(β.app G)) ≫ biprod.desc φU φV = 0 :=
    (lift_neg_comp_desc_eq_zero_iff _ _ _ _).mpr hφ
  have hepiG := (hGV G).epi_g
  have hl := (hGV G).exact.g_desc (biprod.desc φU φV) hz0
  refine ⟨(hGV G).exact.desc (biprod.desc φU φV) hz0, ?_⟩
  have hlU : cU.app G ≫ (hGV G).exact.desc (biprod.desc φU φV) hz0 = φU := by
    simpa using congrArg (fun t => biprod.inl ≫ t) hl
  have hlV : cV.app G ≫ (hGV G).exact.desc (biprod.desc φU φV) hz0 = φV := by
    simpa using congrArg (fun t => biprod.inr ≫ t) hl
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst]
    exact comp_conjugateUnit_app_eq_of_comp_eq adjU cU _ _ hlU
  · rw [Category.assoc, biprod.lift_snd]
    exact comp_conjugateUnit_app_eq_of_comp_eq adjV cV _ _ hlV

omit [ΦP.Additive] in
include hz hGV in
/-- **Stacks 08GW part (1)**, in the abstract form: granted the extension-by-zero short exact
sequence of Stacks 08GV part (1) and the surjectivity `hepi`, the Mayer–Vietoris complex of the
conjugate direct-image maps is short exact.

`hepi` is `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` as soon as the ambient
category has enough injectives, so it is kept as a hypothesis here only to avoid imposing that
on a caller who has the surjectivity by other means — an injective `F`, say. -/
lemma shortExact_conjugate (F : A)
    (hepi : Epi (biprod.desc ((conjugateEquiv adjU adjP α).app F)
      (-((conjugateEquiv adjV adjP β).app F)))) :
    (ShortComplex.mk
      (biprod.lift ((conjugateUnit adjU cU).app F) ((conjugateUnit adjV cV).app F))
      (biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F)))
      (zero_conjugate adjU adjV adjP cU cV α β hz F)).ShortExact :=
  have h := exact_and_mono_conjugate adjU adjV adjP cU cV α β hz hGV F
  ShortComplex.ShortExact.mk' h.1 h.2 hepi

/-! The same two statements for a first map given only up to an equation with the conjugate
unit.  This is what a consumer applies: the equation discharges the identification of the
conjugate unit with the canonical one, in a setting where the heavy instances of the consumer's
category are not in play. -/

omit [ΦP.Additive] in
include hz hGV in
/-- `CategoryTheory.PushforwardMayerVietoris.shortExact_conjugate` for a first map presented up
to an equation with the conjugate units. -/
lemma shortExact_conjugate_of_eq (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV)
    (hηU : ηU = conjugateUnit adjU cU) (hηV : ηV = conjugateUnit adjV cV) (F : A)
    (hz' : biprod.lift (ηU.app F) (ηV.app F) ≫
      biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F)) = 0)
    (hepi : Epi (biprod.desc ((conjugateEquiv adjU adjP α).app F)
      (-((conjugateEquiv adjV adjP β).app F)))) :
    (ShortComplex.mk (biprod.lift (ηU.app F) (ηV.app F))
      (biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F))) hz').ShortExact := by
  subst hηU hηV
  exact shortExact_conjugate adjU adjV adjP cU cV α β hz hGV F hepi

/-! ### The surjectivity on the right, at an arbitrary object

This is the step the source takes with Stacks 01FW, and it is where the hypothesis `hepi`
above comes from.  It is carried out here with no site and no cohomology: in an abelian
category with enough injectives the obstruction to lifting is killed by *some* epimorphism, and
that is all surjectivity asks for.  See the implementation notes of this file. -/

omit [ΦU.Additive] [ΦV.Additive] in
/-- **Transposing a lift.**  A map `σ : G ⟶ Φ_P F` factors through the Mayer–Vietoris map
`Φ_U F ⊕ Φ_V F ⟶ Φ_P F` as soon as its adjoint transpose `Ψ_P G ⟶ F` extends along the
monomorphism `(α, -β)` of the extension-by-zero sequence at `G`.

Nothing is assumed beyond the adjunctions: this is `Hom(Ψ_Y G, F) ≅ Hom(G, Φ_Y F)` read through
`CategoryTheory.homEquiv_comp_conjugateEquiv`, which is what identifies the conjugate
comparisons with restriction along `α` and `β`. -/
lemma exists_lift_of_extension {F G : A} (σ : G ⟶ ΦP.obj F)
    (ψ : ΨU.obj G ⊞ ΨV.obj G ⟶ F)
    (hψ : biprod.lift (α.app G) (-(β.app G)) ≫ ψ = (adjP.homEquiv G F).symm σ) :
    ∃ τ : G ⟶ ΦU.obj F ⊞ ΦV.obj F,
      τ ≫ biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F)) = σ := by
  refine ⟨biprod.lift (adjU.homEquiv G F (biprod.inl ≫ ψ))
    (adjV.homEquiv G F (biprod.inr ≫ ψ)), ?_⟩
  have hsplit : α.app G ≫ biprod.inl ≫ ψ - β.app G ≫ biprod.inr ≫ ψ =
      biprod.lift (α.app G) (-(β.app G)) ≫ ψ := by
    rw [biprod.lift_eq, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
      Preadditive.neg_comp, Category.assoc, ← sub_eq_add_neg]
  rw [biprod.lift_desc, Preadditive.comp_neg,
    homEquiv_comp_conjugateEquiv adjU adjP α G F (biprod.inl ≫ ψ),
    homEquiv_comp_conjugateEquiv adjV adjP β G F (biprod.inr ≫ ψ),
    ← sub_eq_add_neg, ← homEquiv_sub adjP, hsplit, hψ, Equiv.apply_symm_apply]

include hz hGV in
omit [ΦU.Additive] [ΦV.Additive] in
/-- **Stacks 08GW part (1), the surjectivity on the right, at an arbitrary object.**  Granted
the extension-by-zero short exact sequence of Stacks 08GV part (1) at every object, the
Mayer–Vietoris map

`Φ_U F ⊕ Φ_V F ⟶ Φ_P F`

of conjugate direct-image comparisons is an epimorphism, for every `F`.  The only hypothesis on
the ambient abelian category is that it have enough injectives.

*The argument.*  An epimorphism is exactly a map through which some epimorphism factors, so it
is enough to lift one map onto `Φ_P F` — namely the identity, up to precomposition with an
epimorphism of our choosing.  Transposed across `Ψ_P ⊣ Φ_P`, the identity of `G = Φ_P F` is the
counit `s : Ψ_P G ⟶ F`, and lifting it means extending it along the monomorphism `(α, -β)` of
the sequence at `G` (`exists_lift_of_extension`).  Embed `F` in an injective object `I`.  Then
`s ≫ (F ⟶ I)` *does* extend, to some `t`; the extension of `s` itself fails only by the
composite `t ≫ (I ⟶ I/F)`, which kills `(α, -β)` and therefore descends along the epimorphism
`Ψ_U G ⊕ Ψ_V G ⟶ G` of the sequence to a single map `q : G ⟶ I/F` — the obstruction class, as a
map rather than as an element of `Ext¹(G, F) = H¹(F)`.  Pulling back along `I ⟶ I/F` makes it
disappear: on `G' = I ×_{I/F} G` the obstruction is `q` composed with a map that factors
through `I ⟶ I/F`, so correcting `t` by that factorization gives an extension over `G'`, and
the projection `G' ⟶ G` is an epimorphism because `I ⟶ I/F` is.

*Why this is not the source's Stacks 01FW, and why it needs no site.*  The source works with
sections over an object `W` of the site and so must kill a class in `H¹(W, F)`, which it can
only do after an étale covering; the covering is then absorbed because the conclusion is local
surjectivity.  Categorically the covering is unnecessary: `Ext¹(-, F)` is effaceable — every
class dies after precomposition with a suitable epimorphism — and epimorphy of a map is
precisely a statement that survives precomposition with an epimorphism.  The proof below is
that effacement, written out without naming `Ext`. -/
lemma epi_conjugate [EnoughInjectives A] (F : A) :
    Epi (biprod.desc ((conjugateEquiv adjU adjP α).app F)
      (-((conjugateEquiv adjV adjP β).app F))) := by
  -- the object whose identity is to be lifted, and the transpose of that identity
  set G : A := ΦP.obj F with hG
  set s : ΨP.obj G ⟶ F := (adjP.homEquiv G F).symm (𝟙 G) with hs
  have hmonoG : Mono (biprod.lift (α.app G) (-(β.app G))) := (hGV G).mono_f
  have hepiG : Epi (biprod.desc (cU.app G) (cV.app G)) := (hGV G).epi_g
  -- extend `s` after embedding `F` in an injective object
  set t : ΨU.obj G ⊞ ΨV.obj G ⟶ Injective.under F :=
    Injective.factorThru (s ≫ Injective.ι F) (biprod.lift (α.app G) (-(β.app G))) with htdef
  have ht : biprod.lift (α.app G) (-(β.app G)) ≫ t = s ≫ Injective.ι F :=
    Injective.comp_factorThru _ _
  -- the obstruction, as a map from `G` to the cokernel
  have hzq : biprod.lift (α.app G) (-(β.app G)) ≫
      (t ≫ cokernel.π (Injective.ι F)) = 0 := by
    rw [← Category.assoc, ht, Category.assoc, cokernel.condition, comp_zero]
  set q : G ⟶ cokernel (Injective.ι F) :=
    (hGV G).exact.desc (t ≫ cokernel.π (Injective.ι F)) hzq with hqdef
  have hq : biprod.desc (cU.app G) (cV.app G) ≫ q = t ≫ cokernel.π (Injective.ι F) :=
    (hGV G).exact.g_desc _ hzq
  -- kill the obstruction by pulling back along the epimorphism `cokernel.π`
  set G' : A := pullback (cokernel.π (Injective.ι F)) q with hG'
  set v : G' ⟶ G := pullback.snd (cokernel.π (Injective.ι F)) q with hv
  set r : G' ⟶ Injective.under F := pullback.fst (cokernel.π (Injective.ι F)) q with hr
  have hrv : r ≫ cokernel.π (Injective.ι F) = v ≫ q := pullback.condition
  have hepiv : Epi v := by rw [hv]; infer_instance
  -- the two sequences compared along `v`
  have hi : biprod.lift (α.app G') (-(β.app G')) ≫ biprod.map (ΨU.map v) (ΨV.map v) =
      ΨP.map v ≫ biprod.lift (α.app G) (-(β.app G)) := by
    refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [α.naturality, β.naturality]
  have hc : biprod.map (ΨU.map v) (ΨV.map v) ≫ biprod.desc (cU.app G) (cV.app G) =
      biprod.desc (cU.app G') (cV.app G') ≫ v := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      simp [cU.naturality, cV.naturality]
  -- correcting `t` by the pullback projection lands in `F`
  have hw : (biprod.map (ΨU.map v) (ΨV.map v) ≫ t -
      biprod.desc (cU.app G') (cV.app G') ≫ r) ≫ cokernel.π (Injective.ι F) = 0 := by
    have h1 : biprod.map (ΨU.map v) (ΨV.map v) ≫ t ≫ cokernel.π (Injective.ι F) =
        biprod.desc (cU.app G') (cV.app G') ≫ v ≫ q := by
      rw [← hq, ← Category.assoc, hc, Category.assoc]
    rw [Preadditive.sub_comp, Category.assoc, h1, Category.assoc, hrv, sub_self]
  set ψ : ΨU.obj G' ⊞ ΨV.obj G' ⟶ F :=
    Abelian.monoLift (Injective.ι F) _ hw with hψdef
  have hψ : ψ ≫ Injective.ι F = biprod.map (ΨU.map v) (ΨV.map v) ≫ t -
      biprod.desc (cU.app G') (cV.app G') ≫ r :=
    Abelian.monoLift_comp _ _ hw
  -- so `ψ` extends the transpose of `v`
  have hkey : biprod.lift (α.app G') (-(β.app G')) ≫ ψ =
      (adjP.homEquiv G' F).symm v := by
    have hzero' : biprod.lift (α.app G') (-(β.app G')) ≫
        (biprod.desc (cU.app G') (cV.app G') ≫ r) = 0 := by
      rw [← Category.assoc, hz G', zero_comp]
    have h2 : (biprod.lift (α.app G') (-(β.app G')) ≫ ψ) ≫ Injective.ι F =
        (ΨP.map v ≫ s) ≫ Injective.ι F := by
      rw [Category.assoc, hψ, Preadditive.comp_sub, hzero', sub_zero, ← Category.assoc, hi,
        Category.assoc, ht, Category.assoc]
    have h3 : biprod.lift (α.app G') (-(β.app G')) ≫ ψ = ΨP.map v ≫ s :=
      (cancel_mono (Injective.ι F)).mp h2
    rw [h3, hs, ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id]
  obtain ⟨τ, hτ⟩ := exists_lift_of_extension adjU adjV adjP α β v ψ hkey
  exact epi_of_epi_fac hτ

end Dualize

/-! ### From the direct-image short exact sequence to the distinguished triangle -/

section DerivedTriangle

variable {A : Type u} [Category.{v} A] [Abelian A]
  {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]

/-- A natural map `𝟭 ⟶ Φ` applied degreewise to a cochain complex. -/
def unitCochainMap {Φ : A ⥤ A} [Φ.PreservesZeroMorphisms] (η : 𝟭 A ⟶ Φ)
    (K : CochainComplex A ℤ) :
    K ⟶ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K where
  f n := η.app (K.X n)
  comm' i j _ := (η.naturality (K.d i j)).symm

/-- The degree `n` component of `unitCochainMap η K` is `η` at the `n`-th object of `K`. -/
@[simp]
lemma unitCochainMap_f {Φ : A ⥤ A} [Φ.PreservesZeroMorphisms] (η : 𝟭 A ⟶ Φ)
    (K : CochainComplex A ℤ) (n : ℤ) :
    (unitCochainMap η K).f n = η.app (K.X n) :=
  rfl

variable [HasDerivedCategory.{w} A]

/-- **The homological content of the passage from part (1) to part (2) of Stacks 08GW.**  Let
`Φ_U, Φ_V, Φ_P : A ⥤ A` be additive endofunctors of an abelian category and let
`η_U : 𝟭 ⟶ Φ_U`, `η_V : 𝟭 ⟶ Φ_V`, `a : Φ_U ⟶ Φ_P` and `b : Φ_V ⟶ Φ_P` be natural
transformations such that

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

is short exact for every object `M`, the maps being `(η_U, η_V)` and `a - b`.  Then for every
cochain complex `K` the degreewise transformations fit into a distinguished triangle

`K ⟶ Φ_U K ⊕ Φ_V K ⟶ Φ_P K ⟶ K[1]`

in the derived category.  *No exactness of the three functors is needed*, which is what makes
this the right statement for direct images: the triangle is the one attached to the short exact
sequence of cochain complexes that part (1) gives degreewise, and nothing identifies
`Φ_Y K` with a derived functor of `Φ_Y` applied to `K` — for that, `K` has to be K-injective. -/
theorem mem_distTriang_unitBiprod_of_natural_shortExact
    (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (a : ΦU ⟶ ΦP) (b : ΦV ⟶ ΦP)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (a.app M) (-(b.app M)) = 0)
    (hex : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (a.app M) (-(b.app M))) (hzero M)).ShortExact)
    (K : CochainComplex A ℤ) :
    ∃ δ, Triangle.mk
        (biprod.lift (DerivedCategory.Q.map (unitCochainMap ηU K))
          (DerivedCategory.Q.map (unitCochainMap ηV K)))
        (biprod.desc
          (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)).app K))
          (-(DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex b (ComplexShape.up ℤ)).app K))))
        δ ∈ distTriang (DerivedCategory A) := by
  let AU := (ΦU.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let AV := (ΦV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let fU := unitCochainMap ηU K
  let fV := unitCochainMap ηV K
  let gU := (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)).app K
  let gV := (NatTrans.mapHomologicalComplex b (ComplexShape.up ℤ)).app K
  let ev : ℤ → (CochainComplex A ℤ ⥤ A) :=
    fun n => HomologicalComplex.eval A (ComplexShape.up ℤ) n
  have e1 : ∀ n : ℤ, (ev n).map (biprod.lift fU fV) =
      biprod.lift (ηU.app (K.X n)) (ηV.app (K.X n)) ≫
        ((ev n).biprodIsoOfAdditive AU AV).inv := by
    intro n
    rw [Iso.eq_comp_inv, Functor.biprodIsoOfAdditive_hom_map_lift]
    rfl
  have e2 : ∀ n : ℤ, ((ev n).biprodIsoOfAdditive AU AV).inv ≫
      (ev n).map (biprod.desc gU (-gV)) =
      biprod.desc (a.app (K.X n)) (-(b.app (K.X n))) := by
    intro n
    rw [Functor.biprodIsoOfAdditive_inv_map_desc, (ev n).map_neg]
    rfl
  have hz' : biprod.lift fU fV ≫ biprod.desc gU (-gV) = 0 := by
    ext n
    change (ev n).map (biprod.lift fU fV ≫ biprod.desc gU (-gV)) = 0
    rw [(ev n).map_comp, e1 n, assoc, e2 n, hzero (K.X n)]
  have hS : (ShortComplex.mk _ _ hz').ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
    refine ShortComplex.shortExact_of_iso ?_ (hex (K.X n))
    refine ShortComplex.isoMk (Iso.refl _) ((ev n).biprodIsoOfAdditive AU AV).symm
      (Iso.refl _) ?_ ?_
    · simp only [Iso.refl_hom, id_comp, Iso.symm_hom]
      exact e1 n
    · simp only [Iso.refl_hom, comp_id, Iso.symm_hom]
      exact e2 n
  have comm1 : biprod.lift (DerivedCategory.Q.map fU) (DerivedCategory.Q.map fV) ≫
      (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm.hom =
      (Iso.refl (DerivedCategory.Q.obj K)).hom ≫
        DerivedCategory.Q.map (biprod.lift fU fV) := by
    rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Iso.comp_inv_eq,
      Functor.biprodIsoOfAdditive_hom_map_lift]
  have comm2 : biprod.desc (DerivedCategory.Q.map gU) (-(DerivedCategory.Q.map gV)) ≫
      (Iso.refl (DerivedCategory.Q.obj
        ((ΦP.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom =
      (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm.hom ≫
        DerivedCategory.Q.map (biprod.desc gU (-gV)) := by
    rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      Functor.biprodIsoOfAdditive_inv_map_desc, Functor.map_neg]
  have comm3 : DerivedCategory.triangleOfSESδ hS ≫
      (shiftFunctor (DerivedCategory A) (1 : ℤ)).map
        (Iso.refl (DerivedCategory.Q.obj K)).hom =
      (Iso.refl (DerivedCategory.Q.obj
        ((ΦP.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom ≫
        DerivedCategory.triangleOfSESδ hS := by
    simp
  exact ⟨DerivedCategory.triangleOfSESδ hS,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
      (Triangle.isoMk _ _ (Iso.refl _)
        (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm (Iso.refl _) comm1 comm2 comm3)⟩

end DerivedTriangle

/-! ### K-injective representatives at unrestricted universes

`CategoryTheory.exists_isKInjective_representative` and `CategoryTheory.rightDerivedObjIso` are
stated for a category whose objects lie one universe above its morphisms.  The `𝒪`-modules on
the small étale ringed site of an algebraic space are *not* of that shape — objects and
morphisms both land in `Type (u + 1)` — so the two statements are repeated here with
unrestricted universes.  Nothing of their proofs changes: both inputs,
`CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso`
`_isKInjective` (Stacks 070K) and the comparisons `DerivedCategory.quotientCompQhIso` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, are universe-polymorphic already. -/

section KInjective

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **Stacks 079P.**  Every object of the unbounded derived category is `DerivedCategory.Q` of
a K-injective complex, as soon as K-injective resolutions exist. -/
lemma exists_isKInjective_representative_of_universe
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (E : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  obtain ⟨I, i, hI, hi⟩ := hres (DerivedCategory.Q.objPreimage E)
  have := hi
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- **Stacks 070K.**  A right derived functor of `F` is computed on a K-injective complex by
`F` itself. -/
def rightDerivedObjIsoOfKInjective {C : Type u'} [Category.{v'} C] [Abelian C]
    [HasDerivedCategory.{w'} C]
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (F : A ⥤ C) (hF : F.Additive)
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      RF.obj (DerivedCategory.Q.obj I) := by
  have := hF
  have := hRF
  have := hI
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
    DerivedCategory.Qh RF α I inferInstance
  exact (DerivedCategory.quotientCompQhIso C).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm.app I) ≪≫
    asIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ≪≫
    RF.mapIso ((DerivedCategory.quotientCompQhIso A).app I)

end KInjective

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `F ↦ j_{U,*}(F|_U)` for the open immersion `j_U` of an elementary distinguished square:
restriction of modules to the open subspace followed by the direct image back. -/
abbrev edsRestrictPushOpen :
    Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2 :=
  etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) ⋙
    modulePushforward B S hS (edsOpenHom B S hS hsq)

/-- `F ↦ j_{V,*}(F|_V)` for the étale morphism `j_V` of an elementary distinguished square. -/
abbrev edsRestrictPushEtale :
    Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2 :=
  etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) ⋙
    modulePushforward B S hS (edsEtaleHom B S hS hsq)

/-- `F ↦ j_{U ×_X V,*}(F|_{U ×_X V})` for the intersection of an elementary distinguished
square. -/
abbrev edsRestrictPushInter :
    Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2 :=
  etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq) ⋙
    modulePushforward B S hS (edsInterHom B S hS hsq)

/-- The adjunction `(-)|_U ⊣ j_{U,*}` of Stacks 03LU at the open immersion of an elementary
distinguished square.  Its unit is the canonical map `F ⟶ j_{U,*}(F|_U)`. -/
abbrev edsAdjOpen :
    etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) ⊣
      modulePushforward B S hS (edsOpenHom B S hS hsq) :=
  etaleModulePullbackAdjunction B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)

/-- The adjunction `(-)|_V ⊣ j_{V,*}` of Stacks 03LU at the étale morphism of an elementary
distinguished square. -/
abbrev edsAdjEtale :
    etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) ⊣
      modulePushforward B S hS (edsEtaleHom B S hS hsq) :=
  etaleModulePullbackAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)

/-- The adjunction `(-)|_{U ×_X V} ⊣ j_{U ×_X V,*}` of Stacks 03LU at the intersection of an
elementary distinguished square. -/
abbrev edsAdjInter :
    etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) ⊣
      modulePushforward B S hS (edsInterHom B S hS hsq) :=
  etaleModulePullbackAdjunction B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)

section Clause

variable
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  (a : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
      etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU)
  (b : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
      etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV)
  (hzero : ∀ F, biprod.lift (a.app F) (-(b.app F)) ≫
    biprod.desc (adjU.counit.app F) (adjV.counit.app F) = 0)

/-! The two comparison maps `j_{U,*}F|_U ⟶ j_{U ×_X V,*}F|_{U ×_X V}` and
`j_{V,*}F|_V ⟶ j_{U ×_X V,*}F|_{U ×_X V}` of Stacks 08GW part (1) are *not* arbitrary
transformations compatible with the units: they are the conjugates, under the two adjunctions
`j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the extension-by-zero comparisons
`j_{U ×_X V!}F|_{U ×_X V} ⟶ j_{U!}F|_U` and `j_{U ×_X V!}F|_{U ×_X V} ⟶ j_{V!}F|_V` that
Stacks 08GV part (1) provides.  They are written out below rather than abbreviated, because an
abbreviation for them makes the unification against the abstract lemmas diverge. -/

include hzero in
/-- The Mayer–Vietoris complex of direct images of Stacks 08GW part (1) is a complex: the
canonical unit `F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V` followed by the difference of the two
conjugate comparisons into `j_{U ×_X V,*}F|_{U ×_X V}` vanishes.  Nothing is assumed beyond
`hzero`, the corresponding vanishing in Stacks 08GV part (1). -/
theorem zero_edsRestrictPushMayerVietoris (F : Modules.{u, u} B S hS W.1 W.2) :
    biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
        ((edsAdjEtale B S hS hsq).unit.app F) ≫
      biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
            ((edsAdjInter B S hS hsq).comp adjP) a).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
            ((edsAdjInter B S hS hsq).comp adjP) b).app F)) = 0 :=
  zero_conjugate_of_eq ((edsAdjOpen B S hS hsq).comp adjU)
    ((edsAdjEtale B S hS hsq).comp adjV) ((edsAdjInter B S hS hsq).comp adjP)
    adjU.counit adjV.counit a b hzero _ _
    (conjugateUnit_comp_counit (edsAdjOpen B S hS hsq) adjU).symm
    (conjugateUnit_comp_counit (edsAdjEtale B S hS hsq) adjV).symm F

variable (hMV : ∀ F, (ShortComplex.mk (biprod.lift (a.app F) (-(b.app F)))
  (biprod.desc (adjU.counit.app F) (adjV.counit.app F)) (hzero F)).ShortExact)

include hzero hMV in
/-- **The surjectivity on the right of Stacks 08GW part (1)**, granted part (1) of Stacks 08GV
and nothing else.  The map

`j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{U ×_X V,*}F|_{U ×_X V}`

whose two components are the conjugates of the extension-by-zero comparisons is an epimorphism,
for *every* sheaf of `𝒪_X`-modules `F` — no injectivity of `F`, no boundedness, no further
geometry.

This is `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` at the three adjunctions
`j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)` of the square.  The only thing the modules on an algebraic
space supply beyond `hMV` is enough injectives, which they have because they are Grothendieck
abelian (`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`).  In particular the
obstruction class in `Ext¹_{𝒪_X}(𝒪_X, F) = H¹(X, F)` that the source kills étale locally with
Stacks 01FW is killed here by precomposition with a single epimorphism, which is all that
epimorphy of a map requires. -/
theorem epi_edsRestrictPushMayerVietoris (F : Modules.{u, u} B S hS W.1 W.2) :
    Epi (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
          ((edsAdjInter B S hS hsq).comp adjP) a).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
          ((edsAdjInter B S hS hsq).comp adjP) b).app F))) :=
  have := isGrothendieckAbelian_modules B S hS W.1 W.2
  epi_conjugate ((edsAdjOpen B S hS hsq).comp adjU) ((edsAdjEtale B S hS hsq).comp adjV)
    ((edsAdjInter B S hS hsq).comp adjP) adjU.counit adjV.counit a b hzero hMV F

include hzero hMV in
/-- **Stacks 08GW part (1)**, granted part (1) of Stacks 08GV and the surjectivity on the
right.  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces
over a scheme `S`, let `P = U ×_X V`, write `(-)|_Y` for restriction of modules along
`j_Y : Y ⟶ X`, let `j_{Y,*}` be the direct image of Stacks 03LU and let `j_{Y!}` be a left
adjoint of restriction, extension by zero.  Then for every sheaf of `𝒪_X`-modules `F` the
sequence

`0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{U ×_X V,*}F|_{U ×_X V} ⟶ 0`

is short exact.  Its first map is the pair of canonical units `F ⟶ j_{Y,*}F|_Y` of the
adjunctions `(-)|_Y ⊣ j_{Y,*}`, and its second is the difference of the two conjugates, under
the adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the two extension-by-zero comparisons
`j_{U ×_X V!}F|_{U ×_X V} ⟶ j_{U!}F|_U` and `j_{U ×_X V!}F|_{U ×_X V} ⟶ j_{V!}F|_V` of Stacks
08GV part (1).

What is proved here is that the sequence is a complex and that `F` is the *kernel* of its
second map, and both are proved from `hMV`, which is part (1) of Stacks 08GV verbatim.  That is
the source's own argument: apply `Hom(-, F)` to the sequence of Stacks 08GV part (1) and read
the three resulting groups through the adjunctions, using
`Hom(j_{Y!}G|_Y, F) ≅ Hom(G, j_{Y,*}F|_Y)`.

Stacks 08GW is *not* registered here: both of this statement's hypotheses are discharged, and
the tag sits on the resulting unqualified
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisComparison`.  `hMV` is part (1)
of Stacks 08GV, proved as `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, and
`hepi` follows from it by `AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietoris`.  This
form is kept because it is the one that applies to an arbitrary choice of the two comparisons
out of the intersection. -/
theorem shortExact_edsRestrictPushMayerVietoris
    (hepi : ∀ F, Epi (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
          ((edsAdjInter B S hS hsq).comp adjP) a).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
          ((edsAdjInter B S hS hsq).comp adjP) b).app F)))) :
    ∀ F : Modules.{u, u} B S hS W.1 W.2,
      (ShortComplex.mk
        (biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
          ((edsAdjEtale B S hS hsq).unit.app F))
        (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
              ((edsAdjInter B S hS hsq).comp adjP) a).app F)
          (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
              ((edsAdjInter B S hS hsq).comp adjP) b).app F)))
        (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP a b hzero F)).ShortExact :=
  fun F =>
    shortExact_conjugate_of_eq ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjEtale B S hS hsq).comp adjV) ((edsAdjInter B S hS hsq).comp adjP)
      adjU.counit adjV.counit a b hzero hMV _ _
      (conjugateUnit_comp_counit (edsAdjOpen B S hS hsq) adjU).symm
      (conjugateUnit_comp_counit (edsAdjEtale B S hS hsq) adjV).symm F _ (hepi F)

/-- **The surjectivity on the right of Stacks 08GW part (1), at the comparisons of the square,
with nothing granted.**  Part (1) of Stacks 08GV is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, so the hypothesis `hMV` of
`AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietoris` is discharged and

`j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{U ×_X V,*}F|_{U ×_X V}`

is an epimorphism for every sheaf of `𝒪_X`-modules `F`.  This is the hypothesis `hepi`
that the two theorems of this file carrying Stacks 08GW would otherwise need. -/
theorem epi_edsRestrictPushMayerVietorisComparison (F : Modules.{u, u} B S hS W.1 W.2) :
    Epi (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
          ((edsAdjInter B S hS hsq).comp adjP)
          (edsShriekOpenComparison B S hS hsq adjU adjP)).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
          ((edsAdjInter B S hS hsq).comp adjP)
          (edsShriekEtaleComparison B S hS hsq adjV adjP)).app F))) :=
  epi_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) F

/-- **Stacks 08GW part (1)**, with nothing granted.  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V`, write `(-)|_Y`
for restriction of modules along `j_Y : Y ⟶ X`, let `j_{Y,*}` be the direct image of Stacks
03LU and let `j_{Y!}` be a left adjoint of restriction, extension by zero.  Then for *every*
sheaf of `𝒪_X`-modules `F` the sequence

`0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{U ×_X V,*}F|_{U ×_X V} ⟶ 0`

is short exact.  Its first map is the pair of canonical units `F ⟶ j_{Y,*}F|_Y` of the
adjunctions `(-)|_Y ⊣ j_{Y,*}`, and its second is the difference of the conjugates, under the
adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the two extension-by-zero comparisons
`AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` attached to the two factorizations of
`j_{U ×_X V}`.

Every part of this is proved.  The complex condition is
`AlgebraicGeometry.Space.zero_edsRestrictPushMayerVietoris`; the exactness at the first two
spots is read off part (1) of Stacks 08GV through the adjunctions, and that is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`; and the surjectivity on the right
is `AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietorisComparison`.  Extension by zero is
the only thing still entering as data, as it does in Stacks 08GV itself: the three functors
`j_{Y!}` come with adjunctions exhibiting them as left adjoints of restriction, which pins them
up to unique compatible isomorphism.

Stacks 08GW is *not* registered here, because of that one remaining choice: the tag sits on
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisLowerShriek`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisPushforwardTag.lean`), which is this
statement at the extension by zero the library constructs and so quantifies over nothing at
all.  This form is kept because it is the one that applies to any other model of `j_{Y!}`. -/
theorem shortExact_edsRestrictPushMayerVietorisComparison :
    ∀ F : Modules.{u, u} B S hS W.1 W.2,
      (ShortComplex.mk
        (biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
          ((edsAdjEtale B S hS hsq).unit.app F))
        (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
              ((edsAdjInter B S hS hsq).comp adjP)
              (edsShriekOpenComparison B S hS hsq adjU adjP)).app F)
          (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
              ((edsAdjInter B S hS hsq).comp adjP)
              (edsShriekEtaleComparison B S hS hsq adjV adjP)).app F)))
        (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
          (edsShriekOpenComparison B S hS hsq adjU adjP)
          (edsShriekEtaleComparison B S hS hsq adjV adjP)
          (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) F)).ShortExact :=
  shortExact_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (epi_edsRestrictPushMayerVietorisComparison B S hS hsq adjU adjV adjP)

end Clause

section Derived

variable [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]

/-- **The right derived functor of an additive endofunctor of the `𝒪_X`-modules exists**, with
no further hypothesis: `Mod(𝒪_X)` is Grothendieck abelian, so Stacks 079P supplies K-injective
resolutions, and Stacks 070K turns those into a pointwise right derived functor.

Applied to `j_{Y,*}((-)|_Y)` this exhibits inhabitants for the hypotheses `R_Y`, `α_Y` and
`hR_Y` of `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris`:
take `R_Y` to be `CategoryTheory.Functor.totalRightDerived` and `α_Y` its canonical unit.  So
that statement is not vacuous. -/
theorem hasRightDerivedFunctor_mapHomotopyCategory_modules
    (Φ : Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS W.1 W.2) [Φ.Additive] :
    (Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **Stacks 08GW part (2)**, granted part (1).  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V` and write
`Φ_Y = j_{Y,*}((-)|_Y)` for the three composites of restriction with the direct image.  Let
`R_U`, `R_V` and `R_P` be right derived functors of the three `Φ_Y`, with their canonical
comparisons `α_Y`; `R_Y` is the source's `Rj_{Y,*}((-)|_Y)`.  Suppose part (1) holds: the
sequence

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

is short exact for every sheaf of `𝒪_X`-modules `M`.  Then every object `E` of the unbounded
derived category `D(𝒪_X)` sits in a distinguished triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{U ×_X V,*}E|_{U ×_X V} ⟶ E[1]`.

This is the source's own proof: `E` is represented by a K-injective complex `I` (Stacks 079P,
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`), on which each `R_Y` is
computed by `Φ_Y` itself (Stacks 070K,
`CategoryTheory.PushforwardMayerVietoris.rightDerivedObjIsoOfKInjective`), and the triangle is
the one attached to the short exact sequence of cochain complexes that part (1) gives
degreewise.

As in Stacks 08GV part (2), the maps are existentially quantified — the source likewise only
asserts that a triangle with these three terms exists.  The explicit maps the proof produces
are the derived unit `E ⟶ Rj_{Y,*}E|_Y` and the derived comparison, both read off `I`; they
are the ones constructed in the proof term.

Stacks 08GW is *not* registered here: `hMV` is part (1) of this same tag, and it is proved, so
the tag sits on the resulting unqualified
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisComparison`.
This form is kept because it applies to an arbitrary natural short exact sequence with these
three functors, not only to the one the square produces. -/
theorem exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris
    (RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αU : (edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : E ⟶ RU.obj E) (fV : E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) := by
  have hres := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe hres E
  obtain ⟨δ, hδ⟩ := mem_distTriang_unitBiprod_of_natural_shortExact ηU ηV dU dV hzero hMV I
  have hξU := rightDerivedObjIsoOfKInjective hres (edsRestrictPushOpen B S hS hsq)
    inferInstance RU αU hRU I hI
  have hξV := rightDerivedObjIsoOfKInjective hres (edsRestrictPushEtale B S hS hsq)
    inferInstance RV αV hRV I hI
  have hξP := rightDerivedObjIsoOfKInjective hres (edsRestrictPushInter B S hS hsq)
    inferInstance RP αP hRP I hI
  refine ⟨e.inv ≫ DerivedCategory.Q.map (unitCochainMap ηU I) ≫
      (hξU ≪≫ RU.mapIso e).hom,
    e.inv ≫ DerivedCategory.Q.map (unitCochainMap ηV I) ≫ (hξV ≪≫ RV.mapIso e).hom,
    (hξU ≪≫ RU.mapIso e).inv ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex dU (ComplexShape.up ℤ)).app I) ≫
      (hξP ≪≫ RP.mapIso e).hom,
    (hξV ≪≫ RV.mapIso e).inv ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex dV (ComplexShape.up ℤ)).app I) ≫
      (hξP ≪≫ RP.mapIso e).hom,
    (hξP ≪≫ RP.mapIso e).inv ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom,
    isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ e.symm
      (biprod.mapIso (hξU ≪≫ RU.mapIso e).symm (hξV ≪≫ RV.mapIso e).symm)
      (hξP ≪≫ RP.mapIso e).symm ?_ ?_ ?_)⟩
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  · simp

end Derived

section DerivedComparison

variable [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

include adjU adjV adjP in
/-- **Stacks 08GW part (2)**, with nothing granted.  For right derived functors `R_U`, `R_V`,
`R_P` of the three functors `Φ_Y = j_{Y,*}((-)|_Y)` of an elementary distinguished square, with
their comparisons `α_Y`, every object `E` of the unbounded derived category `D(𝒪_X)` sits in a
distinguished triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{U ×_X V,*}E|_{U ×_X V} ⟶ E[1]`.

This is `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris` with
its hypothesis `hMV` — part (1) of this same tag — *discharged*: the four transformations are no
longer arbitrary but the two canonical units `F ⟶ j_{Y,*}F|_Y` and the two conjugates of the
comparisons of the square, and for those part (1) is the unqualified
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisComparison`.  Extension by zero
is the only thing entering as data, exactly as in part (1); it does not appear in the
conclusion, but part (1) is read off it and so the three adjunctions are still taken as
arguments.

Stacks 08GW is *not* registered here.  Two things are still quantified over: the
extension-by-zero data, and the three right derived functors with their comparisons — and the
five maps of the triangle are existential, so this statement is weaker than the tag, which
asserts the triangle whose maps are built from the restriction and extension-by-zero
adjunctions.  The tag sits on
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisPushforwardTag.lean`), which takes
the library's extension by zero and the chosen total right derived functors and states the
triangle with the canonical maps, only the connecting map remaining existential.  This form is
kept because it applies to any other model of `Rj_{Y,*}((-)|_Y)`. -/
theorem exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisComparison
    (RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αU : (edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : E ⟶ RU.obj E) (fV : E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :=
  exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris B S hS hsq RU RV RP αU αV αP
    hRU hRV hRP (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
    (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
      (edsShriekOpenComparison B S hS hsq adjU adjP)
      (edsShriekEtaleComparison B S hS hsq adjV adjP)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
    (shortExact_edsRestrictPushMayerVietorisComparison B S hS hsq adjU adjV adjP) E

end DerivedComparison

end Square

end AlgebraicGeometry.Space

end
