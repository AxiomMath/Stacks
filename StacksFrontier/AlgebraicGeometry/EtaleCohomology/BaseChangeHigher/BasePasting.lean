module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.AbstractPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.EtalePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.DerivedTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.CompositeExtension

/-!
# Pasting the derived base change comparison along the base

Let `g : T ⟶ S` be a morphism of schemes and extend the base twice, first along `f' : X' ⟶ S`
and then along `f'' : X'' ⟶ X'`.  Each extension carries a commutative square of schemes and
hence, on abelian sheaves of the small étale sites, a derived base change comparison
`R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹`; the comparison attached to the composite extension `f'' ≫ f'` ought
to be the composite of the two, read through the identification of `R(f'' ≫ f')⁻¹` with
`R(f')⁻¹ ⋙ R(f'')⁻¹`.  This is the base-functoriality that [Stacks, Tag 0E47] provides for the
base change map of ringed topoi and that
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app` provides for the unbounded
derived étale base change map, but not for the bounded below comparison
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` from which the base change map on higher
direct images of [Stacks, Tag 0F02] is obtained.

The bounded below comparison of a square is the descent of its underived comparison along the
derived-functor unit of `Rg_*`, so the pasting statement is an identity between two
transformations out of `Rg_* ⋙ R(f'' ≫ f')⁻¹`, and both are determined by their composites with
that unit.  `Stacks.Cohomology.BaseChange.derived_paste` is that identity, proved for an
arbitrary pair of commutative squares of additive functors whose four horizontal functors are
exact.  Inverse image of abelian sheaves on a small étale site is exact, so the étale situation
is an instance of it.  Two further results turn that instance into the pasting law for
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` at the composite extension `f'' ≫ f'`:
the pasting law for the *underived* mate `smallEtaleBaseChangeAb`, and the transport of
`Stacks.Cohomology.BaseChange.derived` along isomorphisms of its two exact horizontal functors.
Both are proved below.

## Main definitions

* `Stacks.Cohomology.BaseChange.compUnit` — the unit exhibiting `RF ⋙ RG` as a right derived
  functor of degreewise `F` followed by `RG`.
* `Stacks.Cohomology.BaseChange.exactUnitIso` — the derived-functor unit of an exact functor,
  as an isomorphism.
* `Stacks.Cohomology.BaseChange.iteratedUnit` — the iterated derived-functor unit
  `H(G(K)) ⟶ RH(RG(K))` of two composable additive functors.
* `Stacks.Cohomology.BaseChange.exactDerivedCompIso` — the composition isomorphism
  `R(H ∘ G) ≅ RG ⋙ RH` for exact `G` and `H`.
* `Stacks.Cohomology.BaseChange.pasteTrans` — the horizontal paste of two commutative squares
  of additive functors.
* `Stacks.Cohomology.BaseChange.chaseAux` — the shape of the pasting chase, as a diagram in an
  arbitrary category.
* `Stacks.EtaleCohomology.smallEtalePullbackAbTowerCompIso` and
  `Stacks.EtaleCohomology.smallEtaleDerivedPullbackComp` — the composition isomorphisms
  `(f')⁻¹ ∘ (f'')⁻¹ ≅ (f'' ∘ f')⁻¹` and `R(f'' ∘ f')⁻¹ ≅ R(f')⁻¹ ⋙ R(f'')⁻¹` for inverse image
  of abelian sheaves on the small étale sites.
* `Stacks.Cohomology.BaseChange.pentagonChase` and
  `Stacks.Cohomology.BaseChange.transportAux` — the shapes of the two further chases, as
  diagrams in an arbitrary category.
* `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso'` and
  `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'` — the composition isomorphisms
  `f_* ⋙ g_* ≅ (fg)_*` and `g⁻¹ ⋙ f⁻¹ ≅ (fg)⁻¹` with the composite `fg` carried as a named
  morphism together with an equation naming it.

## Main results

* `Stacks.Cohomology.BaseChange.derived_fac_app` and
  `Stacks.Cohomology.BaseChange.onHomotopy_app` — the derived comparison of a square, read at a
  bounded below complex: it is the comparison `e` undone, the degreewise comparison, and the
  derived-functor units of `RF'` and of `RG'`.
* `Stacks.Cohomology.BaseChange.unit_comp_exactDerivedCompIso_hom`,
  `Stacks.Cohomology.BaseChange.exactDerivedCompIso_hom_app_qh` and
  `Stacks.Cohomology.BaseChange.unit_eq_comp_exactDerivedCompIso_inv` — the derived-functor unit
  of `R(H ∘ G)` and the composition isomorphism determine one another.
* `Stacks.Cohomology.BaseChange.mapPlus_pasteTrans_app` — the degreewise comparison of the
  pasted rectangle is the degreewise comparison of the first square carried by `H` followed by
  that of the second.
* `Stacks.Cohomology.BaseChange.firstStep` and `Stacks.Cohomology.BaseChange.secondStep` — the
  two halves of the chase: in each the derived-functor unit of the exact horizontal functor
  cancels against the comparison through which the square's derived comparison is descended.
* `Stacks.Cohomology.BaseChange.derived_paste` — **the pasting law**: the comparison of the
  pasted rectangle is the comparison of the first square carried by `RH`, followed by the
  comparison of the second square, read through the two composition isomorphisms.
* `Stacks.Cohomology.BaseChange.isIso_derived_paste_app` — two out of three: if the two squares'
  comparisons are invertible at the relevant objects, so is the pasted one.
* `Stacks.Cohomology.BaseChange.homologyFunctor_map_derived_paste_app` — the degree-`n`
  cohomology of the pasting law, which is the shape in which it descends to the base change map
  on higher direct images.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_fac_app` — the bounded below derived
  étale base change comparison of a commutative square of schemes, read at a bounded below
  complex of abelian sheaves.
* `Stacks.Cohomology.BaseChange.derived_transport` — **the transport law**: the comparison
  descended from a comparison read through isomorphisms of the two exact horizontal functors is
  the comparison of the transported square, conjugated by the right derived functors of those
  isomorphisms.
* `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_assoc` — the associativity pentagon of
  the étale inverse image comparison.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_mateEquiv` — the underived étale base
  change comparison of a square is the mate, under the adjunctions of its *horizontal*
  morphisms, of the comparison of the two composite inverse images.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_comp` — **the underived pasting law** for a
  tower of two commutative squares.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_comp` — **base functoriality of the
  bounded below derived étale base change comparison**, for the composite extension `f'' ≫ f'`.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_comp_app` and
  `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_derived_comp` — two out of
  three for the composite extension, and its degree-`q` consequence for the base change map on
  higher direct images of [Stacks, Tag 0F02].

## Implementation notes

*Why the chase is in components.*  The bounded below comparison is a descent along a
derived-functor unit rather than a mate of two adjunctions, so the pasting law is not an
instance of `CategoryTheory.mateEquiv_hcomp` and the ringed-topoi argument of
`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_horizontal` does not apply.
What determines the descent is its composite with the unit at each bounded below complex, which
is `derived_fac_app`, so the comparison of the two sides is a computation in components.

*Why the chase is factored through an abstract diagram.*  In components the composites run
through objects with two spellings of the same thing: the target of `Rh_*` applied to the first
square's comparison is `Rh_*((Re⁻¹ ∘ Rh'_*)(K))`, while the source of the second square's
comparison is `(Rh'_* ∘ Rh_*)(Re⁻¹(K))`.  These are definitionally equal but not syntactically
so, and `CategoryTheory.Functor.comp_obj` is not applied to the object arguments of
`CategoryTheory.CategoryStruct.comp`, so neither `CategoryTheory.Category.assoc` nor the
reassociated form of a rewrite rule matches across such a junction.  `chaseAux` therefore states
the shape of the whole computation for morphisms of an arbitrary category, where every object is
a variable and reassociation is unobstructed, and `pasteTail` instantiates it: an instantiation
is a function application, checked up to definitional equality, so the two spellings are
identified there once and for all.  The same device — a hypothesis of the abstract lemma, or an
`Eq.trans` of two hand-written equations — is what every step of `derived_paste_app` uses in
place of a rewrite.

*How the étale instance is completed.*  `derived_paste` applies verbatim to the four inverse
images `(f')⁻¹`, `e⁻¹`, `(f'')⁻¹`, `(e'')⁻¹`, so it gives the pasting law for the comparison
descended from `pasteTrans (smallEtaleBaseChangeAb …) (smallEtaleBaseChangeAb …)` with
`(f')⁻¹ ⋙ (f'')⁻¹` as its horizontal functor.  Identifying that with
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` for the composite extension `f'' ≫ f'`
is `smallEtaleDerivedBaseChangeAb_comp`, and uses two things.  First, the pasting law for the
*underived* mate: `smallEtaleBaseChangeAb` is a mate of the comparison of the two composite
*direct* images, and `smallEtaleBaseChangeAb_eq_mateEquiv` re-reads it as the mate, across the
adjunctions of the *horizontal* morphisms, of the comparison of the two composite *inverse*
images — the form in which `CategoryTheory.mateEquiv_vcomp` applies, because the horizontal
morphisms of a tower do not compose.  What is then left is the associativity pentagon of the
inverse image comparison, used for three chains; that is `pentagonChase`.  Second, the two
horizontal functors of the pasted square are `(f')⁻¹ ⋙ (f'')⁻¹` and `e⁻¹ ⋙ (e'')⁻¹` rather
than `(f'' ≫ f')⁻¹` and `(e'' ≫ e)⁻¹`, and `derived_transport` moves the descent across those
two isomorphisms.

*Named composites.*  Every composite of two morphisms of schemes that enters the underived
pasting law is carried as a separate morphism together with an equation naming it, as in
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso'`.  Without this each of the three
pentagon instances would have to be transported along `CategoryTheory.Category.assoc`, and the
transports reconciled with the `eqToIso` that `smallEtaleBaseChangeAb` itself carries; with it
that `eqToIso` is absorbed once, in `smallEtaleBaseChangeAb_eq_mateEquiv`.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/
