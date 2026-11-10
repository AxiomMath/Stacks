module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftFlipApp
public import StacksFrontier.Homology.TotalComplexTransportShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoInv
import StacksCore.Tactic.StacksAttribute

/-!
# Assembling the second comparison of Tag 079U, and with it the whole of its shift compatibility

`Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShift₂` is the shift compatibility of
`rightComparison`, curried, in each variable.  `rightComparison f` is

`Functor.whiskerRight ((derivedPullbackNatTrans f).prod (derivedPullbackNatTrans f)) (- ⊗^𝐋 -) ≫
  Functor.whiskerLeft (f^* × f^*) (derivedToTensorNatTrans X) ≫
  Functor.whiskerRight (pullbackTensorComplexNatIso f).inv Q`

and this file reads each of its two one-variable components as a chain of **four** whiskered
factors between the pinned bifunctors, proves each chain shift-compatible from the three legs, and
then discharges the one obligation the two comparisons share by
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorCommShift₂`.  With that
`RightComparisonCommShift₂ f` holds with no hypothesis, and [Stacks, Tag 079U] owes nothing
further.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexBifunctorIso`: **the comparison of
  total tensor complexes of [Stacks, Tag 01CD], in bifunctor form**, and
  `pullbackTensorComplexBifunctorIso_inv_app_app`: its components are those of
  `pullbackTensorComplexNatIso`.
* `Stacks.Cohomology.DerivedPullbackTensor.rightComparisonPinnedApp` and
  `rightComparisonPinnedFlipApp`: **the two one-variable components of `rightComparison f` as
  four-factor chains between the pinned bifunctors**, with `rightComparisonPinnedApp_commShift`
  and `rightComparisonPinnedFlipApp_commShift` their shift compatibility.
* `rightComparisonPinnedApp_app` / `rightComparisonPinnedFlipApp_app` and
  `rightComparisonPinnedApp_eq_curryApp` / `rightComparisonPinnedFlipApp_eq_curryFlipApp`:
  **each chain has the components of `rightComparison f`, and so is the corresponding component
  of `Functor.curry.map (rightComparison f)`** conjugated by the two pinning isomorphisms.  The
  two steps are separate declarations because taken together the kernel cannot re-check them; see
  the note on `rightComparisonPinnedApp_eq_curryApp`.
* `Stacks.Cohomology.DerivedPullbackTensor.rightComparisonCommShiftApp` and
  `rightComparisonCommShiftFlipApp`: **the two halves of `RightComparisonCommShift₂`, with no
  hypothesis**, which is what `PullbackTensorCommShiftComparisons.lean` states and leaves open.
* `Stacks.Cohomology.DerivedPullbackTensor.rightComparisonCommShift₂`: **the second comparison of
  [Stacks, Tag 079U] is compatible with the shifts in both variables, unconditionally.**

## Implementation notes

**Why the chain has four factors and not three.**  The first factor of `rightComparison f`
whiskers the derived pullback into *both* tensor variables at once, and no closure property of
`CategoryTheory.NatTrans.CommShift` covers that.  It does not have to: the component of
`CategoryTheory.Functor.uncurry` at a morphism of a product is *by definition* the composite of
its two one-sided parts, so in each one-variable component that factor already appears as two —
a whiskering of `(- ⊗^𝐋 -)`'s action on the fixed variable, which is the `commShift_map` field of
`CategoryTheory.Functor.CommShift₂`, and a whiskering of the first leg
`derivedPullbackNatTrans_commShift`.  The two occur in opposite orders in the two variables, which
is why there are two chain lemmas, `CategoryTheory.NatTrans.commShift_assocChain₄` and
`commShift_assocChain₄'`, differing only in that order.

**Why the third leg needs the bifunctor form.**  The chain's last factor is a transformation of
one-variable functors, so it needs the comparison of total complexes read one variable at a time;
`pullbackTensorComplexNatIso` is a transformation on a product category, and
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂` — the third leg — is stated for
the curried form.  `pullbackTensorComplexBifunctorIso` is that curried form at this data, and
`pullbackTensorComplexBifunctorIso_inv_app_app` says the two packagings have the same components.
Both sides of that are read off by name, by
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_inv_app_app` where every category is a
variable: asked for as one `rfl` on the whole transformation at this instantiation it is a kernel
timeout.

**Why the chains are stated at the `curried…` spelling and conjugated afterwards.**  As in
`PullbackTensorCommShiftAssembly.lean`: the three junctions of the chain carry the commutation data
that `CategoryTheory.Functor.CommShift₂.precomp₁`, `precomp₂` and `postcompInt` put on the pinned
bifunctors, and those are what `curriedComplexesTensorOfPullbackComplexes_commShift₂Int` and
`curriedComplexesTotalOfPullbackComplexes_commShift₂Int` of
`PullbackTensorCommShiftComplexBifunctors.lean` supply.  The two `Prop`s are stated at the
`CategoryTheory.Functor.curry.obj` spelling instead, whose data are transported along the pinning
isomorphisms; `CategoryTheory.Functor.CommShift.ofIso_compatibility` crosses between the two for
free, once the bookkeeping identity saying that the chain *is* the component is available.

**Why each bookkeeping identity is two declarations.**  That a chain is the component
of the curried comparison is one equation, and written as one `exact` the *elaborator* accepts it
and the kernel then reports `(kernel) deterministic timeout` re-checking it.  The mechanism is not
a mismatch of shapes — the application elaborates, so the shape is right — but the asymmetry
between the two: the elaborator is entitled to this file's `attribute [local implicit_reducible]`
lines and the kernel is not, so the kernel redoes the whole identification with
`Stacks.SheafOfModules.Tensor.sheafTensor`, `structureSheafRing` and
`StacksDraft.KFlat.modulePullback` fully unfolded.  Splitting into `rightComparisonPinnedApp_app`
— the chain's components against `rightComparison`'s, where both sides name the same opaque
constants in the same positions and nothing has to be unfolded — and
`rightComparisonPinnedApp_eq_curryApp` — the two pinning isomorphisms alone, via `id_wrap` — gives
the kernel two obligations it can discharge in place of one it cannot.  The cure is to make each
obligation smaller, never to relax a limit: no budget would have helped, since the cost is the
unfolding and not the search.

**Why `CategoryTheory.NatTrans.commShift_assocChain₄` takes `ν` and `θ` apart rather than their
composite.**  Taking the composite of the first two whiskerings as
one abstract `head` would leave the consumer to supply its compatibility — and at a concrete
instantiation the consumer cannot.  The whiskerings need `CategoryTheory.Functor.CommShift` data
on `(Q ⋙ Lf^*) ⋙ h₁` and on `(Q ⋙ Lf^*) ⋙ h₂`, and here those functors have *competing* routes
to such data: the development's own one-variable instances for the derived tensor product
(`commShift_left`, `commShift_right`) and `CategoryTheory.Functor.CommShift.comp` of locally
seated factors.  Nothing identifies the two, so instance search either fails outright, or reports
`synthesized type class instance is not definitionally equal to expression inferred by typing
rules`, or succeeds with the datum a neighbouring junction then refuses.  Seating instances locally
in each consumer does not repair it.  Passing `ν` and `θ` keeps that search inside the chain lemma,
where every datum is a variable and the only instance available is the intended one.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open Stacks.Cohomology.KFlatDerivedPullback (derivedPullback_commShift)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

/-! ### One bookkeeping shape, with every object a variable

Pure `CategoryTheory.Category.id_comp` arithmetic for a chain with three identity-valued
associators and two pinning isomorphisms whose components are `CategoryTheory.Iso.refl`, stated
over an abstract category so that the single identification it is applied across is one `isDefEq`
rather than a dozen keyed rewrites — the four-factor analogue of
`Stacks.Cohomology.DerivedPullbackTensor.id_paste`. -/

/-- Three factors of a chain, interleaved with the identities its associators contribute, against
their bare composite — with the last two factors replaced along given equalities. -/
theorem id_paste₄ {D : Type*} [Category D] {A B C E : D} (g : A ⟶ B) {d d' : B ⟶ C}
    {r r' : C ⟶ E} (hd : d = d') (hr : r = r') :
    𝟙 A ≫ g ≫ 𝟙 B ≫ d ≫ 𝟙 C ≫ r ≫ 𝟙 E = g ≫ d' ≫ r' := by
  rw [hd, hr]
  simp

/-- A morphism against itself wrapped in the identities that the components of a pinning
isomorphism with `CategoryTheory.Iso.refl` components contribute. -/
theorem id_wrap {D : Type*} [Category D] {A B : D} (x : A ⟶ B) : x = 𝟙 A ≫ x ≫ 𝟙 B := by
  simp

/-- A transformation whose conjugate by two isomorphisms is shift-compatible is shift-compatible,
for the shift data transported along the isomorphisms. -/
private theorem commShift_of_eq_inv_comp_comp_hom {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] {F G F' G' : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ F') (e' : G ≅ G') {θ : F ⟶ G} {η : F' ⟶ G'} [NatTrans.CommShift θ ℤ]
    (h : θ = e.hom ≫ η ≫ e'.inv) :
    letI := Functor.CommShift.ofIso e ℤ
    letI := Functor.CommShift.ofIso e' ℤ
    NatTrans.CommShift η ℤ := by
  let := Functor.CommShift.ofIso e ℤ
  let := Functor.CommShift.ofIso e' ℤ
  let := Functor.CommShift.ofIso_compatibility e ℤ
  let := Functor.CommShift.ofIso_compatibility e' ℤ
  exact NatTrans.commShift_of_eq (eq_inv_comp_comp_hom e e' h)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The third leg at the spelling a one-variable component needs -/

/-- **The comparison of total tensor complexes along `f^*`, as an isomorphism of bifunctors on
cochain complexes**:

`Q(f^*Tot(K ⊗_{𝒪_Y} L)) ≅ Q(Tot(f^*K ⊗_{𝒪_X} f^*L))` before the localization is applied,

that is `CategoryTheory.Functor.mapBifunctorTotalBifunctorIso` at the degreewise comparison of
[Stacks, Tag 01CD].  It is `pullbackTensorComplexNatIso` curried: the same family of comparisons,
packaged as a transformation of bifunctors rather than one on the product category, which is the
packaging whose shift compatibility
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂` states. -/
def pullbackTensorComplexBifunctorIso :
    tensorComplexBifunctor (Y := Y) ⋙
        (Functor.whiskeringRight _ _ _).obj (pullbackComplex f) ≅
      pullbackComplex f ⋙ (tensorComplexBifunctorOn X ⋙
        (Functor.whiskeringLeft _ _ _).obj (pullbackComplex f)) :=
  Functor.mapBifunctorTotalBifunctorIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
    (StacksDraft.KFlat.modulePullback f) (StacksDraft.KFlat.modulePullback f)
    (StacksDraft.KFlat.modulePullback f) (comparisonAppIso f)
    (fun {_ _} w B => comparisonAppIso_naturality_left f w B)
    (fun A {_ _} w => comparisonAppIso_naturality_right f A w)

/-- **The bifunctor form of the comparison of total tensor complexes has the same components as
the product-category form.**  Both are
`CategoryTheory.Functor.mapBifunctorTotalIso` at the pair, read off by
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_inv_app_app` on one side and by the
definition of `totalComplexPairTransport` on the other.

This is a step of the proof of 079U, not a clause of any tag, so it carries no tag attribute. -/
theorem pullbackTensorComplexBifunctorIso_inv_app_app
    (K L : CochainComplex (Modules Y) ℤ) :
    ((pullbackTensorComplexBifunctorIso f).inv.app K).app L =
      (pullbackTensorComplexNatIso f).inv.app (K, L) :=
  Functor.mapBifunctorTotalBifunctorIso_inv_app_app
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
    (StacksDraft.KFlat.modulePullback f) (StacksDraft.KFlat.modulePullback f)
    (StacksDraft.KFlat.modulePullback f) (comparisonAppIso f)
    (fun {_ _} w B => comparisonAppIso_naturality_left f w B)
    (fun A {_ _} w => comparisonAppIso_naturality_right f A w) K L

/-- **The third leg, in both variables**: the bifunctor form of the comparison of total tensor
complexes is compatible with the shifts in each variable.  This is
`CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂`, which is an `instance` and so
has to be named at the unfolded spelling, together with
`CategoryTheory.NatTrans.CommShift₂.of_iso_invInt` for the direction `rightComparison` uses. -/
theorem pullbackTensorComplexBifunctorIso_inv_commShift₂ :
    NatTrans.CommShift₂Int (pullbackTensorComplexBifunctorIso f).inv := by
  unfold pullbackTensorComplexBifunctorIso
  exact NatTrans.CommShift₂.of_iso_invInt _

/-! ### The chain for the second comparison in the second variable -/

section SecondVariable

variable (K : CochainComplex (Modules Y) ℤ)

/-- **The second-variable component of `rightComparison f`, as a four-factor chain between the
pinned bifunctors.**  Reading `rightComparison` one variable at a time turns its three whiskerings
into four: the derived tensor product of `X` applied to the first leg at the *fixed* variable, the
first leg itself whiskered by the derived tensor product, the shared obligation at `f^*K`, and the
third leg; the three associators are the reassociations those whiskerings need, and are the
identity on every object.

That this typechecks says that `(curriedComplexesTensorOfPullbacks f).obj K` *is*
`Q ⋙ (Lf^* ⋙ (Lf^*QK ⊗^𝐋 -))` and `(curriedComplexesTotalPullback f).obj K` *is*
`Tot(K ⊗ -) ⋙ (f^* ⋙ Q)`, definitionally. -/
def rightComparisonPinnedApp :
    (curriedComplexesTensorOfPullbacks f).obj K ⟶ (curriedComplexesTotalPullback f).obj K :=
  (Functor.associator DerivedCategory.Q (derivedPullback f)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj K)))).inv ≫
    (Functor.whiskerLeft (DerivedCategory.Q ⋙ derivedPullback f)
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          ((derivedPullbackNatTrans f).app K)) ≫
      Functor.whiskerRight (derivedPullbackNatTrans f)
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K)))) ≫
    (Functor.associator (pullbackComplex f) DerivedCategory.Q
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K)))).hom ≫
    Functor.whiskerLeft (pullbackComplex f)
        (derivedToTensorPinnedApp X ((pullbackComplex f).obj K)) ≫
    (Functor.associator (pullbackComplex f)
        ((tensorComplexBifunctorOn X).obj ((pullbackComplex f).obj K)) DerivedCategory.Q).inv ≫
    Functor.whiskerRight ((pullbackTensorComplexBifunctorIso f).inv.app K) DerivedCategory.Q ≫
    (Functor.associator ((tensorComplexBifunctor (Y := Y)).obj K) (pullbackComplex f)
        DerivedCategory.Q).hom

/-- **The second-variable component of `rightComparison f`, at the pinned spelling, is
shift-compatible.**  All three junctions of the four-factor chain close at once, by
`CategoryTheory.NatTrans.commShift_assocChain₄`: at an abstract instantiation each junction
matches on the nose, and the identifications
`CategoryTheory.Functor.CommShift₂.precomp₁_commShiftObj`, `precomp₂_commShiftObj` and
`postcomp_commShiftObj` — all `rfl` — are discharged by the `isDefEq` of this `exact` rather than
being asked of instance search.

So the shared obligation `DerivedToTensorCommShift₂ X`, the first leg and the third leg are all
this component needs. -/
theorem rightComparisonPinnedApp_commShift (h : DerivedToTensorCommShift₂ X) :
    (letI := curriedComplexesTensorOfPullbacks_commShift₂Int f
    letI := curriedComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift (rightComparisonPinnedApp f K) ℤ) := by
  let := derivedPullback_commShift f
  let : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj K))).CommShift ℤ :=
    (derivedTensorCommShift₂Int X).commShiftObj _
  let : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).CommShift ℤ :=
    (derivedTensorCommShift₂Int X).commShiftObj _
  let : ((tensorComplexBifunctorOn X).obj ((pullbackComplex f).obj K)).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctorOn X).CommShift₂Int).commShiftObj _
  let : ((tensorComplexBifunctor (Y := Y)).obj K).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftObj K
  let := curriedComplexesDerivedTensor_commShift₂Int X
  let := curriedComplexesTotal_commShift₂Int X
  exact NatTrans.commShift_assocChain₄ DerivedCategory.Q (derivedPullback f)
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj K)))
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj K)))
    (pullbackComplex f) DerivedCategory.Q
    ((tensorComplexBifunctorOn X).obj ((pullbackComplex f).obj K))
    ((tensorComplexBifunctor (Y := Y)).obj K)
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
      ((derivedPullbackNatTrans f).app K))
    (derivedPullbackNatTrans f)
    (derivedToTensorPinnedApp X ((pullbackComplex f).obj K))
    ((pullbackTensorComplexBifunctorIso f).inv.app K)
    ((derivedTensorCommShift₂Int X).commShift_map ((derivedPullbackNatTrans f).app K))
    (derivedPullbackNatTrans_commShift f)
    (derivedToTensorPinnedApp_commShift X ((pullbackComplex f).obj K) h)
    ((pullbackTensorComplexBifunctorIso_inv_commShift₂ f).commShift_app K)

/-- **The components of the four-factor chain are the components of `rightComparison f`.**

Both sides are
`(Lf^*QK ⊗^𝐋 Lf^*QL ⟶ Q(f^*K) ⊗^𝐋 Q(f^*L)) ≫ (derivedToTensorNatTrans X).app (f^*K, f^*L) ≫
Q((pullbackTensorComplexNatIso f).inv.app (K, L))`, the chain's with the identities its three
associators contribute: the first factor of `rightComparison` is
`CategoryTheory.Functor.uncurry`'s action on a morphism of the product, which is *by definition*
the composite of the chain's first two factors.  What is not definitional is that the chain takes
the shared obligation at the pinned spelling and the third leg at the bifunctor spelling, and
those two identifications are `derivedToTensorPinnedApp_app` and
`pullbackTensorComplexBifunctorIso_inv_app_app`, each applied by name.

This is a step of the proof of `RightComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem rightComparisonPinnedApp_app (L : CochainComplex (Modules Y) ℤ) :
    (rightComparisonPinnedApp f K).app L = (rightComparison f).app (K, L) :=
  id_paste₄ _
    (derivedToTensorPinnedApp_app X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L))
    (congrArg (fun v => DerivedCategory.Q.map v)
      (pullbackTensorComplexBifunctorIso_inv_app_app f K L))

/-- **The chain is the second-variable component of `Functor.curry.map (rightComparison f)`,
conjugated by the two pinning isomorphisms.**  Given `rightComparisonPinnedApp_app` what is left
is that the two pinning isomorphisms contribute identities, which is `id_wrap`.

The two halves are separate declarations on purpose, and this is a split forced by cost rather than
a stylistic one: taken as one `exact` the elaborator accepts it and then the kernel reports
`(kernel) deterministic timeout` re-checking it.  The elaborator is entitled to the file's
`attribute [local implicit_reducible]` lines and the kernel is not, so it re-does the whole
identification — the chain's seven factors, `rightComparison`'s delta, `Functor.uncurry`'s action
on a morphism of the product, `Functor.curry.map`, both pinning isomorphisms and
`derivedToTensorPinnedApp`'s delta — with everything unfolded. Split here, each half is checked
on its own and both fit. -/
theorem rightComparisonPinnedApp_eq_curryApp :
    rightComparisonPinnedApp f K =
      ((curryComplexesTensorOfPullbacksIso f).app K).hom ≫
        (Functor.curry.map (rightComparison f)).app K ≫
          ((curryComplexesTotalPullbackIso f).app K).inv := by
  ext L
  exact (rightComparisonPinnedApp_app f K L).trans
    (id_wrap ((rightComparison f).app (K, L)))

/-- **The `commShift_app` half of `RightComparisonCommShift₂` at a fixed `K`**, granted the
obligation the two comparisons share.  The mirror of `leftComparisonCurryApp_commShift`: the chain
is shift-compatible at the *pinned* data, `eq_inv_comp_comp_hom` applied inline reads
`rightComparisonPinnedApp_eq_curryApp` backwards to identify the component with that chain
conjugated by the two pinning isomorphisms, and those are shift-compatible for the transported
data by `CategoryTheory.Functor.CommShift.ofIso_compatibility`. -/
theorem rightComparisonCurryApp_commShift (h : DerivedToTensorCommShift₂ X) :
    (letI := curryComplexesTensorOfPullbacks_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((Functor.curry.map (rightComparison f)).app K) ℤ) := by
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  let := curriedComplexesTensorOfPullbacks_commShift₂Int f
  let := curriedComplexesTotalPullback_commShift₂Int f
  let := rightComparisonPinnedApp_commShift f K h
  exact commShift_of_eq_inv_comp_comp_hom ((curryComplexesTensorOfPullbacksIso f).app K)
    ((curryComplexesTotalPullbackIso f).app K) (rightComparisonPinnedApp_eq_curryApp f K)

end SecondVariable

/-! ### The chain for the second comparison in the first variable -/

section FirstVariable

variable (L : CochainComplex (Modules Y) ℤ)

/-- **The first-variable component of `rightComparison f`, as a four-factor chain between the
pinned bifunctors.**  The mirror of `rightComparisonPinnedApp`, with the first two factors in the
opposite order: in this variable the derived tensor product's action on the *fixed* variable comes
second. -/
def rightComparisonPinnedFlipApp :
    (curriedComplexesTensorOfPullbacks f).flip.obj L ⟶
      (curriedComplexesTotalPullback f).flip.obj L :=
  (Functor.associator DerivedCategory.Q (derivedPullback f)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj L)))).inv ≫
    (Functor.whiskerRight (derivedPullbackNatTrans f)
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj L))) ≫
      Functor.whiskerLeft (pullbackComplex f ⋙ DerivedCategory.Q)
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.map
          ((derivedPullbackNatTrans f).app L))) ≫
    (Functor.associator (pullbackComplex f) DerivedCategory.Q
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj L)))).hom ≫
    Functor.whiskerLeft (pullbackComplex f)
        (derivedToTensorPinnedFlipApp X ((pullbackComplex f).obj L)) ≫
    (Functor.associator (pullbackComplex f)
        ((tensorComplexBifunctorOn X).flip.obj ((pullbackComplex f).obj L))
        DerivedCategory.Q).inv ≫
    Functor.whiskerRight ((pullbackTensorComplexBifunctorIso f).inv.flipApp L) DerivedCategory.Q ≫
    (Functor.associator ((tensorComplexBifunctor (Y := Y)).flip.obj L) (pullbackComplex f)
        DerivedCategory.Q).hom

/-- **The first-variable component of `rightComparison f`, at the pinned spelling, is
shift-compatible.**  The mirror of `rightComparisonPinnedApp_commShift`, with
`CategoryTheory.Functor.CommShift₂.precomp₁_commShiftFlipObj`, `precomp₂_commShiftFlipObj` and
`postcomp_commShiftFlipObj` at the three junctions. -/
theorem rightComparisonPinnedFlipApp_commShift (h : DerivedToTensorCommShift₂ X) :
    (letI := curriedComplexesTensorOfPullbacks_commShift₂Int f
    letI := curriedComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift (rightComparisonPinnedFlipApp f L) ℤ) := by
  let := derivedPullback_commShift f
  let : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj L))).CommShift ℤ :=
    (derivedTensorCommShift₂Int X).commShiftFlipObj _
  let : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj L))).CommShift ℤ :=
    (derivedTensorCommShift₂Int X).commShiftFlipObj _
  let : ((tensorComplexBifunctorOn X).flip.obj ((pullbackComplex f).obj L)).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctorOn X).CommShift₂Int).commShiftFlipObj _
  let : ((tensorComplexBifunctor (Y := Y)).flip.obj L).CommShift ℤ :=
    (inferInstance : (tensorComplexBifunctor (Y := Y)).CommShift₂Int).commShiftFlipObj L
  let := curriedComplexesDerivedTensor_commShift₂Int X
  let := curriedComplexesTotal_commShift₂Int X
  exact NatTrans.commShift_assocChain₄' DerivedCategory.Q (derivedPullback f)
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj L)))
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj L)))
    (pullbackComplex f) DerivedCategory.Q
    ((tensorComplexBifunctorOn X).flip.obj ((pullbackComplex f).obj L))
    ((tensorComplexBifunctor (Y := Y)).flip.obj L)
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.map
      ((derivedPullbackNatTrans f).app L))
    (derivedPullbackNatTrans f)
    (derivedToTensorPinnedFlipApp X ((pullbackComplex f).obj L))
    ((pullbackTensorComplexBifunctorIso f).inv.flipApp L)
    ((derivedTensorCommShift₂Int X).commShift_flip_map ((derivedPullbackNatTrans f).app L))
    (derivedPullbackNatTrans_commShift f)
    (derivedToTensorPinnedFlipApp_commShift X ((pullbackComplex f).obj L) h)
    ((pullbackTensorComplexBifunctorIso_inv_commShift₂ f).commShift_flipApp L)

/-- **The components of the flipped chain are the components of `rightComparison f`** — the same
components as in the second variable, read in the other order.  The mirror of
`rightComparisonPinnedApp_app`.

This is a step of the proof of `RightComparisonCommShift₂`, not a clause of any tag, so it carries
no tag attribute. -/
theorem rightComparisonPinnedFlipApp_app (K : CochainComplex (Modules Y) ℤ) :
    (rightComparisonPinnedFlipApp f L).app K = (rightComparison f).app (K, L) :=
  id_paste₄ _
    (derivedToTensorPinnedFlipApp_app X ((pullbackComplex f).obj L) ((pullbackComplex f).obj K))
    (congrArg (fun v => DerivedCategory.Q.map v)
      (pullbackTensorComplexBifunctorIso_inv_app_app f K L))

/-- **The flipped chain is the first-variable component of `Functor.curry.map (rightComparison f)`,
conjugated by the flips of the two pinning isomorphisms.**  The mirror of
`rightComparisonPinnedApp_eq_curryApp`, split into the same two halves and for the same
reason. -/
theorem rightComparisonPinnedFlipApp_eq_curryFlipApp :
    rightComparisonPinnedFlipApp f L =
      ((Functor.CommShift₂.flipIso (curryComplexesTensorOfPullbacksIso f)).app L).hom ≫
        (Functor.curry.map (rightComparison f)).flipApp L ≫
          ((Functor.CommShift₂.flipIso (curryComplexesTotalPullbackIso f)).app L).inv := by
  ext K
  exact (rightComparisonPinnedFlipApp_app f L K).trans
    (id_wrap ((rightComparison f).app (K, L)))

/-- **The `commShift_flipApp` half of `RightComparisonCommShift₂` at a fixed `L`**, granted the
obligation the two comparisons share.  The mirror of `rightComparisonCurryApp_commShift`. -/
theorem rightComparisonCurryFlipApp_commShift (h : DerivedToTensorCommShift₂ X) :
    (letI := curryComplexesTensorOfPullbacks_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((Functor.curry.map (rightComparison f)).flipApp L) ℤ) := by
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  let := curriedComplexesTensorOfPullbacks_commShift₂Int f
  let := curriedComplexesTotalPullback_commShift₂Int f
  let := rightComparisonPinnedFlipApp_commShift f L h
  exact commShift_of_eq_inv_comp_comp_hom
    ((Functor.CommShift₂.flipIso (curryComplexesTensorOfPullbacksIso f)).app L)
    ((Functor.CommShift₂.flipIso (curryComplexesTotalPullbackIso f)).app L)
    (rightComparisonPinnedFlipApp_eq_curryFlipApp f L)

end FirstVariable

/-! ### `RightComparisonCommShift₂`, with no hypothesis -/

/-- **`RightComparisonCommShiftApp f` holds**, granted the obligation the two comparisons of
[Stacks, Tag 079U] share: this is the statement `PullbackTensorCommShiftComparisons.lean` names
and leaves open in the second variable.

This is a step of the proof of 0B54 and 0G77, not a clause of either tag, so it carries no tag
attribute. -/
theorem rightComparisonCommShiftApp_of_derivedToTensor (h : DerivedToTensorCommShift₂ X) :
    RightComparisonCommShiftApp f :=
  fun K => rightComparisonCurryApp_commShift f K h

/-- **`RightComparisonCommShiftFlipApp f` holds**, granted the same obligation: the mirror in the
first variable.

This is a step of the proof of 0B54 and 0G77, not a clause of either tag, so it carries no tag
attribute. -/
theorem rightComparisonCommShiftFlipApp_of_derivedToTensor (h : DerivedToTensorCommShift₂ X) :
    RightComparisonCommShiftFlipApp f :=
  fun L => rightComparisonCurryFlipApp_commShift f L h

/-- **`RightComparisonCommShiftApp f` holds with no hypothesis**: the shared obligation is
`derivedToTensorCommShift₂` at `X`, a theorem of `PullbackTensorCommShiftFlipApp.lean`.

This is a step of the proof of 0B54 and 0G77, not a clause of either tag, so it carries no tag
attribute. -/
theorem rightComparisonCommShiftApp : RightComparisonCommShiftApp f :=
  rightComparisonCommShiftApp_of_derivedToTensor f (derivedToTensorCommShift₂ X)

/-- **`RightComparisonCommShiftFlipApp f` holds with no hypothesis.**

This is a step of the proof of 0B54 and 0G77, not a clause of either tag, so it carries no tag
attribute. -/
theorem rightComparisonCommShiftFlipApp : RightComparisonCommShiftFlipApp f :=
  rightComparisonCommShiftFlipApp_of_derivedToTensor f (derivedToTensorCommShift₂ X)

/-- **The second comparison of [Stacks, Tag 079U] is compatible with the shifts in both variables,
unconditionally.**  This is `rightComparisonCommShift₂_of` at its two halves, both of which this
file proves: the obligation `DerivedToTensorCommShift₂ X` the two comparisons share is discharged
by `derivedToTensorCommShift₂`, the first leg is `derivedPullbackNatTrans_commShift` and the third
is `CategoryTheory.Functor.mapBifunctorTotalBifunctorIso_commShift₂`.

Together with `leftComparisonCommShift₂'` this is the whole of what the shift compatibility of
[Stacks, Tag 079U] needed: both comparisons are now compatible with the shifts in both variables
with no hypothesis.

This is a step of the proof of 0B54 and 0G77, not a clause of either tag, so it carries no tag
attribute. -/
theorem rightComparisonCommShift₂ : RightComparisonCommShift₂ f :=
  rightComparisonCommShift₂_of f (rightComparisonCommShiftApp f)
    (rightComparisonCommShiftFlipApp f)

end Stacks.Cohomology.DerivedPullbackTensor

end
