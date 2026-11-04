module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# Restricting a derived adjunction to the adequate and quasi-coherent subcategories

Let `S` be a scheme and let `B` be a chosen big `τ`-site over `S`. The morphism of ringed sites
`f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` of [Stacks, Tag 070U] is expected to induce adjoint functors
between `D_Adeq(𝒪)`, the complexes of `𝒪`-modules on the big site with adequate cohomology, and
`D_QCoh(S)`, the complexes of `𝒪_S`-modules with quasi-coherent cohomology, with
`Rf_* Lf^* ≅ id`. This is [Stacks, Tag 070W].

This file supplies the subcategory bookkeeping that statement needs, in the two forms the source
uses it.

*The pushforward side.* The source's argument for `Rf_* : D_Adeq(𝒪) ⟶ D_QCoh(S)` is that after
the reduction to the Zariski topology of [Stacks, Tag 070V] the functor `f_*` is restriction to a
subcategory, hence exact, so `Rf_* = f_*`; the landing is then the module-level statement that
the restriction of an adequate module is quasi-coherent, which is [Stacks, Tag 06VM] (1). On a
chosen big fppf site over `S` both ingredients are in the library: the functor is
`Stacks.Adequate.BigSite.restrictModuleOfSheaf`, the direct image of sheaves of modules along the
morphism of ringed sites of [Stacks, Tag 070U], and the module-level landing is
`Stacks.Adequate.BigSite.isQuasicoherent_zariskiRestrictModule`. The step from the module-level
landing to the derived one is `DerivedCategoryB.mapDerivedCategoryB` below: an *exact* functor
commutes with the cohomology functors of the unbounded derived category, so it carries `D_B` into
`D_B'` as soon as it carries `B` into `B'`.

*The adjunction side.* Once both landings are available, the adjunction and the isomorphism
`Rf_* Lf^* ≅ id` are the ambient derived adjunction and the invertibility of its unit, read
through the two fully faithful inclusions. That reading is
`DerivedCategoryB.restrictAdjunction` and `DerivedCategoryB.restrictAdjunctionUnitIso`.

## Main definitions

* `DerivedCategoryB.mapDerivedCategoryHomologyIso` — an exact additive functor commutes with the
  cohomology functors of the unbounded derived category.
* `DerivedCategoryB.mapDerivedCategoryB` — the functor `D_B(A) ⥤ D_B'(A')` induced by an exact
  functor `A ⥤ A'` carrying `B` into `B'`, with
  `DerivedCategoryB.mapDerivedCategoryBCompι` recording its composite with the inclusion.
* `DerivedCategoryB.liftLeft` and `DerivedCategoryB.liftRight` — the restrictions of two
  functors between the ambient derived categories to the subcategories they preserve.
* `Stacks.Adequate.BigSite.derivedRestrictAdequate` — the functor `D_Adeq(𝒪) ⥤ D_QCoh(S)`
  induced by restriction to the small Zariski site of `S`, with
  `Stacks.Adequate.BigSite.derivedRestrictAdequateCompι` identifying its composite with the
  inclusion of `D_QCoh(S)` as the ambient `f_*` on derived categories.
* `Stacks.Adequate.BigSite.derivedAdequatePullback` and
  `Stacks.Adequate.BigSite.derivedAdequatePushforward` — `Lf^*` and `Rf_*` cut down to the two
  subcategories, given the two landings.

## Main results

* `DerivedCategoryB.derivedCategoryB_mapDerivedCategory` — the landing statement for an exact
  functor: `D_B(A)` goes to `D_B'(A')`.
* `DerivedCategoryB.restrictAdjunction` — an adjunction between the ambient derived categories
  restricts to the two subcategories it preserves.
* `DerivedCategoryB.isIso_restrictAdjunction_unit_app` and
  `DerivedCategoryB.restrictAdjunctionUnitIso` — if the ambient unit is invertible at every
  object of the source subcategory, the restricted composite is isomorphic to the identity.
* `Stacks.Adequate.BigSite.derivedAdequateAdjunction` — [Stacks, Tag 070W], the adjointness
  assertion: the restricted `Lf^*` and `Rf_*` between `D_QCoh(S)` and `D_Adeq(𝒪)` are adjoint.
* `Stacks.Adequate.BigSite.derivedAdequateCompIso` — [Stacks, Tag 070W], the assertion
  `Rf_* Lf^* ≅ id_{D_QCoh(S)}`, from the invertibility of the ambient unit on `D_QCoh(S)`.

## Implementation notes

**What is assumed and why.** On the adjunction side neither the ambient derived adjunction for
the morphism of [Stacks, Tag 070U] nor the landing of `Lf^*` is constructed here; they are the
hypotheses `adj`, `hL` and `hR`, and the clause strings of those tagged declarations say so.

The ambient adjunction is not available in the library for *this* morphism. The unbounded derived
pullback–pushforward adjunction of [Stacks, Tag 07A6] is
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction`,
and it is stated for morphisms of ringed topoi whose site has its objects and its morphisms in
one and the same universe. The source of the morphism of [Stacks, Tag 070U],
`AlgebraicGeometry.BigFppfOver.baseRingedTopos`, is a site whose objects are one universe above
its morphisms, so that adjunction does not apply to
`AlgebraicGeometry.BigFppfOver.baseToZariskiRingedToposHom` as it stands. Carrying the ambient
adjunction as a hypothesis keeps the subcategory statements usable at whatever construction of
`Lf^*` and `Rf_*` for this morphism lands later.

On the pushforward side the only thing left open is right exactness of the restriction functor.
Its additivity and its preservation of finite limits hold with no hypothesis — on underlying
presheaves the direct image is restriction along `v.op`, and it is a right adjoint — and are
recorded as the instances `Stacks.Adequate.BigSite.additive_restrictModuleOfSheaf` and
`Stacks.Adequate.BigSite.preservesFiniteLimits_restrictModuleOfSheaf`. Preservation of finite
colimits is the content of the source's reduction to the Zariski topology: the direct image along
an inclusion of sites is exact when the inclusion is almost cocontinuous ([Stacks, Tag 04BD],
available as
`Stacks.SheafOfModules.PushforwardRightExact.exactFunctor_pushforward_of_isAlmostCocontinuous`),
and the inclusion of the small Zariski site is almost cocontinuous into the big *Zariski* site
but not into the finer ones. The library carries almost cocontinuity of the analogous inclusion
for the Zariski site of a locally quasi-compact space
(`Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_isAlmostCocontinuous`) and not
for a chosen big site of schemes, so right exactness is an instance argument on the concrete
restriction functor.

*Which form of [Stacks, Tag 06VM] (1) is used.* The module-level landing is
`Stacks.Adequate.BigSite.isQuasicoherent_zariskiRestrictModule`, which carries no hypothesis.

**The two compatibility isomorphisms of `CategoryTheory.Adjunction.restrictFullyFaithful` are
identities.** Each restricted functor is by construction `CategoryTheory.ObjectProperty.lift` of
the composite of the inclusion with the ambient functor, and `liftCompιIso` of such a lift is
`Iso.refl`. This is what makes `isIso_restrictAdjunction_unit_app` a one-line reflection of
invertibility along the fully faithful inclusion rather than a diagram chase.

**`mapDerivedCategoryHomologyIso` is stated for a general exact functor.** The library has the
corresponding isomorphism only at the specific functors that consume it — the sheafification
functor of [Stacks, Tag 06Z0] gets it inlined inside
`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj` — and the same three-step
factorisation through `Functor.mapDerivedCategoryFactors`,
`DerivedCategory.homologyFunctorFactors` and `ShortComplex.mapHomologyIso` serves every exact
functor, so it is stated once here.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 070V](https://stacks.math.columbia.edu/tag/070V)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DerivedCategoryB

/-! ### An exact functor and the subcategories `D_B` -/

section Exact

variable {A A' : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category A'] [Abelian A'] [HasDerivedCategory A']
  (G : A ⥤ A') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An exact additive functor commutes with the cohomology functors of the unbounded derived
category. On a complex the comparison is `ShortComplex.mapHomologyIso`; it descends to the
derived category because both sides factor through the localisation at the
quasi-isomorphisms. -/
public def mapDerivedCategoryHomologyIso (n : ℤ) :
    G.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor A' n ≅
      DerivedCategory.homologyFunctor A n ⋙ G := by
  let e : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor A' (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ⋙ G :=
    NatIso.ofComponents (fun P ↦ (P.sc n).mapHomologyIso G) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map φ) G)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (G.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor A' n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor A n ⋙ G)) _ _
    (Functor.isoWhiskerRight G.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor A' n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors A' n) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A n).symm G)

variable {P : ObjectProperty A} {Q : ObjectProperty A'} [Q.IsClosedUnderIsomorphisms]
  (hGQ : ∀ X : A, P X → Q (G.obj X))

include hGQ in
/-- **The landing statement for an exact functor.** An exact additive functor carrying `B` into
`B'` carries the complexes with cohomology in `B` to complexes with cohomology in `B'`: its
degree-`n` cohomology is the image of the degree-`n` cohomology. -/
public theorem derivedCategoryB_mapDerivedCategory {K : DerivedCategory A}
    (hK : derivedCategoryB P K) :
    derivedCategoryB Q (G.mapDerivedCategory.obj K) := fun n ↦
  Q.prop_of_iso ((mapDerivedCategoryHomologyIso G n).app K).symm (hGQ _ (hK n))

/-- The functor `D_B(A) ⥤ D_B'(A')` induced by an exact additive functor carrying `B` into
`B'`. -/
public def mapDerivedCategoryB :
    (derivedCategoryB P).FullSubcategory ⥤ (derivedCategoryB Q).FullSubcategory :=
  (derivedCategoryB Q).lift ((derivedCategoryB P).ι ⋙ G.mapDerivedCategory)
    fun K ↦ derivedCategoryB_mapDerivedCategory G hGQ K.property

/-- Composing the induced functor with the inclusion of `D_B'(A')` gives the inclusion of
`D_B(A)` followed by the ambient induced functor. -/
public def mapDerivedCategoryBCompι :
    mapDerivedCategoryB G hGQ ⋙ (derivedCategoryB Q).ι ≅
      (derivedCategoryB P).ι ⋙ G.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

end Exact

/-! ### Restricting an adjunction of derived categories to two subcategories -/

section Restrict

variable {A A' : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category A'] [Abelian A'] [HasDerivedCategory A']
  {P : ObjectProperty A} {Q : ObjectProperty A'}
  (L : DerivedCategory A' ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ DerivedCategory A')
  (hL : ∀ K : DerivedCategory A', derivedCategoryB Q K → derivedCategoryB P (L.obj K))
  (hR : ∀ K : DerivedCategory A, derivedCategoryB P K → derivedCategoryB Q (R.obj K))

/-- A functor `D(A') ⥤ D(A)` carrying `D_B'(A')` into `D_B(A)`, cut down to those
subcategories. -/
public def liftLeft :
    (derivedCategoryB Q).FullSubcategory ⥤ (derivedCategoryB P).FullSubcategory :=
  (derivedCategoryB P).lift ((derivedCategoryB Q).ι ⋙ L) fun K ↦ hL _ K.property

/-- A functor `D(A) ⥤ D(A')` carrying `D_B(A)` into `D_B'(A')`, cut down to those
subcategories. -/
public def liftRight :
    (derivedCategoryB P).FullSubcategory ⥤ (derivedCategoryB Q).FullSubcategory :=
  (derivedCategoryB Q).lift ((derivedCategoryB P).ι ⋙ R) fun K ↦ hR _ K.property

/-- Composing `liftLeft` with the inclusion of `D_B(A)`. -/
public def liftLeftCompι :
    liftLeft L hL ⋙ (derivedCategoryB P).ι ≅ (derivedCategoryB Q).ι ⋙ L :=
  ObjectProperty.liftCompιIso _ _ _

/-- Composing `liftRight` with the inclusion of `D_B'(A')`. -/
public def liftRightCompι :
    liftRight R hR ⋙ (derivedCategoryB Q).ι ≅ (derivedCategoryB P).ι ⋙ R :=
  ObjectProperty.liftCompιIso _ _ _

/-- **An adjunction of derived categories restricts to two subcategories it preserves.** The
two compatibility isomorphisms are the identity, each restriction being by construction the lift
of the composite of the inclusion with the ambient functor. -/
public def restrictAdjunction (adj : L ⊣ R) : liftLeft L hL ⊣ liftRight R hR :=
  Adjunction.restrictFullyFaithful adj (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _) (liftLeftCompι L hL).symm (liftRightCompι R hR).symm

/-- If the unit of the ambient adjunction is invertible at every object of `D_B'(A')`, then the
unit of the restricted adjunction is invertible: the inclusion of `D_B'(A')` carries it to the
ambient unit, and a fully faithful functor reflects isomorphisms. -/
public theorem isIso_restrictAdjunction_unit_app (adj : L ⊣ R)
    (hunit : ∀ K : DerivedCategory A', derivedCategoryB Q K → IsIso (adj.unit.app K))
    (K : (derivedCategoryB Q).FullSubcategory) :
    IsIso ((restrictAdjunction L R hL hR adj).unit.app K) := by
  have h₁ : IsIso ((derivedCategoryB Q).ι.map
      ((restrictAdjunction L R hL hR adj).unit.app K)) := by
    have h₀ : IsIso (adj.unit.app ((derivedCategoryB Q).ι.obj K)) := hunit _ K.property
    rw [restrictAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
    infer_instance
  exact isIso_of_reflects_iso _ (derivedCategoryB Q).ι

/-- **`R ∘ L ≅ id` on the subcategory.** If the unit of the ambient adjunction is invertible at
every object of `D_B'(A')`, the restricted composite is isomorphic to the identity of
`D_B'(A')`. -/
public def restrictAdjunctionUnitIso (adj : L ⊣ R)
    (hunit : ∀ K : DerivedCategory A', derivedCategoryB Q K → IsIso (adj.unit.app K)) :
    liftLeft L hL ⋙ liftRight R hR ≅ 𝟭 (derivedCategoryB Q).FullSubcategory :=
  haveI : ∀ K : (derivedCategoryB Q).FullSubcategory,
      IsIso ((restrictAdjunction L R hL hR adj).unit.app K) :=
    fun K ↦ isIso_restrictAdjunction_unit_app L R hL hR adj hunit K
  haveI : IsIso (restrictAdjunction L R hL hR adj).unit := NatIso.isIso_of_isIso_app _
  (asIso (restrictAdjunction L R hL hR adj).unit).symm

end Restrict

end DerivedCategoryB

namespace Stacks.Adequate

universe d u

/-! ### The pushforward side, in the source's exact-restriction form -/

section Pushforward

variable {S : Scheme.{u}} (B : BigFppfSite.{u}) (hS : B.Contains S)

variable
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (BigSite.ofBigFppfSite B S hS).structureSheaf)]
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [PreservesFiniteColimits ((BigSite.ofBigFppfSite B S hS).restrictModuleOfSheaf)]

/-- **[Stacks, Tag 070W], the pushforward landing in the source's own form `Rf_* = f_*`.**
Restriction to the small Zariski site of `S` along the morphism of [Stacks, Tag 070U], assumed
right exact, induces a functor `D_Adeq(𝒪) ⥤ D_QCoh(S)` on the chosen big fppf site over `S`;
on modules it lands in the quasi-coherent sheaves by [Stacks, Tag 06VM] (1). -/
@[stacks 070W "the assertion that Rf_* carries D_Adeq(𝒪) into D_QCoh(S), in the source's own form
Rf_* = f_* for the Zariski restriction of the morphism of Tag 070U, with right exactness of that
restriction an instance argument. Lf^*, adjointness and Rf_* Lf^* ≅ id are covered elsewhere"]
public def BigSite.derivedRestrictAdequate :
    (BigSite.derivedAdequate.{u, u, d} (BigSite.ofBigFppfSite B S hS)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  DerivedCategoryB.mapDerivedCategoryB ((BigSite.ofBigFppfSite B S hS).restrictModuleOfSheaf)
    (BigSite.ofBigFppfSite B S hS).isQuasicoherent_zariskiRestrictModule

/-- `Rf_* = f_*`: composing `D_Adeq(𝒪) ⥤ D_QCoh(S)` with the inclusion of `D_QCoh(S)` gives the
inclusion of `D_Adeq(𝒪)` followed by the functor induced on unbounded derived categories by
restriction to the small Zariski site of `S`. -/
public def BigSite.derivedRestrictAdequateCompι :
    BigSite.derivedRestrictAdequate.{d, u} B hS ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent S.ringCatSheaf)).ι ≅
      (BigSite.derivedAdequate.{u, u, d} (BigSite.ofBigFppfSite B S hS)).ι ⋙
        ((BigSite.ofBigFppfSite B S hS).restrictModuleOfSheaf).mapDerivedCategory :=
  DerivedCategoryB.mapDerivedCategoryBCompι ((BigSite.ofBigFppfSite B S hS).restrictModuleOfSheaf)
    (BigSite.ofBigFppfSite B S hS).isQuasicoherent_zariskiRestrictModule

end Pushforward

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
  [HasSheafify B.topology AddCommGrpCat.{u}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} B.structureSheaf)]
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]

/-! ### The adjunction side -/

section Adjunction

variable (L : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) ⥤
    DerivedCategory (SheafOfModules.{u} B.structureSheaf))
  (R : DerivedCategory (SheafOfModules.{u} B.structureSheaf) ⥤
    DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
  (hL : ∀ K : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf),
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
      BigSite.derivedAdequate.{u, u, d} B (L.obj K))
  (hR : ∀ K : DerivedCategory (SheafOfModules.{u} B.structureSheaf),
    BigSite.derivedAdequate.{u, u, d} B K →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        (R.obj K))

/-- `Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)`, the ambient derived pullback cut down to the two
subcategories. -/
public abbrev BigSite.derivedAdequatePullback :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ⥤
      (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory :=
  DerivedCategoryB.liftLeft (P := adequate.{u, u} B)
    (Q := SheafOfModules.isQuasicoherent S.ringCatSheaf) L hL

/-- `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)`, the ambient derived pushforward cut down to the two
subcategories. -/
public abbrev BigSite.derivedAdequatePushforward :
    (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  DerivedCategoryB.liftRight (P := adequate.{u, u} B)
    (Q := SheafOfModules.isQuasicoherent S.ringCatSheaf) R hR

/-- **[Stacks, Tag 070W], the adjointness assertion.** Given the ambient derived adjunction
`Lf^* ⊣ Rf_*` on all `𝒪`-modules and the two landing assertions, the restricted functors
`Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` and `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` are adjoint.

The inputs are the ambient derived adjunction `adj : L ⊣ R` on all modules and both landing
assertions — `hL`, that `Lf^*` carries `D_QCoh(S)` into `D_Adeq(𝒪)`, and `hR`, that `Rf_*`
carries `D_Adeq(𝒪)` into `D_QCoh(S)`. Each carries its own content and none is proved here: the
ambient adjunction of [Stacks, Tag 07A6] is not available for the morphism of [Stacks, Tag 070U]
at the universes in which that morphism is stated. The isomorphism `Rf_* Lf^* ≅ id` is a
separate declaration. -/
@[stacks 070W "the adjointness assertion only, for the subcategories D_Adeq(O) and D_QCoh(S); \
the ambient adjunction and the two landing assertions are inputs, listed in the docstring"]
public def BigSite.derivedAdequateAdjunction (adj : L ⊣ R) :
    BigSite.derivedAdequatePullback B L hL ⊣
      BigSite.derivedAdequatePushforward B R hR :=
  DerivedCategoryB.restrictAdjunction (P := adequate.{u, u} B)
    (Q := SheafOfModules.isQuasicoherent S.ringCatSheaf) L R hL hR adj

/-- If the unit of the ambient derived adjunction is invertible at every complex with
quasi-coherent cohomology, the restricted composite `Rf_* Lf^*` is isomorphic to the identity of
`D_QCoh(S)`.

**This does not register [Stacks, Tag 070W] and carries no attribute.** The tag asserts
`Rf_* Lf^* ≅ id_{D_QCoh(S)}`, and `hunit` asserts that the unit of the adjunction producing that
composite is invertible on `D_QCoh(S)` — which is the same assertion. Mathlib's
`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` turns one into the other in three
lines, both compatibility isomorphisms here being `Iso.refl`
(`DerivedCategoryB.isIso_restrictAdjunction_unit_app` below). A hypothesis that is the conclusion
proves nothing, so the tag is left unregistered until `L`, `R` and `adj` are pinned to the derived
functors of the morphism of [Stacks, Tag 070U] and the unit is proved invertible. For the
coarsening of a topology that invertibility is now available, as
`Stacks.Cohomology.CompareTopologies.isIso_derivedUnit_app_singleFunctor_obj_imageOfLE`. -/
public def BigSite.derivedAdequateCompIso (adj : L ⊣ R)
    (hunit : ∀ K : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
        IsIso (adj.unit.app K)) :
    BigSite.derivedAdequatePullback B L hL ⋙
        BigSite.derivedAdequatePushforward B R hR ≅
      𝟭 (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  DerivedCategoryB.restrictAdjunctionUnitIso (P := adequate.{u, u} B)
    (Q := SheafOfModules.isQuasicoherent S.ringCatSheaf) L R hL hR adj hunit

end Adjunction

end Stacks.Adequate

end
