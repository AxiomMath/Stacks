module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleGlueingEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The second dictionary square of Stacks 03LY

Stacks 03LY describes a sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X`
by a family of modules on the small étale sites of the étale scheme charts of `X`; the
module-coefficient form of Stacks 0GWK does the same with the slices `X_étale/U`.  The
object-by-object dictionary between the two indexings is
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceComparison.lean`, and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleGlueingEquivalence.lean` turns it into an
equivalence of glueing data granted its two *dictionary squares*.  This file proves the second
of them, the one for the **structure morphism of a chart**: that the dictionary carries
`AlgebraicGeometry.Space.chartModuleRestrictionComp` to `SheafOfModules.overFunctorMap`.  The
statement proved, `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_comp`, is the body of
`AlgebraicGeometry.Space.ChartModuleRestrictionSliceSquare`, written out as an explicit `∀`
because a consumer cannot take it through that definition.

It is the module-coefficient analogue of
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartDictionaryCoherence.lean`), which is the
same square for sheaves of sets, and it is proved the same way: the chart-level *bridge* of
Stacks 03LU against Stacks Equation 03LW, together with the cancellation of the transport that
bridge carries against the comparison of Stacks 04M0.

The bridge itself is a hypothesis here, `hcoh`.  It is
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, restricted to
*relatively representable* étale pairs, which is no restriction for Stacks 03LY: both chart
families are relatively representable
(`AlgebraicGeometry.Space.relativelyRepresentable_chartMap` and
`AlgebraicGeometry.Space.relativelyRepresentable_chartToSpace`).  And in that restricted form it
is a theorem,
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_representable`, so
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleSliceDictionarySquares.lean` discharges the
hypothesis and restates this square with none.

## Main results

* `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_comp`: **the second dictionary square
  of Stacks 03LY**.
* `AlgebraicGeometry.Space.chartModuleSliceSquare`: the square with the comparisons of
  Stacks 03LW split off both dictionary isomorphisms — what is left is restriction along the
  comparison of Stacks 04M0 against the transport along
  `AlgebraicGeometry.Space.chartMap_comp_chartToSpace`, and that is the only part with content
  on sections.
* `AlgebraicGeometry.Space.chartModuleSliceSquare_bridge`: that content, on one section: the
  component of `AlgebraicGeometry.Space.chartLocalizationPostcompIso` has the identity for its
  underlying morphism of the big fppf site, so restricting along it *is* the transport.
* `CategoryTheory.comp_bridge_transport`: the abstract rearrangement the assembly needs,
  coefficient-free.

## Implementation notes

Three measurements shape the file, and each was forced by a failure.

**Every comparison is applied by a definition whose type is written out uncomposed.**  This is
the device of `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleGlueingEquivalence.lean`, for the
same reason: a component of an isomorphism of *composite* functors is typed through
`(F ⋙ G).obj T`, the data it must meet are typed through `G.obj (F.obj T)`, and reconciling the
two inline exhausts the elaborator.  So the two dictionary isomorphisms are split, by
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso_eq` and
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso_eq_tail`, into the comparison of
Stacks 03LW and a *tail*, and every tail, transport and comparison is then applied by its own
definition at a variable module.

**On sections, no step may collapse more than one restriction functor.**  Comparing two
spellings of a module over a chart is cheap when they differ by one
`SheafOfModules.pushforward`; comparing a two-fold restriction with the sections of `F` itself
is not, and neither is any `Eq.trans` whose intermediate term is two restrictions away from the
equation's own type.  `AlgebraicGeometry.Space.chartModuleSliceSquare_sections` is therefore a
chain in which every term is within one restriction of its neighbours, and the step that does
reach `F` — `AlgebraicGeometry.Space.chartModuleSliceSquare_bridge` — is a separate declaration
whose own equation lives one restriction away from `F`.

**A concrete `CategoryTheory.eqToHom` must never be presented where the elaborator will try to
reduce it.**  The transport this square carries comes from
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`, a propositional field, so it is a real
`CategoryTheory.eqToHom`; asking for `(A ≪≫ eqToIso h).hom.app M = _ ≫ (eqToIso h).hom.app M` at
a concrete `h` times out in the *kernel*, while the same identity at a variable `h` — which is
`CategoryTheory.iso_trans_hom_app` applied to an equality of isomorphisms — is immediate.  Every
splitting below is therefore performed by an abstract component lemma applied to an identity of
isomorphisms, never by `rfl` on sections of a concrete transport.

Finally, the order of the arguments of `CategoryTheory.comp_bridge_transport` is load-bearing:
the composite endpoints `P` and `Q` come *after* the factors, so that the intermediate objects
are fixed by the factors' own spellings and each composite is reconciled once, where it is
elaborated, rather than inside every hypothesis.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

/-- The component of a composite of isomorphisms of functors.  Stated abstractly: the concrete
isomorphisms it is applied to are adjoint mates and transports, and reducing their components is
what exhausts the budget, whereas an application checks only that the two isomorphisms are the
composite. -/
theorem iso_trans_hom_app {C : Type*} [Category C] {D : Type*} [Category D] {F G H : C ⥤ D}
    (A : F ≅ G) (Bq : G ≅ H) (M : C) :
    (A ≪≫ Bq).hom.app M = A.hom.app M ≫ Bq.hom.app M :=
  (Stacks.CategoryTheory.proj_congr (Iso.trans_hom A Bq) (fun α => NatTrans.app α M)).trans
    (NatTrans.comp_app A.hom Bq.hom M)

/-- The forward direction of a transport of functors, at an object. -/
theorem eqToIso_hom_app {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}
    (h : F = G) (M : C) : (eqToIso h).hom.app M = (eqToHom h).app M := rfl

/-- The rearrangement that turns two naturality squares, a bridge identity, a transport
identity and a coherence identity into one identity of composites.  Stated abstractly, with
every morphism an explicit argument, because the terms it is applied to are large and spelled
inconsistently -- the same object occurs both as `F.obj (G.obj T)` and as `(G ⋙ F).obj T` -- so
neither `rw` nor `simp` can reassociate the concrete composites, whereas an explicit application
checks only definitional equality. -/
theorem comp_bridge_transport {C : Type*} [Category C]
    {OA OB OC OD OE OF OP OQ OR B₀' B₂' G₁' : C}
    (a : OA ⟶ OC) (a1 : OA ⟶ OB) (a2 : OB ⟶ OC)
    (Bm : OC ⟶ OE) (b : OC ⟶ OD) (c : OD ⟶ OE) (D : OE ⟶ OF) (d : OE ⟶ OF)
    (p : OA ⟶ OP) (t : OP ⟶ OQ) (q : OQ ⟶ OR) (s : OR ⟶ OF)
    (P : OA ⟶ OQ) (Q : OQ ⟶ OF)
    (b' : OB ⟶ B₂') (a2' : B₂' ⟶ OD) (b₀ : OA ⟶ B₀') (a1' : B₀' ⟶ B₂')
    (γ : B₂' ⟶ G₁') (Φ : OP ⟶ G₁') (τ : G₁' ⟶ OR)
    (hA : Bm = b ≫ c) (hD : D = d) (hP : P = p ≫ t) (hQ : Q = q ≫ s) (ha : a = a1 ≫ a2)
    (hnat2 : a2 ≫ b = b' ≫ a2') (hnat1 : a1 ≫ b' = b₀ ≫ a1')
    (hbr : b₀ ≫ a1' ≫ γ = p ≫ Φ) (htr : Φ ≫ τ = t ≫ q)
    (hstar : a2' ≫ c ≫ d = γ ≫ τ ≫ s) :
    a ≫ Bm ≫ D = P ≫ Q := by
  rw [hA, hD, hP, hQ, ha]
  simp only [Category.assoc]
  rw [← Category.assoc a2, hnat2]
  simp only [Category.assoc]
  rw [← Category.assoc a1, hnat1]
  simp only [Category.assoc]
  rw [hstar, ← Category.assoc t q s, ← htr]
  simpa only [Category.assoc] using congrArg (fun z : OA ⟶ G₁' => z ≫ τ ≫ s) hbr

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The transport of étale restriction along an equality of étale morphisms, at a module. -/
def etaleModulePullbackTransportApp {A' Y' : AlgebraicSpaces B S hS} {n n' : A' ⟶ Y'}
    (hn : IsEtale B S hS n.hom) (hn' : IsEtale B S hS n'.hom) (e : n = n')
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) :
    (etaleModulePullback.{u, u} B S hS n hn).obj M ⟶
      (etaleModulePullback.{u, u} B S hS n' hn').obj M :=
  (eqToHom (etaleModulePullback_congr B S hS hn hn' e)).app M

/-- The comparison of Stacks 03LW is compatible with the transport along an equality of étale
morphisms. -/
theorem eqToHom_comp_modulePullbackIsoEtaleModulePullback {A' Y' : AlgebraicSpaces B S hS}
    {n n' : A' ⟶ Y'} (hn : IsEtale B S hS n.hom) (hn' : IsEtale B S hS n'.hom) (e : n = n')
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) :
    (eqToHom (congrArg (fun z : A' ⟶ Y' => modulePullback B S hS z) e)).app M ≫
        (modulePullbackIsoEtaleModulePullback B S hS n' hn').hom.app M =
      (modulePullbackIsoEtaleModulePullback B S hS n hn).hom.app M ≫
        (eqToHom (etaleModulePullback_congr B S hS hn hn' e)).app M := by
  subst e
  obtain rfl : hn = hn' := rfl
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- `AlgebraicGeometry.Space.eqToHom_comp_modulePullbackIsoEtaleModulePullback` with the
transport applied by `AlgebraicGeometry.Space.etaleModulePullbackTransportApp`.  The unfolding is
performed here, at a variable equality of morphisms, where `CategoryTheory.eqToHom` cannot be
reduced and the match is syntactic. -/
theorem modulePullbackIsoEtaleModulePullback_transportApp {A' Y' : AlgebraicSpaces B S hS}
    {n n' : A' ⟶ Y'} (hn : IsEtale B S hS n.hom) (hn' : IsEtale B S hS n'.hom) (e : n = n')
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) :
    (eqToIso (congrArg (fun z : A' ⟶ Y' => modulePullback B S hS z) e)).hom.app M ≫
        (modulePullbackIsoEtaleModulePullback B S hS n' hn').hom.app M =
      (modulePullbackIsoEtaleModulePullback B S hS n hn).hom.app M ≫
        etaleModulePullbackTransportApp B S hS hn hn' e M :=
  (Stacks.CategoryTheory.proj_congr
      (eqToIso_hom_app (congrArg (fun z : A' ⟶ Y' => modulePullback B S hS z) e) M)
      (fun z => z ≫ (modulePullbackIsoEtaleModulePullback B S hS n' hn').hom.app M)).trans
    (eqToHom_comp_modulePullbackIsoEtaleModulePullback B S hS hn hn' e M)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The second factor of `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`. -/
noncomputable def chartModuleRestrictionSliceTail (U : SmallEtale B S hS X.1) :
    etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U) ≅
      SheafOfModules.overFunctor (structureRingSheaf B S hS X) U ⋙
        chartModuleSliceReindex B S hS X U :=
  (@SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X U).1) _ (Over U) _
      (SmallEtale B S hS X.1) _
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X U))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_chartSpace B S hS X U)
      (chartSliceRingMap B S hS X U)
      (SmallEtale.topology B S hS X.1) (Over.forget U)
      (structureRingSheaf B S hS X) inferInstance (sliceRingMap B S hS X U) ≪≫
    @SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X U).1) _ (SmallEtale B S hS X.1) _
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U)
      (structureRingSheaf B S hS (chartSpace B S hS X U))
      (structureRingSheaf B S hS X)
      (isContinuous_chartLocalization_comp_forget B S hS X U) _ _
      (chartSliceRingMap_comp B S hS X U)).symm

/-- The restriction-to-a-chart dictionary splits as the comparison of Stacks 03LW followed by
its tail. -/
theorem chartModuleRestrictionSliceIso_eq (U : SmallEtale B S hS X.1) :
    chartModuleRestrictionSliceIso B S hS X U =
      modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U) ≪≫
        chartModuleRestrictionSliceTail B S hS X U := rfl

/-- Restriction of modules along the comparison functor of Stacks 04M0 at the smaller chart
followed by the slice functor, taken at the normalised structure map. -/
noncomputable def chartOverMapModulePushforward {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over U) ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2 :=
  @SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
    (structureRingSheaf B S hS (chartSpace B S hS X V))
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_chartLocalization_comp_overMap B S hS X f)
    (chartOverMapRingMap B S hS X f)

/-- Restriction of modules along chartwise postcomposition followed by the comparison functor
of Stacks 04M0 at the larger chart, taken at the normalised structure map. -/
noncomputable def chartPostcompModulePushforward {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over U) ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2 :=
  @SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
      SmallEtale.chartLocalization B S hS X.1 U)
    (structureRingSheaf B S hS (chartSpace B S hS X V))
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X f)
    (chartPostcompRingMap B S hS X f)

/-- The last two factors of the tail of
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`. -/
noncomputable def chartModuleSliceTail₃ {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartOverMapModulePushforward B S hS X f ≅
      SheafOfModules.overMap (structureRingSheaf B S hS X) f ⋙
        chartModuleSliceReindex B S hS X V :=
  (@SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_comp_overMap B S hS X (f := f)) _ _
      (chartOverMapRingMap_comp B S hS X f)).symm ≪≫
    (@SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over V) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      (SmallEtale.chartLocalization B S hS X.1 V)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over V)
      (isContinuous_chartLocalization_chartSpace B S hS X V)
      (chartSliceRingMap B S hS X V)
      ((SmallEtale.topology B S hS X.1).over U) (Over.map f)
      ((structureRingSheaf B S hS X).over U) inferInstance
      (Sheaf.pushforwardOverMapIso (structureRingSheaf B S hS X) f).inv).symm

/-- The comparison of Stacks 04M0 for the two composite functors of sites, read on sheaves of
modules: it carries one normalised structure map to the other by
`AlgebraicGeometry.Space.chartPostcompRingMap_natTrans`, so it introduces no twist. -/
noncomputable def chartModuleSliceCongr₂ {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartPostcompModulePushforward B S hS X f ≅ chartOverMapModulePushforward B S hS X f :=
  @SheafOfModules.pushforwardCongr₂
    (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
    (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
      SmallEtale.chartLocalization B S hS X.1 U)
    (structureRingSheaf B S hS (chartSpace B S hS X V))
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_chartLocalization_comp_overMap B S hS X f)
    (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X f)
    (chartPostcompRingMap B S hS X f) _ (chartLocalizationPostcompIso B S hS X f).symm
    (chartPostcompRingMap_natTrans B S hS X f)

/-- The last three factors of the tail of
`AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`: the comparison of Stacks 04M0 for
the two composite functors of sites, followed by
`AlgebraicGeometry.Space.chartModuleSliceTail₃`. -/
noncomputable def chartModuleSliceTail₂ {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartPostcompModulePushforward B S hS X f ≅
      SheafOfModules.overMap (structureRingSheaf B S hS X) f ⋙
        chartModuleSliceReindex B S hS X V :=
  chartModuleSliceCongr₂ B S hS X f ≪≫ chartModuleSliceTail₃ B S hS X f

/-- The tail of `AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`. -/
noncomputable def chartModuleInverseImageSliceTail {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleSliceReindex B S hS X U ⋙
        etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f) ≅
      SheafOfModules.overMap (structureRingSheaf B S hS X) f ⋙
        chartModuleSliceReindex B S hS X V :=
  @SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _
      (SmallEtale B S hS (chartSpace B S hS X U).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f))
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      (structureRingSheaf B S hS (chartSpace B S hS X U)) inferInstance
      (chartMapRingMap B S hS X f)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 U)
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_chartSpace B S hS X U)
      (chartSliceRingMap B S hS X U) ≪≫
    @SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X (f := f)) _ _
      (chartMapRingMap_comp B S hS X f) ≪≫
    chartModuleSliceTail₂ B S hS X f

/-- The chartwise-pullback dictionary splits as the comparison of Stacks 03LW whiskered by the
reindexing, followed by its tail. -/
theorem chartModuleInverseImageSliceIso_eq_tail {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleInverseImageSliceIso B S hS X f =
      Functor.isoWhiskerLeft (chartModuleSliceReindex B S hS X U)
          (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
            (isEtale_chartMap B S hS X f)) ≪≫
        chartModuleInverseImageSliceTail B S hS X f := rfl

/-! ### The comparisons, applied at a module

Every comparison below is applied by a definition whose type is written out *uncomposed*, so
that the reconciliation of `(F ⋙ G).obj T` with `G.obj (F.obj T)` happens once, at a variable
module, and never inline; see the implementation notes. -/

/-- The tail of the restriction dictionary at a module. -/
def chartModuleRestrictionSliceTailApp (U : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj F ⟶
      (chartModuleSliceReindex B S hS X U).obj
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) :=
  (chartModuleRestrictionSliceTail B S hS X U).hom.app F

/-- The chartwise étale restriction of `AlgebraicGeometry.Space.chartModuleRestrictionSliceTailApp`
along a morphism of charts. -/
def chartModuleRestrictionSliceTailMapApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).obj F) ⟶
      (etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj
        ((chartModuleSliceReindex B S hS X U).obj
          ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F)) :=
  (etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
    (isEtale_chartMap B S hS X f)).map (chartModuleRestrictionSliceTailApp B S hS X U F)

/-- The tail of the chartwise-pullback dictionary at a module on the slice. -/
def chartModuleInverseImageSliceTailApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).obj
        ((chartModuleSliceReindex B S hS X U).obj M) ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj M) :=
  (chartModuleInverseImageSliceTail B S hS X f).hom.app M

/-- Its last three factors, at a module on the slice. -/
def chartModuleSliceTail₂App {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartPostcompModulePushforward B S hS X f).obj M ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj M) :=
  (chartModuleSliceTail₂ B S hS X f).hom.app M

/-- Its last two factors, at a module on the slice. -/
def chartModuleSliceTail₃App {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartOverMapModulePushforward B S hS X f).obj M ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj M) :=
  (chartModuleSliceTail₃ B S hS X f).hom.app M

/-- The comparison of Stacks 04M0 for the two composite functors of sites, at a module on the
slice. -/
def chartModuleSliceCongr₂App {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    (chartPostcompModulePushforward B S hS X f).obj M ⟶
      (chartOverMapModulePushforward B S hS X f).obj M :=
  (chartModuleSliceCongr₂ B S hS X f).hom.app M

/-- The slice comparison of the two restrictions of an `𝒪_X`-module, at the module. -/
def overFunctorMapApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS X) V).obj F :=
  (SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F

/-- The same, read through the comparison equivalence of Stacks 04M0 at the smaller chart. -/
def reindexOverFunctorMapApp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
          ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F)) ⟶
      (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) V).obj F) :=
  (chartModuleSliceReindex B S hS X V).map (overFunctorMapApp B S hS X f F)

/-- The composition comparison of Stacks 03LU, at a module, with both endpoints written out
uncomposed. -/
def modulePullbackCompApp {A' C' D' : AlgebraicSpaces B S hS} (k : D' ⟶ A') (l : A' ⟶ C')
    (M : Modules.{u, u} B S hS C'.1 C'.2) :
    (modulePullback B S hS k).obj ((modulePullback B S hS l).obj M) ⟶
      (modulePullback B S hS (k ≫ l)).obj M :=
  (modulePullbackCompIso B S hS k l).hom.app M

theorem pom_map_id_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {Z : Cᵒᵖ} (y : M.obj Z) :
    ModuleCat.Hom.hom (M.map (𝟙 Z)) y = y := by
  rw [M.map_id]
  rfl

theorem modules_comp_val_app_hom (W' : AlgebraicSpaces B S hS)
    {M N P : Modules.{u, u} B S hS W'.1 W'.2} (φ : M ⟶ N) (ψ : N ⟶ P)
    (Z : (SmallEtale B S hS W'.1)ᵒᵖ) (x : M.val.obj Z) :
    ModuleCat.Hom.hom ((φ ≫ ψ).val.app Z) x =
      ModuleCat.Hom.hom (ψ.val.app Z) (ModuleCat.Hom.hom (φ.val.app Z) x) := rfl

/-- The sections of a composite of three morphisms of modules, one factor at a time. -/
private theorem modules_comp_comp_val_app_hom (W' : AlgebraicSpaces B S hS)
    {M N P Q : Modules.{u, u} B S hS W'.1 W'.2} (φ : M ⟶ N) (ψ : N ⟶ P) (χ : P ⟶ Q)
    (Z : (SmallEtale B S hS W'.1)ᵒᵖ) (x : M.val.obj Z) :
    ModuleCat.Hom.hom ((φ ≫ ψ ≫ χ).val.app Z) x =
      ModuleCat.Hom.hom (χ.val.app Z)
        (ModuleCat.Hom.hom (ψ.val.app Z) (ModuleCat.Hom.hom (φ.val.app Z) x)) :=
  (modules_comp_val_app_hom B S hS W' φ (ψ ≫ χ) Z x).trans
    (modules_comp_val_app_hom B S hS W' ψ χ Z _)

theorem etaleModulePullback_map_val_app_hom {A' Y' : AlgebraicSpaces B S hS} (n : A' ⟶ Y')
    (hn : IsEtale B S hS n.hom) {M N : Modules.{u, u} B S hS Y'.1 Y'.2} (φ : M ⟶ N)
    (W : SmallEtale B S hS A'.1)
    (y : ((etaleModulePullback.{u, u} B S hS n hn).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom (((etaleModulePullback.{u, u} B S hS n hn).map φ).val.app (op W)) y =
      ModuleCat.Hom.hom (φ.val.app (op ((smallEtalePostcomp B S hS n hn).obj W))) y := rfl

theorem etaleModulePullbackComp_hom_app_val_app_hom {A' C' D' : AlgebraicSpaces B S hS}
    (h' : D' ⟶ A') (g' : A' ⟶ C') (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
    (hhg' : IsEtale B S hS (h' ≫ g').hom) (M : Modules.{u, u} B S hS C'.1 C'.2)
    (W : SmallEtale B S hS D'.1)
    (y : ((etaleModulePullback.{u, u} B S hS g' hg').obj M).val.obj
      (op ((smallEtalePostcomp B S hS h' hh').obj W))) :
    ModuleCat.Hom.hom
        ((etaleModulePullbackCompApp B S hS h' g' hh' hg' hhg' M).val.app (op W)) y =
      y := rfl

theorem eqToHom_etaleModulePullback_app_val_app {A' Y' : AlgebraicSpaces B S hS}
    {n n' : A' ⟶ Y'} (hn : IsEtale B S hS n.hom) (hn' : IsEtale B S hS n'.hom) (e : n = n')
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) (W : SmallEtale B S hS A'.1)
    (y : ((etaleModulePullback.{u, u} B S hS n hn).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((etaleModulePullbackTransportApp B S hS hn hn' e M).val.app (op W)) y =
      ModuleCat.Hom.hom (M.val.map (eqToHom (Functor.congr_obj
        (smallEtalePostcomp_congr B S hS hn' hn e.symm) W)).op) y := by
  subst e
  obtain rfl : hn = hn' := rfl
  refine Eq.trans ?_ (Stacks.CategoryTheory.proj_congr
    (show (𝟙 ((smallEtalePostcomp B S hS n hn).obj W)) =
        eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS hn hn rfl) W) from
      (eqToHom_refl _ _).symm)
    (fun g => ModuleCat.Hom.hom (M.val.map g.op) y))
  exact (pom_map_id_apply M.val (Z := op ((smallEtalePostcomp B S hS n hn).obj W)) y).symm

theorem chartModuleRestrictionSliceTail_hom_app_val_app (U : SmallEtale B S hS X.1)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X U).1)
    (y : ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((chartModuleRestrictionSliceTailApp B S hS X U M).val.app (op W)) y = y := rfl

theorem chartModuleSliceReindex_map_val_app (U : SmallEtale B S hS X.1)
    {M N : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)} (ψ : M ⟶ N)
    (W : SmallEtale B S hS (chartSpace B S hS X U).1)
    (y : ((chartModuleSliceReindex B S hS X U).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom (((chartModuleSliceReindex B S hS X U).map ψ).val.app (op W)) y =
      ModuleCat.Hom.hom
        (ψ.val.app (op ((SmallEtale.chartLocalization B S hS X.1 U).obj W))) y := rfl

theorem overFunctorMap_hom_app_val_app {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) (Z : (Over V)ᵒᵖ)
    (y : (((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U ⋙
      SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj F).val.obj Z)) :
    ModuleCat.Hom.hom ((overFunctorMapApp B S hS X f F).val.app Z) y = y := rfl

theorem chartModuleInverseImageSliceTail_hom_app_val_app {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (y : ((chartPostcompModulePushforward B S hS X f).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((chartModuleInverseImageSliceTailApp B S hS X f M).val.app (op W)) y =
      ModuleCat.Hom.hom
        ((chartModuleSliceTail₂App B S hS X f M).val.app (op W)) y := rfl

theorem chartModuleSliceTail₂_hom_app_val_app {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (y : ((chartPostcompModulePushforward B S hS X f).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom ((chartModuleSliceTail₂App B S hS X f M).val.app (op W)) y =
      ModuleCat.Hom.hom ((chartModuleSliceTail₃App B S hS X f M).val.app (op W))
        (ModuleCat.Hom.hom
          ((chartModuleSliceCongr₂App B S hS X f M).val.app (op W)) y) := rfl

theorem chartModuleSliceCongr₂_hom_app_val_app {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (y : ((chartPostcompModulePushforward B S hS X f).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom ((chartModuleSliceCongr₂App B S hS X f M).val.app (op W)) y =
      ModuleCat.Hom.hom
        (M.val.map ((chartLocalizationPostcompIso B S hS X f).inv.app W).op) y := rfl

theorem chartModuleSliceTail₃_hom_app_val_app {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (z : ((chartOverMapModulePushforward B S hS X f).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom ((chartModuleSliceTail₃App B S hS X f M).val.app (op W)) z =
      z := rfl

theorem overFunctor_val_map_apply (U : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) {Z Z' : Over U} (β : Z ⟶ Z')
    (y : ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F).val.obj (op Z')) :
    ModuleCat.Hom.hom
        (((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F).val.map β.op) y =
      ModuleCat.Hom.hom (F.val.map β.left.op) y := rfl

/-- **The transport the bridge carries is the comparison of Stacks 04M0 on sections.**  The
component of `AlgebraicGeometry.Space.chartLocalizationPostcompIso` has the identity for its
underlying morphism of the big fppf site, so read in the small étale site of `X` it is the
transport along `AlgebraicGeometry.Space.chartMap_comp_chartToSpace`, and a section of an
`𝒪_X`-module is restricted the same way along either. -/
theorem chartLocalizationPostcompIso_inv_left_map_apply {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (x : ((etaleModulePullback.{u, u} B S hS
        (chartMap B S hS X f ≫ chartToSpace B S hS X U)
        (isEtale_chartMap_comp_chartToSpace B S hS X f)).obj F).val.obj (op W)) :
    ModuleCat.Hom.hom (F.val.map
        (((chartLocalizationPostcompIso B S hS X f).inv.app W).left).op) x =
      ModuleCat.Hom.hom (F.val.map (eqToHom (Functor.congr_obj
        (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
          (isEtale_chartMap_comp_chartToSpace B S hS X f)
          (chartMap_comp_chartToSpace B S hS X f).symm) W)).op) x :=
  have h1 : ((chartLocalizationPostcompIso B S hS X f).inv.app W).left =
      eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS
        (isEtale_chartToSpace B S hS X V)
        (isEtale_chartMap_comp_chartToSpace B S hS X f)
        (chartMap_comp_chartToSpace B S hS X f).symm) W) :=
    eq_eqToHom_of_left_eq_id B S hS _ _ (eqToHom_refl _ _).symm
  Stacks.CategoryTheory.proj_congr h1
    (fun g => ModuleCat.Hom.hom (F.val.map (Quiver.Hom.op g)) x)


/-- `AlgebraicGeometry.Space.chartModuleRestrictionSliceTailMapApp` is the identity on
sections. -/
theorem chartModuleRestrictionSliceTailMapApp_val_app {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (x : ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj F)).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((chartModuleRestrictionSliceTailMapApp B S hS X f F).val.app (op W)) x = x := rfl

/-- `AlgebraicGeometry.Space.reindexOverFunctorMapApp` is the identity on sections. -/
theorem reindexOverFunctorMapApp_val_app {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (z : ((chartModuleSliceReindex B S hS X V).obj
      ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F))).val.obj (op W)) :
    ModuleCat.Hom.hom ((reindexOverFunctorMapApp B S hS X f F).val.app (op W)) z = z := rfl

/-- The tail of the chartwise-pullback dictionary, on sections, up to the comparison of
Stacks 04M0 for the two composite functors of sites. -/
theorem chartModuleInverseImageSliceTailApp_val_app {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U))
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (y : ((chartPostcompModulePushforward B S hS X f).obj M).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((chartModuleInverseImageSliceTailApp B S hS X f M).val.app (op W)) y =
      ModuleCat.Hom.hom ((chartModuleSliceCongr₂App B S hS X f M).val.app (op W)) y := by
  refine Eq.trans (chartModuleInverseImageSliceTail_hom_app_val_app B S hS X f M W y) ?_
  refine Eq.trans (chartModuleSliceTail₂_hom_app_val_app B S hS X f M W y) ?_
  exact chartModuleSliceTail₃_hom_app_val_app B S hS X f M W _

/-- **The transport the bridge carries, read on sections.**  Restricting a section of `F` along
the component of `AlgebraicGeometry.Space.chartLocalizationPostcompIso` is the transport along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` of étale restrictions. -/
theorem chartModuleSliceSquare_bridge {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (w : ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj F)).val.obj (op W)) :
    ModuleCat.Hom.hom
        (((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F).val.map
          ((chartLocalizationPostcompIso B S hS X f).inv.app W).op) w =
      ModuleCat.Hom.hom
        ((etaleModulePullbackTransportApp B S hS
          (isEtale_chartMap_comp_chartToSpace B S hS X f)
          (isEtale_chartToSpace B S hS X V)
          (chartMap_comp_chartToSpace B S hS X f) F).val.app (op W)) w := by
  refine Eq.trans (overFunctor_val_map_apply B S hS X U F
    ((chartLocalizationPostcompIso B S hS X f).inv.app W) w) ?_
  refine Eq.trans (chartLocalizationPostcompIso_inv_left_map_apply B S hS X f F W w) ?_
  exact (eqToHom_etaleModulePullback_app_val_app B S hS
    (isEtale_chartMap_comp_chartToSpace B S hS X f)
    (isEtale_chartToSpace B S hS X V)
    (chartMap_comp_chartToSpace B S hS X f) F W w).symm

/-- **The coherence square at the structure morphism of a chart, on sections.** -/
theorem chartModuleSliceSquare_sections {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS (chartSpace B S hS X V).1)
    (x : ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).obj F)).val.obj (op W)) :
    ModuleCat.Hom.hom
        ((chartModuleRestrictionSliceTailMapApp B S hS X f F ≫
          chartModuleInverseImageSliceTailApp B S hS X f
              ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ≫
            reindexOverFunctorMapApp B S hS X f F).val.app (op W)) x =
      ModuleCat.Hom.hom
        ((etaleModulePullbackCompApp B S hS (chartMap B S hS X f) (chartToSpace B S hS X U)
            (isEtale_chartMap B S hS X f) (isEtale_chartToSpace B S hS X U)
            (isEtale_chartMap_comp_chartToSpace B S hS X f) F ≫
          etaleModulePullbackTransportApp B S hS
              (isEtale_chartMap_comp_chartToSpace B S hS X f)
              (isEtale_chartToSpace B S hS X V)
              (chartMap_comp_chartToSpace B S hS X f) F ≫
            chartModuleRestrictionSliceTailApp B S hS X V F).val.app (op W)) x := by
  refine Eq.trans ?_ (Eq.symm
    ((modules_comp_comp_val_app_hom B S hS (chartSpace B S hS X V) _ _ _ (op W) x).trans
      ((chartModuleRestrictionSliceTail_hom_app_val_app B S hS X V F W _).trans
        (Stacks.CategoryTheory.proj_congr
          (etaleModulePullbackComp_hom_app_val_app_hom B S hS (chartMap B S hS X f)
            (chartToSpace B S hS X U) (isEtale_chartMap B S hS X f)
            (isEtale_chartToSpace B S hS X U)
            (isEtale_chartMap_comp_chartToSpace B S hS X f) F W x)
          (fun z => ModuleCat.Hom.hom
            ((etaleModulePullbackTransportApp B S hS
              (isEtale_chartMap_comp_chartToSpace B S hS X f)
              (isEtale_chartToSpace B S hS X V)
              (chartMap_comp_chartToSpace B S hS X f) F).val.app (op W)) z)))))
  refine Eq.trans
    (modules_comp_comp_val_app_hom B S hS (chartSpace B S hS X V) _ _ _ (op W) x) ?_
  refine Eq.trans (reindexOverFunctorMapApp_val_app B S hS X f F W _) ?_
  refine Eq.trans (Stacks.CategoryTheory.proj_congr
    (chartModuleRestrictionSliceTailMapApp_val_app B S hS X f F W x)
    (fun z => ModuleCat.Hom.hom
      ((chartModuleInverseImageSliceTailApp B S hS X f
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F)).val.app
          (op W)) z)) ?_
  refine Eq.trans (chartModuleInverseImageSliceTailApp_val_app B S hS X f
    ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) W x) ?_
  refine Eq.trans (chartModuleSliceCongr₂_hom_app_val_app B S hS X f
    ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) W x) ?_
  exact chartModuleSliceSquare_bridge B S hS X f F W x

/-- **The coherence square at the structure morphism of a chart**, after the comparisons of
Stacks 03LW have been split off the two dictionary isomorphisms. -/
theorem chartModuleSliceSquare {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    chartModuleRestrictionSliceTailMapApp B S hS X f F ≫
        chartModuleInverseImageSliceTailApp B S hS X f
            ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ≫
          reindexOverFunctorMapApp B S hS X f F =
      etaleModulePullbackCompApp B S hS (chartMap B S hS X f) (chartToSpace B S hS X U)
          (isEtale_chartMap B S hS X f) (isEtale_chartToSpace B S hS X U)
          (isEtale_chartMap_comp_chartToSpace B S hS X f) F ≫
        etaleModulePullbackTransportApp B S hS
            (isEtale_chartMap_comp_chartToSpace B S hS X f)
            (isEtale_chartToSpace B S hS X V)
            (chartMap_comp_chartToSpace B S hS X f) F ≫
          chartModuleRestrictionSliceTailApp B S hS X V F := by
  ext A x
  exact chartModuleSliceSquare_sections B S hS X f F (Opposite.unop A) x

/-- The morphism of algebraic spaces represented by a morphism of charts, followed by the
structure morphism of the target chart, is relatively representable: it *is* the structure
morphism of the source chart. -/
theorem relativelyRepresentable_chartMap_comp_chartToSpace {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) :
    yoneda.relativelyRepresentable
      (chartMap B S hS X f ≫ chartToSpace B S hS X U).hom := by
  rw [chartMap_comp_chartToSpace]
  exact relativelyRepresentable_chartToSpace B S hS X V

/-! ### The splittings, at a module -/

/-- The restriction dictionary splits, at a module, as the comparison of Stacks 03LW followed by
its tail. -/
theorem chartModuleRestrictionSliceIso_hom_app_eq (U : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleRestrictionSliceIso B S hS X U).hom.app F =
      (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).hom.app F ≫
        chartModuleRestrictionSliceTailApp B S hS X U F := rfl

/-- The chartwise-pullback dictionary splits, at a module, as the comparison of Stacks 03LW
followed by its tail. -/
theorem chartModuleInverseImageSliceApp_eq_tail {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :
    chartModuleInverseImageSliceApp B S hS X f M =
      (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom.app
            ((chartModuleSliceReindex B S hS X U).obj M) ≫
        chartModuleInverseImageSliceTailApp B S hS X f M := rfl

/-- The comparison of Stacks 03LY for the structure morphism of a chart splits, at a module, as
the composition comparison of Stacks 03LU followed by the transport along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`. -/
theorem chartModuleRestrictionComp_eq_trans {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleRestrictionComp B S hS X f =
      modulePullbackCompIso B S hS (chartMap B S hS X f) (chartToSpace B S hS X U) ≪≫
        eqToIso (congrArg (fun z : chartSpace B S hS X V ⟶ X => modulePullback B S hS z)
          (chartMap_comp_chartToSpace B S hS X f)) := rfl

/-- The comparison of Stacks 03LY for the structure morphism of a chart splits, at a module, as
the composition comparison of Stacks 03LU followed by the transport along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`. -/
theorem chartModuleRestrictionComp_hom_app_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleRestrictionComp B S hS X f).hom.app F =
      modulePullbackCompApp B S hS (chartMap B S hS X f) (chartToSpace B S hS X U) F ≫
        (eqToIso (congrArg (fun z : chartSpace B S hS X V ⟶ X => modulePullback B S hS z)
          (chartMap_comp_chartToSpace B S hS X f))).hom.app F :=
  (Stacks.CategoryTheory.proj_congr (chartModuleRestrictionComp_eq_trans B S hS X f)
      (fun z => z.hom.app F)).trans
    (iso_trans_hom_app
      (modulePullbackCompIso B S hS (chartMap B S hS X f) (chartToSpace B S hS X U))
      (eqToIso (congrArg (fun z : chartSpace B S hS X V ⟶ X => modulePullback B S hS z)
        (chartMap_comp_chartToSpace B S hS X f))) F)

/-- **The transport of the bridge at a chart**, in the spelling the assembly consumes. -/
theorem chartModuleRestrictionTransport {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackIsoEtaleModulePullback B S hS
          (chartMap B S hS X f ≫ chartToSpace B S hS X U)
          (isEtale_chartMap_comp_chartToSpace B S hS X f)).hom.app F ≫
        etaleModulePullbackTransportApp B S hS
          (isEtale_chartMap_comp_chartToSpace B S hS X f)
          (isEtale_chartToSpace B S hS X V)
          (chartMap_comp_chartToSpace B S hS X f) F =
      (eqToIso (congrArg (fun z : chartSpace B S hS X V ⟶ X => modulePullback B S hS z)
          (chartMap_comp_chartToSpace B S hS X f))).hom.app F ≫
        (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).hom.app F :=
  (modulePullbackIsoEtaleModulePullback_transportApp B S hS
    (isEtale_chartMap_comp_chartToSpace B S hS X f)
    (isEtale_chartToSpace B S hS X V)
    (chartMap_comp_chartToSpace B S hS X f) F).symm

/-- The slice comparison of the two restrictions of a module, read through the comparison
equivalence of Stacks 04M0, is `AlgebraicGeometry.Space.reindexOverFunctorMapApp`. -/
theorem reindexOverFunctorMapApp_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleSliceReindex B S hS X V).map
        ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F) =
      reindexOverFunctorMapApp B S hS X f F := rfl

/-- **The second dictionary square of Stacks 03LY, for the structure morphism of a chart.** -/
theorem chartModuleRestrictionSliceIso_comp
    (hcoh : ∀ {A' C' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom),
      yoneda.relativelyRepresentable h'.hom → yoneda.relativelyRepresentable g'.hom →
      yoneda.relativelyRepresentable (h' ≫ g').hom →
      (modulePullbackCompIso B S hS h' g').hom ≫
          (modulePullbackIsoEtaleModulePullback B S hS (h' ≫ g') hhg').hom =
        Functor.whiskerLeft (modulePullback B S hS g')
            (modulePullbackIsoEtaleModulePullback B S hS h' hh').hom ≫
          Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g' hg').hom
              (etaleModulePullback.{u, u} B S hS h' hh') ≫
            (etaleModulePullbackComp B S hS h' g' hh' hg' hhg').hom)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleInverseImage B S hS X f).map
          ((chartModuleRestrictionSliceIso B S hS X U).hom.app F) ≫
        chartModuleInverseImageSliceApp B S hS X f
            ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F) ≫
          (chartModuleSliceReindex B S hS X V).map
            ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F) =
      (chartModuleRestrictionComp B S hS X f).hom.app F ≫
        (chartModuleRestrictionSliceIso B S hS X V).hom.app F := by
  have ha : (chartModuleInverseImage B S hS X f).map
        ((chartModuleRestrictionSliceIso B S hS X U).hom.app F) =
      (modulePullback B S hS (chartMap B S hS X f)).map
          ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
            (isEtale_chartToSpace B S hS X U)).hom.app F) ≫
        (modulePullback B S hS (chartMap B S hS X f)).map
          (chartModuleRestrictionSliceTailApp B S hS X U F) :=
    (Stacks.CategoryTheory.proj_congr
        (chartModuleRestrictionSliceIso_hom_app_eq B S hS X U F)
        (fun m => (modulePullback B S hS (chartMap B S hS X f)).map m)).trans
      ((modulePullback B S hS (chartMap B S hS X f)).map_comp _ _)
  refine comp_bridge_transport
    ((chartModuleInverseImage B S hS X f).map
      ((chartModuleRestrictionSliceIso B S hS X U).hom.app F))
    ((modulePullback B S hS (chartMap B S hS X f)).map
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).hom.app F))
    ((modulePullback B S hS (chartMap B S hS X f)).map
      (chartModuleRestrictionSliceTailApp B S hS X U F))
    (chartModuleInverseImageSliceApp B S hS X f
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F))
    ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.app
        ((chartModuleSliceReindex B S hS X U).obj
          ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F)))
    (chartModuleInverseImageSliceTailApp B S hS X f
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) U).obj F))
    ((chartModuleSliceReindex B S hS X V).map
      ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS X) f).hom.app F))
    (reindexOverFunctorMapApp B S hS X f F)
    (modulePullbackCompApp B S hS (chartMap B S hS X f) (chartToSpace B S hS X U) F)
    ((eqToIso (congrArg (fun z : chartSpace B S hS X V ⟶ X => modulePullback B S hS z)
      (chartMap_comp_chartToSpace B S hS X f))).hom.app F)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).hom.app F)
    (chartModuleRestrictionSliceTailApp B S hS X V F)
    ((chartModuleRestrictionComp B S hS X f).hom.app F)
    ((chartModuleRestrictionSliceIso B S hS X V).hom.app F)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.app
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).obj F))
    (chartModuleRestrictionSliceTailMapApp B S hS X f F)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.app
        ((modulePullback B S hS (chartToSpace B S hS X U)).obj F))
    ((etaleModulePullback.{u, u} B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).map
        ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).hom.app F))
    (etaleModulePullbackCompApp B S hS (chartMap B S hS X f) (chartToSpace B S hS X U)
      (isEtale_chartMap B S hS X f) (isEtale_chartToSpace B S hS X U)
      (isEtale_chartMap_comp_chartToSpace B S hS X f) F)
    ((modulePullbackIsoEtaleModulePullback B S hS
      (chartMap B S hS X f ≫ chartToSpace B S hS X U)
      (isEtale_chartMap_comp_chartToSpace B S hS X f)).hom.app F)
    (etaleModulePullbackTransportApp B S hS
      (isEtale_chartMap_comp_chartToSpace B S hS X f)
      (isEtale_chartToSpace B S hS X V)
      (chartMap_comp_chartToSpace B S hS X f) F)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact chartModuleInverseImageSliceApp_eq_tail B S hS X f _
  · exact (reindexOverFunctorMapApp_eq B S hS X f F)
  · exact chartModuleRestrictionComp_hom_app_eq B S hS X f F
  · exact chartModuleRestrictionSliceIso_hom_app_eq B S hS X V F
  · exact ha
  · exact (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.naturality
        (chartModuleRestrictionSliceTailApp B S hS X U F)
  · exact (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.naturality
        ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).hom.app F)
  · exact Stacks.CategoryTheory.proj_congr
      (hcoh (chartMap B S hS X f) (chartToSpace B S hS X U)
        (isEtale_chartMap B S hS X f) (isEtale_chartToSpace B S hS X U)
        (isEtale_chartMap_comp_chartToSpace B S hS X f)
        (relativelyRepresentable_chartMap B S hS X f)
        (relativelyRepresentable_chartToSpace B S hS X U)
        (relativelyRepresentable_chartMap_comp_chartToSpace B S hS X f)).symm
      (fun α => NatTrans.app α F)
  · exact chartModuleRestrictionTransport B S hS X f F
  · exact chartModuleSliceSquare B S hS X f F

end AlgebraicGeometry.Space

end
