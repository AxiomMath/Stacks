module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The single-complex pullback comparison is compatible with composition

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is the canonical
map `Lf^*(M[-d]) ⟶ (f^*M)[-d]` of a morphism `f` of ringed spaces.  This file proves that it is
compatible with composition: for `a : X ⟶ Y` and `b : Y ⟶ Z` the two routes from
`La^*(Lb^*(M[-d]))` to `(a^*(b^*M))[-d]` — one comparison at a time, or the composition
isomorphism of [Stacks, Tag 0D5S] followed by the comparison for `a ≫ b` — agree up to the
ordinary pullback-composition isomorphism.

This is the statement a base-change argument on single complexes needs and which nothing
recorded: the comparison was known to be natural in the module
(`derivedToOrdinaryPullbackSingle_naturality`) but not to be multiplicative in the morphism.

## Main results

* `Stacks.SingleComparison.singleComparison` — the shape of the comparison with no geometry in
  it: a functor `L` between two "derived" categories, a functor `p` between the two "abelian"
  ones, a comparison `e : Q ⋙ L ⟶ k ⋙ Q'` of `L` with the "homotopy" level and the two
  identifications of the single functors.
* `Stacks.SingleComparison.singleComparison_comp` — **the formal core**: such comparisons
  compose, given the factorization of the comparison for the composite (the hypothesis `hfac`)
  and the coherence of the three single-functor identifications (the hypothesis `hsingle`).
* `AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_eq_singleComparison` — the
  geometric comparison is an instance of the abstract one.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_comp` — the
  coherence `hsingle` for degreewise pullback, proved on cochain complexes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_comp` —
  **the theorem**.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_congr` — the
  comparison transported along an equality of morphisms of ringed spaces.

## Implementation notes

*Why the core is stated abstractly.*  The repository records twice over that a chain of
naturality squares through `derivedToOrdinaryPullbackSingle` at the
`SheafOfModules (structureSheafRing _)` spelling runs into a deterministic `isDefEq` timeout; see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackSingleNaturality.lean` and of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TopDegreePullbackIdentity.lean`.  The chase
below is five naturality squares long, so it is carried out over variables, where the categories
are abstract, and instantiated by a single term.

*The two hypotheses.*  `hfac` is the universal property of
`Stacks.DerivedPullback.Composition.derivedPullbackCompComparison`, which is
`CategoryTheory.Functor.leftDerived_fac_app` at the comparison
`derivedPullbackCompCounit`; `hsingle` is the coherence of
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` with
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`, which reduces to cochain complexes through
`mapHomotopyCategorySingleFunctor_hom_app_eq` and is settled there degreewise.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### The formal core -/

namespace Stacks.SingleComparison

universe v u

section

variable {A A' K K' D D' : Type*} [Category A] [Category A'] [Category K] [Category K']
  [Category D] [Category D']

/-- **The shape of a single-complex comparison.**  For functors `H : A ⥤ K`, `Q : K ⥤ D` and
`P : A ⥤ D` with `s : P ≅ H ⋙ Q`, and the same primed on the other side, together with
`p : A ⥤ A'`, `k : K ⥤ K'`, `L : D ⥤ D'`, a comparison `e : Q ⋙ L ⟶ k ⋙ Q'` and an
identification `m : H ⋙ k ≅ p ⋙ H'`, the composite

`L(P M) ⟶ L(Q(H M)) ⟶ Q'(k(H M)) ⟶ Q'(H'(p M)) ⟶ P'(p M)`.

This is the shape of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle`. -/
def singleComparison (H : A ⥤ K) (Q : K ⥤ D) {P : A ⥤ D} (s : P ≅ H ⋙ Q)
    (H' : A' ⥤ K') (Q' : K' ⥤ D') {P' : A' ⥤ D'} (s' : P' ≅ H' ⋙ Q')
    {p : A ⥤ A'} {k : K ⥤ K'} {L : D ⥤ D'} (e : Q ⋙ L ⟶ k ⋙ Q')
    (m : H ⋙ k ≅ p ⋙ H') (M : A) :
    L.obj (P.obj M) ⟶ P'.obj (p.obj M) :=
  L.map (s.hom.app M) ≫ e.app (H.obj M) ≫ Q'.map (m.hom.app M) ≫ s'.inv.app (p.obj M)

end

section Comp

variable {AZ AY AX KZ KY KX DZ DY DX : Type*} [Category AZ] [Category AY] [Category AX]
  [Category KZ] [Category KY] [Category KX] [Category DZ] [Category DY] [Category DX]
  {HZ : AZ ⥤ KZ} {HY : AY ⥤ KY} {HX : AX ⥤ KX}
  {QZ : KZ ⥤ DZ} {QY : KY ⥤ DY} {QX : KX ⥤ DX}
  {PZ : AZ ⥤ DZ} {PY : AY ⥤ DY} {PX : AX ⥤ DX}
  (sZ : PZ ≅ HZ ⋙ QZ) (sY : PY ≅ HY ⋙ QY) (sX : PX ≅ HX ⋙ QX)
  {pb : AZ ⥤ AY} {pa : AY ⥤ AX} {pc : AZ ⥤ AX}
  {kb : KZ ⥤ KY} {ka : KY ⥤ KX} {kc : KZ ⥤ KX}
  {Lb : DZ ⥤ DY} {La : DY ⥤ DX} {Lc : DZ ⥤ DX}
  (eb : QZ ⋙ Lb ⟶ kb ⋙ QY) (ea : QY ⋙ La ⟶ ka ⋙ QX) (ec : QZ ⋙ Lc ⟶ kc ⋙ QX)
  (mb : HZ ⋙ kb ≅ pb ⋙ HY) (ma : HY ⋙ ka ≅ pa ⋙ HX) (mc : HZ ⋙ kc ≅ pc ⋙ HX)
  (q : pb ⋙ pa ≅ pc) (n : kb ⋙ ka ≅ kc) (cc : Lb ⋙ La ⟶ Lc)

/-- If `x ≫ F.map i.hom = y` then `x = y ≫ F.map i.inv`. -/
private theorem eq_comp_map_inv_of_comp_map_hom {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) {a : E} {c d : C} (i : c ≅ d) (x : a ⟶ F.obj c) (y : a ⟶ F.obj d)
    (h : x ≫ F.map i.hom = y) : x = y ≫ F.map i.inv := by
  rw [← h]
  simp

/-- **Single-complex comparisons compose.**  Granted

* `hfac`, that the comparison `cc` of the composite of the two "derived" functors with the
  derived functor of the composite is compatible with the three comparisons `eb`, `ea`, `ec` and
  the identification `n` of the two "homotopy"-level composites, and
* `hsingle`, the coherence of the three single-functor identifications with `n` and the
  identification `q` of the two "abelian"-level composites,

the two routes from `La(Lb(PZ M))` to `PX(pa(pb M))` agree: one comparison after the other, or
`cc` followed by the comparison for the composite and the ordinary comparison `q`.

Five naturality squares and one cancellation; no hypothesis beyond the two displayed. -/
theorem singleComparison_comp
    (hfac : ∀ Ka : KZ, cc.app (QZ.obj Ka) ≫ ec.app Ka =
      La.map (eb.app Ka) ≫ ea.app (kb.obj Ka) ≫ QX.map (n.hom.app Ka))
    (hsingle : ∀ M : AZ, ka.map (mb.hom.app M) ≫ ma.hom.app (pb.obj M) ≫
        HX.map (q.hom.app M) =
      n.hom.app (HZ.obj M) ≫ mc.hom.app M)
    (M : AZ) :
    La.map (singleComparison HZ QZ sZ HY QY sY eb mb M) ≫
        singleComparison HY QY sY HX QX sX ea ma (pb.obj M) =
      cc.app (PZ.obj M) ≫ singleComparison HZ QZ sZ HX QX sX ec mc M ≫
        PX.map (q.inv.app M) := by
  -- the two inner identifications cancel
  have key : ∀ {W : DX} (z : La.obj ((HY ⋙ QY).obj (pb.obj M)) ⟶ W),
      La.map (sY.inv.app (pb.obj M)) ≫ La.map (sY.hom.app (pb.obj M)) ≫ z = z := by
    intro W z
    rw [← Category.assoc, ← La.map_comp, Iso.inv_hom_id_app, La.map_id, Category.id_comp]
  have hcancel : La.map (singleComparison HZ QZ sZ HY QY sY eb mb M) ≫
      singleComparison HY QY sY HX QX sX ea ma (pb.obj M) =
      La.map (Lb.map (sZ.hom.app M)) ≫ La.map (eb.app (HZ.obj M)) ≫
        La.map (QY.map (mb.hom.app M)) ≫ ea.app (HY.obj (pb.obj M)) ≫
          QX.map (ma.hom.app (pb.obj M)) ≫ sX.inv.app (pa.obj (pb.obj M)) := by
    simp only [singleComparison, Functor.map_comp, Category.assoc, key]
  rw [hcancel]
  -- naturality of `ea` at `mb.hom.app M`
  have h1 : La.map (QY.map (mb.hom.app M)) ≫ ea.app (HY.obj (pb.obj M)) =
      ea.app (kb.obj (HZ.obj M)) ≫ QX.map (ka.map (mb.hom.app M)) := ea.naturality _
  rw [reassoc_of% h1]
  -- the factorization `hfac`, solved for the two comparisons
  have h2 : La.map (eb.app (HZ.obj M)) ≫ ea.app (kb.obj (HZ.obj M)) =
      cc.app (QZ.obj (HZ.obj M)) ≫ ec.app (HZ.obj M) ≫ QX.map (n.inv.app (HZ.obj M)) := by
    rw [← Category.assoc]
    exact eq_comp_map_inv_of_comp_map_hom QX (n.app _) _ _
      ((Category.assoc _ _ _).trans (hfac _).symm)
  rw [reassoc_of% h2]
  -- the single-functor coherence, solved the same way
  have h3 : QX.map (n.inv.app (HZ.obj M)) ≫ QX.map (ka.map (mb.hom.app M)) ≫
        QX.map (ma.hom.app (pb.obj M)) =
      QX.map (mc.hom.app M) ≫ QX.map (HX.map (q.inv.app M)) := by
    simp only [← QX.map_comp]
    congr 1
    rw [eq_comp_map_inv_of_comp_map_hom HX (q.app _)
      (ka.map (mb.hom.app M) ≫ ma.hom.app (pb.obj M))
      (n.hom.app (HZ.obj M) ≫ mc.hom.app M)
      (by rw [Category.assoc]; exact hsingle M)]
    simp
  rw [reassoc_of% h3]
  -- naturality of `sX.inv` at `q.inv.app M`
  have h4 : QX.map (HX.map (q.inv.app M)) ≫ sX.inv.app (pa.obj (pb.obj M)) =
      sX.inv.app (pc.obj M) ≫ PX.map (q.inv.app M) := sX.inv.naturality _
  -- naturality of `cc` at `sZ.hom.app M`
  have h5 : La.map (Lb.map (sZ.hom.app M)) ≫ cc.app (QZ.obj (HZ.obj M)) =
      cc.app (PZ.obj M) ≫ Lc.map (sZ.hom.app M) := cc.naturality _
  simp only [singleComparison, Category.assoc]
  rw [h4, reassoc_of% h5]

end Comp

end Stacks.SingleComparison

/-! ### The geometric comparison -/

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open DerivedCategory

universe u

variable {X Y Z : RingedSpace.{u, u}}

attribute [local instance] HasDerivedCategory.standard

/-- `derivedToOrdinaryPullbackSingle` is an instance of the abstract single-complex comparison:
the `Q ⋙ L ⟶ k ⋙ Q'` is the derived-pullback comparison of [Stacks, Tag 06YJ], the two
identifications of the single functors are `DerivedCategory.singleFunctorIsoCompQh`, and the
`H ⋙ k ≅ p ⋙ H'` is `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor`.

True by definition; it is recorded so that the formal core can be instantiated. -/
theorem derivedToOrdinaryPullbackSingle_eq_singleComparison
    (f : X ⟶ Y) (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    derivedToOrdinaryPullbackSingle f M d =
      Stacks.SingleComparison.singleComparison
        (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d)
        DerivedCategory.Qh
        (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d)
        (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d)
        DerivedCategory.Qh
        (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
        (Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d) M :=
  rfl

/-! ### The two hypotheses, concretely -/

/-- **The single-complex identification of an additive functor is multiplicative**, on cochain
complexes.  For additive functors `F`, `G`, `H` and an isomorphism `e : F ⋙ G ≅ H`, the two
routes from `G(F(M[-j]))` to `H(M)[-j]` agree.

Checked degreewise: off `j` both sides land in a zero object, and in degree `j` the statement is
the naturality of `e` at `HomologicalComplex.singleObjXSelf`. -/
theorem singleMapHomologicalComplex_comp {W₁ W₂ W₃ : Type*} [Category W₁] [Category W₂]
    [Category W₃] [Preadditive W₁] [Preadditive W₂] [Preadditive W₃]
    [HasZeroObject W₁] [HasZeroObject W₂] [HasZeroObject W₃]
    {ι : Type*} (c : ComplexShape ι) [DecidableEq ι] (j : ι)
    (F : W₁ ⥤ W₂) (G : W₂ ⥤ W₃) (H : W₁ ⥤ W₃) [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) (M : W₁) :
    (G.mapHomologicalComplex c).map ((singleMapHomologicalComplex F c j).hom.app M) ≫
        (singleMapHomologicalComplex G c j).hom.app (F.obj M) ≫
        (single W₃ c j).map (e.hom.app M) =
      (Functor.mapHomologicalComplexCompIso e c).hom.app ((single W₁ c j).obj M) ≫
        (singleMapHomologicalComplex H c j).hom.app M := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h : i = j
  · subst h
    have hnat : G.map (F.map (singleObjXSelf c i M).hom) ≫ e.hom.app M =
        e.hom.app (((single W₁ c i).obj M).X i) ≫ H.map (singleObjXSelf c i M).hom :=
      e.hom.naturality (singleObjXSelf c i M).hom
    simp only [Functor.comp_obj, comp_f, Functor.mapHomologicalComplex_map_f,
      singleMapHomologicalComplex_hom_app_self, single_map_f_self,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.map_comp,
      Category.assoc]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc (G.map (singleObjXSelf c i (F.obj M)).inv), ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hnat]
  · exact (isZero_single_obj_X c j (H.obj M) i h).eq_of_tgt _ _

/-- **The hypothesis `hsingle` for degreewise pullback.**  The single-complex identification of
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is compatible with the composition
isomorphism `Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso` of the two
degreewise pullbacks and with `Stacks.DerivedPullback.Composition.modulePullbackComp`.

Everything in sight is the image under `HomotopyCategory.quotient` of a map of cochain
complexes, so this is `singleMapHomologicalComplex_comp`. -/
theorem mapHomotopyCategorySingleFunctor_comp (f : X ⟶ Y) (g : Y ⟶ Z) (d : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategorySingleFunctor (modulePullback g) d).hom.app M) ≫
        (Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d).hom.app
          ((modulePullback g).obj M) ≫
        (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M) =
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing Z)) d).obj M) ≫
        (Functor.mapHomotopyCategorySingleFunctor (modulePullback (f ≫ g)) d).hom.app M := by
  have hgen := singleMapHomologicalComplex_comp (ComplexShape.up ℤ) d
    (modulePullback g) (modulePullback f) (modulePullback (f ≫ g))
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g) M
  have h := congrArg
    (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)).map hgen
  simp only [Functor.map_comp] at h
  rw [mapHomotopyCategorySingleFunctor_hom_app_eq, mapHomotopyCategorySingleFunctor_hom_app_eq,
    mapHomotopyCategorySingleFunctor_hom_app_eq]
  exact h

/-- **The hypothesis `hfac`.**  The canonical comparison of [Stacks, Tag 0D5S], followed by the
derived-pullback comparison for the composite, is the two comparisons in turn and the
composition isomorphism of the degreewise pullbacks.

This is the universal property of
`Stacks.DerivedPullback.Composition.derivedPullbackCompComparison`, which is a
`CategoryTheory.Functor.leftDerivedLift`. -/
theorem derivedPullbackCompComparisonCanonical_fac (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical f g).app
          (DerivedCategory.Qh.obj K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
          (f ≫ g)).app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g).app
            K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g).hom.app K) :=
  (Functor.leftDerived_fac_app
      (LF := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g))
      (α := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
      (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ))
      (G := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (β := Stacks.DerivedPullback.Composition.derivedPullbackCompCounit f g
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g))
      (X := K)).trans
    (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app f g _ _ _ _ K)

/-! ### The theorem -/

/-- **`derivedToOrdinaryPullbackSingle` is multiplicative.**  For `a : X ⟶ Y` and `b : Y ⟶ Z` the
comparison `Lb^*(M[-d]) ⟶ (b^*M)[-d]` followed by `La^*` and then the comparison for `a`, equals
the composition isomorphism of [Stacks, Tag 0D5S] followed by the comparison for `a ≫ b` and the
ordinary pullback-composition isomorphism.

`Stacks.SingleComparison.singleComparison_comp` at the two hypotheses just proved. -/
theorem derivedToOrdinaryPullbackSingle_comp (f : X ⟶ Y) (g : Y ⟶ Z) (d : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (derivedToOrdinaryPullbackSingle g M d) ≫
        derivedToOrdinaryPullbackSingle f ((modulePullback g).obj M) d =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle (f ≫ g) M d ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).inv.app M) :=
  Stacks.SingleComparison.singleComparison_comp
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Z)) d)
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d)
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
    (Functor.mapHomotopyCategorySingleFunctor (modulePullback g) d)
    (Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d)
    (Functor.mapHomotopyCategorySingleFunctor (modulePullback (f ≫ g)) d)
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g)
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical f g)
    (derivedPullbackCompComparisonCanonical_fac f g)
    (mapHomotopyCategorySingleFunctor_comp f g d) M

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
