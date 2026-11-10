module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDatumSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairChartConnect
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumPairReading

/-!
# The naturality of the member-site comparison on a chart of a pairwise fibre product

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X` whose charts are cover dense in the small étale site of `X`, and let `D` be
a descent datum relative to that family. Let `M` be an `𝒪_X`-module and `β` an isomorphism of
the restriction of `M` to the site of the charts of the members with the sheaf of modules
`.memberSheafOfLaws` that `D` defines on that site.

Then `β` is natural across a chart `Z` of a pairwise fibre product `Y i ×_X Y j`: restricting a
section of `M` along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of `Z` and comparing it to a
section of `D.F j` is comparing it to a section of `D.F i` and transporting it by the pairwise
isomorphism `D.transition i j` of the datum, read over `Z`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberArrow`: the arrow of the site of the charts
  of the members carried by a morphism of the induced charts of `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairConnectHom`: the arrow of that site carried
  by the connecting morphism of a chart of `Y i ×_X Y j`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberNaturality_on_pairChart`: the comparison
  is natural across a chart of a pairwise fibre product.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberNaturality_of_eq`: the naturality square
  of the comparison, with the arrow of the site and the sections carried as variables.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberSheafOfLaws_val_map_of_test` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.heq_memberSheafOfLaws_val_map_of_test`: the
  restriction map of the sheaf of modules of the datum along an arrow of the site, read as the
  pairwise isomorphism of the datum over the chart of `Y i ×_X Y j` that a test space presenting
  the arrow induces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The arrow of the member site a chart of a pairwise fibre product induces -/

/-- The arrow of the site of the charts of the members carried by a morphism of the induced
charts of `X`. -/
def memberArrow {i j : I} (V : SmallEtale B S hS (Yi i).1)
    (V' : SmallEtale B S hS (Yi j).1)
    (k : (smallEtalePostcomp B S hS (f j) (hf j)).obj V' ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj V) :
    memberPair B S hS Yi f hf j V' ⟶ memberPair B S hS Yi f hf i V :=
  InducedCategory.homMk k

/-- The arrow of the site of the charts of the members carried by the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of a chart of a pairwise fibre
product. -/
def pairConnectHom {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    memberPair B S hS Yi f hf j
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z) ⟶
      memberPair B S hS Yi f hf i
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z) :=
  memberArrow B S hS Yi f hf _ _ (pairChartConnect B S hS Yi f hf Z)

/-! ### The chart and the morphism of charts the connecting arrow induces -/

/-- The chart of the first member that the connecting arrow of a chart of a pairwise fibre product
induces is the chart that the first projection of that chart induces. -/
theorem memberTransitionChart_pairChartConnect {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    memberTransitionChart B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z) =
      (smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z :=
  smallEtalePostcomp_obj_congr B S hS
    (isEtale_memberChartMap B S hS Yi f hf _ _ (pairChartConnect B S hS Yi f hf Z))
    (isEtale_comp B S hS (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)
      (isEtale_pairFst B S hS Yi f hf i j))
    (chartToSpace_comp_pairFst B S hS Yi f hf Z).symm
    (chartSpaceIdChart B S hS (pair B S hS Yi f i j) Z)

/-- The morphism of charts that the connecting arrow of a chart of a pairwise fibre product
induces is, heterogeneously, the identity. -/
theorem heq_memberTransitionHom_pairChartConnect {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    HEq (memberTransitionHom B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z))
      (𝟙 ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) :=
  heq_hom_of_heq_left B S hS _ _ (memberTransitionChart_pairChartConnect B S hS Yi f hf Z) _ _
    (heq_of_eq ((memberTransitionHom_hom_left B S hS Yi f hf _ _
        (pairChartConnect B S hS Yi f hf Z)).trans
      (pairChartConnect_hom_left B S hS Yi f hf Z)))

/-- Restriction of a section along the morphism of charts that the connecting arrow induces
leaves that section unchanged, heterogeneously. -/
theorem heq_val_map_memberTransitionHom_pairChartConnect (D : DescentDatum B S hS Yi f)
    {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (z : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS
      (pairFst B S hS Yi f i j) (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) :
    HEq (ModuleCat.Hom.hom ((D.F i).val.map
      (memberTransitionHom B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z)).op) z) z :=
  (val_map_heq_of_heq B S hS (D.F i) _ _
      (memberTransitionChart_pairChartConnect B S hS Yi f hf Z) _ (𝟙 _)
      (heq_memberTransitionHom_pairChartConnect B S hS Yi f hf Z) z).trans
    (heq_of_eq (val_map_eq_id_hom_apply B S hS (D.F i) _ rfl z))

/-! ### The test space of a transition may be replaced by an equal one -/

/-- The transition of a descent datum read at two equal test morphisms agrees. -/
theorem transitionHom_congr_test (D : DescentDatum B S hS Yi f) {i j : I}
    {T : AlgebraicSpaces B S hS} (v w : T ⟶ pair B S hS Yi f i j) (hvw : v = w)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : w ≫ pairFst B S hS Yi f i j = vi) (hj' : w ≫ pairSnd B S hS Yi f i j = vj) :
    transitionHom B S hS Yi f D i j v vi vj hi hj =
      transitionHom B S hS Yi f D i j w vi vj hi' hj' := by
  subst hvw
  rfl

/-- The reading of the transition of a descent datum over a chart is unchanged when the test
morphism is replaced by an equal one. -/
theorem transitionHom_val_app_congr_test (D : DescentDatum B S hS Yi f) {i j : I}
    {T : AlgebraicSpaces B S hS} (v w : T ⟶ pair B S hS Yi f i j) (hvw : v = w)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : w ≫ pairFst B S hS Yi f i j = vi) (hj' : w ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (x : ((modulePullback B S hS vi).obj (D.F i)).val.obj (Opposite.op U)) :
    (transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U) x =
      (transitionHom B S hS Yi f D i j w vi vj hi' hj').val.app (Opposite.op U) x :=
  congrArg (fun θ => θ.val.app (Opposite.op U) x)
    (transitionHom_congr_test B S hS Yi f D v w hvw vi vj hi hj hi' hj')

/-! ### The two retypings of the reading at a test space are identities -/

/-- The retyping of a section of the source component module across the two spellings of its
chart is, heterogeneously, the identity. -/
theorem heq_testChartSectFst (D : DescentDatum B S hS Yi f) {i j : I}
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (vi : T ⟶ Yi i) (hvi : IsEtale B S hS vi.hom)
    (hi : w ≫ pairFst B S hS Yi f i j = vi) (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    HEq (testChartSectFst B S hS Yi f D ha w hw vi hvi hi U s) s := by
  subst hi
  exact heq_of_eq (testChartSectFst_rfl B S hS Yi f D ha w hw hvi U s)

/-- The retyping of a section of the target component module across the two spellings of its
chart is, heterogeneously, the identity. -/
theorem heq_testChartSectSnd (D : DescentDatum B S hS Yi f) {i j : I}
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (w : T ⟶ pair B S hS Yi f i j) (hw : IsEtale B S hS w.hom)
    (vj : T ⟶ Yi j) (hvj : IsEtale B S hS vj.hom)
    (hj : w ≫ pairSnd B S hS Yi f i j = vj) (U : SmallEtale B S hS T.1)
    (t : (D.F j).val.obj (Opposite.op ((smallEtalePostcomp B S hS
      (pairSnd B S hS Yi f i j) hb).obj ((smallEtalePostcomp B S hS w hw).obj U)))) :
    HEq (testChartSectSnd B S hS Yi f D hb w hw vj hvj hj U t) t := by
  subst hj
  exact heq_of_eq (testChartSectSnd_rfl B S hS Yi f D hb w hw hvj U t)

/-! ### The reading at a test space, after the test space has been replaced -/

/-- The reading of the transition of a descent datum over a chart of a test space, with the test
morphism replaced by an equal one, is the reading of the pairwise isomorphism of the datum over
the chart of the pairwise fibre product that the chart induces. -/
theorem transitionHom_reading_of_test_congr (D : DescentDatum B S hS Yi f) {i j : I}
    (ha : IsEtale B S hS (pairFst B S hS Yi f i j).hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f i j).hom)
    {T : AlgebraicSpaces B S hS} (v w : T ⟶ pair B S hS Yi f i j) (hvw : v = w)
    (hw : IsEtale B S hS w.hom) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : w ≫ pairFst B S hS Yi f i j = vi) (hj' : w ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (Opposite.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    etaleSect B S hS vj hvj (D.F j) U
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (Opposite.op U)
          (etaleSectInv B S hS vi hvi (D.F i) U s)) =
      testChartSectSnd B S hS Yi f D hb w hw vj hvj hj' U
        (etaleSect B S hS (pairSnd B S hS Yi f i j) hb (D.F j)
          ((smallEtalePostcomp B S hS w hw).obj U)
          ((D.transition i j).hom.val.app
            (Opposite.op ((smallEtalePostcomp B S hS w hw).obj U))
            (etaleSectInv B S hS (pairFst B S hS Yi f i j) ha (D.F i)
              ((smallEtalePostcomp B S hS w hw).obj U)
              (testChartSectFst B S hS Yi f D ha w hw vi hvi hi' U s)))) :=
  (apply_congr
      (transitionHom_val_app_congr_test B S hS Yi f D v w hvw vi vj hi hj hi' hj' U
        (etaleSectInv B S hS vi hvi (D.F i) U s))
      (etaleSect B S hS vj hvj (D.F j) U)).trans
    (transitionHom_reading_of_test B S hS Yi f D ha hb w hw vi vj hvi hvj hi' hj' U s)

/-- The structure morphism of a chart of the pairwise fibre product followed by the second
projection, with the self leg spelled as the one of an identity arrow of the site of the charts of
the members. -/
theorem chartToSpace_comp_pairSnd' {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    chartToSpace B S hS (pair B S hS Yi f i j) Z ≫ pairSnd B S hS Yi f i j =
      memberChartMap B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (memberHom B S hS Yi f hf (𝟙 (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))).unop) :=
  chartToSpace_comp_pairSnd B S hS Yi f hf Z

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

variable (D : DescentDatum B S hS Yi f)
  (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
    (fun _ => inferInstance)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hM : MemberModLaws B S hS Yi f hf (memberDatumObj B S hS Yi f hf D)
      (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hsh : Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
      (memberFunctorOfLawsV B S hS Yi f hf hL))
  (M : Modules.{u, u} B S hS X.1 X.2)
  (β : (memberRestriction B S hS Yi f hf).obj M ≅
    memberSheafOfLaws B S hS Yi f hf hL hM hsh)

/-- Restriction of a section of an `𝒪_X`-module, read on the charts of the members, along the
connecting arrow is its restriction in the module along the connecting morphism of charts
of `X`. -/
theorem memberRestriction_val_map_pairConnectHom {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    ((memberRestriction B S hS Yi f hf).obj M).val.map
        (pairConnectHom B S hS Yi f hf Z).op σ =
      M.val.map (pairChartConnect B S hS Yi f hf Z).op σ :=
  rfl

/-- On a section, the restriction map of the sheaf of modules built from the four laws is the
restriction map of the presheaf of abelian groups built from the three additive ones. -/
theorem memberSheafOfLaws_val_map_eq_memberFunctorOfLawsV
    (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g m =
      (memberFunctorOfLawsV B S hS Yi f hf hL).map g m :=
  rfl

/-- The restriction map of the sheaf of modules of a descent datum, read on a section, is the
composite of its transition factor and its restriction factor. -/
theorem memberSheafOfLaws_val_map_apply (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g m =
      (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
        (memberDatumAbRestrFn B S hS Yi f hf D p q g m) :=
  (memberSheafOfLaws_val_map_eq_memberFunctorOfLawsV B S hS Yi f hf D hL hM hsh p q g m).trans
    (memberDatumAbFunctor_map_apply B S hS Yi f hf D hL p q g m)

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)] in
/-- The transition factor of the restriction map, read on a section, is the reading of the
transition at the test space of the arrow. -/
theorem memberDatumAbTransHom_val_app_reading (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (y : ↥(((etaleModulePullback.{u, u} B S hS
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
        (memberHom B S hS Yi f hf g.unop))).obj (D.F p.unop.1)).val.obj
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))) :
    (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
        (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)) y =
      etaleSect B S hS
          (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (D.F q.unop.1) (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
        ((transitionHom B S hS Yi f D p.unop.1 q.unop.1
            (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
              (memberHom B S hS Yi f hf (𝟙 q).unop))
            (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop)
              (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
          (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
          (etaleSectInv B S hS
            (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (D.F p.unop.1) (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2) y)) :=
  (memberDatumAbTransHom_val_app_apply B S hS Yi f hf D p q g y).trans
    (transitionEtaleForm_val_app_apply B S hS Yi f D p.unop.1 q.unop.1
      (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
      (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
        (memberHom B S hS Yi f hf (𝟙 q).unop))
      (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
        (memberHom B S hS Yi f hf g.unop))
      (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
        (memberHom B S hS Yi f hf (𝟙 q).unop))
      (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
        (memberHom B S hS Yi f hf g.unop))
      (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
        (memberHom B S hS Yi f hf g.unop) (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)
      (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2) y)

/-- The restriction map of the sheaf of modules of a descent datum along an arrow of the site,
read on a section, is the reading of the transition at the test space of that arrow. -/
theorem memberSheafOfLaws_val_map_reading (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g m =
      etaleSect B S hS
          (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
            (memberHom B S hS Yi f hf (𝟙 q).unop))
          (D.F q.unop.1) (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
        ((transitionHom B S hS Yi f D p.unop.1 q.unop.1
            (memberChartPair B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
              (memberHom B S hS Yi f hf (𝟙 q).unop))
            (memberChartPair_fst B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (memberChartPair_snd' B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop)
              (memberHom B S hS Yi f hf (𝟙 q).unop) rfl)).val.app
          (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
          (etaleSectInv B S hS
            (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
              (memberHom B S hS Yi f hf g.unop))
            (D.F p.unop.1) (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
            (memberDatumAbRestrFn B S hS Yi f hf D p q g m))) :=
  (memberSheafOfLaws_val_map_apply B S hS Yi f hf D hL hM hsh p q g m).trans
    (memberDatumAbTransHom_val_app_reading B S hS Yi f hf D p q g
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m))

/-- The restriction factor of the restriction map, at the connecting arrow of a chart of a
pairwise fibre product, leaves a section unchanged, heterogeneously. -/
theorem heq_memberDatumAbRestrFn_pairConnectHom {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (τ : ↥(memberDatumObj B S hS Yi f hf D (Opposite.op (memberPair B S hS Yi f hf i
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z))))) :
    HEq (memberDatumAbRestrFn B S hS Yi f hf D _ _
      (pairConnectHom B S hS Yi f hf Z).op τ) τ :=
  (heq_of_eq (memberDatumAbRestrFn_apply_of_eq B S hS Yi f hf D _ _
      (pairConnectHom B S hS Yi f hf Z).op τ τ rfl)).trans
    (heq_val_map_memberTransitionHom_pairChartConnect B S hS Yi f hf D Z τ)

/-- The restriction map of the sheaf of modules of a descent datum along an arrow of the site,
read on a section, is the reading of the pairwise isomorphism of the datum over the chart of the
pairwise fibre product that a test space presenting the arrow induces. -/
theorem memberSheafOfLaws_val_map_of_test (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (ha : IsEtale B S hS (pairFst B S hS Yi f p.unop.1 q.unop.1).hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f p.unop.1 q.unop.1).hom)
    (w : chartSpace B S hS (Yi q.unop.1) q.unop.2 ⟶ pair B S hS Yi f p.unop.1 q.unop.1)
    (hvw : memberChartPair B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) = w) (hw : IsEtale B S hS w.hom)
    (hi' : w ≫ (pairFst B S hS Yi f p.unop.1 q.unop.1) =
      memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
    (hj' : w ≫ (pairSnd B S hS Yi f p.unop.1 q.unop.1) =
      memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g m =
      testChartSectSnd B S hS Yi f D
        hb
        w
        hw
        (memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
          (memberHom B S hS Yi f hf (𝟙 q).unop))
        (isEtale_memberChartMap B S hS Yi f hf q.unop.2 q.unop.2
          (memberHom B S hS Yi f hf (𝟙 q).unop))
        hj'
        (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
        (etaleSect B S hS
          (pairSnd B S hS Yi f p.unop.1 q.unop.1)
          hb
          (D.F q.unop.1)
          ((smallEtalePostcomp B S hS w hw).obj
            (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
          ((D.transition p.unop.1 q.unop.1).hom.val.app
            (Opposite.op ((smallEtalePostcomp B S hS w hw).obj
              (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))
            (etaleSectInv B S hS
              (pairFst B S hS Yi f p.unop.1 q.unop.1)
              ha
              (D.F p.unop.1)
              ((smallEtalePostcomp B S hS w hw).obj
                (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
              (testChartSectFst B S hS Yi f D
                ha
                w
                hw
                (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
                  (memberHom B S hS Yi f hf g.unop))
                (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
                  (memberHom B S hS Yi f hf g.unop))
                hi'
                (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
                (memberDatumAbRestrFn B S hS Yi f hf D p q g m))))) :=
  (memberSheafOfLaws_val_map_reading B S hS Yi f hf D hL hM hsh p q g m).trans
    (transitionHom_reading_of_test_congr B S hS Yi f D ha hb _ w hvw hw _ _ _ _ _ _ hi' hj' _ _)

/-- The restriction map of the sheaf of modules of a descent datum along an arrow of the site,
read on a section, is heterogeneously the reading of the pairwise isomorphism of the datum over the
chart of the pairwise fibre product that a test space presenting the arrow induces, with the
retyping of the target section removed. -/
theorem heq_memberSheafOfLaws_val_map_of_test (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (ha : IsEtale B S hS (pairFst B S hS Yi f p.unop.1 q.unop.1).hom)
    (hb : IsEtale B S hS (pairSnd B S hS Yi f p.unop.1 q.unop.1).hom)
    (w : chartSpace B S hS (Yi q.unop.1) q.unop.2 ⟶ pair B S hS Yi f p.unop.1 q.unop.1)
    (hvw : memberChartPair B S hS Yi f hf p.unop.2 q.unop.2
      (memberHom B S hS Yi f hf g.unop) = w) (hw : IsEtale B S hS w.hom)
    (hi' : w ≫ (pairFst B S hS Yi f p.unop.1 q.unop.1) =
      memberChartMap B S hS Yi f hf p.unop.2 q.unop.2 (memberHom B S hS Yi f hf g.unop))
    (hj' : w ≫ (pairSnd B S hS Yi f p.unop.1 q.unop.1) =
      memberChartMap B S hS Yi f hf q.unop.2 q.unop.2 (memberHom B S hS Yi f hf (𝟙 q).unop))
    (m : ↥(memberDatumObj B S hS Yi f hf D p)) :
    HEq ((memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g m)
      (etaleSect B S hS (pairSnd B S hS Yi f p.unop.1 q.unop.1) hb (D.F q.unop.1)
         ((smallEtalePostcomp B S hS w hw).obj
           (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
         ((D.transition p.unop.1 q.unop.1).hom.val.app
           (Opposite.op ((smallEtalePostcomp B S hS w hw).obj
             (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)))
           (etaleSectInv B S hS (pairFst B S hS Yi f p.unop.1 q.unop.1) ha (D.F p.unop.1)
             ((smallEtalePostcomp B S hS w hw).obj
               (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
             (testChartSectFst B S hS Yi f D
               ha
               w
               hw
               (memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
                 (memberHom B S hS Yi f hf g.unop))
               (isEtale_memberChartMap B S hS Yi f hf p.unop.2 q.unop.2
                 (memberHom B S hS Yi f hf g.unop))
               hi'
               (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2)
               (memberDatumAbRestrFn B S hS Yi f hf D p q g m))))) :=
  (heq_of_eq (memberSheafOfLaws_val_map_of_test B S hS Yi f hf D hL hM hsh p q g
      ha hb w hvw hw hi' hj' m)).trans
    (heq_testChartSectSnd B S hS Yi f D hb w hw _ _ hj' _ _)

/-! ### The naturality of the comparison on a chart of a pairwise fibre product -/

/-- The retyping of the source section at the test space of the connecting arrow is the
identity. -/
theorem testChartSectFst_pairConnectHom {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (τ : ↥(memberDatumObj B S hS Yi f hf D (Opposite.op (memberPair B S hS Yi f hf i
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z))))) :
    testChartSectFst B S hS Yi f D (isEtale_pairFst B S hS Yi f hf i j)
        (chartToSpace B S hS (pair B S hS Yi f i j) Z)
        (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)
        (memberChartMap B S hS Yi f hf
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
          (pairChartConnect B S hS Yi f hf Z))
        (isEtale_memberChartMap B S hS Yi f hf _ _ (pairChartConnect B S hS Yi f hf Z))
        (chartToSpace_comp_pairFst B S hS Yi f hf Z)
        (chartSpaceIdChart B S hS (Yi j)
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
        (memberDatumAbRestrFn B S hS Yi f hf D _ _
          (pairConnectHom B S hS Yi f hf Z).op τ) = τ :=
  eq_of_heq ((heq_testChartSectFst B S hS Yi f D (isEtale_pairFst B S hS Yi f hf i j)
        (chartToSpace B S hS (pair B S hS Yi f i j) Z)
        (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z) _ _
        (chartToSpace_comp_pairFst B S hS Yi f hf Z) _ _).trans
    (heq_memberDatumAbRestrFn_pairConnectHom B S hS Yi f hf D Z τ))

omit [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)] in
/-- The reading of the pairwise isomorphism over a chart of the fibre product is unchanged when
the member and the chart are read off the object of the site. -/
theorem etaleSect_transition_congr_memberPair {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (x : ((etaleModulePullback.{u, u} B S hS (pairFst B S hS Yi f
      (Opposite.op (memberPair B S hS Yi f hf i
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1
      (Opposite.op (memberPair B S hS Yi f hf j
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
      (isEtale_pairFst B S hS Yi f hf i j)).obj
      (D.F (Opposite.op (memberPair B S hS Yi f hf i
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1)).val.obj (Opposite.op
      ((smallEtalePostcomp B S hS (chartToSpace B S hS (pair B S hS Yi f i j) Z)
          (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)).obj
        (chartSpaceIdChart B S hS (Yi (Opposite.op (memberPair B S hS Yi f hf j
            ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
              (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
          (Opposite.op (memberPair B S hS Yi f hf j
            ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
              (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2)))) :
    etaleSect B S hS (pairSnd B S hS Yi f (Opposite.op (memberPair B S hS Yi f hf i
            ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1
          (Opposite.op (memberPair B S hS Yi f hf j
            ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
              (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
        (isEtale_pairSnd B S hS Yi f hf i j)
        (D.F (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
        ((smallEtalePostcomp B S hS (chartToSpace B S hS (pair B S hS Yi f i j) Z)
            (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)).obj
          (chartSpaceIdChart B S hS (Yi (Opposite.op (memberPair B S hS Yi f hf j
              ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
            (Opposite.op (memberPair B S hS Yi f hf j
              ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2))
        ((D.transition (Opposite.op (memberPair B S hS Yi f hf i
              ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1
            (Opposite.op (memberPair B S hS Yi f hf j
              ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1).hom.val.app (Opposite.op
          ((smallEtalePostcomp B S hS (chartToSpace B S hS (pair B S hS Yi f i j) Z)
              (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)).obj
            (chartSpaceIdChart B S hS (Yi (Opposite.op (memberPair B S hS Yi f hf j
                ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                  (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
              (Opposite.op (memberPair B S hS Yi f hf j
                ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                  (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2)))
          (etaleSectInv B S hS (pairFst B S hS Yi f (Opposite.op (memberPair B S hS Yi f hf i
              ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1
            (Opposite.op (memberPair B S hS Yi f hf j
              ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
            (isEtale_pairFst B S hS Yi f hf i j)
            (D.F (Opposite.op (memberPair B S hS Yi f hf i
              ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.1)
            ((smallEtalePostcomp B S hS (chartToSpace B S hS (pair B S hS Yi f i j) Z)
                (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)).obj
              (chartSpaceIdChart B S hS (Yi (Opposite.op (memberPair B S hS Yi f hf j
                  ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                    (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
                (Opposite.op (memberPair B S hS Yi f hf j
                  ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
                    (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2)) x)) =
      etaleSect B S hS (pairSnd B S hS Yi f i j) (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
        ((D.transition i j).hom.val.app (Opposite.op Z)
          (etaleSectInv B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z x)) :=
  rfl

/-- The retyping of the source section at the test space is unchanged when the members and the
charts are read off the two objects of the site. -/
theorem testChartSectFst_congr_memberPair {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    testChartSectFst B S hS Yi f D
      (isEtale_pairFst B S hS Yi f hf i j)
      (chartToSpace B S hS (pair B S hS Yi f i j) Z)
      (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)
      (memberChartMap B S hS Yi f hf
        (Opposite.op (memberPair B S hS Yi f hf i
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.2
        (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2
        (memberHom B S hS Yi f hf (pairConnectHom B S hS Yi f hf Z).op.unop))
      (isEtale_memberChartMap B S hS Yi f hf
        (Opposite.op (memberPair B S hS Yi f hf i
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z))).unop.2
        (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2
        (memberHom B S hS Yi f hf (pairConnectHom B S hS Yi f hf Z).op.unop))
      (chartToSpace_comp_pairFst B S hS Yi f hf Z)
      (chartSpaceIdChart B S hS (Yi (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.1)
        (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))).unop.2)
      (memberDatumAbRestrFn B S hS Yi f hf D (Opposite.op (memberPair B S hS Yi f hf i
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))
        (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))
        ((pairConnectHom B S hS Yi f hf Z).op)
        (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ)) =
      testChartSectFst B S hS Yi f D
        (isEtale_pairFst B S hS Yi f hf i j)
        (chartToSpace B S hS (pair B S hS Yi f i j) Z)
        (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)
        (memberChartMap B S hS Yi f hf
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z) (pairChartConnect B S hS Yi f hf Z))
        (isEtale_memberChartMap B S hS Yi f hf _ _ (pairChartConnect B S hS Yi f hf Z))
        (chartToSpace_comp_pairFst B S hS Yi f hf Z)
        (chartSpaceIdChart B S hS (Yi j)
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
        (memberDatumAbRestrFn B S hS Yi f hf D _ _
          (pairConnectHom B S hS Yi f hf Z).op
          (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
            ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ)) :=
  rfl

/-- The naturality square of the comparison `β` of an `𝒪_X`-module with the sheaf of modules of
a descent datum on the charts of the members, read on a section, with the two restrictions of the
source section given as variables `y` and `z`. -/
theorem memberNaturality_of_eq (p q : (MemberSite B S hS Yi f hf)ᵒᵖ) (g : p ⟶ q)
    (x : ((memberRestriction B S hS Yi f hf).obj M).val.obj p)
    (y : ((memberRestriction B S hS Yi f hf).obj M).val.obj q)
    (hy : ((memberRestriction B S hS Yi f hf).obj M).val.map g x = y)
    (z : (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.obj p)
    (hz : β.hom.val.app p x = z) :
    β.hom.val.app q y =
      (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map g z := by
  subst hy hz
  exact PresheafOfModules.naturality_apply β.hom.val g x

/-- The naturality of the comparison at the connecting arrow of a chart of a pairwise fibre
product, read as the pairwise isomorphism of the datum over that chart, heterogeneously. -/
theorem heq_memberNaturality_on_pairChart (i j : I)
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    HEq (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))
        (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ))
      (etaleSect B S hS (pairSnd B S hS Yi f i j) (isEtale_pairSnd B S hS Yi f hf i j)
        (D.F j) Z
        ((D.transition i j).hom.val.app (Opposite.op Z)
          (etaleSectInv B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
            (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
              ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ)))) := by
  refine HEq.trans (heq_of_eq (memberNaturality_of_eq B S hS Yi f hf D hL hM hsh M β
    (Opposite.op (memberPair B S hS Yi f hf i
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))
    (Opposite.op (memberPair B S hS Yi f hf j
      ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))
    ((pairConnectHom B S hS Yi f hf Z).op) σ _
    (memberRestriction_val_map_pairConnectHom B S hS Yi f hf M Z σ)
    (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ) rfl)) ?_
  refine HEq.trans (heq_memberSheafOfLaws_val_map_of_test B S hS Yi f hf D hL hM hsh
    (Opposite.op (memberPair B S hS Yi f hf i
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))
    (Opposite.op (memberPair B S hS Yi f hf j
      ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))
    ((pairConnectHom B S hS Yi f hf Z).op) (isEtale_pairFst B S hS Yi f hf i j)
    (isEtale_pairSnd B S hS Yi f hf i j)
    (chartToSpace B S hS (pair B S hS Yi f i j) Z)
    (memberChartPair_pairChartConnect B S hS Yi f hf Z)
    (isEtale_chartToSpace B S hS (pair B S hS Yi f i j) Z)
    (chartToSpace_comp_pairFst B S hS Yi f hf Z)
    (chartToSpace_comp_pairSnd' B S hS Yi f hf Z) _) ?_
  exact heq_of_eq ((etaleSect_transition_congr_memberPair B S hS Yi f hf D Z _).trans
    (apply_congr
      ((testChartSectFst_congr_memberPair B S hS Yi f hf D hL hM hsh M β Z σ).trans
        (testChartSectFst_pairConnectHom B S hS Yi f hf D Z
          (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
            ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ)))
      (fun t => etaleSect B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
        ((D.transition i j).hom.val.app (Opposite.op Z)
          (etaleSectInv B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z t)))))

/-- The comparison `β` of an `𝒪_X`-module `M` with the sheaf of modules of a descent datum on the
charts of the members is natural across a chart `Z` of `Y i ×_X Y j`: restricting a section of
`M` over the chart of `X` that the first projection of `Z` induces along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` and then comparing it to a
section of `D.F j` is the same as comparing it to a section of `D.F i` and applying the pairwise
isomorphism `D.transition i j` of the datum over `Z`. -/
theorem memberNaturality_on_pairChart (i j : I)
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf j
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)))
        (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
      etaleSect B S hS (pairSnd B S hS Yi f i j) (isEtale_pairSnd B S hS Yi f hf i j)
        (D.F j) Z
        ((D.transition i j).hom.val.app (Opposite.op Z)
          (etaleSectInv B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
            (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i
              ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z))) σ))) :=
  eq_of_heq (heq_memberNaturality_on_pairChart B S hS Yi f hf D hL hM hsh M β i j Z σ)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
