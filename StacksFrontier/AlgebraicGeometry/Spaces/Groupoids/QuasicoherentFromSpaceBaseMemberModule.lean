module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMemberSheafCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseLegSect

/-!
# A quasi-coherent module on a kernel-pair groupoid, read on the site of the charts of `φ`

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be an étale morphism
with `R = U ×_X U` and `t`, `s` the two projections, as in Stacks 03M3. The charts of `U`, with
the morphisms of the *induced* charts of `X`, form the site
`AlgebraicGeometry.Space.QuasiCoherentDescent.SingleSite`.

A quasi-coherent module `(ℱ, α)` on the groupoid gives a presheaf of abelian groups on that site:
its sections over a chart `V` of `U` are the sections of `ℱ` over `V`, and its restriction along a
morphism `k` of the induced charts of `X` is restriction along the comparison chart followed by
the action of `α`, `AlgebraicGeometry.Space.legSect`, read at the two legs that `k` determines out
of the algebraic space represented by the source of `V`. This presheaf is a sheaf.

## Main definitions

* `AlgebraicGeometry.Space.memberTestMap`: the morphism of test spaces attached to a morphism of
  the site of the charts of `φ`.
* `AlgebraicGeometry.Space.memberSectMap`: the restriction map, a section of `ℱ` over the target
  chart read as a section over the source chart.
* `AlgebraicGeometry.Space.memberSectAddHom`: the restriction map, as a morphism of the two
  groups of sections.
* `AlgebraicGeometry.Space.memberPresheaf`: those groups of sections and those restriction maps,
  as a presheaf of abelian groups on the site of the charts of `φ`.
* `AlgebraicGeometry.Space.memberPresheafRestrict`: the presheaf restricts along the honest charts
  of `U` to the abelian presheaf of `ℱ`.

## Main results

* `AlgebraicGeometry.Space.memberSectMap_of_leg_eq`: when the two legs attached to a morphism of
  the site agree, the restriction map is an ordinary restriction of sections of `ℱ`.
* `AlgebraicGeometry.Space.memberSectMap_id` and `AlgebraicGeometry.Space.memberSectMap_comp`:
  the restriction maps are functorial.
* `AlgebraicGeometry.Space.memberSectMap_singleInclusion`: along an honest morphism of charts of
  `U` the restriction map is restriction of sections of `ℱ`.
* `AlgebraicGeometry.Space.isSheaf_memberPresheaf`: the presheaf is a sheaf.
* `AlgebraicGeometry.Space.memberSectMap_smul_apply`: the restriction map of a scaled section,
  with the scalar pulled past the first factor.

## Implementation notes

The test space at which the action of `α` is read is the algebraic space represented by the
source of the chart, with the identity chart, so the chart of `U` induced along the first leg is
the source chart definitionally and
`AlgebraicGeometry.Space.QuasiCoherentDescent.chartUnitFst` is the identity.

A leg of a morphism of the site appears in the type of the sections the action is read on, so it
cannot be replaced by an equal morphism by rewriting; `legSect_val_map_of_eq` and
`legSect_comp_left_val_map` include the adjacent restriction map and substitute the equality.

Never use `AlgebraicGeometry.Space.legSectHom` outside its own file: elaborating it underneath a
`CategoryTheory.ModuleCat` instance does not terminate. Additivity and semilinearity are read off
the three factors of `AlgebraicGeometry.Space.legSect` separately. Likewise, `congrArg` at an
explicit abstraction is a recursion-depth failure at these types; use the congruence lemmas at
partially applied constants (`legSect_congr`, `etaleSect_congr`, `val_app_congr`).

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identifications of Stacks 03LW on sections are morphisms of modules -/

section Linear

variable {C D : AlgebraicSpaces B S hS} (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
  (M : Modules.{u, u} B S hS C.1 C.2) (U : SmallEtale B S hS D.1)

/-- Reading a section of an étale restriction back as a section of the inverse image is
additive. -/
private theorem etaleSectInv_add
    (s s' : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj U))) :
    etaleSectInv B S hS g hg M U (s + s') =
      etaleSectInv B S hS g hg M U s + etaleSectInv B S hS g hg M U s' :=
  map_add (((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (.op U)).hom
    s s'

/-- Reading a section of an étale restriction back as a section of the inverse image is linear
over the structure ring of the chart. -/
private theorem etaleSectInv_smul
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS D.1 D.2).O)).obj.obj
      (.op U))
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op U)) :
    etaleSectInv B S hS g hg M U (r • s) = r • etaleSectInv B S hS g hg M U s :=
  (((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app
    (.op U)).hom.map_smul r s

/-- Reading a section of the inverse image as a section over the composite chart is additive. -/
private theorem etaleSect_add (s s' : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    etaleSect B S hS g hg M U (s + s') =
      etaleSect B S hS g hg M U s + etaleSect B S hS g hg M U s' :=
  map_add (((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M).val.app (.op U)).hom
    s s'

/-- Reading a section of the inverse image as a section over the composite chart respects
equality of sections. -/
private theorem etaleSect_congr
    {s s' : ((modulePullback B S hS g).obj M).val.obj (.op U)} (h : s = s') :
    etaleSect B S hS g hg M U s = etaleSect B S hS g hg M U s' :=
  congrArg (etaleSect B S hS g hg M U) h

end Linear

/-- A morphism of modules read on sections respects equality of sections. -/
theorem val_app_congr {P : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS P.1 P.2} (ψ : M ⟶ N) (Y : SmallEtale B S hS P.1)
    {s s' : M.val.obj (.op Y)} (h : s = s') :
    ψ.val.app (.op Y) s = ψ.val.app (.op Y) s' :=
  congrArg (ψ.val.app (.op Y)) h

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)

/-! ### The geometry of a morphism of the site of the charts of `φ` -/

/-- The morphism of test spaces attached to a morphism of the site of the charts of `φ`: the
morphism of the two chart sources underlying it, read between the represented algebraic spaces. -/
def memberTestMap {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    chartTestSpace B S hS p.2 ⟶ chartTestSpace B S hS q.2 :=
  ObjectProperty.homMk (yoneda.map k.hom.hom.left)

/-- The morphism of test spaces, followed by the first leg of the target, is the second leg of
the given morphism. -/
theorem memberTestMap_comp_chartLegFst {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    memberTestMap B S hS G φ hφet k ≫ chartLegFst B S hS q.2 =
      chartLegSnd B S hS φ hφet k.hom :=
  rfl

/-- The morphism of test spaces attached to a morphism of the site is étale. -/
theorem isEtale_memberTestMap {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    IsEtale B S hS (memberTestMap B S hS G φ hφet k).hom :=
  isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS p.2.1.left)
    (isAlgebraicSpace_yoneda B S hS q.2.1.left) G.objects.2 _
    (chartLegSnd B S hS φ hφet k.hom).hom (chartLegFst B S hS q.2).hom
    (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS q.2) rfl

/-- The morphism of test spaces, followed by the second leg of a second morphism of the site, is
the second leg of the composite. -/
theorem memberTestMap_comp_chartLegSnd {p q r : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (l : q ⟶ r) :
    memberTestMap B S hS G φ hφet k ≫ chartLegSnd B S hS φ hφet l.hom =
      chartLegSnd B S hS φ hφet (k ≫ l).hom := by
  apply ObjectProperty.hom_ext
  change yoneda.map k.hom.hom.left ≫ yoneda.map l.hom.hom.left ≫ r.2.1.hom =
    yoneda.map (k.hom.hom.left ≫ l.hom.hom.left) ≫ r.2.1.hom
  rw [yoneda.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The identity chart of the test space of the source, carried along the morphism of test
spaces, maps to the identity chart of the test space of the target, by the morphism of chart
sources. -/
def memberTestChart {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    (smallEtalePostcomp B S hS (memberTestMap B S hS G φ hφet k)
        (isEtale_memberTestMap B S hS G φ hφet k)).obj (chartTestUnit B S hS p.2) ⟶
      chartTestUnit B S hS q.2 :=
  ObjectProperty.homMk (CostructuredArrow.homMk k.hom.hom.left (by
    change yoneda.map k.hom.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map k.hom.hom.left
    rw [Category.id_comp, Category.comp_id]))

/-- The image of `AlgebraicGeometry.Space.memberTestChart` under postcomposition with the first
leg of the target is the comparison of the identity chart of the test space with the target
chart. -/
theorem smallEtalePostcomp_map_memberTestChart {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    (smallEtalePostcomp B S hS (chartLegFst B S hS q.2)
          (isEtale_chartLegFst B S hS q.2)).map (memberTestChart B S hS G φ hφet k) =
      chartUnitSnd B S hS φ hφet k.hom := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  rfl

/-- The second leg attached to the image of an honest morphism of charts of `U` is the first
leg. -/
theorem chartLegSnd_smallEtalePostcomp_map {V W : SmallEtale B S hS G.objects.1} (h : V ⟶ W) :
    chartLegSnd B S hS φ hφet ((smallEtalePostcomp B S hS φ hφet).map h) =
      chartLegFst B S hS V :=
  ObjectProperty.hom_ext _ (CostructuredArrow.w h.hom)

/-- The second leg attached to the identity of an induced chart is the first leg. -/
theorem chartLegSnd_id (V : SmallEtale B S hS G.objects.1) :
    chartLegSnd B S hS φ hφet (𝟙 ((smallEtalePostcomp B S hS φ hφet).obj V)) =
      chartLegFst B S hS V :=
  (congrArg (chartLegSnd B S hS φ hφet)
      ((smallEtalePostcomp B S hS φ hφet).map_id V)).symm.trans
    (chartLegSnd_smallEtalePostcomp_map B S hS G φ hφet (𝟙 V))

/-! ### The restriction map -/

variable (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  (Z : QuasicoherentModule B S hS G)

/-- The restriction map of a quasi-coherent module on the groupoid along a morphism of the site
of the charts of `φ`: a section of `ℱ` over the target chart is restricted along the comparison
of the identity chart of the test space with that chart, and then carried by the action of the
transition morphism along the two legs, giving a section over the source chart. -/
def memberSectMap {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m : Z.F.obj.val.obj (.op q.2)) :
    Z.F.obj.val.obj (.op p.2) :=
  legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
    (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
    (chartLeg_condition B S hS φ hφet k.hom).symm (chartTestUnit B S hS p.2)
    (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet k.hom).op m)

/-- The unfolding of `AlgebraicGeometry.Space.memberSectMap`. -/
theorem memberSectMap_eq {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m : Z.F.obj.val.obj (.op q.2)) :
    memberSectMap B S hS G φ hφet hpb Z k m =
      legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
        (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
        (chartLeg_condition B S hS φ hφet k.hom).symm (chartTestUnit B S hS p.2)
        (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet k.hom).op m) :=
  rfl

/-! ### The calculus of the two factors -/

/-- The reading of the transition morphism on sections respects equality of sections. -/
theorem legSect_congr {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.objects)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ)
    (Y : SmallEtale B S hS P.1)
    {x y : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))} (h : x = y) :
    legSect B S hS G φ hpb Z a b ha hb hab Y x =
      legSect B S hS G φ hpb Z a b ha hb hab Y y :=
  congrArg (legSect B S hS G φ hpb Z a b ha hb hab Y) h

/-- The reading of the transition morphism on sections is additive. -/
private theorem legSect_add {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.objects)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ)
    (Y : SmallEtale B S hS P.1)
    (x y : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y (x + y) =
      legSect B S hS G φ hpb Z a b ha hb hab Y x +
        legSect B S hS G φ hpb Z a b ha hb hab Y y := by
  rw [legSect_eq_etaleSect, legSect_eq_etaleSect, legSect_eq_etaleSect,
    etaleSectInv_add B S hS a ha Z.F.obj Y x y,
    map_add ((legTransition B S hS G φ hpb Z a b hab).val.app (.op Y)).hom,
    etaleSect_add B S hS b hb Z.F.obj Y]

/-- Restriction of sections of `ℱ` along an identity is the identity. -/
theorem val_map_id {V : SmallEtale B S hS G.objects.1}
    (m : Z.F.obj.val.obj (.op V)) :
    Z.F.obj.val.map (𝟙 (Opposite.op V)) m = m :=
  congrArg (fun t : Z.F.obj.val.presheaf.obj (Opposite.op V) ⟶
      Z.F.obj.val.presheaf.obj (Opposite.op V) => ConcreteCategory.hom t m)
    (Z.F.obj.val.presheaf.map_id (Opposite.op V))

/-- Restriction of sections of `ℱ` along a morphism of charts is additive. -/
private theorem val_map_add {V W : SmallEtale B S hS G.objects.1} (c : V ⟶ W)
    (m m' : Z.F.obj.val.obj (.op W)) :
    Z.F.obj.val.map c.op (m + m') =
      Z.F.obj.val.map c.op m + Z.F.obj.val.map c.op m' :=
  map_add (Z.F.obj.val.map c.op).hom m m'

/-- Restriction of sections of `ℱ` along a morphism of charts is semilinear along the
restriction of functions. -/
theorem val_map_smul {V W : SmallEtale B S hS G.objects.1} (c : V ⟶ W)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
      G.objects.2).O)).obj.obj (.op W))
    (m : Z.F.obj.val.obj (.op W)) :
    Z.F.obj.val.map c.op (r • m) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS G.objects.1
        G.objects.2).O)).obj.map c.op r • Z.F.obj.val.map c.op m :=
  Z.F.obj.val.map_smul c.op r m

/-! ### Replacing a leg -/

/-- For equal legs `a = b`, reading a section restricted along a morphism of charts `c₁` is
restricting it along any morphism of charts `c₂` with the same underlying scheme map. -/
private theorem legSect_val_map_of_eq {P : AlgebraicSpaces B S hS} {a b : P ⟶ G.objects}
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) (e : a = b)
    (Y : SmallEtale B S hS P.1) {D : SmallEtale B S hS G.objects.1}
    (c₁ : (smallEtalePostcomp B S hS a ha).obj Y ⟶ D)
    (c₂ : (smallEtalePostcomp B S hS b hb).obj Y ⟶ D) (hc : c₁.hom.left = c₂.hom.left)
    (m : Z.F.obj.val.obj (.op D)) :
    legSect B S hS G φ hpb Z a b ha hb hab Y (Z.F.obj.val.map c₁.op m) =
      Z.F.obj.val.map c₂.op m := by
  subst e
  obtain rfl : c₁ = c₂ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hc)
  exact legSect_self B S hS G φ hpb Z a ha Y _

/-- Naturality in the test space, with the restriction map included: the reading of a pair
whose first leg is a precomposition `q₀ ≫ a` is the reading of the pair `(a, b)` over the induced
chart of the larger test space. -/
private theorem legSect_comp_left_val_map {P Q : AlgebraicSpaces B S hS} (q₀ : P ⟶ Q)
    (hq : IsEtale B S hS q₀.hom) (a b : Q ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) {a' : P ⟶ G.objects}
    (ha' : IsEtale B S hS a'.hom) (ha'b : a' ≫ φ = (q₀ ≫ b) ≫ φ) (e : a' = q₀ ≫ a)
    (hqa : IsEtale B S hS (q₀ ≫ a).hom) (hqb : IsEtale B S hS (q₀ ≫ b).hom)
    (hca : QuasiCoherentDescent.EtaleRestrictionComp B S hS q₀ a hq ha hqa)
    (hcb : QuasiCoherentDescent.EtaleRestrictionComp B S hS q₀ b hq hb hqb)
    (Y : SmallEtale B S hS P.1) {D : SmallEtale B S hS G.objects.1}
    (c₁ : (smallEtalePostcomp B S hS a' ha').obj Y ⟶ D)
    (c₂ : (smallEtalePostcomp B S hS a ha).obj
      ((smallEtalePostcomp B S hS q₀ hq).obj Y) ⟶ D) (hc : c₁.hom.left = c₂.hom.left)
    (m : Z.F.obj.val.obj (.op D)) :
    legSect B S hS G φ hpb Z a' (q₀ ≫ b) ha' hqb ha'b Y (Z.F.obj.val.map c₁.op m) =
      legSect B S hS G φ hpb Z a b ha hb hab ((smallEtalePostcomp B S hS q₀ hq).obj Y)
        (Z.F.obj.val.map c₂.op m) := by
  subst e
  obtain rfl : c₁ = c₂ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hc)
  exact legSect_comp_left B S hS G φ hpb Z q₀ hq a b ha hb hab hqa hqb ha'b hca hcb Y _

/-! ### The restriction map at a morphism whose two legs agree -/

/-- When the two legs attached to a morphism of the site agree, the restriction map is the
restriction of sections of `ℱ` along any morphism of charts of `U` with the same underlying
scheme map. -/
theorem memberSectMap_of_leg_eq {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (e : chartLegSnd B S hS φ hφet k.hom = chartLegFst B S hS p.2) (c : p.2 ⟶ q.2)
    (hc : c.hom.left = k.hom.hom.left) (m : Z.F.obj.val.obj (.op q.2)) :
    memberSectMap B S hS G φ hφet hpb Z k m = Z.F.obj.val.map c.op m :=
  legSect_val_map_of_eq B S hS G φ hpb Z (isEtale_chartLegSnd B S hS φ hφet k.hom)
    (isEtale_chartLegFst B S hS p.2) (chartLeg_condition B S hS φ hφet k.hom).symm e
    (chartTestUnit B S hS p.2) (chartUnitSnd B S hS φ hφet k.hom) c hc.symm m

/-- The restriction map along an honest morphism of charts of `U` is restriction of sections of
`ℱ`. -/
theorem memberSectMap_singleInclusion {V W : SmallEtale B S hS G.objects.1} (h : V ⟶ W)
    (m : Z.F.obj.val.obj (.op W)) :
    memberSectMap B S hS G φ hφet hpb Z ((singleInclusion B S hS φ hφet).map h) m =
      Z.F.obj.val.map h.op m :=
  memberSectMap_of_leg_eq B S hS G φ hφet hpb Z ((singleInclusion B S hS φ hφet).map h)
    (chartLegSnd_smallEtalePostcomp_map B S hS G φ hφet h) h rfl m

/-- The restriction map along an identity is the identity. -/
theorem memberSectMap_id (p : SingleSite B S hS φ hφet) (m : Z.F.obj.val.obj (.op p.2)) :
    memberSectMap B S hS G φ hφet hpb Z (𝟙 p) m = m :=
  (memberSectMap_of_leg_eq B S hS G φ hφet hpb Z (𝟙 p) (chartLegSnd_id B S hS G φ hφet p.2)
    (𝟙 p.2) rfl m).trans (val_map_id B S hS G Z m)

/-! ### Functoriality -/

/-- The reading of the transition morphism along the legs of a morphism of the site respects
equality of sections. -/
private theorem legSect_chartLeg_congr {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    {x y : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS (chartLegSnd B S hS φ hφet k.hom)
      (isEtale_chartLegSnd B S hS φ hφet k.hom)).obj (chartTestUnit B S hS p.2)))}
    (h : x = y) :
    legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
        (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
        (chartLeg_condition B S hS φ hφet k.hom).symm (chartTestUnit B S hS p.2) x =
      legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
        (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
        (chartLeg_condition B S hS φ hφet k.hom).symm (chartTestUnit B S hS p.2) y :=
  legSect_congr B S hS G φ hpb Z _ _ _ _ _ _ h

/-- The `l`-factor of the restriction map along a composite `k ≫ l`, moved to the test space of
`k`: it is the restriction, along the comparison chart of `k`, of the restriction map along `l`. -/
private theorem legSect_memberTestMap {p q r : SingleSite B S hS φ hφet} (k : p ⟶ q) (l : q ⟶ r)
    (m : Z.F.obj.val.obj (.op r.2)) :
    legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet (k ≫ l).hom)
        (chartLegSnd B S hS φ hφet k.hom)
        (isEtale_chartLegSnd B S hS φ hφet (k ≫ l).hom)
        (isEtale_chartLegSnd B S hS φ hφet k.hom)
        ((chartLeg_condition B S hS φ hφet (k ≫ l).hom).symm.trans
          (chartLeg_condition B S hS φ hφet k.hom))
        (chartTestUnit B S hS p.2)
        (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet (k ≫ l).hom).op m) =
      Z.F.obj.val.map (chartUnitSnd B S hS φ hφet k.hom).op
        (memberSectMap B S hS G φ hφet hpb Z l m) := by
  have hq := isEtale_memberTestMap B S hS G φ hφet k
  have hal := isEtale_chartLegSnd B S hS φ hφet l.hom
  have hbw := isEtale_chartLegFst B S hS q.2
  have hrepq := relativelyRepresentable_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_yoneda B S hS q.2.1.left) (memberTestMap B S hS G φ hφet k).hom
  refine ((legSect_comp_left_val_map B S hS G φ hpb Z (memberTestMap B S hS G φ hφet k) hq
        (chartLegSnd B S hS φ hφet l.hom) (chartLegFst B S hS q.2) hal hbw
        (chartLeg_condition B S hS φ hφet l.hom).symm
        (isEtale_chartLegSnd B S hS φ hφet (k ≫ l).hom)
        ((chartLeg_condition B S hS φ hφet (k ≫ l).hom).symm.trans
          (chartLeg_condition B S hS φ hφet k.hom))
        (memberTestMap_comp_chartLegSnd B S hS G φ hφet k l).symm
        (isEtale_comp B S hS hq hal) (isEtale_comp B S hS hq hbw)
        (etaleRestrictionComp_of_representable B S hS (memberTestMap B S hS G φ hφet k)
          (chartLegSnd B S hS φ hφet l.hom) hq hal (isEtale_comp B S hS hq hal) hrepq
          (relativelyRepresentable_legToY B S hS q.2 (chartLegSnd B S hS φ hφet l.hom))
          (relativelyRepresentable_legToY B S hS p.2
            (memberTestMap B S hS G φ hφet k ≫ chartLegSnd B S hS φ hφet l.hom)))
        (etaleRestrictionComp_of_representable B S hS (memberTestMap B S hS G φ hφet k)
          (chartLegFst B S hS q.2) hq hbw (isEtale_comp B S hS hq hbw) hrepq
          (relativelyRepresentable_legToY B S hS q.2 (chartLegFst B S hS q.2))
          (relativelyRepresentable_legToY B S hS p.2
            (memberTestMap B S hS G φ hφet k ≫ chartLegFst B S hS q.2)))
        (chartTestUnit B S hS p.2) (chartUnitSnd B S hS φ hφet (k ≫ l).hom)
        ((smallEtalePostcomp B S hS (chartLegSnd B S hS φ hφet l.hom) hal).map
            (memberTestChart B S hS G φ hφet k) ≫ chartUnitSnd B S hS φ hφet l.hom)
        rfl m).trans
    (legSect_congr B S hS G φ hpb Z (chartLegSnd B S hS φ hφet l.hom)
      (chartLegFst B S hS q.2) hal hbw (chartLeg_condition B S hS φ hφet l.hom).symm
      ((smallEtalePostcomp B S hS (memberTestMap B S hS G φ hφet k) hq).obj
        (chartTestUnit B S hS p.2))
      (Z.F.obj.val.map_comp_apply (chartUnitSnd B S hS φ hφet l.hom).op
        ((smallEtalePostcomp B S hS (chartLegSnd B S hS φ hφet l.hom) hal).map
          (memberTestChart B S hS G φ hφet k)).op m))).trans ?_
  exact (legSect_restrict B S hS G φ hpb Z (chartLegSnd B S hS φ hφet l.hom)
      (chartLegFst B S hS q.2) hal hbw (chartLeg_condition B S hS φ hφet l.hom).symm
      (memberTestChart B S hS G φ hφet k)
      (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet l.hom).op m)).trans
    (Z.F.obj.val.congr_map_apply
      (congrArg Quiver.Hom.op (smallEtalePostcomp_map_memberTestChart B S hS G φ hφet k)) _)

/-- The restriction map along a composite `k ≫ l` is the restriction map along `l` followed by
the restriction map along `k`. -/
theorem memberSectMap_comp {p q r : SingleSite B S hS φ hφet} (k : p ⟶ q) (l : q ⟶ r)
    (m : Z.F.obj.val.obj (.op r.2)) :
    memberSectMap B S hS G φ hφet hpb Z (k ≫ l) m =
      memberSectMap B S hS G φ hφet hpb Z k (memberSectMap B S hS G φ hφet hpb Z l m) :=
  ((legSect_comp B S hS G φ hpb Z (chartLegSnd B S hS φ hφet (k ≫ l).hom)
          (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
          (isEtale_chartLegSnd B S hS φ hφet (k ≫ l).hom)
          (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
          ((chartLeg_condition B S hS φ hφet (k ≫ l).hom).symm.trans
            (chartLeg_condition B S hS φ hφet k.hom))
          (chartLeg_condition B S hS φ hφet k.hom).symm
          (chartLeg_condition B S hS φ hφet (k ≫ l).hom).symm (chartTestUnit B S hS p.2)
          (Z.F.obj.val.map (chartUnitSnd B S hS φ hφet (k ≫ l).hom).op m)).symm).trans
    (legSect_chartLeg_congr B S hS G φ hφet hpb Z k
      (legSect_memberTestMap B S hS G φ hφet hpb Z k l m))

/-- The restriction map is additive. -/
theorem memberSectMap_add {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m m' : Z.F.obj.val.obj (.op q.2)) :
    memberSectMap B S hS G φ hφet hpb Z k (m + m') =
      memberSectMap B S hS G φ hφet hpb Z k m + memberSectMap B S hS G φ hφet hpb Z k m' :=
  (legSect_chartLeg_congr B S hS G φ hφet hpb Z k
      (val_map_add B S hS G Z (chartUnitSnd B S hS φ hφet k.hom) m m')).trans
    (legSect_add B S hS G φ hpb Z (chartLegSnd B S hS φ hφet k.hom) (chartLegFst B S hS p.2)
      (isEtale_chartLegSnd B S hS φ hφet k.hom) (isEtale_chartLegFst B S hS p.2)
      (chartLeg_condition B S hS φ hφet k.hom).symm (chartTestUnit B S hS p.2) _ _)

/-! ### The presheaf and its sheaf condition -/

/-- The restriction map, as a morphism of the two groups of sections. -/
def memberSectAddHom {p q : SingleSite B S hS φ hφet} (k : p ⟶ q) :
    Z.F.obj.val.presheaf.obj (.op q.2) ⟶ Z.F.obj.val.presheaf.obj (.op p.2) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (memberSectMap B S hS G φ hφet hpb Z k)
    (memberSectMap_add B S hS G φ hφet hpb Z k))

/-- The morphism of groups of sections acts on a section as the restriction map. -/
theorem memberSectAddHom_apply {p q : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (m : Z.F.obj.val.presheaf.obj (.op q.2)) :
    (memberSectAddHom B S hS G φ hφet hpb Z k).hom m =
      memberSectMap B S hS G φ hφet hpb Z k m :=
  rfl

/-- A composite of two morphisms of groups of sections acts on a section as the composite of the
two restriction maps. -/
theorem memberSectAddHom_comp_apply {p q r : SingleSite B S hS φ hφet} (k : p ⟶ q) (l : q ⟶ r)
    (m : Z.F.obj.val.presheaf.obj (.op r.2)) :
    (memberSectAddHom B S hS G φ hφet hpb Z l ≫
        memberSectAddHom B S hS G φ hφet hpb Z k).hom m =
      memberSectMap B S hS G φ hφet hpb Z k (memberSectMap B S hS G φ hφet hpb Z l m) := by
  rw [AddCommGrpCat.comp_apply, memberSectAddHom_apply, memberSectAddHom_apply]

/-- The restriction map along an identity, as a morphism of groups of sections, is the
identity. -/
theorem memberSectAddHom_id (p : SingleSite B S hS φ hφet) :
    memberSectAddHom B S hS G φ hφet hpb Z (𝟙 p) =
      𝟙 (Z.F.obj.val.presheaf.obj (.op p.2)) :=
  AddCommGrpCat.ext fun m => memberSectMap_id B S hS G φ hφet hpb Z p m

/-- The restriction maps, as morphisms of groups of sections, are compatible with
composition. -/
theorem memberSectAddHom_comp {p q r : SingleSite B S hS φ hφet} (k : p ⟶ q)
    (l : q ⟶ r) :
    memberSectAddHom B S hS G φ hφet hpb Z (k ≫ l) =
      memberSectAddHom B S hS G φ hφet hpb Z l ≫
        memberSectAddHom B S hS G φ hφet hpb Z k :=
  AddCommGrpCat.ext fun m => ((memberSectAddHom_apply B S hS G φ hφet hpb Z (k ≫ l) m).trans
    (memberSectMap_comp B S hS G φ hφet hpb Z k l m)).trans
    (memberSectAddHom_comp_apply B S hS G φ hφet hpb Z k l m).symm

/-- The restriction map along an honest morphism of charts of `U`, as a morphism of groups of
sections, is restriction of sections of `ℱ`. -/
theorem memberSectAddHom_singleInclusion {V W : SmallEtale B S hS G.objects.1}
    (h : V ⟶ W) :
    memberSectAddHom B S hS G φ hφet hpb Z ((singleInclusion B S hS φ hφet).map h) =
      Z.F.obj.val.presheaf.map h.op :=
  AddCommGrpCat.ext fun m => memberSectMap_singleInclusion B S hS G φ hφet hpb Z h m

/-- The sections of a quasi-coherent module on the groupoid, as a presheaf of abelian groups on
the site of the charts of `φ`: the sections over a chart of `U` are the sections of `ℱ` over that
chart, and the restriction maps are `AlgebraicGeometry.Space.memberSectMap`. -/
def memberPresheaf : (SingleSite B S hS φ hφet)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj p := Z.F.obj.val.presheaf.obj (.op p.unop.2)
  map k := memberSectAddHom B S hS G φ hφet hpb Z k.unop
  map_id p := memberSectAddHom_id B S hS G φ hφet hpb Z p.unop
  map_comp k l := memberSectAddHom_comp B S hS G φ hφet hpb Z l.unop k.unop

/-- The presheaf acts on a section as the restriction map. -/
theorem memberPresheaf_map_apply {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    (memberPresheaf B S hS G φ hφet hpb Z).map f m =
      memberSectMap B S hS G φ hφet hpb Z f.unop m :=
  memberSectAddHom_apply B S hS G φ hφet hpb Z f.unop m

/-- The restriction of `AlgebraicGeometry.Space.memberPresheaf` along the honest charts of `U`
is the abelian presheaf of `ℱ`, with identity components. -/
def memberPresheafRestrict :
    (singleInclusion B S hS φ hφet).op ⋙ memberPresheaf B S hS G φ hφet hpb Z ≅
      Z.F.obj.val.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun h =>
    (Category.comp_id _).trans
      ((memberSectAddHom_singleInclusion B S hS G φ hφet hpb Z h.unop).trans
        (Category.id_comp _).symm))

/-- The presheaf `AlgebraicGeometry.Space.memberPresheaf` is a sheaf for the restricted étale
topology of the site of the charts of `φ`. -/
theorem isSheaf_memberPresheaf :
    Presheaf.IsSheaf (singleTopology B S hS φ hφet)
      (memberPresheaf B S hS G φ hφet hpb Z) :=
  isSheaf_of_isSheaf_singleInclusion' B S hS φ hφet
    (memberPresheaf B S hS G φ hφet hpb Z)
    ((Presheaf.isSheaf_of_iso_iff (memberPresheafRestrict B S hS G φ hφet hpb Z)).2
      Z.F.obj.isSheaf)

/-! ### The sheaf of modules -/

section CoverDense

variable [(singleFunctor B S hS φ hφet).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- The sections of the presheaf over an object of the site of the charts of `φ` are a module
over the restricted structure sheaf, by the module structure of the sections of `ℱ` over the
chart of `U`. -/
instance moduleMemberPresheaf (p : (SingleSite B S hS φ hφet)ᵒᵖ) :
    Module ((singleRing B S hS φ hφet).obj.obj p)
      ((memberPresheaf B S hS G φ hφet hpb Z).obj p) :=
  inferInstanceAs (Module
    (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)).obj.obj
      (.op p.unop.2)) (Z.F.obj.val.presheaf.obj (.op p.unop.2)))

/-- The first factor of the restriction map is semilinear, with the scalar read in the
restricted structure sheaf and the section in the presheaf. -/
theorem memberSectMap_smul_step {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (r : (singleRing B S hS φ hφet).obj.obj P)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    Z.F.obj.val.map (chartUnitSnd B S hS φ hφet f.unop.hom).op (r • m) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)).obj.map
          (chartUnitSnd B S hS φ hφet f.unop.hom).op r •
        Z.F.obj.val.map (chartUnitSnd B S hS φ hφet f.unop.hom).op m :=
  val_map_smul B S hS G Z (chartUnitSnd B S hS φ hφet f.unop.hom) r m

/-- The restriction map of a scaled section, with the scalar pulled past the first factor. -/
theorem memberSectMap_smul_apply {P Q : (SingleSite B S hS φ hφet)ᵒᵖ} (f : P ⟶ Q)
    (r : (singleRing B S hS φ hφet).obj.obj P)
    (m : (memberPresheaf B S hS G φ hφet hpb Z).obj P) :
    memberSectMap B S hS G φ hφet hpb Z f.unop (r • m) =
      legSect B S hS G φ hpb Z (chartLegSnd B S hS φ hφet f.unop.hom)
        (chartLegFst B S hS Q.unop.2) (isEtale_chartLegSnd B S hS φ hφet f.unop.hom)
        (isEtale_chartLegFst B S hS Q.unop.2)
        (chartLeg_condition B S hS φ hφet f.unop.hom).symm (chartTestUnit B S hS Q.unop.2)
        (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS G.objects.1 G.objects.2).O)).obj.map
            (chartUnitSnd B S hS φ hφet f.unop.hom).op r •
          Z.F.obj.val.map (chartUnitSnd B S hS φ hφet f.unop.hom).op m) :=
  legSect_chartLeg_congr B S hS G φ hφet hpb Z f.unop
    (memberSectMap_smul_step B S hS G φ hφet hpb Z f r m)

end CoverDense

end AlgebraicGeometry.Space

end
