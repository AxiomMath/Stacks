module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.AbelianLimitCone
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.PullbackAsAMorphismOfDeltaFunctors
public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemAbelian
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelianComparison

/-!
# The vertex functor of a cofiltered limit of spectral spaces

The degree induction of [Stacks, Tag 0A37] (Lemma 20.19.3) compares two cohomological
δ-functors on the abelian category of systems `SpectralDiagram.AbelianSystem`.  The limit side
of that comparison is cohomology over an open of the vertex of the sheaf `colimⱼ pⱼ⁻¹𝒜ⱼ`, and
`CategoryTheory.DeltaFunctor.precomp` needs that assignment as an **exact functor** of the system,
not merely as a construction on one system at a time.  This file builds it:
`SpectralDiagram.AbelianSystem.vertexFunctor`, with its three exactness instances.

## Exactness

The construction here uses Mathlib's inverse image `TopCat.Sheaf.pullback` rather than the germ
model, and that is what makes the exactness free: the inverse image is additive and exact in both
directions (`Stacks.Cohomology.AbelianColimit.sheafPullback_additive`,
`…_preservesFiniteLimits`, `…_preservesFiniteColimits`), evaluation at a stage is exact in both
directions (`SpectralDiagram.AbelianSystem.ev_preservesFiniteLimits`, `…_preservesFiniteColimits`),
limits and colimits in a functor category are computed pointwise, and `Jᵒᵖ` is filtered for a
cofiltered index category, so `Jᵒᵖ`-colimits of abelian sheaves are exact.  The germ model is
isomorphic to the inverse image objectwise (`GermPullback.abelianSheafPullbackIso`), so nothing is
lost: the compatibility of that objectwise isomorphism with the transition maps is
`SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj_naturality`, the two together are
the natural isomorphism `SpectralDiagram.AbelianSystem.vertexSystemIsoGermSystem`, and its colimit
is `SpectralDiagram.AbelianSystem.vertexFunctorObjIsoConePtSheaf` — see "The identification with
the germ model" below.

## The transition maps, and where the cone identity enters

The transition map `pᵢ⁻¹𝒜ᵢ ⟶ pⱼ⁻¹𝒜ⱼ` attached to `a : j ⟶ i` is defined by transposing across
the adjunction `pᵢ⁻¹ ⊣ (pᵢ)_*`: its transpose is the `f_a`-map of the system followed by `(f_a)_*`
of the adjunction unit and then the comparison
`(pⱼ)_*(f_a)_* ⟶ (pᵢ)_*` of pushforwards, which exists because `pⱼ ≫ f_a = pᵢ` is the cone
identity.  That comparison is `SpectralDiagram.pushConeHom`, and it is the only place where the
cone identity enters a definition.  It is built like the existing `SpectralDiagram.pushIdHom` and
`SpectralDiagram.pushCompHom`: as the whiskering into the sheaf of an arrow of functors of opens,
so that its components are restriction maps along *equal* opens.  All three comparisons are then
identified with each other by the uniqueness of arrows of `(Opens X)ᵒᵖ`
(`SpectralDiagram.pushConeHom_id`, `SpectralDiagram.pushConeHom_comp`), which is what makes the
identity and cocycle laws of the transition maps cheap.

The two laws themselves are instances of `SpectralDiagram.cocycle_aux` and
`SpectralDiagram.naturality_aux`, stated over abstract categories with every category, functor and
object a variable, so that no spelling crossing of the sheaf categories is paid inside them.

## Main definitions

* `SpectralDiagram.pushConeHom`: the comparison `(pⱼ)_*(f_a)_* ⟶ (pᵢ)_*` of pushforwards along
  the legs of a cone of the spaces.
* `SpectralDiagram.AbelianSystem.vertexTrans`: the transition map `pᵢ⁻¹𝒜ᵢ ⟶ pⱼ⁻¹𝒜ⱼ`.
* `SpectralDiagram.AbelianSystem.vertexSystem`: the pullback system `k ↦ pₖ⁻¹𝒜ₖ` on the vertex.
* `SpectralDiagram.AbelianSystem.vertexSystemFunctor`: that system, functorially in the system.
* `SpectralDiagram.AbelianSystem.vertexFunctor`: **`𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ` as a functor on the
  category of systems**, with `vertexFunctor_additive`,
  `vertexFunctor_preservesFiniteLimits` and `vertexFunctor_preservesFiniteColimits` —
  the three properties `CategoryTheory.DeltaFunctor.precomp` asks of it.
* `SpectralDiagram.AbelianSystem.vertexSystemIsoGermSystem`: the pullback system and the
  germ-model system as isomorphic *systems*.
* `SpectralDiagram.AbelianSystem.vertexFunctorObjIsoConePtSheaf`: **`colimⱼ pⱼ⁻¹𝒜ⱼ` is the sheaf
  on the vertex of the limiting cone of the system**, with the leg identity
  `…ι_comp_vertexFunctorObjIsoConePtSheaf_hom`.

## Main results

* `SpectralDiagram.pushforward_cone_comp`: `(pⱼ)_* ∘ (f_a)_* = (pᵢ)_*`, by the cone identity.
* `SpectralDiagram.pushConeHom_app_hom`: the cone comparison of pushforwards is the restriction
  map along an arrow of `(Opens c₀.pt)ᵒᵖ`, i.e. the identification the germ model uses.
* `SpectralDiagram.AbelianSystem.vertexTrans_id` and `…_comp`: the two laws of the system.
* `SpectralDiagram.AbelianSystem.vertexTrans_naturality`: the transition maps are natural in the
  system, which is what makes `vertexSystemFunctor` a functor.
* `SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj_naturality`: **the pullback
  system and the germ-model system agree as systems**, not merely objectwise.

## The identification with the germ model

`vertexSystem` is isomorphic to the germ-model system `germSystem` *as a system*: objectwise by
`GermPullback.abelianSheafPullbackIso`
(`SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj`), and those isomorphisms commute
with `SheafedSpaceLimit.trans`
(`SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj_naturality`).  Those two are the
components of the natural isomorphism
`SpectralDiagram.AbelianSystem.vertexSystemIsoGermSystem`, and taking colimits of it gives
`SpectralDiagram.AbelianSystem.vertexFunctorObjIsoConePtSheaf`:
`colimit (A.vertexSystem c₀)` **is** the sheaf `(A.cone c₀).pt.sheaf`, so the theory of the
vertex sheaf applies to `vertexFunctor`.

The proof of the naturality square is the transpose: both sides are morphisms out
of `pᵢ⁻¹𝒜ᵢ`, the germ model's `trans` is *defined* by its transpose, and the only non-formal step
is the identification of `SpectralDiagram.pushConeHom` with the `eqToHom` that
`SheafedSpaceLimit.transUnit` carries — which is `Subsingleton.elim` of arrows of
`(Opens c₀.pt)ᵒᵖ`, not an `eqToHom` computation (`SpectralDiagram.pushConeHom_app_hom`).

## Use

The vertex functor is the limit side of the comparison of δ-functors of the degree induction of
Stacks 0A37, `SpectralDiagram.AbelianSystem.vertexExtDelta`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonOfDeltaFunctors.lean`).

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

namespace SpectralDiagram

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}

/-- **`(pⱼ)_*` followed by `(f_a)_*` is `(pᵢ)_*`**, by the cone identity `pⱼ ≫ f_a = pᵢ`: the
inverse image of an open along a composite is the composite of the inverse images on the nose, so
the two double pushforwards are the same functor, not merely isomorphic ones. -/
theorem pushforward_cone_comp (c₀ : Cone D.F) {j i : J} (a : j ⟶ i) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j) ⋙ D.pushFunctor a =
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i) := by
  rw [← c₀.w a]
  rfl

/-- `pᵢ⁻¹V = pⱼ⁻¹fₐ⁻¹V` as an arrow of functors of opens. -/
def preConeNatTrans (c₀ : Cone D.F) {j i : J} (a : j ⟶ i) :
    (Opens.map (D.F.map a)).op ⋙ (Opens.map (c₀.π.app j)).op ⟶ (Opens.map (c₀.π.app i)).op :=
  eqToHom (by rw [← c₀.w a]; rfl)

/-- The comparison `(pⱼ)_*(f_a)_* ⟶ (pᵢ)_*` of pushforwards along the legs of a cone. -/
def pushConeHom (c₀ : Cone D.F) {j i : J} (a : j ⟶ i) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j) ⋙ D.pushFunctor a ⟶
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i) where
  app Z := InducedCategory.homMk (Functor.whiskerRight (preConeNatTrans c₀ a) Z.presheaf)
  naturality _ _ u :=
    InducedCategory.Hom.ext (NatTrans.ext (funext fun _ => (u.hom.naturality _).symm))

/-- At an identity, the cone comparison is the identity comparison of pushforwards. -/
lemma pushConeHom_id (c₀ : Cone D.F) (j : J)
    (X : (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}) :
    (pushConeHom c₀ (𝟙 j)).app X =
      (D.pushIdHom j).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).obj X) :=
  InducedCategory.Hom.ext (NatTrans.ext (funext fun _ =>
    congrArg X.presheaf.map (Subsingleton.elim _ _)))

/-- The cocycle law of the cone comparison. -/
lemma pushConeHom_comp (c₀ : Cone D.F) {k j i : J} (b : k ⟶ j) (a : j ⟶ i)
    (X : (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}) :
    (pushConeHom c₀ (b ≫ a)).app X =
      (D.pushCompHom b a).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app k)).obj X) ≫
        (D.pushFunctor a).map ((pushConeHom c₀ b).app X) ≫ (pushConeHom c₀ a).app X :=
  InducedCategory.Hom.ext (NatTrans.ext (funext fun V => by
    change X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)))

/-- **The cone comparison of pushforwards is the identification of pushforwards along equal
continuous maps that the germ model uses.**  Both sides are the restriction map of `Z` along an
arrow of `(Opens c₀.pt)ᵒᵖ` between two spellings of one open, so `Subsingleton.elim` identifies
them; this is what lets the transition maps of the two systems on the vertex be compared. -/
lemma pushConeHom_app_hom (c₀ : Cone D.F) {j i : J} (a : j ⟶ i)
    (Z : (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}) :
    ((pushConeHom c₀ a).app Z).hom =
      eqToHom (congrArg
        (fun m ↦ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} m).obj Z.presheaf) (c₀.w a)) := by
  refine NatTrans.ext (funext fun V => ?_)
  rw [eqToHom_app]
  exact (congrArg Z.presheaf.map (Subsingleton.elim _
    (homOfLE (le_of_eq (congrArg (fun m ↦ (Opens.map m).obj V.unop) (c₀.w a)).symm)).op)).trans
    (GermPullback.eqToHom_eq_map Z.presheaf
    (congrArg (fun m ↦ (Opens.map m).obj V.unop) (c₀.w a)) _).symm

/-- `pⱼ⁻¹`, the inverse image along the `j`-th leg of a cone of the spaces. -/
abbrev conePullback (c₀ : Cone D.F) (j : J) :
    D.StageSheaf j ⥤ (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (c₀.π.app j)

/-- The adjunction `pⱼ⁻¹ ⊣ (pⱼ)_*`. -/
abbrev coneAdj (c₀ : Cone D.F) (j : J) :
    conePullback c₀ j ⊣ TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j) :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (c₀.π.app j)

namespace AbelianSystem

/-- The transition map of the pullback system on the vertex, as a map out of the `i`-th sheaf. -/
def vertexTransUnit (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J} (a : j ⟶ i) :
    A.sheaf i ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).obj
      ((conePullback c₀ j).obj (A.sheaf j)) :=
  A.pushSheaf a ≫ (D.pushFunctor a).map ((coneAdj c₀ j).unit.app (A.sheaf j)) ≫
    (pushConeHom c₀ a).app ((conePullback c₀ j).obj (A.sheaf j))

/-- The transition map `pᵢ⁻¹𝒜ᵢ ⟶ pⱼ⁻¹𝒜ⱼ` of the pullback system on the vertex. -/
def vertexTrans (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J} (a : j ⟶ i) :
    (conePullback c₀ i).obj (A.sheaf i) ⟶ (conePullback c₀ j).obj (A.sheaf j) :=
  ((coneAdj c₀ i).homEquiv _ _).symm (A.vertexTransUnit c₀ a)

/-- The defining property of `vertexTrans`. -/
lemma unit_comp_map_vertexTrans (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J} (a : j ⟶ i) :
    (coneAdj c₀ i).unit.app (A.sheaf i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map (A.vertexTrans c₀ a) =
      A.vertexTransUnit c₀ a :=
  ((coneAdj c₀ i).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- A morphism out of `pⱼ⁻¹X` is determined by its transpose. -/
lemma vertex_hom_ext (c₀ : Cone D.F) {j : J} {X : D.StageSheaf j}
    {Y : (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}}
    {φ ψ : (conePullback c₀ j).obj X ⟶ Y}
    (h : (coneAdj c₀ j).unit.app X ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).map φ =
        (coneAdj c₀ j).unit.app X ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).map ψ) : φ = ψ :=
  ((coneAdj c₀ j).homEquiv X Y).injective
    (((coneAdj c₀ j).homEquiv_unit X Y φ).trans
      (h.trans ((coneAdj c₀ j).homEquiv_unit X Y ψ).symm))

/-- The identity law of the transition maps, transposed. -/
lemma vertexTransUnit_id (c₀ : Cone D.F) (A : D.AbelianSystem) (j : J) :
    A.vertexTransUnit c₀ (𝟙 j) = (coneAdj c₀ j).unit.app (A.sheaf j) :=
  (congrArg
      (fun z => A.pushSheaf (𝟙 j) ≫
        ((D.pushFunctor (𝟙 j)).map ((coneAdj c₀ j).unit.app (A.sheaf j)) ≫ z))
      (pushConeHom_id c₀ j ((conePullback c₀ j).obj (A.sheaf j)))).trans
    ((congrArg (fun z => A.pushSheaf (𝟙 j) ≫ z)
        ((D.pushIdHom j).naturality ((coneAdj c₀ j).unit.app (A.sheaf j)))).trans
      (((Category.assoc _ _ _).symm).trans
        ((congrArg (fun z => z ≫ (coneAdj c₀ j).unit.app (A.sheaf j)) (A.pushSheaf_id j)).trans
          (Category.id_comp _))))

/-- **The identity law of the pullback system on the vertex.** -/
lemma vertexTrans_id (c₀ : Cone D.F) (A : D.AbelianSystem) (j : J) :
    A.vertexTrans c₀ (𝟙 j) = 𝟙 ((conePullback c₀ j).obj (A.sheaf j)) :=
  vertex_hom_ext c₀
    ((A.unit_comp_map_vertexTrans c₀ (𝟙 j)).trans
      ((A.vertexTransUnit_id c₀ j).trans
        ((Category.comp_id _).symm.trans
          (congrArg (fun z => (coneAdj c₀ j).unit.app (A.sheaf j) ≫ z)
            (CategoryTheory.Functor.map_id
              (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j))
              ((conePullback c₀ j).obj (A.sheaf j))).symm))))

end AbelianSystem

/-! ### Two bookkeeping identities, stated over abstract categories -/

/-- The cocycle computation for the transition maps of the pullback system, with every category,
functor and object a variable. -/
theorem cocycle_aux {Sk Sj Si V : Type*} [Category Sk] [Category Sj] [Category Si] [Category V]
    {πk : V ⥤ Sk} {πj : V ⥤ Sj} {πi : V ⥤ Si} {Pa : Sj ⥤ Si} {Pb : Sk ⥤ Sj} {Pba : Sk ⥤ Si}
    (cmp : Pba ⟶ Pb ⋙ Pa) (κa : πj ⋙ Pa ⟶ πi) (κb : πk ⋙ Pb ⟶ πj) (κba : πk ⋙ Pba ⟶ πi)
    {Ak : Sk} {Aj : Sj} {Ai : Si} {Xk Xj : V}
    (psa : Ai ⟶ Pa.obj Aj) (psb : Aj ⟶ Pb.obj Ak) (psba : Ai ⟶ Pba.obj Ak)
    (uj : Aj ⟶ πj.obj Xj) (uk : Ak ⟶ πk.obj Xk) (tb : Xj ⟶ Xk)
    (h1 : psba ≫ cmp.app Ak = psa ≫ Pa.map psb)
    (h2 : κba.app Xk = cmp.app (πk.obj Xk) ≫ Pa.map (κb.app Xk) ≫ κa.app Xk)
    (h3 : uj ≫ πj.map tb = psb ≫ Pb.map uk ≫ κb.app Xk) :
    psba ≫ Pba.map uk ≫ κba.app Xk = (psa ≫ Pa.map uj ≫ κa.app Xj) ≫ πi.map tb := by
  have hc : Pba.map uk ≫ cmp.app (πk.obj Xk) = cmp.app Ak ≫ Pa.map (Pb.map uk) :=
    cmp.naturality uk
  have hκ : Pa.map (πj.map tb) ≫ κa.app Xk = κa.app Xj ≫ πi.map tb := κa.naturality tb
  calc psba ≫ Pba.map uk ≫ κba.app Xk
      = (psba ≫ cmp.app Ak) ≫ Pa.map (Pb.map uk) ≫ Pa.map (κb.app Xk) ≫ κa.app Xk := by
        rw [h2]
        simp only [Category.assoc]
        rw [← Category.assoc (Pba.map uk) (cmp.app (πk.obj Xk)), hc]
        simp only [Category.assoc]
    _ = psa ≫ Pa.map (psb ≫ Pb.map uk ≫ κb.app Xk) ≫ κa.app Xk := by
        rw [h1]
        simp only [Functor.map_comp, Category.assoc]
    _ = psa ≫ Pa.map uj ≫ Pa.map (πj.map tb) ≫ κa.app Xk := by
        rw [← h3]
        simp only [Functor.map_comp, Category.assoc]
    _ = (psa ≫ Pa.map uj ≫ κa.app Xj) ≫ πi.map tb := by
        rw [hκ]
        simp only [Category.assoc]

/-- The naturality computation for the transition maps of the pullback system, with every
category, functor and object a variable. -/
theorem naturality_aux {Sj Si V : Type*} [Category Sj] [Category Si] [Category V]
    {πj : V ⥤ Sj} {πi : V ⥤ Si} {Pa : Sj ⥤ Si} (κa : πj ⋙ Pa ⟶ πi)
    {Aj Bj : Sj} {Ai Bi : Si} {XA XB : V}
    (psaA : Ai ⟶ Pa.obj Aj) (psaB : Bi ⟶ Pa.obj Bj)
    (ujA : Aj ⟶ πj.obj XA) (ujB : Bj ⟶ πj.obj XB)
    (αj : Aj ⟶ Bj) (αi : Ai ⟶ Bi) (q : XA ⟶ XB)
    (h1 : psaA ≫ Pa.map αj = αi ≫ psaB)
    (h2 : ujA ≫ πj.map q = αj ≫ ujB) :
    (psaA ≫ Pa.map ujA ≫ κa.app XA) ≫ πi.map q = αi ≫ psaB ≫ Pa.map ujB ≫ κa.app XB := by
  have hκ : Pa.map (πj.map q) ≫ κa.app XB = κa.app XA ≫ πi.map q := κa.naturality q
  calc (psaA ≫ Pa.map ujA ≫ κa.app XA) ≫ πi.map q
      = psaA ≫ Pa.map (ujA ≫ πj.map q) ≫ κa.app XB := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
        rw [hκ]
    _ = (psaA ≫ Pa.map αj) ≫ Pa.map ujB ≫ κa.app XB := by
        rw [h2]
        simp only [Functor.map_comp, Category.assoc]
    _ = αi ≫ psaB ≫ Pa.map ujB ≫ κa.app XB := by
        rw [h1]
        simp only [Category.assoc]

/-! ### The pullback system, functorially in the system -/

namespace AbelianSystem

/-- The cocycle law of the transition maps, transposed. -/
lemma vertexTransUnit_comp (c₀ : Cone D.F) (A : D.AbelianSystem) {k j i : J} (b : k ⟶ j)
    (a : j ⟶ i) :
    A.vertexTransUnit c₀ (b ≫ a) =
      A.vertexTransUnit c₀ a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map (A.vertexTrans c₀ b) :=
  cocycle_aux (D.pushCompHom b a) (pushConeHom c₀ a) (pushConeHom c₀ b)
    (pushConeHom c₀ (b ≫ a)) (A.pushSheaf a) (A.pushSheaf b) (A.pushSheaf (b ≫ a))
    ((coneAdj c₀ j).unit.app (A.sheaf j)) ((coneAdj c₀ k).unit.app (A.sheaf k))
    (A.vertexTrans c₀ b) (A.pushSheaf_comp b a)
    (pushConeHom_comp c₀ b a ((conePullback c₀ k).obj (A.sheaf k)))
    (A.unit_comp_map_vertexTrans c₀ b)

/-- **The cocycle law of the pullback system on the vertex.** -/
lemma vertexTrans_comp (c₀ : Cone D.F) (A : D.AbelianSystem) {k j i : J} (b : k ⟶ j) (a : j ⟶ i) :
    A.vertexTrans c₀ (b ≫ a) = A.vertexTrans c₀ a ≫ A.vertexTrans c₀ b :=
  vertex_hom_ext c₀ (by
    rw [unit_comp_map_vertexTrans, vertexTransUnit_comp, CategoryTheory.Functor.map_comp,
      ← Category.assoc, unit_comp_map_vertexTrans])

/-- **The pullback system `k ↦ pₖ⁻¹𝒜ₖ` on the vertex of a cone of the spaces.** -/
def vertexSystem (c₀ : Cone D.F) (A : D.AbelianSystem) :
    Jᵒᵖ ⥤ (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} where
  obj j := (conePullback c₀ j.unop).obj (A.sheaf j.unop)
  map α := A.vertexTrans c₀ α.unop
  map_id j := A.vertexTrans_id c₀ j.unop
  map_comp α β := A.vertexTrans_comp c₀ β.unop α.unop

/-- Transposing a composite out of a transition map. -/
lemma unit_comp_map_vertexTrans_comp (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J} (a : j ⟶ i)
    {Y : (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}}
    (g : (conePullback c₀ j).obj (A.sheaf j) ⟶ Y) :
    (coneAdj c₀ i).unit.app (A.sheaf i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map (A.vertexTrans c₀ a ≫ g) =
      A.vertexTransUnit c₀ a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map g := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, A.unit_comp_map_vertexTrans c₀ a]

/-- Transposing a transition map composed after a map of systems. -/
lemma unit_comp_map_comp_vertexTrans (c₀ : Cone D.F) {A B : D.AbelianSystem} (α : A ⟶ B)
    {j i : J} (a : j ⟶ i) :
    (coneAdj c₀ i).unit.app (A.sheaf i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          ((conePullback c₀ i).map (α.app i) ≫ B.vertexTrans c₀ a) =
      α.app i ≫ B.vertexTransUnit c₀ a := by
  have hnat : (coneAdj c₀ i).unit.app (A.sheaf i) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
        ((conePullback c₀ i).map (α.app i)) =
      α.app i ≫ (coneAdj c₀ i).unit.app (B.sheaf i) :=
    ((coneAdj c₀ i).unit.naturality (α.app i)).symm
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hnat, Category.assoc,
    B.unit_comp_map_vertexTrans c₀ a]

/-- **The transition maps are natural in the system.** -/
lemma vertexTrans_naturality (c₀ : Cone D.F) {A B : D.AbelianSystem} (α : A ⟶ B) {j i : J}
    (a : j ⟶ i) :
    A.vertexTrans c₀ a ≫ (conePullback c₀ j).map (α.app j) =
      (conePullback c₀ i).map (α.app i) ≫ B.vertexTrans c₀ a :=
  vertex_hom_ext c₀
    ((A.unit_comp_map_vertexTrans_comp c₀ a ((conePullback c₀ j).map (α.app j))).trans
      ((naturality_aux (pushConeHom c₀ a) (A.pushSheaf a) (B.pushSheaf a)
          ((coneAdj c₀ j).unit.app (A.sheaf j)) ((coneAdj c₀ j).unit.app (B.sheaf j))
          (α.app j) (α.app i) ((conePullback c₀ j).map (α.app j)) (α.push_app a)
          ((coneAdj c₀ j).unit.naturality (α.app j)).symm).trans
        (unit_comp_map_comp_vertexTrans c₀ α a).symm))

/-- The pullback system, functorially in the system. -/
def vertexSystemFunctor (c₀ : Cone D.F) :
    D.AbelianSystem ⥤ (Jᵒᵖ ⥤ (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u}) where
  obj A := A.vertexSystem c₀
  map α :=
    { app := fun j => (conePullback c₀ j.unop).map (α.app j.unop)
      naturality := fun _ _ β => vertexTrans_naturality c₀ α β.unop }
  map_id A := NatTrans.ext (funext fun j =>
    CategoryTheory.Functor.map_id (conePullback c₀ j.unop) (A.sheaf j.unop))
  map_comp α β := NatTrans.ext (funext fun j =>
    CategoryTheory.Functor.map_comp (conePullback c₀ j.unop) (α.app j.unop) (β.app j.unop))

/-- **The vertex functor `𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ`** on the category of systems. -/
def vertexFunctor (c₀ : Cone D.F) :
    D.AbelianSystem ⥤ (c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} :=
  vertexSystemFunctor c₀ ⋙ colim

/-- The value of the vertex functor is the colimit of the pullback system, by definition. -/
lemma vertexFunctor_obj (c₀ : Cone D.F) (A : D.AbelianSystem) :
    (vertexFunctor c₀).obj A = colimit (A.vertexSystem c₀) := rfl

/-- The `k`-th object of the pullback system is the inverse image of the `k`-th sheaf along the
`k`-th leg of the cone, by definition. -/
lemma vertexSystem_obj (c₀ : Cone D.F) (A : D.AbelianSystem) (k : J) :
    (A.vertexSystem c₀).obj (op k) =
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (c₀.π.app k)).obj (A.sheaf k) := rfl

/-- **Objectwise, the pullback system built here is the germ-model system
`SpectralDiagram.AbelianSystem.germSystem`**, by `GermPullback.abelianSheafPullbackIso`: the
abelian germ model is Mathlib's inverse image.  These isomorphisms are compatible with the
transition maps of the two systems, which is
`SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj_naturality` below. -/
def vertexSystemObjIsoGermSystemObj (c₀ : Cone D.F) (A : D.AbelianSystem) (k : J) :
    (A.vertexSystem c₀).obj (op k) ≅ (A.germSystem c₀).obj (op k) :=
  GermPullback.abelianSheafPullbackIso (g := c₀.π.app k) (A.sheaf k)

/-- The unit at `𝒜ⱼ`, followed by the objectwise germ-model comparison, is the germ-model unit. -/
private lemma unit_comp_map_vertexSystemObjIsoGermSystemObj_hom (c₀ : Cone D.F)
    (A : D.AbelianSystem) (j : J) :
    (coneAdj c₀ j).unit.app (A.sheaf j) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).map
        (A.vertexSystemObjIsoGermSystemObj c₀ j).hom =
      GermPullback.toPushforward (c₀.π.app j) (A.sheaf j) :=
  GermPullback.unit_comp_map_abelianSheafPullbackComparison (c₀.π.app j) (A.sheaf j)

/-- The transposed transition map of the pullback system, followed by the germ-model comparison at
the stage `j`, is the `f`-map of the system followed by the germ-model unit and the cone
comparison.  This is the naturality of `SpectralDiagram.pushConeHom` together with the defining
property of the comparison, `GermPullback.unit_comp_map_abelianSheafPullbackComparison`. -/
lemma vertexTransUnit_comp_map_germIso (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J}
    (a : j ⟶ i) :
    A.vertexTransUnit c₀ a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          (A.vertexSystemObjIsoGermSystemObj c₀ j).hom =
      A.pushSheaf a ≫
        (D.pushFunctor a).map (GermPullback.toPushforward (c₀.π.app j) (A.sheaf j)) ≫
          (pushConeHom c₀ a).app ((A.germSystem c₀).obj (op j)) := by
  have hnat : (D.pushFunctor a).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).map
          (A.vertexSystemObjIsoGermSystemObj c₀ j).hom) ≫
        (pushConeHom c₀ a).app ((A.germSystem c₀).obj (op j)) =
      (pushConeHom c₀ a).app ((conePullback c₀ j).obj (A.sheaf j)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          (A.vertexSystemObjIsoGermSystemObj c₀ j).hom :=
    (pushConeHom c₀ a).naturality _
  have hmap : (D.pushFunctor a).map ((coneAdj c₀ j).unit.app (A.sheaf j)) ≫
      (D.pushFunctor a).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app j)).map
        (A.vertexSystemObjIsoGermSystemObj c₀ j).hom) =
      (D.pushFunctor a).map (GermPullback.toPushforward (c₀.π.app j) (A.sheaf j)) :=
    (CategoryTheory.Functor.map_comp (D.pushFunctor a) _ _).symm.trans
      (congrArg (D.pushFunctor a).map
        (A.unit_comp_map_vertexSystemObjIsoGermSystemObj_hom c₀ j))
  rw [vertexTransUnit, Category.assoc, Category.assoc, ← hnat]
  exact congrArg (fun z => A.pushSheaf a ≫ z)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ (pushConeHom c₀ a).app ((A.germSystem c₀).obj (op j))) hmap))

/-- **The transition map of the germ-model system, transposed.**  The `f`-map of the system
followed by the germ-model unit at the stage `j` and the cone comparison is the germ-model unit at
the stage `i` followed by the transition map of the germ-model system: the left-hand side is
`SheafedSpaceLimit.transUnit`, after `SpectralDiagram.pushConeHom_app_hom` identifies the cone
comparison with the `eqToHom` that `transUnit` carries, and the right-hand side is the defining
property `GermPullback.toPushforwardPresheaf_comp_mapOut` of
`SheafedSpaceLimit.trans`. -/
lemma pushSheaf_comp_map_toPushforward (c₀ : Cone D.F) (A : D.AbelianSystem) {j i : J}
    (a : j ⟶ i) :
    A.pushSheaf a ≫
        (D.pushFunctor a).map (GermPullback.toPushforward (c₀.π.app j) (A.sheaf j)) ≫
          (pushConeHom c₀ a).app ((A.germSystem c₀).obj (op j)) =
      GermPullback.toPushforward (c₀.π.app i) (A.sheaf i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          ((A.germSystem c₀).map a.op) :=
  InducedCategory.Hom.ext
    ((congrArg (fun z => (A.push a ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (D.F.map a)).map
          (GermPullback.toPushforwardPresheaf (c₀.π.app j) (A.sheaf j).presheaf)) ≫ z)
      (pushConeHom_app_hom c₀ a ((A.germSystem c₀).obj (op j)))).trans
      (GermPullback.toPushforwardPresheaf_comp_mapOut (c₀.π.app i)
        (Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit.transUnit (A.baseCone c₀) a)
        ((A.germSystem c₀).obj (op j)).2).symm)

/-- **The two systems on the vertex agree, not merely their objects**: the objectwise comparison
`SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj` of the pullback system with the
germ-model system commutes with the transition maps, so the two systems are isomorphic and
`colimit (A.vertexSystem c₀)` is the sheaf `(A.cone c₀).pt.sheaf` that the vertex theory
speaks about.

Both sides are morphisms out of `pᵢ⁻¹𝒜ᵢ`, so `SpectralDiagram.AbelianSystem.vertex_hom_ext`
reduces the claim to their transposes, and there it is the two lemmas above. -/
theorem vertexSystemObjIsoGermSystemObj_naturality (c₀ : Cone D.F) (A : D.AbelianSystem)
    {j i : J} (a : j ⟶ i) :
    A.vertexTrans c₀ a ≫ (A.vertexSystemObjIsoGermSystemObj c₀ j).hom =
      (A.vertexSystemObjIsoGermSystemObj c₀ i).hom ≫ (A.germSystem c₀).map a.op := by
  refine vertex_hom_ext c₀ ?_
  have hR : (coneAdj c₀ i).unit.app (A.sheaf i) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
        ((A.vertexSystemObjIsoGermSystemObj c₀ i).hom ≫ (A.germSystem c₀).map a.op) =
      GermPullback.toPushforward (c₀.π.app i) (A.sheaf i) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          ((A.germSystem c₀).map a.op) :=
    (congrArg (fun z => (coneAdj c₀ i).unit.app (A.sheaf i) ≫ z)
        (CategoryTheory.Functor.map_comp
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i))
          (A.vertexSystemObjIsoGermSystemObj c₀ i).hom ((A.germSystem c₀).map a.op))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (c₀.π.app i)).map
          ((A.germSystem c₀).map a.op))
          (A.unit_comp_map_vertexSystemObjIsoGermSystemObj_hom c₀ i)))
  exact (A.unit_comp_map_vertexTrans_comp c₀ a _).trans
    (((A.vertexTransUnit_comp_map_germIso c₀ a).trans
      (A.pushSheaf_comp_map_toPushforward c₀ a)).trans hR.symm)

/-- **The pullback system on the vertex and the germ-model system are isomorphic as systems.**
Its components are `SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj` and its
naturality is `SpectralDiagram.AbelianSystem.vertexSystemObjIsoGermSystemObj_naturality`. -/
def vertexSystemIsoGermSystem (c₀ : Cone D.F) (A : D.AbelianSystem) :
    A.vertexSystem c₀ ≅ A.germSystem c₀ :=
  NatIso.ofComponents (fun k => A.vertexSystemObjIsoGermSystemObj c₀ k.unop)
    fun {_k _l} α => A.vertexSystemObjIsoGermSystemObj_naturality c₀ α.unop

/-- **The vertex functor computes the sheaf on the vertex of the limiting cone of the system**:
`colimⱼ pⱼ⁻¹𝒜ⱼ`, built here from Mathlib's inverse image, is the sheaf
`SpectralDiagram.AbelianSystem.cone` carries on the vertex, which is where the vertex
theory of [Stacks, Tag 0A37] — the Čech acyclicity and the positive-degree vanishing — lives.

This is the identification that the implementation notes of
`Topology/Sheaves/Cohomology/SpectralSpaceLimit/DegreeZero.lean` record as the one thing still
owed on the limit side of the degree induction.  Both halves of it are definitional unfoldings
(`vertexFunctor_obj` and `SpectralDiagram.AbelianSystem.cone_pt_sheaf`) around
`CategoryTheory.Limits.HasColimit.isoOfNatIso` of `vertexSystemIsoGermSystem`. -/
def vertexFunctorObjIsoConePtSheaf (c₀ : Cone D.F) (A : D.AbelianSystem) :
    (vertexFunctor c₀).obj A ≅ (A.cone c₀).pt.sheaf :=
  HasColimit.isoOfNatIso (A.vertexSystemIsoGermSystem c₀)

/-- The identification of the previous declaration read on the legs of the two colimits: the
`k`-th leg of the pullback system, followed by it, is the germ-model comparison at `k` followed by
the `k`-th leg of the germ-model system. -/
@[reassoc]
lemma ι_comp_vertexFunctorObjIsoConePtSheaf_hom (c₀ : Cone D.F) (A : D.AbelianSystem) (k : Jᵒᵖ) :
    colimit.ι (A.vertexSystem c₀) k ≫ (A.vertexFunctorObjIsoConePtSheaf c₀).hom =
      (A.vertexSystemObjIsoGermSystemObj c₀ k.unop).hom ≫ colimit.ι (A.germSystem c₀) k :=
  HasColimit.ι_isoOfNatIso_hom (A.vertexSystemIsoGermSystem c₀) k

/-- Evaluating the pullback-system functor at a stage is the inverse image of the evaluation at
that stage, on the nose.  This is what carries the exactness of the two factors to the functor. -/
lemma vertexSystemFunctor_comp_evaluation (c₀ : Cone D.F) (k : Jᵒᵖ) :
    vertexSystemFunctor (D := D) c₀ ⋙ (evaluation Jᵒᵖ
        ((c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u})).obj k =
      D.ev k.unop ⋙ conePullback c₀ k.unop := rfl

/-- The pullback-system functor preserves finite limits. -/
instance vertexSystemFunctor_preservesFiniteLimits (c₀ : Cone D.F) :
    PreservesFiniteLimits (vertexSystemFunctor (D := D) c₀) := by
  refine ⟨fun K _ _ => preservesLimitsOfShape_of_evaluation _ K fun k => ?_⟩
  have : PreservesFiniteLimits (conePullback c₀ k.unop) :=
    Stacks.Cohomology.AbelianColimit.sheafPullback_preservesFiniteLimits (c₀.π.app k.unop)
  have : PreservesFiniteLimits (D.ev k.unop ⋙ conePullback c₀ k.unop) :=
    comp_preservesFiniteLimits _ _
  exact inferInstanceAs (PreservesLimitsOfShape K (D.ev k.unop ⋙ conePullback c₀ k.unop))

/-- The pullback-system functor preserves finite colimits. -/
instance vertexSystemFunctor_preservesFiniteColimits (c₀ : Cone D.F) :
    PreservesFiniteColimits (vertexSystemFunctor (D := D) c₀) := by
  refine ⟨fun K _ _ => preservesColimitsOfShape_of_evaluation _ K fun k => ?_⟩
  have : PreservesFiniteColimits (conePullback c₀ k.unop) := inferInstance
  have : PreservesFiniteColimits (D.ev k.unop ⋙ conePullback c₀ k.unop) :=
    comp_preservesFiniteColimits _ _
  exact preservesColimitsOfShape_of_natIso
    (Iso.refl (D.ev k.unop ⋙ conePullback c₀ k.unop) :
      D.ev k.unop ⋙ conePullback c₀ k.unop ≅
        vertexSystemFunctor (D := D) c₀ ⋙ (evaluation Jᵒᵖ
          ((c₀.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u})).obj k)

/-- The vertex functor `𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ` preserves finite limits. -/
instance vertexFunctor_preservesFiniteLimits (c₀ : Cone D.F) :
    PreservesFiniteLimits (vertexFunctor (D := D) c₀) :=
  comp_preservesFiniteLimits _ _

/-- The vertex functor `𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ` preserves finite colimits. -/
instance vertexFunctor_preservesFiniteColimits (c₀ : Cone D.F) :
    PreservesFiniteColimits (vertexFunctor (D := D) c₀) :=
  comp_preservesFiniteColimits _ _

/-- The vertex functor `𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ` is additive. -/
instance vertexFunctor_additive (c₀ : Cone D.F) : (vertexFunctor (D := D) c₀).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (vertexFunctor (D := D) c₀)
  Functor.additive_of_preservesBinaryBiproducts _

end AbelianSystem

end SpectralDiagram

end
