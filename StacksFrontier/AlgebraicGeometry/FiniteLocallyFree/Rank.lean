module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of a finite locally free sheaf and of a finite locally free morphism

Finite local freeness of a fixed rank is transported along isomorphisms, both for sheaves of
modules and for morphisms of schemes. A free sheaf on an index type of cardinality `r` has
rank `r`, the structure sheaf has rank `1`, and an isomorphism of schemes is finite locally
free of rank `1`.

On a ringed space whose structure sheaf has nonzero stalks the rank of a locally free sheaf of
modules is moreover a single locally constant function, not merely a rank at each point:
`LocallyFreeRank.locallyFreeRank` bundles the witness of [Stacks, Tag 01C9] as a `LocallyConstant`
function.

## Main definitions

* `LocallyFreeRank.locallyFreeRank`: the bundled locally constant rank function of a locally
  free sheaf of modules.
* `LocallyFreeRank.trivializationOfLocalGenerators`: the trivialisation carried by a member of
  the local-generator data of a locally free sheaf of modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv`: a free sheaf on an
  index type equivalent to `Fin r` is finite locally free of rank `r`.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit`: the structure sheaf is
  finite locally free of rank `1`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso`: an isomorphism of schemes is
  finite locally free of rank `1`.
* `LocallyFreeRank.isLocallyFree_on_openNeighborhoods`: the site-theoretic notion of local freeness
  of [Stacks, Tag 01C6] provides local trivialisations on open neighbourhoods.
* `LocallyFreeRank.trivialization_rank_eq_locallyFreeRank`: the index set of any local
  trivialisation through a point has cardinality the rank at that point.
* `LocallyFreeRank.locallyFreeRank_eq_mk_generators`: the same identification stated for a
  member of a local-generator presentation.
* `LocallyFreeRank.scheme_stalksNontrivial`: the structure sheaf of a scheme has nonzero
  stalks, so the rank of a locally free sheaf of modules on a scheme is always defined.
* `LocallyFreeRank.restrictIsoFreeOfGeneratingSections` and
  `LocallyFreeRank.isoOverPullbackOpen` exhibit a sheaf of modules as free on an open carrying
  invertible generating sections, and transport such a presentation to an open subscheme;
  `LocallyFreeRank.pullbackOpenIso` is their composite along a member of a presentation.

## Implementation notes

The informal codomain "a natural number or infinity" of the rank function is represented by
`Cardinal`, which retains the exact cardinality of an infinite local basis; the full-support
hypothesis of the source is expressed equivalently as nontriviality of every stalk of the
structure sheaf, `LocallyFreeRank.StalksNontrivial`.

The rank function is obtained from the existential `LocallyFreeRank.exists_locallyConstant_rank`,
so it is `Classical.choice` of a witness and only its specification is available. That
specification is `trivialization_rank_eq_locallyFreeRank`, which pins the value at every point
against every trivialisation through it, and is therefore enough to characterise the function
uniquely.

`restrictIsoFreeOfGeneratingSections` takes the generating sections themselves rather than an
index into a presentation. Phrasing it that way keeps the open a genuine variable, so each of
the three isomorphisms it composes can be ascribed its own type and elaborated on its own; the
same construction stated against the member `q.X i` of a presentation needs an auxiliary
equation and a substitution, and then elaborates as one block whose unifier cost is large.

`hasSheafify_overOpens` and `wEqualsLocallyBijective_overOpens` are stated for a variable open and
applied by name: the site `Over W` has its objects and its morphisms in different universes, so the
instances are found through essential smallness, and instance search for them at a *compound* open
— a member `q.X i` of a local-generator presentation — exhausts the synthesis budget. With the open
a genuine variable the same search succeeds at once, and the result then transports to any open.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The one-element type is equivalent to `Fin 1`. -/
def punitEquivFinOne : PUnit.{u + 1} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

/-- The free sheaf of modules on an index type of cardinality `r` is finite locally free of
rank `r`. -/
theorem SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv {X : Scheme.{u}} (I : Type u)
    (r : ℕ) (e : I ≃ Fin r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I) r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
    (M := _root_.SheafOfModules.free (R := X.ringCatSheaf) I) (r := r)
    ⟨(_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData,
      inferInstance, fun _ ↦ ⟨e⟩⟩

/-- The structure sheaf of a scheme, viewed as a module over itself, is finite locally free of
rank `1`: it is the free module on a one-element index type. -/
theorem SheafOfModules.isFiniteLocallyFreeOfRank_unit (X : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (_root_.SheafOfModules.unit X.ringCatSheaf) 1 :=
  let e : _root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit X.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ _root_.SheafOfModules.unit X.ringCatSheaf)
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e
    (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv PUnit.{u + 1} 1 punitEquivFinOne)

end AlgebraicGeometry

namespace Stacks.Morphisms

/-- An isomorphism of schemes is finite locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsFiniteLocallyFreeOfRank f 1 :=
  .mk (toIsAffineHom := inferInstance)
    (toIsFiniteLocallyFreeOfRank := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (pushforwardStructureSheafIsoUnit (asIso f)).symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_unit Y))

end Stacks.Morphisms

namespace LocallyFreeRank

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The trivialisation carried by a member of the local-generator data of a locally free sheaf
of modules: on `q.X i` the restriction of `F` is isomorphic to the free sheaf on the index type
of the `i`-th family of generators. -/
noncomputable def trivializationOfLocalGenerators
    (F : _root_.SheafOfModules.{u} (toRingSheaf X O))
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} F) (hq : q.IsLocallyFreeData) (i : q.I) :
    Trivialization X (toRingSheaf X O) F (q.X i) := by
  haveI : IsIso (q.generators i).π := hq.isIso i
  let U := q.X i
  let R := toRingSheaf X O
  let E := U.sheafOfModulesEquivOver R
  refine ⟨(q.generators i).I, ?_⟩
  exact (_root_.SheafOfModules.mapFreeIso E.functor (q.generators i).I
      (U.sheafOfModulesEquivOverUnit R) ≪≫
    E.functor.mapIso (asIso (q.generators i).π) ≪≫
    restrictModIsoOver X U R F).symm

/-- The site-theoretic notion of a locally free sheaf of modules provides local trivialisations
on open neighbourhoods. -/
theorem isLocallyFree_on_openNeighborhoods
    (F : _root_.SheafOfModules.{u} (toRingSheaf X O)) [F.IsLocallyFree] :
    IsLocallyFree X (toRingSheaf X O) F := by
  intro x
  obtain ⟨q, hq⟩ := (inferInstance : F.IsLocallyFree).exists_isLocallyFreeData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
  exact ⟨q.X i, hi, ⟨trivializationOfLocalGenerators F q hq i⟩⟩

/-- The rank of a locally free sheaf of modules on a ringed space whose structure sheaf has nonzero
stalks, as a locally constant `Cardinal`-valued function. Its value at a point is the cardinality
of the index set of any local trivialisation through that point. -/
@[ega "0 5.4.1", sga "6 I 6.0"]
noncomputable def locallyFreeRank (F : _root_.SheafOfModules.{u} (toRingSheaf X O))
    (hO : StalksNontrivial X O) [F.IsLocallyFree] :
    LocallyConstant X Cardinal.{u} :=
  let h := exists_locallyConstant_rank X O hO F (isLocallyFree_on_openNeighborhoods F)
  ⟨h.choose, h.choose_spec.1⟩

/-- The index set of any local trivialisation through a point has cardinality the rank at that
point. -/
theorem trivialization_rank_eq_locallyFreeRank
    (F : _root_.SheafOfModules.{u} (toRingSheaf X O))
    (hO : StalksNontrivial X O) [F.IsLocallyFree] (x : X) (U : Opens X) (hx : x ∈ U)
    (t : Trivialization X (toRingSheaf X O) F U) :
    t.rank = locallyFreeRank F hO x :=
  (exists_locallyConstant_rank X O hO F
    (isLocallyFree_on_openNeighborhoods F)).choose_spec.2 x U hx t

/-- On a member of a local-generator presentation of a locally free sheaf of modules, the rank
is the cardinality of that member's index set. -/
theorem locallyFreeRank_eq_mk_generators (F : _root_.SheafOfModules.{u} (toRingSheaf X O))
    (hO : StalksNontrivial X O) [F.IsLocallyFree]
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} F) (hq : q.IsLocallyFreeData) (i : q.I)
    (x : X) (hx : x ∈ q.X i) :
    locallyFreeRank F hO x = Cardinal.mk (q.generators i).I :=
  (trivialization_rank_eq_locallyFreeRank F hO x (q.X i) hx
    (trivializationOfLocalGenerators F q hq i)).symm

/-- The structure sheaf of a scheme has nonzero stalks, so the rank of a locally free sheaf of
modules on a scheme is always defined. -/
theorem scheme_stalksNontrivial (S : Scheme.{u}) : StalksNontrivial S.toTopCat S.sheaf := by
  intro x
  let _ : IsLocalRing (S.presheaf.stalk x) := S.isLocalRing x
  show Nontrivial (S.presheaf.stalk x)
  infer_instance

/-- The generating sections transported along an isomorphism out of a free sheaf of modules
still have an invertible evaluation morphism. -/
theorem isIso_equivOfIso_free_generatingSections_π {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u)
    {N : _root_.SheafOfModules.{u} R} (e : _root_.SheafOfModules.free I ≅ N) :
    IsIso (_root_.SheafOfModules.GeneratingSections.equivOfIso e
      (_root_.SheafOfModules.free.generatingSections I)).π := by
  have h : (_root_.SheafOfModules.GeneratingSections.equivOfIso e
      (_root_.SheafOfModules.free.generatingSections I)).π = e.hom :=
    (_root_.SheafOfModules.GeneratingSections.ofEpi_π _ _).trans
      (by rw [_root_.SheafOfModules.free.generatingSections_π]; exact Category.id_comp _)
  rw [h]
  exact e.isIso_hom

/-! ### Free presentations on opens of a scheme -/

section Scheme

variable {S : Scheme.{u}}

/-- Abelian presheaves on the slice of the site of opens of a scheme over an open can be
sheafified. -/
public theorem hasSheafify_overOpens (W : S.Opens) :
    HasSheafify ((Opens.grothendieckTopology (S : Type u)).over W) AddCommGrpCat.{u} :=
  inferInstance

/-- Sheafification of abelian presheaves on the slice of the site of opens of a scheme over an
open inverts exactly the locally bijective morphisms. -/
public theorem wEqualsLocallyBijective_overOpens (W : S.Opens) :
    ((Opens.grothendieckTopology (S : Type u)).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

/-- A set of generating sections of `F` over an open `W` whose evaluation morphism is invertible
exhibits the restriction of `F` to `W` as a free sheaf of modules on the index set of those
sections. -/
noncomputable def restrictIsoFreeOfGeneratingSections (F : S.Modules) (W : S.Opens)
    (σ : ((_root_.SheafOfModules.overFunctor S.ringCatSheaf W).obj F).GeneratingSections)
    (hσ : IsIso σ.π) :
    (Scheme.Modules.restrictFunctor W.ι).obj F ≅ _root_.SheafOfModules.free σ.I :=
  let E := Scheme.Modules.overEquiv W
  let e₁ : E.functor.obj ((_root_.SheafOfModules.overFunctor S.ringCatSheaf W).obj F) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj F := (Scheme.Modules.overFunctorEquiv W).app F
  let e₂ : E.functor.obj (_root_.SheafOfModules.free σ.I) ≅
      E.functor.obj ((_root_.SheafOfModules.overFunctor S.ringCatSheaf W).obj F) :=
    E.functor.mapIso (@asIso _ _ _ _ σ.π hσ)
  let hpres : Limits.PreservesColimitsOfShape.{u, u} (Discrete σ.I) E.functor :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} E.functor
  let e₃ : _root_.SheafOfModules.free σ.I ≅ E.functor.obj (_root_.SheafOfModules.free σ.I) :=
    @_root_.SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ E.functor σ.I hpres
      (Opens.sheafOfModulesEquivOverUnit W S.ringCatSheaf)
  e₁.symm ≪≫ e₂.symm ≪≫ e₃.symm

/-- Transporting a free presentation on an open `W` of `S` to the open `V` of an open subscheme
`U` of `S` that `W` cuts out. -/
noncomputable def isoOverPullbackOpen (U : S.Opens) (F : S.Modules) (W : S.Opens)
    (V : Scheme.Opens (U : Scheme)) (hV : V = (Opens.map U.ι.base).obj W) (I : Type u)
    (eW : Scheme.Modules.restrict F W.ι ≅ _root_.SheafOfModules.free I) :
    ((Scheme.Modules.pullback U.ι).obj F).over V ≅ _root_.SheafOfModules.free I := by
  let jV := Scheme.Opens.ι V
  let jU := Scheme.Opens.ι U
  let jW := Scheme.Opens.ι W
  have hsubset : Set.range (jV ≫ jU).base ⊆ Set.range jW.base := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    have hz : (z.1 : U) ∈ (Opens.map U.ι.base).obj W := by rw [← hV]; exact z.property
    change jU (jV z) ∈ W at hz
    exact ⟨⟨jU (jV z), hz⟩, rfl⟩
  let l : (V : Scheme) ⟶ (W : Scheme) := IsOpenImmersion.lift jW (jV ≫ jU) hsubset
  have hl : l ≫ jW = jV ≫ jU := IsOpenImmersion.lift_fac _ _ hsubset
  let t₁ := (Scheme.Modules.restrictFunctorIsoPullback jV).app
    ((Scheme.Modules.pullback jU).obj F)
  let t₂ := (Scheme.Modules.pullbackComp jV jU).app F
  let t₃ := (Scheme.Modules.pullbackCongr hl.symm).app F
  let t₄ := (Scheme.Modules.pullbackComp l jW).symm.app F
  let t₅ := (Scheme.Modules.pullback l).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback jW).symm.app F)
  let η : _root_.SheafOfModules.unit _ ≅
      (Scheme.Modules.pullback l).obj (_root_.SheafOfModules.unit _) :=
    ((Scheme.Modules.restrictFunctorIsoPullback l).symm.app (_root_.SheafOfModules.unit _) ≪≫
      Scheme.Modules.restrictUnitIso l).symm
  haveI : (Scheme.Modules.pullback l).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction l).isLeftAdjoint
  letI : Limits.PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback l) :=
    (Scheme.Modules.pullbackPushforwardAdjunction l).leftAdjoint_preservesColimits
  letI : Limits.PreservesColimitsOfSize.{0, u} (Scheme.Modules.pullback l) :=
    Limits.preservesColimitsOfSize_shrink _
  letI : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) (Scheme.Modules.pullback l) :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1}
      (Scheme.Modules.pullback l)
  let eFree := @_root_.SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.pullback l) I
    (show Limits.PreservesColimitsOfShape.{u, u} (Discrete I) (Scheme.Modules.pullback l) from
      inferInstance)
    η
  let eRestr := t₁ ≪≫ t₂ ≪≫ t₃ ≪≫ t₄ ≪≫ t₅ ≪≫ (Scheme.Modules.pullback l).mapIso eW ≪≫
    eFree.symm
  let E := Scheme.Modules.overEquiv V
  let δ := (Scheme.Modules.overFunctorEquiv V).app ((Scheme.Modules.pullback U.ι).obj F)
  let θ := Opens.sheafOfModulesEquivOverUnit V (U : Scheme).ringCatSheaf
  haveI : E.functor.IsEquivalence := inferInstance
  haveI : E.inverse.IsEquivalence := inferInstance
  haveI : E.inverse.IsLeftAdjoint := inferInstance
  letI : Limits.PreservesColimitsOfSize.{u, u} E.inverse :=
    E.inverse.adjunction.leftAdjoint_preservesColimits
  letI : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) E.inverse :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} E.inverse
  let η' := E.unitIso.app (_root_.SheafOfModules.unit _) ≪≫ E.inverse.mapIso θ
  let eFree' := @_root_.SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    E.inverse I
    (show Limits.PreservesColimitsOfShape.{u, u} (Discrete I) E.inverse from inferInstance)
    η'
  exact E.unitIso.app _ ≪≫ E.inverse.mapIso δ ≪≫ E.inverse.mapIso eRestr ≪≫ eFree'.symm

/-- The restriction to an open `U` of a sheaf of modules is free, on the open that a member of a
local-generator presentation cuts out of `U`, on that member's index set. -/
noncomputable def pullbackOpenIso (F : S.Modules) (U : S.Opens)
    (q : F.LocalGeneratorsData) (hq : q.IsLocallyFreeData) (i : q.I) :=
  letI := hasSheafify_overOpens (q.X i)
  letI := wEqualsLocallyBijective_overOpens (q.X i)
  isoOverPullbackOpen U F (q.X i) ((Opens.map U.ι.base).obj (q.X i)) rfl (q.generators i).I
    (restrictIsoFreeOfGeneratingSections F (q.X i) (q.generators i) (hq.isIso i))

end Scheme

end LocallyFreeRank

end
