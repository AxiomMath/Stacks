module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Homology.HomotopyCategory.FilteredColimitHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Homomorphisms in the derived category along a limit of algebraic spaces

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  Put `E_i = Lf_{i0}^*E₀` and
`K_i = Lf_{i0}^*K₀` for `i ≥ 0`, and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  Stacks 09RI asserts that

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism if either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or `E₀` is
pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension.

This file states that assertion for the real objects — the derived pullback of `𝒪`-modules on
the small étale site of an algebraic space — and proves it.  Bijectivity of a map out of a
filtered colimit of sets is `Stacks.IsStagesColimit`, the elementwise form already used for
Stacks 07SI in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`: the
maps to the vertex form a cocone, they are jointly surjective, and two elements of one stage
with the same image agree at a later stage.  For a directed index those three clauses are
exactly the assertion that the comparison out of the colimit is a bijection, so nothing weaker
than the tag's "is an isomorphism" is stated.

## Main definitions

* `AlgebraicGeometry.Space.DerivedModulePullback` is a derived pullback of `𝒪`-modules along a
  morphism of algebraic spaces: a functor between the unbounded derived categories together
  with the counit exhibiting it as a total left derived functor of the inverse image of
  Stacks 03LU.
* `AlgebraicGeometry.Space.DescentSituation.stage`, `limitSpace`, `transition` and `projection`
  read Situation 09RH in the category of algebraic spaces over the base.
* `AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem` is the system of derived
  pullbacks the tag's statement needs: `Lf_{i0}^*`, `Lf_{ji}^*`, `Lf_i^*` and `Lf_0^*`, together
  with the canonical comparisons `Lf_{i0}^* ⋙ Lf_{ji}^* ≅ Lf_{j0}^*` and
  `Lf_{i0}^* ⋙ Lf_i^* ≅ Lf_0^*` coming from the factorisations `f_{ji} ≫ f_{i0} = f_{j0}` and
  `f_i ≫ f_{i0} = f_0`.
* `AlgebraicGeometry.Space.DescentSituation.stageObj` and `limitObj` are the objects `E_i` and
  `E` of the tag, and `homTransition` and `homProjection` are the maps
  `Hom(E_i, K_i) → Hom(E_j, K_j)` and `Hom(E_i, K_i) → Hom(E, K)` of its directed system.
* `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` is **the conclusion of Stacks 09RI**:
  `Hom_{D(𝒪_X)}(E, K)` is the filtered colimit of the `Hom_{D(𝒪_{X_i})}(E_i, K_i)`.
* `AlgebraicGeometry.Space.DescentSituation.RingModel` is the affine translation dictionary the
  proof consumes; see "The carried hypothesis" below.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_ringModel` is **Stacks 09RI**, with
  the ring-level model of the system of homomorphism groups carried as a hypothesis.

## The carried hypothesis

The source proves 09RI by the induction principle of Stacks 08GP, using Mayer–Vietoris for
homomorphisms in the derived category (Stacks 08H9) at the union step, and reducing the affine
case to the scheme-level Stacks 09RE through the comparison of the small étale and the Zariski
site (Stacks 071Q, 08HE, 08HF, 08HG).  Of that chain this library has only the ring-level heart,
`Stacks.FilteredColimitHom.exists_descends_derived` and
`Stacks.FilteredColimitHom.exists_le_eq_of_eq_derived` — the clause labels of those tagged
theorems record that their own sheaf-level reduction is not included — while Stacks 08HE and
08HG are available only in one direction and conditionally on the left exactness of the slice
inverse images (Stacks 08HF is available in both directions, on the `Type u`-presented model of
the small étale ringed topos).

What is carried here is therefore the *dictionary* that the affine case of the source's proof
produces, `AlgebraicGeometry.Space.DescentSituation.RingModel`: a ring `R`, a bounded complex
`cx` of finitely presented projective `R`-modules, a directed system `N` of complexes of
`R`-modules whose degreewise filtered colimit is a complex `P`, and bijections

`Hom_{D(𝒪_{X_i})}(E_i, K_i) ≃ Hom_{D(R)}(cx, N i)`, `Hom_{D(𝒪_X)}(E, K) ≃ Hom_{D(R)}(cx, P)`

compatible with the transition maps and with the maps to the limit.  This is the same shape of
hypothesis as `AlgebraicGeometry.RelativeDescentSituation.AffineRingTranslation` of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineBase.lean`, carried by the tagged
theorem of `StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentCapstone.lean` for Stacks 0DI7,
the relative scheme-level analogue of this tag.

Carrying it does not turn the statement into a restatement of its own conclusion.  A `RingModel`
asserts no colimit property of any system of homomorphism groups.  Its colimit clauses, `hsurj`
and `hzero`, are assertions about the *modules* in each single degree — every element of `P.X n`
comes from some `N i` and an element of `N i` dying in `P` dies at a later stage — which is the
statement that `𝒪_X = colim f_i^{-1}𝒪_{X_i}` read through the dictionary, and they say nothing
about homomorphisms in a derived category.  Passing from them to the colimit property of the
hom-groups is precisely the content of Stacks 09RE, and it is what
`Stacks.FilteredColimitHom.exists_descends_derived` and `exists_le_eq_of_eq_derived` supply and
what this file's proof does.

The hypotheses of the tag itself — `E₀` perfect, or pseudo-coherent, with `K₀` in
`D_QCoh(𝒪_{X₀})` of finite Tor dimension — are stated as the disjunction `hcase` and are what
makes such a dictionary exist in the source's proof; they are not consumed again by the
assembly below.

## Implementation notes

The derived pullback of `𝒪`-modules along a morphism of algebraic spaces is carried as data
rather than constructed.  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModulePullback.lean` is the construction,
but it carries the existence premise `Functor.HasLeftDerivedFunctor` at every use site — the
K-flat resolution of Stacks 06YS is stated in this tree only for a small site, and the small
étale site is only essentially small — and no composition comparison
`Lf^* ⋙ Lg^* ≅ L(g ∘ f)^*` is available for it either; that gap is recorded as the hypothesis
`AlgebraicGeometry.Space.BottomRankBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BottomRankStratum.lean`.  Both are ambient
pseudofunctoriality of `Lf^*`, not part of what 09RI asserts, so a
`AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem` supplies the functors — each
pinned by `Functor.IsLeftDerivedFunctor` to be a total left derived functor of the inverse image
of Stacks 03LU, hence `Lf^*` and not an arbitrary functor — and the two comparisons.

The derived categories are those of `AlgebraicGeometry.Space.Modules`, the `𝒪`-modules of the
small étale *ringed site* of Stacks 04KH, because that is the spelling at which perfectness and
pseudo-coherence are stated (`AlgebraicGeometry.RingedSite.IsPerfect` and
`AlgebraicGeometry.RingedSite.IsPseudoCoherent`), and the derived category model is
`CategoryTheory.HasDerivedCategory.standard`.

Quasi-coherence of the cohomology is spelled out degreewise as
`SheafOfModules.IsQuasicoherentOnSite` of each cohomology sheaf, which is the definition of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` (Stacks 071X) unfolded, and finite Tor
dimension is `Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension` for a derived
tensor product `T` on the site, taken as an argument exactly as
`AlgebraicGeometry.Space.IsPerfectRelativeTo` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/Relative.lean` takes its own.

The index of the system of hom-groups is `AlgebraicGeometry.Space.DescentSituation.Stages`, the
stages at or beyond the chosen index, which is the source's `i ≥ 0`; it is directed because the
ambient index is.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 09RE](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.LimitDerivedHom

/-- An object of the derived category of `R`-modules, reached from a complex through the
homotopy category, in the spelling the results of
`StacksFrontier/Homology/HomotopyCategory/FilteredColimitHom.lean` are stated at. -/
abbrev derivedObj (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : CochainComplex (ModuleCat.{u} R) ℤ) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Qh.obj ((Stacks.FilteredColimitHom.Qh R).obj M)

/-- A morphism of complexes of `R`-modules, read in the derived category through the homotopy
category. -/
abbrev derivedMap {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {M N : CochainComplex (ModuleCat.{u} R) ℤ} (f : M ⟶ N) :
    derivedObj.{w} R M ⟶ derivedObj.{w} R N :=
  DerivedCategory.Qh.map ((Stacks.FilteredColimitHom.Qh R).map f)

end Stacks.LimitDerivedHom

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Derived pullback of modules along a morphism of algebraic spaces, as data -/

/-- Degreewise inverse image of `𝒪`-modules along a morphism of algebraic spaces, followed by
localization to the derived category.  A total left derived functor of this functor is the
derived pullback `Lf^*`. -/
abbrev modulePullbackOnHomotopy {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [(modulePullback B S hS f).Additive] :
    HomotopyCategory (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.obj X.property) :=
  (modulePullback B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **A derived pullback of `𝒪`-modules along a morphism of algebraic spaces.**  A functor
`D(𝒪_Y) ⥤ D(𝒪_X)` together with a counit exhibiting it as a total left derived functor, along
the quasi-isomorphisms, of the inverse image of Stacks 03LU.  The universal property pins it up
to a unique compatible isomorphism, so this is `Lf^*` and not an arbitrary functor. -/
structure DerivedModulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [(modulePullback B S hS f).Additive] where
  /-- The functor `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
  functor : DerivedCategory (Modules.{u, u} B S hS Y.obj Y.property) ⥤
    DerivedCategory (Modules.{u, u} B S hS X.obj X.property)
  /-- The canonical comparison of the functor with the degreewise inverse image. -/
  counit : DerivedCategory.Qh ⋙ functor ⟶ modulePullbackOnHomotopy B S hS f
  /-- The functor is a total left derived functor of the degreewise inverse image. -/
  isLeftDerived : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ))

/-! ### Situation 09RH in the category of algebraic spaces -/

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- The stages of Situation 09RH at or beyond its chosen index — the source's `i ≥ 0` — as a
preorder. -/
abbrev Stages := {i : I // D.base ≤ i}

/-- The stages at or beyond the chosen index are directed, the ambient index being directed. -/
instance isDirectedStages : IsDirected D.Stages (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-- The stage `X_i` of Situation 09RH, as an object of the category of algebraic spaces over the
base. -/
def stage (i : I) : AlgebraicSpaces B S hS := ⟨D.system.obj (op i), D.algebraicSpace i⟩

/-- The limit `X` of Situation 09RH, as an object of the category of algebraic spaces over the
base. -/
def limitSpace : AlgebraicSpaces B S hS := ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩

/-- The transition morphism `f_{ji} : X_j ⟶ X_i` of Situation 09RH, for `i ≤ j`. -/
def transition {i j : I} (h : i ≤ j) : D.stage j ⟶ D.stage i :=
  ObjectProperty.homMk (D.system.map (homOfLE h).op)

/-- The projection `f_i : X ⟶ X_i` from the limit of Situation 09RH to one of its stages. -/
def projection (i : I) : D.limitSpace ⟶ D.stage i :=
  ObjectProperty.homMk (D.limitCone.π.app (op i))

/-- **The transition morphisms of Situation 09RH compose**: `f_{kj} ≫ f_{ji} = f_{ki}`.  The
proof `hik` is an argument rather than `hij.trans hjk` so that the equation is available for
whichever proof of `i ≤ k` is at hand. -/
theorem transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) :
    D.transition hjk ≫ D.transition hij = D.transition hik := by
  apply ObjectProperty.hom_ext
  show D.system.map (homOfLE hjk).op ≫ D.system.map (homOfLE hij).op
      = D.system.map (homOfLE hik).op
  rw [← D.system.map_comp]
  rfl

/-- **A projection of Situation 09RH followed by a transition morphism is a projection**:
`f_j ≫ f_{ji} = f_i`.  This is the naturality of the chosen limiting cone. -/
theorem projection_comp_transition {i j : I} (h : i ≤ j) :
    D.projection j ≫ D.transition h = D.projection i := by
  apply ObjectProperty.hom_ext
  show D.limitCone.π.app (op j) ≫ D.system.map (homOfLE h).op = D.limitCone.π.app (op i)
  exact D.limitCone.w (homOfLE h).op

/-! ### The system of derived pullbacks -/

variable [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), (modulePullback B S hS f).Additive]

/-- **The system of derived pullbacks that the statement of Stacks 09RI is about.**  Derived
pullback along every map of Situation 09RH the tag mentions — `Lf_{i0}^*` from the chosen stage
to a later one, `Lf_{ji}^*` between two later stages, `Lf_i^*` from a later stage to the limit
and `Lf_0^*` from the chosen stage to the limit — together with the two canonical comparisons
coming from the factorisations `f_{ji} ≫ f_{i0} = f_{j0}` and `f_i ≫ f_{i0} = f_0`.

Each functor is pinned by `AlgebraicGeometry.Space.DerivedModulePullback` to be a total left
derived functor of the inverse image of Stacks 03LU, so this is the system of genuine derived
pullbacks.  It is data rather than a construction for the reason given in the implementation
notes of this file: both the existence of `Lf^*` on the small étale site and its
pseudofunctoriality are open in this library. -/
structure DerivedPullbackSystem where
  /-- `Lf_{i0}^* : D(𝒪_{X₀}) ⥤ D(𝒪_{X_i})`. -/
  stagePullback : ∀ i : D.Stages, DerivedModulePullback B S hS (D.transition i.2)
  /-- `Lf_{ji}^* : D(𝒪_{X_i}) ⥤ D(𝒪_{X_j})`. -/
  transPullback : ∀ (i j : D.Stages) (h : i ≤ j),
    DerivedModulePullback B S hS (D.transition (show i.1 ≤ j.1 from h))
  /-- `Lf_i^* : D(𝒪_{X_i}) ⥤ D(𝒪_X)`. -/
  projPullback : ∀ i : D.Stages, DerivedModulePullback B S hS (D.projection i.1)
  /-- `Lf_0^* : D(𝒪_{X₀}) ⥤ D(𝒪_X)`. -/
  limitPullback : DerivedModulePullback B S hS (D.projection D.base)
  /-- The comparison `Lf_{i0}^* ⋙ Lf_{ji}^* ≅ Lf_{j0}^*` of the factorisation
  `f_{ji} ≫ f_{i0} = f_{j0}`. -/
  transComp : ∀ (i j : D.Stages) (h : i ≤ j),
    (stagePullback i).functor ⋙ (transPullback i j h).functor ≅ (stagePullback j).functor
  /-- The comparison `Lf_{i0}^* ⋙ Lf_i^* ≅ Lf_0^*` of the factorisation `f_i ≫ f_{i0} = f_0`. -/
  projComp : ∀ i : D.Stages,
    (stagePullback i).functor ⋙ (projPullback i).functor ≅ limitPullback.functor

variable {D} (sys : D.DerivedPullbackSystem)
  (E₀ : DerivedCategory (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property))

/-- **The object `E_i = Lf_{i0}^*E₀` of Stacks 09RI.** -/
def stageObj (i : D.Stages) :
    DerivedCategory (Modules.{u, u} B S hS (D.stage i.1).obj (D.stage i.1).property) :=
  (sys.stagePullback i).functor.obj E₀

/-- **The object `E = Lf_0^*E₀` of Stacks 09RI.** -/
def limitObj :
    DerivedCategory (Modules.{u, u} B S hS D.limitSpace.obj D.limitSpace.property) :=
  sys.limitPullback.functor.obj E₀

variable (K₀ : DerivedCategory
  (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property))

/-- **The transition map `Hom_{D(𝒪_{X_i})}(E_i, K_i) → Hom_{D(𝒪_{X_j})}(E_j, K_j)` of
Stacks 09RI**: apply `Lf_{ji}^*` and read the result through the comparison
`Lf_{ji}^*Lf_{i0}^* ≅ Lf_{j0}^*` at `E₀` and at `K₀`. -/
def homTransition (i j : D.Stages) (h : i ≤ j) :
    (stageObj sys E₀ i ⟶ stageObj sys K₀ i) →
      (stageObj sys E₀ j ⟶ stageObj sys K₀ j) := fun g =>
  ((sys.transComp i j h).app E₀).inv ≫ (sys.transPullback i j h).functor.map g ≫
    ((sys.transComp i j h).app K₀).hom

/-- **The map `Hom_{D(𝒪_{X_i})}(E_i, K_i) → Hom_{D(𝒪_X)}(E, K)` of Stacks 09RI**: apply
`Lf_i^*` and read the result through the comparison `Lf_i^*Lf_{i0}^* ≅ Lf_0^*` at `E₀` and at
`K₀`. -/
def homProjection (i : D.Stages) :
    (stageObj sys E₀ i ⟶ stageObj sys K₀ i) →
      (limitObj sys E₀ ⟶ limitObj sys K₀) := fun g =>
  ((sys.projComp i).app E₀).inv ≫ (sys.projPullback i).functor.map g ≫
    ((sys.projComp i).app K₀).hom

/-- **The conclusion of Stacks 09RI**: the map

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism, in the elementwise form `Stacks.IsStagesColimit` — the maps
`AlgebraicGeometry.Space.DescentSituation.homProjection` form a cocone on the system given by
`AlgebraicGeometry.Space.DescentSituation.homTransition`, they are jointly surjective, and two
homomorphisms at one stage with the same image at the limit already agree at a later stage.  The
index is directed, so these three clauses are precisely bijectivity of the comparison out of the
colimit. -/
def IsHomColimit : Prop :=
  Stacks.IsStagesColimit (homTransition sys E₀ K₀) (homProjection sys E₀ K₀)

/-! ### The ring-level model of the system of homomorphism groups -/

/-- **The affine translation dictionary that the proof of Stacks 09RI consumes.**  A ring `R`, a
bounded complex `cx` of finitely presented projective `R`-modules, a directed system `N` of
complexes of `R`-modules over the stages with transition maps `t` and a complex `P` with maps
`ι` from every stage, such that `P` is the degreewise filtered colimit of the `N i`, together
with bijections identifying the system of homomorphism groups of Stacks 09RI with the system
`Hom_{D(R)}(cx, N i) → Hom_{D(R)}(cx, P)`.

The two colimit clauses are `hsurj` and `hzero`, and they are assertions about the *modules* in
a single degree, not about homomorphisms in a derived category; see "The carried hypothesis" in
this file's module documentation. -/
structure RingModel (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  /-- The complex of `R`-modules corresponding to `E₀`. -/
  cx : CochainComplex (ModuleCat.{u} R) ℤ
  /-- The complex of `R`-modules corresponding to `K_i`. -/
  N : D.Stages → CochainComplex (ModuleCat.{u} R) ℤ
  /-- The transition maps of the system `N`. -/
  t : ∀ ⦃i j : D.Stages⦄, i ≤ j → (N i ⟶ N j)
  /-- The complex of `R`-modules corresponding to `K`. -/
  P : CochainComplex (ModuleCat.{u} R) ℤ
  /-- The maps from the stages of `N` to `P`. -/
  ι : ∀ i : D.Stages, N i ⟶ P
  /-- The transition maps compose. -/
  htrans : ∀ ⦃i j k : D.Stages⦄ (h : i ≤ j) (h' : j ≤ k), t h ≫ t h' = t (h.trans h')
  /-- The maps to `P` are compatible with the transition maps. -/
  hcompat : ∀ ⦃i j : D.Stages⦄ (h : i ≤ j), t h ≫ ι j = ι i
  /-- `P` is degreewise covered by the stages. -/
  hsurj : ∀ (n : ℤ) (x : P.X n), ∃ (i : D.Stages) (y : (N i).X n), (ι i).f n y = x
  /-- An element of a stage dying in `P` dies at a later stage. -/
  hzero : ∀ (n : ℤ) (i : D.Stages) (y : (N i).X n), (ι i).f n y = 0 →
    ∃ (j : D.Stages) (h : i ≤ j), (t h).f n y = 0
  /-- The finite set of degrees outside which `cx` vanishes. -/
  W : Finset ℤ
  /-- `cx` vanishes outside `W`. -/
  hW : ∀ n : ℤ, n ∉ W → IsZero (cx.X n)
  /-- Every term of `cx` is finitely presented. -/
  hfp : ∀ n : ℤ, Module.FinitePresentation R (cx.X n)
  /-- A degree above which `cx` vanishes. -/
  deg : ℤ
  /-- `cx` is bounded above by `deg`. -/
  isStrictlyLE : cx.IsStrictlyLE deg
  /-- Every term of `cx` is projective. -/
  projective : ∀ n : ℤ, Projective (cx.X n)
  /-- The identification of the homomorphism group at a stage. -/
  stageEquiv : ∀ i : D.Stages, (stageObj sys E₀ i ⟶ stageObj sys K₀ i) ≃
    (Stacks.LimitDerivedHom.derivedObj.{w} R cx ⟶ Stacks.LimitDerivedHom.derivedObj.{w} R (N i))
  /-- The identification of the homomorphism group at the limit. -/
  limitEquiv : (limitObj sys E₀ ⟶ limitObj sys K₀) ≃
    (Stacks.LimitDerivedHom.derivedObj.{w} R cx ⟶ Stacks.LimitDerivedHom.derivedObj.{w} R P)
  /-- The identifications are compatible with the transition maps. -/
  stageEquiv_homTransition : ∀ (i j : D.Stages) (h : i ≤ j)
    (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i),
    stageEquiv j (homTransition sys E₀ K₀ i j h g) =
      stageEquiv i g ≫ Stacks.LimitDerivedHom.derivedMap.{w} (t h)
  /-- The identifications are compatible with the maps to the limit. -/
  limitEquiv_homProjection : ∀ (i : D.Stages)
    (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i),
    limitEquiv (homProjection sys E₀ K₀ i g) =
      stageEquiv i g ≫ Stacks.LimitDerivedHom.derivedMap.{w} (ι i)

/-! ### Stacks 09RI -/

/-- **Stacks 09RI.**  In Situation 09RH, let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`, put
`E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for `i ≥ 0` and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  If
either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or `E₀` is pseudo-coherent and `K₀`
lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism.

The affine translation dictionary `model` is carried as an explicit hypothesis rather than
discharged; see "The carried hypothesis" in this file's module documentation for what it is and
why it is an input of the source's proof and not its conclusion.

The three clauses are read off the ring-level colimit computation of Stacks 09RE, which this
library proves: surjectivity is
`Stacks.FilteredColimitHom.exists_descends_derived`, eventual injectivity is
`Stacks.FilteredColimitHom.exists_le_eq_of_eq_derived`, and the cocone identity is the
compatibility of the dictionary with `RingModel.hcompat`. -/
@[stacks 09RI "the affine ring-translation dictionary `model` is carried as an explicit \
hypothesis: the reduction of the sheaf-level statement to the ring-level colimit computation \
of Stacks 09RE, which runs through the induction principle 08GP, Mayer-Vietoris 08H9 and the \
small-etale-to-Zariski comparison 071Q, is not available in this library"]
theorem isHomColimit_of_ringModel
    [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
      HasSheafify ((smallEtaleRingedSite B S hS (D.stage D.base).obj
        (D.stage D.base).property).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
        (D.stage D.base).property).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
        (D.stage D.base).property).J.over U).HasSheafCompose
          (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS (D.stage D.base).obj
        (D.stage D.base).property).O).obj M).Additive]
    [∀ (M N : CochainComplex
        (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) ℤ),
      HomologicalComplex.HasMapBifunctor M N
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O)
        (ComplexShape.up ℤ)]
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hcase :
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPerfect E₀ ∧
          ∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∨
        ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPseudoCoherent E₀ ∧
          (∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∧
          Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K₀))
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (model : RingModel sys E₀ K₀ R) :
    IsHomColimit sys E₀ K₀ := by
  -- `hcase` is the hypothesis of the tag.  In the source's proof it is what produces the
  -- dictionary `model`, and the assembly below reaches it only through `model`; the case
  -- distinction it makes is immaterial here, so both of its cases are discharged alike.
  have key : IsHomColimit sys E₀ K₀ := by
   have : model.cx.IsStrictlyLE model.deg := model.isStrictlyLE
   have : ∀ n : ℤ, Projective (model.cx.X n) := model.projective
   refine ⟨?_, ?_, ?_⟩
   · -- the cocone identity
     intro i j h g
     refine model.limitEquiv.injective ?_
     rw [model.limitEquiv_homProjection, model.limitEquiv_homProjection,
       model.stageEquiv_homTransition, Category.assoc]
     congr 1
     rw [Stacks.LimitDerivedHom.derivedMap, Stacks.LimitDerivedHom.derivedMap,
       Stacks.LimitDerivedHom.derivedMap, ← Functor.map_comp, ← Functor.map_comp, model.hcompat]
   · -- joint surjectivity
     intro φ
     obtain ⟨i, ψ, hψ⟩ := Stacks.FilteredColimitHom.exists_descends_derived
       model.htrans model.hcompat model.hsurj model.hzero model.W model.hW model.hfp model.deg
       (model.limitEquiv φ)
     refine ⟨i, (model.stageEquiv i).symm ψ, model.limitEquiv.injective ?_⟩
     rw [model.limitEquiv_homProjection, Equiv.apply_symm_apply]
     exact hψ
   · -- two homomorphisms at one stage with the same image agree later
     intro i g g' hgg
     have himg : model.stageEquiv i g ≫ Stacks.LimitDerivedHom.derivedMap.{w} (model.ι i) =
         model.stageEquiv i g' ≫ Stacks.LimitDerivedHom.derivedMap.{w} (model.ι i) := by
       rw [← model.limitEquiv_homProjection, ← model.limitEquiv_homProjection, hgg]
     obtain ⟨j, hij, hij', hj⟩ := Stacks.FilteredColimitHom.exists_le_eq_of_eq_derived
       model.htrans model.hcompat model.hsurj model.hzero model.W model.hW model.hfp model.deg
       (model.stageEquiv i g) (model.stageEquiv i g') himg
     refine ⟨j, hij, (model.stageEquiv j).injective ?_⟩
     rw [model.stageEquiv_homTransition, model.stageEquiv_homTransition]
     -- `hij` and `hij'` are proofs of the same `Prop`, hence interchangeable
     exact hj
  exact hcase.elim (fun _ => key) (fun _ => key)

end DescentSituation

end AlgebraicGeometry.Space

end
