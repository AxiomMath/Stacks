module

public import StacksFrontier.Topology.Simplicial.ProperHypercoveringDescentQc
public import StacksFrontier.Topology.Simplicial.QcTotalSiteMorphism

/-!
# The comparison functor into the total site of `LC_qc/U`, read in the small model

Let `S` be a locally quasi-compact Zariski situation, let `U` be a simplicial object of its
quasi-compact site `LC_qc` of **Tag 09X2** and let `a : U → X` be an augmentation. The site
`(LC_qc/U)_total` of **Section 09X8** is formed, in this development, over the small model of
`LC_qc`: it is the total site of the simplicial semi-representable object `n ↦ {U_n → X}` carried
to the small model, `Stacks.Topology.Simplicial.ProperHypercovering.qcTotalSituation`. Its objects
in degree `n` are the objects `V` of the small model together with a morphism `V → U_n` over `X`.

This file constructs the upper horizontal arrow `h` of the diagram of **Tag 0DAF** on that small
total site, as the morphism of topoi of a morphism of sites `U_Zar ⥤ (LC_qc/U)_total`: an open
`V` of `|U|_n` goes to the open subspace `V` of `U_n`, carried to the small model, in simplicial
degree `n`. It is the
functor `Stacks.Topology.Simplicial.qcTotalComparisonFunctor` of the big model, carried along the
comparison of `LC_qc` with its small model.

## Morphisms into a comparison object

Everything about the functor rests on one description of the morphisms *into* its values. An
object `t` of the total site in degree `n` is a morphism `y : V → U_n` of the small model;
transposing it across the comparison equivalence gives a morphism of `LC_qc` into `U_n`, whose
points are the points of `V` in the only sense available, and is
`Stacks.Topology.Simplicial.qcSmallPoint`. A morphism from `t` to the value at an open `W` of
`|U|_m` lying over a simplex map `β` exists exactly when the points of `t`, carried along `U(β)`,
lie in `W` (`qcSmallHomMk`, `qcSmallComparison_mem`), and it is then unique
(`qcSmallComparison_hom_ext`), because the inclusion of an open subspace is a monomorphism and
the comparison with the small model preserves monomorphisms.

## Main definitions

* `Stacks.Topology.Simplicial.qcSmallSemiRep`: the simplicial semi-representable object
  `n ↦ {U_n → X}` carried to the small model.
* `Stacks.Topology.Simplicial.qcSmallPoint`: the points of an object of the total site.
* `Stacks.Topology.Simplicial.qcSmallComparisonObj`: the value of the comparison at an open.
* `Stacks.Topology.Simplicial.qcSmallHomMk`: a morphism into a comparison object.
* `Stacks.Topology.Simplicial.qcSmallComparisonFunctor`: the comparison functor
  `U_Zar ⥤ (LC_qc/U)_total`.
* `Stacks.Topology.Simplicial.qcSmallComparisonMorphism`: the morphism of topoi
  `h : Sh((LC_qc/U)_total) → Sh(U_Zar)` it defines.

## Main results

* `Stacks.Topology.Simplicial.qcSmallComparison_hom_ext` and
  `Stacks.Topology.Simplicial.qcSmallComparison_mem`: morphisms into a comparison object are
  determined by their simplex map, and exist only over the open.
* `Stacks.Topology.Simplicial.qcSmallComparisonFunctor_representablyFlat`: the comparison functor
  is representably flat.
* `Stacks.Topology.Simplicial.qcSmallComparisonFunctor_coverPreserving` and
  `Stacks.Topology.Simplicial.qcSmallComparisonFunctor_isContinuous`: it is cover-preserving, a
  covering of `U_Zar` in one degree going to a covering of `LC_qc/U_n` by Tag 09X3 and so to a
  covering family of the total site, and hence continuous.
* `Stacks.Topology.Simplicial.qcSmallComparisonFunctor_isMorphismOfSites`: it is a morphism of
  sites in the sense of Tag 00X1, the induced `u_s` being exact because the functor is
  representably flat.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.Simplicial.ProperHypercovering
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (X : S.category) (U : SimplicialObject S.category)
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-- The simplicial semi-representable object `n ↦ {U_n → X}` of Section 09X8, carried to the small
model of `LC_qc`. Its total site is `(LC_qc/U)_total`. -/
abbrev qcSmallSemiRep : SimplicialObject (FormalCoproduct.{u}
    (Over (S.qcSite.smallEquivalence.functor.obj X))) :=
  associatedSimplicialObject.{u} (qcSmallSimplicialObject S U) (qcSmallAugmentation S X U a)

/-- The total category of `(LC_qc/U)_total`, formed in the small model. -/
abbrev qcSmallTotal := Grothendieck (slices (qcSmallSemiRep S X U a))

/-- The topology of `(LC_qc/U)_total`, formed in the small model. -/
abbrev qcSmallTotalTopology : GrothendieckTopology (qcSmallTotal S X U a) :=
  (qcTotalSituation S X U a).totalTopology

/-- The site in simplicial degree `n` of `(LC_qc/U)_total`: the objects `V → U_n` over `X` of the
small model. -/
abbrev qcSmallFiber (n : SimplexCategoryᵒᵖ) :=
  Over (Over.mk (S.qcSite.smallEquivalence.functor.map (a.app n)))

/-- The value of the comparison in simplicial degree `n` at an open `V` of `|U|_n`: the open
subspace `V` of `U_n` carried to the small model, over `U_n` and `X`. -/
abbrev qcSmallComparisonFiber (n : SimplexCategoryᵒᵖ) (V : Opens ((qcSimplicialSpace S U).obj n)) :
    qcSmallFiber S X U a n :=
  Over.mk (Over.homMk (S.qcSite.smallEquivalence.functor.map
      ((S.opensToSlice (U.obj n)).1.obj V).hom) :
    Over.mk (S.qcSite.smallEquivalence.functor.map ((S.opensToSlice (U.obj n)).1.obj V).hom ≫
      S.qcSite.smallEquivalence.functor.map (a.app n)) ⟶
      Over.mk (S.qcSite.smallEquivalence.functor.map (a.app n)))

/-- The value of the comparison functor at a simplicial open. -/
abbrev qcSmallComparisonObj (A : SimplicialOpen (qcSimplicialSpace S U)) : qcSmallTotal S X U a :=
  ⟨A.degree, ⟨PUnit.unit, qcSmallComparisonFiber S X U a A.degree A.toOpens⟩⟩

/-- The points of an object `y : V → U_n` of the total site: the transpose of `y` across the
comparison of `LC_qc` with its small model, a morphism of `LC_qc` into `U_n`. -/
def qcSmallPoint (t : qcSmallTotal S X U a) :
    S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left ⟶ U.obj t.base :=
  (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv _ _).symm t.fiber.2.hom.left

/-- The points of an object of the total site, carried along a simplex map, are the transpose of
its structure morphism followed by that simplex map of `U`. -/
theorem qcSmallPoint_comp (t : qcSmallTotal S X U a) {m : SimplexCategoryᵒᵖ} (β : t.base ⟶ m) :
    qcSmallPoint S X U a t ≫ U.map β =
      (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv _ _).symm
        (t.fiber.2.hom.left ≫ S.qcSite.smallEquivalence.functor.map (U.map β)) :=
  (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv_naturality_right_symm _ _).symm

/-- Morphisms in one simplicial degree into a comparison object are unique: the structure
morphism of an open subspace is a monomorphism, and so is its image in the small model. -/
theorem qcSmallFiber_hom_ext {n : SimplexCategoryᵒᵖ} {V : Opens ((qcSimplicialSpace S U).obj n)}
    {P : Σ _ : PUnit, qcSmallFiber S X U a n}
    (f g : P ⟶ ⟨PUnit.unit, qcSmallComparisonFiber S X U a n V⟩) : f = g := by
  obtain ⟨i, P⟩ := P
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  have := S.mono_opensToSlice_hom (U.obj n) V
  obtain rfl : f = g := by
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (S.qcSite.smallEquivalence.functor.map
      ((S.opensToSlice (U.obj n)).1.obj V).hom)).1
    exact (congrArg (fun k => k.left) (Over.w f)).trans (congrArg (fun k => k.left) (Over.w g)).symm
  rfl

/-- **Morphisms into a comparison object are determined by their simplex map.** -/
theorem qcSmallComparison_hom_ext {t : qcSmallTotal S X U a}
    {A : SimplicialOpen (qcSimplicialSpace S U)} (f g : t ⟶ qcSmallComparisonObj S X U a A)
    (h : f.base = g.base) : f = g :=
  Grothendieck.ext f g h (qcSmallFiber_hom_ext S X U a _ _)

/-- **A morphism into a comparison object lies over the open.** The points of its source,
carried along its simplex map, lie in the open. -/
theorem qcSmallComparison_mem {t : qcSmallTotal S X U a}
    {A : SimplicialOpen (qcSimplicialSpace S U)} (f : t ⟶ qcSmallComparisonObj S X U a A)
    (p : (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj) :
    ((qcSmallPoint S X U a t ≫ U.map f.base : _ ⟶ U.obj A.degree) :
      (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj → (U.obj A.degree).obj) p ∈
        A.toOpens := by
  obtain ⟨n, ⟨i, Y⟩⟩ := t
  obtain ⟨β, φ⟩ := f
  obtain ⟨ψ⟩ := φ
  have hw : ψ.left.left ≫ S.qcSite.smallEquivalence.functor.map
      ((S.opensToSlice (U.obj A.degree)).1.obj A.toOpens).hom =
      Y.hom.left ≫ S.qcSite.smallEquivalence.functor.map (U.map β) :=
    congrArg (fun k => k.left) (Over.w ψ)
  have ht : qcSmallPoint S X U a ⟨n, ⟨i, Y⟩⟩ ≫ U.map β =
      (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv _ _).symm ψ.left.left ≫
        ((S.opensToSlice (U.obj A.degree)).1.obj A.toOpens).hom := by
    rw [qcSmallPoint_comp]
    dsimp only
    rw [← hw]
    exact S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv_naturality_right_symm _ _
  show ((qcSmallPoint S X U a ⟨n, ⟨i, Y⟩⟩ ≫ U.map β : _ ⟶ U.obj A.degree) :
      (S.qcSite.smallEquivalence.inverse.obj Y.left.left).obj → (U.obj A.degree).obj) p ∈
        A.toOpens
  rw [ht]
  exact S.opensToSlice_hom_mem A.toOpens _

/-- The simplex map `U(β) : U_n → U_m` as a morphism of the small model over `X`. -/
abbrev qcSmallTransition {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) :
    Over.mk (S.qcSite.smallEquivalence.functor.map (a.app n)) ⟶
      Over.mk (S.qcSite.smallEquivalence.functor.map (a.app m)) :=
  Over.homMk (S.qcSite.smallEquivalence.functor.map (U.map β)) (by
    change S.qcSite.smallEquivalence.functor.map (U.map β) ≫
      S.qcSite.smallEquivalence.functor.map (a.app m) =
        S.qcSite.smallEquivalence.functor.map (a.app n)
    rw [← Functor.map_comp]
    congr 1
    simp)

/-- The fibre component of a morphism into a comparison object, from a factorization through the
open subspace. -/
def qcSmallFiberHomMk {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) (Y : qcSmallFiber S X U a n)
    (V : Opens ((qcSimplicialSpace S U).obj m))
    (g : Y.left.left ⟶
      S.qcSite.smallEquivalence.functor.obj ((S.opensToSlice (U.obj m)).1.obj V).left)
    (hg : g ≫ S.qcSite.smallEquivalence.functor.map ((S.opensToSlice (U.obj m)).1.obj V).hom =
      Y.hom.left ≫ S.qcSite.smallEquivalence.functor.map (U.map β)) :
    (Over.map (qcSmallTransition S X U a β)).obj Y ⟶ qcSmallComparisonFiber S X U a m V :=
  Over.homMk (Over.homMk g (by
      change g ≫ S.qcSite.smallEquivalence.functor.map ((S.opensToSlice (U.obj m)).1.obj V).hom ≫
        S.qcSite.smallEquivalence.functor.map (a.app m) = Y.left.hom
      rw [← Category.assoc, hg]
      exact (Over.w (Y.hom ≫ qcSmallTransition S X U a β)))) (Over.OverMorphism.ext hg)

/-- **A morphism into a comparison object**, over a simplex map along which the points of the
source land in the open. It is unique, by `qcSmallComparison_hom_ext`. -/
def qcSmallHomMk (t : qcSmallTotal S X U a) (A : SimplicialOpen (qcSimplicialSpace S U))
    (β : t.base ⟶ A.degree)
    (h : ∀ p : (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj,
      ((qcSmallPoint S X U a t ≫ U.map β : _ ⟶ U.obj A.degree) :
        (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj →
          (U.obj A.degree).obj) p ∈ A.toOpens) :
    t ⟶ qcSmallComparisonObj S X U a A := by
  let e := S.qcSite.smallEquivalence
  let ψ := (S.nonempty_over_hom_opensToSlice (Over.mk (qcSmallPoint S X U a t ≫ U.map β))
    A.toOpens h).some
  let g := e.symm.toAdjunction.homEquiv _ _ ψ.left
  have hg : g ≫ e.functor.map ((S.opensToSlice (U.obj A.degree)).1.obj A.toOpens).hom =
      t.fiber.2.hom.left ≫ e.functor.map (U.map β) := by
    calc g ≫ e.functor.map ((S.opensToSlice (U.obj A.degree)).1.obj A.toOpens).hom
        = e.symm.toAdjunction.homEquiv _ _
            (ψ.left ≫ ((S.opensToSlice (U.obj A.degree)).1.obj A.toOpens).hom) :=
          (e.symm.toAdjunction.homEquiv_naturality_right _ _).symm
      _ = e.symm.toAdjunction.homEquiv _ _ (qcSmallPoint S X U a t ≫ U.map β) :=
          congrArg (e.symm.toAdjunction.homEquiv _ _) (Over.w ψ)
      _ = e.symm.toAdjunction.homEquiv _ _ ((e.symm.toAdjunction.homEquiv _ _).symm
            (t.fiber.2.hom.left ≫ e.functor.map (U.map β))) := by rw [qcSmallPoint_comp]
      _ = _ := (e.symm.toAdjunction.homEquiv _ _).apply_symm_apply _
  exact ⟨β, Sigma.SigmaHom.mk (qcSmallFiberHomMk S X U a β t.fiber.2 A.toOpens g hg)⟩

/-- The simplex map of `qcSmallHomMk t A β h` is `β`. -/
@[simp]
theorem qcSmallHomMk_base (t : qcSmallTotal S X U a) (A : SimplicialOpen (qcSimplicialSpace S U))
    (β : t.base ⟶ A.degree) (h) : (qcSmallHomMk S X U a t A β h).base = β := rfl

/-- The points of a comparison object lie in its open. -/
theorem qcSmallPoint_comparisonObj_mem (A : SimplicialOpen (qcSimplicialSpace S U))
    (p : (S.qcSite.smallEquivalence.inverse.obj
      (qcSmallComparisonObj S X U a A).fiber.2.left.left).obj) :
    ((qcSmallPoint S X U a (qcSmallComparisonObj S X U a A) : _ ⟶ U.obj A.degree) :
      _ → (U.obj A.degree).obj) p ∈ A.toOpens := by
  have h := qcSmallComparison_mem S X U a (𝟙 (qcSmallComparisonObj S X U a A)) p
  have hid : Grothendieck.Hom.base (𝟙 (qcSmallComparisonObj S X U a A)) = 𝟙 A.degree := rfl
  rwa [hid, U.map_id, Category.comp_id] at h

/-- **The comparison functor underlying the upper horizontal arrow of the diagram of
Tag 0DAF**, into `(LC_qc/U)_total` formed in the small model. It sends an open `V` of `|U|_n` to
the open subspace `V` of `U_n`, carried to the small model, in simplicial degree `n`, and a
morphism of simplicial opens to the unique morphism over its simplex map. -/
def qcSmallComparisonFunctor : SimplicialOpen (qcSimplicialSpace S U) ⥤ qcSmallTotal S X U a where
  obj := qcSmallComparisonObj S X U a
  map {A B} g := qcSmallHomMk S X U a _ B g.base (fun p =>
    SimplicialOpen.Hom.le g (qcSmallPoint_comparisonObj_mem S X U a A p))
  map_id _ := qcSmallComparison_hom_ext S X U a _ _ rfl
  map_comp _ _ := qcSmallComparison_hom_ext S X U a _ _ rfl

/-- The comparison functor sends a simplicial open `A` to `qcSmallComparisonObj A`. -/
@[simp]
theorem qcSmallComparisonFunctor_obj (A : SimplicialOpen (qcSimplicialSpace S U)) :
    (qcSmallComparisonFunctor S X U a).obj A = qcSmallComparisonObj S X U a A := rfl

/-- The image of a morphism `g` under the comparison functor lies over the simplex map of `g`. -/
@[simp]
theorem qcSmallComparisonFunctor_map_base {A B : SimplicialOpen (qcSimplicialSpace S U)}
    (g : A ⟶ B) : ((qcSmallComparisonFunctor S X U a).map g).base = g.base := rfl

/-- **The comparison functor of Tag 0DAF is representably flat.** For an object `t` of the
total site the simplicial opens receiving it form a cofiltered category: two of them are refined
by intersecting, in the simplicial degree of `t`, the preimages of their opens, and a parallel
pair is equalized by the preimage of the source open, a morphism of simplicial opens being
determined by its simplex map. -/
theorem qcSmallComparisonFunctor_representablyFlat :
    RepresentablyFlat (qcSmallComparisonFunctor S X U a) := by
  refine ⟨fun t => { cone_objs := fun A B => ?_, cone_maps := fun A B f g => ?_, nonempty := ?_ }⟩
  · refine ⟨StructuredArrow.mk (qcSmallHomMk S X U a t
        ⟨t.base, (Opens.map ((qcSimplicialSpace S U).map A.hom.base)).obj A.right.toOpens ⊓
          (Opens.map ((qcSimplicialSpace S U).map B.hom.base)).obj B.right.toOpens⟩ (𝟙 _)
        (fun p => ?_)),
      StructuredArrow.homMk ⟨A.hom.base, fun _ hx => hx.1⟩ ?_,
      StructuredArrow.homMk ⟨B.hom.base, fun _ hx => hx.2⟩ ?_, trivial⟩
    · rw [U.map_id, Category.comp_id]
      exact ⟨qcSmallComparison_mem S X U a A.hom p, qcSmallComparison_mem S X U a B.hom p⟩
    · exact qcSmallComparison_hom_ext S X U a _ _ (Category.id_comp _)
    · exact qcSmallComparison_hom_ext S X U a _ _ (Category.id_comp _)
  · refine ⟨StructuredArrow.mk (qcSmallHomMk S X U a t
        ⟨t.base, (Opens.map ((qcSimplicialSpace S U).map A.hom.base)).obj A.right.toOpens⟩
        (𝟙 _) (fun p => ?_)),
      StructuredArrow.homMk ⟨A.hom.base, fun _ hx => hx⟩ ?_, ?_⟩
    · rw [U.map_id, Category.comp_id]
      exact qcSmallComparison_mem S X U a A.hom p
    · exact qcSmallComparison_hom_ext S X U a _ _ (Category.id_comp _)
    · apply StructuredArrow.hom_ext
      apply SimplicialOpen.Hom.ext
      show A.hom.base ≫ f.right.base = A.hom.base ≫ g.right.base
      exact congrArg Grothendieck.Hom.base
        ((StructuredArrow.w f).trans (StructuredArrow.w g).symm)
  · exact ⟨StructuredArrow.mk (qcSmallHomMk S X U a t ⟨t.base, ⊤⟩ (𝟙 _) (fun _ => trivial))⟩

/-! ### Cover preservation -/

/-- The site in simplicial degree `n` of `(LC_qc/U)_total`, presented as in Section 09X8: the
disjoint union of the slices over the components of `{U_n → X}`, of which there is one. -/
abbrev qcSmallDegree (n : SimplexCategoryᵒᵖ) :=
  SemiRepresentable.ComponentOver ((qcSmallSemiRep S X U a).obj n)

/-- The localized site `LC_qc/U_n` carried into simplicial degree `n` of the total site: an
object `V → U_n` goes to its image in the small model, over `U_n` and `X`. -/
def qcSmallDegreeFunctor (n : SimplexCategoryᵒᵖ) : Over (U.obj n) ⥤ qcSmallDegree S X U a n :=
  Over.post S.qcSite.smallEquivalence.functor ⋙
    (Over.mk (S.qcSite.smallEquivalence.functor.map (a.app n))).iteratedSliceBackward ⋙
      CategoryTheory.Sigma.incl
        (C := fun i : ((qcSmallSemiRep S X U a).obj n).I =>
          Over (((qcSmallSemiRep S X U a).obj n).obj i)) PUnit.unit

/-- The comparison object of an open is the image of the open subspace in its degree. -/
theorem qcSmallDegreeFunctor_obj_opensToSlice (n : SimplexCategoryᵒᵖ)
    (V : Opens ((qcSimplicialSpace S U).obj n)) :
    (Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n).obj
      ((qcSmallDegreeFunctor S X U a n).obj ((S.opensToSlice (U.obj n)).1.obj V)) =
      qcSmallComparisonObj S X U a ⟨n, V⟩ := rfl

/-- The comparison of `LC_qc/U_n` with its small model is continuous for the localized
quasi-compact topologies. -/
theorem overPost_smallEquivalence_coverPreserving (Y : S.category) :
    CoverPreserving (S.qcSite.grothendieckTopology.over Y)
      (S.qcSite.smallPretopology.toGrothendieck.over (S.qcSite.smallEquivalence.functor.obj Y))
      (Over.post (X := Y) S.qcSite.smallEquivalence.functor) := by
  rw [S.qcSite.toGrothendieck_smallPretopology]
  have : (Over.postEquiv (X := Y) S.qcSite.smallEquivalence).symm.functor.IsCocontinuous
      (S.qcSite.smallTopology.over (S.qcSite.smallEquivalence.functor.obj Y))
      (S.qcSite.grothendieckTopology.over Y) :=
    inferInstanceAs ((Over.postEquiv (X := Y) S.qcSite.smallEquivalence).inverse.IsCocontinuous
      _ _)
  have : (Over.postEquiv (X := Y) S.qcSite.smallEquivalence).functor.IsContinuous
      (S.qcSite.grothendieckTopology.over Y)
      (S.qcSite.smallTopology.over (S.qcSite.smallEquivalence.functor.obj Y)) :=
    (Over.postEquiv (X := Y) S.qcSite.smallEquivalence).symm.toAdjunction
      |>.isContinuous_of_isCocontinuous (S.qcSite.smallTopology.over
        (S.qcSite.smallEquivalence.functor.obj Y)) (S.qcSite.grothendieckTopology.over Y)
  exact CoverPreserving.of_isContinuous (Over.postEquiv (X := Y) S.qcSite.smallEquivalence).functor
    _ _

/-- The inclusion of the single component into the disjoint union presenting a simplicial degree
of the total site is cover-preserving. -/
theorem qcSmallSigmaIncl_coverPreserving (n : SimplexCategoryᵒᵖ) :
    CoverPreserving ((S.qcSite.smallOverTopology X).over
        (((qcSmallSemiRep S X U a).obj n).obj PUnit.unit))
      (SemiRepresentable.componentwiseTopology (S.qcSite.smallOverTopology X)
        ((qcSmallSemiRep S X U a).obj n))
      (CategoryTheory.Sigma.incl
        (C := fun i : ((qcSmallSemiRep S X U a).obj n).I =>
          Over (((qcSmallSemiRep S X U a).obj n).obj i)) PUnit.unit) := by
  refine ⟨fun {Y R} hR => ?_⟩
  show (R.functorPushforward _).functorPullback (CategoryTheory.Sigma.incl
    (C := fun i : ((qcSmallSemiRep S X U a).obj n).I =>
      Over (((qcSmallSemiRep S X U a).obj n).obj i)) PUnit.unit) ∈
        ((S.qcSite.smallOverTopology X).over (((qcSmallSemiRep S X U a).obj n).obj PUnit.unit)) Y
  exact ((S.qcSite.smallOverTopology X).over _).superset_covering
    (Sieve.le_functorPushforward_pullback _ R) hR

/-- The localized site `LC_qc/U_n` is carried into simplicial degree `n` of the total site by a
cover-preserving functor. -/
theorem qcSmallDegreeFunctor_coverPreserving (n : SimplexCategoryᵒᵖ) :
    CoverPreserving (S.qcSite.grothendieckTopology.over (U.obj n))
      (SemiRepresentable.componentwiseTopology (S.qcSite.smallOverTopology X)
        ((qcSmallSemiRep S X U a).obj n)) (qcSmallDegreeFunctor S X U a n) :=
  CoverPreserving.comp (hF := overPost_smallEquivalence_coverPreserving S (U.obj n))
    (hG := CoverPreserving.comp
      (hF := CoverPreserving.of_isContinuous
        (Over.mk (S.qcSite.smallEquivalence.functor.map (a.app n))).iteratedSliceBackward
        (S.qcSite.smallPretopology.toGrothendieck.over _)
        ((S.qcSite.smallPretopology.toGrothendieck.over _).over _))
      (hG := qcSmallSigmaIncl_coverPreserving S X U a n))

/-- A covering family of one simplicial degree, included into the total category, is a covering
family of `(LC_qc/U)_total`. -/
theorem qcSmallTotalIota_coverPreserving (n : SimplexCategoryᵒᵖ) :
    CoverPreserving (SemiRepresentable.componentwiseTopology (S.qcSite.smallOverTopology X)
        ((qcSmallSemiRep S X U a).obj n))
      (qcSmallTotalTopology S X U a) (Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n) := by
  refine ⟨fun {P T} hT => ?_⟩
  have hcov : sliceCoverings (S.qcSite.smallOverTopology X) (qcSmallSemiRep S X U a) n
      ⟨P, T.arrows.preZeroHypercover⟩ := by
    show (T.arrows.preZeroHypercover).presieve₀ ∈ _
    rw [Presieve.presieve₀_preZeroHypercover, GrothendieckTopology.mem_toCoverage_iff,
      Sieve.generate_sieve]
    exact hT
  have hgen : Sieve.generate ((T.arrows.preZeroHypercover.map
        (Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n)).presieve₀) ∈
      qcSmallTotalTopology S X U a
        ((Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n).obj P) :=
    Precoverage.generate_mem_toGrothendieck ⟨_, ⟨_, hcov, rfl⟩, rfl⟩
  refine (qcSmallTotalTopology S X U a).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  exact Presieve.ofArrows_le_iff.2 fun i => Sieve.image_mem_functorPushforward _ T i.2

/-- On an arrow of one simplicial degree the comparison functor is the open-subspace comparison
of that degree, carried into the total site. -/
theorem qcSmallComparisonFunctor_map_levelFunctor (n : SimplexCategoryᵒᵖ)
    {V W : Opens ((qcSimplicialSpace S U).obj n)} (t : V ⟶ W) :
    (qcSmallComparisonFunctor S X U a).map ((levelFunctor (qcSimplicialSpace S U) n).map t) =
      (Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n).map
        ((qcSmallDegreeFunctor S X U a n).map ((S.opensToSlice (U.obj n)).1.map t)) :=
  qcSmallComparison_hom_ext S X U a _ _ rfl

/-- **The comparison functor of Tag 0DAF is cover-preserving.** A covering sieve of `U_Zar`
contains an open covering lying in a single simplicial degree; the open-subspace comparison of
Tag 09X3 carries it to a covering of `LC_qc/U_n`, the comparison with the small model to a
covering of the degree of the total site, and the inclusion of that degree to a covering family
of `(LC_qc/U)_total`. -/
theorem qcSmallComparisonFunctor_coverPreserving :
    CoverPreserving (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcSmallTotalTopology S X U a) (qcSmallComparisonFunctor S X U a) := by
  refine ⟨fun {A T} hT => ?_⟩
  have := levelFunctor_isCocontinuous (qcSimplicialSpace S U) A.degree
  have hpull : T.functorPullback (levelFunctor (qcSimplicialSpace S U) A.degree) ∈
      Opens.grothendieckTopology ((qcSimplicialSpace S U).obj A.degree) A.toOpens :=
    Functor.cover_lift (levelFunctor (qcSimplicialSpace S U) A.degree) _ _ hT
  have hcomp := (CoverPreserving.comp (hF := opensToSlice_coverPreserving_qc S U A.degree)
    (hG := CoverPreserving.comp (hF := qcSmallDegreeFunctor_coverPreserving S X U a A.degree)
      (hG := qcSmallTotalIota_coverPreserving S X U a A.degree))).cover_preserve hpull
  refine (qcSmallTotalTopology S X U a).superset_covering ?_ hcomp
  intro Z f hf
  obtain ⟨Y, g, h, hg, hfac⟩ := hf
  refine ⟨(levelFunctor (qcSimplicialSpace S U) A.degree).obj Y,
    (levelFunctor (qcSimplicialSpace S U) A.degree).map g, h, hg, ?_⟩
  rw [hfac]
  exact congrArg (fun k => h ≫ k)
    (qcSmallComparisonFunctor_map_levelFunctor S X U a A.degree g).symm

/-- **The comparison functor of Tag 0DAF is continuous**, the first clause of Tag 00X1: it is
cover-preserving and representably flat. -/
theorem qcSmallComparisonFunctor_isContinuous :
    (qcSmallComparisonFunctor S X U a).IsContinuous
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcSmallTotalTopology S X U a) := by
  have := qcSmallComparisonFunctor_representablyFlat S X U a
  exact (Functor.isContinuous_iff_coverPreserving
    (F := qcSmallComparisonFunctor S X U a)
    (J := SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
    (K := qcSmallTotalTopology S X U a)).2 (qcSmallComparisonFunctor_coverPreserving S X U a)

/-- **The comparison functor of Tag 0DAF is a morphism of sites**, the whole of Tag 00X1 for it:
it is continuous, and `u_s` is exact because the functor is representably flat, so its left Kan
extension on presheaves is left exact. -/
theorem qcSmallComparisonFunctor_isMorphismOfSites :
    IsMorphismOfSites.{u} (qcSmallComparisonFunctor S X U a)
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcSmallTotalTopology S X U a) := by
  have := qcSmallComparisonFunctor_representablyFlat S X U a
  have := qcSmallComparisonFunctor_isContinuous S X U a
  refine ⟨?_⟩
  refine ⟨Functor.sheafPullbackConstruction.sheafPullback (qcSmallComparisonFunctor S X U a)
    (Type u)
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcSmallTotalTopology S X U a),
    ?_⟩
  refine ⟨⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (qcSmallComparisonFunctor S X U a) (Type u)
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
    (qcSmallTotalTopology S X U a)⟩, ?_⟩
  have : PreservesFiniteLimits ((qcSmallComparisonFunctor S X U a).op.lan :
      ((SimplicialOpen (qcSimplicialSpace S U))ᵒᵖ ⥤ Type u) ⥤
        ((qcSmallTotal S X U a)ᵒᵖ ⥤ Type u)) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat
      (qcSmallComparisonFunctor S X U a) (fun _ => inferInstance)
  exact inferInstance

/-- **The upper horizontal arrow of the diagram of Tag 0DAF**, the morphism of topoi
`h : Sh((LC_qc/U)_total) ⟶ Sh(U_Zar)` of the comparison functor, with `(LC_qc/U)_total` formed
in the small model as in Section 09X8. Its direct image is restriction along the comparison
functor. -/
@[stacks 0DAF "the upper horizontal arrow h : Sh((LC_qc/U)_total) → Sh(U_Zar) of the diagram"]
def qcSmallComparisonMorphism :
    MorphismOfTopoi (Sheaf (qcSmallTotalTopology S X U a) (Type u))
      (Sheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type u)) :=
  (qcSmallComparisonFunctor_isMorphismOfSites S X U a).morphismOfTopoi

/-- The direct image of `h` is restriction along the comparison functor. -/
theorem qcSmallComparisonMorphism_pushforward :
    haveI := qcSmallComparisonFunctor_isContinuous S X U a
    (qcSmallComparisonMorphism S X U a).pushforward =
      (qcSmallComparisonFunctor S X U a).sheafPushforwardContinuous (Type u)
        (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
        (qcSmallTotalTopology S X U a) := rfl

end Stacks.Topology.Simplicial

end
