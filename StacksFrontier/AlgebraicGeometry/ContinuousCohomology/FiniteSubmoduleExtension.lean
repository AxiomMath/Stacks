module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Extending an exact functor from finite modules to all discrete modules

Let `R` be a Noetherian ring, `G` a compact topological group, and `F` an exact functor from the
finite `R`-modules with a continuous `G`-action to an abelian category `D` in which filtered
colimits are exact. Every continuous discrete `R`-`G`-module `N` is the filtered union of its
finite `G`-stable submodules, and

`Φ(N) = colim_{P ⊆ N finite, G-stable} F(P)`

defines an exact functor `Φ` on all continuous discrete `R`-`G`-modules, which restricts to `F` on
the finite ones. No choice is involved: the indexing preorder and the transition maps are the
inclusions of submodules.

## Main definitions

* `Stacks.ContinuousCohomology.FiniteStableSubmodule` — the finite `G`-stable submodules of `N`,
  a directed preorder.
* `Stacks.ContinuousCohomology.stableSubmoduleObj` — a `G`-stable submodule as a continuous
  discrete `R`-`G`-module.
* `Stacks.ContinuousCohomology.finiteStableSubmoduleDiagram` — the diagram of finite `G`-stable
  submodules of `N`, valued in finite modules.
* `Stacks.ContinuousCohomology.finiteSubmoduleExtension` — the extension `Φ` of `F`.
* `Stacks.ContinuousCohomology.finiteSubmoduleExtensionιIso` — `Φ` restricted to the finite
  modules is `F`.

## Main results

* `Stacks.ContinuousCohomology.ι_finiteSubmoduleExtension_map` — the computation rule of `Φ` on
  morphisms, through any finite stable submodule containing the image.
* `Stacks.ContinuousCohomology.finiteSubmoduleExtension_exact` — `Φ` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u v w w' w''

namespace Stacks.ContinuousCohomology

section Submodules

variable {R : Type u} [Ring R] {G : Type v} [Group G] [TopologicalSpace G]

/-- A submodule of a continuous discrete `R`-`G`-module is `G`-stable when every element of `G`
maps it into itself. -/
def IsGStable (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) : Prop :=
  ∀ (g : G) (x : N.obj.obj.V), x ∈ P → (N.obj.obj.ρ g).asHom.hom x ∈ P

/-- **The finite `G`-stable submodules** of a continuous discrete `R`-`G`-module, ordered by
inclusion. -/
def FiniteStableSubmodule (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :=
  {P : Submodule R N.obj.obj.V // IsGStable N P ∧ Module.Finite R P}

/-- The finite `G`-stable submodules are partially ordered by inclusion. -/
instance (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    PartialOrder (FiniteStableSubmodule N) :=
  inferInstanceAs (PartialOrder {P : Submodule R N.obj.obj.V // IsGStable N P ∧ Module.Finite R P})

/-- The action of `G` on a `G`-stable submodule. -/
def stableSubmoduleRep (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) (hP : IsGStable N P) : Representation R G P where
  toFun g := (N.obj.obj.ρ g).asHom.hom.restrict (fun x hx ↦ hP g x hx)
  map_one' := by
    ext x
    simp [map_one, End.one_asHom]
  map_mul' g h := by
    ext x
    simp [map_mul, End.mul_asHom]

variable [IsTopologicalGroup G]

open scoped Stacks.DiscreteModuleTopology in
/-- The action on a `G`-stable submodule is continuous: the stabilizers are those in `N`. -/
theorem isContinuous_stableSubmoduleRep
    (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) (hP : IsGStable N P) :
    (actionOfRepresentation R G P (stableSubmoduleRep N P hP)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro x
  convert isOpen_stabilizer R G N x.1 using 1
  ext g
  simp only [Set.mem_setOf_eq, Subtype.ext_iff]
  rfl

/-- **A `G`-stable submodule as a continuous discrete `R`-`G`-module.** -/
def stableSubmoduleObj (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) (hP : IsGStable N P) :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  ofRepresentation (stableSubmoduleRep N P hP) (isContinuous_stableSubmoduleRep N P hP)

/-- The morphism of stable submodules induced by a morphism carrying the first into the second. -/
def stableSubmoduleHom {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : Submodule R N.obj.obj.V) (hP : IsGStable N P)
    (Q : Submodule R N'.obj.obj.V) (hQ : IsGStable N' Q)
    (hPQ : ∀ x ∈ P, h.hom.hom.hom.hom x ∈ Q) :
    stableSubmoduleObj N P hP ⟶ stableSubmoduleObj N' Q hQ :=
  (homEquiv R G _ _).symm
    ⟨h.hom.hom.hom.hom.restrict hPQ, fun g x ↦ by
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (h.hom.hom.comm g) x.1⟩

/-- The inclusion of a `G`-stable submodule. -/
def stableSubmoduleι (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) (hP : IsGStable N P) : stableSubmoduleObj N P hP ⟶ N :=
  (homEquiv R G _ _).symm ⟨P.subtype, fun _ _ ↦ rfl⟩

omit [IsTopologicalGroup G] in
/-- Morphisms of continuous discrete modules are determined by their underlying functions. -/
lemma continuousModule_hom_ext {M M' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    {a b : M ⟶ M'} (h : ∀ x, a.hom.hom.hom.hom x = b.hom.hom.hom.hom x) : a = b := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Action.hom_ext
  apply ModuleCat.hom_ext; exact LinearMap.ext h

/-- Morphisms of finite continuous modules are determined by their underlying functions. -/
private lemma finiteType_hom_ext {R : Type u} [Ring R] {G : Type v} [Group G]
    [TopologicalSpace G] {M M' : FiniteTypeContinuousModule.{u, v, w} R G}
    {a b : M ⟶ M'} (h : ∀ x, a.hom.hom.hom.hom.hom x = b.hom.hom.hom.hom.hom x) : a = b :=
  ObjectProperty.hom_ext _ (continuousModule_hom_ext h)

/-- The morphism of stable submodules induced by a composite is the composite of the induced
morphisms. -/
@[reassoc (attr := simp)]
lemma stableSubmoduleHom_comp
    {N N' N'' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (h' : N' ⟶ N'') (P : Submodule R N.obj.obj.V) (hP : IsGStable N P)
    (Q : Submodule R N'.obj.obj.V) (hQ : IsGStable N' Q)
    (Q' : Submodule R N''.obj.obj.V) (hQ' : IsGStable N'' Q')
    (hPQ : ∀ x ∈ P, h.hom.hom.hom.hom x ∈ Q) (hQQ' : ∀ x ∈ Q, h'.hom.hom.hom.hom x ∈ Q') :
    stableSubmoduleHom h P hP Q hQ hPQ ≫ stableSubmoduleHom h' Q hQ Q' hQ' hQQ' =
      stableSubmoduleHom (h ≫ h') P hP Q' hQ' (fun x hx ↦ hQQ' _ (hPQ x hx)) :=
  continuousModule_hom_ext fun _ ↦ rfl

/-- The identity induces the identity of a stable submodule. -/
@[simp]
lemma stableSubmoduleHom_id (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (P : Submodule R N.obj.obj.V) (hP : IsGStable N P) :
    stableSubmoduleHom (𝟙 N) P hP P hP (fun _ hx ↦ hx) = 𝟙 _ :=
  continuousModule_hom_ext fun _ ↦ rfl

/-- A finite `G`-stable submodule, as a finite `R`-module with a continuous `G`-action. -/
abbrev FiniteStableSubmodule.toFinite {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P : FiniteStableSubmodule N) : FiniteTypeContinuousModule.{u, v, w} R G :=
  ⟨stableSubmoduleObj N P.1 P.2.1, (continuousModuleIsFG_iff _ _ _).2 P.2.2⟩

/-- The morphism of finite stable submodules induced by a morphism carrying the first into the
second. -/
def FiniteStableSubmodule.hom {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) : P.toFinite ⟶ Q.toFinite :=
  ObjectProperty.homMk (stableSubmoduleHom h P.1 P.2.1 Q.1 Q.2.1 hPQ)

/-- The morphism of finite stable submodules induced by a composite is the composite of the
induced morphisms. -/
@[reassoc (attr := simp)]
lemma FiniteStableSubmodule.hom_comp
    {N N' N'' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (h' : N' ⟶ N'') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (Q' : FiniteStableSubmodule N'')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (hQQ' : ∀ x ∈ Q.1, h'.hom.hom.hom.hom x ∈ Q'.1) :
    FiniteStableSubmodule.hom h P Q hPQ ≫ FiniteStableSubmodule.hom h' Q Q' hQQ' =
      FiniteStableSubmodule.hom (h ≫ h') P Q' (fun x hx ↦ hQQ' _ (hPQ x hx)) :=
  ObjectProperty.hom_ext _ (stableSubmoduleHom_comp _ _ _ _ _ _ _ _ _ _)

/-- The identity induces the identity of a finite stable submodule. -/
@[simp]
lemma FiniteStableSubmodule.hom_id {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P : FiniteStableSubmodule N) :
    FiniteStableSubmodule.hom (𝟙 N) P P (fun _ hx ↦ hx) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (stableSubmoduleHom_id _ _ _)

/-- The inclusion of a finite stable submodule of a finite module, in the finite modules. -/
def FiniteStableSubmodule.ι {M : FiniteTypeContinuousModule.{u, v, w} R G}
    (P : FiniteStableSubmodule M.obj) : P.toFinite ⟶ M :=
  ObjectProperty.homMk (stableSubmoduleι M.obj P.1 P.2.1)

/-- **The diagram of finite `G`-stable submodules** of `N`, with the inclusions. -/
abbrev finiteStableSubmoduleDiagram (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    FiniteStableSubmodule N ⥤ FiniteTypeContinuousModule.{u, v, w} R G where
  obj P := P.toFinite
  map {P Q} i := FiniteStableSubmodule.hom (𝟙 N) P Q (fun _ hx ↦ leOfHom i hx)
  map_id _ := ObjectProperty.hom_ext _ (continuousModule_hom_ext fun _ ↦ rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (continuousModule_hom_ext fun _ ↦ rfl)

/-- Following an induced morphism `P ⟶ Q` by the inclusion `Q ⟶ Q'` gives the induced morphism
`P ⟶ Q'`. -/
@[reassoc (attr := simp)]
lemma FiniteStableSubmodule.hom_comp_diagram_map
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q Q' : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (i : Q ⟶ Q') :
    FiniteStableSubmodule.hom h P Q hPQ ≫ (finiteStableSubmoduleDiagram N').map i =
      FiniteStableSubmodule.hom h P Q' (fun x hx ↦ leOfHom i (hPQ x hx)) :=
  finiteType_hom_ext fun _ ↦ rfl

/-- Preceding an induced morphism `P' ⟶ Q` by the inclusion `P ⟶ P'` gives the induced morphism
`P ⟶ Q`. -/
@[reassoc (attr := simp)]
lemma FiniteStableSubmodule.diagram_map_comp_hom
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P P' : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (i : P ⟶ P') (hP'Q : ∀ x ∈ P'.1, h.hom.hom.hom.hom x ∈ Q.1) :
    (finiteStableSubmoduleDiagram N).map i ≫ FiniteStableSubmodule.hom h P' Q hP'Q =
      FiniteStableSubmodule.hom h P Q (fun x hx ↦ hP'Q x (leOfHom i hx)) :=
  finiteType_hom_ext fun _ ↦ rfl

/-- The inclusions of finite stable submodules of a finite module into it are compatible with the
inclusions among them. -/
@[reassoc (attr := simp)]
lemma FiniteStableSubmodule.diagram_map_comp_ι {M : FiniteTypeContinuousModule.{u, v, w} R G}
    {P P' : FiniteStableSubmodule M.obj} (i : P ⟶ P') :
    (finiteStableSubmoduleDiagram M.obj).map i ≫ P'.ι = P.ι :=
  finiteType_hom_ext fun _ ↦ rfl

/-- `FiniteStableSubmodule.hom` depends only on the morphism, not on the proof. -/
lemma FiniteStableSubmodule.hom_congr {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    {h h' : N ⟶ N'} (e : h = h') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (hPQ' : ∀ x ∈ P.1, h'.hom.hom.hom.hom x ∈ Q.1) :
    FiniteStableSubmodule.hom h P Q hPQ = FiniteStableSubmodule.hom h' P Q hPQ' := by
  subst e; rfl

end Submodules

section Extension

variable {R : Type u} [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The sum of two `G`-stable submodules is `G`-stable. -/
lemma IsGStable.sup {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    {P Q : Submodule R N.obj.obj.V} (hP : IsGStable N P) (hQ : IsGStable N Q) :
    IsGStable N (P ⊔ Q) := by
  intro g x hx
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (hP g p hp) (hQ g q hq)

omit [IsTopologicalGroup G] in
/-- The zero submodule is `G`-stable. -/
lemma isGStable_bot (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    IsGStable N ⊥ := by
  intro g x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/-- The sum of two finite stable submodules. -/
def FiniteStableSubmodule.sup {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P Q : FiniteStableSubmodule N) : FiniteStableSubmodule N :=
  ⟨P.1 ⊔ Q.1, P.2.1.sup Q.2.1, Module.Finite.iff_fg.2
      ((Module.Finite.iff_fg.1 P.2.2).sup (Module.Finite.iff_fg.1 Q.2.2))⟩

omit [IsTopologicalGroup G] in
/-- A finite stable submodule is contained in its sum with another. -/
lemma FiniteStableSubmodule.le_sup_left {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P Q : FiniteStableSubmodule N) : P ≤ P.sup Q :=
  (_root_.le_sup_left : P.1 ≤ P.1 ⊔ Q.1)

omit [IsTopologicalGroup G] in
/-- A finite stable submodule is contained in the sum of another with it. -/
lemma FiniteStableSubmodule.le_sup_right {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P Q : FiniteStableSubmodule N) : Q ≤ P.sup Q :=
  (_root_.le_sup_right : Q.1 ≤ P.1 ⊔ Q.1)

/-- The finite stable submodules are directed under inclusion. -/
instance (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    IsDirected (FiniteStableSubmodule N) (· ≤ ·) where
  directed P Q := ⟨P.sup Q, P.le_sup_left Q, P.le_sup_right Q⟩

/-- The zero submodule is a finite stable submodule. -/
instance (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    Nonempty (FiniteStableSubmodule N) :=
  ⟨⟨⊥, isGStable_bot N, inferInstance⟩⟩

/-- The image of a finite stable submodule under a morphism. -/
def FiniteStableSubmodule.map {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) : FiniteStableSubmodule N' :=
  ⟨P.1.map h.hom.hom.hom.hom, fun g y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      refine Submodule.mem_map.2 ⟨(N.obj.obj.ρ g).asHom.hom x, P.2.1 g x hx, ?_⟩
      exact ConcreteCategory.congr_hom (h.hom.hom.comm g) x,
    haveI := P.2.2; inferInstance⟩

omit [IsTopologicalGroup G] in
/-- A morphism carries a finite stable submodule into its image. -/
lemma FiniteStableSubmodule.mem_map {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) :
    ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ (P.map h).1 :=
  fun _ hx ↦ Submodule.mem_map_of_mem hx

variable {D : Type w'} [Category.{w''} D] [HasColimitsOfSize.{w, w} D]
  (F : FiniteTypeContinuousModule.{u, v, w} R G ⥤ D)

/-- The value `colim_P F(P)` of the extension at a continuous discrete module. -/
def finiteSubmoduleExtensionObj (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    D :=
  colimit (finiteStableSubmoduleDiagram N ⋙ F)

/-- The map `F(P) ⟶ Φ(N')` attached to a morphism `h : N ⟶ N'` and a finite stable submodule `Q`
of `N'` containing `h(P)`. -/
def finiteSubmoduleExtensionι {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) :
    F.obj P.toFinite ⟶ finiteSubmoduleExtensionObj F N' :=
  F.map (FiniteStableSubmodule.hom h P Q hPQ) ≫
    colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q

/-- The map `F(P) ⟶ Φ(N')` taken through `Q` agrees with the one taken through any larger
`Q'`. -/
lemma finiteSubmoduleExtensionι_of_le
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q Q' : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (hQQ' : Q ≤ Q') :
    finiteSubmoduleExtensionι F h P Q hPQ =
      finiteSubmoduleExtensionι F h P Q' (fun x hx ↦ hQQ' (hPQ x hx)) := by
  unfold finiteSubmoduleExtensionι
  refine (congrArg (F.map (FiniteStableSubmodule.hom h P Q hPQ) ≫ ·)
    (colimit.w (finiteStableSubmoduleDiagram N' ⋙ F) (homOfLE hQQ')).symm).trans ?_
  refine (F.map_comp_assoc _ _ _).symm.trans ?_
  exact congrArg (F.map · ≫ colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q')
    (FiniteStableSubmodule.hom_comp_diagram_map h P Q Q' hPQ (homOfLE hQQ'))

/-- **The map `F(P) ⟶ Φ(N')` does not depend on the finite stable submodule through which it is
taken.** -/
lemma finiteSubmoduleExtensionι_indep
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q Q' : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (hPQ' : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q'.1) :
    finiteSubmoduleExtensionι F h P Q hPQ = finiteSubmoduleExtensionι F h P Q' hPQ' := by
  rw [finiteSubmoduleExtensionι_of_le F h P Q (Q.sup Q') hPQ (Q.le_sup_left Q'),
    finiteSubmoduleExtensionι_of_le F h P Q' (Q.sup Q') hPQ' (Q.le_sup_right Q')]

/-- Preceding the map `F(P') ⟶ Φ(N')` by `F` of an inclusion `P ⟶ P'` gives the map
`F(P) ⟶ Φ(N')`. -/
lemma diagram_map_comp_finiteSubmoduleExtensionι
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') {P P' : FiniteStableSubmodule N} (i : P ⟶ P') (Q : FiniteStableSubmodule N')
    (hP'Q : ∀ x ∈ P'.1, h.hom.hom.hom.hom x ∈ Q.1) :
    (finiteStableSubmoduleDiagram N ⋙ F).map i ≫ finiteSubmoduleExtensionι F h P' Q hP'Q =
      finiteSubmoduleExtensionι F h P Q (fun x hx ↦ hP'Q x (leOfHom i hx)) := by
  unfold finiteSubmoduleExtensionι
  exact (F.map_comp_assoc _ _ _).symm.trans
    (congrArg (F.map · ≫ colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q)
      (FiniteStableSubmodule.diagram_map_comp_hom h P P' Q i hP'Q))

/-- The action of the extension on a morphism `h : N ⟶ N'`. -/
def finiteSubmoduleExtensionMap {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') : finiteSubmoduleExtensionObj F N ⟶ finiteSubmoduleExtensionObj F N' :=
  colimit.desc (finiteStableSubmoduleDiagram N ⋙ F)
    { pt := finiteSubmoduleExtensionObj F N'
      ι :=
        { app P := finiteSubmoduleExtensionι F h P (P.map h) (P.mem_map h)
          naturality P P' i :=
            (diagram_map_comp_finiteSubmoduleExtensionι F h i (P'.map h)
              (P'.mem_map h)).trans ((finiteSubmoduleExtensionι_indep F h P _ _ _ _).trans
                (Category.comp_id _).symm) } }

/-- **The computation rule of the extension on morphisms**: on `F(P)` it is `F` of the restriction
of `h` to `P ⟶ Q`, for any finite stable submodule `Q` containing `h(P)`. -/
lemma ι_finiteSubmoduleExtensionMap
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) :
    colimit.ι (finiteStableSubmoduleDiagram N ⋙ F) P ≫ finiteSubmoduleExtensionMap F h =
      F.map (FiniteStableSubmodule.hom h P Q hPQ) ≫
        colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q := by
  unfold finiteSubmoduleExtensionMap
  exact (colimit.ι_desc _ _).trans (finiteSubmoduleExtensionι_indep F h P _ Q _ hPQ)

/-- The computation rule `ι_finiteSubmoduleExtensionMap`, followed by an arbitrary morphism. -/
lemma ι_finiteSubmoduleExtensionMap_assoc
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) {Z : D}
    (k : finiteSubmoduleExtensionObj F N' ⟶ Z) :
    colimit.ι (finiteStableSubmoduleDiagram N ⋙ F) P ≫ finiteSubmoduleExtensionMap F h ≫ k =
      F.map (FiniteStableSubmodule.hom h P Q hPQ) ≫
        colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q ≫ k :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ k) (ι_finiteSubmoduleExtensionMap F h P Q hPQ)).trans (Category.assoc _ _ _))

/-- **The extension `Φ` of `F` to all continuous discrete `R`-`G`-modules**:
`Φ(N) = colim_{P ⊆ N} F(P)` over the finite `G`-stable submodules of `N`. -/
def finiteSubmoduleExtension :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ D where
  obj := finiteSubmoduleExtensionObj F
  map := finiteSubmoduleExtensionMap F
  map_id N := by
    apply colimit.hom_ext
    intro P
    refine (ι_finiteSubmoduleExtensionMap F (𝟙 N) P P (fun _ hx ↦ hx)).trans ?_
    refine (congrArg (F.map · ≫ colimit.ι (finiteStableSubmoduleDiagram N ⋙ F) P)
      (FiniteStableSubmodule.hom_id P)).trans ?_
    exact (congrArg (· ≫ colimit.ι (finiteStableSubmoduleDiagram N ⋙ F) P) (F.map_id _)).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp {N N' N''} h h' := by
    apply colimit.hom_ext
    intro P
    refine (ι_finiteSubmoduleExtensionMap F (h ≫ h') P ((P.map h).map h')
      (fun x hx ↦ (P.map h).mem_map h' _ (P.mem_map h x hx))).trans ?_
    refine Eq.symm ((ι_finiteSubmoduleExtensionMap_assoc F h P (P.map h) (P.mem_map h) _).trans ?_)
    refine (congrArg (F.map (FiniteStableSubmodule.hom h P (P.map h) (P.mem_map h)) ≫ ·)
      (ι_finiteSubmoduleExtensionMap F h' (P.map h) ((P.map h).map h')
        ((P.map h).mem_map h'))).trans ?_
    refine (F.map_comp_assoc _ _ _).symm.trans ?_
    exact congrArg (F.map · ≫ colimit.ι (finiteStableSubmoduleDiagram N'' ⋙ F) _)
      (FiniteStableSubmodule.hom_comp _ _ _ _ _ _ _)

/-- The inclusion `F(P) ⟶ Φ(N)` of a finite stable submodule, with its source spelled `F(P)`. -/
def finiteSubmoduleExtensionIncl {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (P : FiniteStableSubmodule N) : F.obj P.toFinite ⟶ (finiteSubmoduleExtension F).obj N :=
  colimit.ι (finiteStableSubmoduleDiagram N ⋙ F) P

/-- The inclusions are compatible with the inclusions of finite stable submodules. -/
lemma map_comp_finiteSubmoduleExtensionIncl
    {N : Stacks.Injectives.ContinuousModule.{u, v, w} R G} (P P' : FiniteStableSubmodule N)
    (hPP' : P ≤ P') :
    F.map (FiniteStableSubmodule.hom (𝟙 N) P P' fun _ hx ↦ hPP' hx) ≫
        finiteSubmoduleExtensionIncl F P' = finiteSubmoduleExtensionIncl F P :=
  colimit.w (finiteStableSubmoduleDiagram N ⋙ F) (homOfLE hPP')

/-- The computation rule of the extension on morphisms, through the inclusions. -/
lemma finiteSubmoduleExtensionIncl_comp_map
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) :
    finiteSubmoduleExtensionIncl F P ≫ (finiteSubmoduleExtension F).map h =
      F.map (FiniteStableSubmodule.hom h P Q hPQ) ≫ finiteSubmoduleExtensionIncl F Q :=
  ι_finiteSubmoduleExtensionMap F h P Q hPQ

/-- The value of the extension at `N` is the colimit of `F` over the finite stable submodules of
`N`. -/
@[simp]
lemma finiteSubmoduleExtension_obj (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    (finiteSubmoduleExtension F).obj N = colimit (finiteStableSubmoduleDiagram N ⋙ F) :=
  rfl

section Restriction

/-- The whole of a finite module, as a finite stable submodule. -/
def FiniteStableSubmodule.top (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    FiniteStableSubmodule M.obj :=
  ⟨⊤, fun _ _ _ ↦ Submodule.mem_top,
    haveI : Module.Finite R M.obj.obj.obj.V := (continuousModuleIsFG_iff _ _ _).1 M.property
    inferInstance⟩

/-- The whole module is the largest finite stable submodule of a finite module. -/
def FiniteStableSubmodule.isTerminalTop (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    IsTerminal (FiniteStableSubmodule.top M) :=
  IsTerminal.ofUnique _ (h := fun _ ↦ ⟨⟨homOfLE (fun _ _ ↦ Submodule.mem_top)⟩,
    fun _ ↦ Subsingleton.elim _ _⟩)

/-- The inclusion of the whole of a finite module into itself is an isomorphism. -/
instance isIso_finiteStableSubmoduleTop_ι (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    IsIso (FiniteStableSubmodule.top M).ι := by
  have h : IsIso ((finiteTypeContinuousModuleι.{u, v, w} R G).map
      (FiniteStableSubmodule.top M).ι) := by
    have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{u, v, w} R G
    have : IsIso ((Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).map
        ((finiteTypeContinuousModuleι.{u, v, w} R G).map (FiniteStableSubmodule.top M).ι)) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨fun x y hxy ↦ Subtype.ext hxy, fun y ↦ ⟨⟨y, Submodule.mem_top⟩, rfl⟩⟩
    exact isIso_of_reflects_iso _ (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G)
  exact isIso_of_fully_faithful (finiteTypeContinuousModuleι.{u, v, w} R G) _

/-- The cocone `F(P) ⟶ F(M)` of the inclusions of the finite stable submodules of a finite
module. -/
def finiteStableSubmoduleCocone (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    Cocone (finiteStableSubmoduleDiagram M.obj ⋙ F) where
  pt := F.obj M
  ι :=
    { app P := F.map P.ι
      naturality _ _ i := (F.map_comp _ _).symm.trans
        ((congrArg F.map (FiniteStableSubmodule.diagram_map_comp_ι i)).trans
          (Category.comp_id _).symm) }

/-- The inclusions of the finite stable submodules of a finite module form a colimit cocone,
the whole module being the largest of them. -/
def isColimitFiniteStableSubmoduleCocone (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    IsColimit (finiteStableSubmoduleCocone F M) :=
  IsColimit.ofIsoColimit (colimitOfDiagramTerminal (FiniteStableSubmodule.isTerminalTop M) _)
    (Cocone.ext (F.mapIso (@asIso _ _ _ _ (FiniteStableSubmodule.top M).ι
      (isIso_finiteStableSubmoduleTop_ι M))) fun _ ↦
      (F.map_comp _ _).symm.trans (congrArg F.map (FiniteStableSubmodule.diagram_map_comp_ι _)))

/-- The value of the extension at a finite module is `F` of it. -/
def finiteSubmoduleExtensionObjIso (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    (finiteSubmoduleExtension F).obj M.obj ≅ F.obj M :=
  colimit.isoColimitCocone ⟨_, isColimitFiniteStableSubmoduleCocone F M⟩

/-- On `F(P)`, the isomorphism `Φ(M) ≅ F(M)` is `F` of the inclusion `P ⟶ M`. -/
lemma ι_finiteSubmoduleExtensionObjIso_hom (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (P : FiniteStableSubmodule M.obj) :
    colimit.ι (finiteStableSubmoduleDiagram M.obj ⋙ F) P ≫
        (finiteSubmoduleExtensionObjIso F M).hom = F.map P.ι :=
  colimit.isoColimitCocone_ι_hom _ _

/-- **The extension restricted to the finite modules is `F`.** -/
def finiteSubmoduleExtensionιIso :
    finiteTypeContinuousModuleι.{u, v, w} R G ⋙ finiteSubmoduleExtension F ≅ F :=
  NatIso.ofComponents (finiteSubmoduleExtensionObjIso F) fun {M M'} h ↦ by
    apply colimit.hom_ext
    intro P
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (finiteSubmoduleExtensionObjIso F M').hom)
      (ι_finiteSubmoduleExtensionMap F h.hom P (FiniteStableSubmodule.top M')
        (fun _ _ ↦ Submodule.mem_top))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (F.map (FiniteStableSubmodule.hom h.hom P (FiniteStableSubmodule.top M')
        (fun _ _ ↦ Submodule.mem_top)) ≫ ·) (ι_finiteSubmoduleExtensionObjIso_hom F M' _)).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (· ≫ F.map h) (ι_finiteSubmoduleExtensionObjIso_hom F M P)).trans ?_
    refine (F.map_comp _ _).symm.trans ((congrArg F.map ?_).trans (F.map_comp _ _))
    exact ObjectProperty.hom_ext _ (continuousModule_hom_ext fun _ ↦ rfl)

/-- On `F(P)`, the component at `M` of `finiteSubmoduleExtensionιIso` is `F` of the inclusion
`P ⟶ M`. -/
lemma finiteSubmoduleExtensionIncl_comp_ιIso_hom (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (P : FiniteStableSubmodule M.obj) :
    finiteSubmoduleExtensionIncl F P ≫ (finiteSubmoduleExtensionιIso F).hom.app M = F.map P.ι :=
  ι_finiteSubmoduleExtensionObjIso_hom F M P

end Restriction

section Additive

variable [Preadditive D] [F.Additive]

/-- The morphism of finite stable submodules induced by a sum is the sum of the induced
morphisms. -/
lemma FiniteStableSubmodule.hom_add {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h h' : N ⟶ N') (P : FiniteStableSubmodule N) (Q : FiniteStableSubmodule N')
    (hPQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1) (hPQ' : ∀ x ∈ P.1, h'.hom.hom.hom.hom x ∈ Q.1) :
    FiniteStableSubmodule.hom (h + h') P Q (fun x hx ↦ Q.1.add_mem (hPQ x hx) (hPQ' x hx)) =
      FiniteStableSubmodule.hom h P Q hPQ + FiniteStableSubmodule.hom h' P Q hPQ' :=
  finiteType_hom_ext fun _ ↦ rfl

/-- **The extension of an additive functor is additive.** -/
instance finiteSubmoduleExtension_additive : (finiteSubmoduleExtension F).Additive where
  map_add {N N' h h'} := by
    apply colimit.hom_ext
    intro P
    let Q := (P.map h).sup (P.map h')
    have hQ : ∀ x ∈ P.1, h.hom.hom.hom.hom x ∈ Q.1 :=
      fun x hx ↦ (P.map h).le_sup_left (P.map h') (P.mem_map h x hx)
    have hQ' : ∀ x ∈ P.1, h'.hom.hom.hom.hom x ∈ Q.1 :=
      fun x hx ↦ (P.map h).le_sup_right (P.map h') (P.mem_map h' x hx)
    refine (ι_finiteSubmoduleExtensionMap F (h + h') P Q
      (fun x hx ↦ Q.1.add_mem (hQ x hx) (hQ' x hx))).trans ?_
    refine (congrArg (F.map · ≫ colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q)
      (FiniteStableSubmodule.hom_add h h' P Q hQ hQ')).trans ?_
    refine (congrArg (· ≫ colimit.ι (finiteStableSubmoduleDiagram N' ⋙ F) Q)
      F.map_add).trans ?_
    refine (Preadditive.add_comp _ _ _ _ _ _).trans ?_
    refine Eq.symm ((Preadditive.comp_add _ _ _ _ _ _).trans ?_)
    exact congrArg₂ (· + ·) (ι_finiteSubmoduleExtensionMap F h P Q hQ)
      (ι_finiteSubmoduleExtensionMap F h' P Q hQ')

end Additive

/-- The finite stable submodules form a filtered category. -/
instance (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    IsFiltered (FiniteStableSubmodule N) :=
  isFiltered_of_directed_le_nonempty _

section Orbits

variable [CompactSpace G]

/-- The orbit of an element of a continuous discrete module under a compact group is finite: the
stabilizer is open, hence of finite index. -/
lemma finite_range_ρ_apply (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (x : N.obj.obj.V) : (Set.range fun g : G ↦ (N.obj.obj.ρ g).asHom.hom x).Finite := by
  have ρ_mul_apply (g h : G) (y : N.obj.obj.V) :
      (N.obj.obj.ρ (g * h)).asHom.hom y = (N.obj.obj.ρ g).asHom.hom ((N.obj.obj.ρ h).asHom.hom y) := by
    rw [map_mul, End.mul_asHom, ModuleCat.hom_comp, LinearMap.comp_apply]
  let S : Subgroup G :=
    { carrier := {g | (N.obj.obj.ρ g).asHom.hom x = x}
      one_mem' := by simp [End.one_asHom]
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [ρ_mul_apply, hb, ha]
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← ρ_mul_apply, inv_mul_cancel, map_one, End.one_asHom, ModuleCat.hom_id,
          LinearMap.id_apply] }
  have := Subgroup.quotient_finite_of_isOpen S (isOpen_stabilizer R G N x)
  let f' : G ⧸ S → N.obj.obj.V := Quotient.lift (fun g ↦ (N.obj.obj.ρ g).asHom.hom x) fun a b hab ↦ by
    have hab' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 hab
    change (N.obj.obj.ρ (a⁻¹ * b)).asHom.hom x = x at hab'
    calc (N.obj.obj.ρ a).asHom.hom x = (N.obj.obj.ρ a).asHom.hom ((N.obj.obj.ρ (a⁻¹ * b)).asHom.hom x) := by
          rw [hab']
      _ = (N.obj.obj.ρ b).asHom.hom x := by
          rw [← ρ_mul_apply, mul_inv_cancel_left]
  refine (Set.finite_range f').subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨(g : G ⧸ S), rfl⟩

/-- **The finite stable submodule spanned by the orbits of a finite set** of elements. -/
def FiniteStableSubmodule.orbitSpan (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (s : Set N.obj.obj.V) (hs : s.Finite) : FiniteStableSubmodule N :=
  ⟨Submodule.span R (⋃ x ∈ s, Set.range fun g : G ↦ (N.obj.obj.ρ g).asHom.hom x), by
      intro g x hx
      have : Submodule.span R (⋃ x ∈ s, Set.range fun g : G ↦ (N.obj.obj.ρ g).asHom.hom x) ≤
          (Submodule.span R (⋃ x ∈ s, Set.range fun g : G ↦ (N.obj.obj.ρ g).asHom.hom x)).comap
            (N.obj.obj.ρ g).asHom.hom := by
        rw [Submodule.span_le]
        intro y hy
        simp only [Set.mem_iUnion, Set.mem_range] at hy
        obtain ⟨z, hz, g', rfl⟩ := hy
        refine Submodule.subset_span ?_
        simp only [Set.mem_iUnion, Set.mem_range]
        refine ⟨z, hz, g * g', ?_⟩
        rw [map_mul, End.mul_asHom, ModuleCat.hom_comp, LinearMap.comp_apply]
      exact this hx,
    Module.Finite.span_of_finite R (hs.biUnion fun z _ ↦ finite_range_ρ_apply N z)⟩

/-- A finite set is contained in the span of its orbits. -/
lemma FiniteStableSubmodule.subset_orbitSpan
    (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) (s : Set N.obj.obj.V) (hs : s.Finite) :
    s ⊆ (FiniteStableSubmodule.orbitSpan N s hs).1 := fun x hx ↦
  Submodule.subset_span (Set.mem_biUnion hx ⟨1, by simp [End.one_asHom]⟩)

/-- The orbit span of a finite set is the smallest finite stable submodule containing it. -/
lemma FiniteStableSubmodule.orbitSpan_le
    (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) (s : Set N.obj.obj.V) (hs : s.Finite)
    (P : FiniteStableSubmodule N) (h : s ⊆ P.1) : FiniteStableSubmodule.orbitSpan N s hs ≤ P := by
  show Submodule.span R _ ≤ P.1
  rw [Submodule.span_le]
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨z, hz, g, rfl⟩ := hy
  exact P.2.1 g z (h hz)

/-- **Finite stable submodules lift along a surjection**: every finite stable submodule of the
target is contained in the image of a finite stable submodule of the source, spanned by the
orbits of lifts of finitely many generators. -/
lemma FiniteStableSubmodule.exists_le_map
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (hsurj : Function.Surjective h.hom.hom.hom.hom) (Q : FiniteStableSubmodule N') :
    ∃ P : FiniteStableSubmodule N, Q ≤ P.map h := by
  obtain ⟨t, ht⟩ := Module.Finite.iff_fg.1 Q.2.2
  choose b hb using hsurj
  refine ⟨FiniteStableSubmodule.orbitSpan N (b '' (t : Set N'.obj.obj.V))
    (t.finite_toSet.image b), ?_⟩
  show Q.1 ≤ Submodule.map h.hom.hom.hom.hom _
  rw [← ht, Submodule.span_le]
  intro q hq
  refine Submodule.mem_map.2 ⟨b q, FiniteStableSubmodule.subset_orbitSpan N _ _ ⟨q, hq, rfl⟩,
    hb q⟩


end Orbits

section Exactness

variable [IsNoetherianRing R] [CompactSpace G]

/-- The preimage of a finite stable submodule under an injective morphism. -/
def FiniteStableSubmodule.comap {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (hinj : Function.Injective h.hom.hom.hom.hom) (P : FiniteStableSubmodule N') :
    FiniteStableSubmodule N :=
  ⟨P.1.comap h.hom.hom.hom.hom, fun g x hx ↦ by
      change h.hom.hom.hom.hom ((N.obj.obj.ρ g).asHom.hom x) ∈ P.1
      rw [show h.hom.hom.hom.hom ((N.obj.obj.ρ g).asHom.hom x) =
        (N'.obj.obj.ρ g).asHom.hom (h.hom.hom.hom.hom x) from
          ConcreteCategory.congr_hom (h.hom.hom.comm g) x]
      exact P.2.1 g _ hx,
    haveI := P.2.2
    Module.Finite.of_injective (h.hom.hom.hom.hom.restrict (p := P.1.comap h.hom.hom.hom.hom)
      (q := P.1) (fun _ hx ↦ hx)) (fun x y hxy ↦ Subtype.ext (hinj (congrArg Subtype.val hxy)))⟩

/-- Preimage of finite stable submodules under an injective morphism, as a functor. -/
def FiniteStableSubmodule.comapFunctor
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (hinj : Function.Injective h.hom.hom.hom.hom) :
    FiniteStableSubmodule N' ⥤ FiniteStableSubmodule N :=
  Monotone.functor (f := FiniteStableSubmodule.comap h hinj)
    (fun _ _ hPQ ↦ Submodule.comap_mono (f := h.hom.hom.hom.hom) hPQ)

/-- Image of finite stable submodules under a morphism, as a functor. -/
def FiniteStableSubmodule.mapFunctor {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') : FiniteStableSubmodule N ⥤ FiniteStableSubmodule N' :=
  Monotone.functor (f := FiniteStableSubmodule.map h)
    (fun _ _ hPQ ↦ Submodule.map_mono (f := h.hom.hom.hom.hom) hPQ)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- Preimage of finite stable submodules under an injective morphism is a final functor. -/
lemma FiniteStableSubmodule.final_comapFunctor
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (hinj : Function.Injective h.hom.hom.hom.hom) :
    (FiniteStableSubmodule.comapFunctor h hinj).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun Q ↦ ⟨Q.map h, ⟨homOfLE fun _ hx ↦ Submodule.mem_comap.2 (Submodule.mem_map_of_mem hx)⟩⟩)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

omit [IsNoetherianRing R] in
/-- Image of finite stable submodules under a surjective morphism is a final functor. -/
lemma FiniteStableSubmodule.final_mapFunctor
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R G}
    (h : N ⟶ N') (hsurj : Function.Surjective h.hom.hom.hom.hom) :
    (FiniteStableSubmodule.mapFunctor h).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun Q ↦ (FiniteStableSubmodule.exists_le_map h hsurj Q).imp fun _ hP ↦ ⟨homOfLE hP⟩)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A short complex of finite modules is short exact as soon as its underlying sequence of modules
is: the first map is injective, the second surjective, and the kernel of the second is the image
of the first. -/
lemma shortExact_of_elements (S : ShortComplex (FiniteTypeContinuousModule.{u, v, w} R G))
    (hf : Function.Injective S.f.hom.hom.hom.hom.hom)
    (hg : Function.Surjective S.g.hom.hom.hom.hom.hom)
    (hex : ∀ y, S.g.hom.hom.hom.hom.hom y = 0 → ∃ x, S.f.hom.hom.hom.hom.hom x = y) :
    S.ShortExact := by
  have := preservesFiniteLimits_finiteTypeContinuousModuleι.{u, v, w} R G
  have := preservesFiniteColimits_finiteTypeContinuousModuleι.{u, v, w} R G
  have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R G
  have := preservesFiniteColimits_continuousModuleToModuleCat.{u, v, w} R G
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{u, v, w} R G
  let U := finiteTypeContinuousModuleι.{u, v, w} R G ⋙
    Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G
  have : PreservesFiniteLimits U := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits U := comp_preservesFiniteColimits _ _
  have : U.Additive := Functor.additive_of_preserves_binary_products U
  have hU : JointlyReflectIsomorphisms (fun _ : Unit ↦ U) :=
    ⟨fun f hf ↦ by have := hf (); exact isIso_of_reflects_iso f U⟩
  refine (hU.shortExact_iff S).2 fun _ ↦ ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.moduleCat_exact_iff _).2 hex
  · exact (ModuleCat.mono_iff_injective _).2 hf
  · exact (ModuleCat.epi_iff_surjective _).2 hg

variable [Abelian D] [AB5OfSize.{w, w} D] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Additive]

omit [AB5OfSize.{w, w} D] in
/-- A filtered colimit of pointwise short exact sequences is short exact. -/
lemma shortExact_map_colim {J : Type w} [SmallCategory J] [IsFiltered J]
    [HasExactColimitsOfShape J D] (T : ShortComplex (J ⥤ D))
    (hT : ∀ j, (T.map ((evaluation J D).obj j)).ShortExact) : (T.map colim).ShortExact := by
  have hP : JointlyReflectIsomorphisms (fun j : J ↦ (evaluation J D).obj j) :=
    ⟨fun f hf ↦ @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f hf⟩
  exact ((hP.shortExact_iff T).2 hT).map_of_exact colim

/-- **The extension of an exact functor preserves short exact sequences.** -/
theorem finiteSubmoduleExtension_map_shortExact
    (S : ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R G)) (hS : S.ShortExact) :
    (S.map (finiteSubmoduleExtension F)).ShortExact := by
  have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R G
  have := preservesFiniteColimits_continuousModuleToModuleCat.{u, v, w} R G
  have := additive_continuousModuleToModuleCat.{u, v, w} R G
  let U := Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G
  have hf : Function.Injective S.f.hom.hom.hom.hom := by
    have := hS.mono_f
    exact (ModuleCat.mono_iff_injective (U.map S.f)).1 inferInstance
  have hg : Function.Surjective S.g.hom.hom.hom.hom := by
    have := hS.epi_g
    exact (ModuleCat.epi_iff_surjective (U.map S.g)).1 inferInstance
  have hex := (ShortComplex.moduleCat_exact_iff (S.map U)).1 (hS.exact.map U)
  have hzero : ∀ x, S.g.hom.hom.hom.hom (S.f.hom.hom.hom.hom x) = 0 := fun x ↦
    congrArg (fun φ ↦ φ.hom.hom.hom.hom x) S.zero
  let pre := FiniteStableSubmodule.comapFunctor S.f hf
  let img := FiniteStableSubmodule.mapFunctor S.g
  have := FiniteStableSubmodule.final_comapFunctor S.f hf
  have := FiniteStableSubmodule.final_mapFunctor S.g hg
  let fP (P : FiniteStableSubmodule S.X₂) : (pre.obj P).toFinite ⟶ P.toFinite :=
    FiniteStableSubmodule.hom S.f (pre.obj P) P fun _ hx ↦ hx
  let gP (P : FiniteStableSubmodule S.X₂) : P.toFinite ⟶ (img.obj P).toFinite :=
    FiniteStableSubmodule.hom S.g P (img.obj P) (P.mem_map S.g)
  have hzP : ∀ P, fP P ≫ gP P = 0 := fun P ↦
    ObjectProperty.hom_ext _ (continuousModule_hom_ext fun x ↦ Subtype.ext (hzero x.1))
  have hSP : ∀ P, (ShortComplex.mk (fP P) (gP P) (hzP P)).ShortExact := fun P ↦ by
    refine shortExact_of_elements _ (fun x y hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy)))
      ?_ ?_
    · rintro ⟨_, ⟨y, hy, rfl⟩⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hex y.1 (congrArg Subtype.val hy)
      exact ⟨⟨x, show S.f.hom.hom.hom.hom x ∈ P.1 from hx ▸ y.2⟩, Subtype.ext hx⟩
  let T : ShortComplex (FiniteStableSubmodule S.X₂ ⥤ D) :=
    { X₁ := pre ⋙ finiteStableSubmoduleDiagram S.X₁ ⋙ F
      X₂ := finiteStableSubmoduleDiagram S.X₂ ⋙ F
      X₃ := img ⋙ finiteStableSubmoduleDiagram S.X₃ ⋙ F
      f :=
        { app P := F.map (fP P)
          naturality P P' i := by
            simp only [Functor.comp_map, ← F.map_comp]
            exact congrArg F.map (finiteType_hom_ext fun _ ↦ rfl) }
      g :=
        { app P := F.map (gP P)
          naturality P P' i := by
            simp only [Functor.comp_map, ← F.map_comp]
            exact congrArg F.map (finiteType_hom_ext fun _ ↦ rfl) }
      zero := NatTrans.ext (funext fun P ↦ (F.map_comp _ _).symm.trans
        ((congrArg F.map (hzP P)).trans (F.map_zero _ _))) }
  have hT : (T.map colim).ShortExact :=
    shortExact_map_colim T fun P ↦ (hSP P).map_of_exact F
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk
    (Functor.Final.colimitIso pre (finiteStableSubmoduleDiagram S.X₁ ⋙ F)) (Iso.refl _)
    (Functor.Final.colimitIso img (finiteStableSubmoduleDiagram S.X₃ ⋙ F)) ?_ ?_
  · apply colimit.hom_ext
    intro P
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ finiteSubmoduleExtensionMap F S.f)
      (Functor.Final.ι_colimitIso_hom pre _ P)).trans ?_
    refine (ι_finiteSubmoduleExtensionMap F S.f (pre.obj P) P fun _ hx ↦ hx).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
    refine (Category.comp_id _).trans ?_
    exact colimit.ι_map T.f P
  · apply colimit.hom_ext
    intro P
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ finiteSubmoduleExtensionMap F S.g) (Category.comp_id _)).trans ?_
    refine (ι_finiteSubmoduleExtensionMap F S.g P (img.obj P) (P.mem_map S.g)).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (· ≫ (Functor.Final.colimitIso img
      (finiteStableSubmoduleDiagram S.X₃ ⋙ F)).hom) (colimit.ι_map T.g P)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (F.map (gP P) ≫ ·) (Functor.Final.ι_colimitIso_hom img _ P)

/-- **The extension of an exact functor is exact.** -/
theorem finiteSubmoduleExtension_exact :
    PreservesFiniteLimits (finiteSubmoduleExtension F) ∧
      PreservesFiniteColimits (finiteSubmoduleExtension F) :=
  ((Functor.exact_tfae (finiteSubmoduleExtension F)).out 1 4).1
    (finiteSubmoduleExtension_map_shortExact F)

/-- The extension of an exact functor preserves finite limits. -/
theorem preservesFiniteLimits_finiteSubmoduleExtension :
    PreservesFiniteLimits (finiteSubmoduleExtension F) :=
  (finiteSubmoduleExtension_exact F).1

/-- The extension of an exact functor preserves finite colimits. -/
theorem preservesFiniteColimits_finiteSubmoduleExtension :
    PreservesFiniteColimits (finiteSubmoduleExtension F) :=
  (finiteSubmoduleExtension_exact F).2

end Exactness

end Extension

end Stacks.ContinuousCohomology

end
