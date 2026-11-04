module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008T — the pullback of a presheaf of modules along a continuous map

Fix a continuous map `f : X → Y` of topological spaces and a presheaf of rings `O` on `Y`.
The pullback presheaf `f_p G` of a presheaf `G` on `Y` is given by the filtered colimit
`(f_p G)(U) = colim_{V ∈ N(U)} G(V)`, where `N(U)` is the poset of open neighbourhoods
`V ⊆ Y` of `f(U)` ordered by reverse inclusion; it is Mathlib's `TopCat.Presheaf.pullback`,
the left adjoint of the pushforward, built as the left Kan extension along `(Opens.map f).op`.
Applied to `O` it yields a presheaf of rings `f_p O` on `X`.

Tag 008T states, for a presheaf of `O`-modules `G`, that

* there is a natural scalar multiplication `f_p O × f_p G → f_p G`, built sectionwise from
  the fact that filtered colimits commute with finite products (Stacks 002W, in Mathlib
  `filtered_colim_preservesFiniteLimits_of_types`), and it makes `f_p G` a presheaf of
  `f_p O`-modules — `pullback_presheaf_module`;
* the construction is functorial in `G`, i.e. `f_p` lifts to a functor
  `PMod(O) ⥤ PMod(f_p O)` — `pullbackModuleFunctor` — lying over the abelian-group-level
  pullback, the comparison isomorphism being `pullbackModuleFunctorCompToPresheaf`.

The sectionwise module structure `pullbackModule` is obtained by transporting Mathlib's
`PresheafOfModules.ModuleColimit`, which puts a `Module (colim O(V)) (colim G(V))` structure
on a filtered colimit with the germ formula `[V, a] • [V, s] = [V, a • s]`, along the
comparison isomorphisms `pbRingIso` and `pbAbIso` between the Kan-extension sections and the
colimits over the costructured-arrow category presenting `N(U)`.

Two general Kan-extension lemmas are proved along the way:
`leftKanExtensionObjIsoColimit_naturality`, saying that restriction maps re-index germs, and
its analogue `lke_morphism_naturality` for a morphism of the extended functors. Since the
transported action is opaque on elements, `pullbackModule_unit_smul` records the germ formula
it satisfies: the Kan-extension units `O(V) → (f_p O)(f^{-1}V)` and `G(V) → (f_p G)(f^{-1}V)`
are semilinear, `unit (a • m) = unit a • unit m`.

## Implementation notes

**Universes.** Everything is stated at a single universe `u` carrying the space, the rings
and the module sections together.  That single universe is forced, not chosen:
`TopCat.Presheaf.pullback` asks for `[Category.{u₁, u₂} C]` with `u₁` the universe of the
space, so with `C = RingCat.{v}` (whose hom universe is `v`) the pullback already forces
`v = u`; and `PresheafOfModules.ModuleColimit` is stated for
`{R : Cᵒᵖ ⥤ RingCat.{v}} {M : PresheafOfModules.{v} R}` with `[InitiallySmall.{v} C]`, so the
module universe and the smallness universe are both the ring universe.  This is why the
`FinallySmall`/`InitiallySmall` instances below are supplied at `.{u}` and not at some
smaller level: the level is not free.  The `RingCat`, `Ab` and `PresheafOfModules` arguments
must be written `.{u}` explicitly — left implicit they default to `0` and silently collapse
every universe in the statement.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits

namespace Stacks.PresheafOfModules.Pullback

universe u v

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

-- Stacks 002W: in `Type`, filtered colimits commute with finite limits (hence finite
-- products). This is the only nontrivial input to the construction of the scalar
-- multiplication `μ`.
example {K : Type v} [Category.{v} K] [IsFiltered K] :
    PreservesFiniteLimits (colim (J := K) (C := Type v)) :=
  CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types

/-- The pullback presheaf of rings `f_p O` (cf. Tag 008F). Its sections are the filtered
colimits `(f_p O)(U) = colim_{V ∈ N(U)} O(V)`, carrying the colimit ring structure. -/
noncomputable def pullbackRing (O : TopCat.Presheaf RingCat.{u} Y) :
    TopCat.Presheaf RingCat.{u} X :=
  (TopCat.Presheaf.pullback RingCat.{u} f).obj O

/-- The pullback presheaf of abelian groups `f_p G`. Its sections are
`(f_p G)(U) = colim_{V ∈ N(U)} G(V)`. -/
noncomputable def pullbackAb (G : TopCat.Presheaf Ab.{u} Y) :
    TopCat.Presheaf Ab.{u} X :=
  (TopCat.Presheaf.pullback Ab.{u} f).obj G

/-- The underlying presheaf of abelian groups of a presheaf of `O`-modules `G`
(forgetting the module structure), i.e. `G` viewed as a presheaf of abelian groups on
`Y`. -/
noncomputable def underlyingAb (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O) :
    TopCat.Presheaf Ab.{u} Y :=
  (PresheafOfModules.toPresheaf O).obj G

/-- Transport a `Module R A` structure across an additive isomorphism `e : A ≃+ B` of the
underlying abelian group, producing a `Module R B`. The scalar action is
`r • b = e (r • e.symm b)`; all module axioms follow from those of `A` since `e` and `e.symm`
are additive. (Auxiliary construction for `pullbackModule`.) -/
@[reducible] noncomputable def moduleOfAddEquiv {R A B : Type*} [Semiring R] [AddCommGroup A]
    [AddCommGroup B] [Module R A] (e : A ≃+ B) : Module R B where
  smul r b := e (r • e.symm b)
  one_smul b := show e (1 • e.symm b) = b by simp
  mul_smul r s b := show e ((r * s) • e.symm b) = e (r • e.symm (e (s • e.symm b))) by
    simp [mul_smul]
  smul_zero r := show e (r • e.symm 0) = 0 by simp
  smul_add r b₁ b₂ := show e (r • e.symm (b₁ + b₂)) = e (r • e.symm b₁) + e (r • e.symm b₂) by
    simp [smul_add]
  add_smul r s b := show e ((r + s) • e.symm b) = e (r • e.symm b) + e (s • e.symm b) by
    simp [add_smul]
  zero_smul b := show e ((0 : R) • e.symm b) = 0 by simp

/-- Index functor: the diagram shape for the colimit, written over the double opposite
`((CostructuredArrow ..)ᵒᵖ)ᵒᵖ` so that `ModuleColimit` (whose diagram lives over `Cᵒᵖ`)
applies with `C = (CostructuredArrow ..)ᵒᵖ`. -/
@[reducible] noncomputable def pbIdx
    (U : (Opens X)ᵒᵖ) :
    ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ ⥤ (Opens Y)ᵒᵖ :=
  (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor ⋙
    CostructuredArrow.proj (Opens.map f).op U

/-- The diagram of rings `O(V)` over the index `pbIdx`. -/
@[reducible] noncomputable def pbRdiag (O : TopCat.Presheaf RingCat.{u} Y)
    (U : (Opens X)ᵒᵖ) :
    ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ ⥤ RingCat.{u} :=
  pbIdx f U ⋙ O

/-- Sectionwise module structure of the diagram `pbIdx ⋙ G.presheaf` over `pbRdiag`. -/
noncomputable instance pbInstMod (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (U : (Opens X)ᵒᵖ) (c) :
    Module ((pbRdiag f O U).obj c) ((pbIdx f U ⋙ G.presheaf).obj c) :=
  (G.obj ((pbIdx f U).obj c)).isModule

/-- The presheaf of `pbRdiag`-modules whose underlying presheaf of abelian groups is
`pbIdx ⋙ G.presheaf`. -/
@[reducible] noncomputable def pbMmod (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) (U : (Opens X)ᵒᵖ) :
    PresheafOfModules.{u} (pbRdiag f O U) :=
  PresheafOfModules.ofPresheaf (R := pbRdiag f O U) (pbIdx f U ⋙ G.presheaf)
    (fun {_ _} h r m => G.map_smul ((pbIdx f U).map h) r m)

/-- The module structure on the colimit-abelian-group over the colimit-ring (germ formula),
from `ModuleColimit`. -/
@[reducible] noncomputable def pbInstCM (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) (U : (Opens X)ᵒᵖ) :
    Module ↑(colimit (pbRdiag f O U)) ↑(colimit (pbMmod f O G U).presheaf) := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  haveI : InitiallySmall.{u} ((CostructuredArrow (Opens.map f).op U)ᵒᵖ) := inferInstance
  exact PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat
    (colimit.isColimit (pbRdiag f O U)) (colimit.isColimit (pbMmod f O G U).presheaf)

/-- The comparison isomorphism between `colimit pbRdiag` and the pullback ring section. -/
noncomputable def pbRingIso (O : TopCat.Presheaf RingCat.{u} Y)
    (U : (Opens X)ᵒᵖ) : colimit (pbRdiag f O U) ≅ (pullbackRing f O).obj U := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  haveI : InitiallySmall.{u} ((CostructuredArrow (Opens.map f).op U)ᵒᵖ) := inferInstance
  exact (Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
      (CostructuredArrow.proj (Opens.map f).op U ⋙ O)) ≪≫
    ((Opens.map f).op.leftKanExtensionObjIsoColimit O U).symm

/-- The comparison isomorphism between `colimit (pbMmod).presheaf` and the pullback Ab
section. -/
noncomputable def pbAbIso (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (U : (Opens X)ᵒᵖ) :
    colimit (pbMmod f O G U).presheaf ≅ (pullbackAb f (underlyingAb O G)).obj U := by
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  haveI : InitiallySmall.{u} ((CostructuredArrow (Opens.map f).op U)ᵒᵖ) := inferInstance
  exact (Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
      (CostructuredArrow.proj (Opens.map f).op U ⋙ G.presheaf)) ≪≫
    ((Opens.map f).op.leftKanExtensionObjIsoColimit G.presheaf U).symm

/- The construction below rests on the single nontrivial input Stacks 002W cited above: in
`Type`, filtered colimits commute with finite products. Mathlib packages the resulting
module structure in `PresheafOfModules.ModuleColimit`: given a colimit ring `cR.pt` and a
colimit abelian group `cM.pt` over the SAME filtered index, it puts a `Module cR.pt cM.pt`
structure on the colimit abelian group, with the germ formula `[V, a] • [V, s] = [V, a • s]`.
Everything below specialises that machinery to the index category `N(U)` of open
neighbourhoods of `f(U)`, which is the costructured-arrow category
`CostructuredArrow ((Opens.map f).op) U` underlying
`TopCat.Presheaf.pullback = (Opens.map f).op.lan`.

The assembly uses `PresheafOfModules.ofPresheaf`, which builds a `PresheafOfModules R` from a
*prescribed* presheaf of abelian groups `M : Cᵒᵖ ⥤ Ab` with sectionwise
`Module (R.obj X) (M.obj X)` instances and a semilinearity hypothesis. Crucially
`(ofPresheaf M h).presheaf = M` holds by `rfl`, so the equality
`(toPresheaf _).obj M = pullbackAb f (underlyingAb O G)` demanded by the tag is closed by
`rfl`. -/

/-- **The scalar multiplication and the module axioms, sectionwise.**

For each open `U ⊆ X`, the abelian group `(f_p G)(U) = colim_{V ∈ N(U)} G(V)` carries a
module structure over the ring `(f_p O)(U) = colim_{V ∈ N(U)} O(V)`.

Both colimits are taken over the same filtered index category
`N(U) = CostructuredArrow ((Opens.map f).op) U` of open neighbourhoods of `f(U)` under
reverse inclusion. By Stacks 002W the forgetful functors to `Type` preserve these filtered
colimits and filtered colimits commute with the finite product, so there is a canonical
bijection `colim (O(V) × G(V)) ≅ (colim O(V)) × (colim G(V))`; the scalar action is the
composite of its inverse with `colim` of the levelwise actions `O(V) × G(V) → G(V)`. On
representatives it is `[V, a] • [V, s] = [V, a • s]`, well defined because `N(U)` is filtered,
so any two germs share a representative `V`, and the module axioms reduce to those of the
`O(V)`-module `G(V)` at a common representative.

Formally this is `PresheafOfModules.ModuleColimit` for
`R := CostructuredArrow.proj _ U ⋙ O` and `M := CostructuredArrow.proj _ U ⋙ G.presheaf`,
transported along `pbRingIso` and `pbAbIso`, the comparison isomorphisms of the colimits with
the Kan-extension sections `(f_p O)(U)` and `(f_p G)(U)`. -/
@[reducible] noncomputable def pullbackModule (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) (U : (Opens X)ᵒᵖ) :
    Module ((pullbackRing f O).obj U) ((pullbackAb f (underlyingAb O G)).obj U) :=
  letI := pbInstCM f O G U
  letI : Module ((pullbackRing f O).obj U) ↑(colimit (pbMmod f O G U).presheaf) :=
    Module.compHom (↑(colimit (pbMmod f O G U).presheaf))
      (pbRingIso f O U).ringCatIsoToRingEquiv.symm.toRingHom
  moduleOfAddEquiv (addEquivIsoAddCommGroupIso.inv (pbAbIso f O G U))

/-- **Characterization of the transported scalar action.**
Unfolds the `•` of `pullbackModule` in terms of the named comparison isos and the
`ModuleColimit` action `pbInstCM`. -/
theorem pullbackModule_smul_eq (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (U : (Opens X)ᵒᵖ) (r : (pullbackRing f O).obj U)
    (m : (pullbackAb f (underlyingAb O G)).obj U) :
    letI := pullbackModule f O G U
    letI := pbInstCM f O G U
    r • m = (pbAbIso f O G U).hom
      ((pbRingIso f O U).ringCatIsoToRingEquiv.symm r •
        (pbAbIso f O G U).symm.hom m) := by
  rfl

/-- **Naturality of the Kan-extension/colimit comparison isomorphism: restriction maps
re-index germs.**

For a left Kan extension `L.leftKanExtension F` and a morphism `i : U ⟶ V` in the target
category `D`, the restriction map `(L.leftKanExtension F).map i` is intertwined, via the
pointwise-colimit comparison isos at `U` and `V`, with the colimit reindexing map
`colimit.pre _ (CostructuredArrow.map i)` along the functor `CostructuredArrow.map i` of
costructured-arrow categories.

This is a purely Kan-extension/colimit statement — no modules, no transport — and is used
below once for the ring presheaf `O` and once for the abelian-group presheaf `G.presheaf`. -/
theorem leftKanExtensionObjIsoColimit_naturality {C D H : Type*} [Category C] [Category D]
    [Category H] (L : C ⥤ D) (F : C ⥤ H) [L.HasPointwiseLeftKanExtension F]
    [L.HasLeftKanExtension F] {U V : D} (i : U ⟶ V)
    [HasColimit (CostructuredArrow.map i ⋙ CostructuredArrow.proj L V ⋙ F)] :
    (L.leftKanExtension F).map i ≫ (L.leftKanExtensionObjIsoColimit F V).hom
      = (L.leftKanExtensionObjIsoColimit F U).hom ≫
          colimit.pre (CostructuredArrow.proj L V ⋙ F) (CostructuredArrow.map i) := by
  rw [← Iso.inv_comp_eq]
  refine colimit.hom_ext fun j => ?_
  have h := Functor.ι_leftKanExtensionObjIsoColimit_hom L F V ((CostructuredArrow.map i).obj j)
  simp only [CostructuredArrow.map_obj_left, CostructuredArrow.map_obj_hom] at h
  rw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, ← Functor.map_comp_assoc, h]
  exact (colimit.ι_pre (CostructuredArrow.proj L V ⋙ F) (CostructuredArrow.map i) j).symm

section
-- `Functor.lan` is a plain `def`, so `L.lan.obj F` and `L.leftKanExtension F` are defeq only
-- at default transparency; the rewrites below need it reducible.
attribute [local implicit_reducible] CategoryTheory.Functor.lan

/-- **Morphism analogue of `leftKanExtensionObjIsoColimit_naturality`.** For a natural
transformation `α : F ⟶ F'` of presheaves, the left-Kan-extension functor's action on `α`
is intertwined, via the pointwise-colimit comparison isos, with the levelwise colimit map
`colimMap (whiskerLeft (proj) α)`. -/
theorem lke_morphism_naturality {C D H : Type*} [Category C] [Category D]
    [Category H] (L : C ⥤ D) {F F' : C ⥤ H} (α : F ⟶ F')
    [L.HasPointwiseLeftKanExtension F] [L.HasLeftKanExtension F]
    [L.HasPointwiseLeftKanExtension F'] [L.HasLeftKanExtension F']
    [∀ (G : C ⥤ H), L.HasLeftKanExtension G]
    (U : D)
    [HasColimit (CostructuredArrow.proj L U ⋙ F)]
    [HasColimit (CostructuredArrow.proj L U ⋙ F')] :
    (L.lan.map α).app U ≫ (L.leftKanExtensionObjIsoColimit F' U).hom
      = (L.leftKanExtensionObjIsoColimit F U).hom ≫
          colimMap (Functor.whiskerLeft (CostructuredArrow.proj L U) α) := by
  have unitFac : ∀ (c : C),
      (L.leftKanExtensionUnit F).app c ≫ ((L.lan.map α).app (L.obj c))
        = α.app c ≫ (L.leftKanExtensionUnit F').app c := fun c =>
    (L.leftKanExtension F).descOfIsLeftKanExtension_fac_app
      (L.leftKanExtensionUnit F) (L.leftKanExtension F') (α ≫ L.leftKanExtensionUnit F') c
  apply (L.leftKanExtensionObjIsoColimit F U).inv_comp_eq.mp
  refine colimit.hom_ext fun j => ?_
  have nat : (L.leftKanExtension F).map j.hom ≫ (L.lan.map α).app U
      = (L.lan.map α).app (L.obj j.left) ≫ (L.leftKanExtension F').map j.hom :=
    (L.lan.map α).naturality j.hom
  rw [ι_colimMap, Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, reassoc_of% nat,
    reassoc_of% (unitFac j.left), Functor.ι_leftKanExtensionObjIsoColimit_hom]
  simp

end

/-- The colimit reindexing map `colimit.pre _ (CostructuredArrow.map i)`, conjugated by the
`opOpEquivalence` comparison isomorphisms, sends the germ at `c` to the germ at
`(CostructuredArrow.map i).obj c`. -/
theorem ι_colimitIso_pre_colimitIso_inv {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (P : C ⥤ H) {U V : D} (i : U ⟶ V)
    [HasColimit (CostructuredArrow.proj L V ⋙ P)]
    [HasColimit (CostructuredArrow.map i ⋙ CostructuredArrow.proj L V ⋙ P)]
    (c : ((CostructuredArrow L U)ᵒᵖ)ᵒᵖ) :
    colimit.ι ((opOpEquivalence (CostructuredArrow L U)).functor ⋙
        (CostructuredArrow.map i ⋙ CostructuredArrow.proj L V ⋙ P)) c ≫
      ((Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow L U)).functor
          (CostructuredArrow.map i ⋙ CostructuredArrow.proj L V ⋙ P)).hom ≫
        colimit.pre (CostructuredArrow.proj L V ⋙ P) (CostructuredArrow.map i) ≫
        (Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow L V)).functor
          (CostructuredArrow.proj L V ⋙ P)).inv)
      = colimit.ι ((opOpEquivalence (CostructuredArrow L V)).functor ⋙
          CostructuredArrow.proj L V ⋙ P)
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) := by
  rw [← Category.assoc, Functor.Final.ι_colimitIso_hom, colimit.ι_pre_assoc,
    ← Functor.Final.ι_colimitIso_inv (opOpEquivalence (CostructuredArrow L V)).functor]
  simp

/-- Morphism analogue of `ι_colimitIso_pre_colimitIso_inv`: the levelwise colimit map of
`α : P ⟶ P'`, conjugated by the `opOpEquivalence` comparison isomorphisms, sends the germ
at `c` to the germ at `c` of the section pushed through `α`. -/
theorem ι_colimitIso_colimMap_colimitIso_inv {C D H : Type*} [Category C] [Category D]
    [Category H] (L : C ⥤ D) {P P' : C ⥤ H} (α : P ⟶ P') (U : D)
    [HasColimit (CostructuredArrow.proj L U ⋙ P)]
    [HasColimit (CostructuredArrow.proj L U ⋙ P')]
    (c : ((CostructuredArrow L U)ᵒᵖ)ᵒᵖ) :
    colimit.ι ((opOpEquivalence (CostructuredArrow L U)).functor ⋙
        (CostructuredArrow.proj L U ⋙ P)) c ≫
      ((Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow L U)).functor
          (CostructuredArrow.proj L U ⋙ P)).hom ≫
        colimMap (Functor.whiskerLeft (CostructuredArrow.proj L U) α) ≫
        (Functor.Final.colimitIso (opOpEquivalence (CostructuredArrow L U)).functor
          (CostructuredArrow.proj L U ⋙ P')).inv)
      = α.app (((opOpEquivalence (CostructuredArrow L U)).functor ⋙
            CostructuredArrow.proj L U).obj c) ≫
          colimit.ι ((opOpEquivalence (CostructuredArrow L U)).functor ⋙
            CostructuredArrow.proj L U ⋙ P') c := by
  rw [← Category.assoc, Functor.Final.ι_colimitIso_hom, ι_colimMap_assoc,
    Functor.Final.ι_colimitIso_inv]
  rfl

/-- The germ reindexing `colim_{N(U)} O → colim_{N(V)} O` along `i : U ⟶ V`, i.e.
`colimit.pre` along `CostructuredArrow.map i` read through the `opOpEquivalence` comparison
isomorphisms. -/
@[reducible] noncomputable def pbRingReindex (O : TopCat.Presheaf RingCat.{u} Y)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbRdiag f O U))) :
    ↑(colimit (pbRdiag f O V)) :=
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op V) :=
    finallySmall_of_essentiallySmall _
  (Functor.Final.colimitIso
      (opOpEquivalence (CostructuredArrow (Opens.map f).op V)).functor
      (CostructuredArrow.proj (Opens.map f).op V ⋙ O)).inv
    (colimit.pre (CostructuredArrow.proj (Opens.map f).op V ⋙ O)
      (CostructuredArrow.map i)
      ((Functor.Final.colimitIso
          (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
          (CostructuredArrow.proj (Opens.map f).op U ⋙ O)).hom x))

/-- The germ reindexing `colim_{N(U)} G → colim_{N(V)} G` along `i : U ⟶ V`, the
abelian-group analogue of `pbRingReindex`. -/
@[reducible] noncomputable def pbAbReindex (O : TopCat.Presheaf RingCat.{u} Y)
    (G : PresheafOfModules.{u} O) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : ↑(colimit (pbMmod f O G U).presheaf)) :
    ↑(colimit (pbMmod f O G V).presheaf) :=
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op V) :=
    finallySmall_of_essentiallySmall _
  (Functor.Final.colimitIso
      (opOpEquivalence (CostructuredArrow (Opens.map f).op V)).functor
      (CostructuredArrow.proj (Opens.map f).op V ⋙ G.presheaf)).inv
    (colimit.pre (CostructuredArrow.proj (Opens.map f).op V ⋙ G.presheaf)
      (CostructuredArrow.map i)
      ((Functor.Final.colimitIso
          (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
          (CostructuredArrow.proj (Opens.map f).op U ⋙ G.presheaf)).hom x))

/-- The map `colim_{N(U)} G → colim_{N(U)} G'` induced by a morphism `φ : G ⟶ G'` of
`O`-modules: the levelwise colimit map of `φ̲`, read through the `opOpEquivalence`
comparison isomorphisms. -/
@[reducible] noncomputable def pbAbColimMap (O : TopCat.Presheaf RingCat.{u} Y)
    {G G' : PresheafOfModules.{u} O} (φ : G ⟶ G') (U : (Opens X)ᵒᵖ)
    (x : ↑(colimit (pbMmod f O G U).presheaf)) :
    ↑(colimit (pbMmod f O G' U).presheaf) :=
  haveI : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  (Functor.Final.colimitIso
      (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
      (CostructuredArrow.proj (Opens.map f).op U ⋙ G'.presheaf)).inv
    (colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Opens.map f).op U)
        ((PresheafOfModules.toPresheaf O).map φ))
      ((Functor.Final.colimitIso
          (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
          (CostructuredArrow.proj (Opens.map f).op U ⋙ G.presheaf)).hom x))

/-- The neighbourhood category `N(U)` is finally small, so its colimits can be reindexed. -/
private instance finallySmall_costructuredArrow_opens_map (U : (Opens X)ᵒᵖ) :
    FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
  finallySmall_of_essentiallySmall _

/-- `pbRingReindex` sends the germ of `a` at `c` to the germ of `a` at the reindexed
object `(CostructuredArrow.map i).obj c`. -/
theorem pbRingReindex_ι (O : TopCat.Presheaf RingCat.{u} Y) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ) (a : ↑((pbRdiag f O U).obj c)) :
    pbRingReindex f O i (colimit.ι (pbRdiag f O U) c a)
      = colimit.ι (pbRdiag f O V)
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) a := by
  have := ConcreteCategory.congr_hom (ι_colimitIso_pre_colimitIso_inv (Opens.map f).op O i c) a
  simp only [ConcreteCategory.comp_apply] at this
  exact this

/-- `pbAbReindex` sends the germ of `x` at `c` to the germ of `x` at the reindexed object
`(CostructuredArrow.map i).obj c`. -/
theorem pbAbReindex_ι (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ)
    (x : ↑((pbMmod f O G U).presheaf.obj c)) :
    pbAbReindex f O G i (colimit.ι (pbMmod f O G U).presheaf c x)
      = colimit.ι (pbMmod f O G V).presheaf
          (Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) x := by
  have := congrArg (fun φ => (ConcreteCategory.hom φ) x)
    (ι_colimitIso_pre_colimitIso_inv (Opens.map f).op G.presheaf i c)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at this
  exact this

/-- `pbAbColimMap` keeps the germ index and applies `φ` to the section levelwise. -/
theorem pbAbColimMap_ι (O : TopCat.Presheaf RingCat.{u} Y) {G G' : PresheafOfModules.{u} O}
    (φ : G ⟶ G') (U : (Opens X)ᵒᵖ) (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ)
    (x : ↑((pbMmod f O G U).presheaf.obj c)) :
    pbAbColimMap f O φ U (colimit.ι (pbMmod f O G U).presheaf c x)
      = colimit.ι (pbMmod f O G' U).presheaf c
          (((PresheafOfModules.toPresheaf O).map φ).app ((pbIdx f U).obj c) x) := by
  have := congrArg (fun ψ => (ConcreteCategory.hom ψ) x)
    (ι_colimitIso_colimMap_colimitIso_inv (Opens.map f).op
      ((PresheafOfModules.toPresheaf O).map φ) U c)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at this
  exact this

/-- **Semilinearity of the germ reindexing along a restriction.** The `ModuleColimit` scalar
actions at `U` and at `V` are computed by the same levelwise action, so `pbAbReindex` is
semilinear over `pbRingReindex`. -/
theorem pbReindex_smul (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (a : ↑(colimit (pbRdiag f O U)))
    (s : ↑(colimit (pbMmod f O G U).presheaf)) :
    letI := pbInstCM f O G U
    letI := pbInstCM f O G V
    pbAbReindex f O G i (a • s) = pbRingReindex f O i a • pbAbReindex f O G i s := by
  obtain ⟨c, a₀, s₀, ha, hs⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := colimit.isColimit (pbRdiag f O U))
      (hcM := colimit.isColimit (pbMmod f O G U).presheaf) a s
  rw [← ha, ← hs]
  erw [PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag f O U)) (colimit.isColimit (pbMmod f O G U).presheaf) a₀ s₀]
  erw [pbAbReindex_ι f O G i c (a₀ • s₀), pbRingReindex_ι f O i c a₀, pbAbReindex_ι f O G i c s₀]
  erw [PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag f O V)) (colimit.isColimit (pbMmod f O G V).presheaf)
      (U := Opposite.op (Opposite.op ((CostructuredArrow.map i).obj c.unop.unop))) a₀ s₀]
  rfl

/-- **Linearity of the germ map induced by a morphism of modules.** `pbAbColimMap` is
`colim O`-linear, because `φ` is `O(V)`-linear levelwise. -/
theorem pbAbColimMap_smul (O : TopCat.Presheaf RingCat.{u} Y) {G G' : PresheafOfModules.{u} O}
    (φ : G ⟶ G') (U : (Opens X)ᵒᵖ) (a : ↑(colimit (pbRdiag f O U)))
    (t : ↑(colimit (pbMmod f O G U).presheaf)) :
    letI := pbInstCM f O G U
    letI := pbInstCM f O G' U
    pbAbColimMap f O φ U (a • t) = a • pbAbColimMap f O φ U t := by
  obtain ⟨c, a₀, t₀, ha, ht⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (hcR := colimit.isColimit (pbRdiag f O U))
      (hcM := colimit.isColimit (pbMmod f O G U).presheaf) a t
  rw [← ha, ← ht]
  erw [PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag f O U)) (colimit.isColimit (pbMmod f O G U).presheaf) a₀ t₀]
  erw [pbAbColimMap_ι f O φ U c (a₀ • t₀), pbAbColimMap_ι f O φ U c t₀]
  erw [PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag f O U)) (colimit.isColimit (pbMmod f O G' U).presheaf)
      a₀ (((PresheafOfModules.toPresheaf O).map φ).app ((pbIdx f U).obj c) t₀)]
  congr 1
  exact (φ.app ((pbIdx f U).obj c)).hom.map_smul a₀ t₀

/-- Naturality of a map `M` of Kan-extension sections against the comparison isomorphisms
`c ≪≫ l.symm`, given the corresponding statement `key` for the pointwise colimit isos `l`. -/
private theorem apply_trans_symm_hom_of_comp_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {K K' K₂ K₂' L L' : C} (c : K ≅ K₂) (l : L ≅ K₂) (c' : K' ≅ K₂') (l' : L' ≅ K₂')
    (M : L ⟶ L') (R : K₂ ⟶ K₂') (key : M ≫ l'.hom = l.hom ≫ R) (x : ToType K) :
    M ((c ≪≫ l.symm).hom x) = (c' ≪≫ l'.symm).hom (c'.inv (R (c.hom x))) := by
  have key' : l.inv ≫ M = R ≫ l'.inv := by
    rw [← cancel_mono l'.hom]
    simp [key]
  simpa only [Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    using ConcreteCategory.congr_hom key' (c.hom x)

/-- If `g` corresponds to `k` under the isomorphisms `e`, `e'`, then it does so for their
inverses. -/
private theorem symm_hom_apply_eq_of_apply_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {A A' B B' : C} (e : A ≅ A') (e' : B ≅ B') (g : A' ⟶ B') (k : ToType A → ToType B)
    (h : ∀ x, g (e.hom x) = e'.hom (k x)) (m : ToType A') :
    e'.symm.hom (g m) = k (e.symm.hom m) := by
  have hnat := h (e.symm.hom m)
  rw [show e.hom (e.symm.hom m) = m from e.inv_hom_id_apply m] at hnat
  rw [hnat]
  exact e'.hom_inv_id_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-- Element-level naturality of `pbAbIso` against the restriction map: pushing the germ
of `(pbMmod U).presheaf` at index `j` through `pbAbIso U` and then restricting equals
pushing the same section through `pbAbIso V` at the reindexed germ. -/
theorem pbAbIso_naturality (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbMmod f O G U).presheaf)) :
    (pullbackAb f (underlyingAb O G)).map i ((pbAbIso f O G U).hom x)
      = (pbAbIso f O G V).hom (pbAbReindex f O G i x) :=
  apply_trans_symm_hom_of_comp_eq _ _ _ _ _ _
    (leftKanExtensionObjIsoColimit_naturality (Opens.map f).op G.presheaf i) x

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring analogue of `pbAbIso_naturality`. -/
theorem pbRingIso_naturality (O : TopCat.Presheaf RingCat.{u} Y)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : ↑(colimit (pbRdiag f O U))) :
    (pullbackRing f O).map i ((pbRingIso f O U).hom x)
      = (pbRingIso f O V).hom (pbRingReindex f O i x) :=
  apply_trans_symm_hom_of_comp_eq _ _ _ _ _ _
    (leftKanExtensionObjIsoColimit_naturality (Opens.map f).op O i) x

set_option backward.isDefEq.respectTransparency.types false in
/-- **Morphism-level naturality of `pbAbIso`.** For a morphism `φ : G ⟶ G'` of
`O`-modules, the underlying Ab-presheaf morphism `f_p φ̲` at `U`, conjugated through the
`pbAbIso` comparison isos, equals the levelwise colimit map of `φ̲`. -/
theorem pbAbIso_morphism_naturality (O : TopCat.Presheaf RingCat.{u} Y)
    {G G' : PresheafOfModules.{u} O} (φ : G ⟶ G') (U : (Opens X)ᵒᵖ)
    (x : ↑(colimit (pbMmod f O G U).presheaf)) :
    ((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ)).app U
        ((pbAbIso f O G U).hom x)
      = (pbAbIso f O G' U).hom (pbAbColimMap f O φ U x) :=
  apply_trans_symm_hom_of_comp_eq _ _ _ _ _ _
    (lke_morphism_naturality (Opens.map f).op ((PresheafOfModules.toPresheaf O).map φ) U) x

/-- `pbRingIso` carries the restriction map of `f_p O` to the germ reindexing
`pbRingReindex`; the inverse form of `pbRingIso_naturality`. -/
theorem pbRingIso_symm_naturality (O : TopCat.Presheaf RingCat.{u} Y) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (r : (pullbackRing f O).obj U) :
    (pbRingIso f O V).ringCatIsoToRingEquiv.symm ((pullbackRing f O).map i r)
      = pbRingReindex f O i ((pbRingIso f O U).ringCatIsoToRingEquiv.symm r) :=
  symm_hom_apply_eq_of_apply_eq _ _ _ _ (pbRingIso_naturality f O i) r

/-- `pbAbIso` carries the restriction map of `f_p G` to the germ reindexing `pbAbReindex`;
the inverse form of `pbAbIso_naturality`. -/
theorem pbAbIso_symm_naturality (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : (pullbackAb f (underlyingAb O G)).obj U) :
    (pbAbIso f O G V).symm.hom ((pullbackAb f (underlyingAb O G)).map i m)
      = pbAbReindex f O G i ((pbAbIso f O G U).symm.hom m) :=
  symm_hom_apply_eq_of_apply_eq _ _ _ _ (pbAbIso_naturality f O G i) m

/-- `pbAbIso` carries `f_p φ̲` to `pbAbColimMap`; the inverse form of
`pbAbIso_morphism_naturality`. -/
theorem pbAbIso_symm_morphism_naturality (O : TopCat.Presheaf RingCat.{u} Y)
    {G G' : PresheafOfModules.{u} O} (φ : G ⟶ G') (U : (Opens X)ᵒᵖ)
    (m : (pullbackAb f (underlyingAb O G)).obj U) :
    (pbAbIso f O G' U).symm.hom
        (((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ)).app U m)
      = pbAbColimMap f O φ U ((pbAbIso f O G U).symm.hom m) :=
  symm_hom_apply_eq_of_apply_eq _ _ _ _ (pbAbIso_morphism_naturality f O φ U) m

/-- **Semilinearity of the restriction maps of `f_p G`.**

For `i : U ⟶ V` in `Opens X`, `r : (f_p O)(U)` and `m : (f_p G)(U)`, one has
`(r • m)|_V = r|_V • m|_V` for the `pullbackModule` actions at `U` and at `V`. Together with
`pullbackModule` this is the module-presheaf structure asserted by the tag.

The proof reduces `r` and `m` to a common germ over some `V₀ ∈ N(U)` (joint surjectivity for
`ModuleColimit`), pushes the restriction maps through the comparison isomorphisms — where
`leftKanExtensionObjIsoColimit_naturality` re-indexes the germ from `N(U)` to `N(V)` — and
concludes because the *same* levelwise `O(V₀)`-action computes both sides, by the germ formula
`ModuleColimit.smul_eq` at `U` and at `V`. -/
theorem pullbackModule_map_smul (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    ⦃U V : (Opens X)ᵒᵖ⦄ (i : U ⟶ V) (r : (pullbackRing f O).obj U)
    (m : (pullbackAb f (underlyingAb O G)).obj U) :
    letI : ∀ W, Module ((pullbackRing f O).obj W) ((pullbackAb f (underlyingAb O G)).obj W) :=
      pullbackModule f O G
    (pullbackAb f (underlyingAb O G)).map i (r • m)
      = (pullbackRing f O).map i r • (pullbackAb f (underlyingAb O G)).map i m := by
  rw [pullbackModule_smul_eq f O G U r m,
    pullbackModule_smul_eq f O G V ((pullbackRing f O).map i r)
      ((pullbackAb f (underlyingAb O G)).map i m),
    pbRingIso_symm_naturality f O i r, pbAbIso_symm_naturality f O G i m,
    ← pbReindex_smul f O G i]
  exact pbAbIso_naturality f O G i _

/-- **Linearity of the underlying Ab map of `Φ.map φ` (functoriality semilinearity).**
For a morphism `φ : G ⟶ G'` of `O`-modules, the Ab-presheaf morphism `f_p φ̲` at `U` is
`(f_p O)(U)`-linear with respect to the `pullbackModule` scalar actions on source and
target. This is the linearity obligation needed to package `Φ.map φ` via `homMk`. -/
theorem pullbackModule_morphism_smul (O : TopCat.Presheaf RingCat.{u} Y)
    {G G' : PresheafOfModules.{u} O} (φ : G ⟶ G') (U : (Opens X)ᵒᵖ) (r : (pullbackRing f O).obj U)
    (m : (pullbackAb f (underlyingAb O G)).obj U) :
    letI := pullbackModule f O G U
    letI := pullbackModule f O G' U
    ((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ)).app U (r • m)
      = r • (show (pullbackAb f (underlyingAb O G')).obj U from
          ((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ)).app U
            m) := by
  let := pbInstCM f O G U
  let := pbInstCM f O G' U
  rw [pullbackModule_smul_eq f O G U r m,
    pullbackModule_smul_eq f O G' U r
      (((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ)).app U m),
    pbAbIso_morphism_naturality f O φ U
      ((pbRingIso f O U).ringCatIsoToRingEquiv.symm r • (pbAbIso f O G U).symm.hom m)]
  congr 1
  rw [pbAbColimMap_smul]
  congr 1
  exact (pbAbIso_symm_morphism_naturality f O φ U m).symm


/-- **Stacks 008T (1), (2).**

Let `O` be a presheaf of rings on `Y` and `G` a presheaf of `O`-modules. Then the
pullback presheaf of abelian groups `f_p G` carries the structure of a presheaf of
`f_p O`-modules: there is a presheaf of `f_p O`-modules `M` whose underlying presheaf of
abelian groups is exactly `f_p G`.

The data of `M : PresheafOfModules (f_p O)` packages, for each open `U ⊆ X`, the scalar
multiplication `(f_p O)(U) × (f_p G)(U) → (f_p G)(U)` together with the module axioms and
the compatibility with the restriction maps. That `toPresheaf.obj M` is literally the
pullback presheaf `f_p G` expresses that this module structure lives on `f_p G` itself. -/
@[stacks 008T "(1), (2)"]
theorem pullback_presheaf_module (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O) :
    ∃ M : PresheafOfModules.{u} (pullbackRing f O),
      (PresheafOfModules.toPresheaf (pullbackRing f O)).obj M =
        pullbackAb f (underlyingAb O G) := by
  -- Equip each section `(f_p G)(U)` with the `(f_p O)(U)`-module structure of
  -- `pullbackModule`, assemble via `PresheafOfModules.ofPresheaf`
  -- (semilinearity = `pullbackModule_map_smul`), and read off the equality:
  -- `(ofPresheaf P h).presheaf = P` holds by `rfl`, hence `(toPresheaf _).obj M = P` by `rfl`.
  let : ∀ W, Module ((pullbackRing f O).obj W) ((pullbackAb f (underlyingAb O G)).obj W) :=
    pullbackModule f O G
  refine ⟨PresheafOfModules.ofPresheaf (pullbackAb f (underlyingAb O G))
    (fun U V i r m => pullbackModule_map_smul f O G i r m), ?_⟩
  rfl

/-- **Stacks 008T (3): the functor lifting `f_p` to presheaves of modules.**

The construction of the module structure is functorial in `G`: `f_p` lifts to a functor
`Φ : PresheafOfModules O ⥤ PresheafOfModules (f_p O)` from the category of presheaves of
`O`-modules on `Y` to the category of presheaves of `f_p O`-modules on `X`.  That it lies
over the abelian-group-level functor `f_p` is `pullbackModuleFunctorCompToPresheaf`.

On objects it sends `G` to the presheaf of `f_p O`-modules with carrier `f_p G` and the
scalar action of `pullbackModule`. On a morphism `φ : G ⟶ G'` of `O`-modules with underlying
Ab-presheaf morphism `φ̲`, it takes `(TopCat.Presheaf.pullback Ab f).map φ̲ : f_p G ⟶ f_p G'`,
which is `(f_p O)(U)`-linear for each `U` by `pullbackModule_morphism_smul`: it is `colim` of
the levelwise `O(V)`-linear maps `φ_V`, and the action is built from the levelwise
`O(V)`-actions. Functoriality is inherited from that of `TopCat.Presheaf.pullback Ab f`, since
`PresheafOfModules.homMk` is built on top of it and `toPresheaf` is faithful. -/
@[stacks 008T "(3)"]
noncomputable def pullbackModuleFunctor (O : TopCat.Presheaf RingCat.{u} Y) :
    PresheafOfModules.{u} O ⥤ PresheafOfModules.{u} (pullbackRing f O) where
  obj G :=
    letI : ∀ W, Module ((pullbackRing f O).obj W) ((pullbackAb f (underlyingAb O G)).obj W) :=
      pullbackModule f O G
    PresheafOfModules.ofPresheaf (pullbackAb f (underlyingAb O G))
      (fun U V i r m => pullbackModule_map_smul f O G i r m)
  map {G G'} φ :=
    letI : ∀ W, Module ((pullbackRing f O).obj W) ((pullbackAb f (underlyingAb O G)).obj W) :=
      pullbackModule f O G
    letI : ∀ W, Module ((pullbackRing f O).obj W) ((pullbackAb f (underlyingAb O G')).obj W) :=
      pullbackModule f O G'
    PresheafOfModules.homMk
      ((TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ))
      (fun U r m => pullbackModule_morphism_smul f O φ U r m)
  map_id G := by
    apply (PresheafOfModules.toPresheaf (pullbackRing f O)).map_injective
    change (TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map (𝟙 G))
      = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp {G G' G''} φ ψ := by
    apply (PresheafOfModules.toPresheaf (pullbackRing f O)).map_injective
    change (TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map (φ ≫ ψ))
      = (TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map φ) ≫
        (TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map ψ)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- **Stacks 008T (3): the comparison isomorphism expressing that `pullbackModuleFunctor`
lies over `f_p`:** `Φ ⋙ toPresheaf (f_p O) ≅ toPresheaf O ⋙ (pullback Ab f)`.

Lying over `f_p` means that forgetting the module structure of `Φ.obj G` recovers `f_p`
applied to the abelian-group presheaf underlying `G`, naturally in `G`.  In particular, for
a morphism `φ : G → G'` of presheaves of `O`-modules, `Φ.map φ` is a morphism of presheaves
of `f_p O`-modules whose underlying morphism of presheaves of abelian groups is `f_p φ`.

It is the identity natural isomorphism: `Φ.obj G` is `ofPresheaf (f_p (underlying G)) …`,
whose underlying Ab presheaf is `f_p (underlying G)` on the nose, and `Φ.map φ` is
`homMk (f_p φ̲) …`, whose underlying Ab map is `f_p φ̲` on the nose, so both composites agree
definitionally (compare `pushforward₀CompToPresheaf` and `restrictScalarsCompToPresheaf` in
Mathlib, both also `Iso.refl _`). -/
@[stacks 008T "(3)"]
noncomputable def pullbackModuleFunctorCompToPresheaf (O : TopCat.Presheaf RingCat.{u} Y) :
    pullbackModuleFunctor f O ⋙ PresheafOfModules.toPresheaf (pullbackRing f O) ≅
      PresheafOfModules.toPresheaf O ⋙ TopCat.Presheaf.pullback Ab.{u} f :=
  Iso.refl _


/- The unit (germ) formula for the scalar action.

The action of `pullbackModule` is a *transport* of `ModuleColimit`'s action along
`pbRingIso`/`pbAbIso`, so on its own it says nothing about concrete elements. The lemmas
below turn it into the germ formula that consumers need: the Kan-extension units
`O(V) → (f_p O)(f⁻¹V)` and `G(V) → (f_p G)(f⁻¹V)` are semilinear,

  unit (a • m) = unit a • unit m.

Equivalently: `(f_p O)(f⁻¹V)` and `(f_p G)(f⁻¹V)` are the colimits over `N(f⁻¹V)`, and the
unit is the injection at the object `(f⁻¹V ⊆ f⁻¹V)` of `N(f⁻¹V)`, so the formula is
`ModuleColimit.smul_eq` at that one index, read through the two comparison isomorphisms and
the `opOpEquivalence` reindexing. -/

/-- The Kan-extension unit `F.obj V ⟶ (L.leftKanExtension F).obj (L.obj V)` is the
colimit injection at the object `(L.obj V ⊆ L.obj V)` of `CostructuredArrow L (L.obj V)`,
read through the pointwise-colimit comparison isomorphism. -/
theorem leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit {C D H : Type*}
    [Category C] [Category D] [Category H] (L : C ⥤ D) (F : C ⥤ H)
    [L.HasPointwiseLeftKanExtension F] [L.HasLeftKanExtension F] (V : C)
    [HasColimit (CostructuredArrow.proj L (L.obj V) ⋙ F)] :
    colimit.ι (CostructuredArrow.proj L (L.obj V) ⋙ F)
        (CostructuredArrow.mk (Y := V) (𝟙 (L.obj V))) ≫
        (L.leftKanExtensionObjIsoColimit F (L.obj V)).inv
      = (L.leftKanExtensionUnit F).app V := by
  rw [Functor.ι_leftKanExtensionObjIsoColimit_inv]
  simp

/-- The index of the germ computed by the unit at `V`: the object `(f⁻¹V ⊆ f⁻¹V)` of the
neighbourhood category `N(f⁻¹V) = CostructuredArrow (Opens.map f).op (f⁻¹V)`, written in
the double opposite used by `pbIdx`. -/
@[reducible] noncomputable def pbUnitIdx (V : (Opens Y)ᵒᵖ) :
    ((CostructuredArrow (Opens.map f).op ((Opens.map f).op.obj V))ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op (CostructuredArrow.mk (Y := V) (𝟙 ((Opens.map f).op.obj V))))

/-- The unit `O(V) → (f_p O)(f⁻¹V)` of the pullback presheaf of rings, i.e. the map
sending a section over `V` to its germ over `f⁻¹V`. -/
noncomputable def pullbackRingUnit (O : TopCat.Presheaf RingCat.{u} Y) (V : (Opens Y)ᵒᵖ) :
    O.obj V ⟶ (pullbackRing f O).obj ((Opens.map f).op.obj V) :=
  ((Opens.map f).op.leftKanExtensionUnit O).app V

/-- The unit `G(V) → (f_p G)(f⁻¹V)` of the pullback presheaf of abelian groups. -/
noncomputable def pullbackAbUnit (G : TopCat.Presheaf Ab.{u} Y) (V : (Opens Y)ᵒᵖ) :
    G.obj V ⟶ (pullbackAb f G).obj ((Opens.map f).op.obj V) :=
  ((Opens.map f).op.leftKanExtensionUnit G).app V

/-- `pullbackAbUnit` is the unit of Mathlib's pullback/pushforward adjunction on presheaves
of abelian groups; this is the form in which `TopCat.Presheaf.germ_stalkPullbackHom`
states the compatibility of `stalkPullbackHom` with germs. -/
theorem pullbackAbUnit_eq_adjunction_unit (G : TopCat.Presheaf Ab.{u} Y) (V : (Opens Y)ᵒᵖ) :
    pullbackAbUnit f G V
      = ((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app G).app V := by
  rw [pullbackAbUnit, TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
  rfl

/-- The ring analogue of `pullbackAbUnit_eq_adjunction_unit`. -/
theorem pullbackRingUnit_eq_adjunction_unit (O : TopCat.Presheaf RingCat.{u} Y) (V : (Opens Y)ᵒᵖ) :
    pullbackRingUnit f O V
      = ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app O).app V := by
  rw [pullbackRingUnit, TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
  rfl

/-- The unit `G(V) → (f_p G)(f⁻¹V)` is the germ at the index `pbUnitIdx`, i.e. the
colimit injection there followed by the comparison isomorphism `pbAbIso`. -/
theorem pbAbIso_unit (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (V : (Opens Y)ᵒᵖ) (m : G.obj V) :
    (pbAbIso f O G ((Opens.map f).op.obj V)).hom
        (colimit.ι (pbMmod f O G ((Opens.map f).op.obj V)).presheaf (pbUnitIdx f V) m)
      = pullbackAbUnit f (underlyingAb O G) V m := by
  have hmor :
      colimit.ι ((opOpEquivalence
            (CostructuredArrow (Opens.map f).op ((Opens.map f).op.obj V))).functor ⋙
          (CostructuredArrow.proj (Opens.map f).op ((Opens.map f).op.obj V) ⋙ G.presheaf))
          (pbUnitIdx f V) ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence
              (CostructuredArrow (Opens.map f).op ((Opens.map f).op.obj V))).functor
            (CostructuredArrow.proj (Opens.map f).op ((Opens.map f).op.obj V) ⋙
              G.presheaf)).hom ≫
          ((Opens.map f).op.leftKanExtensionObjIsoColimit G.presheaf
            ((Opens.map f).op.obj V)).inv)
      = ((Opens.map f).op.leftKanExtensionUnit G.presheaf).app V := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit (Opens.map f).op G.presheaf V
  have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) m) hmor
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  rw [pbAbIso, pullbackAbUnit]
  exact h2

/-- The ring analogue of `pbAbIso_unit`. -/
theorem pbRingIso_unit (O : TopCat.Presheaf RingCat.{u} Y)
    (V : (Opens Y)ᵒᵖ) (a : O.obj V) :
    (pbRingIso f O ((Opens.map f).op.obj V)).hom
        (colimit.ι (pbRdiag f O ((Opens.map f).op.obj V)) (pbUnitIdx f V) a)
      = pullbackRingUnit f O V a := by
  have hmor :
      colimit.ι ((opOpEquivalence
            (CostructuredArrow (Opens.map f).op ((Opens.map f).op.obj V))).functor ⋙
          (CostructuredArrow.proj (Opens.map f).op ((Opens.map f).op.obj V) ⋙ O))
          (pbUnitIdx f V) ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence
              (CostructuredArrow (Opens.map f).op ((Opens.map f).op.obj V))).functor
            (CostructuredArrow.proj (Opens.map f).op ((Opens.map f).op.obj V) ⋙ O)).hom ≫
          ((Opens.map f).op.leftKanExtensionObjIsoColimit O
            ((Opens.map f).op.obj V)).inv)
      = ((Opens.map f).op.leftKanExtensionUnit O).app V := by
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    exact leftKanExtensionUnit_eq_ι_leftKanExtensionObjIsoColimit (Opens.map f).op O V
  have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) a) hmor
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  rw [pbRingIso, pullbackRingUnit]
  exact h2

/-- **Semilinearity of the Kan-extension unit (the germ formula for the scalar action).**

For `a : O(V)` and `m : G(V)`, the unit maps into the pullback presheaves over `f⁻¹V`
satisfy `unit (a • m) = unit a • unit m`, where the action on the right is the
`pullbackModule` action of `(f_p O)(f⁻¹V)` on `(f_p G)(f⁻¹V)`.

This is the elementwise content of Stacks 008T that the transported definition of the
action does not expose: `pullbackModule_smul_eq` describes `•` only through the
comparison isomorphisms `pbRingIso`/`pbAbIso`. Here both germs are pushed back to the
single index `pbUnitIdx` (the object `(f⁻¹V ⊆ f⁻¹V)` of `N(f⁻¹V)`), where the action is
`ModuleColimit.smul_eq` and the levelwise module is `G(V)` itself. -/
theorem pullbackModule_unit_smul (O : TopCat.Presheaf RingCat.{u} Y) (G : PresheafOfModules.{u} O)
    (V : (Opens Y)ᵒᵖ) (a : O.obj V) (m : G.obj V) :
    letI := pullbackModule f O G ((Opens.map f).op.obj V)
    pullbackAbUnit f (underlyingAb O G) V (a • m)
      = pullbackRingUnit f O V a • pullbackAbUnit f (underlyingAb O G) V m := by
  let := pbInstCM f O G ((Opens.map f).op.obj V)
  -- Expose the transported action through the comparison isos.
  rw [pullbackModule_smul_eq f O G ((Opens.map f).op.obj V)
    (pullbackRingUnit f O V a) (pullbackAbUnit f (underlyingAb O G) V m)]
  -- Both unit images are germs at `pbUnitIdx`, so the isos undo to colimit injections.
  have hR : (pbRingIso f O ((Opens.map f).op.obj V)).ringCatIsoToRingEquiv.symm
      (pullbackRingUnit f O V a)
      = colimit.ι (pbRdiag f O ((Opens.map f).op.obj V)) (pbUnitIdx f V) a := by
    rw [← pbRingIso_unit f O V a]
    exact (pbRingIso f O ((Opens.map f).op.obj V)).ringCatIsoToRingEquiv.symm_apply_apply _
  have hM : (pbAbIso f O G ((Opens.map f).op.obj V)).symm.hom
      (pullbackAbUnit f (underlyingAb O G) V m)
      = colimit.ι (pbMmod f O G ((Opens.map f).op.obj V)).presheaf (pbUnitIdx f V) m := by
    rw [← pbAbIso_unit f O G V m]
    exact (pbAbIso f O G ((Opens.map f).op.obj V)).hom_inv_id_apply _
  rw [hR, hM]
  -- `ModuleColimit`'s germ formula at the single index `pbUnitIdx`, whose levelwise
  -- module is `G(V)` with its own `O(V)`-action.
  erw [PresheafOfModules.ModuleColimit.smul_eq
      (colimit.isColimit (pbRdiag f O ((Opens.map f).op.obj V)))
      (colimit.isColimit (pbMmod f O G ((Opens.map f).op.obj V)).presheaf)
      (U := pbUnitIdx f V) a m]
  exact (pbAbIso_unit f O G V (a • m)).symm

end Stacks.PresheafOfModules.Pullback
