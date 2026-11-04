module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# Linear structures on sheaves of modules over an algebra, and functors respecting them

Let `R` be a commutative ring and `(C, O)` a site with a sheaf of commutative rings.  A ring
homomorphism `ψ : R →+* Γ(C, O)` makes the category of `O`-modules `R`-linear: `r ∈ R` acts on
`Hom(M, N)` by precomposition with multiplication by `ψ(r)`.  This file sets up that linear
structure and records the two ways a functor between categories of sheaves of modules is seen to
respect it:

* a pushforward of sheaves of modules along a continuous functor and a morphism of sheaves of
  rings carries multiplication by a global section `a` to multiplication by `b` as soon as the
  ring map carries `b` to `a` objectwise (a computation on sections);
* a left adjoint of such a pushforward does the same, by
  `CategoryTheory.Adjunction.map_endOfId`.

## Main definitions

* `Stacks.SheafOfModules.linearOver`: the `R`-linear structure on `O`-modules induced by
  `ψ : R →+* Γ(C, O)`.

## Main results

* `Stacks.SheafOfModules.pushforward_map_globalSmul`: pushforward and multiplication by global
  sections.
* `Stacks.SheafOfModules.map_globalSmul_of_adjunction`: a left adjoint of a functor respecting
  multiplication by global sections respects it too.
* `Stacks.SheafOfModules.linear_of_map_globalSmul`: a functor carrying multiplication by `ψ(r)`
  to multiplication by `ψ'(r)` is `R`-linear for the induced linear structures.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe w v u v' u' r m


namespace Stacks.SheafOfModules

open Stacks.Cohomology.SiteModules

section Linear

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]
  {R : Type*} [CommRing R]

/-- **The `R`-linear structure on `O`-modules induced by a ring homomorphism
`ψ : R →+* Γ(C, O)`**: `r` acts by multiplication by the global section `ψ(r)`. -/
@[instance_reducible]
def linearOver (ψ : R →+* GlobalSectionRing O) : Linear R (_root_.SheafOfModules.{m} O) :=
  Linear.ofRingHom (D := _root_.SheafOfModules.{m} O) ψ

/-- For the linear structure `linearOver O ψ`, `a • 𝟙 M` is multiplication by the global section
`ψ a`. -/
lemma linearOver_smul_id (ψ : R →+* GlobalSectionRing O) (M : _root_.SheafOfModules.{m} O)
    (a : R) :
    letI := linearOver O ψ
    a • 𝟙 M = globalSmul O (ψ a) M := by
  show ψ a • 𝟙 M = _
  rw [globalSmul_eq_smul_id]

end Linear

section Functoriality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  {O : Sheaf J RingCat.{r}} [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]
  {O' : Sheaf K RingCat.{r}} [∀ X : Dᵒᵖ, IsMulCommutative (O'.obj.obj X)]

/-- Multiplication by a global section is the component of the natural endomorphism of the
identity attached to it. -/
lemma globalSmul_eq_globalSectionToEnd_app (a : GlobalSectionRing O)
    (M : _root_.SheafOfModules.{m} O) :
    globalSmul O a M = (globalSectionToEnd O ⟨a.1, a.2⟩).app M := rfl

/-- **A pushforward of sheaves of modules respects multiplication by global sections** related
by the ring map: if `φ` carries `b` to `a` objectwise, the pushforward of multiplication by `a`
is multiplication by `b`. -/
theorem pushforward_map_globalSmul {F : D ⥤ C} [F.IsContinuous K J]
    (φ : O' ⟶ (F.sheafPushforwardContinuous RingCat.{r} K J).obj O)
    (a : GlobalSectionRing O) (b : GlobalSectionRing O')
    (hab : ∀ U : Dᵒᵖ, φ.hom.app U (b.1 U) = a.1 (op (F.obj U.unop)))
    (M : _root_.SheafOfModules.{m} O) :
    (_root_.SheafOfModules.pushforward φ).map (globalSmul O a M) =
      globalSmul O' b ((_root_.SheafOfModules.pushforward φ).obj M) := by
  ext U x
  let y : M.val.obj (op (F.obj U.unop)) := x
  show a.1 (op (F.obj U.unop)) • y =
    (show O.obj.obj (op (F.obj U.unop)) from φ.hom.app U (b.1 U)) • y
  rw [show (show O.obj.obj (op (F.obj U.unop)) from φ.hom.app U (b.1 U)) =
    a.1 (op (F.obj U.unop)) from hab U]

/-- **A left adjoint of a functor respecting multiplication by global sections respects it
too.** -/
theorem map_globalSmul_of_adjunction
    {L : _root_.SheafOfModules.{m} O' ⥤ _root_.SheafOfModules.{m} O}
    {G : _root_.SheafOfModules.{m} O ⥤ _root_.SheafOfModules.{m} O'} (adj : L ⊣ G)
    (a : GlobalSectionRing O) (b : GlobalSectionRing O')
    (h : ∀ M, G.map (globalSmul O a M) = globalSmul O' b (G.obj M))
    (N : _root_.SheafOfModules.{m} O') :
    L.map (globalSmul O' b N) = globalSmul O a (L.obj N) :=
  adj.map_endOfId (a := globalSectionToEnd O' ⟨b.1, b.2⟩) (b := globalSectionToEnd O ⟨a.1, a.2⟩)
    h N

variable {R : Type*} [CommRing R]

/-- **A functor carrying multiplication by `ψ(r)` to multiplication by `ψ'(r)` is `R`-linear**
for the linear structures induced by `ψ` and `ψ'`. -/
theorem linear_of_map_globalSmul (ψ : R →+* GlobalSectionRing O)
    (ψ' : R →+* GlobalSectionRing O')
    (F : _root_.SheafOfModules.{m} O ⥤ _root_.SheafOfModules.{m} O')
    (h : ∀ (a : R) (M : _root_.SheafOfModules.{m} O),
      F.map (globalSmul O (ψ a) M) = globalSmul O' (ψ' a) (F.obj M)) :
    letI := linearOver O ψ
    letI := linearOver O' ψ'
    F.Linear R := by
  let _ : Linear R (_root_.SheafOfModules.{m} O) := linearOver O ψ
  let _ : Linear R (_root_.SheafOfModules.{m} O') := linearOver O' ψ'
  rw [Functor.linear_iff]
  intro M a
  rw [linearOver_smul_id, linearOver_smul_id, h]

end Functoriality

section RingMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O O' : Sheaf J RingCat.{r}}

/-- **The ring homomorphism on global sections induced by a morphism of sheaves of rings.** -/
def globalSectionRingMap (φ : O ⟶ O') : GlobalSectionRing O →+* GlobalSectionRing O' where
  toFun a := ⟨fun X => φ.hom.app X (a.1 X), fun {X Y} g => by
    change (φ.hom.app X ≫ O'.obj.map g) (a.1 X) = _
    rw [← φ.hom.naturality]
    exact congrArg (φ.hom.app Y) (a.2 g)⟩
  map_one' := Subtype.ext (funext fun X => (φ.hom.app X).hom.map_one)
  map_mul' a b := Subtype.ext (funext fun X => (φ.hom.app X).hom.map_mul _ _)
  map_zero' := Subtype.ext (funext fun X => (φ.hom.app X).hom.map_zero)
  map_add' a b := Subtype.ext (funext fun X => (φ.hom.app X).hom.map_add _ _)

/-- The section of `globalSectionRingMap φ a` over `X` is the image under `φ` of the section of
`a` over `X`. -/
lemma globalSectionRingMap_apply (φ : O ⟶ O') (a : GlobalSectionRing O) (X : Cᵒᵖ) :
    (globalSectionRingMap φ a).1 X = φ.hom.app X (a.1 X) := rfl

variable [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)] [∀ X : Cᵒᵖ, IsMulCommutative (O'.obj.obj X)]

/-- **Restriction of scalars along `φ : O ⟶ O'` carries multiplication by `φ(a)` to multiplication
by `a`.** -/
theorem restrictScalars_map_globalSmul (φ : O ⟶ O') (a : GlobalSectionRing O)
    (M : _root_.SheafOfModules.{m} O') :
    (_root_.SheafOfModules.restrictScalars φ).map (globalSmul O' (globalSectionRingMap φ a) M) =
      globalSmul O a ((_root_.SheafOfModules.restrictScalars φ).obj M) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  rfl

end RingMap

section RightAdjoint

/-- **A right adjoint of a functor respecting multiplication by global sections respects it
too.** -/
theorem map_globalSmul_of_adjunction_right {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (a : End (𝟭 D)) (b : End (𝟭 C))
    (h : ∀ N : C, L.map (b.app N) = a.app (L.obj N)) (M : D) :
    G.map (a.app M) = b.app (G.obj M) := by
  have h₁ := adj.right_triangle_components M
  have h₂ := a.naturality (adj.counit.app M)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at h₂
  calc G.map (a.app M)
      = adj.unit.app (G.obj M) ≫ G.map (adj.counit.app M) ≫ G.map (a.app M) := by
        rw [reassoc_of% h₁]
    _ = adj.unit.app (G.obj M) ≫ G.map (L.map (b.app (G.obj M))) ≫
          G.map (adj.counit.app M) := by
        rw [← G.map_comp, ← G.map_comp, h, ← h₂]
    _ = b.app (G.obj M) := by
        rw [← Category.assoc, ← Functor.comp_map, ← adj.unit.naturality, Functor.id_map,
          Category.assoc]
        exact (congrArg (b.app (G.obj M) ≫ ·) h₁).trans (Category.comp_id _)

end RightAdjoint

end Stacks.SheafOfModules

end
