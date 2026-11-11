module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites

/-!
# Sections of a composite of two direct images of modules

Let `q : 𝒳 ⥤ (Sch/S)` and `r : 𝒴 ⥤ (Sch/S)` be categories fibred in groupoids, `F : 𝒳 ⥤ 𝒴` a
`1`-morphism and `c : 𝒯 ⥤ 𝒳` a continuous and cocontinuous functor of sites. For a sheaf of
modules `N` on `𝒯` the sections over `y` of `F_* c_* N` are compatible families of compatible
families of sections of `N`: an element `s` has a component `s(a, φ) ∈ N(a)` for every object `a`
of `𝒯` and every morphism `φ : F(c(a)) ⟶ y`. This file names that component
(`AlgebraicGeometry.Stack.compositeSectionsEval`), records how it behaves under morphisms of `N`
and under morphisms of `𝒯`, and proves the sections formula: if `t = (a₀, φ₀)` is terminal in
`CostructuredArrow (c ⋙ F) y`, then evaluation at `t` is an isomorphism
`Γ(y, F_* c_* N) ≅ N(a₀)`, naturally in `N`.

## Main definitions

* `AlgebraicGeometry.Stack.compositeSectionsEval`: the component at `(a, φ)`.
* `AlgebraicGeometry.Stack.compositeSectionsIsoOfIsTerminal`: the sections formula at a terminal
  arrow, as an isomorphism of abelian groups natural in `N`.

## Main results

* `AlgebraicGeometry.Stack.compositeSectionsEval_comp`: the components are compatible with the
  morphisms of `𝒯`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  {𝒯 : Type (u + 1)} [Category.{u} 𝒯]
  (q : 𝒳 ⥤ BigFppfOver B S hS) (r : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ r = q)
  (c : 𝒯 ⥤ 𝒳) (J : GrothendieckTopology 𝒯)
  [c.IsContinuous J (associatedTopology B S hS q (B.baseTopology .fppf))]
  [c.IsCocontinuous J (associatedTopology B S hS q (B.baseTopology .fppf))]

/-- The ring sheaf on `𝒯` over which the modules `N` of this file live: the inverse image along
`c` of the structure sheaf of `𝒳`. -/
abbrev compositeRing :
    Sheaf J RingCat.{u} :=
  (c.sheafPushforwardContinuous RingCat.{u} J
    (associatedTopology B S hS q (B.baseTopology .fppf))).obj
    (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf))

/-- The composite `F_* ∘ c_*` of the direct image along `c` and the direct image of
**Stacks 06WE** along `F`, at module universe `u + 1`. -/
abbrev compositeDirectImage :
    SheafOfModules.{u + 1} (compositeRing B S hS q hq c J) ⥤
      SheafOfModules.{u + 1}
        (ringStructureSheafCore B S hS r hr (B.baseTopology .fppf)
          (B.baseTopology_le_topology .fppf)) :=
  SheafOfModules.directImage.{u, u + 1} c J
      (associatedTopology B S hS q (B.baseTopology .fppf))
      (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
        (B.baseTopology_le_topology .fppf)) ⋙
    moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr F hF
      (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)

/-- The direct image `c_*` of this file. -/
abbrev compositeInnerDirectImage :
    SheafOfModules.{u + 1} (compositeRing B S hS q hq c J) ⥤
      SheafOfModules.{u + 1}
        (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
          (B.baseTopology_le_topology .fppf)) :=
  SheafOfModules.directImage.{u, u + 1} c J
    (associatedTopology B S hS q (B.baseTopology .fppf))
    (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
      (B.baseTopology_le_topology .fppf))

/-- The sections over `x` of `c_* N`, as compatible families indexed by
`StructuredArrow x c.op`. -/
abbrev InnerSections (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) (x : 𝒳ᵒᵖ) :
    Type (u + 1) :=
  PresheafOfModules.directImageSections.{u, u, u, u, u + 1, u + 1} c
    (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
      (B.baseTopology_le_topology .fppf)).obj N.val x

variable {B S hS q r hq hr F hF c J}

/-- A section of `c_* N` over `x`, read as a compatible family. -/
def toInner {N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)} {x : 𝒳ᵒᵖ}
    (t : ((compositeInnerDirectImage B S hS q hq c J).obj N).val.presheaf.obj x) :
    InnerSections B S hS q hq c J N x :=
  t

/-- A compatible family, read as a section of `c_* N` over `x`. -/
def ofInner {N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)} {x : 𝒳ᵒᵖ}
    (t : InnerSections B S hS q hq c J N x) :
    ((compositeInnerDirectImage B S hS q hq c J).obj N).val.presheaf.obj x :=
  t

/-- Reading a section as a compatible family is injective. -/
theorem toInner_injective {N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)}
    {x : 𝒳ᵒᵖ} : Function.Injective (toInner (N := N) (x := x)) :=
  fun _ _ h => h

/-- The underlying abelian presheaf of `c_* N`. -/
abbrev innerPresheaf (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) :
    𝒳ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((compositeInnerDirectImage B S hS q hq c J).obj N).val.presheaf

/-- The counit of `c_*`: the value of a compatible family at the identity index. -/
def innerCounit (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) :
    c.op ⋙ innerPresheaf N ⟶ N.val.presheaf :=
  PresheafOfModules.directImageCounit.{u, u} c
    (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
      (B.baseTopology_le_topology .fppf)).obj N.val

/-- The counit of `c_*` at the index `k` of a family restricted along `k` is its value at `k`. -/
theorem innerCounit_apply (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    (x : 𝒳ᵒᵖ) (k : StructuredArrow x c.op) (s : (innerPresheaf N).obj x) :
    ConcreteCategory.hom ((innerCounit N).app k.right)
        (ConcreteCategory.hom ((innerPresheaf N).map k.hom) s) =
      (toInner s).val k :=
  PresheafOfModules.directImageCounit_apply.{u, u} c _ N.val x k s

variable (B S hS q r hq hr F hF c J)

/-- The sections over `y` of the direct image along `F` of a module `X` are the value at `y` of
the right Kan extension along `F.op` of its underlying abelian presheaf. -/
def outerSectionsIso (X : SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
        (B.baseTopology_le_topology .fppf))) (y : 𝒴) :
    ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr F hF
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj X).val.presheaf.obj
        (op y) ≅
      (F.op.ran.obj X.val.presheaf).obj (op y) :=
  ((moduleFunctoriality.{u, u + 1, u, u} B S hS q r hq hr F hF).pushforward_iso.app
    X.val).app (op y)

/-- **The component of a section of `F_* c_* N` over `y` at `(a, φ : F(c(a)) ⟶ y)`**: the leg at
`(c(a), φ)` of the right Kan extension, followed by the evaluation of the compatible family of
`c_* N` at the identity index. -/
def compositeSectionsEvalHom (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y) :
    ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y) ⟶
      N.val.presheaf.obj (op a) :=
  (outerSectionsIso B S hS q r hq hr F hF ((compositeInnerDirectImage B S hS q hq c J).obj N)
      y).hom ≫
    Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y)
      (StructuredArrow.mk (Y := op (c.obj a)) φ.op) ≫ (innerCounit N).app (op a)

/-- The component of a section at `(a, φ)`, as a function. -/
abbrev compositeSectionsEval (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y)
    (s : ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y)) :
    N.val.presheaf.obj (op a) :=
  ConcreteCategory.hom (compositeSectionsEvalHom B S hS q r hq hr F hF c J N a φ) s

variable {B S hS q r hq hr F hF c J}

/-- `compositeSectionsEvalHom`, unfolded. -/
theorem compositeSectionsEvalHom_eq (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y) :
    compositeSectionsEvalHom B S hS q r hq hr F hF c J N a φ =
      (outerSectionsIso B S hS q r hq hr F hF ((compositeInnerDirectImage B S hS q hq c J).obj N)
          y).hom ≫
        Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y)
          (StructuredArrow.mk (Y := op (c.obj a)) φ.op) ≫ (innerCounit N).app (op a) :=
  rfl

/-- The morphism of underlying abelian presheaves of a morphism of presheaves of modules, with
source and target written as the underlying presheaves `M.presheaf` and `M'.presheaf`. -/
def underlyingPresheafHom {𝒞 : Type*} [Category* 𝒞] {R : 𝒞ᵒᵖ ⥤ RingCat.{u}}
    {M M' : PresheafOfModules.{u + 1} R} (f : M ⟶ M') : M.presheaf ⟶ M'.presheaf :=
  (PresheafOfModules.toPresheaf R).map f

/-- The comparison `outerSectionsIso` is natural in `y`. -/
@[reassoc]
theorem outerSectionsIso_naturality (X : SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
        (B.baseTopology_le_topology .fppf))) {y y' : 𝒴} (g : y' ⟶ y) :
    ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr F hF
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj X).val.presheaf.map g.op ≫
        (outerSectionsIso B S hS q r hq hr F hF X y').hom =
      (outerSectionsIso B S hS q r hq hr F hF X y).hom ≫ (F.op.ran.obj X.val.presheaf).map g.op :=
  ((moduleFunctoriality.{u, u + 1, u, u} B S hS q r hq hr F hF).pushforward_iso.hom.app
    X.val).naturality g.op

/-- The comparison `outerSectionsIso` is natural in the module. -/
@[reassoc]
theorem outerSectionsIso_naturality_left {X X' : SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS q hq (B.baseTopology .fppf)
        (B.baseTopology_le_topology .fppf))} (ψ : X ⟶ X') (y : 𝒴) :
    (underlyingPresheafHom ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S
        hS q r hq hr F hF (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).map
          ψ).val).app (op y) ≫ (outerSectionsIso B S hS q r hq hr F hF X' y).hom =
      (outerSectionsIso B S hS q r hq hr F hF X y).hom ≫
        (F.op.ran.map (underlyingPresheafHom ψ.val)).app (op y) :=
  NatTrans.congr_app
    ((moduleFunctoriality.{u, u + 1, u, u} B S hS q r hq hr F hF).pushforward_iso.hom.naturality
      ψ.val) (op y)

/-- The counit of `c_*` is natural in the module. -/
theorem innerCounit_naturality {N N' : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)}
    (ψ : N ⟶ N') (a : 𝒯) :
    (underlyingPresheafHom ((compositeInnerDirectImage B S hS q hq c J).map ψ).val).app
        (op (c.obj a)) ≫ (innerCounit N').app (op a) =
      (innerCounit N).app (op a) ≫ (underlyingPresheafHom ψ.val).app (op a) := by
  ext s
  rfl

/-- **The components of a section are natural in the module.** -/
theorem compositeSectionsEvalHom_naturality_left
    {N N' : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)} (ψ : N ⟶ N')
    {y : 𝒴} (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y) :
    (underlyingPresheafHom ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr
        F hF (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).map
          ((compositeInnerDirectImage B S hS q hq c J).map ψ)).val).app (op y) ≫
        compositeSectionsEvalHom B S hS q r hq hr F hF c J N' a φ =
      compositeSectionsEvalHom B S hS q r hq hr F hF c J N a φ ≫
        (underlyingPresheafHom ψ.val).app (op a) := by
  rw [compositeSectionsEvalHom_eq, compositeSectionsEvalHom_eq,
    outerSectionsIso_naturality_left_assoc, Stacks.SheafOfModules.ranπ_map_functor_assoc,
    Category.assoc, Category.assoc]
  exact congrArg (fun z => _ ≫ _ ≫ z) (innerCounit_naturality ψ a)

/-- **The components of a section, restricted along `g : y' ⟶ y`.** -/
theorem compositeSectionsEvalHom_map
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y y' : 𝒴} (g : y' ⟶ y) (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y') :
    ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr F hF
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj
          ((compositeInnerDirectImage B S hS q hq c J).obj N)).val.presheaf.map g.op ≫
        compositeSectionsEvalHom B S hS q r hq hr F hF c J N a φ =
      compositeSectionsEvalHom B S hS q r hq hr F hF c J N a (φ ≫ g) := by
  rw [compositeSectionsEvalHom_eq, compositeSectionsEvalHom_eq,
    outerSectionsIso_naturality_assoc, Stacks.SheafOfModules.ranπ_map_assoc]
  rfl

/-- The component of a restricted section is the component at the composite. -/
theorem compositeSectionsEval_map (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y y' : 𝒴} (g : y' ⟶ y) (a : 𝒯) (φ : F.obj (c.obj a) ⟶ y')
    (s : ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y)) :
    compositeSectionsEval B S hS q r hq hr F hF c J N a φ
        (ConcreteCategory.hom (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS q r hq hr
          F hF (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)).obj
            ((compositeInnerDirectImage B S hS q hq c J).obj N)).val.presheaf.map g.op) s) =
      compositeSectionsEval B S hS q r hq hr F hF c J N a (φ ≫ g) s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (compositeSectionsEvalHom_map N g a φ) s)

/-- **The components of a section are compatible with the morphisms of `𝒯`.** -/
theorem compositeSectionsEvalHom_comp
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {a a' : 𝒯} (k : a ⟶ a') (φ' : F.obj (c.obj a') ⟶ y) :
    compositeSectionsEvalHom B S hS q r hq hr F hF c J N a' φ' ≫ N.val.presheaf.map k.op =
      compositeSectionsEvalHom B S hS q r hq hr F hF c J N a (F.map (c.map k) ≫ φ') := by
  have hnat := Stacks.SheafOfModules.ranπ_naturality_assoc F.op (innerPresheaf N) (b := op y)
    (j₁ := StructuredArrow.mk (Y := op (c.obj a')) φ'.op)
    (j₂ := StructuredArrow.mk (Y := op (c.obj a)) (F.map (c.map k) ≫ φ').op)
    (StructuredArrow.homMk (c.map k).op (by simp)) ((innerCounit N).app (op a))
  have hc : (innerPresheaf N).map (c.map k).op ≫ (innerCounit N).app (op a) =
      (innerCounit N).app (op a') ≫ N.val.presheaf.map k.op :=
    (innerCounit N).naturality k.op
  rw [compositeSectionsEvalHom_eq, compositeSectionsEvalHom_eq, Category.assoc, Category.assoc,
    ← hc, ← hnat]
  rfl

/-- **The components of a section are compatible with the morphisms of `𝒯`.** -/
theorem compositeSectionsEval_comp (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {a a' : 𝒯} (k : a ⟶ a') (φ' : F.obj (c.obj a') ⟶ y)
    (s : ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y)) :
    ConcreteCategory.hom (N.val.presheaf.map k.op)
        (compositeSectionsEval B S hS q r hq hr F hF c J N a' φ' s) =
      compositeSectionsEval B S hS q r hq hr F hF c J N a (F.map (c.map k) ≫ φ') s :=
  (ConcreteCategory.comp_apply (compositeSectionsEvalHom B S hS q r hq hr F hF c J N a' φ')
    (N.val.presheaf.map k.op) s).symm.trans
      (ConcreteCategory.congr_hom (compositeSectionsEvalHom_comp N k φ') s)

/-- The value of the inner family of a section at an index is a component of the section. -/
theorem toInner_ranπ_val (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} (j : StructuredArrow (op y) F.op) (k : StructuredArrow j.right c.op)
    (v : (F.op.ran.obj (innerPresheaf N)).obj (op y)) :
    (toInner (ConcreteCategory.hom
        (Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y) j) v)).val k =
      ConcreteCategory.hom (Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y)
          (StructuredArrow.mk (Y := op (c.obj k.right.unop))
            (F.map k.hom.unop ≫ j.hom.unop).op) ≫ (innerCounit N).app k.right) v := by
  have hnat := Stacks.SheafOfModules.ranπ_naturality_assoc F.op (innerPresheaf N) (b := op y)
    (j₁ := j) (j₂ := StructuredArrow.mk (Y := op (c.obj k.right.unop))
      (F.map k.hom.unop ≫ j.hom.unop).op)
    (StructuredArrow.homMk k.hom (by simp)) ((innerCounit N).app k.right)
  exact (innerCounit_apply N j.right k _).symm.trans (ConcreteCategory.congr_hom hnat v)

/-- The morphism of `𝒯` from the source of the index `k` (over the index `j`) to the source of
a terminal arrow `t`. -/
def terminalIndex {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) (k : StructuredArrow j.right c.op) :
    k.right.unop ⟶ t.left :=
  (ht.from (CostructuredArrow.mk (Y := k.right.unop) (F.map k.hom.unop ≫ j.hom.unop))).left

/-- `terminalIndex` lies over the structure morphisms. -/
theorem terminalIndex_w {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) (k : StructuredArrow j.right c.op) :
    F.map (c.map (terminalIndex ht j k)) ≫ t.hom = F.map k.hom.unop ≫ j.hom.unop :=
  CostructuredArrow.w (ht.from _)

/-- `terminalIndex` is compatible with the morphisms of indices. -/
theorem terminalIndex_op_comp {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) {k k' : StructuredArrow j.right c.op} (β : k ⟶ k') :
    (terminalIndex ht j k).op ≫ β.right = (terminalIndex ht j k').op := by
  have hw : c.map β.right.unop ≫ k.hom.unop = k'.hom.unop :=
    congrArg Quiver.Hom.unop (StructuredArrow.w β)
  have h := congrArg CommaMorphism.left (ht.hom_ext
    (CostructuredArrow.homMk (S := c ⋙ F) (f := CostructuredArrow.mk (Y := k'.right.unop)
        (F.map k'.hom.unop ≫ j.hom.unop))
      (f' := CostructuredArrow.mk (Y := k.right.unop) (F.map k.hom.unop ≫ j.hom.unop))
      β.right.unop (by
        change F.map (c.map β.right.unop) ≫ F.map k.hom.unop ≫ j.hom.unop =
          F.map k'.hom.unop ≫ j.hom.unop
        rw [← hw, F.map_comp, Category.assoc]) ≫ ht.from _) (ht.from _))
  exact congrArg Quiver.Hom.op h

/-- `terminalIndex` at the identity index over the terminal arrow is the identity. -/
theorem terminalIndex_mk_id {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    terminalIndex ht (StructuredArrow.mk (Y := op (c.obj t.left)) t.hom.op)
      (StructuredArrow.mk (𝟙 (c.op.obj (op t.left)))) = 𝟙 t.left := by
  have h := congrArg CommaMorphism.left (ht.hom_ext
    (CostructuredArrow.homMk (S := c ⋙ F) (f := t)
      (f' := CostructuredArrow.mk (Y := t.left) (F.map (𝟙 (c.obj t.left)) ≫ t.hom))
      (𝟙 t.left) (by simp) ≫ ht.from _) (𝟙 t))
  exact (Category.id_comp _).symm.trans h

/-- The compatible family of sections of `c_* N` over the index `j` attached to a section `m` of
`N` over the source of a terminal arrow `t`: its component at `(a, ψ : c(a) ⟶ x)` is the
restriction of `m` along `terminalIndex`. -/
def terminalLegFun (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) :
    N.val.presheaf.obj (op t.left) →+ InnerSections B S hS q hq c J N j.right where
  toFun m := ⟨fun k => ConcreteCategory.hom (N.val.presheaf.map (terminalIndex ht j k).op) m,
    fun k k' β => by
      refine (ConcreteCategory.comp_apply (N.val.presheaf.map (terminalIndex ht j k).op)
        (N.val.presheaf.map β.right) m).symm.trans ?_
      rw [← Functor.map_comp, terminalIndex_op_comp]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' m m' := Subtype.ext (funext fun _ => map_add _ m m')

/-- `terminalLegFun`, as a morphism of abelian groups. -/
def terminalLeg (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) :
    N.val.presheaf.obj (op t.left) ⟶ (innerPresheaf N).obj j.right :=
  AddCommGrpCat.ofHom (terminalLegFun N ht j)

/-- The components of `terminalLeg`. -/
theorem toInner_terminalLeg_val (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) (m : N.val.presheaf.obj (op t.left))
    (k : StructuredArrow j.right c.op) :
    (toInner (ConcreteCategory.hom (terminalLeg N ht j) m)).val k =
      ConcreteCategory.hom (N.val.presheaf.map (terminalIndex ht j k).op) m :=
  rfl

/-- `terminalIndex` does not depend on how the index is written. -/
theorem terminalIndex_map {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    {j j' : StructuredArrow (op y) F.op} (β : j ⟶ j') (k : StructuredArrow j'.right c.op) :
    terminalIndex ht j' k =
      terminalIndex ht j (StructuredArrow.mk (Y := k.right) (β.right ≫ k.hom)) := by
  have hw : j'.hom.unop = F.map β.right.unop ≫ j.hom.unop :=
    (congrArg Quiver.Hom.unop (StructuredArrow.w β)).symm
  have he : F.map k.hom.unop ≫ j'.hom.unop = F.map (β.right ≫ k.hom).unop ≫ j.hom.unop := by
    rw [hw, unop_comp, F.map_comp, Category.assoc]
  exact @congrArg _ (k.right.unop ⟶ t.left) _ _
    (fun φ => (ht.from (CostructuredArrow.mk (Y := k.right.unop) φ)).left) he

/-- The legs `terminalLeg` form a cone over the diagram computing the right Kan extension. -/
abbrev terminalCone (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    Limits.Cone (StructuredArrow.proj (op y) F.op ⋙ innerPresheaf N) where
  pt := N.val.presheaf.obj (op t.left)
  π :=
    { app := fun j => terminalLeg N ht j
      naturality := fun j j' β => by
        ext m
        refine toInner_injective (N := N) (x := j'.right) (Subtype.ext (funext fun k => ?_))
        change ConcreteCategory.hom (N.val.presheaf.map (terminalIndex ht j' k).op) m =
          ConcreteCategory.hom (N.val.presheaf.map (terminalIndex ht j
            (StructuredArrow.mk (Y := k.right) (β.right ≫ k.hom))).op) m
        rw [terminalIndex_map ht β k] }

/-- The section of `F_* c_* N` over `y` attached to a section `m` of `N` over the source of a
terminal arrow `t` of `CostructuredArrow (c ⋙ F) y`. -/
def compositeSectionsOfIsTerminalHom (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    N.val.presheaf.obj (op t.left) ⟶
      ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y) :=
  (Stacks.SheafOfModules.ranIsLimit F.op (innerPresheaf N) (op y)).lift (terminalCone N ht) ≫
    (outerSectionsIso B S hS q r hq hr F hF _ y).inv

/-- The leg of the attached section at an index is `terminalLeg`. -/
@[reassoc]
theorem ranπ_compositeSectionsOfIsTerminalHom
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J))
    {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    (j : StructuredArrow (op y) F.op) :
    compositeSectionsOfIsTerminalHom (r := r) (hr := hr) (hF := hF) N ht ≫
        (outerSectionsIso B S hS q r hq hr F hF
          ((compositeInnerDirectImage B S hS q hq c J).obj N) y).hom ≫
        Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y) j =
      terminalLeg N ht j :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans
    ((Stacks.SheafOfModules.ranIsLimit F.op (innerPresheaf N) (op y)).fac (terminalCone N ht) j))

/-- The value at an index of the family attached to the component at a terminal arrow of a
section is the value of the inner family of the section. -/
theorem toInner_terminalLeg_compositeSectionsEvalHom
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) {y : 𝒴}
    {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) (j : StructuredArrow (op y) F.op)
    (k : StructuredArrow j.right c.op)
    (s : ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y)) :
    (toInner (ConcreteCategory.hom (terminalLeg N ht j)
        (ConcreteCategory.hom (compositeSectionsEvalHom B S hS q r hq hr F hF c J N t.left t.hom)
          s))).val k =
      (toInner (ConcreteCategory.hom (Stacks.SheafOfModules.ranπ F.op (innerPresheaf N) (op y) j)
        (ConcreteCategory.hom (outerSectionsIso B S hS q r hq hr F hF
          ((compositeInnerDirectImage B S hS q hq c J).obj N) y).hom s))).val k := by
  refine (toInner_terminalLeg_val N ht j _ k).trans ?_
  refine (compositeSectionsEval_comp (B := B) (S := S) (hS := hS) (q := q) (r := r) (hq := hq)
    (hr := hr) (F := F) (hF := hF) (c := c) (J := J) N (terminalIndex ht j k) t.hom s).trans ?_
  refine (congrArg (fun φ => compositeSectionsEval B S hS q r hq hr F hF c J N
    k.right.unop φ s) (terminalIndex_w ht j k)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ s).trans ?_
  exact (toInner_ranπ_val N j k _).symm

/-- The component at a terminal arrow, followed by the attached section, is the identity. -/
theorem compositeSectionsEvalHom_comp_compositeSectionsOfIsTerminalHom
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) {y : 𝒴}
    {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    compositeSectionsEvalHom B S hS q r hq hr F hF c J N t.left t.hom ≫
        compositeSectionsOfIsTerminalHom N ht = 𝟙 _ := by
  rw [← cancel_mono (outerSectionsIso B S hS q r hq hr F hF
    ((compositeInnerDirectImage B S hS q hq c J).obj N) y).hom, Category.id_comp,
    Category.assoc]
  refine Stacks.SheafOfModules.ran_hom_ext F.op (innerPresheaf N) fun j => ?_
  rw [Category.assoc, Category.assoc, ranπ_compositeSectionsOfIsTerminalHom]
  ext s
  refine (ConcreteCategory.comp_apply _ _ s).trans
    (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ s).symm)
  exact toInner_injective (N := N) (x := j.right) (Subtype.ext (funext fun k =>
    toInner_terminalLeg_compositeSectionsEvalHom (B := B) (S := S) (hS := hS) (q := q) (r := r)
      (hq := hq) (hr := hr) (F := F) (hF := hF) (c := c) (J := J) N ht j k s))

/-- The attached section, followed by the component at a terminal arrow, is the identity. -/
theorem compositeSectionsOfIsTerminalHom_comp_compositeSectionsEvalHom
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) {y : 𝒴}
    {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    compositeSectionsOfIsTerminalHom (r := r) (hr := hr) (hF := hF) N ht ≫
        compositeSectionsEvalHom B S hS q r hq hr F hF c J N t.left t.hom = 𝟙 _ := by
  rw [compositeSectionsEvalHom_eq, ranπ_compositeSectionsOfIsTerminalHom_assoc]
  ext m
  change ConcreteCategory.hom (N.val.presheaf.map (terminalIndex ht
    (StructuredArrow.mk (Y := op (c.obj t.left)) t.hom.op)
    (StructuredArrow.mk (𝟙 (c.op.obj (op t.left))))).op) m = m
  rw [terminalIndex_mk_id]
  exact (congrArg (fun (f : N.val.presheaf.obj (op t.left) ⟶ N.val.presheaf.obj (op t.left)) =>
    ConcreteCategory.hom f m) (N.val.presheaf.map_id (op t.left))).trans
      (ConcreteCategory.id_apply m)

/-- **The sections formula of `F_* c_*` at a terminal arrow, at one module.** If
`t = (a₀, φ₀)` is terminal in `CostructuredArrow (c ⋙ F) y`, evaluation at `t` identifies the
sections over `y` of `F_* c_* N` with the sections of `N` over `a₀`. -/
def compositeSectionsIsoOfIsTerminalApp
    (N : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)) {y : 𝒴}
    {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t) :
    ((compositeDirectImage B S hS q r hq hr F hF c J).obj N).val.presheaf.obj (op y) ≅
      N.val.presheaf.obj (op t.left) where
  hom := compositeSectionsEvalHom B S hS q r hq hr F hF c J N t.left t.hom
  inv := compositeSectionsOfIsTerminalHom N ht
  hom_inv_id := compositeSectionsEvalHom_comp_compositeSectionsOfIsTerminalHom N ht
  inv_hom_id := compositeSectionsOfIsTerminalHom_comp_compositeSectionsEvalHom N ht

/-- `compositeSectionsIsoOfIsTerminalApp` is natural in the module. -/
theorem compositeSectionsIsoOfIsTerminalApp_naturality {y : 𝒴}
    {t : CostructuredArrow (c ⋙ F) y} (ht : IsTerminal t)
    {N N' : SheafOfModules.{u + 1} (compositeRing B S hS q hq c J)} (ψ : N ⟶ N') :
    (compositeDirectImage B S hS q r hq hr F hF c J ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y)).map ψ ≫
        (compositeSectionsIsoOfIsTerminalApp N' ht).hom =
      (compositeSectionsIsoOfIsTerminalApp N ht).hom ≫
        (SheafOfModules.toSheaf _ ⋙ (sheafSections J AddCommGrpCat.{u + 1}).obj (op t.left)).map
          ψ :=
  compositeSectionsEvalHom_naturality_left (B := B) (S := S) (hS := hS) (q := q) (r := r)
    (hq := hq) (hr := hr) (F := F) (hF := hF) (c := c) (J := J) ψ t.left t.hom

/-- **The sections formula of `F_* c_*` at a terminal arrow.** If `t = (a₀, φ₀)` is terminal in
`CostructuredArrow (c ⋙ F) y`, evaluation at `t` identifies the sections over `y` of `F_* c_* N`
with the sections of `N` over `a₀`, naturally in `N`. -/
def compositeSectionsIsoOfIsTerminal {y : 𝒴} {t : CostructuredArrow (c ⋙ F) y}
    (ht : IsTerminal t) :
    compositeDirectImage B S hS q r hq hr F hF c J ⋙ SheafOfModules.toSheaf _ ⋙
        (sheafSections _ AddCommGrpCat.{u + 1}).obj (op y) ≅
      SheafOfModules.toSheaf _ ⋙ (sheafSections J AddCommGrpCat.{u + 1}).obj (op t.left) :=
  NatIso.ofComponents (fun N => compositeSectionsIsoOfIsTerminalApp N ht)
    (fun {_ _} ψ => compositeSectionsIsoOfIsTerminalApp_naturality ht ψ)

end AlgebraicGeometry.Stack

end
