module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeKernelFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The relative Hom functor out of a colimit of source modules

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `G` be an
`𝒪_X`-module, and let `F = colim F_i` be a colimit of `𝒪_X`-modules.  Then

`Hom(F, G) = lim Hom(F_i, G)`

as functors on the algebraic spaces over `X`, and therefore — after restriction along the base
change of a morphism `f : X ⟶ B` — as the relative Hom functors of Stacks 08JT of the
situations obtained by replacing the source module.

This is the identification the proof of Stacks 08K6 makes after writing the source module as a
filtered colimit of finitely presented modules by Limits of Spaces, Lemma 07V9: *"It is clear
that `Hom(F, G) = lim Hom(F_i, G)`."*  What makes it work on every test scheme at once is that
the inverse image of modules is a left adjoint, by the adjunction half of Stacks 03LU, so it
carries the colimit presentation of `F` to a colimit presentation of `F_T` for every `T`.

## Main definitions

* `AlgebraicGeometry.Space.moduleHomOverPrecomp`: the morphism of relative Hom functors over
  the algebraic spaces over `X` induced by a morphism of the source modules.
* `AlgebraicGeometry.Space.moduleHomOverPrecompIso`: an isomorphism of the source modules
  induces an isomorphism of the relative Hom functors.
* `AlgebraicGeometry.Space.moduleHomOverSystem`: **the inverse system of relative Hom functors
  of a direct system of source modules.**
* `AlgebraicGeometry.Space.moduleHomOverColimitCone`: the cone on that system whose vertex is
  the relative Hom functor out of the vertex of the direct system's cocone.
* `AlgebraicGeometry.Space.HomSituation.homFunctorSystem`: the same system, read on the test
  schemes over the base, so that its value at a stage is the relative Hom functor of
  Stacks 08JT with the source module replaced by that stage.

## Main results

* `AlgebraicGeometry.Space.isLimit_moduleHomOverColimitCone`: **`Hom(colim F_i, G)` is the
  inverse limit of the `Hom(F_i, G)`**, as functors on the algebraic spaces over `X`.
* `AlgebraicGeometry.Space.HomSituation.isLimit_homFunctorColimitCone`: the same statement for
  the relative Hom functors of Stacks 08JT on the test schemes over the base.

## Implementation notes

**Where the colimit hypothesis is used.**  The only input is that the inverse image
`z^* : Mod(𝒪_X) ⥤ Mod(𝒪_Z)` along an algebraic space `z : Z → X` over `X` preserves colimits,
which holds because it is a left adjoint: `AlgebraicGeometry.Space.modulePullbackAdjunction`,
the adjunction half of Stacks 03LU, is available with no hypothesis.  So `z^*F` is the colimit
of the `z^*F_i`, and a homomorphism out of a colimit is the same thing as a compatible family of
homomorphisms out of the members.  The index of the inverse system is `Iᵒᵖ`, and no
filteredness of `I` is needed for this identification; filteredness enters only where the
limit is turned back into an algebraic space, in
`StacksFrontier/AlgebraicGeometry/Quot/PointsOverBaseInverseLimit.lean`.

**Why the system is built over the algebraic spaces over `X` and then restricted.**  The
relative Hom functor of Stacks 08JT is `AlgebraicGeometry.Space.moduleHomOver` composed with
the base change along the test schemes, as recorded in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.  Both the system and the comparison are
therefore built for `moduleHomOver`, where there is one variable instead of two, and restricted
along `(baseChangeOver s.f).op` afterwards; restriction along a functor preserves limits, so the
comparison survives it.

**The naturality of precomposition** is `CategoryTheory.Functor.conjHom_map_comp`, the
precomposition counterpart of `CategoryTheory.Functor.conjHom_comp_map` of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomClosedImmersion.lean`: the first is naturality
of the comparison `e.hom` of the two inverse images at a morphism of the source, the second
naturality of `e.inv` at a morphism of the target.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS}

/-! ### Changing the source module -/

section Precomp

variable (hc : ModulePushforwardCoherence B S hS)

/-- Precomposition of a homomorphism `z^*F' ⟶ z^*G` with the inverse image of a morphism
`ψ : F ⟶ F'` of the source modules: the component of
`AlgebraicGeometry.Space.moduleHomOverPrecomp`. -/
def moduleHomOverPrecompApp {F F' G : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ F')
    (Z : Over X)
    (α : (modulePullback B S hS Z.hom).obj F' ⟶ (modulePullback B S hS Z.hom).obj G) :
    (modulePullback B S hS Z.hom).obj F ⟶ (modulePullback B S hS Z.hom).obj G :=
  (modulePullback B S hS Z.hom).map ψ ≫ α

/-- **The morphism of relative Hom functors induced by a morphism of the source modules.**  A
morphism `ψ : F ⟶ F'` of `𝒪_X`-modules carries a homomorphism `z^*F' ⟶ z^*G` to its
precomposition with `z^*ψ`, naturally in the algebraic space `z : Z → X` over `X`.

Naturality is `CategoryTheory.Functor.conjHom_map_comp`: inverse image of homomorphisms
commutes with precomposition. -/
def moduleHomOverPrecomp {F F' : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ F')
    (G : Modules.{u, u} B S hS X.1 X.2) :
    moduleHomOver hc F' G ⟶ moduleHomOver hc F G where
  app Z := ↾moduleHomOverPrecompApp (G := G) ψ Z.unop
  naturality W Z m :=
    ofHom_comp_eq_comp
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      (moduleHomOverPrecompApp (G := G) ψ Z.unop)
      (moduleHomOverPrecompApp (G := G) ψ W.unop)
      (Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)))
      fun α ↦ (Functor.conjHom_map_comp
        (modulePullbackTriangle B S hS (Over.w m.unop)) ψ α).symm

/-- The morphism of relative Hom functors induced by a morphism of the source modules acts by
precomposition with the inverse image of that morphism. -/
theorem moduleHomOverPrecomp_app_apply {F F' : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ F')
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : (Over X)ᵒᵖ)
    (α : (moduleHomOver hc F' G).obj Z) :
    (moduleHomOverPrecomp hc ψ G).app Z α =
      (modulePullback B S hS Z.unop.hom).map ψ ≫ α :=
  rfl

/-- Precomposing with the inverse image of an identity changes nothing. -/
theorem moduleHomOverPrecompApp_id (F G : Modules.{u, u} B S hS X.1 X.2) (Z : Over X)
    (α : (modulePullback B S hS Z.hom).obj F ⟶ (modulePullback B S hS Z.hom).obj G) :
    moduleHomOverPrecompApp (𝟙 F) Z α = α := by
  show (modulePullback B S hS Z.hom).map (𝟙 F) ≫ α = α
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Precomposing with the inverse image of a composite is precomposing twice. -/
theorem moduleHomOverPrecompApp_comp {F F' F'' G : Modules.{u, u} B S hS X.1 X.2}
    (ψ : F ⟶ F') (ψ' : F' ⟶ F'') (Z : Over X)
    (α : (modulePullback B S hS Z.hom).obj F'' ⟶ (modulePullback B S hS Z.hom).obj G) :
    moduleHomOverPrecompApp (ψ ≫ ψ') Z α =
      moduleHomOverPrecompApp ψ Z (moduleHomOverPrecompApp ψ' Z α) := by
  show (modulePullback B S hS Z.hom).map (ψ ≫ ψ') ≫ α =
    (modulePullback B S hS Z.hom).map ψ ≫
      (modulePullback B S hS Z.hom).map ψ' ≫ α
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The identity of the source module induces the identity. -/
theorem moduleHomOverPrecomp_id (F G : Modules.{u, u} B S hS X.1 X.2) :
    moduleHomOverPrecomp hc (𝟙 F) G = 𝟙 (moduleHomOver hc F G) := by
  refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun α ↦ ?_)
  exact moduleHomOverPrecompApp_id F G Z.unop α

/-- A composite of morphisms of the source modules induces the composite of the induced
morphisms, in the opposite order. -/
theorem moduleHomOverPrecomp_comp {F F' F'' : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ F')
    (ψ' : F' ⟶ F'') (G : Modules.{u, u} B S hS X.1 X.2) :
    moduleHomOverPrecomp hc (ψ ≫ ψ') G =
      moduleHomOverPrecomp hc ψ' G ≫ moduleHomOverPrecomp hc ψ G := by
  refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun α ↦ ?_)
  exact moduleHomOverPrecompApp_comp ψ ψ' Z.unop α

/-- **An isomorphism of the source modules induces an isomorphism of the relative Hom
functors.** -/
def moduleHomOverPrecompIso {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ F')
    (G : Modules.{u, u} B S hS X.1 X.2) :
    moduleHomOver hc F' G ≅ moduleHomOver hc F G where
  hom := moduleHomOverPrecomp hc e.hom G
  inv := moduleHomOverPrecomp hc e.inv G
  hom_inv_id := by
    rw [← moduleHomOverPrecomp_comp, e.inv_hom_id, moduleHomOverPrecomp_id]
  inv_hom_id := by
    rw [← moduleHomOverPrecomp_comp, e.hom_inv_id, moduleHomOverPrecomp_id]

end Precomp

/-! ### The inverse system of relative Hom functors of a direct system of source modules -/

section System

variable (hc : ModulePushforwardCoherence B S hS)
variable {I : Type u} [Category.{u} I]

/-- **The inverse system of relative Hom functors of a direct system of source modules.**  Its
value at a stage is the relative Hom functor out of that stage, and a transition morphism acts
by precomposition. -/
def moduleHomOverSystem (K : I ⥤ Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS X.1 X.2) : Iᵒᵖ ⥤ ((Over X)ᵒᵖ ⥤ Type (u + 1)) where
  obj i := moduleHomOver hc (K.obj i.unop) G
  map φ := moduleHomOverPrecomp hc (K.map φ.unop) G
  map_id i :=
    (congrArg (fun ψ ↦ moduleHomOverPrecomp hc ψ G) (K.map_id i.unop)).trans
      (moduleHomOverPrecomp_id hc (K.obj i.unop) G)
  map_comp φ ψ :=
    (congrArg (fun m ↦ moduleHomOverPrecomp hc m G) (K.map_comp ψ.unop φ.unop)).trans
      (moduleHomOverPrecomp_comp hc (K.map ψ.unop) (K.map φ.unop) G)

/-- The value of the system of relative Hom functors at a stage is the relative Hom functor out
of that stage. -/
theorem moduleHomOverSystem_obj (K : I ⥤ Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS X.1 X.2) (i : Iᵒᵖ) :
    (moduleHomOverSystem hc K G).obj i = moduleHomOver hc (K.obj i.unop) G :=
  rfl

variable (K : I ⥤ Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS X.1 X.2)

/-- The transition morphism of the inverse system of relative Hom functors acts by
precomposition with the inverse image of the transition morphism of the direct system. -/
theorem moduleHomOverSystem_map_app (Z : (Over X)ᵒᵖ) {i j : Iᵒᵖ} (φ : i ⟶ j)
    (α : ((moduleHomOverSystem hc K G).obj i).obj Z) :
    ((moduleHomOverSystem hc K G).map φ).app Z α =
      (modulePullback B S hS Z.unop.hom).map (K.map φ.unop) ≫ α :=
  rfl

/-- **The cocone on the inverse image of the direct system determined by a compatible family of
homomorphisms to the inverse image of `G`.**  This is the datum the universal property of the
colimit consumes: a section of the inverse system of relative Hom functors at an algebraic
space `z : Z → X` over `X` is exactly a cocone on `z^*K` with vertex `z^*G`. -/
def moduleHomOverSystemCocone (Z : Over X)
    (σ : (i : I) → (K ⋙ modulePullback B S hS Z.hom).obj i ⟶
      (modulePullback B S hS Z.hom).obj G)
    (hσ : ∀ {i j : I} (f : i ⟶ j),
      (K ⋙ modulePullback B S hS Z.hom).map f ≫ σ j = σ i) :
    Cocone (K ⋙ modulePullback B S hS Z.hom) where
  pt := (modulePullback B S hS Z.hom).obj G
  ι := { app := σ, naturality _ _ f := Eq.trans (hσ f) (Category.comp_id _).symm }

variable (cc : Cocone K)

/-- **The cone on the system of relative Hom functors whose vertex is the relative Hom functor
out of the vertex of the given cocone.**  Its leg at a stage is precomposition with the
inclusion of that stage. -/
def moduleHomOverColimitCone : Cone (moduleHomOverSystem hc K G) where
  pt := moduleHomOver hc cc.pt G
  π :=
    { app i := moduleHomOverPrecomp hc (cc.ι.app i.unop) G
      naturality := by
        intro i j φ
        refine (Category.id_comp _).trans ?_
        exact (congrArg (fun ψ ↦ moduleHomOverPrecomp hc ψ G) (cc.w φ.unop).symm).trans
          (moduleHomOverPrecomp_comp hc (K.map φ.unop) (cc.ι.app i.unop) G) }

/-- **`Hom(colim F_i, G)` is the inverse limit of the `Hom(F_i, G)`**, as functors on the
algebraic spaces over `X`.

The claim is pointwise, by `CategoryTheory.Limits.evaluationJointlyReflectsLimits`.  At an
algebraic space `z : Z → X` over `X` the inverse image `z^*` preserves the given colimit,
because it is a left adjoint by the adjunction half of Stacks 03LU, so `z^*F` is the colimit of
the `z^*F_i`; a homomorphism `z^*F ⟶ z^*G` is then exactly a compatible family of
homomorphisms `z^*F_i ⟶ z^*G`, which is the universal property of that colimit. -/
def isLimit_moduleHomOverColimitCone (hcc : IsColimit cc) :
    IsLimit (moduleHomOverColimitCone hc K G cc) := by
  refine evaluationJointlyReflectsLimits _ fun Z ↦ Nonempty.some
    ((Types.isLimit_iff _).mpr ?_)
  intro s hs
  have hpres : PreservesColimitsOfSize.{u, u} (modulePullback B S hS Z.unop.hom) :=
    (modulePullbackAdjunction B S hS Z.unop.hom).leftAdjoint_preservesColimits
  have hZ : IsColimit ((modulePullback B S hS Z.unop.hom).mapCocone cc) :=
    isColimitOfPreserves _ hcc
  have hs' : ∀ {i j : I} (f : i ⟶ j),
      (K ⋙ modulePullback B S hS Z.unop.hom).map f ≫ s (Opposite.op j) =
        s (Opposite.op i) := fun {i j} f ↦
    (moduleHomOverSystem_map_app hc K G Z f.op (s (Opposite.op j))).symm.trans (hs f.op)
  refine ⟨hZ.desc (moduleHomOverSystemCocone K G Z.unop (fun i ↦ s (Opposite.op i))
      fun f ↦ hs' f), fun i ↦ ?_, fun m hm ↦ ?_⟩
  · exact hZ.fac (moduleHomOverSystemCocone K G Z.unop (fun i ↦ s (Opposite.op i))
      fun f ↦ hs' f) i.unop
  · exact hZ.uniq (moduleHomOverSystemCocone K G Z.unop (fun i ↦ s (Opposite.op i))
      fun f ↦ hs' f) m fun i ↦ hm (Opposite.op i)

end System

/-! ### The same statement at the relative Hom functor of Stacks 08JT -/

namespace HomSituation

variable (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)
variable {I : Type u} [Category.{u} I] (K : I ⥤ Modules.{u, u} B S hS s.X.1 s.X.2)

/-- Restriction of a functor on the algebraic spaces over the source along the base change of
the situation's morphism: it carries `AlgebraicGeometry.Space.moduleHomOver` to the relative
Hom functor of Stacks 08JT. -/
abbrev restrictAlongBaseChange :
    (((Over s.X)ᵒᵖ) ⥤ Type (u + 1)) ⥤ (((s.SchemesOver)ᵒᵖ) ⥤ Type (u + 1)) :=
  (Functor.whiskeringLeft ((s.SchemesOver)ᵒᵖ) ((Over s.X)ᵒᵖ) (Type (u + 1))).obj
    (baseChangeOver s.f).op

/-- Restriction along the base change carries the relative Hom functor over the algebraic
spaces over the source to the relative Hom functor of Stacks 08JT. -/
theorem restrictAlongBaseChange_obj_moduleHomOver
    (F G : Modules.{u, u} B S hS s.X.1 s.X.2) :
    s.restrictAlongBaseChange.obj (moduleHomOver hc F G) =
      (baseChangeOver s.f).op ⋙ moduleHomOver hc F G :=
  rfl

/-- **The inverse system of the relative Hom functors of Stacks 08JT of the situations obtained
by replacing the source module by the members of a direct system.** -/
def homFunctorSystem : Iᵒᵖ ⥤ (((s.SchemesOver)ᵒᵖ) ⥤ Type (u + 1)) :=
  moduleHomOverSystem hc K s.G ⋙ s.restrictAlongBaseChange

/-- The cone on the system of relative Hom functors of Stacks 08JT whose vertex is the relative
Hom functor out of the vertex of the given cocone. -/
def homFunctorColimitCone (cc : Cocone K) : Cone (s.homFunctorSystem hc K) :=
  s.restrictAlongBaseChange.mapCone (moduleHomOverColimitCone hc K s.G cc)

/-- **The relative Hom functor of Stacks 08JT out of a colimit of source modules is the inverse
limit of the relative Hom functors out of the members.**

This is `AlgebraicGeometry.Space.isLimit_moduleHomOverColimitCone` restricted along the base
change of the situation's morphism; restriction along a functor preserves limits. -/
def isLimit_homFunctorColimitCone (cc : Cocone K) (hcc : IsColimit cc) :
    IsLimit (s.homFunctorColimitCone hc K cc) :=
  isLimitOfPreserves s.restrictAlongBaseChange
    (isLimit_moduleHomOverColimitCone hc K s.G cc hcc)

/-- The vertex of the cone is the relative Hom functor of Stacks 08JT of the situation whose
source module is the vertex of the given cocone, up to the isomorphism of source modules. -/
def homFunctorColimitConePtIso (cc : Cocone K) (e : cc.pt ≅ s.F) :
    (s.homFunctorColimitCone hc K cc).pt ≅ s.homFunctor hc :=
  s.restrictAlongBaseChange.mapIso (moduleHomOverPrecompIso hc e s.G).symm

end HomSituation

end AlgebraicGeometry.Space

end
