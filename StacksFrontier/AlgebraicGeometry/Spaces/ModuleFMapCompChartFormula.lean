module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# The chart formula for a composite of linear maps of sections

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`.  Stacks 03G4 identifies linear maps of sections along `f` with morphisms of
modules into the direct image, and `AlgebraicGeometry.Space.FMap.comp`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartCorrespondenceComp.lean`) composes the underlying
maps of sheaves of sets, with the chart formula `AlgebraicGeometry.Space.FMap.comp_app` on every
chart diagram over `f ≫ g` that factors through an étale scheme chart of `Y`.

This file composes linear maps of *modules* of sections the same way and proves the
corresponding chart formula.  The composite is built by transport: the two morphisms of modules
into the direct images, composed, followed by a comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct
images, carried back across the module chart correspondence.  The comparison is taken as a
parameter together with the one property of it that is used — that it is the geometric
comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on
underlying sheaves of sets — so that nothing here depends on how it is constructed.  For the
comparison of Stacks 03LU in the form
`AlgebraicGeometry.Space.pushforwardModulesCompAt` transported along
`AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU, that property is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`.

## Main definitions

* `AlgebraicGeometry.Space.moduleFMapCompHom`: the morphism of modules into the direct image
  along `f ≫ g` attached to a linear map of sections along `g` and one along `f`.
* `AlgebraicGeometry.Space.ModuleFMap.compOfIso`: **the composite of two linear maps of
  sections**, relative to a comparison of direct images.

## Main results

* `AlgebraicGeometry.Space.moduleFMapSetHom_compOfIso`: the homomorphism of sheaves of sets of
  the composite is the composite of the two homomorphisms of sheaves of sets, taken with the
  geometric comparison — which is the defining equation of
  `AlgebraicGeometry.Space.FMap.comp`.
* `AlgebraicGeometry.Space.toFMap_compOfIso`: so the `f`-map underlying the composite *is*
  `AlgebraicGeometry.Space.FMap.comp`.
* `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app`: **the chart formula.**  On a chart diagram
  over `f ≫ g` whose vertical morphism factors through an étale scheme chart of `Y`, the
  composite is the composite of the two components.

## Implementation notes

The comparison of direct images is a *parameter* `ι` rather than a fixed construction, and the
composite is a definition whose value mentions `ι` and no proof term.  That is deliberate: Lean
lifts proofs nested in the value of a definition into auxiliary theorems, after which an
argument's inferred type is no longer syntactically the parameter type it is checked against,
the kernel's structural shortcut fails, and the full definitional check reaches the comparison
equivalence of Stacks 03G1 and does not terminate.  With `ι` a parameter, every argument of
every application below is a variable or a constant applied to variables, and no proof is
lifted.

For the same reason the chain of identifications proving
`AlgebraicGeometry.Space.moduleFMapSetHom_compOfIso` is cut into one named step per factor, each
stated at the smallest type that carries it: handing the kernel the composite as a single term
does not terminate even though each factor is immediate.

`CategoryTheory.Functor.map_comp` is used through the private `map_comp'` below rather than as
the field projection `Φ.map_comp`, because the projection has to be taken at the concrete
functor `Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)`, which is a composite, and
reducing it to a structure instance there is not cheap; at a variable functor it is free.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A composite of two equal factors is equal to the composite of the two targets. -/
private theorem comp_congr {C : Type*} [Category C] {A A' A'' : C} {a a' : A ⟶ A'}
    {b b' : A' ⟶ A''} (ha : a = a') (hb : b = b') : a ≫ b = a' ≫ b' := by rw [ha, hb]

/-- `CategoryTheory.Functor.map_comp` at a variable functor, so that applying it to a concrete
one is a first-order match. -/
private theorem map_comp' {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D) {A A' A'' : C}
    (a : A ⟶ A') (b : A' ⟶ A'') : Φ.map (a ≫ b) = Φ.map a ≫ Φ.map b := Φ.map_comp a b

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The module chart correspondence on underlying sheaves of sets -/

/-- **The homomorphism of sheaves of sets of the linear map of sections of a morphism of modules
into the direct image is that morphism.**  This is
`AlgebraicGeometry.Space.moduleFMapSetHom_modulePushforwardHomFMap` read in the direction that
starts from a linear map of sections, the two directions of the module chart correspondence of
Stacks 03G4 being mutually inverse. -/
theorem moduleSheafFunctor_map_moduleFMapHom (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (ξ : ModuleFMap B S hS f F G) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (moduleFMapHom B S hS f F G ξ) =
      moduleFMapSetHom B S hS f F G ξ :=
  (moduleFMapSetHom_modulePushforwardHomFMap B S hS f F G
      (moduleFMapHom B S hS f F G ξ)).symm.trans
    (congrArg (moduleFMapSetHom B S hS f F G)
      ((modulePushforwardHomEquiv B S hS f F G).apply_symm_apply ξ))

/-- The linear map of sections of the identity of the direct image is the counit of the chartwise
universal property of Stacks 03LU. -/
theorem modulePushforwardHomFMap_id (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    modulePushforwardHomFMap B S hS f F ((modulePushforward B S hS f).obj F)
        (𝟙 ((modulePushforward B S hS f).obj F)) =
      modulePushforwardCounit B S hS f F :=
  ModuleFMap.ext B S hS (funext fun _ ↦ funext fun _ ↦ rfl)

/-- **The morphism of modules of the counit is the identity.** -/
theorem moduleFMapHom_modulePushforwardCounit (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleFMapHom B S hS f F ((modulePushforward B S hS f).obj F)
        (modulePushforwardCounit B S hS f F) =
      𝟙 ((modulePushforward B S hS f).obj F) :=
  (congrArg
      (moduleFMapHom B S hS f F ((modulePushforward B S hS f).obj F))
      (modulePushforwardHomFMap_id B S hS f F)).symm.trans
    ((modulePushforwardHomEquiv B S hS f F
      ((modulePushforward B S hS f).obj F)).symm_apply_apply _)

/-! ### The composite of two linear maps of sections -/

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (ι : modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS (f ≫ g))

/-- The morphism of modules from `H` into the direct image of `F` along `f ≫ g` attached to a
linear map of sections along `g` from `G` to `H` and one along `f` from `F` to `G`: the morphism
of modules of the first, followed by the direct image along `g` of the morphism of modules of
the second, followed by the given comparison of the direct images. -/
noncomputable def moduleFMapCompHom : H ⟶ (modulePushforward B S hS (f ≫ g)).obj F :=
  moduleFMapHom B S hS g G H ξ ≫
    ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫ ι.hom.app F)

/-- **The composite of two linear maps of sections**, relative to a comparison `ι` of the direct
images: the linear map of sections along `f ≫ g` which the module chart correspondence of
Stacks 03G4 attaches to `AlgebraicGeometry.Space.moduleFMapCompHom`. -/
noncomputable def ModuleFMap.compOfIso : ModuleFMap B S hS (f ≫ g) F H :=
  modulePushforwardHomFMap B S hS (f ≫ g) F H
    (moduleFMapCompHom B S hS f g F G H ξ η ι)

/-- `AlgebraicGeometry.Space.moduleFMapCompHom` written out. -/
theorem moduleFMapCompHom_eq : moduleFMapCompHom B S hS f g F G H ξ η ι =
    moduleFMapHom B S hS g G H ξ ≫
      ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫ ι.hom.app F) := rfl

/-- The homomorphism of sheaves of sets of the composite is the image of
`AlgebraicGeometry.Space.moduleFMapCompHom`. -/
theorem moduleFMapSetHom_compOfIso_eq :
    moduleFMapSetHom B S hS (f ≫ g) F H (ModuleFMap.compOfIso B S hS f g F G H ξ η ι) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        (moduleFMapHom B S hS g G H ξ ≫
          ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫ ι.hom.app F)) :=
  (moduleFMapSetHom_modulePushforwardHomFMap B S hS (f ≫ g) F H
      (moduleFMapCompHom B S hS f g F G H ξ η ι)).trans
    (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
      (moduleFMapCompHom_eq B S hS f g F G H ξ η ι))

/-- The middle factor on underlying sheaves of sets: the direct image of a morphism of modules is
the direct image of its underlying map of sheaves of sets. -/
theorem moduleSheafFunctor_map_middle :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η)) =
      (smallEtaleDirectImage B S hS g).map (moduleFMapSetHom B S hS f F G η) :=
  (moduleSheafFunctor_map_modulePushforward_map B S hS g
      (moduleFMapHom B S hS f F G η)).trans
    (congrArg (smallEtaleDirectImage B S hS g).map
      (moduleSheafFunctor_map_moduleFMapHom B S hS f F G η))

/-- **The homomorphism of sheaves of sets of the composite is the defining composite of
`AlgebraicGeometry.Space.FMap.comp`**: the homomorphism of the outer linear map of sections, the
direct image of the homomorphism of the inner one, and the geometric comparison of Stacks 03G2,
part (3). -/
theorem moduleFMapSetHom_compOfIso
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map (ι.hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :
    moduleFMapSetHom B S hS (f ≫ g) F H (ModuleFMap.compOfIso B S hS f g F G H ξ η ι) =
      moduleFMapSetHom B S hS g G H ξ ≫
        (smallEtaleDirectImage B S hS g).map (moduleFMapSetHom B S hS f F G η) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  (moduleFMapSetHom_compOfIso_eq B S hS f g F G H ξ η ι).trans
    ((map_comp' (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z))
        (moduleFMapHom B S hS g G H ξ)
        ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η) ≫
          ι.hom.app F)).trans
      (comp_congr (moduleSheafFunctor_map_moduleFMapHom B S hS g G H ξ)
        ((map_comp' (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z))
            ((modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η))
            (ι.hom.app F)).trans
          (comp_congr (moduleSheafFunctor_map_middle B S hS f g F G η) hι))))

/-- **The `f`-map of sheaves of sets underlying the composite is
`AlgebraicGeometry.Space.FMap.comp`.**  Both have the same homomorphism into the direct image,
and the chart correspondence of Stacks 03G4 is a bijection. -/
theorem toFMap_compOfIso
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map (ι.hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :
    ModuleFMap.toFMap B S hS (ModuleFMap.compOfIso B S hS f g F G H ξ η ι) =
      FMap.comp B S hS f g (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
        (moduleSetSheaf B S hS Z H) (ModuleFMap.toFMap B S hS ξ)
        (ModuleFMap.toFMap B S hS η) :=
  FMap.comp_unique B S hS f g (moduleSetSheaf B S hS X F) (moduleSetSheaf B S hS Y G)
    (moduleSetSheaf B S hS Z H) (ModuleFMap.toFMap B S hS ξ) (ModuleFMap.toFMap B S hS η)
    (ModuleFMap.toFMap B S hS (ModuleFMap.compOfIso B S hS f g F G H ξ η ι))
    (moduleFMapSetHom_compOfIso B S hS f g F G H ξ η ι hι)

end Comp

/-! ### The chart formula -/

section Factor

variable (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (ι : modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS (f ≫ g))

/-- **The chart formula for the composite of two linear maps of sections.**  On a chart diagram
over `f ≫ g` whose vertical scheme morphism factors through an étale scheme chart `V` of `Y`,
compatibly with the two structure morphisms, the composite is the component of the inner linear
map of sections at the lower diagram followed by the component of the outer one at the upper
diagram.

This is `AlgebraicGeometry.Space.FMap.comp_app` read through
`AlgebraicGeometry.Space.toFMap_compOfIso`; the components of a linear map of sections and of
the `f`-map underlying it are the same. -/
theorem ModuleFMap.compOfIso_app
    (hι : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map (ι.hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
    (s : H.val.obj (op W)) :
    (ModuleFMap.compOfIso B S hS f g F G H ξ η ι).app
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      η.app ⟨U, V, a, ha⟩ (ξ.app ⟨V, W, b, hb⟩ s) :=
  (congrFun (congrFun (congrArg FMap.app
      (toFMap_compOfIso B S hS f g F G H ξ η ι hι))
    (ChartDiagram.comp B S hS f g a b ha hb)) s).trans
    (FMap.comp_app B S hS f g a b ha hb (moduleSetSheaf B S hS X F)
      (moduleSetSheaf B S hS Y G) (moduleSetSheaf B S hS Z H)
      (ModuleFMap.toFMap B S hS ξ) (ModuleFMap.toFMap B S hS η) s)

end Factor

end AlgebraicGeometry.Space

end
