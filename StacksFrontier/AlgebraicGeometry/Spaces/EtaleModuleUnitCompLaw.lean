module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitChain
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The unit of étale restriction of modules, on underlying sheaves of sets

Let `f : D ⟶ A` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Along an étale morphism the inverse image of modules of Stacks 03LU is étale
restriction, by Stacks 03LW, and `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the
adjunction of Stacks 03LU read through that identification.  This file decomposes its unit and
reads each factor on underlying sheaves of sets, the target being the identification of that
unit with the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`, the
corresponding adjunction for sheaves of sets.

That identification is what carries the composition law for the inverse image of Stacks 03LQ at
an arbitrary sheaf of sets,
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp`, up to modules, and the
law for modules is exactly the comparison of the units that
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` asks for — hence
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, the
coherence that the full faithfulness clause of Stacks 04W6 is conditional on.

## Main results

* `CategoryTheory.Adjunction.ofNatIsoLeft_unit_app` and `.ofNatIsoRight_unit_app`: the unit of a
  transported adjunction at a single object.
* `CategoryTheory.Functor.map_comp₄` and `.comp_map_comp`: the image of a four-factor composite
  under a functor, and a composite with the images of two composable morphisms, each with the
  images named.  Both are stated on variables.
* `AlgebraicGeometry.Space.pullbackAdjPushforwardModules_unit_app`: the unit of Stacks 03D7 for
  the morphism of small étale ringed topoi is the unit of Stacks 03D3 followed by the direct
  image of the unit of the extension of scalars.
* `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app_decomp`: the two together —
  the unit of étale restriction as a four-factor composite.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_restrictScalars_map`: on underlying sheaves of
  sets, restriction of scalars is invisible.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_app_comp`:
  **the unit of the extension of scalars, followed by the identification of Stacks 03LW, is the
  comparison of Stacks 03LQ**, on underlying sheaves of sets.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_directImageModules_map'` and
  `.moduleSheafFunctor_map_inverseImageAdj_unit_app`: the direct image of Stacks 03D3 and the
  unit of Stacks 03D3, read with the direct image and the adjunction of the small étale topoi.
* `CategoryTheory.Sheaf.map_hom_app_congr` and `.map_comp_hom_app_apply`: the image under a
  functor of sheaves of types of two equal morphisms, and of a composite, read on a section.
  Both are stated on variables.
* `AlgebraicGeometry.Space.smallEtaleDirectImage_map_inverseImageIso_hom_app`: **the direct
  image along `f` of the comparison of Stacks 03LQ, read on a section** — the direct image of
  the unit of the extension of scalars, then the direct image of the identification of
  Stacks 03LW.
* `CategoryTheory.Sheaf.hom_app_apply_congr`: a morphism of sheaves of types takes equal
  sections to equal sections, on variables.
* `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction`: **the
  unit of étale restriction of modules is the unit of étale restriction of sheaves of sets**,
  read on a section, with no representability assumed. Its morphism-level form is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`.

## Implementation notes

Two spellings of one category occur throughout: `AlgebraicGeometry.Space.Modules` is
`SheafOfModules (RingedSite.ringSheaf (smallEtaleRingedSite ...))`, while the ringed-topos
development spells the same thing
`SheafOfModules (Stacks.Sheaves.RingedToposModules.structureRingSheaf (smallEtaleRingedTopos ...))`.
The two are definitionally equal but not syntactically so, and a composite that mixes them is
not type-correct at `implicit` transparency, so `rw` declines every step that would rewrite one
into the other.  Each such step is therefore done in term mode, where unification runs at
default transparency.  For the same reason the decomposition of the unit of
`AlgebraicGeometry.Space.modulePullbackAdjunction` is taken at the level of natural
transformations, where the `unit` field of the transported adjunction reduces by iota; at a
component the same equation exhausts the heartbeat budget at `whnf`.  This is the obstruction
that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` describe, and that
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean` exists to absorb.

A second, finer spelling discipline is forced by the same transparency.  The underlying sheaf
of sets of a module has two names, the reducible abbreviation
`AlgebraicGeometry.Space.moduleSetSheaf` and `(CategoryTheory.Sheaf.moduleSheafFunctor _).obj`,
whose equality needs a `def` to be unfolded.  Where such a term is an *argument* of a morphism
that a functor of sheaves of sets is applied to, the two names must agree syntactically: if
they do not, the unifier fails to match the arguments at its current transparency and falls
back on unfolding `AlgebraicGeometry.Space.smallEtaleDirectImage`, which is three functors deep
and exhausts the heartbeat budget.  `smallEtaleDirectImage_map_inverseImageIso_hom_app` is
therefore stated with the name that
`moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_app_comp` uses.

## What this leaves

The comparison of the units that
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` asks for, and with it
`ModulePullbackCompIsoEtaleRestriction` —

```
(etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
  (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit
```

— is **proved**, in `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean`.  What
this file contributes to it is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction` and its
morphism form, the
identification that carries the composition law for sheaves of sets up to modules; the three
remaining steps are
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean` (the decomposition of the
composite unit and the reading of each factor),
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompAbsorption.lean` (the absorption of the
fourth factor and the reading of the inner unit on a section) and the join.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]

/-- The unit of an adjunction transported along a natural isomorphism of its left adjoint, at
a single object. -/
theorem ofNatIsoLeft_unit_app {F F' : CC ⥤ DD} {G : DD ⥤ CC} (adj : F ⊣ G) (iso : F ≅ F')
    (X : CC) :
    (adj.ofNatIsoLeft iso).unit.app X = adj.unit.app X ≫ G.map (iso.hom.app X) := by
  rw [ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app]

/-- The unit of an adjunction transported along a natural isomorphism of its right adjoint, at
a single object. -/
theorem ofNatIsoRight_unit_app {F : CC ⥤ DD} {G G' : DD ⥤ CC} (adj : F ⊣ G) (iso : G ≅ G')
    (X : CC) :
    (adj.ofNatIsoRight iso).unit.app X = adj.unit.app X ≫ iso.hom.app (F.obj X) := by
  rw [ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- The image of a four-factor composite under a functor, with each factor's image named.
Stated on variables, so that the three applications of `CategoryTheory.Functor.map_comp` are
paid once and not inside a concrete term. -/
theorem map_comp₄ {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]
    (F : CC ⥤ DD) {W X Y Z T : CC} {u : W ⟶ T} (e : W ⟶ X) (g : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T)
    (hu : u = ((e ≫ g) ≫ c) ≫ d) {e' : F.obj W ⟶ F.obj X} {g' : F.obj X ⟶ F.obj Z}
    {d' : F.obj Z ⟶ F.obj T} (he : F.map e = e') (hgc : F.map (g ≫ c) = g')
    (hd : F.map d = d') :
    F.map u = e' ≫ g' ≫ d' := by
  rw [hu, Category.assoc e g c, F.map_comp, F.map_comp, he, hgc, hd, Category.assoc]

/-- A composite with the images of two composable morphisms, with their composite's image
named.  Stated on variables, so that the two spellings of the middle object are identified once
and not inside a concrete term. -/
theorem comp_map_comp {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]
    (F : CC ⥤ DD) {V : DD} {X Y Z : CC} (a : V ⟶ F.obj X) (b : X ⟶ Y) (c : Y ⟶ Z)
    {bc : X ⟶ Z} (hbc : b ≫ c = bc) :
    a ≫ F.map b ≫ F.map c = a ≫ F.map bc := by
  rw [← F.map_comp, hbc]

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

universe w v₁ u₁

variable {CC : Type u₁} [Category.{v₁} CC] {JJ : GrothendieckTopology CC}

/-- Equal morphisms of sheaves of types agree on a section. -/
theorem hom_app_congr {P Q : Sheaf JJ (Type w)} {a b : P ⟶ Q} (h : a = b) (W : CCᵒᵖ)
    (x : P.obj.obj W) : a.hom.app W x = b.hom.app W x := by rw [h]

/-- A composite of morphisms of sheaves of types acts on a section as the two factors in
turn. -/
theorem comp_hom_app_apply {P Q R : Sheaf JJ (Type w)} (a : P ⟶ Q) (b : Q ⟶ R) (W : CCᵒᵖ)
    (x : P.obj.obj W) : (a ≫ b).hom.app W x = b.hom.app W (a.hom.app W x) := rfl

universe w' v₂ u₂

variable {DD : Type u₂} [Category.{v₂} DD] {KK : GrothendieckTopology DD}

/-- The image under a functor of sheaves of types of a morphism that factors, read on a
section: it is the images of the two factors in turn, each with its value on the section
named.  Stated on variables, so that the regrouping and the identification of the middle
object are paid once and not inside a concrete term. -/
theorem map_comp_hom_app_apply (F : Sheaf JJ (Type w) ⥤ Sheaf KK (Type w'))
    {P Q R : Sheaf JJ (Type w)} (a : P ⟶ Q) (b : Q ⟶ R) (W : DDᵒᵖ) (x : (F.obj P).obj.obj W)
    {y : (F.obj Q).obj.obj W} (ha : (F.map a).hom.app W x = y) {t : (F.obj R).obj.obj W}
    (hb : (F.map b).hom.app W y = t) :
    (F.map (a ≫ b)).hom.app W x = t := by
  rw [F.map_comp, comp_hom_app_apply, ha, hb]

/-- Equal morphisms of sheaves of types have equal images under a functor of sheaves of types,
read on a section.  Stated on variables, so that the identification of the two spellings of the
source and of the target is paid once and not inside a concrete term. -/
theorem map_hom_app_congr (F : Sheaf JJ (Type w) ⥤ Sheaf KK (Type w'))
    {P Q : Sheaf JJ (Type w)} {a b : P ⟶ Q} (h : a = b) (W : DDᵒᵖ)
    (x : (F.obj P).obj.obj W) :
    (F.map a).hom.app W x = (F.map b).hom.app W x := by rw [h]

/-- A morphism of sheaves of types takes equal sections to equal sections.  Stated on
variables, so that the identification of the two spellings of the section's sheaf is paid once
and not inside a concrete term. -/
theorem hom_app_apply_congr {P Q : Sheaf JJ (Type w)} (a : P ⟶ Q) (W : CCᵒᵖ)
    {x y : P.obj.obj W} (h : x = y) : a.hom.app W x = a.hom.app W y := by rw [h]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS}

/-- The unit of Stacks 03D7 for the morphism of small étale ringed topoi, decomposed into the
unit of Stacks 03D3 and the unit of the extension of scalars. -/
theorem pullbackAdjPushforwardModules_unit_app (f : D ⟶ A)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS D)
        (Y := smallEtaleRingedTopos B S hS A)
        (smallEtaleRingedToposModulesHom B S hS f)).unit.app M =
      (inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A)).unit.app M ≫
        (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A)).map
          ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).obj M)) := by
  simp only [pullbackAdjPushforwardModules]
  rfl

/-- Restriction of scalars does not change the underlying morphism of sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictScalars_map (f : D ⟶ A)
    {N N' : Modules.{u, u} B S hS D.1 D.2} (φ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A))).map
        ((SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map φ) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D)).map φ := rfl

/-- **The extension-of-scalars unit, followed by the identification of Stacks 03LW, is the
comparison of Stacks 03LQ**, on underlying sheaves of sets.

On sections the first composite is the transport half of Stacks 03LW by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`, and that transport is
the comparison of Stacks 03LQ on underlying sheaves. -/
theorem moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_app_comp (f : D ⟶ A)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS A.1 A.2) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A))).map
          ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D)).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M) =
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj M) :=
  Sheaf.hom_ext_sections fun U m ↦
    modulePullbackIsoEtaleModulePullback_unit_app B S hS f hf M U m

/-- The direct image of Stacks 03D3 on underlying sheaves of sets, read with the direct image of
the small étale topoi. -/
theorem moduleSheafFunctor_map_directImageModules_map' (f : D ⟶ A)
    {N N' : SheafOfModules.{u} (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS A))}
    (ψ : N ⟶ N') :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).map
        ((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A)).map ψ) =
      (smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A))).map ψ) :=
  moduleSheafFunctor_map_directImageModules_map
    (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS A) ψ

/-- The unit of Stacks 03D3 on underlying sheaves of sets, read with the adjunction of the small
étale topoi. -/
theorem moduleSheafFunctor_map_inverseImageAdj_unit_app (f : D ⟶ A)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).map
        ((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A)).unit.app M) =
      (smallToposMorphismTypeU B S hS f).adj.unit.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj M) :=
  moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app
    (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS A) M

/-- The unit of étale restriction, decomposed into the unit of Stacks 03D3, the unit of the
extension of scalars, the comparison of the two direct images and the identification of
Stacks 03LW. -/
theorem etaleModulePullbackAdjunction_unit_app_decomp (f : D ⟶ A)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS A.1 A.2) :
    (etaleModulePullbackAdjunction B S hS f hf).unit.app M =
      (((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).unit.app M ≫
            (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
                (structureRingSheaf B S hS A)).map
              ((extendScalarsFSharpAdjunction B S hS f).unit.app
                ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
                  (structureRingSheaf B S hS A)).obj M))) ≫
          (modulePushforwardIso B S hS f).hom.app ((modulePullback B S hS f).obj M)) ≫
        (modulePushforward B S hS f).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M) :=
  (etaleModulePullbackAdjunction_unit_app B S hS f hf M).trans
    (congrArg (fun x ↦ x ≫ (modulePushforward B S hS f).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M))
      ((unit_modulePullbackAdjunction_app B S hS f M).trans
        (congrArg (fun y ↦ y ≫ (modulePushforwardIso B S hS f).hom.app
            ((modulePullback B S hS f).obj M))
          (pullbackAdjPushforwardModules_unit_app B S hS f M))))

/-! ### The unit on sections -/

/-- **The unit of étale restriction, read on a section.**  It is the unit of Stacks 03D3, then
the direct image of the unit of the extension of scalars, then the direct image of the
identification of Stacks 03LW.  The comparison of the two direct images does not appear: it is
the identity on sections, by
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`.

This is not `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnit.lean`, which identifies
that unit with the unit of étale restriction of sheaves of sets for a *representable* `f`.  This
one decomposes it, and assumes no representability. -/
theorem etaleModulePullbackAdjunction_unit_val_app_decomp (f : D ⟶ A) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS A.1)ᵒᵖ) (s : M.val.obj W) :
    ((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app W s =
      ((modulePushforward B S hS f).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).val.app W
        (((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).map
            ((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
                (structureRingSheaf B S hS A)).obj M))).val.app W
          (((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A)).unit.app M).val.app W s)) :=
  (modulesHom_val_app_congr (etaleModulePullbackAdjunction_unit_app B S hS f hf M) W s).trans
    ((Stacks.Sheaves.RingedToposModules.comp_val_app_apply _ _ W s).trans
      (congrArg
        (fun z ↦ ((modulePushforward B S hS f).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).val.app W z)
        ((modulePullbackAdjunction_unit_val_app B S hS f M W s).trans
          ((modulesHom_val_app_congr (pullbackAdjPushforwardModules_unit_app B S hS f M) W s).trans
            (Stacks.Sheaves.RingedToposModules.comp_val_app_apply _ _ W s)))))

/-- The direct image of Stacks 03D3 on a section is the direct image of the underlying morphism
of sheaves of sets, read on that section. -/
theorem smallEtaleDirectImage_map_moduleSheafFunctor_hom_app (f : D ⟶ A)
    {N N' : SheafOfModules.{u} (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS A))}
    (ψ : N ⟶ N') (W : (SmallEtale B S hS A.1)ᵒᵖ)
    (y : ((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS A)).obj N).val.obj W) :
    ((smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A))).map ψ)).hom.app W y =
      ((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS A)).map ψ).val.app W y :=
  (Sheaf.hom_app_congr (moduleSheafFunctor_map_directImageModules_map' B S hS f ψ).symm W y).trans
    (moduleSheafFunctor_map_hom_app _ W y)

/-- The direct image of modules on a section is the direct image of the underlying morphism of
sheaves of sets, read on that section. -/
theorem smallEtaleDirectImage_map_moduleSheafFunctor_modulePushforward_hom_app (f : D ⟶ A)
    {N N' : Modules.{u, u} B S hS D.1 D.2} (φ : N ⟶ N') (W : (SmallEtale B S hS A.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f).obj N).val.obj W) :
    ((smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS D)).map φ)).hom.app W y =
      ((modulePushforward B S hS f).map φ).val.app W y :=
  (Sheaf.hom_app_congr (moduleSheafFunctor_map_modulePushforward_map B S hS f φ).symm W y).trans
    (moduleSheafFunctor_map_hom_app _ W y)

/-- The unit of étale restriction of sheaves of sets is the unit of the adjunction of the small
étale topoi followed by the direct image of the comparison of Stacks 03LQ: that comparison is
the comparison of the two left adjoints, and this is its defining property.

Distinct from `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_app_eq`, which
decomposes the same unit over the equivalence
`AlgebraicGeometry.Space.smallEtaleComparisonRestriction` instead, at an arbitrary sheaf of
sets; the suffix names the adjunction this one decomposes it over. -/
theorem smallEtaleSetRestrictionAdjunction_unit_app_eq_smallToposMorphismTypeU (f : D ⟶ A)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS A.1 A.2) :
    (smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
          (moduleSetSheaf B S hS A M) =
      (smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS A M) ≫
        (smallEtaleDirectImage B S hS f).map
          ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
            (moduleSetSheaf B S hS A M)) :=
  (Adjunction.unit_leftAdjointUniq_hom_app (smallToposMorphismTypeU B S hS f).adj
    (smallEtaleSetRestrictionAdjunction B S hS f hf) (moduleSetSheaf B S hS A M)).symm

/-- The unit of Stacks 03D3 on a section is the unit of the adjunction of the small étale topoi
on that section. -/
theorem inverseImageAdj_unit_val_app (f : D ⟶ A)
    (M : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS A.1)ᵒᵖ) (s : M.val.obj W) :
    ((smallToposMorphismTypeU B S hS f).adj.unit.app
        (moduleSetSheaf B S hS A M)).hom.app W s =
      (((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS A)).unit.app M).val.app W s) :=
  (Sheaf.hom_app_congr (moduleSheafFunctor_map_inverseImageAdj_unit_app B S hS f M).symm
      W s).trans
    (moduleSheafFunctor_map_hom_app _ W s)

/-! ### The direct image of the comparison of Stacks 03LQ, on a section -/

section SetStep

variable (f : D ⟶ A) (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS A.1 A.2)
  (W : (SmallEtale B S hS A.1)ᵒᵖ)

/-- **The direct image along `f` of the comparison of Stacks 03LQ, read on a section.**  It is
the direct image of Stacks 03D3 of the unit of the extension of scalars, followed by the direct
image of modules of the identification of Stacks 03LW, each read on that section.

The section is typed on the direct image of the sheaf of sets underlying the inverse image of
modules; that is the spelling in which neither step has to identify the two readings of the
source, each identification being paid once in
`CategoryTheory.Sheaf.map_hom_app_congr` and `CategoryTheory.Sheaf.map_comp_hom_app_apply`,
which are stated on variables. -/
theorem smallEtaleDirectImage_map_inverseImageIso_hom_app
    (z : ((smallEtaleDirectImage B S hS f).obj
      ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A))).obj
        ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A)).obj M))).obj.obj W) :
    ((smallEtaleDirectImage B S hS f).map
        ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj M))).hom.app W z =
      ((modulePushforward B S hS f).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).val.app W
        (((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).map
            ((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
                (structureRingSheaf B S hS A)).obj M))).val.app W z) :=
  (Sheaf.map_hom_app_congr (smallEtaleDirectImage B S hS f)
    (moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_app_comp B S hS f hf M).symm W
      z).trans
    (Sheaf.map_comp_hom_app_apply (smallEtaleDirectImage B S hS f) _ _ W z
      (smallEtaleDirectImage_map_moduleSheafFunctor_hom_app B S hS f _ W z)
      (smallEtaleDirectImage_map_moduleSheafFunctor_modulePushforward_hom_app B S hS f _ W _))

/-- The direct image of the comparison of Stacks 03LQ on a section, with the underlying sheaf
of sets of `M` written `AlgebraicGeometry.Space.moduleSetSheaf`. -/
private theorem setStep₃
    (z : ((smallEtaleDirectImage B S hS f).obj
      ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS A))).obj
        ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS A)).obj M))).obj.obj W) :
    ((smallEtaleDirectImage B S hS f).map
        ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
          (moduleSetSheaf B S hS A M))).hom.app W z =
      ((modulePushforward B S hS f).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).val.app W
        (((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS A)).map
            ((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
                (structureRingSheaf B S hS A)).obj M))).val.app W z) :=
  smallEtaleDirectImage_map_inverseImageIso_hom_app B S hS f hf M W z

/-- **The unit of étale restriction of modules is the unit of étale restriction of sheaves of
sets**, read on a section.

Both sides are read through the unit of the adjunction of the small étale topoi: on the module
side by `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_decomp` and
`AlgebraicGeometry.Space.inverseImageAdj_unit_val_app`, on the set side by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_app_eq_smallToposMorphismTypeU`,
and the two are joined by the direct image of the comparison of Stacks 03LQ.

`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnit.lean` is this same
identification for a *representable* `f`, proved there through the chart projection; this one
assumes no representability. -/
theorem etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction (s : M.val.obj W) :
    ((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app W s =
      ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (moduleSetSheaf B S hS A M)).hom.app W s :=
  ((Sheaf.hom_app_congr
        (smallEtaleSetRestrictionAdjunction_unit_app_eq_smallToposMorphismTypeU
          B S hS f hf M) W s).trans
    ((Sheaf.comp_hom_app_apply
          ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS A M))
          ((smallEtaleDirectImage B S hS f).map
            ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
              (moduleSetSheaf B S hS A M))) W s).trans
      ((Sheaf.hom_app_apply_congr
            ((smallEtaleDirectImage B S hS f).map
              ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
                (moduleSetSheaf B S hS A M))) W
            (inverseImageAdj_unit_val_app B S hS f M W s)).trans
        ((setStep₃ B S hS f hf M W _).trans
          (etaleModulePullbackAdjunction_unit_val_app_decomp B S hS f hf M W s).symm)))).symm

end SetStep

end AlgebraicGeometry.Space

end
