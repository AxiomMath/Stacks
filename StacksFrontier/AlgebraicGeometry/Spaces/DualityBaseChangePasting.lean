module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangePasting

/-!
# Pasting of base change maps on the quasi-coherent derived categories of algebraic spaces

The composition law of derived pullbacks (Stacks 0D6D) and the composition isomorphism of derived
direct images restrict to the quasi-coherent derived categories `D_QCoh`, and the pasting laws of
Stacks 0E46 and 0E47 for the base change map of Stacks 07A7 hold there. These are the inputs of
Stacks 0E5E and 0E5F.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedModulePullbackCompIso`: `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`
  on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPushforwardCompIso`: `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
  on `D_QCoh`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedBaseChange_vertical`: Stacks 0E46 on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedBaseChange_horizontal`: Stacks 0E47 on `D_QCoh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Composition

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The composition law of derived pullbacks (Stacks 0D6D), restricted to `D_QCoh`. -/
def quasicoherentDerivedModulePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    quasicoherentDerivedModulePullback g ⋙ quasicoherentDerivedModulePullback f ≅
      quasicoherentDerivedModulePullback (f ≫ g) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((smallEtaleDerivedModulePullbackCompIso B S hS f g).app K.obj))
    (fun φ => ObjectProperty.hom_ext _
      ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.naturality φ.hom))

/-- The component of `quasicoherentDerivedModulePullbackCompIso` at `K` is the component of
`smallEtaleDerivedModulePullbackCompIso` at the underlying complex of `K`. -/
@[simp]
theorem quasicoherentDerivedModulePullbackCompIso_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) (K) :
    ((quasicoherentDerivedModulePullbackCompIso f g).hom.app K).hom =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app K.obj := rfl

/-- The component of the inverse of `quasicoherentDerivedModulePullbackCompIso` at `K` is the
component of the inverse of `smallEtaleDerivedModulePullbackCompIso` at the underlying complex
of `K`. -/
@[simp]
theorem quasicoherentDerivedModulePullbackCompIso_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) (K) :
    ((quasicoherentDerivedModulePullbackCompIso f g).inv.app K).hom =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv.app K.obj := rfl

/-- The composition isomorphism of derived direct images, restricted to `D_QCoh`. -/
def quasicoherentDerivedPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hfgqc : IsQuasiCompact B S hS (f ≫ g).hom) (hfgqs : IsQuasiSeparated B S hS (f ≫ g).hom) :
    quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙
        quasicoherentDerivedPushforward B S hS g hgqc hgqs ≅
      quasicoherentDerivedPushforward B S hS (f ≫ g) hfgqc hfgqs :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).app K.obj))
    (fun φ => ObjectProperty.hom_ext _
      ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).hom.naturality φ.hom))

/-- The component of `quasicoherentDerivedPushforwardCompIso` at `K` is the component of
`smallEtaleDerivedPushforwardCompIsoToposHom` at the underlying complex of `K`. -/
@[simp]
theorem quasicoherentDerivedPushforwardCompIso_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfqc hfqs hgqc hgqs hfgqc hfgqs) (K) :
    ((quasicoherentDerivedPushforwardCompIso f g hfqc hfqs hgqc hgqs hfgqc hfgqs).hom.app K).hom =
      (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).hom.app K.obj := rfl

/-- The component of the inverse of `quasicoherentDerivedPushforwardCompIso` at `K` is the
component of the inverse of `smallEtaleDerivedPushforwardCompIsoToposHom` at the underlying
complex of `K`. -/
@[simp]
theorem quasicoherentDerivedPushforwardCompIso_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfqc hfqs hgqc hgqs hfgqc hfgqs) (K) :
    ((quasicoherentDerivedPushforwardCompIso f g hfqc hfqs hgqc hgqs hfgqc hfgqs).inv.app K).hom =
      (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f g).inv.app K.obj := rfl

end Composition

section Vertical

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y')
  (g' : Y' ⟶ Z') (k : X' ⟶ X) (l : Y' ⟶ Y) (m : Z' ⟶ Z)
  (wtop : k ≫ f = f' ≫ l) (wbot : l ≫ g = g' ≫ m)
  (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
  (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
  (hfgqc : IsQuasiCompact B S hS (f ≫ g).hom) (hfgqs : IsQuasiSeparated B S hS (f ≫ g).hom)
  (hf'qc : IsQuasiCompact B S hS f'.hom) (hf'qs : IsQuasiSeparated B S hS f'.hom)
  (hg'qc : IsQuasiCompact B S hS g'.hom) (hg'qs : IsQuasiSeparated B S hS g'.hom)
  (hfg'qc : IsQuasiCompact B S hS (f' ≫ g').hom)
  (hfg'qs : IsQuasiSeparated B S hS (f' ≫ g').hom)

/-- **Stacks 0E46 on `D_QCoh`.** The base change map of the outer rectangle of two vertically
composable commutative squares is the vertical paste of those of the two squares. -/
theorem quasicoherentDerivedBaseChange_vertical (K) :
    (quasicoherentDerivedBaseChange (f ≫ g) m (f' ≫ g') k
        (comp_stack B S hS f g f' g' k l m wtop wbot) hfgqc hfgqs hfg'qc hfg'qs).app K =
      (quasicoherentDerivedModulePullback m).map
          ((quasicoherentDerivedPushforwardCompIso f g hfqc hfqs hgqc hgqs hfgqc hfgqs).inv.app
            K) ≫
        (quasicoherentDerivedBaseChange g m g' l wbot hgqc hgqs hg'qc hg'qs).app
          ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ≫
        (quasicoherentDerivedPushforward B S hS g' hg'qc hg'qs).map
          ((quasicoherentDerivedBaseChange f l f' k wtop hfqc hfqs hf'qc hf'qs).app K) ≫
        (quasicoherentDerivedPushforwardCompIso f' g' hf'qc hf'qs hg'qc hg'qs hfg'qc
          hfg'qs).hom.app ((quasicoherentDerivedModulePullback k).obj K) :=
  ObjectProperty.hom_ext _
    (smallEtaleDerivedBaseChangeMap_vertical B S hS f g f' g' k l m wtop wbot K.obj).symm

end Vertical

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (f'' : X'' ⟶ Y'') (g' : X' ⟶ X) (g'' : X'' ⟶ X') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
  (w : g' ≫ f = f' ≫ g) (w' : g'' ≫ f' = f'' ≫ h)
  (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
  (hf'qc : IsQuasiCompact B S hS f'.hom) (hf'qs : IsQuasiSeparated B S hS f'.hom)
  (hf''qc : IsQuasiCompact B S hS f''.hom) (hf''qs : IsQuasiSeparated B S hS f''.hom)

/-- **Stacks 0E47 on `D_QCoh`.** The base change map of the outer rectangle of two horizontally
composable commutative squares is the horizontal paste of those of the two squares. -/
theorem quasicoherentDerivedBaseChange_horizontal (K) :
    (quasicoherentDerivedBaseChange f (h ≫ g) f'' (g'' ≫ g')
        (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' f'' g' g'' g h w w')
        hfqc hfqs hf''qc hf''qs).app K =
      (quasicoherentDerivedModulePullbackCompIso h g).inv.app
          ((quasicoherentDerivedPushforward B S hS f hfqc hfqs).obj K) ≫
        (quasicoherentDerivedModulePullback h).map
          ((quasicoherentDerivedBaseChange f g f' g' w hfqc hfqs hf'qc hf'qs).app K) ≫
        (quasicoherentDerivedBaseChange f' h f'' g'' w' hf'qc hf'qs hf''qc hf''qs).app
          ((quasicoherentDerivedModulePullback g').obj K) ≫
        (quasicoherentDerivedPushforward B S hS f'' hf''qc hf''qs).map
          ((quasicoherentDerivedModulePullbackCompIso g'' g').hom.app K) :=
  ObjectProperty.hom_ext _
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f' f'' g' g'' g h w w' K.obj).symm

end Horizontal

end AlgebraicGeometry.Space

end
