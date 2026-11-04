module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Fraction
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.AffineOpenHomRecovery
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Laurent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparison
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleBimodule

/-!
# The comparison `ℳ̃_T ≅ h^*ℳ̃` on one chart: the data

Property (1) of [Stacks, Tag 01O7] is a canonical isomorphism `ℳ̃_T ≅ h^*ℳ̃` for the morphism `h`
a quadruple `(f : T → S, d, L, ψ)` classifies, `ℳ̃_T` being the module of [Stacks, Tag 01O6]. It
is built locally on `T`, over the opens on which `f` lands in an affine open `U` of the base and
`ψ(c)` trivializes `L` for a section `c` of `𝒜_d` over `U`; on such an open `h` factors through the
standard open `D₊(c)` of the chart `Proj 𝒜(U)` by a morphism `g`, and `h^*ℳ̃` is `g^*` of the
sheaf `ℳ̃(U)` attached to the graded module of sections of `ℳ` over `U`.

This file fixes the data of that local situation and builds the degreewise pieces of the
comparison:

* the morphism `β_m : f^*ℳ_{md} ⟶ g^*ℳ̃(U)` carrying the pullback of a section `x` of `ℳ_{md}`
  over `U` to the pullback of the fraction `x / c^m`, produced by the recovery of a morphism out of
  a pullback from its effect on sections over an affine open;
* the trivializations of the integral tensor powers `L^{⊗ (-m)}` by the powers of a unit `w` of
  degree one of the ring of global sections of the Laurent algebra, which in the application is
  `ψ(c)`.

The two hypotheses tying `g` to the quadruple are the *chart identity* `hCP`, that `ψ` sends a
section `a` of `𝒜_{id}` over `U` to `g^♯(a / c^i) · w^i`, and the base identity `hgf`, that `g`
lies over `f` on the functions of `U`. They are what [Stacks, Tag 01N8] says of the classifying
morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation
open Stacks.AlgebraicGeometry.AffineOpenHomRecovery (pullbackSection_add pullbackSection_smul)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing
attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

/-! ### The local situation -/

section Chart

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  (U : s.base.affineOpens) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))

/-- The degree-zero fraction `r / 1` of a function `r` on `U`. -/
abbrev baseFrac (r : s.base.ringCatSheaf.obj.obj (op U.1)) :
    HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c) :=
  HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1) (cHom_mem U.1 c) 0
    (s.sectionRingBaseMap U.1 r) (by simpa using sectionRingBaseMap_mem_zero s U.1 r)

/-- **The fraction `x / c^m`, as a section of `ℳ̃(U)` over `D₊(c)`.** -/
abbrev fracSec (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)) :
    moduleSections (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1)
      (ProjectiveSpectrum.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) :=
  degreeZeroToSection (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1) (cHom U.1 c)
    (fracElt ℳ U.1 c m x)

/-- The fraction `(r • x) / c^m` is `(r / 1) • (x / c^m)` for a function `r` on `U`. -/
theorem fracSec_smul_base (m : ℤ) (r : s.base.ringCatSheaf.obj.obj (op U.1))
    (x : sectionModulePieces ℳ U.1 (m * d)) :
    fracSec ℳ U c m (r • x) = baseFrac U c r • fracSec ℳ U c m x :=
  (congrArg (degreeZeroToSection (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1)
    (cHom U.1 c)) (fracElt_smul_base ℳ U.1 c m r x)).trans (map_smul _ _ _)

/-- The fraction `x / c^m`, as an additive map into the degree-zero localization. -/
def fracEltHom (m : ℤ) : sectionModulePieces ℳ U.1 (m * d) →+ Loc ℳ U.1 c where
  toFun := fracElt ℳ U.1 c m
  map_zero' := fracElt_zero ℳ U.1 c m
  map_add' := fracElt_add ℳ U.1 c m

/-- The fraction map onto the sections of `ℳ̃(U)` over `D₊(c)`. -/
def toChart : Loc ℳ U.1 c →+
    (moduleChart ℳ U).val.obj (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) :=
  (degreeZeroToSection (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1)
    (cHom U.1 c)).toAddMonoidHom

/-- **The fraction `x / c^m`, as a section of the chart sheaf `ℳ̃(U)` over `D₊(c)`.** -/
def fracChart (m : ℤ) : sectionModulePieces ℳ U.1 (m * d) →+
    (moduleChart ℳ U).val.obj (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) :=
  (toChart ℳ U c).comp (fracEltHom ℳ U c m)

/-- `fracChart` is the fraction `x / c^m` in the degree-zero localization, mapped by `toChart`. -/
theorem fracChart_eq (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)) :
    fracChart ℳ U c m x = toChart ℳ U c (fracElt ℳ U.1 c m x) :=
  AddMonoidHom.comp_apply _ _ _

/-- The pullback of sections along `g`, as an additive map. -/
def pullbackSectionHom {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (V : X.Opens)
    (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ V) :
    F.val.obj (op V) →+ ((Scheme.Modules.pullback g).obj F).val.obj (op W) where
  toFun := Scheme.Modules.pullbackSection g F V W h
  map_zero' := by
    unfold Scheme.Modules.pullbackSection
    rw [map_zero]
    exact map_zero (((Scheme.Modules.pullback g).obj F).val.map (homOfLE h).op).hom
  map_add' := pullbackSection_add g F V W h

/-- **The pulled-back fraction `g^*(x / c^m)`**, as a global section of `g^*ℳ̃(U)`. -/
def fracPull (m : ℤ) : sectionModulePieces ℳ U.1 (m * d) →+
    ((Scheme.Modules.pullback g).obj (moduleChart ℳ U)).val.obj (op ⊤) :=
  (pullbackSectionHom g (moduleChart ℳ U) _ ⊤ hg).comp (fracChart ℳ U c m)

/-- **The fraction is linear over the functions on `U`**, which act on `D₊(c)` through `r / 1`. -/
theorem fracChart_smul_base (m : ℤ) (r : s.base.ringCatSheaf.obj.obj (op U.1))
    (x : sectionModulePieces ℳ U.1 (m * d)) :
    fracChart ℳ U c m (r • x) =
      (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) from
        Proj.awayToSection _ _ (baseFrac U c r)) • fracChart ℳ U c m x :=
  fracSec_smul_base ℳ U c m r x

/-- `fracPull` is the pullback along `g` of the section `fracChart` of `ℳ̃(U)` over `D₊(c)`. -/
theorem fracPull_apply (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)) :
    fracPull ℳ U c g hg m x =
      Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg (fracChart ℳ U c m x) :=
  AddMonoidHom.comp_apply _ _ _

/-- **The pulled-back fraction is linear over the functions on `U`**, given that `g` lies over
`f` on those functions. -/
theorem fracPull_smul_base
    (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
      f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
    (m : ℤ) (r : s.base.ringCatSheaf.obj.obj (op U.1)) (x : sectionModulePieces ℳ U.1 (m * d)) :
    fracPull ℳ U c g hg m (r • x) =
      (show T.ringCatSheaf.obj.obj (op ⊤) from f.appLE U.1 ⊤ hf r) • fracPull ℳ U c g hg m x := by
  rw [hgf r]
  exact (congrArg (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg)
    (fracChart_smul_base ℳ U c m r x)).trans (pullbackSection_smul g _ _ ⊤ hg _ _)

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))

/-- **The degree-`m` comparison `β_m : f^*ℳ_{md} ⟶ g^*ℳ̃(U)`**, the morphism carrying the
pullback of a section `x` of `ℳ_{md}` over `U` to the pullback of the fraction `x / c^m`. -/
def beta (m : ℤ) :
    (Scheme.Modules.pullback f).obj (ℳ.piece (m * d)) ⟶
      (Scheme.Modules.pullback g).obj (moduleChart ℳ U) :=
  AffineOpenHomRecovery.homOfSections f U.1 hf (ℳ.piece (m * d)) U.2
    ((Scheme.Modules.pullback g).obj (moduleChart ℳ U)) (fracPull ℳ U c g hg m)
    (fun r x => fracPull_smul_base ℳ U c f hf g hg hgf m r x)

/-- The morphism `β_m` carries the pullback along `f` of a section `x` of `ℳ_{md}` over `U` to
the pulled-back fraction `g^*(x / c^m)`. -/
theorem beta_pullbackSection (m : ℤ) (x : sectionModulePieces ℳ U.1 (m * d)) :
    (beta ℳ U c f hf g hg hgf m).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f (ℳ.piece (m * d)) U.1 ⊤ hf x) =
      fracPull ℳ U c g hg m x :=
  AffineOpenHomRecovery.homOfSections_pullbackSection f U.1 hf (ℳ.piece (m * d)) U.2
    ((Scheme.Modules.pullback g).obj (moduleChart ℳ U)) (fracPull ℳ U c g hg m)
    (fun r x => fracPull_smul_base ℳ U c f hf g hg hgf m r x) x

end Chart

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
