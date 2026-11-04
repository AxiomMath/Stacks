module

public import StacksFrontier.Algebra.Homology.SpectralSequence.CoreflectionGrothendieck
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RelativeLeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Leray spectral sequence for the quasi-coherent direct image

Let `f : 𝒳 → 𝒴` and `g : 𝒴 → 𝒵` be quasi-compact and quasi-separated morphisms of algebraic
stacks and let `ℱ` be a quasi-coherent `𝒪_𝒳`-module. **Stacks 0783** asserts the existence of a
spectral sequence

`E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)  ⟹  R^{p+q}(g ∘ f)_{QCoh,*} ℱ`.

The source's proof: the relative Leray spectral sequence `R^pg_*(R^qf_*ℱ) ⟹ R^{p+q}(g ∘ f)_*ℱ`
lies in `LQCoh^fbc(𝒪_𝒵)` from the second page on (Stacks 0771), so the exact functor `Q_𝒵` may be
applied to it (Stacks 0779 (3)); and the second page is identified because the kernel and the
cokernel of `Q_𝒴(R^qf_*ℱ) ⟶ R^qf_*ℱ` are parasitic (Stacks 0779 (2)) while `R^pg_*` carries
parasitic modules to parasitic modules (Stacks 0775 (2)) which `Q_𝒵` kills (Stacks 0779 (1)).

This file carries that argument out at algebraic stacks, at the module universe `u` of the
schemes, with each geometric input entering at one point:

* the direct images are any right adjoints of the inverse images of modules on the fppf sites
  (`AlgebraicGeometry.Stack.fppfModulesPullback`), so `(g ∘ f)_* ≅ f_* ⋙ g_*`
  (`AlgebraicGeometry.Stack.fppfModulesPushforwardCompIsoOfAdjunction`) and `f_*` preserves
  injectives (`AlgebraicGeometry.Stack.injective_obj_of_fppfModulesPullback_adjunction`);
* the spectral sequence is
  `CategoryTheory.Functor.exists_spectralSequence_rightDerived_comp_coreflection`, the
  Grothendieck spectral sequence read through the two coreflections onto the quasi-coherent
  modules.

## Main results

* `AlgebraicGeometry.Stack.exists_quasicoherentRelativeLeraySpectralSequence_of_coreflections`:
  the spectral sequence for any coreflections `i ⊣ Q` of `Mod(𝒪_𝒴)` and `Mod(𝒪_𝒵)` through weak
  Serre classes `L`, given the membership of the higher direct images in `L` and the parasitic
  description of the kernel of `Q`.
* `AlgebraicStacks.exists_quasicoherentRelativeLeraySpectralSequence_ofInputs`:
  the same for the canonical direct images and coherators, with `LQCoh^fbc` the corrected
  `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`; the inputs of Stacks 0771, 0778, 0779 and
  0775 are its hypotheses, each entering at one point.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentRelativeLeraySpectralSequence`:
  **Stacks 0783**, for quasi-compact and quasi-separated `f` and `g`, with those inputs proved.

## References

* [Stacks Project, Tag 0783](https://stacks.math.columbia.edu/tag/0783)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w v₁ u₁ v₂ u₂

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat enoughInjectives_fppfModules

/-- `AlgebraicGeometry.Stack.fppfModulesHigherDirectImage` unfolded. -/
lemma fppfModulesHigherDirectImage_eq_rightDerived {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (n : ℕ) :
    Stack.fppfModulesHigherDirectImage B S hS f n =
      (Stack.fppfModulesPushforward B S hS f).rightDerived n :=
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴 ⟶ 𝒵}
  {Pf : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒴}
  {Pg : fppfModules B S hS 𝒴 ⥤ fppfModules B S hS 𝒵}
  {Pfg : fppfModules B S hS 𝒳 ⥤ fppfModules B S hS 𝒵}
  [Pf.Additive] [Pg.Additive] [Pfg.Additive]
  {𝒬Y : Type u₁} [Category.{v₁} 𝒬Y] [Preadditive 𝒬Y]
  {𝒬Z : Type u₂} [Category.{v₂} 𝒬Z] [Abelian 𝒬Z]
  {iY : 𝒬Y ⥤ fppfModules B S hS 𝒴} {QY : fppfModules B S hS 𝒴 ⥤ 𝒬Y} [iY.Full] [iY.Faithful]
  [QY.Additive]
  {iZ : 𝒬Z ⥤ fppfModules B S hS 𝒵} {QZ : fppfModules B S hS 𝒵 ⥤ 𝒬Z} [iZ.Full] [iZ.Faithful]
  [QZ.Additive]
  {LY : ObjectProperty (fppfModules B S hS 𝒴)} [LY.IsWeakSerreClass]
  [PreservesFiniteColimits (LY.ι ⋙ QY)]
  {LZ : ObjectProperty (fppfModules B S hS 𝒵)} [LZ.IsWeakSerreClass]
  [PreservesFiniteColimits (LZ.ι ⋙ QZ)]

/-- **The relative Leray spectral sequence for the quasi-coherent direct image, through any
coreflections.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks with direct
images `f_*`, `g_*`, `(g ∘ f)_*` on fppf modules (right adjoints of the inverse images), let
`i_𝒴 ⊣ Q_𝒴` and `i_𝒵 ⊣ Q_𝒵` be coreflections of `Mod(𝒪_𝒴)` and `Mod(𝒪_𝒵)` landing in weak Serre
classes `L_𝒴`, `L_𝒵` on which `Q` is right exact, and let `M` be an `𝒪_𝒳`-module. Suppose

* `R^qf_* M` lies in `L_𝒴` (`hM`) and `R^pg_*` carries `L_𝒴` into `L_𝒵` (`hG`) — for the
  coherators these are Stacks 0771 (4)(b);
* an object of `L_𝒴` killed by `Q_𝒴` is parasitic (`hparY`), and a parasitic object of `L_𝒵` is
  killed by `Q_𝒵` (`hparZ`) — Stacks 0779 (1);
* `R^pg_*` carries parasitic modules to parasitic modules (`hpar`) — Stacks 0775 (2).

Then there is a spectral sequence of `𝒬_𝒵`, from the second page on, with

`E_2^{p,q} = Q_𝒵(R^pg_*(i_𝒴(Q_𝒴(R^qf_* M))))`, zero outside the first quadrant,

abutting to `Q_𝒵(R^n(g ∘ f)_* M)` (`n ≥ 0`). For `M = i_𝒳 ℱ` and the coherators this is
**Stacks 0783**. -/
theorem exists_quasicoherentRelativeLeraySpectralSequence_of_coreflections
    (adjf : fppfModulesPullback B S hS f ⊣ Pf) (adjg : fppfModulesPullback B S hS g ⊣ Pg)
    (adjfg : fppfModulesPullback B S hS (f ≫ g) ⊣ Pfg)
    (adjY : iY ⊣ QY) (hiY : ∀ X, LY (iY.obj X)) (adjZ : iZ ⊣ QZ) (hiZ : ∀ X, LZ (iZ.obj X))
    (M : fppfModules B S hS 𝒳) (hM : ∀ q : ℕ, LY ((Pf.rightDerived q).obj M))
    (hG : ∀ N, LY N → ∀ p : ℕ, LZ ((Pg.rightDerived p).obj N))
    (hparY : ∀ N, LY N → IsZero (QY.obj N) → IsParasitic B S hS 𝒴 .fppf N.val)
    (hparZ : ∀ N, LZ N → IsParasitic B S hS 𝒵 .fppf N.val → IsZero (QZ.obj N))
    (hpar : ∀ N : fppfModules B S hS 𝒴, IsParasitic B S hS 𝒴 .fppf N.val → ∀ p : ℕ,
      IsParasitic B S hS 𝒵 .fppf ((Pg.rightDerived p).obj N).val) :
    ∃ E : CohomologicalSpectralSequence 𝒬Z 2,
      (∀ p q : ℕ, Nonempty ((E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
        QZ.obj ((Pg.rightDerived p).obj (iY.obj (QY.obj ((Pf.rightDerived q).obj M)))))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q))) ∧
      SpectralSequence.AbutsTo E
        (extendNatByZero fun n => QZ.obj ((Pfg.rightDerived n).obj M)) :=
  Functor.exists_spectralSequence_rightDerived_comp_coreflection adjY LY hiY adjZ LZ hiZ Pf Pg
    Pfg (injective_obj_of_fppfModulesPullback_adjunction adjf)
    (fppfModulesPushforwardCompIsoOfAdjunction adjf adjg adjfg) M hM hG
    (fun N hN hQ p => hparZ _ (hG N hN p) (hpar N (hparY N hN hQ) p))

/-! ### The canonical direct images and coherators -/

section Canonical


namespace AlgebraicStacks

variable (B S hS) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (f g)
  (hsep𝒴 : HasSeparator (quasicoherentModules B S hS 𝒴))
  (hsep𝒵 : HasSeparator (quasicoherentModules B S hS 𝒵))
  [(lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).IsWeakSerreClass]
  [(lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒵).IsWeakSerreClass]
  [PreservesFiniteColimits
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coheratorOfSeparator B S hS 𝒴 hsep𝒴)]
  [PreservesFiniteColimits
    ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒵).ι ⋙ coheratorOfSeparator B S hS 𝒵 hsep𝒵)]

/-- **Stacks 0783 over its inputs, for the canonical quasi-coherent direct images.** Let
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks and `ℱ` a quasi-coherent
`𝒪_𝒳`-module. Given the inputs the source cites — `LQCoh^fbc` is a weak Serre class containing
`QCoh` on which the coherator is right exact (Stacks 0771 (2), 0778, 0779 (3)), the higher direct
images of `f` and `g` preserve `LQCoh^fbc` (Stacks 0771 (4)(b), `hDf`, `hDg`), the coherator kills
exactly the parasitic objects of `LQCoh^fbc` (Stacks 0779 (1), `hQ𝒴`, `hQ𝒵`) and the higher direct
images of `g` carry parasitic modules to parasitic modules (Stacks 0775 (2), `hpar`) — there is a
spectral sequence of `QCoh(𝒪_𝒵)` with

`E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)`, zero outside the first quadrant,

abutting to `R^n(g ∘ f)_{QCoh,*} ℱ`, the quasi-coherent higher direct images being
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageOfSeparator` and the
abelian structure of `QCoh(𝒪_𝒵)` the one of
`AlgebraicGeometry.Stack.AlgebraicStacks.abelianQuasicoherentModulesOfInputs`. -/
theorem exists_quasicoherentRelativeLeraySpectralSequence_ofInputs
    (hi𝒳 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      ((quasicoherentInclusion B S hS 𝒳).obj M))
    (hi𝒴 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
      ((quasicoherentInclusion B S hS 𝒴).obj M))
    (hi𝒵 : ∀ M, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒵
      ((quasicoherentInclusion B S hS 𝒵).obj M))
    (hDf : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F → ∀ n,
      lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
        ((Stack.fppfModulesHigherDirectImage B S hS f n).obj F))
    (hDg : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 F → ∀ n,
      lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒵
        ((Stack.fppfModulesHigherDirectImage B S hS g n).obj F))
    (hQ𝒴 : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 F →
      (IsZero ((coheratorOfSeparator B S hS 𝒴 hsep𝒴).obj F) ↔
        IsParasitic B S hS 𝒴 .fppf F.val))
    (hQ𝒵 : ∀ F, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒵 F →
      (IsZero ((coheratorOfSeparator B S hS 𝒵 hsep𝒵).obj F) ↔
        IsParasitic B S hS 𝒵 .fppf F.val))
    (hpar : ∀ N : Stack.fppfModules B S hS 𝒴, IsParasitic B S hS 𝒴 .fppf N.val → ∀ n : ℕ,
      IsParasitic B S hS 𝒵 .fppf ((Stack.fppfModulesHigherDirectImage B S hS g n).obj N).val)
    (ℱ : quasicoherentModules B S hS 𝒳) :
    letI := abelianQuasicoherentModulesOfInputs B S hS E h hsep𝒵 hi𝒵
    ∃ E : CohomologicalSpectralSequence (quasicoherentModules B S hS 𝒵) 2,
      (∀ p q : ℕ, Nonempty ((E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
        (quasicoherentHigherDirectImageOfSeparator B S hS g hsep𝒵 p).obj
          ((quasicoherentHigherDirectImageOfSeparator B S hS f hsep𝒴 q).obj ℱ))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q))) ∧
      SpectralSequence.AbutsTo E (extendNatByZero fun n =>
        (quasicoherentHigherDirectImageOfSeparator B S hS (f ≫ g) hsep𝒵 n).obj ℱ) := by
  let := abelianQuasicoherentModulesOfInputs B S hS E h hsep𝒵 hi𝒵
  let := (coheratorAdjunctionOfSeparator B S hS 𝒴 hsep𝒴).right_adjoint_additive
  let := (coheratorAdjunctionOfSeparator B S hS 𝒵 hsep𝒵).right_adjoint_additive
  have key := exists_quasicoherentRelativeLeraySpectralSequence_of_coreflections
    (Stack.fppfModulesPullbackPushforwardAdjunction B S hS f)
    (Stack.fppfModulesPullbackPushforwardAdjunction B S hS g)
    (Stack.fppfModulesPullbackPushforwardAdjunction B S hS (f ≫ g))
    (coheratorAdjunctionOfSeparator B S hS 𝒴 hsep𝒴) hi𝒴
    (coheratorAdjunctionOfSeparator B S hS 𝒵 hsep𝒵) hi𝒵
    ((quasicoherentInclusion B S hS 𝒳).obj ℱ)
    (fun q => by
      have h := hDf _ (hi𝒳 ℱ) q
      rw [fppfModulesHigherDirectImage_eq_rightDerived] at h
      exact h)
    (fun N hN p => by
      have h := hDg N hN p
      rw [fppfModulesHigherDirectImage_eq_rightDerived] at h
      exact h)
    (fun N hN => (hQ𝒴 N hN).1) (fun N hN => (hQ𝒵 N hN).2)
    (fun N hN p => by
      have h := hpar N hN p
      rw [fppfModulesHigherDirectImage_eq_rightDerived] at h
      exact h)
  obtain ⟨E, h2, hz, hab⟩ := key
  refine ⟨E, fun p q => ?_, hz, ?_⟩
  · simp only [quasicoherentHigherDirectImageOfSeparator, Functor.comp_obj,
      fppfModulesHigherDirectImage_eq_rightDerived]
    exact h2 p q
  · simp only [quasicoherentHigherDirectImageOfSeparator, Functor.comp_obj,
      fppfModulesHigherDirectImage_eq_rightDerived]
    exact hab

end AlgebraicStacks

end Canonical

/-! ### Stacks 0783 -/

section Tag

namespace AlgebraicStacks

variable (B S hS) (f g)

/-- **Stacks 0783: the relative Leray spectral sequence for the quasi-coherent direct image.**
Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be quasi-compact and quasi-separated 1-morphisms of algebraic
stacks and let `ℱ` be a quasi-coherent `𝒪_𝒳`-module. There is a spectral sequence of
quasi-coherent `𝒪_𝒵`-modules, from its second page on, with

`E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} ℱ)`

(zero outside the first quadrant) converging to `R^{p+q}(g ∘ f)_{QCoh,*} ℱ`: it abuts to
`n ↦ R^n(g ∘ f)_{QCoh,*} ℱ`, zero in negative degrees. Here `R^i (-)_{QCoh,*}` is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`, the composite
`Q ∘ R^i(-)_* ∘ i` of **Stacks 077A**, and `QCoh(𝒪_𝒵)` carries its abelian structure
`AlgebraicGeometry.Stack.AlgebraicStacks.instAbelianQuasicoherentModules`; modules have sections
in the universe `u` of the schemes.

The proof is the source's: the Grothendieck spectral sequence of `(g ∘ f)_* = g_* ∘ f_*` on fppf
modules (Stacks 0734 for stacks), pushed along the coherator `Q_𝒵`, which is exact on
`LQCoh^fbc(𝒪_𝒵)` (Stacks 0779 (3)) where all of its terms lie from the second page on
(Stacks 0771 (2), (4)(b)); the second page is identified through the counit
`Q_𝒴(R^q f_*ℱ) ⟶ R^q f_*ℱ`, whose kernel and cokernel are parasitic (Stacks 0779 (1)), hence
carried by `R^p g_*` to parasitic modules (Stacks 0775 (2)) which `Q_𝒵` kills. -/
@[stacks 0783 "the spectral sequence E_2^{p,q} = R^p g_{QCoh,*}(R^q f_{QCoh,*} F) converging to \
  R^{p+q}(g ∘ f)_{QCoh,*} F for qcqs morphisms of algebraic stacks, modules at the universe u of \
  the schemes"]
theorem exists_quasicoherentRelativeLeraySpectralSequence
    (hfqc : IsQuasiCompactMorphism B S hS f) (hfqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hgqc : IsQuasiCompactMorphism B S hS g) (hgqs : AlgebraicStacks.IsQuasiSeparated B S hS g)
    (ℱ : quasicoherentModules B S hS 𝒳) :
    ∃ E : CohomologicalSpectralSequence (quasicoherentModules B S hS 𝒵) 2,
      (∀ p q : ℕ, Nonempty ((E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
        (quasicoherentHigherDirectImage B S hS g p).obj
          ((quasicoherentHigherDirectImage B S hS f q).obj ℱ))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q))) ∧
      SpectralSequence.AbutsTo E (extendNatByZero fun n =>
        (quasicoherentHigherDirectImage B S hS (f ≫ g) n).obj ℱ) :=
  haveI := (preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator
    B S hS 𝒴 (associatedBigEtaleSite B) rfl).2
  haveI := (preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator
    B S hS 𝒵 (associatedBigEtaleSite B) rfl).2
  exists_quasicoherentRelativeLeraySpectralSequence_ofInputs B S hS f g
    (associatedBigEtaleSite B) rfl
    (hasSeparator_quasicoherentModules B S hS 𝒴) (hasSeparator_quasicoherentModules B S hS 𝒵)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B (associatedBigEtaleSite B) rfl S hS 𝒳)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B (associatedBigEtaleSite B) rfl S hS 𝒴)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B (associatedBigEtaleSite B) rfl S hS 𝒵)
    (fun F hF n => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B
      (associatedBigEtaleSite B) rfl S hS f hfqc hfqs F hF n)
    (fun F hF n => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B
      (associatedBigEtaleSite B) rfl S hS g hgqc hgqs F hF n)
    (isZero_coherator_obj_iff_isParasitic B S hS 𝒴 (associatedBigEtaleSite B) rfl)
    (isZero_coherator_obj_iff_isParasitic B S hS 𝒵 (associatedBigEtaleSite B) rfl)
    (fun N hN n => isParasitic_fppfModulesHigherDirectImage g N hN n) ℱ

end AlgebraicStacks

end Tag

end AlgebraicGeometry.Stack

end
