module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf

/-!
# Higher direct images of `LQCoh^fbc` in the fppf and the étale topology (Stacks 0771 (4))

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and `F` an
object of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`. Write `ε_* : Mod(𝒪_𝒳) ⥤ Mod(𝒳_étale, 𝒪_𝒳)` for reading an
fppf module on the étale site and `ε^*` for its left adjoint, fppf sheafification. **Stacks 0771**
part (4) says

* (a) the higher direct images `Rⁱf_*F` can be computed in either the étale or the fppf topology
  with the same result, and
* (b) each `Rⁱf_*F` is an object of `LQCoh^fbc(𝒪_𝒴)`.

The étale reading of (b) is
`AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule_stackModuleHigherDirectImage`. Here:

* `AlgebraicGeometry.Stack.nonempty_etaleComparison_fppfModulesHigherDirectImage_iso`, part (a):
  `ε_*(Rⁱf_{fppf,*}F) ≅ Rⁱf_{ét,*}(ε_*F)`;
* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage`, part (b) in
  `Mod(𝒪_𝒴)`: `Rⁱf_{fppf,*}F ∈ LQCoh^fbc(𝒪_𝒴)`.

The proof is the source's. By **Stacks 075R** (3)
(`AlgebraicGeometry.Stack.nonempty_rightDerived_stackModuleDirectImage_iso_of_lqcohSheafFbc`),
`Rⁱf_{fppf,*}F ≅ ε^*(Rⁱf_{ét,*}(ε_*F))`. The étale higher direct image `G = Rⁱf_{ét,*}(ε_*F)` is in
`LQCoh^fbc` by part (b) in the étale topology, so it is an fppf sheaf (**Stacks 0771** part (1)),
that is `G = ε_*M` for an fppf module `M` in `LQCoh^fbc`; then `ε^*G = M` and `ε_*ε^*G = G`.

The total direct image `Rf_*` of part (a), on bounded below derived categories, is
`AlgebraicGeometry.Stack.lqcohSheafFbcTotalDirectImageIso` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LqcohSheafFbcTotalDirectImage.lean`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- A module of `LQCoh^fbc` on the étale site of an algebraic stack is `ε_*` of a module of
`LQCoh^fbc(𝒪_𝒳)` on the fppf site: its underlying presheaf is an fppf sheaf (**Stacks 0771**
part (1)). -/
theorem imageOfLE_lqcohSheafFbcFppfModules_of_lqcohSheafFbcEtaleModules
    {𝒴 : AlgebraicStacks.{u, t} B S hS} (G : StackModules B S hS .etale 𝒴)
    (hG : lqcohSheafFbcEtaleModules.{u, t, u} B E h S hS 𝒴 G) :
    Stacks.Cohomology.CompareTopologies.imageOfLE
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale)
      (fppfSiteRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)
      (lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴) G :=
  ⟨(fppfModuleOfLqcohSheafFbc B E h S hS 𝒴 G hG).obj,
    (fppfModuleOfLqcohSheafFbc B E h S hS 𝒴 G hG).property, ⟨Iso.refl _⟩⟩

/-- `ε^*` carries `LQCoh^fbc` of the étale site into `LQCoh^fbc(𝒪_𝒴)`. -/
theorem lqcohSheafFbcFppfModules_stackModulesEtaleComparisonPullback
    {𝒴 : AlgebraicStacks.{u, t} B S hS} (G : StackModules B S hS .etale 𝒴)
    (hG : lqcohSheafFbcEtaleModules.{u, t, u} B E h S hS 𝒴 G) :
    lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴
      ((stackModulesEtaleComparisonPullback B S hS 𝒴).obj G) :=
  Stacks.Cohomology.CompareTopologies.prop_pullback_obj
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale)
    (fppfSiteRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)
    (lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴) inferInstance
    (imageOfLE_lqcohSheafFbcFppfModules_of_lqcohSheafFbcEtaleModules B E h S hS G hG)

/-- **Stacks 075R (3)**, read with the higher direct images of
`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage`:
`Rⁱf_{fppf,*}F ≅ ε^*(Rⁱf_{ét,*}(ε_*F))` for `F` in `LQCoh^fbc(𝒪_𝒳)`. -/
theorem nonempty_fppfModulesHigherDirectImage_iso_of_lqcohSheafFbc
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    (i : ℕ) : Nonempty ((fppfModulesHigherDirectImage B S hS f i).obj F ≅
      (stackModulesEtaleComparisonPullback B S hS 𝒴).obj
        ((stackModuleHigherDirectImage B S hS f .etale i).obj
          ((stackModulesEtaleComparison B S hS 𝒳).obj F))) :=
  nonempty_rightDerived_stackModuleDirectImage_iso_of_lqcohSheafFbc B S hS E h 𝒳 f F hF i

/-- **Stacks 0771, part (4)(b)**, in `Mod(𝒪_𝒴)`. Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks and `F` an object of `LQCoh^fbc(𝒪_𝒳)`. Then each
higher direct image `Rⁱf_*F`, computed in the fppf topology, is an object of `LQCoh^fbc(𝒪_𝒴)`.

Modules have sections in the universe `u` of the schemes; local quasi-coherence is read against
an auxiliary big étale site `E` with `E.cutoff = B.cutoff`, and the flat base change property is
the sheaf-level one of **Stacks 0762**. -/
@[stacks 0771 "part (4)(b), in Mod(𝒪_𝒴): for f quasi-compact and quasi-separated, each \
  R^i f_*F computed in the fppf topology lies in LQCoh^fbc(𝒪_𝒴), with the flat base change \
  property of 0762 read on sheaves; modules at the module universe u of the schemes"]
theorem lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    (i : ℕ) :
    lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴
      ((fppfModulesHigherDirectImage B S hS f i).obj F) := by
  obtain ⟨e⟩ := nonempty_fppfModulesHigherDirectImage_iso_of_lqcohSheafFbc B E h S hS f F hF i
  exact (lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴).prop_of_iso e.symm
    (lqcohSheafFbcFppfModules_stackModulesEtaleComparisonPullback B E h S hS _
      (lqcohSheafFbcModuleRule_stackModuleHigherDirectImage B E h S hS f hqc hqs
        ((stackModulesEtaleComparison B S hS 𝒳).obj F) hF i))

/-- **Stacks 0771, part (4)(a)**, for the higher direct images. Let `f : 𝒳 ⟶ 𝒴` be a
quasi-compact and quasi-separated 1-morphism of algebraic stacks and `F` an object of
`LQCoh^fbc(𝒪_𝒳)`. Then `Rⁱf_*F` is the same whether computed in the étale or in the fppf
topology: `ε_*(Rⁱf_{fppf,*}F) ≅ Rⁱf_{ét,*}(ε_*F)`, where `ε_*` reads an fppf module on the étale
site.

Modules have sections in the universe `u` of the schemes. The assertion of the source about the
total direct image `Rf_*` is `AlgebraicGeometry.Stack.lqcohSheafFbcTotalDirectImageIso`. -/
@[stacks 0771 "part (4)(a), for the higher direct images: ε_*(R^i f_{fppf,*}F) ≅ \
  R^i f_{ét,*}(ε_*F) for f quasi-compact and quasi-separated and F in LQCoh^fbc, modules at the \
  module universe u of the schemes; the total direct image Rf_* is \
  lqcohSheafFbcTotalDirectImageIso"]
theorem nonempty_etaleComparison_fppfModulesHigherDirectImage_iso
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    (i : ℕ) :
    Nonempty ((stackModulesEtaleComparison B S hS 𝒴).obj
        ((fppfModulesHigherDirectImage B S hS f i).obj F) ≅
      (stackModuleHigherDirectImage B S hS f .etale i).obj
        ((stackModulesEtaleComparison B S hS 𝒳).obj F)) := by
  obtain ⟨e⟩ := nonempty_fppfModulesHigherDirectImage_iso_of_lqcohSheafFbc B E h S hS f F hF i
  have hG := lqcohSheafFbcModuleRule_stackModuleHigherDirectImage B E h S hS f hqc hqs
    ((stackModulesEtaleComparison B S hS 𝒳).obj F) hF i
  have := Stacks.Cohomology.CompareTopologies.isIso_unit_app_of_imageOfLE
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale)
    (fppfSiteRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)
    (lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒴)
    (imageOfLE_lqcohSheafFbcFppfModules_of_lqcohSheafFbcEtaleModules B E h S hS _ hG)
  exact ⟨(stackModulesEtaleComparison B S hS 𝒴).mapIso e ≪≫
    (asIso ((Stacks.Cohomology.CompareTopologies.adjunction
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale)
      (fppfSiteRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)).unit.app
        ((stackModuleHigherDirectImage B S hS f .etale i).obj
          ((stackModulesEtaleComparison B S hS 𝒳).obj F)))).symm⟩

end AlgebraicGeometry.Stack
