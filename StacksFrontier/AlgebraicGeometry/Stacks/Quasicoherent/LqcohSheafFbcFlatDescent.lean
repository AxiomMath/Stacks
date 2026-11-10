module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModuleRuleFlatLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcDirectImageAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf

/-!
# `LQCoh^fbc` is local for smooth and for flat, locally finitely presented families (Stacks 07AQ)

Let `𝒳` be an algebraic stack and `f j : 𝒵 j ⟶ 𝒳` a family of 1-morphisms of algebraic stacks
whose images cover `|𝒳|`. **Stacks 07AQ** says that a module `F` on `𝒳` lies in
`LQCoh^fbc(𝒪_𝒳)` as soon as every `f j^* F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, in two settings:

1. the `f j` are smooth and `F` is a sheaf of `𝒪_𝒳`-modules on `𝒳_ét`;
2. the `f j` are flat and locally of finite presentation and `F` is a sheaf of `𝒪_𝒳`-modules on
   `𝒳_fppf`.

Both are stated for the sheaf-level `LQCoh^fbc` of the library
(`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules`,
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`), whose flat base change property is that of
**Stacks 0762**, with module sections in the universe of the schemes.

## The proofs

Part (1) is the combination the source names: local quasi-coherence descends along the smooth
family by **Stacks 075Y**
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective`), and the flat
base change property by **Stacks 0764** (3)
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective`). The only
glue is that the inverse image of sheaves of modules has, as underlying presheaf, the presheaf
inverse image those two results are stated with
(`isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback_of_modulePullback`).

Part (2) is the instance at `LQCoh^fbc` of the rule-generic reduction
`AlgebraicGeometry.Stack.mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective`, whose
inputs are: closure under isomorphisms and equalizers (**Stacks 0771** (2)), under inverse images
(**Stacks 0771** (3)), under direct images along 1-morphisms of algebraic stacks representable by
affine schemes (the case of **Stacks 0771** (4)(b), in degree `0`, the proof uses:
`lqcohSheafFbcFppfModules_fppfModulesPushforward_of_isAffineRepresentable`), and locality along
smooth families, which is the fppf form of part (1).

## Main results

* `AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules_of_isSmooth_jointlySurjective`:
  **Stacks 07AQ** part (1).
* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_of_isSmooth_jointlySurjective`: the same on
  the fppf site.
* `lqcohSheafFbcFppfModules_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective`:
  **Stacks 07AQ** part (2).

## References

* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m v' w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Membership in `LQCoh^fbc` of the inverse image `f^* G` of a sheaf of modules along a fibred
1-morphism `f` is membership of its underlying presheaf inverse image: the two have the same
underlying presheaf of modules once the structure functor of the source is presented as
`f ⋙ q`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback_of_modulePullback
    [UnivLE.{u, m}] {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (hfq : (f ⋙ q).IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (G : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ))
    (hG : IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS p hp
      ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).obj G).val) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS (f ⋙ q) hfq
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hfq).obj G.val) := by
  subst hf
  exact hG

/-- **Stacks 07AQ**, part (1). Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of
algebraic stacks with `|𝒳| = ⋃ |f j|(|𝒵 j|)`, and `F` a sheaf of `𝒪_𝒳`-modules on `𝒳_ét`. If
every `f j^{-1} F` is in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` is in `LQCoh^fbc(𝒪_𝒳)`.

The source's hypothesis reads `LQCoh^{fpc}`, a misprint for `LQCoh^{fbc}`. `LQCoh^fbc` is the
sheaf-level one (`AlgebraicGeometry.Stack.lqcohSheafFbcEtaleModules`), with the flat base change
property of **Stacks 0762**; the module sections are in the universe of the schemes. -/
@[stacks 07AQ "part (1), on Mod(𝒳_ét, 𝒪_𝒳), with the flat base change property of 0762 read \
  on sheaves; the module sections in the universe of the schemes"]
theorem lqcohSheafFbcEtaleModules_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳) (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : StackModules B S hS .etale 𝒳)
    (hF : ∀ j, lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS (𝒵 j)
      ((stackModuleInverseImage B S hS .etale (f j)).obj F)) :
    lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 F := by
  have hloc : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F.val) := fun j => by
    have hj := hF j
    dsimp only [stackModuleInverseImage, lqcohSheafFbcEtaleModules] at hj
    rw [moduleInverseImage_eq_modulePullback] at hj
    exact isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback_of_modulePullback
      B E h S hS _ _ _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p (f j).hom) _ _ _ F hj
  exact ⟨isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F.val
      F.isSheaf fun j => (hloc j).1,
    hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F.val
      F.isSheaf fun j => (hloc j).2⟩

/-- **Stacks 07AQ** part (1) on the fppf site: for a family of smooth 1-morphisms
`f j : 𝒵 j ⟶ 𝒳` of algebraic stacks with `|𝒳| = ⋃ |f j|(|𝒵 j|)` and a module `G` on `𝒳_fppf`,
if every `f j^* G` is in `LQCoh^fbc(𝒪_{𝒵 j})` then so is `G`. An fppf sheaf is an étale sheaf,
so this is the étale statement for the underlying presheaf. -/
theorem lqcohSheafFbcFppfModules_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳) (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (G : fppfModules B S hS 𝒳)
    (hG : ∀ j, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS (𝒵 j)
      ((fppfModulesPullback B S hS (f j)).obj G)) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 G := by
  have hsh : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      G.val.presheaf :=
    G.isSheaf.of_le (associatedTopology_mono B S hS 𝒳.val.val.p (etaleTopology_le_topology B))
  have hloc := fun j =>
    isLocallyQuasicoherentWithSheafFlatBaseChange_modulePresheafPullback_of_modulePullback
      B E h S hS _ _ _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p (f j).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) _ _ G (hG j)
  exact ⟨isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs G.val hsh
      fun j => (hloc j).1,
    hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs G.val
      hsh fun j => (hloc j).2⟩

/-- **The direct image of an object of `LQCoh^fbc` along a 1-morphism of algebraic stacks
representable by affine schemes**, on the fppf sites at module universe `u`: if `F` is in
`LQCoh^fbc(𝒪_𝒳)` then so is `f_* F`. This is the case of **Stacks 0771** (4)(b) in degree `0`
used by **Stacks 07AQ** (2).

Both halves are read off the cartesianness of `f_* F` between affines
(`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_stackModuleDirectImage`, at the fppf
topology): along étale arrows this is local quasi-coherence
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`), along
flat arrows it gives the flat base change property by the affine criterion
(`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange`); the
input for `F` along flat arrows is `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flat`.

It differs from `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesPushforward`, which
is stated for an affine 1-morphism (`AlgebraicStacks.IsAffineHom`, **Stacks 0CHQ**): here the
hypothesis is that source and target are representable by affine schemes, the form the reduction
of 07AQ (2) produces. The library does not show that such a 1-morphism is affine in the sense of
0CHQ. -/
theorem lqcohSheafFbcFppfModules_fppfModulesPushforward_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : fppfModules B S hS 𝒳) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
      ((fppfModulesPushforward B S hS f).obj F) := by
  let G := (fppfModulesPushforward B S hS f).obj F
  let F' : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)) :=
    ⟨F.val, F.isSheaf.of_le
      (associatedTopology_mono B S hS 𝒳.val.val.p (etaleTopology_le_topology B))⟩
  let G' : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)) :=
    ⟨G.val, G.isSheaf.of_le
      (associatedTopology_mono B S hS 𝒴.val.val.p (etaleTopology_le_topology B))⟩
  have hlqc : IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids G.val :=
    (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _ G').2
      fun _ _ φ hy hy' hφ => isIso_restrictionBaseChange_stackModuleDirectImage B S hS @Etale
        .fppf f h𝒳 h𝒴 F (fun _ _ ψ hx hx' hψ =>
          (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _ F').1
            hF.1 ψ hx hx' hψ) φ hy hy' hφ
  exact ⟨hlqc, hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS _ _ _
    fun {_ _} φ hy hy' hφ => isIso_restrictionBaseChange_stackModuleDirectImage B S hS @Flat .fppf
      f h𝒳 h𝒴 F (fun _ _ ψ hx hx' hψ =>
        isIso_restrictionBaseChange_of_flat B E h S hS _ _ F.val hF ψ hψ hx hx') φ hy hy' hφ⟩

/-- **Stacks 07AQ**, part (2). Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat and locally finitely
presented 1-morphisms of algebraic stacks with `|𝒳| = ⋃ |f j|(|𝒵 j|)`, and `F` a sheaf of
`𝒪_𝒳`-modules on `𝒳_fppf`. If every `f j^{-1} F` is in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` is in
`LQCoh^fbc(𝒪_𝒳)`.

`LQCoh^fbc` is the sheaf-level one (`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`), with the
flat base change property of **Stacks 0762**; the module sections are in the universe of the
schemes. The proof is the source's ("analogous to the proof of 07AP"), carried out for a general
module rule in
`AlgebraicGeometry.Stack.mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective`. -/
@[stacks 07AQ "part (2), on Mod(𝒪_𝒳) (fppf), with the flat base change property of 0762 read \
  on sheaves; the module sections in the universe of the schemes"]
theorem lqcohSheafFbcFppfModules_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳) (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳)
    (hF : ∀ j, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS (𝒵 j)
      ((fppfModulesPullback B S hS (f j)).obj F)) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F :=
  mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective
    (fun 𝒳 => (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 :
      ObjectProperty (fppfModules B S hS 𝒳)))
    (fun g G hG => lqcohSheafFbcFppfModules_fppfModulesPullback B E h S hS g G hG)
    (fun g h𝒳 h𝒴 G hG =>
      lqcohSheafFbcFppfModules_fppfModulesPushforward_of_isAffineRepresentable B E h S hS g h𝒳
        h𝒴 G hG)
    (fun 𝒳 _ _ _ _ _ _ _ hl h₁ h₂ =>
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).prop_of_isLimit_kernelFork
        (Preadditive.isLimitKernelForkOfFork hl) h₁ h₂)
    (fun g hg hjs G hG =>
      lqcohSheafFbcFppfModules_of_isSmooth_jointlySurjective B E h S hS g hg hjs G hG)
    f hflat hlfp hjs F hF

end AlgebraicGeometry.Stack
