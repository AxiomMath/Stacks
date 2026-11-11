module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfInternalHomAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeTensor

/-!
# `LQCoh^fbc(𝒪_𝒳)` is closed under internal Homs out of modules of finite presentation

**Stacks 0771** part (7) says that for `F` an `𝒪_𝒳`-module of finite presentation and `G` in
`LQCoh^fbc(𝒪_𝒳)` on an algebraic stack, the internal Hom `SheafHom_{𝒪_𝒳}(F, G)` lies in
`LQCoh^fbc(𝒪_𝒳)`.  Together with `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` this is the membership clause of
**Stacks 0GQN**.

The proof is the one of part (6) with the tensor product replaced by the internal Hom:

* `G` is cartesian along the flat arrows between objects over affine schemes
  (`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_flat`, step R2 of Stacks 0779);
* so is `SheafHom_{𝒪_𝒳}(F, G)`, `F` being of finite presentation
  (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_internalHomSheafSmall`): over an
  affine object its sections are `Hom_{𝒪(x)}(F(x), G(x))`, with `F(x)` of finite presentation, and
  `Hom` out of a module of finite presentation commutes with flat base change;
* a module cartesian along those arrows is locally quasi-coherent and has the flat base change
  property
  (`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`,
  `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange`).

The finite presentation hypothesis is needed: on `(Sch/ℤ)` the `p`-torsion `𝒪[p]` of the structure
sheaf is in `LQCoh^fbc` and has no global sections, while its identity endomorphism is a non-zero
global section of `SheafHom(𝒪[p], 𝒪[p])`.

## Main results

* `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfInternalHom`: **Stacks 0771, part (7).**
* `AlgebraicStacks.lqcohSheafFbcFppfModules_fppfInternalHom_of_isQuasicoherentOnSite`: the
  membership clause of **Stacks 0GQN**.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0771, part (7).** For `F` an `𝒪_𝒳`-module of finite presentation and `G` in
`LQCoh^fbc(𝒪_𝒳)` on an algebraic stack, the internal Hom `SheafHom_{𝒪_𝒳}(F, G)` of `Mod(𝒪_𝒳)`
is in `LQCoh^fbc(𝒪_𝒳)`.

`G` is cartesian along the flat arrows between objects over affine schemes (step R2 of
Stacks 0779), hence so is `SheafHom_{𝒪_𝒳}(F, G)`, `F` being of finite presentation; a module
cartesian along those arrows is locally quasi-coherent and has the flat base change property. -/
@[stacks 0771 "part (7): SheafHom(F, G) of Mod(𝒪_𝒳) lies in LQCoh^fbc(𝒪_𝒳) for F of finite \
presentation in Mod(𝒪_𝒳) and G in LQCoh^fbc(𝒪_𝒳), with the flat base change property of 0762 \
read on sheaves; modules at the module universe u of the schemes"]
theorem lqcohSheafFbcFppfModules_fppfInternalHom (F G : fppfModules B S hS 𝒳)
    [F.IsFinitePresentationOnSite]
    (hG : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 G) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
      (AlgebraicStacks.fppfInternalHom B S hS 𝒳 F G) := by
  have hT : ∀ {z x : 𝒳.val.val.obj} (φ : z ⟶ x),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
        (AlgebraicStacks.fppfInternalHom B S hS 𝒳 F G).val φ.op) := fun φ hz hx hφ =>
    FibredSite.isIso_restrictionBaseChange_internalHomSheafSmall B S hS _ _ F G
      (fun ψ hz' hx' hψ => isIso_restrictionBaseChange_of_flat B E h S hS _ _ G.val hG ψ hψ hz' hx')
      φ hz hx hφ
  have hL : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (AlgebraicStacks.fppfInternalHom B S hS 𝒳 F G).val :=
    (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _
      ((fppfToEtaleModules B S hS 𝒳).obj (AlgebraicStacks.fppfInternalHom B S hS 𝒳 F G))).2
      fun _ _ φ hy hy' hφ => hT φ hy hy' (by
        have : Etale ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ)) := hφ
        infer_instance)
  exact ⟨hL, hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS _ _ _
    fun φ hz hx hφ => hT φ hz hx hφ⟩

namespace AlgebraicStacks

/-- **Stacks 0GQN**, the membership clause: for `F` an `𝒪_𝒳`-module of finite presentation and `G`
a quasi-coherent `𝒪_𝒳`-module on an algebraic stack, the internal Hom `SheafHom_{𝒪_𝒳}(F, G)`,
whose two computations agree by
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfInternalHom_presheaf_eq_etaleInternalHom`, is an
object of `LQCoh^fbc(𝒪_𝒳)`.  It is Stacks 0771 (7) applied to `G ∈ QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0GQN "the common value SheafHom(F, G) is an object of LQCoh^fbc(𝒪_𝒳), for F of finite \
presentation and G quasi-coherent"]
theorem lqcohSheafFbcFppfModules_fppfInternalHom_of_isQuasicoherentOnSite
    (F G : Stack.fppfModules B S hS 𝒳) [F.IsFinitePresentationOnSite]
    (hG : G.IsQuasicoherentOnSite) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 (fppfInternalHom B S hS 𝒳 F G) :=
  lqcohSheafFbcFppfModules_fppfInternalHom B E h S hS 𝒳 F G
    (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h G hG)

end AlgebraicStacks

end AlgebraicGeometry.Stack
