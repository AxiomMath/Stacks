module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the sheaf-hom of modules on a scheme

Let `X` be a scheme and let `F`, `G` be `𝒪_X`-modules with `F` of finite presentation and `G`
quasi-coherent. Then `SheafHom(F, G)` is quasi-coherent.

The input is the first clause of [Stacks, Tag 01CQ]: around every point `SheafHom(F, G)` is the
kernel of a morphism between finite direct sums of copies of `G`. Quasi-coherent modules on a
scheme are stable under kernels
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`) and under coproducts
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`), and quasi-coherence
is local on the base (`Stacks.Modules.isQuasicoherent_of_restrict`), so the local kernel
description suffices.

## Main results

* `AlgebraicGeometry.isQuasicoherent_of_locally_isoKernel`: a module which is, around every
  point, the kernel of a morphism between finite direct sums of copies of a fixed quasi-coherent
  module is quasi-coherent.
* `AlgebraicGeometry.sheafHom_isQuasicoherent`: **the quasi-coherence clause of
  [Stacks, Tag 0AXZ]**, which is the assertion of Schemes, [Stacks, Tag 01LA] used in its proof.
  The sheaf-hom from a module of finite presentation into a quasi-coherent module is
  quasi-coherent.

## Implementation notes

**Where the statement lives.** The local kernel description of
`StacksFrontier/AlgebraicGeometry/InternalHomCoherent/LocalKernel.lean` is phrased on the slice
sites of the site of opens: it produces an isomorphism `SheafHom(F, G)|_U ≅ ker f` of sheaves of
modules over `𝒪_X.over U`. Everything about quasi-coherence on a scheme is phrased with
`AlgebraicGeometry.Scheme.Modules.restrict` along the open immersion `U.ι`. The two are compared
by `AlgebraicGeometry.Scheme.Modules.overEquiv`, which is an equivalence and hence carries the
kernel and the coproducts across;
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` identifies its forward image of `M.over U`
with `M.restrict U.ι`.

**Why the index type is `Fin m`.** That is the shape the local kernel description produces, and
it is below the universe of the site, so the coproduct lemma is applied through
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit` at the shape
`Discrete (Fin m)` rather than through the coproduct lemma
`isQuasicoherent_sigma`, whose index type is pinned to the universe of the scheme.

## References

* [Stacks Project, Tag 0AXZ](https://stacks.math.columbia.edu/tag/0AXZ)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.InternalHom

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Quasi-coherence of modules on a scheme is transported along isomorphisms. -/
private theorem isQuasicoherent_of_iso {Y : Scheme.{u}} {M N : SheafOfModules Y.ringCatSheaf}
    (e : M ≅ N) (h : M.IsQuasicoherent) : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e h

/-- A finite direct sum of copies of a quasi-coherent module on a scheme is quasi-coherent. -/
theorem isQuasicoherent_finCoprod {m : ℕ} (Q : X.Modules) [Q.IsQuasicoherent] :
    (∐ fun _ : Fin m => Q).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun _ : Fin m => Q) fun _ => inferInstanceAs Q.IsQuasicoherent

/-- The slice-site reading of a finite direct sum of copies of a quasi-coherent module is
quasi-coherent on the open subscheme: restriction preserves quasi-coherence, and
`AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence, so it carries the coproduct
across. -/
theorem isQuasicoherent_overEquiv_finCoprod (U : X.Opens) (G : X.Modules) [G.IsQuasicoherent]
    (m : ℕ) :
    ((Scheme.Modules.overEquiv U).functor.obj (∐ fun _ : Fin m => G.over U)).IsQuasicoherent := by
  have hG : ((Scheme.Modules.overEquiv U).functor.obj (G.over U)).IsQuasicoherent :=
    isQuasicoherent_of_iso ((Scheme.Modules.overFunctorEquiv U).app G).symm inferInstance
  exact isQuasicoherent_of_iso
    (PreservesCoproduct.iso (Scheme.Modules.overEquiv U).functor
      (fun _ : Fin m => G.over U)).symm
    (isQuasicoherent_finCoprod _)

/-- The slice-site reading of a kernel of a morphism between finite direct sums of copies of a
quasi-coherent module is quasi-coherent on the open subscheme. -/
theorem isQuasicoherent_overEquiv_kernel (U : X.Opens) (G : X.Modules) [G.IsQuasicoherent]
    {m n : ℕ} (f : (∐ fun _ : Fin m => G.over U) ⟶ (∐ fun _ : Fin n => G.over U)) :
    ((Scheme.Modules.overEquiv U).functor.obj (kernel f)).IsQuasicoherent := by
  have := isQuasicoherent_overEquiv_finCoprod U G m
  have := isQuasicoherent_overEquiv_finCoprod U G n
  exact isQuasicoherent_of_iso
    (PreservesKernel.iso (Scheme.Modules.overEquiv U).functor f).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
      ((Scheme.Modules.overEquiv U).functor.map f))

/-- **A module which is locally a kernel of a morphism between finite direct sums of copies of a
quasi-coherent module is quasi-coherent.**

The hypothesis is the shape of the local description supplied by the first clause of
[Stacks, Tag 01CQ]; the conclusion follows because quasi-coherence is local on the base and
quasi-coherent modules are stable under finite coproducts and under kernels. -/
theorem isQuasicoherent_of_locally_isoKernel (H G : X.Modules) [G.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ (m n : ℕ)
      (f : (∐ fun _ : Fin m => G.over U) ⟶ (∐ fun _ : Fin n => G.over U)),
      Nonempty (H.over U ≅ kernel f)) : H.IsQuasicoherent := by
  have key : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (H.restrict U.ι).IsQuasicoherent := by
    intro x
    obtain ⟨U, hxU, m, n, f, ⟨e⟩⟩ := h x
    exact ⟨U, hxU, isQuasicoherent_of_iso ((Scheme.Modules.overFunctorEquiv U).app H)
      (isQuasicoherent_of_iso ((Scheme.Modules.overEquiv U).functor.mapIso e).symm
        (isQuasicoherent_overEquiv_kernel U G f))⟩
  choose U hU hqc using key
  exact Stacks.Modules.isQuasicoherent_of_restrict H U
    (le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩) hqc

/-- **The quasi-coherence clause of [Stacks, Tag 0AXZ].** On a scheme, the sheaf-hom
`SheafHom(F, G)` from a module of finite presentation into a quasi-coherent module is
quasi-coherent.

This is the assertion of Schemes, [Stacks, Tag 01LA] which makes the statement of Tag 0AXZ
meaningful: torsion freeness is a notion for quasi-coherent modules. It is deduced from the
first clause of [Stacks, Tag 01CQ],
`Stacks.SheafOfModules.InternalHom.exists_locally_isoKernel_sheafInternalHom`. -/
@[stacks 0AXZ "quasi-coherence"]
theorem sheafHom_isQuasicoherent (F G : X.Modules)
    [F.IsFinitePresentation] [G.IsQuasicoherent] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (sheafInternalHom (spaceRingedSite X.sheaf) F G) := by
  let : SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite X.sheaf).O)) F :=
    ‹F.IsFinitePresentation›
  exact isQuasicoherent_of_locally_isoKernel _ G
    (exists_locally_isoKernel_sheafInternalHom X.sheaf F G)

end AlgebraicGeometry

end
