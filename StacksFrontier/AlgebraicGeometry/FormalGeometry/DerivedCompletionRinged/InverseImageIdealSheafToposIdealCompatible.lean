module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposCompatible
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCompletionTopos

/-!
# The relation of [Stacks, Tag 099J] for `ℐ' = f^{-1}ℐ · 𝒪_X`, at a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi and `ℐ ⊂ 𝒪` a sheaf of ideals.
`InverseImageIdealSheafTopos.lean` builds `ℐ' = f^{-1}ℐ · 𝒪_X ⊂ 𝒪'` as the image of `f^*ℐ ⟶ 𝒪'`.
This file proves that the pair `(ℐ, ℐ')` satisfies the hypothesis of [Stacks, Tag 099J] —
`AlgebraicGeometry.RingedToposHom.IdealCompatible` — with **no hypothesis on `ℐ` and none on the
morphism**. That is the input the comparison map of [Stacks, Tag 0A0G] needs in order to exist at
this generality.

## Main results

* `AlgebraicGeometry.RingedToposHom.idealCompatible_of_pushforward_eq`: the **direct-image form
  implies the inverse-image form**. Given any `ψ : ℐ ⟶ f_*ℐ'` of sheaves of sets with
  `(ℐ ↪ 𝒪) ≫ f^♯ = ψ ≫ f_*(ℐ' ↪ 𝒪')`, the relation `IdealCompatible f ℐ ℐ'` holds.
* `AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf`:
  **`IdealCompatible f ℐ (f^{-1}ℐ · 𝒪_X)`**, the two combined.

## Implementation notes

*Why this is a transposition and nothing more.* `IdealCompatible f ℐ ℐ'` asks for a factorisation
of `f^{-1}ℐ ⟶ f^{-1}𝒪 ⟶ 𝒪'` through `ℐ' ↪ 𝒪'`, in sheaves of sets on the source. What
`InverseImageIdealSheafToposCompatible.lean` provides is the **transpose** of that datum along
`f^{-1} ⊣ f_*`: the equation `(ℐ ↪ 𝒪) ≫ f^♯ = ψ ≫ f_*(ℐ' ↪ 𝒪')` on the target. The two are
carried to one another by `CategoryTheory.Adjunction.homEquiv`, which is a bijection, so neither
form is stronger.

`idealCompatible_of_pushforward_eq` runs that transposition in the direction
direct-image `⟹` inverse-image. It is the same three-step computation that
`AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete` performs inline in the
opposite direction at the start of its proof — `fSharpInverseImage_forget_homEquiv` to recognise
`f^♯` on sections as the adjunct of its inverse-image form, then
`CategoryTheory.Adjunction.homEquiv_naturality_left` and `.homEquiv_naturality_right` to move the
two inclusions across the bijection — read backwards through `Equiv.injective`. The converse
direction is therefore *not* restated here; it is already performed where it is used.

The proof is in term mode throughout. The underlying sheaf of sets of `f^*𝒪` has two
definitionally-equal spellings in the library (and likewise `f_*𝒪'`), which agree only at default
transparency; `rewrite` on them builds motives that fail to re-typecheck. Composing `Eq.trans`
and `congrArg` never forms a motive, so the spellings never have to be reconciled.

## Deliberately untagged

This verifies the *hypothesis* of [Stacks, Tag 099J] for a constructed ideal sheaf; it is not a
statement of the Stacks Project. [Stacks, Tag 099J] itself is registered on
`AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`, which consumes the
relation proved here. The ringed-sites counterpart
`AlgebraicGeometry.RingedSite.pushforwardIdealCompatible_inverseImageIdealSheaf` of
`InverseImageIdealSheaf.lean` carries no attribute either.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 100000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (I' : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The direct-image form of the [Stacks, Tag 099J] relation implies the inverse-image form.**
Given a map `ψ : ℐ ⟶ f_*ℐ'` of the underlying sheaves of sets with
`(ℐ ↪ 𝒪) ≫ f^♯ = ψ ≫ f_*(ℐ' ↪ 𝒪')`, the composite `f^{-1}ℐ ⟶ f^{-1}𝒪 ⟶ 𝒪'` factors through
`ℐ' ↪ 𝒪'`, which is `AlgebraicGeometry.RingedToposHom.IdealCompatible f ℐ ℐ'`.

The factorisation is the adjunct `φ = ψ^♭` of `ψ` under `f^{-1} ⊣ f_*`, and the equation it has
to satisfy is the given one read back across the same bijection: `Equiv.injective` reduces the
goal to an equation between the two adjuncts, and
`CategoryTheory.Adjunction.homEquiv_naturality_left`,
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` and
`CategoryTheory.Adjunction.homEquiv_naturality_right` identify those with the two sides of the
hypothesis. No hypothesis on `ℐ`, on `ℐ'` or on `f`. -/
theorem idealCompatible_of_pushforward_eq
    (psi : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        I.toSheafOfModules ⟶
      f.toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          I'.toSheafOfModules))
    (hpsi : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map I.ι ≫
        forgetFSharp f =
      psi ≫ f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map I'.ι)) :
    IdealCompatible f I I' := by
  refine ⟨(f.toToposHom.adj.homEquiv _ _).symm psi, ?_⟩
  apply (f.toToposHom.adj.homEquiv _ _).injective
  have h1 : forgetFSharp f = f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O)
      (X.forgetRing.obj X.O) (X.forgetRing.map f.fSharpInverseImage) :=
    ((congrArg (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O))
      (fSharpInverseImage_forget_homEquiv.{u, u, u, u, u, u} f)).trans
      (Equiv.apply_symm_apply _ _)).symm
  refine Eq.trans (f.toToposHom.adj.homEquiv_naturality_left
      (X' := (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        I.toSheafOfModules)
      (X := Y.forgetRing.obj Y.O) (Y := X.forgetRing.obj X.O)
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map I.ι)
      (X.forgetRing.map f.fSharpInverseImage)) ?_
  refine Eq.trans (congrArg (fun k => (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map I.ι ≫ k) h1.symm) ?_
  refine hpsi.trans ?_
  refine Eq.trans (congrArg (fun k => k ≫ f.toToposHom.pushforward.map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map I'.ι))
      (Equiv.apply_symm_apply (f.toToposHom.adj.homEquiv _ _) psi).symm) ?_
  exact (f.toToposHom.adj.homEquiv_naturality_right
    ((f.toToposHom.adj.homEquiv _ _).symm psi)
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map I'.ι)).symm

/-- **`f^♯` carries `f^{-1}ℐ` into `ℐ' = f^{-1}ℐ · 𝒪_X`, for an arbitrary morphism of ringed
topoi**: the relation of [Stacks, Tag 099J] holds between `ℐ` and the ideal sheaf the source
constructs out of it, with no hypothesis on `ℐ` and none on `f`.

This is the second of the two properties Section 52.7 asks of `f^{-1}ℐ · 𝒪_X`, the first being
the leastness of `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_le_iff`. It is the
ringed-topoi counterpart of
`AlgebraicGeometry.RingedSite.pushforwardIdealCompatible_inverseImageIdealSheaf`, and it is what
makes the comparison map of [Stacks, Tag 0A0G] exist at this generality.

`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_homEquiv_idealMapFactorThru_comp` is the
relation in direct-image form, proved there from the factorisation
`idealMapFactorThru_ι` of `f^*ℐ ⟶ 𝒪'` through `ℐ'` by transporting it along `f^* ⊣ f_*` in
sheaves of **modules**; `idealCompatible_of_pushforward_eq` then transposes it back along
`f^{-1} ⊣ f_*` in sheaves of **sets**, which is the form the relation is stated in. -/
theorem idealCompatible_inverseImageIdealSheaf :
    IdealCompatible f I (inverseImageIdealSheaf.{u} f I) :=
  idealCompatible_of_pushforward_eq f I _
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((pullbackAdjPushforwardModules f).homEquiv _ _ (idealMapFactorThru.{u} f I)))
    (moduleSheafFunctor_homEquiv_idealMapFactorThru_comp.{u} f I).symm

end AlgebraicGeometry.RingedToposHom

end
