module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocallyProjectivePurity
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover

/-!
# Free global sections over an affine base give universal purity

More on Flatness, Stacks 05K6, says that a finite type quasi-coherent module `F` on `X`, with
`f : X ⟶ S` affine and of finite type, is universally pure relative to `S` as soon as `f_* F` is
locally projective. This file records the special case in which the source's proof of Stacks 0CW4
uses it: `S = Spec R` is affine, `X` is affine, and `Γ(X, F)` is a free `R`-module. A free module
is projective, and a quasi-coherent module on an affine scheme with projective global sections is
locally projective, the whole scheme being an affine open cover of itself.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocallyProjective_of_projective_globalSections`: a
  quasi-coherent module on an affine scheme with projective global sections is locally projective.
* `AlgebraicGeometry.isUniversallyPureRelative_of_free_globalSections`: **Stacks 05K6 for free
  global sections over an affine base.**

## References

* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A quasi-coherent module on an affine scheme whose global sections are a projective module
over the global functions is locally projective: the whole scheme is an affine open cover of
itself on which the sections are projective. -/
theorem Scheme.Modules.isLocallyProjective_of_projective_globalSections {T : Scheme.{u}}
    [IsAffine T] (M : T.Modules) [M.IsQuasicoherent]
    (h : Module.Projective Γ(T, ⊤) Γ(M, ⊤)) : Scheme.Modules.IsLocallyProjective M := by
  refine (isLocallyProjective_iff_exists_affineOpen_cover M).2
    ⟨PUnit, fun _ => ⊤, ?_, fun _ => isAffineOpen_top T, fun _ => h⟩
  change (⨆ _ : PUnit, (⊤ : T.Opens)) = ⊤
  simp

/-- **Stacks 05K6 for free global sections over an affine base.** Let `f : X ⟶ Spec R` be a
morphism locally of finite type from an affine scheme, and let `F` be a finite type
quasi-coherent module on `X` whose global sections are a free `R`-module through `f`. Then `F` is
universally pure relative to `Spec R`.

The direct image `f_* F` is quasi-coherent, `f` being affine, and its global sections are those of
`F`; they are free, hence projective, over `R ≅ Γ(Spec R, ⊤)`, so `f_* F` is locally projective
and Stacks 05K6 applies. -/
theorem isUniversallyPureRelative_of_free_globalSections {R : CommRingCat.{u}} {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec R) [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hfree :
      letI : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
      Module.Free R Γ(F, ⊤)) :
    IsUniversallyPureRelative f F := by
  let : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f F
  let N := Γ((Scheme.Modules.pushforward f).obj F, ⊤)
  have : Module.Free R N := hfree
  let e := Scheme.ΓSpecIso R
  let σ := CommRingCat.Hom.hom e.inv
  let σ' := CommRingCat.Hom.hom e.hom
  let : RingHomInvPair σ σ' := by
    constructor <;> ext x <;> simp [σ, σ']
  let : RingHomInvPair σ' σ := .symm σ σ'
  let q : N ≃ₛₗ[σ] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => by rfl }
  exact isUniversallyPureRelative_of_pushforward_isLocallyProjective f F
    (Scheme.Modules.isLocallyProjective_of_projective_globalSections _ (.of_equiv q))

end AlgebraicGeometry

end
