module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSiteAssociatedModuleCartesian

/-!
# The module attached to a quasi-coherent sheaf is cartesian on a small affine site

Let `S` be a scheme and let `τ` be the Zariski or the étale topology.  Condition (4) of
Stacks 0GZX says that a presheaf of `𝒪_affine`-modules on `S_{affine, τ}` comes from a unique
quasi-coherent `𝒪_S`-module `𝒢` by the procedure of Descent, Section 35.8, that is, that it is
the restriction to the affine objects of `𝒢ᵃ : U/S ↦ Γ(U, f^*𝒢)`.  This file proves the
implication **(4) ⇒ (1)**: such a presheaf has all its base-change comparisons

`𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)`

isomorphisms.  This is the last paragraph of the proof in the source, the one that appeals to
Schemes, Lemma 26.7.3.

The argument is the one already used for the five big affine sites of Stacks 0GZV in
`StacksFrontier.AlgebraicGeometry.Descent.AffineSiteAssociatedModuleCartesian`, namely
`Stacks.Sites.isIso_restrictionBaseChange_associatedModulePresheaf`, which is stated for an
arbitrary category of *affine* schemes over `S` and uses neither the topology nor the size of
the category.  All this file supplies is the two presenting functors of the small affine sites
and the identification of their structure presheaves.

## Main definitions

* `AlgebraicGeometry.smallAffineZariskiToOver` and
  `AlgebraicGeometry.smallAffineEtaleToOver`: the presenting functors
  `S_{affine, τ} ⥤ Over S` of the two small affine sites of Stacks 0GZX.

## Main results

* `AlgebraicGeometry.smallAffineZariskiRingedSite_O_obj` and
  `AlgebraicGeometry.smallAffineEtaleRingedSite_O_obj`: the structure presheaf of each small
  affine ringed site is the presheaf of global functions of its presenting functor, on the
  nose.
* `AlgebraicGeometry.smallAffineZariski_isIso_restrictionBaseChange_associatedModule` and
  `AlgebraicGeometry.smallAffineEtale_isIso_restrictionBaseChange_associatedModule`:
  **Stacks 0GZX, condition (4) implies condition (1)**, at `τ = Zariski` and at `τ = étale`.

## Implementation notes

The presenting functor of a small affine site is the inclusion of the affine objects into the
small site, followed by the inclusion of the small site into the big category over `S`,
followed by `CategoryTheory.Over.post` of the inclusion of the ambient category of schemes.
Its composite with `CategoryTheory.Over.forget` is the canonical functor to schemes
`AlgebraicGeometry.SmallAffineZariski.toScheme`, respectively
`AlgebraicGeometry.SmallAffineEtale.toScheme`, because `Over.post F ⋙ Over.forget` and
`Over.forget ⋙ F` agree on objects and on morphisms; so the structure presheaf identifications
hold by `rfl`, exactly as for the big affine sites.

Only the implication (4) ⇒ (1) is proved *here*.  The existence of `𝒢` in condition (4), and
condition (3) read from condition (2), are in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists` at `τ = étale` and
in `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists` at
`τ = Zariski`; its uniqueness is in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesUnique` and
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiUnique`.  Of those,
only the existence of `𝒢` at `τ = étale` uses Descent, Proposition 03DX — clause (2) of it,
which this development has unconditionally; the Zariski route uses no part of 03DX.  See the
coverage note of `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines`.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Sites

/-! ### The small affine Zariski site -/

/-- The presenting functor of the small affine Zariski site of `S`. -/
public noncomputable abbrev smallAffineZariskiToOver (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : SmallAffineZariski B S hS ⥤ Over S :=
  SmallAffineZariski.inclusion B S hS ⋙ SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.smallAffineZariskiRingedSite` is the presheaf
of global functions of its presenting functor. -/
public theorem smallAffineZariskiRingedSite_O_obj (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (smallAffineZariskiRingedSite B S hS).O.obj =
      commStructurePresheaf S (smallAffineZariskiToOver B S hS) := rfl

public instance isAffine_smallAffineZariskiToOver (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : SmallAffineZariski B S hS) :
    IsAffine ((smallAffineZariskiToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZX, condition (4) implies condition (1) at `τ = Zariski`.** The presheaf `𝒢ᵃ` of
Descent, Section 35.8 attached to a quasi-coherent `𝒪_S`-module `𝒢` has all its base-change
comparisons `𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)` isomorphisms on the small affine Zariski site
of `S`. -/
@[stacks 0GZX "(4) ⇒ (1) at τ = Zariski"]
public theorem smallAffineZariski_isIso_restrictionBaseChange_associatedModule
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (SmallAffineZariski B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (smallAffineZariskiRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (smallAffineZariskiToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

/-! ### The small affine étale site -/

/-- The presenting functor of the small affine étale site of `S`. -/
public noncomputable abbrev smallAffineEtaleToOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : SmallAffineEtale B S hS ⥤ Over S :=
  SmallAffineEtale.inclusion B S hS ⋙ SmallEtale.inclusion B S hS ⋙ Over.post B.inclusion

/-- The structure presheaf of `AlgebraicGeometry.smallAffineEtaleRingedSite` is the presheaf of
global functions of its presenting functor. -/
public theorem smallAffineEtaleRingedSite_O_obj (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (smallAffineEtaleRingedSite B S hS).O.obj =
      commStructurePresheaf S (smallAffineEtaleToOver B S hS) := rfl

public instance isAffine_smallAffineEtaleToOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : SmallAffineEtale B S hS) :
    IsAffine ((smallAffineEtaleToOver B S hS).obj X).left := X.property

/-- **Stacks 0GZX, condition (4) implies condition (1) at `τ = étale`.** The presheaf `𝒢ᵃ` of
Descent, Section 35.8 attached to a quasi-coherent `𝒪_S`-module `𝒢` has all its base-change
comparisons `𝒢ᵃ(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝒢ᵃ(U)` isomorphisms on the small affine étale site
of `S`. -/
@[stacks 0GZX "(4) ⇒ (1) at τ = étale"]
public theorem smallAffineEtale_isIso_restrictionBaseChange_associatedModule
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : S.Modules) [G.IsQuasicoherent] {X Y : (SmallAffineEtale B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (smallAffineEtaleRingedSite B S hS).O.obj)
      (associatedModulePresheaf S G (smallAffineEtaleToOver B S hS)) f) :=
  isIso_restrictionBaseChange_associatedModulePresheaf G _ f

end AlgebraicGeometry

end
