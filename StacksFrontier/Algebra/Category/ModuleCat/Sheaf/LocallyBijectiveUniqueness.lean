module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree

/-!
# Morphisms out of a sheaf of modules are determined on a locally bijective presheaf, and that
# characterizes the isomorphism built from one

`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` builds an isomorphism
`M ≅ N` of sheaves of modules out of an isomorphism `e : P ≅ Q` of presheaves of modules
mapping locally bijectively into them. It is the construction by which the tensor product of
sheaves of modules — a sheafification — is compared with anything: both
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` and
`Stacks.SheafOfModules.TensorLocalProperties.tensor_over_congr` are instances of it.

As a bare `def` it is opaque: it gives an isomorphism and no equation. This file supplies the
equation. The extension principle `existsUnique_moduleHom_of_locallyBijective` already in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorLocallyFree.lean` says a morphism out of a sheaf
is determined by its restriction along a locally bijective map; so

* two morphisms of sheaves of modules agreeing after a locally bijective map are **equal**, and
* the isomorphism produced by `iso_of_locallyBijective` is the **unique** one whose restriction
  along the locally bijective map is the given presheaf isomorphism.

With those, an identity between comparison isomorphisms of tensor products is checked on the
objectwise tensor product, where the monoidal structure of
`PresheafOfModules.pushforward₀OfCommRingCat` computes.

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.hom_ext_of_locallyBijective`: two morphisms of
  sheaves of modules that agree after a locally bijective morphism from a presheaf are equal.
* `Stacks.SheafOfModules.TensorLocalProperties.hom_ext_app_of_locallyBijective`: the same test
  run on sections, which is the form in which an elementary tensor is available.
* `Stacks.SheafOfModules.TensorLocalProperties.iso_ext_of_locallyBijective`: the same for
  isomorphisms.
* `Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective_hom` and
  `iso_of_locallyBijective_inv`: **the characterizing equations**
  `f ≫ hom = e.hom ≫ g` and `g ≫ inv = e.inv ≫ f`.
* `Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective_eq`: any isomorphism
  satisfying the first equation *is* `iso_of_locallyBijective`.
* `Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective_naturality`: **the
  isomorphism is natural.** Two morphisms of sheaves of modules induced by morphisms of the
  presheaves are carried to one another by the two isomorphisms as soon as the two presheaf
  comparisons carry one inducing morphism to the other.
* `Stacks.SheafOfModules.TensorLocalProperties.isoOfLocallyBijective`,
  `isoOfLocallyBijective_hom` and `isoOfLocallyBijective_naturality`: the same three
  statements with the local-bijectivity facts as **explicit** arguments. A comparison
  isomorphism of a sheafified tensor product is read at two spellings of the structure sheaf —
  the pulled-back presheaf of rings on one side and the `structureSheaf` of the smaller site on
  the other, definitionally but not syntactically equal — and instance search, which matches up
  to reducible unfolding only, does not bridge them. These versions let the consumer hand the
  facts over.

## Implementation notes

Every proof here is one application of `moduleHomEquiv_of_locallyBijective`, the bijection
`(Q ⟶ N) ≃ (P ⟶ N)` induced by a locally bijective `P ⟶ Q`: `hom_ext` is its injectivity and
the characterizing equations are `Equiv.apply_symm_apply`, since `iso_of_locallyBijective`
defines its two morphisms as `.symm` of that bijection.

**This file used to record that these equations cannot be transported to a specific comparison
isomorphism from outside the module defining it, and that record is withdrawn.** It described
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` as a tactic block whose `letI`s supply
the two monoidal structures on presheaves of modules, so that recognising it as an
`iso_of_locallyBijective` from outside needed a defeq check reaching the 200000-heartbeat limit.
That is no longer what the definition is: it is `isoOfLocallyBijective` applied to named data,
`whiskerTensorSheafIso_eq` records exactly that by `rfl` inside its own module, and
`whiskerTensorSheafIso_hom` exports the characterizing equation. A consumer therefore needs no
unfolding at all — it rewrites with the exported equation — and the identification of that
isomorphism with the tensorator of slice restriction both *states* and *reduces to a single
equation on the restricted sheafification unit* in a module that merely imports the two files
concerned, with no option override and no heartbeat trouble. What remains true is the narrower
point that the four local-bijectivity facts have to be handed over explicitly rather than found
by instance search, which is what the `isoOfLocallyBijective` family below is for; see its
docstring for the two spellings of the structure sheaf that instance search cannot bridge.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.SheafOfModules.TensorLocalProperties

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} {P Q : PresheafOfModules.{w} R.obj}
  {M N : SheafOfModules.{w} R}

/-- **Two morphisms of sheaves of modules that agree after a locally bijective morphism from a
presheaf of modules are equal.** This is injectivity of
`Stacks.SheafOfModules.TensorLocalProperties.moduleHomEquiv_of_locallyBijective`. -/
theorem hom_ext_of_locallyBijective (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f] {a b : M ⟶ N}
    (h : f ≫ a.val = f ≫ b.val) : a = b :=
  _root_.SheafOfModules.hom_ext
    ((moduleHomEquiv_of_locallyBijective f N.isSheaf).injective h)

/-- `Stacks.SheafOfModules.TensorLocalProperties.hom_ext_of_locallyBijective` with the
hypothesis tested on sections. This is the usable form when the presheaf is an objectwise
tensor product, where the available elements are the elementary tensors. -/
theorem hom_ext_app_of_locallyBijective (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f] {a b : M ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : P.obj X),
      a.val.app X (f.app X x) = b.val.app X (f.app X x)) : a = b :=
  hom_ext_of_locallyBijective f
    (PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext (h X)))

/-- **Two isomorphisms of sheaves of modules that agree after a locally bijective morphism from
a presheaf of modules are equal.** -/
theorem iso_ext_of_locallyBijective (f : P ⟶ M.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f] {a b : M ≅ N}
    (h : f ≫ a.hom.val = f ≫ b.hom.val) : a = b :=
  Iso.ext (hom_ext_of_locallyBijective f h)

/-- **The characterizing equation of
`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective`**: restricted along the
locally bijective map of the source, it is the given isomorphism of presheaves followed by the
locally bijective map of the target. -/
theorem iso_of_locallyBijective_hom (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g]
    [PresheafOfModules.IsLocallySurjective J g] (e : P ≅ Q) :
    f ≫ (iso_of_locallyBijective f g e).hom.val = e.hom ≫ g :=
  (moduleHomEquiv_of_locallyBijective f N.isSheaf).apply_symm_apply _

/-- The characterizing equation of the inverse of
`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective`. -/
theorem iso_of_locallyBijective_inv (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g]
    [PresheafOfModules.IsLocallySurjective J g] (e : P ≅ Q) :
    g ≫ (iso_of_locallyBijective f g e).inv.val = e.inv ≫ f :=
  (moduleHomEquiv_of_locallyBijective g M.isSheaf).apply_symm_apply _

/-- **`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` is the unique
isomorphism satisfying its characterizing equation.** This is what makes a comparison
isomorphism of sheafifications computable: an isomorphism exhibited by any other means, and
agreeing with the presheaf isomorphism on the locally bijective source, is that one. -/
theorem iso_of_locallyBijective_eq (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g]
    [PresheafOfModules.IsLocallySurjective J g] (e : P ≅ Q) (a : M ≅ N)
    (ha : f ≫ a.hom.val = e.hom ≫ g) : a = iso_of_locallyBijective f g e :=
  iso_ext_of_locallyBijective f (ha.trans (iso_of_locallyBijective_hom f g e).symm)

variable {P' Q' : PresheafOfModules.{w} R.obj} {M' N' : SheafOfModules.{w} R}

/-- **`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` is natural.** If a
morphism `φ : M ⟶ M'` of sheaves of modules is induced by a morphism `p : P ⟶ P'` of the
presheaves, a morphism `ψ : N ⟶ N'` by `q : Q ⟶ Q'`, and the two presheaf comparisons carry `p`
to `q`, then the two isomorphisms carry `φ` to `ψ`. -/
theorem iso_of_locallyBijective_naturality
    (f : P ⟶ M.val) (g : Q ⟶ N.val) (f' : P' ⟶ M'.val) (g' : Q' ⟶ N'.val)
    [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    [PresheafOfModules.IsLocallyInjective J g]
    [PresheafOfModules.IsLocallySurjective J g]
    [PresheafOfModules.IsLocallyInjective J f']
    [PresheafOfModules.IsLocallySurjective J f']
    [PresheafOfModules.IsLocallyInjective J g']
    [PresheafOfModules.IsLocallySurjective J g']
    (e : P ≅ Q) (e' : P' ≅ Q') {φ : M ⟶ M'} {ψ : N ⟶ N'} {p : P ⟶ P'} {q : Q ⟶ Q'}
    (hφ : f ≫ φ.val = p ≫ f') (hψ : g ≫ ψ.val = q ≫ g')
    (hpq : p ≫ e'.hom = e.hom ≫ q) :
    φ ≫ (iso_of_locallyBijective f' g' e').hom =
      (iso_of_locallyBijective f g e).hom ≫ ψ := by
  refine hom_ext_of_locallyBijective f ?_
  have h1 : f ≫ (φ ≫ (iso_of_locallyBijective f' g' e').hom).val = e.hom ≫ q ≫ g' := by
    rw [_root_.SheafOfModules.comp_val, ← Category.assoc, hφ, Category.assoc,
      iso_of_locallyBijective_hom, ← Category.assoc, hpq, Category.assoc]
  have h2 : f ≫ ((iso_of_locallyBijective f g e).hom ≫ ψ).val = e.hom ≫ q ≫ g' := by
    rw [_root_.SheafOfModules.comp_val, ← Category.assoc, iso_of_locallyBijective_hom,
      Category.assoc, hψ]
  exact h1.trans h2.symm

/-- `Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` with the four
local-bijectivity facts as explicit arguments, for a consumer whose spelling of the structure
sheaf instance search cannot bridge. -/
noncomputable def isoOfLocallyBijective (f : P ⟶ M.val) (g : Q ⟶ N.val)
    (hfi : PresheafOfModules.IsLocallyInjective J f)
    (hfs : PresheafOfModules.IsLocallySurjective J f)
    (hgi : PresheafOfModules.IsLocallyInjective J g)
    (hgs : PresheafOfModules.IsLocallySurjective J g) (e : P ≅ Q) : M ≅ N :=
  letI := hfi
  letI := hfs
  letI := hgi
  letI := hgs
  iso_of_locallyBijective f g e

/-- The characterizing equation of
`Stacks.SheafOfModules.TensorLocalProperties.isoOfLocallyBijective`. -/
theorem isoOfLocallyBijective_hom (f : P ⟶ M.val) (g : Q ⟶ N.val)
    (hfi : PresheafOfModules.IsLocallyInjective J f)
    (hfs : PresheafOfModules.IsLocallySurjective J f)
    (hgi : PresheafOfModules.IsLocallyInjective J g)
    (hgs : PresheafOfModules.IsLocallySurjective J g) (e : P ≅ Q) :
    f ≫ (isoOfLocallyBijective f g hfi hfs hgi hgs e).hom.val = e.hom ≫ g :=
  have := hfi
  have := hfs
  have := hgi
  have := hgs
  iso_of_locallyBijective_hom f g e

/-- **`Stacks.SheafOfModules.TensorLocalProperties.isoOfLocallyBijective` is natural**, with the
local-bijectivity facts as explicit arguments. -/
theorem isoOfLocallyBijective_naturality
    (f : P ⟶ M.val) (g : Q ⟶ N.val) (f' : P' ⟶ M'.val) (g' : Q' ⟶ N'.val)
    (hfi : PresheafOfModules.IsLocallyInjective J f)
    (hfs : PresheafOfModules.IsLocallySurjective J f)
    (hgi : PresheafOfModules.IsLocallyInjective J g)
    (hgs : PresheafOfModules.IsLocallySurjective J g)
    (hfi' : PresheafOfModules.IsLocallyInjective J f')
    (hfs' : PresheafOfModules.IsLocallySurjective J f')
    (hgi' : PresheafOfModules.IsLocallyInjective J g')
    (hgs' : PresheafOfModules.IsLocallySurjective J g')
    (e : P ≅ Q) (e' : P' ≅ Q') {φ : M ⟶ M'} {ψ : N ⟶ N'} {p : P ⟶ P'} {q : Q ⟶ Q'}
    (hφ : f ≫ φ.val = p ≫ f') (hψ : g ≫ ψ.val = q ≫ g')
    (hpq : p ≫ e'.hom = e.hom ≫ q) :
    φ ≫ (isoOfLocallyBijective f' g' hfi' hfs' hgi' hgs' e').hom =
      (isoOfLocallyBijective f g hfi hfs hgi hgs e).hom ≫ ψ :=
  have := hfi
  have := hfs
  have := hgi
  have := hgs
  have := hfi'
  have := hfs'
  have := hgi'
  have := hgs'
  iso_of_locallyBijective_naturality f g f' g' e e' hφ hψ hpq

end Stacks.SheafOfModules.TensorLocalProperties

end
