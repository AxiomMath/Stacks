module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Sheafification of presheaves of modules commutes with restriction of scalars along an isomorphism

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `α : R₀ ⟶ R.obj` be a locally
bijective morphism from a presheaf of rings, so that `PresheafOfModules.sheafification α` is the
associated sheaf functor from presheaves of `R₀`-modules to sheaves of `R`-modules.  Suppose given
a second such datum `α' : R₀' ⟶ R'.obj`, an isomorphism `R ≅ R'` of sheaves of rings and an
isomorphism `R₀ ≅ R₀'` of presheaves of rings compatible with it.  Then **sheafifying a presheaf
of `R₀`-modules and sheafifying its restriction of scalars to `R₀'` give the same sheaf of
modules**, up to the restriction of scalars along `R ≅ R'`.

This is the statement that the sheafification of presheaves of modules commutes with restriction
of scalars along an isomorphism of presheaves of rings.  It is *not* the corresponding statement
for the objectwise tensor product, which is a genuinely harder one: here nothing has to be
compared except two scalar multiplications on one and the same abelian sheaf.

## Main results

* `PresheafOfModules.Sheafify.smul_restrictScalars_comparison` — the two scalar multiplications on
  the sheafification agree.  This is the mathematical content: both are pinned down by their
  values on a covering sieve, by `PresheafOfModules.Sheafify.map_smul_eq`, and the compatibility
  hypotheses say that the same local lift of a scalar computes both.
* `PresheafOfModules.sheafifyRestrictScalarsCompIso` — the resulting isomorphism of sheaves of
  modules, the identity on sections.
* `PresheafOfModules.sheafificationRestrictScalarsIso` — **the headline statement**, for an
  isomorphism `ι : R ≅ R'` of sheaves of rings on `(C, J)` and a presheaf of `R`-modules `N`:

  `(sheafification (𝟙 R.obj)).obj N ≅
      (SheafOfModules.restrictScalars ι.hom).obj
        ((sheafification (𝟙 R'.obj)).obj ((restrictScalars ι.inv.hom).obj N))`

  — sheafify over `R`, or restrict the scalars to `R'` and sheafify there: the same sheaf of
  modules.

## What is and is not proved

The isomorphisms above are proved in full generality, with **no hypothesis beyond those named in
their statements**: a site, two sheafification data for presheaves of rings, a morphism of sheaves
of rings relating the targets and a morphism of presheaves of rings relating the sources together
with a pointwise one-sided inverse.  No hypothesis is carried that is not an argument.

What is *not* proved here, and is not needed for the statements above:

* the analogous statement for the objectwise **tensor product** of presheaves of modules.  The
  library has the tensor product's interaction with *extension* of scalars, not with restriction;
  nothing here supplies it.
* that `PresheafOfModules.restrictScalars` along an isomorphism of presheaves of rings is an
  equivalence of categories, or that the two sheafification functors are isomorphic as functors.
  Only the objectwise isomorphism is constructed, which is what the applications need.  An
  uniqueness-of-adjoints proof of a functor-level statement would need that equivalence, together
  with the composition isomorphism for `restrictScalars`; the route taken here needs neither.
* any statement about quasi-coherence, or any instance of a Stacks tag.  **No tag attribute is
  placed.**

## Implementation notes

The compatibilities are taken as *pointwise* hypotheses on sections rather than as equations
between morphisms of presheaves of rings, and the inverse of the isomorphism of presheaves of
rings is taken as data rather than through `IsIso`.  Both choices follow the precedent of
`PresheafOfModules.extPowRestrictScalarsIso` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/DifferentialFormsLocallyQuasicoherent.lean`,
and for the same reason: in the applications the presheaves of rings appear at a spelling obtained
by reassociating a composite of functors, and instance search does not see through the
reassociation, so forming `inv` of the comparison at the spelling a lemma asks for fails even
though the comparison is an isomorphism.  Pointwise hypotheses are insensitive to that.

Only one of the two round-trip identities is used: the comparison of the two scalar
multiplications lifts a scalar of `R` to `R₀` and pushes it to `R₀'`, so only
`γ ∘ β = id` is needed, and no hypothesis at all is needed on the morphism of sheaves of rings
beyond its naturality.

## References

* [Stacks Project, Tag 00YR](https://stacks.math.columbia.edu/tag/00YR)
-/

@[expose] public noncomputable section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ R₀' : Cᵒᵖ ⥤ RingCat.{u}} {R R' : Sheaf J RingCat.{u}}
  (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  (α' : R₀' ⟶ R'.obj) [Presheaf.IsLocallyInjective J α'] [Presheaf.IsLocallySurjective J α']
  (b : R ⟶ R') (β : R₀ ⟶ R₀') (γ : R₀' ⟶ R₀)
  {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

/-- **A sheafification morphism for a presheaf of modules, read as one for its restriction of
scalars.**  Restriction of scalars does not change the underlying presheaf of abelian groups, so
this is the identity; it is named because the two spellings of the source presheaf are *not*
interchangeable for instance search, which does not unfold `PresheafOfModules.restrictScalars`.
The two local bijectivity instances below are stated at this spelling for the same reason. -/
def restrictScalarsSheafifyMap (γ : R₀' ⟶ R₀) (M₀ : PresheafOfModules.{v} R₀)
    {A : Sheaf J AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A.obj) :
    ((restrictScalars γ).obj M₀).presheaf ⟶ A.obj :=
  φ

/-- `restrictScalarsSheafifyMap` is locally injective when the morphism it renames is. -/
instance isLocallyInjective_restrictScalarsSheafifyMap (γ : R₀' ⟶ R₀) :
    Presheaf.IsLocallyInjective J (restrictScalarsSheafifyMap γ M₀ φ) :=
  (inferInstance : Presheaf.IsLocallyInjective J φ)

/-- `restrictScalarsSheafifyMap` is locally surjective when the morphism it renames is. -/
instance isLocallySurjective_restrictScalarsSheafifyMap (γ : R₀' ⟶ R₀) :
    Presheaf.IsLocallySurjective J (restrictScalarsSheafifyMap γ M₀ φ) :=
  (inferInstance : Presheaf.IsLocallySurjective J φ)

/-- **The two scalar multiplications on the sheafification agree.**

Let `α : R₀ ⟶ R.obj` and `α' : R₀' ⟶ R'.obj` be two sheafification data for presheaves of rings,
related by a morphism `b : R ⟶ R'` of sheaves of rings and a morphism `β : R₀ ⟶ R₀'` of presheaves
of rings with `α' ∘ β = b ∘ α` on sections, and let `γ : R₀' ⟶ R₀` be a left inverse of `β` on
sections.  Let `M₀` be a presheaf of `R₀`-modules whose underlying presheaf of abelian groups has
`φ` as a sheafification morphism onto the abelian sheaf `A`.

Then the `R`-module structure which `α` puts on the sections of `A`, and the `R`-module structure
obtained by restricting along `b` the `R'`-module structure which `α'` puts on them from the
restriction of scalars of `M₀` along `γ`, are the same.

Both multiplications are characterised, by `PresheafOfModules.Sheafify.map_smul_eq`, by their
restrictions to a covering sieve on which the scalar lifts to `R₀` and the section lifts to `M₀`:
if `r₀` is such a lift of `r`, then `β r₀` is a lift of `b r` for `α'`, by the compatibility and
the naturality of `b`, and `γ (β r₀) = r₀`, so both restrictions are the image of `r₀ • m₀`. -/
theorem Sheafify.smul_restrictScalars_comparison
    (hαβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), α'.app X (β.app X r) = b.hom.app X (α.app X r))
    (hγβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), γ.app X (β.app X r) = r)
    (X : Cᵒᵖ) (r : R.obj.obj X) (m : A.obj.obj X) :
    Sheafify.smul α' (restrictScalarsSheafifyMap γ M₀ φ) (b.hom.app X r) m =
      Sheafify.smul α φ r m := by
  apply A.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J α r) (Presheaf.imageSieve_mem J φ m))
  rintro Y f ⟨⟨r₀, hr₀⟩, ⟨m₀, hm₀⟩⟩
  rw [Sheafify.map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    Sheafify.map_smul_eq α' (restrictScalarsSheafifyMap γ M₀ φ) (b.hom.app X r) m f.op
      (β.app _ r₀) (by rw [hαβ, hr₀]; exact NatTrans.naturality_apply b.hom f.op r)
      m₀ hm₀]
  exact congrArg (φ.app _) (congrArg (· • m₀) (hγβ _ r₀))

/-- **The comparison of the two sheafifications on the sections over one object**: the identity
map of the sections of the abelian sheaf, linear for the two scalar multiplications identified by
`PresheafOfModules.Sheafify.smul_restrictScalars_comparison`. -/
def sheafifyRestrictScalarsCompEquiv
    (hαβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), α'.app X (β.app X r) = b.hom.app X (α.app X r))
    (hγβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), γ.app X (β.app X r) = r)
    (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars b).obj
        (sheafify α' (restrictScalarsSheafifyMap γ M₀ φ))).val.obj X ≃ₗ[R.obj.obj X]
      (sheafify α φ).val.obj X where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := Sheafify.smul_restrictScalars_comparison α α' b β γ φ hαβ hγβ X r x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Sheafification of presheaves of modules commutes with restriction of scalars along an
isomorphism of presheaves of rings.**

In the situation of `PresheafOfModules.Sheafify.smul_restrictScalars_comparison`: the sheaf of
`R`-modules associated with `M₀` and the sheaf of `R'`-modules associated with the restriction of
scalars of `M₀` along `γ`, read as a sheaf of `R`-modules along `b`, are isomorphic.  The
isomorphism is the identity on sections; only the two scalar multiplications have to be compared,
the two sheaves of modules being built on one and the same abelian sheaf `A`. -/
def sheafifyRestrictScalarsCompIso
    (hαβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), α'.app X (β.app X r) = b.hom.app X (α.app X r))
    (hγβ : ∀ (X : Cᵒᵖ) (r : R₀.obj X), γ.app X (β.app X r) = r) :
    (SheafOfModules.restrictScalars b).obj
        (sheafify α' (restrictScalarsSheafifyMap γ M₀ φ)) ≅ sheafify α φ :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun X ↦ (sheafifyRestrictScalarsCompEquiv α α' b β γ φ hαβ hγβ X).toModuleIso)
      fun {_ _} _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **The headline statement: the associated sheaf of modules is unchanged by restriction of
scalars along an isomorphism of sheaves of rings.**

Let `ι : R ≅ R'` be an isomorphism of sheaves of rings on a site `(C, J)` and let `N` be a
presheaf of `R`-modules.  Then the sheaf of `R`-modules associated with `N` is, after restriction
of scalars along `ι`, the sheaf of `R'`-modules associated with the restriction of scalars of `N`
along `ι⁻¹`.

This is `PresheafOfModules.sheafifyRestrictScalarsCompIso` with both sheafification data taken to
be identity morphisms, `b := ι.hom`, `β := ι.hom.hom` and `γ := ι.inv.hom`; the underlying
presheaf of abelian groups of a restriction of scalars being the underlying presheaf of abelian
groups of the module itself, the two sheafifications are formed from the very same abelian
sheafification morphism. -/
def sheafificationRestrictScalarsIso (ι : R ≅ R') (N : PresheafOfModules.{v} R.obj) :
    (sheafification (𝟙 R.obj)).obj N ≅
      (SheafOfModules.restrictScalars ι.hom).obj
        ((sheafification (𝟙 R'.obj)).obj ((restrictScalars ι.inv.hom).obj N)) :=
  (sheafifyRestrictScalarsCompIso (𝟙 R.obj) (𝟙 R'.obj) ι.hom ι.hom.hom ι.inv.hom
    (CategoryTheory.toSheafify J N.presheaf) (fun _ _ ↦ rfl) (fun X r ↦ by
      have h := congrArg (fun f : R ⟶ R ↦ f.hom.app X) ι.hom_inv_id
      exact RingHom.congr_fun (congrArg RingCat.Hom.hom h) r)).symm

end Sheafification

end PresheafOfModules

end
