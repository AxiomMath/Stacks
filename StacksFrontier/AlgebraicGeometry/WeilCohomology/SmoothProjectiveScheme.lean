module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist

/-!
# The category of smooth projective schemes over a field

The cohomology theories of Chapter 45 of the Stacks Project are functors on the category of
smooth projective schemes over a field `k`: schemes `X` over `k` whose structure morphism is
smooth and projective, with morphisms of schemes over `k`. Such a scheme need be neither
irreducible nor nonempty; axiom (A1) of Section 45.14 is about disjoint unions and the empty
scheme.

This file defines that category and proves the closure properties Section 45.12 asks of the
category it works in: an open and closed subscheme of a smooth projective scheme is smooth and
projective, and so is the projective bundle of a finite locally free module of constant rank.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme k`: smooth projective schemes over `k`, as an
  object property of the category of schemes over `k`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.toScheme`: the underlying scheme.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.bundleObject`: the projective bundle `𝐏(ℰ)`
  of a finite locally free module of constant rank `r + 1`, with its projection, in the form of
  clause (3)(a) of Section 45.12.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.clopenSubobject`: an open and closed subscheme,
  in the form of clause (2) of Section 45.12.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology

/-- **Smooth projective schemes over `k`**: schemes over `k` whose structure morphism is smooth
and projective (Tag 01W8). They need not be irreducible, connected or nonempty. -/
def SmoothProjectiveScheme (k : Type u) [Field k] : ObjectProperty (Over (Spec (.of k))) :=
  fun X => Smooth X.hom ∧ IsProjective X.hom

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The underlying scheme of a smooth projective scheme over `k`. -/
abbrev toScheme (k : Type u) [Field k] : (SmoothProjectiveScheme k).FullSubcategory ⥤ Scheme.{u} :=
  (SmoothProjectiveScheme k).ι ⋙ Over.forget _

/-- The structure morphism of a smooth projective scheme over `k` is smooth. -/
theorem smooth (X : (SmoothProjectiveScheme k).FullSubcategory) : Smooth X.obj.hom := X.2.1

/-- The structure morphism of a smooth projective scheme over `k` is projective. -/
theorem isProjective (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsProjective X.obj.hom := X.2.2

/-- Smoothness of the structure morphism, available to instance synthesis. -/
instance (X : (SmoothProjectiveScheme k).FullSubcategory) : Smooth X.obj.hom := X.2.1

/-- A smooth projective scheme over a field is quasi-compact. -/
instance compactSpace (X : (SmoothProjectiveScheme k).FullSubcategory) :
    CompactSpace ((toScheme k).obj X) := by
  have := (isProjective X).isProper
  exact QuasiCompact.compactSpace_of_compactSpace X.obj.hom

/-- A smooth projective scheme over `k` from a scheme over `k`. -/
abbrev mk {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (hs : Smooth f) (hp : IsProjective f) :
    (SmoothProjectiveScheme k).FullSubcategory :=
  ⟨Over.mk f, hs, hp⟩

/-- A morphism of schemes over `k` between smooth projective schemes is a morphism of the
category. -/
abbrev homMk {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : (toScheme k).obj X ⟶ (toScheme k).obj Y) (hf : f ≫ Y.obj.hom = X.obj.hom) : X ⟶ Y :=
  ObjectProperty.homMk (Over.homMk f hf)

/-- The underlying morphism of schemes of `homMk f hf` is `f`. -/
@[simp]
theorem map_homMk {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : (toScheme k).obj X ⟶ (toScheme k).obj Y) (hf : f ≫ Y.obj.hom = X.obj.hom) :
    (toScheme k).map (homMk f hf) = f := rfl

/-- A morphism of the category is a morphism of schemes over `k`. -/
theorem w {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    (toScheme k).map f ≫ Y.obj.hom = X.obj.hom :=
  Over.w f.hom

/-- A morphism of the category is determined by its underlying morphism of schemes. -/
theorem hom_ext' {X Y : (SmoothProjectiveScheme k).FullSubcategory} {f g : X ⟶ Y}
    (h : (toScheme k).map f = (toScheme k).map g) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-! ### Projective bundles -/

section Bundle

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- The projection of the projective bundle of a finite locally free module is projective. -/
theorem isProjective_bundleProj [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsProjective (Stacks.Chow.bundleProj E) := by
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have : E.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree E
  exact isProjective_schemeProjectiveBundleToBase E

/-- **The projective bundle `𝐏(ℰ)` of a finite locally free module of constant rank `r + 1` on a
smooth projective scheme over `k` is a smooth projective scheme over `k`.** -/
def bundle : (SmoothProjectiveScheme k).FullSubcategory :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  mk (Stacks.Chow.bundleProj E ≫ X.obj.hom)
    (haveI := Stacks.Chow.smooth_bundleProj E r; inferInstance)
    (IsProjective.comp (isProjective_bundleProj X E) (isProjective X))

/-- The projection `𝐏(ℰ) ⟶ X`. -/
def bundleProj : bundle X E r ⟶ X :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  homMk (Stacks.Chow.bundleProj E) rfl

/-- **Clause (3)(a) of Section 45.12**: the projective bundle with its projection, as an object
of the category of smooth projective schemes over `k`. -/
def bundleObject : BundleObject (toScheme k) X E r where
  bundle := bundle X E r
  proj := bundleProj X E r
  isBundle :=
    { rank := inferInstance
      iso := Iso.refl _
      iso_hom_comp_bundleProj := by
        simp only [Iso.refl_hom]
        rfl }

end Bundle

/-! ### Open and closed subschemes -/

/-- The inclusion of an open and closed subscheme is a closed immersion. -/
theorem isClosedImmersion_ι {Y : Scheme.{u}} {U : Y.Opens} (hU : IsClopen (U : Set Y)) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [Scheme.Opens.range_ι]; exact hU.isClosed)

/-- **An open and closed subscheme of a smooth projective scheme over `k` is smooth and
projective over `k`.** -/
def clopen (X : (SmoothProjectiveScheme k).FullSubcategory) (U : ((toScheme k).obj X).Opens)
    (hU : IsClopen (U : Set ((toScheme k).obj X))) : (SmoothProjectiveScheme k).FullSubcategory :=
  mk (U.ι ≫ X.obj.hom) inferInstance
    (Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion _ _
      (isClosedImmersion_ι hU) (isProjective X))

/-- **Clause (2) of Section 45.12**: an open and closed subscheme with its inclusion, as an object
of the category of smooth projective schemes over `k`. -/
def clopenSubobject (X : (SmoothProjectiveScheme k).FullSubcategory)
    (U : ((toScheme k).obj X).Opens) (hU : IsClopen (U : Set ((toScheme k).obj X))) :
    ClopenSubobject (toScheme k) X U where
  obj := clopen X U hU
  hom := homMk U.ι rfl
  iso := Iso.refl _
  iso_hom_comp_ι := Category.id_comp _
  exists_factor {Z} h hZ := by
    have hV : IsOpenImmersion U.ι := inferInstance
    have hrange : Set.range ((toScheme k).map h) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hZ z
    refine ⟨homMk (@IsOpenImmersion.lift _ _ _ U.ι ((toScheme k).map h) hV hrange) ?_, ?_⟩
    · have h1 := @IsOpenImmersion.lift_fac _ _ _ U.ι ((toScheme k).map h) hV hrange
      have h2 : (@IsOpenImmersion.lift _ _ _ U.ι ((toScheme k).map h) hV hrange ≫ U.ι) ≫
          X.obj.hom = Z.obj.hom := by
        rw [h1]
        exact w h
      exact (Category.assoc _ _ _).symm.trans h2
    · refine hom_ext' ?_
      change @IsOpenImmersion.lift _ _ _ U.ι ((toScheme k).map h) hV hrange ≫ U.ι = _
      exact @IsOpenImmersion.lift_fac _ _ _ U.ι _ hV _

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
