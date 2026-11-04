module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms

/-!
# Higher direct images commute with restriction to an open of the base, for schemes

[Stacks, Tag 01E5] says that for a morphism `f : X ⟶ S`, an open `V ⊆ S` and `U = f⁻¹(V)`,

  `(R ᵖ f_* ℱ)|_V ≅ R ᵖ (f|_U)_* (ℱ|_U)`,

naturally in `ℱ`. The library's form of Tag 01E5 proves it — but for a morphism
of **ringed spaces**, in terms of `RingedSpaceModuleAdjunction.modulePushforward` and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, and with the restricted morphism its own
bespoke construction `restrictedMorphism`. No goal about schemes is phrased that way: the schemes
material uses `AlgebraicGeometry.Scheme.Modules.pushforward`,
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` and Mathlib's `f ∣_ V`. This file closes that
gap, in both indexings of the right derived functor.

The gap was not a universe or a transparency problem: three of the four identifications needed
are definitional, and this file measures them. What is *not* definitional is the restricted
morphism, because Mathlib builds `f ∣_ V` through `IsOpenImmersion.lift` while
`restrictedMorphism` is assembled by hand from a base map and a map of structure sheaves; they are
nevertheless equal, and `restrictedMorphism_eq` proves it by cancelling the monomorphism `V.ι`
against the two factorizations `f|_U ≫ V.ι = U.ι ≫ f`.

## Main results

* `AlgebraicGeometry.ProjectiveCoherentImage.restrictedMorphism_eq`: the ringed-space restricted
  morphism of [Stacks, Tag 01E5] is Mathlib's `f ∣_ V`.
* `AlgebraicGeometry.ProjectiveCoherentImage.restrictFunctorIso`: Mathlib's restriction of sheaves
  of modules along `V.ι` is the ringed-space `moduleRestriction`.
* `AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme`: **[Stacks, Tag
  01E5] for schemes**, for the `ℕ`-indexed `Functor.rightDerived`.
* `AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictPlusIso`: the same for the
  `ℤ`-indexed `Functor.rightDerivedPlus`, which is the indexing the statements of Tags 02O4 and
  02O5 use.
* `AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`: its value at a
  single sheaf of modules, which is the form a coherence argument consumes.

## Implementation notes

**The four identifications.** For `f : X ⟶ S` of schemes and `V : S.Opens`, writing `f'` for the
underlying morphism of ringed spaces `f.toLRSHom.toShHom`:

* `structureSheafRing X.toRingedSpace = X.ringCatSheaf` — definitional;
* `Scheme.Modules.pushforward f = modulePushforward f'` — definitional;
* `Stacks.Cohomology.HigherDirectImage.restrictToOpen X.toRingedSpace V = V.toScheme.toRingedSpace`
  and `preimageOpen f' V = f ⁻¹ᵁ V` — definitional;
* `Scheme.Modules.restrictFunctor V.ι = moduleRestriction X.toRingedSpace V` — **not**
  definitional, because Mathlib's restriction carries the comparison
  `(V.ι.appIso W).inv` where the ringed-space one carries the identity. The two comparisons are
  equal (`Scheme.Opens.ι_appIso`), so `SheafOfModules.pushforwardCongr` gives the isomorphism
  `restrictFunctorIso`; it is an isomorphism rather than an equality only because that is all
  `pushforwardCongr` returns.

**Why the transport is `simp only` and not `rw`.** The two pushforward functors
`Scheme.Modules.pushforward (f ∣_ V)` and `modulePushforward (restrictedMorphism f' V)` are equal
(`pushforward_morphismRestrict_eq`), but rewriting one into the other inside
`Functor.rightDerived p` is not a type-correct motive: that functor takes the additivity of its
argument as an instance argument. `simp only` discharges exactly this, since the dependency is on
a proof of a `Prop`-valued class.

**Why no generic restricted morphism.** The natural formulation — the isomorphism for any
`g : restrictToOpen X (f ⁻¹ᵁ V) ⟶ restrictToOpen S V` equal to `restrictedMorphism f' V`, proved
by `subst` — cannot even be stated: `(modulePushforward g).Additive` is not found for a variable
`g` between restricted ringed spaces. The instance that fires for `restrictedMorphism f' V` is
the bespoke `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictedMorphism_additive`,
and the generic `modulePushforward_additive` does not apply at the `Preadditive` instance path
these categories acquire. Hence the transport is done on the scheme side.

**No `stacks` attribute is attached.** Every label of Tag 01E5 — `"higher direct images"`,
`"degree-zero compatibility"`, `"bounded below derived image"`, `"compatibility with derived
units"`, `"compatibility with injective resolutions"` — is already carried by
the ringed-space statements of Tag 01E5, which are strictly
more general than the scheme ones proved here. Attaching a label
again would record the same mathematics twice, and no label of the tag is unclaimed.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace AlgebraicGeometry.ProjectiveCoherentImage

/-! ### The comparison of the scheme and ringed-space spellings -/

variable {X S : Scheme.{u}}

/-- **Restriction of sheaves of modules to an open subscheme is the ringed-space restriction.**
Both are a sheaf pushforward along the open-image functor of the inclusion; Mathlib's carries the
comparison of structure sheaves `(V.ι.appIso W).inv` and the ringed-space one carries the
identity, and `Scheme.Opens.ι_appIso` says these agree. -/
noncomputable def restrictFunctorIso (X : Scheme.{u}) (V : X.Opens) :
    Scheme.Modules.restrictFunctor V.ι ≅ moduleRestriction X.toRingedSpace V :=
  SheafOfModules.pushforwardCongr (by ext W x; simp; rfl)

/-- **The restricted morphism of [Stacks, Tag 01E5] is Mathlib's `f ∣_ V`.** Both factor the
inclusion of `f⁻¹(V)` followed by `f` through the inclusion of `V`
(`restrictedMorphism_comp_openSubspaceInclusion`, `AlgebraicGeometry.morphismRestrict_ι`), and
the inclusion of an open subscheme is a monomorphism of sheafed spaces. -/
theorem restrictedMorphism_eq (f : X ⟶ S) (V : S.Opens) :
    restrictedMorphism f.toLRSHom.toShHom V = (f ∣_ V).toLRSHom.toShHom := by
  have hmono : Mono (openSubspaceInclusion S.toRingedSpace V) := by
    change Mono V.ι.toLRSHom.toShHom
    infer_instance
  have key : restrictedMorphism f.toLRSHom.toShHom V ≫ openSubspaceInclusion S.toRingedSpace V =
      (f ∣_ V).toLRSHom.toShHom ≫ openSubspaceInclusion S.toRingedSpace V := by
    rw [← restrictedMorphism_comp_openSubspaceInclusion]
    change _ = ((f ∣_ V) ≫ V.ι).toLRSHom.toShHom
    rw [morphismRestrict_ι]
    rfl
  exact (cancel_mono _).1 key

/-- Pushforward along `f ∣_ V` is pushforward along the ringed-space restricted morphism. -/
theorem pushforward_morphismRestrict_eq (f : X ⟶ S) (V : S.Opens) :
    Scheme.Modules.pushforward (f ∣_ V) =
      modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) := by
  rw [restrictedMorphism_eq]
  rfl

/-! ### Stacks 01E5 for schemes -/

/-- **[Stacks, Tag 01E5] for schemes, `ℕ`-indexed.** For `f : X ⟶ S` and `V : S.Opens`,
restricting a sheaf of `𝒪_X`-modules to `f⁻¹(V)` and taking the `p`-th higher direct image along
`f ∣_ V` agrees with taking the `p`-th higher direct image along `f` and restricting to `V`,
naturally in the sheaf of modules.

This is the ringed-space statement
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`, read through
`restrictFunctorIso` and `pushforward_morphismRestrict_eq`. -/
noncomputable def higherDirectImageRestrictIsoScheme (f : X ⟶ S) (V : S.Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ≅
        (Scheme.Modules.pushforward f).rightDerived p ⋙
          Scheme.Modules.restrictFunctor V.ι := by
  simp only [pushforward_morphismRestrict_eq f V]
  exact Functor.isoWhiskerRight (restrictFunctorIso X (f ⁻¹ᵁ V)) _ ≪≫
    higherDirectImageRestrictIso f.toLRSHom.toShHom V p ≪≫
    Functor.isoWhiskerLeft _ (restrictFunctorIso S V).symm

section Plus

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 01E5] for schemes, `ℤ`-indexed.** The same isomorphism for the bounded-below
right derived functor `Functor.rightDerivedPlus`, in a degree that is a natural number. This is
the indexing in which the statements of [Stacks, Tag 02O4] and [Stacks, Tag 02O5] state higher direct
images, so it is the form a coherence argument on the base consumes.

The comparison of the two indexings is `Stacks.DerivedIndexing.rightDerivedIso`. -/
noncomputable def higherDirectImageRestrictPlusIso (f : X ⟶ S) (V : S.Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ) ≅
        (Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ) ⋙
          Scheme.Modules.restrictFunctor V.ι :=
  Functor.isoWhiskerLeft _
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).symm ≪≫
    higherDirectImageRestrictIsoScheme f V p ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p) _

/-- **[Stacks, Tag 01E5] for schemes, at one sheaf of modules.** The `p`-th higher direct image
along `f ∣_ V` of the restriction of `F` to `f⁻¹(V)` is the restriction to `V` of the `p`-th
higher direct image of `F` along `f`. -/
noncomputable def higherDirectImageRestrictObjIso (f : X ⟶ S) (V : S.Opens) (F : X.Modules)
    (p : ℕ) :
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≅
        (Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) :=
  (higherDirectImageRestrictPlusIso f V p).app F

end Plus

end AlgebraicGeometry.ProjectiveCoherentImage

end
