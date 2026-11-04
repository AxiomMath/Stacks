module

public import StacksFrontier.AlgebraicGeometry.Smooth.ConormalSeparated

/-!
# The module of chart-independent differences as a term of the Čech complex

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation, let `i : T ⟶ T'` be a
first-order thickening with `T'` affine and let `a : T ⟶ X` be arbitrary. Step (II) of the proof
of the infinitesimal lifting criterion [Stacks Project, Tag 02H6] reads the difference of two
local solutions of a lifting problem over a basic open `D(c)` of `T'` as an element of

`H(c) = Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) →ₗ[Γ(T, i ⁻¹ᵁ D(c))] 𝒞_{T_c/T'_c}`,

and `Stacks.Smooth.isLocalizedModule_homLoc_basicOpen` exhibits `H(c)` as the
localization of the single `Γ(T, ⊤)`-module

`N = Γ(a^*Ω_{X/S}, ⊤) →ₗ[Γ(T, ⊤)] 𝒞_{T/T'}`

away from the image of `c`. This file turns that identification into the dictionary the Čech
argument consumes: an isomorphism between the Čech coefficient module
`Stacks.RingTheory.CechAcyclicity.AwayLoc N b` and `H(c)`, for **any** `b` with
`i.appTop c = b`, carrying `Stacks.RingTheory.CechAcyclicity.resAway` to restriction of sections.

## Main definitions

* `Stacks.Smooth.homRes` is the localization map `N →ₗ[Γ(T, ⊤)] H(c)`, namely
  `IsLocalizedModule.mapExtendScalars` for restriction of sections of `a^*Ω_{X/S}` and
  `Stacks.Smooth.conormalResOpens`.


## Main results

* `Stacks.Smooth.homRes_apply`: `Stacks.Smooth.homRes` is restriction of sections on both sides.
* `Stacks.Smooth.isLocalizedModule_homRes`: `Stacks.Smooth.homRes` is a localization map away
  from any element of `Γ(T, ⊤)` equal to the image of `c`.
* `Stacks.Smooth.exists_cechHom`: the Čech coefficient module at `b` *is* `H(c)`.
* `Stacks.Smooth.cechHom_resAway`: **the dictionary.** Transported along that isomorphism, the
  Čech restriction map `Stacks.RingTheory.CechAcyclicity.resAway` is restriction of sections of
  `a^*Ω_{X/S}` on the source and `Stacks.Smooth.conormalResLE` on the target.

## Implementation notes

The whole point of the free variable `b` in `Stacks.Smooth.exists_cechHom` is that the `p`-th
term of `Stacks.RingTheory.CechAcyclicity.CechTerm` localizes `N` at `f * g (x 0) ⋯ g (x p)`, an
element of `Γ(T, ⊤)` built from the *images* of the sections cutting out the members of the
covering, and that element is never syntactically the image of a section of `𝒪_{T'}`. Were the
isomorphism produced only for `b = i.appTop c` it could not be applied to a Čech term at all.
Taking `b` free and `i.appTop c = b` as a hypothesis moves the transport into a single
`subst`, performed once in `Stacks.Smooth.isLocalizedModule_homRes`; after that nothing in the
Čech argument mentions `IsLocalizedModule.mapExtendScalars`.

`Stacks.Smooth.cechHom_resAway` is proved without the abstract comparison map
`Stacks.Smooth.homCompare`, for the same reason: that map is indexed by the submonoid generated
by `b`, so using it would reintroduce the mismatch. Instead both sides are compared directly.
For `z = LocalizedModule.mk ν 1` they agree by `Stacks.Smooth.homRes_apply` together with
`Stacks.Smooth.restrictₗ_restrictₗ` and
`Stacks.Smooth.conormalResLE_comp_conormalResOpens`, after
`IsLocalizedModule.ext` has reduced the comparison of two linear maps out of
`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c))` to their values on restrictions of global sections; and a general `z`
is `LocalizedModule.mk ν s` with `s` a power of `b`, which acts invertibly on the target because
`b ∣ b'`.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.RingTheory.CechAcyclicity

universe u

namespace Stacks.Smooth

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i)

/-- **The localization map of the module of chart-independent differences.** For `c` a global
section of `𝒪_{T'}`, the map carrying a `Γ(T, ⊤)`-linear map
`Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` to the `Γ(T, i ⁻¹ᵁ D(c))`-linear map
`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}` it induces on the localizations.

This is `IsLocalizedModule.mapExtendScalars` for the two localization maps identified by
`Stacks.Smooth.isLocalizedModule_restrictₗ_preimage_basicOpen` and
`Stacks.Smooth.isLocalizedModule_conormalResOpens_basicOpen`; naming it is what lets the
statements below avoid mentioning the submonoid it is indexed by. -/
noncomputable def homRes (c : Γ(T', (⊤ : T'.Opens))) :
    haveI : IsClosedImmersion i := hi.1
    haveI : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTowerOfLE (pullbackCotangentSheaf f a)
      (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isLocalization_preimage_basicOpen i c
    letI := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
    letI := isLocalizedModule_conormalResOpens_basicOpen hi c
    (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        RingHom.ker i.appTop.hom) →ₗ[Γ(T, (⊤ : T.Opens))]
      (Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom) :=
  haveI : IsClosedImmersion i := hi.1
  haveI : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c
  letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  letI := thickeningKerModule hi
  letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  letI := isScalarTowerOfLE (pullbackCotangentSheaf f a)
    (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  letI := isLocalization_preimage_basicOpen i c
  letI := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
  letI := isLocalizedModule_conormalResOpens_basicOpen hi c
  IsLocalizedModule.mapExtendScalars (Submonoid.powers (i.appTop.hom c))
    (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤))
    (conormalResOpens hi (T'.basicOpen c)) Γ(T, i ⁻¹ᵁ T'.basicOpen c)

/-- **`Stacks.Smooth.homRes` is restriction of sections.** The localization of a global linear
map `ν`, evaluated at the restriction to `i ⁻¹ᵁ D(c)` of a global section of `a^*Ω_{X/S}`, is the
restriction to `𝒞_{T_c/T'_c}` of the value of `ν` at that section. -/
theorem homRes_apply (c : Γ(T', (⊤ : T'.Opens)))
    (ν : letI := thickeningKerModule hi
      Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        RingHom.ker i.appTop.hom)
    (y : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens))) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := thickeningKerModule hi
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    homRes f a hi c ν (restrictₗ (pullbackCotangentSheaf f a)
        (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤) y)
      = conormalResOpens hi (T'.basicOpen c) (ν y) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a)
    (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isLocalization_preimage_basicOpen i c
  let := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
  let := isLocalizedModule_conormalResOpens_basicOpen hi c
  exact mapExtendScalars_apply_localizationMap
    (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤))
    (conormalResOpens hi (T'.basicOpen c)) ν y

/-- **`Stacks.Smooth.homRes` is a localization map.** The module of `Γ(T, i ⁻¹ᵁ D(c))`-linear
maps `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}` is the localization of the module of
`Γ(T, ⊤)`-linear maps `Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` away from any element of `Γ(T, ⊤)` equal to
the image of `c`.

The free variable `b` is what makes this applicable to a term of
`Stacks.RingTheory.CechAcyclicity.CechTerm`, whose index is a product of images of sections and
never syntactically an image. -/
theorem isLocalizedModule_homRes [LocallyOfFinitePresentation f] (c : Γ(T', (⊤ : T'.Opens)))
    (b : Γ(T, (⊤ : T.Opens))) (hb : i.appTop.hom c = b) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := thickeningKerModule hi
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    IsLocalizedModule (Submonoid.powers b) (homRes f a hi c) := by
  subst hb
  exact isLocalizedModule_homLoc_basicOpen f a hi c

/-- `Stacks.Smooth.conormalResOpens` at a basic open is a localization map away from any element
of `Γ(T, ⊤)` equal to the image of the section. -/
theorem isLocalizedModule_conormalResOpens_eq (c : Γ(T', (⊤ : T'.Opens)))
    (b : Γ(T, (⊤ : T.Opens))) (hb : i.appTop.hom c = b) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    IsLocalizedModule (Submonoid.powers b) (conormalResOpens hi (T'.basicOpen c)) := by
  subst hb
  exact isLocalizedModule_conormalResOpens_basicOpen hi c

include hi in
/-- Restriction of sections of `a^*Ω_{X/S}` to the closed subscheme of a basic open is a
localization map away from any element of `Γ(T, ⊤)` equal to the image of the section. -/
theorem isLocalizedModule_restrictₗ_eq (c : Γ(T', (⊤ : T'.Opens)))
    (b : Γ(T, (⊤ : T.Opens))) (hb : i.appTop.hom c = b) :
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    IsLocalizedModule (Submonoid.powers b)
      (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  subst hb
  exact isLocalizedModule_restrictₗ_preimage_basicOpen f a i c

/-- Powers of a divisor `b` of `b'` act invertibly on the target of a localization map away
from `b'`. -/
private theorem isUnit_algebraMap_powers_of_isLocalizedModule {A M N : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] {b b' : A} (hd : b ∣ b')
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers b') g] (s : Submonoid.powers b) :
    IsUnit (algebraMap A (Module.End A N) (s : A)) :=
  isUnit_algebraMap_powers_of_dvd hd
    (IsLocalizedModule.map_units g (⟨b', Submonoid.mem_powers b'⟩ : Submonoid.powers b')) s

/-- **The localization map `Stacks.Smooth.homRes` is compatible with restriction of sections.**
For `D(c') ≤ D(c)` with the image of `c` dividing the image of `c'`, the localization of a
global linear map `ν` to `D(c')`, evaluated at the restriction of a section over `i ⁻¹ᵁ D(c)`, is
the `Stacks.Smooth.conormalResLE`-restriction of its localization to `D(c)` evaluated there.

Both sides are `Γ(T, ⊤)`-linear in the section and agree on the restrictions of global sections
by `Stacks.Smooth.homRes_apply`, `Stacks.Smooth.restrictₗ_restrictₗ` and
`Stacks.Smooth.conormalResLE_comp_conormalResOpens`, so `IsLocalizedModule.ext` applies. -/
theorem homRes_conormalResLE (c c' : Γ(T', (⊤ : T'.Opens)))
    (hcc' : T'.basicOpen c' ≤ T'.basicOpen c) (b b' : Γ(T, (⊤ : T.Opens)))
    (hb : i.appTop.hom c = b) (hb' : i.appTop.hom c' = b') (hd : b ∣ b')
    (ν : letI := thickeningKerModule hi
      Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        RingHom.ker i.appTop.hom)
    (w : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c)) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c'
    letI := thickeningKerModule hi
    letI := moduleOfLE (pullbackCotangentSheaf f a)
      (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
    homRes f a hi c' ν (restrictₗ (pullbackCotangentSheaf f a)
        (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) w)
      = conormalResLE hi hcc' (homRes f a hi c ν w) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c
  let : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c'
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c) (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c') (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a)
    (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
  let := isScalarTowerOfLE_of_le (pullbackCotangentSheaf f a)
    (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
  let := isLocalizedModule_conormalResOpens_eq hi c' b' hb'
  let := isLocalizedModule_restrictₗ_eq f a hi c b hb
  have hunit := isUnit_algebraMap_powers_of_isLocalizedModule hd
    (conormalResOpens hi (T'.basicOpen c'))
  have key : ((homRes f a hi c' ν).restrictScalars Γ(T, (⊤ : T.Opens))).comp
        ((restrictₗ (pullbackCotangentSheaf f a)
          (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from
            fun _ hx ↦ hcc' hx)).restrictScalars Γ(T, (⊤ : T.Opens)))
      = (conormalResLE hi hcc').comp
          ((homRes f a hi c ν).restrictScalars Γ(T, (⊤ : T.Opens))) := by
    refine IsLocalizedModule.ext (Submonoid.powers b)
      (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)) hunit
      (LinearMap.ext fun y ↦ ?_)
    show homRes f a hi c' ν (restrictₗ (pullbackCotangentSheaf f a) _
        (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤) y))
      = conormalResLE hi hcc' (homRes f a hi c ν
        (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤) y))
    exact ((congrArg (homRes f a hi c' ν)
        (restrictₗ_restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
          (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) y)).trans
      (homRes_apply f a hi c' ν y)).trans
      ((congrArg (conormalResLE hi hcc') (homRes_apply f a hi c ν y)).trans
        (conormalResLE_comp_conormalResOpens hi hcc' (ν y))).symm
  exact LinearMap.congr_fun key w

/-- **The Čech coefficient module at a basic open.** For `b` any element of `Γ(T, ⊤)` equal to
the image of `c`, the localization of `N = Γ(a^*Ω_{X/S}, ⊤) →ₗ[Γ(T, ⊤)] 𝒞_{T/T'}` at the powers
of `b` — which is the term of `Stacks.RingTheory.CechAcyclicity.CechTerm` attached to `b` — is
the module of `Γ(T, i ⁻¹ᵁ D(c))`-linear maps `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}`, by an
isomorphism carrying the class of a global linear map to its localization
`Stacks.Smooth.homRes`.

The isomorphism is produced through an `∃` rather than named, because its construction
`IsLocalizedModule.iso` carries the whole stack of restriction-of-scalars instances of
`Stacks.Smooth.homRes` in its type; unfolding it inside a rewrite exhausts the heartbeat budget,
whereas the two properties recorded here are all the Čech argument uses. -/
theorem exists_cechHom [LocallyOfFinitePresentation f] (c : Γ(T', (⊤ : T'.Opens)))
    (b : Γ(T, (⊤ : T.Opens))) (hb : i.appTop.hom c = b) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := thickeningKerModule hi
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    ∃ Φ : AwayLoc (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
          RingHom.ker i.appTop.hom) b ≃ₗ[Γ(T, (⊤ : T.Opens))]
        (Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
          RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom),
      ∀ ν, Φ (LocalizedModule.mk ν 1) = homRes f a hi c ν := by
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c
  let := thickeningKerModule hi
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c) (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isLocalizedModule_homRes f a hi c b hb
  exact ⟨IsLocalizedModule.iso (Submonoid.powers b) (homRes f a hi c),
    IsLocalizedModule.iso_mk_one (Submonoid.powers b) (homRes f a hi c)⟩

/-- **The Čech restriction map is restriction of sections.** Let `D(c') ≤ D(c)` be basic opens of
`T'` and let `b`, `b'` be elements of `Γ(T, ⊤)` equal to the images of `c`, `c'` with `b ∣ b'`.
Let `Φ`, `Φ'` be the identifications of `Stacks.Smooth.exists_cechHom` at `c` and at `c'`. Then
`Stacks.RingTheory.CechAcyclicity.resAway` from the Čech term at `b` to the Čech term at `b'`
corresponds to restriction of sections of `a^*Ω_{X/S}` on the source and
`Stacks.Smooth.conormalResLE` on the target.

This is the only property of the Čech restriction maps that step (II) of
[Stacks Project, Tag 02H6] uses. Both sides are `Γ(T, ⊤)`-linear in the Čech class, and the
class of a global linear map is handled by `Stacks.Smooth.homRes_conormalResLE`; a general class
is a quotient `LocalizedModule.mk ν s` by a power of `b`, which acts invertibly on the target
because `b ∣ b'`. -/
theorem cechHom_resAway (c c' : Γ(T', (⊤ : T'.Opens)))
    (hcc' : T'.basicOpen c' ≤ T'.basicOpen c) (b b' : Γ(T, (⊤ : T.Opens)))
    (hb : i.appTop.hom c = b) (hb' : i.appTop.hom c' = b') (hd : b ∣ b')
    (Φ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := thickeningKerModule hi
      letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      AwayLoc (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
          RingHom.ker i.appTop.hom) b ≃ₗ[Γ(T, (⊤ : T.Opens))]
        (Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
          RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom))
    (hΦ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := thickeningKerModule hi
      ∀ ν, Φ (LocalizedModule.mk ν 1) = homRes f a hi c ν)
    (Φ' : letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c'
      letI := thickeningKerModule hi
      letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
      letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
        (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
      letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
        (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
      letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
        (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
      AwayLoc (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
          RingHom.ker i.appTop.hom) b' ≃ₗ[Γ(T, (⊤ : T.Opens))]
        (Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c') →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c')]
          RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom))
    (hΦ' : letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c'
      letI := thickeningKerModule hi
      ∀ ν, Φ' (LocalizedModule.mk ν 1) = homRes f a hi c' ν)
    (z : letI := thickeningKerModule hi
      AwayLoc (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        RingHom.ker i.appTop.hom) b)
    (w : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c)) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c'
    letI := thickeningKerModule hi
    letI := moduleOfLE (pullbackCotangentSheaf f a)
      (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
    Φ' (resAway _ hd z) (restrictₗ (pullbackCotangentSheaf f a)
        (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) w)
      = conormalResLE hi hcc' (Φ z w) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c
  let : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) := (isAffineOpen_top T').basicOpen c'
  let := thickeningKerModule hi
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c) (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c') (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a)
    (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
  let := isLocalizedModule_conormalResOpens_eq hi c' b' hb'
  induction z using LocalizedModule.induction_on with
  | _ ν s =>
    have hunit := isUnit_algebraMap_powers_of_isLocalizedModule hd
      (conormalResOpens hi (T'.basicOpen c')) s
    have hsν : ((s : Γ(T, (⊤ : T.Opens))) • LocalizedModule.mk ν s :
        AwayLoc (Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
          RingHom.ker i.appTop.hom) b) = LocalizedModule.mk ν 1 := by
      rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
    have e1 : (s : Γ(T, (⊤ : T.Opens))) • resAway _ hd (LocalizedModule.mk ν s)
        = LocalizedModule.mk ν 1 :=
      (map_smul (resAway _ hd) (s : Γ(T, (⊤ : T.Opens)))
          (LocalizedModule.mk ν s)).symm.trans
        ((congrArg (resAway _ hd) hsν).trans (resAway_mk_one hd ν))
    have e2 : (s : Γ(T, (⊤ : T.Opens))) • Φ' (resAway _ hd (LocalizedModule.mk ν s))
        = homRes f a hi c' ν :=
      (map_smul Φ' (s : Γ(T, (⊤ : T.Opens)))
          (resAway _ hd (LocalizedModule.mk ν s))).symm.trans
        ((congrArg Φ' e1).trans (hΦ' ν))
    have e3 : (s : Γ(T, (⊤ : T.Opens))) • Φ (LocalizedModule.mk ν s) = homRes f a hi c ν :=
      (map_smul Φ (s : Γ(T, (⊤ : T.Opens))) (LocalizedModule.mk ν s)).symm.trans
        ((congrArg Φ hsν).trans (hΦ ν))
    have hL : (s : Γ(T, (⊤ : T.Opens))) • (Φ' (resAway _ hd (LocalizedModule.mk ν s))
          (restrictₗ (pullbackCotangentSheaf f a)
          (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) w))
        = homRes f a hi c' ν (restrictₗ (pullbackCotangentSheaf f a)
          (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) w) :=
      (LinearMap.smul_apply _ _ _).symm.trans (congrArg (fun φ ↦ φ (restrictₗ
        (pullbackCotangentSheaf f a) (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from
          fun _ hx ↦ hcc' hx) w)) e2)
    have hR : (s : Γ(T, (⊤ : T.Opens))) • conormalResLE hi hcc' (Φ (LocalizedModule.mk ν s) w)
        = conormalResLE hi hcc' (homRes f a hi c ν w) :=
      (map_smul (conormalResLE hi hcc') (s : Γ(T, (⊤ : T.Opens)))
          (Φ (LocalizedModule.mk ν s) w)).symm.trans
        (congrArg (conormalResLE hi hcc')
          ((LinearMap.smul_apply _ _ _).symm.trans (congrArg (fun φ ↦ φ w) e3)))
    exact ((Module.End.isUnit_iff _).mp hunit).1
      (hL.trans ((homRes_conormalResLE f a hi c c' hcc' b b' hb hb' hd ν w).trans hR.symm))

end Stacks.Smooth

end
