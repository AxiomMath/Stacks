module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections on `Spec A ∖ V(J)` read inside `Spec A ∖ V(𝔞)`

Let `A` be a commutative ring and let `J ⊆ 𝔞` be ideals, so that
`V = Spec A ∖ V(J)` is contained in `U = Spec A ∖ V(𝔞)` and appears as the open
`Stacks.Algebraization.opensOffVanishing A J 𝔞` of `U`. There are then two ways to regard the
`A`-module of sections on `V` of a sheaf of modules `F` on `Spec A`:

* evaluate `F` at the open `V` of `Spec A`, which is
  `Stacks.LocalCohomology.sectionsOnAffineComplement A J`, the functor whose total right derived
  functor is derived sections on `V`;
* restrict `F` along the open immersion `ι : U ⟶ Spec A` and evaluate the restriction at the open
  `U ∖ V(J)` of `U`.

As with the two descriptions of global sections, these are not equal: evaluating the restriction
at `U ∖ V(J)` gives the sections on `ι ''ᵁ (U ∖ V(J))`, and
`ι ''ᵁ (U ∖ V(J)) = V` is a propositional equality of opens
(`AlgebraicGeometry.Scheme.Opens.image_preimage_ι`, which needs `V ≤ U`), not a definitional one.
This file provides the natural isomorphism between them.

This is the `J ⊆ 𝔞` generalization of `Stacks.LocalCohomology.sectionsOnAffineComplementIso`,
which is the case `𝔞 = J`: there the open of `U` is `⊤` and the equality of opens is
`AlgebraicGeometry.Scheme.Opens.ι_image_top`. The two statements are not instances of one
another: there the `A`-module structure on the left is the one global sections on `U` carry, taken
along `A ⟶ Γ(U, ⊤)`, and the comparison has to identify it with the structure coming from
`Spec A`, whereas here the structure is taken along `A ⟶ Γ(Spec A, ι ''ᵁ (U ∖ V(J)))` from the
outset — the two section rings being the same ring, which is what makes
`AlgebraicGeometry.Scheme.Opens.ι_appIso` an identity. So one step of that comparison is absent
here; the rest of the argument, and both ring-side agreements, are as they are there.

## Main definitions

* `Stacks.Algebraization.sectionsOffVanishing` — sections on `U ∖ V(J)` of the restriction to `U`
  of a sheaf of modules on `Spec A`, as an `A`-module.
* `Stacks.Algebraization.offVanishingSectionsHom`,
  `Stacks.Algebraization.offVanishingSectionsInv` — the comparison maps.
* `Stacks.Algebraization.sectionsOffVanishingIso` — **the isomorphism**
  `sectionsOffVanishing J 𝔞 F ≅ (sectionsOnAffineComplement A J).obj F`, natural in `F` by
  `Stacks.Algebraization.offVanishingSectionsHom_naturality`.

## Main results

* `Stacks.Algebraization.complementZeroLocus_le_of_le` — the complement of a zero locus grows
  with the ideal, so `V ⊆ U`.
* `Stacks.Algebraization.ι_image_opensOffVanishing` — the image of `U ∖ V(J)` in `Spec A` is `V`.
* `Stacks.Algebraization.complementScalars_eq_comp`,
  `Stacks.Algebraization.offVanishingImageScalars_eq_comp` — the two `A`-algebra structures on
  sections agree, in both directions.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (J a : Ideal A)

/-! ### The two open subsets -/

/-- **The complement of a zero locus grows with the ideal.** For `J ⊆ 𝔞` the open
`V = Spec A ∖ V(J)` is contained in `U = Spec A ∖ V(𝔞)`, the zero locus being antitone. -/
@[ega "I 1.1.2" "(ii) for ideals"]
theorem complementZeroLocus_le_of_le (hJ : J ≤ a) :
    complementZeroLocus A J ≤ complementZeroLocus A a :=
  Set.compl_subset_compl.2 (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ)

/-- **The image of `U ∖ V(J)` in `Spec A` is `V = Spec A ∖ V(J)`.** The open `U ∖ V(J)` of `U` is
by definition the preimage of `V` along `ι`, and `V` is contained in `U`. -/
theorem ι_image_opensOffVanishing (hJ : J ≤ a) :
    (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a = complementZeroLocus A J :=
  Scheme.Opens.image_preimage_ι (complementZeroLocus A a)
    (complementZeroLocus_le_of_le J a hJ)

/-- One of the two inclusions coming from `ι ''ᵁ (U ∖ V(J)) = V`. -/
theorem complementZeroLocus_le_ι_image_opensOffVanishing (hJ : J ≤ a) :
    complementZeroLocus A J ≤ (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a :=
  le_of_eq (ι_image_opensOffVanishing J a hJ).symm

/-- The reverse inclusion. -/
theorem ι_image_opensOffVanishing_le_complementZeroLocus (hJ : J ≤ a) :
    (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a ≤ complementZeroLocus A J :=
  le_of_eq (ι_image_opensOffVanishing J a hJ)

/-! ### The scalars -/

/-- The structure map `A ⟶ Γ(Spec A, ι ''ᵁ (U ∖ V(J)))` defining the `A`-module structure on the
sections on `U ∖ V(J)` of a sheaf of modules on `U`.

The sections of the structure sheaf of `U` on `U ∖ V(J)` and those of the structure sheaf of
`Spec A` on the image `ι ''ᵁ (U ∖ V(J))` are the same ring — that is what makes
`AlgebraicGeometry.Scheme.Opens.ι_appIso` an identity — so this is at the same time the structure
map `A ⟶ Γ(U, U ∖ V(J))`, and it is the one `Stacks.LocalCohomology.complementScalars` would give
were `ι ''ᵁ (U ∖ V(J))` already written as `V`. -/
abbrev offVanishingImageScalars :
    A →+* Γ(Spec (CommRingCat.of A), (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
      (homOfLE (le_top
        (a := (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a))).op).hom.comp
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv)

/-- The restriction map on structure sheaf sections from `ι ''ᵁ (U ∖ V(J))` to `V`. -/
abbrev imageOffVanishingToComplementScalars (hJ : J ≤ a) :
    Γ(Spec (CommRingCat.of A), (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a) →+*
      Γ(Spec (CommRingCat.of A), complementZeroLocus A J) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
    (homOfLE (complementZeroLocus_le_ι_image_opensOffVanishing J a hJ)).op).hom

/-- The restriction map on structure sheaf sections from `V` to `ι ''ᵁ (U ∖ V(J))`. -/
abbrev complementToImageOffVanishingScalars (hJ : J ≤ a) :
    Γ(Spec (CommRingCat.of A), complementZeroLocus A J) →+*
      Γ(Spec (CommRingCat.of A), (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
    (homOfLE (ι_image_opensOffVanishing_le_complementZeroLocus J a hJ)).op).hom

/-- The `A`-module structure on sections on `V` obtained by restricting to `V` directly agrees
with the one obtained through `ι ''ᵁ (U ∖ V(J))`: the two restriction maps
`Γ(Spec A, ⊤) ⟶ Γ(Spec A, V)` that arise are equal, the opens of a scheme forming a poset. -/
theorem complementScalars_eq_comp (hJ : J ≤ a) :
    complementScalars J =
      (imageOffVanishingToComplementScalars J a hJ).comp (offVanishingImageScalars J a) :=
  RingHom.ext fun x =>
    (ConcreteCategory.congr_hom (((Spec (CommRingCat.of A)).presheaf.map_comp
      (homOfLE (le_top
        (a := (complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a))).op
      (homOfLE (complementZeroLocus_le_ι_image_opensOffVanishing J a hJ)).op).symm)
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) x)).symm

/-- The same agreement in the other direction. -/
theorem offVanishingImageScalars_eq_comp (hJ : J ≤ a) :
    offVanishingImageScalars J a =
      (complementToImageOffVanishingScalars J a hJ).comp (complementScalars J) :=
  RingHom.ext fun x =>
    ConcreteCategory.congr_hom ((Spec (CommRingCat.of A)).presheaf.map_comp
      (homOfLE (le_top (a := complementZeroLocus A J))).op
      (homOfLE (ι_image_opensOffVanishing_le_complementZeroLocus J a hJ)).op)
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) x)

/-! ### The comparison of sections -/

/-- The sections on `U ∖ V(J)` of the restriction to `U = Spec A ∖ V(𝔞)` of a sheaf of modules `F`
on `Spec A`, as an `A`-module: the sections of `F` on the image `ι ''ᵁ (U ∖ V(J))`, with scalars
restricted along `Stacks.Algebraization.offVanishingImageScalars`.

This is the sections on the open `U ∖ V(J)` of `U` of the restriction of `F` along `ι`: the
functor `Stacks.LocalCohomology.restrictFunctor` is a pushforward along `ι.opensFunctor`, so it
evaluates at an open of `U` by evaluating `F` at the image of that open, and the two `A`-module
structures agree because `AlgebraicGeometry.Scheme.Opens.ι_appIso` is an identity. It is written
on the `Spec A` side here so that the open at which `F` is evaluated — which is what the
comparison below moves — stays visible. -/
abbrev sectionsOffVanishing (F : (Spec (CommRingCat.of A)).Modules) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (offVanishingImageScalars J a)).obj
    (F.val.obj (op ((complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a)))

variable (F : (Spec (CommRingCat.of A)).Modules)

/-- The comparison from the sections on `U ∖ V(J)` of the restriction of `F` to `U` to the
sections of `F` on the open `V` of `Spec A`: restriction along `V ≤ ι ''ᵁ (U ∖ V(J))`, with the
two `A`-module structures identified. -/
def offVanishingSectionsHom (hJ : J ≤ a) :
    sectionsOffVanishing J a F ⟶ (sectionsOnAffineComplement A J).obj F :=
  (ModuleCat.restrictScalars (offVanishingImageScalars J a)).map
      (F.val.map (homOfLE (complementZeroLocus_le_ι_image_opensOffVanishing J a hJ)).op) ≫
    (ModuleCat.restrictScalarsComp'App (offVanishingImageScalars J a)
      (imageOffVanishingToComplementScalars J a hJ) (complementScalars J)
      (complementScalars_eq_comp J a hJ)
      (F.val.obj (op (complementZeroLocus A J)))).inv

/-- The comparison in the other direction: restriction along `ι ''ᵁ (U ∖ V(J)) ≤ V`. -/
def offVanishingSectionsInv (hJ : J ≤ a) :
    (sectionsOnAffineComplement A J).obj F ⟶ sectionsOffVanishing J a F :=
  (ModuleCat.restrictScalars (complementScalars J)).map
      (F.val.map (homOfLE (ι_image_opensOffVanishing_le_complementZeroLocus J a hJ)).op) ≫
    (ModuleCat.restrictScalarsComp'App (complementScalars J)
      (complementToImageOffVanishingScalars J a hJ) (offVanishingImageScalars J a)
      (offVanishingImageScalars_eq_comp J a hJ)
      (F.val.obj (op ((complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a)))).inv

/-- Restricting along `f` and then along `g` is the identity when `f ≫ g = 𝟙`. -/
private theorem presheafOfModules_map_map_apply_of_comp_eq_id {C : Type*} [Category C]
    {Rg : Cᵒᵖ ⥤ RingCat} (M : PresheafOfModules Rg) {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) (x : M.obj X) : M.map g (M.map f x) = x :=
  (PresheafOfModules.map_comp_apply M f g x).symm.trans
    ((M.congr_map_apply h x).trans (presheafOfModules_map_id_apply M X x))

/-- The two comparisons are mutually inverse: the restriction maps between sections on equal
opens compose to the identity. -/
theorem offVanishingSectionsHom_inv_id (hJ : J ≤ a) :
    offVanishingSectionsHom J a F hJ ≫ offVanishingSectionsInv J a F hJ = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    presheafOfModules_map_map_apply_of_comp_eq_id F.val _ _ rfl x)

/-- The two comparisons are mutually inverse in the other order. -/
theorem offVanishingSectionsInv_hom_id (hJ : J ≤ a) :
    offVanishingSectionsInv J a F hJ ≫ offVanishingSectionsHom J a F hJ = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    presheafOfModules_map_map_apply_of_comp_eq_id F.val _ _ rfl x)

/-- **The two descriptions of sections on `V = Spec A ∖ V(J)` agree, for `J ⊆ 𝔞`.** Restricting a
sheaf of modules on `Spec A` along the open immersion of `U = Spec A ∖ V(𝔞)` and evaluating at the
open `U ∖ V(J)` of `U` gives the same `A`-module as evaluating it at the open `V` of `Spec A`.

The two differ exactly by the propositional equality `ι ''ᵁ (U ∖ V(J)) = V` of opens, so this is
the transport along that equality, including the agreement of the two `A`-module structures. For
`𝔞 = J` the open `U ∖ V(J)` is `⊤` and this is
`Stacks.LocalCohomology.sectionsOnAffineComplementIso`. -/
def sectionsOffVanishingIso (hJ : J ≤ a) :
    sectionsOffVanishing J a F ≅ (sectionsOnAffineComplement A J).obj F where
  hom := offVanishingSectionsHom J a F hJ
  inv := offVanishingSectionsInv J a F hJ
  hom_inv_id := offVanishingSectionsHom_inv_id J a F hJ
  inv_hom_id := offVanishingSectionsInv_hom_id J a F hJ

/-- `Stacks.Algebraization.sectionsOffVanishing` as a functor: evaluation at the open
`ι ''ᵁ (U ∖ V(J))` of `Spec A`, with scalars restricted along
`Stacks.Algebraization.offVanishingImageScalars`. -/
def sectionsOffVanishingFunctor :
    (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat.{u} A where
  obj G := sectionsOffVanishing J a G
  map η := (ModuleCat.restrictScalars (offVanishingImageScalars J a)).map
    (η.val.app (op ((complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor evaluates to `Stacks.Algebraization.sectionsOffVanishing`. -/
theorem sectionsOffVanishingFunctor_obj (G : (Spec (CommRingCat.of A)).Modules) :
    (sectionsOffVanishingFunctor J a).obj G = sectionsOffVanishing J a G :=
  rfl

variable {F} in
/-- The comparison is natural in the sheaf of modules. -/
theorem offVanishingSectionsHom_naturality (hJ : J ≤ a)
    {G : (Spec (CommRingCat.of A)).Modules} (η : F ⟶ G) :
    (ModuleCat.restrictScalars (offVanishingImageScalars J a)).map
          (η.val.app (op ((complementZeroLocus A a).ι ''ᵁ opensOffVanishing A J a))) ≫
        offVanishingSectionsHom J a G hJ =
      offVanishingSectionsHom J a F hJ ≫ (sectionsOnAffineComplement A J).map η :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (PresheafOfModules.naturality_apply η.val
      (homOfLE (complementZeroLocus_le_ι_image_opensOffVanishing J a hJ)).op x).symm)

/-- **The two descriptions of sections on `V = Spec A ∖ V(J)` agree naturally**, for `J ⊆ 𝔞`:
`Stacks.Algebraization.sectionsOffVanishingIso` assembled into an isomorphism of functors. This
is the `J ⊆ 𝔞` analogue of `Stacks.LocalCohomology.sectionsOnAffineComplementIso`. -/
def sectionsOffVanishingNatIso (hJ : J ≤ a) :
    sectionsOffVanishingFunctor J a ≅ sectionsOnAffineComplement A J :=
  NatIso.ofComponents (fun G => sectionsOffVanishingIso J a G hJ)
    (fun η => offVanishingSectionsHom_naturality J a hJ η)

end Stacks.Algebraization

end
