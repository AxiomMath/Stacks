module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle

/-!
# Two descriptions of the sections on the complement of a zero locus

Let `A` be a commutative ring, `I ⊆ A` an ideal and `U = Spec A \ V(I)`. There are two ways to
regard the `A`-module of sections on `U` of a sheaf of modules `F` on `Spec A`:

* evaluate `F` at the open `U` of `Spec A`, which is
  `Stacks.LocalCohomology.sectionsOnAffineComplement`;
* restrict `F` along the open immersion `ι : U ⟶ Spec A` and take global sections of the
  restriction, which is `Stacks.LocalCohomology.complementGlobalSectionsFunctor`.

The two are *not* equal: restricting along `ι` and evaluating at `⊤` gives the sections on
`ι ''ᵁ ⊤`, and `ι ''ᵁ ⊤ = U` is a propositional equality of opens
(`AlgebraicGeometry.Scheme.Opens.ι_image_top`), not a definitional one. They are naturally
isomorphic.

## Main definitions

* `Stacks.LocalCohomology.complementSectionsHom`,
  `Stacks.LocalCohomology.complementSectionsInv`: the comparison maps.
* `Stacks.LocalCohomology.sectionsOnAffineComplementIso`: the natural isomorphism
  `restrictFunctor ι ⋙ complementGlobalSectionsFunctor A I ≅ sectionsOnAffineComplement A I`.

## Main results

* `Stacks.LocalCohomology.complementScalars_eq_comp`,
  `Stacks.LocalCohomology.imageTopScalars_eq_comp`: the two `A`-algebra structures on sections
  agree, in both directions.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The two open subsets -/

/-- The complement of the zero locus is contained in the image of the top open under its own
open immersion. -/
theorem complementZeroLocus_le_ι_image_top :
    complementZeroLocus A I ≤ (complementZeroLocus A I).ι ''ᵁ ⊤ :=
  le_of_eq (Scheme.Opens.ι_image_top (complementZeroLocus A I)).symm

/-- The image of the top open of the complement of the zero locus under its own open immersion
is contained in the complement. -/
theorem ι_image_top_le_complementZeroLocus :
    (complementZeroLocus A I).ι ''ᵁ ⊤ ≤ complementZeroLocus A I :=
  le_of_eq (Scheme.Opens.ι_image_top (complementZeroLocus A I))

/-! ### The scalars -/

/-- The structure map `A ⟶ Γ(U, 𝒪_U)` defining the `A`-module structure on global sections on
`U = Spec A \ V(I)`, viewed as a scheme. -/
abbrev complementTopScalars : A →+* Γ((complementZeroLocus A I : Scheme), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (complementZeroLocus A I).ι.appTop).hom

/-- The comparison of the global sections of the structure sheaf of `U` with the sections of the
structure sheaf of `Spec A` on `ι ''ᵁ ⊤`. -/
abbrev appIsoScalars :
    Γ((complementZeroLocus A I : Scheme), ⊤) →+*
      Γ(Spec (CommRingCat.of A), (complementZeroLocus A I).ι ''ᵁ ⊤) :=
  ((forget₂ CommRingCat RingCat).map (((complementZeroLocus A I).ι.appIso ⊤).inv)).hom

/-- The structure map `A ⟶ Γ(Spec A, ι ''ᵁ ⊤)`, the composite of
`Stacks.LocalCohomology.complementTopScalars` and `Stacks.LocalCohomology.appIsoScalars`. -/
abbrev imageTopScalars :
    A →+* Γ(Spec (CommRingCat.of A), (complementZeroLocus A I).ι ''ᵁ ⊤) :=
  (appIsoScalars I).comp (complementTopScalars I)

/-- The restriction map on structure sheaf sections from `ι ''ᵁ ⊤` to `U`. -/
abbrev imageTopToComplementScalars :
    Γ(Spec (CommRingCat.of A), (complementZeroLocus A I).ι ''ᵁ ⊤) →+*
      Γ(Spec (CommRingCat.of A), complementZeroLocus A I) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
    (homOfLE (complementZeroLocus_le_ι_image_top I)).op).hom

/-- The restriction map on structure sheaf sections from `U` to `ι ''ᵁ ⊤`. -/
abbrev complementToImageTopScalars :
    Γ(Spec (CommRingCat.of A), complementZeroLocus A I) →+*
      Γ(Spec (CommRingCat.of A), (complementZeroLocus A I).ι ''ᵁ ⊤) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
    (homOfLE (ι_image_top_le_complementZeroLocus I)).op).hom

/-- The structure map `A ⟶ Γ(Spec A, U)` defining the `A`-module structure on the sections of a
sheaf of modules on the open `U` of `Spec A`. -/
abbrev complementScalars : A →+* Γ(Spec (CommRingCat.of A), complementZeroLocus A I) :=
  ((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
      (homOfLE (le_top (a := complementZeroLocus A I))).op).hom.comp
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv)

/-- The comparison of structure sheaf sections on `⊤` of `U` with those on `ι ''ᵁ ⊤` of `Spec A`
is the identity. -/
theorem appIsoScalars_eq_id : appIsoScalars I = RingHom.id _ := by
  simp only [appIsoScalars, Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- The structure maps `Stacks.LocalCohomology.imageTopScalars` and
`Stacks.LocalCohomology.complementTopScalars` out of `A` agree. -/
theorem imageTopScalars_eq : imageTopScalars I = complementTopScalars I :=
  RingHom.ext fun a =>
    congrFun (congrArg DFunLike.coe (appIsoScalars_eq_id I)) (complementTopScalars I a)

/-- The `A`-module structure on sections on `U` obtained by restricting to `U` directly agrees
with the one obtained from `Stacks.LocalCohomology.complementTopScalars` by restriction from
`ι ''ᵁ ⊤` to `U`. -/
theorem complementScalars_eq_comp_complementTopScalars :
    complementScalars I = (imageTopToComplementScalars I).comp (complementTopScalars I) :=
  RingHom.ext fun a =>
    (ConcreteCategory.congr_hom (((Spec (CommRingCat.of A)).presheaf.map_comp
      (homOfLE (le_top (a := (complementZeroLocus A I).ι ''ᵁ ⊤))).op
      (homOfLE (complementZeroLocus_le_ι_image_top I)).op).symm)
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) a)).symm

/-- `Stacks.LocalCohomology.complementScalars` is `Stacks.LocalCohomology.imageTopScalars`
followed by restriction from `ι ''ᵁ ⊤` to `U`. -/
theorem complementScalars_eq_comp :
    complementScalars I = (imageTopToComplementScalars I).comp (imageTopScalars I) :=
  (complementScalars_eq_comp_complementTopScalars I).trans
    (congrArg (imageTopToComplementScalars I).comp (imageTopScalars_eq I).symm)

/-- `Stacks.LocalCohomology.imageTopScalars` is `Stacks.LocalCohomology.complementScalars`
followed by restriction from `U` to `ι ''ᵁ ⊤`. -/
theorem imageTopScalars_eq_comp :
    imageTopScalars I = (complementToImageTopScalars I).comp (complementScalars I) :=
  (imageTopScalars_eq I).trans (RingHom.ext fun a =>
    ConcreteCategory.congr_hom ((Spec (CommRingCat.of A)).presheaf.map_comp
      (homOfLE (le_top (a := complementZeroLocus A I))).op
      (homOfLE (ι_image_top_le_complementZeroLocus I)).op)
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) a))

/-! ### The comparison of sections -/

/-- The restriction maps of a presheaf of modules along an identity are the identity. -/
theorem presheafOfModules_map_id_apply {C : Type*} [Category C] {Rg : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules Rg) (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  rw [M.map_id]
  rfl

variable (F : (Spec (CommRingCat.of A)).Modules)

/-- The comparison from the global sections of the restriction of `F` to `U` to the sections of
`F` on the open `U` of `Spec A`: restriction along `U ≤ ι ''ᵁ ⊤`, with the two `A`-module
structures identified. -/
def complementSectionsHom :
    (complementGlobalSectionsFunctor A I).obj
        ((restrictFunctor (complementZeroLocus A I).ι).obj F) ⟶
      (sectionsOnAffineComplement A I).obj F :=
  (ModuleCat.restrictScalarsComp'App (complementTopScalars I) (appIsoScalars I)
      (imageTopScalars I) rfl
      (F.val.obj (op ((complementZeroLocus A I).ι ''ᵁ ⊤)))).inv ≫
    (ModuleCat.restrictScalars (imageTopScalars I)).map
        (F.val.map (homOfLE (complementZeroLocus_le_ι_image_top I)).op) ≫
      (ModuleCat.restrictScalarsComp'App (imageTopScalars I)
        (imageTopToComplementScalars I) (complementScalars I) (complementScalars_eq_comp I)
        (F.val.obj (op (complementZeroLocus A I)))).inv

/-- The comparison in the other direction: restriction along `ι ''ᵁ ⊤ ≤ U`. -/
def complementSectionsInv :
    (sectionsOnAffineComplement A I).obj F ⟶
      (complementGlobalSectionsFunctor A I).obj
        ((restrictFunctor (complementZeroLocus A I).ι).obj F) :=
  (ModuleCat.restrictScalars (complementScalars I)).map
      (F.val.map (homOfLE (ι_image_top_le_complementZeroLocus I)).op) ≫
    (ModuleCat.restrictScalarsComp'App (complementScalars I)
        (complementToImageTopScalars I) (imageTopScalars I) (imageTopScalars_eq_comp I)
        (F.val.obj (op ((complementZeroLocus A I).ι ''ᵁ ⊤)))).inv ≫
      (ModuleCat.restrictScalarsComp'App (complementTopScalars I) (appIsoScalars I)
        (imageTopScalars I) rfl
        (F.val.obj (op ((complementZeroLocus A I).ι ''ᵁ ⊤)))).hom

/-- Restricting a section of `F` along `U ≤ V` and then along `V ≤ U` gives back the section. -/
private theorem map_homOfLE_op_map_homOfLE_op_apply {U V : (Spec (CommRingCat.of A)).Opens}
    (h : U ≤ V) (h' : V ≤ U) (x : F.val.obj (op V)) :
    F.val.map (homOfLE h').op (F.val.map (homOfLE h).op x) = x :=
  ((PresheafOfModules.map_comp_apply F.val (homOfLE h).op (homOfLE h').op x).symm.trans
    (F.val.congr_map_apply (rfl : (homOfLE h).op ≫ (homOfLE h').op = 𝟙 _) x)).trans
    (presheafOfModules_map_id_apply F.val _ x)

/-- `Stacks.LocalCohomology.complementSectionsHom` followed by
`Stacks.LocalCohomology.complementSectionsInv` is the identity. -/
theorem complementSectionsHom_inv_id :
    complementSectionsHom I F ≫ complementSectionsInv I F = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    map_homOfLE_op_map_homOfLE_op_apply F (complementZeroLocus_le_ι_image_top I)
      (ι_image_top_le_complementZeroLocus I) x)

/-- `Stacks.LocalCohomology.complementSectionsInv` followed by
`Stacks.LocalCohomology.complementSectionsHom` is the identity. -/
theorem complementSectionsInv_hom_id :
    complementSectionsInv I F ≫ complementSectionsHom I F = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    map_homOfLE_op_map_homOfLE_op_apply F (ι_image_top_le_complementZeroLocus I)
      (complementZeroLocus_le_ι_image_top I) x)

variable {F} in
/-- The comparison is natural in the sheaf of modules. -/
theorem complementSectionsHom_naturality {G : (Spec (CommRingCat.of A)).Modules} (η : F ⟶ G) :
    (restrictFunctor (complementZeroLocus A I).ι ⋙
        complementGlobalSectionsFunctor A I).map η ≫ complementSectionsHom I G =
      complementSectionsHom I F ≫ (sectionsOnAffineComplement A I).map η :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (PresheafOfModules.naturality_apply η.val
      (homOfLE (complementZeroLocus_le_ι_image_top I)).op x).symm)

/-- For `U = Spec A \ V(I)`, restricting a sheaf of modules on `Spec A` along the open immersion
of `U` and taking global sections is naturally isomorphic to evaluating it at the open `U`, as
functors to `A`-modules. -/
def sectionsOnAffineComplementIso :
    restrictFunctor (complementZeroLocus A I).ι ⋙ complementGlobalSectionsFunctor A I ≅
      sectionsOnAffineComplement A I :=
  NatIso.ofComponents
    (fun F => { hom := complementSectionsHom I F
                inv := complementSectionsInv I F
                hom_inv_id := complementSectionsHom_inv_id I F
                inv_hom_id := complementSectionsInv_hom_id I F })
    (complementSectionsHom_naturality I)

end Stacks.LocalCohomology

end
