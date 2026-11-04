module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence

/-!
# Naturality of the transport of the derived internal Hom along an equivalence of ringed sites

The isomorphism `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`

`φ_* RSheafHom_{O_X}(K, L) ≅ RSheafHom_{O_Y}(φ_* K, φ_* L)`

is built from a chosen representative `N` of `K` and a chosen K-injective representative `I` of
`L`. This file proves that it is natural in the contravariant variable `K`.

On representatives the isomorphism is the class of the chain-level transport of internal Hom
complexes, which is natural in chain maps of the source (`siteEquivDerivedSheafHomModelIso`,
`siteEquivDerivedSheafHomModelIso_natural`). Whiskering by the localization functor is fully
faithful, so this family is the restriction of a unique natural transformation of functors on
`D(O_X)ᵒᵖ`; the isomorphism at `K` is that transformation conjugated by the chosen
identification `Q N ≅ K`, and so it is natural.

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_natural_left`: naturality in the
  first variable.
* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso_natural_left`: the same for the
  variant with an invertible structure map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- The transport of the chosen K-injective resolution of `L` is K-injective. -/
private theorem isKInjective_pushComplex_kInjectiveResolution
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
        𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((pushComplex eqv φ).obj
      ((kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage L))).IsKInjective :=
  letI := pushforward_inverse_preservesFiniteLimits eqv φ ψ H₁ H₂
  letI := pushforward_inverse_preservesFiniteColimits eqv φ ψ H₁ H₂
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
    (modulesEquiv eqv φ ψ H₁ H₂).symm.toAdjunction _

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- The transport of the derived internal Hom on representatives: for a complex `N` and a
K-injective complex `I` whose transport is K-injective, the class of the chain-level transport of
the internal Hom complex. -/
def siteEquivDerivedSheafHomModelIso
    (N I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [((pushComplex eqv φ).obj I).IsKInjective] :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj N))).obj
          (DerivedCategory.Q.obj I)) ≅
      ((derivedSheafHomBifunctor Y).obj
          (op (DerivedCategory.Q.obj ((pushComplex eqv φ).obj N)))).obj
        (DerivedCategory.Q.obj ((pushComplex eqv φ).obj I)) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso (derivedSheafHomComparison X N I) ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app (sheafHomComplex X N I).obj ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I) ≪≫
    (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N) ((pushComplex eqv φ).obj I)).symm

/-- The transport on representatives is natural in chain maps of the source. -/
theorem siteEquivDerivedSheafHomModelIso_natural
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : N' ⟶ N)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [((pushComplex eqv φ).obj I).IsKInjective] :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
          (DerivedCategory.Q.obj I)) ≫
      (siteEquivDerivedSheafHomModelIso eqv φ ψ H₁ H₂ N' I).hom =
    (siteEquivDerivedSheafHomModelIso eqv φ ψ H₁ H₂ N I).hom ≫
      ((derivedSheafHomBifunctor Y).map
        (DerivedCategory.Q.map ((pushComplex eqv φ).map u)).op).app
          (DerivedCategory.Q.obj ((pushComplex eqv φ).obj I)) := by
  have hX := derivedSheafHomComparison_naturality X u (𝟙 I)
  have hY := derivedSheafHomComparison_naturality Y ((pushComplex eqv φ).map u)
    (𝟙 ((pushComplex eqv φ).obj I))
  have hC := siteEquivSheafHomComplexIso_natural eqv φ ψ H₁ H₂ u (𝟙 I)
  have hF := (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.naturality
    (homMap X u (𝟙 I))
  simp only [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.comp_map] at hX hY hC hF
  simp only [siteEquivDerivedSheafHomModelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hX, Functor.map_comp_assoc, reassoc_of% hF,
    ← Functor.map_comp_assoc, hC, Functor.map_comp_assoc]
  congr 3
  rw [Iso.eq_inv_comp, ← Category.assoc, ← hY, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  [I.IsKInjective] [((pushComplex eqv φ).obj I).IsKInjective]
  (eI : DerivedCategory.Q.obj I ≅ L)

/-- The transport of the derived internal Hom, for arbitrary representatives `eN : Q N ≅ K` and
`eI : Q I ≅ L` with `I` K-injective: `siteEquivDerivedSheafHomIso` is this at its chosen ones. -/
def siteEquivDerivedSheafHomIsoOfModels
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (derivedSheafHomObjectsModelIso X eN eI ≪≫ derivedSheafHomComparison X N I) ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app (sheafHomComplex X N I).obj ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ N I) ≪≫
    (derivedSheafHomComparison Y ((pushComplex eqv φ).obj N) ((pushComplex eqv φ).obj I)).symm ≪≫
    (derivedSheafHomObjectsModelIso Y
      (((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app N).symm ≪≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eN)
      (((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI)).symm

/-- The source `K ↦ φ_* RSheafHom(K, L)` of the transport, as a functor on `D(O_X)ᵒᵖ`. -/
abbrev siteEquivSource
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (derivedSheafHomBifunctor X).flip.obj L ⋙ (SheafOfModules.pushforward.{u} φ).mapDerivedCategory

/-- The target `K ↦ RSheafHom(φ_* K, φ_* L)` of the transport, as a functor on `D(O_X)ᵒᵖ`. -/
abbrev siteEquivTarget
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.op ⋙
    (derivedSheafHomBifunctor Y).flip.obj
      ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)

/-- The transport at the class of a complex, with the identity identification. -/
def siteEquivModelHom
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (siteEquivSource eqv φ L).obj (op (DerivedCategory.Q.obj N)) ⟶
      (siteEquivTarget eqv φ L).obj (op (DerivedCategory.Q.obj N)) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj N))).map eI.inv) ≫
    (siteEquivDerivedSheafHomModelIso eqv φ ψ H₁ H₂ N I).hom ≫
    ((derivedSheafHomBifunctor Y).obj (op (DerivedCategory.Q.obj ((pushComplex eqv φ).obj N)))).map
      ((((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI).hom) ≫
    ((derivedSheafHomBifunctor Y).map
      ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.app N).op).app
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)

/-- `siteEquivModelHom` is natural in chain maps `N' ⟶ N` of complexes. -/
theorem siteEquivModelHom_natural
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : N' ⟶ N) :
    (siteEquivSource eqv φ L).map (DerivedCategory.Q.map u).op ≫
        siteEquivModelHom eqv φ ψ H₁ H₂ eI N' =
      siteEquivModelHom eqv φ ψ H₁ H₂ eI N ≫
        (siteEquivTarget eqv φ L).map (DerivedCategory.Q.map u).op := by
  have h1 := ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).naturality eI.inv
  have h2 := siteEquivDerivedSheafHomModelIso_natural eqv φ ψ H₁ H₂ u I
  have h3 := ((derivedSheafHomBifunctor Y).map
    (DerivedCategory.Q.map ((pushComplex eqv φ).map u)).op).naturality
      ((((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
        (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI).hom)
  have h4 := (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.naturality u
  have h5 := congrArg (fun g => ((derivedSheafHomBifunctor Y).map g.op).app
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L)) h4
  simp only [Functor.comp_map, op_comp, Functor.map_comp, NatTrans.comp_app] at h5
  simp only [siteEquivModelHom, Functor.comp_map, Functor.flip_obj_map, Functor.op_map,
    Quiver.Hom.unop_op, Category.assoc]
  rw [← Functor.map_comp_assoc, ← h1, Functor.map_comp_assoc, reassoc_of% h2, ← reassoc_of% h3,
    ← h5]

/-- The transport at classes of complexes, as a natural transformation on cochain complexes. -/
def siteEquivModelNatTrans :
    DerivedCategory.Q.op ⋙ siteEquivSource eqv φ L ⟶
      DerivedCategory.Q.op ⋙ siteEquivTarget eqv φ L where
  app N := siteEquivModelHom eqv φ ψ H₁ H₂ eI N.unop
  naturality _ _ u := siteEquivModelHom_natural eqv φ ψ H₁ H₂ eI u.unop

/-- The natural transformation `φ_* RSheafHom(-, L) ⟶ RSheafHom(φ_* -, φ_* L)` of functors on
`D(O_X)ᵒᵖ` whose value at the class of a complex is `siteEquivModelHom`. -/
def siteEquivNatTrans : siteEquivSource eqv φ L ⟶ siteEquivTarget eqv φ L :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q.op
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      _).preimage (siteEquivModelNatTrans eqv φ ψ H₁ H₂ eI)

/-- The value of `siteEquivNatTrans` at the class of a complex `N` is `siteEquivModelHom` at `N`.
-/
theorem siteEquivNatTrans_app
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (siteEquivNatTrans eqv φ ψ H₁ H₂ eI).app (op (DerivedCategory.Q.obj N)) =
      siteEquivModelHom eqv φ ψ H₁ H₂ eI N :=
  NatTrans.congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q.op
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
      _).map_preimage (siteEquivModelNatTrans eqv φ ψ H₁ H₂ eI)) (op N)

/-- The transport built from a representative `N` with `eN : Q N ≅ K` is `siteEquivModelHom` at
`N` conjugated by the identification `eN`. -/
theorem siteEquivDerivedSheafHomIsoOfModels_hom
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ K) :
    (siteEquivDerivedSheafHomIsoOfModels eqv φ ψ H₁ H₂ eI eN).hom =
      (siteEquivSource eqv φ L).map eN.hom.op ≫ siteEquivModelHom eqv φ ψ H₁ H₂ eI N ≫
        (siteEquivTarget eqv φ L).map eN.inv.op := by
  simp only [siteEquivDerivedSheafHomIsoOfModels, siteEquivModelHom,
    siteEquivDerivedSheafHomModelIso, derivedSheafHomObjectsModelIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Iso.op_hom, Iso.op_inv, Functor.map_comp, Category.assoc,
    Functor.comp_map, Functor.flip_obj_map, Functor.op_map, Quiver.Hom.unop_op, op_comp,
    NatTrans.comp_app]

/-- The transport built from any representative `N` of `K` is the value of `siteEquivNatTrans` at
`K`. -/
theorem siteEquivDerivedSheafHomIsoOfModels_hom_eq
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ K) :
    (siteEquivDerivedSheafHomIsoOfModels eqv φ ψ H₁ H₂ eI eN).hom =
      (siteEquivNatTrans eqv φ ψ H₁ H₂ eI).app (op K) := by
  rw [siteEquivDerivedSheafHomIsoOfModels_hom, ← siteEquivNatTrans_app,
    NatTrans.naturality_assoc, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Derived

section Natural

attribute [local instance] HasDerivedCategory.standard

variable [PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- `siteEquivDerivedSheafHomIso` is the transport at its chosen representatives. -/
theorem siteEquivDerivedSheafHomIso_hom_eq
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := pushforward_inverse_preservesFiniteLimits eqv φ ψ H₁ H₂
    letI := pushforward_inverse_preservesFiniteColimits eqv φ ψ H₁ H₂
    letI : ((kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage L)).IsKInjective :=
      Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (DerivedCategory.Q.objPreimage L)
    letI : ((pushComplex eqv φ).obj
        ((kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage L))).IsKInjective :=
      CochainComplex.isKInjective_mapHomologicalComplex_of_exact
        (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
        (modulesEquiv eqv φ ψ H₁ H₂).symm.toAdjunction _
    (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K L).hom =
      (siteEquivNatTrans eqv φ ψ H₁ H₂
        ((asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
          (DerivedCategory.Q.objPreimage L)))).symm ≪≫
            DerivedCategory.Q.objObjPreimageIso L)).app (op K) := by
  have := isKInjective_pushComplex_kInjectiveResolution eqv φ ψ H₁ H₂ L
  exact siteEquivDerivedSheafHomIsoOfModels_hom_eq eqv φ ψ H₁ H₂ _
    (DerivedCategory.Q.objObjPreimageIso K)

/-- **The transport of the derived internal Hom along an equivalence of ringed sites is natural
in the first variable.** -/
theorem siteEquivDerivedSheafHomIso_natural_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : K' ⟶ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map k.op).app L) ≫
      (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K' L).hom =
    (siteEquivDerivedSheafHomIso eqv φ ψ H₁ H₂ K L).hom ≫
      ((derivedSheafHomBifunctor Y).map
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map k).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
  rw [siteEquivDerivedSheafHomIso_hom_eq, siteEquivDerivedSheafHomIso_hom_eq]
  have := isKInjective_pushComplex_kInjectiveResolution eqv φ ψ H₁ H₂ L
  exact NatTrans.naturality (siteEquivNatTrans eqv φ ψ H₁ H₂
    ((asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (DerivedCategory.Q.objPreimage L)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L)) k.op

end Natural

section OfIso

attribute [local instance] HasDerivedCategory.standard

variable [hφ : IsIso φ] [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- `siteEquivDerivedSheafHomIsoOfIso` is natural in the first variable. -/
theorem siteEquivDerivedSheafHomIsoOfIso_natural_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : K' ⟶ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map k.op).app L) ≫
      (siteEquivDerivedSheafHomIsoOfIso eqv φ K' L).hom =
    (siteEquivDerivedSheafHomIsoOfIso eqv φ K L).hom ≫
      ((derivedSheafHomBifunctor Y).map
        ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map k).op).app
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  siteEquivDerivedSheafHomIso_natural_left eqv φ _
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) L k

end OfIso

end AlgebraicGeometry.RingedSite

end
