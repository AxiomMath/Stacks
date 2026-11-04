module

public import StacksFrontier.Cotangent.NaiveComparison
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.RingTheory.NaiveCotangent.ExtCokernelLinear

/-!
# The naive cotangent complex as a mapping cone, after an additive functor

For a presentation `P` of an `R`-algebra `S` and an additive functor `G` out of `S`-modules, the
image under `G` of the naive cotangent complex `J/J² → Ω_{P/R} ⊗_P S` is the mapping cone of
`G(J/J²)[0] → G(Ω_{P/R} ⊗_P S)[0]`. In that form a map `g : G(J/J²) → Z` gives the cochain map
`ExtCokernelLinear.coneDesc` into `Z[1]`, whose class is the first extension class of `g`; this
file records that the degree `-1` component of the composite is `g` itself.

## Main definitions

* `Stacks.Deformation.naiveComplexConeIso`: `G (NL(P)) ≅ cone(G(J/J²)[0] → G(Ω)[0])`.

## Main results

* `Stacks.Deformation.naiveComplexConeIso_hom_f_negOne`: its degree `-1` component.
* `Stacks.Deformation.naiveComplexCofiberIso_hom_coneDesc_f_negOne`: the degree `-1` component of
  the cocycle attached to `g`.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Deformation

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  (G : ModuleCat S ⥤ D) [G.Additive] (P : Algebra.Extension R S)

/-- The isomorphism `G(J/J²) ≅ G(NL(P))_{-1}`. -/
noncomputable abbrev naiveComplexConeIsoNegOne :
    G.obj (ModuleCat.of S P.Cotangent) ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Algebra.Extension.naiveComplex P)).X (-1) :=
  G.mapIso (Algebra.Extension.naiveComplexXNegOneIso P).symm

/-- The isomorphism `G(Ω_{P/R} ⊗_P S) ≅ G(NL(P))_0`. -/
noncomputable abbrev naiveComplexConeIsoZero :
    G.obj (ModuleCat.of S P.CotangentSpace) ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Algebra.Extension.naiveComplex P)).X 0 :=
  G.mapIso (Algebra.Extension.naiveComplexXZeroIso P).symm

omit [HasZeroObject D] [HasBinaryBiproducts D] in
/-- The two identifications carry the image under `G` of the conormal differential to the
`(-1, 0)` differential of `G(NL(P))`. -/
theorem naiveComplexConeIso_comm :
    (naiveComplexConeIsoNegOne G P).hom ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Algebra.Extension.naiveComplex P)).d (-1) 0 =
      G.map (ModuleCat.ofHom P.cotangentComplex) ≫ (naiveComplexConeIsoZero G P).hom := by
  rw [Functor.mapHomologicalComplex_obj_d, Algebra.Extension.naiveComplex_d]
  simp only [Functor.mapIso_hom, Iso.symm_hom, ← G.map_comp, Iso.inv_hom_id_assoc]

omit [HasZeroObject D] [HasBinaryBiproducts D] in
/-- `G(NL(P))` has no differential out of degree `0`: every term above degree `0` is zero. -/
theorem naiveComplexConeIso_out (j : ℤ) (_ : (ComplexShape.up ℤ).Rel 0 j) :
    (naiveComplexConeIsoZero G P).hom ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Algebra.Extension.naiveComplex P)).d 0 j = 0 :=
  (G.map_isZero (Algebra.Extension.isZero_naiveComplex_X P j
    (by rintro rfl; simp_all) (by rintro rfl; simp_all))).eq_of_tgt _ _

/-- `G(NL(P))` is the two-term complex on `G` of the conormal differential. -/
noncomputable def naiveComplexDoubleIso :
    HomologicalComplex.double (G.map (ModuleCat.ofHom P.cotangentComplex))
        (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Algebra.Extension.naiveComplex P) :=
  HomologicalComplex.doubleIsoOfIsZero _ rfl (by decide) _
    (naiveComplexConeIsoNegOne G P) (naiveComplexConeIsoZero G P)
    (naiveComplexConeIso_comm G P) (naiveComplexConeIso_out G P)
    (fun j h₀ h₁ => G.map_isZero (Algebra.Extension.isZero_naiveComplex_X P j h₀ h₁))

/-- **`G(NL(P))` is a mapping cone**: that of `G(J/J²)[0] → G(Ω_{P/R} ⊗_P S)[0]`. -/
noncomputable def naiveComplexConeIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Algebra.Extension.naiveComplex P) ≅
      CochainComplex.mappingCone
        (HomologicalComplex.singleMap (G.map (ModuleCat.ofHom P.cotangentComplex))) :=
  (naiveComplexDoubleIso G P).symm ≪≫
    HomologicalComplex.singleConeDoubleIso (G.map (ModuleCat.ofHom P.cotangentComplex))

omit [HasBinaryBiproducts D] in
/-- The degree `-1` component of `naiveComplexDoubleIso` is `naiveComplexConeIsoNegOne`, read
through the identification of the degree `-1` term of the two-term complex with `G(J/J²)`. -/
theorem naiveComplexDoubleIso_hom_f_negOne :
    (naiveComplexDoubleIso G P).hom.f (-1) =
      (HomologicalComplex.doubleXIso₀ _ rfl).hom ≫ (naiveComplexConeIsoNegOne G P).hom :=
  HomologicalComplex.mkHomFromDouble_f₀ _ (by decide) _ _ (naiveComplexConeIso_comm G P)
    (naiveComplexConeIso_out G P)

/-- The degree `-1` component of `naiveComplexConeIso`: the inverse of
`naiveComplexConeIsoNegOne` followed by the inclusion of the conormal summand of the cone. -/
theorem naiveComplexConeIso_hom_f_negOne :
    (naiveComplexConeIso G P).hom.f (-1) =
      (naiveComplexConeIsoNegOne G P).inv ≫
        (HomologicalComplex.singleConeNegOneIso
          (G.map (ModuleCat.ofHom P.cotangentComplex))).hom := by
  have h₁ : (naiveComplexDoubleIso G P).inv.f (-1) =
      (naiveComplexConeIsoNegOne G P).inv ≫ (HomologicalComplex.doubleXIso₀ _ rfl).inv := by
    rw [← cancel_epi ((naiveComplexDoubleIso G P).hom.f (-1)), ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f, naiveComplexDoubleIso_hom_f_negOne]
    simp
  have h₂ : (HomologicalComplex.singleConeDoubleIso
      (G.map (ModuleCat.ofHom P.cotangentComplex))).hom.f (-1) =
      (HomologicalComplex.doubleXIso₀ _ rfl).hom ≫
        (HomologicalComplex.singleConeNegOneIso
          (G.map (ModuleCat.ofHom P.cotangentComplex))).hom :=
    HomologicalComplex.mkHomFromDouble_f₀ _ (by decide) _ _
      (HomologicalComplex.singleCone_d _) (fun j hj => by
        have hj' : j = 1 := by simp [ComplexShape.up_Rel] at hj; omega
        subst hj'
        refine IsZero.eq_of_tgt (HomologicalComplex.homotopyCofiber.isZero_X
          (HomologicalComplex.singleMap (G.map (ModuleCat.ofHom P.cotangentComplex))) 1
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ 1 (by decide))
          (fun k hk => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ k
            (by change (1 : ℤ) + 1 = k at hk; omega))) _ _)
  rw [naiveComplexConeIso, Iso.trans_hom, HomologicalComplex.comp_f, Iso.symm_hom, h₁, h₂]
  simp

section Cocycle

variable {B : Type*} [CommRing B] (G : ModuleCat S ⥤ ModuleCat B) [G.Additive]
  (P : Algebra.Extension R S) {Z : ModuleCat B}

/-- `naiveComplexConeIso` for module categories, with the cone written as the homotopy cofiber
of `ExtCokernelLinear.singleMap`, the form in which its first extension classes are computed. -/
noncomputable def naiveComplexCofiberIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Algebra.Extension.naiveComplex P) ≅
      HomologicalComplex.homotopyCofiber (NaiveCotangent.ExtCokernelLinear.singleMap
        (G.map (ModuleCat.ofHom P.cotangentComplex))) :=
  naiveComplexConeIso G P

/-- **The cocycle of a functional on `G(J/J²)`, in degree `-1`.** Composing the identification
`G(NL(P)) ≅ cone(G(J/J²)[0] → G(Ω)[0])` with the cochain map `coneDesc` of
`g : G(J/J²) → Z` gives, in degree `-1`, the map `g` itself. -/
theorem naiveComplexCofiberIso_hom_coneDesc_f_negOne
    (g : G.obj (ModuleCat.of S P.Cotangent) ⟶ Z) :
    ((naiveComplexCofiberIso G P).hom ≫
        NaiveCotangent.ExtCokernelLinear.coneDesc (G.map (ModuleCat.ofHom P.cotangentComplex))
          g).f (-1) =
      (naiveComplexConeIsoNegOne G P).inv ≫ g ≫
        (TwoTermComplexExt.shiftSingleXSelf Z 1).inv := by
  rw [HomologicalComplex.comp_f]
  have h : (naiveComplexCofiberIso G P).hom.f (-1) =
      (naiveComplexConeIsoNegOne G P).inv ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
          HomologicalComplex.homotopyCofiber.inlX (NaiveCotangent.ExtCokernelLinear.singleMap
            (G.map (ModuleCat.ofHom P.cotangentComplex))) 0 (-1)
            ComplexShape.upIntRelNegOneZero :=
    naiveComplexConeIso_hom_f_negOne G P
  rw [h, Category.assoc, Category.assoc, NaiveCotangent.ExtCokernelLinear.inlX_coneDesc_f,
    Iso.inv_hom_id_assoc]

end Cocycle

end Stacks.Deformation

end
