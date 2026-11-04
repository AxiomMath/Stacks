module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.LimitDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization

/-!
# An impurity over a henselization comes from an elementary étale neighbourhood

An impurity whose test family is the spectrum of a henselization of the local ring of the base at
the distinguished point already occurs over an elementary étale neighbourhood of that point.

## Main results

* `AlgebraicGeometry.exists_isImpurity_elementaryEtaleNeighborhood_of_henselization`: an impurity
  over the spectrum of a henselization of `𝒪_{S, s}` occurs over an elementary étale
  neighbourhood of `s`.

## References

* [Stacks Project, Tag 05J2](https://stacks.math.columbia.edu/tag/05J2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Henselization

variable {S : Scheme.{u}} (s : S)

/-- Every elementary étale neighbourhood is refined by an affine one. -/
private theorem exists_affine_elementaryEtaleNeighborhood
    (i : (ElementaryEtaleNeighborhood S s)ᵒᵖ) :
    ∃ j : (ElementaryEtaleNeighborhood S s)ᵒᵖ, IsAffine j.unop.obj.scheme ∧ Nonempty (i ⟶ j) := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hpt, -⟩ :=
    i.unop.obj.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ i.unop.obj.point) isOpen_univ
  let e : EtaleNeighborhood S s :=
    { scheme := Scheme.Opens.toScheme V
      point := ⟨i.unop.obj.point, hpt⟩
      toBase := Scheme.Opens.ι V ≫ i.unop.obj.toBase
      map_point := i.unop.obj.map_point }
  have he : e.IsElementary := by
    change IsIso ((S.residueFieldCongr e.map_point).inv ≫
      (Scheme.Opens.ι V ≫ i.unop.obj.toBase).residueFieldMap e.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (i.unop.obj.residueFieldMap ≫ (Scheme.Opens.ι V).residueFieldMap e.point)
    exact IsIso.comp_isIso' i.unop.property
      (inferInstance : IsIso ((Scheme.Opens.ι V).residueFieldMap e.point))
  exact ⟨op ⟨e, he⟩, hV, ⟨Quiver.Hom.op
    ⟨{ hom := Scheme.Opens.ι V, over := rfl, map_point := rfl }⟩⟩⟩

/-- A ring homomorphism out of the global sections of an affine elementary étale neighbourhood
which factors through the local ring at the distinguished point induces the same morphism of
spectra whether it is read through the affine identification or through the spectrum of that
local ring. -/
private theorem specMap_isoSpec_inv_eq_specMap_fromSpecStalk {Rh : Type u} [CommRing Rh]
    (U : ElementaryEtaleNeighborhood S s) [IsAffine U.obj.scheme]
    (a : Γ(U.obj.scheme, ⊤) →+* Rh) (g : U.obj.scheme.presheaf.stalk U.obj.point →+* Rh)
    (hglobal : a = g.comp (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom) :
    Spec.map (CommRingCat.ofHom a) ≫ U.obj.scheme.isoSpec.inv =
      Spec.map (CommRingCat.ofHom g) ≫ U.obj.scheme.fromSpecStalk U.obj.point := by
  refine (cancel_mono U.obj.scheme.toSpecΓ).1 ?_
  simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Scheme.fromSpecStalk_toSpecΓ]
  have hgerm : CommRingCat.ofHom a =
      CommRingCat.ofHom (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom ≫
        CommRingCat.ofHom g := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom hglobal
  change Spec.map (CommRingCat.ofHom a) =
    Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _))
  simpa [Spec.map_comp, Subsingleton.elim] using congrArg Spec.map hgerm

variable (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra (S.presheaf.stalk s) Rh]

/-- The canonical morphism from the spectrum of a henselization of the local ring of `S` at `s`
down to `S`. -/
abbrev specHenselizationToBase : Spec (CommRingCat.of Rh) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫ S.fromSpecStalk s

/-- A leg of the cocone of global sections, read as a morphism of schemes, is a morphism over the
base. -/
private theorem specMap_isoSpec_inv_comp_toBase (U : ElementaryEtaleNeighborhood S s)
    [IsAffine U.obj.scheme] (a : Γ(U.obj.scheme, ⊤) →+* Rh)
    (ha : IsOverStalk S s Rh U a) :
    (Spec.map (CommRingCat.ofHom a) ≫ U.obj.scheme.isoSpec.inv) ≫ U.obj.toBase =
      specHenselizationToBase s Rh := by
  obtain ⟨g, -, hst, hglobal⟩ := ha
  rw [specMap_isoSpec_inv_eq_specMap_fromSpecStalk s U a g hglobal]
  have hcongr :
      Spec.map ((S.presheaf.stalkCongr
        (Inseparable.of_eq U.obj.map_point.symm)).hom) ≫ S.fromSpecStalk s =
        S.fromSpecStalk (U.obj.toBase U.obj.point) := by
    simpa [TopCat.Presheaf.stalkCongr_hom] using
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := S)
        (Inseparable.of_eq U.obj.map_point.symm).ge
  have hstCat : CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh) =
      (S.presheaf.stalkCongr (Inseparable.of_eq U.obj.map_point.symm)).hom ≫
        Scheme.Hom.stalkMap U.obj.toBase U.obj.point ≫ CommRingCat.ofHom g := by
    refine CommRingCat.hom_ext ?_
    rw [← hst]
    rfl
  calc
    (Spec.map (CommRingCat.ofHom g) ≫ U.obj.scheme.fromSpecStalk U.obj.point) ≫ U.obj.toBase =
        Spec.map (CommRingCat.ofHom g) ≫ Spec.map (Scheme.Hom.stalkMap U.obj.toBase
          U.obj.point) ≫ S.fromSpecStalk (U.obj.toBase U.obj.point) := by
      rw [Category.assoc,
        ← Scheme.SpecMap_stalkMap_fromSpecStalk (f := U.obj.toBase) (x := U.obj.point)]
    _ = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (Scheme.Hom.stalkMap U.obj.toBase
          U.obj.point) ≫ Spec.map ((S.presheaf.stalkCongr
            (Inseparable.of_eq U.obj.map_point.symm)).hom) ≫ S.fromSpecStalk s := by
      rw [hcongr]
    _ = specHenselizationToBase s Rh := by
      have h2 : Spec.map (Scheme.Hom.stalkMap U.obj.toBase U.obj.point ≫
            CommRingCat.ofHom g) =
          Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (Scheme.Hom.stalkMap U.obj.toBase U.obj.point) := Spec.map_comp _ _
      have hmaps := congrArg Spec.map hstCat
      rw [Spec.map_comp, h2] at hmaps
      rw [show specHenselizationToBase s Rh =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫
          S.fromSpecStalk s from rfl, hmaps]
      simp only [Category.assoc]

/-- A point of the spectrum of a henselization which lies over the distinguished point of the
base is its closed point. -/
private theorem eq_closedPoint_of_specHenselizationToBase_eq
    [IsLocalRing.IsHenselization (S.presheaf.stalk s)
      (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]
    (y : Spec (CommRingCat.of Rh)) (hy : specHenselizationToBase s Rh y = s) :
    y = IsLocalRing.closedPoint Rh := by
  let R := S.presheaf.stalk s
  let z : Spec (CommRingCat.of R) :=
    (Spec.map (CommRingCat.ofHom (algebraMap R Rh))).base y
  have hz : z = IsLocalRing.closedPoint R := by
    refine (S.fromSpecStalk s).isEmbedding.injective ?_
    rw [show (S.fromSpecStalk s).base z = s from hy, Scheme.fromSpecStalk_closedPoint]
  have hmax : IsLocalRing.maximalIdeal Rh ≤ y.asIdeal := by
    rw [← IsLocalRing.IsHenselization.map_maximalIdeal (R := R)
      (L := IsLocalRing.ResidueField R) (Rh := Rh), Ideal.map_le_iff_le_comap]
    change IsLocalRing.maximalIdeal R ≤ z.asIdeal
    rw [hz]
    exact le_rfl
  exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal y.2.1) hmax)

/-- A leg of the cocone of global sections, read as a morphism of schemes, carries the closed
point of the henselization to the distinguished point of the neighbourhood. -/
private theorem specMap_isoSpec_inv_closedPoint (U : ElementaryEtaleNeighborhood S s)
    [IsAffine U.obj.scheme] (a : Γ(U.obj.scheme, ⊤) →+* Rh) (ha : IsOverStalk S s Rh U a) :
    (Spec.map (CommRingCat.ofHom a) ≫ U.obj.scheme.isoSpec.inv).base
      (IsLocalRing.closedPoint Rh) = U.obj.point := by
  obtain ⟨g, hgloc, -, hglobal⟩ := ha
  have : IsLocalHom (CommRingCat.ofHom g).hom := hgloc
  rw [specMap_isoSpec_inv_eq_specMap_fromSpecStalk s U a g hglobal]
  change U.obj.scheme.fromSpecStalk U.obj.point
      ((Spec.map (CommRingCat.ofHom g)) (IsLocalRing.closedPoint (CommRingCat.of Rh))) =
    U.obj.point
  rw [Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

end Henselization

/-- An impurity whose test family is the spectrum of a henselization of the local ring of the base
at the distinguished point already occurs over an elementary étale neighbourhood of that point. -/
@[stacks 05J2]
theorem exists_isImpurity_elementaryEtaleNeighborhood_of_henselization
    (P : PrePureSituation.{u}) (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra (P.S.presheaf.stalk P.s) Rh]
    [IsLocalRing.IsHenselization (P.S.presheaf.stalk P.s)
      (IsLocalRing.ResidueField (P.S.presheaf.stalk P.s)) Rh]
    (h : ∃ (D : ImpurityDiagram P) (e : D.T ≅ Spec (CommRingCat.of Rh)),
      D.g = e.hom ≫ specHenselizationToBase P.s Rh ∧ IsImpurity P D) :
    ∃ (D : ImpurityDiagram P) (hD : Etale D.g), IsImpurity P D ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := hD
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood P.S P.s) := by
  classical
  obtain ⟨D, e, hbase, hD⟩ := h
  let E := ElementaryEtaleNeighborhood P.S P.s
  let Q : ObjectProperty E := fun U ↦ IsAffine U.obj.scheme
  let inc : Q.op.FullSubcategory ⥤ Eᵒᵖ := Q.op.ι
  have hAbs : ∀ i : Eᵒᵖ, ∃ j : Q.op.FullSubcategory, Nonempty (i ⟶ inc.obj j) := fun i ↦
    let ⟨j, hj, hij⟩ := exists_affine_elementaryEtaleNeighborhood P.s i
    ⟨⟨j, hj⟩, hij⟩
  have hinc : inc.Final := Functor.final_of_exists_of_isFiltered_of_fullyFaithful inc hAbs
  have : IsFiltered Q.op.FullSubcategory :=
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful inc hAbs
  obtain ⟨ι, -, hst, -, ⟨hcolim⟩⟩ := isColimit_globalSections P.S P.s Rh
  let cR : Cocone (inc ⋙ globalSections P.S P.s) := Cocone.whisker inc (Cocone.mk _ ι)
  have hcR : IsColimit cR :=
    (Functor.Final.isColimitWhiskerEquiv inc (Cocone.mk _ ι)).symm hcolim
  let I := Q.op.FullSubcategoryᵒᵖ
  have : Nonempty I := IsCofiltered.nonempty
  let N : I ⥤ E := inc.leftOp
  let Dsch : I ⥤ Scheme := N ⋙ ElementaryEtaleNeighborhood.toScheme P.S P.s
  have hDschAffine : ∀ i : I, IsAffine (Dsch.obj i) := fun i ↦ i.unop.property
  have hNAffine : ∀ i : I, IsAffine (N.obj i).obj.scheme := fun i ↦ i.unop.property
  let cSpec := Scheme.Spec.mapCone cR.op
  let α : (inc ⋙ globalSections P.S P.s).op ⋙ Scheme.Spec ≅ Dsch :=
    NatIso.ofComponents (fun i ↦ (Dsch.obj i).isoSpec.symm) fun f ↦
      Scheme.isoSpec_inv_naturality (Dsch.map f)
  let cSch := (Cone.postcompose α.hom).obj cSpec
  have hcSch : IsLimit cSch :=
    (IsLimit.postcomposeHomEquiv α cSpec).symm (isLimitOfPreserves Scheme.Spec hcR.op)
  let b : Dsch ⟶ (Functor.const I).obj P.S :=
    { app := fun i ↦ (N.obj i).obj.toBase
      naturality := fun i j f ↦ (N.map f).hom.over }
  let F : I ⥤ Over P.S := Over.lift Dsch b
  have hconeBase : ∀ i, cSch.π.app i ≫ b.app i = specHenselizationToBase P.s Rh := fun i ↦
    specMap_isoSpec_inv_comp_toBase P.s Rh (N.obj i)
      (CommRingCat.Hom.hom (ι.app (inc.obj i.unop))) (hst (inc.obj i.unop))
  let cOver := Over.liftCone Dsch b cSch (specHenselizationToBase P.s Rh) hconeBase
  have hcOver : IsLimit cOver :=
    Over.isLimitLiftCone Dsch b cSch (specHenselizationToBase P.s Rh) hconeBase hcSch
  let eOver : Over.mk D.g ≅ cOver.pt := Over.isoMk e hbase.symm
  obtain ⟨i, hImp⟩ := exists_isImpurity_mapBase_of_isLimit F cOver hcOver D eOver hDschAffine hD
  let π := eOver.hom ≫ cOver.π.app i
  refine ⟨mapBase D (F.obj i).hom π.left π.w,
    inferInstanceAs (Etale (N.obj i).obj.toBase), hImp, ?_⟩
  have hpoint : π.left.base D.t = (N.obj i).obj.point := by
    have hy : e.hom.base D.t = IsLocalRing.closedPoint Rh := by
      refine eq_closedPoint_of_specHenselizationToBase_eq P.s Rh _ ?_
      have hh := congrArg (fun k : D.T ⟶ P.S ↦ k D.t) hbase
      rw [D.mapsToChosenPoint] at hh
      simpa [Scheme.Hom.comp_apply] using hh.symm
    change (cSch.π.app i).base (e.hom.base D.t) = (N.obj i).obj.point
    rw [hy]
    exact specMap_isoSpec_inv_closedPoint P.s Rh (N.obj i)
      (CommRingCat.Hom.hom (ι.app (inc.obj i.unop))) (hst (inc.obj i.unop))
  rw [EtaleNeighborhood.isElementary_iff]
  change IsIso ((N.obj i).obj.toBase.residueFieldMap (π.left.base D.t))
  rw [Scheme.Hom.isIso_residueFieldMap_congr (N.obj i).obj.toBase hpoint]
  exact (EtaleNeighborhood.isElementary_iff _).mp (N.obj i).property

end AlgebraicGeometry

end
