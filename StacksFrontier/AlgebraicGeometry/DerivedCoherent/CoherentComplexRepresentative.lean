module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.EssSurjRestrictOpen
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import StacksCore.Tactic.StacksAttribute

/-!
# Objects and morphisms of `D^b_Coh(𝒪_X)` as bounded complexes of coherent modules

On a Noetherian scheme `X`, the equivalence `D^b(Coh(𝒪_X)) ≌ D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB]
read concretely.

## Main results

* `AlgebraicGeometry.exists_isCoherent_complex_iso_Q_obj`: every object of `D^b_Coh(𝒪_X)` is a
  bounded complex of coherent modules.
* `AlgebraicGeometry.exists_isCoherent_roof`: every morphism of `D(𝒪_X)` between two bounded
  complexes of coherent modules is a roof of morphisms of bounded complexes of coherent modules.
* `AlgebraicGeometry.exists_bounded_isCoherent_complex_restrict_Q_iso`: the form of
  [Stacks, Tag 0G48] along an arbitrary open immersion `j : U ⟶ X`, with the extension given by a
  bounded complex of coherent `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0G48](https://stacks.math.columbia.edu/tag/0G48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

section

variable (X : Scheme.{u})

/-- **Every object of `D^b_Coh(𝒪_X)` is a bounded complex of coherent modules**, on a Noetherian
scheme: by [Stacks, Tag 0FDB] it comes from an object of `D^b(Coh(𝒪_X))`, and that object has a
representative strictly concentrated in the degrees where its cohomology lives. -/
theorem exists_isCoherent_complex_iso_Q_obj [IsNoetherian X]
    (K : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory) :
    ∃ (F : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (a b : ℤ),
      (∀ i, (F.X i).IsCoherent) ∧ F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
      Nonempty (DerivedCategory.Q.obj F ≅ K.obj) := by
  let Y := (coherentToModulesDerivedBounded X).objPreimage K
  have eY : ((coherentToModulesDerivedBounded X).obj Y).obj ≅ K.obj :=
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι.mapIso
      ((coherentToModulesDerivedBounded X).objObjPreimageIso K)
  obtain ⟨a, ha⟩ := Y.property.1
  obtain ⟨b, hb⟩ := Y.property.2
  obtain ⟨F', hGE', hLE', ⟨eF⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE Y.obj a b
  exact ⟨((coherentInModules X).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F', a, b,
    fun i => (F'.X i).property, inferInstance, inferInstance,
    ⟨((coherentInModules X).ι.mapDerivedCategoryFactors.app F').symm ≪≫
      (coherentInModules X).ι.mapDerivedCategory.mapIso eF.symm ≪≫ eY⟩⟩

/-- A lifted complex is strictly `≥ a` as soon as the original complex was. -/
theorem isStrictlyGE_coherentLiftComplex {X : Scheme.{u}}
    (𝒢 : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (h : ∀ i, (𝒢.X i).IsCoherent) (a : ℤ) [𝒢.IsStrictlyGE a] :
    (coherentLiftComplex 𝒢 h).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => isZero_coherentLiftComplex_X 𝒢 h i (𝒢.isZero_of_isStrictlyGE a i hi)

/-- A lifted complex is strictly `≤ b` as soon as the original complex was. -/
theorem isStrictlyLE_coherentLiftComplex {X : Scheme.{u}}
    (𝒢 : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (h : ∀ i, (𝒢.X i).IsCoherent) (b : ℤ) [𝒢.IsStrictlyLE b] :
    (coherentLiftComplex 𝒢 h).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => isZero_coherentLiftComplex_X 𝒢 h i (𝒢.isZero_of_isStrictlyLE b i hi)

/-- **A morphism of `D(𝒪_X)` between bounded complexes of coherent modules is a roof of morphisms
of bounded complexes of coherent modules**, on a Noetherian scheme: it is
`inv (Q s) ≫ Q g` for a quasi-isomorphism `s : 𝓕' ⟶ 𝓕` and a morphism `g : 𝓕' ⟶ 𝓖`, where `𝓕'`
is a complex of coherent modules in the same degrees as `𝓕`. By [Stacks, Tag 0FDB] the morphism
comes from `D^b(Coh(𝒪_X))`, where the calculus of fractions provides the roof. -/
theorem exists_isCoherent_roof [IsNoetherian X]
    {F G : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ}
    (hF : ∀ i, (F.X i).IsCoherent) (hG : ∀ i, (G.X i).IsCoherent) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b] [G.IsStrictlyGE a] [G.IsStrictlyLE b]
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj G) :
    ∃ (F' : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (_ : ∀ i, (F'.X i).IsCoherent)
      (_ : F'.IsStrictlyGE a) (_ : F'.IsStrictlyLE b) (s : F' ⟶ F)
      (_ : IsIso (DerivedCategory.Q.map s)) (g : F' ⟶ G),
      f = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
  let ι := (coherentInModules X).ι
  let F₀ := coherentLiftComplex F hF
  let G₀ := coherentLiftComplex G hG
  have : F₀.IsStrictlyGE a := isStrictlyGE_coherentLiftComplex F hF a
  have : F₀.IsStrictlyLE b := isStrictlyLE_coherentLiftComplex F hF b
  have : G₀.IsStrictlyGE a := isStrictlyGE_coherentLiftComplex G hG a
  have : G₀.IsStrictlyLE b := isStrictlyLE_coherentLiftComplex G hG b
  let eF : ι.mapDerivedCategory.obj (DerivedCategory.Q.obj F₀) ≅ DerivedCategory.Q.obj F :=
    ι.mapDerivedCategoryFactors.app F₀
  let eG : ι.mapDerivedCategory.obj (DerivedCategory.Q.obj G₀) ≅ DerivedCategory.Q.obj G :=
    ι.mapDerivedCategoryFactors.app G₀
  let BF : DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) :=
    ⟨DerivedCategory.Q.obj F₀, ⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  let BG : DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) :=
    ⟨DerivedCategory.Q.obj G₀, ⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  obtain ⟨h, hh⟩ := (DerivedCategory.Bounded.ι
    (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙ ι.mapDerivedCategory).map_surjective
      (X := BF) (Y := BG) (eF.hom ≫ f ≫ eG.inv)
  obtain ⟨F₁, _, _, s, hs, g, fac⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE (X := F₀) (Y := G₀) a b h.hom
  let e₁ : ι.mapDerivedCategory.obj (DerivedCategory.Q.obj F₁) ≅
      DerivedCategory.Q.obj ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁) :=
    ι.mapDerivedCategoryFactors.app F₁
  let s' : (ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁ ⟶ F :=
    (ι.mapHomologicalComplex (ComplexShape.up ℤ)).map s
  let g' : (ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁ ⟶ G :=
    (ι.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  have hs' : DerivedCategory.Q.map s' =
      e₁.inv ≫ ι.mapDerivedCategory.map (DerivedCategory.Q.map s) ≫ eF.hom :=
    e₁.eq_inv_comp.2 (ι.mapDerivedCategoryFactors_hom_naturality s).symm
  have hg' : DerivedCategory.Q.map g' =
      e₁.inv ≫ ι.mapDerivedCategory.map (DerivedCategory.Q.map g) ≫ eG.hom :=
    e₁.eq_inv_comp.2 (ι.mapDerivedCategoryFactors_hom_naturality g).symm
  have hfac : DerivedCategory.Q.map s ≫ h.hom = DerivedCategory.Q.map g := by
    rw [fac, IsIso.hom_inv_id_assoc]
  have hh' : ι.mapDerivedCategory.map h.hom = eF.hom ≫ f ≫ eG.inv := hh
  have : IsIso (DerivedCategory.Q.map s') := by
    rw [hs']
    infer_instance
  refine ⟨_, fun i => (F₁.X i).property, inferInstance, inferInstance, s', this, g', ?_⟩
  rw [← cancel_epi (DerivedCategory.Q.map s'), IsIso.hom_inv_id_assoc, hs', hg', ← hfac,
    Functor.map_comp, hh']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

/-- **An object of `D^b_Coh(𝒪_U)` is the restriction of a bounded complex of coherent
`𝒪_X`-modules**, for an open immersion `j : U ⟶ X` into a Noetherian scheme. This is the form of
[Stacks, Tag 0G48] along `j` rather than along the inclusion of an open subscheme, with the
extension produced as a complex: `K` is represented by a bounded complex of coherent
`𝒪_U`-modules by [Stacks, Tag 0FDB], that complex is moved to the image of `j` along the
isomorphism `U ≅ j(U)`, extended to `X`, and restricting the extension along `j` returns it. -/
theorem exists_bounded_isCoherent_complex_restrict_Q_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsNoetherian X]
    (K : (DerivedCategoryB.derivedCategoryBBounded
      (fun M : U.Modules => M.IsCoherent)).FullSubcategory) :
    ∃ 𝒢 : CochainComplex X.Modules ℤ, (∀ i : ℤ, (𝒢.X i).IsCoherent) ∧
      (∃ a : ℤ, 𝒢.IsStrictlyGE a) ∧ (∃ b : ℤ, 𝒢.IsStrictlyLE b) ∧
      Nonempty ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        (DerivedCategory.Q.obj 𝒢) ≅ K.obj) := by
  have hUN : IsNoetherian U :=
    { toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
      toCompactSpace :=
        have : TopologicalSpace.NoetherianSpace U :=
          (Scheme.Hom.isOpenEmbedding j).isInducing.noetherianSpace
        inferInstance }
  obtain ⟨ℱ, a, b, hℱcoh, hℱGE, hℱLE, ⟨eℱ⟩⟩ := exists_isCoherent_complex_iso_Q_obj U K
  let V := j.opensRange
  let ρ := Scheme.Modules.restrictFunctor j.isoOpensRange.inv
  let ℱV : CochainComplex V.toScheme.Modules ℤ :=
    (ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj ℱ
  have hcoh : ∀ i, (ℱV.X i).IsCoherent := fun i =>
    have : (ℱ.X i).IsCoherent := hℱcoh i
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion j.isoOpensRange.inv (ℱ.X i)
  have hGE : ℱV.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => ρ.map_isZero (ℱ.isZero_of_isStrictlyGE a i hi)
  have hLE : ℱV.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => ρ.map_isZero (ℱ.isZero_of_isStrictlyLE b i hi)
  obtain ⟨𝒢, hGcoh, hGGE, hGLE, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.ExtendBoundedComplex.exists_bounded_isCoherent_complex_restrict_iso
      V a b ℱV hcoh hGE hLE
  refine ⟨𝒢, hGcoh, ⟨a, hGGE⟩, ⟨b, hGLE⟩, ⟨?_⟩⟩
  let eJ : Scheme.Modules.restrictFunctor V.ι ⋙
      Scheme.Modules.restrictFunctor j.isoOpensRange.hom ≅ Scheme.Modules.restrictFunctor j :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom V.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι j)
  let eU : ρ ⋙ Scheme.Modules.restrictFunctor j.isoOpensRange.hom ≅ 𝟭 U.Modules :=
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.isoOpensRange.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId
  let eC : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒢 ≅
      ℱ :=
    ((Functor.mapHomologicalComplexCompIso eJ (ComplexShape.up ℤ)).app 𝒢).symm ≪≫
      ((Scheme.Modules.restrictFunctor j.isoOpensRange.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso eG ≪≫
      (Functor.mapHomologicalComplexCompIso eU (ComplexShape.up ℤ)).app ℱ ≪≫
      (Functor.mapHomologicalComplexIdIso U.Modules (ComplexShape.up ℤ)).app ℱ
  exact (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app 𝒢 ≪≫
    DerivedCategory.Q.mapIso eC ≪≫ eℱ

end AlgebraicGeometry

end
