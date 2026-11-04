module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FilteredModuleCharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FilteredTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplicativity of the characteristic series for a filtered perfect complex

The characteristic series `det(1 - f T)` of an endomorphism of a filtered perfect complex over a
commutative ring is the product of the characteristic series of its graded endomorphisms. This is
the determinant analogue of `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_sum_grDF`
(Stacks 03TK).

## Main results

* `CategoryTheory.FilteredDerived.FilteredPerfectData.isPerfect_forgetDF`: forgetting the
  filtration of a filtered perfect complex gives a perfect object.
* `CategoryTheory.FilteredDerived.FilteredPerfectData.isPerfect_grDF`: every graded piece of a
  filtered perfect complex is perfect.
* `CategoryTheory.FilteredDerived.perfectDerivedCharSeries_forgetDF_eq_prod_grDF`: multiplicativity
  along the filtration, for any model of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Limits Opposite
open scoped BigOperators

universe w u v

namespace CategoryTheory.FilteredDerived

section

/-- The image of a bounded complex under an additive functor is a bounded complex of finite
projective modules as soon as its terms are finite projective. -/
private lemma finiteProjectiveComplex_map (R : Type u) [Ring R]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R) [G.Additive]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hplus : CochainComplex.plus _ P) (hminus : CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, Module.Projective R (G.obj (P.X i)) ∧ Module.Finite R (G.obj (P.X i))) :
    finiteProjectiveComplex R ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine ⟨⟨?_, ?_⟩, hP⟩
  · obtain ⟨n, hn⟩ := hplus
    exact ⟨n, by let : P.IsStrictlyGE n := hn; infer_instance⟩
  · obtain ⟨n, hn⟩ := hminus
    exact ⟨n, by let : P.IsStrictlyLE n := hn; infer_instance⟩

private lemma finiteProjectiveComplex_forget (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hplus : CochainComplex.plus _ P) (hminus : CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i)) :
    finiteProjectiveComplex R
      (((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  finiteProjectiveComplex_map R _ P hplus hminus fun i ↦
    ⟨(hP i).finite_projective_forget.2, (hP i).finite_projective_forget.1⟩

private lemma finiteProjectiveComplex_grP (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hplus : CochainComplex.plus _ P) (hminus : CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i)) (p : ℤ) :
    finiteProjectiveComplex R
      (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  finiteProjectiveComplex_map R _ P hplus hminus fun i ↦ by
    let M := (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj (P.X i)
    let : Projective M := (hP i p).2
    exact ⟨(IsProjective.iff_projective (R := R) (P := M)).2 inferInstance, (hP i p).1⟩

/-- The image under `liftDF G` of a filtered perfect complex is perfect as soon as `G` maps its
representative to a bounded complex of finite projective modules. -/
private theorem isPerfect_liftDF (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R) [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (K : FilteredPerfectData.{u, v} R)
    (hGP : finiteProjectiveComplex R
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.representative)) :
    StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.liftDF G hG).obj K.obj) := by
  let P := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.representative
  let qP := (HomotopyCategory.quotient (FiniteFilteredObject
    (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)).obj K.representative
  obtain ⟨e⟩ := K.iso
  let η := CategoryTheory.Localization.fac
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hG
    (CochainComplex.FilteredDerivedCategory.Qh
      (𝒜 := ModuleCat.{max u v} R))
  have he : Nonempty (DerivedCategory.Q.obj P ≅
      (CochainComplex.FilteredDerivedCategory.liftDF G hG).obj K.obj) :=
    ⟨((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).app P).symm ≪≫
      (η.app qP).symm ≪≫
      (CochainComplex.FilteredDerivedCategory.liftDF G hG).mapIso e⟩
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hterms⟩ := hGP
  exact ⟨P, a, b, ha, hb, (fun i ↦ (hterms i).2), (fun i ↦ (hterms i).1), ⟨he.some.symm⟩⟩

/-- Forgetting the filtration of a filtered perfect complex gives a perfect object, for any model
of the derived category. -/
public theorem FilteredPerfectData.isPerfect_forgetDF (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : FilteredPerfectData.{u, v} R) : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.forgetDF).obj K.obj) :=
  isPerfect_liftDF R _ _ K (finiteProjectiveComplex_forget R K.representative K.bounded.1
    K.bounded.2 K.finiteProjective)

/-- Every graded piece of a filtered perfect complex is perfect, for any model of the derived
category. -/
@[sga "4½ Rapport 4.4" "partial"]
public theorem FilteredPerfectData.isPerfect_grDF (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : FilteredPerfectData.{u, v} R) (p : ℤ) : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.grDF p).obj K.obj) :=
  isPerfect_liftDF R _ _ K (finiteProjectiveComplex_grP R K.representative K.bounded.1
    K.bounded.2 K.finiteProjective p)


private theorem exists_filtered_representative_map (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hminus : CochainComplex.minus _ P)
    (hproj : ∀ i : ℤ, IsFilteredProjective (P.X i))
    (φ : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ⟶
        (CochainComplex.FilteredDerivedCategory.Qh).obj
          ((HomotopyCategory.quotient _ _).obj P)) :
    ∃ g : P ⟶ P,
      (CochainComplex.FilteredDerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ _).map g) = φ := by
  let A := ModuleCat.{max u v} R
  obtain ⟨n, hn⟩ := hminus
  let qP := (HomotopyCategory.quotient (FiniteFilteredObject A)
    (ComplexShape.up ℤ)).obj P
  let X : (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).FullSubcategory :=
    ⟨qP, CochainComplex.FilteredDerivedCategory.kminus_quotient_obj n⟩
  have hX : filteredProjectiveMinus A X := by
    show (filteredProjectiveMinusC A).strictMap
      (HomotopyCategory.quotient _ _) qP
    exact ObjectProperty.strictMap.mk _ ⟨⟨n, hn⟩, hproj⟩
  let Y : (filteredProjectiveMinus A).FullSubcategory := ⟨X, hX⟩
  let F := filteredProjectiveMinusToDerivedMinus A
  let : F.IsEquivalence := filteredProjectiveMinusToDerivedMinus_isEquivalence A
  let ψ : F.obj Y ⟶ F.obj Y := ObjectProperty.homMk (by
    show (CochainComplex.FilteredDerivedCategory.Qh).obj qP ⟶
      (CochainComplex.FilteredDerivedCategory.Qh).obj qP
    exact φ)
  have hψ : (CochainComplex.FilteredDerivedCategory.minus A).ι.map ψ = φ := rfl
  obtain ⟨h, hh⟩ := F.map_surjective ψ
  let h₁ : X ⟶ X := (filteredProjectiveMinus A).ι.map h
  let h₂ : qP ⟶ qP :=
    (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).ι.map h₁
  have hh' : (CochainComplex.FilteredDerivedCategory.Qh).map h₂ = φ := by
    have hh0 := congrArg
      ((CochainComplex.FilteredDerivedCategory.minus A).ι.map) hh
    rw [hψ] at hh0
    simpa [F, filteredProjectiveMinusToDerivedMinus,
      CochainComplex.FilteredDerivedCategory.Qminus, h₂, h₁] using hh0
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient (FiniteFilteredObject A)
    (ComplexShape.up ℤ)).map_surjective h₂
  exact ⟨g, by rw [hg, hh']⟩


private theorem filtered_derived_map_eq_chain_map (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (g : P ⟶ P) (X : CochainComplex.FilteredDerivedCategory
      (ModuleCat.{max u v} R))
    (e : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ≅ X)
    (f : X ⟶ X)
    (hgf : (CochainComplex.FilteredDerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ _).map g) = e.hom ≫ f ≫ e.inv) :
    ∃ e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) ≅ (CochainComplex.FilteredDerivedCategory.liftDF
        G hG).obj X,
      DerivedCategory.Q.map ((G.mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) = e'.hom ≫
          (CochainComplex.FilteredDerivedCategory.liftDF G hG).map f ≫ e'.inv := by
  let H := HomotopyCategory.quotient (FiniteFilteredObject
    (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)
  let qP := H.obj P
  let qg := H.map g
  let U := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let qcomp := DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)
  let β := G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)
  let γ := Functor.isoWhiskerRight β.symm DerivedCategory.Qh
  let η := CategoryTheory.Localization.fac
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    hG (CochainComplex.FilteredDerivedCategory.Qh
      (𝒜 := ModuleCat.{max u v} R))
  let L := CochainComplex.FilteredDerivedCategory.liftDF G hG
  let gc := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  let α := (qcomp.app U).symm ≪≫ (γ.app P) ≪≫ (η.app qP).symm ≪≫ L.mapIso e
  have hq : DerivedCategory.Q.map gc ≫ (qcomp.app U).symm.hom =
      (qcomp.app U).symm.hom ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).map gc) := by
    simp [U]
  have hγ : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).map gc) ≫ (γ.app P).hom =
      (γ.app P).hom ≫ DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map qg) := by
    simpa [Functor.map_comp, gc, qg, H] using γ.hom.naturality g
  have hη : DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map qg) ≫
          (η.app qP).symm.hom =
      (η.app qP).symm.hom ≫ L.map
        ((CochainComplex.FilteredDerivedCategory.Qh).map qg) := by
    simpa [qP, Functor.map_comp] using η.symm.hom.naturality qg
  have hmap : DerivedCategory.Qh.map ((G.mapHomotopyCategory
      (ComplexShape.up ℤ)).map qg) ≫ (η.app qP).symm.hom ≫
        L.map e.hom = (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
    calc
      _ = (DerivedCategory.Qh.map ((G.mapHomotopyCategory
          (ComplexShape.up ℤ)).map qg) ≫ (η.app qP).symm.hom) ≫
            L.map e.hom := by
            simp only [Category.assoc]
      _ = ((η.app qP).symm.hom ≫ L.map
          ((CochainComplex.FilteredDerivedCategory.Qh).map qg)) ≫ L.map e.hom := by
            rw [hη]
      _ = (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
            have hgf' : (CochainComplex.FilteredDerivedCategory.Qh).map qg =
                e.hom ≫ f ≫ e.inv := by simpa [qg, H] using hgf
            rw [hgf']
            simp only [Category.assoc]
            rw [← Functor.map_comp]
            simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id,
              Category.comp_id]
  have hconj : DerivedCategory.Q.map gc ≫ α.hom = α.hom ≫ L.map f := by
    dsimp only [α, Iso.trans_hom, Functor.mapIso_hom]
    calc
      _ = (qcomp.app U).symm.hom ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
            (ComplexShape.up ℤ)).map gc) ≫ (γ.app P).hom ≫
              (η.app qP).symm.hom ≫ L.map e.hom := by
                simpa only [Category.assoc] using congrArg
                  (fun k => k ≫ (γ.app P).hom ≫ (η.app qP).symm.hom ≫ L.map e.hom) hq
      _ = (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫
          DerivedCategory.Qh.map ((G.mapHomotopyCategory
            (ComplexShape.up ℤ)).map qg) ≫
              (η.app qP).symm.hom ≫ L.map e.hom := by
                simpa only [Category.assoc] using congrArg
                  (fun k => (qcomp.app U).symm.hom ≫ k ≫
                    (η.app qP).symm.hom ≫ L.map e.hom) hγ
      _ = (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫
          (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
                simpa only [Category.assoc] using congrArg
                  (fun k => (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫ k) hmap
      _ = _ := by simp only [Category.assoc]
  refine ⟨α, ?_⟩
  calc
    DerivedCategory.Q.map gc = DerivedCategory.Q.map gc ≫ α.hom ≫ α.inv := by
      simp only [Iso.hom_inv_id, Category.comp_id]
    _ = α.hom ≫ L.map f ≫ α.inv := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ α.inv) hconj


/-- The characteristic series of an endomorphism of the image of a filtered derived object under
an additive functor which inverts the filtered quasi-isomorphisms is the alternating
characteristic series of a representing cochain map on the image complex. -/
private theorem perfectDerivedCharSeries_liftDF_eq_alternatingCharSeries (R : Type u)
    [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hGP : finiteProjectiveComplex R
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (X : CochainComplex.FilteredDerivedCategory (ModuleCat.{max u v} R))
    (hX : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.liftDF G hG).obj X))
    (e : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ≅ X)
    (f : X ⟶ X) (g : P ⟶ P)
    (hg : (CochainComplex.FilteredDerivedCategory.Qh).map
      ((HomotopyCategory.quotient _ _).map g) = e.hom ≫ f ≫ e.inv) :
    perfectDerivedCharSeries R ((CochainComplex.FilteredDerivedCategory.liftDF G hG).obj X) hX
        ((CochainComplex.FilteredDerivedCategory.liftDF G hG).map f) =
      alternatingCharSeries R ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hGP
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  obtain ⟨e', hg'⟩ := filtered_derived_map_eq_chain_map R G hG P g X e f hg
  exact perfectDerivedCharSeries_eq_alternatingCharSeries R _ _ _ _ hGP e' _ hg'

/-- Exchanging two finitely supported products of alternating units. -/
private lemma finprod_alt_eq_finprod_finprod_alt {M : Type*} [CommGroup M]
    (c₀ : ℤ → M) (c : ℤ → ℤ → M)
    (h : ∀ i, c₀ i = ∏ᶠ p : ℤ, c i p) (I : Finset ℤ) (J : ℤ → Finset ℤ)
    (hvan : ∀ i p, i ∉ I ∨ p ∉ J i → c i p = 1) :
    ∏ᶠ i : ℤ, (if Even i then c₀ i else (c₀ i)⁻¹) =
      ∏ᶠ p : ℤ, ∏ᶠ i : ℤ, (if Even i then c i p else (c i p)⁻¹) := by
  have hfin : Function.HasFiniteMulSupport fun ip : ℤ × ℤ => c ip.1 ip.2 := by
    let S : Set (ℤ × ℤ) := ⋃ i ∈ (I : Set ℤ), (fun p => (i, p)) '' (J i : Set ℤ)
    have hS : S.Finite := by
      apply Set.Finite.biUnion I.finite_toSet
      intro i _
      exact (J i).finite_toSet.image (fun p => (i, p))
    refine hS.subset fun ip hip => ?_
    by_contra hout
    apply hip
    apply hvan ip.1 ip.2
    by_contra hin
    push Not at hin
    apply hout
    simp only [S, Set.mem_iUnion]
    exact ⟨ip.1, hin.1, ip.2, hin.2, rfl⟩
  let t : ℤ × ℤ → M := fun ip => if Even ip.1 then c ip.1 ip.2 else (c ip.1 ip.2)⁻¹
  have htfin : Function.HasFiniteMulSupport t := by
    refine Set.Finite.subset hfin fun ip hip => ?_
    intro hone
    apply hip
    simp only [t]
    rw [show c ip.1 ip.2 = 1 from hone]
    simp
  have hdeg : ∀ i : ℤ, (if Even i then c₀ i else (c₀ i)⁻¹) = ∏ᶠ p : ℤ, t (i, p) := by
    intro i
    rw [h i]
    by_cases he : Even i
    · simp only [he, if_true, t]
    · simp only [he, if_false, t]
      exact (finprod_inv_distrib _).symm
  rw [finprod_congr hdeg, ← finprod_curry t htfin,
    ← finprod_comp_equiv (Equiv.prodComm ℤ ℤ) (f := t),
    finprod_curry (fun x : ℤ × ℤ => t (Equiv.prodComm ℤ ℤ x)) (by
      show ((Equiv.prodComm ℤ ℤ) ⁻¹' Function.mulSupport t).Finite
      exact Set.Finite.preimage ((Equiv.prodComm ℤ ℤ).injective.injOn) htfin)]
  rfl

/-- The coercion of a finitely supported product of units. -/
private lemma coe_finprod_units {M : Type*} [CommMonoid M] (c : ℤ → Mˣ)
    (hc : Function.HasFiniteMulSupport c) : ((∏ᶠ p, c p : Mˣ) : M) = ∏ᶠ p, (c p : M) := by
  rw [← Units.coeHom_apply, MonoidHom.map_finprod _ hc]
  rfl

/-- The characteristic series of an endomorphism of a zero module is `1`, for any finiteness and
projectivity instances. -/
private lemma charSeries_eq_one_of_isZero (R : Type u) [CommRing R]
    (M : ModuleCat.{max u v} R) (hfin : Module.Finite R M) (hproj : Module.Projective R M)
    (hz : IsZero M) (φ : M ⟶ M) :
    @ProjectiveDeterminant.charSeries R _ M _ _ hfin hproj φ.hom 1 = 1 := by
  have := ModuleCat.subsingleton_of_isZero hz
  exact ProjectiveDeterminant.charSeries_eq_one_of_subsingleton _ _

/-- **Multiplicativity along the filtration.** The characteristic series of an endomorphism of a
filtered perfect complex is the product of the characteristic series of its graded
endomorphisms. -/
public theorem perfectDerivedCharSeries_forgetDF_eq_prod_grDF (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : FilteredPerfectData.{u, v} R) (f : K.obj ⟶ K.obj) :
    perfectDerivedCharSeries R ((CochainComplex.FilteredDerivedCategory.forgetDF).obj K.obj)
        (FilteredPerfectData.isPerfect_forgetDF R K)
        ((CochainComplex.FilteredDerivedCategory.forgetDF).map f) =
      ∏ᶠ p : ℤ, perfectDerivedCharSeries R
        ((CochainComplex.FilteredDerivedCategory.grDF p).obj K.obj)
        (FilteredPerfectData.isPerfect_grDF R K p)
        ((CochainComplex.FilteredDerivedCategory.grDF p).map f) := by
  obtain ⟨e⟩ := K.iso
  obtain ⟨g, hg⟩ := exists_filtered_representative_map R K.representative K.bounded.2
    (fun i => (K.finiteProjective i).isFilteredProjective)
    (e.hom ≫ f ≫ e.inv)
  have h0 := perfectDerivedCharSeries_liftDF_eq_alternatingCharSeries R
    (FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R))
    (CochainComplex.FilteredDerivedCategory.forget_inverts (𝒜 := ModuleCat.{max u v} R))
    K.representative
    (finiteProjectiveComplex_forget R K.representative K.bounded.1 K.bounded.2
      K.finiteProjective)
    K.obj (FilteredPerfectData.isPerfect_forgetDF R K) e f g hg
  have hgr : ∀ p : ℤ, _ := fun p => perfectDerivedCharSeries_liftDF_eq_alternatingCharSeries R
    (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p)
    (CochainComplex.FilteredDerivedCategory.grP_inverts (𝒜 := ModuleCat.{max u v} R) p)
    K.representative
    (finiteProjectiveComplex_grP R K.representative K.bounded.1 K.bounded.2
      K.finiteProjective p)
    K.obj (FilteredPerfectData.isPerfect_grDF R K p) e f g hg
  rw [h0, finprod_congr hgr]
  unfold alternatingCharSeries
  let a : ℤ → ℤ := fun i => Classical.choose (K.representative.X i).property.exists_isIso_ι
  let b : ℤ → ℤ := fun i => Classical.choose (K.representative.X i).property.exists_isZero_obj
  have ha (i : ℤ) : IsIso ((K.representative.X i).obj.filtration.ι.app (op (a i))) :=
    Classical.choose_spec (K.representative.X i).property.exists_isIso_ι
  have hb (i : ℤ) : IsZero ((K.representative.X i).obj.filtration.obj (op (b i))) :=
    Classical.choose_spec (K.representative.X i).property.exists_isZero_obj
  obtain ⟨lo, hlo⟩ := K.bounded.1
  obtain ⟨hi, hhi⟩ := K.bounded.2
  have hzero : ∀ i p : ℤ, (i < lo ∨ hi < i ∨ p < a i ∨ b i ≤ p) →
      IsZero ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj
        (K.representative.X i)) := by
    intro i p hout
    rcases hout with hlow | hhigh | hfilLow | hfilHigh
    · let : K.representative.IsStrictlyGE lo := hlo
      exact (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map_isZero
        (K.representative.isZero_of_isStrictlyGE lo i hlow)
    · let : K.representative.IsStrictlyLE hi := hhi
      exact (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map_isZero
        (K.representative.isZero_of_isStrictlyLE hi i hhigh)
    · exact FilteredObject.isZero_gr_obj_of_isIso_ι_app (K.representative.X i).obj (by omega) (ha i)
    · exact FilteredObject.isZero_gr_obj_of_isZero (K.representative.X i).obj hfilHigh (hb i)
  refine finprod_alt_eq_finprod_finprod_alt _ _ (fun i => ?_) (Finset.Icc lo hi)
    (fun i => Finset.Ico (a i) (b i)) (fun i p hip => ?_)
  · apply Units.ext
    rw [coe_finprod_units _ ?_]
    · simp only [coe_charUnitAt, Functor.mapHomologicalComplex_obj_X,
        Functor.mapHomologicalComplex_map_f]
      exact charSeries_eq_prod_grP R (K.representative.X i) (K.finiteProjective i) (g.f i) 1
    · refine Set.Finite.subset (Set.finite_Ico (a i) (b i)) fun p hp => ?_
      by_contra hout
      apply hp
      apply charUnitAt_eq_one_of_isZero
      exact hzero i p (by simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hout; tauto)
  · simp only [Finset.mem_Icc, Finset.mem_Ico, not_and_or, not_le, not_lt] at hip
    apply Units.ext
    simp only [coe_charUnitAt, Units.val_one, Functor.mapHomologicalComplex_obj_X,
      Functor.mapHomologicalComplex_map_f]
    exact charSeries_eq_one_of_isZero R _ _ _ (hzero i p (by omega)) _

end

end CategoryTheory.FilteredDerived
