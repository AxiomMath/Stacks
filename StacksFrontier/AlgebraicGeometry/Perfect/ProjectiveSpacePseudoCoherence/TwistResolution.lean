module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.PseudoCoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentDetectedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TwistDetection
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TwistEquivalence
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.TensorProduct

/-!
# Pseudo-coherence on projective space from the pseudo-coherence of the twisted global sections

Let `A` be a ring, `n ≥ 0` and `K` an object of `D_QCoh(𝒪_{ℙⁿ_A})`. If
`RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d))` is a pseudo-coherent object of `D(A)` for `d = 0, 1, …, n`, then `K` is
pseudo-coherent. This is the implication (5) ⟹ (1) of [Stacks, Tag 0CSG].

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.exists_unit_hom_mem_range`: on a scheme over
  `A`, every class in `H^j RΓ_A(M)` is the image of a class under a morphism `𝒪[-j] ⟶ M`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.exists_twist_hom_mem_range`: on `ℙⁿ_A`, every
  class in `H^j RΓ_A(C ⊗^𝐋 𝒪(e))` comes from a morphism `𝒪(-e)[-j] ⟶ C`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.exists_kill`: a finite sum of twists
  `𝒪(-e)[-j]`, `0 ≤ e ≤ n`, maps onto the top cohomology of all the twisted global sections.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isPseudoCoherent_of_twists`: an object `K` of
  `D_QCoh(𝒪_{ℙⁿ_A})` whose twisted global sections `RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d))`, `0 ≤ d ≤ n`, are
  pseudo-coherent is pseudo-coherent.

## References

* [Stacks Project, Tag 0CSG](https://stacks.math.columbia.edu/tag/0CSG)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistOverMulIso twistZeroIsoUnit)
open AlgebraicGeometry.ProjectiveSpaceDirectImage (proj)

variable {A : Type u} [CommRing A] (n : ℕ)

/-! ### Morphisms out of the structure sheaf compute derived global sections -/

/-- Applying `H (γ.hom ≫ β)` to `H γ.inv z` gives `H β z`. -/
private theorem map_comp_map_inv_apply {C D : Type*} [Category C] [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] (H : C ⥤ D) {X Y Z : C} (γ : X ≅ Y) (β : Y ⟶ Z)
    (z : ToType (H.obj Y)) : H.map (γ.hom ≫ β) (H.map γ.inv z) = H.map β z := by
  simp [← ConcreteCategory.comp_apply]

section Unit

variable (X : Scheme.{u}) (f : X ⟶ Spec (.of A))

/-- `H^j(RΓ_A(M))`, with the scalars forgotten, is `H^0` of the abelian derived global sections of
`M[j]`, naturally in `M`. -/
def homologyForgetShiftIso (j : ℤ) :
    derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) j ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} ≅
      shiftFunctor (DerivedCategory X.Modules) j ⋙
        Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 :=
  Functor.isoWhiskerLeft (derivedGlobalSectionsOver f)
      (Functor.isoWhiskerRight
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso j 0 j (by omega)).symm
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((derivedGlobalSectionsOver f).commShiftIso j).symm
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory X.Modules) j)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.homologyZeroForgetNatIso f)

/-- **Every class in `H^j(RΓ_A(M))` comes from a morphism `𝒪[-j] ⟶ M`.** -/
theorem exists_unit_hom_mem_range (M : DerivedCategory X.Modules) (j : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((derivedGlobalSectionsOver f).obj M)) :
    ∃ (β : (DerivedCategory.singleFunctor X.Modules j).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶ M)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules j).obj (SheafOfModules.unit X.ringCatSheaf)))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((derivedGlobalSectionsOver f).map β)).hom z = x := by
  let Θ := homologyForgetShiftIso X f j
  let G := Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
    (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
  let E := AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv
    (Stacks.SheafOfModules.ringedSite X.sheaf)
  let O :=
    AlgebraicGeometry.RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite X.sheaf)
  let L := (DerivedCategory.singleFunctor X.Modules j).obj (SheafOfModules.unit X.ringCatSheaf)
  let y0 : G.obj O := (E O).toEquiv.symm (𝟙 _)
  let x' : G.obj (M⟦j⟧) := Θ.hom.app M x
  let β' : O ⟶ M⟦j⟧ := E (M⟦j⟧) x'
  have hβ' : G.map β' y0 = x' := by
    apply (E (M⟦j⟧)).injective
    refine (AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality
      (Stacks.SheafOfModules.ringedSite X.sheaf) β' y0).trans ?_
    change (E O).toEquiv ((E O).toEquiv.symm (𝟙 _)) ≫ β' = (E (M⟦j⟧)).toEquiv x'
    rw [Equiv.apply_symm_apply, Category.id_comp]
    rfl
  let ι : L⟦j⟧ ≅ O :=
    ((DerivedCategory.singleFunctors X.Modules).shiftIso j 0 j (by omega)).app _
  let β : L ⟶ M := (shiftFunctor (DerivedCategory X.Modules) j).preimage (ι.hom ≫ β')
  have hβ : β⟦j⟧' = ι.hom ≫ β' := (shiftFunctor (DerivedCategory X.Modules) j).map_preimage _
  set z := Θ.inv.app L (G.map ι.inv y0) with hz
  refine ⟨β, z, ?_⟩
  apply (Θ.app M).addCommGroupIsoToAddEquiv.injective
  have hnat := ConcreteCategory.congr_hom (Θ.hom.naturality β) z
  simp only [ConcreteCategory.comp_apply] at hnat
  have hz' : Θ.hom.app L z = G.map ι.inv y0 := Iso.inv_hom_id_apply (Θ.app L) _
  change Θ.hom.app M (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((derivedGlobalSectionsOver f).map β)).hom z) = x'
  refine hnat.trans ?_
  rw [hz', Functor.comp_map, hβ]
  exact (map_comp_map_inv_apply G ι β' y0).trans hβ'

end Unit

/-! ### Twisted global sections -/

/-- Twisting by `𝒪(e)`: the functor `- ⊗^𝐋 𝒪(e)[0]` on `D(𝒪_{ℙⁿ_A})`. -/
abbrev tensorTwist (e : ℤ) :
    DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules ⥤
      DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (projectiveSpaceOver n (Spec (.of A))).sheaf).flip.obj (twistObj n (Spec (.of A)) e)

/-- Twisting by `𝒪(e)` commutes with shifts. -/
instance tensorTwist_commShift (e : ℤ) : (tensorTwist (A := A) n e).CommShift ℤ :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).commShift_left _

/-- Twisting by `𝒪(e)` is a triangulated functor. -/
instance tensorTwist_isTriangulated (e : ℤ) : (tensorTwist (A := A) n e).IsTriangulated :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).exact_left _

/-- The twisted global sections `RΓ_A(ℙⁿ_A, - ⊗^𝐋 𝒪(e))`. -/
abbrev twistedSections (e : ℤ) :
    DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  tensorTwist n e ⋙ derivedGlobalSectionsOver (proj (A := A) n)

/-- `𝒪(-e)[j] ⊗^𝐋 𝒪(e)[0] ≅ 𝒪[j]`. -/
def singleTwistTensorUnitIso (j e : ℤ) :
    (tensorTwist (A := A) n e).obj
        ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (-e))) ≅
      (DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).obj
        (SheafOfModules.unit (projectiveSpaceOver n (Spec (.of A))).ringCatSheaf) :=
  singleTwistTensorIso n (Spec (.of A)) j (-e) e ≪≫
    (DerivedCategory.singleFunctor _ j).mapIso
      (eqToIso (congrArg (twistOver n (Spec (.of A))) (by ring)) ≪≫ twistZeroIsoUnit n _)

/-- **Every class in `H^j RΓ_A(C ⊗^𝐋 𝒪(e))` comes from a morphism `𝒪(-e)[-j] ⟶ C`.** -/
theorem exists_twist_hom_mem_range
    (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (e j : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((twistedSections n e).obj C)) :
    ∃ (α : (DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (-e)) ⟶ C)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((twistedSections n e).obj
          ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (-e))))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((twistedSections n e).map α)).hom z = x := by
  obtain ⟨β, z, hz⟩ := exists_unit_hom_mem_range _ (proj (A := A) n) _ j x
  let γ := singleTwistTensorUnitIso (A := A) n j e
  let F := (twistEquivalence n (Spec (.of A)) e).fullyFaithfulFunctor
  let α := F.preimage (γ.hom ≫ β)
  have hα : (tensorTwist (A := A) n e).map α = γ.hom ≫ β := F.map_preimage _
  let H := derivedGlobalSectionsOver (proj (A := A) n) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) j
  refine ⟨α, (H.mapIso γ).inv z, ?_⟩
  change (H.map ((tensorTwist (A := A) n e).map α)).hom ((H.mapIso γ).inv z) = x
  rw [hα]
  exact (map_comp_map_inv_apply H γ β z).trans hz

/-! ### Twisted global sections of the twists -/

/-- `RΓ_A(𝒪(a)[j] ⊗^𝐋 𝒪(e)) ≅ RΓ_A(𝒪(a + e)[j])`. -/
def twistedSectionsSingleTwistIso (e j a : ℤ) :
    (twistedSections (A := A) n e).obj
        ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) a)) ≅
      (derivedGlobalSectionsOver (proj (A := A) n)).obj
        ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (a + e))) :=
  (derivedGlobalSectionsOver (proj (A := A) n)).mapIso (singleTwistTensorIso n _ j a e)

/-- An object of `D(A)` is good at `j` if it is pseudo-coherent with no cohomology above
degree `j`. -/
def IsGoodAt (j : ℤ) (Y : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  StacksDraft.PseudoCoherence.IsPseudoCoherent Y ∧
    ∀ i : ℤ, j < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj Y)

/-- Being good at `j` is invariant under isomorphism. -/
theorem IsGoodAt.ofIso {j : ℤ} {Y Y' : DerivedCategory (ModuleCat.{u} A)} (h : IsGoodAt j Y)
    (e : Y ≅ Y') : IsGoodAt j Y' :=
  ⟨StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso h.1 e,
    fun i hi =>
      (h.2 i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e).symm⟩

/-- The biproduct of two objects good at `j` is good at `j`. -/
theorem IsGoodAt.biprod {j : ℤ} {Y Y' : DerivedCategory (ModuleCat.{u} A)} (h : IsGoodAt j Y)
    (h' : IsGoodAt j Y') : IsGoodAt j (Y ⊞ Y') := by
  have hT := binaryBiproductTriangle_distinguished Y Y'
  refine ⟨(StacksDraft.PseudoCoherence.isPseudoCoherent_of_distinguished _ hT).2.1 h.1 h'.1,
    fun i hi => ?_⟩
  have hex := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequence_exact₂ _ hT i
  exact hex.isZero_X₂ ((h.2 i hi).eq_of_src _ _) ((h'.2 i hi).eq_of_tgt _ _)

/-- A finite biproduct of objects good at `j` is good at `j`. -/
theorem isGoodAt_biproduct (j : ℤ) :
    ∀ (r : ℕ) (f : Fin r → DerivedCategory (ModuleCat.{u} A)),
      (∀ k, IsGoodAt j (f k)) → IsGoodAt j (⨁ f) := by
  intro r
  induction r with
  | zero =>
    intro f _
    have hz := isZero_biproduct_of_isEmpty f
    exact ⟨(StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero _ hz).1,
      fun i _ => Functor.map_isZero _ hz⟩
  | succ r ih =>
    intro f hf
    exact ((hf 0).biprod (ih _ fun k => hf k.succ)).ofIso (biproductFinSuccIso r f).symm

/-- For `-n ≤ a + e`, `RΓ_A(𝒪(a)[j] ⊗^𝐋 𝒪(e))` is pseudo-coherent with no cohomology above
degree `j`. -/
theorem isGoodAt_twistedSections_singleFunctor (e j a : ℤ) (h : -(n : ℤ) ≤ a + e) :
    IsGoodAt j ((twistedSections (A := A) n e).obj
      ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) a))) := by
  refine IsGoodAt.ofIso ?_ (twistedSectionsSingleTwistIso n e j a).symm
  refine ⟨(ProjectiveSpaceDirectImage.IsTwistLike.singleFunctor n
    (ProjectiveSpaceDirectImage.isTwistLike_twistOver (a + e)) j).2, fun i hi => ?_⟩
  have e₁ : (derivedGlobalSectionsOver (proj (A := A) n)).obj
      ((DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (a + e))) ≅
      ((derivedGlobalSectionsOver (proj (A := A) n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) (a + e))))⟦-j⟧ :=
    (derivedGlobalSectionsOver (proj (A := A) n)).mapIso
        (((DerivedCategory.singleFunctors _).shiftIso (-j) j 0 (by omega)).app _).symm ≪≫
      ((derivedGlobalSectionsOver (proj (A := A) n)).commShiftIso (-j)).app _
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e₁)
  refine IsZero.of_iso ?_ (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso
    (-j) i (-j + i) rfl).app _)
  exact ProjectiveSpaceDirectImage.isZero_homology_derivedGlobalSectionsOver_twist n (a + e) h
    (-j + i) (by omega)

/-! ### Killing the top cohomology of all the twisted global sections at once -/

/-- Let `C` be an object of `D(𝒪_{ℙⁿ_A})` whose twisted global sections
`RΓ_A(C ⊗^𝐋 𝒪(e))`, `0 ≤ e ≤ n`, are pseudo-coherent with no cohomology above degree `j`. Then
there is a finite sum `S` of twists `𝒪(-e)[-j]`, `0 ≤ e ≤ n`, with a morphism `S ⟶ C` surjective
on `H^j RΓ_A(- ⊗^𝐋 𝒪(e))` for every `0 ≤ e ≤ n`. -/
theorem exists_kill (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (j : ℤ)
    (hC : ∀ e : ℕ, e ≤ n → IsGoodAt j ((twistedSections n e).obj C)) :
    ∃ (S : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (α : S ⟶ C),
      (∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
        (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) S m) ∧
      (∀ e : ℕ, e ≤ n → IsGoodAt j ((twistedSections n e).obj S)) ∧
      ∀ e : ℕ, e ≤ n → Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((twistedSections n e).map α)) := by
  have hfin : ∀ e : Fin (n + 1), Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((twistedSections n (e : ℕ)).obj C)) := fun e =>
    _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom _ j
      ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1 (hC e (by omega)).1 j)
      (hC e (by omega)).2
  choose r g hg using fun e => (hfin e).exists_fin
  choose α z hz using fun (e : Fin (n + 1)) (k : Fin (r e)) =>
    exists_twist_hom_mem_range n C (e : ℕ) j (g e k)
  let f : Fin (n + 1) → DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules :=
    fun e => ⨁ fun _ : Fin (r e) =>
      (DerivedCategory.singleFunctor _ j).obj (twistOver n (Spec (.of A)) (-((e : ℕ) : ℤ)))
  let α' : ⨁ f ⟶ C := biproduct.desc fun e => biproduct.desc (α e)
  refine ⟨⨁ f, α', fun m => ?_, fun e he => ?_, fun e he => ?_⟩
  · refine AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biproduct
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) m (n + 1) f fun e => ?_
    exact AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biproduct
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) m (r e) _ fun _ =>
        ProjectiveSpaceDirectImage.isPseudoCoherentFrom_singleFunctor_twistOver' n _ j m
  · refine IsGoodAt.ofIso (isGoodAt_biproduct j (n + 1) _ fun e' => ?_)
      ((twistedSections n e).mapBiproduct f).symm
    refine IsGoodAt.ofIso (isGoodAt_biproduct j (r e') _ fun _ => ?_)
      ((twistedSections n e).mapBiproduct _).symm
    exact isGoodAt_twistedSections_singleFunctor n e j _ (by have := e'.is_lt; omega)
  · rw [ModuleCat.epi_iff_surjective, ← LinearMap.range_eq_top]
    let E : Fin (n + 1) := ⟨e, by omega⟩
    refine eq_top_iff.2 ((hg E).symm.le.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((twistedSections n e).map
        (biproduct.ι _ k ≫ biproduct.ι f E))).hom (z E k), ?_⟩
    rw [← hz E k, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    congr 3
    simp [α', E]

/-! ### The induction -/

variable {n} in
/-- An object `C` of `D_QCoh(𝒪_{ℙⁿ_A})` whose twisted global sections, `0 ≤ e ≤ n`, are
pseudo-coherent with no cohomology above degree `j` is `(j + 1 - N)`-pseudo-coherent for every
`N`. -/
theorem isPseudoCoherentFrom_of_isGoodAt (N : ℕ) :
    ∀ (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (j : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj C).IsQuasicoherent) →
      (∀ e : ℕ, e ≤ n → IsGoodAt j ((twistedSections n e).obj C)) →
      RingedSpace.IsPseudoCoherentFrom
        (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C (j + 1 - N) := by
  induction N with
  | zero =>
    intro C j hqc hC
    have hz := isZero_homology_of_twists n C hqc (j + 1) fun d hd i hi => (hC d hd).2 i (by omega)
    have hle : C.IsLE (j + 1 - (0 : ℕ) - 1) := by
      rw [DerivedCategory.isLE_iff]
      exact fun i hi => hz i (by omega)
    exact Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_of_isLE
      (projectiveSpaceOver n (Spec (.of A))).toRingedSpace C _ hle
  | succ N ih =>
    intro C j hqc hC
    obtain ⟨S, α, hS, hSgood, hepi⟩ := exists_kill n C j hC
    obtain ⟨C', g, h, hT⟩ := distinguished_cocone_triangle α
    have hSqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj S).IsQuasicoherent :=
      fun i => isQuasicoherent_homology_of_isPseudoCoherentFrom _ S (i - 1) i (hS (i - 1))
        (by omega)
    have hws := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
      (projectiveSpaceOver n (Spec (.of A)))
    have hC'qc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj C').IsQuasicoherent :=
      @_root_.DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished
        (projectiveSpaceOver n (Spec (.of A))).Modules _ _
        (HasDerivedCategory.standard (projectiveSpaceOver n (Spec (.of A))).Modules)
        (SheafOfModules.isQuasicoherent (projectiveSpaceOver n (Spec (.of A))).ringCatSheaf) hws
        ((Triangle.mk α g h).rotate) (rot_of_distTriang _ hT) hqc
        (@_root_.DerivedCategoryB.derivedCategoryB_shift_mem
          (projectiveSpaceOver n (Spec (.of A))).Modules _ _
          (HasDerivedCategory.standard (projectiveSpaceOver n (Spec (.of A))).Modules)
          (SheafOfModules.isQuasicoherent (projectiveSpaceOver n (Spec (.of A))).ringCatSheaf)
          hws 1 S hSqc)
    have hC'good : ∀ e : ℕ, e ≤ n → IsGoodAt (j - 1) ((twistedSections n e).obj C') := by
      intro e he
      have hTe := (twistedSections n e).map_distinguished _ hT
      refine ⟨(StacksDraft.PseudoCoherence.isPseudoCoherent_of_distinguished _ hTe).1
        (hSgood e he).1 (hC e he).1, fun i hi => ?_⟩
      refine CategoryTheory.isZero_homology_obj₃_of_distinguished j _ hTe (fun i' hi' => ?_)
        (hepi e he) i (by omega)
      exact ⟨⟨0, ((hSgood e he).2 i' hi').eq_of_src _ _, ((hC e he).2 i' hi').eq_of_src _ _⟩⟩
    have hC' := ih C' (j - 1) hC'qc hC'good
    have hm : j + 1 - ((N + 1 : ℕ) : ℤ) = j - 1 + 1 - N := by push_cast; ring
    rw [hm]
    exact @RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished
      (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ _ _ hT (hS _) hC'

/-- Let `A` be a ring, `n ≥ 0` and `K` an object of `D_QCoh(𝒪_{ℙⁿ_A})`. If
`RΓ_A(ℙⁿ_A, K ⊗^𝐋 𝒪(d))` is a pseudo-coherent object of `D(A)` for `d = 0, 1, …, n`, then `K` is
pseudo-coherent ([Stacks, Tag 0CSG], (5) ⟹ (1)). -/
theorem isPseudoCoherent_of_twists
    (K : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (h : ∀ d : ℕ, d ≤ n → StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A))).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (projectiveSpaceOver n (Spec (.of A))).sheaf).obj K).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) d))))) :
    RingedSpace.IsPseudoCoherent (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) K := by
  have hb : ∀ d : Fin (n + 1), ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((twistedSections n (d : ℕ)).obj K)) := fun d =>
    StacksDraft.PseudoCoherence.isZero_homology_of_isPseudoCoherent (h d (by omega))
  choose b hb using hb
  let j₀ : ℤ := ∑ d : Fin (n + 1), |b d|
  have hj₀ : ∀ d : Fin (n + 1), b d ≤ j₀ := fun d =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun d => |b d|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ d))
  have hgood : ∀ e : ℕ, e ≤ n → IsGoodAt j₀ ((twistedSections n e).obj K) := fun e he =>
    ⟨h e he, fun i hi => hb ⟨e, by omega⟩ i (by have := hj₀ ⟨e, by omega⟩; omega)⟩
  have hall : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) K m := fun m => by
    obtain ⟨P, hP, e⟩ := isPseudoCoherentFrom_of_isGoodAt (j₀ + 1 - m).toNat K j₀ hK hgood
    exact ⟨P, hP.mono (by omega), e⟩
  obtain ⟨P, -, ⟨e⟩⟩ := hall 0
  exact ⟨P, fun m => RingedSpace.isPseudoCoherentComplexFrom_of_iso K m (hall m) P e, ⟨e⟩⟩

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence

end
