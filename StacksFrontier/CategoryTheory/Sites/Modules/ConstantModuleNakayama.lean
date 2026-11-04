module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
public import StacksFrontier.Homology.ConstMapHomologicalComplexKFlat
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing
public import StacksFrontier.Homology.DerivedComplete.TriangulatedReflection
public import StacksFrontier.Homology.DerivedComplete.LinearFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorProjective
public import StacksFrontier.Homology.TotalComplexTransportFinite
public import StacksFrontier.Homology.Tor.DerivedTensorToTotalComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Derived Nakayama for sheaves of modules over a constant ring

Let `Λ` be a commutative ring, `I ⊆ Λ` a finitely generated ideal, and `C` an object of the
derived category of sheaves of `Λ`-modules on a site which is derived complete along `I`. If
`C ⊗^L_Λ Λ/I = 0`, then `C = 0`. The proof reduces to the derived Nakayama lemma for complexes of
`Λ`-modules (Stacks 0G1U) by taking derived sections over every object of the site: derived
sections commute with countable products and with tensoring by a perfect complex of
`Λ`-modules, so they carry `C` to derived complete complexes whose reduction modulo `I`
vanishes, and an object of the derived category of sheaves all of whose derived sections vanish
is zero.

## Main results

* `Stacks.ConstantModuleTensor.acyclic_of_isDerivedComplete_of_acyclic_tensor`: a K-injective
  complex of sheaves of `Λ`-modules which is derived complete along a finitely generated ideal `I`
  and whose derived tensor product with `Λ/I` is acyclic is itself acyclic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe w v₁

namespace Stacks.ConstantModuleTensor

variable {C : Type w} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]

/-- Sections over an object of the site, as a functor on sheaves of `Λ`-modules. -/
abbrev sectionsFunctor (U : C) : Sheaf J (ModuleCat.{w} Λ) ⥤ ModuleCat.{w} Λ :=
  sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} Λ)).obj (op U)

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- The functor of sections over `U` is additive. -/
instance additive_sectionsFunctor (U : C) : (sectionsFunctor J Λ U).Additive where
  map_add := rfl

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- The functor of sections over `U` is `Λ`-linear. -/
instance linear_sectionsFunctor (U : C) : (sectionsFunctor J Λ U).Linear Λ where
  map_smul _ _ := rfl

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- A cochain complex isomorphic to an acyclic complex is acyclic. -/
theorem _root_.HomologicalComplex.acyclic_of_iso' {D : Type*} [Category D] [Abelian D]
    {K L : CochainComplex D ℤ} (e : K ≅ L) (h : L.Acyclic) : K.Acyclic := fun i => by
  have hi := h i
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hi ⊢
  exact hi.of_iso (HomologicalComplex.homologyMapIso e i)

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- A complex of sheaves whose complexes of sections over every object are acyclic is acyclic. -/
theorem acyclic_of_forall_acyclic_sectionsFunctor [HasSheafify J (ModuleCat.{w} Λ)]
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (h : ∀ U : C, (((sectionsFunctor J Λ U).mapHomologicalComplex _).obj K).Acyclic) :
    K.Acyclic := by
  have hpre : (((sheafToPresheaf J _).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
    (HomologicalComplex.acyclic_iff_forall_evaluation _).2 fun U => h U.unop
  have hsh : ((((sheafToPresheaf J _ ⋙ presheafToSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)).Acyclic := fun i => by
    rw [HomologicalComplex.exactAt_iff]
    exact (hpre i).map (presheafToSheaf J (ModuleCat.{w} Λ))
  have : IsIso (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit := inferInstance
  exact HomologicalComplex.acyclic_of_iso'
    ((NatIso.mapHomologicalComplex (asIso (sheafificationAdjunction J _).counit)
      (ComplexShape.up ℤ)).app K).symm hsh

section Complete

/-- The category of `Λ`-modules has limits indexed by `Discrete ℕ`. -/
local instance (priority := high) hasLimitsOfShape_discrete_nat_moduleCat :
    HasLimitsOfShape (Discrete ℕ) (ModuleCat.{w} Λ) :=
  ModuleCat.hasLimitsOfShape

attribute [local instance] HasDerivedCategory.standard

variable [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} Λ))]

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- A map between K-injective complexes which becomes an isomorphism in the derived category is
an isomorphism in the homotopy category. -/
theorem isIso_quotient_map_of_isIso_Q {D : Type*} [Category D] [Abelian D]
    {K L : CochainComplex D ℤ} [K.IsKInjective] [L.IsKInjective] (φ : K ⟶ L)
    (h : IsIso (DerivedCategory.Q.map φ)) :
    IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map φ) := by
  have h' :
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map φ)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) φ).2 h
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient D _).obj L) K).2
      (inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map φ)))
  refine ⟨ψ, ?_, ?_⟩ <;> apply (CochainComplex.IsKInjective.Qh_map_bijective _ _).1 <;>
    simp [hψ]

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- An additive functor carries a map of complexes which is an isomorphism in the homotopy
category to a map which is an isomorphism in the derived category. -/
theorem isIso_Q_map_mapHomologicalComplex_map {D E : Type*} [Category D] [Abelian D]
    [Category E] [Abelian E] (F : D ⥤ E) [F.Additive] {K L : CochainComplex D ℤ} (φ : K ⟶ L)
    [IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map φ)] :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) := by
  have : IsIso ((HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
    inferInstanceAs (IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map φ)))
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso E) _).1
    (inferInstanceAs (IsIso (DerivedCategory.Qh.map _)))

variable [HasProductsOfShape ℕ (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
  [HasProductsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))]

/-- **Derived sections preserve derived completeness.** If `K` is K-injective and represents an
object derived complete at `f`, then its complex of sections over `U` represents an object of
`D(Λ)` derived complete at `f`. -/
theorem isDerivedCompleteAt_Q_sectionsFunctor (U : C)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) [K.IsKInjective] (f : Λ)
    (h : IsDerivedCompleteAt (DerivedCategory.Q.obj K) f) :
    IsDerivedCompleteAt
      (DerivedCategory.Q.obj (((sectionsFunctor J Λ U).mapHomologicalComplex _).obj K)) f := by
  have hS : HasLimitsOfShape (Discrete ℕ) (Sheaf J (ModuleCat.{w} Λ)) := ‹_›
  have hX : ∀ n : ℤ, HasProduct fun _ : ℕ => K.X n := fun _ => hS.has_limit _
  have hC : HasLimitsOfShape (Discrete ℕ) (CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :=
    ⟨fun F => by
      have := fun n => hS.has_limit (F ⋙ HomologicalComplex.eval _ _ n)
      exact ⟨⟨⟨_, HomologicalComplex.isLimitConeOfHasLimitEval F⟩⟩⟩⟩
  let P := ∏ᶜ fun _ : ℕ => K
  have hP : P.IsKInjective :=
    Stacks.Injectives.KInjectiveProduct.product_mathlib_isKInjective _ fun _ => inferInstance
  let hL := AlgebraicGeometry.RingedSite.isLimit_fan_Q_pi (fun _ : ℕ => K) fun _ => inferInstance
  let e := hL.conePointUniqueUpToIso (limit.isLimit (Discrete.functor fun _ : ℕ =>
    DerivedCategory.Q.obj K))
  have he : ∀ n, e.hom ≫ Pi.π _ n = DerivedCategory.Q.map (Pi.π (fun _ : ℕ => K) n) := fun n =>
    hL.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
  have hσ : DerivedCategory.Q.map (oneSubSmulShift K f) ≫ e.hom =
      e.hom ≫ oneSubSmulShift (DerivedCategory.Q.obj K) f := by
    refine Pi.hom_ext _ _ fun n => ?_
    rw [Category.assoc, he, ← Functor.map_comp, oneSubSmulShift_π, Category.assoc,
      oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, he, he, Functor.map_sub,
      Functor.map_smul]
  have h1 : IsIso (DerivedCategory.Q.map (oneSubSmulShift K f)) := by
    rw [isDerivedCompleteAt_iff_isIso] at h
    rw [show DerivedCategory.Q.map (oneSubSmulShift K f) =
        e.hom ≫ oneSubSmulShift (DerivedCategory.Q.obj K) f ≫ e.inv by
      rw [← Category.assoc, ← hσ, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
    infer_instance
  have h2 := isIso_quotient_map_of_isIso_Q (oneSubSmulShift K f) h1
  let G := (sectionsFunctor J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)
  have hG : G.Linear Λ := ⟨fun _ _ => by ext; simp [G]⟩
  have h3 : IsIso ((G ⋙ DerivedCategory.Q).map (oneSubSmulShift K f)) :=
    isIso_Q_map_mapHomologicalComplex_map _ _
  have hQp : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := ModuleCat.{w} Λ)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  have e := DerivedCompletionReflection.map_oneSubSmulShift_comp_piComparison
    (G ⋙ DerivedCategory.Q) K f
  rw [← IsIso.inv_comp_eq] at e
  rw [isDerivedCompleteAt_iff_isIso]
  change IsIso (oneSubSmulShift ((G ⋙ DerivedCategory.Q).obj K) f)
  rw [← e]
  infer_instance

end Complete

section Tensor

variable {J Λ}

/-- Sections over `U` of `S ⊗_Λ Q` are `Q ⊗_Λ S(U)`, for `Q` finitely generated projective. -/
def sectionsTensorIso (U : C) (S : Sheaf J (ModuleCat.{w} Λ)) (Q : ModuleCat.{w} Λ)
    [Module.Finite Λ Q] [Module.Projective Λ Q] :
    (sectionsFunctor J Λ U).obj (((sheafTensor J Λ).obj S).obj Q) ≅
      Q ⊗ (sectionsFunctor J Λ U).obj S :=
  (sectionsFunctor J Λ U).mapIso ((flipObjIsoTensorProjectiveFunctor J Q).app S)

/-- The isomorphism `sectionsTensorIso U S Q` is natural in `Q`. -/
theorem sectionsTensorIso_naturality_right (U : C) (S : Sheaf J (ModuleCat.{w} Λ))
    {Q Q' : ModuleCat.{w} Λ} [Module.Finite Λ Q] [Module.Projective Λ Q] [Module.Finite Λ Q']
    [Module.Projective Λ Q'] (g : Q ⟶ Q') :
    (sectionsFunctor J Λ U).map (((sheafTensor J Λ).obj S).map g) ≫
        (sectionsTensorIso U S Q').hom =
      (sectionsTensorIso U S Q).hom ≫ (g ▷ (sectionsFunctor J Λ U).obj S) := by
  have h := congrArg (sectionsFunctor J Λ U).map
    (flipObjIsoTensorProjectiveFunctor_naturality_right J g S)
  rwa [Functor.map_comp, Functor.map_comp] at h

/-- The isomorphism `sectionsTensorIso U S Q` is natural in `S`. -/
theorem sectionsTensorIso_naturality_left (U : C) {S S' : Sheaf J (ModuleCat.{w} Λ)}
    (f : S ⟶ S') (Q : ModuleCat.{w} Λ) [Module.Finite Λ Q] [Module.Projective Λ Q] :
    (sectionsFunctor J Λ U).map (((sheafTensor J Λ).map f).app Q) ≫
        (sectionsTensorIso U S' Q).hom =
      (sectionsTensorIso U S Q).hom ≫ (Q ◁ (sectionsFunctor J Λ U).map f) := by
  have h := congrArg (sectionsFunctor J Λ U).map
    ((flipObjIsoTensorProjectiveFunctor J Q).hom.naturality f)
  rwa [Functor.map_comp, Functor.map_comp] at h

/-- Sections of the bicomplex of `K ⊗_Λ P` over `U` are the bicomplex of `K(U) ⊗_Λ P`, for `P` a
complex of finitely generated projective modules. -/
def sectionsTensorBicomplexIso (U : C) (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) [∀ q, Module.Finite Λ (P.X q)]
    [∀ q, Module.Projective Λ (P.X q)] :
    HomologicalComplex₂.mapBicomplex (sectionsFunctor J Λ U)
        (((sheafTensor J Λ).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K |>.obj P) ≅
      ((curriedTensor (ModuleCat.{w} Λ)).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj (((sectionsFunctor J Λ U).mapHomologicalComplex _).obj K)
        |>.obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => sectionsTensorIso U (K.X p) (P.X q) ≪≫
        β_ (P.X q) ((sectionsFunctor J Λ U).obj (K.X p)))
      (fun q q' _ => by
        change (sectionsTensorIso U (K.X p) (P.X q)).hom ≫
            (β_ (P.X q) ((sectionsFunctor J Λ U).obj (K.X p))).hom ≫
            ((sectionsFunctor J Λ U).obj (K.X p) ◁ P.d q q') =
          (sectionsFunctor J Λ U).map (((sheafTensor J Λ).obj (K.X p)).map (P.d q q')) ≫
            (sectionsTensorIso U (K.X p) (P.X q')).hom ≫
            (β_ (P.X q') ((sectionsFunctor J Λ U).obj (K.X p))).hom
        rw [← BraidedCategory.braiding_naturality_left, ← Category.assoc,
          ← sectionsTensorIso_naturality_right, Category.assoc]))
    (fun p p' _ => by
      refine HomologicalComplex.hom_ext _ _ fun q => ?_
      change (sectionsTensorIso U (K.X p) (P.X q)).hom ≫
          (β_ (P.X q) ((sectionsFunctor J Λ U).obj (K.X p))).hom ≫
          ((sectionsFunctor J Λ U).map (K.d p p') ▷ P.X q) =
        (sectionsFunctor J Λ U).map (((sheafTensor J Λ).map (K.d p p')).app (P.X q)) ≫
          (sectionsTensorIso U (K.X p') (P.X q)).hom ≫
          (β_ (P.X q) ((sectionsFunctor J Λ U).obj (K.X p'))).hom
      rw [← BraidedCategory.braiding_naturality_right, ← Category.assoc,
        ← sectionsTensorIso_naturality_left, Category.assoc])

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- A complex whose identity is null-homotopic is acyclic. -/
theorem _root_.HomologicalComplex.acyclic_of_homotopy_id_zero {D : Type*} [Category D] [Abelian D]
    {T : CochainComplex D ℤ} (H : Homotopy (𝟙 T) 0) : T.Acyclic := fun n => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have := H.homologyMap_eq n
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at this

/-- **Sections of `K ⊗_Λ P` over `U`.** If `K` is K-injective, `P` is a bounded complex of finitely
generated projective modules and `Tot(K ⊗_Λ P)` is acyclic, then `Tot(K(U) ⊗_Λ P)` is acyclic:
`Tot(K ⊗_Λ P)` is K-injective and acyclic, hence contractible, so its sections are contractible,
and they are `Tot(K(U) ⊗_Λ P)`. -/
theorem acyclic_sectionsFunctor_tensor (U : C) (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    [K.IsKInjective] (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ) [P.IsStrictlyLE b]
    [P.IsStrictlyGE a] [∀ q, Module.Finite Λ (P.X q)] [∀ q, Module.Projective Λ (P.X q)]
    (h : (CochainComplex.KFlatBifunctor.totalComplex (sheafTensor J Λ) K P).Acyclic) :
    ((((sectionsFunctor J Λ U).mapHomologicalComplex _).obj K) ⊗ P).Acyclic := by
  have hT := isKInjective_totalComplex J K P a b fun q => ⟨inferInstance, inferInstance⟩
  obtain ⟨H⟩ := hT.nonempty_homotopy_zero (𝟙 _) h
  have hΓ := HomologicalComplex.acyclic_of_homotopy_id_zero
    (((sectionsFunctor J Λ U).mapHomotopy H).trans (Homotopy.ofEq (by simp)) |>.symm.trans
      (Homotopy.ofEq (by simp)) |>.symm)
  classical
  let B := (((sheafTensor J Λ).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K).obj P
  have hfin : ∀ n : ℤ, ∃ s : Finset ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n}), ∀ i ∉ s, IsZero ((B.X i.1.1).X i.1.2) := fun n => by
    refine ⟨(Finset.Icc a b).image fun q => ⟨(n - q, q), by
      change (n - q) + q = n
      omega⟩, fun i hi => ?_⟩
    have hq : i.1.2 ∉ Finset.Icc a b := fun hq => hi (Finset.mem_image.2 ⟨i.1.2, hq, by
      have h2 := i.2
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h2
      change i.1.1 + i.1.2 = n at h2
      apply Subtype.ext
      ext
      · change n - i.1.2 = i.1.1
        omega
      · rfl⟩)
    have hz : IsZero (P.X i.1.2) := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
      rcases hq with hq | hq
      · exact P.isZero_of_isStrictlyGE a _ hq
      · exact P.isZero_of_isStrictlyLE b _ hq
    exact ((sheafTensor J Λ).obj (K.X i.1.1)).map_isZero hz
  have hiso := HomologicalComplex₂.isIso_totalMap_of_finite_support (c₁₂ := ComplexShape.up ℤ)
    (sectionsFunctor J Λ U) B hfin
  exact HomologicalComplex.acyclic_of_iso'
    (HomologicalComplex₂.total.mapIso (sectionsTensorBicomplexIso U K P).symm (ComplexShape.up ℤ) ≪≫
      asIso (HomologicalComplex₂.totalMap (c₁₂ := ComplexShape.up ℤ) (sectionsFunctor J Λ U) B)) hΓ

end Tensor

section Nakayama

attribute [local instance] HasDerivedCategory.standard

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- A cochain complex is acyclic if and only if its image in the derived category is zero. -/
theorem _root_.HomologicalComplex.acyclic_iff_isZero_Q {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (K : CochainComplex D ℤ) :
    K.Acyclic ↔ IsZero (DerivedCategory.Q.obj K) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · have hn := h n
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hn
    exact hn.of_iso ((DerivedCategory.homologyFunctorFactors D n).app K)
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (h n).of_iso ((DerivedCategory.homologyFunctorFactors D n).app K).symm

variable [HasProductsOfShape ℕ (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
  [HasProductsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} Λ))]

/-- **Derived Nakayama for sheaves of `Λ`-modules.** Let `I ⊆ Λ` be a finitely generated ideal,
`P` a bounded complex of finitely generated projective modules representing `Λ/I`, and `K` a
K-injective complex of sheaves of `Λ`-modules which is derived complete along `I`. If
`Tot(K ⊗_Λ P)` (that is, `K ⊗^L_Λ Λ/I`) is acyclic, then `K` is acyclic. -/
theorem acyclic_of_isDerivedComplete_of_acyclic_tensor (I : Ideal Λ) (hI : I.FG)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) [K.IsKInjective]
    (hC : IsDerivedComplete I (DerivedCategory.Q.obj K))
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ) [P.IsStrictlyLE b] [P.IsStrictlyGE a]
    [∀ q, Module.Finite Λ (P.X q)] [∀ q, Module.Projective Λ (P.X q)]
    (eP : (DerivedCategory.singleFunctor (ModuleCat.{w} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)) ≅
      DerivedCategory.Q.obj P)
    (h : (CochainComplex.KFlatBifunctor.totalComplex (sheafTensor J Λ) K P).Acyclic) :
    K.Acyclic := by
  refine acyclic_of_forall_acyclic_sectionsFunctor J Λ K fun U => ?_
  set E := ((sectionsFunctor J Λ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hcomp : IsDerivedComplete I (DerivedCategory.Q.obj E) := fun f hf =>
    isDerivedCompleteAt_Q_sectionsFunctor J Λ U K f (hC f hf)
  have hEP := acyclic_sectionsFunctor_tensor U K P a b h
  have hflat : CochainComplex.KFlat P := CochainComplex.KFlat.kFlat_of_flat P b
  have hiso := CochainComplex.DerivedTensor.ToTotal.isIso_derivedToTensorNatTrans_app
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Λ) E P hflat
  have hred : IsZero (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor Λ).obj
      (DerivedCategory.Q.obj E)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)))) := by
    refine IsZero.of_iso ?_ ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
      Λ).obj (DerivedCategory.Q.obj E)).mapIso eP) ≪≫
        @asIso _ _ _ _ ((CochainComplex.DerivedTensor.ToTotal.derivedToTensorNatTrans
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Λ)).app (E, P)) hiso)
    exact (HomologicalComplex.acyclic_iff_isZero_Q _).1 hEP
  exact (HomologicalComplex.acyclic_iff_isZero_Q E).2
    (KoszulTensorVanishing.isZero_of_isDerivedComplete_of_derivedTensorProduct_mod_ideal_isZero
      I hI _ hcomp hred)

end Nakayama

end Stacks.ConstantModuleTensor
