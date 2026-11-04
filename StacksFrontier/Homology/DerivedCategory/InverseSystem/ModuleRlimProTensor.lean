module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# Derived limits after tensoring a pro-isomorphism

Let `E ⟶ D` be a morphism in the derived category of inverse systems of modules over a
commutative ring. If the induced morphism between the associated systems in `D(A)` is an
isomorphism of pro-objects, then tensoring pointwise with any object of `D(A)` and applying the
right-derived inverse-limit functor gives an isomorphism.

## Main definitions

* `ModuleSystemRlimProTensor.derivedEvaluationFunctor`: the functor from `D(ℕ, A)` to inverse
  systems in `D(A)` induced by derived evaluation.

## Main results

* `ModuleSystemRlimProTensor.derivedLimit_tensor_map_isIso_of_proIsomorphism`: pointwise derived
  tensor product followed by derived inverse limit maps a pro-isomorphism to an isomorphism.

## Implementation notes

The associated system is assembled from the derived evaluation functors and the restriction
maps of a compatible module system. Thus its action on a morphism and its compatibility with all
index transitions are functorial. The functor in the conclusion is the canonical system-valued
derived tensor product of Stacks 091H, applied to the canonical constant system of `K`, followed
by the right-derived inverse-limit functor of Stacks 091J.

Stacks 091L is deduced from the definitions and Stacks 091B. Since 091B is stated for abelian
groups only, its argument — pro-isomorphisms preserve homology pro-systems, and a derived limit
of a system with pro-zero cohomology vanishes by the Milnor sequence — is replayed here for
module systems.

## References

* [Stacks Project, Tag 091L](https://stacks.math.columbia.edu/tag/091L)
-/


namespace ModuleSystemRlimProTensor

section Definitions

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

attribute [local instance] HasDerivedCategory.standard

universe u



/-- The transition between evaluation functors on compatible systems over a constant ring
diagram. -/
public noncomputable def evaluationTransition
    (A : Type u) [CommRing A] {a b : ℕᵒᵖ} (f : a ⟶ b) :
    PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) a ⟶
      PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) b :=
  PresheafOfModules.restriction _ f ≫
    Functor.whiskerLeft _
      (ModuleCat.restrictScalarsId'.{u}
        (((Functor.const ℕᵒᵖ).obj (RingCat.of A)).map f).hom rfl).hom

private theorem evaluationTransition_id
    (A : Type u) [CommRing A] (a : ℕᵒᵖ) :
    evaluationTransition A (𝟙 a) = 𝟙 _ := by
  unfold evaluationTransition
  ext X x
  simp only [Functor.const_obj_obj, Functor.const_obj_map, RingCat.hom_id, NatTrans.comp_app,
    Functor.comp_obj, PresheafOfModules.restriction_app, PresheafOfModules.map_id,
    ModuleCat.restrictScalarsId'_inv_app, Functor.whiskerLeft_app,
    ModuleCat.restrictScalarsId'_hom_app, NatTrans.id_app, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq]
  show x = x
  rfl

private theorem evaluationTransition_comp
    (A : Type u) [CommRing A] {a b c : ℕᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    evaluationTransition A (f ≫ g) =
      evaluationTransition A (a := a) (b := b) f ≫
        evaluationTransition A (a := b) (b := c) g := by
  unfold evaluationTransition
  ext X x
  show X.map (f ≫ g) x = X.map g (X.map f x)
  simp
  rfl

/-- The transition between derived evaluation functors induced by a morphism of indices. -/
public noncomputable def derivedEvaluationTransition
    (A : Type u) [CommRing A] {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) a).mapDerivedCategory ⟶
      (PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) b).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (PresheafOfModules ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))
      (ComplexShape.up ℤ))
    (((PresheafOfModules.evaluation
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) a).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (((PresheafOfModules.evaluation
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) b).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (PresheafOfModules.evaluation
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) a).mapDerivedCategory
    (PresheafOfModules.evaluation
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) b).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (evaluationTransition A (a := a) (b := b) f)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The inverse system in `D(A)` obtained by derived evaluation of an object of `D(ℕ, A)`. -/
public noncomputable def derivedEvaluationSystem
    (A : Type u) [CommRing A]
    (E : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))) :
      ℕᵒᵖ ⥤ CochainComplex.DerivedTensor.DObj A where
  obj n := (PresheafOfModules.evaluation
    ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) n).mapDerivedCategory.obj E
  map {a b} f := (derivedEvaluationTransition A f).app E
  map_id X := by
    unfold derivedEvaluationTransition
    rw [evaluationTransition_id, NatTrans.mapHomologicalComplex_id,
      Functor.whiskerRight_id']
    rw [Localization.liftNatTrans_id]
    rfl
  map_comp {X Y Z} f g := by
    have h : derivedEvaluationTransition A (f ≫ g) =
        derivedEvaluationTransition A (a := X) (b := Y) f ≫
          derivedEvaluationTransition A (a := Y) (b := Z) g := by
      unfold derivedEvaluationTransition
      rw [evaluationTransition_comp,
        NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso
          (PresheafOfModules ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))
          (ComplexShape.up ℤ))
      intro X
      simp [Localization.liftNatTrans_app]
    simpa only [NatTrans.comp_app] using congrArg (fun η => η.app E) h

/-- The object of `derivedEvaluationSystem A E` at `n` is the derived evaluation of `E` at `n`. -/
@[simp]
public theorem derivedEvaluationSystem_obj
    (A : Type u) [CommRing A]
    (E : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))) (n : ℕᵒᵖ) :
    (derivedEvaluationSystem A E).obj n =
      (PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) n).mapDerivedCategory.obj E := rfl

/-- The transition map of `derivedEvaluationSystem A E` along `f` is the component at `E` of the
natural transformation `derivedEvaluationTransition A f`. -/
@[simp]
public theorem derivedEvaluationSystem_map
    (A : Type u) [CommRing A]
    (E : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A))))
    {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (derivedEvaluationSystem A E).map f = (derivedEvaluationTransition A f).app E := rfl

/-- The map of associated evaluation systems induced by a morphism in `D(ℕ, A)`. -/
public noncomputable def derivedEvaluationSystemMap
    (A : Type u) [CommRing A]
    {E D : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))} (f : E ⟶ D) :
    derivedEvaluationSystem A E ⟶ derivedEvaluationSystem A D where
  app n := (PresheafOfModules.evaluation
    ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) n).mapDerivedCategory.map f
  naturality _ _ g := (derivedEvaluationTransition A g).naturality f |>.symm

/-- The component at `n` of `derivedEvaluationSystemMap A f` is the derived evaluation of `f` at
`n`. -/
@[simp]
public theorem derivedEvaluationSystemMap_app
    (A : Type u) [CommRing A]
    {E D : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))}
    (f : E ⟶ D) (n : ℕᵒᵖ) :
    (derivedEvaluationSystemMap A f).app n =
      (PresheafOfModules.evaluation
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) n).mapDerivedCategory.map f := rfl

/-- Derived evaluation, including all transition maps, is functorial in a compatible derived
module system. -/
public noncomputable def derivedEvaluationFunctor
    (A : Type u) [CommRing A] :
    DerivedCategory
        (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ⥤
      (ℕᵒᵖ ⥤ CochainComplex.DerivedTensor.DObj A) where
  obj := derivedEvaluationSystem A
  map := derivedEvaluationSystemMap A
  map_id E := by
    ext n
    simp [derivedEvaluationSystemMap]
  map_comp f g := by
    ext n
    simp [derivedEvaluationSystemMap]


end
end Definitions

section Construction

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory Opposite ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe vC uC vD uD u

private theorem proIso_whisker {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] {X Y : ℕᵒᵖ ⥤ C} (f : X ⟶ Y)
    (hf : IsIso (Rlim.Pro.proMap f)) (F : C ⥤ D) :
    IsIso (Rlim.Pro.proMap (Functor.whiskerRight f F)) := by
  refine Rlim.Pro.isIso_proMap_of_inverse _ fun n => ?_
  obtain ⟨m, a, g, hg, hg'⟩ := Rlim.Pro.exists_proInverse f n
  exact ⟨m, a, F.map g,
    by simpa only [Functor.map_comp, Functor.whiskerRight_app, Functor.comp_map]
      using congrArg F.map hg,
    by simpa only [Functor.map_comp, Functor.whiskerRight_app, Functor.comp_map]
      using congrArg F.map hg'⟩

section

variable {C : Type uC} [Category.{vC} C] [Preadditive C]

private lemma transition_eq_zero_of_proZero (G : ℕᵒᵖ ⥤ C)
    (hG : ∀ n : ℕᵒᵖ, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), G.map f = 0) (n : ℕ) :
    ∃ N : ℕ, ∀ k, N ≤ k → G.map (homOfLE (Nat.le_add_right n k)).op = 0 := by
  obtain ⟨m, f, hf⟩ := hG (op n)
  refine ⟨m.unop - n, fun k hk => ?_⟩
  have h₁ : m.unop ≤ n + k := by have := leOfHom f.unop; omega
  rw [show (homOfLE (Nat.le_add_right n k)).op = (homOfLE h₁).op ≫ f from rfl, G.map_comp, hf,
    comp_zero]

private lemma isSplitEpi_one_sub_shift_of_proZero (G : ℕᵒᵖ ⥤ C)
    [HasProduct fun n : ℕ => G.obj (op n)]
    (hG : ∀ n : ℕᵒᵖ, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), G.map f = 0) :
    IsSplitEpi (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => G.obj (op n)) n -
        Pi.π (fun n : ℕ => G.obj (op n)) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) := by
  choose N hN using transition_eq_zero_of_proZero G hG
  let t : ℕ → ∀ n : ℕ, (∏ᶜ fun n : ℕ => G.obj (op n)) ⟶ G.obj (op n) := fun k n =>
    Pi.π (fun n : ℕ => G.obj (op n)) (n + k) ≫ G.map (homOfLE (Nat.le_add_right n k)).op
  have ht : ∀ n k, N n ≤ k → t k n = 0 := fun n k hk => by
    simp only [t, hN n k hk, comp_zero]
  have hsucc : ∀ n k, t k (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op = t (k + 1) n := by
    intro n k
    simp only [t, Category.assoc, ← G.map_comp]
    have key : ∀ (a b : ℕ) (_ : a = b) (f₁ : op a ⟶ op n) (f₂ : op b ⟶ op n),
        Pi.π (fun n : ℕ => G.obj (op n)) a ≫ G.map f₁ =
          Pi.π (fun n : ℕ => G.obj (op n)) b ≫ G.map f₂ := by
      rintro a _ rfl f₁ f₂
      rw [Subsingleton.elim f₁ f₂]
    exact key _ _ (by omega) _ _
  have hstable : ∀ n M, N n ≤ M → ∑ k ∈ Finset.range M, t k n =
      ∑ k ∈ Finset.range (N n), t k n := by
    intro n M hM
    induction M, hM using Nat.le_induction with
    | base => rfl
    | succ M hM ih => rw [Finset.sum_range_succ, ht n M hM, add_zero, ih]
  refine ⟨⟨Pi.lift fun n => ∑ k ∈ Finset.range (N n), t k n, ?_⟩⟩
  apply Pi.hom_ext
  intro n
  let M := max (N n) (N (n + 1) + 1)
  rw [Category.assoc, Pi.lift_π, Preadditive.comp_sub, Pi.lift_π, ← Category.assoc,
    Pi.lift_π, Preadditive.sum_comp, Category.id_comp]
  simp_rw [hsucc]
  have h₁ := hstable n M (le_max_left _ _)
  have h₂ := hstable (n + 1) (M - 1) (by omega)
  have hM : M = (M - 1) + 1 := by omega
  rw [← h₁, hM, Finset.sum_range_succ']
  have h₃ : ∑ k ∈ Finset.range (N (n + 1)), t (k + 1) n =
      ∑ k ∈ Finset.range (M - 1), t (k + 1) n := by
    simp_rw [← hsucc, ← Preadditive.sum_comp, ← h₂]
  rw [h₃, add_sub_cancel_left]
  simp [t]

end

section

variable {𝒜 : Type uC} [Category.{vC} 𝒜] [Abelian 𝒜]
  [HasProductsOfShape ℕ 𝒜] [HasExactLimitsOfShape (Discrete ℕ) 𝒜]
  [HasLimitsOfShape ℕᵒᵖ 𝒜] [HasDerivedCategory.{vD} 𝒜]

private theorem isZero_of_isDerivedLimit_of_homology_proZero
    (F : ℕᵒᵖ ⥤ DerivedCategory 𝒜) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (K : DerivedCategory 𝒜) (hK : Pretriangulated.IsDerivedLimit F K)
    (hF : ∀ (r : ℤ) (n : ℕᵒᵖ), ∃ (m : ℕᵒᵖ) (f : m ⟶ n),
      (DerivedCategory.homologyFunctor 𝒜 r).map (F.map f) = 0) :
    IsZero K := by
  obtain ⟨a, b, -, hr⟩ := DerivedCategory.isDerivedLimit_homology_shortExact F K hK
  have hK0 : ∀ r : ℤ, IsZero ((DerivedCategory.homologyFunctor 𝒜 r).obj K) := by
    intro r
    obtain ⟨e, i, q, w, -, -, -, hses⟩ := hr r
    have hlim := Rlim.Pro.isZero_limit_of_proZero (F ⋙ DerivedCategory.homologyFunctor 𝒜 r)
      (fun n => by simpa using hF r n)
    have := isSplitEpi_one_sub_shift_of_proZero
      (F ⋙ DerivedCategory.homologyFunctor 𝒜 (r - 1)) (fun n => by simpa using hF (r - 1) n)
    have hcok : IsZero (cokernel (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (F ⋙ DerivedCategory.homologyFunctor 𝒜 (r - 1)).obj (op n)) n -
          Pi.π (fun n : ℕ => (F ⋙ DerivedCategory.homologyFunctor 𝒜 (r - 1)).obj (op n))
            (n + 1) ≫ (F ⋙ DerivedCategory.homologyFunctor 𝒜 (r - 1)).map
              (homOfLE (Nat.le_succ n)).op)) :=
      isZero_cokernel_of_epi _
    exact hses.exact.isZero_of_both_zeros (hcok.eq_of_src _ _) (hlim.eq_of_tgt _ _)
  have : IsIso (0 : K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro r
    exact isIso_of_source_target_iso_zero _ (hK0 r).isoZero
      ((Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))
end

section

variable {C : Type uC} [Category.{vC} C]

private lemma proMap_id (X : ℕᵒᵖ ⥤ C) : Rlim.Pro.proMap (𝟙 X) = 𝟙 _ := by
  simp only [Rlim.Pro.proMap, NatTrans.op_id, Functor.whiskerRight_id']
  exact colim.map_id _

private instance isIso_proMap_hom {X Y : ℕᵒᵖ ⥤ C} (e : X ≅ Y) : IsIso (Rlim.Pro.proMap e.hom) :=
  ⟨Rlim.Pro.proMap e.inv, by rw [← Rlim.Pro.proMap_comp, e.inv_hom_id, proMap_id],
    by rw [← Rlim.Pro.proMap_comp, e.hom_inv_id, proMap_id]⟩

private lemma isIso_proMap_conj {X X' Y Y' : ℕᵒᵖ ⥤ C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (h : f ≫ e₂.hom = e₁.hom ≫ f') (hf : IsIso (Rlim.Pro.proMap f)) :
    IsIso (Rlim.Pro.proMap f') := by
  have : f' = e₁.inv ≫ f ≫ e₂.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [this, Rlim.Pro.proMap_comp, Rlim.Pro.proMap_comp]
  infer_instance

end

section ModuleSystems

open Pretriangulated

attribute [local instance] ModuleSystemRlimTensor.moduleDiagramOfSystem_additive

variable (A : Type u) [CommRing A]

/-- Cochain complexes of compatible module systems over the constant ring system. -/
private abbrev SysComplex := CochainComplex
  (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ

private noncomputable abbrev evalAt (n : ℕᵒᵖ) :
    PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ⥤ ModuleCat.{u} A :=
  ModuleSystemRlimTensor.moduleDiagramOfSystem A ⋙ (evaluation ℕᵒᵖ (ModuleCat.{u} A)).obj n

private noncomputable abbrev evalQ (n : ℕᵒᵖ) :
    SysComplex A ⥤ CochainComplex.DerivedTensor.DObj A :=
  (evalAt A n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

private noncomputable def evalQIso (X : SysComplex A) :
    (derivedEvaluationFunctor A).obj (DerivedCategory.Q.obj X) ≅
      (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj X ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun n => (PresheafOfModules.evaluation _ n).mapDerivedCategoryFactors.app X) (by
    intro a b f
    change (derivedEvaluationTransition A f).app (Q.obj X) ≫ _ = _
    rw [derivedEvaluationTransition, Localization.liftNatTrans_app]
    change (_ ≫ _ ≫ (PresheafOfModules.evaluation _ b).mapDerivedCategoryFactors.inv.app X) ≫
      (PresheafOfModules.evaluation _ b).mapDerivedCategoryFactors.hom.app X = _
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    change _ ≫ Q.map _ = _ ≫ Q.map _
    congr 2)

private lemma evalQIso_naturality {X Y : SysComplex A} (g : X ⟶ Y) :
    (derivedEvaluationFunctor A).map (Q.map g) ≫ (evalQIso A Y).hom =
      (evalQIso A X).hom ≫
        Functor.whiskerRight ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map g) Q := by
  ext n
  exact (PresheafOfModules.evaluation _ n).mapDerivedCategoryFactors_hom_naturality g

private noncomputable abbrev shift1 (X : SysComplex A) : SysComplex A :=
  (shiftFunctor (SysComplex A) (1 : ℤ)).obj X

private noncomputable def shiftEvalIso (X : SysComplex A) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj (shift1 A X) ≅
      (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj X ⋙ shiftFunctor _ (1 : ℤ) :=
  NatIso.ofComponents (fun n =>
    (((evalAt A n).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app X) (by
    intro a b f
    ext i x
    rfl)

/-- The shift comparison for evaluated complexes in the derived category. -/
private noncomputable def shiftEvalQIso (X : SysComplex A) :
    (ModuleSystemRlimTensor.complexEvaluationDiagram A).obj (shift1 A X) ⋙ Q ≅
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj X ⋙ Q) ⋙ shiftFunctor _ (1 : ℤ) :=
  Functor.isoWhiskerRight (shiftEvalIso A X) Q ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Q.commShiftIso (1 : ℤ)) ≪≫ (Functor.associator _ _ _).symm

private lemma shiftEvalQIso_hom_app (X : SysComplex A) (n : ℕᵒᵖ) :
    (shiftEvalQIso A X).hom.app n = ((evalQ A n).commShiftIso (1 : ℤ)).hom.app X := by
  rw [Functor.commShiftIso_comp_hom_app]
  simp only [Functor.comp_obj, shiftEvalQIso, shiftEvalIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  rfl

private lemma evalQ_triangle_distinguished {X Y : SysComplex A} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (evalQ A n).mapTriangle.obj (CochainComplex.mappingCone.triangle g) ∈
      distTriang (CochainComplex.DerivedTensor.DObj A) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    ((Functor.mapTriangleCompIso _ _).app _ ≪≫
      Q.mapTriangle.mapIso (CochainComplex.mappingCone.mapTriangleIso g (evalAt A n)))

private lemma evalQ_map_inr_comp_mor₃ {X Y : SysComplex A} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (evalQ A n).map (CochainComplex.mappingCone.inr g) ≫
      (evalQ A n).map (CochainComplex.mappingCone.triangle g).mor₃ = 0 := by
  have h : (evalQ A n).map (CochainComplex.mappingCone.inr g) ≫
      (evalQ A n).map (CochainComplex.mappingCone.triangle g).mor₃ ≫
        (((evalQ A n).commShiftIso (1 : ℤ)).app X).hom = 0 :=
    comp_distTriang_mor_zero₂₃ _ (evalQ_triangle_distinguished A g n)
  exact (cancel_mono (((evalQ A n).commShiftIso (1 : ℤ)).app X).hom).mp
    ((Category.assoc _ _ _).trans (h.trans zero_comp.symm))

private lemma evalQ_map_shift_comp_commShiftIso {X Y : SysComplex A} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (evalQ A n).map ((shiftFunctor (SysComplex A) (1 : ℤ)).map g) ≫
        (((evalQ A n).commShiftIso (1 : ℤ)).app Y).hom =
      (((evalQ A n).commShiftIso (1 : ℤ)).app X).hom ≫ ((evalQ A n).map g)⟦(1 : ℤ)⟧' :=
  ((evalQ A n).commShiftIso (1 : ℤ)).hom.naturality g

private lemma evalQ_map_mor₃_comp_map_shift {X Y : SysComplex A} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (evalQ A n).map (CochainComplex.mappingCone.triangle g).mor₃ ≫
      (evalQ A n).map ((shiftFunctor (SysComplex A) (1 : ℤ)).map g) = 0 := by
  have h : ((evalQ A n).map (CochainComplex.mappingCone.triangle g).mor₃ ≫
      (((evalQ A n).commShiftIso (1 : ℤ)).app X).hom) ≫ ((evalQ A n).map g)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ (evalQ_triangle_distinguished A g n)
  exact (cancel_mono (((evalQ A n).commShiftIso (1 : ℤ)).app Y).hom).mp
    ((Category.assoc _ _ _).trans ((whisker_eq _ (evalQ_map_shift_comp_commShiftIso A g n)).trans
      ((Category.assoc _ _ _).symm.trans (h.trans zero_comp.symm))))

private lemma isIso_proMap_whisker_shift_map {X Y : SysComplex A} (g : X ⟶ Y)
    (hg : IsIso (Rlim.Pro.proMap (Functor.whiskerRight
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map g) Q)))
    (H : CochainComplex.DerivedTensor.DObj A ⥤ ModuleCat.{u} A) :
    IsIso (Rlim.Pro.proMap (Functor.whiskerRight (Functor.whiskerRight
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map
        ((shiftFunctor (SysComplex A) (1 : ℤ)).map g)) Q) H)) := by
  refine isIso_proMap_conj (Functor.isoWhiskerRight (shiftEvalQIso A X) H).symm
    (Functor.isoWhiskerRight (shiftEvalQIso A Y) H).symm ?_
    (proIso_whisker _ (proIso_whisker _ hg _) H)
  rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  refine NatTrans.ext (funext fun n => ?_)
  show H.map ((shiftEvalQIso A X).hom.app n) ≫ H.map (((evalQ A n).map g)⟦(1 : ℤ)⟧') =
    H.map ((evalQ A n).map ((shiftFunctor (SysComplex A) (1 : ℤ)).map g)) ≫
      H.map ((shiftEvalQIso A Y).hom.app n)
  rw [shiftEvalQIso_hom_app, shiftEvalQIso_hom_app]
  refine Eq.trans ?_
    ((congrArg H.map (evalQ_map_shift_comp_commShiftIso A g n).symm).trans (H.map_comp _ _))
  exact (H.map_comp _ _).symm

/-- Pointwise, the evaluated tensored cohomology of the cone of a pro-isomorphism is
pro-zero. -/
private lemma cone_homology_proZero {X Y : SysComplex A} (g : X ⟶ Y)
    (hg : IsIso (Rlim.Pro.proMap (Functor.whiskerRight
      ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map g) Q)))
    (H : CochainComplex.DerivedTensor.DObj A ⥤ ModuleCat.{u} A) [H.IsHomological] :
    ∀ n : ℕᵒᵖ, ∃ (m : ℕᵒᵖ) (f : m ⟶ n),
      H.map (Q.map (((ModuleSystemRlimTensor.complexEvaluationDiagram A).obj
        (CochainComplex.mappingCone g)).map f)) = 0 := by
  let cED := ModuleSystemRlimTensor.complexEvaluationDiagram A
  let δ : CochainComplex.mappingCone g ⟶ shift1 A X :=
    (CochainComplex.mappingCone.triangle g).mor₃
  let e (n : ℕᵒᵖ) (W : SysComplex A) := ((evalQ A n).commShiftIso (1 : ℤ)).app W
  let a := Functor.whiskerRight (Functor.whiskerRight (cED.map g) Q) H
  let b := Functor.whiskerRight (Functor.whiskerRight
    (cED.map (CochainComplex.mappingCone.inr g)) Q) H
  let c := Functor.whiskerRight (Functor.whiskerRight (cED.map δ) Q) H
  let d := Functor.whiskerRight (Functor.whiskerRight
    (cED.map ((shiftFunctor (SysComplex A) (1 : ℤ)).map g)) Q) H
  have hT := evalQ_triangle_distinguished A g
  have h₁₂ (n : ℕᵒᵖ) : (evalQ A n).map g ≫
      (evalQ A n).map (CochainComplex.mappingCone.inr g) = 0 :=
    comp_distTriang_mor_zero₁₂ _ (hT n)
  have hz : ∀ {P P' P'' : ℕᵒᵖ ⥤ CochainComplex.DerivedTensor.DObj A} (u : P ⟶ P') (v : P' ⟶ P'')
      (_ : ∀ n, u.app n ≫ v.app n = 0), Functor.whiskerRight u H ≫ Functor.whiskerRight v H = 0 :=
    fun u v h => NatTrans.ext (funext fun n => by
      change H.map (u.app n) ≫ H.map (v.app n) = 0
      rw [← H.map_comp, h n, H.map_zero])
  have hab : a ≫ b = 0 := hz _ _ h₁₂
  have hbc : b ≫ c = 0 := hz _ _ (evalQ_map_inr_comp_mor₃ A g)
  have hcd : c ≫ d = 0 := hz _ _ (evalQ_map_mor₃_comp_map_shift A g)
  have he (n : ℕᵒᵖ) : (ShortComplex.mk (b.app n) (c.app n)
      (by rw [← NatTrans.comp_app, hbc, NatTrans.app_zero])).Exact := by
    have hex := H.map_distinguished_exact _ (rot_of_distTriang _ (hT n))
    refine (ShortComplex.exact_iff_of_iso ?_).mp hex
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (H.mapIso (e n X).symm) ?_ ?_
    · erw [Category.id_comp]
    · simp only
      show H.map ((evalQ A n).map δ) = H.map ((evalQ A n).map δ ≫ (e n X).hom) ≫
        H.map (e n X).inv
      rw [← H.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ha : IsIso (Rlim.Pro.proMap a) := proIso_whisker _ hg H
  have hd : IsIso (Rlim.Pro.proMap d) := isIso_proMap_whisker_shift_map A g hg H
  exact Rlim.Pro.proZero_of_exact a b c d hab hbc hcd he

/-- A morphism of `D(ℕ, A)` inducing a pro-isomorphism is represented by a morphism of
complexes whose pointwise evaluation is a pro-isomorphism. -/
private lemma exists_complex_rep_proIso {E D : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))} (f : E ⟶ D)
    (hf : IsIso (colim.map (Functor.whiskerRight
      (NatTrans.op ((derivedEvaluationFunctor A).map f)) coyoneda))) :
    ∃ (X' Y : SysComplex A) (g : X' ⟶ Y) (α₀ : E ≅ Q.obj X') (β₀ : D ≅ Q.obj Y),
      f ≫ β₀.hom = α₀.hom ≫ Q.map g ∧ IsIso (Rlim.Pro.proMap (Functor.whiskerRight
        ((ModuleSystemRlimTensor.complexEvaluationDiagram A).map g) Q)) := by
  obtain ⟨X', s, hs, g, hfac⟩ := DerivedCategory.right_fac
    ((Q.objObjPreimageIso E).hom ≫ f ≫ (Q.objObjPreimageIso D).inv)
  let α₀ : E ≅ Q.obj X' := (Q.objObjPreimageIso E).symm ≪≫ (asIso (Q.map s)).symm
  let β₀ : D ≅ Q.obj (Q.objPreimage D) := (Q.objObjPreimageIso D).symm
  have hsq : f ≫ β₀.hom = α₀.hom ≫ Q.map g := by
    have : Q.map g = Q.map s ≫ ((Q.objObjPreimageIso E).hom ≫ f ≫
        (Q.objObjPreimageIso D).inv) := by
      rw [hfac, IsIso.hom_inv_id_assoc]
    simp [α₀, β₀, this]
  exact ⟨X', _, g, α₀, β₀, hsq,
    isIso_proMap_conj (evalQIso A X') (evalQIso A _) (evalQIso_naturality A g)
      (isIso_proMap_conj ((derivedEvaluationFunctor A).mapIso α₀)
        ((derivedEvaluationFunctor A).mapIso β₀)
        (by simp only [Functor.mapIso_hom, ← Functor.map_comp, hsq]) hf)⟩

end ModuleSystems

attribute [local instance] ModuleSystemRlimTensor.constantSystem_additive
  ModuleSystemRlimTensor.constantSystem_preservesFiniteLimits
    ModuleSystemRlimTensor.constantSystem_preservesFiniteColimits

private theorem tensor_rLim_map_isIso
    (A : Type u) [CommRing A]
    {E D : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))} (f : E ⟶ D)
    (hf : IsIso (colim.map (Functor.whiskerRight
      (NatTrans.op ((derivedEvaluationFunctor A).map f)) coyoneda)))
    (K : CochainComplex.DerivedTensor.DObj A) :
    let AR : ℕᵒᵖ ⥤ CommRingCat.{u} := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
    let R : ℕᵒᵖ ⥤ RingCat.{u} := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
    let C := PresheafOfModules.{u} R
    let DA := CochainComplex.DerivedTensor.DObj A
    let DN := DerivedCategory C
    let S := ModuleSystemKFlatComparison.derivedTensorProduct AR
    let L : C ⥤ ModuleCat.{u} (limit R : RingCat.{u}) := ModuleInverseLimit.inverseLimit R
    ∃ (ρ : (limit R : RingCat.{u}) ≅ RingCat.of A),
      letI : (ModuleCat.restrictScalars.{u} ρ.inv.hom).IsEquivalence :=
        ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
          ρ.symm.ringCatIsoToRingEquiv
      let U : DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})) ⥤ DA :=
        (ModuleCat.restrictScalars.{u} ρ.inv.hom).mapDerivedCategory
      ∃ (hL : L.Additive),
      letI := hL
      ∃ (Δ : DA ⥤ DN)
        (_ : ModuleRightDerivedLimit.derivedModuleDiagram R (Δ.obj K) ⋙ U ≅
          (Functor.const ℕᵒᵖ).obj K)
        (Rlim : DN ⥤ DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})))
        (α : L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ Rlim),
      Rlim.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
        IsIso ((S.tensor.obj (Δ.obj K) ⋙ Rlim ⋙ U).map f) := by
  obtain ⟨_, hL, -, -, -, -, -, Rlim, α, hRlimShift, hRlim, hRlimExact, hlimits, -⟩ :=
    ModuleSystemRlimTensor.exists_exactFunctor_isDerivedLimit_tensor A ((Functor.const ℕᵒᵖ).obj K)
  refine ⟨ModuleSystemRlimTensor.constantLimitIso A, hL,
    (ModuleSystemRlimTensor.constantSystem A).mapDerivedCategory,
    ModuleSystemRlimTensor.constantDerivedDiagramIso A K, Rlim, α, hRlim, ?_⟩
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let Δ := (ModuleSystemRlimTensor.constantSystem A).mapDerivedCategory
  have := ModuleSystemRlimTensor.constantLimitScalars_isEquivalence A
  let U := (ModuleSystemRlimTensor.constantLimitScalars A).mapDerivedCategory
  have : U.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence _
  let G := S.tensor.obj (Δ.obj K)
  let _ := S.commShift_right (Δ.obj K)
  have := S.exact_right (Δ.obj K)
  obtain ⟨X', Y, g, α₀, β₀, hsq, hg⟩ := exists_complex_rep_proIso A f hf
  let Z := CochainComplex.mappingCone g
  have hZ : IsZero (U.obj (Rlim.obj (G.obj (Q.obj Z)))) := by
    obtain ⟨hP, hlim⟩ := hlimits (G.obj (Q.obj Z))
    obtain ⟨_, hlim'⟩ := @ModuleSystemRlimTensor.isDerivedLimit_map_of_iso
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _
      (ModuleRightDerivedLimit.derivedModuleDiagram _ (G.obj (Q.obj Z))) _
      (ModuleSystemRlimTensor.tensorDerivedDiagramIso A Z K) hP _ hlim
    exact isZero_of_isDerivedLimit_of_homology_proZero _ _ hlim' fun r =>
      cone_homology_proZero A g hg (T.tensor.obj K ⋙ homologyFunctor _ r)
  let Gf := G ⋙ Rlim ⋙ U
  have hT' := Gf.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished g)
  have hiso : IsIso (Gf.map (Q.map g)) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT').mp hZ
  show IsIso (Gf.map f)
  rw [show f = α₀.hom ≫ Q.map g ≫ β₀.inv by
    rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id],
    Gf.map_comp, Gf.map_comp]
  infer_instance

/-- If the morphism between the systems in `D(A)` associated to a morphism in `D(ℕ, A)` is an
isomorphism of pro-objects, then for every `K ∈ D(A)` the corresponding map between the derived
limits of the pointwise derived tensor products is an isomorphism. -/
@[stacks 091L]
public theorem derivedLimit_tensor_map_isIso_of_proIsomorphism
    (A : Type u) [CommRing A]
    {E D : DerivedCategory
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)))} (f : E ⟶ D)
    (hf : IsIso (colim.map (Functor.whiskerRight
      (NatTrans.op ((derivedEvaluationFunctor A).map f)) coyoneda)))
    (K : CochainComplex.DerivedTensor.DObj A) :
    let AR : ℕᵒᵖ ⥤ CommRingCat.{u} := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
    let R : ℕᵒᵖ ⥤ RingCat.{u} := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
    let C := PresheafOfModules.{u} R
    let DA := CochainComplex.DerivedTensor.DObj A
    let DN := DerivedCategory C
    let S := ModuleSystemKFlatComparison.derivedTensorProduct AR
    let L : C ⥤ ModuleCat.{u} (limit R : RingCat.{u}) := ModuleInverseLimit.inverseLimit R
    ∃ (ρ : (limit R : RingCat.{u}) ≅ RingCat.of A),
      letI : (ModuleCat.restrictScalars.{u} ρ.inv.hom).IsEquivalence :=
        ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
          ρ.symm.ringCatIsoToRingEquiv
      let U : DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})) ⥤ DA :=
        (ModuleCat.restrictScalars.{u} ρ.inv.hom).mapDerivedCategory
      ∃ (hL : L.Additive),
      letI := hL
      ∃ (Δ : DA ⥤ DN)
        (_ : ModuleRightDerivedLimit.derivedModuleDiagram R (Δ.obj K) ⋙ U ≅
          (Functor.const ℕᵒᵖ).obj K)
        (Rlim : DN ⥤ DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})))
        (α : L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ Rlim),
      Rlim.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
        IsIso ((S.tensor.obj (Δ.obj K) ⋙ Rlim ⋙ U).map f) :=
  tensor_rLim_map_isIso A f hf K

end
end Construction

end ModuleSystemRlimProTensor
