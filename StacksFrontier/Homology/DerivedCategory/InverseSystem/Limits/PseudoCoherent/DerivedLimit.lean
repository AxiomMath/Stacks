module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent.DerivedTransitionLift

/-!
# Pseudo-coherence of a derived inverse limit

A tower of finite free representatives, its limit over the limit ring, and the proof of 0CQF.

## Main results

* `StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso`
  ([stacks 0CQF]): pseudo-coherence of a derived inverse limit together with invertibility of all
  its canonical derived base-change maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace StacksDraft.DerivedInverseLimit

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

private lemma derivedBaseChangeComparison_comp
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {K L : DerivedCategory (ModuleCat.{max u v} R)}
    {M : DerivedCategory (ModuleCat.{max u v} S)} (a : K ⟶ L)
    (g : L ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj M) :
    derivedBaseChangeComparison f (a ≫ g) =
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
        f).functor.map a ≫
        derivedBaseChangeComparison f g := by
  dsimp only [derivedBaseChangeComparison]
  exact Adjunction.homEquiv_naturality_left_symm _ a g

attribute [local instance] extendScalarsGeneral_additive

private structure FiniteFreeRepresentative
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) where
  complex : CochainComplex (ModuleCat.{v} R) ℤ
  bounded : complex.IsStrictlyLE b
  finiteFree : ∀ i, Module.Finite R (complex.X i) ∧ Module.Free R (complex.X i)
  iso : DerivedCategory.Q.obj complex ≅ K

private lemma exists_finiteFree_tower
    (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
    (hf : ∀ n, Function.Surjective (f n))
    (hI : ∀ n, (RingHom.ker (f n)).IsLocallyNilpotent)
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (R n)))
    (hK : ∀ n, PseudoCoherence.IsPseudoCoherent (K n))
    (φ : ∀ n, K (n + 1) ⟶ (ModuleCat.restrictScalars (f n)).mapDerivedCategory.obj (K n))
    (hφ : ∀ n, IsIso (derivedBaseChangeComparison (f n) (φ n))) :
    ∃ (P : ∀ n, CochainComplex (ModuleCat.{max u v} (R n)) ℤ) (b : ℤ),
      (∀ n, (P n).IsStrictlyLE b) ∧
      (∀ n i, Module.Finite (R n) ((P n).X i) ∧ Module.Free (R n) ((P n).X i)) ∧
      ∃ e : ∀ n, DerivedCategory.Q.obj (P n) ≅ K n,
      ∃ g : ∀ n, P (n + 1) ⟶
          ((ModuleCat.restrictScalars (f n)).mapHomologicalComplex (.up ℤ)).obj (P n),
        (∀ n, IsIso (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
          (f n))
          (.up ℤ)).homEquiv _ _).symm (g n))) ∧
        ∀ n, DerivedCategory.Q.map (g n) ≫
          (ModuleCat.restrictScalars (f n)).mapDerivedCategoryFactors.inv.app (P n) ≫
            (ModuleCat.restrictScalars (f n)).mapDerivedCategory.map (e n).hom =
              (e (n + 1)).hom ≫ φ n := by
  obtain ⟨P₀, ⟨⟨b, hb⟩, hP₀⟩, ⟨e₀⟩⟩ := hK 0
  let s₀ : FiniteFreeRepresentative (K 0) b := ⟨P₀, hb, hP₀, e₀⟩
  have hs (n : ℕ) (s : FiniteFreeRepresentative (K n) b) :
      ∃ t : FiniteFreeRepresentative (K (n + 1)) b,
      ∃ g : t.complex ⟶
          ((ModuleCat.restrictScalars (f n)).mapHomologicalComplex (.up ℤ)).obj s.complex,
        IsIso (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v} (f
          n))
          (.up ℤ)).homEquiv _ _).symm g) ∧
        DerivedCategory.Q.map g ≫
          (ModuleCat.restrictScalars (f n)).mapDerivedCategoryFactors.inv.app s.complex ≫
            (ModuleCat.restrictScalars (f n)).mapDerivedCategory.map s.iso.hom =
              t.iso.hom ≫ φ n := by
    have := s.bounded
    obtain ⟨P, hbP, hP, eP, g, hg, he⟩ :=
      exists_finiteFree_lift_of_derived_transition (f n) (hf n) (hI n)
        (K (n + 1)) (hK (n + 1)) (K n) (φ n) (hφ n)
        s.complex b s.finiteFree s.iso
    exact ⟨⟨P, hbP, hP, eP⟩, g, hg, he⟩
  let s : ∀ n, FiniteFreeRepresentative (K n) b := Nat.rec s₀ (fun n s => (hs n s).choose)
  refine ⟨fun n => (s n).complex, b, fun n => (s n).bounded,
    fun n => (s n).finiteFree, fun n => (s n).iso,
    fun n => (hs n (s n)).choose_spec.choose,
    fun n => (hs n (s n)).choose_spec.choose_spec.1,
    fun n => (hs n (s n)).choose_spec.choose_spec.2⟩

/-- Restriction of scalars along a composite `h = g ∘ f`, read on cochain complexes: the
comparison of `mapHomologicalComplex` with the composite of the two restrictions. -/
abbrev restrictScalarsComplexComp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (w : h = g.comp f) :=
  Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp'.{max u v} f g h w).symm (.up ℤ)

/-- On the derived category, the composite-restriction comparison `derivedRestrictScalarsComp`
is induced by its cochain-level counterpart `restrictScalarsComplexComp`. -/
lemma derivedRestrictScalarsComp_factors
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (w : h = g.comp f)
    (E : CochainComplex (ModuleCat.{max u v} T) ℤ) :
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj E) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars g).mapDerivedCategoryFactors.inv.app E) ≫
          (derivedRestrictScalarsComp f g h w).hom.app (DerivedCategory.Q.obj E) =
      DerivedCategory.Q.map ((restrictScalarsComplexComp f g h w).hom.app E) ≫
        (ModuleCat.restrictScalars h).mapDerivedCategoryFactors.inv.app E := by
  simp [derivedRestrictScalarsComp, restrictScalarsComplexComp,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]

/-- A limit of cochain complexes concentrated in degrees `≤ b` is concentrated in degrees
`≤ b`. -/
lemma isStrictlyLE_limit
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasLimits C]
    {J : Type} [SmallCategory J]
    (F : J ⥤ CochainComplex C ℤ) (b : ℤ)
    (hF : ∀ j, (F.obj j).IsStrictlyLE b) : (limit F).IsStrictlyLE b := by
  refine (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi => ?_
  let G := HomologicalComplex.eval C (.up ℤ) i
  exact (isLimitOfPreserves G (limit.isLimit F)).isZero_pt
    ((F ⋙ G).isZero fun j => CochainComplex.isZero_of_isStrictlyLE (F.obj j) b i hi)

private lemma exists_linearEquiv_pi_of_successor_coordinates
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (ι : Type v) (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} c.pt)
    (d : Cone M) (hd : IsLimit d)
    (e : ∀ n : ℕ, (ModuleCat.restrictScalars.{max u v} (c.π.app (op n)).hom).obj
      (ModuleCat.of (A.obj (op n)) (ι → A.obj (op n))) ≅ M.obj (op n))
    (he : ∀ n (x : M.obj (op (n + 1))) (i : ι),
      (e n).inv (M.map (homOfLE (Nat.le_succ n)).op x) i =
        (A.map (homOfLE (Nat.le_succ n)).op).hom ((e (n + 1)).inv x i)) :
    ∃ E : d.pt ≃ₗ[c.pt] (ι → c.pt),
      ∀ (x : d.pt) (n : ℕ) (i : ι),
        (c.π.app (op n)).hom (E x i) = (e n).inv (d.π.app (op n) x) i := by
  have hw (m n : ℕ) (hmn : m ≤ n) (x : M.obj (op n)) (i : ι) :
      (e m).inv (M.map (homOfLE hmn).op x) i =
        (A.map (homOfLE hmn).op).hom ((e n).inv x i) := by
    induction hmn with
    | refl => simp
    | @step n h ih =>
      rw [show (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op from Subsingleton.elim _ _,
        M.map_comp, A.map_comp]
      show (e m).inv (M.map (homOfLE h).op
        (M.map (homOfLE (Nat.le_succ n)).op x)) i =
        (A.map (homOfLE h).op).hom
          ((A.map (homOfLE (Nat.le_succ n)).op).hom ((e (n + 1)).inv x i))
      rw [ih, he]
  obtain ⟨E, hE⟩ := exists_linearEquiv_pi_of_compatible_coordinates A c hc ι M d hd
    (fun j => e j.unop) (fun {j k} f x i => hw k.unop j.unop (leOfHom f.unop) x i)
  exact ⟨E, fun x n i => hE x (op n) i⟩

private abbrev restrictScalarsTower
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (.up ℤ)).obj (P n)) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} c.pt) ℤ :=
  Functor.ofOpSequence (fun n =>
    ((ModuleCat.restrictScalars (c.π.app (op (n + 1))).hom).mapHomologicalComplex (.up ℤ)).map
      (g n) ≫ (restrictScalarsComplexComp (c.π.app (op (n + 1))).hom
        (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
        (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (P n))

set_option backward.isDefEq.respectTransparency false in
private lemma finiteFree_limit_and_baseChange
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (hf : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hI : ∀ n : ℕ, (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A.obj (op n))) ℤ)
    (b : ℤ) (hb : ∀ n, (P n).IsStrictlyLE b)
    (hP : ∀ n i, Module.Finite (A.obj (op n)) ((P n).X i) ∧
      Module.Free (A.obj (op n)) ((P n).X i))
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (hg : ∀ n, IsIso (((mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v}
        (A.map (homOfLE (Nat.le_succ n)).op).hom) (.up ℤ)).homEquiv _ _).symm (g n))) :
    let M := restrictScalarsTower A c P g
    PseudoCoherence.IsBoundedAboveFiniteFree (limit M) ∧
      (∀ n, IsIso (((mapHomologicalComplexAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{max u v} (c.π.app (op n)).hom) (.up ℤ)).homEquiv
          _ _).symm (limit.π M (op n)))) ∧
      ∀ n i, Function.Surjective ((M.map (homOfLE (Nat.le_succ n)).op).f i) := by
  intro M
  have hbM : (limit M).IsStrictlyLE b := isStrictlyLE_limit M b (fun n => by
    have := hb n.unop
    show CochainComplex.IsStrictlyLE
      (((ModuleCat.restrictScalars (c.π.app n).hom).mapHomologicalComplex (.up ℤ)).obj
        (P n.unop)) b
    infer_instance)
  have hterms (i : ℤ) :
      Module.Finite c.pt ((limit M).X i) ∧ Module.Free c.pt ((limit M).X i) ∧
        ∀ n, IsIso (((ModuleCat.extendRestrictScalarsAdj.{max u v}
          (c.π.app (op n)).hom).homEquiv _ _).symm ((limit.π M (op n)).f i)) := by
    have hfin (n : ℕ) := (hP n i).1
    have hfree (n : ℕ) := (hP n i).2
    have hproj (n : ℕ) : Module.Projective (A.obj (op n)) ((P n).X i) := inferInstance
    let ι := Module.Free.ChooseBasisIndex (A.obj (op 0)) ((P 0).X i)
    let e₀ : (P 0).X i ≅ ModuleCat.of (A.obj (op 0)) (ι → A.obj (op 0)) :=
      (Module.Free.chooseBasis (A.obj (op 0)) ((P 0).X i)).equivFun.toModuleIso
    have hg' (n : ℕ) : IsIso (((ModuleCat.extendRestrictScalarsAdj.{max u v}
        (A.map (homOfLE (Nat.le_succ n)).op).hom).homEquiv _ _).symm ((g n).f i)) := by
      have := hg n
      exact inferInstanceAs (IsIso ((((mapHomologicalComplexAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{max u v}
          (A.map (homOfLE (Nat.le_succ n)).op).hom) (.up ℤ)).homEquiv _ _).symm (g n)).f i))
    obtain ⟨e, he₀, he⟩ := exists_compatible_coordinates
      (fun n => A.obj (op n)) (fun n => (A.map (homOfLE (Nat.le_succ n)).op).hom)
      hf (fun n x hx => (hI n x hx).isUnit_one_add)
      (fun n => (P n).X i) (fun n => (g n).f i) hg' ι e₀
    let F := HomologicalComplex.eval (ModuleCat.{max u v} c.pt) (.up ℤ) i
    obtain ⟨E, hE⟩ := exists_linearEquiv_pi_of_successor_coordinates A c hc ι
      (M ⋙ F) (F.mapCone (limit.cone M)) (isLimitOfPreserves F (limit.isLimit M))
      (fun n => (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapIso (e n).symm)
      (fun n x j => by
        show (e n).hom ((M.map (homOfLE (Nat.le_succ n)).op).f i x) j = _
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        exact (he n x j).symm)
    refine ⟨Module.Finite.equiv E.symm, Module.Free.of_equiv E.symm, fun n => ?_⟩
    exact isIso_baseChange_of_coordinates (c.π.app (op n)).hom
      ((limit M).X i) ((P n).X i) ι E.toModuleIso (e n) ((limit.π M (op n)).f i)
      (fun x j => (hE x n j).symm)
  refine ⟨⟨⟨b, hbM⟩, fun i => ⟨(hterms i).1, (hterms i).2.1⟩⟩, ?_, ?_⟩
  · intro n
    let a := ((mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (c.π.app (op n)).hom) (.up ℤ)).homEquiv
        _ _).symm (limit.π M (op n))
    have hi : ∀ i : ℤ, IsIso (a.f i) := fun i => (hterms i).2.2 n
    exact HomologicalComplex.Hom.isIso_of_components a
  · intro n i
    have := hg n
    let a := ((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
      (A.map (homOfLE (Nat.le_succ n)).op).hom) (.up ℤ)).homEquiv _ _).symm (g n)
    have ha : Function.Surjective (a.f i) := (ModuleCat.epi_iff_surjective _).mp inferInstance
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    show Function.Surjective ((g n).f i)
    have hu : Function.Surjective ((ModuleCat.extendRestrictScalarsAdj.{max u v}
        (A.map (homOfLE (Nat.le_succ n)).op).hom).unit.app ((P (n + 1)).X i)) := by
      let := (A.map (homOfLE (Nat.le_succ n)).op).hom.toAlgebra
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul s x =>
        obtain ⟨r, rfl⟩ := hf n s
        refine ⟨r • x, ?_⟩
        show (1 : A.obj (op n)) ⊗ₜ[A.obj (op (n + 1))] (r • x) = _
        rw [TensorProduct.tmul_smul]
        show (((A.map (homOfLE (Nat.le_succ n)).op).hom r * 1) ⊗ₜ[A.obj (op (n + 1))] x) = _
        rw [mul_one]
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
    have he := congrArg (fun k => k.f i)
      (((mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v}
        (A.map (homOfLE (Nat.le_succ n)).op).hom) (.up ℤ)).homEquiv _ _).apply_symm_apply (g n))
    rw [← he]
    exact ha.comp hu

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of a cochain-level transition map with restriction of scalars along a composite
`h = g ∘ f`: restricting `a` along `f` and comparing the two successive restrictions agrees with
the restriction along `f` of the derived map `φ` that `a` presents. -/
public lemma restrictScalars_transition_compatibility
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (w : h = g.comp f)
    (P : CochainComplex (ModuleCat.{max u v} S) ℤ)
    (E : CochainComplex (ModuleCat.{max u v} T) ℤ)
    (a : P ⟶ ((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj E)
    {K : DerivedCategory (ModuleCat.{max u v} S)}
    {L : DerivedCategory (ModuleCat.{max u v} T)}
    (eP : DerivedCategory.Q.obj P ≅ K) (eE : DerivedCategory.Q.obj E ≅ L)
    (φ : K ⟶ (ModuleCat.restrictScalars g).mapDerivedCategory.obj L)
    (ha : DerivedCategory.Q.map a ≫ (ModuleCat.restrictScalars g).mapDerivedCategoryFactors.inv.app
      E ≫
      (ModuleCat.restrictScalars g).mapDerivedCategory.map eE.hom = eP.hom ≫ φ) :
    DerivedCategory.Q.map
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map a ≫
          (restrictScalarsComplexComp f g h w).hom.app E) ≫
      (ModuleCat.restrictScalars h).mapDerivedCategoryFactors.inv.app E ≫
        (ModuleCat.restrictScalars h).mapDerivedCategory.map eE.hom =
    ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app P ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map eP.hom) ≫
        (ModuleCat.restrictScalars f).mapDerivedCategory.map φ ≫
          (derivedRestrictScalarsComp f g h w).hom.app L := by
  let F := ModuleCat.restrictScalars.{max u v} f
  let G := ModuleCat.restrictScalars.{max u v} g
  let H := ModuleCat.restrictScalars.{max u v} h
  rw [Functor.map_comp, Category.assoc, ← Category.assoc
    (DerivedCategory.Q.map ((restrictScalarsComplexComp f g h w).hom.app E)),
    ← derivedRestrictScalarsComp_factors f g h w E]
  simp only [Category.assoc]
  rw [← NatTrans.naturality (derivedRestrictScalarsComp f g h w).hom eE.hom]
  have hn := F.mapDerivedCategoryFactors.inv.naturality a
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
    F.mapDerivedCategoryFactors.inv.app _ = F.mapDerivedCategoryFactors.inv.app P ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map a) at hn
  rw [← Category.assoc (DerivedCategory.Q.map _), hn]
  simp only [Category.assoc]
  simp only [Functor.comp_map]
  rw [← F.mapDerivedCategory.map_comp_assoc
    (G.mapDerivedCategoryFactors.inv.app E) (G.mapDerivedCategory.map eE.hom)]
  rw [← F.mapDerivedCategory.map_comp_assoc (DerivedCategory.Q.map a)
    (G.mapDerivedCategoryFactors.inv.app E ≫ G.mapDerivedCategory.map eE.hom), ha,
    F.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `exists_distTriang_of_degreewise_surjective` transported along a degreewise isomorphism of
the tower with a tower in the derived category. -/
lemma exists_distTriang_of_degreewise_surjective_of_iso
    {R : Type u} [Ring R] (M : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hg : ∀ n i, Function.Surjective ((M.map (homOfLE (Nat.le_succ n)).op).f i))
    (X : ℕ → DerivedCategory (ModuleCat.{max u v} R)) [HasProduct X]
    (t : ∀ n, X (n + 1) ⟶ X n)
    (e : ∀ n, DerivedCategory.Q.obj (M.obj (op n)) ≅ X n)
    (he : ∀ n, DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op) ≫ (e n).hom =
      (e (n + 1)).hom ≫ t n) :
    ∃ δ : ∏ᶜ X ⟶ (DerivedCategory.Q.obj (limit M))⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk
        (Pi.lift fun n ↦ DerivedCategory.Q.map (limit.π M (op n)) ≫ (e n).hom)
        (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} R)) := by
  let Y := fun n : ℕ => DerivedCategory.Q.obj (M.obj (op n))
  have : HasProduct Y := hasProduct_of_equiv_of_iso X Y (Equiv.refl _) e
  obtain ⟨δ, hδ⟩ := exists_distTriang_of_degreewise_surjective M hg
  let E : ∏ᶜ Y ≅ ∏ᶜ X :=
    { hom := Pi.lift fun n => Pi.π Y n ≫ (e n).hom
      inv := Pi.lift fun n => Pi.π X n ≫ (e n).inv
      hom_inv_id := by ext n; simp
      inv_hom_id := by ext n; simp }
  have hE (n : ℕ) : E.hom ≫ Pi.π X n = Pi.π Y n ≫ (e n).hom := Pi.lift_π _ _
  have hEi (n : ℕ) : E.inv ≫ Pi.π Y n = Pi.π X n ≫ (e n).inv := Pi.lift_π _ _
  refine ⟨E.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) E.symm E.symm ?_ ?_ ?_
  · show (Pi.lift fun n => DerivedCategory.Q.map (limit.π M (op n)) ≫ (e n).hom) ≫ E.inv =
      𝟙 _ ≫ (Pi.lift fun n => DerivedCategory.Q.map (limit.π M (op n)))
    apply Pi.hom_ext
    intro n
    simp only [Category.id_comp, Category.assoc, hEi, Pi.lift_π_assoc]
    simp only [Iso.hom_inv_id, Category.comp_id]
    exact (Pi.lift_π (fun n : ℕ => DerivedCategory.Q.map (limit.π M (op n))) n).symm
  · show (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ E.inv =
      E.inv ≫ (Pi.lift fun n => Pi.π Y n - Pi.π Y (n + 1) ≫
        DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op))
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, hE]
    have hd := Pi.lift_π (fun k : ℕ => Pi.π Y k - Pi.π Y (k + 1) ≫
      DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ k)).op)) n
    have hd' := congrArg (fun k => k ≫ (e n).hom) hd
    rw [Category.assoc] at hd'
    rw [hd', Preadditive.sub_comp]
    simp only [Category.assoc, he]
    rw [← Category.assoc E.hom, hE, Category.assoc]
  · simp

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_derivedBaseChangeComparison_of_complex_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (hP : PseudoCoherence.IsBoundedAboveFiniteFree P)
    (E : CochainComplex (ModuleCat.{max u v} S) ℤ)
    (g : P ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E)
    (hg : IsIso (((mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up ℤ)).homEquiv _ _).symm g))
    {L : DerivedCategory (ModuleCat.{max u v} S)} (e : DerivedCategory.Q.obj E ≅ L) :
    IsIso (derivedBaseChangeComparison f (DerivedCategory.Q.map g ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E ≫
        (ModuleCat.restrictScalars f).mapDerivedCategory.map e.hom)) := by
  have := isKProjective_of_boundedAboveFiniteFree P hP
  have := isKProjective_extendScalars_of_boundedAboveFiniteFree f P hP
  let adj := mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up
    ℤ)
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u} f
  let adjD := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    R S _ _ f _ _ D.functor D.comparison D.isLeftDerived
  let a := (adj.homEquiv _ _).symm g
  have hi : IsIso ((adjD.homEquiv _ _).symm (DerivedCategory.Q.map g ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app E)) := by
    have h := (isIso_derived_transpose_iff (ModuleCat.extendRestrictScalarsAdj.{max u v} f)
      adjD P E a).mpr (inferInstanceAs (QuasiIso a))
    change IsIso ((adjD.homEquiv _ _).symm (DerivedCategory.Q.map (adj.homEquiv _ _ a) ≫ _)) at h
    rwa [show (adj.homEquiv _ _) a = g from (adj.homEquiv _ _).apply_symm_apply g] at h
  show IsIso ((adjD.homEquiv _ _).symm _)
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
  infer_instance

/-- **Stacks 0CQF.** Suppose a tower of rings has surjective transition maps with locally
nilpotent kernels, and its derived module objects are preserved by the base-change maps induced
by their transitions. If all terms are pseudo-coherent, or one term is pseudo-coherent and all
subsequent kernels are nilpotent, then every derived inverse limit is pseudo-coherent and its
canonical base-change map to each term is an isomorphism.

The limit ring is the vertex of the arbitrary limit cone `c`. The distinguished triangle has
the prescribed product difference map for the transitions restricted to that vertex. -/
@[stacks 0CQF]
public theorem derivedLimit_isPseudoCoherent_and_baseChange_iso
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A.obj (op n))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj
        (Kₙ n))
    (hSurjective : ∀ n : ℕ,
      Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hLocallyNilpotent : ∀ n : ℕ,
      (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (hPseudoCoherent : (∀ n : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n)) ∨
      ∃ n₀ : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n₀) ∧
        ∀ n : ℕ, n₀ ≤ n →
          IsNilpotent (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom))
    (hBaseChange : ∀ n : ℕ,
      IsIso (derivedBaseChangeComparison (A.map (homOfLE (Nat.le_succ n)).op).hom (φ n))) :
    let X : ℕ → DerivedCategory (ModuleCat.{max u v} c.pt) := fun n ↦
      (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategory.obj (Kₙ n)
    let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
      (ModuleCat.restrictScalars (c.π.app (op (n + 1))).hom).mapDerivedCategory.map
          (φ n) ≫
        (derivedRestrictScalarsComp (c.π.app (op (n + 1))).hom
          (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
          (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (Kₙ n)
    ∀ [HasProduct X] (K : DerivedCategory (ModuleCat.{max u v} c.pt))
      (p : K ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk p
        (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{max u v} c.pt)) →
      PseudoCoherence.IsPseudoCoherent K ∧ ∀ n : ℕ,
        IsIso (derivedBaseChangeComparison (c.π.app (op n)).hom (p ≫ Pi.π X n)) := by
  intro X t hProduct K p δ hTriangle
  have hAll : ∀ n, PseudoCoherence.IsPseudoCoherent (Kₙ n) := by
    rcases hPseudoCoherent with h | ⟨n₀, hK, hI⟩
    · exact h
    · exact isPseudoCoherent_all_of_eventually_nilpotent
        (fun n ↦ A.obj (op n))
        (fun n ↦ (A.map (homOfLE (Nat.le_succ n)).op).hom)
        Kₙ φ hSurjective hBaseChange n₀ hK hI
  suffices hModel : ∃ (L : DerivedCategory (ModuleCat.{max u v} c.pt))
      (q : L ⟶ ∏ᶜ X) (ε : ∏ᶜ X ⟶ L⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk q
          (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ε ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} c.pt)) ∧
      PseudoCoherence.IsPseudoCoherent L ∧ ∀ n : ℕ,
        IsIso (derivedBaseChangeComparison (c.π.app (op n)).hom (q ≫ Pi.π X n)) by
    obtain ⟨L, q, ε, hLTriangle, hL, hLBaseChange⟩ := hModel
    obtain ⟨e, he⟩ := exists_iso_comp_eq_of_distinguished_mk
      p q _ δ ε hTriangle hLTriangle
    refine ⟨PseudoCoherence.IsPseudoCoherent.ofIso hL e.symm, ?_⟩
    intro n
    have := hLBaseChange n
    rw [← he, Category.assoc, derivedBaseChangeComparison_comp]
    infer_instance
  obtain ⟨P, b, hb, hP, e, g, hg, he⟩ := exists_finiteFree_tower
    (fun n => A.obj (op n)) (fun n => (A.map (homOfLE (Nat.le_succ n)).op).hom)
    hSurjective hLocallyNilpotent Kₙ hAll φ hBaseChange
  let M := restrictScalarsTower A c P g
  obtain ⟨hM, hMred, hMsurj⟩ := finiteFree_limit_and_baseChange A c hc
    hSurjective hLocallyNilpotent P b hb hP g hg
  let eX (n : ℕ) : DerivedCategory.Q.obj (M.obj (op n)) ≅ X n :=
    ((ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategoryFactors.app (P n)).symm ≪≫
      (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategory.mapIso (e n)
  have heX (n : ℕ) : DerivedCategory.Q.map (M.map (homOfLE (Nat.le_succ n)).op) ≫
      (eX n).hom = (eX (n + 1)).hom ≫ t n := by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact restrictScalars_transition_compatibility (c.π.app (op (n + 1))).hom
      (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
      (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm
      (P (n + 1)) (P n) (g n) (e (n + 1)) (e n) (φ n) (he n)
  obtain ⟨ε, hε⟩ := exists_distTriang_of_degreewise_surjective_of_iso M hMsurj X t eX heX
  refine ⟨DerivedCategory.Q.obj (limit M),
    Pi.lift (fun n => DerivedCategory.Q.map (limit.π M (op n)) ≫ (eX n).hom), ε,
    hε, ⟨limit M, hM, ⟨Iso.refl _⟩⟩, ?_⟩
  intro n
  rw [Pi.lift_π]
  exact isIso_derivedBaseChangeComparison_of_complex_map (c.π.app (op n)).hom
    (limit M) hM (P n) (limit.π M (op n)) (hMred n) (e n)

end StacksDraft.DerivedInverseLimit

end
