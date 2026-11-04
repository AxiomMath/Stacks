module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProMorphisms
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLeffler
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimHom
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimTriangle
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism.DerivedLimit

/-!
# The right-derived inverse limit and pro-isomorphisms

The right-derived inverse limit on `D(Ab(N))` inverts a morphism whose evaluated systems are
pro-isomorphic (Tag 091B), and an inverse system is zero as a pro-object exactly when `lim` and
`R¹lim` vanish on it and on the countable direct sum of copies of it (Tag 091C).
-/


section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim.Pro

universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _

noncomputable local instance :
    (lim : Functor Rlim.InvSystemAb.{u} Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _
/-- A morphism of derived inverse systems induces an isomorphism between its associated systems
as pro-objects. The component equation records that the displayed natural transformation is the
one obtained by evaluating the original morphism, rather than merely an unrelated isomorphism
between the two pro-objects. -/
public def IsProIsomorphismOnDerivedEvaluationSystems
    {E D : DerivedCategory Rlim.InvSystemAb.{u}} (f : E ⟶ D) : Prop :=
  ∃ g : Rlim.derivedEvaluationSystem E ⟶ Rlim.derivedEvaluationSystem D,
    (∀ n : ℕᵒᵖ,
      g.app n = (Rlim.derivedEvaluationComparison E n).hom ≫
        ((evaluation ℕᵒᵖ Ab.{u}).obj n).mapDerivedCategory.map f ≫
          (Rlim.derivedEvaluationComparison D n).inv) ∧
    IsIso (colim.map (Functor.whiskerRight (NatTrans.op g) coyoneda))

/-- The degreewise-homology criterion used to show that a functor on the derived category of
inverse systems maps a morphism to an isomorphism. -/
public abbrev MapsHomologyProIsomorphismsToIsomorphisms
    (RF : Functor (DerivedCategory Rlim.InvSystemAb.{u}) (DerivedCategory Ab.{u})) : Prop :=
  ∀ {E D : DerivedCategory Rlim.InvSystemAb.{u}} (f : E ⟶ D),
    (∀ p : ℤ,
      let H := DerivedCategory.homologyFunctor Rlim.InvSystemAb.{u} p
      IsIso (colim.map (Functor.whiskerRight (NatTrans.op (H.map f)) coyoneda))) →
    IsIso (RF.map f)

end Rlim.Pro
end

end


section

open CategoryTheory Limits Opposite ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

universe v u

namespace Rlim.Pro

variable {C : Type u} [Category.{v} C]

public abbrev proMap {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) :=
  colim.map (Functor.whiskerRight (NatTrans.op f) coyoneda)

public abbrev proClass (A : ℕᵒᵖ ⥤ C) {X : C} {n : ℕᵒᵖ} (f : A.obj n ⟶ X) :=
  (colimit.ι (A.op ⋙ coyoneda) (op n)).app X f

public lemma proClass_surjective (A : ℕᵒᵖ ⥤ C) (X : C) (x : (colimit (A.op ⋙ coyoneda)).obj X) :
    ∃ (n : ℕᵒᵖ) (f : A.obj n ⟶ X), proClass A f = x := by
  obtain ⟨n, f, h⟩ := FunctorToTypes.jointly_surjective' (A.op ⋙ coyoneda) X x
  exact ⟨n.unop, f, h.symm⟩

public lemma proClass_eq_iff (A : ℕᵒᵖ ⥤ C) {X : C} {n m : ℕᵒᵖ}
    (f : A.obj n ⟶ X) (g : A.obj m ⟶ X) :
    proClass A f = proClass A g ↔
      ∃ (k : ℕᵒᵖ) (a : k ⟶ n) (b : k ⟶ m), A.map a ≫ f = A.map b ≫ g := by
  have h := Types.FilteredColimit.isColimit_eq_iff
    (A.op ⋙ coyoneda ⋙ (evaluation C (Type v)).obj X)
    (isColimitOfPreserves ((evaluation C (Type v)).obj X) (colimit.isColimit (A.op ⋙ coyoneda)))
    (xi := f) (xj := g)
  constructor
  · intro he
    obtain ⟨k, a, b, hk⟩ := h.mp he
    exact ⟨k.unop, a.unop, b.unop, hk⟩
  · rintro ⟨k, a, b, hk⟩
    exact h.mpr ⟨op k, a.op, b.op, hk⟩

public lemma proMap_proClass {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) {X : C} {n : ℕᵒᵖ}
    (g : B.obj n ⟶ X) : (proMap f).app X (proClass B g) = proClass A (f.app n ≫ g) := by
  show ((colimit.ι (B.op ⋙ coyoneda) (op n) ≫ proMap f).app X) g = _
  rw [colimit.ι_map]
  rfl

private lemma proClass_transition (A : ℕᵒᵖ ⥤ C) {X : C} {n m : ℕᵒᵖ}
    (a : m ⟶ n) (f : A.obj n ⟶ X) : proClass A (A.map a ≫ f) = proClass A f := by
  apply (proClass_eq_iff A _ _).mpr
  exact ⟨m, 𝟙 _, a, by simp⟩

public lemma proClass_postcomp (A : ℕᵒᵖ ⥤ C) {X Y : C} {n : ℕᵒᵖ}
    (f : A.obj n ⟶ X) (g : X ⟶ Y) :
    (colimit (A.op ⋙ coyoneda)).map g (proClass A f) = proClass A (f ≫ g) :=
  (ConcreteCategory.congr_hom ((colimit.ι (A.op ⋙ coyoneda) (op n)).naturality g) f).symm

public lemma exists_proInverse {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) [IsIso (proMap f)] (n : ℕᵒᵖ) :
    ∃ (m : ℕᵒᵖ) (a : m ⟶ n) (g : B.obj m ⟶ A.obj n),
      f.app m ≫ g = A.map a ∧ g ≫ f.app n = B.map a := by
  let ψ := inv (proMap f)
  obtain ⟨m, g, hg⟩ := proClass_surjective B _ (ψ.app _ (proClass A (𝟙 (A.obj n))))
  have h₁ : proClass A (f.app m ≫ g) = proClass A (𝟙 (A.obj n)) := by
    rw [← proMap_proClass, hg]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.inv_hom_id (proMap f)) _) _
  have h₂ : proClass B (g ≫ f.app n) = proClass B (𝟙 (B.obj n)) := by
    rw [← proClass_postcomp, hg]
    have hn := ConcreteCategory.congr_hom (ψ.naturality (f.app n)) (proClass A (𝟙 _))
    change ψ.app _ ((colimit (A.op ⋙ coyoneda)).map (f.app n) _) = _ at hn
    simp only [types_comp_apply] at hn
    refine hn.symm.trans ?_
    rw [proClass_postcomp, Category.id_comp, ← Category.comp_id (f.app n), ← proMap_proClass]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (IsIso.hom_inv_id (proMap f)) _) _
  obtain ⟨k, a, b, hk⟩ := (proClass_eq_iff A _ _).mp h₁
  obtain ⟨l, c, d, hl⟩ := (proClass_eq_iff B _ _).mp h₂
  let t := op (max k.unop l.unop)
  let s : t ⟶ k := (homOfLE (Nat.le_max_left _ _)).op
  let r : t ⟶ l := (homOfLE (Nat.le_max_right _ _)).op
  refine ⟨t, s ≫ b, B.map (s ≫ a) ≫ g, ?_, ?_⟩
  · rw [← f.naturality_assoc, Functor.map_comp, Category.assoc, hk, Category.comp_id]
    exact (A.map_comp s b).symm
  · have e : s ≫ a = r ≫ c := Subsingleton.elim _ _
    rw [e, Functor.map_comp, Category.assoc, Category.assoc, hl, Category.comp_id,
      ← Functor.map_comp]
    congr 1

public lemma isIso_proMap_of_inverse {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B)
    (hf : ∀ n, ∃ (m : ℕᵒᵖ) (a : m ⟶ n) (g : B.obj m ⟶ A.obj n),
      f.app m ≫ g = A.map a ∧ g ≫ f.app n = B.map a) : IsIso (proMap f) := by
  have (X : C) : IsIso ((proMap f).app X) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      obtain ⟨n, g, rfl⟩ := proClass_surjective B X x
      obtain ⟨m, h, rfl⟩ := proClass_surjective B X y
      rw [proMap_proClass, proMap_proClass] at hxy
      obtain ⟨k, a, b, hk⟩ := (proClass_eq_iff A _ _).mp hxy
      obtain ⟨l, c, s, -, hs⟩ := hf k
      apply (proClass_eq_iff B _ _).mpr
      refine ⟨l, c ≫ a, c ≫ b, ?_⟩
      simp only [Functor.map_comp, ← hs, Category.assoc]
      simp only [← f.naturality_assoc]
      exact congrArg (s ≫ ·) hk
    · intro x
      obtain ⟨n, g, rfl⟩ := proClass_surjective A X x
      obtain ⟨m, a, h, hh, -⟩ := hf n
      refine ⟨proClass B (h ≫ g), ?_⟩
      rw [proMap_proClass, ← Category.assoc, hh, proClass_transition]
  exact NatIso.isIso_of_isIso_app _

private lemma isIso_proMap_whiskerRight {D : Type*} [Category D] (H : C ⥤ D)
    {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) [IsIso (proMap f)] :
    IsIso (proMap (Functor.whiskerRight f H)) := by
  apply isIso_proMap_of_inverse
  intro n
  obtain ⟨m, a, g, hg, hg'⟩ := exists_proInverse f n
  exact ⟨m, a, H.map g, by simp [← hg], by simp [← hg']⟩

/-- An inverse system over `ℕᵒᵖ` whose transition maps are eventually zero has zero limit. -/
@[ega "III 4.1.7.21" "vanishing of lim Q_k"]
public lemma isZero_limit_of_proZero [Preadditive C] (G : ℕᵒᵖ ⥤ C) [HasLimit G]
    (hG : ∀ n : ℕᵒᵖ, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), G.map f = 0) :
    IsZero (limit G) := by
  rw [IsZero.iff_id_eq_zero]
  apply limit.hom_ext
  intro n
  obtain ⟨m, f, hf⟩ := hG n
  rw [← limit.w G f, hf]
  simp

/-- If the two outer maps of a five-term complex of inverse systems are pro-isomorphisms and the
middle three terms are exact at every index, then the middle system is pro-zero. -/
public lemma proZero_of_exact [Abelian C] {A B D E F : ℕᵒᵖ ⥤ C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (he : ∀ m, (ShortComplex.mk (b.app m) (c.app m)
      (by rw [← NatTrans.comp_app, hbc, NatTrans.app_zero])).Exact)
    [IsIso (proMap a)] [IsIso (proMap d)] :
    ∀ n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), D.map f = 0 := by
  intro n
  obtain ⟨m, f, s, -, hs⟩ := exists_proInverse a n
  obtain ⟨k, g, t, ht, -⟩ := exists_proInverse d m
  refine ⟨k, g ≫ f, ?_⟩
  rw [Functor.map_comp]
  apply (he m).comp_eq_zero
  · show D.map g ≫ c.app m = 0
    rw [c.naturality, ← ht, ← Category.assoc]
    have h := NatTrans.congr_app hcd k
    change c.app k ≫ d.app k = 0 at h
    rw [h, zero_comp]
  · show b.app m ≫ D.map f = 0
    rw [← b.naturality, ← hs, Category.assoc]
    have h := NatTrans.congr_app hab n
    change a.app n ≫ b.app n = 0 at h
    rw [h, comp_zero]

public lemma lim_and_cokernel_isZero_of_proZero (A : ℕᵒᵖ ⥤ Ab.{v})
    (hA : ∀ n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), A.map f = 0) :
    IsZero (limit A) ∧ IsZero (cokernel (Rlim.delta A)) := by
  let B : ℕᵒᵖ ⥤ Ab.{v} := 0
  have hB : IsZero B := isZero_zero _
  have : IsIso (proMap (0 : A ⟶ B)) := by
    apply isIso_proMap_of_inverse
    intro n
    obtain ⟨m, f, hf⟩ := hA n
    exact ⟨m, f, 0, by simpa using hf.symm, (hB.obj n).eq_of_tgt _ _⟩
  obtain ⟨l, r, _, _, _, _, hiso, _⟩ :=
    exists_map_lim_and_cokernel_delta.{v, v}
  obtain ⟨hl, hr⟩ := hiso A B (proMap (0 : A ⟶ B)) inferInstance
  have hlim : IsZero (limit B) := (limit.isLimit B).isZero_pt hB
  have hprod : IsZero (Rlim.product B) :=
    (limit.isLimit _).isZero_pt ((CategoryTheory.Functor.isZero_iff _).mpr fun _ => hB.obj _)
  have hc : IsZero (cokernel (Rlim.delta B)) :=
    hprod.of_epi (cokernel.π _)
  exact ⟨hlim.of_iso (asIso (l A B (proMap (0 : A ⟶ B)))),
    hc.of_iso (asIso (r A B (proMap (0 : A ⟶ B))))⟩

open DerivedCategory

noncomputable local instance : HasDerivedCategory Ab.{v} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{v} :=
  HasDerivedCategory.standard _

private def evaluationHomologyFunctor (p : ℤ) :
    DerivedCategory Rlim.InvSystemAb.{v} ⥤ Rlim.InvSystemAb.{v} where
  obj K := Rlim.homologySystem K p
  map f := {
    app := fun n => (homologyFunctor Ab.{v} p).map
      ((Stacks.InverseSystem.AbelianGroupDerivedLift.evD n).map f)
    naturality := fun n m a => by
      dsimp [Rlim.homologySystem, Rlim.derivedEvaluationSystem]
      rw [← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality] }
  map_id K := by ext n; simp
  map_comp f g := by ext n; simp

private abbrev evaluationComplex (n : ℕᵒᵖ) :=
  ((evaluation ℕᵒᵖ Ab.{v}).obj n).mapHomologicalComplex (ComplexShape.up ℤ)

private def complexEvaluationHomologyIso (K : CochainComplex Rlim.InvSystemAb.{v} ℤ)
    (p : ℤ) (n : ℕᵒᵖ) :
    ((evaluationComplex n).obj K).homology p ≅ (K.homology p).obj n :=
  (K.sc p).mapHomologyIso ((evaluation ℕᵒᵖ Ab.{v}).obj n)

private lemma complexEvaluationHomologyIso_naturality
    (K : CochainComplex Rlim.InvSystemAb.{v} ℤ) (p : ℤ)
    {n m : ℕᵒᵖ} (a : n ⟶ m) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ Ab.{v}).map a)
        (ComplexShape.up ℤ)).app K) p ≫ (complexEvaluationHomologyIso K p m).hom =
      (complexEvaluationHomologyIso K p n).hom ≫ (K.homology p).map a := by
  show ShortComplex.homologyMap ((K.sc p).mapNatTrans
    ((evaluation ℕᵒᵖ Ab.{v}).map a)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp [complexEvaluationHomologyIso]
  rfl

private lemma complexEvaluationHomologyIso_naturality_complex
    {K L : CochainComplex Rlim.InvSystemAb.{v} ℤ} (f : K ⟶ L) (p : ℤ) (n : ℕᵒᵖ) :
    HomologicalComplex.homologyMap ((evaluationComplex n).map f) p ≫
        (complexEvaluationHomologyIso L p n).hom =
      (complexEvaluationHomologyIso K p n).hom ≫
        (HomologicalComplex.homologyMap f p).app n :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ p).map f)
    ((evaluation ℕᵒᵖ Ab.{v}).obj n)

private def evaluationHomologyFactors (p : ℤ) :
    Q ⋙ evaluationHomologyFunctor.{v} p ≅
      HomologicalComplex.homologyFunctor Rlim.InvSystemAb.{v} (ComplexShape.up ℤ) p :=
  NatIso.ofComponents (fun K => NatIso.ofComponents (fun n =>
    (homologyFunctor Ab.{v} p).mapIso
      (((evaluation ℕᵒᵖ Ab.{v}).obj n).mapDerivedCategoryFactors.app K) ≪≫
    (homologyFunctorFactors Ab.{v} p).app ((evaluationComplex n).obj K) ≪≫
    complexEvaluationHomologyIso K p n) (by
      intro n m a
      change (homologyFunctor Ab.{v} p).map ((Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans
        a).app (Q.obj K)) ≫
        ((homologyFunctor Ab.{v} p).map
          (((evaluation ℕᵒᵖ Ab.{v}).obj m).mapDerivedCategoryFactors.hom.app K) ≫ _) = _
      rw [← Functor.map_comp_assoc, evaluationFactors_naturality, Functor.map_comp]
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      simp only [Category.assoc]
      erw [(homologyFunctorFactors Ab.{v} p).hom.naturality_assoc]
      change _ ≫ _ ≫ HomologicalComplex.homologyMap _ p ≫ _ = _
      rw [complexEvaluationHomologyIso_naturality]
      rfl)) (by
    intro K L f
    apply NatTrans.ext
    funext n
    change (homologyFunctor Ab.{v} p).map ((Stacks.InverseSystem.AbelianGroupDerivedLift.evD n).map
      (Q.map f)) ≫
      ((homologyFunctor Ab.{v} p).map
        (((evaluation ℕᵒᵖ Ab.{v}).obj n).mapDerivedCategoryFactors.hom.app L) ≫ _) = _
    rw [← Functor.map_comp_assoc, Functor.mapDerivedCategoryFactors_hom_naturality,
      Functor.map_comp]
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc]
    erw [(homologyFunctorFactors Ab.{v} p).hom.naturality_assoc]
    change _ ≫ _ ≫ HomologicalComplex.homologyMap _ p ≫ _ = _
    rw [complexEvaluationHomologyIso_naturality_complex]
    rfl)

private def evaluationHomologyIso (p : ℤ) :
    evaluationHomologyFunctor.{v} p ≅ homologyFunctor Rlim.InvSystemAb.{v} p := by
  letI : Localization.Lifting Q
      (HomologicalComplex.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ))
      (Q ⋙ evaluationHomologyFunctor.{v} p) (evaluationHomologyFunctor.{v} p) := ⟨Iso.refl _⟩
  letI : Localization.Lifting Q
      (HomologicalComplex.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor Rlim.InvSystemAb.{v} (ComplexShape.up ℤ) p)
      (homologyFunctor Rlim.InvSystemAb.{v} p) := ⟨homologyFunctorFactors _ p⟩
  exact Localization.liftNatIso Q
    (HomologicalComplex.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ))
    _ _ _ _ (evaluationHomologyFactors p)

public lemma proMap_comp {A B D : ℕᵒᵖ ⥤ C} (f : A ⟶ B) (g : B ⟶ D) :
    proMap (f ≫ g) = proMap g ≫ proMap f := by
  simp only [proMap, NatTrans.op_comp, Functor.whiskerRight_comp, Functor.map_comp]

private lemma homology_proIso {E D : DerivedCategory Rlim.InvSystemAb.{v}}
    (f : E ⟶ D) (hf : IsProIsomorphismOnDerivedEvaluationSystems f) (p : ℤ) :
    IsIso (proMap ((homologyFunctor Rlim.InvSystemAb.{v} p).map f)) := by
  obtain ⟨g, hg, hi⟩ := hf
  have := hi
  have he : (evaluationHomologyFunctor p).map f =
      Functor.whiskerRight g (homologyFunctor Ab.{v} p) := by
    apply NatTrans.ext
    funext n
    show (homologyFunctor Ab.{v} p).map ((Stacks.InverseSystem.AbelianGroupDerivedLift.evD n).map
      f) =
      (homologyFunctor Ab.{v} p).map (g.app n)
    rw [hg]
    show (homologyFunctor Ab.{v} p).map _ =
      (homologyFunctor Ab.{v} p).map (𝟙 _ ≫ _ ≫ 𝟙 _)
    simp
  have : IsIso (proMap ((evaluationHomologyFunctor p).map f)) := by
    rw [he]
    exact isIso_proMap_whiskerRight _ g
  have eq : (homologyFunctor Rlim.InvSystemAb.{v} p).map f =
      (evaluationHomologyIso p).inv.app E ≫ (evaluationHomologyFunctor p).map f ≫
        (evaluationHomologyIso p).hom.app D := by
    rw [(evaluationHomologyIso p).hom.naturality]
    simp
  rw [eq, proMap_comp, proMap_comp]
  infer_instance

private lemma proZero_of_iso {A B : ℕᵒᵖ ⥤ Ab.{v}} (e : A ≅ B)
    (hB : ∀ n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), B.map f = 0) :
    ∀ n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n), A.map f = 0 := by
  intro n
  obtain ⟨m, f, hf⟩ := hB n
  refine ⟨m, f, ?_⟩
  apply (cancel_mono (e.hom.app n)).1
  rw [e.hom.naturality, hf, comp_zero, zero_comp]

private lemma isZero_of_homology_isZero (K : DerivedCategory Ab.{v})
    (h : ∀ p, IsZero ((homologyFunctor Ab.{v} p).obj K)) : IsZero K := by
  have : IsIso (0 : K ⟶ 0) := (DerivedCategory.isIso_iff _ _).mpr fun p =>
    (h p).isIso ((homologyFunctor Ab.{v} p).map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

private lemma derivedLimit_isZero_of_proZero
    (K : DerivedCategory Rlim.InvSystemAb.{v}) (L : DerivedCategory Ab.{v})
    [HasProduct fun n : ℕ => (Rlim.derivedEvaluationSystem K).obj (op n)]
    (hL : Pretriangulated.IsDerivedLimit (Rlim.derivedEvaluationSystem K) L)
    (hK : ∀ p n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n),
      ((homologyFunctor Rlim.InvSystemAb.{v} p).obj K).map f = 0) : IsZero L := by
  have hz (p : ℤ) := lim_and_cokernel_isZero_of_proZero
    (Rlim.homologySystem K p) (proZero_of_iso ((evaluationHomologyIso p).app K) (hK p))
  obtain ⟨a, b, hT, hseq⟩ := isDerivedLimit_homology_shortExact _ L hL
  apply isZero_of_homology_isZero
  intro p
  obtain ⟨e, i, q, w, _, _, _, h⟩ := hseq p
  apply h.exact.isZero_of_both_isZero
  · have he : (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (Rlim.homologySystem K (p - 1)).obj (op n)) n -
        Pi.π (fun n : ℕ => (Rlim.homologySystem K (p - 1)).obj (op n)) (n + 1) ≫
          (Rlim.homologySystem K (p - 1)).map (homOfLE (Nat.le_succ n)).op) =
        Rlim.delta (Rlim.homologySystem K (p - 1)) := by
      unfold Rlim.delta Rlim.shift
      apply Pi.hom_ext
      intro n
      rw [Pi.lift_π, Preadditive.sub_comp, Category.id_comp, Pi.lift_π]
    show IsZero (cokernel _)
    rw [he]
    exact (hz (p - 1)).2
  · exact (hz p).1

noncomputable local instance :
    (lim : Functor Rlim.InvSystemAb.{v} Ab.{v}).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem lim_hasRightDerivedFunctor_and_maps_homologyProIsomorphisms :
    let F : Functor Rlim.InvSystemAb.{v} Ab.{v} := lim
    ∃ (RF : Functor (DerivedCategory Rlim.InvSystemAb.{v}) (DerivedCategory Ab.{v}))
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ)) ∧
        MapsHomologyProIsomorphismsToIsomorphisms RF := by
  obtain ⟨RF, α, hRF, _, _, _, _, _, _, _, _, _, cs, hcs, htri, _⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{v}
  let : RF.CommShift ℤ := cs
  have : RF.IsTriangulated := htri
  have := hRF
  obtain ⟨RG, β, hRG, hG⟩ := Rlim.lim_hasRightDerivedFunctor_and_isDerivedLimit.{v}
  have := hRG
  let e := Functor.rightDerivedUnique RF RG α β
    (HomotopyCategory.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ))
  have kills (K : DerivedCategory Rlim.InvSystemAb.{v})
      (hK : ∀ p n, ∃ (m : ℕᵒᵖ) (f : m ⟶ n),
        ((homologyFunctor Rlim.InvSystemAb.{v} p).obj K).map f = 0) :
      IsZero (RF.obj K) := by
    obtain ⟨hprod, hL⟩ := hG K
    have := hprod
    exact (derivedLimit_isZero_of_proZero K (RG.obj K) hL hK).of_iso (e.app K)
  refine ⟨RF, α, hRF, ?_⟩
  intro E D f hf
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  let T := Pretriangulated.Triangle.mk f g h
  have hz : ∀ p n, ∃ (m : ℕᵒᵖ) (a : m ⟶ n),
      ((homologyFunctor Rlim.InvSystemAb.{v} p).obj Z).map a = 0 := by
    intro p
    have := hf p
    have := hf (p + 1)
    exact proZero_of_exact
      ((homologyFunctor Rlim.InvSystemAb.{v} p).map f)
      ((homologyFunctor Rlim.InvSystemAb.{v} p).map g)
      (HomologySequence.δ T p (p + 1))
      ((homologyFunctor Rlim.InvSystemAb.{v} (p + 1)).map f)
      (by
        have hab : f ≫ g = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
        rw [← Functor.map_comp, hab, Functor.map_zero])
      (HomologySequence.comp_δ T hT p (p + 1))
      (HomologySequence.δ_comp T hT p (p + 1))
      (fun m => (HomologySequence.exact₃ T hT p (p + 1)).map ((evaluation ℕᵒᵖ Ab.{v}).obj m))
  exact ((RF.mapTriangle.obj T).distinguished_iff_of_isZero₃ (kills Z hz)).mp
    (RF.map_distinguished T hT)

/-- **Stacks 091B.** The right-derived inverse-limit functor sends a morphism of derived inverse
systems to an isomorphism if the induced morphism between their associated systems in `D(Ab)` is
an isomorphism of pro-objects. Such a pro-isomorphism induces pro-isomorphisms between the
cohomology inverse systems in every degree; the displayed degreewise criterion then gives the
result. -/
@[stacks 091B]
public theorem lim_hasRightDerivedFunctor_and_maps_proIsomorphisms_to_isomorphisms :
    let F : Functor Rlim.InvSystemAb.{v} Ab.{v} := lim
    ∃ (RF : Functor (DerivedCategory Rlim.InvSystemAb.{v}) (DerivedCategory Ab.{v}))
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{v} (ComplexShape.up ℤ)) ∧
        MapsHomologyProIsomorphismsToIsomorphisms RF ∧
        ∀ {E D : DerivedCategory Rlim.InvSystemAb.{v}} (f : E ⟶ D),
          IsProIsomorphismOnDerivedEvaluationSystems f →
            (∀ p : ℤ,
              let H := DerivedCategory.homologyFunctor Rlim.InvSystemAb.{v} p
              IsIso (colim.map
                (Functor.whiskerRight (NatTrans.op (H.map f)) coyoneda))) ∧
            IsIso (RF.map f) := by
  obtain ⟨RF, α, hRF, hH⟩ := lim_hasRightDerivedFunctor_and_maps_homologyProIsomorphisms.{v}
  refine ⟨RF, α, hRF, hH, ?_⟩
  intro E D f hf
  have hp := homology_proIso f hf
  exact ⟨hp, hH f hp⟩

end Rlim.Pro

end

end


section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory Opposite

namespace Rlim.Pro

universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _
noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _
noncomputable local instance :
    (lim : CategoryTheory.Functor Rlim.InvSystemAb.{u} Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem eventualRange_eq_zero_of_isZero_limit (A : Rlim.InvSystemAb.{u})
    (hML : (A ⋙ forget Ab).IsMittagLeffler) (hlim : IsZero (limit A)) (n : ℕᵒᵖ) :
    (A ⋙ forget Ab).eventualRange n = {0} := by
  apply Set.Subset.antisymm
  · intro x hx
    let E := (A ⋙ forget Ab).toPreimages ({x} : Set (A.obj n))
    have hEML : E.IsMittagLeffler := hML.toPreimages _ _
    have hne : ∀ j, Nonempty (E.obj j) := by
      intro j
      rw [show E.obj j = ⋂ f : j ⟶ n, (A ⋙ forget Ab).map f ⁻¹' {x} by rfl]
      simp only [Set.nonempty_coe_sort, Set.nonempty_iInter, Set.mem_preimage,
        Set.mem_singleton_iff]
      obtain h | h := isEmpty_or_nonempty (j ⟶ n)
      · exact ⟨0, fun f ↦ isEmptyElim f⟩
      · let f : j ⟶ n := Classical.choice h
        obtain ⟨y, hy⟩ := (A ⋙ forget Ab).mem_eventualRange_iff.mp hx f
        exact ⟨y, fun g ↦ by simpa [Subsingleton.elim g f] using hy⟩
    obtain ⟨s⟩ := nonempty_sections_of_isMittagLeffler hEML hne
    let t : (A ⋙ forget Ab).sections :=
      ⟨fun j ↦ (s.val j).1, fun f ↦ congrArg Subtype.val (s.property f)⟩
    have ht : t.val n = x := by
      have hs := Set.mem_iInter.mp (s.val n).2 (𝟙 n)
      simpa [t] using hs
    let y : ToType (limit A) := (Types.isLimitEquivSections
      (isLimitOfPreserves (forget Ab) (limit.isLimit A))).symm t
    have hy : limit.π A n y = x := by
      rw [← ht]
      simpa [y, t] using Types.isLimitEquivSections_symm_apply
        (isLimitOfPreserves (forget Ab) (limit.isLimit A)) t n
    rw [← hy, Set.mem_singleton_iff]
    exact ConcreteCategory.congr_hom (hlim.eq_of_src (limit.π A n) 0) y
  · rintro _ rfl
    exact (A ⋙ forget Ab).mem_eventualRange_iff.2 fun {_} f ↦
      ⟨0, map_zero (A.map f).hom⟩

private theorem isProZero_of_isMittagLeffler_of_isZero_limit
    (A : Rlim.InvSystemAb.{u}) (hML : (A ⋙ forget Ab).IsMittagLeffler)
    (hlim : IsZero (limit A)) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), A.map (homOfLE h).op = 0 := by
  intro n
  obtain ⟨⟨m⟩, f, hf⟩ :=
    (A ⋙ forget Ab).isMittagLeffler_iff_eventualRange.mp hML (op n)
  have hnm : n ≤ m := leOfHom f.unop
  refine ⟨m, hnm, ?_⟩
  apply ConcreteCategory.hom_ext
  intro x
  have hx : (A.map f : A.obj (op m) → A.obj (op n)) x ∈
      (A ⋙ forget Ab).eventualRange (op n) := by
    rw [hf]
    exact ⟨x, rfl⟩
  have hz := Set.ext_iff.mp (eventualRange_eq_zero_of_isZero_limit A hML hlim (op n))
    (A.map f x)
  have : A.map f x = 0 := Set.mem_singleton_iff.mp (hz.mp hx)
  simpa [Subsingleton.elim f (homOfLE hnm).op] using this

private theorem isMittagLeffler_of_isProZero (A : Rlim.InvSystemAb.{u})
    (hA : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), A.map (homOfLE h).op = 0) :
    (A ⋙ forget Ab).IsMittagLeffler := by
  intro ⟨n⟩
  obtain ⟨m, hnm, hz⟩ := hA n
  refine ⟨op m, (homOfLE hnm).op, fun k g x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hx
  show A.map (homOfLE hnm).op y ∈ Set.range (A.map g)
  rw [hz]
  exact ⟨0, map_zero _⟩

@[ega "III 4.1.7.21" "Vanishing of lim_k Q_k"]
private theorem isZero_limit_of_isProZero (A : Rlim.InvSystemAb.{u})
    (hA : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), A.map (homOfLE h).op = 0) :
    IsZero (limit A) := by
  refine isZero_limit_of_proZero A fun ⟨n⟩ => ?_
  obtain ⟨m, hnm, hz⟩ := hA n
  exact ⟨op m, (homOfLE hnm).op, hz⟩

private theorem countable_coproduct_isProZero (A : Rlim.InvSystemAb.{u})
    (hA : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), A.map (homOfLE h).op = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (∐ fun _ : Discrete ℕ ↦ A).map (homOfLE h).op = 0 := by
  intro n
  obtain ⟨m, hnm, hz⟩ := hA n
  refine ⟨m, hnm, ?_⟩
  apply colimit_obj_ext
  intro i
  simpa [hz] using
    ((Sigma.ι (fun _ : Discrete ℕ ↦ A) i.as).naturality (homOfLE hnm).op).symm


/-- **Stacks 091C.** An inverse system of abelian groups is zero as a pro-object if and only if
its inverse limit and first derived inverse limit vanish, and the same two vanishings hold for
the countable direct sum of copies of the system. -/
@[stacks 091C]
public theorem isProZero_iff_isZero_lim_and_rightDerivedLim_one_and_countable_coproduct
    (A : Rlim.InvSystemAb.{u}) :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    ∀ (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)) →
        ((∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), A.map (homOfLE h).op = 0) ↔
          IsZero (limit A) ∧
          IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
            (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) ∧
          IsZero (limit (∐ fun _ : Discrete ℕ => A)) ∧
          IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
            (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj
              (∐ fun _ : Discrete ℕ => A))))) := by
  dsimp
  intro RF α hRF
  constructor
  · intro hA
    have hML := isMittagLeffler_of_isProZero A hA
    have hR := (Rlim.isMittagLeffler_iff_isZero_rightDerivedLim_one_and_countable_coproduct
      A RF α hRF).mp hML
    exact ⟨isZero_limit_of_isProZero A hA, hR.1,
      isZero_limit_of_isProZero _ (countable_coproduct_isProZero A hA), hR.2⟩
  · rintro ⟨hlim, hR1, -, hR1sum⟩
    exact isProZero_of_isMittagLeffler_of_isZero_limit A
      ((Rlim.isMittagLeffler_iff_isZero_rightDerivedLim_one_and_countable_coproduct
        A RF α hRF).mpr ⟨hR1, hR1sum⟩) hlim

end Rlim.Pro

end

end
