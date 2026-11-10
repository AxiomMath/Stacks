module

public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksFrontier.Algebra.Homology.InverseLimit
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingComparisonReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CandidateKInjectiveQuasiIso

/-!
# The alternating Čech comparison, by passage to the limit over the truncations

Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be a *finite* open covering of `X` and
let `F^•` be an arbitrary complex of `O_X`-modules. Suppose that the cohomology sheaves of
`F^•` have no higher cohomology on the members of a basis `B` of the topology of `X` -- this is
condition (1) together with condition (3)(c) of Tag 08C2. Let `F^• ⟶ lim_n I_n` be a candidate
K-injective resolution of `F^•` in the sense of Tag 071A, and suppose that the total
alternating Čech complex of each of its stage maps `τ_{≥ -n} F^• ⟶ I_n` is a
quasi-isomorphism. Then the comparison map

`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)`

of Tag 08C1 is an isomorphism.

## Main results

* `Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_stages`: the comparison map of
  Tag 08C1 is invertible at `F^•`.

## References

* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 071A](https://stacks.math.columbia.edu/tag/071A)
* [Stacks Project, Tag 071B](https://stacks.math.columbia.edu/tag/071B)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070E](https://stacks.math.columbia.edu/tag/070E)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Taking sections of sheaves of modules over an open subset of a topological space is an
additive functor. -/
theorem evaluation_additive {Y : TopCat.{u}}
    (S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (W : Opens Y) :
    (SheafOfModules.evaluation S (op W)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

attribute [local instance] evaluation_additive

/-! ### Towers which are eventually constant -/

private lemma isEssentiallyConstantPro_of_eventually_isIso
    {A : Type*} [Category A] {D : ℕᵒᵖ ⥤ A} (c : Cone D) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso (c.π.app (op n))) :
    EssentiallyConstantPro.IsEssentiallyConstantPro D := by
  have := h N le_rfl
  refine ⟨c, op N, inv (c.π.app (op N)), ⟨by simp, fun j ↦ ?_⟩⟩
  have := h (max N j.unop) (le_max_left _ _)
  refine ⟨op (max N j.unop), (homOfLE (le_max_left N j.unop)).op,
    (homOfLE (le_max_right N j.unop)).op, ?_⟩
  apply (cancel_epi (c.π.app (op (max N j.unop)))).mp
  simp only [← Category.assoc, c.w, IsIso.hom_inv_id, Category.id_comp]

private def isLimit_of_eventually_isIso {A : Type*} [Category A] {D : ℕᵒᵖ ⥤ A}
    (c : Cone D) (N : ℕ) (h : ∀ n : ℕ, N ≤ n → IsIso (c.π.app (op n))) : IsLimit c := by
  have := h N le_rfl
  refine { lift := fun s ↦ s.π.app (op N) ≫ inv (c.π.app (op N)), fac := ?_, uniq := ?_ }
  · intro s j
    have := h (max N j.unop) (le_max_left _ _)
    have hc : D.map (homOfLE (le_max_left N j.unop)).op ≫ inv (c.π.app (op N)) =
        inv (c.π.app (op (max N j.unop))) := by
      apply (cancel_epi (c.π.app (op (max N j.unop)))).mp
      simp
    have hv : s.π.app (op N) ≫ inv (c.π.app (op N)) =
        s.π.app (op (max N j.unop)) ≫ inv (c.π.app (op (max N j.unop))) := by
      rw [← s.w (homOfLE (le_max_left N j.unop)).op, Category.assoc, hc]
    rw [hv, ← c.w (homOfLE (le_max_right N j.unop)).op]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    exact s.w (homOfLE (le_max_right N j.unop)).op
  · intro s m hm
    apply (cancel_mono (c.π.app (op N))).mp
    simp [hm]

private lemma isIso_of_eventually_isIso_comp_cone {A : Type*} [Category A] {D : ℕᵒᵖ ⥤ A}
    (c : Cone D) (hc : IsLimit c) {Y : A} (f : Y ⟶ c.pt) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso (f ≫ c.π.app (op n))) : IsIso f := by
  let d : Cone D :=
    { pt := Y
      π := { app := fun i ↦ f ≫ c.π.app i, naturality := by intro i j g; simp } }
  let hd : IsLimit d := isLimit_of_eventually_isIso d N h
  have he : (hd.conePointUniqueUpToIso hc).hom = f :=
    hc.hom_ext fun j ↦ hd.conePointUniqueUpToIso_hom_comp hc j
  rw [← he]
  infer_instance

private lemma isMittagLeffler_of_splitEpi_succ (D : ℕᵒᵖ ⥤ Ab.{u})
    (h : ∀ n : ℕ, IsSplitEpi (D.map (homOfLE (Nat.le_succ n)).op)) :
    (D ⋙ forget Ab).IsMittagLeffler := by
  have hepi (m n : ℕ) (hmn : m ≤ n) : Epi (D.map (homOfLE hmn).op) := by
    induction n, hmn using Nat.le_induction with
    | base => simpa using (inferInstance : Epi (𝟙 (D.obj (op m))))
    | @succ n hmn ih =>
      have := h n
      have hcomp : D.map (homOfLE (Nat.le_succ n)).op ≫ D.map (homOfLE hmn).op =
          D.map (homOfLE (Nat.le_trans hmn (Nat.le_succ n))).op := by
        rw [← D.map_comp]
        congr 1
      rw [← hcomp]
      infer_instance
  refine Functor.isMittagLeffler_of_surjective _ fun i j f ↦ ?_
  have he : Epi (D.map f) := by
    have hle : j.unop ≤ i.unop := leOfHom f.unop
    simpa only [show f = (homOfLE hle).op from Subsingleton.elim _ _] using hepi j.unop i.unop hle
  exact (AddCommGrpCat.epi_iff_surjective (D.map f)).mp he

private lemma isEssentiallyConstantPro_shortComplexHomology_of_derived_cone
    (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (Y : DerivedCategory Ab.{u})
    (f : Y ⟶ DerivedCategory.Q.obj (limit D)) (a b c : ℤ) (ha : (up ℤ).prev b = a)
    (hc : (up ℤ).next b = c) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso ((DerivedCategory.homologyFunctor Ab.{u} b).map
      (f ≫ DerivedCategory.Q.map (limit.π D (op n))))) :
    EssentiallyConstantPro.IsEssentiallyConstantPro
      (D ⋙ HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) a b c ⋙
        ShortComplex.homologyFunctor Ab.{u}) := by
  let H := DerivedCategory.homologyFunctor Ab.{u} b
  let β := DerivedCategory.homologyFunctorFactors Ab.{u} b ≪≫
    HomologicalComplex.homologyFunctorIso' Ab.{u} (up ℤ) a b c ha hc
  let c₀ : Cone (D ⋙ HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) a b c ⋙
      ShortComplex.homologyFunctor Ab.{u}) :=
    { pt := H.obj Y
      π :=
        { app := fun i ↦ H.map (f ≫ DerivedCategory.Q.map (limit.π D i)) ≫ β.hom.app (D.obj i)
          naturality := by
            intro i j g
            simp only [Functor.const_obj_map, Functor.comp_map, Category.assoc]
            have hnat := β.hom.naturality (D.map g)
            simp only [Functor.comp_map] at hnat
            rw [← hnat, ← Category.assoc, ← Category.assoc]
            refine congrArg (· ≫ β.hom.app (D.obj j)) ?_
            calc
              𝟙 (H.obj Y) ≫ H.map (f ≫ DerivedCategory.Q.map (limit.π D j)) =
                  H.map (f ≫ DerivedCategory.Q.map (limit.π D j)) := Category.id_comp _
              _ = H.map (f ≫ DerivedCategory.Q.map (limit.π D i) ≫
                  DerivedCategory.Q.map (D.map g)) := by
                    rw [← DerivedCategory.Q.map_comp, limit.w]
              _ = H.map (f ≫ DerivedCategory.Q.map (limit.π D i)) ≫
                  H.map (DerivedCategory.Q.map (D.map g)) := by
                    rw [← H.map_comp]
                    simp only [Category.assoc] } }
  refine isEssentiallyConstantPro_of_eventually_isIso c₀ N fun n hn ↦ ?_
  dsimp only [c₀]
  have := h n hn
  infer_instance

@[simps]
private def towerDifferential (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b : ℤ) :
    D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a ⟶
      D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b where
  app i := (D.obj i).d a b
  naturality _ _ f := (D.map f).comm a b

private lemma towerDifferential_comp (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c : ℤ)
    (i : ℕᵒᵖ) :
    (towerDifferential D a b).app i ≫ (towerDifferential D b c).app i = 0 :=
  (D.obj i).d_comp_d a b c

/-- The canonical comparison from a degree of the limit of a tower of complexes to the limit of
that degree. -/
private def evalLimitComparison (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a : ℤ) :
    (limit D).X a ⟶ limit (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a) :=
  limit.lift (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a)
    ((HomologicalComplex.eval Ab.{u} (up ℤ) a).mapCone (limit.cone D))

@[reassoc]
private lemma evalLimitComparison_π (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a : ℤ) (i : ℕᵒᵖ) :
    evalLimitComparison D a ≫ limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a) i =
      (limit.π D i).f a :=
  limit.lift_π _ i

private instance isIso_evalLimitComparison (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a : ℤ) :
    IsIso (evalLimitComparison D a) :=
  (limit.isLimit
      (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a)).nonempty_isLimit_iff_isIso_lift.mp
    ⟨isLimitOfPreserves (HomologicalComplex.eval Ab.{u} (up ℤ) a) (limit.isLimit D)⟩

/-- The canonical comparison of `evalLimitComparison`, as an isomorphism. -/
private def evalLimitIso (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a : ℤ) :
    (limit D).X a ≅ limit (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a) :=
  asIso (evalLimitComparison D a)

private lemma evalLimitIso_hom (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a : ℤ) :
    (evalLimitIso D a).hom = evalLimitComparison D a :=
  rfl

private lemma evalLimitComparison_comm (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b : ℤ) :
    evalLimitComparison D a ≫ limMap (towerDifferential D a b) =
      (limit D).d a b ≫ evalLimitComparison D b :=
  limit.hom_ext fun i ↦ by
    have hl : (evalLimitComparison D a ≫ limMap (towerDifferential D a b)) ≫
        limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i =
        (limit.π D i).f a ≫ (D.obj i).d a b :=
      calc (evalLimitComparison D a ≫ limMap (towerDifferential D a b)) ≫
            limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i
          = evalLimitComparison D a ≫ limMap (towerDifferential D a b) ≫
            limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i := Category.assoc _ _ _
        _ = evalLimitComparison D a ≫
            limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a) i ≫
              (towerDifferential D a b).app i := by
                rw [limMap_π]
        _ = (limit.π D i).f a ≫ (D.obj i).d a b := evalLimitComparison_π_assoc D a i _
    have hr : ((limit D).d a b ≫ evalLimitComparison D b) ≫
        limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i =
        (limit D).d a b ≫ (limit.π D i).f b :=
      calc ((limit D).d a b ≫ evalLimitComparison D b) ≫
            limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i
          = (limit D).d a b ≫ evalLimitComparison D b ≫
            limit.π (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b) i := Category.assoc _ _ _
        _ = (limit D).d a b ≫ (limit.π D i).f b := by rw [evalLimitComparison_π]
    rw [hl, hr]
    exact (limit.π D i).comm a b

private def limitShortComplexIso (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c : ℤ) :
    (HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) a b c).obj (limit D) ≅
      limitShortComplexOfInvSystem (towerDifferential D a b) (towerDifferential D b c)
        (towerDifferential_comp D a b c) :=
  ShortComplex.isoMk (evalLimitIso D a) (evalLimitIso D b) (evalLimitIso D c)
    (evalLimitComparison_comm D a b) (evalLimitComparison_comm D b c)

private lemma limitShortComplexIso_hom_τ₁ (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c : ℤ) :
    (limitShortComplexIso D a b c).hom.τ₁ = evalLimitComparison D a :=
  rfl

private lemma limitShortComplexIso_hom_τ₂ (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c : ℤ) :
    (limitShortComplexIso D a b c).hom.τ₂ = evalLimitComparison D b :=
  rfl

private lemma limitShortComplexIso_hom_τ₃ (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c : ℤ) :
    (limitShortComplexIso D a b c).hom.τ₃ = evalLimitComparison D c :=
  rfl

private lemma limitShortComplexIso_hom_comp_π (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ)
    (a b c : ℤ) (i : ℕᵒᵖ) :
    (limitShortComplexIso D a b c).hom ≫
        limitShortComplexπ (towerDifferential D a b) (towerDifferential D b c)
          (towerDifferential_comp D a b c) i =
      (HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) a b c).map (limit.π D i) :=
  ShortComplex.hom_ext _ _ (evalLimitComparison_π D a i) (evalLimitComparison_π D b i)
    (evalLimitComparison_π D c i)

private lemma homologyFunctor_map_limitShortComplexIso_comp (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ)
    (a b c : ℤ) (i : ℕᵒᵖ) :
    (ShortComplex.homologyFunctor Ab.{u}).map (limitShortComplexIso D a b c).hom ≫
        (ShortComplex.homologyFunctor Ab.{u}).map
          (limitShortComplexπ (towerDifferential D a b) (towerDifferential D b c)
            (towerDifferential_comp D a b c) i) =
      (ShortComplex.homologyFunctor Ab.{u}).map
        ((HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) a b c).map (limit.π D i)) := by
  rw [← Functor.map_comp, limitShortComplexIso_hom_comp_π]
  rfl

private lemma isIso_of_eventually_isIso_homologyLimit
    (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ) (a b c d : ℤ)
    (hA : (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) a ⋙ forget Ab.{u}).IsMittagLeffler)
    (hB : (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) b ⋙ forget Ab.{u}).IsMittagLeffler)
    (hH : EssentiallyConstantPro.IsEssentiallyConstantPro
      (homologyInvSystem (towerDifferential D a b) (towerDifferential D b c)
        (towerDifferential_comp D a b c)))
    {Y : Ab.{u}}
    (φ : Y ⟶ (ShortComplex.homologyFunctor Ab.{u}).obj
      ((HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) b c d).obj (limit D)))
    (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → IsIso (φ ≫ (ShortComplex.homologyFunctor Ab.{u}).map
      ((HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) b c d).map (limit.π D (op n))))) :
    IsIso φ := by
  have hlift : IsIso (comparisonHomologyLimit (towerDifferential D b c)
      (towerDifferential D c d) (towerDifferential_comp D b c d)) :=
    isIso_comparisonHomologyLimit_of_isMittagLeffler _ _ _ _
      (towerDifferential D a b) (towerDifferential D b c) (towerDifferential D c d)
      (towerDifferential_comp D a b c) (towerDifferential_comp D b c d) hA hB hH
  have hcone : Nonempty (IsLimit ((ShortComplex.homologyFunctor Ab.{u}).mapCone
      (limitShortComplexCone (towerDifferential D b c) (towerDifferential D c d)
        (towerDifferential_comp D b c d)))) :=
    (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.mpr hlift
  have hψ : IsIso (φ ≫ (ShortComplex.homologyFunctor Ab.{u}).map
      (limitShortComplexIso D b c d).hom) := by
    refine isIso_of_eventually_isIso_comp_cone _ hcone.some
      (φ ≫ (ShortComplex.homologyFunctor Ab.{u}).map (limitShortComplexIso D b c d).hom)
      N fun n hn ↦ ?_
    change IsIso ((φ ≫ (ShortComplex.homologyFunctor Ab.{u}).map
        (limitShortComplexIso D b c d).hom) ≫
      (ShortComplex.homologyFunctor Ab.{u}).map
        (limitShortComplexπ (towerDifferential D b c) (towerDifferential D c d)
          (towerDifferential_comp D b c d) (op n)))
    rw [Category.assoc, homologyFunctor_map_limitShortComplexIso_comp]
    exact h n hn
  exact IsIso.of_isIso_comp_right φ
    ((ShortComplex.homologyFunctor Ab.{u}).map (limitShortComplexIso D b c d).hom)

private lemma isIso_of_eventually_isIso_homology_tower_aux
    (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ)
    (hML : ∀ q : ℤ,
      (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) q ⋙ forget Ab.{u}).IsMittagLeffler)
    {W : DerivedCategory Ab.{u}} (w : W ⟶ DerivedCategory.Q.obj (limit D))
    (hev : ∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor Ab.{u} q).map
        (w ≫ DerivedCategory.Q.map (limit.π D (op n))))) :
    IsIso w := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have hprev' : (up ℤ).prev (q - 1) = q - 2 := by simp [CochainComplex.prev]; omega
  have hnext' : (up ℤ).next (q - 1) = q := by simp [CochainComplex.next]
  have hprevq : (up ℤ).prev q = q - 1 := by simp [CochainComplex.prev]
  have hnextq : (up ℤ).next q = q + 1 := by simp [CochainComplex.next]
  obtain ⟨N₁, hN₁⟩ := hev (q - 1)
  have hprev : EssentiallyConstantPro.IsEssentiallyConstantPro
      (homologyInvSystem (towerDifferential D (q - 2) (q - 1)) (towerDifferential D (q - 1) q)
        (towerDifferential_comp D (q - 2) (q - 1) q)) :=
    isEssentiallyConstantPro_shortComplexHomology_of_derived_cone D W w (q - 2) (q - 1) q
      hprev' hnext' N₁ hN₁
  obtain ⟨N, hN⟩ := hev q
  set β := DerivedCategory.homologyFunctorFactors Ab.{u} q ≪≫
    HomologicalComplex.homologyFunctorIso' Ab.{u} (up ℤ) (q - 1) q (q + 1) hprevq hnextq
    with hβ
  have hq : IsIso ((DerivedCategory.homologyFunctor Ab.{u} q).map w ≫ β.hom.app (limit D)) := by
    refine isIso_of_eventually_isIso_homologyLimit D (q - 2) (q - 1) q (q + 1)
      (hML (q - 2)) (hML (q - 1)) hprev _ N fun n hn ↦ ?_
    have hstep : ((DerivedCategory.homologyFunctor Ab.{u} q).map w ≫ β.hom.app (limit D)) ≫
        (ShortComplex.homologyFunctor Ab.{u}).map
          ((HomologicalComplex.shortComplexFunctor' Ab.{u} (up ℤ) (q - 1) q (q + 1)).map
            (limit.π D (op n))) =
        (DerivedCategory.homologyFunctor Ab.{u} q).map
          (w ≫ DerivedCategory.Q.map (limit.π D (op n))) ≫ β.hom.app (D.obj (op n)) := by
      have hnat := β.hom.naturality (limit.π D (op n))
      simp only [Functor.comp_map] at hnat
      rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp]
    rw [hstep]
    have := hN n hn
    infer_instance
  exact IsIso.of_isIso_comp_right _ (β.hom.app (limit D))

private lemma isIso_of_eventually_isIso_homology_tower
    (D : ℕᵒᵖ ⥤ CochainComplex Ab.{u} ℤ)
    (hML : ∀ q : ℤ,
      (D ⋙ HomologicalComplex.eval Ab.{u} (up ℤ) q ⋙ forget Ab.{u}).IsMittagLeffler)
    {Z : CochainComplex Ab.{u} ℤ} (t : Z ⟶ limit D) [IsIso t]
    {W : DerivedCategory Ab.{u}} (w : W ⟶ DerivedCategory.Q.obj Z)
    (hev : ∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor Ab.{u} q).map
        (w ≫ DerivedCategory.Q.map (t ≫ limit.π D (op n))))) :
    IsIso w := by
  have hw : IsIso (w ≫ DerivedCategory.Q.map t) := by
    refine isIso_of_eventually_isIso_homology_tower_aux D hML _ fun q ↦ ?_
    obtain ⟨N, hN⟩ := hev q
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Category.assoc, ← Functor.map_comp]
    exact hN n hn
  exact IsIso.of_isIso_comp_right w (DerivedCategory.Q.map t)

section

variable (X : TopCat.{u})

/-! ### Homotopies and the total alternating Čech complex -/

private def alternatingCechTotalMapHomotopy {I : Type u} (U : I → Opens X)
    {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy ((alternatingCechTotalComplexFunctor U).map f)
      ((alternatingCechTotalComplexFunctor U).map g) :=
  HomologicalComplex₂.totalMapHomotopy₂ (f := (alternatingCechBicomplexFunctor U).map f)
    (g := (alternatingCechBicomplexFunctor U).map g) (c₁₂ := up ℤ)
    ((alternatingCechComplexFunctorInt U).mapHomotopy h)

private lemma quasiIso_alternatingCechTotal_map_of_homotopyEquiv {I : Type u} (U : I → Opens X)
    {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} (e : HomotopyEquiv K L) :
    QuasiIso ((alternatingCechTotalComplexFunctor U).map e.hom) := by
  let T := alternatingCechTotalComplexFunctor.{u, u, u} U
  let e' : HomotopyEquiv (T.obj K) (T.obj L) :=
    { hom := T.map e.hom
      inv := T.map e.inv
      homotopyHomInvId := by
        rw [← T.map_comp]
        exact (alternatingCechTotalMapHomotopy X U e.homotopyHomInvId).trans
          (Homotopy.ofEq (T.map_id K))
      homotopyInvHomId := by
        rw [← T.map_comp]
        exact (alternatingCechTotalMapHomotopy X U e.homotopyInvHomId).trans
          (Homotopy.ofEq (T.map_id L)) }
  exact e'.quasiIso_hom

/-! ### Finiteness of the Čech direction -/

private lemma isIso_total_map_f_of_summands {A : Type*} [Category A] [Abelian A]
    {K L : HomologicalComplex₂ A (up ℤ) (up ℤ)}
    [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] (φ : K ⟶ L) (n : ℤ)
    (hφ : ∀ p q : ℤ, (up ℤ).π (up ℤ) (up ℤ) (p, q) = n → IsIso ((φ.f p).f q)) :
    IsIso ((HomologicalComplex₂.total.map φ (up ℤ)).f n) :=
  ⟨⟨L.totalDesc fun p q hpq ↦
      have := hφ p q hpq
      inv ((φ.f p).f q) ≫ K.ιTotal (up ℤ) p q n hpq,
    HomologicalComplex₂.total.hom_ext _ fun p q hpq ↦ by simp,
    HomologicalComplex₂.total.hom_ext _ fun p q hpq ↦ by simp⟩⟩

private lemma isZero_alternatingCechComplexFunctorInt_X {I : Type u} [Finite I]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (p : ℤ)
    (hp : p < 0 ∨ (Nat.card I : ℤ) ≤ p) :
    IsZero (((alternatingCechComplexFunctorInt.{u, u, u} U).obj P).X p) := by
  change IsZero (((alternatingCechComplex U P).extend embeddingUpNat).X p)
  by_cases hp0 : p < 0
  · refine HomologicalComplex.isZero_extend_X _ _ _ fun i hi ↦ ?_
    change (i : ℤ) = p at hi
    omega
  · have hcast : embeddingUpNat.f p.toNat = p := Int.toNat_of_nonneg (by omega)
    refine IsZero.of_iso ?_
      ((alternatingCechComplex U P).extendXIso embeddingUpNat hcast)
    rw [alternatingCechComplex_X]
    exact isZero_alternatingSubgroup_of_card_lt U P p.toNat (by omega)

private lemma isIso_alternatingCechTotal_map_f {I : Type u} [Finite I] (U : I → Opens X)
    {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} (f : K ⟶ L)
    (a n : ℤ) (han : a + Nat.card I ≤ n) (hf : ∀ q : ℤ, a < q → IsIso (f.f q)) :
    IsIso (((alternatingCechTotalComplexFunctor U).map f).f n) := by
  refine isIso_total_map_f_of_summands _ _ fun p q hpq ↦ ?_
  change p + q = n at hpq
  change IsIso ((HomologicalComplex.extendMap
    ((alternatingCechComplexFunctor U).map (f.f q)) embeddingUpNat).f p)
  by_cases hp : p < 0 ∨ (Nat.card I : ℤ) ≤ p
  · exact (isZero_alternatingCechComplexFunctorInt_X X U (K.X q) p hp).isIso
      (isZero_alternatingCechComplexFunctorInt_X X U (L.X q) p hp) _
  · have := hf q (by omega)
    have h₂ : IsIso (HomologicalComplex.extendMap
        ((alternatingCechComplexFunctor U).map (f.f q)) embeddingUpNat) :=
      Functor.map_isIso (embeddingUpNat.extendFunctor AddCommGrpCat.{u})
        ((alternatingCechComplexFunctor U).map (f.f q))
    infer_instance

private lemma isIso_πTruncGE_f_of_lt {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (a q : ℤ) (haq : a < q) :
    IsIso ((K.πTruncGE a).f q) := by
  have he : (embeddingUpIntGE a).f (q - a).natAbs = q := by
    change a + ((q - a).natAbs : ℤ) = q
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  change IsIso (((embeddingUpIntGE a).liftExtend (K.restrictionToTruncGE' (embeddingUpIntGE a))
    (K.restrictionToTruncGE'_hasLift (embeddingUpIntGE a))).f q)
  rw [(embeddingUpIntGE a).isIso_liftExtend_f_iff _ _ he]
  refine K.isIso_restrictionToTruncGE' _ _ fun h ↦ ?_
  rw [boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero] at h
  omega

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

private lemma isIso_alternatingCechTotal_πTruncGE_f {I : Type u} [Finite I] (U : I → Opens X)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) (a n : ℤ) (han : a + Nat.card I ≤ n) :
    IsIso (((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (F.πTruncGE a))).f n) := by
  refine isIso_alternatingCechTotal_map_f X U _ a n han fun q hq ↦ ?_
  have := isIso_πTruncGE_f_of_lt F a q hq
  change IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map
    ((F.πTruncGE a).f q))
  infer_instance

private lemma quasiIsoAt_alternatingCechTotal_πTruncGE {I : Type u} [Finite I] (U : I → Opens X)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) (a n : ℤ) (han : a + Nat.card I < n) :
    QuasiIsoAt ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (F.πTruncGE a))) n := by
  set f := (alternatingCechTotalComplexFunctor U).map
    ((underlyingPresheafComplexFunctor X R).map (F.πTruncGE a))
  have h₁ : IsIso (f.f (n - 1)) :=
    isIso_alternatingCechTotal_πTruncGE_f X R U F a (n - 1) (by omega)
  have h₃ : IsIso (f.f (n + 1)) :=
    isIso_alternatingCechTotal_πTruncGE_f X R U F a (n + 1) (by omega)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ (up ℤ) n).map f))
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · change Epi (f.f ((up ℤ).prev n))
    rw [CochainComplex.prev]
    exact IsIso.epi_of_iso _
  · exact isIso_alternatingCechTotal_πTruncGE_f X R U F a n (by omega)
  · change Mono (f.f ((up ℤ).next n))
    rw [CochainComplex.next]
    exact IsIso.mono_of_iso _

private lemma eventually_quasiIsoAt_alternatingCechTotal_πTruncGE
    {I : Type u} [Finite I] (U : I → Opens X)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) (q : ℤ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      QuasiIsoAt ((alternatingCechTotalComplexFunctor U).map
        ((underlyingPresheafComplexFunctor X R).map (F.πTruncGE (-(n : ℤ))))) q := by
  refine ⟨((Nat.card I : ℤ) - q + 1).toNat, fun n hn ↦ ?_⟩
  apply quasiIsoAt_alternatingCechTotal_πTruncGE
  have h : (((Nat.card I : ℤ) - q + 1).toNat : ℤ) ≤ n := Int.ofNat_le.mpr hn
  omega

/-- The alternating Čech functor into the derived category inverts `f` as soon as the total
alternating Čech complex of `f` is a quasi-isomorphism. -/
private lemma isIso_alternatingCechDerived_map_of_quasiIso {I : Type u} (U : I → Opens X)
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map f))) :
    IsIso ((alternatingCechDerivedFunctor X R U).map f) := by
  change IsIso (DerivedCategory.Q.map ((alternatingCechTotalComplexFunctor U).map
    ((underlyingPresheafComplexFunctor X R).map f)))
  rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]

end

section

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-! ### Maps between K-injective complexes -/

private lemma isIso_alternatingCechDerived_map_of_isKInjective {I : Type u} (U : I → Opens X)
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) [QuasiIso f] :
    IsIso ((alternatingCechDerivedFunctor X R U).map f) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp inferInstance
  exact isIso_alternatingCechDerived_map_of_quasiIso X R U _
    (quasiIso_alternatingCechTotal_map_of_homotopyEquiv X U
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).mapHomotopyEquiv
        (c := up ℤ) e))

private instance quasiIso_kInjectiveResolutionUnit
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    QuasiIso (kInjectiveResolutionUnit X R K) :=
  inferInstanceAs (QuasiIso ((kInjectiveResolutionInclusion X R).app K))

private lemma quasiIso_kInjectiveResolution_map
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((kInjectiveResolution X R).map f) := by
  have h : QuasiIso ((kInjectiveResolutionInclusion X R).app K ≫
      (kInjectiveResolution X R).map f) := by
    rw [← (kInjectiveResolutionInclusion X R).naturality f]
    exact quasiIso_comp f ((kInjectiveResolutionInclusion X R).app L)
  exact quasiIso_of_comp_left ((kInjectiveResolutionInclusion X R).app K) _

/-! ### Global sections of the candidate resolution -/

private lemma isIso_Q_map_sectionsComplex_map_of_isKInjective
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L) [QuasiIso f] :
    IsIso (DerivedCategory.Q.map ((underlyingPresheafComplexFunctor X R ⋙
      globalSectionsUliftComplexFunctor.{u, u, u} X).map f)) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp inferInstance
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ⋙
    AddCommGrpCat.uliftFunctor.{u, u}).mapHomotopyEquiv (c := up ℤ)
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).mapHomotopyEquiv
        (c := up ℤ) e)).quasiIso_hom

private lemma isIso_unboundedDerivedGlobalSectionsFunctor_map
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso ((unboundedDerivedGlobalSectionsFunctor X R).map f) := by
  have h₁ : QuasiIso ((kInjectiveResolution X R).map f) := quasiIso_kInjectiveResolution_map X R f
  exact isIso_Q_map_sectionsComplex_map_of_isKInjective X R ((kInjectiveResolution X R).map f)

private instance isIso_globalSectionsToUnboundedDerived_app
    (L : CochainComplex (SheafOfModules.{u} R) ℤ) [L.IsKInjective] :
    IsIso ((globalSectionsToUnboundedDerived X R).app L) := by
  rw [globalSectionsToUnboundedDerived_app]
  exact isIso_Q_map_sectionsComplex_map_of_isKInjective X R (kInjectiveResolutionUnit X R L)

private lemma isIso_alternatingCechToDerivedComparison_app_of_isKInjective
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (L : CochainComplex (SheafOfModules.{u} R) ℤ) [L.IsKInjective] :
    IsIso ((alternatingCechToDerivedComparison X R U hU).app L) := by
  refine isIso_alternatingCechToDerivedComparison_app X R U hU L ?_
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact isIso_alternatingCechDerived_map_of_isKInjective X R U (kInjectiveResolutionUnit X R L)

private lemma inv_globalSectionsToUnboundedDerived_naturality
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (g : K ⟶ L)
    [IsIso ((globalSectionsToUnboundedDerived X R).app K)]
    [IsIso ((globalSectionsToUnboundedDerived X R).app L)] :
    inv ((globalSectionsToUnboundedDerived X R).app K) ≫
        (globalSectionsUliftDerivedFunctor X R).map g =
      (unboundedDerivedGlobalSectionsFunctor X R).map g ≫
        inv ((globalSectionsToUnboundedDerived X R).app L) := by
  refine (cancel_epi ((globalSectionsToUnboundedDerived X R).app K)).mp ?_
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc,
    ← (globalSectionsToUnboundedDerived X R).naturality g, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The canonical comparison from the global sections of the limit of a tower of complexes of
sheaves of modules to the limit of the global sections. -/
private def towerSectionsComparison (E : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} R) ℤ) :
    (underlyingPresheafComplexFunctor X R ⋙
        globalSectionsUliftComplexFunctor.{u, u, u} X).obj (limit E) ⟶
      limit (E ⋙ (underlyingPresheafComplexFunctor X R ⋙
        globalSectionsUliftComplexFunctor.{u, u, u} X)) :=
  limit.lift _ ((underlyingPresheafComplexFunctor X R ⋙
    globalSectionsUliftComplexFunctor.{u, u, u} X).mapCone (limit.cone E))

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
private lemma towerSectionsComparison_π
    (E : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} R) ℤ) (i : ℕᵒᵖ) :
    towerSectionsComparison X R E ≫
        limit.π (E ⋙ (underlyingPresheafComplexFunctor X R ⋙
          globalSectionsUliftComplexFunctor.{u, u, u} X)) i =
      (underlyingPresheafComplexFunctor X R ⋙
        globalSectionsUliftComplexFunctor.{u, u, u} X).map (limit.π E i) :=
  limit.lift_π _ i

private instance preservesLimitsOfShape_sectionsComplex :
    PreservesLimitsOfShape ℕᵒᵖ (underlyingPresheafComplexFunctor X R ⋙
      globalSectionsUliftComplexFunctor.{u, u, u} X) :=
  inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
    ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).mapHomologicalComplex
        (up ℤ) ⋙
      (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ⋙
        AddCommGrpCat.uliftFunctor.{u, u}).mapHomologicalComplex (up ℤ)))

private instance isIso_towerSectionsComparison
    (E : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} R) ℤ) :
    IsIso (towerSectionsComparison X R E) :=
  (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.mp
    ⟨isLimitOfPreserves (underlyingPresheafComplexFunctor X R ⋙
      globalSectionsUliftComplexFunctor.{u, u, u} X) (limit.isLimit E)⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
private lemma isSplitEpi_sectionsComplex_map_g
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (n : ℕ) (q : ℤ) :
    IsSplitEpi (((underlyingPresheafComplexFunctor X R ⋙
      globalSectionsUliftComplexFunctor.{u, u, u} X).map (C.g n)).f q) := by
  have h := C.splitEpi_g n q
  change IsSplitEpi ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ⋙
    AddCommGrpCat.uliftFunctor.{u, u}).map
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map ((C.g n).f q)))
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
private lemma isMittagLeffler_candidateTower
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (q : ℤ) :
    ((Functor.ofOpSequence C.g ⋙ (underlyingPresheafComplexFunctor X R ⋙
        globalSectionsUliftComplexFunctor.{u, u, u} X)) ⋙
      HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) q ⋙ forget Ab.{u}).IsMittagLeffler := by
  refine isMittagLeffler_of_splitEpi_succ ((Functor.ofOpSequence C.g ⋙
    (underlyingPresheafComplexFunctor X R ⋙ globalSectionsUliftComplexFunctor.{u, u, u} X)) ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) q) fun n ↦ ?_
  have hmap : (Functor.ofOpSequence C.g).map (homOfLE (Nat.le_succ n)).op = C.g n :=
    Functor.ofOpSequence_map_homOfLE_succ C.g n
  change IsSplitEpi (((underlyingPresheafComplexFunctor X R ⋙
    globalSectionsUliftComplexFunctor.{u, u, u} X).map
      ((Functor.ofOpSequence C.g).map (homOfLE (Nat.le_succ n)).op)).f q)
  rw [hmap]
  exact isSplitEpi_sectionsComplex_map_g X R F C n q

private lemma quasiIso_candidateCanonicalMap
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (h_homology : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.homology q))) :
    QuasiIso C.canonicalMap := by
  refine Stacks.KInjective.quasiIso_canonicalMap R F C B 0 (fun V ↦ ?_)
    (fun W hW p hp q _ ↦ h_homology W hW q p (by omega))
  obtain ⟨Us, hUs, hV⟩ := Opens.isBasis_iff_cover.mp hB V
  exact ⟨Us, hUs, by rw [hV, Opens.coe_sSup]⟩

private instance isKInjective_candidateStage
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (n : ℕ) :
    (C.I n).IsKInjective := by
  have hGE : (C.I n).IsStrictlyGE (-(n : ℤ)) := C.strictlyGE_I n
  have hinj : ∀ i : ℤ, Injective ((C.I n).X i) := C.injective_I n
  exact CochainComplex.isKInjective_of_injective (C.I n) (-(n : ℤ))

private instance isKInjective_candidateLimit
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) :
    (limit (Functor.ofOpSequence C.g)).IsKInjective :=
  C.kInjective_limit

/-! ### The inverse limit argument -/

/-- The projection from the limit of the tower of the candidate K-injective resolution onto
its `n`-th stage. -/
private def candidateLimitπ (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (n : ℕ) :
    limit (Functor.ofOpSequence C.g) ⟶ C.I n :=
  limit.π (Functor.ofOpSequence C.g) (op n)

private lemma canonicalMap_comp_candidateLimitπ (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (n : ℕ) :
    C.canonicalMap ≫ candidateLimitπ X R F C n = F.πTruncGE (-(n : ℤ)) ≫ C.f n :=
  C.canonicalMap_comp_π n

private lemma candidateComparison_comp_π
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F) (n : ℕ) :
    ((alternatingCechToDerivedComparison X R U hU).app F ≫
        (unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap ≫
        inv ((globalSectionsToUnboundedDerived X R).app
          (limit (Functor.ofOpSequence C.g)))) ≫
      (globalSectionsUliftDerivedFunctor X R).map (candidateLimitπ X R F C n) =
    (alternatingCechDerivedFunctor X R U).map (F.πTruncGE (-(n : ℤ)) ≫ C.f n) ≫
      (alternatingCechToDerivedComparison X R U hU).app (C.I n) ≫
      inv ((globalSectionsToUnboundedDerived X R).app (C.I n)) := by
  rw [Category.assoc, Category.assoc, inv_globalSectionsToUnboundedDerived_naturality,
    ← Category.assoc ((unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap),
    ← Functor.map_comp, canonicalMap_comp_candidateLimitπ, ← Category.assoc, ← Category.assoc,
    ← (alternatingCechToDerivedComparison X R U hU).naturality
      (F.πTruncGE (-(n : ℤ)) ≫ C.f n), Category.assoc]

private lemma eventually_isIso_homology_candidateStage
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F)
    (hstage : ∀ n : ℕ, QuasiIso ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n))))
    (q : ℤ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
        (((alternatingCechToDerivedComparison X R U hU).app F ≫
            (unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap ≫
            inv ((globalSectionsToUnboundedDerived X R).app
              (limit (Functor.ofOpSequence C.g)))) ≫
          (globalSectionsUliftDerivedFunctor X R).map (candidateLimitπ X R F C n))) := by
  obtain ⟨N, hN⟩ := eventually_quasiIsoAt_alternatingCechTotal_πTruncGE X R U F q
  refine ⟨N, fun n hn ↦ ?_⟩
  have hα : IsIso ((alternatingCechToDerivedComparison X R U hU).app (C.I n)) :=
    isIso_alternatingCechToDerivedComparison_app_of_isKInjective X R U hU (C.I n)
  have hstagen : IsIso ((alternatingCechDerivedFunctor X R U).map (C.f n)) :=
    isIso_alternatingCechDerived_map_of_quasiIso X R U _ (hstage n)
  have hπ : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
      ((alternatingCechDerivedFunctor X R U).map (F.πTruncGE (-(n : ℤ))))) := by
    change IsIso ((DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
      ((alternatingCechTotalComplexFunctor U).map
        ((underlyingPresheafComplexFunctor X R).map (F.πTruncGE (-(n : ℤ))))))
    rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} q)]
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hN n hn)
  rw [candidateComparison_comp_π X R U hU F C n]
  simp only [Functor.map_comp]
  infer_instance

/-- **The alternating Čech comparison of Tag 08C1 is invertible under the hypotheses of
Tag 08C2.** Let `(X, O_X)` be a ringed space, let `U` be a finite open covering of `X`, and let
`F^•` be a complex of `O_X`-modules whose cohomology sheaves are acyclic in positive degrees on
a basis `B` of the topology of `X`. If `C` is a candidate K-injective resolution of `F^•` as in
Tag 071A for which the total alternating Čech complex of every stage map
`τ_{≥ -n} F^• ⟶ C.I n` is a quasi-isomorphism, then the comparison map
`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)` of Tag 08C1 is an isomorphism. -/
theorem isIso_alternatingCechToDerivedComparison_of_stages
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (h_homology : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.homology q)))
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F)
    (hstage : ∀ n : ℕ, QuasiIso ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n)))) :
    IsIso ((alternatingCechToDerivedComparison X R U hU).app F) := by
  have : QuasiIso C.canonicalMap := quasiIso_candidateCanonicalMap X R F C B hB h_homology
  have hGcm : IsIso ((unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap) :=
    isIso_unboundedDerivedGlobalSectionsFunctor_map X R C.canonicalMap
  have hall : IsIso ((alternatingCechToDerivedComparison X R U hU).app F ≫
      (unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap ≫
      inv ((globalSectionsToUnboundedDerived X R).app
        (limit (Functor.ofOpSequence C.g)))) := by
    refine isIso_of_eventually_isIso_homology_tower _
      (isMittagLeffler_candidateTower X R F C)
      (towerSectionsComparison X R (Functor.ofOpSequence C.g)) _ fun q ↦ ?_
    obtain ⟨N, hN⟩ := eventually_isIso_homology_candidateStage X R U hU F C hstage q
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [towerSectionsComparison_π]
    exact hN n hn
  exact IsIso.of_isIso_comp_right _
    ((unboundedDerivedGlobalSectionsFunctor X R).map C.canonicalMap ≫
      inv ((globalSectionsToUnboundedDerived X R).app
        (limit (Functor.ofOpSequence C.g))))

end

end

end Stacks.Cech

end
