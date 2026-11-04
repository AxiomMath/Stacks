module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Homology.DerivedComplete.CountableMilnorTower
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SurjectiveTowerDifference

/-!
# The Milnor model of an epimorphic tower is its limit

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of cochain complexes of modules. The map
from `A` to the mapping cocone of `B ⟶ C` whose first component is the inclusion and whose second
component vanishes is a quasi-isomorphism. Applied to the short exact sequence
`0 ⟶ lim F ⟶ ∏ F ⟶ ∏ F ⟶ 0` (second map `1 - shift`) of a tower `F` of cochain complexes of
modules with epimorphic transition maps, this says that the augmentation of the limit into the
strict Milnor model `CountableMilnorTower.countableMilnorFunctor.obj F` is a quasi-isomorphism.

## Main definitions

* `CochainComplex.mappingCocone.toMappingCoconeId`: the map from the mapping cocone of `g : B ⟶ C`
  to the mapping cocone of `𝟙 C` induced by the square `(g, 𝟙 C)`.
* `CountableMilnorTower.TowerAugmentation.ofCone`: the augmentation of a tower given by a cone.

## Main results

* `CochainComplex.mappingCocone.quasiIso_lift_of_shortExact`: for a short exact sequence `S` of
  cochain complexes of modules, the canonical map `S.X₁ ⟶ mappingCocone S.g` is a
  quasi-isomorphism.
* `CountableMilnorTower.quasiIso_augmentationMap_ofCone`: for a tower with epimorphic transition
  maps and a limit cone, the augmentation of the limit into the Milnor model is a
  quasi-isomorphism.

## Implementation notes

The first result is deduced from the degreewise short exact sequence
`0 ⟶ A ⟶ mappingCocone g ⟶ mappingCocone (𝟙 C) ⟶ 0`, whose third term is zero in the derived
category, so that the first map of its distinguished triangle is an isomorphism there.

## References

* [Stacks Project, Tag 091D](https://stacks.math.columbia.edu/tag/091D)
* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex.mappingCocone

open HomComplex

section General

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {B C : CochainComplex V ℤ} (g : B ⟶ C)

/-- The differential of the second projection of a mapping cocone. -/
theorem δ_snd : δ (-1) 0 (snd g) = -Cochain.ofHom (fst g ≫ g) := by
  have h₁ : liftCochain g (Cochain.ofHom (fst g)) (snd g) (neg_add_cancel 1) =
      Cochain.ofHom (𝟙 _) := by
    ext p
    rw [Cochain.ofHom_v, HomologicalComplex.id_f, ← id_X g p (p + -1) rfl,
      ← Category.comp_id ((liftCochain g _ _ _).v p p (add_zero p)), ← id_X g p (p + -1) rfl]
    simp only [Preadditive.comp_add, liftCochain_v_fst_f_assoc, liftCochain_v_snd_v_assoc,
      Cochain.ofHom_v]
  have h₂ := δ_liftCochain g (Cochain.ofHom (fst g)) (snd g) (neg_add_cancel 1) 1 (zero_add 1)
  rw [h₁, δ_ofHom, δ_ofHom, Cochain.zero_comp, zero_sub, eq_comm,
    neg_eq_zero] at h₂
  ext p
  have h₃ := congrArg (fun z => z.v p (p + 1) rfl ≫ (snd g).v (p + 1) p (by omega)) h₂
  simp only [Cochain.comp_v _ _ (zero_add 1) p p (p + 1) (add_zero p) rfl, Category.assoc,
    inr_v_snd_v, Category.comp_id, Cochain.zero_v, zero_comp, Cochain.add_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h₃
  rw [Cochain.neg_v, Cochain.ofHom_v, HomologicalComplex.comp_f]
  exact eq_neg_of_add_eq_zero_left h₃

/-- The map from the mapping cocone of `g : B ⟶ C` to the mapping cocone of `𝟙 C` induced by the
commutative square `(g, 𝟙 C)`. -/
def toMappingCoconeId : mappingCocone g ⟶ mappingCocone (𝟙 C) :=
  lift (𝟙 C) (fst g ≫ g) (snd g) (by simp [δ_snd])

/-- The first component of `toMappingCoconeId`. -/
@[reassoc (attr := simp)]
theorem toMappingCoconeId_f_fst_f (p : ℤ) :
    (toMappingCoconeId g).f p ≫ (fst (𝟙 C)).f p = (fst g).f p ≫ g.f p := by
  simp [toMappingCoconeId]

/-- The second component of `toMappingCoconeId`. -/
@[reassoc (attr := simp)]
theorem toMappingCoconeId_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (toMappingCoconeId g).f p ≫ (snd (𝟙 C)).v p q hpq = (snd g).v p q hpq := by
  simp [toMappingCoconeId]

end General

section ModuleCat

variable {A : Type u} [Ring A]

/-- An element of a degree of the mapping cocone of a map of complexes of modules is determined
by its two components. -/
theorem ext_apply {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) (p : ℤ)
    {x y : (mappingCocone φ).X p} (h₁ : (fst φ).f p x = (fst φ).f p y)
    (h₂ : (snd φ).v p (p + -1) rfl x = (snd φ).v p (p + -1) rfl y) : x = y := by
  have e := id_X φ p (p + -1) rfl
  have hx := congrArg (fun f => f x) e
  have hy := congrArg (fun f => f y) e
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at hx hy
  rw [← hx, ← hy, h₁, h₂]

variable (S : ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ))

/-- The canonical map from the first term of a short complex of complexes to the mapping cocone
of its second map: the first map, with vanishing second component. -/
abbrev liftShortComplex : S.X₁ ⟶ mappingCocone S.g :=
  lift S.g S.f 0 (by simp)

/-- The first component of `liftShortComplex`, elementwise. -/
theorem liftShortComplex_fst_apply (p : ℤ) (x : S.X₁.X p) :
    (fst S.g).f p ((liftShortComplex S).f p x) = S.f.f p x :=
  (elementwise_of% (lift_f_fst_f S.g S.f 0 (by simp) p)) x

/-- The second component of `liftShortComplex` vanishes, elementwise. -/
theorem liftShortComplex_snd_apply (p : ℤ) (x : S.X₁.X p) :
    (snd S.g).v p (p + -1) rfl ((liftShortComplex S).f p x) = 0 := by
  have := (elementwise_of% (lift_f_snd_v S.g S.f 0 (by simp)
    p (p + -1) rfl)) x
  rw [this, Cochain.zero_v]
  rfl

/-- The first component of `toMappingCoconeId`, elementwise. -/
theorem toMappingCoconeId_fst_apply {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (p : ℤ) (x : (mappingCocone φ).X p) :
    (fst (𝟙 L)).f p ((toMappingCoconeId φ).f p x) = φ.f p ((fst φ).f p x) :=
  (elementwise_of% (toMappingCoconeId_f_fst_f φ p)) x

/-- The second component of `toMappingCoconeId`, elementwise. -/
theorem toMappingCoconeId_snd_apply {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (p : ℤ) (x : (mappingCocone φ).X p) :
    (snd (𝟙 L)).v p (p + -1) rfl ((toMappingCoconeId φ).f p x) = (snd φ).v p (p + -1) rfl x :=
  (elementwise_of% (toMappingCoconeId_f_snd_v φ p (p + -1) rfl)) x

/-- The short complex `S.X₁ ⟶ mappingCocone S.g ⟶ mappingCocone (𝟙 S.X₃)`. -/
def coconeShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ) :=
  ShortComplex.mk (liftShortComplex S) (toMappingCoconeId S.g) (by
    ext p x
    change (toMappingCoconeId S.g).f p ((liftShortComplex S).f p x) = 0
    apply ext_apply
    · rw [toMappingCoconeId_fst_apply, liftShortComplex_fst_apply, map_zero]
      exact (elementwise_of% (HomologicalComplex.congr_hom S.zero p)) x
    · rw [toMappingCoconeId_snd_apply, liftShortComplex_snd_apply, map_zero])

variable {S}

/-- For a short exact sequence `S` of complexes of modules, the short complex
`S.X₁ ⟶ mappingCocone S.g ⟶ mappingCocone (𝟙 S.X₃)` is short exact. -/
theorem shortExact_coconeShortComplex (hS : S.ShortExact) :
    (coconeShortComplex S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  have hs := hS.map_of_exact (HomologicalComplex.eval _ _ p)
  have hex := (ShortComplex.moduleCat_exact_iff _).mp hs.exact
  have hinj := (ModuleCat.mono_iff_injective _).mp hs.mono_f
  have hsurj := (ModuleCat.epi_iff_surjective _).mp hs.epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change (toMappingCoconeId S.g).f p x = 0 at hx
    have h₁ : S.g.f p ((fst S.g).f p x) = 0 :=
      (toMappingCoconeId_fst_apply S.g p x).symm.trans (by rw [hx, map_zero])
    have h₂ : (snd S.g).v p (p + -1) rfl x = 0 :=
      (toMappingCoconeId_snd_apply S.g p x).symm.trans (by rw [hx, map_zero])
    obtain ⟨a, ha⟩ := hex _ h₁
    refine ⟨a, ?_⟩
    show (liftShortComplex S).f p a = x
    apply ext_apply
    · exact (liftShortComplex_fst_apply S p a).trans ha
    · rw [liftShortComplex_snd_apply, h₂]
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change (liftShortComplex S).f p a = (liftShortComplex S).f p b at h
    exact hinj ((liftShortComplex_fst_apply S p a).symm.trans
      ((congrArg (fun z => (fst S.g).f p z) h).trans (liftShortComplex_fst_apply S p b)))
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨b, hb⟩ := hsurj ((fst (𝟙 S.X₃)).f p y)
    change S.g.f p b = _ at hb
    refine ⟨(inl S.g).v p p (add_zero p) b +
      (inr S.g).1.v (p + -1) p (by omega) ((snd (𝟙 S.X₃)).v p (p + -1) rfl y), ?_⟩
    show (toMappingCoconeId S.g).f p _ = y
    set z := (snd (𝟙 S.X₃)).v p (p + -1) rfl y
    have e₁ : (fst S.g).f p ((inl S.g).v p p (add_zero p) b) = b :=
      (elementwise_of% (inl_v_fst_f S.g p)) b
    have e₂ : (fst S.g).f p ((inr S.g).1.v (p + -1) p (by omega) z) = 0 := by
      simpa using (elementwise_of% (inr_v_fst_f S.g (p + -1) p (by omega))) z
    have e₃ : (snd S.g).v p (p + -1) rfl ((inl S.g).v p p (add_zero p) b) = 0 := by
      simpa using (elementwise_of% (inl_v_snd_v S.g p (p + -1) rfl)) b
    have e₄ : (snd S.g).v p (p + -1) rfl ((inr S.g).1.v (p + -1) p (by omega) z) = z :=
      (elementwise_of% (inr_v_snd_v S.g (p + -1) p (by omega))) z
    apply ext_apply
    · rw [toMappingCoconeId_fst_apply, map_add, e₁, e₂, map_add, map_zero, add_zero, hb]
    · rw [toMappingCoconeId_snd_apply, map_add, e₃, e₄, zero_add]

/-- **For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of complexes of modules, the canonical map
`A ⟶ mappingCocone (B ⟶ C)` is a quasi-isomorphism.** -/
theorem quasiIso_lift_of_shortExact (hS : S.ShortExact) : QuasiIso (liftShortComplex S) := by
  have hT := DerivedCategory.triangleOfSES_distinguished (shortExact_coconeShortComplex hS)
  have hZ : IsZero (DerivedCategory.Q.obj (mappingCocone (𝟙 S.X₃))) := by
    have h := DerivedCategory.mappingCocone_triangle_distinguished (𝟙 S.X₃)
    refine (Triangle.isZero₁_iff_isIso₂ _ h).2 ?_
    show IsIso (DerivedCategory.Q.map (𝟙 S.X₃))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ

end ModuleCat

end CochainComplex.mappingCocone

namespace CountableMilnorTower

variable {A : Type u} [Ring A]

/-- The augmentation of a tower given by a cone: the legs of the cone. -/
def TowerAugmentation.ofCone {F : Tower.{u, v} (A := A)} (s : Cone F) : TowerAugmentation F where
  source := s.pt
  app n := s.π.app ⟨n⟩
  naturality n := s.w (homOfLE (Nat.le_succ n)).op

/-- The source of the augmentation of a cone is its point. -/
@[simp]
theorem TowerAugmentation.ofCone_source {F : Tower.{u, v} (A := A)} (s : Cone F) :
    (TowerAugmentation.ofCone s).source = s.pt := rfl

/-- The components of the augmentation of a cone are its legs. -/
@[simp]
theorem TowerAugmentation.ofCone_app {F : Tower.{u, v} (A := A)} (s : Cone F) (n : ℕ) :
    (TowerAugmentation.ofCone s).app n = s.π.app ⟨n⟩ := rfl

/-- The difference map `x ↦ (x n - t n (x (n + 1)))` on a countable product of modules is an
epimorphism when all the transition maps `t n` are. -/
theorem epi_pi_sub_shift_of_epi (X : ℕ → ModuleCat.{v} A) (t : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, Epi (t n)] :
    Epi (Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift (fun n ↦ t n)
    (fun n ↦ (ModuleCat.epi_iff_surjective (t n)).mp inferInstance)
    ((ModuleCat.piIsoPi X).hom y)
  refine ⟨(ModuleCat.piIsoPi X).inv x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  show ((Pi.lift (fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) ≫ Pi.π X n)
    ((ModuleCat.piIsoPi X).inv x)) = _
  rw [Pi.lift_π]
  show (Pi.π X n) ((ModuleCat.piIsoPi X).inv x) -
    (t n) ((Pi.π X (n + 1)) ((ModuleCat.piIsoPi X).inv x)) =
      (ModuleCat.piIsoPi X).hom y n
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  exact congrFun hx n

/-- **The Milnor endomorphism `1 - shift` of a tower with epimorphic transition maps is an
epimorphism.** -/
theorem epi_oneMinusShift (F : Tower.{u, v} (A := A))
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] : Epi (oneMinusShift F) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let X := fun n : ℕ ↦ F.obj ⟨n⟩
  let t := fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op
  let G := HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) i
  let d' := Pi.lift fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n -
    Pi.π (fun n ↦ G.obj (X n)) (n + 1) ≫ G.map (t n)
  have : Epi d' := epi_pi_sub_shift_of_epi (fun n ↦ G.obj (X n)) (fun n ↦ G.map (t n))
  let e := asIso (piComparison G X)
  have hd : G.map (oneMinusShift F) ≫ e.hom = e.hom ≫ d' := by
    apply Pi.hom_ext
    intro n
    show (G.map (oneMinusShift F) ≫ piComparison G X) ≫ Pi.π _ n =
      (piComparison G X ≫ d') ≫ Pi.π _ n
    rw [Category.assoc, piComparison_comp_π, ← G.map_comp, oneMinusShift_π]
    simp only [d', Pi.lift_π, G.map_sub, G.map_comp, Category.assoc,
      Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π, X, t]
  have : Epi (G.map (oneMinusShift F) ≫ e.hom) := by
    rw [hd]
    infer_instance
  have hepi : Epi ((G.map (oneMinusShift F) ≫ e.hom) ≫ e.inv) := inferInstance
  show Epi (G.map (oneMinusShift F))
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hepi

/-- The legs of a limit cone of a tower exhibit its point as the kernel of `1 - shift`. -/
def isLimitKernelForkOfCone {F : Tower.{u, v} (A := A)} (s : Cone F) (hs : IsLimit s) :
    IsLimit (KernelFork.ofι ((TowerAugmentation.ofCone s).productLift)
      (TowerAugmentation.productLift_oneMinusShift (TowerAugmentation.ofCone s))) := by
  let coneOfKernel (t : KernelFork (oneMinusShift F)) : Cone F :=
    { pt := t.pt
      π := NatTrans.ofOpSequence (fun n ↦ t.ι ≫ Pi.π _ n) (fun n ↦ by
        have h := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) t.condition
        simp only [Category.assoc, oneMinusShift_π, Preadditive.comp_sub, zero_comp] at h
        change 𝟙 t.pt ≫ (t.ι ≫ Pi.π _ n) =
          (t.ι ≫ Pi.π _ (n + 1)) ≫ F.map (homOfLE (Nat.le_succ n)).op
        exact (Category.id_comp _).trans
          ((sub_eq_zero.mp h).trans (Category.assoc _ _ _).symm)) }
  refine Fork.IsLimit.mk _ (fun t ↦ hs.lift (coneOfKernel t)) ?_ ?_
  · intro t
    apply Pi.hom_ext
    intro n
    have := hs.fac (coneOfKernel t) ⟨n⟩
    change (hs.lift (coneOfKernel t) ≫ Pi.lift (fun n => s.π.app ⟨n⟩)) ≫ Pi.π _ n =
      t.ι ≫ Pi.π _ n
    rw [Category.assoc, Pi.lift_π]
    exact this
  · intro t m hm
    apply hs.hom_ext
    intro n
    have h := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n.unop) hm
    have := hs.fac (coneOfKernel t) n
    change (m ≫ Pi.lift (fun n => s.π.app ⟨n⟩)) ≫ Pi.π _ n.unop =
      t.ι ≫ Pi.π _ n.unop at h
    have e : (Pi.lift fun n ↦ s.π.app (Opposite.op n)) ≫
        Pi.π (fun n ↦ F.obj (Opposite.op n)) n.unop = s.π.app n := Pi.lift_π _ _
    rw [this]
    exact (congrArg (m ≫ ·) e).symm.trans ((Category.assoc _ _ _).symm.trans h)

/-- **The sequence `0 ⟶ lim F ⟶ ∏ F ⟶ ∏ F ⟶ 0`, with second map `1 - shift`, of a tower with
epimorphic transition maps is short exact.** -/
theorem shortExact_ofCone {F : Tower.{u, v} (A := A)}
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] (s : Cone F) (hs : IsLimit s) :
    (ShortComplex.mk ((TowerAugmentation.ofCone s).productLift) (oneMinusShift F)
      (TowerAugmentation.productLift_oneMinusShift _)).ShortExact := by
  have hk := isLimitKernelForkOfCone s hs
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ hk
      mono_f := mono_of_isLimit_fork hk
      epi_g := epi_oneMinusShift F }

/-- **The augmentation of the limit of a tower with epimorphic transition maps into its Milnor
model is a quasi-isomorphism.** -/
theorem quasiIso_augmentationMap_ofCone {F : Tower.{u, v} (A := A)}
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] (s : Cone F) (hs : IsLimit s) :
    QuasiIso (TowerAugmentation.augmentationMap (TowerAugmentation.ofCone s)) := by
  have h := CochainComplex.mappingCocone.quasiIso_lift_of_shortExact (shortExact_ofCone s hs)
  unfold CochainComplex.mappingCocone.liftShortComplex at h
  unfold TowerAugmentation.augmentationMap
  exact h

end CountableMilnorTower
