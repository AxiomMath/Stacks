module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Homology.Tor.CrossProduct

/-!
# The graded Tor algebra: products on projective resolutions

Chain-level lemmas behind the graded Tor algebra: homotopies of maps into a projective
resolution, unit and associativity of a multiplication on a resolution of an algebra up to
homotopy, homology classes represented by cycles, and the compatibility of the Tor cross
product with maps of resolutions.
-/

universe u uR uA v

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped MonoidalCategory
open TorCrossProduct (extC)

private theorem homotopy_of_comp_π_eq
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : ChainComplex C ℕ} [∀ n, Projective (K.X n)]
    {M : C} (P : ProjectiveResolution M) (f g : K ⟶ P.complex)
    (h : f.f 0 ≫ P.π.f 0 = g.f 0 ≫ P.π.f 0) : Nonempty (Homotopy f g) := by
  let e := f - g
  have he : e.f 0 ≫ P.π.f 0 = 0 := by
    change (f.f 0 - g.f 0) ≫ P.π.f 0 = 0
    rw [Preadditive.sub_comp, h, sub_self]
  let s₀ := P.exact₀.liftFromProjective (e.f 0) he
  have hs₀ : s₀ ≫ P.complex.d 1 0 = e.f 0 :=
    P.exact₀.liftFromProjective_comp _ _
  have h₁ : (e.f 1 - K.d 1 0 ≫ s₀) ≫ P.complex.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hs₀, e.comm, sub_self]
  let s₁ := (P.exact_succ 0).liftFromProjective (e.f 1 - K.d 1 0 ≫ s₀) h₁
  have hs₁ : s₁ ≫ P.complex.d 2 1 = e.f 1 - K.d 1 0 ≫ s₀ :=
    (P.exact_succ 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.equivSubZero.invFun (Homotopy.mkInductive e s₀ hs₀.symm s₁ ?_ ?_)⟩
  · rw [hs₁, add_sub_cancel]
  · rintro n ⟨a, b, w⟩
    have hw : (e.f (n + 2) - K.d (n + 2) (n + 1) ≫ b) ≫
        P.complex.d (n + 2) (n + 1) = 0 := by
      simp [w]
    refine ⟨(P.exact_succ (n + 1)).liftFromProjective _ hw, ?_⟩
    rw [(P.exact_succ (n + 1)).liftFromProjective_comp, add_sub_cancel]

section

variable {R : Type u} [CommRing R]
private theorem projective_tensor (M N : ModuleCat.{max u v} R)
    [Projective M] [Projective N] : Projective (M ⊗ N) := by
  have := ModuleCat.projective_of_module_projective M
  have := ModuleCat.projective_of_module_projective N
  change Projective (ModuleCat.of R (TensorProduct R M N))
  exact ModuleCat.projective_of_categoryTheory_projective _
private theorem projective_tensor_complex_X
    (K L : ChainComplex (ModuleCat.{max u v} R) ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)] (i : ℕ) :
    Projective ((K ⊗ L).X i) := by
  classical
  constructor
  intro X Y f e he
  have h (n m : ℕ) (h : n + m = i) :
      ∃ l, l ≫ e = HomologicalComplex.ιMapBifunctor K L
        (curriedTensor _) (ComplexShape.down ℕ) n m i h ≫ f :=
    @Projective.factors _ _ _ (projective_tensor (K.X n) (L.X m)) _ _ _ e he
  choose l hl using h
  refine ⟨HomologicalComplex.mapBifunctorDesc l, ?_⟩
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n m h
  simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, hl]

private theorem epi_tensorHom {M M' N N' : ModuleCat.{max u v} R}
    (f : M ⟶ M') (g : N ⟶ N') [Epi f] [Epi g] : Epi (f ⊗ₘ g) :=
  (ModuleCat.epi_iff_surjective _).2 <| TensorProduct.map_surjective
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

private theorem tensor_zero_hom_ext
    (K L : ChainComplex (ModuleCat.{max u v} R) ℕ) {M : ModuleCat.{max u v} R}
    {f g : (K ⊗ L).X 0 ⟶ M}
    (h : HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫ f =
      HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n m hnm
  have hn : n = 0 := by change n + m = 0 at hnm; lia
  have hm : m = 0 := by change n + m = 0 at hnm; lia
  subst n m
  exact h
private theorem epi_ιTensorObj_zero
    (K L : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    Epi (HomologicalComplex.ιTensorObj K L 0 0 0 rfl) :=
  ⟨fun _ _ h ↦ tensor_zero_hom_ext K L h⟩
private theorem ιTensorObj_associator_hom
    (K L M : ChainComplex (ModuleCat.{max u v} R) ℕ) (n m k : ℕ) :
    (HomologicalComplex.ιTensorObj K L n m (n + m) rfl ▷ M.X k) ≫
      HomologicalComplex.ιTensorObj (K ⊗ L) M (n + m) k (n + m + k) rfl ≫
      (α_ K L M).hom.f (n + m + k) =
    (α_ (K.X n) (L.X m) (M.X k)).hom ≫
      (K.X n ◁ HomologicalComplex.ιTensorObj L M m k (m + k) rfl) ≫
      HomologicalComplex.ιTensorObj K (L ⊗ M) n (m + k) (n + m + k)
        (Nat.add_assoc n m k).symm := by
  have h := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat.{max u v} R)) K L M
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    n m k (n + m + k) rfl
  rwa [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor (ModuleCat.{max u v} R)) (curriedTensor (ModuleCat.{max u v} R))
    K L M (ComplexShape.down ℕ) (ComplexShape.down ℕ) n m k (n + m) (n + m + k) rfl rfl,
    HomologicalComplex.mapBifunctor₂₃.ι_eq
    (curriedTensor (ModuleCat.{max u v} R)) (curriedTensor (ModuleCat.{max u v} R))
    K L M (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    n m k (m + k) (n + m + k) rfl (Nat.add_assoc n m k).symm] at h
set_option maxHeartbeats 2000000 in
-- Elaborating tensor products of complexes involves nested monoidal instances.
lemma tensorHom_ι_apply
    {K L K' L' : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℕ) (h : p + q = n)
    (x : K.X p) (y : L.X q) :
    (f ⊗ₘ g).f n (HomologicalComplex.ιTensorObj K L p q n h (x ⊗ₜ[R] y)) =
      HomologicalComplex.ιTensorObj K' L' p q n h (f.f p x ⊗ₜ[R] g.f q y) := by
  subst n
  exact congrArg (fun t => t (x ⊗ₜ[R] y))
    (HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{max u v} R))
      (ComplexShape.down ℕ) p q (p + q) rfl)

lemma leftUnitor_inv_f_apply
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) (x : K.X n) :
    (λ_ K).inv.f n x =
      HomologicalComplex.ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{max u v} R) ℕ)) K
        0 n n (zero_add n) ((ULift.up 1) ⊗ₜ[R] x) :=
  congrArg (fun f => f x) (HomologicalComplex.leftUnitor'_inv K n)

lemma rightUnitor_inv_f_apply
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) (x : K.X n) :
    (ρ_ K).inv.f n x =
      HomologicalComplex.ιTensorObj K (𝟙_ (ChainComplex (ModuleCat.{max u v} R) ℕ))
        n 0 n (add_zero n) (x ⊗ₜ[R] (ULift.up 1)) :=
  congrArg (fun f => f x) (HomologicalComplex.rightUnitor'_inv K n)

set_option maxHeartbeats 1000000 in
-- The three tensor factors and their summand maps require additional elaboration.
lemma associator_ι_apply
    (K L M : ChainComplex (ModuleCat.{max u v} R) ℕ) (p q r : ℕ)
    (x : K.X p) (y : L.X q) (z : M.X r) :
    (α_ K L M).hom.f (p + q + r)
      (HomologicalComplex.ιTensorObj (K ⊗ L) M (p+q) r (p+q+r) rfl
        (HomologicalComplex.ιTensorObj K L p q (p+q) rfl (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      HomologicalComplex.ιTensorObj K (L ⊗ M) p (q+r) (p+q+r) (Nat.add_assoc p q r).symm
        (x ⊗ₜ[R] HomologicalComplex.ιTensorObj L M q r (q+r) rfl (y ⊗ₜ[R] z)) :=
  congrArg (fun f => f ((x ⊗ₜ[R] y) ⊗ₜ[R] z))
    (ιTensorObj_associator_hom K L M p q r)

set_option maxHeartbeats 2000000 in
-- Elaborating the triple tensor comparison requires additional reductions.
theorem resolution_mul_assoc
    (B : AlgCat.{max u v, u} R)
    (P : ProjectiveResolution (ModuleCat.of R B))
    (μ : P.complex ⊗ P.complex ⟶ P.complex)
    (hμ : ∀ (x y : P.complex.X 0),
      P.π.f 0 (μ.f 0 (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl
        (TensorProduct.tmul R x y))) = @HMul.hMul B B B inferInstance (P.π.f 0 x) (P.π.f 0 y)) :
    Nonempty (Homotopy ((μ ⊗ₘ 𝟙 P.complex) ≫ μ)
      ((α_ P.complex P.complex P.complex).hom ≫ (𝟙 P.complex ⊗ₘ μ) ≫ μ)) := by
  have (n : ℕ) : Projective ((P.complex ⊗ P.complex).X n) :=
    projective_tensor_complex_X.{u, v} P.complex P.complex n
  have (n : ℕ) : Projective (((P.complex ⊗ P.complex) ⊗ P.complex).X n) :=
    projective_tensor_complex_X.{u, v} (P.complex ⊗ P.complex) P.complex n
  apply homotopy_of_comp_π_eq P
  apply tensor_zero_hom_ext
  have : Epi (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl) :=
    epi_ιTensorObj_zero P.complex P.complex
  have : Epi (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl ▷ P.complex.X 0) :=
    epi_tensorHom _ (𝟙 _)
  rw [← cancel_epi (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl ▷ P.complex.X 0)]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change P.π.f 0 (μ.f 0 ((μ ⊗ₘ 𝟙 P.complex).f 0
    (HomologicalComplex.ιTensorObj (P.complex ⊗ P.complex) P.complex 0 0 0 rfl
      (TensorProduct.tmul R (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl
        (TensorProduct.tmul R x y)) z)))) = _
  rw [tensorHom_ι_apply μ (𝟙 P.complex) 0 0 0 rfl _ _, hμ, hμ]
  change @HMul.hMul B B B inferInstance
    (@HMul.hMul B B B inferInstance (P.π.f 0 x) (P.π.f 0 y)) (P.π.f 0 z) =
    P.π.f 0 (μ.f 0 ((𝟙 P.complex ⊗ₘ μ).f 0
      ((α_ P.complex P.complex P.complex).hom.f 0
        (HomologicalComplex.ιTensorObj (P.complex ⊗ P.complex) P.complex 0 0 0 rfl
          (TensorProduct.tmul R (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl
            (TensorProduct.tmul R x y)) z)))))
  rw [associator_ι_apply P.complex P.complex P.complex 0 0 0,
    tensorHom_ι_apply (𝟙 P.complex) μ 0 0 0 rfl _ _, hμ, hμ]
  exact mul_assoc _ _ _

set_option maxHeartbeats 2000000 in
-- Tensor products of complexes require additional reductions.
theorem resolution_one_mul
    (B : AlgCat.{max u v, u} R)
    (P : ProjectiveResolution (ModuleCat.of R B))
    (μ : P.complex ⊗ P.complex ⟶ P.complex)
    (hμ : ∀ (x y : P.complex.X 0),
      P.π.f 0 (μ.f 0 (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl
        (TensorProduct.tmul R x y))) = @HMul.hMul B B B inferInstance (P.π.f 0 x) (P.π.f 0 y))
    (η : 𝟙_ (ChainComplex (ModuleCat.{max u v} R) ℕ) ⟶ P.complex)
    (hη : P.π.f 0 (η.f 0 (ULift.up 1)) = (1 : B)) :
    Nonempty (Homotopy ((λ_ P.complex).inv ≫ (η ⊗ₘ 𝟙 P.complex) ≫ μ) (𝟙 P.complex)) := by
  apply homotopy_of_comp_π_eq P
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change P.π.f 0 (μ.f 0 ((η ⊗ₘ 𝟙 P.complex).f 0 ((λ_ P.complex).inv.f 0 x))) = P.π.f 0 x
  erw [leftUnitor_inv_f_apply, tensorHom_ι_apply η (𝟙 P.complex) 0 0 0 rfl _ _, hμ, hη]
  exact one_mul (M := B) (P.π.f 0 x)

theorem resolution_unit_exists
    (B : AlgCat.{max u v, u} R)
    (P : ProjectiveResolution (ModuleCat.of R B)) :
    ∃ η : 𝟙_ (ChainComplex (ModuleCat.{max u v} R) ℕ) ⟶ P.complex,
      P.π.f 0 (η.f 0 (ULift.up 1)) = (1 : B) := by
  obtain ⟨e, he⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance (1 : B)
  let η₀ : ModuleCat.of R (ULift.{v} R) ⟶ P.complex.X 0 :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton R _ e).comp ULift.moduleEquiv.toLinearMap)
  refine ⟨(P.complex.fromSingle₀Equiv _).symm η₀, ?_⟩
  change P.π.f 0 ((1 : R) • e) = (1 : B)
  simpa only [one_smul] using he

set_option maxHeartbeats 2000000 in
-- Tensor products of complexes require additional reductions.
theorem resolution_mul_one
    (B : AlgCat.{max u v, u} R)
    (P : ProjectiveResolution (ModuleCat.of R B))
    (μ : P.complex ⊗ P.complex ⟶ P.complex)
    (hμ : ∀ (x y : P.complex.X 0),
      P.π.f 0 (μ.f 0 (HomologicalComplex.ιTensorObj P.complex P.complex 0 0 0 rfl
        (TensorProduct.tmul R x y))) = @HMul.hMul B B B inferInstance (P.π.f 0 x) (P.π.f 0 y))
    (η : 𝟙_ (ChainComplex (ModuleCat.{max u v} R) ℕ) ⟶ P.complex)
    (hη : P.π.f 0 (η.f 0 (ULift.up 1)) = (1 : B)) :
    Nonempty (Homotopy ((ρ_ P.complex).inv ≫ (𝟙 P.complex ⊗ₘ η) ≫ μ) (𝟙 P.complex)) := by
  apply homotopy_of_comp_π_eq P
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change P.π.f 0 (μ.f 0 ((𝟙 P.complex ⊗ₘ η).f 0 ((ρ_ P.complex).inv.f 0 x))) = P.π.f 0 x
  erw [rightUnitor_inv_f_apply, tensorHom_ι_apply (𝟙 P.complex) η 0 0 0 rfl _ _, hμ, hη]
  exact mul_one (M := B) (P.π.f 0 x)


def homologyRep (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (n : ℕ) (a : K.homology n) (x : K.X n) : Prop :=
  ∃ z : K.cycles n, K.iCycles n z = x ∧ K.homologyπ n z = a

lemma homologyRep_exists (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (n : ℕ) (a : K.homology n) : ∃ x, homologyRep K n a x := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a
  exact ⟨K.iCycles n z, z, rfl, hz⟩

lemma homologyRep_eq {K : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {n : ℕ} {a b : K.homology n} {x : K.X n}
    (ha : homologyRep K n a x) (hb : homologyRep K n b x) : a = b := by
  obtain ⟨z, hz, ha⟩ := ha
  obtain ⟨w, hw, hb⟩ := hb
  have h := (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance (hz.trans hw.symm)
  exact ha.symm.trans ((congrArg (K.homologyπ n) h).trans hb)

lemma homologyRep_d {K : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {n : ℕ} {a : K.homology n} {x : K.X n}
    (ha : homologyRep K n a x) (j : ℕ) : K.d n j x = 0 := by
  obtain ⟨z, rfl, _⟩ := ha
  exact congrArg (fun f => f z) (K.iCycles_d n j)

lemma homologyRep_of_cycle {K : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {n : ℕ} (x : K.X n) (hx : K.d n ((ComplexShape.down ℕ).next n) x = 0) :
    ∃ a, homologyRep K n a x := by
  let z := K.cyclesMk x _ rfl hx
  exact ⟨K.homologyπ n z, z, HomologicalComplex.i_cyclesMk K x _ rfl hx, rfl⟩

lemma homologyRep_map {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ L) {n : ℕ} {a : K.homology n} {x : K.X n}
    (ha : homologyRep K n a x) :
    homologyRep L n (HomologicalComplex.homologyMap f n a) (f.f n x) := by
  obtain ⟨z, rfl, rfl⟩ := ha
  refine ⟨HomologicalComplex.cyclesMap f n z, ?_, ?_⟩
  · exact congrArg (fun f => f z) (HomologicalComplex.cyclesMap_i f n)
  · exact (congrArg (fun f => f z) (HomologicalComplex.homologyπ_naturality f n)).symm

private lemma homologyRep_cast {K : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {n m : ℕ} (h : n = m) {a : K.homology n} {x : K.X n}
    (ha : homologyRep K n a x) :
    homologyRep K m
      (cast (congrArg (fun i => (K.homology i : Type (max u v))) h) a)
      (cast (congrArg (fun i => (K.X i : Type (max u v))) h) x) := by
  subst m
  exact ha

-- The cycle formula compares the lifted tensor bifunctor to the monoidal tensor.
set_option backward.isDefEq.respectTransparency false in
lemma homologyRep_product {S : Type uA} [CommRing S]
    {K L : ChainComplex (ModuleCat.{max uR uA v} S) ℕ}
    {n m : ℕ} (c : TorCrossProduct.ChainHomologyProduct.{uR, uA, v} S K L n m)
    {a : K.homology n} {x : K.X n} {b : L.homology m} {y : L.X m}
    (ha : homologyRep.{uA, max uR v} K n a x) (hb : homologyRep.{uA, max uR v} L m b y) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} S) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    homologyRep.{uA, max uR v} (K ⊗ L) (n + m) (c.map (a ⊗ₜ[S] b))
      (HomologicalComplex.ιTensorObj K L n m (n + m) rfl (x ⊗ₜ[S] y)) := by
  let : MonoidalCategory (ModuleCat.{max uR uA v} S) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  obtain ⟨z, rfl, rfl⟩ := ha
  obtain ⟨w, rfl, rfl⟩ := hb
  obtain ⟨t, ht, hc⟩ := c.maps_cycles
  refine ⟨t (z ⊗ₜ[S] w), ?_, ?_⟩
  · exact congrArg (fun f => f (z ⊗ₜ[S] w)) ht
  · exact (congrArg (fun f => f (z ⊗ₜ[S] w)) hc).symm

lemma homologyRep_homotopy {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {f g : K ⟶ L} (H : Homotopy f g) {n : ℕ} {a b : L.homology n}
    (x : K.X n) (hx : K.d n ((ComplexShape.down ℕ).next n) x = 0)
    (ha : homologyRep L n a (f.f n x)) (hb : homologyRep L n b (g.f n x)) : a = b := by
  obtain ⟨c, hc⟩ := homologyRep_of_cycle x hx
  calc
    a = HomologicalComplex.homologyMap f n c := homologyRep_eq ha (homologyRep_map f hc)
    _ = HomologicalComplex.homologyMap g n c := congrArg (fun t => t c) (H.homologyMap_eq n)
    _ = b := homologyRep_eq (homologyRep_map g hc) hb
-- The tensor differential is checked on one homogeneous summand.
set_option backward.isDefEq.respectTransparency false in
private lemma tensor_cycles_d
    (K L : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (p q n j : ℕ) (h : p + q = n) :
    (K.iCycles p ⊗ₘ L.iCycles q) ≫
      HomologicalComplex.ιTensorObj K L p q n h ≫ (K ⊗ L).d n j = 0 := by
  erw [HomologicalComplex.mapBifunctor.d_eq K L,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂, Preadditive.comp_add]
  have h₁ : (K.iCycles p ⊗ₘ L.iCycles q) ≫
      HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor _) (ComplexShape.down ℕ) p q j = 0 := by
    cases p with
    | zero =>
      rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), comp_zero]
    | succ p =>
      rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _
        (show (ComplexShape.down ℕ).Rel (p+1) p from rfl),
        Linear.comp_units_smul, ← Category.assoc]
      change _ • (((K.iCycles (p+1) ⊗ₘ L.iCycles q) ≫ (K.d (p+1) p ▷ L.X q)) ≫ _) = 0
      rw [← tensorHom_id, tensorHom_comp_tensorHom, K.iCycles_d, MonoidalPreadditive.zero_tensor,
        zero_comp, smul_zero]
  have h₂ : (K.iCycles p ⊗ₘ L.iCycles q) ≫
      HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor _) (ComplexShape.down ℕ) p q j = 0 := by
    cases q with
    | zero =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp), comp_zero]
    | succ q =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p
        (show (ComplexShape.down ℕ).Rel (q+1) q from rfl),
        Linear.comp_units_smul, ← Category.assoc]
      change _ • (((K.iCycles p ⊗ₘ L.iCycles (q+1)) ≫ (K.X p ◁ L.d (q+1) q)) ≫ _) = 0
      rw [← id_tensorHom, tensorHom_comp_tensorHom, L.iCycles_d, MonoidalPreadditive.tensor_zero,
        zero_comp, smul_zero]
  rw [h₁, h₂, add_zero]

lemma homologyRep_tensor_cycle
    {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    {p q : ℕ} {a : K.homology p} {b : L.homology q} {x : K.X p} {y : L.X q}
    (hx : homologyRep K p a x) (hy : homologyRep L q b y) (n j : ℕ) (h : p + q = n) :
    (K ⊗ L).d n j (HomologicalComplex.ιTensorObj K L p q n h (x ⊗ₜ[R] y)) = 0 := by
  obtain ⟨x, rfl, _⟩ := hx
  obtain ⟨y, rfl, _⟩ := hy
  exact congrArg (fun f => f (x ⊗ₜ[R] y)) (tensor_cycles_d K L p q n j h)

private theorem moduleTensorMap_eq {M M' N N' : ModuleCat.{max u v} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    TorCrossProduct.moduleTensorMap.{v, u, v} f g = f ⊗ₘ g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl
set_option maxHeartbeats 2000000 in
-- Comparing the homology maps unfolds nested tensor-complex constructions.
set_option backward.isDefEq.respectTransparency false in
private theorem homologyProduct_naturality
    {K L K' L' : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n m : ℕ)
    (c : TorCrossProduct.ChainHomologyProduct.{v, u, v} R K L n m)
    (d : TorCrossProduct.ChainHomologyProduct.{v, u, v} R K' L' n m) :
    c.map ≫ HomologicalComplex.homologyMap (f ⊗ₘ g) (n + m) =
      (HomologicalComplex.homologyMap f n ⊗ₘ HomologicalComplex.homologyMap g m) ≫ d.map := by
  obtain ⟨z, hz, hc⟩ := c.maps_cycles
  obtain ⟨z', hz', hd⟩ := d.maps_cycles
  simp only [moduleTensorMap_eq] at hz hc hz' hd
  let cm : K.homology n ⊗ L.homology m ⟶ (K ⊗ L).homology (n + m) := c.map
  let dm : K'.homology n ⊗ L'.homology m ⟶ (K' ⊗ L').homology (n + m) := d.map
  change K.cycles n ⊗ L.cycles m ⟶ (K ⊗ L).cycles (n + m) at z
  change K'.cycles n ⊗ L'.cycles m ⟶ (K' ⊗ L').cycles (n + m) at z'
  change z ≫ (K ⊗ L).iCycles (n + m) = (K.iCycles n ⊗ₘ L.iCycles m) ≫
    HomologicalComplex.ιTensorObj K L n m (n + m) rfl at hz
  change z' ≫ (K' ⊗ L').iCycles (n + m) = (K'.iCycles n ⊗ₘ L'.iCycles m) ≫
    HomologicalComplex.ιTensorObj K' L' n m (n + m) rfl at hz'
  change (K.homologyπ n ⊗ₘ L.homologyπ m) ≫ cm = z ≫ (K ⊗ L).homologyπ (n + m) at hc
  change (K'.homologyπ n ⊗ₘ L'.homologyπ m) ≫ dm = z' ≫ (K' ⊗ L').homologyπ (n + m) at hd
  change cm ≫ _ = _ ≫ dm
  have hi : z ≫ HomologicalComplex.cyclesMap (f ⊗ₘ g) (n + m) =
      (HomologicalComplex.cyclesMap f n ⊗ₘ HomologicalComplex.cyclesMap g m) ≫ z' := by
    rw [← cancel_mono ((K' ⊗ L').iCycles (n + m))]
    have ht : HomologicalComplex.ιTensorObj K L n m (n + m) rfl ≫ (f ⊗ₘ g).f (n + m) =
        (f.f n ⊗ₘ g.f m) ≫ HomologicalComplex.ιTensorObj K' L' n m (n + m) rfl := by
      rw [MonoidalCategory.tensorHom_def (f.f n) (g.f m), Category.assoc]
      exact HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{max u v} R))
          (ComplexShape.down ℕ) n m (n + m) rfl
    calc
      (z ≫ HomologicalComplex.cyclesMap (f ⊗ₘ g) (n + m)) ≫ (K' ⊗ L').iCycles (n + m) =
        ((K.iCycles n ⊗ₘ L.iCycles m) ≫ (f.f n ⊗ₘ g.f m)) ≫
          HomologicalComplex.ιTensorObj K' L' n m (n + m) rfl := by
            rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
              hz, Category.assoc, ht, ← Category.assoc]
      _ = ((HomologicalComplex.cyclesMap f n ⊗ₘ HomologicalComplex.cyclesMap g m) ≫
          (K'.iCycles n ⊗ₘ L'.iCycles m)) ≫
          HomologicalComplex.ιTensorObj K' L' n m (n + m) rfl := by
            rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
              HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i]
      _ = _ := by rw [Category.assoc, ← hz', ← Category.assoc]
  have : Epi (K.homologyπ n ⊗ₘ L.homologyπ m) := epi_tensorHom _ _
  rw [← cancel_epi (K.homologyπ n ⊗ₘ L.homologyπ m)]
  simp only [← Category.assoc, hc]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hi,
    Category.assoc, ← hd]
  simp only [← Category.assoc, tensorHom_comp_tensorHom,
    HomologicalComplex.homologyπ_naturality]

private theorem product_comp_map_resolution
    (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [Algebra R A]
    (n m : ℕ) (M N Z : ModuleCat.{max uR uA v} R)
    (q : (RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, N) ⟶ Z)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution
      ((RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, N)))
    (U : ProjectiveResolution Z)
    (c : TorCrossProduct.ResolutionModel.{uR, uA, v} R A (algebraMap R A) n m
      (RingTheory.TorProducts.torProduct.{uR, uA, v} R A n m) M N P Q T) :
    (RingTheory.TorProducts.torProduct.{uR, uA, v} R A n m).app (M, N) ≫
      (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A (n + m)).map q ≫
      (U.isoLeftDerivedObj (extensionScalars (algebraMap R A)) (n + m)).hom =
    TorCrossProduct.moduleTensorMap.{uR, uA, v}
      (P.isoLeftDerivedObj (extensionScalars (algebraMap R A)) n).hom
      (Q.isoLeftDerivedObj (extensionScalars (algebraMap R A)) m).hom ≫
      c.cohomologyProduct.map ≫ HomologicalComplex.homologyMap
        (c.baseChange ≫
          ((extensionScalars.{uR, uA, v} (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (c.μ ≫ ProjectiveResolution.lift q T U)) (n + m) := by
  rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality q T U
    (ProjectiveResolution.lift q T U) (ProjectiveResolution.lift_commutes_zero q T U)]
  change (RingTheory.TorProducts.torProduct R A n m).app (M, N) ≫
    (T.isoLeftDerivedObj _ (n + m)).hom ≫
      HomologicalComplex.homologyMap
        (((extensionScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (ProjectiveResolution.lift q T U)) (n + m) = _
  erw [← Category.assoc, c.product_eq]
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  erw [Category.assoc, Category.assoc, Category.assoc]


-- Comparing the total tensor products requires additional reductions.
set_option backward.isDefEq.respectTransparency false in
theorem product_comp_map_resolution_of_normalized
    (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [Algebra R A]
    (n m : ℕ) (M N Z : ModuleCat.{max uR uA v} R)
    (q : (RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, N) ⟶ Z)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution
      ((RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, N)))
    (U : ProjectiveResolution Z)
    (c : TorCrossProduct.ResolutionModel.{uR, uA, v} R A (algebraMap R A) n m
      (RingTheory.TorProducts.torProduct.{uR, uA, v} R A n m) M N P Q T)
    (ν : TorCrossProduct.chainTensor.{uA, uR, v} P.complex Q.complex ⟶ U.complex)
    (hν : HomologicalComplex.ιMapBifunctor P.complex Q.complex
      (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
      ν.f 0 ≫ U.π.f 0 = TorCrossProduct.moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0) ≫ q) :
    (RingTheory.TorProducts.torProduct.{uR, uA, v} R A n m).app (M, N) ≫
      (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A (n + m)).map q ≫
      (U.isoLeftDerivedObj (extensionScalars (algebraMap R A)) (n + m)).hom =
    TorCrossProduct.moduleTensorMap.{uR, uA, v}
      (P.isoLeftDerivedObj (extensionScalars (algebraMap R A)) n).hom
      (Q.isoLeftDerivedObj (extensionScalars (algebraMap R A)) m).hom ≫
      c.cohomologyProduct.map ≫ HomologicalComplex.homologyMap
        (c.baseChange ≫
          ((extensionScalars.{uR, uA, v} (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map ν) (n + m) := by
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  have (i : ℕ) : Projective ((TorCrossProduct.chainTensor.{uA, uR, v} P.complex Q.complex).X i) :=
    projective_tensor_complex_X.{uR, max uA v} P.complex Q.complex i
  obtain ⟨h⟩ := homotopy_of_comp_π_eq U
    (c.μ ≫ ProjectiveResolution.lift q T U) ν (by
      apply tensor_zero_hom_ext.{uR, max uA v}
      change HomologicalComplex.ιMapBifunctor P.complex Q.complex
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
        (c.μ.f 0 ≫ (ProjectiveResolution.lift q T U).f 0) ≫ U.π.f 0 =
        HomologicalComplex.ιMapBifunctor P.complex Q.complex
          (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
          ν.f 0 ≫ U.π.f 0
      calc
        _ = (HomologicalComplex.ιMapBifunctor P.complex Q.complex
          (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
          c.μ.f 0 ≫ T.π.f 0) ≫ q := by
            simp only [Category.assoc, ProjectiveResolution.lift_commutes_zero]
        _ = TorCrossProduct.moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0) ≫ q :=
          congrArg (fun t => t ≫ q) c.μ_zero
        _ = _ := hν.symm)
  rw [product_comp_map_resolution.{uR, uA, v} R A n m M N Z q P Q T U c]
  congr 2
  exact (((extensionScalars (algebraMap R A)).mapHomotopy h).compLeft
    c.baseChange).homologyMap_eq (n + m)

end

end
