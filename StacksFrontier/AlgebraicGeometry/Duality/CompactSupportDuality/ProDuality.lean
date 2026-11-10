module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.Topology.Algebra.Module.DualLimitTopology
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.OpenImmersionCovariance

/-!
# Duality between a pro-object and its functor of points

Let `𝒟` be a `k`-linear category over a field `k`, let `A` and `ω` be objects of `𝒟` and let
`t : Hom(A, ω) ⟶ k` be a linear form. For a pro-object `P` of `𝒟` with countable index and
functor of points `L ↦ colim_n Hom(M_n, L)`, a morphism `y` from the constant pro-object at `A`
to `P` and a point `x` of `P` at `ω` pair to `t(y(x)) ∈ k`. This file shows that the pairing
identifies `Hom_{Pro}(A, P)` with the `k`-linear dual of the points of `P` at `ω`, as soon as for
every `n` the composition pairing `Hom(A, M_n) × Hom(M_n, ω) ⟶ k`, `(a, g) ↦ t(a ≫ g)`, is perfect
and `Hom(A, M_n)` is finite dimensional:
`Hom_{Pro}(A, P) = lim_n Hom(A, M_n) = lim_n Hom(M_n, ω)^∨ = (colim_n Hom(M_n, ω))^∨`.

## Main definitions

* `CategoryTheory.ProSeq.constHomValue`: the value `y(x) : A ⟶ N` of a morphism
  `y : A ⟶ P` of pro-objects at a point `x` of `P` at `N`.
* The `k`-module structure on `A ⟶ P` (`CategoryTheory.ProSeq.instModuleConstHom`), computed
  pointwise in the values.
* `CategoryTheory.ProSeq.dualPairingMap`: the linear map `Hom_{Pro}(A, P) ⟶ V^∨` of the pairing,
  for a module `V` identified with the points of `P` at `ω`.

## Main results

* `CategoryTheory.ProSeq.bijective_dualPairingMap`: the pairing is perfect under the hypotheses
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.ProSeq

variable {𝒟 : Type u} [Category.{v} 𝒟]

section Value

variable {A : 𝒟} {P : ProSeq 𝒟}

/-- The value `y(x) : A ⟶ N` of a morphism `y` from the constant pro-object at `A` to `P` at a
point `x` of `P` at `N`: the morphisms `A ⟶ P` of pro-objects are the natural transformations from
the functor of points of `P` to `Hom(A, -)`. -/
public abbrev constHomValue (y : const.obj A ⟶ P) {N : 𝒟} (x : P.points.obj N) : A ⟶ N :=
  y.unop.hom.app N x

/-- The values of a morphism out of a constant pro-object are natural in the target. -/
public lemma constHomValue_map (y : const.obj A ⟶ P) {N N' : 𝒟} (g : N ⟶ N')
    (x : P.points.obj N) : constHomValue y (P.points.map g x) = constHomValue y x ≫ g :=
  ConcreteCategory.congr_hom (y.unop.hom.naturality g) x

/-- Composing with a morphism of pro-objects acts on values through the functors of points. -/
public lemma constHomValue_comp {P' : ProSeq 𝒟} (y : const.obj A ⟶ P) (f : P ⟶ P') {N : 𝒟}
    (x : P'.points.obj N) : constHomValue (y ≫ f) x = constHomValue y (f.unop.hom.app N x) :=
  rfl

/-- A morphism out of a constant pro-object is determined by its values. -/
public lemma constHom_ext_value {y y' : const.obj A ⟶ P}
    (h : ∀ (N : 𝒟) (x : P.points.obj N), constHomValue y x = constHomValue y' x) : y = y' := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext N x
  exact h N x

/-- The natural families of values: those `f_N : P(N) ⟶ Hom(A, N)` with
`f_{N'}(P(g) x) = f_N(x) ≫ g`. -/
public def IsNaturalValues (f : ∀ N : 𝒟, P.points.obj N → (A ⟶ N)) : Prop :=
  ∀ ⦃N N' : 𝒟⦄ (g : N ⟶ N') (x : P.points.obj N), f N' (P.points.map g x) = f N x ≫ g

/-- The morphism of pro-objects with given natural values. -/
public def constHomOfValues (f : ∀ N : 𝒟, P.points.obj N → (A ⟶ N)) (hf : IsNaturalValues f) :
    const.obj A ⟶ P :=
  (ObjectProperty.homMk (X := P.unop) (Y := (const.obj A).unop)
    { app := fun N => TypeCat.ofHom (f N)
      naturality := fun N N' g => by ext x; exact hf g x }).op

/-- The values of `CategoryTheory.ProSeq.constHomOfValues`. -/
public lemma constHomValue_constHomOfValues (f : ∀ N : 𝒟, P.points.obj N → (A ⟶ N))
    (hf : IsNaturalValues f) {N : 𝒟} (x : P.points.obj N) :
    constHomValue (constHomOfValues f hf) x = f N x :=
  rfl

/-- Morphisms out of a constant pro-object are the natural families of values. -/
public def constHomEquivValues :
    (const.obj A ⟶ P) ≃ {f : ∀ N : 𝒟, P.points.obj N → (A ⟶ N) // IsNaturalValues f} where
  toFun y := ⟨fun _ x => constHomValue y x, fun _ _ g x => constHomValue_map y g x⟩
  invFun f := constHomOfValues f.1 f.2
  left_inv _ := constHom_ext_value fun _ _ => rfl
  right_inv _ := rfl

end Value

section Linear

variable [Preadditive 𝒟] {A : 𝒟} {P : ProSeq 𝒟}

/-- The family of values of a morphism out of a constant pro-object. -/
public abbrev constHomValues (y : const.obj A ⟶ P) : ∀ N : 𝒟, P.points.obj N → (A ⟶ N) :=
  fun _ x => constHomValue y x

omit [Preadditive 𝒟] in
/-- A morphism out of a constant pro-object is determined by its family of values. -/
public lemma constHomValues_injective :
    Function.Injective (constHomValues (A := A) (P := P)) := fun _ _ h =>
  constHom_ext_value fun N x => congrFun (congrFun h N) x

/-- The zero morphism out of a constant pro-object, with every value zero. -/
public instance : Zero (const.obj A ⟶ P) :=
  ⟨constHomOfValues (fun _ _ => 0) fun _ _ _ _ => by simp⟩

/-- The sum of two morphisms out of a constant pro-object, computed on values. -/
public instance : Add (const.obj A ⟶ P) :=
  ⟨fun y y' => constHomOfValues (fun _ x => constHomValue y x + constHomValue y' x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, constHomValue_map, Preadditive.add_comp]⟩

/-- The negative of a morphism out of a constant pro-object, computed on values. -/
public instance : Neg (const.obj A ⟶ P) :=
  ⟨fun y => constHomOfValues (fun _ x => -constHomValue y x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, Preadditive.neg_comp]⟩

/-- The difference of two morphisms out of a constant pro-object, computed on values. -/
public instance : Sub (const.obj A ⟶ P) :=
  ⟨fun y y' => constHomOfValues (fun _ x => constHomValue y x - constHomValue y' x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, constHomValue_map, Preadditive.sub_comp]⟩

/-- Natural-number multiples of a morphism out of a constant pro-object, computed on values. -/
public instance : SMul ℕ (const.obj A ⟶ P) :=
  ⟨fun n y => constHomOfValues (fun _ x => n • constHomValue y x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, Preadditive.nsmul_comp]⟩

/-- Integer multiples of a morphism out of a constant pro-object, computed on values. -/
public instance : SMul ℤ (const.obj A ⟶ P) :=
  ⟨fun n y => constHomOfValues (fun _ x => n • constHomValue y x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, Preadditive.zsmul_comp]⟩

/-- **The additive group of morphisms from a constant pro-object**, computed on values: `y + y'`
has values `y(x) + y'(x)`. -/
public instance instAddCommGroupConstHom : AddCommGroup (const.obj A ⟶ P) :=
  constHomValues_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Values of a sum. -/
@[simp]
public lemma constHomValue_add (y y' : const.obj A ⟶ P) {N : 𝒟} (x : P.points.obj N) :
    constHomValue (y + y') x = constHomValue y x + constHomValue y' x :=
  rfl

/-- Values of zero. -/
@[simp]
public lemma constHomValue_zero {N : 𝒟} (x : P.points.obj N) :
    constHomValue (0 : const.obj A ⟶ P) x = 0 :=
  rfl

variable {k : Type w} [Field k] [Linear k 𝒟]

/-- Scalar multiples of a morphism out of a constant pro-object, computed on values. -/
public instance : SMul k (const.obj A ⟶ P) :=
  ⟨fun c y => constHomOfValues (fun _ x => c • constHomValue y x)
    fun _ _ g x => by dsimp only; rw [constHomValue_map, Linear.smul_comp]⟩

/-- **The `k`-module of morphisms from a constant pro-object**, computed on values. -/
public instance instModuleConstHom : Module k (const.obj A ⟶ P) :=
  constHomValues_injective.module k
    ⟨⟨constHomValues, rfl⟩, fun _ _ => rfl⟩ (fun _ _ => rfl)

/-- Values of a scalar multiple. -/
@[simp]
public lemma constHomValue_smul (c : k) (y : const.obj A ⟶ P) {N : 𝒟} (x : P.points.obj N) :
    constHomValue (c • y) x = c • constHomValue y x :=
  rfl

/-- Composition with a morphism of pro-objects is `k`-linear. -/
public def compLinearMap {P' : ProSeq 𝒟} (f : P ⟶ P') :
    (const.obj A ⟶ P) →ₗ[k] (const.obj A ⟶ P') where
  toFun y := y ≫ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Linear

section Duality

variable {k : Type w} [Field k] [Preadditive 𝒟] [Linear k 𝒟] {A ω : 𝒟} (t : (A ⟶ ω) →ₗ[k] k)

/-- The composition pairing `Hom(N, ω) ⟶ Hom(A, N)^∨`, `g ↦ (a ↦ t(a ≫ g))`. -/
public def compPairing (N : 𝒟) : (N ⟶ ω) →ₗ[k] Module.Dual k (A ⟶ N) where
  toFun g :=
    { toFun := fun a => t (a ≫ g)
      map_add' := fun a a' => by rw [Preadditive.add_comp, map_add]
      map_smul' := fun c a => by rw [Linear.smul_comp, map_smul]; rfl }
  map_add' g g' := by ext a; simp [Preadditive.comp_add]
  map_smul' c g := by ext a; simp [Linear.comp_smul]

/-- The composition pairing sends `g : N ⟶ ω` and `a : A ⟶ N` to `t(a ≫ g)`. -/
@[simp]
public lemma compPairing_apply_apply {N : 𝒟} (g : N ⟶ ω) (a : A ⟶ N) :
    compPairing t N g a = t (a ≫ g) :=
  rfl

/-- Postcomposition with an isomorphism, as a `k`-linear equivalence of morphism spaces. -/
public def postcompLinearEquiv {N₁ N₂ : 𝒟} (e : N₁ ≅ N₂) : (A ⟶ N₁) ≃ₗ[k] (A ⟶ N₂) where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' _ _ := Linear.smul_comp _ _ _ _ _ _
  left_inv a := by simp
  right_inv b := by simp

/-- The perfectness of the composition pairing only depends on the isomorphism class of the
object. -/
public lemma bijective_compPairing_of_iso {N₁ N₂ : 𝒟} (e : N₁ ≅ N₂)
    (h : Function.Bijective (compPairing t N₁)) : Function.Bijective (compPairing t N₂) := by
  have hc : (compPairing t N₂ : (N₂ ⟶ ω) → Module.Dual k (A ⟶ N₂)) =
      (postcompLinearEquiv e.symm).dualMap ∘ compPairing t N₁ ∘ (e.hom ≫ ·) := by
    funext g
    ext a
    simp [postcompLinearEquiv, LinearEquiv.dualMap_apply]
  rw [hc]
  refine (postcompLinearEquiv e.symm).dualMap.bijective.comp (h.comp ?_)
  exact ⟨fun g g' hg => (cancel_epi e.hom).1 hg, fun g => ⟨e.inv ≫ g, by simp⟩⟩

variable {M : ℕᵒᵖ ⥤ 𝒟} {P : ProSeq 𝒟} (e : P ≅ of M) {V : Type*} [AddCommGroup V] [Module k V]
  (ρ : V ≃ P.points.obj ω) (ι : ∀ n : ℕ, (M.obj (op n) ⟶ ω) →ₗ[k] V)
  (hι : ∀ (n : ℕ) (g : M.obj (op n) ⟶ ω),
    ρ (ι n g) = e.hom.unop.hom.app ω ((Pro.seqHomColimIso M).inv.app ω (Pro.seqStage M g)))

include hι in
/-- The value of a morphism at the point of `P` attached to `g : M_n ⟶ ω`. -/
public lemma constHomValue_ι (y : const.obj A ⟶ P) {n : ℕ} (g : M.obj (op n) ⟶ ω) :
    constHomValue y (ρ (ι n g)) = constHomComponent (y ≫ e.hom) n ≫ g := by
  rw [hι]
  exact constHom_app_seqStage (y ≫ e.hom) g

include hι in
/-- The points attached to `g` and to `g` precomposed with a transition agree. -/
public lemma ι_tr {n m : ℕ} (h : n ≤ m) (g : M.obj (op n) ⟶ ω) :
    ι m (InverseSequence.tr M h ≫ g) = ι n g :=
  ρ.injective (by rw [hι, hι, Pro.seqStage_transition])

include hι in
/-- Every element of `V` is attached to a morphism `M_n ⟶ ω`. -/
public lemma exists_ι (v : V) : ∃ (n : ℕ) (g : M.obj (op n) ⟶ ω), v = ι n g := by
  let z : (Pro.coyonedaColim (Pro.liftedInverseSequence M)).obj ω := e.inv.unop.hom.app ω (ρ v)
  have hz : (Pro.seqHomColimIso M).inv.app ω ((Pro.seqHomColimIso M).hom.app ω z) = z :=
    Iso.hom_inv_id_app_apply (Pro.seqHomColimIso M) ω z
  obtain ⟨n, g, hg⟩ := Pro.seqStage_surjective M ω ((Pro.seqHomColimIso M).hom.app ω z)
  refine ⟨n, g, ρ.injective ?_⟩
  rw [hι, ← hg, hz]
  have h : (e.hom ≫ e.inv).unop.hom.app ω (ρ v) = ρ v := by rw [e.hom_inv_id]; rfl
  exact h.symm

/-- The pairing `⟨y, v⟩ = t(y(ρ v))` of a morphism `y : A ⟶ P` of pro-objects and an element
`v` of `V`, as a linear form in `v`. -/
public def dualPairing (y : const.obj A ⟶ P) : Module.Dual k V where
  toFun v := t (constHomValue y (ρ v))
  map_add' v v' := by
    obtain ⟨n, g, rfl⟩ := exists_ι e ρ ι hι v
    obtain ⟨n', g', rfl⟩ := exists_ι e ρ ι hι v'
    rw [← ι_tr e ρ ι hι (le_max_left n n') g, ← ι_tr e ρ ι hι (le_max_right n n') g',
      ← map_add, constHomValue_ι e ρ ι hι, constHomValue_ι e ρ ι hι,
      constHomValue_ι e ρ ι hι, Preadditive.comp_add, map_add]
  map_smul' c v := by
    obtain ⟨n, g, rfl⟩ := exists_ι e ρ ι hι v
    rw [← map_smul, constHomValue_ι e ρ ι hι, constHomValue_ι e ρ ι hι, Linear.comp_smul,
      map_smul]
    rfl

/-- **The duality map** `Hom_{Pro}(A, P) ⟶ V^∨`, `y ↦ (v ↦ t(y(ρ v)))`. -/
public def dualPairingMap : (const.obj A ⟶ P) →ₗ[k] Module.Dual k V where
  toFun y := dualPairing t e ρ ι hι y
  map_add' y y' := by
    ext v
    change t (constHomValue y (ρ v) + constHomValue y' (ρ v)) = _
    rw [map_add]
    rfl
  map_smul' c y := by
    ext v
    change t (c • constHomValue y (ρ v)) = _
    rw [map_smul]
    rfl

/-- The duality map at the element attached to `g : M_n ⟶ ω`. -/
public lemma dualPairingMap_apply_ι (y : const.obj A ⟶ P) {n : ℕ} (g : M.obj (op n) ⟶ ω) :
    dualPairingMap t e ρ ι hι y (ι n g) = t (constHomComponent (y ≫ e.hom) n ≫ g) :=
  congrArg t (constHomValue_ι e ρ ι hι y g)

/-- If the composition pairing `Hom(N, ω) ⟶ Hom(A, N)^∨` is surjective, a morphism `a : A ⟶ N` is
determined by the values `t(a ≫ g)`. -/
private lemma eq_of_compPairing {N : 𝒟} (hθ : Function.Surjective (compPairing t N))
    {a a' : A ⟶ N} (h : ∀ g : N ⟶ ω, t (a ≫ g) = t (a' ≫ g)) : a = a' := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (a - a')).1 fun φ => ?_
  obtain ⟨g, rfl⟩ := hθ φ
  rw [map_sub, compPairing_apply_apply, compPairing_apply_apply, h, sub_self]

/-- If `Hom(A, N)` is finite dimensional and the composition pairing is perfect, every linear form
`μ` on `Hom(N, ω)` is of the form `g ↦ t(a ≫ g)`. -/
private lemma exists_comp_eq {N : 𝒟} [FiniteDimensional k (A ⟶ N)]
    (hN : Function.Bijective (compPairing t N)) (μ : Module.Dual k (N ⟶ ω)) :
    ∃ a : A ⟶ N, ∀ g : N ⟶ ω, t (a ≫ g) = μ g := by
  let θ' := LinearEquiv.ofBijective (compPairing t N) hN
  refine ⟨(Module.evalEquiv k (A ⟶ N)).symm (μ ∘ₗ θ'.symm.toLinearMap), fun g => ?_⟩
  have h := LinearMap.congr_fun ((Module.evalEquiv k (A ⟶ N)).apply_symm_apply
    (μ ∘ₗ θ'.symm.toLinearMap)) (θ' g)
  change (θ' g) _ = μ (θ'.symm (θ' g)) at h
  rwa [LinearEquiv.symm_apply_apply] at h

/-- **Duality between a pro-object and its points.** Let `P ≅ (M_n)` be a pro-object of the
`k`-linear category `𝒟`, `t : Hom(A, ω) ⟶ k` a linear form such that every composition pairing
`Hom(A, M_n) × Hom(M_n, ω) ⟶ k`, `(a, g) ↦ t(a ≫ g)`, identifies `Hom(M_n, ω)` with the dual of
the finite-dimensional space `Hom(A, M_n)`, and `V` a vector space identified with the points
`colim_n Hom(M_n, ω)` of `P` at `ω`, linearly on each `Hom(M_n, ω)`. Then
`y ↦ (v ↦ t(y(ρ v)))` is an isomorphism `Hom_{Pro}(A, P) ≅ V^∨`. -/
public theorem bijective_dualPairingMap
    (hθ : ∀ n : ℕ, Function.Bijective (compPairing t (M.obj (op n))))
    [∀ n : ℕ, FiniteDimensional k (A ⟶ M.obj (op n))] :
    Function.Bijective (dualPairingMap t e ρ ι hι) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have hcomp : ∀ n, constHomComponent (y ≫ e.hom) n = constHomComponent (0 ≫ e.hom) n := by
      intro n
      refine eq_of_compPairing t (hθ n).2 fun g => ?_
      have h := LinearMap.congr_fun hy (ι n g)
      rw [dualPairingMap_apply_ι] at h
      rw [h]
      exact (map_zero t).symm.trans (congrArg t (zero_comp (f := g)).symm)
    exact (cancel_mono e.hom).1 (constHom_ext hcomp)
  · intro l
    choose a ha using fun n => exists_comp_eq t (hθ n) (l ∘ₗ ι n)
    have hx : ∀ n : ℕ, a (n + 1) ≫ M.map (homOfLE (Nat.le_succ n)).op = a n := by
      intro n
      refine eq_of_compPairing t (hθ n).2 fun g => ?_
      rw [Category.assoc, ha, ha]
      exact congrArg l (ι_tr e ρ ι hι (Nat.le_succ n) g)
    refine ⟨constHomMk a hx ≫ e.inv, LinearMap.ext fun v => ?_⟩
    obtain ⟨n, g, rfl⟩ := exists_ι e ρ ι hι v
    rw [dualPairingMap_apply_ι, Category.assoc, e.inv_hom_id, Category.comp_id,
      constHomComponent_constHomMk, ha, LinearMap.comp_apply]

end Duality

section Map

variable {k : Type w} [Field k] [Preadditive 𝒟] [Linear k 𝒟]
  {𝒟' : Type*} [Category.{v} 𝒟'] [Preadditive 𝒟'] [Linear k 𝒟'] (F : 𝒟 ⥤ 𝒟')
  [∀ G : 𝒟 ⥤ Type v, F.HasLeftKanExtension G] {A : 𝒟} {A' : 𝒟'}
  (θ : ∀ N : 𝒟, (A' ⟶ F.obj N) ≃ₗ[k] (A ⟶ N))
  (hθ : ∀ {N N' : 𝒟} (g : N ⟶ N') (a : A' ⟶ F.obj N), θ N' (a ≫ F.map g) = θ N a ≫ g)

include θ hθ

/-- The natural isomorphism `Hom(A', F -) ≅ Hom(A, -)` given by a natural family of bijections. -/
public def homNatIsoOfLinearEquiv : F ⋙ coyoneda.obj (op A') ≅ coyoneda.obj (op A) :=
  NatIso.ofComponents (fun N => (θ N).toEquiv.toIso) fun {N N'} g => by
    ext a
    exact hθ g a

/-- **Morphisms from a constant pro-object into a pushed-forward pro-object.** If
`Hom(A', F N) = Hom(A, N)` naturally in `N`, then `Hom_{Pro}(A', F_* P) = Hom_{Pro}(A, P)`. -/
public def homConstMapEquiv (P : ProSeq 𝒟) :
    (const.obj A' ⟶ (map F).obj P) ≃ (const.obj A ⟶ P) :=
  ((opEquiv (const.obj A') ((map F).obj P)).trans InducedCategory.homEquiv).trans <|
    ((F.lanAdjunction (Type v)).homEquiv P.points (coyoneda.obj (op A'))).trans <|
      ((Iso.refl P.points).homCongr (homNatIsoOfLinearEquiv F θ hθ)).trans
        ((opEquiv (const.obj A) P).trans InducedCategory.homEquiv).symm

/-- The values of `CategoryTheory.ProSeq.homConstMapEquiv`. -/
public lemma constHomValue_homConstMapEquiv (P : ProSeq 𝒟) (y : const.obj A' ⟶ (map F).obj P)
    {N : 𝒟} (x : P.points.obj N) :
    constHomValue (homConstMapEquiv F θ hθ P y) x =
      θ N (constHomValue y ((F.lanUnit.app P.points).app N x)) :=
  rfl

/-- `CategoryTheory.ProSeq.homConstMapEquiv` as a `k`-linear equivalence. -/
public def homConstMapLinearEquiv (P : ProSeq 𝒟) :
    (const.obj A' ⟶ (map F).obj P) ≃ₗ[k] (const.obj A ⟶ P) where
  toEquiv := homConstMapEquiv F θ hθ P
  map_add' y y' := constHom_ext_value fun N x => by
    change θ N (constHomValue y ((F.lanUnit.app P.points).app N x) +
        constHomValue y' ((F.lanUnit.app P.points).app N x)) =
      θ N (constHomValue y ((F.lanUnit.app P.points).app N x)) +
        θ N (constHomValue y' ((F.lanUnit.app P.points).app N x))
    exact map_add _ _ _
  map_smul' c y := constHom_ext_value fun N x => by
    change θ N (c • constHomValue y ((F.lanUnit.app P.points).app N x)) =
      c • θ N (constHomValue y ((F.lanUnit.app P.points).app N x))
    exact map_smul _ _ _

/-- The values of `CategoryTheory.ProSeq.homConstMapLinearEquiv`. -/
public lemma constHomValue_homConstMapLinearEquiv (P : ProSeq 𝒟)
    (y : const.obj A' ⟶ (map F).obj P) {N : 𝒟} (x : P.points.obj N) :
    constHomValue (homConstMapLinearEquiv F θ hθ P y) x =
      θ N (constHomValue y ((F.lanUnit.app P.points).app N x)) :=
  rfl

end Map

section Assembly

variable {k : Type w} [Field k] [Preadditive 𝒟] [Linear k 𝒟]
  {𝒟' : Type*} [Category.{v} 𝒟'] [Preadditive 𝒟'] [Linear k 𝒟'] (F : 𝒟 ⥤ 𝒟')
  [∀ G : 𝒟 ⥤ Type v, F.HasLeftKanExtension G] {A ω : 𝒟} {A' : 𝒟'}
  (θ : ∀ N : 𝒟, (A' ⟶ F.obj N) ≃ₗ[k] (A ⟶ N))
  (hθ : ∀ {N N' : 𝒟} (g : N ⟶ N') (a : A' ⟶ F.obj N), θ N' (a ≫ F.map g) = θ N a ≫ g)
  (t : (A ⟶ ω) →ₗ[k] k)

/-- `CategoryTheory.ProSeq.homConstMapLinearEquiv` is natural in the pro-object. -/
public lemma homConstMapLinearEquiv_comp {P P' : ProSeq 𝒟} (g : P ⟶ P')
    (y : const.obj A' ⟶ (map F).obj P) :
    homConstMapLinearEquiv F θ hθ P' (y ≫ (map F).map g) =
      homConstMapLinearEquiv F θ hθ P y ≫ g := by
  refine constHom_ext_value fun N x => ?_
  change θ N (constHomValue y (((map F).map g).unop.hom.app (F.obj N)
      ((F.lanUnit.app P'.points).app N x))) =
    θ N (constHomValue y ((F.lanUnit.app P.points).app N (g.unop.hom.app N x)))
  congr 2
  exact lan_map_app_lanUnit_app F g.unop.hom N x

variable {M : ℕᵒᵖ ⥤ 𝒟} {P : ProSeq 𝒟} (e : P ≅ of M) {V : Type*} [AddCommGroup V] [Module k V]
  (ρ : V ≃ P.points.obj ω) (ι : ∀ n : ℕ, (M.obj (op n) ⟶ ω) →ₗ[k] V)
  (hι : ∀ (n : ℕ) (g : M.obj (op n) ⟶ ω),
    ρ (ι n g) = e.hom.unop.hom.app ω ((Pro.seqHomColimIso M).inv.app ω (Pro.seqStage M g)))
  (hperf : ∀ n : ℕ, Function.Bijective (compPairing t (M.obj (op n))))
  [∀ n : ℕ, FiniteDimensional k (A ⟶ M.obj (op n))]

/-- **The duality isomorphism** `V^∨ ≃ Hom_{Pro}(A', F_* P)`: the pairing of
`CategoryTheory.ProSeq.bijective_dualPairingMap` followed by
`CategoryTheory.ProSeq.homConstMapLinearEquiv`. -/
public def proDualityLinearEquiv : Module.Dual k V ≃ₗ[k] (const.obj A' ⟶ (map F).obj P) :=
  (LinearEquiv.ofBijective (dualPairingMap t e ρ ι hι)
      (bijective_dualPairingMap t e ρ ι hι hperf)).symm.trans
    (homConstMapLinearEquiv F θ hθ P).symm

/-- The duality isomorphism is characterized by the pairing: `⟨φ(l), v⟩ = l(v)`. -/
public lemma dualPairingMap_homConstMapLinearEquiv_proDualityLinearEquiv
    (l : Module.Dual k V) :
    dualPairingMap t e ρ ι hι
      (homConstMapLinearEquiv F θ hθ P (proDualityLinearEquiv F θ hθ t e ρ ι hι hperf l)) = l := by
  unfold proDualityLinearEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (dualPairingMap t e ρ ι hι)
    (bijective_dualPairingMap t e ρ ι hι hperf)) l

/-- **Naturality of the duality isomorphism.** A morphism `g : P ⟶ P'` of pro-objects compatible
with a linear map `φ : V' ⟶ V` on the identified points carries the duality isomorphism of `P` to
that of `P'`: `φ^∨` corresponds to composition with `F_* g`. -/
public theorem proDualityLinearEquiv_naturality {M' : ℕᵒᵖ ⥤ 𝒟} {P' : ProSeq 𝒟} (e' : P' ≅ of M')
    {V' : Type*} [AddCommGroup V'] [Module k V'] (ρ' : V' ≃ P'.points.obj ω)
    (ι' : ∀ n : ℕ, (M'.obj (op n) ⟶ ω) →ₗ[k] V')
    (hι' : ∀ (n : ℕ) (g : M'.obj (op n) ⟶ ω),
      ρ' (ι' n g) = e'.hom.unop.hom.app ω ((Pro.seqHomColimIso M').inv.app ω (Pro.seqStage M' g)))
    (hperf' : ∀ n : ℕ, Function.Bijective (compPairing t (M'.obj (op n))))
    [∀ n : ℕ, FiniteDimensional k (A ⟶ M'.obj (op n))]
    (g : P ⟶ P') (φ : V' →ₗ[k] V) (hg : ∀ v' : V', g.unop.hom.app ω (ρ' v') = ρ (φ v'))
    (l : Module.Dual k V) :
    proDualityLinearEquiv F θ hθ t e' ρ' ι' hι' hperf' (l ∘ₗ φ) =
      proDualityLinearEquiv F θ hθ t e ρ ι hι hperf l ≫ (map F).map g := by
  apply (homConstMapLinearEquiv F θ hθ P').injective
  rw [homConstMapLinearEquiv_comp]
  apply (bijective_dualPairingMap t e' ρ' ι' hι' hperf').1
  rw [dualPairingMap_homConstMapLinearEquiv_proDualityLinearEquiv]
  ext v'
  change l (φ v') = t (constHomValue (homConstMapLinearEquiv F θ hθ P
    (proDualityLinearEquiv F θ hθ t e ρ ι hι hperf l)) (g.unop.hom.app ω (ρ' v')))
  rw [hg]
  exact (LinearMap.congr_fun (dualPairingMap_homConstMapLinearEquiv_proDualityLinearEquiv
    F θ hθ t e ρ ι hι hperf l) (φ v')).symm

/-- The projection of `Hom_{Pro}(A', F_* P)` to its `n`-th term `Hom(A', F M_n)`, through
`F_* P ≅ (F M_n)`. -/
public def pushforwardProjection (n : ℕ) (y : const.obj A' ⟶ (map F).obj P) :
    A' ⟶ F.obj (M.obj (op n)) :=
  constHomComponent (y ≫ ((map F).mapIso e ≪≫ mapOfIso F M).hom) n

omit [∀ (n : ℕ), FiniteDimensional k (A ⟶ M.obj (op n))] in
/-- The `n`-th projection of `y` corresponds under `θ` to the `n`-th component of the morphism
`Hom_{Pro}(A, P)` attached to `y`. -/
public lemma θ_pushforwardProjection (n : ℕ) (y : const.obj A' ⟶ (map F).obj P) :
    θ (M.obj (op n)) (pushforwardProjection F e n y) =
      constHomComponent (homConstMapLinearEquiv F θ hθ P y ≫ e.hom) n := by
  have h1 := mapOfIso_inv_app_lanUnit_app F M (𝟙 (M.obj (op n)))
  rw [F.map_id] at h1
  have h2 : (mapOfIso F M).hom.unop.hom.app (F.obj (M.obj (op n)))
      ((Pro.seqHomColimIso (M ⋙ F)).inv.app _ (Pro.seqStage (M ⋙ F) (𝟙 (F.obj (M.obj (op n)))))) =
      (F.lanUnit.app (of M).points).app _ ((Pro.seqHomColimIso M).inv.app _
        (Pro.seqStage M (𝟙 (M.obj (op n))))) := by
    rw [← h1]
    have h : ((mapOfIso F M).hom ≫ (mapOfIso F M).inv).unop.hom.app (F.obj (M.obj (op n)))
        ((F.lanUnit.app (of M).points).app _ ((Pro.seqHomColimIso M).inv.app _
          (Pro.seqStage M (𝟙 (M.obj (op n)))))) =
        (F.lanUnit.app (of M).points).app _ ((Pro.seqHomColimIso M).inv.app _
          (Pro.seqStage M (𝟙 (M.obj (op n))))) := by
      rw [Iso.hom_inv_id]; rfl
    exact h
  change θ _ (constHomValue y (((map F).map e.hom).unop.hom.app _
      ((mapOfIso F M).hom.unop.hom.app _ ((Pro.seqHomColimIso (M ⋙ F)).inv.app _
        (Pro.seqStage (M ⋙ F) (𝟙 (F.obj (M.obj (op n))))))))) =
    constHomValue (homConstMapLinearEquiv F θ hθ P y) (e.hom.unop.hom.app _
      ((Pro.seqHomColimIso M).inv.app _ (Pro.seqStage M (𝟙 (M.obj (op n))))))
  rw [h2]
  refine (congrArg (fun z => θ (M.obj (op n)) (constHomValue y z))
    (lan_map_app_lanUnit_app F e.hom.unop.hom (M.obj (op n)) _)).trans ?_
  exact (constHomValue_homConstMapLinearEquiv F θ hθ P y _).symm

include hperf in
/-- The terms `Hom(M_n, ω)` are finite dimensional. -/
public lemma finite_hom_omega (n : ℕ) : Module.Finite k (M.obj (op n) ⟶ ω) :=
  Module.Finite.equiv (LinearEquiv.ofBijective (compPairing t _) (hperf n)).symm

/-- **The duality isomorphism is a homeomorphism**, for the limit topology on the dual
(`Module.Dual.limitTopology`) and the limit topology of the projections to `Hom(A', F M_n)`,
each discrete. -/
public theorem isHomeomorph_proDualityLinearEquiv :
    letI := Module.Dual.limitTopology k V
    letI := ⨅ n : ℕ, TopologicalSpace.induced (pushforwardProjection F (A' := A') e n) ⊥
    IsHomeomorph (proDualityLinearEquiv F θ hθ t e ρ ι hι hperf) := by
  have := finite_hom_omega t hperf
  choose a ha using fun n => exists_comp_eq t (hperf n)
  let φ : ∀ n : ℕ, Module.Dual k (M.obj (op n) ⟶ ω) → (A' ⟶ F.obj (M.obj (op n))) := fun n μ =>
    (θ _).symm (a n μ)
  have hj : ⨆ n, LinearMap.range (ι n) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨n, g, rfl⟩ := exists_ι e ρ ι hι v
    exact Submodule.mem_iSup_of_mem n ⟨g, rfl⟩
  have hφ : ∀ n, Function.Injective (φ n) := by
    intro n μ μ' h
    ext g
    rw [← ha, ← ha, (θ _).symm.injective h]
  have he : ∀ (l : Module.Dual k V) (n : ℕ),
      pushforwardProjection F e n ((proDualityLinearEquiv F θ hθ t e ρ ι hι hperf).toEquiv l) =
        φ n (l ∘ₗ ι n) := by
    intro l n
    apply (θ (M.obj (op n))).injective
    rw [LinearEquiv.apply_symm_apply]
    change θ _ (pushforwardProjection F e n (proDualityLinearEquiv F θ hθ t e ρ ι hι hperf l)) = _
    rw [θ_pushforwardProjection (hθ := hθ)]
    refine eq_of_compPairing t (hperf n).2 fun g => ?_
    rw [ha, ← dualPairingMap_apply_ι t e ρ ι hι,
      dualPairingMap_homConstMapLinearEquiv_proDualityLinearEquiv]
    rfl
  exact Module.Dual.isHomeomorph_of_iSup_range_eq_top (R := k) (V := V) ι hj
    (pushforwardProjection F (A' := A') e) φ hφ
    (proDualityLinearEquiv F θ hθ t e ρ ι hι hperf).toEquiv he

end Assembly

section Values

variable {𝒞 : Type*} [Category.{v} 𝒞] {jstar : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jstar)

/-- Under `Rj_! K = (K_n)` for an assigned Deligne system, the class of `g : K_n ⟶ N` is the point
`K ≅ K_n|_U ⟶ N|_U` of `Rj_! K` at `N`. -/
public lemma extensionByZeroIso_hom_app_seqStage (K : 𝒞) {N : 𝒟} {n : ℕ}
    (g : (A.system K).obj (op n) ⟶ N) :
    (extensionByZeroIso jstar A.toAssignment K).hom.unop.hom.app N
        ((Pro.seqHomColimIso (A.system K)).inv.app N (Pro.seqStage (A.system K) g)) =
      (A.restrictIso K).inv.app (op n) ≫ jstar.map g := by
  change (A.systemHomIso K).hom.app N ((Pro.seqHomColimIso (A.system K)).hom.app N
    ((Pro.seqHomColimIso (A.system K)).inv.app N (Pro.seqStage (A.system K) g))) = _
  rw [Iso.inv_hom_id_app_apply]
  refine (proHomComparison_stage (A.system K) jstar (A.restrictCone K) g).trans ?_
  change (𝟙 K ≫ (A.restrictIso K).inv.app (op n)) ≫ jstar.map g = _
  rw [Category.id_comp]

end Values

end CategoryTheory.ProSeq

end
