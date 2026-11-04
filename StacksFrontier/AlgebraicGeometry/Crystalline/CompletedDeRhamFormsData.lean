module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvatureBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel

/-!
# Completed de Rham complexes and their base changes, bundled

The completed de Rham complex `M ⊗^∧_D Ω^*_D` of a module with an integrable completed
connection, and the base change map `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` along a ring map
`D → D'` with a comparison of forms (`Crystalline.CompletedDeRham.baseChangeComplexHom`), are
stated in the library with every datum an explicit argument.  This module bundles them, so that
the formal manipulations of the proof of [Stacks, Lemma 60.21.4, Tag 07LH] — compositions of base
changes, retracts, naturality in horizontal maps — can be stated without restating the data:

* `Crystalline.FormsData` — a ring `D` with a graded family of forms `Ω^*_D`, its wedge product
  with one-forms, its de Rham differential and its universal differential, satisfying the
  identities a completed de Rham complex is built from, and such that every integrable
  connection gives a complex;
* `Crystalline.FormsData.Hom` — a ring map with a comparison of forms compatible with all of it;
* `Crystalline.FormsData.ConnModule` — a `p`-adically complete module with an integrable
  completed connection, and its complex `Crystalline.FormsData.ConnModule.complex`;
* `Crystalline.FormsData.ConnModule.baseChange` and
  `Crystalline.FormsData.ConnModule.baseChangeHom` — the base change of such a module along a
  morphism, and the base change map of complexes;
* `Crystalline.FormsData.ConnModule.Hom` — a horizontal linear map, and the morphism of complexes
  it induces.

## Main results

* `Crystalline.FormsData.ConnModule.baseChangeHom_comp` — **the composition law**: the base change
  along `g' ∘ g` is the base change along `g` followed by the base change along `g'`, up to the
  isomorphism of complexes induced by the comparison of the two base-changed modules.
* `Crystalline.FormsData.ConnModule.isIso_baseChangeHom_id` — the base change along the identity
  is an isomorphism of complexes.
* `Crystalline.FormsData.ConnModule.baseChangeHom_naturality` — the base change map is natural in
  horizontal maps.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

/-- **A ring with a graded family of completed forms**: the data a completed de Rham complex is
built from — the forms `Ω^i_D`, the wedge `Ω^i_D × Ω^1_D → Ω^{i+1}_D`, the de Rham differential and
the universal differential `d : D → Ω^1_D` — subject to the graded Leibniz rule, the
anticommutativity of the wedge of one-forms and `d ∘ d = 0` on `D`, and the property that the de
Rham complex of an integrable completed connection is a complex. -/
structure FormsData (p : ℕ) where
  /-- The ring `D`. -/
  ring : Type u
  /-- Its ring structure. -/
  [commRing : CommRing ring]
  /-- The forms `Ω^i_D`. -/
  Om : ℕ → Type u
  /-- Their additive structure. -/
  [addCommGroup : ∀ i, AddCommGroup (Om i)]
  /-- Their `D`-module structure. -/
  [module : ∀ i, Module ring (Om i)]
  /-- The wedge product with a one-form. -/
  wedge : ∀ i, Om i →ₗ[ring] Om 1 →ₗ[ring] Om (i + 1)
  /-- The de Rham differential. -/
  deRham : ∀ i, Om i →+ Om (i + 1)
  /-- The universal differential `d : D → Ω^1_D`. -/
  diff : ring → Om 1
  /-- `d` is additive. -/
  diff_add : ∀ x y : ring, diff (x + y) = diff x + diff y
  /-- `d` satisfies the product rule. -/
  diff_mul : ∀ x y : ring, diff (x * y) = x • diff y + y • diff x
  /-- The graded Leibniz rule. -/
  isGradedLeibniz : CompletedDeRham.IsGradedLeibniz ring Om wedge deRham diff
  /-- The wedge of one-forms is anticommutative. -/
  wedge_anti : ∀ η ζ : Om 1, wedge 1 η ζ + wedge 1 ζ η = 0
  /-- `d ∘ d = 0` on the ring. -/
  deRham_diff : ∀ c : ring, deRham 1 (diff c) = 0
  /-- The de Rham complex of an integrable connection is a complex. -/
  isSquareZero : ∀ {M : Type u} [AddCommGroup M] [Module ring M]
    (nabla : CompletedConnection p ring (Om 1) diff M),
    CompletedDeRham.IsCurvatureZero p ring Om wedge deRham M nabla isGradedLeibniz →
      CompletedDeRham.IsSquareZero p ring Om wedge deRham M nabla isGradedLeibniz

attribute [instance] FormsData.commRing FormsData.addCommGroup FormsData.module

namespace FormsData

/-- **The base change map is natural in a linear map**, degreewise: the completion of
`(1 ⊗ f) ⊗ 1 ∘ (m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ ω)` is the completion of
`(m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ ω) ∘ (f ⊗ 1)`. -/
theorem baseChangeTerm_horizontalTerm (p : ℕ) (D D' : Type u) [CommRing D] [CommRing D']
    [Algebra D D'] (M N : Type u) [AddCommGroup M] [Module D M] [AddCommGroup N] [Module D N]
    (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
    (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
    (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i) (f : M →ₗ[D] N) (i : ℕ)
    (x : CompletedTensor p D (Om i) M) :
    CompletedDeRham.horizontalTerm p D' (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeCarrier p D D' N) Om'
        (CompletedConnection.baseChangeModuleMap p D D' M N f) i
        (CompletedDeRham.baseChangeTerm p D D' M Om Om' psi i x) =
      CompletedDeRham.baseChangeTerm p D D' N Om Om' psi i
        (CompletedDeRham.horizontalTerm p D M N Om f i x) := by
  have h := completedTensor_addMonoidHom_ext p
    (f := (CompletedDeRham.horizontalTerm p D' (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeCarrier p D D' N) Om'
        (CompletedConnection.baseChangeModuleMap p D D' M N f) i).comp
      (CompletedDeRham.baseChangeTerm p D D' M Om Om' psi i))
    (g := (CompletedDeRham.baseChangeTerm p D D' N Om Om' psi i).comp
      (CompletedDeRham.horizontalTerm p D M N Om f i))
    fun m ω ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply,
        CompletedDeRham.baseChangeTerm_of_tmul, CompletedDeRham.horizontalTerm_of_tmul,
        CompletedConnection.baseChangeModuleMap_inclusion]
  exact DFunLike.congr_fun h x

end FormsData

/-- **The linear extension of a horizontal semilinear map is horizontal.**  Let `μ : M → N` be
semilinear over `D → D'` and horizontal, `∇_N (μ m) = (μ ⊗ ψ)(∇_M m)`, and let
`β : M ⊗̂_D D' → N` be `D'`-linear with `β (1 ⊗ m) = μ m`.  Then `β` is horizontal for the
base-changed connection.  The difference of the two sides is `D'`-linear, the Leibniz corrections
cancelling, and vanishes on the `1 ⊗ m`. -/
theorem horizontal_of_baseChangeInclusion (p : ℕ) (D D' : Type u) [CommRing D] [CommRing D']
    [Algebra D D'] (M N : Type u) [AddCommGroup M] [Module D M] [AddCommGroup N] [Module D' N]
    (Om : Type u) [AddCommGroup Om] [Module D Om] (Om' : Type u) [AddCommGroup Om']
    [Module D' Om'] {d : D → Om} (d' : D' → Om') (psi : Om →ₛₗ[algebraMap D D'] Om')
    (nablaM : CompletedConnection p D Om d M) (nablaN : CompletedConnection p D' Om' d' N)
    (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
    (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
    (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D D' x))
    (β : CompletedConnection.baseChangeCarrier p D D' M →ₗ[D'] N) (mu : M →ₛₗ[algebraMap D D'] N)
    (hβ : ∀ m, β (CompletedConnection.baseChangeInclusion p D D' M m) = mu m)
    (hmu : ∀ m, nablaN (mu m) = adicCompletionMapₛₗ (TensorProduct.map mu psi)
      (CompletedConnection.pAdicIdeal_map_le p D D') (nablaM m))
    (x : CompletedConnection.baseChangeCarrier p D D' M) :
    nablaN (β x) = AdicCompletion.map (pAdicIdeal (A := D') p)
      (TensorProduct.map β (LinearMap.id (R := D') (M := Om')))
      (CompletedConnection.baseChange p D D' M Om Om' d' psi nablaM hd'add hd'leib hpsi x) := by
  set nb := CompletedConnection.baseChange p D D' M Om Om' d' psi nablaM hd'add hd'leib hpsi
  set Φ := AdicCompletion.map (pAdicIdeal (A := D') p)
    (TensorProduct.map β (LinearMap.id (R := D') (M := Om'))) with hΦ
  have hfac : ∀ z : CompletedTensor p D Om M,
      Φ (CompletedConnection.baseChangeValues p D D' M Om Om' psi z) =
        adicCompletionMapₛₗ (TensorProduct.map mu psi)
          (CompletedConnection.pAdicIdeal_map_le p D D') z := by
    intro z
    have h := completedTensor_addMonoidHom_ext p
      (f := Φ.toAddMonoidHom.comp
        (CompletedConnection.baseChangeValues p D D' M Om Om' psi).toAddMonoidHom)
      (g := (adicCompletionMapₛₗ (TensorProduct.map mu psi)
          (CompletedConnection.pAdicIdeal_map_le p D D')).toAddMonoidHom) fun m ω ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          CompletedConnection.baseChangeValues_of_tmul]
        rw [hΦ, AdicCompletion.map_of, TensorProduct.map_tmul, hβ, adicCompletionMapₛₗ_of,
          TensorProduct.map_tmul]
        rfl
    exact DFunLike.congr_fun h z
  let ψ₁ : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D' Om' N :=
    (AddMonoidHom.mk' nablaN nablaN.map_add).comp β.toAddMonoidHom
  let ψ₂ : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D' Om' N :=
    Φ.toAddMonoidHom.comp (AddMonoidHom.mk' nb nb.map_add)
  have h := CompletedConnection.baseChangeCarrier_ext p D D' M (RingHom.id D')
    (inferInstance : IsHausdorff (pAdicIdeal (A := D') p) (CompletedTensor p D' Om' N))
    (ψ := ψ₁ - ψ₂) (ψ' := 0) (fun c x ↦ ?_) (fun c x ↦ by simp) (fun m ↦ ?_)
  · exact sub_eq_zero.mp (DFunLike.congr_fun h x)
  · have hmap : ∀ y : CompletedTensor p D' Om' (CompletedConnection.baseChangeCarrier p D D' M),
        Φ (c • y) = c • Φ y := fun y ↦ (Φ.restrictScalars D').map_smul c y
    change nablaN (β (c • x)) - Φ (nb (c • x)) = c • (nablaN (β x) - Φ (nb x))
    rw [map_smul, nablaN.leibniz, nb.leibniz, map_add, hmap, hΦ, AdicCompletion.map_of,
      TensorProduct.map_tmul, LinearMap.id_apply, smul_sub]
    abel
  · simp only [ψ₁, ψ₂, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply]
    rw [hβ, hmu, CompletedConnection.baseChange_inclusion, hfac, sub_self]

namespace FormsData

variable {p : ℕ}

/-- **A morphism of rings with forms**: a ring map with a comparison of forms, semilinear over
it, compatible with the universal differential, the wedge product and the de Rham differential. -/
structure Hom (R R' : FormsData.{u} p) where
  /-- The ring map. -/
  toRingHom : R.ring →+* R'.ring
  /-- The comparison of forms. -/
  psi : ∀ i, R.Om i →ₛₗ[toRingHom] R'.Om i
  /-- The comparison carries `d x` to `d (g x)`. -/
  psi_diff : ∀ x, psi 1 (R.diff x) = R'.diff (toRingHom x)
  /-- The comparison respects the wedge product. -/
  psi_wedge : ∀ (i : ℕ) (ω : R.Om i) (η : R.Om 1),
    psi (i + 1) (R.wedge i ω η) = R'.wedge i (psi i ω) (psi 1 η)
  /-- The comparison respects the de Rham differential. -/
  psi_deRham : ∀ (i : ℕ) (ω : R.Om i), psi (i + 1) (R.deRham i ω) = R'.deRham i (psi i ω)

namespace Hom

/-- The identity morphism. -/
def id (R : FormsData.{u} p) : Hom R R where
  toRingHom := RingHom.id _
  psi _ := LinearMap.id
  psi_diff _ := rfl
  psi_wedge _ _ _ := rfl
  psi_deRham _ _ := rfl

/-- The composite of two morphisms. -/
def comp {R R' R'' : FormsData.{u} p} (g' : Hom R' R'') (g : Hom R R') : Hom R R'' where
  toRingHom := g'.toRingHom.comp g.toRingHom
  psi i := letI : RingHomCompTriple g.toRingHom g'.toRingHom (g'.toRingHom.comp g.toRingHom) :=
      ⟨rfl⟩
    (g'.psi i).comp (g.psi i)
  psi_diff x := by
    simp only [LinearMap.coe_comp, Function.comp_apply, g.psi_diff, g'.psi_diff,
      RingHom.coe_comp]
  psi_wedge i ω η := by
    simp only [LinearMap.coe_comp, Function.comp_apply, g.psi_wedge, g'.psi_wedge]
  psi_deRham i ω := by
    simp only [LinearMap.coe_comp, Function.comp_apply, g.psi_deRham, g'.psi_deRham]

/-- The ring map of a composite is the composite of the ring maps. -/
@[simp] theorem comp_toRingHom {R R' R'' : FormsData.{u} p} (g' : Hom R' R'') (g : Hom R R') :
    (g'.comp g).toRingHom = g'.toRingHom.comp g.toRingHom := rfl

/-- The comparison of forms of a composite is the composite of the comparisons. -/
@[simp] theorem comp_psi {R R' R'' : FormsData.{u} p} (g' : Hom R' R'') (g : Hom R R') (i : ℕ)
    (ω : R.Om i) : (g'.comp g).psi i ω = g'.psi i (g.psi i ω) := rfl

/-- Two morphisms with the same ring map and the same comparison of forms are equal. -/
theorem ext {R R' : FormsData.{u} p} {g g' : Hom R R'} (h : g.toRingHom = g'.toRingHom)
    (hpsi : ∀ i ω, g.psi i ω = g'.psi i ω) : g = g' := by
  obtain ⟨f, ψ, _, _, _⟩ := g
  obtain ⟨f', ψ', _, _, _⟩ := g'
  obtain rfl : f = f' := h
  obtain rfl : ψ = ψ' := funext fun i ↦ LinearMap.ext fun ω ↦ hpsi i ω
  rfl

end Hom

/-- **A module with an integrable completed connection** over a ring with forms: `p`-adically
complete, with a completed connection whose curvature vanishes. -/
structure ConnModule (R : FormsData.{u} p) where
  /-- The module `M`. -/
  carrier : Type u
  /-- Its additive structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its module structure. -/
  [module : Module R.ring carrier]
  /-- `M` is `p`-adically complete. -/
  isPAdicallyComplete : IsPAdicallyComplete p R.ring carrier
  /-- The completed connection. -/
  nabla : CompletedConnection p R.ring (R.Om 1) R.diff carrier
  /-- The connection is integrable. -/
  isCurvatureZero : CompletedDeRham.IsCurvatureZero p R.ring R.Om R.wedge R.deRham carrier nabla
    R.isGradedLeibniz

attribute [instance] ConnModule.addCommGroup ConnModule.module

namespace ConnModule

variable {R : FormsData.{u} p}

/-- **The completed de Rham complex `M ⊗^∧_D Ω^*_D`.** -/
def complex (M : ConnModule R) : CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex p R.ring R.Om R.wedge R.deRham M.carrier M.nabla R.isGradedLeibniz
    (R.isSquareZero M.nabla M.isCurvatureZero)

/-- **A horizontal linear map** of modules with connection. -/
structure Hom (M N : ConnModule R) where
  /-- The underlying linear map. -/
  toLinearMap : M.carrier →ₗ[R.ring] N.carrier
  /-- It commutes with the connections. -/
  horizontal : ∀ m, N.nabla (toLinearMap m) =
    AdicCompletion.map (pAdicIdeal (A := R.ring) p)
      (TensorProduct.map toLinearMap (LinearMap.id (R := R.ring) (M := R.Om 1))) (M.nabla m)

/-- **The morphism of complexes induced by a horizontal map.** -/
def complexMap {M N : ConnModule R} (f : Hom M N) : M.complex ⟶ N.complex :=
  CompletedDeRham.horizontalComplexHom p R.ring M.carrier N.carrier R.Om f.toLinearMap R.wedge
    R.deRham M.nabla N.nabla R.isGradedLeibniz f.horizontal _ _

/-- The morphism of complexes induced by a horizontal linear equivalence is an isomorphism. -/
theorem isIso_complexMap {M N : ConnModule R} (f : Hom M N)
    (hf : Function.Bijective f.toLinearMap) : IsIso (complexMap f) :=
  CompletedDeRham.isIso_horizontalComplexHom p R.ring M.carrier N.carrier R.Om
    (LinearEquiv.ofBijective f.toLinearMap hf) R.wedge R.deRham M.nabla N.nabla
    R.isGradedLeibniz f.horizontal _ _

section BaseChange

variable {R' : FormsData.{u} p} (g : FormsData.Hom R R')

/-- **The base change of a module with an integrable connection along a morphism**:
`M ⊗̂_D D'` with the base-changed connection, which is again integrable. -/
def baseChange (M : ConnModule R) : ConnModule R' :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  { carrier := CompletedConnection.baseChangeCarrier p R.ring R'.ring M.carrier
    isPAdicallyComplete :=
      CompletedConnection.isPAdicallyComplete_baseChangeCarrier p R.ring R'.ring M.carrier
    nabla := CompletedConnection.baseChange p R.ring R'.ring M.carrier (R.Om 1) (R'.Om 1)
      R'.diff (g.psi 1) M.nabla R'.diff_add R'.diff_mul g.psi_diff
    isCurvatureZero := CompletedDeRham.isCurvatureZero_baseChange p R.ring R'.ring M.carrier
      R.Om R'.Om g.psi R.wedge R'.wedge R.deRham R'.deRham R'.diff M.nabla R'.diff_add
      R'.diff_mul g.psi_diff R.isGradedLeibniz R'.isGradedLeibniz g.psi_wedge g.psi_deRham
      R'.wedge_anti R'.deRham_diff M.isCurvatureZero }

/-- The connection of the base change, unfolded: the base change of the connection along the
ring map, with the comparison of one-forms. -/
theorem baseChange_nabla (M : ConnModule R) :
    (M.baseChange g).nabla =
      (letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      CompletedConnection.baseChange p R.ring R'.ring M.carrier (R.Om 1) (R'.Om 1) R'.diff
        (g.psi 1) M.nabla R'.diff_add R'.diff_mul g.psi_diff) :=
  rfl

/-- **A horizontal map between two base changes of `M`**, given on the completed base-changed
modules and checked against the base-changed connections. -/
def Hom.ofBaseChange (M : ConnModule R) (g' : FormsData.Hom R R')
    (f : (letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      CompletedConnection.baseChangeCarrier p R.ring R'.ring M.carrier) →ₗ[R'.ring]
      (letI : Algebra R.ring R'.ring := g'.toRingHom.toAlgebra
      CompletedConnection.baseChangeCarrier p R.ring R'.ring M.carrier))
    (hf : ∀ x, (letI : Algebra R.ring R'.ring := g'.toRingHom.toAlgebra
        CompletedConnection.baseChange p R.ring R'.ring M.carrier (R.Om 1) (R'.Om 1) R'.diff
          (g'.psi 1) M.nabla R'.diff_add R'.diff_mul g'.psi_diff).toFun (f x) =
      AdicCompletion.map (pAdicIdeal (A := R'.ring) p)
        (TensorProduct.map f (LinearMap.id (R := R'.ring) (M := R'.Om 1)))
        ((letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
        CompletedConnection.baseChange p R.ring R'.ring M.carrier (R.Om 1) (R'.Om 1) R'.diff
          (g.psi 1) M.nabla R'.diff_add R'.diff_mul g.psi_diff).toFun x)) :
    Hom (M.baseChange g) (M.baseChange g') :=
  ⟨f, hf⟩

/-- The underlying linear map of `Crystalline.FormsData.ConnModule.Hom.ofBaseChange`. -/
theorem Hom.ofBaseChange_toLinearMap (M : ConnModule R) (g' : FormsData.Hom R R') (f) (hf) :
    (Hom.ofBaseChange g M g' f hf).toLinearMap = f :=
  rfl

/-- **The base change map of completed de Rham complexes** `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}`,
`m ⊗ ω ↦ (1 ⊗ m) ⊗ ψ ω`. -/
def baseChangeHom (M : ConnModule R) : M.complex ⟶ (M.baseChange g).complex :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  CompletedDeRham.baseChangeComplexHom p R.ring R'.ring M.carrier R.Om R'.Om g.psi R.wedge
    R'.wedge R.deRham R'.deRham R'.diff M.nabla R'.diff_add R'.diff_mul g.psi_diff
    R.isGradedLeibniz R'.isGradedLeibniz g.psi_wedge g.psi_deRham _ _

end BaseChange

section Functoriality

variable {R' R'' : FormsData.{u} p}

/-- The degree-`i` component of the base change map. -/
theorem baseChangeHom_f (g : FormsData.Hom R R') (M : ConnModule R) (i : ℕ) :
    (M.baseChangeHom g).f i =
      letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      AddCommGrpCat.ofHom (CompletedDeRham.baseChangeTerm p R.ring R'.ring M.carrier R.Om R'.Om
        g.psi i) :=
  rfl

/-- The degree-`i` component of the morphism induced by a horizontal map. -/
theorem complexMap_f {M N : ConnModule R} (f : Hom M N) (i : ℕ) :
    (complexMap f).f i =
      AddCommGrpCat.ofHom (CompletedDeRham.horizontalTerm p R.ring M.carrier N.carrier R.Om
        f.toLinearMap i) :=
  rfl

/-- **The comparison `(M ⊗̂_D D') ⊗̂_{D'} D'' → M ⊗̂_D D''`**, as a horizontal map. -/
def baseChangeCompHom (g : FormsData.Hom R R') (g' : FormsData.Hom R' R'') (M : ConnModule R) :
    Hom ((M.baseChange g).baseChange g') (M.baseChange (g'.comp g)) :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  letI : Algebra R'.ring R''.ring := g'.toRingHom.toAlgebra
  letI : Algebra R.ring R''.ring := (g'.comp g).toRingHom.toAlgebra
  haveI : IsScalarTower R.ring R'.ring R''.ring := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  { toLinearMap := CompletedConnection.baseChangeComposite p R.ring R'.ring R''.ring M.carrier
    horizontal := fun x ↦
      (CompletedConnection.baseChange_baseChangeComposite p R.ring R'.ring R''.ring M.carrier
        (R.Om 1) (R'.Om 1) (R''.Om 1) R'.diff R''.diff (g.psi 1) (g'.psi 1) ((g'.comp g).psi 1)
        M.nabla R'.diff_add R'.diff_mul g.psi_diff R''.diff_add R''.diff_mul g'.psi_diff
        (fun _ ↦ rfl) (g'.comp g).psi_diff x).trans
        (CompletedDeRham.horizontalTerm_baseChangeComposite p R.ring R'.ring R''.ring M.carrier
          R''.Om 1 _).symm }

/-- The comparison of the twice base-changed module with the once base-changed one is bijective. -/
theorem baseChangeCompHom_bijective (g : FormsData.Hom R R') (g' : FormsData.Hom R' R'')
    (M : ConnModule R) : Function.Bijective (baseChangeCompHom g g' M).toLinearMap :=
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  let : Algebra R'.ring R''.ring := g'.toRingHom.toAlgebra
  let : Algebra R.ring R''.ring := (g'.comp g).toRingHom.toAlgebra
  have : IsScalarTower R.ring R'.ring R''.ring := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  CompletedConnection.baseChangeComposite_bijective p R.ring R'.ring R''.ring M.carrier

/-- The identification of the iterated base change with the base change along the composite
induces an isomorphism of complexes. -/
instance isIso_complexMap_baseChangeCompHom (g : FormsData.Hom R R') (g' : FormsData.Hom R' R'')
    (M : ConnModule R) : IsIso (complexMap (baseChangeCompHom g g' M)) :=
  isIso_complexMap _ (baseChangeCompHom_bijective g g' M)

/-- **The composition law of base changes**: base changing along `g` and then along `g'` is base
changing along `g' ∘ g`, up to the isomorphism of complexes induced by the comparison of the two
base-changed modules. -/
theorem baseChangeHom_comp (g : FormsData.Hom R R') (g' : FormsData.Hom R' R'')
    (M : ConnModule R) :
    M.baseChangeHom g ≫ (M.baseChange g).baseChangeHom g' ≫
        complexMap (baseChangeCompHom g g' M) =
      M.baseChangeHom (g'.comp g) :=
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  let : Algebra R'.ring R''.ring := g'.toRingHom.toAlgebra
  let : Algebra R.ring R''.ring := (g'.comp g).toRingHom.toAlgebra
  have : IsScalarTower R.ring R'.ring R''.ring := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  CompletedDeRham.baseChangeComplexHom_comp p R.ring R'.ring R''.ring M.carrier R.Om R'.Om R''.Om
    g.psi g'.psi (g'.comp g).psi R.wedge R'.wedge R''.wedge R.deRham R'.deRham R''.deRham
    (fun _ _ ↦ rfl) R'.diff R''.diff M.nabla R'.diff_add R'.diff_mul g.psi_diff R''.diff_add
    R''.diff_mul g'.psi_diff (g'.comp g).psi_diff R.isGradedLeibniz R'.isGradedLeibniz
    R''.isGradedLeibniz g.psi_wedge g.psi_deRham g'.psi_wedge g'.psi_deRham
    (g'.comp g).psi_wedge (g'.comp g).psi_deRham _ _ _ _

/-- **The base change along the identity is an isomorphism of complexes.** -/
instance isIso_baseChangeHom_id (M : ConnModule R) : IsIso (M.baseChangeHom (FormsData.Hom.id R)) :=
  CompletedDeRham.isIso_baseChangeComplexHom_id p R.ring M.carrier R.Om R.wedge R.deRham M.nabla
    R.diff_add R.diff_mul R.isGradedLeibniz M.isPAdicallyComplete _ _

/-- **The base change of a horizontal map**, a horizontal map of the base-changed modules. -/
def baseChangeMap (g : FormsData.Hom R R') {M N : ConnModule R} (f : Hom M N) :
    Hom (M.baseChange g) (N.baseChange g) :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  { toLinearMap := CompletedConnection.baseChangeModuleMap p R.ring R'.ring M.carrier N.carrier
      f.toLinearMap
    horizontal := fun x ↦
      (CompletedConnection.baseChange_baseChangeModuleMap p R.ring R'.ring M.carrier N.carrier
        (R.Om 1) (R'.Om 1) R'.diff (g.psi 1) M.nabla N.nabla R'.diff_add R'.diff_mul g.psi_diff
        f.toLinearMap (fun m ↦ (f.horizontal m).trans
          (CompletedConnection.valuesMap_eq p R.ring (R.Om 1) M.carrier N.carrier
            f.toLinearMap (M.nabla m)).symm) x).trans
        (CompletedConnection.valuesMap_eq p R'.ring (R'.Om 1) _ _ _ _) }

/-- **Naturality of the base change map in horizontal maps.** -/
theorem baseChangeHom_naturality (g : FormsData.Hom R R') {M N : ConnModule R} (f : Hom M N) :
    M.baseChangeHom g ≫ complexMap (baseChangeMap g f) = complexMap f ≫ N.baseChangeHom g := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine AddCommGrpCat.ext fun x ↦ ?_
  exact baseChangeTerm_horizontalTerm p R.ring R'.ring M.carrier N.carrier R.Om R'.Om g.psi
    f.toLinearMap i x

end Functoriality

section QuasiIso

variable {R' R'' : FormsData.{u} p}

/-- The base change of a horizontal map with bijective underlying map has bijective underlying
map. -/
theorem baseChangeMap_bijective (g : FormsData.Hom R R') {M N : ConnModule R} (f : Hom M N)
    (hf : Function.Bijective f.toLinearMap) :
    Function.Bijective (baseChangeMap g f).toLinearMap := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  set e := LinearEquiv.ofBijective f.toLinearMap hf
  have key : ∀ (X Y : Type u) [AddCommGroup X] [Module R.ring X] [AddCommGroup Y]
      [Module R.ring Y] (e : X ≃ₗ[R.ring] Y)
      (x : CompletedConnection.baseChangeCarrier p R.ring R'.ring X),
      CompletedConnection.baseChangeModuleMap p R.ring R'.ring Y X e.symm.toLinearMap
        (CompletedConnection.baseChangeModuleMap p R.ring R'.ring X Y e.toLinearMap x) = x := by
    intro X Y _ _ _ _ e x
    rw [← CompletedConnection.baseChangeModuleMap_comp,
      show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
        LinearMap.ext fun _ ↦ e.symm_apply_apply _,
      CompletedConnection.baseChangeModuleMap_id, LinearMap.id_apply]
  exact ⟨Function.LeftInverse.injective (key M.carrier N.carrier e),
    Function.RightInverse.surjective (key N.carrier M.carrier e.symm)⟩

/-- A morphism of complexes is a quasi-isomorphism as soon as it is a factor of two
quasi-isomorphisms, on the right of one and on the left of the other. -/
theorem quasiIso_of_comp_of_comp {K L M N : CochainComplex AddCommGrpCat.{u} ℕ} (f : K ⟶ L)
    (g : L ⟶ M) (h : M ⟶ N) [QuasiIso (f ≫ g)] [QuasiIso (g ≫ h)] : QuasiIso g := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h1 : IsIso (HomologicalComplex.homologyMap (f ≫ g) i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  have h2 : IsIso (HomologicalComplex.homologyMap (g ≫ h) i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; infer_instance
  rw [HomologicalComplex.homologyMap_comp] at h1 h2
  have : Epi (HomologicalComplex.homologyMap g i) := epi_of_epi
    (HomologicalComplex.homologyMap f i) _
  have : Mono (HomologicalComplex.homologyMap g i) := mono_of_mono _
    (HomologicalComplex.homologyMap h i)
  exact isIso_of_mono_of_epi _

/-- The base change along a composite is a quasi-isomorphism exactly when the composite of the two
base changes is. -/
theorem quasiIso_baseChangeHom_comp_iff (g : FormsData.Hom R R') (g' : FormsData.Hom R' R'')
    (M : ConnModule R) :
    QuasiIso (M.baseChangeHom (g'.comp g)) ↔
      QuasiIso (M.baseChangeHom g ≫ (M.baseChange g).baseChangeHom g') := by
  rw [← baseChangeHom_comp g g' M, ← Category.assoc, quasiIso_iff_comp_right]

/-- The base change along a morphism equal to the identity is a quasi-isomorphism. -/
theorem quasiIso_baseChangeHom_of_eq_id {g : FormsData.Hom R R} (hg : g = FormsData.Hom.id R)
    (M : ConnModule R) : QuasiIso (M.baseChangeHom g) := by
  subst hg
  infer_instance

/-- If the base change along `g` and along `g' ∘ g` are quasi-isomorphisms, so is the base change
along `g'` of the base change along `g`. -/
private theorem quasiIso_baseChange_baseChangeHom (g : FormsData.Hom R R')
    (g' : FormsData.Hom R' R'') (M : ConnModule R) [QuasiIso (M.baseChangeHom g)]
    [QuasiIso (M.baseChangeHom (g'.comp g))] : QuasiIso ((M.baseChange g).baseChangeHom g') := by
  have := (quasiIso_baseChangeHom_comp_iff g g' M).1 inferInstance
  exact quasiIso_of_comp_left (M.baseChangeHom g) _

/-- **The retract step of the proof of [Stacks, Lemma 60.21.4, Tag 07LH]**: for morphisms
`a : D → D'` and `b : D' → D` with `a ∘ b = id`, the base change along `a` is a
quasi-isomorphism as soon as the base change along the round trip `b ∘ a` is. -/
theorem quasiIso_baseChangeHom_of_retract (a : FormsData.Hom R R') (b : FormsData.Hom R' R)
    (hab : a.comp b = FormsData.Hom.id R') (M : ConnModule R)
    [hρ : QuasiIso (M.baseChangeHom (b.comp a))] : QuasiIso (M.baseChangeHom a) := by
  have h1 : QuasiIso (M.baseChangeHom a ≫ (M.baseChange a).baseChangeHom b) :=
    (quasiIso_baseChangeHom_comp_iff a b M).1 hρ
  have h2 : QuasiIso ((M.baseChange a).baseChangeHom b ≫
      ((M.baseChange a).baseChange b).baseChangeHom a) :=
    (quasiIso_baseChangeHom_comp_iff b a (M.baseChange a)).1
      (quasiIso_baseChangeHom_of_eq_id hab _)
  have := quasiIso_of_comp_of_comp (M.baseChangeHom a) ((M.baseChange a).baseChangeHom b)
    (((M.baseChange a).baseChange b).baseChangeHom a)
  exact quasiIso_of_comp_right _ ((M.baseChange a).baseChangeHom b)

/-- **Transport of quasi-isomorphy along a horizontal isomorphism of base changes.**  If two
base changes `σ^* M ≅ δ^* M` are identified by a horizontal isomorphism `Θ`, then base changing
further along any `w` is a quasi-isomorphism out of one exactly when it is out of the other. -/
theorem quasiIso_baseChangeHom_of_horizontalIso {M N : ConnModule R} (Θ : Hom M N)
    (hΘ : Function.Bijective Θ.toLinearMap) (w : FormsData.Hom R R')
    [QuasiIso (M.baseChangeHom w)] : QuasiIso (N.baseChangeHom w) := by
  have := isIso_complexMap Θ hΘ
  have := isIso_complexMap (baseChangeMap w Θ) (baseChangeMap_bijective w Θ hΘ)
  have h := baseChangeHom_naturality w Θ
  have : QuasiIso (M.baseChangeHom w ≫ complexMap (baseChangeMap w Θ)) := inferInstance
  rw [h] at this
  exact quasiIso_of_comp_left (complexMap Θ) _

/-- **The stratification step of the proof of [Stacks, Lemma 60.21.4, Tag 07LH].**  Let
`σ, δ : D₀ → D₁` be two morphisms with a common retraction `s`, and suppose the two base changes
`σ^* M` and `δ^* M` of a module with integrable connection are identified by a horizontal
isomorphism `Θ` and the base change along `σ` is a quasi-isomorphism.  Then for every morphism
`w : D₁ → E`, the base change along `w ∘ δ` is a quasi-isomorphism as soon as the base change
along `w ∘ σ` is. -/
theorem quasiIso_baseChangeHom_comp_of_stratification {R₁ E : FormsData.{u} p}
    (σ δ : FormsData.Hom R R₁) (s : FormsData.Hom R₁ R) (hsσ : s.comp σ = FormsData.Hom.id R)
    (hsδ : s.comp δ = FormsData.Hom.id R) (M : ConnModule R)
    (Θ : Hom (M.baseChange σ) (M.baseChange δ)) (hΘ : Function.Bijective Θ.toLinearMap)
    [hσ : QuasiIso (M.baseChangeHom σ)] (w : FormsData.Hom R₁ E)
    [hwσ : QuasiIso (M.baseChangeHom (w.comp σ))] : QuasiIso (M.baseChangeHom (w.comp δ)) := by
  -- the base change along `δ` is a quasi-isomorphism
  have : QuasiIso (M.baseChangeHom (s.comp σ)) := quasiIso_baseChangeHom_of_eq_id hsσ M
  have : QuasiIso ((M.baseChange σ).baseChangeHom s) := quasiIso_baseChange_baseChangeHom σ s M
  have : QuasiIso ((M.baseChange δ).baseChangeHom s) :=
    quasiIso_baseChangeHom_of_horizontalIso Θ hΘ s
  have : QuasiIso (M.baseChangeHom δ ≫ (M.baseChange δ).baseChangeHom s) :=
    (quasiIso_baseChangeHom_comp_iff δ s M).1 (quasiIso_baseChangeHom_of_eq_id hsδ M)
  have : QuasiIso (M.baseChangeHom δ) :=
    quasiIso_of_comp_right _ ((M.baseChange δ).baseChangeHom s)
  -- the base change along `w`
  have : QuasiIso ((M.baseChange σ).baseChangeHom w) := quasiIso_baseChange_baseChangeHom σ w M
  have : QuasiIso ((M.baseChange δ).baseChangeHom w) :=
    quasiIso_baseChangeHom_of_horizontalIso Θ hΘ w
  exact (quasiIso_baseChangeHom_comp_iff δ w M).2 inferInstance

/-- **The homotopy argument of the proof of [Stacks, Lemma 60.21.4, Tag 07LH]**, assembled.

Let `σ, δ : D₀ → D₁` be two coprojections with a common retraction `s`, identified on the base
changes of `M` by a horizontal isomorphism `Θ`, with the base change along `σ` a
quasi-isomorphism.  Let `σₙ : D₀ → Dₙ` be a morphism along which the base change of `M` is a
quasi-isomorphism, `a : Dₙ → D'` and `b : D' → Dₙ` a retract (`a ∘ b = id`), and `w : D₁ → Dₙ` a
morphism with `w ∘ σ = σₙ` and `w ∘ δ = b ∘ a ∘ σₙ`.  Then the base change of `M` along
`a ∘ σₙ : D₀ → D'` is a quasi-isomorphism. -/
theorem quasiIso_baseChangeHom_of_retract_of_stratification {R₁ Rₙ R' : FormsData.{u} p}
    (σ δ : FormsData.Hom R R₁) (s : FormsData.Hom R₁ R) (hsσ : s.comp σ = FormsData.Hom.id R)
    (hsδ : s.comp δ = FormsData.Hom.id R) (M : ConnModule R)
    (Θ : Hom (M.baseChange σ) (M.baseChange δ)) (hΘ : Function.Bijective Θ.toLinearMap)
    [QuasiIso (M.baseChangeHom σ)] (σₙ : FormsData.Hom R Rₙ) [QuasiIso (M.baseChangeHom σₙ)]
    (a : FormsData.Hom Rₙ R') (b : FormsData.Hom R' Rₙ) (hab : a.comp b = FormsData.Hom.id R')
    (w : FormsData.Hom R₁ Rₙ) (hwσ : w.comp σ = σₙ) (hwδ : w.comp δ = (b.comp a).comp σₙ) :
    QuasiIso (M.baseChangeHom (a.comp σₙ)) := by
  subst hwσ
  have : QuasiIso (M.baseChangeHom (w.comp δ)) :=
    quasiIso_baseChangeHom_comp_of_stratification σ δ s hsσ hsδ M Θ hΘ w
  rw [hwδ] at this
  have : QuasiIso ((M.baseChange (w.comp σ)).baseChangeHom (b.comp a)) :=
    quasiIso_baseChange_baseChangeHom (w.comp σ) (b.comp a) M
  have : QuasiIso ((M.baseChange (w.comp σ)).baseChangeHom a) :=
    quasiIso_baseChangeHom_of_retract a b hab _
  exact (quasiIso_baseChangeHom_comp_iff (w.comp σ) a M).2 inferInstance

end QuasiIso

end ConnModule

end FormsData

end Crystalline

end
