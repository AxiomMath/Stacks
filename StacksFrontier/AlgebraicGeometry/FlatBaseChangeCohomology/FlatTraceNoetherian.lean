module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FiniteLocallyFreeCanonical

/-!
# Flat base change on sections over every open of a Noetherian scheme, and traces

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine and `Γ(S, ⊤) ⟶ Γ(T, ⊤)` flat, and let
`F` be a quasi-coherent `𝒪_X`-module. When every open of `X` is quasi-compact — for instance when
`X` is Noetherian — the canonical comparison

  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`,  `b ⊗ a ↦ b • p^* a`,

is bijective for **every** open `U` of `X`. This is [Stacks, Tag 02KH] part (2) in degree zero,
read on each open; `StacksFrontier/AlgebraicGeometry/SectionsIso/QuasicoherentArbitraryOpen.lean`
proves the same with no hypothesis on `X` when `Γ(T, ⊤)` is moreover finitely presented, by
covering `U` with all of its affine opens. Here `U` is covered by finitely many, so that tensoring
with the flat `Γ(T, ⊤)` commutes with the (finite) products in the sheaf condition.

With this, the trace of a `Γ(S, ⊤)`-linear functional `f` on `Γ(T, ⊤)`, the morphism
`p_* p^* F ⟶ F`, `b ⊗ x ↦ f(b) x`, of `Stacks.Tag0CKW.trace` is available for an arbitrary flat
`q`, and in particular for the base change along an arbitrary extension of fields.

## Main results

* `Stacks.FlatTrace.bijective_sectionsBaseChangeMap_of_flat`: the comparison is bijective over
  every open, for `X` all of whose opens are quasi-compact.
* `Stacks.FlatTrace.trace`: the trace `p_* p^* F ⟶ F` of a functional on `Γ(T, ⊤)`.
* `Stacks.FlatTrace.twistedUnit_comp_trace`: the twisted unit `x ↦ b • p^* x` followed by the trace
  of `f` is multiplication by `f(b)`.
* `Stacks.FlatTrace.eq_zero_of_forall_comp_trace_eq_zero`: the traces of all functionals are
  jointly faithful, when `Γ(S, ⊤)` is a field.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Tag0CKW (homOfSections homOfSections_app twistedUnit twistedUnit_app pushforwardSection
  baseResHom_trans pullbackBaseResHom_trans affineOpensIn le_iSup_affineOpensIn sectionsSmul)
open scoped TensorProduct

universe u

namespace Stacks.FlatTrace

/-! ### Base change of a finite product, componentwise -/

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type u} (M : ι → Type u) [∀ a, AddCommGroup (M a)] [∀ a, Module A (M a)]

/-- The `a`-th component of `B ⊗_A N ⟶ ∏ B ⊗_A M a` applied to `(1 ⊗ (f b)_b)(w)` is
`(1 ⊗ f a)(w)`. -/
theorem piRightHom_lTensor_pi_apply {N : Type u} [AddCommGroup N] [Module A N]
    (f : ∀ a, N →ₗ[A] M a) (a : ι) (w : B ⊗[A] N) :
    TensorProduct.piRightHom A B B M (LinearMap.lTensor B (LinearMap.pi f) w) a =
      LinearMap.lTensor B (f a) w := by
  induction w with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- For `g : M a ⟶ P`, the map `1 ⊗ (g ∘ proj a)` on `B ⊗_A ∏ M b` is `1 ⊗ g` applied to the
`a`-th component of the comparison `B ⊗_A ∏ M b ⟶ ∏ B ⊗_A M b`. -/
theorem lTensor_comp_proj_apply_piRightHom {P : Type u} [AddCommGroup P] [Module A P] (a : ι)
    (g : M a →ₗ[A] P) (z : B ⊗[A] (∀ b, M b)) :
    LinearMap.lTensor B (g ∘ₗ (LinearMap.proj a : (∀ b, M b) →ₗ[A] M a)) z =
      LinearMap.lTensor B g (TensorProduct.piRightHom A B B M z a) := by
  induction z with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **The functionals on a vector space detect the elements of its tensor products**: over a field
`A`, an element `z` of `B ⊗_A M` with `(f ⊗ 1)(z) = 0` for every `A`-linear `f : B ⟶ A` is zero. -/
theorem eq_zero_of_forall_lid_rTensor_eq_zero_of_isField (hA : IsField A) {N : Type u}
    [AddCommGroup N] [Module A N] (z : B ⊗[A] N)
    (hz : ∀ f : B →ₗ[A] A, TensorProduct.lid A N (LinearMap.rTensor N f z) = 0) : z = 0 := by
  classical
  let : Field A := hA.toField
  let b := Module.Free.chooseBasis A B
  refine (TensorProduct.equivFinsuppOfBasisLeft b).injective ?_
  rw [map_zero]
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  exact hz (b.coord i)

/-- Over a finite index type, the comparison `B ⊗_A ∏ M a ⟶ ∏ B ⊗_A M a` is bijective. -/
theorem bijective_piRightHom_of_finite [Finite ι] :
    Function.Bijective (TensorProduct.piRightHom A B B M) := by
  classical
  have := Fintype.ofFinite ι
  exact (TensorProduct.piRight A B B M).bijective

/-- Over a finite index type, `1 ⊗ (f a)_a` kills `w` as soon as each `1 ⊗ f a` does. -/
private theorem lTensor_pi_eq_zero_of_forall [Finite ι] {N : Type u} [AddCommGroup N]
    [Module A N] (f : ∀ a, N →ₗ[A] M a) (w : B ⊗[A] N)
    (h : ∀ a, LinearMap.lTensor B (f a) w = 0) : LinearMap.lTensor B (LinearMap.pi f) w = 0 := by
  refine (bijective_piRightHom_of_finite M).1 ?_
  rw [map_zero]
  funext a
  rw [piRightHom_lTensor_pi_apply, h a]
  rfl

end Algebra

/-! ### A finite affine cover of a quasi-compact open -/

/-- A quasi-compact open is covered by finitely many of the affine opens it contains. -/
theorem exists_finite_affineOpensIn {X : Scheme.{u}} (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ s : Finset (affineOpensIn U), U ≤ ⨆ a : s, ((a : affineOpensIn U).1 : X.Opens) := by
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun a : affineOpensIn U => ((a.1 : X.Opens) : Set X))
    (fun a => (a.1 : X.Opens).isOpen) (fun x hx => by
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (le_iSup_affineOpensIn U hx)
      exact Set.mem_iUnion.mpr ⟨a, ha⟩)
  refine ⟨s, fun x hx => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

/-! ### Injectivity and bijectivity over every open -/

section

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-- **The canonical degree-zero comparison is injective over a quasi-compact open**, for a flat
`Γ(S, ⊤) ⟶ Γ(T, ⊤)`. -/
theorem injective_sectionsBaseChangeMap_of_flat (H : IsPullback p k iX q) [IsAffine S]
    [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Injective (sectionsBaseChangeMap H F U) := by
  classical
  let algAB := baseAlgebra q
  let modAF : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  let modAG : ∀ W : X.Opens,
      Module Γ(S, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let modBG : ∀ W : X.Opens,
      Module Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let towerG : ∀ W : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hq
  obtain ⟨s, hs⟩ := exists_finite_affineOpensIn U hU
  set ι := (s : Type u)
  set V : ι → X.Opens := fun a => ((a : affineOpensIn U).1 : X.Opens)
  have hVle : ∀ a : ι, V a ≤ U := fun a => (a : affineOpensIn U).2
  set r : Γ(F, U) →ₗ[Γ(S, ⊤)] (∀ a : ι, Γ(F, V a)) :=
    LinearMap.pi (fun a => baseResHom iX F (hVle a)) with hrdef
  have hr : Function.Injective r := fun s t hst =>
    TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
      V U (fun a => homOfLE (hVle a)) hs s t fun a => congrFun hst a
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine Module.Flat.lTensor_preserves_injective_linearMap r hr ?_
  rw [map_zero]
  refine lTensor_pi_eq_zero_of_forall (fun a : ι => ↑Γ(F, V a)) _ _ fun a => ?_
  refine (bijective_sectionsBaseChangeMap_of_isAffineOpen H F
    ((a : affineOpensIn U).1.2)).1 ?_
  rw [map_zero, sectionsBaseChangeMap_comm_res H F (hVle a) z, hz, map_zero]

/-- **Local preimages of a section form a cocycle**, for a flat `Γ(S, ⊤) ⟶ Γ(T, ⊤)` and a scheme
`X` all of whose opens are quasi-compact: if `zₐ` is a preimage of `t|_{p⁻¹Vₐ}` under the
comparison over each `Vₐ`, then the base change of the difference of the two restrictions to the
`Vₐ ⊓ Vᵦ` kills the family `(zₐ)`. -/
private theorem lTensor_pi_baseResHom_sub_symm_eq_zero_of_flat (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hX : ∀ W : X.Opens, IsCompact (W : Set X)) {ι : Type u} [Finite ι] {U : X.Opens}
    (V : ι → X.Opens) (hVle : ∀ a, V a ≤ U) (t : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
    ∀ w : Γ(T, ⊤) ⊗[Γ(S, ⊤)] (∀ a, ↑Γ(F, V a)),
      (∀ a, sectionsBaseChangeMap H F (V a)
        (TensorProduct.piRightHom Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) (fun a : ι => ↑Γ(F, V a)) w a) =
          pullbackBaseResHom k p F (hVle a) t) →
      LinearMap.lTensor Γ(T, ⊤) (LinearMap.pi fun ab : ι × ι =>
          baseResHom iX F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) ∘ₗ LinearMap.proj ab.1 -
            baseResHom iX F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) ∘ₗ LinearMap.proj ab.2)
        w = 0 := by
  let := baseAlgebra q
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  intro w hw
  refine lTensor_pi_eq_zero_of_forall (fun a : ι × ι => ↑Γ(F, V a.1 ⊓ V a.2)) _ _ fun ab => ?_
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
    lTensor_comp_proj_apply_piRightHom (fun a : ι => (Γ(F, V a) : Type u)) ab.1,
    lTensor_comp_proj_apply_piRightHom (fun a : ι => (Γ(F, V a) : Type u)) ab.2]
  refine injective_sectionsBaseChangeMap_of_flat H F hq (V ab.1 ⊓ V ab.2) (hX _) ?_
  rw [sectionsBaseChangeMap_comm_res H F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1),
    sectionsBaseChangeMap_comm_res H F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2),
    hw ab.1, hw ab.2, pullbackBaseResHom_trans, pullbackBaseResHom_trans]

/-- **The canonical degree-zero comparison is bijective over every open**, for a flat
`Γ(S, ⊤) ⟶ Γ(T, ⊤)` and a scheme `X` all of whose opens are quasi-compact (a Noetherian scheme,
for instance). -/
theorem bijective_sectionsBaseChangeMap_of_flat (H : IsPullback p k iX q) [IsAffine S]
    [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hX : ∀ W : X.Opens, IsCompact (W : Set X)) (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  classical
  let algAB := baseAlgebra q
  let modAF : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  let modAG : ∀ W : X.Opens,
      Module Γ(S, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let modBG : ∀ W : X.Opens,
      Module Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let towerG : ∀ W : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hq
  refine ⟨injective_sectionsBaseChangeMap_of_flat H F hq U (hX U), fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_finite_affineOpensIn U (hX U)
  set ι := (s : Type u)
  set V : ι → X.Opens := fun a => ((a : affineOpensIn U).1 : X.Opens)
  have hVle : ∀ a : ι, V a ≤ U := fun a => (a : affineOpensIn U).2
  have hcover : p ⁻¹ᵁ U ≤ ⨆ a : ι, p ⁻¹ᵁ V a := by
    rw [← Scheme.Hom.preimage_iSup]
    exact Scheme.Hom.preimage_mono p hs
  choose z hz using fun a : ι =>
    (bijective_sectionsBaseChangeMap_of_isAffineOpen H F ((a : affineOpensIn U).1.2)).2
      (pullbackBaseResHom k p F (hVle a) t)
  obtain ⟨w₀, rfl⟩ := (bijective_piRightHom_of_finite (A := Γ(S, ⊤)) (B := Γ(T, ⊤))
    (fun a : ι => ↑Γ(F, V a))).2 z
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact Γ(T, ⊤)
    (Stacks.Tag0CKW.exact_pi_baseResHom iX F V hVle hs) w₀).mp
    (lTensor_pi_baseResHom_sub_symm_eq_zero_of_flat H F hq hX V hVle t w₀ hz)
  have hwa : ∀ a : ι, LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F (hVle a)) w =
      TensorProduct.piRightHom Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) (fun a : ι => ↑Γ(F, V a)) w₀ a := by
    intro a
    rw [← piRightHom_lTensor_pi_apply (fun a : ι => ↑Γ(F, V a))
      (fun a => baseResHom iX F (hVle a)) a w, hw]
  refine ⟨w, TopCat.Sheaf.eq_of_locally_eq'
    ⟨((Scheme.Modules.pullback p).obj F).presheaf,
      Scheme.Modules.isSheaf ((Scheme.Modules.pullback p).obj F)⟩
    (fun a : ι => p ⁻¹ᵁ V a) (p ⁻¹ᵁ U)
    (fun a => homOfLE (Scheme.Hom.preimage_mono p (hVle a))) hcover
    (sectionsBaseChangeMap H F U w) t fun a => ?_⟩
  show pullbackBaseResHom k p F (hVle a) (sectionsBaseChangeMap H F U w) = _
  rw [← sectionsBaseChangeMap_comm_res H F (hVle a) w, hwa a, hz a]
  rfl

end

section Trace

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
  (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
  (hX : ∀ W : X.Opens, IsCompact (W : Set X))
  (F : X.Modules) [F.IsQuasicoherent]

/-- The canonical comparison `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ≅ Γ(p^* F, p⁻¹U)`, over an arbitrary
open of `X`. -/
def sectionsBaseChangeEquiv (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃ₗ[Γ(T, ⊤)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  LinearEquiv.ofBijective (sectionsBaseChangeMap H F U)
    (bijective_sectionsBaseChangeMap_of_flat H F hq hX U)

/-- The comparison `sectionsBaseChangeEquiv` sends `b ⊗ x` to `b • p^* x`. -/
theorem sectionsBaseChangeEquiv_tmul (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    sectionsBaseChangeEquiv H hq hX F U (b ⊗ₜ[Γ(S, ⊤)] x) = b • pullbackUnitSections p F U x :=
  sectionsBaseChangeMap_tmul H F U b x

/-- The inverse of `sectionsBaseChangeEquiv` is `Γ(X, U)`-linear: it sends `p^♯(r) • y` to
`(1 ⊗ r)` applied to the inverse image of `y`. -/
theorem sectionsBaseChangeEquiv_symm_smul (U : X.Opens) (r : Γ(X, U))
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (sectionsBaseChangeEquiv H hq hX F U).symm ((p.app U).hom r • y) =
      LinearMap.lTensor Γ(T, ⊤) (sectionsSmul F U r)
        ((sectionsBaseChangeEquiv H hq hX F U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquiv H hq hX F U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  induction z with
  | tmul b x =>
    rw [LinearMap.lTensor_tmul, sectionsBaseChangeEquiv_tmul, sectionsBaseChangeEquiv_tmul]
    show (p.app U).hom r • (b • _) = b • pullbackUnitSections p F U (r • x)
    rw [pullbackUnitSections_smul p F U r x]
    show (p.app U).hom r • ((k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        pullbackUnitSections p F U x) =
      (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        ((p.app U).hom r • pullbackUnitSections p F U x)
    rw [← mul_smul, ← mul_smul, mul_comm]
  | add z w hz hw => rw [map_add, smul_add, hz, hw, map_add, map_add]

/-- The inverse of `sectionsBaseChangeEquiv` commutes with restriction from `U` to `V ≤ U`. -/
theorem sectionsBaseChangeEquiv_symm_res {U V : X.Opens} (h : V ≤ U)
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule iX F V
    (sectionsBaseChangeEquiv H hq hX F V).symm
        (((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p h)).op y) =
      LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F h)
        ((sectionsBaseChangeEquiv H hq hX F U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule iX F V
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquiv H hq hX F U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  exact (sectionsBaseChangeMap_comm_res H F h z).symm

/-- The trace of a `Γ(S, ⊤)`-linear functional `f` on `Γ(T, ⊤)`, on the sections of
`p_* p^* F` over one open: `b ⊗ x ↦ f(b) x` read through the comparison. -/
def traceSections (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) (U : X.Opens) :
    Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U) →ₗ[Γ(X, U)]
      Γ(F, U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  { toFun := fun y => TensorProduct.lid Γ(S, ⊤) Γ(F, U)
      (LinearMap.rTensor Γ(F, U) f
        ((sectionsBaseChangeEquiv H hq hX F U).symm (pushforwardSection y)))
    map_add' := fun y y' => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H hq hX F U).symm
            (pushforwardSection y + pushforwardSection y'))) = _
      simp only [map_add]
    map_smul' := fun r y => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H hq hX F U).symm
            ((p.app U).hom r • pushforwardSection y))) = r • _
      rw [sectionsBaseChangeEquiv_symm_smul]
      induction (sectionsBaseChangeEquiv H hq hX F U).symm (pushforwardSection y) with
      | tmul b x =>
        simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        change (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • (r • x) =
          r • ((iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x)
        rw [← mul_smul, ← mul_smul, mul_comm]
      | add z w hz hw => simp only [map_add, smul_add, hz, hw] }

/-- The trace `traceSections` sends `b • p^* x` to `f(b) • x`. -/
theorem traceSections_apply_tmul (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    traceSections H hq hX F f U (b • pullbackUnitSections p F U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  show TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
    ((sectionsBaseChangeEquiv H hq hX F U).symm (b • pullbackUnitSections p F U x))) = _
  rw [← sectionsBaseChangeEquiv_tmul H hq hX F U b x, LinearEquiv.symm_apply_apply,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- The trace of a functional on `Γ(T, ⊤)`, as a morphism of `𝒪_X`-modules `p_* p^* F ⟶ F`. -/
def trace (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ⟶ F :=
  homOfSections (traceSections H hq hX F f) fun {U V} i y => by
    let := baseAlgebra q
    let := baseModule iX F U
    let := baseModule iX F V
    change TensorProduct.lid Γ(S, ⊤) Γ(F, V) (LinearMap.rTensor Γ(F, V) f
      ((sectionsBaseChangeEquiv H hq hX F V).symm (((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p (leOfHom i))).op (pushforwardSection y)))) =
      F.presheaf.map i.op (TensorProduct.lid Γ(S, ⊤) Γ(F, U)
        (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H hq hX F U).symm (pushforwardSection y))))
    rw [sectionsBaseChangeEquiv_symm_res]
    induction (sectionsBaseChangeEquiv H hq hX F U).symm (pushforwardSection y) with
    | tmul b x =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact ((baseResHom iX F (leOfHom i)).map_smul (f b) x).symm
    | add z w hz hw => simp only [map_add, hz, hw]

/-- On sections over `U`, the trace of `f` sends the twisted unit `b • p^* x` to `f(b) • x`. -/
theorem trace_app_twistedUnit_app (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (trace H hq hX F f).app U ((twistedUnit k p F b).app U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [twistedUnit_app]
  exact traceSections_apply_tmul H hq hX F f U b x

/-- **The trace undoes the twisted unit up to the functional.** `x ↦ b • p^* x` followed by
the trace of `f` is multiplication by `f(b)`. -/
theorem twistedUnit_comp_trace (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) :
    twistedUnit k p F b ≫ trace H hq hX F f =
      (Scheme.smulEnd X ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b))).asHom.app F := by
  let := baseAlgebra q
  ext U x
  let := baseModule iX F U
  refine (trace_app_twistedUnit_app H hq hX F f b U x).trans ?_
  show (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x =
    X.presheaf.map (isTerminalTop.from U).op ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b)) • x
  congr 1
  exact (congrArg (fun m : Γ(S, ⊤) ⟶ Γ(X, U) => m.hom (f b))
    (Scheme.Hom.appLE_map iX (le_preimage_top iX ⊤) (isTerminalTop.from U).op)).symm

/-- **The traces of all functionals are jointly faithful** when `Γ(S, ⊤)` is a field: a morphism
into `p_* p^* F` killed by every trace is zero. On the sections over an open `U` the trace of `f`
is `f ⊗ 1` on `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U)`, and the coordinate functionals of a basis of the
vector space `Γ(T, ⊤)` detect an element of that tensor product. -/
theorem eq_zero_of_forall_comp_trace_eq_zero (hS : IsField Γ(S, ⊤)) {M : X.Modules}
    (j : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F))
    (hj : ∀ f : (letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)), j ≫ trace H hq hX F f = 0) :
    j = 0 := by
  let := baseAlgebra q
  ext U m
  let := baseModule iX F U
  set z := (sectionsBaseChangeEquiv H hq hX F U).symm (pushforwardSection (j.app U m))
  have hz0 : z = 0 := eq_zero_of_forall_lid_rTensor_eq_zero_of_isField hS z fun f =>
    congrArg (fun φ => φ.app U m) (hj f)
  exact (sectionsBaseChangeEquiv H hq hX F U).symm.map_eq_zero_iff.mp hz0

end Trace

end Stacks.FlatTrace

end
