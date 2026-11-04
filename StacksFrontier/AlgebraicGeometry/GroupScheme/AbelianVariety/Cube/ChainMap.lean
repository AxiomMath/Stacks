module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Generators

/-!
# The theorem of the cube: the map from the chart complex to the faces

Let `A` be a group scheme over a field, `P = (A × A) × A`, `N` a sheaf of modules on `P`, and
`V ⊆ A` an affine open with ring `R`. The two faces `face₁ : (y, z) ↦ (e, y, z)` and
`face₂ : (x, z) ↦ (x, e, z)` of `P` lie over the third factor. Given generators `g₁`, `g₂` of
the pullbacks of `N` to the two faces which agree along the line `z ↦ (e, e, z)`, restriction to
the faces followed by division by the generators is a map of complexes of `R`-modules

  `C_V⁰ ⟶ C_V¹`  to  `D⁰ ⟶ D¹`,

from the alternating Čech complex of `N` over the chart to the two-term complex of functions on
the faces of `Stacks.Cube.targetD` (`Stacks.Cube.phi₀`, `Stacks.Cube.phi₁`,
`Stacks.Cube.phi₁_comp_d₀`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-! ### The faces in coordinates -/

variable (A) in
/-- The face `(y, z) ↦ (e, y, z)`. -/
noncomputable abbrev face₁ : B A ⟶ P A := (Stacks.Groupoids.cubeFace₁ A).left

variable (A) in
/-- The face `(x, z) ↦ (x, e, z)`. -/
noncomputable abbrev face₂ : B A ⟶ P A := (Stacks.Groupoids.cubeFace₂ A).left

/-- The first coordinate of `face₁` is the identity `e`. -/
@[reassoc (attr := simp)]
theorem face₁_q_bx : face₁ A ≫ q A ≫ bx A = bx A ≫ A.hom ≫ eA := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₁_cubeProj₁ A)
  simp only [Stacks.Groupoids.cubeProj₁, CategoryTheory.Hom.one_def, Over.comp_left,
    Over.fst_left, Over.toUnit_left, Over.tensorObj_hom, Category.assoc] at h
  exact h

/-- The second coordinate of `face₁ (y, z)` is `y`. -/
@[reassoc (attr := simp)]
theorem face₁_q_bz : face₁ A ≫ q A ≫ bz A = bx A := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₁_cubeProj₂ A)
  simp only [Stacks.Groupoids.cubeProj₂, Over.comp_left, Over.fst_left, Over.snd_left] at h
  exact h

/-- The third coordinate of `face₁ (y, z)` is `z`. -/
@[reassoc (attr := simp)]
theorem face₁_r : face₁ A ≫ r A = bz A := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₁_cubeProj₃ A)
  simp only [Stacks.Groupoids.cubeProj₃, Over.snd_left] at h
  exact h

/-- The first coordinate of `face₂ (x, z)` is `x`. -/
@[reassoc (attr := simp)]
theorem face₂_q_bx : face₂ A ≫ q A ≫ bx A = bx A := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₂_cubeProj₁ A)
  simp only [Stacks.Groupoids.cubeProj₁, Over.comp_left, Over.fst_left] at h
  exact h

/-- The second coordinate of `face₂` is the identity `e`. -/
@[reassoc (attr := simp)]
theorem face₂_q_bz : face₂ A ≫ q A ≫ bz A = bx A ≫ A.hom ≫ eA := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₂_cubeProj₂ A)
  simp only [Stacks.Groupoids.cubeProj₂, CategoryTheory.Hom.one_def, Over.comp_left,
    Over.fst_left, Over.snd_left, Over.toUnit_left, Over.tensorObj_hom, Category.assoc] at h
  exact h

/-- The third coordinate of `face₂ (x, z)` is `z`. -/
@[reassoc (attr := simp)]
theorem face₂_r : face₂ A ≫ r A = bz A := by
  have h := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₂_cubeProj₃ A)
  simp only [Stacks.Groupoids.cubeProj₃, Over.snd_left] at h
  exact h

/-- The two faces agree on the line `z ↦ (e, e, z)`. -/
theorem σe_face₁ : σe (A := A) ≫ face₁ A = σe ≫ face₂ A := by
  have he : σe (A := A) ≫ bx A ≫ A.hom ≫ eA (A := A) = A.hom ≫ eA (A := A) := by
    rw [σe_bx_assoc, ← Category.assoc eA, eA_hom (A := A), Category.id_comp]
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · simp only [Category.assoc]
    show σe ≫ face₁ A ≫ q A ≫ bx A = σe ≫ face₂ A ≫ q A ≫ bx A
    rw [face₁_q_bx, face₂_q_bx, he, σe_bx]
  · simp only [Category.assoc]
    show σe ≫ face₁ A ≫ q A ≫ bz A = σe ≫ face₂ A ≫ q A ≫ bz A
    rw [face₁_q_bz, face₂_q_bz, he, σe_bx]
  · simp only [Category.assoc]
    show σe ≫ face₁ A ≫ r A = σe ≫ face₂ A ≫ r A
    rw [face₁_r, face₂_r]

/-! ### The faces map the face opens into the chart cover -/

section Opens

variable {ι : Type u} (U : ι → A.left.Opens) (V : A.left.Opens) {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)

omit [GrpObj A] in
/-- A point `x` of `P A` with third coordinate in `V`, lying in an open `O'` of `PV V`, lies in the
image of `O'` in `P A`. -/
theorem mem_image_PV {O' : (PV V).toScheme.Opens} (x : P A) (hx : r A x ∈ V)
    (h : (⟨x, hx⟩ : (PV V).toScheme) ∈ O') : x ∈ (PV V).ι ''ᵁ O' :=
  ⟨⟨x, hx⟩, h, rfl⟩

omit [GrpObj A] in
/-- A point of `PV V` lies in the chart open indexed by `(a, b)` if and only if its first
coordinate lies in `U a` and its second coordinate lies in `U b`. -/
theorem mem_chartCover (x : P A) (hx : r A x ∈ V) (ab : ι × ι) :
    (⟨x, hx⟩ : (PV V).toScheme) ∈ chartCover U V ab ↔
      bx A (q A x) ∈ U ab.1 ∧ bz A (q A x) ∈ U ab.2 := Iff.rfl

/-- If a coordinate of `f x` is the identity `e`, it lies in `U a₀`. -/
private theorem bx_mem_of_comp_eq_e (ha : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) {f : B A ⟶ P A}
    {c : B A ⟶ A.left} (hf : f ≫ q A ≫ c = bx A ≫ A.hom ≫ eA) (x : B A) : c (q A (f x)) ∈ U a₀ := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply]
  have : A.hom (bx A x) ∈ eA (A := A) ⁻¹ᵁ U a₀ := by rw [ha]; trivial
  exact this

/-- A face open is contained in the preimage under a map `f` over the third factor of the
intersection of chart opens `c`, as soon as the coordinates of `f x` lie in the opens of `c`. -/
private theorem faceOpen_le_preimage_inter {A : Over (Spec (.of k))} {ι : Type u}
    (U : ι → A.left.Opens) (V : A.left.Opens) {f : B A ⟶ P A} (hf : f ≫ r A = bz A) {n : ℕ}
    (i : Fin n → ι) (c : Fin n → ι × ι)
    (h : ∀ x ∈ faceOpen V U i, ∀ m, bx A (q A (f x)) ∈ U (c m).1 ∧ bz A (q A (f x)) ∈ U (c m).2) :
    faceOpen V U i ≤ f ⁻¹ᵁ ((PV V).ι ''ᵁ CechCochains.inter (chartCover U V) c) := by
  intro x hx
  have hxV : r A (f x) ∈ V := by
    rw [← Scheme.Hom.comp_apply, hf]; exact hx.2
  exact mem_image_PV V _ hxV ((mem_inter (chartCover U V) _ _).mpr fun m =>
    (mem_chartCover U V _ hxV _).mpr (h x hx m))

include ha₀ in
/-- The face open indexed by `i` is contained in the preimage under `face₁` of the intersection of
the chart opens indexed by `(a₀, i m)`. -/
theorem le_face₁ {n : ℕ} (i : Fin n → ι) :
    faceOpen V U i ≤ face₁ A ⁻¹ᵁ ((PV V).ι ''ᵁ
      CechCochains.inter (chartCover U V) ((fun b => (a₀, b)) ∘ i)) :=
  faceOpen_le_preimage_inter U V face₁_r i ((fun b => (a₀, b)) ∘ i) fun x hx m =>
    ⟨bx_mem_of_comp_eq_e U ha₀ face₁_q_bx x, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, face₁_q_bz]
      exact (mem_inter U i _).mp hx.1 m⟩

include ha₀ in
/-- The face open indexed by `i` is contained in the preimage under `face₂` of the intersection of
the chart opens indexed by `(i m, a₀)`. -/
theorem le_face₂ {n : ℕ} (i : Fin n → ι) :
    faceOpen V U i ≤ face₂ A ⁻¹ᵁ ((PV V).ι ''ᵁ
      CechCochains.inter (chartCover U V) ((fun a => (a, a₀)) ∘ i)) := by
  refine faceOpen_le_preimage_inter U V face₂_r i ((fun a => (a, a₀)) ∘ i) fun x hx m => ?_
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, face₂_q_bx]
    exact (mem_inter U i _).mp hx.1 m
  · exact bx_mem_of_comp_eq_e U ha₀ face₂_q_bz x

end Opens

/-! ### The map of complexes -/

section Phi

attribute [local instance] faceModule

variable {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} (U : ι → A.left.Opens) {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) (N : (P A).Modules)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)

/-- The degree-`p` term of the chart complex. -/
noncomputable abbrev CX (p : ℕ) := (chartComplex hV U N).X p

/-- The restriction to the first face. -/
noncomputable def phiY (p : ℕ) : CX hV U N p →ₗ[chartRing V] FaceCochain V U p :=
  letI := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
  { toFun := fun x => faceMap N (face₁ A) hg₁ U (fun b => (a₀, b)) (le_face₁ U V ha₀) p x.1
    map_add' := fun x y => map_add _ x.1 y.1
    map_smul' := fun a x => faceMap_smul N (face₁ A) hg₁ hV U _ _ face₁_r p a x.1 }

/-- The restriction to the second face. -/
noncomputable def phiX (p : ℕ) : CX hV U N p →ₗ[chartRing V] FaceCochain V U p :=
  letI := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
  { toFun := fun x => faceMap N (face₂ A) hg₂ U (fun a => (a, a₀)) (le_face₂ U V ha₀) p x.1
    map_add' := fun x y => map_add _ x.1 y.1
    map_smul' := fun a x => faceMap_smul N (face₂ A) hg₂ hV U _ _ face₂_r p a x.1 }

/-- The map in degree zero. -/
noncomputable def phi₀ : CX hV U N 0 →ₗ[chartRing V] FaceCochain V U 0 × FaceCochain V U 0 :=
  (phiY hV U ha₀ N hg₁ 0).prod (phiX hV U ha₀ N hg₂ 0)

/-- The map in degree one. -/
noncomputable def phi₁ :
    CX hV U N 1 →ₗ[chartRing V] FaceCochain V U 1 × FaceCochain V U 1 × chartRing V :=
  (phiY hV U ha₀ N hg₁ 1).prod ((phiX hV U ha₀ N hg₂ 1).prod 0)

/-- The differential of the chart complex in degree zero. -/
noncomputable abbrev d₀ := ((chartComplex hV U N).d 0 1).hom

/-- The differential of the chart complex in degree one. -/
noncomputable abbrev d₁ := ((chartComplex hV U N).d 1 2).hom

omit [GrpObj A] in
/-- On underlying cochains, the differential of the chart complex is the Čech differential. -/
theorem d_apply_val (p : ℕ) (x : CX hV U N p) :
    (((chartComplex hV U N).d p (p + 1)).hom x).1 = CechCochains.cechD _ _ p x.1 := by
  rw [Stacks.CechBaseChange.d_eq]
  rfl

/-- The normalization of the two generators along the line `z ↦ (e, e, z)`. -/
def Normalized : Prop :=
  pulledGen₁ N σe (face₁ A) σe (face₂ A) σe_face₁ (g₁ := g₁) = pulledGen₂ N σe (face₂ A) (g₂ := g₂)

include hg₁ hg₂ in
/-- **The restriction to the faces is a map of complexes.** -/
theorem phi₁_comp_d₀ (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂)) :
    phi₁ hV U ha₀ N hg₁ hg₂ ∘ₗ d₀ hV U N = targetD V U ha₀ ∘ₗ phi₀ hV U ha₀ N hg₁ hg₂ := by
  have key : ∀ {j : B A ⟶ P A} {g} (hg : IsGen _ g) {sel} (hsel : ∀ {n : ℕ} (i : Fin n → ι),
      faceOpen V U i ≤ j ⁻¹ᵁ ((PV V).ι ''ᵁ CechCochains.inter (chartCover U V) (sel ∘ i)))
      (x : CX hV U N 0), faceMap N j hg U sel hsel 1 (((chartComplex hV U N).d 0 1).hom x).1 =
      faceD V U 0 (faceMap N j hg U sel hsel 0 x.1) := by
    intros
    rw [d_apply_val, faceD_faceMap]
  refine LinearMap.ext fun x => Prod.ext (key hg₁ (le_face₁ U V ha₀) x)
    (Prod.ext (key hg₂ (le_face₂ U V ha₀) x) ?_)
  · show (0 : chartRing V) =
      evalE V U ha₀ (faceMap N (face₁ A) hg₁ U _ (le_face₁ U V ha₀) 0 x.1) -
        evalE V U ha₀ (faceMap N (face₂ A) hg₂ U _ (le_face₂ U V ha₀) 0 x.1)
    rw [eq_comm, sub_eq_zero]
    exact appLE_divGen_eq N σe (face₁ A) σe (face₂ A) σe_face₁ hg₁ hg₂ hnorm _ _ _ V _ _ _ _ _

end Phi

end Stacks.Cube

end
