module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.LocalEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerTopBasis
public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison

/-!
# The wedge of the conormal classes of a family of equations

Let `i : Z ⟶ X` be a closed immersion with conormal sheaf `𝒞_{Z/X}`, `W ⊆ X` an open and
`f₁, …, f_c ∈ Γ(W, 𝒪_X)` sections vanishing on `Z`.  Their conormal classes `[fᵢ]` are sections
of `𝒞_{Z/X}` over `Z ∩ W`, and their wedge

`ω_f = [f₁] ∧ ⋯ ∧ [f_c] ∈ Γ(Z ∩ W, ⋀^c 𝒞_{Z/X})`

is the section of the determinant of the conormal sheaf through which Stacks 0G7T twists.  If
`g = a f` for a matrix `a` of functions, then `ω_g = det(a) ω_f`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Perfect.ConormalClass

/-! ### The determinant law for wedges in an exterior power of a module -/

/-- **A wedge of linear combinations is the determinant times the wedge.** -/
theorem ιMulti_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (a : Matrix (Fin n) (Fin n) R) (x : Fin n → M) :
    exteriorPower.ιMulti R n (fun j => ∑ i, a j i • x i) = a.det • exteriorPower.ιMulti R n x := by
  let b := Pi.basisFun R (Fin n)
  let φ : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R x
  let g : (Fin n → R) →ₗ[R] (Fin n → R) := Matrix.toLin' a.transpose
  have h2 := congrArg (exteriorPower.map n φ) (Stacks.ExteriorPower.map_ιMulti_eq_det_smul b b g)
  rw [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.map_apply_ιMulti, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin',
    Matrix.det_transpose] at h2
  have hx : (⇑φ ∘ ⇑b) = x := by
    funext i
    simp [φ, b, Fintype.linearCombination_apply, Pi.single_apply]
  have hy : (⇑φ ∘ ⇑g ∘ ⇑b) = fun j => ∑ i, a j i • x i := by
    funext j
    simp [φ, g, b, Fintype.linearCombination_apply, Matrix.toLin'_apply]
  rwa [hx, hy] at h2

/-- **The determinant law for ordered products of degree-one generators** in a graded algebra
whose degree-one generator squares to zero. -/
theorem homogeneousProd_sum_smul {C : Type*} [Category C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}
    {Pc : ℤ → PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)} (A : Stacks.GradedAlgebra Pc)
    {F : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)} (gen : F ⟶ Pc 1)
    (hs : A.GenSquareZero gen) (Y : Cᵒᵖ) (n : ℕ)
    (a : Matrix (Fin n) (Fin n) ((O ⋙ forget₂ _ RingCat).obj Y)) (x : Fin n → F.obj Y) :
    A.homogeneousProd Y n (fun j => gen.app Y (∑ i, a j i • x i)) =
      a.det • A.homogeneousProd Y n (fun j => gen.app Y (x j)) := by
  rw [← A.extCmpSections_ιMulti gen hs, ← A.extCmpSections_ιMulti gen hs, ιMulti_sum_smul,
    map_smul]

/-! ### Conormal classes -/

section Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The conormal sheaf `𝒞_{Z/X}` of the closed immersion `i`** (Stacks 01R2). -/
abbrev conormal : Z.Modules := Stacks.Conormal.conormalSheaf i

/-- The section of the ideal sheaf of `i` given by a function vanishing on `Z`. -/
def idealLift {A : X.Opens} (a : Γ(X, A)) (ha : (i.app A).hom a = 0) :
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op A) :=
  (Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer i A).symm ⟨a, ha⟩

/-- **The conormal class `[a] ∈ Γ(Z ∩ A, 𝒞_{Z/X})`** of a function `a` on `A` vanishing on `Z`. -/
def conormalClass {A : X.Opens} (a : Γ(X, A)) (ha : (i.app A).hom a = 0) :
    Γ(conormal i, i ⁻¹ᵁ A) :=
  (Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op A) (idealLift i a ha)

omit [IsClosedImmersion i] in
/-- The section `idealLift i a ha` of the ideal sheaf is `a` as a function on `A`. -/
theorem idealLift_coe {A : X.Opens} (a : Γ(X, A)) (ha : (i.app A).hom a = 0) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom))).val.app (op A) (idealLift i a ha) = a :=
  congrArg Subtype.val
    ((Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer i A).apply_symm_apply
      ⟨a, ha⟩)

/-- A section of the ideal sheaf whose image is `a` is the lift of `a`. -/
private theorem idealLift_eq_of_coe_eq {Z X : Scheme.{u}} (i : Z ⟶ X) {A : X.Opens}
    (a : Γ(X, A)) (ha : (i.app A).hom a = 0)
    (s : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op A))
    (hs : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom))).val.app (op A) s = a) : idealLift i a ha = s :=
  (Stacks.Conormal.AffineCotangent.Sections.idealSheafSectionsEquivKer i A).injective
    (Subtype.ext ((idealLift_coe i a ha).trans hs.symm))

omit [IsClosedImmersion i] in
/-- The lift of `a + a'` to the ideal sheaf is the sum of the lifts of `a` and `a'`. -/
theorem idealLift_add {A : X.Opens} (a a' : Γ(X, A)) (ha : (i.app A).hom a = 0)
    (ha' : (i.app A).hom a' = 0) (h : (i.app A).hom (a + a') = 0) :
    idealLift i (a + a') h = idealLift i a ha + idealLift i a' ha' :=
  idealLift_eq_of_coe_eq i _ h _ (by
    rw [map_add, idealLift_coe, idealLift_coe]
    rfl)

omit [IsClosedImmersion i] in
/-- The lift of `b * a` to the ideal sheaf is `b` times the lift of `a`. -/
theorem idealLift_mul {A : X.Opens} (b a : Γ(X, A)) (ha : (i.app A).hom a = 0)
    (h : (i.app A).hom (b * a) = 0) :
    idealLift i (b * a) h = b • idealLift i a ha :=
  idealLift_eq_of_coe_eq i _ h _ (by
    rw [map_smul, idealLift_coe]
    rfl)

omit [IsClosedImmersion i] in
/-- The lift to the ideal sheaf of the restriction of `a` to `A' ≤ A` is the restriction of the
lift of `a`. -/
theorem idealLift_restrict {A' A : X.Opens} (h : A' ≤ A) (a : Γ(X, A))
    (ha : (i.app A).hom a = 0) (ha' : (i.app A').hom (X.presheaf.map (homOfLE h).op a) = 0) :
    idealLift i (X.presheaf.map (homOfLE h).op a) ha' =
      (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.map (homOfLE h).op
        (idealLift i a ha) :=
  idealLift_eq_of_coe_eq i _ ha' _
    ((congrArg (fun q => q.hom (idealLift i a ha))
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))).val.naturality (homOfLE h).op)).trans
      (congrArg (X.presheaf.map (homOfLE h).op) (idealLift_coe i a ha)))

/-- The conormal class is additive: `[a + a'] = [a] + [a']`. -/
theorem conormalClass_add {A : X.Opens} (a a' : Γ(X, A)) (ha : (i.app A).hom a = 0)
    (ha' : (i.app A).hom a' = 0) (h : (i.app A).hom (a + a') = 0) :
    conormalClass i (a + a') h = conormalClass i a ha + conormalClass i a' ha' :=
  (congrArg ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op A)).hom
    (idealLift_add i a a' ha ha' h)).trans (map_add _ _ _)

/-- The conormal class of `b * a` is `i^♯ b` times the conormal class of `a`. -/
theorem conormalClass_mul {A : X.Opens} (b a : Γ(X, A)) (ha : (i.app A).hom a = 0)
    (h : (i.app A).hom (b * a) = 0) :
    conormalClass i (b * a) h = (i.app A).hom b • conormalClass i a ha :=
  (congrArg ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op A)).hom
    (idealLift_mul i b a ha h)).trans (map_smul _ _ _)

/-- The conormal class of the restriction of `a` to `A' ≤ A` is the restriction of the conormal
class of `a` to `Z ∩ A'`. -/
theorem conormalClass_restrict {A' A : X.Opens} (h : A' ≤ A) (a : Γ(X, A))
    (ha : (i.app A).hom a = 0) (ha' : (i.app A').hom (X.presheaf.map (homOfLE h).op a) = 0) :
    conormalClass i (X.presheaf.map (homOfLE h).op a) ha' =
      (conormal i).presheaf.map (homOfLE (i.preimage_mono h)).op (conormalClass i a ha) :=
  (congrArg ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op A')).hom
    (idealLift_restrict i h a ha ha')).trans
    (congrArg (fun q => q.hom (idealLift i a ha))
      ((Stacks.Immersion.canonicalConormalQuotientMap i).val.naturality (homOfLE h).op))

/-- The conormal class, as an additive map on the functions vanishing on `Z`. -/
def conormalClassHom (A : X.Opens) : RingHom.ker (i.app A).hom →+ Γ(conormal i, i ⁻¹ᵁ A) where
  toFun a := conormalClass i a.1 a.2
  map_zero' := by
    have h := conormalClass_add i (0 : Γ(X, A)) 0 (map_zero _) (map_zero _)
      (by rw [add_zero]; exact map_zero _)
    have h0 : conormalClass i ((0 : Γ(X, A)) + 0) (by rw [add_zero]; exact map_zero _) =
        conormalClass i 0 (map_zero _) := by congr 1; exact add_zero _
    rw [h0] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' a a' := conormalClass_add i a.1 a'.1 a.2 a'.2 (a + a').2

/-- The conormal class of `∑ₖ bₖ aₖ` is `∑ₖ i^♯ bₖ • [aₖ]`. -/
theorem conormalClass_sum {A : X.Opens} {n : ℕ} (b a : Fin n → Γ(X, A))
    (ha : ∀ k, (i.app A).hom (a k) = 0) (h : (i.app A).hom (∑ k, b k * a k) = 0) :
    conormalClass i (∑ k, b k * a k) h =
      ∑ k, (i.app A).hom (b k) • conormalClass i (a k) (ha k) := by
  have hk : ∀ k, (i.app A).hom (b k * a k) = 0 := fun k => by rw [map_mul, ha k, mul_zero]
  have e : (⟨∑ k, b k * a k, h⟩ : RingHom.ker (i.app A).hom) = ∑ k, ⟨b k * a k, hk k⟩ :=
    Subtype.ext (by rw [Submodule.coe_sum])
  have e2 := congrArg (conormalClassHom i A) e
  rw [map_sum] at e2
  exact e2.trans (Finset.sum_congr rfl fun k _ => conormalClass_mul i (b k) (a k) (ha k) (hk k))

end Conormal

/-! ### The wedge of the conormal classes -/

section Wedge

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The wedge `ω_f = [f₁] ∧ ⋯ ∧ [f_c]`** of the conormal classes of functions on `A` vanishing
on `Z`, a section of `⋀^c 𝒞_{Z/X}` over `Z ∩ A`. -/
def wedge {A : X.Opens} {c : ℕ} (f : Fin c → Γ(X, A)) (hf : ∀ j, (i.app A).hom (f j) = 0) :
    Γ(Scheme.Modules.exteriorPower (conormal i) c, i ⁻¹ᵁ A) :=
  (Scheme.Modules.exteriorAlgebra (conormal i)).toPresheafGradedAlgebra.homogeneousProd
    (op (i ⁻¹ᵁ A)) c fun j =>
      (Scheme.Modules.exteriorGenerator (conormal i)).val.app (op (i ⁻¹ᵁ A))
        (conormalClass i (f j) (hf j))

/-- The degree-one generator of the exterior algebra of `𝒞_{Z/X}` squares to zero. -/
theorem genSquareZero_conormal :
    Stacks.GradedAlgebra.GenSquareZero
      (Scheme.Modules.exteriorAlgebra (conormal i)).toPresheafGradedAlgebra
      (Scheme.Modules.exteriorGenerator (conormal i)).val :=
  fun Y x => (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (conormal i)).1 Y x

/-- **The determinant law**: if `g = a f`, then `ω_g = det(a) ω_f`. -/
theorem wedge_det {A : X.Opens} {c : ℕ} (f g : Fin c → Γ(X, A))
    (hf : ∀ j, (i.app A).hom (f j) = 0) (hg : ∀ j, (i.app A).hom (g j) = 0)
    (a : Matrix (Fin c) (Fin c) Γ(X, A)) (ha : ∀ j, g j = ∑ k, a j k * f k) :
    wedge i g hg = (i.app A).hom a.det • wedge i f hf := by
  have hcl : ∀ j, conormalClass i (g j) (hg j) =
      ∑ k, (i.app A).hom (a j k) • conormalClass i (f k) (hf k) := fun j =>
    (congrArg (fun x : {x : Γ(X, A) // (i.app A).hom x = 0} => conormalClass i x.1 x.2)
      (Subtype.ext (ha j) : (⟨g j, hg j⟩ : {x : Γ(X, A) // (i.app A).hom x = 0}) =
        ⟨∑ k, a j k * f k, (ha j) ▸ hg j⟩)).trans
      (conormalClass_sum i (a j) f hf _)
  refine (congrArg
      ((Scheme.Modules.exteriorAlgebra (conormal i)).toPresheafGradedAlgebra.homogeneousProd
        (op (i ⁻¹ᵁ A)) c)
      (funext fun j => congrArg
        ((Scheme.Modules.exteriorGenerator (conormal i)).val.app (op (i ⁻¹ᵁ A))).hom
        (hcl j))).trans ?_
  refine (homogeneousProd_sum_smul
    (Scheme.Modules.exteriorAlgebra (conormal i)).toPresheafGradedAlgebra
    (Scheme.Modules.exteriorGenerator (conormal i)).val (genSquareZero_conormal i)
    (op (i ⁻¹ᵁ A)) c (fun j k => (i.app A).hom (a j k))
    (fun k => conormalClass i (f k) (hf k))).trans ?_
  exact congrArg (fun r : Γ(Z, i ⁻¹ᵁ A) => r • wedge i f hf)
    (RingHom.map_det (i.app A).hom a).symm

/-- **The wedge commutes with restriction.** -/
theorem wedge_restrict {A' A : X.Opens} (h : A' ≤ A) {c : ℕ} (f : Fin c → Γ(X, A))
    (hf : ∀ j, (i.app A).hom (f j) = 0)
    (hf' : ∀ j, (i.app A').hom (X.presheaf.map (homOfLE h).op (f j)) = 0) :
    wedge i (fun j => X.presheaf.map (homOfLE h).op (f j)) hf' =
      (Scheme.Modules.exteriorPower (conormal i) c).presheaf.map (homOfLE (i.preimage_mono h)).op
        (wedge i f hf) := by
  have key := Stacks.GradedAlgebra.homogeneousProd_naturality
    (Scheme.Modules.exteriorAlgebra (conormal i)).toPresheafGradedAlgebra
    (homOfLE (i.preimage_mono h)).op c fun j =>
      (Scheme.Modules.exteriorGenerator (conormal i)).val.app (op (i ⁻¹ᵁ A))
        (conormalClass i (f j) (hf j))
  refine Eq.symm (key.trans ?_)
  refine congrArg _ (funext fun j => ?_)
  refine (congrArg (fun q => q.hom (conormalClass i (f j) (hf j)))
    ((Scheme.Modules.exteriorGenerator (conormal i)).val.naturality
      (homOfLE (i.preimage_mono h)).op)).symm.trans ?_
  exact congrArg ((Scheme.Modules.exteriorGenerator (conormal i)).val.app (op (i ⁻¹ᵁ A'))).hom
    (conormalClass_restrict i h (f j) (hf j) (hf' j)).symm

end Wedge

end Stacks.Perfect.ConormalClass
