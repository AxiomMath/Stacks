module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentityShiftDown
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeShiftSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftBy

/-!
# The connecting morphism of an admissible short exact sequence

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `0 → K → L → M → 0` be an admissible short exact sequence of right differential graded
`A`-modules, split after forgetting the differentials by a retraction `r` of `f : K ⟶ L` and a
section `s` of `g : L ⟶ M`. This file constructs

* the connecting morphism `δ : M ⟶ K[1]`, a morphism of right differential graded modules, which
  is `r ∘ d ∘ s` in every degree;
* the morphism `cone(δ) ⟶ L[1]`, which is an isomorphism, so that **the middle term is, up to a
  shift, the cone of a morphism from the third term to a shift of the first**;
* the admissible short exact sequence `0 → C(1_M) → C(g) → K[1] → 0`, so that **a shift of the
  first term is the cokernel of a morphism between cones built from the other two**.

These are the two descriptions through which Tag 0FSC is proved at the goodness of Tag 0FSA, in
`GoodDifferentialGradedAdmissibleTopos.lean`: a base change preserves cones, shifts and colimits.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.connecting`: the connecting morphism.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.coneConnectingIso`:
  `cone(δ) ≅ L[1]`.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.coneIdentityToCone` and
  `coneToShift`: the two maps `C(1_M) ⟶ C(g) ⟶ K[1]`, and `coneGradedSplitting` a graded
  splitting of them.

## Implementation notes

The connecting morphism is not written down degreewise: the commutator `d ∘ r + r ∘ d` of the
retraction with the differentials, read as a morphism `L ⟶ K[1]` by
`SheafOfModules.DifferentialGradedModule.deltaHom`, is a morphism of differential graded modules
automatically, it vanishes on `K` because `r` retracts `f`, and `δ` is its factorisation through
the cokernel `g` of `f`. So neither right `A`-linearity nor compatibility with the differentials
has to be checked by hand; the degreewise formula `δ = s ≫ d ≫ r` is then read off.

All three maps out of cones are `SheafOfModules.DifferentialGradedModule.ConePackage.desc` of a
morphism and a null-homotopy, so their right `A`-linearity is that of the null-homotopy; the
splitting identities are checked degreewise in the coordinates of the two cones.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 09KD](https://stacks.math.columbia.edu/tag/09KD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}
  {K L M : DifferentialGradedModule.{t, a, m} A} {f : K ⟶ L} {g : L ⟶ M}

/-! ### Transports and components -/

/-- The degree-`n` component of a graded homomorphism between the graded modules underlying two
differential graded modules, with its source and target spelled as the terms of the complexes. -/
def gradedApp {P Q : DifferentialGradedModule.{t, a, m} A}
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded Q) (n : ℤ) :
    P.complex.X n ⟶ Q.complex.X n :=
  Φ.app n

/-- Components of a composite. -/
theorem gradedApp_comp {P Q Q' : DifferentialGradedModule.{t, a, m} A}
    (Φ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded Q)
    (Ψ : GradedModule.ofDifferentialGraded Q ⟶ GradedModule.ofDifferentialGraded Q') (n : ℤ) :
    gradedApp (Φ ≫ Ψ) n = gradedApp Φ n ≫ gradedApp Ψ n := rfl

/-- Components of the identity. -/
theorem gradedApp_id (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    gradedApp (𝟙 (GradedModule.ofDifferentialGraded P)) n = 𝟙 _ := rfl

/-- Components of a sum. -/
theorem gradedApp_add {P Q : DifferentialGradedModule.{t, a, m} A}
    (Φ Ψ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded Q) (n : ℤ) :
    gradedApp (Φ + Ψ) n = gradedApp Φ n + gradedApp Ψ n := rfl

/-- Components of the graded homomorphism underlying a morphism. -/
theorem gradedApp_ofDifferentialGradedMap {P Q : DifferentialGradedModule.{t, a, m} A}
    (φ : P ⟶ Q) (n : ℤ) :
    gradedApp (GradedModule.ofDifferentialGradedMap φ) n = φ.toHomologicalComplex.f n := rfl

/-- Two graded homomorphisms with the same components are equal. -/
theorem gradedApp_ext {P Q : DifferentialGradedModule.{t, a, m} A}
    {Φ Ψ : GradedModule.ofDifferentialGraded P ⟶ GradedModule.ofDifferentialGraded Q}
    (h : ∀ n, gradedApp Φ n = gradedApp Ψ n) : Φ = Ψ :=
  GradedModule.Hom.ext h

/-! ### Coordinates of a cone -/

namespace ConePackage

variable {P P' : DifferentialGradedModule.{t, a, m} A} {φ : P ⟶ P'} (Pk : ConePackage φ)

/-- The inclusion of the first summand `P^{n+1}` of the degree-`n` piece of the cone. -/
noncomputable def ι₁ (n : ℤ) : P.complex.X (n + 1) ⟶ Pk.cone.complex.X n :=
  biprod.inl ≫ (Pk.componentIso n).inv

/-- The inclusion of the second summand `P'^n` of the degree-`n` piece of the cone. -/
noncomputable def ι₂ (n : ℤ) : P'.complex.X n ⟶ Pk.cone.complex.X n :=
  biprod.inr ≫ (Pk.componentIso n).inv

/-- The projection of the degree-`n` piece of the cone onto its first summand `P^{n+1}`. -/
noncomputable def π₁ (n : ℤ) : Pk.cone.complex.X n ⟶ P.complex.X (n + 1) :=
  (Pk.componentIso n).hom ≫ biprod.fst

/-- The projection of the degree-`n` piece of the cone onto its second summand `P'^n`. -/
noncomputable def π₂ (n : ℤ) : Pk.cone.complex.X n ⟶ P'.complex.X n :=
  (Pk.componentIso n).hom ≫ biprod.snd

@[reassoc (attr := simp)]
theorem ι₁_π₁ (n : ℤ) : Pk.ι₁ n ≫ Pk.π₁ n = 𝟙 _ := by simp [ι₁, π₁]

@[reassoc (attr := simp)]
theorem ι₁_π₂ (n : ℤ) : Pk.ι₁ n ≫ Pk.π₂ n = 0 := by simp [ι₁, π₂]

@[reassoc (attr := simp)]
theorem ι₂_π₁ (n : ℤ) : Pk.ι₂ n ≫ Pk.π₁ n = 0 := by simp [ι₂, π₁]

@[reassoc (attr := simp)]
theorem ι₂_π₂ (n : ℤ) : Pk.ι₂ n ≫ Pk.π₂ n = 𝟙 _ := by simp [ι₂, π₂]

/-- The two coordinates decompose the identity of the degree-`n` piece of the cone. -/
theorem π₁_ι₁_add_π₂_ι₂ (n : ℤ) : Pk.π₁ n ≫ Pk.ι₁ n + Pk.π₂ n ≫ Pk.ι₂ n = 𝟙 _ := by
  simp only [ι₁, ι₂, π₁, π₂, Category.assoc, ← Preadditive.comp_add]
  rw [← Category.assoc biprod.fst, ← Category.assoc biprod.snd, ← Preadditive.add_comp,
    biprod.total, Category.id_comp, Iso.hom_inv_id]

/-- The inclusion of the target of a cone is the inclusion of the second summand. -/
theorem inclusion_f_eq_ι₂ (n : ℤ) : Pk.inclusion.toHomologicalComplex.f n = Pk.ι₂ n :=
  Pk.inclusion_f n

/-- **A morphism out of a cone, in coordinates.** -/
theorem desc_f_eq {N : DifferentialGradedModule.{t, a, m} A} (β : P' ⟶ N)
    (α : ∀ n : ℤ, P.complex.X (n + 1) ⟶ N.complex.X n) (hα) (hδ) (n : ℤ) :
    (Pk.desc β α hα hδ).toHomologicalComplex.f n =
      Pk.π₁ n ≫ α n + Pk.π₂ n ≫ β.toHomologicalComplex.f n := by
  rw [desc_f, biprod.desc_eq, Preadditive.comp_add, π₁, π₂, Category.assoc, Category.assoc]

/-- Two morphisms out of a degree-`n` piece of a cone agreeing on both summands agree. -/
theorem hom_ext' {n : ℤ} {Z : SheafOfModules.{m} R} {u v : Pk.cone.complex.X n ⟶ Z}
    (h₁ : Pk.ι₁ n ≫ u = Pk.ι₁ n ≫ v) (h₂ : Pk.ι₂ n ≫ u = Pk.ι₂ n ≫ v) : u = v := by
  rw [← Category.id_comp u, ← Category.id_comp v, ← π₁_ι₁_add_π₂_ι₂, Preadditive.add_comp,
    Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, h₁, h₂]

/-- A transport of degrees, the inclusion of the first summand, and a transport back. -/
theorem degCastHom_inl_inv_eqToHom (n p : ℤ) (hp : p = n) (h : n + 1 = p + 1) :
    degCastHom P.complex.X h ≫ biprod.inl ≫ (Pk.componentIso p).inv ≫
      eqToHom (congrArg Pk.cone.complex.X hp) = Pk.ι₁ n := by
  subst hp
  rw [degCastHom_eq_id, eqToHom_refl, Category.comp_id, Category.id_comp, ι₁]

/-- **The family of degree minus one of a cone, in degree `n + 1` and transported back to degree
`n`, is the inclusion of the first summand.** -/
theorem sectionX_comp_eqToHom (n : ℤ) :
    Pk.sectionX (n + 1) ≫ eqToHom (congrArg Pk.cone.complex.X (degSuccSubOne n)) = Pk.ι₁ n := by
  rw [sectionX, Category.assoc, Category.assoc]
  exact Pk.degCastHom_inl_inv_eqToHom n (n + 1 + -1) (degSuccSubOne n) _

/-- The same, with the transport written as a `degCastHom`. -/
theorem sectionX_comp_degCastHom (n : ℤ) (h : n + 1 + -1 = n) :
    Pk.sectionX (n + 1) ≫ degCastHom Pk.cone.complex.X h = Pk.ι₁ n := by
  have key : ∀ {i j : ℤ} (h : i = j),
      degCastHom Pk.cone.complex.X h = eqToHom (congrArg Pk.cone.complex.X h) := by
    intro i j h
    subst h
    rfl
  rw [key]
  exact Pk.sectionX_comp_eqToHom n

end ConePackage

/-! ### A graded homomorphism into the first summand of a cone -/

section ToShiftDownCone

variable {P P' Q : DifferentialGradedModule.{t, a, m} A} {φ : P ⟶ P'} (Pk : ConePackage φ)

/-- **A graded homomorphism into `P`, followed by the inclusion of `P` as the first summand of
the cone of `φ : P ⟶ P'`**, read as a graded homomorphism into the shift down by one of the cone:
in degree `n` it sends `Q^n` to the first summand `P^n` of `C(φ)^{n-1}`. -/
noncomputable def toShiftDownCone
    (θ : GradedModule.ofDifferentialGraded Q ⟶ GradedModule.ofDifferentialGraded P) :
    GradedModule.ofDifferentialGraded Q ⟶ gradedShiftDown Pk.cone where
  app n := θ.app n ≫ Pk.sectionX n
  map_smul n i U x y := by
    refine eq_of_heq ?_
    have e1 := θ.map_smul n i U x y
    have e2 := Pk.sectionX_map_smul n i U ((θ.app n).val.app U x) y
    exact (heq_of_eq ((congrArg (fun z => (Pk.sectionX (n + i)).val.app U z) e1).trans e2)).trans
      ((heq_castHom _ _ U _).trans (gradedShiftDown_smul_eval_heq Pk.cone n i U _ y).symm)

/-- Its transport back to degree `n` is the inclusion of the first summand. -/
theorem ofShiftDownHom_toShiftDownCone
    (θ : GradedModule.ofDifferentialGraded Q ⟶ GradedModule.ofDifferentialGraded P) (n : ℤ) :
    ofShiftDownHom (toShiftDownCone Pk θ) n = gradedApp θ (n + 1) ≫ Pk.ι₁ n := by
  rw [ofShiftDownHom_eq]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun u => gradedApp θ (n + 1) ≫ u) (Pk.sectionX_comp_eqToHom n))

/-- **The commutator of `toShiftDownCone θ` with the differentials, in coordinates**: it is
`θ ≫ φ` into the second summand, plus the commutator `d ∘ θ - θ ∘ d` into the first. -/
theorem deltaHom_toShiftDownCone_f
    (θ : GradedModule.ofDifferentialGraded Q ⟶ GradedModule.ofDifferentialGraded P) (n : ℤ) :
    (deltaHom (toShiftDownCone Pk θ)).toHomologicalComplex.f n =
      gradedApp θ n ≫ φ.toHomologicalComplex.f n ≫ Pk.ι₂ n +
        (Q.complex.d n (n + 1) ≫ gradedApp θ (n + 1) - gradedApp θ n ≫ P.complex.d n (n + 1)) ≫
          Pk.ι₁ n := by
  have hd : (Pk.sectionX n ≫ Pk.cone.complex.d (n - 1) (n - 1 + 1) ≫
        degCastHom Pk.cone.complex.X (show n - 1 + 1 = n by omega) :
          P.complex.X n ⟶ Pk.cone.complex.X n) +
      P.complex.d n (n + 1) ≫ Pk.ι₁ n = φ.toHomologicalComplex.f n ≫ Pk.ι₂ n := by
    rw [← Pk.sectionX_comp_degCastHom n (show n + 1 + -1 = n by omega), ← Pk.inclusion_f_eq_ι₂]
    exact Pk.sectionFamily_d n
  have h1 : (deltaHom (toShiftDownCone Pk θ)).toHomologicalComplex.f n =
      gradedApp θ n ≫ (Pk.sectionX n ≫ Pk.cone.complex.d (n - 1) (n - 1 + 1) ≫
        degCastHom Pk.cone.complex.X (show n - 1 + 1 = n by omega) :
          P.complex.X n ⟶ Pk.cone.complex.X n) +
        Q.complex.d n (n + 1) ≫ gradedApp θ (n + 1) ≫ Pk.ι₁ n := by
    rw [deltaHom_f, deltaFamily, ofShiftDownHom_toShiftDownCone,
      d_comp_degCastHom Pk.cone.complex (n - 1) (show n - 1 + 1 = n by omega)]
    exact congrArg (· + Q.complex.d n (n + 1) ≫ gradedApp θ (n + 1) ≫ Pk.ι₁ n)
      (Category.assoc _ _ _)
  rw [h1, eq_sub_of_add_eq hd, Preadditive.comp_sub, Preadditive.sub_comp]
  simp only [Category.assoc]
  abel

end ToShiftDownCone

/-! ### The identification of `P[1]^n` with `P^{n+1}` -/

/-- The degree-`n` term of `P[1]` is `P^{n+1}`, as a morphism. -/
noncomputable def toShiftByOne (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    P.complex.X (n + 1) ⟶ (shiftBy P 1).complex.X n :=
  eqToHom (shiftBy_one_X P n)

/-- The degree-`n` term of `P[1]` is `P^{n+1}`, as a morphism in the other direction. -/
noncomputable def ofShiftByOne (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (shiftBy P 1).complex.X n ⟶ P.complex.X (n + 1) :=
  eqToHom (shiftBy_one_X P n).symm

@[reassoc (attr := simp)]
theorem toShiftByOne_ofShiftByOne (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    toShiftByOne P n ≫ ofShiftByOne P n = 𝟙 _ := by
  rw [toShiftByOne, ofShiftByOne, eqToHom_trans, eqToHom_refl]

@[reassoc (attr := simp)]
theorem ofShiftByOne_toShiftByOne (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    ofShiftByOne P n ≫ toShiftByOne P n = 𝟙 _ := by
  rw [toShiftByOne, ofShiftByOne, eqToHom_trans, eqToHom_refl]

/-- A morphism followed by a transport of its target is a transport of its source followed by a
heterogeneously equal morphism. -/
theorem comp_eqToHom_eq_eqToHom_comp {X X' Y Y' : SheafOfModules.{m} R} (φ : X ⟶ Y)
    (φ' : X' ⟶ Y') (hX : X = X') (hY : Y = Y') (h : HEq φ φ') :
    φ ≫ eqToHom hY = eqToHom hX ≫ φ' := by
  subst hX hY
  obtain rfl := eq_of_heq h
  simp

/-- A transport, on local sections, is the identity up to `HEq`. -/
theorem eqToHom_app_heq {X Y : SheafOfModules.{m} R} (h : X = Y) (U : Cᵒᵖ) (x : X.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- A morphism followed by `toShiftByOne`, on local sections, is the morphism, up to `HEq`. -/
theorem comp_toShiftByOne_app_heq (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ)
    {X : SheafOfModules.{m} R} (φ : X ⟶ P.complex.X (n + 1)) (U : Cᵒᵖ) (z : X.val.obj U) :
    HEq ((φ ≫ toShiftByOne P n).val.app U z) (φ.val.app U z) := by
  have key : ∀ {Y Z : SheafOfModules.{m} R} (ψ : X ⟶ Y) (h : Y = Z),
      HEq ((ψ ≫ eqToHom h).val.app U z) (ψ.val.app U z) := by
    intro Y Z ψ h
    subst h
    simp
  exact key φ (shiftBy_one_X P n)

/-- `toShiftByOne` commutes with the differentials up to the sign of the differential of the
shift. -/
@[reassoc]
theorem toShiftByOne_d (P : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    toShiftByOne P n ≫ (shiftBy P 1).complex.d n (n + 1) =
      -(P.complex.d (n + 1) (n + 1 + 1) ≫ toShiftByOne P (n + 1)) := by
  have e : (-P.complex.d (n + 1) (n + 1 + 1) : P.complex.X (n + 1) ⟶ P.complex.X (n + 1 + 1)) =
      (shiftBy P 1).complex.d n (n + 1) := by
    rw [shiftBy_d, Int.negOnePow_one, Units.neg_smul, one_smul]
  rw [← Preadditive.neg_comp]
  exact (comp_eqToHom_eq_eqToHom_comp _ _ (shiftBy_one_X P n) (shiftBy_one_X P (n + 1))
    (heq_of_eq e)).symm

/-- The shift by one of a morphism, through `toShiftByOne` and `ofShiftByOne`. -/
theorem shiftByMap_one_f {P Q : DifferentialGradedModule.{t, a, m} A} (φ : P ⟶ Q) (n : ℤ) :
    (shiftByMap 1 φ).toHomologicalComplex.f n =
      ofShiftByOne P n ≫ φ.toHomologicalComplex.f (n + 1) ≫ toShiftByOne Q n := by
  have h := comp_eqToHom_eq_eqToHom_comp ((shiftByMap 1 φ).toHomologicalComplex.f n)
    (φ.toHomologicalComplex.f (n + 1)) (shiftBy_one_X P n).symm (shiftBy_one_X Q n).symm HEq.rfl
  rw [ofShiftByOne, toShiftByOne, ← reassoc_of% h, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Two morphisms into a degree-`n` piece of a cone agreeing on both coordinates agree. -/
theorem ConePackage.hom_ext_to {P P' : DifferentialGradedModule.{t, a, m} A} {φ : P ⟶ P'}
    (Pk : ConePackage φ) {n : ℤ} {Z : SheafOfModules.{m} R} {u v : Z ⟶ Pk.cone.complex.X n}
    (h₁ : u ≫ Pk.π₁ n = v ≫ Pk.π₁ n) (h₂ : u ≫ Pk.π₂ n = v ≫ Pk.π₂ n) : u = v := by
  rw [← Category.comp_id u, ← Category.comp_id v, ← Pk.π₁_ι₁_add_π₂_ι₂, Preadditive.comp_add,
    Preadditive.comp_add, ← Category.assoc u, ← Category.assoc u, ← Category.assoc v,
    ← Category.assoc v, h₁, h₂]

namespace GradedSplitting

variable (S : GradedSplitting f g)

/-! ### The splitting, degreewise -/

/-- The retraction retracts `f`, degreewise. -/
@[reassoc]
theorem f_rX (n : ℤ) : f.toHomologicalComplex.f n ≫ gradedApp S.r n = 𝟙 _ :=
  congrArg (fun φ : GradedModule.ofDifferentialGraded K ⟶ GradedModule.ofDifferentialGraded K =>
    φ.app n) S.f_r

/-- The section is a section of `g`, degreewise. -/
@[reassoc]
theorem sX_g (n : ℤ) : gradedApp S.s n ≫ g.toHomologicalComplex.f n = 𝟙 _ :=
  congrArg (fun φ : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded M =>
    φ.app n) S.s_g

/-- The retraction and the section decompose the identity, degreewise. -/
theorem rX_f_add_g_sX (n : ℤ) :
    gradedApp S.r n ≫ f.toHomologicalComplex.f n + g.toHomologicalComplex.f n ≫ gradedApp S.s n =
      𝟙 _ :=
  congrArg (fun φ : GradedModule.ofDifferentialGraded L ⟶ GradedModule.ofDifferentialGraded L =>
    φ.app n) S.id

include S in
/-- `f ≫ g = 0`, degreewise. -/
@[reassoc]
theorem f_g (n : ℤ) : f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n = 0 := by
  rw [← comp_f, S.comp_eq_zero]
  rfl

/-- The section followed by the retraction vanishes, degreewise. -/
@[reassoc]
theorem sX_rX (n : ℤ) : gradedApp S.s n ≫ gradedApp S.r n = 0 := by
  have h := congrArg (fun φ => gradedApp S.s n ≫ φ ≫ gradedApp S.r n) (S.rX_f_add_g_sX n)
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, S.f_rX,
    Category.comp_id, Category.id_comp, S.sX_g_assoc] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- Transport along an equality of degrees acts on local sections as the identity, up to
`HEq`. -/
theorem heq_eqToHom_app (Y : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (y : (Y i).val.obj U) : HEq ((eqToHom (congrArg Y h)).val.app U y) y := by
  subst h
  rfl

/-- Two transports which compose to an endomorphism compose to the identity. -/
theorem eqToHom_comp_eqToHom_eq_id {X Y : SheafOfModules.{m} R} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ eqToHom q = 𝟙 X := by
  subst p
  simp

/-- The retraction, read as a homomorphism of graded modules into the shift down by one of
`K[1]`. -/
noncomputable def rShift :
    GradedModule.ofDifferentialGraded L ⟶ gradedShiftDown (shiftBy K 1) where
  app n := gradedApp S.r n ≫ eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega))
  map_smul n i U x y := by
    refine eq_of_heq ?_
    have hx : HEq ((eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega))).val.app U
        ((gradedApp S.r n).val.app U x)) ((gradedApp S.r n).val.app U x) :=
      heq_eqToHom_app K.complex.X (show n = n - 1 + 1 by omega) U _
    have h1 : HEq ((eqToHom (congrArg K.complex.X (show n + i = n + i - 1 + 1 by omega))).val.app U
        ((gradedApp S.r (n + i)).val.app U ((L.mul n i).app U x y)))
        ((K.mul n i).app U ((gradedApp S.r n).val.app U x) y) :=
      (heq_eqToHom_app K.complex.X (show n + i = n + i - 1 + 1 by omega) U _).trans
        (heq_of_eq (S.r.map_smul n i U x y))
    have h2 := gradedShiftDown_smul_eval_heq (shiftBy K 1) n i U
      ((eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega))).val.app U
        ((gradedApp S.r n).val.app U x)) y
    have h3 := shiftBy_mul_app_heq K 1 (n - 1) i U
      ((eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega))).val.app U
        ((gradedApp S.r n).val.app U x)) y
    have h4 := heq_dependent_apply (fun d (z : (K.complex.X d).val.obj U) => (K.mul d i).app U z y)
      (show n - 1 + 1 = n by omega) hx
    exact h1.trans (h4.symm.trans (h3.symm.trans h2.symm))

/-- **The commutator of the retraction with the differentials, degreewise**: in degree `n` it is
`-(r ≫ d) + d ≫ r`, the sign being that of the differential of `K[1]`. -/
theorem deltaHom_rShift_f (n : ℤ) :
    (deltaHom S.rShift).toHomologicalComplex.f n =
      (-(gradedApp S.r n ≫ K.complex.d n (n + 1)) + L.complex.d n (n + 1) ≫ gradedApp S.r (n + 1) :
        L.complex.X n ⟶ K.complex.X (n + 1)) := by
  rw [deltaHom_f, deltaFamily, ofShiftDownHom_eq, shiftBy_d]
  have h1 : shiftDownApp S.rShift n =
      gradedApp S.r n ≫ eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega)) := rfl
  have h2 : shiftDownApp S.rShift (n + 1) ≫
      eqToHom (congrArg (shiftBy K 1).complex.X (degSuccSubOne n)) = gradedApp S.r (n + 1) := by
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.comp_id _)
    exact congrArg (fun φ => gradedApp S.r (n + 1) ≫ φ) (eqToHom_comp_eqToHom_eq_id _ _)
  have h3 : (gradedApp S.r n ≫ eqToHom (congrArg K.complex.X (show n = n - 1 + 1 by omega))) ≫
      (-K.complex.d (n - 1 + 1) (n + 1)) = -(gradedApp S.r n ≫ K.complex.d n (n + 1)) := by
    rw [Preadditive.comp_neg, Category.assoc,
      eqToHom_comp_d K.complex (show n = n - 1 + 1 by omega)]
  rw [h1, h2, Int.negOnePow_one, Units.neg_smul, one_smul]
  exact congrArg (· + L.complex.d n (n + 1) ≫ gradedApp S.r (n + 1)) h3

/-- The commutator of the retraction with the differentials vanishes on `K`. -/
theorem f_deltaHom_rShift : f ≫ deltaHom S.rShift = 0 := by
  refine Hom.ext fun n => ?_
  have h : f.toHomologicalComplex.f n ≫ (-(gradedApp S.r n ≫ K.complex.d n (n + 1)) +
      L.complex.d n (n + 1) ≫ gradedApp S.r (n + 1)) = 0 := by
    rw [Preadditive.comp_add, Preadditive.comp_neg,
      ← Category.assoc (f.toHomologicalComplex.f n) (L.complex.d _ _),
      f.toHomologicalComplex.comm, Category.assoc, S.f_rX_assoc, S.f_rX,
      Category.comp_id, neg_add_cancel]
  rw [comp_f, deltaHom_rShift_f]
  exact h

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The connecting morphism `δ : M ⟶ K[1]` of an admissible short exact sequence**: the
factorisation through the cokernel `g` of `f` of the commutator `d ∘ r + r ∘ d` of the
retraction with the differentials. -/
noncomputable def connecting : M ⟶ shiftBy K 1 :=
  S.shortExact.gIsCokernel.desc (CokernelCofork.ofπ (deltaHom S.rShift) S.f_deltaHom_rShift)

/-- **The defining property of the connecting morphism**: `g ≫ δ` is the commutator of the
retraction with the differentials. -/
theorem g_connecting : g ≫ S.connecting = deltaHom S.rShift :=
  S.shortExact.gIsCokernel.fac
    (CokernelCofork.ofπ (deltaHom S.rShift) S.f_deltaHom_rShift) WalkingParallelPair.one

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The retraction, read into the shift down by one, transported back: it is the retraction. -/
theorem ofShiftDownHom_rShift (n : ℤ) :
    ofShiftDownHom S.rShift n = gradedApp S.r (n + 1) ≫ toShiftByOne K n := by
  rw [ofShiftDownHom_eq]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun u => gradedApp S.r (n + 1) ≫ u) (eqToHom_trans _ _))

/-- The degree-`n` component of the connecting morphism, `s ≫ d ≫ r`, with target `K^{n+1}`. -/
noncomputable def connectingX (n : ℤ) : M.complex.X n ⟶ K.complex.X (n + 1) :=
  gradedApp S.s n ≫ L.complex.d n (n + 1) ≫ gradedApp S.r (n + 1)

/-- **The connecting morphism in degree `n` is `s ≫ d ≫ r`.** -/
theorem connecting_f (n : ℤ) :
    S.connecting.toHomologicalComplex.f n = S.connectingX n ≫ toShiftByOne K n := by
  have h1 : S.connecting.toHomologicalComplex.f n =
      gradedApp S.s n ≫ (deltaHom S.rShift).toHomologicalComplex.f n := by
    rw [← S.g_connecting, comp_f, S.sX_g_assoc]
  have h2 : gradedApp S.s n ≫ (-(gradedApp S.r n ≫ K.complex.d n (n + 1)) +
      L.complex.d n (n + 1) ≫ gradedApp S.r (n + 1)) = S.connectingX n := by
    rw [Preadditive.comp_add, Preadditive.comp_neg, S.sX_rX_assoc, zero_comp, neg_zero,
      zero_add]
    rfl
  rw [h1, deltaHom_rShift_f]
  exact h2.trans ((Category.comp_id _).symm.trans
    (congrArg (fun u => S.connectingX n ≫ u) (eqToHom_refl _ _).symm))

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **The commutator of the section with the differentials, followed by `f`, cancels the
connecting morphism followed by `f`.** In degree `n`:
`(d ∘ s - s ∘ d) + δ ∘ f = 0`. -/
theorem commutator_add_connectingX_f (n : ℤ) :
    (M.complex.d n (n + 1) ≫ gradedApp S.s (n + 1) - gradedApp S.s n ≫ L.complex.d n (n + 1)) +
      S.connectingX n ≫ f.toHomologicalComplex.f (n + 1) = 0 := by
  have h : gradedApp S.r (n + 1) ≫ f.toHomologicalComplex.f (n + 1) =
      𝟙 _ - g.toHomologicalComplex.f (n + 1) ≫ gradedApp S.s (n + 1) :=
    eq_sub_of_add_eq (S.rX_f_add_g_sX (n + 1))
  rw [connectingX, Category.assoc, Category.assoc, h, Preadditive.comp_sub, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc (L.complex.d n (n + 1)), ← g.toHomologicalComplex.comm,
    Category.assoc, S.sX_g_assoc]
  abel

/-! ### The cone of `g` maps onto `K[1]` -/

/-- **The morphism `C(g) ⟶ K[1]`**: the retraction on the first summand and the connecting
morphism on the second. -/
noncomputable def coneToShift : cone g ⟶ shiftBy K 1 :=
  coneDescOf S.connecting S.rShift S.g_connecting.symm

/-- `C(g) ⟶ K[1]` in coordinates. -/
theorem coneToShift_f (n : ℤ) :
    (S.coneToShift).toHomologicalComplex.f n =
      (conePackage g).π₁ n ≫ gradedApp S.r (n + 1) ≫ toShiftByOne K n +
        (conePackage g).π₂ n ≫ S.connectingX n ≫ toShiftByOne K n := by
  rw [coneToShift, coneDescOf, ConePackage.desc_f_eq, ofShiftDownHom_rShift, connecting_f]

/-! ### The cone of the identity of `M` maps into the cone of `g` -/

/-- **The morphism `C(1_M) ⟶ C(g)`** attached to the section: on the first summand it is the
section into the first summand. -/
noncomputable def coneIdentityToCone : cone (𝟙 M) ⟶ cone g :=
  (coneIdentityShiftDownEquiv M (cone g)).symm (toShiftDownCone (conePackage g) S.s)

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- `C(1_M) ⟶ C(g)` in coordinates. -/
theorem coneIdentityToCone_f (n : ℤ) :
    (S.coneIdentityToCone).toHomologicalComplex.f n =
      (conePackage (𝟙 M)).π₁ n ≫ gradedApp S.s (n + 1) ≫ (conePackage g).ι₁ n +
        (conePackage (𝟙 M)).π₂ n ≫ ((conePackage g).ι₂ n +
          (M.complex.d n (n + 1) ≫ gradedApp S.s (n + 1) -
            gradedApp S.s n ≫ L.complex.d n (n + 1)) ≫ (conePackage g).ι₁ n) := by
  change ((conePackage (𝟙 M)).desc (deltaHom (toShiftDownCone (conePackage g) S.s))
    (ofShiftDownHom (toShiftDownCone (conePackage g) S.s))
    (ofShiftDownHom_mul (toShiftDownCone (conePackage g) S.s))
    (deltaHom_delta (toShiftDownCone (conePackage g) S.s))).toHomologicalComplex.f n = _
  rw [ConePackage.desc_f_eq, ofShiftDownHom_toShiftDownCone, deltaHom_toShiftDownCone_f,
    S.sX_g_assoc]

/-! ### The cone of `g` maps onto the cone of the identity of `M` -/

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The commutator condition for `C(g) ⟶ C(1_M)`. -/
theorem deltaHom_toShiftDownCone_g :
    deltaHom (toShiftDownCone (conePackage (𝟙 M)) (GradedModule.ofDifferentialGradedMap g)) =
      g ≫ (conePackage (𝟙 M)).inclusion := by
  refine Hom.ext fun n => ?_
  rw [deltaHom_toShiftDownCone_f, comp_f, (conePackage (𝟙 M)).inclusion_f_eq_ι₂,
    gradedApp_ofDifferentialGradedMap, gradedApp_ofDifferentialGradedMap, id_f,
    g.toHomologicalComplex.comm, sub_self, zero_comp, add_zero, Category.id_comp]

/-- **The morphism `C(g) ⟶ C(1_M)`** induced by `g` on the first summand and the identity on the
second; a retraction of `C(1_M) ⟶ C(g)` at the graded level. -/
noncomputable def coneToConeIdentity : cone g ⟶ cone (𝟙 M) :=
  coneDescOf (conePackage (𝟙 M)).inclusion
    (toShiftDownCone (conePackage (𝟙 M)) (GradedModule.ofDifferentialGradedMap g))
    (deltaHom_toShiftDownCone_g (g := g))

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- `C(g) ⟶ C(1_M)` in coordinates. -/
theorem coneToConeIdentity_f (n : ℤ) :
    (coneToConeIdentity (g := g)).toHomologicalComplex.f n =
      (conePackage g).π₁ n ≫ g.toHomologicalComplex.f (n + 1) ≫ (conePackage (𝟙 M)).ι₁ n +
        (conePackage g).π₂ n ≫ (conePackage (𝟙 M)).ι₂ n := by
  rw [coneToConeIdentity, coneDescOf, ConePackage.desc_f_eq, ofShiftDownHom_toShiftDownCone,
    (conePackage (𝟙 M)).inclusion_f_eq_ι₂, gradedApp_ofDifferentialGradedMap]

/-! ### `K[1]` maps into the cone of `g`, at the graded level -/

/-- **The graded homomorphism `K[1] ⟶ C(g)`**: `f` into the first summand. -/
noncomputable def shiftToCone :
    GradedModule.ofDifferentialGraded (shiftBy K 1) ⟶ GradedModule.ofDifferentialGraded (cone g) :=
  GradedModule.ofDifferentialGradedMap (shiftByMap 1 f) ≫
    GradedModule.ofDifferentialGradedMap (eqToHom (shiftBy_one L)) ≫
      (conePackage g).gradedSplitting.s

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- `K[1] ⟶ C(g)` in coordinates. -/
theorem gradedApp_shiftToCone (n : ℤ) :
    gradedApp (shiftToCone (f := f) (g := g)) n =
      ofShiftByOne K n ≫ f.toHomologicalComplex.f (n + 1) ≫ (conePackage g).ι₁ n := by
  refine (conePackage g).hom_ext_to ?_ ?_
  · rw [Category.assoc, Category.assoc, ConePackage.ι₁_π₁, Category.comp_id]
    change (shiftByMap 1 f).toHomologicalComplex.f n ≫
        (eqToHom (shiftBy_one L)).toHomologicalComplex.f n ≫
          (conePackage g).coneSectionX n ≫ (conePackage g).π₁ n = _
    have hx : ((shiftPackage L).xIso n).hom =
        (eqToHom (shiftPackage L).shifted_complex).f n := rfl
    have key : ∀ {P Q : DifferentialGradedModule.{t, a, m} A} (h : P = Q) (k : ℤ),
        (eqToHom h).toHomologicalComplex.f k =
          eqToHom (congrArg (fun T : DifferentialGradedModule.{t, a, m} A => T.complex.X k) h) := by
      intro P Q h k
      subst h
      rfl
    rw [ConePackage.π₁, ConePackage.coneSectionX_fst, key, hx,
      HomologicalComplex.eqToHom_f, eqToHom_trans]
    exact comp_eqToHom_eq_eqToHom_comp _ _ (shiftBy_one_X K n).symm _ HEq.rfl
  · rw [Category.assoc, Category.assoc, ConePackage.ι₁_π₂, comp_zero, comp_zero]
    change (shiftByMap 1 f).toHomologicalComplex.f n ≫
        (eqToHom (shiftBy_one L)).toHomologicalComplex.f n ≫
          (conePackage g).coneSectionX n ≫ (conePackage g).π₂ n = _
    rw [ConePackage.π₂, ConePackage.coneSectionX_snd, comp_zero, comp_zero]

/-! ### The admissible short exact sequence `0 → C(1_M) → C(g) → K[1] → 0` -/

/-- **A graded splitting of `C(1_M) ⟶ C(g) ⟶ K[1]`.** -/
noncomputable def coneGradedSplitting :
    GradedSplitting S.coneIdentityToCone S.coneToShift where
  r := GradedModule.ofDifferentialGradedMap (coneToConeIdentity (g := g))
  s := shiftToCone (f := f) (g := g)
  f_r := gradedApp_ext fun n => by
    rw [gradedApp_comp, gradedApp_ofDifferentialGradedMap, gradedApp_ofDifferentialGradedMap,
      coneIdentityToCone_f, coneToConeIdentity_f (g := g), gradedApp_id]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      ConePackage.ι₁_π₁_assoc, ConePackage.ι₁_π₂_assoc, ConePackage.ι₂_π₁_assoc,
      ConePackage.ι₂_π₂_assoc, zero_comp, comp_zero, add_zero, zero_add, S.sX_g_assoc,
      Preadditive.sub_comp, ← g.toHomologicalComplex.comm_assoc, sub_self]
    exact (conePackage (𝟙 M)).π₁_ι₁_add_π₂_ι₂ n
  s_g := gradedApp_ext fun n => by
    rw [gradedApp_comp, gradedApp_ofDifferentialGradedMap, gradedApp_shiftToCone (f := f) (g := g),
      coneToShift_f, gradedApp_id]
    simp only [Preadditive.comp_add, Category.assoc, ConePackage.ι₁_π₁_assoc,
      ConePackage.ι₁_π₂_assoc, zero_comp, comp_zero, add_zero, S.f_rX_assoc,
      ofShiftByOne_toShiftByOne]
  id := gradedApp_ext fun n => by
    rw [gradedApp_add, gradedApp_comp, gradedApp_comp, gradedApp_ofDifferentialGradedMap,
      gradedApp_ofDifferentialGradedMap, gradedApp_ofDifferentialGradedMap,
      coneIdentityToCone_f, coneToConeIdentity_f (g := g), coneToShift_f,
      gradedApp_shiftToCone (f := f) (g := g), gradedApp_id]
    have h := S.commutator_add_connectingX_f n
    have h' := S.rX_f_add_g_sX (n + 1)
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      ConePackage.ι₁_π₁_assoc, ConePackage.ι₁_π₂_assoc, ConePackage.ι₂_π₁_assoc,
      ConePackage.ι₂_π₂_assoc, zero_comp, comp_zero, add_zero, zero_add,
      toShiftByOne_ofShiftByOne_assoc]
    have e1 : (conePackage g).π₁ n ≫ g.toHomologicalComplex.f (n + 1) ≫ gradedApp S.s (n + 1) ≫
          (conePackage g).ι₁ n + (conePackage g).π₁ n ≫ gradedApp S.r (n + 1) ≫
            f.toHomologicalComplex.f (n + 1) ≫ (conePackage g).ι₁ n =
        (conePackage g).π₁ n ≫ (conePackage g).ι₁ n := by
      have h'' : g.toHomologicalComplex.f (n + 1) ≫ gradedApp S.s (n + 1) +
          gradedApp S.r (n + 1) ≫ f.toHomologicalComplex.f (n + 1) = 𝟙 _ := by
        exact (add_comm _ _).trans h'
      rw [← Preadditive.comp_add, ← Category.assoc (g.toHomologicalComplex.f (n + 1)),
        ← Category.assoc (gradedApp S.r (n + 1)), ← Preadditive.add_comp, h'', Category.id_comp]
    have e2 : (conePackage g).π₂ n ≫ (M.complex.d n (n + 1) ≫ gradedApp S.s (n + 1) -
          gradedApp S.s n ≫ L.complex.d n (n + 1)) ≫ (conePackage g).ι₁ n +
        (conePackage g).π₂ n ≫ S.connectingX n ≫ f.toHomologicalComplex.f (n + 1) ≫
          (conePackage g).ι₁ n = 0 := by
      rw [← Preadditive.comp_add, ← Category.assoc (S.connectingX n), ← Preadditive.add_comp, h,
        zero_comp, comp_zero]
    rw [← sub_eq_zero, ← (conePackage g).π₁_ι₁_add_π₂_ι₂ n, ← e1, ← e2]
    abel

/-- **`0 → C(1_M) → C(g) → K[1] → 0` is an admissible short exact sequence.** -/
theorem isAdmissibleShortExact_cone :
    IsAdmissibleShortExact S.coneIdentityToCone S.coneToShift :=
  ⟨S.coneGradedSplitting⟩

/-! ### The middle term is the cone of the connecting morphism, shifted -/

/-- The null-homotopy for `cone(δ) ⟶ L[1]`: minus the section. -/
noncomputable def coneConnectingα (n : ℤ) :
    M.complex.X (n + 1) ⟶ (shiftBy L 1).complex.X n :=
  -(gradedApp S.s (n + 1) ≫ toShiftByOne L n)

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The null-homotopy for `cone(δ) ⟶ L[1]` is right `A`-linear. -/
theorem coneConnectingα_mul (n i : ℤ) (U : Cᵒᵖ) (x : (M.complex.X (n + 1)).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (S.coneConnectingα (n + i)).val.app U (gradedCast (fun q ↦ (M.complex.X q).val.obj U)
        (add_right_comm n 1 i) ((M.mul (n + 1) i).app U x y)) =
      ((shiftBy L 1).mul n i).app U ((S.coneConnectingα n).val.app U x) y := by
  have hneg : ∀ {X Y : SheafOfModules.{m} R} (u : X ⟶ Y) (z : X.val.obj U),
      (-u).val.app U z = -(u.val.app U z) := fun u z => by
    change (ConcreteCategory.hom ((-u.val).app U)) z = _
    simp
  rw [coneConnectingα, coneConnectingα, hneg, hneg]
  have hR : ((shiftBy L 1).mul n i).app U
        (-((gradedApp S.s (n + 1) ≫ toShiftByOne L n).val.app U x)) y =
      -(((shiftBy L 1).mul n i).app U
        ((gradedApp S.s (n + 1) ≫ toShiftByOne L n).val.app U x) y) := by
    rw [map_neg, AddMonoidHom.neg_apply]
  rw [hR]
  refine congrArg Neg.neg (eq_of_heq ?_)
  have h1 : HEq ((gradedApp S.s (n + i + 1) ≫ toShiftByOne L (n + i)).val.app U
      (gradedCast (fun q ↦ (M.complex.X q).val.obj U) (add_right_comm n 1 i)
        ((M.mul (n + 1) i).app U x y)))
      ((L.mul (n + 1) i).app U ((gradedApp S.s (n + 1)).val.app U x) y) := by
    refine (comp_toShiftByOne_app_heq L (n + i) _ U _).trans ?_
    refine HEq.trans ?_ (heq_of_eq (S.s.map_smul (n + 1) i U x y))
    exact heq_dependent_apply (fun d (z : (M.complex.X d).val.obj U) =>
      (gradedApp S.s d).val.app U z) (add_right_comm n 1 i).symm (gradedCast_heq _ _ _)
  refine h1.trans ?_
  refine HEq.trans ?_ (shiftBy_mul_app_heq L 1 n i U _ y).symm
  exact heq_dependent_apply (fun d (z : (L.complex.X d).val.obj U) => (L.mul d i).app U z y) rfl
    (comp_toShiftByOne_app_heq L n _ U _).symm

/-- The null-homotopy condition for `cone(δ) ⟶ L[1]`. -/
theorem coneConnectingα_d (n : ℤ) :
    S.coneConnectingα n ≫ (shiftBy L 1).complex.d n (n + 1) +
        M.complex.d (n + 1) (n + 1 + 1) ≫ S.coneConnectingα (n + 1) =
      S.connecting.toHomologicalComplex.f (n + 1) ≫
        (shiftByMap 1 f).toHomologicalComplex.f (n + 1) := by
  have h := S.commutator_add_connectingX_f (n + 1)
  rw [coneConnectingα, coneConnectingα, connecting_f, shiftByMap_one_f, Category.assoc,
    toShiftByOne_ofShiftByOne_assoc, Preadditive.neg_comp, Category.assoc, toShiftByOne_d,
    Preadditive.comp_neg, neg_neg, Preadditive.comp_neg, ← Category.assoc,
    ← Category.assoc (S.connectingX (n + 1)), eq_neg_of_add_eq_zero_right h]
  simp only [Preadditive.sub_comp, Category.assoc, neg_sub]
  abel

/-- **The morphism `cone(δ) ⟶ L[1]`**: minus the section on the first summand and `f[1]` on the
second. -/
noncomputable def coneConnectingHom : cone S.connecting ⟶ shiftBy L 1 :=
  (conePackage S.connecting).desc (shiftByMap 1 f) S.coneConnectingα S.coneConnectingα_mul
    S.coneConnectingα_d

/-- `cone(δ) ⟶ L[1]` in coordinates. -/
theorem coneConnectingHom_f (n : ℤ) :
    S.coneConnectingHom.toHomologicalComplex.f n =
      (conePackage S.connecting).π₁ n ≫ S.coneConnectingα n +
        (conePackage S.connecting).π₂ n ≫ ofShiftByOne K n ≫ f.toHomologicalComplex.f (n + 1) ≫
          toShiftByOne L n := by
  rw [coneConnectingHom, ConePackage.desc_f_eq, shiftByMap_one_f]

/-- The inverse of `cone(δ) ⟶ L[1]` in degree `n`. -/
noncomputable def coneConnectingInvX (n : ℤ) :
    (shiftBy L 1).complex.X n ⟶ (cone S.connecting).complex.X n :=
  -(ofShiftByOne L n ≫ g.toHomologicalComplex.f (n + 1) ≫ (conePackage S.connecting).ι₁ n) +
    ofShiftByOne L n ≫ gradedApp S.r (n + 1) ≫ toShiftByOne K n ≫ (conePackage S.connecting).ι₂ n

/-- **`cone(δ) ⟶ L[1]` is an isomorphism**, being one in every degree. -/
instance isIso_coneConnectingHom : IsIso S.coneConnectingHom := by
  refine isIso_of_componentwise _ fun n => ⟨S.coneConnectingInvX n, ?_, ?_⟩
  · refine (conePackage S.connecting).hom_ext' ?_ ?_
    · rw [coneConnectingHom_f, coneConnectingInvX, coneConnectingα, Category.comp_id]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
        Preadditive.comp_neg, Category.assoc, ConePackage.ι₁_π₁_assoc, ConePackage.ι₁_π₂_assoc,
        zero_comp, add_zero, toShiftByOne_ofShiftByOne_assoc, S.sX_g_assoc, S.sX_rX_assoc,
        neg_neg, comp_zero, neg_zero]
    · rw [coneConnectingHom_f, coneConnectingInvX, Category.comp_id]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_neg, Category.assoc,
        ConePackage.ι₂_π₁_assoc, ConePackage.ι₂_π₂_assoc,
        zero_comp, zero_add, toShiftByOne_ofShiftByOne_assoc, S.f_g_assoc, S.f_rX_assoc,
        neg_zero, comp_zero, ofShiftByOne_toShiftByOne_assoc]
  · rw [coneConnectingHom_f, coneConnectingInvX, coneConnectingα]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
      Preadditive.comp_neg, Category.assoc, ConePackage.ι₁_π₁_assoc, ConePackage.ι₁_π₂_assoc,
      ConePackage.ι₂_π₁_assoc, ConePackage.ι₂_π₂_assoc, zero_comp, comp_zero, neg_zero, add_zero,
      zero_add, neg_neg, toShiftByOne_ofShiftByOne_assoc]
    have h'' : g.toHomologicalComplex.f (n + 1) ≫ gradedApp S.s (n + 1) +
        gradedApp S.r (n + 1) ≫ f.toHomologicalComplex.f (n + 1) = 𝟙 _ := by
      exact (add_comm _ _).trans (S.rX_f_add_g_sX (n + 1))
    rw [← Preadditive.comp_add, ← Category.assoc (g.toHomologicalComplex.f (n + 1)),
      ← Category.assoc (gradedApp S.r (n + 1)), ← Preadditive.add_comp, h'', Category.id_comp,
      ofShiftByOne_toShiftByOne]

/-- **The middle term of an admissible short exact sequence is, shifted by one, the cone of the
connecting morphism**: `cone(δ) ≅ L[1]`. -/
noncomputable def coneConnectingIso : cone S.connecting ≅ shiftBy L 1 :=
  asIso S.coneConnectingHom

end GradedSplitting

end SheafOfModules.DifferentialGradedModule

end
