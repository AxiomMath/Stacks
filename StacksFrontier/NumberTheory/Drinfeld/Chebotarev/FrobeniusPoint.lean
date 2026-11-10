module

public import StacksFrontier.NumberTheory.Drinfeld.Chebotarev.SemilinearWeilBound
public import StacksFrontier.NumberTheory.Drinfeld.Chebotarev.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.Generation

/-!
# Frobenius elements from geometric points with a prescribed Frobenius

Let `X` be a connected scheme locally of finite type over a finite field `k` with `q = p ^ e`
elements, `Ω` an algebraically closed extension of `k`, `Z` a finite étale cover of `X` and `σ` an
endomorphism of `Z` over `X`. Let `z : Spec Ω ⟶ Z` be a point lying over a point `x̄ ∈ X(Ω)` whose
image `x` is a closed point of degree `D`, with `z ≫ σ = Spec (a ↦ a ^ q ^ D) ≫ z`. Since
`a ↦ a ^ q ^ D` is the arithmetic Frobenius of `Ω` over `κ(x)`, the local Frobenius element at `x̄`
acts on the lift `z` as `σ` does (`AlgebraicGeometry.FrobeniusData.localElement_app_apply`), and
transporting along a path to the base point gives Frobenius data `c` at `x` and a point `w` of the
fibre at the base point with `c.element • w = σ w`
(`Stacks.Drinfeld.exists_frobeniusData_element_smul_eq`).

If moreover `Z` is the Galois cover of an open normal subgroup `U` with a point `z₀` of
stabilizer `U` and `σ z₀ = g • z₀`, some Frobenius element at `x` lies in `g U`
(`Stacks.Drinfeld.exists_frobeniusData_element_mem_smul`).

We also record two facts about a point `x̄ ∈ X(Ω)` fixed by `Spec (a ↦ a ^ q ^ D)`: its image is a
closed point whose degree divides `D` (`Stacks.Drinfeld.isClosed_and_dvd_of_fixed`), and `x̄` is
fixed by `Spec (a ↦ a ^ q ^ d)`, `d` the degree of its image
(`Stacks.Drinfeld.specMap_iterateFrobenius_residueDegree_comp`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.WeilBound
  Stacks.EtaleCohomology

open scoped Pointwise

universe u

namespace Stacks.Drinfeld

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
  (e : ℕ) (hq : Fintype.card k = p ^ e)

omit [IsAlgClosed Ω] in
/-- A point `x̄ ∈ X(Ω)` gives the point `x` of `X` and the embedding `κ(x) → Ω` it factors
through. -/
theorem specMap_comp_fromSpecResidueField_eq (t : Spec (.of Ω) ⟶ X) :
    Spec.map (Scheme.SpecToEquivOfField Ω X t).2 ≫
      X.fromSpecResidueField (Scheme.SpecToEquivOfField Ω X t).1 = t := by
  rw [← Scheme.SpecToEquivOfField_symm_apply, Equiv.symm_apply_apply]

include hq in
/-- **A point fixed by a power of the Frobenius lies over a closed point of dividing degree.** If
`x̄ ∈ X(Ω)` satisfies `Spec (a ↦ a ^ q ^ D) ≫ x̄ = x̄`, `D ≥ 1`, its image is a closed point of
degree dividing `D`. -/
theorem isClosed_and_dvd_of_fixed [LocallyOfFiniteType f] (t : fieldValuedPoints f Ω) {D : ℕ}
    (hD : D ≠ 0)
    (ht : Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * D))) ≫ t.1 = t.1) :
    IsClosed ({(Scheme.SpecToEquivOfField Ω X t.1).1} : Set X) ∧
      residueDegree f (Scheme.SpecToEquivOfField Ω X t.1).1 ∣ D := by
  obtain ⟨K, _, _, _, hK⟩ := FrobeniusSplitting.exists_finrank_eq k hD
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let j : K →ₐ[k] Ω := IsAlgClosed.lift
  set τ := frobeniusAlgEquiv Ω p e hq ^ D
  have hτ' : (τ.toAlgHom : Ω →+* Ω) = iterateFrobenius Ω p (e * D) := by
    ext a
    change τ a = _
    rw [frobeniusAlgEquiv_pow_apply, hq, iterateFrobenius_def, ← pow_mul]
  have hcardK : Fintype.card K = Fintype.card k ^ D := by
    rw [← hK]
    exact Module.card_eq_pow_finrank
  have hj : ∀ c : K, τ.toAlgHom (j c) = j c := fun c => by
    change τ (j c) = j c
    rw [frobeniusAlgEquiv_pow_apply, ← map_pow, ← hcardK, FiniteField.pow_card]
  have hτ : ∀ a : Ω, τ.toAlgHom a = a → a ∈ Set.range j := fun a ha => by
    change τ a = a at ha
    rw [frobeniusAlgEquiv_pow_apply, ← hcardK] at ha
    exact mem_range_of_pow_card_eq j.toRingHom ha
  obtain ⟨s, hs⟩ := (fixedFieldValuedPointsEquiv f j τ.toAlgHom hj hτ).surjective
    ⟨t, Subtype.ext (by
      change Spec.map (CommRingCat.ofHom (τ.toAlgHom : Ω →+* Ω)) ≫ t.1 = t.1
      rwa [hτ'])⟩
  have hst : Spec.map (CommRingCat.ofHom j.toRingHom) ≫ s.1 = t.1 :=
    congrArg (fun u => u.1.1) hs
  have hpt : (Scheme.SpecToEquivOfField Ω X t.1).1 = (Scheme.SpecToEquivOfField K X s.1).1 := by
    rw [← hst, Scheme.SpecToEquivOfField_specMap_comp]
  set xι := Scheme.SpecToEquivOfField K X s.1
  have hσ : residueEmbeddings f K xι.1 := ⟨xι.2, by
    have hs2 := s.2
    rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply s.1,
      Scheme.SpecToEquivOfField_symm_apply, fromSpecResidueField_comp_eq_iff] at hs2
    exact hs2⟩
  rw [hpt, ← hK]
  exact isClosed_and_dvd_of_residueEmbeddings f K xι.1 hσ

omit [IsAlgClosed Ω] in
include hq in
/-- **A point is fixed by the Frobenius of its residue field.** If the image `x` of `x̄ ∈ X(Ω)`
has positive degree `d`, then `Spec (a ↦ a ^ q ^ d) ≫ x̄ = x̄`. -/
theorem specMap_iterateFrobenius_residueDegree_comp [LocallyOfFiniteType f]
    (t : fieldValuedPoints f Ω) (hd : residueDegree f (Scheme.SpecToEquivOfField Ω X t.1).1 ≠ 0) :
    Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p
        (e * residueDegree f (Scheme.SpecToEquivOfField Ω X t.1).1))) ≫ t.1 = t.1 := by
  set y := (Scheme.SpecToEquivOfField Ω X t.1).1
  set ι := (Scheme.SpecToEquivOfField Ω X t.1).2
  let : Algebra k (X.residueField y) := (fieldToResidue f y).hom.toAlgebra
  have : Module.Finite k (X.residueField y) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have : Finite (X.residueField y) := Module.finite_of_finite k
  let := Fintype.ofFinite (X.residueField y)
  have hcard : Fintype.card (X.residueField y) = p ^ (e * residueDegree f y) := by
    rw [Module.card_eq_pow_finrank (K := k), hq, ← pow_mul]
    rfl
  conv_lhs => rw [← specMap_comp_fromSpecResidueField_eq Ω t.1]
  rw [← Category.assoc, ← Spec.map_comp]
  conv_rhs => rw [← specMap_comp_fromSpecResidueField_eq Ω t.1]
  congr 2
  ext a
  change (ι.hom a) ^ p ^ (e * residueDegree f y) = ι.hom a
  rw [← map_pow, ← hcard, FiniteField.pow_card]

include hq in
/-- **The local Frobenius acts on a twisted lift as the deck transformation.** Let `Z` be a finite
étale cover of `X`, `σ` an endomorphism of `Z` over `X` and `z : Spec Ω ⟶ Z` a point over `k`
whose image in `X` is a closed point of degree `D ≥ 1` with `z ≫ σ = Spec (a ↦ a ^ q ^ D) ≫ z`.
Then there are Frobenius data `c` at that point and a point `w` of the fibre of `Z` at the base
point with `c.element • w = σ w`. -/
theorem exists_frobeniusData_element_smul_eq [ConnectedSpace X] [LocallyOfFiniteType f]
    [Algebra.IsAlgebraic k Ω] (base : GeometricPoint X) (Z : FiniteEtaleOver X) (σ : Z ⟶ Z)
    (z : Spec (.of Ω) ⟶ Z.left) (hz : z ≫ Z.hom ≫ f = baseMap k Ω) {D : ℕ} (hD : D ≠ 0)
    (htw : z ≫ σ.left = Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * D))) ≫ z)
    (hdeg : residueDegree f (Scheme.SpecToEquivOfField Ω X (z ≫ Z.hom)).1 = D) :
    ∃ (hx : IsClosed ({(Scheme.SpecToEquivOfField Ω X (z ≫ Z.hom)).1} : Set X))
      (c : FrobeniusData base ⟨_, hx⟩) (w : (finiteEtaleFiberFunctor base).obj Z),
      c.element • w = (finiteEtaleFiberFunctor base).map σ w := by
  set t : fieldValuedPoints f Ω := ⟨z ≫ Z.hom, by rwa [Category.assoc]⟩
  have hfix : Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (e * D))) ≫ t.1 = t.1 := by
    change _ ≫ z ≫ Z.hom = z ≫ Z.hom
    rw [← Category.assoc, ← htw, Category.assoc, MorphismProperty.Over.w σ]
  obtain ⟨hcl, -⟩ := isClosed_and_dvd_of_fixed f Ω p e hq t hD hfix
  set y := (Scheme.SpecToEquivOfField Ω X (z ≫ Z.hom)).1
  set ι := (Scheme.SpecToEquivOfField Ω X (z ≫ Z.hom)).2
  have hι : Spec.map ι ≫ X.fromSpecResidueField y = z ≫ Z.hom :=
    specMap_comp_fromSpecResidueField_eq Ω (z ≫ Z.hom)
  let : Algebra k (X.residueField y) := (fieldToResidue f y).hom.toAlgebra
  let : Algebra (X.residueField y) Ω := ι.hom.toAlgebra
  have : Module.Finite k (X.residueField y) :=
    Module.finite_of_finrank_pos (show 0 < residueDegree f y by omega)
  have hfin : Finite (X.residueField y) := Module.finite_of_finite k
  let := Fintype.ofFinite (X.residueField y)
  have hover : fieldToResidue f y ≫ ι = CommRingCat.ofHom (algebraMap k Ω) := by
    rwa [← fromSpecResidueField_comp_eq_iff, hι, Category.assoc]
  have : IsScalarTower k (X.residueField y) Ω := IsScalarTower.of_algebraMap_eq fun c =>
    (congrArg (fun φ => φ.hom c) hover).symm
  have : Algebra.IsAlgebraic (X.residueField y) Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) (X.residueField y)
  have : IsAlgClosure (X.residueField y) Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨path⟩ := nonempty_finiteEtaleFiberFunctorIso
    (x := (algebraicClosureGeometricPoint (X.residueField y) Ω).map (X.fromSpecResidueField y))
    (x' := base)
  let c : FrobeniusData base ⟨y, hcl⟩ :=
    { closure := Ω
      finite_residueField := hfin
      path := path }
  have hzq : z ≫ Z.hom = c.geometricPoint.hom := hι.symm
  set qz : finiteEtaleFiber c.geometricPoint Z := ⟨z, hzq⟩
  have hcard : Fintype.card (X.residueField y) = p ^ (e * D) := by
    rw [Module.card_eq_pow_finrank (K := k), hq, ← pow_mul]
    change p ^ (e * residueDegree f y) = _
    rw [hdeg]
  have hfrob : (c.frobenius : Ω →+* Ω) = iterateFrobenius Ω p (e * D) := by
    ext a
    change a ^ Fintype.card (X.residueField y) = a ^ p ^ (e * D)
    convert congrArg (a ^ ·) hcard using 2
  have hloc :
      (c.localElement.asIso.app Z).hom qz =
        (finiteEtaleFiberFunctor c.geometricPoint).map σ qz := by
    apply Subtype.ext
    rw [FrobeniusData.localElement_app_apply c Z qz, hfrob]
    exact htw.symm
  refine ⟨hcl, c, path.hom.app Z qz, ?_⟩
  change ((path.conjAut c.localElement).asIso.app Z).hom (path.hom.app Z qz) = _
  refine (Stacks.FundamentalGroup.conjAut_app_apply path c.localElement Z qz).trans ?_
  rw [hloc]
  exact congrArg (fun φ => φ qz) (path.hom.naturality σ)

/-- **Transport into a coset.** Let `Z` be a finite étale cover with a point `z₀` of its fibre at
the base point whose stabilizer is `U` and on whose fibre `π₁` acts transitively, and `σ` an
endomorphism of `Z` with `σ z₀ = g • z₀`. If Frobenius data `c` at `x` and a point `w` satisfy
`c.element • w = σ w`, some Frobenius element at `x` lies in `g U`. -/
theorem exists_frobeniusData_element_mem_smul {X : Scheme.{u}} [ConnectedSpace X]
    {base : GeometricPoint X} {x : closedPoints X} (Z : FiniteEtaleOver X) (σ : Z ⟶ Z)
    (U : Subgroup (EtaleFundamentalGroup X base)) (g : EtaleFundamentalGroup X base)
    (z₀ : (finiteEtaleFiberFunctor base).obj Z)
    (hstab : ∀ γ : EtaleFundamentalGroup X base, γ • z₀ = z₀ ↔ γ ∈ U)
    (htrans : ∀ w : (finiteEtaleFiberFunctor base).obj Z, ∃ γ : EtaleFundamentalGroup X base,
      γ • z₀ = w)
    (hσ : (finiteEtaleFiberFunctor base).map σ z₀ = g • z₀) (c : FrobeniusData base x)
    (w : (finiteEtaleFiberFunctor base).obj Z)
    (hw : c.element • w = (finiteEtaleFiberFunctor base).map σ w) :
    ∃ c' : FrobeniusData base x, c'.element ∈ g • (U : Set (EtaleFundamentalGroup X base)) := by
  obtain ⟨γ, rfl⟩ := htrans w
  have hnat : ∀ (δ : EtaleFundamentalGroup X base) (v : (finiteEtaleFiberFunctor base).obj Z),
      (finiteEtaleFiberFunctor base).map σ (δ • v) = δ • (finiteEtaleFiberFunctor base).map σ v :=
    fun δ v => (congrArg (fun φ => φ v) (δ.asIso.hom.naturality σ)).symm
  rw [hnat, hσ] at hw
  refine ⟨{ c with path := c.path ≪≫ (γ⁻¹ : EtaleFundamentalGroup X base).asIso }, ?_⟩
  rw [FrobeniusData.element_path_trans, inv_inv, mem_leftCoset_iff, SetLike.mem_coe, ← hstab,
    mul_smul, mul_smul, mul_smul, hw, inv_smul_smul, inv_smul_smul]

end Stacks.Drinfeld

end
