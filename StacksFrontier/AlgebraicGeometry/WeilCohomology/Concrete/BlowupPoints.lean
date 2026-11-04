module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Blowup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SeparableExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SeparatingClosedPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separable closed points of a blowup off the exceptional divisor

Let `b : X' ⟶ X` be the blowing up of a smooth projective scheme `X` over `k` in a smooth closed
subscheme `Z`. The proof of Stacks 0FIS chooses a closed point `x' ∈ X'` off the exceptional
divisor whose residue field is separable over `k` (Varieties, Tag 056U), and uses that
`H^0(X') ⟶ H^0(x')` is injective (axiom (A8) and Tag 0FVS). Here finitely many such points are
chosen, one detecting each factor of `Γ(X', 𝒪_{X'})`, so that no reduction to a connected `X` is
needed:

* the complement of the exceptional divisor is dense (it is the complement of an effective
  Cartier divisor, Tag 02OS (2)), so Stacks 056U provides the points
  (`AlgebraicGeometry.exists_separableClosedPoints_injective_Γevaluation`);
* `b` is an isomorphism over `X ∖ Z` (Tag 02OS (1)), so each point `x' ↪ X'` has
  `x' ×_X X' = x'` along `b` (`Stacks.WeilCohomology.isIso_pullback_fst_comp_of_isIso_restrict`);
* restriction to the points is injective on `H^0(X')`, by (A8) and the finite étale form of
  Tag 0FVS (`Stacks.WeilCohomology.FirstChernClassData.injective_pull_specMap_family_of_axioms`).

## Main results

* `Stacks.WeilCohomology.isIso_pullback_fst_comp_of_isIso_restrict`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.exists_separablePoints_blowup`: the points,
  as morphisms `Spec(κ(x'ⱼ)) ⟶ X'` of smooth projective `k`-schemes.
* `Stacks.WeilCohomology.FirstChernClassData.pull_points_injective`: restriction to them is
  injective on `H^0(X')`.

## References

* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

/-- **A morphism which is an isomorphism over an open `U` has trivial fibre products along maps
into `U`.** If `b ∣_ U` is an isomorphism and `t : T ⟶ X'` lands in `b⁻¹ U`, then the projection
`T ×_X X' ⟶ T` along `t ≫ b` and `b` is an isomorphism, with inverse `(1, t)`. -/
theorem isIso_pullback_fst_comp_of_isIso_restrict {T X' X : Scheme.{u}} (t : T ⟶ X') (b : X' ⟶ X)
    (U : X.Opens) [IsIso (b ∣_ U)] (ht : ∀ x, b (t x) ∈ U) :
    IsIso (Limits.pullback.fst (t ≫ b) b) := by
  -- `b` is a monomorphism on maps into `b⁻¹ U`
  have hmono : ∀ {P : Scheme.{u}} (α β : P ⟶ X'), (∀ p, α p ∈ b ⁻¹ᵁ U) → (∀ p, β p ∈ b ⁻¹ᵁ U) →
      α ≫ b = β ≫ b → α = β := by
    intro P α β hα hβ h
    have hlift : ∀ γ : P ⟶ X', (∀ p, γ p ∈ b ⁻¹ᵁ U) → ∃ γ', γ' ≫ (b ⁻¹ᵁ U).ι = γ := fun γ hγ =>
      ⟨IsOpenImmersion.lift (b ⁻¹ᵁ U).ι γ (by
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hγ p), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨α', hα''⟩ := hlift α hα
    obtain ⟨β', hβ''⟩ := hlift β hβ
    have : α' ≫ b ∣_ U = β' ≫ b ∣_ U := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        reassoc_of% hα'', reassoc_of% hβ'', h]
    rw [← hα'', ← hβ'', (cancel_mono (b ∣_ U)).mp this]
  refine ⟨⟨pullback.lift (𝟙 T) t (by rw [Category.id_comp]), ?_, pullback.lift_fst _ _ _⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
    refine hmono _ _ (fun p => ht _) (fun p => ?_) (by rw [Category.assoc, pullback.condition])
    show b (pullback.snd (t ≫ b) b p) ∈ U
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact ht _

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

omit [IsClosedImmersion i.hom.left] in
/-- The blowing up morphism is an isomorphism over the complement of the centre. -/
@[sga "7 XVIII 2.1" "special case"]
theorem isIso_blowupHom_restrict :
    IsIso (Stacks.Blowup.blowUpToBase i.hom.left.ker ∣_
      (⟨(i.hom.left.ker.support : Set X.obj.left)ᶜ, i.hom.left.ker.support.isClosed.isOpen_compl⟩ :
        X.obj.left.Opens)) := by
  have h : Stacks.Blowup.blowUpToBase i.hom.left.ker =
      (AlgebraicGeometry.blowUpIso i.hom.left.ker).inv ≫ AlgebraicGeometry.blowUpToBase _ := by
    rw [Iso.eq_inv_comp, AlgebraicGeometry.blowUpIso_hom_blowUpToBase]
  rw [h, morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (instIsIsoSchemeMorphismRestrict (AlgebraicGeometry.blowUpIso i.hom.left.ker).inv _)
    (isIso_blowUp_restrict_compl_support i.hom.left.ker)

/-- The support of the ideal of the centre is the centre. -/
theorem mem_support_ker_iff (x : X.obj.left) :
    x ∈ (i.hom.left.ker.support : Set X.obj.left) ↔ x ∈ Set.range i.hom.left.base := by
  rw [Scheme.Hom.support_ker, i.hom.left.isClosedEmbedding.isClosed_range.closure_eq]

/-- **Finitely many separable closed points of the blowup off the exceptional divisor detect its
global functions**: there are closed points `x'ⱼ` of `X'`, with `b(x'ⱼ) ∉ Z` and `κ(x'ⱼ)` finite
separable over `k`, such that evaluation at them is injective on `Γ(X', 𝒪_{X'})`. -/
theorem exists_separablePoints_blowup :
    ∃ (ι : Type u) (_ : Finite ι) (x : ι → (blowupObj i).obj.left),
      (∀ j, (blowupHom i).hom.left (x j) ∉ Set.range i.hom.left.base ∧
        letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ (blowupObj i).obj.hom.appTop ≫
          (blowupObj i).obj.left.Γevaluation (x j)).hom.toAlgebra
        Module.Finite k ((blowupObj i).obj.left.residueField (x j)) ∧
          Algebra.IsSeparable k ((blowupObj i).obj.left.residueField (x j))) ∧
      Function.Injective fun s : Γ((blowupObj i).obj.left, ⊤) =>
        fun j => ((blowupObj i).obj.left.Γevaluation (x j)).hom s := by
  let I := i.hom.left.ker
  let U : (blowupObj i).obj.left.Opens := (Stacks.Blowup.exceptionalIdeal I).support.compl
  have hmem : ∀ x : (blowupObj i).obj.left, x ∈ U →
      (blowupHom i).hom.left x ∉ Set.range i.hom.left.base := by
    intro x hx hrange
    apply hx
    show x ∈ (((I.comap (Stacks.Blowup.blowUpToBase I)).support :
      TopologicalSpace.Closeds (Stacks.Blowup.blowUp I)) : Set (Stacks.Blowup.blowUp I))
    rw [Scheme.IdealSheafData.support_comap]
    exact (mem_support_ker_iff i _).mpr hrange
  obtain ⟨ι, hι, x, hx, hinj⟩ :=
    exists_separableClosedPoints_injective_Γevaluation (blowupObj i).obj.hom U
      (dense_of_isSchemeTheoreticallyDense _
        (Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal I))
  exact ⟨ι, hι, x, fun j => ⟨hmem _ (hx j).1, (hx j).2.2⟩, hinj⟩

/-! ### Closed points as smooth projective schemes -/

/-- The `k`-algebra structure on the residue field `κ(x)` of a point of a `k`-scheme. -/
abbrev residueAlgebra (X : (SmoothProjectiveScheme k).FullSubcategory) (x : X.obj.left) :
    Algebra k (X.obj.left.residueField x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop ≫ X.obj.left.Γevaluation x).hom.toAlgebra

/-- `Spec(κ(x)) ⟶ X ⟶ Spec(k)` is `Spec` of the structure map of `κ(x)`. -/
theorem fromSpecResidueField_comp_hom (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : X.obj.left) :
    letI := residueAlgebra X x
    X.obj.left.fromSpecResidueField x ≫ X.obj.hom =
      specStructure k (X.obj.left.residueField x) := by
  let := residueAlgebra X x
  have h1 : X.obj.hom = X.obj.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      X.obj.hom.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc X.obj.hom,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [h1, Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- `Spec(κ(x)) ⟶ X ⟶ Spec Γ(X, 𝒪_X)` is `Spec` of evaluation at `x`. -/
theorem fromSpecResidueField_comp_toSpecΓ (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : X.obj.left) :
    X.obj.left.fromSpecResidueField x ≫ X.obj.left.toSpecΓ =
      Spec.map (X.obj.left.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

variable {X : (SmoothProjectiveScheme k).FullSubcategory} (x : X.obj.left)

/-- **The closed point `x` as a morphism `Spec(κ(x)) ⟶ X`** of smooth projective `k`-schemes, for
`κ(x)` finite separable over `k`. -/
def pointHom [letI := residueAlgebra X x; Module.Finite k (X.obj.left.residueField x)]
    [letI := residueAlgebra X x; Algebra.IsSeparable k (X.obj.left.residueField x)] :
    letI := residueAlgebra X x
    spec k (X.obj.left.residueField x) ⟶ X :=
  letI := residueAlgebra X x
  SmoothProjectiveScheme.homMk (X.obj.left.fromSpecResidueField x)
    (fromSpecResidueField_comp_hom X x)

/-- Evaluation at `x`, as a map of `k`-algebras `Γ(X, 𝒪_X) → κ(x)`. -/
def evalAlgHom : letI := residueAlgebra X x
    globalSections X →ₐ[k] X.obj.left.residueField x :=
  letI := residueAlgebra X x
  { (X.obj.left.Γevaluation x).hom with commutes' := fun _ => rfl }

/-- The composite `Spec(κ(x)) ⟶ X ⟶ Spec Γ(X, 𝒪_X)` is `Spec` of evaluation at `x`. -/
theorem pointHom_comp_toSpecGlobalSections
    [letI := residueAlgebra X x; Module.Finite k (X.obj.left.residueField x)]
    [letI := residueAlgebra X x; Algebra.IsSeparable k (X.obj.left.residueField x)] :
    letI := residueAlgebra X x
    pointHom x ≫ toSpecGlobalSections X = specMap (evalAlgHom x) := by
  let := residueAlgebra X x
  refine hom_ext_left ?_
  show X.obj.left.fromSpecResidueField x ≫ X.obj.left.toSpecΓ = _
  rw [fromSpecResidueField_comp_toSpecΓ]
  rfl

end SmoothProjectiveScheme

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **Restriction to finitely many separable closed points detecting `Γ(X, 𝒪_X)` is injective on
`H^0(X)`**, under axioms (A1), (A3), (A4), (A5) and (A8): by (A8), `H^0(X) = H^0(Spec Γ(X, 𝒪_X))`,
and the restriction to the points is then the pullback along `Spec(κ(xⱼ)) ⟶ Spec Γ(X, 𝒪_X)`,
injective by the finite étale form of Stacks 0FVS. -/
theorem pull_points_injective [CharZero F] (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    (hA8 : 𝔇.GlobalSectionsAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) {ι : Type u}
    [Finite ι]
    (x : ι → X.obj.left) [Nonempty ι]
    [hfin : ∀ j, letI := residueAlgebra X (x j); Module.Finite k (X.obj.left.residueField (x j))]
    [hsep : ∀ j, letI := residueAlgebra X (x j);
      Algebra.IsSeparable k (X.obj.left.residueField (x j))]
    (hinj : Function.Injective fun s : Γ(X.obj.left, ⊤) =>
      fun j => (X.obj.left.Γevaluation (x j)).hom s) :
    ∀ a ∈ 𝔇.grade X 0, (∀ j, 𝔇.pull (pointHom (x j)) a = 0) → a = 0 := by
  intro a ha h0
  let : ∀ j, Algebra k (X.obj.left.residueField (x j)) := fun j => residueAlgebra X (x j)
  have : Nontrivial (globalSections X) := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    refine ⟨⟨1, 0, fun h => one_ne_zero (α := X.obj.left.residueField (x j)) ?_⟩⟩
    have := congrArg (X.obj.left.Γevaluation (x j)).hom h
    rwa [map_one, map_zero] at this
  obtain ⟨a0, ha0⟩ := (hA8 X).2 ⟨a, ha⟩
  have ha0' : 𝔇.pull (toSpecGlobalSections X) a0 = a := congrArg Subtype.val ha0
  have : (a0 : 𝔇.H (spec k (globalSections X))) = 0 := by
    apply 𝔇.injective_pull_specMap_family_of_axioms hA1 hA3 hA4 hA5
      (L := fun j => X.obj.left.residueField (x j)) (fun j => evalAlgHom (x j)) hinj
    funext j
    show 𝔇.pull (specMap (evalAlgHom (x j))) a0 = 𝔇.pull (specMap (evalAlgHom (x j))) 0
    rw [map_zero, ← pointHom_comp_toSpecGlobalSections, 𝔇.pull_comp, AlgHom.comp_apply, ha0']
    exact h0 j
  rw [← ha0', this, map_zero]

end FirstChernClassData

end Stacks.WeilCohomology

end
