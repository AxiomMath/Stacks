module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyGoodDivisors
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications

/-!
# The ratio map of a good fibre divisor (towards Stacks 0E6F)

Two inputs of the proof that a family of curves with two good relative divisors is a scheme near
the closed fibre (`AlgebraicGeometry.C1590Private.SchemeNearFibreOfGoodDivisors`).

## Main results

* `AlgebraicGeometry.C1590Private.fibreRatioRingHomFinite`: on the fibre, the ring map
  `R[x₁, …, xₙ] ⟶ Γ(Z, U)` sending the variables to generators of the affine complement `U` of the
  divisor is finite, because the restrictions of the global functions of the proper scheme `Z` are
  integral over the base field.
* `AlgebraicGeometry.C1590Private.rangeLeOpenComplementOfPreimage`: a scheme mapping into the
  complement of `E` in the fibre maps into the open complement of `D`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.C1590Private

universe u

/-- **(Q1) The fibre map is finite.** `Z` proper over a field `K`, `U ⊆ Z` open, `f j ∈ Γ(Z, U)`
generating `Γ(Z, U)` over the restrictions of the global functions (the generation clause of
`IsGoodDivisor`), `α : R → K` surjective, and `ψ : R[x₁..xₙ] → Γ(Z, U)` with `ψ xⱼ = fⱼ` and
`ψ (C a)` = the restriction of the pullback of `α a`. Then `ψ` is finite (`Γ(Z, ⊤)` is finite
over `K` by properness). -/
def FibreRatioRingHomFinite : Prop :=
  ∀ {Z : Scheme.{u}} {K : Type u} [Field K] (fZ : Z ⟶ Spec (.of K)) [IsProper fZ]
    (U : Z.Opens) (_ : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(Z, U)),
    Subring.closure (Set.range (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ∪
      Set.range f) = ⊤ →
    ∀ {R : Type u} [CommRing R] (α : R →+* K), Function.Surjective α →
    ∀ ψ : MvPolynomial (Fin n) R →+* Γ(Z, U), (∀ j, ψ (MvPolynomial.X j) = f j) →
      (∀ a, ψ (MvPolynomial.C a) = Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (fZ.appTop ((Scheme.ΓSpecIso (.of K)).inv (α a)))) →
      ψ.Finite

/-- **(Q1).** The ring map from the polynomial ring to the functions on the complement of a good
divisor of the fibre is finite. The restrictions of the global functions are integral over the
base field (Mathlib `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`), hence over the
image of `ψ`; with the generators `fⱼ` they generate, so `Γ(Z, U)` is integral and, being of finite
type over the field, finite over the polynomial ring. -/
theorem fibreRatioRingHomFinite : FibreRatioRingHomFinite := by
  intro Z K _ fZ _ U hU n f hgen R _ α hα ψ hψX hψC
  set r : Γ(Z, ⊤) →+* Γ(Z, U) := (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom with hr
  set κ : K →+* Γ(Z, U) := r.comp (fZ.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) with hκ
  let : Algebra (MvPolynomial (Fin n) R) Γ(Z, U) := ψ.toAlgebra
  let : Algebra R Γ(Z, U) := (ψ.comp MvPolynomial.C).toAlgebra
  let : Algebra K Γ(Z, U) := κ.toAlgebra
  let : Algebra R K := α.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) Γ(Z, U) := IsScalarTower.of_algebraMap_eq
    (fun _ => rfl)
  have : IsScalarTower R K Γ(Z, U) := IsScalarTower.of_algebraMap_eq (fun a => hψC a)
  have : Algebra.IsIntegral R K := ⟨fun x => (α.isIntegral_of_surjective hα) x⟩
  -- integrality
  have hint : ∀ g : Γ(Z, ⊤), _root_.IsIntegral (MvPolynomial (Fin n) R) (r g) := by
    intro g
    obtain ⟨p, hp, hpe⟩ := isIntegral_appTop_of_universallyClosed fZ g
    have hK : _root_.IsIntegral K (r g) := by
      refine ⟨p.map (Scheme.ΓSpecIso (.of K)).hom.hom, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap K Γ(Z, U)).comp (Scheme.ΓSpecIso (.of K)).hom.hom =
          r.comp fZ.appTop.hom := by
        ext a
        simp only [κ, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        have : (Scheme.ΓSpecIso (.of K)).inv.hom ((Scheme.ΓSpecIso (.of K)).hom.hom a) = a := by
          rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
        rw [this]
      rw [hcomp, ← Polynomial.hom_eval₂, hpe, map_zero]
    exact (isIntegral_trans (R := R) (A := K) _ hK).tower_top
  have hI : Algebra.IsIntegral (MvPolynomial (Fin n) R) Γ(Z, U) := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ (⊤ : Subring Γ(Z, U)) := trivial
    rw [← hgen] at hy
    refine Subring.closure_induction (p := fun y _ => _root_.IsIntegral (MvPolynomial (Fin n) R) y)
      (fun y hy => ?_) ?_ ?_ (fun _ _ _ _ => IsIntegral.add) (fun _ _ => IsIntegral.neg)
      (fun _ _ _ _ => IsIntegral.mul) hy
    · rcases hy with ⟨g, rfl⟩ | ⟨j, rfl⟩
      · exact hint g
      · rw [← hψX j]; exact isIntegral_algebraMap
    · exact isIntegral_zero
    · exact isIntegral_one
  -- finite type
  have hft : Algebra.FiniteType (MvPolynomial (Fin n) R) Γ(Z, U) := by
    have hle : U ≤ fZ ⁻¹ᵁ ⊤ := le_top
    have happLE := fZ.finiteType_appLE (isAffineOpen_top _) hU hle
    have hκft : κ.FiniteType := by
      have : κ = (fZ.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom := by
        ext a; rfl
      rw [this]
      exact happLE.comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
    have hC : (ψ.comp MvPolynomial.C).FiniteType := by
      have : ψ.comp MvPolynomial.C = κ.comp α := by ext a; exact hψC a
      rw [this]
      exact hκft.comp (RingHom.FiniteType.of_surjective _ hα)
    exact RingHom.FiniteType.of_comp_finiteType hC
  exact Algebra.IsIntegral.finite

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **(Q2) The complement of `E` maps into the complement of `D`.** If the inverse image of a
closed subspace `D ⊆ Y` along `q : h_V ⟶ Y` is the closed subspace of `h_V` cut out by an ideal
sheaf `E` of `V`, then every morphism `ι : V° ⟶ V` of the site whose scheme map lands in
`V ∖ supp E` gives `h_ι ≫ q` landing in the open complement `Y ∖ D`. -/
def RangeLeOpenComplementOfPreimage : Prop :=
  ∀ (Y : AlgebraicSpaces B integerBase hZ) (V : BigFppfOver B integerBase hZ)
    (q : yoneda.obj V ⟶ Y.obj) (D : Space.ClosedSubspaces B integerBase hZ Y.obj)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData),
    D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1 →
    ∀ (Vo : BigFppfOver B integerBase hZ) (ι : Vo ⟶ V),
      ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map ι ⁻¹ᵁ E.support.compl →
      ∀ (a : (BigFppfOver B integerBase hZ)ᵒᵖ) (x : (yoneda.obj Vo).obj a),
        (yoneda.map ι ≫ q).app a x ∈ (Space.openComplement B integerBase hZ D.1).obj a

/-- **(Q2).** A morphism of the site landing in the complement of `E` in the fibre gives a
morphism into the open complement of `D`. -/
theorem rangeLeOpenComplementOfPreimage : RangeLeOpenComplementOfPreimage B hZ := by
  intro Y V q D E hDE Vo ι hι a x A b hb
  have hnat : Y.obj.map b ((yoneda.map ι ≫ q).app a x) =
      q.app A ((yoneda.obj Vo).map b x ≫ ι) :=
    (NatTrans.naturality_apply (yoneda.map ι ≫ q) b x).symm
  rw [hnat] at hb
  have hmem : (yoneda.obj Vo).map b x ≫ ι ∈ (D.1.preimage q).obj A := hb
  rw [hDE] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨fun p => ?_⟩
  have h1 : (BigFppfOver.toScheme B integerBase hZ).map ((yoneda.obj Vo).map b x ≫ ι) p ∈
      (E.support : Set _) := by
    have hz' : z ≫ Space.closedSubschemeOverι B integerBase hZ V E =
        (yoneda.obj Vo).map b x ≫ ι := hz
    rw [← hz', Functor.map_comp, Scheme.Hom.comp_apply, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  have h2 := hι (show (BigFppfOver.toScheme B integerBase hZ).map ((yoneda.obj Vo).map b x) p ∈
    (⊤ : Opens _) from trivial)
  rw [Functor.map_comp, Scheme.Hom.comp_apply] at h1
  exact h2 h1

end AlgebraicGeometry.C1590Private

end
