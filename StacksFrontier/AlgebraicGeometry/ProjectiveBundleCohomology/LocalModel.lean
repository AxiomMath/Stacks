module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BundleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.SectionRing
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The projective bundle over an open trivializing the module

Let `S` be a scheme, `E` an `𝒪_S`-module and `V` an affine open of `S` over which `E` is free of
rank `n + 1`. Then the sections `Γ(E, V)` are a free `Γ(S, V)`-module of rank `n + 1`, the graded
ring `Γ(V, Sym(E))` is the polynomial ring `Γ(S, V)[T₀, …, Tₙ]` graded by total degree, and so
the part `π⁻¹(V)` of the projective bundle `𝐏(E)` lying over `V` is the projective space
`Proj Γ(S, V)[T₀, …, Tₙ]`, with `𝒪_{𝐏(E)}(d)` restricting to its twist `𝒪(d)`.

## Main results

* `nonempty_basis_sections`: a trivialization of `E` over `V` gives a basis of `Γ(E, V)` over
  `Γ(S, V)`.
* `toPolyGrading` and `ofPolyGrading`: mutually inverse graded ring homomorphisms between
  `Γ(V, Sym(E))` and `Γ(S, V)[T₀, …, Tₙ]`, attached to a basis of `Γ(E, V)` indexed by
  `Fin (n + 1)`.
* `isZero_rightDerivedPlus_pushforward_twist_of_poly`: `Rᵠ π_* 𝒪_{𝐏(E)}(d) = 0` as soon as
  `Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` for every ring `R`.
* `isZero_rightDerivedPlus_pushforward_twist_of_ne`: **`Rᵠ π_* 𝒪_{𝐏(E)}(d) = 0` for every
  `q ≠ 0, n`**, for `E` finite locally free of constant rank `n + 1` over an arbitrary scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-! ### A basis of the sections over a trivializing open -/

section Basis

variable {S : Scheme.{u}} (E : S.Modules)

/-- **A trivialization of `E` over `V` gives a basis of `Γ(E, V)` over `Γ(S, V)`**, indexed by
the index type of the free module: the standard basis of the sections of the free module,
carried across the trivialization. -/
public theorem nonempty_basis_sections {I : Type u} [Finite I] {V : S.Opens}
    (e : E.restrict V.ι ≅ SheafOfModules.free.{u} I) :
    Nonempty (Module.Basis I Γ(S, V) Γ(E, V)) := by
  classical
  rw [← V.ι_image_top]
  let _ : Module ↑Γ(S, V.ι ''ᵁ (⊤ : (V.toScheme).Opens))
      ↑((E.restrict V.ι).val.obj (op (⊤ : (V.toScheme).Opens))) :=
    inferInstanceAs (Module ↑Γ(S, V.ι ''ᵁ (⊤ : (V.toScheme).Opens))
      ↑Γ(E, V.ι ''ᵁ (⊤ : (V.toScheme).Opens)))
  let b : Module.Basis I ↑((V.toScheme).ringCatSheaf.obj.obj (op (⊤ : (V.toScheme).Opens)))
      ↑((SheafOfModules.free.{u} (R := (V.toScheme).ringCatSheaf) I).val.obj
        (op (⊤ : (V.toScheme).Opens))) :=
    Stacks.SheafOfModules.freeCoordBasis
      (V.toScheme).ringCatSheaf.property (ι := I) (op (⊤ : (V.toScheme).Opens))
  let Le : ↑((SheafOfModules.free.{u} (R := (V.toScheme).ringCatSheaf) I).val.obj
        (op (⊤ : (V.toScheme).Opens))) ≃ₗ[↑((V.toScheme).ringCatSheaf.obj.obj
          (op (⊤ : (V.toScheme).Opens)))]
      ↑((E.restrict V.ι).val.obj (op (⊤ : (V.toScheme).Opens))) :=
    ((PresheafOfModules.evaluation _ (op (⊤ : (V.toScheme).Opens))).mapIso
    ((SheafOfModules.forget _).mapIso e.symm)).toLinearEquiv
  let ρ := (Scheme.Hom.appIso V.ι (⊤ : (V.toScheme).Opens)).symm.commRingCatIsoToRingEquiv
  exact ⟨(b.map Le).mapCoeffs ρ fun c x =>
    (Scheme.Modules.smul_restrictAppIso_hom_apply V.ι E ⊤ c x).symm⟩

/-- **A finite locally free module of constant rank is quasi-coherent** ([Stacks, Tag 01C7]). -/
public theorem isQuasicoherent_of_isFiniteLocallyFreeOfRank {r : ℕ}
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E r) : E.IsQuasicoherent := by
  have : SheafOfModules.IsLocallyFree.{u, u, u} E :=
    (Stacks.Modules.isLocallyFree_iff_localGenerators E).mp fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hfree x
      exact ⟨U, hx, _, ⟨e⟩⟩
  obtain ⟨q, hq⟩ := this.exists_isLocallyFreeData
  exact q.quasiCoherentData.isQuasicoherent

end Basis

/-! ### The section ring over a trivializing affine open is a polynomial ring -/

section Graded

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) {V : S.Opens} (hV : IsAffineOpen V)

/-- The graded ring of sections of `Sym(E)` over an affine open, to the symmetric algebra of the
sections of `E`. -/
public def toSymGrading :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V →+*ᵍ
      fun k : ℕ => SymPow.symmetricPower k Γ(S, V) Γ(E, V) where
  toRingHom := (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).toRingHom
  map_mem {k x} hx :=
    (Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hV hqc k x).mpr hx

/-- The inverse of `toSymGrading`. -/
public def ofSymGrading :
    (fun k : ℕ => SymPow.symmetricPower k Γ(S, V) Γ(E, V)) →+*ᵍ
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V where
  toRingHom := (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).symm.toRingHom
  map_mem {k x} hx :=
    (Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv E hV hqc k _).mp
      (by simpa using hx)

variable {n : ℕ} (b : Module.Basis (Fin (n + 1)) Γ(S, V) Γ(E, V))

/-- **`Γ(V, Sym(E)) → Γ(S, V)[T₀, …, Tₙ]`**, the graded ring homomorphism attached to a basis of
`Γ(E, V)`. -/
public def toPolyGrading :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V →+*ᵍ
      Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n :=
  (SymPow.gradedMvPolynomialHom b).comp (toSymGrading E hqc hV)

/-- **`Γ(S, V)[T₀, …, Tₙ] → Γ(V, Sym(E))`**, the inverse of `toPolyGrading`. -/
public def ofPolyGrading :
    Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n →+*ᵍ
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V :=
  (ofSymGrading E hqc hV).comp (SymPow.gradedMvPolynomialInv b)

/-- `toPolyGrading` is a left inverse of `ofPolyGrading`. -/
public theorem toPolyGrading_ofPolyGrading (p : MvPolynomial (Fin (n + 1)) Γ(S, V)) :
    toPolyGrading E hqc hV b (ofPolyGrading E hqc hV b p) = p := by
  show SymmetricAlgebra.equivMvPolynomial b
      ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc)
        ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).symm
          ((SymmetricAlgebra.equivMvPolynomial b).symm p))) = p
  simp

/-- `ofPolyGrading` is a left inverse of `toPolyGrading`. -/
public theorem ofPolyGrading_toPolyGrading
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionRing V) :
    ofPolyGrading E hqc hV b (toPolyGrading E hqc hV b x) = x := by
  show (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).symm
      ((SymmetricAlgebra.equivMvPolynomial b).symm
        (SymmetricAlgebra.equivMvPolynomial b
          ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc) x))) = x
  simp

end Graded

/-! ### Vanishing over a trivializing affine open -/

section Vanishing

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)

/-- **Vanishing on the chart from vanishing on projective space.** Over an affine open `V` with a
basis of `Γ(E, V)` of cardinality `n + 1`, `Hᵠ(Proj Γ(V, Sym(E)), 𝒪(d))` vanishes as soon as
`Hᵠ(ℙⁿ_{Γ(S, V)}, 𝒪(d))` does. -/
public theorem isZero_Hgroup_chart_twist_of_poly {V : S.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) Γ(S, V) Γ(E, V)) (d : ℤ) (q : ℕ)
    (h : IsZero (Hgroup (AlgebraicGeometry.Proj
        (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n)).ringCatSheaf ⊤ q
      (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading Γ(S, V) n) d))) :
    IsZero (Hgroup (AlgebraicGeometry.Proj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf ⊤ q
      (twistingSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) d)) :=
  (isZero_Hgroup_twistingSheaf_iff_of_inverse (ofPolyGrading E hqc hV b)
      (toPolyGrading E hqc hV b) (ofPolyGrading_toPolyGrading E hqc hV b)
      (toPolyGrading_ofPolyGrading E hqc hV b) d q).mpr h

/-- **Vanishing over a trivializing affine open from vanishing on projective space.** -/
public theorem isZero_Hgroup_preimage_twist_of_poly
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {V : S.Opens}
    (hV : IsAffineOpen V) {n : ℕ}
    (e : E.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin (n + 1)))) (d : ℤ) (q : ℕ)
    (h : ∀ R : CommRingCat.{u}, IsZero (Hgroup (AlgebraicGeometry.Proj
        (Stacks.ProjectiveCohomology.polyGrading R n)).ringCatSheaf ⊤ q
      (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading R n) d))) :
    IsZero (Hgroup
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V) q
      (D.algebra.piece d)) := by
  obtain ⟨b⟩ := nonempty_basis_sections E e
  have := D.chartData.chart_isOpenImmersion V hV
  rw [← D.chartData.chart_range V hV]
  refine (isZero_Hgroup_image_top_iff _ _ q).mpr ?_
  refine (Iso.isZero_iff ((Hfunctor (AlgebraicGeometry.Proj
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf ⊤ q).mapIso
      (D.chartData.chartIso V hV d))).mpr ?_
  exact isZero_Hgroup_chart_twist_of_poly E hqc hV (b.reindex Equiv.ulift) d q (h Γ(S, V))

/-- **The higher direct images of a twist on `𝐏(E)` vanish in a degree in which the cohomology
of the twist on projective space over every ring vanishes.** -/
public theorem isZero_rightDerivedPlus_pushforward_twist_of_poly (n : ℕ)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) (d : ℤ) (q : ℕ)
    (h : ∀ R : CommRingCat.{u}, IsZero (Hgroup (AlgebraicGeometry.Proj
        (Stacks.ProjectiveCohomology.polyGrading R n)).ringCatSheaf ⊤ q
      (twistingSheaf (Stacks.ProjectiveCohomology.polyGrading R n) d))) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (q : ℤ)).obj (D.algebra.piece d)) :=
  Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
    _ _ q (ProjectiveBundleVanishing.isBasis_trivializing E hfree) fun _ hV =>
      isZero_Hgroup_preimage_twist_of_poly E hqc D hV.1 hV.2.some d q h

/-- **[Stacks, Tag 01XX], the vanishing clause.** Let `E` be an `𝒪_S`-module which is finite
locally free of constant rank `n + 1`, and `π : 𝐏(E) ⟶ S` its projective bundle. Then
`Rᵠ π_* 𝒪_{𝐏(E)}(d) = 0` for every integer `d` and every integer `q` with `q ≠ 0` and `q ≠ n`. -/
public theorem isZero_rightDerivedPlus_pushforward_twist_of_ne (n : ℕ)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
    (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) (d : ℤ) (q : ℤ)
    (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      q).obj (D.algebra.piece d)) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q hq _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = (p : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq).symm⟩
    exact isZero_rightDerivedPlus_pushforward_twist_of_poly E hqc n hfree D d p fun R =>
      ProjectiveSpaceHigherDirectImage.MiddleVanishing.isZero_Hgroup_twistingSheaf_of_isZero
        R n d p (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology R n d p (by
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact hq0 (by exact_mod_cast h)
          · exact hqn (by exact_mod_cast h)))

end Vanishing

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
