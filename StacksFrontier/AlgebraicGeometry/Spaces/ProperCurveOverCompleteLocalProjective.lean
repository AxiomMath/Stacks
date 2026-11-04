module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# A proper algebraic space of fibre dimension one over a complete local ring is projective

Let `(A, 𝔪, κ)` be a complete Noetherian local ring and `X` an algebraic space proper over
`Spec A` with `dim X_κ ≤ 1`. Stacks 0AE7 says that `X` is a scheme, projective over `A`.

The source's proof: the adic fibres `X_n = X ×_{Spec A} Spec(A/𝔪ⁿ)` form a cartesian tower whose
bottom member `X_κ` is proper of dimension at most one, so Stacks 0E7R algebraizes it by a
projective scheme `Y ⟶ Spec A` with `X_n ≅ Y_n` compatibly; Grothendieck's algebraization theorem
for morphisms, Stacks 0A4Z, applied in both directions then gives `X ≅ Y`. That argument is
`AlgebraicGeometry.Space.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one`,
which takes the statement of Stacks 0A4Z (existence and uniqueness of the algebraization of a
compatible system of morphisms of adic fibres) as its hypothesis `halg`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one`:
  Stacks 0AE7, from the statement of Stacks 0A4Z.

## Implementation notes

Stacks 0A4Z is proved in the source from Grothendieck's existence theorem, Stacks 08BE, and
from Zariski's main theorem, Stacks 082K; this module records no tag. Stacks 0AE7 follows from
Stacks 0A4Z by applying the theorem below to it.

The fibre `X_κ` is the adic fibre of index `0` along `𝔪`, the library's adic fibres being
indexed from `0` with index `n` the quotient by `𝔪 ^ (n + 1)`.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AE7, from Stacks 0A4Z.** Let `(A, 𝔪, κ)` be a complete Noetherian local ring and
`fX : X ⟶ Spec A` a proper morphism of algebraic spaces with `dim X_κ ≤ 1`. Then `X` is a
scheme projective over `A`: there are a projective morphism of schemes `fY : Y ⟶ Spec A` and an
isomorphism of `X` with the algebraic space `Y` over `Spec A`.

The hypothesis `halg` is the statement of Stacks 0A4Z for the ideal `𝔪`: a compatible system of
morphisms between the adic fibres of a proper and of a separated finite type space over `Spec A`
is the system of adic fibres of exactly one morphism. -/
theorem exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))
    (halg : ∀ {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B (Spec (.of A)) hS X → IsAlgebraicSpace B (Spec (.of A)) hS Y →
      ∀ (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS)),
      IsProper B (Spec (.of A)) hS fX → IsSeparated B (Spec (.of A)) hS fY →
      IsFiniteType B (Spec (.of A)) hS fY →
      ∀ (g : ∀ n, adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ⟶
          adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n),
      (∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n)) =
        pullback.snd fX (yoneda.map (adicThickeningMap A (maximalIdeal A) B hS
          (contains_adicThickening A _ B hS) n))) →
      (∀ n, adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX n ≫
          g (n + 1) =
        g n ≫ adicFibreSucc A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fY n) →
      ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n,
        adicFibreMap A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) φ hφ n = g n)
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (hproper : IsProper B (Spec (.of A)) hS fX)
    (hdim : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) ≤ 1) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)),
      IsProjective fY ∧ IsProjectiveMorphism fY ∧
      ∃ e : X ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY),
        e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = fX := by
  set I := maximalIdeal A
  set hSn := contains_adicThickening A I B hS
  have hyo := isAlgebraicSpace_yoneda B (Spec (.of A)) hS
  have hbase := hyo (baseObject A B hS)
  -- the tower of adic fibres of `X` satisfies the hypotheses of Stacks 0E7R
  have hT := fun n => isAlgebraicSpace_adicFibre A I B hS hSn hX fX n
  have hpb := isAlgebraicSpace_pullback B (Spec (.of A)) hS
    (yoneda.map (adicThickeningMap A I B hS hSn 0)) fX
    (hyo _) hX hbase
  have hp0 : IsProper B (Spec (.of A)) hS
      (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn 0))) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact isProper_comp B (Spec (.of A)) hS (hT 0) hpb
      (hyo _) _ _
      (isProper_of_isClosedImmersion B (Spec (.of A)) hS (hT 0) hpb _
        (isClosedImmersion_of_isIso B (Spec (.of A)) hS _))
      (isProper_pullback_fst B (Spec (.of A)) hS hX hbase
        (hyo _) fX _ hproper)
  obtain ⟨Y, hY, fY, hfY, hfY', k, hk, hkpb⟩ :=
    exists_isProjective_algebraization_of_dimension_le_one A B hS
      (fun n => adicFibre A I B hS hSn fX n) hT
      (fun n => pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (fun n => adicFibreSucc A I B hS hSn fX n)
      (fun n => isPullback_adicFibreSucc A I B hS hSn fX n) hp0 hdim
  -- the algebraization `Y`, as an algebraic space over `Spec A`
  set fYs := yoneda.map (siteObjectToBase A B hS hY fY)
  have hYs := hyo (siteObject B (Spec (.of A)) hS hY fY)
  have hfYsp : IsProper B (Spec (.of A)) hS fYs :=
    isProper_yoneda_map B (Spec (.of A)) hS _ hfY.isProper
  -- the identifications `X_n ≅ Y_n` of Stacks 0E7R, as a compatible system
  set g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fYs n :=
    fun n => (hkpb n).isoPullback.hom
  have hgs : ∀ n, g n ≫ pullback.snd fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => (hkpb n).isoPullback_hom_snd
  have hgf : ∀ n, g n ≫ pullback.fst fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) = k n :=
    fun n => (hkpb n).isoPullback_hom_fst
  have hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fYs n := by
    intro n
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, hk, Category.assoc, adicFibreSucc_fst, hgf]
    · rw [Category.assoc, hgs, adicFibreSucc_snd, Category.assoc, adicFibreSucc_snd,
        ← Category.assoc, hgs]
  have hgs' : ∀ n, inv (g n) ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) := fun n => by
    rw [IsIso.inv_comp_eq, hgs]
  have hgc' : ∀ n, adicFibreSucc A I B hS hSn fYs n ≫ inv (g (n + 1)) =
      inv (g n) ≫ adicFibreSucc A I B hS hSn fX n := fun n => by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hgc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  -- Stacks 0A4Z in both directions
  obtain ⟨φ, ⟨hφ, hφn⟩, -⟩ := halg hX hYs fX fYs hproper hfYsp.isSeparated hfYsp.isFiniteType
    g hgs hgc
  obtain ⟨ψ, ⟨hψ, hψn⟩, -⟩ := halg hYs hX fYs fX hfYsp hproper.isSeparated
    hproper.isFiniteType (fun n => inv (g n)) hgs' hgc'
  -- an endomorphism over `Spec A` inducing the identity on all adic fibres is the identity
  have hid : ∀ {P} (hP : IsAlgebraicSpace B _ hS P) fP (hfP : IsProper B _ hS fP)
      (e : P ⟶ P) (he : e ≫ fP = fP), (∀ n, adicFibreMap A I B hS hSn e he n = 𝟙 _) → e = 𝟙 P :=
    fun hP fP hfP e he hen => by
    obtain ⟨_, _, huniq⟩ := halg hP hP fP fP hfP hfP.isSeparated hfP.isFiniteType
      (fun n => 𝟙 _) (fun n => Category.id_comp _) (fun n => by simp)
    exact (huniq _ ⟨he, hen⟩).trans
      (huniq _ ⟨Category.id_comp fP, fun n => adicFibreMap_id A I B hS hSn fP n⟩).symm
  have hφψ : φ ≫ ψ = 𝟙 X := hid hX fX hproper _ (by rw [Category.assoc, hψ, hφ]) fun n => by
    rw [adicFibreMap_comp A I B hS hSn φ hφ ψ hψ n, hφn, hψn, IsIso.hom_inv_id]
  have hψφ : ψ ≫ φ = 𝟙 _ := hid hYs fYs hfYsp _ (by rw [Category.assoc, hφ, hψ]) fun n => by
    rw [adicFibreMap_comp A I B hS hSn ψ hψ φ hφ n, hψn, hφn, IsIso.inv_hom_id]
  exact ⟨Y, hY, fY, hfY, hfY', ⟨φ, ψ, hφψ, hψφ⟩, hφ⟩

end AlgebraicGeometry.Space

end
