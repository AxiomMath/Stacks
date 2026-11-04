module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf

/-!
# Inverse image of the sheaves of representations: the dictionary

The sheaves `ℱ_ρ` of continuous representations are built with the canonical equivalence of
Tag 0DV5 (2) (`Stacks.EtaleCohomology.canonicalFiniteLocallyConstantAbelianSheafEquivalence`),
while the compatibility of that equivalence with inverse image (Tag 0DV6) is stated for
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence`. The two are assembled from the
same pieces, so their functors and inverse functors agree on the nose, and Tag 0DV6 gives, for
`f : Y ⟶ X` of connected schemes, a natural isomorphism `f⁻¹ ∘ E_X⁻¹ ≅ E_Y⁻¹ ∘ res_{f_*}` on the
inverse functors, which is what the levels of `ℱ_ρ` are made of: the inverse image of the level
sheaves of `ℱ_ρ` are those of `ℱ_{ρ ∘ f_*}`.

## Main results

* `canonicalFiniteLocallyConstantAbelianSheafEquivalence_functor`, `..._inverse`: the canonical
  and the chosen equivalences have the same functors.
* `nonempty_canonicalFiniteLocallyConstantAbelianSheafEquivalence_pullbackIso`: Tag 0DV6 for the
  canonical equivalence.
* `nonempty_pullback_inverse_iso`: the conjugate isomorphism `E_X⁻¹ ⋙ f⁻¹ ≅ res_{f_*} ⋙ E_Y⁻¹` on
  the inverse functors.
* `exists_pullback_representationLevelAbelian_iso`: the underlying abelian level sheaves of
  `f⁻¹ℱ_ρ` are those of `ℱ_{ρ ∘ f_*}`, compatibly with the reduction maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1]

/-- The canonical equivalence of Tag 0DV5 (2) has the functor of the chosen one. -/
public theorem canonicalFiniteLocallyConstantAbelianSheafEquivalence_functor
    (x : GeometricPoint X.1) :
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor =
      (finiteLocallyConstantAbelianSheafEquivalence B X x).functor :=
  rfl

/-- The canonical equivalence of Tag 0DV5 (2) has the inverse functor of the chosen one. -/
public theorem canonicalFiniteLocallyConstantAbelianSheafEquivalence_inverse
    (x : GeometricPoint X.1) :
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse =
      (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse :=
  rfl

/-- **Tag 0DV6 for the canonical equivalence**: on finite locally constant abelian sheaves, the
canonical equivalence commutes with inverse image, the action being restricted along
`π₁(Y, ȳ) → π₁(X, f(ȳ))`. -/
public theorem nonempty_canonicalFiniteLocallyConstantAbelianSheafEquivalence_pullbackIso
    (y : GeometricPoint Y.1) :
    Nonempty ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).functor ⋙
        ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y) ≅
      finiteLocallyConstantAbelianSheafPullback B f ⋙
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).functor) :=
  nonempty_finiteLocallyConstantAbelianSheafEquivalence_pullbackIso B f y

/-- **The conjugate of Tag 0DV6 on inverse functors**: `f⁻¹ (E_X⁻¹ M) ≅ E_Y⁻¹ (res M)`, naturally
in the finite `π₁(X, f(ȳ))`-module `M`. -/
public theorem nonempty_pullback_inverse_iso (y : GeometricPoint Y.1) :
    Nonempty ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse ⋙
        finiteLocallyConstantAbelianSheafPullback B f ≅
      ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y) ⋙
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse) := by
  obtain ⟨α⟩ := nonempty_canonicalFiniteLocallyConstantAbelianSheafEquivalence_pullbackIso B f y
  set EX := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)
  set EY := canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y
  exact ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ EY.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _ α.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight EX.counitIso _ ≪≫
      Functor.leftUnitor _) _⟩

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- Restricting the level module of `ρ` along `φ` gives the level module of `ρ ∘ φ`. -/
public theorem resIsFinite_levelAbelian (y : GeometricPoint Y.1)
    (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (k : ℕ) :
    (ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y)).obj
        (levelAbelian ρ hρ k) =
      levelAbelian (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
        (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k :=
  rfl

/-- **The levels of `f⁻¹ℱ_ρ` are those of `ℱ_{ρ ∘ f_*}`, compatibly with reduction**: on the
underlying finite locally constant abelian sheaves, there are isomorphisms
`f⁻¹ E_X⁻¹((ℤ/ℓ^k)^r_ρ) ≅ E_Y⁻¹((ℤ/ℓ^k)^r_{ρ ∘ f_*})` intertwining the reduction maps. -/
public theorem exists_pullback_representationLevelAbelian_iso (y : GeometricPoint Y.1)
    (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) :
    ∃ γ : ∀ k, (finiteLocallyConstantAbelianSheafPullback B f).obj
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.obj
          (levelAbelian ρ hρ k)) ≅
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse.obj
          (levelAbelian (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
            (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k),
      ∀ k, (finiteLocallyConstantAbelianSheafPullback B f).map
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.map
            (levelAbelianReduction ρ hρ k)) ≫ (γ k).hom =
        (γ (k + 1)).hom ≫ (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse.map
          (levelAbelianReduction (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
            (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k) := by
  obtain ⟨β⟩ := nonempty_pullback_inverse_iso B f y
  exact ⟨fun k => β.app (levelAbelian ρ hρ k), fun k => β.hom.naturality _⟩

end Stacks.EtaleCohomology
