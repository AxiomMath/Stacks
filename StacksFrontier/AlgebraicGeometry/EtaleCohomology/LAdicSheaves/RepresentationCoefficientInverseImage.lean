module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.CharacterSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# The inverse image of the `O`-sheaf of a representation

For an action `μ : O → M_r(ℤ_ℓ)` of a finite `ℤ_ℓ`-algebra commuting with `ρ`, the `O`-sheaf
`Stacks.EtaleCohomology.representationCoefficientSheaf` has `O` acting through the morphisms of
the intertwiners `μ(o)`. The isomorphism `f⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ f_*}` is natural in intertwiners
(`Stacks.EtaleCohomology.representationLAdicSheafInverseImageHom_naturality`), so it commutes with
the actions of `O`: it is an isomorphism of `O`-sheaves between the inverse image
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.inverseImage`) of the `O`-sheaf of `ρ` and
the `O`-sheaf of `ρ ∘ f_*`. With `μ` the scalar matrices of a basis this applies to
`Stacks.EtaleCohomology.coefficientRepresentationSheaf`, hence to the twists `ℱ_ρ ⊗ L_ψ(g)`.

## Main results

* `Stacks.EtaleCohomology.representationLAdicSheafInverseImageIso_hom_act`: the isomorphism
  commutes with the actions of `O`.
* `Stacks.EtaleCohomology.restrictScalarsRepresentation_comp`,
  `Stacks.EtaleCohomology.characterTwist_comp`: restriction of scalars and twisting by a
  character commute with composition by the map of fundamental groups.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [IsNoetherian X.1] [IsNoetherian Y.1]
  (y : GeometricPoint Y.1)
  (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (μ : O →+* Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (hμ : ∀ o g, μ o * (ρ g).val = (ρ g).val * μ o)

attribute [local instance] hasWeakSheafify_smallEtale_levels

/-- **The isomorphism `f⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ f_*}` commutes with the actions of `O`**: it is an
isomorphism of `O`-sheaves from the inverse image of the `O`-sheaf of `ρ` to the `O`-sheaf of
`ρ ∘ f_*`. -/
public theorem representationLAdicSheafInverseImageIso_hom_act (o : O) :
    (representationLAdicSheafInverseImageIso B f y ρ hρ).hom ≫
        ((representationCoefficientSheaf B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) μ (fun o _ => hμ o _)).act o).asHom =
      ((LAdicSheaf.CoefficientSheaf.inverseImage f
          (representationCoefficientSheaf B X (y.map f.hom) ρ hρ μ hμ)).act o).asHom ≫
        (representationLAdicSheafInverseImageIso B f y ρ hρ).hom :=
  representationLAdicSheafInverseImageHom_naturality B f y _ ρ hρ hρ (μ o) (hμ o)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [AlgebraicGeometry.IsNoetherian X.1] [AlgebraicGeometry.IsNoetherian Y.1] in
/-- Restriction of scalars of representations commutes with composition by the map of
fundamental groups. -/
public theorem restrictScalarsRepresentation_comp {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
    (σ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) O) :
    restrictScalarsRepresentation B Y y b (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) =
      (restrictScalarsRepresentation B X (y.map f.hom) b σ).comp
        (etaleFundamentalGroupMap f.hom y).toMonoidHom :=
  rfl

/-- The twist by a character commutes with composition by a group homomorphism. -/
public theorem characterTwist_comp {G H : Type*} [Group G] [Group H] {n : Type*} [Fintype n]
    [DecidableEq n] (σ : H →* GL n O) (χ : H →* Oˣ) (φ : G →* H) :
    characterTwist (σ.comp φ) (χ.comp φ) = (characterTwist σ χ).comp φ :=
  rfl

end Stacks.EtaleCohomology
