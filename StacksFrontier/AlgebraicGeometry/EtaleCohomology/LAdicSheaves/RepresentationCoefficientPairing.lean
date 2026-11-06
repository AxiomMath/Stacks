module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModulesPairing
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDesc

/-!
# The pairing of coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ`

Let `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous. At level `k` the evaluation pairing
`⟨x, y⟩ = Σ xᵢ yᵢ` of `(ℤ/ℓ^kℤ)^r` with the action of `ρ` and `(ℤ/ℓ^kℤ)^r` with the action of the
contragredient `ρ^∨` is invariant
(`Stacks.EtaleCohomology.levelRepresentation_dotProduct_contragredient`), so the canonical
equivalence of Tag 0DV5 (2) carries it to a pairing of the level sheaves
`ℱ_{ρ,k} × ℱ_{ρ^∨,k} → ℤ/ℓ^kℤ`, bilinear on sections and compatible with restriction.

## Main definitions

* `Stacks.EtaleCohomology.levelEvaluation`: the evaluation pairing of the level modules.
* `Stacks.EtaleCohomology.representationLevelPairing`: the pairing of the level sheaves, on
  sections; `Stacks.EtaleCohomology.representationLevelBilinear` is the same map as a
  `ℤ/ℓ^kℤ`-bilinear map.
* `Stacks.EtaleCohomology.representationLevelTensorPairing`: the pairing as a morphism of sheaves
  `ℱ_{ρ,k} ⊗ ℱ_{ρ^∨,k} ⟶ ℤ/ℓ^kℤ` out of the tensor product of sheaves of `ℤ/ℓ^kℤ`-modules.

## Main results

* `Stacks.EtaleCohomology.levelEvaluation_equivariant`: the evaluation pairing is invariant.
* `Stacks.EtaleCohomology.representationLevelPairing_naturality`: the pairing of sections
  commutes with restriction.

## Implementation notes

The target is the level sheaf of the trivial representation of rank one, `E⁻¹(ℤ/ℓ^kℤ)` for the
equivalence `E` of Tag 0DV5 (2), rather than the constant sheaf: the general construction
`Stacks.ConstantSheaf.finiteLocallyConstantPairing` takes any finite discrete `π₁`-module as
target.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Matrix

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

section Abelian

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- The trivial representation of rank one, whose level modules are `ℤ/ℓ^kℤ` with trivial
action. -/
abbrev trivialRepresentation : G →* GL (Fin 1) ℤ_[ℓ] := 1

/-- **The evaluation pairing at level `k`**: `⟨x, y⟩ = Σ xᵢ yᵢ` between `(ℤ/ℓ^kℤ)^r` with the
action of `ρ` and `(ℤ/ℓ^kℤ)^r` with the action of `ρ^∨`, valued in the trivial module
`ℤ/ℓ^kℤ = (ℤ/ℓ^kℤ)^1`. -/
def levelEvaluation (k : ℕ) :
    (levelAbelian ρ hρ k).obj.obj.obj.V →+
      (levelAbelian (contragredient ρ) (continuous_contragredient hρ) k).obj.obj.obj.V →+
        (levelAbelian (trivialRepresentation (G := G) (ℓ := ℓ)) continuous_const
          k).obj.obj.obj.V :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => ULift.up fun _ => x.down ⬝ᵥ y.down)
    (fun y y' => ULift.ext (funext fun _ => dotProduct_add x.down y.down y'.down)))
    (fun x x' => AddMonoidHom.ext fun y =>
      ULift.ext (funext fun _ => add_dotProduct x.down x'.down y.down))

/-- The action of `g` on the level module is the level representation of `ρ`. -/
theorem levelAbelian_ρ_apply (k : ℕ) (g : G) (a : (levelAbelian ρ hρ k).obj.obj.obj.V) :
    ((levelAbelian ρ hρ k).obj.obj.obj.ρ g).asHom.hom a =
      ULift.up (levelRepresentation ρ k g a.down) :=
  rfl

/-- **The evaluation pairing is invariant**: `⟨ρ(g) a, ρ^∨(g) b⟩ = ⟨a, b⟩`, and `g` acts trivially
on the target. -/
theorem levelEvaluation_equivariant (k : ℕ) (g : G)
    (a : (levelAbelian ρ hρ k).obj.obj.obj.V)
    (b : (levelAbelian (contragredient ρ) (continuous_contragredient hρ) k).obj.obj.obj.V) :
    levelEvaluation ρ hρ k (((levelAbelian ρ hρ k).obj.obj.obj.ρ g).asHom.hom a)
        (((levelAbelian (contragredient ρ) (continuous_contragredient hρ) k).obj.obj.obj.ρ
          g).asHom.hom b) =
      ((levelAbelian (trivialRepresentation (G := G) (ℓ := ℓ)) continuous_const k).obj.obj.obj.ρ
        g).asHom.hom (levelEvaluation ρ hρ k a b) := by
  refine ULift.ext (funext fun _ => ?_)
  show levelRepresentation ρ k g a.down ⬝ᵥ levelRepresentation (contragredient ρ) k g b.down =
    levelRepresentation (trivialRepresentation (G := G) (ℓ := ℓ)) k g (fun _ => a.down ⬝ᵥ b.down) _
  rw [levelRepresentation_dotProduct_contragredient, levelRepresentation_apply]
  simp

end Abelian

section Sheaves

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- **The pairing of coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` at level `k`**, on sections over `U`:
the evaluation pairing `⟨x, y⟩ = Σ xᵢ yᵢ`, invariant under `π₁(X, x̄)`, carried to the finite
locally constant sheaves by the canonical equivalence of Tag 0DV5 (2). The target is the level
sheaf of the trivial representation of rank one. -/
def representationLevelPairing (k : ℕ) (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    (representationLevelAbelian B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ k).obj.obj U →+
      (representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
          (continuous_contragredient hρ) k).obj.obj U →+
        (representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (trivialRepresentation (ℓ := ℓ)) continuous_const k).obj.obj U :=
  Stacks.ConstantSheaf.finiteLocallyConstantPairing (SmallEtale.topology B X.1 X.2)
    (canonicalFiniteLocallyConstantSetsEquivalence B X x) _ _ _ (levelEvaluation ρ hρ k)
    (levelEvaluation_equivariant ρ hρ k) U

/-- The pairing of coefficients commutes with restriction. -/
theorem representationLevelPairing_naturality (k : ℕ) {U V : (SmallEtale B X.1 X.2)ᵒᵖ}
    (f : U ⟶ V)
    (a : (representationLevelAbelian B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.obj U)
    (b : (representationLevelAbelian B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
        (continuous_contragredient hρ) k).obj.obj U) :
    (representationLevelAbelian B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (trivialRepresentation (ℓ := ℓ)) continuous_const k).obj.map f
        (representationLevelPairing B X x ρ hρ k U a b) =
      representationLevelPairing B X x ρ hρ k V
        ((representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.map f a)
        ((representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
            (continuous_contragredient hρ) k).obj.map f b) :=
  Stacks.ConstantSheaf.finiteLocallyConstantPairing_naturality _ _ _ _ _ _ _ f a b

/-- **The pairing of coefficients is `ℤ/ℓ^kℤ`-bilinear** on the sections of the level sheaves of
`ℤ/ℓ^kℤ`-modules. -/
def representationLevelBilinear (k : ℕ) (U : (SmallEtale B X.1 X.2)ᵒᵖ) :
    (representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ k).obj.obj U →ₗ[ZMod (ℓ ^ k)]
      (representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (contragredient ρ) (continuous_contragredient hρ) k).obj.obj U →ₗ[ZMod (ℓ ^ k)]
        (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (trivialRepresentation (ℓ := ℓ)) continuous_const k).obj.obj U :=
  let p : (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.obj U →+
      (representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (contragredient ρ) (continuous_contragredient hρ) k).obj.obj U →+
        (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (trivialRepresentation (ℓ := ℓ)) continuous_const k).obj.obj U :=
    representationLevelPairing B X x ρ hρ k U
  LinearMap.mk₂ (ZMod (ℓ ^ k)) (fun a b => p a b)
    (fun a a' b => by rw [map_add, AddMonoidHom.add_apply])
    (fun c a b => by
      rw [← AddMonoidHom.flip_apply]
      exact (AddMonoidHom.toZModLinearMap (ℓ ^ k) (p.flip b)).map_smul c a)
    (fun a b b' => map_add _ b b')
    (fun c a b => (AddMonoidHom.toZModLinearMap (ℓ ^ k) (p a)).map_smul c b)

/-- The pairing of coefficients commutes with restriction, as a bilinear map. -/
theorem representationLevelBilinear_naturality (k : ℕ) {U V : (SmallEtale B X.1 X.2)ᵒᵖ}
    (f : U ⟶ V)
    (a : (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.obj U)
    (b : (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
        (continuous_contragredient hρ) k).obj.obj U) :
    (representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (trivialRepresentation (ℓ := ℓ)) continuous_const k).obj.map f
        (representationLevelBilinear B X x ρ hρ k U a b) =
      representationLevelBilinear B X x ρ hρ k V
        ((representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj.map f a)
        ((representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ)
            (continuous_contragredient hρ) k).obj.map f b) :=
  representationLevelPairing_naturality B X x ρ hρ k f a b

attribute [local instance] Sheaf.monoidalCategory

/-- The morphisms of presheaves of `ℤ/ℓ^kℤ`-modules on the small étale site inverted by
sheafification form a monoidal class, for the large-universe tensor product. -/
instance isMonoidal_W_smallEtale_zmodPow (k : ℕ) : ((SmallEtale.topology B X.1 X.2).W
    (A := ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).IsMonoidal :=
  ModuleCat.isMonoidal_W_lifted.{u + 1} (ZMod (ℓ ^ k)) _

/-- **The pairing of coefficients `ℱ_{ρ,k} ⊗ ℱ_{ρ^∨,k} ⟶ ℤ/ℓ^kℤ` as a morphism of sheaves** of
`ℤ/ℓ^kℤ`-modules on the small étale site, out of the tensor product of sheaves, induced by the
bilinear pairing of sections `Stacks.EtaleCohomology.representationLevelBilinear`. -/
def representationLevelTensorPairing (k : ℕ) :
    representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ k ⊗
      representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (contragredient ρ) (continuous_contragredient hρ) k ⟶
      representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (trivialRepresentation (ℓ := ℓ)) continuous_const k :=
  Sheaf.tensorDesc (representationLevelBilinear B X x ρ hρ k)
    (fun f a b => representationLevelBilinear_naturality B X x ρ hρ k f a b)

end Sheaves

end Stacks.EtaleCohomology
