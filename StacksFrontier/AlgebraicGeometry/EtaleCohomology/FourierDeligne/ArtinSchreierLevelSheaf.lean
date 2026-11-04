module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness

/-!
# The Artin–Schreier sheaf with coefficients in a finite ring

Let `Λ` be a finite commutative ring, `k` a finite field, `A` a `k`-algebra with `Spec A` connected
and `g ∈ A`, and `ψ : k → Λ` an additive character. The *Artin–Schreier sheaf* `L_ψ(g)` with
coefficients in `Λ` is the lisse sheaf of free `Λ`-modules of rank one on `Spec A` on which
`π₁(Spec A, x̄)` acts through the character `ψ(-χ)`, `χ` the character of the Artin–Schreier cover
`t^q - t = g` (`Stacks.ArtinSchreier.artinSchreierCharacter`). For `Λ = O/ℓⁿ⁺¹` it is the level `n`
of the `O`-sheaf `Stacks.ArtinSchreier.artinSchreierSheaf`, read as a sheaf of `O/ℓⁿ⁺¹`-modules;
this is the form in which it is the kernel of the Fourier transform at a finite level, the tensor
products being over `Λ`.

## Main definitions

* `Stacks.EtaleCohomology.characterContinuousModule`: `Λ` with `G` acting through a character with
  open kernel.
* `Stacks.ArtinSchreier.artinSchreierLevelSheaf`: `L_ψ(g)` with coefficients in `Λ`, on Mathlib's
  small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section Character

variable (Λ : Type) [CommRing Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The representation of `G` on `Λ` (lifted to `Type (u + 1)`) through a character
`χ : G →* Λˣ`: `g` acts as multiplication by `χ g`. -/
def characterRepresentationULift (χ : G →* Λˣ) : Representation Λ G (ULift.{u + 1} Λ) where
  toFun g := (χ g : Λ) • LinearMap.id
  map_one' := by
    ext x
    simp
  map_mul' g g' := by
    ext x
    simp [mul_smul, mul_left_comm]

/-- **`Λ` with `G` acting through a character `χ` with open kernel**, as a finite `Λ`-module with
continuous `G`-action. -/
def characterContinuousModule (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G)) :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G :=
  ⟨ofRepresentation (characterRepresentationULift Λ χ)
      ((isContinuous_actionOfRepresentation_iff _).2 fun x => by
        refine isOpen_iff_forall_mem_open.2 fun g hg =>
          ⟨(fun h => g⁻¹ * h) ⁻¹' (χ.ker : Set G), ?_, ?_, ?_⟩
        · intro h hh
          simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker] at hh
          simp only [Set.mem_setOf_eq] at hg ⊢
          have : χ h = χ g := by
            rw [show h = g * (g⁻¹ * h) by group, map_mul, hh, mul_one]
          change ((χ h : Λ) • x) = x
          rw [this]
          exact hg
        · exact hχ.preimage (continuous_const.mul continuous_id)
        · simp [MonoidHom.mem_ker]),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (ULift.moduleEquiv (R := Λ)).symm)⟩

/-- The action on `Stacks.EtaleCohomology.characterContinuousModule` is multiplication by the
character. -/
theorem characterContinuousModule_ρ_hom (χ : G →* Λˣ) (hχ : IsOpen (χ.ker : Set G)) (g : G)
    (x : ULift.{u + 1} Λ) :
    (((characterContinuousModule Λ χ hχ).obj.obj.obj.ρ g).hom x : ULift.{u + 1} Λ) =
      (χ g : Λ) • x :=
  rfl

end Character

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)

/-- The kernel of the Artin–Schreier character is open: it contains the kernel of the character
of the cover, which is continuous for the discrete topology on `k`. -/
theorem isOpen_ker_artinSchreierCharacter (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    IsOpen ((artinSchreierCharacter k A g ψ x p₀).ker : Set (EtaleFundamentalGroup _ x)) := by
  let : TopologicalSpace (Multiplicative k) := ⊥
  have : DiscreteTopology (Multiplicative k) := ⟨rfl⟩
  have hc := (torsorCover k A g).continuous_character x p₀
  have : ((artinSchreierCharacter k A g ψ x p₀).ker : Set (EtaleFundamentalGroup _ x)) =
      (fun σ => ((torsorCover k A g).character x p₀ σ)) ⁻¹'
        {a | ψ.toMonoidHom.toHomUnits a⁻¹ = 1} := by
    ext σ
    simp [artinSchreierCharacter, MonoidHom.mem_ker]
  rw [this]
  exact (isOpen_discrete _).preimage hc

variable (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- **The Artin–Schreier sheaf `L_ψ(g)` with coefficients in the finite ring `Λ`**: the lisse sheaf
on `Spec A` of `Λ` with `π₁` acting through `ψ(-χ)`, read on Mathlib's small étale site. -/
def artinSchreierLevelSheaf (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) : EtaleModules.{u, 0} Λ (Spec (.of A)) :=
  (lisseEtaleSheaf B (specObject A B hX) x Λ).obj
    (characterContinuousModule Λ (artinSchreierCharacter k A g ψ x p₀)
      (isOpen_ker_artinSchreierCharacter k A g Λ ψ x p₀))

end Stacks.ArtinSchreier

end
