module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FamilyCechAmitsur

/-!
# The first Čech cohomology of a covering family whose sections are base changes

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FamilyCechAmitsur` transports
degree-one exactness of the Amitsur complex of a faithfully flat algebra to the vanishing of the
first Čech cohomology of a covering family, taking the identification of the Čech terms with the
terms of the Amitsur complex as data;
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition`
produces that data from the base-change comparisons of the sections at the members, the double
overlaps and the triple overlaps.  This file is the composite, and it is the shape in which the
geometric side consumes the whole chain: nothing in its statement mentions the Amitsur complex.

The algebra of the descent is the product `∀ i, Bᵢ` of the coefficient rings of the members, whose
faithful flatness over the coefficient ring of the base is the one flatness hypothesis; the rings
of the double and the triple overlaps are tensor products, with their two structure maps given
explicitly rather than as instances, so that the diagonal of the family does not collide.

## Main results

* `PresheafOfModules.exists_familyCechDiff₀_eq_of_baseChange`: **a degree-one Čech cocycle of a
  covering family whose sections are computed by base change is a Čech coboundary**, the vanishing
  of the first Čech cohomology of the family.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe y z v u

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{z}}

/-- **A degree-one Čech cocycle of a covering family whose sections are computed by base change is
a Čech coboundary**: the vanishing of the first Čech cohomology of the family.

Every hypothesis but two is that of `PresheafOfModules.exists_familyBaseChange`, which turns the
base-change comparisons at the members, the double overlaps and the triple overlaps into the
pairwise and triple comparisons and the five slot equations.  The two further ones are finiteness
of the index type, which is what makes the product of the coefficient rings base change a module
into the product of its base changes, and faithful flatness of that product, which is where the
exactness of the Amitsur complex comes from.  `PresheafOfModules.exists_amitsurDiff₁_data`
assembles the comparisons into the degree-one Amitsur data and
`PresheafOfModules.exists_familyCechDiff₀_eq` concludes.

No object is affine, no ring is a ring of functions and no topology occurs: the covering property
of the family enters only through the faithful flatness of the product. -/
theorem exists_familyCechDiff₀_eq_of_baseChange {N : PresheafOfModules.{y} R} {T : C}
    {ιi : Type*} [Finite ιi] {Y : ιi → C} {Pb : ιi → ιi → C} {Pb₃ : ιi → ιi → ιi → C}
    (g : ∀ i, Y i ⟶ T)
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
    (A : Type*) [CommRing A] [Module A (N.obj (op T))]
    (Bi : ιi → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    [Module.FaithfullyFlat A (∀ i, Bi i)]
    (D : ιi → ιi → Type*) [∀ i j, CommRing (D i j)] [∀ i j, Algebra A (D i j)]
    (E : ιi → ιi → ιi → Type*) [∀ i j k, CommRing (E i j k)]
    [∀ i j k, Algebra A (E i j k)]
    [∀ i, Module (Bi i) (N.obj (op (Y i)))] [∀ i j, Module (D i j) (N.obj (op (Pb i j)))]
    [∀ i j k, Module (E i j k) (N.obj (op (Pb₃ i j k)))]
    (e : ∀ i, Bi i ⊗[A] N.obj (op T) ≃ₗ[Bi i] N.obj (op (Y i)))
    (he : ∀ (i) (n : N.obj (op T)),
      e i ((1 : Bi i) ⊗ₜ[A] n) = N.restrictₛₗ (g i).op n)
    (eD : ∀ i j, D i j ⊗[A] N.obj (op T) ≃ₗ[D i j] N.obj (op (Pb i j)))
    (heD : ∀ (i j) (n : N.obj (op T)),
      eD i j ((1 : D i j) ⊗ₜ[A] n) = N.restrictₛₗ (pr₁ i j ≫ g i).op n)
    (eE : ∀ i j k, E i j k ⊗[A] N.obj (op T) ≃ₗ[E i j k] N.obj (op (Pb₃ i j k)))
    (heE : ∀ (i j k) (n : N.obj (op T)), eE i j k ((1 : E i j k) ⊗ₜ[A] n) =
      N.restrictₛₗ (s₁ i j k ≫ pr₁ j k ≫ g j).op n)
    (u : ∀ i j, Bi i →ₐ[A] D i j) (v : ∀ i j, Bi j →ₐ[A] D i j)
    (ψ : ∀ i j, Bi i ⊗[A] Bi j ≃+* D i j)
    (hψ : ∀ (i j) (b : Bi i) (c : Bi j), ψ i j (b ⊗ₜ[A] c) = u i j b * v i j c)
    (u₃ : ∀ i j k, Bi i →ₐ[A] E i j k) (v₃ : ∀ i j k, D j k →ₐ[A] E i j k)
    (ψ₃ : ∀ i j k, Bi i ⊗[A] D j k ≃+* E i j k)
    (hψ₃ : ∀ (i j k) (b : Bi i) (d : D j k),
      ψ₃ i j k (b ⊗ₜ[A] d) = u₃ i j k b * v₃ i j k d)
    (σ₂ : ∀ i j k, D i k →+* E i j k) (σ₃ : ∀ i j k, D i j →+* E i j k)
    (hw : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j)
    (hw₂ : ∀ i j k, s₂ i j k ≫ pr₁ i k ≫ g i = s₁ i j k ≫ pr₁ j k ≫ g j)
    (hw₃ : ∀ i j k, s₃ i j k ≫ pr₁ i j ≫ g i = s₁ i j k ≫ pr₁ j k ≫ g j)
    (hsm₁ : ∀ (i j) (b : Bi i) (x : N.obj (op (Y i))),
      N.restrictₛₗ (pr₁ i j).op (b • x) = u i j b • N.restrictₛₗ (pr₁ i j).op x)
    (hsm₂ : ∀ (i j) (b : Bi j) (x : N.obj (op (Y j))),
      N.restrictₛₗ (pr₂ i j).op (b • x) = v i j b • N.restrictₛₗ (pr₂ i j).op x)
    (hsmt₁ : ∀ (i j k) (d : D j k) (x : N.obj (op (Pb j k))),
      N.restrictₛₗ (s₁ i j k).op (d • x) = v₃ i j k d • N.restrictₛₗ (s₁ i j k).op x)
    (hsmt₂ : ∀ (i j k) (d : D i k) (x : N.obj (op (Pb i k))),
      N.restrictₛₗ (s₂ i j k).op (d • x) = σ₂ i j k d • N.restrictₛₗ (s₂ i j k).op x)
    (hsmt₃ : ∀ (i j k) (d : D i j) (x : N.obj (op (Pb i j))),
      N.restrictₛₗ (s₃ i j k).op (d • x) = σ₃ i j k d • N.restrictₛₗ (s₃ i j k).op x)
    (hσ₂u : ∀ (i j k) (b : Bi i), σ₂ i j k (u i k b) = u₃ i j k b)
    (hσ₂v : ∀ (i j k) (c : Bi k), σ₂ i j k (v i k c) = v₃ i j k (v j k c))
    (hσ₃u : ∀ (i j k) (b : Bi i), σ₃ i j k (u i j b) = u₃ i j k b)
    (hσ₃v : ∀ (i j k) (c : Bi j), σ₃ i j k (v i j c) = v₃ i j k (u j k c))
    {ζ : ∀ i j, N.obj (op (Pb i j))}
    (hζ : ∀ i j k, N.restrictₛₗ (s₁ i j k).op (ζ j k) -
      N.restrictₛₗ (s₂ i j k).op (ζ i k) + N.restrictₛₗ (s₃ i j k).op (ζ i j) = 0) :
    ∃ z : ∀ i, N.obj (op (Y i)), ∀ i j,
      N.restrictₛₗ (pr₁ i j).op (z i) - N.restrictₛₗ (pr₂ i j).op (z j) = ζ i j := by
  obtain ⟨f, f₃, hf₃, hnat₁, hnat₂, hs₁, hs₂, hs₃⟩ :=
    exists_familyBaseChange g pr₁ pr₂ s₁ s₂ s₃ A Bi D E e he eD heD eE heE u v ψ hψ u₃ v₃
      ψ₃ hψ₃ σ₂ σ₃ hw hw₂ hw₃ hsm₁ hsm₂ hsmt₁ hsmt₂ hsmt₃ hσ₂u hσ₂v hσ₃u hσ₃v
  obtain ⟨eW, eV, eV₃, -, -, heV, heV₃, hd₀, hd₁⟩ :=
    exists_amitsurDiff₁_data g pr₁ pr₂ s₁ s₂ s₃ A Bi (fun i => (e i).toAddEquiv) he f f₃
      hf₃ hnat₁ hnat₂ hs₁ hs₂ hs₃
  exact N.exists_familyCechDiff₀_eq pr₁ pr₂ s₁ s₂ s₃ A (∀ i, Bi i) (N.obj (op T)) eW eV eV₃
    heV heV₃ hd₀ hd₁ hζ

end PresheafOfModules

end
