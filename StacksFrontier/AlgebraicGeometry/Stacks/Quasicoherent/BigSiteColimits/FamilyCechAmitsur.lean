module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur

/-!
# The Čech complex of a covering family in degree one, and the Amitsur complex

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur` identifies the
first two differentials of the Čech complex of a *one-element* covering `{h : W ⟶ U}` with the
first two differentials of the Amitsur complex, and transports the degree-one exactness of the
latter to the vanishing of the first Čech cohomology of `{h}`.  A covering sieve of an object does
not in general contain a single morphism out of a disjoint union of a covering family — a sieve is
closed under precomposition, not under coproducts — so the same transport is needed for a *family*
`{g i : Y i ⟶ T}`, whose Čech terms are the products of the sections over the members, over the
double overlaps `Pb i j` and over the triple overlaps `Pb₃ i j k`.

This file is that degree-one transport, and the descent of sections it feeds.  Both statements
take the identification of the Čech terms with the terms of the Amitsur complex of a single
algebra `A → Sa` as data, in the shape it comes in: `Sa` is the product of the rings of the
members, and `PresheafOfModules.exists_amitsurDiff₀_data` already produces the degree-zero half of
exactly this data from the member-wise base-change comparisons.  Nothing here assumes that the
family covers anything, that the objects are affine, or that `Sa` is a product.

The second statement is the family analogue of `SheafOfModules.detectsRange_of_cechH1Vanishing`,
and it is the shape in which the vanishing of the first cohomology of a quasi-coherent module on
an affine is consumed where no single covering morphism is available: the hypothesis is the
vanishing of the first Čech cohomology *of the kernel* of the morphism, phrased inside the source,
and the conclusion is `SheafOfModules.JointlyDetectsRange`, which
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` turns into surjectivity on the
sections over a terminal object.

## Main results

* `PresheafOfModules.exists_familyCechDiff₀_eq`: **the vanishing of the first Čech cohomology of a
  covering family**, from degree-one exactness of the Amitsur complex: a degree-one Čech cocycle
  of the family is the Čech coboundary of a family of sections over the members.
* `SheafOfModules.jointlyDetectsRange_of_familyCechH1Vanishing`: **a morphism whose kernel has
  vanishing first Čech cohomology along a covering family has its images jointly detected by that
  family.**

## Implementation notes

The three commutations `hc₁`, `hc₂` and `hc₃` between the projections of a triple overlap and
those of the double overlaps are exactly the ones
`CategoryTheory.IsPullback.exists_familyCechProjections` produces, and they are what makes a Čech
coboundary a cocycle at a family; at a one-element family they degenerate to the three equations
of `PresheafOfModules.cechDiff₁_cechDiff₀_apply`.

The Čech differentials are written out rather than packaged as additive maps between the product
modules.  `PresheafOfModules.cechDiff₀` and `PresheafOfModules.cechDiff₁` are differences of
restriction maps between the sections over two objects; at a family the sources and targets are
products indexed by pairs and by triples, and each component is a difference of restrictions along
arrows between *different* objects, so no single restriction map is being subtracted and the
element form is the statement.

No `@[stacks]` attribute is claimed.  Stacks 03DW is the comparison of the cohomology of a
quasi-coherent module computed in several topologies and in all degrees; what is here is one
transport of exactness, with the comparison of the terms taken as data.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe w u v r m

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}} (P : PresheafOfModules.{m} R)

/-- **The vanishing of the first Čech cohomology of a covering family**, from degree-one
exactness of the Amitsur complex of a faithfully flat algebra.

The identification of the Čech terms with the terms of the Amitsur complex of `M` along `A → Sa`
is the data `eW`, `eV` and `eV₃` together with the two equations `hd₀` and `hd₁` saying that the
Čech differentials of the family correspond to the Amitsur differentials; `eV` is required to be
surjective and `eV₃` injective, and nothing is asked of `eW`.  Under that identification a
degree-one cocycle `ζ` of the family — a family of sections over the double overlaps whose
alternating restriction to each triple overlap vanishes — is `eV` of a `1`-cocycle of the Amitsur
complex, hence of a coboundary, hence is the Čech coboundary of the family `eW x`.

This is the family analogue of `PresheafOfModules.exists_cechDiff₀_eq`, and the degree-one
companion of the degree-zero data of `PresheafOfModules.exists_amitsurDiff₀_data`. -/
theorem exists_familyCechDiff₀_eq {ι : Type w} {Y : ι → C} {Pb : ι → ι → C}
    {Pb₃ : ι → ι → ι → C} (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
    (A Sa : Type*) [CommRing A] [CommRing Sa] [Algebra A Sa] [Module.FaithfullyFlat A Sa]
    (M : Type*) [AddCommGroup M] [Module A M]
    (eW : Sa ⊗[A] M →+ (∀ i, P.obj (op (Y i))))
    (eV : Sa ⊗[A] (Sa ⊗[A] M) →+ (∀ i j, P.obj (op (Pb i j))))
    (eV₃ : Sa ⊗[A] (Sa ⊗[A] (Sa ⊗[A] M)) →+ (∀ i j k, P.obj (op (Pb₃ i j k))))
    (heV : Function.Surjective eV) (heV₃ : Function.Injective eV₃)
    (hd₀ : ∀ (x : Sa ⊗[A] M) (i j), eV (Module.Descent.amitsurDiff₀ A Sa M x) i j =
      P.restrictₛₗ (pr₁ i j).op (eW x i) - P.restrictₛₗ (pr₂ i j).op (eW x j))
    (hd₁ : ∀ (x : Sa ⊗[A] (Sa ⊗[A] M)) (i j k),
      eV₃ (Module.Descent.amitsurDiff₁ A Sa M x) i j k =
        P.restrictₛₗ (s₁ i j k).op (eV x j k) - P.restrictₛₗ (s₂ i j k).op (eV x i k) +
          P.restrictₛₗ (s₃ i j k).op (eV x i j))
    {ζ : ∀ i j, P.obj (op (Pb i j))}
    (hζ : ∀ i j k, P.restrictₛₗ (s₁ i j k).op (ζ j k) - P.restrictₛₗ (s₂ i j k).op (ζ i k) +
      P.restrictₛₗ (s₃ i j k).op (ζ i j) = 0) :
    ∃ z : ∀ i, P.obj (op (Y i)), ∀ i j,
      P.restrictₛₗ (pr₁ i j).op (z i) - P.restrictₛₗ (pr₂ i j).op (z j) = ζ i j := by
  obtain ⟨y, hy⟩ := heV ζ
  have hcocycle : ∀ i j k, eV₃ (Module.Descent.amitsurDiff₁ A Sa M y) i j k = 0 := by
    intro i j k
    rw [hd₁ y i j k, hy]
    exact hζ i j k
  have hy₁ : Module.Descent.amitsurDiff₁ A Sa M y = 0 := by
    refine heV₃ ?_
    rw [map_zero]
    exact funext fun i => funext fun j => funext fun k => hcocycle i j k
  obtain ⟨x, hx⟩ := Module.Descent.exists_amitsurDiff₀_eq A Sa M hy₁
  refine ⟨eW x, fun i j => ?_⟩
  rw [← hd₀ x i j, hx, hy]

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A morphism whose kernel has vanishing first Čech cohomology along a covering family has its
images jointly detected by that family.**

Let `b : P ⟶ N`, let `{g i : Y i ⟶ T}` be a family, let `Pb i j` be objects over `Y i` and `Y j`
and `Pb₃ i j k` objects over the three double overlaps, subject to the commutation `hw` of the two
projections of a double overlap with the family and the three commutations `hc₁`, `hc₂`, `hc₃` of
the projections of a triple overlap with those of the double overlaps.  The hypotheses are: that
every degree-one Čech cocycle of the family which `b` kills is the Čech coboundary of a family of
sections over the members which `b` kills, the vanishing of the first Čech cohomology of the
kernel of `b`; that a family of sections of `P` over the members agreeing on the double overlaps
descends to `T`, the sheaf condition for `P` for the family; and that restriction to the members
is injective on the sections of `N` over `T`, the separatedness half of the sheaf condition for
`N`.

The proof is the classical one.  A section `n` of `N` over `T` which is a value of `b` over each
member lifts to sections `p i`, whose pairwise differences over the double overlaps are killed by
`b` — the two restrictions of `n` agree there by `hw` — and form a cocycle, the three commutations
turning the alternating sum into zero; so the cohomology hypothesis corrects the `p i` by sections
`z i` of the kernel to a family which agrees on the overlaps, hence descends to a section `p₀`
over `T`; and `b p₀` restricts to the same section as `n` over every member, hence equals `n`.

This is the family analogue of `SheafOfModules.detectsRange_of_cechH1Vanishing`, and like it it
takes no base-change identification for the target: the identification enters, if at all, only in
verifying the cohomological hypothesis for the kernel.  Composed with
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` it gives surjectivity of an
epimorphism on the sections over a terminal object. -/
theorem jointlyDetectsRange_of_familyCechH1Vanishing {P N : SheafOfModules.{m} R} (b : P ⟶ N)
    {T : C} {ι : Type w} {Y : ι → C} {Pb : ι → ι → C} {Pb₃ : ι → ι → ι → C}
    (g : ∀ i, Y i ⟶ T) (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (s₁ : ∀ i j k, Pb₃ i j k ⟶ Pb j k) (s₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (s₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
    (hw : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j)
    (hc₁ : ∀ i j k, s₃ i j k ≫ pr₁ i j = s₂ i j k ≫ pr₁ i k)
    (hc₂ : ∀ i j k, s₃ i j k ≫ pr₂ i j = s₁ i j k ≫ pr₁ j k)
    (hc₃ : ∀ i j k, s₂ i j k ≫ pr₂ i k = s₁ i j k ≫ pr₂ j k)
    (hker : ∀ ζ : ∀ i j, P.val.obj (op (Pb i j)),
      (∀ i j, b.val.app (op (Pb i j)) (ζ i j) = 0) →
      (∀ i j k, P.val.restrictₛₗ (s₁ i j k).op (ζ j k) -
        P.val.restrictₛₗ (s₂ i j k).op (ζ i k) +
          P.val.restrictₛₗ (s₃ i j k).op (ζ i j) = 0) →
      ∃ z : ∀ i, P.val.obj (op (Y i)), (∀ i, b.val.app (op (Y i)) (z i) = 0) ∧
        ∀ i j, P.val.restrictₛₗ (pr₁ i j).op (z i) -
          P.val.restrictₛₗ (pr₂ i j).op (z j) = ζ i j)
    (hdesc : ∀ p : ∀ i, P.val.obj (op (Y i)),
      (∀ i j, P.val.restrictₛₗ (pr₁ i j).op (p i) = P.val.restrictₛₗ (pr₂ i j).op (p j)) →
      ∃ p₀ : P.val.obj (op T), ∀ i, P.val.restrictₛₗ (g i).op p₀ = p i)
    (hinj : Function.Injective
      fun n : N.val.obj (op T) => fun i => N.val.restrictₛₗ (g i).op n) :
    JointlyDetectsRange.{w} b g := by
  intro n hn
  have hnat : ∀ (X X' : Cᵒᵖ) (f : X ⟶ X') (x : P.val.obj X),
      b.val.app X' (P.val.restrictₛₗ f x) = N.val.restrictₛₗ f (b.val.app X x) :=
    fun _ _ f x => PresheafOfModules.naturality_apply b.val f x
  choose p hp₀ using fun i => hn i
  have hp : ∀ i, b.val.app (op (Y i)) (p i) = N.val.restrictₛₗ (g i).op n := hp₀
  have hbζ : ∀ i j, b.val.app (op (Pb i j))
      (P.val.restrictₛₗ (pr₁ i j).op (p i) - P.val.restrictₛₗ (pr₂ i j).op (p j)) = 0 := by
    intro i j
    rw [map_sub, hnat _ _ _ (p i), hnat _ _ _ (p j), hp i, hp j,
      N.val.restrictₛₗ_restrictₛₗ_op, N.val.restrictₛₗ_restrictₛₗ_op, hw i j, sub_self]
  have hcoc : ∀ i j k,
      P.val.restrictₛₗ (s₁ i j k).op
          (P.val.restrictₛₗ (pr₁ j k).op (p j) - P.val.restrictₛₗ (pr₂ j k).op (p k)) -
        P.val.restrictₛₗ (s₂ i j k).op
          (P.val.restrictₛₗ (pr₁ i k).op (p i) - P.val.restrictₛₗ (pr₂ i k).op (p k)) +
        P.val.restrictₛₗ (s₃ i j k).op
          (P.val.restrictₛₗ (pr₁ i j).op (p i) - P.val.restrictₛₗ (pr₂ i j).op (p j)) = 0 := by
    intro i j k
    rw [map_sub, map_sub, map_sub, P.val.restrictₛₗ_restrictₛₗ_op,
      P.val.restrictₛₗ_restrictₛₗ_op, P.val.restrictₛₗ_restrictₛₗ_op,
      P.val.restrictₛₗ_restrictₛₗ_op, P.val.restrictₛₗ_restrictₛₗ_op,
      P.val.restrictₛₗ_restrictₛₗ_op, hc₁ i j k, hc₂ i j k, hc₃ i j k]
    abel
  obtain ⟨z, hz, hzd₀⟩ := hker _ hbζ hcoc
  have hzd : ∀ i j, P.val.restrictₛₗ (pr₁ i j).op (z i) -
      P.val.restrictₛₗ (pr₂ i j).op (z j) =
      P.val.restrictₛₗ (pr₁ i j).op (p i) - P.val.restrictₛₗ (pr₂ i j).op (p j) := hzd₀
  have hagree : ∀ i j, P.val.restrictₛₗ (pr₁ i j).op (p i - z i) =
      P.val.restrictₛₗ (pr₂ i j).op (p j - z j) := by
    intro i j
    have hswap : (P.val.restrictₛₗ (pr₁ i j).op (p i) -
          P.val.restrictₛₗ (pr₁ i j).op (z i)) -
        (P.val.restrictₛₗ (pr₂ i j).op (p j) - P.val.restrictₛₗ (pr₂ i j).op (z j)) =
        (P.val.restrictₛₗ (pr₁ i j).op (p i) - P.val.restrictₛₗ (pr₂ i j).op (p j)) -
        (P.val.restrictₛₗ (pr₁ i j).op (z i) -
          P.val.restrictₛₗ (pr₂ i j).op (z j)) := by abel
    rw [map_sub, map_sub, ← sub_eq_zero, hswap, hzd i j, sub_self]
  obtain ⟨q, hq₀⟩ := hdesc _ hagree
  have hq : ∀ i, P.val.restrictₛₗ (g i).op q = p i - z i := hq₀
  refine ⟨q, hinj (funext fun i => ?_)⟩
  show N.val.restrictₛₗ (g i).op (b.val.app (op T) q) = N.val.restrictₛₗ (g i).op n
  rw [← hnat _ _ _ q, hq i, map_sub, hz i, sub_zero, hp i]

end SheafOfModules

end
