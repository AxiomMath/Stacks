module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.AlgebraicGeometry.Picard.EssentiallySmall.SmallModel
public import StacksFrontier.AlgebraicGeometry.Picard.Group
public import StacksCore.Tactic.StacksAttribute

/-!
# The invertible modules on a ringed site are essentially small

Let `O` be a sheaf of commutative rings on a site `(C, J)` and call a sheaf `L` of `O`-modules
*invertible* when tensoring by it is an equivalence of the category of sheaves of `O`-modules
(Tag 01CS). This file proves Stacks Tag 040B: the isomorphism classes of invertible
`O`-modules form a *set*, of size `max u v w` where `C : Type u` has morphisms in `Type v` and
the module sections live in `Type w`.

The proof is the one of the source, carried out on sections rather than on covers. Invertibility
of `L` produces a presheaf of modules `N` and a pairing `ψ : L ⊗ N ⟶ O` of presheaves of modules
which is locally bijective (`Stacks.SheafOfModules.exists_locallyBijective_pairing`, the input
Tag 0B8N uses as well). Over an object `W` on which the unit section `1` lies in the image of
`ψ` — such objects cover any given object, by local surjectivity — write
`1 = ∑ⱼ ψ(xⱼ ⊗ yⱼ)` with finitely many sections `xⱼ` of `L` and `yⱼ` of `N` over `W`. Then the
finitely many "coordinates" `v ↦ (ψ(v ⊗ yⱼ))ⱼ` determine `v`: if `ψ(d ⊗ yⱼ) = 0` for every `j`,
then `d ⊗ yⱼ` is locally zero by local injectivity of `ψ`, so contracting against `xⱼ` shows
that `ψ(xⱼ ⊗ yⱼ) • d` is locally zero, hence zero because `L` is a sheaf; summing over `j` gives
`d = 1 • d = 0`. So the sections of `L` over `W` inject into `Σ n, Fin n → O(W)`, and the sheaf
condition propagates this to a uniform bound on the sections of `L` over any object: they inject
into `invertibleSectionBound O`, a family of types of size `max u v w` which does not depend on
`L`. Smallness of the isomorphism classes then follows from
`Stacks.SheafOfModules.essentiallySmall_of_exists_injective_sections`.

No local trivialization, no slice site and no sheafification of the slice sites are used; the
only hypotheses beyond those of the statement of Tag 01CS are the two the invertibility API of
this development always carries, `HasWeakSheafify J AddCommGrpCat.{w}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{w}`.

## Main definitions

* `Stacks.SheafOfModules.pairingLin` — a pairing `L ⊗ N ⟶ O` of presheaves of modules read over
  one object of the site as a linear map out of the tensor product of the sections.
* `Stacks.SheafOfModules.smulPairing` — the linear map `v ⊗ z ↦ ψ(a ⊗ z) • v` on sections, for a
  fixed section `a` of `L`.
* `Stacks.SheafOfModules.invertibleSectionBound` — the uniform bound on the sections of an
  invertible sheaf of modules.

## Main results

* `Stacks.SheafOfModules.injective_pairingCoords` — the coordinates against a dual basis of a
  locally bijective pairing determine a section.
* `Stacks.SheafOfModules.exists_injective_invertibleSectionBound` — the sections of an
  invertible sheaf of modules inject into the uniform bound.
* `Stacks.SheafOfModules.essentiallySmall_isInvertible` — Tag 040B.
* `Stacks.Picard.small_picardGroup` — consequently the Picard group of `(C, J, O)` is
  `max u v w`-small.

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    O)}

section Pairing

/-- A pairing `ψ : L ⊗ N ⟶ O` of presheaves of modules, evaluated over one object of the site.
The tensor product of presheaves of modules is computed sectionwise, so this is an honest
linear map `L(X) ⊗_{O(X)} N(X) →ₗ O(X)`. -/
def pairingLin
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (X : Cᵒᵖ) :
    (Lp.obj X) ⊗[O.obj X] (Np.obj X) →ₗ[O.obj X] O.obj X :=
  ((PresheafOfModules.evaluation _ X).map ψ).hom

/-- On a pure tensor, `pairingLin ψ X` is the component of `ψ` at `X`. -/
theorem pairingLin_tmul
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (X : Cᵒᵖ) (v : Lp.obj X) (z : Np.obj X) :
    pairingLin ψ X (v ⊗ₜ z) = ψ.app X (v ⊗ₜ z) := rfl

/-- The pairing commutes with restriction, on pure tensors: the naturality of `ψ`. -/
theorem map_pairingLin_tmul
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Lp.obj X) (z : Np.obj X) :
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).map f (pairingLin ψ X (v ⊗ₜ
      z))
      = pairingLin ψ Y (Lp.map f v ⊗ₜ Np.map f z) :=
  (PresheafOfModules.naturality_apply ψ f (v ⊗ₜ[O.obj X] z)).symm

/-- Contracting the second factor against a pairing and scaling a fixed section `a` of `L`:
the linear map `v ⊗ z ↦ ψ(a ⊗ z) • v` on the sections over one object. -/
def smulPairing
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (X : Cᵒᵖ) (a : Lp.obj X) :
    (Lp.obj X) ⊗[O.obj X] (Np.obj X) →ₗ[O.obj X] Lp.obj X :=
  TensorProduct.lift
    (LinearMap.flip (LinearMap.lsmul (O.obj X) (Lp.obj X) ∘ₗ
      (pairingLin ψ X ∘ₗ TensorProduct.mk (O.obj X) (Lp.obj X) (Np.obj X) a)))

/-- On a pure tensor, `smulPairing ψ X a (v ⊗ z) = ψ(a ⊗ z) • v`. -/
theorem smulPairing_tmul
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (X : Cᵒᵖ) (a v : Lp.obj X) (z : Np.obj X) :
    smulPairing ψ X a (v ⊗ₜ z) = pairingLin ψ X (a ⊗ₜ z) • v := rfl

end Pairing

/-- **The coordinates of a dual basis determine a section.** Let `ψ : L ⊗ N ⟶ O` be a locally
injective pairing of presheaves of modules with `L` a sheaf, and let `xⱼ`, `yⱼ` be finitely many
sections of `L` and `N` over an object `W` whose pairings sum to `1`. Then a section of `L` over
`W` is determined by the finitely many values `ψ(· ⊗ yⱼ)`.

This is the sections form of the splitting of Tag 0B8N: the retraction of the resulting
embedding `L(W) ↪ O(W)^n` is `(cⱼ) ↦ ∑ⱼ cⱼ • xⱼ`. Unlike Tag 0B8N it needs nothing about the
slice site over `W`, because the conclusion is about `W` alone. -/
theorem injective_pairingCoords
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallyInjective J ψ]
    {W : C} {n : ℕ} (x : Fin n → Lp.obj (op W)) (y : Fin n → Np.obj (op W))
    (hxy : ∑ j, pairingLin ψ (op W) (x j ⊗ₜ y j) = 1) :
    Function.Injective
      (fun (v : Lp.obj (op W)) (j : Fin n) => pairingLin ψ (op W) (v ⊗ₜ y j)) := by
  intro v v' h
  rw [← sub_eq_zero]
  set d : Lp.obj (op W) := v - v' with hd
  have h1 : ∀ j, pairingLin ψ (op W) (d ⊗ₜ y j) = 0 := by
    intro j
    rw [hd, TensorProduct.sub_tmul, map_sub]
    exact sub_eq_zero_of_eq (congrFun h j)
  have h2 : ∀ j, (pairingLin ψ (op W) (x j ⊗ₜ y j)) • d = 0 := by
    intro j
    have hmem : Presheaf.equalizerSieve (F := (Lp ⊗ Np).presheaf) (X := op W)
        (d ⊗ₜ y j) 0 ∈ J W := by
      refine Presheaf.equalizerSieve_mem J
        ((PresheafOfModules.toPresheaf
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)).map ψ) _ _ ?_
      exact (h1 j).trans (map_zero _).symm
    refine hLp.isSeparated W _ hmem _ _ ?_
    intro W' g hg
    have hz : (Lp.map g.op d ⊗ₜ Np.map g.op (y j) :
        (Lp.obj (op W')) ⊗[O.obj (op W')] (Np.obj (op W'))) = 0 := by
      have h0 : (Lp ⊗ Np).presheaf.map g.op (d ⊗ₜ y j)
          = (Lp ⊗ Np).presheaf.map g.op 0 := hg
      rw [map_zero] at h0
      exact h0
    have hs := congrArg (smulPairing ψ (op W') (Lp.map g.op (x j))) hz
    rw [map_zero] at hs
    have e2 : Lp.map g.op ((pairingLin ψ (op W) (x j ⊗ₜ y j)) • d)
        = (0 : Lp.obj (op W')) := by
      rw [PresheafOfModules.map_smul, map_pairingLin_tmul]
      exact hs
    exact e2.trans (map_zero _).symm
  rw [← one_smul (O.obj (op W)) d, ← hxy, Finset.sum_smul]
  exact Finset.sum_eq_zero fun j _ => h2 j

/-- The uniform bound on the sections of an invertible sheaf of `O`-modules over an object `X`:
a family, indexed by the arrows into `X`, of finite tuples of sections of `O`. It is a type of
size `max u v w`, and crucially it does not mention the invertible module. -/
def invertibleSectionBound (O : Cᵒᵖ ⥤ CommRingCat.{w}) (X : Cᵒᵖ) : Type (max u v w) :=
  ∀ W : C, (W ⟶ X.unop) → Σ n : ℕ, (Fin n → O.obj (op W))

section Bound

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The sections of an invertible sheaf of modules are uniformly bounded.** Over an object `U`
they inject into `invertibleSectionBound O (op U)`, a type that does not depend on the module.
A section is sent to the tuple of its coordinates against a dual basis of the invertible
pairing over each member of the covering sieve on which the unit section is in the image of the
pairing; the sheaf condition makes that assignment injective. -/
theorem exists_injective_invertibleSectionBound
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) [hL :
      IsInvertible O hO L]
    (U : C) :
    ∃ f : L.val.obj (op U) → invertibleSectionBound O (op U), Function.Injective f := by
  obtain ⟨Lp, hLp, rfl⟩ : ∃ (Lp : PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (hLp : Presheaf.IsSheaf J Lp.presheaf),
      L = (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        O hO)) :=
    ⟨L.val, L.isSheaf, rfl⟩
  obtain ⟨Np, ψ, hsurj, hinj⟩ :=
    exists_locallyBijective_pairing (hO := hO) hLp inferInstance
  set S : Sieve U := Presheaf.imageSieve
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)).map ψ)
    (1 : O.obj (op U))
  have hS : S ∈ J U := Presheaf.imageSieve_mem J _ _
  have key : ∀ (W : C) (g : W ⟶ U),
      ∃ f : Lp.obj (op W) → Σ n : ℕ, (Fin n → O.obj (op W)),
        S.arrows g → Function.Injective f := by
    intro W g
    by_cases hg : S.arrows g
    · obtain ⟨t, ht⟩ := hg
      obtain ⟨n, x, y, hxy⟩ := exists_fin_tmul_eq t
      have hxy' : (∑ j, x j ⊗ₜ y j :
          (Lp.obj (op W)) ⊗[O.obj (op W)] (Np.obj (op W))) = t := hxy
      have hsum : ∑ j, pairingLin ψ (op W) (x j ⊗ₜ y j) = 1 := by
        have ht1 : pairingLin ψ (op W) (∑ j, x j ⊗ₜ y j) = 1 := by
          rw [hxy']
          exact ht.trans (PresheafOfModules.unit_map_one _ _)
        rw [map_sum] at ht1
        exact ht1
      exact ⟨fun v => ⟨n, fun j => pairingLin ψ (op W) (v ⊗ₜ y j)⟩,
        fun _ => fun v v' hvv' =>
          injective_pairingCoords hLp ψ x y hsum (eq_of_heq (Sigma.mk.injEq .. ▸ hvv').2)⟩
    · exact ⟨fun _ => ⟨0, Fin.elim0⟩, fun h => absurd h hg⟩
  choose F hF using key
  refine ⟨fun a W g => F W g (Lp.map g.op a), ?_⟩
  intro a b hab
  exact hLp.isSeparated U S hS a b
    (fun W g hg => hF W g hg (congrFun (congrFun hab W) g))

/-- **Stacks 040B.** The invertible sheaves of modules on a ringed site form an essentially
small class: there is a set of invertible modules such that every invertible module is
isomorphic to exactly one of them. Equivalently, the isomorphism classes of invertible
`O`-modules form a set of size `max u v w`.

The two instance hypotheses are the standing hypotheses of the invertible-module API of this
development — they are what makes the sheafified tensor product and the locally bijective
pairing of Tag 0B8N available — and they are satisfied wherever Tag 01CX builds the Picard
group. -/
@[stacks 040B]
theorem essentiallySmall_isInvertible
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)) :
    ObjectProperty.EssentiallySmall.{max u v w} (IsInvertible O hO) :=
  essentiallySmall_of_exists_injective_sections _ (invertibleSectionBound O)
    fun L hL X => exists_injective_invertibleSectionBound hO L (hL := hL) X.unop

/-- **Stacks 040B**, for the `AlgebraicGeometry` spelling of invertibility. The two
invertibility predicates of this library agree
(`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`), so the class of invertible
modules is the same and essential smallness transfers. -/
theorem essentiallySmall_isInvertible_algebraicGeometry
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)) :
    ObjectProperty.EssentiallySmall.{max u v w}
      (AlgebraicGeometry.SheafOfModules.IsInvertible O hO) :=
  have := essentiallySmall_isInvertible O hO
  ObjectProperty.EssentiallySmall.of_le
    fun L hL => IsInvertible.ofAlgebraicGeometry O hO L hL

end Bound

end Stacks.SheafOfModules

namespace Stacks.Picard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Stacks 040B for the Picard group.** The Picard group of `(C, J, O)` is `max u v w`-small:
the isomorphism classes of invertible sheaves of `O`-modules form a set of that size. This is
`Stacks.Picard.small_picardGroup_of_essentiallySmall` with its two hypotheses discharged, the
first by `Stacks.SheafOfModules.locallySmall` and the second by Tag 040B. -/
theorem small_picardGroup :
    Small.{max u v w} (Stacks.SheafOfModules.PicardGroup O hO) :=
  have := Stacks.SheafOfModules.locallySmall
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) (C := C) (J := J)
  have := Stacks.SheafOfModules.essentiallySmall_isInvertible O hO
  small_picardGroup_of_essentiallySmall O hO

end Stacks.Picard

end
