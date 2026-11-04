module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksFrontier.Deformation.Basic

/-!
# An object of `𝒞_Λ` whose maximal ideal vanishes is terminal

An object of the category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field
identified with `k` is terminal as soon as it is a field, i.e. as soon as its maximal
ideal vanishes. Indeed a morphism `A ⟶ K` into such an object is forced: compatibility
with the chosen identifications of the residue fields determines the image of every
element modulo the maximal ideal of `K`, which is zero. The map so determined is the
residue map of `A` read through the two identifications, and it is a local `Λ`-algebra
map.

This file proves that criterion, in the generality in which it applies to every object of
`𝒞_Λ` supported on a field — among them the object denoted `k` in Stacks Project, Tag
06GC, which is the base of the special fibre of a deformation problem over `𝒞_Λ`.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.toField` is the unique morphism into an object of
  `𝒞_Λ` whose maximal ideal vanishes.
* `Deformation.ArtinianLocalAlgCat.algEquivOfEq` transports an equality of objects into a
  `Λ`-algebra isomorphism.

## Main results

* `Deformation.ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot`: an object of
  `𝒞_Λ` whose maximal ideal vanishes is terminal.
* `Deformation.ArtinianLocalAlgCat.isTerminal_of_algEquiv`: an object of `𝒞_Λ` which is
  `Λ`-algebra isomorphic to `k` is terminal.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue map of an object of `𝒞_Λ` whose maximal ideal vanishes is injective. -/
theorem residue_injective_of_maximalIdeal_eq_bot
    (K : ArtinianLocalAlgCat.{u, v, w} Λ k) (hK : maximalIdeal K = ⊥) :
    Function.Injective (residue K) := by
  intro x y hxy
  have hz : residue K (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hmem := (residue_eq_zero_iff _).mp hz
  rw [hK] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

/-- The residue map of an object of `𝒞_Λ` whose maximal ideal vanishes, as a `Λ`-algebra
isomorphism onto the residue field. -/
noncomputable def residueAlgEquiv (K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) : K ≃ₐ[Λ] ResidueField K :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom Λ K (ResidueField K)) <| by
    have hcoe : ((IsScalarTower.toAlgHom Λ K (ResidueField K) : K →ₐ[Λ] ResidueField K) :
        K → ResidueField K) = residue K := by
      funext x
      change algebraMap K (ResidueField K) x = _
      rw [ResidueField.algebraMap_eq]
    rw [hcoe]
    exact ⟨residue_injective_of_maximalIdeal_eq_bot K hK, residue_surjective⟩

/-- The isomorphism `residueAlgEquiv K hK` sends `x` to its residue class. -/
@[simp]
theorem residueAlgEquiv_apply (K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) (x : K) : residueAlgEquiv K hK x = residue K x := by
  show algebraMap K (ResidueField K) x = _
  rw [ResidueField.algebraMap_eq]

/-- The identification of the residue field of `A` with the underlying ring of an object
`K` of `𝒞_Λ` whose maximal ideal vanishes, obtained from the two chosen identifications
with `k`. -/
noncomputable def residueFieldAlgEquivOfField (A K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) : ResidueField A ≃ₐ[Λ] K :=
  A.residueEquiv.trans (K.residueEquiv.symm.trans (residueAlgEquiv K hK).symm)

/-- The canonical morphism of `𝒞_Λ` into an object whose maximal ideal vanishes: the
residue map of the source, read through the two chosen identifications with `k`. -/
noncomputable def toField (A K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) : A ⟶ K where
  hom := (residueFieldAlgEquivOfField A K hK).toAlgHom.comp
    (IsScalarTower.toAlgHom Λ A (ResidueField A))
  isLocal := by
    refine ⟨fun a ha ↦ ?_⟩
    have ha' : IsUnit (residue A a) := by
      refine (MulEquiv.isUnit_map (residueFieldAlgEquivOfField A K hK)).mp ?_
      have : (residueFieldAlgEquivOfField A K hK) (residue A a) =
          ((residueFieldAlgEquivOfField A K hK).toAlgHom.comp
            (IsScalarTower.toAlgHom Λ A (ResidueField A))) a := by
        change _ = (residueFieldAlgEquivOfField A K hK)
          (algebraMap A (ResidueField A) a)
        rw [ResidueField.algebraMap_eq]
      rw [this]
      exact ha
    exact (inferInstance : IsLocalHom (residue A)).map_nonunit a ha'
  residue_comm := fun a ↦ by
    have hval : ((residueFieldAlgEquivOfField A K hK).toAlgHom.comp
        (IsScalarTower.toAlgHom Λ A (ResidueField A))) a =
        (residueAlgEquiv K hK).symm (K.residueEquiv.symm (A.residueEquiv (residue A a))) := by
      change (residueFieldAlgEquivOfField A K hK)
        (algebraMap A (ResidueField A) a) = _
      rw [ResidueField.algebraMap_eq]
      rfl
    rw [hval]
    have hres : residue K
        ((residueAlgEquiv K hK).symm
          (K.residueEquiv.symm (A.residueEquiv (residue A a)))) =
        K.residueEquiv.symm (A.residueEquiv (residue A a)) := by
      rw [← residueAlgEquiv_apply K hK, AlgEquiv.apply_symm_apply]
    rw [hres, AlgEquiv.apply_symm_apply]

/-- An object of `𝒞_Λ` whose maximal ideal vanishes is a terminal object. -/
noncomputable def isTerminal_of_maximalIdeal_eq_bot (K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) : Limits.IsTerminal K := by
  refine Limits.IsTerminal.ofUniqueHom (fun A ↦ toField A K hK) fun A f ↦ ?_
  apply hom_ext
  ext a
  refine residue_injective_of_maximalIdeal_eq_bot K hK ?_
  apply K.residueEquiv.injective
  rw [f.residue_comm a, (toField A K hK).residue_comm a]

/-- An object of `𝒞_Λ` that is `Λ`-algebra isomorphic to `k` is a terminal object. -/
noncomputable def isTerminal_of_algEquiv (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (i : A ≃ₐ[Λ] k) : Limits.IsTerminal A := by
  refine isTerminal_of_maximalIdeal_eq_bot A ?_
  rw [← isField_iff_maximalIdeal_eq]
  exact MulEquiv.isField (Field.toIsField k) i.toMulEquiv

/-- An equality of objects of `𝒞_Λ` induces a `Λ`-algebra isomorphism of the underlying
algebras. -/
noncomputable def algEquivOfEq {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B) :
    A ≃ₐ[Λ] B := by
  subst h
  exact AlgEquiv.refl

/-- In an object of `𝒞_Λ` whose maximal ideal vanishes, the nonunits are exactly `0`. -/
theorem eq_zero_iff_not_isUnit_of_maximalIdeal_eq_bot
    (K : ArtinianLocalAlgCat.{u, v, w} Λ k) (hK : maximalIdeal K = ⊥) (z : K) :
    z = 0 ↔ ¬ IsUnit z := by
  rw [← Ideal.mem_bot, ← hK, mem_maximalIdeal]
  rfl

/-- A morphism of `𝒞_Λ` into an object whose maximal ideal vanishes kills exactly the
nonunits of its source, i.e. exactly the maximal ideal. -/
theorem hom_eq_zero_iff_not_isUnit (A K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) (f : A ⟶ K) (a : A) : f.hom a = 0 ↔ ¬ IsUnit a := by
  rw [eq_zero_iff_not_isUnit_of_maximalIdeal_eq_bot K hK]
  refine not_congr ⟨fun h ↦ f.isLocal.map_nonunit a h, fun h ↦ h.map f.hom⟩

/-- A morphism of `𝒞_Λ` into an object whose maximal ideal vanishes is surjective: on
residue fields it is the chosen identification with `k`, and the residue map of the target
is bijective. -/
theorem hom_surjective (A K : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hK : maximalIdeal K = ⊥) (f : A ⟶ K) : Function.Surjective f.hom := by
  intro c
  have hinj : Function.Injective
      (fun z : K ↦ K.residueEquiv (residue K z)) := fun z z' hzz ↦
    residue_injective_of_maximalIdeal_eq_bot K hK (K.residueEquiv.injective hzz)
  obtain ⟨a, ha⟩ : ∃ a : A, A.residueEquiv (residue A a) =
      K.residueEquiv (residue K c) := by
    obtain ⟨a, ha⟩ := residue_surjective
      (R := A) (A.residueEquiv.symm (K.residueEquiv (residue K c)))
    exact ⟨a, by rw [ha, AlgEquiv.apply_symm_apply]⟩
  exact ⟨a, hinj ((f.residue_comm a).trans ha)⟩

end ArtinianLocalAlgCat

end Deformation

end
