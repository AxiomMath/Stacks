module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceGradedChart
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.ChartRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The cyclic cover

Given a line bundle `L` on a `k`-scheme `Z`, a trivialisation `φ : Symⁿ L ≅ 𝒪_Z`, and an element
`c` of a `k`-algebra `S`, the cyclic cover is `X = 𝕃 ×_{𝔸¹_k} Spec S`, where `𝕃` is the total space
of `L` mapping to `𝔸¹_k` by the function `φ⁻¹(1)`, and `Spec S ⟶ 𝔸¹_k` is given by `c`.
Equivalently `X = Spec_{Z_S}(Sym(L_S)/(φ - c))`, with `Z_S = Z ×_k Spec S`.

## Main definitions

* `Stacks.CyclicCover.rootMap`: The morphism `𝕃 ⟶ 𝔸¹_k` given by the function `φ⁻¹(1)`.
* `Stacks.CyclicCover.pointMap`: The morphism `Spec S ⟶ 𝔸¹_k` given by `c`.
* `Stacks.CyclicCover.cover`: The cyclic cover `X = 𝕃 ×_{𝔸¹_k} Spec S`.
* `Stacks.CyclicCover.coverMap`: The morphism `X ⟶ Z_S`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial

universe u

namespace Stacks.CyclicCover


variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (L : Z.Modules)
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L]

/-- The line bundle `L` on `Z`, over `Spec k`. -/
abbrev situation : Stacks.LineBundle.Situation.{u} := ⟨Z, Spec (.of k), f, L⟩

/-- The total space `𝕃 = Spec_Z(Sym L)` of `L`. -/
abbrev totalSpace : Scheme.{u} := (situation f L).totalSpace

/-- The projection `𝕃 ⟶ Z`. -/
abbrev totalSpaceToBase : totalSpace f L ⟶ Z := (situation f L).totalSpaceToBase

variable {L} {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- The global section `φ⁻¹(1)` of `Symⁿ L`. -/
def rootSection : ((situation f L).symmetricAlgebra.piece (n : ℤ)).val.obj (op ⊤) :=
  φ.inv.val.app (op ⊤) (1 : Γ(Z, ⊤))

/-- The function `φ⁻¹(1)` on `𝕃`, homogeneous of degree `n`. -/
def rootFunction : Γ(totalSpace f L, ⊤) :=
  (totalSpace f L).presheaf.map (homOfLE (by simp) : (⊤ : (totalSpace f L).Opens) ⟶
      totalSpaceToBase f L ⁻¹ᵁ ⊤).op
    ((situation f L).totalFunction n ⊤ (rootSection f φ))

/-- The `k`-algebra structure of the functions on `𝕃`. -/
def totalStructure : k →+* Γ(totalSpace f L, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (totalSpaceToBase f L ≫ f).appTop).hom

/-- The morphism `𝕃 ⟶ 𝔸¹_k` given by the function `φ⁻¹(1)`. -/
def rootMap : totalSpace f L ⟶ Spec (.of k[X]) :=
  (totalSpace f L).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (eval₂RingHom (totalStructure f (L := L)) (rootFunction f φ)))

variable (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- The morphism `Spec S ⟶ 𝔸¹_k` given by `c`. -/
def pointMap : Spec (.of S) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (aeval (R := k) c).toRingHom)

/-- The base change `Z_S = Z ×_k Spec S`. -/
abbrev baseChange : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k S)))

/-- **The cyclic cover** `X = 𝕃 ×_{𝔸¹_k} Spec S`, i.e. `Spec_{Z_S}(Sym(L_S)/(φ - c))`. -/
abbrev cover : Scheme.{u} := pullback (rootMap f φ) (pointMap S c)

/-- `𝕃 ⟶ 𝔸¹_k ⟶ Spec k` is the structure morphism of `𝕃`. -/
theorem rootMap_comp : rootMap f φ ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) =
    totalSpaceToBase f L ≫ f := by
  rw [rootMap, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (eval₂RingHom (totalStructure f (L := L)) (rootFunction f φ)).comp (algebraMap k k[X]) =
      totalStructure f := by ext r; simp
  rw [this, totalStructure, CommRingCat.ofHom_hom, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc]
  simp

/-- `Spec S ⟶ 𝔸¹_k ⟶ Spec k` is the structure morphism of `Spec S`. -/
theorem pointMap_comp : pointMap S c ≫ Spec.map (CommRingCat.ofHom (algebraMap k k[X])) =
    Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  rw [pointMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r; simp

/-- **The finite morphism `p : X ⟶ Z_S`** of the cyclic cover
`X = Spec_{Z_S}(Sym(L_S)/(φ - c)) = 𝕃 ×_{𝔸¹_k} Spec S`. -/
def coverMap : cover f φ S c ⟶ baseChange f S :=
  pullback.lift (pullback.fst _ _ ≫ totalSpaceToBase f L) (pullback.snd _ _) (by
    rw [Category.assoc, ← rootMap_comp f φ, ← Category.assoc, pullback.condition,
      Category.assoc, pointMap_comp])

/-- The composite of `coverMap` with the projection `Z_S ⟶ Z` is the composite `X ⟶ 𝕃 ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem coverMap_fst : coverMap f φ S c ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ totalSpaceToBase f L := pullback.lift_fst _ _ _

/-- The composite of `coverMap` with the projection `Z_S ⟶ Spec S` is the projection
`X ⟶ Spec S`. -/
@[reassoc (attr := simp)]
theorem coverMap_snd : coverMap f φ S c ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

end Stacks.CyclicCover
