module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionFirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionAffine
public import StacksFrontier.RingTheory.Polynomial.ArtinSchreierCokernel

/-!
# The Artin–Schreier boundary `Γ(X, 𝒪_X) ⟶ H¹(X, 𝐙/p𝐙)`

Let `X` be a scheme on which the prime `p` vanishes. The long exact cohomology sequence of the
Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` ([Stacks, Tag 0A3J]) begins

`Γ(X, 𝒪_X) ⟶[F - 1] Γ(X, 𝒪_X) ⟶[δ] H¹(X, 𝐙/p𝐙) ⟶ H¹(X, 𝐆_a)`,

where `H⁰(X, 𝐆_a) = Γ(X, 𝒪_X)`. When `X` is affine the last group vanishes, so
`H¹(X, 𝐙/p𝐙)` is the cokernel of `f ↦ f ^ p - f` on `Γ(X, 𝒪_X)`. This file constructs `δ`,
proves the exactness, and proves that `δ` is compatible with restriction along any morphism of
schemes `g : Y ⟶ X`, the function `a` going to its pullback `g^* a`.

## Main definitions

* `Stacks.ArtinSchreier.sheafHZeroAdditiveAddEquiv`: `H⁰(X, 𝐆_a) ≃+ Γ(X, 𝒪_X)`.
* `Stacks.ArtinSchreier.artinSchreierBoundary`: the boundary `δ : Γ(X, 𝒪_X) →+ H¹(X, 𝐙/p𝐙)`.

## Main results

* `Stacks.ArtinSchreier.exact_ringArtinSchreier_artinSchreierBoundary`: the kernel of `δ` is the
  image of `f ↦ f ^ p - f`.
* `Stacks.ArtinSchreier.surjective_artinSchreierBoundary`: `δ` is onto when `X` is affine.
* `Stacks.ArtinSchreier.sheafHIsoCongr_etaleCohomologyRestrictionMap_artinSchreierBoundary`:
  restriction along `g` carries `δ a` to `δ (g^* a)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

section DegreeZero

variable (X : Scheme.{u}) [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`H⁰(X, 𝐆_a) ≅ Γ(X, 𝒪_X)`**: a degree-zero class is a global section of `𝐆_a`, that is a
global function on `X`. -/
def sheafHZeroAdditiveAddEquiv : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) 0 ≃+ Γ(X, ⊤) :=
  (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).trans
    (AddEquiv.ulift (α := Γ(X, ⊤)))

/-- `H⁰(𝐆_a) ≅ Γ(𝒪)` reads a class as the global section it is. -/
theorem sheafHZeroAdditiveAddEquiv_apply (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) 0) :
    sheafHZeroAdditiveAddEquiv.{w} X x =
      ULift.down (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminalEtaleMkId X) x) :=
  rfl

/-- The inverse of `H⁰(𝐆_a) ≅ Γ(𝒪)` sends `a` to the class of the section `a`. -/
theorem sheafHZeroAdditiveAddEquiv_symm_apply (a : Γ(X, ⊤)) :
    (sheafHZeroAdditiveAddEquiv.{w} X).symm a =
      (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).symm
        (ofSection.{u, u + 1} (U := Scheme.Etale.mk (𝟙 X)) a) :=
  rfl

/-- **The Artin–Schreier map on `H⁰(𝐆_a)` is `a ↦ a ^ p - a`.** -/
theorem sheafHZeroAdditiveAddEquiv_map_artinSchreierMap {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) 0) :
    sheafHZeroAdditiveAddEquiv.{w} X (Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp hX) 0 x) =
      sheafHZeroAdditiveAddEquiv.{w} X x ^ p - sheafHZeroAdditiveAddEquiv.{w} X x := by
  obtain ⟨a, rfl⟩ := (sheafHZeroAdditiveAddEquiv.{w} X).symm.surjective x
  rw [AddEquiv.apply_symm_apply, sheafHZeroAdditiveAddEquiv_symm_apply,
    Sheaf.H.equiv₀_symm_naturality, sheafHZeroAdditiveAddEquiv_apply, AddEquiv.apply_symm_apply]
  rfl

end DegreeZero

section Restriction

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The comparison on `𝐆_a`, computed on a section.** A global function `x` on an étale
`X`-scheme `V`, viewed as a section of `g^{-1} 𝐆_{a,X}` over `V ×_X Y` through the unit of the
adjunction, is carried to its pullback along the projection `V ×_X Y ⟶ V`. -/
theorem additiveInverseImageComparison_app_ofSection (V : X.Etale) (x : Γ(V.left, ⊤)) :
    (additiveInverseImageComparison.{u, u + 1} g).hom.app (op ((smallEtaleBaseChange g).obj V))
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
          (additiveSheaf.{u, u + 1} X)).hom.app (op V) (ofSection.{u, u + 1} x)) =
      ofSection.{u, u + 1} (U := (smallEtaleBaseChange g).obj V)
        ((pullback.fst V.hom g).appTop.hom x) := by
  have h := additiveInverseImageComparison_transpose.{u, u + 1} g
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ : additiveSheaf.{u, u + 1} X ⟶
      (etaleAbelianDirectImage.{u, 0} g).obj (additiveSheaf.{u, u + 1} Y) =>
    φ.hom.app (op V) (ofSection.{u, u + 1} x)) h

/-- **Restriction on `H⁰(𝐆_a)` is pullback of functions**, through `H⁰(𝐆_a) ≅ Γ(𝒪)`. -/
theorem sheafHZeroAdditiveAddEquiv_additiveRestriction
    (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) 0) :
    sheafHZeroAdditiveAddEquiv.{w} Y (additiveRestriction g 0 x) =
      g.appTop.hom (sheafHZeroAdditiveAddEquiv.{w} X x) := by
  obtain ⟨a, rfl⟩ := (sheafHZeroAdditiveAddEquiv.{w} X).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  let h := ((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange g)).from
    (Scheme.Etale.mk (𝟙 Y))
  have hn := ConcreteCategory.congr_hom
    ((additiveInverseImageComparison.{u, u + 1} g).hom.naturality h.op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
      (additiveSheaf.{u, u + 1} X)).hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (ofSection.{u, u + 1} (U := Scheme.Etale.mk (𝟙 X)) a))
  have key := hn.trans (congrArg ((additiveSheaf.{u, u + 1} Y).obj.map h.op)
    (additiveInverseImageComparison_app_ofSection g (Scheme.Etale.mk (𝟙 X)) a))
  have main : Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} Y) (isTerminalEtaleMkId Y)
      (additiveRestriction g 0 ((sheafHZeroAdditiveAddEquiv.{w} X).symm a)) =
      ofSection.{u, u + 1} (U := Scheme.Etale.mk (𝟙 Y)) (g.appTop.hom a) := by
    refine (Sheaf.H.equiv₀_naturality (isTerminalEtaleMkId Y)
      (additiveInverseImageComparison.{u, u + 1} g)
      (etaleCohomologyRestrictionMap.{u, 0, w} g (additiveSheaf.{u, u + 1} X) 0
        ((sheafHZeroAdditiveAddEquiv.{w} X).symm a))).symm.trans ?_
    refine (congrArg ((additiveInverseImageComparison.{u, u + 1} g).hom.app
      (op (Scheme.Etale.mk (𝟙 Y))))
      (equiv₀_etaleCohomologyRestrictionMap_zero.{u, 0, w} g (additiveSheaf.{u, u + 1} X)
        (isTerminalEtaleMkId Y) ((sheafHZeroAdditiveAddEquiv.{w} X).symm a))).trans ?_
    refine (congrArg (fun z => (additiveInverseImageComparison.{u, u + 1} g).hom.app
      (op (Scheme.Etale.mk (𝟙 Y)))
      (((etaleAbelianInverseImage.{u, 0} g).obj (additiveSheaf.{u, u + 1} X)).obj.map h.op
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
          (additiveSheaf.{u, u + 1} X)).hom.app (op (Scheme.Etale.mk (𝟙 X))) z)))
      ((Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).apply_symm_apply _)).trans ?_
    refine key.trans ?_
    exact congrArg (fun φ : Y ⟶ X => ofSection.{u, u + 1} (U := Scheme.Etale.mk (𝟙 Y))
      (φ.appTop.hom a)) (left_comp_pullback_fst_etaleMkId g h)
  rw [sheafHZeroAdditiveAddEquiv_apply, main]
  rfl

end Restriction

/-! ### The boundary -/

section Boundary

variable (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The Artin–Schreier sequence is short exact**, stated with the terms of the sequence
displayed, so that its objects are `𝐙/p𝐙` and `𝐆_a` up to reducible unfolding. -/
theorem shortExact_mk_artinSchreierMap :
    (ShortComplex.mk (zmodSheafHom.{u, u + 1} X hX) (artinSchreierMap.{u, u + 1} X hp hX)
      (zmodSheafHom_comp_artinSchreierMap.{u, u + 1} X hp hX)).ShortExact :=
  constantArtinSchreierSequence_shortExact.{u, u + 1} X hp hX

/-- **The Artin–Schreier boundary** `δ : Γ(X, 𝒪_X) →+ H¹(X, 𝐙/p𝐙)`: a global function, read as a
class in `H⁰(X, 𝐆_a)`, followed by the connecting map of the Artin–Schreier sequence
`0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` ([Stacks, Tag 0A3J]). -/
def artinSchreierBoundary : Γ(X, ⊤) →+ Sheaf.H.{w} (etaleConstantZMod X p) 1 :=
  ((shortExact_mk_artinSchreierMap X hp hX).extClass.postcomp _
    (zero_add 1)).comp (sheafHZeroAdditiveAddEquiv.{w} X).symm.toAddMonoidHom

/-- `Stacks.ArtinSchreier.artinSchreierBoundary`, unfolded. -/
theorem artinSchreierBoundary_apply (a : Γ(X, ⊤)) :
    artinSchreierBoundary.{w} X hp hX a =
      ((sheafHZeroAdditiveAddEquiv.{w} X).symm a).comp
        (shortExact_mk_artinSchreierMap X hp hX).extClass (zero_add 1) :=
  rfl

/-- **The kernel of the Artin–Schreier boundary is the image of `a ↦ a ^ p - a`.** This is
exactness of `H⁰(X, 𝐆_a) ⟶[F - 1] H⁰(X, 𝐆_a) ⟶[δ] H¹(X, 𝐙/p𝐙)` read on global functions. -/
theorem exact_ringArtinSchreier_artinSchreierBoundary [Fact p.Prime] [CharP Γ(X, ⊤) p] :
    Function.Exact (ringArtinSchreier Γ(X, ⊤) p) (artinSchreierBoundary.{w} X hp hX) := by
  have hS := shortExact_mk_artinSchreierMap X hp hX
  intro a
  constructor
  · intro ha
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS
      ((sheafHZeroAdditiveAddEquiv.{w} X).symm a) (zero_add 1) ha
    refine ⟨sheafHZeroAdditiveAddEquiv.{w} X x₂, ?_⟩
    rw [ringArtinSchreier_apply, ← sheafHZeroAdditiveAddEquiv_map_artinSchreierMap X hp hX]
    exact (congrArg (sheafHZeroAdditiveAddEquiv.{w} X) hx₂).trans
      ((sheafHZeroAdditiveAddEquiv.{w} X).apply_symm_apply a)
  · rintro ⟨b, rfl⟩
    have hb : (sheafHZeroAdditiveAddEquiv.{w} X).symm (ringArtinSchreier Γ(X, ⊤) p b) =
        ((sheafHZeroAdditiveAddEquiv.{w} X).symm b).comp
          (Ext.mk₀ (artinSchreierMap.{u, u + 1} X hp hX)) (add_zero 0) := by
      apply (sheafHZeroAdditiveAddEquiv.{w} X).injective
      rw [AddEquiv.apply_symm_apply, ringArtinSchreier_apply]
      exact ((sheafHZeroAdditiveAddEquiv_map_artinSchreierMap X hp hX _).trans
        (by rw [AddEquiv.apply_symm_apply])).symm
    rw [artinSchreierBoundary_apply, hb]
    exact (Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
      ((congrArg (fun z => Ext.comp ((sheafHZeroAdditiveAddEquiv.{w} X).symm b) z (zero_add 1))
        hS.comp_extClass).trans (Ext.comp_zero _ _ _ _ _))

/-- **On an affine scheme the Artin–Schreier boundary is onto**: `H¹(X, 𝐆_a) = 0`
([Stacks, Tag 01XB] with the comparison of [Stacks, Tag 03P2]). -/
theorem surjective_artinSchreierBoundary [IsAffine X] :
    Function.Surjective (artinSchreierBoundary.{w} X hp hX) := by
  have hS := shortExact_mk_artinSchreierMap X hp hX
  have hvan : Subsingleton (Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) 1) :=
    subsingleton_sheafH_additiveSheaf_of_isZero_hgroup X 1 Nat.one_pos
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X
        (SheafOfModules.unit X.ringCatSheaf) ⊤ (isAffineOpen_top X) 1 Nat.one_pos)
  intro y
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS y (hvan.elim _ _) (zero_add 1)
  exact ⟨sheafHZeroAdditiveAddEquiv.{w} X x₃,
    (congrArg (fun z => Ext.comp z hS.extClass (zero_add 1))
      ((sheafHZeroAdditiveAddEquiv.{w} X).symm_apply_apply x₃)).trans hx₃⟩

end Boundary

/-! ### Restriction of the boundary -/

section Naturality

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
  (hY : (p : Γ(Y, ⊤)) = 0)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The inverse image of the Artin–Schreier sequence maps to the Artin–Schreier sequence**: on
`𝐙/p𝐙` by the identification of the inverse image of a constant sheaf, on `𝐆_a` by pulling
functions back. -/
def artinSchreierInverseImageHom :
    (ShortComplex.mk (zmodSheafHom.{u, u + 1} X hX) (artinSchreierMap.{u, u + 1} X hp hX)
      (zmodSheafHom_comp_artinSchreierMap.{u, u + 1} X hp hX)).map
        (etaleAbelianInverseImage.{u, 0} g) ⟶
      ShortComplex.mk (zmodSheafHom.{u, u + 1} Y hY) (artinSchreierMap.{u, u + 1} Y hp hY)
        (zmodSheafHom_comp_artinSchreierMap.{u, u + 1} Y hp hY) where
  τ₁ := ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))).hom
  τ₂ := additiveInverseImageComparison.{u, u + 1} g
  τ₃ := additiveInverseImageComparison.{u, u + 1} g
  comm₁₂ := (inverseImage_zmodSheafHom_comp_additiveInverseImageComparison.{u, u + 1} g hX).symm
  comm₂₃ :=
    (inverseImage_artinSchreierMap_comp_additiveInverseImageComparison.{u, u + 1} g hp hX).symm

/-- **Restriction carries the boundary of a function to the boundary of its pullback.** For
`g : Y ⟶ X` and `a ∈ Γ(X, 𝒪_X)`, restricting `δ a ∈ H¹(X, 𝐙/p𝐙)` along `g` and identifying
`g^{-1} 𝐙/p𝐙` with `𝐙/p𝐙` gives `δ (g^* a)`. -/
theorem sheafHIsoCongr_etaleCohomologyRestrictionMap_artinSchreierBoundary (a : Γ(X, ⊤)) :
    Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
        ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))) 1
        (etaleCohomologyRestrictionMap.{u, 0, w} g (etaleConstantZMod X p) 1
          (artinSchreierBoundary.{w} X hp hX a)) =
      artinSchreierBoundary.{w} Y hp hY (g.appTop.hom a) := by
  have hS := shortExact_mk_artinSchreierMap X hp hX
  have hS' := shortExact_mk_artinSchreierMap Y hp hY
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hS.map_of_exact (etaleAbelianInverseImage.{u, 0} g)) hS'
    (artinSchreierInverseImageHom g hp hX hY)
  have h0 : (sheafHZeroAdditiveAddEquiv.{w} Y).symm (g.appTop.hom a) =
      additiveRestriction g 0 ((sheafHZeroAdditiveAddEquiv.{w} X).symm a) := by
    apply (sheafHZeroAdditiveAddEquiv.{w} Y).injective
    rw [AddEquiv.apply_symm_apply, sheafHZeroAdditiveAddEquiv_additiveRestriction,
      AddEquiv.apply_symm_apply]
  rw [artinSchreierBoundary_apply, etaleCohomologyRestrictionMap_comp_extClass g hS 0 1 rfl,
    artinSchreierBoundary_apply, h0, additiveRestriction_apply, Sheaf.H.map_apply]
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_
  refine (congrArg (fun z => Ext.comp _ z (zero_add 1)) hnat).trans ?_
  exact (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm

end Naturality

end Stacks.ArtinSchreier

end
