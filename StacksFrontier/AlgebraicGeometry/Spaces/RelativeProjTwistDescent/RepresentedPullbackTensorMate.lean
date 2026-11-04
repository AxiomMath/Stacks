module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackConjugate
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# The comparison of the two factorizations of the square of a represented morphism

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` and `φ` the morphism of
representable algebraic spaces it represents.  The pullback of modules along the diagonal of the
square of ringed topoi of `g` factors in two ways, and
`AlgebraicGeometry.Space.representedSquareModulePullbackIso` is the comparison of the two
factorizations, read off the comparison of direct images
`AlgebraicGeometry.Space.representedSquareDirectImageIso`.  This file identifies it with the
conjugate, by the comparisons `E_U` of Stacks 04M0, of the comparison
`AlgebraicGeometry.Space.representedModulePullbackIso` of the inverse image of Stacks 03LU along
`φ` with small étale pullback of schemes.

The identification is a computation with mates.  Every isomorphism involved is a comparison of
left adjoints (`CategoryTheory.Adjunction.leftAdjointUniq`), so its conjugate is the comparison of
right adjoints it was transported along.  The generic part, at arbitrary categories, is in the
namespace `Stacks.Mates`: the conjugate of a comparison of two factorizations
(`Stacks.Mates.conjugateEquiv_factorizationIso_hom`) and the passage from the square read with the
inverses of two equivalences to the square read with their functors
(`Stacks.Mates.mateEquiv_eq_of_conjugateEquiv`).  What remains is one identity of comparisons of
direct images, `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`, in which every
factor is a restriction of sections.

## Main definitions

* `Stacks.Mates.RightAdjointSquareCompat`: the identity of comparisons of right adjoints the
  generic statement asks for, and `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`
  its instance at the square of `g`.
* `AlgebraicGeometry.Space.representedModulePullbackIsoConjApp`: the component at `M` of the
  conjugate of `AlgebraicGeometry.Space.representedModulePullbackIso`.

## Main results

* `Stacks.Mates.factorizationIso_hom_app_eq`: **the comparison of two factorizations is the
  conjugate of a square of left adjoints**, at arbitrary categories.
* `AlgebraicGeometry.Space.representedReindexModulePullbackIso_eq`: the comparison of left
  adjoints at the spelling of the square is `AlgebraicGeometry.Space.representedModulePullbackIso`.
* `AlgebraicGeometry.Space.representedSquareModulePullbackIso_hom_app_of_rightAdjointCompat`:
  **the comparison of the two factorizations of the square of `g` is the conjugate of
  `AlgebraicGeometry.Space.representedModulePullbackIso`**, given
  `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`.

## Implementation notes

The categories of modules of the square are spelled at the sides of its morphisms of ringed topoi
(`AlgebraicGeometry.Space.representedReindexEquivalence`): comparing the two spellings of the
category of modules of one scheme inside a statement about conjugates exhausts the elaboration
budget, while retyping each object once costs little.  So every comparison is first written at
that spelling (`AlgebraicGeometry.Space.representedReindexModulePullbackIso`,
`AlgebraicGeometry.Space.representedReindexPushforwardSquareIso`), the conjugate calculus is done
there, and only the last step returns to `AlgebraicGeometry.Space.representedModulePullbackIso`,
by `rfl` (`AlgebraicGeometry.Space.representedReindexModulePullbackIso_eq`).

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Mates

section

variable {C : Type*} {D : Type*} [Category C] [Category D]

/-- Conjugation of the inverse of an isomorphism of left adjoints with known conjugate. -/
theorem conjugateEquiv_hom_eq_of_inv {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (α : L₁ ≅ L₂) (P : R₁ ≅ R₂)
    (h : conjugateEquiv adj₁ adj₂ α.inv = P.hom) :
    conjugateEquiv adj₂ adj₁ α.hom = P.inv := by
  have h1 := conjugateEquiv_comm adj₁ adj₂ (α := α.inv) (β := α.hom) α.hom_inv_id
  rw [h] at h1
  exact (P.eq_inv_comp.2 h1).trans (Category.comp_id _)

/-- The conjugate of a comparison of left adjoints read through an intermediate adjunction. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_trans_hom {L L' L'' : C ⥤ D}
    {R R' : D ⥤ C} (a : L ⊣ R) (e : R ≅ R') (gen : L' ⊣ R') (b : L'' ⊣ R') :
    conjugateEquiv b a (Adjunction.leftAdjointUniq (a.ofNatIsoRight e) gen ≪≫
      Adjunction.leftAdjointUniq gen b).hom = e.inv := by
  rw [Iso.trans_hom, ← conjugateEquiv_comp b gen a,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom gen b,
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom a e gen,
    Category.id_comp]

/-- Conjugation along a composite whose second adjunction is transported. -/
theorem conjugateEquiv_comp_ofNatIsoRight {E : Type*} [Category E] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {L₁ : D ⥤ E} {R₁ R₁' : E ⥤ D} (a : L₁ ⊣ R₁) (μ : R₁ ≅ R₁') {L₂ : C ⥤ E}
    {R₂ : E ⥤ C} (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L ⋙ L₁) :
    conjugateEquiv (adj.comp (a.ofNatIsoRight μ)) adj₂ α =
      Functor.whiskerRight μ.inv R ≫ conjugateEquiv (adj.comp a) adj₂ α := by
  ext d
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp]
  rw [← adj₂.unit_naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, α.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp]
  rw [adj.counit_naturality]

end

section Factorization

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {χs : 𝒵 ⥤ 𝒳} {χr : 𝒳 ⥤ 𝒵} {ψ₁s : 𝒵 ⥤ 𝒴₁} {ψ₁r : 𝒴₁ ⥤ 𝒵} {φ₁s : 𝒴₁ ⥤ 𝒳} {φ₁r : 𝒳 ⥤ 𝒴₁}
  {ψ₂s : 𝒵 ⥤ 𝒴₂} {ψ₂r : 𝒴₂ ⥤ 𝒵} {φ₂s : 𝒴₂ ⥤ 𝒳} {φ₂r : 𝒳 ⥤ 𝒴₂}
  (aχ : χs ⊣ χr) (aψ₁ : ψ₁s ⊣ ψ₁r) (aφ₁ : φ₁s ⊣ φ₁r) (aψ₂ : ψ₂s ⊣ ψ₂r) (aφ₂ : φ₂s ⊣ φ₂r)
  (c₁ : χs ≅ ψ₁s ⋙ φ₁s) (c₂ : χs ≅ ψ₂s ⋙ φ₂s) (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (τ₂ : φ₂r ⋙ ψ₂r ≅ χr)
  {Lψ₁ : 𝒵 ⥤ 𝒴₁} {Rψ₁ : 𝒴₁ ⥤ 𝒵} {Lφ₁ : 𝒴₁ ⥤ 𝒳} {Rφ₁ : 𝒳 ⥤ 𝒴₁}
  {Lψ₂ : 𝒵 ⥤ 𝒴₂} {Rψ₂ : 𝒴₂ ⥤ 𝒵}
  (bψ₁ : Lψ₁ ⊣ Rψ₁) (bφ₁ : Lφ₁ ⊣ Rφ₁) (bψ₂ : Lψ₂ ⊣ Rψ₂)
  (αψ₁ : ψ₁s ≅ Lψ₁) (αφ₁ : φ₁s ≅ Lφ₁) (αψ₂ : ψ₂s ≅ Lψ₂)
  (Pψ₁ : ψ₁r ≅ Rψ₁) (Pφ₁ : φ₁r ≅ Rφ₁) (Pψ₂ : ψ₂r ≅ Rψ₂)

/-- The conjugate of the comparison of two factorizations. -/
theorem conjugateEquiv_factorizationIso_hom
    (hc₁ : conjugateEquiv (aψ₁.comp aφ₁) aχ c₁.hom = τ₁.hom)
    (hc₂ : conjugateEquiv (aψ₂.comp aφ₂) aχ c₂.hom = τ₂.hom)
    (hψ₁ : conjugateEquiv bψ₁ aψ₁ αψ₁.hom = Pψ₁.inv)
    (hφ₁ : conjugateEquiv bφ₁ aφ₁ αφ₁.hom = Pφ₁.inv)
    (hψ₂ : conjugateEquiv bψ₂ aψ₂ αψ₂.hom = Pψ₂.inv) :
    conjugateEquiv (bψ₂.comp aφ₂) (bψ₁.comp bφ₁)
        (Functor.isoWhiskerLeft Lψ₁ αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s).hom =
      Functor.whiskerLeft φ₂r Pψ₂.inv ≫ τ₂.hom ≫ τ₁.inv ≫ Functor.whiskerLeft φ₁r Pψ₁.hom ≫
        Functor.whiskerRight Pφ₁.hom Rψ₁ := by
  have h₅ := conjugateEquiv_whiskerRight bψ₂ aψ₂ aφ₂ αψ₂.hom
  rw [hψ₂] at h₅
  have h₃ := conjugateEquiv_hom_eq_of_inv (aψ₁.comp aφ₁) aχ c₁.symm τ₁ hc₁
  have h₂ := conjugateEquiv_whiskerRight aψ₁ bψ₁ aφ₁ αψ₁.symm.hom
  rw [conjugateEquiv_hom_eq_of_inv bψ₁ aψ₁ αψ₁.symm Pψ₁.symm hψ₁] at h₂
  have h₁ := conjugateEquiv_whiskerLeft aφ₁ bφ₁ bψ₁ αφ₁.symm.hom
  rw [conjugateEquiv_hom_eq_of_inv bφ₁ aφ₁ αφ₁.symm Pφ₁.symm hφ₁] at h₁
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ (bψ₁.comp aφ₁), ← conjugateEquiv_comp _ (aψ₁.comp aφ₁),
    ← conjugateEquiv_comp _ aχ, ← conjugateEquiv_comp _ (aψ₂.comp aφ₂),
    h₅, hc₂, h₃, h₂, h₁]
  simp only [Category.assoc, Iso.symm_inv]

end Factorization

section Square

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {pb : 𝒵 ⥤ 𝒴₁} {pbr : 𝒴₁ ⥤ 𝒵} {φs : 𝒴₂ ⥤ 𝒳} {φr : 𝒳 ⥤ 𝒴₂}
  (aPb : pb ⊣ pbr) (aφ : φs ⊣ φr) (E : 𝒵 ≌ 𝒴₂) (E' : 𝒴₁ ≌ 𝒳)

/-- The square of left adjoints read with the functors of two equivalences, from the square read
with their inverses. -/
theorem mateEquiv_eq_of_conjugateEquiv (θ : pb ⋙ E'.functor ⟶ E.functor ⋙ φs)
    (ρ : φs ⋙ E'.inverse ≅ E.inverse ⋙ pb) (Sg : pbr ⋙ E.functor ≅ E'.functor ⋙ φr)
    (hρ : conjugateEquiv (E.symm.toAdjunction.comp aPb) (aφ.comp E'.symm.toAdjunction) ρ.hom =
      Sg.hom)
    (hθ : conjugateEquiv (E.toAdjunction.comp aφ) (aPb.comp E'.toAdjunction) θ =
      (mateEquiv E'.symm.toAdjunction E.symm.toAdjunction).symm Sg.inv) :
    mateEquiv E.toAdjunction E'.toAdjunction θ = ρ.inv := by
  have h₁ := iterated_mateEquiv_conjugateEquiv E.toAdjunction E'.toAdjunction aPb aφ θ
  have h₂ := iterated_mateEquiv_conjugateEquiv aφ aPb E.symm.toAdjunction E'.symm.toAdjunction
    ρ.inv
  have hρ' := conjugateEquiv_hom_eq_of_inv _ _ ρ.symm Sg hρ
  exact (mateEquiv aφ aPb).injective ((h₁.trans hθ).trans
    ((mateEquiv E'.symm.toAdjunction E.symm.toAdjunction).symm_apply_eq.2 (h₂.trans hρ').symm))

/-- The components of the square read with the functors of the equivalences. -/
theorem app_eq_of_mateEquiv_eq (θ : pb ⋙ E'.functor ⟶ E.functor ⋙ φs)
    (ρ : φs ⋙ E'.inverse ≅ E.inverse ⋙ pb)
    (h : mateEquiv E.toAdjunction E'.toAdjunction θ = ρ.inv) (M : 𝒵) :
    θ.app M = E'.functor.map (pb.map (E.unit.app M)) ≫
      E'.functor.map (ρ.inv.app (E.functor.obj M)) ≫ E'.counit.app (φs.obj (E.functor.obj M)) := by
  obtain rfl : θ = (mateEquiv E.toAdjunction E'.toAdjunction).symm ρ.inv :=
    (mateEquiv E.toAdjunction E'.toAdjunction).eq_symm_apply.2 h
  simp [mateEquiv]

/-- The components of the inverse mate of an isomorphism of right adjoints. -/
theorem mateEquiv_symm_app_eq (Sg : pbr ⋙ E.functor ≅ E'.functor ⋙ φr) (N : 𝒳) :
    ((mateEquiv E'.symm.toAdjunction E.symm.toAdjunction).symm Sg.inv).app N =
      E.inverse.map (φr.map (E'.counitIso.inv.app N)) ≫
        E.inverse.map (Sg.inv.app (E'.inverse.obj N)) ≫
          E.unitIso.inv.app (pbr.obj (E'.inverse.obj N)) := by
  simp [mateEquiv]

end Square

section Combined

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {χs : 𝒵 ⥤ 𝒳} {χr : 𝒳 ⥤ 𝒵} {ψ₁s : 𝒵 ⥤ 𝒴₁} {ψ₁r : 𝒴₁ ⥤ 𝒵} {φ₁s : 𝒴₁ ⥤ 𝒳} {φ₁r : 𝒳 ⥤ 𝒴₁}
  {ψ₂s : 𝒵 ⥤ 𝒴₂} {ψ₂r : 𝒴₂ ⥤ 𝒵} {φ₂s : 𝒴₂ ⥤ 𝒳} {φ₂r φr : 𝒳 ⥤ 𝒴₂}
  {pb : 𝒵 ⥤ 𝒴₁} {pbr : 𝒴₁ ⥤ 𝒵}
  (aχ : χs ⊣ χr) (aψ₁ : ψ₁s ⊣ ψ₁r) (aφ₁ : φ₁s ⊣ φ₁r) (aψ₂ : ψ₂s ⊣ ψ₂r) (aφ₂ : φ₂s ⊣ φ₂r)
  (aPb : pb ⊣ pbr) (E : 𝒵 ≌ 𝒴₂) (E' : 𝒴₁ ≌ 𝒳) (μ : φ₂r ≅ φr)
  (c₁ : χs ≅ ψ₁s ⋙ φ₁s) (c₂ : χs ≅ ψ₂s ⋙ φ₂s) (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (τ₂ : φ₂r ⋙ ψ₂r ≅ χr)
  (αψ₁ : ψ₁s ≅ pb) (αφ₁ : φ₁s ≅ E'.functor) (αψ₂ : ψ₂s ≅ E.functor)
  (Pψ₁ : ψ₁r ≅ pbr) (Pφ₁ : φ₁r ≅ E'.inverse) (Pψ₂ : ψ₂r ≅ E.inverse)
  (ρ : φ₂s ⋙ E'.inverse ≅ E.inverse ⋙ pb) (Sg : pbr ⋙ E.functor ≅ E'.functor ⋙ φr)

/-- The identity between the comparisons of right adjoints that
`Stacks.Mates.factorizationIso_hom_app_eq` asks for: the comparison `τ₂ ≪≫ τ₁⁻¹` of the two
factorizations on direct images, read through the identifications `P` and `μ` of the right
adjoints, is the square `Sg` of right adjoints conjugated by the two equivalences. -/
def RightAdjointSquareCompat : Prop :=
  ∀ N : 𝒳, E.inverse.map (μ.inv.app N) ≫ Pψ₂.inv.app (φ₂r.obj N) ≫ τ₂.hom.app N ≫
      τ₁.inv.app N ≫ Pψ₁.hom.app (φ₁r.obj N) ≫ pbr.map (Pφ₁.hom.app N) =
    E.inverse.map (φr.map (E'.counitIso.inv.app N)) ≫
      E.inverse.map (Sg.inv.app (E'.inverse.obj N)) ≫
        E.unitIso.inv.app (pbr.obj (E'.inverse.obj N))

/-- The conjugate of the comparison of two factorizations, once the comparisons of right adjoints
that the two are built from agree. -/
theorem conjugateEquiv_factorizationIso_hom_eq
    (hc₁ : conjugateEquiv (aψ₁.comp aφ₁) aχ c₁.hom = τ₁.hom)
    (hc₂ : conjugateEquiv (aψ₂.comp aφ₂) aχ c₂.hom = τ₂.hom)
    (hψ₁ : conjugateEquiv aPb aψ₁ αψ₁.hom = Pψ₁.inv)
    (hφ₁ : conjugateEquiv E'.toAdjunction aφ₁ αφ₁.hom = Pφ₁.inv)
    (hψ₂ : conjugateEquiv E.toAdjunction aψ₂ αψ₂.hom = Pψ₂.inv)
    (H : RightAdjointSquareCompat E E' μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂ Sg) :
    conjugateEquiv (E.toAdjunction.comp (aφ₂.ofNatIsoRight μ)) (aPb.comp E'.toAdjunction)
        (Functor.isoWhiskerLeft pb αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s).hom =
      (mateEquiv E'.symm.toAdjunction E.symm.toAdjunction).symm Sg.inv := by
  rw [conjugateEquiv_comp_ofNatIsoRight,
    conjugateEquiv_factorizationIso_hom aχ aψ₁ aφ₁ aψ₂ aφ₂ c₁ c₂ τ₁ τ₂ aPb E'.toAdjunction
      E.toAdjunction αψ₁ αφ₁ αψ₂ Pψ₁ Pφ₁ Pψ₂ hc₁ hc₂ hψ₁ hφ₁ hψ₂]
  ext N
  rw [mateEquiv_symm_app_eq]
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using H N

/-- **The comparison of two factorizations is the conjugate of a square of left adjoints**, once
the comparisons of right adjoints that the two are built from agree. -/
theorem factorizationIso_hom_app_eq
    (hc₁ : conjugateEquiv (aψ₁.comp aφ₁) aχ c₁.hom = τ₁.hom)
    (hc₂ : conjugateEquiv (aψ₂.comp aφ₂) aχ c₂.hom = τ₂.hom)
    (hψ₁ : conjugateEquiv aPb aψ₁ αψ₁.hom = Pψ₁.inv)
    (hφ₁ : conjugateEquiv E'.toAdjunction aφ₁ αφ₁.hom = Pφ₁.inv)
    (hψ₂ : conjugateEquiv E.toAdjunction aψ₂ αψ₂.hom = Pψ₂.inv)
    (hρ : conjugateEquiv (E.symm.toAdjunction.comp aPb)
      ((aφ₂.ofNatIsoRight μ).comp E'.symm.toAdjunction) ρ.hom = Sg.hom)
    (H : RightAdjointSquareCompat E E' μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂ Sg)
    (M : 𝒵) :
    (Functor.isoWhiskerLeft pb αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s).hom.app M =
      E'.functor.map (pb.map (E.unit.app M)) ≫
        E'.functor.map (ρ.inv.app (E.functor.obj M)) ≫
          E'.counit.app (φ₂s.obj (E.functor.obj M)) :=
  app_eq_of_mateEquiv_eq E E' _ ρ
    (mateEquiv_eq_of_conjugateEquiv aPb (aφ₂.ofNatIsoRight μ) E E' _ ρ Sg hρ
      (conjugateEquiv_factorizationIso_hom_eq aχ aψ₁ aφ₁ aψ₂ aφ₂ aPb E E' μ c₁ c₂ τ₁ τ₂ αψ₁ αφ₁
        αψ₂ Pψ₁ Pφ₁ Pψ₂ Sg hc₁ hc₂ hψ₁ hφ₁ hψ₂ H)) M

end Combined

end Stacks.Mates

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The comparison of the two direct images round the square of `g`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, with the categories of modules
spelled as the sides of the morphisms of ringed topoi of the square and the direct image along
base change of schemes written as that of the morphism of ringed sites of Stacks 070R (2). -/
noncomputable abbrev representedReindexPushforwardSquareIso :
    @Iso ((_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).toRingedTopos.O)) ⥤
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O))) _
    ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pushforwardTopos ⋙
      (representedReindexEquivalence B S hS T).functor)
    ((representedReindexEquivalence B S hS T').functor ⋙
      modulePushforward B S hS (representedSpaceMap B S hS g)) :=
  representedModulePushforwardSquareIso B S hS g hg

/-- `AlgebraicGeometry.Space.representedModulePullbackIso` with the categories of modules spelled
as the sides of the morphisms of ringed topoi of the square of `g`: the comparison of the two left
adjoints of `E_{T'} ⋙ φ_*`, the pullback along base change of schemes being that of the morphism of
ringed sites of Stacks 070R (2). -/
noncomputable abbrev representedReindexModulePullbackIso :=
  Adjunction.leftAdjointUniq
    (((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))).ofNatIsoRight
        (modulePushforwardIso B S hS (representedSpaceMap B S hS g))).comp
      (representedReindexEquivalence B S hS T').symm.toAdjunction)
    (((representedReindexEquivalence B S hS T).symm.toAdjunction.comp
        (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
          g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral).ofNatIsoRight
      (representedReindexPushforwardSquareIso B S hS g hg))

/-- The conjugate of `AlgebraicGeometry.Space.representedReindexModulePullbackIso` is the
comparison of direct images it was transported along. -/
theorem conjugateEquiv_representedReindexModulePullbackIso_hom :
    conjugateEquiv
      ((representedReindexEquivalence B S hS T).symm.toAdjunction.comp
        (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
          g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral)
      (((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))).ofNatIsoRight
        (modulePushforwardIso B S hS (representedSpaceMap B S hS g))).comp
      (representedReindexEquivalence B S hS T').symm.toAdjunction)
      (representedReindexModulePullbackIso B S hS g hg).hom =
    (representedReindexPushforwardSquareIso B S hS g hg).hom :=
  Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The conjugate of the comparison of pullbacks along the scheme route of the square. -/
theorem conjugateEquiv_representedSchemeRoutePullbackCompIso_hom :
    conjugateEquiv ((pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS g)).comp
        (pullbackAdjPushforwardModules (representedReindexHom B S hS T')))
      (pullbackAdjPushforwardModules (representedSquareHom B S hS g))
      (representedSchemeRoutePullbackCompIso B S hS g).hom =
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)).hom :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The conjugate of the comparison of pullbacks along the space route of the square. -/
theorem conjugateEquiv_representedSpaceRoutePullbackCompIso_hom :
    conjugateEquiv ((pullbackAdjPushforwardModules (representedReindexHom B S hS T)).comp
        (pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))))
      (pullbackAdjPushforwardModules (representedSquareHom B S hS g))
      (representedSpaceRoutePullbackCompIso B S hS g hg).hom =
    (pushforwardModulesCompIso
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)).hom :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- `AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso` with its target written as the
pullback along the morphism of ringed sites of Stacks 070R (2). -/
noncomputable abbrev representedSchemeBaseChangePullbackIso :
    (representedSchemeBaseChangeHom B S hS g).pullbackModules ≅
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackToposGeneral :=
  SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left

/-- The direct image of modules along base change of schemes is that along the morphism of
ringed sites of Stacks 070R (2)
(`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`). -/
noncomputable abbrev representedSchemeBaseChangePushforwardIso :
    pushforwardModules.{u, u, u, u + 1, u, u + 1} (representedSchemeBaseChangeHom B S hS g) ≅
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pushforwardTopos :=
  (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).pushforwardModulesToposIsoGeneral

/-- The conjugate of the identification of the pullback along base change of schemes. -/
theorem conjugateEquiv_pullbackModulesBaseChangeIso_hom :
    conjugateEquiv
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS g))
      (representedSchemeBaseChangePullbackIso B S hS g).hom =
    (representedSchemeBaseChangePushforwardIso B S hS g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS g))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).pushforwardModulesToposIsoGeneral
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral

/-- The conjugate of the identification of the pullback along the reindexing of `U`. -/
theorem conjugateEquiv_representedReindexPullbackIso_hom (U : BigFppfOver B S hS) :
    conjugateEquiv (representedReindexEquivalence B S hS U).toAdjunction
      (pullbackAdjPushforwardModules (representedReindexHom B S hS U))
      (representedReindexPullbackIso B S hS U).hom =
    (representedReindexPushforwardIso B S hS U).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The identity of comparisons of right adjoints round the square of `g` that
`Stacks.Mates.factorizationIso_hom_app_eq` asks for: the comparison of direct images
`AlgebraicGeometry.Space.representedSquareDirectImageIso` of the space route, followed by the
trivial comparison of the scheme route, is the square of direct images
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` conjugated by the comparisons of
Stacks 04M0.  Every factor is a restriction of sections. -/
abbrev RepresentedSquareRightAdjointCompat : Prop :=
  Stacks.Mates.RightAdjointSquareCompat (representedReindexEquivalence B S hS T)
      (representedReindexEquivalence B S hS T')
      (modulePushforwardIso B S hS (representedSpaceMap B S hS g))
      (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g))
      (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg))
      (representedSchemeBaseChangePushforwardIso B S hS g)
      (representedReindexPushforwardIso B S hS T') (representedReindexPushforwardIso B S hS T)
      (representedReindexPushforwardSquareIso B S hS g hg)

/-- `AlgebraicGeometry.Space.representedSquareModulePullbackIso` written out at the sides of the
morphisms of ringed topoi of the square of `g`. -/
noncomputable abbrev representedSquareFactorizationIso :=
  Functor.isoWhiskerLeft
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackToposGeneral
      (representedReindexPullbackIso B S hS T').symm ≪≫
    Functor.isoWhiskerRight (representedSchemeBaseChangePullbackIso B S hS g).symm
      (representedReindexHom B S hS T').pullbackModules ≪≫
    (representedSchemeRoutePullbackCompIso B S hS g).symm ≪≫
    representedSpaceRoutePullbackCompIso B S hS g hg ≪≫
    Functor.isoWhiskerRight (representedReindexPullbackIso B S hS T)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)).pullbackModules

/-- The conjugate of `AlgebraicGeometry.Space.representedSquareFactorizationIso`, given the
identity `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat` of right adjoints. -/
theorem conjugateEquiv_representedSquareFactorizationIso_hom
    (H : RepresentedSquareRightAdjointCompat B S hS g hg) :
    conjugateEquiv ((representedReindexEquivalence B S hS T).toAdjunction.comp
        ((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))).ofNatIsoRight
          (modulePushforwardIso B S hS (representedSpaceMap B S hS g))))
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
          g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral.comp
        (representedReindexEquivalence B S hS T').toAdjunction)
      (representedSquareFactorizationIso B S hS g hg).hom =
    (mateEquiv (representedReindexEquivalence B S hS T').symm.toAdjunction
      (representedReindexEquivalence B S hS T).symm.toAdjunction).symm
      (representedReindexPushforwardSquareIso B S hS g hg).inv :=
  Stacks.Mates.conjugateEquiv_factorizationIso_hom_eq
    (pullbackAdjPushforwardModules (representedSquareHom B S hS g))
    (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS g))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T'))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T))
    (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T')
    (modulePushforwardIso B S hS (representedSpaceMap B S hS g))
    (representedSchemeRoutePullbackCompIso B S hS g)
    (representedSpaceRoutePullbackCompIso B S hS g hg)
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g))
    (pushforwardModulesCompIso
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg))
    (representedSchemeBaseChangePullbackIso B S hS g)
    (representedReindexPullbackIso B S hS T') (representedReindexPullbackIso B S hS T)
    (representedSchemeBaseChangePushforwardIso B S hS g)
    (representedReindexPushforwardIso B S hS T') (representedReindexPushforwardIso B S hS T)
    (representedReindexPushforwardSquareIso B S hS g hg)
    (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS g)
    (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS g hg)
    (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS g)
    (conjugateEquiv_representedReindexPullbackIso_hom B S hS T')
    (conjugateEquiv_representedReindexPullbackIso_hom B S hS T)
    H

/-- The mate of `AlgebraicGeometry.Space.representedSquareFactorizationIso` with respect to the
two comparisons of Stacks 04M0 is the inverse of
`AlgebraicGeometry.Space.representedReindexModulePullbackIso`. -/
theorem mateEquiv_representedSquareFactorizationIso_hom
    (H : RepresentedSquareRightAdjointCompat B S hS g hg) :
    mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
        (representedReindexEquivalence B S hS T').toAdjunction
        (representedSquareFactorizationIso B S hS g hg).hom =
      (representedReindexModulePullbackIso B S hS g hg).inv :=
  Stacks.Mates.mateEquiv_eq_of_conjugateEquiv
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      g.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))).ofNatIsoRight
      (modulePushforwardIso B S hS (representedSpaceMap B S hS g)))
    (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T') _
    (representedReindexModulePullbackIso B S hS g hg)
    (representedReindexPushforwardSquareIso B S hS g hg)
    (conjugateEquiv_representedReindexModulePullbackIso_hom B S hS g hg)
    (conjugateEquiv_representedSquareFactorizationIso_hom B S hS g hg H)

/-- The components of `AlgebraicGeometry.Space.representedSquareFactorizationIso`. -/
theorem representedSquareFactorizationIso_hom_app
    (H : RepresentedSquareRightAdjointCompat B S hS g hg)
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O))) :
    (representedSquareFactorizationIso B S hS g hg).hom.app M =
      (representedReindexEquivalence B S hS T').functor.map
          ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
            g.left).toRingedToposSiteHom.pullbackToposGeneral.map
            ((representedReindexEquivalence B S hS T).unit.app M)) ≫
        (representedReindexEquivalence B S hS T').functor.map
          ((representedReindexModulePullbackIso B S hS g hg).inv.app
            ((representedReindexEquivalence B S hS T).functor.obj M)) ≫
          (representedReindexEquivalence B S hS T').counit.app
            ((smallEtaleRingedToposModulesHom B S hS
              (representedSpaceMap B S hS g)).pullbackModules.obj
              ((representedReindexEquivalence B S hS T).functor.obj M)) :=
  Stacks.Mates.app_eq_of_mateEquiv_eq (representedReindexEquivalence B S hS T)
    (representedReindexEquivalence B S hS T') _ (representedReindexModulePullbackIso B S hS g hg)
    (mateEquiv_representedSquareFactorizationIso_hom B S hS g hg H) M

/-- `AlgebraicGeometry.Space.representedSquareModulePullbackIso` is
`AlgebraicGeometry.Space.representedSquareFactorizationIso`, componentwise. -/
theorem representedSquareModulePullbackIso_hom_app_eq
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O))) :
    (representedSquareModulePullbackIso B S hS g hg).hom.app M =
      (representedSquareFactorizationIso B S hS g hg).hom.app M :=
  rfl

/-- `AlgebraicGeometry.Space.representedReindexModulePullbackIso` *is*
`AlgebraicGeometry.Space.representedModulePullbackIso`: the two are the same comparison of left
adjoints, written at two spellings of the categories of modules. -/
theorem representedReindexModulePullbackIso_eq :
    representedReindexModulePullbackIso B S hS g hg = representedModulePullbackIso B S hS g hg :=
  rfl

/-- The component at `M` of the conjugate, by the comparisons of Stacks 04M0, of the comparison
`AlgebraicGeometry.Space.representedModulePullbackIso`:
`E_{T'}(g^*(η_M)) ≫ E_{T'}(ρ⁻¹_{E_T M}) ≫ ε_{φ^* E_T M}`. -/
noncomputable abbrev representedModulePullbackIsoConjApp
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O))) :=
  (representedReindexEquivalence B S hS T').functor.map
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackToposGeneral.map
        ((representedReindexEquivalence B S hS T).unit.app M)) ≫
    (representedReindexEquivalence B S hS T').functor.map
      ((representedModulePullbackIso B S hS g hg).inv.app
        ((representedReindexEquivalence B S hS T).functor.obj M)) ≫
      (representedReindexEquivalence B S hS T').counit.app
        ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS g)).pullbackModules.obj
          ((representedReindexEquivalence B S hS T).functor.obj M))

/-- `AlgebraicGeometry.Space.representedSquareFactorizationIso_hom_app` read through
`AlgebraicGeometry.Space.representedReindexModulePullbackIso_eq`. -/
theorem representedSquareFactorizationIso_hom_app_eq_conjApp
    (H : RepresentedSquareRightAdjointCompat B S hS g hg)
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O))) :
    (representedSquareFactorizationIso B S hS g hg).hom.app M =
      (representedReindexEquivalence B S hS T').functor.map
          ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
            g.left).toRingedToposSiteHom.pullbackToposGeneral.map
            ((representedReindexEquivalence B S hS T).unit.app M)) ≫
        (representedReindexEquivalence B S hS T').functor.map
          ((representedModulePullbackIso B S hS g hg).inv.app
            ((representedReindexEquivalence B S hS T).functor.obj M)) ≫
          (representedReindexEquivalence B S hS T').counit.app
            ((smallEtaleRingedToposModulesHom B S hS
              (representedSpaceMap B S hS g)).pullbackModules.obj
              ((representedReindexEquivalence B S hS T).functor.obj M)) := by
  rw [← representedReindexModulePullbackIso_eq]
  exact representedSquareFactorizationIso_hom_app B S hS g hg H M

/-- **The comparison of the two factorizations of the square of `g` is the conjugate, by the
comparisons of Stacks 04M0, of the comparison of Stacks 03LU with small étale pullback of
schemes**, once the two comparisons of direct images round the square agree
(`AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`).  For `M` on the small étale site
of the scheme underlying `T`, the component of
`AlgebraicGeometry.Space.representedSquareModulePullbackIso` at `M` is
`E_{T'}(g^*(η_M)) ≫ E_{T'}(ρ⁻¹_{E_T M}) ≫ ε_{φ^* E_T M}`, with `ρ` the comparison
`AlgebraicGeometry.Space.representedModulePullbackIso`, `η` the unit of `E_T` and `ε` the counit of
`E_{T'}`. -/
theorem representedSquareModulePullbackIso_hom_app_of_rightAdjointCompat
    (H : RepresentedSquareRightAdjointCompat B S hS g hg)
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O))) :
    (representedSquareModulePullbackIso B S hS g hg).hom.app M =
      (representedReindexEquivalence B S hS T').functor.map
          ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
            g.left).toRingedToposSiteHom.pullbackToposGeneral.map
            ((representedReindexEquivalence B S hS T).unit.app M)) ≫
        (representedReindexEquivalence B S hS T').functor.map
          ((representedModulePullbackIso B S hS g hg).inv.app
            ((representedReindexEquivalence B S hS T).functor.obj M)) ≫
          (representedReindexEquivalence B S hS T').counit.app
            ((smallEtaleRingedToposModulesHom B S hS
              (representedSpaceMap B S hS g)).pullbackModules.obj
              ((representedReindexEquivalence B S hS T).functor.obj M)) :=
  (representedSquareModulePullbackIso_hom_app_eq B S hS g hg M).trans
    (representedSquareFactorizationIso_hom_app_eq_conjApp B S hS g hg H M)

end AlgebraicGeometry.Space

end
