module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.UnitChase
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.LocalProduct

/-!
# Maps out of inverse images of graded algebras into tensor powers, on sections

For a morphism `r : X ⟶ P`, a sheaf of graded algebras `G` on `P` and an invertible `ℒ` on `X`, a
family `Θ_n : r^* G_n ⟶ ℒ^{⊗ n}` is *multiplicative on inverse images* (`UnitMul`) if it carries
the inverse image of a product of homogeneous sections to the product of the values. This file
records how such families compose: with a map of graded algebras `M^* G ⟶ H` along a further
morphism `M` (`comp₂`), with the inverse image along `q : X₁ ⟶ X` and an identification
`q^*ℒ ≅ ℒ₁` (`comp₃`, read through [Stacks, Tag 01CU]'s comparison of tensor powers with inverse
images), and with an equality of morphisms (`congr`); in each case the value on an inverse image of
a section is computed.

## Main definitions

* `UnitMul`: a family `Θ_n : r^* G_n ⟶ ℒ^{⊗ n}` is multiplicative on inverse images of sections.
* `comp₂`: the family `(r ≫ M)^* G_n ⟶ r^* H_n ⟶ ℒ^{⊗ n}` along a map `M^* G ⟶ H`.
* `congrFamily`: transport of a family along an equality of morphisms.
* `polPow`: the comparison `q^* ℒ^{⊗ n} ⟶ ℒ₁^{⊗ n}` induced by `q^* ℒ ≅ ℒ₁`.
* `comp₃`: the family `(q ≫ r)^* G_n ⟶ q^* ℒ^{⊗ n} ⟶ ℒ₁^{⊗ n}`.

## Main results

* `comp₂_unitMul`, `congrFamily_unitMul`, `comp₃_unitMul`: each construction preserves `UnitMul`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE sectionPull)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; with it the
-- arrows below can be elaborated at a quiver structure other than the one of `Scheme.Modules`,
-- which their users then have to unfold to compare.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {X P Q : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- A family `Θ_n : r^* G_n ⟶ ℒ^{⊗ n}` **is multiplicative on inverse images of sections**. -/
def UnitMul (r : X ⟶ P) (G : SheafOfModules.GradedAlgebra.{u, u} P.ringCatSheaf)
    (Θ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (G.piece n) ⟶ tensorPowerModule X L n) : Prop :=
  ∀ (i j : ℤ) (O : P.Opens) (s : Γ(G.piece i, O)) (t : Γ(G.piece j, O)),
    (Θ (i + j)).app (r ⁻¹ᵁ O) (unitApp r (G.piece (i + j)) O ((G.mul i j).app (op O) s t)) =
      Stacks.TensorPowerDivision.localMul L ((Θ i).app (r ⁻¹ᵁ O) (unitApp r (G.piece i) O s))
        ((Θ j).app (r ⁻¹ᵁ O) (unitApp r (G.piece j) O t))

section Comp₂

variable (r : X ⟶ P) (M : P ⟶ Q) {G : SheafOfModules.GradedAlgebra.{u, u} Q.ringCatSheaf}
  {H : SheafOfModules.GradedAlgebra.{u, u} P.ringCatSheaf}
  (Ψ : Stacks.Conormal.gradedPullback M G ⟶ H)
  (Θ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (H.piece n) ⟶ tensorPowerModule X L n)

/-- The family `(r ≫ M)^* G_n ⟶ r^* M^* G_n ⟶ r^* H_n ⟶ ℒ^{⊗ n}`. -/
def comp₂ (n : ℤ) :
    (Scheme.Modules.pullback (r ≫ M)).obj (G.piece n) ⟶ tensorPowerModule X L n :=
  (Scheme.Modules.pullbackComp r M).inv.app (G.piece n) ≫
    (Scheme.Modules.pullback r).map (Ψ.app n) ≫ Θ n

/-- The composite `(f ≫ g)^* F ⟶ f^* g^* F ⟶ f^* N ⟶ T` sends the inverse image of `s` along
`f ≫ g` to `ψ` of the inverse image along `f` of `φ` of the inverse image of `s` along `g`. -/
private theorem pullbackComp_inv_map_comp_unitApp {X₁ Y Z : Scheme.{u}} (f : X₁ ⟶ Y) (g : Y ⟶ Z)
    {F : Z.Modules} {N : Y.Modules} {T : X₁.Modules}
    (φ : (Scheme.Modules.pullback g).obj F ⟶ N) (ψ : (Scheme.Modules.pullback f).obj N ⟶ T)
    (O : Z.Opens) (s : Γ(F, O)) :
    ((Scheme.Modules.pullbackComp f g).inv.app F ≫ (Scheme.Modules.pullback f).map φ ≫ ψ).app
        ((f ≫ g) ⁻¹ᵁ O) (unitApp (f ≫ g) F O s) =
      ψ.app (f ⁻¹ᵁ (g ⁻¹ᵁ O)) (unitApp f N (g ⁻¹ᵁ O)
        (φ.app (g ⁻¹ᵁ O) (unitApp g F O s))) := by
  have e1 := Scheme.Modules.pullbackComp_inv_unit f g F O s
  have e2 := unitApp_naturality f φ (g ⁻¹ᵁ O) (unitApp g F O s)
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  exact (congrArg (fun z => ψ.app (f ⁻¹ᵁ (g ⁻¹ᵁ O))
    (((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ (g ⁻¹ᵁ O)) z)) e1).trans
    (congrArg (fun z => ψ.app (f ⁻¹ᵁ (g ⁻¹ᵁ O)) z) e2)

/-- The value of `comp₂` on the inverse image along `r ≫ M` of a section `s` of `G_n` is the value
of `Θ_n` on the inverse image along `r` of `Ψ_n` applied to the inverse image of `s` along `M`. -/
theorem comp₂_app (n : ℤ) (O : Q.Opens) (s : Γ(G.piece n, O)) :
    (comp₂ L r M Ψ Θ n).app ((r ≫ M) ⁻¹ᵁ O) (unitApp (r ≫ M) (G.piece n) O s) =
      (Θ n).app (r ⁻¹ᵁ (M ⁻¹ᵁ O)) (unitApp r (H.piece n) (M ⁻¹ᵁ O)
        (Scheme.Modules.Hom.app (Ψ.app n) (M ⁻¹ᵁ O) (unitApp M (G.piece n) O s))) := by
  exact pullbackComp_inv_map_comp_unitApp r M (Ψ.app n) (Θ n) O s

/-- If `Ψ_n` sends the inverse image of `s` along `M` to the restriction of a section `y` of `H_n`
over `W`, then `comp₂` sends the inverse image of `s` to the restriction of `Θ_n` of the inverse
image of `y`. -/
theorem comp₂_app_eq (n : ℤ) (O : Q.Opens) (s : Γ(G.piece n, O)) {W : P.Opens}
    (y : Γ(H.piece n, W)) (h1 : M ⁻¹ᵁ O ≤ W)
    (hΨ : Scheme.Modules.Hom.app (Ψ.app n) (M ⁻¹ᵁ O) (unitApp M (G.piece n) O s) =
      (Scheme.Modules.presheaf (X := P) (H.piece n)).map (homOfLE h1).op y) :
    (comp₂ L r M Ψ Θ n).app ((r ≫ M) ⁻¹ᵁ O) (unitApp (r ≫ M) (G.piece n) O s) =
      (tensorPowerModule X L n).presheaf.map (homOfLE (r.preimage_mono h1)).op
        ((Θ n).app (r ⁻¹ᵁ W) (unitApp r (H.piece n) W y)) := by
  rw [comp₂_app, hΨ]
  exact (congrArg (fun z => (Θ n).app (r ⁻¹ᵁ (M ⁻¹ᵁ O)) z)
    (unitApp_map r (H.piece n) h1 y)).trans (hom_app_map (Θ n) (r.preimage_mono h1) _)

/-- If `Θ` is multiplicative on inverse images, then so is `comp₂`. -/
theorem comp₂_unitMul (hΘ : UnitMul L r H Θ) : UnitMul L (r ≫ M) G (comp₂ L r M Ψ Θ) := by
  intro i j O s t
  refine (comp₂_app L r M Ψ Θ (i + j) O _).trans ?_
  rw [comp₂_app L r M Ψ Θ i O s, comp₂_app L r M Ψ Θ j O t]
  have hm := Stacks.AlgebraicGeometry.GradedAlgebraHomSections.app_unitApp_mul M G Ψ i j O s t
  exact (congrArg (fun z => (Θ (i + j)).app (r ⁻¹ᵁ (M ⁻¹ᵁ O))
    (unitApp r (H.piece (i + j)) (M ⁻¹ᵁ O) z)) hm).trans (hΘ i j (M ⁻¹ᵁ O) _ _)

end Comp₂

section Congr

variable {r r' : X ⟶ P} (e : r' = r) {G : SheafOfModules.GradedAlgebra.{u, u} P.ringCatSheaf}
  (Θ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (G.piece n) ⟶ tensorPowerModule X L n)

/-- Transport of a family along an equality of morphisms. -/
def congrFamily (n : ℤ) :
    (Scheme.Modules.pullback r').obj (G.piece n) ⟶ tensorPowerModule X L n :=
  (Scheme.Modules.pullbackCongr e).hom.app (G.piece n) ≫ Θ n

include e in
/-- If `r' = r`, then `r'⁻¹ O ≤ r⁻¹ O`. -/
theorem preimage_le_of_eq (O : P.Opens) : r' ⁻¹ᵁ O ≤ r ⁻¹ᵁ O := by rw [e]

/-- The value of `congrFamily` on the inverse image along `r'` of a section `s` of `G_n` is the
restriction of the value of `Θ_n` on the inverse image of `s` along `r`. -/
theorem congrFamily_app (n : ℤ) (O : P.Opens) (s : Γ(G.piece n, O)) :
    (congrFamily L e Θ n).app (r' ⁻¹ᵁ O) (unitApp r' (G.piece n) O s) =
      (tensorPowerModule X L n).presheaf.map (homOfLE (preimage_le_of_eq e O)).op
        ((Θ n).app (r ⁻¹ᵁ O) (unitApp r (G.piece n) O s)) := by
  subst e
  have h : (Scheme.Modules.pullbackCongr (rfl : r' = r')).hom.app (G.piece n) = 𝟙 _ := rfl
  change (Θ n).app _
    (((Scheme.Modules.pullbackCongr (rfl : r' = r')).hom.app (G.piece n)).app _ _) = _
  rw [h]
  have hid : (homOfLE (preimage_le_of_eq (rfl : r' = r') O)).op = 𝟙 (op (r' ⁻¹ᵁ O)) :=
    Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id]
  rfl

/-- If `Θ` is multiplicative on inverse images, then so is `congrFamily`. -/
theorem congrFamily_unitMul (hΘ : UnitMul L r G Θ) : UnitMul L r' G (congrFamily L e Θ) := by
  intro i j O s t
  refine (congrFamily_app L e Θ (i + j) O _).trans ?_
  rw [congrFamily_app L e Θ i O s, congrFamily_app L e Θ j O t]
  exact (congrArg ((tensorPowerModule X L (i + j)).presheaf.map
    (homOfLE (preimage_le_of_eq e O)).op) (hΘ i j O s t)).trans
    (Stacks.TensorPowerDivision.map_localMul L _ _ _)

end Congr

section Comp₃

variable {X₁ : Scheme.{u}} (q : X₁ ⟶ X) (L₁ : X₁.Modules) [Stacks.Ample.IsInvertibleModule X₁ L₁]
  (ε : (Scheme.Modules.pullback q).obj L ≅ L₁)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Restriction along `W ≤ W` is the identity. -/
theorem val_map_refl {Y : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    (N : SheafOfModules.{u} R) (W : Opens Y) (z : N.val.obj (op W)) :
    N.val.map (homOfLE (le_refl W)).op z = z := by
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, PresheafOfModules.map_id]
  rfl

/-- **The inverse image along `q` of a tensor power, read in the tensor powers of `ℒ₁`**: the
comparison of [Stacks, Tag 01CU] followed by `ε^{⊗ n}`. -/
def polPow (n : ℤ) :
    (Scheme.Modules.pullback q).obj (tensorPowerModule X L n) ⟶ tensorPowerModule X₁ L₁ n :=
  haveI := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X L
  haveI := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  haveI := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁
    ((Scheme.Modules.pullback q).obj L)
  (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L n).hom ≫
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom

/-- The value of `polPow` on the inverse image along `q` of a section `y` of `ℒ^{⊗ n}` over `V` is
`sectionPull` of `y`. -/
theorem polPow_unitApp (n : ℤ) (V : X.Opens) (y : Γ(tensorPowerModule X L n, V)) :
    (polPow L q L₁ ε n).app (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule X L n) V y) =
      sectionPull q L L₁ ε n V (q ⁻¹ᵁ V) le_rfl y := by
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X L
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁
    ((Scheme.Modules.pullback q).obj L)
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull_apply q L L₁ ε n V
    (q ⁻¹ᵁ V) le_rfl y).symm
  refine Eq.trans ?_ (congrArg (fun z =>
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom.val.app
      (op (q ⁻¹ᵁ V)) z) (val_map_refl _ (q ⁻¹ᵁ V) _).symm)
  rfl

/-- `sectionPull` of a restricted section is `sectionPull` from the larger open. -/
theorem sectionPull_map_source (n : ℤ) {W V : X.Opens} (i : W ≤ V) (V' : X₁.Opens)
    (h : V' ≤ q ⁻¹ᵁ W) (y : Γ(tensorPowerModule X L n, V)) :
    sectionPull q L L₁ ε n W V' h ((tensorPowerModule X L n).presheaf.map (homOfLE i).op y) =
      sectionPull q L L₁ ε n V V' (h.trans (q.preimage_mono i)) y := by
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X L
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁
    ((Scheme.Modules.pullback q).obj L)
  have e1 := unitApp_map q (tensorPowerModule X L n) i y
  have e2 := hom_app_map (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L n).hom
    (q.preimage_mono i) (unitApp q (tensorPowerModule X L n) V y)
  have e3 : Scheme.Modules.Hom.app
      (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L n).hom
      (q ⁻¹ᵁ W) (unitApp q (tensorPowerModule X L n) W
        ((tensorPowerModule X L n).presheaf.map (homOfLE i).op y)) =
      (tensorPowerModule X₁ ((Scheme.Modules.pullback q).obj L) n).presheaf.map
        (homOfLE (q.preimage_mono i)).op
        (Scheme.Modules.Hom.app
          (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L n).hom
          (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule X L n) V y)) :=
    (congrArg _ e1).trans e2
  refine (congrArg (fun z => Scheme.Modules.Hom.app
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom V'
      ((tensorPowerModule X₁ ((Scheme.Modules.pullback q).obj L) n).presheaf.map (homOfLE h).op z))
    e3).trans ?_
  exact congrArg (fun z => Scheme.Modules.Hom.app
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom V' z)
    (map_map_homOfLE _ _ _ _ _)

variable (r : X ⟶ P) {G : SheafOfModules.GradedAlgebra.{u, u} P.ringCatSheaf}
  (Θ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (G.piece n) ⟶ tensorPowerModule X L n)

/-- The family `(q ≫ r)^* G_n ⟶ q^* r^* G_n ⟶ q^* ℒ^{⊗ n} ⟶ ℒ₁^{⊗ n}`. -/
def comp₃ (n : ℤ) :
    (Scheme.Modules.pullback (q ≫ r)).obj (G.piece n) ⟶ tensorPowerModule X₁ L₁ n :=
  (Scheme.Modules.pullbackComp q r).inv.app (G.piece n) ≫ (Scheme.Modules.pullback q).map (Θ n) ≫
    polPow L q L₁ ε n

/-- The value of `comp₃` on the inverse image along `q ≫ r` of a section `s` of `G_n` is
`sectionPull` of the value of `Θ_n` on the inverse image of `s` along `r`. -/
theorem comp₃_app (n : ℤ) (O : P.Opens) (s : Γ(G.piece n, O)) :
    (comp₃ L q L₁ ε r Θ n).app ((q ≫ r) ⁻¹ᵁ O) (unitApp (q ≫ r) (G.piece n) O s) =
      sectionPull q L L₁ ε n (r ⁻¹ᵁ O) (q ⁻¹ᵁ (r ⁻¹ᵁ O)) le_rfl
        ((Θ n).app (r ⁻¹ᵁ O) (unitApp r (G.piece n) O s)) := by
  refine (pullbackComp_inv_map_comp_unitApp q r (Θ n) (polPow L q L₁ ε n) O s).trans ?_
  exact polPow_unitApp L q L₁ ε n (r ⁻¹ᵁ O) _

/-- If `Θ` is multiplicative on inverse images, then so is `comp₃`. -/
theorem comp₃_unitMul (hΘ : UnitMul L r G Θ) : UnitMul L₁ (q ≫ r) G (comp₃ L q L₁ ε r Θ) := by
  intro i j O s t
  refine (comp₃_app L q L₁ ε r Θ (i + j) O _).trans ?_
  rw [comp₃_app L q L₁ ε r Θ i O s, comp₃_app L q L₁ ε r Θ j O t]
  exact (congrArg (sectionPull q L L₁ ε (i + j) (r ⁻¹ᵁ O) (q ⁻¹ᵁ (r ⁻¹ᵁ O)) le_rfl)
    (hΘ i j O s t)).trans
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull_mul q L L₁ ε i j _ _ _ _ _)

end Comp₃

end Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections

end
