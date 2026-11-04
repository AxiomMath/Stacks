module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverPullbackFiber
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SieveDescentDatum

/-!
# The gluing isomorphism of a descent datum of `ℋ_d`, in fibre-product coordinates

A descent datum of the category `ℋ_d` of degree-`d` finite locally free covers relative to a
sieve `R` on `U` attaches to each arrow `f : V ⟶ U` of `R` a cover `Z_f ⟶ V` and, to each object
`Z` of the site mapping into two of the sources compatibly over `U`, an isomorphism between the
*chosen* pullbacks of the two covers.  This file expresses those isomorphisms between the fibre
products of the covers, which are the chosen pullbacks by
`AlgebraicGeometry.Stack.pullbackFiberIsoPointObj`, and as isomorphisms of the covering objects
*over* `Z`, and proves the cocycle condition in these coordinates.

## Main definitions

* `AlgebraicGeometry.Stack.datumCoverIso`: the gluing isomorphism between the two
  fibre-product covers of `Z`, as an isomorphism of the fibre of `ℋ_d` over `Z`.
* `AlgebraicGeometry.Stack.datumGluing`: the same, as an isomorphism of the two
  covering objects of the site.

## Main results

* `AlgebraicGeometry.Stack.datumCoverIso_trans` and
  `AlgebraicGeometry.Stack.datumGluing_trans`: **the cocycle condition in
  fibre-product coordinates.**
* `AlgebraicGeometry.Stack.datumCoverIso_self` and
  `AlgebraicGeometry.Stack.datumGluing_self`: the gluing isomorphism of an arrow
  with itself along one and the same morphism is the identity.
* `AlgebraicGeometry.Stack.datumGluing_hom_comp_snd` and
  `AlgebraicGeometry.Stack.datumGluing_inv_comp_snd`: the gluing isomorphism is an
  isomorphism *over* `Z`, that is it commutes with the two structure morphisms.

## References

* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 026C](https://stacks.math.columbia.edu/tag/026C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] finiteCoverPointObj finiteCoverProjection
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {U : BigFppfOver B S hS} {R : Sieve U}

variable (D : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).SieveDescentDatum R)

/-- **The gluing isomorphism of a descent datum of `ℋ_d` between the two fibre-product covers.**
The datum's isomorphism is between the chosen pullbacks; conjugating it by
`AlgebraicGeometry.Stack.pullbackFiberIsoPointObj` at each end puts it between the fibre products
of the two covers along `ε` and `ε'`. -/
def datumCoverIso ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    fiberPointObj (D.obj f hf) ε ≅ fiberPointObj (D.obj g hg) ε' :=
  (pullbackFiberIsoPointObj (D.obj f hf) ε).symm ≪≫ D.iso hf hg ε ε' heq ≪≫
    pullbackFiberIsoPointObj (D.obj g hg) ε'

/-- **The cocycle condition between the fibre-product covers.** -/
theorem datumCoverIso_trans ⦃V W X Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) ⦃h : X ⟶ U⦄ (hh : R h) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (datumCoverIso D hf hg ε₁ ε₂ h₁₂).hom ≫ (datumCoverIso D hg hh ε₂ ε₃ h₂₃).hom =
      (datumCoverIso D hf hh ε₁ ε₃ h₁₃).hom := by
  simp only [datumCoverIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃, Category.assoc]

/-- The gluing isomorphism between the fibre-product covers of an arrow with itself along one and
the same morphism into its source is the identity. -/
@[simp]
theorem datumCoverIso_self ⦃V Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V)
    (heq : ε ≫ f = ε ≫ f) : (datumCoverIso D hf hf ε ε heq).hom = 𝟙 _ := by
  simp only [datumCoverIso, Iso.trans_hom, Iso.symm_hom, Functor.SieveDescentDatum.iso_self D,
    Category.id_comp, Iso.inv_hom_id]

/-- **The gluing isomorphism of a descent datum of `ℋ_d`, as an isomorphism of the two covering
objects of the site.** This is the cover component of
`AlgebraicGeometry.Stack.datumCoverIso`. -/
def datumGluing ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullback (fiberCoverHom (D.obj f hf)) ε ≅ pullback (fiberCoverHom (D.obj g hg)) ε' where
  hom := (datumCoverIso D hf hg ε ε' heq).hom.1.g
  inv := (datumCoverIso D hf hg ε ε' heq).inv.1.g
  hom_inv_id := congrArg (fun m => (Subtype.val m).g) (datumCoverIso D hf hg ε ε' heq).hom_inv_id
  inv_hom_id := congrArg (fun m => (Subtype.val m).g) (datumCoverIso D hf hg ε ε' heq).inv_hom_id

/-- The forward map of `AlgebraicGeometry.Stack.datumGluing` is the cover component of the forward
map of `AlgebraicGeometry.Stack.datumCoverIso`. -/
@[simp]
theorem datumGluing_hom ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (datumGluing D hf hg ε ε' heq).hom = (datumCoverIso D hf hg ε ε' heq).hom.1.g :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.datumGluing` is the cover component of the inverse of
`AlgebraicGeometry.Stack.datumCoverIso`. -/
@[simp]
theorem datumGluing_inv ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (datumGluing D hf hg ε ε' heq).inv = (datumCoverIso D hf hg ε ε' heq).inv.1.g :=
  rfl

/-- The base component of a morphism of `ℋ_d` between two fibre-product covers of `Z` lying over
the identity of `Z` is the identity. -/
theorem fiberPointObj_hom_f_eq_id ⦃V W Z : BigFppfOver B S hS⦄
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber V)
    (y : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber W)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (m : fiberPointObj x ε ⟶ fiberPointObj y ε') :
    (Subtype.val m).f = 𝟙 Z := by
  have := m.2
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    (a := Subtype.val (fiberPointObj x ε)) (b := Subtype.val (fiberPointObj y ε'))
    (𝟙 Z) (Subtype.val m)).symm

/-- The cover component of a morphism between fibre-product covers of `Z` commutes with the two
structure morphisms to `Z`. -/
private theorem cover_hom_g_comp_snd ⦃V W Z : BigFppfOver B S hS⦄
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber V)
    (y : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber W)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (m : fiberPointObj x ε ⟶ fiberPointObj y ε') :
    (Subtype.val m).g ≫ pullback.snd (fiberCoverHom y) ε' = pullback.snd (fiberCoverHom x) ε := by
  have hw := (Subtype.val m).square.w
  simp only [fiberPointObj_hom_f_eq_id x y ε ε' m] at hw
  exact hw

/-- **The gluing isomorphism is an isomorphism over `Z`.** It carries the structure morphism of
the fibre product along `ε'` back to the structure morphism of the fibre product along `ε`. -/
@[reassoc]
theorem datumGluing_hom_comp_snd ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (datumGluing D hf hg ε ε' heq).hom ≫ pullback.snd (fiberCoverHom (D.obj g hg)) ε' =
      pullback.snd (fiberCoverHom (D.obj f hf)) ε :=
  cover_hom_g_comp_snd _ _ ε ε' (datumCoverIso D hf hg ε ε' heq).hom

/-- **The inverse of the gluing isomorphism is an isomorphism over `Z`.** -/
@[reassoc]
theorem datumGluing_inv_comp_snd ⦃V W Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (datumGluing D hf hg ε ε' heq).inv ≫ pullback.snd (fiberCoverHom (D.obj f hf)) ε =
      pullback.snd (fiberCoverHom (D.obj g hg)) ε' :=
  cover_hom_g_comp_snd _ _ ε' ε (datumCoverIso D hf hg ε ε' heq).inv

/-- **The cocycle condition on the covering objects of the site.** -/
theorem datumGluing_trans ⦃V W X Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄
    (hg : R g) ⦃h : X ⟶ U⦄ (hh : R h) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (datumGluing D hf hg ε₁ ε₂ h₁₂).hom ≫ (datumGluing D hg hh ε₂ ε₃ h₂₃).hom =
      (datumGluing D hf hh ε₁ ε₃ h₁₃).hom :=
  congrArg (fun m => (Subtype.val m).g) (datumCoverIso_trans D hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃)

/-- The gluing isomorphism on the covering objects of an arrow with itself along one and the same
morphism into its source is the identity. -/
@[simp]
theorem datumGluing_self ⦃V Z : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V)
    (heq : ε ≫ f = ε ≫ f) : (datumGluing D hf hf ε ε heq).hom = 𝟙 _ :=
  congrArg (fun m => (Subtype.val m).g) (datumCoverIso_self D hf ε heq)

end AlgebraicGeometry.Stack

end
