module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.RightDerivedCompIsoTargetCongr

/-!
# The classical excision across a change of spelling of the degree-zero functors

The classical degree-`n` excision for a datum `S : 𝒜 ⥤ 𝒜`, `S' : 𝒜' ⥤ 𝒜'`, `L : 𝒜 ⥤ 𝒜'` exact and
preserving injective objects, and `e : S ⋙ L ≅ L ⋙ S'`, is

`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n ≪≫
  Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n :
    S.rightDerived n ⋙ L ≅ L ⋙ S'.rightDerived n`.

This file proves it natural in the degree-zero functors: an isomorphism `κ : S₁ ≅ S₂` and an
isomorphism `κ' : S₁' ≅ S₂'` carrying `e₁` to `e₂` carry the excision at the first datum to the
excision at the second, through Mathlib's `CategoryTheory.NatTrans.rightDerived` of `κ` and of
`κ'`.

## Main results

* `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_natTrans_source`:
  `CategoryTheory.Functor.rightDerivedCompIso` is natural in the inner functor.
* `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_natTrans_target`:
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` is natural in the outer
  functor.
* `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_natTrans_exact`: it is
  natural in the exact functor as well.
* `Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app` and
  `Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans`: the classical excision is
  natural in the degree-zero functors, at an object and as natural transformations.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v v' v'' u u' u''

namespace Stacks.Cohomology.DerivedCompTransport

section Inner

variable {A : Type u} {B : Type u'} {B' : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} B']
  [Abelian A] [Abelian B] [Abelian B'] [EnoughInjectives A]
  (S₁ S₂ : A ⥤ B) [S₁.Additive] [S₂.Additive] (κ : S₁ ⟶ S₂)
  (E : B ⥤ B') [E.Additive] [E.PreservesHomology]

/-- **Pulling an exact functor out of a right derived functor is natural in the inner functor.**
For `κ : S₁ ⟶ S₂` of additive functors and `E` exact, the right derived functor of `κ` whiskered
by `E` is carried by `CategoryTheory.Functor.rightDerivedCompIso` to `E` applied to the right
derived functor of `κ`. -/
theorem rightDerivedCompIso_hom_app_natTrans_source (n : ℕ) (X : A) :
    (NatTrans.rightDerived (Functor.whiskerRight κ E) n).app X ≫
        (S₂.rightDerivedCompIso E n).hom.app X =
      (S₁.rightDerivedCompIso E n).hom.app X ≫
        E.map ((NatTrans.rightDerived κ n).app X) := by
  rw [Stacks.DerivedIndexing.rightDerivedCompIso_hom_app,
    Stacks.DerivedIndexing.rightDerivedCompIso_hom_app]
  exact (E.mapHomotopyCategoryHomologyIso (ComplexShape.up ℕ) n).hom.naturality
    ((NatTrans.mapHomotopyCategory κ (ComplexShape.up ℕ)).app ((injectiveResolutions A).obj X))

end Inner

/-- One pair of mutually inverse morphisms cancelled on the left-hand side of an equation whose
right-hand side is rewritten by a commuting square. -/
private theorem cancel_one {D : Type*} [Category* D] {a b c x y z : D}
    (h1 : a ⟶ b) (g : b ⟶ c) (iv : c ⟶ x) (ih : x ⟶ c) (t : c ⟶ z)
    (jv : b ⟶ y) (m : y ⟶ z) (g' : b ⟶ c) (t' : c ⟶ z)
    (hi : iv ≫ ih = CategoryStruct.id c) (hj : jv ≫ m = g' ≫ t')
    (hg : g = g') (ht : t = t') :
    (h1 ≫ g ≫ iv) ≫ ih ≫ t = (h1 ≫ jv) ≫ m := by
  subst hg ht
  simp [reassoc_of% hi, hj]

section Outer

variable {A : Type u} {C : Type u'} {E : Type u''}
  [Category.{v} A] [Category.{v'} C] [Category.{v''} E]
  [Abelian A] [Abelian C] [Abelian E] [EnoughInjectives A] [EnoughInjectives C]
  (L : A ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects]
  (G₁ G₂ : C ⥤ E) [G₁.Additive] [G₂.Additive] (κ : G₁ ⟶ G₂)

/-- **The composite right derived comparison is natural in the outer functor.**  For `L` exact and
preserving injective objects and `κ : G₁ ⟶ G₂` of additive functors, the right derived functor of
`κ` whiskered by `L` is carried by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` to the right derived functor of
`κ` read at `L X`. -/
theorem compRightDerivedNatIso_hom_app_natTrans_target (n : ℕ) (X : A) :
    (NatTrans.rightDerived (Functor.whiskerLeft L κ) n).app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G₂ n).hom.app X =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G₁ n).hom.app X ≫
        (NatTrans.rightDerived κ n).app (L.obj X) := by
  rw [compRightDerivedNatIso_hom_app, compRightDerivedNatIso_hom_app,
    InjectiveResolution.rightDerived_app_eq (Functor.whiskerLeft L κ) (injectiveResolution X) n,
    InjectiveResolution.rightDerived_app_eq κ
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution X)) n]
  refine cancel_one _ _ _ _ _ _ _ _ _
    ((injectiveResolution X).isoRightDerivedObj (L ⋙ G₂) n).inv_hom_id ?_ (by rfl) rfl
  exact Iso.inv_hom_id_assoc _ _

/-- **The composite right derived comparison is natural in the exact functor.**  For a morphism
`lam : L₁ ⟶ L₂` of exact functors preserving injective objects and `G` additive, the right derived
functor of `lam` whiskered by `G` is carried by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` to `R ⁿG` applied to `lam`. -/
theorem compRightDerivedNatIso_hom_app_natTrans_exact (L₁ L₂ : A ⥤ C)
    [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
      [L₁.PreservesInjectiveObjects]
    [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
      [L₂.PreservesInjectiveObjects]
    (lam : L₁ ⟶ L₂) (G : C ⥤ E) [G.Additive] (n : ℕ) (X : A) :
    (NatTrans.rightDerived (Functor.whiskerRight lam G) n).app X ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L₂ G n).hom.app X =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L₁ G n).hom.app X ≫
        (G.rightDerived n).map (lam.app X) := by
  have hcomm : (Stacks.Cohomology.CompositeRightDerived.mapInjRes L₁
          (injectiveResolution X)).ι.f 0 ≫
        ((NatTrans.mapHomologicalComplex lam (ComplexShape.up ℕ)).app
          (injectiveResolution X).cocomplex).f 0 =
      lam.app X ≫ (Stacks.Cohomology.CompositeRightDerived.mapInjRes L₂
        (injectiveResolution X)).ι.f 0 := by
    rw [mapInjRes_ι_f_zero, mapInjRes_ι_f_zero]
    exact lam.naturality _
  have hQ := InjectiveResolution.isoRightDerivedObj_inv_naturality (lam.app X)
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L₁ (injectiveResolution X))
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L₂ (injectiveResolution X))
    ((NatTrans.mapHomologicalComplex lam (ComplexShape.up ℕ)).app
      (injectiveResolution X).cocomplex) hcomm G n
  rw [compRightDerivedNatIso_hom_app, compRightDerivedNatIso_hom_app,
    InjectiveResolution.rightDerived_app_eq (Functor.whiskerRight lam G) (injectiveResolution X) n]
  exact cancel_one _ _ _ _ _ _ _ _ _
    ((injectiveResolution X).isoRightDerivedObj (L₂ ⋙ G) n).inv_hom_id hQ (by rfl) (by rfl)

end Outer

section Transport

variable {A : Type u} {A' : Type u'}
  [Category.{v} A] [Category.{v'} A'] [Abelian A] [Abelian A']
  [EnoughInjectives A] [EnoughInjectives A']
  (S₁ S₂ : A ⥤ A) [S₁.Additive] [S₂.Additive] (κ : S₁ ≅ S₂)
  (S₁' S₂' : A' ⥤ A') [S₁'.Additive] [S₂'.Additive] (κ' : S₁' ≅ S₂')
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects]
  (e₁ : S₁ ⋙ L ≅ L ⋙ S₁') (e₂ : S₂ ⋙ L ≅ L ⋙ S₂')

/-- Flipping a commuting square across two pairs of mutually inverse morphisms. -/
private theorem flip_sq {D : Type*} [Category* D] {a b c d : D}
    (f : a ⟶ b) (g : c ⟶ d) (ih1 : a ⟶ c) (iv1 : c ⟶ a) (ih2 : b ⟶ d) (iv2 : d ⟶ b)
    (h1 : iv1 ≫ ih1 = CategoryStruct.id c) (h2 : ih2 ≫ iv2 = CategoryStruct.id b)
    (h : f ≫ ih2 = ih1 ≫ g) : g ≫ iv2 = iv1 ≫ f := by
  simpa [reassoc_of% h1, h2, reassoc_of% h2] using (iv1 ≫= h =≫ iv2).symm

/-- Composing three commuting squares along a common edge. -/
private theorem transport_chase {D : Type*} [Category* D] {a b c d g d' h' h : D}
    (k : a ⟶ b) (i2 : b ⟶ c) (r2 : c ⟶ d) (q2 : d ⟶ h)
    (i1 : a ⟶ g) (rk : g ⟶ c) (r1 : g ⟶ d') (q1 : d' ⟶ h') (kk : d' ⟶ d) (kl : h' ⟶ h)
    (hflip : k ≫ i2 = i1 ≫ rk) (hcomp : rk ≫ r2 = r1 ≫ kk) (hfin : kk ≫ q2 = q1 ≫ kl) :
    k ≫ i2 ≫ r2 ≫ q2 = (i1 ≫ r1 ≫ q1) ≫ kl := by
  simp [reassoc_of% hflip, reassoc_of% hcomp, hfin]

/-- **The classical excision moves across a change of spelling of the degree-zero functors.**
Let `κ : S₁ ≅ S₂` and `κ' : S₁' ≅ S₂'` be isomorphisms of the degree-zero functors, and let the
two degree-zero excisions `e₁` and `e₂` correspond under them.  Then the two classical degree-`n`
excisions

`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso Sᵢ L (L ⋙ Sᵢ') eᵢ n ≪≫
  Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L Sᵢ' n`

correspond under the right derived functors of `κ` and `κ'`. -/
theorem classicalExcision_natTrans_app
    (hκ : Functor.whiskerRight κ.hom L ≫ e₂.hom = e₁.hom ≫ Functor.whiskerLeft L κ'.hom)
    (n : ℕ) (X : A) :
    L.map ((NatTrans.rightDerived κ.hom n).app X) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₂ L (L ⋙ S₂') e₂ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₂' n).hom.app X =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₁ L (L ⋙ S₁') e₁ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₁' n).hom.app X ≫
        (NatTrans.rightDerived κ'.hom n).app (L.obj X) := by
  have hflip := flip_sq ((NatTrans.rightDerived (Functor.whiskerRight κ.hom L) n).app X)
    (L.map ((NatTrans.rightDerived κ.hom n).app X))
    ((S₁.rightDerivedCompIso L n).hom.app X) ((S₁.rightDerivedCompIso L n).inv.app X)
    ((S₂.rightDerivedCompIso L n).hom.app X) ((S₂.rightDerivedCompIso L n).inv.app X)
    ((S₁.rightDerivedCompIso L n).inv_hom_id_app X)
    ((S₂.rightDerivedCompIso L n).hom_inv_id_app X)
    (rightDerivedCompIso_hom_app_natTrans_source S₁ S₂ κ.hom L n X)
  have hcomp : (NatTrans.rightDerived (Functor.whiskerRight κ.hom L) n).app X ≫
      (NatTrans.rightDerived e₂.hom n).app X =
    (NatTrans.rightDerived e₁.hom n).app X ≫
      (NatTrans.rightDerived (Functor.whiskerLeft L κ'.hom) n).app X := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.rightDerived_comp,
      ← NatTrans.rightDerived_comp, hκ]
  simpa only [Iso.trans_hom, NatTrans.comp_app,
    Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app, Category.assoc] using
    transport_chase _ _ _ _ _ _ _ _ _ _ hflip hcomp
      (compRightDerivedNatIso_hom_app_natTrans_target L S₁' S₂' κ'.hom n X)

/-- **The classical excision moves across a change of spelling of the degree-zero functors.**
As an equality of natural transformations. -/
theorem classicalExcision_natTrans
    (hκ : Functor.whiskerRight κ.hom L ≫ e₂.hom = e₁.hom ≫ Functor.whiskerLeft L κ'.hom)
    (n : ℕ) :
    Functor.whiskerRight (NatTrans.rightDerived κ.hom n) L ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₂ L (L ⋙ S₂') e₂ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₂' n).hom =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S₁ L (L ⋙ S₁') e₁ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S₁' n).hom ≫
        Functor.whiskerLeft L (NatTrans.rightDerived κ'.hom n) :=
  NatTrans.ext <| funext <| classicalExcision_natTrans_app S₁ S₂ κ S₁' S₂' κ' L e₁ e₂ hκ n

end Transport

end Stacks.Cohomology.DerivedCompTransport

end
