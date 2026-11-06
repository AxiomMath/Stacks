module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageHomChartComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Associativity of the composition law of inverse images on small étale topoi

For morphisms of algebraic spaces `e : V ⟶ W`, `i : W ⟶ X` and `g : X ⟶ Y`, the two ways of
contracting the triple inverse image `e⁻¹i⁻¹g⁻¹` to `(e ≫ i ≫ g)⁻¹` through the composition law
of Stacks 03G8 agree, for sheaves of sets and for sheaves of commutative rings.

The composition law for inverse images is the mate of the composition law
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of direct images, and the associativity of
the latter is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` (Stacks 03G2, part
(3)). The associativity of the former is its mate: both sides are compared through
`CategoryTheory.conjugateEquiv`, which turns composites and whiskerings of maps of left adjoints
into composites and whiskerings of maps of right adjoints. The ring-level statement follows
because the composition law for sheaves of commutative rings is the set-level one on underlying
sheaves of sets.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageIso_inv_assoc`: associativity
  of the composition law of inverse images of sheaves of sets.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc`: the same
  for sheaves of commutative rings.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W X Y : AlgebraicSpaces B S hS}

local notation "τ" f => RingedToposHom.toToposHom (smallEtaleRingedToposHom B S hS f)

/-- The mate of the composition law `p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` of inverse images is the composition law
`p_* f_* ≅ (p ≫ f)_*` of direct images. -/
theorem conjugateEquiv_compInverseImageIso_inv (p : V ⟶ W) (f : W ⟶ X) :
    conjugateEquiv ((τ f).adj.comp (τ p).adj) (τ (p ≫ f)).adj
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).inv =
      (smallToposMorphismTypeU_comp B S hS p f).hom := by
  have h1 := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    ((τ f).adj.comp (τ p).adj) (smallToposMorphismTypeU_comp B S hS p f) (τ (p ≫ f)).adj
  have h2 := conjugateEquiv_comp ((τ f).adj.comp (τ p).adj) (τ (p ≫ f)).adj
    ((τ f).adj.comp (τ p).adj)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).inv
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom
  exact (Iso.comp_inv_eq_id _).mp ((congrArg (_ ≫ ·) h1.symm).trans (h2.trans
    ((congrArg _ (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom_inv_id).trans
      (conjugateEquiv_id _))))

/-- **Associativity of the composition law of inverse images of sheaves of sets** (the mate of
Stacks 03G2, part (3), associativity). For `e : V ⟶ W`, `i : W ⟶ X` and `g : X ⟶ Y`, the two
contractions `(e ≫ i ≫ g)⁻¹ ≅ g⁻¹ ⋙ i⁻¹ ⋙ e⁻¹` agree. -/
theorem smallEtaleRingedToposHom_compInverseImageIso_inv_assoc (e : V ⟶ W) (i : W ⟶ X)
    (g : X ⟶ Y) :
    (smallEtaleRingedToposHom_compInverseImageIso B S hS (e ≫ i) g).inv ≫
        Functor.whiskerLeft (τ g).inverseImage
          (smallEtaleRingedToposHom_compInverseImageIso B S hS e i).inv =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS e (i ≫ g)).inv ≫
        Functor.whiskerRight (smallEtaleRingedToposHom_compInverseImageIso B S hS i g).inv
          (τ e).inverseImage ≫
        (Functor.associator _ _ _).hom := by
  apply (conjugateEquiv ((τ g).adj.comp ((τ i).adj.comp (τ e).adj))
    (τ (e ≫ i ≫ g)).adj).injective
  have hL := (conjugateEquiv_comp ((τ g).adj.comp ((τ i).adj.comp (τ e).adj))
    ((τ g).adj.comp (τ (e ≫ i)).adj) (τ (e ≫ i ≫ g)).adj
    (Functor.whiskerLeft (τ g).inverseImage
      (smallEtaleRingedToposHom_compInverseImageIso B S hS e i).inv)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS (e ≫ i) g).inv).symm.trans
    (congrArg₂ (· ≫ ·) ((conjugateEquiv_whiskerLeft ((τ i).adj.comp (τ e).adj)
      (τ (e ≫ i)).adj (τ g).adj _).trans
      (congrArg (Functor.whiskerRight · (τ g).pushforward)
        (conjugateEquiv_compInverseImageIso_inv B S hS e i)))
      (conjugateEquiv_compInverseImageIso_inv B S hS (e ≫ i) g))
  have hA := (conjugateEquiv_comp ((τ g).adj.comp ((τ i).adj.comp (τ e).adj))
    (((τ g).adj.comp (τ i).adj).comp (τ e).adj) ((τ (i ≫ g)).adj.comp (τ e).adj)
    (Functor.associator _ _ _).hom
    (Functor.whiskerRight (smallEtaleRingedToposHom_compInverseImageIso B S hS i g).inv
      (τ e).inverseImage)).symm.trans
    (congrArg₂ (· ≫ ·) (conjugateEquiv_associator_hom (τ g).adj (τ i).adj (τ e).adj)
      ((conjugateEquiv_whiskerRight ((τ g).adj.comp (τ i).adj) (τ (i ≫ g)).adj (τ e).adj _).trans
        (congrArg (Functor.whiskerLeft (τ e).pushforward)
          (conjugateEquiv_compInverseImageIso_inv B S hS i g))))
  have hR := (conjugateEquiv_comp ((τ g).adj.comp ((τ i).adj.comp (τ e).adj))
    ((τ (i ≫ g)).adj.comp (τ e).adj) (τ (e ≫ i ≫ g)).adj
    (Functor.whiskerRight (smallEtaleRingedToposHom_compInverseImageIso B S hS i g).inv
      (τ e).inverseImage ≫ (Functor.associator _ _ _).hom)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS e (i ≫ g)).inv).symm.trans
    (congrArg₂ (· ≫ ·) hA (conjugateEquiv_compInverseImageIso_inv B S hS e (i ≫ g)))
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine NatTrans.ext (funext fun M => ?_)
  exact (smallToposMorphismTypeU_comp_assoc B S hS e i g M).trans (Category.id_comp _).symm

/-- **Associativity of the composition law of inverse images of sheaves of sets**, at a sheaf
`F` on `Y`: the two contractions `(e ≫ i ≫ g)⁻¹F ⟶ e⁻¹i⁻¹g⁻¹F` agree. -/
theorem smallEtaleRingedToposHom_compInverseImageIso_inv_app_assoc (e : V ⟶ W) (i : W ⟶ X)
    (g : X ⟶ Y) (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallEtaleRingedToposHom_compInverseImageIso B S hS (e ≫ i) g).inv.app F ≫
        (smallEtaleRingedToposHom_compInverseImageIso B S hS e i).inv.app
          ((τ g).inverseImage.obj F) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS e (i ≫ g)).inv.app F ≫
        (τ e).inverseImage.map
          ((smallEtaleRingedToposHom_compInverseImageIso B S hS i g).inv.app F) := by
  have h := NatTrans.congr_app
    (smallEtaleRingedToposHom_compInverseImageIso_inv_assoc B S hS e i g) F
  simp only [NatTrans.comp_app] at h
  exact h

/-- On underlying sheaves of sets the inverse of the composition law `p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` for
sheaves of commutative rings is that for sheaves of sets, at every sheaf of commutative rings. -/
theorem forget_map_compInverseImageRingIso_inv_app (p : V ⟶ W) (f : W ⟶ X)
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (smallEtaleRingedTopos B S hS V).forgetRing.map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).inv.app A) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).inv.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj A) := by
  have hhom : (smallEtaleRingedTopos B S hS V).forgetRing.map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).hom.app A) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj A) := by
    haveI hfl := ((smallEtaleRingedToposHom B S hS f).toToposHom.comp
      (smallEtaleRingedToposHom B S hS p).toToposHom).preservesFiniteLimits
    haveI := (⟨fun _ ↦ hfl.preservesFiniteLimits _⟩ :
      Limits.PreservesFiniteProducts ((smallEtaleRingedToposHom B S hS f).toToposHom.comp
        (smallEtaleRingedToposHom B S hS p).toToposHom).inverseImage)
    haveI hfl' := (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.preservesFiniteLimits
    haveI := (⟨fun _ ↦ hfl'.preservesFiniteLimits _⟩ :
      Limits.PreservesFiniteProducts
        (smallEtaleRingedToposHom B S hS (p ≫ f)).toToposHom.inverseImage)
    refine Eq.trans ((smallEtaleRingedTopos B S hS V).forgetRing.map_comp _ _) ?_
    refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b)
      (forget_map_inverseImageCommRingComp_hom (smallEtaleRingedToposHom B S hS f).toToposHom
        (smallEtaleRingedToposHom B S hS p).toToposHom A)
      (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (smallEtaleRingedTopos B S hS V).J A
        (smallEtaleRingedToposHom_compInverseImageIso B S hS p f))) ?_
    exact Category.id_comp _
  exact congrArg Iso.inv (show (smallEtaleRingedTopos B S hS V).forgetRing.mapIso
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).app A) =
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p f).app
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj A) from Iso.ext hhom)

/-- On underlying sheaves of sets, the inverse image of a homomorphism of sheaves of commutative
rings is the inverse image of the underlying map of sheaves of sets. -/
theorem forget_map_smallEtaleInverseImageRing_map (p : V ⟶ W)
    {A A' : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}} (a : A ⟶ A') :
    (smallEtaleRingedTopos B S hS V).forgetRing.map ((smallEtaleInverseImageRing B S hS p).map a) =
      (τ p).inverseImage.map ((smallEtaleRingedTopos B S hS W).forgetRing.map a) := by
  haveI hfl : Limits.PreservesFiniteLimits (τ p).inverseImage := (τ p).preservesFiniteLimits
  haveI : Limits.PreservesFiniteProducts (τ p).inverseImage :=
    ⟨fun _ ↦ hfl.preservesFiniteLimits _⟩
  exact underlyingRingSheaf_map_pullbackCommRingSheafMap.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedTopos B S hS V).J _ a

/-- **Associativity of the composition law of inverse images of sheaves of commutative rings**
(Stacks 03G8 with Stacks 03G2, part (3)). For `e : V ⟶ W`, `i : W ⟶ X`, `g : X ⟶ Y` and a sheaf of
commutative rings `𝒜` on `Y`, the two contractions `(e ≫ i ≫ g)⁻¹𝒜 ≅ e⁻¹i⁻¹g⁻¹𝒜` agree. -/
theorem smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc (e : V ⟶ W) (i : W ⟶ X)
    (g : X ⟶ Y) (A : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}) :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (e ≫ i) g).inv.app A ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS e i).inv.app
          ((smallEtaleInverseImageRing B S hS g).obj A) =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS e (i ≫ g)).inv.app A ≫
        (smallEtaleInverseImageRing B S hS e).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i g).inv.app A) := by
  refine (smallEtaleRingedTopos B S hS V).forgetRing.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    forget_map_compInverseImageRingIso_inv_app, forget_map_compInverseImageRingIso_inv_app,
    forget_map_compInverseImageRingIso_inv_app, forget_map_smallEtaleInverseImageRing_map,
    forget_map_compInverseImageRingIso_inv_app]
  exact smallEtaleRingedToposHom_compInverseImageIso_inv_app_assoc B S hS e i g _

end AlgebraicGeometry.Space

end
