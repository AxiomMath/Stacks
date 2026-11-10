module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceClause
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomSolutions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# Generalized elements of the small étale structure sheaf

For a scheme `S` of a big étale site, the morphisms of sheaves of sets `Z ⟶ 𝒪_S` on the small
étale site of `S` — the *generalized elements* of shape `Z` of the structure sheaf — form a
commutative ring, and for a representable `Z = h_U` that ring is `Γ(U, ⊤)` (Yoneda).  For a
morphism of ringed topoi `g` between two small étale ringed topoi, applying the inverse image
and following with the structure map of `g` is a ring homomorphism between generalized elements.

These are the three pieces of algebra the existence half of Stacks 04I7 is assembled from: a
section of `𝒪_Y` over an étale `V` *is* a generalized element of shape `h_V`, it can be moved to
`X` by `g`, and polynomial identities between sections survive the move.

## Main definitions

* `AlgebraicGeometry.smallEtaleSchemeRingSheaf`: the structure sheaf of the small étale site as a
  sheaf of rings; its underlying sheaf of sets is `AlgebraicGeometry.setStructureSheaf` on the
  nose.
* `AlgebraicGeometry.smallEtaleSectionRingEquiv`: the Yoneda isomorphism
  `(h_U ⟶ 𝒪_S) ≃+* Γ(U, ⊤)`, evaluation at the identity of `U`.
* `AlgebraicGeometry.transportRingHom`: for `g` a morphism of small étale ringed topoi and
  `c : W ⟶ g⁻¹Z`, the ring homomorphism `a ↦ c ≫ g⁻¹a ≫ g^♯` from generalized elements of
  `𝒪_Y` of shape `Z` to generalized elements of `𝒪_X` of shape `W`.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the small étale site of `S`, as a sheaf of rings.  Its underlying
sheaf of sets is `AlgebraicGeometry.setStructureSheaf B S hS` by `rfl`. -/
abbrev smallEtaleSchemeRingSheaf : Sheaf (SmallEtale.topology B S hS) RingCat.{u} :=
  (sheafCompose (SmallEtale.topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O

/-- The sections of `AlgebraicGeometry.smallEtaleSchemeRingSheaf` commute: they are the global
functions of a scheme. -/
theorem smallEtaleRingSheaf_sections_mul_comm (U : (SmallEtale B S hS)ᵒᵖ)
    (x y : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS) U).obj
      (Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS))) : x * y = y * x :=
  mul_comm (G := ↥Γ((SmallEtale.toScheme B S hS).obj U.unop, ⊤)) x y

/-- The generalized elements of the small étale structure sheaf of a fixed shape form a
commutative ring. -/
instance smallEtaleHomCommRing (Z : Sheaf (SmallEtale.topology B S hS) (Type u)) :
    CommRing (Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) :=
  Sheaf.homCommRing (smallEtaleRingSheaf_sections_mul_comm B S hS) Z

/-- Evaluation of a generalized element of shape `h_U` at the identity of `U`, as a ring
homomorphism to `Γ(U, ⊤)`. -/
def smallEtaleSectionRingHom (U : SmallEtale B S hS) :
    ((smallEtaleYoneda B S hS).obj U ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) →+*
      ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
  Sheaf.sectionsEvalRingHom (J := SmallEtale.topology B S hS) (op U)
    (Z := (smallEtaleYoneda B S hS).obj U) (𝟙 U)

/-- **The Yoneda isomorphism for the small étale structure sheaf, as rings.**  A generalized
element of shape `h_U` of `𝒪_S` is a section of `𝒪_S` over `U`, and the ring operations of the
two sides correspond. -/
def smallEtaleSectionRingEquiv (U : SmallEtale B S hS) :
    ((smallEtaleYoneda B S hS).obj U ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) ≃+*
      ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
  RingEquiv.ofBijective (smallEtaleSectionRingHom B S hS U)
    ((SmallEtale.topology B S hS).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS))).bijective

/-- The Yoneda isomorphism of the small étale structure sheaf is evaluation at the identity of
`U`. -/
theorem smallEtaleSectionRingEquiv_apply (U : SmallEtale B S hS)
    (a : (smallEtaleYoneda B S hS).obj U ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) :
    smallEtaleSectionRingEquiv B S hS U a = a.hom.app (op U) (𝟙 U) :=
  rfl

/-- The generalized element named by a section `b` over `U`, evaluated on a chart `k : V ⟶ U`,
is the restriction of `b` along `k`. -/
@[simp]
theorem smallEtaleSectionRingEquiv_symm_hom_app (U : SmallEtale B S hS)
    (b : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) (V : (SmallEtale B S hS)ᵒᵖ)
    (k : V.unop ⟶ U) :
    ((smallEtaleSectionRingEquiv B S hS U).symm b).hom.app V k =
      smallEtaleRestrict B S hS k b := by
  have h : (smallEtaleSectionRingEquiv B S hS U).symm b =
      (SmallEtale.topology B S hS).yonedaEquiv.symm b :=
    (smallEtaleSectionRingEquiv B S hS U).symm_apply_eq.2
      (Equiv.apply_symm_apply ((SmallEtale.topology B S hS).yonedaEquiv
        (F := Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) (X := U)) b).symm
  rw [h]
  rfl

/-- Two generalized elements of shape `h_U` with the same value at the identity agree. -/
theorem smallEtaleSectionRingEquiv_symm_apply_eq (U : SmallEtale B S hS)
    (a : (smallEtaleYoneda B S hS).obj U ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) :
    (smallEtaleSectionRingEquiv B S hS U).symm (a.hom.app (op U) (𝟙 U)) = a :=
  (smallEtaleSectionRingEquiv B S hS U).symm_apply_apply a

/-- **Restricting a section is precomposing its generalized element.** -/
theorem yoneda_map_comp_smallEtaleSectionRingEquiv_symm {U U' : SmallEtale B S hS}
    (k : U' ⟶ U) (b : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) :
    (smallEtaleYoneda B S hS).map k ≫ (smallEtaleSectionRingEquiv B S hS U).symm b =
      (smallEtaleSectionRingEquiv B S hS U').symm (smallEtaleRestrict B S hS k b) := by
  refine (smallEtaleSectionRingEquiv B S hS U').injective ?_
  rw [RingEquiv.apply_symm_apply, smallEtaleSectionRingEquiv_apply]
  change ((smallEtaleSectionRingEquiv B S hS U).symm b).hom.app (op U') (𝟙 U' ≫ k) = _
  rw [smallEtaleSectionRingEquiv_symm_hom_app, Category.id_comp]

/-- The value of a generalized element of shape `Z` on a section `z` of `Z` over `U` is the
section over `U` of the generalized element obtained by precomposing with the morphism `h_U ⟶ Z`
that names `z`. -/
theorem hom_app_eq_smallEtaleSectionRingEquiv {Z : Sheaf (SmallEtale.topology B S hS) (Type u)}
    (a : Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) (U : SmallEtale B S hS)
    (z : Z.obj.obj (op U)) :
    a.hom.app (op U) z = smallEtaleSectionRingEquiv B S hS U
      ((SmallEtale.topology B S hS).yonedaEquiv.symm z ≫ a) :=
  (congrArg (a.hom.app (op U)) ((SmallEtale.topology B S hS).yonedaEquiv.apply_symm_apply z)).symm

end Site

/-! ### Transport of generalized elements along a morphism of small étale ringed topoi -/

section Transport

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- **Moving a generalized element along `g`, as a ring homomorphism.**  For `c : W ⟶ g⁻¹Z`, a
generalized element `a : Z ⟶ 𝒪_Y` goes to `c ≫ g⁻¹a ≫ g^♯ : W ⟶ 𝒪_X`.  That this is additive
and multiplicative is `Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom` followed by
`CategoryTheory.Sheaf.postcompRingHomOfSheaf` at the inverse-image form of the structure map. -/
def transportRingHom {Z : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u)}
    {W : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
    (c : W ⟶ g.toToposHom.inverseImage.obj Z) :
    (Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B Y.obj Y.property)) →+*
      (W ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B X.obj X.property)) :=
  letI := g.toToposHom.preservesFiniteLimits
  (Sheaf.postcompRingHomOfSheaf (RingedToposHom.fSharpInverseImageRing.{u, u + 1, u, u, u + 1, u} g)
      W).comp
    (Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom _ g.toToposHom.inverseImage c)

/-- `AlgebraicGeometry.transportRingHom` is `a ↦ c ≫ g⁻¹a ≫ g^♯`, by definition. -/
theorem transportRingHom_apply {Z : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u)}
    {W : Sheaf (SmallEtale.topology B X.obj X.property) (Type u)}
    (c : W ⟶ g.toToposHom.inverseImage.obj Z)
    (a : Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B Y.obj Y.property)) :
    transportRingHom g c a = c ≫ g.toToposHom.inverseImage.map a ≫ g.fSharpSet :=
  rfl

end Transport

end AlgebraicGeometry

end
