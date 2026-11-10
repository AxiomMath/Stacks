module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing

/-!
# The two identifications of iterated étale restriction with restriction along a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be étale morphisms of algebraic spaces over a scheme `S`.
Restriction of modules along `g` followed by restriction along `f` is restriction along `f ≫ g`
in two ways.  `AlgebraicGeometry.Space.etaleModulePullbackComp` is the strict one: étale
restriction is the pushforward of modules along postcomposition of charts, postcomposition
composes on the nose, and the identification is `SheafOfModules.pushforwardComp`.
`AlgebraicGeometry.Space.etaleModulePullbackFactorIso` passes instead through the inverse image
of modules: it is the composition comparison of Stacks 03LU, transported along the
identification of Stacks 03LW of the inverse image along an étale morphism with étale
restriction.  **The two agree**, which is what this file proves, for a composite and for an
elementary distinguished square, and on unbounded derived categories.  So the Mayer–Vietoris
comparison of Stacks 08GV, written with the second, and the Mayer–Vietoris triangle that
Stacks 08HB is stated with, written with the first, speak of the same map.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullbackFactorIso_eq_etaleModulePullbackComp`: **the two
  identifications agree**, and `AlgebraicGeometry.Space.etaleModulePullbackFactorIso_eq` is the
  same for a morphism presented as a composite.
* `AlgebraicGeometry.Space.edsRestrictCompOpen_eq_edsFactorIsoOpen` and
  `AlgebraicGeometry.Space.edsRestrictCompEtale_eq_edsFactorIsoEtale`: the two identifications
  of iterated restriction with restriction to the intersection of an elementary distinguished
  square agree, through the open subspace and through the étale algebraic space.
* `AlgebraicGeometry.Space.edsDerivedRestrictCompOpen_eq` and
  `AlgebraicGeometry.Space.edsDerivedRestrictCompEtale_eq`: the same on unbounded derived
  categories.
* `AlgebraicGeometry.Space.edsShriekOpenComparison_eq` and
  `AlgebraicGeometry.Space.edsShriekEtaleComparison_eq`: consequently each comparison map out
  of the intersection of the square is the comparison of left adjoints attached to the strict
  identification.

## Implementation notes

The content is `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, which
compares the composition comparison of Stacks 03LU with the strict composition of étale
restrictions once the two adjunctions of étale restriction along a composite are known to have
the same unit, and that comparison of units is
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`.  What is added is the
bookkeeping of the two transports of Stacks 03LW, which cancel.

Everything on the derived categories is read off the underived statement through
`CategoryTheory.NatTrans.mapDerivedCategory`, so no derived computation occurs.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Factor

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The two identifications of iterated étale restriction with restriction along the composite
agree.**  Restricting modules along `g` and then along `f` is restricting along `f ≫ g`, and the
strict identification is the one carried by the composition comparison for the inverse image of
modules. -/
theorem etaleModulePullbackFactorIso_eq_etaleModulePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) :
    etaleModulePullbackFactorIso B S hS f g hf hg rfl hfg =
      etaleModulePullbackComp B S hS f g hf hg hfg := by
  have h1 : Functor.whiskerLeft (modulePullback B S hS g)
        (modulePullbackIsoEtaleModulePullback B S hS f hf).inv ≫
      Functor.whiskerLeft (modulePullback B S hS g)
        (modulePullbackIsoEtaleModulePullback B S hS f hf).hom = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, Iso.inv_hom_id, Functor.whiskerLeft_id']
  have h2 : Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).inv
        (etaleModulePullback.{u, u} B S hS f hf) ≫
      Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).hom
        (etaleModulePullback.{u, u} B S hS f hf) = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id']
  apply Iso.ext
  change (Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).symm
          (etaleModulePullback.{u, u} B S hS f hf) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS g)
          (modulePullbackIsoEtaleModulePullback B S hS f hf).symm ≪≫
        modulePullbackCompIso B S hS f g ≪≫
        modulePullbackIsoEtaleModulePullback B S hS (f ≫ g) hfg).hom = _
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom]
  rw [modulePullbackCompIso_hom_comp_etaleRestriction B S hS f g hf hg hfg
      (etaleModulePullbackCompAdjunction_unit B S hS f g hf hg hfg),
    ← assoc (Functor.whiskerLeft (modulePullback B S hS g)
      (modulePullbackIsoEtaleModulePullback B S hS f hf).inv),
    h1, id_comp, ← assoc, h2, id_comp]

/-- The two identifications agree for an étale morphism presented as a composite, read through
the comparison of étale restrictions along equal morphisms. -/
theorem etaleModulePullbackFactorIso_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) {k : X ⟶ Z} (hk : f ≫ g = k)
    (hk' : IsEtale B S hS k.hom) :
    etaleModulePullbackFactorIso B S hS f g hf hg hk hk' =
      etaleModulePullbackComp B S hS f g hf hg hfg ≪≫
        etaleModulePullbackCongr B S hS hfg hk' hk := by
  subst hk
  obtain rfl : hk' = hfg := proof_irrel hk' hfg
  refine (etaleModulePullbackFactorIso_eq_etaleModulePullbackComp B S hS f g hf hg hk').trans ?_
  exact (Iso.trans_refl _).symm

end Factor

section Square

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The two identifications of iterated restriction with restriction to the intersection of an
elementary distinguished square agree, through the open subspace.** -/
theorem edsRestrictCompOpen_eq_edsFactorIsoOpen :
    edsRestrictCompOpen B S hS hsq = edsFactorIsoOpen B S hS hsq :=
  (etaleModulePullbackFactorIso_eq_etaleModulePullbackComp B S hS (edsFst B S hS hsq)
    (edsOpenHom B S hS hsq) (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)).symm

/-- **The two identifications of iterated restriction with restriction to the intersection of an
elementary distinguished square agree, through the étale algebraic space.** -/
theorem edsRestrictCompEtale_eq_edsFactorIsoEtale :
    edsRestrictCompEtale B S hS hsq = edsFactorIsoEtale B S hS hsq :=
  (etaleModulePullbackFactorIso_eq B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
    (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (edsSnd_comp_edsEtaleHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)).symm

/-- The derived forms of the two identifications of iterated restriction with restriction to the
intersection agree, through the open subspace. -/
theorem mapDerivedCategory_edsFactorIsoOpen_hom :
    NatTrans.mapDerivedCategory (edsFactorIsoOpen B S hS hsq).hom =
      NatTrans.mapDerivedCategory (edsRestrictCompOpen B S hS hsq).hom := by
  rw [edsRestrictCompOpen_eq_edsFactorIsoOpen]

/-- The derived forms of the two identifications of iterated restriction with restriction to the
intersection agree, through the étale algebraic space. -/
theorem mapDerivedCategory_edsFactorIsoEtale_hom :
    NatTrans.mapDerivedCategory (edsFactorIsoEtale B S hS hsq).hom =
      NatTrans.mapDerivedCategory (edsRestrictCompEtale B S hS hsq).hom := by
  rw [edsRestrictCompEtale_eq_edsFactorIsoEtale]

/-- **On unbounded derived categories the two identifications of iterated restriction with
restriction to the intersection agree, through the open subspace.** -/
theorem edsDerivedRestrictCompOpen_eq :
    (Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq)
          (edsRestrictFst B S hS hsq)).symm ≪≫
        asIso (NatTrans.mapDerivedCategory (edsFactorIsoOpen B S hS hsq).hom) =
      edsDerivedRestrictCompOpen B S hS hsq :=
  by rw [← edsRestrictCompOpen_eq_edsFactorIsoOpen]; rfl

/-- **On unbounded derived categories the two identifications of iterated restriction with
restriction to the intersection agree, through the étale algebraic space.** -/
theorem edsDerivedRestrictCompEtale_eq :
    (Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq)
          (edsRestrictSnd B S hS hsq)).symm ≪≫
        asIso (NatTrans.mapDerivedCategory (edsFactorIsoEtale B S hS hsq).hom) =
      edsDerivedRestrictCompEtale B S hS hsq :=
  by rw [← edsRestrictCompEtale_eq_edsFactorIsoEtale]; rfl

section Comparison

variable
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}

/-- The comparison out of the intersection attached to the factorization through the open
subspace is the comparison of left adjoints attached to the strict identification of iterated
restriction with restriction to the intersection. -/
theorem edsShriekOpenComparison_eq (adjU : shriekU ⊣ edsRestrictOpen B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq) :
    edsShriekOpenComparison B S hS hsq adjU adjP =
      Adjunction.factorLeftAdjointComparison _ _ _
        (edsRestrictCompOpen B S hS hsq) adjP adjU := by
  rw [edsRestrictCompOpen_eq_edsFactorIsoOpen]
  rfl

/-- The comparison out of the intersection attached to the factorization through the étale
algebraic space is the comparison of left adjoints attached to the strict identification of
iterated restriction with restriction to the intersection. -/
theorem edsShriekEtaleComparison_eq (adjV : shriekV ⊣ edsRestrictEtale B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq) :
    edsShriekEtaleComparison B S hS hsq adjV adjP =
      Adjunction.factorLeftAdjointComparison _ _ _
        (edsRestrictCompEtale B S hS hsq) adjP adjV := by
  rw [edsRestrictCompEtale_eq_edsFactorIsoEtale]
  rfl

end Comparison

end Square

end AlgebraicGeometry.Space

end
