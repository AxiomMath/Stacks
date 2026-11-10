module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleLift

/-!
# Naturality of the global-sections comparisons for affine ind-étale base change

Let `i : Z ⟶ X` be a closed immersion of affine objects of a big pro-étale site. Taking global
sections identifies the base change of an affine ind-étale object of `X` along `i` with the
quotient base change of its ind-étale algebra of global sections, by
`AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRingIso`. This file records that
identification one morphism at a time: how quotient base change acts on the two pushout
inclusions, how base change interacts with the two projections of the fibre product, and the
resulting naturality of the comparison, both on underlying rings and in the opposite category
of ind-étale algebras where the lifting adjunction lives.

It also packages the full faithfulness of the passage to ind-étale algebras, and of that
passage followed by transport along the isomorphism of base rings attached to `i`.

## Main definitions

* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRingIsoOp` reads the comparison
  isomorphism for base change in the opposite category of ind-étale algebras.
* `AlgebraicGeometry.ProEtale.affineIndEtaleGlobalSections_fullyFaithful`: an object of the
  affine ind-étale site of `S` is determined, with its morphisms, by its ind-étale algebra of
  global sections.
* `AlgebraicGeometry.ProEtale.affineIndEtaleGlobalSectionsRebase_fullyFaithful`: reading an
  object of the affine ind-étale site of `Z` as an ind-étale `Γ(X, ⊤)`-algebra through `i` is
  fully faithful.

## Main results

* `AlgebraicGeometry.ProEtale.indEtaleQuotientBaseChange_map_inl` and
  `AlgebraicGeometry.ProEtale.indEtaleQuotientBaseChange_map_inr` describe the action of
  quotient base change of ind-étale algebras on the two pushout inclusions.
* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange_map_comp_fst_appTop` and
  `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange_map_comp_snd_appTop`: on global sections
  base change is compatible with the two projections of the fibre product.
* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRing_map_eq`: quotient base change of
  a morphism is conjugate, through the comparison, to base change of that morphism on global
  sections.
* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRingIso_naturality`: the comparison is
  natural on underlying rings.

## Implementation notes

Naturality of the comparison is checked one pushout inclusion at a time, in
`AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRingIso_naturality_inl` and
`AlgebraicGeometry.ProEtale.affineIndEtaleBaseChangeSiteRingIso_naturality_inr`; the two
branches are then combined by the universal property of the pushout.

The comparison isomorphisms identify values of composites of functors through categories of
ind-étale algebras, and those identifications are definitional unfoldings of the composites.
Making the factors implicit-reducible lets the elaborator perform them.

## References

* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] affineIndEtaleGlobalSections rebaseIndEtaleAlongIso
  affineIndEtaleBaseChange

/-! ### Quotient base change on the pushout inclusions -/

/-- Quotient base change acts on the first pushout inclusion by the given map. -/
theorem indEtaleQuotientBaseChange_map_inl {A : Type u} [CommRing A] (I : Ideal A)
    {U V : IndEtaleAlgebra A} (g : V ⟶ U) :
    pushout.inl V.obj.hom (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Under.Hom.right ((indEtaleQuotientBaseChange A I).map g).hom =
      Under.Hom.right g.hom ≫
        pushout.inl U.obj.hom (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  dsimp [indEtaleQuotientBaseChange]
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ (by
    dsimp [Under.pushout]
    rw [← Category.assoc, Under.w g.hom]
    exact pushout.condition)

/-- Quotient base change fixes the second pushout inclusion. -/
theorem indEtaleQuotientBaseChange_map_inr {A : Type u} [CommRing A] (I : Ideal A)
    {U V : IndEtaleAlgebra A} (g : V ⟶ U) :
    pushout.inr V.obj.hom (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Under.Hom.right ((indEtaleQuotientBaseChange A I).map g).hom =
      pushout.inr U.obj.hom (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  dsimp [indEtaleQuotientBaseChange]
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ (by
    dsimp [Under.pushout]
    rw [← Category.assoc, Under.w g.hom]
    exact pushout.condition)

/-! ### Base change against the projections of the fibre product -/

variable (B : BigProetaleSite.{u}) {X Z : B.Scheme}

/-- Global sections of a composite of morphisms of the big pro-étale site. -/
private theorem appTop_map_comp_eq {S T W : B.Scheme} (f : S ⟶ T) (g : T ⟶ W) (h : S ⟶ W)
    (e : f ≫ g = h) :
    (B.inclusion.map g).appTop ≫ (B.inclusion.map f).appTop = (B.inclusion.map h).appTop := by
  subst e
  simp

/-- On global sections, base change along `i` is compatible with the first projections of the
two fibre products. -/
theorem affineIndEtaleBaseChange_map_comp_fst_appTop (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    (B.inclusion.map (pullback.fst V.obj.obj.hom i)).appTop ≫
        Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
          ((affineIndEtaleGlobalSections B Z).map
            ((affineIndEtaleBaseChange B i).map f))).unop.hom =
      Under.Hom.right (((affineIndEtaleGlobalSections B X).map f).unop.hom) ≫
        (B.inclusion.map (pullback.fst U.obj.obj.hom i)).appTop := by
  exact appTop_map_comp_eq B _ _ _ (pullback.lift_fst _ _ _)

/-- On global sections, base change along `i` is compatible with the second projections of the
two fibre products. -/
theorem affineIndEtaleBaseChange_map_comp_snd_appTop (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    (B.inclusion.map (pullback.snd V.obj.obj.hom i)).appTop ≫
        Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
          ((affineIndEtaleGlobalSections B Z).map
            ((affineIndEtaleBaseChange B i).map f))).unop.hom =
      (B.inclusion.map (pullback.snd U.obj.obj.hom i)).appTop := by
  exact appTop_map_comp_eq B _ _ _ (pullback.lift_snd _ _ _)

/-! ### Naturality of the comparison isomorphism for base change -/

/-- The inverse of the comparison isomorphism for base change composed with it is the identity
of underlying rings. -/
theorem affineIndEtaleBaseChangeSiteRingIso_right_inv_hom_id (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (U : AffineIndEtaleProetale B X) :
    Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).hom.hom = 𝟙 _ :=
  (((ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of (Γ(X.obj, ⊤) ⧸ (affineClosedImmersionRingData B i).1)))).ι ⋙
    Under.forget (CommRingCat.of (Γ(X.obj, ⊤) ⧸
      (affineClosedImmersionRingData B i).1))).mapIso
      (affineIndEtaleBaseChangeSiteRingIso B i U)).inv_hom_id

/-- The first pushout branch of the naturality of the base-change comparison. -/
theorem affineIndEtaleBaseChangeSiteRingIso_naturality_inl (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    pushout.inl (B.inclusion.map V.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).map
          ((affineIndEtaleGlobalSections B X).map f).unop).hom =
    pushout.inl (B.inclusion.map V.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i V).hom.hom ≫
        Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
          Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom := by
  refine (indEtaleQuotientBaseChange_map_inl (affineClosedImmersionRingData B i).1
      (((affineIndEtaleGlobalSections B X).map f).unop)).trans ?_
  refine (congrArg
      (fun t => Under.Hom.right (((affineIndEtaleGlobalSections B X).map f).unop.hom) ≫ t)
      (affineIndEtaleBaseChangeSiteRingIso_inl_inv B i U).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg
      (fun t => t ≫ Under.Hom.right
        (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom)
      (affineIndEtaleBaseChange_map_comp_fst_appTop B i f).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => t ≫ Under.Hom.right
        ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom)
      (affineIndEtaleBaseChangeSiteRingIso_inl B i V).symm).trans ?_
  exact Category.assoc _ _ _

/-- The second pushout branch of the naturality of the base-change comparison. -/
theorem affineIndEtaleBaseChangeSiteRingIso_naturality_inr (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    pushout.inr (B.inclusion.map V.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).map
          ((affineIndEtaleGlobalSections B X).map f).unop).hom =
    pushout.inr (B.inclusion.map V.obj.obj.hom).appTop
        (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionRingData B i).1)) ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i V).hom.hom ≫
        Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
          Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom := by
  refine (indEtaleQuotientBaseChange_map_inr (affineClosedImmersionRingData B i).1
      (((affineIndEtaleGlobalSections B X).map f).unop)).trans ?_
  refine (affineIndEtaleBaseChangeSiteRingIso_inr_inv B i U).symm.trans ?_
  refine (congrArg (fun t => (affineClosedImmersionRingData B i).2.hom ≫ t ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom)
      (affineIndEtaleBaseChange_map_comp_snd_appTop B i f).symm).trans ?_
  refine (congrArg (fun t => (affineClosedImmersionRingData B i).2.hom ≫ t)
      (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ Under.Hom.right
        ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom)
      (affineIndEtaleBaseChangeSiteRingIso_inr B i V).symm).trans ?_
  exact Category.assoc _ _ _

/-- Quotient base change of a morphism is conjugate, through the base-change comparison, to
base change of that morphism on global sections. -/
theorem affineIndEtaleBaseChangeSiteRing_map_eq (i : Z ⟶ X) [IsAffine X.obj] [IsAffine Z.obj]
    [IsClosedImmersion (B.inclusion.map i)] {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    Under.Hom.right ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).map
          ((affineIndEtaleGlobalSections B X).map f).unop).hom =
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i V).hom.hom ≫
        Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
          Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom :=
  pushout.hom_ext (affineIndEtaleBaseChangeSiteRingIso_naturality_inl B i f)
    (affineIndEtaleBaseChangeSiteRingIso_naturality_inr B i f)

/-- The comparison isomorphism for base change is natural, on underlying rings. -/
theorem affineIndEtaleBaseChangeSiteRingIso_naturality (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    {U V : AffineIndEtaleProetale B X} (f : U ⟶ V) :
    Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i V).symm.hom.hom ≫
      Under.Hom.right ((indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).map
          ((affineIndEtaleGlobalSections B X).map f).unop).hom =
    Under.Hom.right ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
        ((affineIndEtaleGlobalSections B Z).map
          ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom := by
  refine (congrArg
      (fun t => Under.Hom.right
        (affineIndEtaleBaseChangeSiteRingIso B i V).symm.hom.hom ≫ t)
      (affineIndEtaleBaseChangeSiteRing_map_eq B i f)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ Under.Hom.right
        ((rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).map
            ((affineIndEtaleGlobalSections B Z).map
              ((affineIndEtaleBaseChange B i).map f))).unop.hom ≫
      Under.Hom.right (affineIndEtaleBaseChangeSiteRingIso B i U).symm.hom.hom)
      (affineIndEtaleBaseChangeSiteRingIso_right_inv_hom_id B i V)).trans ?_
  exact Category.id_comp _

/-- The comparison isomorphism for base change, read in the opposite category, where the
lifting adjunction lives. -/
def affineIndEtaleBaseChangeSiteRingIsoOp (i : Z ⟶ X) [IsAffine X.obj] [IsAffine Z.obj]
    [IsClosedImmersion (B.inclusion.map i)] (U : AffineIndEtaleProetale B X) :
    (affineIndEtaleGlobalSections B X ⋙ (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
      (affineClosedImmersionRingData B i).1).op).obj U ≅
      (affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
        rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).obj U := by
  change Opposite.op (((affineIndEtaleGlobalSections B X ⋙
      (indEtaleQuotientBaseChange Γ(X.obj, ⊤)
        (affineClosedImmersionRingData B i).1).op).obj U).unop) ≅
    Opposite.op (((affineIndEtaleBaseChange B i ⋙ affineIndEtaleGlobalSections B Z ⋙
      rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).obj U).unop)
  exact (affineIndEtaleBaseChangeSiteRingIso B i U).symm.op

/-! ### Full faithfulness of the passage to ind-étale algebras -/

/-- Reading an object of the affine ind-étale site of `S` as an ind-étale algebra is fully
faithful. -/
def affineIndEtaleGlobalSections_fullyFaithful (S : B.Scheme) [IsAffine S.obj] :
    (affineIndEtaleGlobalSections B S).FullyFaithful := by
  letI : (affineIndEtaleGlobalSections B S).Full := affineIndEtaleGlobalSections_full B S
  letI : (affineIndEtaleGlobalSections B S).Faithful :=
    affineIndEtaleGlobalSections_faithful B S
  exact .ofFullyFaithful _

/-- Reading an object of the affine ind-étale site of `Z` as an ind-étale `Γ(X, ⊤)`-algebra
through the closed immersion `i` is fully faithful. -/
def affineIndEtaleGlobalSectionsRebase_fullyFaithful (i : Z ⟶ X) [IsAffine X.obj]
    [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)] :
    (affineIndEtaleGlobalSections B Z ⋙
      rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2).FullyFaithful :=
  (affineIndEtaleGlobalSections_fullyFaithful B Z).comp
    (rebaseIndEtaleAlongIso_fullyFaithful (affineClosedImmersionRingData B i).2)

end AlgebraicGeometry.ProEtale
