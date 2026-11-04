module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The composition isomorphism of induced functors commutes with the shift

Let `e : F ⋙ G ≅ H` be an isomorphism of additive functors. It induces an isomorphism
`F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c` of the
functors induced on categories of complexes, and an isomorphism of the functors induced on
homotopy categories. For cochain complexes indexed by `ℤ` the first commutes with the shift.

The commutation isomorphism of a functor induced degreewise is the identity in each degree, so
in each degree the square to be checked is the naturality of `e` at an identity.

## Main results

* `CategoryTheory.Functor.commShift_mapHomologicalComplexCompIso_hom`: the composition
  isomorphism on cochain complexes commutes with the shift.
* `CategoryTheory.Functor.mapHomotopyCategoryCompIso_hom_app_quotient`: the composition
  isomorphism on homotopy categories is, at the image of a complex, the image of the
  composition isomorphism on complexes.
* `CategoryTheory.Functor.commShift_mapHomotopyCategoryCompIso_hom`: **the composition
  isomorphism on homotopy categories commutes with the shift**, transported from the
  complex-level statement above.

## Implementation notes

The three `rfl` lemmas record the identifications that the passage from the homotopy category
down to complexes needs: both halves of `Functor.mapHomotopyCategoryFactors` are identities,
and `Functor.mapHomotopyCategoryCompIso` is `Functor.mapHomologicalComplexCompIso` read through
the quotient functor. They are stated because the underlying definitions are `Quotient.lift` and
`Quotient.natIsoLift`, which `simp` does not unfold.

*Transporting the complex-level `CommShift` to the homotopy category.* `Functor.CommShift` is
*data*: two presentations of the same functor out of the homotopy category carry two different
`CommShift.comp`-derived instances, and conjugating the complex-level instance by
`Functor.mapHomotopyCategoryFactors` directly (rewriting the restricted transformation along the
factoring isomorphism on both sides) asks a single `▸` to transport across a mismatch in that
ambient instance bracketing, which it cannot do; the resulting goal is well-typed only up to a
definitional unfolding of the underlying `Quotient.lift`/`Quotient.natIsoLift` functors, which no
available tactic (`simp`, `rw [Functor.map_id]`, `cat_disch`, `convert`) closes. The fix used here
is `CategoryTheory.NatTrans.commShift_of_eq_conj`, which replaces the single `▸` by an explicit
isomorphism `mapHomotopyCategoryAssocIso : quotient V ⋙ (F.mapHomotopyCategory ⋙
G.mapHomotopyCategory) ≅ (F.mapHomologicalComplex ⋙ G.mapHomologicalComplex) ⋙ quotient W'`,
built from the associators and the two `mapHomotopyCategoryFactors` isomorphisms for `F` and `G`,
together with its own `CommShift` instance (assembled from the generic `.of_iso_inv`,
`.whiskerRight`, `.associator`, `.whiskerLeft` and `.comp` combinators — none of these fire as
instances, so each is applied explicitly). Pointwise, each component of
`mapHomotopyCategoryAssocIso.hom` is a chain of identities (both `mapHomotopyCategoryFactors`
isomorphisms are literally `𝟙` by `rfl`): `mapHomotopyCategoryAssocIso_hom_app_eq_id` records
this, collapsing the composite in *term* mode via an explicit `Category.id_comp`-chain, since
`rw`/`simp`/`rfl` in tactic mode do not fire on the `𝟙`s once they sit inside the unfolded
associator/whisker goal (the same kabstract-matching fragility as above; the robust fix is the
same, proving the needed `Functor.map_id`/`Category.id_comp` facts as standalone terms before
substitution). With this isomorphism in hand, `commShift_mapHomotopyCategoryCompIso_hom` first
reduces to the restriction along `quotient V` via
`CategoryTheory.NatTrans.commShift_of_whiskerLeft`, then exhibits that restriction as the
conjugate, by `mapHomotopyCategoryAssocIso` and `H.mapHomotopyCategoryFactors`, of the
right-whiskering `Functor.whiskerRight (mapHomologicalComplexCompIso e c).hom (quotient W' c)` —
itself shift-compatible by `NatTrans.CommShift.whiskerRight` applied to
`commShift_mapHomologicalComplexCompIso_hom` — and closes with `commShift_of_eq_conj`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open CategoryTheory Category

universe v v' v'' u u' u''

variable {V : Type u} [Category.{v} V] [Preadditive V]
  {W : Type u'} [Category.{v'} W] [Preadditive W]
  {W' : Type u''} [Category.{v''} W'] [Preadditive W']
  {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
  [F.Additive] [G.Additive] [H.Additive]

/-- **The composition isomorphism of functors induced on cochain complexes commutes with the
shift.** Both commutation isomorphisms are degreewise the identity, so in each degree the square
is the naturality of `e` at an identity. -/
instance commShift_mapHomologicalComplexCompIso_hom :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  ext K i
  dsimp
  simp [Functor.commShiftIso_comp_hom_app]

/-- The factoring isomorphism of the functor induced on homotopy categories is the identity. -/
theorem mapHomotopyCategoryFactors_hom_app_eq_id
    (K : HomologicalComplex V (ComplexShape.up ℤ)) :
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := rfl

/-- The inverse of the factoring isomorphism of the functor induced on homotopy categories is
the identity. -/
theorem mapHomotopyCategoryFactors_inv_app_eq_id
    (K : HomologicalComplex V (ComplexShape.up ℤ)) :
    (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := rfl

/-- **The composition isomorphism on homotopy categories, at the image of a complex, is the
image of the composition isomorphism on complexes.** -/
theorem mapHomotopyCategoryCompIso_hom_app_quotient
    (K : HomologicalComplex V (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient W' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) := rfl

/-- The reassociation isomorphism carrying the homotopy-category composite `quotient V ⋙
(F.mapHomotopyCategory ⋙ G.mapHomotopyCategory)` to `(F.mapHomologicalComplex ⋙
G.mapHomologicalComplex) ⋙ quotient W'`, built from the two `Functor.mapHomotopyCategoryFactors`
isomorphisms for `F` and `G` and the associators. Its purpose is purely to let
`CategoryTheory.NatTrans.commShift_of_eq_conj` identify two different presentations of the same
functor. -/
noncomputable def mapHomotopyCategoryAssocIso :
    HomotopyCategory.quotient V (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ)) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        HomotopyCategory.quotient W' (ComplexShape.up ℤ) :=
  (Functor.associator (HomotopyCategory.quotient V (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ))).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient W (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).symm

/-- **`mapHomotopyCategoryAssocIso` commutes with the shift**, assembled from the generic
`NatTrans.CommShift` combinators: each associator and whiskering factor is shift-compatible on
its own, and `.comp` chains the five factors. -/
instance commShift_mapHomotopyCategoryAssocIso_hom :
    NatTrans.CommShift (mapHomotopyCategoryAssocIso (F := F) (G := G)).hom ℤ := by
  have h1 : NatTrans.CommShift
      (Functor.associator (HomotopyCategory.quotient V (ComplexShape.up ℤ))
        (F.mapHomotopyCategory (ComplexShape.up ℤ)) (G.mapHomotopyCategory (ComplexShape.up ℤ))).inv
      ℤ := NatTrans.CommShift.of_iso_inv _ _
  have h2 : NatTrans.CommShift
      (Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
        (G.mapHomotopyCategory (ComplexShape.up ℤ))) ℤ :=
    NatTrans.CommShift.whiskerRight _ _ ℤ
  have h3 : NatTrans.CommShift
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient W (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom
      ℤ := NatTrans.CommShift.associator _ _ ℤ
  have h4 : NatTrans.CommShift
      (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom) ℤ :=
    NatTrans.CommShift.whiskerLeft _ _ _ ℤ
  have h5 : NatTrans.CommShift
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have c45 := NatTrans.CommShift.comp
      (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom)
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).inv ℤ
  have c345 := NatTrans.CommShift.comp
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.quotient W (ComplexShape.up ℤ))
        (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom
      (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
        (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (G.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).inv) ℤ
  have c2345 := NatTrans.CommShift.comp
      (Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
        (G.mapHomotopyCategory (ComplexShape.up ℤ)))
      ((Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient W (ComplexShape.up ℤ))
          (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
        (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
          (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
            (G.mapHomologicalComplex (ComplexShape.up ℤ))
            (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).inv)) ℤ
  exact NatTrans.CommShift.comp
    (Functor.associator (HomotopyCategory.quotient V (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) (G.mapHomotopyCategory (ComplexShape.up ℤ))).inv
    (Functor.whiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
      ((Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient W (ComplexShape.up ℤ))
          (G.mapHomotopyCategory (ComplexShape.up ℤ))).hom ≫
        (Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
          (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
            (G.mapHomologicalComplex (ComplexShape.up ℤ))
            (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).inv))) ℤ

/-- **Each component of `mapHomotopyCategoryAssocIso.hom` is an identity.** Both factoring
isomorphisms it is built from are identities in each degree, and the associators and whiskerings
contribute nothing; what remains is a chain of `𝟙`'s, collapsed in term mode because `rw`/`simp`
do not fire on the `𝟙`'s once they sit inside the goal produced by unfolding the associator and
whisker structure. -/
theorem mapHomotopyCategoryAssocIso_hom_app_eq_id
    (K : HomologicalComplex V (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryAssocIso (F := F) (G := G)).hom.app K = 𝟙 _ := by
  have hF : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := rfl
  have key : (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ :=
    hF ▸ CategoryTheory.Functor.map_id _ _
  have hG : (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  dsimp only [mapHomotopyCategoryAssocIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [key, hG]
  exact (Category.id_comp _).trans ((Category.id_comp _).trans
    ((Category.id_comp _).trans (Category.id_comp _)))

/-- **The composition isomorphism of functors induced on homotopy categories commutes with the
shift.** First reduced, via `CategoryTheory.NatTrans.commShift_of_whiskerLeft`, to the restriction
along the quotient functor; that restriction is then identified, by
`CategoryTheory.NatTrans.commShift_of_eq_conj` along `mapHomotopyCategoryAssocIso` and
`H.mapHomotopyCategoryFactors`, with the right-whiskering of the complex-level comparison by the
target quotient functor, which is shift-compatible by the generic `NatTrans.CommShift.whiskerRight`
instance together with the complex-level instance `commShift_mapHomologicalComplexCompIso_hom`. -/
instance commShift_mapHomotopyCategoryCompIso_hom :
    NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom ℤ := by
  apply NatTrans.commShift_of_whiskerLeft (HomotopyCategory.quotient V (ComplexShape.up ℤ))
  have hθ : NatTrans.CommShift
      (Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
        (HomotopyCategory.quotient W' (ComplexShape.up ℤ))) ℤ :=
    NatTrans.CommShift.whiskerRight _ _ ℤ
  have heq : Functor.whiskerLeft (HomotopyCategory.quotient V (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom =
      (mapHomotopyCategoryAssocIso (F := F) (G := G)).hom ≫
        Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
          (HomotopyCategory.quotient W' (ComplexShape.up ℤ)) ≫
        (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv :=
    NatTrans.ext (funext fun K => by
      have h1 : (Functor.whiskerLeft (HomotopyCategory.quotient V (ComplexShape.up ℤ))
          (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom).app K =
          (Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
            (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).app K :=
        mapHomotopyCategoryCompIso_hom_app_quotient e K
      have hRHS : ((mapHomotopyCategoryAssocIso (F := F) (G := G)).hom ≫
          Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
            (HomotopyCategory.quotient W' (ComplexShape.up ℤ)) ≫
          (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv).app K =
          (Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom
            (HomotopyCategory.quotient W' (ComplexShape.up ℤ))).app K := by
        simp only [NatTrans.comp_app]
        rw [mapHomotopyCategoryAssocIso_hom_app_eq_id, mapHomotopyCategoryFactors_inv_app_eq_id]
        exact (Category.id_comp _).trans (Category.comp_id _)
      exact h1.trans hRHS.symm)
  exact NatTrans.commShift_of_eq_conj (mapHomotopyCategoryAssocIso (F := F) (G := G))
    (H.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ heq

end CategoryTheory.Functor

end
