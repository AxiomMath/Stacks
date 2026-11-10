module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeEssSurj

/-!
# `F^R` of Stacks 0E94 is essentially surjective, hence an equivalence

Let `G` be a functor over the site from the points of `T` to
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` and `ξ = (X ⟶ T, L)` the polarized
family glued from it (`AlgebraicGeometry.PolarizedOverSpace.gluePolarized`). The isomorphisms
`σ_a : M_a ≅ s_a^* L` (`AlgebraicGeometry.PolarizedOverSpace.glueSigma`) are natural in the point
(`AlgebraicGeometry.PolarizedOverSpace.glueSigma_comp`), hence form a natural isomorphism of `G`
with the inverse images `a ↦ (Z_a, s_a^* L)`
(`CategoryTheory.Pseudofunctor.CoGrothendieck.liftConstNatTrans`). Followed by the inverse images
of the isomorphisms of the families of `G` with the base changes of `X`, this is an isomorphism
`G ≅ F^R(ξ)`, so that `F^R` is essentially surjective and, being fully faithful, an equivalence.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.glueSigmaNatTrans`: `σ`, as a natural transformation.
* `AlgebraicGeometry.PolarizedOverSpace.glueBaseChangeIso`: `G ≅ F^R(ξ)`.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_essSurj`,
  `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_isEquivalence`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

-- The morphisms of the Grothendieck construction carry the quiver of `CategoryStruct`.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}}

section Square

/-- **A naturality square of modules, read in the Grothendieck construction of the modules on the
arrows.** For a morphism `m : P ⟶ Q` of that construction, an object `Y = (X, L)` of modules on
algebraic spaces and maps `s_P, s_Q` to `X` with `m ≫ s_Q = s_P`, morphisms
`σ_Q : Q.fiber ⟶ s_Q^* L` and `σ_P : P.fiber ⟶ s_P^* L` with `m.fiber ≫ m^* σ_Q = σ_P ≫ c` in the
language of modules (`c` the comparison of iterated inverse images, Stacks 03LU) satisfy the same
square with the inverse image and the comparison of the pseudofunctor. Every datum is also given in
the language of modules, linked by equalities, so that a concrete square only has to match its data
one by one. -/
theorem inverseImageSquare_of_heq
    {P Q : Pseudofunctor.CoGrothendieck ((arrowSpace B).op.toPseudofunctor.comp
      (Space.modulesPseudofunctor B integerBase (hZ B)))} {m : P ⟶ Q}
    {Y : Pseudofunctor.CoGrothendieck (Space.modulesPseudofunctor B integerBase (hZ B))}
    {sP : (arrowSpace B).obj P.base ⟶ Y.base} {sQ : (arrowSpace B).obj Q.base ⟶ Y.base}
    {hs : (arrowSpace B).map m.base ≫ sQ = sP}
    {σQ : Q.fiber ⟶
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map sQ.op.toLoc).toFunctor.obj Y.fiber}
    {σP : P.fiber ⟶
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map sP.op.toLoc).toFunctor.obj Y.fiber}
    {X' Y' Z' : AlgebraicSpaces B integerBase (hZ B)} {q' : Z' ⟶ Y'} {f' : Y' ⟶ X'} {k' : Z' ⟶ X'}
    {hk' : q' ≫ f' = k'} {L' : Space.Modules.{u, u} B integerBase (hZ B) X'.1 X'.2}
    {MY' : Space.Modules.{u, u} B integerBase (hZ B) Y'.1 Y'.2}
    {MZ' : Space.Modules.{u, u} B integerBase (hZ B) Z'.1 Z'.2}
    {σY' : MY' ⟶ (Space.modulePullback B integerBase (hZ B) f').obj L'}
    {σZ' : MZ' ⟶ (Space.modulePullback B integerBase (hZ B) k').obj L'}
    {κ' : MZ' ⟶ (Space.modulePullback B integerBase (hZ B) q').obj MY'}
    (h : κ' ≫ (Space.modulePullback B integerBase (hZ B) q').map σY' =
      σZ' ≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) q' f' k' hk' L').hom)
    (hX : Y.base = X') (hY : (arrowSpace B).obj Q.base = Y') (hZZ : (arrowSpace B).obj P.base = Z')
    (hq : HEq ((arrowSpace B).map m.base) q') (hf : HEq sQ f') (hk : HEq sP k')
    (hL : HEq Y.fiber L') (hMY : HEq Q.fiber MY') (hMZ : HEq P.fiber MZ') (hσY : HEq σQ σY')
    (hσZ : HEq σP σZ') (hκ : HEq m.fiber κ') :
    LiftConstSquare (F := Space.modulesPseudofunctor B integerBase (hZ B)) (G := arrowSpace B) m Y
      sP sQ hs σP σQ := by
  unfold LiftConstSquare
  subst hX hY hZZ
  cases hq
  cases hf
  cases hk
  cases hL
  cases hMY
  cases hMZ
  cases hσY
  cases hσZ
  cases hκ
  exact (congrArg (m.fiber ≫ ·) (modulesPseudofunctor_map_map ((arrowSpace B).map m.base) σQ)).trans
    (h.trans (congrArg (σP ≫ ·) (Space.modulesPseudofunctor_mapComp'_hom_app
      ((arrowSpace B).map m.base) sQ sP hk' _ Y.fiber).symm))

end Square

variable {T : AlgebraicSpaces B integerBase (hZ B)}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B))

section Sigma

/-- **`σ` as a natural transformation** from `G` to the inverse images `a ↦ (Z_a, s_a^* L)` of the
glued polarization: its naturality is the naturality of `σ`
(`AlgebraicGeometry.PolarizedOverSpace.glueSigma_comp`). -/
def glueSigmaNatTrans :
    glueInclusion G ⟶ glueComma G ⋙ fibreInverseImage :=
  liftConstNatTrans (glueInclusion G) ((familyPair B T).obj (gluePolarized G)) (chartMap G)
    (chartHom_comp_chartMap G) (glueSigmaHom G) (fun {a' a} u => by
      refine inverseImageSquare_of_heq
        (Iso.hom_comp_map_hom_eq_of_trans_mapIso_trans_symm_eq _ _ _ _ _ (glueSigma_comp G a u))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact rfl
      · exact rfl
      · exact rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl
      · exact HEq.rfl)

/-- The components of `σ` are invertible. -/
instance isIso_glueSigmaNatTrans_app (a : (Points T).obj) : IsIso ((glueSigmaNatTrans G).app a) :=
  isIso_liftConstNatTrans_app _ _ _ _ _ _ a (isIso_glueSigmaHom G a)

end Sigma

section Comparison

/-- The morphisms of triples from the families of `G` to the base changes of the glued family. -/
abbrev glueCommaHom : glueComma G ⟶ fibreComma (gluePolarized G) :=
  Comma.liftConstHom (fun u => chartHom_comp_chartMap G u)
    (fibreSpaceMap_naturality (gluePolarized G)) (glueArrowNatTrans G) (𝟙 _) (fun a =>
      ((ObjectProperty.hom_ext _ (glueFibreLift_fst G a)).trans (Category.comp_id _).symm).trans
        (congrArg (chartMap G a ≫ ·) (CategoryTheory.Functor.map_id _ _).symm))

/-- The inverse image of the morphism of triples at a point is invertible: its base is the
isomorphism of the family of `G` with the base change, its fibre an identity. -/
instance isIso_inverseImage_glueCommaHom_app (a : (Points T).obj) :
    IsIso (fibreInverseImage.map ((glueCommaHom G).app a)) := by
  have hl : IsIso ((glueCommaHom G).app a).left :=
    @Arrow.isIso_of_isIso_left_of_isIso_right _ _ _ _ (glueArrowHom G a) (isIso_glueFibreLift G a)
      (inferInstance : IsIso (eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a)))
  exact isIso_of_isIso_base_of_isIso_fiber _ hl
    (isIso_inverseImage_map_fiber (arrowSpace B) ((glueCommaHom G).app a)
      (inferInstance : IsIso (𝟙 ((familyPair B T).obj (gluePolarized G)))))

/-- **The comparison of `G` with `F^R(ξ)`**, in the Grothendieck construction: `σ` followed by the
inverse images of the morphisms of triples. -/
def glueComparison : glueInclusion G ⟶ fibreComma (gluePolarized G) ⋙ fibreInverseImage :=
  glueSigmaNatTrans G ≫ Functor.whiskerRight (glueCommaHom G) fibreInverseImage

/-- The comparison of `G` with `F^R(ξ)` in the Grothendieck construction is an isomorphism. -/
instance isIso_glueComparison : IsIso (glueComparison G) := by
  have : ∀ a, IsIso ((Functor.whiskerRight (glueCommaHom G) fibreInverseImage).app a) :=
    fun a => isIso_inverseImage_glueCommaHom_app G a
  have : IsIso (glueSigmaNatTrans G) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (glueCommaHom G) fibreInverseImage) :=
    NatIso.isIso_of_isIso_app _
  exact IsIso.comp_isIso

/-- The comparison, with target the functor `F^R(ξ)` read in the Grothendieck construction. -/
def glueComparisonTransport : glueInclusion G ⟶
    (baseChangeRepresented (gluePolarized G)).toFunctor ⋙ representedPolarizedInclusion (B := B) :=
  NatTrans.transportOfEq rfl (baseChangeRepresented_comp_inclusion (gluePolarized G)).symm
    (glueComparison G)

/-- The transported comparison of `G` with `F^R(ξ)` is an isomorphism. -/
instance isIso_glueComparisonTransport : IsIso (glueComparisonTransport G) := by
  unfold glueComparisonTransport NatTrans.transportOfEq
  infer_instance

/-- The inclusion of `RepresentedPolarized` into the Grothendieck construction is faithful. -/
instance representedPolarizedInclusion_faithful :
    (representedPolarizedInclusion (B := B)).Faithful :=
  Functor.Faithful.comp (wideSubcategoryInclusion (cartesianIso B))
    (ObjectProperty.ι (IsRepresentedPolarized B))

/-- **The comparison of `G` with `F^R(ξ)`**, as a natural transformation of functors to
`RepresentedPolarized`: its components lie in `RepresentedPolarized` because they are
invertible. -/
def glueBaseChangeHom : G.toFunctor ⟶ (baseChangeRepresented (gluePolarized G)).toFunctor :=
  NatTrans.liftOfFaithful (A := G.toFunctor) (hI := representedPolarizedInclusion_faithful)
    (representedPolarizedInclusion (B := B))
    (glueComparisonTransport G)
    (fun a => ⟨ObjectProperty.homMk ((glueComparisonTransport G).app a),
      @cartesianIso_of_isIso _ (G.obj a).obj ((baseChangeRepresented (gluePolarized G)).obj a).obj
        (ObjectProperty.homMk ((glueComparisonTransport G).app a))
        (inferInstanceAs (IsIso ((glueComparisonTransport G).app a)))⟩)
    (fun _ => rfl)

/-- The components of the comparison of `G` with `F^R(ξ)` are isomorphisms. -/
instance isIso_glueBaseChangeHom_app (a : (Points T).obj) :
    IsIso ((glueBaseChangeHom G).app a) :=
  isIso_of_isIso_hom_hom _ (inferInstanceAs (IsIso ((glueComparisonTransport G).app a)))

/-- The comparison of `G` with `F^R(ξ)` is a natural isomorphism. -/
instance isIso_glueBaseChangeHom : IsIso (glueBaseChangeHom G) :=
  NatIso.isIso_of_isIso_app _

/-- The base of the comparison at a point, on the bases of the arrows, is the identification of
the base of the family of `G` with the point. -/
theorem glueComparison_app_base_right (a : (Points T).obj) :
    (Pseudofunctor.CoGrothendieck.forget (arrowModules B) ⋙ Arrow.rightFunc).map
        ((glueComparison G).app a) =
      𝟙 _ ≫ eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a) :=
  rfl

/-- The components of the comparison lie over the identities of the points. -/
theorem isHomLift_glueBaseChangeHom_app (a : (Points T).obj) :
    (representedPolarizedProjection B).IsHomLift (𝟙 ((Points T).p.obj a))
      ((glueBaseChangeHom G).app a) := by
  have e1 : (ObjectProperty.ι (IsRepresentedPolarized B)).map
      ((wideSubcategoryInclusion (cartesianIso B)).map ((glueBaseChangeHom G).app a)) =
      (glueComparisonTransport G).app a :=
    (Functor.comp_map (wideSubcategoryInclusion (cartesianIso B))
      (ObjectProperty.ι (IsRepresentedPolarized B)) ((glueBaseChangeHom G).app a)).symm.trans
      (NatTrans.map_liftOfFaithful_app (hI := representedPolarizedInclusion_faithful)
        (representedPolarizedInclusion (B := B)) (glueComparisonTransport G) _ _ a)
  refine IsHomLift.of_fac' (p := representedPolarizedProjection B) _ _
    (SpacesOverSpace.fam_right (glueFamilies G) a) rfl ?_
  rw [Functor.comp_map, Functor.comp_map, e1, glueComparisonTransport,
    NatTrans.map_transportOfEq_app,
    glueComparison_app_base_right, Category.id_comp, Category.id_comp]
  exact eqToHom_comp_eqToHom_comp_eqToHom_eq_comp _ _ _ _ _

/-- **`G` is the base-change functor of the glued polarized family**, `G ≅ F^R(ξ)`. -/
def glueBaseChangeIso : G ≅ baseChangeRepresented (gluePolarized G) :=
  BasedNatIso.mkNatIso (asIso (glueBaseChangeHom G)) (isHomLift_glueBaseChangeHom_app G)

end Comparison

section EssSurj

variable (B T) in
/-- **`F^R` is essentially surjective**: every functor over the site from the points of `T` to
`RepresentedPolarized` is the base-change functor of the polarized family glued from it. -/
instance baseChangeRepresentedFunctor_essSurj : (baseChangeRepresentedFunctor B T).EssSurj :=
  ⟨fun G => ⟨gluePolarized G, ⟨(glueBaseChangeIso G).symm⟩⟩⟩

variable (B T) in
/-- **`F^R` is an equivalence**: it is fully faithful and essentially surjective. -/
instance baseChangeRepresentedFunctor_isEquivalence :
    (baseChangeRepresentedFunctor B T).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩


end EssSurj

end AlgebraicGeometry.PolarizedOverSpace

end
