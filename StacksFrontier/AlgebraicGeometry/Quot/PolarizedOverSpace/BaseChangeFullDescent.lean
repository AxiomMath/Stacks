module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFull

/-!
# The functor `F^R` of Stacks 0E94 is full

Let `η : F^R(X, L) ⟶ F^R(X', L')` be a morphism of the functors attached by `F^R` to two
polarized families over `T`, and `f : X ⟶ X'` its underlying morphism (Stacks 0E93). On the base
change `Z₀ ⟶ X` of the atlas of `T`, `η` gives `ψ : q₀^* L ⟶ q₀^* f^* L'`
(`CategoryTheory.Pseudofunctor.CoGrothendieck.descentFiber`). It satisfies the pairwise condition
of Stacks 04W3 on `Z₀ ×_X Z₀`, because `η` is natural for the two projections of the product point
`U₀ ×_T U₀` whose base change is `Z₀ ×_X Z₀`. As `Z₀ ⟶ X` is an étale covering (Stacks 041F), the
fullness half of Stacks 04W6
(`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq`) gives
`φ : L ⟶ f^* L'` with `q₀^* φ = ψ`. On every point `a` of `T` the inverse image of `φ` is the
morphism read from `η` on `Z_a`, since both agree after the inverse image along the étale covering
`Z_{a ×_T U₀} ⟶ Z_a`; so `φ` is invertible and the isomorphism `(f, φ)` is sent by `F^R` to `η`.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isPairwiseCompatible_fullDescent`: the pairwise condition.
* `AlgebraicGeometry.PolarizedOverSpace.exists_map_eq_descentFiber_atlasPoint`: the morphism `φ`.
* `AlgebraicGeometry.PolarizedOverSpace.fullIso`: the isomorphism `(f, φ)` of polarized families,
  with `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_map_fullIso`.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_full`: `F^R` is full.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

-- Elaboration compares the inverse images of the pseudofunctor with the functors themselves
-- without unfolding the latter.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

-- The coherences of `CategoryTheory.Pseudofunctor.CoGrothendieck` are stated over a generic
-- category, whose morphisms carry the quiver of `CategoryStruct`; the statements here use the same
-- quiver on algebraic spaces, so that they are instances of those coherences on the nose.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}
variable {ξ ξ' : PolarizedSpacesOver B T} (η : baseChangeRepresented ξ ⟶ baseChangeRepresented ξ')

/-- **The morphism read on the base change of the atlas satisfies the pairwise condition of
Stacks 04W3** on `Z₀ ×_X Z₀`: it is the naturality of `η` along the two projections of the
product point `U₀ ×_T U₀`, whose base change maps isomorphically to `Z₀ ×_X Z₀`. -/
theorem isPairwiseCompatible_fullDescent :
    Space.QuasiCoherentDescent.IsPairwiseCompatible B integerBase (hZ B)
      (X := ((familyPair B T).obj ξ).base)
      (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
      (fun _ => fibreSpaceMap ξ (atlasPoint T))
      (fun _ => descentFiber (fullTheta η) (fullMap η) (fullTheta_square η) (atlasPoint T)) :=
  have H := descentFiber_compat_of_factor (fullTheta η) (fullMap η) (fullTheta_square η)
    (prodPointFst (atlasPoint T) (atlasPoint T)) (prodPointSnd (atlasPoint T) (atlasPoint T))
    (atlasPairFst ξ) (atlasPairSnd ξ) (atlasPair_condition ξ) (prodPointPairMap ξ)
    (prodPointPairMap_fst ξ) (prodPointPairMap_snd ξ)
    (modulesPseudofunctor_map_injective _ (prodPointPairMap_injective ξ))
  isPairwiseCompatible_unit_of_modulesPseudofunctor _ _ _ rfl (atlasPair_condition ξ).symm rfl rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl H

/-- **The module part of `η` descends along the base change of the atlas** (Stacks 04W6): there
is `φ : L ⟶ f^* L'` whose inverse image along `Z₀ ⟶ X` is the morphism read from `η` on `Z₀`. -/
theorem exists_map_eq_descentFiber_atlasPoint :
    ∃ φ : ((familyPair B T).obj ξ).fiber ⟶
        ((Space.modulesPseudofunctor B integerBase (hZ B)).map (fullMap η).op.toLoc).toFunctor.obj
          ((familyPair B T).obj ξ').fiber,
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map
          (fibreSpaceMap ξ (atlasPoint T)).op.toLoc).toFunctor.map φ =
        descentFiber (fullTheta η) (fullMap η) (fullTheta_square η) (atlasPoint T) := by
  have hf : ∀ _ : Unit, Space.IsEtale B integerBase (hZ B) (fibreSpaceMap ξ (atlasPoint T)).hom :=
    fun _ => (isEtaleCovering_fibreFst_atlasPoint ξ).etale ()
  obtain ⟨φ, hφ⟩ := Space.QuasiCoherentDescent.exists_modulePullback_map_eq B integerBase (hZ B)
    (X := ((familyPair B T).obj ξ).base)
    (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
    (fun _ => fibreSpaceMap ξ (atlasPoint T)) hf
    (Space.QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable B integerBase (hZ B)
      _ _ hf (fun _ => relativelyRepresentable_fibreFst ξ (atlasPoint T)))
    (isEtaleCovering_fibreFst_atlasPoint ξ) _ (isPairwiseCompatible_fullDescent η)
  exact ⟨φ, (modulesPseudofunctor_map_map _ φ).trans (hφ ())⟩

/-- **The morphism `φ : L ⟶ f^* L'` descended from `η`.** -/
def fullFiberMap : ((familyPair B T).obj ξ).fiber ⟶
    ((Space.modulesPseudofunctor B integerBase (hZ B)).map (fullMap η).op.toLoc).toFunctor.obj
      ((familyPair B T).obj ξ').fiber :=
  (exists_map_eq_descentFiber_atlasPoint η).choose

/-- The inverse image of `fullFiberMap η` along `Z₀ ⟶ X` is the morphism read from `η` on `Z₀`. -/
theorem map_fullFiberMap_atlasPoint :
    ((Space.modulesPseudofunctor B integerBase (hZ B)).map
        (fibreSpaceMap ξ (atlasPoint T)).op.toLoc).toFunctor.map (fullFiberMap η) =
      descentFiber (fullTheta η) (fullMap η) (fullTheta_square η) (atlasPoint T) :=
  (exists_map_eq_descentFiber_atlasPoint η).choose_spec

/-- **The inverse image of `φ` along every base change `Z_a ⟶ X` is the morphism read from `η`
on `Z_a`**: both agree after the inverse image along `Z_{a ×_T U₀} ⟶ Z_a`, an étale covering, by
naturality of `η` along the two projections of `a ×_T U₀`. -/
theorem map_fullFiberMap (a : (Points T).obj) :
    ((Space.modulesPseudofunctor B integerBase (hZ B)).map
        (fibreSpaceMap ξ a).op.toLoc).toFunctor.map (fullFiberMap η) =
      descentFiber (fullTheta η) (fullMap η) (fullTheta_square η) a :=
  map_map_eq_descentFiber_of_span (fullTheta η) (fullMap η) (fullTheta_square η)
    (fullFiberMap η) (map_fullFiberMap_atlasPoint η) (prodPointFst a (atlasPoint T))
    (prodPointSnd a (atlasPoint T))
    (modulesPseudofunctor_map_injective _ (modulePullback_fibreMap_prodPointFst_injective ξ a))

/-- **Every component of `η` is the inverse image of the morphism of triples `(β_a, (f, φ))`.** -/
theorem fullTheta_app_eq_inverseImage_map (a : (Points T).obj) :
    (fullTheta η).app a = fibreInverseImage.map
      (descentHom (fullTheta η) (fullMap η) (fullTheta_square η) (fullFiberMap η) a) :=
  eq_inverseImage_map_of_map_eq _ _ _ _ a (map_fullFiberMap η a)

/-- `φ` is an isomorphism: its inverse image along the étale covering `Z₀ ⟶ X` is the morphism
read from `η` on `Z₀`, which is invertible, and being invertible descends along flat jointly
surjective families. -/
theorem isIso_fullFiberMap : IsIso (fullFiberMap η) := by
  have hcov := isEtaleCovering_fibreFst_atlasPoint ξ
  refine Space.isIso_of_forall_isIso_modulePullback_map_of_isFlat B integerBase (hZ B)
    (Z' := fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
    (fun _ => fibreSpaceMap ξ (atlasPoint T))
    (fun _ => Space.isFlat_of_isEtale B integerBase (hZ B) (hcov.etale ())) hcov.jointly_surjective
    (fullFiberMap η) fun _ => ?_
  have h : (Space.modulePullback B integerBase (hZ B) (fibreSpaceMap ξ (atlasPoint T))).map
      (fullFiberMap η) =
        descentFiber (fullTheta η) (fullMap η) (fullTheta_square η) (atlasPoint T) :=
    (modulesPseudofunctor_map_map _ _).symm.trans (map_fullFiberMap_atlasPoint η)
  rw [h]
  refine isIso_descentFiber _ _ _ _ ?_
  rw [fullTheta_app]
  exact isIso_fiber (η.app (atlasPoint T))

/-- The pair `(f, φ)` as a morphism of the Grothendieck construction of the modules on the families
over `T`. -/
abbrev fullPairHom : ξ.of.obj ⟶ ξ'.of.obj := ⟨fullBaseMap η, fullFiberMap η⟩

/-- The pair `(f, φ)` is an isomorphism of the Grothendieck construction. -/
instance isIso_fullPairHom : IsIso (fullPairHom η) := by
  refine isIso_of_isIso_base_of_isIso_fiber _ ?_ (isIso_fullFiberMap η)
  have : IsIso ((ObjectProperty.ι _).map (fullBaseMap η)) := IsIso.of_groupoid _
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

/-- The pair `(f, φ)`, as a morphism of polarized families, is an isomorphism. -/
instance isIso_homMk_fullPairHom :
    IsIso (ObjectProperty.homMk (P := polarizationProperty B T) (fullPairHom η)) := by
  have : IsIso ((ObjectProperty.ι (polarizationProperty B T)).map
      (ObjectProperty.homMk (P := polarizationProperty B T) (fullPairHom η))) :=
    isIso_fullPairHom η
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

/-- **The isomorphism of polarized families underlying `η`.** -/
def fullIso : ξ ⟶ ξ' :=
  ⟨asIso (ObjectProperty.homMk (P := polarizationProperty B T) (fullPairHom η))⟩

/-- The morphisms of fibre products induced by `fullIso η` are the bases of the components of
`η`. -/
theorem fibreHomMap_fullIso (a : (Points T).obj) :
    fibreHomMap (fullIso η) a = (η.app a).hom.hom.base.left :=
  fibre_hom_ext ξ' ((fibreHomMap_fst (fullIso η) a).trans
      (yoneda_map_comp_fibreFst_fullBaseMap η a).symm)
    ((fibreHomMap_proj (fullIso η) a).trans ((Category.comp_id _).symm.trans
      ((congrArg (fibreProj ξ a ≫ ·) (fullTheta_app_base_right η a).symm).trans
        (Arrow.w (η.app a).hom.hom.base).symm)))

/-- **The morphism of triples of `fullIso η` at a point is `(β_a, (f, φ))`.** -/
theorem fibreCommaNatTrans_app_fullIso (a : (Points T).obj) :
    (fibreCommaNatTrans (fullIso η)).app a =
      descentHom (fullTheta η) (fullMap η) (fullTheta_square η) (fullFiberMap η) a :=
  Comma.hom_ext _ _
    ((Arrow.hom_ext _ _ (fibreHomMap_fullIso η a) (fullTheta_app_base_right η a).symm).trans
      (congrArg (fun m => m.base) (fullTheta_app η a)).symm)
    rfl

/-- **`F^R` sends `fullIso η` to `η`.** -/
theorem baseChangeRepresentedFunctor_map_fullIso :
    (baseChangeRepresentedFunctor B T).map (fullIso η) = η := by
  refine BasedNatTrans.ext _ _ (NatTrans.ext (funext fun a => ?_))
  refine WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ ?_)
  exact (baseChangeRepresentedFunctor_map_app_hom_hom (fullIso η) a).trans
    ((congrArg fibreInverseImage.map (fibreCommaNatTrans_app_fullIso η a)).trans
      ((fullTheta_app_eq_inverseImage_map η a).symm.trans (fullTheta_app η a)))

omit η in
/-- **`F^R` is full.** -/
instance baseChangeRepresentedFunctor_full : (baseChangeRepresentedFunctor B T).Full where
  map_surjective η := ⟨fullIso η, baseChangeRepresentedFunctor_map_fullIso η⟩

end AlgebraicGeometry.PolarizedOverSpace

end
