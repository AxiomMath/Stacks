module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian

/-!
# The monoidal unit of the tensor product of étale sheaves of modules is locally constant

Let `B` be a big étale site, `S` an object of it and `Λ` a commutative ring in the coefficient
universe `max (u + 1) v` at which this library computes étale cohomology. Two descriptions of
one abelian étale sheaf on the small étale site of `S` occur in the trace map of
[Stacks, Tag 0GKG]: the abelian sheaf underlying the monoidal unit
`𝟙_ (ModuleSheaf B S Λ)` of the tensor product of sheaves of `Λ`-modules, which is what the
projection formula of [Stacks, Tag 0GKF] speaks about, and the sheaf
`AlgebraicGeometry.locallyConstantSheafAb` of Zariski locally constant `Λ`-valued functions, on
whose sections the fibre integral of [Stacks, Tag 0GKG] is defined. This file identifies the
two, together with their stalks at a geometric point.

The identification is pinned down on sections: it carries the image of `a : Λ` under the
sheafification unit of the constant presheaf of `Λ`-modules to the constant function with value
`a`. That is what makes the stalk statement provable, and it is the reason the identification is
built here as the sheafification of an explicit comparison map rather than transported along
`AlgebraicGeometry.SmallEtale.constantSheafForget_natIso`, whose two sides are compared only
through the uniqueness of a left adjoint.

## Main definitions

* `AlgebraicGeometry.SmallEtale.constantToForgetTensorUnit` — the comparison from the constant
  abelian presheaf with value `Λ` to the abelian sheaf underlying the monoidal unit: the
  sheafification unit of the constant presheaf of `Λ`-modules, read on underlying abelian
  groups.
* `AlgebraicGeometry.SmallEtale.constantSheafIsoForgetTensorUnit` — the resulting identification
  of the constant abelian sheaf with value `Λ` with the abelian sheaf underlying the monoidal
  unit.
* `AlgebraicGeometry.SmallEtale.forgetTensorUnitIsoLocallyConstantSheafAb` — **the abelian sheaf
  underlying the monoidal unit is the sheaf of locally constant `Λ`-valued functions.**

## Main results

* `AlgebraicGeometry.SmallEtale.forgetTensorUnitIsoLocallyConstantSheafAb_toSheafify` — the
  identification on sections: the sheafification-unit image of `a : Λ` goes to the constant
  function with value `a`.
* `AlgebraicGeometry.SmallEtale.modStalk_ε_eq` and
  `AlgebraicGeometry.SmallEtale.modStalk_ε_apply` — the unit constraint `ε` of the monoidal
  stalk functor is the germ of the sheafification unit of the constant presheaf.
* `AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso_inv_app_toPresheafFiber` — the comparison of
  the two `Λ`-module structures on a stalk carries the germ formed in `Λ`-modules to the germ
  formed in abelian groups.
* `AlgebraicGeometry.SmallEtale.presheafFiber_map_toPresheafFiber` — the étale stalk of a
  morphism of abelian sheaves, on a germ.
* `AlgebraicGeometry.SmallEtale.etaleStalkLocallyConstantMapsAbIso_tensorUnit_eps` — **the two
  identifications of the stalk of the monoidal unit with `Λ` agree.** The monoidal one, `ε` of
  the stalk functor, and the concrete one, evaluation of a locally constant function at the
  geometric point, are the same map.

## Implementation notes

**Why the comparison map is the sheafification unit.** The monoidal unit of
`CategoryTheory.Sheaf.monoidalCategory` is the sheafification of the monoidal unit of the
presheaf category, which is the constant presheaf with value `𝟙_ (ModuleCat Λ) = Λ`; so the
underlying abelian sheaf is the sheafification of the constant abelian presheaf with value `Λ`,
and the comparison map is the sheafification unit with its module structure forgotten. Local
bijectivity of that map is local bijectivity of the sheafification unit with module
coefficients, which is
`Stacks.ConstantSheaf.isLocallyInjective_toSheafify_moduleCat` and its surjective companion;
both are statements about elements, so they transfer across the forgetful functor by
`CategoryTheory.Presheaf.equalizerSieve_mem` and
`CategoryTheory.Presheaf.imageSieve_mem` with no further work.

**How `ε` is computed.** The stalk functor on sheaves is monoidal by
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`, whose `ε` is, by definition, the
`ε` of the stalk functor on presheaves followed by the fibre of the sheafification unit and the
oplax unit of sheafification; the last is the identity because the unit of
`CategoryTheory.Sheaf.monoidalCategory` is chosen to be the sheafification of the presheaf unit.
Mathlib's `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_ε` identifies the `ε` of
the presheaf stalk functor with the canonical map out of the sections over *any* étale
neighbourhood of the geometric point, so `ε` is the germ of the sheafification-unit image of
`a`. The neighbourhood used below is the final object `S / S`, which is also the one appearing
in `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbIso_inv_const`.

**The two stalks.** The stalk appearing in the monoidal structure is the colimit formed in
`ModuleCat Λ`, while `AlgebraicGeometry.etaleStalk` is the colimit formed in abelian groups;
`AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso` identifies them. The size hypotheses that the
comparison of the two colimits needs are introduced inside the proof below exactly as
`moduleEtaleStalkIso` introduces them, so that the two terms agree definitionally and none of
the statements here has to carry them.

Nothing here carries a `stacks` attribute: every declaration is a dictionary entry between two
descriptions of one sheaf, not a statement of the source.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section TensorUnit

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall
attribute [local instance] modStalkMonoidal

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type (max (u + 1) v)) [CommRing Λ]

/-- **The comparison from the constant abelian presheaf to the monoidal unit.** The monoidal
unit of the tensor product of étale sheaves of `Λ`-modules is the sheafification of the constant
presheaf with value `Λ`; this is its sheafification unit, read on underlying abelian groups. -/
public def constantToForgetTensorUnit :
    (Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj
        (AddCommGrpCat.of Λ) ⟶
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).obj :=
  Functor.whiskerRight
    (toSheafify (SmallEtale.topology B S.obj S.property)
      (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ)))
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})

/-- Two sections of the constant abelian presheaf with the same image in the monoidal unit agree
locally: the sheafification unit with module coefficients is locally injective, and local
injectivity is a statement about elements, so it does not see the forgetful functor. -/
public theorem isLocallyInjective_constantToForgetTensorUnit :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ) := by
  have : Presheaf.IsLocallyInjective (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property)
        (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) :=
    Stacks.ConstantSheaf.isLocallyInjective_toSheafify_moduleCat _ _ _
  exact ⟨fun x y h => Presheaf.equalizerSieve_mem _
    (toSheafify (SmallEtale.topology B S.obj S.property)
      (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) x y h⟩

/-- Every section of the monoidal unit is locally the image of a constant: the sheafification
unit with module coefficients is locally surjective. -/
public theorem isLocallySurjective_constantToForgetTensorUnit :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ) := by
  have : Presheaf.IsLocallySurjective (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property)
        (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) :=
    Stacks.ConstantSheaf.isLocallySurjective_toSheafify_moduleCat _ _ _
  exact ⟨fun s => Presheaf.imageSieve_mem _
    (toSheafify (SmallEtale.topology B S.obj S.property)
      (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) s⟩

/-- **The abelian sheaf underlying the monoidal unit is the constant abelian sheaf with value
`Λ`.** The comparison `AlgebraicGeometry.SmallEtale.constantToForgetTensorUnit` is locally
bijective, hence an isomorphism after sheafification. -/
public def constantSheafIsoForgetTensorUnit :
    (constantSheaf (SmallEtale.topology B S.obj S.property)
          AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of Λ) ≅
      (forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)) := by
  haveI := isLocallyInjective_constantToForgetTensorUnit.{u, v} B S Λ
  haveI := isLocallySurjective_constantToForgetTensorUnit.{u, v} B S Λ
  have hfac : toSheafify (SmallEtale.topology B S.obj S.property)
        ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj (AddCommGrpCat.of Λ)) ≫
      sheafifyLift (SmallEtale.topology B S.obj S.property)
        (constantToForgetTensorUnit.{u, v} B S Λ)
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property =
      constantToForgetTensorUnit.{u, v} B S Λ :=
    toSheafify_sheafifyLift _ _ _
  have hinj : Presheaf.IsLocallyInjective (SmallEtale.topology B S.obj S.property)
      (sheafifyLift (SmallEtale.topology B S.obj S.property)
        (constantToForgetTensorUnit.{u, v} B S Λ)
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property) := by
    rw [← Presheaf.comp_isLocallyInjective_iff (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property)
        ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj (AddCommGrpCat.of Λ))), hfac]
    infer_instance
  have hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S.obj S.property)
      (sheafifyLift (SmallEtale.topology B S.obj S.property)
        (constantToForgetTensorUnit.{u, v} B S Λ)
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property) := by
    rw [← Presheaf.comp_isLocallySurjective_iff (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property)
        ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj (AddCommGrpCat.of Λ))), hfac]
    infer_instance
  haveI : IsIso (ObjectProperty.homMk (sheafifyLift (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property) :
      (presheafToSheaf (SmallEtale.topology B S.obj S.property)
            AddCommGrpCat.{max (u + 1) v}).obj
          ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj (AddCommGrpCat.of Λ)) ⟶
        (forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hinj, hsurj⟩
  have e : (presheafToSheaf (SmallEtale.topology B S.obj S.property)
          AddCommGrpCat.{max (u + 1) v}).obj
        ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj (AddCommGrpCat.of Λ)) ≅
      (forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)) :=
    asIso (ObjectProperty.homMk (sheafifyLift (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property))
  exact e

/-- The identification of the constant abelian sheaf with the monoidal unit sends the
sheafification-unit image of `a : Λ` to the sheafification-unit image of `a` taken in
`Λ`-modules. -/
public theorem constantSheafIsoForgetTensorUnit_unit
    (T : (SmallEtale B S.obj S.property)ᵒᵖ) (a : Λ) :
    ((constantSheafIsoForgetTensorUnit.{u, v} B S Λ).hom.hom.app T)
        ((toSheafify (SmallEtale.topology B S.obj S.property)
          ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj
            (AddCommGrpCat.of Λ))).app T a) =
      (toSheafify (SmallEtale.topology B S.obj S.property)
        (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))).app T a := by
  have h := congrArg (fun f => f.app T a)
    (toSheafify_sheafifyLift (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property)
  show (sheafifyLift (SmallEtale.topology B S.obj S.property)
      (constantToForgetTensorUnit.{u, v} B S Λ)
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))).property).app T
    (((toSheafify (SmallEtale.topology B S.obj S.property)
      ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj
        (AddCommGrpCat.of Λ))).app T) a) = _
  exact h

/-- **The abelian sheaf underlying the monoidal unit is the sheaf of locally constant
`Λ`-valued functions.** Both are the constant abelian sheaf with value `Λ`: the first by
`AlgebraicGeometry.SmallEtale.constantSheafIsoForgetTensorUnit`, the second by Stacks 03P5 in
the form `AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale`. -/
public def forgetTensorUnitIsoLocallyConstantSheafAb :
    (forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)) ≅
      locallyConstantSheafAb.{u, v} B S.obj S.property Λ :=
  (constantSheafIsoForgetTensorUnit.{u, v} B S Λ).symm ≪≫
    constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v} B S.obj S.property Λ

/-- **The identification on sections.** The sheafification-unit image of `a : Λ` in the monoidal
unit goes to the constant function with value `a`. -/
public theorem forgetTensorUnitIsoLocallyConstantSheafAb_toSheafify
    (T : (SmallEtale B S.obj S.property)ᵒᵖ) (a : Λ) :
    (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S Λ).hom.hom.app T
        ((toSheafify (SmallEtale.topology B S.obj S.property)
          (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
            ModuleCat.{max (u + 1) v} Λ))).app T a) =
      LocallyConstant.const ((SmallEtale.toScheme B S.obj S.property).obj T.unop) a := by
  have h1 : ((constantSheafIsoForgetTensorUnit.{u, v} B S Λ).inv.hom.app T)
        ((toSheafify (SmallEtale.topology B S.obj S.property)
          (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
            ModuleCat.{max (u + 1) v} Λ))).app T a) =
      (toSheafify (SmallEtale.topology B S.obj S.property)
        ((Functor.const (SmallEtale B S.obj S.property)ᵒᵖ).obj
          (AddCommGrpCat.of Λ))).app T a := by
    rw [← constantSheafIsoForgetTensorUnit_unit.{u, v} B S Λ T a]
    exact Iso.hom_inv_id_apply
      (((sheafToPresheaf (SmallEtale.topology B S.obj S.property)
        AddCommGrpCat.{max (u + 1) v}).mapIso
          (constantSheafIsoForgetTensorUnit.{u, v} B S Λ)).app T) _
  show (constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v}
      B S.obj S.property Λ).hom.hom.app T
    (((constantSheafIsoForgetTensorUnit.{u, v} B S Λ).inv.hom.app T)
      ((toSheafify (SmallEtale.topology B S.obj S.property)
        (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
          ModuleCat.{max (u + 1) v} Λ))).app T a)) = _
  rw [h1]
  exact constantSheafIsoLocallyConstantMapsAb_smallEtale_unit.{u, v} B S.obj S.property Λ T a

end TensorUnit

section Stalk

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall
attribute [local instance] modStalkMonoidal

variable (B : BigEtaleSite.{u}) (S : B.Scheme) (Λ : Type (max (u + 1) v)) [CommRing Λ]
  (t : GeometricPoint S.obj)

/-- **The unit constraint of the monoidal stalk functor is a germ of the sheafification unit.**
Over any étale neighbourhood of the geometric point, `ε` factors as the sheafification unit of
the constant presheaf of `Λ`-modules followed by the canonical map into the stalk. -/
public theorem modStalk_ε_eq (W : SmallEtale B S.obj S.property)
    (q : (geometricPointSitePoint B S.obj S.property t).fiber.obj W) :
    Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) =
      (toSheafify (SmallEtale.topology B S.obj S.property)
            (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
              ModuleCat.{max (u + 1) v} Λ))).app (op W) ≫
        (geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q
          (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)).obj := by
  have h : Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) =
      Functor.LaxMonoidal.ε ((geometricPointSitePoint B S.obj S.property t).presheafFiber
          (A := ModuleCat.{max (u + 1) v} Λ)) ≫
        ((geometricPointSitePoint B S.obj S.property t).presheafFiber
            (A := ModuleCat.{max (u + 1) v} Λ)).map
          (toSheafify (SmallEtale.topology B S.obj S.property)
            (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) ≫
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map (𝟙 _) :=
    rfl
  have h' : ((geometricPointSitePoint B S.obj S.property t).presheafFiber
          (A := ModuleCat.{max (u + 1) v} Λ)).map
        (toSheafify (SmallEtale.topology B S.obj S.property)
          (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) ≫
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map (𝟙 _) =
      ((geometricPointSitePoint B S.obj S.property t).presheafFiber
          (A := ModuleCat.{max (u + 1) v} Λ)).map
        (toSheafify (SmallEtale.topology B S.obj S.property)
          (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) :=
    (congrArg (fun g => ((geometricPointSitePoint B S.obj S.property t).presheafFiber
        (A := ModuleCat.{max (u + 1) v} Λ)).map
          (toSheafify (SmallEtale.topology B S.obj S.property)
            (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) ≫ g)
      (CategoryTheory.Functor.map_id
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) _)).trans (Category.comp_id _)
  refine h.trans ((congrArg (fun g =>
    Functor.LaxMonoidal.ε ((geometricPointSitePoint B S.obj S.property t).presheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)) ≫ g) h').trans ?_)
  rw [(geometricPointSitePoint B S.obj S.property t).toPresheafFiber_ε W q]
  exact (geometricPointSitePoint B S.obj S.property t).toPresheafFiber_naturality
    (toSheafify (SmallEtale.topology B S.obj S.property)
      (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ))) W q

/-- The unit constraint of the monoidal stalk functor, on an element: `a : Λ` goes to the germ
at the geometric point of the sheafification-unit image of `a`. -/
public theorem modStalk_ε_apply (W : SmallEtale B S.obj S.property)
    (q : (geometricPointSitePoint B S.obj S.property t).fiber.obj W) (a : Λ) :
    Functor.LaxMonoidal.ε (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) a =
      (geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q
        (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ)).obj
        ((toSheafify (SmallEtale.topology B S.obj S.property)
          (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
            ModuleCat.{max (u + 1) v} Λ))).app (op W) a) :=
  ConcreteCategory.congr_hom (modStalk_ε_eq.{u, v} B S Λ t W q) a

/-- **The two `Λ`-module structures on a stalk agree on germs.** The comparison
`AlgebraicGeometry.SmallEtale.moduleEtaleStalkIso` carries the germ of a section formed in the
colimit of `Λ`-modules to the germ of the same section formed in abelian groups. -/
public theorem moduleEtaleStalkIso_inv_app_toPresheafFiber
    (G : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) (W : SmallEtale B S.obj S.property)
    (q : (geometricPointSitePoint B S.obj S.property t).fiber.obj W) (m : G.obj.obj (op W)) :
    (moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ S t).inv.app G
        ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q G.obj m) =
      (geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj G).obj m := by
  let : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v,
      max (u + 1) v, max (u + 1) v} Λ
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) :=
    preservesColimitsOfSize_shrink.{u, max (u + 1) v, u, max (u + 1) v} _
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) :=
    ⟨fun _ => inferInstance⟩
  have h : ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app G.obj
      ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj G).obj m) =
      (geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q G.obj m :=
    ConcreteCategory.congr_hom
      ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber_presheafFiberCompIso_hom_app
        (F := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) W q G.obj) m
  show ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app G.obj
      ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q G.obj m) = _
  rw [← h]
  exact Iso.hom_inv_id_apply
    (((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).app G.obj) _

/-- **The étale stalk of a morphism of abelian sheaves, on a germ.** This is Mathlib's
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality` read on an element, at
the coefficients used here; the composite form the `elementwise` attribute produces does not
rewrite against a goal in which the two maps are applied one after the other. -/
public theorem presheafFiber_map_toPresheafFiber
    (P Q : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (g : P ⟶ Q)
    (W : SmallEtale B S.obj S.property)
    (q : (geometricPointSitePoint B S.obj S.property t).fiber.obj W) (m : P.obj (op W)) :
    ((geometricPointSitePoint B S.obj S.property t).presheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).map g
        ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q P m) =
      (geometricPointSitePoint B S.obj S.property t).toPresheafFiber W q Q (g.app (op W) m) :=
  ConcreteCategory.congr_hom
    ((geometricPointSitePoint B S.obj S.property t).toPresheafFiber_naturality g W q) m

/-- **The monoidal and the concrete identification of the stalk of the monoidal unit with `Λ`
agree.** The unit constraint `ε` of the stalk functor, read through the identification of the
two `Λ`-module structures on a stalk and the stalk of
`AlgebraicGeometry.SmallEtale.forgetTensorUnitIsoLocallyConstantSheafAb`, is inverse to
evaluation of a locally constant function at the geometric point: both send `a : Λ` to the germ
of the constant function with value `a`. -/
public theorem etaleStalkLocallyConstantMapsAbIso_tensorUnit_eps (a : Λ) :
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t Λ).hom
        (((geometricPointSitePoint B S.obj S.property t).presheafFiber
              (A := AddCommGrpCat.{max (u + 1) v})).map
          (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S Λ).hom.hom
          ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ S t).inv.app
            (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))
            (Functor.LaxMonoidal.ε
              (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) a))) =
      a := by
  obtain ⟨q⟩ : Nonempty ((geometricPointSitePoint B S.obj S.property t).fiber.obj
      (SmallEtale.final B S.obj S.property)) :=
    ⟨SmallEtale.finalLift B S.obj S.property t⟩
  rw [modStalk_ε_apply.{u, v} B S Λ t (SmallEtale.final B S.obj S.property) q a,
    moduleEtaleStalkIso_inv_app_toPresheafFiber.{u, v} B S Λ t
      (𝟙_ (ModuleSheaf.{u, v, max (u + 1) v} B S Λ))
      (SmallEtale.final B S.obj S.property) q _]
  exact Eq.trans
    (congrArg (fun z =>
        (etaleStalkLocallyConstantMapsAbIso.{u, v} B S.obj S.property t Λ).hom z)
      ((presheafFiber_map_toPresheafFiber.{u, v} B S t _ _
            (forgetTensorUnitIsoLocallyConstantSheafAb.{u, v} B S Λ).hom.hom
            (SmallEtale.final B S.obj S.property) q
            ((toSheafify (SmallEtale.topology B S.obj S.property)
              (𝟙_ ((SmallEtale B S.obj S.property)ᵒᵖ ⥤
                ModuleCat.{max (u + 1) v} Λ))).app
                  (op (SmallEtale.final B S.obj S.property)) a)).trans
        (congrArg (fun y =>
            (geometricPointSitePoint B S.obj S.property t).toPresheafFiber
              (SmallEtale.final B S.obj S.property) q
              (locallyConstantSheafAb.{u, v} B S.obj S.property Λ).obj y)
          (forgetTensorUnitIsoLocallyConstantSheafAb_toSheafify.{u, v} B S Λ
            (op (SmallEtale.final B S.obj S.property)) a))))
    (etaleStalkLocallyConstantMapsAbIso_etaleGerm.{u, v} B S.obj S.property t Λ
      (SmallEtale.final B S.obj S.property) q
      (LocallyConstant.const ((SmallEtale.toScheme B S.obj S.property).obj
        (SmallEtale.final B S.obj S.property)) a))

end Stalk

end AlgebraicGeometry.SmallEtale

end
