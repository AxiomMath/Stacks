module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplexBounded

/-!
# The change of coefficients on the small étale site reflects vanishing

Reading a sheaf of `Λ`-modules on the small étale site of a scheme `X` as a sheaf of modules
over the constant coefficient ring sheaf of Stacks 03TR is
`AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor`, the sheafification of
`AlgebraicGeometry.modulePresheafOverConstantCoefficients`. That presheaf of modules is already
a sheaf, so the sheafification unit is an isomorphism and the change of coefficients leaves the
modules of sections unchanged up to the lift of universes. Vanishing therefore transports
backwards across the functor, over a slice of the site as well as globally.

## Main results

* `AlgebraicGeometry.isSheaf_modulePresheafOverConstantCoefficients`: the presheaf of modules
  over the constant presheaf of rings attached to a sheaf of `Λ`-modules is a sheaf.
* `AlgebraicGeometry.isIso_modulePresheafOverConstantCoefficients_unit`: hence the
  sheafification unit at it is an isomorphism.
* `AlgebraicGeometry.isZero_of_isZero_moduleSheafOverConstantCoefficients`: the change of
  coefficients reflects zero objects.
* `AlgebraicGeometry.isZero_overPullback_of_isZero_over_moduleSheafOverConstantCoefficients`:
  a sheaf of `Λ`-modules whose change of coefficients vanishes over an object of the site
  already vanishes over that object.
* `AlgebraicGeometry.isZero_of_isZero_over_moduleSheafOverConstantCoefficients_of_connectedSpace`:
  the composite of that transport with
  `AlgebraicGeometry.isZero_of_isZero_overPullback_of_connectedSpace`, which spreads a local
  vanishing over a connected base.
* `AlgebraicGeometry.moduleSheafOverConstantCoefficientsFunctor_faithful` and
  `AlgebraicGeometry.isIso_of_isIso_map_moduleSheafOverConstantCoefficients`: the change of
  coefficients is faithful, and conservative on a balanced category of sheaves.

## Implementation notes

The sheaf condition for the lifted presheaf of modules is
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` applied to the universe lift followed by the
forgetful functor to abelian groups, which is the composite whose underlying presheaf is the
one in question. Preservation of limits indexed by the small étale site, whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u`, needs the size hypothesis
`UnivLE.{u + 1, w}` on the universe `w` of the module sections. The hypothesis is stated rather
than derived; the boundedness argument of Stacks 09BI uses these results at `w = u + 1`, where
it holds by `UnivLE.self`.

No point of the site and no stalk comparison enters: the modules of sections are themselves
unchanged, which is a stronger statement than equality of stalks and needs none of the
enough-points theory.

There is no natural isomorphism relating `SheafOfModules.overFunctor` composed with the change
of coefficients to `CategoryTheory.GrothendieckTopology.overPullback`, because the structure
sheaf of the slice of `AlgebraicGeometry.constantCoefficientRingedSite` over an object is the
restriction of the constant coefficient ring sheaf and not the constant coefficient ring sheaf
of the slice site, so the change of coefficients is not defined on the slice. The transport of
vanishing over a slice is obtained from the unchanged sections instead.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace AlgebraicGeometry

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- A left adjoint is injective on a hom set whose target has an invertible unit, the unit being
natural and cancellable. -/
private lemma map_injective_of_isIso_unit {A : Type*} [Category A] {D : Type*} [Category D]
    {L : A ⥤ D} {R : D ⥤ A} (adj : L ⊣ R) {P Q : A} [IsIso (adj.unit.app Q)] :
    Function.Injective (fun f : P ⟶ Q => L.map f) := by
  intro f g hfg
  refine (cancel_mono (adj.unit.app Q)).mp ?_
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg]
  exact congrArg (fun ψ => adj.unit.app P ≫ R.map ψ) hfg

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [UnivLE.{u + 1, w}]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))

/-- The presheaf of modules over the constant presheaf of rings attached to a sheaf of
`Λ`-modules is a sheaf: its underlying presheaf of abelian groups is the given sheaf composed
with a universe lift and a forgetful functor, both of which preserve limits. -/
theorem isSheaf_modulePresheafOverConstantCoefficients :
    Presheaf.IsSheaf (SmallEtale.topology B X.obj X.property)
      (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F).presheaf := by
  have : UnivLE.{u, w} := UnivLE.trans.{u, u + 1, w}
  let G : ModuleCat.{w} Λ ⥤ AddCommGrpCat.{max (u + 1) w r} :=
    ModuleCat.uliftFunctor.{max (u + 1) r} Λ ⋙
      forget₂ (ModuleCat.{max (u + 1) w r} Λ) AddCommGrpCat.{max (u + 1) w r}
  have : PreservesLimitsOfSize.{w, w} G := by
    dsimp only [G]
    infer_instance
  have : PreservesLimitsOfSize.{u, u + 1} G :=
    preservesLimitsOfSize_of_univLE.{w, w, u, u + 1} G
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ G F.property

/-- The unit of the sheafification adjunction at the presheaf of modules over the constant
presheaf of rings is an isomorphism, that presheaf being a sheaf already. -/
theorem isIso_modulePresheafOverConstantCoefficients_unit :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
      (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
        (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F)) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
        (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
          (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F))) :=
    CategoryTheory.isIso_toSheafify _
      (isSheaf_modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F)
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-- The sheafification unit at the presheaf of modules over the constant presheaf of rings is
injective on the sections over every object of the small étale site. -/
theorem injective_modulePresheafOverConstantCoefficients_unit_app
    (U : (SmallEtale B X.obj X.property)ᵒᵖ) :
    Function.Injective
      (((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
        (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
          (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F)).app U) := by
  have := isIso_modulePresheafOverConstantCoefficients_unit.{u, w, r} B X Λ F
  have hU : IsIso ((PresheafOfModules.evaluation _ U).map
      ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
        (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
          (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F))) := inferInstance
  exact ((ConcreteCategory.isIso_iff_bijective _).mp hU).1

/-- A section of a sheaf of `Λ`-modules whose image in the change of coefficients is killed by
the zero morphism of that image is zero. -/
private lemma eq_zero_of_apply_unit_eq_zero
    (U : (SmallEtale B X.obj X.property)ᵒᵖ) (x : F.obj.obj U)
    (h : ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
      (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
        (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F)).app U
          (ULift.up x) = 0) :
    x = 0 := by
  have hinj := injective_modulePresheafOverConstantCoefficients_unit_app.{u, w, r} B X Λ F U
  refine congrArg ULift.down (hinj (h.trans ?_))
  exact (map_zero (((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
    (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
      (modulePresheafOverConstantCoefficients.{u, w, r} B X Λ F)).app U).hom).symm

/-- **The change of coefficients reflects zero objects.** A sheaf of `Λ`-modules on the small
étale site whose reading over the constant coefficient ring sheaf is zero is itself zero. -/
theorem isZero_of_isZero_moduleSheafOverConstantCoefficients
    (h : IsZero ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) :
    IsZero F := by
  refine (IsZero.iff_id_eq_zero _).mpr (Sheaf.hom_ext ?_)
  ext U x
  refine eq_zero_of_apply_unit_eq_zero.{u, w, r} B X Λ F U x ?_
  have hsec := congrArg (fun f => f.val.app U) (h.eq_of_src (𝟙 _) 0)
  exact ConcreteCategory.congr_hom hsec _

/-- **Vanishing of the change of coefficients over an object of the small étale site implies
vanishing over that object.** The restriction of a sheaf of `Λ`-modules to the slice over an
object is zero as soon as the restriction of its reading over the constant coefficient ring
sheaf is. -/
theorem isZero_overPullback_of_isZero_over_moduleSheafOverConstantCoefficients
    (V : SmallEtale B X.obj X.property)
    (h : IsZero ((SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O) V).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))) :
    IsZero (((SmallEtale.topology B X.obj X.property).overPullback
      (ModuleCat.{w} Λ) V).obj F) := by
  refine (IsZero.iff_id_eq_zero _).mpr (Sheaf.hom_ext ?_)
  ext W x
  refine eq_zero_of_apply_unit_eq_zero.{u, w, r} B X Λ F (op W.unop.left) x ?_
  have hsec := congrArg (fun f => f.val.app W) (h.eq_of_src (𝟙 _) 0)
  exact ConcreteCategory.congr_hom hsec _

/-- **A locally constant sheaf of `Λ`-modules on the small étale site of a connected scheme
whose change of coefficients vanishes over an object with nonempty image is zero.** The
composite of the transport of vanishing with
`AlgebraicGeometry.isZero_of_isZero_overPullback_of_connectedSpace`. -/
theorem isZero_of_isZero_over_moduleSheafOverConstantCoefficients_of_connectedSpace
    [ConnectedSpace X.obj]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
    [∀ U : SmallEtale B X.obj X.property,
      HasSheafify ((SmallEtale.topology B X.obj X.property).over U) (ModuleCat.{w} Λ)]
    [HasProducts.{max u v} (ModuleCat.{w} Λ)]
    [HasColimitsOfSize.{max u v, max u v} (ModuleCat.{w} Λ)]
    (hF : Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B X.obj X.property) F)
    (V : SmallEtale B X.obj X.property) (z : X.obj)
    (hz : z ∈ (siteEtaleImageOpen B X.obj X.property V : Set X.obj))
    (h : IsZero ((SheafOfModules.overFunctor.{max (u + 1) w r}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ).O) V).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))) :
    IsZero F :=
  isZero_of_isZero_overPullback_of_connectedSpace.{w, v, r, u}
    B X.obj X.property Λ F hF V z hz
    (isZero_overPullback_of_isZero_over_moduleSheafOverConstantCoefficients.{u, w, r}
      B X Λ F V h)

/-! ### Faithfulness and conservativity -/

/-- The presheaf-level change of coefficients is faithful, being a universe lift and a
restriction of scalars on the module of sections over every object. -/
instance modulePresheafOverConstantCoefficientsFunctor_faithful :
    (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).Faithful where
  map_injective {M N} {f g} h := by
    refine Sheaf.hom_ext ?_
    ext U x
    refine congrArg ULift.down (ConcreteCategory.congr_hom (congrArg
      (fun ψ : (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj M ⟶
        (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj N =>
          ψ.app U) h) (ULift.up x))

/-- **The change of coefficients is faithful.** The presheaf-level reading is faithful and the
sheafification unit at its values is invertible, so sheafifying loses no morphisms. -/
instance moduleSheafOverConstantCoefficientsFunctor_faithful :
    (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).Faithful where
  map_injective {M N} {f g} h := by
    have : IsIso ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
        (constantCoefficientRingMap.{u, w, r} B X Λ)).unit.app
          ((modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj N)) :=
      isIso_modulePresheafOverConstantCoefficients_unit.{u, w, r} B X Λ N
    have key : (PresheafOfModules.sheafification.{max (u + 1) w r}
        (constantCoefficientRingMap.{u, w, r} B X Λ)).map
          ((modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f) =
        (PresheafOfModules.sheafification.{max (u + 1) w r}
          (constantCoefficientRingMap.{u, w, r} B X Λ)).map
            ((modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map g) := h
    exact (modulePresheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map_injective
      (map_injective_of_isIso_unit
        (PresheafOfModules.sheafificationAdjunction.{max (u + 1) w r}
          (constantCoefficientRingMap.{u, w, r} B X Λ)) key)

/-- **The change of coefficients is conservative.** It is faithful, hence reflects monomorphisms
and epimorphisms, and the category of sheaves of `Λ`-modules is balanced. -/
theorem isIso_of_isIso_map_moduleSheafOverConstantCoefficients
    [Balanced (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))]
    {M N : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)} (f : M ⟶ N)
    (h : IsIso ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).map f)) :
    IsIso f := by
  exact isIso_of_reflects_iso f (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ)

end AlgebraicGeometry

end
