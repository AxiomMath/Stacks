module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineCounitBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TensorFunctorAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf

/-!
# The unit of `g_{QCoh,*}𝒪_U` splits after pulling back to `U`

Let `g : U ⟶ 𝒳` be an affine, flat and surjective 1-morphism from a scheme to an algebraic
stack, and `G = g_{QCoh,*}𝒪_U` the commutative algebra of Stacks 0GRK.  The proof of Stacks 0GRL
uses that the unit `1 : 𝒪_𝒳 ⟶ G` "becomes the inclusion of a direct summand upon pullback to
`U`".  On sections this is `AlgebraicGeometry.Stack.HasFlatLocalUnitRetractions`: for a flat object
`y` of `𝒳` over an affine scheme `T`, the object `y' = g (r y)` lying over `U ×_𝒳 T` maps to `y`
by the counit `ε_y` of `g ⊣ r`, the ring map `𝒪(y) ⟶ 𝒪(y')` is faithfully flat (the projection
`U ×_𝒳 T ⟶ T` is affine, flat and surjective), and restriction along `g(η_{r y}) : y' ⟶ g (r y')`,
the diagonal of `U ×_𝒳 U ×_𝒳 T ⟶ U ×_𝒳 T`, is an `𝒪(y')`-linear retraction
`G(y') = 𝒪(U ×_𝒳 U ×_𝒳 T) ⟶ 𝒪(y')` of the unit, by the triangle identity of `g ⊣ r`.

With this, Stacks 0GRL follows from the argument
`AlgebraicGeometry.Stack.universallyInjective_algebraMap_tensorFunctor_of_unitRetractions` and the
one remaining input, Stacks 0GRF (every quasi-coherent module on a Noetherian algebraic stack is
a filtered colimit of coherent ones), taken in the form `hgen` that Stacks 0GRJ uses.

## Main results

* `AlgebraicGeometry.Stack.unit_hom_val_app_affineQuasicoherentStructureSheaf`: the unit of
  `g_{QCoh,*}𝒪_U` is `1` on sections.
* `AlgebraicGeometry.Stack.hasFlatLocalUnitRetractions_affineQuasicoherentStructureSheaf`: the
  splitting of the unit for `g` affine, flat and surjective.
* `AlgebraicGeometry.Stack.universallyInjective_affineTensorAlgebra_of_coherentGeneration`:
  Stacks 0GRL with the input Stacks 0GRF as the hypothesis `hgen`.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRL](https://stacks.math.columbia.edu/tag/0GRL)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj

universe u w w'

namespace AlgebraicGeometry.Stack

/-- **The triangle identity on rings of functions.**  For an adjunction `F ⊣ G` and a presheaf of
commutative rings `RC` on the source which is the restriction of `RD` on the target, restriction
along the counit at `F X` followed by restriction along the unit at `X` is the identity of
`RD(F X)`. -/
theorem counit_comp_unit_eq_id_of_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {RC : Cᵒᵖ ⥤ CommRingCat.{u}} {RD : Dᵒᵖ ⥤ CommRingCat.{u}}
    (h : RC = F.op ⋙ RD) (X : C) :
    (Functor.whiskerRight (NatTrans.op adj.counit) RD ≫
        eqToHom (congrArg (fun K => G.op ⋙ K) h).symm).app (op (F.obj X)) ≫
      RC.map (adj.unit.app X).op ≫ (eqToHom h).app (op X) = 𝟙 _ := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, NatTrans.id_app, Functor.whiskerRight_app,
    NatTrans.op_app, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  refine (congrArg (fun k => RD.map (adj.counit.app (F.obj X)).op ≫ k)
    (Category.comp_id (RD.map (F.map (adj.unit.app X)).op))).trans ?_
  rw [← RD.map_comp, ← op_comp]
  refine (congrArg (fun k => RD.map k.op) (adj.left_triangle_components X)).trans ?_
  rw [op_id, RD.map_id]
  rfl

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory monObjAffineQuasicoherentStructureSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- **The unit of `g_{QCoh,*}𝒪_U` is `1` on sections**: at every object `x` of `𝒳` the unit
`𝒪_𝒳 ⟶ g_{QCoh,*}𝒪_U` sends `1 ∈ 𝒪(x)` to `1 ∈ 𝒪_U(r x)`. -/
theorem unit_hom_val_app_affineQuasicoherentStructureSheaf (x : 𝒳.val.val.obj) :
    PresheafOfModules.toRingElem (pushforwardCommRingHom g hg)
      (η[affineQuasicoherentStructureSheaf g hg].hom.val.app (op x)
        (1 : fibredSectionRing B S hS 𝒳.val.val.p x)) = 1 := by
  let O := (AlgebraicStacks.fppfStructureSheaf B S hS 𝒳).obj
  let hO := AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳
  let φ : _root_.SheafOfModules.unit (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒳) ⟶
      affinePushforwardStructureSheaf g hg :=
    ⟨PresheafOfModules.algebraPresheafOne (pushforwardCommRingHom g hg)⟩
  have h1 : η[affineQuasicoherentStructureSheaf g hg].hom =
      (Stacks.SheafOfModules.sheafifyValIso O hO
          (_root_.SheafOfModules.unit (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒳))).inv ≫
        (Stacks.SheafOfModules.sheafifyFunctor O hO).map φ.val ≫
          (Stacks.SheafOfModules.sheafifyValIso O hO (affinePushforwardStructureSheaf g hg)).hom :=
    rfl
  rw [h1, Stacks.SheafOfModules.sheafifyFunctor_map_comp_sheafifyValIso_hom O hO φ]
  have h2 : (Stacks.SheafOfModules.sheafifyValIso O hO
          (_root_.SheafOfModules.unit (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒳))).inv ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO
          (_root_.SheafOfModules.unit (AlgebraicStacks.fppfStructureRingSheaf B S hS 𝒳))).hom ≫ φ =
      φ :=
    Iso.inv_hom_id_assoc _ _
  refine (congrArg (fun k => PresheafOfModules.toRingElem (pushforwardCommRingHom g hg)
    ((k.val.app (op x)).hom (1 : fibredSectionRing B S hS 𝒳.val.val.p x))) h2).trans ?_
  exact (PresheafOfModules.algebraPresheafOne_app (pushforwardCommRingHom g hg) (op x) 1).trans
    (map_one _)

/-- The ring map `G(y') = 𝒪_U(r y') ⟶ 𝒪(y')` for `y' = g (r y)`: restriction along the unit
`r y ⟶ r (g (r y))` of `g ⊣ r`, read in the functions of `y'` through `𝒪_U = 𝒪_𝒳 ∘ g`.  It is the
restriction along the diagonal of `U ×_𝒳 U ×_𝒳 T ⟶ U ×_𝒳 T`. -/
noncomputable def affineUnitRetractionRingHom (y : 𝒳.val.val.obj) :
    (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj.obj
        (op ((affineRightAdjoint g hg).obj
          (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) ⟶
      (AlgebraicStacks.fppfStructureSheaf B S hS 𝒳).obj.obj
        (op (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y))) :=
  (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj.map
      ((affineAdjunction g hg).unit.app ((affineRightAdjoint g hg).obj y)).op ≫
    (eqToHom (structureSheaf_obj_eq_homFunctor g)).app (op ((affineRightAdjoint g hg).obj y))

/-- The retraction of the comorphism of `r`: `𝒪(y') ⟶ G(y') ⟶ 𝒪(y')` is the identity. -/
theorem affineUnitRetractionRingHom_pushforwardCommRingHom (y : 𝒳.val.val.obj)
    (a : (AlgebraicStacks.fppfStructureSheaf B S hS 𝒳).obj.obj
      (op (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))) :
    (affineUnitRetractionRingHom g hg y).hom
      (((pushforwardCommRingHom g hg).app
        (op (g.hom.hom.toFunctor.obj ((affineRightAdjoint g hg).obj y)))).hom a) = a := by
  exact congrArg (fun k => k.hom a) (counit_comp_unit_eq_id_of_eq (affineAdjunction g hg)
    (structureSheaf_obj_eq_homFunctor g) ((affineRightAdjoint g hg).obj y))

/-- **Stacks 0GRL: the unit of `g_{QCoh,*}𝒪_U` splits after pulling back to `U`.**  For an affine,
flat and surjective `g : U ⟶ 𝒳`, over every flat object `y` of `𝒳` lying over an affine scheme
`T` there are the flat object `y' = g (r y)` over the affine scheme `U ×_𝒳 T`, the counit
`y' ⟶ y` with faithfully flat ring map `𝒪(T) ⟶ 𝒪(U ×_𝒳 T)`, and an `𝒪(y')`-linear retraction
`G(y') ⟶ 𝒪(y')` of the unit of `G = g_{QCoh,*}𝒪_U`, restriction along the diagonal. -/
theorem hasFlatLocalUnitRetractions_affineQuasicoherentStructureSheaf
    (hflat : AlgebraicStacks.IsFlat B S hS g) (hsurj : IsSurjective B S hS g) :
    HasFlatLocalUnitRetractions (affineQuasicoherentStructureSheaf g hg) := by
  intro y hy hyaff
  let r := affineRightAdjoint g hg
  let ε := (affineAdjunction g hg).counit.app y
  let y' := g.hom.hom.toFunctor.obj (r.obj y)
  let f : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y') ⟶
      (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) :=
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ε)
  have : _root_.AlgebraicGeometry.IsAffineHom f := isAffineHom_map_affineAdjunction_counit g hg y
  have : _root_.AlgebraicGeometry.Flat f := flat_map_affineAdjunction_counit g hg hflat y
  have : _root_.AlgebraicGeometry.Surjective f :=
    surjective_map_affineAdjunction_counit g hg hsurj y
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) := hyaff
  have hy'aff : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y')) :=
    isAffine_of_isAffineHom f
  refine ⟨g.hom.hom.toFunctor.obj (r.obj y), ε,
    flatObject_of_flat B S hS 𝒳 ε (flat_map_affineAdjunction_counit g hg hflat y) hy, hy'aff,
    ?_, ?_⟩
  · exact @faithfullyFlat_gamma_of_flat_of_surjective _ _ f _ _ _ _
      (fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) ε) rfl
  · let _ := fibredSectionsModule 𝒳.val.isFiberedInGroupoids
      (affineQuasicoherentStructureSheaf g hg).obj (g.hom.hom.toFunctor.obj (r.obj y))
    let σ := affineUnitRetractionRingHom g hg y
    refine ⟨{ toFun := fun m => σ.hom (PresheafOfModules.toRingElem (pushforwardCommRingHom g hg) m)
              map_add' := fun m m' => σ.hom.map_add _ _
              map_smul' := fun a m => ?_ }, ?_⟩
    · have key : ∀ (b : (AlgebraicStacks.fppfStructureSheaf B S hS 𝒳).obj.obj (op y'))
          (m' : (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj.obj
            (op (r.obj y'))),
          σ.hom (((pushforwardCommRingHom g hg).app (op y')).hom b * m') = b * σ.hom m' :=
        fun b m' => by rw [map_mul, affineUnitRetractionRingHom_pushforwardCommRingHom]
      exact key a (PresheafOfModules.toRingElem (pushforwardCommRingHom g hg) m)
    · show σ.hom (PresheafOfModules.toRingElem (pushforwardCommRingHom g hg)
        (η[affineQuasicoherentStructureSheaf g hg].hom.val.app (op y')
          (1 : fibredSectionRing B S hS 𝒳.val.val.p y'))) = 1
      rw [unit_hom_val_app_affineQuasicoherentStructureSheaf]
      exact map_one σ.hom

/-- **Stacks 0GRL, with Stacks 0GRF as the input `hgen`.**  Let `𝒳` be a Noetherian algebraic
stack with affine (absolute) diagonal, `R` a ring and `F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact
tensor functor which commutes with direct sums.  Let `g : U ⟶ 𝒳` be a flat and surjective
morphism from an affine scheme `U`.  Then `g` is affine, and the structure map `R ⟶ C` of the
commutative `R`-algebra `C = F(g_{QCoh,*}𝒪_U)` of Stacks 0GRK
(`AlgebraicGeometry.Stack.affineTensorAlgebra`) is universally injective.

The hypothesis `hgen` is Stacks 0GRF in the form in which Stacks 0GRJ uses it: every
quasi-coherent module is a filtered colimit of coherent ones.  Everything else of the source's
proof is proved: the factorization of the unit through a coherent `𝓕` (Stacks 0GQZ), the dual
`hom(𝓕, 𝒪_𝒳)` of Stacks 0GQN with its evaluation, and the surjectivity of evaluation at the
factorization, from the splitting of the unit after pulling back to `U`
(`AlgebraicGeometry.Stack.hasFlatLocalUnitRetractions_affineQuasicoherentStructureSheaf`). -/
theorem universallyInjective_affineTensorAlgebra_of_coherentGeneration
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) (hUaff : IsAffineOver B S hS U)
    {R : Type u} [CommRing R]
    (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Braided]
    [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hsurj : IsSurjective B S hS g)
    (hgen : ∀ M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids, (coherentQuasicoherent B S hS 𝒳).ind.{u} M) :
    ∃ hg : AlgebraicStacks.IsAffineHom B S hS g,
      Algebra.UniversallyInjective R (affineTensorAlgebra g hg F) := by
  have hg : AlgebraicStacks.IsAffineHom B S hS g :=
    AlgebraicStacks.isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS
      (contains_terminalScheme B) hUaff hΔ g
  have := isCommMonObjAffineQuasicoherentStructureSheaf g hg
  exact ⟨hg, universallyInjective_algebraMap_tensorFunctor_of_unitRetractions 𝒳 h𝒳 F
    (affineQuasicoherentStructureSheaf g hg) hgen
    (hasFlatLocalUnitRetractions_affineQuasicoherentStructureSheaf g hg hflat hsurj)⟩

end AlgebraicGeometry.Stack

end
