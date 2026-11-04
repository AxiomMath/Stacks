module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingKernelStalkPaste
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImageAbelianSheafUlift
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAbelianInverseImageRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionChartBaseChange

/-!
# Stacks 0AER on geometric module fibres, in the formal glueing situation

The step the source of Stacks 0AF0 marks "(omitted)" needs, at a geometric point `ȳ` of `Y` lying
over `x̄` of `X`, that the square of geometric module fibres
```
(f_*G)_x̄           --θ_G-->            G_ȳ
    |                                   |
(f_*(j'_*(G|_V)))_x̄  --θ-->  (j'_*(G|_V))_ȳ
```
is cartesian, the vertical maps being the fibres of the unit `G ⟶ j'_*j'^*G` of the module
adjunction along the inclusion `j' : V ⟶ Y` of `V = Y ∖ f⁻¹Z`.  This is Stacks 0AER read on
`𝒪`-modules instead of abelian sheaves.

## Main definitions

* `AlgebraicGeometry.Space.directImageFiberMap`: the comparison
  `θ : (f_*M)_x̄ ⟶ M_ȳ`, linear over the homomorphism `ρ : 𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` of stalk rings,
  natural in the `𝒪_Y`-module `M`; its transpose along extension of scalars is the fibre of the
  counit `f^*f_*M ⟶ M` read through Stacks 05V5
  (`AlgebraicGeometry.Space.directImageFiberMap_homEquiv_symm`).

## Main results

* `CategoryTheory.IsPullback.of_natTrans_of_arrowIso`: a naturality square of one natural
  transformation is cartesian as soon as, after a functor reflecting the relevant pullback, it
  is identified — through two natural isomorphisms of the source and target functors — with a
  cartesian naturality square of another natural transformation at an arrow isomorphic to the
  image of the given one.
* `AlgebraicGeometry.Space.exists_iso_abelianUnit_comp_eq`: for an open immersion `j`, the
  abelian sheaf underlying the unit `G ⟶ j_*j^*G` of the module adjunction is, up to an
  isomorphism of its target, the unit of the abelian adjunction along `j` at the abelian sheaf
  underlying `G`.  No mate condition is needed: the direct image of abelian sheaves along an
  open immersion is fully faithful, and a map into its essential image inverted by the inverse
  image is the unit up to an isomorphism of the target
  (`CategoryTheory.Adjunction.exists_iso_unit_comp_eq_of_isIso_counit`).
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_iso_restrictionUnit_comp_eq`: the same
  in Situation 0AEV, against the unit `smallEtaleAbelianRestrictionUnit` along which Stacks 0AER
  is stated; the two inclusions of `V` are matched by generalising over the subfunctor and
  substituting `AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplementPreimage`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageFiberMap_of_compat`: the
  cartesian square above, from Stacks 0AER on abelian sheaves
  (`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageStalkMap_ambientMorphism`)
  and a dictionary carrying `θ` to `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap`.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- The counit of an adjunction is invertible when its right adjoint is fully faithful. -/
private theorem isIso_counit_of_fullyFaithful {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hG : G.FullyFaithful) : IsIso adj.counit := by
  have := hG.full
  have := hG.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-- **A map into the essential image of a fully faithful right adjoint, inverted by the left
adjoint, is the unit up to an isomorphism of its target.**  For an adjunction `F ⊣ G` with
invertible counit, a map `φ : P ⟶ P'` with `P' ≅ G Q` and `F φ` invertible factors as the unit at
`P` followed by an isomorphism `G F P ≅ P'`. -/
theorem Adjunction.exists_iso_unit_comp_eq_of_isIso_counit {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [IsIso adj.counit]
    {P P' : C} (φ : P ⟶ P') {Q : D} (χ : G.obj Q ≅ P') [IsIso (F.map φ)] :
    ∃ ψ : G.obj (F.obj P) ≅ P', adj.unit.app P ≫ ψ.hom = φ := by
  obtain ⟨k, hk⟩ : ∃ k : F.obj P ⟶ Q, k = (adj.homEquiv P Q).symm (φ ≫ χ.inv) := ⟨_, rfl⟩
  have hk' : k = F.map φ ≫ F.map χ.inv ≫ adj.counit.app Q := by
    rw [hk, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have : IsIso k := by rw [hk']; infer_instance
  refine ⟨G.mapIso (asIso k) ≪≫ χ, ?_⟩
  have h1 : adj.unit.app P ≫ G.map k = φ ≫ χ.inv := by
    rw [← adj.homEquiv_unit P Q k, hk]
    exact (adj.homEquiv P Q).apply_symm_apply _
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Transport of a cartesian naturality square.**  Let `θ : Φ ⟶ Ψ` and `τ : Φ' ⟶ Ψ'` be natural
transformations, `L` a functor and `F` a functor reflecting the relevant pullback, with natural
isomorphisms `α : Φ ⋙ F ≅ L ⋙ Φ'` and `β : Ψ ⋙ F ≅ L ⋙ Ψ'` carrying `F θ` to `τ L`.  If an arrow
`u : L G ⟶ P` is isomorphic, under `L G`, to `L g`, and the naturality square of `τ` at `u` is
cartesian, then so is the naturality square of `θ` at `g`. -/
theorem IsPullback.of_natTrans_of_arrowIso {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂}
    [Category.{v₂} 𝒟] {ℰ : Type u₃} [Category.{v₃} ℰ] {𝒜 : Type u₄} [Category.{v₄} 𝒜]
    {Φ Ψ : 𝒞 ⥤ 𝒟} (θ : Φ ⟶ Ψ) (F : 𝒟 ⥤ 𝒜) {L : 𝒞 ⥤ ℰ} {Φ' Ψ' : ℰ ⥤ 𝒜} (τ : Φ' ⟶ Ψ')
    (α : Φ ⋙ F ≅ L ⋙ Φ') (β : Ψ ⋙ F ≅ L ⋙ Ψ')
    (hc : ∀ M, F.map (θ.app M) ≫ β.hom.app M = α.hom.app M ≫ τ.app (L.obj M))
    {G G' : 𝒞} (g : G ⟶ G') {P : ℰ} (u : L.obj G ⟶ P) (ψ : P ≅ L.obj G')
    (hu : u ≫ ψ.hom = L.map g)
    (h : IsPullback (τ.app (L.obj G)) (Φ'.map u) (Ψ'.map u) (τ.app P))
    [ReflectsLimit (cospan (Ψ.map g) (θ.app G')) F] :
    IsPullback (θ.app G) (Φ.map g) (Ψ.map g) (θ.app G') := by
  have h₂ : IsPullback (τ.app P) (Φ'.map ψ.hom) (Ψ'.map ψ.hom) (τ.app (L.obj G')) :=
    IsPullback.of_vert_isIso ⟨(τ.naturality ψ.hom).symm⟩
  have h₃ := h.paste_vert h₂
  rw [← Φ'.map_comp, ← Ψ'.map_comp, hu] at h₃
  have hc' : ∀ M, τ.app (L.obj M) ≫ β.inv.app M = α.inv.app M ≫ F.map (θ.app M) := by
    intro M
    rw [← cancel_epi (α.hom.app M), Iso.hom_inv_id_app_assoc, ← reassoc_of% (hc M)]
    simp
  refine IsPullback.of_map F (θ.naturality g).symm ?_
  exact h₃.of_iso (α.app G).symm (β.app G).symm (α.app G').symm (β.app G').symm
    (hc' G) (α.inv.naturality g) (β.inv.naturality g) (hc' G')

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of geometric module fibres along a direct image -/

section DirectImageFiberMap

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1)

/-- The transpose of `θ` along extension of scalars: the identification
`𝒪_{Y,ȳ} ⊗ (f_*M)_x̄ ≅ (f^*f_*M)_ȳ` of Stacks 05V5 followed by the fibre at `ȳ` of the counit
`f^*f_*M ⟶ M`. -/
def directImageFiberMapTranspose (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).obj
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O).obj ((modulePushforward B S hS f).obj M)) ⟶
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).obj M :=
  (modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) ≫
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
      (smallEtaleRingedTopos B S hS Y).O).map ((modulePullbackAdjunction B S hS f).counit.app M)

/-- **The comparison `θ : (f_*M)_x̄ ⟶ M_ȳ` of geometric module fibres.**  For a morphism
`f : Y ⟶ X` of algebraic spaces, a geometric point `ȳ` of `Y` with image `x̄`, and an
`𝒪_Y`-module `M`, the map `m ↦ (f^*f_*M ⟶ M)_ȳ (1 ⊗ m)` from the fibre at `x̄` of the direct image
to the fibre at `ȳ`, read through the identification `(f^*N)_ȳ ≅ 𝒪_{Y,ȳ} ⊗ N_x̄` of Stacks 05V5.
It is linear over the homomorphism `ρ : 𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` of stalk rings, so it is valued in
the restriction of scalars of `M_ȳ` along `ρ`, and it is natural in `M`.

It is defined as the transpose, along extension of scalars, of the fibre of the counit
precomposed with the identification of Stacks 05V5; that this transpose is what it is defined
to be is `AlgebraicGeometry.Space.directImageFiberMap_homEquiv_symm`. -/
def directImageFiberMap :
    modulePushforward B S hS f ⋙
        Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O ⟶
      Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O ⋙
        ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS f y) where
  app M :=
    (ModuleCat.extendRestrictScalarsAdj.{u} (smallEtaleStalkPullbackRingMap B S hS f y)).homEquiv
      _ _ (directImageFiberMapTranspose B S hS f y M)
  naturality M M' g := by
    have h1 : (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).map ((modulePushforward B S hS f).map g)) ≫
          (modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M') =
        (modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) ≫
          (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O).map
            ((modulePullback B S hS f).map ((modulePushforward B S hS f).map g)) :=
      (modulePullbackFiberIso B S hS f y).inv.naturality ((modulePushforward B S hS f).map g)
    have h2 : (modulePullback B S hS f).map ((modulePushforward B S hS f).map g) ≫
          (modulePullbackAdjunction B S hS f).counit.app M' =
        (modulePullbackAdjunction B S hS f).counit.app M ≫ g :=
      (modulePullbackAdjunction B S hS f).counit.naturality g
    have core : (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).map ((modulePushforward B S hS f).map g)) ≫
          ((modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M') ≫
            (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
              (smallEtaleRingedTopos B S hS Y).O).map
                ((modulePullbackAdjunction B S hS f).counit.app M')) =
        ((modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) ≫
            (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
              (smallEtaleRingedTopos B S hS Y).O).map
                ((modulePullbackAdjunction B S hS f).counit.app M)) ≫
          (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O).map g := by
      rw [reassoc_of% h1, Category.assoc]
      congr 1
      exact ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map_comp _ _).symm.trans
        ((congrArg (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map h2).trans
          ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O).map_comp _ _))
    exact ((ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).homEquiv_naturality_left _ _).symm.trans
      ((congrArg _ core).trans ((ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).homEquiv_naturality_right _ _))

/-- **The transpose of `θ` is the fibre of the counit read through Stacks 05V5.**  Along
extension of scalars by `ρ : 𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}`, `θ_M` corresponds to
`AlgebraicGeometry.Space.directImageFiberMapTranspose`, the identification
`𝒪_{Y,ȳ} ⊗ (f_*M)_x̄ ≅ (f^*f_*M)_ȳ` of Stacks 05V5 followed by the fibre at `ȳ` of the counit
`f^*f_*M ⟶ M` (`AlgebraicGeometry.Space.directImageFiberMapTranspose_eq`). -/
theorem directImageFiberMap_homEquiv_symm (M : Modules.{u, u} B S hS Y.1 Y.2) :
    ((ModuleCat.extendRestrictScalarsAdj.{u} (smallEtaleStalkPullbackRingMap B S hS f y)).homEquiv
        _ _).symm ((directImageFiberMap B S hS f y).app M) =
      directImageFiberMapTranspose B S hS f y M :=
  Equiv.symm_apply_apply _ _

/-- The transpose of `θ`, written out. -/
theorem directImageFiberMapTranspose_eq (M : Modules.{u, u} B S hS Y.1 Y.2) :
    directImageFiberMapTranspose B S hS f y M =
      (modulePullbackFiberIso B S hS f y).inv.app ((modulePushforward B S hS f).obj M) ≫
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map
            ((modulePullbackAdjunction B S hS f).counit.app M) :=
  rfl

end DirectImageFiberMap

/-! ### The unit along an open immersion, module side against abelian side -/

/-- The abelian sheaf underlying an `𝒪_X`-module, with its coefficients lifted to the universe
`u + 1` at which the geometric stalk of an abelian sheaf, and Stacks 0AER, live. -/
abbrev moduleUliftAbelianSheaf (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
    sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}

section OpenImmersion

variable {V Y : AlgebraicSpaces B S hS} (j : V ⟶ Y) (hj : IsOpenImmersion B S hS j.hom)

/-- **The unit of the module adjunction along an open immersion is the abelian unit, up to an
isomorphism of its target.**  For an open immersion `j : V ⟶ Y` and an `𝒪_Y`-module `G`, the
abelian sheaf underlying `G ⟶ j_*j^*G` is the unit `G ⟶ j_*j⁻¹G` of the abelian adjunction along
`j`, followed by an isomorphism `j_*j⁻¹G ≅ j_*j^*G` of abelian sheaves.

The abelian direct image along `j` is fully faithful, the target is in its essential image by the
direct-image dictionary
`AlgebraicGeometry.Space.modulePushforwardCompToSheafAbelianDirectImageIso`, and the abelian
inverse image of the map is the abelian sheaf underlying `j^*` of the module unit, which is
invertible by the triangle identity because `j_*` is fully faithful on modules too. So
`CategoryTheory.Adjunction.exists_iso_unit_comp_eq_of_isIso_counit` applies, and no comparison of
the two units through the dictionary is needed. -/
theorem exists_iso_abelianUnit_comp_eq (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ∃ ψ : (smallEtaleAbelianPushforward.{u + 1} B S hS j hj.rep).obj
          ((smallEtaleAbelianInverseImage B S hS j hj.rep).obj
            ((moduleUliftAbelianSheaf B S hS Y).obj G)) ≅
        (moduleUliftAbelianSheaf B S hS Y).obj
          ((modulePullback B S hS j ⋙ modulePushforward B S hS j).obj G),
      (smallEtaleAbelianInverseImageAdjunction B S hS j hj.rep).unit.app
          ((moduleUliftAbelianSheaf B S hS Y).obj G) ≫ ψ.hom =
        (moduleUliftAbelianSheaf B S hS Y).map
          ((modulePullbackAdjunction B S hS j).unit.app G) := by
  have : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS j hj.rep).counit :=
    isIso_counit_of_fullyFaithful _ (fullyFaithfulSmallEtaleRestrictionOfIsOpenImmersion B S hS j hj
      AddCommGrpCat.{u + 1})
  have : IsIso (modulePullbackAdjunction B S hS j).counit :=
    isIso_counit_of_fullyFaithful _ (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj)
  have hη : IsIso ((modulePullback B S hS j).map
      ((modulePullbackAdjunction B S hS j).unit.app G)) := by
    have : IsIso ((modulePullback B S hS j).map
        ((modulePullbackAdjunction B S hS j).unit.app G) ≫
          (modulePullbackAdjunction B S hS j).counit.app ((modulePullback B S hS j).obj G)) := by
      rw [(modulePullbackAdjunction B S hS j).left_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((modulePullbackAdjunction B S hS j).counit.app ((modulePullback B S hS j).obj G))
  have hL : IsIso ((smallEtaleAbelianInverseImage B S hS j hj.rep).map
      ((moduleUliftAbelianSheaf B S hS Y).map
        ((modulePullbackAdjunction B S hS j).unit.app G))) := by
    have h := (NatIso.isIso_map_iff (modulePullbackCompToSheafInverseImageIso B S hS j
      (isEtale_of_isOpenImmersion B S hS hj) hj.rep)
      ((modulePullbackAdjunction B S hS j).unit.app G)).mp
      (by dsimp only [Functor.comp_map]; infer_instance)
    exact h
  exact Adjunction.exists_iso_unit_comp_eq_of_isIso_counit
    (smallEtaleAbelianInverseImageAdjunction B S hS j hj.rep)
    ((moduleUliftAbelianSheaf B S hS Y).map ((modulePullbackAdjunction B S hS j).unit.app G))
    ((smallEtaleAbelianDirectImageIso B S hS j hj.rep).app
        ((moduleUliftAbelianSheaf B S hS V).obj ((modulePullback B S hS j).obj G)) ≪≫
      ((modulePushforwardCompToSheafAbelianDirectImageIso B S hS j).app
        ((modulePullback B S hS j).obj G)).symm)

end OpenImmersion

namespace FormalGlueingSituation

variable {B S hS} (D : FormalGlueingSituation B S hS)

/-- **In Situation 0AEV the module unit along `j'` is the unit of Stacks 0AER, up to an
isomorphism of its target.**  The abelian sheaf underlying the unit `G ⟶ j'_*j'^*G` of the
module adjunction along `j' = D.openImmersionOver` is the unit
`AlgebraicGeometry.Space.smallEtaleAbelianRestrictionUnit` along the inclusion of the open
complement of Stacks 0AER, followed by an isomorphism of abelian sheaves.

The two inclusions are inclusions of equal subfunctors, which are not definitionally equal; the
statement is proved for an arbitrary subfunctor equal to the second one, where the equation can
be substituted away, and then instantiated at `V` by
`AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplementPreimage`. -/
theorem exists_iso_restrictionUnit_comp_eq (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :
    ∃ ψ : smallEtaleAbelianRestrictionPushforward B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
          ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G) ≅
        (moduleUliftAbelianSheaf B S hS D.spaceY).obj
          ((modulePullback B S hS D.openImmersionOver ⋙
            modulePushforward B S hS D.openImmersionOver).obj G),
      smallEtaleAbelianRestrictionUnit B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
          ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G) ≫ ψ.hom =
        (moduleUliftAbelianSheaf B S hS D.spaceY).map
          ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G) := by
  have key : ∀ (V' : AlgebraicSpaces B S hS) (j : V' ⟶ D.spaceY)
      (_ : V' = openComplementPreimageSpace B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩)
      (_ : HEq j (openComplementPreimageι B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩)),
      ∃ ψ : smallEtaleAbelianRestrictionPushforward B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
            ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G) ≅
          (moduleUliftAbelianSheaf B S hS D.spaceY).obj
            ((modulePullback B S hS j ⋙ modulePushforward B S hS j).obj G),
        smallEtaleAbelianRestrictionUnit B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
            ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G) ≫ ψ.hom =
          (moduleUliftAbelianSheaf B S hS D.spaceY).map
            ((modulePullbackAdjunction B S hS j).unit.app G) := by
    intro V' j hV hj
    subst hV
    obtain rfl := eq_of_heq hj
    exact exists_iso_abelianUnit_comp_eq B S hS _
      (isOpenImmersion_openComplementPreimageι B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩) G
  refine key D.spaceV D.openImmersionOver D.spaceV_eq_openComplementPreimageSpace ?_
  have hheq : ∀ (P : Subfunctor D.Y) (_ : P = (openComplementOfClosedSubspace B S hS D.spaceY
      ⟨D.Z.preimage D.ambientMorphism.hom,
        isClosedSubspace_preimage B S hS D.ambientMorphism.hom D.Z
          D.spaceX.property D.spaceY.property D.closed_Z⟩).1)
      (hPa : IsAlgebraicSpace B S hS P.toFunctor),
      HEq (ObjectProperty.homMk P.ι : (⟨P.toFunctor, hPa⟩ : AlgebraicSpaces B S hS) ⟶ D.spaceY)
        (openComplementPreimageι B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩) := by
    intro P hP hPa
    subst hP
    rfl
  exact hheq D.V D.V_eq_openComplementPreimage D.isOpenSubspace_V.1

/-- **Stacks 0AER on geometric module fibres, from a dictionary.**  Let `ȳ` be a geometric point
of `Y` with image `x̄`, and suppose given natural isomorphisms identifying, after forgetting to
abelian groups and lifting to `u + 1`, the fibre at `x̄` of `f_*` with the abelian geometric stalk
of the abelian direct image, and the fibre at `ȳ` with the abelian geometric stalk, which carry
`θ = AlgebraicGeometry.Space.directImageFiberMap` to
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap`.  Then for every `𝒪_Y`-module `G`
the square of `θ` at the unit `G ⟶ j'_*j'^*G` is cartesian.

This is `CategoryTheory.IsPullback.of_natTrans_of_arrowIso` applied to Stacks 0AER on abelian
sheaves,
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_directImageStalkMap_ambientMorphism`,
with the units matched by
`AlgebraicGeometry.Space.FormalGlueingSituation.exists_iso_restrictionUnit_comp_eq`. -/
theorem isPullback_directImageFiberMap_of_compat (y : GeometricPoint B S hS D.spaceY.1)
    (α : (modulePushforward B S hS D.ambientMorphism ⋙
          Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O) ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      moduleUliftAbelianSheaf B S hS D.spaceY ⋙
        (smallEtaleAbelianDirectImage B S hS D.ambientMorphism ⋙
          smallEtaleAbelianStalk B S hS (geometricPointMap D.ambientMorphism.hom y)))
    (β : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
          ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)) ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      moduleUliftAbelianSheaf B S hS D.spaceY ⋙ smallEtaleAbelianStalk B S hS y)
    (hc : ∀ M, (forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          ((directImageFiberMap B S hS D.ambientMorphism y).app M) ≫ β.hom.app M =
        α.hom.app M ≫ (smallEtaleAbelianDirectImageStalkMap B S hS D.ambientMorphism y).app
          ((moduleUliftAbelianSheaf B S hS D.spaceY).obj M))
    (G : Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :
    IsPullback ((directImageFiberMap B S hS D.ambientMorphism y).app G)
      ((modulePushforward B S hS D.ambientMorphism ⋙
          Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G))
      ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
          ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G))
      ((directImageFiberMap B S hS D.ambientMorphism y).app
        ((modulePullback B S hS D.openImmersionOver ⋙
          modulePushforward B S hS D.openImmersionOver).obj G)) := by
  obtain ⟨ψ, hψ⟩ := D.exists_iso_restrictionUnit_comp_eq G
  exact IsPullback.of_natTrans_of_arrowIso (directImageFiberMap B S hS D.ambientMorphism y)
    (forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
    (smallEtaleAbelianDirectImageStalkMap B S hS D.ambientMorphism y) α β hc
    ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app G)
    (smallEtaleAbelianRestrictionUnit B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩
      ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G)) ψ hψ
    (D.isPullback_directImageStalkMap_ambientMorphism y
      ((moduleUliftAbelianSheaf B S hS D.spaceY).obj G))

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
