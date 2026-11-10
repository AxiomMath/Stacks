module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceDiagonal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSectionsCanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The top-degree trace of a relative curve, on the base

Let `f : X ⟶ S` be proper, smooth of relative dimension one, with geometrically irreducible
fibres, `N ≥ 1` invertible on `X`, and `ζ` a primitive `N`-th root of unity of a field `k` over
which `X ×_S X` lies. Then `G ≅ R²f_*(f⁻¹G)` for sheaves `G` of `ℤ/N`-modules on `S`, as
abelian sheaves, naturally in `G` (`Stacks.EtaleCohomology.TopTrace.topSheafIso`).

The proof descends the top-degree trace of the Kummer class of the diagonal of `X ×_S X`
(`Stacks.EtaleCohomology.TopTrace.isIso_trace_diagonalModuleClass`), which lives on `X`, to `S`:

* proper base change along `f` itself identifies `f⁻¹R²f_*(f⁻¹G)` with `R²pr₂_*(pr₂⁻¹f⁻¹G)`,
  naturally in `G` (`Stacks.EtaleCohomology.TopTrace.topSheafBaseChangeIso`);
* the inverse image along `f` is fully faithful on abelian sheaves: the unit `F ⟶ f_*f⁻¹F` is
  an isomorphism over every étale `V ⟶ S`, because the base change `X_V ⟶ V` is flat,
  quasi-compact and has geometrically connected fibres (Tag 0A3H localized,
  `Stacks.EtaleCohomology.isIso_smallEtaleInverseImageSections`);
* so the natural isomorphism `f⁻¹G ≅ f⁻¹R²f_*(f⁻¹G)` is the inverse image of a unique natural
  isomorphism on `S`.

This is a step of the construction of the top-degree trace of an elementary fibration in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianInverseImageDirectImageAdj_unit_app`.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageFullyFaithful`.
* `Stacks.EtaleCohomology.TopTrace.topSheafBaseChangeIso`.
* `Stacks.EtaleCohomology.TopTrace.topSheafIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-! ### Inverse image along a flat quasi-compact morphism with geometrically connected fibres -/

section FullyFaithful

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]

/-- **The unit `F ⟶ f_* f⁻¹ F` is an isomorphism** of abelian sheaves for `f` flat,
quasi-compact, with geometrically connected fibres: over an étale `V ⟶ S` it is the map
`F(V) ⟶ (f⁻¹F)(X ×_S V)`, bijective by Tag 0A3H for the base change `X ×_S V ⟶ V`. -/
theorem isIso_etaleAbelianInverseImageDirectImageAdj_unit_app
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F) := by
  have hV : ∀ V : S.Etale, IsIso (((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app
      F).hom.app (op V)) := by
    intro V
    have hsub : (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally
        (𝟙 _ ≫ pullback.fst V.hom f) := by
      rw [Category.id_comp]
      exact universally_isQuotientMap_of_flat_quasiCompact _
    have hconn : GeometricallyConnected (𝟙 _ ≫ pullback.fst V.hom f) := by
      rw [Category.id_comp]
      infer_instance
    have h := isIso_smallEtaleInverseImageSections.{u, 0} f
      ((sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)
      (𝟙 ((smallEtaleBaseChange f).obj V)) hsub hconn
    have hid : smallEtaleInverseImageSections.{u, 0} f
        ((sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)
        (𝟙 ((smallEtaleBaseChange f).obj V)) =
        smallEtaleUnitApp.{u, 0} f ((sheafCompose S.smallEtaleTopology
          (forget AddCommGrpCat.{u + 1})).obj F) V := by
      change _ ≫ ((smallEtaleInverseImage.{u, 0} f).obj _).obj.map (𝟙 _).op = _
      rw [op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hid] at h
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_unit_app_of_isIso_forget f F V h)
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F).hom :=
    NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F)) := by
    change IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F).hom
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The inverse image along `f` is fully faithful** on abelian sheaves, for `f` flat,
quasi-compact, with geometrically connected fibres. -/
def etaleAbelianInverseImageFullyFaithful : (etaleAbelianInverseImage.{u, 0} f).FullyFaithful :=
  haveI : IsIso (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun F => isIso_etaleAbelianInverseImageDirectImageAdj_unit_app f F
  (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).fullyFaithfulLOfIsIsoUnit

end FullyFaithful

namespace TopTrace

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### Proper base change along `f` itself -/

section BaseChange

variable {S X : Scheme.{u}} (f : X ⟶ S) {N : ℕ}

/-- The base change map of `R(f)_*` along `f` itself, on `U(f⁻¹G)[0]⟦2⟧`, followed by `H⁰`. -/
def topSheafBaseChangeMap :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ etaleModuleUnderlyingAbelian X (ZMod N) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ ((2 : ℕ) : ℤ) ⋙
          (etaleAbelianDerivedDirectImage.{u, 0} f ⋙ etaleAbelianDerivedInverseImage.{u, 0} f) ⋙
            DerivedCategory.homologyFunctor _ 0 ⟶
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ etaleModuleUnderlyingAbelian X (ZMod N) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ ((2 : ℕ) : ℤ) ⋙
          (etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f f) ⋙
            etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)) ⋙
            DerivedCategory.homologyFunctor _ 0 :=
  Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
      etaleModuleUnderlyingAbelian X (ZMod N) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        shiftFunctor _ ((2 : ℕ) : ℤ))
    (Functor.whiskerRight (etaleAbelianDerivedBaseChange.{u, 0} f f (pullback.fst f f)
      (pullback.snd f f) pullback.condition) (DerivedCategory.homologyFunctor _ 0))

/-- **Proper base change is an isomorphism** here (Tag 0DDE): the complexes are bounded below
and killed by `N`. -/
theorem isIso_topSheafBaseChangeMap_app [IsProper f] (hN : N ≠ 0)
    (G : EtaleModules.{u, 0} (ZMod N) S) : IsIso ((topSheafBaseChangeMap f (N := N)).app G) := by
  have := isIso_etaleAbelianDerivedBaseChange_of_isProper f (IsPullback.of_hasPullback f f)
    (((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian X (ZMod N)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj G)))⟦((2 : ℕ) : ℤ)⟧) (-2)
    (DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega))
    (torsionCohomologyProperty_shift_single hN _)
  exact (inferInstance : IsIso ((DerivedCategory.homologyFunctor _ 0).map
    ((etaleAbelianDerivedBaseChange.{u, 0} f f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).app (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian X (ZMod N)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj G)))⟦((2 : ℕ) : ℤ)⟧))))

/-- **Proper base change along `f`**, natural in the sheaf (Tag 0DDE):
`f⁻¹ R²f_*(f⁻¹G) ≅ R²pr₂_*(pr₂⁻¹f⁻¹G)` for `pr₂ : X ×_S X ⟶ X`, through `pr₁⁻¹ f⁻¹ = pr₂⁻¹ f⁻¹`;
the complexes are bounded below and killed by `N`. -/
def topSheafBaseChangeIso [IsProper f] (hN : N ≠ 0) :
    topSheaf f (N := N) ⋙ etaleAbelianInverseImage.{u, 0} f ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ topSheaf (pullback.snd f f) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
      etaleModuleUnderlyingAbelian X (ZMod N) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        shiftFunctor _ ((2 : ℕ) : ℤ) ⋙ etaleAbelianDerivedDirectImage.{u, 0} f)
      (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
        (etaleAbelianInverseImage.{u, 0} f) 0).symm ≪≫
    @asIso _ _ _ _ (topSheafBaseChangeMap f (N := N))
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (isIso_topSheafBaseChangeMap_app f hN)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
      etaleModuleUnderlyingAbelian X (ZMod N) ⋙ DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        ((etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f f)).commShiftIso ((2 : ℕ) : ℤ))
        (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f) ⋙
          DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
      (Functor.isoWhiskerRight (inverseImageSingleNatIso (N := N) (pullback.fst f f))
        (shiftFunctor _ ((2 : ℕ) : ℤ) ⋙ etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f) ⋙
          DerivedCategory.homologyFunctor _ 0)) ≪≫
    Functor.isoWhiskerRight (moduleSquareIso (N := N) (pullback.fst f f) f f (pullback.snd f f)
        pullback.condition)
      (etaleModuleUnderlyingAbelian (pullback f f) (ZMod N) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        shiftFunctor _ ((2 : ℕ) : ℤ) ⋙ etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f) ⋙
          DerivedCategory.homologyFunctor _ 0)

end BaseChange

/-! ### Descent to the base -/

section Descent

variable {k : Type u} [Field k] {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f] {N : ℕ} [NeZero N]
  (hX : IsUnit ((N : ℕ) : Γ(X, ⊤))) (hY : IsUnit ((N : ℕ) : Γ(pullback f f, ⊤)))
  (qY : pullback f f ⟶ Spec (.of k)) {ζ : k} (hζ : IsPrimitiveRoot ζ N)

omit [IsProper f] [SmoothOfRelativeDimension 1 f] in
/-- `f` has geometrically connected fibres: they are irreducible. -/
theorem geometricallyConnected_of_geometricallyIrreducible : GeometricallyConnected f := by
  rw [GeometricallyConnected.eq_geometrically]
  intro K _ y Z fst snd hpull
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd hpull
  exact connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ Z).isConnected

include hX in
/-- On `X`, after inverse image: `f⁻¹ G ≅ f⁻¹ R²f_*(f⁻¹G)`, naturally in `G`, by the top-degree
trace of the Kummer class of the diagonal and proper base change. -/
def topSheafInverseImageIso :
    etaleModuleUnderlyingAbelian S (ZMod N) ⋙ etaleAbelianInverseImage.{u, 0} f ≅
      topSheaf f (N := N) ⋙ etaleAbelianInverseImage.{u, 0} f :=
  haveI : IsIso (trace (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun G => isIso_trace_diagonalModuleClass f hX hY qY hζ G
  haveI : ∀ G, IsIso ((Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
      (trace (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ))).app G) :=
    fun _G => isIso_trace_diagonalModuleClass f hX hY qY hζ _
  etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) f ≪≫
    Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
      (asIso (trace (pullback.snd f f) (diagonalModuleClass f (NeZero.ne N) hY qY hζ))) ≪≫
    (topSheafBaseChangeIso f (NeZero.ne N)).symm

include hX in
/-- **`G ≅ R²f_*(f⁻¹G)` for sheaves of `ℤ/N`-modules on `S`**, as abelian sheaves, naturally in
`G`: the descent along the fully faithful `f⁻¹` of
`Stacks.EtaleCohomology.TopTrace.topSheafInverseImageIso`. -/
def topSheafIso : etaleModuleUnderlyingAbelian S (ZMod N) ≅ topSheaf f (N := N) :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI := geometricallyConnected_of_geometricallyIrreducible f
  ((etaleAbelianInverseImageFullyFaithful f).whiskeringRight _).preimageIso
    (topSheafInverseImageIso f hX hY qY hζ)

end Descent

end TopTrace

end Stacks.EtaleCohomology
