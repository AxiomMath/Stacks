module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximation by perfect complexes extends from an open subscheme

Let `X` be a scheme, `T ⊆ X` a closed subset contained in an open subscheme `U`, and `E` an
object of the derived category of `𝒪_X`-modules whose cohomology vanishes off `T` in every
degree at least `m`. If approximation by perfect complexes holds for the restriction of `E` to
`U`, relative to the preimage of `T` and the same degree `m`, then it holds for `E` itself.

The approximating object is the extension by zero `j_! P` of an approximation `P ⟶ E|_U` on the
open subscheme, and the map to `E` is the extension by zero of that approximation followed by
the derived counit of `j_! ⊣ j^*`.

## Main definitions

* `CategoryTheory.NatTrans.mapDerivedCategoryCompToId`: its counit-shaped form, for a
  transformation `G ⋙ F ⟶ 𝟭`.

## Main results

* `AlgebraicGeometry.hasPerfectApproximation_of_open`: approximation extends from an open
  subscheme under the stated support hypothesis.
* `CategoryTheory.NatTrans.mapDerivedCategory_homology`: the derived form of a natural
  transformation of exact functors acts on cohomology as the transformation itself.
* `CategoryTheory.isIso_homologyFunctor_map_mapDerivedCategoryCompToId`: a derived counit is
  invertible on cohomology in every degree where the counit itself is.
* `CategoryTheory.Functor.epi_homologyFunctor_map_mapDerivedCategory_map_iff`: an exact functor
  preserves cohomology epimorphisms of derived objects.

## Implementation notes

The open subscheme is the scheme associated to an open subset of `X`, and the closed subset it
carries is the preimage of `T`. Only closedness of `T` is needed from the source's triple;
quasi-compactness of its complement and quasi-coherence of `E` play no role in this extension
step. Support is expressed, as in `AlgebraicGeometry.CohomologySupportedOn`, by vanishing of
the cohomology stalks off `T`.

Two functors between the module categories of `X` and of `U` occur under a second spelling,
and both spellings are definitionally equal to the ones already in the library:
`AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U` is
`ExtensionByZeroModules.jStar U X.ringCatSheaf`, and
`ExtensionByZeroModules.jPush U X.ringCatSheaf` is
`RingedSpaceModuleAdjunction.modulePushforward (X.toRingedSpace.ofRestrict U.isOpenEmbedding)`.
Exactness and additivity of `j_!` and `j^*` are global instances, so the proof takes them from
instance search rather than from the existential form of Stacks 08BT.

The derived pushforward `Rj` and its comparison `αj` are the total right derived functor of
`j_*` on the homotopy category; the K-injective resolutions that make it exist come from
Stacks 079P. Both Stacks 08DP and Stacks 08DF take `Rj` and `αj` as arguments together with
the right-derived-functor datum, and that datum is passed explicitly rather than left to
instance search, because its statement mentions the structure sheaf of the open subscheme under
a second spelling which instance search does not see through.

The section "Derived functors of natural transformations" is abstract category theory, stated
over arbitrary abelian categories with derived categories. That is not only tidier: elaborated
against the module categories of a scheme the same terms cost many times the default heartbeat
budget, because every unification unfolds the scheme vocabulary.

## References

* [Stacks Project, Tag 08EP](https://stacks.math.columbia.edu/tag/08EP)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology Stacks.Cohomology.ClosedSupportPerfect
open Stacks.Cohomology.PushforwardRestriction (extensionByZeroToDerivedPushforward
  cohomologySupportedOn_jShriek)

/-! ### Derived functors of natural transformations -/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **The homology comparison of a homology-preserving functor is natural in the functor.** On a
homological complex, the degreewise transformation followed by the comparison for the target
functor is the comparison for the source functor followed by the transformation at the homology
object. -/
theorem Functor.mapHomologicalComplexHomologyIso_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    (η : F ⟶ G) {ι : Type*} (c : ComplexShape ι) (n : ι) (K : HomologicalComplex C c) :
    (HomologicalComplex.homologyFunctor D c n).map
        ((NatTrans.mapHomologicalComplex η c).app K) ≫
      (G.mapHomologicalComplexHomologyIso c n).hom.app K =
    (F.mapHomologicalComplexHomologyIso c n).hom.app K ≫
      η.app ((HomologicalComplex.homologyFunctor C c n).obj K) := by
  let S := (HomologicalComplex.shortComplexFunctor C c n).obj K
  change ShortComplex.homologyMap (S.mapNatTrans η) ≫ (S.mapHomologyIso G).hom =
    (S.mapHomologyIso F).hom ≫ η.app S.homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

/-- **A derived natural transformation acts on cohomology as the transformation itself.** The
two sides agree after composing with the localization functor, by
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso_naturality`, and a natural
transformation out of a localization is determined by that composite. -/
theorem NatTrans.mapDerivedCategory_homology
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) (n : ℤ) (E : DerivedCategory C) :
    (DerivedCategory.homologyFunctor D n).map ((NatTrans.mapDerivedCategory η).app E) ≫
        (G.mapDerivedCategoryHomologyIso n).hom.app E =
      (F.mapDerivedCategoryHomologyIso n).hom.app E ≫
        η.app ((DerivedCategory.homologyFunctor C n).obj E) := by
  let HC := DerivedCategory.homologyFunctor C n
  let HD := DerivedCategory.homologyFunctor D n
  let τ₁ : F.mapDerivedCategory ⋙ HD ⟶ HC ⋙ G :=
    Functor.whiskerRight (NatTrans.mapDerivedCategory η) HD ≫
      (G.mapDerivedCategoryHomologyIso n).hom
  let τ₂ : F.mapDerivedCategory ⋙ HD ⟶ HC ⋙ G :=
    (F.mapDerivedCategoryHomologyIso n).hom ≫ Functor.whiskerLeft HC η
  have hτ : τ₁ = τ₂ := by
    apply Localization.natTrans_ext (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    intro K
    simp only [Functor.comp_obj, NatTrans.mapDerivedCategory_app_Q_obj,
      Functor.mapDerivedCategoryHomologyIso, Functor.mapDerivedCategoryHomologyIsoAux,
      Localization.liftNatIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, comp_app, Functor.whiskerRight_app,
      Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, id_app,
      Iso.refl_inv, Category.comp_id, Category.id_comp, Functor.map_comp,
      Localization.Lifting.compRight_iso, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Category.assoc, τ₁, τ₂]
    have hL (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
        Localization.Lifting.iso DerivedCategory.Q
          (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
          (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          H.mapDerivedCategory = H.mapDerivedCategoryFactors := rfl
    rw [hL F, hL G]
    dsimp only [HC, HD]
    rw [← Functor.map_comp_assoc (DerivedCategory.homologyFunctor D n)
      (G.mapDerivedCategoryFactors.inv.app K) (G.mapDerivedCategoryFactors.hom.app K),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
      cancel_epi ((DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategoryFactors.hom.app K)),
      DerivedCategory.homologyFunctorFactors_hom_naturality_assoc
        ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) n
        ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
          G.map ((DerivedCategory.homologyFunctorFactors C n).inv.app K)),
      cancel_epi ((DerivedCategory.homologyFunctorFactors D n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))]
    calc
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
        G.map ((DerivedCategory.homologyFunctorFactors C n).inv.app K) =
          ((F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
            η.app ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj K)) ≫
            G.map ((DerivedCategory.homologyFunctorFactors C n).inv.app K) := by
              rw [← Category.assoc,
                Functor.mapHomologicalComplexHomologyIso_naturality η (ComplexShape.up ℤ) n K]
      _ = (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
          F.map ((DerivedCategory.homologyFunctorFactors C n).inv.app K) ≫
          η.app ((DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj K)) := by
            rw [Category.assoc]
            simpa only [Functor.comp_obj] using
              (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫=
                (η.naturality ((DerivedCategory.homologyFunctorFactors C n).inv.app K)).symm
  simpa [τ₁, τ₂] using NatTrans.congr_app hτ E

/-- **An exact functor preserves cohomology epimorphisms of derived objects.** The companion of
`CategoryTheory.Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff` for epimorphisms,
and proved the same way, by transporting along
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`. -/
theorem Functor.epi_homologyFunctor_map_mapDerivedCategory_map_iff
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory C} (f : K ⟶ L) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) ↔
      Epi (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
  Stacks.PseudoCoherence.DerivedCharacterization.epi_map_iff_of_natIso
    (F.mapDerivedCategoryHomologyIso n) f

/-- An exact functor carries a cohomology isomorphism of derived objects to one: the direction
of `CategoryTheory.Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff` that is used
as a transport, stated so that a caller need not supply the hypothesis as an instance. -/
theorem Functor.isIso_homologyFunctor_map_mapDerivedCategory_map
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory C} (f : K ⟶ L) (n : ℤ)
    (hf : IsIso ((DerivedCategory.homologyFunctor C n).map f)) :
    IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) :=
  (F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff f n).mpr inferInstance

/-- An exact functor carries a cohomology epimorphism of derived objects to one: the transport
direction of `CategoryTheory.Functor.epi_homologyFunctor_map_mapDerivedCategory_map_iff`. -/
theorem Functor.epi_homologyFunctor_map_mapDerivedCategory_map
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory C} (f : K ⟶ L) (n : ℤ)
    (hf : Epi ((DerivedCategory.homologyFunctor C n).map f)) :
    Epi ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) :=
  (F.epi_homologyFunctor_map_mapDerivedCategory_map_iff f n).mpr inferInstance

variable (G : C ⥤ D) (F : D ⥤ C)

/-- **The derived form of a counit-shaped transformation `G ⋙ F ⟶ 𝟭`.** It is
`CategoryTheory.NatTrans.mapDerivedCategory` of the transformation, read through the
identifications of the derived functor of a composite with the composite of the derived
functors and of the derived functor of `𝟭` with `𝟭`. -/
noncomputable def NatTrans.mapDerivedCategoryCompToId
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : G ⋙ F ⟶ 𝟭 C) :
    G.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C) :=
  (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).inv ≫
    NatTrans.mapDerivedCategory η ≫ (Functor.mapDerivedCategoryIdIso C).hom

/-- **The derived counit is invertible on cohomology wherever the counit is.** -/
theorem isIso_homologyFunctor_map_mapDerivedCategoryCompToId
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : G ⋙ F ⟶ 𝟭 C) (n : ℤ) (K : DerivedCategory C)
    (hη : IsIso (η.app ((DerivedCategory.homologyFunctor C n).obj K))) :
    IsIso ((DerivedCategory.homologyFunctor C n).map
      ((NatTrans.mapDerivedCategoryCompToId G F η).app K)) := by
  have hε : IsIso ((DerivedCategory.homologyFunctor C n).map
      ((NatTrans.mapDerivedCategory η).app K)) := by
    have : IsIso ((DerivedCategory.homologyFunctor C n).map
        ((NatTrans.mapDerivedCategory η).app K) ≫
        ((𝟭 C).mapDerivedCategoryHomologyIso n).hom.app K) := by
      rw [NatTrans.mapDerivedCategory_homology η n K]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (((𝟭 C).mapDerivedCategoryHomologyIso n).hom.app K)
  change IsIso ((DerivedCategory.homologyFunctor C n).map
    ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).inv.app K ≫
      (NatTrans.mapDerivedCategory η).app K ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K))
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

end CategoryTheory

/-! ### Extension of an approximation from an open subscheme -/

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 08EP.** Let `T` be a closed subset of a scheme `X` contained in an
open subscheme `U`, and let `E` be an object of the derived category of `𝒪_X`-modules whose
cohomology vanishes off `T` in every degree at least `m`. If approximation by a perfect complex
holds for the restriction of `E` to `U`, relative to the preimage of `T` and the same degree
`m`, then it holds for `E`.

The perfect object is the extension by zero `j_! P` of an approximation `P` over `U`: it is
perfect because the derived pushforward of a perfect object with closed support is perfect
(Stacks 08DP) and agrees there with extension by zero (Stacks 08DF), and its cohomology is
supported on `T` because extension by zero preserves the support. The map to `E` is the
extension by zero of the approximation, followed by the derived counit of `j_! ⊣ j^*`; the
support hypothesis on `E` makes the underived counit invertible on each cohomology sheaf in
degree at least `m`, and hence the derived counit invertible on cohomology there. -/
@[stacks 08EP]
theorem hasPerfectApproximation_of_open
    (X : Scheme.{u}) (U : X.Opens) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ)
    (hApprox : HasPerfectApproximation (U : Scheme.{u})
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T)
      ((RingedSpace.restrictModules X.toRingedSpace U).mapDerivedCategory.obj E) m)
    (hSupport : ∀ i : ℤ, m ≤ i → ∀ x : X, x ∉ T →
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) :
    HasPerfectApproximation X T E m := by
  classical
  obtain ⟨P, hP, hPT, α, hαiso, hαepi⟩ := hApprox
  set O := X.ringCatSheaf
  -- The derived pushforward along the inclusion of the open subscheme, as the total right
  -- derived functor of `j_*`; the K-injective resolutions making it exist are Stacks 079P.
  have hJPush : (ExtensionByZeroModules.jPush U O).Additive := by
    have : (ExtensionByZeroModules.jPush U O).IsRightAdjoint :=
      (ExtensionByZeroModules.jStarAdjunction U O).isRightAdjoint
    exact Functor.additive_of_preserves_binary_products _
  let C := SheafOfModules.{u} (ExtensionByZeroModules.resRing U O)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let J := (ExtensionByZeroModules.jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := SheafOfModules.{u} O)
  have hC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := fun K =>
    let R := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective C).some
    ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩
  have : J.HasPointwiseRightDerivedFunctor W :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} J hC).1
  let Rj := J.totalRightDerived (DerivedCategory.Qh (C := C)) W
  let αj := J.totalRightDerivedUnit (DerivedCategory.Qh (C := C)) W
  have hRj : Rj.IsRightDerivedFunctor αj W := inferInstance
  -- The image of the preimage of `T` in the open subscheme is `T` itself, so it is closed.
  have hTimage : IsClosed ((X.toRingedSpace.ofRestrict U.isOpenEmbedding).hom.base ''
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T)) := by
    convert hT using 1
    ext x
    refine ⟨?_, fun hx => ⟨⟨x, hTU hx⟩, hx, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  -- Stacks 08DP: the derived pushforward of `P` is perfect.
  have hPperfect : RingedSpace.IsPerfect (X := X.toRingedSpace) (Rj.obj P) :=
    isPerfect_derivedPushforward_of_closedSupport
      X.toRingedSpace U ((fun x : U ↦ (x.1 : X)) ⁻¹' T) hTimage Rj αj P hP hPT (hRj := hRj)
  -- Stacks 08DF, part (2): on `P` the derived pushforward is extension by zero.
  have hFtoRj : IsIso ((extensionByZeroToDerivedPushforward O U Rj αj).app P) :=
    isIso_extensionByZeroToDerivedPushforward_app_of_supported' O U T hT hTU Rj αj hRj P hPT
  have hFperfect : RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((ExtensionByZeroModules.jShriek U O).mapDerivedCategory.obj P) :=
    hPperfect.of_iso
      (asIso ((extensionByZeroToDerivedPushforward O U Rj αj).app P)).symm
  have hFPT : CohomologySupportedOn O T
      ((ExtensionByZeroModules.jShriek U O).mapDerivedCategory.obj P) :=
    cohomologySupportedOn_jShriek O U T P hPT
  -- The approximating map: extension by zero of `α`, followed by the derived counit.
  let E' : DerivedCategory (SheafOfModules.{u} O) := E
  let P' : DerivedCategory (SheafOfModules.{u} (ExtensionByZeroModules.resRing U O)) := P
  let α' : P' ⟶ (ExtensionByZeroModules.jStar U O).mapDerivedCategory.obj E' := α
  let η : ExtensionByZeroModules.jStar U O ⋙ ExtensionByZeroModules.jShriek U O ⟶
      𝟭 (SheafOfModules.{u} O) := (ExtensionByZeroModules.jShriekAdjunction U O).counit
  let β : ((ExtensionByZeroModules.jStar U O).mapDerivedCategory ⋙
      (ExtensionByZeroModules.jShriek U O).mapDerivedCategory).obj E' ⟶ E' :=
    (NatTrans.mapDerivedCategoryCompToId (ExtensionByZeroModules.jStar U O)
      (ExtensionByZeroModules.jShriek U O) η).app E'
  let γ : (ExtensionByZeroModules.jShriek U O).mapDerivedCategory.obj P' ⟶ E' :=
    (ExtensionByZeroModules.jShriek U O).mapDerivedCategory.map α' ≫ β
  have hβIso : ∀ n : ℤ, m ≤ n →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map β) := fun n hn =>
    isIso_homologyFunctor_map_mapDerivedCategoryCompToId
      (ExtensionByZeroModules.jStar U O) (ExtensionByZeroModules.jShriek U O) η n E'
      (ExtensionByZeroModules.counit_isIso_of_stalk_isZero U O _
        fun x hxU => hSupport n hn x fun hx => hxU (hTU hx))
  have hγ (n : ℤ) : (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map γ =
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map
        ((ExtensionByZeroModules.jShriek U O).mapDerivedCategory.map α') ≫
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map β :=
    Functor.map_comp _ _ _
  have hγIso : ∀ n : ℤ, m < n →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) n).map γ) := by
    intro n hn
    have := Functor.isIso_homologyFunctor_map_mapDerivedCategory_map
      (ExtensionByZeroModules.jShriek U O) α' n (hαiso n hn)
    have := hβIso n hn.le
    rw [hγ]
    infer_instance
  have hγEpi : Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) m).map γ) := by
    have := Functor.epi_homologyFunctor_map_mapDerivedCategory_map
      (ExtensionByZeroModules.jShriek U O) α' m hαepi
    have := hβIso m le_rfl
    rw [hγ]
    infer_instance
  exact ⟨(ExtensionByZeroModules.jShriek U O).mapDerivedCategory.obj P', hFperfect, hFPT, γ,
    hγIso, hγEpi⟩

end AlgebraicGeometry

end
