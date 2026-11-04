module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived category of a closed subscheme as a subcategory of the ambient one

Let `i : Z ⟶ X` be a closed immersion of schemes.  Direct image of abelian sheaves along `i` is
exact, so it needs no derivation: the induced functor `D(Z_étale) ⟶ D(X_étale)` is obtained by
applying `i_*` termwise.  It identifies `D(Z_étale)` with the full subcategory `D_Z(X_étale)` of
complexes whose cohomology sheaves are supported on `Z`, and the quasi-inverse is the
restriction of inverse image `i^{-1}` to that subcategory.

## Main definitions

* `AlgebraicGeometry.supportedDerivedProperty` — the property of an object of `D(X_étale)` that
  all of its cohomology sheaves are supported on `Z`, and
  `AlgebraicGeometry.SupportedDerivedCategory`, the subcategory `D_Z(X_étale)` it cuts out.
* `AlgebraicGeometry.smallEtalePushforwardSupportedEquivalence` — the equivalence of
  `D(Z_étale)` with `D_Z(X_étale)` induced by direct image.

## Main results

* `AlgebraicGeometry.smallEtalePushforward_exact_ab` — direct image of abelian sheaves along a
  closed immersion is exact, so `Ri_* = i_*`.
* `AlgebraicGeometry.smallEtalePushforwardSupportedEquivalence_functor` and
  `AlgebraicGeometry.smallEtalePushforwardSupportedEquivalence_inverse` — the equivalence is
  given by direct image and its quasi-inverse by inverse image.
* `AlgebraicGeometry.smallEtalePushforwardStalkIsoAb` — the abelian form of the stalk of a
  direct image at a geometric point of the closed subscheme.

## Implementation notes

Exactness of `i_*` is the one point needing geometry.  Direct image is left exact for any
continuous functor of sites, being a right adjoint, so only preservation of epimorphisms is at
issue, and that is checked on stalks at geometric points: the stalk of `i_*` at a point of `Z`
is the stalk of the sheaf itself, because base change of pointed étale neighbourhoods along a
closed immersion is an initial functor, and away from `Z` both stalks vanish.  Epimorphisms of
abelian sheaves are the locally surjective morphisms, and local surjectivity gives surjectivity
on stalks because a geometric point is a point of the site.

The subcategory is cut out by membership of each cohomology sheaf in the essential image of
`i_*`, which by the unit of the adjunction is exactly the assertion that the cohomology sheaf is
supported on `Z`.  Given this, the equivalence is formal: the counit of the derived adjunction
is invertible because `i_*` is fully faithful, and the unit is invertible exactly on the
subcategory.

## References

* [Stacks Project, Tag 0AEG](https://stacks.math.columbia.edu/tag/0AEG)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v u

namespace AlgebraicGeometry

/-! ### Derived categories of an adjunction of exact functors -/

section DerivedAdjunction

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{w₂} C]
  {L : A ⥤ C} {R : C ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- An adjunction between exact functors of abelian categories induces an adjunction between
the functors they induce on derived categories: each is a lifting of the termwise functor
through the localization, and an adjunction descends to localizations. -/
public def exactAdjunctionDerived (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  let _ : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  let _ : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) L.mapDerivedCategory R.mapDerivedCategory

/-- If the right adjoint is fully faithful then the counit of the derived adjunction is
invertible: on the image of the localization functor it is the counit of the original
adjunction, and every object of the derived category is in that image up to isomorphism. -/
public lemma exactAdjunctionDerived_counit_isIso (adj : L ⊣ R) [R.Full] [R.Faithful] :
    IsIso (exactAdjunctionDerived adj).counit := by
  have h (Y : CochainComplex C ℤ) :
      IsIso ((exactAdjunctionDerived adj).counit.app (DerivedCategory.Q.obj Y)) := by
    dsimp [exactAdjunctionDerived]
    rw [Adjunction.localization_counit_app]
    infer_instance
  have (Y : DerivedCategory C) : IsIso ((exactAdjunctionDerived adj).counit.app Y) :=
    ((exactAdjunctionDerived adj).counit.isIso_app_iff_of_iso
      (DerivedCategory.Q.objObjPreimageIso Y)).mp (h (DerivedCategory.Q.objPreimage Y))
  exact NatIso.isIso_of_isIso_app _

omit [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} C] in
/-- A natural transformation of exact functors which is invertible on the homology objects of a
complex induces a quasi-isomorphism on that complex. -/
public lemma quasiIso_mapHomologicalComplex_of_homology {F G : A ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) (K : CochainComplex A ℤ) (h : ∀ n, IsIso (τ.app (K.homology n))) :
    QuasiIso ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  show IsIso (ShortComplex.homologyMap ((K.sc n).mapNatTrans τ))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso (τ.app (K.sc n).homology) := h n
  infer_instance

/-- The unit of the derived adjunction is invertible at a complex whose homology objects the
unit of the original adjunction already inverts. -/
public lemma exactAdjunctionDerived_unit_isIso_of_homology (adj : L ⊣ R)
    (K : CochainComplex A ℤ) (h : ∀ n, IsIso (adj.unit.app (K.homology n))) :
    IsIso ((exactAdjunctionDerived adj).unit.app (DerivedCategory.Q.obj K)) := by
  have : QuasiIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) :=
    quasiIso_mapHomologicalComplex_of_homology adj.unit K h
  dsimp [exactAdjunctionDerived]
  rw [Adjunction.localization_unit_app]
  infer_instance

end DerivedAdjunction

/-- An adjunction whose counit is invertible restricts to an equivalence of the right adjoint's
source with any full subcategory of its target containing the image of the right adjoint and on
which the unit is invertible; the quasi-inverse is the left adjoint restricted there. -/
public def equivalenceOfUnitIso {A C : Type*} [Category* A] [Category* C]
    {L : A ⥤ C} {R : C ⥤ A} (adj : L ⊣ R) [IsIso adj.counit] (P : ObjectProperty A)
    (hR : ∀ Y, P (R.obj Y)) (hP : ∀ Y, P Y → IsIso (adj.unit.app Y)) :
    C ≌ P.FullSubcategory :=
  let F := P.lift R hR
  let G := P.ι ⋙ L
  let α : F ⋙ G ≅ 𝟭 C := asIso adj.counit
  let β : 𝟭 P.FullSubcategory ≅ G ⋙ F :=
    Functor.fullyFaithfulCancelRight P.ι (NatIso.ofComponents
      (fun Y => by let := hP Y.obj Y.property; exact asIso (adj.unit.app Y.obj))
      (fun f => by dsimp [F, G]; exact adj.unit.naturality f.hom))
  CategoryTheory.Equivalence.mk F G α.symm β.symm

/-! ### Stalks of a direct image along a closed immersion -/

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- The diagram computing the stalk of a direct image of abelian sheaves at the image of a
geometric point is, after reindexing along base change, the diagram computing the stalk of the
sheaf itself. -/
public def stalkPushforwardDiagramIsoAb (s : GeometricPoint Z.1)
    (F : SmallEtaleAbelianSheaf B Z) :
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (s.map (B.inclusion.map i)))).op ⋙
      (sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}).obj
        (((smallEtaleBaseChange B i).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B X.1 X.property)
          (SmallEtale.topology B Z.1 Z.property)).obj F)) ≅
    (pullbackNeighborhoodFunctor B i s).op ⋙
      (CategoryOfElements.π (geometricPointFiber B Z.1 Z.property s)).op ⋙ F.obj := by
  classical
  let P := smallEtaleBaseChange B i
  let H := pullbackNeighborhoodFunctor B i s
  let JX := geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))
  let JZ := geometricPointFiber B Z.1 Z.property s
  let D := (CategoryOfElements.π JX).op ⋙
    (sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}).obj
      ((P.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)).obj F)
  let E := H.op ⋙ (CategoryOfElements.π JZ).op ⋙ F.obj
  have hDE : ∀ U, D.obj U = E.obj U := fun U => by
    simp [D, E, P, H, JX, JZ, pullbackNeighborhoodFunctor,
      CategoryOfElements.π, geometricPointFiber,
      Functor.sheafPushforwardContinuous_obj_obj_obj]
  refine NatIso.ofComponents (fun U => eqToIso (hDE U)) ?_
  intro U V f
  have hmap : D.map f ≍ E.map f := by
    dsimp [D, E, P, H, JX, JZ]
    exact HEq.rfl
  have hconj : D.map f = eqToHom (hDE U) ≫ E.map f ≫ eqToHom (hDE V).symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ (hDE U) (hDE V)).2 hmap
  calc
    D.map f ≫ eqToHom (hDE V) =
        (eqToHom (hDE U) ≫ E.map f ≫ eqToHom (hDE V).symm) ≫ eqToHom (hDE V) := by
      rw [← hconj]
    _ = eqToHom (hDE U) ≫ E.map f := by simp

/-- **Stacks 04FX for abelian sheaves.** At a geometric point of the closed subscheme, direct
image of abelian sheaves along a closed immersion does not change the stalk, naturally in the
sheaf: base change of pointed étale neighbourhoods is initial, so the two colimits agree. -/
@[stacks 04FX "stalk of a direct image inside the closed subscheme, abelian sheaves"]
public def smallEtalePushforwardStalkIsoAb (s : GeometricPoint Z.1) :
    (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property) ⋙
      sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} ⋙
      etaleStalkPresheafFunctor B X.1 X.property
        (s.map (B.inclusion.map i)) AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (SmallEtale.topology B Z.1 Z.property) AddCommGrpCat.{u + 1} ⋙
      etaleStalkPresheafFunctor B Z.1 Z.property s AddCommGrpCat.{u + 1} := by
  classical
  let H := pullbackNeighborhoodFunctor B i s
  let _ : H.Initial := pullbackNeighborhoodFunctor_initial B i s
  let _ : H.op.Final := Functor.final_op_of_initial H
  let P := smallEtaleBaseChange B i
  let JX := geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))
  let JZ := geometricPointFiber B Z.1 Z.property s
  let πX := (CategoryOfElements.π JX).op
  let πZ := (CategoryOfElements.π JZ).op
  let ShX := sheafToPresheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}
  let ShZ := sheafToPresheaf (SmallEtale.topology B Z.1 Z.property) AddCommGrpCat.{u + 1}
  refine NatIso.ofComponents (fun F =>
    (colim.mapIso (stalkPushforwardDiagramIsoAb B i s F)) ≪≫
      Functor.Final.colimitIso H.op (πZ ⋙ ShZ.obj F)) ?_
  intro F G φ
  let αX := ShX.map ((P.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B Z.1 Z.property)).map φ)
  let αZ := ShZ.map φ
  let sourceMap := πX.whiskerLeft αX
  let targetMap := πZ.whiskerLeft αZ
  have hdiag : sourceMap ≫ (stalkPushforwardDiagramIsoAb B i s G).hom =
      (stalkPushforwardDiagramIsoAb B i s F).hom ≫ H.op.whiskerLeft targetMap := by
    ext U
    simp [H, P, JX, JZ, πX, πZ, ShX, ShZ, αX, αZ, sourceMap, targetMap,
      stalkPushforwardDiagramIsoAb, pullbackNeighborhoodFunctor,
      geometricPointFiber, CategoryOfElements.π]
    rfl
  let EF := πZ ⋙ ShZ.obj F
  let EG := πZ ⋙ ShZ.obj G
  have hcolim : colim.map sourceMap ≫
      colim.map (stalkPushforwardDiagramIsoAb B i s G).hom =
      colim.map (stalkPushforwardDiagramIsoAb B i s F).hom ≫
        colim.map (H.op.whiskerLeft targetMap) := by
    simpa only [Functor.map_comp] using congrArg (fun η => colim.map η) hdiag
  calc
    colim.map sourceMap ≫ colim.map (stalkPushforwardDiagramIsoAb B i s G).hom ≫
        colimit.pre EG H.op =
      colim.map (stalkPushforwardDiagramIsoAb B i s F).hom ≫
        colim.map (H.op.whiskerLeft targetMap) ≫ colimit.pre EG H.op := by
      rw [← Category.assoc, hcolim, Category.assoc]
    _ = colim.map (stalkPushforwardDiagramIsoAb B i s F).hom ≫
          (colimit.pre EF H.op ≫ colim.map targetMap) :=
        congrArg (fun k => colim.map (stalkPushforwardDiagramIsoAb B i s F).hom ≫ k)
          (colimit.pre_map targetMap H.op).symm

/-! ### Exactness of direct image -/

private instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget AddCommGrpCat.{u + 1})

/-- **Stacks 03PU.** A locally surjective morphism of abelian sheaves on a small étale site is
surjective on the stalk at every geometric point: the stalk is the fiber of the point of the
site attached to the geometric point, and a point of a site turns local surjectivity into
surjectivity. -/
@[stacks 03PU "surjectivity on stalks at geometric points, abelian sheaves",
  sga "4 VIII 3.6" "epi ⇒ surj on stalks"]
public theorem surjective_etaleStalkMap_of_isLocallySurjective
    (Y : Scheme.{u}) (hY : B.Contains Y)
    {F G : Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}} (α : F ⟶ G)
    [Presheaf.IsLocallySurjective (SmallEtale.topology B Y hY) α.hom]
    (s : GeometricPoint Y) :
    Function.Surjective
      ((etaleStalkPresheafFunctor B Y hY s AddCommGrpCat.{u + 1}).map α.hom) :=
  (geometricPointSitePoint B Y hY s).toPresheafFiber_map_surjective α.hom

/-- Surjectivity of the map a functor induces on underlying abelian groups depends on the
functor only through its isomorphism class. -/
public lemma surjective_of_natIso {C : Type*} [Category* C]
    {L R : C ⥤ AddCommGrpCat.{v}} (e : L ≅ R) {A A' : C} (g : A ⟶ A')
    (h : Function.Surjective (R.map g)) : Function.Surjective (L.map g) := by
  have hL : L.map g = e.hom.app A ≫ R.map g ≫ e.inv.app A' := by
    rw [← Category.assoc, ← e.hom.naturality g, Category.assoc, e.hom_inv_id_app,
      Category.comp_id]
  have : Epi (R.map g) := (AddCommGrpCat.epi_iff_surjective _).mpr h
  refine (AddCommGrpCat.epi_iff_surjective _).mp ?_
  rw [hL]
  infer_instance

/-- Every map of abelian groups into a zero object is surjective. -/
public lemma surjective_of_isZero_tgt {M N : AddCommGrpCat.{v}} (h : IsZero N)
    (f : M ⟶ N) : Function.Surjective f := by
  intro y
  obtain rfl : y = 0 := by
    simpa using congrArg (fun m : N ⟶ N => m y) (h.eq_of_tgt (𝟙 N) 0)
  exact ⟨0, by simp⟩

/-- Direct image of abelian sheaves along a closed immersion preserves epimorphisms.  An
epimorphism of abelian sheaves is locally surjective, hence surjective on every stalk; the
stalk of the direct image is the stalk of the sheaf at a geometric point of the closed
subscheme and vanishes at a geometric point outside it, so the direct image is again surjective
on every stalk and therefore locally surjective. -/
public instance smallEtalePushforward_preservesEpi_ab :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Z.1 Z.property)).PreservesEpimorphisms := by
  constructor
  intro F G φ hφ
  set pf := (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Z.1 Z.property)
  have hls : Presheaf.IsLocallySurjective (SmallEtale.topology B Z.1 Z.property) φ.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) φ).2 hφ
  have hstalk : ∀ s : GeometricPoint X.1, Function.Surjective
      ((etaleStalkPresheafFunctor B X.1 X.property s AddCommGrpCat.{u + 1}).map
        (pf.map φ).hom) := by
    intro s
    by_cases hs : s.hom default ∈ Set.range (B.inclusion.map i).base
    · obtain ⟨t, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B i s hs
      exact surjective_of_natIso (smallEtalePushforwardStalkIsoAb B i t) φ
        (surjective_etaleStalkMap_of_isLocallySurjective B Z.1 Z.property φ t)
    · exact surjective_of_isZero_tgt
        (smallEtalePushforward_stalk_isZero_of_not_mem_range B i G s hs) _
  exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) (pf.map φ)).1
    (isLocallySurjective_of_surjective_etaleStalkMap B X.1 X.property (pf.map φ) hstalk)

/-- Direct image of abelian sheaves along a morphism of small étale sites preserves finite
limits, being a right adjoint. -/
public instance smallEtalePushforward_preservesFiniteLimits_ab {Y W : B.Scheme} (f : Y ⟶ W) :
    PreservesFiniteLimits
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)) :=
  have : PreservesLimitsOfSize.{0, 0}
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)) :=
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B W.obj W.property)
      (SmallEtale.topology B Y.obj Y.property)).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Direct image of abelian sheaves along a closed immersion preserves finite colimits: it is
additive, preserves finite limits as a right adjoint, and preserves epimorphisms, so it
preserves homology. -/
public instance smallEtalePushforward_preservesFiniteColimits_ab :
    PreservesFiniteColimits
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)) := by
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Z.1 Z.property))
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Stacks 0AEG.** Direct image of abelian sheaves along a closed immersion is exact, so it
coincides with its own right derived functor: `Ri_{small,*} = i_{small,*}`. -/
@[stacks 0AEG "Ri_* = i_* : direct image is exact, hence equal to its right derived functor"]
public theorem smallEtalePushforward_exact_ab :
    exactFunctor (SmallEtaleAbelianSheaf B Z) (SmallEtaleAbelianSheaf B X)
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)) :=
  ⟨(leftExactFunctor_iff _).mpr inferInstance, (rightExactFunctor_iff _).mpr inferInstance⟩

/-- Inverse image of abelian sheaves along a morphism of small étale sites preserves finite
colimits, being a left adjoint. -/
public instance smallEtalePullback_preservesFiniteColimits_ab {Y W : B.Scheme} (f : Y ⟶ W) :
    PreservesFiniteColimits
      ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)) :=
  have : PreservesColimitsOfSize.{0, 0}
      ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)) :=
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B W.obj W.property)
      (SmallEtale.topology B Y.obj Y.property)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-! ### The subcategory of complexes supported on the closed subscheme -/

section Supported

variable [HasDerivedCategory.{w₁} (SmallEtaleAbelianSheaf B Z)]
  [HasDerivedCategory.{w₂} (SmallEtaleAbelianSheaf B X)]

/-- The adjunction between inverse and direct image of abelian sheaves along `i`. -/
public def adjAb :
    (smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property) ⊣
      (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property) :=
  (smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Z.obj Z.property)

/-- `D_Z(X_étale)`, as a property of objects of `D(X_étale)`: all cohomology sheaves of the
complex are supported on the closed subscheme, that is, lie in the essential image of direct
image along `i`. -/
public def supportedDerivedProperty :
    ObjectProperty (DerivedCategory (SmallEtaleAbelianSheaf B X)) :=
  fun K => ∀ n : ℤ,
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).essImage
      ((DerivedCategory.homologyFunctor (SmallEtaleAbelianSheaf B X) n).obj K)

/-- The full subcategory `D_Z(X_étale)` of complexes on `X_étale` whose cohomology sheaves are
supported on the closed subscheme `Z`. -/
public abbrev SupportedDerivedCategory := (supportedDerivedProperty.{w₂} B i).FullSubcategory

omit [IsClosedImmersion (B.inclusion.map i)]
  [HasDerivedCategory.{w₁} (SmallEtaleAbelianSheaf B Z)] in
/-- Being supported on the closed subscheme is invariant under isomorphism in the derived
category, the cohomology sheaves being functorial. -/
public lemma supportedDerivedProperty_of_iso
    {K L : DerivedCategory (SmallEtaleAbelianSheaf B X)} (e : K ≅ L)
    (h : supportedDerivedProperty.{w₂} B i K) : supportedDerivedProperty.{w₂} B i L :=
  fun n => Functor.essImage.ofIso
    ((DerivedCategory.homologyFunctor (SmallEtaleAbelianSheaf B X) n).mapIso e) (h n)

/-- A complex coming from the closed subscheme is supported there: direct image is exact, so
the cohomology sheaves of `i_* K` are the direct images of those of `K`. -/
public lemma supportedDerivedProperty_mapDerivedCategory
    (K : DerivedCategory (SmallEtaleAbelianSheaf B Z)) :
    supportedDerivedProperty.{w₂} B i
      (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory.obj K) := by
  intro n
  exact Functor.essImage.ofIso
    ((((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategoryHomologyIso n).app K).symm
    (Functor.obj_mem_essImage _ _)

/-- On a complex supported on the closed subscheme the unit of the derived adjunction is
invertible: it suffices to check this on cohomology sheaves, where it is the assertion that
each of them lies in the essential image of direct image. -/
public lemma derived_unit_isIso_of_supported
    (K : DerivedCategory (SmallEtaleAbelianSheaf B X))
    (hK : supportedDerivedProperty.{w₂} B i K) :
    IsIso ((exactAdjunctionDerived (adjAb B i)).unit.app K) := by
  have hM := supportedDerivedProperty_of_iso B i
    (DerivedCategory.Q.objObjPreimageIso K).symm hK
  have : IsIso ((exactAdjunctionDerived (adjAb B i)).unit.app
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K))) := by
    refine exactAdjunctionDerived_unit_isIso_of_homology _ _ (fun n => ?_)
    refine (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr ?_
    exact Functor.essImage.ofIso
      ((DerivedCategory.homologyFunctorFactors (SmallEtaleAbelianSheaf B X) n).app
        (DerivedCategory.Q.objPreimage K)) (hM n)
  exact ((exactAdjunctionDerived (adjAb B i)).unit.isIso_app_iff_of_iso
    (DerivedCategory.Q.objObjPreimageIso K)).mp inferInstance

/-- **Stacks 0AEG.** Direct image along a closed immersion induces an equivalence of
`D(Z_étale)` with the full subcategory `D_Z(X_étale)` of `D(X_étale)` of complexes whose
cohomology sheaves are supported on `Z`. -/
@[stacks 0AEG "i_* induces an equivalence D(Z_étale) → D_Z(X_étale)"]
public def smallEtalePushforwardSupportedEquivalence :
    DerivedCategory (SmallEtaleAbelianSheaf B Z) ≌ SupportedDerivedCategory.{w₂} B i :=
  have := exactAdjunctionDerived_counit_isIso (adjAb B i)
  equivalenceOfUnitIso (exactAdjunctionDerived (adjAb B i)) (supportedDerivedProperty.{w₂} B i)
    (supportedDerivedProperty_mapDerivedCategory B i) (derived_unit_isIso_of_supported B i)

/-- **Stacks 0AEG.** The equivalence is given by direct image: composed with the inclusion of
`D_Z(X_étale)` into `D(X_étale)` it is the functor induced by `i_*`. -/
@[stacks 0AEG "the equivalence is induced by i_*"]
public def smallEtalePushforwardSupportedEquivalence_functor :
    (smallEtalePushforwardSupportedEquivalence.{w₁, w₂} B i).functor ⋙
        (supportedDerivedProperty.{w₂} B i).ι ≅
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- **Stacks 0AEG.** The quasi-inverse of the equivalence is inverse image restricted to
`D_Z(X_étale)`: `i^{-1}|_{D_Z(X_étale)}`. -/
@[stacks 0AEG "the quasi-inverse is i^{-1} restricted to D_Z(X_étale)"]
public def smallEtalePushforwardSupportedEquivalence_inverse :
    (smallEtalePushforwardSupportedEquivalence.{w₁, w₂} B i).inverse ≅
      (supportedDerivedProperty.{w₂} B i).ι ⋙
        ((smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property)).mapDerivedCategory :=
  Iso.refl _

end Supported

end AlgebraicGeometry

end
