module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing

/-!
# Locality of `R ℰom(𝒪_Z, -)` for a closed immersion of schemes

Let `i : Z ⟶ W` be a closed immersion of schemes and `R ℰom(𝒪_Z, -) : D(𝒪_W) ⥤ D(𝒪_Z)` the right
derived functor of sheaf Hom with exact support, the right adjoint of `Ri_*` of
[Stacks, Tag 0A76]. This functor is local on `W`: for an open `V ⊆ W`,

`(R ℰom(𝒪_Z, K))|_{i⁻¹V} ≅ R ℰom(𝒪_{i⁻¹V}, K|_V)`

for every `K` in `D(𝒪_W)`, with no boundedness assumed on `K`. The analogous statement holds along
an isomorphism of squares.

## Main results

* `Stacks.Duality.ClosedImmersionDualizing.rhomPushforwardIso` — for a commutative square of
  closed immersions `i`, `i'` and open immersions `j`, `j'` with a base-change isomorphism
  `j^* i_* ≅ i'_* j'^*`, the right adjoints agree:
  `R ℰom(𝒪_Z, -) ∘ Rj_* ≅ Rj'_* ∘ R ℰom(𝒪_{Z'}, -)`.
* `Stacks.Duality.ClosedImmersionDualizing.isIso_restrict_rhom_map_unit` — `j'^* R ℰom(𝒪_Z, -)`
  inverts the unit `K ⟶ Rj_* j^* K` as soon as it kills what `j^*` kills.
* `Stacks.Duality.ClosedImmersionDualizing.isZero_restrict_rhom_of_isZero` — for an open
  `V ⊆ W`, `(R ℰom(𝒪_Z, C))|_{i⁻¹V}` vanishes whenever `C|_V` does.
* `Stacks.Duality.ClosedImmersionDualizing.restrictRhomOpensIso` — locality along an open of the
  target: `(R ℰom(𝒪_Z, K))|_{i⁻¹V} ≅ R ℰom(𝒪_{i⁻¹V}, K|_V)`.
* `Stacks.Duality.ClosedImmersionDualizing.restrictRhomIsoIso` — the same along an isomorphism
  of squares.

## Implementation notes

Everything is at the model `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance of priority `10000`. Objects of `D(𝒪_W)` are written as `DerivedCategory W.Modules`;
mixing this spelling with `SheafOfModules (structureSheafRing _)` inside one isomorphism makes
elaboration compare the two `HasDerivedCategory` instances and time out.

## References

* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion (closedQuotientOfClosedImmersion)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.ClosedImmersionDualizing

variable {Z W Z' W' : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
  (i' : Z' ⟶ W') [IsClosedImmersion i'] (j : W' ⟶ W) [IsOpenImmersion j]
  (j' : Z' ⟶ Z) [IsOpenImmersion j']

/-- `R ℰom(𝒪_Z, -)` for a closed immersion of schemes, at the standard model. -/
abbrev rhom :=
  (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport

/-- `Ri_*` for a closed immersion of schemes, at the standard model, as the functor induced by
the exact functor `i_*`. -/
abbrev push := (modulePushforward
  (closedQuotientOfClosedImmersion i).i).mapDerivedCategory

/-- The adjunction `Ri_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] at the standard model. -/
abbrev pushAdj : push i ⊣ rhom i :=
  ClosedQuotientMorphismOfRingedSpaces.derivedModulePushforwardSheafHomExactSupportAdjunction
    (closedQuotientOfClosedImmersion i)

variable {i i' j j'}

/-- A base-change isomorphism `j^* i_* ≅ i'_* j'^*` of sheaves of modules induces one on derived
categories. -/
def derivedSquareIso
    (κ : Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j' ⋙ Scheme.Modules.pushforward i') :
    (Scheme.Modules.pushforward i).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor j).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor j').mapDerivedCategory ⋙
        (Scheme.Modules.pushforward i').mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso κ

/-- The right adjoints of the two sides of the square agree:
`R ℰom(𝒪_Z, -) ∘ Rj_* ≅ Rj'_* ∘ R ℰom(𝒪_{Z'}, -)`. -/
def rhomPushforwardIso
    (κ : Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j' ⋙ Scheme.Modules.pushforward i') :
    Stacks.Duality.derivedPushforward j ⋙ rhom i ≅
      rhom i' ⋙ Stacks.Duality.derivedPushforward j' :=
  ((pushAdj i).comp (OpenImmersion.derivedRestrictPushforwardAdjunction j)).rightAdjointUniq
    (((OpenImmersion.derivedRestrictPushforwardAdjunction j').comp (pushAdj i')).ofNatIsoLeft
      (derivedSquareIso κ).symm)

/-- **Locality of `R ℰom(𝒪_Z, -)`, given that it inverts the unit.** If `j'^* R ℰom(𝒪_Z, -)`
inverts the unit `K ⟶ Rj_* j^* K`, then `(R ℰom(𝒪_Z, K))|_{Z'} ≅ R ℰom(𝒪_{Z'}, K|_{W'})`. -/
def restrictRhomIso
    (κ : Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j' ⋙ Scheme.Modules.pushforward i')
    (K : DerivedCategory W.Modules)
    [IsIso ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.map ((rhom i).map
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app K)))] :
    (Scheme.Modules.restrictFunctor j').mapDerivedCategory.obj ((rhom i).obj K) ≅
      (rhom i').obj ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K) :=
  asIso ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.map ((rhom i).map
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app K))) ≪≫
    (Scheme.Modules.restrictFunctor j').mapDerivedCategory.mapIso
      ((rhomPushforwardIso κ).app _) ≪≫
    @asIso _ _ _ _ ((OpenImmersion.derivedRestrictPushforwardAdjunction j').counit.app _)
      (OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit_app j' _)

open ZeroObject in
/-- An object whose image under a functor reflecting isomorphisms and preserving zero objects
is zero, is zero. -/
theorem isZero_of_isZero_map {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D] (F : C ⥤ D) [F.ReflectsIsomorphisms]
    [F.PreservesZeroMorphisms] {X : C} (h : IsZero (F.obj X)) : IsZero X := by
  have : IsIso (F.map (0 : X ⟶ 0)) :=
    isIso_of_source_target_iso_zero _ h.isoZero (F.map_isZero (isZero_zero C)).isoZero
  have : IsIso (0 : X ⟶ 0) := isIso_of_reflects_iso _ F
  exact (isZero_zero C).of_iso (asIso (0 : X ⟶ 0))

/-- The shift-commutation datum of `R ℰom(𝒪_Z, -)` as a right derived functor. -/
@[instance_reducible]
def rhomCommShift : (rhom i).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (rhom i)
    (closedQuotientOfClosedImmersion i).derivedSheafHomExactSupportComparison
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing
      (closedQuotientOfClosedImmersion i).X)) (ComplexShape.up ℤ)) ℤ

/-- `R ℰom(𝒪_Z, -)` is exact, for the shift-commutation datum attached to it as a right derived
functor. -/
theorem rhom_isTriangulated :
    letI := rhomCommShift (i := i)
    (rhom i).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) _ _ _

open Pretriangulated in
/-- **`j'^* R ℰom(𝒪_Z, -)` inverts the unit of `j^* ⊣ Rj_*`**, as soon as it kills every object
which `j^*` kills. -/
theorem isIso_restrict_rhom_map_unit
    (hV : ∀ C : DerivedCategory W.Modules,
      IsZero ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj C) →
        IsZero ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.obj ((rhom i).obj C)))
    (K : DerivedCategory W.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.map ((rhom i).map
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app K))) := by
  let := rhomCommShift (i := i)
  have := rhom_isTriangulated (i := i)
  set η := (OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app K with hη
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle η
  have hj : IsIso ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.map η) := by
    have : IsIso ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.map η ≫
        (OpenImmersion.derivedRestrictPushforwardAdjunction j).counit.app
          ((OpenImmersion.derivedRestrict j).obj K)) := by
      rw [hη, (OpenImmersion.derivedRestrictPushforwardAdjunction j).left_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((OpenImmersion.derivedRestrictPushforwardAdjunction j).counit.app
          ((OpenImmersion.derivedRestrict j).obj K))
  have hC : IsZero ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj C) :=
    Triangle.isZero₃_of_isIso₁ _
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.map_distinguished _ hT) hj
  exact (Triangle.isZero₃_iff_isIso₁ _
    ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.map_distinguished _
      ((rhom i).map_distinguished _ hT))).1 (hV C hC)

omit [IsOpenImmersion j] [IsOpenImmersion j'] in
/-- **`R ℰom(𝒪_Z, -)` kills, over `i⁻¹V`, what restriction to `V` kills.** If `C|_V` is zero,
then `(R ℰom(𝒪_Z, C))|_{i⁻¹V}` is zero. -/
theorem isZero_restrict_rhom_of_isZero (V : W.Opens)
    (C : DerivedCategory W.Modules)
    (hC : IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj C)) :
    IsZero ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapDerivedCategory.obj
      ((rhom i).obj C)) := by
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := W.ringCatSheaf) V
  have := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := W.ringCatSheaf) V
  refine isZero_of_isZero_map (push (i ∣_ V)) ?_
  have e1 := ((derivedSquareIso
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V)).app
    ((rhom i).obj C)).symm
  have e2 := (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapIso
    ((ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso
      (closedQuotientOfClosedImmersion i)).app C)
  have e3 := Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso V
    ((modulePushforward (closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
      (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite
        (closedQuotientOfClosedImmersion i).Z.sheaf))) C
  have hadd := RingedSite.additive_derivedSheafHom_obj
    (Stacks.SheafOfModules.ringedSite (V : W.Opens).toScheme.sheaf)
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((modulePushforward (closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite
            (closedQuotientOfClosedImmersion i).Z.sheaf))))
  have h3 := Functor.map_isZero ((RingedSite.derivedSheafHomBifunctor
    (Stacks.SheafOfModules.ringedSite (V : W.Opens).toScheme.sheaf)).obj
      (Opposite.op ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((modulePushforward (closedQuotientOfClosedImmersion i).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite
            (closedQuotientOfClosedImmersion i).Z.sheaf)))))) hC
  exact h3.of_iso (e1 ≪≫ e2 ≪≫ e3)

/-- **The locality isomorphism**, `(R ℰom(𝒪_Z, K))|_{Z'} ≅ R ℰom(𝒪_{Z'}, K|_{W'})`, for a square
along which `R ℰom(𝒪_Z, -)` restricted to `Z'` kills what restriction to `W'` kills. -/
def restrictRhomIsoOfVanishing
    (κ : Scheme.Modules.pushforward i ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor j' ⋙ Scheme.Modules.pushforward i')
    (hV : ∀ C : DerivedCategory W.Modules,
      IsZero ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj C) →
        IsZero ((Scheme.Modules.restrictFunctor j').mapDerivedCategory.obj ((rhom i).obj C)))
    (K : DerivedCategory W.Modules) :
    (Scheme.Modules.restrictFunctor j').mapDerivedCategory.obj ((rhom i).obj K) ≅
      (rhom i').obj ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K) :=
  haveI := isIso_restrict_rhom_map_unit hV K
  restrictRhomIso κ K

/-- **Locality of `R ℰom(𝒪_Z, -)` along an open of the target.** For a closed immersion
`i : Z ⟶ W` and an open `V ⊆ W`, `(R ℰom(𝒪_Z, K))|_{i⁻¹V} ≅ R ℰom(𝒪_{i⁻¹V}, K|_V)` for every
`K` in `D(𝒪_W)`, with no boundedness assumed. -/
def restrictRhomOpensIso (V : W.Opens)
    (K : DerivedCategory W.Modules) :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapDerivedCategory.obj ((rhom i).obj K) ≅
      (rhom (i ∣_ V)).obj ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K) :=
  restrictRhomIsoOfVanishing
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V)
    (isZero_restrict_rhom_of_isZero V) K

/-- Restriction along an isomorphism of schemes reflects zero objects of the derived category. -/
theorem isZero_of_isZero_restrict_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (C : DerivedCategory Y.Modules)
    (hC : IsZero ((Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory.obj C)) : IsZero C := by
  let r : Scheme.Modules.restrictFunctor e.hom ⋙ Scheme.Modules.restrictFunctor e.inv ≅
      𝟭 Y.Modules :=
    (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId
  exact (Functor.map_isZero (Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory hC).of_iso
    ((Functor.mapDerivedCategoryCompIsoOfCompIso r ≪≫ Functor.mapDerivedCategoryId _).app C).symm

/-- The base-change isomorphism `j^* i_* ≅ i'_* j'^*` for a commutative square whose two
horizontal arrows are isomorphisms. -/
def isoSquareRestrictPushforwardIso {X' X S' S : Scheme.{u}} (eX : X' ≅ X) (eS : S' ≅ S)
    (f : X ⟶ S) (f' : X' ⟶ S') (w : eX.hom ≫ f = f' ≫ eS.hom) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor eS.hom ≅
      Scheme.Modules.restrictFunctor eX.hom ⋙ Scheme.Modules.pushforward f' :=
  Functor.isoWhiskerLeft _
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv eS) ≪≫
    Scheme.Modules.pushforwardComp f eS.inv ≪≫
    Scheme.Modules.pushforwardCongr (by
      rw [Iso.eq_inv_comp, ← Category.assoc, w, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]) ≪≫
    (Scheme.Modules.pushforwardComp eX.inv f').symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv eX).symm _

/-- **`R ℰom(𝒪_Z, -)` along an isomorphism of squares.** For a commutative square of closed
immersions whose horizontal arrows are isomorphisms of schemes,
`(R ℰom(𝒪_Z, K))|_{Z'} ≅ R ℰom(𝒪_{Z'}, K|_{W'})`. -/
def restrictRhomIsoIso (eZ : Z' ≅ Z) (eW : W' ≅ W) (w : eZ.hom ≫ i = i' ≫ eW.hom)
    (K : DerivedCategory W.Modules) :
    (Scheme.Modules.restrictFunctor eZ.hom).mapDerivedCategory.obj ((rhom i).obj K) ≅
      (rhom i').obj ((Scheme.Modules.restrictFunctor eW.hom).mapDerivedCategory.obj K) :=
  restrictRhomIsoOfVanishing (isoSquareRestrictPushforwardIso eZ eW i i' w)
    (fun C hC => by
      have := (pushAdj i).isRightAdjoint
      exact Functor.map_isZero _ ((rhom i).map_isZero (isZero_of_isZero_restrict_iso eW C hC))) K

end Stacks.Duality.ClosedImmersionDualizing
