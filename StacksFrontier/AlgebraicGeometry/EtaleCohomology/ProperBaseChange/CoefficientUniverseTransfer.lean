module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.CoefficientUniverseVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# Cohomology commutes with base change at every coefficient universe

For a morphism of schemes `f : X ⟶ Y` in `Scheme.{u}`, the condition
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, v} f` asks that the base change map
`g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` be invertible for every cartesian square and every torsion abelian
sheaf `F` with sections in `AddCommGrpCat.{max (u + 1) v}`. This file shows that, for a
quasi-compact and quasi-separated `f`, the condition at the smallest coefficient universe gives it
at every universe:

  `CohomologyCommutesWithBaseChange.{u, 0} f → CohomologyCommutesWithBaseChange.{u, v} f`.

## The argument

Write `L` for the universe lift `Stacks.Sheaves.UniverseLift.uliftSheafFunctor` from abelian
sheaves with sections in `AddCommGrpCat.{u + 1}` to those with sections in
`AddCommGrpCat.{max (u + 1) v}`. Two steps.

* **The base change map commutes with `L`.** This is proved for any coefficient functor
  `Φ : AddCommGrpCat.{max (u + 1) v₀} ⥤ AddCommGrpCat.{max (u + 1) v}` such that composition with
  `Φ` is exact on abelian sheaves of the small étale sites, carries injective sheaves to injective
  sheaves, and commutes with sheafification and with the Kan extensions computing inverse images;
  the universe lift is such a functor
  (`preservesInjectiveObjects_uliftSheafFunctor_smallEtale_of_univLE` for injectives). Composition
  with `Φ` commutes with direct image on the nose and with inverse image up to the comparison
  `etaleAbelianInverseImageCoefficientSquare`, which matches the two underived base change maps
  (`etaleAbelianBaseChange_sheafCompose`). On a K-injective complex `I` with a K-injective
  resolution `t : (g')⁻¹ I ⟶ J`, invertibility of the derived base change map is the statement
  that the complex map `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I ⟶ f'_* J` is a quasi-isomorphism
  (`isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso`). Taking for `I` and `J` bounded below
  complexes of injectives, `Φ` carries both to complexes of the same kind and the comparison map to
  the comparison map, so invertibility at a sheaf `G` gives invertibility at `Φ ∘ G`
  (`isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`).
* **Every torsion sheaf is a filtered colimit of universe lifts of torsion sheaves.** A sheaf `F`
  in the larger universe is the sheafification of the filtered union of the subpresheaves of `F`
  whose groups of sections are all `u`-small (`smallSubpresheafSheafCoconeIsColimit`), each of
  which is the universe lift of a torsion sheaf of the smaller universe
  (`smallSubpresheafSheafIso`), sheafification commuting with `L`. Higher direct images along a
  quasi-compact quasi-separated morphism commute with filtered colimits ([Stacks, Tag 09Z1]), so
  the base change map in each degree is invertible at the colimit
  (`isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit`).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso` — the derived
  base change map at a K-injective complex, through a K-injective resolution of its inverse image.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose` — the base change
  map is invertible at `Φ ∘ G` if it is at `G`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit` — invertibility
  passes to filtered colimits, for a quasi-compact quasi-separated morphism.
* `Stacks.EtaleCohomology.smallSubpresheafSheafCoconeIsColimit` — an abelian sheaf is the filtered
  colimit of the sheafifications of its small subpresheaves.
* `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.of_univ_zero` — the transfer.

## Implementation notes

The derived-category statements are stated for plain universe variables `v₀` and `v` and a
variable coefficient functor `Φ`, and the universe lift is substituted only at the end, at the
level of the proposition `CohomologyCommutesWithBaseChange`. Instantiating them at a compound
universe (`max v₀ v`, or the numeral `0` against `u + 1`) leaves the kernel comparing structurally
different but equivalent universe levels inside large terms, which it does not do in reasonable
time. For the same reason the comparisons with the base change maps are stated for variable
transformations and the base change maps are substituted only at the end, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap`, and the
resolutions passed between lemmas are always typed as resolutions of `G[0]`, so that the instances
of the complexes they carry agree.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare Opposite
open Stacks.Sheaves.UniverseLift AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale (ts_vComp_app ts_whiskerLeft_app ts_whiskerRight_app)

attribute [local instance] HasDerivedCategory.standard

universe v₀ v u

namespace Stacks.EtaleCohomology

section BaseChangeMapInstances

/- The statements of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap`
reach the `Preadditive` structure on abelian sheaves through `CategoryTheory.Abelian.toPreadditive`
of `CategoryTheory.sheafIsAbelian` at `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`.
Among this module's imports `Stacks.SheafOfModules.coefficientSheafification` is a second
`HasSheafify` instance for the small étale site, preferred by default, and comparing the two
spellings at `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange` exceeds the kernel's budget.
Both choices are therefore fixed to the ones that module makes, up to the final transfer, whose
universe-`0` instances the raised priority of the latter would leave stuck. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10000] AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology

/-! ### Two cancellation lemmas -/

section Abstract

variable {D : Type*} [Category* D]

/-- If `a ≫ b ≫ β = x ≫ y ≫ c` with `a`, `b`, `c` invertible, then `β` is invertible exactly
when `x ≫ y` is. -/
private theorem isIso_iff_of_fac {P Q R S T U : D} {a : P ⟶ Q} {b : Q ⟶ R} {β : R ⟶ S}
    {x : P ⟶ T} {y : T ⟶ U} {c : U ⟶ S} (hfac : a ≫ b ≫ β = x ≫ y ≫ c) (ha : IsIso a)
    (hb : IsIso b) (hc : IsIso c) : IsIso β ↔ IsIso (x ≫ y) := by
  rw [← isIso_comp_left_iff (a ≫ b), Category.assoc, hfac, ← Category.assoc,
    isIso_comp_right_iff]

/-- If `y ≫ r = s ≫ y'` with `r` and `y'` invertible, then `x ≫ y` is invertible exactly when
`x ≫ s` is. -/
private theorem isIso_comp_iff_of_square {P T U V W : D} (x : P ⟶ T) {y : T ⟶ U} {r : U ⟶ V}
    {s : T ⟶ W} {y' : W ⟶ V} (e : y ≫ r = s ≫ y') (hr : IsIso r) (hy' : IsIso y') :
    IsIso (x ≫ y) ↔ IsIso (x ≫ s) := by
  rw [← isIso_comp_right_iff (x ≫ y) r, Category.assoc, e, ← Category.assoc,
    isIso_comp_right_iff]

/-- A natural isomorphism applied degreewise is an isomorphism of complexes. -/
private theorem isIso_mapHomologicalComplex_app {E : Type*} [Category* E] [Preadditive D]
    [Preadditive E] {F G : D ⥤ E} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) [IsIso α] {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex D c) :
    IsIso ((NatTrans.mapHomologicalComplex α c).app K) := by
  show IsIso ((NatIso.mapHomologicalComplex (asIso α) c).app K).hom
  infer_instance

end Abstract

/-! ### The derived base change map at a K-injective complex -/

section Criterion

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- The degreewise comparison on homotopy categories built from a transformation `α`, given as a
variable `w` equal to it, at the class of a complex `K`, is the class of the degreewise
comparison on `K`. -/
private theorem homotopyComparison_app_quotient_of_eq
    (α : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (w : (etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ))
    (hw : w = (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) :
    w.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) := by
  subst hw
  exact homotopyComparison_app_quotient.{u, v} f g g' f' α K

/-- **The degreewise base change comparison at the class of a complex** is the class of the
underived base change map applied degreewise. -/
theorem etaleAbelianHomotopyBaseChange_app_quotient (h : g' ≫ f = f' ≫ g)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) :
    (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app K) :=
  homotopyComparison_app_quotient_of_eq f g g' f' _ _
    (by rw [etaleAbelianHomotopyBaseChange]) K

/-- `isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso` for variable transformations: the
derived map `bc` and the homotopy-level comparison `w`, related by the defining factorization
`hfac` of the shape of `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac`, and the
underived map `α`, related to `w` by `hw`. -/
private theorem isIso_iff_quasiIso_of_fac
    (α : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (w : (etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    [I.IsKInjective]
    {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    [J.IsKInjective]
    (t : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso t]
    (hw : w.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I))
    (bc : (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ⟶
      (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f').obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))
    (hfac : (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫ bc =
    DerivedCategory.Qh.map (w.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :
    IsIso bc ↔ QuasiIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  have s4 : ∀ {A : Type (max (u + 1) v + 1)} [Category.{max (u + 1) v} A] [Abelian A]
      {M N : CochainComplex A ℤ} (ψ : M ⟶ N),
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ψ)) ↔
        QuasiIso ψ := fun ψ ↦ by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
      ← isIso_comp_right_iff _ ((DerivedCategory.quotientCompQhIso _).hom.app _),
      DerivedCategory.quotientCompQhIso_hom_naturality, isIso_comp_left_iff]
  have hu : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (etaleAbelianDirectImage.{u, v} f) I
  have hu' : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (etaleAbelianDirectImage.{u, v} f') J
  have ht : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)) := (s4 t).2 ‹_›
  have hn := ((etaleAbelianDerivedDirectImageUnit.{u, v} f').naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)).symm
  refine (isIso_iff_of_fac hfac inferInstance (Functor.map_isIso _ _) inferInstance).trans ?_
  refine (isIso_comp_iff_of_square _ hn (by
    exact Functor.map_isIso (etaleAbelianDerivedDirectImage.{u, v} f')
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)))
    hu').trans ?_
  rw [hw]
  have e : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I)) ≫
      (etaleAbelianPushforwardToDerivedCategory.{u, v} f').map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          t)) := by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  exact (congrArg IsIso e).to_iff.trans (s4 _)

/-- **The derived base change map at a K-injective complex.** Let `I` be a K-injective complex of
abelian sheaves on `X_étale` and `t : (g')⁻¹ I ⟶ J` a quasi-isomorphism to a K-injective complex.
The base change map `g⁻¹ Rf_* I ⟶ Rf'_* (g')⁻¹ I` is an isomorphism if and only if the map of
complexes `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I ⟶ f'_* J`, the degreewise base change map followed by
`f'_*` of the resolution, is a quasi-isomorphism: both units of the derived direct images are
invertible at K-injective complexes, and the unit of `Rf'_*` is natural along `t`. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso (h : g' ≫ f = f' ≫ g)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    [I.IsKInjective]
    {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    [J.IsKInjective]
    (t : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso t] :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app (DerivedCategory.Q.obj I)) ↔
      QuasiIso ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map t) :=
  (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.quotientCompQhIso _).app I)).symm.trans
    (isIso_iff_quasiIso_of_fac f g g' f' _ _ I t
      (etaleAbelianHomotopyBaseChange_app_quotient.{v, u} f g g' f' h I) _
      (etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h _))

end Criterion

/-! ### Changing the coefficient category -/

section Coefficients

variable (Φ : AddCommGrpCat.{max (u + 1) v₀} ⥤ AddCommGrpCat.{max (u + 1) v})
  [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op]
  [∀ S : Scheme.{u}, S.smallEtaleTopology.HasSheafCompose Φ]
  [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]

/-- **The comparison of inverse image with a change of coefficients**, `g⁻¹ (Φ F) ⟶ Φ (g⁻¹ F)`:
the mate of the identity comparison of direct images,
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`. It is invertible
(`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`). -/
abbrev etaleAbelianInverseImageCoefficientSquare {X Y : Scheme.{u}} (i : Y ⟶ X) :
    TwoSquare (sheafCompose X.smallEtaleTopology Φ)
      (etaleAbelianInverseImage.{u, v₀} i) (etaleAbelianInverseImage.{u, v} i)
      (sheafCompose Y.smallEtaleTopology Φ) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange i) X.smallEtaleTopology Y.smallEtaleTopology Φ

/-- The comparison `etaleAbelianInverseImageCoefficientSquare` as a natural transformation
`Φ ⋙ i⁻¹ ⟶ i⁻¹ ⋙ Φ`. -/
abbrev etaleAbelianInverseImageCoefficient {X Y : Scheme.{u}} (i : Y ⟶ X) :
    sheafCompose X.smallEtaleTopology Φ ⋙ etaleAbelianInverseImage.{u, v} i ⟶
      etaleAbelianInverseImage.{u, v₀} i ⋙ sheafCompose Y.smallEtaleTopology Φ :=
  (etaleAbelianInverseImageCoefficientSquare Φ i).natTrans

/-- The comparison `etaleAbelianInverseImageCoefficient Φ i : Φ ⋙ i⁻¹ ⟶ i⁻¹ ⋙ Φ` is an
isomorphism. -/
instance isIso_etaleAbelianInverseImageCoefficient {X Y : Scheme.{u}} (i : Y ⟶ X) :
    IsIso (etaleAbelianInverseImageCoefficient Φ i) :=
  isIso_coefficientPullbackTwoSquare (smallEtaleBaseChange i) X.smallEtaleTopology
    Y.smallEtaleTopology Φ

omit [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
  [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op] in
/-- The identity comparison `Φ ⋙ i_* ⟶ i_* ⋙ Φ`: direct image commutes with a change of
coefficients on the nose. -/
private def coefficientDirectImageInv {X Y : Scheme.{u}} (i : X ⟶ Y) :
    sheafCompose X.smallEtaleTopology Φ ⋙ etaleAbelianDirectImage.{u, v} i ⟶
      etaleAbelianDirectImage.{u, v₀} i ⋙ sheafCompose Y.smallEtaleTopology Φ :=
  𝟙 _

omit [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
  [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op] in
private theorem coefficientDirectImageInv_app {X Y : Scheme.{u}} (i : X ⟶ Y)
    (c : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) :
    (coefficientDirectImageInv Φ i).app c = 𝟙 _ := rfl

omit [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
  [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op] in
private theorem coefficientPushforwardTwoSquare_app_eq_id {X Y : Scheme.{u}} (i : X ⟶ Y)
    (c : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) :
    (coefficientPushforwardTwoSquare (smallEtaleBaseChange i) Y.smallEtaleTopology
      X.smallEtaleTopology Φ).natTrans.app c = 𝟙 _ := rfl

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The underived base change map commutes with a change of coefficients**: after applying
`Φ`, the base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of the source coefficients is that of the target
coefficients, up to the comparisons `etaleAbelianInverseImageCoefficientSquare` of the inverse
images with `Φ`. Both maps are mates of the comparison of composite direct images, and those agree
after `Φ` on sections, so this is the cube identity
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app`. -/
theorem etaleAbelianBaseChange_sheafCompose
    (c : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) :
    (etaleAbelianInverseImageCoefficientSquare Φ g).natTrans.app
          ((etaleAbelianDirectImage.{u, v₀} f).obj c) ≫
        (sheafCompose Y'.smallEtaleTopology Φ).map
          ((etaleAbelianBaseChange.{u, v₀} f g g' f' h).app c) =
      (etaleAbelianBaseChange.{u, v} f g g' f' h).app
          ((sheafCompose X.smallEtaleTopology Φ).obj c) ≫
        (etaleAbelianDirectImage.{u, v} f').map
          ((etaleAbelianInverseImageCoefficientSquare Φ g').natTrans.app c) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v₀} f g g' f' h (g' ≫ f)
    rfl h, etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} f g g' f' h
    (g' ≫ f) rfl h]
  have key := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app
    (etaleAbelianInverseImageDirectImageAdj.{u, v₀} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, v₀} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (etaleAbelianInverseImageCoefficientSquare Φ g')
    (etaleAbelianInverseImageCoefficientSquare Φ g)
    (coefficientPushforwardTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology Φ).natTrans
    (coefficientDirectImageInv Φ f')
    (smallEtaleDirectImageSquare f g g' f' h AddCommGrpCat.{max (u + 1) v₀})
    (smallEtaleDirectImageSquare f g g' f' h AddCommGrpCat.{max (u + 1) v}) (by
      have hm : ∀ {S T : Scheme.{u}} (i : T ⟶ S),
          mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v₀} i)
              (etaleAbelianInverseImageDirectImageAdj.{u, v} i)
              (etaleAbelianInverseImageCoefficientSquare Φ i) =
            coefficientPushforwardTwoSquare (smallEtaleBaseChange i) S.smallEtaleTopology
              T.smallEtaleTopology Φ :=
        fun _ ↦ mateEquiv_coefficientPullbackTwoSquare _ _ _ _
      rw [hm g', hm g]
      refine TwoSquare.ext _ _ fun d => ?_
      rw [ts_whiskerLeft_app, ts_whiskerRight_app, ts_vComp_app, ts_vComp_app]
      simp only [coefficientPushforwardTwoSquare_app_eq_id, coefficientDirectImageInv_app,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      show _ = (sheafCompose Y.smallEtaleTopology Φ).map
        ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl _).hom.app d ≫
          (smallEtalePushforwardComp' f' g (g' ≫ f) h _).inv.app _)
      rw [Functor.map_comp, sheafCompose_map_smallEtalePushforwardComp'_hom,
        sheafCompose_map_smallEtalePushforwardComp'_inv]
      rfl) c
  refine key.trans ?_
  simp only [coefficientPushforwardTwoSquare_app_eq_id, coefficientDirectImageInv_app]
  show (etaleAbelianInverseImage.{u, v} g).map (𝟙 ((sheafCompose Y.smallEtaleTopology Φ).obj
    ((etaleAbelianDirectImage.{u, v₀} f).obj c))) ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  show _ ≫ _ ≫ 𝟙 ((etaleAbelianDirectImage.{u, v} f').obj
    ((sheafCompose X'.smallEtaleTopology Φ).obj ((etaleAbelianInverseImage.{u, v₀} g').obj c))) = _
  rw [Category.comp_id]
  rfl

end Coefficients

/-! ### The base change map after a change of coefficients -/

section Transfer

variable (Φ : AddCommGrpCat.{max (u + 1) v₀} ⥤ AddCommGrpCat.{max (u + 1) v})
  [∀ S : Scheme.{u}, S.smallEtaleTopology.HasSheafCompose Φ]
  [∀ S : Scheme.{u}, (sheafCompose S.smallEtaleTopology Φ).Additive]

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The complex-level square behind `isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`,
for variable transformations `βs`, `βb` (in place of the two base change maps) and `τ`, `τ'` (in
place of the comparisons of the inverse images with the universe lift) satisfying the underived
agreement `hC`. -/
private theorem coefficient_complex_square
    (βs : etaleAbelianDirectImage.{u, v₀} f ⋙ etaleAbelianInverseImage.{u, v₀} g ⟶
      etaleAbelianInverseImage.{u, v₀} g' ⋙ etaleAbelianDirectImage.{u, v₀} f')
    (βb : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (τ : (sheafCompose Y.smallEtaleTopology Φ) ⋙
        etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v₀} g ⋙ (sheafCompose Y'.smallEtaleTopology Φ))
    (τ' : (sheafCompose X.smallEtaleTopology Φ) ⋙
        etaleAbelianInverseImage.{u, v} g' ⟶
      etaleAbelianInverseImage.{u, v₀} g' ⋙
        (sheafCompose X'.smallEtaleTopology Φ))
    (hC : ∀ c, τ.app ((etaleAbelianDirectImage.{u, v₀} f).obj c) ≫
        ((sheafCompose Y'.smallEtaleTopology Φ)).map (βs.app c) =
      βb.app (((sheafCompose X.smallEtaleTopology Φ)).obj c) ≫
        (etaleAbelianDirectImage.{u, v} f').map (τ'.app c))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) ℤ)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) ℤ}
    (t : ((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J)
    (tb : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ⟶
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    (htb : tb = (NatTrans.mapHomologicalComplex τ' (ComplexShape.up ℤ)).app I ≫
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).map t) :
    (NatTrans.mapHomologicalComplex βb (ComplexShape.up ℤ)).app
        ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫
      ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
        tb =
    (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        (((etaleAbelianDirectImage.{u, v₀} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      (((sheafCompose Y'.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex βs (ComplexShape.up ℤ)).app I ≫
          ((etaleAbelianDirectImage.{u, v₀} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
            t) := by
  subst htb
  ext n : 1
  show βb.app _ ≫ (etaleAbelianDirectImage.{u, v} f').map (τ'.app (I.X n) ≫
      ((sheafCompose X'.smallEtaleTopology Φ)).map (t.f n)) =
    τ.app _ ≫ ((sheafCompose Y'.smallEtaleTopology Φ)).map (βs.app (I.X n) ≫
      (etaleAbelianDirectImage.{u, v₀} f').map (t.f n))
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hC]
  rfl

/-- The comparison of complexes of the larger universe is a quasi-isomorphism when that of the
smaller one is, for variable transformations as in `coefficient_complex_square`. -/
private theorem quasiIso_coefficient_comparison
    [∀ S : Scheme.{u}, PreservesFiniteLimits (sheafCompose S.smallEtaleTopology Φ)]
    [∀ S : Scheme.{u}, PreservesFiniteColimits (sheafCompose S.smallEtaleTopology Φ)]
    (βs : etaleAbelianDirectImage.{u, v₀} f ⋙ etaleAbelianInverseImage.{u, v₀} g ⟶
      etaleAbelianInverseImage.{u, v₀} g' ⋙ etaleAbelianDirectImage.{u, v₀} f')
    (βb : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (τ : (sheafCompose Y.smallEtaleTopology Φ) ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v₀} g ⋙ (sheafCompose Y'.smallEtaleTopology Φ)) [IsIso τ]
    (τ' : (sheafCompose X.smallEtaleTopology Φ) ⋙ etaleAbelianInverseImage.{u, v} g' ⟶
      etaleAbelianInverseImage.{u, v₀} g' ⋙ (sheafCompose X'.smallEtaleTopology Φ))
    (hC : ∀ c, τ.app ((etaleAbelianDirectImage.{u, v₀} f).obj c) ≫
        ((sheafCompose Y'.smallEtaleTopology Φ)).map (βs.app c) =
      βb.app (((sheafCompose X.smallEtaleTopology Φ)).obj c) ≫
        (etaleAbelianDirectImage.{u, v} f').map (τ'.app c))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) ℤ)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) ℤ}
    (t : ((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J)
    (tb : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ⟶
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    (htb : tb = (NatTrans.mapHomologicalComplex τ' (ComplexShape.up ℤ)).app I ≫
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).map t)
    (hs : QuasiIso ((NatTrans.mapHomologicalComplex βs (ComplexShape.up ℤ)).app I ≫
      ((etaleAbelianDirectImage.{u, v₀} f').mapHomologicalComplex (ComplexShape.up ℤ)).map t)) :
    QuasiIso ((NatTrans.mapHomologicalComplex βb (ComplexShape.up ℤ)).app
        ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫
      ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
        tb) := by
  rw [coefficient_complex_square.{v₀, v} Φ f g g' f' βs βb τ τ' hC I t tb htb]
  have : IsIso ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
      (((etaleAbelianDirectImage.{u, v₀} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    isIso_mapHomologicalComplex_app _ _ _
  have h2 : QuasiIso ((((sheafCompose Y'.smallEtaleTopology Φ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex βs (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, v₀} f').mapHomologicalComplex (ComplexShape.up ℤ)).map t)) :=
    inferInstance
  have h1 : QuasiIso ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
      (((etaleAbelianDirectImage.{u, v₀} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h1) (hφ' := h2)

/-- The small half of `isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`: invertibility
of the base change map at `G` is quasi-invertibility of the comparison of complexes built from
injective resolutions. -/
private theorem quasiIso_of_isIso_etaleAbelianSheafDerivedBaseChange
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀})
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) 0).obj G))
    [R.cocomplex.IsKInjective]
    (R' : CochainComplex.InjectiveResolution
      (((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        R.cocomplex)) [R'.cocomplex.IsKInjective]
    (hG : IsIso (etaleAbelianSheafDerivedBaseChange.{u, v₀} f g g' f' h G)) :
    QuasiIso ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v₀} f g g' f' h)
      (ComplexShape.up ℤ)).app R.cocomplex ≫
      ((etaleAbelianDirectImage.{u, v₀} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
        R'.ι) := by
  rw [← isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso.{v₀, u} f g g' f' h R.cocomplex
    R'.ι]
  have : IsIso (DerivedCategory.Q.map R.ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ R.ι).2 R.quasiIso
  exact (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G ≪≫
    asIso (DerivedCategory.Q.map R.ι))).1 hG

/-- The universe lift of a bounded below complex of injective abelian sheaves on the small étale
site is K-injective. -/
private theorem isKInjective_sheafCompose_mapHomologicalComplex
    [∀ S : Scheme.{u}, (sheafCompose S.smallEtaleTopology Φ).PreservesInjectiveObjects]
    {Z : Scheme.{u}}
    {K : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) ℤ}
    (R : CochainComplex.InjectiveResolution K) :
    CochainComplex.IsKInjective
      ((((sheafCompose Z.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex) := by
  obtain ⟨d, hd⟩ := R.boundedBelow
  have : CochainComplex.IsStrictlyGE
      ((((sheafCompose Z.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex) d :=
    Stacks.DerivedFunctor.isStrictlyGE_mapHomologicalComplex _ _ d
  have : ∀ n, Injective
      (((((sheafCompose Z.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex).X n) :=
    fun n ↦ ((sheafCompose Z.smallEtaleTopology Φ)).injective_obj
      (R.cocomplex.X n)
  exact CochainComplex.isKInjective_of_injective _ d

/-- The large half of `isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`: if the
comparison of complexes built from injective resolutions is a quasi-isomorphism, the base change
map of the larger universe is invertible at the universe lift of the resolving complex. -/
private theorem isIso_etaleAbelianDerivedBaseChange_app_sheafCompose
    [∀ S : Scheme.{u}, PreservesFiniteLimits (sheafCompose S.smallEtaleTopology Φ)]
    [∀ S : Scheme.{u}, PreservesFiniteColimits (sheafCompose S.smallEtaleTopology Φ)]
    [∀ S : Scheme.{u}, (sheafCompose S.smallEtaleTopology Φ).PreservesInjectiveObjects]
    [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op]
    [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀})
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) 0).obj G))
    (R' : CochainComplex.InjectiveResolution
      (((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        R.cocomplex))
    (hs : QuasiIso ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v₀} f g g' f' h)
      (ComplexShape.up ℤ)).app R.cocomplex ≫
      ((etaleAbelianDirectImage.{u, v₀} f').mapHomologicalComplex (ComplexShape.up ℤ)).map R'.ι)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Q.obj ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex))) := by
  have := isKInjective_sheafCompose_mapHomologicalComplex.{v₀, v} Φ R
  have := isKInjective_sheafCompose_mapHomologicalComplex.{v₀, v} Φ R'
  have : QuasiIso ((NatTrans.mapHomologicalComplex
      (etaleAbelianInverseImageCoefficient.{v₀, v} Φ g') (ComplexShape.up ℤ)).app R.cocomplex ≫
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        R'.ι) := by
    have : IsIso ((NatTrans.mapHomologicalComplex
        (etaleAbelianInverseImageCoefficient.{v₀, v} Φ g') (ComplexShape.up ℤ)).app
        R.cocomplex) :=
      isIso_mapHomologicalComplex_app _ _ _
    infer_instance
  have hq := quasiIso_coefficient_comparison.{v₀, v} Φ f g g' f'
    (etaleAbelianBaseChange.{u, v₀} f g g' f' h) (etaleAbelianBaseChange.{u, v} f g g' f' h)
    (etaleAbelianInverseImageCoefficient.{v₀, v} Φ g)
    (etaleAbelianInverseImageCoefficient.{v₀, v} Φ g')
    (etaleAbelianBaseChange_sheafCompose.{v₀, v} Φ f g g' f' h) R.cocomplex R'.ι _ rfl hs
  exact (isIso_etaleAbelianDerivedBaseChange_app_Q_iff_quasiIso.{v, u} f g g' f' h
    ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cocomplex)
    (J := (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R'.cocomplex)
    ((NatTrans.mapHomologicalComplex (etaleAbelianInverseImageCoefficient.{v₀, v} Φ g')
      (ComplexShape.up ℤ)).app R.cocomplex ≫
      (((sheafCompose X'.smallEtaleTopology Φ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        R'.ι)).2 hq

/-- **The base change map commutes with an exact change of coefficients.** Let
`Φ : AddCommGrpCat.{max (u + 1) v₀} ⥤ AddCommGrpCat.{max (u + 1) v}` be a functor such that
composition with `Φ` is an exact functor of abelian sheaves on every small étale site, carrying
injective sheaves to injective sheaves, and commuting with sheafification and with the left Kan
extensions computing inverse images. For a commutative square `g' ≫ f = f' ≫ g`, if the base
change map `g⁻¹ Rf_* G ⟶ Rf'_* (g')⁻¹ G` is an isomorphism at an abelian sheaf `G`, so is the
base change map of the target coefficients at every sheaf isomorphic to `Φ ∘ G`. The universe lift
`AddCommGrpCat.uliftFunctor` is such a functor. -/
theorem isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose
    [∀ S : Scheme.{u}, PreservesFiniteLimits (sheafCompose S.smallEtaleTopology Φ)]
    [∀ S : Scheme.{u}, PreservesFiniteColimits (sheafCompose S.smallEtaleTopology Φ)]
    [∀ S : Scheme.{u}, (sheafCompose S.smallEtaleTopology Φ).PreservesInjectiveObjects]
    [∀ {S T : Scheme.{u}} (i : T ⟶ S), Φ.PreservesLeftKanExtensions (smallEtaleBaseChange i).op]
    [∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification Φ]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀})
    (hG : IsIso (etaleAbelianSheafDerivedBaseChange.{u, v₀} f g g' f' h G))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (eF : (sheafCompose X.smallEtaleTopology Φ).obj G ≅ F) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h F) := by
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₀}) 0).obj G)
  have : CochainComplex.IsStrictlyGE (((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.cocomplex) 0 :=
    Stacks.DerivedFunctor.isStrictlyGE_mapHomologicalComplex _ _ 0
  obtain ⟨R', -, hR'⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    (((etaleAbelianInverseImage.{u, v₀} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cocomplex)
  have : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex 0
  have : R'.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R'.cocomplex 0
  have hb := isIso_etaleAbelianDerivedBaseChange_app_sheafCompose.{v₀, v} Φ f g g' f' h G R R'
    (quasiIso_of_isIso_etaleAbelianSheafDerivedBaseChange f g g' f' h G R R' hG)
  have : IsIso (DerivedCategory.Q.map
      ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map R.ι)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : (DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F ≅
      DerivedCategory.Q.obj ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex) :=
    ((DerivedCategory.singleFunctor _ 0).mapIso eF).symm ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        ((sheafCompose X.smallEtaleTopology Φ)) (ComplexShape.up ℤ) 0).app
          G).symm ≪≫
      asIso (DerivedCategory.Q.map
        ((((sheafCompose X.smallEtaleTopology Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map R.ι))
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 hb

end Transfer

/-! ### Filtered colimits -/

section Colimit

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **Invertibility of the base change map passes to filtered colimits**, for a cartesian square
with `f` quasi-compact and quasi-separated. In each degree both sides of the base change map
commute with filtered colimits: `g⁻¹` and `(g')⁻¹` are left adjoints, and the higher direct images
along `f` and along its base change `f'` commute with filtered colimits ([Stacks, Tag 09Z1]). -/
theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] {I : Type (max (u + 1) v)} [SmallCategory I]
    [IsFiltered I] (K : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ i, IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w (K.obj i))) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w c.pt) := by
  have : QuasiCompact f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  have : QuasiSeparated f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹_›
  rw [DerivedCategory.isIso_iff]
  intro q
  rcases lt_or_ge q 0 with hq | hq
  · exact isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg f g g' f' sq.w c.pt q hq
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have : PreservesColimit K ((etaleAbelianDirectImage.{u, v} f).rightDerived p) := by
      have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{v, u} f p I
      exact PreservesColimitsOfShape.preservesColimit
    have : PreservesColimit (K ⋙ etaleAbelianInverseImage.{u, v} g')
        ((etaleAbelianDirectImage.{u, v} f').rightDerived p) := by
      have := preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage.{v, u} f' p I
      exact PreservesColimitsOfShape.preservesColimit
    have : PreservesColimit (K ⋙ (etaleAbelianDirectImage.{u, v} f).rightDerived p)
        (etaleAbelianInverseImage.{u, v} g) := inferInstance
    have : PreservesColimit K (etaleAbelianInverseImage.{u, v} g') := inferInstance
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
          (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g)) ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ)) :=
      preservesColimit_of_natIso K (etaleAbelianHigherBaseChangeSourceIso f g p).symm
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
          (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')) ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℤ)) :=
      preservesColimit_of_natIso K (etaleAbelianHigherBaseChangeTargetIso g' f' p).symm
    refine isIso_app_of_isColimit (etaleAbelianHigherBaseChange f g g' f' sq.w (p : ℤ)) hc
      (fun i ↦ ?_)
    have := hK i
    exact Functor.map_isIso (DerivedCategory.homologyFunctor _ (p : ℤ))
      (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w (K.obj i))

end Colimit


end BaseChangeMapInstances

/-! ### The transfer -/

/-- **Cohomology commutes with base change at every coefficient universe.** For a quasi-compact
and quasi-separated morphism `f : X ⟶ Y`, if the base change map is invertible at every torsion
abelian sheaf with sections in `AddCommGrpCat.{u + 1}`, it is invertible at every torsion abelian
sheaf with sections in `AddCommGrpCat.{max (u + 1) v}`.

A torsion sheaf `F` of the larger universe is the filtered colimit of the sheafifications of its
small subpresheaves (`smallSubpresheafSheafCoconeIsColimit`), each of which is the universe lift
of a torsion sheaf of the smaller universe (`smallSubpresheafSheafIso`); the base change map is
invertible at universe lifts (`isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose`) and its
invertibility passes to filtered colimits
(`isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit`). -/
theorem CohomologyCommutesWithBaseChange.of_univ_zero {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] (hf : CohomologyCommutesWithBaseChange.{u, 0} f) :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  intro X' Y' g g' f' sq F hF
  have : ∀ S : Scheme.{u}, S.smallEtaleTopology.HasSheafCompose
      AddCommGrpCat.uliftFunctor.{v, u + 1} := fun _ ↦ inferInstance
  have : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}) :=
    fun S ↦ preservesFiniteLimits_uliftSheafFunctor.{v, u + 1} S.smallEtaleTopology
  have : ∀ S : Scheme.{u}, PreservesFiniteColimits
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}) :=
    fun S ↦ preservesFiniteColimits_uliftSheafFunctor.{v, u + 1} S.smallEtaleTopology
  have : ∀ S : Scheme.{u},
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}).Additive :=
    fun _ ↦ Functor.additive_of_preserves_binary_products _
  have : ∀ S : Scheme.{u},
      (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{v, u + 1}).PreservesInjectiveObjects :=
    fun S ↦ preservesInjectiveObjects_uliftSheafFunctor_smallEtale_of_univLE.{0, v} S
  have : ∀ {S T : Scheme.{u}} (i : T ⟶ S),
      AddCommGrpCat.uliftFunctor.{v, u + 1}.PreservesLeftKanExtensions
        (smallEtaleBaseChange i).op := fun _ ↦ inferInstance
  have : ∀ S : Scheme.{u}, S.smallEtaleTopology.PreservesSheafification
      AddCommGrpCat.uliftFunctor.{v, u + 1} :=
    fun _ ↦ preservesSheafification_uliftFunctor.{u + 1, u, u + 1, v}
  refine isIso_etaleAbelianSheafDerivedBaseChange_of_isColimit f g g' f' sq
    (smallSubpresheafSheafDiagram F) (smallSubpresheafSheafCoconeIsColimit F) (fun S ↦ ?_)
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, 0} X
  have hG : Stacks.Torsion.torsionSheafProperty.{u + 1, u, u + 1} X.smallEtaleTopology
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S.shrinkPresheaf) :=
    Stacks.Torsion.torsionSheafProperty_sheafify X.smallEtaleTopology S.shrinkPresheaf
      (S.isLocallyTorsion_shrinkPresheaf hF)
  exact isIso_etaleAbelianSheafDerivedBaseChange_sheafCompose.{0, v}
    AddCommGrpCat.uliftFunctor.{v, u + 1} f g g' f' sq.w _ (hf g g' f' sq _ hG) _
    (smallSubpresheafSheafIso F S)

end Stacks.EtaleCohomology

end
