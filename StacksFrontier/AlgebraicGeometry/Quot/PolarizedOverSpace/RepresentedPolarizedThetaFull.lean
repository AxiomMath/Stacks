module

public import
        StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedThetaFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso

/-!
# The comparison `Θ : RepresentedPolarized ⥤ Polarized` is full

A morphism `Θ X ⟶ Θ Y` of polarized families is a cartesian square of schemes of the site together
with an isomorphism `t^*(R M_Y) ≅ R M_X` of polarizations, where `R` restricts a module on the
small étale site of `yoneda Z` to the Zariski site of `Z`. Over the terminal base `Spec(ℤ)` the
square is a square of the site (`AlgebraicGeometry.BigFppfOver.fullyFaithfulToScheme`), and
composing the isomorphism of polarizations with the comparison `R((h)^* M_Y) ≅ t^*(R M_Y)` of
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso` gives an isomorphism
`R(h^* M_Y) ≅ R M_X`, which comes from an isomorphism `h^* M_Y ≅ M_X` because `R` is full on
quasi-coherent modules (its counit is an isomorphism there).

## Main results

* `CategoryTheory.Adjunction.map_preimageOfIsIsoCounitApp`: a right adjoint is full between objects
  at which the counit is an isomorphism.
* `AlgebraicGeometry.PolarizedOverSpace.toPolarized_full`: `Θ` is full.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The preimage under a right adjoint of a morphism between objects at which the counit is an
isomorphism: `ε⁻¹ ≫ L χ ≫ ε`. -/
def preimageOfIsIsoCounitApp {M N : D} (hM : IsIso (adj.counit.app M)) (χ : R.obj M ⟶ R.obj N) :
    M ⟶ N :=
  inv (adj.counit.app M) ≫ L.map χ ≫ adj.counit.app N

/-- **A right adjoint is full between objects at which the counit is an isomorphism.** -/
theorem map_preimageOfIsIsoCounitApp {M N : D} (hM : IsIso (adj.counit.app M))
    (χ : R.obj M ⟶ R.obj N) : R.map (adj.preimageOfIsIsoCounitApp hM χ) = χ := by
  have h1 : R.map (inv (adj.counit.app M)) = adj.unit.app (R.obj M) := by
    rw [← cancel_mono (R.map (adj.counit.app M)), ← R.map_comp, IsIso.inv_hom_id, R.map_id,
      adj.right_triangle_components]
    rfl
  rw [preimageOfIsIsoCounitApp, R.map_comp, R.map_comp, h1, adj.unit_naturality_assoc,
    adj.right_triangle_components, Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso
        Scheme.Modules.pullback
  Space.representedSmallEtaleModuleEquivalence SmallEtale.restrictModule

variable {B : BigFppfSite.{u}}

/-- The counit of restriction to the Zariski site is an isomorphism at a quasi-coherent module. -/
theorem isIso_zariskiCounit {A : Arrow (Site B)} (M : SheafOfModules.{u}
        (Space.representedStructureRingSheaf B integerBase (hZ B) A.left))
    (hM : SheafOfModules.IsQuasicoherentOnSite M) :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B integerBase (hZ B)).obj A.left)
        A.left.left.property).counit.app ((etaleInverse A).obj M)) :=
  _root_.AlgebraicGeometry.SmallEtale.isIso_counit _ _ _ _
    (Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase (hZ B) A.left M hM)
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule _ _ _ _
      (Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase (hZ B) A.left M hM))

/-- The preimage under `R` of a morphism of restrictions of a quasi-coherent module. -/
def zariskiPreimage {A : Arrow (Site B)} {M N : SheafOfModules.{u}
        (Space.representedStructureRingSheaf B integerBase (hZ B) A.left)}
    (hM : SheafOfModules.IsQuasicoherentOnSite M)
    (χ : (zariskiRestriction A).obj ((etaleInverse A).obj M) ⟶
      (zariskiRestriction A).obj ((etaleInverse A).obj N)) : M ⟶ N :=
  (etaleInverse A).preimage
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase (hZ B)).obj A.left)
      A.left.left.property).preimageOfIsIsoCounitApp (isIso_zariskiCounit M hM) χ)

/-- **`R` is full on quasi-coherent modules.** -/
theorem map_zariskiPreimage {A : Arrow (Site B)} {M N : SheafOfModules.{u}
        (Space.representedStructureRingSheaf B integerBase (hZ B) A.left)}
    (hM : SheafOfModules.IsQuasicoherentOnSite M)
    (χ : (zariskiRestriction A).obj ((etaleInverse A).obj M) ⟶
      (zariskiRestriction A).obj ((etaleInverse A).obj N)) :
    (zariskiRestriction A).map ((etaleInverse A).map (zariskiPreimage hM χ)) = χ :=
  (congrArg (zariskiRestriction A).map (Functor.map_preimage (etaleInverse A) _)).trans
    (Adjunction.map_preimageOfIsIsoCounitApp _ _ χ)

/-- An isomorphism of restrictions of quasi-coherent modules comes from an isomorphism. -/
def zariskiPreimageIso {A : Arrow (Site B)} {M N : SheafOfModules.{u}
        (Space.representedStructureRingSheaf B integerBase (hZ B) A.left)}
    (hM : SheafOfModules.IsQuasicoherentOnSite M) (hN : SheafOfModules.IsQuasicoherentOnSite N)
    (χ : (zariskiRestriction A).obj ((etaleInverse A).obj M) ≅
      (zariskiRestriction A).obj ((etaleInverse A).obj N)) : M ≅ N where
  hom := zariskiPreimage hM χ.hom
  inv := zariskiPreimage hN χ.inv
  hom_inv_id := zariskiRestriction_map_injective hM (by
    rw [Functor.map_comp, Functor.map_comp, map_zariskiPreimage, map_zariskiPreimage,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  inv_hom_id := zariskiRestriction_map_injective hN (by
    rw [Functor.map_comp, Functor.map_comp, map_zariskiPreimage, map_zariskiPreimage,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])

/-- An isomorphism whose source is transported along an equality of objects. -/
theorem _root_.CategoryTheory.Iso.heq_of_hom_eq_eqToHom_comp {C : Type*} [Category C] {A A' D : C}
    (h : A = A') (e : A ≅ D) (e' : A' ≅ D) (hh : e.hom = eqToHom h ≫ e'.hom) : e ≍ e' := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hh
  exact heq_of_eq (Iso.ext hh)

section Full

variable {X Y : RepresentedPolarized B} (p : toPolarizedObj B X ⟶ toPolarizedObj B Y)

/-- The map of total spaces of the preimage. -/
def fullLeft : X.obj.obj.base.left ⟶ Y.obj.obj.base.left :=
  (BigFppfOver.fullyFaithfulToScheme B integerBase (hZ B) specULiftZIsTerminal).preimage p.totalMap

/-- The map of bases of the preimage. -/
def fullRight : X.obj.obj.base.right ⟶ Y.obj.obj.base.right :=
  (BigFppfOver.fullyFaithfulToScheme B integerBase (hZ B) specULiftZIsTerminal).preimage
    (B.inclusion.map p.baseMap)

/-- The underlying morphism of schemes of `fullLeft p` is the map of total spaces of `p`. -/
theorem sch_fullLeft : sch B (fullLeft p) = p.totalMap :=
  (BigFppfOver.fullyFaithfulToScheme B integerBase (hZ B) specULiftZIsTerminal).map_preimage _

/-- The underlying morphism of schemes of `fullRight p` is the map of bases of `p`. -/
theorem sch_fullRight : sch B (fullRight p) = B.inclusion.map p.baseMap :=
  (BigFppfOver.fullyFaithfulToScheme B integerBase (hZ B) specULiftZIsTerminal).map_preimage _

/-- The maps `fullLeft p` and `fullRight p` commute with the structure morphisms. -/
theorem fullLeft_comp : fullLeft p ≫ Y.obj.obj.base.hom = X.obj.obj.base.hom ≫ fullRight p :=
  (BigFppfOver.toScheme B integerBase (hZ B)).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    show sch B (fullLeft p) ≫ sch B Y.obj.obj.base.hom = sch B X.obj.obj.base.hom ≫
      sch B (fullRight p)
    rw [sch_fullLeft, sch_fullRight]
    exact p.cartesian.w)

/-- The morphism of arrows of the preimage. -/
def fullBase : @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver X.obj.obj.base Y.obj.obj.base :=
  Arrow.homMk (fullLeft p) (fullRight p) (fullLeft_comp p)

/-- The pullback of the polarization along the map of total spaces of the preimage. -/
theorem pullback_obj_fullLeft :
    (Scheme.Modules.pullback (sch B (fullBase p).left)).obj (zariskiPolarization B Y.obj.obj) =
      (Scheme.Modules.pullback p.totalMap).obj (toPolarizedObj B Y).lineBundle :=
  congrArg (fun t => (Scheme.Modules.pullback t).obj (zariskiPolarization B Y.obj.obj))
    (sch_fullLeft p)

/-- The isomorphism `R(h^* M_Y) ≅ R M_X` of a morphism of polarized families. -/
def fullZariskiIso :
    (zariskiRestriction X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj
      ((Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) (fullBase p).left)).obj Y.obj.obj.fiber)) ≅
      (zariskiRestriction X.obj.obj.base).obj ((etaleInverse X.obj.obj.base).obj X.obj.obj.fiber) :=
  (Space.representedZariskiModulePullbackIso B integerBase (hZ B) (fullBase p).left
      (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Y.obj.obj.fiber
      Y.obj.property.quasicoherent).symm ≪≫ eqToIso (pullback_obj_fullLeft p) ≪≫ p.lineBundleIso

/-- The comparison of modules of the preimage, `h^* M_Y ≅ M_X`. -/
def fullModuleIso :
    (Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) (fullBase p).left)).obj Y.obj.obj.fiber ≅
      X.obj.obj.fiber :=
  zariskiPreimageIso
    (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
      (fullBase p).left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
      Y.obj.obj.fiber Y.obj.property.quasicoherent)
    X.obj.property.quasicoherent (fullZariskiIso p)

/-- **The preimage of a morphism of polarized families under `Θ`.** -/
def fullPreimage : X ⟶ Y :=
  ⟨⟨⟨fullBase p, ((fullModuleIso p).inv : X.obj.obj.fiber ⟶
    ((arrowModules B).map (fullBase p).op.toLoc).toFunctor.obj Y.obj.obj.fiber)⟩⟩,
    ⟨by
      change IsPullback (sch B (fullLeft p)) _ _ (sch B (fullRight p))
      rw [sch_fullLeft, sch_fullRight]
      exact p.cartesian,
      ⟨⟨(fullModuleIso p).hom, (fullModuleIso p).inv_hom_id,
        (fullModuleIso p).hom_inv_id⟩⟩⟩⟩

/-- `Θ` sends `fullPreimage p` to `p`. -/
theorem toPolarizedMap_fullPreimage : toPolarizedMap B (fullPreimage p) = p := by
  refine PolarizedFamily.Hom.ext (B.inclusion.map_injective (sch_fullRight p)) (sch_fullLeft p)
    (Iso.heq_of_hom_eq_eqToHom_comp (pullback_obj_fullLeft p) _ _ ?_)
  have h1 : inv (I := isIso_fiber (fullPreimage p)) (fullPreimage p).hom.hom.fiber =
      (fullModuleIso p).hom := by
    have := isIso_fiber (fullPreimage p)
    exact IsIso.inv_eq_of_inv_hom_id (fullModuleIso p).hom_inv_id
  refine (toPolarizedLineBundleIso_hom_eq (fullPreimage p)).trans ?_
  refine (congrArg (fun x => _ ≫
    (zariskiRestriction X.obj.obj.base).map ((etaleInverse X.obj.obj.base).map x)) h1).trans ?_
  exact (congrArg _ (map_zariskiPreimage
    (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B)
      (fullBase p).left (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _)
      Y.obj.obj.fiber Y.obj.property.quasicoherent) (fullZariskiIso p).hom)).trans
    (Iso.hom_inv_id_assoc _ _)

end Full

variable (B) in
/-- **`Θ` is full.** -/
instance toPolarized_full : (toPolarized B).Full where
  map_surjective p := ⟨fullPreimage p, toPolarizedMap_fullPreimage p⟩

end AlgebraicGeometry.PolarizedOverSpace

end
