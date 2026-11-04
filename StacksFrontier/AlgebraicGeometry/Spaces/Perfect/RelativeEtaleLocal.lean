module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor

/-!
# Relative perfectness of objects of algebraic spaces is étale local

Consider a commutative square of algebraic spaces over `S`

```
X' --a--> X
|f'       |f
v         v
Y' --b--> Y
```

with `a` and `b` étale, and `f`, `f'` flat and locally of finite presentation. The geometric
stalks of `f⁻¹𝒪_Y` and `𝒪_X` are étale local rings, which étale morphisms do not change, so the
derived stalk of `L(a)^*E` at `x̄'` read over `(f'⁻¹𝒪_{Y'})_{x̄'}` is the derived stalk of `E`
at `a(x̄')` read over `(f⁻¹𝒪_Y)_{a(x̄')}`, up to a ring isomorphism. Consequently `L(a)^*E` is
`Y'`-perfect when `E` is `Y`-perfect, and `E` is `Y`-perfect as soon as its pullbacks along a
jointly surjective family of such squares are.

## Main results

* `hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback_iff`: the stalk
  comparison.
* `isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale`: relative perfectness
  passes to an étale square.
* `isPerfectRelativeToCanonical_of_forall_isEtale`: relative perfectness descends along a jointly
  surjective family of étale squares.

## References

* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.TorAmplitude

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Étale morphisms do not change the stalk rings -/

section Rings

/-- The canonical homomorphism of étale local rings along an étale morphism is bijective. -/
theorem bijective_etaleLocalRingMap_of_isEtale {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1) :
    Function.Bijective (etaleLocalRingMap Y.2 φ.hom y) := by
  rw [← eq_etaleLocalRingMap Y.2 φ.hom y
    (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS φ hφ y)]
  exact (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).symm.commRingCatIsoToRingEquiv.bijective

/-- The homomorphism of stalk rings along which the pullback of modules extends scalars is
bijective at every geometric point when the morphism is étale. -/
theorem bijective_smallEtaleStalkPullbackRingMap_of_isEtale {X' X : AlgebraicSpaces B S hS}
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) (x' : GeometricPoint B S hS X'.1) :
    Function.Bijective (smallEtaleStalkPullbackRingMap B S hS a x') := by
  have heq : smallEtaleStalkPullbackRingMap B S hS a x' =
      (pointStalkRingEquiv B S hS X' x').symm.toRingHom.comp
        ((etaleLocalRingMap X'.2 a.hom x').comp
          (pointStalkRingEquiv B S hS X (geometricPointMap a.hom x')).toRingHom) := by
    rw [← pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS a x']
    exact RingHom.ext fun z => ((pointStalkRingEquiv B S hS X' x').symm_apply_apply _).symm
  rw [heq]
  exact (pointStalkRingEquiv B S hS X' x').symm.bijective.comp
    ((bijective_etaleLocalRingMap_of_isEtale a ha x').comp
      (pointStalkRingEquiv B S hS X (geometricPointMap a.hom x')).bijective)

variable {X' X Y' Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (b : Y' ⟶ Y) (x' : GeometricPoint B S hS X'.1)

/-- The bottom homomorphism of the square of stalk rings of a commutative square with étale
right-hand side is bijective. -/
theorem bijective_relativeBaseStalkMap_of_isEtale (hb : IsEtale B S hS b.hom)
    (w : a ≫ f = f' ≫ b) : Function.Bijective (relativeBaseStalkMap a f' f b x' w) :=
  (relativeStalkRingEquiv f' x').symm.bijective.comp
    (((bijective_etaleLocalRingMap_of_isEtale b hb (geometricPointMap f'.hom x')).comp
      (RingEquiv.bijective (Iso.commRingCatIsoToRingEquiv (eqToIso
        (congrArg (etaleLocalRing B S hS Y.1)
          (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') w)))))).comp
      (relativeStalkRingEquiv f (geometricPointMap a.hom x')).bijective)

/-- **The square of stalk rings of a commutative square of algebraic spaces commutes**:
`(f⁻¹𝒪_Y)_{a(x̄')} ⟶ (𝒪_X)_{a(x̄')} ⟶ (𝒪_{X'})_{x̄'}` equals
`(f⁻¹𝒪_Y)_{a(x̄')} ⟶ (f'⁻¹𝒪_{Y'})_{x̄'} ⟶ (𝒪_{X'})_{x̄'}`, because the canonical homomorphisms
of étale local rings of Stacks 04NG compose. -/
theorem smallEtaleStalkPullbackRingMap_comp_relativeStalkMap (w : a ≫ f = f' ≫ b) :
    (smallEtaleStalkPullbackRingMap B S hS a x').comp
        (relativeStalkMap f (geometricPointMap a.hom x')) =
      (relativeStalkMap f' x').comp (relativeBaseStalkMap a f' f b x' w) := by
  have hw : a.hom ≫ f.hom = f'.hom ≫ b.hom := congrArg (fun k : X' ⟶ Y => k.hom) w
  refine RingHom.ext fun r => (pointStalkRingEquiv B S hS X' x').injective ?_
  have h1 := RingHom.congr_fun (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS a x')
    (relativeStalkMap f (geometricPointMap a.hom x') r)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at h1 ⊢
  rw [h1, pointStalkRingEquiv_relativeStalkMap, pointStalkRingEquiv_relativeStalkMap,
    relativeStalkRingEquiv_relativeBaseStalkMap]
  refine (RingHom.congr_fun (etaleLocalRingMap_comp X'.2 X.2 a.hom f.hom x') _).trans ?_
  refine (RingHom.congr_fun (etaleLocalRingMap_eq_of_hom_eq B S hS X'.2 hw x') _).trans ?_
  exact (RingHom.congr_fun (etaleLocalRingMap_comp X'.2 Y'.2 f'.hom b.hom x') _).symm

/-- The ring isomorphism `(f⁻¹𝒪_Y)_{a(x̄')} ≅ (f'⁻¹𝒪_{Y'})_{x̄'}` of a commutative square with
étale right-hand side. -/
def relativeBaseStalkRingEquiv (hb : IsEtale B S hS b.hom) (w : a ≫ f = f' ≫ b) :
    relativeStalkRing f (geometricPointMap a.hom x') ≃+* relativeStalkRing f' x' :=
  RingEquiv.ofBijective _ (bijective_relativeBaseStalkMap_of_isEtale a f' f b x' hb w)

end Rings

/-! ### Restriction of scalars after an invertible extension of scalars -/

section ModuleCat

variable {R A R' C : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing C]

/-- Extension of scalars along a bijective ring homomorphism, followed by restriction of scalars
along a square of ring homomorphisms whose bottom edge is a ring isomorphism, is restriction of
scalars. -/
def restrictScalarsIsoExtendScalarsRestrictScalars (ψ : R →+* A) (ψ' : R' →+* C) (φ : A →+* C)
    (hφ : Function.Bijective φ) (σ : R ≃+* R') (h : φ.comp ψ = ψ'.comp σ.toRingHom) :
    ModuleCat.restrictScalars.{u} ψ ≅
      ModuleCat.extendScalars.{u, u, u} φ ⋙ ModuleCat.restrictScalars ψ' ⋙
        ModuleCat.restrictScalars σ.toRingHom :=
  haveI : (ModuleCat.restrictScalars.{u} φ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (RingEquiv.ofBijective φ hφ)
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u} φ).isEquivalence_left_of_isEquivalence_right
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (ModuleCat.extendRestrictScalarsAdj.{u} φ).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((ModuleCat.restrictScalarsComp' ψ φ (φ.comp ψ) rfl).symm ≪≫
      ModuleCat.restrictScalarsComp' σ.toRingHom ψ' (φ.comp ψ) h)

/-- The complex form of `restrictScalarsIsoExtendScalarsRestrictScalars`. -/
def restrictScalarsComplexIsoExtendScalarsRestrictScalars (ψ : R →+* A) (ψ' : R' →+* C)
    (φ : A →+* C) (hφ : Function.Bijective φ) (σ : R ≃+* R')
    (h : φ.comp ψ = ψ'.comp σ.toRingHom) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars ψ').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≅
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((restrictScalarsIsoExtendScalarsRestrictScalars ψ ψ' φ hφ σ h).app (M.X i)).symm)
    (fun i j _ => ((restrictScalarsIsoExtendScalarsRestrictScalars ψ ψ' φ hφ σ h).inv.naturality
      (M.d i j)).symm)

end ModuleCat

/-! ### The stalk comparison -/

section Stalk

open AlgebraicGeometry.BaseChangeTorAmplitude (hasTorAmplitudeCanonical_of_iso)

variable {X' X Y' Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (b : Y' ⟶ Y)

/-- **The relative derived stalks along an étale square.** For a commutative square
`a ≫ f = f' ≫ b` of algebraic spaces with `a` and `b` étale, the derived stalk of `L(a)^*E` at
`x̄'`, read over `(f'⁻¹𝒪_{Y'})_{x̄'}`, has Tor amplitude in `[lo, hi]` exactly when the derived
stalk of `E` at `a(x̄')`, read over `(f⁻¹𝒪_Y)_{a(x̄')}`, does: étale morphisms induce
isomorphisms of étale local rings (Stacks 04NG), and the stalk of the pullback is the extension
of scalars of the stalk (Stacks 05V5). -/
theorem hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback_iff
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (w : a ≫ f = f' ≫ b)
    (x' : GeometricPoint B S hS X'.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (lo hi : ℤ) :
    HasTorAmplitudeCanonical (relativeStalkRing f' x')
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).obj ((derivedScalarRestriction B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS a).obj E))) lo hi ↔
      HasTorAmplitudeCanonical (relativeStalkRing f (geometricPointMap a.hom x'))
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap a.hom x') X.2)
          (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
        lo hi := by
  let x := geometricPointMap a.hom x'
  obtain ⟨P, s, hs, hP, -⟩ :=
    exists_kFlat_resolution_kFlat_geometricStalks X (DerivedCategory.Q.objPreimage E)
  let eP : DerivedCategory.Q.obj P ≅ E :=
    @asIso _ _ _ _ (DerivedCategory.Q.map s)
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs) ≪≫
      DerivedCategory.Q.objObjPreimageIso E
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS a _ hP
  let eL : (smallEtaleDerivedModulePullback B S hS a).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS a).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
    (smallEtaleDerivedModulePullback B S hS a).mapIso
        ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso ((smallEtaleDerivedModulePullbackComparison B S hS a).app
        ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let M := stalkComplex x P
  let e₁ := (Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).mapIso
        ((derivedScalarRestriction B S hS f').mapIso
          ((smallEtaleDerivedModulePullback B S hS a).mapIso eP.symm ≪≫ eL)) ≪≫
      derivedRelativeStalkIso f' x' _ ≪≫
      DerivedCategory.Q.mapIso
        (((ModuleCat.restrictScalars (relativeStalkMap f' x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (pullbackStalkComplexIso a x' P))
  let e₂ := (Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapIso
        ((derivedScalarRestriction B S hS f).mapIso eP.symm) ≪≫
      derivedRelativeStalkIso f x P
  let σ := relativeBaseStalkRingEquiv a f' f b x' hb w
  let e₃ := restrictScalarsComplexIsoExtendScalarsRestrictScalars (relativeStalkMap f x)
    (relativeStalkMap f' x') (smallEtaleStalkPullbackRingMap B S hS a x')
    (bijective_smallEtaleStalkPullbackRingMap_of_isEtale a ha x') σ
    (smallEtaleStalkPullbackRingMap_comp_relativeStalkMap a f' f b x' w) M
  have key := AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
    σ (((ModuleCat.restrictScalars (relativeStalkMap f' x')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars
        (smallEtaleStalkPullbackRingMap B S hS a x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) lo hi
  exact ⟨fun h => hasTorAmplitudeCanonical_of_iso (DerivedCategory.Q.mapIso e₃ ≪≫ e₂.symm) lo hi
      (key.2 (hasTorAmplitudeCanonical_of_iso e₁ lo hi h)),
    fun h => hasTorAmplitudeCanonical_of_iso e₁.symm lo hi
      (key.1 (hasTorAmplitudeCanonical_of_iso (e₂ ≪≫ DerivedCategory.Q.mapIso e₃.symm) lo hi h))⟩

end Stalk

/-! ### Relative perfectness along étale squares -/

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section EtaleLocal

variable {X' X Y' Y : AlgebraicSpaces B S hS} (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (b : Y' ⟶ Y)

/-- A lift of a geometric point of `X` into the image `a ∘ V` of an étale chart `V` of `X'`
comes from a lift into `V` of a geometric point of `X'` lying over it. -/
theorem exists_geometricPoint_of_smallEtalePostcomp (ha : IsEtale B S hS a.hom)
    (V : SmallEtale B S hS X'.1) (x : GeometricPoint B S hS X.1)
    (q : (etaleSitePoint B S hS X.1 x X.2).fiber.obj ((smallEtalePostcomp B S hS a ha).obj V)) :
    ∃ (x' : GeometricPoint B S hS X'.1) (_ : (etaleSitePoint B S hS X'.1 x' X'.2).fiber.obj V),
      geometricPointMap a.hom x' = x := by
  obtain ⟨⟨c, cont, tb, v⟩, hx⟩ := x
  obtain ⟨q, hq⟩ := q
  refine ⟨⟨⟨c, cont, tb, V.obj.hom.app _ q⟩, hx⟩, ⟨q, rfl⟩, Subtype.ext ?_⟩
  exact congrArg (fun t => (⟨c, cont, tb, t⟩ : FieldValuedPoint B S hS X.1)) hq

/-- An object has Tor amplitude on a slice as soon as its derived stalks over the stalk rings
have it at every geometric point lying in the slice object. -/
private theorem hasTorAmplitude_slice_of_forall_geometricPoint {A C : AlgebraicSpaces B S hS}
    (g : A ⟶ C) (E : DerivedCategory (Modules.{u, u} B S hS A.1 A.2))
    (V : (inverseImageRingedSite B S hS g).C) (lo hi : ℤ)
    (h : ∀ (x : GeometricPoint B S hS A.1) (_ : (etaleSitePoint B S hS A.1 x A.2).fiber.obj V),
      HasTorAmplitudeCanonical (relativeStalkRing g x)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS A.1 x A.2)
          (inverseImageRingedSite B S hS g).O).obj ((derivedScalarRestriction B S hS g).obj E))
        lo hi) :
    (canonicalSliceDerivedTensorProduct B S hS g V).HasTorAmplitude
      (((inverseImageRingedSite B S hS g).derivedRestriction V).obj
        ((derivedScalarRestriction B S hS g).obj E)) lo hi := by
  refine
    Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
    _ _ lo hi
    (fun ψ : Σ x : GeometricPoint B S hS A.1, (etaleSitePoint B S hS A.1 x A.2).fiber.obj V =>
      (etaleSitePoint B S hS A.1 ψ.1 A.2).over ψ.2)
    (isConservativeFamilyOfPoints_etaleSitePointOver B S hS A.2 V) fun ψ => ?_
  exact (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
    (inverseImageRingedSite B S hS g) (etaleSitePoint B S hS A.1 ψ.1 A.2) ψ.2 _ lo hi).2
    (h ψ.1 ψ.2)

variable (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
  (hfl' : IsFlat B S hS f'.hom) (hlfp' : IsLocallyOfFinitePresentation B S hS f'.hom)

/-- **Relative perfectness passes to an étale square.** For a commutative square
`a ≫ f = f' ≫ b` of algebraic spaces with `a` and `b` étale and `f`, `f'` flat and locally of
finite presentation, if `K ∈ D(𝒪_X)` is `Y`-perfect then `L(a)^*K` is `Y'`-perfect. -/
theorem isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (w : a ≫ f = f' ≫ b)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f' hfl' hlfp'
      ((smallEtaleDerivedModulePullback B S hS a).obj K) := by
  refine ⟨isPseudoCoherent_smallEtaleDerivedModulePullback a K hK.1, fun U' => ?_⟩
  let P : SmallEtale B S hS X.1 → Prop := fun W => ∃ lo hi : ℤ,
    ∀ (x : GeometricPoint B S hS X.1) (_ : (etaleSitePoint B S hS X.1 x X.2).fiber.obj W),
      HasTorAmplitudeCanonical (relativeStalkRing f x)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj K))
        lo hi
  let R : Presieve U' := fun V' _ => ∃ (W : SmallEtale B S hS X.1) (q : V'.1.left ⟶ W.1.left),
    yoneda.map q ≫ W.1.hom = V'.1.hom ≫ a.hom ∧ P W
  refine ⟨R, ?_, fun V' k ⟨W, q, hq, lo, hi, hW⟩ => ⟨lo, hi, ?_⟩⟩
  · exact generate_mem_topology_chartsOver_of_cover a P
      (fun W => (exists_cover_hasTorAmplitudeCanonical_relativeStalk f hfl hlfp K hK W).imp
        fun R hR => ⟨hR.1, fun V k hk => hR.2 k hk⟩)
      (fun m ⟨lo, hi, hab⟩ =>
        ⟨lo, hi, fun x p => hab x ((etaleSitePoint B S hS X.1 x X.2).fiber.map m p)⟩)
      U'
  · refine hasTorAmplitude_slice_of_forall_geometricPoint f' _ V' lo hi fun x' p => ?_
    refine (hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback_iff a f' f b
      ha hb w x' K lo hi).2 (hW _ ⟨p.1 ≫ q, ?_⟩)
    exact (congrArg (fun α => α.app (op x'.val.siteObject) p.1) hq).trans
      (congrArg (a.hom.app (op x'.val.siteObject)) p.2)

/-- **Relative perfectness descends along a jointly surjective family of étale squares.** For
commutative squares `aᵢ ≫ f = f'ᵢ ≫ bᵢ` of algebraic spaces with `aᵢ`, `bᵢ` étale, the images of
the `aᵢ` covering `|X|`, and `f`, `f'ᵢ` flat and locally of finite presentation, if every
`L(aᵢ)^*K` is `Y'ᵢ`-perfect then `K ∈ D(𝒪_X)` is `Y`-perfect. -/
theorem isPerfectRelativeToCanonical_of_forall_isEtale {ι : Type*}
    {Xi Yi : ι → AlgebraicSpaces B S hS} (ai : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i)
    (bi : ∀ i, Yi i ⟶ Y) (hfli : ∀ i, IsFlat B S hS (fi i).hom)
    (hlfpi : ∀ i, IsLocallyOfFinitePresentation B S hS (fi i).hom)
    (ha : ∀ i, IsEtale B S hS (ai i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Xi i).1,
      pointsMap B S hS _ (ai i).hom y = x)
    (hb : ∀ i, IsEtale B S hS (bi i).hom)
    (w : ∀ i, ai i ≫ f = fi i ≫ bi i) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ i, IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS (fi i) (hfli i) (hlfpi i)
      ((smallEtaleDerivedModulePullback B S hS (ai i)).obj K)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K := by
  refine ⟨(RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ K).2 fun m =>
    isPseudoCoherentFrom_of_forall_etale Xi ai ha hsurj K m
      (fun i => (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 (hK i).1 m),
    fun U => ?_⟩
  let P : SmallEtale B S hS X.1 → Prop := fun W => ∃ lo hi : ℤ,
    ∀ (x : GeometricPoint B S hS X.1) (_ : (etaleSitePoint B S hS X.1 x X.2).fiber.obj W),
      HasTorAmplitudeCanonical (relativeStalkRing f x)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj K))
        lo hi
  let U₀ : SmallEtale B S hS X.1 := U
  refine ⟨fun V _ => P V, ?_, fun V k ⟨lo, hi, hV⟩ => ⟨lo, hi, ?_⟩⟩
  · change Sieve.generate (fun (V : SmallEtale B S hS X.1) (_ : V ⟶ U₀) => P V) ∈
      SmallEtale.topology B S hS X.1 U₀
    rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro z
    obtain ⟨u, rfl⟩ := surjective_pointsToScheme B S hS U₀.1.left z
    obtain ⟨i, y, hy⟩ := hsurj (pointsMap B S hS _ U₀.1.hom u)
    obtain ⟨V, p, hp, w', hw⟩ := exists_chart_lift_of_isEtale B S hS (ai i) (ha i) U₀ u y hy.symm
    obtain ⟨R₀, hR₀, hR₀P⟩ :=
      exists_cover_hasTorAmplitudeCanonical_relativeStalk (fi i) (hfli i) (hlfpi i) _ (hK i) V
    obtain ⟨W', m₁, ⟨W'', m', m'', hm'', rfl⟩, w'', hw''⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS (Xi i).1 _).1 hR₀ w'
    let Wx : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS (ai i) (ha i)).obj W''
    have hm''w : yoneda.map ((SmallEtale.toOver B S hS (Xi i).1).map m'') ≫ V.1.hom = W''.1.hom :=
      CostructuredArrow.w m''.hom
    let gx : Wx ⟶ U₀ := ObjectProperty.homMk (CostructuredArrow.homMk
      ((SmallEtale.toOver B S hS (Xi i).1).map m'' ≫ p) (by
        change yoneda.map (_ ≫ p) ≫ U₀.1.hom = W''.1.hom ≫ (ai i).hom
        rw [Functor.map_comp, Category.assoc, hp, ← Category.assoc, hm''w]))
    refine ⟨Wx, gx, Sieve.le_generate _ _ _ ?_, ?_⟩
    · obtain ⟨lo, hi, hab⟩ := hR₀P m'' hm''
      refine ⟨lo, hi, fun x q => ?_⟩
      obtain ⟨x', q', rfl⟩ := exists_geometricPoint_of_smallEtalePostcomp (ai i) (ha i) W'' x q
      exact (hasTorAmplitudeCanonical_relativeStalk_smallEtaleDerivedModulePullback_iff (ai i)
        (fi i) f (bi i) (ha i) (hb i) (w i) x' K lo hi).1 (hab x' q')
    · refine ⟨(BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (Xi i).1).map m') w'',
        ?_⟩
      change (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (Xi i).1).map m'' ≫ p) _ = _
      rw [← hw, ← hw'']
      simp only [Functor.map_comp, Scheme.Hom.comp_apply]
      refine congrArg ((BigFppfOver.toScheme B S hS).map p) ?_
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
      rfl
  · exact hasTorAmplitude_slice_of_forall_geometricPoint f _ V lo hi hV

/-- **Relative perfectness descends along a surjective étale square.** For a commutative square
`a ≫ f = f' ≫ b` of algebraic spaces with `a` étale and surjective, `b` étale and `f`, `f'` flat
and locally of finite presentation, if `L(a)^*K` is `Y'`-perfect then `K ∈ D(𝒪_X)` is
`Y`-perfect. -/
theorem isPerfectRelativeToCanonical_of_isEtale_of_isSurjective
    (ha : IsEtale B S hS a.hom) (hsurj : IsSurjective B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (w : a ≫ f = f' ≫ b) (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f' hfl' hlfp'
      ((smallEtaleDerivedModulePullback B S hS a).obj K)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K :=
  isPerfectRelativeToCanonical_of_forall_isEtale f hfl hlfp (Xi := fun _ : Unit => X')
    (Yi := fun _ => Y') (fun _ => a) (fun _ => f') (fun _ => b) (fun _ => hfl') (fun _ => hlfp')
    (fun _ => ha) (fun x => ⟨(), hsurj x⟩) (fun _ => hb) (fun _ => w) K (fun _ => hK)

end EtaleLocal

end AlgebraicGeometry.Space

end
