module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus

/-!
# Openness of the flat locus

For a morphism of schemes locally of finite presentation and a finitely presented
quasi-coherent module on its source, the locus where the module is flat over the target is
open.

## Main results

* `AlgebraicGeometry.isOpen_setOf_flatOverAt` proves openness of the relative flat locus.
* `AlgebraicGeometry.flatOverAt_iff_of_iso`, its global form
  `AlgebraicGeometry.isFlatOver_iff_of_iso`, and
  `AlgebraicGeometry.flatOverAt_iff_flat_sectionsStalk`
  are the comparisons relative flatness at a point is reduced through, and
  `AlgebraicGeometry.germ_spec_comp_stalkMap` identifies the ring map that the second one is
  flatness over. They are stated publicly because the finite type version of this theorem
  (Stacks 05IK) reduces to the affine case through exactly the same chain.
* `AlgebraicGeometry.moduleStalkLinearEquiv` turns an isomorphism of sheaves of modules into a
  linear equivalence of stalks, over the stalk of the structure sheaf. It is what
  `AlgebraicGeometry.flatOverAt_iff_of_iso` is proved from, and it is public because the same
  equivalence transports finite presentation of a stalk, which is how the dévissage transfer
  lemmas of Stacks 057T compare the three stalks of an elementary dévissage.

## Implementation notes

Flatness over the target at a point is expressed by `AlgebraicGeometry.IsFlatOverAt`, the
stalkwise definition. The proof is local: over an affine open `U` of the target and an affine
open `V` of the source mapping into it, the stalk of the module is a localization of a finitely
presented module over `Γ(X, V)`, and the ring-theoretic openness statement
`Module.isOpen_setOf_flat_localizedModule_atPrime` applies. Transporting that back needs the
compatibility of relative flatness with an isomorphism of modules and with restriction along an
open immersion; the former is proved here and the latter is
`AlgebraicGeometry.isFlatOverAt_restrict_iff`.

## References

* [EGA IV, Theorem 11.3.1]
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
-/

@[expose] public section

open CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The map of stalks induced by a morphism of sheaves of modules. -/
def moduleStalkMap
    {X : Scheme.{u}} {F G : X.Modules} (α : F ⟶ G) (x : X) :
    F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab x).map α.mapPresheaf

/-- The induced map of stalks is semilinear over the stalk of the structure sheaf. -/
theorem moduleStalkMap_smul
    {X : Scheme.{u}} (F G : X.Modules) (α : F ⟶ G) (x : X)
    (a : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    moduleStalkMap α x (a • m) = a • moduleStalkMap α x m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq m
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op r
  let sW : Γ(F, W) := F.presheaf.map (homOfLE inf_le_right).op s
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxW r,
    ← F.presheaf.germ_res_apply (homOfLE inf_le_right) x hxW s]
  have hF : X.presheaf.germ W x hxW rW • F.presheaf.germ W x hxW sW =
      F.presheaf.germ W x hxW (rW • sW) :=
    (PresheafOfModules.germ_smul F.val x W hxW rW sW).symm
  have hnat (t : Γ(F, W)) :
      moduleStalkMap α x (F.presheaf.germ W x hxW t) =
        G.presheaf.germ W x hxW (α.app W t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW α.mapPresheaf t
  rw [hF, hnat, α.app_smul]
  have hG : G.presheaf.germ W x hxW (rW • α.app W sW) =
      X.presheaf.germ W x hxW rW • G.presheaf.germ W x hxW (α.app W sW) :=
    PresheafOfModules.germ_smul G.val x W hxW rW (α.app W sW)
  rw [hG, hnat]

/-- The induced map of stalks as a linear map. -/
def moduleStalkLinearMap
    {X : Scheme.{u}} {F G : X.Modules} (α : F ⟶ G) (x : X) :
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x where
  toFun := moduleStalkMap α x
  map_add' := (moduleStalkMap α x).hom.map_add
  map_smul' := moduleStalkMap_smul F G α x

/-- An isomorphism of sheaves of modules induces a linear equivalence on stalks. -/
def moduleStalkLinearEquiv
    {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x := by
  have : IsIso e.hom.mapPresheaf := by
    change IsIso ((Scheme.Modules.toPresheaf X).map e.hom)
    infer_instance
  have : IsIso (moduleStalkMap e.hom x) := by
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map e.hom.mapPresheaf)
    infer_instance
  exact LinearEquiv.ofBijective (moduleStalkLinearMap e.hom x)
    (ConcreteCategory.bijective_of_isIso (moduleStalkMap e.hom x))

/-- Flatness over `R` of a module over `A`, with scalars restricted along `g : R →+* A`, is
invariant under a linear equivalence over `A`. -/
private theorem flat_compHom_iff_of_linearEquiv
    {R A M N : Type*} [CommRing R] [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] (g : R →+* A) (e : M ≃ₗ[A] N) :
    (letI := Module.compHom M g; Module.Flat R M) ↔
      (letI := Module.compHom N g; Module.Flat R N) := by
  let _ := g.toAlgebra
  let _ := Module.compHom M g
  let _ := Module.compHom N g
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.equiv_iff (e.restrictScalars R)

/-- Relative flatness at a point is invariant under an isomorphism of modules. -/
theorem flatOverAt_iff_of_iso
    {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules}
    (e : F ≅ G) (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      IsFlatOverAt f.toLRSHom.toShHom G x := by
  exact flat_compHom_iff_of_linearEquiv (M := F.presheaf.stalk x) (N := G.presheaf.stalk x)
    (f.stalkMap x).hom (moduleStalkLinearEquiv e x)

/-- Relative flatness is invariant under an isomorphism of modules. -/
theorem isFlatOver_iff_of_iso {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules} (e : F ≅ G) :
    IsFlatOver f.toLRSHom.toShHom F ↔ IsFlatOver f.toLRSHom.toShHom G :=
  forall_congr' (flatOverAt_iff_of_iso f e)

/-- Relative flatness at a point is flatness of the stalk over the sections of an affine open
neighbourhood of the image point. -/
theorem flatOverAt_iff_flat_sectionsStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {U : S.Opens} (hU : IsAffineOpen U) (x : X) (hx : f x ∈ U) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      let M : PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        inferInstanceAs (Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))
      letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
        Module.compHom _ (f.stalkMap x).hom
      letI : Module Γ(S, U) (F.presheaf.stalk x) :=
        Module.compHom _ (S.presheaf.germ U (f x) hx).hom
      Module.Flat Γ(S, U) (F.presheaf.stalk x) := by
  let _ : Algebra Γ(S, U) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let _ : IsLocalization (hU.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl
      (S.presheaf.stalk (f x)) := hU.isLocalization_stalk ⟨f x, hx⟩
  let M : PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let _ : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    inferInstanceAs (Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))
  let _ : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let _ : Module Γ(S, U) (F.presheaf.stalk x) :=
    Module.compHom _ (S.presheaf.germ U (f x) hx).hom
  let _ : IsScalarTower Γ(S, U) (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.flat_iff_of_isLocalization (S.presheaf.stalk (f x))
    (hU.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl (F.presheaf.stalk x)

/-- Finite presentation of a sheaf of modules is preserved by restriction along an open
immersion. -/
public theorem finitePresentation_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : Y.Modules) [F.IsFinitePresentation] :
    (F.restrict f).IsFinitePresentation := by
  have hF : F.IsFinitePresentation := inferInstance
  have hp := @Stacks.SheafOfModules.modulePullback_isFinitePresentation
    _ _ f.toLRSHom.toShHom F hF
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm hp

/-- For a finitely presented ring map and a finitely presented module, the locus where the
stalk of the associated sheaf is flat over the base is open. -/
@[sga "1 IV 6.10" "special case", sga "3 VIB 13.1" "(i), special case"]
private theorem isOpen_flat_tilde_stalk
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : ModuleCat.{u} B)
    (hφ : RingHom.FinitePresentation φ.hom) [Module.FinitePresentation B M] :
    IsOpen {q : PrimeSpectrum B |
      letI : Module A ((tilde M).presheaf.stalk q) :=
        Module.compHom _ φ.hom
      Module.Flat A ((tilde M).presheaf.stalk q)} := by
  algebraize [φ.hom]
  let _ : Module A M := Module.compHom M φ.hom
  let _ : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Algebra.FinitePresentation A B :=
    RingHom.finitePresentation_algebraMap.mp hφ
  have hO : IsOpen {q : PrimeSpectrum B |
      Module.Flat A (LocalizedModule.AtPrime q.asIdeal M)} :=
    Module.isOpen_setOf_flat_localizedModule_atPrime
  convert hO using 1
  ext q
  let _ : q.asIdeal.IsPrime := q.isPrime
  let _ : Module B ((tilde M).presheaf.stalk q) := inferInstance
  let _ : Module A ((tilde M).presheaf.stalk q) := Module.compHom _ φ.hom
  let _ : IsScalarTower A B ((tilde M).presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : LocalizedModule.AtPrime q.asIdeal M ≃ₗ[B] ((tilde M).presheaf.stalk q) :=
    IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ M) (tilde.toStalk M q).hom
  exact (Module.Flat.equiv_iff (e.restrictScalars A)).symm

/-- The germ at a point of an affine open followed by the stalk map of its canonical morphism
from the spectrum of its sections. -/
theorem germ_fromSpec_stalkMap
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(S, U)) (hp : hU.fromSpec p ∈ U) :
    S.presheaf.germ U (hU.fromSpec p) hp ≫ hU.fromSpec.stalkMap p =
      (Scheme.ΓSpecIso Γ(S, U)).inv ≫
        (Spec Γ(S, U)).presheaf.germ ⊤ p (by simp) := by
  rw [Scheme.Hom.germ_stalkMap, hU.fromSpec_app_self, Category.assoc]
  exact congrArg (fun t => (Scheme.ΓSpecIso Γ(S, U)).inv ≫ t)
    ((Spec Γ(S, U)).presheaf.germ_res
      (eqToHom hU.fromSpec_preimage_self) p hp)

/-- The same computation for a morphism factored through the spectrum of an algebra over the
sections. -/
theorem germ_spec_comp_stalkMap
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    {B : CommRingCat.{u}} (φ : Γ(S, U) ⟶ B) (q : Spec B)
    (hq : (Spec.map φ ≫ hU.fromSpec) q ∈ U) :
    S.presheaf.germ U ((Spec.map φ ≫ hU.fromSpec) q) hq ≫
      (Spec.map φ ≫ hU.fromSpec).stalkMap q =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.germ ⊤ q (by simp) := by
  calc
    _ = (S.presheaf.germ U (hU.fromSpec (Spec.map φ q)) hq ≫
          hU.fromSpec.stalkMap (Spec.map φ q)) ≫
          (Spec.map φ).stalkMap q := by
            rw [Scheme.Hom.stalkMap_comp]
            rfl
    _ = ((Scheme.ΓSpecIso Γ(S, U)).inv ≫
          (Spec Γ(S, U)).presheaf.germ ⊤ (Spec.map φ q) (by simp)) ≫
          (Spec.map φ).stalkMap q := by
            rw [germ_fromSpec_stalkMap hU (Spec.map φ q) hq]
    _ = _ := by
      rw [Category.assoc, Scheme.Hom.germ_stalkMap]
      change (Scheme.ΓSpecIso Γ(S, U)).inv ≫
        (Spec.map φ).appTop ≫
          (Spec B).presheaf.germ ⊤ q (by simp) =
        φ ≫ (Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.germ ⊤ q (by simp)
      rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality φ, Category.assoc]

/-- Openness of the relative flat locus for a morphism from the spectrum of a finitely
presented algebra over the sections of an affine open. -/
private theorem isOpen_flatOverAt_spec
    {B : CommRingCat.{u}} {S : Scheme.{u}} {U : S.Opens}
    (hU : IsAffineOpen U) (φ : Γ(S, U) ⟶ B)
    (hφ : RingHom.FinitePresentation φ.hom)
    (F : (Spec B).Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    IsOpen {q : Spec B |
      IsFlatOverAt (Spec.map φ ≫ hU.fromSpec).toLRSHom.toShHom F q} := by
  let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
  have : Module.FinitePresentation B M := finitePresentation_sections_of_affine F
  change IsOpen {q : PrimeSpectrum B |
    IsFlatOverAt (Spec.map φ ≫ hU.fromSpec).toLRSHom.toShHom F q}
  have heq : {q : PrimeSpectrum B |
      IsFlatOverAt (Spec.map φ ≫ hU.fromSpec).toLRSHom.toShHom F q} =
      {q : PrimeSpectrum B |
        let : Module Γ(S, U) ((tilde M).presheaf.stalk q) :=
          Module.compHom _ φ.hom
        Module.Flat Γ(S, U) ((tilde M).presheaf.stalk q)} := by
    ext q
    let _ : Module Γ(S, U) ((tilde M).presheaf.stalk q) :=
      Module.compHom _ φ.hom
    change IsFlatOverAt (Spec.map φ ≫ hU.fromSpec).toLRSHom.toShHom F q ↔
      Module.Flat Γ(S, U) ((tilde M).presheaf.stalk q)
    rw [flatOverAt_iff_of_iso (Spec.map φ ≫ hU.fromSpec) (asIso F.fromTildeΓ).symm q]
    have hx : (Spec.map φ ≫ hU.fromSpec) q ∈ U := by
      change (Spec.map φ q) ∈ hU.fromSpec ⁻¹ᵁ U
      rw [hU.fromSpec_preimage_self]
      trivial
    rw [flatOverAt_iff_flat_sectionsStalk
      (Spec.map φ ≫ hU.fromSpec) (tilde M) hU q hx]
    let N := ((tilde M).presheaf.stalk q)
    let _ : Module ((Spec B).presheaf.stalk q) N :=
      AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) q
    let _ : Algebra B ((Spec B).presheaf.stalk q) :=
      StructureSheaf.stalkAlgebra B q
    have hB (b : B) (m : N) :
        (algebraMap B ((Spec B).presheaf.stalk q) b) • m = b • m := rfl
    have hr :
        S.presheaf.germ U ((Spec.map φ ≫ hU.fromSpec) q) hx ≫
          (Spec.map φ ≫ hU.fromSpec).stalkMap q =
        φ ≫ CommRingCat.ofHom (algebraMap B ((Spec B).presheaf.stalk q)) :=
      (germ_spec_comp_stalkMap hU φ q hx).trans (by ext; rfl)
    let moduleS : Module (S.presheaf.stalk ((Spec.map φ ≫ hU.fromSpec) q)) N :=
      Module.compHom N ((Spec.map φ ≫ hU.fromSpec).stalkMap q).hom
    let moduleLeft : Module Γ(S, U) N :=
      let : Module (S.presheaf.stalk ((Spec.map φ ≫ hU.fromSpec) q)) N := moduleS
      Module.compHom N (S.presheaf.germ U _ hx).hom
    let moduleRight : Module Γ(S, U) N := Module.compHom N φ.hom
    have hmodule : moduleLeft = moduleRight := by
      apply Module.ext'
      intro a m
      change ((Spec.map φ ≫ hU.fromSpec).stalkMap q).hom
        ((S.presheaf.germ U _ hx).hom a) • m = (φ.hom a) • m
      have hval := congrArg
        (fun t : Γ(S, U) ⟶ (Spec B).presheaf.stalk q => t a) hr
      change ((Spec.map φ ≫ hU.fromSpec).stalkMap q).hom
        ((S.presheaf.germ U _ hx).hom a) =
          algebraMap B ((Spec B).presheaf.stalk q) (φ.hom a) at hval
      rw [hval, hB]
    change @Module.Flat Γ(S, U) N _ _ moduleLeft ↔
      @Module.Flat Γ(S, U) N _ _ moduleRight
    rw [hmodule]
  exact heq ▸ isOpen_flat_tilde_stalk φ M hφ

/-- **Stacks Project, Tag 0399.** The locus where a finitely presented quasi-coherent module is
flat over the target of a locally finitely presented morphism is open. -/
@[stacks 0399, ega "IV 11.3.1" "U open", ega "IV 15.4.1" "partial"]
public theorem isOpen_setOf_flatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    IsOpen {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU
      (U.2.preimage f.continuous)
  let j : Spec Γ(X, V) ⟶ X := hV.fromSpec
  have : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  let φ : Γ(S, U) ⟶ Γ(X, V) := f.appLE U V hVU
  let G : (Spec Γ(X, V)).Modules := F.restrict j
  have : G.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor j F
  have : G.IsFinitePresentation := finitePresentation_restrict j F
  have hjf : Spec.map φ ≫ hU.fromSpec = j ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU
  have hO : IsOpen {q : Spec Γ(X, V) |
      IsFlatOverAt (j ≫ f).toLRSHom.toShHom G q} := by
    rw [← hjf]
    exact isOpen_flatOverAt_spec hU φ
      (f.finitePresentation_appLE hU hV hVU) G
  have heq : {q : Spec Γ(X, V) |
      IsFlatOverAt (j ≫ f).toLRSHom.toShHom G q} =
      j ⁻¹' {y : X | IsFlatOverAt f.toLRSHom.toShHom F y} :=
    Set.ext fun q => isFlatOverAt_restrict_iff j f F q
  refine ⟨j '' (j ⁻¹'
    {y : X | IsFlatOverAt f.toLRSHom.toShHom F y}), ?_, ?_, ?_⟩
  · exact Set.image_preimage_subset _ _
  · exact j.isOpenEmbedding.isOpenMap _ (heq ▸ hO)
  · obtain ⟨q, hq⟩ : x ∈ Set.range j := by simpa only [j, hV.range_fromSpec] using hxV
    exact ⟨q, by simpa only [Set.mem_preimage, hq] using hx, hq⟩

end

end AlgebraicGeometry
