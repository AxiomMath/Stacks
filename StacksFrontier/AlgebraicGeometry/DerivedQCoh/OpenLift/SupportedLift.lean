module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PartialIdentityCone
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PowerTorsionAffineOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.DerivedTensorDatumBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PowerTorsionRestrict
public import StacksFrontier.CategoryTheory.Triangulated.ConeOfScalar
public import StacksFrontier.CategoryTheory.Triangulated.ConeOfZero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.Perfect.RestrictionOfPerfectObjects
import all StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules

/-!
# Support, scalars and towers of cones

Cohomological support in the derived category of modules on a ringed space is stable under
isomorphisms, shifts, cones and derived tensor products, and an object killed by a power of a
global function `r` is supported off `X_r`. Iterated cones of multiplications by scalars kill
an object by powers of those scalars.

## Main results

* `Stacks.SheafOfModules.cohomologySupportedOn_derivedTensor_left`: the derived tensor product of
  a complex supported on `T` with any complex is supported on `T`.
* `Stacks.DerivedQCoh.cohomologySupportedOn_compl_basicOpen_of_pow_smul_id`: an object killed by
  a power of a global function `r` is supported on the complement of `X_r`.
* `CategoryTheory.Pretriangulated.exists_coneTower_restrict_iso_biprod`: the tower of cones of
  multiplications by scalars which a triangulated functor carries to scalars killing the image.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Cohomological support only depends on the isomorphism class. -/
theorem CohomologySupportedOn.of_iso {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {T : Set X}
    {E E' : DerivedCategory (SheafOfModules.{u} O)} (h : CohomologySupportedOn O T E)
    (e : E ≅ E') : CohomologySupportedOn O T E' := by
  rw [cohomologySupportedOn_iff_forall_isZero_derivedStalk] at h ⊢
  exact fun y hy => (h y hy).of_iso
    ((SheafOfModules.stalkFunctor O y).mapDerivedCategory.mapIso e.symm)

/-- Cohomological support is preserved by the shift. -/
theorem CohomologySupportedOn.shift {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {T : Set X}
    {E : DerivedCategory (SheafOfModules.{u} O)} (h : CohomologySupportedOn O T E) (n : ℤ) :
    CohomologySupportedOn O T (E⟦n⟧) := fun i x hx => by
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O x]
  refine IsZero.of_iso ?_ ((SheafOfModules.stalkFunctor O x).mapIso
    (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) 0).shiftIso n i (n + i) rfl).app E))
  exact (SheafOfModules.isZero_stalkFunctor_obj_iff O x _).2 (h (n + i) x hx)

/-- Cohomological support is a two-out-of-three property, for the third vertex. -/
theorem cohomologySupportedOn_obj₃_of_distinguished {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X)
    (S : Triangle (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (hS : S ∈ distTriang (DerivedCategory (_root_.SheafOfModules.{u} O)))
    (h₁ : CohomologySupportedOn O T S.obj₁) (h₂ : CohomologySupportedOn O T S.obj₂) :
    CohomologySupportedOn O T S.obj₃ :=
  cohomologySupportedOn_obj₂_of_distinguished O T S.rotate (rot_of_distTriang S hS) h₂
    (h₁.shift 1)

end AlgebraicGeometry

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The derived tensor product of a complex supported on `T` with an arbitrary complex is
supported on `T`. -/
theorem cohomologySupportedOn_derivedTensor_left (T : Set X)
    (A K : DerivedCategory (StructureSheafModules Rc))
    (hA : CohomologySupportedOn (Tensor.ringSheaf.{u, u, u} Rc) T A) :
    CohomologySupportedOn (Tensor.ringSheaf.{u, u, u} Rc) T (((derivedTensor Rc).obj A).obj K) := by
  let T₁ := Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDatum (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc))
  let T₂ := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Rc
  let e : ((derivedTensor Rc).obj A).obj K ≅ ((T₂.tensor).obj A).obj K :=
    Stacks.DerivedTensor.RingedSite.derivedTensorProductIso Rc T₁
      (DerivedTensorStalk.kFlat_kFlatModel Rc A) (DerivedTensorStalk.kFlat_kFlatModel Rc K)
      (DerivedTensorStalk.kFlatModelIso Rc A) (DerivedTensorStalk.kFlatModelIso Rc K) ≪≫
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductIso Rc T₂
      (DerivedTensorStalk.kFlat_kFlatModel Rc A) (DerivedTensorStalk.kFlat_kFlatModel Rc K)
      (DerivedTensorStalk.kFlatModelIso Rc A) (DerivedTensorStalk.kFlatModelIso Rc K)).symm
  exact (DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left Rc T A K hA).of_iso e.symm

end Stacks.SheafOfModules

namespace CategoryTheory.Pretriangulated

section Linear

variable {Λ : Type*} [CommRing Λ] {C : Type*} [Category C] [Preadditive C] [Linear Λ C]

/-- A scalar killing two objects kills their biproduct. -/
theorem smul_id_biprod_eq_zero [HasBinaryBiproducts C] (a : Λ) {A B : C} (hA : a • 𝟙 A = 0)
    (hB : a • 𝟙 B = 0) : a • 𝟙 (A ⊞ B) = 0 := by
  apply biprod.hom_ext
  · simpa using congrArg (biprod.fst ≫ ·) hA
  · simpa using congrArg (biprod.snd ≫ ·) hB

/-- A scalar killing an object kills every isomorphic object. -/
theorem smul_id_eq_zero_of_iso (a : Λ) {A B : C} (e : A ≅ B) (hA : a • 𝟙 A = 0) :
    a • 𝟙 B = 0 := by
  rw [← Stacks.Koszul.PowerLift.smul_id_conj e a, hA, zero_comp, comp_zero]

end Linear

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ']
  {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear Λ C]
  [∀ n : ℤ, Functor.Linear Λ (shiftFunctor C n)]
  {D : Type*} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasBinaryBiproducts D]
  [Linear Λ' D] [∀ n : ℤ, Functor.Linear Λ' (shiftFunctor D n)]

/-- Let `R : C ⥤ D` be a triangulated functor and let `s₀, …, s_{r-1}` be scalars on `C` which
`R` carries to scalars `s'ᵢ` on `D`. Let `E₀` be an object satisfying a property `Q` closed under
cones, with `R E₀ ≅ G₀ ⊞ F` and every `s'ᵢ` killing `R E₀`. Then there is an object `C` with
`Q C`, killed by a power of every `sᵢ`, and with `R C ≅ G ⊞ F` for some `G`: the top of the tower
`C₀ = E₀, C_{k+1} = Cone(s_k • 𝟙 C_k)`. -/
theorem exists_coneTower_restrict_iso_biprod (R : C ⥤ D) [R.CommShift ℤ] [R.IsTriangulated]
    {r : ℕ} (s : Fin r → Λ) (s' : Fin r → Λ')
    (hR : ∀ (i : Fin r) {K L : C} (f : K ⟶ L), R.map (s i • f) = s' i • R.map f)
    (Q : C → Prop) (hQ : ∀ T ∈ distTriang C, Q T.obj₁ → Q T.obj₂ → Q T.obj₃)
    (E₀ : C) (hE₀ : Q E₀) (F G₀ : D) (b₀ : G₀ ⊞ F ≅ R.obj E₀)
    (hs : ∀ i, s' i • 𝟙 (R.obj E₀) = 0) :
    ∃ (E : C) (G : D) (_ : G ⊞ F ≅ R.obj E), Q E ∧ ∀ i, ∃ k : ℕ, s i ^ k • 𝟙 E = 0 := by
  suffices H : ∀ m : ℕ, m ≤ r → ∃ (E : C) (G : D) (_ : G ⊞ F ≅ R.obj E), Q E ∧
      (∀ i, s' i • 𝟙 (R.obj E) = 0) ∧ ∀ i : Fin r, i.val < m → ∃ k : ℕ, s i ^ k • 𝟙 E = 0 by
    obtain ⟨E, G, b, hE, -, hk⟩ := H r le_rfl
    exact ⟨E, G, b, hE, fun i => hk i i.2⟩
  intro m
  induction m with
  | zero => exact fun _ => ⟨E₀, G₀, b₀, hE₀, hs, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨E, G, b, hE, hRE, hk⟩ := ih (by lia)
    let j : Fin r := ⟨m, by lia⟩
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (s j • 𝟙 E)
    have hT' := R.map_distinguished _ hT
    have h0 : (R.mapTriangle.obj (Triangle.mk (s j • 𝟙 E) g h)).mor₁ = 0 := by
      show R.map (s j • 𝟙 E) = 0
      rw [hR, Functor.map_id, hRE]
    obtain ⟨e⟩ := nonempty_iso_biprod_shift_of_mor₁_eq_zero _ hT' h0
    have hRZ : ∀ i, s' i • 𝟙 (R.obj Z) = 0 := fun i =>
      smul_id_eq_zero_of_iso (s' i) e (smul_id_biprod_eq_zero (s' i) (hRE i) (by
        rw [← Functor.map_id, ← Functor.map_smul]
        exact (congrArg (shiftFunctor D (1 : ℤ)).map (hRE i)).trans (Functor.map_zero _ _ _)))
    refine ⟨Z, G ⊞ (R.obj E)⟦(1 : ℤ)⟧,
      (biprod.associator G ((R.obj E)⟦(1 : ℤ)⟧) F ≪≫
        biprod.mapIso (Iso.refl G) (biprod.braiding _ _) ≪≫
        (biprod.associator G F ((R.obj E)⟦(1 : ℤ)⟧)).symm ≪≫
        biprod.mapIso b (Iso.refl _) ≪≫ e),
      hQ _ hT hE hE, hRZ, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i.val m with him | him
    · obtain ⟨k, hk'⟩ := hk i him
      exact exists_pow_smul_id_eq_zero_of_distTriang (s i) _ hT ⟨k, hk'⟩ ⟨k, hk'⟩
    · obtain rfl : i = j := Fin.ext (by simp only [j]; lia)
      exact ⟨2, sq_smul_id_eq_zero_of_cone_smul_id (s _) g h hT⟩

end CategoryTheory.Pretriangulated

namespace Stacks.DerivedQCoh

open Stacks.Cohomology.SiteModules Stacks.ExtensionByZero
open Stacks.Duality.OpenImmersion (derivedRestrict)

attribute [local instance 10000] HasDerivedCategory.standard

/-- If `r ^ k • 𝟙 E = 0` for a global section `r` of `𝒪_X`, then the cohomology of `E` is
supported on the complement of `X_r`. -/
theorem cohomologySupportedOn_compl_basicOpen_of_pow_smul_id {X : Scheme.{u}} (r : Γ(X, ⊤))
    (E : DerivedCategory X.Modules) (k : ℕ)
    (h : globalScalar X.ringCatSheaf r ^ k • 𝟙 E = 0) :
    CohomologySupportedOn X.ringCatSheaf ((X.basicOpen r : Set X)ᶜ) E := by
  let V := X.basicOpen r
  have h0 : globalScalar X.ringCatSheaf (r ^ k) • 𝟙 E = 0 :=
    (congrArg (fun s => s • 𝟙 E) (globalScalar_pow X.ringCatSheaf r k)).trans h
  have h1 : globalScalar V.toScheme.ringCatSheaf (V.ι.appTop (r ^ k)) •
      𝟙 ((derivedRestrict V.ι).obj E) = 0 :=
    (derivedRestrict_map_globalScalar_smul_id V.ι (r ^ k) E).symm.trans
      ((congrArg (derivedRestrict V.ι).map h0).trans (Functor.map_zero _ _ _))
  have key : IsUnit (X.presheaf.map (homOfLE (le_top : V.ι ''ᵁ ⊤ ≤ ⊤)).op r) := by
    have hunit : IsUnit ((X.presheaf.map
        (homOfLE (show X.basicOpen r ≤ ⊤ from le_top)).op) r) :=
      X.toRingedSpace.isUnit_res_basicOpen r
    have hmap := hunit.map (X.presheaf.map
      (homOfLE (le_of_eq V.ι_image_top : V.ι ''ᵁ ⊤ ≤ X.basicOpen r)).op).hom
    convert hmap using 1
    simp [← X.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]
  have hres : IsUnit (V.ι.appTop r) := by rwa [Scheme.Opens.ι_appTop]
  have hu : IsUnit (globalScalar V.toScheme.ringCatSheaf (V.ι.appTop (r ^ k))) := by
    have e : globalScalar V.toScheme.ringCatSheaf (V.ι.appTop (r ^ k)) =
        globalScalarHom V.toScheme.ringCatSheaf (V.ι.appTop r) ^ k :=
      (congrArg (globalScalarHom V.toScheme.ringCatSheaf)
        (map_pow (ConcreteCategory.hom V.ι.appTop) r k)).trans (map_pow _ _ k)
    rw [e]
    exact (hres.map (globalScalarHom V.toScheme.ringCatSheaf)).pow k
  obtain ⟨u, hu⟩ := hu
  have hid : 𝟙 ((derivedRestrict V.ι).obj E) = 0 := by
    calc 𝟙 ((derivedRestrict V.ι).obj E)
        = (↑u⁻¹ * ↑u : GlobalSectionRing V.toScheme.ringCatSheaf) • 𝟙 _ := by
          rw [Units.inv_mul, one_smul]
      _ = 0 := by rw [mul_smul, hu, h1, smul_zero]
  exact cohomologySupportedOn_compl_of_isZero_derivedRestrict V E
    ((IsZero.iff_id_eq_zero _).2 hid)

end Stacks.DerivedQCoh

namespace Stacks.DerivedQCoh.OpenLift

open Stacks.Cohomology.SiteModules Stacks.ExtensionByZero Stacks.Cohomology.PerfectComplexes
open _root_.Stacks.StrictlyPerfect Koszul.DerivedSystem Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

/-- The third vertex of a distinguished triangle of `D(𝒪_Y)` is perfect when the first two are,
for the derived category written over `Y.Modules`. -/
theorem isPerfect_obj₃_of_distinguished_modules (Y : Scheme.{u})
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang (DerivedCategory Y.Modules))
    (h₁ : IsPerfect (X := Y.toRingedSpace) T.obj₁) (h₂ : IsPerfect (X := Y.toRingedSpace) T.obj₂) :
    IsPerfect (X := Y.toRingedSpace) T.obj₃ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (X := Y.toRingedSpace) T hT h₁ h₂

end Stacks.DerivedQCoh.OpenLift

end
