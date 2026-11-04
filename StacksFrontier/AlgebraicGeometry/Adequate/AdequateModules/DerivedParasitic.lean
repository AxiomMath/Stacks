module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedQuotient
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Parasitic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre

/-!
# The triangulated structure of `D_Adeq(𝒪)` and its parasitic part

Let `S` be a scheme and let `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of [Stacks, Tag 070U]. The adequate `𝒪`-modules form a weak Serre subcategory of all
`𝒪`-modules ([Stacks, Tag 06VQ]), and the quasi-coherent `𝒪_S`-modules a weak Serre subcategory
of all `𝒪_S`-modules, so the complexes `D_Adeq(𝒪)` and `D_QCoh(S)` with cohomology in them are
strictly full triangulated subcategories of `D(𝒪)` and `D(𝒪_S)` ([Stacks, Tag 06UQ]), and they
are pretriangulated (indeed triangulated) categories in their own right. A triangulated functor
between the ambient derived categories which preserves the two subcategories restricts to a
triangulated functor between them; in particular so do the restrictions of `Lf^*` and `Rf_*`
used in [Stacks, Tags 070W and 070X].

[Stacks, Tag 070X] quotients `D_Adeq(𝒪)` by `D_𝒞(𝒪)`, the complexes whose cohomology modules
are parasitic adequate modules, and observes that `D_𝒞(𝒪)` is the kernel of `Rf_*`; for an
adequate module `𝓕` the vanishing of `f_*𝓕 = 𝓕|_{S_Zar}` is the parasitic condition by
[Stacks, Tag 06ZM]. The quotient itself is then formal: a triangulated functor with a fully
faithful left adjoint is the Verdier quotient by its kernel.

## Main definitions

* `Stacks.Adequate.BigSite.parasiticModule` — the parasitic adequate `𝒪`-modules, as a property
  of all `𝒪`-modules.
* `Stacks.Adequate.BigSite.derivedParasitic` — `D_𝒞(𝒪)`, the complexes of `𝒪`-modules whose
  cohomology modules are parasitic adequate.

## Main results

* `DerivedCategoryB.isTriangulated_liftRight`, `DerivedCategoryB.isTriangulated_liftLeft` and
  `DerivedCategoryB.isTriangulated_mapDerivedCategoryB` — the restriction of a triangulated
  functor to two triangulated subcategories `D_B` it preserves is triangulated.
* `DerivedCategoryB.isZero_mapDerivedCategoryB_obj_iff` — for an exact functor `G`, a complex is
  killed by the induced functor exactly when `G` kills all its cohomology objects.
* `Stacks.Adequate.BigSite.isTriangulated_derivedAdequate` — `D_Adeq(𝒪)` is a triangulated
  subcategory of `D(𝒪)`, so that `D_Adeq(𝒪)` is a pretriangulated and triangulated category.
* `Stacks.Adequate.BigSite.isWeakSerreClass_parasiticModule` — the parasitic adequate modules
  are a weak Serre subcategory of all `𝒪`-modules, so that `D_𝒞(𝒪)` is triangulated.
* `Stacks.Adequate.BigSite.parasiticModule_iff_isZero` — an adequate module is parasitic exactly
  when its restriction to the small Zariski site of `S` vanishes ([Stacks, Tag 06ZM]).
* `Stacks.Adequate.BigSite.isLocalization_trW_derivedParasitic_of_adjunction` — the deduction of
  [Stacks, Tag 070X] from [Stacks, Tag 070W]: a triangulated `Rf_*` with kernel `D_𝒞(𝒪)` and a
  fully faithful left adjoint is the Verdier quotient of `D_Adeq(𝒪)` by `D_𝒞(𝒪)`.

## Implementation notes

The triangulated structures are Mathlib's on a full subcategory cut out by a triangulated
`ObjectProperty`, so they need no construction beyond the statement that the subcategory is
triangulated, which is [Stacks, Tag 06UQ] for a weak Serre class
(`DerivedCategoryB.isTriangulated_derivedCategoryB`). The adequate modules are a weak Serre class
by `Stacks.Adequate.adequate_isWeakSerreClass`, a theorem rather than an instance, so the
triangulatedness of `D_Adeq(𝒪)` is recorded here as an instance.

The parasitic adequate modules are a weak Serre class of `Mod(𝒪)` because they are the kernel of
the exact functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` inside the weak Serre class `Adeq(𝒪)`
([Stacks, Tags 06ZM and 06ZN]): closure under kernels, cokernels and extensions in `Mod(𝒪)` is
closure in `Adeq(𝒪)`, where it is the Serre property of the kernel of `v`.

## References

* [Stacks Project, Tag 070X](https://stacks.math.columbia.edu/tag/070X)
* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06ZM](https://stacks.math.columbia.edu/tag/06ZM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DerivedCategoryB

/-! ### Restricting triangulated functors to the subcategories `D_B` -/

section Triangulated

variable {A A' : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category A'] [Abelian A'] [HasDerivedCategory A']
  {P : ObjectProperty A} {Q : ObjectProperty A'}
  [(derivedCategoryB P).IsTriangulated] [(derivedCategoryB Q).IsTriangulated]

section Right

variable (R : DerivedCategory A ⥤ DerivedCategory A')
  (hR : ∀ K : DerivedCategory A, derivedCategoryB P K → derivedCategoryB Q (R.obj K))
  [R.CommShift ℤ]

/-- The restriction of a functor commuting with the shifts commutes with the shifts. -/
public instance commShift_liftRight : (liftRight R hR).CommShift ℤ :=
  inferInstanceAs (((derivedCategoryB Q).lift _ _).CommShift ℤ)

/-- The restriction of a triangulated functor to two triangulated subcategories `D_B` it
preserves is triangulated. -/
public instance isTriangulated_liftRight [R.IsTriangulated] : (liftRight R hR).IsTriangulated :=
  inferInstanceAs ((derivedCategoryB Q).lift _ _).IsTriangulated

end Right

section Left

variable (L : DerivedCategory A' ⥤ DerivedCategory A)
  (hL : ∀ K : DerivedCategory A', derivedCategoryB Q K → derivedCategoryB P (L.obj K))
  [L.CommShift ℤ]

/-- The restriction of a functor commuting with the shifts commutes with the shifts. -/
public instance commShift_liftLeft : (liftLeft L hL).CommShift ℤ :=
  inferInstanceAs (((derivedCategoryB P).lift _ _).CommShift ℤ)

/-- The restriction of a triangulated functor to two triangulated subcategories `D_B` it
preserves is triangulated. -/
public instance isTriangulated_liftLeft [L.IsTriangulated] : (liftLeft L hL).IsTriangulated :=
  inferInstanceAs ((derivedCategoryB P).lift _ _).IsTriangulated

end Left

section Exact

variable (G : A ⥤ A') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [Q.IsClosedUnderIsomorphisms] (hGQ : ∀ X : A, P X → Q (G.obj X))

/-- The functor `D_B(A) ⥤ D_B'(A')` induced by an exact functor commutes with the shifts. -/
public instance commShift_mapDerivedCategoryB : (mapDerivedCategoryB G hGQ).CommShift ℤ :=
  inferInstanceAs (((derivedCategoryB Q).lift _ _).CommShift ℤ)

/-- The functor `D_B(A) ⥤ D_B'(A')` induced by an exact functor is triangulated. -/
public instance isTriangulated_mapDerivedCategoryB : (mapDerivedCategoryB G hGQ).IsTriangulated :=
  inferInstanceAs ((derivedCategoryB Q).lift _ _).IsTriangulated

end Exact

end Triangulated

/-! ### The kernel of the functor induced by an exact functor -/

section Kernel

variable {A A' : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category A'] [Abelian A'] [HasDerivedCategory A']
  (G : A ⥤ A') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The kernel of the derived functor of an exact functor.** A complex is killed by the functor
induced on derived categories by an exact functor `G` exactly when `G` kills each of its
cohomology objects, since `G` commutes with taking cohomology. -/
public theorem isZero_mapDerivedCategory_obj_iff (K : DerivedCategory A) :
    IsZero (G.mapDerivedCategory.obj K) ↔
      ∀ n : ℤ, IsZero (G.obj ((DerivedCategory.homologyFunctor A n).obj K)) := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · exact (((DerivedCategory.homologyFunctor A' n).map_isZero h)).of_iso
      ((mapDerivedCategoryHomologyIso G n).app K).symm
  · have hK : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor A' n).obj
        (G.mapDerivedCategory.obj K)) :=
      fun n => (h n).of_iso ((mapDerivedCategoryHomologyIso G n).app K)
    have : IsIso (0 : G.mapDerivedCategory.obj K ⟶ G.mapDerivedCategory.obj K) :=
      (DerivedCategory.isIso_iff A' _).2 fun n => (hK n).isIso (hK n) _
    exact (IsZero.iff_id_eq_zero _).2 ((cancel_mono
      (0 : G.mapDerivedCategory.obj K ⟶ G.mapDerivedCategory.obj K)).1 (by simp))

variable {P : ObjectProperty A} {Q : ObjectProperty A'} [Q.IsClosedUnderIsomorphisms]
  (hGQ : ∀ X : A, P X → Q (G.obj X))

/-- A complex of `D_B(A)` is killed by the functor `D_B(A) ⥤ D_B'(A')` induced by an exact
functor `G` exactly when `G` kills each of its cohomology objects. -/
public theorem isZero_mapDerivedCategoryB_obj_iff (K : (derivedCategoryB P).FullSubcategory) :
    IsZero ((mapDerivedCategoryB G hGQ).obj K) ↔
      ∀ n : ℤ, IsZero (G.obj ((DerivedCategory.homologyFunctor A n).obj K.obj)) := by
  rw [← isZero_mapDerivedCategory_obj_iff G]
  exact ⟨fun h => (derivedCategoryB Q).ι.map_isZero h,
    fun h => IsZero.of_full_of_faithful_of_isZero (derivedCategoryB Q).ι _ h⟩

end Kernel

end DerivedCategoryB

namespace Stacks.Adequate

universe d d' u

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### `D_Adeq(𝒪)` and `D_QCoh(S)` are triangulated -/

section Triangulated

variable [HasSheafify B.topology AddCommGrpCat.{u}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} B.structureSheaf)]

/-- **`D_Adeq(𝒪)` is a triangulated subcategory of `D(𝒪)`**, by [Stacks, Tag 06UQ] for the weak
Serre class of adequate modules ([Stacks, Tag 06VQ]). With Mathlib's structure on a full
subcategory cut out by a triangulated property, this makes `D_Adeq(𝒪)` a pretriangulated
category, and a triangulated one. -/
public instance BigSite.isTriangulated_derivedAdequate :
    (BigSite.derivedAdequate.{u, u, d} B).IsTriangulated :=
  have := adequate_isWeakSerreClass B
  inferInstance

end Triangulated

/-! ### `D_𝒞(𝒪)`, the complexes with parasitic adequate cohomology -/

/-- The parasitic adequate `𝒪`-modules on a chosen big `τ`-site over `S`, as a property of all
`𝒪`-modules: the subcategory `𝒞` of [Stacks, Tag 070X] read inside `Mod(𝒪)`. -/
public def BigSite.parasiticModule : ObjectProperty (SheafOfModules.{u} B.structureSheaf) :=
  fun F => IsAdequate B F ∧ IsParasitic S B.toOver F.val

/-- A module is parasitic adequate exactly when it is adequate and, as an adequate module, lies
in the subcategory `𝒞 ⊂ Adeq(𝒪)` of [Stacks, Tag 06ZN]. -/
public theorem BigSite.parasiticModule_iff (F : SheafOfModules.{u} B.structureSheaf) :
    B.parasiticModule F ↔ ∃ hF : IsAdequate B F, B.parasiticAdequate ⟨F, hF⟩ :=
  ⟨fun h => ⟨h.1, h.2⟩, fun ⟨hF, h⟩ => ⟨hF, h⟩⟩

/-- An adequate module is parasitic exactly when its restriction to the small Zariski site of
`S` vanishes, which is [Stacks, Tag 06ZM] (1) ⇔ (2). -/
public theorem BigSite.parasiticModule_iff_isZero (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) :
    B.parasiticModule F ↔ IsZero (B.restrictModuleOfSheaf.obj F) :=
  ⟨fun h => ((tfae_isZero_restrictModule_of_isAdequate.{u, u} B F hF).out 1 2).2 h.2,
    fun h => ⟨hF, ((tfae_isZero_restrictModule_of_isAdequate.{u, u} B F hF).out 1 2).1 h⟩⟩

variable [HasSheafify B.topology AddCommGrpCat.{u}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The parasitic adequate modules are a weak Serre subcategory of `Mod(𝒪)`.** They are the
kernel of the exact functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` inside the weak Serre subcategory
`Adeq(𝒪)`. -/
public theorem BigSite.isWeakSerreClass_parasiticModule : B.parasiticModule.IsWeakSerreClass := by
  have := adequate_isWeakSerreClass B
  have hiff := B.parasiticModule_iff_isZero
  let G := B.restrictModuleOfSheaf
  have hz : ∀ {X}, B.parasiticModule X → IsZero (G.obj X) := fun h => (hiff _ h.1).1 h
  have hp : ∀ {X}, IsAdequate B X → IsZero (G.obj X) → B.parasiticModule X :=
    fun hX h => (hiff _ hX).2 h
  refine
    { exists_zero := ?_
      of_iso := ?_
      kernels_le := ?_
      cokernels_le := ?_
      prop_X₂_of_shortExact := ?_ }
  · obtain ⟨Z, hZ, hZP⟩ := (adequate.{u, u} B).exists_prop_of_containsZero
    exact ⟨Z, hZ, hp hZP (G.map_isZero hZ)⟩
  · intro X Y e h
    exact hp ((adequate.{u, u} B).prop_of_iso e h.1) ((hz h).of_iso (G.mapIso e).symm)
  · rintro _ ⟨f, k, hk, hX, hY⟩
    have hk' : IsAdequate B k.pt :=
      (adequate.{u, u} B).prop_of_isLimit_kernelFork hk hX.1 hY.1
    have := Fork.IsLimit.mono hk
    exact hp hk' (IsZero.of_mono (G.map k.ι) (hz hX))
  · rintro _ ⟨f, k, hk, hX, hY⟩
    have hk' : IsAdequate B k.pt :=
      (adequate.{u, u} B).prop_of_isColimit_cokernelCofork hk hX.1 hY.1
    have := Cofork.IsColimit.epi hk
    let T := ShortComplex.mk (kernel.ι k.π) k.π (kernel.condition _)
    have hT : T.ShortExact := ShortComplex.ShortExact.mk' (T.exact_of_f_is_kernel
      (kernelIsKernel _)) (inferInstanceAs (Mono (kernel.ι k.π))) (inferInstanceAs (Epi k.π))
    have h₁ : IsAdequate B T.X₁ := (adequate.{u, u} B).prop_kernel _ hY.1 hk'
    have : Epi (G.map k.π) := B.epi_zariskiRestrictModule_map_of_shortExact T hT h₁
    exact hp hk' (IsZero.of_epi (G.map k.π) (hz hY))
  · intro T hT h₁ h₃
    have h₂ : IsAdequate B T.X₂ := (adequate.{u, u} B).prop_X₂_of_shortExact hT h₁.1 h₃.1
    have hex : (T.map G).Exact := (T.map G).exact_of_f_is_kernel
      (isLimitForkMapOfIsLimit' G T.zero hT.fIsKernel)
    exact hp h₂ (hex.isZero_X₂ ((hz h₁).eq_of_src _ _) ((hz h₃).eq_of_tgt _ _))

variable [HasDerivedCategory.{d} (SheafOfModules.{u} B.structureSheaf)]

/-- `D_𝒞(𝒪)`: the complexes of `𝒪`-modules on a chosen big `τ`-site over `S` whose cohomology
modules are parasitic adequate, the subcategory `D_B(A)` of [Stacks, Tag 06UP] at the parasitic
adequate modules. -/
public abbrev BigSite.derivedParasitic :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} B.structureSheaf)) :=
  DerivedCategoryB.derivedCategoryB B.parasiticModule

/-- `D_𝒞(𝒪)` is a triangulated subcategory of `D(𝒪)`. -/
public instance BigSite.isTriangulated_derivedParasitic :
    (BigSite.derivedParasitic.{d, u} B).IsTriangulated :=
  have := B.isWeakSerreClass_parasiticModule
  inferInstance

/-- `D_𝒞(𝒪)` is contained in `D_Adeq(𝒪)`. -/
public theorem BigSite.derivedParasitic_le_derivedAdequate :
    BigSite.derivedParasitic.{d, u} B ≤ BigSite.derivedAdequate.{u, u, d} B :=
  fun _ hK n => (hK n).1

/-! ### The deduction of the quotient from the adjunction -/

/-- **[Stacks, Tag 070X] from the adjunction of [Stacks, Tag 070W].** Let
`Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` be a triangulated functor whose kernel is `D_𝒞(𝒪)`. If `Rf_*` has a
fully faithful left adjoint `Lf^*`, then `Rf_*` is the Verdier quotient of `D_Adeq(𝒪)` by
`D_𝒞(𝒪)`: it is a localization functor for the morphisms whose cone has parasitic adequate
cohomology.

This is the source's argument: the counit `Lf^*Rf_*X ⟶ X` is inverted by `Rf_*`, and `Lf^*`
inverts `Rf_*` on `Hom`-sets
(`CategoryTheory.Functor.isLocalization_trW_kernel_of_leftAdjoint`). -/
public theorem BigSite.isLocalization_trW_derivedParasitic_of_adjunction
    [HasDerivedCategory.{d'} (SheafOfModules.{u} S.ringCatSheaf)]
    {Lf : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ⥤
      (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory}
    {Rf : (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory}
    [Lf.Full] [Lf.Faithful] (adj : Lf ⊣ Rf) [Rf.CommShift ℤ] [Rf.IsTriangulated]
    (hker : Rf.kernel = (BigSite.derivedParasitic.{d, u} B).inverseImage
      (BigSite.derivedAdequate.{u, u, d} B).ι) :
    Rf.IsLocalization ((BigSite.derivedParasitic.{d, u} B).inverseImage
      (BigSite.derivedAdequate.{u, u, d} B).ι).trW := by
  rw [← hker]
  exact Functor.isLocalization_trW_kernel_of_leftAdjoint adj

end Stacks.Adequate

end
