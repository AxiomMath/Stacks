module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift

/-!
# The derived fibre over a point of an affine scheme

Let `χ : R ⟶ K` be a homomorphism of commutative rings, with `K = CommRingCat.of K₀`, and let
`t = Spec χ : Spec K ⟶ Spec R`. For `M ∈ D(R)` the derived fibre `M ⊗ᴸ_R K` is computed on the
geometric side: its cohomology is the cohomology of the derived global sections, over the base
`Spec K`, of the derived pullback along `t` of `M̃`,

`Hⁿ(M ⊗ᴸ_R K) ≅ Hⁿ(RΓ(Spec K, Lt^*(M̃)))`,

naturally in `M`. This is how the fibres of the proofs of
[Stacks, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1) and
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2) — cohomology of `X_s` over `κ(s)` —
are read as the derived fibres `E ⊗ᴸ κ(s)` of the source's perfect complexes `E` over the ring of
an affine neighbourhood.

## Main definitions

* `AlgebraicGeometry.MinimalComplexFunctoriality.homologySpecIso`: on `Spec K`, the cohomology of
  `N ∈ D(K)` is the cohomology of the derived global sections of `Ñ`, the latter read as a
  `K`-module through `Γ(Spec K, 𝒪) ≅ K`.
* `AlgebraicGeometry.MinimalComplexFunctoriality.homologyFibreIso`: the displayed natural
  isomorphism, the composite of `homologySpecIso` with the affine comparison square of
  [Stacks, Tag 08DW] (2).

## Main results

* `AlgebraicGeometry.MinimalComplexFunctoriality.exists_map_derivedPullback_ne_zero`: the matrix
  argument of [Stacks, Tag 0BF2] over an affine base, for perfect objects of `D(𝒪_{Spec R})` with
  quasi-coherent cohomology and their derived fibres over `Spec K`; it is
  `StacksDraft.Perfect.FibreCycleLift.exists_unit_map_derived_ne_zero` transported through
  [Stacks, Tag 06Z0] and `homologyFibreIso`.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of the derived base
change map of [Stacks, Tag 08HY] and of [Stacks, Tag 0B91]. The global sections over the base are
`Stacks.Cohomology.GlobalKunneth.baseSections`, the spelling of the fibre cohomology in the cube
chain. The identification with the derived global sections of [Stacks, Tag 06Z0] is
`AlgebraicGeometry.derivedSectionsBaseIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry.MinimalComplexFunctoriality

attribute [local instance 10000] HasDerivedCategory.standard

variable (K : Type u) [CommRing K]

/-- **The cohomology of `N ∈ D(K)` is the cohomology of `RΓ(Spec K, Ñ)`**, the latter read as a
`K`-module through `Γ(Spec K, 𝒪) ≅ K`. The unit of the derived Spec–Γ adjunction of
[Stacks, Tag 06Z0]
(`AlgebraicGeometry.StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit`)
followed by `AlgebraicGeometry.derivedSectionsBaseIso` and the commutation of the exact functor
of restriction of scalars with cohomology. -/
def homologySpecIso (n : ℤ) :
    DerivedCategory.homologyFunctor (ModuleCat.{u} K) n ≅
      (tilde.functor (CommRingCat.of K)).mapDerivedCategory ⋙
        Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace ⋙
          DerivedCategory.homologyFunctor _ n ⋙
            ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of K)
  let u : 𝟭 _ ≅ (derivedTilde (CommRingCat.of K) ⋙
      (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of K)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of K)).ringCatSheaf)).ι) ⋙
      derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of K))) :=
    asIso (derivedTildeGlobalSectionsAdjunction (CommRingCat.of K)).val.unit
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight u _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (derivedTildeCompι (CommRingCat.of K)) _ ≪≫
      Functor.isoWhiskerLeft _ (derivedSectionsBaseIso (A := K)).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Stacks.Homology.derivedHomologyIso
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) n))

variable {K} {R : CommRingCat.{u}} (χ : R ⟶ CommRingCat.of K)

/-- **The derived fibre `M ⊗ᴸ_R K` has the cohomology of `RΓ(Spec K, Lt^*(M̃))`**, naturally in
`M ∈ D(R)`, for `t = Spec χ`: `homologySpecIso` composed with the affine comparison square
`Lt^*(M̃) ≅ (M ⊗ᴸ_R K)~` of [Stacks, Tag 08DW] (2),
`AlgebraicGeometry.StandardModel.affinePullbackComparison`. -/
def homologyFibreIso (n : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} χ.hom).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} K) n ≅
      (tilde.functor R).mapDerivedCategory ⋙ StandardModel.specDerivedPullback χ ⋙
        Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace ⋙
          DerivedCategory.homologyFunctor _ n ⋙
            ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
  Functor.isoWhiskerLeft _ (homologySpecIso K n) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).symm _ ≪≫
    Functor.associator _ _ _

/-- A naturality square for a natural isomorphism `F ≅ G ⋙ H` followed by `H` of isomorphisms
out of the values of `G`. -/
theorem natIso_trans_mapIso_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) (H : E ⥤ D) (η : F ≅ G ⋙ H) {X X' : C} {Y Y' : E}
    (e : G.obj X ≅ Y) (e' : G.obj X' ≅ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (hab : G.map a ≫ e'.hom = e.hom ≫ b) :
    F.map a ≫ (η.app X' ≪≫ H.mapIso e').hom = (η.app X ≪≫ H.mapIso e).hom ≫ H.map b := by
  have hn := η.hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, hab, Functor.map_comp]

/-- The fibre functor `M ↦ Hⁿ(RΓ(Spec K, Lt^*(M̃)))`, read as `K`-modules, on `D(𝒪_{Spec R})`. -/
abbrev fibreHomology (n : ℤ) : DerivedCategory (Spec R).Modules ⥤ ModuleCat.{u} K :=
  StandardModel.specDerivedPullback χ ⋙
    Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of K)).toRingedSpace ⋙
      DerivedCategory.homologyFunctor _ n ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- The identification `Hⁿ(M ⊗ᴸ_R K) ≅ Hⁿ(RΓ(Spec K, Lt^* Ẽ))` for an isomorphism `M̃ ≅ E`. -/
private def fibreHomologyIso (n : ℤ) {X : DerivedCategory (ModuleCat.{u} R)}
    {Y : DerivedCategory (Spec R).Modules} (e : (tilde.functor R).mapDerivedCategory.obj X ≅ Y) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).obj
        ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.obj X) ≅
      (fibreHomology χ n).obj Y :=
  (homologyFibreIso χ n).app X ≪≫ (fibreHomology χ n).mapIso e

/-- Taking `tilde` of the transpose `homEquiv` of a map `M̃ ⟶ Ñ` gives back that map. -/
private theorem mapDerivedCategory_homEquiv {M N : DerivedCategory (ModuleCat.{u} R)}
    (f : (tilde.functor R).mapDerivedCategory.obj M ⟶ (tilde.functor R).mapDerivedCategory.obj N) :
    (tilde.functor R).mapDerivedCategory.map (StandardModel.homEquiv R M N f) = f :=
  (StandardModel.homEquiv R M N).symm_apply_apply _

/-- A map whose image under `F`, composed with an isomorphism, vanishes has vanishing image. -/
private theorem map_eq_zero_of_map_comp_isIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (e : Y ⟶ Z) [IsIso e]
    (h : F.map (f ≫ e) = 0) : F.map f = 0 := by
  rwa [← cancel_mono (F.map e), zero_comp, ← Functor.map_comp]

/-- A map `a` of `D(R)` has `Lt^*(ã) = 0` if and only if its derived fibre `a ⊗ᴸ_R K` is zero, by
the affine comparison square of [Stacks, Tag 08DW] (2) and the full faithfulness of
`D(K) ⥤ D(𝒪_{Spec K})`. -/
private theorem specDerivedPullback_map_eq_zero_iff {X X' : DerivedCategory (ModuleCat.{u} R)}
    (a : X ⟶ X') :
    (StandardModel.specDerivedPullback χ).map ((tilde.functor R).mapDerivedCategory.map a) = 0 ↔
      (totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.map a = 0 := by
  have h : (StandardModel.specDerivedPullback χ).map ((tilde.functor R).mapDerivedCategory.map a) ≫
        (StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).hom.app X' =
      (StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).hom.app X ≫
        (tilde.functor (CommRingCat.of K)).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.map a) :=
    (StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).hom.naturality a
  constructor
  · intro ha
    rw [ha, zero_comp] at h
    refine (StandardModel.mapDerivedCategoryFullyFaithful (CommRingCat.of K)).map_injective ?_
    rw [Functor.map_zero,
      ← cancel_epi ((StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).hom.app X),
      comp_zero]
    exact h.symm
  · intro ha
    rw [ha, Functor.map_zero, comp_zero] at h
    rwa [← cancel_mono ((StandardModel.affinePullbackComparison R (CommRingCat.of K) χ).hom.app X'),
      zero_comp]

/-- Joint injectivity of the maps `(fibreHomology χ n).map (φ k)` transports, along isomorphisms
`M̃ ≅ E` and `Ñ k ≅ F k` intertwining `ψ k` with `φ k`, to joint injectivity of the maps
`Hⁿ(ψ k ⊗ᴸ_R K)`. -/
private theorem eq_zero_of_forall_homology_map_eq_zero (n : ℤ) {ι : Type*}
    {M : DerivedCategory (ModuleCat.{u} R)} {N : ι → DerivedCategory (ModuleCat.{u} R)}
    {E : DerivedCategory (Spec R).Modules} {F : ι → DerivedCategory (Spec R).Modules}
    (eM : (tilde.functor R).mapDerivedCategory.obj M ≅ E)
    (eN : ∀ k, (tilde.functor R).mapDerivedCategory.obj (N k) ≅ F k)
    (ψ : ∀ k, M ⟶ N k) (φ : ∀ k, E ⟶ F k)
    (hψφ : ∀ k, (tilde.functor R).mapDerivedCategory.map (ψ k) ≫ (eN k).hom = eM.hom ≫ φ k)
    (h : ∀ c : (fibreHomology χ n).obj E, (∀ k, (fibreHomology χ n).map (φ k) c = 0) → c = 0)
    (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).obj
      ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.obj M))
    (hc : ∀ k, (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).map
      ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.map (ψ k)) c = 0) : c = 0 := by
  let Θ : ∀ {X : DerivedCategory (ModuleCat.{u} R)} {Y : DerivedCategory (Spec R).Modules}
      (_ : (tilde.functor R).mapDerivedCategory.obj X ≅ Y),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).obj
          ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.obj X) ≅
        (fibreHomology χ n).obj Y := fun {X _} e =>
    (homologyFibreIso χ n).app X ≪≫ (fibreHomology χ n).mapIso e
  have hΘ : ∀ k, (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).map
      ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.map (ψ k)) ≫
        (fibreHomologyIso χ n (eN k)).hom =
        (fibreHomologyIso χ n eM).hom ≫ (fibreHomology χ n).map (φ k) := fun k =>
    natIso_trans_mapIso_naturality _ _ _ (homologyFibreIso χ n) eM (eN k) (ψ k) (φ k) (hψφ k)
  have h0 : (fibreHomologyIso χ n eM).hom c = 0 := h _ fun k => by
    have := congrArg (fun f => f.hom c) (hΘ k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [← this, hc k, map_zero]
  have := congrArg (fibreHomologyIso χ n eM).inv h0
  rwa [← ModuleCat.comp_apply, Iso.hom_inv_id, map_zero] at this

/-- **The matrix argument of [Stacks, Tag 0BF2] over an affine base.** Let `E` and `E k` (`k` in a
finite type) be perfect objects of `D(𝒪_{Spec R})` with quasi-coherent cohomology, let
`φ k : E ⟶ E k`, and let `t = Spec χ` for a homomorphism `χ : R ⟶ K` to a field. If the maps
`H¹(RΓ(Spec K, Lt^* φ k))` are jointly injective, each `H⁰(RΓ(Spec K, Lt^*(E k)))` has dimension at
most one and is reached by a map `𝒪[0] ⟶ E k` whose derived pullback is nonzero, and
`H⁰(RΓ(Spec K, Lt^* E)) ≠ 0`, then some map `𝒪[0] ⟶ E` has nonzero derived pullback along `t`.

Here `𝒪[0]` is `R̃` in degree `0`. -/
theorem exists_map_derivedPullback_ne_zero (hK : IsField K)
    (E : DerivedCategory (Spec R).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hEq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent)
    {ι : Type u} [Finite ι] (F : ι → DerivedCategory (Spec R).Modules)
    (hF : ∀ k, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) (F k))
    (hFq : ∀ k (n : ℤ),
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj (F k)).IsQuasicoherent)
    (φ : ∀ k, E ⟶ F k)
    (h1 : ∀ c : (fibreHomology χ 1).obj E, (∀ k, (fibreHomology χ 1).map (φ k) c = 0) → c = 0)
    (hdim : ∀ k, Module.finrank K ((fibreHomology χ 0).obj (F k)) ≤ 1)
    (hz : ∀ k, ∃ z : (tilde.functor R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.unitComplex R)) ⟶ F k,
      (StandardModel.specDerivedPullback χ).map z ≠ 0)
    (hne : Nontrivial ((fibreHomology χ 0).obj E)) :
    ∃ y : (tilde.functor R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.unitComplex R)) ⟶ E,
      (StandardModel.specDerivedPullback χ).map y ≠ 0 := by
  let : Field K := hK.toField
  classical
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E hEq
  choose N eN' using fun k => StandardModel.exists_iso_mapDerivedCategory R (F k) (hFq k)
  let eN : ∀ k, (tilde.functor R).mapDerivedCategory.obj (N k) ≅ F k := fun k => (eN' k).some
  have hM : StacksDraft.Perfect.IsPerfect M := (isPerfect_tilde_iff M).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
      eM.symm hE)
  have hN : ∀ k, StacksDraft.Perfect.IsPerfect (N k) := fun k => (isPerfect_tilde_iff (N k)).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
      (eN k).symm (hF k))
  let ψ : ∀ k, M ⟶ N k := fun k => StandardModel.homEquiv R M (N k) (eM.hom ≫ φ k ≫ (eN k).inv)
  have hψE : ∀ k, (tilde.functor R).mapDerivedCategory.map (ψ k) ≫ (eN k).hom = eM.hom ≫ φ k :=
    fun k => by
      rw [mapDerivedCategory_homEquiv]
      simp
  have hdim' : ∀ k, Module.finrank K ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) 0).obj
      ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.obj (N k))) ≤ 1 := fun k =>
    (fibreHomologyIso χ 0 (eN k)).toLinearEquiv.finrank_eq ▸ hdim k
  have hne' : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) 0).obj
      ((totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.obj M)) :=
    (fibreHomologyIso χ 0 eM).toLinearEquiv.symm.injective.nontrivial
  have hz' : ∀ k, ∃ z : DerivedCategory.Q.obj (StacksDraft.Perfect.FibreCycleLift.unitComplex R) ⟶
      N k, (totalDerivedExtensionScalars.{u, u, u} χ.hom).functor.map z ≠ 0 := by
    intro k
    obtain ⟨z, hz⟩ := hz k
    refine ⟨StandardModel.homEquiv R _ (N k) (z ≫ (eN k).inv), fun h0 => hz ?_⟩
    have h2 := (specDerivedPullback_map_eq_zero_iff χ _).2 h0
    rw [mapDerivedCategory_homEquiv] at h2
    exact map_eq_zero_of_map_comp_isIso _ _ _ h2
  obtain ⟨y, hy⟩ := StacksDraft.Perfect.FibreCycleLift.exists_unit_map_derived_ne_zero χ.hom
    (totalDerivedExtensionScalars.{u, u, u} χ.hom) M hM N hN ψ
    (eq_zero_of_forall_homology_map_eq_zero χ 1 eM eN ψ φ hψE h1) hdim' hz' hne'
  refine ⟨(tilde.functor R).mapDerivedCategory.map y ≫ eM.hom,
    fun h0 => hy ((specDerivedPullback_map_eq_zero_iff χ y).1 ?_)⟩
  exact map_eq_zero_of_map_comp_isIso _ _ _ h0

end AlgebraicGeometry.MinimalComplexFunctoriality

end
