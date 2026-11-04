module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPullbackLimitPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.Homology.DerivedCategory.ModelHomBijective

/-!
# Pulling back an inverse limit along a proper flat morphism

Let `R` be a ring and `f : X ⟶ Spec R` proper, flat and of finite presentation, and let `(Mₙ)` be
an inverse system of `R`-modules with surjective transition maps. [Stacks, Tag 0D2Q] asserts
that the canonical map

`O_X ⊗_R (lim Mₙ) ⟶ lim (O_X ⊗_R Mₙ)`

induces an isomorphism from the source to `DQ_X` applied to the target, `DQ_X` being the right
adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` ([Stacks, Tag 0CR0]). As the source's proof
says, this means that for every object `E` of `D_QCoh(𝒪_X)` the induced map
`Hom(E, O_X ⊗_R lim Mₙ) ⟶ Hom(E, lim O_X ⊗_R Mₙ)` is bijective.

Here `O_X ⊗_R M` is `f^*M^~` (`tilde.functor R ⋙ Scheme.Modules.pullback f`), both modules sit in
degree zero, the limit on the right is taken in `𝒪_X`-modules, and the canonical map is
`CategoryTheory.Limits.limit.post`.

## Main results

* `Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_map_limitPost`:
  **[Stacks, Tag 0D2Q]** in the form the source's proof unfolds it, at an arbitrary model of the
  derived category.
* `Stacks.ProperFlatPullbackLimit.isIso_homEquiv_singleFunctor_map_limitPost`:
  **[Stacks, Tag 0D2Q]** as stated: for every right adjoint `DQ` of the inclusion of
  `D_QCoh(𝒪_X)`, the morphism from the source to `DQ` of the target adjoint to the canonical map
  is an isomorphism.

## The proof

This is the source's proof.

* For a perfect object `E`, with dual `E^∨`, morphisms `E ⟶ O_X ⊗_R N` are morphisms
  `Q' ⟶ N^~` for the dual `Q'` of the perfect complex `Q = Rf_*E^∨` on `Spec R`
  (`Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_pullback_map_π`; the duality
  [Stacks, Tag 08DQ], the adjunction `Lf^* ⊣ Rf_*`, the projection formula [Stacks, Tag 08EU] and
  the perfectness of `Rf_*E^∨` of [Stacks, Tag 0A1H]). Since `D(R) ≃ D_QCoh(𝒪_{Spec R})`
  ([Stacks, Tag 06Z0]) and products of modules are products in `D(R)`, they commute with products
  in `N`. With the vanishing of higher cohomology of quasi-coherent modules on affines, this gives
  the statement for products, and the five lemma on the short exact sequences
  `0 → lim → ∏ → ∏ → 0` (the second one is exact because the towers of sections over affine opens
  are surjective, [Stacks, Tag 0A0J]) gives it for the limit
  (`Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_map_limitPost_of_isPerfect`).
* `D_QCoh(𝒪_X)` has a set of perfect generators ([Stacks, Tag 09IS]) and a coherator `DQ_X`
  ([Stacks, Tag 0CR0]). The cone `C` of the canonical map receives no morphism from a shift of a
  perfect object, so `DQ_X(C)` is zero, so `C` receives no morphism from an object of
  `D_QCoh(𝒪_X)`, which is the assertion.

The coherator and the generators are taken at the locally small model, the perfect-object case
at the standard model; bijectivity is carried between models by
`StacksDraft.DerivedModel.bijective_comp_Q_map_iff`.

## References

* [Stacks Project, Tag 0D2Q](https://stacks.math.columbia.edu/tag/0D2Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe w u

namespace Stacks.ProperFlatPullbackLimit

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The image of a perfect complex in the derived category is perfect. -/
lemma isPerfect_Q_obj_of_isPerfectComplex (Y : RingedSpace.{u, u})
    [h : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u, u} Y)]
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Y) ℤ)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex P) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj P) :=
  ⟨P, hP, ⟨Iso.refl _⟩⟩

/-- The cohomology sheaves of a complex are quasi-coherent iff those of its image in the derived
category are. -/
private lemma isQuasicoherent_homologyFunctor_obj_Q_iff [HasDerivedCategory.{w} X.Modules]
    (K : CochainComplex X.Modules ℤ) (q : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules q).obj (DerivedCategory.Q.obj K)).IsQuasicoherent ↔
      (K.homology q).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_iff_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules q).app K)

/-- The cohomology of a perfect complex is quasi-coherent. -/
lemma isQuasicoherent_homology_of_isPerfectComplex (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.toRingedSpace) P) (q : ℤ) :
    (P.homology q).IsQuasicoherent := by
  let := HasDerivedCategory.standard X.Modules
  exact (isQuasicoherent_homologyFunctor_obj_Q_iff P q).1
    (ProperFlatBaseChange.isQuasicoherent_homology_of_isPerfect (DerivedCategory.Q.obj P)
      (isPerfect_Q_obj_of_isPerfectComplex (X.toRingedSpace)
        (h := HasDerivedCategory.standard X.Modules) P hP) q)

/-- **[Stacks, Tag 0D2Q] on a perfect complex, at any model.** For a perfect complex `P`, the
canonical map `O_X ⊗_R lim Mₙ ⟶ lim (O_X ⊗_R Mₙ)` induces a bijection on morphisms out of `P`. -/
theorem bijective_comp_Q_map_single_map_limitPost_of_isPerfectComplex [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (M : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op))
    (h : HasDerivedCategory.{w} X.Modules) (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.toRingedSpace) P) :
    Function.Bijective (fun x : (@DerivedCategory.Q _ _ _ h).obj P ⟶
        (@DerivedCategory.Q _ _ _ h).obj ((CochainComplex.singleFunctor X.Modules 0).obj
          ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (limit M))) =>
      x ≫ (@DerivedCategory.Q _ _ _ h).map ((CochainComplex.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f)))) := by
  rw [StacksDraft.DerivedModel.bijective_comp_Q_map_iff h (HasDerivedCategory.standard X.Modules)]
  let := HasDerivedCategory.standard X.Modules
  exact (bijective_comp_iff_of_iso (Iso.refl _) _ _
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _)
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _)
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.naturality _)).1
    (bijective_comp_singleFunctor_map_limitPost_of_isPerfect f M hsurj _
      (isPerfect_Q_obj_of_isPerfectComplex (X.toRingedSpace)
        (h := HasDerivedCategory.standard X.Modules) P hP))

/-- The cohomology sheaves of a perfect object are quasi-coherent. -/
lemma isQuasicoherent_homologyFunctor_obj_of_isPerfect (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (q : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  let P' : CochainComplex X.Modules ℤ := P
  let e' : DerivedCategory.Q.obj P' ≅ E := e
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules q).mapIso e')
    ((isQuasicoherent_homologyFunctor_obj_Q_iff P' q).2
      (isQuasicoherent_homology_of_isPerfectComplex P' hP q))

/-- On a qcqs scheme, an object receiving no nonzero morphism from a perfect object receives no
nonzero morphism from an object of `D_QCoh(𝒪_X)`: its coherator vanishes. -/
lemma eq_zero_of_forall_isPerfect_eq_zero [CompactSpace X] [QuasiSeparatedSpace X]
    {C : DerivedCategory X.Modules}
    (hC : ∀ E : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E → ∀ w : E ⟶ C, w = 0)
    (Y : Stacks.Duality.quasiCoherentDerivedCategory X)
    (w : (Stacks.Duality.Coherator.quasiCoherentι X).obj Y ⟶ C) : w = 0 := by
  have := Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι X
  let ι := Stacks.Duality.Coherator.quasiCoherentι X
  let adj := Adjunction.ofIsLeftAdjoint ι
  obtain ⟨I, _, Eg, hEg, hgen⟩ := Stacks.Duality.QcqsPerfect.exists_finite_perfect_generators X
  have hDQ : IsZero (ι.obj (ι.rightAdjoint.obj C)) := by
    refine hgen _ (ι.rightAdjoint.obj C).property fun i n g' => ?_
    have hn := Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift (hEg i) n
    let Y : Stacks.Duality.quasiCoherentDerivedCategory X :=
      ⟨(Eg i)⟦n⟧, isQuasicoherent_homologyFunctor_obj_of_isPerfect _ hn⟩
    obtain ⟨g'', rfl⟩ := ι.map_surjective (X := Y) g'
    have h0 : ι.map g'' ≫ adj.counit.app C = 0 := hC _ hn _
    have h2 : (adj.homEquiv Y C).symm g'' = (adj.homEquiv Y C).symm 0 :=
      (adj.homEquiv_counit Y C g'').trans (h0.trans (zero_comp.symm.trans
        ((congrArg (· ≫ adj.counit.app C) (ι.map_zero Y _).symm).trans
          (adj.homEquiv_counit Y C 0).symm)))
    rw [(adj.homEquiv Y C).symm.injective h2, ι.map_zero]
    rfl
  rw [((adj.homEquiv Y C).symm_apply_apply w).symm.trans
      (adj.homEquiv_counit Y C (adj.homEquiv Y C w)),
    hDQ.eq_of_tgt (ι.map (adj.homEquiv Y C w)) 0, zero_comp]

/-- **[Stacks, Tag 0D2Q] on a complex with quasi-coherent cohomology, at the locally small
model.** This is where the coherator and the perfect generators of `D_QCoh(𝒪_X)` are used. -/
theorem bijective_comp_Q_map_single_map_limitPost_of_isQuasicoherent [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (M : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ q : ℤ, (K.homology q).IsQuasicoherent) :
    Function.Bijective (fun x : DerivedCategory.Q.obj K ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj
          ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (limit M))) =>
      x ≫ DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f)))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let g := DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map
    (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f)))
  obtain ⟨Cn, v, w, hT⟩ := distinguished_cocone_triangle g
  let Pf : DerivedCategory X.Modules → Prop := fun E =>
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E
  have hPf : ∀ (E : DerivedCategory X.Modules) (n : ℤ), Pf E → Pf (E⟦n⟧) := fun _ n hE =>
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hE n
  have hbij : ∀ E, Pf E → Function.Bijective (fun x : E ⟶ _ => x ≫ g) := by
    intro E hE
    obtain ⟨P, hP, ⟨e⟩⟩ := hE
    let P' : CochainComplex X.Modules ℤ := P
    let e' : DerivedCategory.Q.obj P' ≅ E := e
    exact (bijective_comp_iff_of_iso e' g g (Iso.refl _) (Iso.refl _) (by simp)).1
      (bijective_comp_Q_map_single_map_limitPost_of_isPerfectComplex f M hsurj _ P' hP)
  have hzero : ∀ E, Pf E → ∀ w' : E ⟶ Cn, w' = 0 :=
    eq_zero_of_bijective_comp_mor₁ (Triangle.mk g v w) hT Pf hPf hbij
  have hQK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj
      (DerivedCategory.Q.obj K)).IsQuasicoherent :=
    fun q => (isQuasicoherent_homologyFunctor_obj_Q_iff K q).2 (hK q)
  have hQK₁ : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj
      ((DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧)).IsQuasicoherent :=
    fun q => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso 1 q (1 + q) rfl).app _).symm
      (hQK (1 + q))
  exact bijective_comp_mor₁_of_eq_zero (Triangle.mk g v w) hT (DerivedCategory.Q.obj K)
    (eq_zero_of_forall_isPerfect_eq_zero hzero ⟨DerivedCategory.Q.obj K, hQK⟩)
    (eq_zero_of_forall_isPerfect_eq_zero hzero ⟨(DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧, hQK₁⟩)

/-- **Stacks Project, Tag 0D2Q**, in the form the source's proof unfolds it. Let `R` be a ring,
`f : X ⟶ Spec R` proper, flat and of finite presentation, and `(Mₙ)` an inverse system of
`R`-modules with surjective transition maps. Then for every object `E` of `D_QCoh(𝒪_X)` the
canonical map `O_X ⊗_R (lim Mₙ) ⟶ lim (O_X ⊗_R Mₙ)` induces a bijection

`Hom(E, O_X ⊗_R (lim Mₙ)) ⟶ Hom(E, lim O_X ⊗_R Mₙ)`.

Here `O_X ⊗_R M` is `f^*M^~`, both modules are placed in degree zero, the limit on the right is
the limit in `𝒪_X`-modules and the canonical map is `limit.post`. The statement is made at an
arbitrary model of the derived category of `𝒪_X`-modules. -/
@[stacks 0D2Q "the canonical map O_X ⊗_R lim M_n --> lim O_X ⊗_R M_n induces bijections \
Hom(E, source) --> Hom(E, target) for every E in D_QCoh(O_X), which is what the source's proof \
says the statement means; at every model of the derived category"]
theorem bijective_comp_singleFunctor_map_limitPost (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op))
    [HasDerivedCategory.{w} X.Modules] (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    Function.Bijective (fun φ : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (limit M)) =>
      φ ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f))) := by
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q (C := X.Modules)) E
  have hK : ∀ q : ℤ, (K.homology q).IsQuasicoherent := fun q =>
    (isQuasicoherent_homologyFunctor_obj_Q_iff K q).1
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules q).mapIso e.symm) (hE q))
  have hL := bijective_comp_Q_map_single_map_limitPost_of_isQuasicoherent f M hsurj K hK
  have hh := (StacksDraft.DerivedModel.bijective_comp_Q_map_iff
    (Scheme.Modules.hasDerivedCategory X) ‹_› K _).1 hL
  exact (bijective_comp_iff_of_iso e _ _
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).inv.naturality _)).1 hh

/-- `O_X ⊗_R lim Mₙ`, placed in degree zero, as an object of `D_QCoh(𝒪_X)`. -/
def pullbackTildeLimitQCoh (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    Stacks.Duality.quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj
      ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (limit M)),
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) _
      (Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance)).2⟩

/-- **Stacks Project, Tag 0D2Q.** Let `R` be a ring, `f : X ⟶ Spec R` proper, flat and of finite
presentation, and `(Mₙ)` an inverse system of `R`-modules with surjective transition maps. Then
the canonical map `O_X ⊗_R (lim Mₙ) ⟶ lim (O_X ⊗_R Mₙ)` induces an isomorphism from the source to
`DQ_X` applied to the target: for every right adjoint `DQ` of the inclusion
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` (one exists by [Stacks, Tag 0CR0]), the morphism
`O_X ⊗_R (lim Mₙ) ⟶ DQ(lim O_X ⊗_R Mₙ)` adjoint to the canonical map is an isomorphism. -/
@[stacks 0D2Q]
theorem isIso_homEquiv_singleFunctor_map_limitPost (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} R) (hsurj : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op))
    {DQ : DerivedCategory X.Modules ⥤ Stacks.Duality.quasiCoherentDerivedCategory X}
    (adj : Stacks.Duality.Coherator.quasiCoherentι X ⊣ DQ) :
    IsIso (adj.homEquiv (pullbackTildeLimitQCoh f M) _
      ((DerivedCategory.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f)))) := by
  let ι := Stacks.Duality.Coherator.quasiCoherentι X
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have heq : (fun x : T ⟶ pullbackTildeLimitQCoh f M => x ≫ adj.homEquiv _ _
      ((DerivedCategory.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f)))) =
      adj.homEquiv T _ ∘ (fun z : ι.obj T ⟶ _ => z ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        (limit.post M (tilde.functor R ⋙ Scheme.Modules.pullback f))) ∘ ι.map :=
    funext fun x => (adj.homEquiv_naturality_left x _).symm
  rw [heq]
  exact (adj.homEquiv T _).bijective.comp
    ((bijective_comp_singleFunctor_map_limitPost R f M hsurj T.obj T.property).comp
      ((ObjectProperty.fullyFaithfulι _).map_bijective _ _))

end Stacks.ProperFlatPullbackLimit
