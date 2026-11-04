module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Naturality

/-!
# The comparison of the `Ext` presheaf with the cohomology sheaf

The maps `Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f) ⟶ Γ(D(f), Hⁿ(R𝓗om(K̃, L̃)))` commute with restriction and
are locally surjective and locally injective.

## Main results

* `AlgebraicGeometry.AffineExt.extToCohomologySheaf_restrict`: the comparison commutes with
  restriction along `D(g) ⊆ D(f)`.
* `AlgebraicGeometry.AffineExt.extToCohomologySheaf_locally_surjective`: the comparison is locally
  surjective.
* `AlgebraicGeometry.AffineExt.extToCohomologySheaf_locally_injective`: the comparison is locally
  injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R))

/-- `K̃` is represented by the associated complex of `srcModel R K`. -/
def srcTildeIso : (tilde.functor R).mapDerivedCategory.obj K ≅
    DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (srcModel R K)) :=
  (tilde.functor R).mapDerivedCategory.mapIso (srcModelIso R K).symm ≪≫
    (tilde.functor R).mapDerivedCategoryFactors.app (srcModel R K)

/-- `L̃` is represented by the resolution. -/
def tgtTildeIso : (tilde.functor R).mapDerivedCategory.obj L ≅
    DerivedCategory.Q.obj (resolution R L) :=
  haveI := quasiIso_resolutionMap R L
  (tilde.functor R).mapDerivedCategory.mapIso (srcModelIso R L).symm ≪≫
    (tilde.functor R).mapDerivedCategoryFactors.app (srcModel R L) ≪≫
    asIso (DerivedCategory.Q.map (resolutionMap R L))

/-- The resolution of `L̃` is K-injective as a complex of sheaves of modules on `Spec R`. -/
lemma isKInjective_resolution' : @CochainComplex.IsKInjective
    (Stacks.SheafOfModules.StructureSheafModules (Spec R).sheaf) _ inferInstance (resolution R L) :=
  isKInjective_resolution R L

/-- `R𝓗om(K̃, L̃)` is represented by the internal Hom complex `homModel R K L`. -/
def derivedSheafHomIso :
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
        (op ((tilde.functor R).mapDerivedCategory.obj K))).obj
          ((tilde.functor R).mapDerivedCategory.obj L) ≅
      DerivedCategory.Q.obj (homModel R K L).obj :=
  ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso (srcTildeIso R K).symm.op).app _ ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj _).mapIso (tgtTildeIso R L) ≪≫
    haveI := isKInjective_resolution' R L
    Stacks.SheafOfModules.derivedSheafHomComparison (Spec R).sheaf _ _

/-- The `n`-th cohomology sheaf of `R𝓗om(K̃, L̃)` is the `n`-th cohomology of the internal Hom
complex. -/
def cohomologySheafIso (n : ℤ) : cohomologySheaf R K L n ≅ (homModel R K L).obj.homology n :=
  (DerivedCategory.homologyFunctor _ n).mapIso (derivedSheafHomIso R K L) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app _

variable (n : ℤ)

/-- The comparison of the cohomology of sections over `D(f)` of the internal Hom complex with the
sections over `D(f)` of the cohomology sheaf of `R𝓗om(K̃, L̃)`. -/
def sectionsToCohomologySheaf (f : R) :
    (secC R K L f).homology n ⟶ (cohomologySheaf R K L n).presheaf.obj (op (basicOpen R f)) :=
  (sectionsHomologyIso (homModel R K L).obj n (op (basicOpen R f))).hom ≫
    ((PresheafOfModules.toPresheaf _).map (toHomologySheaf (homModel R K L).obj n)).app
      (op (basicOpen R f)) ≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (cohomologySheafIso R K L n).inv).app (op (basicOpen R f))

/-- For `D(g) ⊆ D(f)`, `sectionsToCohomologySheaf` commutes with restriction from `D(f)` to
`D(g)`. -/
lemma sectionsToCohomologySheaf_naturality {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    sectionsToCohomologySheaf R K L n f ≫ (cohomologySheaf R K L n).presheaf.map (homOfLE h).op =
      HomologicalComplex.homologyMap (secRestrict R K L h) n ≫
        sectionsToCohomologySheaf R K L n g := by
  ext x
  have e₁ := ConcreteCategory.congr_hom
    (sectionsHomologyIso_naturality (homModel R K L).obj n (homOfLE h).op) x
  have e₂ := ConcreteCategory.congr_hom
    (((PresheafOfModules.toPresheaf _).map (toHomologySheaf (homModel R K L).obj n)).naturality
      (homOfLE h).op)
    ((sectionsHomologyIso (homModel R K L).obj n (op (basicOpen R f))).hom x)
  have e₃ := ConcreteCategory.congr_hom
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (cohomologySheafIso R K L n).inv).naturality (homOfLE h).op)
    (((PresheafOfModules.toPresheaf _).map (toHomologySheaf (homModel R K L).obj n)).app
      (op (basicOpen R f)) ((sectionsHomologyIso (homModel R K L).obj n (op (basicOpen R f))).hom
          x))
  exact e₃.symm.trans (congrArg (ConcreteCategory.hom (((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).map (cohomologySheafIso R K L n).inv).app (op (basicOpen R g))))
      (e₂.symm.trans (congrArg (ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).map
        (toHomologySheaf (homModel R K L).obj n)).app (op (basicOpen R g)))) e₁.symm)))

/-- **The comparison of the `Ext` presheaf with the cohomology sheaf.** Over each principal open
`D(f)`, the map `Ext^n_{R_f}(K ⊗_R R_f, L ⊗_R R_f) ⟶ Γ(D(f), Hⁿ(R𝓗om(K̃, L̃)))`. -/
def extToCohomologySheaf (f : R) :
    localizedExt R K L f n →+ Γ(cohomologySheaf R K L n, basicOpen R f) :=
  (sectionsToCohomologySheaf R K L n f).hom.comp
    (sectionHomologyEquiv R K L f n).symm.toAddMonoidHom

/-- On the class corresponding to `x` under `sectionHomologyEquiv`, `extToCohomologySheaf` agrees
with `sectionsToCohomologySheaf`. -/
lemma extToCohomologySheaf_sectionHomologyEquiv (f : R) (x : ((secC R K L f).homology n : Type u)) :
    extToCohomologySheaf R K L n f (sectionHomologyEquiv R K L f n x) =
      sectionsToCohomologySheaf R K L n f x := by
  rw [extToCohomologySheaf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply]

/-- **The comparison commutes with restriction.** For `D(g) ⊆ D(f)`, restricting the image of an
`Ext` class from `D(f)` to `D(g)` is the image of its derived base change along `R_f ⟶ R_g`. -/
theorem extToCohomologySheaf_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (α : localizedExt R K L f n) :
    (cohomologySheaf R K L n).presheaf.map (homOfLE h).op (extToCohomologySheaf R K L n f α) =
      extToCohomologySheaf R K L n g (localizedExtRestrict R K L h n α) := by
  obtain ⟨x, rfl⟩ := (sectionHomologyEquiv R K L f n).surjective α
  rw [← sectionHomologyEquiv_restrict, extToCohomologySheaf_sectionHomologyEquiv,
    extToCohomologySheaf_sectionHomologyEquiv]
  exact ConcreteCategory.congr_hom (sectionsToCohomologySheaf_naturality R K L n h) x

omit n in
/-- Every open neighbourhood `V` of a point `x` of `Spec R` contains a principal open `D(g)`
containing `x`. -/
lemma exists_basicOpen_le {V : (Spec R).Opens} {x : Spec R} (hx : x ∈ V) :
    ∃ g : R, x ∈ basicOpen R g ∧ basicOpen R g ≤ V := by
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx V.2
  exact ⟨g, hxg, hgV⟩

/-- Restricting along `i` and then along `j` is restricting along `j ≫ i`. -/
private theorem map_op_map_op_apply {C D : Type*} [Category C] [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (F : Cᵒᵖ ⥤ D) {U V W : C} (j : U ⟶ V) (i : V ⟶ W) (x : ToType (F.obj (op W))) :
    (F.map j.op) ((F.map i.op) x) = (F.map (j ≫ i).op) x := by
  rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]

/-- **The comparison is locally surjective.** Every section of `Hⁿ(R𝓗om(K̃, L̃))` over `D(f)` is,
near every point of `D(f)`, the image of an `Ext` class over a smaller principal open. -/
theorem extToCohomologySheaf_locally_surjective (f : R)
    (s : Γ(cohomologySheaf R K L n, basicOpen R f)) (x : Spec R) (hx : x ∈ basicOpen R f) :
    ∃ (g : R) (h : basicOpen R g ≤ basicOpen R f), x ∈ basicOpen R g ∧
      ∃ α : localizedExt R K L g n,
        extToCohomologySheaf R K L n g α =
          (cohomologySheaf R K L n).presheaf.map (homOfLE h).op s := by
  let C := (homModel R K L).obj
  let T := (PresheafOfModules.toPresheaf _).map (toHomologySheaf C n)
  let β := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (cohomologySheafIso R K L n).hom
  let α₃ := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (cohomologySheafIso R K L n).inv
  let s' := β.app (op (basicOpen R f)) s
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology (Spec R))
    T s' x hx
  obtain ⟨g, hxg, hgV⟩ := exists_basicOpen_le R hxV
  refine ⟨g, leOfHom (homOfLE hgV ≫ i), hxg, ?_⟩
  let t' := (homologyPresheaf C n).presheaf.map (homOfLE hgV).op t
  refine ⟨sectionHomologyEquiv R K L g n ((sectionsHomologyIso C n (op (basicOpen R g))).inv t'),
      ?_⟩
  refine (extToCohomologySheaf_sectionHomologyEquiv R K L n g _).trans ?_
  have e₃ : α₃.app (op (basicOpen R f)) s' = s :=
    ConcreteCategory.congr_hom (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
      (cohomologySheafIso R K L n)).hom_inv_id_app (op (basicOpen R f))) s
  refine (congrArg (fun z => α₃.app (op (basicOpen R g)) (T.app (op (basicOpen R g)) z))
    (Iso.inv_hom_id_apply (sectionsHomologyIso C n (op (basicOpen R g))) t')).trans ?_
  refine (congrArg (α₃.app (op (basicOpen R g)))
    (ConcreteCategory.congr_hom (T.naturality (homOfLE hgV).op) t)).trans ?_
  refine (congrArg (fun z => α₃.app (op (basicOpen R g))
    ((((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)) ⋙
      PresheafOfModules.toPresheaf _).obj (C.homology n)).map (homOfLE hgV).op z)) ht).trans ?_
  have e₄ := map_op_map_op_apply
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)) ⋙
      PresheafOfModules.toPresheaf _).obj (C.homology n)) (homOfLE hgV) i s'
  refine (congrArg (α₃.app (op (basicOpen R g))) e₄).trans ?_
  exact (ConcreteCategory.congr_hom
    (α₃.naturality (homOfLE (leOfHom (homOfLE hgV ≫ i))).op) s').trans (congrArg _ e₃)

/-- **The comparison is locally injective.** An `Ext` class over `D(f)` whose image in the
sections of `Hⁿ(R𝓗om(K̃, L̃))` vanishes restricts to zero over a principal open around every point
of `D(f)`. -/
theorem extToCohomologySheaf_locally_injective (f : R) (α : localizedExt R K L f n)
    (hα : extToCohomologySheaf R K L n f α = 0) (x : Spec R) (hx : x ∈ basicOpen R f) :
    ∃ (g : R) (h : basicOpen R g ≤ basicOpen R f), x ∈ basicOpen R g ∧
      localizedExtRestrict R K L h n α = 0 := by
  let C := (homModel R K L).obj
  let T := (PresheafOfModules.toPresheaf _).map (toHomologySheaf C n)
  let β := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (cohomologySheafIso R K L n).hom
  obtain ⟨y, rfl⟩ := (sectionHomologyEquiv R K L f n).surjective α
  rw [extToCohomologySheaf_sectionHomologyEquiv] at hα
  let y' := (sectionsHomologyIso C n (op (basicOpen R f))).hom y
  have hT : T.app (op (basicOpen R f)) y' = T.app (op (basicOpen R f)) 0 := by
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (((SheafOfModules.forget _ ⋙
      PresheafOfModules.toPresheaf _).mapIso (cohomologySheafIso R K L n)).inv_hom_id_app
        (op (basicOpen R f))) (T.app (op (basicOpen R f)) y')).symm.trans
      ((congrArg (β.app (op (basicOpen R f))) hα).trans (map_zero _))
  obtain ⟨V, i, hi, hxV⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (Spec R))
    T y' 0 hT x hx
  obtain ⟨g, hxg, hgV⟩ := exists_basicOpen_le R hxV
  refine ⟨g, leOfHom (homOfLE hgV ≫ i), hxg, ?_⟩
  rw [← sectionHomologyEquiv_restrict]
  have e₁ := ConcreteCategory.congr_hom (sectionsHomologyIso_naturality C n
    (homOfLE (leOfHom (homOfLE hgV ≫ i))).op) y
  have e₂ := map_op_map_op_apply (homologyPresheaf C n).presheaf (homOfLE hgV) i y'
  have hz : ConcreteCategory.hom (HomologicalComplex.homologyMap (secRestrict R K L
      (leOfHom (homOfLE hgV ≫ i))) n) y = 0 := by
    refine (Iso.hom_inv_id_apply (sectionsHomologyIso C n (op (basicOpen R g))) _).symm.trans ?_
    refine (congrArg (sectionsHomologyIso C n (op (basicOpen R g))).inv
      (e₁.trans (e₂.symm.trans ?_))).trans (map_zero _)
    refine (congrArg ((homologyPresheaf C n).presheaf.map (homOfLE hgV).op) hi).trans ?_
    exact (congrArg ((homologyPresheaf C n).presheaf.map (homOfLE hgV).op)
      (map_zero ((homologyPresheaf C n).presheaf.map i.op).hom)).trans (map_zero _)
  rw [hz, map_zero]

end AlgebraicGeometry.AffineExt
