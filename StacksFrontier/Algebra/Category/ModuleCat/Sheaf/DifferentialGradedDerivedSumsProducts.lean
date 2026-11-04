module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeWeakCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryCoproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjectiveProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveResolution
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProductHomotopy
public import StacksFrontier.CategoryTheory.Localization.LocalObjectsFromResolutions

/-!
# Direct sums and products in the derived category of a sheaf of differential graded algebras

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The
derived category `D(A, d)` of right differential graded `A`-modules has arbitrary direct sums
and products; direct sums are computed by direct sums of right differential graded modules, and
products by products of *K-injective* right differential graded modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.HasKInjectiveResolutions`: every right differential
  graded module admits a quasi-isomorphism into a graded injective K-injective one.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasKInjectiveResolutions_of_detectingFamily`: a
  set-indexed family of monomorphisms of acyclic modules detecting the graded injective
  K-injective modules gives `HasKInjectiveResolutions`.
* `SheafOfModules.DifferentialGradedModule.bijective_toDerivedCategory_map_of_isKInjective`:
  the localization functor is bijective on homotopy classes of morphisms into a K-injective
  module, and `SheafOfModules.DifferentialGradedModule.bijective_toDerivedCategory_map` is the
  case of a graded injective K-injective module.
* `SheafOfModules.DifferentialGradedModule.derivedCategory_hasProducts` and
  `SheafOfModules.DifferentialGradedModule.derivedCategory_hasCoproducts`: `D(A, d)` has
  products and direct sums.
* `SheafOfModules.DifferentialGradedModule.isColimit_derivedCofanOfModules`: direct sums in
  `D(A, d)` are computed by direct sums of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.isLimit_derivedFanOfKInjectives`: products in
  `D(A, d)` are computed by products of K-injective right differential graded modules.

## Implementation notes

The module universe is `max u v w`, and the families are indexed by types in that universe.

## References

* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Tag 0FT9](https://stacks.math.columbia.edu/tag/0FT9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-! ### The hypotheses -/

/-- Every right differential graded module admits a quasi-isomorphism into a module which is
graded injective and K-injective. -/
def HasKInjectiveResolutions [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∀ M : DifferentialGradedModule.{u, v, max u v w} A,
    ∃ (I : DifferentialGradedModule.{u, v, max u v w} A) (f : M ⟶ I),
      QuasiIso f.toHomologicalComplex ∧ GradedInjective I ∧ IsKInjective I

section Resolutions

variable [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- A set-indexed family of monomorphisms of acyclic right differential graded modules detecting
the graded injective K-injective modules gives a quasi-isomorphism of every module into one of
them. -/
theorem hasKInjectiveResolutions_of_detectingFamily
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {Idx : Type max u v w}
    (Ms Ms' : Idx → DifferentialGradedModule.{u, v, max u v w} A) (i : ∀ r, Ms r ⟶ Ms' r)
    (hi : ∀ r, Mono (i r)) (hMs : ∀ r, (Ms r).complex.Acyclic)
    (hMs' : ∀ r, (Ms' r).complex.Acyclic)
    (hdetect : ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
      (∀ (r : Idx) (f : Ms r ⟶ I), ∃ g : Ms' r ⟶ I, i r ≫ g = f) →
        IsKInjective I ∧ GradedInjective I) :
    HasKInjectiveResolutions.{u, v, w} A := fun M =>
  exists_quasiIso_gradedInjective_isKInjective.{u, v, w} A Ms Ms' i hi hMs hMs' hdetect M

end Resolutions

section Derived

variable [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-! ### Morphisms of the derived category into a K-injective module -/

/-- The K-injective modules are objects local for the quasi-isomorphisms, and every object of
the homotopy category admits a quasi-isomorphism into one of them. -/
theorem localResolutions (hres : HasKInjectiveResolutions.{u, v, w} A) :
    (quasiIsomorphisms.{u, v, max u v w} A).LocalResolutions (fun Z => IsKInjective Z.as) where
  bijective_comp {Z₁ Z₂} s hs I hI := by
    obtain ⟨b, rfl⟩ := (HomotopyCategory.quotient A).map_surjective s
    have hbq : QuasiIso b.toHomologicalComplex := (quasiIsomorphisms_quotient_map_iff b).1 hs
    refine ⟨fun g g' hgg' => ?_, fun a => ?_⟩
    · obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient A).map_surjective g
      obtain ⟨c', rfl⟩ := (HomotopyCategory.quotient A).map_surjective g'
      refine (HomotopyCategory.quotient_map_eq_iff c c').2
        (hI.homotopic_of_comp_homotopic hbq c c'
          ((HomotopyCategory.quotient_map_eq_iff _ _).1 ?_))
      simpa only [Functor.map_comp] using hgg'
    · obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient A).map_surjective a
      obtain ⟨c, hcc⟩ := hI.exists_homotopic_lift_of_quasiIso a b hbq
      refine ⟨(HomotopyCategory.quotient A).map c, ?_⟩
      change (HomotopyCategory.quotient A).map b ≫ (HomotopyCategory.quotient A).map c = _
      rw [← Functor.map_comp]
      exact (HomotopyCategory.quotient_map_eq_iff _ _).2 hcc
  exists_resolution Z := by
    obtain ⟨I, f, hf, hGI, hKI⟩ := hres Z.as
    exact ⟨(HomotopyCategory.quotient A).obj I, (HomotopyCategory.quotient A).map f,
      (quasiIsomorphisms_quotient_map_iff f).2 hf, hKI⟩

/-- The localization functor from the homotopy category to the derived category is bijective on
homotopy classes of morphisms into a K-injective right differential graded module. -/
theorem bijective_toDerivedCategory_map_of_isKInjective
    (hres : HasKInjectiveResolutions.{u, v, w} A) (Z : HomotopyCategory.{u, v, max u v w} A)
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hKI : IsKInjective I) :
    Function.Bijective (fun f : Z ⟶ (HomotopyCategory.quotient A).obj I =>
      (toDerivedCategory.{u, v, max u v w} A).map f) :=
  (localResolutions hres).bijective_Q_map Z hKI

/-- The localization functor from the homotopy category to the
derived category is bijective on homotopy classes of morphisms into a graded injective
K-injective right differential graded module. -/
theorem bijective_toDerivedCategory_map (hres : HasKInjectiveResolutions.{u, v, w} A)
    (Z : HomotopyCategory.{u, v, max u v w} A)
    {I : DifferentialGradedModule.{u, v, max u v w} A} (hKI : IsKInjective I)
    (_hGI : GradedInjective I) :
    Function.Bijective (fun f : Z ⟶ (HomotopyCategory.quotient A).obj I =>
      (toDerivedCategory.{u, v, max u v w} A).map f) :=
  bijective_toDerivedCategory_map_of_isKInjective hres Z hKI

/-! ### Products -/

/-- The image of a product of right differential graded modules, with its canonical
projections, is a product in the homotopy category. -/
def isLimitQuotientFan {T : Type max u v w}
    (I : T → DifferentialGradedModule.{u, v, max u v w} A) :
    IsLimit (Fan.mk ((HomotopyCategory.quotient A).obj (∏ᶜ I))
      (fun t => (HomotopyCategory.quotient A).map (Pi.π I t))) := by
  classical
  refine Fan.IsLimit.mk _
    (fun s => (HomotopyCategory.quotient A).map
      (Pi.lift fun t => (HomotopyCategory.quotient A).preimage (s.proj t))) ?_ ?_
  · intro s t
    change (HomotopyCategory.quotient A).map
        (Pi.lift fun j => (HomotopyCategory.quotient A).preimage (s.proj j)) ≫
      (HomotopyCategory.quotient A).map (Pi.π I t) = s.proj t
    rw [← Functor.map_comp, Pi.lift_π, Functor.map_preimage]
  · intro s m hm
    rw [fan_mk_proj] at hm
    have hpre : (HomotopyCategory.quotient A).map
        ((HomotopyCategory.quotient A).preimage m) = m := Functor.map_preimage _ _
    rw [← hpre]
    refine (HomotopyCategory.quotient_map_eq_iff ((HomotopyCategory.quotient A).preimage m)
      (Pi.lift fun t => (HomotopyCategory.quotient A).preimage (s.proj t))).2
      ⟨homotopyIntoProduct I (∏ᶜ I) (Pi.π I) (productIsProduct I) fun t => ?_⟩
    refine (HomotopyCategory.quotient_map_eq_iff _ _).1 ?_
    rw [Pi.lift_π, Functor.map_preimage, Functor.map_comp, hpre]
    exact hm t

/-- For a family of K-injective right differential graded modules, the image of their product,
with its canonical projections, is a product in the derived category. -/
def isLimit_derivedFanOfKInjectives (hres : HasKInjectiveResolutions.{u, v, w} A)
    {T : Type max u v w} (I : T → DifferentialGradedModule.{u, v, max u v w} A)
    (hKI : ∀ t, IsKInjective (I t)) :
    IsLimit (Fan.mk
      ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∏ᶜ I))
      (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
        (Pi.π I t))) :=
  (localResolutions hres).isLimitMapFan hKI (isKInjective_pi I hKI)
    (fun t => (HomotopyCategory.quotient A).map (Pi.π I t)) (isLimitQuotientFan I)

/-- The derived category of a sheaf of differential graded algebras has arbitrary products. -/
theorem derivedCategory_hasProducts (hres : HasKInjectiveResolutions.{u, v, w} A) :
    HasProducts.{max u v w} (derivedCategory.{u, v, max u v w} A) := by
  classical
  intro T
  refine ⟨fun F => ?_⟩
  let H := localResolutions hres
  let I : T → DifferentialGradedModule.{u, v, max u v w} A := fun t => (H.model (F.obj ⟨t⟩)).as
  have hKI : ∀ t, IsKInjective (I t) := fun t => H.prop_model (F.obj ⟨t⟩)
  have : HasProduct (fun t =>
      (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (I t)) :=
    ⟨⟨_, isLimit_derivedFanOfKInjectives hres I hKI⟩⟩
  exact hasLimit_of_iso (F := Discrete.functor fun t =>
      (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (I t))
    (Discrete.natIso fun t => H.modelIso (F.obj t))

/-! ### Direct sums -/

/-- The derived category of a sheaf of differential graded algebras has arbitrary direct
sums. -/
theorem derivedCategory_hasCoproducts (hres : HasKInjectiveResolutions.{u, v, w} A)
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] :
    HasCoproducts.{max u v w} (derivedCategory.{u, v, max u v w} A) := by
  classical
  intro T
  refine ⟨fun F => ?_⟩
  let H := localResolutions hres
  let Z : T → HomotopyCategory.{u, v, max u v w} A := fun t =>
    (toDerivedCategory.{u, v, max u v w} A).objPreimage (F.obj ⟨t⟩)
  have : HasCoproduct (fun t => (toDerivedCategory.{u, v, max u v w} A).obj (Z t)) :=
    ⟨⟨_, H.isColimitMapCofan (Sigma.ι Z) (coproductIsCoproduct Z)⟩⟩
  exact hasColimit_of_iso
    (F := Discrete.functor fun t => (toDerivedCategory.{u, v, max u v w} A).obj (Z t))
    (Discrete.natIso fun t =>
      ((toDerivedCategory.{u, v, max u v w} A).objObjPreimageIso (F.obj t)).symm)

/-- The image of a direct sum of right differential graded modules, with its canonical
inclusions, is a direct sum in the homotopy category. -/
def isColimitQuotientCofan
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] {T : Type max u v w}
    (M : T → DifferentialGradedModule.{u, v, max u v w} A) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient A).obj (∐ M))
      (fun t => (HomotopyCategory.quotient A).map (Sigma.ι M t))) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun s => (HomotopyCategory.quotient A).map
      (Sigma.desc fun t => (HomotopyCategory.quotient A).preimage (s.inj t))) ?_ ?_
  · intro s t
    change (HomotopyCategory.quotient A).map (Sigma.ι M t) ≫
      (HomotopyCategory.quotient A).map
        (Sigma.desc fun j => (HomotopyCategory.quotient A).preimage (s.inj j)) = s.inj t
    rw [← Functor.map_comp, Sigma.ι_desc, Functor.map_preimage]
  · intro s m hm
    rw [cofan_mk_inj] at hm
    have hpre : (HomotopyCategory.quotient A).map
        ((HomotopyCategory.quotient A).preimage m) = m := Functor.map_preimage _ _
    rw [← hpre]
    refine (HomotopyCategory.quotient_map_eq_iff ((HomotopyCategory.quotient A).preimage m)
      (Sigma.desc fun t => (HomotopyCategory.quotient A).preimage (s.inj t))).2
      ⟨coproductHomotopy _ _ fun t => ?_⟩
    refine (HomotopyCategory.quotient_map_eq_iff _ _).1 ?_
    rw [Sigma.ι_desc, Functor.map_preimage, Functor.map_comp, hpre]
    exact hm t

/-- The image in the derived category of a direct sum of right differential graded modules,
with its canonical inclusions, is a direct sum. -/
def isColimit_derivedCofanOfModules (hres : HasKInjectiveResolutions.{u, v, w} A)
    [HasWeakSheafify X.J AddCommGrpCat.{max u v w}] {T : Type max u v w}
    (M : T → DifferentialGradedModule.{u, v, max u v w} A) :
    IsColimit (Cofan.mk
      ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∐ M))
      (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
        (Sigma.ι M t))) :=
  (localResolutions hres).isColimitMapCofan
    (fun t => (HomotopyCategory.quotient A).map (Sigma.ι M t)) (isColimitQuotientCofan M)

end Derived

end SheafOfModules.DifferentialGradedModule

end
