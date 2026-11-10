module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recognising a homology isomorphism of complexes of sheaves of modules locally

Let `C` be a site, `O` a sheaf of rings on it, and `f` a morphism of cochain complexes of
`O`-modules. Whether `f` induces an isomorphism on the degree-`j` homology *sheaf* is a local
question: the homology sheaf is the sheafification of the presheaf-level homology, so `f` is a
homology isomorphism exactly when the presheaf-level homology map is locally bijective.

This file proves that equivalence and the local criterion that goes with it. The criterion is
the one the convergence argument for derived inverse limits uses, and it is shaped by the
hypotheses of the Olsson--Laszlo situation of Stacks 0D6R: there is a class `B` of objects
covering every object of the site, and each `V ∈ B` carries a cofinal system of coverings. Over
such a `V` one is allowed to replace the map by a locally bijective approximation, and only has
to check invertibility on the members of the distinguished coverings.

## Main definitions

* `Stacks.Cohomology.sheafificationComplexHomologyIso`: the sheafification of the presheaf-level
  homology of a complex of sheaves of modules is its homology.

## Main results

* `Stacks.Cohomology.mem_of_pullback_mem_preZeroHypercover`: transitivity of a topology against
  a covering family.
* `Stacks.Cohomology.CofinalCoveringSystem.exists_cov_arrows_mem`: a covering sieve is refined
  by a distinguished covering family of a cofinal system.
* `Stacks.Cohomology.isIso_homologyMap_iff_w`: a map of complexes of sheaves of modules is a
  homology isomorphism exactly when the presheaf-level homology map is locally bijective.
* `Stacks.Cohomology.isIso_presheaf_homologyMap_app_of_evaluation`: evaluation-level homology
  isomorphisms are the sections of the presheaf-level homology map.
* `Stacks.Cohomology.w_of_cofinal_local_isomorphisms`: the local criterion for a map of
  presheaves of abelian groups to be locally bijective.

## Implementation notes

Local bijectivity is `CategoryTheory.GrothendieckTopology.W` for presheaves of abelian groups,
which is the class of maps inverted by sheafification; the identification with pointwise local
injectivity and surjectivity is `GrothendieckTopology.W_iff_isLocallyBijective`. Working with
presheaves of abelian groups rather than of modules is what makes that identification available:
the module structure plays no part in the local criterion, and the comparison with modules is
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`.

Covering families are `PreZeroHypercover`, covering when the sieve they generate belongs to the
topology, matching `Stacks.Cohomology.CofinalCoveringSystem`.

## References

* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology

universe v u wRing wModule

/-- **A sieve is covering as soon as its pullback to the members of a covering family is.**
Transitivity of a Grothendieck topology, in the form in which a `PreZeroHypercover` supplies
the covering family.

Used in the local-to-global step of Stacks 0D6T. -/
@[sga "3 IV 4.2.3" "(C 5)", sga "4 II 1.1" "more general"]
lemma mem_of_pullback_mem_preZeroHypercover
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {V : C} (𝒰 : PreZeroHypercover V) (h𝒰 : 𝒰.sieve₀ ∈ J V)
    (R : Sieve V) (hR : ∀ i, R.pullback (𝒰.f i) ∈ J (𝒰.X i)) : R ∈ J V := by
  apply J.transitive h𝒰 R
  rintro W f ⟨Y, g, k, ⟨i⟩, rfl⟩
  simpa only [Sieve.pullback_comp] using J.pullback_stable g (hR i)

/-- **Every covering sieve is refined by a member of a cofinal covering system.** Concretely,
there is a distinguished covering family all of whose members belong to the sieve.

The cofinal systems are those of Stacks 0D6R, used in the proof of Stacks 0D6T. -/
lemma CofinalCoveringSystem.exists_cov_arrows_mem
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {V : C}
    (Cov : Stacks.Cohomology.CofinalCoveringSystem J V) (R : Sieve V) (hR : R ∈ J V) :
    ∃ 𝒰, Cov.cov 𝒰 ∧ ∀ i, R (𝒰.f i) := by
  have h : R.arrows.preZeroHypercover.sieve₀ = R := by
    change Sieve.generate R.arrows.preZeroHypercover.presieve₀ = R
    simp
  obtain ⟨𝒰, h𝒰, ⟨f⟩⟩ := Cov.cofinal R.arrows.preZeroHypercover (by rw [h]; exact hR)
  exact ⟨𝒰, h𝒰, fun i => h ▸ f.sieve₀_le_sieve₀ _ (𝒰.sieve₀_f i)⟩

/-- **Sheafifying the presheaf-level homology of a complex of sheaves of modules gives the
sheaf-level homology.** The forgetful functor to presheaves of modules is exact, so it commutes
with homology; sheafification is exact as well, and is a left inverse of the forgetful functor
on sheaves.

This is the identification that makes the conclusion of Stacks 0D6T a local statement. -/
noncomputable def sheafificationComplexHomologyIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] (j : ℤ) :
    ((SheafOfModules.forget.{wModule} R).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (PresheafOfModules.{wModule} R.obj) (.up ℤ) j) ⋙
      PresheafOfModules.sheafification (𝟙 R.obj) ≅
      HomologicalComplex.homologyFunctor (SheafOfModules.{wModule} R) (.up ℤ) j := by
  let F := SheafOfModules.forget.{wModule} R
  let a := PresheafOfModules.sheafification.{wModule} (𝟙 R.obj)
  let H := HomologicalComplex.homologyFunctor (SheafOfModules.{wModule} R) (.up ℤ) j
  let H' := HomologicalComplex.homologyFunctor (PresheafOfModules.{wModule} R.obj) (.up ℤ) j
  have : PreservesFiniteColimits a := by
    have := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits
    infer_instance
  have : a.Additive := by
    have : PreservesBinaryBiproducts a := preservesBinaryBiproducts_of_preservesBinaryCoproducts a
    exact Functor.additive_of_preservesBinaryBiproducts a
  let adj := PresheafOfModules.sheafificationAdjunction.{wModule} (𝟙 R.obj)
  have hcounit : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Adjunction.instIsIsoAppCounitOfFullOfFaithful adj M
  let e : F ⋙ a ≅ 𝟭 (SheafOfModules.{wModule} R) := @asIso _ _ _ _ adj.counit hcounit
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Stacks.Homology.exactHomologyIso a j).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)) H ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (.up ℤ)) H ≪≫
    Functor.leftUnitor H

/-- **A map of complexes of sheaves of modules is a homology isomorphism exactly when the
presheaf-level homology map is a local isomorphism.** The right-hand side is membership in the
class `J.W` of morphisms of presheaves inverted by sheafification, that is, local
bijectivity.

This is the reduction of Stacks 0D6T to a local question. -/
theorem isIso_homologyMap_iff_w
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    {M N : CochainComplex (SheafOfModules.{wModule} R) ℤ} (f : M ⟶ N) (j : ℤ) :
    IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map f) ↔
      J.W (((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) j ⋙
        PresheafOfModules.toPresheaf R.obj).map f) := by
  rw [← NatIso.isIso_map_iff (sheafificationComplexHomologyIso R j) f]
  exact Iff.symm (show
    (J.W.inverseImage (PresheafOfModules.toPresheaf R.obj)) _ ↔
    ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (𝟙 R.obj))) _ by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 R.obj)]
    rfl)

/-- **Evaluation-level homology isomorphisms are the sections of the presheaf-level homology
map.** The section over `U` of the presheaf of degree-`j` homology of the underlying complex of
presheaves of modules is the degree-`j` homology of the complex evaluated at `U`, because
evaluation is exact.

Used in the proof of Stacks 0D6T. -/
theorem isIso_presheaf_homologyMap_app_of_evaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    {M N : CochainComplex (SheafOfModules.{wModule} R) ℤ} (f : M ⟶ N) (j : ℤ) (U : Cᵒᵖ)
    (hf : IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map
      (((SheafOfModules.evaluation R U).mapHomologicalComplex (.up ℤ)).map f))) :
    IsIso ((((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℤ) j ⋙
      PresheafOfModules.toPresheaf R.obj).map f).app U) := by
  let e := Stacks.Homology.exactHomologyIso (PresheafOfModules.evaluation R.obj U) j
  have h := (NatIso.isIso_map_iff e
    (((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ)).map f)).1 hf
  have h' : IsIso (((HomologicalComplex.homologyFunctor _ (.up ℤ) j).map
    (((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ)).map f)).app U) := h
  exact Functor.map_isIso (forget₂ (ModuleCat.{wModule} (R.obj.obj U)) AddCommGrpCat) _

/-- A sieve is covering if, for a covering sieve `R`, it contains every member of each
distinguished covering whose members lie in `R`. -/
private theorem mem_of_forall_cov_arrows_mem
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {V : C}
    (Cov : Stacks.Cohomology.CofinalCoveringSystem J V) {R : Sieve V} (hR : R ∈ J V)
    (S : Sieve V) (h : ∀ 𝒰, Cov.cov 𝒰 → (∀ i, R (𝒰.f i)) → ∀ i, S (𝒰.f i)) : S ∈ J V := by
  obtain ⟨𝒰, h𝒰, he⟩ := CofinalCoveringSystem.exists_cov_arrows_mem Cov R hR
  apply J.superset_covering _ (Cov.isCover 𝒰 h𝒰)
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact h 𝒰 h𝒰 he

/-- **Local isomorphisms over a cofinal system of coverings of a locally covering class of
objects give a local isomorphism.** Let `B` be a class of objects covering every object of the
site, each `V ∈ B` carrying a cofinal system of coverings. A map `φ : P ⟶ Q` of presheaves of
abelian groups is locally bijective as soon as it factors, over each `V ∈ B`, as a map which is
an isomorphism on the members of every distinguished covering of `V` followed by a locally
bijective map.

Local injectivity and local surjectivity are each checked by covering an object by members of
`B` and then refining by a distinguished covering of each member, on which the first factor of
the factorisation is invertible.

The hypotheses are those available in the Olsson--Laszlo situation of Stacks 0D6R, and this is
the local criterion the proof of Stacks 0D6T applies. -/
theorem w_of_cofinal_local_isomorphisms
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    (B : Set C)
    (hB : ∀ U, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (Cov : ∀ V, B V → Stacks.Cohomology.CofinalCoveringSystem J V)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{wModule}} (φ : P ⟶ Q)
    (hφ : ∀ V (hV : B V), ∃ (R : Cᵒᵖ ⥤ AddCommGrpCat.{wModule})
      (ψ : P ⟶ R) (τ : R ⟶ Q), ψ ≫ τ = φ ∧ J.W τ ∧
      ∀ 𝒰, (Cov V hV).cov 𝒰 → ∀ i, IsIso (ψ.app (.op (𝒰.X i)))) : J.W φ := by
  apply (J.W_iff_isLocallyBijective φ).2
  constructor
  · constructor
    intro U x y hxy
    obtain ⟨𝒱, h𝒱, h𝒱B⟩ := hB U.unop
    apply mem_of_pullback_mem_preZeroHypercover J 𝒱 h𝒱
    intro k
    let V := 𝒱.X k
    let g := 𝒱.f k
    let x' := P.map g.op x
    let y' := P.map g.op y
    have hxy' : φ.app (.op V) x' = φ.app (.op V) y' := by
      dsimp [x', y']
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    obtain ⟨R, ψ, τ, hfac, hτ, hψ⟩ := hφ V (h𝒱B k)
    have := (J.W_iff_isLocallyBijective τ).1 hτ |>.1
    have heq : τ.app (.op V) (ψ.app (.op V) x') =
        τ.app (.op V) (ψ.app (.op V) y') := by
      change (ψ ≫ τ).app _ x' = (ψ ≫ τ).app _ y'
      simpa only [hfac] using hxy'
    refine mem_of_forall_cov_arrows_mem (Cov V (h𝒱B k))
      (Presheaf.equalizerSieve_mem J τ (ψ.app (.op V) x') (ψ.app (.op V) y') heq) _ ?_
    intro 𝒰 h𝒰 he i
    have := hψ 𝒰 h𝒰 i
    have hh := (ConcreteCategory.bijective_of_isIso (ψ.app (.op (𝒰.X i)))).1
    have hei : P.map (𝒰.f i).op x' = P.map (𝒰.f i).op y' :=
      hh ((ψ.naturality_apply (𝒰.f i).op x').trans
        ((he i).trans (ψ.naturality_apply (𝒰.f i).op y').symm))
    simpa [Presheaf.equalizerSieve, Sieve.pullback, x', y', g, V,
      ← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] using hei
  · constructor
    intro U y
    obtain ⟨𝒱, h𝒱, h𝒱B⟩ := hB U
    apply mem_of_pullback_mem_preZeroHypercover J 𝒱 h𝒱
    intro k
    rw [Presheaf.pullback_imageSieve]
    let V := 𝒱.X k
    let y' := Q.map (𝒱.f k).op y
    obtain ⟨R, ψ, τ, hfac, hτ, hψ⟩ := hφ V (h𝒱B k)
    have := (J.W_iff_isLocallyBijective τ).1 hτ |>.2
    refine mem_of_forall_cov_arrows_mem (Cov V (h𝒱B k)) (Presheaf.imageSieve_mem J τ y') _ ?_
    intro 𝒰 h𝒰 he i
    obtain ⟨z, hz⟩ := he i
    have := hψ 𝒰 h𝒰 i
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (ψ.app (.op (𝒰.X i)))).2 z
    refine ⟨x, ?_⟩
    rw [← hfac]
    change τ.app _ (ψ.app _ x) = _
    rw [hx]
    exact hz

end Stacks.Cohomology

end
