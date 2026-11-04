module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.AdicCompletionFunctorSingleIso
public import StacksFrontier.Homology.DerivedComplete.AdicCompletionUnitSingle
public import StacksFrontier.Homology.DerivedComplete.CechCompletion
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion

/-!
# The derived completion unit is surjective modulo the ideal on cohomology

Let `I` be an ideal of a Noetherian ring `A` and let `X` be an object of `D(A)` all of whose
cohomology modules are finite. The derived completion unit `η_X : X ⟶ X^∧` induces a map

`H^0(X) ⟶ H^0(X^∧)`

whose image, together with `I · H^0(X^∧)`, is all of `H^0(X^∧)`: the unit is **surjective modulo
`I`** on degree-zero cohomology. Equivalently, the cokernel of `H^0(η_X)` is `I`-divisible.

This is the one statement the general case of [Stacks, Tag 0EFX] still waited on. Stacks 0A06
identifies `H^0(X^∧)` with the ordinary `I`-adic completion of `H^0(X)`, for which the statement
is immediate from `AdicCompletion.of` being surjective modulo `I`; but that identification is
available in this library only as an unpinned isomorphism of modules
(`AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion`), with no compatibility
with the unit, and a statement about the image of a map cannot be transported across an
isomorphism that is not known to commute with it.

The proof below therefore never transports anything across Stacks 0A06; it uses that theorem only
to see that a cohomology module **vanishes**, which no compatibility is needed for. The statement
itself is reduced to the case of a finite module placed in degree zero, where unit-compatibility
*is* available — `Stacks.Algebraization.exists_iso_adicCompletionFunctor_single_normalized`
normalizes the identification of `M[0]^∧` so that its composite with the unit is the ordinary
completion map `M ⟶ AdicCompletion I M`.

The reduction is in two steps, both of the same shape: a morphism `a : P ⟶ X` whose completion is
surjective on `H^0` carries the statement from `P` to `X`, because the unit is natural, so the
image of `H^0(η_P)` lands in the image of `H^0(η_X)`.

* First `X` is replaced by `τ^{≤0}X`. The cone of `τ^{≤0}X ⟶ X` has vanishing cohomology in
  degrees `≤ 0` and finite cohomology in all degrees, so Stacks 0A06 makes `H^0` of *its*
  completion vanish, and the long exact sequence gives the surjectivity.
* Then a finite free module `A^n` surjecting onto `H^0(τ^{≤0}X)` is lifted to a morphism
  `A^n[0] ⟶ τ^{≤0}X` of `D(A)`. On a complex representing `τ^{≤0}X` the lift is explicit: a
  generating family of `H^0` lifts to cycles because `A^n` is projective, and a map into the
  degree-zero cycles is a map of complexes out of a single complex. Since `τ^{≤0}X` has no
  cohomology above degree zero, [Stacks, Tag 0AAJ] — derived completion preserves an upper
  cohomological bound and is surjective on boundary cohomology — makes the completion of that
  morphism surjective on `H^0`.

## Main results

* `Stacks.Algebraization.range_adicCompletion_of_sup_smul_eq_top` — the ordinary completion map
  `M ⟶ AdicCompletion I M` is surjective modulo `I`, for a finitely generated `I`.
* `Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_finite` — [Stacks, Tag 0EEU]
  for a finite module placed in degree zero.
* `Stacks.Algebraization.exists_finiteFree_single_map_epi_homologyMap` — a finite free module in
  degree zero mapping onto the degree-zero cohomology of an arbitrary object of `D(A)`.
* `Stacks.Algebraization.range_homologyMap_adicCompletionUnit_sup_smul_eq_top` — the main
  statement, for the reflection model of derived completion.
* `Stacks.Algebraization.range_homologyMap_derivedCompletionUnit_sup_smul_eq_top` — the same for
  the Čech model `DerivedCompletion.derivedCompletionFunctor`, which is the model local duality
  is phrased over.

## References

* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0AAJ](https://stacks.math.columbia.edu/tag/0AAJ)
* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u v

namespace Stacks.Algebraization

/-! ### The ordinary completion map is surjective modulo the ideal -/

/-- **The ordinary `I`-adic completion map is surjective modulo `I`.** For a finitely generated
ideal `I` and any module `M`, the image of `AdicCompletion.of I M` together with
`I · AdicCompletion I M` is all of `AdicCompletion I M`.

Indeed `AdicCompletion.pow_smul_top_eq_ker_eval` identifies `I · AdicCompletion I M` with the
kernel of the evaluation `AdicCompletion I M ⟶ M ⧸ IM`, and that evaluation composed with
`AdicCompletion.of I M` is the quotient map `M ⟶ M ⧸ IM`, which is surjective. -/
theorem range_adicCompletion_of_sup_smul_eq_top {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (M : Type v) [AddCommGroup M] [Module A M] :
    LinearMap.range (AdicCompletion.of I M) ⊔
      I • (⊤ : Submodule A (AdicCompletion I M)) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I ^ 1 • (⊤ : Submodule A M))
    (AdicCompletion.eval I M 1 x)
  have hker : AdicCompletion.eval I M 1 (x - AdicCompletion.of I M m) = 0 := by
    rw [map_sub, AdicCompletion.eval_of, hm, sub_self]
  have hmem : x - AdicCompletion.of I M m ∈ I • (⊤ : Submodule A (AdicCompletion I M)) := by
    rw [show (I • (⊤ : Submodule A (AdicCompletion I M))) = I ^ 1 • ⊤ by rw [pow_one],
      AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact hker
  exact Submodule.mem_sup.2 ⟨AdicCompletion.of I M m, ⟨m, rfl⟩,
    x - AdicCompletion.of I M m, hmem, by abel⟩

/-- If `q ∘ G = F ∘ p` with `q` surjective, surjectivity of `G` modulo `I` gives that of `F`. -/
private theorem range_sup_smul_eq_top_of_comp_eq {A : Type*} [CommRing A] (I : Ideal A)
    {M M' N N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (F : M →ₗ[A] N) (G : M' →ₗ[A] N') (p : M' →ₗ[A] M) (q : N' →ₗ[A] N)
    (hq : Function.Surjective q) (h : ∀ m, q (G m) = F (p m))
    (hG : LinearMap.range G ⊔ I • (⊤ : Submodule A N') = ⊤) :
    LinearMap.range F ⊔ I • (⊤ : Submodule A N) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨z, rfl⟩ := hq x
  obtain ⟨y₁, ⟨m, rfl⟩, y₂, hy₂, rfl⟩ :=
    Submodule.mem_sup.1 (hG.ge (Submodule.mem_top (x := z)))
  rw [map_add, h]
  exact Submodule.add_mem_sup ⟨p m, rfl⟩ (Submodule.smul_top_le_comap_smul_top I q hy₂)

/-! ### Derived completion of a finite module in degree zero -/

/-- **[Stacks, Tag 0EEU] for a finite module in degree zero.** Over a Noetherian ring the derived
`I`-adic completion of a finite module placed in degree zero is its ordinary `I`-adic completion
placed in degree zero. This is the tensor clause of
`Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_tensor_flat` read at the flat
module `A`, transported along `M ⊗[A] A ≅ M`. -/
theorem nonempty_iso_adicCompletionFunctor_single_finite
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I M))) := by
  set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 with hS
  obtain ⟨e₀⟩ := nonempty_iso_adicCompletionFunctor_single_tensor_flat A I hI M A
  let r : TensorProduct A M A ≃ₗ[A] M := TensorProduct.rid A M
  exact ⟨((adicCompletionFunctor A I hI).mapIso (S.mapIso r.toModuleIso)).symm ≪≫ e₀ ≪≫
    S.mapIso ((AdicCompletion.congr I r).restrictScalars A).toModuleIso⟩

/-- **The main statement for a finite module in degree zero.** The unit of derived `I`-adic
completion at `M[0]`, read on degree-zero cohomology, is surjective modulo `I`.

The identification of `H^0(M[0]^∧)` with `AdicCompletion I M` furnished by
`Stacks.Algebraization.nonempty_iso_adicCompletionFunctor_single_finite` is normalized by
`Stacks.Algebraization.exists_iso_adicCompletionFunctor_single_normalized` so that its composite
with the unit is the ordinary completion map; the statement is then
`Stacks.Algebraization.range_adicCompletion_of_sup_smul_eq_top`. -/
theorem range_homologyMap_adicCompletionUnit_single_sup_smul_eq_top
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((adicCompletionUnit A I hI).app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M)))).hom ⊔
        I • (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((adicCompletionFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M))))) = ⊤ := by
  have : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 with hS
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH
  set ηM := (adicCompletionUnit A I hI).app (S.obj (ModuleCat.of A M)) with hηM
  obtain ⟨e⟩ := nonempty_iso_adicCompletionFunctor_single_finite A I hI M
  obtain ⟨e', he'⟩ := exists_iso_adicCompletionFunctor_single_normalized I hI
    (ModuleCat.of A M) (ModuleCat.of A (AdicCompletion I M)) e
  set sIso := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0 with hsIso
  set u : H.obj ((adicCompletionFunctor A I hI).obj (S.obj (ModuleCat.of A M))) ≅
      ModuleCat.of A (AdicCompletion I M) :=
    H.mapIso e' ≪≫ sIso.app (ModuleCat.of A (AdicCompletion I M)) with hu
  have hkey : H.map ηM ≫ u.hom =
      (sIso.app (ModuleCat.of A M)).hom ≫ ModuleCat.ofHom (AdicCompletion.of I M) := by
    rw [hu]
    show H.map _ ≫ H.map e'.hom ≫ (sIso.app _).hom = _
    rw [← Category.assoc, ← H.map_comp, hηM, he']
    exact sIso.hom.naturality (ModuleCat.ofHom (AdicCompletion.of I M))
  have hinv : ModuleCat.ofHom (AdicCompletion.of I M) ≫ u.inv =
      (sIso.app (ModuleCat.of A M)).inv ≫ H.map ηM := by
    rw [Iso.comp_inv_eq, Category.assoc, hkey, Iso.inv_hom_id_assoc]
  exact range_sup_smul_eq_top_of_comp_eq I _ _ (sIso.app (ModuleCat.of A M)).inv.hom u.inv.hom
    ((ModuleCat.epi_iff_surjective u.inv).1 inferInstance)
    (fun m => by simpa using ConcreteCategory.congr_hom hinv m)
    (range_adicCompletion_of_sup_smul_eq_top I hI M)

/-! ### A finite free module onto the degree-zero cohomology -/

/-- **A finite free module in degree zero mapping onto `H^0`.** For any object `X` of `D(A)` with
`H^0(X)` finite there is a morphism `A^n[0] ⟶ X` of `D(A)` which is surjective on degree-zero
cohomology.

On a cochain complex `W` representing `X` the morphism is explicit. A finite generating family of
`H^0(W)` is a map `A^n ⟶ H^0(W)`; since `A^n` is projective and `W.cycles 0 ⟶ W.homology 0` is
epi, it lifts to a map `A^n ⟶ W.cycles 0`, and a map into the degree-zero cycles is exactly a
map of complexes from `A^n` placed in degree zero (`HomologicalComplex.mkHomFromSingle`). Its
effect on `H^0` is the chosen generating family, by
`CechCompletion.singleObjHomologySelfIso_inv_comp_homologyMap_mkHomFromSingle`. -/
theorem exists_finiteFree_single_map_epi_homologyMap
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{u} A))
    (hfin : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X)) :
    ∃ (n : ℕ) (a : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Fin n → A)) ⟶ X),
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map a) := by
  obtain ⟨W, ⟨eW⟩⟩ : ∃ W : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj W ≅ X) :=
    ⟨DerivedCategory.Q.objPreimage X, ⟨DerivedCategory.Q.objObjPreimageIso X⟩⟩
  have hfinW : Module.Finite A (W.homology 0) := by
    have := hfin
    exact Module.Finite.equiv
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app W).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso eW).toLinearEquiv.symm
  obtain ⟨n, sMor, hepis⟩ : ∃ (n : ℕ) (sMor : ModuleCat.of A (Fin n → A) ⟶ W.homology 0),
      Epi sMor := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' A (W.homology 0)
    exact ⟨n, ModuleCat.ofHom s, (ModuleCat.epi_iff_surjective _).2 hs⟩
  refine ⟨n, ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
      (ModuleCat.of A (Fin n → A))).hom ≫
    DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle
      (Projective.factorThru sMor (W.homologyπ 0) ≫ W.iCycles 0)
      (by intro i _hi; simp [Category.assoc])) ≫ eW.hom, ?_⟩
  set b := Projective.factorThru sMor (W.homologyπ 0) with hb
  set g := HomologicalComplex.mkHomFromSingle (b ≫ W.iCycles 0)
    (by intro i _hi; simp [Category.assoc]) with hg
  have hcyc := CechCompletion.singleObjHomologySelfIso_inv_comp_homologyMap_mkHomFromSingle W
    (ModuleCat.of A (Fin n → A)) 0 b
  change (singleObjHomologySelfIso (ComplexShape.up ℤ) 0
    (ModuleCat.of A (Fin n → A))).inv ≫ homologyMap g 0 = b ≫ W.homologyπ 0 at hcyc
  have hge : Epi (homologyMap g 0) := by
    have h1 : Epi ((singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of A (Fin n → A))).inv ≫ homologyMap g 0) := by
      rw [hcyc, hb, Projective.factorThru_comp]
      exact hepis
    exact epi_of_epi (singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of A (Fin n → A))).inv _
  have hQ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (DerivedCategory.Q.map g)) := by
    have h2 : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (DerivedCategory.Q.map g) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app W) := by
      rw [show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          (DerivedCategory.Q.map g) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app W =
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A (Fin n → A))) ≫ homologyMap g 0 from
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.naturality g]
      exact @epi_comp _ _ _ _ _ _ inferInstance _ hge
    have h3 : Epi (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (DerivedCategory.Q.map g) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).hom.app W) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).inv.app W) :=
      epi_comp _ _
    rw [Category.assoc, Iso.hom_inv_id_app] at h3
    simpa using h3
  rw [Functor.map_comp, Functor.map_comp]
  exact epi_comp _ _

/-! ### Replacing an object by its truncation -/

/-- **Every object of `D(A)` receives a morphism from an object with no cohomology above degree
zero which is an isomorphism on cohomology in degrees `≤ 0`.** This is the canonical truncation
`τ^{≤0}X ⟶ X`, formed on a cochain complex representing `X`. -/
theorem exists_isLE_isIso_homologyMap
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{u} A)) :
    ∃ (K₀ : DerivedCategory (ModuleCat.{u} A)) (φ : K₀ ⟶ X), K₀.IsLE 0 ∧
      ∀ i : ℤ, i ≤ 0 →
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ) := by
  obtain ⟨W, ⟨eW⟩⟩ : ∃ W : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj W ≅ X) :=
    ⟨DerivedCategory.Q.objPreimage X, ⟨DerivedCategory.Q.objObjPreimageIso X⟩⟩
  refine ⟨DerivedCategory.Q.obj (W.truncLE 0),
    DerivedCategory.Q.map (W.ιTruncLE 0) ≫ eW.hom, inferInstance, fun i hi => ?_⟩
  have := AdicCompletionCohomology.isIso_homologyFunctor_map_ιTruncLE W 0 i hi
  rw [Functor.map_comp]
  infer_instance

/-- **Derived completion is surjective on `H^0` along a truncation morphism.** Let `X` have
finite cohomology modules, let `K₀` have no cohomology above degree zero and let `φ : K₀ ⟶ X` be
an isomorphism on cohomology in all degrees `≤ 0`. Then `H^0(φ^∧)` is surjective.

The cone of `φ` has vanishing cohomology in every degree `≤ 0` — in degree `i ≤ -1` because `φ`
is an isomorphism in degrees `i` and `i + 1`, and in degree `0` because `φ` is an isomorphism
there while `K₀` has no cohomology in degree `1`, so that `H^1(φ)` is a monomorphism out of a
zero object. Its cohomology is finite in every degree: it vanishes below degree `1`, and above it
is a quotient of the cohomology of `X` because the connecting map lands in the vanishing
cohomology of `K₀`. So [Stacks, Tag 0A06] applies to the cone and makes `H^0` of its completion
the adic completion of a zero module, hence zero; the long exact sequence of the completed
triangle then gives the surjectivity. -/
theorem epi_homologyMap_adicCompletionFunctor_map_of_isLE
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    {X K₀ : DerivedCategory (ModuleCat.{u} A)} (φ : K₀ ⟶ X) [K₀.IsLE 0]
    (hX : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X))
    (hiso : ∀ i : ℤ, i ≤ 0 →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ)) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionFunctor A I hI).map φ)) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  subst hf
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K ↦ IsDerivedComplete (Ideal.span (Set.range f)) K
  let C : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory :=
    Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI
  let adj : C ⊣ P.ι := adicCompletionAdjunction A (Ideal.span (Set.range f)) hI
  have : P.IsTriangulated :=
    CompletionAdjunction.isDerivedComplete_isTriangulated A (Ideal.span (Set.range f))
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : C.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨Z, p, q, hT⟩ := distinguished_cocone_triangle φ
  have hZzero : ∀ i : ℤ, i ≤ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (Triangle.mk φ p q).obj₃) := by
    intro i hi
    have := hiso i hi
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (Triangle.mk φ p q).mor₁) :=
      inferInstanceAs (Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ))
    have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + 1)).map
        (Triangle.mk φ p q).mor₁) := by
      by_cases h : i + 1 ≤ 0
      · have := hiso (i + 1) h
        exact inferInstanceAs (Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A)
          (i + 1)).map φ))
      · exact (DerivedCategory.isZero_of_isLE K₀ 0 (i + 1) (by omega)).mono _
    exact CompletionAdjunction.isZero_homologyFunctor_obj₃_of_epi_of_mono (Triangle.mk φ p q) hT i
  have hZfin : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (Triangle.mk φ p q).obj₃) := by
    intro n
    by_cases hn : n ≤ 0
    · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
          (Triangle.mk φ p q).obj₃) :=
        ModuleCat.isZero_iff_subsingleton.mp (hZzero n hn)
      infer_instance
    · have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (Triangle.mk φ p q).mor₂) :=
        (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
          (Triangle.mk φ p q) hT n (n + 1) rfl).mpr
          ((DerivedCategory.isZero_of_isLE K₀ 0 (n + 1) (by omega)).eq_zero_of_tgt _)
      have : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (Triangle.mk φ p q).obj₂) := hX n
      exact Module.Finite.of_surjective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (Triangle.mk φ p q).mor₂).hom ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have h0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((C ⋙ P.ι).obj (Triangle.mk φ p q).obj₃)) := by
    obtain ⟨e⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
      A (Ideal.span (Set.range f)) (Triangle.mk φ p q).obj₃ hZfin C adj 0
    refine IsZero.of_iso ?_ e
    rw [ModuleCat.isZero_iff_subsingleton]
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (Triangle.mk φ p q).obj₃) :=
      ModuleCat.isZero_iff_subsingleton.mp (hZzero 0 le_rfl)
    exact ⟨fun x y => Subtype.ext (funext fun k => Subsingleton.elim _ _)⟩
  have hFT : (C ⋙ P.ι).mapTriangle.obj (Triangle.mk φ p q) ∈ distTriang _ :=
    (C ⋙ P.ι).map_distinguished (Triangle.mk φ p q) hT
  exact CompletionAdjunction.epi_homologyFunctor_map_mor₁_of_isZero
    ((C ⋙ P.ι).mapTriangle.obj (Triangle.mk φ p q)) hFT 0 h0

/-! ### Surjectivity on `H^0` for the completion of a morphism from a bounded-above object -/

/-- **[Stacks, Tag 0AAJ] for the named derived completion endofunctor.** Derived completion
preserves isomorphisms in positive cohomological degrees and is surjective on degree-zero
cohomology: if `H^i(a)` is invertible for all `i ≥ 1` and `H^0(a)` is an epimorphism, then
`H^0(a^∧)` is an epimorphism. -/
theorem epi_homologyMap_adicCompletionFunctor_map
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    {P X : DerivedCategory (ModuleCat.{u} A)} (a : P ⟶ X)
    (h1 : ∀ i : ℤ, 1 ≤ i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map a))
    (h2 : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map a)) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionFunctor A I hI).map a)) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  subst hf
  exact ((CompletionAdjunction.derivedCompletion_finiteCohomologicalDimension A f
    (Dualizing.derivedCompletion A (Ideal.span (Set.range f)) hI)
    (adicCompletionAdjunction A (Ideal.span (Set.range f)) hI) a).1 ⟨h1, h2⟩).2

/-! ### The main statement -/

/-- **The derived completion unit is surjective modulo `I` on degree-zero cohomology.** Let `I`
be a finitely generated ideal of a Noetherian ring `A` and let `X` be an object of `D(A)` all of
whose cohomology modules are finite. Then the image of

`H^0(X) ⟶ H^0(X^∧)`

together with `I · H^0(X^∧)` is all of `H^0(X^∧)`.

This is the statement [Stacks, Tag 0EFX] needs in order to read a vanishing of Ext modules back
as a vanishing of local cohomology: it says precisely that the cokernel of the local duality map
is `I`-divisible, and at `I = 𝔪` that is what makes the Matlis detection lemma
`Stacks.LocalCohomology.eq_zero_of_forall_mem_comp_eq_zero_of_sup_eq_top` applicable.

*Proof.* The statement is transported along two morphisms whose completions are surjective on
`H^0`, the unit being natural so that the image of `H^0(η)` at the source lands in the image of
`H^0(η)` at the target: first the truncation `τ^{≤0}X ⟶ X`
(`Stacks.Algebraization.epi_homologyMap_adicCompletionFunctor_map_of_isLE`), then a morphism
`A^n[0] ⟶ τ^{≤0}X` surjective on `H^0`
(`Stacks.Algebraization.exists_finiteFree_single_map_epi_homologyMap`), whose completion is
surjective on
`H^0` by [Stacks, Tag 0AAJ] because `τ^{≤0}X` has no cohomology above degree zero. At `A^n[0]`
the statement is
`Stacks.Algebraization.range_homologyMap_adicCompletionUnit_single_sup_smul_eq_top`. -/
theorem range_homologyMap_adicCompletionUnit_sup_smul_eq_top
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X)) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((adicCompletionUnit A I hI).app X)).hom ⊔
        I • (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((adicCompletionFunctor A I hI).obj X))) = ⊤ := by
  classical
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH
  obtain ⟨K₀, φ, hle, hisoφ⟩ := exists_isLE_isIso_homologyMap A X
  have := hle
  have := hisoφ 0 le_rfl
  have hfin₀ : Module.Finite A (H.obj K₀) := by
    have := hX 0
    exact Module.Finite.equiv (asIso (H.map φ)).toLinearEquiv.symm
  obtain ⟨n, a', ha'⟩ := exists_finiteFree_single_map_epi_homologyMap A K₀ hfin₀
  -- the composite morphism from a finite free module in degree zero
  have hIso₁ : ∀ i : ℤ, 1 ≤ i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map a') := by
    intro i hi
    exact (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Fin n → A))) 0 i (by omega)).isIso
      (DerivedCategory.isZero_of_isLE K₀ 0 i (by omega)) _
  have hepi₁ : Epi (H.map ((adicCompletionFunctor A I hI).map a')) :=
    epi_homologyMap_adicCompletionFunctor_map A I hI a' hIso₁ ha'
  have hepi₂ : Epi (H.map ((adicCompletionFunctor A I hI).map φ)) :=
    epi_homologyMap_adicCompletionFunctor_map_of_isLE A I hI φ hX hisoφ
  have hepi : Epi (H.map ((adicCompletionFunctor A I hI).map (a' ≫ φ))) := by
    rw [Functor.map_comp, Functor.map_comp]
    exact @epi_comp _ _ _ _ _ _ hepi₁ _ hepi₂
  -- naturality of the unit
  have hnat := (adicCompletionUnit A I hI).naturality (a' ≫ φ)
  simp only [Functor.id_map] at hnat
  have hcomm := congrArg H.map hnat
  rw [H.map_comp, H.map_comp] at hcomm
  exact range_sup_smul_eq_top_of_comp_eq I _ _ (H.map (a' ≫ φ)).hom
    (H.map ((adicCompletionFunctor A I hI).map (a' ≫ φ))).hom
    ((ModuleCat.epi_iff_surjective _).1 hepi)
    (fun m => by simpa using (ConcreteCategory.congr_hom hcomm m).symm)
    (range_homologyMap_adicCompletionUnit_single_sup_smul_eq_top A I hI (Fin n → A))

/-- **The same statement for the Čech model of derived completion.** The reflection model and the
Čech model `DerivedCompletion.derivedCompletionFunctor` are isomorphic compatibly with their
units (`Stacks.Algebraization.exists_iso_derivedCompletionFunctor_completionFunctor`), so the
image of the unit on degree-zero cohomology is the same submodule up to that isomorphism. This is
the form local duality is phrased over. -/
theorem range_homologyMap_derivedCompletionUnit_sup_smul_eq_top
    (A : Type u) [CommRing A] [IsNoetherianRing A] {r : ℕ} (f : Fin r → A)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X)) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((DerivedCompletion.derivedCompletionUnit A f).app X)).hom ⊔
        Ideal.span (Set.range f) •
          (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((DerivedCompletion.derivedCompletionFunctor A f).obj X))) = ⊤ := by
  classical
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hH
  have hI : (Ideal.span (Set.range f)).FG := Submodule.fg_span (Set.finite_range f)
  obtain ⟨e, he⟩ := exists_iso_derivedCompletionFunctor_completionFunctor
    (Ideal.span (Set.range f)) hI f rfl X
  have hcomp : H.map ((adicCompletionUnit A (Ideal.span (Set.range f)) hI).app X) ≫ H.map e.inv =
      H.map ((DerivedCompletion.derivedCompletionUnit A f).app X) := by
    rw [← H.map_comp, ← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact range_sup_smul_eq_top_of_comp_eq _ _ _ LinearMap.id (H.map e.inv).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    (fun m => by simpa using ConcreteCategory.congr_hom hcomp m)
    (range_homologyMap_adicCompletionUnit_sup_smul_eq_top A (Ideal.span (Set.range f)) hI X hX)

end Stacks.Algebraization

end
