module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import StacksFrontier.Homology.HomComplex.HomologyZeroHomotopyHom
public import StacksFrontier.Homology.HomComplex.LinearFunctorComparison
public import StacksFrontier.RingTheory.Module.AdicSystem.RowReductionHomology

/-!
# Mittag-Leffler for homotopy classes of maps into the adic reductions of a perfect complex

Let `A` be a Noetherian ring, `𝔞 ⊆ A` an ideal, `M` a bounded complex of finite projective
`A`-modules and `E` an exact `A`-linear endofunctor of the category of `A`-modules. The inverse
system of sets

`j ↦ Hom_{K(A)}(M, E(M ⊗_A A/𝔞ʲ))`,

the tensor product being taken termwise and `E` applied termwise, satisfies the Mittag-Leffler
condition.

## Main results

* `CategoryTheory.Functor.IsMittagLeffler.of_equiv`: the Mittag-Leffler condition passes along
  natural bijections between inverse systems of sets in arbitrary universes.
* `Stacks.AdicSystem.HomotopyHom.finite_cochain`: over a Noetherian ring the Hom complex out of a
  bounded complex of finite modules into a complex of finite modules has finite terms.
* `Stacks.AdicSystem.HomotopyHom.homologyHomComplexIso`: the identification
  `H⁰(Hom^•(M, E(M ⊗ L))) ≅ E(H⁰(Hom^•(M, M) ⊗ L))`, and its naturality in `L`.
* `Stacks.AdicSystem.HomotopyHom.isMittagLeffler_coyoneda_adicQuotient_rowFunctor`: the
  Mittag-Leffler property of `j ↦ Hom_{K(A)}(M, E(M ⊗_A A/𝔞ʲ))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex
  CochainComplex.HomComplex CochainComplex.KFlatBifunctor

universe u

namespace CategoryTheory.Functor

/-- **The Mittag-Leffler condition passes along natural bijections.** If `F` and `G` are
inverse systems of sets, possibly in different universes, and `e` is a family of bijections
`F j ≃ G j` compatible with the transition maps, then `F` is Mittag-Leffler when `G` is. -/
theorem IsMittagLeffler.of_equiv {J : Type*} [Category J] {F : J ⥤ Type*} {G : J ⥤ Type*}
    (e : ∀ j, F.obj j ≃ G.obj j)
    (he : ∀ ⦃i j : J⦄ (f : i ⟶ j) (x : F.obj i), e j (F.map f x) = G.map f (e i x))
    (hG : G.IsMittagLeffler) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hG j
  refine ⟨i, f, fun k g => ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hf g ⟨e i x, rfl⟩
  refine ⟨(e k).symm y, (e j).injective ?_⟩
  rw [he, Equiv.apply_symm_apply, hy, he]

end CategoryTheory.Functor

namespace Stacks.AdicSystem.HomotopyHom

open Stacks.HomComplex.TensorHomMap (postcomp)

variable {A : Type u} [CommRing A]

/-- **The Hom complex between bounded complexes of finite modules has finite terms**, over a
Noetherian ring. -/
theorem finite_cochain [IsNoetherianRing A] (K L : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] (hK : ∀ p, Module.Finite A (K.X p))
    (hL : ∀ q, Module.Finite A (L.X q)) (n : ℤ) :
    Module.Finite A (Cochain K L n) := by
  choose k f hf using fun p => (hK p).exists_fin'
  let Φ : Cochain K L n →ₗ[A]
      (∀ p : Finset.Icc a b, (Fin (k p) → A) →ₗ[A] L.X ((p : ℤ) + n)) :=
    { toFun z := fun p => (z.v p (p + n) rfl).hom ∘ₗ f p
      map_add' z z' := by
        funext p
        simp [Cochain.add_v, LinearMap.add_comp]
      map_smul' r z := by
        funext p
        simp [Cochain.smul_v, LinearMap.smul_comp] }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun z hz => ?_)
  ext p q hpq m
  obtain rfl : q = p + n := hpq.symm
  by_cases hp : p ∈ Finset.Icc a b
  · have h := LinearMap.congr_fun (congrFun hz ⟨p, hp⟩)
    obtain ⟨y, rfl⟩ := hf p m
    exact h y
  · have hzero := Stacks.HomComplex.LinearFunctor.isZero_X_of_notMem_Icc (K := K) a b hp
    rw [Stacks.HomComplex.LinearFunctor.eq_zero_of_isZero hzero m, map_zero, map_zero]

section Comparison

variable (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
  (hM : ∀ k, Module.Finite A (M.X k) ∧ Module.Projective A (M.X k))
  (E : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [E.Additive] [E.Linear A]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- The comparison `E(Hom^•(M, M) ⊗ L) ≅ Hom^•(M, E(M ⊗ L))` of Hom complexes with the linear
functor `E(- ⊗ L)`, an isomorphism since `M` is bounded with finite projective terms. -/
def comparisonIso (L : ModuleCat.{u} A) :
    ((tensorRight L ⋙ E).mapHomologicalComplex _).obj (HomComplexR A M M) ≅
      HomComplexR A M (((tensorRight L ⋙ E).mapHomologicalComplex _).obj M) :=
  letI := Stacks.HomComplex.LinearFunctor.isIso_comparison M (tensorRight L ⋙ E) a b hM
  asIso (Stacks.HomComplex.LinearFunctor.comparison M M (tensorRight L ⋙ E))

omit [PreservesFiniteLimits E] [PreservesFiniteColimits E] in
/-- The forward map of `comparisonIso` is the comparison map of Hom complexes. -/
lemma comparisonIso_hom (L : ModuleCat.{u} A) :
    (comparisonIso M a b hM E L).hom =
      Stacks.HomComplex.LinearFunctor.comparison M M (tensorRight L ⋙ E) :=
  rfl

omit [E.Linear A] in
/-- Degree-zero cohomology commutes with the exact functor `E`, read on a complex obtained by
applying an additive functor `F` termwise. -/
def mapHomologyIsoComp (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [F.Additive]
    (X : CochainComplex (ModuleCat.{u} A) ℤ) :
    (((F ⋙ E).mapHomologicalComplex _).obj X).homology 0 ≅
      E.obj (((F.mapHomologicalComplex _).obj X).homology 0) :=
  (((F.mapHomologicalComplex _).obj X).sc 0).mapHomologyIso E

omit [E.Linear A] in
/-- `mapHomologyIsoComp` is natural in the additive functor. -/
theorem homologyMap_comp_mapHomologyIsoComp_hom
    {F F' : ModuleCat.{u} A ⥤ ModuleCat.{u} A} [F.Additive] [F'.Additive] (β : F ⟶ F')
    (X : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (Functor.whiskerRight β E) _).app X) 0 ≫
        (mapHomologyIsoComp E F' X).hom =
      (mapHomologyIsoComp E F X).hom ≫
        E.map (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex β _).app X) 0) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) 0).map
      ((NatTrans.mapHomologicalComplex β _).app X)) E

/-- **The degree-zero cohomology of `Hom^•(M, E(M ⊗ L))` is `E(H⁰(Hom^•(M, M) ⊗ L))`**, for `M`
bounded with finite projective terms and `E` exact and `A`-linear: the comparison of Hom
complexes with the linear functor `E(- ⊗ L)`, followed by the commutation of cohomology with the
exact functor `E`. -/
def homologyHomComplexIso (L : ModuleCat.{u} A) :
    (HomComplexR A M (((tensorRight L ⋙ E).mapHomologicalComplex _).obj M)).homology 0 ≅
      E.obj ((((tensorRight L).mapHomologicalComplex _).obj (HomComplexR A M M)).homology 0) :=
  HomologicalComplex.homologyMapIso (comparisonIso M a b hM E L).symm 0 ≪≫
    mapHomologyIsoComp E (tensorRight L) (HomComplexR A M M)

/-- The forward map of `homologyHomComplexIso`, as the map on degree-zero cohomology induced by
the inverse of `comparisonIso` followed by `mapHomologyIsoComp`. -/
lemma homologyHomComplexIso_hom (L : ModuleCat.{u} A) :
    (homologyHomComplexIso M a b hM E L).hom =
      HomologicalComplex.homologyMap (comparisonIso M a b hM E L).inv 0 ≫
        (mapHomologyIsoComp E (tensorRight L) (HomComplexR A M M)).hom :=
  rfl

/-- **Naturality of `homologyHomComplexIso` in the module `L`.** -/
theorem homologyHomComplexIso_hom_naturality {L L' : ModuleCat.{u} A} (g : L ⟶ L') :
    HomologicalComplex.homologyMap (postcomp A M _ _ ((NatTrans.mapHomologicalComplex
        (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E) _).app M)) 0 ≫
        (homologyHomComplexIso M a b hM E L').hom =
      (homologyHomComplexIso M a b hM E L).hom ≫
        E.map (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          ((curriedTensor (ModuleCat.{u} A)).flip.map g) _).app (HomComplexR A M M)) 0) := by
  have hnat := Stacks.HomComplex.LinearFunctor.comparison_natTrans M M _
    (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E)
  rw [← comparisonIso_hom M a b hM E L, ← comparisonIso_hom M a b hM E L'] at hnat
  have hinv : postcomp A M _ _ ((NatTrans.mapHomologicalComplex
        (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E) _).app M) ≫
        (comparisonIso M a b hM E L').inv =
      (comparisonIso M a b hM E L).inv ≫ (NatTrans.mapHomologicalComplex
        (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E) _).app
          (HomComplexR A M M) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [homologyHomComplexIso_hom, homologyHomComplexIso_hom,
    ← HomologicalComplex.homologyMap_comp_assoc, hinv, HomologicalComplex.homologyMap_comp_assoc,
    homologyMap_comp_mapHomologyIsoComp_hom, Category.assoc]

/-- **Homotopy classes of maps `M ⟶ E(M ⊗ L)` are the elements of `E(H⁰(Hom^•(M, M) ⊗ L))`.** -/
def homotopyHomEquiv (L : ModuleCat.{u} A) :
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tensorRight L ⋙ E).mapHomologicalComplex _).obj M)) ≃
      E.obj ((((tensorRight L).mapHomologicalComplex _).obj (HomComplexR A M M)).homology 0) :=
  (Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _).symm.toEquiv.trans
    (homologyHomComplexIso M a b hM E L).toLinearEquiv.toEquiv

/-- **Naturality of `homotopyHomEquiv` in the module `L`.** -/
theorem homotopyHomEquiv_naturality {L L' : ModuleCat.{u} A} (g : L ⟶ L')
    (x : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tensorRight L ⋙ E).mapHomologicalComplex _).obj M)) :
    homotopyHomEquiv M a b hM E L' (x ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E) _).app M)) =
      (E.map (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        ((curriedTensor (ModuleCat.{u} A)).flip.map g) _).app (HomComplexR A M M)) 0)).hom
          (homotopyHomEquiv M a b hM E L x) := by
  obtain ⟨y, rfl⟩ := (Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _).surjective x
  rw [← Stacks.HomComplex.homologyZeroHomotopyHomEquiv_naturality]
  show (homologyHomComplexIso M a b hM E L').hom.hom
      ((Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _).symm
        ((Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _)
          ((HomologicalComplex.homologyMap (postcomp A M _ _ ((NatTrans.mapHomologicalComplex
            (Functor.whiskerRight ((curriedTensor (ModuleCat.{u} A)).flip.map g) E) _).app M))
              0).hom y))) =
    (E.map (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
        ((curriedTensor (ModuleCat.{u} A)).flip.map g) _).app (HomComplexR A M M)) 0)).hom
      ((homologyHomComplexIso M a b hM E L).hom.hom
        ((Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _).symm
          ((Stacks.HomComplex.homologyZeroHomotopyHomEquiv A M _) y)))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact congrArg (fun f => f.hom y) (homologyHomComplexIso_hom_naturality M a b hM E g)

include a b hM in
/-- **Mittag-Leffler for homotopy classes of maps into the adic reductions of a perfect
complex.** Let `A` be a Noetherian ring, `𝔞 ⊆ A` an ideal, `M` a bounded complex of finite
projective `A`-modules and `E` an exact `A`-linear endofunctor of the category of `A`-modules.
The inverse system of sets `j ↦ Hom_{K(A)}(M, E(M ⊗_A A/𝔞ʲ))`, the tensor product being taken
termwise, satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_coyoneda_adicQuotient_rowFunctor [IsNoetherianRing A] (𝔞 : Ideal A) :
    Functor.IsMittagLeffler
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A) ⋙
        rowFunctor (curriedTensor (ModuleCat.{u} A)) M ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
              coyoneda.obj (op ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))) := by
  have hP : ∀ n, Module.Finite A ((HomComplexR A M M).X n) := fun n =>
    finite_cochain M M a b (fun p => (hM p).1) (fun p => (hM p).1) n
  have h0 :=
    Stacks.PseudoCoherent.AdicCompletion.isMittagLefflerCategorical_adicQuotient_rowFunctor_homology
      𝔞 (HomComplexR A M M) hP 0
  have h1 := isMittagLeffler_forget_of_isMittagLefflerCategorical _ (h0.map _ E)
  exact Functor.IsMittagLeffler.of_equiv
    (G := ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A) ⋙
      rowFunctor (curriedTensor (ModuleCat.{u} A)) (HomComplexR A M M) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0) ⋙ E) ⋙
          forget (ModuleCat.{u} A))
    (fun j => homotopyHomEquiv M a b hM E
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A)).obj j))
    (fun _ _ f x => homotopyHomEquiv_naturality M a b hM E
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A)).map f) x) h1

end Comparison

end Stacks.AdicSystem.HomotopyHom

end
