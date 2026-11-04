module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CoheratorLeraySpectralSequence
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Leray spectral sequence of an adjunction

Let `L : ℬ ⥤ 𝒜` be left adjoint to `P : 𝒜 ⥤ ℬ`, between abelian categories with enough
injectives, with `L` preserving monomorphisms, and let `𝒪_𝒜` and `𝒪_ℬ` be objects with
`L(𝒪_ℬ) ≅ 𝒪_𝒜`.  Write `Γ_𝒜 = Hom(𝒪_𝒜, -)` and `Γ_ℬ = Hom(𝒪_ℬ, -)`, and `H^p(𝒜, -)`,
`H^p(ℬ, -)` for their right derived functors.  Then for every bounded below complex `K` of
`𝒜` there is a spectral sequence

`E_2^{p,q} = H^p(ℬ, R^q P(K))  ⟹  H^{p+q}(𝒜, K)`.

This is the shape of the Leray spectral sequence of **Stacks 0732** whenever the inverse image
`L = f^*` is exact and carries the structure sheaf to the structure sheaf: `P = f_*` then
carries injectives to injectives, because its left adjoint preserves monomorphisms
(`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`), and
`Γ_ℬ ∘ P ≅ Γ_𝒜`, because `Hom(𝒪_ℬ, f_* M) = Hom(f^* 𝒪_ℬ, M) = Hom(𝒪_𝒜, M)`.  So the Grothendieck
spectral sequence of **Stacks 015N** for the composite `Γ_ℬ ∘ P` applies, and its abutment is
`H^*(𝒜, K)`.  A 1-morphism of algebraic stacks is of this kind, its inverse image being
restriction along the 1-morphism (**Stacks 06WE**).

Taking global sections to be `Hom(𝒪, -)` is what makes the statement independent of any
presentation of the two categories: on sheaves of modules over a ringed site it is the functor
of global sections (`SheafOfModules.unitHomEquiv`), and its right derived functors are
`Ext^p(𝒪, -)`, the cohomology of **Stacks 071H**.

## Main definitions

* `CategoryTheory.Adjunction.compPreadditiveCoyonedaIso`: `P ⋙ Hom(𝒪_ℬ, -) ≅ Hom(𝒪_𝒜, -)`.

## Main results

* `CategoryTheory.Adjunction.exists_leraySpectralSequence`: the spectral sequence.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u₂ w₁ w₂ w₃

namespace CategoryTheory.Adjunction

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Category.{v} 𝒜] [Category.{v} ℬ]

section Preadditive

variable [Preadditive 𝒜] [Preadditive ℬ] {L : ℬ ⥤ 𝒜} {P : 𝒜 ⥤ ℬ} (adj : L ⊣ P) [L.Additive]
  {O𝒜 : 𝒜} {Oℬ : ℬ} (e : L.obj Oℬ ≅ O𝒜)

/-- **Global sections commute with the right adjoint**: `Hom(𝒪_ℬ, P M) ≅ Hom(L 𝒪_ℬ, M)` by the
adjunction, and `Hom(L 𝒪_ℬ, M) ≅ Hom(𝒪_𝒜, M)` along `e : L 𝒪_ℬ ≅ 𝒪_𝒜`. -/
def compPreadditiveCoyonedaIso :
    P ⋙ preadditiveCoyoneda.obj (Opposite.op Oℬ) ≅ preadditiveCoyoneda.obj (Opposite.op O𝒜) :=
  NatIso.ofComponents
    (fun M => (adj.homAddEquiv Oℬ M).symm.toAddCommGrpIso ≪≫
      (preadditiveCoyoneda.mapIso e.op).symm.app M)
    (fun {M N} g => by
      ext (x : Oℬ ⟶ P.obj M)
      change e.inv ≫ (adj.homEquiv Oℬ N).symm (x ≫ P.map g) =
        (e.inv ≫ (adj.homEquiv Oℬ M).symm x) ≫ g
      rw [adj.homEquiv_naturality_right_symm, Category.assoc])

end Preadditive

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w₁} 𝒜] [HasDerivedCategory.{w₂} ℬ]
  [HasDerivedCategory.{w₃} AddCommGrpCat.{v}] [EnoughInjectives 𝒜] [EnoughInjectives ℬ]
  {L : ℬ ⥤ 𝒜} {P : 𝒜 ⥤ ℬ} (adj : L ⊣ P) [L.Additive] [P.Additive] [L.PreservesMonomorphisms]
  {O𝒜 : 𝒜} {Oℬ : ℬ} (e : L.obj Oℬ ≅ O𝒜)

include adj e in
/-- **The Leray spectral sequence of an adjunction.**  Let `L ⊣ P` with `L : ℬ ⥤ 𝒜` additive
and preserving monomorphisms (`P` is then additive, by `Adjunction.right_adjoint_additive`),
both categories abelian with enough injectives, and let
`e : L 𝒪_ℬ ≅ 𝒪_𝒜`.  For every `K` in `D⁺(𝒜)` there is a spectral sequence with

`E_2^{p,q} = H^p(ℬ, H^q(RP(K)))`, where `H^p(ℬ, -) = R^p Hom(𝒪_ℬ, -)`,

abutting to `H^{p+q}(𝒜, K) = H^{p+q}(R Hom(𝒪_𝒜, -)(K))`. -/
theorem exists_leraySpectralSequence (K : DerivedCategory.Plus 𝒜) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{v} 0,
      (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        ((preadditiveCoyoneda.obj (Opposite.op Oℬ)).rightDerivedPlus p).obj
          ((DerivedCategory.Plus.homologyFunctor ℬ q).obj (P.rightDerivedFunctorPlus.obj K)))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
          ((preadditiveCoyoneda.obj (Opposite.op O𝒜)).rightDerivedFunctorPlus.obj K)) := by
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  obtain ⟨L', hL'⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp P
    (preadditiveCoyoneda.obj (Opposite.op Oℬ)) (fun I _ => Functor.rightAcyclic_of_injective _ _) K
  let Fil : ∀ (_p n : ℤ), Subobject (L'.X.X n) := fun p n =>
    Subobject.mk ((L'.filtration.ι.app (Opposite.op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (L'.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (L'.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (L'.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (L'.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1))
  obtain ⟨E, -, h2, habuts⟩ := hL' Fil (fun _ _ => rfl) Zc (fun _ _ _ => rfl)
    Dc (fun _ _ _ => rfl)
  refine ⟨E, h2, habuts.of_nonempty_iso fun n => ⟨?_⟩⟩
  exact (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).mapIso
    ((Functor.rightDerivedFunctorPlusNatIso (adj.compPreadditiveCoyonedaIso e)).app K)

include adj e in
/-- **The Leray spectral sequence of an adjunction, with its second page read through a
coreflection.**  In the situation of `CategoryTheory.Adjunction.exists_leraySpectralSequence`, let
`incl ⊣ Q` be a coreflection of `ℬ` onto a category `𝒬` and `M` an object of `𝒜`.  If for every
`q` the kernel and the cokernel of the counit `incl (Q (R^q P M)) ⟶ R^q P M` are acyclic for
`Hom(𝒪_ℬ, -)`, then there is a first quadrant spectral sequence with

`E_2^{p,q} = H^p(ℬ, incl (Q (R^q P M)))`

abutting to `H^{p+q}(𝒜, M)`. -/
@[sga "4 V 5.3" "more general"]
theorem exists_leraySpectralSequence_of_coreflection {𝒬 : Type*} [Category 𝒬] {incl : 𝒬 ⥤ ℬ}
    {Q : ℬ ⥤ 𝒬} (adjQ : incl ⊣ Q) (M : 𝒜)
    (hker : ∀ q : ℕ, ∀ p : ℕ, IsZero (((preadditiveCoyoneda.obj (Opposite.op Oℬ)).rightDerivedPlus
      (p : ℤ)).obj (kernel (adjQ.counit.app ((P.rightDerived q).obj M)))))
    (hcoker : ∀ q : ℕ, ∀ p : ℕ, IsZero
      (((preadditiveCoyoneda.obj (Opposite.op Oℬ)).rightDerivedPlus (p : ℤ)).obj
        (cokernel (adjQ.counit.app ((P.rightDerived q).obj M))))) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{v} 0,
      (∀ p q : ℕ, Nonempty ((E.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        ((preadditiveCoyoneda.obj (Opposite.op Oℬ)).rightDerivedPlus (p : ℤ)).obj
          (incl.obj (Q.obj ((P.rightDerived q).obj M))))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 zero_le_two).X (p, q))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        ((preadditiveCoyoneda.obj (Opposite.op O𝒜)).rightDerivedPlus n).obj M) := by
  obtain ⟨E, hE₂, habuts⟩ :=
    exists_leraySpectralSequence adj e ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj M)
  let G := preadditiveCoyoneda.obj (Opposite.op Oℬ)
  refine ⟨E, fun p q => ?_, fun p q hpq => ?_, habuts⟩
  · have hiso : IsIso ((G.rightDerivedPlus (p : ℤ)).map
        (adjQ.counit.app ((P.rightDerived q).obj M))) :=
      Stacks.Cohomology.isIso_rightDerivedPlus_map_of_isZero_kernel_cokernel G _
        (hker q) (hcoker q) p
    exact ⟨(hE₂ p q).some ≪≫ (G.rightDerivedPlus (p : ℤ)).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso P q).app M).symm ≪≫
      (asIso ((G.rightDerivedPlus (p : ℤ)).map
        (adjQ.counit.app ((P.rightDerived q).obj M)))).symm⟩
  · refine IsZero.of_iso ?_ (hE₂ p q).some
    rcases hpq with hp | hq
    · exact Functor.isZero_rightDerivedPlus_of_neg G _ p hp
    · let : G.rightDerivedFunctorPlus.CommShift ℤ := G.commShiftRightDerivedFunctorPlus
      have : G.rightDerivedFunctorPlus.IsTriangulated := G.isTriangulated_rightDerivedFunctorPlus
      have : (G.rightDerivedPlus p).Additive := by
        unfold Functor.rightDerivedPlus
        infer_instance
      exact (G.rightDerivedPlus p).map_isZero (Functor.isZero_rightDerivedPlus_of_neg P M q hq)

end CategoryTheory.Adjunction

end
