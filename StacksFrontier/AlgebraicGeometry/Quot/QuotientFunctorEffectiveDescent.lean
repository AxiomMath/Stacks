module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSourceSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity

/-!
# Effective descent of quotients along an fpqc covering of algebraic spaces

Let `{p i : Z i ⟶ W}` be an fpqc covering of algebraic spaces over a scheme `S` of a big fppf
site and let `M` be a quasi-coherent `𝒪_W`-module.  This file proves the two halves of the
bijection of Stacks 08IU that the descent of quasi-coherent modules of Stacks 04W8 supplies:

* a homomorphism of `𝒪_W`-modules is determined by its inverse images along the covering, and
  in particular a quotient of `M` is determined by its restrictions to the members;
* a family of quasi-coherent quotients `p i ^* M ⟶ G i` which agree on the pairwise fibre
  products — in the sense that there are isomorphisms of the two inverse images of the `G`
  carrying one projection to the other through the canonical comparison of the two inverse
  images of `M` — comes from a quasi-coherent quotient `M ⟶ N`.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_modulePullback_map_eq_zero_of_isFpqcCovering`: a
  homomorphism of modules killed by the inverse images along an fpqc covering is zero.
* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_map_of_isFpqcCovering`: surjectivity of a
  homomorphism of modules is fpqc local.
* `AlgebraicGeometry.Space.exists_epi_of_isFpqcCovering`: **the effectivity half of the
  bijection of Stacks 08IU**, for epimorphisms out of the inverse images of a quasi-coherent
  module.

## References

* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- The ambient-universe abelian structure on sheaves of modules does not apply to the modules on
an algebraic space, whose sections live in the universe of the site's morphisms. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- Inverse image of `𝒪`-modules preserves zero morphisms, being a left adjoint by the adjunction
half of Stacks 03LU. -/
theorem modulePullback_preservesZeroMorphisms_of_adjunction {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : (modulePullback B S hS f).PreservesZeroMorphisms :=
  have : (modulePullback B S hS f).IsLeftAdjoint := ⟨_, ⟨modulePullbackAdjunction B S hS f⟩⟩
  inferInstance

/-- Inverse image of `𝒪`-modules preserves epimorphisms, being a left adjoint. -/
theorem epi_modulePullback_map_of_epi {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (g : M ⟶ N) [Epi g] :
    Epi ((modulePullback B S hS f).map g) :=
  have := Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f)
  inferInstance

/-! ### Faithfulness along an fpqc covering -/

/-- **A homomorphism of modules killed by the inverse images along an fpqc covering is zero.**
This is the faithfulness clause of Stacks 04W8, in the form
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering`
proves it, with no quasi-coherence hypothesis. -/
theorem eq_zero_of_modulePullback_map_eq_zero_of_isFpqcCovering {I : Type v}
    {W : AlgebraicSpaces B S hS} (Z : I → AlgebraicSpaces B S hS) (p : ∀ i, Z i ⟶ W)
    (hp : IsFpqcCovering B S hS fun i => (p i).hom)
    {M N : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS (p i)).map φ = 0) : φ = 0 := by
  refine modulePullback_map_injective_of_isFpqcCovering B S hS (reprFpqcHomInjective B S hS)
    Z p hp φ 0 fun i => ?_
  have := modulePullback_preservesZeroMorphisms_of_adjunction B S hS (p i)
  rw [h i, Functor.map_zero]

/-- **Surjectivity of a homomorphism of modules is fpqc local.**  If the inverse image of `φ`
along every member of an fpqc covering is an epimorphism, then `φ` is one: its cokernel
projection is killed by every inverse image, hence vanishes by the faithfulness clause of
Stacks 04W8. -/
theorem epi_of_epi_modulePullback_map_of_isFpqcCovering {I : Type v}
    {W : AlgebraicSpaces B S hS} (Z : I → AlgebraicSpaces B S hS) (p : ∀ i, Z i ⟶ W)
    (hp : IsFpqcCovering B S hS fun i => (p i).hom)
    {M N : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N)
    (h : ∀ i, Epi ((modulePullback B S hS (p i)).map φ)) : Epi φ := by
  refine Preadditive.epi_of_cokernel_zero
    (eq_zero_of_modulePullback_map_eq_zero_of_isFpqcCovering B S hS Z p hp _ fun i => ?_)
  have := modulePullback_preservesZeroMorphisms_of_adjunction B S hS (p i)
  have := h i
  rw [← cancel_epi ((modulePullback B S hS (p i)).map φ), ← Functor.map_comp,
    cokernel.condition, Functor.map_zero, comp_zero]

/-! ### Naturality of the reading of a pairwise isomorphism on a test space -/

/-- **The reading of a pairwise isomorphism on a test space is natural.**  A family of
morphisms `a i : F i ⟶ F' i` intertwining two families of pairwise isomorphisms intertwines
their readings on any test space mapping compatibly to two members. -/
theorem transitionOn_hom_naturality {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F F' : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    (φ' : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F' i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F' j))
    (a : ∀ i, F i ⟶ F' i)
    (ha : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (a i) ≫ (φ' i j).hom =
      (φ i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (a j))
    {T : AlgebraicSpaces B S hS} (i j : I) (w : T ⟶ pair B S hS Y f i j)
    (wi : T ⟶ Y i) (wj : T ⟶ Y j) (hi : w ≫ pairFst B S hS Y f i j = wi)
    (hj : w ≫ pairSnd B S hS Y f i j = wj) :
    (modulePullback B S hS wi).map (a i) ≫
        (transitionOn B S hS Y f F' φ' i j w wi wj hi hj).hom =
      (transitionOn B S hS Y f F φ i j w wi wj hi hj).hom ≫
        (modulePullback B S hS wj).map (a j) := by
  subst hi hj
  simp only [transitionOn, pullbackComparison_rfl, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.symm_inv, Iso.app_hom, Category.assoc]
  have n1 := (modulePullbackCompIso B S hS w (pairFst B S hS Y f i j)).inv.naturality (a i)
  have n2 := (modulePullbackCompIso B S hS w (pairSnd B S hS Y f i j)).hom.naturality (a j)
  simp only [Functor.comp_map] at n1 n2
  rw [reassoc_of% n1, ← n2]
  simp only [← Functor.map_comp_assoc]
  rw [ha i j]

/-! ### Effectivity -/

section Effectivity

variable {I : Type v} {W : AlgebraicSpaces B S hS} (Z : I → AlgebraicSpaces B S hS)
  (p : ∀ i, Z i ⟶ W)

/-- The canonical comparison of the two inverse images of `M` on the pairwise fibre product of
two members of a family. -/
abbrev pairComparison (M : Modules.{u, u} B S hS W.1 W.2) (i j : I) :
    (modulePullback B S hS (pairFst B S hS Z p i j)).obj ((modulePullback B S hS (p i)).obj M) ≅
      (modulePullback B S hS (pairSnd B S hS Z p i j)).obj ((modulePullback B S hS (p j)).obj M) :=
  canonicalComparison (pairFst B S hS Z p i j) (pairSnd B S hS Z p i j) (p i) (p j)
    (pair_condition B S hS Z p i j) M

/-- **The cocycle condition transported along epimorphisms.**  If a family of epimorphisms
`π i : F i ⟶ G i` intertwines two families of pairwise isomorphisms and the first family
satisfies the cocycle condition on a test space, so does the second. -/
theorem transitionOn_cocycle_of_epi_of_cocycle {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F G : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    (τ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (G j))
    (π : ∀ i, F i ⟶ G i) (hπ : ∀ i, Epi (π i))
    (hτ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (π i) ≫ (τ i j).hom =
      (φ i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (π j))
    (i j k : I) (T : AlgebraicSpaces B S hS)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (vk : T ⟶ Y k)
    (vij : T ⟶ pair B S hS Y f i j) (vjk : T ⟶ pair B S hS Y f j k)
    (vik : T ⟶ pair B S hS Y f i k)
    (hij₀ : vij ≫ pairFst B S hS Y f i j = vi) (hij₁ : vij ≫ pairSnd B S hS Y f i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Y f j k = vj) (hjk₁ : vjk ≫ pairSnd B S hS Y f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS Y f i k = vi) (hik₁ : vik ≫ pairSnd B S hS Y f i k = vk)
    (hφ : transitionOn B S hS Y f F φ i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS Y f F φ j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS Y f F φ i k vik vi vk hik₀ hik₁) :
    transitionOn B S hS Y f G τ i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS Y f G τ j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS Y f G τ i k vik vi vk hik₀ hik₁ := by
  have : Epi ((modulePullback B S hS vi).map (π i)) :=
    have := hπ i
    epi_modulePullback_map_of_epi B S hS vi (π i)
  refine Iso.ext ((cancel_epi ((modulePullback B S hS vi).map (π i))).1 ?_)
  rw [Iso.trans_hom, ← Category.assoc,
    transitionOn_hom_naturality B S hS Y f F G φ τ π hτ i j vij vi vj hij₀ hij₁,
    Category.assoc, transitionOn_hom_naturality B S hS Y f F G φ τ π hτ j k vjk vj vk hjk₀ hjk₁,
    ← Category.assoc, ← Iso.trans_hom, hφ,
    transitionOn_hom_naturality B S hS Y f F G φ τ π hτ i k vik vi vk hik₀ hik₁]

/-- The descent datum of a family of quotients of the inverse images of a quasi-coherent module
which agree on the pairwise fibre products.  The cocycle condition is the one of the canonical
descent datum of the module, transported along the projections, which are epimorphisms. -/
def quotientDescentDatum (M : Modules.{u, u} B S hS W.1 W.2) (hM : M.IsQuasicoherentOnSite)
    (G : ∀ i, Modules.{u, u} B S hS (Z i).1 (Z i).2) (hG : ∀ i, (G i).IsQuasicoherentOnSite)
    (π : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ G i) (hπ : ∀ i, Epi (π i))
    (τ : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Z p i j)).obj (G j))
    (hτ : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).map (π i) ≫ (τ i j).hom =
      ((canonicalDescentDatum' B S hS Z p M hM).transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z p i j)).map (π j)) :
    DescentDatum B S hS Z p where
  F := G
  quasicoherent := hG
  transition := τ
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ :=
    transitionOn_cocycle_of_epi_of_cocycle B S hS Z p (canonicalDescentDatum' B S hS Z p M hM).F G
      (canonicalDescentDatum' B S hS Z p M hM).transition τ π hπ hτ i j k T vi vj vk vij vjk vik
      hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁
      ((canonicalDescentDatum' B S hS Z p M hM).cocycle i j k T vi vj vk vij vjk vik
        hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)

/-- **The effectivity half of the bijection of Stacks 08IU.**  Let `{p i : Z i ⟶ W}` be an fpqc
covering and `M` a quasi-coherent `𝒪_W`-module.  A family of epimorphisms `π i : p i ^* M ⟶ G i`
onto quasi-coherent modules which agree on the pairwise fibre products — there are isomorphisms
`τ i j` of the two inverse images of the `G` carrying one inverse image of the projections to
the other, read through the canonical comparison of the two inverse images of `M` — is the
family of inverse images of an epimorphism `φ : M ⟶ N` onto a quasi-coherent module. -/
@[sga "1 VIII 1.8" "partial"]
theorem exists_epi_of_isFpqcCovering (hp : IsFpqcCovering B S hS fun i => (p i).hom)
    (M : Modules.{u, u} B S hS W.1 W.2) (hM : M.IsQuasicoherentOnSite)
    (G : ∀ i, Modules.{u, u} B S hS (Z i).1 (Z i).2) (hG : ∀ i, (G i).IsQuasicoherentOnSite)
    (π : ∀ i, (modulePullback B S hS (p i)).obj M ⟶ G i) (hπ : ∀ i, Epi (π i))
    (τ : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Z p i j)).obj (G j))
    (hτ : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).map (π i) ≫ (τ i j).hom =
      (pairComparison B S hS Z p M i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z p i j)).map (π j)) :
    ∃ (N : Modules.{u, u} B S hS W.1 W.2) (_ : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
      (e : ∀ i, (modulePullback B S hS (p i)).obj N ≅ G i),
      Epi φ ∧ ∀ i, (modulePullback B S hS (p i)).map φ ≫ (e i).hom = π i := by
  obtain ⟨N, hN, ⟨e⟩⟩ := forall_isEffective_of_isFpqcCovering B S hS Z p hp
    (quotientDescentDatum B S hS Z p M hM G hG π hπ τ hτ)
  let ei : ∀ i, G i ≅ (modulePullback B S hS (p i)).obj N :=
    fun i => DescentDatum.appIso B S hS e i
  have hei : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).map (ei i).hom ≫
      (pairComparison B S hS Z p N i j).hom =
        (τ i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Z p i j)).map (ei j).hom :=
    fun i j => e.hom.naturality i j
  obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS
    (reprFpqcHomSurjective B S hS) Z p hp (fun i => π i ≫ (ei i).hom)
    (isPairwiseCompatible_mk B S hS Z p _ fun i j => by
      rw [Functor.map_comp, Category.assoc, hei i j, reassoc_of% (hτ i j),
        Functor.map_comp]) hM hN
  have hfac : ∀ i, (modulePullback B S hS (p i)).map φ ≫ (ei i).inv = π i := fun i => by
    rw [hφ i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨N, hN, φ, fun i => (ei i).symm, ?_, hfac⟩
  refine epi_of_epi_modulePullback_map_of_isFpqcCovering B S hS Z p hp φ fun i => ?_
  rw [hφ i]
  exact epi_comp' (hπ i) (@IsIso.epi_of_iso _ _ _ _ (ei i).hom (Iso.isIso_hom (ei i)))

end Effectivity

end AlgebraicGeometry.Space

end
