module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenDerived
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleProjectionSituation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleNullity
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-!
# Uniqueness of cartesian objects with a given simplicial system

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total site
with flat transitions. A cartesian object of `D(O)` is determined, together with its maps, by
its associated simplicial system of Stacks 0D9N: Stacks 0D9S realises every morphism of
simplicial systems out of a cartesian object by a map of `D(O)`, and Stacks 0D9R makes such a
map unique. This is the uniqueness assertion of Stacks 0DCA, which the source deduces from these
two lemmas.

This file also introduces the simplicial object `K = u(L)` of `SR(C)` attached to a simplicial
object `L` of `SR(B)` in Situation 0DC9, and its total site `(C/K)_total` of Remark 0D9W.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.DegreeZeroFaithful`: maps between two objects of
  `D(O)` are determined by their degree-zero restriction. This is the conclusion of
  Stacks 0D9R.
* `AlgebraicGeometry.RingedSite.LocallyGiven.image`: the simplicial object `K = u(L)` of
  `SR(C)` attached to a simplicial object `L` of `SR(B)`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.totalSituation`: the total simplicial site
  `(C/K)_total` of Remark 0D9W, read as a simplicial-site situation.

## Main results

* `CategoryTheory.SimplicialSiteSituation.degreeZeroFaithful_of_eq_zero`: Stacks 0D9R gives
  `DegreeZeroFaithful`, two maps agreeing in degree zero differing by a map vanishing there.
* `CategoryTheory.SimplicialSiteSituation.existsUnique_iso_of_derivedModuleSystem_iso`: two
  cartesian objects of `D(O)` with isomorphic simplicial systems whose positively shifted
  self-maps vanish are isomorphic by exactly one isomorphism inducing the given isomorphism of
  systems, granted degree-zero faithfulness.
* `CategoryTheory.CocontinuousSimplicialSite.existsUnique_iso_of_derivedModuleSystem_iso`: the
  same in case (B) of Situation 09WE, with degree-zero faithfulness supplied by Stacks 0D9R.

## Implementation notes

*The vanishing hypotheses.* Stacks 0D9S asks for `Hom(K_i[i - 1], K'_i) = 0` for `i > 1` and
Stacks 0D9R for `Hom(K_i[i], K'_i) = 0` for `i > 0` and `Hom(K_i[i + 1], K'_i) = 0` for
`i ≥ 0`, for the pairs `(E, E')`, `(E', E)`, `(E, E)` and `(E', E')`. Since all four systems are
identified with one system, each of these is an instance of the vanishing of the positively
shifted self-maps of that one system, transported along the degreewise identifications
(`CategoryTheory.SimplicialSiteSituation.shift_hom_eq_zero_of_iso`).

*Universes.* The simplicial-site infrastructure of this development is monomorphic in one
universe `u`: the component sites of `CategoryTheory.SimplicialSiteSituation` are objects of
`Cat.{u, u}` and the structure sheaf on the total site takes sections in `Type u`.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe uM u w uB vB

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- Maps from `A` to `B` in the derived category of `O`-modules on the total site are determined
by their restriction to simplicial degree zero.

This is the conclusion of **Stacks 0D9R** for the pair `(A, B)`, in the form in which the
uniqueness argument of Stacks 0DCA consumes it. -/
def DegreeZeroFaithful (A B : DerivedCategory (S.totalRingedTopos O).Modules) : Prop :=
  ∀ f g : A ⟶ B,
    (S.derivedComponentModuleRestriction O ⦋0⦌).map f =
        (S.derivedComponentModuleRestriction O ⦋0⦌).map g →
      f = g

/-- Maps of `D(O)` are determined in simplicial degree zero as soon as every map vanishing there
vanishes: the morphisms of `D(O)` form abelian groups and derived degree-zero restriction is
additive. -/
theorem degreeZeroFaithful_of_eq_zero (A B : DerivedCategory (S.totalRingedTopos O).Modules)
    (h : ∀ f : A ⟶ B, (S.derivedComponentModuleRestriction O ⦋0⦌).map f = 0 → f = 0) :
    DegreeZeroFaithful S O A B := by
  have : (S.derivedComponentModuleRestriction O ⦋0⦌).Additive :=
    inferInstanceAs ((S.componentModulesRestriction O ⦋0⦌).mapDerivedCategory).Additive
  intro f g hfg
  refine sub_eq_zero.mp (h (f - g) ?_)
  rw [CategoryTheory.Functor.map_sub, hfg, sub_self]

/-- Shifted maps between two objects vanish when both objects are isomorphic to one whose
shifted self-maps vanish. -/
theorem shift_hom_eq_zero_of_iso {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasShift 𝒟 ℤ]
    {A B T : 𝒟} (a : A ≅ T) (b : B ≅ T) (t : ℤ)
    (hT : ∀ g : (shiftFunctor 𝒟 t).obj T ⟶ T, g = 0) (g : (shiftFunctor 𝒟 t).obj A ⟶ B) :
    g = 0 := by
  have h := hT ((shiftFunctor 𝒟 t).map a.inv ≫ g ≫ b.hom)
  have e : g = (shiftFunctor 𝒟 t).map a.hom ≫ ((shiftFunctor 𝒟 t).map a.inv ≫ g ≫ b.hom) ≫
      b.inv := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [e, h, zero_comp, comp_zero]

section Derived

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

variable {S O}

/-- **Two cartesian objects of `D(O)` with isomorphic simplicial systems are isomorphic by
exactly one isomorphism inducing the given isomorphism of systems**, granted flat structure-sheaf
transitions, vanishing positively shifted self-maps of the system, and degree-zero faithfulness.

Stacks 0D9S, `CategoryTheory.SimplicialSiteSituation.exists_hom_of_cartesian`, produces maps
`γ : E ⟶ E'` and `δ : E' ⟶ E` realising `e` and `e⁻¹` in every simplicial degree. Their composites
agree with the identities after restriction to degree zero, so faithfulness in degree zero makes
them the identities; faithfulness also makes the resulting isomorphism the only one inducing `e`.
The vanishing hypotheses of Stacks 0D9S are instances of `hSelf`, transported along the
degreewise components of `e`. -/
theorem existsUnique_iso_of_derivedModuleSystem_iso
    (hflat : ∀ (m n : SimplexCategory) (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (E E' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hE : S.IsCartesianDerivedModule O E) (hE' : S.IsCartesianDerivedModule O E')
    (hSelf : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O k).Modules)) (t : ℤ)).obj
          ((S.derivedModuleSystem O E).obj k) ⟶ (S.derivedModuleSystem O E).obj k, g = 0)
    (hfaithful : DegreeZeroFaithful S O E E')
    (hfaithfulE : DegreeZeroFaithful S O E E)
    (hfaithfulE' : DegreeZeroFaithful S O E' E')
    (e : S.derivedModuleSystem O E ≅ S.derivedModuleSystem O E') :
    ∃! ε : E ≅ E', ∀ n : SimplexCategory,
      (S.derivedComponentModuleRestriction O n).map ε.hom = e.hom.app n := by
  have hpred : ∀ i : ℕ, 1 < i → ∀ g : (shiftFunctor
      (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) ((i : ℤ) - 1)).obj
        ((S.derivedModuleSystem O E).obj ⦋i⦌) ⟶ (S.derivedModuleSystem O E).obj ⦋i⦌, g = 0 := by
    intro i hi
    have h := hSelf ⦋i⦌ (i - 1) (by omega)
    rwa [show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega] at h
  let eI := fun k : SimplexCategory =>
    (SimplicialDerivedModuleSystem.evaluation k).mapIso e
  obtain ⟨γ, hγ⟩ := S.exists_hom_of_cartesian O E E' hflat hE
    (fun i hi g => shift_hom_eq_zero_of_iso (Iso.refl _) (eI ⦋i⦌).symm _ (hpred i hi) g) e.hom
  obtain ⟨δ, hδ⟩ := S.exists_hom_of_cartesian O E' E hflat hE'
    (fun i hi g => shift_hom_eq_zero_of_iso (eI ⦋i⦌).symm (Iso.refl _) _ (hpred i hi) g) e.inv
  have hγδ : γ ≫ δ = 𝟙 E := by
    refine hfaithfulE _ _ ?_
    rw [CategoryTheory.Functor.map_comp, hγ, hδ, CategoryTheory.Functor.map_id]
    exact (eI ⦋0⦌).hom_inv_id
  have hδγ : δ ≫ γ = 𝟙 E' := by
    refine hfaithfulE' _ _ ?_
    rw [CategoryTheory.Functor.map_comp, hδ, hγ, CategoryTheory.Functor.map_id]
    exact (eI ⦋0⦌).inv_hom_id
  exact ⟨⟨γ, δ, hγδ, hδγ⟩, hγ, fun ε hε =>
    Iso.ext (hfaithful _ _ ((hε ⦋0⦌).trans (hγ ⦋0⦌).symm))⟩

end Derived

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u}) (P : Sheaf (situation C).totalTopology
    CommRingCat.{u})
  [hder : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy ((situation C).transitionRingedToposHom P φ)).HasLeftDerivedFunctor
      (targetQuasiIso ((situation C).componentRingedTopos P m))]

/-- **Two cartesian objects of `D(P)` with isomorphic simplicial systems, in case (B) of
Situation 09WE.** If the structure-sheaf transitions are flat and the positively shifted
self-maps of the simplicial system vanish, two cartesian objects `E`, `E'` with an isomorphism
`e` of their simplicial systems are isomorphic by exactly one isomorphism inducing `e`.

Degree-zero faithfulness is Stacks 0D9R,
`CategoryTheory.SimplicialSiteSituation.eq_zero_of_derivedComponentModuleRestriction_map_eq_zero`,
whose vanishing hypotheses for each of the pairs `(E, E')`, `(E, E)` and `(E', E')` are instances
of `hSelf`, transported along the degreewise components of `e`. -/
theorem existsUnique_iso_of_derivedModuleSystem_iso
    (hflat : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
      ((situation C).transitionRingedToposHom P φ).IsFlat)
    (E E' : DerivedCategory ((situation C).totalRingedTopos P).Modules)
    (hE : (situation C).IsCartesianDerivedModule P E)
    (hE' : (situation C).IsCartesianDerivedModule P E')
    (hSelf : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ g : (shiftFunctor (DerivedCategory (((situation C).componentRingedTopos P k).Modules))
          (t : ℤ)).obj (((situation C).derivedModuleSystem P E).obj k) ⟶
          ((situation C).derivedModuleSystem P E).obj k, g = 0)
    (e : (situation C).derivedModuleSystem P E ≅ (situation C).derivedModuleSystem P E') :
    ∃! ε : E ≅ E', ∀ n : SimplexCategory,
      ((situation C).derivedComponentModuleRestriction P n).map ε.hom = e.hom.app n := by
  let eI := fun k : SimplexCategory =>
    (SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation k).mapIso e
  have hflat' : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
      ((situation C).transitionRingedToposHom P φ).IsFlat := fun m n φ => hflat m n φ
  have hsucc : ∀ i : ℕ, ∀ g : (shiftFunctor
      (DerivedCategory (((situation C).componentRingedTopos P ⦋i⦌).Modules)) ((i : ℤ) + 1)).obj
        (((situation C).derivedModuleSystem P E).obj ⦋i⦌) ⟶
        ((situation C).derivedModuleSystem P E).obj ⦋i⦌, g = 0 := by
    intro i
    have h := hSelf ⦋i⦌ (i + 1) (by omega)
    rwa [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by omega] at h
  -- Each of the three pairs is handled by Stacks 0D9R.
  have faithful : ∀ (A B : DerivedCategory ((situation C).totalRingedTopos P).Modules)
      (_ : (situation C).IsCartesianDerivedModule P A)
      (a : ∀ k, ((situation C).derivedModuleSystem P A).obj k ≅
        ((situation C).derivedModuleSystem P E).obj k)
      (b : ∀ k, ((situation C).derivedModuleSystem P B).obj k ≅
        ((situation C).derivedModuleSystem P E).obj k),
      SimplicialSiteSituation.DegreeZeroFaithful (situation C) P A B := by
    intro A B hA a b
    exact SimplicialSiteSituation.degreeZeroFaithful_of_eq_zero _ P A B fun f hf =>
      (situation C).eq_zero_of_derivedComponentModuleRestriction_map_eq_zero P A B hflat' hA
        (fun i hi g => SimplicialSiteSituation.shift_hom_eq_zero_of_iso (a ⦋i⦌) (b ⦋i⦌) _
          (hSelf ⦋i⦌ i hi) g)
        (fun i g => SimplicialSiteSituation.shift_hom_eq_zero_of_iso (a ⦋i⦌) (b ⦋i⦌) _
          (hsucc i) g) f hf
  exact SimplicialSiteSituation.existsUnique_iso_of_derivedModuleSystem_iso hflat E E' hE hE'
    hSelf (faithful E E' hE (fun _ => Iso.refl _) (fun k => (eI k).symm))
    (faithful E E hE (fun _ => Iso.refl _) (fun _ => Iso.refl _))
    (faithful E' E' hE' (fun k => (eI k).symm) (fun k => (eI k).symm)) e

end CategoryTheory.CocontinuousSimplicialSite

namespace AlgebraicGeometry.RingedSite

attribute [local instance] LocallyGiven.category

variable {X : RingedSite.{u, u, w}} (G : LocallyGiven.{uM, u, u, w, uB, vB} X)
  (L : SimplicialObject (FormalCoproduct.{u} G.B))

/-- The simplicial object `K = u(L)` of `SR(C)` obtained by applying `u` to every component of a
simplicial object `L` of `SR(B)`. -/
def LocallyGiven.image : SimplicialObject (FormalCoproduct.{u} X.C) :=
  L ⋙ Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct G.u

variable [X.J.toCoverage.HasPullbacks]

/-- The total simplicial site `(C/K)_total` of Remark 0D9W for `K = u(L)`, read as a
simplicial-site situation in the sense of Stacks 09WE. -/
def LocallyGiven.totalSituation : SimplicialSiteSituation.{u} :=
  CategoryTheory.SimplicialSemiRepresentable.situation X.J (G.image L)

end AlgebraicGeometry.RingedSite

end
