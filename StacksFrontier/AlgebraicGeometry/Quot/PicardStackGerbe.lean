module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorSheafification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiscretePresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.Sites.Gerbe.CostructuredArrowProj

/-!
# The Picard stack is a gerbe over the Picard functor (Stacks 0DME)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` (Situation 0D25).  Every
object `(U, b, L)` of the Picard stack `Picardstack_{X/B}` of Section 0372 — a scheme `U` with a
morphism `b : U ⟶ B` and an invertible module `L` on `X_U` — names an element of the relative
Picard functor `Pic_{X/B}` at `(U, b)`: the image of the class of `L` under the canonical map
`Pic(X_U) ⟶ Pic_{X/B}(U)` into the fppf sheafification.  A morphism of the Picard stack carries
the element of its target to the element of its source, so this is a morphism of categories over
the schemes from `Picardstack_{X/B}` to the category fibred in sets attached to `Pic_{X/B}`.
Stacks 0DME asserts that this morphism makes the Picard stack a gerbe over the Picard functor.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.picardFunctorFibred`: the category fibred in sets over
  the test schemes attached to `Pic_{X/B}`, and
  `AlgebraicGeometry.Space.PicardSituation.picardFunctorBasedCategory` the same category over the
  schemes of the big fppf site of `S`.
* `AlgebraicGeometry.Space.PicardSituation.picardFunctorClass`: the element of `Pic_{X/B}(U, b)`
  named by an object `(U, b, L)` of the Picard stack.
* `AlgebraicGeometry.Space.PicardSituation.toPicardFunctorFibred` and
  `AlgebraicGeometry.Space.PicardSituation.toPicardFunctorBased`: **the morphism
  `Picardstack_{X/B} ⟶ Pic_{X/B}`**, as a functor and as a functor over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.isGerbeOver_toPicardFunctorFibred`: the morphism makes
  the Picard stack a gerbe over the Picard functor over the test schemes, for the fppf topology
  on them.
* `AlgebraicGeometry.Space.PicardSituation.isGerbeOver_toPicardFunctorBased`: **Stacks 0DME**,
  the same over the big fppf site of `S`, which is where Stacks 06QC and Stacks 06P2 read it.

## Implementation notes

**The gerbe conditions.**  `CategoryTheory.IsGerbeOver` is Stacks 06P2 in the form of conditions
(2)(a) and (2)(b) of Stacks 06P1, and `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOver`
(Stacks 06QC) is that predicate for the underlying functor of a 1-morphism of algebraic stacks
over the big fppf site of `S`.  The statement here is that predicate for the morphism
`Picardstack_{X/B} ⟶ Pic_{X/B}` over the big fppf site of `S`.  Condition (2)(a) is the local
surjectivity of the unit `Pic(X_T) ⟶ Pic_{X/B}(T)` of the sheafification, and (2)(b) its local
injectivity: two invertible modules on `X_T` with the same image in `Pic_{X/B}(T)` become
isomorphic on an fppf covering, and an isomorphism of the pullbacks is a morphism of the fibre of
the Picard stack.  Both are proved over the test schemes,
where `Pic_{X/B}` and its topology live, and transported to the big fppf site of `S` by
`CategoryTheory.IsGerbeOver.comp_costructuredArrowProj`.

**No hypothesis of the section is used.**  The section's standing assumptions — `f` flat, proper,
of finite presentation, with `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` an isomorphism for every `T` — are what make
`Pic_{X/B}` an algebraic space (Stacks 0D2C) and the Picard stack algebraic; the proof of 0DME
uses none of them, only that `Pic_{X/B}` is the fppf sheafification of `T ↦ Pic(X_T)`
(Stacks 0D25, 0D26).  The statement is therefore proved for every morphism `f` of Situation 0D25,
which contains the statement under the section's assumptions.

**The category attached to `Pic_{X/B}`.**  It is the category of elements of the sheaf,
`CategoryTheory.presheafOfGroupoids` of the presheaf of discrete groupoids
`Pic_{X/B} ⋙ CategoryTheory.typeToGrpd`, the construction Stacks 0458 uses for the presheaves on
the big fppf site (`AlgebraicGeometry.Stack.fibredCategory`).  `Pic_{X/B}` is a presheaf on the
schemes *over the base*, with values in `Type (u + 1)`, so the category is built over the test
schemes and read over the big fppf site of `S` through the projection of the test schemes, as a
sheaf on `(Sch/S)_fppf` with a map to `B`.

**The Picard stack** is the category `AlgebraicGeometry.Space.picardBasedCategory` of Stacks 04WN
at the pseudofunctoriality datum `AlgebraicGeometry.Space.modulePushforwardCoherence` of Stacks
03LU.

## References

* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06P2](https://stacks.math.columbia.edu/tag/06P2)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D26](https://stacks.math.columbia.edu/tag/0D26)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

variable (s : PicardSituation B S hS)

attribute [local instance] picardObjectCategory

/-! ### The category fibred in sets attached to the Picard functor -/

/-- The relative Picard functor `Pic_{X/B}` as a category over the test schemes over the base:
its category of elements, an object over `T` being an element of `Pic_{X/B}(T)`. -/
abbrev picardFunctorFibred : BasedCategory s.SchemesOver :=
  presheafOfGroupoids (s.picardFunctor ⋙ typeToGrpd)

/-- The category attached to the relative Picard functor is fibred in groupoids over the test
schemes (Stacks 0049). -/
theorem isFiberedInGroupoids_picardFunctorFibred :
    s.picardFunctorFibred.p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_presheafOfGroupoids _

/-- The relative Picard functor `Pic_{X/B}` as a category over the schemes of the big fppf site
of `S`: an object over `U` is a morphism `b : U ⟶ B` together with an element of
`Pic_{X/B}(U, b)`. -/
abbrev picardFunctorBasedCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (s.picardFunctorFibred.p ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)

/-! ### The morphism from the Picard stack -/

/-- The element of `Pic_{X/B}(T)` named by an object `(T, L)` of the Picard stack: the image of
the class of `L` under the canonical map `Pic(X_T) ⟶ Pic_{X/B}(T)`. -/
def picardFunctorClass (A : PicardObject s) : s.picardFunctor.obj (op A.T) :=
  s.toPicardFunctor.app (op A.T) (picardClass (s.baseChange A.T) A.lineBundle A.invertible)

/-- A morphism `(f, g) : (T, L) ⟶ (T', L')` of the Picard stack pulls the class of `L'` back to
the class of `L`, since `g : f^*L' ⟶ L` is an isomorphism. -/
theorem picardMap_picardClass_of_hom {A C : PicardObject s} (m : PicardHom A C) :
    s.picardMap m.base (picardClass (s.baseChange C.T) C.lineBundle C.invertible) =
      picardClass (s.baseChange A.T) A.lineBundle A.invertible := by
  rw [picardMap_eq, picardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨asIso m.fibre⟩

/-- A morphism `(f, g) : A ⟶ C` of the Picard stack carries the element of `Pic_{X/B}` named by
`C` to the element named by `A`. -/
theorem picardFunctor_map_picardFunctorClass {A C : PicardObject s} (m : PicardHom A C) :
    s.picardFunctor.map m.base.op (s.picardFunctorClass C) = s.picardFunctorClass A :=
  (NatTrans.naturality_apply s.toPicardFunctor m.base.op
    (picardClass (s.baseChange C.T) C.lineBundle C.invertible)).symm.trans <|
    congrArg (s.toPicardFunctor.app (op A.T)) (s.picardMap_picardClass_of_hom m)

/-- **The morphism `Picardstack_{X/B} ⟶ Pic_{X/B}`**: an object `(T, L)` goes to the element of
`Pic_{X/B}(T)` it names, and a morphism to its morphism of test schemes. -/
def toPicardFunctorFibred : PicardObject s ⥤ s.picardFunctorFibred.obj where
  obj A := ⟨A.T, Discrete.mk (s.picardFunctorClass A)⟩
  map m := ⟨m.base, Discrete.eqToHom (s.picardFunctor_map_picardFunctorClass m).symm⟩
  map_id _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq
  map_comp _ _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq

/-- The morphism `Picardstack_{X/B} ⟶ Pic_{X/B}` lies over the test schemes: followed by the
projection of `Pic_{X/B}` it is the projection of the Picard stack. -/
theorem toPicardFunctorFibred_comp_p :
    s.toPicardFunctorFibred ⋙ s.picardFunctorFibred.p =
      picardProjection (modulePushforwardCoherence B S hS) s :=
  rfl

/-- **The morphism `Picardstack_{X/B} ⟶ Pic_{X/B}` as a functor over the big fppf site of
`S`.** -/
def toPicardFunctorBased :
    picardBasedCategory (modulePushforwardCoherence B S hS) s ⥤ᵇ s.picardFunctorBasedCategory where
  toFunctor := s.toPicardFunctorFibred
  w := rfl

/-! ### The gerbe property -/

/-- The unit `Pic(X_T) ⟶ Pic_{X/B}(T)` of the sheafification is locally surjective: every
element of `Pic_{X/B}(T)` is, fppf locally on `T`, the image of a Picard class. -/
@[sga "6 XIII 3.1" "partial"]
instance isLocallySurjective_toPicardFunctor :
    Presheaf.IsLocallySurjective s.fppfTopology s.toPicardFunctor := by
  have := GrothendieckTopology.isLocallySurjective_toSheafify_type_of_univLE s.fppfTopology
    s.picardPresheaf
  exact (Presheaf.isLocallySurjective_iff_of_fac s.fppfTopology
    (toSheafify_plusPlusIsoSheafify_hom s.fppfTopology (Type (u + 1)) s.picardPresheaf)).2
    inferInstance

/-- The unit `Pic(X_T) ⟶ Pic_{X/B}(T)` of the sheafification is locally injective: two Picard
classes with the same image in `Pic_{X/B}(T)` agree fppf locally on `T`. -/
@[sga "6 XIII 3.1" "partial"]
instance isLocallyInjective_toPicardFunctor :
    Presheaf.IsLocallyInjective s.fppfTopology s.toPicardFunctor := by
  have := GrothendieckTopology.isLocallyInjective_toSheafify_type_of_univLE s.fppfTopology
    s.picardPresheaf
  exact (Presheaf.isLocallyInjective_iff_of_fac s.fppfTopology
    (toSheafify_plusPlusIsoSheafify_hom s.fppfTopology (Type (u + 1)) s.picardPresheaf)).2
    inferInstance

/-- **The Picard stack is a gerbe over the Picard functor, over the test schemes.**  The morphism
`Picardstack_{X/B} ⟶ Pic_{X/B}` satisfies conditions (2)(a) and (2)(b) of Stacks 06P1 for the
fppf topology on the schemes over the base: every element of `Pic_{X/B}(T)` is fppf locally the
class of an invertible module, and two invertible modules on `X_T` with the same image in
`Pic_{X/B}(T)` are fppf locally isomorphic. -/
theorem isGerbeOver_toPicardFunctorFibred :
    IsGerbeOver s.fppfTopology s.picardFunctorFibred.p s.toPicardFunctorFibred where
  base_isFiberedInGroupoids := s.isFiberedInGroupoids_picardFunctorFibred
  isFiberedInGroupoids := s.isFiberedInGroupoids_picardProjection
  locally_essSurj := by
    rintro U ⟨T, ⟨ξ⟩⟩ rfl
    refine ⟨_, Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor (U := op T) ξ, ?_⟩
    rintro V g ⟨t, ht⟩
    obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange V) t
    let ψ : s.toPicardFunctorFibred.obj ⟨V, L, hL⟩ ⟶ ⟨T, ⟨ξ⟩⟩ := ⟨g, Discrete.eqToHom ht⟩
    exact ⟨⟨V, L, hL⟩, ψ, IsHomLift.of_fac' _ g ψ rfl rfl (by
      simp only [eqToHom_refl, Category.comp_id]
      rfl)⟩
  locally_full := by
    intro U x x' b hb
    obtain ⟨T, L, hL⟩ := x
    obtain ⟨T', L', hL'⟩ := x'
    have hT : T = U := IsHomLift.domain_eq s.picardFunctorFibred.p (𝟙 U) b
    have hT' : T' = U := IsHomLift.codomain_eq s.picardFunctorFibred.p (𝟙 U) b
    subst hT
    have e : T = T' := hT'.symm
    subst e
    have hb' : s.picardFunctorFibred.p.IsHomLift
        (R := s.picardFunctorFibred.p.obj (s.toPicardFunctorFibred.obj ⟨T, L, hL⟩))
        (S := s.picardFunctorFibred.p.obj (s.toPicardFunctorFibred.obj ⟨T, L', hL'⟩)) (𝟙 T) b :=
      hb
    have hbase : b.base = 𝟙 T :=
      (IsHomLift.eq_of_isHomLift (p := s.picardFunctorFibred.p)
        (a := s.toPicardFunctorFibred.obj ⟨T, L, hL⟩)
        (b := s.toPicardFunctorFibred.obj ⟨T, L', hL'⟩) (𝟙 T) b).symm
    have hcls : s.toPicardFunctor.app (op T) (picardClass (s.baseChange T) L hL) =
        s.toPicardFunctor.app (op T) (picardClass (s.baseChange T) L' hL') := by
      have h : s.picardFunctorClass ⟨T, L, hL⟩ =
          s.picardFunctor.map b.base.op (s.picardFunctorClass ⟨T, L', hL'⟩) :=
        Discrete.eq_of_hom b.fiber
      have key : ∀ (k : T ⟶ T), k = 𝟙 T → ∀ y, s.picardFunctor.map k.op y = y := by
        rintro k rfl y
        simp
      exact h.trans (key b.base hbase _)
    refine ⟨_, Presheaf.equalizerSieve_mem s.fppfTopology s.toPicardFunctor (X := op T) _ _ hcls,
      ?_⟩
    intro V g hg
    let A : PicardObject s := ⟨T, L, hL⟩
    let A' : PicardObject s := ⟨T, L', hL'⟩
    have hgcls : picardClass _ ((modulePullback B S hS (baseChangeMap s.f g)).obj L)
          (modulePullbackInvertible (baseChangeMap s.f g) L hL) =
        picardClass _ ((modulePullback B S hS (baseChangeMap s.f g)).obj L')
          (modulePullbackInvertible (baseChangeMap s.f g) L' hL') := by
      rwa [← picardPullback_picardClass, ← picardPullback_picardClass]
    obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1 hgcls
    let m : PicardHom (pullbackObject A g) (pullbackObject A' g) :=
      ⟨𝟙 V, ((baseChangeIdComparison (modulePushforwardCoherence B S hS) s.f V).app _ ≪≫
        e.symm).hom, Iso.isIso_hom _⟩
    have hm' : m.base = 𝟙 V := rfl
    have hmlift : (picardProjection (modulePushforwardCoherence B S hS) s).IsHomLift (𝟙 V) m :=
      inferInstanceAs ((picardProjection (modulePushforwardCoherence B S hS) s).IsHomLift
        ((picardProjection (modulePushforwardCoherence B S hS) s).map m) m)
    refine ⟨pullbackObject A g, pullbackObject A' g, pullbackHom A g, pullbackHom A' g, m,
      s.isHomLift_pullbackHom A g, s.isHomLift_pullbackHom A' g, hmlift, ?_⟩
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ Discrete.hom_eq
    show m.base ≫ g = g ≫ b.base
    rw [hm', hbase]
    exact (Category.id_comp g).trans (Category.comp_id g).symm

/-- In Situation 0D25 — a morphism `f : X ⟶ B` of algebraic spaces over `S` —
the morphism `Picardstack_{X/B} ⟶ Pic_{X/B}`, sending an object `(U, b, L)` to the element of
`Pic_{X/B}(U, b)` named by the class of `L`, turns the Picard stack into a gerbe over the Picard
functor: it satisfies the two conditions of Stacks 06P2 (conditions (2)(a) and (2)(b) of
Stacks 06P1) over the big fppf site of `S`, which is the condition of Stacks 06QC.

The section's assumptions on `f` (flat, proper, of finite presentation, with
`𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every `T`) are not assumed. -/
@[stacks 0DME]
theorem isGerbeOver_toPicardFunctorBased :
    IsGerbeOver (BigFppfOver.topology B S hS) s.picardFunctorBasedCategory.p
      s.toPicardFunctorBased.toFunctor :=
  s.isGerbeOver_toPicardFunctorFibred.comp_costructuredArrowProj

end PicardSituation

end AlgebraicGeometry.Space

end
