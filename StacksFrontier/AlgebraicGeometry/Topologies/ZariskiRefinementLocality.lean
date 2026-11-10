module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineOpenCovering

/-!
# Zariski-local statements become site-local on a site refining Zariski coverings

Let `C` be a site of schemes over `S` such that every Zariski covering of the scheme underlying an
object `T` of `C` is refined by a covering of `C`: there is a covering family `Q` of `T` each of
whose arrows, read downstairs, factors through a member of the Zariski covering (condition (2) of
Tag 03OJ). Then the sieve on `T` of arrows of `C` whose image factors through a member of a
Zariski covering `R` is a covering sieve, and a morphism of presheaves on `C` which is surjective
(or injective) on the sections over every object whose structure morphism factors through a member
of a Zariski covering is locally surjective (locally injective).

## Main results

* `Stacks.Sites.functorPullback_generate_mem_toGrothendieck_of_zariskiRefinement`: the sieve of
  arrows of the site whose image factors through a member of a Zariski covering is a covering
  sieve.
* `Stacks.Sites.isLocallySurjective_of_zariskiRefinement` and
  `Stacks.Sites.isLocallyInjective_of_zariskiRefinement`: a morphism of presheaves on the site
  which is surjective, respectively injective, on sections over the objects factoring through a
  member of some Zariski covering is locally surjective, respectively locally injective.
* `Stacks.Sites.isLocallySurjective_of_zariskiRefinement'` and
  `Stacks.Sites.isLocallyInjective_of_zariskiRefinement'`: the same with one Zariski covering
  fixed in advance for all sections over a given object.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe w' v' u' u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (K : Precoverage C)

/-- On a site refining Zariski coverings, the arrows of the site whose image factors through a
member of a Zariski covering form a covering sieve. -/
public theorem functorPullback_generate_mem_toGrothendieck_of_zariskiRefinement
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (T : C) (R : Presieve ((toOver.obj T).left))
    (hR : R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left)) :
    Sieve.functorPullback (toOver ⋙ Over.forget S) (Sieve.generate R) ∈
      K.toGrothendieck T := by
  obtain ⟨Q, hQ, hQle⟩ := hZariski T R hR
  refine K.toGrothendieck.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hQ)
  rintro Z f ⟨W, l, q, hq, rfl⟩
  change (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map (l ≫ q))
  rw [Functor.map_comp]
  exact (Sieve.generate R).downward_closed
    (hQle _ _ (Presieve.map_map (F := toOver ⋙ Over.forget S) hq)) _

section Concrete

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

variable (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
  R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
    ∃ Q : Presieve T, Q ∈ K T ∧
      Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)

include hZariski

/-- A morphism of presheaves on a site refining Zariski coverings which is surjective on the
sections over the objects factoring through a member of a Zariski covering, which may depend on
the section to be lifted, is locally surjective. -/
public theorem isLocallySurjective_of_zariskiRefinement {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (h : ∀ (T : C) (s : ToType (Q.obj (op T))),
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              ∃ t : ToType (P.obj (op Z)), α.app (op Z) t = Q.map f.op s) :
    Presheaf.IsLocallySurjective K.toGrothendieck α where
  imageSieve_mem {T} s := by
    obtain ⟨R, hR, hlift⟩ := h T s
    exact K.toGrothendieck.superset_covering (fun _ f hf => hlift f hf)
      (functorPullback_generate_mem_toGrothendieck_of_zariskiRefinement S toOver K hZariski T R hR)

/-- A morphism of presheaves on a site refining Zariski coverings which is injective on the
sections over the objects factoring through a member of a Zariski covering, which may depend on
the pair of sections, is locally injective. -/
public theorem isLocallyInjective_of_zariskiRefinement {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (h : ∀ (T : C) (x y : ToType (P.obj (op T))), α.app (op T) x = α.app (op T) y →
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              P.map f.op x = P.map f.op y) :
    Presheaf.IsLocallyInjective K.toGrothendieck α where
  equalizerSieve_mem {T} x y hxy := by
    obtain ⟨R, hR, heq⟩ := h T.unop x y hxy
    exact K.toGrothendieck.superset_covering (fun _ f hf => heq f hf)
      (functorPullback_generate_mem_toGrothendieck_of_zariskiRefinement S toOver K hZariski
        T.unop R hR)

/-- `Stacks.Sites.isLocallySurjective_of_zariskiRefinement` with the Zariski covering chosen
before the section. -/
public theorem isLocallySurjective_of_zariskiRefinement' {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (R : ∀ T : C, Presieve ((toOver.obj T).left))
    (hR : ∀ T : C, R T ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left))
    (h : ∀ (T : C) ⦃Z : C⦄ (f : Z ⟶ T),
      (Sieve.generate (R T)).arrows ((toOver ⋙ Over.forget S).map f) →
        Function.Surjective (α.app (op Z))) :
    Presheaf.IsLocallySurjective K.toGrothendieck α :=
  isLocallySurjective_of_zariskiRefinement S toOver K hZariski α
    fun T _ => ⟨R T, hR T, fun _ f hf => h T f hf _⟩

/-- `Stacks.Sites.isLocallyInjective_of_zariskiRefinement` with the Zariski covering chosen before
the pair of sections. -/
public theorem isLocallyInjective_of_zariskiRefinement' {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
    (R : ∀ T : C, Presieve ((toOver.obj T).left))
    (hR : ∀ T : C, R T ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left))
    (h : ∀ (T : C) ⦃Z : C⦄ (f : Z ⟶ T),
      (Sieve.generate (R T)).arrows ((toOver ⋙ Over.forget S).map f) →
        Function.Injective (α.app (op Z))) :
    Presheaf.IsLocallyInjective K.toGrothendieck α :=
  isLocallyInjective_of_zariskiRefinement S toOver K hZariski α
    fun T x y hxy => ⟨R T, hR T, fun _ f hf => h T f hf (by
      rw [NatTrans.naturality_apply α f.op x, NatTrans.naturality_apply α f.op y, hxy])⟩

end Concrete

end Stacks.Sites

end
