module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Sites.AbelianRestrictionExact
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Simplicial.AugmentationFibreInjectives

/-!
# The cohomology of the fibre of a simplicial space over an open

Let `X` be a simplicial topological space, let `a : X ⟶ Y` be an augmentation and let `V` be an
open of `Y`.  The cohomology `Hⁿ((X ×_Y V)_Zar, -)` of the total site of the fibre is the `n`-th
right derived functor of its global sections.  This file shows that restriction along the
comparison of total sites is exact and records the consequence that the derived functors of the
composite collapse:

`R ⁿ (Γ((X ×_Y V)_Zar, -|)) (F) ≅ Hⁿ((X ×_Y V)_Zar, F|)`.

This is the reduction step in the proof of [Stacks, Tag 0D84]: once an injective resolution of
`F` on `X_Zar` is chosen, its restriction to `(X ×_Y V)_Zar` is again an injective resolution,
because restriction is exact and preserves injectives, so the cohomology of the fibre is
computed by it.

## Main definitions

* `Stacks.Topology.Simplicial.fibreGlobalSections`: `Γ((X ×_Y V)_Zar, -)`.
* `Stacks.Topology.Simplicial.fibreCohomology`: `Hⁿ((X ×_Y V)_Zar, -)`.
* `Stacks.Topology.Simplicial.fibreRestrictedSections`: `F ↦ Γ((X ×_Y V)_Zar, F|)`, as a
  functor of an abelian sheaf on `X_Zar`.

## Main results

* `Stacks.Topology.Simplicial.fibreImage_isCocontinuous` and
  `Stacks.Topology.Simplicial.fibreRestrictionAb_exact`: restriction to the fibre is exact.
* `Stacks.Topology.Simplicial.fibreRestrictedSections_rightDerived_iso`: **the derived functors
  of the sections of the restriction are the cohomology of the fibre.**
* `Stacks.Topology.Simplicial.fibreRestrictedSections_rightDerived_iso_naturality`: that
  identification is natural in the abelian sheaf.

## Implementation notes

Exactness of restriction is the general statement for a functor of sites that is both
continuous and cocontinuous,
`CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous`;
cocontinuity of the comparison is proved here, from the pointwise description of the covering
sieves of a simplicial site together with the fact that an object of `X_Zar` admitting an arrow
into the fibre is in the image of the comparison.

The collapse is `Stacks.RightDerivedComp.objIso`, whose hypotheses are exactly that restriction
be additive, left exact, acyclic — which for an exact functor is
`CategoryTheory.Functor.isZero_rightDerived_of_exact` — and injective-preserving, the last being
part (1) of the source proof, proved in
`StacksFrontier/Topology/Simplicial/AugmentationFibreInjectives.lean`.

What is **not** proved here is part (2) of the source proof, the identification of
`Γ((X ×_Y V)_Zar, F|)` with the sections `(a_*F)(V)` of the direct image over `V`.  Without it
the displayed collapse is a statement about the derived functors of the sections of the
restriction, not yet about the derived functors of the sections of the direct image.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
* [Stacks Project, Tag 0796](https://stacks.math.columbia.edu/tag/0796)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y) (V : Opens Y)

/-- Sheafification of abelian presheaves on the total site of a simplicial space inverts exactly
the locally bijective morphisms. -/
instance wEqualsLocallyBijective_simplicialOpen_ab (Z : SimplicialObject TopCat.{u}) :
    (SimplicialOpen.grothendieckTopology Z).WEqualsLocallyBijective Ab.{u} :=
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u} _

/-- **The comparison of total sites is cocontinuous.** A covering sieve of the image of an
object `W` of `(X ×_Y V)_Zar` pulls back to a covering sieve of `W`: a member of the covering
family through a given point has its source inside the fibre, because it maps into the image of
`W`, hence is itself the image of an object of `(X ×_Y V)_Zar`, and full faithfulness turns the
member into an arrow of the fibre site. -/
instance fibreImage_isCocontinuous :
    (fibreImage X Y a V).IsCocontinuous
      (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V))
      (SimplicialOpen.grothendieckTopology X) where
  cover_lift {W S} hS := by
    rw [SimplicialOpen.mem_grothendieckTopology] at hS ⊢
    obtain ⟨R, hR, hRS⟩ := hS
    refine ⟨fun _ f => SimplicialOpen.IsLevelwise f ∧ S.arrows ((fibreImage X Y a V).map f),
      ⟨fun _ f hf => hf.1, ?_⟩, fun _ f hf => hf.2⟩
    intro x hx
    obtain ⟨U', g, hg, y, hy, hyx⟩ :=
      hR.2 (fibrePt X Y a V x) (Fibre.mem_imageOpens X Y a V hx)
    obtain ⟨W'', rfl⟩ : ∃ W'', (fibreImage X Y a V).obj W'' = U' :=
      ⟨_, fibreImage_obj_eq_of_le X Y a V (le_fibreOpens_of_hom X Y a V g)⟩
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨W'', (fibreImage_fullyFaithful X Y a V).preimage g, ⟨?_, ?_⟩, z, hz, ?_⟩
    · obtain ⟨e, he⟩ := hR.1 _ g hg
      exact ⟨e, he⟩
    · rw [(fibreImage_fullyFaithful X Y a V).map_preimage]
      exact hRS _ g hg
    · refine fibrePt_injective X Y a V W.degree ?_
      change X.map ((fibreImage_fullyFaithful X Y a V).preimage g).base (fibrePt X Y a V z) = _
      rw [show ((fibreImage_fullyFaithful X Y a V).preimage g).base = g.base from rfl, hzy]
      exact hyx

/-- **Restriction of abelian sheaves to the fibre is exact.** -/
@[stacks 0D84 "the proof's use of exactness of restriction to the fibre"]
theorem fibreRestrictionAb_exact :
    exactFunctor (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u})
      (Sheaf (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u})
      (fibreRestrictionAb X Y a V) :=
  CategoryTheory.Functor.exactFunctor_sheafPushforwardContinuous_of_isCocontinuous.{u} _ _ _

/-- Restriction of abelian sheaves from `X_Zar` to the fibre preserves finite limits. -/
instance fibreRestrictionAb_preservesFiniteLimits :
    PreservesFiniteLimits (fibreRestrictionAb X Y a V) :=
  ((exactFunctor_iff _).1 (fibreRestrictionAb_exact X Y a V)).1

/-- Restriction of abelian sheaves from `X_Zar` to the fibre preserves finite colimits. -/
instance fibreRestrictionAb_preservesFiniteColimits :
    PreservesFiniteColimits (fibreRestrictionAb X Y a V) :=
  ((exactFunctor_iff _).1 (fibreRestrictionAb_exact X Y a V)).2

/-- Restriction of abelian sheaves from `X_Zar` to the fibre is an additive functor. -/
instance fibreRestrictionAb_additive : (fibreRestrictionAb X Y a V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Global sections on the total site of the fibre `X ×_Y V`**, the functor `Γ` of
[Stacks, Tag 06UN] on abelian sheaves. -/
noncomputable def fibreGlobalSections :
    Sheaf (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u} ⥤ Ab.{u} :=
  Sheaf.Γ (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u}

/-- The global sections functor on abelian sheaves on `(X ×_Y V)_Zar` is additive. -/
instance fibreGlobalSections_additive : (fibreGlobalSections X Y a V).Additive := by
  have : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u}) :=
    (constantSheafΓAdj _ _).rightAdjoint_preservesLimits
  dsimp only [fibreGlobalSections]
  exact Functor.additive_of_preserves_binary_products _

/-- **The cohomology `Hⁿ((X ×_Y V)_Zar, -)` of the total site of the fibre**, the `n`-th right
derived functor of its global sections. -/
noncomputable def fibreCohomology (n : ℕ) :
    Sheaf (SimplicialOpen.grothendieckTopology (fibreSpace X Y a V)) Ab.{u} ⥤ Ab.{u} :=
  (fibreGlobalSections X Y a V).rightDerived n

/-- The sections over the fibre of the restriction of an abelian sheaf on `X_Zar`:
`F ↦ Γ((X ×_Y V)_Zar, F|)`.  This is the rule part (2) of the proof of Stacks 0D84 identifies
with `V ↦ (a_*F)(V)`. -/
noncomputable def fibreRestrictedSections :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} ⥤ Ab.{u} :=
  fibreRestrictionAb X Y a V ⋙ fibreGlobalSections X Y a V

/-- The functor `F ↦ Γ((X ×_Y V)_Zar, F|)` on abelian sheaves on `X_Zar` is additive. -/
instance fibreRestrictedSections_additive : (fibreRestrictedSections X Y a V).Additive := by
  dsimp only [fibreRestrictedSections]
  infer_instance

/-- The higher right derived functors of restriction to the fibre vanish, restriction being
exact. -/
theorem isZero_rightDerived_fibreRestrictionAb
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) (n : ℕ) (hn : 0 < n) :
    IsZero (((fibreRestrictionAb X Y a V).rightDerived n).obj F) :=
  CategoryTheory.Functor.isZero_rightDerived_of_exact (fibreRestrictionAb X Y a V) F n hn

/-- **Stacks 0D84, the reduction step of the proof.** The `n`-th right derived functor of
`F ↦ Γ((X ×_Y V)_Zar, F|)` is the cohomology `Hⁿ((X ×_Y V)_Zar, F|)` of the restriction.

An injective resolution of `F` on `X_Zar` restricts to an injective resolution of `F|` on
`(X ×_Y V)_Zar`, because restriction is exact (`fibreRestrictionAb_exact`) and carries
injectives to injectives (part (1) of the source proof,
`fibreRestrictionAb_preservesInjectiveObjects`); so one and the same complex computes both
sides. -/
@[stacks 0D84 "the proof's reduction: derived sections of the restriction are fibre cohomology"]
noncomputable def fibreRestrictedSections_rightDerived_iso (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    ((fibreRestrictedSections X Y a V).rightDerived n).obj F ≅
      (fibreCohomology X Y a V n).obj ((fibreRestrictionAb X Y a V).obj F) :=
  haveI := fibreRestrictionAb_preservesInjectiveObjects X Y a V
  Stacks.RightDerivedComp.objIso (fibreRestrictionAb X Y a V) (injectiveResolution F)
    (isZero_rightDerived_fibreRestrictionAb X Y a V F) (fibreGlobalSections X Y a V) n

/-- The identification of the derived sections of the restriction with the cohomology of the
fibre is natural in the abelian sheaf. -/
theorem fibreRestrictedSections_rightDerived_iso_naturality (n : ℕ)
    {F G : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}} (f : F ⟶ G) :
    ((fibreRestrictedSections X Y a V).rightDerived n).map f ≫
        (fibreRestrictedSections_rightDerived_iso X Y a V n G).hom =
      (fibreRestrictedSections_rightDerived_iso X Y a V n F).hom ≫
        (fibreCohomology X Y a V n).map ((fibreRestrictionAb X Y a V).map f) :=
  have := fibreRestrictionAb_preservesInjectiveObjects X Y a V
  Stacks.RightDerivedComp.objIso_hom_naturality (fibreRestrictionAb X Y a V)
    (fibreGlobalSections X Y a V) n
    (isZero_rightDerived_fibreRestrictionAb X Y a V F)
    (isZero_rightDerived_fibreRestrictionAb X Y a V G) f

end Stacks.Topology.Simplicial

end
