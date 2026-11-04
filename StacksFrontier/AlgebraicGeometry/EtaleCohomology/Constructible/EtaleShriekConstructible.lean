module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.Topology.Stratification.Partition
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of the sheaf represented by an étale scheme

Let `j : U ⟶ X` be an étale morphism of quasi-compact and quasi-separated schemes, presented as
an object `U` of the small étale site of `X`. The sheaf `h_U` represented by `U` is a
constructible sheaf of sets: on each stratum of a partition of `X` into constructible locally
closed subschemes over which `j` becomes finite étale, the inverse image of `h_U` is represented
by a finite étale scheme, hence finite locally constant.

## Main definitions

* `AlgebraicGeometry.HasFiniteEtaleStratification` is the conclusion of Stacks 03S0 for `U`: a
  partition of `X` into constructible locally closed subschemes over each of which `j` is finite
  étale.

## Main results

* `Stacks.Sites.sheafPullbackSheafifiedYonedaIso` identifies the sheaf pullback of a sheafified
  representable with the sheafified representable of the image object.
* `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda` is constructibility of `h_U`.

## Implementation notes

The represented sheaf is the sheafified Yoneda image, which makes sense without choosing a
subcanonical instance for the small étale site. Its inverse image along a stratum is computed by
corepresentability: both the pullback of `h_U^♯` and the representable of the base-changed object
corepresent sections over that object, so the fully faithful coyoneda embedding produces the
isomorphism. The existence of the stratification is a hypothesis, stated as the conclusion of
Stacks 03S0; it is a property of the morphism alone and involves no sheaf.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v c

namespace Stacks.Sites

section PullbackRepresentable

variable {C : Type c} [Category.{v} C] {D : Type c} [Category.{v} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [HasWeakSheafify J (Type (max c v))]
  [HasWeakSheafify K (Type (max c v))]
  [(u.sheafPushforwardContinuous (Type (max c v)) J K).IsRightAdjoint]

/-- Morphisms out of the sheaf pullback of a sheafified representable `h_U^♯` are the sections
over `u U`: the adjunction between pullback and pushforward, followed by Yoneda's lemma for
sheaves. -/
public def sheafPullbackSheafifiedYonedaSectionEquiv (U : C)
    (G : Sheaf K (Type (max c v))) :
    ((u.sheafPullback (Type (max c v)) J K).obj ((Sheaf.sheafifiedYoneda J).obj U) ⟶ G) ≃
      G.obj.obj (Opposite.op (u.obj U)) :=
  ((u.sheafAdjunctionContinuous (Type (max c v)) J K).homEquiv _ G).trans
    ((Sheaf.sectionEquiv J).trans
      (Equiv.cast (Functor.sheafPushforwardContinuous_obj_obj_obj u (Type (max c v)) J K G
        (Opposite.op U))))

omit [HasWeakSheafify K (Type (max c v))] in
/-- The corepresentability bijection of `sheafPullbackSheafifiedYonedaSectionEquiv` is natural in
the test sheaf. -/
public theorem sheafPullbackSheafifiedYonedaSectionEquiv_comp (U : C)
    {G G' : Sheaf K (Type (max c v))} (α : G ⟶ G')
    (f : (u.sheafPullback (Type (max c v)) J K).obj
      ((Sheaf.sheafifiedYoneda J).obj U) ⟶ G) :
    sheafPullbackSheafifiedYonedaSectionEquiv u J K U G' (f ≫ α) =
      α.hom.app (Opposite.op (u.obj U))
        (sheafPullbackSheafifiedYonedaSectionEquiv u J K U G f) := by
  simp only [sheafPullbackSheafifiedYonedaSectionEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Sheaf.sectionEquiv_comp]
  rfl

/-- Both `u_s(h_U^♯)` and `h_{u U}^♯` corepresent the sections over `u U`, naturally in the test
sheaf. -/
public def sheafPullbackSheafifiedYonedaCorepIso (U : C) :
    coyoneda.obj (Opposite.op ((u.sheafPullback (Type (max c v)) J K).obj
        ((Sheaf.sheafifiedYoneda J).obj U))) ≅
      coyoneda.obj (Opposite.op ((Sheaf.sheafifiedYoneda K).obj (u.obj U))) :=
  NatIso.ofComponents
    (fun G => Equiv.toIso
      ((sheafPullbackSheafifiedYonedaSectionEquiv u J K U G).trans
        (Sheaf.sectionEquiv K).symm))
    (by
      intro G G' α
      ext f
      change (Sheaf.sectionEquiv K).symm
          (sheafPullbackSheafifiedYonedaSectionEquiv u J K U G' (f ≫ α)) =
        (Sheaf.sectionEquiv K).symm
          (sheafPullbackSheafifiedYonedaSectionEquiv u J K U G f) ≫ α
      apply (Sheaf.sectionEquiv K).injective
      rw [Equiv.apply_symm_apply, sheafPullbackSheafifiedYonedaSectionEquiv_comp,
        Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply])

/-- **Stacks 04D3 for sheafified representables.** The sheaf pullback along a continuous functor
`u` of the sheaf represented by `U` is the sheaf represented by `u U`. -/
public def sheafPullbackSheafifiedYonedaIso (U : C) :
    (u.sheafPullback (Type (max c v)) J K).obj ((Sheaf.sheafifiedYoneda J).obj U) ≅
      (Sheaf.sheafifiedYoneda K).obj (u.obj U) :=
  ((Coyoneda.fullyFaithful (C := Sheaf K (Type (max c v)))).preimageIso
    (sheafPullbackSheafifiedYonedaCorepIso u J K U)).unop.symm

end PullbackRepresentable

end Stacks.Sites

namespace AlgebraicGeometry

/-- **The conclusion of Stacks 03S0** for the étale object `U` of the small étale site of `X`:
there is a partition of `X` into constructible subsets, each the image of an immersed subscheme
over which the structure morphism of `U` becomes finite étale. -/
public def HasFiniteEtaleStratification (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.obj X.property) : Prop :=
  ∃ P : Set (Set X.obj), IsTopologicalPartition P ∧
    (∀ S ∈ P, Topology.IsConstructible S) ∧
    (∀ S ∈ P, ∃ (Y : B.Scheme) (i : Y ⟶ X),
      IsImmersion (B.inclusion.map i) ∧
        Set.range (B.inclusion.map i).base = S ∧
        IsFinite (B.inclusion.map ((smallEtaleBaseChange B i).obj U).obj.hom) ∧
        Etale (B.inclusion.map ((smallEtaleBaseChange B i).obj U).obj.hom))

/-- **Stacks 03S8, part (1).** For an étale morphism of quasi-compact and quasi-separated
schemes `j : U ⟶ X`, presented as an object `U` of the small étale site of `X`, the sheaf `h_U`
represented by `U` is a constructible sheaf of sets on `X_étale`. -/
@[stacks 03S8 "part (1), carrying the conclusion of Stacks 03S0 (an etale morphism of \
quasi-compact quasi-separated schemes becomes finite etale on the strata of a partition of its \
target into constructible locally closed subschemes) as the explicit hypothesis hstrat"]
public theorem isConstructibleSetSheaf_sheafifiedYoneda (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj]
    (hstrat : HasFiniteEtaleStratification B X U) :
    IsConstructibleSetSheaf B X
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) := by
  classical
  obtain ⟨P, hP, hc, hstrata⟩ := hstrat
  choose T i himm hrange hfin het using fun s : {S : Set X.obj // S ∈ P} => hstrata s.1 s.2
  refine isConstructibleFiniteSheaf_of_constructible_immersion_cover B X _ T i himm
    (fun s => (hrange s).symm ▸ hc s.1 s.2) ?_ ?_
  · ext x
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
    obtain ⟨S, ⟨hS, hx⟩, -⟩ := hP.1.2 x
    exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, (hrange ⟨S, hS⟩).symm ▸ hx⟩
  · intro s
    exact isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B (T s) _
      (hF := Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable B (T s) _
        ⟨(smallEtaleBaseChange B (i s)).obj U, hfin s,
          ⟨Stacks.Sites.sheafPullbackSheafifiedYonedaIso (smallEtaleBaseChange B (i s))
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (T s).obj (T s).property) U⟩⟩)

end AlgebraicGeometry

end
