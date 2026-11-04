module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Representable.CoveredByRepresentables

/-!
# The set-theoretic condition of Stacks 0GF6

Stacks 0GF6 attaches to a sheaf of sets `𝓕` on the small étale site of an algebraic space `Y`
over `S` the functor
`X(T) = {(y, s) | y : T → Y a morphism over S and s ∈ Γ(T, y_small⁻¹ 𝓕)}`
and asserts, *provided a set theoretic condition is satisfied*, that `X` is an algebraic space
étale over `Y` with `𝓕 ≅ h_X`. The source defers the condition to its proof, where it reads:
by Tag 00WS one finds a set `I`, objects `V_i` of `Y_étale` and a surjection
`∐ h_{V_i} → 𝓕`, and *the set theoretic condition we need is that the index set `I` is not too
large* — so that `V = ∐ V_i` is itself an object of `(Sch/S)_fppf`, hence of `Y_étale`, and one
has a surjection `h_V → 𝓕`. The footnote offers the
sufficient criterion that the supremum of the cardinalities of the stalks of `𝓕` at geometric
points of `Y` be bounded by the size of some object of `(Sch/S)_fppf`.

This file states that condition as the source does, and records the step that needs no
hypothesis.

* The Tag 00WS step holds **unconditionally**: every sheaf of sets on any site is the target of
  an epimorphism from a coproduct of sheafified representables, indexed by the pairs `(U, s)`
  with `U` an object and `s ∈ 𝓕(U)`.
* The **hypothesis** is that for some such family the disjoint union `∐ V_i` is an object of
  `Y_étale`, i.e. that the coproduct `∐ h_{V_i}^#` is the sheafified representable `h_W^#` of an
  étale chart `W` of `Y`, through the maps `V_i → W`. Equivalently
  (`AlgebraicGeometry.Space.SheafGivesSpace.satisfiesSetTheoreticCondition_iff`), some single
  chart `V` has `h_V^#` surjecting onto `𝓕`, which is the form in which the rest of the proof
  uses it.

## Main definitions

* `AlgebraicGeometry.Space.SheafGivesSpace.SatisfiesSetTheoreticCondition`: the set-theoretic
  condition of the proof of Tag 0GF6.

## Main results

* `CategoryTheory.Sheaf.exists_epi_coproduct_sheafifiedYoneda`: on an arbitrary site, every
  sheaf of sets receives an epimorphism from a coproduct of sheafified representables.
* `AlgebraicGeometry.Space.SheafGivesSpace.exists_epi_coproduct_charts`: the Tag 00WS step of
  the proof of Tag 0GF6, for the small étale site of an algebraic space.
* `AlgebraicGeometry.Space.SheafGivesSpace.satisfiesSetTheoreticCondition_iff`: the condition
  is a surjection from the sheafified representable of a single chart.
* `AlgebraicGeometry.Space.SheafGivesSpace.satisfiesSetTheoreticCondition_sheafifiedYoneda`,
  `…_of_epi` and `…_of_iso`: the condition holds for a sheafified representable, and passes
  along an epimorphism of sheaves and in particular along an isomorphism.
* `AlgebraicGeometry.Space.SheafGivesSpace.nonempty_smallEtale` and
  `…_exists_satisfiesSetTheoreticCondition`: the small étale site of an algebraic space is
  nonempty, so the condition is satisfiable over every `Y`.

## Implementation notes

"`∐ V_i` is an object of `Y_étale`" is expressed sheaf-theoretically, as representability of the
sheaf coproduct by an object of the site, so that no construction of disjoint unions of schemes
inside the big fppf site is presupposed; when the disjoint union scheme belongs to the site, it
is such an object. The footnote's stalk-cardinality criterion is a sufficient condition and is
not used.

This differs from `AlgebraicGeometry.SatisfiesSetTheoreticCondition` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Defs.lean`, which is a *two-stage*
presentation: a representable surjects onto the sheaf, **and** a representable surjects onto
the resulting kernel pair. Tag 0GF6 needs only the first stage: the source obtains the relation
`R` with `h_V ×_𝓕 h_V = h_R` as an *open subscheme* of `V ×_Y V` by Tag 04K8.

The general-site result is proved directly rather than transported from
`isLocallySurjective_π` of `StacksFrontier/CategoryTheory/Sites/Representable/`
`StacksFrontier/CategoryTheory/Sites/Representable/CoveredByRepresentables.lean` (Tag 00WS), whose source object is the sheafification of a
*presheaf* coproduct; stating the conclusion with `CategoryTheory.Sheaf.sheafifiedYoneda`
matches the shape `∐ h_{V_i} → 𝓕` the source's proof writes down. The witness is `Sigma.desc`
of the Yoneda transposes `CategoryTheory.Sheaf.sectionEquiv` of the sections, and local
surjectivity is witnessed by the identity arrow: the index `(U, s)` itself lifts `s`, so the
image sieve is the maximal sieve.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 00WS](https://stacks.math.columbia.edu/tag/00WS)
* [Stacks Project, Tag 04K8](https://stacks.math.columbia.edu/tag/04K8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type max u v)]

/-- Every sheaf of sets on a site is the target of an epimorphism from a coproduct of
sheafified representables: the coproduct indexed by the pairs `(U, s)` with `U` an object of
the site and `s` a section of the sheaf over `U`, mapping by the Yoneda transpose of `s` on the
`(U, s)` summand.

This is the shape in which the proof of Stacks 0GF6 uses Stacks 00WS, and it is the half of
that step which needs no set-theoretic hypothesis: the index set is allowed to be as large as
the site requires. -/
theorem exists_epi_coproduct_sheafifiedYoneda (F : Sheaf J (Type max u v)) :
    letI : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
      CategoryTheory.Sheaf.instHasColimitsOfSize
    ∃ (I : Type max u v) (U : I → C)
      (f : (∐ fun i ↦ (Sheaf.sheafifiedYoneda J).obj (U i)) ⟶ F), Epi f := by
  let : HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type max u v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  let I : Type max u v := Σ U : C, F.obj.obj (op U)
  let U : I → C := fun i => i.1
  let f : (∐ fun i : I ↦ (Sheaf.sheafifiedYoneda J).obj (U i)) ⟶ F :=
    Sigma.desc fun i => (Sheaf.sectionEquiv J).symm i.2
  refine ⟨I, U, f, ?_⟩
  have hls : Sheaf.IsLocallySurjective f := by
    refine ⟨?_⟩
    intro X s
    -- The index `(X, s)` lifts `s` itself, so the identity of `X` is in the image sieve.
    let j : I := ⟨X, s⟩
    let t := (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda J).obj (U i)) j).hom.app
      (op (U j)) (Sheaf.tautologicalSection J (U j))
    have hι : Sheaf.sectionEquiv J
        (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda J).obj (U i)) j) = t := by
      rw [← Category.id_comp (Sigma.ι (fun i : I ↦ (Sheaf.sheafifiedYoneda J).obj (U i)) j)]
      exact Sheaf.sectionEquiv_comp J (𝟙 _) _
    have hval : f.hom.app (op (U j)) t = s := by
      rw [← hι, ← Sheaf.sectionEquiv_comp J _ f, Sigma.ι_desc]
      exact Equiv.apply_symm_apply _ _
    have hid : Presheaf.imageSieve f.hom s (𝟙 X) := ⟨t, by simpa using hval⟩
    rw [Sieve.id_mem_iff_eq_top.1 hid]
    exact J.top_mem _
  exact Sheaf.epi_of_isLocallySurjective f

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space.SheafGivesSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS)

/-- **The set-theoretic condition of Stacks 0GF6**, as the source's proof states it. By
Stacks 00WS one finds a set `I`, objects `V i` of `Y_étale` and a surjection
`∐ h_{V i} → 𝓕`; *the set theoretic condition we need is that the index set `I` is not too
large*, so that `V = ∐ V i` is an object of `(Sch/S)_fppf`, hence of `Y_étale`.

Formally: there is a family `V : I → Y_étale` with an epimorphism
`∐ h_{V i}^# ⟶ 𝓕` whose disjoint union is an object of `Y_étale`, that is, an étale chart
`W` of `Y` with maps `ι i : V i ⟶ W` exhibiting `h_W^#` as the coproduct of the sheaves
`h_{V i}^#`. When the disjoint union scheme `∐ V i` lies in the big fppf site it is such a
`W`; the condition asks for nothing more. The footnote's criterion (a bound on the
cardinalities of the geometric stalks of `𝓕`) is a sufficient condition and is not used. -/
def SatisfiesSetTheoreticCondition
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS Y.1)
    (f : (∐ fun i ↦ (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).obj (V i)) ⟶ F),
    Epi f ∧ ∃ (W : SmallEtale B S hS Y.1) (ι : ∀ i, V i ⟶ W),
      IsIso (Sigma.desc fun i ↦ (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).map
        (ι i))

/-- **The set-theoretic condition of Stacks 0GF6 is a surjection from a single chart.** The
condition holds exactly when some étale chart `V` of `Y` has a sheafified representable
`h_V^#` surjecting onto `𝓕`: this is the form `h_V → 𝓕` in which the rest of the source's
proof uses it, `V` being the disjoint union of the charts of the condition. -/
theorem satisfiesSetTheoreticCondition_iff
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :
    SatisfiesSetTheoreticCondition B S hS Y F ↔
      ∃ (V : SmallEtale B S hS Y.1)
        (e : (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).obj V ⟶ F), Epi e := by
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  constructor
  · rintro ⟨I, V, f, hf, W, ι, hι⟩
    exact ⟨W, inv (Sigma.desc fun i ↦
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).map (ι i)) ≫ f, epi_comp _ _⟩
  · rintro ⟨V, e, he⟩
    let D : PUnit.{u + 2} → Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)) :=
      fun _ ↦ (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).obj V
    refine ⟨PUnit, fun _ ↦ V, Sigma.desc fun _ ↦ e, ?_, V, fun _ ↦ 𝟙 V, ?_⟩
    · have hfac : Sigma.ι D PUnit.unit ≫ Sigma.desc (fun _ ↦ e) = e := Sigma.ι_desc _ _
      exact epi_of_epi_fac hfac
    · have hsig : (Sigma.desc fun _ : PUnit.{u + 2} ↦
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).map (𝟙 V)) =
            Sigma.desc fun _ ↦ 𝟙 _ := by
        congr 1
        funext
        exact (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).map_id V
      rw [hsig]
      refine ⟨Sigma.ι D PUnit.unit, ?_, Sigma.ι_desc _ _⟩
      apply Sigma.hom_ext
      rintro ⟨⟩
      rw [Sigma.ι_desc_assoc, Category.id_comp, Category.comp_id]

/-- **The Stacks 00WS step in the proof of Stacks 0GF6.** Every sheaf of sets on the small
étale site of an algebraic space `Y` over `S` receives an epimorphism from a coproduct
`∐_{i ∈ I} h_{V_i}^#` of sheafified representables attached to étale charts `V_i` of `Y`.

This holds with no set-theoretic hypothesis; the hypothesis of Stacks 0GF6,
`AlgebraicGeometry.Space.SheafGivesSpace.SatisfiesSetTheoreticCondition`, is that the
disjoint union of such a family of charts be an object of the site. -/
theorem exists_epi_coproduct_charts
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :
    letI : HasColimitsOfSize.{u + 1, u + 1}
        (Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :=
      CategoryTheory.Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS Y.1)
      (f : (∐ fun i ↦ (Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).obj (V i)) ⟶ F),
        Epi f :=
  CategoryTheory.Sheaf.exists_epi_coproduct_sheafifiedYoneda _ F

/-- A sheafified representable satisfies the set-theoretic condition, the identity being the
required surjection. This is the case in which the source's construction returns the chart it
started from. -/
theorem satisfiesSetTheoreticCondition_sheafifiedYoneda (V : SmallEtale B S hS Y.1) :
    SatisfiesSetTheoreticCondition B S hS Y
      ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS Y.1)).obj V) :=
  (satisfiesSetTheoreticCondition_iff B S hS Y _).2 ⟨V, 𝟙 _, inferInstance⟩

/-- The set-theoretic condition passes along an epimorphism of sheaves: a chart surjecting onto
`F` surjects onto any quotient of `F`. -/
theorem satisfiesSetTheoreticCondition_of_epi
    {F G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))} (α : F ⟶ G) [Epi α]
    (hF : SatisfiesSetTheoreticCondition B S hS Y F) :
    SatisfiesSetTheoreticCondition B S hS Y G := by
  obtain ⟨V, e, he⟩ := (satisfiesSetTheoreticCondition_iff B S hS Y F).1 hF
  exact (satisfiesSetTheoreticCondition_iff B S hS Y G).2 ⟨V, e ≫ α, epi_comp e α⟩

/-- The set-theoretic condition is invariant under isomorphism of sheaves. -/
theorem satisfiesSetTheoreticCondition_of_iso
    {F G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))} (α : F ≅ G)
    (hF : SatisfiesSetTheoreticCondition B S hS Y F) :
    SatisfiesSetTheoreticCondition B S hS Y G :=
  satisfiesSetTheoreticCondition_of_epi B S hS Y α.hom hF

/-- The small étale site of an algebraic space is nonempty: a surjective étale scheme atlas of
`Y` is in particular an étale chart of `Y`, hence an object of the site. -/
theorem nonempty_smallEtale : Nonempty (SmallEtale B S hS Y.1) := by
  obtain ⟨U, f, _, hetale⟩ := Y.2.exists_atlas
  exact ⟨⟨CostructuredArrow.mk f, hetale⟩⟩

/-- Over every algebraic space `Y` the set-theoretic condition of Stacks 0GF6 is satisfiable:
the sheafified representable of any étale chart of `Y` satisfies it, and `Y` has one. -/
theorem exists_satisfiesSetTheoreticCondition :
    ∃ F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)),
      SatisfiesSetTheoreticCondition B S hS Y F := by
  obtain ⟨V⟩ := nonempty_smallEtale B S hS Y
  exact ⟨_, satisfiesSetTheoreticCondition_sheafifiedYoneda B S hS Y V⟩

end AlgebraicGeometry.Space.SheafGivesSpace

end
