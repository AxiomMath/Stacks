module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Stalks of a direct image along a closed immersion, away from the closed subscheme

Let `i : Z ⟶ X` be a closed immersion in a big étale site. The direct image along `i` of a
sheaf of sets on the small étale site of `Z` has a singleton stalk at every geometric point of
`X` whose image misses `Z`.

## Main results

* `AlgebraicGeometry.smallEtalePushforward_stalk_unique_of_not_mem_range` — the stalk is a
  singleton.

## Implementation notes

A geometric point of `X` missing `Z` has an affine étale neighbourhood whose image is disjoint
from `Z`, because the complement of a closed immersion is open. Every further refinement of
that neighbourhood has empty base change to `Z`, so the sections of the sheaf over that base
change form a singleton: the empty presieve covers an object with empty underlying scheme, and
a sheaf takes an object covered by the empty presieve to a terminal object. The stalk is the
filtered colimit over the étale neighbourhoods, and a filtered colimit in which every object
is refined by one with singleton value is itself a singleton.

Singleton-ness is stated as `∃!`, which avoids choosing an identification with `PUnit`.

## References

* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

section

universe uI vI uT

/-- A filtered colimit of types in which every object admits a morphism to one with singleton
value is itself a singleton. -/
@[instance_reducible]
private noncomputable def unique_colimit_of_refinements
    {I : Type uI} [Category.{vI} I] [IsFiltered I]
    (F : I ⥤ Type uT) [Limits.HasColimit F]
    (hF : ∀ i, ∃ j, Nonempty (i ⟶ j) ∧ Subsingleton (F.obj j) ∧
      Nonempty (F.obj j)) :
    Unique (colimit F) := by
  classical
  let i : I := Classical.choice (IsFiltered.nonempty (C := I))
  let i₀ := Classical.choose (hF i)
  let x₀ := Classical.choice (Classical.choose_spec (hF i)).2.2
  refine ⟨⟨colimit.ι F i₀ x₀⟩, fun x => ?_⟩
  obtain ⟨i, xi, rfl⟩ := Concrete.colimit_exists_rep F x
  let k := IsFiltered.max i i₀
  obtain ⟨l, ⟨g⟩, ⟨hsl, _⟩⟩ := hF k
  change colimit.ι F i xi = colimit.ι F i₀ x₀
  rw [Types.FilteredColimit.colimit_eq_iff]
  exact ⟨l, IsFiltered.leftToMax i i₀ ≫ g, IsFiltered.rightToMax i i₀ ≫ g, hsl.elim _ _⟩

end

/-- A sheaf of sets on the small étale site takes an object with empty underlying scheme to a
singleton: such an object is covered by the empty family. -/
@[instance_reducible]
private noncomputable def unique_sections_of_empty_etale_object
    (B : BigEtaleSite.{u}) (Z : B.Scheme)
    (G : Sheaf (SmallEtale.topology B Z.1 Z.property) (Type (max (u + 1) v)))
    (E : SmallEtale B Z.1 Z.property)
    (hE : IsEmpty ((SmallEtale.toScheme B Z.1 Z.property).obj E)) :
    Unique (G.obj.obj (op E)) := by
  letI := hE
  have hE' : IsEmpty ((schemeBelowInclusion B.cutoff).obj
      ((Over.forget (B.obj Z.1 Z.property)).obj
        ((SmallEtale.inclusion B Z.1 Z.property).obj E))) := hE
  letI := hE'
  have hbotPre : (⊥ : Presieve E) ∈ SmallEtale.precoverage B Z.1 Z.property E := by
    rw [SmallEtale.mem_precoverage_iff]
    refine ⟨PreZeroHypercover.empty E, by simp, ?_⟩
    change BigEtaleOver.IsCovering B Z.1 Z.property _
    change B.IsCovering _
    refine ⟨?_, ?_⟩
    · simp only [IsEtaleCovering, PreZeroHypercover.presieve₀_map,
        PreZeroHypercover.presieve₀_empty, Presieve.map_bot, Scheme.etalePrecoverage]
      exact Scheme.bot_mem_precoverage (P := @Etale) _
    · simp
  have hbot : (⊥ : Sieve E) ∈ SmallEtale.topology B Z.1 Z.property E := by
    simpa using (SmallEtale.precoverage B Z.1 Z.property).generate_mem_toGrothendieck hbotPre
  exact Types.isTerminalEquivUnique _ (G.isTerminalOfBotCover E hbot)

/-- The range of the underlying map of a composite lies in the range of the last map. -/
private theorem range_comp_base_subset {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    Set.range (f ≫ g).base ⊆ Set.range g.base :=
  Set.range_comp_subset_range f.base g.base

/-- A geometric point of `X` missing the closed subscheme has an affine étale neighbourhood
whose image is disjoint from it. -/
private theorem exists_open_neighborhood_away_from_closed
    (B : BigEtaleSite.{u}) {Z X : B.Scheme}
    (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]
    (s : GeometricPoint X.1)
    (hs : s.hom default ∉ Set.range (B.inclusion.map i).base) :
    ∃ (V : SmallEtale B X.1 X.property)
      (_ : (geometricPointFiber B X.1 X.property s).obj V),
      Disjoint (Set.range (B.inclusion.map V.obj.hom).base)
        (Set.range (B.inclusion.map i).base) := by
  let f := B.inclusion.map i
  let U : X.1.Opens :=
    ⟨(Set.range f.base)ᶜ,
      (IsClosedImmersion.isClosedEmbedding f).isClosed_range.isOpen_compl⟩
  have hpoint : s.hom default ∈ U := hs
  obtain ⟨R, j, hj, hxj, hsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := s.hom default) (U := U) hpoint
  have hrange : Set.range s.hom.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    exact Subsingleton.elim a default ▸ hxj
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType j).trans_lt X.property
  let V : SmallEtale B X.1 X.property :=
    ⟨Over.mk (ObjectProperty.homMk j : B.obj (Spec R) hR ⟶ B.obj X.1 X.property), by
      show Etale j
      infer_instance⟩
  have hp : (geometricPointFiber B X.1 X.property s).obj V :=
    ⟨IsOpenImmersion.lift j s.hom hrange, by
      simpa [V] using IsOpenImmersion.lift_fac j s.hom hrange⟩
  refine ⟨V, hp, Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨y, rfl⟩ hyx
  exact hsub ⟨y, rfl⟩ hyx

/-- The stalk of the direct image from a closed subscheme is a singleton
outside that subscheme. -/
@[stacks 04FX "stalk_pushforward_outside"]
public theorem smallEtalePushforward_stalk_unique_of_not_mem_range
    (B : BigEtaleSite.{u}) {Z X : B.Scheme}
    (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]
    (G : Sheaf (SmallEtale.topology B Z.1 Z.property)
      (Type (max (u + 1) v)))
    (s : GeometricPoint X.1)
    (hs : s.hom default ∉ Set.range (B.inclusion.map i).base) :
    ∃! _ : (etaleStalk B X.1 X.property s
      (((smallEtaleBaseChange B i).sheafPushforwardContinuous
        (Type (max (u + 1) v))
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)).obj G).obj), True := by
  classical
  let P := smallEtaleBaseChange B i
  let H := P.sheafPushforwardContinuous (Type (max (u + 1) v))
    (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B Z.1 Z.property)
  let J := geometricPointFiber B X.1 X.property s
  let I := J.Elementsᵒᵖ
  let F : I ⥤ Type (max (u + 1) v) := (CategoryOfElements.π J).op ⋙ (H.obj G).obj
  obtain ⟨V, p, hdisjV⟩ := exists_open_neighborhood_away_from_closed B i s hs
  let e₀ : J.Elements := J.elementsMk V p
  let e₀' : I := op e₀
  have : IsFiltered I := inferInstance
  have hF : ∀ a : I, ∃ b : I, Nonempty (a ⟶ b) ∧
      Subsingleton (F.obj b) ∧ Nonempty (F.obj b) := by
    intro a
    let c := IsFiltered.max a e₀'
    let α : c.unop ⟶ e₀ := (IsFiltered.rightToMax a e₀').unop
    let C : SmallEtale B X.1 X.property := c.unop.obj
    let g := (SmallEtale.inclusion B X.1 X.property).map α.hom
    have hOver : g.left ≫ V.obj.hom = C.obj.hom := Over.w g
    have hfac : B.inclusion.map g.left ≫ B.inclusion.map V.obj.hom =
        B.inclusion.map C.obj.hom := by
      rw [← Functor.map_comp, hOver]
    have hsub : Set.range (B.inclusion.map C.obj.hom).base ⊆
        Set.range (B.inclusion.map V.obj.hom).base := by
      rw [← hfac]
      exact range_comp_base_subset _ _
    have hEmpty : IsEmpty ((SmallEtale.toScheme B Z.1 Z.property).obj (P.obj C)) := by
      show IsEmpty (B.inclusion.obj ((Over.pullback i).obj C.obj).left)
      refine ⟨fun w => ?_⟩
      let fst := B.inclusion.map (Limits.pullback.fst C.obj.hom i)
      let snd := B.inclusion.map (Limits.pullback.snd C.obj.hom i)
      have hEq : fst ≫ B.inclusion.map C.obj.hom = snd ≫ B.inclusion.map i := by
        rw [← Functor.map_comp, ← Functor.map_comp, Limits.pullback.condition]
      have hw : (fst ≫ B.inclusion.map C.obj.hom).base w ∈
          Set.range (snd ≫ B.inclusion.map i).base := hEq ▸ ⟨w, rfl⟩
      exact Set.disjoint_left.mp (hdisjV.mono_left hsub) (range_comp_base_subset _ _ ⟨w, rfl⟩)
        (range_comp_base_subset _ _ hw)
    have hUnique : Unique (F.obj c) := by
      show Unique ((H.obj G).obj.obj (op C))
      show Unique (G.obj.obj (op (P.obj C)))
      exact unique_sections_of_empty_etale_object B Z G (P.obj C) hEmpty
    refine ⟨c, ⟨IsFiltered.leftToMax a e₀'⟩, ?_⟩
    let := hUnique
    exact ⟨inferInstance, ⟨default⟩⟩
  let := unique_colimit_of_refinements F hF
  show ∃! _ : colimit F, True
  exact ⟨default, trivial, fun _ _ => Subsingleton.elim _ _⟩

end AlgebraicGeometry
