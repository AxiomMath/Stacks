module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition

/-!
# A point in every member of a descending family of nonempty affine opens

Let `U` be a scheme and let `V` be a family of affine opens of `U`, nonempty and directed
downwards — for instance a descending sequence `V 0 ⊇ V 1 ⊇ V 2 ⊇ …`. Then some point of `U`
lies in every `V i`.

## Main results

* `AlgebraicGeometry.Scheme.exists_mem_of_directed_isAffineOpen`: for a family of nonempty
  affine opens indexed by a nonempty directed preorder of the scheme's own universe and
  antitone in the index, a point of `U` lying in all of them.
* `AlgebraicGeometry.Scheme.exists_mem_iInter_of_antitone_isAffineOpen`: the same for a
  descending sequence `V : ℕ → U.Opens`.
* `AlgebraicGeometry.Scheme.exists_fromSpecResidueField_factorsThrough_of_antitone_isAffineOpen`
  packages that point as a morphism from the spectrum of a field factoring through every member
  of the sequence.

## Implementation notes

The index type of the general statement lives in the scheme's universe, as the existence of the
limit of the members requires; the sequence version is taken at `ULift.{u} ℕ`.

## References

* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {U : Scheme.{u}} {ι : Type u} [Preorder ι]

/-- The inverse system of the members of an antitone family of opens of `U`, indexed by the
opposite of the index preorder, with the inclusions as transition morphisms. -/
private noncomputable def descendingOpensDiagram (V : ι → U.Opens) (hV : Antitone V) :
    ιᵒᵖ ⥤ Scheme.{u} where
  obj i := (V i.unop : Scheme.{u})
  map {_ _} f := U.homOfLE (hV (leOfHom f.unop))
  map_id _ := Scheme.homOfLE_rfl _ _
  map_comp {_ _ _} _ _ := (U.homOfLE_homOfLE _ _).symm

/-- The open immersion of a member of the system into `U`. -/
private def descendingOpensDiagramι (V : ι → U.Opens) (hV : Antitone V) (i : ιᵒᵖ) :
    (descendingOpensDiagram V hV).obj i ⟶ U := (V i.unop).ι

private theorem descendingOpensDiagram_map_ι (V : ι → U.Opens) (hV : Antitone V) {i j : ιᵒᵖ}
    (f : i ⟶ j) : (descendingOpensDiagram V hV).map f ≫ descendingOpensDiagramι V hV j
      = descendingOpensDiagramι V hV i :=
  U.homOfLE_ι (hV (leOfHom f.unop))

private theorem range_descendingOpensDiagramι (V : ι → U.Opens) (hV : Antitone V) (i : ι) :
    Set.range (descendingOpensDiagramι V hV (Opposite.op i)).base = (V i : Set U) :=
  Scheme.Opens.range_ι (V i)

/-- A nonempty family of nonempty affine opens of a scheme `U`, antitone in a directed index
preorder, has a point of `U` in every member. -/
theorem exists_mem_of_directed_isAffineOpen [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (V : ι → U.Opens) (hanti : Antitone V) (haff : ∀ i, IsAffineOpen (V i))
    (hne : ∀ i, (V i : Set U).Nonempty) : ∃ x : U, ∀ i, x ∈ V i := by
  classical
  have hiA : ∀ i : ιᵒᵖ, IsAffine ((descendingOpensDiagram V hanti).obj i) :=
    fun i => haff i.unop
  have hcpt : ∀ i : ιᵒᵖ, CompactSpace ((descendingOpensDiagram V hanti).obj i) := fun i => by
    have := hiA i; infer_instance
  have hnei : ∀ i : ιᵒᵖ, Nonempty ((descendingOpensDiagram V hanti).obj i) := fun i => by
    obtain ⟨x, hx⟩ := hne i.unop
    exact ⟨⟨x, hx⟩⟩
  have hah : ∀ {i j : ιᵒᵖ} (f : i ⟶ j),
      IsAffineHom ((descendingOpensDiagram V hanti).map f) := by
    intro i j f
    have h₁ : IsAffine ((V i.unop : Scheme.{u})) := haff i.unop
    have h₂ : IsAffine ((V j.unop : Scheme.{u})) := haff j.unop
    exact inferInstanceAs (IsAffineHom (U.homOfLE (hanti (leOfHom f.unop))))
  set c := (affineLimitCone (descendingOpensDiagram V hanti)).cone with hc
  obtain ⟨z⟩ := Scheme.nonempty_of_isLimit (descendingOpensDiagram V hanti) c
    (affineLimitCone (descendingOpensDiagram V hanti)).isLimit
  have hconst : ∀ {i j : ιᵒᵖ} (_ : i ⟶ j),
      c.π.app i ≫ descendingOpensDiagramι V hanti i
        = c.π.app j ≫ descendingOpensDiagramι V hanti j := by
    intro i j f
    rw [← c.w f, Category.assoc, descendingOpensDiagram_map_ι]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨(c.π.app (Opposite.op i₀) ≫ descendingOpensDiagramι V hanti (Opposite.op i₀)).base z,
    fun i => ?_⟩
  obtain ⟨j, hj₀, hji⟩ := directed_of (· ≤ ·) i₀ i
  have e := congrArg (fun f => f.base z)
    ((hconst (j := Opposite.op i₀) (Opposite.op (homOfLE hj₀))).symm.trans
      (hconst (j := Opposite.op i) (Opposite.op (homOfLE hji))))
  change _ ∈ (V i : Set U)
  rw [e, ← range_descendingOpensDiagramι V hanti i]
  exact ⟨(c.π.app (Opposite.op i)).base z, rfl⟩

/-- A descending sequence of nonempty affine opens of a scheme has a point of the scheme in
every member. -/
theorem exists_mem_iInter_of_antitone_isAffineOpen (V : ℕ → U.Opens) (hanti : Antitone V)
    (haff : ∀ n, IsAffineOpen (V n)) (hne : ∀ n, (V n : Set U).Nonempty) :
    ∃ x : U, ∀ n, x ∈ V n := by
  obtain ⟨x, hx⟩ := exists_mem_of_directed_isAffineOpen (ι := ULift.{u} ℕ)
    (fun i => V i.down) (fun _ _ h => hanti h) (fun i => haff i.down) fun i => hne i.down
  exact ⟨x, fun n => hx ⟨n⟩⟩

/-- A descending sequence of nonempty affine opens of a scheme `U` has a point `x` of `U`
such that `U.fromSpecResidueField x` factors through every member. -/
theorem exists_fromSpecResidueField_factorsThrough_of_antitone_isAffineOpen (V : ℕ → U.Opens)
    (hanti : Antitone V) (haff : ∀ n, IsAffineOpen (V n)) (hne : ∀ n, (V n : Set U).Nonempty) :
    ∃ x : U, ∀ n, ∃ g : Spec (U.residueField x) ⟶ (V n : Scheme.{u}),
      g ≫ (V n).ι = U.fromSpecResidueField x := by
  obtain ⟨x, hx⟩ := exists_mem_iInter_of_antitone_isAffineOpen V hanti haff hne
  refine ⟨x, fun n => ⟨IsOpenImmersion.lift (V n).ι (U.fromSpecResidueField x) ?_, ?_⟩⟩
  · rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.2 (hx n)
  · exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme

end
