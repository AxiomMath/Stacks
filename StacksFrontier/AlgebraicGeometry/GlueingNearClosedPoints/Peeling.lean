module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.EquivalenceSinglePoint

/-!
# Peeling a point off a finite family of closed points

Let `s : I → S` be a finite family of pairwise distinct closed points of a scheme `S` with open
complement `U`. This file proves two facts about such a family, in the setting of
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q). If the inclusion of `U` is
quasi-compact, so is the inclusion of the open complement of any subfamily. The preimage of `U`
in the local scheme `Spec 𝒪_{S, s i}` does not change when the points of the family other than
`s i` are put back into `U`, since those points are not in the image of
`Spec 𝒪_{S, s i} ⟶ S`.

It also defines the canonical functor from schemes of finite presentation over a scheme `T` to
the gluing data attached to a family of commutative squares, and shows that the canonical
restriction functor of Tag 0E8Q is of that form.

## Main definitions

* `AlgebraicGeometry.glueingDataOf`: gluing data for a family of pairs of maps `O i ⟶ U`,
  `O i ⟶ L i`, as the iso-comma category of the two base-change functors.
* `AlgebraicGeometry.restrictionFunctorOf`: the canonical functor from schemes of finite
  presentation over `T` to such gluing data, attached to a family of commutative squares.

## Main results

* `AlgebraicGeometry.canonicalRestrictionFunctor_eq`: the canonical restriction functor of
  Tag 0E8Q is the canonical functor attached to the family of base-change squares of the
  inclusion of the open complement and the maps from the local schemes.
* `AlgebraicGeometry.quasiCompact_ι_complementOfClosedPoints_comp`: the open complement of a
  subfamily again has quasi-compact inclusion.
* `AlgebraicGeometry.preimage_fromSpecStalk_complementOfClosedPoints`: the preimage of the open
  complement in the local scheme at a point of the family does not change if the other points of
  the family are put back.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-! ### Gluing data for a family of commutative squares -/

/-- Gluing data for a family of pairs of maps `a i : O i ⟶ U` and `b i : O i ⟶ L i`: a scheme of
finite presentation over `U`, a family of schemes of finite presentation over the `L i`, and an
isomorphism of the two restrictions to each `O i`. -/
abbrev glueingDataOf {I : Type u} {U : Scheme.{u}} {L O : I → Scheme.{u}}
    (a : ∀ i, O i ⟶ U) (b : ∀ i, O i ⟶ L i) :=
  IsoComma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
    (Functor.pi fun i ↦ finitePresentationBaseChange (b i))

/-- The canonical functor to gluing data of `AlgebraicGeometry.restrictionFunctorOf`, before
cutting the comma category down to the objects whose comparison is invertible. -/
noncomputable def restrictionFunctorOfComma {T U : Scheme.{u}} {I : Type u} {L O : I → Scheme.{u}}
    (c : U ⟶ T) (d : ∀ i, L i ⟶ T) (a : ∀ i, O i ⟶ U) (b : ∀ i, O i ⟶ L i)
    (h : ∀ i, a i ≫ c = b i ≫ d i) :
    FinitePresentationOver T ⥤
      Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
        (Functor.pi fun i ↦ finitePresentationBaseChange (b i)) where
  obj X := ⟨(finitePresentationBaseChange c).obj X,
    fun i ↦ (finitePresentationBaseChange (d i)).obj X,
    fun i ↦ (finitePresentationPullbackSquareIso (h i)).hom.app X⟩
  map f := ⟨(finitePresentationBaseChange c).map f,
    fun i ↦ (finitePresentationBaseChange (d i)).map f,
    funext fun i ↦ (finitePresentationPullbackSquareIso (h i)).hom.naturality f⟩
  map_id := by intro X; ext <;> simp
  map_comp := by intro X Y Z f g; ext <;> simp

/-- The canonical functor from schemes of finite presentation over `T` to the gluing data of a
family of commutative squares `a i ≫ c = b i ≫ d i`: a scheme over `T` is restricted along `c`
and along each `d i`, and its two restrictions to `O i` are identified by the base-change
associativity isomorphism of the square. -/
noncomputable def restrictionFunctorOf {T U : Scheme.{u}} {I : Type u} {L O : I → Scheme.{u}}
    (c : U ⟶ T) (d : ∀ i, L i ⟶ T) (a : ∀ i, O i ⟶ U) (b : ∀ i, O i ⟶ L i)
    (h : ∀ i, a i ≫ c = b i ≫ d i) :
    FinitePresentationOver T ⥤ glueingDataOf a b :=
  (show ObjectProperty (Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
      (Functor.pi fun i ↦ finitePresentationBaseChange (b i))) from fun X ↦ IsIso X.hom).lift
    (restrictionFunctorOfComma c d a b h)
    (fun X ↦ (isIso_pi_iff _).mpr fun i ↦ by
      change IsIso ((finitePresentationPullbackSquareIso (h i)).hom.app X)
      infer_instance)

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- The canonical restriction functor of **Stacks Project, Tag 0E8Q** is the canonical functor
attached to the family of commutative squares
`((S.fromSpecStalk (s i)) ∣_ U) ≫ U.ι = O i ≫ S.fromSpecStalk (s i)`, where `U` is the open
complement of the family and `O i` is the preimage of `U` in the local scheme at `s i`. -/
theorem canonicalRestrictionFunctor_eq :
    canonicalRestrictionFunctor s hs =
      restrictionFunctorOf (complementOfClosedPoints s hs).ι
        (fun i ↦ S.fromSpecStalk (s i))
        (fun i ↦ (S.fromSpecStalk (s i)) ∣_ (complementOfClosedPoints s hs))
        (fun i ↦ ((S.fromSpecStalk (s i)) ⁻¹ᵁ (complementOfClosedPoints s hs)).ι)
        (fun i ↦ morphismRestrict_ι (S.fromSpecStalk (s i)) (complementOfClosedPoints s hs)) :=
  rfl

/-! ### Quasi-compactness of the complement of a subfamily -/

/-- An open subscheme whose underlying set is retrocompact has quasi-compact inclusion.  This is
the converse of `AlgebraicGeometry.GlueingNearPoint.isRetrocompact_of_quasiCompact_ι`. -/
theorem quasiCompact_ι_of_isRetrocompact (V : S.Opens) (h : IsRetrocompact (V : Set S)) :
    QuasiCompact V.ι :=
  quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp h)

/-- A finite set is retrocompact. -/
theorem isRetrocompact_of_finite {F : Set S} (hF : F.Finite) : IsRetrocompact F :=
  fun _ _ _ ↦ (hF.inter_of_left _).isCompact

/-- A set containing a retrocompact set and differing from it by finitely many points is
retrocompact. -/
theorem isRetrocompact_of_diff_finite {A B : Set S} (hA : IsRetrocompact A) (hAB : A ⊆ B)
    (hfin : (B \ A).Finite) : IsRetrocompact B := by
  rw [← Set.union_sdiff_cancel hAB]
  exact hA.union (isRetrocompact_of_finite hfin)

/-- The open complement of a family of closed points is contained in that of any subfamily. -/
private theorem complementOfClosedPoints_le_comp {J : Type u} [Finite J] (g : J → I) :
    complementOfClosedPoints s hs ≤ complementOfClosedPoints (s ∘ g) (fun j ↦ hs (g j)) :=
  fun _ hx ↦ Set.mem_iInter.mpr fun j ↦ Set.mem_iInter.mp hx (g j)

include hs in
/-- If the open complement of a finite family of closed points has quasi-compact inclusion, so
does the open complement of any subfamily. -/
theorem quasiCompact_ι_complementOfClosedPoints_comp {J : Type u} [Finite J] (g : J → I)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    QuasiCompact (complementOfClosedPoints (s ∘ g) (fun j ↦ hs (g j))).ι := by
  refine quasiCompact_ι_of_isRetrocompact _ (isRetrocompact_of_diff_finite
    (GlueingNearPoint.isRetrocompact_of_quasiCompact_ι _ hqc)
    (complementOfClosedPoints_le_comp s hs g) ?_)
  refine (Set.finite_range s).subset ?_
  intro x hx
  by_contra hcon
  refine hx.2 (Set.mem_iInter.mpr fun i ↦ ?_)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  exact hcon ⟨i, heq.symm⟩

/-! ### The overlaps do not move -/

/-- A closed point distinct from `x` is not in the image of the local scheme at `x`: the preimage
of its complement in `Spec 𝒪_{S, x}` is everything. -/
theorem preimage_fromSpecStalk_compl_singleton_eq_top {x t : S}
    (ht : IsClosed ({t} : Set S)) (hxt : x ≠ t) :
    (S.fromSpecStalk x) ⁻¹ᵁ ⟨({t}ᶜ : Set S), ht.isOpen_compl⟩ = ⊤ := by
  apply TopologicalSpace.Opens.ext
  change (S.fromSpecStalk x).base ⁻¹' ({t}ᶜ : Set S) = Set.univ
  rw [Set.eq_univ_iff_forall]
  intro z
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  have hmem : (S.fromSpecStalk x).base z ∈ Set.range (S.fromSpecStalk x).base := ⟨z, rfl⟩
  rw [Scheme.range_fromSpecStalk, heq] at hmem
  exact hxt (hmem.mem_closed ht rfl)

include hs in
/-- Putting back the points of the family which are different from `x` does not change the
preimage, in the local scheme at `x`, of the open complement of the family. -/
theorem preimage_fromSpecStalk_complementOfClosedPoints {J : Type u} [Finite J] (g : J → I)
    {x : S} (hx : ∀ i, i ∉ Set.range g → s i ≠ x) :
    (S.fromSpecStalk x) ⁻¹ᵁ (complementOfClosedPoints s hs) =
      (S.fromSpecStalk x) ⁻¹ᵁ (complementOfClosedPoints (s ∘ g) (fun j ↦ hs (g j))) := by
  apply TopologicalSpace.Opens.ext
  apply Set.eq_of_subset_of_subset
  · exact fun z hz ↦ complementOfClosedPoints_le_comp s hs g hz
  · intro z hz
    refine Set.mem_iInter.mpr fun i ↦ ?_
    by_cases hi : i ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hi
      exact Set.mem_iInter.mp hz j
    · have htop := preimage_fromSpecStalk_compl_singleton_eq_top
        (mem_closedPoints_iff.mp (hs i)) (Ne.symm (hx i hi))
      have : z ∈ (S.fromSpecStalk x) ⁻¹ᵁ
          (⟨({s i}ᶜ : Set S), (mem_closedPoints_iff.mp (hs i)).isOpen_compl⟩ : S.Opens) := by
        rw [htop]
        trivial
      exact this

end AlgebraicGeometry

end
