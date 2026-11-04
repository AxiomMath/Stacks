module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionQuotient
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RightExactness

/-!
# The completed tensor product of a quotient

Let `A → B` and `A → R` be linearly topologized algebras and let `π : R ↠ C` be a continuous
open surjection of `A`-algebras — the quotient map `R → R ⧸ K` by an ideal, in the intended
application.  Then

  `B ⊗̂[A] C  ≃  (B ⊗̂[A] R) ⧸ closure (ker π · (B ⊗̂[A] R))`.

This is right-exactness of the completed tensor product in the second variable.  It is the
identification `B ⊗̂_A (R ⧸ K) ≃ (B ⊗̂_A R) ⧸ K · (B ⊗̂_A R)` that the third paragraph of Tag
0GGR needs in order to replace `C` by the restricted power series ring it is a quotient of;
Tag 0AMZ is the special case `R = A`, which does not apply there because the ideal is an ideal
of `A{x₁, …, xₙ}` and not of `A`.

The proof is the composite of three facts, each proved elsewhere: the ordinary tensor product
is right exact and `id ⊗ π` is an open surjection
(`TopologicalRing.isOpenMap_tensorProduct_lTensor`), so `B ⊗[A] C` carries the quotient
topology of `B ⊗[A] R`; and the completion of a quotient is the quotient of the completion by
the closure of the extended ideal (`TopologicalRing.completionQuotientRingEquiv`, which is
Tags 0ARZ and 0AS0).

## Main results

* `TopologicalRing.exists_completedTensorProductQuotientRingEquiv`: the isomorphism, together
  with its compatibility with the canonical maps from `B ⊗[A] R`.
* `TopologicalRing.exists_completedTensorProductQuotientIdealRingEquiv`: the same for the
  quotient by an ideal, with the ideal written intrinsically as the extension of `K` along the
  canonical map `R → B ⊗̂[A] R`.  This is the form the third paragraph of Tag 0GGR uses.
* `TopologicalRing.isLinearTopology_quotient`: the quotient of a linearly topologized ring by
  an ideal is linearly topologized.
* `TopologicalRing.ker_tensorProduct_map_quotientMk`: the kernel of `id ⊗ (R → R ⧸ K)` is the
  extension of `K` to `B ⊗[A] R`.

## Implementation notes

The closure is genuinely present at this generality and the statement does not hide it: it may
be removed exactly when `ker π · (B ⊗̂[A] R)` is a closed ideal, which holds for instance when
`B ⊗̂[A] R` is Noetherian and adically complete, and is not assumed here.

The general statement takes the second factor to be an abstract topological ring `C` with a
continuous open surjection from `R`, rather than literally `R ⧸ K`; the ideal-quotient case is
the corollary `exists_completedTensorProductQuotientIdealRingEquiv`.
`Function.Surjective`, `Continuous` and `IsOpenMap` for `Ideal.Quotient.mk K` are
`Ideal.Quotient.mk_surjective`, `continuous_quot_mk` and `QuotientRing.isOpenMap_coe`.

Specialising to `C := R ⧸ K` has to apply the general statement with `@` and supply the three
`C`-instances positionally.  The reason is not a defeq failure: at the point of application the
`TopologicalSpace (R ⧸ K)` argument is still an unassigned metavariable — it is pinned only
when the result is matched against the goal — so instance search for `IsTopologicalRing (R ⧸ K)`
runs with a metavariable in the instance argument and fails, and no `haveI` in the local context
can repair that.  Passing `inferInstance` for the topology assigns it first, after which
`topologicalRing_quotient K` and `isLinearTopology_quotient K` are accepted.

The tensor product topology is not a global instance, so it and its uniformity are supplied by
hand, as elsewhere in this directory.

## References

* [Stacks Project, Tag 0ARZ](https://stacks.math.columbia.edu/tag/0ARZ)
* [Stacks Project, Tag 0AS0](https://stacks.math.columbia.edu/tag/0AS0)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace TopologicalRing

section

open UniformSpace
open scoped TensorProduct Topology

variable {A B R C : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C]
  [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- **Right exactness of the completed tensor product in the second variable.**  For a
continuous open surjection `π : R ↠ C` of linearly topologized `A`-algebras, the completed
tensor product `B ⊗̂[A] C` is the quotient of `B ⊗̂[A] R` by the closure of the extension of
`ker (id ⊗ π)`.

The isomorphism is compatible with the canonical maps from `B ⊗[A] R`: it takes the class of
the image of `t` to the image of `(id ⊗ π) t`. -/
public theorem exists_completedTensorProductQuotientRingEquiv
    (π : R →ₐ[A] C) (hsurj : Function.Surjective π) (hcont : Continuous π)
    (hopen : IsOpenMap π)
    (hcount : letI : TopologicalSpace (B ⊗[A] R) :=
        tensorProductTopology (R := A) (M := B) (N := R)
      (nhds (0 : B ⊗[A] R)).IsCountablyGenerated) :
    letI : TopologicalSpace (B ⊗[A] R) := tensorProductTopology (R := A) (M := B) (N := R)
    letI : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] R) := tensorProductUniformSpace (R := A) (M := B) (N := R)
    letI : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
    ∃ e : (CompletedTensorProduct (R := A) (M := B) (N := R) ⧸
        Ideal.closure ((RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B) π).toRingHom).map
          (Completion.coeRingHom : (B ⊗[A] R) →+* Completion (B ⊗[A] R)))) ≃+*
        CompletedTensorProduct (R := A) (M := B) (N := C),
      ∀ t : B ⊗[A] R,
        e (Ideal.Quotient.mk _ (t : CompletedTensorProduct (R := A) (M := B) (N := R))) =
          ((Algebra.TensorProduct.map (AlgHom.id A B) π t : B ⊗[A] C) :
            CompletedTensorProduct (R := A) (M := B) (N := C)) := by
  let _ : TopologicalSpace (B ⊗[A] R) := tensorProductTopology (R := A) (M := B) (N := R)
  let _ : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
  let _ : UniformSpace (B ⊗[A] R) := tensorProductUniformSpace (R := A) (M := B) (N := R)
  let _ : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
  let _ : IsTopologicalRing (B ⊗[A] R) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := R)
  let _ : IsTopologicalRing (B ⊗[A] C) :=
    tensorProduct_isTopologicalRing (R := A) (A := B) (B := C)
  let _ : IsUniformAddGroup (B ⊗[A] R) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := R)
  let _ : IsUniformAddGroup (B ⊗[A] C) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  set ψ : (B ⊗[A] R) →+* (B ⊗[A] C) :=
    (Algebra.TensorProduct.map (AlgHom.id A B) π).toRingHom
  have hψsurj : Function.Surjective ψ :=
    surjective_tensorProduct_lTensor (M := B) π.toLinearMap hsurj
  have hψcont : Continuous ψ :=
    continuous_algebraTensorProduct_map (AlgHom.id A B) π continuous_id hcont
  have hψopen : IsOpenMap ψ :=
    isOpenMap_tensorProduct_lTensor (M := B) π.toLinearMap hsurj hopen
  set J : Ideal (B ⊗[A] R) := RingHom.ker ψ
  let _ : UniformSpace ((B ⊗[A] R) ⧸ J) :=
    IsTopologicalAddGroup.rightUniformSpace ((B ⊗[A] R) ⧸ J)
  let _ : IsUniformAddGroup ((B ⊗[A] R) ⧸ J) := isUniformAddGroup_of_addCommGroup
  -- the algebraic quotient, as a topological ring isomorphism
  set e₀ : ((B ⊗[A] R) ⧸ J) ≃+* (B ⊗[A] C) :=
    RingHom.quotientKerEquivOfSurjective hψsurj
  have he₀cont : Continuous (e₀ : ((B ⊗[A] R) ⧸ J) → (B ⊗[A] C)) := by
    rw [(QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous_iff]
    exact hψcont.congr fun x =>
      (RingHom.quotientKerEquivOfSurjective_apply_mk hψsurj x).symm
  have he₀symm : Continuous (e₀.symm : (B ⊗[A] C) → ((B ⊗[A] R) ⧸ J)) := by
    rw [(IsOpenQuotientMap.mk hψsurj hψcont hψopen).isQuotientMap.continuous_iff]
    exact continuous_quot_mk.congr fun x =>
      (RingHom.quotientKerEquivOfSurjective_symm_apply hψsurj x).symm
  refine ⟨(completionQuotientRingEquiv J hcount).trans
    (Completion.mapRingEquiv e₀ he₀cont he₀symm), fun t => ?_⟩
  have h1 : completionQuotientRingEquiv J hcount
      (Ideal.Quotient.mk _ (t : Completion (B ⊗[A] R))) =
      ((Ideal.Quotient.mk J t : (B ⊗[A] R) ⧸ J) : Completion ((B ⊗[A] R) ⧸ J)) := by
    rw [completionQuotientRingEquiv]
    exact completionQuotientRingHom_coe J t
  rw [RingEquiv.trans_apply, h1]
  exact (Completion.mapRingHom_coe he₀cont (Ideal.Quotient.mk J t)).trans
    (congrArg (fun y : B ⊗[A] C => (y : Completion (B ⊗[A] C)))
      (RingHom.quotientKerEquivOfSurjective_apply_mk hψsurj t))

/-- **The quotient of a linearly topologized ring by an ideal is linearly topologized.**  The
quotient map is an open surjection, so the images of the open ideals of `R` are a fundamental
system of open ideals of `R ⧸ K`. -/
public theorem isLinearTopology_quotient (K : Ideal R) :
    IsLinearTopology (R ⧸ K) (R ⧸ K) := by
  have hnhds : Filter.map (Ideal.Quotient.mk K) (nhds (0 : R)) = nhds (0 : R ⧸ K) := by
    simpa only [map_zero] using (QuotientRing.isOpenQuotientMap_mk K).map_nhds_eq (0 : R)
  refine IsLinearTopology.mk_of_hasBasis (R ⧸ K)
    (s := fun L : Ideal R => L.map (Ideal.Quotient.mk K))
    (p := fun L : Ideal R => IsOpen (L : Set R)) ?_
  rw [← hnhds]
  refine ((IsLinearTopology.hasBasis_open_ideal (R := R)).map
    (Ideal.Quotient.mk K)).to_hasBasis (fun L hL => ⟨L, hL, ?_⟩) (fun L hL => ⟨L, hL, ?_⟩)
  all_goals rw [Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]

/-- **The kernel of `id ⊗ (R → R ⧸ K)` is the extension of `K`.**  This is the algebraic
right-exactness of the tensor product, read off from Mathlib's
`Algebra.TensorProduct.tensorQuotientEquiv`, which identifies `B ⊗[A] (R ⧸ K)` with
`(B ⊗[A] R) ⧸ K · (B ⊗[A] R)`. -/
public theorem ker_tensorProduct_map_quotientMk (K : Ideal R) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B)
        (Ideal.Quotient.mkₐ A K)).toRingHom =
      K.map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom := by
  set ψ : (B ⊗[A] R) →+* (B ⊗[A] (R ⧸ K)) :=
    (Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A K)).toRingHom
  set 𝔞 : Ideal (B ⊗[A] R) :=
    K.map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom
  set ε : (B ⊗[A] (R ⧸ K)) ≃+* ((B ⊗[A] R) ⧸ 𝔞) :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A R B K).toRingEquiv
  have hcomp : (ε : (B ⊗[A] (R ⧸ K)) →+* ((B ⊗[A] R) ⧸ 𝔞)).comp ψ =
      Ideal.Quotient.mk 𝔞 := by
    refine RingHom.ext fun x => ?_
    induction x with
    | zero => simp
    | tmul b r => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : RingHom.ker ((ε : (B ⊗[A] (R ⧸ K)) →+* ((B ⊗[A] R) ⧸ 𝔞)).comp ψ) =
      RingHom.ker ψ := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply]
    exact ⟨fun h => ε.injective (by simpa using h), fun h => by rw [h, map_zero]⟩
  rw [← hinj, hcomp, Ideal.mk_ker]

/-- **Right exactness of the completed tensor product in the second variable, for the quotient
by an ideal.**  This is the statement the third paragraph of Tag 0GGR uses:

  `B ⊗̂[A] (R ⧸ K)  ≃  (B ⊗̂[A] R) ⧸ closure (K · (B ⊗̂[A] R))`,

the ideal being the extension of `K` along the canonical map `R → B ⊗̂[A] R`. -/
public theorem exists_completedTensorProductQuotientIdealRingEquiv (K : Ideal R)
    (hcount : letI : TopologicalSpace (B ⊗[A] R) :=
        tensorProductTopology (R := A) (M := B) (N := R)
      (nhds (0 : B ⊗[A] R)).IsCountablyGenerated) :
    letI : TopologicalSpace (B ⊗[A] R) := tensorProductTopology (R := A) (M := B) (N := R)
    letI : TopologicalSpace (B ⊗[A] (R ⧸ K)) :=
      tensorProductTopology (R := A) (M := B) (N := R ⧸ K)
    letI : UniformSpace (B ⊗[A] R) := tensorProductUniformSpace (R := A) (M := B) (N := R)
    letI : UniformSpace (B ⊗[A] (R ⧸ K)) :=
      tensorProductUniformSpace (R := A) (M := B) (N := R ⧸ K)
    ∃ e : (CompletedTensorProduct (R := A) (M := B) (N := R) ⧸
        Ideal.closure (K.map
          ((Completion.coeRingHom : (B ⊗[A] R) →+* Completion (B ⊗[A] R)).comp
            (Algebra.TensorProduct.includeRight :
              R →ₐ[A] B ⊗[A] R).toRingHom))) ≃+*
        CompletedTensorProduct (R := A) (M := B) (N := R ⧸ K),
      ∀ t : B ⊗[A] R,
        e (Ideal.Quotient.mk _ (t : CompletedTensorProduct (R := A) (M := B) (N := R))) =
          ((Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A K) t :
              B ⊗[A] (R ⧸ K)) :
            CompletedTensorProduct (R := A) (M := B) (N := R ⧸ K)) := by
  obtain ⟨e, he⟩ := @exists_completedTensorProductQuotientRingEquiv A B R (R ⧸ K)
    _ _ _ _ _ _ _ _ _ _ _ _ _ inferInstance (topologicalRing_quotient K)
    (isLinearTopology_quotient K) (Ideal.Quotient.mkₐ A K) Ideal.Quotient.mk_surjective
    continuous_quot_mk (QuotientRing.isOpenMap_coe K) hcount
  refine ⟨(Ideal.quotEquivOfEq ?_).trans e, fun t => ?_⟩
  · rw [ker_tensorProduct_map_quotientMk K, Ideal.map_map]
  · rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact he t

end

end TopologicalRing

end
