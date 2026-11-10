module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocalStructure.DisjointDecomposition

/-!
# Fibres of a closed subset proper over the base of an étale morphism

Let `f : X ⟶ S` be an étale morphism of schemes and let `Z` be a closed subset of `X` which is
proper over `S`. Since `f` is locally quasi-finite, `Z` meets every fibre of `f` in a finite
set, and since `Z` is proper over `S` its image is closed, so a point of `S` missed by that
image has a whole Zariski open neighbourhood missed by it.

Combining the finiteness with the étale-local structure of a separated étale morphism
decomposes, after an étale base change, the ambient scheme into finitely many pairwise disjoint
copies of the new base together with a remainder which does not meet `Z` over the
distinguished point.

## Main results

* `AlgebraicGeometry.finite_fiber_of_isProperOver` — a closed subset proper over the base meets
  each fibre of an étale morphism in a finite set.
* `AlgebraicGeometry.exists_opens_mem_disjoint_image_of_isProperOver` — a point of the base
  outside the image of a closed subset proper over the base has a Zariski open neighbourhood
  disjoint from that image.
* `AlgebraicGeometry.exists_etaleNeighborhood_openCopies_decomposition_of_isProperOver` — the
  étale-local decomposition of a separated étale morphism adapted to a closed subset proper over
  the base.

## Implementation notes

The decomposition is obtained from the general étale-local structure theorem by taking for the
finite family of points the whole intersection of `Z` with the fibre, which is finite by the
first result. The structure theorem indexes its copies of the base by a sigma type over that
family; the statement here re-indexes them by `Fin n`, which is what a consumer wanting to sum
over the copies needs.

## References

* [Stacks Project, Tag 04HM](https://stacks.math.columbia.edu/tag/04HM)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Function

universe u

namespace AlgebraicGeometry

/-- A closed subset proper over the base meets each fibre of an étale morphism in a finite
set. -/
public theorem finite_fiber_of_isProperOver {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (Z : Closeds X) (hZ : IsProperOver f Z) (s : S) :
    {x : X | x ∈ Z ∧ f x = s}.Finite := by
  have := (locallyQuasiFinite_of_etale f).2
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g := I.subschemeι ≫ f
  have : IsProper g := hZ
  have : LocallyQuasiFinite g := inferInstance
  have hr : Set.range I.subschemeι = Z := by
    simp [I, Scheme.IdealSheafData.range_subschemeι]
  convert (g.finite_preimage_singleton s).image I.subschemeι using 1
  rw [show g ⁻¹' {s} = I.subschemeι ⁻¹' (f ⁻¹' {s}) from rfl,
    Set.image_preimage_eq_inter_range, hr]
  ext x
  simp [and_comm]

/-- A point of the base which is not the image of any point of a closed subset proper over the
base has a Zariski open neighbourhood disjoint from the image of that subset. -/
public theorem exists_opens_mem_disjoint_image_of_isProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (Z : Closeds X) (hZ : IsProperOver f Z) (s : S)
    (hs : ∀ x ∈ Z, f x ≠ s) :
    ∃ O : S.Opens, s ∈ O ∧ ∀ x ∈ Z, f x ∉ O :=
  ⟨⟨(f.base '' (Z : Set X))ᶜ,
    (isClosed_image_of_isProperOver f (𝟙 S) f (by simp) Z hZ).isOpen_compl⟩,
    fun ⟨x, hx, hxs⟩ => hs x hx hxs, fun x hx h => h ⟨x, hx, rfl⟩⟩

/-- After an étale base change, a separated étale morphism is the disjoint union of finitely many
copies of the new base together with a remainder whose distinguished fibre misses a given closed
subset proper over the base. -/
public theorem exists_etaleNeighborhood_openCopies_decomposition_of_isProperOver
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f]
    (Z : Closeds X) (hZ : IsProperOver f Z) (s : S) :
    ∃ (U : EtaleNeighborhood S s) (W : (pullback f U.toBase).Opens) (n : ℕ)
      (V : Fin n → (pullback f U.toBase).Opens),
      (⨆ i, V i) ⊔ W = ⊤ ∧ Pairwise (Disjoint on V) ∧ (∀ i, Disjoint (V i) W) ∧
        (∀ i, IsIso ((V i).ι ≫ pullback.snd f U.toBase)) ∧
        ∀ z : (pullback f U.toBase : Scheme), pullback.snd f U.toBase z = U.point →
          pullback.fst f U.toBase z ∈ Z → ∃ i, z ∈ V i := by
  classical
  let T := {x : X | x ∈ Z ∧ f x = s}
  have : Fintype T := (finite_fiber_of_isProperOver f Z hZ s).fintype
  let x : Fin (Fintype.card T) → X := fun i => (Fintype.equivFin T).symm i
  have hx (i) : f (x i) = s := ((Fintype.equivFin T).symm i).property.2
  obtain ⟨N, W, m, V, hcover, hpair, hdis, hiso, hW, _⟩ :=
    exists_etaleNeighborhood_disjoint_openCopies_decomposition f _ x s hx
      (fun i => (etale_iff_forall_etaleAt f).mp inferInstance (x i))
  let e := Fintype.equivFin (Σ i, Fin (m i))
  refine ⟨N, W, Fintype.card (Σ i, Fin (m i)), V ∘ e.symm, ?_,
    fun i j hij => hpair (by simpa using hij), fun i => hdis (e.symm i),
    fun i => hiso (e.symm i), ?_⟩
  · simpa only [Function.comp_def, Equiv.iSup_comp, sSup_range] using hcover
  · intro z hz hzZ
    have hzW : z ∉ W := by
      intro hzW
      let w : (↑W : Scheme) := ⟨z, hzW⟩
      obtain ⟨w', hw'⟩ : w ∈ Set.range ((W.ι ≫ pullback.snd f N.toBase).fiberι N.point) := by
        rw [Scheme.Hom.range_fiberι]
        exact hz
      have hf : f (pullback.fst f N.toBase z) = s :=
        calc
          _ = N.toBase (pullback.snd f N.toBase z) :=
            congrArg (fun h : pullback f N.toBase ⟶ S => h z)
              (pullback.condition (f := f) (g := N.toBase))
          _ = s := by rw [hz, N.map_point]
      let t : T := ⟨pullback.fst f N.toBase z, hzZ, hf⟩
      apply hW w' ((Fintype.equivFin T) t)
      change pullback.fst f N.toBase (W.ι
        ((W.ι ≫ pullback.snd f N.toBase).fiberι N.point w')) = x _
      rw [hw']
      exact congrArg Subtype.val ((Fintype.equivFin T).symm_apply_apply t).symm
    have hzcover : z ∈ sSup (Set.range V) ⊔ W := by
      rw [hcover]
      trivial
    rcases hzcover with hzV | hzW'
    · rcases TopologicalSpace.Opens.mem_sSup.mp hzV with ⟨O, ⟨i, rfl⟩, hi⟩
      exact ⟨e i, by simpa using hi⟩
    · exact absurd hzW' hzW

end AlgebraicGeometry

end
