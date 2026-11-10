module

public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyDevissage
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
import StacksCore.Tactic.StacksAttribute

/-!
# Eilenberg–Zilber for simplicial modules

For two simplicial modules `M` and `N` over a commutative ring, the Moore complex of the
degreewise tensor product `M ⊗ N` is quasi-isomorphic to the total tensor product of the Moore
complexes of `M` and of `N`, by the Alexander–Whitney map: in degree `n` its `(p, q)` component
restricts `M` to the front `p` vertices and `N` to the back `q` vertices.

The proof is a dévissage along the décalage. The décalage `dec N` is contractible over `N _⦋0⦌`,
so the comparison inverts it; the zeroth face `dec N ⟶ N` is a degreewise split epimorphism,
split by the zeroth degeneracy of `N`, so its degreewise kernel sits in a short complex of
simplicial modules which is split in every simplicial degree. Both sides of the comparison carry
that short complex to a short exact sequence of complexes, the comparison is a morphism between
the two, and the long exact homology sequences then raise by one the degree in which the
comparison is epi, and afterwards the degree in which it is mono. In degree zero the comparison
is the inclusion of the only summand, hence an isomorphism, which starts the induction.

## Main results

* `Stacks.ChaoticSite.quasiIso_alexanderWhitney`: Tag 08QD, the Eilenberg–Zilber theorem. The
  Alexander–Whitney map of two simplicial modules is a quasi-isomorphism.

## Implementation notes

The tag asserts that `s(M ⊗_B N)` *is quasi-isomorphic to* the total complex of
`s(M) ⊗_B s(N)`. What is proved here is sharper on two counts, and implies that assertion.

First, the quasi-isomorphism is not merely exhibited but identified: it is the
Alexander–Whitney map `alexanderWhitney M N`, the canonical comparison whose `(p, q)` component
restricts `M` to the front `p` vertices and `N` to the back `q` vertices.

Second, flatness is dropped. The tag carries it because it reads the statement off the derived
statement of Lemma 08QC, and flatness is what makes those derived tensor products agree with
the ordinary ones; the ordinary statement needs none of it. The dévissage uses only that the
zeroth face of the décalage is split in every degree, and a degreewise split short complex
stays short exact after tensoring, flat or not.

## References

* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject MonoidalCategory
open Opposite AlgebraicTopology StacksDraft.SimplicialTensor

open scoped Simplicial

universe v w

namespace Stacks.ChaoticSite

variable {B : Type w} [CommRing B] (N : SimplicialObject (ModuleCat.{max v w} B))

/-! ### The degreewise splitting of the décalage -/

/-- The zeroth degeneracy of `N`, read as a morphism into the décalage. -/
public def decSigmaZero (q : ℕ) : N _⦋q⦌ ⟶ (dec N) _⦋q⦌ := N.σ (0 : Fin (q + 1))

/-- The zeroth degeneracy splits the zeroth face of the décalage. -/
public lemma decSigmaZero_comp_decδ₀_app (q : ℕ) :
    decSigmaZero N q ≫ (decδ₀ N).app (op ⦋q⦌) = 𝟙 _ :=
  N.δ_comp_σ_self' (by simp)

/-- The complementary idempotent of the splitting of the zeroth face of the décalage: the
identity minus the zeroth degeneracy of the zeroth face. -/
public def decKerRetractAux (q : ℕ) : (dec N) _⦋q⦌ ⟶ (dec N) _⦋q⦌ :=
  𝟙 _ - (decδ₀ N).app (op ⦋q⦌) ≫ decSigmaZero N q

/-- The complementary idempotent `decKerRetractAux` lands in the kernel of the zeroth face of the
décalage. -/
public lemma decKerRetractAux_comp_decδ₀_app (q : ℕ) :
    decKerRetractAux N q ≫ (decδ₀ N).app (op ⦋q⦌) = 0 := by
  rw [decKerRetractAux, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    decSigmaZero_comp_decδ₀_app, Category.comp_id, sub_self]

/-- The degreewise retraction of the inclusion of the kernel of the zeroth face of the
décalage. -/
public def decKerRetract (q : ℕ) : (dec N) _⦋q⦌ ⟶ (simpKer (decδ₀ N)) _⦋q⦌ :=
  ModuleCat.ofHom (LinearMap.codRestrict _ (decKerRetractAux N q).hom (fun x => by
    refine LinearMap.mem_ker.mpr ?_
    have h := congrArg ModuleCat.Hom.hom (decKerRetractAux_comp_decδ₀_app N q)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x))

/-- The retraction `decKerRetract` followed by the kernel inclusion is the complementary idempotent
`decKerRetractAux`. -/
public lemma decKerRetract_comp_simpKerι_app (q : ℕ) :
    decKerRetract N q ≫ (simpKerι (decδ₀ N)).app (op ⦋q⦌) = decKerRetractAux N q := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

/-- The short complex of simplicial modules given by the zeroth face of the décalage and its
degreewise kernel. -/
public def decKerShortComplex : ShortComplex (SimplicialObject (ModuleCat.{max v w} B)) where
  X₁ := simpKer (decδ₀ N)
  X₂ := dec N
  X₃ := N
  f := simpKerι (decδ₀ N)
  g := decδ₀ N
  zero := simpKerι_comp (decδ₀ N)

/-- The retraction `decKerRetract` is a left inverse of the inclusion of the kernel of the zeroth
face of the décalage. -/
public lemma simpKerι_app_comp_decKerRetract (q : ℕ) :
    (simpKerι (decδ₀ N)).app (op ⦋q⦌) ≫ decKerRetract N q = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
  refine Subtype.ext ?_
  have hw : (((decδ₀ N).app (op ⦋q⦌)).hom) w.1 = 0 := w.2
  change (decKerRetractAux N q).hom w.1 = w.1
  rw [decKerRetractAux]
  simp only [ModuleCat.hom_sub, ModuleCat.hom_id, ModuleCat.hom_comp, LinearMap.sub_apply,
    LinearMap.id_coe, id_eq, LinearMap.coe_comp, Function.comp_apply, hw, map_zero, sub_zero]

/-- The degreewise splitting identity of `decKerShortComplex`: retraction then inclusion, plus the
zeroth face then the zeroth degeneracy, is the identity of the décalage. -/
public lemma decKerShortComplex_splitting_id (q : ℕ) :
    decKerRetract N q ≫ (simpKerι (decδ₀ N)).app (op ⦋q⦌) +
      (decδ₀ N).app (op ⦋q⦌) ≫ decSigmaZero N q = 𝟙 _ := by
  rw [decKerRetract_comp_simpKerι_app, decKerRetractAux, sub_add_cancel]

/-! ### The dévissage -/

variable (M : SimplicialObject (ModuleCat.{max v w} B))

/-- **Stacks Project, Tag 08QD.** The Alexander–Whitney map of two simplicial modules is a
quasi-isomorphism. This is the Eilenberg–Zilber theorem: the Moore complex
`s(M ⊗_B N)` of the degreewise tensor product is computed, through the canonical comparison,
by the total complex `s(M) ⊗_B s(N)` of the double complex of the two Moore complexes. -/
@[stacks 08QD "flat_eilenberg_zilber"]
public instance quasiIso_alexanderWhitney : QuasiIso (alexanderWhitney M N) := by
  have hepi : ∀ (n : ℕ) (N' : SimplicialObject (ModuleCat.{max v w} B)),
      Epi (HomologicalComplex.homologyMap (alexanderWhitney M N') n) := by
    intro n
    induction n with
    | zero =>
      intro N'
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
    | succ n ih =>
      intro N'
      exact epi_homologyMap_alexanderWhitney_of_splitting M (decKerShortComplex N')
        (decKerRetract N') (decSigmaZero N')
        (simpKerι_app_comp_decKerRetract N')
        (decSigmaZero_comp_decδ₀_app N') (decKerShortComplex_splitting_id N')
        (quasiIso_alexanderWhitney_dec M N') n (ih _)
  have hmono : ∀ (n : ℕ) (N' : SimplicialObject (ModuleCat.{max v w} B)),
      Mono (HomologicalComplex.homologyMap (alexanderWhitney M N') n) := by
    intro n
    induction n with
    | zero =>
      intro N'
      refine mono_homologyMap_alexanderWhitney_of_splitting M (decKerShortComplex N')
        (decKerRetract N') (decSigmaZero N')
        (simpKerι_app_comp_decKerRetract N')
        (decSigmaZero_comp_decδ₀_app N') (decKerShortComplex_splitting_id N')
        (quasiIso_alexanderWhitney_dec M N') 0 (hepi 0 _) (fun j hj => ?_)
      simp at hj
    | succ n ih =>
      intro N'
      refine mono_homologyMap_alexanderWhitney_of_splitting M (decKerShortComplex N')
        (decKerRetract N') (decSigmaZero N')
        (simpKerι_app_comp_decKerRetract N')
        (decSigmaZero_comp_decδ₀_app N') (decKerShortComplex_splitting_id N')
        (quasiIso_alexanderWhitney_dec M N') (n + 1) (hepi (n + 1) _) (fun j hj => ?_)
      obtain rfl : j = n := by simpa using hj
      exact ih _
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := hepi n N
  have := hmono n N
  exact isIso_of_mono_of_epi _

end Stacks.ChaoticSite

end
