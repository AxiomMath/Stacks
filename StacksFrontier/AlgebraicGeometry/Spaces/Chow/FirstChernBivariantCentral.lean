module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernBivariantClass

/-!
# The first Chern class is central in the Chow cohomology

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  **Stacks 0ERR**
asserts that the bivariant class `c₁(ℒ) ∈ A^1(X)` of Stacks 0ERM commutes with every
`c ∈ A^p(X)`:

  `c₁(ℒ) ∘ c = c ∘ c₁(ℒ)`  in  `A^{p+1}(X)`.

Both composites are classes for the identity of `X`; on a good test space `g : Y' ⟶ X` they cap
`α ∈ CH_k(Y')` as `c₁(ℒ) ∩ (c ∩ α)` and `c ∩ (c₁(ℒ) ∩ α)`
(`AlgebraicGeometry.Space.BivariantClassCanonical.compCap`), and a bivariant class is determined
by its cap operations, so the statement is the equality of these.

## Main results

* `AlgebraicGeometry.Space.firstChernBivariantClass_compCap_comm`: **Stacks 0ERR**.

## Implementation notes

The source proves the lemma on the line bundle `p : L → X`, through the injectivity of `p^*`
(Stacks 0ERH), Stacks 0EQR and Stacks 0ERE.  The proof here is shorter and uses only the axioms
of a bivariant class.  Axiom (3) of Stacks 0ERJ quantifies over every triple `(ℒ', s', D' → Y')`
as in Stacks 0ER1, including those with `s' = 0`.  For the zero section `D' = Y'`, every integral
closed subspace `W` lies in `D'`, and clause (1)(b) of Stacks 0ER1 makes the Gysin map the cap
product `c₁(ℒ') ∩ -`; the same holds for the pulled-back triple on `X'`.  So axiom (3) at
`(g^*ℒ, 0)` says that `c` commutes with `c₁(g^*ℒ) ∩ -`, which is
`AlgebraicGeometry.Space.BivariantClassCanonical.cap_canonicalFirstChernCapCanonicalChowMap`.
What is left is bookkeeping: the cap operation of Stacks 0ERM on a test space `Y'` is
`c₁ ∩ -` after the identification `Y' ≅ X ×_X Y'`, which `c` respects by axiom (1)
(`BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward_inv_pullbackSnd`),
and the two inverse images of `ℒ` to `X ×_X (X ×_X Y')` are isomorphic (Stacks 0EPT).

The composite `c ∘ d` of two bivariant classes for the identity is not constructed as a
bivariant class here; only its cap operations are, and the lemma compares them.

## References

* [Stacks Project, Tag 0ERR](https://stacks.math.columbia.edu/tag/0ERR)
* [Stacks Project, Tag 0ERM](https://stacks.math.columbia.edu/tag/0ERM)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **Stacks 0ERR.** In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible
`𝒪_X`-module.  Then `c₁(ℒ) ∈ A^1(X)` (Stacks 0ERM,
`AlgebraicGeometry.Space.firstChernBivariantClass`) commutes with every `c ∈ A^p(X)`: on every
good test space `g : Y' ⟶ X` the composites `c₁(ℒ) ∘ c` and `c ∘ c₁(ℒ)` have the same cap
operation, `c₁(ℒ) ∩ (c ∩ α) = c ∩ (c₁(ℒ) ∩ α)` for every `α ∈ CH_k(Y')`, the two degrees
`k - p - 1` and `k - 1 - p` being identified. -/
@[stacks 0ERR "c_1(L) ∈ A^1(X) commutes with every c ∈ A^p(X): the composites c_1(L) ∘ c and \
c ∘ c_1(L) have the same cap operation on every test space"]
theorem firstChernBivariantClass_compCap_comm {p : ℤ}
    (c : BivariantClassCanonical.{u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) p)
    {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    BivariantClassCanonical.compCap D (firstChernBivariantClass D sX hX L hL) c g hY' k x =
      chowGroupCanonicalDegreeCongr D _ _ (by omega)
        (BivariantClassCanonical.compCap D c (firstChernBivariantClass D sX hX L hL) g hY' k
          x) := by
  have hX' := isGood_pullback_fst D hX hX (𝟙 X) g hY'
  have hX'' := isGood_pullback_fst D hX hX (𝟙 X) (pullback.fst (𝟙 X) g) hX'
  -- the inverse images of `ℒ` to `X'' = X ×_X X'` along `X'' ⟶ X' ⟶ X` and `X'' ⟶ X` agree
  let q : (⟨pullback (𝟙 X) (pullback.fst (𝟙 X) g), hX''.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨pullback (𝟙 X) g, hX'.1⟩ :=
    ObjectProperty.homMk (pullback.snd (𝟙 X) (pullback.fst (𝟙 X) g))
  have hcompHom : q ≫ firstChernBivariantFst D sX hX g hX' =
      firstChernBivariantFst D sX hX (pullback.fst (𝟙 X) g) hX'' :=
    ObjectProperty.hom_ext _ (pullback.condition.symm.trans (Category.comp_id _))
  let e : (modulePullback D.site D.base D.base_mem q).obj
        ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L) ≅
      (modulePullback D.site D.base D.base_mem
        (firstChernBivariantFst D sX hX (pullback.fst (𝟙 X) g) hX'')).obj L :=
    (modulePullbackCompIso D.site D.base D.base_mem q
      (firstChernBivariantFst D sX hX g hX')).app L ≪≫ eqToIso (by rw [hcompHom])
  have hM := modulePullbackInvertible (firstChernBivariantFst D sX hX g hX') L hL
  have hM' := modulePullbackInvertible
    (firstChernBivariantFst D sX hX (pullback.fst (𝟙 X) g) hX'') L hL
  set z := chowGroupCanonicalProperPushforward.{u + 1} D (g ≫ sX) hY' (pullback.fst (𝟙 X) g ≫ sX)
    hX' (firstChernBivariantTestIso_hom_comp D sX g)
    (isProper_of_isIso D.site D.base D.base_mem (firstChernBivariantTestIso D g).hom) k x
  have hA := BivariantClassCanonical.cap_canonicalFirstChernCapCanonicalChowMap D c
    (pullback.fst (𝟙 X) g) hX' hX''
    ((modulePullback D.site D.base D.base_mem (firstChernBivariantFst D sX hX g hX')).obj L) hM
    (k - 1) (chowGroupCanonicalDegreeCongr D _ hX' (Int.sub_add_cancel k 1).symm z)
  have hT := BivariantClassCanonical.cap_chowGroupCanonicalDegreeCongr D c
    (pullback.fst (𝟙 X) g) hX' hX'' (Int.sub_add_cancel k 1).symm z
  have hB : c.cap (pullback.fst (𝟙 X) g) hX' hX'' k z =
      chowGroupCanonicalProperPushforward.{u + 1} D (pullback.fst (𝟙 X) g ≫ sX) hX'
        (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) g) ≫ sX) hX''
        (firstChernBivariantTestIso_hom_comp D sX (pullback.fst (𝟙 X) g))
        (isProper_of_isIso D.site D.base D.base_mem
          (firstChernBivariantTestIso D (pullback.fst (𝟙 X) g)).hom) (k - p)
        (c.cap g hY' hX' k x) :=
    BivariantClassCanonical.cap_chowGroupCanonicalProperPushforward_inv_pullbackSnd D c g hY' hX'
      hX'' k x
  have hI := canonicalFirstChernCapCanonicalChowMap_congr_iso D _ hX'' _ _
    (modulePullbackInvertible q _ hM) hM' e (k - 1 - p)
  rw [BivariantClassCanonical.compCap_apply, BivariantClassCanonical.compCap_apply]
  change firstChernBivariantCap D sX hX L hL (pullback.fst (𝟙 X) g) hX' hX'' (k - p)
      (c.cap g hY' hX' k x) =
    chowGroupCanonicalDegreeCongr D _ hX'' _
      (c.cap (pullback.fst (𝟙 X) g) hX' hX'' (k - 1)
        (firstChernBivariantCap D sX hX L hL g hY' hX' k x))
  rw [firstChernBivariantCap, firstChernBivariantCap, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, hA, hT, hB,
    chowGroupCanonicalDegreeCongr_trans]
  exact (chowGroupCanonicalDegreeCongr_canonicalFirstChernCapCanonicalChowMap D _ hX'' _
    hM' (by omega) _ _ _).symm.trans (congrArg _ (hI _).symm)

end AlgebraicGeometry.Space

end
