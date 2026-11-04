module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus

/-!
# The generic dimension formula for a dominant morphism of finite type

For a dominant morphism `g : W ⟶ V` of finite type to an integral locally Noetherian scheme,
with `W` locally Noetherian, there is a nonempty open subset of `W` on which

`dim_w(W) = dim_{g(w)}(V) + dim_w(W_{g(w)})`,

equivalently `dim_w(W_{g(w)}) = dim_w(W) - dim_{g(w)}(V)`. This is the scheme-level step of the
proof of Stacks 0DS4, where it is applied to a chart comparison and reduces the dimension of a
1-morphism of algebraic stacks relative to its scheme theoretic image to a statement about
schemes.

## Main results

* `AlgebraicGeometry.RelativeDimension.topologicalKrullDimAt_fiber_eq`: a morphism of relative
  dimension `d` has local fibre dimension `d` at every point of every fibre.
* `AlgebraicGeometry.exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber`: the generic
  dimension formula.

## Implementation notes

The three inputs are all available, and the proof is their composition.

* Generic flatness over a reduced base, Stacks 052B in the form
  `AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf`, gives a dense
  open `V₁ ⊆ V` over which `g` is flat and of finite presentation. An integral scheme is
  reduced. The restriction is taken in the form `W₁.ι ≫ g` for `W₁ = g ⁻¹ᵁ V₁` rather than as
  `Scheme.Hom.resLE`: the two differ by postcomposition with the open immersion `V₁.ι`, which is
  flat and of finite presentation, so the composite inherits both, and keeping the target equal
  to `V` avoids transporting local dimensions along `V₁.ι` afterwards.
* Stacks 054T, `AlgebraicGeometry.exists_open_relativeDimension_fiberwise_dense`, cuts a flat
  morphism locally of finite presentation into open pieces of pure relative dimension `d` whose
  union is dense in every fibre. This is the step that supplies *equidimensionality* of the
  fibres, which constancy of the fibre dimension alone (Stacks 05F7) does not give, and it is
  why no Cohen–Macaulay hypothesis is needed: the Cohen–Macaulay decomposition of Stacks 02NM
  would need one.
* Stacks 0AFE, `AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_relativeDimension`, is the
  formula itself on such a piece.

Dominance is used once, to see that `W₁` is nonempty: the image of `g` is dense, so it meets the
nonempty open `V₁`. The source says *scheme theoretically* dominant, which is stronger; all the
argument consumes is that the image meets a dense open, so the hypothesis here is the weaker
`AlgebraicGeometry.IsDominant` and the statement is correspondingly more general.
Irreducibility of `W` is *not* needed — only some nonempty open is asserted, and the piece of
pure relative dimension through any point of `W₁` is one. Quasi-compactness of `g` is what makes
it of finite type, as generic flatness requires; the source's proof arranges it by shrinking
instead of assuming it.

The conclusion is stated as an addition rather than a subtraction, as `WithBot ℕ∞` has no total
subtraction, and as a nonempty open *set* rather than a `Scheme.Opens`, because the open produced
is the range of a composite of two open immersions.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 054T](https://stacks.math.columbia.edu/tag/054T)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of relative dimension `d` has local fibre dimension `d` at every point of every
fibre: the fibre is equidimensional of dimension `d` and locally of finite type over the residue
field of its base point, so its local dimension is `d` everywhere. -/
theorem RelativeDimension.topologicalKrullDimAt_fiber_eq {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimension f d) (s : S)
    (x : f.fiber s) : topologicalKrullDimAt (f.fiber s) x = (d : WithBot ℕ∞) :=
  have _ := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
  topologicalKrullDimAt_eq_of_equidimensional (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) (hf s ⟨x⟩).1 (hf s ⟨x⟩).2 x

/-- **The generic dimension formula**, the scheme-level step of Stacks 0DS4. For a dominant
morphism `g : W ⟶ V` of finite type between locally Noetherian schemes with `V` integral, there
is a nonempty open subset of `W` on which `dim_w(W) = dim_{g(w)}(V) + dim_w(W_{g(w)})`. -/
@[sga "3 VIB 1.2" "special case"]
theorem exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber
    {W V : Scheme.{u}} (g : W ⟶ V) [IsIntegral V]
    [IsLocallyNoetherian W] [IsLocallyNoetherian V]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsDominant g] :
    ∃ O : Set W, IsOpen O ∧ O.Nonempty ∧
      ∀ w ∈ O, topologicalKrullDimAt W w =
        topologicalKrullDimAt V (g w) +
          topologicalKrullDimAt (g.fiber (g w)) (g.asFiber w) := by
  classical
  -- Generic flatness: `g` is flat and of finite presentation over a dense open `V₁ ⊆ V`.
  obtain ⟨V₁, hV₁dense, hflat, hfp⟩ := exists_dense_open_flat_finitePresentation_structureSheaf g
  have _ : LocallyOfFinitePresentation (g.resLE V₁ (g ⁻¹ᵁ V₁) le_rfl) :=
    hfp.locallyOfFinitePresentation
  set W₁ : W.Opens := g ⁻¹ᵁ V₁
  -- Keep the target equal to `V`: `W₁.ι ≫ g` is the flat restriction followed by `V₁.ι`.
  have hjfact : W₁.ι ≫ g = g.resLE V₁ W₁ le_rfl ≫ V₁.ι :=
    (Scheme.Hom.resLE_comp_ι g le_rfl).symm
  have _ : Flat (W₁.ι ≫ g) := by rw [hjfact]; infer_instance
  have _ : LocallyOfFinitePresentation (W₁.ι ≫ g) := by rw [hjfact]; infer_instance
  -- Stacks 054T: open pieces of pure relative dimension, fibrewise dense.
  obtain ⟨U, hUdense, hrel⟩ := exists_open_relativeDimension_fiberwise_dense (W₁.ι ≫ g)
  -- `W₁` is nonempty: the dense image of `g` meets the nonempty open `V₁`.
  obtain ⟨x₀⟩ : Nonempty W₁.toScheme := by
    obtain ⟨v, hvV₁, w, hw⟩ := (IsDominant.denseRange (f := g)).inter_open_nonempty
      (V₁ : Set V) V₁.2 hV₁dense.nonempty
    exact ⟨⟨w, show g w ∈ V₁ from hw ▸ hvV₁⟩⟩
  -- Some piece is nonempty, being dense in a nonempty fibre.
  have hfibne : Nonempty ((W₁.ι ≫ g).fiber ((W₁.ι ≫ g) x₀)) := ⟨(W₁.ι ≫ g).asFiber x₀⟩
  obtain ⟨y, hy⟩ := (hUdense ((W₁.ι ≫ g) x₀)).nonempty
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hy
  -- The piece of pure relative dimension `d`, as an open of `W`.
  set k : (U d).toScheme ⟶ W := (U d).ι ≫ W₁.ι with hkdef
  have hrd : RelativeDimension ((U d).ι ≫ W₁.ι ≫ g) d := hrel d
  refine ⟨Set.range k, k.isOpenEmbedding.isOpen_range, ⟨k ⟨_, hd⟩, _, rfl⟩, ?_⟩
  rintro w ⟨x, rfl⟩
  have hkx : k x = W₁.ι ((U d).ι x) := by simp [hkdef]
  -- Stacks 0AFE on the piece, which has relative dimension `d` over `V`.
  have h0AFE := topologicalKrullDimAt_eq_add_of_relativeDimension ((U d).ι ≫ W₁.ι ≫ g) hrd x
  have hpt : ((U d).ι ≫ W₁.ι ≫ g) x = g (W₁.ι ((U d).ι x)) := by simp
  rw [hpt] at h0AFE
  -- `d` is the local fibre dimension of the piece, carried down the two open immersions.
  have hval : topologicalKrullDimAt (((U d).ι ≫ W₁.ι ≫ g).fiber (((U d).ι ≫ W₁.ι ≫ g) x))
      (((U d).ι ≫ W₁.ι ≫ g).asFiber x) = (d : WithBot ℕ∞) :=
    RelativeDimension.topologicalKrullDimAt_fiber_eq _ hrd _ _
  -- The absolute local dimension is unchanged along each of them as well.
  rwa [hkx, W₁.ι.isOpenEmbedding.topologicalKrullDimAt_eq ((U d).ι x),
    (U d).ι.isOpenEmbedding.topologicalKrullDimAt_eq x,
    ← fiberDimensionAt_comp_openImmersion W₁.ι g ((U d).ι x),
    ← fiberDimensionAt_comp_openImmersion (U d).ι (W₁.ι ≫ g) x, hval]

/-- Quasi-compactness passes to the induced morphism of reductions, as local finite type does in
`AlgebraicGeometry.Scheme.locallyOfFiniteType_reductionMap`. -/
@[ega "I 6.3.4" "clause (vi)"]
instance quasiCompact_reductionMap {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] :
    QuasiCompact (Scheme.reductionMap f) :=
  have : QuasiCompact (Scheme.reductionMap f ≫ S.reductionι) := by
    rw [Scheme.reductionMap_comp_reductionι]; infer_instance
  QuasiCompact.of_comp (Scheme.reductionMap f) S.reductionι

/-- **The generic dimension formula without a reducedness hypothesis**, the scheme-level step of
Stacks 0DS4 in the form its proof uses it: for a dominant morphism `g : W ⟶ V` of finite type
between locally Noetherian schemes with `V` merely irreducible, there is a nonempty open subset
of `W` on which `dim_w(W) = dim_{g(w)}(V) + dim_w(W_{g(w)})`.

This is the source's "pass to the reductions" step. The reduction `V_red` of an irreducible
scheme is integral, the induced `W_red ⟶ V_red` is again dominant of finite type, and all three
quantities are unchanged: `X_red ⟶ X` is a homeomorphism on points, so the two absolute local
dimensions transport, and the fibres of `g` and of `W_red ⟶ V_red` are homeomorphic by
`Stacks.Divisors.fiberReductionHomeo`, so the local fibre dimension transports too. -/
@[sga "3 VIB 1.2" "more general"]
theorem exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace
    {W V : Scheme.{u}} (g : W ⟶ V) [IrreducibleSpace V]
    [IsLocallyNoetherian W] [IsLocallyNoetherian V]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsDominant g] :
    ∃ O : Set W, IsOpen O ∧ O.Nonempty ∧
      ∀ w ∈ O, topologicalKrullDimAt W w =
        topologicalKrullDimAt V (g w) +
          topologicalKrullDimAt (g.fiber (g w)) (g.asFiber w) := by
  -- The reduction of a locally Noetherian scheme is locally Noetherian, `X_red ⟶ X` being a
  -- closed immersion and so locally of finite type.
  have _ : IsLocallyNoetherian W.reduction := LocallyOfFiniteType.isLocallyNoetherian W.reductionι
  have _ : IsLocallyNoetherian V.reduction := LocallyOfFiniteType.isLocallyNoetherian V.reductionι
  obtain ⟨O', hO'open, hO'ne, hO'⟩ :=
    exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber (Scheme.reductionMap g)
  refine ⟨Scheme.reductionHomeo W '' O', (Scheme.reductionHomeo W).isOpenMap _ hO'open,
    hO'ne.image _, ?_⟩
  rintro w ⟨w', hw', rfl⟩
  set s' := Scheme.reductionMap g w'
  set y' := (Scheme.reductionMap g).asFiber w'
  have hbase : g (Scheme.reductionHomeo W w') = V.reductionι s' :=
    Stacks.Divisors.apply_reductionHomeo g w'
  -- The fibre comparison carries the chosen point of the fibre of `W_red ⟶ V_red` to the
  -- chosen point of the fibre of `g`.
  have hz : g.fiberι (V.reductionι s') (Stacks.Divisors.fiberReductionHomeo g s' y') =
      Scheme.reductionHomeo W w' := by
    rw [Stacks.Divisors.fiberReductionHomeo,
      fiberι_fiberHomeoOfSquare g (Scheme.reductionMap g) (Scheme.reductionHomeo W) V.reductionι
        V.injective_reductionι (Stacks.Divisors.apply_reductionHomeo g) s' y']
    exact congrArg (Scheme.reductionHomeo W)
      (Scheme.Hom.fiberι_asFiber (Scheme.reductionMap g) w')
  have hfib : topologicalKrullDimAt (g.fiber (g (Scheme.reductionHomeo W w')))
        (g.asFiber (Scheme.reductionHomeo W w')) =
      topologicalKrullDimAt ((Scheme.reductionMap g).fiber s') y' := by
    rw [← hz, Scheme.Hom.topologicalKrullDimAt_fiber_fiberι]
    exact (topologicalKrullDimAt_eq_of_homeomorph
      (Stacks.Divisors.fiberReductionHomeo g s') y').symm
  rw [hfib, hbase, ← topologicalKrullDimAt_eq_of_homeomorph (Scheme.reductionHomeo W) w',
    show V.reductionι s' = Scheme.reductionHomeo V s' from rfl,
    ← topologicalKrullDimAt_eq_of_homeomorph (Scheme.reductionHomeo V) s']
  exact hO' w' hw'

end AlgebraicGeometry

end
