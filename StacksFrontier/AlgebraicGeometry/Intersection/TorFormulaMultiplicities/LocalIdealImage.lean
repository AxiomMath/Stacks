module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# The local ideal of a subvariety contains the pullback of the ideal of its image

Let `f : X ⟶ S` be a morphism of schemes and let `c` be a point of `X` whose closure `f` carries
into the closure of the image of a point `ξ` of that closure. Then, in the local ring of `X` at
`ξ`,

`I_{f^{-1}(closure {f ξ})} ≤ I_{closure {c}}`

the left-hand side being the extension along the stalk map of the ideal of the reduced closure of
`f ξ`. Scheme-theoretically this is the containment `closure {c} ⊆ f^{-1}(closure {f ξ})`, and it
holds for the *reduced* closure of `c` precisely because the reduced induced structure carries
the largest ideal with its support.

This is the containment the multiplicity-one step of the proof of Stacks 0B0E consumes. There
`C` is the scheme-theoretic closure of `π^{-1}(π(Z))`, so `π` carries `C` into `π(Z)`, and the
containment of ideals which the local form of Stacks 0B1J needs is this one — it is what the
construction of `C` supplies, with no further argument.

## Main results

* `AlgebraicGeometry.TorFormula.map_stalkMap_localIdealAt_le`: the containment of local ideals
  from the set-theoretic containment of the images.

## Implementation notes

The proof factors `f` restricted to the reduced closure of `c` through the reduced closure of
`f ξ`: the former is reduced and its image lies in the latter, so
`AlgebraicGeometry.IsClosedImmersion.lift` produces the factorization from the containment of
ranges alone. The stalk of the ideal of a closed subscheme at a point is the kernel of the stalk
map of its inclusion (`AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι`), and a kernel
only grows under postcomposition; that is the whole of the argument, isolated as
`stalk_le_ker_stalkMap_of_factors`, whose morphism hypothesis is substituted away so that no
transport along the equality of points is needed.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

variable {X S : Scheme.{u}}

/-- A morphism factoring through the closed subscheme cut out by an ideal sheaf kills the stalk
of that ideal sheaf: the stalk is the kernel of the stalk map of the inclusion, and a kernel only
grows under postcomposition. -/
private theorem stalk_le_ker_stalkMap_of_factors {A : Scheme.{u}} (I : S.IdealSheafData)
    {g : A ⟶ S} (h : A ⟶ I.subscheme) (hfac : h ≫ I.subschemeι = g) (z : A) :
    IdealSheafData.stalk I (g.base z) ≤ RingHom.ker (g.stalkMap z).hom := by
  subst hfac
  intro a ha
  have hker : a ∈ RingHom.ker (I.subschemeι.stalkMap (h.base z)).hom := by
    rw [IdealSheafData.ker_stalkMap_subschemeι]
    exact ha
  have hzero : (I.subschemeι.stalkMap (h.base z)).hom a = 0 := RingHom.mem_ker.mp hker
  refine RingHom.mem_ker.mpr ?_
  have hc : ((h ≫ I.subschemeι).stalkMap z).hom a =
      (h.stalkMap z).hom ((I.subschemeι.stalkMap (h.base z)).hom a) :=
    congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.stalkMap_comp h I.subschemeι z)
  rw [hc, hzero, map_zero]

/-- **The local ideal of a subvariety contains the pullback of the ideal of its image.** Let
`f : X ⟶ S`, let `ξ` lie in the closure of `c` and suppose `f` carries the closure of `c` into
the closure of `f ξ`. Then, in the local ring of `X` at `ξ`, the extension along the stalk map of
the ideal of the reduced closure of `f ξ` is contained in the ideal of the reduced closure of
`c`.

This is the hypothesis the local form of Stacks 0B1J takes on the scheme-theoretic intersection,
in the form the construction of `C` in the proof of Stacks 0B0E supplies it: `C` is the closure
of `π^{-1}(π(Z))`, so `π` carries `C` into `π(Z)`, which is the closure of `π ξ` for `ξ` the
generic point of `Z`. -/
public theorem map_stalkMap_localIdealAt_le (f : X ⟶ S) {c ξ : X}
    (hξ : ξ ∈ closure ({c} : Set X))
    (himg : f.base '' closure ({c} : Set X) ⊆ closure ({f.base ξ} : Set S)) :
    Ideal.map (f.stalkMap ξ).hom (localIdealAt (f.base ξ) (f.base ξ)) ≤ localIdealAt c ξ := by
  let J := Stacks.Chow.integralComponentAt c
  let I := Stacks.Chow.integralComponentAt (f.base ξ)
  have hξJ : ξ ∈ J.support := mem_support_integralComponentAt hξ
  let z : J.subscheme := IdealSheafData.subschemePoint J ξ hξJ
  have hrangeJ : Set.range J.subschemeι.base = closure ({c} : Set X) :=
    (Scheme.IdealSheafData.range_subschemeι J).trans
      (Stacks.Chow.coe_support_integralComponentAt c)
  have hrange : Set.range (J.subschemeι ≫ f).base ⊆ closure ({f.base ξ} : Set S) := by
    rintro _ ⟨w, rfl⟩
    exact himg ⟨J.subschemeι.base w, by rw [← hrangeJ]; exact ⟨w, rfl⟩, rfl⟩
  have : IsIntegral J.subscheme := Stacks.Chow.isIntegral_integralComponentAt c
  have hker : I.subschemeι.ker ≤ (J.subschemeι ≫ f).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (J.subschemeι ≫ f),
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      ← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_closure,
      Stacks.Chow.coe_support_integralComponentAt (f.base ξ)]
    exact isClosed_closure.closure_subset_iff.mpr hrange
  have hle := stalk_le_ker_stalkMap_of_factors I
    (IsClosedImmersion.lift I.subschemeι (J.subschemeι ≫ f) hker)
    (IsClosedImmersion.lift_fac I.subschemeι (J.subschemeι ≫ f) hker) z
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  have ha' : a ∈ IdealSheafData.stalk I ((J.subschemeι ≫ f).base z) := ha
  have h0 : ((J.subschemeι ≫ f).stalkMap z).hom a = 0 := RingHom.mem_ker.mp (hle ha')
  rw [Scheme.Hom.stalkMap_comp] at h0
  simp only at h0
  have hmem : (f.stalkMap ξ).hom a ∈ RingHom.ker (J.subschemeι.stalkMap z).hom :=
    RingHom.mem_ker.mpr h0
  rwa [IdealSheafData.ker_stalkMap_subschemeι] at hmem

end AlgebraicGeometry.TorFormula

end
