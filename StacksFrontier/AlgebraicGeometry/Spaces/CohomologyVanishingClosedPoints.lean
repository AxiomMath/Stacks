module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective

/-!
# The closed points of a space with vanishing first cohomology are separated by its spectrum

Let `X` be a quasi-compact, quasi-separated algebraic space all of whose quasi-coherent modules
have vanishing first cohomology — the data of Stacks 07UY — and write `A = Γ(X, 𝒪_X)`.  The
canonical morphism `p : X ⟶ Spec A` of Stacks 05Z1 then takes distinct closed points of `|X|`
to distinct points of `Spec A`.

The reason is the separating function of Stacks 07V1: two distinct closed points are disjoint
closed subsets of `|X|`, so some `a ∈ A` vanishes at the first and takes the value `1` at the
second, and no point of `Spec A` lies outside both the nonvanishing locus of `a` and that of
`a - 1`, the local ring of a scheme at a point being a local ring.

## Main results

* `AlgebraicGeometry.Space.mem_sectionSupport_pullbackToGlobalFunctions_iff`: a point of an
  algebraic space lies in the nonvanishing locus of the pullback of a regular function along a
  morphism to an object of the site exactly when its image lies in the nonvanishing locus of
  that function.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation`'s
  `pointsToScheme_pointsMap_toSpecGlobalFunctions_ne_of_isClosed_of_ne`: in the situation of
  Stacks 07UY the canonical morphism `p : X ⟶ Spec A` separates the closed points of `|X|`.

## Implementation notes

The nonvanishing locus of a global regular function on an algebraic space is
`AlgebraicGeometry.Space.sectionSupport`, read on the étale charts through
`AlgebraicGeometry.Space.mem_sectionSupport_iff`; so the dictionary between it and the
scheme-theoretic basic open `AlgebraicGeometry.Scheme.basicOpen` on the target is assembled
chartwise, from the chart formula
`AlgebraicGeometry.Space.pullbackToGlobalFunctions_apply_chart` for the pullback of a regular
function and `AlgebraicGeometry.Scheme.preimage_basicOpen_top`.  Every point of the space lies
under a point of a surjective étale chart, which is where the algebraicity of the source enters.

The morphism `p` is `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctions`
in the form used by the neighbouring tag Stacks 07V5: `Spec A` is presented by an affine object
`V` of the site together with a ring isomorphism `Γ(V, 𝒪_V) ≅ A`, and the base of the situation
is terminal, as the universal property of Stacks 05Z1 requires.  That isomorphism is what turns
the function produced by Stacks 07V1 into a regular function on `V`.

Stacks 07V1 is available at the module universe of the structure sheaf, so the situation here is
one of type `CohomologyVanishingSituation.{u, u}`.

*Stacks 07V4 itself.*  The separation of closed points proved here is the final step of the
source proof of Stacks 07V4.  The tag itself, universal injectivity of `p`, is
`Space.CohomologyVanishingSituation.universallyInjective_toSpecGlobalFunctionsOverIntegers`
in `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingUniversallyInjective.lean`.

## References

* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
* [Stacks Project, Tag 07U5](https://stacks.math.columbia.edu/tag/07U5)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- At every point of a scheme one of a global regular function `a` and of `a - 1` is
invertible: the local ring there is a local ring, and the two differ by `1`. -/
private theorem Scheme.mem_basicOpen_or_mem_basicOpen_sub_one (Y : Scheme.{u}) (a : Γ(Y, ⊤))
    (z : Y) : z ∈ Y.basicOpen a ∨ z ∈ Y.basicOpen (a - 1) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      ((Y.presheaf.germ ⊤ z trivial).hom a) with h | h
  · exact Or.inl ((Y.mem_basicOpen_top a z).mpr h)
  · refine Or.inr ((Y.mem_basicOpen_top (a - 1) z).mpr ?_)
    have hg : (Y.presheaf.germ ⊤ z trivial).hom (a - 1) =
        -(1 - (Y.presheaf.germ ⊤ z trivial).hom a) := by
      rw [neg_sub, map_sub, map_one]
    rw [hg]
    exact h.neg

/-- A point of the source of a morphism of schemes lies in the nonvanishing locus of the
pullback of a global regular function exactly when its image lies in the nonvanishing locus of
that function. -/
private theorem Scheme.mem_basicOpen_appTop_iff {A Y : Scheme.{u}} (g : A ⟶ Y) (r : Γ(Y, ⊤))
    (z : A) : z ∈ A.basicOpen (g.appTop r) ↔ g z ∈ Y.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top]
  exact Iff.rfl

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (f : X ⟶ _root_.AlgebraicGeometry.schemeSpace T)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))

/-- **The nonvanishing locus of a pulled-back regular function, read on an étale chart.** A
point of an étale chart of `X` lies over a point of the nonvanishing locus of the pullback of
`s` along `f` exactly when its image in `T` lies in the nonvanishing locus of `s`. -/
theorem mem_sectionSupport_pullbackToGlobalFunctions_chart_iff (W : SmallEtale B S hS X.obj)
    (r : points B S hS (yoneda.obj W.obj.left)) :
    pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom r ∈
        sectionSupport B S hS X.obj (pullbackToGlobalFunctions B S hS X T f s) ↔
      pointsToScheme B S hS T
          (pointsMap B S hS X.obj f.hom
            (pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom r)) ∈
        ((BigFppfOver.toScheme B S hS).obj T).basicOpen s := by
  have hstep : pointsMap B S hS X.obj f.hom
        (pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom r) =
      pointsMap B S hS (yoneda.obj W.obj.left)
        (yoneda.map (yoneda.preimage (W.obj.hom ≫ f.hom))) r :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj W.obj.left) W.obj.hom f.hom) r).symm.trans
      (congrArg (fun m : yoneda.obj W.obj.left ⟶ yoneda.obj T =>
          pointsMap B S hS (yoneda.obj W.obj.left) m r)
        (yoneda.map_preimage (W.obj.hom ≫ f.hom)).symm)
  have himage : pointsToScheme B S hS T
        (pointsMap B S hS X.obj f.hom
          (pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom r)) =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (W.obj.hom ≫ f.hom))
        (pointsToScheme B S hS W.obj.left r) :=
    (congrArg (pointsToScheme B S hS T) hstep).trans
      (pointsToScheme_pointsMap_yoneda B S hS (yoneda.preimage (W.obj.hom ≫ f.hom)) r)
  exact ((mem_sectionSupport_iff B S hS X.obj _ W r).trans
      (Scheme.mem_basicOpen_appTop_iff
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (W.obj.hom ≫ f.hom))) s
        (pointsToScheme B S hS W.obj.left r))).trans
    (Iff.of_eq (congrArg
      (fun z => z ∈ ((BigFppfOver.toScheme B S hS).obj T).basicOpen s) himage)).symm

/-- **The nonvanishing locus of a pulled-back regular function.** A point of `X` lies in the
nonvanishing locus of the pullback of `s` along `f` exactly when its image in `T` lies in the
nonvanishing locus of `s`. -/
theorem mem_sectionSupport_pullbackToGlobalFunctions_iff (z : points B S hS X.obj) :
    z ∈ sectionSupport B S hS X.obj (pullbackToGlobalFunctions B S hS X T f s) ↔
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom z) ∈
        ((BigFppfOver.toScheme B S hS).obj T).basicOpen s := by
  obtain ⟨U, φ, hsurj, hetale⟩ := X.property.exists_atlas
  obtain ⟨q, hq⟩ :=
    (surjective_iff_surjective_pointsMap B S hS X.obj X.property U φ).1 hsurj z
  rw [← hq]
  exact mem_sectionSupport_pullbackToGlobalFunctions_chart_iff B S hS X T f s
    ⟨CostructuredArrow.mk φ, hetale⟩ q

namespace CohomologyVanishingSituation

attribute [local instance] pointTopology

variable (T' : CohomologyVanishingSituation.{u, u}) (hterminal : IsTerminal T'.base)
    (V : BigFppfOver T'.site T'.base T'.containsBase)
    [IsAffine ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V)]
    (e : Γ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V, ⊤) ≃+*
      _root_.AlgebraicGeometry.Space.globalFunctions T'.site T'.base T'.containsBase
        T'.space.1)

/-- **The canonical morphism to `Spec A` separates the closed points of `|X|`.** In the
situation of Stacks 07UY, two distinct closed points of `|X|` have distinct images in `Spec A`
under `p : X ⟶ Spec A`, where `Spec A` is presented by an affine object `V` of the site through
a ring isomorphism `Γ(V, 𝒪_V) ≅ A = Γ(X, 𝒪_X)`.

Stacks 07V1 supplies `a ∈ A` vanishing at the first point and taking the value `1` at the
second; if the two images agreed, that point of `Spec A` would lie in neither the nonvanishing
locus of `a` nor that of `a - 1`, which no point of a scheme does. -/
@[stacks 07V4 "the final step of the source proof only: in Situation 07UY the morphism \
p : X -> Spec A separates the closed points of |X|, two distinct closed points of |X| having \
distinct images. Universal injectivity of p, which is the assertion of the tag, is NOT proved \
by this declaration, and neither is injectivity of p on all of |X|; see \
universallyInjective_toSpecGlobalFunctions in this same file, which does state universal \
injectivity and carries the two steps that are missing. The source reaches universal \
injectivity from this step by three reductions, none of them available in this development. \
Clause (2) of Stacks 07V0 reduces to the case of a field A, but its library form -- \
isAffineHom_of_isPullback_toSpecGlobalFunctions -- carries the affineness assertion only and \
not the computation Gamma(X', O_X') = A' that the reduction needs. Stacks 0488 then replaces \
the field by a large algebraically closed extension and Stacks 07U5 makes the resulting \
field-valued points closed points of |X|, but the library's 07U5 -- \
isClosed_singleton_class_of_isAlgebraic_residueField -- requires the field of the point to be \
algebraic over the residue field at a closed point of the base, which is exactly what the first \
reduction would have arranged. And the source's passage from one point of |X| to one \
field-valued point of X is left implicit there. IsTerminal T'.base, the affine object V and \
the isomorphism e are inherited from the signature of toSpecGlobalFunctions, as for \
the neighbouring Stacks 07V5"]
theorem pointsToScheme_pointsMap_toSpecGlobalFunctions_ne_of_isClosed_of_ne
    {x y : points T'.site T'.base T'.containsBase T'.space.1}
    (hx : IsClosed ({x} : Set (points T'.site T'.base T'.containsBase T'.space.1)))
    (hy : IsClosed ({y} : Set (points T'.site T'.base T'.containsBase T'.space.1)))
    (hxy : x ≠ y) :
    pointsToScheme T'.site T'.base T'.containsBase V
        (pointsMap T'.site T'.base T'.containsBase T'.space.1
          (toSpecGlobalFunctions T' hterminal V e).hom x) ≠
      pointsToScheme T'.site T'.base T'.containsBase V
        (pointsMap T'.site T'.base T'.containsBase T'.space.1
          (toSpecGlobalFunctions T' hterminal V e).hom y) := by
  intro heq
  obtain ⟨a, ha₀, ha₁⟩ :=
    exists_subset_compl_sectionSupport_of_disjoint T' hx hy (Set.disjoint_singleton.2 hxy)
  have hdict : ∀ (z : points T'.site T'.base T'.containsBase T'.space.1)
      (σ : Γ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V, ⊤)),
      (z ∈ _root_.AlgebraicGeometry.Space.sectionSupport T'.site T'.base T'.containsBase
          T'.space.1 (e σ) ↔
        pointsToScheme T'.site T'.base T'.containsBase V
            (pointsMap T'.site T'.base T'.containsBase T'.space.1
              (toSpecGlobalFunctions T' hterminal V e).hom z) ∈
          ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V).basicOpen σ) := by
    intro z σ
    have hfun : pullbackToGlobalFunctions T'.site T'.base T'.containsBase T'.space V
          (toSpecGlobalFunctions T' hterminal V e) σ = e σ :=
      congrArg
        (fun φ : Γ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V, ⊤) →+*
            _root_.AlgebraicGeometry.Space.globalFunctions T'.site T'.base T'.containsBase
              T'.space.1 => φ σ)
        (pullbackToGlobalFunctions_toSpecGlobalFunctions T' hterminal V e)
    exact (Iff.of_eq (congrArg (fun c => z ∈ _root_.AlgebraicGeometry.Space.sectionSupport
          T'.site T'.base T'.containsBase T'.space.1 c) hfun)).symm.trans
      (mem_sectionSupport_pullbackToGlobalFunctions_iff T'.site T'.base T'.containsBase
        T'.space V (toSpecGlobalFunctions T' hterminal V e) σ z)
  have hnot : ∀ (z : points T'.site T'.base T'.containsBase T'.space.1)
      (σ : Γ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V, ⊤)) (b),
      e σ = b → z ∉ _root_.AlgebraicGeometry.Space.sectionSupport T'.site T'.base
          T'.containsBase T'.space.1 b →
        pointsToScheme T'.site T'.base T'.containsBase V
            (pointsMap T'.site T'.base T'.containsBase T'.space.1
              (toSpecGlobalFunctions T' hterminal V e).hom z) ∉
          ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V).basicOpen σ :=
    fun z σ b hb hz hmem => hz (hb ▸ (hdict z σ).2 hmem)
  rcases Scheme.mem_basicOpen_or_mem_basicOpen_sub_one
      ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj V) (e.symm a)
      (pointsToScheme T'.site T'.base T'.containsBase V
        (pointsMap T'.site T'.base T'.containsBase T'.space.1
          (toSpecGlobalFunctions T' hterminal V e).hom x)) with h | h
  · exact hnot x _ _ (e.apply_symm_apply a) (ha₀ rfl) h
  · exact hnot y _ _ (by rw [map_sub, map_one, e.apply_symm_apply]) (ha₁ rfl) (heq ▸ h)

end CohomologyVanishingSituation

end Space

end AlgebraicGeometry

end
