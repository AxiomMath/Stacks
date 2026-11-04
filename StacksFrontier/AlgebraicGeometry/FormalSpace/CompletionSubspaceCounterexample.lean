module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveOfSheafifyIso
public import StacksFrontier.RingTheory.MvPolynomial.NoUniformNilpotenceExponent

/-!
# The comparison of the two completions is not an isomorphism in general

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `Z ⊆ X` be a closed subspace with point set `T = |Z|`. The canonical morphism
`c : X^∧_Z ⟶ X_{/T}` of `AlgebraicGeometry.Space.completionSubspaceComparison` is an isomorphism
when `Z ⟶ X` is of finite presentation
(`AlgebraicGeometry.Space.isIso_completionSubspaceComparison`). This file supplies the other half
of [Stacks, Tag 0H8N]: without that hypothesis `c` need not be an isomorphism.

The counterexample is the source's. Take `A = ℤ[x₀, x₁, x₂, …]`, let `S = X = Spec A` and let
`Z = Spec (A ⧸ I)` be the closed subscheme cut out by `I = (x₀, x₁, x₂, …)`, which is not of
finite presentation. The test object is `Spec R` for `R = A ⧸ (xₙ ^ (n + 1) : n ∈ ℕ)`, in which
every variable is nilpotent but no single exponent kills them all
(`StacksFrontier/RingTheory/MvPolynomial/NoUniformNilpotenceExponent.lean`). The resulting section
`Spec R ⟶ Spec A` is supported on `T`, so it is a section of `X_{/T}`; but it is not locally a
section of `X^∧_Z`, so `c` is not an isomorphism.

## Main results

* `AlgebraicGeometry.Space.not_isIso_completionSubspaceComparison`: **Stacks 0H8N**, the negative
  half — a big fppf site, a base scheme, an algebraic space and a closed subspace for which the
  comparison morphism is not an isomorphism.
* `AlgebraicGeometry.Space.Counterexample0H8N.hasImageIn_testHom`: the test section is supported
  on `|Z|`.
* `AlgebraicGeometry.Space.Counterexample0H8N.not_isLocallySurjective_inclHom`: the test section
  does not lie locally in the union of the infinitesimal neighbourhoods of `Z`.

## Implementation notes

The big fppf site is not chosen until the final statement, so every intermediate result takes a
site `B` containing `Spec A` as a hypothesis; `Spec (A ⧸ I)` and `Spec R` then lie in `B` too,
being closed subschemes of `Spec A` and so no larger
(`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`). The closed subspace `Z` is the range
of the representable morphism attached to the closed immersion, which is a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`.

That the section is supported on `T` is a field-valued point argument: a field-valued point of
`Spec R` sends each variable to a nilpotent element of a field, hence to `0`, so the composite
`A → R → k` kills `I` and the point factors through `Spec (A ⧸ I)`; the factorization is lifted
back into the site with `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`.

That the section is not locally a section of `X^∧_Z` is where the three finiteness mismatches
meet. If it were, the witnessing covering sieve of the affine object `Spec R` would be refined by
a *standard* fppf covering `{Vᵢ ⟶ Spec R}` (Stacks 02W3,
`AlgebraicGeometry.exists_standardFppf_refinement`): finite, by flat morphisms of finite
presentation of affine schemes, jointly surjective. On each `Vᵢ` the restricted section has
inverse image of `Z` a universal `nᵢ`th-order thickening, and reading the defining ideal on the
identity étale chart of `Vᵢ` (`AlgebraicGeometry.Space.definingIdealAt_eq_ker`) shows that each
variable pulls back to an element of `Γ(Vᵢ, ⊤)` killed by the exponent `nᵢ + 1`. The membership
of a variable in that ideal is a diagram chase, not an ideal computation: the cartesian square
presenting the inverse image exhibits its projection as a section of the inverse image, which
after composing with the section is a section of `Z`, and every variable dies on `Z`. Finally the
index set is finite, so one exponent `N + 1` works for all `Vᵢ` at once; and the product of the
`Γ(Vᵢ, ⊤)` is faithfully flat over `Γ(Spec R, ⊤) = R`
(`AlgebraicGeometry.faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ`), so `R → ∏ᵢ Γ(Vᵢ, ⊤)` is
injective and `N + 1` would kill every variable of `R` — which it does not.

Everything is stated in the universe `0`, which is where `ℤ[x₀, x₁, …]` lives.

## References

* [Stacks Project, Tag 0H8N](https://stacks.math.columbia.edu/tag/0H8N)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial Opposite

namespace AlgebraicGeometry.Space.Counterexample0H8N

/-! ### The rings -/

/-- The polynomial ring `A = ℤ[x₀, x₁, x₂, …]`. -/
abbrev polyRing : CommRingCat.{0} := CommRingCat.of (MvPolynomial ℕ ℤ)

/-- The ideal `I = (x₀, x₁, x₂, …)` of `A`. -/
def varIdeal : Ideal (MvPolynomial ℕ ℤ) :=
  Ideal.span (Set.range fun n : ℕ => (X n : MvPolynomial ℕ ℤ))

/-- Each variable lies in `I`. -/
theorem X_mem_varIdeal (n : ℕ) : (X n : MvPolynomial ℕ ℤ) ∈ varIdeal :=
  Ideal.subset_span ⟨n, rfl⟩

/-- The quotient `A ⧸ I`. -/
abbrev quotVar : CommRingCat.{0} := CommRingCat.of (MvPolynomial ℕ ℤ ⧸ varIdeal)

/-- The quotient `R = A ⧸ (xₙ ^ (n + 1) : n)`. -/
abbrev quotPow : CommRingCat.{0} := CommRingCat.of (MvPolynomial ℕ ℤ ⧸ powerIdeal)

/-- The quotient map `A ⟶ A ⧸ I`. -/
abbrev mkVar : polyRing ⟶ quotVar :=
  CommRingCat.ofHom (Ideal.Quotient.mk varIdeal)

/-- The quotient map `A ⟶ R`. -/
abbrev mkPow : polyRing ⟶ quotPow :=
  CommRingCat.ofHom (Ideal.Quotient.mk powerIdeal)

/-- `Spec (A ⧸ I) ⟶ Spec A` is a closed immersion. -/
instance isClosedImmersion_specMap_mkVar :
    _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map mkVar) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective mkVar
    Ideal.Quotient.mk_surjective

/-- `Spec R ⟶ Spec A` is a closed immersion. -/
instance isClosedImmersion_specMap_mkPow :
    _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map mkPow) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective mkPow
    Ideal.Quotient.mk_surjective

/-! ### The site -/

variable (B : BigFppfSite.{0}) (hA : B.Contains (Spec polyRing))

include hA in
/-- `Spec (A ⧸ I)` is no larger than `Spec A`, so it lies in any big fppf site containing the
latter. -/
theorem contains_quotVar : B.Contains (Spec quotVar) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (Spec.map mkVar)) hA

include hA in
/-- `Spec R` is no larger than `Spec A`, so it lies in any big fppf site containing the
latter. -/
theorem contains_quotPow : B.Contains (Spec quotPow) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (Spec.map mkPow)) hA

/-- The underlying scheme of an object of the big fppf site over `Spec A`. -/
abbrev toSch : BigFppfOver B (Spec polyRing) hA ⥤ Scheme.{0} :=
  BigFppfOver.toScheme B (Spec polyRing) hA

/-- `Spec A` as the base object of the big fppf site over `Spec A`. -/
abbrev baseObj : BigFppfOver B (Spec polyRing) hA := Over.mk (𝟙 (B.obj hA))

/-- The closed subscheme `Spec (A ⧸ I)`, as an object of the site over `Spec A`. -/
abbrev subObj : BigFppfOver B (Spec polyRing) hA :=
  Over.mk (ObjectProperty.homMk (Spec.map mkVar) :
    B.obj (contains_quotVar B hA) ⟶ B.obj hA)

/-- The test object `Spec R`, as an object of the site over `Spec A`. -/
abbrev testObj : BigFppfOver B (Spec polyRing) hA :=
  Over.mk (ObjectProperty.homMk (Spec.map mkPow) :
    B.obj (contains_quotPow B hA) ⟶ B.obj hA)

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A`, as a morphism of the site. -/
abbrev subIncl : subObj B hA ⟶ baseObj B hA :=
  Over.homMk (ObjectProperty.homMk (Spec.map mkVar) :
    B.obj (contains_quotVar B hA) ⟶ B.obj hA) (by simp)

/-- The section `Spec R ⟶ Spec A`, as a morphism of the site. -/
abbrev testHom : testObj B hA ⟶ baseObj B hA :=
  Over.homMk (ObjectProperty.homMk (Spec.map mkPow) :
    B.obj (contains_quotPow B hA) ⟶ B.obj hA) (by simp)

/-- A morphism of the site into the base object is, on underlying schemes, the structure
morphism of its source. -/
theorem toSch_map_to_baseObj {W : BigFppfOver B (Spec polyRing) hA} (f : W ⟶ baseObj B hA) :
    (toSch B hA).map f = B.inclusion.map W.hom := by
  have hw : f.left = W.hom := by simpa using Over.w f
  exact congrArg B.inclusion.map hw

/-- `Spec A`, as an algebraic space over itself. -/
abbrev ambSpace : AlgebraicSpaces B (Spec polyRing) hA :=
  ⟨yoneda.obj (baseObj B hA),
    _root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec polyRing) hA (baseObj B hA)⟩

/-- The closed subspace `Z = Spec (A ⧸ I) ⊆ Spec A`. -/
abbrev subSpace : Subfunctor (ambSpace B hA).1 :=
  Subfunctor.range (yoneda.map (subIncl B hA))

/-- `Z` is a closed subspace of `Spec A`. -/
theorem isClosedSubspace_subSpace :
    IsClosedSubspace B (Spec polyRing) hA (subSpace B hA) :=
  isClosedSubspace_range_yoneda_map B (Spec polyRing) hA (subIncl B hA)
    (by exact inferInstanceAs
      (_root_.AlgebraicGeometry.IsClosedImmersion (Spec.map mkVar)))

/-! ### The test section is supported on the point set of `Z` -/

/-- **Every field-valued point of `Spec R` factors through `Spec (A ⧸ I)` over `Spec A`.** The
composite ring map `A → R → k` sends each variable to a nilpotent element of the field `k`,
hence to `0`, so it kills `I`. -/
theorem exists_factor_subIncl
    (p : FieldValuedPoint B (Spec polyRing) hA (yoneda.obj (testObj B hA))) :
    ∃ l : p.siteObject ⟶ subObj B hA,
      l ≫ subIncl B hA = p.value ≫ testHom B hA := by
  -- the morphism of schemes underlying `p.value`, with its source spelled as a spectrum
  obtain ⟨γ, hγ⟩ : ∃ γ : Spec (CommRingCat.of p.carrier) ⟶ Spec quotPow,
      (toSch B hA).map p.value = γ := ⟨_, rfl⟩
  have hψmap : Spec.map (mkPow ≫ Spec.preimage γ) =
      (toSch B hA).map (p.value ≫ testHom B hA) := by
    rw [Spec.map_comp, Spec.map_preimage, ← hγ, Functor.map_comp]
    rfl
  -- the composite ring map kills `I`, because each variable goes to a nilpotent of a field
  have hker : varIdeal ≤ RingHom.ker (mkPow ≫ Spec.preimage γ).hom := by
    rw [varIdeal, Ideal.span_le]
    rintro _ ⟨n, rfl⟩
    refine RingHom.mem_ker.2 ?_
    have hnil : IsNilpotent ((Spec.preimage γ).hom
        (Ideal.Quotient.mk powerIdeal (X n : MvPolynomial ℕ ℤ))) :=
      (isNilpotent_powerIdealMk_X n).map (Spec.preimage γ).hom
    exact hnil.eq_zero
  -- hence factors through `A ⧸ I`
  have hcomp : mkVar ≫ CommRingCat.ofHom
      (Ideal.Quotient.lift varIdeal (mkPow ≫ Spec.preimage γ).hom hker) =
      mkPow ≫ Spec.preimage γ :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  have hδ : Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.lift varIdeal (mkPow ≫ Spec.preimage γ).hom hker)) ≫
      Spec.map mkVar = (toSch B hA).map (p.value ≫ testHom B hA) := by
    rw [← Spec.map_comp, hcomp, hψmap]
  have hbase : (toSch B hA).map (p.value ≫ testHom B hA) = p.toBase :=
    toSch_map_to_baseObj B hA (p.value ≫ testHom B hA)
  obtain ⟨l, hl⟩ := BigFppfOver.exists_hom_of_comp_eq B (Spec polyRing) hA
    (X := p.siteObject) (Y := subObj B hA)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.lift varIdeal (mkPow ≫ Spec.preimage γ).hom hker)))
    (by rw [show B.inclusion.map (subObj B hA).hom = Spec.map mkVar from rfl, hδ, hbase]; rfl)
  refine ⟨l, (toSch B hA).map_injective ?_⟩
  rw [Functor.map_comp, hl]
  exact hδ

/-- **The test section is supported on `|Z|`.** Its point-set image lies in the point set of
the closed subspace, because every field-valued point of `Spec R` factors through
`Spec (A ⧸ I)`. -/
theorem hasImageIn_testHom :
    HasImageIn B (Spec polyRing) hA (ambSpace B hA).1
      (subspacePoints B (Spec polyRing) hA (subSpace B hA))
      (testObj B hA) (testHom B hA) := by
  intro p
  obtain ⟨l, hl⟩ := exists_factor_subIncl B hA p
  exact ⟨(⟨p.carrier, p.contained, p.toBase, ⟨p.value ≫ testHom B hA, ⟨l, hl⟩⟩⟩ :
    FieldValuedPoint B (Spec polyRing) hA (subSpace B hA).toFunctor).class
      B (Spec polyRing) hA (subSpace B hA).toFunctor, rfl⟩

/-! ### Vanishing of the variables on an infinitesimal neighbourhood -/

/-- The `m`th variable, read as a global function on `Spec A`. -/
abbrev varSection (m : ℕ) : Γ(Spec polyRing, ⊤) :=
  (Scheme.ΓSpecIso polyRing).inv.hom (MvPolynomial.X m)

/-- The pullback of the `m`th variable along `Spec S ⟶ Spec A` is the image of that variable
in `S`. -/
private theorem appTop_specMap_varSection {S : CommRingCat.{0}} (f : polyRing ⟶ S) (m : ℕ) :
    (Spec.map f).appTop.hom (varSection m) =
      (Scheme.ΓSpecIso S).inv.hom (f.hom (MvPolynomial.X m)) :=
  (congrArg (fun t : polyRing ⟶ Γ(Spec S, ⊤) => t.hom (MvPolynomial.X m : MvPolynomial ℕ ℤ))
    (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- Each variable pulls back to `0` on `Spec (A ⧸ I)`. -/
theorem appTop_mkVar_varSection (m : ℕ) :
    (Spec.map mkVar).appTop.hom (varSection m) = 0 := by
  rw [appTop_specMap_varSection]
  show (Scheme.ΓSpecIso quotVar).inv.hom
    (Ideal.Quotient.mk varIdeal (MvPolynomial.X m : MvPolynomial ℕ ℤ)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (X_mem_varIdeal m), map_zero]

/-- **The variables vanish to order `n` on an `n`th-order infinitesimal neighbourhood of `Z`.**
Let `w : V ⟶ Spec A` be a morphism of the site whose inverse image of `Z` is a universal
`n`th-order thickening of `V`. Then the `(n+1)`st power of the pullback of each variable to
`Γ(V, ⊤)` vanishes.

Read on the identity étale chart of `V`, the defining ideal of the inverse image of `Z` is the
kernel of pullback of regular functions along the closed immersion `Z ×_{Spec A} V ⟶ V`
(`AlgebraicGeometry.Space.definingIdealAt_eq_ker`), and each variable lies in that kernel: the
closed immersion composed with `w` factors through `Spec (A ⧸ I) ⟶ Spec A`, because the
cartesian square presenting the inverse image exhibits its projection as a section of the
inverse image, hence of `Z` after composing with `w`. -/
theorem pow_appTop_varSection_eq_zero
    {V : BigFppfOver B (Spec polyRing) hA} (w : V ⟶ baseObj B hA) (n m : ℕ)
    (hn : IsUniversalNthOrderThickening B (Spec polyRing) hA n V
      ((subSpace B hA).preimage (yoneda.map w))) :
    ((toSch B hA).map w).appTop.hom (varSection m) ^ (n + 1) = 0 := by
  classical
  obtain ⟨hG, hid⟩ := hn.isNthOrderThickening
  -- the identity étale chart of `V`
  have hEt : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{0} : MorphismProperty Scheme.{0})
      (BigFppfOver.toScheme B (Spec polyRing) hA)).presheaf (𝟙 (yoneda.obj V)) := by
    rw [show (𝟙 (yoneda.obj V) : yoneda.obj V ⟶ yoneda.obj V) = yoneda.map (𝟙 V) from
      (yoneda.map_id V).symm]
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec polyRing) hA _ (𝟙 V)).2 ?_
    rw [CategoryTheory.Functor.map_id]
    exact inferInstance
  set W : SmallEtale B (Spec polyRing) hA
      ((schemeSpaceFunctor B (Spec polyRing) hA).obj V).1 :=
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj V)), hEt⟩ with hW
  -- the closed immersion presenting the inverse image of `Z` over the chart
  have hsq := hG.1.2.rep.isPullback W.1.hom
  have key := congrArg yonedaEquiv hsq.w
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at key
  -- the projection is a section of the inverse image of `Z`, so of `Z` after composing with `w`
  have hmem : (hG.1.2.rep.snd W.1.hom) ≫ w ∈
      (subSpace B hA).obj (op (hG.1.2.rep.pullback W.1.hom)) := by
    obtain ⟨y, hy⟩ : ∃ y : ((subSpace B hA).preimage (yoneda.map w)).toFunctor.obj
        (op (hG.1.2.rep.pullback W.1.hom)),
        yonedaEquiv (hG.1.2.rep.fst W.1.hom) = y := ⟨_, rfl⟩
    rw [hy] at key
    obtain ⟨y₀, hy₀⟩ := y
    have key' : y₀ = hG.1.2.rep.snd W.1.hom := key
    rw [key'] at hy₀
    exact hy₀
  obtain ⟨l, hl⟩ := hmem
  -- the variables vanish on the closed immersion
  have hcompmaps : (toSch B hA).map (hG.1.2.rep.snd W.1.hom) ≫ (toSch B hA).map w
      = (toSch B hA).map l ≫ Spec.map mkVar := by
    rw [← Functor.map_comp, show (hG.1.2.rep.snd W.1.hom) ≫ w = l ≫ subIncl B hA from hl.symm,
      Functor.map_comp]
    rfl
  have hfinal : ((toSch B hA).map (hG.1.2.rep.snd W.1.hom)).appTop.hom
      (((toSch B hA).map w).appTop.hom (varSection m)) = 0 := by
    have h1 : ((toSch B hA).map (hG.1.2.rep.snd W.1.hom) ≫
        (toSch B hA).map w).appTop.hom (varSection m) =
          ((toSch B hA).map (hG.1.2.rep.snd W.1.hom)).appTop.hom
            (((toSch B hA).map w).appTop.hom (varSection m)) := rfl
    rw [← h1, hcompmaps]
    show ((toSch B hA).map l).appTop.hom ((Spec.map mkVar).appTop.hom (varSection m)) = 0
    rw [appTop_mkVar_varSection, map_zero]
  -- conclude from the vanishing of the power of the defining ideal
  have hpow := hid W
  rw [definingIdealAt_eq_ker B (Spec polyRing) hA
    ((schemeSpaceFunctor B (Spec polyRing) hA).obj V) ⟨_, hG.1⟩ W] at hpow
  have hmemker : ((toSch B hA).map w).appTop.hom (varSection m) ∈
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec polyRing) hA).map
        (hG.1.2.rep.snd W.1.hom)).op).hom :=
    RingHom.mem_ker.2 hfinal
  exact Ideal.mem_bot.1 (le_of_eq hpow (Ideal.pow_mem_pow hmemker (n + 1)))

/-! ### The comparison is not an isomorphism -/

/-- The fppf topology of the big site over `Spec A`. -/
abbrev fppfTop : GrothendieckTopology (BigFppfOver B (Spec polyRing) hA) :=
  BigFppfOver.topology B (Spec polyRing) hA

/-- The inclusion of the union of the infinitesimal neighbourhoods of `Z` into the subfunctor
of sections of `Spec A` supported on `|Z|`. Its sheafification is the comparison morphism. -/
abbrev inclHom :
    (completionSubspaceSubfunctor B (Spec polyRing) hA (ambSpace B hA)
        (subSpace B hA)).toFunctor ⟶
      (completionSubfunctor B (Spec polyRing) hA (ambSpace B hA).1
        (subspacePoints B (Spec polyRing) hA (subSpace B hA))).toFunctor :=
  Subfunctor.homOfLe (completionSubspaceSubfunctor_le_completionSubfunctor
    B (Spec polyRing) hA (ambSpace B hA) (subSpace B hA))

/-- The pullback of the `m`th variable to `Γ(Spec R, ⊤)` is the image of that variable in `R`. -/
theorem appTop_mkPow_varSection (m : ℕ) :
    (Spec.map mkPow).appTop.hom (varSection m) =
      (Scheme.ΓSpecIso quotPow).inv.hom
        (Ideal.Quotient.mk powerIdeal (MvPolynomial.X m : MvPolynomial ℕ ℤ)) :=
  appTop_specMap_varSection mkPow m

/-- If the comparison morphism is an isomorphism then the inclusion of subfunctors it
sheafifies is locally surjective. -/
theorem isLocallySurjective_inclHom_of_isIso
    (hc : IsIso (completionSubspaceComparison B (Spec polyRing) hA (ambSpace B hA)
      (subSpace B hA))) :
    Presheaf.IsLocallySurjective (fppfTop B hA) (inclHom B hA) := by
  have h1 : IsIso ((sheafToPresheaf (fppfTop B hA) (Type 1)).map
      (completionSubspaceComparison B (Spec polyRing) hA (ambSpace B hA)
        (subSpace B hA))) := inferInstance
  exact Presheaf.isLocallySurjective_of_isIso_sheafifyMap _ _
    (h1 : IsIso ((fppfTop B hA).sheafifyMap (inclHom B hA)))

/-- The `i`th member of a covering family of the test object, as an object of the site over
`Spec A`. -/
abbrev coverObj
    (Q : PreZeroHypercover.{1}
      ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA))) (i : Q.I₀) :
    BigFppfOver B (Spec polyRing) hA :=
  Over.mk (Q.f i ≫ (testObj B hA).hom)

/-- The structure morphism of the `i`th member of a covering family to the test object. -/
abbrev coverHom
    (Q : PreZeroHypercover.{1}
      ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA))) (i : Q.I₀) :
    coverObj B hA Q i ⟶ testObj B hA :=
  Over.homMk (Q.f i)

/-- **A covering of `Spec R` on which the test section would have finite order.** If the
inclusion of subfunctors is locally surjective then, `Spec R` being affine, the covering sieve
witnessing this at the test section is refined by a standard fppf covering of `Spec R` on each
member of which the restricted section has inverse image of `Z` a universal finite-order
thickening. -/
theorem exists_order_cover
    (hls : Presheaf.IsLocallySurjective (fppfTop B hA) (inclHom B hA)) :
    ∃ (Q : PreZeroHypercover.{1}
        ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA))) (n : Q.I₀ → ℕ),
      _root_.AlgebraicGeometry.IsStandardFppfCovering
          (fun i => (toSch B hA).obj (coverObj B hA Q i))
          (fun i => (toSch B hA).map (coverHom B hA Q i)) ∧
        ∀ i, IsUniversalNthOrderThickening B (Spec polyRing) hA (n i) (coverObj B hA Q i)
          ((subSpace B hA).preimage
            (yoneda.map (coverHom B hA Q i ≫ testHom B hA))) := by
  classical
  have hbase : Sieve.overEquiv (testObj B hA) (Presheaf.imageSieve (inclHom B hA)
      (⟨ULift.up (testHom B hA), hasImageIn_testHom B hA⟩ :
        (completionSubfunctor B (Spec polyRing) hA (ambSpace B hA).1
          (subspacePoints B (Spec polyRing) hA (subSpace B hA))).toFunctor.obj
            (op (testObj B hA)))) ∈
      B.topology ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA)) :=
    Presheaf.imageSieve_mem (fppfTop B hA) (inclHom B hA) (U := op (testObj B hA)) _
  have hTaff : IsAffine (B.inclusion.obj
      ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA))) :=
    inferInstanceAs (IsAffine (Spec quotPow))
  obtain ⟨Q, -, hQstd, hQle⟩ := exists_standardFppf_refinement B hbase
  have horder : ∀ i, ∃ nn : ℕ, IsUniversalNthOrderThickening B (Spec polyRing) hA nn
      (coverObj B hA Q i)
      ((subSpace B hA).preimage (yoneda.map (coverHom B hA Q i ≫ testHom B hA))) := by
    intro i
    obtain ⟨t, ht⟩ := (Sieve.overEquiv_iff _ (Q.f i)).1 (hQle _ _ ⟨i⟩)
    have ht2 : t.1.down = coverHom B hA Q i ≫ testHom B hA :=
      congrArg (fun y => ULift.down y.1) ht
    obtain ⟨nn, hnn⟩ := t.2
    refine ⟨nn, ?_⟩
    rw [ht2, show (yonedaEquiv.symm (coverHom B hA Q i ≫ testHom B hA) :
        yoneda.obj (coverObj B hA Q i) ⟶ (ambSpace B hA).1) =
          yoneda.map (coverHom B hA Q i ≫ testHom B hA) from
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm] at hnn
    exact hnn
  choose n hn using horder
  exact ⟨Q, n, hQstd, hn⟩

/-- **A single exponent kills every variable of `R`, if the test section has finite order on a
standard fppf covering.** The product of the rings of global functions on the members of the
covering is faithfully flat over `Γ(Spec R, ⊤)`, so a global function vanishing on every member
vanishes; and on each member the `(N+1)`st power of each variable vanishes, where `N` bounds the
finitely many orders. -/
theorem exists_pow_appTop_mkPow_eq_zero
    (Q : PreZeroHypercover.{1}
      ((BigFppfOver.forget B (Spec polyRing) hA).obj (testObj B hA))) (n : Q.I₀ → ℕ)
    (hQstd : _root_.AlgebraicGeometry.IsStandardFppfCovering
      (fun i => (toSch B hA).obj (coverObj B hA Q i))
      (fun i => (toSch B hA).map (coverHom B hA Q i)))
    (hn : ∀ i, IsUniversalNthOrderThickening B (Spec polyRing) hA (n i) (coverObj B hA Q i)
      ((subSpace B hA).preimage (yoneda.map (coverHom B hA Q i ≫ testHom B hA)))) :
    ∃ N : ℕ, ∀ m : ℕ, (Spec.map mkPow).appTop.hom (varSection m) ^ (N + 1) = 0 := by
  classical
  have hfin := hQstd.finite_index
  let _ : Fintype Q.I₀ := Fintype.ofFinite Q.I₀
  have hZaff : IsAffine ((toSch B hA).obj (testObj B hA)) :=
    inferInstanceAs (IsAffine (Spec quotPow))
  have haff : ∀ i, IsAffine ((toSch B hA).obj (coverObj B hA Q i)) := hQstd.affine_source
  have hflat : ∀ i, Flat ((toSch B hA).map (coverHom B hA Q i)) := hQstd.flat
  let alg : ∀ i, Algebra Γ((toSch B hA).obj (testObj B hA), ⊤)
      Γ((toSch B hA).obj (coverObj B hA Q i), ⊤) :=
    fun i => (((toSch B hA).map (coverHom B hA Q i)).appTop.hom).toAlgebra
  have hff : Module.FaithfullyFlat Γ((toSch B hA).obj (testObj B hA), ⊤)
      (∀ i, Γ((toSch B hA).obj (coverObj B hA Q i), ⊤)) :=
    faithfullyFlat_pi_gamma_of_iUnion_range_eq_univ
      (fun i => (toSch B hA).map (coverHom B hA Q i)) hQstd.jointly_surjective (fun _ => rfl)
  have hinj : Function.Injective
      (algebraMap Γ((toSch B hA).obj (testObj B hA), ⊤)
        (∀ i, Γ((toSch B hA).obj (coverObj B hA Q i), ⊤))) :=
    FaithfulSMul.algebraMap_injective _ _
  refine ⟨Finset.univ.sup n, fun m => ?_⟩
  have hvan : ∀ i : Q.I₀, ((toSch B hA).map (coverHom B hA Q i)).appTop.hom
      ((Spec.map mkPow).appTop.hom (varSection m)) ^ (Finset.univ.sup n + 1) = 0 := fun i =>
    pow_eq_zero_of_le (Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ i)))
      (pow_appTop_varSection_eq_zero B hA (coverHom B hA Q i ≫ testHom B hA) (n i) m (hn i))
  refine hinj ?_
  rw [map_zero]
  funext i
  rw [Pi.algebraMap_apply]
  show ((toSch B hA).map (coverHom B hA Q i)).appTop.hom
    ((Spec.map mkPow).appTop.hom (varSection m) ^ (Finset.univ.sup n + 1)) = _
  rw [map_pow, hvan i]
  rfl

/-- **The test section does not lie locally in the union of the infinitesimal neighbourhoods of
`Z`.** A standard fppf covering on which it had finite order would supply a single exponent
killing every variable of `R`, which `MvPolynomial.exists_powerIdealMk_X_pow_ne_zero`
forbids. -/
theorem not_isLocallySurjective_inclHom :
    ¬ Presheaf.IsLocallySurjective (fppfTop B hA) (inclHom B hA) := by
  intro hls
  obtain ⟨Q, n, hQstd, hn⟩ := exists_order_cover B hA hls
  obtain ⟨N, hNvan⟩ := exists_pow_appTop_mkPow_eq_zero B hA Q n hQstd hn
  obtain ⟨m, hm⟩ := exists_powerIdealMk_X_pow_ne_zero N
  refine hm ?_
  have hinj2 : Function.Injective (Scheme.ΓSpecIso quotPow).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso quotPow).inv).1
  refine hinj2 ?_
  rw [map_pow, map_zero, ← appTop_mkPow_varSection]
  exact hNvan m

end AlgebraicGeometry.Space.Counterexample0H8N

namespace AlgebraicGeometry.Space

/-- **Stacks 0H8N, the negative half.** There are a scheme `S` in a big fppf site `B`, an
algebraic space `X` over `S` and a closed subspace `Z ⊆ X` for which the canonical morphism
`c : X^∧_Z ⟶ X_{/T}`, `T = |Z|`, is **not** an isomorphism.

Take `A = ℤ[x₀, x₁, x₂, …]`, `S = X = Spec A` and `Z = Spec (A ⧸ I)` the closed subscheme cut
out by `I = (x₀, x₁, x₂, …)`, which is not of finite presentation. The section
`Spec (A ⧸ (xₙ ^ (n+1) : n)) ⟶ Spec A` is supported on `|Z|`, because every variable is
nilpotent in the quotient and so dies in any field-valued point; but no infinitesimal
neighbourhood of `Z` contains it, not even after an fppf covering, because the exponent needed
to kill `xₘ` in the quotient grows with `m` while a covering supplies only finitely many
exponents and detects vanishing faithfully. -/
@[stacks 0H8N "the comparison is not an isomorphism in general"]
theorem not_isIso_completionSubspaceComparison :
    ∃ (B : BigFppfSite.{0}) (S : Scheme.{0}) (hS : B.Contains S)
      (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1),
      IsClosedSubspace B S hS Z ∧
        ¬ IsIso (completionSubspaceComparison B S hS X Z) := by
  obtain ⟨B, hA⟩ := BigFppfSite.exists_contains (Spec Counterexample0H8N.polyRing)
  exact ⟨B, _, hA, _, _, Counterexample0H8N.isClosedSubspace_subSpace B hA,
    fun hc => Counterexample0H8N.not_isLocallySurjective_inclHom B hA
      (Counterexample0H8N.isLocallySurjective_inclHom_of_isIso B hA hc)⟩

end AlgebraicGeometry.Space

end
