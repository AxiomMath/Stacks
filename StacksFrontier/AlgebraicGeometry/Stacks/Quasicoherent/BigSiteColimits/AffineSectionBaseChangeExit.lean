module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyAlgebraTower
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineMemberBaseChange
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSpannedRelations
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.QuasicoherentColimitsOfSpan

/-!
# Exiting the family descent engine through bijectivity

Flat descent along a covering family produces, from the member-wise base-change comparisons over
the double and the triple overlaps, a descent datum on the product of the modules of sections over
the members.  `SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange` exits that datum
through `Module.Descent.span_range_eq_top_of_comparison`, which keeps only one inclusion of the
sheaf axiom and concludes a span condition.  This file exits the same datum through
`Module.Descent.bijective_liftBaseChange_of_comparison` instead, which keeps both, and concludes
that the sections over each member are the base change of the sections over the object covered.

Three things separate the two exits.  The bijective exit needs the *separatedness* half of the
sheaf axiom as well as the amalgamation half, which is `SheafOfModules.injective_restrict`; it
needs the description of the descended module as an equivalence rather than as one implication,
whose extra direction is functoriality of restriction across the fibre product squares; and its
conclusion is bijectivity of a base change along the product of the coefficient rings of the
members, which has to be split into the individual members before a consumer can use it.  That
last step is `Module.BaseChange.exists_piAddEquiv`, exactly as in
`Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange`: the base change along the
product is a module over the product while each member's is a module over that member, so the
comparison between them is additive and no single ring is available over which it could be linear.

## Main results

* `Module.BaseChange.bijective_liftBaseChange_trans`: **two base changes compose**.  If the
  sections over an intermediate ring are the base change of those over the base and the sections
  over the top ring are the base change of those over the intermediate one, then they are the base
  change of those over the base.
* `Module.BaseChange.bijective_liftBaseChange_pi_apply`: **a base change along a finite product of
  rings is a product of base changes**, read at one factor.
* `SheafOfModules.exists_restrictₛₗ_eq_iff_pairwise_eq`: the locus where the two restrictions to
  the double overlaps of a covering family agree is exactly the set of families of restrictions of
  a single section, which is the sheaf axiom in the form the descended module of a family descent
  datum is cut out by.
* `SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange`: **the sections over each
  member of a covering family are the base change of the sections over the object covered**, from
  the member-wise base-change comparisons over the double and the triple overlaps.  This is
  `SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange` with its conclusion strengthened
  from a span to a bijection.
* `AlgebraicGeometry.FibredSite.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`: **a
  quasi-coherent module on the slice site at an affine object has a covering family of that object
  over whose affine objects its sections are the base change of its sections over the object
  itself**, which is the hypothesis `hbc` of
  `AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_hasSectionBaseChangeOn`.
* `AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite`: **the span
  condition on the affine slice sites, with no hypothesis beyond quasi-coherence.**
* `AlgebraicGeometry.FibredSite.hasColimitsOfSize_quasicoherentModules'` and
  `AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion'`: **the colimit
  clause of Stacks 06WN(1), with nothing assumed beyond the standing essential smallness of the
  fibred category** — quasi-coherent modules on a category fibred in groupoids have all small
  colimits, and those colimits are computed in all module sheaves for the associated fppf
  topology. They carry primed names because they are the weaker-hypothesis forms: the plain
  `AlgebraicGeometry.FibredSite.hasColimitsOfSize_quasicoherentModules` and
  `AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion` take the
  closure of quasi-coherence under colimits as a hypothesis, which is discharged here.

## Implementation notes

The comparison the span condition consumes is between the sections over the object the slice is
taken at and the sections over an affine object lying over a member of the covering family, and it
is **not** obtainable from a global presentation at the object the slice is taken at:
quasi-coherence never provides one there.  It is obtained in two steps instead — flat descent along
the family from the object to a member, then a presentation at a member of the family
quasi-coherence does provide — composed by
`Module.BaseChange.bijective_liftBaseChange_trans`.

The rings of global functions on the scheme underlying the object the slice is taken at are written
both as `p.obj x` and as `p.obj (Over.mk (𝟙 x)).left`.  The two are the same ring definitionally
but instance search does not identify them, so each algebra and module structure over that ring
whose consumer is stated at the second spelling is bound a second time with the same value.

`Module.BaseChange.bijective_liftBaseChange_pi_apply` takes the map to the product and the maps to
the factors as separate data related by a hypothesis, rather than projecting the first, so that the
conclusion speaks of the map a consumer already holds; the same shape is used throughout the
`SheafOfModules` statements below, where the maps are restrictions of a sheaf of modules and a
consumer holds them as linear maps built out of the restriction maps.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Module.BaseChange

/-- **Two base changes compose.**  Let `A → Bc → Cc` be a tower of commutative rings, let `ρ₁`
carry an `A`-module `M` to a `Bc`-module `N` and `ρ₂` carry `N` to a `Cc`-module `P`, and let `ρ`
be their composite.  If the base change of `ρ₁` along `A → Bc` and the base change of `ρ₂` along
`Bc → Cc` are bijective, so is the base change of `ρ` along `A → Cc`.

The identification used is `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which exhibits
`Cc ⊗[A] M` as `Cc ⊗[Bc] (Bc ⊗[A] M)`; tensoring the first comparison with `Cc` over `Bc` then
turns it into `Cc ⊗[Bc] N`, where the second comparison applies. -/
theorem bijective_liftBaseChange_trans
    (A Bc Cc : Type*) [CommRing A] [CommRing Bc] [CommRing Cc]
    [Algebra A Bc] [Algebra Bc Cc] [Algebra A Cc] [IsScalarTower A Bc Cc]
    {M N P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module Bc N] [IsScalarTower A Bc N]
    [AddCommGroup P] [Module A P] [Module Bc P] [Module Cc P]
    [IsScalarTower A Bc P] [IsScalarTower Bc Cc P] [IsScalarTower A Cc P]
    (ρ₁ : M →ₗ[A] N) (ρ₂ : N →ₗ[Bc] P) (ρ : M →ₗ[A] P) (hρ : ∀ m, ρ m = ρ₂ (ρ₁ m))
    (h₁ : Function.Bijective (ρ₁.liftBaseChange Bc))
    (h₂ : Function.Bijective (ρ₂.liftBaseChange Cc)) :
    Function.Bijective (ρ.liftBaseChange Cc) := by
  set e₁ : Bc ⊗[A] M ≃ₗ[Bc] N := LinearEquiv.ofBijective (ρ₁.liftBaseChange Bc) h₁ with he₁
  set Φ : Cc ⊗[A] M ≃ₗ[Cc] Cc ⊗[Bc] N :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Bc Cc Cc M).symm.trans
      (LinearEquiv.baseChange Bc Cc (Bc ⊗[A] M) N e₁) with hΦ
  have key : ∀ z, ρ.liftBaseChange Cc z = ρ₂.liftBaseChange Cc (Φ z) := by
    intro z
    induction z with
    | tmul c m =>
      rw [LinearMap.liftBaseChange_tmul, hΦ]
      have h0 : Φ (c ⊗ₜ[A] m) = c ⊗ₜ[Bc] ρ₁ m := by
        rw [hΦ]
        change (LinearEquiv.baseChange Bc Cc (Bc ⊗[A] M) N e₁)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A Bc Cc Cc M).symm
            (c ⊗ₜ[A] m)) = _
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
          LinearEquiv.baseChange_tmul, he₁]
        congr 1
        change (ρ₁.liftBaseChange Bc) ((1 : Bc) ⊗ₜ[A] m) = ρ₁ m
        rw [LinearMap.liftBaseChange_tmul, one_smul]
      rw [← hΦ, h0, LinearMap.liftBaseChange_tmul, hρ]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
  refine ⟨fun z z' hzz' => Φ.injective (h₂.1 ((key z).symm.trans (hzz'.trans (key z')))), ?_⟩
  intro q
  obtain ⟨y, hy⟩ := h₂.2 q
  exact ⟨Φ.symm y, (key _).trans (by rw [Φ.apply_symm_apply, hy])⟩

/-- **A base change along a finite product of rings is a product of base changes**, read at one
factor.  Let `ρ` carry an `A`-module `M` to the product of modules `Ni i`, with `ρi i` its value at
the `i`-th factor.  If the base change of `ρ` along `A → ∀ i, Bi i` is bijective, so is the base
change of each `ρi i` along `A → Bi i`.

The identification of `(∀ i, Bi i) ⊗[A] M` with `∀ i, Bi i ⊗[A] M` is
`Module.BaseChange.exists_piAddEquiv`, which is additive: the left-hand side is a module over the
product and the `i`-th factor of the right-hand side over `Bi i`, so there is no ring over which it
could be stated as a linear map.  Both halves of the conclusion are read off at one factor by
extending an element of that factor to the family which is zero elsewhere. -/
theorem bijective_liftBaseChange_pi_apply
    (A : Type*) [CommRing A] {ιi : Type*} [Finite ιi] (Bi : ιi → Type*)
    [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    {M : Type*} [AddCommGroup M] [Module A M]
    (Ni : ιi → Type*) [∀ i, AddCommGroup (Ni i)] [∀ i, Module A (Ni i)]
    [∀ i, Module (Bi i) (Ni i)] [∀ i, IsScalarTower A (Bi i) (Ni i)]
    (ρ : M →ₗ[A] ∀ i, Ni i) (ρi : ∀ i, M →ₗ[A] Ni i)
    (hρ : ∀ (m : M) (i : ιi), ρ m i = ρi i m)
    (h : Function.Bijective (ρ.liftBaseChange (∀ i, Bi i))) (i : ιi) :
    Function.Bijective ((ρi i).liftBaseChange (Bi i)) := by
  classical
  obtain ⟨E, hE⟩ := exists_piAddEquiv A M Bi (fun i => Bi i ⊗[A] M) fun _ => AddEquiv.refl _
  have hE' : ∀ (b : ∀ i, Bi i) (m : M) (j : ιi), E (b ⊗ₜ[A] m) j = b j ⊗ₜ[A] m := hE
  have key : ∀ (z : (∀ i, Bi i) ⊗[A] M) (j : ιi),
      ρ.liftBaseChange (∀ i, Bi i) z j = (ρi j).liftBaseChange (Bi j) (E z j) := by
    intro z
    induction z with
    | tmul b m =>
      intro j
      rw [LinearMap.liftBaseChange_tmul, show (b • ρ m) j = b j • ρ m j from rfl, hρ, hE',
        LinearMap.liftBaseChange_tmul]
    | add z z' hz hz' =>
      intro j
      rw [map_add, Pi.add_apply, hz, hz',
        show E (z + z') j = E z j + E z' j from congrFun (map_add E z z') j, map_add]
  refine ⟨fun z z' hzz' => ?_, fun y => ?_⟩
  · have hw : ρ.liftBaseChange (∀ i, Bi i) (E.symm (Function.update 0 i z)) =
        ρ.liftBaseChange (∀ i, Bi i) (E.symm (Function.update 0 i z')) := by
      refine funext fun j => ?_
      rw [key, key, E.apply_symm_apply, E.apply_symm_apply]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self]
        exact hzz'
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    have := congrFun (E.symm.injective (h.1 hw)) i
    rwa [Function.update_self, Function.update_self] at this
  · obtain ⟨z, hz⟩ := h.2 (Function.update 0 i y)
    refine ⟨E z i, ?_⟩
    rw [← key, hz, Function.update_self]

end Module.BaseChange

namespace SheafOfModules

universe w uC vC r m

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A family of sections over the members of a covering family agrees on the double overlaps
exactly when it is the family of restrictions of a single section.**

The forward implication is `SheafOfModules.exists_restrictₛₗ_eq_of_pairwise_eq`, the amalgamation
half of the sheaf axiom.  The converse is functoriality of restriction together with the
commutation of the fibre product square: both restrictions of a restricted section to an overlap
are its restriction along the common composite.

This is the description of the descended module of a family descent datum which
`Module.Descent.bijective_liftBaseChange_of_comparison` consumes.  The span exit
`Module.Descent.span_range_eq_top_of_comparison` uses only the forward implication; the converse is
what the bijective exit adds. -/
theorem exists_restrictₛₗ_eq_iff_pairwise_eq (N : SheafOfModules.{m} R) {T : C} {ι : Type w}
    {Y : ι → C} (g : ∀ i, Y i ⟶ T) {Pb : ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    (hcov : Sieve.ofArrows Y g ∈ J T) (uu : ∀ i, N.val.obj (op (Y i))) :
    (∀ i j, N.val.restrictₛₗ (pr₁ i j).op (uu i) =
        N.val.restrictₛₗ (pr₂ i j).op (uu j)) ↔
      ∃ n : N.val.obj (op T), ∀ i, N.val.restrictₛₗ (g i).op n = uu i :=
  ⟨N.exists_restrictₛₗ_eq_of_pairwise_eq g pr₁ pr₂ hpb hcov uu, by
    rintro ⟨n, hn⟩ i j
    rw [← hn i, ← hn j, N.val.restrictₛₗ_restrictₛₗ_op, N.val.restrictₛₗ_restrictₛₗ_op,
      (hpb i j).w]⟩

/-- **The sections over each member of a covering family are the base change of the sections over
the object covered**, from the member-wise base-change comparisons over the overlaps.

This is `SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange` with its conclusion
strengthened from a span to a bijection, and with exactly the same hypotheses about the geometry of
the overlaps and about the rings: the two factorisations of the identity through a diagonal, the
three commutations of a triple overlap, the fibre product squares, the ring isomorphisms exhibiting
the coefficient ring of an overlap as a tensor product, the semilinearity of restriction along the
four projections, and the two bijectivity statements `hbij₂` and `hbij₃`.

The strengthening is paid for in three places.  The descent datum is exited through
`Module.Descent.bijective_liftBaseChange_of_comparison` rather than through
`Module.Descent.span_range_eq_top_of_comparison`, which asks for the sheaf axiom as an equivalence
(`SheafOfModules.exists_restrictₛₗ_eq_iff_pairwise_eq`) and for injectivity of the restriction to
the members (`SheafOfModules.injective_restrict`, the separatedness half of the sheaf axiom, which
a span condition does not use).  Its conclusion is bijectivity of the base change along the product
of the coefficient rings of the members, which
`Module.BaseChange.bijective_liftBaseChange_pi_apply` reads at a single member. -/
theorem bijective_liftBaseChange_of_family_cancelBaseChange (N : SheafOfModules.{m} R)
    {T : C} {ι : Type w} [Finite ι] {Y : ι → C} (g : ∀ i, Y i ⟶ T)
    {Pb : ι → ι → C} {Pb₃ : ι → ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
    (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k)
    (hδ₁ : ∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) (hδ₂ : ∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i))
    (hc₁ : ∀ i j k, t₁₂ i j k ≫ pr₁ i j = t₁₃ i j k ≫ pr₁ i k)
    (hc₂ : ∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k)
    (hc₃ : ∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    (hcov : Sieve.ofArrows Y g ∈ J T)
    (A : Type*) [CommRing A] (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (D : ι → ι → Type*) [∀ i j, CommRing (D i j)] [∀ i j, Algebra A (D i j)]
    [∀ i j, Algebra (Bi j) (D i j)]
    (D₃ : ι → ι → ι → Type*) [∀ i j k, CommRing (D₃ i j k)]
    [∀ i j k, Algebra (D j k) (D₃ i j k)]
    [Module A (N.val.obj (op T))]
    [∀ i, Module A (N.val.obj (op (Y i)))] [∀ i, Module (Bi i) (N.val.obj (op (Y i)))]
    [∀ i, IsScalarTower A (Bi i) (N.val.obj (op (Y i)))]
    [∀ i j, Module A (N.val.obj (op (Pb i j)))] [∀ i j, Module (Bi j) (N.val.obj (op (Pb i j)))]
    [∀ i j, Module (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower A (Bi j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower (Bi j) (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower A (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j k, Module A (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, Module (D j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, Module (D₃ i j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, IsScalarTower A (D j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, IsScalarTower (D j k) (D₃ i j k) (N.val.obj (op (Pb₃ i j k)))]
    [Module.Flat A (∀ i, Bi i)]
    (v₁ : ∀ i j, Bi i →+* D i j) (ψ : ∀ i j, Bi i ⊗[A] Bi j ≃+* D i j)
    (hv : ∀ (i j : ι) (b : Bi i), ψ i j (b ⊗ₜ[A] (1 : Bi j)) = v₁ i j b)
    (hw : ∀ (i j : ι) (c : Bi j), ψ i j ((1 : Bi i) ⊗ₜ[A] c) = algebraMap (Bi j) (D i j) c)
    (u₁ : ∀ i j k, Bi i →+* D₃ i j k) (ψ₃ : ∀ i j k, Bi i ⊗[A] D j k ≃+* D₃ i j k)
    (hu : ∀ (i j k : ι) (b : Bi i), ψ₃ i j k (b ⊗ₜ[A] (1 : D j k)) = u₁ i j k b)
    (hw₃ : ∀ (i j k : ι) (d : D j k),
      ψ₃ i j k ((1 : Bi i) ⊗ₜ[A] d) = algebraMap (D j k) (D₃ i j k) d)
    (w₁₂ : ∀ i j k, D i j →+* D₃ i j k) (w₁₃ : ∀ i j k, D i k →+* D₃ i j k)
    (wδ : ∀ i, D i i →+* Bi i)
    (hwδ : ∀ (i : ι) (b : Bi i), wδ i (v₁ i i b) = b)
    (h₁₂ : ∀ (i j k : ι) (b : Bi i), w₁₂ i j k (v₁ i j b) = u₁ i j k b)
    (h₁₃ : ∀ (i j k : ι) (b : Bi i), w₁₃ i j k (v₁ i k b) = u₁ i j k b)
    (hsmq₁ : ∀ (i j : ι) (b : Bi i) (n : N.val.obj (op (Y i))),
      N.val.restrictₛₗ (pr₁ i j).op (b • n) = v₁ i j b • N.val.restrictₛₗ (pr₁ i j).op n)
    (hsmδ : ∀ (i : ι) (d : D i i) (ww : N.val.obj (op (Pb i i))),
      N.val.restrictₛₗ (δ i).op (d • ww) = wδ i d • N.val.restrictₛₗ (δ i).op ww)
    (hsm₁₂ : ∀ (i j k : ι) (d : D i j) (ww : N.val.obj (op (Pb i j))),
      N.val.restrictₛₗ (t₁₂ i j k).op (d • ww) =
        w₁₂ i j k d • N.val.restrictₛₗ (t₁₂ i j k).op ww)
    (hsm₁₃ : ∀ (i j k : ι) (d : D i k) (ww : N.val.obj (op (Pb i k))),
      N.val.restrictₛₗ (t₁₃ i j k).op (d • ww) =
        w₁₃ i j k d • N.val.restrictₛₗ (t₁₃ i j k).op ww)
    (ρ₂ : ∀ i j, N.val.obj (op (Y j)) →ₗ[Bi j] N.val.obj (op (Pb i j)))
    (hρ₂ : ∀ (i j : ι) (n : N.val.obj (op (Y j))),
      ρ₂ i j n = N.val.restrictₛₗ (pr₂ i j).op n)
    (hbij₂ : ∀ i j, Function.Bijective ((ρ₂ i j).liftBaseChange (D i j)))
    (ρ₃ : ∀ i j k, N.val.obj (op (Pb j k)) →ₗ[D j k] N.val.obj (op (Pb₃ i j k)))
    (hρ₃ : ∀ (i j k : ι) (ww : N.val.obj (op (Pb j k))),
      ρ₃ i j k ww = N.val.restrictₛₗ (t₂₃ i j k).op ww)
    (hbij₃ : ∀ i j k, Function.Bijective ((ρ₃ i j k).liftBaseChange (D₃ i j k)))
    (ρ : N.val.obj (op T) →ₗ[A] ∀ i, N.val.obj (op (Y i)))
    (hρ : ∀ (n : N.val.obj (op T)) (i : ι), ρ n i = N.val.restrictₛₗ (g i).op n)
    (ρmem : ∀ i, N.val.obj (op T) →ₗ[A] N.val.obj (op (Y i)))
    (hρmem : ∀ (i : ι) (n : N.val.obj (op T)), ρmem i n = N.val.restrictₛₗ (g i).op n)
    (i : ι) :
    Function.Bijective ((ρmem i).liftBaseChange (Bi i)) := by
  obtain ⟨e, e₃, he, he₃, he₃tmul⟩ := Module.Descent.exists_cancelBaseChange_pi_pair A Bi D D₃
    v₁ ψ hv hw u₁ ψ₃ hu hw₃ ρ₂ hbij₂ ρ₃ hbij₃
  obtain ⟨d, hd⟩ := PresheafOfModules.exists_family_datum_of_baseChange pr₁ pr₂ δ t₁₂ t₁₃ t₂₃
    hδ₁ hδ₂ hc₁ hc₂ hc₃ A Bi D D₃ v₁ u₁ w₁₂ w₁₃ wδ hwδ h₁₂ h₁₃ hsmq₁ hsmδ hsm₁₂ hsm₁₃
    e (fun s uu a b => by rw [he, hρ₂]) e₃ he₃ (fun s y a b c => by rw [he₃tmul, hρ₃])
  have hinj : Function.Injective ρ := fun n n' hnn' =>
    N.injective_restrict g hcov (funext fun j =>
      show N.val.restrictₛₗ (g j).op n = N.val.restrictₛₗ (g j).op n' by
        rw [← hρ n j, ← hρ n' j, hnn'])
  have hone : ∀ (uu : ∀ i, N.val.obj (op (Y i))) (a b : ι),
      e ((1 : ∀ i, Bi i) ⊗ₜ[A] uu) a b = N.val.restrictₛₗ (pr₂ a b).op (uu b) := fun uu a b => by
    rw [he, hρ₂, Pi.one_apply, map_one, one_smul]
  have hmem : ∀ uu : ∀ i, N.val.obj (op (Y i)),
      (fun a b => N.val.restrictₛₗ (pr₁ a b).op (uu a)) =
          (fun a b => e ((1 : ∀ i, Bi i) ⊗ₜ[A] uu) a b) ↔
        uu ∈ LinearMap.range ρ := by
    intro uu
    refine Iff.trans ⟨fun hpq a b => ?_, fun hag => funext fun a => funext fun b => ?_⟩
      ((N.exists_restrictₛₗ_eq_iff_pairwise_eq g pr₁ pr₂ hpb hcov uu).trans ?_)
    · rw [← hone uu a b]
      exact congrFun (congrFun hpq a) b
    · rw [hone uu a b]
      exact hag a b
    · exact ⟨fun ⟨n, hn⟩ => ⟨n, funext fun a => (hρ n a).trans (hn a)⟩,
        fun ⟨n, hn⟩ => ⟨n, fun a => (hρ n a).symm.trans (congrFun hn a)⟩⟩
  have hbijpi : Function.Bijective (ρ.liftBaseChange (∀ i, Bi i)) :=
    Module.Descent.bijective_liftBaseChange_of_comparison A (∀ i, Bi i) d e e.injective
      (fun uu a b => N.val.restrictₛₗ (pr₁ a b).op (uu a))
      (fun uu a b => e ((1 : ∀ i, Bi i) ⊗ₜ[A] uu) a b)
      (fun uu => funext fun a => funext fun b => (hd uu a b).symm) (fun _ => rfl) ρ hinj hmem
  exact Module.BaseChange.bijective_liftBaseChange_pi_apply A Bi
    (fun j => N.val.obj (op (Y j))) ρ ρmem
    (fun n j => (hρ n j).trans (hρmem j n).symm) hbijpi i

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

universe v w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  {x : 𝒳}

include hp in
/-- The linear map induced by restriction along `f`, given that restriction is linear over `A`. -/
private noncomputable def restrictLinear
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)) {Z Z' : Over x}
    (f : Z' ⟶ Z) {A : Type*} [CommRing A] [Module A (N.val.obj (op Z))]
    [Module A (N.val.obj (op Z'))]
    (h : ∀ (c : A) (n : N.val.obj (op Z)),
      N.val.restrictₛₗ f.op (c • n) = c • N.val.restrictₛₗ f.op n) :
    N.val.obj (op Z) →ₗ[A] N.val.obj (op Z') where
  toFun n := N.val.restrictₛₗ f.op n
  map_add' := map_add _
  map_smul' := h

include hp in
/-- **The sections over the affine objects of a finite affine covering family are the base change
of the sections over the object the slice is taken at.**  This is flat descent along the family,
whose two inputs over the double and the triple overlaps are the presentations at the objects the
members map to; from a member to an affine object over it, the comparison is a presentation, and
the two steps compose. -/
private theorem hasSectionBaseChangeOn_of_affine_family
    (hx : IsAffineOver B S hS (p.obj x))
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    {m : ℕ} (Y : Fin m → Over x) (g : ∀ j, Y j ⟶ Over.mk (𝟙 x))
    (hYaff : ∀ j, IsAffineOver B S hS (p.obj (Y j).left))
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
      (Over.mk (𝟙 x)))
    (hfppf : Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left))
        (fun j => (BigFppfOver.toScheme B S hS).map (p.map (g j).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left)))
    (V : Fin m → Over x) (hpres : ∀ j, (N.over (V j)).HasGlobalPresentation)
    (cc : ∀ j, Y j ⟶ V j) :
    HasSectionBaseChangeOn B S hS p hp
      (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} N)
      fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j) := by
  classical
  -- the module structures on the sections over the members
  let mT : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Over.mk (𝟙 x)))) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Over.mk (𝟙 x))))
    (N.val.obj (op (Over.mk (𝟙 x)))))
  let mYB : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
      (N.val.obj (op (Y i))) := fun i => inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Y i)))
    (N.val.obj (op (Y i))))
  let algY : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := fun i =>
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map (g i).left)).appTop.hom
  let mYA : ∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      (N.val.obj (op (Y i))) := fun i => Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
  have twY : ∀ i, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) (N.val.obj (op (Y i))) :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρmem : ∀ i, N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x), ⊤)] N.val.obj (op (Y i)) := fun i =>
    restrictLinear B S hS p hp N (g i) (N.val.map_smul (g i).op)
  have hmem : ∀ i, Function.Bijective ((ρmem i).liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := by
    obtain ⟨Pb, Pb₃, pr₁, pr₂, δ, q, t₁₂, t₁₃, t₂₃, hPbaff, hPb₃aff, hpb, hpb₃,
      hδ₁, hδ₂, hq₁₂, hq₁₃, hcc₂, hcc₃⟩ :=
      exists_affine_family_overlaps B S hS p hp Y g hx hYaff
    -- the four layers of rings, and the algebra structures between them
    let algY' : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤) := algY
    let algD : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) := fun i j =>
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map (p.map (pr₁ i j ≫ g i).left)).appTop.hom
    let algD' : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) := algD
    let algBD : ∀ i j, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) := fun i j =>
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map (pr₂ i j).left)).appTop.hom
    let algD₃ : ∀ i j k, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤) := fun i j k =>
      RingHom.toAlgebra
        ((BigFppfOver.toScheme B S hS).map (p.map (q i j k ≫ g i).left)).appTop.hom
    let algD₃' : ∀ i j k,
        Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Over.mk (𝟙 x)).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤) := algD₃
    let algDD₃ : ∀ i j k, Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤) := fun i j k =>
      RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map (t₂₃ i j k).left)).appTop.hom
    -- the module structures on the sections
    let mPD : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
        (N.val.obj (op (Pb i j))) := fun i j => inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Pb i j)))
      (N.val.obj (op (Pb i j))))
    let mPA : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (N.val.obj (op (Pb i j))) := fun i j => Module.compHom _
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤))
    let mPA' : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj
        (p.obj (Over.mk (𝟙 x)).left), ⊤) (N.val.obj (op (Pb i j))) := mPA
    let mPB : ∀ i j, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        (N.val.obj (op (Pb i j))) := fun i j => Module.compHom _
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤))
    have twPBD : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
        (N.val.obj (op (Pb i j))) := fun _ _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have twPAD : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
        (N.val.obj (op (Pb i j))) := fun _ _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have twPAB : ∀ i j, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        (N.val.obj (op (Pb i j))) := fun i j =>
      isScalarTower_appTopGamma B S hS p hp N (pr₂ i j) (g j) (pr₁ i j ≫ g i)
        (hpb i j).w.symm rfl (fun _ _ => rfl) fun _ _ => rfl
    let mP₃D₃ : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤)
        (N.val.obj (op (Pb₃ i j k))) := fun i j k => inferInstanceAs (Module
      (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op (Pb₃ i j k)))
      (N.val.obj (op (Pb₃ i j k))))
    let mP₃A : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (N.val.obj (op (Pb₃ i j k))) := fun i j k => Module.compHom _
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤))
    let mP₃A' : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj
        (p.obj (Over.mk (𝟙 x)).left), ⊤) (N.val.obj (op (Pb₃ i j k))) := mP₃A
    let mP₃D : ∀ i j k, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
        (N.val.obj (op (Pb₃ i j k))) := fun i j k => Module.compHom _
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤))
    have twP₃DD₃ : ∀ i j k,
        IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤)
          (N.val.obj (op (Pb₃ i j k))) := fun _ _ _ =>
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have twP₃AD : ∀ i j k, IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
        (N.val.obj (op (Pb₃ i j k))) := fun i j k =>
      isScalarTower_appTopGamma B S hS p hp N (t₂₃ i j k) (pr₁ j k ≫ g j) (q i j k ≫ g i)
        (hpb₃ i j k).w.symm rfl (fun _ _ => rfl) fun _ _ => rfl
    -- the rings of the overlaps as tensor products
    have hψex : ∀ i j, ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
          ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤) ≃+*
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤),
        (∀ b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤),
            ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
              (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤))) =
              ((BigFppfOver.toScheme B S hS).map (p.map (pr₁ i j).left)).appTop.hom b) ∧
          ∀ c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤),
            ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
              ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)] c) =
              algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
                Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤) c := fun i j =>
      exists_ringEquivTensorGamma_of_isPullback B S hS p hp (hpb i j) hx (hYaff i) (hYaff j)
        rfl rfl rfl rfl
    choose ψ hψv hψw using hψex
    have hψ₃ex : ∀ i j k, ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)
          ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤) ≃+*
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤),
        (∀ b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤),
            ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
              (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤))) =
              ((BigFppfOver.toScheme B S hS).map (p.map (q i j k).left)).appTop.hom b) ∧
          ∀ c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤),
            ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤))
              ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)] c) =
              algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
                Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤) c :=
      fun i j k => exists_ringEquivTensorGamma_of_isPullback B S hS p hp (hpb₃ i j k) hx
        (hYaff i) (hPbaff j k) rfl rfl rfl rfl
    choose ψ₃ hψ₃u hψ₃w using hψ₃ex
    -- faithful flatness of the product of the rings of the members
    have hff : Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) :=
      faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage B S hS p Y g hx hYaff hfppf
        fun _ => rfl
    have hflat : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y i).left), ⊤)) := inferInstance
    -- the restrictions to the members, and the two comparisons over the overlaps
    let ρ₂ : ∀ i j, N.val.obj (op (Y j)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        (p.obj (Y j).left), ⊤)] N.val.obj (op (Pb i j)) := fun i j =>
      restrictLinear B S hS p hp N (pr₂ i j) (N.val.map_smul (pr₂ i j).op)
    let ρ₃ : ∀ i j k, N.val.obj (op (Pb j k)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
        (p.obj (Pb j k).left), ⊤)] N.val.obj (op (Pb₃ i j k)) := fun i j k =>
      restrictLinear B S hS p hp N (t₂₃ i j k) (N.val.map_smul (t₂₃ i j k).op)
    have hbij₂ : ∀ i j, Function.Bijective ((ρ₂ i j).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)) := fun i j =>
      bijective_liftBaseChange_of_hasGlobalPresentation_over B S hS p hp (V j)
        (hpres j) (cc j) (pr₂ i j ≫ cc j) (pr₂ i j) rfl (hYaff j) (hPbaff i j)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y j).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb i j).left), ⊤)
        (sectionRingEquivGamma B S hS p hp .fppf (Y j)) (fun _ _ => rfl)
        (sectionRingEquivGamma B S hS p hp .fppf (Pb i j)) (fun _ _ => rfl) (fun _ => rfl)
        (ρ₂ i j) fun _ => rfl
    have hbij₃ : ∀ i j k, Function.Bijective ((ρ₃ i j k).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤)) := fun i j k =>
      bijective_liftBaseChange_of_hasGlobalPresentation_over B S hS p hp (V k)
        (hpres k) (pr₂ j k ≫ cc k) (t₂₃ i j k ≫ pr₂ j k ≫ cc k) (t₂₃ i j k) rfl
        (hPbaff j k) (hPb₃aff i j k)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb j k).left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ i j k).left), ⊤)
        (sectionRingEquivGamma B S hS p hp .fppf (Pb j k)) (fun _ _ => rfl)
        (sectionRingEquivGamma B S hS p hp .fppf (Pb₃ i j k)) (fun _ _ => rfl) (fun _ => rfl)
        (ρ₃ i j k) fun _ => rfl
    -- the descent along the extracted family
    exact fun i =>
      SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange N g pr₁ pr₂ δ t₁₂ t₁₃ t₂₃
        hδ₁ hδ₂ (fun a b c => (hq₁₂ a b c).trans (hq₁₃ a b c).symm) hcc₂ hcc₃ hpb hcov
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
        (fun a => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y a).left), ⊤))
        (fun a b => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb a b).left), ⊤))
        (fun a b c => Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Pb₃ a b c).left), ⊤))
        (fun a b => ((BigFppfOver.toScheme B S hS).map (p.map (pr₁ a b).left)).appTop.hom)
        ψ hψv hψw
        (fun a b c => ((BigFppfOver.toScheme B S hS).map (p.map (q a b c).left)).appTop.hom)
        ψ₃ hψ₃u hψ₃w
        (fun a b c => ((BigFppfOver.toScheme B S hS).map (p.map (t₁₂ a b c).left)).appTop.hom)
        (fun a b c => ((BigFppfOver.toScheme B S hS).map (p.map (t₁₃ a b c).left)).appTop.hom)
        (fun a => ((BigFppfOver.toScheme B S hS).map (p.map (δ a).left)).appTop.hom)
        (fun a b =>
          (appTopGamma_comp_apply_of_eq B S hS p (δ a) (pr₁ a a) (𝟙 (Y a)) (hδ₁ a) b).trans
            (appTopGamma_id_apply B S hS p b))
        (fun a b c => appTopGamma_comp_apply_of_eq B S hS p (t₁₂ a b c) (pr₁ a b) (q a b c)
          (hq₁₂ a b c))
        (fun a b c => appTopGamma_comp_apply_of_eq B S hS p (t₁₃ a b c) (pr₁ a c) (q a b c)
          (hq₁₃ a b c))
        (fun a b => restrictₛₗ_smul_appTopGamma B S hS p hp N (pr₁ a b)
          (fun _ _ => rfl) fun _ _ => rfl)
        (fun a => restrictₛₗ_smul_appTopGamma B S hS p hp N (δ a) (fun _ _ => rfl) fun _ _ => rfl)
        (fun a b c => restrictₛₗ_smul_appTopGamma B S hS p hp N (t₁₂ a b c)
          (fun _ _ => rfl) fun _ _ => rfl)
        (fun a b c => restrictₛₗ_smul_appTopGamma B S hS p hp N (t₁₃ a b c)
          (fun _ _ => rfl) fun _ _ => rfl)
        ρ₂ (fun _ _ _ => rfl) hbij₂ ρ₃ (fun _ _ _ _ => rfl) hbij₃
          (LinearMap.pi ρmem) (fun _ _ => rfl)
        ρmem (fun _ _ => rfl) i
  refine fun W hQW => ?_
  obtain ⟨hWaff, jj, ⟨bb⟩⟩ := hQW
  intro mNUT mNUW algW mNUW' twNU
  have hfacW : bb ≫ g jj = Over.mkIdTerminal.from W :=
    (Over.mkIdTerminal (X := x)).hom_ext _ _
  let algBW : Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) :=
    RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map bb.left)).appTop.hom
  have twABW : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (appTopGamma_comp_apply_of_eq B S hS p bb (g jj) (Over.mkIdTerminal.from W) hfacW c).symm
  let mWC : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (N.val.obj (op W)) := inferInstanceAs (Module
    (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj (op W)) (N.val.obj (op W)))
  let mWB : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      (N.val.obj (op W)) := Module.compHom _
    (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  let mWA : Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) (N.val.obj (op W)) :=
    Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
  have twWBC : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twWAC : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have twWAB : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤) (N.val.obj (op W)) :=
    IsScalarTower.of_algebraMap_smul fun c n =>
      congrArg (fun d : Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) => d • n)
        (appTopGamma_comp_apply_of_eq B S hS p bb (g jj) (Over.mkIdTerminal.from W) hfacW c)
  let ρ₂W : N.val.obj (op (Y jj)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj (Y jj).left), ⊤)] N.val.obj (op W) :=
    restrictLinear B S hS p hp N bb (N.val.map_smul bb.op)
  have hbijW : Function.Bijective (ρ₂W.liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)) :=
    bijective_liftBaseChange_of_hasGlobalPresentation_over B S hS p hp (V jj)
      (hpres jj) (cc jj) (bb ≫ cc jj) bb rfl (hYaff jj) hWaff
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (sectionRingEquivGamma B S hS p hp .fppf (Y jj)) (fun _ _ => rfl)
      (sectionRingEquivGamma B S hS p hp .fppf W) (fun _ _ => rfl) (fun _ => rfl)
      ρ₂W fun _ => rfl
  let ρW : N.val.obj (op (Over.mk (𝟙 x))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)]
      N.val.obj (op W) :=
    restrictLinear B S hS p hp N (Over.mkIdTerminal.from W)
      (N.val.map_smul (Over.mkIdTerminal.from W).op)
  have hcomp : ∀ n, ρW n = ρ₂W (ρmem jj n) := fun n =>
    show N.val.restrictₛₗ (Over.mkIdTerminal.from W).op n =
        N.val.restrictₛₗ bb.op (N.val.restrictₛₗ (g jj).op n) by
      rw [N.val.restrictₛₗ_restrictₛₗ_op, hfacW]
  have htrans : Function.Bijective (ρW.liftBaseChange
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)) :=
    Module.BaseChange.bijective_liftBaseChange_trans
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Y jj).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      (ρmem jj) ρ₂W ρW hcomp (hmem jj) hbijW
  exact Module.BaseChange.bijective_liftBaseChange_of_comm _ ρW
    (by exact ULift.moduleEquiv) (by exact ULift.moduleEquiv) (fun _ => rfl) htrans

include hp in
/-- **A quasi-coherent module on the slice site at an affine object has a covering family of that
object over whose affine objects its sections are the base change of its sections over the object
itself.**  This is the hypothesis `hbc` of
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_hasSectionBaseChangeOn`.

The family is extracted from the one quasi-coherence provides: that one carries global
presentations on the iterated slices at its members but is neither finite nor affine, so
`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le_over` replaces it by a finite
family of affine objects whose image in schemes is an fppf covering family, each member of which
factors through a member of the original one by `CategoryTheory.Sieve.mem_ofArrows_iff`.  No
presentation is claimed on the slice at a member of the extracted family; what the factorisation
supplies is the hypothesis of
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over`, whose base
object is the member of the original family and whose two affine objects are the ones compared.

The comparison asked for is between the sections over the object the slice is taken at and the
sections over an affine object lying over a member, and it is obtained in two steps.  From the
object itself to a member it is flat descent along the extracted family,
`SheafOfModules.bijective_liftBaseChange_of_family_cancelBaseChange`, whose two inputs over the
overlaps are
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation_over`; no
presentation on the slice at the object itself is used, and none is available, quasi-coherence
never providing one there.  From a member to an affine object over it, it is that same statement
once more.  The two compose by `Module.BaseChange.bijective_liftBaseChange_trans`.

The rings are the rings of global functions on the underlying schemes, the ring of an overlap is
exhibited as a tensor product by
`AlgebraicGeometry.FibredSite.exists_ringEquivTensorGamma_of_isPullback`, the identities between
the induced maps are
`AlgebraicGeometry.FibredSite.appTopGamma_comp_apply_of_eq`, the semilinearity of restriction is
`AlgebraicGeometry.FibredSite.restrictₛₗ_smul_appTopGamma`, and the faithful flatness of the
product of the rings of the members is
`AlgebraicGeometry.FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`.

The conclusion is asked of the universe lift of the module, because
`SheafOfModules.HasSpannedRelationsOn` quantifies over the coverings of that lift; the sections of
the lift are the sections of the module lifted, so the comparison for the lift is the comparison
for the module transported along `ULift.up` by
`Module.BaseChange.bijective_liftBaseChange_of_comm`. -/
theorem exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite
    (hx : IsAffineOver B S hS (p.obj x))
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    (hN : N.IsQuasicoherentOnSite) :
    ∃ (m : ℕ) (Y : Fin m → Over x) (g : ∀ j, Y j ⟶ Over.mk (𝟙 x)),
      Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x)
          (Over.mk (𝟙 x)) ∧
        HasSectionBaseChangeOn B S hS p hp
          (SheafOfModules.uliftForPresentation.{max v w, w, u, u, max v w u} N)
          fun W => IsAffineOver B S hS (p.obj W.left) ∧ ∃ j, Nonempty (W ⟶ Y j) := by
  classical
  obtain ⟨I₀, V, f₀, hcov₀, hpres⟩ := hN.locally_hasGlobalPresentation (Over.mk (𝟙 x))
  obtain ⟨m, Y, g, hYaff, hle, hcov, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le_over B S hS p hp (𝟙 x) hx (Sieve.ofArrows V f₀) hcov₀
  choose kk cc hcc using fun i => (Sieve.mem_ofArrows_iff V f₀ (g i)).1 (hle i)
  exact ⟨m, Y, g, hcov, hasSectionBaseChangeOn_of_affine_family B S hS p hp hx N Y g hYaff hcov
    hfppf (fun j => V (kk j)) (fun j => hpres (kk j)) cc⟩

include hp in
/-- **The span condition on the affine slice sites, with no hypothesis beyond
quasi-coherence.**  Every quasi-coherent module on the slice site at an affine object of a
category fibred in groupoids over the big fppf category of schemes is locally spanned by its
sections over that object, and so are the relations between any family of its generators.

This is
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_hasSectionBaseChangeOn` with its
hypothesis `hbc` discharged by
`AlgebraicGeometry.FibredSite.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`; the
covering family is the finite affine family extracted there, so the existentially quantified
index type is `Fin m`. -/
theorem isAffineLocallySpanned_of_isQuasicoherentOnSite :
    IsAffineLocallySpanned B S hS p hp :=
  isAffineLocallySpanned_of_hasSectionBaseChangeOn B S hS p hp fun i N hN => by
    obtain ⟨m, Y, g, hcov, hbc⟩ :=
      exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite B S hS p hp i.property N hN
    exact ⟨Fin m, Y, g, hcov, hbc⟩

variable [EssentiallySmall.{u} 𝒳]

include hp in
/-- **Quasi-coherent modules on a category fibred in groupoids have all small colimits.**  This
is the existence half of the colimit clause of Stacks 06WN(1) with both hypotheses of
`AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_span` discharged: the closure
one inside that statement by
`AlgebraicGeometry.FibredSite.hasAffineColimitPresentations`, and the span one by
`AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite`.  What is left
assumed is the standing essential smallness of the fibred category, which is what makes the
colimits in question small. -/
theorem hasColimitsOfSize_quasicoherentModules' :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, v, w, u} B S hS p hp) :=
  hasColimits_quasicoherentModules_of_span B S hS p hp
    (isAffineLocallySpanned_of_isQuasicoherentOnSite B S hS p hp)

include hp in
/-- **Colimits of quasi-coherent modules are fppf-module colimits.**  The inclusion of the
quasi-coherent modules into all module sheaves for the associated fppf topology preserves all
small colimits; this is the comparison half of the colimit clause of Stacks 06WN(1), again with
both hypotheses of
`AlgebraicGeometry.FibredSite.inclusion_preservesColimits_of_span` discharged and only the
standing essential smallness left assumed.

Right exactness of the inclusion functor, Stacks 06WV(3), is this statement: the source
derives it from the agreement of colimits, Stacks 06WV(4). -/
@[stacks 06WV "inclusion_right_exact"]
theorem preservesColimitsOfSize_quasicoherentInclusion' :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  inclusion_preservesColimits_of_span B S hS p hp
    (isAffineLocallySpanned_of_isQuasicoherentOnSite B S hS p hp)

end AlgebraicGeometry.FibredSite

end
