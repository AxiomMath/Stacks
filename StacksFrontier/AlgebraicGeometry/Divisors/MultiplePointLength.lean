module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# The length of a multiple point, and the dimension count of [Stacks, Tag 0AYT] (2)

Let `Y` be a locally Noetherian integral scheme proper over a field `k`, let `y ∈ Y` be a closed
point whose local ring `𝒪_{Y,y}` is a discrete valuation ring, let `D = ℐ_y^{N+1}` be the
`(N+1)`-st power of the ideal sheaf of `y` and let `i : Z ⟶ Y` be the closed immersion of the
subscheme it cuts out. This file proves

`N + 1 ≤ dim_k H⁰(Y, i_* i^* 𝒪_Y((N+1)y))`,

which is the dimension count of clause (2) of [Stacks, Tag 0AYT] in exactly the shape the proof
of [Stacks, Tag 0A27] consumes: it is the inequality `hd'` of
`Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank` at `d = N + 1`.

The route is the source's, in four moves.

* **Move to `Z`.** A closed immersion changes neither cohomology nor its dimension
  (`AlgebraicGeometry.finrank_cohomologyOverField_pushforward_of_isClosedImmersion`), so the
  count may be made on `Z` for the restricted module `i^*𝒪_Y((N+1)y)`.
* **`Z` is one point.** Its space is the support of `D`, which is the support of `ℐ_y`, which is
  `{y}`; a closed immersion is injective, so `Z` is a subsingleton. Every module on it then has
  support of dimension at most zero, which is what clauses (3), (4) and (5) of Tag 0AYT ask
  for.
* **The restricted module contributes no extra dimension.** It is invertible, hence finite
  locally free of rank one, so clause (5) at rank one together with clause (4) gives
  `dim_k H⁰(Z, i^*𝒪_Y((N+1)y)) = dim_k H⁰(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z)`.
* **Compute `Γ(Z, 𝒪_Z)`.** On a one-point space the germ map at that point is an isomorphism, so
  `Γ(Z, 𝒪_Z) ≅ 𝒪_{Z,z} ≅ 𝒪_{Y,y}/𝔪_y^{N+1}`, and the length of the latter over `𝒪_{Y,y}` is
  `N + 1`. Lengths multiply along the extension `k ⟶ 𝒪_{Y,y}`
  (`IsLocalRing.length_restrictScalars`) and the residue-field factor is at least one, so the
  `k`-dimension is at least `N + 1`. This is the source's count of `1, π, …, π^N`, carried out
  through `Module.length` rather than through an explicit basis.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_multiplePoint_ge`: the inequality above.
* `AlgebraicGeometry.MultiplePointLength.le_finrank_quotient_maximalIdeal_pow`: for a discrete
  valuation ring `R` that is a `k`-algebra, `n ≤ dim_k (R/𝔪^n)` whenever that quotient is a
  finite `k`-module.
* `AlgebraicGeometry.MultiplePointLength.finrank_cohomologyOverField_zero_eq_of_subsingleton`:
  on a one-point proper scheme a module that is finite locally free of rank one has the same
  `H⁰`-dimension as the structure sheaf.
* `AlgebraicGeometry.MultiplePointLength.globalSectionsStalkLinearEquiv`: on a one-point scheme
  over `k` the germ map identifies `Γ(Z, 𝒪_Z)` with `𝒪_{Z,z}`, `k`-linearly.
* `AlgebraicGeometry.MultiplePointLength.subschemeStalkQuotAlgEquiv`: the local ring of the
  subscheme cut out by an ideal sheaf is `𝒪_{Y,y}/D_y` as a `k`-algebra.

## Implementation notes

**The `k`-algebra structures are supplied inside the statements.** They are the ones the
structure morphism induces, `k ⟶ Γ(Spec k, 𝒪) ⟶ Γ(Z, 𝒪_Z) ⟶ 𝒪_{Z,z}`, so they depend on the
morphism and not only on the rings; they appear as `letI` in the statements, which is the
spelling of
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` and of
`AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk`, so no transport is needed
between them. That the map on local rings respects them is
`AlgebraicGeometry.MultiplePointLength.stalkMap_algebraMap_eq`, which is the naturality of
`AlgebraicGeometry.Scheme.Hom.stalkMap` read at `⊤`.

**The point of `Z` is named rather than chosen.**
`AlgebraicGeometry.IdealSheafData.subschemePoint` produces it from the membership
`y ∈ D.support`, and its image under `i` is `y` by definition; every stalk of `Y` that appears
is then literally the stalk at `y`, so the discrete-valuation hypothesis applies with no
transport along an equality of points.

**No attribute is attached.** Tag 0AYT has five clauses, and each is carried elsewhere: clause
(1) by `AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`, clauses (2), (3)
and (4) in `StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing`, clause
(5) by `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_rank_mul`. What is here is
the numerical consequence of those clauses at a multiple point of a curve, which is an input of
Tag 0A27 rather than a clause of either tag.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing
open Stacks.Divisors

universe u

namespace AlgebraicGeometry.MultiplePointLength

section Point

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsIntegral Y]
  {y : Y} (hy : IsClosed ({y} : Set Y))

omit [IsLocallyNoetherian Y] [IsIntegral Y] in
/-- **The subscheme cut out by a positive power of the ideal sheaf of a closed point sits at
that point.** The space of the subscheme is the support of the ideal sheaf, a positive power
does not move a support, and the support of the reduced structure on `{y}` is `{y}`. -/
theorem range_subschemeι_vanishingIdeal_pow (n : ℕ) (hn : 0 < n) :
    Set.range ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hy⟩ : Closeds Y) ^ n).subschemeι).base = ({y} : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  show ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n).supportSet) = _
  rw [Stacks.Divisors.supportSet_pow _ hn]
  exact supportSet_vanishingIdeal_singleton hy

omit [IsLocallyNoetherian Y] [IsIntegral Y] in
/-- **The subscheme cut out by `ℐ_y^n`, for `n ≥ 1`, has at most one point**: its image is the
single point `y`, and a closed immersion is injective. -/
theorem subsingleton_subscheme_vanishingIdeal_pow (n : ℕ) (hn : 0 < n) :
    Subsingleton
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n).subscheme) := by
  refine ⟨fun a b => ?_⟩
  have h := fun c => Set.mem_singleton_iff.mp
    ((Set.ext_iff.mp (range_subschemeι_vanishingIdeal_pow hy n hn) _).mp ⟨c, rfl⟩)
  exact (IsClosedImmersion.isClosedEmbedding
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n).subschemeι).injective
    ((h a).trans (h b).symm)

end Point

/-- **A space with at most one point has topological Krull dimension at most zero.** An empty
space has no irreducible closed subset at all, so its dimension is `⊥`; otherwise the whole
space is the only one. -/
theorem topologicalKrullDim_le_zero_of_subsingleton (Z : Type*) [TopologicalSpace Z]
    [Subsingleton Z] : topologicalKrullDim Z ≤ 0 := by
  rcases isEmpty_or_nonempty Z with h | h
  · have : IsEmpty (IrreducibleCloseds Z) := ⟨fun T => h.elim T.isIrreducible'.1.some⟩
    exact le_of_eq_of_le (Order.krullDim_eq_bot (α := IrreducibleCloseds Z)) bot_le
  · exact le_of_eq topologicalKrullDim_eq_zero_of_nonempty_subsingleton

section Chain

variable (k : Type u) [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))

/-- **On a one-point scheme proper over a field, a module that is finite locally free of rank
one has the same `H⁰`-dimension as the structure sheaf.** Every module on such a scheme has
support of dimension at most zero, so clause (5) of [Stacks, Tag 0AYT] at rank one gives
`χ(Z, 𝒪_Z ⊗ ℒ) = χ(Z, 𝒪_Z)`, tensoring by the structure sheaf leaves an Euler characteristic
unchanged, and clause (4) turns each Euler characteristic into the dimension of `H⁰`. -/
theorem finrank_cohomologyOverField_zero_eq_of_subsingleton [IsProper g] [Subsingleton Z]
    (L : Z.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    Module.finrank k (cohomologyOverField k g L 0) =
      Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have hLcoh : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree (X := Z) L
  have hucoh : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hdimL : topologicalKrullDim (_root_.SheafOfModules.supp L) ≤ 0 :=
    topologicalKrullDim_le_zero_of_subsingleton _
  have hdimu : topologicalKrullDim
      (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ 0 :=
    topologicalKrullDim_le_zero_of_subsingleton _
  obtain ⟨hT, hχ⟩ := exists_eulerCharacteristic_tensorSheaf_eq_rank_mul k g
    (SheafOfModules.unit Z.ringCatSheaf) hdimu L 1
  have hswap := eulerCharacteristic_unit_tensorSheaf k g L hLcoh hucoh
  have h1 : @eulerCharacteristic k _ Z g _ L hLcoh
      = @eulerCharacteristic k _ Z g _ (SheafOfModules.unit Z.ringCatSheaf) hucoh := by
    rw [← hswap]
    rw [show (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ L hucoh hLcoh) = hT from
      Subsingleton.elim _ _, hχ, Nat.cast_one, one_mul]
  rw [@eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k _ Z g _ L hLcoh
    hdimL] at h1
  rw [@eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k _ Z g _ _ hucoh
    hdimu] at h1
  exact_mod_cast h1

/-- **An open subset of a one-point space that contains the point is the whole space.** -/
theorem eq_top_of_mem_of_subsingleton [Subsingleton Z] (z : Z) (V : Z.Opens) (hz : z ∈ V) :
    V = ⊤ :=
  TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => by
    rw [Subsingleton.elim x z]; exact hz)

/-- **On a one-point scheme over `k` the germ map identifies the global functions with the local
ring at that point, `k`-linearly.** The whole space is the only open neighbourhood of the point,
so the colimit computing the stalk is attained at `⊤`; the germ map is a ring homomorphism, and
the `k`-algebra structure on the stalk is the one it transports. -/
def globalSectionsStalkLinearEquiv [Subsingleton Z] (z : Z) :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    letI : Algebra k (Z.presheaf.stalk z) :=
      ((Z.presheaf.germ ⊤ z trivial).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    Γ(Z, ⊤) ≃ₗ[k] Z.presheaf.stalk z :=
  letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  letI : Algebra k (Z.presheaf.stalk z) :=
    ((Z.presheaf.germ ⊤ z trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  haveI : IsIso (Z.presheaf.Γgerm z) :=
    TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top Z.presheaf z (eq_top_of_mem_of_subsingleton z)
  LinearEquiv.ofBijective
    { toFun := fun s => (Z.presheaf.germ ⊤ z trivial).hom s
      map_add' := fun s t => map_add _ s t
      map_smul' := fun c s => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rfl }
    (ConcreteCategory.bijective_of_isIso (Z.presheaf.Γgerm z))

end Chain

/-- **An invertible module on a scheme is finite locally free of rank one**, at the
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` spelling. The characterization
clause of [Stacks, Tag 0B8M] states its conclusion with
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank`; the two classes carry the same
field, so the passage between them rebuilds one structure from the other. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  ((Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry
      (X := X.toRingedSpace) L).mp h).exists_isFiniteLocallyFreeOfRankData.elim
    fun p hp => { exists_isFiniteLocallyFreeOfRankData := ⟨p, hp⟩ }

section Length

/-- **The `k`-dimension of `R/𝔪^n` for a discrete valuation ring `R` over `k` is at least `n`.**
The length of `R/𝔪^n` over `R` is `n`, lengths multiply along the extension `k ⟶ R`, and the
residue-field factor is at least one. This is the count the source performs with the elements
`1, π, …, π^{n-1}`, which form a `k`-linearly independent family in `R/𝔪^n`. -/
theorem le_finrank_quotient_maximalIdeal_pow (k : Type u) [Field k] (R : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] (n : ℕ)
    [Module.Finite k (R ⧸ maximalIdeal R ^ n)] :
    n ≤ Module.finrank k (R ⧸ maximalIdeal R ^ n) := by
  have : IsLocalHom (algebraMap k R) :=
    ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha
        exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have key := IsLocalRing.length_restrictScalars k R (R ⧸ maximalIdeal R ^ n)
  rw [Module.length_eq_finrank k (R ⧸ maximalIdeal R ^ n),
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R n] at key
  have h1 : (1 : ℕ∞) ≤ Module.length (ResidueField k) (ResidueField R) := by
    rcases eq_or_ne (Module.length (ResidueField k) (ResidueField R)) 0 with h | h
    · exact absurd (Module.length_eq_zero_iff.mp h) (not_subsingleton _)
    · exact Order.one_le_iff_ne_zero.mpr h
  have hle : ((n : ℕ∞)) ≤ (Module.finrank k (R ⧸ maximalIdeal R ^ n) : ℕ∞) := by
    rw [key]
    exact le_mul_of_one_le_right zero_le h1
  exact_mod_cast hle

end Length

section Quotient

variable (k : Type u) [Field k] {W : Scheme.{u}} (q : W ⟶ Spec (.of k))

/-- **The germ map and the map on local rings commute with the map on global functions**, at
`⊤`. This is the naturality of `AlgebraicGeometry.Scheme.Hom.stalkMap` read at the whole
space. -/
theorem germ_comp_stalkMap_subschemeι (D : W.IdealSheafData) (z : D.subscheme) :
    W.presheaf.germ ⊤ (D.subschemeι z) trivial ≫ D.subschemeι.stalkMap z
      = D.subschemeι.appTop ≫ D.subscheme.presheaf.germ ⊤ z trivial := by
  simpa using Scheme.Hom.germ_stalkMap D.subschemeι ⊤ z trivial

/-- **The map on local rings along a closed subscheme respects the `k`-algebra structures** the
two structure morphisms induce. The structure morphism of the subscheme is the closed immersion
followed by that of the ambient scheme, so both composites `k ⟶ 𝒪_{Z,z}` run through
`Γ(W, 𝒪_W)` and `𝒪_{W,w}`. -/
theorem stalkMap_algebraMap_eq (D : W.IdealSheafData) (z : D.subscheme) (a : k) :
    (D.subschemeι.stalkMap z).hom
        ((W.presheaf.germ ⊤ (D.subschemeι z) trivial).hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom a))
      = (D.subscheme.presheaf.germ ⊤ z trivial).hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom a) := by
  have hc : ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop) ≫
        (W.presheaf.germ ⊤ (D.subschemeι z) trivial ≫ D.subschemeι.stalkMap z)
      = ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop) ≫
        D.subscheme.presheaf.germ ⊤ z trivial := by
    rw [germ_comp_stalkMap_subschemeι, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hc) a

/-- **The local ring of the subscheme cut out by an ideal sheaf is the quotient of the local
ring of the ambient scheme by the stalk of that ideal sheaf, as a `k`-algebra.** The underlying
ring isomorphism is `AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`, which comes from
the surjectivity of the map on local rings together with the computation of its kernel; that it
respects the two `k`-algebra structures is
`AlgebraicGeometry.MultiplePointLength.stalkMap_algebraMap_eq`. -/
def subschemeStalkQuotAlgEquiv (D : W.IdealSheafData) (z : D.subscheme) :
    letI : Algebra k (W.presheaf.stalk (D.subschemeι z)) :=
      ((W.presheaf.germ ⊤ (D.subschemeι z) trivial).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom).toAlgebra
    letI : Algebra k (D.subscheme.presheaf.stalk z) :=
      ((D.subscheme.presheaf.germ ⊤ z trivial).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom).toAlgebra
    (W.presheaf.stalk (D.subschemeι z) ⧸ IdealSheafData.stalk D (D.subschemeι z))
      ≃ₐ[k] D.subscheme.presheaf.stalk z :=
  letI : Algebra k (W.presheaf.stalk (D.subschemeι z)) :=
    ((W.presheaf.germ ⊤ (D.subschemeι z) trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom).toAlgebra
  letI : Algebra k (D.subscheme.presheaf.stalk z) :=
    ((D.subscheme.presheaf.germ ⊤ z trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom).toAlgebra
  AlgEquiv.ofRingEquiv (f := IdealSheafData.subschemeStalkQuotEquiv D z) fun a => by
    rw [show (algebraMap k (W.presheaf.stalk (D.subschemeι z) ⧸
        IdealSheafData.stalk D (D.subschemeι z))) a
      = Ideal.Quotient.mk _ (algebraMap k (W.presheaf.stalk (D.subschemeι z)) a) from rfl,
      IdealSheafData.subschemeStalkQuotEquiv_mk]
    exact stalkMap_algebraMap_eq k q D z a

/-- **For a one-point closed subscheme of a scheme proper over `k`, the `H⁰`-dimension of the
restriction of `𝒪_W(D)` is the `k`-dimension of the local ring of the subscheme.** Three moves:
a closed immersion does not change cohomology, so the count passes to the subscheme; the
restriction of an invertible module is finite locally free of rank one, so on a one-point space
it has the `H⁰`-dimension of the structure sheaf; and degree-zero cohomology of the structure
sheaf is global functions, which on a one-point space is the local ring there. -/
theorem finrank_cohomologyOverField_pushforward_pullback_eq_finrank_stalk [IsProper q]
    (D : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Subsingleton D.subscheme] (z : D.subscheme) :
    letI : Algebra k (D.subscheme.presheaf.stalk z) :=
      ((D.subscheme.presheaf.germ ⊤ z trivial).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom).toAlgebra
    Module.finrank k (cohomologyOverField k q
        ((Scheme.Modules.pushforward D.subschemeι).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D))) 0)
      = Module.finrank k (D.subscheme.presheaf.stalk z) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (modulesInvertibleSheaf D) 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible _ inferInstance
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D)) 1 :=
    isFiniteLocallyFreeOfRank_pullback D.subschemeι (modulesInvertibleSheaf D) 1
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom.toAlgebra
  let : Algebra k (D.subscheme.presheaf.stalk z) :=
    ((D.subscheme.presheaf.germ ⊤ z trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom).toAlgebra
  have hΓ : Module.finrank k (cohomologyOverField k (D.subschemeι ≫ q)
      (SheafOfModules.unit D.subscheme.ringCatSheaf) 0) = Module.finrank k Γ(D.subscheme, ⊤) :=
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ q)
  rw [← finrank_cohomologyOverField_pushforward_of_isClosedImmersion k D.subschemeι q _ 0,
    finrank_cohomologyOverField_zero_eq_of_subsingleton k (D.subschemeι ≫ q) _, hΓ]
  exact (globalSectionsStalkLinearEquiv k (D.subschemeι ≫ q) z).finrank_eq

end Quotient

end AlgebraicGeometry.MultiplePointLength

namespace AlgebraicGeometry

open MultiplePointLength

variable (k : Type u) [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- **Clause (2) of [Stacks, Tag 0AYT] at a multiple point of a curve.** Let `Y` be a locally
Noetherian integral scheme proper over a field `k`, and let `y` be a closed point at which
`𝒪_{Y,y}` is a discrete valuation ring. Then

`N + 1 ≤ dim_k H⁰(Y, i_* i^* 𝒪_Y((N+1)y))`

for every `N`, where `i` is the closed immersion of the subscheme cut out by `ℐ_y^{N+1}`.

This is the inequality `hd'` of
`Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank` at `d = N + 1`: it is
what makes `𝒪_Y((N+1)y)` carry a global section that is not a section of `𝒪_Y` as soon as
`N + 1` exceeds `dim_k H¹(Y, 𝒪_Y)`, so it is the dimension count that the proof of
[Stacks, Tag 0A27] runs on.

The subscheme is a single point, so the module whose cohomology is counted has support of
dimension at most zero and its higher cohomology vanishes; the count is therefore the
`k`-dimension of a space of global functions, namely `𝒪_{Y,y}/𝔪_y^{N+1}`, whose length over
`𝒪_{Y,y}` is `N + 1`. -/
theorem finrank_cohomologyOverField_multiplePoint_ge
    [IsLocallyNoetherian Y] [IsIntegral Y] (hq : IsProper q) (_hc : IsCurve k q)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] (N : ℕ) :
    N + 1 ≤ Module.finrank k (cohomologyOverField k q
      ((Scheme.Modules.pushforward
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (N + 1)).subschemeι).obj
        ((Scheme.Modules.pullback
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨{y}, hy⟩ : Closeds Y) ^ (N + 1)).subschemeι).obj
          (modulesInvertibleSheaf
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (N + 1))))) 0) := by
  have : IsProper q := hq
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (N + 1) with hD
  have : Subsingleton D.subscheme :=
    subsingleton_subscheme_vanishingIdeal_pow hy (N + 1) N.succ_pos
  have hyD : y ∈ D.support := by
    rw [hD, Scheme.IdealSheafData.support_pow_succ,
      ← Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
      supportSet_vanishingIdeal_singleton hy]
    rfl
  let z : D.subscheme := IdealSheafData.subschemePoint _ y hyD
  let algΓ : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom.toAlgebra
  let algS : Algebra k (D.subscheme.presheaf.stalk z) :=
    ((D.subscheme.presheaf.germ ⊤ z trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ q).appTop).hom).toAlgebra
  let algR : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y trivial).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom).toAlgebra
  have hst : IdealSheafData.stalk D y = maximalIdeal (Y.presheaf.stalk y) ^ (N + 1) := by
    rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_vanishingIdeal_singleton y hy]
  have e : (Y.presheaf.stalk y ⧸ maximalIdeal (Y.presheaf.stalk y) ^ (N + 1)) ≃ₐ[k]
      D.subscheme.presheaf.stalk z :=
    (Ideal.quotientEquivAlgOfEq k hst).symm.trans (subschemeStalkQuotAlgEquiv k q D z)
  have : Module.Finite k Γ(D.subscheme, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k
      (D.subschemeι ≫ q)
  have : Module.Finite k (D.subscheme.presheaf.stalk z) :=
    Module.Finite.equiv (globalSectionsStalkLinearEquiv k (D.subschemeι ≫ q) z)
  have : Module.Finite k (Y.presheaf.stalk y ⧸ maximalIdeal (Y.presheaf.stalk y) ^ (N + 1)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  rw [finrank_cohomologyOverField_pushforward_pullback_eq_finrank_stalk k q D z,
    ← e.toLinearEquiv.finrank_eq]
  exact le_finrank_quotient_maximalIdeal_pow k (Y.presheaf.stalk y) (N + 1)

end AlgebraicGeometry

end
