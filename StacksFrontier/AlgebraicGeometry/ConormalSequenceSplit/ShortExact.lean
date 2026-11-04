module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeMiddleExact
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.RingTheory.Kaehler.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# A left inverse makes the conormal sequence split exact

For an immersion `i : Z ⟶ X` of schemes over `p : X ⟶ S`, [Stacks, Tag 0474] asserts that the
conormal sequence

```
0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
```

of [Stacks, Tag 01UZ] is split exact as soon as `i` has a left inverse over `S`, and that for a
section `s : S ⟶ X` of `X ⟶ S` the first arrow `𝒞_{S/X} ⟶ s^*Ω_{X/S}` is an isomorphism.

This file proves both, and also the source's parenthetical *(locally)*: under a local left
inverse the sequence is short exact globally and split short exact over an open neighbourhood of
every point, the splitting of its second arrow over such a neighbourhood being in
`StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.Basic`.

## Main results

* `Stacks.ConormalSequenceSplit.injective_kerCotangentToTensor_of_section`: the algebraic input,
  [Stacks, Tag 02HP] read as injectivity of `KaehlerDifferential.kerCotangentToTensor` for a
  tower `R ⟶ A ⟶ C` whose second map has an `R`-algebra section.
* `Stacks.ConormalSequenceSplit.exists_stalkMap_section_of_retraction`: a left inverse over the
  base gives, at every point of the source, a section of the stalk map compatible with the base.
* `Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_stalkSection` and
  `Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_retraction`: the first arrow
  `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` is a monomorphism, which is the `0 ⟶` at the left-hand end of the
  sequence.
* `Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_retraction`: the sequence is
  short exact.
* `Stacks.ConormalSequenceSplit.exists_stalkMap_section_liftCoborder`,
  `Stacks.ConormalSequenceSplit.exists_stalkMap_section_of_localRetraction` and
  `Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_localRetraction`: the same
  monomorphy from a left inverse of the restriction of `i` to opens, which is the source's
  *locally* has a left inverse.
* `Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_localRetraction`: the
  sequence is short exact under that local hypothesis too. This is the assertion labelled *the
  local clause*.
* `Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction`: the sequence is
  *split* short exact — a `CategoryTheory.ShortComplex.Splitting`, so both a retraction of the
  first arrow and a section of the second are produced. This is the assertion labelled *a left
  inverse splits the sequence*.
* `Stacks.ConormalSequenceSplit.conormalShortComplexRestrictSplitting_of_localRetraction` and
  `Stacks.ConormalSequenceSplit.forall_exists_nonempty_splitting_restrict_of_localRetraction`:
  under the *local* hypothesis the sequence restricted to a neighbourhood of any point carries a
  `CategoryTheory.ShortComplex.Splitting`, so it is **locally split exact**. This is the
  assertion labelled *the parenthetical local clause*.
* `Stacks.ConormalSequenceSplit.isIso_conormalDifferential_of_section`: for a section
  `s : S ⟶ X` of `p` the first arrow `𝒞_{S/X} ⟶ s^*Ω_{X/S}` is an isomorphism. This is the
  source's final assertion.

## Route

Exactness at the middle term and surjectivity on the right are already known for every
immersion, by `Stacks.ConormalSequenceRight.conormalShortComplex_exact` and
`Stacks.ConormalSequenceRight.epi_conormalShortComplex_g`, and splitness of the second arrow is
`Stacks.ConormalSequenceSplit.isSplitEpi_differentialsMapOver_of_retraction`. What the left
inverse is needed for is **injectivity of the first arrow**, and that is the content below.

Injectivity is checked on stalks, in the model of
`Stacks.ConormalSequenceRight.conormalShortComplex_shortExact_of_formallySmooth`: write
`W = i.coborderRange` for the coborder neighbourhood, `j = i.liftCoborder : Z ⟶ W` for the closed
factor and `q = ι ≫ p : W ⟶ S`, and at a point `z` of `Z` put `A = 𝒪_{W, j z}`, `C = 𝒪_{Z, z}`
and `R = 𝒪_{S, q (j z)}`, a tower `R ⟶ A ⟶ C` whose second map is surjective. Under the
identifications of `Stacks.ConormalSequenceRight.exists_conormalSheafStalkCotangentEquiv` and
`AlgebraicGeometry.Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv` the stalk of the
first arrow is `KaehlerDifferential.kerCotangentToTensor R A C`, both carrying the conormal class
of a local section `f` of the defining ideal sheaf to `1 ⊗ d f`.

That algebraic map is injective when `A ⟶ C` has an `R`-algebra section, which is
[Stacks, Tag 02HP] in the form
`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange_of_section`: a section of
`A ⟶ C` gives one of `A ⧸ J² ⟶ C`, which is the hypothesis that statement carries. The section
is where the left inverse enters: if `g : X ⟶ Z` is a left inverse of `i` over `S` then
`ι ≫ g : W ⟶ Z` is a left inverse of `j` over `S`, and the stalk map of a left inverse is a
section of the stalk map.

This is the only place the hypothesis of [Stacks, Tag 0474] is used; the source's own proof of
injectivity is the same one, [Stacks, Tag 02HP] in the affine case.

Under the *local* hypothesis the same section is produced at each point out of local data. A
left inverse `g : U ⟶ V` of the restriction `j : V ⟶ U` of `i` to opens `V ⊆ Z`, `U ⊆ X` gives
a section of `𝒪_{U, j v} ⟶ 𝒪_{V, v}` by the same argument, and the stalk maps of the open
immersions `V ↪ Z`, `U ↪ X` and `ι : W ↪ X` are isomorphisms and carry it to a section of
`𝒪_{W, j z} ⟶ 𝒪_{Z, z}`. Monomorphy being a condition on the stalks, the short exactness that
results is global.

## The local clause

[Stacks, Tag 0474] states its hypothesis and conclusion as *"(locally) has a left inverse"* and
*"(locally) split exact"*. Under the local hypothesis the sequence is proved **short exact**,
which is more than the source claims there, its second arrow is proved **split over a
neighbourhood of every point** by
`Stacks.ConormalSequenceSplit.forall_exists_isSplitEpi_restrict_of_localRetraction`, and the two
combine into a `CategoryTheory.ShortComplex.Splitting` of the sequence **restricted to such a
neighbourhood**. The combination needs the restriction of the sequence along an open immersion to
be known short exact, which is
`AlgebraicGeometry.Scheme.Modules.shortExact_map_restrictFunctor`: restriction along an open
immersion is a left adjoint and preserves finite limits, hence is exact.

Restriction is spelled `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` rather than
`AlgebraicGeometry.Scheme.Modules.pullback V.ι`, matching
`AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict`, the library's other local
splitting statement; the two functors are naturally isomorphic and the splitness of the second
arrow is carried between them by
`Stacks.ConormalSequenceSplit.isSplitEpi_differentialsMapOver_restrictFunctor_of_localRetraction`.

## References

* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP)
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.ConormalSequenceRight
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceSplit

/-! ### The algebraic input: Tag 02HP as injectivity -/

/-- **[Stacks, Tag 02HP] as injectivity of the conormal map.** Let `R ⟶ A ⟶ C` be a tower of
commutative rings and let `σ : C ⟶ A` be an `R`-algebra section of `A ⟶ C`. Then
`KaehlerDifferential.kerCotangentToTensor R A C : J/J² ⟶ C ⊗_A Ω[A⁄R]`, with
`J = ker (A ⟶ C)`, is injective.

A section of `A ⟶ C` composed with `A ⟶ A ⧸ J²` is a section of `A ⧸ J² ⟶ C`, which is the
hypothesis of `KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange_of_section`;
that statement decomposes the middle term of the conormal sequence so as to carry this map to
`LinearMap.inl`. -/
@[ega "0 20.6.22" "Injectivity of δ_{C/B/A}", ega "0 22.2.9" "special case"]
theorem injective_kerCotangentToTensor_of_section {R A C : Type*} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (σ : C →+* A) (hσR : σ.comp (algebraMap R C) = algebraMap R A)
    (hσ : (algebraMap A C).comp σ = RingHom.id C) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor R A C) := by
  let σₐ : C →ₐ[R] A := { σ with commutes' := fun r => RingHom.congr_fun hσR r }
  have hg : (IsScalarTower.toAlgHom R A C).kerSquareLift.comp
      ((Ideal.Quotient.mkₐ R (RingHom.ker (algebraMap A C) ^ 2)).comp σₐ) = AlgHom.id R C :=
    AlgHom.ext fun c => RingHom.congr_fun hσ c
  obtain ⟨e, he, -⟩ :=
    KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange_of_section _ hg
  intro x y hxy
  rw [he] at hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hxy
  simpa using congrArg Prod.fst (e.symm.injective hxy)

/-! ### Category arithmetic

The four computations below are the categorical skeletons of the stalk arguments that follow.
They are stated at an arbitrary category because at the stalks the objects are indexed by points
of a scheme written in several definitionally equal ways, and a rewrite inside such a goal is
rejected although the term is well typed; with the objects abstract there is nothing to rewrite
under. -/

private theorem comp_eq_id_of_section {C : Type*} [Category* C] {Zz Xz Ax Aw : C}
    (τ : Zz ⟶ Xz) (κ : Xz ≅ Ax) (ws : Ax ⟶ Aw) (js : Aw ⟶ Zz) (ii : Xz ⟶ Zz)
    (k : ws ≫ js = κ.inv ≫ ii) (hτ : τ ≫ ii = 𝟙 Zz) :
    (τ ≫ κ.hom ≫ ws) ≫ js = 𝟙 Zz := by
  rw [Category.assoc, Category.assoc, k, Iso.hom_inv_id_assoc]
  exact hτ

private theorem comp_section_eq {C : Type*} [Category* C] {A A' Zz Xz Ax Aw : C}
    (ν : A ≅ A') (u : A ⟶ Zz) (u' : A' ⟶ Zz) (τ : Zz ⟶ Xz) (κ : Xz ≅ Ax) (ws : Ax ⟶ Aw)
    (pz : A' ⟶ Xz) (pw : A ⟶ Ax) (qs : A ⟶ Aw) (e₁ : u = ν.hom ≫ u')
    (hτ : u' ≫ τ = pz) (e₂ : pz ≫ κ.hom = ν.inv ≫ pw) (hq : qs = pw ≫ ws) :
    u ≫ (τ ≫ κ.hom ≫ ws) = qs := by
  rw [e₁, hq, Category.assoc, ← Category.assoc u', hτ, ← Category.assoc pz, e₂, Category.assoc,
    Iso.hom_inv_id_assoc]

private theorem comp_eq_id_of_split {C : Type*} [Category* C] {Zz Cv Au Ax Xz : C}
    (α : Zz ⟶ Cv) [IsIso α] (σ : Cv ⟶ Au) (β : Ax ⟶ Au) [IsIso β] (κ : Ax ≅ Xz)
    (ii : Xz ⟶ Zz) (js : Au ⟶ Cv) (k : ii ≫ α = κ.inv ≫ β ≫ js) (hσ : σ ≫ js = 𝟙 Cv) :
    (α ≫ σ ≫ inv β ≫ κ.hom) ≫ ii = 𝟙 Zz := by
  rw [← cancel_mono α, Category.id_comp, Category.assoc, k]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, hσ, Category.comp_id]

private theorem split_tail_eq {C : Type*} [Category* C] {A A' Cv Au Ax Xz : C}
    (ν : A ≅ A') (u : A ⟶ Cv) (w : A' ⟶ Cv) (σ : Cv ⟶ Au) (β : Ax ⟶ Au) [IsIso β]
    (κ : Ax ≅ Xz) (pm : A ⟶ Ax) (pz : A' ⟶ Xz) (t : A ⟶ Au) (e₁ : u = ν.hom ≫ w)
    (hσ : u ≫ σ = t) (hc : t = pm ≫ β) (e₂ : pm ≫ κ.hom = ν.hom ≫ pz) :
    w ≫ σ ≫ inv β ≫ κ.hom = pz := by
  rw [← cancel_epi ν.hom, ← Category.assoc, ← e₁, ← Category.assoc, hσ, hc]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc, e₂]

/-! ### The geometric input: a left inverse gives a section on stalks -/

/-- **A left inverse over the base gives a section of the stalk map.** Let `j : Z ⟶ W` admit a
left inverse `gw : W ⟶ Z`, both over `S`: `j ≫ gw = 𝟙 Z` and `gw ≫ r = q`. Then at every point
`z` of `Z` the stalk map of `gw` is, up to the identification of the stalks at `gw (j z)` and
`z`, a section of `j`'s stalk map, and it is a map of algebras over the stalk of `𝒪_S`. -/
theorem exists_stalkMap_section_of_retraction {Z W S : Scheme.{u}} (j : Z ⟶ W) (gw : W ⟶ Z)
    (hj : j ≫ gw = 𝟙 Z) (r : Z ⟶ S) (q : W ⟶ S) (hq : gw ≫ r = q) (z : Z) :
    ∃ σ : Z.presheaf.stalk z ⟶ W.presheaf.stalk (j.base z),
      σ ≫ j.stalkMap z = 𝟙 _ ∧ (j ≫ q).stalkMap z ≫ σ = q.stalkMap (j.base z) := by
  subst hq
  have hbase : gw.base (j.base z) = z := congrArg (fun f : Z ⟶ Z => f.base z) hj
  have hS : r.base (gw.base (j.base z)) = r.base z := congrArg r.base hbase
  refine ⟨(Z.presheaf.stalkCongr (Inseparable.of_eq hbase.symm)).hom ≫
    gw.stalkMap (j.base z), ?_, ?_⟩
  · have k : gw.stalkMap (j.base z) ≫ j.stalkMap z =
        (Z.presheaf.stalkCongr (Inseparable.of_eq hbase.symm)).inv ≫ 𝟙 _ := by
      rw [← Scheme.Hom.stalkMap_comp j gw z]
      exact (Iso.eq_inv_comp _).2
        ((Scheme.Hom.stalkMap_congr_hom (𝟙 Z) (j ≫ gw) hj.symm z).symm.trans
          (Scheme.Hom.stalkMap_id Z z))
    simpa using comp_eq_id_of_section (𝟙 _) (Z.presheaf.stalkCongr (Inseparable.of_eq hbase.symm))
      (gw.stalkMap (j.base z)) (j.stalkMap z) (𝟙 _) k (Category.id_comp _)
  · have h₁ : j ≫ gw ≫ r = r := by rw [← Category.assoc, hj, Category.id_comp]
    simpa using comp_section_eq (S.presheaf.stalkCongr (Inseparable.of_eq hS))
      ((j ≫ gw ≫ r).stalkMap z) (r.stalkMap z) (𝟙 _)
      (Z.presheaf.stalkCongr (Inseparable.of_eq hbase.symm)) (gw.stalkMap (j.base z))
      (r.stalkMap z) (r.stalkMap (gw.base (j.base z))) _
      (Scheme.Hom.stalkMap_congr_hom (j ≫ gw ≫ r) r h₁ z) (Category.comp_id _)
      (Scheme.Hom.stalkMap_congr_point r z (gw.base (j.base z)) hbase.symm)
      (Scheme.Hom.stalkMap_comp gw r (j.base z))

/-! ### Injectivity of the first arrow -/

/-- **The first arrow of the conormal sequence is a monomorphism when the closed factor has a
section on every stalk.** For an immersion `i : Z ⟶ X` over `p : X ⟶ S`, write
`W = i.coborderRange`, `j = i.liftCoborder` and `q = ι ≫ p`; the hypothesis is that at every
point `z` of `Z` the surjection `𝒪_{W, j z} ⟶ 𝒪_{Z, z}` admits a section over `𝒪_{S, q (j z)}`.

A morphism of sheaves of modules injective on every stalk is a monomorphism, and the stalk of
the first arrow is `KaehlerDifferential.kerCotangentToTensor`, injective by
`Stacks.ConormalSequenceSplit.injective_kerCotangentToTensor_of_section`. -/
theorem mono_conormalDifferential_of_stalkSection {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S)
    (hsec : ∀ z : Z, ∃ σ : Z.presheaf.stalk z ⟶
        (i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z),
      σ ≫ i.liftCoborder.stalkMap z = 𝟙 _ ∧
        (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)).stalkMap z ≫ σ =
          (i.coborderRange.ι ≫ p).stalkMap (i.liftCoborder.base z)) :
    Mono (conormalDifferential i p) := by
  classical
  set q : i.coborderRange.toScheme ⟶ S := i.coborderRange.ι ≫ p with hqdef
  have key : ∀ z : Z, Function.Injective ((stalkAb Z z).map (conormalDifferential i p)) := by
    intro z
    -- the tower of local rings at `z`
    let A : Type u :=
      ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))
    let C : Type u := ToType (Z.presheaf.stalk z)
    let R : Type u := ToType (S.presheaf.stalk (q.base (i.liftCoborder.base z)))
    let : Algebra R A := algebraStalkMap q (i.liftCoborder.base z)
    let : Algebra A C := (i.liftCoborder.stalkMap z).hom.toAlgebra
    let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ q) z
    let : IsScalarTower R A C := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder q z
    -- the algebraic input: `kerCotangentToTensor` is injective
    obtain ⟨σ, hσ, hσR⟩ := hsec z
    have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor R A C) :=
      injective_kerCotangentToTensor_of_section σ.hom
        (CommRingCat.hom_ext_iff.mp hσR) (CommRingCat.hom_ext_iff.mp hσ)
    -- the identifications of the three stalks
    obtain ⟨eL, heL⟩ := exists_conormalSheafStalkCotangentEquiv i z
    obtain ⟨eM, heMgerm, -⟩ :=
      Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv i.liftCoborder q z
    have hψ : Function.Bijective
        ((stalkAb Z z).map (coborderPullbackDifferentialsIso i p).hom) :=
      ConcreteCategory.bijective_of_isIso
        ((stalkAb Z z).mapIso (coborderPullbackDifferentialsIso i p)).hom
    -- the first arrow on the conormal class of a section of the ideal sheaf
    have hcgerm : ∀ (V : Opens i.coborderRange.toScheme)
        (hz : i.liftCoborder.base z ∈ V)
        (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
        (stalkAb Z z).map (conormalDifferential i p)
            (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
            (i.liftCoborder ⁻¹ᵁ V) z hz
            (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
              ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
          (stalkAb Z z).map (coborderPullbackDifferentialsIso i p).hom
            (TopCat.Presheaf.germ (C := Ab.{u})
            ((Scheme.Modules.pullback i.liftCoborder).obj
              (Scheme.Hom.relativeDifferentials q)).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hz
            (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials q)).val.app (op V)
              ((Scheme.Hom.universalRelativeDerivation q).d s.1))) := by
      intro V hz s
      refine Eq.trans (stalkAb_map_germ (conormalDifferential i p) z
        (i.liftCoborder ⁻¹ᵁ V) hz _) ?_
      refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hz)
        (congrArg (fun m => (m.val.app (op V)).hom s)
          (conormalComparison_comp_conormalDifferential i p))) ?_
      exact (stalkAb_map_germ (coborderPullbackDifferentialsIso i p).hom z
        (i.liftCoborder ⁻¹ᵁ V) hz _).symm
    intro x₁ x₂ hx
    obtain ⟨V₁, hz₁, s₁, rfl⟩ := exists_germ_unit_eq i z x₁
    obtain ⟨V₂, hz₂, s₂, rfl⟩ := exists_germ_unit_eq i z x₂
    have hx' := (hcgerm V₁ hz₁ s₁).symm.trans (hx.trans (hcgerm V₂ hz₂ s₂))
    have h2 := congrArg eM (hψ.1 hx')
    refine eL.injective (Eq.trans (heL V₁ hz₁ s₁) (Eq.trans (hinj ?_) (heL V₂ hz₂ s₂).symm))
    refine Eq.trans (KaehlerDifferential.kerCotangentToTensor_toCotangent R A C _)
      (Eq.trans ?_ (KaehlerDifferential.kerCotangentToTensor_toCotangent R A C _).symm)
    exact (heMgerm V₁ hz₁ s₁.1).symm.trans (h2.trans (heMgerm V₂ hz₂ s₂.1))
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 fun z =>
      (AddCommGrpCat.mono_iff_injective _).2 (key z))

/-- **A left inverse makes the first arrow of the conormal sequence a monomorphism.** If
`g : X ⟶ Z` is a left inverse of the immersion `i : Z ⟶ X` over `S`, then
`𝒞_{Z/X} ⟶ i^*Ω_{X/S}` is a monomorphism.

The left inverse of `i` restricts to a left inverse `ι ≫ g` of the closed factor
`j = i.liftCoborder` into the coborder neighbourhood, whose stalk maps are the sections the
previous statement asks for. -/
theorem mono_conormalDifferential_of_retraction {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgS : g ≫ (i ≫ p) = p) :
    Mono (conormalDifferential i p) := by
  refine mono_conormalDifferential_of_stalkSection i p fun z => ?_
  have hj : i.liftCoborder ≫ (i.coborderRange.ι ≫ g) = 𝟙 Z := by
    rw [← Category.assoc, i.liftCoborder_ι, hg]
  have hq : (i.coborderRange.ι ≫ g) ≫ (i ≫ p) = i.coborderRange.ι ≫ p := by
    rw [Category.assoc, hgS]
  exact exists_stalkMap_section_of_retraction i.liftCoborder (i.coborderRange.ι ≫ g) hj
    (i ≫ p) (i.coborderRange.ι ≫ p) hq z

/-! ### From a section on the stalks of `i` to one on the stalks of the closed factor -/

/-- **A section of the stalk map of an immersion gives one for its closed factor.** For an
immersion `i : Z ⟶ X` over `p : X ⟶ S`, write `W = i.coborderRange` and `j = i.liftCoborder`,
so that `j ≫ ι = i`. A section of `𝒪_{X, i z} ⟶ 𝒪_{Z, z}` over `𝒪_S` gives a section of
`𝒪_{W, j z} ⟶ 𝒪_{Z, z}` over `𝒪_S`, by composing with the stalk map of the open immersion `ι`.

This is the form the hypothesis of
`Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_stalkSection` is stated in. -/
theorem exists_stalkMap_section_liftCoborder {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (z : Z) (τ : Z.presheaf.stalk z ⟶ X.presheaf.stalk (i.base z))
    (hτ : τ ≫ i.stalkMap z = 𝟙 _) (hτS : (i ≫ p).stalkMap z ≫ τ = p.stalkMap (i.base z)) :
    ∃ σ : Z.presheaf.stalk z ⟶
        (i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z),
      σ ≫ i.liftCoborder.stalkMap z = 𝟙 _ ∧
        (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)).stalkMap z ≫ σ =
          (i.coborderRange.ι ≫ p).stalkMap (i.liftCoborder.base z) := by
  have hW : i.coborderRange.ι.base (i.liftCoborder.base z) = i.base z :=
    congrArg (fun f : Z ⟶ X => f.base z) i.liftCoborder_ι
  have hS : p.base (i.coborderRange.ι.base (i.liftCoborder.base z)) = p.base (i.base z) :=
    congrArg p.base hW
  have k₁ : i.coborderRange.ι.stalkMap (i.liftCoborder.base z) ≫ i.liftCoborder.stalkMap z =
      (X.presheaf.stalkCongr (Inseparable.of_eq hW.symm)).inv ≫ i.stalkMap z :=
    (Scheme.Hom.stalkMap_comp i.liftCoborder i.coborderRange.ι z).symm.trans
      (Scheme.Hom.stalkMap_congr_hom (i.liftCoborder ≫ i.coborderRange.ι) i
        i.liftCoborder_ι z)
  refine ⟨τ ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hW.symm)).hom ≫
    i.coborderRange.ι.stalkMap (i.liftCoborder.base z), ?_, ?_⟩
  · exact comp_eq_id_of_section τ (X.presheaf.stalkCongr (Inseparable.of_eq hW.symm))
      (i.coborderRange.ι.stalkMap (i.liftCoborder.base z)) (i.liftCoborder.stalkMap z)
      (i.stalkMap z) k₁ hτ
  · have hpq : i.liftCoborder ≫ (i.coborderRange.ι ≫ p) = i ≫ p := by
      rw [← Category.assoc, i.liftCoborder_ι]
    have e₁ : (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)).stalkMap z =
        (S.presheaf.stalkCongr (Inseparable.of_eq hS)).hom ≫ (i ≫ p).stalkMap z :=
      Scheme.Hom.stalkMap_congr_hom (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) (i ≫ p) hpq z
    have e₂ : p.stalkMap (i.base z) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hW.symm)).hom =
        (S.presheaf.stalkCongr (Inseparable.of_eq hS)).inv ≫
          p.stalkMap (i.coborderRange.ι.base (i.liftCoborder.base z)) :=
      Scheme.Hom.stalkMap_congr_point p (i.base z)
        (i.coborderRange.ι.base (i.liftCoborder.base z)) hW.symm
    exact comp_section_eq (S.presheaf.stalkCongr (Inseparable.of_eq hS)) _
      ((i ≫ p).stalkMap z) τ (X.presheaf.stalkCongr (Inseparable.of_eq hW.symm))
      (i.coborderRange.ι.stalkMap (i.liftCoborder.base z))
      (p.stalkMap (i.base z))
      (p.stalkMap (i.coborderRange.ι.base (i.liftCoborder.base z))) _ e₁ hτS e₂
      (Scheme.Hom.stalkMap_comp i.coborderRange.ι p (i.liftCoborder.base z))

/-! ### The local clause: a left inverse over opens -/

/-- **A left inverse of `i` over opens gives a section of the stalk map of `i` at every point of
the chosen open.** Let `V` be an open of `Z` and `U` an open of `X` through which `i` restricted
to `V` factors as `j : V ⟶ U`, and let `g : U ⟶ V` be a left inverse of `j` over `S`. Then at
every point `z` of `V` the surjection `𝒪_{X, i z} ⟶ 𝒪_{Z, z}` has a section over `𝒪_S`.

The section of `𝒪_{U, j v} ⟶ 𝒪_{V, v}` is
`Stacks.ConormalSequenceSplit.exists_stalkMap_section_of_retraction` applied to `j` and `g`; the
stalk maps of the open immersions `V ↪ Z` and `U ↪ X` are isomorphisms, and transport it. -/
theorem exists_stalkMap_section_of_localRetraction {Z X S : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ S)
    (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme) (hfac : V.ι ≫ i = j ≫ U.ι)
    (g : U.toScheme ⟶ V.toScheme) (hg : j ≫ g = 𝟙 V.toScheme)
    (hgS : g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) (v : V.toScheme) :
    ∃ τ : Z.presheaf.stalk (V.ι.base v) ⟶ X.presheaf.stalk (i.base (V.ι.base v)),
      τ ≫ i.stalkMap (V.ι.base v) = 𝟙 _ ∧
        (i ≫ p).stalkMap (V.ι.base v) ≫ τ = p.stalkMap (i.base (V.ι.base v)) := by
  obtain ⟨σ, hσ, hσS⟩ := exists_stalkMap_section_of_retraction j g hg (V.ι ≫ i ≫ p)
    (U.ι ≫ p) hgS v
  have hX : U.ι.base (j.base v) = i.base (V.ι.base v) :=
    (congrArg (fun f : V.toScheme ⟶ X => f.base v) hfac).symm
  have hS : p.base (U.ι.base (j.base v)) = p.base (i.base (V.ι.base v)) := congrArg p.base hX
  have k₁ : i.stalkMap (V.ι.base v) ≫ V.ι.stalkMap v =
      (X.presheaf.stalkCongr (Inseparable.of_eq hX)).inv ≫
        U.ι.stalkMap (j.base v) ≫ j.stalkMap v := by
    refine ((Scheme.Hom.stalkMap_comp V.ι i v).symm.trans
      (Scheme.Hom.stalkMap_congr_hom (V.ι ≫ i) (j ≫ U.ι) hfac v)).trans ?_
    exact congrArg (fun m => (X.presheaf.stalkCongr (Inseparable.of_eq hX)).inv ≫ m)
      (Scheme.Hom.stalkMap_comp j U.ι v)
  refine ⟨V.ι.stalkMap v ≫ σ ≫ inv (U.ι.stalkMap (j.base v)) ≫
    (X.presheaf.stalkCongr (Inseparable.of_eq hX)).hom, ?_, ?_⟩
  · exact comp_eq_id_of_split (V.ι.stalkMap v) σ (U.ι.stalkMap (j.base v))
      (X.presheaf.stalkCongr (Inseparable.of_eq hX)) (i.stalkMap (V.ι.base v))
      (j.stalkMap v) k₁ hσ
  · have hju : j ≫ (U.ι ≫ p) = V.ι ≫ i ≫ p := by
      rw [← Category.assoc, ← hfac, Category.assoc]
    have e₁ : (j ≫ (U.ι ≫ p)).stalkMap v =
        (S.presheaf.stalkCongr (Inseparable.of_eq hS)).hom ≫ (V.ι ≫ i ≫ p).stalkMap v :=
      Scheme.Hom.stalkMap_congr_hom (j ≫ (U.ι ≫ p)) (V.ι ≫ i ≫ p) hju v
    have e₂ : p.stalkMap (U.ι.base (j.base v)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hX)).hom =
        (S.presheaf.stalkCongr (Inseparable.of_eq hS)).hom ≫
          p.stalkMap (i.base (V.ι.base v)) :=
      Scheme.Hom.stalkMap_congr_point p (U.ι.base (j.base v)) (i.base (V.ι.base v)) hX
    have A : (i ≫ p).stalkMap (V.ι.base v) ≫ V.ι.stalkMap v = (V.ι ≫ i ≫ p).stalkMap v :=
      (Scheme.Hom.stalkMap_comp V.ι (i ≫ p) v).symm
    have B : (V.ι ≫ i ≫ p).stalkMap v ≫ (σ ≫ inv (U.ι.stalkMap (j.base v)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hX)).hom) =
        p.stalkMap (i.base (V.ι.base v)) :=
      split_tail_eq (S.presheaf.stalkCongr (Inseparable.of_eq hS))
        ((j ≫ (U.ι ≫ p)).stalkMap v) _ σ (U.ι.stalkMap (j.base v))
        (X.presheaf.stalkCongr (Inseparable.of_eq hX))
        (p.stalkMap (U.ι.base (j.base v))) (p.stalkMap (i.base (V.ι.base v))) _ e₁ hσS
        (Scheme.Hom.stalkMap_comp U.ι p (j.base v)) e₂
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ (σ ≫ inv (U.ι.stalkMap (j.base v)) ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hX)).hom)) A).trans B)

/-- **A local left inverse makes the first arrow of the conormal sequence a monomorphism.** Let
`i : Z ⟶ X` be an immersion of schemes over `S` which *locally has a left inverse*: every point
`z` of `Z` has an open neighbourhood `V` which `i` maps into an open `U` of `X`, the restricted
morphism `j : V ⟶ U` admitting a left inverse `g : U ⟶ V` over `S`. Then
`𝒞_{Z/X} ⟶ i^*Ω_{X/S}` is a monomorphism.

Being a monomorphism is checked on stalks, and at a point of `Z` only a left inverse near that
point is needed. -/
theorem mono_conormalDifferential_of_localRetraction {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S)
    (hloc : ∀ z : Z, ∃ (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme)
      (g : U.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ U.ι ∧ j ≫ g = 𝟙 V.toScheme ∧
        g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    Mono (conormalDifferential i p) := by
  refine mono_conormalDifferential_of_stalkSection i p fun z => ?_
  obtain ⟨V, U, j, g, hzV, hfac, hg, hgS⟩ := hloc z
  obtain ⟨τ, hτ, hτS⟩ :=
    exists_stalkMap_section_of_localRetraction i p V U j hfac g hg hgS (⟨z, hzV⟩ : V.toScheme)
  exact exists_stalkMap_section_liftCoborder i p z τ hτ hτS

/-! ### Split exactness -/

/-- **[Stacks, Tag 0474], short exactness under a left inverse.** For an immersion `i : Z ⟶ X`
of schemes over `p : X ⟶ S` admitting a left inverse `g : X ⟶ Z` over `S`, the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is short exact.

Exactness at the middle term and surjectivity on the right hold for every immersion; the left
inverse supplies injectivity of the first arrow. -/
theorem conormalShortComplex_shortExact_of_retraction {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgS : g ≫ (i ≫ p) = p) :
    (conormalShortComplex i p).ShortExact :=
  ShortComplex.ShortExact.mk' (conormalShortComplex_exact i p)
    (mono_conormalDifferential_of_retraction i p g hg hgS) (epi_conormalShortComplex_g i p)

/-- **[Stacks, Tag 0474], short exactness under a *local* left inverse.** Let `i : Z ⟶ X` be an
immersion of schemes over `p : X ⟶ S` which *locally has a left inverse*: every point `z` of `Z`
has an open neighbourhood `V` which `i` maps into an open `U` of `X`, the restricted morphism
`j : V ⟶ U` admitting a left inverse `g : U ⟶ V` over `S`. Then the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is short exact.

This is the exactness half of the source's *locally split exact* under the source's local
hypothesis, and it is global: being a monomorphism is a stalkwise condition, so a left inverse
near each point is enough. The splitting half under the same hypothesis is
`Stacks.ConormalSequenceSplit.forall_exists_isSplitEpi_restrict_of_localRetraction`, which
splits the second arrow over a neighbourhood of every point; the two combine into the local
split exactness
`Stacks.ConormalSequenceSplit.forall_exists_nonempty_splitting_restrict_of_localRetraction`. -/
@[stacks 0474 "the local clause: under a local left inverse — every point of Z has a
neighbourhood V mapping into an open U of X with the restricted morphism admitting a left
inverse over S — the sequence 0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0 of Tag 01UZ is short
exact. This is exactness, globally; the local splitting under the same hypothesis is
forall_exists_nonempty_splitting_restrict_of_localRetraction"]
theorem conormalShortComplex_shortExact_of_localRetraction {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S)
    (hloc : ∀ z : Z, ∃ (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme)
      (g : U.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ U.ι ∧ j ≫ g = 𝟙 V.toScheme ∧
        g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    (conormalShortComplex i p).ShortExact :=
  ShortComplex.ShortExact.mk' (conormalShortComplex_exact i p)
    (mono_conormalDifferential_of_localRetraction i p hloc) (epi_conormalShortComplex_g i p)

/-- **[Stacks, Tag 0474], a left inverse splits the sequence.** For an immersion `i : Z ⟶ X` of
schemes over `p : X ⟶ S` admitting a left inverse `g : X ⟶ Z` over `S`, the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is *split* short exact: a
splitting is produced, consisting of a retraction of the first arrow and a section of the second
whose composites add up to the identity of `i^*Ω_{X/S}`.

The section of the second arrow is the source's `i^*c_g`, through
`Stacks.ConormalSequenceSplit.isSplitEpi_differentialsMapOver_of_retraction`; the sequence is
short exact by `Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_retraction`, and
a short exact sequence whose epimorphism has a section is split. -/
@[stacks 0474 "a left inverse over S splits the sequence 0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
of Tag 01UZ: a splitting is produced, so in particular the sequence is short exact. The
hypothesis is a global left inverse g : X ⟶ Z with i ≫ g = 𝟙 Z and g ≫ (i ≫ p) = p; the
source's parenthetical local clause is
forall_exists_nonempty_splitting_restrict_of_localRetraction"]
noncomputable def conormalShortComplexSplitting_of_retraction {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgS : g ≫ (i ≫ p) = p) :
    (conormalShortComplex i p).Splitting :=
  haveI hse := conormalShortComplex_shortExact_of_retraction i p g hg hgS
  haveI : IsSplitEpi (conormalShortComplex i p).g :=
    isSplitEpi_differentialsMapOver_of_retraction i p g hg hgS
  ShortComplex.Splitting.ofExactOfSection _ hse.exact
    (CategoryTheory.section_ (conormalShortComplex i p).g) (IsSplitEpi.id _) hse.mono_f

/-- **A local left inverse splits the conormal sequence over the open it lives on.** The data are
those of
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction`
— an open `V` of `Z` and an open `U` of `X` through which `i` restricted to `V` factors as
`j : V ⟶ U`, together with a left inverse `g : U ⟶ V` of `j` over `S` — plus the source's local
hypothesis `hloc`, which is what makes the first arrow a monomorphism. The conormal sequence of
`i` restricted to `V` is then split short exact.

Restriction along the open immersion `V.ι` is exact, so the restricted sequence is short exact by
`AlgebraicGeometry.Scheme.Modules.shortExact_map_restrictFunctor`; the left inverse on `U` splits
its second arrow by
`Stacks.ConormalSequenceSplit.isSplitEpi_differentialsMapOver_restrictFunctor_of_localRetraction`;
and a short exact sequence whose epimorphism has a section is split. -/
noncomputable def conormalShortComplexRestrictSplitting_of_localRetraction
    {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)
    (hloc : ∀ z : Z, ∃ (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme)
      (g : U.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ U.ι ∧ j ≫ g = 𝟙 V.toScheme ∧
        g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p)
    (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme) (hfac : V.ι ≫ i = j ≫ U.ι)
    (g : U.toScheme ⟶ V.toScheme) (hg : j ≫ g = 𝟙 V.toScheme)
    (hgS : g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    ((conormalShortComplex i p).map (Scheme.Modules.restrictFunctor V.ι)).Splitting :=
  haveI hse := Scheme.Modules.shortExact_map_restrictFunctor V.ι (conormalShortComplex i p)
    (conormalShortComplex_shortExact_of_localRetraction i p hloc)
  haveI : IsSplitEpi ((conormalShortComplex i p).map
      (Scheme.Modules.restrictFunctor V.ι)).g :=
    isSplitEpi_differentialsMapOver_restrictFunctor_of_localRetraction i p V U j hfac g hg hgS
  ShortComplex.Splitting.ofExactOfSection _ hse.exact
    (CategoryTheory.section_ ((conormalShortComplex i p).map
      (Scheme.Modules.restrictFunctor V.ι)).g) (IsSplitEpi.id _) hse.mono_f

/-- **[Stacks, Tag 0474], a local left inverse makes the conormal sequence locally split
exact.** Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S` which *locally has a left
inverse*: every point `z` of `Z` has an open neighbourhood `V` which `i` maps into an open `U` of
`X`, the restricted morphism `j : V ⟶ U` admitting a left inverse `g : U ⟶ V` over `S`. Then
every point of `Z` has an open neighbourhood `V` over which the conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is *split* short exact: the
sequence restricted to `V` carries a `CategoryTheory.ShortComplex.Splitting`.

This is the source's *(locally) split exact* under the source's *(locally) has a left inverse*.
The neighbourhood produced is the one the hypothesis supplies, and the splitting over it is
`Stacks.ConormalSequenceSplit.conormalShortComplexRestrictSplitting_of_localRetraction`. -/
@[stacks 0474 "the parenthetical local clause: under a local left inverse — every point of Z has
a neighbourhood V mapping into an open U of X with the restricted morphism j : V ⟶ U admitting a
left inverse over S — the sequence 0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0 of Tag 01UZ is
*locally split exact*: every point of Z has an open neighbourhood V over which the restricted
sequence carries a ShortComplex.Splitting, so both a retraction of the first arrow and a section
of the second are produced over V. This is the full (locally) reading of the source's hypothesis
and conclusion; the global reading is conormalShortComplexSplitting_of_retraction",
  ega "IV 16.4.21" "special case"]
theorem forall_exists_nonempty_splitting_restrict_of_localRetraction
    {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)
    (hloc : ∀ z : Z, ∃ (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme)
      (g : U.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ U.ι ∧ j ≫ g = 𝟙 V.toScheme ∧
        g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
      Nonempty (((conormalShortComplex i p).map
        (Scheme.Modules.restrictFunctor V.ι)).Splitting) := by
  intro z
  obtain ⟨V, U, j, g, hzV, hfac, hg, hgS⟩ := hloc z
  exact ⟨V, hzV,
    ⟨conormalShortComplexRestrictSplitting_of_localRetraction i p hloc V U j hfac g hg hgS⟩⟩

/-- **[Stacks, Tag 0474], the conormal sheaf of a section.** For a section `s : S ⟶ X` of
`p : X ⟶ S` the first arrow `𝒞_{S/X} ⟶ s^*Ω_{X/S}` of the conormal sequence of
[Stacks, Tag 01UZ] is an isomorphism.

A section is an immersion whose left inverse over `S` is `p` itself, so the sequence of `s` is
short exact; and `Ω_{S/S}` is a zero object by [Stacks, Tag 01UY], `s ≫ p = 𝟙 S` being a
monomorphism. The first arrow is therefore both a monomorphism and, the sequence being exact at
the middle term with zero on the right, an epimorphism. -/
@[stacks 0474 "the source's final assertion: for a section s of p, the first arrow
𝒞_{S/X} ⟶ s^*Ω_{X/S} of the sequence of Tag 01UZ, which is induced by d_{X/S}, is an
isomorphism", sga "6 VIII 2.2" "(b)"]
theorem isIso_conormalDifferential_of_section {X S : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X)
    (hs : s ≫ p = 𝟙 S) :
    haveI := isImmersion_of_section p s hs
    IsIso (conormalDifferential s p) := by
  have := isImmersion_of_section p s hs
  have hse := conormalShortComplex_shortExact_of_retraction s p p hs
    (by rw [hs, Category.comp_id])
  have : Mono (s ≫ p) := by rw [hs]; infer_instance
  have hz : Limits.IsZero (Scheme.Hom.relativeDifferentials (s ≫ p)) :=
    Scheme.Hom.isZero_relativeDifferentials_of_mono (s ≫ p)
  have : Epi (conormalDifferential s p) :=
    (ShortComplex.exact_iff_epi _ (hz.eq_zero_of_tgt _)).mp (conormalShortComplex_exact s p)
  have : Mono (conormalDifferential s p) := hse.mono_f
  exact isIso_of_mono_of_epi _

end Stacks.ConormalSequenceSplit

end
