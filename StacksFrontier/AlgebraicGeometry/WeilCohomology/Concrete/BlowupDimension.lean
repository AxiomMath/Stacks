module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Blowup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula

/-!
# Dimensions of the blowup of a smooth projective scheme in a smooth centre

Let `X` be a smooth projective scheme over a field `k`, equidimensional of dimension `n`, and let
`i : Z ⟶ X` be a closed immersion of smooth projective schemes. Let `b : X' ⟶ X` be the blowing
up in `Z` with exceptional divisor `j : E ⟶ X'` and `π : E ⟶ Z`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.blowupObj` and its siblings). Then

* `X'` is equidimensional of dimension `n`: the exceptional divisor is an effective Cartier
  divisor (Tag 02OS (2)), so its complement is dense, and `b` is an isomorphism over `X \ Z`
  (Tag 02OS (1)), so every part of `X'` of constant dimension meets an open subscheme of `X`;
* `E` is equidimensional of dimension `n - 1`: the generic points of the components of an
  effective Cartier divisor have ambient local ring of dimension one (Tag 0BCN), and the dimension
  formula of Tag 0A21 on `X'` reads off the dimension of each component of `E`;
* `π` has relative dimension `n - 1 - e` when `Z` is equidimensional of dimension `e`, by the
  dimension formula of Tag 0AFF for the smooth morphism `π`;
* if every irreducible component of `Z` has codimension `r` in `X` (Lemma 0FIH's hypothesis),
  then `Z` is equidimensional of dimension `n - r`, again by Tag 0A21 on `X`.

The dimension statements are `AlgebraicGeometry.RelativeDimension` of the structure morphisms
over `Spec k`, the predicate of `Stacks.WeilCohomology.IsNonemptyEquidimensional`.

## Main results

* `Stacks.WeilCohomology.relativeDimension_iff_forall_topologicalKrullDimAt_of_field`: over a
  field, relative dimension `d` is local dimension `d` at every point.
* `Stacks.WeilCohomology.relativeDimension_of_ringKrullDim_stalk_eq`: a closed subscheme of a
  scheme of dimension `n` whose components all have codimension `c` has dimension `n - c`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDimension_blowupObj`,
  `isNonemptyEquidimensional_blowupObj`: `X'` has dimension `n`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDimension_exceptionalObj`,
  `isNonemptyEquidimensional_exceptionalObj`: `E` has dimension `n - 1`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDimension_exceptionalProj`: `π` has
  relative dimension `n - 1 - e`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDimension_of_codimension`: `Z` has
  dimension `n - r` when all its components have codimension `r` in `X`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0AFF](https://stacks.math.columbia.edu/tag/0AFF)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-! ### Relative dimension over a field, pointwise -/

/-- Over a field the fibre of a morphism at the image of a point is the whole scheme, so the
local dimension of the fibre there is the local dimension of the scheme. -/
theorem topologicalKrullDimAt_fiber_of_field {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) (t : T) :
    topologicalKrullDimAt (q.fiber (q t)) (q.asFiber t) = topologicalKrullDimAt T t := by
  have hpre : q ⁻¹' {q t} = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  let e : q.fiber (q t) ≃ₜ T :=
    (q.fiberHomeo (q t)).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ T))
  have he : e (q.asFiber t) = t := by
    simp [e, Scheme.Hom.asFiber]
    rfl
  simpa only [he] using topologicalKrullDimAt_eq_of_homeomorph e (q.asFiber t)

/-- **Over a field, relative dimension `d` is local dimension `d` everywhere.** -/
theorem relativeDimension_iff_forall_topologicalKrullDimAt_of_field {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] (d : ℕ) :
    RelativeDimension q d ↔ ∀ t : T, topologicalKrullDimAt T t = (d : WithBot ℕ∞) := by
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  exact forall_congr' fun t ↦ by rw [topologicalKrullDimAt_fiber_of_field q t]

/-- A smooth morphism has relative dimension `d` exactly when its part of dimension `d` is
everything. -/
theorem relativeDimension_iff_forall_mem_dimPart {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX]
    (d : ℕ) : RelativeDimension sX d ↔ ∀ x : X, x ∈ dimPart sX d := by
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  exact forall_congr' fun x ↦ (mem_dimPart_iff_topologicalKrullDimAt sX d x).symm

/-! ### Closed subschemes of pure codimension -/

/-- **A closed subscheme of pure codimension `c` in a scheme of dimension `n` has dimension
`n - c`.** Let `j : T ⟶ P` be a closed immersion of schemes locally of finite type over `k`, with
`P` of relative dimension `n`, such that the local ring of `P` at the image of the generic point
of every irreducible component of `T` has dimension `c`. Then `T` has relative dimension `n - c`.

At a point `t`, the local dimension of `T` is the dimension of some component `W ∋ t`; by the
dimension formula of Tag 0A21 on `P` at the image of the generic point `η` of `W`,
`n = dim j(W) + dim 𝒪_{P, j η} = dim W + c`. -/
theorem relativeDimension_of_ringKrullDim_stalk_eq {T P : Scheme.{u}} (q : T ⟶ Spec (.of k))
    (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType q] [LocallyOfFiniteType sP] (j : T ⟶ P)
    [IsClosedImmersion j] (hj : j ≫ sP = q) {n c : ℕ} (hP : RelativeDimension sP n)
    (hc : ∀ η : T, closure ({η} : Set T) ∈ irreducibleComponents T →
      ringKrullDim (P.presheaf.stalk (j η)) = c) :
    RelativeDimension q (n - c) := by
  rw [relativeDimension_iff_forall_topologicalKrullDimAt_of_field]
  intro t
  obtain ⟨W, hW, -, hWdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k T q t
  have hη : closure ({hW.1.genericPoint} : Set T) = W :=
    (hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)).def
  set η := hW.1.genericPoint
  have hδ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction
      q η = Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction
        sP (j η) := by
    subst hj
    exact Stacks.Chow.relativeDimension_comp_closedImmersion _ j sP η
  have h3 := topologicalKrullDimAt_eq_add_ringKrullDim_stalk k sP (j η)
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sP, hc η (hη ▸ hW),
    (relativeDimension_iff_forall_topologicalKrullDimAt_of_field sP n).1 hP, ← hδ] at h3
  have h4 : n = (Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation k).dimensionFunction q η).toNat + c := by
    exact_mod_cast h3
  rw [← hWdim, ← hη, Stacks.Chow.topologicalKrullDim_closure_singleton_eq k q η,
    show n - c = (Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation k).dimensionFunction q η).toNat by omega]

/-- **The relative dimension of a smooth morphism between equidimensional schemes.** For a smooth
morphism `g : T ⟶ Y` of schemes over `k` with `T` of dimension `a` and `Y` of dimension `b`, the
dimension formula of Tag 0AFF, `dim_t T = dim_{g t} Y + dim_t T_{g t}`, gives fibre dimension
`a - b` at every point. -/
theorem relativeDimension_of_smooth_of_relativeDimension {T Y : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    [LocallyOfFiniteType sY] (g : T ⟶ Y) [Smooth g] {a b : ℕ} (hT : RelativeDimension q a)
    (hY : RelativeDimension sY b) : RelativeDimension g (a - b) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  intro t
  have h := topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth g t
  rw [(relativeDimension_iff_forall_topologicalKrullDimAt_of_field q a).1 hT t,
    (relativeDimension_iff_forall_topologicalKrullDimAt_of_field sY b).1 hY (g t)] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, topologicalKrullDimAt (g.fiber (g t)) (g.asFiber t) = m := by
    generalize topologicalKrullDimAt (g.fiber (g t)) (g.asFiber t) = x at h ⊢
    induction x using WithBot.recBotCoe with
    | bot => simp at h
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        have h' : ((a : ℕ∞) : WithBot ℕ∞) = (((b : ℕ∞) + ⊤ : ℕ∞) : WithBot ℕ∞) := by
          exact_mod_cast h
        rw [add_top] at h'
        exact ENat.natCast_ne_top a (WithBot.coe_injective h')
      | coe m => exact ⟨m, rfl⟩
  rw [hm] at h ⊢
  have h' : a = b + m := by exact_mod_cast h
  rw [show a - b = m by omega]

/-! ### The blowup and its exceptional divisor -/

namespace SmoothProjectiveScheme

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]

/-- The complement of a closed nowhere dense set is dense. -/
private theorem dense_compl_of_isClosed_of_isNowhereDense {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsClosed s) (h : IsNowhereDense s) : Dense sᶜ :=
  (isClosed_isNowhereDense_iff_compl.mp ⟨hs, h⟩).2

/-- The support of the ideal sheaf of `i` is the image of `Z`. -/
theorem coe_support_ker :
    (i.hom.left.ker.support : Set X.obj.left) = Set.range i.hom.left.base := by
  rw [Scheme.Hom.support_ker,
    (IsClosedImmersion.isClosedEmbedding i.hom.left).isClosed_range.closure_eq]

omit [IsClosedImmersion i.hom.left] in
/-- The exceptional divisor `b⁻¹(Z)` of the blowup is nowhere dense (it is an effective Cartier
divisor, Tag 02OS (2)), so its complement, the inverse image of `X \ Z`, is dense in `X'`. -/
theorem dense_preimage_compl_support :
    Dense ((Stacks.Blowup.blowUpToBase i.hom.left.ker).base ⁻¹'
      ((i.hom.left.ker.support : Set X.obj.left)ᶜ)) := by
  have hnd := isNowhereDense_supportSet_of_isEffectiveCartierDivisor _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData i.hom.left.ker)
  have hsupp : (Stacks.Blowup.exceptionalIdeal i.hom.left.ker).supportSet =
      (Stacks.Blowup.blowUpToBase i.hom.left.ker).base ⁻¹'
        (i.hom.left.ker.support : Set X.obj.left) := by
    change ((i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).support :
      Set (Stacks.Blowup.blowUp i.hom.left.ker)) = _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  rw [hsupp] at hnd
  exact dense_compl_of_isClosed_of_isNowhereDense (i.hom.left.ker.support.isClosed.preimage
    (Stacks.Blowup.blowUpToBase i.hom.left.ker).continuous) hnd

/-- **`X'` is equidimensional of dimension `n`** when `X` is (Tag 02OS). Every part of `X'` of
constant dimension is open, so it meets the dense open `b⁻¹(X \ Z)`, over which `b` is an
isomorphism onto an open subscheme of `X` (Tag 02OS (1)); open immersions preserve the parts of
constant dimension. No hypothesis on `Z` is needed: over a component of `X` contained in `Z` the
blowup is empty. -/
theorem relativeDimension_blowupObj {n : ℕ} (hX : RelativeDimension X.obj.hom n) :
    RelativeDimension (blowupObj i).obj.hom n := by
  set b := (blowupHom i).hom.left
  rw [relativeDimension_iff_forall_mem_dimPart]
  intro x
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart (blowupObj i).obj.hom).exists_mem x
  obtain ⟨u, huD, huU⟩ := (dense_preimage_compl_support i).inter_open_nonempty _
    (dimPart (blowupObj i).obj.hom e).2 ⟨x, he⟩
  let V : (blowupObj i).obj.left.Opens := b ⁻¹ᵁ i.hom.left.ker.support.compl
  have : IsIso (b ∣_ i.hom.left.ker.support.compl) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_compl_support_reesData _
  have : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]
    infer_instance
  let v : V := ⟨u, huU⟩
  have h1 := mem_dimPart_iff_of_isOpenImmersion (V.ι ≫ (blowupObj i).obj.hom)
    (blowupObj i).obj.hom V.ι rfl e v
  have h2 := mem_dimPart_iff_of_isOpenImmersion (V.ι ≫ (blowupObj i).obj.hom) X.obj.hom
    (V.ι ≫ b) (by rw [Category.assoc, Over.w (blowupHom i).hom]) e v
  rwa [eq_of_mem_dimPart X.obj.hom hX (h2.1 (h1.2 huD))] at he

/-- **`X'` is nonempty and equidimensional of dimension `n`** when `X` is and `Z` is nowhere
dense in `X`: then `X \ Z` is nonempty and `b` is an isomorphism over it. -/
theorem isNonemptyEquidimensional_blowupObj {n : ℕ} (hX : IsNonemptyEquidimensional X n)
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) :
    IsNonemptyEquidimensional (blowupObj i) n where
  nonempty := by
    have := hX.nonempty
    obtain ⟨w, hw⟩ := (dense_compl_of_isClosed_of_isNowhereDense
      (IsClosedImmersion.isClosedEmbedding i.hom.left).isClosed_range hZ).nonempty
    have : IsIso (Stacks.Blowup.blowUpToBase i.hom.left.ker ∣_ i.hom.left.ker.support.compl) :=
      Stacks.Blowup.isIso_blowUpToBase_restrict_compl_support_reesData _
    let w' : Scheme.Opens.toScheme (X := X.obj.left) i.hom.left.ker.support.compl :=
      ⟨w, show w ∉ (i.hom.left.ker.support : Set X.obj.left) by rwa [coe_support_ker]⟩
    exact ⟨((Stacks.Blowup.blowUpToBase i.hom.left.ker ⁻¹ᵁ
      i.hom.left.ker.support.compl).ι) (inv (Stacks.Blowup.blowUpToBase i.hom.left.ker ∣_
        i.hom.left.ker.support.compl) w')⟩
  relativeDimension := relativeDimension_blowupObj i hX.relativeDimension

/-- The inclusion `j : E ⟶ X'` of the exceptional divisor is a closed immersion. -/
instance isClosedImmersion_exceptionalHom : IsClosedImmersion (exceptionalHom i).hom.left :=
  inferInstanceAs (IsClosedImmersion
    (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left))

/-- The projection `π : E ⟶ Z` is smooth. -/
instance smooth_exceptionalProj_hom_left : Smooth (exceptionalProj i).hom.left :=
  smooth_exceptionalProj i

/-- The exceptional divisor `E = X' ×_X Z` is the closed subscheme of `X'` cut out by the
exceptional ideal `b⁻¹ℐ 𝒪_{X'}` (`Stacks.Blowup.exceptionalIdeal`): an isomorphism over `X'`. -/
def exceptionalToSubscheme :
    Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left ⟶
      (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).subscheme :=
  pullback.map (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left
      (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left.ker.subschemeι (𝟙 _)
      i.hom.left.toImage (𝟙 _) (by simp) (by simp [Scheme.Hom.toImage_imageι]) ≫
    (i.hom.left.ker.comapIso (Stacks.Blowup.blowUpToBase i.hom.left.ker)).inv

/-- The comparison map `exceptionalToSubscheme i` is an isomorphism. -/
instance : IsIso (exceptionalToSubscheme i) := by
  rw [exceptionalToSubscheme]
  infer_instance

omit [IsClosedImmersion i.hom.left] in
/-- The isomorphism `exceptionalToSubscheme i` commutes with the projections to `X'`: composed with
the inclusion of the subscheme it is the first projection of `X' ×_X Z`. -/
@[reassoc (attr := simp)]
theorem exceptionalToSubscheme_subschemeι :
    exceptionalToSubscheme i ≫
        (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).subschemeι =
      pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left := by
  simp [exceptionalToSubscheme]

/-- **The components of `E` have codimension one in `X'`** (Tag 0BCN (2)): `E` is an effective
Cartier divisor (Tag 02OS (2)). -/
theorem ringKrullDim_stalk_exceptionalHom (η : (exceptionalObj i).obj.left)
    (hη : closure ({η} : Set (exceptionalObj i).obj.left) ∈
      irreducibleComponents (exceptionalObj i).obj.left) :
    ringKrullDim ((blowupObj i).obj.left.presheaf.stalk ((exceptionalHom i).hom.left η)) = 1 := by
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp i.hom.left.ker) :=
    isLocallyNoetherian (blowupObj i)
  let η' : ↥(Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left : Scheme.{u}) :=
    η
  let h := (exceptionalToSubscheme i).homeomorph
  have hW : h '' closure {η'} ∈ irreducibleComponents
      (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).subscheme :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber h h.continuous h.isOpenMap
      (fun _ ↦ (Set.subsingleton_singleton.preimage h.injective).isPreirreducible)
      h.surjective hη
  have hgen : IsGenericPoint (h η') (h '' closure {η'}) := by
    rw [h.image_closure, Set.image_singleton]
    exact isGenericPoint_closure
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData i.hom.left.ker
  have := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor _ hD (h η') ⟨⟨_, hW⟩, hgen⟩
  have hpt : (i.hom.left.ker.comap (Stacks.Blowup.blowUpToBase i.hom.left.ker)).subschemeι (h η') =
      pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left η' := by
    rw [← exceptionalToSubscheme_subschemeι i, Scheme.Hom.comp_apply]
    rfl
  rwa [hpt] at this

/-- **`E` is equidimensional of dimension `n - 1`** when `X` is equidimensional of dimension `n`:
by `relativeDimension_blowupObj` `X'` has dimension `n`, and every component of the effective
Cartier divisor `E` has codimension one in it (Tags 02OS, 0BCN, 0A21). (For `n = 0`, `E` is
empty.) -/
theorem relativeDimension_exceptionalObj {n : ℕ} (hX : RelativeDimension X.obj.hom n) :
    RelativeDimension (exceptionalObj i).obj.hom (n - 1) :=
  relativeDimension_of_ringKrullDim_stalk_eq (exceptionalObj i).obj.hom (blowupObj i).obj.hom
    (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom) (relativeDimension_blowupObj i hX)
    fun η hη ↦ by rw [ringKrullDim_stalk_exceptionalHom i η hη]; rfl

/-- **`E` is nonempty and equidimensional of dimension `n - 1`** when `X` is nonempty and
equidimensional of dimension `n` and `Z` is nonempty and nowhere dense in `X`: the blowup is then
surjective, so `E = b⁻¹(Z)` is nonempty. -/
theorem isNonemptyEquidimensional_exceptionalObj {n : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) [Nonempty Z.obj.left] :
    IsNonemptyEquidimensional (exceptionalObj i) (n - 1) where
  nonempty := by
    obtain ⟨z⟩ := ‹Nonempty Z.obj.left›
    have hdense : Dense ((i.hom.left.ker.support.compl : X.obj.left.Opens) : Set X.obj.left) := by
      change Dense ((i.hom.left.ker.support : Set X.obj.left)ᶜ)
      rw [coe_support_ker]
      exact dense_compl_of_isClosed_of_isNowhereDense
        (IsClosedImmersion.isClosedEmbedding i.hom.left).isClosed_range hZ
    have hsurj := Stacks.Blowup.surjective_blowUpToBase hdense (I := i.hom.left.ker)
      ⟨inferInstance, inferInstance, inferInstance⟩ (by
        change Disjoint (i.hom.left.ker.support : Set X.obj.left)ᶜ _
        exact disjoint_compl_left)
    obtain ⟨x, hx⟩ := hsurj.surj (i.hom.left z)
    obtain ⟨e, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
    exact ⟨e⟩
  relativeDimension := relativeDimension_exceptionalObj i hX

/-- **`π : E ⟶ Z` has relative dimension `n - 1 - e`** when `X` and `Z` are equidimensional of
dimensions `n` and `e`: `π` is smooth, and the dimension formula of Tag 0AFF reads off its fibre
dimension. -/
theorem relativeDimension_exceptionalProj {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) :
    RelativeDimension (exceptionalProj i).hom.left (n - 1 - e) :=
  relativeDimension_of_smooth_of_relativeDimension (exceptionalObj i).obj.hom Z.obj.hom
    (exceptionalProj i).hom.left (relativeDimension_exceptionalObj i hX) hZ

/-- **A smooth closed subscheme all of whose irreducible components have codimension `r` in `X`
is equidimensional of dimension `n - r`** when `X` is equidimensional of dimension `n` (Tag 0A21).
The codimension of the component `W = closure {z}` of `Z` in `X` is the coheight of the image of
its generic point `z`, i.e. the dimension of the local ring of `X` there (Tag 02IZ); this is the
hypothesis of Lemma 0FIH. -/
theorem relativeDimension_of_codimension {n r : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r) :
    RelativeDimension Z.obj.hom (n - r) :=
  relativeDimension_of_ringKrullDim_stalk_eq Z.obj.hom X.obj.hom i.hom.left (Over.w i.hom) hX
    fun z hz ↦ by rw [ringKrullDim_stalk_eq_coheight, hr z hz]; rfl

end SmoothProjectiveScheme

end Stacks.WeilCohomology
