module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.EvenCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation

/-!
# The standing situation of Section 45.12 attached to data (D0), (D1), (D2')

Tag 0FIE applies the theory of Chern classes of Section 45.12 to the category of smooth
projective schemes over `k`, the functor `A : X ↦ ⨁_{i ≥ 0} H^{2i}(X)(i)` and the map `c₁^H`.
This file builds that standing situation, as a `Stacks.WeilCohomology.Weak.ChernSetup`, out of
data (D0), (D1), (D2') satisfying axioms (A1) and (A3).

The twists are the tensor-defined `Stacks.WeilCohomology.tateTwist`, and their cup products
`Stacks.WeilCohomology.tateCup` are defined through the coordinates
`Stacks.WeilCohomology.tateTwistCoordinates` attached to the canonical coordinate
`Stacks.WeilCohomology.tateLineCoordinate` on the one-dimensional line `F(1)`, on which they do
not depend. The construction works in those coordinates: they identify `H^{2i}(X)(i)` with
`H^{2i}(X)` compatibly with cup products and pullbacks, so `A(X)` is realised as the even part
`⨁_{i ≥ 0} H^{2i}(X)` of `H^*(X)`, and `c₁^H` is read as a class of `H^2(X)`.

`H^*` is graded by `𝐙`, and the projective bundle formula (A3) is a statement about all of
`H^*`. Read on `A`, it is injective and resolves `c₁^H(𝒪_P(1))^{r+1}` — whose coefficients lie in
the positive degrees `2(r + 1 - i)` — but it need not be onto `A(P)` when `H^*` is nonzero in
negative degrees. That is why the situation is the weak one of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.κ`: the coordinates `H^*(X)(n) ≅ H^*(X)`.
* `Stacks.WeilCohomology.FirstChernClassData.A`: `⨁_{i ≥ 0} H^{2i}(X)(i)`, read through the
  coordinates as `⨁_{i ≥ 0} H^{2i}(X)`.
* `Stacks.WeilCohomology.FirstChernClassData.pullA`: its pullback maps.
* `Stacks.WeilCohomology.FirstChernClassData.c₁A`: `c₁^H` with values in it.
* `Stacks.WeilCohomology.FirstChernClassData.toChernSetup`: the standing situation.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.bijective_pull_of_isOpenImmersion`: axiom (A1)
  for finite decompositions into open and closed subschemes.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-! ### Open immersions into an open subscheme -/

section OpenSubscheme

variable {Y : Scheme.{u}} (W : Y.Opens)

/-- A morphism into an open subscheme is an open immersion when its composite with the
inclusion is. -/
theorem isOpenImmersion_of_comp_ι {Z : Scheme.{u}} (g : Z ⟶ W.toScheme) {f : Z ⟶ Y}
    (h : g ≫ W.ι = f) [IsOpenImmersion f] : IsOpenImmersion g := by
  subst h
  exact IsOpenImmersion.of_comp g W.ι

/-- The range of a morphism into an open subscheme, pushed into the ambient scheme, is the range
of its composite with the inclusion. -/
theorem image_range_of_comp_ι {Z : Scheme.{u}} (g : Z ⟶ W.toScheme) {f : Z ⟶ Y}
    (h : g ≫ W.ι = f) : W.ι '' Set.range g = Set.range f := by
  subst h
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- Two open immersions into an open subscheme have disjoint images when their composites with
the inclusion do. -/
theorem disjoint_opensRange_of_comp_ι {Z₁ Z₂ : Scheme.{u}} (g₁ : Z₁ ⟶ W.toScheme)
    (g₂ : Z₂ ⟶ W.toScheme) {f₁ : Z₁ ⟶ Y} {f₂ : Z₂ ⟶ Y} [IsOpenImmersion g₁]
    [IsOpenImmersion g₂] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    (h₁ : g₁ ≫ W.ι = f₁) (h₂ : g₂ ≫ W.ι = f₂) (h : Disjoint f₁.opensRange f₂.opensRange) :
    Disjoint g₁.opensRange g₂.opensRange := by
  simp only [← TopologicalSpace.Opens.coe_disjoint, Scheme.Hom.coe_opensRange] at h ⊢
  rw [← image_range_of_comp_ι W g₁ h₁, ← image_range_of_comp_ι W g₂ h₂] at h
  exact (Set.disjoint_image_iff W.ι.isOpenEmbedding.injective).mp h

/-- A family of open immersions into an open subscheme `W` covers `W` when the images of their
composites with the inclusion cover `W`. -/
theorem iSup_opensRange_of_comp_ι {ι : Type*} {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ W.toScheme)
    {f : ∀ i, Z i ⟶ Y} [∀ i, IsOpenImmersion (g i)] [∀ i, IsOpenImmersion (f i)]
    (h : ∀ i, g i ≫ W.ι = f i) (hW : W ≤ ⨆ i, (f i).opensRange) :
    ⨆ i, (g i).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : W.ι x ∈ W := by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  obtain ⟨i, z, hz⟩ := TopologicalSpace.Opens.mem_iSup.mp (hW hx)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, z, W.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, h i]
  exact hz

/-- `Y` is the coproduct of `Z` and an open subscheme `W` when the image of `Z` and `W` are
complementary. -/
theorem nonempty_isColimit_binaryCofanMk_ι {Z : Scheme.{u}} (f : Z ⟶ Y) [IsOpenImmersion f]
    (h : IsCompl f.opensRange W) : Nonempty (IsColimit (BinaryCofan.mk f W.ι)) :=
  nonempty_isColimit_binaryCofanMk_of_isCompl f W.ι (by rwa [Scheme.Opens.opensRange_ι])

end OpenSubscheme

/-! ### Axiom (A1) for finite decompositions -/

/-- **Axiom (A1) for a finite decomposition.** If `X` is covered by the pairwise disjoint images of
finitely many open immersions `p i : P i → X` of smooth projective schemes, then
`a ↦ (p_i^* a)_i` identifies `H^*(X)` with `∏ᵢ H^*(P i)`. The source's (A1) is the case of two
pieces and of none; the general case follows by splitting off one piece at a time. -/
theorem bijective_pull_of_isOpenImmersion (hA1 : 𝔇.CoproductAxiom) {ι : Type} [Finite ι]
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (P : ι → (SmoothProjectiveScheme k).FullSubcategory) (p : ∀ i, P i ⟶ X)
    (hp : ∀ i, IsOpenImmersion ((toScheme k).map (p i)))
    (hdisj : Pairwise (Disjoint on fun i => ((toScheme k).map (p i)).opensRange))
    (hcov : ⨆ i, ((toScheme k).map (p i)).opensRange = ⊤) :
    Function.Bijective fun a : 𝔇.H X => fun i => 𝔇.pull (p i) a := by
  revert X P p hp hdisj hcov
  refine Finite.induction_empty_option
    (P := fun ι => ∀ (X : (SmoothProjectiveScheme k).FullSubcategory)
    (P : ι → (SmoothProjectiveScheme k).FullSubcategory) (p : ∀ i, P i ⟶ X)
    (_ : ∀ i, IsOpenImmersion ((toScheme k).map (p i)))
    (_ : Pairwise (Disjoint on fun i => ((toScheme k).map (p i)).opensRange))
    (_ : ⨆ i, ((toScheme k).map (p i)).opensRange = ⊤),
    Function.Bijective fun a : 𝔇.H X => fun i => 𝔇.pull (p i) a) ?_ ?_ ?_ ι
  · -- reindexing along an equivalence
    intro α β e h X P p hp hdisj hcov
    have hα := h X (P ∘ e) (fun i => p (e i)) (fun i => hp (e i))
      (fun i j hij => hdisj (e.injective.ne hij))
      ((Equiv.iSup_comp (g := fun j => ((toScheme k).map (p j)).opensRange) e).trans hcov)
    refine ⟨fun a a' haa' => hα.1 (funext fun i => congrFun haa' (e i)), fun g => ?_⟩
    obtain ⟨a, ha⟩ := hα.2 fun i => g (e i)
    refine ⟨a, funext fun j => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun ha i
  · -- the empty decomposition: `X` is empty and `H^*(X) = 0`
    intro X P p _ _ hcov
    have : IsEmpty ((toScheme k).obj X) := ⟨fun x => by
      have hx : x ∈ (⊤ : ((toScheme k).obj X).Opens) := trivial
      rw [← hcov] at hx
      obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact i.elim⟩
    have := hA1.1 X inferInstance
    exact ⟨fun a a' _ => Subsingleton.elim a a', fun g => ⟨0, funext fun i => i.elim⟩⟩
  · -- splitting off one piece
    intro α _ h X P p hp hdisj hcov
    let S := toScheme k
    let W : (S.obj X).Opens := ⨆ i : α, (S.map (p (some i))).opensRange
    have hcompl : IsCompl (S.map (p none)).opensRange W := by
      constructor
      · rw [disjoint_iSup_iff]
        exact fun i => hdisj (Option.some_ne_none i).symm
      · rw [codisjoint_iff, ← hcov, iSup_option]
    have hW : IsClopen (W : Set (S.obj X)) := by
      have hc : (W : Set (S.obj X))ᶜ = ((S.map (p none)).opensRange : Set (S.obj X)) := by
        refine IsCompl.compl_eq ⟨TopologicalSpace.Opens.coe_disjoint.mpr hcompl.symm.disjoint, ?_⟩
        rw [codisjoint_iff]
        show ((W ⊔ (S.map (p none)).opensRange : (S.obj X).Opens) : Set (S.obj X)) = Set.univ
        rw [sup_comm, hcompl.sup_eq_top]
        rfl
      exact ⟨isOpen_compl_iff.mp (hc ▸ (S.map (p none)).opensRange.isOpen), W.isOpen⟩
    let Wo := clopenSubobject X W hW
    have hfac : ∀ i : α, ∀ z : S.obj (P (some i)), (S.map (p (some i))) z ∈ W := fun i z =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨z, rfl⟩⟩
    choose q hq using fun i : α => Wo.exists_factor (p (some i)) (hfac i)
    have hqmap : ∀ i, (S.map (q i) : S.obj (P (some i)) ⟶ W.toScheme) ≫ W.ι =
        S.map (p (some i)) := fun i => by
      rw [← hq i, S.map_comp]
      rfl
    have := hp
    have hqo : ∀ i, IsOpenImmersion (S.map (q i)) := fun i =>
      isOpenImmersion_of_comp_ι W _ (hqmap i)
    have hdisj' : Pairwise (Disjoint on fun i => (S.map (q i)).opensRange) := fun i j hij =>
      @disjoint_opensRange_of_comp_ι _ W _ _ (S.map (q i)) (S.map (q j)) _ _ (hqo i) (hqo j) _ _
        (hqmap i) (hqmap j) (hdisj (Option.some_injective _ |>.ne hij))
    have hcov' : ⨆ i, (S.map (q i)).opensRange = ⊤ :=
      @iSup_opensRange_of_comp_ι _ W _ _ (fun i => S.map (q i)) _ hqo _ hqmap le_rfl
    have hIH := h (clopen X W hW) (fun i => P (some i)) q hqo hdisj' hcov'
    have hbin := hA1.2 (P none) (clopen X W hW) X (p none) Wo.hom
      (nonempty_isColimit_binaryCofanMk_ι W _ hcompl)
    have hpull : ∀ i (a : 𝔇.H X), 𝔇.pull (p (some i)) a = 𝔇.pull (q i) (𝔇.pull Wo.hom a) :=
      fun i a => by rw [← hq i, 𝔇.pull_comp]; rfl
    refine ⟨fun a a' haa' => hbin.1 (Prod.ext (congrFun haa' none) (hIH.1 (funext fun i => ?_))),
      fun g => ?_⟩
    · have := congrFun haa' (some i)
      simp only [hpull] at this
      exact this
    · obtain ⟨b, hb⟩ := hIH.2 fun i => g (some i)
      obtain ⟨a, ha⟩ := hbin.2 (g none, b)
      refine ⟨a, funext fun o => ?_⟩
      cases o with
      | none => exact congrArg Prod.fst ha
      | some i =>
        show 𝔇.pull (p (some i)) a = g (some i)
        rw [hpull, show 𝔇.pull Wo.hom a = b from congrArg Prod.snd ha]
        exact congrFun hb i


/-! ### Coordinates on the twists -/

/-- The canonical coordinate on the one-dimensional Tate line. -/
abbrev coord : 𝔇.tate ≃ₗ[F] F := tateLineCoordinate 𝔇.finrank_tate

/-- The coordinates `H^*(X)(n) ≅ H^*(X)` attached to `coord`. -/
abbrev κ (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    tateTwist F 𝔇.tate (𝔇.H X) n ≃ₗ[F] 𝔇.H X :=
  tateTwistCoordinates 𝔇.coord n

/-- The coordinates are compatible with pullback: the coordinate of `f^* x` is `f^*` of the
coordinate of `x`. -/
theorem κ_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (x : tateTwist F 𝔇.tate (𝔇.H Y) n) : 𝔇.κ X n (𝔇.pullTw f n x) = 𝔇.pull f (𝔇.κ Y n x) :=
  tateTwistCoordinates_map _ _ _ _

/-- The coordinates carry the cup product of twists to the product of `H^*(X)`. -/
theorem κ_tateCup (X : (SmoothProjectiveScheme k).FullSubcategory) (n m l : ℤ) (h : n + m = l)
    (x : tateTwist F 𝔇.tate (𝔇.H X) n) (y : tateTwist F 𝔇.tate (𝔇.H X) m) :
    𝔇.κ X l (tateCup 𝔇.finrank_tate (𝔇.cup X) n m l h x y) = 𝔇.κ X n x * 𝔇.κ X m y :=
  tateTwistCoordinates_tateCup _ _ _ _ _ _ _ _

/-- The coordinate of the unit of `H^*(X)(0)` is the unit of `H^*(X)`. -/
theorem κ_unitTw (X : (SmoothProjectiveScheme k).FullSubcategory) : 𝔇.κ X 0 (𝔇.unitTw X) = 1 := by
  rw [κ, tateTwistCoordinates_zero, unitTw, LinearEquiv.apply_symm_apply]

/-- The coordinate of the `n`-th twisted power of `x` is the `n`-th power of the coordinate
of `x`. -/
theorem κ_twistPow (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist F 𝔇.tate (𝔇.H X) 1) (n : ℕ) :
    𝔇.κ X n (𝔇.twistPow X x n) = 𝔇.κ X 1 x ^ n := by
  induction n with
  | zero => exact (𝔇.κ_unitTw X).trans (pow_zero _).symm
  | succ n ih =>
    have := 𝔇.κ_tateCup X n 1 (n + 1) (by ring) (𝔇.twistPow X x n) x
    rw [ih, ← pow_succ] at this
    exact this

/-- A twisted class lies in the image of `M(n)` exactly when its coordinate lies in `M`. -/
theorem mem_range_tateTwistMap_iff {X : (SmoothProjectiveScheme k).FullSubcategory}
    (M : Submodule F (𝔇.H X)) (n : ℤ) (x : tateTwist F 𝔇.tate (𝔇.H X) n) :
    x ∈ LinearMap.range (tateTwistMap (L := 𝔇.tate) M.subtype n) ↔ 𝔇.κ X n x ∈ M := by
  constructor
  · rintro ⟨y, rfl⟩
    show tateTwistCoordinates 𝔇.coord n (tateTwistMap M.subtype n y) ∈ M
    rw [tateTwistCoordinates_map]
    exact Submodule.coe_mem _
  · intro hx
    refine ⟨(tateTwistCoordinates 𝔇.coord n).symm ⟨_, hx⟩, (𝔇.κ X n).injective ?_⟩
    show tateTwistCoordinates 𝔇.coord n (tateTwistMap M.subtype n _) = _
    rw [tateTwistCoordinates_map, LinearEquiv.apply_symm_apply]
    rfl

/-- `c₁^H(L)` in coordinates is a class of `H^2(X)`. -/
theorem κ_c₁_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (L) :
    𝔇.κ X 1 (𝔇.c₁ X L) ∈ 𝔇.grade X 2 :=
  (𝔇.mem_range_tateTwistMap_iff _ _ _).mp (𝔇.c₁_mem X L)

/-! ### The projective bundle formula in coordinates -/

/-- `c₁^H(𝒪_P(1))` in coordinates, a class of `H^2(P)`. -/
def bundleClassU (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    𝔇.H (bundle X E r) :=
  𝔇.κ _ 1 (𝔇.bundleClass X E r)

/-- `c₁^H(𝒪_P(1))` in coordinates is a class of `H^2(P)`. -/
theorem bundleClassU_mem (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    𝔇.bundleClassU X E r ∈ 𝔇.grade (bundle X E r) 2 :=
  𝔇.κ_c₁_mem _ _

/-- The projective bundle formula in coordinates. -/
theorem κ_bundleFormula (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (a : ∀ i : Fin (r + 1), tateTwist F 𝔇.tate (𝔇.H X) (-(i : ℤ))) :
    𝔇.κ _ 0 (𝔇.bundleFormula X E r a) =
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) *
        𝔇.pull (bundleProj X E r) (𝔇.κ X (-(i : ℤ)) (a i)) := by
  rw [bundleFormula, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [κ_tateCup, κ_twistPow, κ_pullTw]
  rfl

/-- **Axiom (A3) in coordinates**: `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)` is a bijection
`H^*(X)^{r+1} → H^*(P)`, where `ξ` is `c₁^H(𝒪_P(1))` in coordinates. -/
theorem bijective_bundleFormulaU (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    Function.Bijective fun a : Fin (r + 1) → 𝔇.H X =>
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i) := by
  have key : (fun a : Fin (r + 1) → 𝔇.H X =>
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i)) =
      (𝔇.κ _ 0) ∘ 𝔇.bundleFormula X E r ∘
        fun a i => (𝔇.κ X (-(i : ℤ))).symm (a i) := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, κ_bundleFormula]
    simp only [LinearEquiv.apply_symm_apply]
  rw [key]
  refine (𝔇.κ _ 0).bijective.comp ((hA3 X E r hE).comp ?_)
  exact ⟨fun a b h => funext fun i => (𝔇.κ X _).symm.injective (congrFun h i),
    fun b => ⟨fun i => 𝔇.κ X _ (b i), funext fun i => by simp⟩⟩

/-! ### The functor `A = ⨁_{i ≥ 0} H^{2i}` -/

/-- **`A(X) = ⨁_{i ≥ 0} H^{2i}(X)`**, which the coordinates identify with
`⨁_{i ≥ 0} H^{2i}(X)(i)`. -/
abbrev A (X : (SmoothProjectiveScheme k).FullSubcategory) : Type w := evenPart (𝔇.grade X)

/-- The pullback `f^* : A(Y) → A(X)`. -/
def pullA {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) : 𝔇.A Y →ₐ[F] 𝔇.A X :=
  evenPartMap (𝔇.grade Y) (𝔇.grade X) (𝔇.pull f) (𝔇.pull_grade f)

/-- `f^* : A(Y) → A(X)` acts as `f^* : H^*(Y) → H^*(X)` on underlying classes. -/
@[simp]
theorem coe_pullA {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : 𝔇.A Y) :
    (𝔇.pullA f a : 𝔇.H X) = 𝔇.pull f a := rfl

/-- `c₁^H(L)` in coordinates lies in `A(X)`, being a class of `H^2(X)`. -/
theorem κ_c₁_mem_evenPart (X : (SmoothProjectiveScheme k).FullSubcategory) (L) :
    𝔇.κ X 1 (𝔇.c₁ X L) ∈ evenPart (𝔇.grade X) :=
  mem_evenPart_of_mem (i := 1) _ (by simpa using 𝔇.κ_c₁_mem X L)

/-- `c₁^H : Pic(X) → A^1(X)`, in coordinates. -/
def c₁A (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((toScheme k).obj X).picardGroup →+ 𝔇.A X :=
  ((𝔇.κ X 1).toLinearMap.toAddMonoidHom.comp (𝔇.c₁ X)).codRestrict
    (evenPart (𝔇.grade X)).toSubring.toAddSubgroup fun L => 𝔇.κ_c₁_mem_evenPart X L

/-- `c₁^H : Pic(X) → A^1(X)` is `c₁^H` read in coordinates. -/
@[simp]
theorem coe_c₁A (X : (SmoothProjectiveScheme k).FullSubcategory) (L) :
    (𝔇.c₁A X L : 𝔇.H X) = 𝔇.κ X 1 (𝔇.c₁ X L) := rfl

/-- `c₁^H(L)` lies in the degree-one piece `A^1(X)`. -/
theorem c₁A_mem_evenGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (L) :
    𝔇.c₁A X L ∈ evenGrade (𝔇.grade X) 1 := by
  rw [mem_evenGrade, coe_c₁A]
  simpa using 𝔇.κ_c₁_mem X L

/-! ### Condition (4) on `A` -/

section Bundle

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
  (r : ℕ) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- The clause-(3)(a) object identifies its bundle with `𝐏(ℰ)` by the identity. -/
theorem bundleObject_iso : (bundleObject X E r).iso = Iso.refl _ := by
  unfold BundleObject.iso
  rfl

/-- The twist class of the clause-(3)(a) object is the class of `𝒪_P(1)`. -/
theorem twistClass_bundleObject :
    (bundleObject X E r).twistClass =
      letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
        (r + 1)
      picardClassOf (Stacks.Chow.bundle E) (Stacks.Chow.bundleTwist E)
        (Stacks.Chow.isInvertible_bundleTwist E) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  refine picardClassOf_eq_of_iso _ _ _ _ _
    (eqToIso (bundleObject X E r).twist_eq ≪≫
      (Scheme.Modules.pullbackCongr (by rw [bundleObject_iso, Iso.refl_hom])).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _)

/-- `c₁^H` of the twist class of the clause-(3)(a) object is `c₁^H(𝒪_P(1))` in coordinates. -/
theorem coe_c₁A_twistClass :
    (𝔇.c₁A (bundle X E r) (bundleObject X E r).twistClass : 𝔇.H (bundle X E r)) =
      𝔇.bundleClassU X E r :=
  congrArg (fun L => 𝔇.κ (bundle X E r) 1 (𝔇.c₁ (bundle X E r) L))
    (twistClass_bundleObject X E r)

/-- A combination `∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)` formed in `A(P)` is the same combination formed
in `H^*(P)`. -/
theorem coe_sum_A (a : Fin (r + 1) → 𝔇.A X) :
    ((∑ i : Fin (r + 1),
        𝔇.c₁A (bundle X E r) (bundleObject X E r).twistClass ^ (i : ℕ) *
          𝔇.pullA (bundleProj X E r) (a i) : 𝔇.A (bundle X E r)) : 𝔇.H (bundle X E r)) =
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) *
        𝔇.pull (bundleProj X E r) (a i : 𝔇.H X) := by
  simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
    coe_c₁A_twistClass, coe_pullA]

/-- **Condition (4) on `A`, injectivity**, from axiom (A3). -/
theorem injective_bundleFormulaA (hA3 : 𝔇.ProjectiveBundleAxiom) :
    Function.Injective fun a : Fin (r + 1) → 𝔇.A X =>
      ∑ i : Fin (r + 1), 𝔇.c₁A (bundle X E r) (bundleObject X E r).twistClass ^ (i : ℕ) *
        𝔇.pullA (bundleProj X E r) (a i) := by
  intro a a' h
  have h' := congrArg (fun z : 𝔇.A (bundle X E r) => (z : 𝔇.H (bundle X E r))) h
  simp only [coe_sum_A] at h'
  have := (𝔇.bijective_bundleFormulaU hA3 X E r).1 h'
  funext i
  exact Subtype.ext (congrFun this i)

/-- **Condition (4) on `A`, the top power**, from axiom (A3): `c₁^H(𝒪_P(1))^{r+1}` is
`∑ c₁^H(𝒪_P(1))^i ∪ p^*(a_i)` with `a_i ∈ H^{2(r+1-i)}(X)`. The coefficients the projective bundle
formula produces are homogeneous of these degrees because the formula is graded. -/
theorem exists_bundleFormulaA_eq_pow (hA3 : 𝔇.ProjectiveBundleAxiom) :
    ∃ a : Fin (r + 1) → 𝔇.A X,
      ∑ i : Fin (r + 1), 𝔇.c₁A (bundle X E r) (bundleObject X E r).twistClass ^ (i : ℕ) *
          𝔇.pullA (bundleProj X E r) (a i) =
        𝔇.c₁A (bundle X E r) (bundleObject X E r).twistClass ^ (r + 1) := by
  classical
  set η := 𝔇.bundleClassU X E r with hη
  have hηm : η ∈ 𝔇.grade (bundle X E r) 2 := 𝔇.bundleClassU_mem X E r
  have hηpow : ∀ n : ℕ, η ^ n ∈ 𝔇.grade (bundle X E r) (2 * (n : ℤ)) := fun n => by
    have := SetLike.pow_mem_graded n hηm
    rwa [nsmul_eq_mul, mul_comm] at this
  obtain ⟨c, hc⟩ := (𝔇.bijective_bundleFormulaU hA3 X E r).2 (η ^ (r + 1))
  simp only [← hη] at hc
  let c' : Fin (r + 1) → 𝔇.H X := fun i =>
    DirectSum.decompose (𝔇.grade X) (c i) (2 * ((r + 1 - (i : ℕ) : ℕ) : ℤ))
  have hc' : ∑ i : Fin (r + 1), η ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (c' i) =
      η ^ (r + 1) := by
    have h := congrArg (_root_.GradedAlgebra.proj (𝔇.grade (bundle X E r))
      (2 * ((r + 1 : ℕ) : ℤ))) hc
    rw [map_sum] at h
    simp only [_root_.GradedAlgebra.proj_apply] at h
    rw [DirectSum.decompose_of_mem_same _ (hηpow (r + 1))] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdeg : 2 * ((r + 1 : ℕ) : ℤ) = 2 * ((i : ℕ) : ℤ) + 2 * ((r + 1 - (i : ℕ) : ℕ) : ℤ) := by
      have := i.2
      push_cast [Nat.cast_sub this.le]
      ring
    rw [hdeg, DirectSum.coe_decompose_mul_add_of_left_mem (𝔇.grade (bundle X E r)) (hηpow i),
      decompose_map (𝔇.grade X) (𝔇.grade (bundle X E r)) (𝔇.pull (bundleProj X E r))
        (𝔇.pull_grade _)]
  let a : Fin (r + 1) → 𝔇.A X := fun i =>
    ⟨c' i, mem_evenPart_of_mem _ (DirectSum.decompose (𝔇.grade X) (c i) _).2⟩
  refine ⟨a, Subtype.ext ?_⟩
  rw [coe_sum_A, SubmonoidClass.coe_pow, coe_c₁A_twistClass, ← hc']

end Bundle

/-! ### Condition (2) on `A` -/

section Clopen

variable (hA1 : 𝔇.CoproductAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (ι : Type)
  [Finite ι] (U : ι → ((toScheme k).obj X).Opens)
  (hU : ∀ i, IsClopen (U i : Set ((toScheme k).obj X)))
  (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
  (hcover : (⨆ i, U i) = ⊤)

include hA1 hdisj hcover in
/-- Axiom (A1) for a finite decomposition into open and closed subschemes. -/
theorem bijective_pull_clopen :
    Function.Bijective fun a : 𝔇.H X => fun i => 𝔇.pull (clopenSubobject X (U i) (hU i)).hom a := by
  refine 𝔇.bijective_pull_of_isOpenImmersion hA1 X (fun i => (clopenSubobject X (U i) (hU i)).obj)
    (fun i => (clopenSubobject X (U i) (hU i)).hom)
    (fun i => (inferInstance : IsOpenImmersion (U i).ι)) (fun i j hij => ?_) ?_
  · show Disjoint (U i).ι.opensRange (U j).ι.opensRange
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact hdisj i j hij
  · show ⨆ i, (U i).ι.opensRange = ⊤
    simp only [Scheme.Opens.opensRange_ι]
    exact hcover

include hA1 hdisj hcover in
/-- **Condition (2) on `A`**, from axiom (A1): `A(X) = ∏ᵢ A(U i)` for a finite decomposition of
`X` into open and closed subschemes. -/
theorem bijective_pullA_clopen :
    Function.Bijective
      fun a : 𝔇.A X => fun i => 𝔇.pullA (clopenSubobject X (U i) (hU i)).hom a := by
  have hH := 𝔇.bijective_pull_clopen hA1 X ι U hU hdisj hcover
  refine ⟨fun a a' h => Subtype.ext (hH.1 (funext fun i => congrArg Subtype.val (congrFun h i))),
    fun g => ?_⟩
  obtain ⟨y, hy⟩ := hH.2 fun i => (g i : 𝔇.H _)
  have hym : y ∈ ⨆ n : ℕ, 𝔇.grade X (2 * (n : ℤ)) :=
    mem_iSup_of_forall_map_mem (𝔇.grade X) (fun i => 𝔇.grade (clopenSubobject X (U i) (hU i)).obj)
      (fun i => 𝔇.pull (clopenSubobject X (U i) (hU i)).hom) (fun i n => 𝔇.pull_grade _ n)
      hH.1 (fun n : ℕ => 2 * (n : ℤ)) fun i => by
        rw [show 𝔇.pull (clopenSubobject X (U i) (hU i)).hom y = _ from congrFun hy i]
        exact (g i).2
  exact ⟨⟨y, hym⟩, funext fun i => Subtype.ext (congrFun hy i)⟩

include hA1 hdisj hcover in
/-- Condition (2) on `A` is a splitting of graded rings. -/
theorem mem_grade_of_pullA_clopen (a : 𝔇.A X) (n : ℕ)
    (h : ∀ i, 𝔇.pullA (clopenSubobject X (U i) (hU i)).hom a ∈
      evenGrade (𝔇.grade (clopenSubobject X (U i) (hU i)).obj) n) :
    a ∈ evenGrade (𝔇.grade X) n :=
  mem_of_forall_map_mem (𝔇.grade X) (fun i => 𝔇.grade (clopenSubobject X (U i) (hU i)).obj)
    (fun i => 𝔇.pull (clopenSubobject X (U i) (hU i)).hom) (fun _ n => 𝔇.pull_grade _ n)
    (𝔇.bijective_pull_clopen hA1 X ι U hU hdisj hcover).1 fun i => h i

end Clopen

/-! ### The standing situation -/

/-- **The standing situation of Section 45.12 attached to data (D0), (D1), (D2') satisfying
(A1) and (A3)**: the category of smooth projective schemes over `k`, the functor
`A : X ↦ ⨁_{i ≥ 0} H^{2i}(X)(i)` — read through the coordinates as `⨁_{i ≥ 0} H^{2i}(X)` — and
the map `c₁^H`. Condition (2) is (A1) and condition (4), in the weak form of
`Stacks.WeilCohomology.Weak.ChernSetup`, is (A3). -/
def toChernSetup (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) :
    Weak.ChernSetup (SmoothProjectiveScheme k).FullSubcategory (toScheme k) where
  compactSpace X := inferInstance
  A := 𝔇.A
  grade X := evenGrade (𝔇.grade X)
  one_mem X := one_mem_even _
  mul_mem X i j a b ha hb := mul_mem_even _ ha hb
  isInternal_grade X := isInternal_evenGrade (𝔇.grade X)
  pull f := (𝔇.pullA f).toRingHom
  pull_id X := RingHom.ext fun a => Subtype.ext (by
    change 𝔇.pull (𝟙 X) (a : 𝔇.H X) = a
    rw [𝔇.pull_id]
    rfl)
  pull_comp f g := RingHom.ext fun a => Subtype.ext (by
    change 𝔇.pull (f ≫ g) (a : 𝔇.H _) = 𝔇.pull f (𝔇.pull g a)
    rw [𝔇.pull_comp]
    rfl)
  pull_grade f i a ha := 𝔇.pull_grade f _ _ ha
  c₁ := 𝔇.c₁A
  c₁_mem X L := 𝔇.c₁A_mem_evenGrade X L
  c₁_central X L a := Subtype.ext (mul_comm_of_mem_evenPart _ (𝔇.graded_comm X)
    (𝔇.c₁A X L).2 a.2)
  bundleObject X E r hE := @bundleObject k _ X E r hE
  injective_bundleFormula_bundleObject X E r hE := @injective_bundleFormulaA k _ F _ 𝔇 X E r hE hA3
  exists_bundleFormula_eq_pow_bundleObject X E r hE :=
    @exists_bundleFormulaA_eq_pow k _ F _ 𝔇 X E r hE hA3
  clopenSubobject := clopenSubobject
  bijective_pull_clopenSubobject X ι _ U hU hdisj hcover :=
    𝔇.bijective_pullA_clopen hA1 X ι U hU hdisj hcover
  mem_grade_of_pull_clopenSubobject X ι _ U hU hdisj hcover a n h :=
    𝔇.mem_grade_of_pullA_clopen hA1 X ι U hU hdisj hcover a n h

end FirstChernClassData

end Stacks.WeilCohomology

end
