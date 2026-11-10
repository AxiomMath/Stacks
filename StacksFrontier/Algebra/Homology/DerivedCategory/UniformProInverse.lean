module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.CategoryTheory.InverseSequence.UniformInverses
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Uniform inverses in the derived category, detected on cohomology

Let `α : X ⟶ Y` be a morphism of inverse sequences of cochain complexes in an abelian category
`𝒜`.  This file gives a criterion for the induced morphism of inverse sequences in `D(𝒜)` to have
*uniform inverses* — inverses `Y_m ⟶ X_n` for all `m ≥ n + c`, with `c` independent of `n` —
which is the notion of isomorphism of the strict pro-category of [Stacks, Tag 0GA5].

The criterion is the one the source sketches for the comparison of the derived and the naive
reductions of a complex.  Assume:

* the `Y_n` have cohomology in a fixed interval `[a, b]` and the `X_n` have none above `b`;
* the transition maps of `X`, after a fixed number of steps, kill every map from an object with
  cohomology in degrees `≤ e` (this is how the source uses Proposition 15.96.? / [Stacks, Tag
  0GA3]: the transitions of the derived system factor through a truncation);
* in every degree `d`, the morphism `H^d(α)` has uniform inverses (possibly only after applying
  a faithful exact functor `G`).

Then `α` has uniform inverses in `D(𝒜)`.  The cohomology of the cones of `α` then has uniformly
vanishing transitions in every degree, the cones are bounded above uniformly, and their
transitions kill everything in degrees `≤ e`; a composite of `b - e` transitions which vanish on
cohomology factors through the `≤ e` part (this is [Stacks, Tag 08Q2], read in the t-structure),
so a fixed composite of transitions of the cones vanishes, and the long exact sequences of the
triangles `X_n ⟶ Y_n ⟶ C_n ⟶ X_n[1]` turn this into uniform inverses.

## Main definitions

* `DerivedCategory.coneTriangleSystem`: the inverse system of distinguished triangles given by
  the mapping cones of the components of `α`.

## Main results

* `DerivedCategory.eq_zero_of_isGE_of_isLE`: a morphism between objects concentrated in one
  degree `n` vanishes as soon as it vanishes on `H^n`.
* `DerivedCategory.comp_truncGEπ_eq_zero`: a morphism out of an object with no cohomology above
  `n` that vanishes on `H^n` factors through the truncation `τ_{< n}` of its target.
* `DerivedCategory.hasUniformInverses_whiskerRight_Q`: **the criterion.**

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Opposite CategoryTheory.InverseSequence

namespace DerivedCategory

universe w v u v' u'

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

open TStructure

/-! ### Morphisms and truncations -/

/-- A map of complexes vanishing on `H^d` vanishes on `H^d` in the derived category. -/
theorem homologyFunctor_map_Q_map_eq_zero {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (d : ℤ)
    (hf : HomologicalComplex.homologyMap f d = 0) :
    (homologyFunctor 𝒜 d).map (Q.map f) = 0 := by
  refine (cancel_mono ((homologyFunctorFactors 𝒜 d).hom.app L)).1 ?_
  rw [homologyFunctorFactors_hom_naturality, hf, zero_comp]
  exact comp_zero

/-- A morphism between two objects of `D(𝒜)` concentrated in the degree `n` vanishes as soon as
it vanishes on `H^n`: both are single complexes, and the single functor is fully faithful. -/
theorem eq_zero_of_isGE_of_isLE {S T : DerivedCategory 𝒜} (n : ℤ) [S.IsGE n] [S.IsLE n]
    [T.IsGE n] [T.IsLE n] (f : S ⟶ T) (hf : (homologyFunctor 𝒜 n).map f = 0) : f = 0 := by
  obtain ⟨A, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE S n
  obtain ⟨B, ⟨e'⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T n
  obtain ⟨g, hg⟩ := (singleFunctor 𝒜 n).map_surjective (e.inv ≫ f ≫ e'.hom)
  have hg0 : g = 0 := by
    have h := NatIso.naturality_2 (singleFunctorCompHomologyFunctorIso 𝒜 n) g
    have h0 : (homologyFunctor 𝒜 n).map ((singleFunctor 𝒜 n).map g) = 0 := by
      rw [hg, Functor.map_comp, Functor.map_comp, hf, zero_comp, comp_zero]
    rw [Functor.comp_map, h0] at h
    have hg' : g = (singleFunctorCompHomologyFunctorIso 𝒜 n).inv.app A ≫
        ((singleFunctorCompHomologyFunctorIso 𝒜 n).hom.app A ≫ (𝟭 𝒜).map g ≫
          (singleFunctorCompHomologyFunctorIso 𝒜 n).inv.app B) ≫
        (singleFunctorCompHomologyFunctorIso 𝒜 n).hom.app B := by simp
    rw [hg', h, zero_comp, comp_zero]
  have hf' : f = e.hom ≫ (singleFunctor 𝒜 n).map g ≫ e'.inv := by
    rw [hg]
    simp
  rw [hf', hg0, Functor.map_zero, zero_comp, comp_zero]

/-- A morphism `f : X ⟶ Y` with `X` without cohomology above `n` and `H^n(f) = 0` is killed by
the truncation `Y ⟶ τ_{≥ n} Y`. -/
theorem comp_truncGEπ_eq_zero {X Y : DerivedCategory 𝒜} (n : ℤ) [X.IsLE n] (f : X ⟶ Y)
    (hf : (homologyFunctor 𝒜 n).map f = 0) : f ≫ (t.truncGEπ n).app Y = 0 := by
  rw [← t.truncGEπ_naturality]
  suffices h : (t.truncGE n).map f = 0 by rw [h, comp_zero]
  have hiso : IsIso ((homologyFunctor 𝒜 n).map ((t.truncGEπ n).app X)) :=
    isIso_homologyFunctor_map_truncGEπ n n le_rfl X
  have hw : (homologyFunctor 𝒜 n).map ((t.truncGE n).map f) = 0 := by
    rw [← cancel_epi ((homologyFunctor 𝒜 n).map ((t.truncGEπ n).app X)), comp_zero,
      ← Functor.map_comp, t.truncGEπ_naturality, Functor.map_comp, hf, zero_comp]
  let w' := t.liftTruncLT ((t.truncGE n).map f) n (n + 1) rfl
  have hw' : w' ≫ (t.truncLTι (n + 1)).app ((t.truncGE n).obj Y) = (t.truncGE n).map f :=
    t.liftTruncLT_ι _ _ _ _
  have hiso' : IsIso ((homologyFunctor 𝒜 n).map
      ((t.truncLTι (n + 1)).app ((t.truncGE n).obj Y))) :=
    isIso_homologyFunctor_map_truncLTι (n + 1) n (by omega) _
  have h0 : w' = 0 := by
    apply eq_zero_of_isGE_of_isLE n
    rw [← cancel_mono ((homologyFunctor 𝒜 n).map
      ((t.truncLTι (n + 1)).app ((t.truncGE n).obj Y))), zero_comp, ← Functor.map_comp, hw', hw]
  rw [← hw', h0, zero_comp]

/-- A morphism killed by `τ_{≥ n}` of its target factors through `τ_{< n}` of it. -/
theorem exists_eq_comp_truncLTι {W Y : DerivedCategory 𝒜} (n : ℤ) (f : W ⟶ Y)
    (hf : f ≫ (t.truncGEπ n).app Y = 0) :
    ∃ g : W ⟶ (t.truncLT n).obj Y, f = g ≫ (t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n Y) f hf

/-- A morphism of cochain complexes vanishing in all degrees `≤ e` kills, in `D(𝒜)`, every map
out of an object without cohomology above `e`. -/
theorem comp_Q_map_eq_zero_of_f_eq_zero {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (e : ℤ)
    (hf : ∀ i, i ≤ e → f.f i = 0) (W : DerivedCategory 𝒜) (hW : W.IsLE e)
    (g : W ⟶ Q.obj K) : g ≫ Q.map f = 0 := by
  have hS := K.shortComplexTruncLE_shortExact e
  have hT := triangleOfSES_distinguished hS
  have hiso : IsIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE e (e + 1) rfl)) := inferInstance
  have hge : (Q.obj (K.shortComplexTruncLE e).X₃).IsGE (e + 1) :=
    t.isGE_of_iso (asIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE e (e + 1) rfl))).symm (e + 1)
  obtain ⟨g', hg'⟩ : ∃ g' : W ⟶ Q.obj (K.truncLE e), g = g' ≫ Q.map (K.ιTruncLE e) :=
    Triangle.coyoneda_exact₂ _ hT g (t.zero_of_isLE_of_isGE _ e (e + 1) (by omega) hW hge)
  have hι : K.ιTruncLE e ≫ f = 0 := by
    ext i
    by_cases hi : i ≤ e
    · simp [hf i hi]
    · exact (CochainComplex.isZero_of_isStrictlyLE (K.truncLE e) e i (by omega)).eq_of_src _ _
  rw [hg', Category.assoc, ← Q.map_comp, hι, Q.map_zero, comp_zero]

/-! ### Iterated vanishing along an inverse sequence -/

section Iteration

variable (Z : ℕᵒᵖ ⥤ DerivedCategory 𝒜)

/-- A composite of transitions, whose first factor is killed by `τ_{≥ k}`, is killed by `u` as soon
as `u` kills the second factor precomposed with `τ_{< k} ⟶ id`. -/
private theorem tr_comp_eq_zero_of_truncGEπ {n n' m : ℕ} (h₁ : n' ≤ m) (h₂ : n ≤ n') (k : ℤ)
    {V : DerivedCategory 𝒜} (u : Z.obj (op n) ⟶ V)
    (hk : tr Z h₁ ≫ (t.truncGEπ k).app (Z.obj (op n')) = 0)
    (hu : ((t.truncLTι k).app (Z.obj (op n')) ≫ tr Z h₂) ≫ u = 0) :
    tr Z (h₂.trans h₁) ≫ u = 0 := by
  obtain ⟨g, hg⟩ := exists_eq_comp_truncLTι _ _ hk
  rw [← tr_comp Z h₂ h₁, hg, Category.assoc, Category.assoc, ← Category.assoc _ (tr Z h₂), hu,
    comp_zero]

/-- **[Stacks, Tag 08Q2], read in the t-structure.**  If an inverse sequence has no cohomology
above `b` from the level `N` on, and its `c`-step transitions vanish on `H^d` for `e < d ≤ b`,
then each composite of `k ≤ b - e` such transitions is killed by `τ_{≥ b + 1 - k}`. -/
theorem tr_comp_truncGEπ_eq_zero (b e : ℤ) (N c : ℕ)
    (hZ : ∀ n, N ≤ n → (Z.obj (op n)).IsLE b)
    (hH : ∀ d : ℤ, e < d → d ≤ b → ∀ n, N ≤ n →
      (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0) :
    ∀ k : ℕ, k ≤ (b - e).toNat → ∀ n m : ℕ, N ≤ n → (h : n ≤ m) → n + k * c ≤ m →
      tr Z h ≫ (t.truncGEπ (b + 1 - k)).app (Z.obj (op n)) = 0 := by
  intro k
  induction k with
  | zero =>
    intro _ n m hn h _
    have := hZ n hn
    have hz : IsZero ((t.truncGE (b + 1 - ((0 : ℕ) : ℤ))).obj (Z.obj (op n))) :=
      t.isZero_truncGE_obj_of_isLE b (b + 1 - ((0 : ℕ) : ℤ)) (by simp) _
    exact hz.eq_of_tgt _ _
  | succ k ih =>
    intro hk n m hn h hm
    have h₁ : n + c ≤ m := by
      have : c ≤ (k + 1) * c := Nat.le_mul_of_pos_left c (Nat.succ_pos k)
      omega
    have h₂ : n + c + k * c ≤ m := by rw [Nat.succ_mul] at hm; omega
    have hih := ih (by omega) (n + c) m (by omega) h₁ h₂
    have hle : ((t.truncLT (b + 1 - k)).obj (Z.obj (op (n + c)))).IsLE (b - k) :=
      t.isLE_truncLT_obj _ _ _ (by omega)
    have hd := hH (b - k) (by omega) (by omega) n hn
    have hz := comp_truncGEπ_eq_zero (b - k)
      ((t.truncLTι (b + 1 - k)).app (Z.obj (op (n + c))) ≫ tr Z (Nat.le_add_right n c))
      (by rw [Functor.map_comp, hd, comp_zero])
    have he : b + 1 - ((k + 1 : ℕ) : ℤ) = b - k := by omega
    rw [he]
    exact tr_comp_eq_zero_of_truncGEπ Z h₁ _ _ _ hih hz

/-- **A fixed composite of transitions vanishes.**  If moreover the `c₂`-step transitions kill
every map out of an object with no cohomology above `e`, then the transitions over
`c₂ + (b - e) c` steps vanish from the level `N` on. -/
theorem tr_eq_zero_of_homology (b e : ℤ) (N c c₂ : ℕ)
    (hZ : ∀ n, N ≤ n → (Z.obj (op n)).IsLE b)
    (hH : ∀ d : ℤ, e < d → d ≤ b → ∀ n, N ≤ n →
      (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0)
    (htail : ∀ n, N ≤ n → ∀ (W : DerivedCategory 𝒜), W.IsLE e →
      ∀ g : W ⟶ Z.obj (op (n + c₂)), g ≫ tr Z (Nat.le_add_right n c₂) = 0) :
    ∀ n m : ℕ, N ≤ n → (h : n ≤ m) → n + c₂ + (b - e).toNat * c ≤ m → tr Z h = 0 := by
  intro n m hn h hm
  have h₁ : n + c₂ ≤ m := by omega
  have hk := tr_comp_truncGEπ_eq_zero Z b e N c hZ hH (b - e).toNat le_rfl (n + c₂) m
    (by omega) h₁ (by omega)
  have hle : ((t.truncLT (b + 1 - (b - e).toNat)).obj (Z.obj (op (n + c₂)))).IsLE e :=
    t.isLE_truncLT_obj _ _ _ (by omega)
  simpa using tr_comp_eq_zero_of_truncGEπ Z h₁ (Nat.le_add_right n c₂) _ (𝟙 _) hk
    (by simpa using htail n hn _ hle _)

end Iteration

/-! ### The system of cones -/

section Cones

variable {X Y : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (α : X ⟶ Y)

omit [HasDerivedCategory 𝒜] in
/-- `mappingCone.map` along identities is the identity. -/
private lemma mappingCone_map_eq_id {K L : CochainComplex 𝒜 ℤ} (φ : K ⟶ L) (a : K ⟶ K)
    (b : L ⟶ L) (h : φ ≫ b = a ≫ φ) (ha : a = 𝟙 _) (hb : b = 𝟙 _) :
    CochainComplex.mappingCone.map φ φ a b h = 𝟙 _ := by
  subst ha hb
  exact CochainComplex.mappingCone.map_id φ

omit [HasDerivedCategory 𝒜] in
/-- `mappingCone.map` of composites is the composite. -/
private lemma mappingCone_map_eq_comp {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex 𝒜 ℤ} (φ₁ : K₁ ⟶ L₁)
    (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃)
    (a'' : K₁ ⟶ K₃) (b'' : L₁ ⟶ L₃) (h : φ₁ ≫ b = a ≫ φ₂) (h' : φ₂ ≫ b' = a' ≫ φ₃)
    (h'' : φ₁ ≫ b'' = a'' ≫ φ₃) (ha : a'' = a ≫ a') (hb : b'' = b ≫ b') :
    CochainComplex.mappingCone.map φ₁ φ₃ a'' b'' h'' =
      CochainComplex.mappingCone.map φ₁ φ₂ a b h ≫
        CochainComplex.mappingCone.map φ₂ φ₃ a' b' h' := by
  subst ha hb
  exact CochainComplex.mappingCone.map_comp φ₁ φ₂ φ₃ a b h a' b' h'

/-- The inverse system of the distinguished triangles `X_n ⟶ Y_n ⟶ C(α_n) ⟶ X_n[1]` in
`D(𝒜)`, given by the mapping cones of the components of `α`. -/
noncomputable def coneTriangleSystem : ℕᵒᵖ ⥤ Triangle (DerivedCategory 𝒜) where
  obj n := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (α.app n))
  map f := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap (α.app _) (α.app _)
    (X.map f) (Y.map f) (α.naturality f).symm)
  map_id n := by
    rw [← Q.mapTriangle.map_id]
    congr 1
    refine Triangle.hom_ext _ _ ?_ ?_ ?_
    · exact X.map_id n
    · exact Y.map_id n
    · exact mappingCone_map_eq_id _ _ _ (α.naturality _).symm (X.map_id n) (Y.map_id n)
  map_comp f g := by
    rw [← Q.mapTriangle.map_comp]
    congr 1
    refine Triangle.hom_ext _ _ ?_ ?_ ?_
    · exact X.map_comp f g
    · exact Y.map_comp f g
    · exact mappingCone_map_eq_comp _ _ _ _ _ _ _ _ _ (α.naturality _).symm
        (α.naturality _).symm (α.naturality _).symm (X.map_comp f g) (Y.map_comp f g)

/-- Each triangle `X_n ⟶ Y_n ⟶ C(α_n) ⟶ X_n[1]` of `coneTriangleSystem α` is distinguished. -/
theorem coneTriangleSystem_distinguished (n : ℕᵒᵖ) :
    (coneTriangleSystem α).obj n ∈ distTriang (DerivedCategory 𝒜) :=
  mappingCone_triangle_distinguished (α.app n)

/-- The first morphism of the `n`-th triangle of `coneTriangleSystem α` is the image of `α_n`. -/
@[simp]
theorem coneTriangleSystem_obj_mor₁ (n : ℕᵒᵖ) :
    ((coneTriangleSystem α).obj n).mor₁ = Q.map (α.app n) := rfl

/-- The first component of the transition map of `coneTriangleSystem α` along `f` is the image
of `X.map f`. -/
@[simp]
theorem coneTriangleSystem_map_hom₁ {n n' : ℕᵒᵖ} (f : n ⟶ n') :
    ((coneTriangleSystem α).map f).hom₁ = Q.map (X.map f) := rfl

/-- The second component of the transition map of `coneTriangleSystem α` along `f` is the image
of `Y.map f`. -/
@[simp]
theorem coneTriangleSystem_map_hom₂ {n n' : ℕᵒᵖ} (f : n ⟶ n') :
    ((coneTriangleSystem α).map f).hom₂ = Q.map (Y.map f) := rfl

end Cones

/-! ### The criterion -/

/-- If `f` kills every map out of an object without cohomology above `e`, then `f[1]` kills every
map out of an object without cohomology above `e - 1`. -/
theorem comp_shift_map_eq_zero {A B : DerivedCategory 𝒜} (f : A ⟶ B) (e : ℤ)
    (hf : ∀ (W : DerivedCategory 𝒜), W.IsLE e → ∀ g : W ⟶ A, g ≫ f = 0)
    (W : DerivedCategory 𝒜) (hW : W.IsLE (e - 1)) (g : W ⟶ A⟦(1 : ℤ)⟧) :
    g ≫ f⟦(1 : ℤ)⟧' = 0 := by
  let F := shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)
  let iso := (shiftFunctorCompIsoId (DerivedCategory 𝒜) (-1 : ℤ) 1 (by norm_num)).app W
  obtain ⟨g', hg'⟩ := F.map_surjective (iso.hom ≫ g)
  have hW' : (W⟦(-1 : ℤ)⟧).IsLE e := t.isLE_shift W (e - 1) (-1) e (by omega)
  have hg : g = iso.inv ≫ F.map g' := by rw [hg']; simp
  rw [hg, Category.assoc, ← F.map_comp, hf _ hW' g', F.map_zero, comp_zero]

section Criterion

variable {X Y : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (α : X ⟶ Y)

/-- Vanishing on `H^d` of the transitions of the cones over `c` steps persists over more steps. -/
private lemma cone_homology_eq_zero_mono {d : ℤ} {c c' : ℕ} (hcc' : c ≤ c')
    (h : ∀ n : ℕ, (homologyFunctor 𝒜 d).map
      (tr (coneTriangleSystem α) (Nat.le_add_right n c)).hom₃ = 0) (n : ℕ) :
    (homologyFunctor 𝒜 d).map (tr (coneTriangleSystem α) (Nat.le_add_right n c')).hom₃ = 0 := by
  rw [← tr_comp _ (Nat.le_add_right n c) (by omega : n + c ≤ n + c'), comp_hom₃,
    Functor.map_comp, h, comp_zero]

/-- Finitely many degrees of vanishing on cohomology hold with a common number of steps. -/
private lemma exists_cone_homology_eq_zero_of_finite
    (h : ∀ d : ℤ, ∃ c : ℕ, ∀ n : ℕ, (homologyFunctor 𝒜 d).map
      (tr (coneTriangleSystem α) (Nat.le_add_right n c)).hom₃ = 0) (lo : ℤ) (L : ℕ) :
    ∃ c : ℕ, ∀ d : ℤ, lo ≤ d → d ≤ lo + L → ∀ n : ℕ, (homologyFunctor 𝒜 d).map
      (tr (coneTriangleSystem α) (Nat.le_add_right n c)).hom₃ = 0 := by
  induction L with
  | zero =>
    obtain ⟨c, hc⟩ := h lo
    exact ⟨c, fun d h₁ h₂ => by
      obtain rfl : d = lo := by omega
      exact hc⟩
  | succ L ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := h (lo + (L + 1 : ℕ))
    refine ⟨max c c', fun d h₁ h₂ => ?_⟩
    by_cases hd : d ≤ lo + L
    · exact cone_homology_eq_zero_mono α (le_max_left _ _) (hc d h₁ hd)
    · obtain rfl : d = lo + (L + 1 : ℕ) := by omega
      exact cone_homology_eq_zero_mono α (le_max_right _ _) hc'

/-- **Uniform inverses in `D(𝒜)` from the cohomology of the cones.**  Let `α : X ⟶ Y` be a
morphism of inverse sequences of cochain complexes such that the `Y_n` have cohomology in
`[a, b]`, the `X_n` have none above `b`, the transitions of `X` over `c₀` steps kill every map
out of an object without cohomology above `e < a`, and in every degree `d` the transitions of
the mapping cones of the components of `α` over some number of steps vanish on `H^d`.  Then `α`
has uniform inverses in `D(𝒜)`. -/
theorem hasUniformInverses_whiskerRight_Q (a b e : ℤ) (hea : e < a)
    (hYge : ∀ n, (Q.obj (Y.obj n)).IsGE a) (hYle : ∀ n, (Q.obj (Y.obj n)).IsLE b)
    (hXle : ∀ n, (Q.obj (X.obj n)).IsLE b)
    (htail : ∃ c₀ : ℕ, ∀ n m : ℕ, (h : n ≤ m) → n + c₀ ≤ m → ∀ (W : DerivedCategory 𝒜),
      W.IsLE e → ∀ g : W ⟶ Q.obj (X.obj (op m)), g ≫ Q.map (tr X h) = 0)
    (hcone : ∀ d : ℤ, ∃ c : ℕ, ∀ n : ℕ, (homologyFunctor 𝒜 d).map
      (tr (coneTriangleSystem α) (Nat.le_add_right n c)).hom₃ = 0) :
    HasUniformInverses (Functor.whiskerRight α Q) := by
  let T := coneTriangleSystem α
  let Z := T ⋙ Triangle.π₃
  have hT : ∀ n, T.obj n ∈ distTriang (DerivedCategory 𝒜) := coneTriangleSystem_distinguished α
  obtain ⟨c₀, hc₀⟩ := htail
  have hZ : ∀ n, (Z.obj n).IsLE b := by
    intro n
    have : t.IsLE ((T.obj n).obj₁) b := hXle n
    have h₃ : t.IsLE ((T.obj n).obj₁⟦(1 : ℤ)⟧) b := by
      have : t.IsLE ((T.obj n).obj₁⟦(1 : ℤ)⟧) (b - 1) := t.isLE_shift _ b 1 (b - 1) (by omega)
      exact t.isLE_of_le _ (b - 1) b (by omega)
    exact t.isLE₂ _ (rot_of_distTriang _ (hT n)) b (hYle n) h₃
  obtain ⟨C, hC⟩ := exists_cone_homology_eq_zero_of_finite α hcone e (b - e).toNat
  have htailZ : ∀ n, 0 ≤ n → ∀ (W : DerivedCategory 𝒜), W.IsLE (e - 1) →
      ∀ g : W ⟶ Z.obj (op (n + c₀)), g ≫ tr Z (Nat.le_add_right n c₀) = 0 := by
    intro n _ W hW g
    let g₀ : W ⟶ (T.obj (op (n + c₀))).obj₃ := g
    change g₀ ≫ (tr T (Nat.le_add_right n c₀)).hom₃ = 0
    have h₃ : (g₀ ≫ (tr T (Nat.le_add_right n c₀)).hom₃) ≫ (T.obj (op n)).mor₃ = 0 := by
      rw [Category.assoc, ← (tr T (Nat.le_add_right n c₀)).comm₃, ← Category.assoc]
      exact comp_shift_map_eq_zero _ e (fun W hW g => hc₀ n (n + c₀) _ le_rfl W hW g) W hW _
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ _ (hT _) _ h₃
    have : (T.obj (op n)).obj₂.IsGE a := hYge (op n)
    rw [hg', t.zero_of_isLE_of_isGE g' (e - 1) a (by omega) hW this, zero_comp]
  have hzero := tr_eq_zero_of_homology Z b (e - 1) 0 C c₀ (fun n _ => hZ (op n))
    (fun d _ _ n _ => hC d (by omega) (by omega) n) htailZ
  let S := c₀ + (b - (e - 1)).toNat * C
  refine ⟨2 * S, fun n m hm => ?_⟩
  have h₁ : n + S ≤ m := by omega
  have h₂ : n ≤ n + S := Nat.le_add_right n S
  -- two composable morphisms of triangles out of a distinguished one, both vanishing on the
  -- third terms, give an inverse of the first morphism of the last triangle up to them
  have key : ∀ {T₁ T₂ T₃ : Triangle (DerivedCategory 𝒜)} (_ : T₂ ∈ distTriang _)
      (ψ : T₁ ⟶ T₂) (φ : T₂ ⟶ T₃), ψ.hom₃ = 0 → φ.hom₃ = 0 →
      ∃ s : T₁.obj₂ ⟶ T₃.obj₁, T₁.mor₁ ≫ s = ψ.hom₁ ≫ φ.hom₁ ∧
        s ≫ T₃.mor₁ = ψ.hom₂ ≫ φ.hom₂ := by
    intro T₁ T₂ T₃ hT₂ ψ φ hψ hφ
    obtain ⟨s, hs⟩ : ∃ s : T₂.obj₂ ⟶ T₃.obj₁, φ.hom₁ = T₂.mor₁ ≫ s := by
      have hrot : Triangle.mk T₂.mor₂ T₂.mor₃ (-(T₂.mor₁⟦(1 : ℤ)⟧')) ∈ distTriang _ :=
        rot_of_distTriang _ hT₂
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hrot (φ.hom₁⟦(1 : ℤ)⟧')
        (by change T₂.mor₃ ≫ _ = 0; rw [φ.comm₃, hφ, zero_comp])
      refine ⟨(shiftFunctor _ (1 : ℤ)).preimage (-g), (shiftFunctor _ (1 : ℤ)).map_injective ?_⟩
      rw [Functor.map_comp, Functor.map_preimage, hg]
      simp only [Triangle.mk_mor₃, Preadditive.comp_neg, Preadditive.neg_comp]
    refine ⟨ψ.hom₂ ≫ s, by rw [ψ.comm₁_assoc, ← hs], ?_⟩
    rw [Category.assoc, ← sub_eq_zero, ← Preadditive.comp_sub]
    obtain ⟨t', ht'⟩ := Triangle.yoneda_exact₂ _ hT₂ (s ≫ T₃.mor₁ - φ.hom₂)
      (by rw [Preadditive.comp_sub, ← Category.assoc, ← hs, φ.comm₁, sub_self])
    rw [ht', ← ψ.comm₂_assoc, hψ, zero_comp, comp_zero]
  obtain ⟨s, hs₁, hs₂⟩ := key (hT (op (n + S)))
    (tr T h₁) (tr T h₂) (hzero (n + S) m (Nat.zero_le _) h₁ (by omega))
    (hzero n (n + S) (Nat.zero_le _) h₂ (by omega))
  refine ⟨s, h₂.trans h₁, hs₁.trans ?_, hs₂.trans ?_⟩
  · exact (Q.map_comp _ _).symm.trans (congrArg Q.map (tr_comp X h₂ h₁))
  · exact (Q.map_comp _ _).symm.trans (congrArg Q.map (tr_comp Y h₂ h₁))

end Criterion

end DerivedCategory

end
