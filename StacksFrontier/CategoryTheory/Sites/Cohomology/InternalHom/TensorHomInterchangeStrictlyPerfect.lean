module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeUnitSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalDegreeFamily

/-!
# The interchange morphism at a strictly perfect source

Let `X` be a ringed site and let `A`, `I` be complexes of `O`-modules. This file completes the
proof that the interchange morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is a quasi-isomorphism whenever `N` is **strictly perfect**: bounded, with every term a direct
summand of a finite free `O`-module. That is the step the source of Stacks 0ATN calls clear, and
it is the last input its reduction needs on this side.

The argument follows
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso`, which
runs it for the induced map of internal Hom complexes, step for step:

* the trivialised single-degree case is
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_unit`, where the interchange is
  in fact an isomorphism;
* a single degree carrying a power `O^{⊕r}` follows by induction on `r` along the degreewise
  split short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`;
* a single degree carrying a direct summand of a finite free module is a retract of that;
* a bounded complex follows by induction on the width of the window, splitting off the bottom
  term.

The one step with no counterpart in the model file is the **degreewise splitting of the row**
`Tot(A ⊗_O SheafHom(−, I))`. In the model the corresponding row is a product over the degrees of
the Hom source and its splitting is `internalHomTermwiseSplitting`; here it is a total complex,
whose degree `n` is a coproduct over `p + q = n`, so the splitting has to be assembled from the
summands. That is what `AlgebraicGeometry.RingedSite.tensorTotalDegreeFamilyMap` is for, and the
assembly is `AlgebraicGeometry.RingedSite.tensorTotalTermwiseSplitting`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalShortComplex`: the row obtained by applying
  `Tot(A ⊗_O −)` to a short complex of complexes.
* `AlgebraicGeometry.RingedSite.tensorTotalTermwiseSplitting`: its degreewise splitting, given
  one of the original short complex.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalShortComplex_shortExact`: a degreewise split short
  complex of complexes stays short exact after `Tot(A ⊗_O −)`.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_degreewiseSplit`: two out of
  three for the interchange morphism along a degreewise split short complex of sources.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_single_quasiIso_of_unitPower` and
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_single_quasiIso_of_isFiniteFreeSummand`:
  the single-degree cases. The second discharges the hypothesis of
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_single_of_isFiniteFreeSummand`.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_bounded` and
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`: **the
  bounded and the strictly perfect cases.** The second is the goal of the file.

## Implementation notes

The splitting axioms are stated as three separate lemmas before the splitting itself, at the
types of the total complexes rather than at the types of the mapped short complex, because the
two are not equal at `implicit` transparency and a rewrite inside the structure instance is
refused. This is the same arrangement as `internalHomTermwiseSplitting` and its three lemmas.

The finite biproducts of sheaves of modules are needed for `unitPower`; the instance is the
file-local one of the model file, switched on here as it is there.

## References

* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})

/-- The zero morphism of sheaves of modules sends every local section to zero. -/
private lemma zero_val_app_apply₅
    {P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (W : X.Cᵒᵖ) (x : P.val.obj W) : ((0 : P ⟶ Q).val.app W) x = 0 := rfl

variable (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-! ### The row of total complexes and its splitting -/

/-- The total tensor-product morphism of the identity and a zero morphism vanishes: it vanishes
on every homogeneous local pure tensor. -/
lemma tensorTotalMap_zero_right
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} :
    tensorTotalMap X (𝟙 A) (0 : B ⟶ B') = 0 := by
  refine tensorTotal_hom_ext X fun U t r a b ↦ ?_
  refine Eq.trans (tensorTotalMap_tensorTotalSection X (𝟙 A) 0 U t r a b) ?_
  refine Eq.trans (congrArg (tensorTotalSection X A B' U t r
    ((HomologicalComplex.Hom.f (𝟙 A) t).val.app (op U) a)) (zero_val_app_apply₅ X (op U) b)) ?_
  exact (tensorTotalSection_zero_right X A B' U t r _).trans
    (zero_val_app_apply₅ X (op U) _).symm

/-- **The row obtained by tensoring a short complex of complexes with `A` and taking total
complexes.** -/
def tensorTotalShortComplex
    (T : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)) :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (tensorTotalMap X (𝟙 A) T.f) (tensorTotalMap X (𝟙 A) T.g) (by
    rw [tensorTotalMap_comp, Category.comp_id, T.zero, tensorTotalMap_zero_right])

variable (T : ShortComplex
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (σ : ∀ q : ℤ, (T.map (HomologicalComplex.eval _ _ q)).Splitting)

/-- The family map of a family of identities is the identity. -/
private lemma tensorTotalDegreeFamilyMap_of_eq_id
    {B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : ∀ q, B.X q ⟶ B.X q) (hg : ∀ q, g q = 𝟙 (B.X q)) (n : ℤ) :
    tensorTotalDegreeFamilyMap X A g n = 𝟙 ((tensorTotal X A B).X n) :=
  (congrArg (fun g => tensorTotalDegreeFamilyMap X A g n) (funext hg)).trans
    (tensorTotalDegreeFamilyMap_id X A n)

/-- A degreewise retraction of `T.f` induces a retraction of the row of total complexes in each
total degree. -/
lemma tensorTotalMap_f_comp_degreeFamilyMap (rr : ∀ q, T.X₂.X q ⟶ T.X₁.X q)
    (hr : ∀ q, T.f.f q ≫ rr q = 𝟙 (T.X₁.X q)) (n : ℤ) :
    (tensorTotalMap X (𝟙 A) T.f).f n ≫ tensorTotalDegreeFamilyMap X A rr n =
      𝟙 ((tensorTotal X A T.X₁).X n) := by
  rw [tensorTotalMap_comp_tensorTotalDegreeFamilyMap]
  exact tensorTotalDegreeFamilyMap_of_eq_id X A _ hr n

/-- A degreewise section of `T.g` induces a section of the row of total complexes in each total
degree. -/
lemma degreeFamilyMap_comp_tensorTotalMap_g (ss : ∀ q, T.X₃.X q ⟶ T.X₂.X q)
    (hs : ∀ q, ss q ≫ T.g.f q = 𝟙 (T.X₃.X q)) (n : ℤ) :
    tensorTotalDegreeFamilyMap X A ss n ≫ (tensorTotalMap X (𝟙 A) T.g).f n =
      𝟙 ((tensorTotal X A T.X₃).X n) := by
  rw [tensorTotalDegreeFamilyMap_comp_tensorTotalMap]
  exact tensorTotalDegreeFamilyMap_of_eq_id X A _ hs n

/-- The degreewise retraction and section of a splitting of `T` add up to the identity after
`Tot(A ⊗_O −)`, in each total degree. -/
lemma degreeFamilyMap_splitting_id (rr : ∀ q, T.X₂.X q ⟶ T.X₁.X q)
    (ss : ∀ q, T.X₃.X q ⟶ T.X₂.X q)
    (h : ∀ q, rr q ≫ T.f.f q + T.g.f q ≫ ss q = 𝟙 (T.X₂.X q)) (n : ℤ) :
    tensorTotalDegreeFamilyMap X A rr n ≫ (tensorTotalMap X (𝟙 A) T.f).f n +
        (tensorTotalMap X (𝟙 A) T.g).f n ≫ tensorTotalDegreeFamilyMap X A ss n =
      𝟙 ((tensorTotal X A T.X₂).X n) := by
  rw [tensorTotalDegreeFamilyMap_comp_tensorTotalMap,
    tensorTotalMap_comp_tensorTotalDegreeFamilyMap, ← tensorTotalDegreeFamilyMap_add]
  exact tensorTotalDegreeFamilyMap_of_eq_id X A _ h n

/-- **In each total degree the row of total complexes is split**, the splitting being the
degreewise family map of the given splitting of the second factor. -/
def tensorTotalTermwiseSplitting (n : ℤ) :
    ((tensorTotalShortComplex X A T).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := tensorTotalDegreeFamilyMap X A (fun q => show T.X₂.X q ⟶ T.X₁.X q from (σ q).r) n
  s := tensorTotalDegreeFamilyMap X A (fun q => show T.X₃.X q ⟶ T.X₂.X q from (σ q).s) n
  f_r := tensorTotalMap_f_comp_degreeFamilyMap X A T _ (fun q => (σ q).f_r) n
  s_g := degreeFamilyMap_comp_tensorTotalMap_g X A T _ (fun q => (σ q).s_g) n
  id := degreeFamilyMap_splitting_id X A T _ _ (fun q => (σ q).id) n

/-- **A degreewise split short complex of complexes stays short exact after `Tot(A ⊗_O −)`**,
being degreewise split there too. -/
lemma tensorTotalShortComplex_shortExact
    (T' : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ' : ∀ q : ℤ, (T'.map (HomologicalComplex.eval _ _ q)).Splitting) :
    (tensorTotalShortComplex X A T').ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (tensorTotalTermwiseSplitting X A T' σ' n).shortExact)

/-! ### The induction -/

variable (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Two out of three for a degreewise split short complex of sources.** The interchange
morphism is a morphism of short complexes from the row of its sources, which is short exact by
`tensorTotalShortComplex_shortExact`, to the row of its targets, which is short exact by
`internalHomTermwiseSplitting`; two out of three in the middle is
`StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂`. -/
theorem tensorHomInterchange_quasiIso_of_degreewiseSplit
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σs : ∀ q : ℤ, (S.map (HomologicalComplex.eval _ _ q)).Splitting)
    [QuasiIso (tensorHomInterchange X A I S.X₁)]
    [QuasiIso (tensorHomInterchange X A I S.X₃)] :
    QuasiIso (tensorHomInterchange X A I S.X₂) := by
  let φ : tensorTotalShortComplex X A (internalHomShortComplex X S I) ⟶
      internalHomShortComplex X S (tensorTotal X A I) :=
    { τ₁ := tensorHomInterchange X A I S.X₃
      τ₂ := tensorHomInterchange X A I S.X₂
      τ₃ := tensorHomInterchange X A I S.X₁
      comm₁₂ := by
        dsimp [tensorTotalShortComplex, internalHomShortComplex]
        rw [← tensorHomInterchange_natural X (𝟙 A) (𝟙 I) S.g, tensorTotalMap_id]
      comm₂₃ := by
        dsimp [tensorTotalShortComplex, internalHomShortComplex]
        rw [← tensorHomInterchange_natural X (𝟙 A) (𝟙 I) S.f, tensorTotalMap_id] }
  have h1 : QuasiIso φ.τ₁ := ‹QuasiIso (tensorHomInterchange X A I S.X₃)›
  have h3 : QuasiIso φ.τ₃ := ‹QuasiIso (tensorHomInterchange X A I S.X₁)›
  exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ φ
    (tensorTotalShortComplex_shortExact X A (internalHomShortComplex X S I)
      (internalHomTermwiseSplitting X S I σs))
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X S (tensorTotal X A I) σs n).shortExact))

/-- **The single-degree finite free case**, by induction on the rank along the degreewise split
short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`. The base of the induction is the vanishing case and
the third term is always the trivialised case. -/
theorem tensorHomInterchange_single_quasiIso_of_unitPower (k : ℤ) (r : ℕ) :
    QuasiIso (tensorHomInterchange X A I
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj (unitPower X r))) := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  have hone : QuasiIso (tensorHomInterchange X A I
      (Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
    tensorHomInterchange_quasiIso_of_unit X A I k (HomologicalComplex.singleObjXSelf _ k _)
      fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ p hp
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact tensorHomInterchange_quasiIso_of_isZero X A I (Sg.map_isZero (isZero_zero _))
  | succ r ih =>
    rw [unitPower_succ]
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _
    have h1 : QuasiIso (tensorHomInterchange X A I T.X₁) := ih
    have h3 : QuasiIso (tensorHomInterchange X A I T.X₃) := hone
    exact tensorHomInterchange_quasiIso_of_degreewiseSplit X A I T hT

/-- **The single-degree case for a direct summand of a finite free module**, which discharges
the hypothesis left open by
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_single_of_isFiniteFreeSummand`. -/
theorem tensorHomInterchange_single_quasiIso_of_isFiniteFreeSummand
    (k : ℤ) {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    QuasiIso (tensorHomInterchange X A I
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj M)) :=
  tensorHomInterchange_quasiIso_single_of_isFiniteFreeSummand X A I k hM
    (tensorHomInterchange_single_quasiIso_of_unitPower X A I k)

/-- **The bounded case.** If `N` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free `O`-module, then the interchange morphism at `N` is a
quasi-isomorphism. The induction is on the width of the window, splitting off the bottom term as
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_bounded` does. -/
theorem tensorHomInterchange_quasiIso_of_bounded (r : ℕ) (a : ℤ)
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (N.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (N.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (N.X i)) :
    QuasiIso (tensorHomInterchange X A I N) := by
  induction r generalizing a N with
  | zero =>
    refine tensorHomInterchange_quasiIso_of_isZero X A I
      (complex_isZero_of_terms N fun i => ?_)
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (N.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection N a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self N a ha
    have hKterm (i : ℤ) : IsFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsFiniteFreeSummand.of_isZero X hz
      · have := isIso_kernel_ι_bottomProjection_f N a ha i hi
        exact IsFiniteFreeSummand.of_iso X (asIso ((kernel.ι p).f i)) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · have := isIso_kernel_ι_bottomProjection_f N a ha i hia
        exact IsZero.of_iso (hlo i (by omega)) (asIso ((kernel.ι p).f i))
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) := by
      have := isIso_kernel_ι_bottomProjection_f N a ha i (by omega)
      exact IsZero.of_iso (hhi i (by push_cast; omega)) (asIso ((kernel.ι p).f i))
    have hKq : QuasiIso (tensorHomInterchange X A I K) := ih (a + 1) K hKlo hKhi hKterm
    have hAq : QuasiIso (tensorHomInterchange X A I
        ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (N.X a))) :=
      tensorHomInterchange_single_quasiIso_of_isFiniteFreeSummand X A I a (hterm a)
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine tensorHomInterchange_quasiIso_of_degreewiseSplit X A I T (fun i => ?_)
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self N a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_kernel_ι_bottomProjection_f N a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (N.X a) i hi)

/-- **The strictly perfect case: the interchange morphism of Stacks 0BYR is a quasi-isomorphism
at a strictly perfect source.** If `N` has only finitely many nonzero terms and each of them is
a direct summand of a finite free `O`-module, then

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is a quasi-isomorphism, for arbitrary `A` and `I`. This is the step the source of Stacks 0ATN
calls clear. -/
theorem tensorHomInterchange_quasiIso_of_isFiniteFreeSummand
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (N.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (N.X i)) :
    QuasiIso (tensorHomInterchange X A I N) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine tensorHomInterchange_quasiIso_of_bounded X A I (b - a + 1).toNat a N ?_ ?_ hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

end AlgebraicGeometry.RingedSite

end
