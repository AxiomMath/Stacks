module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.PresheavesOfModulesComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Homology of the Čech chain complex of presheaves

The augmented Čech chain complex of an open covering is exact on every open set.
Consequently its positive-degree homology presheaves vanish, and its degree-zero
homology is the image presheaf of the augmentation to the structure presheaf.

All names are in the namespace `Stacks.Cohomology.CechImagePresheaf`.

## Main definitions

* `augmentationApp`: the canonical map from the degree-zero term to the structure ring on an
  open set.
* `imagePresheaf`: its image presheaf, with induced restrictions.
* `homologyZeroIsoImage`: the canonical isomorphism, on each open, from degree-zero homology to
  the image presheaf.

## Main results

* `positive_exact`: the complex is exact in every positive degree.
* `augmentation_naturality`: the augmentation is a morphism of presheaves.
* `augmentation_ker`: the kernel of the augmentation is the image of the first differential.
* `homologyZeroIsoImage_naturality`: the degree-zero isomorphism commutes with restriction.

## Implementation notes

Homology is presented by objectwise quotients. The degree-zero isomorphism is characterized on
classes of elements and commutes with restriction, so it identifies presheaves, not only their
values on each open.

## References

* [Stacks Project, Tag 01EM](https://stacks.math.columbia.edu/tag/01EM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.CechImagePresheaf

open StacksCechPresheaf StacksCechPresheaf.ModPresheaf

variable {X : AlgebraicGeometry.RingedSpace} {I : Type u}

/-- The augmentation of the degree-zero Čech term on sections over `W`: each extension-by-zero
summand maps to the structure ring by inclusion, and the summands are added. -/
public noncomputable def augmentationApp (U : Cover X I) (W : Opens X.carrier) :
    (Kterm U 0).obj W →ₗ[sections X W] sections X W := by
  classical
  exact DirectSum.toModule (sections X W) (Fin 1 → I) (sections X W)
    (fun σ => (extZeroSub X (interOpens U σ) W).subtype)

/-! ### Values of the extension by zero -/

/-- The underlying section of a value of the extension by zero `(j_{p!} O_V)(W)`. -/
private noncomputable def extZeroVal (V W : Opens X.carrier) :
    (extZeroOX X V).obj W →ₗ[sections X W] sections X W := (extZeroSub X V W).subtype

private theorem extZeroVal_inj {V W : Opens X.carrier} {x y : (extZeroOX X V).obj W}
    (h : extZeroVal V W x = extZeroVal V W y) : x = y := Subtype.ext h

private theorem extZeroVal_eq_zero {V W : Opens X.carrier} (hW : ¬ W ≤ V)
    (x : (extZeroOX X V).obj W) : extZeroVal V W x = 0 :=
  mem_extZeroSub_of_not_le hW (extZeroVal V W x) x.2

private theorem extZeroVal_res (V : Opens X.carrier) {W W' : Opens X.carrier} (h : W ≤ W')
    (x : (extZeroOX X V).obj W') :
    extZeroVal V W ((extZeroOX X V).res h x) =
      (X.presheaf.map (homOfLE h).op) (extZeroVal V W' x) := rfl

/-- The canonical inclusion of extensions by zero, typed by the bundled presheaf values. -/
private noncomputable def extZeroCanon {V V' : Opens X.carrier} (h : V ≤ V')
    (W : Opens X.carrier) :
    (extZeroOX X V).obj W →ₗ[sections X W] (extZeroOX X V').obj W := extZeroCanonicalApp h W

private theorem extZeroVal_canon {V V' : Opens X.carrier} (h : V ≤ V') (W : Opens X.carrier)
    (x : (extZeroOX X V).obj W) :
    extZeroVal V' W (extZeroCanon h W x) = extZeroVal V W x := rfl

/-! ### The degree-zero term and its augmentation -/

open Classical in
/-- The augmentation with the direct sum itself, rather than `(Kterm U 0).obj W`, as domain. -/
private noncomputable def augApp (U : Cover X I) (W : Opens X.carrier) :
    KtermObj U 0 W →ₗ[sections X W] sections X W :=
  DirectSum.toModule (sections X W) (Fin (0 + 1) → I) (sections X W)
    (fun σ => extZeroVal (interOpens U σ) W)

open Classical in
private theorem augApp_lof (U : Cover X I) (W : Opens X.carrier) (σ : Fin (0 + 1) → I)
    (y : (extZeroOX X (interOpens U σ)).obj W) :
    augApp U W (DirectSum.lof (sections X W) (Fin (0 + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ y) =
      extZeroVal (interOpens U σ) W y := by
  rw [augApp, DirectSum.toModule_lof]

open Classical in
/-- Induction over the generators of `K(U)_p(W)`, phrased with `DirectSum.lof`. -/
@[elab_as_elim]
private theorem KtermObj_induction (U : Cover X I) (p : ℕ) (W : Opens X.carrier)
    {motive : KtermObj U p W → Prop} (x : KtermObj U p W) (hzero : motive 0)
    (hlof : ∀ (σ : Fin (p + 1) → I) (y : (extZeroOX X (interOpens U σ)).obj W),
      motive (DirectSum.lof (sections X W) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ y))
    (hadd : ∀ a b, motive a → motive b → motive (a + b)) : motive x :=
  DirectSum.induction_on x hzero hlof hadd

open Classical in
private theorem Kterm_map_lof (U : Cover X I) (p : ℕ) {W W' : Opens X.carrier} (h : W ≤ W')
    (σ : Fin (p + 1) → I) (y : (extZeroOX X (interOpens U σ)).obj W') :
    DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom h)
        (DirectSum.lof (sections X W') (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W') σ y) =
      DirectSum.lof (sections X W) (Fin (p + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ
        ((extZeroOX X (interOpens U σ)).res h y) :=
  DirectSum.map_of (fun τ => (extZeroOX X (interOpens U τ)).resHom h) σ y

open Classical in
private theorem augApp_res (U : Cover X I) {W W' : Opens X.carrier} (h : W ≤ W')
    (x : KtermObj U 0 W') :
    augApp U W (DirectSum.map (fun τ => (extZeroOX X (interOpens U τ)).resHom h) x) =
      (X.presheaf.map (homOfLE h).op) (augApp U W' x) := by
  refine KtermObj_induction U 0 W' x ?_ ?_ ?_
  · simp only [map_zero]
  · intro σ y
    rw [Kterm_map_lof, augApp_lof, augApp_lof, extZeroVal_res]
  · intro a b ha hb
    simp only [_root_.map_add, ha, hb]

/-- The sectionwise augmentations commute with restriction, so their ranges form the image presheaf
inside the structure presheaf. -/
public theorem augmentation_naturality (U : Cover X I)
    {W W' : Opens X.carrier} (h : W ≤ W') (x : (Kterm U 0).obj W') :
    augmentationApp U W ((Kterm U 0).res h x) =
      (X.presheaf.map (homOfLE h).op) (augmentationApp U W' x) := by
  classical
  exact augApp_res U h x

/-- The image of the augmentation as a presheaf of modules inside the structure presheaf. -/
public noncomputable def imagePresheaf (U : Cover X I) : ModPresheaf X where
  obj W := LinearMap.range (augmentationApp U W)
  addCommGroup W := inferInstance
  module W := inferInstance
  res {W W'} h x := ⟨(X.presheaf.map (homOfLE h).op) x.1, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨(Kterm U 0).res h y, by rw [augmentation_naturality U h y, hy]⟩⟩
  map_smul {W W'} h r x := by
    apply Subtype.ext
    change (X.presheaf.map (homOfLE h).op) (r * x.1) =
      (X.presheaf.map (homOfLE h).op r) * (X.presheaf.map (homOfLE h).op) x.1
    exact map_mul _ _ _
  map_add {W W'} h x y := Subtype.ext (map_add _ _ _)
  res_id {W} x := by
    apply Subtype.ext
    change (X.presheaf.map (homOfLE (le_refl W)).op) x.1 = x.1
    simp
  res_comp {W W' W''} h h' x := by
    apply Subtype.ext
    change (X.presheaf.map (homOfLE (h.trans h')).op) x.1 =
      (X.presheaf.map (homOfLE h).op)
        ((X.presheaf.map (homOfLE h').op) x.1)
    rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
    rfl

add_to_stacks 01EM imagePresheaf

/-! ### Prepending an index to a tuple -/

private theorem le_interOpens_cons (U : Cover X I) (W : Opens X.carrier)
    {n : ℕ} (i : I) (σ : Fin (n + 1) → I) (hi : W ≤ U.obj i)
    (hσ : W ≤ interOpens U σ) :
    W ≤ interOpens U (Fin.cons i σ) := by
  refine le_iInf fun k => Fin.cases ?_ (fun k => ?_) k
  · simpa [interOpens, Fin.cons] using hi
  · simpa [interOpens, Fin.cons] using (le_iInf_iff.mp hσ k)

private theorem prepend_mem (U : Cover X I) (W : Opens X.carrier)
    {n : ℕ} (i : I) (hi : W ≤ U.obj i) (σ : Fin (n + 1) → I)
    (x : (extZeroOX X (interOpens U σ)).obj W) :
    extZeroVal (interOpens U σ) W x ∈ extZeroSub X (interOpens U (Fin.cons i σ)) W := by
  by_cases hσ : W ≤ interOpens U σ
  · rw [extZeroSub_eq_top (le_interOpens_cons U W i σ hi hσ)]
    trivial
  · rw [extZeroVal_eq_zero hσ x]
    exact Submodule.zero_mem _

/-- Prepending the index `i` to `σ`: on an open `W` contained in `U_i` the summand
`(j_σ)_{p!} O_{U_σ}` maps isomorphically onto `(j_{iσ})_{p!} O_{U_{iσ}}`. -/
private noncomputable def prependComponent (U : Cover X I) (W : Opens X.carrier)
    {n : ℕ} (i : I) (hi : W ≤ U.obj i) (σ : Fin (n + 1) → I) :
    (extZeroOX X (interOpens U σ)).obj W →ₗ[sections X W]
      (extZeroOX X (interOpens U (Fin.cons i σ))).obj W :=
  LinearMap.codRestrict (extZeroSub X (interOpens U (Fin.cons i σ)) W)
    (extZeroVal (interOpens U σ) W) (prepend_mem U W i hi σ)

private theorem extZeroVal_prepend (U : Cover X I) (W : Opens X.carrier)
    {n : ℕ} (i : I) (hi : W ≤ U.obj i) (σ : Fin (n + 1) → I)
    (x : (extZeroOX X (interOpens U σ)).obj W) :
    extZeroVal (interOpens U (Fin.cons i σ)) W (prependComponent U W i hi σ x) =
      extZeroVal (interOpens U σ) W x := rfl

open Classical in
private noncomputable def prependChainMap (U : Cover X I) (W : Opens X.carrier)
    (n : ℕ) (i : I) (hi : W ≤ U.obj i) :
    KtermObj U n W →ₗ[sections X W] KtermObj U (n + 1) W :=
  DirectSum.toModule (sections X W) (Fin (n + 1) → I) (KtermObj U (n + 1) W)
    (fun σ => (DirectSum.lof (sections X W) (Fin (n + 1 + 1) → I)
      (fun τ => (extZeroOX X (interOpens U τ)).obj W) (Fin.cons i σ)).comp
        (prependComponent U W i hi σ))

open Classical in
private theorem prependChainMap_lof (U : Cover X I) (W : Opens X.carrier)
    (n : ℕ) (i : I) (hi : W ≤ U.obj i) (σ : Fin (n + 1) → I)
    (y : (extZeroOX X (interOpens U σ)).obj W) :
    prependChainMap U W n i hi
        (DirectSum.lof (sections X W) (Fin (n + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ y) =
      DirectSum.lof (sections X W) (Fin (n + 1 + 1) → I)
        (fun τ => (extZeroOX X (interOpens U τ)).obj W) (Fin.cons i σ)
        (prependComponent U W i hi σ y) := by
  rw [prependChainMap, DirectSum.toModule_lof, LinearMap.comp_apply]

/-! ### Faces of a prepended tuple -/

private theorem omit_cons_zero {n : ℕ} (i : I) (σ : Fin (n + 1) → I) :
    omitIdx (Fin.cons i σ) (0 : Fin (n + 2)) = σ := by
  funext k
  simp [omitIdx, Fin.cons]

private theorem omit_cons_succ {n : ℕ} (i : I) (σ : Fin (n + 1 + 1) → I)
    (j : Fin (n + 1 + 1)) :
    omitIdx (Fin.cons i σ) j.succ = Fin.cons i (omitIdx σ j) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp [omitIdx, Fin.cons]
  · intro k
    simp [omitIdx, Fin.cons]

open Classical in
/-- Omitting the first index of a prepended tuple undoes the prepending. The index of the summand
is passed as the variable `τ` so that the statement is free of transport. -/
private theorem prepend_face_zero (U : Cover X I) (W : Opens X.carrier)
    {m : ℕ} (i : I) (hi : W ≤ U.obj i) (σ : Fin (m + 1) → I)
    {τ : Fin (m + 1) → I} (hτ : τ = σ)
    (hle : interOpens U (Fin.cons i σ) ≤ interOpens U τ)
    (y : (extZeroOX X (interOpens U σ)).obj W) :
    DirectSum.lof (sections X W) (Fin (m + 1) → I)
        (fun ρ => (extZeroOX X (interOpens U ρ)).obj W) τ
        (extZeroCanon hle W (prependComponent U W i hi σ y)) =
      DirectSum.lof (sections X W) (Fin (m + 1) → I)
        (fun ρ => (extZeroOX X (interOpens U ρ)).obj W) σ y := by
  subst τ
  have hv : extZeroCanon hle W (prependComponent U W i hi σ y) = y :=
    extZeroVal_inj ((extZeroVal_canon hle W _).trans (extZeroVal_prepend U W i hi σ y))
  rw [hv]

open Classical in
/-- Omitting a later index of a prepended tuple is prepending to the corresponding face. -/
private theorem prepend_face_succ (U : Cover X I) (W : Opens X.carrier)
    {m : ℕ} (i : I) (hi : W ≤ U.obj i) (σ : Fin (m + 1 + 1) → I) (j : Fin (m + 1 + 1))
    {τ : Fin (m + 1 + 1) → I} (hτ : τ = Fin.cons i (omitIdx σ j))
    (hle : interOpens U (Fin.cons i σ) ≤ interOpens U τ)
    (y : (extZeroOX X (interOpens U σ)).obj W) :
    DirectSum.lof (sections X W) (Fin (m + 1 + 1) → I)
        (fun ρ => (extZeroOX X (interOpens U ρ)).obj W) τ
        (extZeroCanon hle W (prependComponent U W i hi σ y)) =
      DirectSum.lof (sections X W) (Fin (m + 1 + 1) → I)
        (fun ρ => (extZeroOX X (interOpens U ρ)).obj W) (Fin.cons i (omitIdx σ j))
        (prependComponent U W i hi (omitIdx σ j)
          (extZeroCanon (interOpens_le_omitIdx U σ j) W y)) := by
  subst hτ
  have hv : extZeroCanon hle W (prependComponent U W i hi σ y) =
      prependComponent U W i hi (omitIdx σ j)
        (extZeroCanon (interOpens_le_omitIdx U σ j) W y) :=
    extZeroVal_inj (by
      rw [extZeroVal_canon, extZeroVal_prepend, extZeroVal_prepend, extZeroVal_canon])
  rw [hv]

/-! ### The differential on generators -/

open Classical in
private theorem KdiffSummand_eq (U : Cover X I) (p : ℕ) (W : Opens X.carrier)
    (σ : Fin (p + 1 + 1) → I) :
    KdiffSummand U p W σ =
      ∑ j : Fin (p + 1 + 1), (-1 : ℤ) ^ (j : ℕ) •
        (DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)).comp
            (extZeroCanon (interOpens_le_omitIdx U σ j) W) := rfl

open Classical in
private theorem KdiffSummand_apply (U : Cover X I) (p : ℕ) (W : Opens X.carrier)
    (σ : Fin (p + 1 + 1) → I) (y : (extZeroOX X (interOpens U σ)).obj W) :
    KdiffSummand U p W σ y =
      ∑ j : Fin (p + 1 + 1), (-1 : ℤ) ^ (j : ℕ) •
        DirectSum.lof (sections X W) (Fin (p + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) (omitIdx σ j)
          (extZeroCanon (interOpens_le_omitIdx U σ j) W y) := by
  rw [KdiffSummand_eq, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [LinearMap.smul_apply, LinearMap.comp_apply]

open Classical in
private theorem KdiffApp_lof (U : Cover X I) (p : ℕ) (W : Opens X.carrier)
    (σ : Fin (p + 1 + 1) → I) (y : (extZeroOX X (interOpens U σ)).obj W) :
    KdiffApp U p W
        (DirectSum.lof (sections X W) (Fin (p + 1 + 1) → I)
          (fun τ => (extZeroOX X (interOpens U τ)).obj W) σ y) =
      KdiffSummand U p W σ y := by
  rw [KdiffApp, DirectSum.toModule_lof]

private theorem linearMap_map_zsmul {R M N : Type*} [Semiring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (k : ℤ) (x : M) : f (k • x) = k • f x :=
  f.toAddMonoidHom.map_zsmul k x

private theorem neg_one_pow_succ (m : ℕ) (j : Fin (m + 1)) :
    (-1 : ℤ) ^ ((j.succ : Fin (m + 1 + 1)) : ℕ) = -((-1 : ℤ) ^ (j : ℕ)) := by
  simp only [Fin.val_succ, pow_succ]
  ring

/-! ### The contracting homotopy in positive degrees -/

private theorem prepend_homotopy (U : Cover X I) (W : Opens X.carrier)
    (n : ℕ) (i : I) (hi : W ≤ U.obj i) :
    (KdiffApp U (n + 1) W).comp (prependChainMap U W (n + 1) i hi) +
      (prependChainMap U W n i hi).comp (KdiffApp U n W) = LinearMap.id := by
  classical
  refine LinearMap.ext fun x => KtermObj_induction U (n + 1) W x ?_ ?_ ?_
  · simp
  · intro σ y
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
      prependChainMap_lof, KdiffApp_lof, KdiffApp_lof, KdiffSummand_apply, KdiffSummand_apply,
      map_sum]
    simp_rw [linearMap_map_zsmul, prependChainMap_lof]
    have key := fun j : Fin (n + 1 + 1) =>
      prepend_face_succ U W i hi σ j (omit_cons_succ i σ j)
        (interOpens_le_omitIdx U (Fin.cons i σ) j.succ) y
    rw [Fin.sum_univ_succ]
    simp only [key, Fin.val_zero, pow_zero, one_smul]
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp only [neg_one_pow_succ, neg_smul, neg_add_cancel, Finset.sum_const_zero, add_zero]
    exact prepend_face_zero U W i hi σ (omit_cons_zero i σ) _ y
  · intro a b ha hb
    simp only [_root_.map_add, ha, hb]

private theorem KdiffApp_comp_zero (U : Cover X I) (p : ℕ) (W : Opens X.carrier) :
    (KdiffApp U p W).comp (KdiffApp U (p + 1) W) = 0 := by
  have hW := congrArg (fun f => ModPresheaf.Hom.app f W) (Kdiff_comp_Kdiff U p)
  have hcomp : ((Kdiff U p).app W).comp ((Kdiff U (p + 1)).app W) = 0 := by
    simpa [comp_app, zero_app] using hW
  exact hcomp

/-! ### The contracting homotopy in degree zero -/

private def oneTuple (i : I) : Fin 1 → I := fun _ => i

private theorem omit_cons_one (i : I) (σ : Fin 1 → I) :
    omitIdx (Fin.cons i σ) (Fin.succ (0 : Fin 1)) = oneTuple i := by
  funext k
  fin_cases k
  simp [omitIdx, Fin.cons, oneTuple]

private noncomputable def chosenSectionComponent (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) :
    sections X W →ₗ[sections X W]
      (extZeroOX X (interOpens U (oneTuple i))).obj W :=
  LinearMap.codRestrict (extZeroSub X (interOpens U (oneTuple i)) W) LinearMap.id
    (fun _ => by
      rw [extZeroSub_eq_top (by simpa [interOpens, oneTuple] using hi)]
      trivial)

private theorem extZeroVal_chosen (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) (s : sections X W) :
    extZeroVal (interOpens U (oneTuple i)) W (chosenSectionComponent U W i hi s) = s := rfl

open Classical in
private noncomputable def chosenSectionMap (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) :
    sections X W →ₗ[sections X W] KtermObj U 0 W :=
  (DirectSum.lof (sections X W) (Fin (0 + 1) → I)
    (fun σ => (extZeroOX X (interOpens U σ)).obj W) (oneTuple i)).comp
      (chosenSectionComponent U W i hi)

open Classical in
private theorem chosenSectionMap_apply (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) (s : sections X W) :
    chosenSectionMap U W i hi s =
      DirectSum.lof (sections X W) (Fin (0 + 1) → I)
        (fun σ => (extZeroOX X (interOpens U σ)).obj W) (oneTuple i)
        (chosenSectionComponent U W i hi s) := rfl

open Classical in
/-- In degree zero the second face of a prepended one-tuple is the chosen section. -/
private theorem prepend_degreeZero_tail (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) (σ : Fin (0 + 1) → I)
    {τ : Fin (0 + 1) → I} (hτ : τ = oneTuple i)
    (hle : interOpens U (Fin.cons i σ) ≤ interOpens U τ)
    (y : (extZeroOX X (interOpens U σ)).obj W) :
    DirectSum.lof (sections X W) (Fin (0 + 1) → I)
        (fun ρ => (extZeroOX X (interOpens U ρ)).obj W) τ
        (extZeroCanon hle W (prependComponent U W i hi σ y)) =
      chosenSectionMap U W i hi (extZeroVal (interOpens U σ) W y) := by
  subst hτ
  rw [chosenSectionMap_apply]
  have hv : extZeroCanon hle W (prependComponent U W i hi σ y) =
      chosenSectionComponent U W i hi (extZeroVal (interOpens U σ) W y) :=
    extZeroVal_inj (by rw [extZeroVal_canon, extZeroVal_prepend, extZeroVal_chosen])
  rw [hv]

private theorem augmentation_degreeZero_homotopy (U : Cover X I) (W : Opens X.carrier)
    (i : I) (hi : W ≤ U.obj i) (x : KtermObj U 0 W) :
    KdiffApp U 0 W (prependChainMap U W 0 i hi x) +
      chosenSectionMap U W i hi (augApp U W x) = x := by
  classical
  refine KtermObj_induction U 0 W x ?_ ?_ ?_
  · simp
  · intro σ y
    rw [prependChainMap_lof, KdiffApp_lof, KdiffSummand_apply, augApp_lof, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      prepend_degreeZero_tail U W i hi σ (omit_cons_one i σ) _ y]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one,
      neg_one_smul]
    rw [add_assoc, neg_add_cancel, add_zero]
    exact prepend_face_zero U W i hi σ (omit_cons_zero i σ) _ y
  · intro a b ha hb
    simp only [_root_.map_add]
    rw [add_add_add_comm, ha, hb]

private theorem augApp_KdiffApp_zero (U : Cover X I) (W : Opens X.carrier) :
    (augApp U W).comp (KdiffApp U 0 W) = 0 := by
  classical
  refine LinearMap.ext fun z => KtermObj_induction U (0 + 1) W z ?_ ?_ ?_
  · simp
  · intro σ y
    rw [LinearMap.comp_apply, KdiffApp_lof, KdiffSummand_apply, map_sum]
    simp_rw [linearMap_map_zsmul, augApp_lof, extZeroVal_canon]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp
  · intro a b ha hb
    simp only [_root_.map_add, ha, hb]

private theorem KtermObj_subsingleton_of_no_cover (U : Cover X I)
    (W : Opens X.carrier) (n : ℕ) (hnone : ∀ i : I, ¬ W ≤ U.obj i) :
    Subsingleton (KtermObj U n W) := by
  classical
  constructor
  intro a b
  have hzero (z : KtermObj U n W) : z = 0 := by
    refine KtermObj_induction U n W z ?_ ?_ ?_
    · rfl
    · intro σ y
      have hW : ¬ W ≤ interOpens U σ := fun hσ => hnone (σ 0) (le_iInf_iff.mp hσ 0)
      have hy : y = 0 := extZeroVal_inj (by rw [extZeroVal_eq_zero hW y, map_zero])
      rw [hy, map_zero]
    · intro a b ha hb
      rw [ha, hb, add_zero]
  rw [hzero a, hzero b]

/-! ### Exactness -/

/-- A submodule `T` of the degree-`n` term lies in `S` once this holds on each open `W` contained
in some `U_i`, since the term is trivial when no `U_i` contains `W`. -/
private theorem le_of_forall_active (U : Cover X I) (W : Opens X.carrier) (n : ℕ)
    (S T : Submodule (sections X W) (KtermObj U n W))
    (h : ∀ i : I, W ≤ U.obj i → ∀ x ∈ T, x ∈ S) : T ≤ S := by
  classical
  intro x hx
  by_cases hactive : ∃ i : I, W ≤ U.obj i
  · obtain ⟨i, hi⟩ := hactive
    exact h i hi x hx
  · have hx0 : x = 0 :=
      (KtermObj_subsingleton_of_no_cover U W n fun i hi => hactive ⟨i, hi⟩).elim x 0
    rw [hx0]
    exact S.zero_mem

private theorem positive_exact_aux (U : Cover X I) (p : ℕ) (W : Opens X.carrier) :
    LinearMap.range (KdiffApp U (p + 1) W) = LinearMap.ker (KdiffApp U p W) :=
  le_antisymm (LinearMap.range_le_ker_iff.mpr (KdiffApp_comp_zero U p W))
    (le_of_forall_active U W (p + 1) _ _ fun i hi x hx => by
      have hval := congrArg (fun f => f x) (prepend_homotopy U W p i hi)
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hval
      rw [LinearMap.mem_ker.mp hx, map_zero, add_zero] at hval
      exact ⟨prependChainMap U W (p + 1) i hi x, hval⟩)

/-- The Čech chain complex of an open covering is exact in every positive degree, objectwise on
opens. Equivalently all its positive-degree homology presheaves vanish. -/
@[stacks 01EM "positive-degree homology"]
public theorem positive_exact (U : Cover X I) (p : ℕ) (W : Opens X.carrier) :
    LinearMap.range ((Kdiff U (p + 1)).app W) =
      LinearMap.ker ((Kdiff U p).app W) := by
  classical
  exact positive_exact_aux U p W

private theorem augmentation_ker_aux (U : Cover X I) (W : Opens X.carrier) :
    LinearMap.ker (augApp U W) = LinearMap.range (KdiffApp U 0 W) :=
  le_antisymm
    (le_of_forall_active U W 0 _ _ fun i hi x hx => by
      have hhom := augmentation_degreeZero_homotopy U W i hi x
      rw [LinearMap.mem_ker.mp hx, map_zero, add_zero] at hhom
      exact ⟨prependChainMap U W 0 i hi x, hhom⟩)
    (LinearMap.range_le_ker_iff.mpr (augApp_KdiffApp_zero U W))

/-- The kernel of the canonical augmentation is the image of the first Čech differential. Thus
degree-zero homology is canonically the image presheaf of `K(U)₀ → O_X`, with its evident maps on
restrictions. -/
@[stacks 01EM "degree-zero homology"]
public theorem augmentation_ker (U : Cover X I) (W : Opens X.carrier) :
    LinearMap.ker (augmentationApp U W) =
      LinearMap.range ((Kdiff U 0).app W) := by
  classical
  exact augmentation_ker_aux U W

/-- The canonical identification of degree-zero homology with the image of the augmentation. Its
value on a homology class is the augmentation of a representative; this specification determines
the isomorphism uniquely. -/
@[stacks 01EM "canonical degree-zero identification"]
public noncomputable def homologyZeroIsoImage (U : Cover X I)
    (W : Opens X.carrier) :
    { e : (((Kterm U 0).obj W ⧸ LinearMap.range ((Kdiff U 0).app W)) ≃ₗ[sections X W]
        (imagePresheaf U).obj W) //
      ∀ x : (Kterm U 0).obj W,
        e ((LinearMap.range ((Kdiff U 0).app W)).mkQ x) =
          ⟨augmentationApp U W x, ⟨x, rfl⟩⟩ } := by
  classical
  let e : ((Kterm U 0).obj W ⧸ LinearMap.range ((Kdiff U 0).app W)) ≃ₗ[sections X W]
      (imagePresheaf U).obj W := (Submodule.quotEquivOfEq
      (LinearMap.range ((Kdiff U 0).app W)) (LinearMap.ker (augmentationApp U W))
      (augmentation_ker U W).symm).trans
    (LinearMap.quotKerEquivRange (augmentationApp U W))
  refine ⟨e, fun x => Subtype.ext ?_⟩
  simp only [e]
  exact LinearMap.quotKerEquivRange_apply_mk (augmentationApp U W) x

/-- The canonical degree-zero identification commutes with restrictions; hence it is an isomorphism
of homology presheaves, not merely a family of isomorphisms. -/
@[stacks 01EM "naturality of degree-zero identification"]
public theorem homologyZeroIsoImage_naturality (U : Cover X I)
    {W W' : Opens X.carrier} (h : W ≤ W') (x : (Kterm U 0).obj W') :
    (homologyZeroIsoImage U W).1
        ((LinearMap.range ((Kdiff U 0).app W)).mkQ ((Kterm U 0).res h x)) =
      (imagePresheaf U).res h
        ((homologyZeroIsoImage U W').1
          ((LinearMap.range ((Kdiff U 0).app W')).mkQ x)) := by
  apply Subtype.ext
  rw [(homologyZeroIsoImage U W).2 ((Kterm U 0).res h x),
    (homologyZeroIsoImage U W').2 x]
  simpa [imagePresheaf] using augmentation_naturality U h x

end Stacks.Cohomology.CechImagePresheaf

end
