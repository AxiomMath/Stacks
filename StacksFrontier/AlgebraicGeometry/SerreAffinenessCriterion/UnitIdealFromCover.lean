module

public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence

/-!
# A covering family of global sections generates the unit ideal

Let `X` be a scheme on which `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals
`𝓘 ⊆ 𝒪_X`, and let `r₁, …, r_n` be global sections whose basic opens cover `X`. Then
`r₁, …, r_n` generate the unit ideal of `Γ(X, 𝒪_X)`.

This is the last paragraph of Serre's criterion for affineness. The map `𝒪_X^{⊕n} ⟶ 𝒪_X`
determined by the family is surjective exactly because the basic opens cover, its kernel is
quasi-coherent, and the cohomology of that kernel vanishes by dévissage along the summands: a
quasi-coherent subsheaf of `ℱ ⊞ 𝒪_X` sits in a short exact sequence whose outer terms are a
quasi-coherent subsheaf of `ℱ` and a quasi-coherent sheaf of ideals. Surjectivity of
`Γ(X, 𝒪_X)^{⊕n} ⟶ Γ(X, 𝒪_X)` then writes `1` as `∑ aᵢrᵢ`.

## Main definitions

* `Stacks.SerreCriterion.freeFinSuccIso` and `Stacks.SerreCriterion.freeFinOneIso`: the free
  sheaf of modules on `n + 1` letters as `R^{⊕n} ⊞ R`, and on one letter as `R`.

## Main results

* `Stacks.SerreCriterion.epi_freeHomEquiv_symm_sectionOfTop`: a finite family of global sections
  whose basic opens cover `X` generates `𝒪_X` as a sheaf of modules.
* `Stacks.SerreCriterion.isZero_hgroup_one_subobject_free`: the dévissage — the vanishing
  hypothesis on ideal sheaves propagates to quasi-coherent subsheaves of a finite free sheaf.
* `Stacks.SerreCriterion.span_eq_top_of_forall_mem_basicOpen`: the conclusion.

## Implementation notes

The two decompositions of a finite free sheaf are stated for an arbitrary sheaf of rings, never
for `X.ringCatSheaf`. A lemma restated at that instantiation cannot be
rewritten with, because `X.ringCatSheaf` is a `TopCat.Sheaf` and the sheaf of modules over it is
type-correct only after unfolding; with the sheaf of rings left as a parameter the rewrite
matches it as an argument instead. For the same reason the categorical half of the dévissage,
`mono_arrow_comp_fst`, is proved in an arbitrary abelian category.

The cohomology used here is the group-valued `Hgroup`, which is what the long exact sequence of
`StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence` speaks about. A
consumer whose vanishing hypothesis is phrased with the module-valued right derived functor of
sections over `⊤` translates it by
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe v u u'

namespace Stacks.SerreCriterion

/-! ### Global sections as sections of a sheaf of modules -/

section GlobalSection

variable {Z : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology ↥Z) RingCat.{u})

/-- Acting on the restriction of a global section of the coefficient sheaf is multiplication.
This is the single place where the module structure of `SheafOfModules.unit R` over `R` is
unfolded into the ring multiplication of `R`. -/
theorem smul_sectionOfTop_eval (t : ToType ((SheafOfModules.unit R).val.obj (op ⊤)))
    (U : Opens ↥Z) (a : ToType (R.obj.obj (op U))) :
    a • (Stacks.PresheafOfModules.sectionOfTop (SheafOfModules.unit R).val t).eval (op U) =
      (a * R.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (t : ToType (R.obj.obj (op ⊤))) : ToType (R.obj.obj (op U))) := rfl

end GlobalSection

/-! ### Finite free sheaves of modules split off a copy of the coefficient sheaf -/

section Free

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on one letter is the coefficient sheaf itself. -/
def freeFinOneIso :
    SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) ≅ SheafOfModules.unit R :=
  Stacks.SheafOfModules.Invertible.freeUniqueIso (R := R) _

variable [HasSheafify J AddCommGrpCat.{u}]

/-- The free sheaf of modules on `n + 1` letters is the free sheaf on `n` letters together with
one more copy of the coefficient sheaf. -/
def freeFinSuccIso (n : ℕ) :
    SheafOfModules.free (R := R) (ULift.{u} (Fin n)) ⊞ SheafOfModules.unit R ≅
      SheafOfModules.free (R := R) (ULift.{u} (Fin (n + 1))) :=
  biprod.mapIso (Iso.refl _)
      (Stacks.SheafOfModules.Invertible.freeUniqueIso (R := R) PUnit.{u + 1}).symm ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫
      (SheafOfModules.freeFunctor (R := R)).mapIso
        ((Equiv.sumCongr Equiv.ulift (Equiv.ofUnique PUnit.{u + 1} (Fin 1))).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)).toIso

end Free

/-! ### The categorical half of the dévissage -/

/-- A morphism killed by the factorisation of `p` through its image is killed by `p`. -/
theorem comp_eq_zero_of_comp_factorThruImageSubobject {C : Type u'} [Category.{v} C] [Abelian C]
    {A B Z : C} (p : A ⟶ B) {v : Z ⟶ A} (hv : v ≫ factorThruImageSubobject p = 0) :
    v ≫ p = 0 := by
  rw [← imageSubobject_arrow_comp p, ← Category.assoc, hv, zero_comp]

/-- A subobject of `A ⊞ B` meets `A` in the kernel of its projection to `B`: the composite of
that kernel inclusion with the first projection is a monomorphism. -/
theorem mono_arrow_comp_fst {C : Type u'} [Category.{v} C] [Abelian C] {A B : C}
    (I : Subobject (A ⊞ B)) :
    Mono (kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)) ≫
      I.arrow ≫ biprod.fst) := by
  have h0 : kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)) ≫
      (I.arrow ≫ biprod.snd) = 0 :=
    comp_eq_zero_of_comp_factorThruImageSubobject _ (kernel.condition _)
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z v hv
  refine (cancel_mono (kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)))).1
    ((cancel_mono I.arrow).1 (biprod.hom_ext _ _ ?_ ?_))
  · simpa only [Category.assoc, zero_comp] using hv
  · simp only [Category.assoc, zero_comp, h0, comp_zero]

/-! ### Dévissage along the summands of a finite free sheaf -/

variable {X : Scheme.{u}}

/-- Vanishing of `H¹` on quasi-coherent subobjects of `M` gives vanishing on any quasi-coherent
source of a monomorphism into `M`. -/
private theorem isZero_hgroup_one_of_mono {M K : SheafOfModules.{u} X.ringCatSheaf} (g : K ⟶ M)
    [Mono g] (hK : K.IsQuasicoherent)
    (hM : ∀ J : Subobject M, (Subobject.underlying.obj J).IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 K) :=
  have heq := Subobject.underlyingIso g
  (hM (Subobject.mk g)
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso heq.symm hK)).of_iso
    ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso heq.symm)

/-- Vanishing of `H¹` on quasi-coherent subsheaves of `ℱ` and on quasi-coherent sheaves of
ideals propagates to quasi-coherent subsheaves of `ℱ ⊞ 𝒪_X`: such a subsheaf maps onto a
quasi-coherent sheaf of ideals, and the kernel of that map is a quasi-coherent subsheaf of
`ℱ`. -/
theorem isZero_hgroup_one_subobject_biprod
    (hH₁ : ∀ J : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj J).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J)))
    (M : SheafOfModules.{u} X.ringCatSheaf) [M.IsQuasicoherent]
    (hM : ∀ J : Subobject M, (Subobject.underlying.obj J).IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J)))
    (I : Subobject (M ⊞ SheafOfModules.unit X.ringCatSheaf))
    (hI : (Subobject.underlying.obj I).IsQuasicoherent) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I)) := by
  have hu : Mono (kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)) ≫
    I.arrow ≫ biprod.fst) := mono_arrow_comp_fst I
  have hS : (ShortComplex.mk (kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)))
      (factorThruImageSubobject (I.arrow ≫ biprod.snd))
      (kernel.condition _)).ShortExact :=
    ShortComplex.shortExact_mk_kernel_ι _
  have himageQC : (Subobject.underlying.obj
      (imageSubobject (I.arrow ≫ biprod.snd))).IsQuasicoherent :=
    imageSubobject_isQuasicoherent _
  have hkerQC : (kernel (factorThruImageSubobject (I.arrow ≫ biprod.snd))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _
  have hker : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (kernel (factorThruImageSubobject (I.arrow ≫ biprod.snd)))) :=
    isZero_hgroup_one_of_mono (kernel.ι (factorThruImageSubobject (I.arrow ≫ biprod.snd)) ≫
      I.arrow ≫ biprod.fst) hkerQC hM
  exact Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact X ⊤ hS 1 hker
    (hH₁ (imageSubobject (I.arrow ≫ biprod.snd)) himageQC)

/-- A finite free sheaf of modules on a nonempty index type is quasi-coherent. -/
instance isQuasicoherent_free_fin (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n + 1)))).IsQuasicoherent := by
  induction n with
  | zero =>
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (freeFinOneIso X.ringCatSheaf).symm inferInstance
  | succ n ih =>
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (freeFinSuccIso X.ringCatSheaf (n + 1)) inferInstance

/-- **The dévissage.** If `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals, then
`H¹(X, 𝓕) = 0` for every quasi-coherent subsheaf `𝓕` of a free sheaf of modules on a nonempty
finite index type. -/
theorem isZero_hgroup_one_subobject_free
    (hH₁ : ∀ J : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj J).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J))) :
    ∀ (n : ℕ) (I : Subobject (SheafOfModules.free (R := X.ringCatSheaf)
      (ULift.{u} (Fin (n + 1))))),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I)) := by
  intro n
  induction n with
  | zero =>
      intro I hI
      exact isZero_hgroup_one_of_mono (I.arrow ≫ (freeFinOneIso X.ringCatSheaf).hom) hI hH₁
  | succ n ih =>
      intro I hI
      exact isZero_hgroup_one_of_mono (I.arrow ≫ (freeFinSuccIso X.ringCatSheaf (n + 1)).inv) hI
        (isZero_hgroup_one_subobject_biprod hH₁
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n + 1)))) ih)

/-! ### A covering family of global sections generates the structure sheaf -/

/-- **A finite family of global sections whose basic opens cover `X` generates `𝒪_X`.** The
induced map out of the finite free sheaf of modules is an epimorphism, because over the basic
open of a member of the family that member is invertible. -/
theorem epi_freeHomEquiv_symm_sectionOfTop {I : Type u} [Finite I] (f : I → Γ(X, ⊤))
    (hcover : ∀ x : X, ∃ i, x ∈ X.basicOpen (f i)) :
    Epi ((SheafOfModules.freeHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
      (fun i ↦ Stacks.PresheafOfModules.sectionOfTop
        (SheafOfModules.unit X.ringCatSheaf).val (f i))) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  set q := (SheafOfModules.freeHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
    (fun i ↦ Stacks.PresheafOfModules.sectionOfTop
      (SheafOfModules.unit X.ringCatSheaf).val (f i)) with hq
  have hcoord : ∀ (W : X.Opens) (c : I → ToType (X.ringCatSheaf.obj.obj (op W))),
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map q.val).app (op W)
          (Stacks.SheafOfModules.freeMk (op W) c) =
        ∑ i, c i • (Stacks.PresheafOfModules.sectionOfTop
          (SheafOfModules.unit X.ringCatSheaf).val (f i)).eval (op W) := by
    intro W c
    change q.val.app (op W) (Stacks.SheafOfModules.freeMk (op W) c) = _
    rw [Stacks.SheafOfModules.app_freeMk q (op W) c]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq, Stacks.SheafOfModules.ιFree_comp_freeHomEquiv_symm,
      Stacks.SheafOfModules.unitHomEquiv_symm_app_unitOne]
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective q ⟨fun {V} t => ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hxV
  obtain ⟨i, hxi⟩ := hcover x
  refine ⟨V ⊓ X.basicOpen (f i), homOfLE inf_le_left, ?_, hxV, hxi⟩
  have hle : V ⊓ X.basicOpen (f i) ≤ X.basicOpen (f i) := inf_le_right
  obtain ⟨w, hw⟩ : ∃ w : ToType (X.ringCatSheaf.obj.obj (op (V ⊓ X.basicOpen (f i)))),
      w * X.ringCatSheaf.obj.map
        (homOfLE (show V ⊓ X.basicOpen (f i) ≤ ⊤ from le_top)).op (f i) = 1 := by
    have h0 : IsUnit (X.presheaf.map
        (homOfLE (show V ⊓ X.basicOpen (f i) ≤ ⊤ from le_top)).op (f i)) := by
      rw [show (homOfLE (show V ⊓ X.basicOpen (f i) ≤ ⊤ from le_top)) =
        homOfLE hle ≫ homOfLE (X.basicOpen_le (f i)) from Subsingleton.elim _ _,
        op_comp, X.presheaf.map_comp, CommRingCat.comp_apply]
      exact RingHom.isUnit_map (X.presheaf.map (homOfLE hle).op).hom
        (X.toRingedSpace.isUnit_res_basicOpen (f i))
    exact ⟨(↑h0.unit⁻¹ : Γ(X, V ⊓ X.basicOpen (f i))), Units.inv_mul_of_eq h0.unit_spec⟩
  have hkey : ∀ s : ToType (X.ringCatSheaf.obj.obj (op (V ⊓ X.basicOpen (f i)))),
      (s * w) * X.ringCatSheaf.obj.map
        (homOfLE (show V ⊓ X.basicOpen (f i) ≤ ⊤ from le_top)).op (f i) = s := by
    intro s
    rw [mul_assoc, hw, mul_one]
  set c : I → ToType (X.ringCatSheaf.obj.obj (op (V ⊓ X.basicOpen (f i)))) :=
    fun j => if j = i then
      X.ringCatSheaf.obj.map (homOfLE (show V ⊓ X.basicOpen (f i) ≤ V from inf_le_left)).op
        (t : ToType (X.ringCatSheaf.obj.obj (op V))) * w
      else 0 with hc
  have hci : c i = X.ringCatSheaf.obj.map
      (homOfLE (show V ⊓ X.basicOpen (f i) ≤ V from inf_le_left)).op
      (t : ToType (X.ringCatSheaf.obj.obj (op V))) * w := by simp [hc]
  have hcj : ∀ j, j ≠ i → c j = 0 := fun j hj => by simp [hc, hj]
  refine ⟨Stacks.SheafOfModules.freeMk (op (V ⊓ X.basicOpen (f i))) c, ?_⟩
  rw [hcoord (V ⊓ X.basicOpen (f i)) c,
    Finset.sum_eq_single i (fun j _ hj => by rw [hcj j hj, zero_smul]) (by simp), hci]
  exact (smul_sectionOfTop_eval X.ringCatSheaf (f i) _ _).trans (hkey _)

/-! ### The unit ideal -/

/-- **Serre's criterion, second input: a finite covering family of global sections spans.** On a
scheme whose quasi-coherent sheaves of ideals have vanishing `H¹`, a finite family of global
sections whose basic opens cover `X` generates the unit ideal of `Γ(X, 𝒪_X)`. -/
theorem span_eq_top_of_forall_mem_basicOpen
    (hH₁ : ∀ J : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj J).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J)))
    {I : Type u} [Finite I] [Nonempty I] (f : I → Γ(X, ⊤))
    (hcover : ∀ x : X, ∃ i, x ∈ X.basicOpen (f i)) :
    Ideal.span (Set.range f) = ⊤ := by
  classical
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card I = n + 1 :=
    ⟨Fintype.card I - 1, by have := Fintype.card_pos_iff.mpr ‹Nonempty I›; omega⟩
  let eFree : SheafOfModules.free (R := X.ringCatSheaf) I ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n + 1))) :=
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
      (((Fintype.equivFin I).trans (finCongr hn)).trans Equiv.ulift.symm).toIso
  set q := (SheafOfModules.freeHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
    (fun i ↦ Stacks.PresheafOfModules.sectionOfTop
      (SheafOfModules.unit X.ringCatSheaf).val (f i)) with hq
  have hepi : Epi q := epi_freeHomEquiv_symm_sectionOfTop f hcover
  have hfreeQC : (SheafOfModules.free (R := X.ringCatSheaf) I).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eFree.symm
      (isQuasicoherent_free_fin X n)
  have hkerQC : (kernel q).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel q
  have hKzero : IsZero (Hgroup X.ringCatSheaf ⊤ 1 (kernel q)) :=
    isZero_hgroup_one_of_mono (kernel.ι q ≫ eFree.hom) hkerQC
      (isZero_hgroup_one_subobject_free hH₁ n)
  have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    ShortComplex.shortExact_mk_kernel_ι q
  obtain ⟨t, ht⟩ := Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one
    X ⊤ hS hKzero (1 : Γ(X, ⊤))
  obtain ⟨a, ha⟩ := Stacks.SheafOfModules.exists_eq_sum_smul_freeHomEquiv q (op ⊤) t
  refine (Ideal.eq_top_iff_one _).2 ?_
  let b : I → Γ(X, ⊤) := fun i => a i
  have hterm : ∀ i,
      a i • ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv q i).eval (op ⊤) =
        b i * f i := by
    intro i
    have h1 : (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv q i =
        Stacks.PresheafOfModules.sectionOfTop (SheafOfModules.unit X.ringCatSheaf).val (f i) := by
      rw [hq, Equiv.apply_symm_apply]
    have h2 : ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv q i).eval (op ⊤) = f i :=
      (congrArg (fun s => PresheafOfModules.sections.eval s (op ⊤)) h1).trans
        (Stacks.PresheafOfModules.sectionOfTop_val_top _ _)
    exact congrArg (a i • ·) h2
  have hone : ∑ i, b i * f i = (1 : Γ(X, ⊤)) :=
    ((Finset.sum_congr rfl fun i _ => (hterm i).symm).trans ha).trans ht
  rw [← hone]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end Stacks.SerreCriterion

end
