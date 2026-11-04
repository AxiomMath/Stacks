module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Germ
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.QuasiRegularUnitIdeal.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a basis of the cotangent fibre to local generators

Let `X` be a locally ringed space, `J ⊆ O_X` an ideal subsheaf of its structure sheaf, `x` a
point of `X` and `f₁, …, f_r ∈ J_x` germs whose classes form a basis of the cotangent fibre
`J_x / 𝔪_x J_x` over the residue field `κ(x)`.  If `J` is quasi-regular, `H₁`-regular or
Koszul-regular, then the `f_i` are the germs at `x` of sections of `J` over some open
neighbourhood `U` of `x` which generate `J` over `U` and form a sequence of the same kind
there.  These are the three parts of Stacks tag 067N.

All three are read off one shrinking argument,
`Stacks.RingedSpace.exists_invertible_change_of_local_generators`: a local quasi-regular
generating sequence `g₁, …, g_s` has `s = r`, and after shrinking its open set the `f_i` are
sections of `J` obtained from the `g_j` by an invertible matrix of sections of `O_X`.  Over each
stalk of the shrunken open set the two sequences therefore generate the same ideal and have the
same length, so Stacks tag 066A carries each of the three regularity conditions from the `g_j`
to the `f_i`.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegular_of_isUnit_apply`: a sequence one of
  whose terms is a unit is Koszul-regular.  This is the degenerate case the statement of 067N has
  to allow, and it is also what makes a family of units count as a Koszul-regular family of
  equations cutting out the empty subscheme away from a closed immersion.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_quasiRegular_generators_of_basis`:
  **Stacks tag 067N, part (1)**, the quasi-regular case.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_h1Regular_generators_of_basis`:
  **Stacks tag 067N, part (2)**, the `H₁`-regular case.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_koszulRegular_generators_of_basis`:
  **Stacks tag 067N, part (3)**, the Koszul-regular case.

## Implementation notes

The three conditions are stated exactly as the definitions of Stacks tag 063D state them for the
local witness of a regular ideal sheaf: quasi-regularity by `IsIso` of the sheaf morphism of
Stacks tag 063B on `X` restricted to `U`, and `H₁`- and Koszul-regularity by
`IsKoszulSequenceExactOn`, the germwise exactness of the Koszul complex in the relevant degrees.
In particular a conclusion of any of the three can be fed straight back into
`IsQuasiRegularIdealSheaf`, `IsH1RegularIdealSheaf` or `IsKoszulRegularIdealSheaf`.

The shrinking argument needs a *quasi-regular* local generating sequence, which parts (2) and
(3) do not hand over directly.  They supply one through commutative algebra rather than through
the sheaf-level implications of Stacks tag 063E: an `H₁`-regular sequence in a ring is
quasi-regular by Stacks tag 062I (`Koszul.isQuasiRegular_of_isH1RegularOn`), so the *same*
witness serves both purposes.  Going through Stacks tag 063E instead would produce a second,
unrelated witness on a second open set, and the length comparison would then have to be made
twice.

The hypothesis of 067N places no condition on `x`, so `J_x = O_{X,x}` has to be allowed.  There
the cotangent fibre is `κ(x)`, every `f_i` is a unit, and the conclusion holds for a trivial
reason on the open set where one of them is an invertible section: the sections of `J` are all
of `O_X` there, and a sequence generating the unit ideal is quasi-regular
(`Stacks.AlgebraicGeometry.QuasiRegularUnitIdeal.isQuasiRegular_of_isUnit_mem`) and
Koszul-regular, the latter because the one-term sequence consisting of the unit is weakly
regular and Stacks tag 066A then transfers Koszul-regularity to any generating sequence of the
same length.

## References

* [Stacks Project, Lemma 31.20.5 (Tag 067N)](https://stacks.math.columbia.edu/tag/067N),
  parts (1), (2) and (3).
* [Stacks Project, Lemma 15.30.3 (Tag 066A)](https://stacks.math.columbia.edu/tag/066A)
* [Stacks Project, Lemma 15.30.2 (Tag 062I)](https://stacks.math.columbia.edu/tag/062I)
* [Stacks Project, Lemma 15.30.1 (Tag 062F)](https://stacks.math.columbia.edu/tag/062F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingTheory.Sequence
open Stacks.RingTheory.QuasiRegular
open Stacks.RingTheory.RegularIdealSheaf
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### Changing a sequence by an invertible matrix -/

section ChangeMatrix

variable {R : Type*} [CommRing R] {r : ℕ}

/-- An invertible change of a finite sequence can be inverted. -/
lemma exists_inverse_change (f g : Fin r → R) (A : Matrix (Fin r) (Fin r) R)
    (hA : IsUnit A) (h : ∀ i, f i = ∑ j, A i j * g j) :
    ∃ B : Matrix (Fin r) (Fin r) R, ∀ i, g i = ∑ j, B i j * f j := by
  classical
  have hfg : f = A.mulVec g := funext h
  have hBA : (↑hA.unit⁻¹ : Matrix (Fin r) (Fin r) R) * A = 1 := by
    simpa only [hA.unit_spec] using Units.inv_mul hA.unit
  refine ⟨↑hA.unit⁻¹, fun i => ?_⟩
  have heq : (↑hA.unit⁻¹ : Matrix (Fin r) (Fin r) R).mulVec f = g := by
    rw [hfg, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact (congrFun heq i).symm

/-- An invertible change of a finite sequence does not change the ideal it generates. -/
lemma jid_eq_of_isUnit_matrix (f g : Fin r → R) (A : Matrix (Fin r) (Fin r) R)
    (hA : IsUnit A) (h : ∀ i, f i = ∑ j, A i j * g j) : Jid f = Jid g := by
  obtain ⟨B, hB⟩ := exists_inverse_change f g A hA h
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro z ⟨i, rfl⟩
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨A i, ?_⟩
    simpa only [smul_eq_mul] using (h i).symm
  · rintro z ⟨i, rfl⟩
    refine Ideal.mem_span_range_iff_exists_fun.2 ⟨B i, ?_⟩
    simpa only [smul_eq_mul] using (hB i).symm

/-- A sequence one of whose terms is a unit is Koszul-regular: the one-term sequence consisting
of that unit is weakly regular, hence Koszul-regular, and it generates the same (unit) ideal. -/
lemma isKoszulRegular_of_isUnit_apply (f : Fin r → R) (i : Fin r)
    (hi : IsUnit (f i)) : Koszul.IsKoszulRegular f := by
  have hr : r ≠ 0 := by
    rintro rfl
    exact absurd i.isLt (Nat.not_lt_zero i.val)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  set g : Fin (n + 1) → R := Fin.cons (f i) 0 with hg
  have hg0 : g 0 = f i := by rw [hg, Fin.cons_zero]
  have hgu : IsUnit (g 0) := by rw [hg0]; exact hi
  have hspan : Ideal.span (Set.range g) = Jid f := by
    have h1 : Ideal.span (Set.range g) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self 0)) hgu
    have h2 : Jid f = ⊤ :=
      Ideal.eq_top_of_isUnit_mem (Jid f) (Ideal.subset_span (Set.mem_range_self i)) hi
    rw [h1, h2]
  have hweak : IsWeaklyRegular R (List.ofFn g) := by
    rw [List.ofFn_succ]
    refine (RingTheory.Sequence.isWeaklyRegular_cons_iff R (g 0) _).mpr ⟨hgu.isSMulRegular R, ?_⟩
    have hsub : Subsingleton (QuotSMulTop (g 0) R) := by
      refine Submodule.Quotient.subsingleton_iff.mpr ?_
      rw [← Submodule.ideal_span_singleton_smul, Ideal.span_singleton_eq_top.mpr hgu,
        Submodule.top_smul]
    rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
    exact fun _ a b _ => Subsingleton.elim a b
  exact (Koszul.regularity_of_generators_of_eq_span_range (Jid f) f rfl).2.2
    ⟨g, hspan, (Koszul.isKoszulRegularOn_self_iff g).mp
      (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1 hweak)⟩

end ChangeMatrix

/-! ### Generation and regularity through an invertible matrix of sections -/

section Sections

variable {X : RingedSpace.{u}} {r : ℕ}

/-- Two families of sections related by an invertible matrix generate the same ideal
subsheaf. -/
private lemma generatedIdealOn_eq_of_unit_matrix (U : Opens X)
    (f g : Fin r → X.presheaf.obj (op U)) (A : Matrix (Fin r) (Fin r) (X.presheaf.obj (op U)))
    (hA : IsUnit A) (h : ∀ i, f i = ∑ j, A i j * g j) :
    generatedIdealOn X U f = generatedIdealOn X U g := by
  obtain ⟨B, hB⟩ := exists_inverse_change f g A hA h
  refine le_antisymm (generatedIdealOn_le X U f _ fun i => ?_)
    (generatedIdealOn_le X U g _ fun i => ?_)
  · rw [h i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mem_generatedIdealOn X U g j)
  · rw [hB i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mem_generatedIdealOn X U f j)

/-- Generation of an ideal sheaf passes along an invertible change of the generating family. -/
private lemma isGeneratedByOn_of_unit_matrix (J : (structureSheafModule X).Submodule)
    (U : Opens X) (f g : Fin r → X.presheaf.obj (op U))
    (A : Matrix (Fin r) (Fin r) (X.presheaf.obj (op U))) (hA : IsUnit A)
    (h : ∀ i, f i = ∑ j, A i j * g j) (hgen : IsGeneratedByOn X J U g) :
    IsGeneratedByOn X J U f := fun V hVU => by
  rw [hgen V hVU, generatedIdealOn_eq_of_unit_matrix U f g A hA h]

/-- Sheaf quasi-regularity of a family of sections over `U` is germwise quasi-regularity. -/
private lemma isIso_quasiRegularMap_iff_forall_isQuasiRegular_germ (U : Opens X)
    (f : Fin r → X.presheaf.obj (op U)) :
    IsIso (quasiRegularMap (X.restrict U.isOpenEmbedding)
        (fun i => sectionOnRestriction X U (f i))).hom ↔
      ∀ (y : X) (hy : y ∈ U), IsQuasiRegular (X.presheaf.stalk y)
        (List.ofFn (germFamily X U f y hy)) := by
  rw [isQuasiRegularMapIso_iff_forall_germ X U f]
  exact forall_congr' fun y => forall_congr' fun hy =>
    (Stacks.RingTheory.RegularIdealSheaf.isQuasiRegularRel_iff_bijective _).trans
      (Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff _).symm

/-- A family of sections one of which is invertible generates the whole structure sheaf, hence
any ideal subsheaf containing the family. -/
private lemma isGeneratedByOn_of_isUnit (J : (structureSheafModule X).Submodule) (U : Opens X)
    (f : Fin r → X.presheaf.obj (op U)) (hf : ∀ j, f j ∈ J.obj (op U)) (i : Fin r)
    (hi : IsUnit (f i)) : IsGeneratedByOn X J U f := by
  intro V hVU
  obtain ⟨a, ha⟩ := (hi.map (X.presheaf.map (homOfLE hVU).op).hom).exists_left_inv
  have hmem : X.presheaf.map (homOfLE hVU).op (f i) ∈ (generatedIdealOn X U f).obj (op V) :=
    (generatedIdealOn X U f).map_mem (homOfLE hVU).op (mem_generatedIdealOn X U f i)
  have h1 : (1 : X.presheaf.obj (op V)) ∈ (generatedIdealOn X U f).obj (op V) := by
    rw [← ha]
    exact Submodule.smul_mem _ a hmem
  have hgentop : (generatedIdealOn X U f).obj (op V) = ⊤ := (Ideal.eq_top_iff_one _).mpr h1
  refine le_antisymm ?_ (generatedIdealOn_le X U f J hf (op V))
  rw [hgentop]
  exact le_top

end Sections

/-! ### Realising germs of an ideal subsheaf by sections -/

section Germs

variable {X : LocallyRingedSpace.{u}} (J : (structureSheafModule X.toRingedSpace).Submodule)

/-- Finitely many germs lying in the stalk of an ideal subsheaf are simultaneously represented by
sections *of that subsheaf* on one neighbourhood. -/
lemma exists_mem_sections_germ_eq (x : X) {ι : Type*} (F : ι → X.presheaf.stalk x)
    (hF : ∀ i, F i ∈ Stacks.RingedSpace.stalkIdeal J x) (t : Finset ι) :
    ∃ (U : Opens X) (hx : x ∈ U) (σ : ι → X.presheaf.obj (op U)),
      (∀ i, σ i ∈ J.obj (op U)) ∧ ∀ i ∈ t, X.presheaf.germ U x hx (σ i) = F i := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨⊤, trivial, fun _ => 0, fun _ => Submodule.zero_mem _, by simp⟩
  | insert i t hi ih =>
    obtain ⟨U₁, hx₁, σ₁, hσ₁J, hσ₁⟩ := ih
    obtain ⟨U₂, hx₂, s₂, hs₂J, hs₂⟩ := Stacks.RingedSpace.mem_stalkIdeal_iff J |>.mp (hF i)
    have hx₁₂ : x ∈ U₁ ⊓ U₂ := ⟨hx₁, hx₂⟩
    refine ⟨U₁ ⊓ U₂, hx₁₂,
      Function.update
        (fun k => X.presheaf.map (homOfLE (inf_le_left (a := U₁) (b := U₂))).op (σ₁ k)) i
        (X.presheaf.map (homOfLE (inf_le_right (a := U₁) (b := U₂))).op s₂), ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self]
        exact Stacks.RingedSpace.restrict_mem J _ hs₂J
      · rw [Function.update_of_ne hki]
        exact Stacks.RingedSpace.restrict_mem J _ (hσ₁J k)
    · intro k hk
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self, X.presheaf.germ_res_apply]
        exact hs₂
      · rw [Function.update_of_ne hki, X.presheaf.germ_res_apply]
        exact hσ₁ k (by simpa [hki] using hk)

/-- A finite family of germs in the stalk of an ideal subsheaf is realised by sections of that
subsheaf on one neighbourhood. -/
private lemma exists_sections_of_stalkIdeal (x : X) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x) :
    ∃ (U : Opens X) (hx : x ∈ U) (fU : Fin r → X.presheaf.obj (op U)),
      (∀ i, fU i ∈ J.obj (op U)) ∧ ∀ i, X.presheaf.germ U x hx (fU i) = (f i).1 := by
  obtain ⟨U, hx, σ, hσJ, hσ⟩ :=
    exists_mem_sections_germ_eq J x (fun i => (f i).1) (fun i => (f i).2) Finset.univ
  exact ⟨U, hx, σ, hσJ, fun i => hσ i (Finset.mem_univ i)⟩

/-- At a point where an ideal of a local ring is the unit ideal, every lift of a basis of
`I / 𝔪 I` consists of units — and there is at least one of them, because `I / 𝔪 I` is then the
residue field and in particular nonzero. -/
private lemma exists_isUnit_of_basis_of_eq_top {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I = ⊤) {r : ℕ} (f : Fin r → I)
    (b : Module.Basis (Fin r) (R ⧸ IsLocalRing.maximalIdeal R)
      (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i)) : ∃ i, IsUnit (f i).1 := by
  have hone : (1 : R) ∈ I := by rw [hI]; trivial
  have hle : IsLocalRing.maximalIdeal R • (⊤ : Submodule R I) ≤
      Submodule.comap I.subtype (IsLocalRing.maximalIdeal R) :=
    Submodule.smul_le.mpr fun a ha z _ => Ideal.mul_mem_right z.1 _ ha
  have hn : IsLocalRing.maximalIdeal R • (⊤ : Submodule R I) ≠ ⊤ := by
    intro hh
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R :=
      hle (hh ▸ (Submodule.mem_top : (⟨1, hone⟩ : I) ∈ ⊤))
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hnt : Nontrivial (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))) :=
    Submodule.Quotient.nontrivial_iff.mpr hn
  obtain ⟨i⟩ := b.index_nonempty
  refine ⟨i, ?_⟩
  by_contra hi
  have hm : (f i).1 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hi
  have hfi : f i ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R I) := by
    have he : (f i).1 • (⟨1, hone⟩ : I) = f i := Subtype.ext (by simp)
    rw [← he]
    exact Submodule.smul_mem_smul hm Submodule.mem_top
  exact b.ne_zero i ((hf i).trans ((Submodule.Quotient.mk_eq_zero _).mpr hfi))

/-- Where the stalk of the ideal subsheaf is the unit ideal, a lift of a basis of the cotangent
fibre is realised by sections of `J` one of which is invertible. -/
private lemma exists_unit_sections_of_stalkIdeal_eq_top (x : X)
    (htop : Stacks.RingedSpace.stalkIdeal J x = ⊤) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i)) :
    ∃ (U : Opens X) (hxU : x ∈ U) (fU : Fin r → X.presheaf.obj (op U)),
      (∀ i, fU i ∈ J.obj (op U)) ∧
        (∀ i, X.presheaf.germ U x hxU (fU i) = (f i).1) ∧ ∃ i, IsUnit (fU i) := by
  obtain ⟨i, hi⟩ := exists_isUnit_of_basis_of_eq_top _ htop f b hf
  obtain ⟨V, hxV, fV, hfVJ, hfV⟩ := exists_sections_of_stalkIdeal J x f
  have hiV : IsUnit (X.presheaf.germ V x hxV (fV i)) := by rw [hfV i]; exact hi
  obtain ⟨U, iUV, hxU, hiU⟩ :=
    X.toRingedSpace.isUnit_res_of_isUnit_germ V (fV i) x hxV hiV
  refine ⟨U, hxU, fun j => X.presheaf.map iUV.op (fV j),
    fun j => Stacks.RingedSpace.restrict_mem J iUV (hfVJ j), fun j => ?_, i, hiU⟩
  rw [X.presheaf.germ_res_apply]
  exact hfV j

/-- A point at which the stalk of an ideal subsheaf is a proper ideal lies in the support of the
quotient. -/
private lemma mem_idealQuotientSupport_of_stalkIdeal_ne_top (x : X)
    (h : Stacks.RingedSpace.stalkIdeal J x ≠ ⊤) :
    x ∈ idealQuotientSupport X.toRingedSpace J := by
  by_contra hx
  obtain ⟨U, hxU, h1⟩ := (notMem_idealQuotientSupport_iff J x).mp hx
  exact h (Ideal.eq_top_of_isUnit_mem _
    ((Stacks.RingedSpace.mem_stalkIdeal_iff J).mpr ⟨U, hxU, 1, h1, map_one _⟩) isUnit_one)

end Germs

/-! ### The three parts of Stacks tag 067N -/

section Main

variable {X : LocallyRingedSpace.{u}} (J : (structureSheafModule X.toRingedSpace).Submodule)

/-- **The common core of the three parts of Stacks tag 067N.** A lift `f` of a basis of the
cotangent fibre at a point `x` of the support is realised, after shrinking a neighbourhood `V`
carrying a quasi-regular generating sequence `g`, by sections of `J` which generate `J` and whose
germs generate, at every point of the shrunken neighbourhood, the same ideal as the germs of
`g`.  The lengths of the two sequences agree. -/
private lemma exists_change_of_local_generators (x : X) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hsupp : Stacks.RingedSpace.stalkIdeal J x ≠ ⊤)
    {s : ℕ} (V : Opens X) (hxV : x ∈ V) (g : Fin s → X.presheaf.obj (op V))
    (hgen : IsGeneratedByOn X.toRingedSpace J V g)
    (hqr : ∀ (y : X) (hy : y ∈ V), IsQuasiRegular (X.presheaf.stalk y)
      (List.ofFn (germFamily X.toRingedSpace V g y hy))) :
    ∃ (hrs : r = s) (U : Opens X) (hxU : x ∈ U) (hUV : U ≤ V) (fU : Fin r → J.obj (op U)),
      (∀ i, X.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧
      IsGeneratedByOn X.toRingedSpace J U (fun i => (fU i).1) ∧
      (∀ (y : X) (hy : y ∈ U),
        Jid (germFamily X.toRingedSpace U (fun i => (fU i).1) y hy)
          = Jid (fun j : Fin r =>
              germFamily X.toRingedSpace V g y (hUV hy) (Fin.cast hrs j))) := by
  obtain ⟨hrs, U, hxU, iUV, fU, A, hA, hfU, hchange⟩ :=
    Stacks.RingedSpace.exists_invertible_change_of_local_generators J x f b hf hsupp V hxV g
      (fun y hy => stalkIdeal_eq_Jid_germFamily J V g hgen y hy) hqr
  subst hrs
  simp only [Fin.cast_refl, id_eq] at hchange
  have hiUV : homOfLE (leOfHom iUV) = iUV := Subsingleton.elim _ _
  refine ⟨rfl, U, hxU, leOfHom iUV, fU, hfU, ?_, ?_⟩
  · refine isGeneratedByOn_of_unit_matrix J U _
      (fun j => X.presheaf.map iUV.op (g j)) A hA hchange ?_
    simpa only [hiUV] using isGeneratedByOn_of_le V g hgen U (leOfHom iUV)
  · intro y hy
    simp only [Fin.cast_refl, id_eq]
    refine jid_eq_of_isUnit_matrix _ _ ((X.presheaf.germ U y hy).hom.mapMatrix A)
      (hA.map (X.presheaf.germ U y hy).hom.mapMatrix) fun i => ?_
    have := congrArg (X.presheaf.germ U y hy) (hchange i)
    simpa only [map_sum, map_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
      X.presheaf.germ_res_apply, germFamily] using this

/-- **The skeleton shared by the three parts of Stacks tag 067N.** For a sheaf-level condition `Q`
which is the germwise form of a ring-level condition `P` on finite sequences, where `P` implies
quasi-regularity, holds as soon as one term is a unit and is transported along equality of the
generated ideals, a local witness for `Q` at every point of the support yields one with the given
germs at `x`. -/
private lemma exists_generators_of_basis_of_germwise (x : X) {r : ℕ}
    (Q : ∀ (U : Opens X) {n : ℕ}, (Fin n → X.presheaf.obj (op U)) → Prop)
    (P : ∀ (R : Type u) [CommRing R] {n : ℕ}, (Fin n → R) → Prop)
    (hQ : ∀ (U : Opens X) (n : ℕ) (f : Fin n → X.presheaf.obj (op U)),
      Q U f ↔ ∀ (y : X) (hy : y ∈ U), P _ (germFamily X.toRingedSpace U f y hy))
    (hqr : ∀ (R : Type u) [CommRing R] (n : ℕ) (g : Fin n → R), P R g →
      IsQuasiRegular R (List.ofFn g))
    (hunit : ∀ (R : Type u) [CommRing R] (n : ℕ) (g : Fin n → R) (i : Fin n),
      IsUnit (g i) → P R g)
    (htrans : ∀ (R : Type u) [CommRing R] (n : ℕ) (f g : Fin n → R),
      Jid f = Jid g → P R g → P R f)
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hJ : ∀ y : X, y ∈ idealQuotientSupport X.toRingedSpace J →
      ∃ (U : Opens X) (_ : y ∈ U) (s : ℕ) (g : Fin s → X.presheaf.obj (op U)),
        Q U g ∧ IsGeneratedByOn X.toRingedSpace J U g) :
    ∃ (U : Opens X) (hxU : x ∈ U) (fU : Fin r → J.obj (op U)),
      (∀ i, X.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧ Q U (fun i => (fU i).1) ∧
      IsGeneratedByOn X.toRingedSpace J U (fun i => (fU i).1) := by
  by_cases htop : Stacks.RingedSpace.stalkIdeal J x = ⊤
  · obtain ⟨U, hxU, fU, hfUJ, hfU, i, hi⟩ :=
      exists_unit_sections_of_stalkIdeal_eq_top J x htop f b hf
    exact ⟨U, hxU, fun j => ⟨fU j, hfUJ j⟩, hfU,
      (hQ U r fU).mpr fun y hy => hunit _ r _ i (hi.map (X.presheaf.germ U y hy).hom),
      isGeneratedByOn_of_isUnit J U fU hfUJ i hi⟩
  · obtain ⟨V, hxV, s, g, hQV, hgen⟩ :=
      hJ x (mem_idealQuotientSupport_of_stalkIdeal_ne_top J x htop)
    have hP := (hQ V s g).mp hQV
    obtain ⟨hrs, U, hxU, hUV, fU, hfU, hgenU, hJid⟩ :=
      exists_change_of_local_generators J x f b hf htop V hxV g hgen
        fun y hy => hqr _ s _ (hP y hy)
    subst hrs
    simp only [Fin.cast_refl, id_eq] at hJid
    exact ⟨U, hxU, fU, hfU, (hQ U r _).mpr fun y hy =>
      htrans _ r _ _ (hJid y hy) (hP y (hUV hy)), hgenU⟩

/-- **Stacks Project, Tag 067N, part (1).** Let `J` be a quasi-regular ideal sheaf on a locally
ringed space `X`, let `x ∈ X` and let `f₁, …, f_r ∈ J_x` be germs whose classes form a basis of
the cotangent fibre `J_x / 𝔪_x J_x`.  Then there is an open neighbourhood `U` of `x` on which the
`f_i` are the germs of sections of `J` which form a quasi-regular sequence generating `J`
over `U`. -/
@[stacks 067N "(1)", ega "IV 16.9.5" "(b') => (a)"]
theorem exists_quasiRegular_generators_of_basis (x : X) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hJ : IsQuasiRegularIdealSheaf X.toRingedSpace J) :
    ∃ (U : Opens X) (hxU : x ∈ U) (fU : Fin r → J.obj (op U)),
      (∀ i, X.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧
      IsIso (quasiRegularMap (X.toRingedSpace.restrict U.isOpenEmbedding)
        (fun i => sectionOnRestriction X.toRingedSpace U (fU i).1)).hom ∧
      IsGeneratedByOn X.toRingedSpace J U (fun i => (fU i).1) := by
  exact exists_generators_of_basis_of_germwise J x
    (fun U _ f => IsIso (quasiRegularMap (X.toRingedSpace.restrict U.isOpenEmbedding)
      (fun i => sectionOnRestriction X.toRingedSpace U (f i))).hom)
    (fun R _ _ g => IsQuasiRegular R (List.ofFn g))
    (fun U _ f => isIso_quasiRegularMap_iff_forall_isQuasiRegular_germ U f)
    (fun _ _ _ _ => id)
    (fun _ _ _ g i hi => Stacks.AlgebraicGeometry.QuasiRegularUnitIdeal.isQuasiRegular_of_isUnit_mem
      hi (List.mem_ofFn.mpr ⟨i, rfl⟩))
    (fun _ _ _ f g h hg =>
      (Koszul.regularity_of_generators_of_eq_span_range (Jid f) f rfl).1 ⟨g, h.symm, hg⟩)
    f b hf hJ

/-- **Stacks Project, Tag 067N, part (2).** The `H₁`-regular case: for an `H₁`-regular ideal
sheaf the sections produced over `U` have a Koszul complex which is germwise exact in degree
`1`. -/
@[stacks 067N "(2)"]
theorem exists_h1Regular_generators_of_basis (x : X) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hJ : IsH1RegularIdealSheaf X.toRingedSpace J) :
    ∃ (U : Opens X) (hxU : x ∈ U) (fU : Fin r → J.obj (op U)),
      (∀ i, X.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧
      IsKoszulSequenceExactOn X.toRingedSpace U (fun i => (fU i).1) (fun j => j = 1) ∧
      IsGeneratedByOn X.toRingedSpace J U (fun i => (fU i).1) := by
  exact exists_generators_of_basis_of_germwise J x
    (fun U _ f => IsKoszulSequenceExactOn X.toRingedSpace U f (fun j => j = 1))
    (fun _ _ _ g => Koszul.IsH1Regular g)
    (fun U _ f => isKoszulSequenceExactOn_iff_forall_germ_isH1Regular X.toRingedSpace U f)
    (fun _ _ _ _ h => Koszul.isQuasiRegular_of_isH1RegularOn
      ((Koszul.isH1RegularOn_self_iff _).mpr h))
    (fun _ _ _ g i hi => isKoszulRegular_of_isUnit_apply g i hi 1 one_ne_zero)
    (fun _ _ _ f g h hg =>
      (Koszul.regularity_of_generators_of_eq_span_range (Jid f) f rfl).2.1 ⟨g, h.symm, hg⟩)
    f b hf hJ

/-- **Stacks Project, Tag 067N, part (3).** The Koszul-regular case: for a Koszul-regular ideal
sheaf the sections produced over `U` have a Koszul complex which is germwise exact in every
positive degree. -/
@[stacks 067N "(3)"]
theorem exists_koszulRegular_generators_of_basis (x : X) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hJ : IsKoszulRegularIdealSheaf X.toRingedSpace J) :
    ∃ (U : Opens X) (hxU : x ∈ U) (fU : Fin r → J.obj (op U)),
      (∀ i, X.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧
      IsKoszulSequenceExactOn X.toRingedSpace U (fun i => (fU i).1) (fun j => 0 < j) ∧
      IsGeneratedByOn X.toRingedSpace J U (fun i => (fU i).1) := by
  exact exists_generators_of_basis_of_germwise J x
    (fun U _ f => IsKoszulSequenceExactOn X.toRingedSpace U f (fun j => 0 < j))
    (fun _ _ _ g => Koszul.IsKoszulRegular g)
    (fun U _ f => isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace U f)
    (fun _ _ _ _ h => Koszul.isQuasiRegular_of_isH1RegularOn
      ((Koszul.isH1RegularOn_self_iff _).mpr (h 1 one_ne_zero)))
    (fun _ _ _ g i hi => isKoszulRegular_of_isUnit_apply g i hi)
    (fun _ _ _ f g h hg =>
      (Koszul.regularity_of_generators_of_eq_span_range (Jid f) f rfl).2.2 ⟨g, h.symm, hg⟩)
    f b hf hJ

end Main

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
