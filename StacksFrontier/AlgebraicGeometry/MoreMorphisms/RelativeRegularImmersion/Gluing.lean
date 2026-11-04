module

public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Relative
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.IdealEquality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SequenceSpreadingOut
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# From a regular sequence on the fibre to a regular ideal sheaf

Let `g : Y ⟶ S` be flat and locally of finite presentation and let `j : Z ⟶ Y` be a closed
immersion with `Z ⟶ S` flat and with a finitely generated defining ideal.  Suppose that near
every point the defining ideal is cut out, *on the fibre over the base*, by a regular sequence.
Then the defining ideal of `j` is regular.

This is the scheme-level half of Stacks 063W: the two ring-level statements it rests on are
already in the tree, and all that is done here is to run them at a chart and glue.

## Main results

* `Stacks.AlgebraicGeometry.exists_affineOpen_isWeaklyRegular_generators_of_isRegular_fibre`:
  the affine-local step.
* `Stacks.AlgebraicGeometry.isRegularIdealSheaf_definingIdealOfHom_of_isRegular_fibre`:
  regularity of the defining ideal sheaf.

## Implementation notes

The fibre hypothesis is quantified over every compatible pair of affine opens `W ⊆ S`,
`U ⊆ g⁻¹W` and every prime `q` of `Γ(Y, U)` containing the defining ideal `I = ker(j.app U)`,
and it asks for a family `f₁, …, f_r ∈ I` whose image in the fibre `Γ(Y, U)_q/pΓ(Y, U)_q` is a
regular sequence generating `I` there.  That is exactly the conjunction of the hypotheses of the
two ring-level theorems, in their exact shapes:

* `Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_and_flat_quotient_away`
  (Stacks 062Y (3) for a sequence) turns the regularity of the fibre sequence into weak
  regularity in `Γ(Y, U)_{g₁}` for some `g₁ ∉ q`;
* `Stacks.RingTheory.SpreadingOut.exists_notMem_map_eq_map_away` (Stacks 046Y) turns the
  generation of the fibre ideal into the equality `I Γ(Y, U)_{g₂} = (f) Γ(Y, U)_{g₂}` for some
  `g₂ ∉ q`.

Those two elements are different, and the conclusion is asserted on the affine open
`D(g₂|_{D(g₁)}) = D(g₁) ∩ D(g₂)`.  Weak regularity survives the further shrinking because the
ring of sections of a basic open is a localization (`isWeaklyRegular_res_basicOpen`, from
`RingTheory.Sequence.IsWeaklyRegular.of_isLocalization`), and the ideal equality survives it
because the defining ideal of a quasi-compact morphism is quasi-coherent
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`).

The hypothesis that every member of the family lie in `q` — which the ring-level spreading out
needs and which is *not* automatic — is here free: the members lie in `I`, and `I ≤ q`.  The
case `I ≰ q` is the one Stacks handles by shrinking: a section of the defining ideal which is
invertible at the point forces the defining ideal to be the whole structure sheaf nearby, and the
one-element family `1` generates it and is weakly regular.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingTheory.Sequence
open Stacks.RingTheory.SpreadingOut

namespace Stacks.AlgebraicGeometry

open RegularIdealSheaf
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-- **Weak regularity passes to a basic open.**  The ring of sections of a basic open of an
affine open is a localization of the ring of sections, and weak regularity of a sequence is
preserved by localization. -/
private theorem isWeaklyRegular_res_basicOpen {Y : Scheme.{u}} {V U : Y.Opens}
    (hU : IsAffineOpen U) (t : Γ(Y, U)) (hV : V = Y.basicOpen t) (hVU : V ≤ U) {r : ℕ}
    (c : Fin r → Γ(Y, U)) (h : IsWeaklyRegular Γ(Y, U) (List.ofFn c)) :
    IsWeaklyRegular Γ(Y, V) (List.ofFn fun k => Y.presheaf.map (homOfLE hVU).op (c k)) := by
  subst hV
  have := hU.isLocalization_basicOpen t
  have h' := h.of_isLocalization Γ(Y, Y.basicOpen t) (Submonoid.powers t)
  rwa [List.map_ofFn] at h'

/-- Two successive restriction maps of the structure presheaf compose to the restriction map. -/
private theorem presheaf_map_homOfLE_comp {Y : Scheme.{u}} {U V' V : Y.Opens} (h₁ : V' ≤ U)
    (h₂ : V ≤ V') (h : V ≤ U) :
    Y.presheaf.map (homOfLE h₁).op ≫ Y.presheaf.map (homOfLE h₂).op =
      Y.presheaf.map (homOfLE h).op := by
  rw [← Y.presheaf.map_comp]
  rfl

/-- **Where a section of the defining ideal is invertible the defining ideal is everything.**
If `t` lies in the kernel of `j.app U` then over any open contained in `D(t)` the defining ideal
of `j` has all sections:  the restriction of `t` is both invertible and zero in the ring of
sections of `Z`, which is therefore the zero ring. -/
private theorem definingIdealOfHom_obj_eq_top_of_mem_ker {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    {U : Y.Opens} (t : Γ(Y, U)) (ht : t ∈ RingHom.ker (j.app U).hom)
    {V' : Y.Opens} (hV' : V' ≤ Y.basicOpen t) :
    (definingIdealOfHom j).obj (op V') = ⊤ := by
  have htU : t ∈ (definingIdealOfHom j).obj (op U) :=
    (mem_definingIdealOfHom_iff_app j U t).mpr (RingHom.mem_ker.mp ht)
  have hle : V' ≤ U := hV'.trans (Y.basicOpen_le t)
  -- the restriction of `t` to `V'` still lies in the defining ideal
  have ht' : Y.presheaf.map (homOfLE hle).op t ∈ (definingIdealOfHom j).obj (op V') :=
    (definingIdealOfHom j).toSubmodule.map_mem (homOfLE hle).op htU
  -- and it is invertible, so the ring of sections of `Z` over `j⁻¹V'` is the zero ring
  have hunit : IsUnit (Y.presheaf.map (homOfLE hle).op t) := by
    rw [← presheaf_map_homOfLE_comp (Y.basicOpen_le t) hV' hle, CommRingCat.comp_apply]
    exact (Y.toRingedSpace.isUnit_res_basicOpen t).map (Y.presheaf.map (homOfLE hV').op).hom
  have hzero : (j.app V').hom (Y.presheaf.map (homOfLE hle).op t) = 0 :=
    (mem_definingIdealOfHom_iff_app j V' _).mp ht'
  have : (0 : Γ(Z, j ⁻¹ᵁ V')) = 1 := by
    rw [← isUnit_zero_iff, ← hzero]
    exact hunit.map (j.app V').hom
  have := subsingleton_of_zero_eq_one this
  exact top_unique fun s _ =>
    (mem_definingIdealOfHom_iff_app j V' s).mpr (Subsingleton.elim _ _)

/-- **Flatness of the quotient at a prime.**  If `B ⧸ I` is flat over `A` then so is
`B_q ⧸ I B_q`, which is a localization of `B ⧸ I`.  An alias of
`Stacks.RingTheory.SpreadingOut.flat_quotient_localization`. -/
private alias flat_quotient_map_atPrime := Stacks.RingTheory.SpreadingOut.flat_quotient_localization

/-- Extending an ideal along two successive restriction maps extends it along their composite. -/
private theorem map_res_res {Y : Scheme.{u}} {U V' V : Y.Opens} (h₁ : V' ≤ U) (h₂ : V ≤ V')
    (h : V ≤ U) (K : Ideal Γ(Y, U)) :
    (K.map (Y.presheaf.map (homOfLE h₁).op).hom).map (Y.presheaf.map (homOfLE h₂).op).hom
      = K.map (Y.presheaf.map (homOfLE h).op).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, presheaf_map_homOfLE_comp]

/-- **The defining ideal over a smaller affine open.**  For a quasi-compact `j` and affine opens
`V ≤ U` the kernel of `j.app V` is the extension of the kernel of `j.app U`;  so if that
extension is the ideal generated by the restrictions of a family, the kernel is. -/
private theorem ker_app_eq_span_range_res {Y Z : Scheme.{u}} (j : Z ⟶ Y) [QuasiCompact j]
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) {r : ℕ}
    (f : Fin r → Γ(Y, U))
    (h : (RingHom.ker (j.app U).hom).map (Y.presheaf.map (homOfLE hVU).op).hom =
      (Ideal.span (Set.range f)).map (Y.presheaf.map (homOfLE hVU).op).hom) :
    RingHom.ker (j.app V).hom =
      Ideal.span (Set.range fun k => Y.presheaf.map (homOfLE hVU).op (f k)) := by
  have hmap : (RingHom.ker (j.app U).hom).map (Y.presheaf.map (homOfLE hVU).op).hom =
      RingHom.ker (j.app V).hom := by
    have hki := j.ker.map_ideal (U := (⟨V, hV⟩ : Y.affineOpens))
      (V := (⟨U, hU⟩ : Y.affineOpens)) hVU
    rwa [Scheme.Hom.ker_apply j (⟨U, hU⟩ : Y.affineOpens),
      Scheme.Hom.ker_apply j (⟨V, hV⟩ : Y.affineOpens)] at hki
  rw [← hmap, h, Ideal.map_span, ← Set.range_comp]
  rfl

section Affine

variable {S Y Z : Scheme.{u}} (g : Y ⟶ S) (j : Z ⟶ Y)

/-- **The quotient of the ring of sections by the defining ideal, over the base.**  For a closed
immersion `j : Z ⟶ Y` of schemes over `S`, an affine open `W` of `S` and an affine open `U` of
`Y` mapping into `W`, the quotient of `Γ(Y, U)` by the kernel of `j.app U` is, as a
`Γ(S, W)`-algebra, the ring of sections of `Z` over `j⁻¹U`. -/
def quotientKerAlgEquiv [IsClosedImmersion j] {W : S.Opens} {U : Y.Opens}
    (hU : IsAffineOpen U) (hUW : U ≤ g ⁻¹ᵁ W) [Algebra Γ(S, W) Γ(Y, U)]
    (halg : ∀ t : Γ(S, W), algebraMap Γ(S, W) Γ(Y, U) t = (g.appLE W U hUW).hom t)
    [Algebra Γ(S, W) Γ(Z, j ⁻¹ᵁ U)]
    (halg' : ∀ t : Γ(S, W), algebraMap Γ(S, W) Γ(Z, j ⁻¹ᵁ U) t =
      ((j ≫ g).appLE W (j ⁻¹ᵁ U) (fun _ hz => hUW hz)).hom t) :
    (Γ(Y, U) ⧸ RingHom.ker (j.app U).hom) ≃ₐ[Γ(S, W)] Γ(Z, j ⁻¹ᵁ U) := by
  refine AlgEquiv.ofRingEquiv (f := quotientDefiningIdealEquiv j hU) fun t => ?_
  have hcomp : (j ≫ g).appLE W (j ⁻¹ᵁ U) (fun _ hz => hUW hz) =
      g.appLE W U hUW ≫ j.app U := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [halg', hcomp, CommRingCat.hom_comp, RingHom.comp_apply, ← halg t]
  rfl

/-- **Flatness of the quotient by the defining ideal.**  For a closed immersion `j : Z ⟶ Y` of
schemes over `S` with `Z ⟶ S` flat, an affine open `W` of `S` and an affine open `U` of `Y`
mapping into `W`, the quotient of `Γ(Y, U)` by the kernel of `j.app U` is flat over
`Γ(S, W)`. -/
theorem flat_quotient_ker_of_flat_comp [IsClosedImmersion j] [Flat (j ≫ g)]
    {W : S.Opens} (hW : IsAffineOpen W) {U : Y.Opens} (hU : IsAffineOpen U)
    (hUW : U ≤ g ⁻¹ᵁ W) [Algebra Γ(S, W) Γ(Y, U)]
    (halg : ∀ t : Γ(S, W), algebraMap Γ(S, W) Γ(Y, U) t = (g.appLE W U hUW).hom t) :
    Module.Flat Γ(S, W) (Γ(Y, U) ⧸ RingHom.ker (j.app U).hom) := by
  let _ : Algebra Γ(S, W) Γ(Z, j ⁻¹ᵁ U) :=
    ((j ≫ g).appLE W (j ⁻¹ᵁ U) (fun _ hz => hUW hz)).hom.toAlgebra
  have : Module.Flat Γ(S, W) Γ(Z, j ⁻¹ᵁ U) :=
    (j ≫ g).flat_appLE hW (hU.preimage j) (fun _ hz => hUW hz)
  exact Module.Flat.of_linearEquiv
    (quotientKerAlgEquiv g j hU hUW halg (fun _ => rfl)).toLinearEquiv

/-- **The affine-local step.**  Let `g : Y ⟶ S` be flat and locally of finite presentation and
let `j : Z ⟶ Y` be a closed immersion with `Z ⟶ S` flat and with finitely generated defining
ideal.  Suppose that over every compatible pair of affine opens, at every prime containing the
defining ideal, the defining ideal is cut out on the fibre over the base by a regular sequence of
its own members.  Then every point of `Y` has an affine open neighbourhood over which the
defining ideal is generated by a family weakly regular in the ring of sections. -/
theorem exists_affineOpen_isWeaklyRegular_generators_of_isRegular_fibre [IsClosedImmersion j]
    [Flat g] [LocallyOfFinitePresentation g] [Flat (j ≫ g)]
    (hfg : ∀ (W : S.Opens), IsAffineOpen W → ∀ (U : Y.Opens), IsAffineOpen U →
      U ≤ g ⁻¹ᵁ W → (RingHom.ker (j.app U).hom).FG)
    (hfib : ∀ (W : S.Opens) (_ : IsAffineOpen W) (U : Y.Opens) (_ : IsAffineOpen U)
      (hUW : U ≤ g ⁻¹ᵁ W) (q : Ideal Γ(Y, U)) (_ : q.IsPrime),
        RingHom.ker (j.app U).hom ≤ q →
        letI : Algebra Γ(S, W) Γ(Y, U) := (g.appLE W U hUW).hom.toAlgebra
        ∃ (r : ℕ) (f : Fin r → Γ(Y, U)),
          (∀ i, f i ∈ RingHom.ker (j.app U).hom) ∧
          IsRegular (Localization.AtPrime q ⧸
              (q.comap (algebraMap Γ(S, W) Γ(Y, U))).map
                (algebraMap Γ(S, W) (Localization.AtPrime q)))
            (List.ofFn fun i => algebraMap Γ(Y, U) (Localization.AtPrime q) (f i)) ∧
          (RingHom.ker (j.app U).hom).map (algebraMap Γ(Y, U) (Localization.AtPrime q)) ≤
            (Ideal.span (Set.range f)).map (algebraMap Γ(Y, U) (Localization.AtPrime q)) ⊔
              (q.comap (algebraMap Γ(S, W) Γ(Y, U))).map
                (algebraMap Γ(S, W) (Localization.AtPrime q)))
    (x : Y) :
    ∃ (V : Y.Opens) (_hV : IsAffineOpen V) (_hxV : x ∈ V) (s : ℕ) (c : Fin s → Γ(Y, V)),
      IsGeneratedByOn Y.toRingedSpace (definingIdealOfHom j) V c ∧
        IsWeaklyRegular Γ(Y, V) (List.ofFn c) := by
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g.base x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show x ∈ g ⁻¹ᵁ W from hxW)
  let _ : Algebra Γ(S, W) Γ(Y, U) := (g.appLE W U hUW).hom.toAlgebra
  have : Module.Flat Γ(S, W) Γ(Y, U) := g.flat_appLE hW hU hUW
  have : Algebra.FinitePresentation Γ(S, W) Γ(Y, U) := g.finitePresentation_appLE hW hU hUW
  set q : Ideal Γ(Y, U) := (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).asIdeal
  have hqp : q.IsPrime := (hU.primeIdealOf (⟨x, hxU⟩ : ↥U)).isPrime
  -- a section outside `q` is invertible at `x`
  have hmem : ∀ t : Γ(Y, U), t ∉ q → x ∈ Y.basicOpen t := by
    intro t ht
    let _ := Y.presheaf.algebra_section_stalk (⟨x, hxU⟩ : ↥U)
    have := hU.isLocalization_stalk (⟨x, hxU⟩ : ↥U)
    have hunit : IsUnit (algebraMap Γ(Y, U) (Y.presheaf.stalk x) t) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ q t).mpr ht
    rw [Y.mem_basicOpen t x hxU]
    exact hunit
  by_cases hIq : RingHom.ker (j.app U).hom ≤ q
  · -- the two ring-level spreadings out apply
    obtain ⟨r, f, hfI, hfibreg, hfibsup⟩ := hfib W hW U hU hUW q hqp hIq
    obtain ⟨g₁, hg₁, hwr, -⟩ := exists_notMem_isWeaklyRegular_and_flat_quotient_away
      (A := Γ(S, W)) q f (fun i => hIq (hfI i)) hfibreg
    obtain ⟨g₂, hg₂, heq⟩ := exists_notMem_map_eq_map_away (A := Γ(S, W)) q
      (Ideal.span (Set.range f)) (RingHom.ker (j.app U).hom)
      (Ideal.span_le.mpr (Set.range_subset_iff.mpr hfI))
      (Submodule.fg_span (Set.finite_range f)) (hfg W hW U hU hUW)
      (flat_quotient_map_atPrime _ q (flat_quotient_ker_of_flat_comp g j hW hU hUW fun _ => rfl))
      hfibsup
    -- the affine open `D(g₁) ∩ D(g₂)`, written as a basic open of `D(g₁)`
    set V₁ : Y.Opens := Y.basicOpen g₁
    have hV₁ : IsAffineOpen V₁ := hU.basicOpen g₁
    have hV₁U : V₁ ≤ U := Y.basicOpen_le g₁
    set t : Γ(Y, V₁) := Y.presheaf.map (homOfLE hV₁U).op g₂
    have hV : IsAffineOpen (Y.basicOpen t) := hV₁.basicOpen t
    have hVV₁ : Y.basicOpen t ≤ V₁ := Y.basicOpen_le t
    have hVU : Y.basicOpen t ≤ U := hVV₁.trans hV₁U
    have hVbo : Y.basicOpen t = V₁ ⊓ Y.basicOpen g₂ := Y.basicOpen_res g₂ (homOfLE hV₁U).op
    have hVV₂ : Y.basicOpen t ≤ Y.basicOpen g₂ := hVbo.le.trans inf_le_right
    refine ⟨Y.basicOpen t, hV, hVbo ▸ ⟨hmem g₁ hg₁, hmem g₂ hg₂⟩, r,
      fun k => Y.presheaf.map (homOfLE hVU).op (f k), ?_, ?_⟩
    · -- generation: part (2), restricted from `D(g₂)`
      refine isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span j hV _
        (ker_app_eq_span_range_res j hU hV hVU f ?_)
      have heq₂ : (RingHom.ker (j.app U).hom).map
            (Y.presheaf.map (homOfLE (Y.basicOpen_le g₂)).op).hom =
          (Ideal.span (Set.range f)).map
            (Y.presheaf.map (homOfLE (Y.basicOpen_le g₂)).op).hom := by
        have hloc := hU.isLocalization_basicOpen g₂
        set e := IsLocalization.algEquiv (Submonoid.powers g₂) (Localization.Away g₂)
          Γ(Y, Y.basicOpen g₂)
        have hcomp : ((e : Localization.Away g₂ →+* Γ(Y, Y.basicOpen g₂))).comp
            (algebraMap Γ(Y, U) (Localization.Away g₂)) =
            algebraMap Γ(Y, U) Γ(Y, Y.basicOpen g₂) := RingHom.ext fun z => e.commutes z
        have hmapped := congrArg
          (Ideal.map (e : Localization.Away g₂ →+* Γ(Y, Y.basicOpen g₂))) heq
        rw [Ideal.map_map, Ideal.map_map, hcomp.trans (RingHom.algebraMap_toAlgebra _)] at hmapped
        exact hmapped
      rw [← map_res_res (Y.basicOpen_le g₂) hVV₂ hVU, ← map_res_res (Y.basicOpen_le g₂) hVV₂ hVU,
        heq₂]
    · -- weak regularity: part (1), restricted from `D(g₁)`
      have hwr₂ := isWeaklyRegular_res_basicOpen hV₁ t rfl hVV₁ _
        (isWeaklyRegular_res_basicOpen_of_away hU g₁ f hwr)
      have hres : ∀ k, Y.presheaf.map (homOfLE hVV₁).op (Y.presheaf.map (homOfLE hV₁U).op (f k)) =
          Y.presheaf.map (homOfLE hVU).op (f k) := by
        intro k
        rw [← CommRingCat.comp_apply, presheaf_map_homOfLE_comp]
      simpa only [hres] using hwr₂
  · -- a section of the defining ideal is invertible at `x`
    obtain ⟨t, htI, htq⟩ := SetLike.not_le_iff_exists.mp hIq
    refine ⟨Y.basicOpen t, hU.basicOpen t, hmem t htq, 1, fun _ => 1, fun V' hV' => ?_, ?_⟩
    · rw [definingIdealOfHom_obj_eq_top_of_mem_ker j t htI hV',
        generatedIdealOn_one_obj_eq_top hV']
    · have h1 : (List.ofFn fun _ : Fin 1 => (1 : Γ(Y, Y.basicOpen t))) = [1] := by simp
      rw [h1]
      exact IsWeaklyRegular.cons (IsSMulRegular.one _) (IsWeaklyRegular.nil _ _)

/-- **The scheme-level half of Stacks 063W.**  Let `g : Y ⟶ S` be flat and locally of finite
presentation and let `j : Z ⟶ Y` be a closed immersion with `Z ⟶ S` flat and with finitely
generated defining ideal.  If the defining ideal is cut out on the fibres over the base by
regular sequences of its own members, then it is a regular ideal sheaf. -/
theorem isRegularIdealSheaf_definingIdealOfHom_of_isRegular_fibre [IsClosedImmersion j]
    [Flat g] [LocallyOfFinitePresentation g] [Flat (j ≫ g)]
    (hfg : ∀ (W : S.Opens), IsAffineOpen W → ∀ (U : Y.Opens), IsAffineOpen U →
      U ≤ g ⁻¹ᵁ W → (RingHom.ker (j.app U).hom).FG)
    (hfib : ∀ (W : S.Opens) (_ : IsAffineOpen W) (U : Y.Opens) (_ : IsAffineOpen U)
      (hUW : U ≤ g ⁻¹ᵁ W) (q : Ideal Γ(Y, U)) (_ : q.IsPrime),
        RingHom.ker (j.app U).hom ≤ q →
        letI : Algebra Γ(S, W) Γ(Y, U) := (g.appLE W U hUW).hom.toAlgebra
        ∃ (r : ℕ) (f : Fin r → Γ(Y, U)),
          (∀ i, f i ∈ RingHom.ker (j.app U).hom) ∧
          IsRegular (Localization.AtPrime q ⧸
              (q.comap (algebraMap Γ(S, W) Γ(Y, U))).map
                (algebraMap Γ(S, W) (Localization.AtPrime q)))
            (List.ofFn fun i => algebraMap Γ(Y, U) (Localization.AtPrime q) (f i)) ∧
          (RingHom.ker (j.app U).hom).map (algebraMap Γ(Y, U) (Localization.AtPrime q)) ≤
            (Ideal.span (Set.range f)).map (algebraMap Γ(Y, U) (Localization.AtPrime q)) ⊔
              (q.comap (algebraMap Γ(S, W) Γ(Y, U))).map
                (algebraMap Γ(S, W) (Localization.AtPrime q))) :
    IsRegularIdealSheaf Y.toRingedSpace (definingIdealOfHom j) :=
  RegularIdealSheaf.isRegularIdealSheaf_of_exists_affine_generators Y _ fun x _ =>
    exists_affineOpen_isWeaklyRegular_generators_of_isRegular_fibre g j hfg hfib x

end Affine

end Stacks.AlgebraicGeometry

end
