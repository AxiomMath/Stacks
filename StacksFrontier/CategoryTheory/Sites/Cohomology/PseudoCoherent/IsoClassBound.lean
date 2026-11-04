module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseRestrictionCode
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DenseSpanApproximation

/-!
# Pseudo-coherent objects on a ringed site with a small dense family are few

Let `(C, O)` be a ringed site and `c : ι → C` a dense family of objects (every object is
covered by arrows from the `c i`), and suppose the family, the arrows between its members and
the rings of sections of `O` over them are bounded by an infinite cardinal `ν`.  Then every
pseudo-coherent complex of `O`-modules (Stacks 08FT) receives a quasi-isomorphism from a member
of one family of complexes indexed by a type of cardinality at most `2 ^ 2 ^ ν`; so the
pseudo-coherent objects of `D(O)` fall into at most `2 ^ 2 ^ ν` isomorphism classes.

## The argument

A pseudo-coherent complex `K` is approximated, locally and in every range of degrees, by
strictly perfect complexes, whose sections over the family are bounded by `ν`
(`mk_sections_le_of_isStrictlyPerfect`).  The images of these sections, together with chosen
primitives of the boundaries in their span, enlarged countably often, are `ν` generators whose
local span is a subcomplex `K'` of `K`
(`Stacks.SheafOfModules.DenseSpan.subcomplex`); the inclusion is a quasi-isomorphism
(`Stacks.SheafOfModules.DenseSpan.quasiIso_incl`), the approximations giving surjectivity
on cohomology and the primitives injectivity.  The sections of `K'` over the family are bounded
by `2 ^ ν` (`Stacks.SheafOfModules.DenseSpan.injective_restrictSpan`), and a complex is
determined up to isomorphism by those sections with their structure
(`Stacks.SheafOfModules.DenseCode.nonempty_iso_of_code_eq`), of which there are at most
`2 ^ 2 ^ ν` codes (`Stacks.SheafOfModules.DenseCode.mk_code_le`).

## Main results

* `AlgebraicGeometry.RingedSite.exists_family_quasiIso_of_isPseudoCoherentComplex`: the family
  of complexes.
* `AlgebraicGeometry.RingedSite.exists_family_iso_of_isPseudoCoherent`: the family of objects
  of the derived category, at any model of it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.SheafOfModules.DenseSpan Stacks.SheafOfModules.DenseCode

universe d t u'

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u', t, t})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{t}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})]
  [HasSheafify X.J AddCommGrpCat.{t}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {ι : Type t} (c : ι → X.C) [hc : (inducedFunctor c).IsCoverDense X.J]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
include hc in
/-- **Every pseudo-coherent complex receives a quasi-isomorphism from one of at most
`2 ^ 2 ^ ν` complexes.** -/
theorem exists_family_quasiIso_of_isPseudoCoherentComplex {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν)
    (hι : #ι ≤ ν) (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν)
    (hO : ∀ i : ι, #(X.O.obj.obj (op (c i))) ≤ ν) :
    ∃ (Cd : Type t) (F : Cd → CochainComplex
        (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
      #Cd ≤ (2 : Cardinal.{t}) ^ (2 : Cardinal.{t}) ^ ν ∧
      ∀ K : CochainComplex (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        X.IsPseudoCoherentComplex K → ∃ (a : Cd) (φ : F a ⟶ K), QuasiIso φ := by
  classical
  let L : Type t := (2 ^ ν : Cardinal.{t}).out
  have hL : #L = 2 ^ ν := Cardinal.mk_out _
  have h2ν : ℵ₀ ≤ 2 ^ ν := hν.trans (Cardinal.cantor ν).le
  have hνle : ν ≤ 2 ^ ν := (Cardinal.cantor ν).le
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let F : Code (R := R) c L → CochainComplex (SheafOfModules.{t} R) ℤ := fun a =>
    if h : ∃ (M : CochainComplex (SheafOfModules.{t} R) ℤ)
        (e : ∀ (n : ℤ) (i : ι), (M.X n).val.obj (op (c i)) → L),
        (∀ n i, Function.Injective (e n i)) ∧ code M e = a then h.choose
    else HomologicalComplex.zero
  refine ⟨Code (R := R) c L, F, ?_, fun K hK => ?_⟩
  · exact mk_code_le h2ν hL.le (hι.trans hνle) (fun i j => (hHom j i).trans hνle)
      (fun i => (hO i).trans hνle)
  obtain ⟨A⟩ := nonempty_denseApproximation (c := c) hK
  have hGd := isDClosed_enlargement A.gens
  have hG : #(enlargement A.gens) ≤ ν :=
    mk_enlargement_le hν hι hHom hO _ (A.mk_gens_le hν hι hHom hO)
  have hq : QuasiIso (incl hGd) :=
    quasiIso_incl hGd (A.hasLocalHomology _ (subset_enlargement _))
      (exists_mem_closure_d_eq_of_enlargement _)
  have hsec : ∀ (n : ℤ) (i : ι),
      #(((subcomplex hGd).X n).val.obj (op (c i))) ≤ #L := by
    intro n i
    rw [hL]
    refine (Cardinal.mk_le_of_injective (injective_restrictSpan (c := c) n i)).trans ?_
    refine mk_pi_le_two_power hν (mk_sigma_le_of_le hν hι (fun j => hHom j i)) (fun a => ?_)
    rw [Cardinal.mk_option]
    exact (Cardinal.add_le_of_le hν (mk_span_obj_le _ hν hG hι hHom hO n a.1)
      (Cardinal.one_le_aleph0.trans hν)).trans hνle
  let e : ∀ (n : ℤ) (i : ι), ((subcomplex hGd).X n).val.obj (op (c i)) ↪ L :=
    fun n i => Classical.choice ((Cardinal.le_def _ _).1 (hsec n i))
  have hex : ∃ (M : CochainComplex (SheafOfModules.{t} R) ℤ)
      (e' : ∀ (n : ℤ) (i : ι), (M.X n).val.obj (op (c i)) → L),
      (∀ n i, Function.Injective (e' n i)) ∧ code M e' = code (subcomplex hGd) (fun n i => e n i) :=
    ⟨_, fun n i => e n i, fun n i => (e n i).injective, rfl⟩
  have hF : F (code (subcomplex hGd) (fun n i => e n i)) = hex.choose := dif_pos hex
  obtain ⟨iso⟩ := nonempty_iso_of_code_eq (c := c) _ _ hex.choose_spec.choose_spec.1
    (fun n i => (e n i).injective) hex.choose_spec.choose_spec.2
  exact ⟨_, eqToHom hF ≫ iso.hom ≫ incl hGd, inferInstance⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{t} AddCommGrpCat.{t})] in
include hc in
/-- **The pseudo-coherent objects of `D(O)` fall into at most `2 ^ 2 ^ ν` isomorphism
classes**, at any model of the derived category. -/
theorem exists_family_iso_of_isPseudoCoherent
    [HasDerivedCategory.{d} (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν) (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν)
    (hO : ∀ i : ι, #(X.O.obj.obj (op (c i))) ≤ ν) :
    ∃ (Cd : Type t) (F : Cd → DerivedCategory
        (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      #Cd ≤ (2 : Cardinal.{t}) ^ (2 : Cardinal.{t}) ^ ν ∧
      ∀ E, X.IsPseudoCoherent E → ∃ a : Cd, Nonempty (F a ≅ E) := by
  obtain ⟨Cd, F, hCd, hF⟩ :=
    exists_family_quasiIso_of_isPseudoCoherentComplex X c hν hι hHom hO
  refine ⟨Cd, fun a => DerivedCategory.Q.obj (F a), hCd, fun E hE => ?_⟩
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨a, φ, hφ⟩ := hF K hK
  have : IsIso (DerivedCategory.Q.map φ) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)).2 hφ
  exact ⟨a, ⟨asIso (DerivedCategory.Q.map φ) ≪≫ eK⟩⟩

end AlgebraicGeometry.RingedSite
