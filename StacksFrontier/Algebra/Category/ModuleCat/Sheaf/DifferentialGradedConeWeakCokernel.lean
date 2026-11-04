module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting

/-!
# Cancelling a quasi-isomorphism from the left on morphisms into a K-injective module

Let `X` be a ringed site, let `A` be a sheaf of differential graded algebras on it, and let `I`
be a right differential graded `A`-module that is K-injective and graded injective. Tag 0FSX,
`SheafOfModules.DifferentialGradedModule.exists_homotopic_lift_of_quasiIso`, says that
precomposition with a quasi-isomorphism `b : M ⟶ M'` is surjective on homotopy classes of
morphisms into `I`. Proved here is the complementary *injectivity* statement: a morphism
`M' ⟶ I` whose composite with `b` is homotopic to zero is itself homotopic to zero, and hence
`b` can be cancelled from the left in a homotopy between two morphisms `M' ⟶ I`.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopic_zero_of_comp_homotopic_zero`: the
  companion uniqueness statement, that a morphism into `I` whose composite with a
  quasi-isomorphism is homotopic to zero is itself homotopic to zero.
* `SheafOfModules.DifferentialGradedModule.homotopic_of_comp_homotopic`: the same statement in
  its two-morphism form, that a quasi-isomorphism can be cancelled from the left in a homotopy
  between morphisms into `I`.
* `SheafOfModules.DifferentialGradedModule.IsKInjective.homotopic_zero_of_comp_homotopic_zero`
  and `SheafOfModules.DifferentialGradedModule.IsKInjective.homotopic_of_comp_homotopic`: the
  same two statements for a K-injective `I` which need not be graded injective.

## Implementation notes

The argument is the cone argument of Tag 0FSX run in the other direction. A null homotopy of
`b ≫ d` is exactly the data needed by `HomologicalComplex.homotopyCofiber.desc` to extend `d`
over the cone of `b`, which gives the factorisation `exists_cone_factorisation` of `d` through
the canonical inclusion `M' ⟶ cone b`. The cone of a quasi-isomorphism is acyclic, by
`SheafOfModules.DifferentialGradedModule.acyclic_cone_iff_quasiIso`, so every morphism out of it
into the K-injective `I` is homotopic to zero; `d` is therefore homotopic to zero as well. As
for Tag 0FSX, graded injectivity of `I` is not used: the two statements are proved for a
K-injective `I` as `IsKInjective.homotopic_zero_of_comp_homotopic_zero` and
`IsKInjective.homotopic_of_comp_homotopic`, and the versions carrying graded injectivity, the
hypothesis of the source, are read off them.

What has to be checked by hand is that the extension produced by `desc` — a morphism of
complexes — is action-linear, so a morphism of differential graded modules. The check is
degreewise on the two summands of the cone: on the second summand it is the action-linearity of
`d`, and on the first it is the action-linearity of the null homotopy. Both are read through the
degreewise splitting of the cone recorded by
`SheafOfModules.DifferentialGradedModule.ConePackage`, whose first and second projections are
`fstX` and `sndX` of `HomologicalComplex.homotopyCofiber`.

## References

* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-! ### Transport lemmas -/

/-- The second projection out of a mapping cone, spelled through the degreewise splitting. -/
private lemma sndX_eq
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.sndX φ n =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) (up_rel rfl)).hom ≫
        biprod.snd := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X φ (n + 1) n (up_rel rfl)
  · rw [HomologicalComplex.homotopyCofiber.inlX_sndX, ← Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom, biprod.inl_snd]
  · rw [HomologicalComplex.homotopyCofiber.inrX_sndX, ← Category.assoc,
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom, biprod.inr_snd]

/-! ### Factorisation of a morphism through a cone -/

/-- A morphism `d : M' ⟶ I` whose composite with `b : M ⟶ M'` is null homotopic factors
through the inclusion of `M'` into the cone of `b`. -/
private theorem exists_cone_factorisation {M M' I : DifferentialGradedModule.{u, v, w} A}
    {b : M ⟶ M'} (P : ConePackage b) {d : M' ⟶ I} (hd : Homotopic (b ≫ d) 0) :
    ∃ e : P.cone ⟶ I, P.inclusion ≫ e = d := by
  obtain ⟨H⟩ := hd
  rcases P with ⟨⟨Cc, cm, ca, co, cd⟩, inc, proj, hC, ciso, hciso, hfst, hsnd, hinc, hproj⟩
  dsimp only at hC
  have hC' : Cc = HomologicalComplex.homotopyCofiber b.toHomologicalComplex := hC
  subst hC'
  have hciso' : ciso = fun n => HomologicalComplex.homotopyCofiber.XIsoBiprod
      b.toHomologicalComplex n (n + 1) (up_rel rfl) :=
    funext (fun n => eq_of_heq (hciso n))
  subst ciso
  have hinc' : inc.toHomologicalComplex =
      HomologicalComplex.homotopyCofiber.inr b.toHomologicalComplex := eq_of_heq hinc
  let hcomp : _root_.Homotopy (b.toHomologicalComplex ≫ d.toHomologicalComplex)
      (0 : M.complex ⟶ I.complex) := H.toComplexHomotopy
  have hhom (k : ℤ) : hcomp.hom (k + 1) k =
      H.app (k + 1) ≫ eqToHom (congrArg I.complex.X (show k + 1 - 1 = k by omega)) :=
    dite_eq_left rfl
  let ec : HomologicalComplex.homotopyCofiber b.toHomologicalComplex ⟶ I.complex :=
    HomologicalComplex.homotopyCofiber.desc b.toHomologicalComplex
      d.toHomologicalComplex hcomp
  have hdesc (k : ℤ) :
      ec.f k =
        HomologicalComplex.homotopyCofiber.fstX b.toHomologicalComplex k (k + 1)
            (up_rel rfl) ≫
          (H.app (k + 1) ≫
            eqToHom (congrArg I.complex.X (show k + 1 - 1 = k by omega))) +
        HomologicalComplex.homotopyCofiber.sndX b.toHomologicalComplex k ≫
          d.toHomologicalComplex.f k := by
    rw [show ec = _ from rfl,
      HomologicalComplex.homotopyCofiber.desc_f b.toHomologicalComplex _ hcomp k (k + 1)
        (up_rel rfl), hhom k]
  refine ⟨{ toHomologicalComplex := ec, map_mul := ?_ }, ?_⟩
  · intro n i U x y
    dsimp only
    rw [hdesc, hdesc, add_val_app, add_val_app, map_add, AddMonoidHom.add_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [comp_val_app, comp_val_app, comp_val_app, comp_val_app]
      refine eq_of_heq ?_
      refine (sheaf_eqToHom_apply_heq
        (congrArg I.complex.X (show n + i + 1 - 1 = n + i by omega)) U
        ((H.app (n + i + 1)).val.app U _)).trans ?_
      refine (heq_dependent_apply
        (fun k (t : (M.complex.X k).val.obj U) => (H.app k).val.app U t)
        (show n + i + 1 = n + 1 + i by omega) (hfst n i U x y)).trans ?_
      refine (H.map_mul (n + 1) i U _ y).trans ?_
      refine gradedBilinear_apply_heq
        (B := fun k => (I.complex.X k).val.obj U)
        (D := fun k => (I.complex.X k).val.obj U)
        (show n + 1 - 1 = n by omega) (show n + 1 - 1 + i = n + i by omega)
        (congr_arg_heq (fun k => (I.mul k i).app U) (show n + 1 - 1 = n by omega))
        (sheaf_eqToHom_apply_heq (congrArg I.complex.X (show n + 1 - 1 = n by omega)) U
          ((H.app (n + 1)).val.app U _)).symm y
    · rw [comp_val_app, comp_val_app, sndX_eq, sndX_eq, hsnd n i U x y]
      exact d.map_mul n i U _ y
  · refine Hom.ext fun k => ?_
    have hk : inc.toHomologicalComplex.f k ≫ ec.f k = d.toHomologicalComplex.f k := by
      rw [hinc']
      simp only [HomologicalComplex.homotopyCofiber.inr_f]
      exact HomologicalComplex.homotopyCofiber.inrX_desc_f b.toHomologicalComplex
        d.toHomologicalComplex hcomp k
    exact hk

/-! ### Cancelling a quasi-isomorphism from the left -/

section Abelian

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Let `I` be a K-injective right differential graded module. A morphism `d : M' ⟶ I` whose
composite with a quasi-isomorphism `b : M ⟶ M'` is homotopic to zero is itself homotopic to
zero. -/
theorem IsKInjective.homotopic_zero_of_comp_homotopic_zero
    {M M' I : DifferentialGradedModule.{u, v, w} A} (hI : IsKInjective I)
    {b : M ⟶ M'} (hb : QuasiIso b.toHomologicalComplex)
    (d : M' ⟶ I) (hd : Homotopic (b ≫ d) 0) : Homotopic d 0 := by
  obtain ⟨e, he⟩ := exists_cone_factorisation (conePackage b) hd
  have hz : (HomotopyCategory.quotient A).map e =
      (HomotopyCategory.quotient A).map (0 : cone b ⟶ I) :=
    (hI (cone b) ((acyclic_cone_iff_quasiIso _ b).2 hb)).elim _ _
  refine (HomotopyCategory.quotient_map_eq_iff d 0).mp ?_
  rw [← he, Functor.map_comp, hz, ← Functor.map_comp, comp_zero]

/-- Two morphisms into a K-injective right differential graded module whose composites with a
quasi-isomorphism are homotopic are themselves homotopic. -/
theorem IsKInjective.homotopic_of_comp_homotopic
    {M M' I : DifferentialGradedModule.{u, v, w} A} (hI : IsKInjective I)
    {b : M ⟶ M'} (hb : QuasiIso b.toHomologicalComplex)
    (c c' : M' ⟶ I) (hcc : Homotopic (b ≫ c) (b ≫ c')) : Homotopic c c' := by
  rw [← homotopic_sub_zero_iff]
  refine hI.homotopic_zero_of_comp_homotopic_zero hb (c - c') ?_
  rw [Preadditive.comp_sub]
  exact (homotopic_sub_zero_iff _ _).mpr hcc

/-- Let `I` be a K-injective and graded injective right differential graded module. A morphism
`d : M' ⟶ I` whose composite with a quasi-isomorphism `b : M ⟶ M'` is homotopic to zero is
itself homotopic to zero. -/
theorem homotopic_zero_of_comp_homotopic_zero
    {M M' I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (_hI' : GradedInjective I)
    {b : M ⟶ M'} (hb : QuasiIso b.toHomologicalComplex)
    (d : M' ⟶ I) (hd : Homotopic (b ≫ d) 0) : Homotopic d 0 :=
  hI.homotopic_zero_of_comp_homotopic_zero hb d hd

/-- Two morphisms into a K-injective and graded injective right differential graded module whose
composites with a quasi-isomorphism are homotopic are themselves homotopic. -/
theorem homotopic_of_comp_homotopic
    {M M' I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (_hI' : GradedInjective I)
    {b : M ⟶ M'} (hb : QuasiIso b.toHomologicalComplex)
    (c c' : M' ⟶ I) (hcc : Homotopic (b ≫ c) (b ≫ c')) : Homotopic c c' :=
  hI.homotopic_of_comp_homotopic hb c c' hcc

end Abelian

end SheafOfModules.DifferentialGradedModule

end
