module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorUnitFactor
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The interchange morphism at a single-degree trivialised tensor factor

Let `X` be a ringed site, let `A` be a cochain complex of `O`-modules vanishing outside a single
degree `k` and with `A^k ≅ O`, and let `I` and `N` be arbitrary cochain complexes of `O`-modules.
The interchange morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is then an isomorphism. That is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_isIso_of_unitTensorFactor`, and it is the base
case of the dévissage of Stacks 0ATN part (2) on the tensor factor — the counterpart of
`tensorHomInterchange_single_quasiIso_of_unitPower`, which is the same step for part (1), where
the single-degree complex is the source of the internal Hom instead.

The argument is componentwise, and that is what keeps it free of signs: the interchange morphism
is already a morphism of complexes, so it is an isomorphism as soon as each of its components is,
and the Koszul signs of the total complex only ever enter in commuting with differentials. Each
component is shown bijective on sections. The source is first collapsed by
`tensorTotalUnitFactorIso`, after which both sides are degree terms of internal Hom complexes,
whose sections are cochains by `SheafHomComplex.sectionsEquiv` — a plain family of components,
with no cocycle condition, so a cochain may be built from an arbitrary family. Injectivity and
surjectivity then both come from the evaluation formula
`applyHomSectionOver_interchange_collAt_inv`, which says that the comparison acts on evaluations
as the collapse applied componentwise.

## Implementation notes

The proofs are in term mode, against explicitly applied equations, rather than by rewriting. The
reason is documented at
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/ExtensionByZeroTensor.lean`,
lines 47-58: several reducible abbreviations for the structure sheaf of rings are in circulation,
and a reducible abbreviation does not unfold at `implicit` transparency, so a goal mixing two of
them is not type-correct there and `rw` refuses to build a motive for it. Term-mode application
checks at default transparency and is unaffected.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

variable {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (k : ℤ) (e : A.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (hA : ∀ p, p ≠ k → IsZero (A.X p))

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The collapse of the total tensor complex at a single-degree tensor factor, with the two
degrees given independently.** This is `tensorTotalUnitFactorIso` with the degree of `Y` supplied
as a variable `q` together with `k + q = c` rather than computed as `c - k`.

The interchange morphism of Stacks 0BYR is described on local pure tensors
(`tensorHomInterchange_applyHomSectionOver`) at the total degree spelled literally `p + q`, so a
comparison with the collapse at a degree spelled `c - k` is not type-correct without a cast. This
variant carries the cast once, here, and nothing below has to mention it. -/
private def collAt
    (Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (q c : ℤ) (h : k + q = c) : (tensorTotal X A Y).X c ≅ Y.X q :=
  tensorTotalUnitFactorIso X k e hA c ≪≫ Y.XIsoOfEq (by omega : c - k = q)

/-- **The free-degree collapse sends a section to the local pure tensor with the trivialising
section**, which is `tensorTotalUnitFactorIso_inv_apply` read at independent degrees. -/
private lemma collAt_inv_apply
    (Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (q c : ℤ) (h : k + q = c) (W : X.C) (y : (Y.X q).val.obj (op W)) :
    (collAt X k e hA Y q c h).inv.val.app (op W) y =
      tensorTotalSectionAt X A Y W k q c h
        (e.inv.val.app (op W)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) y := by
  obtain rfl : q = c - k := by omega
  exact tensorTotalUnitFactorIso_inv_apply X k e hA c W y

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The section of `A^k` corresponding to `1` restricts to the section corresponding to `1`.**
The trivialisation is a morphism of sheaves, so it commutes with restriction, and the restriction
maps of the structure sheaf preserve `1`. -/
public lemma restrictSection_unitSection {V W : X.C} (i : W ⟶ V) :
    restrictSection X i
        (e.inv.val.app (op V) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))) =
      e.inv.val.app (op W) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) :=
  (restrictSection_natural X e.inv i
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))).trans
    (congrArg (fun z => e.inv.val.app (op W) z)
      (map_one (RingCat.Hom.hom ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map i.op))))

/-- **The interchange morphism, read on a section of the collapsed source.** Evaluating the
interchange morphism at a section coming from the collapse, on a section `m` of `N`, gives the
image under the collapse of the evaluation of the original section on `m`.

This is the whole computation of the base case of Stacks 0ATN part (2): the left-hand side is the
comparison, and the right-hand side is the collapse applied componentwise. It is
`tensorHomInterchange_applyHomSectionOver` fed with the fact that the section of the collapsed
source is a local pure tensor, and the restriction of the trivialising section. -/
private lemma applyHomSectionOver_interchange_collAt_inv
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (q c : ℤ) (h : k + q = c) (V W : X.C) (i : W ⟶ V) (a s b : ℤ)
    (has : a + q = s) (hsb : s + k = b)
    (y : (((sheafHomComplex X N I).obj).X q).val.obj (op V))
    (m : (N.X a).val.obj (op W)) :
    applyHomSectionOver X (sheafHomComplex X N (tensorTotal X A I)) V W i c a b (by omega)
        (((tensorHomInterchange X A I N).f c).val.app (op V)
          ((collAt X k e hA ((sheafHomComplex X N I).obj) q c h).inv.val.app (op V) y)) m =
      (collAt X k e hA I s b (by omega)).inv.val.app (op W)
        (applyHomSectionOver X (sheafHomComplex X N I) V W i q a s has y m) := by
  subst h
  rw [collAt_inv_apply, collAt_inv_apply]
  exact (tensorHomInterchange_applyHomSectionOver X A I N V W i k q a s b has hsb
      (e.inv.val.app (op V)
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))) y m).trans
    (congrArg (fun z => tensorTotalSectionAt X A I W k s b (by omega) z
        (applyHomSectionOver X (sheafHomComplex X N I) V W i q a s has y m))
      (restrictSection_unitSection X k e i))

/-- **The comparison is injective on sections.** Two sections with the same image have, by the
evaluation formula, evaluations with the same image under the collapse, which is injective; and a
section of an internal Hom complex is determined by its evaluations. -/
private lemma injective_interchange_collAt
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (q c : ℤ) (h : k + q = c) (V : X.Cᵒᵖ) :
    Function.Injective (((collAt X k e hA ((sheafHomComplex X N I).obj) q c h).inv ≫
      (tensorHomInterchange X A I N).f c).val.app V) := by
  intro s s' hss
  refine homSection_ext X (sheafHomComplex X N I) V.unop q
    (fun p q' hpq' W i m => ?_)
  have hev := congrArg (fun z =>
    applyHomSectionOver X (sheafHomComplex X N (tensorTotal X A I)) V.unop W i c p (p + c)
      (by omega) z m) hss
  rw [comp_val_app_apply', comp_val_app_apply'] at hev
  rw [applyHomSectionOver_interchange_collAt_inv X k e hA I N q c h V.unop W i p q' (p + c)
      (by omega) (by omega) s m,
    applyHomSectionOver_interchange_collAt_inv X k e hA I N q c h V.unop W i p q' (p + c)
      (by omega) (by omega) s' m] at hev
  exact (bijective_val_app_of_iso X (collAt X k e hA I q' (p + c) (by omega)).symm (op W)).1 hev

/-- **The comparison is surjective on sections.** A section of the target is a cochain into
`Tot(A ⊗_O I)`; composing each of its components with the collapse gives a cochain into `I`,
hence a section of the source, and the evaluation formula identifies its image with the section
one started from. Nothing has to be checked of the constructed cochain, because a cochain is an
arbitrary family of components. -/
private lemma surjective_interchange_collAt
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (q c : ℤ) (h : k + q = c) (V : X.Cᵒᵖ) :
    Function.Surjective (((collAt X k e hA ((sheafHomComplex X N I).obj) q c h).inv ≫
      (tensorHomInterchange X A I N).f c).val.app V) := by
  intro t
  refine ⟨((sheafHomComplex X N I).sectionsEquiv V.unop q).symm
    (CochainComplex.HomComplex.Cochain.mk (fun p q' hpq' =>
      ((sheafHomComplex X N (tensorTotal X A I)).sectionsEquiv V.unop c t).v p (p + c) rfl ≫
        ((collAt X k e hA I q' (p + c) (by omega)).hom.over V.unop))), ?_⟩
  refine homSection_ext X (sheafHomComplex X N (tensorTotal X A I)) V.unop c
    (fun p b hpb W i m => ?_)
  subst hpb
  have hpc : k + (p + q) = p + c := by omega
  rw [comp_val_app_apply',
    applyHomSectionOver_interchange_collAt_inv X k e hA I N q c h V.unop W i p (p + q) (p + c)
      (by omega) (by omega) _ m]
  have hhom : ∀ z, (collAt X k e hA I (p + q) (p + c) hpc).inv.val.app (op W)
      ((collAt X k e hA I (p + q) (p + c) hpc).hom.val.app (op W) z) = z := fun z =>
    congrArg (fun φ => φ.val.app (op W) z) (collAt X k e hA I (p + q) (p + c) hpc).hom_inv_id
  have hsc := congrArg (fun z =>
      (z.v p (p + q) (by omega : p + q = p + q)).val.app (op (Over.mk i)) m)
    (((sheafHomComplex X N I).sectionsEquiv V.unop q).apply_symm_apply
      (CochainComplex.HomComplex.Cochain.mk (fun p' q'' (_ : p' + q = q'') =>
        ((sheafHomComplex X N (tensorTotal X A I)).sectionsEquiv V.unop c t).v p' (p' + c) rfl ≫
          ((collAt X k e hA I q'' (p' + c) (by omega)).hom.over V.unop))))
  exact (congrArg (fun z =>
    (collAt X k e hA I (p + q) (p + c) hpc).inv.val.app (op W) z) hsc).trans (hhom _)

include e hA in
/-- **The interchange morphism of Stacks 0BYR is an isomorphism when the tensor factor is
concentrated in one degree and trivialised there.** If `A` vanishes outside degree `k` and
`A^k ≅ O`, then

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is an isomorphism, for arbitrary `I` and `N`.

This is the base case of the dévissage of Stacks 0ATN part (2) on the tensor factor, the
counterpart of
`AlgebraicGeometry.RingedSite.tensorHomInterchange_single_quasiIso_of_unitPower` for part (1),
and it is an isomorphism rather than merely a quasi-isomorphism. Each component is treated
separately — which is why no sign ever has to be computed, the morphism being already a morphism
of complexes — and shown bijective on sections through the description of the sections of an
internal Hom complex as cochains. -/
theorem tensorHomInterchange_isIso_of_unitTensorFactor
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (tensorHomInterchange X A I N) := by
  have hn : ∀ n, IsIso ((tensorHomInterchange X A I N).f n) := by
    intro n
    have hψ : IsIso ((collAt X k e hA ((sheafHomComplex X N I).obj) (n - k) n (by omega)).inv ≫
        (tensorHomInterchange X A I N).f n) :=
      Stacks.SheafOfModules.isIso_of_bijective_app _ (fun V =>
        ⟨injective_interchange_collAt X k e hA I N (n - k) n (by omega) V,
          surjective_interchange_collAt X k e hA I N (n - k) n (by omega) V⟩)
    have hfac : (tensorHomInterchange X A I N).f n =
        ((collAt X k e hA ((sheafHomComplex X N I).obj) (n - k) n (by omega)) ≪≫
          (@asIso _ _ _ _ _ hψ)).hom := by
      rw [Iso.trans_hom, asIso_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hfac]
    exact Iso.isIso_hom _
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry.RingedSite

end
