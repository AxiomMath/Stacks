module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexIntoASingleComplex
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomDegreeProjectionEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# The differential of the naive dual of a bounded complex

Let `(𝒞, 𝒪)` be a ringed site and let `E` be a bounded complex of `𝒪`-modules. Its **naive
termwise dual** is the internal Hom complex `SheafHom^•(E, 𝒪[0])`, whose degree-`n` term is
identified with `𝓗om(E^{-n}, 𝒪)` by the degreewise collapse
`AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso` of [Stacks, Tag 08DM]. This file
computes its **differential** through that collapse: it is, up to the sign `(-1)^{n+1}`,
precomposition with the differential of `E`.

That is the content that `homStructureSheafDegreeIso` alone does not carry. The collapse is a
degreewise statement, and before this file nothing in the library related the differential of
`SheafHom^•(E, 𝒪[0])` to the differential of `E` for a source concentrated in more than one
degree; the only identifications of a naive dual as a *complex* were for a source concentrated
in a single degree, where the differential vanishes for trivial reasons.

## Main results

* `AlgebraicGeometry.RingedSite.d_comp_homStructureSheafDegreeIso_hom`: **the differential of
  the naive dual is `(-1)^{n+1}` times precomposition with the differential of the source.**

## Implementation notes

The only public handle on the internal Hom complex `SheafHom^•(E, F)` is its characterisation
on sections: the product description `AlgebraicGeometry.RingedSite.homDegreeProjection` with its
value on a section
(`AlgebraicGeometry.RingedSite.homDegreeProjection_app_eq_applyHomSectionOver`), and the Leibniz
rule `AlgebraicGeometry.RingedSite.applyHomSectionOver_differential`. The term, the differential
and the component formula of the differential are all `private` where the complex is built, so
the proof necessarily descends to sections, applies the Leibniz rule there, and comes back by
extensionality. The term of the Leibniz rule involving the differential of the *target* vanishes
because `𝒪[0]` has zero differentials — the same move as in
`AlgebraicGeometry.RingedSite.evalAtOneFun_differential`, which is the covariant analogue of
this statement.

**Where the index bookkeeping goes.** The Leibniz rule produces the source index `-(n+1) + 1`,
while the collapse in degree `n` is stated at `E^{-n}`. These are equal, but not as terms, and
they occur inside the *types* of the sections involved, so no `rw` can bridge them. The bridge
is `applyHomSectionOver_congr_index`: the indices are free variables there, constrained by
equations, so `subst` makes the two sides identical and the transports collapse to identities.
The transport that the use site is left with is
`CategoryTheory.HomologicalComplex.XIsoOfEq`, absorbed into the differential by
`CategoryTheory.HomologicalComplex.d_comp_XIsoOfEq_hom`.

**Why the private evaluation lemmas are stated in the `restrFun` spelling.** A section of
`𝓗om(A, B)` over `U` is a morphism `(restrFun 𝒪 U).obj A.val ⟶ (restrFun 𝒪 U).obj B.val`, and
the same object is also spelled `(A.over U).val`. The two are definitionally equal but not
syntactically, and `rw` matches syntactically; each private lemma below is therefore stated in
the spelling that occurs at its use site, and where a use site has the other spelling the
general lemma is instantiated at an explicit section instead of being matched.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Evaluation of a section of an internal Hom sheaf at a fixed section of the source, as an
additive map in the Hom section. -/
private def evalInternalHomAddHom
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (U : X.C) (W : (Over U)ᵒᵖ) (y : ((restrFun X.O.obj U).obj (valOf X A)).obj W) :
    (internalHomSheaf X A B).val.obj (op U) →+ ((restrFun X.O.obj U).obj (valOf X B)).obj W :=
  AddMonoidHom.mk' (fun t => t.app W y) (fun _ _ => by with_unfolding_all rfl)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- An integer multiple of a section of an internal Hom sheaf acts by the same multiple. -/
private lemma internalHom_zsmul_app_apply
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (ε : ℤ)
    (U : X.C) (t : (internalHomSheaf X A B).val.obj (op U)) (W : (Over U)ᵒᵖ)
    (y : ((restrFun X.O.obj U).obj (valOf X A)).obj W) :
    (ε • t).app W y = ε • (t.app W y) :=
  map_zsmul (evalInternalHomAddHom X (B := B) U W y) ε t

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Precomposition on internal Hom sheaves acts on a section by precomposing its value. -/
private lemma internalHomPre_app_apply
    {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : A ⟶ B)
    (U : X.C) (t : (internalHomSheaf X B C).val.obj (op U)) (V : X.C) (i : V ⟶ U)
    (y : ((restrFun X.O.obj U).obj (valOf X A)).obj (op (Over.mk i))) :
    ((internalHomPre X (C := C) g).val.app (op U) t).app (op (Over.mk i)) y =
      t.app (op (Over.mk i)) (g.val.app (op V) y) := by
  with_unfolding_all rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A transport of the target of an internal Hom sheaf is linear on sections. -/
private lemma eqToHom_over_zsmul_apply
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hN : N = N') (U V : X.C) (i : V ⟶ U) (ε : ℤ) (z : N.val.obj (op V)) :
    (eqToHom (congrArg (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
          (Z.over U).val.obj (op (Over.mk i))) hN)) (ε • z) =
      ε • ((eqToHom (congrArg
        (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
          (Z.over U).val.obj (op (Over.mk i))) hN)) z) := by
  subst hN
  rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Two successive transports of the target of an internal Hom sheaf are one transport. -/
private lemma eqToHom_over_trans_apply
    {N N' N'' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hA : N = N') (hB : N' = N'') (hC : N = N'') (U V : X.C) (i : V ⟶ U)
    (z : N.val.obj (op V)) :
    (eqToHom (congrArg (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
          (Z.over U).val.obj (op (Over.mk i))) hB))
        ((eqToHom (congrArg
          (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
            (Z.over U).val.obj (op (Over.mk i))) hA)) z) =
      (eqToHom (congrArg
        (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
          (Z.over U).val.obj (op (Over.mk i))) hC)) z := by
  subst hA
  subst hB
  rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Evaluation of a Hom section at equal but differently spelled indices.** The two degrees
are free variables constrained by equations, so `subst` identifies the two sides and the
transports become identities; this is what lets a use site move between the index `p + 1` that
the Leibniz rule produces and the index the degreewise collapse is stated at. -/
private lemma applyHomSectionOver_congr_index (H : SheafHomComplex X K L) (U V : X.C) (i : V ⟶ U)
    (n : ℤ) {p p' q q' : ℤ} (hp : p = p') (hq : q = q') (hpq : p + n = q) (hpq' : p' + n = q')
    (hL : (L.X q').val.obj (op V) = (L.X q).val.obj (op V))
    (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    applyHomSectionOver X H U V i n p q hpq f x =
      eqToHom hL (applyHomSectionOver X H U V i n p' q' hpq' f
        ((K.XIsoOfEq hp).hom.val.app (op V) x)) := by
  subst hp
  subst hq
  simp

/-- **The differential of the naive termwise dual of a bounded complex is, up to the sign
`(-1)^{n+1}`, precomposition with the differential of the source.** Transported through the
degreewise collapse `AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso` of
[Stacks, Tag 08DM], the differential `SheafHom^n(E, 𝒪[0]) ⟶ SheafHom^{n+1}(E, 𝒪[0])` of the
internal Hom complex becomes `(-1)^{n+1} 𝓗om(d_E, 𝒪) : 𝓗om(E^{-n}, 𝒪) ⟶ 𝓗om(E^{-n-1}, 𝒪)`.

The differential of the internal Hom complex is `d_M ∘ f + (-1)^{n+1} f ∘ d_E` on a homogeneous
local section; the first term vanishes here because `𝒪[0]` has zero differentials, and the
second is precomposition with `d_E`. -/
theorem d_comp_homStructureSheafDegreeIso_hom
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n n' : ℤ) (hnn' : n + 1 = n') :
    (sheafHomComplex X E (structureSheafComplex X)).obj.d n n' ≫
        (homStructureSheafDegreeIso X E hE n').hom =
      n'.negOnePow • ((homStructureSheafDegreeIso X E hE n).hom ≫
        internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (E.d (-n') (-n))) := by
  subst hnn'
  have hN : ∀ m : ℤ, (structureSheafComplex X).X (m - m) =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := fun m => by
    rw [sub_self]; rfl
  have hN1 := hN (n + 1)
  have hN2 := hN n
  have hshift : -(n + 1) + 1 = -n := by omega
  have hdeg : n - n = (n + 1) - (n + 1) := by omega
  have hzero : (structureSheafComplex X).d (n - (n + 1)) ((n + 1) - (n + 1)) = 0 := rfl
  rw [homStructureSheafDegreeIso_hom X E hE (n + 1) (congrArg _ hN1),
    homStructureSheafDegreeIso_hom X E hE n (congrArg _ hN2)]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  obtain ⟨V, i, rfl⟩ : ∃ (V : X.C) (i : V ⟶ unop U), W = op (Over.mk i) :=
    ⟨_, (unop W).hom, rfl⟩
  have hvanish : ∀ z : ((structureSheafComplex X).X (n - (n + 1))).val.obj (op V),
      ((structureSheafComplex X).d (n - (n + 1)) ((n + 1) - (n + 1))).val.app (op V) z = 0 :=
    fun z => by rw [hzero]; rfl
  have hd : ∀ z : (E.X (-(n + 1))).val.obj (op V),
      (HomologicalComplex.XIsoOfEq E hshift).hom.val.app (op V)
          ((E.d (-(n + 1)) (-(n + 1) + 1)).val.app (op V) z) =
        (E.d (-(n + 1)) (-n)).val.app (op V) z :=
    fun z => by rw [← comp_val_app_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [comp_val_app_apply, comp_val_app_apply,
    internalHomSheaf_eqToHom_target_app X (E.X (-(n + 1))) hN1 (congrArg _ hN1) (unop U) _ _ y,
    homDegreeProjection_app_eq_applyHomSectionOver X E (structureSheafComplex X) (n + 1) (n + 1)
      (unop U) V i _ y,
    applyHomSectionOver_differential X (sheafHomComplex X E (structureSheafComplex X))
      (unop U) V i n (-(n + 1)) (n - (n + 1)) ((n + 1) - (n + 1)) (by omega) (by omega) s y,
    hvanish, zero_add]
  simp only [Units.smul_def]
  rw [zsmul_val_app_apply ((n + 1).negOnePow : ℤ) _ U s, internalHom_zsmul_app_apply]
  simp only [comp_val_app_apply]
  rw [internalHomPre_app_apply,
    internalHomSheaf_eqToHom_target_app X (E.X (-n)) hN2 (congrArg _ hN2) (unop U) _
      (op (Over.mk i)) ((E.d (-(n + 1)) (-n)).val.app (op V) y),
    homDegreeProjection_app_eq_applyHomSectionOver X E (structureSheafComplex X) n n
      (unop U) V i s ((E.d (-(n + 1)) (-n)).val.app (op V) y),
    applyHomSectionOver_congr_index X (sheafHomComplex X E (structureSheafComplex X))
      (unop U) V i n hshift hdeg.symm (by omega) (by omega)
      (congrArg (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
          (Z.over (unop U)).val.obj (op (Over.mk i)))
        (congrArg (structureSheafComplex X).X hdeg)) s _,
    hd y, eqToHom_over_zsmul_apply X hN1 (unop U) V i ((n + 1).negOnePow : ℤ) _]
  congr 1
  exact eqToHom_over_trans_apply X (congrArg (structureSheafComplex X).X hdeg) hN1 hN2
    (unop U) V i _

end AlgebraicGeometry.RingedSite

end
