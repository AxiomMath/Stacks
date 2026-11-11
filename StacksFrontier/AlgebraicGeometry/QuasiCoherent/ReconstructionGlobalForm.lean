module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionCover
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionMatchedPair
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.StructureQuotientSupport

/-!
# Gabriel–Rosenberg reconstruction over an affine open cover

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Let `U i` be an affine open cover of `X` and let
`G i` be a finitely presented quasi-coherent `𝒪_X`-module whose support is the complement of
`U i`.  This file gives the **global** form of [Stacks, Tag 0GPJ]: the produced opens `V i ⊆ Y`
**cover `Y`** and are each affine and quasi-compact, and each carries the matched pair
`(f_i, L_i)` of the local form.

Each chart `V i` is the complement of the support of `e.functor.obj (G i)`, exactly as in
`AlgebraicGeometry.exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation`; what
is new here is that these opens cover `Y`, which is
`AlgebraicGeometry.isOpenCover_of_supportedCorrespondence`.

Step 2 — the module `G` — is run here too, so the global statement is also available with
no module hypothesised, as
`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover`: the
module is `𝒪_X/I` for the finite type ideal sheaf `I` of [Stacks, Tag 01PH].

The local data produced here **is** glued downstream, in files importing this one: the `f_i` into
a single isomorphism `Y ≅ X` by
`AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence`
(`QuasiCoherent/ReconstructionGlobalSchemeIso.lean`), and the `L_i` into a single invertible
`𝒪_Y`-module — namely `e(𝒪_X)` — by
`AlgebraicGeometry.exists_isOpenCover_invertibleModule_restrictIso_of_isAffineOpenCover`
(`QuasiCoherent/ReconstructionGlobalModule.lean`).  The last piece, which the source dismisses
with "We omit the details", is the **comparison of functors**, a single natural isomorphism
`e(F) ≅ g^*F ⊗ M`; it is
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence`
(`QuasiCoherent/ReconstructionGlobalComparison.lean`), which is [Stacks, Tag 0GPJ] in full.

## Main results

* `AlgebraicGeometry.exists_eq_compl_supportSet_schemeIso_invertibleSheaf` — the local form of
  [Stacks, Tag 0GPJ] with the chart `V` *identified* as the complement of the support of
  `e.functor.obj G`.  That identification is what the covering statement consumes.
* `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isFinitePresentation` — the
  **global** form: for an affine open cover `U i` of `X`, the produced opens `V i` are affine and
  **cover** `Y`, and each carries the matched pair `(f_i, L_i)`.
* `AlgebraicGeometry.exists_isFinitePresentation_supportSet_eq_compl` — **step 2**: the module
  whose support is the complement of a quasi-compact open, produced rather than hypothesised.
* `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover` — the
  **global** form with step 2 discharged: only the affine open cover of `X` is given.

## Implementation notes

**The indexed statement is assembled with `choose`, not proved index by index.**  The charts come
from the single-index lemma
`AlgebraicGeometry.exists_eq_compl_supportSet_schemeIso_invertibleSheaf`, so `choose` leaves the
family as an opaque local `V : ι → Y.Opens` and the conclusion is elaborated against that
variable.  This is not a matter of taste: supplying the family instead as the explicit composite
`fun i => supportComplement (e.functor.obj (G i)).obj` and proving the indexed conclusion under
`fun i => …` does not finish.  That instantiates every occurrence of `V i` in the conclusion —
`(V i).toScheme.ringCatSheaf`, `(V i).toScheme.presheaf`, `quasicoherentRestriction (V i).ι`,
the `pullbackTensorFunctor` comparison — with the composite, so each later unification drives
definitional unfolding through `AlgebraicGeometry.supportComplement`, a subtype carrying a
closedness proof, and then through the `Opens → toScheme → ringCatSheaf` projection chain, once
per index and once per conjunct.  On this file the `choose` form elaborates in about nine seconds,
while the composite form does not finish elaborating in practice.

Two plausible-looking culprits are **not** the cause, so they need not be
avoided here: the `∀`-shaped instance binder in the signature costs nothing, which is why the
statement below keeps it exactly as stated, and having a `∀`-shaped local instance in scope costs
nothing either.  Nor is it the kernel — with kernel type-checking skipped the composite form is
still unbounded, so the time is the elaborator's.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

/-! ### The local form with the chart identified -/

/-- **The local form of [Stacks, Tag 0GPJ] with the chart `V` identified.**  This is
`AlgebraicGeometry.exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation`
together with the one extra fact that the chart it produces is the complement of the support of
`e.functor.obj G` — which is how it is built there as well, but the statement does not say so,
and the covering statement needs it.

Finite presentation of `G` is an explicit hypothesis rather than an instance binder, promoted to
an instance in the proof, so that the indexed form below can hand it over one index at a time
after `choose`. -/
theorem exists_eq_compl_supportSet_schemeIso_invertibleSheaf (U : X.Opens)
    (hUaff : IsAffineOpen U)
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hGfp : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj)
    (hG : supportSet G.obj = (U : Set X)ᶜ) :
    ∃ V : Y.Opens, (V : Set Y) = (supportSet (e.functor.obj G).obj)ᶜ ∧ IsAffineOpen V ∧
      IsCompact (V : Set Y) ∧
      ∃ (F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
          (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory)
        (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf),
        F.IsEquivalence ∧
          Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatSheaf.2 L ∧
          Nonempty (e.functor ⋙ quasicoherentRestriction V.ι ≅
            quasicoherentRestriction U.ι ⋙ F) ∧
          Nonempty (F ⋙ ObjectProperty.ι
              (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
            pullbackTensorFunctor f.hom L) := by
  have := hGfp
  have hfp : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (e.functor.obj G).obj :=
    isFinitePresentation_map_of_equivalence e G
  have hqc : ((e.functor.obj G).obj).IsQuasicoherent := (e.functor.obj G).property
  have hUZ : (U : Set X) = (supportSet G.obj)ᶜ := by rw [hG, compl_compl]
  have hVc : IsCompact ((supportComplement (e.functor.obj G).obj : Set Y)) :=
    isCompact_compl_supportSet (e.functor.obj G).obj
  obtain ⟨haff, hrest⟩ := exists_schemeIso_invertibleSheaf_of_supportedCorrespondence e
    (supportSet G.obj) (supportSet (e.functor.obj G).obj)
    (quasicoherentSupportedOn_supportSet_correspondence e G) U hUZ hUaff.isCompact hUaff
    (supportComplement (e.functor.obj G).obj) (coe_supportComplement _) hVc
  exact ⟨supportComplement (e.functor.obj G).obj, coe_supportComplement _, haff, hVc, hrest⟩

/-! ### The global form: the chart opens cover `Y` -/

/-- **Stacks Project, Tag 0GPJ in its global form.**  Let `X` and `Y` be quasi-compact and
quasi-separated schemes and let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Let `U i` be an
affine open cover of `X` and let `G i` be a finitely presented quasi-coherent `𝒪_X`-module whose
support is the complement of `U i`.  Then there are opens `V i ⊆ Y` which **cover `Y`** and are
each affine and quasi-compact, and for each `i` an equivalence `F_i : QCoh(𝒪_{U i}) ≌
QCoh(𝒪_{V i})` compatible with `e` and the two restrictions, an isomorphism of schemes
`f_i : V i ≅ U i` and an invertible sheaf `L_i` of `𝒪_{V i}`-modules such that `F_i` is inverse
image along `f_i` followed by `- ⊗_{𝒪_{V i}} L_i`.

The chart `V i` is the complement of the support of `e.functor.obj (G i)`, as in
`AlgebraicGeometry.exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation`; what
is new here is that these opens cover `Y`, which is
`AlgebraicGeometry.isOpenCover_of_supportedCorrespondence`. -/
theorem exists_isOpenCover_schemeIso_invertibleSheaf_of_isFinitePresentation {ι : Type u}
    (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U)
    (G : ι → (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [∀ i, SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (G i).obj]
    (hG : ∀ i, supportSet (G i).obj = (U i : Set X)ᶜ) :
    ∃ V : ι → Y.Opens, IsOpenCover V ∧
      ∀ i, IsAffineOpen (V i) ∧ IsCompact (V i : Set Y) ∧
        ∃ (F : (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ⥤
            (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory)
          (f : (V i).toScheme ≅ (U i).toScheme)
          (L : SheafOfModules.{u} (V i).toScheme.ringCatSheaf),
          F.IsEquivalence ∧
            Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
              (V i).toScheme.ringCatSheaf.2 L ∧
            Nonempty (e.functor ⋙ quasicoherentRestriction (V i).ι ≅
              quasicoherentRestriction (U i).ι ⋙ F) ∧
            Nonempty (F ⋙ ObjectProperty.ι
                (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
              pullbackTensorFunctor f.hom L) := by
  have hGfp : ∀ i, SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (G i).obj :=
    inferInstance
  choose V hVeq hVaff hVc hrest using fun i =>
    exists_eq_compl_supportSet_schemeIso_invertibleSheaf e (U i) (hUaff i) (G i) (hGfp i) (hG i)
  have hcorr : ∀ (i : ι)
      (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
      quasicoherentSupportedOn X (supportSet (G i).obj) E ↔
        quasicoherentSupportedOn Y (supportSet (e.functor.obj (G i)).obj) (e.functor.obj E) := by
    intro i
    have := hGfp i
    exact quasicoherentSupportedOn_supportSet_correspondence e (G i)
  refine ⟨V, ?_, fun i => ⟨hVaff i, hVc i, hrest i⟩⟩
  exact isOpenCover_of_supportedCorrespondence e U V (fun i => supportSet (G i).obj)
    (fun i => supportSet (e.functor.obj (G i)).obj) hcorr
    (fun i => by rw [hG i, compl_compl]) hVeq hUcover

/-! ### Step 2: the module `G`, produced rather than hypothesised -/

/-- **Step 2 of [Stacks, Tag 0GPJ]: the module `G`.**  For a quasi-compact open `U` of a
quasi-compact quasi-separated scheme `X` there is a finitely presented quasi-coherent
`𝒪_X`-module whose support is exactly the complement of `U`.

It is `𝒪_X / I` for a finite type quasi-coherent sheaf of ideals `I` with `V(I) = X \ U`:
[Stacks, Tag 01PH] supplies `I`
(`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`),
`Stacks.AlgebraicGeometry.IdealSheafQuotient.isFinitePresentation_structureQuotient` makes
`𝒪_X / I` of finite presentation — hence quasi-coherent — and
`Stacks.AlgebraicGeometry.IdealSheafQuotient.supp_structureQuotient` identifies its support with
`V(I)`.  No Noetherian or coherence hypothesis enters anywhere in that chain.

Finite presentation is a conjunct of the conclusion rather than an instance, so that the indexed
form below can hand it over one index at a time after `choose`. -/
theorem exists_isFinitePresentation_supportSet_eq_compl (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj ∧
        supportSet G.obj = (U : Set X)ᶜ := by
  obtain ⟨I, hI, hIsupp⟩ := exists_isFiniteType_idealSheafData_support_eq_compl U hU
  have hfp : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.IdealSheafQuotient.structureQuotient I) :=
    Stacks.AlgebraicGeometry.IdealSheafQuotient.isFinitePresentation_structureQuotient I hI
  exact ⟨⟨Stacks.AlgebraicGeometry.IdealSheafQuotient.structureQuotient I, inferInstance⟩, hfp,
    (Stacks.AlgebraicGeometry.IdealSheafQuotient.supp_structureQuotient I).trans hIsupp⟩

/-- **Stacks Project, Tag 0GPJ in its global form, with step 2 discharged.**  Let `X` and `Y` be
quasi-compact and quasi-separated schemes, let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence and
let `U i` be an affine open cover of `X`.  Then there are opens `V i ⊆ Y` which **cover `Y`** and
are each affine and quasi-compact, and for each `i` an equivalence
`F_i : QCoh(𝒪_{U i}) ≌ QCoh(𝒪_{V i})` compatible with `e` and the two restrictions, an
isomorphism of schemes `f_i : V i ≅ U i` and an invertible sheaf `L_i` of `𝒪_{V i}`-modules such
that `F_i` is inverse image along `f_i` followed by `- ⊗_{𝒪_{V i}} L_i`.

This is
`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isFinitePresentation` with its
hypotheses `G` and `hG` *deleted*: the modules are produced by
`AlgebraicGeometry.exists_isFinitePresentation_supportSet_eq_compl`.  Only the affine open cover
of `X` is given.

The module family is kept opaque, by `choose` against the single-index statement above, for the
reason recorded in the implementation notes: handing over an explicit composite instead makes
the conclusion unfold definitionally once per index and per conjunct. -/
theorem exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover {ι : Type u}
    (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ V : ι → Y.Opens, IsOpenCover V ∧
      ∀ i, IsAffineOpen (V i) ∧ IsCompact (V i : Set Y) ∧
        ∃ (F : (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ⥤
            (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory)
          (f : (V i).toScheme ≅ (U i).toScheme)
          (L : SheafOfModules.{u} (V i).toScheme.ringCatSheaf),
          F.IsEquivalence ∧
            Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
              (V i).toScheme.ringCatSheaf.2 L ∧
            Nonempty (e.functor ⋙ quasicoherentRestriction (V i).ι ≅
              quasicoherentRestriction (U i).ι ⋙ F) ∧
            Nonempty (F ⋙ ObjectProperty.ι
                (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
              pullbackTensorFunctor f.hom L) := by
  choose G hGfp hGsupp using fun i =>
    exists_isFinitePresentation_supportSet_eq_compl (X := X) (U i) (hUaff i).isCompact
  have : ∀ i, SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (G i).obj := hGfp
  exact exists_isOpenCover_schemeIso_invertibleSheaf_of_isFinitePresentation e U hUaff hUcover
    G hGsupp

end Reconstruction

end AlgebraicGeometry

end
