module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.ConormalSource

/-!
# The source coherence of Tag 0B3V's base-change square for the conormal isomorphism

`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange`
rests on a single hypothesis, the *source coherence* `hsrc`. Writing `P` for
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` at `ℰ`, `P'` for it at `ℰ'`, `K` for
`Stacks.Divisors.conormalSourceBaseChange`, `R` for the identification of the square
`σ' ≫ h = g ≫ σ` and `Φ` for `Stacks.ProjectiveBundleConormal.twistedSourceBaseChange`, it says

`K.hom ≫ (P').inv = g^*(P.inv) ≫ R.hom ≫ σ'^*Φ`.

All four of `P`, `P'`, `K` and `Φ` are a comparison of [Stacks, Tag 01CD] followed by a `⊗` of
two factor comparisons, so `hsrc` splits into three pieces: the Tag 01CD coherence of the square,
the kernel factor, and the inverse-line factor. **This file supplies the first two and the whole
assembly**, reducing `hsrc` to the inverse-line factor alone.

## Main results

* `Stacks.ProjectiveBundleConormal.sectionSquare_coherence_scheme`:
  `Stacks.Modules.sectionSquare_coherence` restated at
  `Stacks.ProjectiveBundleConormal.schemePullbackCompIso` and
  `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso`, which is the vocabulary the factors of
  `Φ` are built at.
* `Stacks.ProjectiveBundleConormal.kernelFactor_coherence`: **the kernel factor of `hsrc`.**
  The pullback along `g` of the section collapse followed by
  `Stacks.Divisors.quotientKernelBaseChange` is the square's identification followed by `σ'^*` of
  the kernel factor of `Φ` and the section collapse downstairs. It is the pasting coherence above
  together with the naturality of the collapse at the kernel comparison; no new geometry enters.
* `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_naturality_right` and
  `pullbackTensorComparison_naturality_tensorHom`: the naturality of Tag 01CD's comparison in the
  second variable and in both at once, at the scheme spelling and the re-seated monoidal
  structure. The repository had only the first-variable half there.
* `Stacks.ProjectiveBundleConormal.positiveLine_coherence`: **the compatibility of the positive
  lines**, `g^*e ≫ hL.inv = R.hom ≫ σ'^*(h^*𝒪(1) ≅ 𝒪'(1)) ≫ e'`, from the hypotheses `hqe` and
  `hqe'` that say the two sections classify the two quotients, together with `hq` and `comm`. It
  is the relation whose absence makes the inverse-line factor unprovable at `sourceCoherence`,
  which does not carry `hqe` and `hqe'`.
* `Stacks.ProjectiveBundleConormal.sourceCoherence_forward` and `sourceCoherence`: **`hsrc` from
  the inverse-line factor alone**, in the forward direction and at the spelling
  `conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` takes it.

## The crossings

Five vocabulary crossings this assembly needs are stated here as equations. Each is a `rfl` or one
rewrite, and each is given its own declaration so that the kernel meets one definitional crossing at
a time:

* `pullbackCompIso_hom_eq`: `Stacks.ClosedImmersion.pullbackCompIso` — the spelling `hsrc`
  is stated at — against `schemePullbackCompIso`, the spelling everything is proved at. The two
  are built from oppositely oriented composition laws; the forward maps are nonetheless `rfl`.
* `comparisonBifunctorIso_hom_app_eq` and `conormalSourcePullbackTensor_hom_eq`:
  `Stacks.RingedSpace.comparisonBifunctorIso`, which `Stacks.Divisors.conormalSourceBaseChange`
  is built from, against `pullbackTensorComparison`. Both `rfl`.
* `tensorProductIso_hom_eq_tensorHom`: the tensor product sheaf of two isomorphisms against
  `⊗ₘ` of the re-seated structure. **Not** a `rfl`; it is
  `Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom`, accepted here against the
  `tensorProductIso` spelling definitionally.
* `pullbackSourceIso_hom_eq`, `conormalSourceBaseChange_hom_eq` and
  `twistedSourceBaseChangeIso_hom_eq`: the three composites spelled out as
  `pullbackTensorComparison ≫ (… ⊗ₘ …)`.

Every reassociation is hoisted to a bare category or a bare monoidal category
(`kernelFactorSquareAux`, `sourceFactorAux`, `flipAux`), as
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceBaseChange` records it must be.

## What this reduces to, and where it is discharged

`hsrc` is reduced here to the **inverse-line factor**, the hypothesis `hinv` of
`Stacks.ProjectiveBundleConormal.sourceCoherence`: the two identifications of `g^*σ^*𝒪(-1)` with
`(Q'.L)^{⊗ -1}` — one as `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` followed by
`Stacks.Divisors.inverseQuotientBaseChange`, one as the square's identification followed by
`σ'^*` of the twist factor of `Φ` and `inverseTwistBaseChangeIso` downstairs — agree.

`hinv` is **not** provable from the hypotheses `sourceCoherence` carries. Its left-hand side does
not mention `e'` and its right-hand side ends in `inverseTwistBaseChangeIso E' Q' e'`, which
*determines* `e'` by `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso_injective`; and
`e` and `e'` are independent parameters there. What is needed is the compatibility of the
*positive* lines, `Stacks.ProjectiveBundleConormal.positiveLine_coherence` below, whose
hypotheses `hqe` and `hqe'` — that the two sections classify the two quotients — every assembly
point of the clause carries.

**`hinv` is proved**, from `positiveLine_coherence`, in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`, as
`Stacks.ProjectiveBundleConormal.inverseLineFactor`; that module also carries the form of this
file's two results with `hqe` and `hqe'` in place of `hinv`
(`sourceCoherence_of_classifying`) and the clause itself
(`conormalCanonicalMap_baseChange`). The passage is a pin calculus: each of the five factors of
`hinv` is pinned against an evaluation pairing, being pinned composes and determines the
morphism, and the two sides are therefore pinned along the two sides of `positiveLine_coherence`.
The handedness is the `mulIso'` one of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineDetermination`, because that
is the form whose snake identity is spent at the *target* of each comparison, and every target is
a plain `Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`.

**No `@[stacks 0B3V]` attribute is attached in this file**: nothing here states a clause of the
tag. The label is on `conormalCanonicalMap_baseChange` in the module named above.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe v u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)

/-- The components of `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso` in the backward
direction, spelled out. -/
theorem pullbackSectionNatIso_inv_app {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X) (F : X.Modules) :
    (pullbackSectionNatIso E hσ).inv.app F =
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).hom.app F ≫
        (Scheme.Modules.pullbackCongr hσ).hom.app F ≫
          (Scheme.Modules.pullbackId X).hom.app F := by
  simp [pullbackSectionNatIso]

/-- **The pasting coherence of the two squares, in the vocabulary of this file.** The square's
identification of `g^*σ^*` with `σ'^*h^*`, then `σ'^*` of its identification of `h^*π^*` with
`π'^*g^*`, then the section collapse of `σ'`, is the pullback along `g` of the section collapse
of `σ`.

This is `Stacks.Modules.sectionSquare_coherence`, whose statement writes out all nine
comparison maps, restated at `Stacks.ProjectiveBundleConormal.schemePullbackCompIso` and
`pullbackSectionNatIso` — the vocabulary the factors of `Φ` are built at. The two
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` factors enter it in opposite directions on the
two sides, and that crossing is the content of the restatement. -/
theorem sectionSquare_coherence_scheme {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X) {σ' : X' ⟶ (bundle E').scheme}
    (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) (M : X.Modules) :
    (schemePullbackCompIso comm ((Scheme.Modules.pullback (bundle E).toBase).obj M)).hom ≫
        (Scheme.Modules.pullback σ').map
          (schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm M).hom ≫
        (pullbackSectionNatIso E' hσ').inv.app ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback g).map ((pullbackSectionNatIso E hσ).inv.app M) := by
  have h := Stacks.Modules.sectionSquare_coherence g σ (bundle E).toBase σ' (bundle E').toBase
    (bundleBaseChangeHom g E E' hE) hσ hσ' (bundleBaseChangeHom_comp_toBase g E E' hE) comm M
  simp only [schemePullbackCompIso_hom, pullbackSectionNatIso_inv_app, Functor.map_comp,
    Category.assoc] at h ⊢
  exact h

/-- Reassociation for the kernel factor, over a bare category. -/
private theorem kernelFactorSquareAux {D : Type u} [Category.{v} D] {A B C F G H : D}
    (p1 : A ⟶ B) (p2 : B ⟶ C) (p3 : C ⟶ F) (c' : F ⟶ G) (cg : C ⟶ H) (k1 : H ⟶ G) (q : A ⟶ H)
    (pk : B ⟶ F) (hpk : pk = p2 ≫ p3) (hnat : p3 ≫ c' = cg ≫ k1)
    (hsec : p1 ≫ p2 ≫ cg = q) : q ≫ k1 = p1 ≫ pk ≫ c' := by
  rw [hpk, ← hsec, Category.assoc p2 p3 c', hnat, Category.assoc, Category.assoc]

/-- **The kernel factor of `hsrc`.** The pullback along `g` of the section collapse at
`\ker q`, followed by `Stacks.Divisors.quotientKernelBaseChange`, is the square's identification
followed by `σ'^*` of the kernel factor of `Φ` and the section collapse of `σ'` at `\ker q'`.

This is the piece of `hsrc` recorded as owed in the "What is still owed, precisely" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceBaseChange` as (2), and it needs
no new geometry: it is `sectionSquare_coherence_scheme` at `M = \ker q`, the naturality of the
section collapse of `σ'` at the kernel comparison, and
`Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso_hom`, with all the reassociation
paid by `kernelFactorSquareAux` over a bare category. -/
theorem kernelFactor_coherence {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X) {σ' : X' ⟶ (bundle E').scheme}
    (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) :
    (Scheme.Modules.pullback g).map ((pullbackSectionNatIso E hσ).inv.app (kernel Q.q)) ≫
        (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1.hom =
      (schemePullbackCompIso comm
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))).hom ≫
        (Scheme.Modules.pullback σ').map
            (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom ≫
          (pullbackSectionNatIso E' hσ').inv.app (kernel Q'.q) := by
  have hpk : (Scheme.Modules.pullback σ').map
        (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom =
      (Scheme.Modules.pullback σ').map
          (schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm
            (kernel Q.q)).hom ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullback (bundle E').toBase).map
          (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1.hom) := by
    rw [kernelTwistedBaseChangeIso_hom, Functor.map_comp]
  apply kernelFactorSquareAux _ _ _ _ _ _ _ _ hpk
    ((pullbackSectionNatIso E' hσ').inv.naturality
      (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1.hom)
    (sectionSquare_coherence_scheme g E E' hE hσ hσ' comm (kernel Q.q))

/-! ### The compatibility of the positive lines -/

/-- The epi cancellation and the reassociation of the positive-line compatibility, over a bare
category. -/
private theorem positiveFactorAux {D : Type u} [Category.{v} D]
    {U V Y₁ R Y₂ Y₃ Z₁ Z₂ Z₃ G Eo : D}
    (p : U ⟶ V) [Epi p] (ge : V ⟶ Y₁) (hli : Y₁ ⟶ R) (cc : V ⟶ Y₂) (sw : Y₂ ⟶ Y₃)
    (eh : Y₃ ⟶ R) (ce : U ⟶ Z₁) (ht : Z₁ ⟶ Y₂) (d1 : Z₁ ⟶ Z₂) (hei : Z₂ ⟶ Z₃)
    (tp : Z₃ ⟶ Y₃) (sp : Z₃ ⟶ Eo) (cg : Z₂ ⟶ G) (hb : G ⟶ Eo) (qq : Eo ⟶ R)
    (gs : U ⟶ G) (gq : G ⟶ Y₁)
    (hpin : p ≫ ge = gs ≫ gq) (hqinv : gq ≫ hli = hb ≫ qq) (hnat : p ≫ cc = ce ≫ ht)
    (htaut : d1 ≫ hei ≫ tp = ht ≫ sw) (hpin' : tp ≫ eh = sp ≫ qq)
    (hsq : ce ≫ d1 ≫ cg = gs) (hnat' : hei ≫ sp = cg ≫ hb) :
    ge ≫ hli = cc ≫ sw ≫ eh := by
  refine (cancel_epi p).mp ?_
  rw [reassoc_of% hpin, hqinv, ← hsq, reassoc_of% hnat]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat', ← hpin', reassoc_of% htaut]

/-- A section's classifying comparison, with the section collapse moved to the other side. -/
private theorem tautologicalMap_comp_eq {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent]
    {s : Y ⟶ (bundle F).scheme} (hs : s ≫ (bundle F).toBase = 𝟙 Y)
    (R : Stacks.Divisors.InvertibleQuotient Y F)
    (r : (Scheme.Modules.pullback s).obj (tautologicalTwist F (symPieces F)) ≅ R.L)
    (hr : (Scheme.Modules.pullbackId Y).inv.app F ≫
      (Scheme.Modules.pullbackCongr hs).inv.app F ≫
        (Scheme.Modules.pullbackComp s (bundle F).toBase).inv.app F ≫
          (Scheme.Modules.pullback s).map (tautologicalMap F (symPieces F)) ≫ r.hom = R.q) :
    (Scheme.Modules.pullback s).map (tautologicalMap F (symPieces F)) ≫ r.hom =
      (pullbackSectionNatIso F hs).inv.app F ≫ R.q := by
  refine ((pullbackSectionNatIso F hs).app F).eq_inv_comp.mpr ?_
  rw [Iso.app_hom, pullbackSectionNatIso_hom_app]
  simpa only [Category.assoc] using hr

include hq in
/-- **The compatibility of the positive lines**, where the data relating the two classifying
comparisons is in scope: `g^*e` followed by `hL⁻¹` is the square's identification followed by
`σ'^*` of `Stacks.ProjectiveBundleConormal.symTwistBundleBaseChangeIso` and `e'`.

This is **not** an assumption. It is a consequence of the hypothesis `hqe` of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at both bundles — each pins its
classifying comparison against the tautological map — together with the identification `hq` of
the quotients and the commuting square `comm`. Cancelling `g^*σ^*` of the tautological map, which
is an epimorphism by `Stacks.ProjectiveBundleSplitting.epi_tautologicalMap` and the preservation
of epimorphisms by the two pullbacks, both sides become the section collapse of `σ` pulled back
along `g`, followed by `hE⁻¹` and `q'`: on the left by `hqe` and `hq`, on the right by `hqe'`,
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_comp_pullbackTautologicalMap` and the
pasting coherence `sectionSquare_coherence_scheme` at `ℰ`. All the reassociation is paid by
`positiveFactorAux` over a bare category.

It is the relation whose absence makes the inverse-line factor of the source coherence
unprovable at `Stacks.ProjectiveBundleConormal.sourceCoherence`, where `hqe` and `hqe'` are not
parameters; see the module documentation. -/
theorem positiveLine_coherence {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
      (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
        (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
          (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
      (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
        (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
          (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ) :
    (Scheme.Modules.pullback g).map e.hom ≫ hL.inv =
      (schemePullbackCompIso comm (tautologicalTwist E (symPieces E))).hom ≫
        (Scheme.Modules.pullback σ').map (symTwistBundleBaseChangeIso g E E' hE).hom ≫
          e'.hom := by
  have : Epi (tautologicalMap E (symPieces E)) := epi_tautologicalMap E (symPieces E)
  have : (Scheme.Modules.pullback σ).PreservesEpimorphisms := inferInstance
  have : (Scheme.Modules.pullback g).PreservesEpimorphisms := inferInstance
  have h1g := congrArg (Scheme.Modules.pullback g).map (tautologicalMap_comp_eq E hσ Q e hqe)
  simp only [Functor.map_comp] at h1g
  have hd := congrArg (Scheme.Modules.pullback σ').map
    (schemePullbackCompIso_comp_pullbackTautologicalMap g E E' hE)
  simp only [Functor.map_comp] at hd
  have hqinv : (Scheme.Modules.pullback g).map Q.q ≫ hL.inv = hE.inv ≫ Q'.q := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact positiveFactorAux
    ((Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E))))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h1g hqinv
    (schemePullbackCompIso_naturality comm (tautologicalMap E (symPieces E)))
    hd (tautologicalMap_comp_eq E' hσ' Q' e' hqe')
    (sectionSquare_coherence_scheme g E E' hE hσ hσ' comm E)
    ((pullbackSectionNatIso E' hσ').inv.naturality hE.inv)

section SquareSpelling

variable {Z₁ Z₂ W₁ W₂ : Scheme.{u}} {i : Z₁ ⟶ Z₂} {k : Z₂ ⟶ W₂} {f : Z₁ ⟶ W₁} {j : W₁ ⟶ W₂}

/-- **The square's identification at the ringed-space spelling is the one at the scheme
spelling**, on forward maps. `Stacks.ClosedImmersion.pullbackCompIso` is the spelling the
hypothesis `hsrc` of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` is
stated at, and `Stacks.ProjectiveBundleConormal.schemePullbackCompIso` is the one everything is
proved at; they are definitionally equal, and this lemma states it. They are built from oppositely
oriented composition laws — `RingedSpaceModuleAdjunction.modulePullbackComp` runs from the pullback
along a composite, `AlgebraicGeometry.Scheme.Modules.pullbackComp` towards it — and the forward maps
are nonetheless the same term. -/
theorem pullbackCompIso_hom_eq (e : i ≫ k = f ≫ j) (M : W₂.Modules) :
    (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom e) M).hom =
      (schemePullbackCompIso e M).hom := rfl

end SquareSpelling

/-- **Tag 01CD's comparison as a component of the bifunctor isomorphism is the one used
here.** `Stacks.RingedSpace.comparisonBifunctorIso` is the spelling
`Stacks.Divisors.conormalSourcePullbackTensor` is built from. -/
theorem comparisonBifunctorIso_hom_app_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules) :
    (Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app (A, B) =
      pullbackTensorComparison f A B := rfl

/-- **Naturality of the comparison of [Stacks, Tag 01CD] in the second variable**, in whiskered
form, at the scheme spelling.
`Stacks.ProjectiveBundleConormal.pullbackTensorComparison_naturality_left` is the first-variable
half; this is its mirror, re-ascribed from
`Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_right` exactly as that one is. -/
theorem pullbackTensorComparison_naturality_right {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (A : Z.Modules) {B B' : Z.Modules} (w : B ⟶ B') :
    pullbackTensorComparison f A B ≫
        ((Scheme.Modules.pullback f).obj A ◁ (Scheme.Modules.pullback f).map w) =
      (Scheme.Modules.pullback f).map (A ◁ w) ≫ pullbackTensorComparison f A B' :=
  Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_right f.toLRSHom.toShHom A w

/-- **Naturality of the comparison of [Stacks, Tag 01CD] in both variables at once**: it carries
the pullback of a tensor product of two morphisms to the tensor product of their pullbacks. A
monoidal tensor product of morphisms is the composite of the two whiskerings, so this is the two
halves above.

Stated at the scheme spelling and at the re-seated monoidal structure. The repository has the
same statement at `Stacks.PullbackGradedAlgebra.monoidalCategory`'s `⊗ₘ`, which — as
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonCompSheafTensor` records —
is not definitionally this one. -/
theorem pullbackTensorComparison_naturality_tensorHom {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {A A' B B' : Z.Modules} (u : A ⟶ A') (v : B ⟶ B') :
    (Scheme.Modules.pullback f).map (u ⊗ₘ v) ≫ pullbackTensorComparison f A' B' =
      pullbackTensorComparison f A B ≫
        ((Scheme.Modules.pullback f).map u ⊗ₘ (Scheme.Modules.pullback f).map v) := by
  calc (Scheme.Modules.pullback f).map (u ⊗ₘ v) ≫ pullbackTensorComparison f A' B'
      = ((Scheme.Modules.pullback f).map (u ▷ B) ≫
            (Scheme.Modules.pullback f).map (A' ◁ v)) ≫
          pullbackTensorComparison f A' B' := by
        rw [← Functor.map_comp, ← MonoidalCategory.tensorHom_def]
    _ = (Scheme.Modules.pullback f).map (u ▷ B) ≫
          (Scheme.Modules.pullback f).map (A' ◁ v) ≫
            pullbackTensorComparison f A' B' := Category.assoc _ _ _
    _ = (Scheme.Modules.pullback f).map (u ▷ B) ≫
          pullbackTensorComparison f A' B ≫
            ((Scheme.Modules.pullback f).obj A' ◁ (Scheme.Modules.pullback f).map v) := by
        rw [pullbackTensorComparison_naturality_right]
    _ = (pullbackTensorComparison f A B ≫
            ((Scheme.Modules.pullback f).map u ▷ (Scheme.Modules.pullback f).obj B)) ≫
          ((Scheme.Modules.pullback f).obj A' ◁ (Scheme.Modules.pullback f).map v) := by
        rw [pullbackTensorComparison_naturality_left, Category.assoc]
    _ = pullbackTensorComparison f A B ≫
          ((Scheme.Modules.pullback f).map u ⊗ₘ (Scheme.Modules.pullback f).map v) := by
        rw [Category.assoc, ← MonoidalCategory.tensorHom_def]

/-- **The tensor product sheaf of two isomorphisms is `⊗ₘ`** for the re-seated monoidal
structure, on forward maps. This is `Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom`,
whose statement writes the bifunctor's action on a pair; the crossing to
`Stacks.SheafOfModules.Invertible.tensorProductIso` — the spelling
`Stacks.Divisors.conormalSourceFactors` is built at — is taken here. Only the forward maps are
compared: `Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso` records that the `inv`
fields of these two crossings are not definitionally equal. -/
theorem tensorProductIso_hom_eq_tensorHom {A A' B B' : X.Modules} (a : A ≅ A') (b : B ≅ B') :
    (Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf X.ringCatSheaf.2 a b).hom =
      a.hom ⊗ₘ b.hom :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ a.hom b.hom).symm.trans
    (Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom a.hom b.hom)

omit [E.IsQuasicoherent] in
/-- **The Tag 01CD factor of `Stacks.Divisors.conormalSourceBaseChange` is the comparison used
here.** -/
theorem conormalSourcePullbackTensor_hom_eq (Q : Stacks.Divisors.InvertibleQuotient X E) :
    (Stacks.Divisors.conormalSourcePullbackTensor g E Q).hom =
      pullbackTensorComparison g (kernel Q.q)
        (letI := Q.invertible
         Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) :=
  rfl

/-- **`P` spelled out**: Tag 01CD's comparison followed by the `⊗` of the section collapse and
`Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso`. -/
theorem pullbackSourceIso_hom_eq {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L) :
    (pullbackSourceIso E Q hσ e).hom =
      pullbackTensorComparison σ
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E) ≫
        ((pullbackSectionNatIso E hσ).inv.app (kernel Q.q) ⊗ₘ
          (inverseTwistBaseChangeIso E Q e).hom) := rfl

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- **`K` spelled out**: Tag 01CD's comparison followed by the `⊗` of
`Stacks.Divisors.quotientKernelBaseChange` and `Stacks.Divisors.inverseQuotientBaseChange`. One
rewrite of the Tag 01CD factor and one of the `tensorProductIso` factor. -/
theorem conormalSourceBaseChange_hom_eq :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom =
      pullbackTensorComparison g (kernel Q.q)
          (letI := Q.invertible
           Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≫
        ((Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1.hom ⊗ₘ
          (Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL).hom) := by
  rw [Stacks.Divisors.conormalSourceBaseChange_hom, conormalSourcePullbackTensor_hom_eq]
  exact congrArg _ (tensorProductIso_hom_eq_tensorHom _ _)

/-- **`Φ` spelled out** at `pullbackTensorComparison` rather than at
`Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso`, which is the form the assembly
consumes. -/
theorem twistedSourceBaseChangeIso_hom_eq :
    (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom =
      pullbackTensorComparison (bundleBaseChangeHom g E E' hE)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E) ≫
        ((kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom ⊗ₘ
          (inverseTwistBundleBaseChangeIso g E E' hE).hom) :=
  twistedSourceBaseChangeIso_hom g E E' hE Q Q' hL hq

/-- The whole of the source coherence's reassociation, over a bare monoidal category. -/
private theorem sourceFactorAux {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {U M₁ M₃ N₁ N₂ N₃ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : D}
    (pσ : U ⟶ M₁) (pg : M₁ ⟶ A₁ ⊗ B₁) (gcc : M₁ ⟶ M₃) (ptcg : M₃ ⟶ A₂ ⊗ B₂)
    (gc1 : A₁ ⟶ A₂) (gc2 : B₁ ⟶ B₂) (k1 : A₂ ⟶ A₃) (k2 : B₂ ⟶ B₃)
    (ra : A₁ ⟶ A₄) (rb : B₁ ⟶ B₄) (sk1 : A₄ ⟶ A₅) (st2 : B₄ ⟶ B₅)
    (c1' : A₅ ⟶ A₃) (c2' : B₅ ⟶ B₃)
    (rr : U ⟶ N₁) (sph : N₁ ⟶ N₂) (ptcs : N₂ ⟶ A₄ ⊗ B₄) (skt : N₂ ⟶ N₃)
    (ptcs2 : N₃ ⟶ A₅ ⊗ B₅)
    (hL1 : gcc ≫ ptcg = pg ≫ (gc1 ⊗ₘ gc2))
    (hR1 : skt ≫ ptcs2 = ptcs ≫ (sk1 ⊗ₘ st2))
    (hp1 : rr ≫ sph ≫ ptcs = pσ ≫ pg ≫ (ra ⊗ₘ rb))
    (hker : gc1 ≫ k1 = ra ≫ sk1 ≫ c1')
    (hinv : gc2 ≫ k2 = rb ≫ st2 ≫ c2') :
    (pσ ≫ gcc) ≫ ptcg ≫ (k1 ⊗ₘ k2) =
      rr ≫ (sph ≫ skt) ≫ ptcs2 ≫ (c1' ⊗ₘ c2') := by
  calc (pσ ≫ gcc) ≫ ptcg ≫ (k1 ⊗ₘ k2)
      = pσ ≫ (gcc ≫ ptcg) ≫ (k1 ⊗ₘ k2) := by rw [Category.assoc, Category.assoc]
    _ = pσ ≫ pg ≫ ((gc1 ≫ k1) ⊗ₘ (gc2 ≫ k2)) := by
        rw [hL1, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    _ = pσ ≫ pg ≫ ((ra ≫ sk1 ≫ c1') ⊗ₘ (rb ≫ st2 ≫ c2')) := by rw [hker, hinv]
    _ = pσ ≫ pg ≫ ((ra ⊗ₘ rb) ≫ (sk1 ⊗ₘ st2) ≫ (c1' ⊗ₘ c2')) := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom,
          MonoidalCategory.tensorHom_comp_tensorHom]
    _ = (pσ ≫ pg ≫ (ra ⊗ₘ rb)) ≫ (sk1 ⊗ₘ st2) ≫ (c1' ⊗ₘ c2') := by
        rw [Category.assoc, Category.assoc]
    _ = (rr ≫ sph ≫ ptcs) ≫ (sk1 ⊗ₘ st2) ≫ (c1' ⊗ₘ c2') := by rw [hp1]
    _ = rr ≫ (sph ≫ skt) ≫ ptcs2 ≫ (c1' ⊗ₘ c2') := by
        rw [Category.assoc, Category.assoc, ← Category.assoc ptcs, ← hR1,
          Category.assoc, Category.assoc]

/-- Reading a four-arrow identity of isomorphisms the other way round, over a bare category. -/
private theorem flipAux {D : Type u} [Category.{v} D] {U V T' V' W : D}
    (pg : U ≅ V) (kk : V ⟶ T') (pp : V' ≅ T') (rr : U ⟶ W) (ff : W ⟶ V')
    (h : pg.hom ≫ kk = rr ≫ ff ≫ pp.hom) : kk ≫ pp.inv = pg.inv ≫ rr ≫ ff := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h]
  simp

/-- **The source coherence, in the forward direction, from the inverse-line factor alone.**
`g^*P` followed by `K` is the square's identification followed by `σ'^*Φ` and `P'`.

Each of the four is Tag 01CD's comparison followed by a `⊗` of two factor comparisons, so after
moving each `⊗` across the comparison next to it
(`pullbackTensorComparison_naturality_tensorHom`) both sides are the *same* two-step prefix
`g^*(\text{Tag 01CD at }σ) ≫ \text{Tag 01CD at }g` followed by a single `⊗`; that prefix is
what `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pullbackTensorComparison` supplies
for the right-hand side. What is left is one equation per tensor factor: the kernel factor, which
is `kernelFactor_coherence`, and the inverse-line factor, which is the hypothesis `hinv`. All the
reassociation is paid by `sourceFactorAux` over a bare monoidal category, so nothing is rewritten
underneath a `⊗`. -/
theorem sourceCoherence_forward {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (hinv : (Scheme.Modules.pullback g).map (inverseTwistBaseChangeIso E Q e).hom ≫
        (Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL).hom =
      (schemePullbackCompIso comm (inverseTautologicalTwist E)).hom ≫
        (Scheme.Modules.pullback σ').map (inverseTwistBundleBaseChangeIso g E E' hE).hom ≫
          (inverseTwistBaseChangeIso E' Q' e').hom) :
    (Scheme.Modules.pullback g).map (pullbackSourceIso E Q hσ e).hom ≫
        (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom =
      (schemePullbackCompIso comm (twistedSource E Q)).hom ≫
        (Scheme.Modules.pullback σ').map
            (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom ≫
          (pullbackSourceIso E' Q' hσ' e').hom := by
  rw [pullbackSourceIso_hom_eq E Q hσ e,
    conormalSourceBaseChange_hom_eq g E E' hE Q Q' hL hq,
    twistedSourceBaseChangeIso_hom_eq g E E' hE Q Q' hL hq,
    pullbackSourceIso_hom_eq E' Q' hσ' e', Functor.map_comp, Functor.map_comp]
  exact sourceFactorAux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorComparison_naturality_tensorHom g _ _)
    (pullbackTensorComparison_naturality_tensorHom σ' _ _)
    (schemePullbackCompIso_pullbackTensorComparison comm
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E))
    (kernelFactor_coherence g E E' hE Q Q' hL hq hσ hσ' comm) hinv

/-- **`hsrc` itself, from the inverse-line factor alone**, at the spelling
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_twistedSourceBaseChange`
takes its one remaining hypothesis.

`sourceCoherence_forward` read the other way round by `flipAux`, together with the three
crossings this spelling costs: `RingedSpaceModuleAdjunction.modulePullback` against
`AlgebraicGeometry.Scheme.Modules.pullback`, `Stacks.ClosedImmersion.pullbackCompIso` against
`schemePullbackCompIso` (`pullbackCompIso_hom_eq`), and
`Stacks.ProjectiveBundleConormal.twistedSourceBaseChange` against the forward map of
`twistedSourceBaseChangeIso`. They are taken in this declaration, which has its own heartbeat
budget, rather than in the one that does the diagram chase. -/
theorem sourceCoherence {σ : X ⟶ (bundle E).scheme}
    (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
    (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
    {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
    (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (hinv : (Scheme.Modules.pullback g).map (inverseTwistBaseChangeIso E Q e).hom ≫
        (Stacks.Divisors.inverseQuotientBaseChange g E E' Q Q' hL).hom =
      (schemePullbackCompIso comm (inverseTautologicalTwist E)).hom ≫
        (Scheme.Modules.pullback σ').map (inverseTwistBundleBaseChangeIso g E E' hE).hom ≫
          (inverseTwistBaseChangeIso E' Q' e').hom) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
            (twistedSource E Q)).hom ≫
          (modulePullback σ'.toLRSHom.toShHom).map
            (twistedSourceBaseChange g E E' hE Q Q' hL hq) := by
  rw [pullbackCompIso_hom_eq comm]
  exact flipAux ((Scheme.Modules.pullback g).mapIso (pullbackSourceIso E Q hσ e)) _
    (pullbackSourceIso E' Q' hσ' e') _ _
    (sourceCoherence_forward g E E' hE Q Q' hL hq hσ e hσ' e' comm hinv)

end Stacks.ProjectiveBundleConormal

end

