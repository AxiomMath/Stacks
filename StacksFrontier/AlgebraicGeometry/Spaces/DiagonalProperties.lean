module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest

/-!
# Properties of the diagonal of an algebraic space (Stacks 02X4)

Let `S` be a scheme contained in a big fppf site `B` and let `F` be an algebraic space over
`S`. Its diagonal `Δ : F ⟶ F × F` is representable, and this file proves that as a
representable morphism it is locally of finite type, a monomorphism, separated and locally
quasi-finite: that is, each of these four properties of morphisms of schemes holds for every
represented base change of `Δ`.

The Stacks proof is the following. Choose a scheme atlas `q : h_U ⟶ F`, surjective and étale.
Then `q × q : h_{U × U} ⟶ F × F` is again surjective and étale, because each of those two
properties is stable under base change and composition and `q × q` factors as
`(q, 1) ≫ (1, q)`. The base change of `Δ` along `q × q` is the kernel pair `R = U ×_F U` of
`q` mapping to `U × U` by `(s, t)`; since `q` is étale, so is `s`, and therefore `(s, t)` is
locally of finite type, being a factor of `s = (s, t) ≫ pr₁`. It is also a monomorphism,
because `s` and `t` are jointly monomorphic — this is immediate from the kernel-pair square
being cartesian — hence separated and, being locally of finite type, locally quasi-finite.
Each of the four properties is stable under base change and local on the target for the fppf
topology, so **Stacks 02WZ** transports it from this one base change back to `Δ` itself.

## Main results

* `AlgebraicGeometry.presheaf_locallyOfFiniteType_diag`: **Stacks 02X4**, part (1).
* `AlgebraicGeometry.presheaf_monomorphisms_diag`: **Stacks 02X4**, part (2).
* `AlgebraicGeometry.presheaf_isSeparated_diag`: **Stacks 02X4**, part (3).
* `AlgebraicGeometry.presheaf_locallyQuasiFinite_diag`: **Stacks 02X4**, part (4).

## Implementation notes

The absolute product `U ⨯ U` of the site is needed throughout. `HasBinaryProducts` for the big
fppf category over `S` comes from
`AlgebraicGeometry.Space.bigFppfOver_hasBinaryProducts`, so every occurrence of `U ⨯ U` in
this file denotes the same object.

Joint monomorphy of the two projections of the kernel pair is proved directly from the
cartesian square, by `CategoryTheory.Limits.IsPullback.hom_ext` and faithfulness of Yoneda.
The Stacks text instead invokes the equivalence-relation structure of the kernel pair
(**Stacks 0262**), which is a substantially longer route to the same three lines.

Part (3) is deduced from part (2) by monotonicity of
`CategoryTheory.MorphismProperty.presheaf`, a monomorphism of schemes being separated; the
alternative — running the descent argument for `AlgebraicGeometry.IsSeparated` directly —
would need separatedness to be fppf local on the target, which is **Stacks 02KU** and is not
available in this library. Parts (1), (2) and (4) use the descent argument, whose fppf
locality hypotheses come from the fpqc statements **Stacks 02KX**, **Stacks 02YK** and
**Stacks 02VI** together with `AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`;
that last step is the fppf half of **Stacks 02WH**, which this library does not yet state.

## References

* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The product `q × q : h_{U ⨯ U} ⟶ F ⨯ F` of an atlas `q : h_U ⟶ F` with itself, written
through the canonical comparison of `h_{U ⨯ U}` with `h_U ⨯ h_U`. -/
noncomputable def atlasProd {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) : yoneda.obj (U ⨯ U) ⟶ F ⨯ F :=
  prod.lift (yoneda.map prod.fst ≫ q) (yoneda.map prod.snd ≫ q)

/-- The comparison isomorphism `h_{U ⨯ U} ≅ h_U ⨯ h_U`, Yoneda preserving products. -/
noncomputable def yonedaProdIso (U : BigFppfOver B S hS) :
    yoneda.obj (U ⨯ U) ≅ (yoneda.obj U ⨯ yoneda.obj U :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  preservesLimitIso yoneda (pair U U) ≪≫ HasLimit.isoOfNatIso (pairComp U U yoneda)

/-- The comparison `yonedaProdIso` followed by the first projection is the Yoneda image of the
first projection `U ⨯ U ⟶ U`. -/
theorem yonedaProdIso_hom_fst (U : BigFppfOver B S hS) :
    (yonedaProdIso B S hS U).hom ≫ prod.fst = yoneda.map prod.fst := by
  simp [yonedaProdIso, prod.fst, pairComp]

/-- The comparison `yonedaProdIso` followed by the second projection is the Yoneda image of the
second projection `U ⨯ U ⟶ U`. -/
theorem yonedaProdIso_hom_snd (U : BigFppfOver B S hS) :
    (yonedaProdIso B S hS U).hom ≫ prod.snd = yoneda.map prod.snd := by
  simp [yonedaProdIso, prod.snd, pairComp]

/-- The kernel pair `R = U ×_F U` of an atlas `q : h_U ⟶ F`, together with the identification
of the base change of the diagonal of `F` along `q × q` with `(s, t) : R ⟶ U ⨯ U`. -/
structure AtlasKernelPair {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) where
  /-- The kernel pair, an object of the site. -/
  R : BigFppfOver B S hS
  /-- First projection of the kernel pair. -/
  s : R ⟶ U
  /-- Second projection of the kernel pair. -/
  t : R ⟶ U
  /-- The structure morphism of the kernel pair to `F`. -/
  toSpace : yoneda.obj R ⟶ F
  /-- `s` and `t` form a kernel pair of `q`. -/
  kernelPair : IsPullback (yoneda.map s) (yoneda.map t) q q
  /-- The diagonal of `F` pulls back along `q × q` to `(s, t)`. -/
  diagonalPullback :
    IsPullback toSpace (yoneda.map (prod.lift s t)) (diag F) (atlasProd B S hS q)

/-- The kernel pair of an atlas exists as soon as the diagonal of `F` is representable: it is
the representing object of the base change of the diagonal along `(q, q)`. -/
noncomputable def atlasKernelPair {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (hdiag : yoneda.relativelyRepresentable (diag F)) : AtlasKernelPair B S hS q := by
  let hq := hdiag.of_diag q
  let R := hq.pullback q
  let s : R ⟶ U := yoneda.preimage (hq.fst q)
  let t : R ⟶ U := hq.snd q
  have hK : IsPullback (yoneda.map s) (yoneda.map t) q q := by
    simpa [s, t] using hq.isPullback q
  let j : R ⟶ U ⨯ U := prod.lift s t
  let qprod := atlasProd B S hS q
  refine ⟨R, s, t, hq.fst q ≫ q, hK, ?_⟩
  let e := yonedaProdIso B S hS U
  have ehfst : e.hom ≫ prod.fst = yoneda.map prod.fst := yonedaProdIso_hom_fst B S hS U
  have ehsnd : e.hom ≫ prod.snd = yoneda.map prod.snd := yonedaProdIso_hom_snd B S hS U
  have hcomm : CommSq (hq.fst q ≫ q) (yoneda.map j) (diag F) qprod := by
    refine ⟨?_⟩
    apply prod.hom_ext
    · calc
        (hq.fst q ≫ q) ≫ diag F ≫ prod.fst = hq.fst q ≫ q := by simp
        _ = yoneda.map s ≫ q := by simp [s]
        _ = yoneda.map j ≫ qprod ≫ prod.fst := by
          simp only [j, qprod, atlasProd, prod.lift_fst]
          rw [← Category.assoc, ← Functor.map_comp, prod.lift_fst]
    · calc
        (hq.fst q ≫ q) ≫ diag F ≫ prod.snd = hq.fst q ≫ q := by simp
        _ = yoneda.map s ≫ q := by simp [s]
        _ = yoneda.map t ≫ q := hK.w
        _ = yoneda.map j ≫ qprod ≫ prod.snd := by
          simp only [j, qprod, atlasProd, prod.lift_snd]
          rw [← Category.assoc, ← Functor.map_comp, prod.lift_snd]
  let lift := fun c : PullbackCone (diag F) qprod =>
    let h₁ : c.fst = c.snd ≫ yoneda.map prod.fst ≫ q := by
      have := congrArg (fun k => k ≫ prod.fst) c.condition
      simpa [qprod, atlasProd, Category.assoc] using this
    let h₂ : c.fst = c.snd ≫ yoneda.map prod.snd ≫ q := by
      have := congrArg (fun k => k ≫ prod.snd) c.condition
      simpa [qprod, atlasProd, Category.assoc] using this
    hK.lift (c.snd ≫ yoneda.map prod.fst) (c.snd ≫ yoneda.map prod.snd) (h₁.symm.trans h₂)
  apply IsPullback.of_isLimit' hcomm
  refine PullbackCone.IsLimit.mk hcomm.w lift ?_ ?_ ?_
  · intro c
    calc
      lift c ≫ hq.fst q ≫ q = lift c ≫ yoneda.map s ≫ q := by simp [s]
      _ = c.snd ≫ yoneda.map prod.fst ≫ q := by simp [lift]
      _ = c.fst := (show c.fst = c.snd ≫ yoneda.map prod.fst ≫ q from by
        have := congrArg (fun k => k ≫ prod.fst) c.condition
        simpa [qprod, atlasProd, Category.assoc] using this).symm
  · intro c
    apply (cancel_mono e.hom).1
    apply prod.hom_ext
    · calc
        lift c ≫ yoneda.map j ≫ e.hom ≫ prod.fst = lift c ≫ yoneda.map s := by
          simp [j, ehfst, ← Functor.map_comp]
        _ = c.snd ≫ yoneda.map prod.fst := by simp [lift]
        _ = c.snd ≫ e.hom ≫ prod.fst := by rw [ehfst]
    · calc
        lift c ≫ yoneda.map j ≫ e.hom ≫ prod.snd = lift c ≫ yoneda.map t := by
          simp [j, ehsnd, ← Functor.map_comp]
        _ = c.snd ≫ yoneda.map prod.snd := by simp [lift]
        _ = c.snd ≫ e.hom ≫ prod.snd := by rw [ehsnd]
  · intro c k hk₁ hk₂
    apply hK.hom_ext
    · calc
        k ≫ yoneda.map s = k ≫ yoneda.map j ≫ e.hom ≫ prod.fst := by
          simp [j, ehfst, ← Functor.map_comp]
        _ = c.snd ≫ e.hom ≫ prod.fst := by
          simpa only [Category.assoc] using congrArg (fun z => z ≫ e.hom ≫ prod.fst) hk₂
        _ = c.snd ≫ yoneda.map prod.fst := by rw [ehfst]
        _ = lift c ≫ yoneda.map s := by simp [lift]
    · calc
        k ≫ yoneda.map t = k ≫ yoneda.map j ≫ e.hom ≫ prod.snd := by
          simp [j, ehsnd, ← Functor.map_comp]
        _ = c.snd ≫ e.hom ≫ prod.snd := by
          simpa only [Category.assoc] using congrArg (fun z => z ≫ e.hom ≫ prod.snd) hk₂
        _ = c.snd ≫ yoneda.map prod.snd := by rw [ehsnd]
        _ = lift c ≫ yoneda.map t := by simp [lift]

/-- A relative property stable under base change and composition passes from an atlas
`q : h_U ⟶ F` to its square `q × q : h_{U ⨯ U} ⟶ F ⨯ F`, which factors as
`(q, 1) ≫ (1, q)`. -/
private theorem presheaf_atlasProd {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    (hq : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))) q) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (atlasProd B S hS q) := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  let QP := Q.presheaf
  have : QP.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  have : QP.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  have : QP.RespectsIso := MorphismProperty.relative_respectsIso Q
  let e := yonedaProdIso B S hS U
  have h₁ : QP (prod.map q (𝟙 (yoneda.obj U))) :=
    (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
      (IsPullback.of_prod_fst_with_id q (yoneda.obj U)) hq
  have h₂' : QP (prod.map q (𝟙 F)) :=
    (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
      (IsPullback.of_prod_fst_with_id q F) hq
  let a : F ⨯ yoneda.obj U ≅ yoneda.obj U ⨯ F := prod.braiding F (yoneda.obj U)
  let b : F ⨯ F ≅ F ⨯ F := prod.braiding F F
  have h₂ : QP (prod.map (𝟙 F) q) := by
    have hpost : QP (a.hom ≫ prod.map q (𝟙 F) ≫ b.hom) :=
      MorphismProperty.RespectsIso.postcomp QP b.hom _
        (MorphismProperty.RespectsIso.precomp QP a.hom _ h₂')
    have heq : a.hom ≫ prod.map q (𝟙 F) ≫ b.hom = prod.map (𝟙 F) q := by
      ext <;> simp [a, b, prod.braiding]
    rwa [heq] at hpost
  have hprod : QP (prod.map q q) := by
    have hcomp : QP (prod.map q (𝟙 (yoneda.obj U)) ≫ prod.map (𝟙 F) q) :=
      MorphismProperty.comp_mem QP _ _ h₁ h₂
    have heq : prod.map q (𝟙 (yoneda.obj U)) ≫ prod.map (𝟙 F) q = prod.map q q := by
      apply prod.hom_ext <;> simp
    rwa [heq] at hcomp
  have heq : e.hom ≫ prod.map q q = atlasProd B S hS q := by
    apply prod.hom_ext
    · calc
        e.hom ≫ prod.map q q ≫ prod.fst = (e.hom ≫ prod.fst) ≫ q := by simp [Category.assoc]
        _ = yoneda.map prod.fst ≫ q := by rw [yonedaProdIso_hom_fst]
        _ = atlasProd B S hS q ≫ prod.fst := by simp [atlasProd]
    · calc
        e.hom ≫ prod.map q q ≫ prod.snd = (e.hom ≫ prod.snd) ≫ q := by simp [Category.assoc]
        _ = yoneda.map prod.snd ≫ q := by rw [yonedaProdIso_hom_snd]
        _ = atlasProd B S hS q ≫ prod.snd := by simp [atlasProd]
  simpa only [heq] using MorphismProperty.RespectsIso.precomp QP e.hom _ hprod

/-- The two projections of a kernel pair are jointly monomorphic, so `(s, t) : R ⟶ U ⨯ U` is a
monomorphism of the site. This is the cartesian square alone, by faithfulness of Yoneda. -/
private theorem mono_prodLift_of_kernelPair {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U R : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F} {s t : R ⟶ U}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) q q) : Mono (prod.lift s t) := by
  refine ⟨fun {Z} a b hab => ?_⟩
  have h₁ : a ≫ s = b ≫ s := by simpa using congrArg (fun k => k ≫ prod.fst) hab
  have h₂ : a ≫ t = b ≫ t := by simpa using congrArg (fun k => k ≫ prod.snd) hab
  refine yoneda.map_injective (hR.hom_ext ?_ ?_)
  · rw [← Functor.map_comp, ← Functor.map_comp, h₁]
  · rw [← Functor.map_comp, ← Functor.map_comp, h₂]

/-- The four properties of the kernel-pair map `(s, t) : R ⟶ U ⨯ U` of an étale atlas: it is
locally of finite type, a monomorphism, separated and locally quasi-finite. -/
private theorem kernelPairProperties {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U R : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (prod.lift s t)) ∧
      Mono ((BigFppfOver.toScheme B S hS).map (prod.lift s t)) ∧
      IsSeparated ((BigFppfOver.toScheme B S hS).map (prod.lift s t)) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (prod.lift s t)) := by
  let T := BigFppfOver.toScheme B S hS
  have hsEtale : Etale (T.map s) := hqEtale.property q (yoneda.map t) s hR.flip
  have hsLft : LocallyOfFiniteType (T.map s) := inferInstance
  have hjComp : LocallyOfFiniteType (T.map (prod.lift s t) ≫ T.map prod.fst) := by
    rw [← T.map_comp]
    simpa using hsLft
  have hjLft : LocallyOfFiniteType (T.map (prod.lift s t)) :=
    locallyOfFiniteType_of_comp (T.map (prod.lift s t)) (T.map prod.fst)
  have : Mono (prod.lift s t) := mono_prodLift_of_kernelPair B S hS hR
  have hjMono : Mono (T.map (prod.lift s t)) := preserves_mono_of_preservesLimit T _
  exact ⟨hjLft, hjMono, IsSeparated.isSeparated_of_mono _, inferInstance⟩

/-- The descent step. If `P` is a property of morphisms of schemes which is stable under base
change and fppf local on the target, and if it holds for the kernel-pair map `(s, t)` of every
étale atlas of an algebraic space `F`, then the diagonal of `F` has the associated relative
property. -/
private theorem presheaf_diag_of_kernelPair {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : ∀ {U R : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) q q →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q →
      P ((BigFppfOver.toScheme B S hS).map (prod.lift s t))) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) (diag F) := by
  obtain ⟨U, q, hqSurj, hqEtale⟩ := hF.exists_atlas
  have hdiag := hF.diagonal_representable
  let data := atlasKernelPair B S hS q hdiag
  have hPj := hP q data.s data.t data.kernelPair hqEtale
  let T := BigFppfOver.toScheme B S hS
  let qprod := atlasProd B S hS q
  have : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => ⟨hg.1.comp hf.1⟩⟩
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun f g _ _ => Etale.etale_comp f g⟩
  have hqprodSurj := presheaf_atlasProd B S hS q (@Surjective.{u}) hqSurj
  have hqprodEtale := presheaf_atlasProd B S hS q (@Etale.{u}) hqEtale
  have hcan : IsPullback (hdiag.fst qprod) (yoneda.map (hdiag.snd qprod)) (diag F) qprod :=
    hdiag.isPullback qprod
  let eD := data.diagonalPullback.isoIsPullback _ _ hcan
  let e := yoneda.preimageIso eD
  have he : e.hom ≫ hdiag.snd qprod = prod.lift data.s data.t := by
    apply yoneda.map_injective
    simp [e, eD, data.diagonalPullback.isoIsPullback_hom_snd _ _ hcan]
  have heScheme : T.map e.hom ≫ T.map (hdiag.snd qprod) =
      T.map (prod.lift data.s data.t) := by rw [← T.map_comp, he]
  exact (presheaf_inverseImage_iff_atlas_snd B S hS P (diag F) hdiag (U ⨯ U) qprod
    hqprodSurj hqprodEtale).2
    ((P.arrow_mk_iso_iff (Arrow.isoMk (T.mapIso e) (Iso.refl _) heScheme)).1 hPj)

/-- **Stacks 02X4, part (1).** The diagonal of an algebraic space over `S` is locally of
finite type: every represented base change of it is a morphism of schemes locally of finite
type. -/
@[stacks 02X4 "part (1)"]
theorem presheaf_locallyOfFiniteType_diag (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) := by
  have : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_diag_of_kernelPair B S hS hF (@LocallyOfFiniteType.{u})
    fun q s t hR hqEtale => (kernelPairProperties B S hS q s t hR hqEtale).1

/-- **Stacks 02X4, part (2).** The diagonal of an algebraic space over `S` is a monomorphism:
every represented base change of it is a monomorphism of schemes. -/
@[stacks 02X4 "part (2)"]
theorem presheaf_monomorphisms_diag (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) := by
  have : MorphismProperty.IsLocalAtTarget (MorphismProperty.monomorphisms Scheme.{u})
      Scheme.fppfPrecoverage := .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_diag_of_kernelPair B S hS hF (MorphismProperty.monomorphisms Scheme.{u})
    fun q s t hR hqEtale => (kernelPairProperties B S hS q s t hR hqEtale).2.1

/-- **Stacks 02X4, part (3).** The diagonal of an algebraic space over `S` is separated: every
represented base change of it is a separated morphism of schemes. This follows from part (2),
a monomorphism of schemes being separated. -/
@[stacks 02X4 "part (3)"]
theorem presheaf_isSeparated_diag (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) := by
  refine MorphismProperty.relative_monotone (F := yoneda)
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) ?_) _
    (presheaf_monomorphisms_diag B S hS F hF)
  exact fun _ _ f (_ : Mono f) => IsSeparated.isSeparated_of_mono f

/-- **Stacks 02X4, part (4).** The diagonal of an algebraic space over `S` is locally
quasi-finite: every represented base change of it is a morphism of schemes which is locally of
finite type and has discrete fibres. -/
@[stacks 02X4 "part (4)"]
theorem presheaf_locallyQuasiFinite_diag (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (diag F) := by
  have : MorphismProperty.IsStableUnderBaseChange
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.IsLocalAtTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) Scheme.fppfPrecoverage :=
    .of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_diag_of_kernelPair B S hS hF
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    fun q s t hR hqEtale =>
      ⟨(kernelPairProperties B S hS q s t hR hqEtale).1,
        (kernelPairProperties B S hS q s t hR hqEtale).2.2.2⟩

end

end AlgebraicGeometry

end
