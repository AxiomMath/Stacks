module

import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Basic

/-!
# Cartan-Eilenberg resolutions: construction

This file glues a cochain complex `K` out of the short exact sequences
```
0 → Z^p → K^p → B^{p+1} → 0,      0 → B^p → Z^p → H^p → 0
```
where `Z^p = Ker(d_K^p)`, `B^p = Im(d_K^{p-1})` and `H^p = Z^p / B^p`, and assembles a
Cartan-Eilenberg resolution of `K` from injective resolutions of the `B^p` and the `H^p`, in an
abelian category with the horseshoe property: completing each of the two sequences by the
horseshoe lemma resolves first `Z^p` and then `K^p`, and the first differential of the resulting
double complex is the composite `I^{p,•} ↠ J_B^{p+1,•} ↪ J_Z^{p+1,•} ↪ I^{p+1,•}`, whose
kernel, image and cohomology are the chosen resolutions by construction. Starting the
construction at a degree `n` below which `K` vanishes produces a double complex with
`I^{p,q} = 0` for `p < n`.

## Implementation notes

The two applications of the horseshoe lemma are performed without the induction on `p` of the
source: taking the resolutions of the `B^p` and of the `H^p` as the data chosen first, and asking
the horseshoe lemma for the middle term of a short exact sequence *both* of whose ends are
already resolved, makes the two families `J_Z^{p,•}` and `I^{p,•}` functions of `p` rather than
terms of a recursion, at no cost in the mathematics.

## References

* [Stacks, Tag 015I]
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex StacksDraft.TotalComplexQuasiIso

namespace StacksDraft.CartanEilenbergResolutions

universe w w' v v' u u' v'' u''

section Glue

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **Cycles of a complex glued out of short exact sequences.** If
`0 → Z → X ^ p → B → 0` is a short exact sequence and the differential of `X` out of degree
`p` factors as `X ^ p ↠ B ↪ X ^ {p + 1}` through it, then `Z`, mapping to `X ^ p` by the
given monomorphism, is the object of cycles of `X` in degree `p`.

Both maps of the isomorphism are canonical: one way it is the lift of `Z ⟶ X ^ p` to the
cycles, the other way the factorization of `Ker (d ^ p) ⟶ X ^ p` through `Z`, available
because that composite is killed by `X ^ p ↠ B`, the second map being a monomorphism. -/
private theorem exists_cyclesIso {X : CochainComplex D ℤ} {p : ℤ} {Zo Bo : D}
    (ci : Zo ⟶ X.X p) (ee : X.X p ⟶ Bo) (wA : ci ≫ ee = 0)
    (hA : (ShortComplex.mk ci ee wA).ShortExact)
    (mm : Bo ⟶ X.X (p + 1)) [Mono mm] (hd : X.d p (p + 1) = ee ≫ mm) :
    ∃ u : X.cycles p ≅ Zo, u.hom ≫ ci = X.iCycles p := by
  have hmono : Mono ci := hA.mono_f
  have h1 : ci ≫ X.d p (p + 1) = 0 := by rw [hd, ← Category.assoc, wA, zero_comp]
  have h2 : X.iCycles p ≫ ee = 0 := by
    rw [← cancel_mono mm, zero_comp, Category.assoc, ← hd]
    simp
  obtain ⟨l, hl⟩ : ∃ l : X.cycles p ⟶ Zo, l ≫ ci = X.iCycles p := by
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hA.exact.fIsKernel (X.iCycles p) h2
    exact ⟨l, hl⟩
  refine ⟨⟨l, X.liftCycles ci (p + 1) (by simp) h1, ?_, ?_⟩, hl⟩
  · rw [← cancel_mono (X.iCycles p)]
    simp [hl]
  · rw [← cancel_mono ci]
    simp [hl]

/-- **The image of a morphism factored as an epimorphism followed by a monomorphism.** This
is `CategoryTheory.Limits.image.isoStrongEpiMono` in an abelian category, where every
epimorphism is strong, phrased as the existence of an isomorphism compatible with the two
monomorphisms to the target. -/
private theorem exists_imageIso {Y Z Bo : D} {f : Y ⟶ Z} (ee : Y ⟶ Bo) (mm : Bo ⟶ Z) [Epi ee]
    [Mono mm] (hf : ee ≫ mm = f) : ∃ v : image f ≅ Bo, image.ι f = v.hom ≫ mm := by
  have : StrongEpi ee := strongEpi_of_epi ee
  refine ⟨(image.isoStrongEpiMono ee mm hf).symm, ?_⟩
  simp only [Iso.symm_hom]
  rw [Iso.eq_inv_comp]
  exact image.isoStrongEpiMono_hom_comp_ι ee mm hf

/-- **Homology of a complex glued out of short exact sequences.** If `Z` is the object of
cycles of `X` in degree `p` (via an isomorphism `u`), if `0 → B → Z → H → 0` is a short exact
sequence, and if the map `X ^ q ⟶ Z` induced by the differential into degree `p` factors as
an epimorphism `X ^ q ↠ B` followed by `B ↪ Z`, then `H` is the homology of `X` in degree
`p`.

The homology is the cokernel of `X ^ q ⟶ Ker (d ^ p)` ([Mathlib]
`HomologicalComplex.homologyIsCokernel`), which by the factorization is the cokernel of
`B ↪ Z`, namely `H`. -/
private theorem exists_homologyIso {X : CochainComplex D ℤ} {p q : ℤ} (hq : q + 1 = p)
    {Zo Ho Bo : D} (u : X.cycles p ≅ Zo) (aa : Bo ⟶ Zo) (bb : Zo ⟶ Ho) (wB : aa ≫ bb = 0)
    (hB : (ShortComplex.mk aa bb wB).ShortExact) (ee : X.X q ⟶ Bo) [Epi ee]
    (hee : ee ≫ aa = X.toCycles q p ≫ u.hom) :
    ∃ w : X.homology p ≅ Ho, X.homologyπ p ≫ w.hom = u.hom ≫ bb := by
  have hepi : Epi bb := hB.epi_g
  have hcok := X.homologyIsCokernel q p ((ComplexShape.up ℤ).prev_eq' (by simpa using hq))
  have h0 : X.toCycles q p ≫ u.hom ≫ bb = 0 := by
    rw [← Category.assoc, ← hee, Category.assoc, wB, comp_zero]
  have h0' : aa ≫ u.inv ≫ X.homologyπ p = 0 := by
    refine zero_of_epi_comp ee ?_
    rw [← Category.assoc, hee, Category.assoc, Iso.hom_inv_id_assoc]
    simp
  obtain ⟨w1, hw1⟩ : ∃ w1 : X.homology p ⟶ Ho, X.homologyπ p ≫ w1 = u.hom ≫ bb := by
    obtain ⟨w1, hw1⟩ := CokernelCofork.IsColimit.desc' hcok (u.hom ≫ bb) h0
    exact ⟨w1, hw1⟩
  obtain ⟨w2, hw2⟩ : ∃ w2 : Ho ⟶ X.homology p, bb ≫ w2 = u.inv ≫ X.homologyπ p := by
    obtain ⟨w2, hw2⟩ := CokernelCofork.IsColimit.desc' hB.exact.gIsCokernel
      (u.inv ≫ X.homologyπ p) h0'
    exact ⟨w2, hw2⟩
  refine ⟨⟨w1, w2, ?_, ?_⟩, hw1⟩
  · rw [← cancel_epi (X.homologyπ p), ← Category.assoc, hw1, Category.assoc, hw2,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [← cancel_epi bb, ← Category.assoc, hw2, Category.assoc, hw1, Iso.inv_hom_id_assoc,
      Category.comp_id]

/-- A morphism which is, up to isomorphisms of its source and target, a quasi-isomorphism, is
one. -/
private lemma quasiIso_of_eq {A B A' B' : CochainComplex D ℤ} {f : A ⟶ B} (u : A ≅ A')
    (v : B ≅ B') (g : A' ⟶ B') [QuasiIso g] (hf : f = u.hom ≫ g ≫ v.inv) : QuasiIso f := by
  rw [hf]; infer_instance

/-- A short exact sequence whose two outer terms are zero objects has a zero object as its
middle term. -/
private theorem isZero_X₂_of_shortExact {S : ShortComplex D} (hS : S.ShortExact)
    (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ := by
  have := hS.mono_f
  obtain ⟨l, hl⟩ := hS.exact.lift' (𝟙 S.X₂) (h₃.eq_of_tgt _ _)
  rw [h₁.eq_of_src S.f 0, comp_zero] at hl
  rw [IsZero.iff_id_eq_zero]
  exact hl.symm

/-- A subobject of a zero object is a zero object. -/
private theorem isZero_of_mono {W X : D} (f : W ⟶ X) [Mono f] (hX : IsZero X) : IsZero W := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono f]
  exact hX.eq_of_tgt _ _

/-- A quotient of a zero object is a zero object. -/
private theorem isZero_of_epi {X Y : D} (f : X ⟶ Y) [Epi f] (hX : IsZero X) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi f]
  exact hX.eq_of_src _ _

/-- **A short complex with epimorphic second map whose first map is a kernel of the second map
followed by a monomorphism is short exact.** The kernel of `e` and the kernel of `e ≫ m` agree
when `m` is a monomorphism, so this is the usual criterion; it is phrased with the composite
`f = e ≫ m` given separately because the kernel one has at hand is a kernel of a differential,
not of the epimorphism it factors through. -/
private theorem shortExact_of_isKernel_of_epi {W X Y Z : D} {i : W ⟶ X} {e : X ⟶ Y} {m : Y ⟶ Z}
    {f : X ⟶ Z} (hf : e ≫ m = f) (w : i ≫ e = 0) (wf : i ≫ f = 0) [Mono i] [Epi e] [Mono m]
    (hi : IsLimit (KernelFork.ofι i wf)) : (ShortComplex.mk i e w).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) ‹Mono i› ‹Epi e›
  refine KernelFork.IsLimit.ofι' i w (fun {A} k hk => ?_)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hi k
    (by rw [← hf, ← Category.assoc, hk, zero_comp])
  exact ⟨l, hl⟩

/-- **The morphism to the kernel of a cokernel is an epimorphism**: if `g : Y ⟶ Z` is a cokernel
of `f : X ⟶ Y`, the morphism `X ⟶ Ker g` induced by `f` is an epimorphism. This is the
statement that `X → Y → Z` is exact at `Y`, read off the left homology datum given by the
chosen kernel of `g`. -/
private theorem epi_kernel_lift_of_isColimit {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (hg : IsColimit (CokernelCofork.ofπ g w)) : Epi (kernel.lift g f w) := by
  have hex : (ShortComplex.mk f g w).Exact := ShortComplex.exact_of_g_is_cokernel _ hg
  have := hex.epi_toCycles
  have hcomp : (IsLimit.conePointUniqueUpToIso (ShortComplex.mk f g w).cyclesIsKernel
      (kernelIsKernel g)).hom ≫ kernel.ι g = (ShortComplex.mk f g w).iCycles :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hk : kernel.lift g f w = (ShortComplex.mk f g w).toCycles ≫
      (IsLimit.conePointUniqueUpToIso (ShortComplex.mk f g w).cyclesIsKernel
        (kernelIsKernel g)).hom := by
    rw [← cancel_mono (kernel.ι g), Category.assoc, hcomp, kernel.lift_ι]
    simp
  rw [hk]
  infer_instance

end Glue

section Gluing

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **The data presenting a cochain complex as glued out of short exact sequences.** A gluing
datum for `X` consists of three families of objects `Z ^ p`, `B ^ p`, `H ^ p` — to be thought
of as the cycles `Ker (d ^ p)`, the boundaries `Im (d ^ {p - 1})` and the cohomology — together
with short exact sequences
```
0 → Z ^ p → X ^ p → B ^ {p + 1} → 0,      0 → B ^ p → Z ^ p → H ^ p → 0
```
whose maps compose to the differential of `X`.

Every cochain complex over an abelian category has one (`cochainGluingData`), and a gluing datum
determines the cycles, the image of a differential and the cohomology of `X` up to canonical
isomorphism (`exists_cyclesIso_of_cochainGluingData`, `exists_imageIso_of_cochainGluingData`,
`exists_homologyIso_of_cochainGluingData`). Its point is that the *converse* reading is available:
a complex assembled by hand out of two such families of short exact sequences — as the double
complex of a Cartan-Eilenberg resolution is — has its cycles, images and cohomology named by
that assembly, with no computation. -/
structure CochainGluingData (X : CochainComplex D ℤ) where
  /-- the cycles `Z ^ p = Ker (d ^ p)` -/
  Z : ℤ → D
  /-- the boundaries `B ^ p = Im (d ^ {p - 1})` -/
  B : ℤ → D
  /-- the cohomology `H ^ p` -/
  H : ℤ → D
  /-- the inclusion `Z ^ p ↪ X ^ p` -/
  ci : ∀ p, Z p ⟶ X.X p
  /-- the projection `X ^ p ↠ B ^ {p + 1}` -/
  ee : ∀ p, X.X p ⟶ B (p + 1)
  /-- the inclusion `B ^ p ↪ Z ^ p` -/
  aa : ∀ p, B p ⟶ Z p
  /-- the projection `Z ^ p ↠ H ^ p` -/
  bb : ∀ p, Z p ⟶ H p
  /-- `Z ^ p → X ^ p → B ^ {p + 1}` is zero -/
  wA : ∀ p, ci p ≫ ee p = 0
  /-- `B ^ p → Z ^ p → H ^ p` is zero -/
  wB : ∀ p, aa p ≫ bb p = 0
  /-- `0 → Z ^ p → X ^ p → B ^ {p + 1} → 0` is short exact -/
  hA : ∀ p, (ShortComplex.mk (ci p) (ee p) (wA p)).ShortExact
  /-- `0 → B ^ p → Z ^ p → H ^ p → 0` is short exact -/
  hB : ∀ p, (ShortComplex.mk (aa p) (bb p) (wB p)).ShortExact
  /-- the differential factors as `X ^ p ↠ B ^ {p + 1} ↪ Z ^ {p + 1} ↪ X ^ {p + 1}` -/
  hd : ∀ p, X.d p (p + 1) = ee p ≫ aa (p + 1) ≫ ci (p + 1)

/-- **The cycles of a glued complex are the object the datum calls the cycles.** -/
private theorem exists_cyclesIso_of_cochainGluingData {X : CochainComplex D ℤ}
    (G : CochainGluingData X)
    (p : ℤ) : ∃ u : X.cycles p ≅ G.Z p, u.hom ≫ G.ci p = X.iCycles p := by
  have := (G.hB (p + 1)).mono_f
  have := (G.hA (p + 1)).mono_f
  exact exists_cyclesIso (G.ci p) (G.ee p) (G.wA p) (G.hA p) (G.aa (p + 1) ≫ G.ci (p + 1))
    (G.hd p)

/-- **The image of a differential of a glued complex is the object the datum calls the
boundaries.** -/
theorem exists_imageIso_of_cochainGluingData {X : CochainComplex D ℤ}
    (G : CochainGluingData X)
    (p : ℤ) : ∃ v : image (X.dFrom p) ≅ G.B (p + 1),
      factorThruImage (X.dFrom p) ≫ v.hom = G.ee p := by
  have := (G.hB (p + 1)).mono_f
  have := (G.hA (p + 1)).mono_f
  have := (G.hA p).epi_g
  have hrel : (ComplexShape.up ℤ).Rel p (p + 1) := by simp
  have hf : G.ee p ≫ (G.aa (p + 1) ≫ G.ci (p + 1) ≫ (X.xNextIso hrel).inv) = X.dFrom p := by
    rw [X.dFrom_eq hrel, G.hd p]
    simp only [Category.assoc]
  obtain ⟨v, hv⟩ := exists_imageIso (f := X.dFrom p) (G.ee p)
    (G.aa (p + 1) ≫ G.ci (p + 1) ≫ (X.xNextIso hrel).inv) hf
  refine ⟨v, ?_⟩
  rw [← cancel_mono (G.aa (p + 1) ≫ G.ci (p + 1) ≫ (X.xNextIso hrel).inv), Category.assoc,
    ← hv, image.fac]
  exact hf.symm

/-- **The cohomology of a glued complex is the object the datum calls the cohomology.** -/
private theorem exists_homologyIso_of_cochainGluingData {X : CochainComplex D ℤ}
    (G : CochainGluingData X)
    (p q : ℤ) (hq : q + 1 = p) (u : X.cycles p ≅ G.Z p) (hu : u.hom ≫ G.ci p = X.iCycles p) :
    ∃ w : X.homology p ≅ G.H p, X.homologyπ p ≫ w.hom = u.hom ≫ G.bb p := by
  subst hq
  have := (G.hA q).epi_g
  have := (G.hA (q + 1)).mono_f
  refine exists_homologyIso rfl u (G.aa (q + 1)) (G.bb (q + 1)) (G.wB (q + 1)) (G.hB (q + 1))
    (G.ee q) ?_
  rw [← cancel_mono (G.ci (q + 1)), Category.assoc, Category.assoc, hu, ← G.hd q]
  simp

/-- **The canonical gluing datum of a cochain complex**: the cycles are `X.cycles p`, the
cohomology is `X.homology p`, and the boundaries are `Ker (X.homologyπ p)` — the kernel of the
projection from the cycles onto the cohomology, which is the image of the differential into
degree `p` and, unlike that image, is indexed by `p` without a subtraction. -/
noncomputable def cochainGluingData (X : CochainComplex D ℤ) : CochainGluingData X where
  Z p := X.cycles p
  B p := kernel (X.homologyπ p)
  H p := X.homology p
  ci p := X.iCycles p
  ee p := kernel.lift (X.homologyπ (p + 1)) (X.toCycles p (p + 1))
    (X.toCycles_comp_homologyπ p (p + 1))
  aa p := kernel.ι (X.homologyπ p)
  bb p := X.homologyπ p
  wA p := by
    have h : X.iCycles p ≫ X.toCycles p (p + 1) = 0 := by
      rw [← cancel_mono (X.iCycles (p + 1)), zero_comp, Category.assoc]
      simp
    rw [← cancel_mono (kernel.ι (X.homologyπ (p + 1))), zero_comp, Category.assoc,
      kernel.lift_ι, h]
  wB p := kernel.condition _
  hA p := by
    have : Epi (kernel.lift (X.homologyπ (p + 1)) (X.toCycles p (p + 1))
        (X.toCycles_comp_homologyπ p (p + 1))) :=
      epi_kernel_lift_of_isColimit (X.toCycles p (p + 1)) (X.homologyπ (p + 1)) _
        (X.homologyIsCokernel p (p + 1) ((ComplexShape.up ℤ).prev_eq' (by simp)))
    exact shortExact_of_isKernel_of_epi (f := X.d p (p + 1))
      (m := kernel.ι (X.homologyπ (p + 1)) ≫ X.iCycles (p + 1))
      (by rw [← Category.assoc, kernel.lift_ι]; simp) _ (by simp)
      (X.cyclesIsKernel p (p + 1) ((ComplexShape.up ℤ).next_eq' (by simp)))
  hB p := ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance
  hd p := by
    rw [← Category.assoc, kernel.lift_ι]
    simp

/-- **The image of a gluing datum under an exact functor.** -/
private abbrev CochainGluingData.map {X : CochainComplex D ℤ} (G : CochainGluingData X)
    {D' : Type u''}
    [Category.{v''} D'] [Abelian D'] (F : D ⥤ D') [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CochainGluingData ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) where
  Z p := F.obj (G.Z p)
  B p := F.obj (G.B p)
  H p := F.obj (G.H p)
  ci p := F.map (G.ci p)
  ee p := F.map (G.ee p)
  aa p := F.map (G.aa p)
  bb p := F.map (G.bb p)
  wA p := by rw [← F.map_comp, G.wA p, F.map_zero]
  wB p := by rw [← F.map_comp, G.wB p, F.map_zero]
  hA p := (G.hA p).map_of_exact F
  hB p := (G.hB p).map_of_exact F
  hd p := by
    change F.map (X.d p (p + 1)) = _
    rw [G.hd p, F.map_comp, F.map_comp]

end Gluing

section Assembly

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The construction of a Cartan-Eilenberg resolution from the horseshoe lemma.** Let `C`
be an abelian category with the horseshoe property (`HorseshoeProperty`, which by
`horseshoeProperty` it has as soon as it has enough injectives) in which every object has an
injective resolution vanishing when the object does (`exists_injectiveResolution_isZero`),
and let `K` be a cochain complex over `C` which is strictly `≥ n`. Then `K` has a
Cartan-Eilenberg resolution whose double complex is strictly `≥ n` in the first
direction.

The construction is the one described in the module docstring: choose injective resolutions
`J_B ^ {p, •}` of `B ^ p = Im (d ^ {p - 1})` and `J_H ^ {p, •}` of `H ^ p`, zero for `p < n`
since the objects are; apply the horseshoe property to
`0 → B ^ p → Z ^ p → H ^ p → 0` and then to `0 → Z ^ p → K ^ p → B ^ {p + 1} → 0`, getting
resolutions `J_Z ^ {p, •}` of `Z ^ p` and `I ^ {p, •}` of `K ^ p` inside short exact
sequences of complexes; and let the double complex be `p ↦ I ^ {p, •}` with differential the
composite `I ^ {p, •} ↠ J_B ^ {p + 1, •} ↪ J_Z ^ {p + 1, •} ↪ I ^ {p + 1, •}`, whose
kernel, image and cohomology at `p` are `J_Z ^ {p, •}`, `J_B ^ {p + 1, •}` and
`J_H ^ {p, •}`. -/
@[ega "0 11.4.2" "partial"]
private theorem exists_cartanEilenbergResolution_of_horseshoe (h : HorseshoeProperty C)
    (hres : ∀ A : C, ∃ (T : CochainComplex C ℤ)
      (ι : (single C (ComplexShape.up ℤ) 0).obj A ⟶ T),
      CochainComplex.IsStrictlyGE T 0 ∧ (∀ q, Injective (T.X q)) ∧ QuasiIso ι ∧
        (IsZero A → IsZero T))
    (K : CochainComplex C ℤ) (n : ℤ) [CochainComplex.IsStrictlyGE K n] :
    ∃ I : CochainComplex.CartanEilenbergResolution K,
      CochainComplex.IsStrictlyGE I.bicomplex n := by
  classical
  -- the short exact sequences `K` is glued out of
  let GK : CochainGluingData K := cochainGluingData K
  -- injective resolutions of the boundaries and of the cohomology, zero where those vanish
  choose JB ιB hgeB hinjB hqiB hzB using fun p : ℤ => hres (GK.B p)
  choose JH ιH hgeH hinjH hqiH hzH using fun p : ℤ => hres (GK.H p)
  -- the horseshoe property on `0 → B ^ p → Z ^ p → H ^ p → 0`
  choose JZ aJ bJ wJ ιZ hseJ hgeJ hinjJ hqiJ hcJ₁ hcJ₂ using fun p : ℤ =>
    h _ (GK.hB p) (JB p) (JH p) (hgeB p) (hgeH p) (hinjB p) (hinjH p) (ιB p) (ιH p)
      (hqiB p) (hqiH p)
  -- the horseshoe property on `0 → Z ^ p → K ^ p → B ^ {p + 1} → 0`
  choose Ic fI gI wI ιK hseI hgeI hinjI hqiI hcI₁ hcI₂ using fun p : ℤ =>
    h _ (GK.hA p) (JZ p) (JB (p + 1)) (hgeJ p) (hgeB (p + 1)) (hinjJ p) (hinjB (p + 1))
      (ιZ p) (ιB (p + 1)) (hqiJ p) (hqiB (p + 1))
  -- the four commutation identities, with the maps of the two sequences spelled out
  have hcJ₁' : ∀ p : ℤ, ιB p ≫ aJ p
    = (single C (ComplexShape.up ℤ) 0).map (GK.aa p) ≫ ιZ p := hcJ₁
  have hcJ₂' : ∀ p : ℤ, ιZ p ≫ bJ p
    = (single C (ComplexShape.up ℤ) 0).map (GK.bb p) ≫ ιH p := hcJ₂
  have hcI₁' : ∀ p : ℤ, ιZ p ≫ fI p
    = (single C (ComplexShape.up ℤ) 0).map (GK.ci p) ≫ ιK p := hcI₁
  have hcI₂' : ∀ p : ℤ, ιK p ≫ gI p
    = (single C (ComplexShape.up ℤ) 0).map (GK.ee p) ≫ ιB (p + 1) := hcI₂
  -- the double complex, with its gluing datum and its augmentation
  have hsq : ∀ p : ℤ, (gI p ≫ aJ (p + 1) ≫ fI (p + 1)) ≫
      (gI (p + 1) ≫ aJ (p + 1 + 1) ≫ fI (p + 1 + 1)) = 0 := by
    intro p
    have h0 : fI (p + 1) ≫ gI (p + 1) ≫ aJ (p + 1 + 1) ≫ fI (p + 1 + 1) = 0 := by
      rw [← Category.assoc, wI (p + 1), zero_comp]
    simp only [Category.assoc, h0, comp_zero]
  let Ibi : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    CochainComplex.of Ic (fun p => gI p ≫ aJ (p + 1) ≫ fI (p + 1)) hsq
  have hIbid : ∀ p : ℤ, Ibi.d p (p + 1) = gI p ≫ aJ (p + 1) ≫ fI (p + 1) := fun p => by
    apply CochainComplex.of_d
  let GI : CochainGluingData Ibi :=
    { Z := JZ, B := JB, H := JH, ci := fI, ee := gI, aa := aJ, bb := bJ,
      wA := wI, wB := wJ, hA := hseI, hB := hseJ, hd := hIbid }
  obtain ⟨ε, hε⟩ : ∃ ε : ((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ Ibi, ∀ p, ε.f p = ιK p :=
    ⟨{ f := ιK
       comm' := fun i j hij => by
         obtain rfl : j = i + 1 := hij.symm
         show ιK i ≫ Ibi.d i (i + 1)
           = (single C (ComplexShape.up ℤ) 0).map (K.d i (i + 1)) ≫ ιK (i + 1)
         rw [hIbid i, reassoc_of% (hcI₂' i), reassoc_of% (hcJ₁' (i + 1)), hcI₁' (i + 1),
           ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ← GK.hd i] },
      fun _ => rfl⟩
  -- the gluing datum of `K` placed in second degree `0`
  let GKK : CochainGluingData (((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K) := GK.map (single C (ComplexShape.up ℤ) 0)
  choose cyK hcyK using fun p : ℤ => exists_cyclesIso_of_cochainGluingData GKK p
  choose cyI hcyI using fun p : ℤ => exists_cyclesIso_of_cochainGluingData GI p
  choose imK himK using fun p : ℤ => exists_imageIso_of_cochainGluingData GKK p
  choose imI himI using fun p : ℤ => exists_imageIso_of_cochainGluingData GI p
  choose hoK hhoK using fun p : ℤ =>
    exists_homologyIso_of_cochainGluingData GKK p (p - 1) (by ring) (cyK p) (hcyK p)
  choose hoI hhoI using fun p : ℤ =>
    exists_homologyIso_of_cochainGluingData GI p (p - 1) (by ring) (cyI p) (hcyI p)
  -- the same six identities, with the projections of the two gluing data spelled out
  have hcyK' : ∀ p : ℤ, (cyK p).hom ≫ (single C (ComplexShape.up ℤ) 0).map (GK.ci p)
    = (((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).iCycles p := hcyK
  have hcyI' : ∀ p : ℤ, (cyI p).hom ≫ fI p = Ibi.iCycles p := hcyI
  have himK' : ∀ p : ℤ, factorThruImage ((((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).dFrom p) ≫ (imK p).hom
    = (single C (ComplexShape.up ℤ) 0).map (GK.ee p) := himK
  have himI' : ∀ p : ℤ, factorThruImage (Ibi.dFrom p) ≫ (imI p).hom = gI p := himI
  have hhoK' : ∀ p : ℤ, (((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homologyπ p ≫ (hoK p).hom
    = (cyK p).hom ≫ (single C (ComplexShape.up ℤ) 0).map (GK.bb p) := hhoK
  have hhoI' : ∀ p : ℤ, Ibi.homologyπ p ≫ (hoI p).hom = (cyI p).hom ≫ bJ p := hhoI
  -- the map on cycles induced by the augmentation is the resolution of the cycles
  have keyC : ∀ p : ℤ, cyclesMap ε p ≫ (cyI p).hom = (cyK p).hom ≫ ιZ p := by
    intro p
    have := (hseI p).mono_f
    rw [← cancel_mono (fI p)]
    simp only [Category.assoc]
    rw [hcyI' p, HomologicalComplex.cyclesMap_i, hε p, hcI₁' p, ← Category.assoc, hcyK' p]
  -- the double complex vanishes in first degrees `< n`, because `K` does
  have hzeroIc : ∀ p : ℤ, p < n → IsZero (Ic p) := by
    intro p hp
    have := (GK.hA p).mono_f
    have := (GK.hA p).epi_g
    have := (GK.hB p).mono_f
    have := (GK.hB p).epi_g
    have hKp : IsZero (K.X p) := K.isZero_of_isStrictlyGE n p hp
    have hZp : IsZero (GK.Z p) := isZero_of_mono (GK.ci p) hKp
    exact isZero_X₂_of_shortExact (hseI p)
      (isZero_X₂_of_shortExact (hseJ p) (hzB p (isZero_of_mono (GK.aa p) hZp))
        (hzH p (isZero_of_epi (GK.bb p) hZp)))
      (hzB (p + 1) (isZero_of_epi (GK.ee p) hKp))
  have hgeIbi : CochainComplex.IsStrictlyGE Ibi n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hzeroIc i hi
  refine ⟨{ bicomplex := Ibi
            ε := ε
            boundedBelow := ⟨n, hgeIbi⟩
            isStrictlyGE := hgeI
            injective := hinjI
            quasiIso := ?_
            injective_cycles := ?_
            quasiIso_cyclesMap := ?_
            injective_image := ?_
            quasiIso_imageMap := ?_
            injective_homology := ?_
            quasiIso_homologyMap := ?_ }, hgeIbi⟩
  · intro p
    rw [hε p]
    exact hqiI p
  · exact fun p q => Injective.of_iso
      (((HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapIso (cyI p)).symm) (hinjJ p q)
  · intro p
    have := hqiJ p
    refine quasiIso_of_eq (cyK p) (cyI p) (ιZ p) ?_
    rw [← Category.assoc, ← keyC p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact fun p q => Injective.of_iso
      (((HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapIso (imI p)).symm)
      (hinjB (p + 1) q)
  · intro p
    have := hqiB (p + 1)
    refine quasiIso_of_eq (imK p) (imI p) (ιB (p + 1)) ?_
    have hfac : factorThruImage (Ibi.dFrom p) = gI p ≫ (imI p).inv := by
      rw [← himI' p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hfm : factorThruImage ((((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).dFrom p) ≫ image.map (ε.sqFrom p)
      = ιK p ≫ factorThruImage (Ibi.dFrom p) := by
      rw [← hε p]
      exact image.factor_map (ε.sqFrom p)
    rw [← cancel_epi (factorThruImage ((((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).dFrom p)), hfm, hfac, reassoc_of% (hcI₂' p),
      reassoc_of% (himK' p)]
  · exact fun p q => Injective.of_iso
      (((HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapIso (hoI p)).symm) (hinjH p q)
  · intro p
    have := hqiH p
    refine quasiIso_of_eq (hoK p) (hoI p) (ιH p) ?_
    have hπ : Ibi.homologyπ p = (cyI p).hom ≫ bJ p ≫ (hoI p).inv := by
      rw [← Category.assoc, ← hhoI' p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← cancel_epi ((((single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homologyπ p), HomologicalComplex.homologyπ_naturality, hπ,
      reassoc_of% (hhoK' p), ← reassoc_of% (hcJ₂' p), ← reassoc_of% (keyC p)]

end Assembly

end StacksDraft.CartanEilenbergResolutions

end
