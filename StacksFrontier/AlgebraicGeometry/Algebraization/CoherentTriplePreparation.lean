module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplayRestrict
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Pasting
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# Preparing a coherent triple

Let `A` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor, and let `(F, F₀, α)` be a
coherent triple for `(A, f)`: a coherent module `F` on the punctured spectrum `U = Spec A ∖ {𝔪}`
on which `f` acts injectively, a coherent module `F₀` on the closed fibre `X₀ = Spec (A / fA)`,
and an identification of the two over the punctured closed fibre `U₀ = U ∩ X₀`.

This file produces a *prepared extension* of such a triple: a coherent module `F'` on `Spec A`
on which `f` acts injectively, an isomorphism `F'|_U ≅ F`, and a map `F'|_{X₀} ⟶ F₀` agreeing
with `α` over `U₀`. That is the content of [Stacks, Tag 0F23], and `F'` is the module from which
the Euler characteristic attached to the triple is computed.

## Main results

* `Stacks.Algebraization.nonempty_preparedExtension`: **[Stacks, Tag 0F23]** — every coherent
  triple admits a prepared extension.

## Implementation notes

The construction has three steps.

First the coherent module `F` on the punctured spectrum is extended to `Spec A`. The source
quotes the finiteness clause of [Stacks, Tag 0BK0]; here the extension is produced instead as a
coherent subobject `G` of the direct image `j_*F`, by applying the subobject-extension theorem
[Stacks, Tag 01PF] to the subobject of `(j_*F)|_U ≅ F` cut out by that isomorphism and reading
coherence as quasi-coherence together with finite type ([Stacks, Tag 01XZ]). Keeping the
monomorphism `G ⟶ j_*F` is what makes the injectivity of `f` on the sections of the extension
automatic, by `Stacks.Algebraization.regular_of_mono_pushforward`.

Second the map to the closed fibre is produced. The transpose of the triple's identification
along the adjunction for the restricted closed immersion `k : U₀ ⟶ U`, read through affine base
change for the square
```
U₀ ⟶ U
|     |
v     v
X₀ ⟶ Spec A
```
([Stacks, Tag 02KG]), is a morphism `G|_U ⟶ (i_*F₀)|_U`. The extension assertion of the first
display of [Stacks, Tag 01YB] turns it into a morphism `𝔪ⁿ G ⟶ i_*F₀` for some `n`, whose
transpose along the adjunction for `i` is the required map on the closed fibre.

Third, `F' := 𝔪ⁿ G` is the prepared extension: the ideal-power multiple of a coherent module is
coherent, it still injects into `j_*F`, and over the punctured spectrum the inclusion
`𝔪ⁿ G ⟶ G` is an isomorphism because the punctured spectrum is exactly the complement of the
support of `𝔪`. The compatibility over the punctured closed fibre is the element-level mates
correspondence `Stacks.CategoryTheory.homEquiv_mate` for the square above, which identifies the
two transposes with each other up to the base-change comparison.

The maximal ideal is presented as the kernel ideal sheaf of `Spec (A/𝔪) ⟶ Spec A`, whose support
is the closed point, so that the punctured spectrum is literally the complement of that support
and the machinery of [Stacks, Tag 01YB] applies to it.

The conclusion is stated as `Nonempty (PreparedExtension A f T)` rather than as a construction of
a prepared extension, because both of the extension theorems it rests on — [Stacks, Tag 01PF] and
the first display of [Stacks, Tag 01YB] — are existence statements, from which no datum can be
extracted without a choice principle.

Neither the membership `f ∈ 𝔪` nor the regularity of `f` is used: the construction extends the
punctured-spectrum member of the triple and multiplies it by a power of the maximal ideal, and
the injectivity of `f` on the result is inherited from the triple's own torsion-freeness. The
two hypotheses are nevertheless carried, being the standing hypotheses of the source's section
and of every consumer of a prepared extension.

## References

* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open Stacks.AlgebraicGeometry.IdealPower Stacks.AlgebraicGeometry.IdealPowerColimit
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### The base-change comparison and the mates correspondence -/

/-- The conjugate, under the pullback--pushforward adjunctions, of the comparison of the inverse
images along two equal morphisms is the comparison of their direct images. -/
public theorem conjugateEquiv_pullbackCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst h
  have h0 : (Scheme.Modules.pullbackCongr (rfl : f = f)).hom = 𝟙 _ := rfl
  rw [h0, conjugateEquiv_id]
  ext V x
  simp

/-- **The 2-cell of a commutative square of schemes, read on inverse images.** The 2-cell of
direct images around a commutative square `g' ≫ f = f' ≫ g` — the one whose mate is the
base-change morphism — has as its conjugate the corresponding composite of comparisons of
inverse images. -/
public theorem conjugateEquiv_symm_pushforwardSquare {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) :
    (conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g'))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f'))).symm
      ((Scheme.Modules.pushforwardComp g' f).hom ≫
        (Scheme.Modules.pushforwardCongr w).hom ≫
        (Scheme.Modules.pushforwardComp f' g).inv) =
      (Scheme.Modules.pullbackComp f' g).hom ≫
        (Scheme.Modules.pullbackCongr w.symm).hom ≫
        (Scheme.Modules.pullbackComp g' f).inv := by
  apply (conjugateEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ← conjugateEquiv_comp, ← conjugateEquiv_comp,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr w,
    Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom]
  simp only [Category.assoc]

/-- **The base-change morphism as a transposition comparison.** For a commutative square
`g' ≫ f = f' ≫ g` of schemes, a module `G` on `S` and a morphism `q : f^*G ⟶ F`, transposing
the inverse image of `q` under the adjunction for `f'` and transposing `q` under the adjunction
for `f` and then taking the inverse image along `g` differ exactly by the base-change morphism
at `F`.

This is the element-level mates correspondence `Stacks.CategoryTheory.homEquiv_mate`, the
base-change morphism being by definition the mate of the 2-cell of direct images around the
square. -/
@[sga "4 Vbis 3.2.2" "special case"]
public theorem homEquiv_baseChangeNatTrans {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) {F : X.Modules}
    (G : S.Modules) (q : (Scheme.Modules.pullback f).obj G ⟶ F) :
    (Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _
      ((Scheme.Modules.pullbackComp f' g).hom.app G ≫
        (Scheme.Modules.pullbackCongr w.symm).hom.app G ≫
        (Scheme.Modules.pullbackComp g' f).inv.app G ≫
        (Scheme.Modules.pullback g').map q) =
      (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ q) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app F := by
  have h := Stacks.CategoryTheory.homEquiv_mate
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction f')
    ((Scheme.Modules.pushforwardComp g' f).hom ≫
      (Scheme.Modules.pushforwardCongr w).hom ≫
      (Scheme.Modules.pushforwardComp f' g).inv) q
  rw [conjugateEquiv_symm_pushforwardSquare w] at h
  simpa only [NatTrans.comp_app, Category.assoc,
    Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans] using h

/-! ### Ingredients of the construction -/

/-- **The ideal-power multiple of a coherent module is coherent.** It is a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme. -/
public theorem isCoherent_idealPowerMultiple {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) (G : X.Modules) [G.IsCoherent] [G.IsQuasicoherent] :
    (idealPowerMultiple I n G).toSheafOfModules.IsCoherent :=
  Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule G
    (idealPowerMultiple I n G)
    (Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple I n G)

/-- **The punctured spectrum is the complement of the support of the maximal ideal sheaf.** The
kernel ideal sheaf of `Spec (A/𝔪) ⟶ Spec A` has as its support the closure of the image of that
morphism, and that image is the closed point. -/
public theorem puncturedSpectrum_eq_support_compl (A : Type u) [CommRing A] [IsLocalRing A] :
    Stacks.Divisors.puncturedSpectrum A =
      (Scheme.Hom.ker
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).support.compl := by
  let X := Spec (CommRingCat.of A)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hrange : Set.range r = ({IsLocalRing.closedPoint A} : Set X) := by
    show Set.range (PrimeSpectrum.comap (IsLocalRing.residue A)) = _
    rw [range_comap_of_surjective _ _ IsLocalRing.residue_surjective, IsLocalRing.ker_residue]
    ext x
    rw [PrimeSpectrum.mem_zeroLocus]
    show IsLocalRing.maximalIdeal A ≤ x.asIdeal ↔ x = IsLocalRing.closedPoint A
    refine ⟨fun h ↦ le_antisymm le_top h, ?_⟩
    rintro rfl
    exact le_rfl
  have hclosed : IsClosed ({IsLocalRing.closedPoint A} : Set X) := by
    rw [← hrange]
    show IsClosed (Set.range (PrimeSpectrum.comap (IsLocalRing.residue A)))
    exact PrimeSpectrum.isClosed_range_comap_of_surjective _ _ IsLocalRing.residue_surjective
  have hsupp : ((Scheme.Hom.ker r).support : Set X) =
      ({IsLocalRing.closedPoint A} : Set X) := by
    rw [Scheme.Hom.support_ker, hrange, hclosed.closure_eq]
  ext x
  show x ∈ ({IsLocalRing.closedPoint A} : Set X)ᶜ ↔
    x ∉ ((Scheme.Hom.ker r).support : Set X)
  simp [hsupp]

/-- **A coherent module on an open extends to a coherent subobject of its direct image.** For a
coherent module `F` on an open `U` of a Noetherian scheme `X`, the direct image `j_*F` along the
inclusion has a coherent subobject whose restriction to `U` is `F`.

The isomorphism `(j_*F)|_U ≅ F` given by the counit of the restriction adjunction exhibits `F`
as a quasi-coherent subobject of `(j_*F)|_U` of finite type, so the extension theorem
[Stacks, Tag 01PF] applies; the resulting subobject is coherent by [Stacks, Tag 01XZ]. Retaining
the monomorphism into `j_*F` is what the injectivity statement downstream consumes. -/
@[sga "6 0 2.5" "more general"]
public theorem exists_coherent_subobject_pushforward {X : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens) (F : U.toScheme.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (_ : G.IsCoherent)
      (g : G ⟶ (Scheme.Modules.pushforward U.ι).obj F) (_ : Mono g),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj G ≅ F) := by
  classical
  have htfae := Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae U.toScheme F
  obtain ⟨hFqc, hFft⟩ := (htfae.out 1 2).mp ‹F.IsCoherent›
  have hFfp : F.IsFinitePresentation := (htfae.out 1 3).mp ‹F.IsCoherent›
  have hUc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  have hqc : QuasiCompact U.ι := quasiCompact_opens_ι hUc
  have hPqc : ((Scheme.Modules.pushforward U.ι).obj F).IsQuasicoherent := inferInstance
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward U.ι).obj F) ≅ F :=
    asIso ((Scheme.Modules.restrictAdjunction U.ι).counit.app F)
  let S : Subobject ((Scheme.Modules.restrictFunctor U.ι).obj
    ((Scheme.Modules.pushforward U.ι).obj F)) := Subobject.mk e.inv
  let eS : (S : U.toScheme.Modules) ≅ F := Subobject.underlyingIso e.inv
  have hSqc : (S : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso eS.symm hFqc
  have hSfp : (S : U.toScheme.Modules).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso eS.symm hFfp
  have hSft : (S : U.toScheme.Modules).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso (M := F) (N := (S : U.toScheme.Modules)) eS.symm
  obtain ⟨K, hKqc, hKft, eK, _⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension
      ((Scheme.Modules.pushforward U.ι).obj F) U hUc S
  exact ⟨(K : X.Modules),
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X (K : X.Modules)).out 2 1).mp
      (And.intro hKqc hKft), K.arrow, inferInstance, ⟨eK ≪≫ eS⟩⟩

/-! ### The prepared extension -/

/-- **Stacks Project, Tag 0F23.** Every coherent triple admits a prepared extension: a coherent
module on `Spec A` on which `f` acts regularly, isomorphic to the triple's punctured-spectrum
member over the punctured spectrum, and mapping compatibly to its closed-fibre member.

The module is `𝔪ⁿ G` for a coherent extension `G ⟶ j_*F` of the punctured-spectrum member of the
triple and a suitable power `n`; the three steps are described in the implementation notes of
this file. -/
@[stacks 0F23]
public theorem nonempty_preparedExtension (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsRegular f) (T : CoherentTriple A f) : Nonempty (PreparedExtension A f T) := by
  classical
  let U := Stacks.Divisors.puncturedSpectrum A
  let j := U.ι
  let i := closedImmersion A f
  let j₀ := (puncturedClosedFibre A f).ι
  let k := morphismRestrict i U
  have hTF : T.F.IsCoherent := T.coherent_F
  have hTF₀ : T.F₀.IsCoherent := T.coherent_F₀
  obtain ⟨hF₀qc, -⟩ :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (closedFibre A f) T.F₀).out
      1 2).mp T.coherent_F₀
  obtain ⟨G, hGc, g, hgm, ⟨eG⟩⟩ := exists_coherent_subobject_pushforward U T.F
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let I := Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  have hU : U = I.support.compl := puncturedSpectrum_eq_support_compl A
  have hpb : IsPullback j₀ k i j := (isPullback_morphismRestrict i U).flip
  have hiaff : IsAffineHom i := inferInstance
  have hBiso : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      hpb.w).app T.F₀) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      hpb T.F₀
  let B := asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hpb.w).app T.F₀)
  let P := (Scheme.Modules.pushforward i).obj T.F₀
  let L := Scheme.Modules.pullback j
  let R := Scheme.Modules.restrictFunctor j
  let eR : R ≅ L := Scheme.Modules.restrictFunctorIsoPullback j
  let e : L.obj G ≅ T.F := eR.symm.app G ≪≫ eG
  let adj := Scheme.Modules.pullbackPushforwardAdjunction k
  let β := (Scheme.Modules.pullback k).map e.hom ≫ T.alpha.hom
  let φ : R.obj G ⟶ R.obj P := eR.hom.app G ≫ (adj.homEquiv _ _ β) ≫ B.inv ≫ eR.inv.app P
  have hPqc : P.IsQuasicoherent := inferInstance
  obtain ⟨n, ψ₀, hψ₀⟩ := exists_hom_idealPowerMultiple_restrict_eq I U hU G P φ
  let N := idealPowerMultiple I n G
  let H : (baseScheme A).Modules := N.toSheafOfModules
  let p : H ⟶ G := N.ι
  let ψ : H ⟶ P := ψ₀
  have hHU : Disjoint (U : Set (baseScheme A)) (I.support : Set (baseScheme A)) := by
    rw [hU]
    exact disjoint_compl_left
  have hpIso : IsIso (R.map p) := isIso_restrictFunctor_map_idealPowerMultiple_ι I n G hHU
  have hpIsoL : IsIso (L.map p) := (NatIso.isIso_map_iff eR p).mp hpIso
  let α' : L.obj H ≅ T.F := asIso (L.map p) ≪≫ e
  let α₀' := ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv H T.F₀).symm ψ
  have hpm : Mono p := AlgebraicGeometry.Scheme.Modules.mono_submodule_ι N
  have hψ' : R.map p ≫ φ = R.map ψ := hψ₀
  refine ⟨⟨H, isCoherent_idealPowerMultiple I n G,
    regular_of_mono_pushforward A f T.F T.torsionFree H (p ≫ g), α', α₀', ?_⟩⟩
  have hext : L.map p ≫ adj.homEquiv _ _ β = L.map ψ ≫ B.hom := by
    have hh := congrArg (fun z => eR.inv.app H ≫ z ≫ eR.hom.app P ≫ B.hom) hψ'
    simp only [φ, Category.assoc, Iso.inv_hom_id_app_assoc] at hh
    rw [← eR.inv.naturality_assoc p, ← eR.inv.naturality_assoc ψ] at hh
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      Category.comp_id] using hh
  have hext' : L.map ψ ≫ B.hom =
      adj.homEquiv _ _ ((Scheme.Modules.pullback k).map α'.hom ≫ T.alpha.hom) := by
    rw [← hext]
    simp only [α', Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc]
    exact (adj.homEquiv_naturality_left _ _).symm
  have hbc := homEquiv_baseChangeNatTrans hpb.w H α₀'
  have hq : (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv H T.F₀ α₀' = ψ :=
    Equiv.apply_symm_apply _ ψ
  rw [hq] at hbc
  have hcompat := (adj.homEquiv _ _).injective (hbc.trans hext')
  show (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).hom.app H ≫
      (Scheme.Modules.pullbackComp k j).inv.app H ≫
      (Scheme.Modules.pullback k).map α'.hom ≫ T.alpha.hom =
    (Scheme.Modules.pullbackComp j₀ i).inv.app H ≫
      (Scheme.Modules.pullback j₀).map α₀'
  rw [← hcompat]
  simp only [Iso.inv_hom_id_app_assoc]
  simp [Scheme.Modules.pullbackCongr]

end Stacks.Algebraization

end
