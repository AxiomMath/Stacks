module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftedEtalePresentationCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.RingTheory.Etale.CountableFaithfullyFlatModel

/-!
# A thickening of an affine space carrying a lifted étale presentation is affine

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S` with `G` affine, `G ≅ h_{T_G}`,
and let `φ : h_V ⟶ X` be a surjective étale chart with `V` affine, so that `U = G ×_X V` is an
affine scheme étale and surjective over `T_G`. Suppose the étale algebra `Γ(U)` over `Γ(T_G)` is
the base change of an étale, faithfully flat algebra `E` over a countable ring `P`, along
`α : P → Γ(T_G)`, and that `α` lifts to an *invariant* ring homomorphism `β : P → Γ(V)` — one
whose two pullbacks along any pair of morphisms into `V` that agree over `X` coincide. Then `X`
is affine.

This is the step of Stacks 07SQ (an affine limit of quasi-compact and quasi-separated algebraic
spaces has an affine stage) that applies to a single thickening, with the topological invariance
of the étale site, Stacks 05ZH, doing the work that Stacks 07SI and 084S do in the source.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_liftedEtalePresentation`: the statement above.
* `AlgebraicGeometry.Space.isAffineSpace_of_forall_exists_lift`: the same conclusion when every
  global function of `T_G` lifts to an invariant function on `V`; the étale, faithfully flat model
  is then supplied by `Algebra.exists_countable_etale_faithfullyFlat_model`.

## Implementation notes

The invariant lift `β` descends along the coequalizer `V ×_X V ⇉ V ⟶ X` to a morphism
`ψ : X ⟶ Spec P`, read on the site of `S` as a morphism to the restriction of the representable
presheaf of `Spec P` over `Spec ℤ`. The base change `X ×_{Spec P} Spec E` is étale over `X` and
has the same base change to `G` as `V` does, namely `U = T_G ×_{Spec P} Spec E`; full
faithfulness of Stacks 05ZH (`AlgebraicGeometry.Space.exists_iso_of_isPullback_of_isThickening`)
identifies it with `V`. So `V ⟶ X` is a base change of the surjective étale morphism
`Spec E ⟶ Spec P` of affine schemes.

Affineness is then read off over `Spec ℤ`, not over `S`: over a non-separated `S` the scheme `V`
need not be affine over `S × Spec E`. The projection formula moves the cartesian square to the
lower-shriek extension of `X` along `S ⟶ Spec ℤ`, where effective descent of affine morphisms
along `Spec E ⟶ Spec P` applies, and the representing object is carried back to `S`
(`AlgebraicGeometry.Space.isAffineSpace_of_isPullback_relocalize`). No solution of the étale
equations needs to be lifted, and nothing about the order of the thickening is used.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebra of finite type over a countable ring is countable. -/
theorem _root_.Algebra.FiniteType.countable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [Countable R] : Countable A := by
  obtain ⟨_, _, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  exact hf.countable

/-- A pushout `Γ(Y) ⊗_P E = Γ(X)` of rings presents the affine scheme `X` as the fibre product
`Y ×_{Spec P} Spec E`. -/
theorem isPullback_toSpecOfRingHom_of_isPushout {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) {P E : Type u} [CommRing P] [CommRing E] [Algebra P E] (α : P →+* Γ(Y, ⊤))
    (ε : E →+* Γ(X, ⊤))
    (hpush : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap P E)) f.appTop
      (CommRingCat.ofHom ε)) :
    IsPullback (toSpecOfRingHom ε) f (Spec.map (CommRingCat.ofHom (algebraMap P E)))
      (toSpecOfRingHom α) := by
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip.of_iso X.isoSpec.symm (Iso.refl _)
    Y.isoSpec.symm (Iso.refl _) ?_ (Scheme.isoSpec_inv_naturality _) (by simp) ?_ <;>
  simp

/-- An étale surjective morphism `f : X ⟶ Y` of affine schemes makes `Γ(X)` an étale, faithfully
flat `Γ(Y)`-algebra. -/
theorem etale_faithfullyFlat_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [Etale f] [Surjective f] :
    letI := f.appTop.hom.toAlgebra
    Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) ∧ Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := by
  let := f.appTop.hom.toAlgebra
  have hE : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := by
    rw [← RingHom.etale_algebraMap]
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have _ : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  refine ⟨hE, Module.FaithfullyFlat.of_comap_surjective ?_⟩
  have _ : Surjective (Spec.map f.appTop) := by
    rw [← Iso.inv_hom_id_assoc X.isoSpec (Spec.map f.appTop), Scheme.isoSpec_hom_naturality]
    infer_instance
  exact (surjective_iff (Spec.map f.appTop)).mp inferInstance

/-- If `p : C →+* R` followed by `R →+* Γ(X)` is the restriction of functions along a surjective
morphism `f : X ⟶ Y` of affine schemes, for a subring `C` of `Γ(Y)`, then `p` has nil kernel. -/
theorem ker_le_nilradical_of_comp_eq_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Surjective f] {C : Subring Γ(Y, ⊤)} {R : Type*} [CommRing R] (p : C →+* R)
    (q : R →+* Γ(X, ⊤)) (h : ∀ b, q (p b) = f.appTop.hom b) : RingHom.ker p ≤ nilradical C := by
  intro b hb
  obtain ⟨n, hn⟩ := ker_appTop_le_nilradical_of_surjective f
    (RingHom.mem_ker.mpr (show f.appTop.hom b = 0 by rw [← h, RingHom.mem_ker.mp hb, map_zero]))
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

section

variable {B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` in presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_AffineOfLiftedEtalePresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_AffineOfLiftedEtalePresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change to an affine chart `V` of the inclusion of a thickening is affine. -/
theorem isAffine_of_isPullback_isThickening {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) {V U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {φ : yoneda.obj V ⟶ X.1} (ιU : U ⟶ V)
    (q : yoneda.obj U ⟶ G.toFunctor) (sqU : IsPullback (yoneda.map ιU) q φ G.ι) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) :=
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ιU) :=
    hG.1.2.property _ _ _ sqU.flip
  isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map ιU)

/-- The base change `U ⟶ T_G` of a surjective étale chart `φ` along `G ≅ h_{T_G} ⊂ X` is a
surjective étale morphism of schemes. -/
theorem etale_and_surjective_of_isPullback {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    {TG V U : BigFppfOver B S hS} (eG : G.toFunctor ≅ yoneda.obj TG) {φ : yoneda.obj V ⟶ X.1}
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (ιU : U ⟶ V) (πU : U ⟶ TG) (sqU : IsPullback (yoneda.map ιU) (yoneda.map πU ≫ eG.inv) φ G.ι) :
    Etale ((BigFppfOver.toScheme B S hS).map πU) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map πU) := by
  have sqU' : IsPullback (yoneda.map ιU) (yoneda.map πU) φ (eG.inv ≫ G.ι) :=
    sqU.of_iso (Iso.refl _) (Iso.refl _) eG (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact ⟨hφe.property _ _ _ sqU', hφs.property _ _ _ sqU'⟩

/-- **Descent of a morphism to an object over `Spec ℤ` along a surjective étale chart.** A
morphism of schemes `v : V ⟶ Y` invariant under every pair of morphisms into `V` agreeing over
`X` descends to a morphism from `X` to the restriction of `h_Y`. -/
theorem exists_comp_eq_eltInt (X : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X.1)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {Y : IntOver B} (v : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B _ _).obj Y)
    (hv : ∀ ⦃W : BigFppfOver B S hS⦄ (r₁ r₂ : W ⟶ V), yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ →
      (BigFppfOver.toScheme B S hS).map r₁ ≫ v = (BigFppfOver.toScheme B S hS).map r₂ ≫ v) :
    ∃ ψ : X.1 ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj Y), φ ≫ ψ = eltInt v := by
  let s₁ := hφe.rep.fst' φ
  let s₂ := hφe.rep.snd φ
  have hR : IsPullback (yoneda.map s₁) (yoneda.map s₂) φ φ := hφe.rep.isPullback' φ
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS φ s₁ s₂ hR X.2 hφs hφe
  let FY : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨(relocalizeRestrict (toInt B S hS)).obj (yoneda.obj Y),
      isSheaf_relocalizeRestrict B S _ hS _ (toInt B S hS) _
        ((isSheaf_iff_isSheaf_of_type _ _).2 (BigFppfOver.isSheaf_of_type_yoneda_obj Y))⟩
  obtain ⟨ψS, hψS⟩ := Cofork.IsColimit.desc' hc (⟨eltInt v⟩ : (⟨yoneda.obj V, hUsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ FY) (by
        apply Sheaf.hom_ext
        change yoneda.map s₁ ≫ eltInt v = yoneda.map s₂ ≫ eltInt v
        rw [yoneda_map_comp_eltInt, yoneda_map_comp_eltInt, hv s₁ s₂ hR.w])
  exact ⟨ψS.hom, congrArg (·.hom) hψS⟩

/-- A morphism `ψ` to the restriction of `h_Y`, `Y` affine over `Spec ℤ`, which is `v` on `h_V`, is
`τ` on `h_T` when `U ⟶ T` is flat and surjective and `v` and `τ` agree on `U`. -/
theorem comp_eq_eltInt_of_comp_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T V U : BigFppfOver B S hS} {Y : IntOver B} [IsAffine ((BigFppfOver.toScheme B _ _).obj Y)]
    (ιU : U ⟶ V) (πU : U ⟶ T) [Flat ((BigFppfOver.toScheme B S hS).map πU)]
    [Surjective ((BigFppfOver.toScheme B S hS).map πU)] {φ : yoneda.obj V ⟶ F}
    {j : yoneda.obj T ⟶ F} (hw : yoneda.map ιU ≫ φ = yoneda.map πU ≫ j)
    {ψ : F ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj Y)}
    {v : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B _ _).obj Y}
    {τ : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B _ _).obj Y}
    (hφψ : φ ≫ ψ = eltInt v)
    (hv : (BigFppfOver.toScheme B S hS).map ιU ≫ v = (BigFppfOver.toScheme B S hS).map πU ≫ τ) :
    j ≫ ψ = eltInt τ := by
  obtain ⟨t, ht⟩ := exists_eq_eltInt (j ≫ ψ)
  rw [ht]
  congr 1
  refine eq_of_comp_eq_of_flat_of_surjective ((BigFppfOver.toScheme B S hS).map πU)
    (eltInt_injective ?_)
  rw [← yoneda_map_comp_eltInt, ← ht, ← reassoc_of% hw, hφψ, yoneda_map_comp_eltInt, hv]

/-- **Stacks 05ZH identifies the chart with a base change of an étale cover over `Spec ℤ`.** Let
`G ⊂ X` be a thickening, `φ : h_V ⟶ X` an étale chart with `V` affine and `U = G ×_X V`, and
`ψ : X ⟶ Y` a morphism to an affine object over `Spec ℤ` such that the base change of a surjective
étale morphism `e : E ⟶ Y` of affine objects along `ψ` restricts to `U` over `G`. Then `X` is an
affine algebraic space. -/
theorem isAffineSpace_of_isPullback_relocalizeRestrict (X : AlgebraicSpaces B S hS)
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) {TG V U : BigFppfOver B S hS}
    (eG : G.toFunctor ≅ yoneda.obj TG) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {φ : yoneda.obj V ⟶ X.1}
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (ιU : U ⟶ V) (πU : U ⟶ TG) (sqU : IsPullback (yoneda.map ιU) (yoneda.map πU ≫ eG.inv) φ G.ι)
    {EZ TZ : IntOver B} [IsAffine ((BigFppfOver.toScheme B _ _).obj EZ)]
    [IsAffine ((BigFppfOver.toScheme B _ _).obj TZ)] (eZ : EZ ⟶ TZ)
    (hEt : Etale ((BigFppfOver.toScheme B _ _).map eZ))
    (hSurj : Surjective ((BigFppfOver.toScheme B _ _).map eZ))
    (ψ : X.1 ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj TZ))
    (a : yoneda.obj U ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj EZ))
    (hbig : IsPullback a (yoneda.map πU ≫ eG.inv)
      ((relocalizeRestrict (toInt B S hS)).map (yoneda.map eZ)) (G.ι ≫ ψ)) :
    IsAffineSpace B S hS X.1 := by
  let g := toInt B S hS
  let jE := (relocalizeRestrict g).map (yoneda.map eZ)
  have hjE := presheaf_etale_relocalizeRestrict_map (S := S) (hS := hS) eZ hEt
  have hE'pb : IsPullback (pullback.fst jE ψ) (pullback.snd jE ψ) jE ψ :=
    IsPullback.of_hasPullback jE ψ
  have hw : IsEtale B S hS (pullback.snd jE ψ) :=
    have : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    isEtale_of_presheaf_etale B S hS (MorphismProperty.of_isPullback hE'pb hjE)
  have hY : ∀ Y : IntOver B, IsAlgebraicSpace B S hS ((relocalizeRestrict g).obj (yoneda.obj Y)) :=
    fun Y => isAlgebraicSpace_relocalizeRestrict B S _ hS _ g _ (isAlgebraicSpace_yoneda B _ _ Y)
  have hE' : IsAlgebraicSpace B S hS (pullback jE ψ) :=
    isAlgebraicSpace_pullback B S hS jE ψ (hY EZ) X.2 (hY TZ)
  have hcomm : a ≫ jE = (yoneda.map ιU ≫ φ) ≫ ψ := by
    rw [hbig.w, sqU.w]
    simp only [Category.assoc]
  let d : yoneda.obj U ⟶ pullback jE ψ := pullback.lift a (yoneda.map ιU ≫ φ) hcomm
  have hd₁ : d ≫ pullback.fst jE ψ = a := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd jE ψ = yoneda.map ιU ≫ φ := pullback.lift_snd _ _ _
  have sqE : IsPullback d (yoneda.map πU ≫ eG.inv) (pullback.snd jE ψ) G.ι := by
    refine IsPullback.of_right ?_ ?_ hE'pb
    · rwa [hd₁]
    · rw [hd₂, sqU.w]
  obtain ⟨i, hi, -⟩ := exists_iso_of_isPullback_of_isThickening hG
    (isEtale_of_presheaf_etale B S hS hφe) ιU _ sqU hE' hw d sqE
  have sqV : IsPullback (i.hom ≫ pullback.fst jE ψ) φ jE ψ :=
    hE'pb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← hi])
      (by simp) (by simp)
  have sqZ := (isPullback_relocalizeOfRestricted g sqV).flip
  let ι := (relocalizeYonedaIso g).app V
  let r := yoneda.preimage (ι.inv ≫ relocalizeOfRestricted g (i.hom ≫ pullback.fst jE ψ))
  have sqZ' : IsPullback (ι.inv ≫ (relocalizePresheafFunctor g).map φ) (yoneda.map r)
      (relocalizeOfRestricted g ψ) (yoneda.map eZ) :=
    sqZ.of_iso ι (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [r]) (by simp)
      (by simp)
  exact isAffineSpace_of_isPullback_relocalize B g X.2.isSheaf (a := TZ) (c := EZ)
    (v := (Over.map g).obj V) inferInstance inferInstance hV eZ hSurj hEt
    (relocalizeOfRestricted g ψ) _ r sqZ'

end

/-- **A thickening of an affine space carrying a lifted étale presentation is affine.** Let
`G ⊂ X` be a thickening with `G ≅ h_{T_G}` affine, `φ : h_V ⟶ X` a surjective étale chart with
`V` affine, and `U = G ×_X V` (the square `sqU`). If `Γ(U) = Γ(T_G) ⊗_P E` for an étale,
faithfully flat algebra `E` over a countable ring `P` (the pushout `hpush`), and the map
`α : P → Γ(T_G)` lifts to a ring homomorphism `β : P → Γ(V)` which restricts to `α` on `U`
(`hβU`) and is invariant under every pair of morphisms into `V` agreeing over `X` (`hβ`), then
`X` is an affine algebraic space. -/
theorem isAffineSpace_of_liftedEtalePresentation
    (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) (hG : IsThickening B S hS X G)
    {TG : BigFppfOver B S hS} (hTG : IsAffine ((BigFppfOver.toScheme B S hS).obj TG))
    (eG : G.toFunctor ≅ yoneda.obj TG)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ X.1)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {U : BigFppfOver B S hS} (ιU : U ⟶ V) (πU : U ⟶ TG)
    (sqU : IsPullback (yoneda.map ιU) (yoneda.map πU ≫ eG.inv) φ G.ι)
    (P E : Type u) [CommRing P] [CommRing E] [Algebra P E] [Algebra.Etale P E]
    [Module.FaithfullyFlat P E] [Countable P]
    (α : P →+* Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤))
    (ε : E →+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (hpush : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap P E))
      ((BigFppfOver.toScheme B S hS).map πU).appTop (CommRingCat.ofHom ε))
    (β : P →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hβU : ((BigFppfOver.toScheme B S hS).map ιU).appTop.hom.comp β =
      ((BigFppfOver.toScheme B S hS).map πU).appTop.hom.comp α)
    (hβ : ∀ ⦃W : BigFppfOver B S hS⦄ (r₁ r₂ : W ⟶ V), yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ →
      ((BigFppfOver.toScheme B S hS).map r₁).appTop.hom.comp β =
        ((BigFppfOver.toScheme B S hS).map r₂).appTop.hom.comp β) :
    IsAffineSpace B S hS X.1 := by
  have _ := isAffine_of_isPullback_isThickening hG ιU _ sqU
  have _ : Countable E := Algebra.FiniteType.countable P E
  let TZ := specInt B P
  let EZ := specInt B E
  let eZ : EZ ⟶ TZ := intHom B (Spec.map (CommRingCat.ofHom (algebraMap P E)))
  have _ : IsAffine ((BigFppfOver.toScheme B _ _).obj TZ) :=
    inferInstanceAs (IsAffine (Spec (.of P)))
  have _ : IsAffine ((BigFppfOver.toScheme B _ _).obj EZ) :=
    inferInstanceAs (IsAffine (Spec (.of E)))
  have heZ : (BigFppfOver.toScheme B _ _).map eZ = Spec.map (CommRingCat.ofHom (algebraMap P E)) :=
    toScheme_map_intHom B _
  have hEt : Etale ((BigFppfOver.toScheme B _ _).map eZ) := by
    rw [heZ]
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap P E)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hSurj : Surjective ((BigFppfOver.toScheme B _ _).map eZ) := by
    rw [heZ]
    change Surjective (Spec.map (CommRingCat.ofHom (algebraMap P E)))
    rw [surjective_iff]
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  let τ : (BigFppfOver.toScheme B S hS).obj TG ⟶ (BigFppfOver.toScheme B _ _).obj TZ :=
    toSpecOfRingHom α
  let aE : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B _ _).obj EZ :=
    toSpecOfRingHom ε
  let vT : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B _ _).obj TZ :=
    toSpecOfRingHom β
  have sqS : IsPullback aE ((BigFppfOver.toScheme B S hS).map πU)
      ((BigFppfOver.toScheme B _ _).map eZ) τ := by
    rw [heZ]
    exact isPullback_toSpecOfRingHom_of_isPushout _ α ε hpush
  obtain ⟨_, _⟩ := etale_and_surjective_of_isPullback eG hφs hφe ιU πU sqU
  obtain ⟨ψ, hφψ⟩ := exists_comp_eq_eltInt X φ hφs hφe vT fun _ r₁ r₂ h => by
    change _ ≫ toSpecOfRingHom β = _ ≫ toSpecOfRingHom β
    rw [comp_toSpecOfRingHom, comp_toSpecOfRingHom, hβ r₁ r₂ h]
  have hGψ : eG.inv ≫ G.ι ≫ ψ = eltInt τ :=
    (Category.assoc _ _ _).symm.trans <| comp_eq_eltInt_of_comp_eq ιU πU
      (sqU.w.trans (Category.assoc _ _ _)) hφψ (by
        change _ ≫ toSpecOfRingHom β = _ ≫ toSpecOfRingHom α
        rw [comp_toSpecOfRingHom, comp_toSpecOfRingHom, hβU])
  exact isAffineSpace_of_isPullback_relocalizeRestrict X hG eG hV hφe ιU πU sqU eZ hEt hSurj ψ
    (eltInt aE)
    ((isPullback_eltInt πU eZ aE τ sqS).of_iso (Iso.refl _) (Iso.refl _) eG.symm (Iso.refl _)
      (by simp) (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hGψ]))

/-- **A thickening of an affine space whose functions lift invariantly to a chart is affine.**
Let `G ⊂ X` be a thickening with `G ≅ h_{T_G}` affine, `φ : h_V ⟶ X` a surjective étale chart with
`V` affine, and `U = G ×_X V` (the square `sqU`). If every global function `a` of `T_G` lifts to a
function `b` on `V` which restricts to `a` on `U` and is invariant under every pair of morphisms
into `V` agreeing over `X` (`hlift`), then `X` is an affine algebraic space.

The invariant functions on `V` whose restriction to `U` comes from `T_G` form a subring `C` of
`Γ(V)` mapping onto `Γ(T_G)` with nil kernel; the étale, faithfully flat `Γ(T_G)`-algebra `Γ(U)`
has a countable étale, faithfully flat model over a finitely generated subring of `C`
(`Algebra.exists_countable_etale_faithfullyFlat_model`), and
`AlgebraicGeometry.Space.isAffineSpace_of_liftedEtalePresentation` applies to it. -/
theorem isAffineSpace_of_forall_exists_lift
    (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) (hG : IsThickening B S hS X G)
    {TG : BigFppfOver B S hS} (hTG : IsAffine ((BigFppfOver.toScheme B S hS).obj TG))
    (eG : G.toFunctor ≅ yoneda.obj TG)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ X.1)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hφe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {U : BigFppfOver B S hS} (ιU : U ⟶ V) (πU : U ⟶ TG)
    (sqU : IsPullback (yoneda.map ιU) (yoneda.map πU ≫ eG.inv) φ G.ι)
    (hlift : ∀ a : Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤),
      ∃ b : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
        ((BigFppfOver.toScheme B S hS).map ιU).appTop b =
          ((BigFppfOver.toScheme B S hS).map πU).appTop a ∧
        ∀ ⦃W : BigFppfOver B S hS⦄ (r₁ r₂ : W ⟶ V), yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ →
          ((BigFppfOver.toScheme B S hS).map r₁).appTop b =
            ((BigFppfOver.toScheme B S hS).map r₂).appTop b) :
    IsAffineSpace B S hS X.1 := by
  have _ := isAffine_of_isPullback_isThickening hG ιU _ sqU
  obtain ⟨_, _⟩ := etale_and_surjective_of_isPullback eG hφs hφe ιU πU sqU
  have _ := surjective_of_isPullback_of_isThickening hG ιU _ sqU
  let rU := ((BigFppfOver.toScheme B S hS).map ιU).appTop.hom
  let pU := ((BigFppfOver.toScheme B S hS).map πU).appTop.hom
  have hpU : Function.Injective pU :=
    Scheme.Hom.appTop_injective_of_flat_of_surjective ((BigFppfOver.toScheme B S hS).map πU)
  let Inv : Subring Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ⨅ (W : BigFppfOver B S hS) (r₁ : W ⟶ V) (r₂ : W ⟶ V)
      (_ : yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ),
      RingHom.eqLocus ((BigFppfOver.toScheme B S hS).map r₁).appTop.hom
        ((BigFppfOver.toScheme B S hS).map r₂).appTop.hom
  let C := Inv ⊓ pU.range.comap rU
  have hmemC : ∀ b, b ∈ C ↔ (∀ ⦃W : BigFppfOver B S hS⦄ (r₁ r₂ : W ⟶ V),
      yoneda.map r₁ ≫ φ = yoneda.map r₂ ≫ φ →
        ((BigFppfOver.toScheme B S hS).map r₁).appTop b =
          ((BigFppfOver.toScheme B S hS).map r₂).appTop b) ∧ rU b ∈ pU.range := fun b => by
    simp only [C, Inv, Subring.mem_inf, Subring.mem_iInf, RingHom.mem_eqLocus, Subring.mem_comap]
  let e : Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤) ≃+* pU.range :=
    RingEquiv.ofBijective pU.rangeRestrict
      ⟨fun a b h => hpU (congrArg Subtype.val h), pU.rangeRestrict_surjective⟩
  let c : C →+* pU.range :=
    (rU.comp C.subtype).codRestrict pU.range (fun b => ((hmemC b.1).1 b.2).2)
  let α : C →+* Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤) := e.symm.toRingHom.comp c
  have hα : ∀ b : C, pU (α b) = rU b := fun b => congrArg Subtype.val (e.apply_symm_apply (c b))
  let : Algebra C Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤) := α.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := pU.toAlgebra
  have hαsurj : Function.Surjective (algebraMap C Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)) := by
    intro a
    obtain ⟨b, hb₁, hb₂⟩ := hlift a
    have hbC : b ∈ C := (hmemC b).2 ⟨hb₂, ⟨a, hb₁.symm⟩⟩
    exact ⟨⟨b, hbC⟩, hpU ((hα ⟨b, hbC⟩).trans hb₁)⟩
  obtain ⟨_, _⟩ : Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ∧
    Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj TG, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    etale_faithfullyFlat_appTop ((BigFppfOver.toScheme B S hS).map πU)
  obtain ⟨P, E, _, _, hPfg, _, _, ε, hpush⟩ :=
    Algebra.exists_countable_etale_faithfullyFlat_model
      (B := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) hαsurj
      (ker_le_nilradical_of_comp_eq_appTop ((BigFppfOver.toScheme B S hS).map ιU) α pU hα)
  have := Subalgebra.countable_of_fg hPfg
  exact isAffineSpace_of_liftedEtalePresentation B S hS X G hG hTG eG hV φ hφs hφe ιU πU sqU
    P E (α.comp P.val.toRingHom) ε hpush (C.subtype.comp P.val.toRingHom)
    (RingHom.ext fun _ => (hα _).symm)
    (fun W r₁ r₂ h => RingHom.ext fun x => ((hmemC _).1 (P.val x).2).1 r₁ r₂ h)

end AlgebraicGeometry.Space

end
