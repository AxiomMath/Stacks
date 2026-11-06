module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.BeauvilleLaszlo
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Covering
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Surjectivity

/-!
# Faithfulness of the Beauville--Laszlo glueing functor for algebraic spaces

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair, so that `g` induces isomorphisms
`R/fⁿR ≅ R'/fⁿR'` for all `n > 0` and the sequence `0 → R → R' ⊕ R_f → R'_f → 0` is short
exact. Write `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and `U' = Spec R'_f`. The glueing
functor of Stacks 0F9N sends an algebraic space `Y/X` to the cartesian triple formed by its
base changes to `U`, `U'` and `X'`. This module proves that this functor is *faithful* on the
full subcategory of algebraic spaces over `X` that are glueable for `(g, f)` in the sense of
Stacks 0F9P.

## Main results

* `BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable`:
  **Stacks 0F9S**, two morphisms of glueable algebraic spaces over `Spec R` that have equal
  images under the glueing functor are equal.

## Implementation notes

Faithfulness on a full subcategory is injectivity of the map on each hom-set between its
objects, which is how the statement is phrased. The four arrows of the glueing square are the
canonical morphisms of affine schemes induced by `g`, by the localization maps, and by the
localization of `g` away from `f`.

The proof follows the source. Two morphisms `φ, ψ : Y ⟶ Z` agreeing after both base changes are
compared on an étale covering of `Y` by affine schemes (`Y` is an algebraic space, so such a
covering exists and the sheaf condition reduces equality of `φ` and `ψ` to equality on it).
Fix such an affine chart `T = Spec A` with `A` glueable. The equalizer `E ⟶ T` of the two
composites is representable because the diagonal of `Z` is, and it is a monomorphism which is
locally quasi-finite and locally of finite type for the same reason. Equality of the two base
changes produces sections of `E ⟶ T` over `Spec (A ⊗[R] R')` and `Spec (A ⊗[R] R_f)`, which
jointly cover `Spec A` because `Spec R' ⊔ Spec R_f → Spec R` is surjective for a glueing pair
(Stacks 0BNM); hence `E` is quasi-compact, and Zariski's main theorem (Stacks 05K0) makes it
quasi-affine. Glueability of `A` glues the two sections into a ring map `Γ(E, ⊤) → A`, whose
`Spec` is a retraction of `E ⟶ T` landing in the quasi-affine open; since `E ⟶ T` is a
monomorphism it is therefore an isomorphism, which is exactly the required equality on `T`.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

private theorem primeSpectrum_cover_of_glueingPair
    {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    Function.Surjective
      (Sum.elim (PrimeSpectrum.comap g)
        (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))) := by
  apply (BeauvilleLaszlo.primeSpectrum_cover_of_quotientMap_bijective f).1 g
  let e := (Ideal.quotEquivOfEq (pow_one (Ideal.span ({f} : Set R))).symm).trans
    ((RingEquiv.ofBijective _ (hglue.1 1 Nat.one_pos)).trans
      (Ideal.quotEquivOfEq (by simp [Ideal.map_span] :
        Ideal.span ({g f} : Set R') ^ 1 = Ideal.map g (Ideal.span {f}))))
  have he : (e : R ⧸ Ideal.span {f} →+* R' ⧸ Ideal.map g (Ideal.span {f})) =
      Ideal.quotientMap _ g Ideal.le_comap_map := by
    ext r
    simp [e, BeauvilleLaszlo.quotientPowMap]
  rw [← he]
  exact e.bijective

private theorem eq_of_baseChanges_eq_of_isGlueable
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Algebra R S] [Module R M] (f : R)
    (hM : BeauvilleLaszlo.IsGlueableFor (S := S) M f)
    {x y : M}
    (hS : x ⊗ₜ[R] (1 : S) = y ⊗ₜ[R] (1 : S))
    (hf : x ⊗ₜ[R] (1 : Localization.Away f) =
      y ⊗ₜ[R] (1 : Localization.Away f)) : x = y := by
  apply hM.1
  ext
  · simpa [BeauvilleLaszlo.toTensorBaseChanges_apply] using hS
  · simpa [BeauvilleLaszlo.toTensorBaseChanges_apply] using hf

private theorem ringHom_lift_of_baseChanges_compatible
    {R S A C : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing C]
    [Algebra R S] [Algebra R A] (f : R)
    (hA : BeauvilleLaszlo.IsGlueableFor (S := S) A f)
    (φ : C →+* TensorProduct R A S)
    (ψ : C →+* TensorProduct R A (Localization.Away f))
    (hcomp : ∀ c,
      BeauvilleLaszlo.baseChangeToAway (M := A) f (φ c) =
        BeauvilleLaszlo.localizedBaseChangeToAway (M := A) f (ψ c)) :
    ∃ θ : C →+* A,
      (∀ c, algebraMap A (TensorProduct R A S) (θ c) = φ c) ∧
      (∀ c, algebraMap A (TensorProduct R A (Localization.Away f)) (θ c) = ψ c) := by
  have key : ∀ ι : A →+* TensorProduct R A S × TensorProduct R A (Localization.Away f),
      Function.Injective ι → (∀ c, ∃ a, ι a = φ.prod ψ c) →
        ∃ θ : C →+* A, ∀ c, ι (θ c) = φ.prod ψ c := by
    intro ι hι h
    choose θ hθ using h
    exact ⟨{ toFun := θ
             map_one' := hι (by simp [hθ])
             map_mul' := fun a b => hι (by simp [hθ])
             map_zero' := hι (by simp [hθ])
             map_add' := fun a b => hι (by simp [hθ]) }, hθ⟩
  obtain ⟨θ, hθ⟩ := key ((algebraMap A (TensorProduct R A S)).prod
      (algebraMap A (TensorProduct R A (Localization.Away f)))) hA.1
    fun c => (hA.2.1 (φ c, ψ c)).mp (by
      rw [BeauvilleLaszlo.tensorAwayDifference_apply, hcomp c]
      simp)
  exact ⟨θ, fun c => congrArg Prod.fst (hθ c), fun c => congrArg Prod.snd (hθ c)⟩

/-- Equal images under `F` give equal images under any functor isomorphic to `F ⋙ H`. -/
private theorem map_eq_of_comp_iso_map_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (H : D ⥤ E) (G : C ⥤ E) (e : F ⋙ H ≅ G) {X Y : C} (f g : X ⟶ Y)
    (h : F.map f = F.map g) : G.map f = G.map g := by
  have hh : e.hom.app X ≫ G.map f = e.hom.app X ≫ G.map g := by
    rw [← e.hom.naturality f, ← e.hom.naturality g, Functor.comp_map, Functor.comp_map, h]
  exact (cancel_epi (e.hom.app X)).1 hh

private theorem representable_equalizer_of_algebraicSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p q : yoneda.obj T ⟶ F) :
    ∃ (E : AlgebraicGeometry.BigFppfOver B S hS) (i : E ⟶ T)
      (e : yoneda.obj E ⟶ F),
      IsPullback e (yoneda.map i) (diag F) (prod.lift p q) := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hd : yoneda.relativelyRepresentable (diag F) := hF.diagonal_representable
  exact ⟨_, hd.snd _, hd.fst _, hd.isPullback (prod.lift p q)⟩

private theorem equalizer_lift_of_equal_after_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T E T' : AlgebraicGeometry.BigFppfOver B S hS}
    (i : E ⟶ T) (p q : yoneda.obj T ⟶ F) (e : yoneda.obj E ⟶ F)
    (hpb : IsPullback e (yoneda.map i) (diag F) (prod.lift p q))
    (a : T' ⟶ T) (ha : yoneda.map a ≫ p = yoneda.map a ≫ q) :
    ∃ l : T' ⟶ E, l ≫ i = a ∧ yoneda.map l ≫ e = yoneda.map a ≫ p := by
  let l' := hpb.lift (yoneda.map a ≫ p) (yoneda.map a) (by
    apply prod.hom_ext <;> simp [ha])
  let l := Yoneda.fullyFaithful.preimage l'
  have hl : yoneda.map l = l' :=
    Yoneda.fullyFaithful.map_preimage l'
  refine ⟨l, ?_, ?_⟩
  · apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, hl]
    exact hpb.lift_snd _ _ _
  · rw [hl]
    exact hpb.lift_fst _ _ _

private theorem mono_of_faithfullyMapped_mono
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (hF : F.FullyFaithful) {X Y : C} (f : X ⟶ Y)
    [Mono (F.map f)] : Mono f := by
  constructor
  intro Z a b h
  have hmap : F.map a = F.map b := by
    apply (cancel_mono (F.map f)).1
    simpa only [Functor.map_comp] using congrArg F.map h
  exact hF.map_injective hmap

private theorem representable_equalizer_map_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (T E : AlgebraicGeometry.BigFppfOver B S hS) (i : E ⟶ T)
    (p q : yoneda.obj T ⟶ F)
    (e : yoneda.obj E ⟶ F)
    (hpb : IsPullback e (yoneda.map i) (diag F) (prod.lift p q)) : Mono i := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : Mono (yoneda.map i) := hpb.mono_snd_of_mono
  exact mono_of_faithfullyMapped_mono yoneda Yoneda.fullyFaithful i

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_beauvilleLaszloGlueingFaithful
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_beauvilleLaszloGlueingFaithful
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem finiteType_locallyQuasiFinite_representable_equalizer_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (T E : AlgebraicGeometry.BigFppfOver B S hS) (i : E ⟶ T)
    (p q : yoneda.obj T ⟶ F)
    (e : yoneda.obj E ⟶ F)
    (hpb : IsPullback e (yoneda.map i) (diag F) (prod.lift p q)) :
    LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      LocallyQuasiFinite ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let : HasPullbacks C := inferInstance
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.presheaf (MorphismProperty.inverseImage
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) Q)
  have hdiag : P (pullback.diagonal (terminal.from F)) :=
    AlgebraicGeometry.presheaf_locallyQuasiFinite_pullbackDiagonal B S hS (terminal.from F) hF
  have hdiagEq : diag F ≫ (prodIsoPullback F F).hom =
      pullback.diagonal (terminal.from F) := by
    apply pullback.hom_ext <;> simp [diag]
  exact ((P.arrow_mk_iso_iff (Arrow.isoMk (Iso.refl F) (prodIsoPullback F F)
    hdiagEq.symm)).mpr hdiag).property (prod.lift p q) e i hpb

private theorem quasiAffine_of_mono_locallyQuasiFinite
    {E T : Scheme.{u}} (i : E ⟶ T) [Mono i] [LocallyOfFiniteType i]
    [LocallyQuasiFinite i] [QuasiCompact i] [IsAffine T] :
    Scheme.IsQuasiAffine E := by
  have : CompactSpace E := QuasiCompact.compactSpace_of_compactSpace i
  obtain ⟨T', j, π, hj, hjqc, hπ, hcomp⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization i
  have : IsAffine T' := isAffine_of_isAffineHom π
  exact Scheme.IsQuasiAffine.of_isImmersion j

private theorem isIso_of_section_toSpecΓ
    {E T : Scheme.{u}} (i : E ⟶ T) [Mono i] [IsAffine T]
    [Scheme.IsQuasiAffine E]
    (s : T ⟶ Spec (.of Γ(E, ⊤)))
    (hs : s ≫ Spec.map i.appTop = T.toSpecΓ)
    (hrange : Set.range s ⊆ Set.range E.toSpecΓ) : IsIso i := by
  let t := IsOpenImmersion.lift E.toSpecΓ s hrange
  have ht : t ≫ E.toSpecΓ = s := IsOpenImmersion.lift_fac _ _ hrange
  have hti : t ≫ i = 𝟙 T := by
    apply (cancel_mono T.toSpecΓ).1
    rw [Category.assoc, Scheme.toSpecΓ_naturality, reassoc_of% ht, hs, Category.id_comp]
  have hEq : i ≫ t = 𝟙 E := by
    apply (cancel_mono i).1
    rw [Category.assoc, hti, Category.id_comp, Category.comp_id]
  exact ⟨⟨t, hEq, hti⟩⟩

private theorem compactSpace_of_jointly_surjective_lifts
    {E T T₁ T₂ : Scheme.{u}} (i : E ⟶ T) [Mono i]
    [CompactSpace T₁] [CompactSpace T₂]
    (a : T₁ ⟶ T) (b : T₂ ⟶ T)
    (ha : ∀ x : T, x ∈ Set.range a ∨ x ∈ Set.range b)
    (s₁ : T₁ ⟶ E) (s₂ : T₂ ⟶ E)
    (hs₁ : s₁ ≫ i = a) (hs₂ : s₂ ≫ i = b) : CompactSpace E := by
  have hsurj : Function.Surjective (Sum.elim s₁ s₂) := by
    intro x
    rcases ha (i x) with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨Sum.inl y, i.injective ?_⟩
      show i (s₁ y) = i x
      simpa only [← Scheme.Hom.comp_apply, hs₁] using hy
    · refine ⟨Sum.inr y, i.injective ?_⟩
      show i (s₂ y) = i x
      simpa only [← Scheme.Hom.comp_apply, hs₂] using hy
  exact Function.Surjective.compactSpace (f := Sum.elim s₁ s₂)
    (continuous_sum_dom.mpr ⟨s₁.continuous, s₂.continuous⟩) hsurj

private theorem affine_lift_of_ringHom_lift
    {A A₁ A₂ A₁₂ : Type u}
    [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing A₁₂]
    (a : A →+* A₁) (b : A →+* A₂)
    (c : A₁ →+* A₁₂) (d : A₂ →+* A₁₂)
    (hcomm : c.comp a = d.comp b)
    (hlift : ∀ (C : Type u) [CommRing C] (p : C →+* A₁) (q : C →+* A₂),
      c.comp p = d.comp q → ∃ r : C →+* A, a.comp r = p ∧ b.comp r = q)
    {E : Scheme.{u}} (i : E ⟶ Spec (.of A)) [Mono i]
    (s₁ : Spec (.of A₁) ⟶ E) (s₂ : Spec (.of A₂) ⟶ E)
    (hs₁ : s₁ ≫ i = Spec.map (CommRingCat.ofHom a))
    (hs₂ : s₂ ≫ i = Spec.map (CommRingCat.ofHom b)) :
    ∃ s : Spec (.of A) ⟶ Spec Γ(E, ⊤),
      Spec.map (CommRingCat.ofHom a) ≫ s = s₁ ≫ E.toSpecΓ ∧
      Spec.map (CommRingCat.ofHom b) ≫ s = s₂ ≫ E.toSpecΓ := by
  let p := (Spec.preimage (s₁ ≫ E.toSpecΓ)).hom
  let q := (Spec.preimage (s₂ ≫ E.toSpecΓ)).hom
  have hsq : Spec.map (CommRingCat.ofHom c) ≫ s₁ = Spec.map (CommRingCat.ofHom d) ≫ s₂ := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hs₁, hs₂, ← Spec.map_comp]
    exact congrArg (fun z : A →+* A₁₂ => Spec.map (CommRingCat.ofHom z)) hcomm
  have hpq : c.comp p = d.comp q := by
    show (CommRingCat.ofHom (c.comp p)).hom = (CommRingCat.ofHom (d.comp q)).hom
    congr 1
    apply Spec.map_injective
    show Spec.map (Spec.preimage (s₁ ≫ E.toSpecΓ) ≫ CommRingCat.ofHom c) =
      Spec.map (Spec.preimage (s₂ ≫ E.toSpecΓ) ≫ CommRingCat.ofHom d)
    simpa only [CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_preimage,
      ← Category.assoc] using congrArg (fun z => z ≫ E.toSpecΓ) hsq
  obtain ⟨r, hr₁, hr₂⟩ := hlift Γ(E, ⊤) p q hpq
  refine ⟨Spec.map (CommRingCat.ofHom r), ?_, ?_⟩
  · rw [← Spec.map_comp]
    show Spec.map (CommRingCat.ofHom (a.comp r)) = _
    rw [hr₁]
    exact Spec.map_preimage _
  · rw [← Spec.map_comp]
    show Spec.map (CommRingCat.ofHom (b.comp r)) = _
    rw [hr₂]
    exact Spec.map_preimage _

private theorem spec_hom_ext_of_injective_pair
    {A A₁ A₂ C : Type u}
    [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing C]
    (a : A →+* A₁) (b : A →+* A₂)
    (hinj : Function.Injective (fun x => (a x, b x)))
    (p q : Spec (.of A) ⟶ Spec (.of C))
    (ha : Spec.map (CommRingCat.ofHom a) ≫ p = Spec.map (CommRingCat.ofHom a) ≫ q)
    (hb : Spec.map (CommRingCat.ofHom b) ≫ p = Spec.map (CommRingCat.ofHom b) ≫ q) : p = q := by
  apply Spec.homEquiv.injective
  ext x
  apply hinj
  apply Prod.ext
  · simpa only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, Spec.homEquiv_apply] using
      congrArg (fun z : CommRingCat.of C ⟶ .of A₁ => z.hom x) (congrArg Spec.preimage ha)
  · simpa only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, Spec.homEquiv_apply] using
      congrArg (fun z : CommRingCat.of C ⟶ .of A₂ => z.hom x) (congrArg Spec.preimage hb)

private theorem exists_retraction_toSpec_of_ringHom_lift
    {A A₁ A₂ A₁₂ : Type u}
    [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing A₁₂]
    (a : A →+* A₁) (b : A →+* A₂)
    (c : A₁ →+* A₁₂) (d : A₂ →+* A₁₂)
    (hcomm : c.comp a = d.comp b)
    (hinj : Function.Injective (fun x => (a x, b x)))
    (hlift : ∀ (C : Type u) [CommRing C] (p : C →+* A₁) (q : C →+* A₂),
      c.comp p = d.comp q → ∃ r : C →+* A, a.comp r = p ∧ b.comp r = q)
    {E : Scheme.{u}} (i : E ⟶ Spec (.of A)) [Mono i]
    (hcover : ∀ x : Spec (.of A),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom a)) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom b)))
    (s₁ : Spec (.of A₁) ⟶ E) (s₂ : Spec (.of A₂) ⟶ E)
    (hs₁ : s₁ ≫ i = Spec.map (CommRingCat.ofHom a))
    (hs₂ : s₂ ≫ i = Spec.map (CommRingCat.ofHom b)) :
    ∃ s : Spec (.of A) ⟶ Spec Γ(E, ⊤),
      s ≫ Spec.map i.appTop = (Spec (.of A)).toSpecΓ ∧
      Set.range s ⊆ Set.range E.toSpecΓ := by
  obtain ⟨s, ha, hb⟩ := affine_lift_of_ringHom_lift a b c d hcomm hlift i s₁ s₂ hs₁ hs₂
  refine ⟨s, ?_, ?_⟩
  · apply spec_hom_ext_of_injective_pair (C := Γ(Spec (.of A), ⊤)) a b hinj
    · rw [← Category.assoc, ha, Category.assoc, ← Scheme.toSpecΓ_naturality,
        ← Category.assoc, hs₁]
    · rw [← Category.assoc, hb, Category.assoc, ← Scheme.toSpecΓ_naturality,
        ← Category.assoc, hs₂]
  · rintro _ ⟨x, rfl⟩
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨s₁ y, (congrArg (fun z => z y) ha).symm⟩
    · exact ⟨s₂ y, (congrArg (fun z => z y) hb).symm⟩

private theorem spec_tensorProduct_jointly_surjective
    (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra R T]
    (hcover : ∀ x : Spec (.of R),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R T)))) :
    ∀ x : Spec (.of A),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A S)))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A T)))) := by
  have key (W : Type u) [CommRing W] [Algebra R W] (x : Spec (.of A))
      (y : Spec (.of W))
      (hy : Spec.map (CommRingCat.ofHom (algebraMap R W)) y =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) x) :
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A W)))) := by
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨(pullbackSpecIso R A W).hom z,
      (congrArg (fun m => m z) (pullbackSpecIso_hom_fst' R A W)).trans hz⟩
  intro x
  rcases hcover (Spec.map (CommRingCat.ofHom (algebraMap R A)) x) with ⟨y, hy⟩ | ⟨y, hy⟩
  exacts [Or.inl (key S x y hy), Or.inr (key T x y hy)]

private theorem isIso_of_mono_of_glueable_affine_lifts
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (f : R)
    (hA : BeauvilleLaszlo.IsGlueableFor (S := S) A f)
    (hcover : ∀ x : Spec (.of R),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
    {E : Scheme.{u}} (i : E ⟶ Spec (.of A))
    [Mono i] [LocallyOfFiniteType i] [LocallyQuasiFinite i]
    (s₁ : Spec (.of (TensorProduct R A S)) ⟶ E)
    (s₂ : Spec (.of (TensorProduct R A (Localization.Away f))) ⟶ E)
    (hs₁ : s₁ ≫ i = Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A S))))
    (hs₂ : s₂ ≫ i = Spec.map
      (CommRingCat.ofHom (algebraMap A (TensorProduct R A (Localization.Away f))))) :
    IsIso i := by
  let a := algebraMap A (TensorProduct R A S)
  let b := algebraMap A (TensorProduct R A (Localization.Away f))
  let c := (Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S f)))).toRingHom
  let d := (Algebra.TensorProduct.map (AlgHom.id R A)
    (Localization.awayMapₐ (Algebra.ofId R S) f)).toRingHom
  have hcomm : c.comp a = d.comp b := by
    ext x
    show BeauvilleLaszlo.baseChangeToAway A f (x ⊗ₜ[R] (1 : S)) =
      BeauvilleLaszlo.localizedBaseChangeToAway A f (x ⊗ₜ[R] (1 : Localization.Away f))
    rw [BeauvilleLaszlo.baseChangeToAway_tmul,
      BeauvilleLaszlo.localizedBaseChangeToAway_tmul, map_one, map_one]
  have hinj : Function.Injective (fun x => (a x, b x)) := by
    intro x y h
    exact eq_of_baseChanges_eq_of_isGlueable f hA
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hlift (C : Type u) [CommRing C] (p : C →+* TensorProduct R A S)
      (q : C →+* TensorProduct R A (Localization.Away f))
      (h : c.comp p = d.comp q) : ∃ r : C →+* A, a.comp r = p ∧ b.comp r = q := by
    have hcomp (x : C) : BeauvilleLaszlo.baseChangeToAway A f (p x) =
        BeauvilleLaszlo.localizedBaseChangeToAway A f (q x) := DFunLike.congr_fun h x
    obtain ⟨r, hr₁, hr₂⟩ := ringHom_lift_of_baseChanges_compatible f hA p q hcomp
    exact ⟨r, RingHom.ext hr₁, RingHom.ext hr₂⟩
  have hc := spec_tensorProduct_jointly_surjective R A S (Localization.Away f) hcover
  have : CompactSpace (Spec (.of (TensorProduct R A S))) :=
    Scheme.compactSpace_of_isAffine _
  have : CompactSpace (Spec (.of (TensorProduct R A (Localization.Away f)))) :=
    Scheme.compactSpace_of_isAffine _
  have : CompactSpace E := compactSpace_of_jointly_surjective_lifts i
    (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) hc s₁ s₂ hs₁ hs₂
  have : QuasiCompact i := inferInstance
  have : Scheme.IsQuasiAffine E := quasiAffine_of_mono_locallyQuasiFinite i
  obtain ⟨s, hs, hr⟩ := exists_retraction_toSpec_of_ringHom_lift
    a b c d hcomm hinj hlift i hc s₁ s₂ hs₁ hs₂
  exact isIso_of_section_toSpecΓ i s hs hr

private theorem isoSpec_inv_comp_eq_specMap
    {R : CommRingCat.{u}} {T : Scheme.{u}} [IsAffine T] (p : T ⟶ Spec R) :
    T.isoSpec.inv ≫ p = Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop) := by
  apply (cancel_epi T.toSpecΓ).mp
  simp only [Scheme.toSpecΓ_isoSpec_inv_assoc, Spec.map_comp]
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem equalizer_lift_of_baseChange_map_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S X : Scheme.{u})
    (hS : B.Contains S) (hX : B.Contains X) (g : B.obj hS ⟶ B.obj hX)
    {Y Z : _root_.AlgebraicGeometry.AlgebraicSpaces B X hX} (φ ψ : Y ⟶ Z)
    (h : (_root_.BeauvilleLaszlo.Space.baseChange B S X hS hX g).map φ =
      (_root_.BeauvilleLaszlo.Space.baseChange B S X hS hX g).map ψ)
    {T E : AlgebraicGeometry.BigFppfOver B X hX} (i : E ⟶ T)
    (p : yoneda.obj T ⟶ Y.obj) (e : yoneda.obj E ⟶ Z.obj)
    (hpb : IsPullback e (yoneda.map i) (diag Z.obj)
      (prod.lift (p ≫ φ.hom) (p ≫ ψ.hom)))
    (V : Scheme.{u}) (hV : B.Contains V)
    (a : V ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B X hX).obj T)
    (k : V ⟶ S) (ha : a ≫ B.inclusion.map T.hom = k ≫ B.inclusion.map g) :
    ∃ l : V ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B X hX).obj E,
      l ≫ (AlgebraicGeometry.BigFppfOver.toScheme B X hX).map i = a := by
  let V₀ : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (⟨k⟩ : B.obj hV ⟶ B.obj hS)
  let V₁ := (Over.map g).obj V₀
  let a' : V₁ ⟶ T := Over.homMk ⟨a⟩ (by
    apply ObjectProperty.hom_ext
    exact ha)
  have hcomp : yoneda.map a' ≫ (p ≫ φ.hom) = yoneda.map a' ≫ (p ≫ ψ.hom) := by
    apply yonedaEquiv.injective
    show φ.hom.app (Opposite.op V₁) (p.app (Opposite.op V₁) a') =
      ψ.hom.app (Opposite.op V₁) (p.app (Opposite.op V₁) a')
    exact congrArg (fun z => z (p.app (Opposite.op V₁) a'))
      (congrArg (fun z => z.hom.app (Opposite.op V₀)) h)
  obtain ⟨l, hl, _⟩ := equalizer_lift_of_equal_after_map B X hX
    i (p ≫ φ.hom) (p ≫ ψ.hom) e hpb a' hcomp
  exact ⟨(AlgebraicGeometry.BigFppfOver.toScheme B X hX).map l,
    congrArg (fun z => (AlgebraicGeometry.BigFppfOver.toScheme B X hX).map z) hl⟩

private theorem tensorProduct_equalizer_lift_of_baseChange_map_eq
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hS : B.Contains (Spec (.of S))) (hX : B.Contains (Spec (.of R)))
    {Y Z : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX} (φ ψ : Y ⟶ Z)
    (h : (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of S)) (Spec (.of R)) hS hX
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R S))⟩).map φ =
      (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of S)) (Spec (.of R)) hS hX
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R S))⟩).map ψ)
    {T E : AlgebraicGeometry.BigFppfOver B (Spec (.of R)) hX} (i : E ⟶ T)
    (p : yoneda.obj T ⟶ Y.obj) (e : yoneda.obj E ⟶ Z.obj)
    (hpb : IsPullback e (yoneda.map i) (diag Z.obj)
      (prod.lift (p ≫ φ.hom) (p ≫ ψ.hom)))
    (eT : (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of R)) hX).obj T ≅ Spec (.of A))
    (hT : eT.inv ≫ B.inclusion.map T.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ l : Spec (.of (TensorProduct R A S)) ⟶
        (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of R)) hX).obj E,
      l ≫ (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of R)) hX).map i ≫ eT.hom =
        Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A S))) := by
  have hA : B.Contains (Spec (.of A)) := by
    show (Spec (.of A)).size < B.cutoff
    rw [← Scheme.size_congr eT]
    exact T.left.property
  have hAS : B.Contains (Spec (.of (TensorProduct R A S))) := by
    show (Spec (.of (TensorProduct R A S))).size < B.cutoff
    rw [← Scheme.size_congr (pullbackSpecIso R A S)]
    exact Scheme.size_pullback_lt _ _ hA hS
  let a := Spec.map (CommRingCat.ofHom (algebraMap A (TensorProduct R A S)))
  let k := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R A S).toRingHom)
  have ha : (a ≫ eT.inv) ≫ B.inclusion.map T.hom =
      k ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [Category.assoc, hT]
    dsimp [a, k]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  obtain ⟨l, hl⟩ := equalizer_lift_of_baseChange_map_eq B (Spec (.of S))
    (Spec (.of R)) hS hX ⟨Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
    φ ψ h i p e hpb _ hAS (a ≫ eT.inv) k ha
  refine ⟨l, ?_⟩
  rw [← Category.assoc, hl, Category.assoc, eT.inv_hom_id, Category.comp_id]

private theorem hom_comp_eq_of_baseChanges_eq_of_affine_isGlueable
    (R S : Type u) [CommRing R] [CommRing S] (g : R →+* S) (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hS : B.Contains (Spec (.of S))) (hX : B.Contains (Spec (.of R)))
    {Y Z : _root_.AlgebraicGeometry.AlgebraicSpaces B (Spec (.of R)) hX} (φ ψ : Y ⟶ Z)
    (h₁ : (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of S)) (Spec (.of R)) hS hX
        ⟨Spec.map (CommRingCat.ofHom g)⟩).map φ =
      (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of S)) (Spec (.of R)) hS hX
        ⟨Spec.map (CommRingCat.ofHom g)⟩).map ψ)
    (h₂ : (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of (Localization.Away f)))
        (Spec (.of R)) hU hX
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩).map φ =
      (_root_.BeauvilleLaszlo.Space.baseChange B (Spec (.of (Localization.Away f)))
        (Spec (.of R)) hU hX
        ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩).map ψ)
    (T : AlgebraicGeometry.BigFppfOver B (Spec (.of R)) hX)
    (p : yoneda.obj T ⟶ Y.obj)
    (hT : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of R)) hX).obj T))
    (hA : _root_.AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX T) :
    p ≫ φ.hom = p ≫ ψ.hom := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of R)) hX
  let : HasPullbacks B.Schemes := inferInstance
  let : PreservesLimitsOfShape WalkingCospan G := by apply comp_preservesLimitsOfShape
  let : IsAffine (G.obj T) := hT
  let : Algebra R S := g.toAlgebra
  let A := Γ(G.obj T, ⊤)
  let : Algebra R A :=
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (B.inclusion.map T.hom).appTop).hom).toAlgebra
  have hA' : BeauvilleLaszlo.IsGlueableFor (S := S) A f := hA
  have hT' : (G.obj T).isoSpec.inv ≫ B.inclusion.map T.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    isoSpec_inv_comp_eq_specMap _
  obtain ⟨E, i, e, hpb⟩ := representable_equalizer_of_algebraicSpace B
    (Spec (.of R)) hX Z.property T (p ≫ φ.hom) (p ≫ ψ.hom)
  have : Mono i := representable_equalizer_map_mono B (Spec (.of R)) hX
    Z.property T E i (p ≫ φ.hom) (p ≫ ψ.hom) e hpb
  obtain ⟨hft, hqf⟩ := finiteType_locallyQuasiFinite_representable_equalizer_map
    B (Spec (.of R)) hX Z.property T E i (p ≫ φ.hom) (p ≫ ψ.hom) e hpb
  obtain ⟨s₁, hs₁⟩ := tensorProduct_equalizer_lift_of_baseChange_map_eq
    R S A B hS hX φ ψ h₁ i p e hpb (G.obj T).isoSpec hT'
  obtain ⟨s₂, hs₂⟩ := tensorProduct_equalizer_lift_of_baseChange_map_eq
    R (Localization.Away f) A B hU hX φ ψ h₂ i p e hpb (G.obj T).isoSpec hT'
  have hc : ∀ x : Spec (.of R),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
    intro x
    rcases primeSpectrum_cover_of_glueingPair g f hglue x with ⟨y | y, hy⟩
    exacts [Or.inl ⟨y, hy⟩, Or.inr ⟨y, hy⟩]
  have : IsIso (G.map i ≫ (G.obj T).isoSpec.hom) :=
    isIso_of_mono_of_glueable_affine_lifts f hA' hc _ s₁ s₂ hs₁ hs₂
  have : IsIso (G.map i) := IsIso.of_isIso_comp_right _ (G.obj T).isoSpec.hom
  have : IsIso i := isIso_of_reflects_iso i G
  apply (cancel_epi (yoneda.map i)).mp
  have hfst := congrArg (fun a => a ≫ prod.fst) hpb.w
  have hsnd := congrArg (fun a => a ≫ prod.snd) hpb.w
  simp only [diag, Category.assoc, prod.lift_fst, prod.lift_snd,
    Category.comp_id] at hfst hsnd
  exact hfst.symm.trans hsnd

private theorem natTrans_eq_of_locallySurjective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F Y Z : Cᵒᵖ ⥤ Type u} (k : F ⟶ Y)
    (hk : Presheaf.IsLocallySurjective J k) (hZ : Presheaf.IsSheaf J Z)
    (φ ψ : Y ⟶ Z) (h : k ≫ φ = k ≫ ψ) : φ = ψ := by
  let := hk
  ext X x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 hZ).isSeparated _
    (Presheaf.imageSieve_mem J k x)).ext
  rintro W a ⟨s, hs⟩
  have h₁ := ConcreteCategory.congr_hom (φ.naturality a.op) x
  have h₂ := ConcreteCategory.congr_hom (ψ.naturality a.op) x
  dsimp at h₁ h₂ ⊢
  rw [← h₁, ← h₂, ← hs]
  exact ConcreteCategory.congr_hom (congr_app h (Opposite.op W)) s

private theorem natTrans_eq_of_surjectiveEtale_atlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hZ : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Z)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ F)
    (hpS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (hpE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p)
    (φ ψ : F ⟶ Z) (h : p ≫ φ = p ≫ ψ) : φ = ψ := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hp : yoneda.relativelyRepresentable p :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
      hF.diagonal_representable p
  let V := hp.pullback p
  let s : V ⟶ U := yoneda.preimage (hp.fst p)
  have hpb : IsPullback (yoneda.map s) (yoneda.map (hp.snd p)) p p := by
    simpa [s] using hp.isPullback p
  obtain ⟨hV, hU, ⟨hc⟩⟩ :=
    AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale B S hS p s (hp.snd p) hpb hF hpS hpE
  have hh : (⟨φ⟩ : (⟨F, hF.isSheaf⟩ : Sheaf _ (Type u)) ⟶ ⟨Z, hZ⟩) = ⟨ψ⟩ :=
    Cofork.IsColimit.hom_ext hc (Sheaf.hom_ext h)
  exact congrArg (fun z => z.hom) hh

private theorem natTrans_eq_of_affine_etale_tests
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hZ : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) Z)
    (φ ψ : F ⟶ Z)
    (h : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj T ⟶ F),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) →
      AlgebraicGeometry.Space.IsEtale B S hS p → p ≫ φ = p ≫ ψ) : φ = ψ := by
  obtain ⟨I, X, hcover, hatlas⟩ :=
    AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas B S hS F hF
  apply natTrans_eq_of_locallySurjective _ (Sigma.desc fun i => (X i).ι) hcover.2 hZ
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_desc_assoc]
  obtain ⟨U, p, V, hU, hpS, hpE, _⟩ := hatlas i
  apply natTrans_eq_of_surjectiveEtale_atlas B S hS (hcover.1 i).1 hZ U p hpS hpE
  rw [← Category.assoc, ← Category.assoc]
  apply h U (p ≫ (X i).ι) hU
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    ⟨fun a b ha hb => Etale.etale_comp b (f := a)⟩
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Q.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  have hinc : Q.presheaf (X i).ι := by
    apply MorphismProperty.relative_monotone (F := yoneda) (P :=
      MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) _ _ (hcover.1 i).2
    intro A C m hm
    let : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) := hm
    exact inferInstanceAs (Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m))
  exact fun T q hq => MorphismProperty.comp_mem Q.presheaf _ _ hq
    (MorphismProperty.comp_mem Q.presheaf _ _ hpE hinc)

/-- The Beauville--Laszlo gluing functor is faithful on glueable algebraic spaces over `Spec R`. -/
@[stacks 0F9S]
theorem beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable
    (R R' : Type u) [CommRing R] [CommRing R']
    (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R')))
    (hX : B.Contains (Spec (.of R))) :
    let U' : Scheme.{u} := Spec (.of (Localization.Away (g f)))
    let U : Scheme.{u} := Spec (.of (Localization.Away f))
    let X' : Scheme.{u} := Spec (.of R')
    let X : Scheme.{u} := Spec (.of R)
    let gU : B.obj hU' ⟶ B.obj hU :=
      ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩
    let gX' : B.obj hU' ⟶ B.obj hX' :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩
    let jU : B.obj hU ⟶ B.obj hX :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩
    let jX' : B.obj hX' ⟶ B.obj hX :=
      ⟨Spec.map (CommRingCat.ofHom g)⟩
    ∀ (hcomm : gU ≫ jU = gX' ≫ jX')
      (Y Z : _root_.AlgebraicGeometry.AlgebraicSpaces B X hX),
      _root_.AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y →
      _root_.AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z →
      Function.Injective (fun (φ : Y ⟶ Z) ↦
        (BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces
          B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor.map φ) := by
  intro U' U X' X gU gX' jU jX' hcomm Y Z hY hZ φ ψ hmap
  let L := BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces
    B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
  have hUeq :
      (_root_.BeauvilleLaszlo.Space.baseChange B U X hU hX jU).map φ =
        (_root_.BeauvilleLaszlo.Space.baseChange B U X hU hX jU).map ψ :=
    map_eq_of_comp_iso_map_eq _ _ _ L.overUIso φ ψ hmap
  have hX'eq :
      (_root_.BeauvilleLaszlo.Space.baseChange B X' X hX' hX jX').map φ =
        (_root_.BeauvilleLaszlo.Space.baseChange B X' X hX' hX jX').map ψ :=
    map_eq_of_comp_iso_map_eq _ _ _ L.overX'Iso φ ψ hmap
  apply ObjectProperty.hom_ext
  apply natTrans_eq_of_affine_etale_tests B X hX Y.property Z.property.isSheaf φ.hom ψ.hom
  intro T p hT hp
  exact hom_comp_eq_of_baseChanges_eq_of_affine_isGlueable R R' g f hglue B hU hX' hX φ ψ
    hX'eq hUeq T p hT (hY T p hT hp)

end BeauvilleLaszlo.Space

end
