module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine

/-!
# Closed immersions of inverse limits of algebraic spaces

A morphism of cofiltered inverse systems of algebraic spaces with affine transition maps
induces a closed immersion on limits when it is a closed immersion at every stage.

## Main results

* `AlgebraicGeometry.exists_closedSubschemeInter`: a family of closed immersions into a scheme
  has a scheme-theoretic intersection.
* `AlgebraicGeometry.exists_siteClosedInter`: the scheme-theoretic intersection of a family of
  closed immersions into an object of the big fppf site is again an object of that site.
* `AlgebraicGeometry.Space.isClosedImmersion_limitMap`: the induced map of inverse limits
  is a closed immersion.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 0CUH](https://stacks.math.columbia.edu/tag/0CUH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Scheme-theoretic intersections of families of closed subschemes -/

/-- A family of closed immersions `v i : V i ⟶ A` has a scheme-theoretic intersection: a closed
immersion `w : W ⟶ A` that factors through every `v i` and through which every morphism to `A`
factoring through all the `v i` factors. -/
@[sga "3 VIII 6.4" "Final reduction step"]
public theorem exists_closedSubschemeInter {A : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (v : ∀ i, V i ⟶ A) (hv : ∀ i, IsClosedImmersion (v i)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ A), IsClosedImmersion w ∧
      (∀ i, ∃ q : W ⟶ V i, q ≫ v i = w) ∧
      (∀ (T : Scheme.{u}) (φ : T ⟶ A), (∀ i, ∃ ψ : T ⟶ V i, ψ ≫ v i = φ) →
        ∃ χ : T ⟶ W, χ ≫ w = φ) := by
  refine ⟨(⨆ i, (v i).ker).subscheme, (⨆ i, (v i).ker).subschemeι, inferInstance, ?_, ?_⟩
  · intro i
    refine ⟨IsClosedImmersion.lift (v i) (⨆ i, (v i).ker).subschemeι ?_,
      IsClosedImmersion.lift_fac _ _ _⟩
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact le_iSup (fun i => (v i).ker) i
  · intro T φ h
    refine ⟨IsClosedImmersion.lift (⨆ i, (v i).ker).subschemeι φ ?_,
      IsClosedImmersion.lift_fac _ _ _⟩
    rw [Scheme.IdealSheafData.ker_subschemeι]
    refine iSup_le fun i => ?_
    obtain ⟨ψ, hψ⟩ := h i
    exact hψ ▸ Scheme.Hom.le_ker_comp ψ (v i)

/-- The scheme-theoretic intersection of a family of closed immersions into an object `a` of
the big fppf site of `S` is again an object of that site. -/
public theorem exists_siteClosedInter (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (a : BigFppfOver B S hS) {ι : Type*} (Z : ι → BigFppfOver B S hS)
    (sn : ∀ i, Z i ⟶ a)
    (hsn : ∀ i, IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (sn i))) :
    ∃ (b : BigFppfOver B S hS) (sb : b ⟶ a),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map sb) ∧
      (∀ i, ∃ q : b ⟶ Z i, q ≫ sn i = sb) ∧
      (∀ (T : BigFppfOver B S hS) (φ : T ⟶ a), (∀ i, ∃ ψ : T ⟶ Z i, ψ ≫ sn i = φ) →
        ∃ χ : T ⟶ b, χ ≫ sb = φ) := by
  obtain ⟨W, w, hw, hq, hl⟩ :=
    exists_closedSubschemeInter (fun i => (BigFppfOver.toScheme B S hS).map (sn i)) hsn
  have hWsize : B.Contains W := Scheme.size_lt_of_isClosedImmersion w a.left.property
  refine ⟨Over.mk (ObjectProperty.homMk (X := B.obj hWsize) (Y := a.left) w ≫ a.hom),
    Over.homMk (ObjectProperty.homMk (X := B.obj hWsize) (Y := a.left) w) rfl, hw, ?_, ?_⟩
  · intro i
    obtain ⟨q, hq'⟩ := hq i
    have key : ObjectProperty.homMk (X := B.obj hWsize) (Y := (Z i).left) q ≫ (sn i).left
        = ObjectProperty.homMk (X := B.obj hWsize) (Y := a.left) w := by
      apply ObjectProperty.hom_ext
      simpa using hq'
    refine ⟨Over.homMk (ObjectProperty.homMk (X := B.obj hWsize) (Y := (Z i).left) q)
      (by simp only [Over.mk_hom]; rw [← Over.w (sn i), ← Category.assoc, key]), ?_⟩
    ext1
    simpa using key
  · intro T φ h
    obtain ⟨χ, hχ⟩ := hl ((BigFppfOver.toScheme B S hS).obj T)
      ((BigFppfOver.toScheme B S hS).map φ) fun i => by
        obtain ⟨ψ, hψ⟩ := h i
        exact ⟨(BigFppfOver.toScheme B S hS).map ψ, by rw [← Functor.map_comp, hψ]⟩
    have key : ObjectProperty.homMk (X := T.left) (Y := B.obj hWsize) χ
        ≫ ObjectProperty.homMk (X := B.obj hWsize) (Y := a.left) w = φ.left := by
      apply ObjectProperty.hom_ext
      simpa using hχ
    refine ⟨Over.homMk (ObjectProperty.homMk (X := T.left) (Y := B.obj hWsize) χ)
      (by simp only [Over.mk_hom]; rw [← Category.assoc, key]; exact Over.w φ), ?_⟩
    ext1
    simpa using key

namespace Space

/-! ### Closed immersions of inverse limits -/

/-- A stagewise closed immersion between inverse systems of algebraic spaces with affine
transition morphisms induces a closed immersion of their inverse limits. -/
@[stacks 0CUH]
theorem isClosedImmersion_limitMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X Y : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (η : X ⟶ Y)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X.obj i))
    (hY : ∀ i, IsAlgebraicSpace B S hS (Y.obj i))
    (hXAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (X.map f))
    (hYAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (Y.map f))
    (hClosed : ∀ i, IsClosedImmersion B S hS (η.app i)) :
    IsClosedImmersion B S hS (limMap η) := by
  have _ := hX
  have _ := hY
  have _ := @hXAffine
  have _ := @hYAffine
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a g
  choose Z sn fs hpb using fun i : I =>
    MorphismProperty.relative.rep (hClosed i) (g ≫ limit.π Y i)
  have hci : ∀ i, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (sn i)) := fun i =>
    MorphismProperty.relative.property (hClosed i) (g ≫ limit.π Y i) (fs i) (sn i) (hpb i)
  have hmono : ∀ i, Mono (sn i) := fun i =>
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := sn i) inferInstance
  obtain ⟨bb, snb, hsnb, hpex, hlift⟩ := exists_siteClosedInter B S hS a Z sn hci
  have : Mono snb := (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := snb) inferInstance
  choose p hp using hpex
  have hζaux : ∀ (i j : I) (f : i ⟶ j),
      (fs i ≫ X.map f) ≫ η.app j = yoneda.map (sn i) ≫ (g ≫ limit.π Y j) := by
    intro i j f
    rw [Category.assoc, η.naturality f, ← Category.assoc, (hpb i).w, Category.assoc,
      Category.assoc, limit.w]
  have hζex : ∀ (i j : I) (f : i ⟶ j), ∃ z : Z i ⟶ Z j,
      yoneda.map z ≫ fs j = fs i ≫ X.map f ∧ z ≫ sn j = sn i := by
    intro i j f
    refine ⟨yoneda.preimage ((hpb j).lift (fs i ≫ X.map f) (yoneda.map (sn i)) (hζaux i j f)),
      ?_, ?_⟩
    · rw [Functor.map_preimage]
      exact (hpb j).lift_fst _ _ _
    · apply Functor.map_injective (yoneda (C := BigFppfOver B S hS))
      rw [Functor.map_comp, Functor.map_preimage]
      exact (hpb j).lift_snd _ _ _
  choose ζ hζfs hζsn using hζex
  have hpζ : ∀ (i j : I) (f : i ⟶ j), p i ≫ ζ i j f = p j := by
    intro i j f
    rw [← cancel_mono (sn j), Category.assoc, hζsn i j f, hp i, hp j]
  have hcompat : ∀ (i j : I) (f : i ⟶ j),
      (yoneda.map (p i) ≫ fs i) ≫ X.map f = yoneda.map (p j) ≫ fs j := by
    intro i j f
    rw [Category.assoc, ← hζfs i j f, ← Category.assoc, ← Functor.map_comp, hpζ i j f]
  obtain ⟨fsb, hfsb⟩ : ∃ fsb : yoneda.obj bb ⟶ limit X,
      ∀ i, fsb ≫ limit.π X i = yoneda.map (p i) ≫ fs i :=
    ⟨limit.lift X ⟨yoneda.obj bb, ⟨fun i => yoneda.map (p i) ≫ fs i, fun {i j} f => by
      simpa using (hcompat i j f).symm⟩⟩, fun i => limit.lift_π _ _⟩
  have hw : fsb ≫ limMap η = yoneda.map snb ≫ g := by
    refine limit.hom_ext fun i => ?_
    rw [Category.assoc, limMap_π, ← Category.assoc, hfsb i, Category.assoc, (hpb i).w,
      ← Category.assoc, ← Functor.map_comp, hp i, Category.assoc]
  have key : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (uu : T ⟶ limit X)
      (t : T ⟶ yoneda.obj a), uu ≫ limMap η = t ≫ g →
      ∃ m : T ⟶ yoneda.obj bb, m ≫ yoneda.map snb = t := by
    intro T uu t hut
    have haux : ∀ i, (uu ≫ limit.π X i) ≫ η.app i = t ≫ (g ≫ limit.π Y i) := by
      intro i
      rw [Category.assoc, ← limMap_π, ← Category.assoc, hut, Category.assoc]
    have hfac : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (x : T.obj U) (i : I),
        ∃ ψ : U.unop ⟶ Z i, ψ ≫ sn i = t.app U x := by
      intro U x i
      exact ⟨((hpb i).lift (uu ≫ limit.π X i) t (haux i)).app U x,
        ConcreteCategory.congr_hom (NatTrans.congr_app ((hpb i).lift_snd _ _ _) U) x⟩
    choose mm hmm using fun (U : (BigFppfOver B S hS)ᵒᵖ) (x : T.obj U) =>
      hlift U.unop (t.app U x) (hfac U x)
    refine ⟨{ app := fun U => ↾(mm U), naturality := ?_ }, ?_⟩
    · intro U U' k
      ext x
      change mm U' (T.map k x) = k.unop ≫ mm U x
      rw [← cancel_mono snb, Category.assoc, hmm, hmm]
      exact ConcreteCategory.congr_hom (t.naturality k) x
    · ext U x
      exact hmm U x
  have hfacleft : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (uu : T ⟶ limit X)
      (t : T ⟶ yoneda.obj a), uu ≫ limMap η = t ≫ g → ∀ m : T ⟶ yoneda.obj bb,
      m ≫ yoneda.map snb = t → m ≫ fsb = uu := by
    intro T uu t hut m hm
    refine limit.hom_ext fun i => ?_
    have haux : (uu ≫ limit.π X i) ≫ η.app i = t ≫ (g ≫ limit.π Y i) := by
      rw [Category.assoc, ← limMap_π, ← Category.assoc, hut, Category.assoc]
    have h1 : m ≫ yoneda.map (p i) = (hpb i).lift (uu ≫ limit.π X i) t haux := by
      rw [← cancel_mono (yoneda.map (sn i)), Category.assoc, ← Functor.map_comp, hp i, hm,
        (hpb i).lift_snd]
    rw [Category.assoc, hfsb i, ← Category.assoc, h1, (hpb i).lift_fst]
  refine ⟨bb, fsb, snb, IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => (key s.pt s.fst s.snd s.condition).choose)
    (fun s => hfacleft s.pt s.fst s.snd s.condition _
      (key s.pt s.fst s.snd s.condition).choose_spec)
    (fun s => (key s.pt s.fst s.snd s.condition).choose_spec)
    (fun s m _ h2 => by
      rw [← cancel_mono (yoneda.map snb), h2,
        (key s.pt s.fst s.snd s.condition).choose_spec])), hsnb⟩

end Space

end AlgebraicGeometry

end
