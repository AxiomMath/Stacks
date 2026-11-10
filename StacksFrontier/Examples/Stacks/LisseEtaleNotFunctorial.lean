module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineLineSectionsSeparate
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSchemeSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The lisse-étale site is not functorial (Stacks 07BG)

Let `f : X ⟶ Y` be a morphism of schemes. Base change along `f` is a *continuous* functor
`u : Y_{lisse,étale} ⥤ X_{lisse,étale}`
(`AlgebraicGeometry.Stack.LisseEtale.isContinuous_pullback`), so it induces an adjoint pair
`u^s ⊣ u_s` on sheaves. **Stacks 07BG** says that `u` nevertheless does not define a *morphism of
sites*: `u_s` is not left exact in general, so the assignment `Y ↦ Y_{lisse,étale}` is not
functorial even on schemes.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.exists_not_isMorphismOfSites_pullback`: **Stacks 07BG**.

## The counterexample

This is the one the source calls silly, with `p = 2`. Take `Y = Spec ℤ` and `X = Spec 𝔽₂`, and
in the lisse-étale site of `Y` take the two smooth objects `𝟙 : Y → Y` and the affine line
`A¹_ℤ = Spec ℤ[T] → Y`, with the two morphisms `a, b : Y ⟶ A¹_ℤ` given by the constant sections
`T ↦ 0` and `T ↦ 2`.

* **Their equaliser in `Y_{lisse,étale}` is the empty object.** A smooth object `W` with a
  morphism `k : W ⟶ 𝟙_Y` equalising `a` and `b` is a scheme smooth, hence flat, over `Spec ℤ` on
  which the `0` and `2` sections of the affine line agree; by
  `AlgebraicGeometry.isEmpty_of_flat_of_eval_sections_eq` it is empty. So the empty smooth object
  — the empty scheme is smooth over everything — is the equaliser, and the empty family covers it
  (`AlgebraicGeometry.Stack.LisseEtale.bot_mem_topology_of_isEmpty`).
* **After base change to `X` the two morphisms become equal**, because `2 = 0` in `𝔽₂`.

Were `u` a morphism of sites, its left adjoint `u_s` would preserve the equaliser, so the image of
the empty object would again be covered by the empty family
(`CategoryTheory.IsMorphismOfSites.bot_mem_of_equalizer_collapsed`). But the image of `𝟙_Y` under
base change is `Spec 𝔽₂`, which is nonempty, and the image of the empty object is empty, so there
is no morphism between them at all; the lisse-étale site of `X` is subcanonical
(`AlgebraicGeometry.Stack.LisseEtale.subcanonical_topology`), and over a subcanonical topology an
object admitting no morphism to `Y` is not covered by the empty family
(`CategoryTheory.GrothendieckTopology.bot_notMem_of_isEmpty_hom`). Contradiction.

## Implementation notes

The source's `a(x) = x` and `b(x) = x + p` on `V₁ = V₂ = A¹_ℤ` is replaced by the transposed
`V₁ = Spec ℤ`, `V₂ = A¹_ℤ` with the two constant sections. The content is the same — the closed
subscheme of `V₁` where the two agree is `Spec(ℤ/2)`, and the source's condition is exactly that
no scheme smooth over `Y` maps into it — and this form needs only the flat generalisation
argument of `AlgebraicGeometry.isEmpty_of_flat_of_eval_sections_eq` rather than a computation of
an equaliser subscheme.

The base ring is `ULift ℤ` and its quotient `ULift (ZMod 2)`, so that the two spectra are schemes
in the ambient universe. A big fppf site containing `Spec ℤ`, `Spec 𝔽₂`, `A¹_ℤ` and the empty
scheme is supplied by `AlgebraicGeometry.BigFppfSite.exists_containing`; the four schemes have to
be *in* the site, since every object of the lisse-étale site of `Y` is one of its objects over
`Y`.

Smoothness of the affine line over `Spec ℤ` is `RingHom.smooth_algebraMap` for the polynomial
ring, carried across `AlgebraicGeometry.HasRingHomProperty.Spec_iff`; smoothness of the empty
scheme is the standard-smooth criterion at a vacuous family of points.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07BG](https://stacks.math.columbia.edu/tag/07BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

/-- The constant section `T ↦ c` of the affine line over `Spec R` is a section of its structure
morphism. -/
private theorem Spec_map_evalRingHom_comp_Spec_map_C {R : Type u} [CommRing R] (c : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
        𝟙 (Spec (CommRingCat.of R)) := by
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of R) using 2
  ext r
  simp

/-- The affine line `Spec R[T] ⟶ Spec R` is smooth. -/
private theorem smooth_Spec_map_C (R : Type u) [CommRing R] :
    Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- Two constant sections `T ↦ c` and `T ↦ d` of the affine line over `Spec R` agree after
base change along `Spec Q ⟶ Spec R` whenever `c` and `d` have the same image in `Q`. -/
private theorem Spec_map_comp_evalRingHom_eq {R Q : Type u} [CommRing R] [CommRing Q]
    (φ : R →+* Q) {c d : R} (h : φ c = φ d) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) =
      Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom d)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · ext r
    simp
  · simpa using h

/-- The morphism from the empty scheme is smooth. -/
private theorem smooth_emptyTo (X : Scheme.{u}) : Smooth (Scheme.emptyTo X) :=
  (Smooth.iff_forall_exists_isStandardSmooth _).mpr isEmptyElim

/-- **Stacks 07BG.** *The lisse-étale site is not functorial, even for morphisms of schemes.*

There is a morphism `f : X ⟶ Y` of schemes over `S` in a big fppf site for which the base-change
functor `Y_{lisse,étale} ⥤ X_{lisse,étale}` — identified here by a natural isomorphism after
forgetting smoothness, so that no particular choice of fibre products is asserted — is
continuous, and yet does not define a morphism of sites: its pushforward on sheaves has no left
exact left adjoint.

See the module documentation for the counterexample. -/
@[stacks 07BG]
theorem exists_not_isMorphismOfSites_pullback :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : BigFppfOver B S hS) (f : X ⟶ Y)
      (F : LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS Y) ⥤
        LisseEtale.{u, w} B S hS (schemeStack.{u, w} B S hS X)),
      Nonempty (F ⋙ inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS X) ≅
        inclusion.{u, w} B S hS (schemeStack.{u, w} B S hS Y) ⋙ Over.pullback f) ∧
      F.IsContinuous (topology.{u, w} B S hS (schemeStack.{u, w} B S hS Y))
        (topology.{u, w} B S hS (schemeStack.{u, w} B S hS X)) ∧
      ¬ IsMorphismOfSites.{u + 1} F
        (topology.{u, w} B S hS (schemeStack.{u, w} B S hS Y))
        (topology.{u, w} B S hS (schemeStack.{u, w} B S hS X)) := by
  classical
  let R := ULift.{u, 0} ℤ
  let Q := ULift.{u, 0} (ZMod 2)
  let eR : R ≃+* ℤ := ULift.ringEquiv
  let eQ : Q ≃+* ZMod 2 := ULift.ringEquiv
  have : IsDomain R := Function.Injective.isDomain eR eR.injective
  let φ : R →+* Q := eQ.symm.toRingHom.comp ((Int.castRingHom (ZMod 2)).comp eR.toRingHom)
  let S : Scheme.{u} := Spec (.of R)
  let X₀ : Scheme.{u} := Spec (.of Q)
  let A : Scheme.{u} := Spec (.of (Polynomial R))
  let p : X₀ ⟶ S := Spec.map (CommRingCat.ofHom φ)
  let AtoS : A ⟶ S := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  let S₀ : Set Scheme.{u} := {S, X₀, A, ∅}
  have : Small.{u} S₀ := by
    dsimp [S₀]
    infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hSite : B.Contains S := hB S (by simp [S₀])
  have hX : B.Contains X₀ := hB X₀ (by simp [S₀])
  have hA : B.Contains A := hB A (by simp [S₀])
  have hE₀ : B.Contains (∅ : Scheme.{u}) := hB _ (by simp [S₀])
  let T := BigFppfOver.toScheme B S hSite
  let Y : BigFppfOver B S hSite := Over.mk (𝟙 (B.obj hSite))
  let pB : B.obj hX ⟶ B.obj hSite :=
    B.inclusion.preimage (X := B.obj hX) (Y := B.obj hSite) p
  let X : BigFppfOver B S hSite := Over.mk pB
  let f : X ⟶ Y := Over.homMk pB (by simp [X, Y])
  refine ⟨B, S, hSite, X, Y, f, pullback.{u, w} B S hSite f, ⟨Iso.refl _⟩,
    isContinuous_pullback.{u, w} B S hSite f, ?_⟩
  intro hmor
  -- the two constant sections of the affine line over `S`
  let a₀ : S ⟶ A := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
  let a₂ : S ⟶ A := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (2 : R)))
  have hpa : p ≫ a₀ = p ≫ a₂ := Spec_map_comp_evalRingHom_eq φ (by
    norm_num [φ, eQ, eR, ULift.ringEquiv]
    rfl)
  -- the affine line as a smooth object of the lisse-étale site of `Y`
  let AtoSB := B.inclusion.preimage (X := B.obj hA) (Y := B.obj hSite) AtoS
  let AO : BigFppfOver B S hSite := Over.mk AtoSB
  let q : AO ⟶ Y := Over.homMk AtoSB (by simp [AO, Y])
  have hq : Smooth (T.map q) := by
    change Smooth (B.inclusion.map AtoSB)
    rw [Functor.map_preimage]
    exact smooth_Spec_map_C R
  let V : LisseEtale.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y) :=
    ⟨Over.mk q, (smoothObject_schemeStack_iff.{u, w} B S hSite Y _).mpr hq⟩
  let T₀ : LisseEtale.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y) :=
    ⟨Over.mk (𝟙 Y), (smoothObject_schemeStack_iff.{u, w} B S hSite Y _).mpr (by
      change Smooth (T.map (𝟙 Y))
      rw [T.map_id]
      infer_instance)⟩
  let aB := B.inclusion.preimage (X := B.obj hSite) (Y := B.obj hA) a₀
  let bB := B.inclusion.preimage (X := B.obj hSite) (Y := B.obj hA) a₂
  have hsec (c : R) : B.inclusion.preimage (X := B.obj hSite) (Y := B.obj hA)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))) ≫ AtoSB = 𝟙 (B.obj hSite) := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_id, B.inclusion.map_comp, B.inclusion.map_preimage,
      B.inclusion.map_preimage]
    exact Spec_map_evalRingHom_comp_Spec_map_C c
  have haB : aB ≫ AtoSB = 𝟙 (B.obj hSite) := hsec 0
  have hbB : bB ≫ AtoSB = 𝟙 (B.obj hSite) := hsec 2
  let aO : Y ⟶ AO := Over.homMk aB haB
  let bO : Y ⟶ AO := Over.homMk bB hbB
  let a : T₀ ⟶ V := ObjectProperty.homMk (Over.homMk aO (Over.OverMorphism.ext haB))
  let b : T₀ ⟶ V := ObjectProperty.homMk (Over.homMk bO (Over.OverMorphism.ext hbB))
  -- the empty smooth object, and the collapsed equaliser of `a` and `b`
  let zB := B.inclusion.preimage (X := B.obj hE₀) (Y := B.obj hSite) (Scheme.emptyTo S)
  let ZO : BigFppfOver B S hSite := Over.mk zB
  let z : ZO ⟶ Y := Over.homMk zB (by simp [ZO, Y])
  have hZOempty : IsEmpty (T.obj ZO) := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  let Ez : LisseEtale.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y) :=
    ⟨Over.mk z, (smoothObject_schemeStack_iff.{u, w} B S hSite Y _).mpr (by
      change Smooth (B.inclusion.map zB)
      rw [Functor.map_preimage]
      exact smooth_emptyTo S)⟩
  have hEzempty : IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y)).obj Ez)) :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  let e : Ez ⟶ T₀ := homOfIsEmpty.{u, w} B S hSite Ez T₀
  have he : e ≫ a = e ≫ b := hom_ext_of_isEmpty.{u, w} B S hSite _ _
  have hempty : ∀ c : Fork a b, IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y)).obj c.pt)) := by
    intro c
    let W := c.pt
    let k := c.ι
    have hk : k ≫ a = k ≫ b := c.condition
    have hkbase : k.hom.left = W.obj.hom := by simpa [T₀] using Over.w k.hom
    let g : T.obj W.obj.left ⟶ Spec (CommRingCat.of R) := T.map k.hom.left
    have hgs : Smooth g := by
      change Smooth (T.map k.hom.left)
      rw [hkbase]
      exact (smoothObject_schemeStack_iff.{u, w} B S hSite Y W.obj).mp W.property
    have hgf : Flat g := inferInstance
    have hr2 : (2 : R) ≠ 0 := fun h => absurd (congrArg ULift.down h : (2 : ℤ) = 0) (by norm_num)
    refine @isEmpty_of_flat_of_eval_sections_eq R _ _ (2 : R) hr2 _ g hgf ?_
    have h := congrArg (fun m : W ⟶ V => T.map m.hom.left) hk
    change T.map (k.hom.left ≫ aO) = T.map (k.hom.left ≫ bO) at h
    rwa [Functor.map_comp, Functor.map_comp,
      show T.map aO = a₀ from B.inclusion.map_preimage _,
      show T.map bO = a₂ from B.inclusion.map_preimage _] at h
  have hl : IsLimit (Fork.ofι e he) := by
    have := hempty
    refine Fork.IsLimit.mk _ (fun c => homOfIsEmpty.{u, w} B S hSite c.pt Ez) ?_ ?_
    · exact fun c => hom_ext_of_isEmpty.{u, w} B S hSite _ _
    · exact fun c m _ => hom_ext_of_isEmpty.{u, w} B S hSite _ _
  -- after base change to `X` the two sections agree
  have hfab : (pullback.{u, w} B S hSite f).map a = (pullback.{u, w} B S hSite f).map b := by
    have hfa : f ≫ aO = f ≫ bO := by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      change B.inclusion.map (pB ≫ aB) = B.inclusion.map (pB ≫ bB)
      simpa only [Functor.map_comp, pB, aB, bB, Functor.map_preimage] using hpa
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change ((Over.pullback f).map a.hom).left = ((Over.pullback f).map b.hom).left
    have h1 : ∀ k : T₀.obj ⟶ V.obj,
        ((Over.pullback f).map k).left ≫ Limits.pullback.fst V.obj.hom f =
          Limits.pullback.fst T₀.obj.hom f ≫ k.left :=
      fun _ => Limits.pullback.lift_fst _ _ _
    have h2 : ∀ k : T₀.obj ⟶ V.obj,
        ((Over.pullback f).map k).left ≫ Limits.pullback.snd V.obj.hom f =
          Limits.pullback.snd T₀.obj.hom f :=
      fun _ => Limits.pullback.lift_snd _ _ _
    apply Limits.pullback.hom_ext
    · rw [h1 a.hom, h1 b.hom]
      have hfst : Limits.pullback.fst T₀.obj.hom f =
          Limits.pullback.snd T₀.obj.hom f ≫ f := by
        rw [← Limits.pullback.condition]
        exact (Category.comp_id _).symm
      change Limits.pullback.fst T₀.obj.hom f ≫ aO =
        Limits.pullback.fst T₀.obj.hom f ≫ bO
      rw [hfst, Category.assoc, Category.assoc, hfa]
    · rw [h2 a.hom, h2 b.hom]
  have hcov := IsMorphismOfSites.bot_mem_of_equalizer_collapsed
    (pullback.{u, w} B S hSite f)
    (topology.{u, w} B S hSite (schemeStack.{u, w} B S hSite Y))
    (topology.{u, w} B S hSite (schemeStack.{u, w} B S hSite X))
    a b e he hl (bot_mem_topology_of_isEmpty.{u, w} B S hSite Ez) hfab
  have hsub : (topology.{u, w} B S hSite (schemeStack.{u, w} B S hSite X)).Subcanonical :=
    subcanonical_topology.{u, w} B S hSite X
  have hFEempty : IsEmpty (B.inclusion.obj
      ((toSchemes.{u, w} B S hSite (schemeStack.{u, w} B S hSite X)).obj
        ((pullback.{u, w} B S hSite f).obj Ez))) :=
    ⟨fun x => isEmptyElim (T.map (Limits.pullback.fst z f) x)⟩
  let q₀ := T.map (Limits.pullback.snd (𝟙 Y) f)
  have hq₀ : IsIso q₀ := by
    dsimp [q₀]
    infer_instance
  let x₀ : B.inclusion.obj
      ((toSchemes.{u, w} B S hSite (schemeStack.{u, w} B S hSite X)).obj
        ((pullback.{u, w} B S hSite f).obj T₀)) :=
    (inv q₀) (⊥ : PrimeSpectrum Q)
  have hno : IsEmpty ((pullback.{u, w} B S hSite f).obj T₀ ⟶
      (pullback.{u, w} B S hSite f).obj Ez) :=
    ⟨fun m => isEmptyElim ((B.inclusion.map
      ((toSchemes.{u, w} B S hSite (schemeStack.{u, w} B S hSite X)).map m)) x₀)⟩
  exact GrothendieckTopology.bot_notMem_of_isEmpty_hom _ _ _ hno hcov

end AlgebraicGeometry.Stack.LisseEtale

end
