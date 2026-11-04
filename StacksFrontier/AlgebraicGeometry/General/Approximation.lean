module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation

/-!
# Separating a closed subscheme from a fibre over a finitely presented base

This file proves the approximation statement that the hard implication of Stacks 05JX rests on:
a closed subscheme of a base change `X ×_S T` which misses the fibre over a point `t ∈ T` can be
separated from that fibre already over an *affine* base `T'` which is locally of finite
presentation over `S`, after shrinking `T` to an affine neighbourhood of `t`.

The proof writes an affine neighbourhood of `t` as a cofiltered limit of affine schemes of
finite presentation over an affine open of `S` (`exists_affine_limit_presentation`, from the
direct-limit presentation of a ring as a filtered colimit of finitely presented algebras), notes
that the base changes of `f` along that tower form a limit cone with affine transition maps, and
uses Mathlib's `AlgebraicGeometry.exists_preimage_eq` to push a quasi-compact open of the limit
down to a finite stage.

## Main results

* `isPullback_baseChangeMap`: the comparison morphism between two base changes of `f` along
  `g = a ≫ b` exhibits `X ×_S T` as the base change of `X ×_S T'` along `a`.
* `exists_directedOrder_affine_limit_presentation`: a morphism of affine schemes is the limit of
  an inverse system, indexed by a nonempty directed partially ordered set, of morphisms of affine
  schemes locally of finite presentation.
* `exists_affine_limit_presentation`: the same presentation with the index set remembered only as
  a cofiltered category.

## Implementation notes

Closed subschemes are expressed by `Scheme.IdealSheafData`.  Disjointness from the fibre over
`t` is the statement that `t` is not in the image of the support.  The two comparison morphisms
`p` and `q` out of `X ×_S V` are specified by their projections rather than by a `pullback.map`
expression, so that the statement does not depend on how they are built; the ideal-sheaf
inequality `I'.comap q ≤ I.comap p` is the scheme-theoretic form of "the closed subscheme over
`V` is contained in the one pulled back from `T'`".

## References

* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.Tag05JXGeneral

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- A directed system whose canonical map out of the direct limit is bijective is a directed
colimit. -/
theorem isDirectedColimit_of_bijective
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (f : ∀ ⦃i j⦄, i ≤ j → G i →ₐ[R] G j)
    [DirectedSystem G (fun {_ _} h => ((f h : G _ →ₐ[R] G _) : G _ → G _))]
    {B : Type*} [CommRing B] [Algebra R B]
    (g : ∀ i, G i →ₐ[R] B)
    (hg : ∀ ⦃i j⦄ (h : i ≤ j) x, g j (f h x) = g i x)
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G
      (fun i j h => f (i := i) (j := j) h) B g hg)) :
    IsDirectedColimit G f B g := by
  refine ⟨fun _ _ _ hij hjk x => DirectedSystem.map_map' (fun {_ _} h => f h) hij hjk x,
    fun _ x => DirectedSystem.map_self' (fun {_ _} h => f h) x, hg, ?_, ?_⟩
  · intro b
    obtain ⟨z, rfl⟩ := hbij.2 b
    induction z using DirectLimit.induction with
    | _ i x => exact ⟨i, x, by simp⟩
  · intro i x hx
    have hz : DirectLimit.Algebra.of G (fun i j h => f (i := i) (j := j) h) i x = 0 :=
      hbij.1 (by simpa [DirectLimit.Algebra.lift_of] using hx)
    have hz' : (⟦⟨i, x⟩⟧ : DirectLimit G (fun i j h => f (i := i) (j := j) h)) = 0 := hz
    exact (DirectLimit.exists_eq_zero (⟨i, x⟩ : Σ i, G i)).mp hz'

/-- Any point of the source of a morphism of schemes has an affine neighbourhood mapping into an
affine open of the target, together with the induced morphism between them. -/
theorem exists_affine_neighborhood_lift
    {S T : Scheme.{u}} (g : T ⟶ S) (t : T) :
    ∃ (U : S.affineOpens) (V : T.affineOpens) (_ : t ∈ V.1)
      (gV : V.1.toScheme ⟶ U.1.toScheme), gV ≫ U.1.ι = V.1.ι ≫ g := by
  obtain ⟨U₀, hU₀, hgt, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := g t) (by simp)
  let U : S.affineOpens := ⟨U₀, hU₀⟩
  obtain ⟨V₀, hV₀, htV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ U₀) (x := t) hgt
  let V : T.affineOpens := ⟨V₀, hV₀⟩
  have hrange : Set.range (V.1.ι ≫ g).base ⊆ Set.range U.1.ι.base := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨g x.1, hVU x.2⟩, rfl⟩
  exact ⟨U, V, htV, IsOpenImmersion.lift U.1.ι (V.1.ι ≫ g) hrange,
    IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism of affine schemes is the limit of an inverse system of morphisms of affine schemes
locally of finite presentation over the same target, indexed by a nonempty directed partially
ordered set.  This is the geometric form of the presentation of a ring as a filtered colimit of
finitely presented algebras. -/
theorem exists_directedOrder_affine_limit_presentation
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    ∃ (Λ : Type u) (_ : PartialOrder Λ) (_ : Nonempty Λ) (_ : IsDirectedOrder Λ)
      (D : Λᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c) (e : T ≅ c.pt)
      (b : D ⟶ (Functor.const Λᵒᵖ).obj S),
      (∀ l, IsAffine (D.obj l)) ∧ (∀ l, LocallyOfFinitePresentation (b.app l)) ∧
      (∀ l, g = e.hom ≫ c.π.app l ≫ b.app l) := by
  classical
  let R := Γ(S, ⊤)
  let B := Γ(T, ⊤)
  let : Algebra R B := g.appTop.hom.toAlgebra
  obtain ⟨Λ, _, _, _, G, _, _, φ, _, σ, hσ, hfp, -, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective R B
  let hc := isDirectedColimit_of_bijective (fun {_ _} h => φ _ _ h) σ hσ hbij
  let F : Λ ⥤ CommRingCat.{u} :=
    { obj i := .of (G i)
      map {i j} h := CommRingCat.ofHom (φ i j (leOfHom h)).toRingHom
      map_id i := by ext x; exact hc.map_id i x
      map_comp h k := by ext x; exact (hc.map_comp (leOfHom h) (leOfHom k) x).symm }
  let cR : Cocone F :=
    { pt := .of B
      ι := { app i := CommRingCat.ofHom (σ i).toRingHom
             naturality i j h := by ext x; exact hc.comp (leOfHom h) x } }
  have hcR : IsColimit cR := by
    let := reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨i, y, hy⟩ := hc.jointly_surjective x
      exact ⟨i, y, hy.symm⟩
    · intro i x y hxy
      obtain ⟨j, hij, hj⟩ := hc.exists_eq_zero (x - y) (by
        rw [map_sub]
        exact sub_eq_zero.mpr hxy)
      refine ⟨j, homOfLE hij, ?_⟩
      show φ i j hij x = φ i j hij y
      exact sub_eq_zero.mp (by simpa only [map_sub] using hj)
  let D : Λᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone cR.op
  have hcS : IsLimit c := isLimitOfPreserves Scheme.Spec hcR.op
  let b : D ⟶ (Functor.const Λᵒᵖ).obj S :=
    { app i := Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ S.isoSpec.inv
      naturality i j h := by
        dsimp [D, F]
        rw [← Spec.map_comp_assoc]
        congr 2
        ext x
        exact (φ _ _ (leOfHom h.unop)).commutes x }
  have hbp (i : Λᵒᵖ) : LocallyOfFinitePresentation (b.app i) := by
    have : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop)))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
        (RingHom.finitePresentation_algebraMap.mpr (hfp i.unop))
    dsimp [b]
    infer_instance
  refine ⟨Λ, inferInstance, inferInstance, inferInstance, D, c, hcS, T.isoSpec, b,
    (fun _ => by dsimp [D, F]; infer_instance), hbp, ?_⟩
  intro i
  have hring : CommRingCat.ofHom (algebraMap R (G i.unop)) ≫
      CommRingCat.ofHom (σ i.unop).toRingHom = g.appTop := by
    ext x
    exact (σ i.unop).commutes x
  show g = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (σ i.unop).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ S.isoSpec.inv
  rw [← Spec.map_comp_assoc, hring, ← Category.assoc,
    Scheme.isoSpec_hom_naturality]
  simp

/-- A morphism of affine schemes is a cofiltered limit of morphisms of affine schemes locally of
finite presentation over the same target.  This is the geometric form of the presentation of a
ring as a filtered colimit of finitely presented algebras. -/
theorem exists_affine_limit_presentation
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    ∃ (J : Type u) (_ : Category.{u} J) (_ : IsCofiltered J)
      (D : J ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c) (e : T ≅ c.pt)
      (b : D ⟶ (Functor.const J).obj S),
      (∀ j, IsAffine (D.obj j)) ∧ (∀ j, LocallyOfFinitePresentation (b.app j)) ∧
      (∀ j, g = e.hom ≫ c.π.app j ≫ b.app j) := by
  obtain ⟨Λ, _, _, _, D, c, hc, e, b, hDa, hbp, hfac⟩ :=
    exists_directedOrder_affine_limit_presentation g
  exact ⟨Λᵒᵖ, inferInstance, inferInstance, D, c, hc, e, b, hDa, hbp, hfac⟩

/-- Factoring `g` as `a ≫ b` exhibits the base change of `f` along `g` as the base change of the
base change along `b`, via the canonical comparison morphism. -/
theorem isPullback_baseChangeMap
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (b : T' ⟶ S) (a : T ⟶ T') (h : g = a ≫ b) :
    IsPullback
      (pullback.map f g f b (𝟙 X) a (𝟙 S) (by simp) (by simpa using h))
      (pullback.snd f g) (pullback.snd f b) a := by
  apply IsPullback.of_right (t := IsPullback.of_hasPullback f b)
  · simpa [pullback.map, h] using IsPullback.of_hasPullback f g
  · simp [pullback.map]

/-- A quasi-compact open of a base change along a cofiltered limit of affine bases is already the
preimage of an open at a finite stage. -/
theorem exists_open_baseChange_of_isLimit
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (e : T ≅ c.pt) (b : D ⟶ (Functor.const J).obj S)
    (hb : ∀ j, g = e.hom ≫ c.π.app j ≫ b.app j)
    [∀ j, IsAffine (D.obj j)]
    (W : (pullback f g).Opens) (hW : IsCompact (W : Set ↑(pullback f g))) :
    ∃ (j : J) (W' : (pullback f (b.app j)).Opens),
      let q := pullback.map f g f (b.app j) (𝟙 X) (e.hom ≫ c.π.app j) (𝟙 S)
        (by simp) (by simpa [Category.assoc] using hb j)
      q ⁻¹ᵁ W' = W := by
  let a (j : J) : T ⟶ D.obj j := e.hom ≫ c.π.app j
  have ha (j : J) : g = a j ≫ b.app j := by simpa [a] using hb j
  let F : J ⥤ Scheme.{u} :=
    { obj j := pullback f (b.app j)
      map {i j} h := pullback.map f (b.app i) f (b.app j) (𝟙 X) (D.map h) (𝟙 S)
        (by simp) (by simp)
      map_id j := by apply pullback.hom_ext <;> simp [pullback.map]
      map_comp h k := by apply pullback.hom_ext <;> simp [pullback.map, Category.assoc] }
  let cF : Cone F :=
    { pt := pullback f g
      π :=
        { app j := pullback.map f g f (b.app j) (𝟙 X) (a j) (𝟙 S)
            (by simp) (by simpa using ha j)
          naturality i j h := by
            apply pullback.hom_ext <;> simp [F, a, pullback.map, Category.assoc] } }
  let α : F ⟶ D :=
    { app j := pullback.snd _ _
      naturality i j h := by simp [F, pullback.map] }
  let cT : Cone D :=
    { pt := T
      π := { app := a, naturality i j h := by simp [a] } }
  have hcT : IsLimit cT := IsLimit.ofIsoLimit hc
    (Cone.ext e.symm (fun j => by simp [cT, a]))
  have : IsConnected J := IsCofiltered.isConnected J
  have hcF : IsLimit cF := isLimitOfIsPullbackOfIsConnected α cF cT
    { hom := pullback.snd f g, w j := by simp [cF, cT, α, pullback.map] }
    (fun j => isPullback_baseChangeMap f g (b.app j) (a j) (ha j)) hcT
  have hF {i j : J} (h : i ⟶ j) : IsAffineHom (F.map h) :=
    MorphismProperty.of_isPullback
      (isPullback_baseChangeMap f (b.app i) (b.app j) (D.map h) (by simp)).flip inferInstance
  obtain ⟨j, W', -, hW'⟩ := AlgebraicGeometry.exists_preimage_eq F cF hcF W hW
  exact ⟨j, W', hW'⟩

end Stacks.AlgebraicGeometry.Tag05JXGeneral
