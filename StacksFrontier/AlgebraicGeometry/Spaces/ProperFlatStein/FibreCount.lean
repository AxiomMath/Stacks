module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Connected geometric fibres over a radicial point

Let `f' : X ⟶ Y'` be a morphism of presheaves on the big fppf site of a scheme `S` all of whose
geometric fibres are connected, let `c : h_V ⟶ Y'` be a morphism from a representable presheaf
and let `q : V ⟶ U` be a morphism of the site. Put `g = pr₂ ≫ h_q : X ×_{Y'} h_V ⟶ h_U`. Let `u`
be a point of `U` over which the underlying morphism of schemes `Q` of `q` has exactly one point
`v`, with `κ(v)/κ(u)` purely inseparable. Then every geometric fibre of `g` over `u` is connected,
so `g` has exactly one geometric connected component over `u`.

This is the step of the proof of Stacks 0E0D showing that the algebraic spaces `X_{y'_i}` are
geometrically connected over `κ(y)`.

## Main results

* `AlgebraicGeometry.ProperFlatStein.specField_hom_ext_of_isPurelyInseparable`: two morphisms from
  the spectrum of a field into `X` landing at a point `x` whose residue field is purely inseparable
  over that of its image agree as soon as they agree after composing with `Q : X ⟶ Y`.
* `AlgebraicGeometry.ProperFlatStein.exists_specField_lift_of_isPurelyInseparable`: a morphism from
  the spectrum of an algebraically closed field into `Y` landing at `Q x` lifts through `Q` to a
  morphism landing at `x`.
* `AlgebraicGeometry.Space.ProperFlatStein.geometricFiberComponentCount_eq_one`: the fibre of `g`
  over a geometric point lying over `u` has exactly one connected component.
* `AlgebraicGeometry.Space.ProperFlatStein.numberGeometricConnectedComponents_eq_one`: the number
  of geometric connected components of `g` at the point `u` is one.

## Implementation notes

Let `p : Spec Ω ⟶ U` be a geometric point lying over `u`. The two scheme-level lemmas give a
lift `ℓ : Spec Ω ⟶ V` of `p` through `q`, and show that every field-valued point of the presheaf
fibre product `W = h_V ×_{h_U} h_{Spec Ω}` is the image of a field-valued point of
`h_{Spec Ω}` under the section `s = (h_ℓ, 1) : h_{Spec Ω} ⟶ W`; so `s` is surjective on points.
Pasting cartesian squares identifies the base change of `s` along `F = X_p ⟶ W` with the fibre
of `f'` over the geometric point `ℓ ≫ c` of `Y'`, which is connected by hypothesis. Its point
space surjects continuously onto that of `F`, so `F` is connected and nonempty.

Neither integrality of `Q` nor any algebraic-space hypothesis is used: a purely inseparable
residue field extension is algebraic, which is all that the lift requires.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatStein

/-- Composing `Spec ρ ≫ fromSpecResidueField x` with `Q` factors through `κ(Q x)`. -/
private theorem comp_fromSpecResidueField_comp {X Y : Scheme.{u}} (Q : X ⟶ Y) (x : X) {K : Type u}
    [Field K] (ρ : X.residueField x ⟶ .of K) :
    (Spec.map ρ ≫ X.fromSpecResidueField x) ≫ Q =
      Spec.map (Q.residueFieldMap x ≫ ρ) ≫ Y.fromSpecResidueField (Q x) := by
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp]

/-- Two morphisms from the spectrum of a field into `X`, both with image the point `x`, agree as
soon as they agree after composing with `Q : X ⟶ Y`, provided `κ(x)` is purely inseparable over
`κ(Q x)`: both factor through `Spec κ(x)`, and a purely inseparable extension has at most one
embedding into a field over the base. -/
theorem specField_hom_ext_of_isPurelyInseparable {X Y : Scheme.{u}} (Q : X ⟶ Y) (x : X)
    (hx : (Q.residueFieldMap x).hom.IsPurelyInseparable) {K : Type u} [Field K]
    (α β : Spec (.of K) ⟶ X) (hα : ∀ z, α z = x) (hβ : ∀ z, β z = x) (h : α ≫ Q = β ≫ Q) :
    α = β := by
  obtain ⟨ρα, rfl⟩ := exists_residueFieldHom_comp_fromSpecResidueField α x hα
  obtain ⟨ρβ, rfl⟩ := exists_residueFieldHom_comp_fromSpecResidueField β x hβ
  rw [comp_fromSpecResidueField_comp, comp_fromSpecResidueField_comp, cancel_mono,
    Spec.map_inj] at h
  algebraize [(Q.residueFieldMap x).hom]
  have hρ : ρα = ρβ := CommRingCat.hom_ext
    (IsPurelyInseparable.injective_comp_algebraMap (Y.residueField (Q x)) (X.residueField x) K
      (CommRingCat.hom_ext_iff.mp h))
  rw [hρ]

/-- A morphism from the spectrum of an algebraically closed field into `Y` with image the point
`Q x` lifts through `Q : X ⟶ Y` to a morphism with image `x`, provided `κ(x)` is purely
inseparable, hence algebraic, over `κ(Q x)`: embed `κ(x)` into the field over `κ(Q x)`. -/
theorem exists_specField_lift_of_isPurelyInseparable {X Y : Scheme.{u}} (Q : X ⟶ Y) (x : X)
    (hx : (Q.residueFieldMap x).hom.IsPurelyInseparable) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (φ : Spec (.of Ω) ⟶ Y) (hφ : ∀ z, φ z = Q x) :
    ∃ ℓ : Spec (.of Ω) ⟶ X, ℓ ≫ Q = φ ∧ ∀ z, ℓ z = x := by
  obtain ⟨ρ, rfl⟩ := exists_residueFieldHom_comp_fromSpecResidueField φ (Q x) hφ
  algebraize [(Q.residueFieldMap x).hom]
  let : Algebra (Y.residueField (Q x)) Ω := ρ.hom.toAlgebra
  let σ : X.residueField x →ₐ[Y.residueField (Q x)] Ω := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ X.fromSpecResidueField x, ?_, fun z ↦ ?_⟩
  · rw [comp_fromSpecResidueField_comp]
    congr 2
    ext a
    exact σ.commutes a
  · rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry.ProperFlatStein

namespace AlgebraicGeometry.Space.ProperFlatStein

open AlgebraicGeometry.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A geometric point `p` of `h_U` whose underlying morphism lands at `u` lifts through `q : V ⟶ U`
to a morphism landing at `v`, when `v` is the only point over `u` and `κ(v)/κ(u)` is purely
inseparable. -/
theorem exists_value_lift_of_isPurelyInseparable {U V : BigFppfOver B S hS} (q : V ⟶ U)
    (u : (BigFppfOver.toScheme B S hS).obj U) (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (BigFppfOver.toScheme B S hS).map q ⁻¹' {u} = {v})
    (hinsep : ((BigFppfOver.toScheme B S hS).map q |>.residueFieldMap v).hom.IsPurelyInseparable)
    (p : GeometricPoint B S hS (yoneda.obj U))
    (hφ : ∀ z, (BigFppfOver.toScheme B S hS).map p.val.value z = u) :
    ∃ ℓ : p.val.siteObject ⟶ V,
      ℓ ≫ q = p.val.value ∧ ∀ z, (BigFppfOver.toScheme B S hS).map ℓ z = v := by
  have : IsAlgClosed p.val.carrier := p.prop
  have hQv : (BigFppfOver.toScheme B S hS).map q v = u :=
    (Set.ext_iff.mp hv v).mpr (Set.mem_singleton v)
  obtain ⟨ℓs, hℓQ, hℓpt⟩ := exists_specField_lift_of_isPurelyInseparable
    ((BigFppfOver.toScheme B S hS).map q) v hinsep (Ω := p.val.carrier)
    ((BigFppfOver.toScheme B S hS).map p.val.value) fun z ↦ (hφ z).trans hQv.symm
  have hw : ∀ {A A' : BigFppfOver B S hS} (g : A ⟶ A'),
      (BigFppfOver.toScheme B S hS).map g ≫ A'.hom.hom = A.hom.hom :=
    fun g ↦ congrArg (fun k ↦ k.hom) (Over.w g)
  refine ⟨Over.homMk (⟨ℓs⟩ : p.val.siteObject.left ⟶ V.left) (by
    ext
    show ℓs ≫ V.hom.hom = p.val.toBase
    rw [← hw q, ← Category.assoc, hℓQ]
    exact hw p.val.value), ?_, hℓpt⟩
  exact (BigFppfOver.toScheme B S hS).map_injective (by rw [Functor.map_comp]; exact hℓQ)

/-- A section `s = (h_ℓ, 1)` of `h_V ×_{h_U} h_W ⟶ h_W`, where `ℓ ≫ q = φ` lands at the only
point `v` over `u` and `κ(v)/κ(u)` is purely inseparable, is surjective on points. -/
theorem surjective_pointsMap_of_isPurelyInseparable {U V W : BigFppfOver B S hS} (q : V ⟶ U)
    (φ : W ⟶ U) (ℓ : W ⟶ V) (hℓq : ℓ ≫ q = φ) (u : (BigFppfOver.toScheme B S hS).obj U)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (BigFppfOver.toScheme B S hS).map q ⁻¹' {u} = {v})
    (hinsep : ((BigFppfOver.toScheme B S hS).map q |>.residueFieldMap v).hom.IsPurelyInseparable)
    (hφ : ∀ z, (BigFppfOver.toScheme B S hS).map φ z = u)
    (hℓ : ∀ z, (BigFppfOver.toScheme B S hS).map ℓ z = v)
    (s : yoneda.obj W ⟶ pullback (yoneda.map q) (yoneda.map φ))
    (hs₁ : s ≫ pullback.fst _ _ = yoneda.map ℓ) (hs₂ : s ≫ pullback.snd _ _ = 𝟙 _) :
    Function.Surjective (pointsMap B S hS _ s) := by
  intro z
  obtain ⟨⟨K, hK, τ, w⟩, rfl⟩ := Quot.exists_rep z
  obtain ⟨k, rfl⟩ := yonedaEquiv.surjective w
  obtain ⟨a, ha⟩ := yoneda.map_surjective (k ≫ pullback.fst _ _)
  obtain ⟨b, hb⟩ := yoneda.map_surjective (k ≫ pullback.snd _ _)
  have hab : a ≫ q = b ≫ φ := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, ha, hb, Category.assoc, Category.assoc,
      pullback.condition])
  have hpa : ∀ z, (BigFppfOver.toScheme B S hS).map a z = v := by
    intro z
    have hmem : (BigFppfOver.toScheme B S hS).map a z ∈
        (BigFppfOver.toScheme B S hS).map q ⁻¹' {u} := by
      show (BigFppfOver.toScheme B S hS).map q ((BigFppfOver.toScheme B S hS).map a z) = u
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hab, Functor.map_comp,
        Scheme.Hom.comp_apply, hφ]
    rwa [hv] at hmem
  have hpb : ∀ z, (BigFppfOver.toScheme B S hS).map (b ≫ ℓ) z = v := fun z ↦ by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hℓ]
  have haeq : a = b ≫ ℓ := (BigFppfOver.toScheme B S hS).map_injective
    (specField_hom_ext_of_isPurelyInseparable ((BigFppfOver.toScheme B S hS).map q) v hinsep
      (K := K) _ _ hpa hpb (by
        rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hℓq, hab]))
  have hk : k = yoneda.map b ≫ s := pullback.hom_ext
    (by rw [← ha, haeq, Functor.map_comp, Category.assoc, hs₁])
    (by rw [← hb, Category.assoc, hs₂, Category.comp_id])
  refine ⟨FieldValuedPoint.class B S hS _
    { carrier := K, contained := hK, toBase := τ, value := b }, ?_⟩
  rw [pointsMap_class, hk, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rfl

/-- Let `f' : X ⟶ Y'` have connected geometric fibres, let `c : h_V ⟶ Y'` and `q : V ⟶ U`, and
let `u` be a point of `U` over which the morphism of schemes underlying `q` has the single point
`v`, with `κ(v)/κ(u)` purely inseparable. Then the fibre of `pr₂ ≫ h_q : X ×_{Y'} h_V ⟶ h_U` over
any geometric point lying over `u` has exactly one connected component. -/
theorem geometricFiberComponentCount_eq_one
    {X Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f' : X ⟶ Y')
    (hconn : ∀ y' : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y'.val.value))
    {U V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ Y') (q : V ⟶ U)
    (u : (BigFppfOver.toScheme B S hS).obj U) (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (BigFppfOver.toScheme B S hS).map q ⁻¹' {u} = {v})
    (hinsep : ((BigFppfOver.toScheme B S hS).map q |>.residueFieldMap v).hom.IsPurelyInseparable)
    (p : GeometricPoint B S hS (yoneda.obj U))
    (hp : pointsToScheme B S hS U p.image = u) :
    geometricFiberComponentCount B S hS (pullback.snd f' c ≫ yoneda.map q) p.val = 1 := by
  let φ : p.val.siteObject ⟶ U := p.val.value
  have hφ : ∀ z, (BigFppfOver.toScheme B S hS).map φ z = u := by
    intro z
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.val.siteObject) :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.val.carrier)))
    rw [← hp]
    exact congrArg ((BigFppfOver.toScheme B S hS).map φ) (Subsingleton.elim _ _)
  obtain ⟨ℓ, hℓq, hℓpt⟩ := exists_value_lift_of_isPurelyInseparable B S hS q u v hv hinsep p hφ
  -- The morphism represented by `p` is `h_φ`, definitionally.
  show Cardinal.toENat (Cardinal.mk (ConnectedComponents (points B S hS
    (pullback (pullback.snd f' c ≫ yoneda.map q) (yoneda.map φ))))) = 1
  -- The section `s = (h_ℓ, 1)` of `h_V ×_{h_U} h_{Spec Ω} ⟶ h_{Spec Ω}`.
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s : yoneda.obj p.val.siteObject ⟶
      pullback (yoneda.map q) (yoneda.map φ),
      s ≫ pullback.fst _ _ = yoneda.map ℓ ∧ s ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨pullback.lift (yoneda.map ℓ) (𝟙 _) (by rw [← yoneda.map_comp, hℓq, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- The comparison `F = X_p ⟶ h_V ×_{h_U} h_{Spec Ω}`.
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h : pullback (pullback.snd f' c ≫ yoneda.map q) (yoneda.map φ) ⟶
      pullback (yoneda.map q) (yoneda.map φ),
      h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.snd f' c ∧
        h ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ pullback.snd f' c) (pullback.snd _ _)
        (by rw [Category.assoc, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsurj := surjective_pointsMap_of_isPurelyInseparable B S hS q φ ℓ hℓq u v hv hinsep hφ
    hℓpt s hs₁ hs₂
  have sqA : IsPullback (pullback.fst (pullback.snd f' c ≫ yoneda.map q) (yoneda.map φ)) h
      (pullback.snd f' c) (pullback.fst (yoneda.map q) (yoneda.map φ)) :=
    IsPullback.of_bot (by rw [hh₂]; exact IsPullback.of_hasPullback _ _) hh₁.symm
      (IsPullback.of_hasPullback _ _)
  have outer := ((IsPullback.of_hasPullback h s).paste_horiz sqA).paste_horiz
    (IsPullback.of_hasPullback f' c)
  let y' : GeometricPoint B S hS Y' :=
    ⟨{ carrier := p.val.carrier, contained := p.val.contained, toBase := p.val.toBase
       value := yonedaEquiv ((s ≫ pullback.fst _ _) ≫ c) }, p.prop⟩
  have hc := hconn y'
  have e : yonedaEquiv.symm y'.val.value = (s ≫ pullback.fst _ _) ≫ c :=
    Equiv.symm_apply_apply _ _
  rw [e] at hc
  have hW : ConnectedPoints B S hS (pullback h s) :=
    connectedSpace_of_presheafIso B S hS outer.isoPullback.symm hc
  have hsurjF := surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback h s).flip
    hsurj
  have := hsurjF.connectedSpace (continuous_pointsMap B S hS _)
  have hone : Cardinal.mk (ConnectedComponents (points B S hS
      (pullback (pullback.snd f' c ≫ yoneda.map q) (yoneda.map φ)))) = 1 :=
    Cardinal.eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [hone, map_one]

/-- In the situation of
`AlgebraicGeometry.Space.ProperFlatStein.geometricFiberComponentCount_eq_one`, the number
of geometric connected components of `pr₂ ≫ h_q : X ×_{Y'} h_V ⟶ h_U` at the point of `h_U`
corresponding to `u` is one. -/
theorem numberGeometricConnectedComponents_eq_one
    {X Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f' : X ⟶ Y')
    (hconn : ∀ y' : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y'.val.value))
    {U V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ Y') (q : V ⟶ U)
    (u : (BigFppfOver.toScheme B S hS).obj U) (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (BigFppfOver.toScheme B S hS).map q ⁻¹' {u} = {v})
    (hinsep : ((BigFppfOver.toScheme B S hS).map q |>.residueFieldMap v).hom.IsPurelyInseparable)
    (y : points B S hS (yoneda.obj U)) (hy : pointsToScheme B S hS U y = u) :
    numberGeometricConnectedComponents B S hS (pullback.snd f' c ≫ yoneda.map q) y = 1 := by
  have hcount (p : GeometricPoint B S hS (yoneda.obj U)) (hp : p.image = y) :
      geometricFiberComponentCount B S hS (pullback.snd f' c ≫ yoneda.map q) p.val = 1 :=
    geometricFiberComponentCount_eq_one B S hS f' hconn c q u v hv hinsep p (by rw [hp, hy])
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS (yoneda.obj U) y
  exact le_antisymm (sInf_le ⟨p, hp, hcount p hp⟩)
    (le_sInf fun n ⟨p', hp', hn⟩ ↦ hn ▸ (hcount p' hp').ge)

end AlgebraicGeometry.Space.ProperFlatStein

end
