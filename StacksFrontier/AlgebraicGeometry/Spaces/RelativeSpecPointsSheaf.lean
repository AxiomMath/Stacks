module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointPushforwardAlgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecChartEval

/-!
# The functor of points of a relative spectrum is an fppf sheaf

For a sheaf of `𝒪_X`-algebras `𝒜` on an algebraic space `X`, the presheaf
`AlgebraicGeometry.Space.relativeSpecPoints` sends `T` to the pairs `(x, α)` of a point
`x ∈ X(T)` and a morphism of `𝒪_X`-algebras `α : 𝒜 ⟶ x_* 𝒪_T`.  This file proves that it is a
sheaf for the fppf topology.

## Main results

* `AlgebraicGeometry.Space.isSheaf_relativeSpecPoints`: the functor of points of the relative
  spectrum is an fppf sheaf.

## Implementation notes

The points of `X` glue because `X` is a sheaf.  The morphisms of algebras glue by
`AlgebraicGeometry.Space.existsUnique_pushforwardAlgebra_lift_of_covering`: for a covering sieve
`R` of `T` and the glued point `x`, the base changes to an étale chart `V` of `X` of the members of
`R` generate a sieve on `T ×_X V` containing the pullback of `R` along the projection
`T ×_X V ⟶ T`, hence a covering sieve, and the compatibility of the family of morphisms of
algebras is the compatibility of the given family of points.

The points `x_f ∈ X(T')` of the members `f : T' ⟶ T` of the family are only propositionally equal
to the restrictions of the glued point, so the morphisms of algebras are moved between the
corresponding objects `AlgebraicGeometry.Space.specPointOver` along the identity morphisms
`AlgebraicGeometry.Space.specPointOverEq`, never along a transport of the dependent second
component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- The identity of `T`, as a morphism over `X` between the objects `specPointOver T x` and
`specPointOver T x'` of two equal points. -/
def specPointOverEq {T : BigFppfOver B S hS} {x x' : X.1.obj (op T)} (h : x = x') :
    specPointOver B S hS T x ⟶ specPointOver B S hS T x' :=
  Over.homMk (𝟙 _) (by subst h; exact Category.id_comp _)

/-- The underlying morphism of `AlgebraicGeometry.Space.specPointOverEq h` is the identity of
`T`. -/
@[simp]
theorem specPointOverEq_left {T : BigFppfOver B S hS} {x x' : X.1.obj (op T)} (h : x = x') :
    (specPointOverEq B S hS h).left = 𝟙 _ :=
  rfl

variable {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}

/-- `AlgebraicGeometry.Space.compPushforwardAlgebraMap` only depends on the underlying morphism
of algebraic spaces. -/
theorem compPushforwardAlgebraMap_congr {P Q : Over X} (α : A ⟶ pushforwardAlgebra B S hS P)
    {f f' : Q ⟶ P} (h : f.left = f'.left) :
    compPushforwardAlgebraMap B S hS α f = compPushforwardAlgebraMap B S hS α f' := by
  rw [Over.OverMorphism.ext h]

/-- Equal points of the relative spectrum give equal morphisms of algebras after composing with
morphisms over `X` with the same underlying morphism. -/
theorem RelativeSpecPoint.comp_hom_eq_of_eq {T : BigFppfOver B S hS}
    {p p' : RelativeSpecPoint B S hS A T} (h : p = p') {Z : Over X}
    (e : Z ⟶ specPointOver B S hS T p.pt) (e' : Z ⟶ specPointOver B S hS T p'.pt)
    (he : e.left = e'.left) :
    compPushforwardAlgebraMap B S hS p.hom e = compPushforwardAlgebraMap B S hS p'.hom e' := by
  subst h
  exact compPushforwardAlgebraMap_congr B S hS p.hom he

/-- Two points of the relative spectrum are equal when their points of `X` are and their
morphisms of algebras agree along `AlgebraicGeometry.Space.specPointOverEq`. -/
theorem RelativeSpecPoint.ext_of_comp {T : BigFppfOver B S hS}
    {p p' : RelativeSpecPoint B S hS A T} (h : p'.pt = p.pt)
    (hh : compPushforwardAlgebraMap B S hS p.hom (specPointOverEq B S hS h) = p'.hom) : p = p' := by
  obtain ⟨x, α⟩ := p
  obtain ⟨x', α'⟩ := p'
  change x' = x at h
  subst h
  change compPushforwardAlgebraMap B S hS α (specPointOverEq B S hS rfl) = α' at hh
  rw [compPushforwardAlgebraMap_congr B S hS α (f := specPointOverEq B S hS rfl) (f' := 𝟙 _) rfl,
    compPushforwardAlgebraMap_id] at hh
  rw [hh]

/-- A morphism of algebras of a point of the relative spectrum, composed with a morphism over `X`
from a representable algebraic space whose underlying morphism is that of `a : W ⟶ T'`, is the
morphism of algebras of the pulled-back point `p.map a`, read along an identity. -/
theorem RelativeSpecPoint.exists_comp_hom_eq_map {T' W : BigFppfOver B S hS}
    (p : RelativeSpecPoint B S hS A T') {y : X.1.obj (op T')} (hy : y = p.pt)
    {z : yonedaSpace B S hS W ⟶ X} (r : Over.mk z ⟶ specPointOver B S hS T' y) (a : W ⟶ T')
    (ha : r.left = ObjectProperty.homMk (yoneda.map a)) :
    ∃ E : Over.mk z ⟶ specPointOver B S hS W (p.map B S hS a).pt, E.left = 𝟙 _ ∧
      compPushforwardAlgebraMap B S hS p.hom (r ≫ specPointOverEq B S hS hy) =
        compPushforwardAlgebraMap B S hS (p.map B S hS a).hom E := by
  subst hy
  have hw : (𝟙 _ : yonedaSpace B S hS W ⟶ _) ≫
      (specPointOver B S hS W (X.1.map a.op p.pt)).hom = (Over.mk z).hom := by
    rw [Category.id_comp, ← Over.w r, ha]
    exact ObjectProperty.hom_ext _ (yonedaEquiv_symm_map a.op p.pt)
  let E : Over.mk z ⟶ specPointOver B S hS W (X.1.map a.op p.pt) := Over.homMk (𝟙 _) hw
  refine ⟨E, rfl, ?_⟩
  refine (compPushforwardAlgebraMap_congr B S hS p.hom ?_).trans
    (compPushforwardAlgebraMap_comp B S hS p.hom (specPointOverMap B S hS a p.pt) E)
  rw [Over.comp_left, Over.comp_left, specPointOverEq_left, ha, specPointOverMap_left,
    Category.comp_id]
  exact (Category.id_comp _).symm

/-- Composing twice is composing with the composite, up to the underlying morphism. -/
theorem compPushforwardAlgebraMap_comp_of_left {P Q R : Over X}
    (α : A ⟶ pushforwardAlgebra B S hS P) (f : Q ⟶ P) (k : R ⟶ Q) (f' : R ⟶ P)
    (h : k.left ≫ f.left = f'.left) :
    compPushforwardAlgebraMap B S hS (compPushforwardAlgebraMap B S hS α f) k =
      compPushforwardAlgebraMap B S hS α f' := by
  rw [← compPushforwardAlgebraMap_comp]
  exact compPushforwardAlgebraMap_congr B S hS α ((Over.comp_left _ _ _ _ _).trans h)

/-! ### The covering of the base-changed charts -/

section Covering

variable {T : BigFppfOver B S hS} (x : X.1.obj (op T)) (R : Sieve T)

/-- The members of a sieve on `T`, as an index type. -/
abbrev SieveIndex := Σ Z : BigFppfOver B S hS, {f : Z ⟶ T // R f}

/-- The member `Z ⟶ T` of the sieve with the restricted point, as an algebraic space over `X`. -/
def sieveFamily (i : SieveIndex B S hS R) : Over X :=
  specPointOver B S hS i.1 (X.1.map i.2.1.op x)

/-- The morphism over `X` attached to a member of the sieve. -/
def sieveFamilyHom (i : SieveIndex B S hS R) :
    sieveFamily B S hS x R i ⟶ specPointOver B S hS T x :=
  specPointOverMap B S hS i.2.1 x

/-- The structure morphism of `AlgebraicGeometry.Space.sieveFamily` to `X` is relatively
representable. -/
theorem relativelyRepresentable_sieveFamily (i : SieveIndex B S hS R) :
    yoneda.relativelyRepresentable (sieveFamily B S hS x R i).hom.hom :=
  relativelyRepresentable_specPointOver B S hS i.1 (X.1.map i.2.1.op x)

/-- **The base changes to a chart of a covering sieve cover.**  For a covering sieve `R` of `T`
and a point `x ∈ X(T)`, the base changes to an étale chart `V` of `X` of the morphisms
`specPointOver Z (x|_Z) ⟶ specPointOver T x` attached to the members of `R` generate a covering
sieve of `T ×_X V`: it contains the pullback of `R` along the projection `T ×_X V ⟶ T`. -/
theorem generate_chartPresieve_pointOver_mem (hR : R ∈ BigFppfOver.topology B S hS T)
    (V : SmallEtale B S hS X.1) :
    Sieve.generate (chartPresieve B S hS (relativelyRepresentable_specPointOver B S hS T x)
      (relativelyRepresentable_sieveFamily B S hS x R) (sieveFamilyHom B S hS x R) V) ∈
      BigFppfOver.topology B S hS
        ((relativelyRepresentable_specPointOver B S hS T x).pullback V.obj.hom) := by
  let hP := relativelyRepresentable_specPointOver B S hS T x
  let fst' : hP.pullback V.obj.hom ⟶ T := yoneda.preimage (hP.fst V.obj.hom)
  have hfst : yoneda.map fst' = hP.fst V.obj.hom := yoneda.map_preimage _
  refine GrothendieckTopology.superset_covering _ ?_
    (GrothendieckTopology.pullback_stable _ fst' hR)
  intro W h hh
  let i : SieveIndex B S hS R := ⟨W, h ≫ fst', hh⟩
  let hQ := relativelyRepresentable_sieveFamily B S hS x R i
  have hcond : 𝟙 (yoneda.obj W) ≫ (sieveFamily B S hS x R i).hom.hom =
      yoneda.map (h ≫ hP.snd V.obj.hom) ≫ V.obj.hom := by
    show 𝟙 (yoneda.obj W) ≫ yonedaEquiv.symm (X.1.map (h ≫ fst').op x) = _
    rw [Category.id_comp, yonedaEquiv_symm_map, Quiver.Hom.unop_op, Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc, hfst]
    exact congrArg (yoneda.map h ≫ ·) (hP.w V.obj.hom)
  let l : W ⟶ hQ.pullback V.obj.hom := hQ.lift (𝟙 _) (h ≫ hP.snd V.obj.hom) hcond
  refine ⟨_, l, smallBaseChangeOverMap B S hS (sieveFamilyHom B S hS x R i) hQ hP V,
    Presieve.ofArrows.mk i, ?_⟩
  have hl₁ : yoneda.map l ≫ hQ.fst V.obj.hom = 𝟙 _ := hQ.lift_fst _ _ _
  have hl₂ : l ≫ hQ.snd V.obj.hom = h ≫ hP.snd V.obj.hom := hQ.lift_snd _ _ _
  refine hP.hom_ext ?_ ?_
  · rw [Functor.map_comp, Category.assoc, yoneda_map_smallBaseChangeOverMap_fst,
      ← Category.assoc, hl₁]
    show 𝟙 (yoneda.obj W) ≫ yoneda.map (h ≫ fst') = _
    rw [Category.id_comp, Functor.map_comp, hfst]
  · rw [Category.assoc, smallBaseChangeOverMap_snd, hl₂]

/-- **Descent of morphisms of algebras into the direct image of a point along a covering
sieve.** -/
theorem existsUnique_pointOver_lift (hR : R ∈ BigFppfOver.topology B S hS T)
    (β : ∀ i : SieveIndex B S hS R, A ⟶ pushforwardAlgebra B S hS (sieveFamily B S hS x R i))
    (hβ : AlgebraMapsCompatible B S hS (sieveFamilyHom B S hS x R) β) :
    ∃! α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x),
      ∀ i, α ≫ pushforwardAlgebraMap B S hS (sieveFamilyHom B S hS x R i) = β i :=
  existsUnique_pushforwardAlgebra_lift_of_covering B S hS
    (relativelyRepresentable_specPointOver B S hS T x)
    (relativelyRepresentable_sieveFamily B S hS x R) (sieveFamilyHom B S hS x R)
    (generate_chartPresieve_pointOver_mem B S hS x R hR) hβ

/-- Uniqueness in `AlgebraicGeometry.Space.existsUnique_pointOver_lift`. -/
theorem specPointOver_hom_ext (hR : R ∈ BigFppfOver.topology B S hS T)
    {α α' : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)}
    (h : ∀ i, α ≫ pushforwardAlgebraMap B S hS (sieveFamilyHom B S hS x R i) =
      α' ≫ pushforwardAlgebraMap B S hS (sieveFamilyHom B S hS x R i)) : α = α' :=
  hom_ext_of_covering B S hS (relativelyRepresentable_specPointOver B S hS T x)
    (relativelyRepresentable_sieveFamily B S hS x R) (sieveFamilyHom B S hS x R)
    (generate_chartPresieve_pointOver_mem B S hS x R hR) h

end Covering

/-! ### The sheaf property -/

section Sheaf

variable {T : BigFppfOver B S hS} {R : Sieve T}
  (p : Presieve.FamilyOfElements (relativeSpecPoints B S hS A) R.arrows) (x : X.1.obj (op T))
  (hxf : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ T) (hf : R f),
    X.1.map f.op x = (relativeSpecPointsEquiv B S hS A Z (p f hf)).pt)

/-- Two morphisms over `X` out of a representable algebraic space whose composites with
`specPointOverMap` agree come from morphisms of the site with equal composites. -/
theorem exists_left_eq_of_comp_pointOverMap_eq {W Z₁ Z₂ : BigFppfOver B S hS}
    {z : yonedaSpace B S hS W ⟶ X} {f₁ : Z₁ ⟶ T} {f₂ : Z₂ ⟶ T}
    (r : Over.mk z ⟶ specPointOver B S hS Z₁ (X.1.map f₁.op x))
    (s : Over.mk z ⟶ specPointOver B S hS Z₂ (X.1.map f₂.op x))
    (hrs : r ≫ specPointOverMap B S hS f₁ x = s ≫ specPointOverMap B S hS f₂ x) :
    ∃ (a : W ⟶ Z₁) (b : W ⟶ Z₂), r.left = ObjectProperty.homMk (yoneda.map a) ∧
      s.left = ObjectProperty.homMk (yoneda.map b) ∧ a ≫ f₁ = b ≫ f₂ := by
  obtain ⟨a, ha⟩ := yoneda.map_surjective r.left.hom
  obtain ⟨b, hb⟩ := yoneda.map_surjective s.left.hom
  refine ⟨a, b, ObjectProperty.hom_ext _ ha.symm, ObjectProperty.hom_ext _ hb.symm, ?_⟩
  have h := congrArg (fun k => k.left.hom) hrs
  simp only [Over.comp_left, specPointOverMap_left, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom] at h
  rw [← ha, ← hb, ← Functor.map_comp, ← Functor.map_comp] at h
  exact yoneda.map_injective h

omit hxf in
/-- Compatibility of a family of points of the relative spectrum, read through
`AlgebraicGeometry.Space.relativeSpecPointsEquiv`. -/
theorem map_eq_map_of_compatible (hp : p.Compatible) {W Z₁ Z₂ : BigFppfOver B S hS}
    {f₁ : Z₁ ⟶ T} {f₂ : Z₂ ⟶ T} (h₁ : R f₁) (h₂ : R f₂) (a : W ⟶ Z₁) (b : W ⟶ Z₂)
    (hab : a ≫ f₁ = b ≫ f₂) :
    (relativeSpecPointsEquiv B S hS A Z₁ (p f₁ h₁)).map B S hS a =
      (relativeSpecPointsEquiv B S hS A Z₂ (p f₂ h₂)).map B S hS b := by
  rw [← relativeSpecPointsEquiv_map, ← relativeSpecPointsEquiv_map]
  exact congrArg (relativeSpecPointsEquiv B S hS A W) (hp a b h₁ h₂ hab)

/-- The family of morphisms of algebras of a compatible family of points is compatible. -/
theorem algebraMapsCompatible_of_eq (hp : p.Compatible)
    (β : ∀ i : SieveIndex B S hS R, A ⟶ pushforwardAlgebra B S hS (sieveFamily B S hS x R i))
    (hβ : ∀ i, β i = compPushforwardAlgebraMap B S hS
        (relativeSpecPointsEquiv B S hS A i.1 (p i.2.1 i.2.2)).hom
        (specPointOverEq B S hS (hxf i.2.1 i.2.2))) :
    AlgebraMapsCompatible B S hS (sieveFamilyHom B S hS x R) β := by
  intro i j W z r s hrs
  obtain ⟨a, b, ha, hb, hab⟩ := exists_left_eq_of_comp_pointOverMap_eq B S hS x r s hrs
  have key : ∀ (k : SieveIndex B S hS R) {W : BigFppfOver B S hS} {z : yonedaSpace B S hS W ⟶ X}
      (r : Over.mk z ⟶ sieveFamily B S hS x R k), compPushforwardAlgebraMap B S hS (β k) r =
        compPushforwardAlgebraMap B S hS
          (relativeSpecPointsEquiv B S hS A k.1 (p k.2.1 k.2.2)).hom
          (r ≫ specPointOverEq B S hS (hxf k.2.1 k.2.2)) := fun k _ _ r => by
    rw [hβ k]
    exact (compPushforwardAlgebraMap_comp B S hS _ _ r).symm
  obtain ⟨E, hE, hE'⟩ := RelativeSpecPoint.exists_comp_hom_eq_map B S hS
    (relativeSpecPointsEquiv B S hS A i.1 (p i.2.1 i.2.2)) (hxf i.2.1 i.2.2) r a ha
  obtain ⟨F, hF, hF'⟩ := RelativeSpecPoint.exists_comp_hom_eq_map B S hS
    (relativeSpecPointsEquiv B S hS A j.1 (p j.2.1 j.2.2)) (hxf j.2.1 j.2.2) s b hb
  exact (compPushforwardAlgebraMap_def B S hS (β i) r).symm.trans
    ((key i r).trans (hE'.trans ((RelativeSpecPoint.comp_hom_eq_of_eq B S hS
      (map_eq_map_of_compatible B S hS p hp i.2.2 j.2.2 a b hab) E F (hE.trans hF.symm)).trans
        (hF'.symm.trans (((key j s).symm.trans (compPushforwardAlgebraMap_def B S hS (β j) s)))))))

/-- The point of the relative spectrum glued from `x` and a morphism `α` whose composites with
the `specPointOverMap` are the family restricts to the family. -/
theorem map_mk_eq_of_comp_eq
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x))
    {Z : BigFppfOver B S hS} (f : Z ⟶ T) (hf : R f)
    (hα : compPushforwardAlgebraMap B S hS α (specPointOverMap B S hS f x) =
      compPushforwardAlgebraMap B S hS (relativeSpecPointsEquiv B S hS A Z (p f hf)).hom
        (specPointOverEq B S hS (hxf f hf))) :
    RelativeSpecPoint.map B S hS f (⟨x, α⟩ : RelativeSpecPoint B S hS A T) =
      relativeSpecPointsEquiv B S hS A Z (p f hf) := by
  rw [RelativeSpecPoint.map_mk]
  refine RelativeSpecPoint.ext_of_comp B S hS
    (p := ⟨X.1.map f.op x, compPushforwardAlgebraMap B S hS α (specPointOverMap B S hS f x)⟩)
    (hxf f hf).symm ?_
  refine (congrArg (fun γ => compPushforwardAlgebraMap B S hS γ
    (specPointOverEq B S hS (hxf f hf).symm)) hα).trans ?_
  exact (compPushforwardAlgebraMap_comp_of_left B S hS _ _ _ (𝟙 _) rfl).trans
    (compPushforwardAlgebraMap_id B S hS _)

/-- **Uniqueness of the amalgamation**: a point of the relative spectrum over `T` restricting to
the family is the one glued from `x` and `α`. -/
theorem eq_mk_of_map_eq (hR : R ∈ BigFppfOver.topology B S hS T)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x))
    (hα : ∀ i : SieveIndex B S hS R,
      compPushforwardAlgebraMap B S hS α (sieveFamilyHom B S hS x R i) =
        compPushforwardAlgebraMap B S hS
          (relativeSpecPointsEquiv B S hS A i.1 (p i.2.1 i.2.2)).hom
          (specPointOverEq B S hS (hxf i.2.1 i.2.2)))
    (q : RelativeSpecPoint B S hS A T) (hqx : x = q.pt)
    (hq : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ T) (hf : R f),
      q.map B S hS f = relativeSpecPointsEquiv B S hS A Z (p f hf)) :
    q = ⟨x, α⟩ := by
  refine RelativeSpecPoint.ext_of_comp B S hS (p' := ⟨x, α⟩) hqx ?_
  show compPushforwardAlgebraMap B S hS q.hom (specPointOverEq B S hS hqx) = α
  refine specPointOver_hom_ext B S hS x R hR fun i => ?_
  rw [← compPushforwardAlgebraMap_def, ← compPushforwardAlgebraMap_def, hα i]
  have h₁ : X.1.map i.2.1.op x = (q.map B S hS i.2.1).pt := by
    rw [RelativeSpecPoint.map_pt, hqx]
  refine (compPushforwardAlgebraMap_comp_of_left B S hS _ (specPointOverEq B S hS hqx)
    (sieveFamilyHom B S hS x R i)
    (specPointOverEq B S hS h₁ ≫ specPointOverMap B S hS i.2.1 q.pt) ?_).trans ?_
  · show (specPointOverMap B S hS i.2.1 x).left ≫ 𝟙 _ =
      (specPointOverEq B S hS h₁ ≫ specPointOverMap B S hS i.2.1 q.pt).left
    show (ObjectProperty.homMk (yoneda.map i.2.1) :
        yonedaSpace B S hS i.1 ⟶ yonedaSpace B S hS T) ≫ 𝟙 _ =
      𝟙 _ ≫ (ObjectProperty.homMk (yoneda.map i.2.1) :
        yonedaSpace B S hS i.1 ⟶ yonedaSpace B S hS T)
    rw [Category.comp_id, Category.id_comp]
  · refine (compPushforwardAlgebraMap_comp B S hS q.hom (specPointOverMap B S hS i.2.1 q.pt)
      (specPointOverEq B S hS h₁)).trans ?_
    exact RelativeSpecPoint.comp_hom_eq_of_eq B S hS (hq i.2.1 i.2.2) _ _ rfl

end Sheaf

/-- **The functor of points of the relative spectrum of `𝒜` is an fppf sheaf.** -/
theorem isSheaf_relativeSpecPoints (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (relativeSpecPoints B S hS A) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR p hp
  have hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).1 X.2.isSheaf
  obtain ⟨x, hx, hxu⟩ := hX R hR _ (hp.map (relativeSpecPointsπ B S hS A))
  have hxf : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ T) (hf : R f),
      X.1.map f.op x = (relativeSpecPointsEquiv B S hS A Z (p f hf)).pt := fun Z f hf =>
    (hx f hf).trans (relativeSpecPointsπ_app B S hS A Z (p f hf))
  obtain ⟨β, hβ⟩ : ∃ β : ∀ i : SieveIndex B S hS R,
      A ⟶ pushforwardAlgebra B S hS (sieveFamily B S hS x R i),
      ∀ i, β i = compPushforwardAlgebraMap B S hS
        (relativeSpecPointsEquiv B S hS A i.1 (p i.2.1 i.2.2)).hom
        (specPointOverEq B S hS (hxf i.2.1 i.2.2)) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα, -⟩ := existsUnique_pointOver_lift B S hS x R hR β
    (algebraMapsCompatible_of_eq B S hS p x hxf hp β hβ)
  have hα' : ∀ i : SieveIndex B S hS R,
      compPushforwardAlgebraMap B S hS α (sieveFamilyHom B S hS x R i) =
        compPushforwardAlgebraMap B S hS
          (relativeSpecPointsEquiv B S hS A i.1 (p i.2.1 i.2.2)).hom
          (specPointOverEq B S hS (hxf i.2.1 i.2.2)) := fun i =>
    (compPushforwardAlgebraMap_def B S hS α _).trans ((hα i).trans (hβ i))
  refine ⟨(relativeSpecPointsEquiv B S hS A T).symm ⟨x, α⟩, fun Z f hf => ?_, fun t ht => ?_⟩
  · apply (relativeSpecPointsEquiv B S hS A Z).injective
    rw [relativeSpecPointsEquiv_map, Equiv.apply_symm_apply]
    exact map_mk_eq_of_comp_eq B S hS p x hxf α f hf (hα' ⟨Z, f, hf⟩)
  · apply (relativeSpecPointsEquiv B S hS A T).injective
    rw [Equiv.apply_symm_apply]
    have htx : x = (relativeSpecPointsEquiv B S hS A T t).pt :=
      (hxu _ (ht.map (relativeSpecPointsπ B S hS A))).symm.trans
        (relativeSpecPointsπ_app B S hS A T t)
    refine eq_mk_of_map_eq B S hS p x hxf hR α hα' _ htx fun Z f hf => ?_
    rw [← relativeSpecPointsEquiv_map]
    exact congrArg (relativeSpecPointsEquiv B S hS A Z) (ht f hf)

end AlgebraicGeometry.Space

end
