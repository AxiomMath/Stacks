module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic

/-!
# When a morphism of quotient stacks is a gerbe

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B`, and let `[f] : [U/R] ⟶ [U'/R']` be the induced morphism of quotient
stacks of Stacks 046Q. This file proves that `[f]` makes `[U/R]` a gerbe over `[U'/R']` as soon
as `f : U ⟶ U'` and `R ⟶ R'|_U` are surjective as maps of fppf sheaves, where `R'|_U` is the
restriction of `R'` to `U` along `f`.

The same criterion is also proved for the second canonical arrow of Stacks 044R, the structure
arrow `[U/R] ⟶ B` to the base: it makes `[U/R]` a gerbe over `B` as soon as `U ⟶ B` is a
surjective map of fppf sheaves and any two local points of `U` with the same image in `B` are
joined by an arrow of `R`.

"Gerbe over `[U'/R']`" is `CategoryTheory.IsGerbeOver` for the projection of the quotient stack
`[U'/R']` to the big fppf site: local essential surjectivity on objects, and local fullness on
arrows lying over an identity of the site.

Surjectivity of `R ⟶ R'|_U` is spelled out rather than packaged as a map of sheaves: for any two
local points `a, b` of `U` over a test object `T` and any arrow `r'` of `R'` from `f ∘ a` to
`f ∘ b`, there is a covering of `T` over which `r'` restricts to the image of an arrow `r` of `R`
from `a` to `b`. This is local surjectivity of the map from `R` to the fibre product
`(U ×_B U) ×_{U' ×_B U'} R'`.

## Main results

* `AlgebraicGeometry.Stack.isGerbeOver_quotientStackMap`: `[f]` is a gerbe when `U ⟶ U'` and
  `R ⟶ R'|_U` are surjective maps of fppf sheaves.
* `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase`,
  `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_of_locallyFull` and
  `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_of_isIso`: the structure arrow
  `[U/R] ⟶ B` is a gerbe, in general, when points with the same image in `B` are joined by an
  arrow of `R` only after a covering, and when `U ⟶ B` is an isomorphism.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06PE](https://stacks.math.columbia.edu/tag/06PE)
-/

@[expose] public section

open CategoryTheory

universe u uP uX uY uC vP vX vY vC

namespace AlgebraicGeometry.Stack

set_option backward.isDefEq.respectTransparency false

private theorem isGerbeOver_of_locallyEssentiallySurjective_precomp
    {P0 : Type uP} [Category.{vP} P0] {X0 : Type uX} [Category.{vX} X0]
    {Y0 : Type uY} [Category.{vY} Y0] {C0 : Type uC} [Category.{vC} C0]
    (J : GrothendieckTopology C0) (q : Y0 ⥤ C0)
    (A : P0 ⥤ X0) (F : X0 ⥤ Y0)
    (hA : ∀ {U : C0} (x : X0), (F ⋙ q).obj x = U →
      ∃ R ∈ J U, ∀ ⦃V : C0⦄ (i : V ⟶ U), R i →
        ∃ p : P0, ∃ ψ : A.obj p ⟶ x, (F ⋙ q).IsHomLift i ψ)
    (hB : IsGerbeOver J q (A ⋙ F))
    (hF : (F ⋙ q).IsFiberedInGroupoids) : IsGerbeOver J q F := by
  refine ⟨hB.base_isFiberedInGroupoids, hF, ?_, ?_⟩
  · intro U y hy
    obtain ⟨R, hR, hcov⟩ := hB.locally_essSurj y hy
    refine ⟨R, hR, fun V i hi => ?_⟩
    obtain ⟨p, ψ, hψ⟩ := hcov i hi
    exact ⟨A.obj p, ψ, hψ⟩
  · intro U x x' b hb
    have hx : (F ⋙ q).obj x = U := IsHomLift.domain_eq q (𝟙 U) b
    have hx' : (F ⋙ q).obj x' = U := IsHomLift.codomain_eq q (𝟙 U) b
    obtain ⟨R, hR, hcov⟩ := hA x hx
    obtain ⟨R', hR', hcov'⟩ := hA x' hx'
    refine J.exists_covering_of_refine (J.intersection_covering hR hR') ?_
    intro V i hi
    obtain ⟨p, ψ, hψ⟩ := hcov i hi.1
    obtain ⟨p', ψ', hψ'⟩ := hcov' i hi.2
    have : q.IsHomLift i (F.map ψ) :=
      (Functor.isHomLift_comp_iff F q i ψ).1 hψ
    have : q.IsHomLift i (F.map ψ') :=
      (Functor.isHomLift_comp_iff F q i ψ').1 hψ'
    have : q.IsHomLift (𝟙 U) b := hb
    have hpbase : q.obj (F.obj (A.obj p)) = V := IsHomLift.domain_eq q i (F.map ψ)
    have hp'base : q.obj (F.obj (A.obj p')) = V := IsHomLift.domain_eq q i (F.map ψ')
    have hsource : q.obj (F.obj (A.obj p)) = q.obj (F.obj (A.obj p')) :=
      hpbase.trans hp'base.symm
    have hcompat : eqToHom hsource ≫ q.map (F.map ψ') =
        q.map (F.map ψ ≫ b) := by
      rw [IsHomLift.fac' q i (F.map ψ'), q.map_comp,
        IsHomLift.fac' q i (F.map ψ), IsHomLift.fac' q (𝟙 U) b]
      simp [Category.assoc]
    obtain ⟨β, ⟨hβmap, hβfac⟩, -⟩ :=
      hB.base_isFiberedInGroupoids.unique_lift (F.map ψ') (F.map ψ ≫ b)
        (eqToHom hsource) hcompat
    have hβ : q.IsHomLift (𝟙 V) β :=
      IsHomLift.of_fac' q (𝟙 V) β hpbase hp'base (by simpa using hβmap)
    obtain ⟨R₂, hR₂, hloc⟩ := hB.locally_full β hβ
    refine ⟨R₂, hR₂, fun W j hj => ?_⟩
    obtain ⟨p₁, p₁', ξ, ξ', a, hξ, hξ', ha, hsquare⟩ := hloc j hj
    have : (F ⋙ q).IsHomLift j (A.map ξ) := (Functor.isHomLift_comp_iff A (F ⋙ q) j ξ).1 hξ
    have : (F ⋙ q).IsHomLift j (A.map ξ') := (Functor.isHomLift_comp_iff A (F ⋙ q) j ξ').1 hξ'
    have haA : (F ⋙ q).IsHomLift (𝟙 W) (A.map a) :=
      (Functor.isHomLift_comp_iff A (F ⋙ q) (𝟙 W) a).1 ha
    refine ⟨A.obj p₁, A.obj p₁', A.map ξ ≫ ψ, A.map ξ' ≫ ψ', A.map a,
      IsHomLift.comp (F ⋙ q) j i (A.map ξ) ψ,
      IsHomLift.comp (F ⋙ q) j i (A.map ξ') ψ', haA, ?_⟩
    · dsimp only [Functor.comp_map] at hsquare
      simp only [Functor.map_comp]
      calc
        F.map (A.map a) ≫ F.map (A.map ξ') ≫ F.map ψ' =
            (F.map (A.map a) ≫ F.map (A.map ξ')) ≫ F.map ψ' :=
          (Category.assoc _ _ _).symm
        _ = (F.map (A.map ξ) ≫ β) ≫ F.map ψ' :=
          congrArg (fun m => m ≫ F.map ψ') hsquare
        _ = F.map (A.map ξ) ≫ (β ≫ F.map ψ') := Category.assoc _ _ _
        _ = F.map (A.map ξ) ≫ (F.map ψ ≫ b) :=
          congrArg (fun m => F.map (A.map ξ) ≫ m) hβfac
        _ = (F.map (A.map ξ) ≫ F.map ψ) ≫ b :=
          (Category.assoc (F.map (A.map ξ)) (F.map ψ) b).symm

private theorem isGerbeOver_of_verticalNatIso
    {X0 : Type uX} [Category.{vX} X0] {Y0 : Type uY} [Category.{vY} Y0]
    {C0 : Type uC} [Category.{vC} C0] (J : GrothendieckTopology C0)
    (q : Y0 ⥤ C0) (F F' : X0 ⥤ Y0) (hcomp : F ⋙ q = F' ⋙ q)
    (η : F ≅ F')
    (hvert : ∀ x, q.IsHomLift (𝟙 (q.obj (F.obj x))) (η.hom.app x))
    (hF : IsGerbeOver J q F) : IsGerbeOver J q F' := by
  have hbase (x : X0) : q.obj (F.obj x) = q.obj (F'.obj x) :=
    congrArg (fun K : X0 ⥤ C0 => K.obj x) hcomp
  refine ⟨hF.base_isFiberedInGroupoids, ?_, ?_, ?_⟩
  · rw [← hcomp]
    exact hF.isFiberedInGroupoids
  · intro U y hy
    obtain ⟨R, hR, hcov⟩ := hF.locally_essSurj y hy
    refine ⟨R, hR, fun V i hi => ?_⟩
    obtain ⟨x, ψ, hψ⟩ := hcov i hi
    have hxV : q.obj (F.obj x) = V := IsHomLift.domain_eq q i ψ
    have hηx : q.IsHomLift (𝟙 (q.obj (F.obj x))) (η.hom.app x) := hvert x
    have hηxInv0 : q.IsHomLift (𝟙 (q.obj (F.obj x))) (η.inv.app x) :=
      @IsHomLift.lift_id_inv _ _ _ _ q _ _ _ (η.app x) hηx
    have hxV' : q.obj (F'.obj x) = V := (hbase x).symm.trans hxV
    have hηxInv : q.IsHomLift (𝟙 (q.obj (F'.obj x))) (η.inv.app x) := by
      rwa [← hbase x]
    have : q.IsHomLift (𝟙 V) (η.inv.app x) := by
      rwa [← hxV']
    exact ⟨x, η.inv.app x ≫ ψ,
      by simpa using IsHomLift.comp q (𝟙 V) i (η.inv.app x) ψ⟩
  · intro U x x' b hb
    have hxU' : q.obj (F'.obj x) = U := IsHomLift.domain_eq q (𝟙 U) b
    have hx'U' : q.obj (F'.obj x') = U := IsHomLift.codomain_eq q (𝟙 U) b
    have hxU : q.obj (F.obj x) = U := (hbase x).trans hxU'
    have hx'U : q.obj (F.obj x') = U := (hbase x').trans hx'U'
    have hηx : q.IsHomLift (𝟙 U) (η.hom.app x) := hxU ▸ hvert x
    have hηx' : q.IsHomLift (𝟙 U) (η.hom.app x') := hx'U ▸ hvert x'
    have hbF : q.IsHomLift (𝟙 U) b := hb
    have hb' : q.IsHomLift (𝟙 U) (η.hom.app x ≫ b ≫ η.inv.app x') := by
      have := hηx
      have := hbF
      have : q.IsHomLift (𝟙 U) (η.inv.app x') :=
        @IsHomLift.lift_id_inv _ _ _ _ q U _ _ (η.app x') hηx'
      have h₂ := IsHomLift.comp q (𝟙 U) (𝟙 U)
        (η.hom.app x ≫ b) (η.inv.app x')
      simpa using h₂
    obtain ⟨R, hR, hcov⟩ :=
      hF.locally_full (η.hom.app x ≫ b ≫ η.inv.app x') hb'
    refine ⟨R, hR, fun V i hi => ?_⟩
    obtain ⟨x₁, x₁', ξ, ξ', a, hξ, hξ', ha, hsquare⟩ := hcov i hi
    have hξF' : (F' ⋙ q).IsHomLift i ξ := by simpa only [← hcomp] using hξ
    have hξ'F' : (F' ⋙ q).IsHomLift i ξ' := by simpa only [← hcomp] using hξ'
    have haF' : (F' ⋙ q).IsHomLift (𝟙 V) a := by simpa only [← hcomp] using ha
    refine ⟨x₁, x₁', ξ, ξ', a, hξF', hξ'F', haF', ?_⟩
    have hpost : η.hom.app x₁ ≫ (F'.map a ≫ F'.map ξ') ≫ η.inv.app x' =
        η.hom.app x₁ ≫ (F'.map ξ ≫ b) ≫ η.inv.app x' := by
      calc
      η.hom.app x₁ ≫ (F'.map a ≫ F'.map ξ') ≫ η.inv.app x' =
          (η.hom.app x₁ ≫ F'.map a) ≫ F'.map ξ' ≫ η.inv.app x' := by
            simp only [Category.assoc]
      _ = (F.map a ≫ η.hom.app x₁') ≫ F'.map ξ' ≫ η.inv.app x' := by
            rw [η.hom.naturality a]
      _ = (F.map a ≫ (η.hom.app x₁' ≫ F'.map ξ')) ≫ η.inv.app x' := by
            simp only [Category.assoc]
      _ = (F.map a ≫ (F.map ξ' ≫ η.hom.app x')) ≫ η.inv.app x' := by
            rw [η.hom.naturality ξ']
      _ = F.map a ≫ F.map ξ' := by simp [Category.assoc]
      _ = F.map ξ ≫ η.hom.app x ≫ b ≫ η.inv.app x' := hsquare
      _ = (η.hom.app x₁ ≫ F'.map ξ) ≫ b ≫ η.inv.app x' := by
            have hn := η.hom.naturality ξ
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ b ≫ η.inv.app x') hn
      _ = η.hom.app x₁ ≫ (F'.map ξ ≫ b) ≫ η.inv.app x' := by
            simp only [Category.assoc]
    have hunit1 : η.hom.app x₁ ≫ η.inv.app x₁ = 𝟙 _ := η.hom_inv_id_app x₁
    have hunit2 : η.hom.app x' ≫ η.inv.app x' = 𝟙 _ := η.hom_inv_id_app x'
    have hcancelLeft := congrArg (fun k => η.inv.app x₁ ≫ k) hpost
    have hcancelRight := congrArg (fun k => k ≫ η.hom.app x') hcancelLeft
    simpa [Category.assoc, hunit1, hunit2] using hcancelRight

open Opposite CategoryTheory.Pseudofunctor

private noncomputable abbrev presentation
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :=
  presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)

private noncomputable def arrowValue
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G : GroupoidInAlgebraicSpaces C S hS B}
    {x y : (presentation G).obj} (a : x ⟶ y) : G.arrows.obj.obj (op x.base) :=
  (G.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _ a.fiber).1

private lemma arrow_conjugate
    {D : Type uC} [Category.{vC} D] (G : Deformation.GroupoidInFunctors D) (T : D)
    {a a' b b' : G.Evaluation T} (ha : a = a') (hb : b' = b) (r : a' ⟶ b') :
    (G.evaluationArrowEquiv T _ _ (eqToHom ha ≫ r ≫ eqToHom hb)).1 =
      (G.evaluationArrowEquiv T _ _ r).1 := by
  cases ha; cases hb; simp

/-- The underlying section of an arrow is unchanged by conjugating with object
identifications, with the identification of the target split into two steps. -/
private lemma arrow_conjugate_assoc
    {D : Type uC} [Category.{vC} D] (G : Deformation.GroupoidInFunctors D) (T : D)
    {a a' b'' b' b : G.Evaluation T} (ha : a = a') (hb : b' = b'') (hb' : b'' = b)
    (r : a' ⟶ b') :
    (G.evaluationArrowEquiv T _ _ ((eqToHom ha ≫ r ≫ eqToHom hb) ≫ eqToHom hb')).1 =
      (G.evaluationArrowEquiv T _ _ r).1 := by
  cases ha; cases hb; cases hb'; simp

private lemma arrowValue_ext
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G : GroupoidInAlgebraicSpaces C S hS B}
    {x y : (presentation G).obj} (a b : x ⟶ y)
    (h : a.base = b.base) (hab : arrowValue a = arrowValue b) : a = b := by
  obtain ⟨ab, af⟩ := a
  obtain ⟨bb, bf⟩ := b
  dsimp at h
  subst bb
  have he : af = bf := (G.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _).injective
    (Subtype.ext hab)
  cases he
  rfl

private lemma arrowValue_map
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    {x y : (presentation G).obj} (a : x ⟶ y) :
    arrowValue ((quotientPointwiseMap f).map a) =
      f.toGroupoidHom.mapArrows.app (op x.base) (arrowValue a) := by
  let α := (quotientPointwiseMapData f).val
  obtain ⟨h, hh⟩ := (quotientPointwiseMapData f).property.2 a.base.op.toLoc
  change (H.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _
    ((α.app ⟨op x.base⟩).toFunctor.map a.fiber ≫
      (α.naturality a.base.op.toLoc).hom.toNatTrans.app y.fiber)).1 = _
  rw [hh]
  simp only [eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  change (H.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _
    ((α.app ⟨op x.base⟩).toFunctor.map a.fiber ≫ eqToHom _)).1 = _
  rw [Functor.congr_hom ((quotientPointwiseMapData f).property.1 x.base),
    arrow_conjugate_assoc]
  exact f.toGroupoidHom.evaluation_map_arrow _ _

private lemma isGerbeOver_of_vertical_full
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {D : Type uC} [Category.{vC} D] (J : GrothendieckTopology D)
    (q : Y ⥤ D) (F : X ⥤ Y)
    (hq : q.IsFiberedInGroupoids) (hp : (F ⋙ q).IsFiberedInGroupoids)
    (he : ∀ {U : D} (y : Y), q.obj y = U → ∃ R ∈ J U,
      ∀ ⦃V : D⦄ (i : V ⟶ U), R i → ∃ (x : X) (ψ : F.obj x ⟶ y), q.IsHomLift i ψ)
    (hf : ∀ {U : D} {x y : X} (b : F.obj x ⟶ F.obj y), q.IsHomLift (𝟙 U) b →
      ∃ a : x ⟶ y, F.map a = b) : IsGerbeOver J q F := by
  refine ⟨hq, hp, he, ?_⟩
  intro U x y b hb
  obtain ⟨a, ha⟩ := hf b hb
  let p := F ⋙ q
  have : p.IsFibered := hp.isFibered
  have hxa : p.IsHomLift (𝟙 U) a := by
    apply (Functor.isHomLift_comp_iff F q _ a).2
    rwa [ha]
  let x₀ : p.Fiber U := ⟨x, IsHomLift.domain_eq p (𝟙 U) a⟩
  let y₀ : p.Fiber U := ⟨y, IsHomLift.codomain_eq p (𝟙 U) a⟩
  let a₀ : x₀ ⟶ y₀ := ⟨a, hxa⟩
  refine ⟨⊤, J.top_mem U, fun V i _ => ?_⟩
  refine ⟨(p.pullbackFiber x₀ i).1, (p.pullbackFiber y₀ i).1,
    Functor.IsPreFibered.pullbackMap x₀.2 i,
    Functor.IsPreFibered.pullbackMap y₀.2 i,
    (Functor.pullbackFiberHom a₀ i).1, inferInstance, inferInstance,
    (Functor.pullbackFiberHom a₀ i).2, ?_⟩
  calc
    _ = F.map ((Functor.pullbackFiberHom a₀ i).1 ≫
        Functor.IsPreFibered.pullbackMap y₀.2 i) := (F.map_comp _ _).symm
    _ = F.map (Functor.IsPreFibered.pullbackMap x₀.2 i ≫ a) :=
      congrArg (fun m => F.map m) (Functor.pullbackFiberHom_fac a₀ i)
    _ = _ := by rw [F.map_comp, ha]

private lemma locally_essSurj_presentation
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U : BigFppfOver C S hS} (x : (quotientStack G).obj)
    (hx : (quotientStack G).p.obj x = U) :
    ∃ R ∈ BigFppfOver.topology C S hS U,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ U), R i →
        ∃ (a : (presentation G).obj) (φ : (pointwiseToQuotientStack G).obj a ⟶ x),
          (quotientStack G).p.IsHomLift i φ := by
  let q := (quotientStack G).p
  let x₀ : q.Fiber U := ⟨x, hx⟩
  obtain ⟨R, hR, hr⟩ := essImage_toQuotientStack G U x₀
  refine ⟨R, hR, fun V i hi => ?_⟩
  obtain ⟨a, ⟨e⟩⟩ := hr hi
  refine ⟨(quotientPrestackEquivalence G).inverse.obj a.1,
    e.hom.1 ≫ Functor.IsPreFibered.pullbackMap x₀.2 i, ?_⟩
  have := e.hom.2
  simpa only [Category.id_comp] using IsHomLift.comp q (𝟙 V) i e.hom.1
    (Functor.IsPreFibered.pullbackMap x₀.2 i)

private lemma isGerbeOver_presentation
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsGerbeOver (BigFppfOver.topology C S hS)
      (quotientStack G).p (pointwiseToQuotientStack G) := by
  apply isGerbeOver_of_vertical_full
  · exact isFiberedInGroupoids_quotientStack G
  · rw [(isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq]
    exact isFiberedInGroupoids_presheafOfGroupoids _
  · exact locally_essSurj_presentation G
  · intro U x y b hb
    let p := (quotientPrestack G).p
    let q := (quotientStack G).p
    let c := (isFibredOneMorphism_toQuotientStack G).comp_eq
    have hx : p.obj ((quotientPrestackEquivalence G).functor.obj x) = U :=
      (congrArg (fun k => k.obj ((quotientPrestackEquivalence G).functor.obj x)) c).symm.trans
        (IsHomLift.domain_eq q (𝟙 U) b)
    have hy : p.obj ((quotientPrestackEquivalence G).functor.obj y) = U :=
      (congrArg (fun k => k.obj ((quotientPrestackEquivalence G).functor.obj y)) c).symm.trans
        (IsHomLift.codomain_eq q (𝟙 U) b)
    let x₀ : p.Fiber U := ⟨(quotientPrestackEquivalence G).functor.obj x, hx⟩
    let y₀ : p.Fiber U := ⟨(quotientPrestackEquivalence G).functor.obj y, hy⟩
    let b₀ : (Functor.fiberFunctorOfCompEq c U).obj x₀ ⟶
        (Functor.fiberFunctorOfCompEq c U).obj y₀ := ⟨b, hb⟩
    obtain ⟨a, ha⟩ := (fullyFaithful_fiberFunctor_toQuotientStack G U).some.map_surjective b₀
    exact ⟨(quotientPrestackEquivalence G).inverse.map a.1, congrArg Subtype.val ha⟩

private lemma pointwiseMap_obj_fiber
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H) (x : (presentation G).obj) :
    ((quotientPointwiseMap f).obj x).fiber =
      f.toGroupoidHom.mapObjects.app (op x.base) x.fiber := by
  change ((quotientPointwiseMapData f).val.app ⟨op x.base⟩).toFunctor.obj _ = _
  rw [(quotientPointwiseMapData f).property.1]
  rfl

private lemma arrowValue_map_cartesian_comp
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    {x y : (presentation G).obj}
    (b : (quotientPointwiseMap f).obj x ⟶
      (quotientPointwiseMap f).obj y)
    {V : BigFppfOver C S hS} (i : V ⟶ x.base) :
    arrowValue ((quotientPointwiseMap f).map
        (CoGrothendieck.cartesianLift x.fiber i) ≫ b) =
      H.arrows.obj.map i.op (arrowValue b) := by
  let α := (quotientPointwiseMapData f).val
  obtain ⟨h, hh⟩ := (quotientPointwiseMapData f).property.2 i.op.toLoc
  change (H.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _
    (((α.app ⟨op V⟩).toFunctor.map (𝟙 _) ≫
      (α.naturality i.op.toLoc).hom.toNatTrans.app x.fiber) ≫
      (Deformation.evaluationMap H.toGroupoidInFunctors i.op).map b.fiber ≫
      ((evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'.mapComp b.base.op.toLoc i.op.toLoc).inv.toNatTrans.app
          ((quotientPointwiseMap f).obj y).fiber)).1 = _
  simp only [Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
  rw [hh, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToIso.hom, Cat.eqToHom_app]
  change (H.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _
    (eqToHom _ ≫ (Deformation.evaluationMap H.toGroupoidInFunctors i.op).map b.fiber ≫
      eqToHom _)).1 = _
  rw [arrow_conjugate]
  exact Deformation.evaluationMap_map_arrow _ _ _

private lemma isGerbeOver_pointwise
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hobj : Presheaf.IsLocallySurjective
      (BigFppfOver.topology C S hS) f.toGroupoidHom.mapObjects)
    (harr : ∀ (T : BigFppfOver C S hS)
      (a b : G.objects.obj.obj (op T)) (r' : H.arrows.obj.obj (op T)),
      H.source.hom.app (op T) r' = f.toGroupoidHom.mapObjects.app (op T) a →
      H.target.hom.app (op T) r' = f.toGroupoidHom.mapObjects.app (op T) b →
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ r : G.arrows.obj.obj (op V),
            G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op b ∧
            f.toGroupoidHom.mapArrows.app (op V) r = H.arrows.obj.map i.op r') :
    IsGerbeOver (BigFppfOver.topology C S hS)
      (presentation H).p (quotientPointwiseMap f).toFunctor := by
  let F := quotientPointwiseMap f
  let p := (presentation G).p
  let q := (presentation H).p
  have hp : (F.toFunctor ⋙ q).IsFiberedInGroupoids := by
    rw [F.w]
    exact isFiberedInGroupoids_presheafOfGroupoids _
  refine ⟨isFiberedInGroupoids_presheafOfGroupoids _, hp, ?_, ?_⟩
  · intro U y hy
    change y.base = U at hy
    subst U
    refine ⟨Presheaf.imageSieve f.toGroupoidHom.mapObjects y.fiber,
      hobj.imageSieve_mem _, fun V i hi => ?_⟩
    obtain ⟨a, ha⟩ := hi
    let x : (presentation G).obj := ⟨V, a⟩
    have he : (F.obj x).fiber = H.objects.obj.map i.op y.fiber :=
      (pointwiseMap_obj_fiber f x).trans ha
    let ψ : F.obj x ⟶ y := ⟨i, eqToHom he⟩
    exact ⟨x, ψ, IsHomLift.map q ψ⟩
  · intro U x y b hb
    have hx : x.base = U := IsHomLift.domain_eq q (𝟙 U) b
    subst U
    let r' := arrowValue b
    have hs : H.source.hom.app (op x.base) r' =
        f.toGroupoidHom.mapObjects.app (op x.base) x.fiber :=
      (H.toGroupoidInFunctors.evaluationArrowEquiv (op x.base) _ _ b.fiber).2.1.trans
        (pointwiseMap_obj_fiber f x)
    have ht : H.target.hom.app (op x.base) r' =
        f.toGroupoidHom.mapObjects.app (op x.base)
          (G.objects.obj.map b.base.op y.fiber) := by
      have h := (H.toGroupoidInFunctors.evaluationArrowEquiv
        (op x.base) _ _ b.fiber).2.2
      change H.target.hom.app (op x.base) r' =
        H.objects.obj.map b.base.op (F.obj y).fiber at h
      rw [pointwiseMap_obj_fiber] at h
      exact h.trans (NatTrans.naturality_apply f.toGroupoidHom.mapObjects b.base.op y.fiber).symm
    obtain ⟨R, hR, hr⟩ := harr x.base x.fiber
      (G.objects.obj.map b.base.op y.fiber) r' hs ht
    refine ⟨R, hR, fun V i hi => ?_⟩
    obtain ⟨r, hrs, hrt, hrf⟩ := hr i hi
    let x₁ : (presentation G).obj := CoGrothendieck.domainCartesianLift x.fiber i
    let ξ : x₁ ⟶ x := CoGrothendieck.cartesianLift x.fiber i
    let l : x₁ ⟶ y := ⟨i ≫ b.base,
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _).symm
        ⟨r, hrs, hrt.trans (by
          change G.objects.obj.map i.op (G.objects.obj.map b.base.op y.fiber) =
            G.objects.obj.map (i ≫ b.base).op y.fiber
          rw [show (i ≫ b.base).op = b.base.op ≫ i.op from rfl]
          exact (G.objects.obj.map_comp_apply b.base.op i.op y.fiber).symm)⟩⟩
    have hξ : (F.toFunctor ⋙ q).IsHomLift i ξ := by
      rw [F.w]; exact IsHomLift.map p ξ
    have hl : F.map l = F.map ξ ≫ b := by
      apply arrowValue_ext
      · rfl
      · change arrowValue ((quotientPointwiseMap f).map l) =
          arrowValue ((quotientPointwiseMap f).map
            (CoGrothendieck.cartesianLift x.fiber i) ≫ b)
        rw [arrowValue_map, arrowValue_map_cartesian_comp]
        change f.toGroupoidHom.mapArrows.app (op V)
          ((G.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _
            ((G.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _).symm _)).1) = _
        simpa only [Equiv.apply_symm_apply] using hrf
    have := hb
    have := hξ
    obtain ⟨y₁, ξ', a, hξ', ha, he⟩ :=
      (IsGerbeOver.exists_fiberHom_iff_mem_imageSieve (U := x.base) (V := V)
        (f := i) (b := b) hp ξ).2 ⟨l, hl⟩
    exact ⟨x₁, y₁, ξ, ξ', a, hξ, hξ', ha, he⟩

/-- The induced morphism of quotient stacks `[f] : [U/R] ⟶ [U'/R']` makes `[U/R]` a gerbe over
`[U'/R']` as soon as `f : U ⟶ U'` and `R ⟶ R'|_U` are surjective maps of fppf sheaves: the first
hypothesis is local surjectivity of the map of object spaces, the second asks that an arrow of
`R'` between the images of two local points of `U` lift, after an fppf covering, to an arrow of
`R` between those points. -/
@[stacks 06PE]
public theorem isGerbeOver_quotientStackMap
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (f : GroupoidInAlgebraicSpaces.Hom G H)
    (hobj : Presheaf.IsLocallySurjective
      (BigFppfOver.topology C S hS) f.toGroupoidHom.mapObjects)
    (harr : ∀ (T : BigFppfOver C S hS)
      (a b : G.objects.obj.obj (Opposite.op T))
      (r' : H.arrows.obj.obj (Opposite.op T)),
      H.source.hom.app (Opposite.op T) r' =
        f.toGroupoidHom.mapObjects.app (Opposite.op T) a →
      H.target.hom.app (Opposite.op T) r' =
        f.toGroupoidHom.mapObjects.app (Opposite.op T) b →
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ r : G.arrows.obj.obj (Opposite.op V),
            G.source.hom.app (Opposite.op V) r =
              G.objects.obj.map i.op a ∧
            G.target.hom.app (Opposite.op V) r =
              G.objects.obj.map i.op b ∧
            f.toGroupoidHom.mapArrows.app (Opposite.op V) r =
              H.arrows.obj.map i.op r') :
    CategoryTheory.IsGerbeOver
      (BigFppfOver.topology C S hS)
      (quotientStack H).p
      (quotientStackMap f).toFunctor := by
  let q := (quotientStack H).p
  let F := quotientStackMap f
  let A := pointwiseToQuotientStackBased G
  let A' := pointwiseToQuotientStackBased H
  let P := quotientPointwiseMap f
  have hP : IsGerbeOver (BigFppfOver.topology C S hS)
      (A'.toFunctor ⋙ q) P.toFunctor := by
    rw [A'.w]
    exact isGerbeOver_pointwise f hobj harr
  have hPA := hP.comp (isGerbeOver_presentation H)
  let η := quotientStackMap_commutes f
  have hAF : IsGerbeOver (BigFppfOver.topology C S hS)
      q (A.toFunctor ⋙ F.toFunctor) := by
    apply isGerbeOver_of_verticalNatIso _ q (P.toFunctor ⋙ A'.toFunctor)
      (A.toFunctor ⋙ F.toFunctor)
      ((BasedFunctor.comp P A').w.trans (BasedFunctor.comp A F).w.symm)
      ((BasedNatTrans.forgetful _ _).mapIso η) _ hPA
    intro x
    change q.IsHomLift (𝟙 (q.obj ((BasedFunctor.comp P A').obj x)))
      (η.hom.toNatTrans.app x)
    rw [(BasedFunctor.comp P A').w_obj]
    exact η.hom.isHomLift' x
  refine isGerbeOver_of_locallyEssentiallySurjective_precomp _ q A.toFunctor F.toFunctor
    ?_ hAF ?_
  · intro U x hx
    rw [F.w] at hx ⊢
    exact locally_essSurj_presentation G x hx
  · rw [F.w]
    exact isFiberedInGroupoids_quotientStack G

/-! ### The structure arrow of a quotient stack to the base

The second canonical arrow of Stacks 044R, `[U/R] ⟶ B`, is a gerbe as soon as the object space
`U` locally surjects onto `B` and any two local points of `U` with the same image in `B` are
joined by an arrow of `R`. -/

private theorem toBase_obj_pointwise
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (x : (presentation G).obj) :
    (quotientStackToBase G).obj ((pointwiseToQuotientStack G).obj x) =
      ⟨x.base, Discrete.mk (G.objectsToBase.hom.app (op x.base) x.fiber)⟩ := by
  rw [quotientStackToBase, pointwiseToQuotientStack, Functor.comp_obj,
    quotientStackOfInvariant_obj_toQuotientStack]
  rfl

private theorem pointwiseToBase_comp_p
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
        (fibredCategory C S hS B.obj).val.p = (presentation G).p := by
  rw [Functor.assoc, (quotientStackToBase G).w,
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq]

private theorem pointwiseToBase_p_obj
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (z : (presentation G).obj) :
    (fibredCategory C S hS B.obj).val.p.obj
      ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).obj z) = z.base :=
  congrArg (fun k => k.obj z) (pointwiseToBase_comp_p G)

private lemma locally_essSurj_pointwiseToBase
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsurj : ∀ (T : BigFppfOver C S hS) (b : B.obj.obj (op T)),
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ a : G.objects.obj.obj (op V),
            G.objectsToBase.hom.app (op V) a = B.obj.map i.op b)
    {U : BigFppfOver C S hS} (y : (fibredCategory C S hS B.obj).val.obj)
    (hy : (fibredCategory C S hS B.obj).val.p.obj y = U) :
    ∃ R ∈ BigFppfOver.topology C S hS U,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ U), R i →
        ∃ (x : (presentation G).obj)
          (ψ : (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).obj x ⟶ y),
          (fibredCategory C S hS B.obj).val.p.IsHomLift i ψ := by
  change y.base = U at hy
  subst U
  obtain ⟨R, hR, hr⟩ := hsurj y.base y.fiber.as
  refine ⟨R, hR, fun V i hi => ?_⟩
  obtain ⟨a, ha⟩ := hr i hi
  refine ⟨⟨V, a⟩, ?_⟩
  have hobj : (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).obj
      (⟨V, a⟩ : (presentation G).obj) = ⟨V, Discrete.mk (B.obj.map i.op y.fiber.as)⟩ :=
    (toBase_obj_pointwise G ⟨V, a⟩).trans (congrArg (fun s => (⟨V, Discrete.mk s⟩ :
      (fibredCategory C S hS B.obj).val.obj)) ha)
  rw [hobj]
  let ψ : (⟨V, Discrete.mk (B.obj.map i.op y.fiber.as)⟩ :
      (fibredCategory C S hS B.obj).val.obj) ⟶ y := ⟨i, eqToHom rfl⟩
  exact ⟨ψ, IsHomLift.map (fibredCategory C S hS B.obj).val.p ψ⟩

/-- Assume that two points of the object space over a test object with the same image in `B`
become the source and the target of an arrow of the arrow space after an fppf covering. Then the
composite of the projection of Stacks 044R with the structure arrow satisfies the local fullness
clause of Stacks 06P1 (2)(b). -/
private lemma locally_vertical_full_pointwiseToBase
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hfull : ∀ (T : BigFppfOver C S hS) (a b : G.objects.obj.obj (op T)),
      G.objectsToBase.hom.app (op T) a = G.objectsToBase.hom.app (op T) b →
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ r : G.arrows.obj.obj (op V),
            G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op b)
    (T : BigFppfOver C S hS) (xf yf : G.objects.obj.obj (op T))
    (b : (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).obj
        (⟨T, xf⟩ : (presentation G).obj) ⟶
      (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).obj
        (⟨T, yf⟩ : (presentation G).obj))
    (hb : (fibredCategory C S hS B.obj).val.p.IsHomLift (𝟙 T) b) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
        ∃ (x₁ x₁' : (presentation G).obj)
          (ξ : x₁ ⟶ (⟨T, xf⟩ : (presentation G).obj))
          (ξ' : x₁' ⟶ (⟨T, yf⟩ : (presentation G).obj)) (a : x₁ ⟶ x₁'),
          ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
              (fibredCategory C S hS B.obj).val.p).IsHomLift i ξ ∧
            ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
              (fibredCategory C S hS B.obj).val.p).IsHomLift i ξ' ∧
            ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
              (fibredCategory C S hS B.obj).val.p).IsHomLift (𝟙 V) a ∧
            (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map a ≫
                (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ' =
              (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ ≫ b := by
  have hp : ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
      (fibredCategory C S hS B.obj).val.p).IsFiberedInGroupoids := by
    rw [pointwiseToBase_comp_p G]
    exact isFiberedInGroupoids_presheafOfGroupoids _
  have hfs : (fibredCategory C S hS B.obj).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection B.obj).IsFiberedInSets
  have hx := toBase_obj_pointwise G (⟨T, xf⟩ : (presentation G).obj)
  have hy := toBase_obj_pointwise G (⟨T, yf⟩ : (presentation G).obj)
  set b' := eqToHom hx.symm ≫ b ≫ eqToHom hy with hb'def
  have hb' : (fibredCategory C S hS B.obj).val.p.IsHomLift (𝟙 T) b' := by
    rwa [hb'def, IsHomLift.comp_eqToHom_lift_iff, IsHomLift.eqToHom_comp_lift_iff]
  have hbb : b'.base = 𝟙 T := by
    have h := IsHomLift.fac' (fibredCategory C S hS B.obj).val.p (𝟙 T) b'
    simp only [eqToHom_refl, Category.comp_id] at h
    exact h
  have hfib := Discrete.eq_of_hom b'.fiber
  have hfib' : G.objectsToBase.hom.app (op T) xf =
      B.obj.map b'.base.op (G.objectsToBase.hom.app (op T) yf) := hfib
  have hfib2 : G.objectsToBase.hom.app (op T) xf =
      G.objectsToBase.hom.app (op T) (G.objects.obj.map b'.base.op yf) :=
    hfib'.trans (NatTrans.naturality_apply G.objectsToBase.hom b'.base.op yf).symm
  obtain ⟨R, hR, hr⟩ := hfull T xf (G.objects.obj.map b'.base.op yf) hfib2
  refine ⟨R, hR, fun V i hi => ?_⟩
  obtain ⟨r, hrs, hrt⟩ := hr i hi
  let x₁ : (presentation G).obj :=
    CoGrothendieck.domainCartesianLift (⟨T, xf⟩ : (presentation G).obj).fiber i
  let ξ : x₁ ⟶ (⟨T, xf⟩ : (presentation G).obj) :=
    CoGrothendieck.cartesianLift (⟨T, xf⟩ : (presentation G).obj).fiber i
  let l : x₁ ⟶ (⟨T, yf⟩ : (presentation G).obj) := ⟨i ≫ b'.base,
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _).symm
      ⟨r, hrs, hrt.trans (by
        change G.objects.obj.map i.op (G.objects.obj.map b'.base.op yf) =
          G.objects.obj.map (i ≫ b'.base).op yf
        rw [show (i ≫ b'.base).op = b'.base.op ≫ i.op from rfl]
        exact (G.objects.obj.map_comp_apply b'.base.op i.op yf).symm)⟩⟩
  have hξ : ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
      (fibredCategory C S hS B.obj).val.p).IsHomLift i ξ := by
    rw [pointwiseToBase_comp_p G]
    exact IsHomLift.map (presentation G).p ξ
  have hlq : (fibredCategory C S hS B.obj).val.p.IsHomLift (i ≫ b'.base)
      ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map l) := by
    refine (Functor.isHomLift_comp_iff _ _ (i ≫ b'.base) _).1 ?_
    rw [pointwiseToBase_comp_p G]
    exact IsHomLift.map (presentation G).p l
  have hξq : (fibredCategory C S hS B.obj).val.p.IsHomLift i
      ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ) :=
    (Functor.isHomLift_comp_iff _ _ i _).1 hξ
  have hcompq : (fibredCategory C S hS B.obj).val.p.IsHomLift (i ≫ b'.base)
      ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ ≫ b) := by
    rw [hbb, Category.comp_id]
    have := hξq
    have := hb
    simpa only [Category.comp_id] using
      IsHomLift.comp (fibredCategory C S hS B.obj).val.p i (𝟙 T)
        ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ) b
  have hl : (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map l =
      (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor).map ξ ≫ b := by
    have := hlq
    have := hcompq
    exact Functor.IsFiberedInSets.hom_ext_of_isHomLift
      (fibredCategory C S hS B.obj).val.p (i ≫ b'.base) _ _
  have := hb
  have := hξ
  obtain ⟨y₁, ξ', a, hξ', ha, he⟩ :=
    (IsGerbeOver.exists_fiberHom_iff_mem_imageSieve (U := T) (V := V)
      (f := i) (b := b) hp ξ).2 ⟨l, hl⟩
  exact ⟨x₁, y₁, ξ, ξ', a, hξ, hξ', ha, he⟩

/-- Local surjectivity of `U ⟶ B` and local fullness make `[U/R] ⟶ B` a gerbe over `B`. -/
private theorem isGerbeOver_toBase_of_locallyFull
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsurj : ∀ (T : BigFppfOver C S hS) (b : B.obj.obj (op T)),
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ a : G.objects.obj.obj (op V),
            G.objectsToBase.hom.app (op V) a = B.obj.map i.op b)
    (hfull : ∀ (T : BigFppfOver C S hS) (a b : G.objects.obj.obj (op T)),
      G.objectsToBase.hom.app (op T) a = G.objectsToBase.hom.app (op T) b →
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ r : G.arrows.obj.obj (op V),
            G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op b) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p (quotientStackToBase G).toFunctor := by
  have hB : IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p
      (pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) := by
    have hp : ((pointwiseToQuotientStack G ⋙ (quotientStackToBase G).toFunctor) ⋙
        (fibredCategory C S hS B.obj).val.p).IsFiberedInGroupoids := by
      rw [pointwiseToBase_comp_p G]
      exact isFiberedInGroupoids_presheafOfGroupoids _
    refine ⟨(fibredCategory C S hS B.obj).property, hp,
      locally_essSurj_pointwiseToBase G hsurj, ?_⟩
    intro U x y b hb
    obtain ⟨xb, xf⟩ := x
    obtain ⟨yb, yf⟩ := y
    have hxU : xb = U :=
      (pointwiseToBase_p_obj G ⟨xb, xf⟩).symm.trans
        (IsHomLift.domain_eq (fibredCategory C S hS B.obj).val.p (𝟙 U) b)
    have hyU : yb = U :=
      (pointwiseToBase_p_obj G ⟨yb, yf⟩).symm.trans
        (IsHomLift.codomain_eq (fibredCategory C S hS B.obj).val.p (𝟙 U) b)
    subst hxU
    subst hyU
    exact locally_vertical_full_pointwiseToBase G hfull _ _ _ b hb
  refine isGerbeOver_of_locallyEssentiallySurjective_precomp _
    (fibredCategory C S hS B.obj).val.p (pointwiseToQuotientStack G)
    (quotientStackToBase G).toFunctor ?_ hB ?_
  · intro U x hx
    rw [(quotientStackToBase G).w] at hx ⊢
    exact locally_essSurj_presentation G x hx
  · rw [(quotientStackToBase G).w]
    exact isFiberedInGroupoids_quotientStack G

/-- The structure arrow `[U/R] ⟶ B` of Stacks 044R turns `[U/R]` into a gerbe over `B` as soon
as `U ⟶ B` is a surjective map of fppf sheaves and any two local points of `U` with the same
image in `B` are the source and the target of an arrow of `R`. -/
public theorem isGerbeOver_quotientStackToBase
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsurj : ∀ (T : BigFppfOver C S hS) (b : B.obj.obj (op T)),
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ a : G.objects.obj.obj (op V),
            G.objectsToBase.hom.app (op V) a = B.obj.map i.op b)
    (hfull : ∀ (T : BigFppfOver C S hS) (a b : G.objects.obj.obj (op T)),
      G.objectsToBase.hom.app (op T) a = G.objectsToBase.hom.app (op T) b →
      ∃ r : G.arrows.obj.obj (op T),
        G.source.hom.app (op T) r = a ∧ G.target.hom.app (op T) r = b) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p (quotientStackToBase G).toFunctor := by
  refine isGerbeOver_toBase_of_locallyFull G hsurj fun T a b hab =>
    ⟨⊤, (BigFppfOver.topology C S hS).top_mem T, fun V i _ => hfull V _ _ ?_⟩
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hab]

/-- The structure arrow `[U/R] ⟶ B` of Stacks 044R turns `[U/R]` into a gerbe over `B` as soon
as `U ⟶ B` is a surjective map of fppf sheaves and any two local points of `U` with the same image
in `B` become, after an fppf covering, the source and the target of an arrow of `R`. -/
public theorem isGerbeOver_quotientStackToBase_of_locallyFull
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsurj : ∀ (T : BigFppfOver C S hS) (b : B.obj.obj (op T)),
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ a : G.objects.obj.obj (op V),
            G.objectsToBase.hom.app (op V) a = B.obj.map i.op b)
    (hfull : ∀ (T : BigFppfOver C S hS) (a b : G.objects.obj.obj (op T)),
      G.objectsToBase.hom.app (op T) a = G.objectsToBase.hom.app (op T) b →
      ∃ R ∈ BigFppfOver.topology C S hS T,
        ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), R i →
          ∃ r : G.arrows.obj.obj (op V),
            G.source.hom.app (op V) r = G.objects.obj.map i.op a ∧
            G.target.hom.app (op V) r = G.objects.obj.map i.op b) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p (quotientStackToBase G).toFunctor :=
  isGerbeOver_toBase_of_locallyFull G hsurj hfull

/-- If the structure morphism `U ⟶ B` of the object space is an isomorphism then the structure
arrow `[U/R] ⟶ B` turns `[U/R]` into a gerbe over `B`. -/
public theorem isGerbeOver_quotientStackToBase_of_isIso
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (h : IsIso G.objectsToBase.hom) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p (quotientStackToBase G).toFunctor := by
  have hbij : ∀ T : (BigFppfOver C S hS)ᵒᵖ,
      Function.Bijective (G.objectsToBase.hom.app T) := fun T => by
    exact ConcreteCategory.bijective_of_isIso _
  refine isGerbeOver_quotientStackToBase G (fun T b => ?_) (fun T a b hab => ?_)
  · exact ⟨⊤, (BigFppfOver.topology C S hS).top_mem T, fun V i _ =>
      (hbij (op V)).2 (B.obj.map i.op b)⟩
  · obtain rfl := (hbij (op T)).1 hab
    let a' : G.toGroupoidInFunctors.Evaluation (op T) := a
    exact ⟨(G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a' a' (𝟙 a')).1,
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a' a' (𝟙 a')).2.1,
      (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) a' a' (𝟙 a')).2.2⟩

end AlgebraicGeometry.Stack

end
