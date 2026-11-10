module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Basic

/-!
# Strongly cartesian morphisms of quasi-coherent modules

A morphism of the category of quasi-coherent modules over a scheme `S`, fibred over the big
fppf category of `S`, is strongly cartesian exactly when the adjoint map from the pullback of
the target module to the source module is an isomorphism.

## Main results

* `Stacks.QCoh.isStronglyCartesian_iff`: the characterisation of the strongly cartesian
  arrows.

## Implementation notes

The morphism of schemes underlying an arrow is recovered from the hom-set description
`Stacks.QCoh.homEquivPullbackHom` of Stacks 04U2, and the comparison map is the pullback-hom
component of the same description; strong cartesianness is taken with respect to the
projection to the big fppf category of `S`.

Both directions go through the same calculation: an arrow is strongly cartesian precisely
when, for every quasi-coherent module `K` on the source scheme, composing with the comparison
map is a bijection from the morphisms out of the source module to the morphisms out of the
pullback of the target module. Applied to the pullback itself this produces an inverse of the
comparison map, and conversely the existence of an inverse supplies the unique factorisation
through the universal property.

## References

* [Stacks Project, Tag 04U3](https://stacks.math.columbia.edu/tag/04U3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A C : Object B S hS} (m : A ⟶ C)

/-- The base morphism recorded by `homEquivPullbackHom` is the image of the arrow under the
projection, up to the identification of the projection with the base. -/
private theorem base_eq (A C : Object B S hS) (m : A ⟶ C) :
    (homEquivPullbackHom A C m).1 =
      eqToHom ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj A).symm ≫
        (projection (B := B) (S := S) (hS := hS)).map m ≫
        eqToHom ((Classical.choice
          (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj C) := by
  classical
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let : Category (Object B S hS) := d.category
  simp [homEquivPullbackHom, projection, d, d.projection_map]

/-- The base morphism recorded by `homEquivPullbackHom` is the base morphism of the
corresponding `f`-map. -/
private theorem base_raw_eq (A C : Object B S hS) (m : A ⟶ C) :
    (homEquivPullbackHom A C m).1 =
      ((Equiv.cast ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type A C)) m).1 := by
  classical
  simp only [homEquivPullbackHom, Equiv.trans_apply, Equiv.sigmaCongrRight_apply]

/-- The base morphism of the `f`-map of an arrow is its image under the projection, up to the
identification of the projection with the base. -/
private theorem raw_base_eq_projection_map (A C : Object B S hS) (m : A ⟶ C) :
    ((Equiv.cast ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type A C)) m).1 =
      eqToHom ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj A).symm ≫
        (projection (B := B) (S := S) (hS := hS)).map m ≫
        eqToHom ((Classical.choice
          (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj C) :=
  (base_raw_eq A C m).symm.trans (base_eq A C m)

/-- An arrow lies over a morphism of the base exactly when its `f`-map has that morphism as base,
up to the identification of the projection with the base. -/
private theorem isHomLift_iff_raw_base_eq {X Y : Object B S hS}
    (h : (projection (B := B) (S := S) (hS := hS)).obj X ⟶
      (projection (B := B) (S := S) (hS := hS)).obj Y) (φ : X ⟶ Y) :
    (projection (B := B) (S := S) (hS := hS)).IsHomLift h φ ↔
      ((Equiv.cast ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type X Y)) φ).1 =
        eqToHom ((Classical.choice
          (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj X).symm ≫ h ≫
          eqToHom ((Classical.choice
            (exists_categoryData (B := B) (S := S) (hS := hS))).projection_obj Y) := by
  refine ⟨fun _ => (raw_base_eq_projection_map X Y φ).trans ?_, fun h' => ?_⟩
  · rw [← IsHomLift.eq_of_isHomLift (f := h) (φ := φ)]
  · let P := projection (B := B) (S := S) (hS := hS)
    have rX : P.obj X = X.base := (Classical.choice (exists_categoryData (B := B) (S := S)
      (hS := hS))).projection_obj X
    have rY : P.obj Y = Y.base := (Classical.choice (exists_categoryData (B := B) (S := S)
      (hS := hS))).projection_obj Y
    have key : eqToHom rX.symm ≫ P.map φ ≫ eqToHom rY = eqToHom rX.symm ≫ h ≫ eqToHom rY :=
      (raw_base_eq_projection_map X Y φ).symm.trans h'
    have hmap : P.map φ = h := (cancel_mono _).mp ((cancel_epi _).mp key)
    exact hmap ▸ Functor.IsHomLift.map φ

/-- The comparison map recorded by `homEquivPullbackHom` is adjoint to the `f`-map of the
corresponding morphism. -/
private theorem adjoint_eq (A C : Object B S hS) (m : A ⟶ C) :
    (Scheme.Modules.pullbackPushforwardAdjunction
      (Object.schemeMap (homEquivPullbackHom A C m).1)).homEquiv
        C.module A.module ((homEquivPullbackHom A C m).2) =
      ((Equiv.cast ((Classical.choice
        (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type A C)) m).2 := by
  classical
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let : Category (Object B S hS) := d.category
  let r := (Equiv.cast (d.hom_type A C)) m
  change (Scheme.Modules.pullbackPushforwardAdjunction
      (Object.schemeMap r.1)).homEquiv C.module A.module
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (Object.schemeMap r.1)).homEquiv C.module A.module).symm r.2) = r.2
  exact Equiv.apply_symm_apply _ _

/-- The `f`-map of an arrow is given by its base morphism and the adjoint of its comparison map. -/
private theorem cast_hom_eq_sigma (A C : Object B S hS) (m : A ⟶ C) :
    (Equiv.cast ((Classical.choice
      (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type A C)) m =
      ⟨(homEquivPullbackHom A C m).1,
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Object.schemeMap (homEquivPullbackHom A C m).1)).homEquiv
            C.module A.module (homEquivPullbackHom A C m).2⟩ :=
  Sigma.ext (base_raw_eq A C m).symm (heq_of_eq (adjoint_eq A C m).symm)

/-- If the adjoint of an `f`-map out of a pullback is an isomorphism, then every `f`-map over a
composite factors uniquely through it. This is the module-theoretic content of strong
cartesianness. -/
private theorem pullbackAdjoint_factor
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (F : X.Modules) (G : Y.Modules) (K : Z.Modules)
    (α : ((Scheme.Modules.pullback f).obj G) ⟶ F) [IsIso α]
    (β : G ⟶ (Scheme.Modules.pushforward (h ≫ f)).obj K) :
    ∃! γ : F ⟶ (Scheme.Modules.pushforward h).obj K,
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv G F α ≫
        (Scheme.Modules.pushforward f).map γ =
          β ≫ (Scheme.Modules.pushforwardComp h f).inv.app K := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let δ := (adj.homEquiv G ((Scheme.Modules.pushforward h).obj K)).symm
    (β ≫ (Scheme.Modules.pushforwardComp h f).inv.app K)
  let γ : F ⟶ (Scheme.Modules.pushforward h).obj K := inv α ≫ δ
  have hγ : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv G F α ≫
      (Scheme.Modules.pushforward f).map γ =
      β ≫ (Scheme.Modules.pushforwardComp h f).inv.app K := by
    rw [← adj.homEquiv_naturality_right]
    simp [γ, δ, adj]
  refine ⟨γ, hγ, fun γ' hγ' => (cancel_epi α).mp <|
    (adj.homEquiv G ((Scheme.Modules.pushforward h).obj K)).injective ?_⟩
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
  exact hγ'.trans hγ.symm

/-- If the adjoint of the module component of an `f`-map `⟨f, _⟩` is an isomorphism, then every
`f`-map over a composite `g₀ ≫ f` factors uniquely through it over `g₀`. -/
theorem FMap.existsUnique_comp_of_isIso {X A C : Object B S hS} (f : A.base ⟶ C.base)
    (α : (Scheme.Modules.pullback (Object.schemeMap f)).obj C.module ⟶ A.module) [IsIso α]
    (g₀ : X.base ⟶ A.base)
    (ρ : C.module ⟶ (Scheme.Modules.pushforward (Object.schemeMap (g₀ ≫ f))).obj X.module) :
    ∃! γ : A.module ⟶ (Scheme.Modules.pushforward (Object.schemeMap g₀)).obj X.module,
      FMap.comp (⟨g₀, γ⟩ : FMap X A) ⟨f, (Scheme.Modules.pullbackPushforwardAdjunction
        (Object.schemeMap f)).homEquiv C.module A.module α⟩ = (⟨g₀ ≫ f, ρ⟩ : FMap X C) := by
  have he : Object.schemeMap (g₀ ≫ f) = Object.schemeMap g₀ ≫ Object.schemeMap f := by
    simp [Object.schemeMap]
  let beta : C.module ⟶
      (Scheme.Modules.pushforward (Object.schemeMap g₀ ≫ Object.schemeMap f)).obj X.module :=
    ρ ≫ (Scheme.Modules.pushforwardCongr he).hom.app X.module
  obtain ⟨γ, hγ, hγuniq⟩ := pullbackAdjoint_factor
    (Object.schemeMap f) (Object.schemeMap g₀) A.module C.module X.module α beta
  refine ⟨γ, ?_, fun γ' hγ' => hγuniq γ' ?_⟩
  · refine Sigma.ext rfl ?_
    cases he
    apply heq_of_eq
    dsimp [FMap.comp]
    dsimp [beta] at hγ
    rw [← Category.assoc, hγ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  · have hcomponent' :
        (Scheme.Modules.pullbackPushforwardAdjunction (Object.schemeMap f)).homEquiv
            C.module A.module α ≫ (Scheme.Modules.pushforward (Object.schemeMap f)).map γ' ≫
          (Scheme.Modules.pushforwardComp
            (Object.schemeMap g₀) (Object.schemeMap f)).hom.app X.module ≫
          (Scheme.Modules.pushforwardCongr he.symm).inv.app X.module = ρ := by
      simpa [FMap.comp] using eq_of_heq (Sigma.ext_iff.mp hγ').2
    have hpost := congrArg (fun z => z ≫
        (Scheme.Modules.pushforwardCongr he).hom.app X.module ≫
        (Scheme.Modules.pushforwardComp
          (Object.schemeMap g₀) (Object.schemeMap f)).inv.app X.module) hcomponent'
    simpa [beta, Category.assoc] using hpost

/-- An arrow whose comparison map is an isomorphism is strongly cartesian. -/
private theorem isStronglyCartesian_of_isIso
    (hα : IsIso ((homEquivPullbackHom A C m).2)) :
    (projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m := by
  classical
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let : Category (Object B S hS) := d.category
  let p := projection (B := B) (S := S) (hS := hS)
  have hp : p = d.projection := by
    dsimp [p, projection, d]
  let e := homEquivPullbackHom A C m
  have : IsIso e.2 := hα
  have : p.IsHomLift (p.map m) m := Functor.IsHomLift.map m
  refine { universal_property' := ?_ }
  intro X g τ hτ
  have hrawM := cast_hom_eq_sigma A C m
  rcases hraw : Equiv.cast (d.hom_type X C) τ with ⟨rawBase, rawMod⟩
  let rA : p.obj A = A.base := by simpa [hp] using d.projection_obj A
  let rC : p.obj C = C.base := by simpa [hp] using d.projection_obj C
  let rX : p.obj X = X.base := by simpa [hp] using d.projection_obj X
  let g₀ : X.base ⟶ A.base := eqToHom rX.symm ≫ g ≫ eqToHom rA
  have hbaseM : e.1 = eqToHom rA.symm ≫ p.map m ≫ eqToHom rC := base_eq A C m
  obtain rfl : rawBase = g₀ ≫ e.1 :=
    ((congrArg Sigma.fst hraw).symm.trans ((isHomLift_iff_raw_base_eq _ τ).mp hτ)).trans (by
      rw [hbaseM]
      change eqToHom rX.symm ≫ (g ≫ p.map m) ≫ eqToHom rC =
        (eqToHom rX.symm ≫ g ≫ eqToHom rA) ≫ (eqToHom rA.symm ≫ p.map m ≫ eqToHom rC)
      simp [Category.assoc])
  obtain ⟨γ, hγ, hγuniq⟩ := FMap.existsUnique_comp_of_isIso e.1 e.2 g₀ rawMod
  let χ : X ⟶ A := (Equiv.cast (d.hom_type X A)).symm ⟨g₀, γ⟩
  have hχraw : Equiv.cast (d.hom_type X A) χ = ⟨g₀, γ⟩ := Equiv.apply_symm_apply _ _
  have hχlift : p.IsHomLift g χ :=
    (isHomLift_iff_raw_base_eq g χ).mpr ((congrArg Sigma.fst hχraw).trans rfl)
  have hcomp : χ ≫ m = τ := by
    apply (Equiv.cast (d.hom_type X C)).injective
    calc
      _ = FMap.comp (Equiv.cast (d.hom_type X A) χ) (Equiv.cast (d.hom_type A C) m) :=
        d.composition χ m
      _ = _ := by rwa [hχraw, hrawM, hraw]
  refine ⟨χ, ⟨hχlift, hcomp⟩, fun χ' hχ' => ?_⟩
  rcases hχ'raw : Equiv.cast (d.hom_type X A) χ' with ⟨rawχ'Base, rawχ'Mod⟩
  obtain rfl : rawχ'Base = g₀ :=
    (congrArg Sigma.fst hχ'raw).symm.trans ((isHomLift_iff_raw_base_eq g χ').mp hχ'.1)
  have hc := d.composition χ' m
  rw [hχ'.2, hraw, hχ'raw, hrawM] at hc
  apply (Equiv.cast (d.hom_type X A)).injective
  rw [hχ'raw, hχraw, hγuniq rawχ'Mod hc.symm]

/-- An `f`-map from a second quasi-coherent module on the same scheme, over the identity of the
base. -/
private noncomputable def fiberHom
    (K : ((BigFppfOver.toScheme B S hS).obj A.base).Modules)
    (hK : K.IsQuasicoherent) (γ : A.module ⟶ K) : FMap ⟨A.base, K, hK⟩ A :=
  ⟨𝟙 A.base, γ⟩

/-- Composing with an `f`-map over the identity of the base pushes the module map forward. -/
private lemma fiberHom_comp
    (K : ((BigFppfOver.toScheme B S hS).obj A.base).Modules)
    (hK : K.IsQuasicoherent) (γ : A.module ⟶ K) (n : FMap A C) :
    FMap.comp (fiberHom K hK γ) n =
      ⟨n.1, n.2 ≫ (Scheme.Modules.pushforward (Object.schemeMap n.1)).map γ⟩ := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  dsimp [FMap.comp, fiberHom]
  simp only [Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_rfl_inv_app, Stacks.Modules.pushforward_comp_obj,
    Stacks.Modules.pushforward_id_obj, CategoryTheory.Functor.comp_obj, Category.comp_id]

/-- Different module maps give different `f`-maps over the identity of the base. -/
private lemma fiberHom_injective
    (K : ((BigFppfOver.toScheme B S hS).obj A.base).Modules)
    (hK : K.IsQuasicoherent) : Function.Injective (fiberHom (A := A) K hK) :=
  fun _ _ h => eq_of_heq (Sigma.ext_iff.mp h).2

/-- Every `f`-map over the identity of the base comes from a module map. -/
private lemma exists_fiberHom
    (K : ((BigFppfOver.toScheme B S hS).obj A.base).Modules)
    (hK : K.IsQuasicoherent) (χ : FMap ⟨A.base, K, hK⟩ A)
    (hχ : χ.1 = 𝟙 A.base) : ∃ γ, fiberHom K hK γ = χ := by
  rcases χ with ⟨g, φ⟩
  obtain rfl : g = 𝟙 A.base := hχ
  exact ⟨φ, rfl⟩

/-- For a strongly cartesian arrow, composing with the comparison map is a bijection from the
module maps out of the source module to the module maps out of the pullback of the target
module. -/
private lemma existsUnique_moduleFactor
    (hsc : (projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m)
    (K : ((BigFppfOver.toScheme B S hS).obj A.base).Modules)
    (hK : K.IsQuasicoherent)
    (δ : (Scheme.Modules.pullback (Object.schemeMap
      (homEquivPullbackHom A C m).1)).obj C.module ⟶ K) :
    ∃! γ : A.module ⟶ K, (homEquivPullbackHom A C m).2 ≫ γ = δ := by
  classical
  let d := Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))
  let p := d.projection
  let e := homEquivPullbackHom A C m
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Object.schemeMap e.1)
  let E : Object B S hS := ⟨A.base, K, hK⟩
  let rE := d.projection_obj E
  let rA := d.projection_obj A
  let g : p.obj E ⟶ p.obj A := eqToHom rE ≫ eqToHom rA.symm
  let τ : E ⟶ C := (Equiv.cast (d.hom_type E C)).symm
    ⟨e.1, adj.homEquiv C.module K δ⟩
  let v (γ : A.module ⟶ K) : E ⟶ A :=
    (Equiv.cast (d.hom_type E A)).symm (fiberHom K hK γ)
  have hg : eqToHom rE.symm ≫ g ≫ eqToHom rA = 𝟙 A.base := by simp [g, E]
  have hv (γ : A.module ⟶ K) : p.IsHomLift g (v γ) :=
    (isHomLift_iff_raw_base_eq g (v γ)).mpr ((congrArg Sigma.fst
      (Equiv.apply_symm_apply (Equiv.cast (d.hom_type E A)) (fiberHom K hK γ))).trans hg.symm)
  have ht : p.IsHomLift (g ≫ p.map m) τ := by
    have hh : p.map τ = g ≫ p.map m := by
      simp [p, d.projection_map, τ, g, e, homEquivPullbackHom]
    exact hh ▸ Functor.IsHomLift.map τ
  have hrawm := cast_hom_eq_sigma A C m
  have hfac (γ : A.module ⟶ K) : v γ ≫ m = τ ↔ e.2 ≫ γ = δ := by
    have hc : (Equiv.cast (d.hom_type E C)) (v γ ≫ m) =
        ⟨e.1, adj.homEquiv C.module K (e.2 ≫ γ)⟩ := by
      rw [d.composition]
      simp only [v, Equiv.apply_symm_apply]
      rw [hrawm, fiberHom_comp]
      congr 1
    rw [← (Equiv.cast (d.hom_type E C)).injective.eq_iff, hc]
    simp only [τ, Equiv.apply_symm_apply]
    exact ⟨fun h => (adj.homEquiv C.module K).injective (eq_of_heq (Sigma.ext_iff.mp h).2),
      fun h => by rw [h]⟩
  change p.IsStronglyCartesian (p.map m) m at hsc
  obtain ⟨χ, ⟨hχ, hχcomp⟩, huniq⟩ := hsc.universal_property' g τ
  have hχbase : ((Equiv.cast (d.hom_type E A)) χ).1 = 𝟙 A.base :=
    ((isHomLift_iff_raw_base_eq g χ).mp hχ).trans hg
  obtain ⟨γ, hγ⟩ := exists_fiberHom K hK ((Equiv.cast (d.hom_type E A)) χ) hχbase
  have hvγ : v γ = χ := by
    apply (Equiv.cast (d.hom_type E A)).injective
    simpa [v] using hγ
  refine ⟨γ, (hfac γ).mp (by simpa [hvγ] using hχcomp), fun γ' hγ' => ?_⟩
  apply fiberHom_injective K hK
  have hh : v γ' = v γ := (huniq (v γ') ⟨hv γ', (hfac γ').mpr hγ'⟩).trans hvγ.symm
  simpa [v] using congrArg (Equiv.cast (d.hom_type E A)) hh

/-- **Stacks 04U3.** An arrow of quasi-coherent modules is strongly cartesian if and only if
its canonical pullback comparison map is an isomorphism. -/
@[stacks 04U3]
public theorem isStronglyCartesian_iff :
    (projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m ↔
      IsIso ((homEquivPullbackHom A C m).2) := by
  refine ⟨fun hsc => ?_, isStronglyCartesian_of_isIso m⟩
  let e := homEquivPullbackHom A C m
  let F := (Scheme.Modules.pullback (Object.schemeMap e.1)).obj C.module
  obtain ⟨γ, hγ, _⟩ := existsUnique_moduleFactor m hsc F
    (Stacks.Modules.isQuasicoherent_pullback _ C.module C.quasicoherent) (𝟙 F)
  obtain ⟨η, _, hη⟩ := existsUnique_moduleFactor m hsc A.module A.quasicoherent e.2
  have hγ' : γ ≫ e.2 = 𝟙 A.module := by
    apply (hη _ ?_).trans (hη (𝟙 A.module) (Category.comp_id e.2)).symm
    change e.2 ≫ (γ ≫ e.2) = e.2
    rw [← Category.assoc, hγ, Category.id_comp]
  exact ⟨⟨γ, hγ, hγ'⟩⟩

end Stacks.QCoh

end
