module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackGlueing
public import StacksFrontier.AlgebraicGeometry.SpecLimitCoproductAffine
public import StacksFrontier.Deformation.Artin.Versality.OpennessTower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Cotangent.StandardResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Square-zero towers in `Coh_{X/Y}` are effective, given Grothendieck existence on towers

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over `Spec ℤ`, with `Y`
represented by a coproduct `V₀` of affine schemes. A system `ξₙ` of objects of `Coh_{X/Y}` over
the spectra of an inverse system `Aₙ` of rings with surjective square-zero transitions, together
with a cocone of their test schemes onto `Spec A`, `A = lim Aₙ`, is effective as soon as
Grothendieck's existence theorem holds on the tower of base changes of `X` (in the form
`AlgebraicGeometry.Space.CoherentSituation.TowerExistence`): the morphisms of the test schemes to
`V₀` extend to `Spec A`, because `V₀` is a coproduct of affines
(`AlgebraicGeometry.exists_spec_limit_hom_of_isColimit_cofan`), and the algebraized module with
its identifications on the thickenings is the cocone of `Coh_{X/Y}` lifting the given one.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.TowerExistence`: Grothendieck existence for the
  base changes of `X` to a tower of thickenings, read on `Coh_{X/Y}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isSquareZeroEffective_of_towerExistence`: square-zero
  effectivity of `Coh_{X/Y}` from it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **The underlying cone of rings of a limit cone of commutative algebras is a limit.** -/
def CommAlgCat.isLimitForget₂CommRingCat {Λ : Type u} [CommRing Λ] {J : Type} [SmallCategory J]
    {F : J ⥤ CommAlgCat.{u} Λ} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone c) := by
  haveI : PreservesLimitsOfSize.{0, 0} (forget (CommAlgCat.{u} Λ)) :=
    (CommAlgCat.adj.{u, u} Λ).rightAdjoint_preservesLimits
  haveI : PreservesLimit F (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u} ⋙ forget CommRingCat) := by
    rw [HasForget₂.forget_comp]
    infer_instance
  haveI : ReflectsLimit (F ⋙ forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}) (forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  haveI : PreservesLimit F (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}) :=
    preservesLimit_of_reflects_of_preserves _ (forget CommRingCat)
  exact isLimitOfPreserves _ hc

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- The object of `Coh_{X/Y}` over a test scheme with a given module. -/
abbrev objectOf (T : SchemesOver D.Y) (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hq : G.IsQuasicoherentOnSite) (hfp : G.IsFinitePresentationOnSite)
    (hfl : IsFlatOver B S hS (D.space T).2 (D.projection T).hom G)
    (hps : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T G)),
      IsProperOver B S hS (D.space T).2
        ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T G) hU) :
    CoherentObject D :=
  ⟨T, G, hq, hfp, hfl, hps⟩

/-- **Grothendieck existence on a tower of thickenings, read on `Coh_{X/Y}`.** For every inverse
system `Aₙ` of algebras with surjective square-zero transitions, every test scheme `T` over `Y`
whose scheme is `Spec (lim Aₙ)`, and every system `ξₙ` of objects of `Coh_{X/Y}` over the
`Spec Aₙ`, mapping compatibly to `T`, there is an object of `Coh_{X/Y}` over `T` whose
restrictions are the `ξₙ`, compatibly with the transitions of the system. -/
def TowerExistence : Prop :=
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  ∀ (Λ : Type u) [CommRing Λ] (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ) (cR : Cone R) (_ : IsLimit cR)
    (_ : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (_ : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), (RingHom.ker (R.map f).hom.toRingHom) ^ 2 = ⊥)
    (T : SchemesOver D.Y)
    (eT : (BigFppfOver.toScheme B S hS).obj T.left ≅ Spec (.of cR.pt))
    (ξ : ℕ ⥤ CoherentObject D) (b : ∀ n, (ξ.obj n).T ⟶ T)
    (_ : ∀ n, (ξ.map (homOfLE (n.le_add_right 1))).base ≫ b (n + 1) = b n)
    (e : ∀ n, (BigFppfOver.toScheme B S hS).obj (ξ.obj n).T.left ≅
      Spec (.of (R.obj (op n))))
    (_ : ∀ n, (BigFppfOver.toScheme B S hS).map
        (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).base.left ≫ (e (n + 1)).hom =
      (e n).hom ≫
        Spec.map (CommRingCat.ofHom (R.map (homOfLE (n.le_add_right 1)).op).hom.toRingHom))
    (_ : ∀ n, (BigFppfOver.toScheme B S hS).map (b n).left ≫ eT.hom =
      (e n).hom ≫ Spec.map (CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom)),
    ∃ (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (hq : G.IsQuasicoherentOnSite)
      (hfp : G.IsFinitePresentationOnSite)
      (hfl : IsFlatOver B S hS (D.space T).2 (D.projection T).hom G)
      (hps : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
        (hU : IsClosed (D.support T G)),
        IsProperOver B S hS (D.space T).2
          ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T G) hU)
      (ψ : ∀ n, (modulePullback B S hS (D.relativeMap (b n))).obj G ≅ (ξ.obj n).F),
      ∀ n, ((ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).comp
          (⟨b (n + 1), (ψ (n + 1)).hom, inferInstance⟩ :
            CoherentHom (ξ.obj (n + 1)) (D.objectOf T G hq hfp hfl hps))) =
        ⟨b n, (ψ n).hom, inferInstance⟩


/-- **Square-zero towers in `Coh_{X/Y}` are effective, given Grothendieck existence on towers**,
when `Y` is represented by a coproduct of affine schemes over `Spec ℤ`. -/
theorem isSquareZeroEffective_of_towerExistence {hZ : B.Contains (⊤_ Scheme.{u})}
    (D : CoherentSituation B (⊤_ Scheme.{u}) hZ) (V₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hY : D.Y = (schemeSpaceFunctor B _ hZ).obj V₀) (hV₀ : IsCoproductOfAffines V₀)
    (hTE : D.TowerExistence) :
    Deformation.Artin.IsSquareZeroEffective B _ hZ D.coherentCFG.val.p
      D.coherentCFG.isFiberedInGroupoids := by
  obtain ⟨X, Y, f, hf⟩ := D
  subst hY
  rintro Λ _ chart _ R cR hcR hsurj hsq ξ ⟨pt, ι⟩ e eLimit he heLimit -
  let D : CoherentSituation B (⊤_ Scheme.{u}) hZ :=
    ⟨X, (schemeSpaceFunctor B _ hZ).obj V₀, f, hf⟩
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  -- the data, read without the coercions of `coherentCFG`
  let ξ' : ℕ ⥤ CoherentObject D := ξ
  let e' : ∀ n, (BigFppfOver.toScheme B _ hZ).obj (ξ'.obj n).T.left ≅
      Spec (.of (R.obj (op n))) := e
  let ι' : ∀ n, (ξ'.obj n).T.left ⟶ pt := fun n => ι.app n
  have he' : ∀ {i j : ℕ} (g : i ⟶ j),
      (BigFppfOver.toScheme B _ hZ).map (ξ'.map g : CoherentHom _ _).base.left ≫ (e' j).hom =
        (e' i).hom ≫ Spec.map (CommRingCat.ofHom (R.map g.op).hom.toRingHom) := fun g => he g
  have heLimit' : ∀ n, (BigFppfOver.toScheme B _ hZ).map (ι' n) ≫ eLimit.hom =
      (e' n).hom ≫ Spec.map (CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom) := heLimit
  -- the morphisms of the test schemes to `V₀`
  let τ : ∀ n, (ξ'.obj n).T.left ⟶ V₀ := fun n =>
    (Yoneda.fullyFaithful (C := BigFppfOver B _ hZ)).preimage (ξ'.obj n).T.hom.hom
  have hτ : ∀ n, yoneda.map (τ n) = (ξ'.obj n).T.hom.hom := fun n =>
    (Yoneda.fullyFaithful (C := BigFppfOver B _ hZ)).map_preimage _
  have hτc : ∀ {i j : ℕ} (g : i ⟶ j), (ξ'.map g : CoherentHom _ _).base.left ≫ τ j = τ i := by
    intro i j g
    apply (Yoneda.fullyFaithful (C := BigFppfOver B _ hZ)).map_injective
    rw [Functor.map_comp, hτ, hτ]
    exact congrArg (fun k => k.hom) (CostructuredArrow.w (ξ'.map g : CoherentHom _ _).base)
  -- the extension to `Spec A`
  let A : ℕᵒᵖ ⥤ CommRingCat.{u} := R ⋙ forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}
  let t : ∀ n, Spec (A.obj (op n)) ⟶ (BigFppfOver.toScheme B _ hZ).obj V₀ := fun n =>
    (e' n).inv ≫ (BigFppfOver.toScheme B _ hZ).map (τ n)
  have ht : ∀ {i j : ℕ} (g : i ⟶ j), Spec.map (A.map g.op) ≫ t j = t i := by
    intro i j g
    have h1 : Spec.map (A.map g.op) = (e' i).inv ≫
        (BigFppfOver.toScheme B _ hZ).map (ξ'.map g : CoherentHom _ _).base.left ≫ (e' j).hom := by
      rw [Iso.eq_inv_comp]
      exact (he' g).symm
    change Spec.map (A.map g.op) ≫ (e' j).inv ≫ (BigFppfOver.toScheme B _ hZ).map (τ j) =
      (e' i).inv ≫ (BigFppfOver.toScheme B _ hZ).map (τ i)
    rw [h1, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hτc g]
  have hnil' : ∀ n, RingHom.ker (A.map (homOfLE (Nat.zero_le n)).op).hom ≤
      nilradical (A.obj (op n)) := fun n x hx =>
    ⟨2, by
      have hx' : x * x ∈ RingHom.ker (R.map (homOfLE (Nat.zero_le n)).op).hom.toRingHom ^ 2 := by
        rw [sq]
        exact Ideal.mul_mem_mul hx hx
      rw [hsq] at hx'
      simpa [pow_two] using hx'⟩
  obtain ⟨K, W, hWa, cW, ⟨hcW⟩⟩ := hV₀
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B _ hZ).obj (W k)) := hWa
  obtain ⟨τA, hτA⟩ := exists_spec_limit_hom_of_isColimit_cofan
    (fun k => (BigFppfOver.toScheme B _ hZ).map (cW k)) (nonempty_isColimit_cofan_toScheme hcW).some
    A _ (CommAlgCat.isLimitForget₂CommRingCat hcR) (fun _ => hsurj _) hnil' t ht
  -- the morphism `Spec A ⟶ V₀` in the site
  let g₀ : (BigFppfOver.toScheme B _ hZ).obj pt ⟶ (BigFppfOver.toScheme B _ hZ).obj V₀ :=
    eLimit.hom ≫ τA
  let g : pt ⟶ V₀ := Over.homMk (ObjectProperty.homMk g₀) (ObjectProperty.hom_ext _
    (terminal.hom_ext _ _))
  have hg : ∀ n, ι' n ≫ g = τ n := fun n => by
    apply (BigFppfOver.toScheme B _ hZ).map_injective
    rw [Functor.map_comp]
    change (BigFppfOver.toScheme B _ hZ).map (ι' n) ≫ eLimit.hom ≫ τA = _
    rw [← Category.assoc, heLimit' n, Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom) ≫ τA = t n from hτA n]
    change (e' n).hom ≫ (e' n).inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc]
  -- the test scheme over `Y` and the maps to it
  let Tc : SchemesOver D.Y := CostructuredArrow.mk (Y := pt) ((schemeSpaceFunctor B _ hZ).map g)
  let b : ∀ n, (ξ'.obj n).T ⟶ Tc := fun n => CostructuredArrow.homMk (ι' n) (by
    apply ObjectProperty.hom_ext
    change yoneda.map (ι' n) ≫ yoneda.map g = (ξ'.obj n).T.hom.hom
    rw [← Functor.map_comp, hg]
    exact hτ n)
  have hb : ∀ n, (ξ'.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).base ≫ b (n + 1) =
      b n := fun n => CostructuredArrow.hom_ext _ _ ((ι.naturality _).trans (Category.comp_id _))
  obtain ⟨G, hq, hfp, hfl, hps, ψ, hψ⟩ :=
    hTE Λ R cR hcR hsurj hsq Tc eLimit ξ' b hb e' (fun n => he' _) heLimit'
  let d₀ := D.objectOf Tc G hq hfp hfl hps
  let L : ∀ n, ξ'.obj n ⟶ d₀ := fun n =>
    (⟨b n, (ψ n).hom, inferInstance⟩ : CoherentHom (ξ'.obj n) d₀)
  have hL : ∀ n, ξ'.map (homOfLE (n.le_add_right 1)) ≫ L (n + 1) =
      L n ≫ ((Functor.const ℕ).obj d₀).map (homOfLE (n.le_add_right 1)) := fun n =>
    (hψ n).trans (Category.comp_id (L n)).symm
  exact ⟨⟨d₀, NatTrans.ofSequence L hL⟩, rfl⟩

end AlgebraicGeometry.Space.CoherentSituation

end
