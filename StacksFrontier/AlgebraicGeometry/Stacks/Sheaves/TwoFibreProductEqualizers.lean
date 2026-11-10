module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# Faithfulness and equalizers in a 2-fibre product of categories fibred in groupoids

For faithful morphisms of categories fibred in groupoids over a common base, the 2-fibre
product remains faithful over the common target, and if both source categories have equalizers
then so does the 2-fibre product.

Faithfulness is componentwise: a morphism of the 2-fibre product is determined by its first
component because the comparison isomorphism then determines the second. Equalizers are built
from the equalizers of the two components: both are carried to equalizers of the common target
(which is where `CatFiberedInGroupoids.preservesEqualizers_homFunctor_of_faithful` is used,
after moving the two categories into a common universe), the comparison isomorphism transports
across the two resulting forks, and the fill-in axiom of the second projection replaces the
vertex by one lying over the right base object.

## Main results

* `CategoryTheory.TwoFibreProductOver.faithful_fst_comp`: the functor from the 2-fibre product
  to the common target is faithful.
* `CategoryTheory.TwoFibreProductOver.hasEqualizers`: the 2-fibre product has equalizers when
  both factors do.

## Implementation notes

The two conclusions are stated separately, as in the source. The functor of the first is the
first projection followed by `F`; the second projection followed by `G` is naturally isomorphic
to it. Both statements are over an arbitrary base category and hence apply in particular to the
big fppf category of a scheme.

Preservation of equalizers is only available for a morphism of
`CategoryTheory.CatFiberedInGroupoids`, whose source and target live in one universe, so a
faithful functor between categories fibred in groupoids in unrelated universes is first pushed
into a common universe by `ULiftHom (ULift _)` and the conclusion is pulled back along the
round trip. That is the role of `CommonCategory` and the `commonUp`/`commonDown` pair.
`CategoryTheory.TwoFibreProductOver.preservesLimitsOfShape_of_commonLift` is that round trip
isolated as a lemma, and `CategoryTheory.TwoFibreProductOver.preservesPullbacks_of_fibred` is
the same lifting applied to
`CategoryTheory.CatFiberedInGroupoids.preservesPullbacks_homFunctor`, which removes its
same-universe restriction; it is used where fibre products and equalizers of the source are
both needed, as in the exactness criterion for lower shriek (Stacks 04BH).

## References

* [Stacks Project, Tag 06X0](https://stacks.math.columbia.edu/tag/06X0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

attribute [local instance] CategoryTheory.uliftCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒵 : Type u₃} [Category.{v₃} 𝒵]
variable {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞)
variable (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴)

/-- A category moved into a prescribed universe for both its objects and its morphisms. -/
abbrev CommonCategory.{vX, uX, w} (X : Type uX) [Category.{vX} X] :=
  CategoryTheory.ULiftHom.{w} (ULift.{w} X)

/-- The equivalence of a category with its universe-lifted copy. -/
def commonEquiv.{vX, uX, w} (X : Type uX) [Category.{vX} X] :
    X ≌ CommonCategory.{vX, uX, w} X :=
  (CategoryTheory.ULift.equivalence (C := X)).trans
    (CategoryTheory.ULiftHom.equiv (C := ULift.{w} X))

/-- The functor into the universe-lifted copy of a category. -/
def commonUp.{vX, uX, w} (X : Type uX) [Category.{vX} X] :
    X ⥤ CommonCategory.{vX, uX, w} X where
  obj x := ULift.up x
  map f := ULift.up f

/-- The functor out of the universe-lifted copy of a category. -/
def commonDown.{vX, uX, w} (X : Type uX) [Category.{vX} X] :
    CommonCategory.{vX, uX, w} X ⥤ X where
  obj x := ULift.down x
  map f := ULift.down f

/-- The functor into the universe-lifted copy of a category is faithful. -/
instance commonUp_faithful.{vX, uX, w} (X : Type uX) [Category.{vX} X] :
    (commonUp.{vX, uX, w} X).Faithful := Functor.Faithful.mk (fun h => ULift.up_injective h)

/-- The functor out of the universe-lifted copy of a category is faithful. -/
instance commonDown_faithful.{vX, uX, w} (X : Type uX) [Category.{vX} X] :
    (commonDown.{vX, uX, w} X).Faithful := Functor.Faithful.mk (fun h => ULift.ext h)

/-- Universe lifting preserves the property of being fibred in groupoids. -/
theorem lift_isFiberedInGroupoids.{vX, uX, w}
    {𝒟 : Type uX} [Category.{vX} 𝒟] {p : 𝒟 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids) :
    (commonDown.{vX, uX, w} 𝒟 ⋙ p).IsFiberedInGroupoids := by
  let up := commonUp.{vX, uX, w} 𝒟
  let down := commonDown.{vX, uX, w} 𝒟
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    cases x with
    | up x =>
      obtain ⟨y, φ, hφ⟩ := hp.exists_lift f x hx
      have hdom : (down ⋙ p).obj (up.obj y) = V := by
        change p.obj (down.obj (up.obj y)) = V
        simpa [down, commonDown, up, commonUp] using IsHomLift.domain_eq p f φ
      have hcod : (down ⋙ p).obj (up.obj x) = U := hx
      refine ⟨up.obj y, up.map φ, ?_⟩
      apply IsHomLift.of_fac' (down ⋙ p) f (up.map φ) hdom hcod ?_
      change p.map (down.map (up.map φ)) = _
      simpa [down, commonDown, up, commonUp] using IsHomLift.fac' p f φ
  · intro x y z φ ψ f hf
    cases x
    cases y
    cases z
    let φ₀ := down.map φ
    let ψ₀ := down.map ψ
    have hf₀ : f ≫ p.map φ₀ = p.map ψ₀ := hf
    obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift φ₀ ψ₀ f hf₀
    let χ' := up.map χ
    refine ⟨χ', ?_, ?_⟩
    · constructor
      · change p.map (down.map (up.map χ)) = f
        simpa [down, commonDown, up, commonUp] using hχ.1
      · apply Functor.map_injective (F := down)
        exact hχ.2
    · intro χ'' hχ''
      have hdown : down.map χ'' = χ := huniq (down.map χ'') ⟨
        hχ''.1,
        congrArg down.map hχ''.2⟩
      apply Functor.map_injective (F := down)
      rw [hdown]
      rfl

/-- The universe-lifted copy of a functor strictly over the base is again strictly over the
base. -/
theorem commonLift_comp_eq.{w} (hF : F ⋙ p𝒴 = p𝒳) :
    (commonDown.{v₂, u₂, w} 𝒳 ⋙ F ⋙ commonUp.{v₄, u₄, w} 𝒴) ⋙
        (commonDown.{v₄, u₄, w} 𝒴 ⋙ p𝒴) =
      commonDown.{v₂, u₂, w} 𝒳 ⋙ p𝒳 := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · cases x with
    | up x =>
        have hobj := congrArg (fun H : 𝒳 ⥤ 𝒞 => H.obj x) hF
        change p𝒴.obj ((commonDown.{v₄, u₄, w} 𝒴).obj
          ((commonUp.{v₄, u₄, w} 𝒴).obj
            (F.obj ((commonDown.{v₂, u₂, w} 𝒳).obj
              ((commonUp.{v₂, u₂, w} 𝒳).obj x))))) =
          p𝒳.obj ((commonDown.{v₂, u₂, w} 𝒳).obj ((commonUp.{v₂, u₂, w} 𝒳).obj x))
        simpa [commonDown, commonUp] using hobj
  · intro x y f
    exact Functor.congr_hom hF ((commonDown.{v₂, u₂, w} 𝒳).map f)

/-- Preservation of a small limit shape transfers from the universe-lifted copy of a functor
back to the functor itself. The round trip through `commonUp` and `commonDown` is the functor
on the nose, and each of those two preserves all small limits, being half of an equivalence. -/
theorem preservesLimitsOfShape_of_commonLift.{w} {K : Type} [SmallCategory K]
    (h : PreservesLimitsOfShape K
      (commonDown.{v₂, u₂, w} 𝒳 ⋙ F ⋙ commonUp.{v₄, u₄, w} 𝒴)) :
    PreservesLimitsOfShape K F := by
  have hup : PreservesLimitsOfSize.{0, 0} (commonUp.{v₂, u₂, w} 𝒳) :=
    Adjunction.rightAdjoint_preservesLimits.{0, 0}
      (commonEquiv.{v₂, u₂, w} 𝒳).symm.toAdjunction
  have hdown : PreservesLimitsOfSize.{0, 0} (commonDown.{v₄, u₄, w} 𝒴) :=
    Adjunction.rightAdjoint_preservesLimits.{0, 0}
      (commonEquiv.{v₄, u₄, w} 𝒴).toAdjunction
  have hcomp : PreservesLimitsOfShape K (commonUp.{v₂, u₂, w} 𝒳 ⋙
      (commonDown.{v₂, u₂, w} 𝒳 ⋙ F ⋙ commonUp.{v₄, u₄, w} 𝒴) ⋙
      commonDown.{v₄, u₄, w} 𝒴) := by
    have := h
    infer_instance
  have hround : commonUp.{v₂, u₂, w} 𝒳 ⋙
      (commonDown.{v₂, u₂, w} 𝒳 ⋙ F ⋙ commonUp.{v₄, u₄, w} 𝒴) ⋙
      commonDown.{v₄, u₄, w} 𝒴 = F :=
    CategoryTheory.Functor.hext (fun _ => rfl) (by
      intro x y f
      dsimp [commonUp, commonDown]
      rfl)
  rw [hround] at hcomp
  exact hcomp

/-- The universe-lifted copy of a category fibred in groupoids, as a `CatFiberedInGroupoids`. -/
private def commonFibred.{vX, uX, w} {𝒟 : Type uX} [Category.{vX} 𝒟] {p : 𝒟 ⥤ 𝒞}
    (hp : p.IsFiberedInGroupoids) : CatFiberedInGroupoids.{v₁, max vX w, u₁, max uX w} 𝒞 :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (commonDown.{vX, uX, w} 𝒟 ⋙ p)) (lift_isFiberedInGroupoids hp)

/-- The universe-lifted copy of a functor strictly over the base, as a 1-morphism of
`CatFiberedInGroupoids`; its underlying functor is `commonDown ⋙ F ⋙ commonUp`. -/
private def commonHom (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) :
    commonFibred.{v₁, u₁, v₂, u₂, max (max v₂ v₄) (max u₂ u₄)} h𝒳 ⟶
      commonFibred.{v₁, u₁, v₄, u₄, max (max v₂ v₄) (max u₂ u₄)} h𝒴 :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm
    ⟨commonDown _ ⋙ F ⋙ commonUp _, commonLift_comp_eq _ _ _ hF⟩

/-- A faithful functor between categories fibred in groupoids over a common base preserves
equalizers, with no constraint relating the universes of the two categories. -/
theorem preservesEqualizers_of_faithful
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) [F.Faithful] :
    PreservesLimitsOfShape WalkingParallelPair F := by
  have : (CatFiberedInGroupoids.homFunctor (commonHom p𝒳 p𝒴 F h𝒳 h𝒴 hF)).Faithful :=
    inferInstanceAs (Functor.Faithful (commonDown _ ⋙ F ⋙ commonUp _))
  exact preservesLimitsOfShape_of_commonLift F
    (CatFiberedInGroupoids.preservesEqualizers_homFunctor_of_faithful
      (commonHom p𝒳 p𝒴 F h𝒳 h𝒴 hF))

/-- A 1-morphism of categories fibred in groupoids over a common base with fibre products
preserves fibre products, with no constraint relating the universes of the two categories.

This is `CategoryTheory.CatFiberedInGroupoids.preservesPullbacks_homFunctor` with the
same-universe restriction removed, by the same universe lifting that
`preservesEqualizers_of_faithful` uses. No faithfulness is needed. -/
theorem preservesPullbacks_of_fibred [HasPullbacks 𝒞]
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) :
    PreservesLimitsOfShape WalkingCospan F :=
  preservesLimitsOfShape_of_commonLift F
    (CatFiberedInGroupoids.preservesPullbacks_homFunctor (commonHom p𝒳 p𝒴 F h𝒳 h𝒴 hF))

/-- The base morphism of a morphism of the 2-fibre product, read off from either component. -/
theorem base_eq_of_comparison (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G}
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (w : F.map a ≫ Q.iso.hom = P.iso.hom ≫ G.map b) :
    eqToHom P.hy.symm ≫ p𝒵.map b ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ p𝒳.map a ≫ eqToHom Q.hx := by
  cases hF
  cases hG
  rcases P with ⟨up, x, z, hx, hz, φ, hφ⟩
  rcases Q with ⟨uq, y, t, hy, ht, ψ, hψ⟩
  cases hx
  cases hy
  have : p𝒴.IsHomLift (𝟙 ((F ⋙ p𝒴).obj x)) φ.hom := hφ
  have : p𝒴.IsHomLift (𝟙 ((F ⋙ p𝒴).obj y)) ψ.hom := hψ
  have hw := congrArg (fun k => p𝒴.map k) w
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at hw ⊢
  rw [IsHomLift.fac' p𝒴 (𝟙 ((F ⋙ p𝒴).obj x)) φ.hom,
    IsHomLift.fac' p𝒴 (𝟙 ((F ⋙ p𝒴).obj y)) ψ.hom] at hw
  have hw' : eqToHom hz.symm ≫ p𝒴.map (G.map b) =
      p𝒴.map (F.map a) ≫ eqToHom ht.symm := by
    simpa [Functor.comp_obj, Functor.comp_map, Category.assoc, eqToHom_trans] using hw.symm
  simpa [Functor.comp_obj, Functor.comp_map, Category.assoc] using
    congrArg (fun k => k ≫ eqToHom ht) hw'

/-- **Stacks 06X0, part (1).** The 2-fibre product of faithful functors is faithful over their
common target. -/
@[stacks 06X0 "part (1)"]
theorem faithful_fst_comp [F.Faithful] [G.Faithful] :
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 F G ⋙ F).Faithful :=
  Functor.Faithful.mk fun {P Q} f g h => by
    change F.map f.a = F.map g.a at h
    apply TwoFibreProductOver.Hom.ext'
    · exact Functor.map_injective F h
    · apply Functor.map_injective G
      apply (cancel_epi P.iso.hom).1
      calc
        P.iso.hom ≫ G.map f.b = F.map f.a ≫ Q.iso.hom := f.w.symm
        _ = F.map g.a ≫ Q.iso.hom := by rw [h]
        _ = P.iso.hom ≫ G.map g.b := g.w

/-- **Stacks 06X0, part (2).** Equalizers in the two source categories induce equalizers in
their 2-fibre product over the common base. -/
@[stacks 06X0 "part (2)"]
theorem hasEqualizers
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    [F.Faithful] [G.Faithful] [HasEqualizers 𝒳] [HasEqualizers 𝒵] :
    HasEqualizers (TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G) := by
  classical
  have : PreservesLimitsOfShape WalkingParallelPair F :=
    preservesEqualizers_of_faithful (p𝒳 := p𝒳) (p𝒴 := p𝒴) (F := F) h𝒳 h𝒴 hF
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_faithful (p𝒳 := p𝒵) (p𝒴 := p𝒴) (F := G) h𝒵 h𝒴 hG
  have key : ∀ {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G} (f g : P ⟶ Q),
      HasLimit (parallelPair f g) := by
    intro P Q f g
    let ex := equalizer.ι f.a g.a
    let ez := equalizer.ι f.b g.b
    let cX : Fork f.a g.a := Fork.ofι ex (equalizer.condition f.a g.a)
    let cZ : Fork f.b g.b := Fork.ofι ez (equalizer.condition f.b g.b)
    have hcX : IsLimit cX := equalizerIsEqualizer f.a g.a
    have hcZ : IsLimit cZ := equalizerIsEqualizer f.b g.b
    have hcFX : IsLimit (Fork.ofι (F.map ex) (by
        calc
          F.map ex ≫ F.map f.a = F.map (ex ≫ f.a) := (Functor.map_comp F ex f.a).symm
          _ = F.map (ex ≫ g.a) := congrArg F.map (equalizer.condition f.a g.a)
          _ = F.map ex ≫ F.map g.a := Functor.map_comp F ex g.a)) :=
      isLimitOfHasEqualizerOfPreservesLimit F f.a g.a
    have hcGZ : IsLimit (Fork.ofι (G.map ez) (by
        calc
          G.map ez ≫ G.map f.b = G.map (ez ≫ f.b) := (Functor.map_comp G ez f.b).symm
          _ = G.map (ez ≫ g.b) := congrArg G.map (equalizer.condition f.b g.b)
          _ = G.map ez ≫ G.map g.b := Functor.map_comp G ez g.b)) :=
      isLimitOfHasEqualizerOfPreservesLimit G f.b g.b
    let kx := F.map ex
    let kz := G.map ez
    have hkernel : (kx ≫ P.iso.hom) ≫ G.map f.b = (kx ≫ P.iso.hom) ≫ G.map g.b := by
      calc
        _ = F.map ex ≫ F.map f.a ≫ Q.iso.hom := by rw [Category.assoc, ← f.w]
        _ = F.map ex ≫ F.map g.a ≫ Q.iso.hom := by
          simpa only [← Category.assoc, ← Functor.map_comp] using
            congrArg (fun t => F.map t ≫ Q.iso.hom) (equalizer.condition f.a g.a)
        _ = (kx ≫ P.iso.hom) ≫ G.map g.b := by rw [Category.assoc, g.w]
    let cLam : Fork (G.map f.b) (G.map g.b) := Fork.ofι (kx ≫ P.iso.hom) hkernel
    let lam := hcGZ.lift cLam
    have hlam : lam ≫ kz = kx ≫ P.iso.hom :=
      Fork.IsLimit.lift_ι' hcGZ (kx ≫ P.iso.hom) hkernel
    have hInv (h : P ⟶ Q) : P.iso.inv ≫ F.map h.a = G.map h.b ≫ Q.iso.inv := by
      calc
        P.iso.inv ≫ F.map h.a = P.iso.inv ≫ (P.iso.hom ≫ G.map h.b) ≫ Q.iso.inv := by
          rw [← h.w]; simp [Category.assoc]
        _ = G.map h.b ≫ Q.iso.inv := by simp [Category.assoc]
    have hkernelInv : (kz ≫ P.iso.inv) ≫ F.map f.a = (kz ≫ P.iso.inv) ≫ F.map g.a := by
      calc
        (kz ≫ P.iso.inv) ≫ F.map f.a = kz ≫ (P.iso.inv ≫ F.map f.a) := by rw [Category.assoc]
        _ = kz ≫ (G.map f.b ≫ Q.iso.inv) := by rw [hInv f]
        _ = (kz ≫ G.map f.b) ≫ Q.iso.inv := by rw [Category.assoc]
        _ = (kz ≫ G.map g.b) ≫ Q.iso.inv :=
          congrArg (fun t => t ≫ Q.iso.inv) (by
            calc
              kz ≫ G.map f.b = G.map (ez ≫ f.b) := by rw [← Functor.map_comp]
              _ = G.map (ez ≫ g.b) := congrArg G.map (equalizer.condition f.b g.b)
              _ = kz ≫ G.map g.b := by rw [Functor.map_comp])
        _ = kz ≫ (G.map g.b ≫ Q.iso.inv) := by rw [← Category.assoc]
        _ = kz ≫ (P.iso.inv ≫ F.map g.a) := by rw [← hInv g]
        _ = (kz ≫ P.iso.inv) ≫ F.map g.a := by rw [← Category.assoc]
    let cMu : Fork (F.map f.a) (F.map g.a) := Fork.ofι (kz ≫ P.iso.inv) hkernelInv
    let mu := hcFX.lift cMu
    have hmu : mu ≫ kx = kz ≫ P.iso.inv :=
      Fork.IsLimit.lift_ι' hcFX (kz ≫ P.iso.inv) hkernelInv
    let compIso : F.obj (equalizer f.a g.a) ≅ G.obj (equalizer f.b g.b) :=
      { hom := lam
        inv := mu
        hom_inv_id := Fork.IsLimit.hom_ext hcFX (by
          calc
            (lam ≫ mu) ≫ kx = lam ≫ (mu ≫ kx) := by rw [Category.assoc]
            _ = lam ≫ (kz ≫ P.iso.inv) := by rw [hmu]
            _ = (lam ≫ kz) ≫ P.iso.inv := by rw [Category.assoc]
            _ = (kx ≫ P.iso.hom) ≫ P.iso.inv := by rw [hlam]
            _ = kx := by simp [Category.assoc]
            _ = 𝟙 _ ≫ Fork.ι (Fork.ofι (F.map ex) _) := by simp [kx])
        inv_hom_id := Fork.IsLimit.hom_ext hcGZ (by
          calc
            (mu ≫ lam) ≫ kz = mu ≫ (lam ≫ kz) := by rw [Category.assoc]
            _ = mu ≫ (kx ≫ P.iso.hom) := by rw [hlam]
            _ = (mu ≫ kx) ≫ P.iso.hom := by rw [Category.assoc]
            _ = (kz ≫ P.iso.inv) ≫ P.iso.hom := by rw [hmu]
            _ = kz := by simp [Category.assoc]
            _ = 𝟙 _ ≫ Fork.ι (Fork.ofι (G.map ez) _) := by simp [kz]) }
    let eX := equalizer f.a g.a
    let eZ := equalizer f.b g.b
    have hbaseX : p𝒴.obj (F.obj eX) = p𝒳.obj eX := Functor.congr_obj hF eX
    have hbaseZ : p𝒴.obj (G.obj eZ) = p𝒵.obj eZ := Functor.congr_obj hG eZ
    have : IsIso compIso.hom := Iso.isIso_hom compIso
    let beta : p𝒳.obj eX ≅ p𝒵.obj eZ :=
      eqToIso hbaseX.symm ≪≫ asIso (p𝒴.map compIso.hom) ≪≫ eqToIso hbaseZ
    obtain ⟨eZ', k, hk⟩ := h𝒵.exists_lift beta.hom eZ rfl
    have : p𝒵.IsHomLift beta.hom k := hk
    have : IsIso beta.hom := inferInstance
    have : p𝒵.IsStronglyCartesian beta.hom k := h𝒵.isStronglyCartesian_homLift beta.hom k
    have : IsIso k := Functor.IsStronglyCartesian.isIso_of_base_isIso p𝒵 beta.hom k
    have : IsIso (G.map k) := Functor.map_isIso G k
    have hLamLift : p𝒴.IsHomLift beta.hom lam := by
      apply IsHomLift.of_fac' p𝒴 beta.hom lam hbaseX hbaseZ
      simp [beta, compIso, Category.assoc]
    have hGfib := h𝒴.isFibredOneMorphism hG
    have : p𝒴.IsHomLift beta.hom (G.map k) := hGfib.map_isHomLift beta.hom k
    have : p𝒴.IsStronglyCartesian beta.hom (G.map k) :=
      h𝒴.isStronglyCartesian_homLift beta.hom (G.map k)
    have hβ : beta.hom = (𝟙 (p𝒳.obj eX)) ≫ beta.hom := by simp
    let delta := Functor.IsStronglyCartesian.map p𝒴 beta.hom (G.map k)
      (g := 𝟙 (p𝒳.obj eX)) hβ lam
    have hdelta : p𝒴.IsHomLift (𝟙 (p𝒳.obj eX)) delta :=
      Functor.IsStronglyCartesian.map_isHomLift p𝒴 beta.hom (G.map k)
        (g := 𝟙 (p𝒳.obj eX)) hβ lam
    have hdeltaFac : delta ≫ G.map k = lam :=
      Functor.IsStronglyCartesian.fac p𝒴 beta.hom (G.map k)
        (g := 𝟙 (p𝒳.obj eX)) hβ lam
    have hdeltaIso : IsIso delta := by
      have hδeq : delta = lam ≫ inv (G.map k) := by
        apply (cancel_mono (G.map k)).1
        simp [Category.assoc, hdeltaFac]
      rw [hδeq]
      infer_instance
    let E : TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G :=
      { base := p𝒳.obj eX
        x := eX
        y := eZ'
        hx := rfl
        hy := IsHomLift.domain_eq p𝒵 beta.hom k
        iso := asIso delta
        vertical := hdelta }
    have hew : F.map ex ≫ P.iso.hom = E.iso.hom ≫ G.map (k ≫ ez) := by
      dsimp [E]
      calc
        F.map ex ≫ P.iso.hom = lam ≫ G.map ez := hlam.symm
        _ = delta ≫ G.map k ≫ G.map ez := by rw [← hdeltaFac, Category.assoc]
        _ = delta ≫ G.map (k ≫ ez) := by simp [Functor.map_comp]
    let e : E ⟶ P := TwoFibreProductOver.Hom.mk' ex (k ≫ ez)
      (base_eq_of_comparison p𝒳 p𝒵 p𝒴 F G (hF := hF) (hG := hG) (P := E) (Q := P)
        (a := ex) (b := k ≫ ez) (w := hew)) hew
    have hcone : e ≫ f = e ≫ g := by
      apply TwoFibreProductOver.Hom.ext'
      · exact equalizer.condition f.a g.a
      · change (k ≫ ez) ≫ f.b = (k ≫ ez) ≫ g.b
        calc
          (k ≫ ez) ≫ f.b = k ≫ (ez ≫ f.b) := Category.assoc _ _ _
          _ = k ≫ (ez ≫ g.b) := congrArg (fun t => k ≫ t) (equalizer.condition f.b g.b)
          _ = (k ≫ ez) ≫ g.b := (Category.assoc _ _ _).symm
    let cE : Fork f g := Fork.ofι e hcone
    have hsa (s : Fork f g) : s.ι.a ≫ f.a = s.ι.a ≫ g.a :=
      congrArg TwoFibreProductOver.Hom.a s.condition
    have hsb (s : Fork f g) : s.ι.b ≫ f.b = s.ι.b ≫ g.b :=
      congrArg TwoFibreProductOver.Hom.b s.condition
    let lift : (s : Fork f g) → s.pt ⟶ E := fun s => by
      let cx : Fork f.a g.a := Fork.ofι s.ι.a (hsa s)
      let cz : Fork f.b g.b := Fork.ofι s.ι.b (hsb s)
      let ax := hcX.lift cx
      let bz := hcZ.lift cz
      have hax : ax ≫ ex = s.ι.a := Fork.IsLimit.lift_ι' hcX s.ι.a (hsa s)
      have hbz : bz ≫ ez = s.ι.b := Fork.IsLimit.lift_ι' hcZ s.ι.b (hsb s)
      let bzTransport := bz ≫ inv k
      have hbzTransport : bzTransport ≫ k ≫ ez = s.ι.b := by
        simpa [bzTransport, Category.assoc] using hbz
      have : Mono (G.map ez) := Fork.IsLimit.mono hcGZ
      have : Mono (G.map (k ≫ ez)) := by
        rw [Functor.map_comp]
        infer_instance
      have hcmp : F.map ax ≫ E.iso.hom = s.pt.iso.hom ≫ G.map bzTransport := by
        apply (cancel_mono (G.map (k ≫ ez))).1
        have hDE : E.iso.hom ≫ G.map (k ≫ ez) = lam ≫ G.map ez := by
          dsimp [E]
          calc
            delta ≫ G.map (k ≫ ez) = delta ≫ (G.map k ≫ G.map ez) := by rw [Functor.map_comp]
            _ = (delta ≫ G.map k) ≫ G.map ez := (Category.assoc _ _ _).symm
            _ = lam ≫ G.map ez := congrArg (fun t => t ≫ G.map ez) hdeltaFac
        have hleft : F.map ax ≫ E.iso.hom ≫ G.map (k ≫ ez) = F.map s.ι.a ≫ P.iso.hom := by
          calc
            F.map ax ≫ (E.iso.hom ≫ G.map (k ≫ ez)) =
                F.map ax ≫ (lam ≫ G.map ez) := congrArg (fun t => F.map ax ≫ t) hDE
            _ = F.map ax ≫ (lam ≫ kz) := rfl
            _ = F.map ax ≫ (kx ≫ P.iso.hom) := congrArg (fun t => F.map ax ≫ t) hlam
            _ = (F.map ax ≫ kx) ≫ P.iso.hom := (Category.assoc _ _ _).symm
            _ = F.map (ax ≫ ex) ≫ P.iso.hom := by rw [← Functor.map_comp]
            _ = F.map s.ι.a ≫ P.iso.hom := by rw [hax]
        calc
          (F.map ax ≫ E.iso.hom) ≫ G.map (k ≫ ez) =
              F.map ax ≫ E.iso.hom ≫ G.map (k ≫ ez) := Category.assoc _ _ _
          _ = F.map s.ι.a ≫ P.iso.hom := hleft
          _ = s.pt.iso.hom ≫ G.map s.ι.b := s.ι.w
          _ = s.pt.iso.hom ≫ G.map (bzTransport ≫ k ≫ ez) :=
                congrArg (fun t => s.pt.iso.hom ≫ G.map t) hbzTransport.symm
          _ = (s.pt.iso.hom ≫ G.map bzTransport) ≫ G.map (k ≫ ez) := by
                simp [Functor.map_comp, Category.assoc]
      exact TwoFibreProductOver.Hom.mk' ax bzTransport
        (base_eq_of_comparison p𝒳 p𝒵 p𝒴 F G (hF := hF) (hG := hG) (P := s.pt) (Q := E)
          (a := ax) (b := bzTransport) (w := hcmp)) hcmp
    have hlift_a (s : Fork f g) : (lift s).a ≫ ex = s.ι.a := by
      exact Fork.IsLimit.lift_ι' hcX s.ι.a (hsa s)
    have hlift_b (s : Fork f g) : (lift s).b ≫ (k ≫ ez) = s.ι.b := by
      dsimp [lift]
      let bz := hcZ.lift (Fork.ofι s.ι.b (hsb s))
      have hbz : bz ≫ ez = s.ι.b := Fork.IsLimit.lift_ι' hcZ s.ι.b (hsb s)
      simpa [Category.assoc] using hbz
    have hcE : IsLimit cE := by
      refine Fork.IsLimit.mk cE lift ?_ ?_
      · intro s
        apply TwoFibreProductOver.Hom.ext'
        · exact hlift_a s
        · exact hlift_b s
      · intro s m hm
        have hma : (m ≫ e).a = s.ι.a := congrArg TwoFibreProductOver.Hom.a hm
        have hmb : (m ≫ e).b = s.ι.b := congrArg TwoFibreProductOver.Hom.b hm
        apply TwoFibreProductOver.Hom.ext'
        · apply (cancel_mono ex).1
          calc
            m.a ≫ ex = (m ≫ e).a := by simp [TwoFibreProductOver.comp_a, e]
            _ = s.ι.a := hma
            _ = (lift s).a ≫ ex := (hlift_a s).symm
        · apply (cancel_mono (k ≫ ez)).1
          calc
            m.b ≫ (k ≫ ez) = (m ≫ e).b := by
              simp [TwoFibreProductOver.comp_b, e]
            _ = s.ι.b := hmb
            _ = (lift s).b ≫ (k ≫ ez) := (hlift_b s).symm
    exact ⟨⟨cE, hcE⟩⟩
  exact hasEqualizers_of_hasLimit_parallelPair _

end CategoryTheory.TwoFibreProductOver

end
