module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriekLan

/-!
# The adjointness of `Rf_!` and `f^!`, abstractly

Let `j^* : 𝒟 ⥤ 𝒞` carry a Deligne-system assignment, so that `Rj_! : 𝒞 ⥤ Pro-𝒟` exists, and let
`Rf̄_* : 𝒟 ⥤ ℰ` be a functor, so that `Rf_! = Rf̄_* ∘ Rj_! : 𝒞 ⥤ Pro-ℰ`. Suppose `𝒟` and `ℰ` sit
in larger categories `𝒟⁺` and `ℰ⁺` (for the duality chapter, `D^b_{Coh} ⊆ D^+_{Coh}`), that
`Rf̄_*` extends to `Rf̄_*⁺ : 𝒟⁺ ⥤ ℰ⁺` with a right adjoint `f̄^!`, and that `j^*` extends to
`j^*⁺ : 𝒟⁺ ⥤ 𝒞'` in such a way that the identification of [Stacks, Tag 0G2H] holds for targets
in `𝒟⁺` ([Stacks, Tag 0G4K]). Then for `K` in `𝒞` and `L` in `ℰ⁺`

`Hom_{Pro-ℰ⁺}(Rf_! K, L) = Hom(K, j^*⁺ f̄^! L)`,

naturally in `K` and `L`. This is the chain of identifications of the proof of
[Stacks, Tag 0G51]:
`Hom(Rf̄_* Rj_! K, L) = Hom(Rj_! K, f̄^! L) = Hom(K, j^* f̄^! L)`. On functors of points the first
step is that the left Kan extension along the left adjoint `Rf̄_*⁺` is precomposition with
`f̄^!` (`CategoryTheory.Adjunction.lanIsoProPointsWhisker`), and the second is
`CategoryTheory.isIso_baseChangePointsHom`.

## Main definitions

* `CategoryTheory.shriekLanIso`: `Lan_{ι_ℰ} ∘ Lan_{Rf̄_*} ≅ (- ∘ f̄^!) ∘ Lan_{ι_𝒟}`.
* `CategoryTheory.shriekPointsIso`: the functor of points of `Rf_! K` in `Pro-ℰ⁺` is
  `Hom(K, j^*⁺ f̄^! -)`.
* `CategoryTheory.shriekHomEquiv`: the resulting bijection, with its naturality in `K` and `L`.

## References

* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
* [Stacks Project, Tag 0G4K](https://stacks.math.columbia.edu/tag/0G4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒞' : Type u₂} [Category.{v} 𝒞']
  {𝒟 : Type u₃} [Category.{v} 𝒟] {𝒟p : Type u₄} [Category.{v} 𝒟p]
  {ℰ : Type u₅} [Category.{v} ℰ] {ℰp : Type u₆} [Category.{v} ℰp]
  (ιX : 𝒟 ⥤ 𝒟p) (direct : 𝒟 ⥤ ℰ) (ιY : ℰ ⥤ ℰp) (directPlus : 𝒟p ⥤ ℰp)
  (γ : direct ⋙ ιY ≅ ιX ⋙ directPlus) {shriek : ℰp ⥤ 𝒟p} (adj : directPlus ⊣ shriek)
  [∀ A : 𝒟 ⥤ Type v, direct.HasLeftKanExtension A] [∀ A : ℰ ⥤ Type v, ιY.HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, ιX.HasLeftKanExtension A]
  [∀ A : 𝒟p ⥤ Type v, directPlus.HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, (direct ⋙ ιY).HasLeftKanExtension A]
  [∀ A : 𝒟 ⥤ Type v, (ιX ⋙ directPlus).HasLeftKanExtension A]

/-- **Left Kan extension along `Rf̄_*` and then along `ι_ℰ` is left Kan extension along `ι_𝒟`
followed by precomposition with `f̄^!`**, for `Rf̄_* ⋙ ι_ℰ ≅ ι_𝒟 ⋙ Rf̄_*⁺` and
`Rf̄_*⁺ ⊣ f̄^!`. -/
public def shriekLanIso :
    direct.lan (H := Type v) ⋙ ιY.lan ≅ ιX.lan ⋙ proPointsWhisker shriek :=
  Functor.lanCompIso (Type v) direct ιY ≪≫ Functor.lanIsoOfIso (Type v) γ ≪≫
    (Functor.lanCompIso (Type v) ιX directPlus).symm ≪≫
    Functor.isoWhiskerLeft ιX.lan adj.lanIsoProPointsWhisker

variable {jX : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jX) (ιU : 𝒞 ⥤ 𝒞') (jY : 𝒟p ⥤ 𝒞')
  (β : ιX ⋙ jY ≅ jX ⋙ ιU) (hlift : ∀ (K : 𝒞) (N : 𝒟p), RestrictionLifting (A.system K ⋙ ιX) jY N)

/-- `Rf_! K = Rf̄_* Rj_! K`, viewed in `Pro-ℰ⁺`. -/
public abbrev shriekPro (K : 𝒞) : ProSeq ℰp :=
  (ProSeq.map ιY).obj ((ProSeq.map direct).obj ((extensionByZero jX A.toAssignment).obj K))

/-- **The functor of points of `Rf_! K` in `Pro-ℰ⁺` is `Hom(K, j^*⁺ f̄^! -)`.** -/
public def shriekPointsIso (K : 𝒞) :
    (shriekPro direct ιY A K).points ≅ shriek ⋙ jY ⋙ coyoneda.obj (op (ιU.obj K)) :=
  (shriekLanIso ιX direct ιY directPlus γ adj).app (jX ⋙ coyoneda.obj (op K)) ≪≫
    (proPointsWhisker shriek).mapIso
      (@asIso _ _ _ _ (baseChangePointsHom ιX ιU β K)
        (isIso_baseChangePointsHom A ιX ιU β K (hlift K)))

/-- **The adjointness of `Rf_!` and `f^!`, abstractly:**
`Hom_{Pro-ℰ⁺}(Rf_! K, L) ≃ Hom(K, j^*⁺ f̄^! L)`. -/
public def shriekHomEquiv (K : 𝒞) (L : ℰp) :
    (shriekPro direct ιY A K ⟶ ProSeq.const.obj L) ≃ (ιU.obj K ⟶ jY.obj (shriek.obj L)) :=
  (ProSeq.homConstEquiv _ L).trans
    ((shriekPointsIso ιX direct ιY directPlus γ adj A ιU jY β hlift K).app L).toEquiv

/-- `CategoryTheory.shriekHomEquiv` is natural in `L`. -/
public lemma shriekHomEquiv_comp_const (K : 𝒞) {L L' : ℰp} (g : L ⟶ L')
    (φ : shriekPro direct ιY A K ⟶ ProSeq.const.obj L) :
    shriekHomEquiv ιX direct ιY directPlus γ adj A ιU jY β hlift K L' (φ ≫ ProSeq.const.map g) =
      shriekHomEquiv ιX direct ιY directPlus γ adj A ιU jY β hlift K L φ ≫
        jY.map (shriek.map g) := by
  have h : ProSeq.homConstEquiv _ L' (φ ≫ ProSeq.const.map g) =
      (shriekPro direct ιY A K).points.map g (ProSeq.homConstEquiv _ L φ) := by
    rw [ProSeq.homConstEquiv_apply, ProSeq.homConstEquiv_apply]
    exact (coyonedaEquiv_naturality φ.unop.hom g).symm
  simp only [shriekHomEquiv, Equiv.trans_apply, Iso.toEquiv_fun, h]
  exact ConcreteCategory.congr_hom
    ((shriekPointsIso ιX direct ιY directPlus γ adj A ιU jY β hlift K).hom.naturality g) _

/-- `Rf_!` on morphisms, in `Pro-ℰ⁺`. -/
public abbrev shriekProMap {K' K : 𝒞} (k : K' ⟶ K) :
    shriekPro direct ιY A K' ⟶ shriekPro direct ιY A K :=
  (ProSeq.map ιY).map ((ProSeq.map direct).map ((extensionByZero jX A.toAssignment).map k))

omit [∀ (A : 𝒟 ⥤ Type v), (direct ⋙ ιY).HasLeftKanExtension A] in
/-- On functors of points, `Rf_!` of a morphism `k : K' ⟶ K` is the left Kan extension of the
precomposition with `k`. -/
public lemma shriekProMap_unop_hom {K' K : 𝒞} (k : K' ⟶ K) :
    (shriekProMap direct ιY A k).unop.hom =
      ιY.lan.map (direct.lan.map (Functor.whiskerLeft jX (coyoneda.map k.op))) :=
  rfl

/-- `CategoryTheory.shriekPointsIso` is natural in `K`. -/
public lemma shriekProMap_unop_hom_comp_shriekPointsIso_hom {K' K : 𝒞} (k : K' ⟶ K) :
    (shriekProMap direct ιY A k).unop.hom ≫
        (shriekPointsIso ιX direct ιY directPlus γ adj A ιU jY β hlift K').hom =
      (shriekPointsIso ιX direct ιY directPlus γ adj A ιU jY β hlift K).hom ≫
        Functor.whiskerLeft (shriek ⋙ jY) (coyoneda.map (ιU.map k).op) := by
  have h₁ := (shriekLanIso ιX direct ιY directPlus γ adj).hom.naturality
    (Functor.whiskerLeft jX (coyoneda.map k.op))
  have h₂ := baseChangePointsHom_naturality ιX ιU β k
  dsimp only [Functor.comp_map] at h₁
  have key : ιY.lan.map (direct.lan.map (Functor.whiskerLeft jX (coyoneda.map k.op))) ≫
      (shriekLanIso ιX direct ιY directPlus γ adj).hom.app (jX ⋙ coyoneda.obj (op K')) ≫
        (proPointsWhisker shriek).map (baseChangePointsHom ιX ιU β K') =
      ((shriekLanIso ιX direct ιY directPlus γ adj).hom.app (jX ⋙ coyoneda.obj (op K)) ≫
        (proPointsWhisker shriek).map (baseChangePointsHom ιX ιU β K)) ≫
        Functor.whiskerLeft (shriek ⋙ jY) (coyoneda.map (ιU.map k).op) := by
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, ← Functor.map_comp, h₂,
      Functor.map_comp]
    rfl
  exact key

/-- `CategoryTheory.shriekHomEquiv` is natural in `K`. -/
public lemma shriekHomEquiv_shriekProMap_comp {K' K : 𝒞} (k : K' ⟶ K) (L : ℰp)
    (φ : shriekPro direct ιY A K ⟶ ProSeq.const.obj L) :
    shriekHomEquiv ιX direct ιY directPlus γ adj A ιU jY β hlift K' L
        (shriekProMap direct ιY A k ≫ φ) =
      ιU.map k ≫ shriekHomEquiv ιX direct ιY directPlus γ adj A ιU jY β hlift K L φ := by
  have h : ProSeq.homConstEquiv _ L (shriekProMap direct ιY A k ≫ φ) =
      (shriekProMap direct ιY A k).unop.hom.app L (ProSeq.homConstEquiv _ L φ) := rfl
  simp only [shriekHomEquiv, Equiv.trans_apply, Iso.toEquiv_fun, h]
  exact ConcreteCategory.congr_hom (congr_app
    (shriekProMap_unop_hom_comp_shriekPointsIso_hom ιX direct ιY directPlus γ adj A ιU jY β hlift
      k) L) _

end CategoryTheory

end
