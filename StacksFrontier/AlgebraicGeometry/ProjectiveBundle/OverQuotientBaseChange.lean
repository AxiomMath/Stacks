module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsEquivBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.UniversalOver
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent

/-!
# The invertible quotient carried by a morphism into a projective bundle, and base change

Let `F` be a quasi-coherent module on a scheme `X`, `π : 𝐏(F) ⟶ X` its projective bundle and
`h : T ⟶ 𝐏(F)` a morphism with `h ≫ π = f`.  Pulling back the tautological quotient along `h`
gives an invertible quotient of `f^*F` (`Stacks.RelativeProj.TautologicalDatum.overQuotient`).
This file proves that it determines `h` (the uniqueness half of Tag 01O4), and that it is
compatible with the base-change morphism `𝐏(E') ⟶ 𝐏(E)` of Tag 01O3: the quotient carried by
`h ≫ b` is the one carried by `h` for the base-changed datum.

## Main results

* `Stacks.RelativeProj.pullbackComp_square_coherence`: the coherence of the comparisons of
  inverse images along a commutative square, preceded by a morphism.
* `Stacks.RelativeProj.TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange`: the
  quotient carried by `h ≫ b`.
* `Stacks.RelativeProj.TautologicalDatum.overQuotient_isEquivalent_of_univ`: the quotient only
  depends on the datum up to isomorphism.
* `Stacks.RelativeProj.projectiveBundleSectionsEquiv_eq_overQuotient`: the bijection of
  Tag 0B3V at a section `σ` is the class of the quotient carried by `σ ≫ b`.
* `Stacks.RelativeProj.eq_of_overQuotient_isEquivalent`: **a morphism into `𝐏(F)` over `X` is
  determined by the quotient it carries** (Tag 01O4, uniqueness).

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

/-- The comparison of inverse images along equal morphisms, on a module. -/
theorem pullbackCongr_hom_app {Y X : Scheme.{u}} {f f' : Y ⟶ X} (e : f = f') (M : X.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e
  rfl

/-- The inverse of the comparison of inverse images along equal morphisms, on a module. -/
theorem pullbackCongr_inv_app {Y X : Scheme.{u}} {f f' : Y ⟶ X} (e : f = f') (M : X.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e
  rfl

/-- **Associativity of the comparisons of inverse images**, on a module. -/
theorem pullbackComp_hom_app_assoc_eq {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : C ⟶ D) (M : D.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback k).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) k).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g k).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ k)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity (f := f) (g := g)
    (h := k)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at key
  rw [← key]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simp

/-- The comparison `a^* d^* ≅ (a ≫ d)^*` along equal morphisms `d = d'`. -/
theorem pullbackComp_hom_app_eqToHom {T P' Y : Scheme.{u}} (a : T ⟶ P') {d d' : P' ⟶ Y}
    (w : d = d') (M : Y.Modules) :
    (Scheme.Modules.pullbackComp a d).hom.app M ≫ eqToHom (by rw [w]) =
      (Scheme.Modules.pullback a).map (eqToHom (by rw [w])) ≫
        (Scheme.Modules.pullbackComp a d').hom.app M := by
  subst w
  simp

/-- **The comparisons of inverse images along a commutative square `b ≫ c = p ≫ g`, preceded by
`a`**: the two routes from `((a ≫ p) ≫ g)^*` to `a^* b^* c^*` agree. -/
theorem pullbackComp_square_coherence {T P' P Y X : Scheme.{u}} (a : T ⟶ P') (b : P' ⟶ P)
    (c : P ⟶ Y) (p : P' ⟶ X) (g : X ⟶ Y) (w : b ≫ c = p ≫ g)
    (he : (a ≫ p) ≫ g = (a ≫ b) ≫ c) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (a ≫ p) g).hom.app M ≫
        (Scheme.Modules.pullbackCongr he).hom.app M ≫
        (Scheme.Modules.pullbackComp (a ≫ b) c).inv.app M ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj M) =
      (Scheme.Modules.pullbackComp a p).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp p g).hom.app M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackCongr w).inv.app M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) := by
  rw [pullbackCongr_inv_app]
  have A1 := pullbackComp_hom_app_assoc_eq a b c M
  have A2 := pullbackComp_hom_app_assoc_eq a p g M
  have B := pullbackComp_hom_app_eqToHom a w.symm M
  rw [← Iso.cancel_iso_hom_left
      ((Scheme.Modules.pullbackComp a p).app ((Scheme.Modules.pullback g).obj M)), Iso.app_hom,
    reassoc_of% A2, Iso.hom_inv_id_app_assoc]
  simp only [pullbackCongr_hom_app]
  rw [← Iso.cancel_iso_hom_right _ _
      ((Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback c).obj M) ≪≫
        (Scheme.Modules.pullbackComp (a ≫ b) c).app M), Iso.trans_hom, Iso.app_hom, Iso.app_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [A1]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% B]
  simp

/-- `pullbackComp_square_coherence` with the comparison along `(a ≫ p) ≫ g = (a ≫ b) ≫ c` split
through a third spelling `f₂`. -/
theorem pullbackComp_square_coherence' {T P' P Y X : Scheme.{u}} (a : T ⟶ P') (b : P' ⟶ P)
    (c : P ⟶ Y) (p : P' ⟶ X) (g : X ⟶ Y) (w : b ≫ c = p ≫ g) {f₂ : T ⟶ Y}
    (hf : (a ≫ p) ≫ g = f₂) (hh : (a ≫ b) ≫ c = f₂) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (a ≫ p) g).hom.app M ≫
        (Scheme.Modules.pullbackCongr hf).hom.app M ≫
        (Scheme.Modules.pullbackCongr hh).inv.app M ≫
        (Scheme.Modules.pullbackComp (a ≫ b) c).inv.app M ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj M) =
      (Scheme.Modules.pullbackComp a p).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp p g).hom.app M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackCongr w).inv.app M) ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) := by
  subst hf
  rw [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl, Category.id_comp,
    ← pullbackCongr_hom_app hh.symm]
  exact pullbackComp_square_coherence a b c p g w hh.symm M

/-- The paste behind `TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange`, in a bare
category. -/
theorem _root_.CategoryTheory.overQuotient_baseChange_paste {𝒞 : Type*} [Category 𝒞]
    {F A A₁ A₂ A₃ B₁ B₂ L L' N C₂ K₁ K₂ K₃ : 𝒞} (x : F ⟶ A) (a₁ : A ⟶ A₁) (a₂ : A₁ ⟶ A₂)
    (a₃ : A₂ ⟶ A₃) (b₁ : A₃ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ L) (α : L ⟶ L') (α' : B₂ ⟶ N)
    (υ : N ⟶ L') (c₁ : A ⟶ A) (c₂ : A ⟶ C₂) (c₂' : A₁ ⟶ K₁) (d₁ : C₂ ⟶ K₁) (d₂ : K₁ ⟶ K₂)
    (d₃ : K₂ ⟶ K₃) (d₄ : K₃ ⟶ N) (H : C₂ ⟶ L')
    (n₁ : b₃ ≫ α = α' ≫ υ) (n₂ : a₁ ≫ c₂' = c₂ ≫ d₁) (hc₁ : c₁ = 𝟙 A)
    (coh : a₂ ≫ a₃ ≫ b₁ ≫ b₂ ≫ α' = c₂' ≫ d₂ ≫ d₃ ≫ d₄) (hH : H = d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ υ) :
    ((x ≫ a₁ ≫ a₂ ≫ a₃) ≫ b₁ ≫ b₂ ≫ b₃) ≫ α = x ≫ c₁ ≫ c₂ ≫ H := by
  rw [hH, hc₁, Category.id_comp]
  simp only [Category.assoc]
  rw [n₁, reassoc_of% coh, reassoc_of% n₂]

/-- **The unit coherence**: an identification `F' ≅ f^*F` is recovered from its inverse image along
the identity through the comparisons `(𝟙)^* ≅ 𝟭` and `(𝟙)^* f^* ≅ (𝟙 ≫ f)^* = f^*`. -/
theorem pullbackId_inv_map_pullbackComp_id {T X : Scheme.{u}} (f : T ⟶ X) {F : X.Modules}
    {F' : T.Modules} (hF : F' ≅ (Scheme.Modules.pullback f).obj F) :
    hF.hom = (Scheme.Modules.pullbackId T).inv.app F' ≫
      (Scheme.Modules.pullback (𝟙 T)).map hF.hom ≫
      (Scheme.Modules.pullbackComp (𝟙 T) f).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp f)).hom.app F := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality (f := f)) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at key
  have n := (Scheme.Modules.pullbackId T).inv.naturality hF.hom
  simp only [Functor.id_map, Functor.id_obj] at n
  rw [← reassoc_of% n, pullbackCongr_hom_app]
  have key2 : (Scheme.Modules.pullbackComp (𝟙 T) f).inv.app F ≫
      (Scheme.Modules.pullbackId T).hom.app ((Scheme.Modules.pullback f).obj F) =
        eqToHom (by simp) := by
    simpa using key
  conv_lhs => rw [← Category.comp_id hF.hom]
  congr 1
  have key3 : (Scheme.Modules.pullbackId T).hom.app ((Scheme.Modules.pullback f).obj F) =
      (Scheme.Modules.pullbackComp (𝟙 T) f).hom.app F ≫ eqToHom (by simp) := by
    rw [← key2, Iso.hom_inv_id_app_assoc]
  rw [← key3, Iso.inv_hom_id_app]
  rfl

namespace TautologicalDatum

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]
  (E' : X.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The quotient carried by `h ≫ b` is the quotient carried by `h` for the base-changed
datum**, for `b : 𝐏(E') ⟶ 𝐏(E)` the base-change morphism along `g` and identifications of the
module on `T` with the two inverse images that are compatible through `E' ≅ g^*E`. -/
theorem overQuotient_comp_projectiveBundleBaseChange (D : TautologicalDatum Y E)
    {T : Scheme.{u}} {f : T ⟶ X} {f₂ : T ⟶ Y} (hf : f ≫ g = f₂) (F' : T.Modules)
    [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj E')
    (hF₂ : F' ≅ (Scheme.Modules.pullback f₂).obj E)
    (hcompat : hF₂.hom = hF.hom ≫ (Scheme.Modules.pullback f).map hE.hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app E ≫ (Scheme.Modules.pullbackCongr hf).hom.app E)
    (h : T ⟶ projectiveBundle X E') (hh : h ≫ projectiveBundleToBase X E' = f)
    (hh₂ : (h ≫ projectiveBundleBaseChange g E E' hE) ≫ projectiveBundleToBase Y E = f₂) :
    (D.overQuotient F' hF₂ (h ≫ projectiveBundleBaseChange g E E' hE) hh₂).IsEquivalent
      ((D.baseChange g E E' hE).overQuotient F' hF h hh) := by
  refine ⟨((Scheme.Modules.pullbackComp h (projectiveBundleBaseChange g E E' hE)).app
    D.twist).symm, ?_⟩
  subst hh
  subst hf
  rw [overQuotient_q, overQuotient_q, hcompat]
  simp only [overQuotientMap, Category.assoc, baseChange_univ]
  exact CategoryTheory.overQuotient_baseChange_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Scheme.Modules.pullbackComp h (projectiveBundleBaseChange g E E' hE)).inv.naturality D.univ)
    ((Scheme.Modules.pullbackComp h (projectiveBundleToBase X E')).inv.naturality hE.hom)
    (pullbackCongr_inv_app rfl E')
    (pullbackComp_square_coherence' h (projectiveBundleBaseChange g E E' hE)
      (projectiveBundleToBase Y E) (projectiveBundleToBase X E') g
      (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE) rfl hh₂ E)
    (((Scheme.Modules.pullback h).map_comp _ _).trans (by
      simp only [tautologicalBaseChangeIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
        Iso.app_inv, Functor.map_comp, Category.assoc]
      rfl))

/-- **The quotient carried by a morphism depends on the datum only up to isomorphism.** -/
theorem overQuotient_isEquivalent_of_univ {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]
    {T : Scheme.{u}} {f : T ⟶ X} (D₁ D₂ : TautologicalDatum X F) (β : D₁.twist ≅ D₂.twist)
    (hβ : D₁.univ ≫ β.hom = D₂.univ) (F' : T.Modules) [F'.IsQuasicoherent]
    (hF : F' ≅ (Scheme.Modules.pullback f).obj F) (h : T ⟶ projectiveBundle X F)
    (hh : h ≫ projectiveBundleToBase X F = f) :
    (D₁.overQuotient F' hF h hh).IsEquivalent (D₂.overQuotient F' hF h hh) :=
  ⟨(Scheme.Modules.pullback h).mapIso β, by
    rw [overQuotient_q, overQuotient_q]
    exact (Category.assoc _ _ _).trans (congrArg (hF.hom ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (((Scheme.Modules.pullback h).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pullback h).map hβ)))))))⟩

/-- The quotient carried by a morphism only depends on the morphism. -/
theorem overQuotient_isEquivalent_of_eq {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]
    {T : Scheme.{u}} {f : T ⟶ X} (D : TautologicalDatum X F) (F' : T.Modules)
    [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj F)
    {h h' : T ⟶ projectiveBundle X F} (e : h = h') (hh : h ≫ projectiveBundleToBase X F = f)
    (hh' : h' ≫ projectiveBundleToBase X F = f) :
    (D.overQuotient F' hF h hh).IsEquivalent (D.overQuotient F' hF h' hh') := by
  subst e
  exact (Stacks.Divisors.invertibleQuotientSetoid T F').refl _

end TautologicalDatum

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent] {T : Scheme.{u}} {f : T ⟶ X}
  (F' : T.Modules) [F'.IsQuasicoherent] (hF : F' ≅ (Scheme.Modules.pullback f).obj F)

/-- **The bijection of Tag 0B3V at a section `σ` of `𝐏(F') ⟶ T` is the class of the quotient
carried by `σ ≫ b`**, for `b : 𝐏(F') ⟶ 𝐏(F)` the base-change morphism along `f`. -/
theorem projectiveBundleSectionsEquiv_eq_overQuotient
    (σ : {σ : T ⟶ projectiveBundle T F' // σ ≫ projectiveBundleToBase T F' = 𝟙 T})
    (hσ : (σ.1 ≫ projectiveBundleBaseChange f F F' hF) ≫ projectiveBundleToBase X F = f) :
    projectiveBundleSectionsEquiv σ = Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid T F')
      ((tautologicalDatum F).overQuotient F' hF (σ.1 ≫ projectiveBundleBaseChange f F F' hF)
        hσ) := by
  have hS : ((tautologicalDatum F).baseChange f F F' hF).sectionsMap =
      (tautologicalDatum F').sectionsMap :=
    TautologicalDatum.sectionsMap_eq_of_univ_comp _ _
      (tautologicalDatumTwistBaseChangeIso f F F' hF)
      (tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom f F F' hF)
  rw [projectiveBundleSectionsEquiv_apply]
  change _ = _
  rw [show Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid T F')
      ((tautologicalDatum F').pullbackQuotient σ.1 σ.2) =
        (tautologicalDatum F').sectionsMap σ from rfl, ← hS]
  refine Quotient.sound ((Stacks.Divisors.invertibleQuotientSetoid T F').symm ?_)
  exact TautologicalDatum.overQuotient_comp_projectiveBundleBaseChange f F F' hF
    (tautologicalDatum F) (Category.id_comp f) F' ((Scheme.Modules.pullbackId T).app F').symm hF
    (pullbackId_inv_map_pullbackComp_id f hF) σ.1 σ.2 hσ

/-- **A morphism into `𝐏(F)` over `X` is determined by the invertible quotient it carries**
(Tag 01O4, uniqueness): it is the base change of the section of `𝐏(F') ⟶ T` it induces through
the cartesian square of Tag 01O3, and that section is determined by its class (Tag 0B3V). -/
theorem eq_of_overQuotient_isEquivalent (h₁ h₂ : T ⟶ projectiveBundle X F)
    (hh₁ : h₁ ≫ projectiveBundleToBase X F = f) (hh₂ : h₂ ≫ projectiveBundleToBase X F = f)
    (H : ((tautologicalDatum F).overQuotient F' hF h₁ hh₁).IsEquivalent
      ((tautologicalDatum F).overQuotient F' hF h₂ hh₂)) : h₁ = h₂ := by
  have key : ∀ (k : {k : T ⟶ projectiveBundle X F // k ≫ projectiveBundleToBase X F = f}),
      projectiveBundleSectionsEquiv (overMorphismEquivSection F' hF k) =
        Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid T F')
          ((tautologicalDatum F).overQuotient F' hF k.1 k.2) := by
    intro k
    have e : (overMorphismEquivSection F' hF k).1 ≫ projectiveBundleBaseChange f F F' hF = k.1 :=
      congrArg Subtype.val ((overMorphismEquivSection F' hF).left_inv k)
    refine (projectiveBundleSectionsEquiv_eq_overQuotient F' hF _ (e ▸ k.2)).trans
      (Quotient.sound ?_)
    exact TautologicalDatum.overQuotient_isEquivalent_of_eq _ F' hF e _ _
  have h := (key ⟨h₁, hh₁⟩).trans ((Quotient.sound H).trans (key ⟨h₂, hh₂⟩).symm)
  exact congrArg Subtype.val ((overMorphismEquivSection F' hF).injective
    (projectiveBundleSectionsEquiv.injective h))

end Stacks.RelativeProj

end
