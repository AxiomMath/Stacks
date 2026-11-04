module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.GlueDescentDatum
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Reading
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback

/-!
# The descended polarization read on the families of points over the atlas

Let `G` be a functor over the site from the points of `T` to
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized`, `X` the glued algebraic space and `L`
the module on `X` descended from the module `M₀` of `G` at the atlas `U₀` of `T`
(`AlgebraicGeometry.PolarizedOverSpace.glueModule`), with `τ : M₀ ≅ s₀^* L`. This file proves
that `τ` turns the pairwise isomorphism of the descent datum, read on any algebraic space, into
the canonical comparison of the two inverse images of `L` (Stacks 04W5).

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.appIso_transitionOn`: an isomorphism of a descent
  datum with the canonical descent datum of `L` intertwines the pairwise isomorphisms read on a
  test space with the canonical comparisons.
* `AlgebraicGeometry.PolarizedOverSpace.glueDatum_reading`: the case of the descent datum of `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The pairwise isomorphism of the canonical descent datum of `L`, read on a test space, is the
canonical comparison of Stacks 04W5. -/
theorem transitionOn_canonicalDescentDatum {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : L.IsQuasicoherentOnSite) (i j : I)
    {T : AlgebraicSpaces B S hS} (v : T ⟶ pair B S hS Y f i j) (vi : T ⟶ Y i) (vj : T ⟶ Y j)
    (hi : v ≫ pairFst B S hS Y f i j = vi) (hj : v ≫ pairSnd B S hS Y f i j = vj)
    (h : vi ≫ f i = vj ≫ f j) :
    transitionOn B S hS Y f (canonicalDescentDatum B S hS Y f L hL).F
        (canonicalDescentDatum B S hS Y f L hL).transition i j v vi vj hi hj =
      canonicalComparison vi vj (f i) (f j) h L :=
  transitionOn_canonicalComparison B S hS Y f L i j v vi vj hi hj

/-- **An isomorphism `e` of a descent datum `D` with the canonical descent datum of `L`
intertwines the pairwise isomorphisms of `D`, read on any algebraic space, with the canonical
comparisons of Stacks 04W5.** -/
theorem appIso_transitionOn {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (D : DescentDatum B S hS Y f)
    {L : Modules.{u, u} B S hS X.1 X.2} (hL : L.IsQuasicoherentOnSite)
    (e : D ≅ canonicalDescentDatum B S hS Y f L hL) (i j : I)
    {T : AlgebraicSpaces B S hS} (v : T ⟶ pair B S hS Y f i j) (vi : T ⟶ Y i) (vj : T ⟶ Y j)
    (hi : v ≫ pairFst B S hS Y f i j = vi) (hj : v ≫ pairSnd B S hS Y f i j = vj)
    (h : vi ≫ f i = vj ≫ f j) :
    (modulePullback B S hS vi).mapIso (DescentDatum.appIso B S hS e i) ≪≫
        canonicalComparison vi vj (f i) (f j) h L =
      transitionOn B S hS Y f D.F D.transition i j v vi vj hi hj ≪≫
        (modulePullback B S hS vj).mapIso (DescentDatum.appIso B S hS e j) := by
  apply Iso.ext
  have N := transitionOn_naturality B S hS Y f e.hom i j v vi vj hi hj
  have hC := congrArg Iso.hom (transitionOn_canonicalDescentDatum Y f L hL i j v vi vj hi hj h)
  refine (Iso.trans_hom _ _).trans ?_
  refine Eq.trans ?_ (Iso.trans_hom _ _).symm
  refine (congrArg (· ≫ _) (Functor.mapIso_hom _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Functor.mapIso_hom _ _)).symm
  exact (congrArg (_ ≫ ·) hC.symm).trans N

/-- **`appIso_transitionOn` for a member given a second time.** The member `Y i`, its morphism
`f i`, its module, the component of `e`, the two morphisms to `Y i` and the reading are given
again as `Y₀`, `s₀`, `M₀`, `τ`, `v₁`, `v₂` and `R`, with the equalities identifying the two;
the identification is made here, at variable level, by substitution. -/
theorem appIso_transitionOn_of_heq {I : Type v} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (D : DescentDatum B S hS Y f)
    {L : Modules.{u, u} B S hS X.1 X.2} (hL : L.IsQuasicoherentOnSite)
    (e : D ≅ canonicalDescentDatum B S hS Y f L hL) (i : I)
    {Y₀ : AlgebraicSpaces B S hS} {s₀ : Y₀ ⟶ X} {M₀ : Modules.{u, u} B S hS Y₀.1 Y₀.2}
    {τ : M₀ ≅ (modulePullback B S hS s₀).obj L}
    (hY : Y i = Y₀) (hs : HEq (f i) s₀) (hM : HEq (D.F i) M₀)
    (hτ : HEq (DescentDatum.appIso B S hS e i) τ)
    {T : AlgebraicSpaces B S hS} (v : T ⟶ pair B S hS Y f i i) {vi vj : T ⟶ Y i}
    (hi : v ≫ pairFst B S hS Y f i i = vi) (hj : v ≫ pairSnd B S hS Y f i i = vj)
    {v₁ v₂ : T ⟶ Y₀} (hv₁ : HEq vi v₁) (hv₂ : HEq vj v₂) (h : v₁ ≫ s₀ = v₂ ≫ s₀)
    {R : (modulePullback B S hS v₁).obj M₀ ≅ (modulePullback B S hS v₂).obj M₀}
    (hR : HEq (transitionOn B S hS Y f D.F D.transition i i v vi vj hi hj) R) :
    (modulePullback B S hS v₁).mapIso τ ≪≫ canonicalComparison v₁ v₂ s₀ s₀ h L =
      R ≪≫ (modulePullback B S hS v₂).mapIso τ := by
  subst hY
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hM
  obtain rfl := eq_of_heq hτ
  obtain rfl := eq_of_heq hv₁
  obtain rfl := eq_of_heq hv₂
  obtain rfl := eq_of_heq hR
  exact appIso_transitionOn Y f D hL e i i v vi vj hi hj h

/-- **A reading `Mx ≅ sx^* L` through `A : Yx ⟶ Y₀` and `τ : M₀ ≅ s₀^* L`, pulled back along
`y`, is the reading through `y ≫ A`**, given the composition law of the isomorphisms of
modules. -/
theorem reading_comp {X Y₀ Yx Yx' : AlgebraicSpaces B S hS} {s₀ : Y₀ ⟶ X}
    {L : Modules.{u, u} B S hS X.1 X.2} {M₀ : Modules.{u, u} B S hS Y₀.1 Y₀.2}
    (τ : M₀ ≅ (modulePullback B S hS s₀).obj L) {Mx : Modules.{u, u} B S hS Yx.1 Yx.2}
    {Mx' : Modules.{u, u} B S hS Yx'.1 Yx'.2} (A : Yx ⟶ Y₀) (sx : Yx ⟶ X) (hA : A ≫ s₀ = sx)
    (f : Mx ≅ (modulePullback B S hS A).obj M₀) (y : Yx' ⟶ Yx) (sx' : Yx' ⟶ X)
    (hy : y ≫ sx = sx') (fy : Mx' ≅ (modulePullback B S hS y).obj Mx) (A' : Yx' ⟶ Y₀)
    (hyA : y ≫ A = A') (hA' : A' ≫ s₀ = sx') (f' : Mx' ≅ (modulePullback B S hS A').obj M₀)
    (law : fy ≪≫ (modulePullback B S hS y).mapIso f ≪≫
      (pullbackComparison B S hS y A A' hyA M₀).symm = f') :
    fy ≪≫ (modulePullback B S hS y).mapIso
        (f ≪≫ (modulePullback B S hS A).mapIso τ ≪≫
          (pullbackComparison B S hS A s₀ sx hA L).symm) ≪≫
        (pullbackComparison B S hS y sx sx' hy L).symm =
      f' ≪≫ (modulePullback B S hS A').mapIso τ ≪≫
        (pullbackComparison B S hS A' s₀ sx' hA' L).symm := by
  subst law
  have T' : (modulePullback B S hS y).mapIso (pullbackComparison B S hS A s₀ sx hA L).symm ≪≫
      (pullbackComparison B S hS y sx sx' hy L).symm =
      (pullbackComparison B S hS y A A' hyA ((modulePullback B S hS s₀).obj L)).symm ≪≫
        (pullbackComparison B S hS A' s₀ sx' hA' L).symm := by
    rw [Functor.mapIso_symm, ← Iso.trans_symm,
      pullbackComparison_trans B S hS y A s₀ sx hA A' hyA sx' hy hA' L, Iso.trans_symm]
  have N : (modulePullback B S hS y).mapIso ((modulePullback B S hS A).mapIso τ) ≪≫
      (pullbackComparison B S hS y A A' hyA ((modulePullback B S hS s₀).obj L)).symm =
      (pullbackComparison B S hS y A A' hyA M₀).symm ≪≫ (modulePullback B S hS A').mapIso τ :=
    Iso.ext (pullbackComparison_inv_naturality B S hS y A A' hyA τ.hom)
  simp only [Functor.mapIso_trans, Iso.trans_assoc, T', Iso.subst_trans₂ N]

/-- **The reading along `R : Q ⟶ Zd` of `κ⁻¹ ≫ ρ`**, for `κ : Md ≅ E^* M` and `ρ : Md ≅ sd^* L`,
is `μ⁻¹ ≫ ρ_Q` as soon as `κ` and `ρ` pulled back along `R` are `μ` and `ρ_Q`. -/
theorem readIso_reading {X Za Zd Q : AlgebraicSpaces B S hS} {sa : Za ⟶ X}
    {L : Modules.{u, u} B S hS X.1 X.2} {M : Modules.{u, u} B S hS Za.1 Za.2}
    {Md : Modules.{u, u} B S hS Zd.1 Zd.2} {MQ : Modules.{u, u} B S hS Q.1 Q.2}
    (E : Zd ⟶ Za) (sd : Zd ⟶ X) (hE : E ≫ sa = sd)
    (κ : Md ≅ (modulePullback B S hS E).obj M) (ρ : Md ≅ (modulePullback B S hS sd).obj L)
    (R : Q ⟶ Zd) (q : Q ⟶ Za) (hq : R ≫ E = q) (sQ : Q ⟶ X) (hR : R ≫ sd = sQ)
    (hqs : q ≫ sa = sQ) (κR : MQ ≅ (modulePullback B S hS R).obj Md)
    (μ : MQ ≅ (modulePullback B S hS q).obj M) (ρQ : MQ ≅ (modulePullback B S hS sQ).obj L)
    (lκ : κR ≪≫ (modulePullback B S hS R).mapIso κ ≪≫
      (pullbackComparison B S hS R E q hq M).symm = μ)
    (lρ : κR ≪≫ (modulePullback B S hS R).mapIso ρ ≪≫
      (pullbackComparison B S hS R sd sQ hR L).symm = ρQ) :
    readIso R hq hq (κ.symm ≪≫ ρ ≪≫ pullbackComparison B S hS E sa sd hE L) =
      μ.symm ≪≫ ρQ ≪≫ pullbackComparison B S hS q sa sQ hqs L := by
  subst lκ lρ
  have T' : (modulePullback B S hS R).mapIso (pullbackComparison B S hS E sa sd hE L) ≪≫
      (pullbackComparison B S hS R E q hq ((modulePullback B S hS sa).obj L)).symm =
      (pullbackComparison B S hS R sd sQ hR L).symm ≪≫ pullbackComparison B S hS q sa sQ hqs L := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    simpa only [Iso.trans_hom, Functor.mapIso_hom] using
      congrArg Iso.hom (pullbackComparison_trans B S hS R E sa sd hE q hq sQ hR hqs L)
  simp only [readIso, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc, T']

/-- **The pairwise condition of Stacks 04W3 at a pair `a, b : P ⟶ Zd` through which a pair
`R₁, R₂ : Q ⟶ Zd` with equal readings of `Ψ` factors.** -/
theorem compat_of_readIso_factor {Za Zd Q P : AlgebraicSpaces B S hS} {E : Zd ⟶ Za}
    {M N : Modules.{u, u} B S hS Za.1 Za.2}
    (Ψ : (modulePullback B S hS E).obj M ≅ (modulePullback B S hS E).obj N) (R₁ R₂ : Q ⟶ Zd)
    (q : Q ⟶ Za) (hq₁ : R₁ ≫ E = q) (hq₂ : R₂ ≫ E = q)
    (H : readIso R₁ hq₁ hq₁ Ψ = readIso R₂ hq₂ hq₂ Ψ)
    (a b : P ⟶ Zd) (hab : a ≫ E = b ≫ E) (t : P ⟶ Q) (ht₁ : t ≫ R₁ = a) (ht₂ : t ≫ R₂ = b) :
    (modulePullback B S hS a).map Ψ.hom ≫ (canonicalComparison a b E E hab N).hom =
      (canonicalComparison a b E E hab M).hom ≫ (modulePullback B S hS b).map Ψ.hom := by
  subst ht₁ ht₂
  have e₁ := readIso_readIso t R₁ hq₁ hq₁ (rfl : t ≫ q = t ≫ q) rfl Ψ
  have e₂ := readIso_readIso t R₂ hq₂ hq₂ (rfl : t ≫ q = t ≫ q) rfl Ψ
  have H' := e₁.symm.trans ((congrArg (readIso t (rfl : t ≫ q = t ≫ q) rfl) H).trans e₂)
  exact canonicalComparison_naturality_of_restrictForm_eq B S hS (t ≫ R₁) (t ≫ R₂) E E (t ≫ q)
    _ _ hab Ψ.hom Ψ.hom (congrArg Iso.hom H')

/-- Two isomorphisms whose images under a functor agree after composing with the same
isomorphisms on either side have the same image. -/
theorem map_hom_eq_of_trans_mapIso_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {W Z : D} (κ : W ≅ F.obj A) (P : F.obj B ≅ Z) (X₁ X₂ : A ≅ B)
    (h : κ ≪≫ F.mapIso X₁ ≪≫ P = κ ≪≫ F.mapIso X₂ ≪≫ P) : F.map X₁.hom = F.map X₂.hom := by
  have e := congrArg (fun e => κ.symm ≪≫ e ≪≫ P.symm) h
  simp only [Iso.symm_self_id_assoc, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at e
  exact congrArg Iso.hom e

/-- Cancelling an isomorphism and its inverse on both sides. -/
theorem trans_symm_trans_trans_symm {C : Type*} [Category C] {W X Y Z : C} (κ : W ≅ X)
    (ρ : W ≅ Y) (P : Y ≅ Z) : κ ≪≫ (κ.symm ≪≫ ρ ≪≫ P) ≪≫ P.symm = ρ := by
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

end AlgebraicGeometry.Space.QuasiCoherentDescent

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B))

/-- The family at `U₀ ×_T U₀`, mapped to `Z₀ ×_X Z₀`. -/
def gluePairInv : chart G atlas₁ ⟶
    Space.QuasiCoherentDescent.pair B integerBase (hZ B) (fun _ : Unit => chart G (atlasPoint T))
      (fun _ => chartMap G (atlasPoint T)) () () :=
  ObjectProperty.homMk (isPullback_famMap_prodPoint (glueFamilies G) (atlasPoint T)
    (atlasPoint T)).isoPullback.hom

/-- The morphism `gluePairInv` is a right inverse of `gluePairMap`. -/
theorem gluePairInv_comp_gluePairMap : gluePairInv G ≫ gluePairMap G = 𝟙 _ :=
  ObjectProperty.hom_ext _ (Iso.hom_inv_id _)

/-- **`τ : M₀ ≅ s₀^* L` intertwines the pairwise isomorphism of the descent datum, read along any
morphism into the family at `U₀ ×_T U₀`, with the canonical comparison of Stacks 04W5.** -/
theorem glueDatum_reading (T' : AlgebraicSpaces B integerBase (hZ B))
    (w : T' ⟶ chart G atlas₁) (v₁ v₂ : T' ⟶ chart G (atlasPoint T))
    (e₁ : w ≫ chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)) = v₁)
    (e₂ : w ≫ chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)) = v₂)
    (h : v₁ ≫ chartMap G (atlasPoint T) = v₂ ≫ chartMap G (atlasPoint T)) :
    (Space.modulePullback B integerBase (hZ B) v₁).mapIso (glueModuleIso G) ≪≫
        Space.QuasiCoherentDescent.canonicalComparison v₁ v₂ _ _ h (glueModule G) =
      Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) w v₁ v₂ e₁ e₂ ≪≫
        (Space.modulePullback B integerBase (hZ B) v₂).mapIso (glueModuleIso G) := by
  have hρ : (w ≫ gluePairInv G) ≫ gluePairMap G = w := by
    rw [Category.assoc, gluePairInv_comp_gluePairMap, Category.comp_id]
  have hv : ∀ {Y : AlgebraicSpaces B integerBase (hZ B)} {p : _ ⟶ Y} {q : chart G atlas₁ ⟶ Y}
      {v : T' ⟶ Y}, gluePairMap G ≫ q = p → w ≫ q = v → (w ≫ gluePairInv G) ≫ p = v := by
    rintro _ _ _ _ rfl rfl
    rw [← Category.assoc, hρ]
  have hv₁ := hv (gluePairMap_fst G) e₁
  have hv₂ := hv (gluePairMap_snd G) e₂
  have hD : Space.QuasiCoherentDescent.transitionOn B integerBase (hZ B) _ _
      (glueDescentDatum G).F (glueDescentDatum G).transition () () (w ≫ gluePairInv G) v₁ v₂
        hv₁ hv₂ = Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) w v₁ v₂ e₁ e₂ :=
    (Space.QuasiCoherentDescent.readAlong_comp _ _ (glueTheta G) (w ≫ gluePairInv G)
      (gluePairMap G) _ _ (gluePairMap_fst G) (gluePairMap_snd G) v₁ v₂ hv₁ hv₂).trans
      (Space.QuasiCoherentDescent.readAlong_congr _ _ (glueTheta G) hρ v₁ v₂ _ _)
  exact Space.QuasiCoherentDescent.appIso_transitionOn_of_heq _ _ (glueDescentDatum G)
    (isQuasicoherentOnSite_glueModule G) (glueDatumIso G) () rfl HEq.rfl HEq.rfl HEq.rfl
    (w ≫ gluePairInv G) hv₁ hv₂ HEq.rfl HEq.rfl h (heq_of_eq hD)

/-- **The reading of `L` along a morphism of points `α : x ⟶ U₀`**: the isomorphism
`M_x ≅ g_α^* M₀` of `G`, followed by the inverse image of `τ : M₀ ≅ s₀^* L`, as an isomorphism
`M_x ≅ s_x^* L`. -/
def glueReading {x : (Points T).obj} (α : x ⟶ atlasPoint T) :
    chartModule G x ≅
      (Space.modulePullback B integerBase (hZ B) (chartMap G x)).obj (glueModule G) :=
  fiberIso (G.map α) ≪≫
    (Space.modulePullback B integerBase (hZ B) (chartHom G α)).mapIso (glueModuleIso G) ≪≫
    (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G α)
      (chartMap G (atlasPoint T)) (chartMap G x) (chartHom_comp_chartMap G α) (glueModule G)).symm

/-- **The reading of `L` does not depend on the morphism to the atlas.** -/
theorem glueReading_eq {x : (Points T).obj} (α β : x ⟶ atlasPoint T) :
    glueReading G α = glueReading G β := by
  have K₀ := glueDatum_reading G (chart G x) (chartHom G (prodPointLift α β)) (chartHom G α)
    (chartHom G β) (chartHom_comp G _ _ _ (prodPointLift_fst α β))
    (chartHom_comp G _ _ _ (prodPointLift_snd α β))
    ((chartHom_comp_chartMap G α).trans (chartHom_comp_chartMap G β).symm)
  have R := Space.QuasiCoherentDescent.readAlong_eq_of_comp_law _ _ _ _ _ _ _ _ _ _ _ _
    (fiberIso_map_comp_law G (prodPointLift α β) (prodPointFst _ _) α (prodPointLift_fst α β))
    (fiberIso_map_comp_law G (prodPointLift α β) (prodPointSnd _ _) β (prodPointLift_snd α β))
  exact Space.QuasiCoherentDescent.reading_eq_of_compat (glueModuleIso G) (chartHom G α)
    (chartHom G β) (chartMap G x) (chartHom_comp_chartMap G α) (chartHom_comp_chartMap G β)
    (fiberIso (G.map α)) (fiberIso (G.map β)) (K₀.trans (congrArg (· ≪≫ _) R))

/-- **The reading of `L` is natural in the point.** -/
theorem glueReading_comp {x' x : (Points T).obj} (y : x' ⟶ x) (α : x ⟶ atlasPoint T) :
    fiberIso (G.map y) ≪≫
        (Space.modulePullback B integerBase (hZ B) (chartHom G y)).mapIso (glueReading G α) ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G y)
          (chartMap G x) (chartMap G x') (chartHom_comp_chartMap G y) (glueModule G)).symm =
      glueReading G (y ≫ α) :=
  Space.QuasiCoherentDescent.reading_comp (glueModuleIso G) (chartHom G α) (chartMap G x)
    (chartHom_comp_chartMap G α) (fiberIso (G.map α)) (chartHom G y) (chartMap G x')
    (chartHom_comp_chartMap G y) (fiberIso (G.map y)) (chartHom G (y ≫ α))
    (chartHom_comp G y α _ rfl) (chartHom_comp_chartMap G (y ≫ α)) (fiberIso (G.map (y ≫ α)))
    (fiberIso_map_comp_law G y α _ rfl)

section Sigma

variable (a : (Points T).obj)

/-- The étale covering `Z_{a ×_T U₀} ⟶ Z_a`. -/
abbrev glueCover : chart G (prodPoint a (atlasPoint T)) ⟶ chart G a :=
  chartHom G (prodPointFst a (atlasPoint T))

/-- **The isomorphism `g^* M_a ≅ g^* s_a^* L` on `Z_{a ×_T U₀}`**, `g : Z_{a ×_T U₀} ⟶ Z_a`, read
through the second projection to the atlas. -/
def gluePsi : (Space.modulePullback B integerBase (hZ B) (glueCover G a)).obj (chartModule G a) ≅
    (Space.modulePullback B integerBase (hZ B) (glueCover G a)).obj
      ((Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G)) :=
  (fiberIso (G.map (prodPointFst a (atlasPoint T)))).symm ≪≫
    glueReading G (prodPointSnd a (atlasPoint T)) ≪≫
    Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (glueCover G a)
      (chartMap G a) (chartMap G (prodPoint a (atlasPoint T)))
      (chartHom_comp_chartMap G (prodPointFst a (atlasPoint T))) (glueModule G)

/-- The reading of `gluePsi` along a morphism of families over `a` to `a ×_T U₀`. -/
theorem readIso_gluePsi {x : (Points T).obj} (r : x ⟶ prodPoint a (atlasPoint T)) (m : x ⟶ a)
    (hm : r ≫ prodPointFst a (atlasPoint T) = m) :
    Space.QuasiCoherentDescent.readIso (chartHom G r)
        (chartHom_comp G r (prodPointFst a (atlasPoint T)) m hm)
        (chartHom_comp G r (prodPointFst a (atlasPoint T)) m hm) (gluePsi G a) =
      (fiberIso (G.map m)).symm ≪≫ glueReading G (r ≫ prodPointSnd a (atlasPoint T)) ≪≫
        Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B)
          (chartHom G m) (chartMap G a) (chartMap G x) (chartHom_comp_chartMap G m)
          (glueModule G) :=
  Space.QuasiCoherentDescent.readIso_reading _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fiberIso_map_comp_law G r (prodPointFst a (atlasPoint T)) m hm)
    (glueReading_comp G r (prodPointSnd a (atlasPoint T)))

/-- **`gluePsi` satisfies the pairwise condition of Stacks 04W3 at every pair of morphisms**: both
factor through the family at `(a ×_T U₀) ×_T U₀`, where the two readings are readings of `L`
along morphisms to the atlas. -/
theorem gluePsi_compat (P : AlgebraicSpaces B integerBase (hZ B))
    (a' b' : P ⟶ chart G (prodPoint a (atlasPoint T)))
    (hab : a' ≫ glueCover G a = b' ≫ glueCover G a) :
    (Space.modulePullback B integerBase (hZ B) a').map (gluePsi G a).hom ≫
        (Space.QuasiCoherentDescent.canonicalComparison a' b' _ _ hab
          ((Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G))).hom =
      (Space.QuasiCoherentDescent.canonicalComparison a' b' _ _ hab (chartModule G a)).hom ≫
        (Space.modulePullback B integerBase (hZ B) b').map (gluePsi G a).hom := by
  have sqd := isPullback_chart G (prodPoint a (atlasPoint T)) (atlasPoint T)
  have hw : a' ≫ chartMap G (prodPoint a (atlasPoint T)) =
      (b' ≫ chartHom G (prodPointSnd a (atlasPoint T))) ≫ chartMap G (atlasPoint T) := by
    rw [Category.assoc, chartHom_comp_chartMap G (prodPointSnd a (atlasPoint T)),
      ← chartHom_comp_chartMap G (prodPointFst a (atlasPoint T)), ← Category.assoc, hab,
      Category.assoc]
  have ht₂ : sqd.lift a' _ hw ≫ chartHom G (prodPointLift
      (prodPointFst (prodPoint a (atlasPoint T)) (atlasPoint T) ≫ prodPointFst a (atlasPoint T))
      (prodPointSnd (prodPoint a (atlasPoint T)) (atlasPoint T))) = b' := by
    refine (isPullback_chart G a (atlasPoint T)).hom_ext ?_ ?_
    · rw [Category.assoc, chartHom_comp G _ _ _ (prodPointLift_fst _ _),
        ← chartHom_comp G _ _ _ rfl, ← Category.assoc, sqd.lift_fst, hab]
    · rw [Category.assoc, chartHom_comp G _ _ _ (prodPointLift_snd _ _), sqd.lift_snd]
  refine Space.QuasiCoherentDescent.compat_of_readIso_factor (gluePsi G a)
    (chartHom G (prodPointFst (prodPoint a (atlasPoint T)) (atlasPoint T))) _
    (chartHom G (prodPointFst (prodPoint a (atlasPoint T)) (atlasPoint T) ≫
      prodPointFst a (atlasPoint T)))
    (chartHom_comp G _ _ _ rfl) (chartHom_comp G _ _ _ (prodPointLift_fst _ _)) ?_ a' b' hab
    (sqd.lift a' _ hw) (sqd.lift_fst _ _ _) ht₂
  refine (readIso_gluePsi G a _ _ rfl).trans (Eq.trans ?_
    (readIso_gluePsi G a _ _ (prodPointLift_fst _ _)).symm)
  rw [glueReading_eq G (prodPointLift (prodPointFst (prodPoint a (atlasPoint T)) (atlasPoint T) ≫
      prodPointFst a (atlasPoint T)) (prodPointSnd (prodPoint a (atlasPoint T)) (atlasPoint T)) ≫
      prodPointSnd a (atlasPoint T))
    (prodPointFst (prodPoint a (atlasPoint T)) (atlasPoint T) ≫ prodPointSnd a (atlasPoint T))]

/-- `Z_{a ×_T U₀} ⟶ Z_a` is an étale covering (Stacks 041F): it is the base change of
`Z₀ ⟶ X`. -/
theorem isEtaleCovering_glueCover :
    Space.IsEtaleCovering B integerBase (hZ B)
      (fun _ : Unit => (chart G (prodPoint a (atlasPoint T))).1)
      (fun _ => (glueCover G a).hom) :=
  isEtaleCovering_fst_of_isPullback (isPullback_famMap_prodPoint (glueFamilies G) a (atlasPoint T))
    (isAlgebraicSpace_yoneda B integerBase (hZ B) _)
    (isEtaleCovering_famToGlue_atlasPoint (glueFamilies G))

/-- **`gluePsi` descends along `Z_{a ×_T U₀} ⟶ Z_a`** (Stacks 04W6). -/
theorem exists_glueSigma :
    ∃ χ : chartModule G a ⟶
        (Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G),
      (Space.modulePullback B integerBase (hZ B) (glueCover G a)).map χ = (gluePsi G a).hom :=
  Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated B integerBase (hZ B)
    (glueCover G a) ((isEtaleCovering_glueCover G a).etale ())
    (Space.relativelyRepresentable_of_isAlgebraicSpace B integerBase (hZ B)
      (isAlgebraicSpace_yoneda B integerBase (hZ B) _) _)
    (isEtaleCovering_glueCover G a) _ (gluePsi_compat G a)

/-- **The isomorphism `σ_a : M_a ⟶ s_a^* L`** at a point `a` of `T`. -/
def glueSigmaHom : chartModule G a ⟶
    (Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G) :=
  (exists_glueSigma G a).choose

/-- The inverse image of `glueSigmaHom G a` along `Z_{a ×_T U₀} ⟶ Z_a` is `gluePsi`. -/
theorem modulePullback_map_glueSigmaHom :
    (Space.modulePullback B integerBase (hZ B) (glueCover G a)).map (glueSigmaHom G a) =
      (gluePsi G a).hom :=
  (exists_glueSigma G a).choose_spec

/-- The morphism `glueSigmaHom G a : M_a ⟶ s_a^* L` is an isomorphism. -/
instance isIso_glueSigmaHom : IsIso (glueSigmaHom G a) := by
  have hcov := isEtaleCovering_glueCover G a
  refine Space.isIso_of_forall_isIso_modulePullback_map_of_isFlat B integerBase (hZ B)
    (Z' := fun _ : Unit => chart G (prodPoint a (atlasPoint T))) (fun _ => glueCover G a)
    (fun _ => Space.isFlat_of_isEtale B integerBase (hZ B) (hcov.etale ())) hcov.jointly_surjective
    (glueSigmaHom G a) fun _ => ?_
  rw [modulePullback_map_glueSigmaHom]
  infer_instance

/-- **`σ_a : M_a ≅ s_a^* L`.** -/
def glueSigma : chartModule G a ≅
    (Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G) :=
  asIso (glueSigmaHom G a)

/-- The underlying morphism of `glueSigma G a` is `glueSigmaHom G a`. -/
theorem glueSigma_hom : (glueSigma G a).hom = glueSigmaHom G a := rfl

/-- `σ_a` is the unique morphism whose inverse image along `Z_{a ×_T U₀} ⟶ Z_a` is `gluePsi`. -/
theorem glueSigmaHom_eq_of_map_eq (χ : chartModule G a ⟶
      (Space.modulePullback B integerBase (hZ B) (chartMap G a)).obj (glueModule G))
    (hχ : (Space.modulePullback B integerBase (hZ B) (glueCover G a)).map χ = (gluePsi G a).hom) :
    χ = glueSigmaHom G a :=
  Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B integerBase (hZ B)
    (fun _ : Unit => chart G (prodPoint a (atlasPoint T))) (fun _ => glueCover G a)
    (isEtaleCovering_glueCover G a) _ _
    (fun _ => hχ.trans (modulePullback_map_glueSigmaHom G a).symm)

/-- **`σ_a` read on any point over `a` with a morphism to the atlas is the reading of `L`.** -/
theorem glueSigma_reading {x : (Points T).obj} (r : x ⟶ a) (α : x ⟶ atlasPoint T) :
    fiberIso (G.map r) ≪≫
        (Space.modulePullback B integerBase (hZ B) (chartHom G r)).mapIso (glueSigma G a) ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G r)
          (chartMap G a) (chartMap G x) (chartHom_comp_chartMap G r) (glueModule G)).symm =
      glueReading G α := by
  have e2 : fiberIso (G.map (prodPointFst a (atlasPoint T))) ≪≫
      (Space.modulePullback B integerBase (hZ B) (glueCover G a)).mapIso (glueSigma G a) ≪≫
      (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (glueCover G a)
        (chartMap G a) (chartMap G (prodPoint a (atlasPoint T)))
        (chartHom_comp_chartMap G (prodPointFst a (atlasPoint T))) (glueModule G)).symm =
      glueReading G (prodPointSnd a (atlasPoint T)) := by
    rw [show (Space.modulePullback B integerBase (hZ B) (glueCover G a)).mapIso (glueSigma G a) =
        gluePsi G a from Iso.ext (modulePullback_map_glueSigmaHom G a)]
    exact Space.QuasiCoherentDescent.trans_symm_trans_trans_symm _ _ _
  have e1 := Space.QuasiCoherentDescent.reading_comp (glueSigma G a) (glueCover G a)
    (chartMap G (prodPoint a (atlasPoint T))) (chartHom_comp_chartMap G _)
    (fiberIso (G.map (prodPointFst a (atlasPoint T)))) (chartHom G (prodPointLift r α))
    (chartMap G x) (chartHom_comp_chartMap G _) (fiberIso (G.map (prodPointLift r α)))
    (chartHom G r) (chartHom_comp G _ _ r (prodPointLift_fst r α)) (chartHom_comp_chartMap G r)
    (fiberIso (G.map r)) (fiberIso_map_comp_law G _ _ r (prodPointLift_fst r α))
  exact e1.symm.trans ((congrArg (fun z => fiberIso (G.map (prodPointLift r α)) ≪≫
      (Space.modulePullback B integerBase (hZ B) (chartHom G (prodPointLift r α))).mapIso z ≪≫
      (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B)
        (chartHom G (prodPointLift r α)) (chartMap G (prodPoint a (atlasPoint T))) (chartMap G x)
        (chartHom_comp_chartMap G _) (glueModule G)).symm) e2).trans
    ((glueReading_comp G (prodPointLift r α) (prodPointSnd a (atlasPoint T))).trans
      (glueReading_eq G _ α)))

/-- The two sides of the naturality of `σ`, pulled back to `Z_{a' ×_T U₀}`, agree. -/
theorem glueSigma_comp_cover {a' : (Points T).obj} (u : a' ⟶ a) :
    fiberIso (G.map (prodPointFst a' (atlasPoint T))) ≪≫
        (Space.modulePullback B integerBase (hZ B) (glueCover G a')).mapIso
          (fiberIso (G.map u) ≪≫
            (Space.modulePullback B integerBase (hZ B) (chartHom G u)).mapIso (glueSigma G a) ≪≫
            (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G u)
              (chartMap G a) (chartMap G a') (chartHom_comp_chartMap G u) (glueModule G)).symm) ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (glueCover G a')
          (chartMap G a') (chartMap G (prodPoint a' (atlasPoint T)))
          (chartHom_comp_chartMap G _) (glueModule G)).symm =
      fiberIso (G.map (prodPointFst a' (atlasPoint T))) ≪≫
        (Space.modulePullback B integerBase (hZ B) (glueCover G a')).mapIso (glueSigma G a') ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (glueCover G a')
          (chartMap G a') (chartMap G (prodPoint a' (atlasPoint T)))
          (chartHom_comp_chartMap G _) (glueModule G)).symm :=
  ((Space.QuasiCoherentDescent.reading_comp (glueSigma G a) (chartHom G u)
    (chartMap G a') (chartHom_comp_chartMap G u) (fiberIso (G.map u)) (glueCover G a')
    (chartMap G (prodPoint a' (atlasPoint T))) (chartHom_comp_chartMap G _)
    (fiberIso (G.map (prodPointFst a' (atlasPoint T))))
    (chartHom G (prodPointFst a' (atlasPoint T) ≫ u)) (chartHom_comp G _ u _ rfl)
    (chartHom_comp_chartMap G _) (fiberIso (G.map (prodPointFst a' (atlasPoint T) ≫ u)))
    (fiberIso_map_comp_law G _ u _ rfl)).trans
    (glueSigma_reading G a (prodPointFst a' (atlasPoint T) ≫ u)
      (prodPointSnd a' (atlasPoint T)))).trans
    (glueSigma_reading G a' (prodPointFst a' (atlasPoint T)) (prodPointSnd a' (atlasPoint T))).symm

/-- The naturality of `σ`, on morphisms. -/
theorem glueSigma_comp_hom {a' : (Points T).obj} (u : a' ⟶ a) :
    (fiberIso (G.map u) ≪≫
        (Space.modulePullback B integerBase (hZ B) (chartHom G u)).mapIso (glueSigma G a) ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G u)
          (chartMap G a) (chartMap G a') (chartHom_comp_chartMap G u) (glueModule G)).symm).hom =
      glueSigmaHom G a' := by
  apply glueSigmaHom_eq_of_map_eq G a'
  rw [← modulePullback_map_glueSigmaHom G a', ← glueSigma_hom G a']
  exact Space.QuasiCoherentDescent.map_hom_eq_of_trans_mapIso_eq _ _ _ _ _
    (glueSigma_comp_cover G a u)

/-- **`σ` is natural in the point**: for `u : a' ⟶ a`, `σ_{a'}` is `κ_u` followed by the inverse
image of `σ_a`. -/
theorem glueSigma_comp {a' : (Points T).obj} (u : a' ⟶ a) :
    fiberIso (G.map u) ≪≫
        (Space.modulePullback B integerBase (hZ B) (chartHom G u)).mapIso (glueSigma G a) ≪≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) (chartHom G u)
          (chartMap G a) (chartMap G a') (chartHom_comp_chartMap G u) (glueModule G)).symm =
      glueSigma G a' :=
  Iso.ext (glueSigma_comp_hom G a u)

end Sigma

end AlgebraicGeometry.PolarizedOverSpace

end
