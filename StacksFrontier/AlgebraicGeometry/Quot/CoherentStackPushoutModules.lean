module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFlatModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFiniteModules
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleCompFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Stacks.RimSchlessingerOfThickeningPushout

/-!
# `Coh_{X/B}` and pushouts along thickenings: the gluing of modules (Stacks 08LQ)

This file supplies the hypothesis of
`AlgebraicGeometry.Space.CoherentSituation.fiberSquareComparison_isEquivalence_of_modulesGlueOver`
from Stacks 08KV: along a square of test schemes over a pushout of schemes along a thickening and
an affine morphism, modules satisfying the conditions of Stacks 08KB glue.

The base changes `X_T = X ×_B T` of the four corners are identified with the four spaces of
Stacks 08KV for the projection `X_{Y'} ⟶ Y'`, the scheme pushout being a pushout of algebraic
spaces by Stacks 07SY. The gluing statements of Stacks 08KV are then transported along these
identifications.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.fiberSquareComparison_isEquivalence`:
  **Stacks 08LQ.**
* `AlgebraicGeometry.Space.CoherentSituation.satisfiesRS`: `Coh_{X/B}` satisfies condition (RS)
  of Stacks 07WP.
* `AlgebraicGeometry.Space.CoherentSituation.modulesGlueOver_of_isPushout`: modules satisfying
  the conditions of Stacks 08KB glue along every square of test schemes over a pushout along a
  thickening and an affine morphism, from Stacks 08KV.
* `AlgebraicGeometry.Space.CoherentSituation.modulesGlue_of_identification`: the transport of the
  gluing statements of Stacks 08KV to a square identified with its square of spaces.
* `CategoryTheory.TripleGluing.existsUnique_of_isEquivalence_lift` and
  `CategoryTheory.TripleGluing.exists_iso_of_isEquivalence_lift`: an equivalence between full
  subcategories induced by the restriction to triples glues morphisms and objects.
* `AlgebraicGeometry.Space.transportCoherent_modulePullback`: the comparisons of inverse images
  along two presentations of a square of spaces agree.

## References

* [Stacks Project, Tag 08LQ](https://stacks.math.columbia.edu/tag/08LQ)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Gluing through an equivalence induced by the restriction to triples -/

namespace CategoryTheory.TripleGluing

variable {𝒱' 𝒱 𝒰' 𝒰 : Type*} [Category* 𝒱'] [Category* 𝒱] [Category* 𝒰'] [Category* 𝒰]
  {pV : 𝒱' ⥤ 𝒱} {pA : 𝒱' ⥤ 𝒰'} {pT : 𝒱 ⥤ 𝒰} {pC : 𝒰' ⥤ 𝒰} {c : pV ⋙ pT ≅ pA ⋙ pC}
  {P : ObjectProperty 𝒱'} {Q : ObjectProperty (Triple pT pC)}
  {hPQ : ∀ M : P.FullSubcategory, Q ((P.ι ⋙ restrictFunctor c).obj M)}

/-- **Morphisms glue through an equivalence induced by the restriction to triples.**  If the
restriction to triples induces an equivalence between full subcategories, a pair of morphisms of
the two restrictions of objects of the first subcategory, compatible through `c`, is the pair of
restrictions of exactly one morphism. -/
theorem existsUnique_of_isEquivalence_lift
    (hL : (Q.lift (P.ι ⋙ restrictFunctor c) hPQ).IsEquivalence)
    {M N : 𝒱'} (hM : P M) (hN : P N) (ψY : pV.obj M ⟶ pV.obj N) (ψZ : pA.obj M ⟶ pA.obj N)
    (hcomm : pT.map ψY ≫ c.hom.app N = c.hom.app M ≫ pC.map ψZ) :
    ∃! φ : M ⟶ N, pV.map φ = ψY ∧ pA.map φ = ψZ := by
  let L := Q.lift (P.ι ⋙ restrictFunctor c) hPQ
  have hF : L.FullyFaithful := (L.asEquivalence).fullyFaithfulFunctor
  let t : (restrictFunctor c).obj M ⟶ (restrictFunctor c).obj N := ⟨ψY, ψZ, hcomm⟩
  let φ' : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩ :=
    hF.preimage (ObjectProperty.homMk t : L.obj ⟨M, hM⟩ ⟶ L.obj ⟨N, hN⟩)
  have hφ' : L.map φ' = ObjectProperty.homMk t := hF.map_preimage _
  have h₁ : (L.map φ').hom = t := congrArg (fun x => x.hom) hφ'
  refine ⟨φ'.hom, ⟨congrArg TripleHom.target h₁, congrArg TripleHom.ambient h₁⟩, ?_⟩
  rintro φ ⟨hY, hZ⟩
  have : (ObjectProperty.homMk φ : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩) = φ' :=
    hF.map_injective (by
      rw [hφ']
      ext
      · exact hY
      · exact hZ)
  exact congrArg (fun x => x.hom) this

/-- **Objects glue through an equivalence induced by the restriction to triples.**  If the
restriction to triples induces an equivalence between full subcategories, every triple of the
second subcategory is isomorphic to the restriction of an object of the first. -/
theorem exists_iso_of_isEquivalence_lift (hL : (Q.lift (P.ι ⋙ restrictFunctor c) hPQ).IsEquivalence)
    (T : Triple pT pC) (hT : Q T) :
    ∃ (G : 𝒱') (_ : P G) (ζY : pV.obj G ≅ T.target) (ζA : pA.obj G ≅ T.ambient),
      pT.map ζY.hom ≫ T.comparison.hom = c.hom.app G ≫ pC.map ζA.hom := by
  let L := Q.lift (P.ι ⋙ restrictFunctor c) hPQ
  let e : L.obj (L.objPreimage ⟨T, hT⟩) ≅ ⟨T, hT⟩ := L.objObjPreimageIso ⟨T, hT⟩
  have h₁ : e.hom.hom.target ≫ e.inv.hom.target = 𝟙 _ :=
    congrArg (fun x => TripleHom.target x.hom) e.hom_inv_id
  have h₂ : e.inv.hom.target ≫ e.hom.hom.target = 𝟙 _ :=
    congrArg (fun x => TripleHom.target x.hom) e.inv_hom_id
  have h₃ : e.hom.hom.ambient ≫ e.inv.hom.ambient = 𝟙 _ :=
    congrArg (fun x => TripleHom.ambient x.hom) e.hom_inv_id
  have h₄ : e.inv.hom.ambient ≫ e.hom.hom.ambient = 𝟙 _ :=
    congrArg (fun x => TripleHom.ambient x.hom) e.inv_hom_id
  exact ⟨(L.objPreimage ⟨T, hT⟩).obj, (L.objPreimage ⟨T, hT⟩).property,
    ⟨e.hom.hom.target, e.inv.hom.target, h₁, h₂⟩, ⟨e.hom.hom.ambient, e.inv.hom.ambient, h₃, h₄⟩,
    e.hom.hom.comm⟩

end CategoryTheory.TripleGluing

/-! ### The coherence of two presentations of a gluing problem, abstractly -/

section TransportCoherentOf

variable {𝒲 𝒱 𝒰' 𝒰 𝒱c 𝒰'c 𝒰c : Type*} [Category* 𝒲] [Category* 𝒱] [Category* 𝒰']
  [Category* 𝒰] [Category* 𝒱c] [Category* 𝒰'c] [Category* 𝒰c]
  {pV : 𝒲 ⥤ 𝒱} {pA : 𝒲 ⥤ 𝒰'} {pT : 𝒱 ⥤ 𝒰} {pC : 𝒰' ⥤ 𝒰} {Pa Pb : 𝒲 ⥤ 𝒰}
  {qV : 𝒲 ⥤ 𝒱c} {qA : 𝒲 ⥤ 𝒰'c} {qT : 𝒱c ⥤ 𝒰c} {qC : 𝒰'c ⥤ 𝒰c}
  {EV : 𝒱c ⥤ 𝒱} {EA : 𝒰'c ⥤ 𝒰'} {EU : 𝒰c ⥤ 𝒰} {Rt Ra : 𝒲 ⥤ 𝒰c} {KT : 𝒱c ⥤ 𝒰} {KC : 𝒰'c ⥤ 𝒰}

/-- **The coherence of two presentations of a gluing problem, from the coherences of its
pieces.**  The second presentation's comparison is `sT ≫ ε ≫ sA⁻¹`, and the identifications
of the overlaps are `uT⁻¹ ≫ vT` and `uC⁻¹ ≫ vC`; the coherence
`CategoryTheory.Functor.TransportCoherent` follows from five coherences, one for each
triangle of the picture. -/
theorem CategoryTheory.Functor.transportCoherent_of (c₁ : Pa ≅ pV ⋙ pT) (c₂ : Pa ≅ Pb)
    (c₃ : Pb ≅ pA ⋙ pC) (sT : qV ⋙ qT ≅ Rt) (ε : Rt ≅ Ra) (sA : qA ⋙ qC ≅ Ra)
    (θV : pV ≅ qV ⋙ EV) (θA : pA ≅ qA ⋙ EA) (uT : KT ≅ qT ⋙ EU) (vT : KT ≅ EV ⋙ pT)
    (uC : KC ≅ qC ⋙ EU) (vC : KC ≅ EA ⋙ pC) (xR : Pa ≅ qV ⋙ KT) (xL : Pb ≅ qA ⋙ KC)
    (yR : Pa ≅ Rt ⋙ EU) (yL : Pb ≅ Ra ⋙ EU)
    (hL : ∀ K, xL.hom.app K ≫ vC.hom.app (qA.obj K) = c₃.hom.app K ≫ pC.map (θA.hom.app K))
    (hR : ∀ K, xR.hom.app K ≫ vT.hom.app (qV.obj K) = c₁.hom.app K ≫ pT.map (θV.hom.app K))
    (hMR : ∀ K, xR.hom.app K ≫ uT.hom.app (qV.obj K) = yR.hom.app K ≫ EU.map (sT.inv.app K))
    (hML : ∀ K, xL.hom.app K ≫ uC.hom.app (qA.obj K) = yL.hom.app K ≫ EU.map (sA.inv.app K))
    (hC : ∀ K, c₂.hom.app K ≫ yL.hom.app K = yR.hom.app K ≫ EU.map (ε.hom.app K)) :
    CategoryTheory.Functor.TransportCoherent c₁ c₂ c₃ (sT ≪≫ ε ≪≫ sA.symm) θV θA (uT.symm ≪≫ vT)
      (uC.symm ≪≫ vC) := by
  intro K
  have eR : pT.map (θV.hom.app K) = c₁.inv.app K ≫ xR.hom.app K ≫ vT.hom.app (qV.obj K) := by
    rw [hR K, Iso.inv_hom_id_app_assoc]
  have eMR : xR.hom.app K ≫ uT.hom.app (qV.obj K) ≫ EU.map (sT.hom.app K) = yR.hom.app K := by
    rw [reassoc_of% (hMR K), ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
      Category.comp_id]
  have eML : yL.hom.app K ≫ EU.map (sA.inv.app K) ≫ uC.inv.app (qA.obj K) = xL.hom.app K := by
    rw [← reassoc_of% (hML K), Iso.hom_inv_id_app, Category.comp_id]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [eR]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% eMR, reassoc_of% (hC K).symm, reassoc_of% eML, hL K]

end TransportCoherentOf

/-! ### The comparisons of inverse images along two presentations of a square -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A family of isomorphisms `H j ≅ F i ⋙ G`, indexed by the pairs `(i, j)` satisfying a
condition, changes at equal indices only by the identifications of the functors. -/
theorem _root_.CategoryTheory.Functor.iso_hom_app_congr₂ {C D E ι κ : Type*} [Category* C]
    [Category* D] [Category* E] (P : ι → κ → Prop) (F : ι → C ⥤ D) (H : κ → C ⥤ E) (G : D ⥤ E)
    (τ : ∀ i j, P i j → (H j ≅ F i ⋙ G)) {i i' : ι} {j j' : κ} (hi : i = i') (hj : j = j')
    (hp : P i j) (hp' : P i' j') (K : C) :
    (eqToHom (congrArg H hj)).app K ≫ (τ i' j' hp').hom.app K =
      (τ i j hp).hom.app K ≫ G.map ((eqToHom (congrArg F hi)).app K) := by
  subst hi hj
  simp

/-- **The comparisons of inverse images along two presentations of a square of spaces agree.**
A square `α' ≫ γ' = β' ≫ δ'` of algebraic spaces whose corners are identified, through
`eV`, `eA` and `eU`, with the corners of a second square `cA ≫ aR = cT ≫ tR`: the comparison of
the two inverse images to the first corner along the first square is, read through these
identifications, the comparison `AlgebraicGeometry.Space.PushoutModules.squareOverlap` along the
second. -/
theorem transportCoherent_modulePullback
    {X0 Y0 X1 W Vt Ua Uc : AlgebraicSpaces B S hS} {α' : X0 ⟶ Y0} {β' : X0 ⟶ X1}
    {γ' : Y0 ⟶ W} {δ' : X1 ⟶ W} {a0 b0 : X0 ⟶ W} (hαγ : α' ≫ γ' = a0) (hβδ : β' ≫ δ' = b0)
    (hab : a0 = b0) {eV : Y0 ⟶ Vt} {tR : Vt ⟶ W} (hV : eV ≫ tR = γ') {eA : X1 ⟶ Ua}
    {aR : Ua ⟶ W} (hA : eA ≫ aR = δ') {eU : X0 ⟶ Uc} {cT : Uc ⟶ Vt} {cA : Uc ⟶ Ua}
    (hc : cA ≫ aR = cT ≫ tR) {kT : X0 ⟶ Vt} (hT1 : eU ≫ cT = kT) (hT2 : α' ≫ eV = kT)
    {kC : X0 ⟶ Ua} (hC1 : eU ≫ cA = kC) (hC2 : β' ≫ eA = kC) :
    CategoryTheory.Functor.TransportCoherent (modulePullbackTriangle B S hS hαγ)
      (eqToIso (congrArg (modulePullback B S hS) hab)) (modulePullbackTriangle B S hS hβδ)
      (PushoutModules.squareOverlap cT tR cA aR hc) (modulePullbackTriangle B S hS hV)
      (modulePullbackTriangle B S hS hA) (modulePullbackSquare B S hS hT1 hT2)
      (modulePullbackSquare B S hS hC1 hC2) := by
  have hkR : kT ≫ tR = a0 := by rw [← hT2, Category.assoc, hV, hαγ]
  have hkL : kC ≫ aR = b0 := by rw [← hC2, Category.assoc, hA, hβδ]
  have hyR : eU ≫ cT ≫ tR = a0 := by rw [← Category.assoc, hT1, hkR]
  have hyL : eU ≫ cA ≫ aR = b0 := by rw [← Category.assoc, hC1, hkL]
  refine CategoryTheory.Functor.transportCoherent_of _ _ _ (modulePullbackCompIso B S hS cT tR)
    (eqToIso (congrArg (modulePullback B S hS) hc.symm)) (modulePullbackCompIso B S hS cA aR)
    _ _ _ _ _ _ (modulePullbackTriangle B S hS hkR) (modulePullbackTriangle B S hS hkL)
    (modulePullbackTriangle B S hS hyR) (modulePullbackTriangle B S hS hyL)
    (fun K => modulePullbackTriangle_comp_app hC2 hA hβδ hkL K)
    (fun K => modulePullbackTriangle_comp_app hT2 hV hαγ hkR K) (fun K => ?_) (fun K => ?_)
    (fun K => ?_)
  · have h := modulePullbackTriangle_comp_app hT1 rfl hyR hkR K
    rw [modulePullbackTriangle_rfl] at h
    exact h
  · have h := modulePullbackTriangle_comp_app hC1 rfl hyL hkL K
    rw [modulePullbackTriangle_rfl] at h
    exact h
  · rw [eqToIso.hom, eqToIso.hom]
    exact CategoryTheory.Functor.iso_hom_app_congr₂ (fun (q : Uc ⟶ W) (r : X0 ⟶ W) => eU ≫ q = r)
      (modulePullback B S hS) (modulePullback B S hS) (modulePullback B S hS eU)
      (fun _ _ h => modulePullbackTriangle B S hS h) hc.symm hab hyR hyL K

/-! ### Modules glue along a square identified with the square of Stacks 08KV -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

variable {D} in
/-- The conditions of Stacks 08KB on a module depend only on its isomorphism class. -/
theorem IsCoherentModule.of_iso {T : SchemesOver D.Y}
    {F G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (e : F ≅ G)
    (h : D.IsCoherentModule T F) : D.IsCoherentModule T G := by
  have hs : D.support T F = D.support T G := supportOfSheaf_eq_of_iso B S hS (D.space T) e
  obtain ⟨hp, hU, hpr⟩ := h.properSupport
  refine ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e h.quasicoherent,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e h.finitePresentation,
    IsFlatOver.of_iso B S hS _ e h.flat, hp, ?_⟩
  rw [← hs]
  exact ⟨hU, hpr⟩

/-- A module on a space isomorphic to `Y` over `Z` is the pullback of a module on `Y` with the same
quasi-coherence, flatness and finite presentation. -/
private theorem exists_modulePullback_iso_of_iso {X Y Z : AlgebraicSpaces B S hS}
    (hcoh : ModulePushforwardCoherence B S hS) (e : X ≅ Y) {p : X ⟶ Z} {q : Y ⟶ Z}
    (hpq : e.hom ≫ q = p) (M : Modules.{u, u} B S hS X.1 X.2) (hq : M.IsQuasicoherentOnSite)
    (hfl : IsFlatOver B S hS X.2 p.hom M) (hfp : M.IsFinitePresentationOnSite) :
    ∃ (K : Modules.{u, u} B S hS Y.1 Y.2) (_ : (modulePullback B S hS e.hom).obj K ≅ M),
      K.IsQuasicoherentOnSite ∧ IsFlatOver B S hS Y.2 q.hom K ∧
        K.IsFinitePresentationOnSite := by
  have hq' := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS e.inv M hq
  have := hq'
  have hpb : IsPullback e.inv q p (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← hpq, Iso.inv_hom_id_assoc]⟩
  exact ⟨_, (hcoh.modulePullbackEquivalence e).counitIso.app M, hq',
    isFlatOver_modulePullback B S hS hpb M hfl,
    isFinitePresentationOnSite_modulePullback B S hS e.inv M hfp⟩

open PushoutModules in
/-- **Modules glue along a square of test schemes identified with the square of Stacks 08KV.**
Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces with a
pushout `Y'`, and `g : X_{TY'} ⟶ Y'` a morphism locally of finite presentation over which the
modules satisfying the conditions of Stacks 08KB on `X_{TY'}` are exactly the quasi-coherent ones
flat over `Y'`. If the base changes `X_{TY}`, `X_{TX'}`, `X_{TX}` are identified with the spaces
`V`, `U'`, `U` of Stacks 08KV compatibly with all the maps, and `TY ⟶ TY'` is a thickening, then
modules glue along the square. -/
theorem modulesGlue_of_identification {TX TY TX' TY' : SchemesOver D.Y} {α : TX ⟶ TY}
    {β : TX ⟶ TX'} {γ : TY ⟶ TY'} {δ : TX' ⟶ TY'} (hw : α ≫ γ = β ≫ δ)
    (hγ : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map γ.left))
    {X : AlgebraicSpaces B S hS} (i : X ⟶ (schemeSpaceFunctor B S hS).obj TX'.left)
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj TY.left)
    [HasPushout i f] (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (g : D.space TY' ⟶ pushout i f) (hg : IsLocallyOfFinitePresentation B S hS g.hom)
    (hflat : ∀ M, D.IsCoherentModule TY' M → IsFlatOver B S hS (D.space TY').2 g.hom M)
    (hflat' : ∀ M, M.IsQuasicoherentOnSite → IsFlatOver B S hS (D.space TY').2 g.hom M →
      IsFlatOver B S hS (D.space TY').2 (D.projection TY').hom M)
    (eV : D.space TY ≅ targetSpace i f g) (hV : eV.hom ≫ targetRestriction i f g = D.relativeMap γ)
    (hVf : eV.hom ≫ pullback.fst (pushout.inr i f) g = D.projection TY)
    (eA : D.space TX' ≅ ambientSpace i f g)
    (hA : eA.hom ≫ ambientRestriction i f g = D.relativeMap δ)
    (hAf : eA.hom ≫ pullback.fst (pushout.inl i f) g = D.projection TX')
    (eU : D.space TX ≅ commonSpace i f g)
    (hT : eU.hom ≫ commonToTarget i f g = D.relativeMap α ≫ eV.hom)
    (hC : eU.hom ≫ commonToAmbient i f g = D.relativeMap β ≫ eA.hom) :
    D.ModulesGlue α β γ δ hw := by
  have hc := transportCoherent_modulePullback (B := B) (S := S) (hS := hS)
    (baseChangeMap_comp D.f α γ).symm (baseChangeMap_comp D.f β δ).symm
    (congrArg D.relativeMap hw) hV hA (commonToAmbient_comp_eq i f g) hT rfl hC rfl
  have hc' : CategoryTheory.Functor.TransportCoherent (D.compComparison α γ)
      (D.relativeMapComparison hw) (D.compComparison β δ)
      (squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
        (ambientRestriction i f g) (commonToAmbient_comp_eq i f g))
      (modulePullbackTriangle B S hS hV) (modulePullbackTriangle B S hS hA)
      (modulePullbackSquare B S hS hT rfl) (modulePullbackSquare B S hS hC rfl) := hc
  let hcoh := modulePushforwardCoherence B S hS
  have hE : ∀ {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y),
      (modulePullback B S hS e.hom).FullyFaithful := fun e =>
    (hcoh.modulePullbackEquivalence e).fullyFaithfulFunctor
  have hEU := hE eU
  have hL := isEquivalence_flatRestrictionFunctor_of_hasPushout i f g hi hf
  refine ⟨fun M N hM hN φY φZ hm => ?_, fun MY MX' θY hθ hMY hMX' => ?_⟩
  · exact CategoryTheory.Functor.hom_glue_of_transport hc' (hE eV) (hE eA) hEU
      (fun ψY ψZ h => TripleGluing.existsUnique_of_isEquivalence_lift hL
        ⟨hM.quasicoherent, hflat M hM⟩ ⟨hN.quasicoherent, hflat N hN⟩ ψY ψZ h) φY φZ hm
  · have := hθ
    have := hMY.quasicoherent
    have := hMX'.quasicoherent
    obtain ⟨KY, εY, hqY, hfY, hpY⟩ := exists_modulePullback_iso_of_iso hcoh eV hVf MY
      hMY.quasicoherent hMY.flat hMY.finitePresentation
    obtain ⟨KA, εA, hqA, hfA, hpA⟩ := exists_modulePullback_iso_of_iso hcoh eA hAf MX'
      hMX'.quasicoherent hMX'.flat hMX'.finitePresentation
    obtain ⟨θ'', hθ''⟩ : ∃ θ'' : (modulePullback B S hS (commonToTarget i f g)).obj KY ≅
        (modulePullback B S hS (commonToAmbient i f g)).obj KA,
        (modulePullback B S hS eU.hom).map θ''.hom =
          (modulePullbackSquare B S hS hT rfl).hom.app KY ≫
            (modulePullback B S hS (D.relativeMap α)).map εY.hom ≫ θY ≫
            (modulePullback B S hS (D.relativeMap β)).map εA.inv ≫
            (modulePullbackSquare B S hS hC rfl).inv.app KA :=
      ⟨hEU.preimageIso ((modulePullbackSquare B S hS hT rfl).app KY ≪≫
        (modulePullback B S hS (D.relativeMap α)).mapIso εY ≪≫ asIso θY ≪≫
        (modulePullback B S hS (D.relativeMap β)).mapIso εA.symm ≪≫
        (modulePullbackSquare B S hS hC rfl).symm.app KA), by
          rw [hEU.preimageIso_hom, hEU.map_preimage]
          rfl⟩
    have hT'' : FlatQuasicoherentTriple i f g ⟨KY, KA, θ''⟩ := ⟨hqY, hfY, hqA, hfA⟩
    obtain ⟨G, hPG, ζY, ζA, hζ⟩ := TripleGluing.exists_iso_of_isEquivalence_lift hL _ hT''
    have key := CategoryTheory.Functor.obj_glue_of_transport hc' θY εY εA θ''.hom hθ''
      ζY.hom ζA.hom hζ
    have hfpG : G.IsFinitePresentationOnSite :=
      (isFinitePresentationOnSite_iff_restrict_of_hasPushout i f g hi hf hg G hPG).2
        ⟨SheafOfModules.IsFinitePresentationOnSite.of_iso ζY.symm hpY,
          SheafOfModules.IsFinitePresentationOnSite.of_iso ζA.symm hpA⟩
    have := hfpG
    let eY := (modulePullbackTriangle B S hS hV).hom.app G ≫
      (modulePullback B S hS eV.hom).map ζY.hom ≫ εY.hom
    let eX' := (modulePullbackTriangle B S hS hA).hom.app G ≫
      (modulePullback B S hS eA.hom).map ζA.hom ≫ εA.hom
    have hcY : D.IsCoherentModule TY ((modulePullback B S hS (D.relativeMap γ)).obj G) :=
      IsCoherentModule.of_iso (asIso eY).symm hMY
    refine ⟨G, eY, eX', inferInstance, inferInstance,
      ⟨hPG.1, hfpG, hflat' G hPG.1 hPG.2, D.properSupport_of_thickening γ hγ G hPG.1
        inferInstance hcY.properSupport⟩, key⟩

open PushoutModules in
/-- **Modules glue along a square of test schemes over a pushout along a thickening and an affine
morphism.**  For a commutative square `α ≫ γ = β ≫ δ` of test schemes whose underlying square of
schemes is a pushout with `β` a thickening and `α` affine, modules satisfying the conditions of
Stacks 08KB glue along it.

The square is a pushout of algebraic spaces (Stacks 07SY), the base changes of its corners are the
spaces of Stacks 08KV for the projection `X_{TY'} ⟶ TY'`, which is of finite presentation, and
`TY ⟶ TY'` is a thickening (Stacks 07RT), across which properness of the support is carried. -/
theorem modulesGlue_of_isPushout {TX TY TX' TY' : SchemesOver D.Y} {α : TX ⟶ TY}
    {β : TX ⟶ TX'} {γ : TY ⟶ TY'} {δ : TX' ⟶ TY'} (hw : α ≫ γ = β ≫ δ)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map β.left))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map α.left)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map β.left)
      ((BigFppfOver.toScheme B S hS).map α.left) ((BigFppfOver.toScheme B S hS).map δ.left)
      ((BigFppfOver.toScheme B S hS).map γ.left)) :
    D.ModulesGlue α β γ δ hw := by
  have P : IsPushout ((schemeSpaceFunctor B S hS).map β.left)
      ((schemeSpaceFunctor B S hS).map α.left) ((schemeSpaceFunctor B S hS).map δ.left)
      ((schemeSpaceFunctor B S hS).map γ.left) :=
    isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS β.left α.left δ.left γ.left
      hi hsq
  have : HasPushout ((schemeSpaceFunctor B S hS).map β.left)
      ((schemeSpaceFunctor B S hS).map α.left) := P.hasPushout
  have hγ : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map γ.left) :=
    Stacks.Pushout.isThickening_of_isPushout_of_isThickening hsq hi
  have hi' : IsThickeningHom B S hS ((schemeSpaceFunctor B S hS).map β.left) :=
    FormalSpace.isThickeningHom_yonedaSpace_map B S hS β.left hi
  have hf' : IsAffineHom B S hS ((schemeSpaceFunctor B S hS).map α.left).hom :=
    isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance α.left).2 inferInstance)
  let e := P.isoPushout
  let eP := (ObjectProperty.ι _).mapIso e
  let g := D.projection TY' ≫ e.hom
  have hg : IsLocallyOfFinitePresentation B S hS g.hom :=
    (isFinitePresentation_comp_iso (D.space TY').2
      ((schemeSpaceFunctor B S hS).obj TY'.left).2
      (pushout ((schemeSpaceFunctor B S hS).map β.left)
        ((schemeSpaceFunctor B S hS).map α.left)).2 _ eP
      (D.isFinitePresentation_projection TY')).1
  have hfl : IsFlat B S hS e.hom.hom := isFlat_of_isIso eP.hom
    (pushout ((schemeSpaceFunctor B S hS).map β.left) ((schemeSpaceFunctor B S hS).map α.left)).2
  have hfl' : IsFlat B S hS e.inv.hom :=
    isFlat_of_isIso eP.inv ((schemeSpaceFunctor B S hS).obj TY'.left).2
  have hflat : ∀ M, D.IsCoherentModule TY' M → IsFlatOver B S hS (D.space TY').2 g.hom M :=
    fun M hM => by
      have := hM.quasicoherent
      exact isFlatOver_comp_of_isFlat B S hS _ _ M hM.flat hfl
  have hflat' : ∀ M : Modules.{u, u} B S hS (D.space TY').1 (D.space TY').2,
      M.IsQuasicoherentOnSite → IsFlatOver B S hS (D.space TY').2 g.hom M →
        IsFlatOver B S hS (D.space TY').2 (D.projection TY').hom M := fun M hq hM => by
    have := hq
    have h := isFlatOver_comp_of_isFlat B S hS g e.inv M hM hfl'
    have hge : g ≫ e.inv = D.projection TY' := by simp [g]
    rwa [hge] at h
  have hpbV : IsPullback (D.projection TY) (D.relativeMap γ)
      (pushout.inr ((schemeSpaceFunctor B S hS).map β.left)
        ((schemeSpaceFunctor B S hS).map α.left)) g :=
    (isPullback_baseChangeMap D.f γ).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp [e]) (by simp [g])
  have hpbA : IsPullback (D.projection TX') (D.relativeMap δ)
      (pushout.inl ((schemeSpaceFunctor B S hS).map β.left)
        ((schemeSpaceFunctor B S hS).map α.left)) g :=
    (isPullback_baseChangeMap D.f δ).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp [e]) (by simp [g])
  have hpbU : IsPullback (D.projection TX) (D.relativeMap (β ≫ δ))
      ((schemeSpaceFunctor B S hS).map β.left ≫ pushout.inl ((schemeSpaceFunctor B S hS).map β.left)
        ((schemeSpaceFunctor B S hS).map α.left)) g :=
    (isPullback_baseChangeMap D.f (β ≫ δ)).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp [e, CostructuredArrow.comp_left]) (by simp [g])
  refine D.modulesGlue_of_identification hw hγ _ _ hi' hf' g hg hflat hflat' hpbV.isoPullback
    hpbV.isoPullback_hom_snd hpbV.isoPullback_hom_fst hpbA.isoPullback hpbA.isoPullback_hom_snd
    hpbA.isoPullback_hom_fst hpbU.isoPullback ?_ ?_
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, commonToTarget_fst, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_fst, baseChangeMap_comp_inclusion]
    · rw [Category.assoc, Category.assoc, commonToTarget_restriction,
        IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd, ← baseChangeMap_comp, hw]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, commonToAmbient_fst, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_fst, baseChangeMap_comp_inclusion]
    · rw [Category.assoc, Category.assoc, commonToAmbient_restriction,
        IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd, ← baseChangeMap_comp]

/-- **Stacks 08KV supplies the gluing of modules of the reduction of Stacks 08LQ.**  For a
pushout of schemes over `S` along a thickening `i` and an affine morphism `f`, modules satisfying
the conditions of Stacks 08KB glue along every square of test schemes lying over it. -/
theorem modulesGlueOver_of_isPushout {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    D.ModulesGlueOver i f a b := by
  intro TX TY TX' TY' α β γ δ hw hX hY hX' hY' hα hβ hγ hδ
  subst hX hY hX' hY'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hα hβ hγ hδ
  subst hα hβ hγ hδ
  exact D.modulesGlue_of_isPushout hw hi hsq

end CoherentSituation

end AlgebraicGeometry.Space

/-! ### Stacks 08LQ -/

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square of schemes over `S` commutes as soon as its underlying square of schemes is a
pushout: the functor to schemes is faithful. -/
theorem comm_of_isPushout_toScheme {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y}
    {a : Z' ⟶ Y'} {b : Y ⟶ Y'}
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    f ≫ b = i ≫ a :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact hsq.w.symm)

/-- **Stacks Project, Tag 08LQ.**  In Situation 08KB, let `f : X ⟶ B` be a morphism of algebraic
spaces over `S` of finite presentation, and let

```
  Z ---i---> Z'
  |          |
  f          a
  v          v
  Y ---b---> Y'
```

be a pushout in the category of schemes over `S` with `Z ⟶ Z'` a thickening and `Z ⟶ Y` affine
(Stacks 07RT). Then the functor on fibre categories
`Coh_{X/B, Y'} ⟶ Coh_{X/B, Y} ×_{Coh_{X/B, Z}} Coh_{X/B, Z'}` is an equivalence.

Here `Coh_{X/B}` is the category of `AlgebraicGeometry.Space.CoherentSituation.categoryData`
fibred over the schemes over `S` by `AlgebraicGeometry.Space.coherentSiteProjection`, and the
functor is `Deformation.Artin.fiberSquareComparison` at its chosen pullbacks, for the square
`f ≫ b = i ≫ a` of schemes over `S`, which commutes by
`AlgebraicGeometry.Space.CoherentSituation.comm_of_isPushout_toScheme`.

The proof follows the source: the map `B(Y') ⟶ B(Y) ×_{B(Z)} B(Z')` is bijective (Stacks 07SY),
which fixes the morphism `Y' ⟶ B` (`fiberSquareComparison_isEquivalence_of_modulesGlueOver`),
and the statement becomes Stacks 08KV for the base change `X ×_B Y' ⟶ Y'`
(`modulesGlueOver_of_isPushout`). -/
@[stacks 08LQ]
theorem fiberSquareComparison_isEquivalence (D : CoherentSituation B S hS)
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : (coherentSiteProjection D.categoryData).IsFibered :=
      D.isFiberedInGroupoids_siteProjection.isFibered
    (Deformation.Artin.fiberSquareComparison (coherentSiteProjection D.categoryData)
      (coherentSiteProjection D.categoryData).chosenPullbacks f i b a
        (comm_of_isPushout_toScheme hsq)).IsEquivalence :=
  D.fiberSquareComparison_isEquivalence_of_modulesGlueOver
    (D.modulesGlueOver_of_isPushout i f a b hi hsq) (comm_of_isPushout_toScheme hsq).symm hi hsq

/-- **`Coh_{X/B}` satisfies the Rim–Schlessinger condition (RS) of Stacks 07WP.**  The pushouts
of spectra of local Artinian rings of (RS) are pushouts along a thickening and an affine morphism,
so this is Stacks 08LQ; it is the first sentence of the source's proof of Stacks 08W8. -/
theorem satisfiesRS (D : CoherentSituation B S hS) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.SatisfiesRS B S hS (coherentSiteProjection D.categoryData)
      D.isFiberedInGroupoids_siteProjection := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  intro X X' Y Y'
  exact (Deformation.Artin.satisfiesRS_of_forall_isEquivalence
    (p := coherentSiteProjection D.categoryData) D.isFiberedInGroupoids_siteProjection
    fun i j i' j' _ hi hj hpo => by
      have := hj
      exact D.fiberSquareComparison_isEquivalence i j i' j' hi hpo)

end AlgebraicGeometry.Space.CoherentSituation

end
