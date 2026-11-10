module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentObj

/-!
# Descent of vertical morphisms for `Coh_{X/Y}`

In Situation 08KB assume `Y` locally of finite presentation over `S`, and let `T = lim T_j` be a
cofiltered limit of affine schemes of the site, taken in schemes. A vertical morphism between the
pullbacks to `T` of two objects of `Coh_{X/Y}` over a stage `T_i` already comes from a vertical
morphism at a later stage. This is the descent condition `Deformation.Artin.DescentHom` of Stacks
07XL that makes the comparison functor `colim Coh_{X/Y, T_j} ⥤ Coh_{X/Y, T}` full, and it is the
fullness part of the proof of Stacks 08KD.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.mk_comp_eq_of` and
  `AlgebraicGeometry.Space.CoherentSituation.mk_comp_mk_eq_of`: a composite whose first factor is
  given by its base map and module comparison is a given morphism as soon as the composite
  comparison of modules is.
* `AlgebraicGeometry.Space.CoherentSituation.map_stageIso_eq`: the inverse image to `X_T` of an
  isomorphism of modules at a stage, given through its restriction.
* `AlgebraicGeometry.Space.CoherentSituation.exists_lift_comp_eq` and
  `AlgebraicGeometry.Space.CoherentSituation.exists_stage_lift`: the morphisms out of the object
  over the limit which the descended isomorphism produces.
* `AlgebraicGeometry.Space.CoherentSituation.descentHom_coherent`: the condition
  `Deformation.Artin.DescentHom` for `Coh_{X/Y}`.

## Implementation notes

Let `δ : x ⟶ x_i`, `ε : y ⟶ y_i` lie over `T ⟶ T_i` and let `φ : x ⟶ y` be vertical. The two
structure morphisms `T_i ⟶ Y` of `x_i` and `y_i` agree on `T`, hence on a later stage `T_k` by
Stacks 05N0; above that stage both objects pull back to test schemes `T_k` with one structure
morphism, and the module comparisons of `δ` and of `φ ≫ ε` give an isomorphism between the inverse
images to `X_T` of the two pulled-back modules. The fullness clause of Stacks 07V7 for isomorphisms
(`AlgebraicGeometry.Space.CoherentSituation.exists_stage_iso_of_cone`) descends it to a still later
stage `T_j`. The morphism of `Coh_{X/Y}` it defines, from the pullback of `x_i` to `y_i`, factors
through the pullback of `y_i` by a vertical morphism, which is the one sought.

That the composite with the morphism `x ⟶ x_j` is `φ ≫ ε` is a computation with the comparisons
of inverse images of Stacks 03LU only: the composition of `Coh_{X/Y}` is read, through
`AlgebraicGeometry.Space.CoherentHom.comp_fibre` and
`AlgebraicGeometry.Space.CoherentSituation.compComparison_app`, as the comparison
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison` of the descent files, and the
restriction `AlgebraicGeometry.Space.moduleHomRestrict` of Stacks 07V7 is unfolded into the same
comparisons, which the cocycle
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison_trans_hom` then cancels.

Every statement is arranged so that no two comparisons of inverse images are ever identified by
unfolding: the elaborator and the kernel both unfold
`AlgebraicGeometry.Space.CoherentSituation.compComparison` and
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison` into the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU rather than compare their arguments,
which does not finish, as soon as those arguments are only definitionally equal (a base map read
off a structure literal, the cone projections of `CategoryTheory.Limits.Cone.extend`, a test scheme
of a pullback object). So the stage lemmas take the morphism into the stage object as an opaque
variable, the cone over the stages is the explicit
`AlgebraicGeometry.Space.CoherentSituation.stageTestConeAt`, and the isomorphism handed to Stacks
07V7 is written in exactly the form the stage lemma expects.

## References

* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison pullbackComparison_trans_hom
  pullbackComparison_trans_inv)

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

section PullbackLift

/-- **A composite with a morphism given by its base map and module comparison.** The composite of
`(b, f) : A₀ ⟶ X` with `n : X ⟶ A` is `m : A₀ ⟶ A` as soon as the base maps compose to the base
map of `m` and the composite comparison `X_{b ≫ n}^*F_A ⟶ X_b^*X_n^*F_A ⟶ X_b^*F_X ⟶ F_{A₀}` is the
comparison of `m`. -/
theorem mk_comp_eq_of {A₀ X A : CoherentObject D} (b : A₀.T ⟶ X.T)
    (f : (modulePullback B S hS (D.relativeMap b)).obj X.F ⟶ A₀.F) (hf : IsIso f)
    (n : CoherentHom X A) (m : CoherentHom A₀ A) (hb : b ≫ n.base = m.base)
    (h : (D.compComparison b n.base).hom.app A.F ≫
        (modulePullback B S hS (D.relativeMap b)).map n.fibre ≫ f =
      eqToHom (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj A.F) hb) ≫
        m.fibre) :
    CoherentHom.comp ⟨b, f, hf⟩ n = m :=
  coherentHom_eq_of_heq hb (by
    rw [CoherentHom.comp_fibre]
    dsimp only
    exact heq_of_eq_eqToHom_comp
      (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj A.F) hb) m.fibre h)

/-- The form of `mk_comp_eq_of` with both factors given by their base maps and module
comparisons. -/
theorem mk_comp_mk_eq_of {A₀ X A : CoherentObject D} (b : A₀.T ⟶ X.T)
    (f : (modulePullback B S hS (D.relativeMap b)).obj X.F ⟶ A₀.F) (hf : IsIso f)
    (b' : X.T ⟶ A.T) (f' : (modulePullback B S hS (D.relativeMap b')).obj A.F ⟶ X.F)
    (hf' : IsIso f') (m : CoherentHom A₀ A) (hb : b ≫ b' = m.base)
    (h : (D.compComparison b b').hom.app A.F ≫
        (modulePullback B S hS (D.relativeMap b)).map f' ≫ f =
      eqToHom (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj A.F) hb) ≫
        m.fibre) :
    CoherentHom.comp ⟨b, f, hf⟩ ⟨b', f', hf'⟩ = m :=
  coherentHom_eq_of_heq hb (by
    rw [CoherentHom.comp_fibre]
    dsimp only
    exact heq_of_eq_eqToHom_comp
      (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj A.F) hb) m.fibre h)

/-- The composite comparison of `mk_comp_eq_of`, written through the comparison of Stacks 03LU at
a factorization `X_b ≫ X_n = X_m`. -/
theorem compComparison_app_eq {A₀ X A : CoherentObject D} (b : A₀.T ⟶ X.T) (n : X.T ⟶ A.T)
    (m : A₀.T ⟶ A.T) (hb : b ≫ n = m)
    (hr : D.relativeMap b ≫ D.relativeMap n = D.relativeMap m) :
    (D.compComparison b n).hom.app A.F =
      eqToHom (congrArg (fun t => (modulePullback B S hS (D.relativeMap t)).obj A.F) hb) ≫
        (pullbackComparison B S hS (D.relativeMap b) (D.relativeMap n) (D.relativeMap m) hr
          A.F).hom := by
  subst hb
  rw [← Iso.app_hom, D.compComparison_app]
  simp

end PullbackLift

/-- **Lifting a morphism through a morphism over a factorization of its base map.** Let
`δ : A₀ ⟶ A`, `ζ : A₀ ⟶ A'` and `dX : X ⟶ A` be morphisms of `Coh_{X/Y}`, `b : T_{A₀} ⟶ T_X`
with `b ≫ dX = δ` and `b ≫ h' = ζ` on base maps, and `g : X_{h'}^*F_{A'} ⟶ F_X` an isomorphism
whose inverse image along `X_b` is the comparison of the module comparisons of `ζ`, `δ` and `dX`.
Then there is a morphism `δ' : A₀ ⟶ X` over `b` with `δ' ≫ dX = δ` and `δ' ≫ (h', g) = ζ`. -/
theorem exists_lift_comp_eq {A₀ A A' X : CoherentObject D} (δ : CoherentHom A₀ A)
    (ζ : CoherentHom A₀ A') (dX : CoherentHom X A) (h' : X.T ⟶ A'.T) (b : A₀.T ⟶ X.T)
    (hb : D.relativeMap b ≫ D.relativeMap dX.base = D.relativeMap δ.base)
    (hc : D.relativeMap b ≫ D.relativeMap h' = D.relativeMap ζ.base)
    (hb' : b ≫ dX.base = δ.base) (hc' : b ≫ h' = ζ.base)
    (g : (modulePullback B S hS (D.relativeMap h')).obj A'.F ⟶ X.F) (hgi : IsIso g)
    (hg : (modulePullback B S hS (D.relativeMap b)).map g =
      (pullbackComparison B S hS (D.relativeMap b) (D.relativeMap h') (D.relativeMap ζ.base)
        hc A'.F).inv ≫ ζ.fibre ≫ inv δ.fibre ≫
      (pullbackComparison B S hS (D.relativeMap b) (D.relativeMap dX.base) (D.relativeMap δ.base)
        hb A.F).hom ≫ (modulePullback B S hS (D.relativeMap b)).map dX.fibre) :
    ∃ δ' : CoherentHom A₀ X, δ'.base = b ∧ δ'.comp dX = δ ∧ δ'.comp ⟨h', g, hgi⟩ = ζ := by
  let fδ := (modulePullback B S hS (D.relativeMap b)).map (inv dX.fibre) ≫
    (pullbackComparison B S hS (D.relativeMap b) (D.relativeMap dX.base) (D.relativeMap δ.base)
      hb A.F).inv ≫ δ.fibre
  refine ⟨⟨b, fδ, inferInstance⟩, rfl, ?_, ?_⟩
  · refine D.mk_comp_eq_of b fδ _ dX δ hb' ?_
    rw [D.compComparison_app_eq b dX.base δ.base hb' hb]
    simp only [fδ, Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_assoc]
  · refine D.mk_comp_mk_eq_of b fδ _ h' g hgi ζ hc' ?_
    rw [D.compComparison_app_eq b h' ζ.base hc' hc, hg]
    simp only [fδ, Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_assoc]
    simp only [Iso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The comparison of module comparisons, read at a later stage.** Let `b : Q ⟶ P_j`,
`ex : P_j ⟶ P_k` and `p_k = b ≫ ex` be morphisms of algebraic spaces, `u : P_k ⟶ Z`,
`u' : P_k ⟶ Z'` morphisms with composites `δ_b = p_k ≫ u`, `ζ_b = p_k ≫ u'`, and
`δ_f : δ_b^*F ⟶ F₀`, `ζ_f : ζ_b^*F' ⟶ F₀` isomorphisms. If `ψ : ex^*u'^*F' ≅ ex^*u^*F` restricts
along `b` to the isomorphism `p_k^*u'^*F' ≅ p_k^*u^*F` of `ζ_f` and `δ_f`, then the inverse image
along `b` of `ψ`, read as an isomorphism `(ex ≫ u')^*F' ≅ (ex ≫ u)^*F`, is the comparison of
`ζ_f` and `δ_f` along `b`. -/
theorem map_stageIso_eq {Q Pj Pk Z Z' : AlgebraicSpaces B S hS} (b : Q ⟶ Pj) (ex : Pj ⟶ Pk)
    (pk : Q ⟶ Pk) (u : Pk ⟶ Z) (u' : Pk ⟶ Z') (dxb : Pj ⟶ Z) (wx' : Pj ⟶ Z') (δb : Q ⟶ Z)
    (ζb : Q ⟶ Z') (hce : b ≫ ex = pk) (hw : ex ≫ u = dxb) (hw' : ex ≫ u' = wx')
    (hδ' : pk ≫ u = δb) (hζ' : pk ≫ u' = ζb) (hδj : b ≫ dxb = δb) (hζj : b ≫ wx' = ζb)
    {F : Modules.{u, u} B S hS Z.1 Z.2} {F' : Modules.{u, u} B S hS Z'.1 Z'.2}
    {F₀ : Modules.{u, u} B S hS Q.1 Q.2} (δf : (modulePullback B S hS δb).obj F ⟶ F₀)
    (ζf : (modulePullback B S hS ζb).obj F' ⟶ F₀) [IsIso δf] [IsIso ζf]
    (ψ : (modulePullback B S hS ex).obj ((modulePullback B S hS u').obj F') ≅
      (modulePullback B S hS ex).obj ((modulePullback B S hS u).obj F))
    (hψ : moduleHomRestrict ((modulePullback B S hS u').obj F') ((modulePullback B S hS u).obj F)
      b ex pk hce ψ.hom =
      ((pullbackComparison B S hS pk u' ζb hζ' F').symm ≪≫ asIso ζf ≪≫ (asIso δf).symm ≪≫
        pullbackComparison B S hS pk u δb hδ' F).hom) :
    (modulePullback B S hS b).map (pullbackComparison B S hS ex u' wx' hw' F' ≪≫ ψ ≪≫
        (pullbackComparison B S hS ex u dxb hw F).symm).hom =
      (pullbackComparison B S hS b wx' ζb hζj F').inv ≫ ζf ≫ inv δf ≫
        (pullbackComparison B S hS b dxb δb hδj F).hom := by
  have hmap : (modulePullback B S hS b).map ψ.hom =
      (pullbackComparison B S hS b ex pk hce _).inv ≫
        ((pullbackComparison B S hS pk u' ζb hζ' F').symm ≪≫ asIso ζf ≪≫ (asIso δf).symm ≪≫
          pullbackComparison B S hS pk u δb hδ' F).hom ≫
        (pullbackComparison B S hS b ex pk hce _).hom := by
    rw [← hψ]
    simp [moduleHomRestrict]
  have t₁ := pullbackComparison_trans_hom B S hS b ex u' wx' hw' pk hce ζb hζj hζ' F'
  have t₂ := pullbackComparison_trans_inv B S hS b ex u dxb hw pk hce δb hδj hδ' F
  have hA' : (modulePullback B S hS b).map (pullbackComparison B S hS ex u' wx' hw' F').hom =
      (pullbackComparison B S hS b wx' ζb hζj F').inv ≫
        (pullbackComparison B S hS pk u' ζb hζ' F').hom ≫
        (pullbackComparison B S hS b ex pk hce _).hom := by
    rw [← t₁, Iso.inv_hom_id_assoc]
  have hA : (modulePullback B S hS b).map (pullbackComparison B S hS ex u dxb hw F).inv =
      (pullbackComparison B S hS b ex pk hce _).inv ≫
        (pullbackComparison B S hS pk u δb hδ' F).inv ≫
        (pullbackComparison B S hS b dxb δb hδj F).hom := by
    rw [← Category.assoc, ← t₂, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp]
  rw [hA', hmap, hA]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- **The descent of a morphism at a stage.** Let `δ : A₀ ⟶ A` and `ζ : A₀ ⟶ A'` be morphisms of
`Coh_{X/Y}` whose base maps factor as `π_k ≫ u` and `π_k ≫ u'` through a test scheme `W`, let
`dX : X ⟶ A` have base map `ex ≫ u` with `ex : T_X ⟶ W`, and let `π_j ≫ ex = π_k`. If an
isomorphism `ψ : X_{ex}^*X_{u'}^*F_{A'} ≅ X_{ex}^*X_u^*F_A` restricts along `X_{π_j}` to the
isomorphism of the module comparisons of `ζ` and `δ`, then there are morphisms `δ' : A₀ ⟶ X` over
`π_j` and `n : X ⟶ A'` over `ex ≫ u'` with `δ' ≫ dX = δ` and `δ' ≫ n = ζ`. -/
theorem exists_stage_lift {A₀ A A' X : CoherentObject D} (δ : CoherentHom A₀ A)
    (ζ : CoherentHom A₀ A') (dX : CoherentHom X A) {W : SchemesOver D.Y} (ex : X.T ⟶ W)
    (u : W ⟶ A.T) (u' : W ⟶ A'.T) (πj : A₀.T ⟶ X.T) (πk : A₀.T ⟶ W) (hπ : πj ≫ ex = πk)
    (hdX : dX.base = ex ≫ u) (hδ : δ.base = πk ≫ u) (hζ : ζ.base = πk ≫ u')
    (ψ : (modulePullback B S hS (D.relativeMap ex)).obj
        ((modulePullback B S hS (D.relativeMap u')).obj A'.F) ≅
      (modulePullback B S hS (D.relativeMap ex)).obj
        ((modulePullback B S hS (D.relativeMap u)).obj A.F))
    (hψ : moduleHomRestrict ((modulePullback B S hS (D.relativeMap u')).obj A'.F)
      ((modulePullback B S hS (D.relativeMap u)).obj A.F) (D.relativeMap πj) (D.relativeMap ex)
      (D.relativeMap πk)
      ((baseChangeMap_comp D.f πj ex).symm.trans (congrArg (baseChangeMap D.f) hπ)) ψ.hom =
      ((pullbackComparison B S hS (D.relativeMap πk) (D.relativeMap u') (D.relativeMap ζ.base)
          ((baseChangeMap_comp D.f πk u').symm.trans (congrArg (baseChangeMap D.f) hζ.symm))
          A'.F).symm ≪≫ asIso ζ.fibre ≪≫ (asIso δ.fibre).symm ≪≫
        pullbackComparison B S hS (D.relativeMap πk) (D.relativeMap u) (D.relativeMap δ.base)
          ((baseChangeMap_comp D.f πk u).symm.trans (congrArg (baseChangeMap D.f) hδ.symm))
          A.F).hom) :
    ∃ (δk : CoherentHom A₀ X) (n : CoherentHom X A'), δk.base = πj ∧ n.base = ex ≫ u' ∧
      δk.comp dX = δ ∧ δk.comp n = ζ := by
  have hce : D.relativeMap πj ≫ D.relativeMap ex = D.relativeMap πk :=
    (baseChangeMap_comp D.f πj ex).symm.trans (congrArg (baseChangeMap D.f) hπ)
  have hζ' : D.relativeMap πk ≫ D.relativeMap u' = D.relativeMap ζ.base :=
    (baseChangeMap_comp D.f πk u').symm.trans (congrArg (baseChangeMap D.f) hζ.symm)
  have hδ' : D.relativeMap πk ≫ D.relativeMap u = D.relativeMap δ.base :=
    (baseChangeMap_comp D.f πk u).symm.trans (congrArg (baseChangeMap D.f) hδ.symm)
  have hw : D.relativeMap ex ≫ D.relativeMap u = D.relativeMap dX.base := by
    rw [hdX]
    exact (baseChangeMap_comp D.f ex u).symm
  have hw' : D.relativeMap ex ≫ D.relativeMap u' = D.relativeMap (ex ≫ u') :=
    (baseChangeMap_comp D.f ex u').symm
  have hδj : D.relativeMap πj ≫ D.relativeMap dX.base = D.relativeMap δ.base := by
    rw [← hw, ← Category.assoc, hce, hδ']
  have hζj : D.relativeMap πj ≫ D.relativeMap (ex ≫ u') = D.relativeMap ζ.base := by
    rw [← hw', ← Category.assoc, hce, hζ']
  have hjw : πj ≫ dX.base = δ.base := by
    rw [hdX, ← Category.assoc, hπ, hδ]
  have hjw' : πj ≫ (ex ≫ u') = ζ.base := by
    rw [← Category.assoc, hπ, hζ]
  let gI := pullbackComparison B S hS (D.relativeMap ex) (D.relativeMap u')
      (D.relativeMap (ex ≫ u')) hw' A'.F ≪≫ ψ ≪≫
    (pullbackComparison B S hS (D.relativeMap ex) (D.relativeMap u)
      (D.relativeMap dX.base) hw A.F).symm
  have hg₀ : (modulePullback B S hS (D.relativeMap πj)).map gI.hom =
      (pullbackComparison B S hS (D.relativeMap πj) (D.relativeMap (ex ≫ u'))
        (D.relativeMap ζ.base) hζj A'.F).inv ≫ ζ.fibre ≫ inv δ.fibre ≫
      (pullbackComparison B S hS (D.relativeMap πj) (D.relativeMap dX.base)
        (D.relativeMap δ.base) hδj A.F).hom :=
    map_stageIso_eq (D.relativeMap πj) (D.relativeMap ex) (D.relativeMap πk) (D.relativeMap u)
      (D.relativeMap u') (D.relativeMap dX.base) (D.relativeMap (ex ≫ u')) (D.relativeMap δ.base)
      (D.relativeMap ζ.base) hce hw hw' hδ' hζ' hδj hζj δ.fibre ζ.fibre ψ hψ
  have hg : (modulePullback B S hS (D.relativeMap πj)).map (gI.hom ≫ dX.fibre) =
      (pullbackComparison B S hS (D.relativeMap πj) (D.relativeMap (ex ≫ u'))
        (D.relativeMap ζ.base) hζj A'.F).inv ≫ ζ.fibre ≫ inv δ.fibre ≫
      (pullbackComparison B S hS (D.relativeMap πj) (D.relativeMap dX.base)
        (D.relativeMap δ.base) hδj A.F).hom ≫
      (modulePullback B S hS (D.relativeMap πj)).map dX.fibre := by
    rw [CategoryTheory.Functor.map_comp, hg₀]
    simp only [Category.assoc]
  obtain ⟨δk, hδk, hE₁, hE₂⟩ := D.exists_lift_comp_eq δ ζ dX (ex ≫ u') πj hδj hζj hjw hjw'
    (gI.hom ≫ dX.fibre) inferInstance hg
  exact ⟨δk, _, hδk, rfl, hE₁, hE₂⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigAffineFppf B S hS)
  (c : Cone E) (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- **The descent of vertical morphisms of Stacks 07XL for `Coh_{X/Y}`.** Let `Y` be locally of
finite presentation over `S` and let `T = lim T_j` be a cofiltered limit of affine schemes of the
site, taken in schemes. A vertical morphism `φ : x ⟶ y` over `T` between objects with morphisms
`δ : x ⟶ x_i`, `ε : y ⟶ y_i` over `T ⟶ T_i` comes from a vertical morphism `x_k ⟶ y_k` between
pullbacks of `x_i`, `y_i` to a later stage. This is the fullness half of the proof of Stacks 08KD,
by Stacks 05N0 and the fullness clause of Stacks 07V7. -/
theorem descentHom_coherent (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    Deformation.Artin.DescentHom (coherentSiteProjection D.categoryData)
      (E ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let p := coherentSiteProjection D.categoryData
  let incl := BigAffineFppf.inclusion B S hS
  let sSF := schemeSpaceFunctor B S hS
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  have hZ := B.contains_terminal
  rintro i ⟨A, hA⟩ ⟨A', hA'⟩ ⟨A₀, hA₀⟩ ⟨A₀', hA₀'⟩ δ ε hδ hε φ hφ
  change A.T.left = (E ⋙ incl).obj i at hA
  change A'.T.left = (E ⋙ incl).obj i at hA'
  change A₀.T.left = (incl.mapCone c).pt at hA₀
  change A₀'.T.left = (incl.mapCone c).pt at hA₀'
  change CoherentHom A₀ A at δ
  change CoherentHom A₀' A' at ε
  change CoherentHom A₀ A₀' at φ
  have hδb : δ.base.left = eqToHom hA₀ ≫ incl.map (c.π.app i) ≫ eqToHom hA.symm :=
    IsHomLift.fac' p ((incl.mapCone c).π.app i) δ
  have hεb : ε.base.left = eqToHom hA₀' ≫ incl.map (c.π.app i) ≫ eqToHom hA'.symm :=
    IsHomLift.fac' p ((incl.mapCone c).π.app i) ε
  have hφb : φ.base.left = eqToHom hA₀ ≫ 𝟙 _ ≫ eqToHom hA₀'.symm :=
    IsHomLift.fac' p (𝟙 (incl.mapCone c).pt) φ
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : CoherentHom A₀ A', φ.comp ε = ζ := ⟨_, rfl⟩
  have hζb : ζ.base.left = eqToHom hA₀ ≫ incl.map (c.π.app i) ≫ eqToHom hA'.symm := by
    rw [← hζdef]
    change φ.base.left ≫ ε.base.left = _
    rw [hφb, hεb]
    simp
  let g := sSF.map (eqToHom hA.symm) ≫ A.T.hom
  let g' := sSF.map (eqToHom hA'.symm) ≫ A'.T.hom
  have hA₀g : A₀.T.hom = sSF.map (eqToHom hA₀ ≫ incl.map (c.π.app i)) ≫ g := by
    have hw := δ.base.w
    change sSF.map δ.base.left ≫ A.T.hom = A₀.T.hom at hw
    rw [← hw, hδb]
    simp only [g, Functor.map_comp, Category.assoc]
  have hA₀g' : A₀.T.hom = sSF.map (eqToHom hA₀ ≫ incl.map (c.π.app i)) ≫ g' := by
    have hw := ζ.base.w
    change sSF.map ζ.base.left ≫ A'.T.hom = A₀.T.hom at hw
    rw [← hw, hζb]
    simp only [g', Functor.map_comp, Category.assoc]
  have hgg : sSF.map (incl.map (c.π.app i)) ≫ g = sSF.map (incl.map (c.π.app i)) ≫ g' := by
    have h := hA₀g.symm.trans hA₀g'
    rw [Functor.map_comp, Category.assoc, Category.assoc] at h
    exact (cancel_epi (sSF.map (eqToHom hA₀))).1 h
  obtain ⟨k, s, hs⟩ := D.exists_stage_structureMap_eq E c hc hY g g' hgg
  let k' : Over i := Over.mk s
  let Tsys := D.stageTestSystem E g
  let u : Tsys.obj k' ⟶ A.T := CostructuredArrow.homMk (incl.map (E.map s) ≫ eqToHom hA.symm)
    (by
      change sSF.map (incl.map (E.map s) ≫ eqToHom hA.symm) ≫ A.T.hom =
        sSF.map (incl.map (E.map s)) ≫ g
      rw [Functor.map_comp, Category.assoc])
  let u' : Tsys.obj k' ⟶ A'.T := CostructuredArrow.homMk (incl.map (E.map s) ≫ eqToHom hA'.symm)
    (by
      change sSF.map (incl.map (E.map s) ≫ eqToHom hA'.symm) ≫ A'.T.hom =
        sSF.map (incl.map (E.map s)) ≫ g
      rw [Functor.map_comp, Category.assoc, hs])
  let v : A₀.T ≅ (D.stageTestCone E c g).pt := CostructuredArrow.isoMk (eqToIso hA₀) (by
    change sSF.map (eqToHom hA₀) ≫ (sSF.map (incl.map (c.π.app i)) ≫ g) = A₀.T.hom
    rw [hA₀g, Functor.map_comp, Category.assoc])
  let cT := D.stageTestConeAt E c g v
  let πT : ∀ j : Over i, A₀.T ⟶ Tsys.obj j := fun j => cT.π.app j
  have hπleft : ∀ j : Over i, (πT j).left = eqToHom hA₀ ≫ incl.map (c.π.app j.left) :=
    fun j => rfl
  have hδdec : δ.base = πT k' ≫ u := by
    apply CostructuredArrow.hom_ext
    rw [hδb, CostructuredArrow.comp_left, hπleft]
    change _ = (eqToHom hA₀ ≫ incl.map (c.π.app k)) ≫ incl.map (E.map s) ≫ eqToHom hA.symm
    rw [Category.assoc, ← Category.assoc (incl.map (c.π.app k)), ← Functor.map_comp, c.w]
  have hζdec : ζ.base = πT k' ≫ u' := by
    apply CostructuredArrow.hom_ext
    rw [hζb, CostructuredArrow.comp_left, hπleft]
    change _ = (eqToHom hA₀ ≫ incl.map (c.π.app k)) ≫ incl.map (E.map s) ≫ eqToHom hA'.symm
    rw [Category.assoc, ← Category.assoc (incl.map (c.π.app k)), ← Functor.map_comp, c.w]
  let χ := (pullbackComparison B S hS (D.relativeMap (πT k')) (D.relativeMap u')
        (D.relativeMap ζ.base)
          ((baseChangeMap_comp D.f (πT k') u').symm.trans (congrArg (baseChangeMap D.f) hζdec.symm))
          A'.F).symm ≪≫ asIso ζ.fibre ≪≫ (asIso δ.fibre).symm ≪≫
        pullbackComparison B S hS (D.relativeMap (πT k')) (D.relativeMap u) (D.relativeMap δ.base)
          ((baseChangeMap_comp D.f (πT k') u).symm.trans (congrArg (baseChangeMap D.f) hδdec.symm))
          A.F
  obtain ⟨j, e, ψ, hψ⟩ := D.exists_stage_iso_of_cone Tsys cT hZ
    (fun e => D.isAffineHom_stageSpaceSystem_map E g e) (D.isQuasiCompactSpace_stageSpaceSystem E g)
    (D.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
    (D.isLimit_stageSpaceConeAt E c hc g v)
    (D.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
    k' _ _ (isFinitePresentationOnSite_modulePullback B S hS (D.relativeMap u') _
      A'.finitePresentation)
    (isFinitePresentationOnSite_modulePullback B S hS (D.relativeMap u) _ A.finitePresentation) χ
  let xk := D.pullbackObject' hst A (Tsys.map e ≫ u)
  let yk := D.pullbackObject' hst A' (Tsys.map e ≫ u')
  let dx := D.pullbackHom' hst A (Tsys.map e ≫ u)
  let dy := D.pullbackHom' hst A' (Tsys.map e ≫ u')
  obtain ⟨δk, n, hδk, hn, hE₁, hE₂⟩ := D.exists_stage_lift (X := xk) δ ζ dx
    (Tsys.map e) u u' (πT j) (πT k') (cT.w e) rfl hδdec hζdec ψ hψ
  obtain ⟨ψk, hψk₁, hψk₂⟩ := D.exists_fillIn dy n (𝟙 _)
    ((Category.id_comp _).trans (by rw [hn]; rfl))
  have hej : e.left ≫ s = j.hom := Over.w e
  refine ⟨j.left, j.hom, ⟨xk, rfl⟩, ⟨yk, rfl⟩, dx, dy, δk, ψk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsHomLift.of_fac' p _ _ rfl hA ?_
    change incl.map (E.map e.left) ≫ (incl.map (E.map s) ≫ eqToHom hA.symm) =
      𝟙 _ ≫ incl.map (E.map j.hom) ≫ eqToHom hA.symm
    rw [Category.id_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, hej]
  · refine IsHomLift.of_fac' p _ _ rfl hA' ?_
    change incl.map (E.map e.left) ≫ (incl.map (E.map s) ≫ eqToHom hA'.symm) =
      𝟙 _ ≫ incl.map (E.map j.hom) ≫ eqToHom hA'.symm
    rw [Category.id_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, hej]
  · refine IsHomLift.of_fac' p _ _ hA₀ rfl ?_
    change δk.base.left = _
    rw [hδk]
    rfl
  · refine IsHomLift.of_fac' p _ _ rfl rfl ?_
    change ψk.base.left = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [hψk₁, Category.id_comp, Category.id_comp]
  · exact hE₁
  · exact (congrArg (CoherentHom.comp δk) hψk₂).trans (hE₂.trans hζdef.symm)

end AlgebraicGeometry.Space.CoherentSituation

end
