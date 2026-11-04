module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingStalkCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkFiberBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingPullbackGenericCriterion

/-!
# The stalk computation in the proof of Stacks 0AF0

At a geometric point `ȳ` of `f⁻¹(Z)` with image `x̄ = f(ȳ)`, the source's proof of Stacks 0AF0
identifies the fibre at `x̄` of the module `K = Ker(j_*ℋ ⊕ f_*𝒢 → (f ∘ j')_*𝒢|_V)` of
Stacks 0AEX with the fibre product `(j_*ℋ)_x̄ ×_{(j'_*𝒢|_V)_ȳ} 𝒢_ȳ` (a diagram chase it omits,
using Stacks 0AER on fibres), and then reads the second component `f^*K ⟶ 𝒢` of the counit of
Stacks 0AEY on the geometric stalk at `ȳ` as the generic map
`𝒪_{Y,ȳ} ⊗ (N ×_Q P) ⟶ P` of the stalk glueing datum.

## Main results

* `CategoryTheory.Adjunction.isPullback_paste_squareTranspose` and
  `CategoryTheory.Adjunction.exists_isPullback_paste_squareTranspose`: the omitted chase in the
  abstract comma setting of `toCommaPullbackAdjunction`, through a functor preserving pullbacks.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_isPullback_glueingKernel_fiber`: the
  chase for the situation.
* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_glueingCounitRight_of_isPullback`:
  granted the cartesian square of Stacks 0AER on fibres at `ȳ` and the bijectivity of the generic
  map of the stalk glueing datum, the counit component is bijective on the geometric stalk at `ȳ`.

## Implementation notes

The objects of the pasted square reach the elementwise statements through several syntactically
different but definitionally equal spellings (the category of `𝒪`-modules as `Modules` or as
sheaves of modules over the ring sheaf of the structure sheaf, the stalk ring as `ringFiber` or
as a fibre of a presheaf).  The elementwise lemmas are therefore stated with their coercions'
categories and objects given explicitly, and the comparison `θ` and the transpose of the map of
the triple enter through variables equal to them, so that no comparison has to unfold them.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {E : Type u₁} [Category.{v₁} E] {A : Type u₂} [Category.{v₂} A]
    {Bb : Type u₃} [Category.{v₃} Bb] {T : Type u₄} [Category.{v₄} T]
    {F : E ⥤ A} {F' : A ⥤ E} {G : E ⥤ Bb} {G' : Bb ⥤ E}
    {L : A ⥤ T} {L' : T ⥤ A} {R : Bb ⥤ T} {R' : T ⥤ Bb} {N : E ⥤ T} {N' : T ⥤ E}

/-- **The first canonical map of Stacks 0AEX, transposed, is the square transpose of the
triple.**  In the setting of `toCommaPullbackAdjunction`, the transpose along `G ⊣ G'` of the
first canonical map `r` followed by the comparison `pG⁻¹ : N' ⟶ G' ∘ R'` is the square transpose
of the structure arrow of the comma object. -/
theorem homEquiv_symm_r_comp_eq_squareTranspose
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N')
    (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R) (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN) (X : Comma L R) :
    (adjG.homEquiv _ _).symm (r.app X ≫ pG.inv.app (R.obj X.right)) =
      squareTranspose adjF adjL adjG adjR αIso.inv X.left X.hom := by
  have hinv : αIso.inv = cG.hom ≫ cF.inv := by
    ext M
    rw [← cancel_epi (αIso.hom.app M), Iso.hom_inv_id_app, hα]
    simp
  have hconj : conjugateEquiv (adjF.comp adjL) (adjG.comp adjR) αIso.inv =
      (pFmid.hom ≫ eN) ≫ pG.inv := by
    rw [hinv, ← conjugateEquiv_comp (adjF.comp adjL) adjN (adjG.comp adjR), hpF]
    congr 1
    refine (Iso.comp_hom_eq_id pG).mp ?_
    rw [← hpG, conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
  rw [squareTranspose, hconj]
  congr 1
  subst hr
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Comma.natTrans_app, Functor.comp_obj, Comma.fst_obj, Comma.snd_obj, Category.assoc,
    homEquiv_unit, Functor.map_comp]
  have hn := pFmid.hom.naturality X.hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- **The pasting of the omitted chase of Stacks 0AF0, in the comma setting.**  The pullback
square of the module of Stacks 0AEX, read through a functor `J` preserving pullbacks at a comma
object `X`, pastes onto a pullback square whose top row is `J` of the direct image of the unit
`X.right ⟶ R' R X.right`. -/
theorem isPullback_paste_comma [HasPullbacks E] {E' : Type*} [Category* E']
    (adjR : R ⊣ R') (pG : R' ⋙ G' ≅ N')
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) (J : E ⥤ E') [PreservesLimitsOfShape WalkingCospan J]
    (X : Comma L R) {Y₁ Y₂ : E'} {θ : J.obj (G'.obj X.right) ⟶ Y₁}
    {w : J.obj (G'.obj (R'.obj (R.obj X.right))) ⟶ Y₂} {v : Y₁ ⟶ Y₂}
    (hH : IsPullback θ (J.map (G'.map (adjR.unit.app X.right))) v w) :
    IsPullback (J.map (κ₁.app X)) (J.map (κ₂.app X) ≫ θ)
      (J.map (r.app X ≫ pG.inv.app (R.obj X.right)) ≫ w) v := by
  subst hs
  have h1 := (Functor.map_isPullback ((evaluation (Comma L R) E).obj X) hKnat).map J
  have h2 : IsPullback (J.map (κ₁.app X)) (J.map (κ₂.app X))
      (J.map (r.app X ≫ pG.inv.app (R.obj X.right)))
      (J.map (G'.map (adjR.unit.app X.right))) := by
    refine IsPullback.of_iso h1 (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (J.mapIso (pG.app (R.obj X.right))).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]
  simpa only [Category.assoc] using h2.paste_vert hH.flip

/-- The first projection out of the pullback at a comma object, with its functors fixed to the
shape of the comma setting. -/
abbrev commaFstMap {K : Comma L R ⥤ E} (κ₁ : K ⟶ Comma.fst L R ⋙ F') (X : Comma L R) :
    K.obj X ⟶ F'.obj X.left :=
  κ₁.app X

/-- The second projection out of the pullback at a comma object, with its functors fixed to the
shape of the comma setting. -/
abbrev commaSndMap {K : Comma L R ⥤ E} (κ₂ : K ⟶ Comma.snd L R ⋙ G') (X : Comma L R) :
    K.obj X ⟶ G'.obj X.right :=
  κ₂.app X

/-- **The pasted square of the omitted chase, with the square transpose as its right map.**
The pullback square of `isPullback_paste_comma`, whose right map, `r` followed by the comparison
of direct images, is rewritten as the transpose of the square transpose of the comma object by
`homEquiv_symm_r_comp_eq_squareTranspose`.  No map built from `r` remains in the statement. -/
theorem isPullback_paste_squareTranspose [HasPullbacks E] {E' : Type*} [Category* E']
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N')
    (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R) (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) (J : E ⥤ E') [hJ : PreservesLimitsOfShape WalkingCospan J]
    (X : Comma L R) {Y₁ Y₂ : E'} {θ : J.obj (G'.obj X.right) ⟶ Y₁}
    {w : J.obj (G'.obj (R'.obj (R.obj X.right))) ⟶ Y₂} {v : Y₁ ⟶ Y₂}
    (hH : IsPullback θ (J.map (G'.map (adjR.unit.app X.right))) v w) :
    IsPullback (J.map (commaFstMap κ₁ X)) (J.map (commaSndMap κ₂ X) ≫ θ)
      (J.map ((adjG.homEquiv _ _) (squareTranspose adjF adjL adjG adjR αIso.inv X.left X.hom)) ≫
        w) v := by
  have key := homEquiv_symm_r_comp_eq_squareTranspose adjF adjG adjL adjR adjN cF cG pFmid eN pG
    hpF hpG αIso hα hr X
  have e : (adjG.homEquiv (F'.obj X.left) (R'.obj (R.obj X.right)))
      (squareTranspose adjF adjL adjG adjR αIso.inv X.left X.hom) =
      r.app X ≫ pG.inv.app (R.obj X.right) := by
    rw [← key]
    exact Equiv.apply_symm_apply _ _
  rw [e]
  exact isPullback_paste_comma adjR pG hs hKnat J X hH

/-- The morphisms `F' X.left ⟶ G' R' R X.right` of the comma setting. -/
abbrev commaTransposeHom (F' : A ⥤ E) (G' : Bb ⥤ E) (R' : T ⥤ Bb) (X : Comma L R) :=
  F'.obj X.left ⟶ G'.obj (R'.obj (R.obj X.right))

/-- `J` of a morphism `F' X.left ⟶ G' R' R X.right`, with its functors fixed to the shape of the
comma setting. -/
abbrev commaFiberMap {E' : Type*} [Category* E'] (J : E ⥤ E') {X : Comma L R}
    (q : commaTransposeHom F' G' R' X) :
    J.obj (F'.obj X.left) ⟶ J.obj (G'.obj (R'.obj (R.obj X.right))) :=
  J.map q

/-- `isPullback_paste_squareTranspose`, with the transpose of the square transpose named: there
is a morphism `r` whose transpose is the square transpose of the comma object, and the pasted
square with right map `J r` followed by `w` is a pullback. -/
theorem exists_isPullback_paste_squareTranspose [HasPullbacks E] {E' : Type*} [Category* E']
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N')
    (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R) (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) (J : E ⥤ E') [hJ : PreservesLimitsOfShape WalkingCospan J]
    (X : Comma L R) {Y₁ Y₂ : E'} {θ : J.obj (G'.obj X.right) ⟶ Y₁}
    {w : J.obj (G'.obj (R'.obj (R.obj X.right))) ⟶ Y₂} {v : Y₁ ⟶ Y₂}
    (hH : IsPullback θ (J.map (G'.map (adjR.unit.app X.right))) v w) :
    ∃ q : commaTransposeHom F' G' R' X,
      (adjG.homEquiv _ _).symm q = squareTranspose adjF adjL adjG adjR αIso.inv X.left X.hom ∧
      IsPullback (J.map (commaFstMap κ₁ X)) (J.map (commaSndMap κ₂ X) ≫ θ)
        (commaFiberMap J q ≫ w) v :=
  ⟨_, Equiv.symm_apply_apply _ _, isPullback_paste_squareTranspose adjF adjG adjL adjR adjN cF cG
    pFmid eN pG hpF hpG αIso hα hr hs hKnat J (hJ := hJ) X hH⟩

end CategoryTheory.Adjunction

namespace ModuleCat

/-- A pullback square of modules whose left and right maps are composites, elementwise. -/
theorem isPullback_comp_elem {R : Type*} {_ : Ring R} {A B C C' D D' : ModuleCat R} {t : A ⟶ B}
    {l₁ : A ⟶ C} {l₂ : C ⟶ C'} {r₁ : B ⟶ D} {r₂ : D ⟶ D'} {b : C' ⟶ D'}
    (h : IsPullback t (l₁ ≫ l₂) (r₁ ≫ r₂) b) :
    (∀ x, r₂ (r₁ (t x)) = b (l₂ (l₁ x))) ∧
      (∀ x x', t x = t x' → l₂ (l₁ x) = l₂ (l₁ x') → x = x') ∧
      (∀ u v, r₂ (r₁ u) = b v → ∃ x, t x = u ∧ l₂ (l₁ x) = v) := by
  have hT := h.map (forget (ModuleCat R))
  exact ⟨fun x => ConcreteCategory.congr_hom h.w x, fun x x' h₁ h₂ =>
    Types.ext_of_isPullback hT h₁ h₂, fun u v huv => Types.exists_of_isPullback hT u v huv⟩

end ModuleCat

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibre of a transpose along `f^* ⊣ f_*`, on a pure tensor.**  For `k : K ⟶ f_*M` the
fibre at `ȳ` of the transpose `f^*K ⟶ M`, at the element `e⁻¹(1 ⊗ v)` of `(f^*K)_ȳ`, is the
comparison `θ` of the direct image applied to the fibre of `k` at `v`. -/
theorem moduleFiber_homEquiv_symm_apply {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) {K : Modules.{u, u} B S hS X.1 X.2}
    {M : Modules.{u, u} B S hS Y.1 Y.2} (k : K ⟶ (modulePushforward B S hS f).obj M)
    (v : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).obj K) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        (((modulePullbackAdjunction B S hS f).homEquiv K M).symm k)
        ((modulePullbackFiberIso B S hS f y).inv.app K
          ((1 : Stacks.ringFiber (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O.obj) ⊗ₜ[_, smallEtaleStalkPullbackRingMap B S hS f y]
              v)) =
      (directImageFiberMap B S hS f y).app M
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O).map k v) := by
  have hn := ConcreteCategory.congr_hom ((modulePullbackFiberIso B S hS f y).inv.naturality k)
    ((1 : Stacks.ringFiber (etaleSitePoint B S hS Y.1 y Y.2)
      (smallEtaleRingedTopos B S hS Y).O.obj) ⊗ₜ[_, smallEtaleStalkPullbackRingMap B S hS f y] v)
  have hc := ConcreteCategory.congr_hom ((Stacks.sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS Y.1 y Y.2) (smallEtaleRingedTopos B S hS Y).O).map_comp
      ((modulePullback B S hS f).map k) ((modulePullbackAdjunction B S hS f).counit.app M))
    ((modulePullbackFiberIso B S hS f y).inv.app K
      ((1 : Stacks.ringFiber (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O.obj) ⊗ₜ[_, smallEtaleStalkPullbackRingMap B S hS f y] v))
  rw [Adjunction.homEquiv_counit]
  refine hc.trans ?_
  refine (congrArg (fun w => (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
    (smallEtaleRingedTopos B S hS Y).O).map ((modulePullbackAdjunction B S hS f).counit.app M) w)
    hn.symm).trans ?_
  rfl

/-- **The geometric stalk of a transpose along `f^* ⊣ f_*`, on a pure tensor.**  Read through
Stacks 05VQ and the identification of fibres with geometric stalks, the transpose of
`k : K ⟶ f_*M` sends `1 ⊗ v` to the comparison `θ` of the direct image applied to `k(v)`. -/
theorem geometricModuleStalkMap_homEquiv_symm_tmul {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) {K : Modules.{u, u} B S hS X.1 X.2}
    {M : Modules.{u, u} B S hS Y.1 Y.2} (k : K ⟶ (modulePushforward B S hS f).obj M)
    (v : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).obj K) :
    geometricModuleStalkMap B S hS Y y (((modulePullbackAdjunction B S hS f).homEquiv K M).symm k)
        ((geometricModuleStalkPullbackIso B S hS f y K).inv
          ((1 : etaleLocalRing B S hS Y.1 y) ⊗ₜ[_, etaleLocalRingMap Y.2 f.hom y]
            fiberStalkAddEquiv B S hS X (geometricPointMap f.hom y) K v)) =
      fiberStalkAddEquiv B S hS Y y M
        ((directImageFiberMap B S hS f y).app M
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).map k v)) := by
  rw [geometricModuleStalkPullbackIso_inv_tmul, ← fiberStalkAddEquiv_naturality,
    moduleFiber_homEquiv_symm_apply]

/-- `geometricModuleStalkMap_homEquiv_symm_tmul`, for any natural transformation equal to `θ`. -/
theorem geometricModuleStalkMap_homEquiv_symm_tmul_of {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (θ' : type_of% (directImageFiberMap B S hS f y)) (hθ : θ' = directImageFiberMap B S hS f y)
    {K : Modules.{u, u} B S hS X.1 X.2}
    {M : Modules.{u, u} B S hS Y.1 Y.2} (k : K ⟶ (modulePushforward B S hS f).obj M)
    (v : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).obj K) :
    geometricModuleStalkMap B S hS Y y (((modulePullbackAdjunction B S hS f).homEquiv K M).symm k)
        ((geometricModuleStalkPullbackIso B S hS f y K).inv
          ((1 : etaleLocalRing B S hS Y.1 y) ⊗ₜ[_, etaleLocalRingMap Y.2 f.hom y]
            fiberStalkAddEquiv B S hS X (geometricPointMap f.hom y) K v)) =
      fiberStalkAddEquiv B S hS Y y M
        (θ'.app M
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).map k v)) := by
  subst hθ
  exact geometricModuleStalkMap_homEquiv_symm_tmul f y k v

namespace FormalGlueingSituation

variable (D : FormalGlueingSituation B S hS)

/-- The map of a glueing triple, spelled as the square transpose. -/
theorem overlapTranspose_eq_squareTranspose (t : D.moduleGlueingComma) :
    D.overlapTranspose t = Adjunction.squareTranspose
      (modulePullbackAdjunction B S hS D.openImmersion)
      (modulePullbackAdjunction B S hS D.overlapRestriction)
      (modulePullbackAdjunction B S hS D.ambientMorphism)
      (modulePullbackAdjunction B S hS D.openImmersionOver) D.overlapPullbackComparison.inv
      t.left t.hom := rfl

variable (y : GeometricPoint B S hS D.spaceY.1)

/-- The target of a morphism, spelled as the morphism's own type spells it. -/
abbrev homTarget {C : Type*} [Quiver C] {X Y : C} (_ : X ⟶ Y) : C := Y

/-- The triple of a glueing datum, its type spelled through the two pullback functors. -/
abbrev glueingTriple (t : D.moduleGlueingData) : Comma (modulePullback B S hS D.overlapRestriction)
      (modulePullback B S hS D.openImmersionOver) :=
  t.obj

/-- `b` on the image of a fibre element. -/
theorem localB_fiberStalkAddEquiv (t : Comma (modulePullback B S hS D.overlapRestriction)
      (modulePullback B S hS D.openImmersionOver))
    (p : (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
        (smallEtaleRingedTopos B S hS D.spaceY).O).obj t.right) :
    (D.localB y t).hom (fiberStalkAddEquiv B S hS D.spaceY y t.right p) =
      fiberStalkAddEquiv B S hS D.spaceY y ((modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj t.right))
        (ConcreteCategory.hom
          (C := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
          (X := homTarget ((directImageFiberMap B S hS D.ambientMorphism y).app t.right))
          ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
          (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
            ModuleCat.restrictScalars
              (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).map
          ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app t.right)) p) :=
  (fiberStalkAddEquiv_naturality B S hS D.spaceY y (D.overlapUnit t) p).symm

/-- `a` applied to an element of `𝒪_{Y,ȳ} ⊗ N`. -/
theorem localA_apply (t : D.moduleGlueingComma)
    (z : ModuleCat.of (D.localRingY y) (D.localRingY y ⊗[D.localRingX y] D.localN y t)) :
    (D.localA y t).hom z = geometricModuleStalkLinearMap B S hS D.spaceY y (D.overlapTranspose t)
      ((geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
        ((modulePushforward B S hS D.openImmersion).obj t.left)).inv.hom z) :=
  LinearMap.comp_apply _ _ z

/-- **The map `β` on the geometric stalk at `ȳ`, read through Stacks 05VQ**: the map
`𝒪_{Y,ȳ} ⊗ K_x̄ ⟶ 𝒢_ȳ`, in the shape of the stalk glueing datum. -/
def glueingCounitRightStalk (t : D.moduleGlueingData) :
    ModuleCat.of (D.localRingY y) (D.localRingY y ⊗[D.localRingX y]
      geometricModuleStalk B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
        (D.glueingKernelDiagram.obj t.obj)) ⟶ D.localP y t.obj :=
  (geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
      (D.glueingKernelDiagram.obj t.obj)).inv ≫
    ModuleCat.homEquiv.symm (geometricModuleStalkLinearMap B S hS D.spaceY y
      (D.glueingCounitRight t))

/-- `β` on the geometric stalk at `ȳ`, applied to an element of `𝒪_{Y,ȳ} ⊗ K_x̄`. -/
theorem glueingCounitRightStalk_apply (t : D.moduleGlueingData)
    (z : ModuleCat.of (D.localRingY y) (D.localRingY y ⊗[D.localRingX y]
      geometricModuleStalk B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
        (D.glueingKernelDiagram.obj t.obj))) :
    (D.glueingCounitRightStalk y t).hom z =
      geometricModuleStalkLinearMap B S hS D.spaceY y (D.glueingCounitRight t)
        ((geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
          (D.glueingKernelDiagram.obj t.obj)).inv.hom z) :=
  LinearMap.comp_apply _ _ z

/-- The map `β` on a pure tensor of the geometric stalk of the module of Stacks 0AEX. -/
theorem glueingCounitRight_tmul_fiberStalkAddEquiv' (t : D.moduleGlueingData)
    (k : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj (D.glueingKernelDiagram.obj t.obj)) :
    geometricModuleStalkMap B S hS D.spaceY y (D.glueingCounitRight t)
        ((geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
          (D.glueingKernelDiagram.obj t.obj)).inv.hom
          ((1 : D.localRingY y) ⊗ₜ[D.localRingX y]
            fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ k)) =
      fiberStalkAddEquiv B S hS D.spaceY y _
        ((directImageFiberMap B S hS D.ambientMorphism y).app _
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O).map
            (Adjunction.commaSndMap D.glueingKernelSnd t.obj) k)) :=
  geometricModuleStalkMap_homEquiv_symm_tmul D.ambientMorphism y
    (Adjunction.commaSndMap D.glueingKernelSnd t.obj) k

/-- `β` on the geometric stalk at `ȳ`, on a pure tensor of a fibre element of the module of
Stacks 0AEX. -/
theorem glueingCounitRight_tmul_fiberStalkAddEquiv (t : D.moduleGlueingData)
    (k : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj (D.glueingKernelDiagram.obj t.obj)) :
    (D.glueingCounitRightStalk y t).hom ((1 : D.localRingY y) ⊗ₜ[D.localRingX y]
        fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ k) =
      fiberStalkAddEquiv B S hS D.spaceY y _
        ((directImageFiberMap B S hS D.ambientMorphism y).app _
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O).map
            (Adjunction.commaSndMap D.glueingKernelSnd t.obj) k)) :=
  (D.glueingCounitRightStalk_apply y t _).trans
    (D.glueingCounitRight_tmul_fiberStalkAddEquiv' y t k)

/-- The fibre map of `J` at a morphism of the comma setting, read in the `ringFiber`
spelling of the category of modules over the stalk ring. -/
theorem commaFiberMap_apply (t : D.moduleGlueingComma)
    (g : Adjunction.commaTransposeHom (modulePushforward B S hS D.openImmersion)
      (modulePushforward B S hS D.ambientMorphism) (modulePushforward B S hS D.openImmersionOver) t)
    (n : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj
          ((modulePushforward B S hS D.openImmersion).obj t.left)) :
    ConcreteCategory.hom (C := (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj)))
            (Adjunction.commaFiberMap
              (E' := (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj)))
              (F' := modulePushforward B S hS D.openImmersion)
              (G' := modulePushforward B S hS D.ambientMorphism)
              (R' := modulePushforward B S hS D.openImmersionOver)
                (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O) (X := t) g) n =
      (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).map g n := rfl

/-- A natural transformation of the type of `θ`, applied at `j'_*𝒢|_V`, read in the `ringFiber`
spelling of the category of modules over the stalk ring. -/
theorem directImageFiberMap_app_apply (t : D.moduleGlueingComma)
    (θ' : type_of% (directImageFiberMap B S hS D.ambientMorphism y))
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj
          ((modulePushforward B S hS D.ambientMorphism).obj
              ((modulePushforward B S hS D.openImmersionOver).obj
                ((modulePullback B S hS D.openImmersionOver).obj t.right)))) :
        ConcreteCategory.hom
          (C := (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj)))
          (X := @CategoryTheory.Functor.obj (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
              (@SheafOfModules.instCategory _ _ _ _)
            _ _ (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O)
            ((modulePushforward B S hS D.ambientMorphism).obj
              ((modulePushforward B S hS D.openImmersionOver).obj
                ((modulePullback B S hS D.openImmersionOver).obj t.right))))
          (Y := (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
              ModuleCat.restrictScalars
                (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).obj
                ((modulePullback B S hS D.openImmersionOver ⋙
                  modulePushforward B S hS D.openImmersionOver).obj t.right))
          (θ'.app _) m = θ'.app _ m := rfl

/-- `a` on a pure tensor, read through Stacks 05VQ in the extension-of-scalars form. -/
theorem localA_tmul_eq (t : D.moduleGlueingComma)
    (n : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj
          ((modulePushforward B S hS D.openImmersion).obj t.left)) :
    (D.localA y t).hom ((1 : D.localRingY y) ⊗ₜ[D.localRingX y]
        fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ n) =
      geometricModuleStalkMap B S hS D.spaceY y (D.overlapTranspose t)
        ((geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
          ((modulePushforward B S hS D.openImmersion).obj t.left)).inv
          ((1 : etaleLocalRing B S hS D.spaceY.1 y) ⊗ₜ[_, etaleLocalRingMap D.spaceY.2
            D.ambientMorphism.hom y]
            fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
              _ n)) := by
  rw [localA_apply]
  rfl

/-- `a` on the image of a fibre element, for any morphism `g : j_*ℋ ⟶ f_*j'_*𝒢|_V` whose
transpose is the map of the triple. -/
theorem localA_tmul_fiberStalkAddEquiv_of (t : D.moduleGlueingComma)
    (θ' : type_of% (directImageFiberMap B S hS D.ambientMorphism y))
    (hθ : θ' = directImageFiberMap B S hS D.ambientMorphism y)
    (g : Adjunction.commaTransposeHom (modulePushforward B S hS D.openImmersion)
      (modulePushforward B S hS D.ambientMorphism) (modulePushforward B S hS D.openImmersionOver) t)
    (hg : ((modulePullbackAdjunction B S hS D.ambientMorphism).homEquiv _ _).symm g =
      D.overlapTranspose t)
    (n : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj
          ((modulePushforward B S hS D.openImmersion).obj t.left)) :
    (D.localA y t).hom ((1 : D.localRingY y) ⊗ₜ[D.localRingX y]
        fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ n) =
      fiberStalkAddEquiv B S hS D.spaceY y ((modulePushforward B S hS D.openImmersionOver).obj
          ((modulePullback B S hS D.openImmersionOver).obj t.right))
        (ConcreteCategory.hom
          (C := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
          (X := @CategoryTheory.Functor.obj (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
              (@SheafOfModules.instCategory _ _ _ _)
            _ _ (Stacks.sheafModuleFiberOfCommRing
              (etaleSitePoint B S hS D.spaceX.1
                (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
              (smallEtaleRingedTopos B S hS D.spaceX).O)
            ((modulePushforward B S hS D.ambientMorphism).obj
              ((modulePushforward B S hS D.openImmersionOver).obj
                ((modulePullback B S hS D.openImmersionOver).obj t.right))))
          (Y := (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
              ModuleCat.restrictScalars
                (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).obj
                ((modulePullback B S hS D.openImmersionOver ⋙
                  modulePushforward B S hS D.openImmersionOver).obj t.right))
          (θ'.app _)
          (ConcreteCategory.hom
            (C := (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj)))
            (Adjunction.commaFiberMap
              (E' := (ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj)))
              (F' := modulePushforward B S hS D.openImmersion)
              (G' := modulePushforward B S hS D.ambientMorphism)
              (R' := modulePushforward B S hS D.openImmersionOver)
              (Stacks.sheafModuleFiberOfCommRing
                (etaleSitePoint B S hS D.spaceX.1
                  (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
                (smallEtaleRingedTopos B S hS D.spaceX).O) (X := t) g) n)) := by
  rw [directImageFiberMap_app_apply D y t θ', commaFiberMap_apply D y t g n, localA_tmul_eq, ← hg]
  exact geometricModuleStalkMap_homEquiv_symm_tmul_of D.ambientMorphism y θ' hθ g n

/-- `κ` on a fibre element, with the fibre map read in the category of modules over the
`ringFiber` spelling of the stalk ring. -/
theorem kernelFst_fiberStalkAddEquiv (t : D.moduleGlueingData)
    (k : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj (D.glueingKernelDiagram.obj t.obj)) :
    geometricModuleStalkLinearMap B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
        (Adjunction.commaFstMap D.glueingKernelFst t.obj)
        (fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ k) =
      fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
        ((modulePushforward B S hS D.openImmersion).obj t.obj.left)
        (ConcreteCategory.hom
          (C := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
          ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).map
          (Adjunction.commaFstMap D.glueingKernelFst t.obj)) k) :=
  (fiberStalkAddEquiv_naturality B S hS D.spaceX _
    (Adjunction.commaFstMap D.glueingKernelFst t.obj) k).symm

/-- `β` on a pure tensor, with the fibre maps read in the category of modules over the
`ringFiber` spelling of the stalk ring. -/
theorem glueingCounitRightStalk_tmul_fiberStalkAddEquiv (t : D.moduleGlueingData)
    (θ' : type_of% (directImageFiberMap B S hS D.ambientMorphism y))
    (hθ : θ' = directImageFiberMap B S hS D.ambientMorphism y)
    (k : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).obj (D.glueingKernelDiagram.obj t.obj)) :
    (D.glueingCounitRightStalk y t).hom ((1 : D.localRingY y) ⊗ₜ[D.localRingX y]
        fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _ k) =
      fiberStalkAddEquiv B S hS D.spaceY y t.obj.right
        (ConcreteCategory.hom
          (C := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
          (θ'.app _)
          (ConcreteCategory.hom
            (C := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
            ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
        (smallEtaleRingedTopos B S hS D.spaceX).O).map
          (Adjunction.commaSndMap D.glueingKernelSnd t.obj)) k)) := by
  subst hθ
  exact D.glueingCounitRight_tmul_fiberStalkAddEquiv y t k

/-- **The omitted chase of Stacks 0AF0 for the situation, through any functor preserving
pullbacks.**  Read through `J`, the pullback square of the module of Stacks 0AEX pastes onto a
pullback square whose top row is `J` of the direct image of the unit `𝒢 ⟶ j'_*𝒢|_V`; the right
map of the pasted square is `J` of a transpose of the map of the triple. -/
theorem exists_isPullback_glueingKernel_fiber {E' : Type*} [Category* E']
    (J : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤ E')
    [hJ : PreservesLimitsOfShape WalkingCospan J]
    (X : Comma (modulePullback B S hS D.overlapRestriction)
      (modulePullback B S hS D.openImmersionOver)) {Y₁ Y₂ : E'}
    {θ : J.obj ((modulePushforward B S hS D.ambientMorphism).obj X.right) ⟶ Y₁}
    {w : J.obj ((modulePushforward B S hS D.ambientMorphism).obj
      ((modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj X.right))) ⟶ Y₂} {v : Y₁ ⟶ Y₂}
    (hH : IsPullback θ (J.map ((modulePushforward B S hS D.ambientMorphism).map
      ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app X.right))) v w) :
    ∃ q : Adjunction.commaTransposeHom (modulePushforward B S hS D.openImmersion)
        (modulePushforward B S hS D.ambientMorphism)
        (modulePushforward B S hS D.openImmersionOver) X,
      ((modulePullbackAdjunction B S hS D.ambientMorphism).homEquiv _ _).symm q =
        D.overlapTranspose X ∧
      IsPullback (J.map (Adjunction.commaFstMap D.glueingKernelFst X))
        (J.map (Adjunction.commaSndMap D.glueingKernelSnd X) ≫ θ)
        (Adjunction.commaFiberMap J q ≫ w) v :=
  Adjunction.exists_isPullback_paste_squareTranspose
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel
    J X hH

/-- **`β` on the geometric stalk at a point of `f⁻¹(Z)`, granted Stacks 0AER on fibres.**  If the
square of Stacks 0AER is cartesian on fibres at `ȳ` and the generic map of the stalk glueing datum
of the triple at `ȳ` is bijective, then `β` is bijective on the geometric stalk at `ȳ`. -/
theorem bijective_glueingCounitRight_of_isPullback (t : D.moduleGlueingData)
    (hH : IsPullback ((directImageFiberMap B S hS D.ambientMorphism y).app
        (D.glueingTriple t).right)
      ((modulePushforward B S hS D.ambientMorphism ⋙
          Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)
              D.spaceX.2) (smallEtaleRingedTopos B S hS D.spaceX).O).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app (D.glueingTriple t).right))
      ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS D.spaceY.1 y D.spaceY.2)
            (smallEtaleRingedTopos B S hS D.spaceY).O ⋙
          ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS D.ambientMorphism y)).map
        ((modulePullbackAdjunction B S hS D.openImmersionOver).unit.app (D.glueingTriple t).right))
      ((directImageFiberMap B S hS D.ambientMorphism y).app
        ((modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj (D.glueingTriple t).right))))
    (hbij : Function.Bijective (FormalGlueing.pullbackGenericMap.{u + 1, u + 1, 0} (D.localRingY y)
      (D.localN y t.obj) (D.localP y t.obj) (D.localQ y t.obj) (D.localA y t.obj)
      (D.localB y t.obj))) :
    Function.Bijective (geometricModuleStalkMap B S hS D.spaceY y (D.glueingCounitRight t)) := by
  obtain ⟨θ', hθ'⟩ : ∃ θ' : type_of% (directImageFiberMap B S hS D.ambientMorphism y),
      θ' = directImageFiberMap B S hS D.ambientMorphism y := ⟨_, rfl⟩
  rw [← hθ'] at hH
  have hfl := Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
    (smallEtaleRingedTopos B S hS D.spaceX).O
  obtain ⟨q, hq', hP⟩ := D.exists_isPullback_glueingKernel_fiber
    (E' := ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS D.spaceX.1
          (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
          (smallEtaleRingedTopos B S hS D.spaceX).O.obj))
    (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y) D.spaceX.2)
      (smallEtaleRingedTopos B S hS D.spaceX).O) (hJ := hfl.preservesFiniteLimits WalkingCospan)
      (D.glueingTriple t) hH
  obtain ⟨hw0, hinj0, hsurj0⟩ := ModuleCat.isPullback_comp_elem hP
  have hT : Function.Bijective (D.glueingCounitRightStalk y t).hom := by
    refine FormalGlueing.bijective_of_isFibreProduct_transport (D.localRingY y)
      (D.localN y t.obj) (D.localP y t.obj) (D.localQ y t.obj) (D.localA y t.obj) (D.localB y t.obj)
      (geometricModuleStalkLinearMap B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
        (Adjunction.commaFstMap D.glueingKernelFst t.obj))
      (D.glueingCounitRightStalk y t).hom
      (fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _)
      (fiberStalkAddEquiv B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y) _)
      (fiberStalkAddEquiv B S hS D.spaceY y t.obj.right)
      (fiberStalkAddEquiv B S hS D.spaceY y ((modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj t.obj.right)))
      ?_ ?_ ?_ ?_ hw0 hinj0 hsurj0 hbij
    · exact D.kernelFst_fiberStalkAddEquiv y t
    · exact D.glueingCounitRightStalk_tmul_fiberStalkAddEquiv y t θ' hθ'
    · intro n
      exact D.localA_tmul_fiberStalkAddEquiv_of y t.obj θ' hθ' q hq' n
    · intro p
      exact D.localB_fiberStalkAddEquiv y (D.glueingTriple t) p
  have hiso := (geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
    (D.glueingKernelDiagram.obj t.obj)).toLinearEquiv.bijective
  have hfun : ⇑(geometricModuleStalkMap B S hS D.spaceY y (D.glueingCounitRight t)) =
      (D.glueingCounitRightStalk y t).hom ∘ (geometricModuleStalkPullbackIso B S hS
        D.ambientMorphism y (D.glueingKernelDiagram.obj t.obj)).toLinearEquiv := by
    funext z
    refine Eq.trans ?_ (D.glueingCounitRightStalk_apply y t _).symm
    exact congrArg (geometricModuleStalkMap B S hS D.spaceY y (D.glueingCounitRight t))
      (Iso.hom_inv_id_apply _ z).symm
  rw [hfun]
  exact hT.comp hiso

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
