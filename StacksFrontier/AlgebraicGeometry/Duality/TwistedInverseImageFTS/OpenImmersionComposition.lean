module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Formalism

/-!
# The upper shriek functors of open immersions compose like derived pullbacks

For an open immersion `j`, the upper shriek functor `j^!` at any compactification is the derived
pullback `Lj^*` on `D⁺_QCoh` ([Stacks, Tag 0AU0]). This file proves that these identifications
carry the composition isomorphisms `k^! ≅ j^! ∘ i^!` of [Stacks, Tag 0ATX] for `k = j ≫ i` to the
composition isomorphisms `Lk^* ≅ Lj^* ∘ Li^*` of derived pullback.

## Main results

* `Stacks.Duality.upperShriekOpenIso_comp` and
  `Stacks.Duality.UpperShriek.shriekOfIsoPullbackOfIsOpenImmersion_factorIso`: `j^! = Lj^*`
  carries `(h ≫ j)^! ≅ h^! ∘ j^!` to `L(h ≫ j)^* ≅ Lh^* ∘ Lj^*`, at the compactifications by the
  targets and at any choice of compactifications.
* `Stacks.Duality.openBaseChange_id_app_comp`: the base change map of the square of an open
  immersion over the identity is the identity, against the units `a_𝟙 ≅ 𝟭`.

## References

* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

private lemma idIso_chase {C D : Type*} [Category C] [Category D] (L : C ⥤ D) {x y z : C}
    {w : D} (C' : y ≅ x) (A : y ≅ z) (ι₀ : z ⟶ x) (β : L.obj z ⟶ w) (ι : w ⟶ L.obj x)
    (h : L.map (C'.inv ≫ A.hom) ≫ β ≫ ι = 𝟙 _) (h₃ : A.inv ≫ C'.hom = ι₀) :
    β ≫ ι = L.map ι₀ := by
  have e : ι₀ ≫ C'.inv ≫ A.hom = 𝟙 _ := by simp [← h₃]
  calc β ≫ ι = (L.map ι₀ ≫ L.map (C'.inv ≫ A.hom)) ≫ β ≫ ι := by
        rw [← L.map_comp, e, L.map_id, Category.id_comp]
    _ = L.map ι₀ := by rw [Category.assoc, h, Category.comp_id]

section IdSquare

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S] {X Y : FTS S}
  (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))

/-- **The base change map of the square `X ⊆ X̄` over itself is the identity**, against the units
`a_𝟙 ≅ 𝟭`: at `ā(K)` for `K` bounded below, the map of [Stacks, Tag 0A9L] for the square formed
by the open immersion of a compactification and two identities, followed by the unit of `X`, is
the restriction of the unit of `X̄`. This is `α_𝟙 = 𝟙` ([Stacks, Tag 0AA0]) unfolded. -/
theorem openBaseChange_id_app_comp (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    (openBaseChange c.immersion (𝟙 X.left) (𝟙 c.space) c.immersion
        (IsPullback.id_vert c.immersion)).app
        ((twistedInverseImage c.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K.obj) ≫
      (twistedInverseImageIdIsoOfComp X.left).hom.app _ =
    (quasiCoherentDerivedPullback' c.immersion).map
      ((twistedInverseImageIdIsoOfComp c.space).hom.app
        ((twistedInverseImage c.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K.obj)) := by
  have h₁ := congrArg (fun e => (e.hom.app K).hom) (upperShriekCompactificationIso_id f c)
  have h₂ := upperShriekCompactificationMap_app_eq_openBaseChange f c c (𝟙 c.space)
    (Category.id_comp _) (IsPullback.id_vert c.immersion) K.obj
  refine idIso_chase (quasiCoherentDerivedPullback' c.immersion)
    ((twistedInverseImageCongr (Category.id_comp c.toBase)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K.obj)
    ((twistedInverseImageCompIso (𝟙 c.space) c.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app K.obj) _ _ _ ?_
    (twistedInverseImageCompIso_id_comp c.toBase K.obj)
  simp only [Iso.app_inv, Iso.app_hom,
    twistedInverseImageCongr_inv (Category.id_comp c.toBase) K.obj]
  exact h₂.symm.trans h₁

end IdSquare

/-- The left unit law at `𝟙 ≫ 𝟙`: `a_{𝟙 ≫ 𝟙} ≅ a_𝟙 ⋙ a_𝟙` followed by the unit `a_𝟙 ≅ 𝟭` is the
identity. -/
private theorem twistedInverseImageCompIso_id_id_hom_app_comp (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (K : quasiCoherentDerivedCategory Z) :
    (twistedInverseImageCompIso (𝟙 Z) (𝟙 Z)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K ≫
      (twistedInverseImageIdIsoOfComp Z).hom.app
        ((twistedInverseImage (𝟙 Z) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K) = 𝟙 _ := by
  rw [← twistedInverseImageCompIso_id_comp (𝟙 Z) K, Iso.hom_inv_id_app_assoc]
  rfl

private lemma open_comp_chase {C E D : Type*} [Category C] [Category E] [Category D]
    (Lk : C ⥤ D) (Lj : C ⥤ E) (Lh : E ⥤ D) (P : Lk ⟶ Lj ⋙ Lh) {K a aa : C} {b : E}
    (T : a ⟶ aa) (ι₁ : a ⟶ K) (ι₂ : aa ⟶ a) (B : Lj.obj aa ⟶ b) (ιU : b ⟶ Lj.obj a)
    (c : Lh.obj (Lj.obj K) ⟶ Lk.obj K) (F2 : B ≫ ιU = Lj.map ι₂) (F3 : T ≫ ι₂ = 𝟙 _)
    (F5 : P.app K ≫ c = 𝟙 _) :
    Lk.map ι₁ = (𝟙 _ ≫ (Lk.map T ≫ P.app aa ≫ Lh.map B) ≫ 𝟙 _ ≫ 𝟙 _) ≫ Lh.map ιU ≫
      Lh.map (Lj.map ι₁) ≫ c := by
  simp only [Category.id_comp, Category.comp_id]
  have n₁ := P.naturality ι₂
  have n₂ := P.naturality ι₁
  simp only [Functor.comp_map] at n₁ n₂
  calc Lk.map ι₁ = Lk.map (T ≫ ι₂ ≫ ι₁) ≫ P.app K ≫ c := by
        rw [F5, Category.comp_id, ← Category.assoc, F3, Category.id_comp]
    _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← Lh.map_comp_assoc B ιU, F2, reassoc_of% n₂, reassoc_of% n₁]

section OpenCompactifications

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S]

/-- **`f^! = Lf^*` for an open immersion** at the compactification of `f` by its target
([Stacks, Tag 0AU0]): `a_𝟙 ≅ 𝟭` followed by the derived pullback, with the unit of the identity
taken as the one compatible with composition. -/
def upperShriekOpenIso {X Y : FTS S} (f : X ⟶ Y) [IsOpenImmersion f.left] :
    upperShriek f (openCompactification f) ≅ quasiCoherentDerivedPullback' f.left :=
  Functor.isoWhiskerRight (twistedInverseImageIdIsoOfComp Y.left) _ ≪≫ Functor.leftUnitor _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The component of `upperShriekOpenIso f` at `K` is the derived pullback `Lf^*` of the component
of `a_𝟙 ≅ 𝟭` at `K`. -/
theorem upperShriekOpenIso_hom_app {X Y : FTS S} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (K : quasiCoherentDerivedCategory Y.left) :
    (upperShriekOpenIso f).hom.app K =
      (quasiCoherentDerivedPullback' f.left).map
        ((twistedInverseImageIdIsoOfComp Y.left).hom.app K) := by
  simp only [upperShriekOpenIso]
  exact Category.comp_id _

variable {W U X : FTS S} (h : W ⟶ U) (j : U ⟶ X) [IsOpenImmersion h.left] [IsOpenImmersion j.left]

/-- The underlying morphism of a composition of open immersions of `FTS S` is an open immersion. -/
instance isOpenImmersion_comp_left : IsOpenImmersion (h ≫ j).left :=
  inferInstanceAs (IsOpenImmersion (h.left ≫ j.left))

/-- The nested compactification of two open immersions `h`, `j` over the compactification of `j`
by its target: `R = X` over itself and `Q = U`. -/
def NestedCompactification.ofOpen : NestedCompactification h j (openCompactification j) where
  R := X.left
  r := 𝟙 _
  isProper_r := inferInstanceAs (IsProper (𝟙 X.left))
  u := h.left ≫ j.left
  u_r := by simp
  Q := U.left
  v := j.left
  rQ := 𝟙 _
  isPullback := IsPullback.id_vert j.left
  uQ := h.left
  uQ_v := rfl
  uQ_rQ := Category.comp_id _

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
/-- The transport isomorphism of `NestedCompactification.ofOpen h j` is inverse to the composition
isomorphism `L(h ≫ j)^* ≅ Lh^* ∘ Lj^*`. -/
private theorem NestedCompactification.ofOpen_pullbackIso_hom_app_comp
    (K : quasiCoherentDerivedCategory X.left) :
    (NestedCompactification.ofOpen h j).pullbackIso.hom.app K ≫
      (quasiCoherentDerivedPullbackCompIso h.left j.left).hom.app K = 𝟙 _ := by
  change ((quasiCoherentDerivedPullbackCongr (X := W.left) (h₁ := h.left ≫ j.left) rfl).hom.app
      K ≫ (quasiCoherentDerivedPullbackCompIso h.left j.left).inv.app K) ≫
      (quasiCoherentDerivedPullbackCompIso h.left j.left).hom.app K = 𝟙 _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply ObjectProperty.hom_ext
  simp [quasiCoherentDerivedPullbackCongr]

/-- **The identifications `f^! = Lf^*` of open immersions carry the composition isomorphism of
upper shriek functors to the composition isomorphism of derived pullbacks** ([Stacks, Tag 0ATX]
read through [Stacks, Tag 0AU0]), at the compactifications by the targets. -/
theorem upperShriekOpenIso_comp (K : quasiCoherentDerivedCategoryPlusOfModel X.left) :
    (upperShriekOpenIso (h ≫ j)).hom.app K.obj =
      ((upperShriekCompIso h j (openCompactification h) (openCompactification j)
          (openCompactification (h ≫ j))).hom.app K).hom ≫
        (upperShriekOpenIso h).hom.app ((upperShriek j (openCompactification j)).obj K.obj) ≫
        (quasiCoherentDerivedPullback' h.left).map ((upperShriekOpenIso j).hom.app K.obj) ≫
        (quasiCoherentDerivedPullbackCompIso h.left j.left).hom.app K.obj := by
  rw [NestedCompactification.upperShriekCompIso_eq_compIsoVia _ _ _
    (NestedCompactification.ofOpen h j)]
  have F0 := congrArg (fun i => (i.hom.app K).hom)
    (show DominatingCompactification.upperShriekPlusIso (h ≫ j) (openCompactification (h ≫ j))
      (NestedCompactification.ofOpen h j).compFG = Iso.refl _ from upperShriekPlusIso_refl _ _)
  have F0' := congrArg
    (fun i => (i.hom.app ((upperShriekPlus j (openCompactification j)).obj K)).hom)
    (show DominatingCompactification.upperShriekPlusIso h (NestedCompactification.ofOpen h j).compF
      (openCompactification h) = Iso.refl _ from upperShriekPlusIso_refl _ _)
  have F0'' := congrArg (fun i => ((Functor.isoWhiskerRight i
      (upperShriekPlus h (openCompactification h))).hom.app K).hom)
    (upperShriekPlusIso_refl j (openCompactification j))
  simp only [Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.id_app] at F0 F0' F0''
  have F1 : (NestedCompactification.ofOpen h j).compHom.app K.obj =
      (quasiCoherentDerivedPullback' (h ≫ j).left).map
        ((twistedInverseImageCompIso (𝟙 X.left) (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K.obj) ≫
      (NestedCompactification.ofOpen h j).pullbackIso.hom.app
        ((twistedInverseImage (𝟙 X.left)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((twistedInverseImage (𝟙 X.left)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K.obj)) ≫
      (quasiCoherentDerivedPullback' h.left).map
        ((openBaseChange j.left (𝟙 U.left) (𝟙 X.left) j.left (IsPullback.id_vert j.left)).app
          ((twistedInverseImage (𝟙 X.left)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K.obj)) :=
    NestedCompactification.compHom_app (NestedCompactification.ofOpen h j) K.obj
  rw [upperShriekOpenIso_hom_app, upperShriekOpenIso_hom_app, upperShriekOpenIso_hom_app]
  change _ = (((DominatingCompactification.upperShriekPlusIso (h ≫ j) (openCompactification (h ≫ j))
      (NestedCompactification.ofOpen h j).compFG).hom.app K).hom ≫
    (NestedCompactification.ofOpen h j).compHom.app K.obj ≫
    ((DominatingCompactification.upperShriekPlusIso h (NestedCompactification.ofOpen h j).compF
      (openCompactification h)).hom.app ((upperShriekPlus j (openCompactification j)).obj K)).hom ≫
    ((Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso j
      (openCompactification j) (openCompactification j))
      (upperShriekPlus h (openCompactification h))).hom.app K).hom) ≫ _
  rw [F0, F0', F0'', F1]
  exact open_comp_chase (quasiCoherentDerivedPullback' (h ≫ j).left)
    (quasiCoherentDerivedPullback' j.left) (quasiCoherentDerivedPullback' h.left)
    (NestedCompactification.ofOpen h j).pullbackIso.hom _ _ _ _ _ _
    (openBaseChange_id_app_comp j (openCompactification j) K)
    (twistedInverseImageCompIso_id_id_hom_app_comp X.left K.obj)
    (NestedCompactification.ofOpen_pullbackIso_hom_app_comp h j K.obj)

end OpenCompactifications

private lemma shriek_comp_chase {C C' : Type*} [Category C] [Category C'] (Lh : C' ⥤ C)
    {O0 O1 O2 O3 O4 O5 M4 : C} {N1 N2 N3 : C'} (dk : O0 ⟶ O1) (ρk : O1 ⟶ M4) (ci : O1 ⟶ O2)
    (dh1 : O2 ⟶ O3) (hcdj1 : O3 ⟶ O4) (dh2 : O4 ⟶ O5) (ρhc : O5 ⟶ Lh.obj N2) (dj1 : N1 ⟶ N2)
    (dj2 : N2 ⟶ N1) (ρj : N1 ⟶ N3) (ρho : O2 ⟶ Lh.obj N1) (hodj1 : O2 ⟶ O5)
    (comp : Lh.obj N3 ⟶ M4) (cong : M4 ⟶ M4)
    (A0 : ρk = ci ≫ ρho ≫ Lh.map ρj ≫ comp) (G12 : dh1 ≫ hcdj1 ≫ dh2 = hodj1)
    (G3 : hodj1 ≫ ρhc = ρho ≫ Lh.map dj1) (G4 : dj1 ≫ dj2 = 𝟙 _) (hc : cong = 𝟙 _) :
    dk ≫ ρk = (dk ≫ ci ≫ dh1 ≫ hcdj1) ≫ (dh2 ≫ ρhc) ≫ Lh.map (dj2 ≫ ρj) ≫ comp ≫ cong := by
  subst hc A0
  simp only [Category.assoc, Category.comp_id, Functor.map_comp]
  rw [reassoc_of% G12, reassoc_of% G3, ← Lh.map_comp_assoc, G4, Lh.map_id, Category.id_comp]

/-- The isomorphisms of [Stacks, Tag 0AA0] in the two directions compose to the identity. -/
private theorem upperShriekPlusIso_hom_app_comp_symm {S : Scheme.{u}}
    [QuasiSeparatedSpace S] [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
    (c₁ c₂ : CompactificationOf (Over.mk f.left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    (DominatingCompactification.upperShriekPlusIso f c₁ c₂).hom.app K ≫
      (DominatingCompactification.upperShriekPlusIso f c₂ c₁).hom.app K = 𝟙 _ := by
  have := congrArg (fun i => i.hom.app K)
    ((upperShriekPlusIso_trans f c₁ c₂ c₁).trans (upperShriekPlusIso_refl f c₁))
  simpa using this

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-- **For a shriekable open immersion `j`, `j^!` is the derived pullback `Lj^*`** on `D⁺_QCoh`, at
the compactification `c j` ([Stacks, Tag 0AU0] together with [Stacks, Tag 0AA0]). -/
def shriekOfIsoPullbackOfIsOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsShriekable j)
    [IsOpenImmersion j] :
    shriekOf c j hj ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ quasiCoherentDerivedPullback' j :=
  haveI := hj.target_noetherian
  haveI : IsOpenImmersion (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id j)).left := inferInstanceAs (IsOpenImmersion j)
  Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso
      (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))
      (c j hj) (openCompactification
        (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))))
      (ObjectProperty.ι _) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) (upperShriekOpenIso
      (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j)))

/-- The component of `shriekOfIsoPullbackOfIsOpenImmersion c j hj` at `K` is the comparison of
`j^!` at the compactifications `c j` and the target, followed by `upperShriekOpenIso`. -/
theorem shriekOfIsoPullbackOfIsOpenImmersion_hom_app {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hj : IsShriekable j) [IsOpenImmersion j] (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    haveI := hj.target_noetherian
    haveI : IsOpenImmersion (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y)
      (Category.comp_id j)).left := inferInstanceAs (IsOpenImmersion j)
    (shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app K =
      ((DominatingCompactification.upperShriekPlusIso
        (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id j))
        (c j hj) (openCompactification
          (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y)
            (Category.comp_id j)))).hom.app K).hom ≫
      (upperShriekOpenIso
        (ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id Y)
          (Category.comp_id j))).hom.app
          K.obj :=
  rfl

/-- **The identifications `j^! = Lj^*` of open immersions are compatible with composition**
([Stacks, Tag 0AU0] and [Stacks, Tag 0ATX]): for open immersions `h`, `j` with `h ≫ j = k`, at
any choice of compactifications, `k^! ≅ h^! ∘ j^!` corresponds to `Lk^* ≅ Lh^* ∘ Lj^*`. -/
theorem shriekOfIsoPullbackOfIsOpenImmersion_factorIso {W U X : Scheme.{u}} {h : W ⟶ U}
    {j : U ⟶ X} {k : W ⟶ X} (e : h ≫ j = k) (hh : IsShriekable h) (hj : IsShriekable j)
    (hk : IsShriekable k) [IsOpenImmersion h] [IsOpenImmersion j] [IsOpenImmersion k]
    (K : quasiCoherentDerivedCategoryPlusOfModel X) :
    (shriekOfIsoPullbackOfIsOpenImmersion c k hk).hom.app K =
      ((factorIsoOf c e hh hj hk).hom.app K).hom ≫
        (shriekOfIsoPullbackOfIsOpenImmersion c h hh).hom.app ((shriekOf c j hj).obj K) ≫
        (quasiCoherentDerivedPullback' h).map
          ((shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.app K) ≫
        (quasiCoherentDerivedPullbackCompIso h j).hom.app K.obj ≫
        (quasiCoherentDerivedPullbackCongr e).hom.app K.obj := by
  subst e
  have := hj.target_noetherian
  rw [shriekOfIsoPullbackOfIsOpenImmersion_hom_app, shriekOfIsoPullbackOfIsOpenImmersion_hom_app,
    shriekOfIsoPullbackOfIsOpenImmersion_hom_app]
  let fh := ftsHomOf h hk.separatedFiniteType hj.separatedFiniteType rfl
  let fj := ftsHomOf j hj.separatedFiniteType (isSeparatedFiniteType_id X) (Category.comp_id j)
  have : IsOpenImmersion fh.left := inferInstanceAs (IsOpenImmersion h)
  have : IsOpenImmersion fj.left := inferInstanceAs (IsOpenImmersion j)
  have hF : factorIsoOf c rfl hh hj hk =
      upperShriekCompIso fh fj (c h hh) (c j hj) (c (h ≫ j) hk) := rfl
  rw [hF, NestedCompactification.upperShriekCompIso_eq_conj (f := fh) (g := fj)
    (openCompactification fh) (openCompactification fj) (openCompactification (fh ≫ fj))
    (c h hh) (c j hj) (c (h ≫ j) hk)]
  have G12 : ((DominatingCompactification.upperShriekPlusIso fh (openCompactification fh)
        (c h hh)).hom.app ((upperShriekPlus fj (openCompactification fj)).obj K)).hom ≫
      (upperShriek fh (c h hh)).map ((DominatingCompactification.upperShriekPlusIso fj
        (openCompactification fj) (c j hj)).hom.app K).hom ≫
      ((DominatingCompactification.upperShriekPlusIso fh (c h hh)
        (openCompactification fh)).hom.app ((upperShriekPlus fj (c j hj)).obj K)).hom =
      (upperShriek fh (openCompactification fh)).map ((DominatingCompactification.upperShriekPlusIso
        fj (openCompactification fj) (c j hj)).hom.app K).hom := by
    have nat := (DominatingCompactification.upperShriekPlusIso fh (c h hh)
      (openCompactification fh)).hom.naturality
        ((DominatingCompactification.upperShriekPlusIso fj (openCompactification fj)
          (c j hj)).hom.app K)
    have inv := upperShriekPlusIso_hom_app_comp_symm fh (openCompactification fh) (c h hh)
      ((upperShriekPlus fj (openCompactification fj)).obj K)
    have := congrArg (fun φ => ((DominatingCompactification.upperShriekPlusIso fh
      (openCompactification fh) (c h hh)).hom.app
        ((upperShriekPlus fj (openCompactification fj)).obj K) ≫ φ).hom) nat
    simp only [← Category.assoc, inv, Category.id_comp] at this
    rwa [Category.assoc] at this
  have G4 := congrArg (·.hom) (upperShriekPlusIso_hom_app_comp_symm fj (openCompactification fj)
    (c j hj) K)
  exact shriek_comp_chase (quasiCoherentDerivedPullback' h) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (upperShriekOpenIso_comp fh fj K) G12
    ((upperShriekOpenIso fh).hom.naturality ((DominatingCompactification.upperShriekPlusIso
      fj (openCompactification fj) (c j hj)).hom.app K).hom) G4 rfl

end UpperShriek

end Stacks.Duality

end
