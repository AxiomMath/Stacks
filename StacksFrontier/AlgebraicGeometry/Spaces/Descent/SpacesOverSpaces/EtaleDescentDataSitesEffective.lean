module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleDescentDataSites
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# Effectivity of étale descent data read on spaces-étale sites

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `(U/X, φ)` be a descent
datum relative to `f` with `U` étale over `X`. If the descent datum
`AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData` it induces on the
pseudofunctor of spaces-étale sites is isomorphic to the canonical descent datum of an algebraic
space `W` étale over `Y`, then `(U/X, φ)` is isomorphic to the canonical descent datum of `W`
in the sense of Stacks 0ADQ.

## Main results

In the namespace `AlgebraicGeometry.Space.Descent`:

* `HomDescentData.canonical_transport_move_left`: the move operation of the canonical descent
  datum of a space `W` over `Y` keeps the `W`-coordinate.
* `HomDescentData.homBase_comm`: the commutation of a morphism of descent data on spaces-étale
  sites out of the canonical datum of `W` with the gluing morphisms, read on fibre products.
* `HomDescentData.nonempty_iso_canonicalDescentFunctor_obj`: an isomorphism of descent data on
  spaces-étale sites gives an isomorphism of descent data of algebraic spaces.
* `HomDescentData.exists_isEtale_nonempty_iso_of_toDescentData_iso`: an isomorphism between the
  canonical descent datum of the sheaf `h_W` and the transport of the datum along `V ↦ h_V` makes
  `(U/X, φ)` the canonical descent datum of the étale space `W`.

## References

* [Stacks Project, Tag 0ADQ](https://stacks.math.columbia.edu/tag/0ADQ)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace HomDescentData

section Canonical

variable {P T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : P ⟶ T) (hT : IsAlgebraicSpace B S hS T)
  (hP : IsAlgebraicSpace B S hS P)

/-- **The move operation of a canonical descent datum keeps the coordinate on the space.** For
an algebraic space `W` over `T`, the underlying space of its canonical descent datum relative to
`p : P ⟶ T` is identified with `W ×_T P`, and under that identification the move operation does
not change the `W`-coordinate of a point. -/
theorem canonical_transport_move_left (W : AlgebraicSpacesOver (B := B) (S := S) (hS := hS) T) :
    ∃ α : ((canonicalDescentFunctor.{u, 0} p hT hP).obj W).obj PUnit.unit ≅
        (Over.pullback p).obj W.obj,
      ∀ {Z : Over T} (v : Z ⟶ (Over.map p).obj
          (((canonicalDescentFunctor.{u, 0} p hT hP).obj W).obj PUnit.unit))
        (y : Z ⟶ Over.mk p),
        (((canonicalDescentFunctor.{u, 0} p hT hP).obj W).transport.move
            (i := PUnit.unit) (j := PUnit.unit) v y).left ≫ α.hom.left ≫
            pullback.fst W.obj.hom p =
          v.left ≫ α.hom.left ≫ pullback.fst W.obj.hom p := by
  obtain ⟨α, -, h⟩ := (pullbackDescentDataFunctor.{u, 0, 0} (𝟙 T) p (𝟙 T) p (by simp)
    hT hT hT hP).property
  obtain ⟨q, r, hq, -, hg⟩ := h ((trivialDescentFunctor.{u, 0} T hT).obj W)
  refine ⟨α _, fun {Z} v y ↦ ?_⟩
  dsimp only at hg
  have h₁ := congrArg (· ≫ prod.snd) hg
  simp only [Category.assoc, prod.lift_snd, trivialDescentFunctor, Over.isoMk_hom_left,
    prod.braiding_hom, prod.lift_fst] at h₁
  have h₂ := congrArg (fun k ↦ (prod.lift v y).left ≫ Over.Hom.left k) h₁
  simp only [Over.comp_left, Over.map_map_left] at h₂
  have hq' : (α ((trivialDescentFunctor.{u, 0} T hT).obj W)).hom.left ≫
      pullback.fst W.obj.hom p = q.left := hq.symm
  rw [hq']
  refine (congrArg (fun k ↦ Over.Hom.left k ≫ q.left)
    (DescentData.transport_move _ v y)).trans ?_
  simp only [Over.comp_left, Category.assoc]
  refine h₂.trans ?_
  rw [← Over.comp_left_assoc, prod.lift_fst]

end Canonical

section Comparison

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (D : HomDescentData.{u, 0} f.hom Y.property X.property)
  (hD : IsEtale B S hS (D.obj PUnit.unit).hom) (W : SpacesEtale B S hS Y)

variable (f) in
/-- The test space `(W ×_Y X) ×_Y X` of the universal case. -/
abbrev univObj : AlgebraicSpaces B S hS := pullback (pullback.snd W.obj.hom f ≫ f) f

variable (f) in
/-- The first map of the test space of the universal case to `X`. -/
abbrev univFst : univObj f W ⟶ X := pullback.fst _ _ ≫ pullback.snd W.obj.hom f

/-- The two maps `(W ×_Y X) ×_Y X ⟶ X` of the universal case agree over `Y`. -/
lemma univSnd_comp : pullback.snd (pullback.snd W.obj.hom f ≫ f) f ≫ f = univFst f W ≫ f := by
  rw [Category.assoc]
  exact pullback.condition.symm

/-- The first projection `(W ×_Y X) ×_Y X ⟶ W` and the second map to `X` agree over `Y`. -/
lemma univ_cond :
    (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ pullback.fst W.obj.hom f) ≫ W.obj.hom =
      pullback.snd (pullback.snd W.obj.hom f ≫ f) f ≫ f := by
  rw [Category.assoc, pullback.condition]
  exact pullback.condition

/-- `univSnd_comp` on the underlying morphisms of presheaves. -/
lemma univ_hb : (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom ≫ f.hom =
    (univFst f W ≫ f).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, univSnd_comp]

/-- A map `e₀ : W ×_Y X ⟶ U` over `X` is over `X` on underlying morphisms of presheaves. -/
private lemma hom_comp_hom_of_comp_eq (e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left)
    (he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f) :
    e₀.hom ≫ (D.obj PUnit.unit).hom = (pullback.snd W.obj.hom f).hom :=
  congrArg (fun k ↦ k.hom) he₀

/-- For a map `e₀ : W ×_Y X ⟶ U` over `X`, the map `(W ×_Y X) ×_Y X ⟶ U` it induces lies over
the first map to `X`, on underlying morphisms of presheaves to `Y`. -/
lemma univ_ha (e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left)
    (he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f) :
    (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀).hom ≫ (D.obj PUnit.unit).hom ≫ f.hom =
      (univFst f W ≫ f).hom := by
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    reassoc_of% hom_comp_hom_of_comp_eq D hD W e₀ he₀]

/-- **The universal case of the compatibility of a comparison with the move operation.** Let
`e₀ : W ×_Y X ⟶ U` be a map over `X` and let `T = (W ×_Y X) ×_Y X`. If the base change of `e₀`
to `T` along the first map `T ⟶ X`, followed by the gluing morphism of
`AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData` at the two maps
`T ⟶ X`, is the canonical gluing of `W` followed by the base change of `e₀` along the second
map, then moving the image under `e₀` of the tautological point of `T` is applying `e₀` to the
point with the same `W`-coordinate over the second map. -/
lemma pointMove_universal (e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left)
    (he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f)
    (c₁ : pullback (pullback.snd W.obj.hom f) (univFst f W) ⟶
      pullback W.obj.hom (univFst f W ≫ f))
    (hc₁ : c₁ ≫ pullback.fst W.obj.hom (univFst f W ≫ f) =
      pullback.fst (pullback.snd W.obj.hom f) (univFst f W) ≫ pullback.fst W.obj.hom f)
    (hc₁' : c₁ ≫ pullback.snd W.obj.hom (univFst f W ≫ f) =
      pullback.snd (pullback.snd W.obj.hom f) (univFst f W))
    (c₂ : pullback W.obj.hom (univFst f W ≫ f) ⟶
      pullback (pullback.snd W.obj.hom f) (pullback.snd (pullback.snd W.obj.hom f ≫ f) f))
    (hc₂ : c₂ ≫ pullback.fst (pullback.snd W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) ≫ pullback.fst W.obj.hom f =
      pullback.fst W.obj.hom (univFst f W ≫ f))
    (hc₂' : c₂ ≫ pullback.snd (pullback.snd W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) =
      pullback.snd W.obj.hom (univFst f W ≫ f))
    (a₁ : pullback (pullback.snd W.obj.hom f) (univFst f W) ⟶
      pullback (etaleObj D hD).obj.hom (univFst f W))
    (ha₁ : a₁ ≫ pullback.fst (etaleObj D hD).obj.hom (univFst f W) =
      pullback.fst (pullback.snd W.obj.hom f) (univFst f W) ≫ e₀)
    (ha₁' : a₁ ≫ pullback.snd (etaleObj D hD).obj.hom (univFst f W) =
      pullback.snd (pullback.snd W.obj.hom f) (univFst f W))
    (a₂ : pullback (pullback.snd W.obj.hom f) (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) ⟶
      pullback (etaleObj D hD).obj.hom (pullback.snd (pullback.snd W.obj.hom f ≫ f) f))
    (ha₂ : a₂ ≫ pullback.fst (etaleObj D hD).obj.hom
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) =
      pullback.fst (pullback.snd W.obj.hom f) (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) ≫
        e₀)
    (hc : a₁ ≫ etaleLift D hD (univFst f W ≫ f) (univFst f W)
          (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) rfl (univSnd_comp W) =
      (c₁ ≫ c₂) ≫ a₂) :
    D.pointMove (univFst f W ≫ f).hom
      (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀).hom
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom (univ_ha D hD W e₀ he₀)
      (univ_hb W) =
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f)
        (univ_cond W) ≫ e₀).hom := by
  let tsec : univObj f W ⟶ pullback (pullback.snd W.obj.hom f) (univFst f W) :=
    pullback.lift (pullback.fst _ _) (𝟙 _) (by rw [Category.id_comp])
  have h := congrArg (fun k ↦ tsec ≫ k ≫ pullback.fst (etaleObj D hD).obj.hom
    (pullback.snd (pullback.snd W.obj.hom f ≫ f) f)) hc
  have h' : tsec ≫ a₁ ≫ ObjectProperty.homMk (etaleMove D hD (univFst f W ≫ f) (univFst f W)
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) rfl (univSnd_comp W)) =
      tsec ≫ c₁ ≫ c₂ ≫ pullback.fst _ _ ≫ e₀ := by
    rw [← etaleLift_fst D hD (univFst f W ≫ f) (univFst f W)
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) rfl (univSnd_comp W), ← ha₂]
    simpa only [Category.assoc] using h
  have hpt : tsec ≫ c₁ ≫ c₂ ≫ pullback.fst _ _ =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) (univ_cond W) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hc₂, hc₁, tsec, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.condition, reassoc_of% hc₂', reassoc_of% hc₁', tsec,
        pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
  rw [reassoc_of% hpt] at h'
  refine Eq.trans ?_ (congrArg (fun k ↦ k.hom) h')
  conv_rhs => rw [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, etaleMove,
    D.comp_pointMove, D.comp_pointMove]
  have hs : tsec ≫ a₁ ≫ pullback.snd (etaleObj D hD).obj.hom (univFst f W) = 𝟙 _ := by
    rw [ha₁']
    exact pullback.lift_snd _ _ _
  have hf : tsec ≫ a₁ ≫ pullback.fst (etaleObj D hD).obj.hom (univFst f W) =
      pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀ := by
    rw [ha₁, ← Category.assoc]
    exact congrArg (· ≫ e₀) (pullback.lift_fst _ _ _)
  have hs' : tsec.hom ≫ a₁.hom ≫ (pullback.snd (etaleObj D hD).obj.hom (univFst f W)).hom =
      𝟙 _ :=
    congrArg (fun k ↦ k.hom) hs
  have hf' : tsec.hom ≫ a₁.hom ≫ (pullback.fst (etaleObj D hD).obj.hom (univFst f W)).hom =
      (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀).hom :=
    congrArg (fun k ↦ k.hom) hf
  refine D.pointMove_congr _ _ ?_ hf'.symm ?_ <;> rw [reassoc_of% hs']

/-- The move operation of a descent datum, on underlying presheaves, is `pointMove`. -/
lemma transport_move_left {Z : Over Y.obj}
    (v : Z ⟶ (Over.map f.hom).obj (D.obj PUnit.unit)) (y : Z ⟶ Over.mk f.hom) :
    (D.transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left =
      D.pointMove Z.hom v.left y.left (by simpa using Over.w v) (Over.w y) :=
  rfl

/-- **The compatibility of a comparison with the move operation**, at every point: if
`e₀ : W ×_Y X ⟶ U` satisfies the universal case `pointMove_universal`, then moving the image
under `e₀` of a point `(w, x₀)` of `W ×_Y X` to a point `x` of `X` with the same image in `Y` is
applying `e₀` to the point `(w, x)`. -/
lemma pointMove_comp_of_universal (e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left)
    (he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f)
    (huniv : D.pointMove (univFst f W ≫ f).hom
      (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀).hom
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom (univ_ha D hD W e₀ he₀)
      (univ_hb W) =
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) (univ_cond W) ≫ e₀).hom)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : Z ⟶ W.obj.left.obj) (x₀ x : Z ⟶ X.obj)
    (hw : w ≫ W.obj.hom.hom = x₀ ≫ f.hom) (hx : x ≫ f.hom = x₀ ≫ f.hom) :
    D.pointMove (x₀ ≫ f.hom)
      ((AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)).lift
        w x₀ hw ≫ e₀.hom) x
      (by
        have he₀' : e₀.hom ≫ (D.obj PUnit.unit).hom = (pullback.snd W.obj.hom f).hom :=
          congrArg (fun k ↦ k.hom) he₀
        rw [Category.assoc, reassoc_of% he₀', IsPullback.lift_snd_assoc]) hx =
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)).lift
        w x (hw.trans hx.symm) ≫ e₀.hom := by
  let sqP := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)
  let sqT := AlgebraicSpaces.isPullback_hom B S hS
    (IsPullback.of_hasPullback (pullback.snd W.obj.hom f ≫ f) f)
  let k : Z ⟶ (univObj f W).obj := sqT.lift (sqP.lift w x₀ hw) x
    (by rw [ObjectProperty.FullSubcategory.comp_hom, IsPullback.lift_snd_assoc, hx])
  have hk₁ : k ≫ (pullback.fst (pullback.snd W.obj.hom f ≫ f) f).hom = sqP.lift w x₀ hw :=
    sqT.lift_fst _ _ _
  have hk₂ : k ≫ (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom = x := sqT.lift_snd _ _ _
  have h := congrArg (k ≫ ·) huniv
  dsimp only at h
  rw [D.comp_pointMove] at h
  refine (D.pointMove_congr _ _ ?_ ?_ ?_).trans (h.trans ?_)
  · simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, reassoc_of% hk₁,
      IsPullback.lift_snd_assoc]
  · simp only [ObjectProperty.FullSubcategory.comp_hom, reassoc_of% hk₁]
  · rw [hk₂]
  · rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc]
    congr 1
    apply sqP.hom_ext
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, pullback.lift_fst,
        ObjectProperty.FullSubcategory.comp_hom, reassoc_of% hk₁, IsPullback.lift_fst,
        IsPullback.lift_fst]
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, pullback.lift_snd, hk₂,
        IsPullback.lift_snd]

/-- The composition comparison of the pseudofunctor of spaces-étale sites from `f` and `g` to
`q`, at `W`, on the underlying fibre products. -/
def canInv {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    pullback (pullback.snd W.obj.hom f) g ⟶ pullback W.obj.hom q :=
  (((spacesEtaleSitePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← h]; rfl)).inv.toNatTrans.app W).hom.left

/-- The inverse of `canInv`. -/
def canHom {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    pullback W.obj.hom q ⟶ pullback (pullback.snd W.obj.hom f) g :=
  (((spacesEtaleSitePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← h]; rfl)).hom.toNatTrans.app W).hom.left

/-- The first projection of `canInv`. -/
lemma canInv_fst {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    canInv W g q h ≫ pullback.fst W.obj.hom q =
      pullback.fst (pullback.snd W.obj.hom f) g ≫ pullback.fst W.obj.hom f := by
  subst h
  exact spacesEtaleSitePseudofunctor_mapComp'_inv_app_fst B S hS f.op.toLoc g.op.toLoc
    (g ≫ f).op.toLoc rfl W

/-- The second projection of `canInv`. -/
lemma canInv_snd {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    canInv W g q h ≫ pullback.snd W.obj.hom q = pullback.snd (pullback.snd W.obj.hom f) g :=
  Over.w (((spacesEtaleSitePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← h]; rfl)).inv.toNatTrans.app W).hom

/-- The first projection of `canHom`. -/
lemma canHom_fst {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    canHom W g q h ≫ pullback.fst (pullback.snd W.obj.hom f) g ≫ pullback.fst W.obj.hom f =
      pullback.fst W.obj.hom q := by
  subst h
  exact spacesEtaleSitePseudofunctor_mapComp'_hom_app_fst B S hS f.op.toLoc g.op.toLoc
    (g ≫ f).op.toLoc rfl W

/-- The second projection of `canHom`. -/
lemma canHom_snd {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) (q : Y' ⟶ Y) (h : g ≫ f = q) :
    canHom W g q h ≫ pullback.snd (pullback.snd W.obj.hom f) g = pullback.snd W.obj.hom q :=
  Over.w (((spacesEtaleSitePseudofunctor B S hS).mapComp' f.op.toLoc g.op.toLoc q.op.toLoc
    (by rw [← h]; rfl)).hom.toNatTrans.app W).hom

variable (φ : ((spacesEtaleSitePseudofunctor B S hS).toDescentData (fun _ : Unit ↦ f)).obj W ⟶
  D.toSpacesEtaleDescentData hD)

/-- The component of a morphism of descent data on spaces-étale sites out of the canonical
descent datum of `W`, as a map `W ×_Y X ⟶ U`. -/
def homLeft : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left :=
  (φ.hom ()).hom.left

/-- `homLeft` is a map over `X`. -/
lemma homLeft_comp : homLeft D hD W φ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f :=
  Over.w (φ.hom ()).hom

/-- The base change along `g` of the component of `φ`, on fibre products. -/
def homBase {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) :
    pullback (pullback.snd W.obj.hom f) g ⟶ pullback (etaleObj D hD).obj.hom g :=
  (((spacesEtaleSitePseudofunctor B S hS).map g.op.toLoc).toFunctor.map (φ.hom ())).hom.left

/-- The first projection of `homBase`. -/
lemma homBase_fst {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) :
    homBase D hD W φ g ≫ pullback.fst (etaleObj D hD).obj.hom g =
      pullback.fst (pullback.snd W.obj.hom f) g ≫ homLeft D hD W φ :=
  pullback.lift_fst _ _ _

/-- The second projection of `homBase`. -/
lemma homBase_snd {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) :
    homBase D hD W φ g ≫ pullback.snd (etaleObj D hD).obj.hom g =
      pullback.snd (pullback.snd W.obj.hom f) g :=
  pullback.lift_snd _ _ _

/-- Composition in the fibres of the pseudofunctor of spaces-étale sites, on underlying
spaces. -/
lemma spacesEtaleSitePseudofunctor_comp_hom_left {a : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ}
    {M N K : (spacesEtaleSitePseudofunctor B S hS).obj a} (x : M ⟶ N) (y : N ⟶ K) :
    (x ≫ y).hom.left = x.hom.left ≫ y.hom.left :=
  rfl

/-- **A morphism of descent data on spaces-étale sites, on fibre products.** The commutation
of a morphism `φ` of descent data with the gluing morphisms, at a test space `Y'` with two maps
`f₁, f₂` to `X` agreeing over `Y`, read on the underlying fibre products. -/
lemma descentDataHom_comm_hom_left
    {D₁ D₂ : (spacesEtaleSitePseudofunctor B S hS).DescentData (fun _ : Unit ↦ f)}
    (ψ : D₁ ⟶ D₂) {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    (((spacesEtaleSitePseudofunctor B S hS).map f₁.op.toLoc).toFunctor.map (ψ.hom ())).hom.left ≫
        (D₂.hom q (i₁ := ()) (i₂ := ()) f₁ f₂ h₁ h₂).hom.left =
      (D₁.hom q (i₁ := ()) (i₂ := ()) f₁ f₂ h₁ h₂).hom.left ≫
        (((spacesEtaleSitePseudofunctor B S hS).map f₂.op.toLoc).toFunctor.map
          (ψ.hom ())).hom.left :=
  (spacesEtaleSitePseudofunctor_comp_hom_left _ _).symm.trans
    ((congrArg (fun ψ ↦ ψ.hom.left) (ψ.comm q (i₁ := ()) (i₂ := ()) f₁ f₂ h₁ h₂)).trans
      (spacesEtaleSitePseudofunctor_comp_hom_left _ _))

/-- The commutation of `φ` with the gluing morphisms, on fibre products, in terms of
`homBase`, `canInv` and `canHom`. -/
lemma homBase_comm {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    homBase D hD W φ f₁ ≫ etaleLift D hD q f₁ f₂ h₁ h₂ =
      (canInv W f₁ q h₁ ≫ canHom W f₂ q h₂) ≫ homBase D hD W φ f₂ :=
  descentDataHom_comm_hom_left φ q f₁ f₂ h₁ h₂

/-- The universal case `pointMove_universal` for the map `W ×_Y X ⟶ U` underlying a morphism
of descent data on spaces-étale sites. -/
lemma pointMove_universal_of_hom :
    D.pointMove (univFst f W ≫ f).hom
      (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ homLeft D hD W φ).hom
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom
      (univ_ha D hD W _ (homLeft_comp D hD W φ)) (univ_hb W) =
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) (univ_cond W) ≫
          homLeft D hD W φ).hom :=
  pointMove_universal D hD W _ (homLeft_comp D hD W φ) _ (canInv_fst W _ _ rfl)
    (canInv_snd W _ _ rfl) _ (canHom_fst W _ _ (univSnd_comp W)) (canHom_snd W _ _ _) _
    (homBase_fst D hD W φ _) (homBase_snd D hD W φ _) _ (homBase_fst D hD W φ _)
    (homBase_comm D hD W φ _ _ _ rfl (univSnd_comp W))

/-- `W`, as an algebraic space over the underlying presheaf of `Y`. -/
abbrev overObj : AlgebraicSpacesOver (B := B) (S := S) (hS := hS) Y.obj :=
  ⟨Over.mk W.obj.hom.hom, W.obj.left.property⟩

/-- The comparison map is compatible with the move operations, given the universal case. -/
lemma move_comp_of_universal
    (α : ((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
        (overObj W)).obj PUnit.unit ≅ (Over.pullback f.hom).obj (overObj W).obj)
    (hα : ∀ {Z : Over Y.obj} (v : Z ⟶ (Over.map f.hom).obj
          (((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
            (overObj W)).obj PUnit.unit))
        (y : Z ⟶ Over.mk f.hom),
        (((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
            (overObj W)).transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
            α.hom.left ≫ pullback.fst (overObj W).obj.hom f.hom =
          v.left ≫ α.hom.left ≫ pullback.fst (overObj W).obj.hom f.hom)
    (e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left)
    (he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f)
    (huniv : D.pointMove (univFst f W ≫ f).hom
      (pullback.fst (pullback.snd W.obj.hom f ≫ f) f ≫ e₀).hom
      (pullback.snd (pullback.snd W.obj.hom f ≫ f) f).hom (univ_ha D hD W e₀ he₀)
      (univ_hb W) =
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst W.obj.hom f)
        (pullback.snd (pullback.snd W.obj.hom f ≫ f) f) (univ_cond W) ≫ e₀).hom)
    (m₀ : Limits.pullback (overObj W).obj.hom f.hom ≅ (D.obj PUnit.unit).left)
    (hm₀ : m₀.hom ≫ (D.obj PUnit.unit).hom = pullback.snd (overObj W).obj.hom f.hom)
    (hlift : ∀ {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : Z' ⟶ W.obj.left.obj)
      (x : Z' ⟶ X.obj) (h : w ≫ W.obj.hom.hom = x ≫ f.hom),
      pullback.lift (f := (overObj W).obj.hom) w x h ≫ m₀.hom =
        (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)).lift
          w x h ≫ e₀.hom)
    {Z : Over Y.obj}
    (v : Z ⟶ (Over.map f.hom).obj
      (((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
        (overObj W)).obj PUnit.unit))
    (y : Z ⟶ Over.mk f.hom) :
    ((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
        (overObj W)).transport.move (i := PUnit.unit) (j := PUnit.unit) v y ≫
        (Over.map f.hom).map (α ≪≫ Over.isoMk m₀ hm₀).hom =
      D.transport.move (i := PUnit.unit) (j := PUnit.unit)
        (v ≫ (Over.map f.hom).map (α ≪≫ Over.isoMk m₀ hm₀).hom) y := by
  let sqP := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)
  let can := (canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj (overObj W)
  apply Over.OverMorphism.ext
  rw [Over.comp_left, transport_move_left D]
  have hα₂ : α.hom.left ≫ pullback.snd (overObj W).obj.hom f.hom = (can.obj PUnit.unit).hom :=
    Over.w α.hom
  have hv₁ : v.left ≫ (can.obj PUnit.unit).hom ≫ f.hom = Z.hom := by
    simpa using Over.w v
  have hy₁ : y.left ≫ f.hom = Z.hom := by simpa using Over.w y
  have hbase : (can.transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
      (can.obj PUnit.unit).hom = y.left :=
    congrArg (fun k ↦ k.left) (can.transport.move_base v y)
  let w : Z.left ⟶ W.obj.left.obj := v.left ≫ α.hom.left ≫ pullback.fst (overObj W).obj.hom f.hom
  let x₀ : Z.left ⟶ X.obj := v.left ≫ α.hom.left ≫ pullback.snd (overObj W).obj.hom f.hom
  have hZ : x₀ ≫ f.hom = Z.hom := by
    simp only [x₀, Category.assoc, reassoc_of% hα₂, hv₁]
  have hwx₀ : w ≫ W.obj.hom.hom = x₀ ≫ f.hom := by
    simp only [w, x₀, Category.assoc]
    exact congrArg (fun k ↦ v.left ≫ α.hom.left ≫ k) pullback.condition
  have hyx : y.left ≫ f.hom = x₀ ≫ f.hom := hy₁.trans hZ.symm
  have hmove : (can.transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
      α.hom.left = pullback.lift (f := (overObj W).obj.hom) w y.left (hwx₀.trans hyx.symm) := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((hα v y).trans (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg _ hα₂).trans
        (hbase.trans (pullback.lift_snd _ _ _).symm))
  have hv : v.left ≫ α.hom.left = pullback.lift (f := (overObj W).obj.hom) w x₀ hwx₀ :=
    pullback.hom_ext ((Category.assoc _ _ _).trans (pullback.lift_fst _ _ _).symm)
      ((Category.assoc _ _ _).trans (pullback.lift_snd _ _ _).symm)
  have hl : (can.transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
      α.hom.left ≫ m₀.hom = sqP.lift w y.left (hwx₀.trans hyx.symm) ≫ e₀.hom := by
    rw [← Category.assoc, hmove, hlift]
  have hr : v.left ≫ α.hom.left ≫ m₀.hom = sqP.lift w x₀ hwx₀ ≫ e₀.hom := by
    rw [← Category.assoc, hv, hlift]
  refine hl.trans ((pointMove_comp_of_universal D hD W e₀ he₀ huniv w x₀ y.left hwx₀
    hyx).symm.trans (D.pointMove_congr _ _ hZ hr.symm rfl))

/-- **An isomorphism of descent data on spaces-étale sites is an isomorphism of descent data of
algebraic spaces.** Let `(U/X, φ)` be a descent datum relative to `f : X ⟶ Y` with `U` étale over
`X`, and let `W` be an algebraic space étale over `Y`. If the canonical descent datum of `W` for
the pseudofunctor of spaces-étale sites is isomorphic to
`AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData`, then the canonical
descent datum of `W` in the sense of Stacks 0ADQ is isomorphic to `(U/X, φ)`. -/
theorem nonempty_iso_canonicalDescentFunctor_obj
    (e : ((spacesEtaleSitePseudofunctor B S hS).toDescentData (fun _ : Unit ↦ f)).obj W ≅
      D.toSpacesEtaleDescentData hD) :
    Nonempty ((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj
      (overObj W) ≅ D) := by
  obtain ⟨α, hα⟩ := canonical_transport_move_left f.hom Y.property X.property (overObj W)
  let e₀ : pullback W.obj.hom f ⟶ (etaleObj D hD).obj.left := homLeft D hD W e.hom
  let e₀' : (etaleObj D hD).obj.left ⟶ pullback W.obj.hom f := (e.inv.hom ()).hom.left
  have he₀ : e₀ ≫ (etaleObj D hD).obj.hom = pullback.snd W.obj.hom f :=
    homLeft_comp D hD W e.hom
  have hinv₁ : e₀ ≫ e₀' = 𝟙 _ := congrArg (fun φ ↦ (φ.hom ()).hom.left) e.hom_inv_id
  have hinv₂ : e₀' ≫ e₀ = 𝟙 _ := congrArg (fun φ ↦ (φ.hom ()).hom.left) e.inv_hom_id
  let sqP := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback W.obj.hom f)
  let m₀ : Limits.pullback (overObj W).obj.hom f.hom ≅ (D.obj PUnit.unit).left :=
    sqP.isoPullback.symm ≪≫
      { hom := e₀.hom, inv := e₀'.hom
        hom_inv_id := congrArg (fun k ↦ k.hom) hinv₁
        inv_hom_id := congrArg (fun k ↦ k.hom) hinv₂ }
  have hm₀e : m₀.hom = sqP.isoPullback.inv ≫ e₀.hom := rfl
  have hm₀ : m₀.hom ≫ (D.obj PUnit.unit).hom = pullback.snd (overObj W).obj.hom f.hom := by
    rw [hm₀e, Category.assoc, hom_comp_hom_of_comp_eq D hD W e₀ he₀]
    exact IsPullback.isoPullback_inv_snd _
  have hlift : ∀ {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : Z' ⟶ W.obj.left.obj)
      (x : Z' ⟶ X.obj) (h : w ≫ W.obj.hom.hom = x ≫ f.hom),
      pullback.lift (f := (overObj W).obj.hom) w x h ≫ m₀.hom = sqP.lift w x h ≫ e₀.hom := by
    intro Z' w x h
    rw [hm₀e, ← Category.assoc]
    congr 1
    apply sqP.hom_ext
    · simpa using pullback.lift_fst _ _ _
    · simpa using pullback.lift_snd _ _ _
  let m := α ≪≫ Over.isoMk m₀ hm₀
  let ψ := DescentData.homOfMove (fun _ ↦ m.hom) (fun {i j Z} v y ↦ by
    cases i
    cases j
    exact move_comp_of_universal D hD W α hα e₀ he₀ (pointMove_universal_of_hom D hD W e.hom)
      m₀ hm₀ hlift v y)
  exact ⟨DescentData.isoMk (fun _ ↦ m) (fun i j ↦ ψ.comm i j)⟩

end Comparison

section Assembly

attribute [local instance] uliftCategory

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (D : HomDescentData.{u, 0} f.hom Y.property X.property)
  (hD : IsEtale B S hS (D.obj PUnit.unit).hom)

/-- **From an effective descent datum of sheaves back to algebraic spaces.** Let `(U/X, φ)` be
a descent datum relative to `f : X ⟶ Y` with `U` étale over `X`, and let `W` be an algebraic
space étale over `Y`. If the canonical descent datum of the sheaf `h_W` for the pseudofunctor of
spaces-étale sheaves is isomorphic to the transport of
`AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData` along `V ↦ h_V`, then
`(U/X, φ)` is isomorphic to the canonical descent datum of `W`, which is étale over `Y`. -/
theorem exists_isEtale_nonempty_iso_of_toDescentData_iso (W : SpacesEtale B S hS Y)
    (e : ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit ↦ f)).obj
        ((SpacesEtale.topology B S hS Y).yoneda.obj W) ≅
      ((spacesEtaleYonedaStrongTrans B S hS).descentDataFunctor (fun _ : Unit ↦ f)).obj
        (D.toSpacesEtaleDescentData hD).uliftObj.{u + 2}) :
    ∃ V : AlgebraicSpacesOver (B := B) (S := S) (hS := hS) Y.1,
      IsEtale B S hS V.obj.hom ∧
        Nonempty ((canonicalDescentFunctor.{u, 0} f.hom Y.property X.property).obj V ≅ D) := by
  let τ := spacesEtaleYonedaStrongTrans B S hS
  have := τ.full_descentDataFunctor (fun _ : Unit ↦ f)
  have := τ.faithful_descentDataFunctor (fun _ : Unit ↦ f)
  let e₁ := (τ.toDescentDataCompDescentDataFunctorIso (fun _ : Unit ↦ f)).app (ULift.up W) ≪≫ e
  let e₂ := (τ.descentDataFunctor (fun _ : Unit ↦ f)).preimageIso e₁
  exact ⟨overObj W, W.property, nonempty_iso_canonicalDescentFunctor_obj D hD W
    (Pseudofunctor.DescentData.isoOfToDescentDataUliftObjIso e₂)⟩

end Assembly

end HomDescentData

end AlgebraicGeometry.Space.Descent

end
