module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Restriction of an algebraic space to a smaller base scheme (Stacks 03I5 (1))

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `j = Over.map g` be the associated
localization functor from the big fppf site of `S` to that of `S'`. Stacks 03I5 part (1) says that
restriction along `j` — that is, precomposition with `jᵒᵖ`, the functor
`CategoryTheory.OverShriek.relocalizeRestrict g` — carries algebraic spaces over `S'` to algebraic
spaces over `S`. The complementary part (2), the lower-shriek extension, is
`AlgebraicGeometry.isAlgebraicSpace_viewOver`.

## Main results

* `CategoryTheory.OverShriek.isPullback_restrictReindex`: the reindexing square, the engine of the
  whole file.
* `CategoryTheory.OverShriek.relativelyRepresentable_relocalizeRestrict_map` and
  `CategoryTheory.OverShriek.relative_relocalizeRestrict_map`: restriction preserves relative
  representability, and any relative property of morphisms inherited by reindexing.
* `CategoryTheory.OverShriek.restrictYonedaIso`: the restriction of a representable presheaf is
  represented by the base change of the representing object, by
  `CategoryTheory.Over.mapPullbackAdj`;
  `CategoryTheory.OverShriek.restrictYonedaIso_hom_app_left` computes it on a section, as
  composition with the first projection of that base change.
* `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict`: **Stacks 03I5 (1)**, the restriction of
  an algebraic space is an algebraic space.
* `AlgebraicGeometry.baseChangePresentation`: **Stacks 03I4 (6)**, the restriction of a
  presentation `U'/R'` is the presentation of the restricted space obtained by base changing both
  the presenting scheme and its relation along `g`.

## Implementation notes

The source proves part (1) by exhibiting a presentation of the restriction — base change both the
atlas and its étale equivalence relation and appeal to Theorem 02WW, that the quotient of an étale
equivalence relation is an algebraic space. Theorem 02WW is not in the library, so the three
defining conditions of `AlgebraicGeometry.IsAlgebraicSpace` are verified for the restriction
directly instead. That is possible because restriction is *reindexing*, and reindexing changes
neither the objects nor the morphisms of schemes involved:

* the sheaf condition is `AlgebraicGeometry.isSheaf_relocalizeRestrict`, the continuity of the
  localization functor;
* for the diagonal and for the atlas the common input is the reindexing square
  `CategoryTheory.OverShriek.isPullback_restrictReindex`. A section of a restricted presheaf over
  `V` is a section of the original over `j V`
  (`CategoryTheory.OverShriek.restrictYonedaEquiv`), so the fibre product of `h : A ⟶ G` with such
  a section is already represented over `S'`, by some `b ⟶ j V`; and a morphism `j T ⟶ b` comes
  from a morphism `T ⟶ V` of the big fppf site of `S` exactly when its composite
  `T ⟶ b.left ⟶ V.left ⟶ S` is the structure morphism of `T`. So `b` with the structure morphism
  `b.left ⟶ V.left ⟶ S` — the *reindexing*
  `CategoryTheory.OverShriek.restrictReindex` — represents the fibre product formed over `S`.
  Since reindexing leaves the underlying morphism of schemes untouched
  (`AlgebraicGeometry.inverseImage_restrictReindexSnd`), surjectivity and étaleness of the atlas
  transfer on the nose.

Representability of the diagonal is obtained from
`CategoryTheory.Functor.relativelyRepresentable.diag_of_map_from_obj`: a morphism
`h_V ⟶ F'|_S` factors as the tautological morphism `h_V ⟶ (h_{j V})|_S` followed by the
restriction of a morphism `h_{j V} ⟶ F'`
(`CategoryTheory.OverShriek.eq_restrictYonedaUnit_comp`). The second factor is handled by the
reindexing square; the first is the Yoneda image of the unit of
`CategoryTheory.Over.mapPullbackAdj` (`CategoryTheory.OverShriek.restrictYonedaUnit_eq`), hence
relatively representable because it is a morphism of representables. This is the one place where a
fibre product of schemes is needed, and it is exactly the step that the restriction of a
representable presheaf is representable.

Part (6) base changes the atlas and relation of a presentation of `F'` along `g`, using
`CategoryTheory.Over.pullback g`. Its kernel-pair square is the image, under `relocalizeRestrict
g`, of that of the original presentation, read back along the representability comparison
`CategoryTheory.OverShriek.restrictYonedaIso` via its naturality
(`CategoryTheory.OverShriek.restrictYonedaIso_naturality`). Étaleness of the base-changed
projections follows because `CategoryTheory.Over.pullback`'s action on a morphism is itself a
base change of the underlying morphism of schemes
(`CategoryTheory.OverShriek.isPullback_pullback_map`), and `Etale` is stable under base change.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} (g : X ⟶ Y)

/-- **Sections of a restricted presheaf over `V` are sections of the original over `j V`.** Both
hom-sets are the value of `G` at `j V`, so this is the Yoneda lemma applied twice. -/
@[sga "3 I 1.6.1" "Γ(F_S) ≃ Hom(h_S"]
def restrictYonedaEquiv (V : Over X) (G : (Over Y)ᵒᵖ ⥤ Type v) :
    (yoneda.obj V ⟶ (relocalizeRestrict g).obj G) ≃
      (yoneda.obj ((Over.map g).obj V) ⟶ G) :=
  (yonedaEquiv (X := V) (F := (relocalizeRestrict g).obj G)).trans
    (yonedaEquiv (X := (Over.map g).obj V) (F := G)).symm

/-- The morphism of presheaves on `C/X` attached to `α : h_{j V} ⟶ G` sends a morphism `k` of
`C/X` to the value of `α` at its image `j k`. -/
theorem restrictYonedaEquiv_symm_app_apply {V : Over X} {G : (Over Y)ᵒᵖ ⥤ Type v}
    (α : yoneda.obj ((Over.map g).obj V) ⟶ G) (T : Over X) (k : T ⟶ V) :
    ((restrictYonedaEquiv g V G).symm α).app (op T) k =
      α.app (op ((Over.map g).obj T)) ((Over.map g).map k) := by
  show G.map ((Over.map g).map k).op (yonedaEquiv α) = _
  rw [yonedaEquiv_naturality]
  simp [yonedaEquiv]

/-- `CategoryTheory.OverShriek.restrictYonedaEquiv_symm_app_apply`, read in the other direction:
a morphism `t : h_V ⟶ G|_X` is determined by the morphism `h_{j V} ⟶ G` it corresponds to. -/
theorem restrictYonedaEquiv_app_apply {V : Over X} {G : (Over Y)ᵒᵖ ⥤ Type v}
    (t : yoneda.obj V ⟶ (relocalizeRestrict g).obj G) (T : Over X) (k : T ⟶ V) :
    t.app (op T) k =
      (restrictYonedaEquiv g V G t).app (op ((Over.map g).obj T)) ((Over.map g).map k) := by
  conv_lhs => rw [← (restrictYonedaEquiv g V G).symm_apply_apply t]
  rw [restrictYonedaEquiv_symm_app_apply]

section Reindex

variable {V : Over X} {b : Over Y} (s : b ⟶ (Over.map g).obj V)

/-- **Reindexing.** An object of `C/Y` equipped with a morphism `s` to `j V` is an object of `C/X`,
with structure morphism the composite `b.left ⟶ V.left ⟶ X`. -/
def restrictReindex : Over X := Over.mk (s.left ≫ V.hom)

/-- The reindexing of `b` along `s : b ⟶ j V` comes with a morphism to `V` over `X`, namely `s`
again. -/
def restrictReindexSnd : restrictReindex g s ⟶ V := Over.homMk s.left rfl

/-- Reindexing and then viewing over `Y` again recovers `b`: both have underlying object `b.left`
and structure morphism `b.left ⟶ V.left ⟶ X ⟶ Y`. -/
def restrictReindexIso : (Over.map g).obj (restrictReindex g s) ≅ b :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ b.hom = (s.left ≫ V.hom) ≫ g
    rw [Category.id_comp, Category.assoc]
    exact (Over.w s).symm)

/-- Reindexing leaves the underlying morphism of `C` untouched. -/
@[simp]
theorem restrictReindexSnd_left : (restrictReindexSnd g s).left = s.left := rfl

/-- The comparison isomorphism of `CategoryTheory.OverShriek.restrictReindexIso` is the
identity on underlying objects. -/
@[simp]
theorem restrictReindexIso_hom_left : (restrictReindexIso g s).hom.left = 𝟙 b.left := rfl

/-- The comparison isomorphism identifies `s` with the image of the reindexed morphism to `V`. -/
theorem restrictReindexIso_hom_comp :
    (restrictReindexIso g s).hom ≫ s = (Over.map g).map (restrictReindexSnd g s) :=
  Over.OverMorphism.ext (by
    rw [Over.comp_left, restrictReindexIso_hom_left]
    exact Category.id_comp s.left)

/-- **Restriction carries a represented pullback square over `Y` to one over `X`.**

If the fibre product of `h : A ⟶ G` and a section `t` of the restriction of `G`, formed over `Y`
against `j V`, is represented by `b`, then the fibre product formed over `X` against `V` is
represented by the reindexing of `b`: a morphism `j T ⟶ b` lands in the smaller fibre product
exactly when its composite with `b ⟶ j V ⟶ j X` factors the structure morphism of `T`, which is
what the reindexed structure morphism of `b` records. -/
theorem isPullback_restrictReindex {A G : (Over Y)ᵒᵖ ⥤ Type v} (h : A ⟶ G)
    (t : yoneda.obj V ⟶ (relocalizeRestrict g).obj G) {fs : yoneda.obj b ⟶ A}
    (hpb : IsPullback fs (yoneda.map s) h (restrictYonedaEquiv g V G t)) :
    IsPullback ((restrictYonedaEquiv g (restrictReindex g s) A).symm
        (yoneda.map (restrictReindexIso g s).hom ≫ fs))
      (yoneda.map (restrictReindexSnd g s))
      ((relocalizeRestrict g).map h) t := by
  have hιs : (restrictReindexIso g s).hom ≫ s = (Over.map g).map (restrictReindexSnd g s) :=
    restrictReindexIso_hom_comp g s
  apply IsPullback.of_forall_isPullback_app
  intro T
  set W : Over Y := (Over.map g).obj (unop T)
  set t' := restrictYonedaEquiv g V G t
  have hT := hpb.app (op W)
  rw [Limits.Types.isPullback_iff] at hT
  have keyw : ∀ x : W ⟶ b, h.app (op W) (fs.app (op W) x) = t'.app (op W) (x ≫ s) := by
    intro x
    rw [← types_comp_apply (fs.app (op W)) (h.app (op W)) x, hT.1]
    rfl
  have keysurj : ∀ (α : A.obj (op W)) (m' : W ⟶ (Over.map g).obj V),
      h.app (op W) α = t'.app (op W) m' → ∃ x : W ⟶ b, fs.app (op W) x = α ∧ x ≫ s = m' :=
    fun α m' hm' => hT.2.2 α m' hm'
  have hp : ∀ k : unop T ⟶ restrictReindex g s,
      ((restrictYonedaEquiv g (restrictReindex g s) A).symm
          (yoneda.map (restrictReindexIso g s).hom ≫ fs)).app T k =
        fs.app (op W) ((Over.map g).map k ≫ (restrictReindexIso g s).hom) := by
    intro k
    rw [restrictYonedaEquiv_symm_app_apply]
    rfl
  have ht : ∀ m : unop T ⟶ V, t.app T m = t'.app (op W) ((Over.map g).map m) :=
    fun m => restrictYonedaEquiv_app_apply g t (unop T) m
  have hρ : ∀ α : ((relocalizeRestrict g).obj A).obj T,
      ((relocalizeRestrict g).map h).app T α = h.app (op W) α := fun _ => rfl
  have hq : ∀ k : unop T ⟶ restrictReindex g s,
      (yoneda.map (restrictReindexSnd g s)).app T k = k ≫ restrictReindexSnd g s :=
    fun _ => rfl
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, fun k k' hkk' => ?_, fun α m hα => ?_⟩
  · ext k
    show ((relocalizeRestrict g).map h).app T
        (((restrictYonedaEquiv g (restrictReindex g s) A).symm
          (yoneda.map (restrictReindexIso g s).hom ≫ fs)).app T k) =
      t.app T ((yoneda.map (restrictReindexSnd g s)).app T k)
    rw [hp k, hρ, keyw, hq, ht (k ≫ restrictReindexSnd g s)]
    congr 1
    rw [Category.assoc, hιs, ← Functor.map_comp]
  · obtain ⟨h₁, h₂⟩ := hkk'
    have h₁' : fs.app (op W) ((Over.map g).map k ≫ (restrictReindexIso g s).hom) =
        fs.app (op W) ((Over.map g).map k' ≫ (restrictReindexIso g s).hom) := by
      rwa [← hp k, ← hp k']
    have h₂' : ((Over.map g).map k ≫ (restrictReindexIso g s).hom) ≫ s =
        ((Over.map g).map k' ≫ (restrictReindexIso g s).hom) ≫ s := by
      rw [Category.assoc, Category.assoc, hιs, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun n : unop T ⟶ V => (Over.map g).map n)
        (show k ≫ restrictReindexSnd g s = k' ≫ restrictReindexSnd g s from h₂)
    have hcomp := hT.2.1 _ _ ⟨h₁', h₂'⟩
    have hcomp' : (Over.map g).map k = (Over.map g).map k' :=
      (cancel_mono (restrictReindexIso g s).hom).mp hcomp
    exact Over.OverMorphism.ext (congrArg (·.left) hcomp')
  · have hα' : h.app (op W) α = t'.app (op W) ((Over.map g).map m) := by
      rwa [← ht m]
    obtain ⟨n, hn₁, hn₂⟩ := keysurj α ((Over.map g).map m) hα'
    have hnleft : n.left ≫ s.left = m.left := by
      simpa using congrArg (·.left) hn₂
    have hk : n.left ≫ (restrictReindex g s).hom = (unop T).hom := by
      show n.left ≫ s.left ≫ V.hom = (unop T).hom
      rw [← Category.assoc, hnleft]
      exact Over.w m
    refine ⟨Over.homMk n.left hk, ?_, ?_⟩
    · have hn : (Over.map g).map (Over.homMk n.left hk : unop T ⟶ restrictReindex g s) ≫
          (restrictReindexIso g s).hom = n :=
        Over.OverMorphism.ext (by
          rw [Over.comp_left, restrictReindexIso_hom_left]
          exact Category.comp_id n.left)
      rw [hp, hn]
      exact hn₁
    · show (Over.homMk n.left hk : unop T ⟶ restrictReindex g s) ≫ restrictReindexSnd g s = m
      exact Over.OverMorphism.ext (by rwa [Over.comp_left])

end Reindex

/-- **Restriction preserves relative representability.** The fibre product against a section of
the restriction is already represented over `Y`, and its reindexing represents the fibre product
formed over `X` (`CategoryTheory.OverShriek.isPullback_restrictReindex`). -/
theorem relativelyRepresentable_relocalizeRestrict_map
    {A G : (Over Y)ᵒᵖ ⥤ Type v} {h : A ⟶ G} (hh : yoneda.relativelyRepresentable h) :
    yoneda.relativelyRepresentable ((relocalizeRestrict g).map h) := by
  intro V t
  obtain ⟨b, s, fs, hpb⟩ := hh (restrictYonedaEquiv g V G t)
  exact ⟨_, _, _, isPullback_restrictReindex g s h t hpb⟩

/-- **Restriction preserves a relative property of morphisms of presheaves**, provided the
property is inherited by the reindexing of a morphism over `Y` to one over `X`. -/
theorem relative_relocalizeRestrict_map
    {P : MorphismProperty (Over X)} {P' : MorphismProperty (Over Y)} [P.RespectsIso]
    (hPP' : ∀ {V : Over X} {b : Over Y} (s : b ⟶ (Over.map g).obj V),
      P' s → P (restrictReindexSnd g s))
    {A G : (Over Y)ᵒᵖ ⥤ Type v} {h : A ⟶ G} (hh : P'.presheaf h) :
    P.presheaf ((relocalizeRestrict g).map h) := by
  refine MorphismProperty.relative.of_exists fun V t => ?_
  obtain ⟨b, s, fs, hpb⟩ := hh.1 (restrictYonedaEquiv g V G t)
  exact ⟨_, _, _, isPullback_restrictReindex g s h t hpb, hPP' s (hh.2 _ _ _ hpb)⟩

section Representable

variable [Limits.HasPullbacks C]

/-- **The restriction of a representable presheaf is representable**, by the base change of the
representing object along `g`: this is the adjunction `CategoryTheory.Over.mapPullbackAdj`. -/
@[sga "3 I 1.6.1" "partial"]
noncomputable def restrictYonedaRepresentableBy (X' : Over Y) :
    ((relocalizeRestrict g).obj (yoneda.obj X')).RepresentableBy
      ((Over.pullback g).obj X') where
  homEquiv {T} := ((Over.mapPullbackAdj g).homEquiv T X').symm
  homEquiv_comp f k := (Over.mapPullbackAdj g).homEquiv_naturality_left_symm f k

/-- `CategoryTheory.OverShriek.restrictYonedaRepresentableBy` as an isomorphism of presheaves. -/
noncomputable def restrictYonedaIso (X' : Over Y) :
    yoneda.obj ((Over.pullback g).obj X') ≅ (relocalizeRestrict g).obj (yoneda.obj X') :=
  Functor.representableByEquiv (restrictYonedaRepresentableBy g X')

/-- **The identification of the restriction of a representable presheaf, on sections.** A
section of the restriction of `h_{X'}` over `T`, that is a morphism `j T ⟶ X'`, is obtained
from the corresponding morphism `T ⟶ X' ×_Y X` by composing with the first projection. -/
theorem restrictYonedaIso_hom_app_left (X' : Over Y) (T : Over X)
    (t : T ⟶ (Over.pullback g).obj X') :
    ((restrictYonedaIso g X').hom.app (op T) t).left = t.left ≫ pullback.fst X'.hom g := by
  have h : (restrictYonedaIso g X').hom.app (op T) t =
      ((Over.mapPullbackAdj g).homEquiv T X').symm t := rfl
  rw [h, Adjunction.homEquiv_counit, Over.comp_left]
  simp

/-- The tautological morphism from `h_V` to the restriction of `h_{j V}`, which sends a morphism
of `C/X` to its image under `j`, is the Yoneda image of the unit of
`CategoryTheory.Over.mapPullbackAdj`. In particular it is relatively representable. -/
theorem restrictYonedaUnit_eq (V : Over X) :
    (restrictYonedaEquiv g V (yoneda.obj ((Over.map g).obj V))).symm
        (𝟙 (yoneda.obj ((Over.map g).obj V))) =
      yoneda.map ((Over.mapPullbackAdj g).unit.app V) ≫
        (restrictYonedaIso g ((Over.map g).obj V)).hom := by
  ext T k
  show ((restrictYonedaEquiv g V (yoneda.obj ((Over.map g).obj V))).symm
      (𝟙 (yoneda.obj ((Over.map g).obj V)))).app T k =
    (restrictYonedaIso g ((Over.map g).obj V)).hom.app T
      (k ≫ (Over.mapPullbackAdj g).unit.app V)
  rw [restrictYonedaEquiv_symm_app_apply]
  show (Over.map g).map k =
    ((Over.mapPullbackAdj g).homEquiv (unop T) ((Over.map g).obj V)).symm
      (k ≫ (Over.mapPullbackAdj g).unit.app V)
  rw [(Over.mapPullbackAdj g).homEquiv_naturality_left_symm]
  rw [show ((Over.mapPullbackAdj g).homEquiv V ((Over.map g).obj V)).symm
      ((Over.mapPullbackAdj g).unit.app V) = 𝟙 ((Over.map g).obj V) from
    (Equiv.symm_apply_eq _).2 (by
      rw [(Over.mapPullbackAdj g).homEquiv_unit, Functor.map_id]
      exact (Category.comp_id _).symm)]
  rw [Category.comp_id]

/-- **Naturality of `CategoryTheory.OverShriek.restrictYonedaIso` in its object argument.** The
comparison isomorphism identifying the restriction of a representable presheaf transports a
morphism `k` of `C/Y` on the representing side to the restriction of its Yoneda image. -/
theorem restrictYonedaIso_naturality {X' Y' : Over Y} (k : X' ⟶ Y') :
    yoneda.map ((Over.pullback g).map k) ≫ (restrictYonedaIso g Y').hom =
      (restrictYonedaIso g X').hom ≫ (relocalizeRestrict g).map (yoneda.map k) := by
  ext T t
  show ((Over.mapPullbackAdj g).homEquiv (unop T) Y').symm (t ≫ (Over.pullback g).map k) =
    ((Over.mapPullbackAdj g).homEquiv (unop T) X').symm t ≫ k
  exact (Over.mapPullbackAdj g).homEquiv_naturality_right_symm t k

/-- The lift exhibiting `CategoryTheory.Over.pullback`'s action on a morphism `k : g₁ ⟶ g₂` of
`Over Y` as a base change of `k.left` along `g`, stated on underlying objects of `C` before
packaging it as a morphism of `Over X`. -/
private theorem isPullback_pullbackMap
    {Z₁ Z₂ : C} (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y) (k : Z₁ ⟶ Z₂) (hk : k ≫ g₂ = g₁) :
    IsPullback (pullback.lift (pullback.fst g₁ g ≫ k) (pullback.snd g₁ g)
        (by rw [Category.assoc, hk, pullback.condition]))
      (pullback.fst g₁ g) (pullback.fst g₂ g) k := by
  set m := pullback.lift (pullback.fst g₁ g ≫ k) (pullback.snd g₁ g)
        (by rw [Category.assoc, hk, pullback.condition])
  have e : m ≫ pullback.fst g₂ g = pullback.fst g₁ g ≫ k := pullback.lift_fst _ _ _
  have lhs : IsPullback (m ≫ pullback.snd g₂ g) (pullback.fst g₁ g) g (k ≫ g₂) := by
    rw [pullback.lift_snd, hk]
    exact (IsPullback.of_hasPullback g₁ g).flip
  exact (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback g₂ g).flip e).mp lhs

/-- **`CategoryTheory.Over.pullback`'s action on morphisms is a base change on underlying
objects.** For `k : g₁ ⟶ g₂` in `Over Y`, the underlying morphism of `(Over.pullback g).map k`
realises `k.left` as a base change of itself along `g`, against the two structure morphisms. -/
theorem isPullback_pullback_map {g₁ g₂ : Over Y} (k : g₁ ⟶ g₂) :
    IsPullback ((Over.pullback g).map k).left (pullback.fst g₁.hom g)
      (pullback.fst g₂.hom g) k.left := by
  have hk : k.left ≫ g₂.hom = g₁.hom := Over.w k
  simpa [Over.pullback_map_left] using isPullback_pullbackMap g g₁.hom g₂.hom k.left hk

end Representable

/-- Every section of a restricted presheaf factors through the restriction of a representable:
`t` is the tautological morphism `h_V ⟶ (h_{j V})|_X` followed by the restriction of the morphism
of presheaves on `C/Y` that `t` corresponds to. -/
theorem eq_restrictYonedaUnit_comp {V : Over X} {G : (Over Y)ᵒᵖ ⥤ Type v}
    (t : yoneda.obj V ⟶ (relocalizeRestrict g).obj G) :
    t = (restrictYonedaEquiv g V (yoneda.obj ((Over.map g).obj V))).symm
        (𝟙 (yoneda.obj ((Over.map g).obj V))) ≫
      (relocalizeRestrict g).map (restrictYonedaEquiv g V G t) := by
  ext T k
  show t.app T k =
    ((relocalizeRestrict g).map (restrictYonedaEquiv g V G t)).app T
      (((restrictYonedaEquiv g V (yoneda.obj ((Over.map g).obj V))).symm
        (𝟙 (yoneda.obj ((Over.map g).obj V)))).app T k)
  rw [restrictYonedaEquiv_symm_app_apply]
  exact restrictYonedaEquiv_app_apply g t (unop T) k

end CategoryTheory.OverShriek

namespace AlgebraicGeometry

universe w

variable (B : BigFppfSite.{w}) (S S' : Scheme.{w}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- Restriction along `CategoryTheory.Over.map g` carries sheaves on the big fppf site of `S'` to
sheaves on the big fppf site of `S`: the localization functor is continuous. -/
theorem isSheaf_relocalizeRestrict (F' : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type w)
    (hF' : Presheaf.IsSheaf (BigFppfOver.topology B S' hS') F') :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((OverShriek.relocalizeRestrict g).obj F') :=
  (((Over.map g).sheafPushforwardContinuous (Type w)
    (BigFppfOver.topology B S hS) (BigFppfOver.topology B S' hS')).obj ⟨F', hF'⟩).property

/-- Reindexing a scheme over `S'` equipped with a morphism to `j V` into a scheme over `S` does
not change the underlying morphism of schemes, so every property of morphisms of schemes is
inherited. -/
theorem inverseImage_restrictReindexSnd (Q : MorphismProperty Scheme.{w})
    {V : BigFppfOver B S hS} {b : BigFppfOver B S' hS'} (s : b ⟶ (Over.map g).obj V)
    (hs : MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S' hS') s) :
    MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)
      (OverShriek.restrictReindexSnd g s) := hs

/-- Étaleness of morphisms of schemes is invariant under pre- and post-composition with
isomorphisms. -/
private theorem etale_scheme_respectsIso : MorphismProperty.RespectsIso (@Etale.{w}) :=
  MorphismProperty.RespectsIso.mk _ (fun e f hf => by
    let _ : Etale e.hom := inferInstance
    let _ : Etale f := hf
    infer_instance) (fun e f hf => by
    let _ : Etale e.hom := inferInstance
    let _ : Etale f := hf
    infer_instance)

/-- **Stacks 03I5, part (1), algebraicity.** The restriction of an algebraic space over `S'` along
a morphism `g : S ⟶ S'` of a big fppf site is an algebraic space over `S`. -/
@[stacks 03I5 "part (1), algebraicity"]
theorem isAlgebraicSpace_relocalizeRestrict
    (F' : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type w) (hF' : IsAlgebraicSpace B S' hS' F') :
    IsAlgebraicSpace B S hS ((OverShriek.relocalizeRestrict g).obj F') := by
  have _ : HasPullbacks B.Schemes := inferInstance
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : HasPullbacks (BigFppfOver B S' hS') := inferInstance
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : HasBinaryProducts (BigFppfOver B S' hS') :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : (MorphismProperty.inverseImage (@Surjective.{w})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@Etale.{w})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    have := etale_scheme_respectsIso.{w}
    MorphismProperty.RespectsIso.inverseImage _ _
  refine ⟨isSheaf_relocalizeRestrict B S S' hS hS' g F' hF'.isSheaf, ?_, ?_⟩
  · apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro V e
    rw [OverShriek.eq_restrictYonedaUnit_comp g e, OverShriek.restrictYonedaUnit_eq]
    refine MorphismProperty.comp_mem _ _ _ ?_
      (OverShriek.relativelyRepresentable_relocalizeRestrict_map g
        (Functor.relativelyRepresentable.of_diag hF'.diagonal_representable _))
    exact MorphismProperty.RespectsIso.postcomp _ _ _
      (Functor.relativelyRepresentable.map yoneda _)
  · obtain ⟨U, q, hqS, hqE⟩ := hF'.exists_atlas
    refine ⟨(Over.pullback g).obj U,
      (OverShriek.restrictYonedaIso g U).hom ≫ (OverShriek.relocalizeRestrict g).map q, ?_, ?_⟩
    · exact MorphismProperty.RespectsIso.precomp _ _ _
        (OverShriek.relative_relocalizeRestrict_map g
          (inverseImage_restrictReindexSnd B S S' hS hS' g (@Surjective.{w})) hqS)
    · exact MorphismProperty.RespectsIso.precomp _ _ _
        (OverShriek.relative_relocalizeRestrict_map g
          (inverseImage_restrictReindexSnd B S S' hS hS' g (@Etale.{w})) hqE)

add_to_stacks 03I4 "restriction_algebraic_space, algebraicity"
  isAlgebraicSpace_relocalizeRestrict

/-- **Stacks 03I4, part (6).** The restriction along `g : S ⟶ S'` of a presentation `U'/R'` of an
algebraic space `F'` over `S'` is again a presentation, of the restriction `j⁻¹F' = F'|_S`: the
presenting scheme and its relation are the base changes `U'_S = (Over.pullback g).obj U'` and
`R'_S = (Over.pullback g).obj R'` along `g`, with projections the images under `Over.pullback g`
of the original ones, and atlas the restriction of the original atlas read through
`CategoryTheory.OverShriek.restrictYonedaIso`. -/
@[stacks 03I4 "part (6): restriction of a presentation"]
noncomputable def baseChangePresentation
    {F' : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type w} {hF' : IsAlgebraicSpace B S' hS' F'}
    (P' : Space.Presentation B S' hS' F' hF') :
    Space.Presentation B S hS ((OverShriek.relocalizeRestrict g).obj F')
      (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g F' hF') := by
  have _ : HasPullbacks B.Schemes := inferInstance
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : HasPullbacks (BigFppfOver B S' hS') := inferInstance
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : HasBinaryProducts (BigFppfOver B S' hS') :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : (MorphismProperty.inverseImage (@Surjective.{w})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@Etale.{w})
      (BigFppfOver.toScheme B S hS)).RespectsIso := by
    have _ : MorphismProperty.RespectsIso (@Etale.{w}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.inverseImage _ _
  set targetC := (Over.pullback g).map P'.target with htargetC
  set sourceC := (Over.pullback g).map P'.source with hsourceC
  set toSpaceC := (OverShriek.restrictYonedaIso g P'.U).hom ≫
    (OverShriek.relocalizeRestrict g).map P'.toSpace with htoSpaceC
  have hpbC : IsPullback (yoneda.map targetC) (yoneda.map sourceC) toSpaceC toSpaceC := by
    apply (P'.isPullback.map (OverShriek.relocalizeRestrict g)).of_iso'
      (OverShriek.restrictYonedaIso g P'.R) (OverShriek.restrictYonedaIso g P'.U)
      (OverShriek.restrictYonedaIso g P'.U) (Iso.refl _)
    · exact (OverShriek.restrictYonedaIso_naturality g P'.target).symm
    · exact (OverShriek.restrictYonedaIso_naturality g P'.source).symm
    · simp [toSpaceC]
    · simp [toSpaceC]
  have hEq : IsEquivalenceRelation
      ((Over.post B.inclusion).map targetC) ((Over.post B.inclusion).map sourceC) :=
    Space.isEquivalenceRelation_of_isPullback B S hS toSpaceC targetC sourceC hpbC
  have hEs' : Etale ((Over.post B.inclusion).map P'.source).left := by
    have h := P'.isEtaleEquivalenceRelation.etale_source
    simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd] at h
    exact h
  have hEt' : Etale ((Over.post B.inclusion).map P'.target).left := by
    have h := P'.isEtaleEquivalenceRelation.etale_target
    simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst] at h
    exact h
  have hEsC : Etale ((Over.post B.inclusion).map sourceC).left := by
    have sq := (OverShriek.isPullback_pullback_map g P'.source).map B.inclusion
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hEs'
  have hEtC : Etale ((Over.post B.inclusion).map targetC).left := by
    have sq := (OverShriek.isPullback_pullback_map g P'.target).map B.inclusion
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hEt'
  refine
    { U := (Over.pullback g).obj P'.U
      R := (Over.pullback g).obj P'.R
      target := targetC
      source := sourceC
      isEtaleEquivalenceRelation := ?_
      toSpace := toSpaceC
      surjective := ?_
      etale := ?_
      isPullback := hpbC }
  · refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
    · simp only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        prod.lift_fst, prod.lift_snd]
      exact hEq
    · simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
      exact hEsC
    · simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
      exact hEtC
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.relative_relocalizeRestrict_map g
        (inverseImage_restrictReindexSnd B S S' hS hS' g (@Surjective.{w})) P'.surjective)
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.relative_relocalizeRestrict_map g
        (inverseImage_restrictReindexSnd B S S' hS hS' g (@Etale.{w})) P'.etale)

end AlgebraicGeometry

end
