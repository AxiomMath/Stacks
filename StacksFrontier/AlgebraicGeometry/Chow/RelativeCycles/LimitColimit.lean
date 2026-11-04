module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescentCore

/-!
# Relative cycles over a limit of Noetherian schemes

Let `S = lim_{i ∈ I} S_i` be the limit of a directed inverse system of Noetherian schemes with
affine transition morphisms, let `0 ∈ I` and let `X_0 ⟶ S_0` be of finite type. For `i ≥ 0` put
`X_i = X_0 ×_{S_0} S_i` and `X = X_0 ×_{S_0} S`. If `S` is Noetherian too, then
`z(X/S, r) = colim_{i ≥ 0} z(X_i/S_i, r)`, the transition maps being base change of relative
`r`-cycles: this is Lemma 0H5D.

## Main definitions

* `Stacks.Chow.limitMap` — the map `z(X_a/S_a, r) ⟶ z(X/S, r)` for a stage `a ≥ i₀`, base change
  along `S ⟶ S_a`.
* `Stacks.Chow.transitionMap` — the transition map `z(X_a/S_a, r) ⟶ z(X_b/S_b, r)` for `b ≥ a`,
  base change along `S_b ⟶ S_a`.
* `Stacks.Chow.relativeCyclesDiagram`, `Stacks.Chow.relativeCyclesCocone` — the system of the
  groups `z(X_a/S_a, r)` and its cocone with vertex `z(X/S, r)`.

## Main results

* `Stacks.Chow.nonempty_isColimit_relativeCyclesCocone` — **Stacks Project, Lemma 0H5D.**

## Implementation notes

The inverse system is a cofiltered diagram `D : I ⥤ Scheme` with affine transition morphisms and
a limiting cone `c`; the stages `i ≥ i₀` are the objects `a` of `Over i₀`, and `X_a` is the
fibre product `X₀ ×_{S_{i₀}} S_a` of Mathlib. The maps are base changes of families of cycles
through the cartesian squares relating `X` and `X_b` to `X_a`
(`Stacks.Chow.baseChangeFamilyOfIsPullback`), so they are honest maps between the groups of
relative cycles on `X_a/S_a`, `X_b/S_b` and `X/S`, with no choice of identification involved;
functoriality and the cocone condition are Tag 0H4P, part (1), read on squares.

The colimit is a filtered colimit of abelian groups, recognised on the underlying sets
(`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`): every element of `z(X/S, r)` comes
from a stage, and two elements of one stage with the same image already agree at a later stage.

Surjectivity is the source's argument: Lemma 0H59
(`Stacks.Chow.exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle`)
provides a completely decomposed proper `g : S' ⟶ S` with `g^*α` a cycle class, and
`Stacks.Chow.exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage` descends
`α` to a stage. Injectivity is `Stacks.Chow.exists_map_baseChangeFamily_eq_of_isLimit`, which
rests on Lemma 0H5C.

## References

* [Stacks Project, Lemma 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The vertex of a cone of schemes, read at an index, is the vertex: it inherits being
Noetherian. -/
instance isNoetherian_const_obj {I : Type*} [Category I] (X : Scheme.{u}) [IsNoetherian X]
    (i : I) : IsNoetherian (((Functor.const I).obj X).obj i) :=
  inferInstanceAs (IsNoetherian X)

section Maps

variable {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D) {i₀ : I} {X₀ : Scheme.{u}}
  (f₀ : X₀ ⟶ D.obj i₀)

/-- The square exhibiting `X = X₀ ×_{S₀} S` as the base change of `X_a = X₀ ×_{S₀} S_a` along
`S ⟶ S_a`, for a stage `a ≥ i₀`. -/
theorem isPullback_limitStage (a : Over i₀) :
    IsPullback (pullback.lift (pullback.fst _ _) (pullback.snd f₀ (c.π.app i₀) ≫ c.π.app a.left)
        (by rw [pullback.condition, Category.assoc, c.w a.hom]) :
        pullback f₀ (c.π.app i₀) ⟶ pullback f₀ (D.map a.hom))
      (pullback.snd f₀ (c.π.app i₀)) (pullback.snd f₀ (D.map a.hom)) (c.π.app a.left) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, c.w a.hom]
  exact IsPullback.of_hasPullback _ _

/-- The square exhibiting `X_b = X₀ ×_{S₀} S_b` as the base change of `X_a = X₀ ×_{S₀} S_a`
along `S_b ⟶ S_a`, for stages `m : b ⟶ a` over `i₀`. -/
theorem isPullback_transitionStage {a b : Over i₀} (m : b ⟶ a) :
    IsPullback (pullback.lift (pullback.fst _ _) (pullback.snd f₀ (D.map b.hom) ≫ D.map m.left)
        (by rw [pullback.condition, Category.assoc, ← D.map_comp, Over.w m]) :
        pullback f₀ (D.map b.hom) ⟶ pullback f₀ (D.map a.hom))
      (pullback.snd f₀ (D.map b.hom)) (pullback.snd f₀ (D.map a.hom)) (D.map m.left) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, ← D.map_comp, Over.w m]
  exact IsPullback.of_hasPullback _ _

variable [LocallyOfFiniteType f₀] (r : ℕ) [∀ i, IsNoetherian (D.obj i)] [IsNoetherian c.pt]

/-- The map `z(X_a/S_a, r) ⟶ z(X/S, r)` for a stage `a ≥ i₀`: base change of relative cycles
along the projection `S ⟶ S_a`, read on `X = X₀ ×_{S₀} S`. -/
def limitMap (a : Over i₀) :
    relativeCycles (pullback.snd f₀ (D.map a.hom)) r →+
      relativeCycles (pullback.snd f₀ (c.π.app i₀)) r :=
  ((baseChangeFamilyOfIsPullbackHom _ (isPullback_limitStage D c f₀ a) r).comp
    (relativeCycles _ r).subtype).codRestrict _
      fun α => isRelativeCycle_baseChangeFamilyOfIsPullback _ _ r α.2

/-- The transition map `z(X_a/S_a, r) ⟶ z(X_b/S_b, r)` for stages `m : b ⟶ a` over `i₀`: base
change of relative cycles along `S_b ⟶ S_a`, read on `X_b = X₀ ×_{S₀} S_b`. -/
def transitionMap {a b : Over i₀} (m : b ⟶ a) :
    relativeCycles (pullback.snd f₀ (D.map a.hom)) r →+
      relativeCycles (pullback.snd f₀ (D.map b.hom)) r :=
  ((baseChangeFamilyOfIsPullbackHom _ (isPullback_transitionStage D f₀ m) r).comp
    (relativeCycles _ r).subtype).codRestrict _
      fun α => isRelativeCycle_baseChangeFamilyOfIsPullback _ _ r α.2

/-- The underlying family of cycles of `limitMap D c f₀ r a α` is the base change of `α` along
`S ⟶ S_a`. -/
theorem limitMap_apply (a : Over i₀) (α : relativeCycles (pullback.snd f₀ (D.map a.hom)) r) :
    (limitMap D c f₀ r a α : FamilyOfCycles (pullback.snd f₀ (c.π.app i₀)) r) =
      baseChangeFamilyOfIsPullback _ (isPullback_limitStage D c f₀ a) r α :=
  rfl

/-- The underlying family of cycles of `transitionMap D f₀ r m α` is the base change of `α` along
`S_b ⟶ S_a`. -/
theorem transitionMap_apply {a b : Over i₀} (m : b ⟶ a)
    (α : relativeCycles (pullback.snd f₀ (D.map a.hom)) r) :
    (transitionMap D f₀ r m α : FamilyOfCycles (pullback.snd f₀ (D.map b.hom)) r) =
      baseChangeFamilyOfIsPullback _ (isPullback_transitionStage D f₀ m) r α :=
  rfl

/-- A relative cycle on `X_a/S_a` whose base change to `S`, read through the canonical
identification `AlgebraicGeometry.limitComparison`, is `α` is sent to `α` by the map to
`z(X/S, r)`. -/
theorem limitMap_eq_of_baseChangeFamily_eq (a : Over i₀)
    (αₐ : relativeCycles (pullback.snd f₀ (D.map a.hom)) r)
    (α : relativeCycles (pullback.snd f₀ (c.π.app i₀)) r)
    (h : baseChangeFamily (pullback.snd f₀ (D.map a.hom)) (c.π.app a.left) r αₐ = fun s =>
      fiberCycleRestrict (pullback.snd f₀ (c.π.app i₀))
        (pullback.snd (pullback.snd f₀ (D.map a.hom)) (c.π.app a.left))
        (limitComparison D c a.hom f₀) (limitComparison_snd D c a.hom f₀) s r (α.1 s)) :
    limitMap D c f₀ r a αₐ = α := by
  apply Subtype.ext
  rw [limitMap_apply]
  funext s
  simp only [baseChangeFamilyOfIsPullback]
  rw [h, fiberCycleRestrict_fiberCycleRestrict]
  refine fiberCycleRestrict_eq_self _ _ _ (pullback.hom_ext ?_ ?_) s r _
  · rw [Category.assoc, limitComparison_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      Category.id_comp]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, limitComparison_snd, IsPullback.isoPullback_hom_snd, Category.id_comp]

/-- Two successive maps `X ×_Z A₃ ⟶ X ×_Z A₂ ⟶ X ×_Z A₁` induced by `A₃ ⟶ A₂ ⟶ A₁` compose to the
map induced by the composite. -/
private theorem lift_comp_lift {X Z A₁ A₂ A₃ : Scheme.{u}} {f : X ⟶ Z} {p₁ : A₁ ⟶ Z}
    {p₂ : A₂ ⟶ Z} {p₃ : A₃ ⟶ Z} {u : A₃ ⟶ A₂} {v : A₂ ⟶ A₁} {w : A₃ ⟶ A₁} (hw : u ≫ v = w)
    {h₁ : pullback.fst f p₃ ≫ f = (pullback.snd f p₃ ≫ u) ≫ p₂}
    {h₂ : pullback.fst f p₂ ≫ f = (pullback.snd f p₂ ≫ v) ≫ p₁}
    {h₃ : pullback.fst f p₃ ≫ f = (pullback.snd f p₃ ≫ w) ≫ p₁} :
    pullback.lift (pullback.fst f p₃) (pullback.snd f p₃ ≫ u) h₁ ≫
      pullback.lift (pullback.fst f p₂) (pullback.snd f p₂ ≫ v) h₂ =
        pullback.lift (pullback.fst f p₃) (pullback.snd f p₃ ≫ w) h₃ := by
  subst hw
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
      pullback.lift_snd]

/-- The transition map of the identity is the identity. -/
theorem transitionMap_id (a : Over i₀) : transitionMap D f₀ r (𝟙 a) = AddMonoidHom.id _ := by
  ext α : 2
  rw [transitionMap_apply, AddMonoidHom.id_apply,
    baseChangeFamilyOfIsPullback_congr _ (p := pullback.snd f₀ (D.map a.hom))
      (isPullback_transitionStage D f₀ (𝟙 a)) (IsPullback.id_horiz _) ?_ (by simp) r,
    baseChangeFamilyOfIsPullback_id]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- The transition maps are functorial: base change along `S_c ⟶ S_b ⟶ S_a` is base change
along `S_c ⟶ S_b` after base change along `S_b ⟶ S_a` (Tag 0H4P, part (1)). -/
theorem transitionMap_comp {a b d : Over i₀} (m' : d ⟶ b) (m : b ⟶ a) :
    transitionMap D f₀ r (m' ≫ m) =
      (transitionMap D f₀ r m').comp (transitionMap D f₀ r m) := by
  ext α : 2
  rw [AddMonoidHom.comp_apply, transitionMap_apply, transitionMap_apply, transitionMap_apply,
    baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
  refine baseChangeFamilyOfIsPullback_congr _ _ _ ?_ (by simp) r _
  refine (lift_comp_lift ?_).symm
  simp

/-- The maps to `z(X/S, r)` are compatible with the transition maps. -/
theorem limitMap_comp_transitionMap {a b : Over i₀} (m : b ⟶ a) :
    (limitMap D c f₀ r b).comp (transitionMap D f₀ r m) = limitMap D c f₀ r a := by
  ext α : 2
  rw [AddMonoidHom.comp_apply, limitMap_apply, limitMap_apply, transitionMap_apply,
    baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
  refine baseChangeFamilyOfIsPullback_congr _ _ _ ?_ (c.w m.left) r _
  exact lift_comp_lift (c.w m.left)

/-- The inverse system `{z(X_a/S_a, r)}_{a ≥ i₀}` of groups of relative cycles, the transition
maps being base change of relative cycles. -/
def relativeCyclesDiagram : (Over i₀)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj a := AddCommGrpCat.of (relativeCycles (pullback.snd f₀ (D.map a.unop.hom)) r)
  map m := AddCommGrpCat.ofHom (transitionMap D f₀ r m.unop)
  map_id a := by
    rw [unop_id, transitionMap_id]
    rfl
  map_comp m m' := by
    rw [unop_comp, transitionMap_comp]
    rfl

/-- The cocone on the system of the groups `z(X_a/S_a, r)` with vertex `z(X/S, r)`, given by base
change along the projections `S ⟶ S_a`. -/
def relativeCyclesCocone : Cocone (relativeCyclesDiagram D f₀ r) where
  pt := AddCommGrpCat.of (relativeCycles (pullback.snd f₀ (c.π.app i₀)) r)
  ι :=
    { app a := AddCommGrpCat.ofHom (limitMap D c f₀ r a.unop)
      naturality a b m := by
        change AddCommGrpCat.ofHom (transitionMap D f₀ r m.unop) ≫
          AddCommGrpCat.ofHom (limitMap D c f₀ r b.unop) =
            AddCommGrpCat.ofHom (limitMap D c f₀ r a.unop) ≫ 𝟙 _
        rw [Category.comp_id, ← limitMap_comp_transitionMap D c f₀ r m.unop]
        rfl }

end Maps

/-- **Stacks Project, Lemma 0H5D.** Let `S = lim_{i ∈ I} S_i` be the limit of a cofiltered system
of Noetherian schemes with affine transition morphisms, let `i₀ ∈ I` and let `X₀ ⟶ S_{i₀}` be of
finite type; for a stage `a ≥ i₀` put `X_a = X₀ ×_{S_{i₀}} S_a`, and put `X = X₀ ×_{S_{i₀}} S`. If
`S` is Noetherian, then `z(X/S, r) = colim_{a ≥ i₀} z(X_a/S_a, r)`, the transition maps being
base change of relative `r`-cycles: the cocone `Stacks.Chow.relativeCyclesCocone` of base changes
along the projections `S ⟶ S_a` is a colimit in the category of abelian groups. -/
@[stacks 0H5D]
theorem nonempty_isColimit_relativeCyclesCocone {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, IsNoetherian (D.obj i)] (c : Cone D) (hc : IsLimit c) [IsNoetherian c.pt] {i₀ : I}
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ D.obj i₀) [LocallyOfFiniteType f₀] [QuasiCompact f₀] (r : ℕ) :
    Nonempty (IsColimit (relativeCyclesCocone D c f₀ r)) := by
  have : ReflectsColimit (relativeCyclesDiagram D f₀ r) (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (forget AddCommGrpCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)⟩
  · -- Surjectivity: Lemma 0H59 and the descent along the cover.
    intro x
    let α : relativeCycles (pullback.snd f₀ (c.π.app i₀)) r := x
    obtain ⟨S', g, hgp, hPB, hcd⟩ :=
      exists_isProper_isCompletelyDecomposed_pullbackInCycleClassImage_of_isRelativeCycle
        (pullback.snd f₀ (c.π.app i₀)) r α.2
    have := hgp
    obtain ⟨i, u, αᵢ, hαᵢ, hbase⟩ :=
      exists_relativeCycles_baseChangeFamily_eq_of_pullbackInCycleClassImage D c hc f₀ r α.1 g
        hcd hPB
    refine ⟨Opposite.op (Over.mk u), (⟨αᵢ, hαᵢ⟩ : relativeCycles (pullback.snd f₀ (D.map u)) r), ?_⟩
    exact (limitMap_eq_of_baseChangeFamily_eq D c f₀ r (Over.mk u) ⟨αᵢ, hαᵢ⟩ α hbase).symm
  · -- Injectivity: Lemma 0H5C and the limit lemma 01ZM.
    intro a x y h
    let α : relativeCycles (pullback.snd f₀ (D.map a.unop.hom)) r := x
    let β : relativeCycles (pullback.snd f₀ (D.map a.unop.hom)) r := y
    have h' : limitMap D c f₀ r a.unop α = limitMap D c f₀ r a.unop β := h
    have h'' := congrArg Subtype.val h'
    rw [limitMap_apply, limitMap_apply, baseChangeFamilyOfIsPullback_eq_iff,
      ← baseChangeFamily_eq_iff] at h''
    obtain ⟨j, v, hv⟩ :=
      exists_map_baseChangeFamily_eq_of_isLimit D c hc (pullback.snd f₀ (D.map a.unop.hom)) r α β
        h''
    refine ⟨Opposite.op (Over.mk (v ≫ a.unop.hom)), (Over.homMk v rfl : Over.mk (v ≫ a.unop.hom) ⟶
      a.unop).op, ?_⟩
    change transitionMap D f₀ r (Over.homMk v rfl : Over.mk (v ≫ a.unop.hom) ⟶ a.unop) α =
      transitionMap D f₀ r (Over.homMk v rfl : Over.mk (v ≫ a.unop.hom) ⟶ a.unop) β
    exact Subtype.ext ((baseChangeFamilyOfIsPullback_eq_iff ..).mpr
      ((baseChangeFamily_eq_iff _ _ r _ _).mp hv))

end Stacks.Chow

end
