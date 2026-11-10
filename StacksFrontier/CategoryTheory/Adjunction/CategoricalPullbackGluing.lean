module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Gluing a category from a closed part and a modification

Let `𝒳`, `𝒳'`, `𝒵`, `ℰ` be categories, with adjunctions `Lf ⊣ Rf : 𝒳 ⇄ 𝒳'`, `Li ⊣ Ri : 𝒳 ⇄ 𝒵`
and `Lj ⊣ Rj : 𝒳' ⇄ ℰ`, a functor `Lg : 𝒵 ⥤ ℰ`, and a natural isomorphism
`c : Lf ⋙ Lj ≅ Li ⋙ Lg`. This is the shape of the inverse-image functors of sheaves around a
commutative square of spaces
```
E --j--> X'
|g       |f
v        v
Z --i--> X
```
and the canonical functor `𝒳 ⥤ 𝒳' ×_ℰ 𝒵` into the two-fibre product
(`CategoryTheory.Limits.CategoricalPullback Lj Lg`) sends `F` to `(Lf F, Li F, c_F)`.

This file constructs a right adjoint of that functor whenever `𝒳` has pullbacks: it sends a
triple `(F', G, α : Lj F' ≅ Lg G)` to the fibre product
`Rf F' ×_{Rf Rj Lg G} Ri G`, the two maps being the adjuncts of `Lj ε_{F'} ≫ α` and of
`c ≫ Lg ε_G` along the composite adjunction `Lf ⋙ Lj ⊣ Rj ⋙ Rf`. It then proves that the functor
is an **equivalence** under hypotheses modelled on a proper morphism `f` which is an isomorphism
over the complement `U` of a closed immersion `i`:

* `Li` and the restriction `Lu : 𝒳 ⥤ 𝒰` to the complement jointly reflect isomorphisms, and so
  do `Lj` and the restriction `Lu' : 𝒳' ⥤ 𝒰'` to the complement of `E`;
* the counits of `Li ⊣ Ri` and `Lj ⊣ Rj` are invertible (direct image along a closed immersion
  is fully faithful), and `Lu` kills the essential images of `Ri`, `Lu'` those of `Rj`;
* `Li` and `Lu` preserve pullbacks;
* the restriction `fU : U' ⟶ U` of `f` gives an adjoint equivalence `LfU ⊣ RfU`, with an
  isomorphism `d : Lf ⋙ Lu' ≅ Lu ⋙ LfU`;
* some natural isomorphism `Rf ⋙ Li ≅ Lj ⋙ Rg` exists (proper base change over `Z`), and the mate
  `Rf ⋙ Lu ⟶ Lu' ⋙ RfU` of `d⁻¹` is invertible (base change over `U`).

This is the formal content of [Stacks, Tag 0GF4].

## Main definitions

* `Stacks.CategoryTheory.modificationGluingFunctor` — the functor `𝒳 ⥤ 𝒳' ×_ℰ 𝒵`.
* `Stacks.CategoryTheory.modificationGluingAdjunction` — its right adjoint, as an adjunction.

## Main results

* `Stacks.CategoryTheory.isIso_modificationGluingAdjunction_counit` — the counit is invertible.
* `Stacks.CategoryTheory.isIso_modificationGluingAdjunction_unit` — the unit is invertible.
* `Stacks.CategoryTheory.modificationGluingFunctor_isEquivalence` — the functor is an equivalence.

## References

* [Stacks Project, Tag 0GF4](https://stacks.math.columbia.edu/tag/0GF4)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

namespace Stacks.CategoryTheory

section Construction

variable {𝒳 : Type*} {𝒳' : Type*} {𝒵 : Type*} {ℰ : Type*}
  [Category* 𝒳] [Category* 𝒳'] [Category* 𝒵] [Category* ℰ]
  {Lf : 𝒳 ⥤ 𝒳'} {Rf : 𝒳' ⥤ 𝒳} (adjf : Lf ⊣ Rf)
  {Li : 𝒳 ⥤ 𝒵} {Ri : 𝒵 ⥤ 𝒳} (adji : Li ⊣ Ri)
  {Lj : 𝒳' ⥤ ℰ} {Rj : ℰ ⥤ 𝒳'} (adjj : Lj ⊣ Rj)
  {Lg : 𝒵 ⥤ ℰ} (c : Lf ⋙ Lj ≅ Li ⋙ Lg)

/-- The canonical functor `𝒳 ⥤ 𝒳' ×_ℰ 𝒵` into the two-fibre product, sending `F` to the triple
`(Lf F, Li F, c_F)`. -/
def modificationGluingFunctor : 𝒳 ⥤ Lj ⊡ Lg :=
  (CatCommSqOver.toFunctorToCategoricalPullback Lj Lg 𝒳).obj
    { fst := Lf
      snd := Li
      iso := c }

/-- The first entry of the triple attached to `F` is `Lf F`. -/
@[simp]
lemma modificationGluingFunctor_obj_fst (F : 𝒳) :
    ((modificationGluingFunctor c).obj F).fst = Lf.obj F := rfl

/-- The second entry of the triple attached to `F` is `Li F`. -/
@[simp]
lemma modificationGluingFunctor_obj_snd (F : 𝒳) :
    ((modificationGluingFunctor c).obj F).snd = Li.obj F := rfl

/-- The structure isomorphism of the triple attached to `F` is `c_F`. -/
@[simp]
lemma modificationGluingFunctor_obj_iso (F : 𝒳) :
    ((modificationGluingFunctor c).obj F).iso = c.app F := rfl

/-- The first component of the image of `φ` is `Lf φ`. -/
@[simp]
lemma modificationGluingFunctor_map_fst {F F' : 𝒳} (φ : F ⟶ F') :
    ((modificationGluingFunctor c).map φ).fst = Lf.map φ := rfl

/-- The second component of the image of `φ` is `Li φ`. -/
@[simp]
lemma modificationGluingFunctor_map_snd {F F' : 𝒳} (φ : F ⟶ F') :
    ((modificationGluingFunctor c).map φ).snd = Li.map φ := rfl

/-- The first leg `Rf F' ⟶ Rf Rj Lg G` of the fibre product computing the right adjoint at a
triple `(F', G, α)`: `Rf` of the unit of `Lj ⊣ Rj` followed by `α`. -/
def modificationGluingLeft (T : Lj ⊡ Lg) : Rf.obj T.fst ⟶ Rf.obj (Rj.obj (Lg.obj T.snd)) :=
  Rf.map (adjj.unit.app T.fst ≫ Rj.map T.iso.hom)

/-- The second leg `Ri G ⟶ Rf Rj Lg G` of the fibre product computing the right adjoint at a
triple `(F', G, α)`: the adjunct, along `Lf ⋙ Lj ⊣ Rj ⋙ Rf`, of `c` followed by `Lg` of the counit
of `Li ⊣ Ri`. -/
def modificationGluingRight (T : Lj ⊡ Lg) : Ri.obj T.snd ⟶ Rf.obj (Rj.obj (Lg.obj T.snd)) :=
  (adjf.comp adjj).homEquiv _ _ (c.hom.app (Ri.obj T.snd) ≫ Lg.map (adji.counit.app T.snd))

/-- **The compatibility condition of a pair of maps into the two legs is the compatibility
condition of a morphism of triples.** For `p : F ⟶ Rf F'` and `q : F ⟶ Ri G`, the two composites
into `Rf Rj Lg G` agree exactly when the adjuncts `Lf F ⟶ F'` and `Li F ⟶ G` define a morphism
`(Lf F, Li F, c_F) ⟶ (F', G, α)` of the two-fibre product. -/
theorem modificationGluing_condition_iff (T : Lj ⊡ Lg) {F : 𝒳} (p : F ⟶ Rf.obj T.fst)
    (q : F ⟶ Ri.obj T.snd) :
    p ≫ modificationGluingLeft adjj T = q ≫ modificationGluingRight adjf adji adjj c T ↔
      Lj.map ((adjf.homEquiv _ _).symm p) ≫ T.iso.hom =
        c.hom.app F ≫ Lg.map ((adji.homEquiv _ _).symm q) := by
  rw [← ((adjf.comp adjj).homEquiv _ _).symm.injective.eq_iff]
  have h1 : ((adjf.comp adjj).homEquiv _ _).symm (p ≫ modificationGluingLeft adjj T) =
      Lj.map ((adjf.homEquiv _ _).symm p) ≫ T.iso.hom := by
    simp [modificationGluingLeft, Adjunction.comp_homEquiv, Adjunction.homEquiv_counit]
  have h2 : ((adjf.comp adjj).homEquiv _ _).symm (q ≫ modificationGluingRight adjf adji adjj c T) =
      c.hom.app F ≫ Lg.map ((adji.homEquiv _ _).symm q) := by
    rw [modificationGluingRight, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
      Adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc, c.hom.naturality q]
    simp
  rw [h1, h2]

/-- For `p : Lf F ⟶ F'` and `q : Li F ⟶ G`, the adjuncts of `p` and `q` satisfy the compatibility
condition of the two legs exactly when `(p, q)` satisfies that of a morphism of triples
`(Lf F, Li F, c_F) ⟶ (F', G, α)`. -/
theorem modificationGluing_condition_iff' (T : Lj ⊡ Lg) {F : 𝒳} (p : Lf.obj F ⟶ T.fst)
    (q : Li.obj F ⟶ T.snd) :
    adjf.homEquiv _ _ p ≫ modificationGluingLeft adjj T =
        adji.homEquiv _ _ q ≫ modificationGluingRight adjf adji adjj c T ↔
      Lj.map p ≫ T.iso.hom = c.hom.app F ≫ Lg.map q := by
  rw [modificationGluing_condition_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable [Limits.HasPullbacks 𝒳]

/-- The value of the right adjoint at a triple `(F', G, α)`: the fibre product
`Rf F' ×_{Rf Rj Lg G} Ri G`. -/
abbrev modificationGluingRightObj (T : Lj ⊡ Lg) : 𝒳 :=
  pullback (modificationGluingLeft adjj T) (modificationGluingRight adjf adji adjj c T)

/-- The hom-set bijection `(Lf F, Li F, c_F) ⟶ T ≃ F ⟶ modificationGluingRightObj T` defining the
right adjoint. -/
def modificationGluingHomEquiv (F : 𝒳) (T : Lj ⊡ Lg) :
    ((modificationGluingFunctor c).obj F ⟶ T) ≃
      (F ⟶ modificationGluingRightObj adjf adji adjj c T) where
  toFun φ := pullback.lift ((adjf.homEquiv _ _) φ.fst) ((adji.homEquiv _ _) φ.snd) (by
    exact (modificationGluing_condition_iff' adjf adji adjj c T φ.fst φ.snd).2 φ.w)
  invFun ψ :=
    { fst := (adjf.homEquiv _ _).symm (ψ ≫ pullback.fst _ _)
      snd := (adji.homEquiv _ _).symm (ψ ≫ pullback.snd _ _)
      w := by
        have := (modificationGluing_condition_iff adjf adji adjj c T (ψ ≫ pullback.fst _ _)
          (ψ ≫ pullback.snd _ _)).1 (by simp [pullback.condition])
        simpa using this }
  left_inv φ := by
    ext
    · exact (congrArg (adjf.homEquiv _ _).symm (pullback.lift_fst _ _ _)).trans
        (Equiv.symm_apply_apply _ _)
    · exact (congrArg (adji.homEquiv _ _).symm (pullback.lift_snd _ _ _)).trans
        (Equiv.symm_apply_apply _ _)
  right_inv ψ := pullback.hom_ext ((pullback.lift_fst _ _ _).trans (Equiv.apply_symm_apply _ _))
    ((pullback.lift_snd _ _ _).trans (Equiv.apply_symm_apply _ _))

/-- The bijection `modificationGluingHomEquiv` is natural in the object of `𝒳`: it sends
`(modificationGluingFunctor c).map f ≫ g` to `f` followed by the image of `g`. -/
lemma modificationGluingHomEquiv_naturality (F' F : 𝒳) (T : Lj ⊡ Lg) (f : F' ⟶ F)
    (g : (modificationGluingFunctor c).obj F ⟶ T) :
    modificationGluingHomEquiv adjf adji adjj c F' T ((modificationGluingFunctor c).map f ≫ g) =
      f ≫ modificationGluingHomEquiv adjf adji adjj c F T g := by
  apply pullback.hom_ext
  · change pullback.lift _ _ _ ≫ _ = (f ≫ pullback.lift _ _ _) ≫ _
    rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    exact adjf.homEquiv_naturality_left f g.fst
  · change pullback.lift _ _ _ ≫ _ = (f ≫ pullback.lift _ _ _) ≫ _
    rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    exact adji.homEquiv_naturality_left f g.snd

/-- **The right adjoint of the gluing functor**, sending `(F', G, α)` to
`Rf F' ×_{Rf Rj Lg G} Ri G`. -/
def modificationGluingAdjunction :
    modificationGluingFunctor c ⊣
      Adjunction.rightAdjointOfEquiv (modificationGluingHomEquiv adjf adji adjj c)
        (modificationGluingHomEquiv_naturality adjf adji adjj c) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The hom-set bijection of `modificationGluingAdjunction` is `modificationGluingHomEquiv`. -/
lemma modificationGluingAdjunction_homEquiv :
    (modificationGluingAdjunction adjf adji adjj c).homEquiv =
      modificationGluingHomEquiv adjf adji adjj c := by
  unfold modificationGluingAdjunction Adjunction.adjunctionOfEquivRight
  exact Adjunction.mkOfHomEquiv_homEquiv _

/-- The counit of `modificationGluingAdjunction` at `T` is the image of the identity under the
inverse of `modificationGluingHomEquiv`. -/
private lemma modificationGluingAdjunction_counit_app_eq (T : Lj ⊡ Lg) :
    (modificationGluingAdjunction adjf adji adjj c).counit.app T =
      (modificationGluingHomEquiv adjf adji adjj c _ T).symm (𝟙 _) := by
  rw [← Adjunction.homEquiv_symm_id, modificationGluingAdjunction_homEquiv]
  rfl

/-- The first component of the counit of `modificationGluingAdjunction` at `T` is `Lf` of the first
projection of the fibre product followed by the counit of `Lf ⊣ Rf`. -/
lemma modificationGluingAdjunction_counit_app_fst (T : Lj ⊡ Lg) :
    ((modificationGluingAdjunction adjf adji adjj c).counit.app T).fst =
      Lf.map (pullback.fst (modificationGluingLeft adjj T)
        (modificationGluingRight adjf adji adjj c T)) ≫ adjf.counit.app T.fst := by
  rw [modificationGluingAdjunction_counit_app_eq]
  simp [modificationGluingHomEquiv, Adjunction.homEquiv_counit]

/-- The second component of the counit of `modificationGluingAdjunction` at `T` is `Li` of the
second projection of the fibre product followed by the counit of `Li ⊣ Ri`. -/
lemma modificationGluingAdjunction_counit_app_snd (T : Lj ⊡ Lg) :
    ((modificationGluingAdjunction adjf adji adjj c).counit.app T).snd =
      Li.map (pullback.snd (modificationGluingLeft adjj T)
        (modificationGluingRight adjf adji adjj c T)) ≫ adji.counit.app T.snd := by
  rw [modificationGluingAdjunction_counit_app_eq]
  simp [modificationGluingHomEquiv, Adjunction.homEquiv_counit]

end Construction

section Equivalence

variable {𝒳 : Type*} {𝒳' : Type*} {𝒵 : Type*} {ℰ : Type*} {𝒰 : Type*} {𝒰' : Type*}
  [Category* 𝒳] [Category* 𝒳'] [Category* 𝒵] [Category* ℰ] [Category* 𝒰] [Category* 𝒰']
  {Lf : 𝒳 ⥤ 𝒳'} {Rf : 𝒳' ⥤ 𝒳} (adjf : Lf ⊣ Rf)
  {Li : 𝒳 ⥤ 𝒵} {Ri : 𝒵 ⥤ 𝒳} (adji : Li ⊣ Ri)
  {Lj : 𝒳' ⥤ ℰ} {Rj : ℰ ⥤ 𝒳'} (adjj : Lj ⊣ Rj)
  {Lg : 𝒵 ⥤ ℰ} {Rg : ℰ ⥤ 𝒵} (c : Lf ⋙ Lj ≅ Li ⋙ Lg)
  {Lu : 𝒳 ⥤ 𝒰} {Lu' : 𝒳' ⥤ 𝒰'} {LfU : 𝒰 ⥤ 𝒰'} {RfU : 𝒰' ⥤ 𝒰} (adjfU : LfU ⊣ RfU)
  (d : Lf ⋙ Lu' ≅ Lu ⋙ LfU)
  [Limits.HasPullbacks 𝒳]

/-- `Lj` of the unit of `Lj ⊣ Rj` is invertible when the counit is: it is a section of the
counit. -/
private lemma isIso_map_unit_app [IsIso adjj.counit] (A : 𝒳') :
    IsIso (Lj.map (adjj.unit.app A)) := by
  have h : Lj.map (adjj.unit.app A) = inv (adjj.counit.app (Lj.obj A)) :=
    IsIso.eq_inv_of_inv_hom_id (adjj.left_triangle_components A)
  rw [h]
  infer_instance

/-- **The counit of the gluing adjunction is invertible.** -/
theorem isIso_modificationGluingAdjunction_counit
    [IsIso adji.counit] [IsIso adjj.counit] [IsIso adjfU.counit]
    [PreservesLimitsOfShape WalkingCospan Li] [PreservesLimitsOfShape WalkingCospan Lu]
    (hX' : ∀ {A B : 𝒳'} (φ : A ⟶ B), IsIso (Lj.map φ) → IsIso (Lu'.map φ) → IsIso φ)
    (hZ : ∀ G : 𝒵, Nonempty (IsTerminal (Lu.obj (Ri.obj G))))
    (hE : ∀ G : ℰ, Nonempty (IsTerminal (Lu'.obj (Rj.obj G))))
    (βZ : Rf ⋙ Li ≅ Lj ⋙ Rg)
    (hβU : IsIso (mateEquiv adjf adjfU (TwoSquare.mk Lu Lf LfU Lu' d.inv)))
    (T : Lj ⊡ Lg) :
    IsIso ((modificationGluingAdjunction adjf adji adjj c).counit.app T) := by
  have hRfU : PreservesLimitsOfSize.{0, 0} RfU := adjfU.rightAdjoint_preservesLimits
  set β := (mateEquiv adjf adjfU (TwoSquare.mk Lu Lf LfU Lu' d.inv))
  have hpb := IsPullback.of_hasPullback (modificationGluingLeft (Rf := Rf) adjj T)
    (modificationGluingRight adjf adji adjj c T)
  have hLa : IsIso (Li.map (modificationGluingLeft (Rf := Rf) adjj T)) := by
    have : IsIso (Lj.map (adjj.unit.app T.fst)) := isIso_map_unit_app adjj T.fst
    have : IsIso (Li.map (Rf.map (adjj.unit.app T.fst))) :=
      (NatIso.isIso_map_iff βZ _).2 (by
        change IsIso (Rg.map (Lj.map (adjj.unit.app T.fst)))
        infer_instance)
    rw [modificationGluingLeft, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hsnd : IsIso ((modificationGluingAdjunction adjf adji adjj c).counit.app T).snd := by
    rw [modificationGluingAdjunction_counit_app_snd]
    exact IsIso.comp_isIso' (Li.map_isPullback hpb).isIso_snd_of_isIso inferInstance
  have hLb : IsIso (Lu.map (modificationGluingRight adjf adji adjj c T)) := by
    obtain ⟨h₁⟩ := hZ T.snd
    obtain ⟨h₂⟩ := hE (Lg.obj T.snd)
    have h₃ : IsTerminal (RfU.obj (Lu'.obj (Rj.obj (Lg.obj T.snd)))) :=
      h₂.isTerminalObj RfU _
    have : IsIso (β.app (Rj.obj (Lg.obj T.snd))) := inferInstance
    exact isIso_of_isTerminal h₁
      (h₃.ofIso (asIso (β.app (Rj.obj (Lg.obj T.snd)))).symm) _
  have hLufst : IsIso (Lu.map (pullback.fst (modificationGluingLeft (Rf := Rf) adjj T)
      (modificationGluingRight adjf adji adjj c T))) :=
    (Lu.map_isPullback hpb).isIso_fst_of_isIso
  have hfst : IsIso ((modificationGluingAdjunction adjf adji adjj c).counit.app T).fst := by
    refine hX' _ ?_ ?_
    · have hw := ((modificationGluingAdjunction adjf adji adjj c).counit.app T).w
      rw [(Iso.eq_comp_inv T.iso).2 hw]
      infer_instance
    · have h1 : IsIso (Lu'.map (Lf.map
          (pullback.fst (modificationGluingLeft (Rf := Rf) adjj T)
            (modificationGluingRight adjf adji adjj c T)))) := by
        have : IsIso ((Lu ⋙ LfU).map
            (pullback.fst (modificationGluingLeft (Rf := Rf) adjj T)
              (modificationGluingRight adjf adji adjj c T))) := by
          change IsIso (LfU.map (Lu.map _))
          infer_instance
        exact (NatIso.isIso_map_iff d _).2 this
      have h2 : IsIso (Lu'.map (adjf.counit.app T.fst)) := by
        have hc := mateEquiv_counit adjf adjfU (TwoSquare.mk Lu Lf LfU Lu' d.inv) T.fst
        have : IsIso (d.inv.app (Rf.obj T.fst) ≫ Lu'.map (adjf.counit.app T.fst)) := by
          rw [← hc]
          have : IsIso (β.app T.fst) := inferInstance
          infer_instance
        exact IsIso.of_isIso_comp_left (d.inv.app (Rf.obj T.fst)) _
      have key : IsIso (Lu'.map (Lf.map (pullback.fst (modificationGluingLeft (Rf := Rf) adjj T)
          (modificationGluingRight adjf adji adjj c T)) ≫ adjf.counit.app T.fst)) := by
        rw [Functor.map_comp]
        exact IsIso.comp_isIso' h1 h2
      rw [modificationGluingAdjunction_counit_app_fst]
      exact key
  exact (CategoricalPullback.isIso_iff _ _ _).2 ⟨hfst, hsnd⟩

include adjfU d in
/-- **The unit of the gluing adjunction is invertible**, once the counit is. -/
theorem isIso_modificationGluingAdjunction_unit [IsIso adjfU.unit]
    (hX : ∀ {A B : 𝒳} (φ : A ⟶ B), IsIso (Li.map φ) → IsIso (Lu.map φ) → IsIso φ)
    (hcounit : ∀ T, IsIso ((modificationGluingAdjunction adjf adji adjj c).counit.app T)) (F : 𝒳) :
    IsIso ((modificationGluingAdjunction adjf adji adjj c).unit.app F) := by
  set adj := modificationGluingAdjunction adjf adji adjj c
  have hΦ : IsIso ((modificationGluingFunctor c).map (adj.unit.app F)) := by
    have hε := hcounit ((modificationGluingFunctor c).obj F)
    have h2 : IsIso ((modificationGluingFunctor c).map (adj.unit.app F) ≫
        adj.counit.app ((modificationGluingFunctor c).obj F)) := by
      rw [adj.left_triangle_components F]
      exact IsIso.id _
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hε h2
  obtain ⟨hf, hi⟩ : IsIso (Lf.map (adj.unit.app F)) ∧ IsIso (Li.map (adj.unit.app F)) :=
    (CategoricalPullback.isIso_iff _ _ _).1 hΦ
  refine hX _ hi ?_
  have h1 : IsIso ((Lu ⋙ LfU).map (adj.unit.app F)) :=
    (NatIso.isIso_map_iff d _).1 (by
      change IsIso (Lu'.map (Lf.map _))
      infer_instance)
  have h2 : IsIso ((LfU ⋙ RfU).map (Lu.map (adj.unit.app F))) := by
    change IsIso (RfU.map ((Lu ⋙ LfU).map _))
    infer_instance
  exact (NatIso.isIso_map_iff (asIso adjfU.unit) _).2 h2

/-- **The gluing functor `𝒳 ⥤ 𝒳' ×_ℰ 𝒵` is an equivalence of categories** under the hypotheses
listed in the module documentation. -/
theorem modificationGluingFunctor_isEquivalence
    [IsIso adji.counit] [IsIso adjj.counit] [IsIso adjfU.unit] [IsIso adjfU.counit]
    [PreservesLimitsOfShape WalkingCospan Li] [PreservesLimitsOfShape WalkingCospan Lu]
    (hX : ∀ {A B : 𝒳} (φ : A ⟶ B), IsIso (Li.map φ) → IsIso (Lu.map φ) → IsIso φ)
    (hX' : ∀ {A B : 𝒳'} (φ : A ⟶ B), IsIso (Lj.map φ) → IsIso (Lu'.map φ) → IsIso φ)
    (hZ : ∀ G : 𝒵, Nonempty (IsTerminal (Lu.obj (Ri.obj G))))
    (hE : ∀ G : ℰ, Nonempty (IsTerminal (Lu'.obj (Rj.obj G))))
    (βZ : Rf ⋙ Li ≅ Lj ⋙ Rg)
    (hβU : IsIso (mateEquiv adjf adjfU (TwoSquare.mk Lu Lf LfU Lu' d.inv))) :
    (modificationGluingFunctor c).IsEquivalence := by
  have hcounit :=
    isIso_modificationGluingAdjunction_counit adjf adji adjj c adjfU d hX' hZ hE βZ hβU
  have hunit := isIso_modificationGluingAdjunction_unit adjf adji adjj c adjfU d hX hcounit
  have := hcounit
  have := hunit
  exact (modificationGluingAdjunction adjf adji adjj c).toEquivalence.isEquivalence_functor

end Equivalence

end Stacks.CategoryTheory

end
