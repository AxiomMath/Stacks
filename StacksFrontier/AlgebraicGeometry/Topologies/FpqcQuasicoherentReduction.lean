module

public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Stacks 022H dichotomy on an over-site, and Tag 03DT

Mathlib's `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` (Stacks 022H) reduces the fpqc sheaf
condition for a presheaf on the category of *all* schemes to two statements: the Zariski sheaf
condition, and the sheaf condition for a single faithfully flat morphism of affine schemes.  The
presheaf of Tag 03DS lives on `CategoryTheory.Over S`, not on `AlgebraicGeometry.Scheme`, so that
dichotomy does not apply to it directly.

For a presheaf of types `P` on `CategoryTheory.Over X` there is a presheaf of types
`Stacks.Sites.totalPresheaf P` on the base category — the "total space" `T ↦ Σ f : T ⟶ X, P(f)` —
together with a morphism to `CategoryTheory.yoneda.obj X`, and `P` is a sheaf for the localized
topology `CategoryTheory.GrothendieckTopology.over` exactly when the total presheaf is a sheaf for
the topology itself, provided the latter is subcanonical. This gives the 022H dichotomy on the
fpqc over-site, and the reduction of Tag 03DT to two statements about one quasi-coherent module.

## Main definitions

* `Stacks.Sites.fibrePresheaf` is the presheaf on `CategoryTheory.Over X` cut out of a presheaf `G`
  on the base by a morphism `G ⟶ CategoryTheory.yoneda.obj X`: its value at `f : T ⟶ X` is the
  fibre of `G T` over `f`.
* `Stacks.Sites.totalPresheaf` is the inverse construction, `T ↦ Σ f : T ⟶ X, P(f)`, and
  `Stacks.Sites.totalProj` its projection to `CategoryTheory.yoneda.obj X`.
* `Stacks.Sites.fibrePresheafTotalIso` identifies the fibre presheaf of the total presheaf with the
  presheaf one started from.

## Main results

* `Stacks.Sites.isSheafFor_fibrePresheaf_iff`: for a sieve `R` of `T` for which
  `CategoryTheory.yoneda.obj X` satisfies the sheaf condition, `G` satisfies the sheaf condition
  for `R` if and only if the fibre presheaf satisfies it for the sieve of `CategoryTheory.Over X`
  attached to `R` at every `f : T ⟶ X`.
* `Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf`: a presheaf of types on
  `CategoryTheory.Over X` is a sheaf for the localized topology if and only if its total presheaf
  is a sheaf for the topology on the base.
* `Stacks.Sites.isSheaf_fpqcTopology_over_of_zariski_of_affine`: **the Stacks 022H dichotomy on the
  fpqc over-site.**  A presheaf of types on the schemes over `X` is an fpqc sheaf as soon as it is
  a Zariski sheaf and satisfies the sheaf condition for a single faithfully flat morphism of affine
  schemes over `X`.
* `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine`: **Tag 03DT,
  fpqc case, reduced to those two statements** for one scheme and one quasi-coherent module on it.
* `Stacks.Sites.isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine_base`: the
  same reduction with the affine half moved down to an affine base by the base change of
  `Stacks.Sites.isSheafFor_overEquiv_symm_baseChange_iff`, where it is a statement of commutative
  algebra.
* `Stacks.Sites.isSheafFor_quasiCoherentPresheaf_terminal`: an fpqc sheaf on the schemes over `S`
  satisfies the sheaf condition for the sieve of the terminal object attached to any fpqc covering
  sieve of `S`.

## Implementation notes

The total presheaf is a `Sigma` type, so computations with it involve dependent rewriting.
`Stacks.Sites.totalPresheafMap_mk` computes the map of the total presheaf with the first component
of the target supplied as a variable, and `Stacks.Sites.castP_eq` rewrites the transport of a value
of `P` along an equality of structure morphisms as `P.map` of an explicit
`CategoryTheory.Over.homMk`; together they keep every `cast` out of the functor laws.

## References

* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TypeCat

universe v u

namespace Stacks.Sites

section Fibre

variable {C : Type u} [Category.{v} C] {X : C}

/-- The presheaf on `CategoryTheory.Over X` cut out of a presheaf `G` on `C` by a morphism
`p : G ⟶ CategoryTheory.yoneda.obj X`: its value at an object `A` is the set of elements of
`G A.left` whose image under `p` is the structure morphism of `A`. -/
@[simps]
public def fibrePresheaf {G : Cᵒᵖ ⥤ Type v} (p : G ⟶ yoneda.obj X) : (Over X)ᵒᵖ ⥤ Type v where
  obj A := { s : G.obj (op A.unop.left) // p.app (op A.unop.left) s = A.unop.hom }
  map {A B} h := ↾fun s => ⟨G.map h.unop.left.op s.1, by
    rw [NatTrans.naturality_apply p, s.2]
    exact Over.w h.unop⟩
  map_id A := by
    ext s
    exact G.map_id_apply _ s.1
  map_comp f g := by
    ext s
    exact G.map_comp_apply f.unop.left.op g.unop.left.op s.1

variable {G : Cᵒᵖ ⥤ Type v} (p : G ⟶ yoneda.obj X)

/-- If `y` is the restriction of `t` along `g`, then `p y` is `g` followed by `p t`. -/
private theorem app_eq_comp_of_map_eq {T Y : C} (g : Y ⟶ T) {t : G.obj (op T)}
    {y : G.obj (op Y)} (h : G.map g.op t = y) : p.app (op Y) y = g ≫ p.app (op T) t :=
  h ▸ NatTrans.naturality_apply p g.op t

/-- The underlying element of the restriction along a morphism of `CategoryTheory.Over X` is the
restriction of the underlying element. -/
@[simp]
public lemma fibrePresheaf_map_val {A B : (Over X)ᵒᵖ} (h : A ⟶ B)
    (s : (fibrePresheaf p).obj A) :
    ((fibrePresheaf p).map h s).1 = G.map h.unop.left.op s.1 := rfl

/-- A morphism of the base lying in a sieve `R` of `T` gives a morphism of `CategoryTheory.Over X`
lying in the sieve of `CategoryTheory.Over.mk f` attached to `R`. -/
public lemma overEquiv_symm_homMk {T : C} {R : Sieve T} (f : T ⟶ X) {Y : C} (g : Y ⟶ T)
    (hg : R.arrows g) :
    ((Sieve.overEquiv (Over.mk f)).symm R).arrows
      (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) :=
  (Sieve.overEquiv_symm_iff (Y := Over.mk f) R
    (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f)).2 hg

/-- **A compatible family of elements of the fibre presheaf depends only on the underlying
morphism of the base.**  Its value at `hA : A ⟶ CategoryTheory.Over.mk f` has the same underlying
element as its value at `CategoryTheory.Over.homMk hA.left`. -/
public lemma fibre_family_val_homMk {T : C} {f : T ⟶ X} {R : Sieve T}
    {u : Presieve.FamilyOfElements (fibrePresheaf p)
      ((Sieve.overEquiv (Over.mk f)).symm R).arrows}
    (hu : u.Compatible) {A : Over X} (hA : A ⟶ Over.mk f)
    (hh : ((Sieve.overEquiv (Over.mk f)).symm R).arrows hA) :
    (u (Over.homMk hA.left rfl : Over.mk (hA.left ≫ f) ⟶ Over.mk f)
        (overEquiv_symm_homMk f hA.left ((Sieve.overEquiv_symm_iff R hA).1 hh))).1 =
      (u hA hh).1 := by
  have hk₂ : (𝟙 A.left) ≫ A.hom = hA.left ≫ f := by simpa using (Over.w hA).symm
  have hcmp := hu (𝟙 (Over.mk (hA.left ≫ f)))
    (Over.homMk (𝟙 A.left) hk₂ : Over.mk (hA.left ≫ f) ⟶ A)
    (overEquiv_symm_homMk f hA.left ((Sieve.overEquiv_symm_iff R hA).1 hh)) hh
    (Over.OverMorphism.ext (by simp))
  have h1 := congrArg Subtype.val hcmp
  simp only [fibrePresheaf_map_val, Quiver.Hom.unop_op, unop_id, Over.id_left, Over.homMk_left,
    op_id, G.map_id_apply] at h1
  exact h1.trans (G.map_id_apply _ _)

/-- **The sheaf condition for a presheaf over `CategoryTheory.yoneda.obj X` is the sheaf condition
for its fibres.**  Let `R` be a sieve of `T` for which `CategoryTheory.yoneda.obj X` satisfies the
sheaf condition.  Then `G` satisfies the sheaf condition for `R` if and only if, for every
`f : T ⟶ X`, the fibre presheaf satisfies the sheaf condition for the sieve of
`CategoryTheory.Over X` attached to `R` at `CategoryTheory.Over.mk f`. -/
public theorem isSheafFor_fibrePresheaf_iff {T : C} (R : Sieve T)
    (hR : Presieve.IsSheafFor (yoneda.obj X) R.arrows) :
    Presieve.IsSheafFor G R.arrows ↔
      ∀ f : T ⟶ X, Presieve.IsSheafFor (fibrePresheaf p)
        ((Sieve.overEquiv (Over.mk f)).symm R).arrows := by
  refine ⟨fun hG f u hu => ?_, fun h x hx => ?_⟩
  · set x : Presieve.FamilyOfElements G R.arrows := fun _ g hg =>
      (u (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) (overEquiv_symm_homMk f g hg)).1
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ a₁ a₂ h₁ h₂ he
      have hk₂ : g₂ ≫ (a₂ ≫ f) = g₁ ≫ (a₁ ≫ f) := by
        rw [← Category.assoc, ← he, Category.assoc]
      exact congrArg Subtype.val
        (hu (Over.homMk g₁ rfl : Over.mk (g₁ ≫ (a₁ ≫ f)) ⟶ Over.mk (a₁ ≫ f))
          (Over.homMk g₂ hk₂ : Over.mk (g₁ ≫ (a₁ ≫ f)) ⟶ Over.mk (a₂ ≫ f))
          (overEquiv_symm_homMk f a₁ h₁) (overEquiv_symm_homMk f a₂ h₂)
          (Over.OverMorphism.ext (by simpa using he)))
    obtain ⟨t, ht, htuniq⟩ := hG x hx
    have hp : p.app (op T) t = f := by
      refine hR.isSeparatedFor.ext fun Y g hg => ?_
      exact (app_eq_comp_of_map_eq p g (ht g hg)).symm.trans
        (u (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) (overEquiv_symm_homMk f g hg)).2
    refine ⟨⟨t, hp⟩, fun A hA hh => Subtype.ext ?_, fun t' ht' => Subtype.ext ?_⟩
    · refine (ht hA.left ((Sieve.overEquiv_symm_iff R hA).1 hh)).trans ?_
      exact fibre_family_val_homMk p hu hA hh
    · refine htuniq t'.1 ?_
      intro Y g hg
      exact congrArg Subtype.val (ht' (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f)
        (overEquiv_symm_homMk f g hg))
  · set y : Presieve.FamilyOfElements (yoneda.obj X) R.arrows := fun Y g hg =>
      p.app (op Y) (x g hg)
    have hy : y.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ a₁ a₂ h₁ h₂ he
      exact (app_eq_comp_of_map_eq p g₁ rfl).symm.trans
        (app_eq_comp_of_map_eq p g₂ (hx g₁ g₂ h₁ h₂ he).symm)
    obtain ⟨f, hf, hfuniq⟩ := hR y hy
    set u : Presieve.FamilyOfElements (fibrePresheaf p)
        ((Sieve.overEquiv (Over.mk f)).symm R).arrows := fun A hA hh =>
      ⟨x hA.left ((Sieve.overEquiv_symm_iff R hA).1 hh),
        (hf hA.left ((Sieve.overEquiv_symm_iff R hA).1 hh)).symm.trans (Over.w hA)⟩
    have hu : u.Compatible := by
      intro A₁ A₂ B k₁ k₂ a₁ a₂ h₁ h₂ he
      exact Subtype.ext (hx k₁.left k₂.left _ _ (by simpa using congrArg Over.Hom.left he))
    obtain ⟨t, ht, htuniq⟩ := h f u hu
    refine ⟨t.1, ?_, ?_⟩
    · intro Y g hg
      exact congrArg Subtype.val (ht (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f)
        (overEquiv_symm_homMk f g hg))
    · intro t' ht'
      have hp : p.app (op T) t' = f := by
        exact hfuniq _ fun Y g hg => (app_eq_comp_of_map_eq p g (ht' g hg)).symm
      exact congrArg Subtype.val
        (htuniq ⟨t', hp⟩ fun A hA hh => Subtype.ext (ht' hA.left _))

/-- **A presheaf over `CategoryTheory.yoneda.obj X` is a sheaf exactly when its fibre presheaf
is**, for a topology `J` for which `CategoryTheory.yoneda.obj X` is a sheaf; the fibre presheaf
is taken for the localized topology `J.over X`. -/
public theorem isSheaf_iff_isSheaf_fibrePresheaf (J : GrothendieckTopology C)
    (hy : Presieve.IsSheaf J (yoneda.obj X)) :
    Presieve.IsSheaf J G ↔ Presieve.IsSheaf (J.over X) (fibrePresheaf p) := by
  refine ⟨fun hG A S hS => ?_, fun h T R hR => ?_⟩
  · have hRmem : Sieve.overEquiv A S ∈ J A.left := (J.mem_over_iff S).1 hS
    have h2 : Presieve.IsSheafFor (fibrePresheaf p)
        ((Sieve.overEquiv A).symm (Sieve.overEquiv A S)).arrows :=
      (isSheafFor_fibrePresheaf_iff p _ (hy _ hRmem)).1 (hG _ hRmem) A.hom
    rwa [OrderIso.symm_apply_apply] at h2
  · refine (isSheafFor_fibrePresheaf_iff p R (hy _ hR)).2 fun f => h _ ?_
    rw [J.mem_over_iff, OrderIso.apply_symm_apply]
    exact hR

end Fibre

section Total

variable {C : Type u} [Category.{v} C] {X : C}

/-- The underlying map of `Stacks.Sites.totalPresheaf`: a pair consisting of a morphism `f` to `X`
and an element of `P` over it is sent to the composite morphism together with the restriction of
the element. -/
public def totalPresheafMap (P : (Over X)ᵒᵖ ⥤ Type v) {T U : Cᵒᵖ} (h : T ⟶ U)
    (s : Σ f : T.unop ⟶ X, P.obj (op (Over.mk f))) :
    Σ f : U.unop ⟶ X, P.obj (op (Over.mk f)) :=
  ⟨h.unop ≫ s.1, P.map (Over.homMk h.unop rfl : Over.mk (h.unop ≫ s.1) ⟶ Over.mk s.1).op s.2⟩

/-- `Stacks.Sites.totalPresheafMap` with the first component of the value supplied as a variable
`c`, equal to `h.unop ≫ g`. -/
public lemma totalPresheafMap_mk (P : (Over X)ᵒᵖ ⥤ Type v) {T U : Cᵒᵖ} (h : T ⟶ U) {g : T.unop ⟶ X}
    {c : U.unop ⟶ X} (hc : h.unop ≫ g = c) (s : P.obj (op (Over.mk g))) :
    totalPresheafMap P h ⟨g, s⟩ =
      ⟨c, P.map (Over.homMk h.unop hc : Over.mk c ⟶ Over.mk g).op s⟩ := by
  subst hc; rfl

/-- **The total presheaf of a presheaf on `CategoryTheory.Over X`.**  Its value at `T` is the set
of pairs consisting of a morphism `f : T ⟶ X` and an element of `P` at `f`. -/
@[simps]
public def totalPresheaf (P : (Over X)ᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ Type v where
  obj T := Σ f : T.unop ⟶ X, P.obj (op (Over.mk f))
  map h := ↾totalPresheafMap P h
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change totalPresheafMap P (𝟙 T) s = s
    rw [totalPresheafMap_mk P (𝟙 T) (Category.id_comp s.1) s.2]
    refine congrArg (Sigma.mk s.1) ?_
    rw [show (Over.homMk (𝟙 T).unop (Category.id_comp s.1) :
      Over.mk s.1 ⟶ Over.mk s.1) = 𝟙 _ from Over.OverMorphism.ext rfl, op_id]
    exact P.map_id_apply _ s.2
  map_comp {T _ _} f g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change totalPresheafMap P (f ≫ g) s = totalPresheafMap P g (totalPresheafMap P f s)
    rw [totalPresheafMap_mk P (f ≫ g) (Category.assoc g.unop f.unop s.1) s.2,
      totalPresheafMap_mk P f rfl s.2, totalPresheafMap_mk P g rfl _]
    refine congrArg (Sigma.mk _) ?_
    rw [← P.map_comp_apply, ← op_comp]
    exact congrArg (fun m : Over.mk (g.unop ≫ f.unop ≫ s.1) ⟶ Over.mk s.1 => P.map m.op s.2)
      (Over.OverMorphism.ext rfl)

/-- The projection of the total presheaf to `CategoryTheory.yoneda.obj X`. -/
@[simps]
public def totalProj (P : (Over X)ᵒᵖ ⥤ Type v) : totalPresheaf P ⟶ yoneda.obj X where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

/-- Transport of an element of `P` along an equality of structure morphisms. -/
public def castP (P : (Over X)ᵒᵖ ⥤ Type v) {Y : C} {c c' : Y ⟶ X} (e : c = c')
    (w : P.obj (op (Over.mk c))) : P.obj (op (Over.mk c')) :=
  cast (congrArg (fun d => P.obj (op (Over.mk d))) e) w

/-- The transport of `Stacks.Sites.castP` is the restriction along the morphism of
`CategoryTheory.Over X` given by the identity of the underlying object. -/
public lemma castP_eq (P : (Over X)ᵒᵖ ⥤ Type v) {Y : C} {c c' : Y ⟶ X} (e : c = c')
    (w : P.obj (op (Over.mk c))) :
    castP P e w =
      P.map (Over.homMk (𝟙 Y) (by simpa using e) : Over.mk c' ⟶ Over.mk c).op w := by
  subst e
  rw [show (Over.homMk (𝟙 Y) (by simp) : Over.mk c ⟶ Over.mk c) = 𝟙 _ from
    Over.OverMorphism.ext rfl, op_id]
  exact (P.map_id_apply _ w).symm

/-- Transport along `rfl` is the identity. -/
@[simp]
public lemma castP_rfl (P : (Over X)ᵒᵖ ⥤ Type v) {Y : C} {c : Y ⟶ X}
    (w : P.obj (op (Over.mk c))) : castP P rfl w = w := rfl

/-- The fibre of the total presheaf over the structure morphism of `A` is the value of `P` at
`A`. -/
public def fibreTotalEquiv (P : (Over X)ᵒᵖ ⥤ Type v) (A : Over X) :
    { s : (Σ f : A.left ⟶ X, P.obj (op (Over.mk f))) // s.1 = A.hom } ≃ P.obj (op A) where
  toFun s := castP P s.2 s.1.2
  invFun w := ⟨⟨A.hom, w⟩, rfl⟩
  left_inv := by
    intro s
    obtain ⟨⟨c, w⟩, hc⟩ := s
    cases hc
    rfl
  right_inv _ := rfl

/-- **The fibre presheaf of the total presheaf is the presheaf one started from.** -/
public def fibrePresheafTotalIso (P : (Over X)ᵒᵖ ⥤ Type v) :
    fibrePresheaf (totalProj P) ≅ P :=
  NatIso.ofComponents (fun A => (fibreTotalEquiv P A.unop).toIso) (by
    intro A B h
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    have hs : s.1.1 = A.unop.hom := s.2
    change castP P (show h.unop.left ≫ s.1.1 = B.unop.hom by
        rw [hs]; exact Over.w h.unop) (P.map (Over.homMk h.unop.left rfl :
        Over.mk (h.unop.left ≫ s.1.1) ⟶ Over.mk s.1.1).op s.1.2) =
      P.map h (castP P hs s.1.2)
    rw [castP_eq, castP_eq P hs, ← P.map_comp_apply, ← P.map_comp_apply]
    refine congrArg (fun m : op (Over.mk s.1.1) ⟶ B => P.map m s.1.2) ?_
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp)

/-- **The sheaf condition on an over-site is the sheaf condition for the total presheaf.** -/
public theorem isSheafFor_totalPresheaf_iff (P : (Over X)ᵒᵖ ⥤ Type v) {T : C} (R : Sieve T)
    (hR : Presieve.IsSheafFor (yoneda.obj X) R.arrows) :
    Presieve.IsSheafFor (totalPresheaf P) R.arrows ↔
      ∀ f : T ⟶ X, Presieve.IsSheafFor P ((Sieve.overEquiv (Over.mk f)).symm R).arrows := by
  rw [isSheafFor_fibrePresheaf_iff (totalProj P) R hR]
  exact forall_congr' fun _ => Presieve.isSheafFor_iff_of_iso (fibrePresheafTotalIso P)

/-- **A presheaf of types on `CategoryTheory.Over X` is a sheaf for the localized topology if and
only if its total presheaf is a sheaf for the topology on the base.**  The hypothesis is the sheaf
condition for `CategoryTheory.yoneda.obj X`, which holds whenever the topology is subcanonical. -/
public theorem isSheaf_over_iff_isSheaf_totalPresheaf (J : GrothendieckTopology C)
    (P : (Over X)ᵒᵖ ⥤ Type v) (hy : Presieve.IsSheaf J (yoneda.obj X)) :
    Presieve.IsSheaf (J.over X) P ↔ Presieve.IsSheaf J (totalPresheaf P) := by
  rw [isSheaf_iff_isSheaf_fibrePresheaf (totalProj P) J hy]
  exact ⟨Presieve.isSheaf_iso _ (fibrePresheafTotalIso P).symm,
    Presieve.isSheaf_iso _ (fibrePresheafTotalIso P)⟩

end Total

section Schemes

/-- **The Stacks 022H dichotomy on the fpqc over-site.**  A presheaf of types on the schemes over
`X` is an fpqc sheaf as soon as it is a Zariski sheaf and satisfies the sheaf condition for the
sieve generated by a single faithfully flat morphism of affine schemes, for every structure
morphism of the source to `X`. -/
public theorem isSheaf_fpqcTopology_over_of_zariski_of_affine (X : Scheme.{u})
    (P : (Over X)ᵒᵖ ⥤ Type u)
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over X) P)
    (haff : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ f : Spec R' ⟶ X, Presieve.IsSheafFor P
        ((Sieve.overEquiv (Over.mk f)).symm
          (Sieve.generate (Presieve.singleton (Spec.map φ)))).arrows) :
    Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over X) P := by
  have hy : Presieve.IsSheaf Scheme.fpqcTopology.{u} (yoneda.obj X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hyz : Presieve.IsSheaf Scheme.zariskiTopology.{u} (yoneda.obj X) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  -- `inferInstance` misses this instance: the coercion of `@Flat` to a `MorphismProperty` is
  -- reducible, so its discrimination-tree key differs from the generic instance's.
  have : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  refine (isSheaf_over_iff_isSheaf_totalPresheaf _ P hy).2
    ((isSheaf_type_propQCTopology_iff (P := @Flat) (totalPresheaf P)).2
      ⟨(isSheaf_over_iff_isSheaf_totalPresheaf _ P hyz).1 hzar, ?_⟩)
  intro R' S' φ hφ hsurj
  have : Surjective (Spec.map φ) := hsurj
  rw [Presieve.isSheafFor_iff_generate]
  exact (isSheafFor_totalPresheaf_iff P _
    (hy _ (Scheme.Hom.generate_singleton_mem_propQCTopology (Spec.map φ) hφ))).2 (haff φ hφ hsurj)

/-- **Tag 03DT, fpqc case, reduced to a Zariski statement and an affine statement.**  The presheaf
of Tag 03DS of a quasi-coherent module `F` on `S` is an fpqc sheaf on the schemes over `S` as soon
as it is a Zariski sheaf and satisfies the sheaf condition for a single faithfully flat morphism of
affine schemes over `S`. -/
@[sga "3 IV 6.3.1" "(ii)"]
public theorem isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat))
    (haff : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ f : Spec R' ⟶ S, Presieve.IsSheafFor
        (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk f)).symm
          (Sieve.generate (Presieve.singleton (Spec.map φ)))).arrows) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_fpqcTopology_over_of_zariski_of_affine S _ hzar haff)

/-- **Tag 03DT, fpqc case, reduced to the Zariski sheaf condition and faithfully flat descent of
sections over an affine base.**  The presheaf of Tag 03DS of a quasi-coherent module `F` on `S`
is an fpqc sheaf on the schemes over `S` as soon as it is a Zariski sheaf and, for every
quasi-coherent module on an affine scheme `Spec R'`, the presheaf of that module satisfies the
sheaf condition for the sieve generated by a single faithfully flat morphism to `Spec R'`. -/
public theorem isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine_base
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat))
    (haff : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ (F' : (Spec R').Modules) [F'.IsQuasicoherent],
        Presieve.IsSheafFor
          (quasiCoherentPresheafFunctor (Spec R') F' ⋙ CategoryTheory.forget AddCommGrpCat)
          ((Sieve.overEquiv (Over.mk (𝟙 (Spec R')) : Over (Spec R'))).symm
            (Sieve.generate (Presieve.singleton (Spec.map φ)))).arrows) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (quasiCoherentPresheafFunctor S F) := by
  refine isSheaf_fpqcTopology_over_quasiCoherentPresheaf_of_zariski_of_affine S F hzar ?_
  intro R' S' φ hφ hsurj f
  exact (isSheafFor_overEquiv_symm_baseChange_iff F (Over.mk f) (quasiCoherentPresheaf S F)
    (quasiCoherentPresheaf (Spec R') ((Scheme.Modules.pullback f).obj F)) _).1
    (haff φ hφ hsurj _)

/-- The sheaf condition of Tag 03DT at the terminal object of the schemes over `S`: if the presheaf
of Tag 03DS of `F` is an fpqc sheaf on the schemes over `S`, then it satisfies the sheaf condition
for the sieve of the terminal object attached to any fpqc covering sieve `T` of `S`. -/
public theorem isSheafFor_quasiCoherentPresheaf_terminal (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent]
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat))
    (T : Sieve S) (hT : T ∈ Scheme.fpqcTopology.{u} S) :
    Presieve.IsSheafFor (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)
      ((Sieve.overEquiv (Over.mk (𝟙 S) : Over S)).symm T).arrows :=
  h _ (by
    rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    exact hT)

end Schemes

end Stacks.Sites

end
