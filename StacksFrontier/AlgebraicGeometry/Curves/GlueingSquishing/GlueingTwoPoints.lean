module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Glueing two rational points

Let `X'` and `X` be algebraic schemes over an algebraically closed field. This file says what
it means for a morphism `X' ⟶ X` to identify precisely two distinct rational points, with the
prescribed additive conductor quotient.

## Main definitions

* `AlgebraicGeometry.sectionAt` evaluates a section of the structure sheaf at a rational point.
* `AlgebraicGeometry.constHom` gives the constant sections over an open of a scheme over `k`.
* `AlgebraicGeometry.IsGlueingTwoPoints` is the predicate that `X` is obtained from `X'` by
  glueing the two given rational points.

## Implementation notes

The short exact sequence of sheaves is written in its equivalent germ-local form. Sections of
the pushforward over `U` are sections on `f ⁻¹ᵁ U`; its map to the skyscraper at the glued
point is explicitly evaluation at `a` minus evaluation at `b`. The three final clauses are
respectively injectivity, exactness in the middle, and surjectivity on the stalk at the glued
point. Away from that point exactness follows from the asserted restricted isomorphism.

An algebraic `k`-scheme is represented by an `Over (Spec k)` structure whose structure
morphism is quasi-compact and locally of finite type. The conditions `a.IsOver (Spec k)` and
`b.IsOver (Spec k)` say that the two scheme points are `k`-rational points, rather than
arbitrary morphisms from `Spec k`.

## References

* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Evaluation of a section of the structure sheaf at a rational point. -/
noncomputable def sectionAt {k : Type u} [Field k] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)) : k :=
  (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom s

/-- Evaluation of a section at a rational point, as a ring homomorphism to the residue field:
the germ at the point followed by the map out of the stalk. -/
noncomputable def sectionAtHom {k : Type u} [Field k] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U) : Γ(X, U) →+* k :=
  (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom

/-- `sectionAtHom` computes `AlgebraicGeometry.sectionAt`. -/
theorem sectionAtHom_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, U)) :
    sectionAtHom a U ha s = AlgebraicGeometry.sectionAt a U ha s := rfl

/-- Evaluation at a rational point is unchanged by restricting a section to a smaller open which
still contains the point. -/
theorem sectionAt_map {k : Type u} [Field k] {X : Scheme.{u}}
    (a : Spec (.of k) ⟶ X) {U V : X.Opens} (i : U ⟶ V)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(X, V)) :
    AlgebraicGeometry.sectionAt a U ha (X.presheaf.map i.op s) =
      AlgebraicGeometry.sectionAt a V (i.le ha) s := by
  change (Scheme.stalkClosedPointTo a).hom (X.presheaf.germ U _ ha (X.presheaf.map i.op s)) =
    (Scheme.stalkClosedPointTo a).hom (X.presheaf.germ V _ (i.le ha) s)
  rw [X.presheaf.germ_res_apply i _ ha s]

/-- The constant sections over an open of a scheme over `k`: the image of `k` under the
structure morphism, as a ring homomorphism. -/
noncomputable def constHom {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (U : X.Opens) (hU : U ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U hU).hom

/-- A morphism `Spec R ⟶ Spec R` equal to the identity acts as the identity on global
sections. -/
theorem appLE_eq_id_of_eq_id {R : CommRingCat.{u}}
    (g : Spec R ⟶ Spec R) (hg : g = 𝟙 (Spec R))
    (e : (⊤ : (Spec R).Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ e = 𝟙 Γ(Spec R, ⊤) := by
  subst hg
  exact (Scheme.Hom.appLE_eq_app (𝟙 (Spec R))).trans (Scheme.Hom.id_app ⊤)

/-- The germ at a point with values in a local ring, followed by the induced map to that ring,
written as the restriction of sections to the preimage of the open followed by the global
sections isomorphism.

Stated for an arbitrary local ring `R` rather than only for a field: with `R = DualNumber k` it
is what computes the `ε`-coefficient of `AlgebraicGeometry.epsilonCoefficientAt` at a tangent
vector, exactly as it computes `AlgebraicGeometry.sectionAt` at a rational point for `R = k`. -/
theorem germ_stalkClosedPointTo_appLE {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (a : Spec (.of R) ⟶ X) (U : X.Opens)
    (ha : a.base (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a =
      a.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem a ha).ge ≫
        (Scheme.ΓSpecIso (.of R)).hom := by
  rw [Scheme.germ_stalkClosedPointTo (f := a) U ha, Iso.trans_hom, Functor.mapIso_hom,
    Scheme.Hom.appLE, Category.assoc,
    Subsingleton.elim (homOfLE
      (Scheme.preimage_eq_top_of_closedPoint_mem a ha).ge).op (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem a ha).symm).op.hom]

/-- **The value of a constant section at a rational point is that constant.** This is where
the hypothesis that `a` is a section of the structure morphism enters. -/
theorem sectionAt_constHom {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (a : Spec (.of k) ⟶ X) (ha : a.IsOver (Spec (.of k)))
    (U : X.Opens) (hU : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hUle : U ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : k) :
    AlgebraicGeometry.sectionAt a U hU (constHom X U hUle c) = c := by
  have hid : a ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) := ha.comp_over
  have hcomp : (X ↘ Spec (.of k)).appLE ⊤ U hUle ≫
      a.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem a hU).ge =
      𝟙 Γ(Spec (.of k), ⊤) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ hid _
  change ((X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo a).hom)
    (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U hUle).hom c) = c
  rw [germ_stalkClosedPointTo_appLE a U hU]
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U hUle ≫
    a.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem a hU).ge ≫
      (Scheme.ΓSpecIso (.of k)).hom).hom) c = c
  rw [← Category.assoc ((X ↘ Spec (.of k)).appLE ⊤ U hUle), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl

/-- A morphism of algebraic `k`-schemes glues the distinct rational points `a` and `b` if
they have the same image, the morphism is finite and is an isomorphism off that image, and
the additive difference of evaluation at `a` and `b` gives the skyscraper quotient of its
pushforward structure sheaf. -/
@[stacks 0C1J "glueing_two_points"]
def IsGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X') : Prop :=
  let p : Spec (.of k) := IsLocalRing.closedPoint k
  let x : X := (a ≫ f).base p
  a.IsOver (Spec (.of k)) ∧ b.IsOver (Spec (.of k)) ∧
    a ≠ b ∧ f.IsOver (Spec (.of k)) ∧
    LocallyOfFiniteType (X' ↘ Spec (.of k)) ∧ QuasiCompact (X' ↘ Spec (.of k)) ∧
    LocallyOfFiniteType (X ↘ Spec (.of k)) ∧ QuasiCompact (X ↘ Spec (.of k)) ∧
    ∃ hab : a ≫ f = b ≫ f, IsFinite f ∧
    (∃ U : X.Opens, (U : Set X) = {x}ᶜ ∧ IsIso (f ∣_ U)) ∧
    (∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      (∃ (V : X.Opens) (hVU : V ≤ U) (hxV : x ∈ V),
        X'.presheaf.map
          (homOfLE (f.preimage_mono hVU)).op (f.app U s) = 0) →
      ∃ (V : X.Opens) (hVU : V ≤ U) (_hxV : x ∈ V),
        X.presheaf.map (homOfLE hVU).op s = 0) ∧
    (∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U)),
      sectionAt a (f ⁻¹ᵁ U) (by change f (a p) ∈ U; exact hx) s -
          sectionAt b (f ⁻¹ᵁ U) (by
            change f (b p) ∈ U
            have h := congrArg (fun g : Spec (.of k) ⟶ X ↦ g.base p) hab
            change f (a p) = f (b p) at h; rw [← h]; exact hx) s = 0 →
      ∃ (V : X.Opens) (hVU : V ≤ U) (_hxV : x ∈ V) (t : Γ(X, V)),
        X'.presheaf.map
            (homOfLE (f.preimage_mono hVU)).op s = f.app V t) ∧
    ∀ c : k, ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U)),
      sectionAt a (f ⁻¹ᵁ U) (by change f (a p) ∈ U; exact hx) s -
        sectionAt b (f ⁻¹ᵁ U) (by
          change f (b p) ∈ U
          have h := congrArg (fun g : Spec (.of k) ⟶ X ↦ g.base p) hab
          change f (a p) = f (b p) at h; rw [← h]; exact hx) s = c

end AlgebraicGeometry
