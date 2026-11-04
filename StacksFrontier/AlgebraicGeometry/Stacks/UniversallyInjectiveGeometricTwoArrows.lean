module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalPointOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibreSections
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePoint

/-!
# Lifting 2-arrows at geometric points (Stacks 0CPN, part (3))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Condition (3) of **Stacks 0CPN**
is that for every algebraically closed field `k`, all 1-morphisms `x₁, x₂ : Spec k ⟶ 𝒳` and
every 2-arrow `β : f ∘ x₁ ⟶ f ∘ x₂` there is a 2-arrow `α : x₁ ⟶ x₂` with `β = id_f ⋆ α`. This
file proves that condition (3) is equivalent to condition (2) — surjectivity of the relative
diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` — and hence, through the equivalence of parts (1) and (2) already
in the library, to condition (1), universal injectivity of `f`.

## Main definitions

* `AlgebraicGeometry.Stack.LiftsTwoArrowsAtGeometricPoints`: condition (3) of Stacks 0CPN.

## Main results

* `AlgebraicGeometry.Stack.exists_isAlgClosed_fieldValuedPoint`: every point of a category
  fibred in groupoids over the big fppf site is represented by a field-valued point whose field
  is algebraically closed.
* `AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints`:
  **Stacks 0CPN, part (3) implies part (2)**.
* `AlgebraicGeometry.Stack.universallyInjective_of_liftsTwoArrowsAtGeometricPoints`:
  **Stacks 0CPN, part (3) implies part (1)**.
* `AlgebraicGeometry.Stack.liftsTwoArrowsAtGeometricPoints_of_isSurjective_relativeDiagonal`:
  **Stacks 0CPN, part (2) implies part (3)**.
* `AlgebraicGeometry.Stack.universallyInjective_iff_liftsTwoArrowsAtGeometricPoints`:
  **Stacks 0CPN, parts (1) and (3)**.

## Implementation notes

A 1-morphism `Spec k ⟶ 𝒳` is recorded, as everywhere in this development and as the 2-Yoneda
lemma licenses, by an object of `𝒳` lying over a site object whose underlying scheme is
`Spec k`; a 2-arrow between two such is then an arrow of the total category lying over the
identity of that site object, and `β = id_f ⋆ α` is the equation `f(α) = β`. This is the reading
under which `AlgebraicGeometry.Stack.exists_fiber_lift_of_universallyInjective`
(**Stacks 0DTM**) consumes condition (3).

The proof follows the source. A point `t` of `|𝒳 ×_𝒴 𝒳|` is represented by a field-valued point
over an algebraically closed field: this is `exists_isAlgClosed_fieldValuedPoint`, which replaces
a representative by one over the algebraic closure of its field — an arrow of the site, which the
fibred-in-groupoids property lifts to an arrow of the total category, so the two representatives
have a common refinement. The only thing to check is that the algebraic closure is still small
enough for the site, which is the cardinality count of
`AlgebraicGeometry.Space.exists_geometricRepresentative` repeated at the level of a category
fibred in groupoids, where a field-valued point carries its base as an object of the site rather
than as a bare field.

An object of the canonical 2-fibre product over a site object `V` *is* a triple `(x₁, x₂, β)`
with `x₁`, `x₂` over `V` and `β : f(x₁) ≅ f(x₂)` vertical, by the construction
`CategoryTheory.TwoFibreProductOver`; so the source's "by our construction of 2-fibre products we
can represent `t` by `(x₁, x₂, β)`" needs no argument here. Condition (3) produces `α` with
`f(α) = β`, and `CategoryTheory.TwoFibreProductOver.homDiagonal` turns that equation into the
arrow `(𝟙, α) : Δ_f(x₁) = (x₁, x₁, id) ⟶ (x₁, x₂, β)`, which exhibits the two field-valued
points as having a common refinement. Hence `t` is in the image of `|Δ_f|`.

The converse implication (2) `⟹` (3) follows the source too. The triple `t = (x₁, x₂, β)` is
read as a 1-morphism out of the slice site of `V` by 2-Yoneda
(`CategoryTheory.StacksRepresentableCFG.exists_pointOverMap_of_obj`), and then **Stacks 04XS** —
`AlgebraicGeometry.Stack.isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack` together with
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack` — says
that the fibre `T = 𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, t} Spec k` is an algebraic space locally of finite type
over `Spec k`. Its sections over an object `a` of the slice site are exactly the vertical
morphisms between the two components of the pullback of `t` to `a` which `f` carries to the
pullback of `β`, that is the witnesses that the comparison isomorphism of that pullback descends
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.nonempty_relVertHom_iff`). Surjectivity
of `Δ_f` writes `t` as a common refinement with a diagonal object, which makes one such witness
exist over the base of the refinement
(`CategoryTheory.TwoFibreProductOver.exists_map_eq_iso_of_hom_to_diagonal` and
`…RelativeDiagonalFibre.exists_nonempty_relVertHom_of_hom`), so `T` is nonempty; and since `k` is
algebraically closed `T` then has a rational point, which is
`AlgebraicGeometry.Space.nonempty_obj_base_of_nonempty_points`, the case of a structural morphism
of Stacks 0487. A rational point is a section over the base object of the slice site, and that
section is the sought `α` once transported along the comparison of `t` with the value of the
1-morphism at that base object.

## References

* [Stacks Project, Tag 0487](https://stacks.math.columbia.edu/tag/0487)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0DTM](https://stacks.math.columbia.edu/tag/0DTM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every point is represented over an algebraically closed field.** A point of a category
fibred in groupoids over the big fppf site of `S` is the class of a field-valued point whose
field is algebraically closed, namely of a lift of any representative to the algebraic closure
of its field.

Deliberately untagged: this is not a clause of a Stacks result, but the step which lets a
statement about geometric points be read as a statement about points — the counterpart for a
category fibred in groupoids of
`AlgebraicGeometry.Space.exists_geometricRepresentative`. -/
theorem exists_isAlgClosed_fieldValuedPoint
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (y : points B S hS 𝒳 h𝒳) :
    ∃ p : FieldValuedPoint B S hS 𝒳, IsAlgClosed p.carrier ∧
      pointClass B S hS 𝒳 h𝒳 p = y := by
  classical
  obtain ⟨p₀, rfl⟩ := Quotient.exists_rep y
  let K := AlgebraicClosure p₀.carrier
  have hKsite : B.Contains (Spec (.of K)) := by
    have hb : ((BigFppfOver.toScheme B S hS).obj p₀.base).size < B.cutoff := p₀.base.left.2
    rw [Scheme.size_congr p₀.isSpec, Scheme.size_Spec] at hb
    show (Spec (.of K)).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff ((Algebra.IsAlgebraic.cardinalMk_le_max p₀.carrier K).trans_lt
      (max_lt ((le_max_right _ _).trans_lt hb) B.aleph0_lt_cutoff))
  -- The spectrum of the algebraic closure, as an object of the site over the base of `p₀`.
  let gScheme : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj p₀.base :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap p₀.carrier K)).op ≫ p₀.isSpec.inv
  let e : B.obj hKsite ⟶ p₀.base.left := B.inclusion.preimage gScheme
  let W : BigFppfOver B S hS := Over.mk (e ≫ p₀.base.hom)
  let eOver : W ⟶ p₀.base := Over.homMk e
  obtain ⟨wObj, φ, hφ⟩ := h𝒳.exists_lift eOver p₀.obj p₀.over
  exact ⟨{ carrier := K
           field := inferInstance
           base := W
           isSpec := Iso.refl _
           obj := wObj
           «over» := IsHomLift.domain_eq 𝒳.p eOver φ }, inferInstance,
    (class_eq_class_iff_hasCommonExtension B S hS 𝒳 h𝒳 _ _).2 ⟨_, ⟨𝟙 _⟩, ⟨φ⟩⟩⟩

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Condition (3) of Stacks 0CPN.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
*lifts 2-arrows at geometric points* when for every algebraically closed field `k`, all
1-morphisms `x₁, x₂ : Spec k ⟶ 𝒳` and every 2-arrow `β : f ∘ x₁ ⟶ f ∘ x₂` there is a 2-arrow
`α : x₁ ⟶ x₂` with `β = id_f ⋆ α`.

The 1-morphisms out of `Spec k` are the objects of `𝒳` over a site object with that underlying
scheme, the 2-arrows between them are the arrows lying over the identity of that site object,
and `β = id_f ⋆ α` is the equation `f(α) = β`. -/
abbrev LiftsTwoArrowsAtGeometricPoints (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
    ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
      ∀ (x₁ x₂ : 𝒳.val.val.obj), 𝒳.val.val.p.obj x₁ = V → 𝒳.val.val.p.obj x₂ = V →
        ∀ β : (CatFiberedInGroupoids.homFunctor f.hom).obj x₁ ⟶
            (CatFiberedInGroupoids.homFunctor f.hom).obj x₂,
          𝒴.val.val.p.IsHomLift (𝟙 V) β →
            ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α ∧
              (CatFiberedInGroupoids.homFunctor f.hom).map α = β

/-- **Stacks 0CPN, the implication (3) `⟹` (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` which lifts 2-arrows at geometric points has surjective relative diagonal
`Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`.

A point of `|𝒳 ×_𝒴 𝒳|` is represented over an algebraically closed field, where it is a triple
`(x₁, x₂, β)`; condition (3) writes `β` as `f(α)`, and then `(𝟙, α)` is an arrow from
`Δ_f(x₁) = (x₁, x₁, id)` to that triple, so the two represent the same point. -/
@[stacks 0CPN "part (3) implies part (2)"]
theorem isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints (f : 𝒳 ⟶ 𝒴)
    (h₃ : LiftsTwoArrowsAtGeometricPoints B S hS f) :
    IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f) := by
  classical
  intro tc
  obtain ⟨P, hPclosed, hPt⟩ := exists_isAlgClosed_fieldValuedPoint B S hS
    (AlgebraicStacks.twoFibreProduct B S hS f f).val.val
    (Classical.choose (AlgebraicStacks.twoFibreProduct B S hS f f).property) tc
  have : IsAlgClosed P.carrier := hPclosed
  -- The object of the 2-fibre product underlying `P` is a triple `(x₁, x₂, β)`.
  set Q : TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor f.hom) := P.obj
  have hbase : Q.base = P.base := P.over
  have hx₁ : 𝒳.val.val.p.obj Q.x = P.base := Q.hx.trans hbase
  have hx₂ : 𝒳.val.val.p.obj Q.y = P.base := Q.hy.trans hbase
  have hvert : 𝒴.val.val.p.IsHomLift (𝟙 P.base) Q.iso.hom := hbase ▸ Q.vertical
  obtain ⟨α, -, hα⟩ := h₃ P.carrier P.base P.isSpec Q.x Q.y hx₁ hx₂ Q.iso.hom hvert
  exact ⟨pointClass B S hS 𝒳.val.val (Classical.choose 𝒳.property)
    { carrier := P.carrier
      field := P.field
      base := P.base
      isSpec := P.isSpec
      obj := Q.x
      «over» := hx₁ },
    ((class_eq_class_iff_hasCommonExtension B S hS
      (AlgebraicStacks.twoFibreProduct B S hS f f).val.val _ _ _).2
      ⟨_, ⟨𝟙 _⟩, ⟨TwoFibreProductOver.homDiagonal
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) Q α hα⟩⟩).trans hPt⟩

/-- **Stacks 0CPN, the implication (3) `⟹` (1).** A 1-morphism of algebraic stacks over `S`
which lifts 2-arrows at geometric points is universally injective: its relative diagonal is
surjective, and parts (1) and (2) of Stacks 0CPN
(`AlgebraicGeometry.Stack.universallyInjective_iff_isSurjective_relativeDiagonal`) conclude. -/
@[stacks 0CPN "part (3) implies part (1)"]
theorem universallyInjective_of_liftsTwoArrowsAtGeometricPoints (f : 𝒳 ⟶ 𝒴)
    (h₃ : LiftsTwoArrowsAtGeometricPoints B S hS f) :
    UniversallyInjective B S hS f :=
  universallyInjective_of_isSurjective_relativeDiagonal B S hS f
    (isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints B S hS f h₃)

/-- The fibre of the relative diagonal of a 1-morphism of algebraic stacks over a point `Y` of
`𝒳 ×_𝒴 𝒳` with values in an algebraically closed field `k` has a `k`-point as soon as it has a
point: it is an algebraic space locally of finite type over `Spec k` by **Stacks 04XS**. -/
private theorem nonempty_relVertHomPresheaf_obj_base_of_nonempty_points (f : 𝒳 ⟶ 𝒴) (k : Type u)
    [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS) (e : V.left.1 ≅ Spec (.of k))
    (Y : BigFppfOver B V.left.1 V.left.2 ⥤ TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor f.hom))
    (hY : Y ⋙ TwoFibreProductOver.RelativeDiagonalFibre.RelProdP 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) = Over.map V.hom)
    (hne : Nonempty (Space.points B V.left.1 V.left.2
      (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
        𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hY f.hom.hom.w))) :
    Nonempty ((TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
      𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hY f.hom.hom.w).obj
        (Opposite.op (Over.mk (𝟙 (B.obj V.left.2))))) := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳.val 𝒴.val f.hom 𝒳.2 𝒴.2 V Y hY
  exact Space.nonempty_obj_base_of_nonempty_points B V.left.1 V.left.2 k e _
    (isAlgebraicSpace_of_iso B V.left.1 V.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eG) hG)
    (isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack B S hS 𝒳.val 𝒴.val f.hom
      𝒳.2 𝒴.2 V Y hY) hne

/-- **Stacks 0CPN, the implication (2) `⟹` (3).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` whose relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective lifts 2-arrows at geometric
points: for every algebraically closed field `k`, all `x₁, x₂ : Spec k ⟶ 𝒳` and every 2-arrow
`β : f ∘ x₁ ⟶ f ∘ x₂` there is a 2-arrow `α : x₁ ⟶ x₂` with `β = id_f ⋆ α`.

The triple `t = (x₁, x₂, β)` is a point of `𝒳 ×_𝒴 𝒳` over `Spec k`, and the fibre
`T = 𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, t} Spec k` is an algebraic space locally of finite type over `Spec k` by
**Stacks 04XS**. Surjectivity of `Δ_f` makes `T` nonempty, and since `k` is algebraically closed
`T` then has a `k`-point
(`AlgebraicGeometry.Space.nonempty_obj_base_of_nonempty_points`), which is exactly the
2-arrow `α`. -/
@[stacks 0CPN "part (2) implies part (3)"]
theorem liftsTwoArrowsAtGeometricPoints_of_isSurjective_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (h₂ : IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f)) :
    LiftsTwoArrowsAtGeometricPoints B S hS f := by
  classical
  intro k _ _ V e x₁ x₂ hx₁ hx₂ β hβ
  have hp := 𝒳.val.isFiberedInGroupoids
  have hq := 𝒴.val.isFiberedInGroupoids
  -- `β` is invertible: it is vertical and `𝒴` is fibred in groupoids.
  have _ := hβ
  have _ := hq.isStronglyCartesian_homLift (𝟙 V) β
  have _ : IsIso β := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.val.p (𝟙 V) β
  -- The triple `t = (x₁, x₂, β)`, a point of `𝒳 ×_𝒴 𝒳` over `V`.
  set Q : TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor f.hom) :=
    { base := V, x := x₁, y := x₂, hx := hx₁, hy := hx₂, iso := asIso β, vertical := hβ }
  -- Read it as a 1-morphism out of the slice site of `V`, by 2-Yoneda.
  obtain ⟨Y, hY, ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj
    (TwoFibreProductOver.RelativeDiagonalFibre.RelProdP 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom))
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hp hp hq f.hom.hom.w f.hom.hom.w) V Q rfl
  -- Surjectivity of `Δ_f` at `t`: a point of `𝒳` whose diagonal image is `t`.
  obtain ⟨cpt, hcpt⟩ := h₂ (pointClass B S hS
    (AlgebraicStacks.twoFibreProduct B S hS f f).val.val
    (Classical.choose (AlgebraicStacks.twoFibreProduct B S hS f f).property)
    { carrier := k
      base := V
      isSpec := e
      obj := Q
      «over» := rfl })
  obtain ⟨qp, rfl⟩ := Quotient.exists_rep cpt
  obtain ⟨r, ⟨u⟩, ⟨w⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).1 hcpt
  -- The comparison isomorphism of the common refinement descends, as it maps to a diagonal.
  have hu : r.obj ⟶ (TwoFibreProductOver.diagonal (𝒮 := 𝒳.val.val.obj)
      f.hom.hom.w).obj qp.obj := u
  -- So the fibre has a section over an object of the slice site with nonempty underlying scheme.
  obtain ⟨a, ha, ⟨m⟩⟩ :=
    TwoFibreProductOver.RelativeDiagonalFibre.exists_nonempty_relVertHom_of_hom
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids hY f.hom.hom.w r.obj (w ≫ ξ.inv)
      (TwoFibreProductOver.exists_map_eq_iso_of_hom_to_diagonal hp hq f.hom.hom.w hu)
  have hane : Nonempty ((BigFppfOver.toScheme B V.left.1 V.left.2).obj a) := by
    rw [show (BigFppfOver.toScheme B V.left.1 V.left.2).obj a = B.inclusion.obj a.left from rfl,
      ha, show r.obj.base = r.base from r.over]
    exact ⟨r.isSpec.inv.base (Classical.arbitrary (Spec (CommRingCat.of r.carrier)))⟩
  -- It is nonempty, so it has a `k`-point: a section over the base object of the slice site.
  obtain ⟨m₀⟩ := nonempty_relVertHomPresheaf_obj_base_of_nonempty_points B S hS f k V e Y hY
    (Space.nonempty_points_of_section B V.left.1 V.left.2 _ a hane m)
  -- Unwinding, that section is the 2-arrow.
  obtain ⟨α, hα⟩ := TwoFibreProductOver.exists_map_eq_iso_of_hom hp hq f.hom.hom.w ξ.inv
    ((TwoFibreProductOver.RelativeDiagonalFibre.nonempty_relVertHom_iff
      𝒳.val.isFiberedInGroupoids hY f.hom.hom.w (Over.mk (𝟙 V.left))).1 ⟨m₀⟩)
  exact ⟨α, TwoFibreProductOver.isHomLift_id_of_map_eq_iso f.hom.hom.w Q α hα, hα⟩

/-- **Stacks 0CPN, parts (1) and (3).** A 1-morphism of algebraic stacks over `S` is universally
injective if and only if it lifts 2-arrows at geometric points. -/
@[stacks 0CPN "parts (1) and (3)"]
theorem universallyInjective_iff_liftsTwoArrowsAtGeometricPoints (f : 𝒳 ⟶ 𝒴) :
    UniversallyInjective B S hS f ↔ LiftsTwoArrowsAtGeometricPoints B S hS f :=
  ⟨fun hf ↦ liftsTwoArrowsAtGeometricPoints_of_isSurjective_relativeDiagonal B S hS f
      ((universallyInjective_iff_isSurjective_relativeDiagonal B S hS f).1 hf),
    universallyInjective_of_liftsTwoArrowsAtGeometricPoints B S hS f⟩

end AlgebraicGeometry.Stack

end
