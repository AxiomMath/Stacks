module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski

/-!
# Pseudo-torsors under group algebraic spaces

An action of a group algebraic space `G` on an algebraic space `X` over `B` is a
*pseudo-torsor* when the shear map `(g, x) ↦ (g • x, x)` is an isomorphism, and it is
*trivial* when `X` is equivariantly isomorphic to `G` with its left regular action.  A
pseudo-torsor is recognized by its points: the action on the points over every test scheme
over `B` is either empty or simply transitive, and the pseudo-torsor is trivial exactly
when its structure morphism to `B` has a section.

## Main definitions

* `AlgebraicGeometry.Space.IsTorsorFor` is a pseudo-torsor trivialized by a family of
  morphisms to the base satisfying a prescribed covering property.
* `AlgebraicGeometry.Space.IsPrincipalHomogeneousSpace` is fpqc-local triviality.
  `AlgebraicGeometry.Space.IsFppfTorsor`, `AlgebraicGeometry.Space.IsSyntomicTorsor`,
  `AlgebraicGeometry.Space.IsSmoothTorsor`, `AlgebraicGeometry.Space.IsEtaleTorsor` and
  `AlgebraicGeometry.Space.IsZariskiTorsor` are the same condition for the other four topologies.

## Main results

* `AlgebraicGeometry.Space.isPseudoTorsor_iff_points`: a pseudo-torsor is characterized by simple
  transitivity on the points over every test scheme over the base.
* `AlgebraicGeometry.Space.isTrivialPseudoTorsor_iff_exists_section`: a pseudo-torsor is trivial
  exactly when its structure morphism to the base has a section.

## Implementation notes

The slice category of presheaves over `B` carries the pullback cartesian monoidal
structure, whose tensor product is the fibre product over `B`.  The general predicates on
an action in a cartesian monoidal category therefore apply verbatim to algebraic spaces
over `B`: `CategoryTheory.ModObj.leftSMul` is the shear map, so
`AlgebraicGeometry.IsPseudoTorsor` is the pseudo-torsor condition, while `Mod.regular` is
left multiplication on `G`, so `AlgebraicGeometry.IsTrivialPseudoTorsor` is equivariant
triviality.  In the slice the monoidal unit is the identity of `B`, so a morphism from the unit
to `X` is exactly a morphism `B ⟶ X.left` splitting the structure morphism of `X`.

The trivializing family is indexed by an arbitrary type and its members are arbitrary algebraic
spaces over the base; a local section over a member is a morphism from the monoidal unit of the
slice over it, which is the identity of that member, into the pullback of the acted-on object.
The six predicates differ only in the covering property imposed on the family, so they are all
instances of `AlgebraicGeometry.Space.IsTorsorFor`, which takes that property as an argument.

A test scheme over `B` is presented by a morphism from its Yoneda presheaf to `B`, and its
`X`-valued points over `B` are the morphisms out of that object in the slice.  Simple
transitivity is expressed by the unique group element carrying one point to another, a
formulation that also holds when there are no points.  The algebraicity hypotheses on `B`,
`G` and `X` are not needed for the characterization and are not imposed.

## References

* [Stacks Project, Tag 04TW](https://stacks.math.columbia.edu/tag/04TW)
* [Stacks Project, Tag 04TX](https://stacks.math.columbia.edu/tag/04TX)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 04TW "part (1): pseudo-torsor" AlgebraicGeometry.IsPseudoTorsor
add_to_stacks 04TW "part (2): trivial pseudo-torsor" AlgebraicGeometry.IsTrivialPseudoTorsor

add_to_stacks 04TX "trivial_iff_section"
  AlgebraicGeometry.isTrivial_iff_exists_globalSection

/-- A morphism in the slice over a presheaf `B` is an isomorphism as soon as it is
bijective on the sections over every representable object of the slice. -/
private lemma isIso_of_bijective_on_representable_sections
    (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) {F G : Over B} (f : F ⟶ G)
    (h : ∀ (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B), Function.Bijective
      (fun x : (Over.mk b : Over B) ⟶ F => x ≫ f)) : IsIso f := by
  have hw : ∀ (T : (BigFppfOver 𝒞 S hS)ᵒᵖ) (H : Over B) (z : H.left.obj T),
      (yonedaEquiv (X := T.unop) (F := H.left)).symm z ≫ H.hom =
        (yonedaEquiv (X := T.unop) (F := B)).symm (H.hom.app T z) := by
    intro T H z
    apply (yonedaEquiv (X := T.unop) (F := B)).injective
    rw [yonedaEquiv_comp]
    simp
  have hmap : IsIso ((Over.forget B).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [CategoryTheory.isIso_iff_bijective]
    let eF := yonedaEquiv (X := T.unop) (F := F.left)
    let eG := yonedaEquiv (X := T.unop) (F := G.left)
    constructor
    · intro x y hxy
      have hyval : F.hom.app T y = F.hom.app T x := by
        rw [← Over.w f]
        exact congrArg (G.hom.app T) hxy.symm
      let xx : (Over.mk ((yonedaEquiv (X := T.unop) (F := B)).symm (F.hom.app T x)) :
          Over B) ⟶ F := Over.homMk (eF.symm x) (hw T F x)
      let yy : (Over.mk ((yonedaEquiv (X := T.unop) (F := B)).symm (F.hom.app T x)) :
          Over B) ⟶ F := Over.homMk (eF.symm y) (by rw [hw, hyval]; rfl)
      have heq : xx ≫ f = yy ≫ f := by
        apply Over.OverMorphism.ext
        apply eG.injective
        show yonedaEquiv (xx.left ≫ f.left) = yonedaEquiv (yy.left ≫ f.left)
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simpa [xx, yy, eF, eG] using hxy
      have := congrArg Over.Hom.left ((h T.unop _).injective heq)
      simpa [xx, yy] using congrArg eF this
    · intro y
      let yy : (Over.mk ((yonedaEquiv (X := T.unop) (F := B)).symm (G.hom.app T y)) :
          Over B) ⟶ G := Over.homMk (eG.symm y) (hw T G y)
      obtain ⟨x, hx⟩ := (h T.unop _).surjective yy
      refine ⟨eF (Over.Hom.left x), ?_⟩
      show f.left.app T (eF (Over.Hom.left x)) = y
      calc
        f.left.app T (eF (Over.Hom.left x)) = eG (Over.Hom.left x ≫ f.left) := by
          rw [yonedaEquiv_comp]
        _ = eG (Over.Hom.left yy) := congrArg eG (congrArg Over.Hom.left hx)
        _ = y := by simp [yy, eG]
  exact (isIso_iff_of_reflects_iso f (Over.forget B)).mp hmap

/-- A pseudo-torsor is characterized by simple transitivity on the points of every test scheme
over its base presheaf. -/
@[stacks 04TX "pointwise_characterization",
  sga "3 IV 6.7" "(i) <=> (ii)",
  sga "3 IV 5.1.0" "pointwise criterion", sga "3 III 0.1" "fppf site presheaves"]
theorem isPseudoTorsor_iff_points
    (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (G X : Over B) [GrpObj G] [ModObj G X] :
    IsPseudoTorsor G X ↔
      ∀ (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
        (x y : (Over.mk b : Over B) ⟶ X),
        ∃! g : (Over.mk b : Over B) ⟶ G, g • x = y := by
  constructor
  · intro h T b x y
    exact (ModObj.isIso_leftSMul_iff.mp h) (Over.mk b) x y
  · intro h
    show IsIso (ModObj.leftSMul G X)
    apply isIso_of_bijective_on_representable_sections 𝒞 S hS B (ModObj.leftSMul G X)
    intro T b
    rw [Function.bijective_iff_existsUnique]
    intro k
    let x := k ≫ CartesianMonoidalCategory.snd X X
    let y := k ≫ CartesianMonoidalCategory.fst X X
    have hk : CartesianMonoidalCategory.lift y x = k :=
      CartesianMonoidalCategory.lift_comp_fst_snd k
    obtain ⟨g, hg, hgu⟩ := h T b x y
    refine ⟨CartesianMonoidalCategory.lift g x, ?_, ?_⟩
    · show CartesianMonoidalCategory.lift g x ≫ ModObj.leftSMul G X = k
      rw [ModObj.lift_leftSMul, hg, hk]
    · intro q hq
      let g' := q ≫ CartesianMonoidalCategory.fst G X
      let x' := q ≫ CartesianMonoidalCategory.snd G X
      have hqη : q = CartesianMonoidalCategory.lift g' x' :=
        (CartesianMonoidalCategory.lift_comp_fst_snd q).symm
      have hpair : CartesianMonoidalCategory.lift (g' • x') x' =
          CartesianMonoidalCategory.lift y x := by
        rw [← ModObj.lift_leftSMul, ← hqη]
        exact hq.trans hk.symm
      have hpair' := (CartesianMonoidalCategory.hom_ext_iff).mp hpair
      have hx' : x' = x := by simpa using hpair'.2
      have hg' : g' • x = y := by simpa [hx'] using hpair'.1
      have hgg' : g' = g := hgu g' hg'
      exact CartesianMonoidalCategory.hom_ext_iff.mpr
        ⟨by simpa [g'] using hgg', by simpa [x'] using hx'⟩

/-- A pseudo-torsor is trivial if and only if its structure morphism to the base presheaf has a
section. -/
@[stacks 04TX "part (2): trivial iff the structure morphism has a section"]
theorem isTrivialPseudoTorsor_iff_exists_section
    (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
    (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (G X : Over B) [GrpObj G] [ModObj G X] (hX : IsPseudoTorsor G X) :
    IsTrivialPseudoTorsor G X ↔ ∃ s : B ⟶ X.left, s ≫ X.hom = 𝟙 B := by
  rw [isTrivial_iff_exists_globalSection G X hX]
  constructor
  · rintro ⟨f⟩
    exact ⟨f.left, by simp⟩
  · rintro ⟨s, hs⟩
    exact ⟨Over.homMk s (by simpa using hs)⟩

/-! ### Principal homogeneous spaces and torsors -/

section Torsors

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)

/-- A pseudo-torsor under a group algebraic space which becomes trivial after a family of
morphisms to the base satisfying the covering property `P`: the members of the family are
algebraic spaces, the family satisfies `P`, and the pullback of the acted-on object to each
member has a section. -/
abbrev IsTorsorFor (_hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (_hG : IsAlgebraicSpace 𝒞 S hS G.left) (_hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (P : ∀ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u),
      (∀ i, Bᵢ i ⟶ B) → Prop) : Prop :=
  IsPseudoTorsor G X ∧
    ∃ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
      (f : ∀ i, Bᵢ i ⟶ B),
      (∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) ∧
        P I Bᵢ f ∧
        ∀ i, Nonempty (𝟙_ (Over (Bᵢ i)) ⟶ (Over.pullback (f i)).obj X)

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
  (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)

/-- A *principal homogeneous space* under a group algebraic space `G` over `B` is a pseudo-torsor
which has sections after an fpqc covering of `B`. -/
@[stacks 04TY "part (1): principal homogeneous space",
  sga "3 IV 5.1.5" "alg. spaces, fpqc",
  sga "3 IV 6.5" "fpqc row",
  sga "3 IV 5.1" "princ. homog. bundle",
  sga "3 VIB 10.15" "G-torsor, fpqc T", sga "1 XI 4.1"]
abbrev IsPrincipalHomogeneousSpace : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun _ _ f => IsFpqcCovering 𝒞 S hS f)

/-- A pseudo-torsor which has sections after an fppf covering of the base. -/
@[stacks 04TY "part (2): fppf torsor",
  sga "3 IV 5.1.5" "alg. spaces, fppf",
  sga "3 VIB 10.15" "G-torsor, fppf T"]
abbrev IsFppfTorsor : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun _ Bᵢ f => IsFppfCovering 𝒞 S hS Bᵢ f)

/-- A pseudo-torsor which has sections after a syntomic covering of the base. -/
@[stacks 04TY "part (2): syntomic torsor"]
abbrev IsSyntomicTorsor : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun _ Bᵢ f => IsSyntomicCovering 𝒞 S hS Bᵢ f)

/-- A pseudo-torsor which has sections after a smooth covering of the base. -/
@[stacks 04TY "part (2): smooth torsor"]
abbrev IsSmoothTorsor : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun _ Bᵢ f => IsSmoothCovering 𝒞 S hS Bᵢ f)

/-- A pseudo-torsor which has sections after an étale covering of the base; for a principal
homogeneous space this is quasi-isotriviality. -/
@[stacks 04TY "parts (2), (3): étale torsor and quasi-isotriviality",
  sga "3 IV 5.1.5" "alg. spaces, étale",
  sga "3 IV 6.5" "étale row",
  sga "3 VIB 10.15" "G-torsor, étale T"]
abbrev IsEtaleTorsor : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun _ Bᵢ f => IsEtaleCovering 𝒞 S hS Bᵢ f)

/-- A pseudo-torsor which has sections after a Zariski covering of the base; for a principal
homogeneous space this is local triviality. -/
@[stacks 04TY "parts (2), (4): Zariski torsor and local triviality",
  sga "1 XI 4.7" "more general",
  sga "3 IV 6.5" "(Zar) row"]
abbrev IsZariskiTorsor : Prop :=
  IsTorsorFor 𝒞 S hS B hB G X hG hX (fun I Bᵢ f => IsZariskiCovering 𝒞 S hS I Bᵢ f)

end Torsors

end AlgebraicGeometry.Space

end
