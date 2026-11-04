module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingTwoPoints
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic

/-!
# Picard groups and the glueing of two rational points

Let `k` be an algebraically closed field and let `f : X' ⟶ X` be the glueing of two distinct
rational points `a, b` of an algebraic `k`-scheme `X'`, in the sense of
[Stacks, Tag 0C1J]: `f` is finite, it is an isomorphism away from the image point `x` of `a`
and `b`, and the structure sheaf of `X` is the subsheaf of `f_*𝒪_{X'}` cut out by the
condition that the values at `a` and at `b` agree. [Stacks, Tag 0C1M] records an exact
sequence

`k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`,

whose first map sends a scalar `c` to the invertible `𝒪_X`-module obtained by glueing the
fibres of `𝒪_{X'}` at `a` and `b` with ratio `c`, and whose second map is pullback along `f`.

Two of its clauses are proved here.

**Surjectivity of pullback.** Every invertible `𝒪_{X'}`-module is the pullback of an invertible
`𝒪_X`-module. The morphism `f` is finite and is an isomorphism over an open `U` of `X` whose
complement is the single point `x`, hence discrete, so this is exactly the descent statement of
[Stacks, Tag 0C0T]. Transporting it to Picard classes uses that pullback computes the class of
`L` from the class of `f^*L` for *any* representative `L`, so the representative chosen by the
skeleton underlying `Pic(X')` may be fed to Tag 0C0T directly.

**Vanishing of the first map when `a` and `b` lie on different connected components.** The
first map of the sequence is the connecting homomorphism of the short exact sequence of
sheaves of units on `X` whose middle term is `f_*𝒪_{X'}^*`, so it kills exactly those scalars
that are the ratio of the values at `a` and at `b` of a unit on the whole of `X'`. That the
map is zero is therefore the statement that *every* scalar is such a ratio, which is what is
proved: an algebraic `k`-scheme is locally Noetherian, hence locally connected, so the
connected component `U` of the image of `a` is open and closed; the point of `b` lies in the
complementary open `V`; and the constant `c` on `U` together with the constant `1` on `V` glue
to a section of `𝒪_{X'}` over `X'`. The glued section is exhibited as `(c - 1) e + 1`, where
`e` is the idempotent that is `1` on `U` and `0` on `V`; the inverse is then the explicit
section `(c⁻¹ - 1) e + 1`, so no second glueing is needed to see that a unit has been built.

## Main results

* `Stacks.GluePicard.surjective_schemePullbackClassHom` — pullback `Pic(X) → Pic(X')` along the
  glueing of two points is surjective.
* `Stacks.GluePicard.exists_globalUnit_sectionAt_eq_of_ne_connectedComponents` — when the two
  glued points lie on different connected components of `X'`, every scalar is the ratio of the
  values at those points of a unit on `X'`; equivalently the first map of the sequence of
  Tag 0C1M is zero.

## Implementation notes

The Picard group used is `Stacks.Picard.ofScheme`, the units of the skeleton of the category of
invertible sheaves of modules on a scheme, and the pullback map is the bundled homomorphism
`Stacks.Picard.schemePullbackClassHom`. It is bundled, which is what the vanishing statement
needs, and it is defined directly by pullback of invertible modules, so
`Stacks.Picard.pullbackClass_classOf` evaluates it on a representative in one step.

Evaluation of a section at a rational point is `AlgebraicGeometry.sectionAt`. Two facts about
it are used: `AlgebraicGeometry.sectionAt_map`, its compatibility with restriction, and
`AlgebraicGeometry.sectionAt_constHom`, which says that it sends the constant section
`AlgebraicGeometry.constHom` attached to a scalar `t` back to `t`. The second is the only place
where the hypothesis that the glued points are `k`-rational — that is, sections of the
structure morphism — is used, and only for `a`, since the value at `b` of the section built
below is read off from the vanishing of the idempotent there. The constant sections are
phrased through `AlgebraicGeometry.Scheme.Hom.appLE` rather than through `app` composed with a
restriction, because `appLE` names the open on which a section lands and so avoids having to
identify `π ⁻¹ᵁ ⊤` with `⊤`.

The multiplicative ratio of the two values is written out as a product with an inverse rather
than packaged as an element of `kˣ`: the conclusion below gives the two values separately, `c`
at `a` and `1` at `b`, which determines the ratio and is what the connecting homomorphism
consumes.

## References

* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GluePicard

open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

/-- **Pullback of invertible modules along the glueing of two rational points is surjective on
Picard groups.** The glueing is finite and is an isomorphism away from a single point, so
[Stacks, Tag 0C0T] descends a representative of any class on `X'` to `X`. -/
@[stacks 0C1M "surjectivity"]
theorem surjective_schemePullbackClassHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    Function.Surjective (Stacks.Picard.schemePullbackClassHom f) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfin, ⟨U, hU, hUiso⟩, -, -, -⟩ := h
  have : IsFinite f := hfin
  have : IsIso (f ∣_ U) := hUiso
  have : DiscreteTopology ((U : Set X)ᶜ : Set X) := by
    rw [hU, compl_compl]
    have : Subsingleton
        {y : X // y ∈ ({(a ≫ f).base (IsLocalRing.closedPoint k)} : Set X)} :=
      Set.subsingleton_singleton.coe_sort
    infer_instance
  intro x
  obtain ⟨M, hM, ⟨e⟩⟩ := Stacks.PicFinite.exists_isInvertible_modulePullback_iso f U
    (Stacks.Picard.picardRepresentative X'.toSheafedSpace x).obj
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _
      (structureIsSheaf X'.toSheafedSpace) _).mp
      (Stacks.Picard.picardRepresentative X'.toSheafedSpace x).property)
  let M₀ : SheafOfModules.{u} (structureSheaf X.toSheafedSpace.presheaf
    (structureIsSheaf X.toSheafedSpace)) := M
  have hM' : Stacks.SheafOfModules.IsInvertible X.toSheafedSpace.presheaf
      (structureIsSheaf X.toSheafedSpace) M₀ :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _
      (structureIsSheaf X.toSheafedSpace) M₀).mpr hM
  refine ⟨Stacks.SheafOfModules.picardClass X.toSheafedSpace.presheaf
      (structureIsSheaf X.toSheafedSpace) M₀ hM',
    (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom M₀ hM').trans
      (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩).trans
        (Stacks.Picard.classOf_picardRepresentative X'.toSheafedSpace x))⟩

/-- On an algebraic `k`-scheme, two rational points on different connected components are
separated by a unit taking the prescribed value at the first point and the value `1` at the
second: the connected component of the first point is open and closed, and the prescribed
constant on it glues with `1` on the complement. -/
private theorem exists_globalUnit_aux {k : Type u} [Field k] {X' : Scheme.{u}}
    [X'.Over (Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    (a b : Spec (.of k) ⟶ X') (ha : a.IsOver (Spec (.of k)))
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) (c : kˣ) :
    ∃ s : Γ(X', ⊤)ˣ,
      AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) (s : Γ(X', ⊤)) = (c : k) ∧
        AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) (s : Γ(X', ⊤)) = 1 := by
  have hnoeth : IsLocallyNoetherian X' :=
    LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (.of k))
  let U : X'.Opens :=
    X'.connectedComponentOpens (ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)))
  let V : X'.Opens := ⟨(U : Set X')ᶜ, (X'.isClosed_connectedComponentOpens _).isOpen_compl⟩
  have haU : a.base (IsLocalRing.closedPoint k) ∈ U := rfl
  have hbV : b.base (IsLocalRing.closedPoint k) ∈ V := hab.symm
  have hUV : U ⊓ V = ⊥ := by
    ext y
    simp [V]
  have htop : U ⊔ V = ⊤ := by
    ext y
    by_cases hy : y ∈ U <;> simp [V]
  let W : Bool → X'.Opens := fun i => cond i V U
  have hcover : (⊤ : X'.Opens) ≤ ⨆ i, W i := by
    rw [← htop]
    exact sup_le (le_iSup_of_le false le_rfl) (le_iSup_of_le true le_rfl)
  let Fsh : TopCat.Sheaf CommRingCat.{u} X' := ⟨X'.presheaf, X'.IsSheaf⟩
  let ef : ∀ i : Bool, Γ(X', W i) := fun i =>
    match i with
    | false => (1 : Γ(X', U))
    | true => (0 : Γ(X', V))
  have hbot : ∀ Z : X'.Opens, Z = ⊥ → Subsingleton Γ(X', Z) := by
    intro Z hZ
    rw [hZ]
    infer_instance
  have hcompat : X'.presheaf.IsCompatible W ef := by
    intro i j
    cases i <;> cases j
    · rw [Subsingleton.elim (Opens.infLELeft (W false) (W false))
        (Opens.infLERight (W false) (W false))]
    · exact @Subsingleton.elim _ (hbot (W false ⊓ W true) hUV) _ _
    · exact @Subsingleton.elim _ (hbot (W true ⊓ W false) (inf_comm U V ▸ hUV)) _ _
    · rw [Subsingleton.elim (Opens.infLELeft (W true) (W true))
        (Opens.infLERight (W true) (W true))]
  obtain ⟨e, he, -⟩ := Fsh.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcover ef hcompat
  have heU : X'.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op e = 1 := he false
  have heV : X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op e = 0 := he true
  have hesq : e * e = e := by
    refine Fsh.eq_of_locally_eq₂ (U₁ := U) (U₂ := V) (homOfLE le_top) (homOfLE le_top)
      htop.ge (e * e) e ?_ ?_
    · rw [map_mul, heU, one_mul]
    · rw [map_mul, heV, mul_zero]
  have hle : (⊤ : X'.Opens) ≤ (X' ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := by simp
  have hring : ((c : k) - 1) * (((c⁻¹ : kˣ) : k) - 1) +
      (((c : k) - 1) + (((c⁻¹ : kˣ) : k) - 1)) = 0 := by
    linear_combination c.mul_inv
  have hcoef : constHom X' ⊤ hle ((c : k) - 1) * constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1) +
      (constHom X' ⊤ hle ((c : k) - 1) + constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1)) = 0 := by
    rw [← map_mul, ← map_add, ← map_add, hring, map_zero]
  have hmulone : (constHom X' ⊤ hle ((c : k) - 1) * e + 1) *
      (constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1) * e + 1) = 1 := by
    have hexp : (constHom X' ⊤ hle ((c : k) - 1) * e + 1) *
        (constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1) * e + 1) =
        constHom X' ⊤ hle ((c : k) - 1) *
            constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1) * (e * e) +
          (constHom X' ⊤ hle ((c : k) - 1) +
            constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1)) * e + 1 := by
      ring
    rw [hexp, hesq, ← add_mul, hcoef, zero_mul, zero_add]
  have hone : AlgebraicGeometry.sectionAt a U haU (1 : Γ(X', U)) = 1 :=
    map_one (sectionAtHom a U haU)
  have hzero : AlgebraicGeometry.sectionAt b V hbV (0 : Γ(X', V)) = 0 :=
    map_zero (sectionAtHom b V hbV)
  refine ⟨⟨constHom X' ⊤ hle ((c : k) - 1) * e + 1,
    constHom X' ⊤ hle (((c⁻¹ : kˣ) : k) - 1) * e + 1, hmulone, by
      rw [mul_comm]; exact hmulone⟩, ?_, ?_⟩
  · rw [← sectionAtHom_apply, map_add, map_mul, map_one, sectionAtHom_apply,
      sectionAtHom_apply, sectionAt_constHom a ha ⊤ (Opens.mem_top _) hle,
      ← sectionAt_map a (homOfLE (le_top : U ≤ ⊤)) haU e, heU, hone]
    ring
  · rw [← sectionAtHom_apply, map_add, map_mul, map_one, sectionAtHom_apply,
      sectionAtHom_apply, ← sectionAt_map b (homOfLE (le_top : V ≤ ⊤)) hbV e, heV, hzero,
      mul_zero, zero_add]

/-- **The first map of the sequence of Stacks Tag 0C1M is zero when the two glued points lie
on different connected components of `X'`**, in the form that the connecting homomorphism
consumes: every scalar `c` is the ratio of the values at `a` and at `b` of a unit on all of
`X'`, so the invertible module obtained by glueing the fibres at `a` and `b` with ratio `c` is
trivial. -/
@[stacks 0C1M "the lifting criterion for vanishing at points on different components"]
theorem exists_globalUnit_sectionAt_eq_of_ne_connectedComponents
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) (c : kˣ) :
    ∃ s : Γ(X', ⊤)ˣ,
      AlgebraicGeometry.sectionAt a ⊤ (Opens.mem_top _) (s : Γ(X', ⊤)) = (c : k) ∧
        AlgebraicGeometry.sectionAt b ⊤ (Opens.mem_top _) (s : Γ(X', ⊤)) = 1 := by
  have hft : LocallyOfFiniteType (X' ↘ Spec (.of k)) := h.2.2.2.2.1
  exact exists_globalUnit_aux a b h.1 hab c

end Stacks.GluePicard

end
