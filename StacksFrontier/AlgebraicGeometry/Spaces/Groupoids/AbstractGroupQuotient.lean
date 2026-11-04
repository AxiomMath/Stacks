module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.GroupTheory.GroupAction.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# Quotients of algebraic spaces by free actions of abstract groups

An abstract group `G` acting on a presheaf `X` on the big fppf site of `S` by pointwise
actions commuting with restriction has a quotient presheaf `T ↦ X(T)/G` of pointwise
orbits. Its fppf sheafification is the quotient of `X` by `G`, and when `X` is an
algebraic space and the action is free on the points over every test object, the quotient
is again an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.IsNaturalAction` is the compatibility of a family of pointwise
  actions with restriction.
* `AlgebraicGeometry.Space.orbitPresheaf` is the presheaf of pointwise orbits of a natural
  action, and `AlgebraicGeometry.Space.orbitQuotientSheaf` is its fppf sheafification.
* `AlgebraicGeometry.Space.orbitLift` and `AlgebraicGeometry.Space.orbitQuotientLift` are the
  universal properties of those two quotients: an invariant map out of `X` factors through
  the orbit presheaf, and through the quotient sheaf when its target is a sheaf.
* `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints` is freeness of the action on the points
  over the test objects whose underlying scheme is nonempty.

## Main results

* `AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`: a group action on a sheaf
  of sets is cancellative on the points over every object of the site exactly when the group
  is trivial.
* `AlgebraicGeometry.Space.isAlgebraicSpace_orbitQuotientSheaf`: the quotient of an
  algebraic space by an action free over every test object is an algebraic space. See the
  implementation notes: by the previous result that hypothesis forces the group to be
  trivial, so this is the degenerate case rather than Tag 071S itself.

## Implementation notes

The quotient is formed before sheafification, as in the source: it is the sheafification
of the pointwise orbit presheaf, not the pointwise quotient of an already sheafified
presentation.

`isAlgebraicSpace_orbitQuotientSheaf` asks freeness of the action on the points over
*every* object of the site, including the objects with empty underlying scheme. Over such an
object the sheaf `X` is terminal, so a free action there forces `G` to be trivial;
`forall_isCancelSMul_iff_subsingleton` proves that the hypothesis is in fact *equivalent* to
`Subsingleton G`. The hypothesis is therefore unsatisfiable for every nontrivial group, and
the theorem is proved by exhibiting the resulting isomorphism rather than by a descent
argument. It carries **no** Stacks attribute — it is vacuous precisely where Tag 071S has
content. An action of a group *space* escapes this, because its own points over the empty
object form a one-element group; the collapse is particular to abstract groups.

Stating the tag faithfully means taking `IsFreeOnNonemptyPoints` as the hypothesis, and
proving it needs the geometry of the orbit relation: a surjective étale chart `U ⟶ X`, the
relation `⨿_{g} (U ×_X U) ⟶ U ×_S U` it generates, and the identification of `X/G` with the
quotient of `U` by that relation. The equivalence-relation machinery for the analogous
statement about a *scheme* `U` is `AlgebraicGeometry.Space.actionRelation` and
`AlgebraicGeometry.Space.actionQuotient` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation`, gated on
`ActsNontriviallyOnFixedResidueFields`. The final step, that the quotient of a scheme by an
étale equivalence relation is an algebraic space, is available in this library only with an
undischarged effective fppf descent hypothesis — see
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` and
`AlgebraicGeometry.isAlgebraicSpace_quotientSheaf_of_chart` — so Tag 071S cannot be closed
here either.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type*) [Group G]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [∀ T, MulAction G (X.obj T)]

/-- A family of pointwise `G`-actions on the values of a presheaf `X` on the big fppf site
of `S` is *natural* when every restriction map of `X` is `G`-equivariant. -/
abbrev IsNaturalAction : Prop :=
  ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (g : G) (x : X.obj T),
    X.map f (g • x) = g • X.map f x

/-- The map on orbit sets induced by a restriction map of `X`. -/
def orbitMap (hnat : IsNaturalAction B S hS G X) {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) :
    Quotient (MulAction.orbitRel G (X.obj T)) → Quotient (MulAction.orbitRel G (X.obj U)) :=
  Quotient.map (X.map f)
    (show ∀ ⦃x y : X.obj T⦄, MulAction.orbitRel G (X.obj T) x y →
      MulAction.orbitRel G (X.obj U) (X.map f x) (X.map f y) from by
    intro x y h
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨g, (hnat f g y).symm⟩)

/-- The presheaf of pointwise orbits of a natural action, sending an object `T` of the big
fppf site of `S` to the orbit set `X(T)/G`. -/
def orbitPresheaf (hnat : IsNaturalAction B S hS G X) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := Quotient (MulAction.orbitRel G (X.obj T))
  map f := ↾(orbitMap B S hS G X hnat f)
  map_id T := by
    ext q
    induction q using Quotient.inductionOn with
    | _ x => simp [orbitMap]
  map_comp {_ _ _} f g := by
    ext q
    induction q using Quotient.inductionOn with
    | _ x => simp [orbitMap]

/-- A `G`-invariant map out of `X` descends to the presheaf of pointwise orbits. -/
def orbitLift (hnat : IsNaturalAction B S hS G X)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y)
    (hφ : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (g : G) (x : X.obj T), φ.app T (g • x) = φ.app T x) :
    orbitPresheaf B S hS G X hnat ⟶ Y where
  app T := ↾(Quotient.lift (φ.app T)
    (show ∀ ⦃x y : X.obj T⦄, MulAction.orbitRel G (X.obj T) x y →
        φ.app T x = φ.app T y from by
      intro x y h
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
      exact hφ T g y))
  naturality {T U} f := by
    ext q
    induction q using Quotient.inductionOn with
    | _ x => exact NatTrans.naturality_apply φ f x

/-- The quotient of `X` by a natural action of an abstract group `G`, the fppf
sheafification of the presheaf `T ↦ X(T)/G` of pointwise orbits. -/
noncomputable def orbitQuotientSheaf [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G X) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  (presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).obj
    (orbitPresheaf B S hS G X hnat)

/-- The universal property of the quotient sheaf: a `G`-invariant map from `X` to a sheaf `Y`
factors through `X/G`. -/
noncomputable def orbitQuotientLift [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G X)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y)
    (hφ : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (g : G) (x : X.obj T), φ.app T (g • x) = φ.app T x)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) :
    (orbitQuotientSheaf B S hS G X hnat).obj ⟶ Y :=
  sheafifyLift (BigFppfOver.topology B S hS) (orbitLift B S hS G X hnat φ hφ) hY

/-- For a trivial group the orbit relation on any action is equality. -/
private theorem orbitRel_iff_eq_of_subsingleton {α : Type*} [MulAction G α] [Subsingleton G]
    {x y : α} : MulAction.orbitRel G α x y ↔ x = y := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨?_, fun h => ⟨1, by simp [h]⟩⟩
  rintro ⟨g, rfl⟩
  simp [Subsingleton.elim g 1]

/-- For a trivial group the projection to the presheaf of pointwise orbits is an
isomorphism. -/
private noncomputable def orbitPresheafIso (hnat : IsNaturalAction B S hS G X)
    [Subsingleton G] : orbitPresheaf B S hS G X hnat ≅ X := by
  let e (T : (BigFppfOver B S hS)ᵒᵖ) :
      Quotient (MulAction.orbitRel G (X.obj T)) ≃ X.obj T :=
    { toFun := Quotient.lift id fun _ _ h => (orbitRel_iff_eq_of_subsingleton G).mp h
      invFun := Quotient.mk _
      left_inv := fun q => by induction q using Quotient.inductionOn with | _ x => rfl
      right_inv := fun _ => rfl }
  refine NatIso.ofComponents (fun T => Equiv.toIso (e T)) fun {T U} f => ?_
  ext q
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- For a trivial group every action is cancellative. -/
private theorem isCancelSMul_of_subsingleton {α : Type*} [MulAction G α] [Subsingleton G] :
    IsCancelSMul G α where
  left_cancel' a b c hbc := by rwa [Subsingleton.elim a 1, one_smul, one_smul] at hbc
  right_cancel' a b _ _ := Subsingleton.elim a b

/-- Asking a group action on a sheaf of sets to be cancellative on the points over *every*
object of the big fppf site is the same as asking the group to be trivial.

The big fppf site of `S` has an object with empty underlying scheme, and a sheaf is terminal
there, so the group acts on a one-element set: two elements acting alike on that single point
must be equal. Conversely a trivial group acts cancellatively on everything. An action of an
abstract group therefore has no room to be free over the empty object, which is what
distinguishes this situation from an action of a group *space*, whose own points over the
empty object form a one-element group. -/
theorem forall_isCancelSMul_iff_subsingleton
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    (∀ T, IsCancelSMul G (X.obj T)) ↔ Subsingleton G := by
  refine ⟨fun hfree => ?_, fun _ _ => isCancelSMul_of_subsingleton G⟩
  let emptyOver : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage (X := B.obj B.contains_empty) (Y := B.obj hS)
      (Scheme.emptyTo (B.inclusion.obj (B.obj hS))))
  let A : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hX⟩
  have hterm := A.isTerminalOfBotCover emptyOver
    (BigFppfOver.bot_mem_topology_of_left_eq_empty B S hS emptyOver rfl)
  have := Limits.Types.isTerminalEquivUnique _ hterm
  have := hfree (Opposite.op emptyOver)
  exact ⟨fun g h => IsCancelSMul.right_cancel g h (hterm.from PUnit PUnit.unit)
    (Subsingleton.elim _ _)⟩

/-- The action of `G` on the points of `X` is *free* in the sense the Stacks Project uses for
an action of an abstract group on an algebraic space, read on the test objects whose underlying
scheme is nonempty: over each such object two group elements acting alike on a point are
equal.

The restriction to nonempty test objects is what keeps the condition satisfiable for a
nontrivial group, by `AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`. It is also
the only form the geometry uses: freeness enters the source's argument at points of the orbit
relation, which are points of nonempty schemes. -/
def IsFreeOnNonemptyPoints : Prop :=
  ∀ T : (BigFppfOver B S hS)ᵒᵖ,
    Nonempty ((BigFppfOver.toScheme B S hS).obj T.unop) → IsCancelSMul G (X.obj T)

/-- Freeness over every test object is a stronger demand than freeness over the test objects
with nonempty underlying scheme. -/
theorem isFreeOnNonemptyPoints_of_forall_isCancelSMul
    (hfree : ∀ T, IsCancelSMul G (X.obj T)) :
    IsFreeOnNonemptyPoints B S hS G X :=
  fun T _ => hfree T

/-- **Stacks 071S, the algebraic-space property**, in the degenerate range of its
hypothesis. The quotient of an algebraic space over `S` by a free action of an abstract
group is an algebraic space over `S`.

It does **not** carry `@[stacks 071S]`: `hfree` asks for a cancellative action on the
points over *every* object of the site, including those with empty underlying scheme, where
`X` is terminal. By `AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton` that
hypothesis is equivalent to `G` being trivial, so the statement is vacuous exactly where the
tag has content. The tag belongs on the form of this result whose freeness hypothesis is
`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, which needs the geometry of the orbit
relation. -/
theorem isAlgebraicSpace_orbitQuotientSheaf
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : ∀ T, IsCancelSMul G (X.obj T)) :
    IsAlgebraicSpace B S hS (orbitQuotientSheaf B S hS G X hnat).obj := by
  have : Subsingleton G :=
    (forall_isCancelSMul_iff_subsingleton B S hS G X hX.isSheaf).mp hfree
  let eQ : (orbitQuotientSheaf B S hS G X hnat).obj ≅ X :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
        ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
          (orbitPresheafIso B S hS G X hnat)) ≪≫
      (isoSheafify (BigFppfOver.topology B S hS) hX.isSheaf).symm
  exact isAlgebraicSpace_of_iso B S hS eQ.symm hX

end AlgebraicGeometry.Space

end
