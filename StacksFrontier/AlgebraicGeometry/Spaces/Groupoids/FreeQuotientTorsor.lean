module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic

/-!
# The quotient map of a free group action is a pseudo-torsor split by the total space

Let `X` be a presheaf of sets on the big fppf site of a scheme `S` carrying a natural action of
an abstract group `G`, and let `X/G` be the quotient of `X` by `G`, that is the fppf
sheafification of the presheaf `T ↦ X(T)/G` of pointwise orbits. This file describes the
quotient map `q : X ⟶ X/G` and its kernel pair: `q` is surjective as a map of fppf sheaves, it
identifies a point of `X` with each of its translates, and two points of `X` with the same
image under `q` become translates of each other by a *single* element of `G` locally on the
base. When the action is free that element is unique over every test object whose underlying
scheme is nonempty.

Taken together these statements say that `X ×_{X/G} X` is, locally on `X`, the disjoint union
of one copy of `X` for each element of `G`: the quotient map is a pseudo-torsor under the
constant group `G`, and it is split by `X` itself. That is the form in which the quotient of
an algebraic space by a free action of a finite group is used, both to recognise the quotient
map as a finite étale `G`-covering and to compute with sheaves on the quotient which have been
trivialized over `X`.

## Main definitions

* `AlgebraicGeometry.Space.toOrbitPresheaf` is the projection of `X` onto its presheaf of
  pointwise orbits.
* `AlgebraicGeometry.Space.toOrbitQuotient` is the quotient map `X ⟶ X/G`.
* `AlgebraicGeometry.Space.orbitSieve` is the sieve of arrows along which two given points of
  `X` become translates of each other by a single element of `G`.

## Main results

* `AlgebraicGeometry.Space.toOrbitQuotient_smul`: the quotient map is invariant.
* `AlgebraicGeometry.Space.isLocallySurjective_toOrbitQuotient`: the quotient map is
  surjective as a map of fppf sheaves.
* `AlgebraicGeometry.Space.orbitSieve_mem`: two points of `X` with the same image in `X/G`
  are translates of each other by a single element of `G` locally on the base.
* `AlgebraicGeometry.Space.exists_mem_topology_existsUnique_smul_eq`: for a free action the
  group element provided by the previous result is unique over the test objects with nonempty
  underlying scheme, so that the kernel pair of the quotient map is locally one copy of `X`
  for each element of `G`.

## Implementation notes

The locality of `AlgebraicGeometry.Space.orbitSieve_mem` is not an artefact of the proof: the
presheaf of pointwise orbits is not a separated presheaf, so the element of `G` relating two
points of `X` with the same image in `X/G` is genuinely only a locally constant function on the
base. Over a test object which is a disjoint union of two pieces, a point of `X` and the point
obtained by translating it by two different group elements on the two pieces have the same
image in `X/G` while being translates of each other by no single element of `G`. This is why
the statements below are statements about covering sieves rather than about sections, and why
the comparison morphism from the disjoint union of `G` copies of `X` to the kernel pair of the
quotient map is an isomorphism only after sheafification.

Freeness is taken in the form `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, which asks for
a cancellative action on the points over the test objects with nonempty underlying scheme.
That restriction is forced: over a test object with empty underlying scheme a sheaf of sets is
terminal, so a cancellative action there would make `G` trivial, by
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`. It is also exactly what the
geometry uses, since the uniqueness of the translating element is only ever read over a
nonempty object.

Nothing here assumes `X` to be a sheaf, to be an algebraic space, or `G` to be finite, and `G`
lives in an arbitrary universe: the presheaf of pointwise orbits of a `Type u`-valued presheaf
again takes values in `Type u` whatever the universe of `G`.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : Type v) [Group G]
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [∀ T, MulAction G (X.obj T)]

/-- The projection of `X` onto its presheaf of pointwise orbits, sending a point of `X` over a
test object to its orbit under `G`. -/
def toOrbitPresheaf (hnat : IsNaturalAction B S hS G X) :
    X ⟶ orbitPresheaf B S hS G X hnat where
  app T := ↾(fun x ↦ Quotient.mk (MulAction.orbitRel G (X.obj T)) x)
  naturality := by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- The projection onto the presheaf of pointwise orbits sends a point of `X` to its orbit. -/
@[simp]
theorem toOrbitPresheaf_app (hnat : IsNaturalAction B S hS G X)
    (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.obj T) :
    (toOrbitPresheaf B S hS G X hnat).app T x =
      Quotient.mk (MulAction.orbitRel G (X.obj T)) x :=
  rfl

/-- The quotient map from `X` to the quotient of `X` by a natural action of an abstract group
`G`, the composite of the projection onto the presheaf of pointwise orbits with the
sheafification map. -/
noncomputable def toOrbitQuotient [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hnat : IsNaturalAction B S hS G X) :
    X ⟶ (orbitQuotientSheaf B S hS G X hnat).obj :=
  toOrbitPresheaf B S hS G X hnat ≫
    toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The quotient map is the projection onto the presheaf of pointwise orbits followed by the
sheafification map. -/
theorem toOrbitQuotient_eq (hnat : IsNaturalAction B S hS G X) :
    toOrbitQuotient B S hS G X hnat =
      toOrbitPresheaf B S hS G X hnat ≫
        toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat) :=
  rfl

/-- The image of a point of `X` under the quotient map is the image of its orbit under the
sheafification map. -/
@[simp]
theorem toOrbitQuotient_app (hnat : IsNaturalAction B S hS G X)
    (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.obj T) :
    (toOrbitQuotient B S hS G X hnat).app T x =
      (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat)).app T
        (Quotient.mk (MulAction.orbitRel G (X.obj T)) x) :=
  rfl

/-- **The quotient map is invariant.** A point of `X` and its translate by a group element have
the same image in the quotient of `X` by `G`. -/
theorem toOrbitQuotient_smul (hnat : IsNaturalAction B S hS G X)
    {T : (BigFppfOver B S hS)ᵒᵖ} (g : G) (x : X.obj T) :
    (toOrbitQuotient B S hS G X hnat).app T (g • x) =
      (toOrbitQuotient B S hS G X hnat).app T x := by
  have hq : Quotient.mk (MulAction.orbitRel G (X.obj T)) (g • x) =
      Quotient.mk (MulAction.orbitRel G (X.obj T)) x :=
    Quotient.sound (MulAction.mem_orbit x g)
  rw [toOrbitQuotient_app, toOrbitQuotient_app, hq]

/-- **The quotient map is surjective as a map of fppf sheaves.** Every point of the quotient of
`X` by `G` lifts, locally for the fppf topology, to a point of `X`: the projection onto the
presheaf of pointwise orbits is surjective on sections, and the sheafification map is locally
surjective. -/
theorem isLocallySurjective_toOrbitQuotient (hnat : IsNaturalAction B S hS G X) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (toOrbitQuotient B S hS G X hnat) := by
  have h₁ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (toOrbitPresheaf B S hS G X hnat) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun _ q ↦ Quot.exists_rep q
  have h₂ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat)) :=
    ((GrothendieckTopology.WEqualsLocallyBijective.iff
      (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat))).1
        ((BigFppfOver.topology B S hS).W_toSheafify _)).2
  rw [toOrbitQuotient_eq]
  exact Presheaf.isLocallySurjective_comp (BigFppfOver.topology B S hS)
    (toOrbitPresheaf B S hS G X hnat)
    (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat))

/-- The sieve of arrows along which two given points `x` and `y` of `X` over a test object
become translates of each other by a single element of `G`: an arrow `f` belongs to it when
some `g : G` carries the restriction of `y` along `f` to the restriction of `x`.

It is a sieve because the action is natural: the same group element continues to work after a
further restriction. -/
def orbitSieve (hnat : IsNaturalAction B S hS G X) {T : (BigFppfOver B S hS)ᵒᵖ}
    (x y : X.obj T) : Sieve T.unop where
  arrows _ f := ∃ g : G, g • X.map f.op y = X.map f.op x
  downward_closed := by
    rintro b c f ⟨g, hg⟩ k
    refine ⟨g, ?_⟩
    have h₁ : ∀ z : X.obj T, X.map (k ≫ f).op z = X.map k.op (X.map f.op z) := by
      intro z
      rw [op_comp, Functor.map_comp_apply]
    rw [h₁, h₁, ← hg, hnat k.op g]

/-- **Two points of `X` with the same image in `X/G` are translates of each other by a single
group element, locally on the base.** The sieve of arrows along which they become translates of
each other is a covering sieve of the big fppf site.

This is the kernel-pair description of the quotient map: no freeness is needed for it, and no
single group element need relate the two points globally, because the presheaf of pointwise
orbits is not separated. -/
theorem orbitSieve_mem (hnat : IsNaturalAction B S hS G X)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x y : X.obj T)
    (h : (toOrbitQuotient B S hS G X hnat).app T x =
      (toOrbitQuotient B S hS G X hnat).app T y) :
    orbitSieve B S hS G X hnat x y ∈ BigFppfOver.topology B S hS T.unop := by
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat)) :=
    ((GrothendieckTopology.WEqualsLocallyBijective.iff
      (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat))).1
        ((BigFppfOver.topology B S hS).W_toSheafify _)).1
  have hmem := Presheaf.equalizerSieve_mem (BigFppfOver.topology B S hS)
    (toSheafify (BigFppfOver.topology B S hS) (orbitPresheaf B S hS G X hnat))
    ((toOrbitPresheaf B S hS G X hnat).app T x)
    ((toOrbitPresheaf B S hS G X hnat).app T y) h
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hmem
  intro b f hf
  have hf' : Quotient.mk (MulAction.orbitRel G (X.obj (Opposite.op b))) (X.map f.op x) =
      Quotient.mk (MulAction.orbitRel G (X.obj (Opposite.op b))) (X.map f.op y) := hf
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hf')
  exact ⟨g, hg⟩

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **For a free action the group element translating one point of `X` into another is unique**
over a test object whose underlying scheme is nonempty. -/
theorem smul_right_cancel_of_nonempty (hfree : IsFreeOnNonemptyPoints B S hS G X)
    {T : (BigFppfOver B S hS)ᵒᵖ} (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T.unop))
    (x : X.obj T) {g g' : G} (h : g • x = g' • x) : g = g' :=
  have := hfree T hT
  IsCancelSMul.right_cancel g g' x h

/-- **The kernel pair of the quotient map of a free action is locally one copy of `X` for each
element of `G`.** If two points of `X` have the same image in the quotient of `X` by a free
action of `G`, then there is a covering sieve of the base along whose arrows the two points are
translates of each other by a group element which, over an object with nonempty underlying
scheme, is unique.

This is the statement that the quotient map `X ⟶ X/G` is a pseudo-torsor under the constant
group `G` split by `X` itself: the disjoint union of one copy of `X` for each element of `G`
is, locally on the base, the fibre product of `X` with itself over `X/G`. -/
theorem exists_mem_topology_existsUnique_smul_eq (hnat : IsNaturalAction B S hS G X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x y : X.obj T)
    (h : (toOrbitQuotient B S hS G X hnat).app T x =
      (toOrbitQuotient B S hS G X hnat).app T y) :
    ∃ V : Sieve T.unop, V ∈ BigFppfOver.topology B S hS T.unop ∧
      ∀ ⦃b : BigFppfOver B S hS⦄ (f : b ⟶ T.unop), V f →
        Nonempty ((BigFppfOver.toScheme B S hS).obj b) →
        ∃! g : G, g • X.map f.op y = X.map f.op x := by
  refine ⟨orbitSieve B S hS G X hnat x y, orbitSieve_mem B S hS G X hnat x y h, ?_⟩
  intro b f hf hb
  obtain ⟨g, hg⟩ := hf
  refine ⟨g, hg, fun g' hg' ↦ ?_⟩
  exact smul_right_cancel_of_nonempty B S hS G X hfree (T := Opposite.op b) hb
    (X.map f.op y) (hg'.trans hg.symm)

end AlgebraicGeometry.Space

end
