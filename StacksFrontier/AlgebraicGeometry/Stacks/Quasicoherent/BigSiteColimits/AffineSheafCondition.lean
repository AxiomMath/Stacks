module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.ZariskiGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One covering family per covering sieve is enough at the distinguished objects

A presheaf on a site satisfies the sheaf condition for *every* covering sieve of a distinguished
object as soon as it satisfies it for *one* covering family contained in each such sieve, provided
the distinguished objects carry a covering family of every object for which the presheaf is
separated.  Separatedness is the only part of the condition that has to be known away from the
distinguished objects, and it is strictly weaker than the sheaf condition.

The reduction has two halves, which are independent of each other and are stated separately.
Separatedness for an arbitrary covering sieve of an arbitrary object follows from separatedness
for the covering sieves of the distinguished objects, because two sections over an object agree
as soon as they agree over the members of a family of distinguished objects, and over a
distinguished object they amalgamate one family for a covering sieve.  Given that, the sheaf
condition for a covering sieve follows from the sheaf condition for a covering family contained
in it: an amalgamation over the family is one over the whole sieve because the two agree after
restriction along the arrows of the pulled-back family, which is a covering sieve, and
separatedness applies there.

For a slice of the associated fppf site of a category fibred in groupoids this turns the affine
hypothesis of `AlgebraicGeometry.FibredSite.isSheaf_over_of_isSheafFor_affine_of_exists_isSheafFor`
— the sheaf condition for every covering sieve of every affine object — into the sheaf condition
for one covering family of affine objects inside each such sieve, which is the form in which a
covering of an affine object is verified: a covering sieve of an affine object contains a finite
covering family of affine objects
(`AlgebraicGeometry.FibredSite.exists_finite_affine_ofArrows_le_over`), a finite family of affine
objects has an affine disjoint union
(`AlgebraicGeometry.FibredSite.nonempty_finiteDisjointUnion`), and the sheaf condition for a
covering by a single affine object is the one the Amitsur complex computes.  The hypothesis at the
non-affine objects is unchanged, and by
`CategoryTheory.Presheaf.not_isSheaf_of_isSheafFor_objects_eqFalse` it cannot be dropped.

## Main results

* `CategoryTheory.Presieve.IsSeparatedFor.of_le`: separatedness passes to a larger presieve.
* `CategoryTheory.Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le`: **separatedness for a
  covering sieve follows from separatedness for one family of arrows of it.**
* `CategoryTheory.Presheaf.isSeparatedFor_of_isSeparatedFor_objects`: **separatedness for every
  covering sieve of every object follows from separatedness for the covering sieves of a
  distinguished class of objects**, together with a family of distinguished objects over each
  object for which the presheaf is separated.
* `CategoryTheory.Presheaf.isSheafFor_of_exists_isSheafFor_le`: **the sheaf condition for a
  covering sieve follows from the sheaf condition for one covering family contained in it**, for a
  presheaf separated for every covering sieve.
* `AlgebraicGeometry.FibredSite.isSheafFor_affine_of_exists_isSheafFor_le`: **on a slice of the
  associated fppf site, the sheaf condition for every covering sieve of every affine object
  follows from the sheaf condition for one covering family of affine objects inside each such
  sieve**, together with the hypothesis at the non-affine objects.
* `AlgebraicGeometry.FibredSite.isSheaf_over_of_exists_isSheafFor_le`: **the resulting sheaf
  criterion**, which asks at an affine object only for one covering family per covering sieve.

## Implementation notes

The family of distinguished objects over each object is not asked to be covering in
`CategoryTheory.Presheaf.isSeparatedFor_of_isSeparatedFor_objects`: separatedness of the presheaf
for it already forces two sections which agree over its members to be equal, and the covering
sieves that enter the argument are the pullbacks of the given one along the members, which cover
by stability under pullback.  In the geometric application the family is covering anyway.

The index universe of the families is free in the site-level statements and is the universe of
the chosen covering families of the fppf site in the geometric ones, which is where the family of
affine objects over a non-affine object comes from.  A family indexed by a finite type is used
there at `ULift` of its index type, exactly as in
`AlgebraicGeometry.FibredSite.nonempty_finiteDisjointUnion`.

Both halves of the reduction are about a presheaf of types; the statements for a presheaf with
values in an arbitrary category are obtained by testing against each object of the target, which
is what the sheaf condition for such a presheaf means, and so no separate proof is needed.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v₂ u₂ v u

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {X : C} {P : Cᵒᵖ ⥤ Type w}

/-- **Separatedness passes to a larger presieve.**  Two amalgamations of a family for the larger
presieve are amalgamations of its restriction to the smaller one. -/
theorem IsSeparatedFor.of_le {R R' : Presieve X} (hR : IsSeparatedFor P R) (hle : R ≤ R') :
    IsSeparatedFor P R' := fun y t₁ t₂ ht₁ ht₂ =>
  hR (y.restrict hle) t₁ t₂ (isAmalgamation_restrict hle y t₁ ht₁)
    (isAmalgamation_restrict hle y t₂ ht₂)

end CategoryTheory.Presieve

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w)

/-- **Separatedness for a covering sieve follows from separatedness for one family of arrows of
it.**  The arrows of the family belong to the sieve, so the presieve they form is contained in it
and `CategoryTheory.Presieve.IsSeparatedFor.of_le` applies; nothing about the topology is used. -/
@[sga "3 IV 6.2.3" "partial"]
theorem isSeparatedFor_of_exists_isSeparatedFor_le {X : C} (T : Sieve X) {I : Type w'}
    {Y : I → C} (g : ∀ i, Y i ⟶ X) (hgT : ∀ i, T (g i))
    (hg : Presieve.IsSeparatedFor P (Presieve.ofArrows Y g)) :
    Presieve.IsSeparatedFor P (T : Presieve X) :=
  hg.of_le (by rintro Z f ⟨i⟩; exact hgT i)

/-- **A presheaf separated for every covering sieve of every object of a distinguished class is
separated for every covering sieve of every object**, provided every object carries a family of
distinguished objects for which the presheaf is separated.

Two amalgamations of a family for the given sieve agree after restriction to a member of the
chosen family, because there they are two amalgamations of one family for a covering sieve of a
distinguished object — the pullback of the given sieve, which covers by stability under pullback;
and the chosen family is separating.  This is the separatedness half of
`CategoryTheory.Presheaf.isSheaf_of_isSheafFor_objects` with both hypotheses weakened from the
sheaf condition to separatedness, which is all its proof uses. -/
theorem isSeparatedFor_of_isSeparatedFor_objects (Q : C → Prop)
    (hQ : ∀ ⦃V : C⦄, Q V → ∀ T : Sieve V, T ∈ J V → Presieve.IsSeparatedFor P (T : Presieve V))
    (hcov : ∀ X : C, ∃ (I : Type w') (Y : I → C) (g : ∀ i, Y i ⟶ X),
      (∀ i, Q (Y i)) ∧ Presieve.IsSeparatedFor P (Presieve.ofArrows Y g))
    {X : C} (T : Sieve X) (hT : T ∈ J X) :
    Presieve.IsSeparatedFor P (T : Presieve X) := by
  obtain ⟨I, Y, g, hQY, hsh⟩ := hcov X
  intro y t₁ t₂ ht₁ ht₂
  refine hsh.ext ?_
  rintro Z f ⟨i⟩
  have hpb : ∀ t, y.IsAmalgamation t →
      (y.pullback (g i)).IsAmalgamation (P.map (g i).op t) := fun t ht V d hd => by
    simpa [Presieve.FamilyOfElements.pullback] using ht (d ≫ g i) hd
  exact hQ (hQY i) (T.pullback (g i)) (J.pullback_stable _ hT) _ _ _ (hpb _ ht₁) (hpb _ ht₂)

/-- **The sheaf condition for a covering sieve follows from the sheaf condition for one covering
family contained in it**, for a presheaf separated for every covering sieve.

The family generates a subsieve of the given one, for which the presheaf is a sheaf, and the
pullback of that subsieve along an arrow of the given sieve covers its source, so the presheaf is
separated for it; `CategoryTheory.Presieve.isSheafFor_subsieve_aux` assembles the two.  No fibre
products are needed: the pullback of a *sieve* is a sieve, and it covers by stability of the
topology under pullback. -/
@[sga "3 IV 6.2.3" "partial"]
theorem isSheafFor_of_exists_isSheafFor_le
    (hsep : ∀ ⦃Z : C⦄ (T : Sieve Z), T ∈ J Z → Presieve.IsSeparatedFor P (T : Presieve Z))
    {X : C} (T : Sieve X) {I : Type w'} {Y : I → C} (g : ∀ i, Y i ⟶ X) (hgT : ∀ i, T (g i))
    (hgcov : Sieve.ofArrows Y g ∈ J X)
    (hg : Presieve.IsSheafFor P (Presieve.ofArrows Y g)) :
    Presieve.IsSheafFor P (T : Presieve X) := by
  refine Presieve.isSheafFor_subsieve_aux P (S := Sieve.ofArrows Y g) ?_
    ((Presieve.isSheafFor_iff_generate _).1 hg)
    fun {_} f _ => hsep _ (J.pullback_stable f hgcov)
  intro Z f hf
  rw [Sieve.mem_ofArrows_iff] at hf
  obtain ⟨i, b, rfl⟩ := hf
  exact T.downward_closed (hgT i) b

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  {A : Type u₂} [Category.{v₂} A]

/-- **On a slice of the associated fppf site, the sheaf condition for every covering sieve of
every affine object follows from the sheaf condition for one covering family of affine objects
inside each such sieve**, together with one covering family of affine objects at each non-affine
object.

This is the affine hypothesis of
`AlgebraicGeometry.FibredSite.isSheaf_over_of_isSheafFor_affine_of_exists_isSheafFor` reduced to
the form in which a covering of an affine object is verified.  Separatedness for an arbitrary
covering sieve of an arbitrary object of the slice is assembled from the two hypotheses by
`CategoryTheory.Presheaf.isSeparatedFor_of_isSeparatedFor_objects`, the affine objects being the
distinguished class and the separating family at an affine object coming from the given family
inside the maximal sieve; `CategoryTheory.Presheaf.isSheafFor_of_exists_isSheafFor_le` then
upgrades the sheaf condition for the given family to the sheaf condition for the whole sieve.

Neither step uses the fibre products of the slice, so the structure functor is not asked to be
fibred in groupoids here; that hypothesis enters only in
`AlgebraicGeometry.FibredSite.isSheaf_over_of_exists_isSheafFor_le`, where the amalgamation at a
non-affine object is glued. -/
theorem isSheafFor_affine_of_exists_isSheafFor_le (x : 𝒳)
    (F : (Over x)ᵒᵖ ⥤ A)
    (haff : ∀ W : Over x, IsAffineOver B S hS (p.obj W.left) → ∀ T : Sieve W,
      T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
      ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
        (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧ (∀ j, T (a j)) ∧
          Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W ∧
            ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a))
    (hnonaff : ∀ W : Over x, ¬ IsAffineOver B S hS (p.obj W.left) →
      ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
        (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧
          Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W ∧
            ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a)) :
    ∀ W : Over x, IsAffineOver B S hS (p.obj W.left) → ∀ T : Sieve W,
      T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
      ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (T : Presieve W) := by
  intro W hW T hT M
  have hQ : ∀ ⦃V : Over x⦄, IsAffineOver B S hS (p.obj V.left) → ∀ U : Sieve V,
      U ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) V →
      Presieve.IsSeparatedFor (F ⋙ coyoneda.obj (op M)) (U : Presieve V) := by
    intro V hV U hU
    obtain ⟨_, _, a, -, haU, -, hsh⟩ := haff V hV U hU
    exact Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le _ U a haU (hsh M).isSeparatedFor
  have hcov : ∀ V : Over x, ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ V),
      (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧
        Presieve.IsSeparatedFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a) := by
    intro V
    by_cases hV : IsAffineOver B S hS (p.obj V.left)
    · obtain ⟨I, Y, a, hYaff, -, -, hsh⟩ := haff V hV ⊤
        (((BigFppfOver.associatedTopology B S hS p .fppf).over x).top_mem V)
      exact ⟨I, Y, a, hYaff, (hsh M).isSeparatedFor⟩
    · obtain ⟨I, Y, a, hYaff, -, hsh⟩ := hnonaff V hV
      exact ⟨I, Y, a, hYaff, (hsh M).isSeparatedFor⟩
  obtain ⟨_, _, a, -, haT, hacov, hsh⟩ := haff W hW T hT
  exact Presheaf.isSheafFor_of_exists_isSheafFor_le _ _
    (fun {Z} U hU => Presheaf.isSeparatedFor_of_isSeparatedFor_objects.{u + 1} _ _
      (fun V : Over x => IsAffineOver B S hS (p.obj V.left)) hQ hcov U hU)
    T a haT hacov (hsh M)

/-- **A presheaf on a slice of the associated fppf site which satisfies the sheaf condition for
one covering family of affine objects inside every covering sieve of every affine object, and for
one covering family of affine objects of every non-affine object, is a sheaf.**

This is `AlgebraicGeometry.FibredSite.isSheaf_over_of_isSheafFor_affine_of_exists_isSheafFor` with
its affine hypothesis replaced by the weaker one of
`AlgebraicGeometry.FibredSite.isSheafFor_affine_of_exists_isSheafFor_le`.  The hypothesis at the
non-affine objects is unchanged, and by
`CategoryTheory.Presheaf.not_isSheaf_of_isSheafFor_objects_eqFalse` it cannot be dropped. -/
theorem isSheaf_over_of_exists_isSheafFor_le (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : (Over x)ᵒᵖ ⥤ A)
    (haff : ∀ W : Over x, IsAffineOver B S hS (p.obj W.left) → ∀ T : Sieve W,
      T ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W →
      ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
        (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧ (∀ j, T (a j)) ∧
          Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W ∧
            ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a))
    (hnonaff : ∀ W : Over x, ¬ IsAffineOver B S hS (p.obj W.left) →
      ∃ (I : Type (u + 1)) (Y : I → Over x) (a : ∀ j, Y j ⟶ W),
        (∀ j, IsAffineOver B S hS (p.obj (Y j).left)) ∧
          Sieve.ofArrows Y a ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W ∧
            ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) (Presieve.ofArrows Y a)) :
    Presheaf.IsSheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) F :=
  isSheaf_over_of_isSheafFor_affine_of_exists_isSheafFor B S hS p hp x F
    (isSheafFor_affine_of_exists_isSheafFor_le B S hS p x F haff hnonaff) hnonaff

end AlgebraicGeometry.FibredSite

end
