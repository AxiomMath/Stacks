module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FamilyRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase

/-!
# Descending a morphism of algebraic spaces along an extension of the ground field

Let `k ⊆ K` be an extension of fields whose spectra are objects of a big fppf site. Base change
of an algebraic space over `k` to one over `K` is restriction along the induced morphism of
spectra, `CategoryTheory.OverShriek.relocalizeRestrict`, which carries algebraic spaces to
algebraic spaces by [Stacks, Tag 03I5] part (1) and morphisms to morphisms because it is a
functor. This file proves that the functor is *faithful* on morphisms out of a reduced algebraic
space into one which is separated over the base, so that a morphism constructed over `K` and
pinned down by an equation descends to `k`.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_eq_univ_of_forall_mem`: a subfunctor of an
  algebraic space over `k` which contains every section over an object of the site whose
  structure morphism factors through `Spec K` carries every point of the space.
* `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_map_eq`: **two morphisms of algebraic spaces
  over `k` with reduced source and target separated over the base which agree after base change
  to `K` are equal.**
* `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_map_eq_of_isTerminal`: the same with the
  separatedness taken over a terminal object, which is the form in which a space separated over
  the ground field satisfies it.
* `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_fieldExtensionMap_eq`: the same for the
  morphism of spectra attached to a field extension `K/k`.

## Implementation notes

The source of the faithfulness is not a sheaf condition. For a general extension `K/k` the
morphism `Spec K ⟶ Spec k` is faithfully flat and quasi-compact but not locally of finite
presentation — a field which is a finitely generated algebra over `k` is a finite extension of
`k` — so `{Spec K ⟶ Spec k}` is not a covering of the big *fppf* site, and an algebraic space
is not known here to satisfy the fpqc sheaf condition: that is Gabber's [Stacks, Tag 0APL],
which this development carries as a hypothesis wherever it is needed. The argument used instead
is geometric, and is the one the source itself uses to compare two morphisms agreeing on a dense
part of the source:

* the agreement locus of the two morphisms carries *every* point of the source. A point of an
  algebraic space over `k` is represented by a section over the spectrum of a field `F`, and the
  agreement of the two morphisms after base change is agreement on every object of the site
  whose structure morphism factors through `Spec K`. Any `F` can be enlarged inside the site to
  a field containing both `F` and `K` — `AlgebraicGeometry.Space.exists_fieldExtension_common` —
  and the enlarged representative has the same class, so every point is carried;
* two morphisms into a space separated over the base which agree on a part of a *reduced* source
  whose point set is dense are equal, `AlgebraicGeometry.Space.eq_of_eq_on_dense`, which is
  [Stacks, Tag 084N] fed by [Stacks, Tag 03JJ]. Carrying every point is in particular carrying a
  dense set of them.

The middle step is exactly the surjectivity on points of the base change,
`AlgebraicGeometry.Space.surjective_pointsOfRelocalizeRestrict_fieldExtension`, which is already
available; it is applied to the representative, not to the morphism, which is why no hypothesis
beyond the two spectra lying in the site is needed and why the statements below take an
arbitrary morphism `Spec K ⟶ Spec k` of the site rather than one coming from an algebra
structure.

The passage from a section over an object of the site to a morphism of presheaves is the Yoneda
lemma, and it is what turns a pointwise coincidence into the global identity
`u ≫ a = u ≫ b` that `AlgebraicGeometry.Space.le_eqSubfunctor_iff` consumes.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- The section a morphism out of a representable presheaf is named by lies in the range of
that morphism: it is its value at the identity. -/
private theorem mem_range_yonedaEquiv_symm {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u} {V : C}
    (x : F.obj (op V)) :
    x ∈ (Subfunctor.range ((yonedaEquiv (X := V) (F := F)).symm x)).obj (op V) :=
  ⟨𝟙 V, by simp⟩

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (g : B.obj hK ⟶ B.obj hk)

/-- **A subfunctor detected after a field extension carries every point.** Let `X` be a presheaf
on the big fppf site over `Spec k` and let `W ⊆ X` be a subfunctor containing every section of
`X` over an object of the site whose structure morphism factors through `Spec K`. Then every
point of `X` is the image of a point of `W`.

A point of `X` is represented by a section over the spectrum of a field, and the representative
can be enlarged to one whose field contains `K`; the enlarged section then lies in `W`. -/
theorem range_pointsMap_ι_eq_univ_of_forall_mem
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (W : Subfunctor X)
    (hW : ∀ (V : BigFppfOver B (Spec (.of K)) hK) (x : X.obj (op ((Over.map g).obj V))),
      x ∈ W.obj (op ((Over.map g).obj V))) :
    Set.range (pointsMap B (Spec (.of k)) hk W.toFunctor W.ι) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  obtain ⟨z, hz⟩ := surjective_pointsOfRelocalizeRestrict_fieldExtension B k K hk hK g X y
  obtain ⟨q, rfl⟩ := Quot.exists_rep z
  refine ⟨({ carrier := q.carrier
             field := q.field
             contained := q.contained
             toBase := q.toBase ≫ B.inclusion.map g
             value := ⟨q.value, hW q.siteObject q.value⟩ } :
      FieldValuedPoint B (Spec (.of k)) hk W.toFunctor).class B (Spec (.of k)) hk W.toFunctor, ?_⟩
  exact hz

/-- **Two morphisms agreeing after a field extension are equal.** Let `a, b : X ⟶ Y` be morphisms
of algebraic spaces over a field `k` with `X` reduced and `Y` separated over `T` along `q`. If
the base changes of `a` and `b` along a morphism `Spec K ⟶ Spec k` of the site agree, then
`a = b`.

The hypothesis says that `a` and `b` agree on every object of the site factoring through
`Spec K`, so by `AlgebraicGeometry.Space.range_pointsMap_ι_eq_univ_of_forall_mem` their
agreement locus carries every point of `X`; being a dense part on which the two agree, it makes
them equal by `AlgebraicGeometry.Space.eq_of_eq_on_dense`. -/
theorem eq_of_relocalizeRestrict_map_eq
    {T X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B (Spec (.of k)) hk q)
    (a b : X ⟶ Y) (hab : a ≫ q = b ≫ q)
    (h : (OverShriek.relocalizeRestrict g).map a = (OverShriek.relocalizeRestrict g).map b) :
    a = b := by
  set E := eqSubfunctor B (Spec (.of k)) hk q a b hab with hE
  -- the two morphisms agree on every object of the site factoring through `Spec K`
  have hmem : ∀ (V : BigFppfOver B (Spec (.of K)) hK)
      (x : X.obj (op ((Over.map g).obj V))), x ∈ E.obj (op ((Over.map g).obj V)) := by
    intro V x
    -- the section `x`, read as a morphism out of the presheaf it represents
    have happ : a.app (op ((Over.map g).obj V)) = b.app (op ((Over.map g).obj V)) :=
      congrArg (fun t : (OverShriek.relocalizeRestrict g).obj X ⟶
        (OverShriek.relocalizeRestrict g).obj Y => t.app (op V)) h
    set s := (yonedaEquiv (X := (Over.map g).obj V) (F := X)).symm x with hs
    have hcomp : s ≫ a = s ≫ b := by
      refine (yonedaEquiv (X := (Over.map g).obj V) (F := Y)).injective ?_
      rw [yonedaEquiv_comp, yonedaEquiv_comp, hs, Equiv.apply_symm_apply]
      exact congrArg (fun f => f x) happ
    have hle : Subfunctor.range s ≤ E := by
      rw [hE, le_eqSubfunctor_iff]
      refine (cancel_epi (Subfunctor.toRange s)).mp ?_
      rw [← Category.assoc, ← Category.assoc, Subfunctor.toRange_ι]
      exact hcomp
    exact hle (op ((Over.map g).obj V)) (mem_range_yonedaEquiv_symm x)
  -- so the agreement locus carries every point of `X`, in particular a dense set of them
  have hrange := range_pointsMap_ι_eq_univ_of_forall_mem B k K hk hK g X E hmem
  exact eq_of_eq_on_dense B (Spec (.of k)) hk hT hX hY hXred q hq a b hab E
    (by rw [hrange]; exact dense_univ)
    ((le_eqSubfunctor_iff B (Spec (.of k)) hk q a b hab E).1 le_rfl)

/-- `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_map_eq` for a target separated over a
terminal object of presheaves, which is how an algebraic space separated over the ground field
presents itself. The compatibility of the two morphisms over the base is automatic there. -/
theorem eq_of_relocalizeRestrict_map_eq_of_isTerminal
    {T X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hTterm : IsTerminal T)
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B (Spec (.of k)) hk q)
    (a b : X ⟶ Y)
    (h : (OverShriek.relocalizeRestrict g).map a = (OverShriek.relocalizeRestrict g).map b) :
    a = b :=
  eq_of_relocalizeRestrict_map_eq B k K hk hK g hT hX hY hXred q hq a b
    (hTterm.hom_ext _ _) h

/-- `AlgebraicGeometry.Space.eq_of_relocalizeRestrict_map_eq` for the morphism of spectra
attached to a field extension `K/k`: two morphisms of algebraic spaces over `k` out of a reduced
space into one separated over the base whose base changes to `K` agree are equal. -/
theorem eq_of_relocalizeRestrict_fieldExtensionMap_eq [Algebra k K]
    {T X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B (Spec (.of k)) hk T)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (hXred : HasEtaleLocalProperty B (Spec (.of k)) hk X
      (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B (Spec (.of k)) hk q)
    (a b : X ⟶ Y) (hab : a ≫ q = b ≫ q)
    (h : (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map a =
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map b) :
    a = b :=
  eq_of_relocalizeRestrict_map_eq B k K hk hK (fieldExtensionMap B k K hk hK)
    hT hX hY hXred q hq a b hab h

end AlgebraicGeometry.Space

end
