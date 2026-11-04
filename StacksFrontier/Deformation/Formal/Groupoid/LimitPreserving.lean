module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.Groupoid.CofiberedCompletion

/-!
# Completion of a limit-preserving functor on complete local algebras

A complete local `Λ`-algebra is the limit of its Artinian truncations, so a functor on
complete local algebras that preserves limits is recovered from its restriction to Artinian
local algebras: the unit of the restriction--completion adjunction is an isomorphism at such
a functor. This gives the canonical comparison from the completion of the restriction back
to the functor.

## Main results

* `Deformation.cofiberedCompletionUnit_isIso`: the unit of the adjunction is an isomorphism
  at a limit-preserving functor.
* `Deformation.cofiberedCompletionRestrictionIso`: the resulting comparison from the
  completion of the restriction to the original functor.
* `Deformation.cofiberedCompletionRestrictionIso_inv`: its inverse is the unit.
* `Deformation.isRightKanExtension_restriction`: a limit-preserving functor is the right Kan
  extension of its restriction, for the identity comparison.

## Implementation notes

Bijectivity of a component of the unit is read off the limit cone of the Artinian
truncations: a compatible family of values is a cone with vertex a one-point type, and the
induced map out of that cone is the inverse. The value universe of the functor stays
independent of the hom-set universe of the categories of algebras, which is why this does
not reduce to `Deformation.adicCompletionRestrictionIso`.

`isRightKanExtension_restriction` is the same fact stated as a Kan extension property and
for an arbitrary value universe, unconstrained by the hom-set universe: a complete local
algebra is the limit of its own Artinian truncations, so a limit-preserving functor's value
on it is determined by its values on them, which is what the Kan extension condition
asserts. It is proved directly from the universal property of `adicQuotientCone`, so it does
not go through the completion functor and needs no relation between the universes.

## References

* [Stacks Project, Tag 06HE](https://stacks.math.columbia.edu/tag/06HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation

universe u v w z q

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The limit cone of the Artinian truncations is given by the canonical quotient maps. -/
private theorem adicQuotientCone_π_app (S : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (adicQuotientCone S).π.app (Opposite.op n) = quotientProjection S n := by
  apply CompleteLocalAlgCat.Hom.ext
  rfl

/-- A compatible family of values of a restricted functor on the Artinian truncations of `S`,
viewed as a cone with one-point vertex over the diagram of truncations. -/
private noncomputable def sectionCone
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (s : completedSections (artinianToComplete (Λ := Λ) (k := k) ⋙ G) S) :
    Cone (adicQuotientDiagram S ⋙ G) where
  pt := PUnit.{max v z + 1}
  π := {
    app := fun i => TypeCat.ofHom (fun _ : PUnit.{max v z + 1} => s.1 i.unop)
    naturality := fun _ _ f => TypeCat.Hom.ext <| TypeCat.Fun.ext <| funext fun _ =>
      (completedSections_eval_truncationMapLE
        (artinianToComplete (Λ := Λ) (k := k) ⋙ G) S s f.unop.le).symm }

/-- The value of the adjunction unit at a section index is the image of the element under
the corresponding quotient map. -/
private theorem unit_app_val
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : G.obj S) (n : ℕ) :
    ((((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G).app S) x).1 n =
      G.map ((adicQuotientCone S).π.app (Opposite.op n)) x := by
  rw [adicQuotientCone_π_app]
  rfl

/-- A limit-preserving functor preserves the limit cone of the Artinian truncations. -/
private noncomputable def isLimitMapAdicQuotientCone
    {G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) : IsLimit (G.mapCone (adicQuotientCone S)) :=
  letI := preservesSmallestLimits_of_preservesLimits G
  isLimitOfPreserves G (adicQuotientConeIsLimit S)

/-- The map inverse to a component of the adjunction unit at a limit-preserving functor. -/
private noncomputable def unitInverse
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (s : completedSections (artinianToComplete (Λ := Λ) (k := k) ⋙ G) S) : G.obj S :=
  (isLimitMapAdicQuotientCone S).lift (sectionCone G S s) PUnit.unit

/-- The inverse map is a right inverse of the unit. -/
private theorem unit_unitInverse
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (s : completedSections (artinianToComplete (Λ := Λ) (k := k) ⋙ G) S) :
    (((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G).app S)
      (unitInverse G S s) = s := by
  refine Subtype.ext (funext fun n => ?_)
  have hcoord := congrArg (fun f => f PUnit.unit)
    ((isLimitMapAdicQuotientCone S).fac (sectionCone G S s) (Opposite.op n))
  change G.map ((adicQuotientCone S).π.app (Opposite.op n))
      (unitInverse G S s) = s.1 n at hcoord
  exact (unit_app_val G S (unitInverse G S s) n).trans hcoord

/-- The inverse map is a left inverse of the unit. -/
private theorem unitInverse_unit
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : G.obj S) :
    unitInverse G S
      ((((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G).app S) x) = x := by
  let c := sectionCone G S
    ((((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G).app S) x)
  let m : PUnit.{max v z + 1} ⟶ G.obj S := TypeCat.ofHom (fun _ => x)
  have hm : ∀ j, m ≫ (G.mapCone (adicQuotientCone S)).π.app j = c.π.app j := fun j =>
    TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun _ => (unit_app_val G S x j.unop).symm))
  exact (congrArg (fun f => f PUnit.unit)
    ((isLimitMapAdicQuotientCone S).uniq c m hm)).symm

/-- The unit of the completion--restriction adjunction is an isomorphism at a
limit-preserving functor. -/
public theorem cofiberedCompletionUnit_isIso
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G] :
    IsIso ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro S
  rw [CategoryTheory.isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · intro x y h
    exact (unitInverse_unit G S x).symm.trans
      ((congrArg (unitInverse G S) h).trans (unitInverse_unit G S y))
  · intro s
    exact ⟨unitInverse G S s, unit_unitInverse G S s⟩

/-- The canonical comparison from the completion of the restriction of a limit-preserving
functor to the functor itself. -/
public noncomputable def cofiberedCompletionRestrictionIso
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G] :
    cofiberedCompletion.obj (artinianToComplete (Λ := Λ) (k := k) ⋙ G) ≅ G := by
  letI := cofiberedCompletionUnit_isIso G
  exact (asIso ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G)).symm

/-- The inverse of the comparison is the unit of the completion--restriction adjunction. -/
@[simp]
public theorem cofiberedCompletionRestrictionIso_inv
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)) [PreservesLimits G] :
    (cofiberedCompletionRestrictionIso G).inv =
      (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app G := rfl

section KanExtension

open CategoryTheory.Functor

/- `adicQuotientDiagram` is a plain `def`, so `(adicQuotientDiagram S).obj j` and
`artinianToComplete.obj (AdicTruncation.obj S j.unop)` are definitionally equal and not
syntactically so, and every goal below that composes a map of the diagram with a component
of `α` is ill-typed at the `implicit` transparency level. The local attribute below makes the
two spellings visible to the unifier, which is all a transparency option would buy. -/
attribute [local implicit_reducible] adicQuotientDiagram adicQuotientCone

/-- The projection from a complete local algebra onto the level-`j` term of its diagram of
Artinian truncations. Its declared type names `S` itself rather than the vertex of
`adicQuotientCone`; the two are definitionally equal but not syntactically so, and every
goal below is ill-typed at the `implicit` transparency level in the second spelling. -/
private noncomputable abbrev adicProj (S : CompleteLocalAlgCat.{u, v, w} Λ k) (j : ℕᵒᵖ) :
    S ⟶ (adicQuotientDiagram S).obj j :=
  (adicQuotientCone S).π.app j

/-- The projections `adicProj` form a cone over the diagram of Artinian truncations. -/
private theorem adicProj_w {S : CompleteLocalAlgCat.{u, v, w} Λ k} {i j : ℕᵒᵖ} (f : i ⟶ j) :
    adicProj S i ≫ (adicQuotientDiagram S).map f = adicProj S j :=
  (adicQuotientCone S).w f

/-- The projections `adicProj` are natural in the complete local algebra. -/
private theorem adicProj_naturality {S T : CompleteLocalAlgCat.{u, v, w} Λ k} (f : S ⟶ T)
    (n : ℕ) :
    adicProj S (Opposite.op n) ≫ artinianToComplete.map (AdicTruncation.map f n) =
      f ≫ adicProj T (Opposite.op n) :=
  adicQuotientCone_naturality f n

/-- The cone, with vertex the value of `H` at `S`, that the universal property of the limit
of the Artinian truncations lifts a map of restrictions against. -/
private noncomputable def restrictionLiftCone
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q}
    (α : artinianToComplete ⋙ H ⟶ artinianToComplete ⋙ G)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) : Cone (adicQuotientDiagram S ⋙ G) where
  pt := H.obj S
  π := {
    app := fun j => H.map (adicProj S j) ≫
      α.app (AdicTruncation.obj S j.unop)
    naturality := by
      intro i j f
      have hn := α.naturality (truncationMapLE S f.unop.le)
      change H.map ((adicQuotientDiagram S).map f) ≫
          α.app (AdicTruncation.obj S j.unop) =
        α.app (AdicTruncation.obj S i.unop) ≫ G.map ((adicQuotientDiagram S).map f) at hn
      change 𝟙 (H.obj S) ≫ H.map (adicProj S j) ≫ α.app (AdicTruncation.obj S j.unop) =
        (H.map (adicProj S i) ≫ α.app (AdicTruncation.obj S i.unop)) ≫
          G.map ((adicQuotientDiagram S).map f)
      exact (Category.id_comp _).trans
        ((congrArg (· ≫ α.app (AdicTruncation.obj S j.unop))
            (((H.map_comp (adicProj S i) ((adicQuotientDiagram S).map f)).symm.trans
              (congrArg H.map (adicProj_w f))).symm)).trans
          (((Category.assoc _ _ _).trans
            (congrArg (H.map (adicProj S i) ≫ ·) hn)).trans
              (Category.assoc _ _ _).symm)) }

/-- The component at `S` of the lift of a map of restrictions along a limit-preserving
functor. -/
private noncomputable def restrictionLiftApp
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (α : artinianToComplete ⋙ H ⟶ artinianToComplete ⋙ G)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) : H.obj S ⟶ G.obj S :=
  (isLimitMapAdicQuotientCone S).lift (restrictionLiftCone α S)

/-- The defining factorisation of `restrictionLiftApp` through a level projection. -/
private theorem restrictionLiftApp_fac
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (α : artinianToComplete ⋙ H ⟶ artinianToComplete ⋙ G)
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    restrictionLiftApp α S ≫ G.map (adicProj S (Opposite.op n)) =
      H.map (adicProj S (Opposite.op n)) ≫
        α.app (AdicTruncation.obj S n) := by
  exact (isLimitMapAdicQuotientCone S).fac (restrictionLiftCone α S) (Opposite.op n)

/-- The lift of a map of restrictions to a map into a limit-preserving functor. -/
private noncomputable def restrictionLift
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (α : artinianToComplete ⋙ H ⟶ artinianToComplete ⋙ G) : H ⟶ G where
  app := restrictionLiftApp α
  naturality := by
    intro S T f
    apply (isLimitMapAdicQuotientCone (G := G) T).hom_ext
    intro j
    change (H.map f ≫ restrictionLiftApp α T) ≫ G.map (adicProj T (Opposite.op j.unop)) =
      (restrictionLiftApp α S ≫ G.map f) ≫ G.map (adicProj T (Opposite.op j.unop))
    have hn := α.naturality (AdicTruncation.map f j.unop)
    change H.map (artinianToComplete.map (AdicTruncation.map f j.unop)) ≫ _ =
      _ ≫ G.map (artinianToComplete.map (AdicTruncation.map f j.unop)) at hn
    rw [Category.assoc, restrictionLiftApp_fac, Category.assoc, ← G.map_comp,
      ← adicProj_naturality f j.unop, G.map_comp, ← Category.assoc (restrictionLiftApp α S),
      restrictionLiftApp_fac, Category.assoc,
      ← hn]
    change H.map f ≫ H.map _ ≫ _ = (H.map _ ≫ H.map _) ≫ _
    rw [← Category.assoc, ← H.map_comp, ← H.map_comp, adicQuotientCone_naturality]

/-- The lift restricts back to the map it was built from. -/
private theorem restrictionLift_restrict
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (α : artinianToComplete ⋙ H ⟶ artinianToComplete ⋙ G) :
    whiskerLeft artinianToComplete (restrictionLift α) = α := by
  apply NatTrans.ext
  funext A
  apply (isLimitMapAdicQuotientCone (G := G) (artinianToComplete.obj A)).hom_ext
  intro j
  change restrictionLiftApp α (artinianToComplete.obj A) ≫
      G.map (adicProj (artinianToComplete.obj A) (Opposite.op j.unop)) =
    α.app A ≫ G.map (adicProj (artinianToComplete.obj A) (Opposite.op j.unop))
  rw [restrictionLiftApp_fac]
  let f := artinianAdicQuotient A j.unop
  exact α.naturality f

/-- Two maps into a limit-preserving functor that restrict to the same map are equal. -/
private theorem restriction_hom_ext
    {H G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q} [PreservesLimits G]
    (α β : H ⟶ G)
    (h : whiskerLeft artinianToComplete α =
      whiskerLeft artinianToComplete β) : α = β := by
  refine NatTrans.ext (funext fun S => ?_)
  refine (isLimitMapAdicQuotientCone (G := G) S).hom_ext fun j => ?_
  change α.app S ≫ G.map (adicProj S (Opposite.op j.unop)) =
    β.app S ≫ G.map (adicProj S (Opposite.op j.unop))
  rw [← α.naturality, ← β.naturality]
  exact congrArg (H.map (adicProj S j) ≫ ·)
    (NatTrans.congr_app h (AdicTruncation.obj S j.unop))

/-- A limit-preserving functor is the right Kan extension of its restriction. -/
public theorem isRightKanExtension_restriction
    (G : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type q) [PreservesLimits G] :
    G.IsRightKanExtension (𝟙 (artinianToComplete ⋙ G)) := by
  refine ⟨⟨IsTerminal.ofUniqueHom (fun e =>
    CostructuredArrow.homMk (restrictionLift (G := G) e.hom) ?_) ?_⟩⟩
  · simpa using restrictionLift_restrict e.hom
  · intro e f
    apply CostructuredArrow.hom_ext
    apply restriction_hom_ext (G := G)
    change whiskerLeft artinianToComplete f.left =
      whiskerLeft artinianToComplete (restrictionLift e.hom)
    rw [restrictionLift_restrict]
    simpa using f.w

end KanExtension

end Deformation
