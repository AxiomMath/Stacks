module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitCoprojections

/-!
# The termwise colimit as a derived colimit datum with its canonical coprojections

Let `A` be an abelian category in which colimits over `ℕ` exist and are exact and let
`L : ℕ ⥤ CochainComplex A ℤ` be a system of complexes of `A`. [Stacks, Tag 0949]
(`DerivedCategory.isHomotopyColimit_Q_obj_colimit`) says that `Q(colim Lₙ)` is a derived colimit
of the system `L ⋙ Q` in `D(A)`, and `DerivedCategory.isHomotopyColimitWith_Q_obj_colimit` that
its coprojections may be taken to be the images `Q(ιₙ)` of the coprojections of the termwise
colimit. This file restates the latter in the form of a derived colimit datum
([Stacks, Tag 0CRH], `CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections`), whose
second map is `Sigma.desc` of the coprojections and whose third map is named.

## Main results

* `DerivedCategory.isHomotopyColimitWithCoprojections_Q_obj_colimit`: `Q(colim Lₙ)` carries a
  derived colimit datum for `L ⋙ Q` with coprojections `Q(ιₙ)`.

## Implementation notes

The two predicates differ only in how the second map of the defining triangle is recorded:
`IsHomotopyColimitWith` gives a map `p : ∐ Q(Lₙ) ⟶ Q(colim Lₙ)` restricting to `Q(ιₙ)` on the
`n`-th summand, and a map out of a coproduct is determined by its restrictions, so `p` is
`Sigma.desc` of the `Q(ιₙ)`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated

/-- **Stacks 0949 with the coprojections of the derived colimit named.** Let `A` be an abelian
category in which colimits over `ℕ` exist and are exact and let `L : ℕ ⥤ CochainComplex A ℤ` be a
system of complexes of `A`. Then the image under `Q : CochainComplex A ℤ ⥤ D(A)` of the termwise
colimit `colimit L` carries a derived colimit datum ([Stacks, Tag 0CRH],
`CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections`) for `L ⋙ Q` **whose
coprojections are the images `Q(ιₙ)` of the coprojections of the termwise colimit**.

`CategoryTheory.Pretriangulated.IsHomotopyColimit` quantifies the structural map of its Milnor
triangle away, so `DerivedCategory.isHomotopyColimit_Q_obj_colimit` — which is this statement
with the datum forgotten — says nothing about which cocone the presentation carries. Any
argument that has to compute a map out of a derived colimit, or the projections of the derived
limit it produces under a contravariant functor, needs that cocone named; and the point of the
statement below is that it may be taken to be the **canonical** one.

The defining triangle is the one of `DerivedCategory.isHomotopyColimitWith_Q_obj_colimit`, whose
second map restricts to `Q(ιₙ)` on the `n`-th summand and is therefore `Sigma.desc` of them. The
morphism `c` to the shifted direct sum is left existentially bound because a derived colimit
datum does not pin it and no consumer names it. -/
theorem DerivedCategory.isHomotopyColimitWithCoprojections_Q_obj_colimit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] (L : ℕ ⥤ CochainComplex A ℤ)
    [HasCoproduct (L ⋙ DerivedCategory.Q).obj] :
    ∃ c : DerivedCategory.Q.obj (colimit L) ⟶ (∐ (L ⋙ DerivedCategory.Q).obj)⟦(1 : ℤ)⟧,
      IsHomotopyColimitWithCoprojections (L ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (colimit L))
        (fun n => DerivedCategory.Q.map (colimit.ι L n)) c := by
  obtain ⟨p, q, hT, hp⟩ := DerivedCategory.isHomotopyColimitWith_Q_obj_colimit L
  obtain rfl : p = Sigma.desc (f := (L ⋙ DerivedCategory.Q).obj)
      fun n => DerivedCategory.Q.map (colimit.ι L n) :=
    Sigma.hom_ext _ _ fun n => by rw [Sigma.ι_desc]; exact hp n
  exact ⟨q, isHomotopyColimitWithCoprojections_of_distTriang _ _ hT⟩

end
