module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Etale.Finite
public import StacksFrontier.Cotangent.EtaleVanishing
public import StacksFrontier.Cotangent.FilteredColimitVanishing
public import StacksFrontier.Cotangent.Triangle.VanishingVertex
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

/-!
# The cotangent complex of a henselization

Let `(R, 𝔪, κ)` be a local ring and let `R → Rh` be a henselization of `R` with residue field a
prescribed extension `κ ⊆ L`, in the sense of `IsLocalRing.IsHenselization`. A henselization is
an ind-étale `R`-algebra, so the vanishing of `L_{P/R}` for `P` étale over `R`
(item (5) of [Stacks, Tag 08R2]) and the compatibility of the cotangent complex with filtered
colimits (item (6) of the same lemma) give `L_{Rh/R} = 0`. At `L = κ` that is item (7) of
[Stacks, Tag 08R2] and at `L = κ^sep` it is item (8).

## Main definitions

* `CommAlgCat.HasEtaleDiagonalTriangle`: the family of instances of Proposition 08QX that item
  (5) of [Stacks, Tag 08R2] consumes, one for the diagonal tower `P → P ⊗_R P → P` of each
  étale `R`-algebra `P`.

## Main results

* `CommAlgCat.isZero_cotangentComplexDerived_of_bijective_square`: the vanishing of `L_{B/A}`
  only depends on the pair `A → B` up to isomorphism.
* `CommAlgCat.isZero_cotangentComplexDerived_of_ind_etale`: the relative cotangent complex of an
  ind-étale algebra vanishes.
* `IsLocalRing.IsHenselization.isZero_cotangentComplexDerived`: items (7) and (8) of
  [Stacks, Tag 08R2], `L_{R^h/R} = 0` and `L_{R^{sh}/R} = 0`, for a given family of diagonal
  triangles. The form with nothing carried is
  `IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional` in
  `StacksFrontier.Cotangent.HenselizationUnconditional`.

## Implementation notes

*Why Proposition 08QX appears as a family.* Item (5) of [Stacks, Tag 08R2],
`CommAlgCat.isZero_cotangentComplexDerived_of_etale`, takes the distinguished triangle of
Proposition 08QX for the diagonal tower `P → P ⊗_R P → P` as a parameter, because this file is
upstream of Proposition 08QX (`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`). The route to items (7) and (8) applies item
(5) at every étale stage of a presentation of `Rh` as a filtered colimit, and the index category
of that presentation is produced by the existential statement `CategoryTheory.ObjectProperty.ind`
inside the proof, so it cannot appear in the statement. The parameter is therefore quantified
over the étale algebras rather than over the stages: `CommAlgCat.HasEtaleDiagonalTriangle R`.
That is exactly the instance of Proposition 08QX item (5) needs, at every ring where the proof
needs it, and nothing more. `CommAlgCat.hasEtaleDiagonalTriangle` of
`StacksFrontier.Cotangent.HenselizationUnconditional` proves it for every ring from Proposition
08QX.

*The forgetful functor to rings.* `IsLocalRing.IsHenselization.ind_etale` presents a
henselization as a filtered colimit in `CommAlgCat R`, whereas item (6)
(`CommAlgCat.cotangentComplex_isZero_of_filtered_colimit`) is stated for a system in
`CommRingCat`. The bridge is
`CommAlgCat.preservesColimitsOfShape_forget₂CommRingCat`: the equivalence
`CategoryTheory.commAlgCatEquivUnder` identifies `CommAlgCat R` with `Under (CommRingCat.of R)`,
whose forgetful functor preserves filtered colimits.

*Invariance under isomorphism.* Item (6) concludes about the chosen colimits
`colimit A → colimit B`, which for the system at hand are isomorphic to, but not equal to,
`R → Rh`. `CommAlgCat.isZero_cotangentComplexDerived_of_bijective_square` moves the conclusion
across such an isomorphism. It is obtained from the degreewise colimit statement of
[Stacks, Tag 08S9] (`CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb`) applied to the
*constant* system on `A → B`: for a constant system whose transition maps are the identity, the
assertion that the comparison maps exhibit the target as the colimit is precisely the assertion
that they are bijective, so the induced map of complexes of abelian groups is an isomorphism in
every degree, and acyclicity transfers. The same lemma also reconciles the `Algebra` instance
`CommAlgCat.of` carries with the one item (6) builds from the underlying ring map.

## References

* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), items (5) to (8).
* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9), the compatibility with
  filtered colimits.
* [Stacks Project, Tag 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the definition of the
  henselization and of a strict henselization.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle, taken here as a parameter and supplied in
  `StacksFrontier.Cotangent.HenselizationUnconditional`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

/-- **Forgetting the algebra structure preserves filtered colimits of algebras.** The
equivalence `CategoryTheory.commAlgCatEquivUnder` identifies `CommAlgCat A` with
`Under (CommRingCat.of A)`, and the forgetful functor of an under category preserves filtered
colimits. -/
theorem preservesColimitsOfShape_forget₂CommRingCat (A : Type u) [CommRing A] (J : Type u)
    [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} A) CommRingCat) := by
  have : IsConnected J := IsFiltered.isConnected J
  change PreservesColimitsOfShape J
    ((commAlgCatEquivUnder (.of A)).functor ⋙ Under.forget (CommRingCat.of A))
  infer_instance

section Invariance

variable {A A' : Type u} [CommRing A] [CommRing A'] {B : CommAlgCat.{u} A}
  {B' : CommAlgCat.{u} A'}

/-- A bijection, with identity transitions, exhibits its target as the colimit of the constant
system on its source. -/
private theorem isDirectedColimitOfTypes_of_bijective {X Y : Type u} (g : X → Y)
    (hg : Function.Bijective g) :
    IsDirectedColimitOfTypes (I := ℕ) (fun (_ _ : ℕ) (_ : _ ≤ _) (x : X) => x) (fun _ => g) :=
  { map_id := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ _ => rfl
    comp := fun _ _ _ _ => rfl
    jointly_surjective := fun y => by
      obtain ⟨x, hx⟩ := hg.surjective y
      exact ⟨0, x, hx⟩
    exists_eq := fun i _ _ hab => ⟨i, le_rfl, hg.injective hab⟩ }

/-- **The vanishing of `L_{B/A}` depends only on the pair `A → B` up to isomorphism.** Let
`A → B` and `A' → B'` be ring maps and let a commutative square between them have bijective
horizontal maps. If `L_{B/A} = 0` in `D(B)` then `L_{B'/A'} = 0` in `D(B')`.

The degreewise colimit statement of [Stacks, Tag 08S9] applied to the constant system on
`A → B` shows that the induced map `L_{B/A} → L_{B'/A'}` of complexes of abelian groups is
bijective in every degree; acyclicity then transfers along the resulting isomorphism. -/
theorem isZero_cotangentComplexDerived_of_bijective_square
    (sq : AlgebraSquare.{u, u, u} A A' B B') (hbase : Function.Bijective sq.base)
    (hmap : Function.Bijective sq.map)
    (h : IsZero (cotangentComplexDerived.{u, u} A B)) :
    IsZero (cotangentComplexDerived.{u, u} A' B') := by
  have key := fun n : ℤ => isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, 0}
    (I := ℕ) (A := fun _ => A) (B := fun _ => B) (Ainf := A') (Binf := B')
    (fun _ _ _ => AlgebraSquare.id.{u, u} A B) (fun _ => sq)
    (isDirectedColimitOfTypes_of_bijective _ hbase)
    (isDirectedColimitOfTypes_of_bijective _ hmap) n
  have hbij : ∀ n : ℤ, Function.Bijective ((cotangentComplexAbMap.{u, u, u} sq).f n) := by
    intro n
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨j, hij, hj⟩ := (key n).exists_eq 0 x y hxy
      exact ((key n).map_id 0 x).symm.trans (hj.trans ((key n).map_id 0 y))
    · obtain ⟨_, a, ha⟩ := (key n).jointly_surjective z
      exact ⟨a, ha⟩
  have hcomp : ∀ n : ℤ, IsIso ((cotangentComplexAbMap.{u, u, u} sq).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij n)
  have hiso : IsIso (cotangentComplexAbMap.{u, u, u} sq) :=
    @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _
      (cotangentComplexAbMap.{u, u, u} sq) hcomp
  refine CochainComplex.isZero_Q_obj_of_acyclic _ fun n =>
    (CochainComplex.exactAt_forget₂_addCommGrp_iff _ n).1 ?_
  exact HomologicalComplex.ExactAt.of_iso
    ((CochainComplex.exactAt_forget₂_addCommGrp_iff _ n).2
      (CochainComplex.exactAt_of_isZero_Q _ n h))
    (@asIso _ _ _ _ (cotangentComplexAbMap.{u, u, u} sq) hiso)

end Invariance

section IndEtale

/-- **The family of instances of Proposition 08QX that item (5) of [Stacks, Tag 08R2]
consumes.** For each étale algebra `P` over `R`, the three vertices of the display 92.7.0.1 for
the diagonal tower `P → P ⊗_R P → P` form a distinguished triangle in `D(P)`.

This is the hypothesis `hT` of `CommAlgCat.isZero_cotangentComplexDerived_of_etale`, quantified
over the étale algebras because the étale stages at which item (5) is applied below are produced
inside the proof. See the module docstring. It holds for every ring:
`CommAlgCat.hasEtaleDiagonalTriangle`. -/
def HasEtaleDiagonalTriangle (R : Type u) [CommRing R] : Prop :=
  ∀ (P : Type u) [CommRing P] [Algebra R P], Algebra.Etale R P →
    ∃ (α : fundamentalVertex₁.{u, u} P (P ⊗[R] P) P ⟶ fundamentalVertex₂.{u, u} P P)
      (β : fundamentalVertex₂.{u, u} P P ⟶ fundamentalVertex₃.{u, u} (P ⊗[R] P) P)
      (γ : fundamentalVertex₃.{u, u} (P ⊗[R] P) P ⟶
        (fundamentalVertex₁.{u, u} P (P ⊗[R] P) P)⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} P))

variable {R : Type u} [CommRing R]

/-- **[Stacks, Tag 08R2] item (5)** for an object of `CommAlgCat R`, with the triangle of
Proposition 08QX taken from the family `CommAlgCat.HasEtaleDiagonalTriangle`. -/
theorem isZero_cotangentComplexDerived_of_etale_obj (hQX : HasEtaleDiagonalTriangle.{u} R)
    (P : CommAlgCat.{u} R) [Algebra.Etale R (P : Type u)] :
    IsZero (cotangentComplexDerived.{u, u} R P) := by
  obtain ⟨_, _, _, hT⟩ := hQX (P : Type u) inferInstance
  exact isZero_cotangentComplexDerived_of_etale R (P : Type u) hT

/-- **The relative cotangent complex of an ind-étale algebra vanishes.** If `S` is a filtered
colimit of étale `R`-algebras then `L_{S/R} = 0` in `D(S)`.

Item (5) of [Stacks, Tag 08R2] gives the vanishing at each étale stage and item (6) — the
compatibility of the cotangent complex with filtered colimits — passes it to the colimit. The
presentation is a colimit in `CommAlgCat R`, so
`CommAlgCat.preservesColimitsOfShape_forget₂CommRingCat` turns it into one in `CommRingCat`, and
`CommAlgCat.isZero_cotangentComplexDerived_of_bijective_square` moves the conclusion from the
chosen colimit of the system onto `R → S`. -/
theorem isZero_cotangentComplexDerived_of_ind_etale (hQX : HasEtaleDiagonalTriangle.{u} R)
    {S : CommAlgCat.{u} R} (hind : (CommAlgCat.etale.{u} R).ind.{u} S) :
    IsZero (cotangentComplexDerived.{u, u} R S) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  let Afun : J ⥤ CommRingCat.{u} := (Functor.const J).obj (CommRingCat.of R)
  let Bfun : J ⥤ CommRingCat.{u} := pres.diag ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat
  let f : Afun ⟶ Bfun :=
    { app := fun j => CommRingCat.ofHom (algebraMap R (pres.diag.obj j : Type u))
      naturality := fun i j g => by
        apply CommRingCat.hom_ext
        ext a
        exact ((pres.diag.map g).hom.commutes a).symm }
  have hstage : ∀ j : J,
      letI : Algebra (Afun.obj j : Type u) (Bfun.obj j : Type u) := (f.app j).hom.toAlgebra
      IsZero (DerivedCategory.Q.obj (cotangentComplex (Afun.obj j : Type u)
        (CommAlgCat.of (Afun.obj j : Type u) (Bfun.obj j : Type u)))) := by
    intro j
    have : Algebra.Etale R (pres.diag.obj j : Type u) := hpres j
    refine isZero_cotangentComplexDerived_of_bijective_square (A := R) (B := pres.diag.obj j)
      ⟨RingHom.id R, RingHom.id _, fun a => rfl⟩ Function.bijective_id Function.bijective_id
      (isZero_cotangentComplexDerived_of_etale_obj hQX (pres.diag.obj j))
  have hvan := cotangentComplex_isZero_of_filtered_colimit Afun Bfun f hstage
  have hforget : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat) :=
    preservesColimitsOfShape_forget₂CommRingCat R J
  have hconn : IsConnected J := IsFiltered.isConnected J
  have hcA : IsColimit (Cocone.mk (CommRingCat.of R) (𝟙 Afun)) := isColimitConstCocone J _
  have hcB : IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat).mapCocone pres.cocone) :=
    isColimitOfPreserves _ pres.isColimit
  have hA1 : ∀ j : J,
      colimit.ι Afun j ≫ ((colimit.isColimit Afun).coconePointUniqueUpToIso hcA).hom =
        𝟙 (CommRingCat.of R) :=
    fun j => IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Afun) hcA j
  have hB1 : ∀ j : J,
      colimit.ι Bfun j ≫ ((colimit.isColimit Bfun).coconePointUniqueUpToIso hcB).hom =
        (forget₂ (CommAlgCat.{u} R) CommRingCat).map (pres.ι.app j) :=
    fun j => IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Bfun) hcB j
  have hcomm : colim.map f ≫ ((colimit.isColimit Bfun).coconePointUniqueUpToIso hcB).hom =
      ((colimit.isColimit Afun).coconePointUniqueUpToIso hcA).hom ≫
        CommRingCat.ofHom (algebraMap R (S : Type u)) := by
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, ← colimMap_eq, ι_colimMap, Category.assoc, hB1 j]
    rw [← Category.assoc, hA1 j]
    apply CommRingCat.hom_ext
    ext a
    exact (pres.ι.app j).hom.commutes a
  exact isZero_cotangentComplexDerived_of_bijective_square
    ⟨((colimit.isColimit Afun).coconePointUniqueUpToIso hcA).hom.hom,
      ((colimit.isColimit Bfun).coconePointUniqueUpToIso hcB).hom.hom,
      fun a => ConcreteCategory.congr_hom hcomm a⟩
    ((ConcreteCategory.isIso_iff_bijective
      ((colimit.isColimit Afun).coconePointUniqueUpToIso hcA).hom).1 inferInstance)
    ((ConcreteCategory.isIso_iff_bijective
      ((colimit.isColimit Bfun).coconePointUniqueUpToIso hcB).hom).1 inferInstance) hvan

end IndEtale

end CommAlgCat

namespace IsLocalRing.IsHenselization

open CommAlgCat

/-- **[Stacks, Tag 08R2] items (7) and (8), for a given family of triangles.** Let `(R, 𝔪, κ)` be
a local ring and let `R → Rh` be a henselization of `R` with residue field a prescribed extension
`κ ⊆ L` of its residue field, and let `hQX` supply the diagonal triangles of the étale
`R`-algebras. Then `L_{Rh/R} = 0` in `D(Rh)`. The form with `hQX` discharged is
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional`.

At `L = κ` this is item (7), the henselization `R → R^h`, and at `L = κ^sep` a separable
algebraic closure it is item (8), a strict henselization `R → R^{sh}`; the two are the two
instances of `IsLocalRing.IsHenselization`, so one statement covers both.

The henselization hypothesis enters through `IsLocalRing.IsHenselization.ind_etale`: a
henselization is a filtered colimit of étale `R`-algebras, and
`CommAlgCat.isZero_cotangentComplexDerived_of_ind_etale` concludes. -/
theorem isZero_cotangentComplexDerived {R : Type u} [CommRing R] [IsLocalRing R] (L : Type v)
    [Field L] [Algebra (ResidueField R) L] {Rh : Type u} [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] [IsHenselization R L Rh] (hQX : HasEtaleDiagonalTriangle.{u} R) :
    IsZero (cotangentComplexDerived.{u, u} R (CommAlgCat.of R Rh)) :=
  isZero_cotangentComplexDerived_of_ind_etale hQX (ind_etale_of_universe_le.{u, v, u} L)

end IsLocalRing.IsHenselization

namespace CommAlgCat

open IsLocalRing

section Identification

variable (A : Type u) [CommRing A]

/-- **[Stacks, Tag 08UN], the identification over the henselized source.** Let `A → A^h` be a
henselization of the local ring `A` and let `C` be an `A^h`-algebra. Then
`L_{C/A} = L_{C/A^h}` in `D(C)`.

This is the first equality of the lemma, at `C = B^h`: the fundamental triangle of the tower
`A → A^h → C` has first vertex `L_{A^h/A} ⊗^𝐋_{A^h} C`, which vanishes because `L_{A^h/A} = 0`,
so its second arrow `L_{C/A} ⟶ L_{C/A^h}` is an isomorphism. Both the henselization `A^h` and a
strict henselization `A^{sh}` are instances of `IsLocalRing.IsHenselization`, so the statement
covers the lemma's `resp.` variant as well. -/
@[stacks 08UN "the FIRST of the lemma's two equalities, `L_{B^h/A^h} = L_{B^h/A}`, and its \
`resp.` strict variant `L_{B^{sh}/A^{sh}} = L_{B^{sh}/A}` — one statement for both, because the \
henselization and a strict henselization are the two instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). It is proved for an ARBITRARY `A^h`-algebra `C` in \
place of `B^h`, which is a generalization of the lemma and not a weakening of it. TWO carried \
hypotheses: `hT`, the distinguished triangle of Proposition 08QX for the tower `A → A^h → C`, \
which is not formalized in this library (see the `No @[stacks 08QX]` section of \
`StacksFrontier.Cotangent.Triangle.Distinguished`), and `hQX`, the family of instances of \
Proposition 08QX that items (7) and (8) of Stacks 08R2 consume. The source's input \
`L_{A^h/A} = 0` is NOT carried: it is proved here, as \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived`, which is what makes the \
henselization hypothesis on `A^h` load-bearing. The lemma's SECOND equality, \
`L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, is \
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization`"]
theorem nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization [IsLocalRing A]
    (L : Type v) [Field L] [Algebra (ResidueField A) L]
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [IsHenselization A L Ah]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra Ah C] [IsScalarTower A Ah C]
    (hQX : HasEtaleDiagonalTriangle.{u} A)
    {α : fundamentalVertex₁.{u, u} A Ah C ⟶ fundamentalVertex₂.{u, u} A C}
    {β : fundamentalVertex₂.{u, u} A C ⟶ fundamentalVertex₃.{u, u} Ah C}
    {γ : fundamentalVertex₃.{u, u} Ah C ⟶ (fundamentalVertex₁.{u, u} A Ah C)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} C))) :
    Nonempty (fundamentalVertex₂.{u, u} A C ≅ fundamentalVertex₃.{u, u} Ah C) :=
  have hzero : IsZero (fundamentalVertex₁.{u, u} A Ah C) :=
    Functor.map_isZero _ (IsHenselization.isZero_cotangentComplexDerived L hQX)
  have hβ : IsIso β := (Triangle.isZero₁_iff_isIso₂ _ hT).1 hzero
  ⟨@asIso _ _ _ _ β hβ⟩

/-- **[Stacks, Tag 08UN], the derived scalar-extension identification.** Let `A → B` be a ring
map, let `B → B^h` be a henselization of the local ring `B`, and let `A → B → B^h` be a tower.
Then `L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h` in `D(B^h)`.

This is the second equality of the lemma: the fundamental triangle of the tower `A → B → B^h`
has third vertex `L_{B^h/B}`, which vanishes because `B → B^h` is a henselization, so its first
arrow is an isomorphism. As above, one statement covers the lemma's `resp.` variant. -/
@[stacks 08UN "the SECOND of the lemma's two equalities, `L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, and \
its `resp.` strict variant `L_{B^{sh}/A} = L_{B/A} ⊗^𝐋_B B^{sh}` — one statement for both, the \
henselization and a strict henselization being the two instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). TWO carried hypotheses: `hT`, the distinguished \
triangle of Proposition 08QX for the tower `A → B → B^h`, not formalized in this library, and \
`hQX`, the family of instances of Proposition 08QX that items (7) and (8) of Stacks 08R2 \
consume. The source's input `L_{B^h/B} = 0` is NOT carried: it is proved here, as \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived`, so the henselization hypothesis \
on `B^h` is load-bearing. The lemma's FIRST equality, `L_{B^h/A^h} = L_{B^h/A}`, is \
`CommAlgCat.nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization`. NOTE that the \
local ring homomorphism `A → B` of the source is not assumed: the conclusion holds for any ring \
map `A → B` whose target is local, which is a generalization"]
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] (L : Type v) [Field L]
    [Algebra (ResidueField B) L]
    (Bh : Type u) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [IsHenselization B L Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] (hQX : HasEtaleDiagonalTriangle.{u} B)
    {α : fundamentalVertex₁.{u, u} A B Bh ⟶ fundamentalVertex₂.{u, u} A Bh}
    {β : fundamentalVertex₂.{u, u} A Bh ⟶ fundamentalVertex₃.{u, u} B Bh}
    {γ : fundamentalVertex₃.{u, u} B Bh ⟶ (fundamentalVertex₁.{u, u} A B Bh)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} Bh))) :
    Nonempty (fundamentalVertex₁.{u, u} A B Bh ≅ fundamentalVertex₂.{u, u} A Bh) :=
  nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero.{u, u} A B Bh hT
    (IsHenselization.isZero_cotangentComplexDerived L hQX)

/-- **[Stacks, Tag 08UN], the full chain.** Let `A → B` be a ring map of local rings, let
`A → A^h` and `B → B^h` be henselizations, and let `A^h → B^h` be compatible with them. Then
`L_{B^h/A^h} = L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h` in `D(B^h)`, read as an isomorphism
`L_{B/A} ⊗^𝐋_B B^h ≅ L_{B^h/A^h}`.

This composes the two identifications above. The `resp.` strict variant is the same statement
at `L_A = κ_A^sep` and `L_B = κ_B^sep`. -/
@[stacks 08UN "the lemma's full chain `L_{B^h/A^h} = L_{B^h/A} = L_{B/A} ⊗^𝐋_B B^h`, read as the \
isomorphism `L_{B/A} ⊗^𝐋_B B^h ≅ L_{B^h/A^h}` in `D(B^h)` obtained by composing the two \
equalities, together with its `resp.` strict variant — one statement for both, the henselization \
and a strict henselization being the instances `L = κ` and `L = κ^sep` of \
`IsLocalRing.IsHenselization` (Stacks 04GQ). The induced map `A^h → B^h` is taken as given data \
(an `A^h`-algebra structure on `B^h` with `IsScalarTower A A^h B^h`) rather than constructed. \
FOUR carried hypotheses: the two distinguished triangles `hT₁` and `hT₂` of Proposition 08QX, \
for the towers `A → B → B^h` and `A → A^h → B^h`, Proposition 08QX not being formalized in this \
library; and `hQXA`, `hQXB`, the families of instances of Proposition 08QX that items (7) and \
(8) of Stacks 08R2 consume over `A` and over `B`. The source's inputs `L_{A^h/A} = 0` and \
`L_{B^h/B} = 0` are NOT carried: both are proved, by \
`IsLocalRing.IsHenselization.isZero_cotangentComplexDerived`, so both henselization hypotheses \
are load-bearing"]
theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₃_henselization [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    (LA : Type v) [Field LA] [Algebra (ResidueField A) LA]
    (LB : Type w) [Field LB] [Algebra (ResidueField B) LB]
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [IsHenselization A LA Ah]
    (Bh : Type u) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [IsHenselization B LB Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] [Algebra Ah Bh] [IsScalarTower A Ah Bh]
    (hQXA : HasEtaleDiagonalTriangle.{u} A) (hQXB : HasEtaleDiagonalTriangle.{u} B)
    {α₁ : fundamentalVertex₁.{u, u} A B Bh ⟶ fundamentalVertex₂.{u, u} A Bh}
    {β₁ : fundamentalVertex₂.{u, u} A Bh ⟶ fundamentalVertex₃.{u, u} B Bh}
    {γ₁ : fundamentalVertex₃.{u, u} B Bh ⟶ (fundamentalVertex₁.{u, u} A B Bh)⟦(1 : ℤ)⟧}
    (hT₁ : Triangle.mk α₁ β₁ γ₁ ∈ distTriang (DerivedCategory (ModuleCat.{u} Bh)))
    {α₂ : fundamentalVertex₁.{u, u} A Ah Bh ⟶ fundamentalVertex₂.{u, u} A Bh}
    {β₂ : fundamentalVertex₂.{u, u} A Bh ⟶ fundamentalVertex₃.{u, u} Ah Bh}
    {γ₂ : fundamentalVertex₃.{u, u} Ah Bh ⟶ (fundamentalVertex₁.{u, u} A Ah Bh)⟦(1 : ℤ)⟧}
    (hT₂ : Triangle.mk α₂ β₂ γ₂ ∈ distTriang (DerivedCategory (ModuleCat.{u} Bh))) :
    Nonempty (fundamentalVertex₁.{u, u} A B Bh ≅ fundamentalVertex₃.{u, u} Ah Bh) := by
  obtain ⟨e₁⟩ :=
    nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization A B LB Bh hQXB hT₁
  obtain ⟨e₂⟩ :=
    nonempty_fundamentalVertex₂_iso_fundamentalVertex₃_henselization A LA Ah Bh hQXA hT₂
  exact ⟨e₁.trans e₂⟩

end Identification

end CommAlgCat

end
