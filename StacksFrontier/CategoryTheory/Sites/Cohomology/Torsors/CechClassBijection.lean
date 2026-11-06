module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassSurjectivity
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
import StacksCore.Tactic.StacksAttribute

/-!
# First Čech cohomology is the set of locally trivial torsor classes

Let `(C, J)` be a site, let `G` be an abelian sheaf on `C` and let `𝒰 = {U_i → U}` be a
covering family of an object `U`. This file proves that the Čech class map of
`Stacks.Cohomology.Torsors.cechClass` is a bijection from the isomorphism classes of
`G|_U`-torsors which restrict to trivial torsors over each `U_i` onto `Ȟ¹(𝒰, G)`.

Injectivity is `Stacks.Cohomology.Torsors.cechClass_injective`. Surjectivity is the
construction of `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassSurjectivity`,
which produces from a Čech `1`-cocycle `z` of `G` and a degree-zero Čech cochain `b` of the
middle term of a short exact sequence `0 → G → I → Q → 0` with `d b = z` a torsor under
`G|_U` with a section over every member of the family and with Čech class the class of `z`.
What remains, and is proved here, is that such a cochain `b` always exists: embed `G` in an
injective abelian sheaf `I` and take the cokernel; the positive-degree Čech cohomology of an
injective abelian sheaf vanishes (Stacks 03AW,
`Stacks.CechSite.injective_sheaf_cechCohomology_isZero`), so the image of `z` in `I` is a Čech
coboundary.

The vanishing theorem is stated at the small-site universe convention
`AddCommGrpCat.{max a u v w}` for a site `C : Type u` with `Category.{v} C` and a family
indexed in `Type w`, and enough injectives for abelian sheaves
(`CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`) is available at that convention, so
the results of this file are stated there.

## Main results

* `Stacks.Cohomology.Torsors.exists_cechClass_eq`: every Čech `1`-cocycle is the Čech class of
  an isomorphism class of torsors which is trivial on the members of the family.
* `Stacks.Cohomology.Torsors.cechClass_bijective` and
  `Stacks.Cohomology.Torsors.locallyTrivialClassEquivCechH1`: **Stacks 0A6G**, the Čech class
  map identifies the isomorphism classes of `G|_U`-torsors which restrict to trivial torsors
  over each `U_i` with `Ȟ¹(𝒰, G)`.

## Implementation notes

The short exact sequence used to realize a cocycle as a coboundary is not fixed in advance:
`Stacks.Cohomology.Torsors.exists_cechClass_eq_of_injective` takes any short exact sequence
whose middle term is injective, and `Stacks.Cohomology.Torsors.exists_cechClass_eq` feeds it
the cokernel of a monomorphism into an injective sheaf. This keeps `EnoughInjectives` out of
all but the last statement, where it is supplied as a local instance inside the proof rather
than as a hypothesis.

The other assertion of Stacks 0A6G, that the canonical map `Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX
is injective, is `Stacks.CechSite.injective_cechCohomologyToCohomology_one`; it is stated for the
degree-one Čech cohomology read in the bounded-below derived category rather than for the
explicit quotient `Stacks.CechSite.cechH1` which the bijection here lands in. The two groups are
identified by `Stacks.CechSite.cechH1Equiv`, and the two assertions are put together at one group
in `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassCohomologyComparison`. The Čech
class map of this file is related to that comparison there as well, by
`Stacks.CechSite.torsorCohomologyClass_eq`, which gives both assertions of the source inside
`H¹(U, G)` (`Stacks.CechSite.injective_torsorCohomologyClass_and_range_eq`). The source's
description of the identification as the one induced by the bijection of Stacks 03AJ is
`Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq`.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 01DP](https://stacks.math.columbia.edu/tag/01DP)
* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R), the same statement for
  an open covering of a topological space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h a w v u

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

section Push

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} AddCommGrpCat.{a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- Pushing a Čech `1`-cocycle along a morphism of abelian presheaves gives a Čech
`1`-cocycle, because pushing commutes with the Čech differential. -/
lemma pushCochain_mem_cocycles1 {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F')
    (z : cocycles1 E F) :
    pushCochain E φ 1 (z : cechCochain E F 1) ∈ cocycles1 E F' := by
  have hz : cechDifferential E F 1 (z : cechCochain E F 1) = 0 :=
    AddMonoidHom.mem_ker.1 z.2
  refine AddMonoidHom.mem_ker.2 ?_
  rw [cechDifferential_pushCochain, hz, map_zero]

/-- The push of a Čech `1`-cocycle along a morphism of abelian presheaves, as a Čech
`1`-cocycle. -/
def pushCocycles1 {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F') (z : cocycles1 E F) :
    cocycles1 E F' :=
  ⟨pushCochain E φ 1 (z : cechCochain E F 1), pushCochain_mem_cocycles1 E φ z⟩

/-- The underlying Čech `1`-cochain of `pushCocycles1 E φ z` is the push of the underlying
cochain of `z` along `φ`. -/
@[simp] lemma pushCocycles1_coe {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ F')
    (z : cocycles1 E F) :
    (pushCocycles1 E φ z : cechCochain E F' 1) =
      pushCochain E φ 1 (z : cechCochain E F 1) := rfl

end Push

section Injective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- **Every Čech `1`-cocycle with values in an injective abelian sheaf is a Čech
coboundary**, because the positive-degree Čech cohomology of an injective abelian sheaf
vanishes (Stacks 03AW). -/
theorem exists_cechDifferential_zero_of_injective (I : Sheaf J AddCommGrpCat.{max a u v w})
    [Injective I] (c : cocycles1 E I.obj) :
    ∃ b : cechCochain E I.obj 0,
      cechDifferential E I.obj 0 b = (c : cechCochain E I.obj 1) :=
  (subsingleton_cechCohomologyOne_iff E I.obj).1
    (AddCommGrpCat.subsingleton_of_isZero
      (injective_sheaf_cechCohomology_isZero.{a, w, v, u} E I 1 Nat.one_pos)) c

end Injective

section Bijection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify J AddCommGrpCat.{max a u v w}]
  [HasSheafify (J.over U) AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{max a u v w})]

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})] in
/-- **A Čech `1`-cocycle is the Čech class of a locally trivial isomorphism class of
torsors**, provided the coefficient sheaf sits in a short exact sequence whose middle term is
injective: the cocycle becomes a Čech coboundary there, and the torsor of the cocycle is then
available. -/
theorem exists_cechClass_eq_of_injective (hE : E.sieve₀ ∈ J U)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max a u v w})) (hS : S.ShortExact)
    (hI : Injective S.X₂) (z : cocycles1 E S.X₁.obj) :
    ∃ c : LocallyTrivialClass E S.X₁, cechClass E S.X₁ c = cls E S.X₁.obj z := by
  have := hI
  obtain ⟨b, hb⟩ := exists_cechDifferential_zero_of_injective.{a, w, v, u} E S.X₂
    (pushCocycles1 E S.f.hom z)
  exact ⟨⟨Quotient.mk (torsorSetoid (S.X₁.over U)) (cocycleTorsor E S hS hE z b hb),
      ⟨cocycleTorsor E S hS hE z b hb, rfl,
        fun i ↦ ⟨cocycleSection E S hS hE z b hb i⟩⟩⟩,
    cechClass_cocycleTorsor E S hS hE z b hb⟩

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})] in
/-- **Every Čech `1`-cocycle is the Čech class of a locally trivial isomorphism class of
torsors.** The coefficient sheaf is embedded in an injective abelian sheaf (Stacks 01DP) and
the cokernel is formed there, which realizes the cocycle as a Čech coboundary of the middle
term. -/
@[ega "IV 16.5.15" "partial"]
theorem exists_cechClass_eq (hE : E.sieve₀ ∈ J U) (G : Sheaf J AddCommGrpCat.{max a u v w})
    (z : cocycles1 E G.obj) :
    ∃ c : LocallyTrivialClass E G, cechClass E G c = cls E G.obj z := by
  have : EnoughInjectives (Sheaf J AddCommGrpCat.{max a u v w}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat J
  have hS : (ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _
      mono_f := Injective.ι_mono G
      epi_g := inferInstance }
  exact exists_cechClass_eq_of_injective.{h, a, w, v, u} E hE _ hS
    (Injective.injective_under G) z

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})] in
/-- **The Čech class map is surjective onto `Ȟ¹(𝒰, G)`.** -/
theorem cechClass_surjective (hE : E.sieve₀ ∈ J U)
    (G : Sheaf J AddCommGrpCat.{max a u v w}) :
    Function.Surjective (cechClass E G) := by
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact exists_cechClass_eq.{h, a, w, v, u} E hE G z

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})] in
/-- **Stacks Project, Tag 0A6G.** The Čech class map is a bijection from the isomorphism
classes of `G|_U`-torsors which restrict to trivial torsors over each member of the covering
family onto first Čech cohomology. -/
@[ega "IV 16.5.15" "For a fixed covering"]
theorem cechClass_bijective (hE : E.sieve₀ ∈ J U)
    (G : Sheaf J AddCommGrpCat.{max a u v w}) :
    Function.Bijective (cechClass E G) :=
  ⟨cechClass_injective E G hE, cechClass_surjective.{h, a, w, v, u} E hE G⟩

/-- **Stacks Project, Tag 0A6G.** First Čech cohomology of a covering family, as the set of
isomorphism classes of `G|_U`-torsors which restrict to trivial torsors over each member of
the family. -/
@[stacks 0A6G "variant: the Čech class bijection onto Ȟ¹(𝒰,G); \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "partial"]
def locallyTrivialClassEquivCechH1 (hE : E.sieve₀ ∈ J U)
    (G : Sheaf J AddCommGrpCat.{max a u v w}) :
    LocallyTrivialClass E G ≃ cechH1 E G.obj :=
  Equiv.ofBijective (cechClass E G) (cechClass_bijective.{h, a, w, v, u} E hE G)

end Bijection

end Stacks.Cohomology.Torsors

end
