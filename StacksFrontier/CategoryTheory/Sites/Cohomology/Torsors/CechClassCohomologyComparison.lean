module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeOneInjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassBijection
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech class of a torsor, and its image in `H¹(U, G)`

Let `(C, K)` be a site, let `G` be an abelian sheaf on `C` and let `𝒰 = {U_i → U}` be a covering
family of an object `U`. This file shows that the comparison `Ȟ¹(𝒰, G) → H¹(U, G)` is injective
and that `Ȟ¹(𝒰, G)` is identified with the set of isomorphism classes of `G|_U`-torsors which
restrict to trivial torsors over each `U_i`, both at the explicit quotient
`Stacks.CechSite.cechH1` of Čech `1`-cocycles by Čech `1`-coboundaries.

The class in `H¹(U, G)` of such a torsor, `Stacks.CechSite.torsorCohomologyClass`, is its Čech
class followed by the comparison, so that the triangle

`{isomorphism classes of G|_U-torsors trivial over each U_i} → Ȟ¹(𝒰, G) → H¹(U, G)`

commutes (`Stacks.CechSite.torsorCohomologyClass_eq`). That composite is injective and its image
is exactly the image of `Ȟ¹(𝒰, G)`: the subgroup `Ȟ¹(𝒰, G)` of `H¹(U, G)` is precisely the set
of classes of torsors which are trivial over every member of the family, each of which is the
Čech class of the transition cocycle of any family of its local sections
(`Stacks.CechSite.torsorCohomologyClass_mk`).

## Main results

* `Stacks.CechSite.cechDerivedHomologyIso`: the cohomology of the Čech complex read in the
  bounded-below derived category is the homology of the Čech complex itself.
* `Stacks.CechSite.cechH1Equiv`: the degree-one case of the previous isomorphism, carried on to
  the explicit quotient of Čech `1`-cocycles by Čech `1`-coboundaries.
* `Stacks.CechSite.cechH1ToCohomology`: the comparison `Ȟ¹(𝒰, G) → H¹(U, G)`, as an additive map
  out of that explicit quotient, and `Stacks.CechSite.injective_cechH1ToCohomology`, its
  injectivity.
* `Stacks.CechSite.injective_cechH1ToCohomology_and_bijective_cechClass`: the comparison is
  injective and the Čech class map of torsors is bijective, at one first Čech cohomology group.
* `Stacks.CechSite.torsorCohomologyClass` and `Stacks.CechSite.torsorCohomologyClass_eq`: the
  compatibility of the Čech class map of torsors with the comparison to `H¹(U, G)`, and
  `Stacks.CechSite.torsorCohomologyClass_mk`, its computation by a transition cocycle.
* `Stacks.CechSite.injective_torsorCohomologyClass_and_range_eq`: the class map of torsors into
  `H¹(U, G)` is injective with image the image of `Ȟ¹(𝒰, G)`;
  `Stacks.CechSite.locallyTrivialClassEquivRangeCohomology` is the resulting bijection with the
  image of `Ȟ¹(𝒰, G)` in `H¹(U, G)` and
  `Stacks.CechSite.isTrivial_iff_torsorCohomologyClass_eq_zero` its normalization at the trivial
  torsor.

## Implementation notes

The identification of the derived reading of Čech cohomology with the homology of the Čech
complex is `CategoryTheory.DerivedCategory.homologyFunctorFactors`, whiskered by the Čech complex
functor. The passage from there to `Stacks.CechSite.cechH1` is two further steps, because the
Čech complex is graded by `ℕ` and extended by zero to `ℤ` before it is handed to the derived
category: `HomologicalComplex.extendHomologyIso` undoes the extension and
`Stacks.CechSite.cechCohomologyOneEquiv` is the explicit description of its degree-one homology.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R), the same statement for
  an open covering of a topological space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h a w v u

namespace Stacks.CechSite

attribute [local instance] HasDerivedCategory.standard

section Identification

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- **The Čech cohomology of a covering family read in the bounded-below derived category is the
homology of its Čech complex.** The bounded-below localisation followed by the inclusion into the
unbounded derived category is the inclusion of complexes followed by the unbounded localisation,
so this is `CategoryTheory.DerivedCategory.homologyFunctorFactors`. -/
def cechDerivedHomologyIso (i : ℤ) :
    cechDerivedFunctor.{a} K E ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max a u v w} i ≅
      cechComplexIntFunctor.{a} K E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max a u v w} (ComplexShape.up ℤ) i :=
  Functor.isoWhiskerLeft (cechComplexIntFunctor.{a} K E)
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max a u v w} i)

/-- **The degree-one Čech cohomology of a covering family, read in the bounded-below derived
category, is the explicit quotient of Čech `1`-cocycles by Čech `1`-coboundaries.** -/
def cechH1Equiv (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    (cechDerivedFunctor.{a} K E ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max a u v w} 1).obj G ≃+
      cechH1 E G.obj :=
  (((cechDerivedHomologyIso.{a} K E 1).app G).addCommGroupIsoToAddEquiv.trans
      (HomologicalComplex.extendHomologyIso (cechComplex E G.obj)
          ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ))
          rfl).addCommGroupIsoToAddEquiv).trans
    (cechCohomologyOneEquiv E G.obj)

end Identification

section Comparison

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify K AddCommGrpCat.{max a u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w})]

/-- **The comparison `Ȟ¹(𝒰, G) → H¹(U, G)`, out of the explicit first Čech cohomology group**:
the degree-one comparison transported along `Stacks.CechSite.cechH1Equiv`. -/
def cechH1ToCohomology (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    cechH1 E G.obj →+
      (derivedSectionsFunctor K U ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max a u v w} 1).obj G :=
  (ConcreteCategory.hom ((cechCohomologyToCohomology.{a} K E hE 1).app G)).comp
    (cechH1Equiv.{a} K E G).symm.toAddMonoidHom

/-- **The comparison `Ȟ¹(𝒰, G) → H¹(U, G)` is injective on the explicit first Čech cohomology
group.** -/
theorem injective_cechH1ToCohomology (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (cechH1ToCohomology.{a} K E hE G) := fun _ _ hxy ↦
  (cechH1Equiv.{a} K E G).symm.injective
    (injective_cechCohomologyToCohomology_one.{a} K E hE G hxy)

variable [HasSheafify (K.over U) AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})]
  [HasExt.{h} (Sheaf (K.over U) AddCommGrpCat.{max a u v w})]

omit [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- For a covering family `𝒰 = {U_i → U}` of an object of a site and an abelian sheaf `G`, the
map `Ȟ¹(𝒰, G) → H¹(U, G)` is injective, and `Ȟ¹(𝒰, G)` is in bijection — under the Čech class
of a family of local sections — with the isomorphism classes of `G|_U`-torsors which restrict to
trivial torsors over each `U_i`. Both assertions are about the group
`Stacks.CechSite.cechH1 E G.obj`. -/
@[stacks 0A6G "variant: injectivity and the Čech class bijection at the explicit Ȟ¹(𝒰,G); \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq"]
theorem injective_cechH1ToCohomology_and_bijective_cechClass (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (cechH1ToCohomology.{a} K E hE G) ∧
      Function.Bijective (Stacks.Cohomology.Torsors.cechClass E G) :=
  ⟨injective_cechH1ToCohomology.{a} K E hE G,
    Stacks.Cohomology.Torsors.cechClass_bijective.{h, a, w, v, u} E hE G⟩

/-! ### The Čech class of a torsor, read in `H¹(U, G)` -/

/-- **The class in `H¹(U, G)` of a locally trivial isomorphism class of torsors**: its Čech class
`Stacks.Cohomology.Torsors.cechClass` pushed along the comparison
`Stacks.CechSite.cechH1ToCohomology`. -/
def torsorCohomologyClass (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w})
    (c : Stacks.Cohomology.Torsors.LocallyTrivialClass E G) :
    (derivedSectionsFunctor K U ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max a u v w} 1).obj G :=
  cechH1ToCohomology.{a} K E hE G (Stacks.Cohomology.Torsors.cechClass E G c)

omit [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- **The Čech class map of torsors is compatible with the comparison to `H¹(U, G)`.** The class
in `H¹(U, G)` of a locally trivial isomorphism class of torsors is the image under
`Stacks.CechSite.cechH1ToCohomology` of its Čech class: the triangle

`{torsors trivial over each U_i} → Ȟ¹(𝒰, G) → H¹(U, G)`

commutes. -/
theorem torsorCohomologyClass_eq (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w})
    (c : Stacks.Cohomology.Torsors.LocallyTrivialClass E G) :
    torsorCohomologyClass.{h, a} K E hE G c =
      cechH1ToCohomology.{a} K E hE G (Stacks.Cohomology.Torsors.cechClass E G c) :=
  rfl

omit [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- **The class in `H¹(U, G)` of a torsor is computed by its transition cocycle**, for any
representative with sections over all members of the covering family and any choice of those
sections. -/
theorem torsorCohomologyClass_mk (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (G.over U))
    (hF : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i)))))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) :
    torsorCohomologyClass.{h, a} K E hE G
        ⟨Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid (G.over U)) F, ⟨F, rfl, hF⟩⟩ =
      cechH1ToCohomology.{a} K E hE G
        (cls E G.obj (Stacks.Cohomology.Torsors.transitionCocycle E G F s)) :=
  congrArg (cechH1ToCohomology.{a} K E hE G)
    (Stacks.Cohomology.Torsors.cechClass_mk E G F hF s)

omit [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- **The isomorphism classes of torsors trivial over each `U_i` inject into `H¹(U, G)`.** The
Čech class map is injective on them (`Stacks.Cohomology.Torsors.cechClass_injective`) and the
comparison is injective (`Stacks.CechSite.injective_cechH1ToCohomology`). -/
theorem injective_torsorCohomologyClass (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (torsorCohomologyClass.{h, a} K E hE G) :=
  (injective_cechH1ToCohomology.{a} K E hE G).comp
    (Stacks.Cohomology.Torsors.cechClass_injective E G hE)

omit [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- **A torsor trivial over each `U_i` is trivial exactly when its class in `H¹(U, G)`
vanishes.** -/
theorem isTrivial_iff_torsorCohomologyClass_eq_zero (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (G.over U))
    (hF : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i))))) :
    F.1.IsTrivial ↔
      torsorCohomologyClass.{h, a} K E hE G
        ⟨Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid (G.over U)) F, ⟨F, rfl, hF⟩⟩ = 0 :=
  (Stacks.Cohomology.Torsors.isTrivial_iff_cechClass_eq_zero E G hE F hF).trans
    ((injective_cechH1ToCohomology.{a} K E hE G).eq_iff'
      (map_zero (cechH1ToCohomology.{a} K E hE G))).symm

omit [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- **The image of `Ȟ¹(𝒰, G)` in `H¹(U, G)` is exactly the set of classes of torsors trivial over
each `U_i`.** Every Čech class is the Čech class of such a torsor
(`Stacks.Cohomology.Torsors.cechClass_surjective`). -/
theorem range_torsorCohomologyClass (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Set.range (torsorCohomologyClass.{h, a} K E hE G) =
      Set.range (cechH1ToCohomology.{a} K E hE G) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨Stacks.Cohomology.Torsors.cechClass E G c, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := Stacks.Cohomology.Torsors.cechClass_surjective.{h, a, w, v, u} E hE G x
    exact ⟨c, congrArg (cechH1ToCohomology.{a} K E hE G) hc⟩

omit [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- For a covering family `𝒰 = {U_i → U}` of an object of a site and an abelian sheaf `G`, the
map which sends an isomorphism class of `G|_U`-torsors trivial over each `U_i` to the image in
`H¹(U, G)` of its Čech class is injective, and its image is exactly the image of
`Ȟ¹(𝒰, G) → H¹(U, G)`.

So `Ȟ¹(𝒰, G)` is a subgroup of `H¹(U, G)`, and the Čech class map identifies that subgroup with
the isomorphism classes of `G|_U`-torsors which restrict to trivial torsors over each `U_i`. The
map is `Stacks.CechSite.torsorCohomologyClass`, which is the Čech class map
followed by the comparison (`Stacks.CechSite.torsorCohomologyClass_eq`); on a representative with
local sections it is the comparison applied to the class of the transition cocycle
(`Stacks.CechSite.torsorCohomologyClass_mk`), and it vanishes exactly on the trivial torsor
(`Stacks.CechSite.isTrivial_iff_torsorCohomologyClass_eq_zero`). -/
@[stacks 0A6G "variant: the Čech class of a torsor read in the derived H¹(U,G); \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "Abelian"]
theorem injective_torsorCohomologyClass_and_range_eq (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (torsorCohomologyClass.{h, a} K E hE G) ∧
      Set.range (torsorCohomologyClass.{h, a} K E hE G) =
        Set.range (cechH1ToCohomology.{a} K E hE G) :=
  ⟨injective_torsorCohomologyClass.{h, a} K E hE G,
    range_torsorCohomologyClass.{h, a} K E hE G⟩

/-- **The isomorphism classes of `G|_U`-torsors which restrict to trivial torsors over each `U_i`
are in bijection with the image of `Ȟ¹(𝒰, G)` in `H¹(U, G)`**, by the Čech class followed by the
comparison. The underlying map is `Stacks.CechSite.torsorCohomologyClass`
(`Stacks.CechSite.locallyTrivialClassEquivRangeCohomology_apply_coe`). -/
def locallyTrivialClassEquivRangeCohomology (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Stacks.Cohomology.Torsors.LocallyTrivialClass E G ≃
      Set.range (cechH1ToCohomology.{a} K E hE G) :=
  (Stacks.Cohomology.Torsors.locallyTrivialClassEquivCechH1.{h, a, w, v, u} E hE G).trans
    (Equiv.ofInjective _ (injective_cechH1ToCohomology.{a} K E hE G))

omit [HasExt.{h} (Sheaf K AddCommGrpCat.{max a u v w})] in
/-- The image of a class under `locallyTrivialClassEquivRangeCohomology`, viewed in `H¹(U, G)`,
is its image under `Stacks.CechSite.torsorCohomologyClass`. -/
@[simp]
theorem locallyTrivialClassEquivRangeCohomology_apply_coe (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w})
    (c : Stacks.Cohomology.Torsors.LocallyTrivialClass E G) :
    (locallyTrivialClassEquivRangeCohomology.{h, a} K E hE G c).1 =
      torsorCohomologyClass.{h, a} K E hE G c :=
  rfl

end Comparison

end Stacks.CechSite

end
