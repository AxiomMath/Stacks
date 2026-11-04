module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBaseCompositionResidue
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatComposition
public import StacksFrontier.CategoryTheory.CompositeCancellation

/-!
# The collapse mirror of [Stacks, Tag 01XK] at the unbounded model

`Stacks.Cohomology.AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`
(`AlgebraicGeometry/AffineCohomologyComparison/UnboundedModel.lean`) reads the collapse factor of
[Stacks, Tag 089W] at the unbounded model: the crossing of the two models of the iterated derived
functor at an object, followed by the collapse of the **inner** functor at a right acyclic object,
is the degree-`n` cohomology of the comparison `θ` of the two iterated derived functors, then of
`RG` of the unbounded collapse, then the crossing of the two models downstairs.

This file proves its mirror, for [Stacks, Tag 01XK] rather than 089W. The two tags share their
first factor exactly — `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop` — and differ only in which functor
collapses: 089W collapses the inner one through
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso`, while 01XK collapses the **outer**
one through `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`. So where the 089W factor is
followed by `RG` of a collapse, the 01XK factor is followed by the **edge morphism** of `G` and by
`G` of the crossing of the two models for `F` alone.

## Main results

* `singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`: **[Stacks, Tag 01XK]'s collapse
  factor read at the unbounded model.** The crossing of the two models of the iterated derived
  functor at `E X`, followed by Grothendieck's comparison inverted, is the degree-`n` cohomology
  of `θ` at `(E X)[0]`, then the cohomology edge morphism of `G` at `RF((E X)[0])`, then `G`
  applied to the crossing of the two models for `F` at `E X`.

  The functor `E` is kept general rather than specialised to the identity: [Stacks, Tag 01XK]
  whiskers by the inclusion of the quasi-coherent modules, and an `(𝟭 _).obj` in that slot is a
  known unfolding obstacle.

* `homotopyHomologyComparisonToDerived_app_quotient_comp_factorsh`: the transported comparison of
  `G` at the image of a complex, with the derived-category factorisation of the cohomology functor
  cancelled off its right-hand end.

* `factorsh_comp_rightDerivedIsoRes_inv_comp_rightDerivedCompNatIso_inv`: the residue of the
  mirror, with the two model crossings already removed — Grothendieck's comparison inverted
  against the transported comparison of `G`.

## How the chase goes

`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res` reads each
model crossing off its construction: the cohomology of `Rw` applied to the comparison
`X[0] ≅ Qh(resH X)`, the unit of `Rw` at the extended chosen resolution inverted, the derived
category's cohomology factorisation, and `Stacks.DerivedIndexing.rightDerivedIsoRes` inverted.
That is the form these cancel in; the older `…_hom_app` takes the
`CategoryTheory.Functor.boundedDerivedIso` route, which cancels against 089W instead.

With both crossings so read, the chase is in two halves.

* **The derived half.** The leading cohomology of the comparison `X[0] ≅ Qh(resH X)` is common to
  the two sides once the naturality of `θ` has moved it across, and the naturality of the edge
  morphism of `G` moves the unit of `RF` across. What is then left in front of the edge morphism
  is `αFG` inverted, `θ` and the unit of `RF` inverted, which `hθ` — the factorisation
  characterising `θ` — turns into `αG` alone, the crossing
  `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of `CategoryTheory.Iso.refl (F ⋙ G)` being
  an identity. The defining factorisation of the edge morphism,
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison_fac_app`,
  then replaces `αG` and the edge morphism by the transported comparison.
* **The residue.** What remains has no derived functor and no unit in it:
  `Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient` evaluates the transported
  comparison at the extended chosen resolution, and
  `Stacks.Cohomology.AffineBase.rightDerivedIsoRes_comp_homologyComparison` identifies the
  resulting homology comparison with Grothendieck's comparison.

## Implementation notes

*Every reassociation and every cancellation is hoisted onto variables.* The goals carry two
spellings of the degree-`n` cohomology of the composite — computed in the homotopy category of
`C` and computed on a complex — and two spellings of `G ∘ F` applied termwise. Each pair is equal
definitionally and not syntactically, so the goals are not type-correct at the `implicit`
transparency level at which a rewrite builds its motive, and `rw` is unavailable on them. The
chases are therefore stated at variables of an abstract category and applied in argument position,
where the elaborator checks against the goal at default transparency.

*Invertibility is passed on plain morphisms.* Each cancelling pair is given as a hypothesis
`f ≫ g = 𝟙 _` rather than as a `CategoryTheory.Iso`, because the morphisms involved are
components of four different natural isomorphisms and a hypothesis phrased with
`CategoryTheory.Iso.inv` would let the unifier identify two of their objects.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.EdgeCompat

universe vD uD vA uA vB uB vC uC

/-! ### The chases, on variables -/

section Abstract

variable {V : Type*} [Category* V]

/-- **An isomorphism's inverse against the two halves of a known factorisation.** If
`ii ≫ i = 𝟙`, `g ≫ gi = 𝟙` and `i ≫ t = v ≫ g`, then `ii ≫ v = t ≫ gi`. At variables, with each
invertibility on plain morphisms. -/
private theorem inv_comp_of_comp_eq {P Q R S : V} {i : P ⟶ Q} {ii : Q ⟶ P}
    (hii : ii ≫ i = 𝟙 Q) {t : Q ⟶ R} {v : P ⟶ S} {g : S ⟶ R} {gi : R ⟶ S}
    (hg : g ≫ gi = 𝟙 S) (hv : i ≫ t = v ≫ g) : ii ≫ v = t ≫ gi := by
  have hvv : i ≫ t ≫ gi = v := by
    rw [← Category.assoc, hv, Category.assoc, hg, Category.comp_id]
  rw [← hvv, ← Category.assoc ii i, hii, Category.id_comp]

/-- **A leading factor known to be an identity, dropped.** At variables, so that the source of
the trailing morphism — a second spelling of the identity's object — is reconciled in argument
position. -/
private theorem id_comp_of_eq_id {P R : V} {z : P ⟶ P} (hz : z = 𝟙 P) (f : P ⟶ R) :
    z ≫ f = f := by rw [hz, Category.id_comp]

/-- **A cancelling pair removed from the tail of a five-fold composite.** At variables. -/
private theorem comp_tail_cancel {P₀ P₁ P₂ P₃ P₄ P₅ : V} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂)
    (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄) {e : P₄ ⟶ P₅} {f : P₅ ⟶ P₄} (hef : e ≫ f = 𝟙 P₄) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ f = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]
  rw [hef, Category.comp_id]

/-- **A trailing factor substituted and the head replaced by a known square.** At variables. -/
private theorem comp_tail_of {P Q R S T : V} {u : P ⟶ Q} {a : Q ⟶ T} {v : P ⟶ S} {b : S ⟶ R}
    {w : Q ⟶ R} {c : R ⟶ T} (h1 : v ≫ b = u ≫ w) (h2 : w ≫ c = a) :
    u ≫ a = v ≫ b ≫ c := by
  rw [← h2, ← Category.assoc u w c, ← h1, Category.assoc]

/-- **The residue read off the hom-form, at variables.** From `p ≫ q = v ≫ r₁ ≫ r₂` with `r₂` and
`r₁` invertible on the right and `p` invertible on the left, `pi ≫ v = q ≫ r₂i ≫ r₁i`. -/
private theorem inv_comp_eq_of_comp_eq_comp {P Q R R' S T : V} {p : P ⟶ Q} {pi : Q ⟶ P}
    (hp : pi ≫ p = 𝟙 Q) {q₁ : Q ⟶ R'} {q₂ : R' ⟶ R} {v : P ⟶ S} {r₁ : S ⟶ T} {r₂ : T ⟶ R}
    {r₂i : R ⟶ T} (h2 : r₂ ≫ r₂i = 𝟙 T) {r₁i : T ⟶ S} (h1 : r₁ ≫ r₁i = 𝟙 S)
    (hres : p ≫ q₁ ≫ q₂ = v ≫ r₁ ≫ r₂) : pi ≫ v = q₁ ≫ q₂ ≫ r₂i ≫ r₁i := by
  rw [← Category.assoc]
  exact inv_comp_of_comp_eq hp (g := r₁ ≫ r₂) (gi := r₂i ≫ r₁i)
    (by simp [reassoc_of% h2, h1]) (by simpa using hres)

/-- **Two known factorisations glued through a common four-fold middle.** At variables. -/
private theorem glue_four {P Q R S T U V' W : V} {f : P ⟶ Q} {g : Q ⟶ R} {k : R ⟶ S}
    {a : P ⟶ T} {b : T ⟶ U} {c : U ⟶ S} {m₁ : Q ⟶ V'} {m₂ : V' ⟶ W} {m₃ : W ⟶ U}
    (hab : a ≫ b = f ≫ m₁ ≫ m₂ ≫ m₃) (hgk : g ≫ k = m₁ ≫ m₂ ≫ m₃ ≫ c) :
    f ≫ g ≫ k = a ≫ b ≫ c := by
  rw [hgk, ← Category.assoc a b c, hab]
  simp only [Category.assoc]

/-- **A three-fold composite carried under a functor, with its value and two trailing factors
known.** At variables of two abstract categories, which is where the cohomology functor of the
derived category meets the two spellings of its value. -/
private theorem map_chase {W' : Type*} [Category* W'] (H : V ⥤ W')
    {P Q R S T' : V} {s : P ⟶ Q} {a : Q ⟶ R} {g : R ⟶ S} {t : P ⟶ T'} {m : T' ⟶ S}
    (h : s ≫ a ≫ g = t ≫ m) {X' Y' : W'} {e : H.obj S ⟶ X'} {d : H.obj T' ⟶ Y'} {k : Y' ⟶ X'}
    (hd : H.map m ≫ e = d ≫ k) {ha : H.obj R ⟶ X'} (hha : H.map g ≫ e = ha) :
    H.map s ≫ H.map a ≫ ha = H.map t ≫ d ≫ k := by
  simp only [← hha, ← hd, ← Functor.map_comp_assoc, h]

/-- **The outer assembly of the mirror, at variables.** The residue (`hM3`), the derived half
(`hKEY`) and the right-hand model crossing (`hGM`) are glued. -/
private theorem final_chase {P Q R S T U V' W Z' Z'' : V} {c₁ : P ⟶ Q} {c₂ : Q ⟶ R} {f : R ⟶ S}
    {g : S ⟶ T} {rdc : T ⟶ U} {hh : R ⟶ V'} {b₁ : V' ⟶ W} {b₂ : W ⟶ U}
    (hM3 : f ≫ g ≫ rdc = hh ≫ b₁ ≫ b₂)
    {x₁ : P ⟶ Z''} {x₂ : Z'' ⟶ Z'} {y : Z' ⟶ V'} (hKEY : c₁ ≫ c₂ ≫ hh = x₁ ≫ x₂ ≫ y)
    {gm : Z' ⟶ U} (hGM : y ≫ b₁ ≫ b₂ = gm) :
    (c₁ ≫ c₂ ≫ f ≫ g) ≫ rdc = x₁ ≫ x₂ ≫ gm := by
  simp only [Category.assoc, hM3, reassoc_of% hKEY, hGM]

end Abstract

/-! ### The transported comparison with the derived factorisation cancelled -/

section Transported

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] (n : ℕ)

/-- **The transported comparison of `G` at the image of a complex, with the derived-category
factorisation cancelled off its right-hand end.**
`Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient` ends with `G` applied to
that factorisation inverted; composing with `G` applied to the factorisation itself leaves the
homotopy-category factorisation of the degree-`n` cohomology of `G` applied termwise to the
complex, the homology comparison of `G`, and `G` applied to the homotopy-category factorisation
inverted. -/
public theorem homotopyHomologyComparisonToDerived_app_quotient_comp_factorsh
    (Z : CochainComplex B ℤ) :
    (homotopyHomologyComparisonToDerived G (n : ℤ)).app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Z) ≫
        G.map ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Z)) =
      (DerivedCategory.homologyFunctorFactorsh C (n : ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (n : ℤ)).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
          homologyComparison G Z (n : ℤ) ≫
            G.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).inv.app
              Z) := by
  rw [homotopyHomologyComparisonToDerived_app_quotient]
  exact comp_tail_cancel _ _ _ _
    (map_comp_cancel G (Iso.inv_hom_id_app (DerivedCategory.homologyFunctorFactorsh B (n : ℤ))
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Z)))

end Transported

/-! ### The residue, with the two model crossings removed -/

section Residue

variable {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
  (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
  (n : ℕ)

omit [HasDerivedCategory A] in
/-- **The residue of the mirror.** The derived-category factorisation of the degree-`n` cohomology
of `G ∘ F` applied termwise to the extended chosen injective resolution of `E X`, followed by
`Stacks.DerivedIndexing.rightDerivedIsoRes` inverted and by Grothendieck's comparison inverted,
is the transported comparison of `G` at that resolution's image under `F`, followed by `G` applied
to the derived-category factorisation and to `rightDerivedIsoRes` inverted for `F`.

No derived functor and no unit occurs: this is what the mirror reduces to once both model
crossings have been cancelled. It is
`Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient_comp_factorsh` against
`Stacks.Cohomology.AffineBase.rightDerivedIsoRes_comp_homologyComparison`. -/
public theorem factorsh_comp_rightDerivedIsoRes_inv_comp_rightDerivedCompNatIso_inv
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n))
    (X : D)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex).sc n)] :
    (DerivedCategory.homologyFunctorFactorsh C (n : ℤ)).hom.app
          (((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (Stacks.DerivedIndexing.resH.obj (E.obj X))) ≫
        (Stacks.DerivedIndexing.rightDerivedIsoRes (F ⋙ G) n).inv.app (E.obj X) ≫
          (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E F G n h).inv.app X =
      (homotopyHomologyComparisonToDerived G (n : ℤ)).app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (Stacks.DerivedIndexing.resH.obj (E.obj X))) ≫
        G.map ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              (Stacks.DerivedIndexing.resH.obj (E.obj X)))) ≫
          G.map ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app (E.obj X)) :=
  glue_four
    (homotopyHomologyComparisonToDerived_app_quotient_comp_factorsh G n
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((injectiveResolution (E.obj X)).cocomplex.extend ComplexShape.embeddingUpNat)))
    (inv_comp_eq_of_comp_eq_comp
      (Iso.inv_hom_id_app (Stacks.DerivedIndexing.rightDerivedIsoRes (F ⋙ G) n) (E.obj X))
      (map_comp_cancel G
        (Iso.hom_inv_id_app (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ))
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution (E.obj X)).cocomplex.extend ComplexShape.embeddingUpNat))))
      (map_comp_cancel G
        ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).hom_inv_id_app (E.obj X)))
      (Stacks.Cohomology.AffineBase.rightDerivedIsoRes_comp_homologyComparison E F G n h X))

end Residue

/-! ### The mirror -/

section Mirror

variable {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
  (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
  (n : ℕ)
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RG : DerivedCategory B ⥤ DerivedCategory C)
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (RFG : DerivedCategory A ⥤ DerivedCategory C)
  (αFG : (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RFG)
  [RFG.IsRightDerivedFunctor αFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (θ : RFG ⟶ RF ⋙ RG)

/-- **[Stacks, Tag 01XK]'s collapse factor read at the unbounded model.** For `E : D ⥤ A`,
`F : A ⥤ B` and `G : B ⥤ C` additive with `G` left exact, unbounded right derived functors `RF`,
`RG` and `RFG` of the three degreewise functors, a comparison `θ : RFG ⟶ RF ⋙ RG` satisfying the
factorisation `hθ` that characterises it, and the pointwise homology-preservation hypothesis `h`
of `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`, the crossing of the two models at
`E X` followed by Grothendieck's comparison inverted is

> the degree-`n` cohomology of `θ` at `(E X)[0]`, then the cohomology edge morphism of `G` at
> `RF((E X)[0])`, then `G` applied to the crossing of the two models for `F` at `E X`.

This is the `Gamma(V, -)`-exactness mirror of
`Stacks.Cohomology.AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`:
the same data and the same `hθ`, with the **outer** functor collapsing rather than the inner one.
Nothing is assumed of the object, and in particular no acyclicity: where 089W needs `F X` to be
right acyclic for `G`, 01XK needs only that `G` preserve the homology that occurs. -/
public theorem singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L))
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n))
    (X : D)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex).sc n)] :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (F ⋙ G) RFG αFG
            hresA n).hom.app (E.obj X) ≫
        (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E F G n h).inv.app X =
      (DerivedCategory.homologyFunctor C (n : ℤ)).map
          (θ.app ((DerivedCategory.singleFunctor A 0).obj (E.obj X))) ≫
        (derivedHomologyComparison G RG αG hresB (n : ℤ)).app
            (RF.obj ((DerivedCategory.singleFunctor A 0).obj (E.obj X))) ≫
          G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF αF
            hresA n).hom.app (E.obj X)) := by
  have hcid : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).inv.app (Stacks.DerivedIndexing.resH.obj (E.obj X))) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hθK : αFG.app (Stacks.DerivedIndexing.resH.obj (E.obj X)) ≫
        θ.app (DerivedCategory.Qh.obj (Stacks.DerivedIndexing.resH.obj (E.obj X))) =
      αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (Stacks.DerivedIndexing.resH.obj (E.obj X))) ≫
        RG.map (αF.app (Stacks.DerivedIndexing.resH.obj (E.obj X))) :=
    (hθ (Stacks.DerivedIndexing.resH.obj (E.obj X))).trans (id_comp_of_eq_id hcid _)
  have hRGcancel : RG.map (αF.app (Stacks.DerivedIndexing.resH.obj (E.obj X))) ≫
      RG.map ((Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).inv.app (E.obj X)) = 𝟙 _ := by
    exact map_comp_cancel RG
      ((Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).hom_inv_id_app (E.obj X))
  have hKEY3 : (Stacks.DerivedFunctor.resCompUnitIso (F ⋙ G) RFG αFG hresA).inv.app (E.obj X) ≫
        αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (Stacks.DerivedIndexing.resH.obj (E.obj X))) =
      θ.app (DerivedCategory.Qh.obj (Stacks.DerivedIndexing.resH.obj (E.obj X))) ≫
        RG.map ((Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).inv.app (E.obj X)) :=
    inv_comp_of_comp_eq
      ((Stacks.DerivedFunctor.resCompUnitIso (F ⋙ G) RFG αFG hresA).inv_hom_id_app (E.obj X))
      hRGcancel hθK
  have hKEY2 : RFG.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (E.obj X)) ≫
        (Stacks.DerivedFunctor.resCompUnitIso (F ⋙ G) RFG αFG hresA).inv.app (E.obj X) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (Stacks.DerivedIndexing.resH.obj (E.obj X))) =
      θ.app ((DerivedCategory.singleFunctor A 0).obj (E.obj X)) ≫
        RG.map (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (E.obj X)) ≫
          (Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).inv.app (E.obj X)) := by
    rw [RG.map_comp]
    exact comp_tail_of
      (θ.naturality ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (E.obj X))).symm
      hKEY3.symm
  have hKEY := map_chase (DerivedCategory.homologyFunctor C (n : ℤ)) hKEY2
    ((derivedHomologyComparison G RG αG hresB (n : ℤ)).naturality
      (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (E.obj X)) ≫
        (Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).inv.app (E.obj X)))
    (derivedHomologyComparison_fac_app G RG αG hresB (n : ℤ)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (Stacks.DerivedIndexing.resH.obj (E.obj X))))
  have hGM : G.map ((DerivedCategory.homologyFunctor B (n : ℤ)).map
          (RF.map ((Stacks.DerivedFunctor.singleIsoResCompQh (A := A)).hom.app (E.obj X)) ≫
            (Stacks.DerivedFunctor.resCompUnitIso F RF αF hresA).inv.app (E.obj X))) ≫
        G.map ((DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              (Stacks.DerivedIndexing.resH.obj (E.obj X)))) ≫
          G.map ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app (E.obj X)) =
      G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF αF
        hresA n).hom.app (E.obj X)) := by
    rw [← G.map_comp, ← G.map_comp,
      Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res F RF αF
        hresA n (E.obj X), (DerivedCategory.homologyFunctor B (n : ℤ)).map_comp]
    exact congrArg G.map (by simp only [Category.assoc])
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_res (F ⋙ G) RFG
    αFG hresA n (E.obj X)]
  exact final_chase
    (factorsh_comp_rightDerivedIsoRes_inv_comp_rightDerivedCompNatIso_inv E F G n h X)
    hKEY hGM

end Mirror

end Stacks.EdgeCompat

end
