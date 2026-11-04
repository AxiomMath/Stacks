module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafConditionOneElement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monad.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# The left exact sequence of an étale presentation, on sections over a chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U → X` be a surjective étale morphism from a scheme, and put `R = U ×_X U` with its
two projections `t, s : R → U`. For every sheaf `P` on the spaces-étale site `X_{spaces,étale}`,
with values in an arbitrary category, and every object `W` of that site,

`P(W) → P(W ×_X U) ⇉ P(W ×_X R)`

is an equalizer diagram, functorially in `W`. For a sheaf of sets `G` on `X_{étale}`, taking
`W = V ×_Y X` for the étale scheme charts `V` of `Y` gives the exact sequence of presheaves

`0 → f_*G → (V ↦ G(V ×_Y U)) → (V ↦ G(V ×_Y R))`

on `Y_{étale}`, whose first term is the direct image itself. The direct image of `𝒪_X`-modules
along `f` is a right adjoint and an additive functor.

## Main results

* `CategoryTheory.Limits.isPullback_lift_of_isTerminal`: in a category with a terminal object,
  if `Z` is a product `W × U` and `Z₂` is a product `Z × U`, then `Z₂` is the fibre product
  `Z ×_W Z` of the projection `Z → W` with itself.
* `AlgebraicGeometry.Space.SpacesEtale.isCovering_singleton_of_isSurjective`: a one-element
  family of the spaces-étale site whose morphism is surjective on points is a covering family.
* `AlgebraicGeometry.Space.isLimitForkOfSurjectiveSingleton`: the sheaf condition for a
  one-element covering of the spaces-étale site given by a surjective morphism.
* `AlgebraicGeometry.Space.isSurjective_of_isPullback_isTerminal`: the projection `W ×_X U → W`
  is surjective when `U → X` is.
* `AlgebraicGeometry.Space.exists_relationChart`: `U ×_X U` is again an étale scheme chart.
* `AlgebraicGeometry.Space.isLimitForkOfEtalePresentation`: `P(W) → P(W ×_X U) ⇉ P(W ×_X R)` is
  an equalizer diagram.
* `AlgebraicGeometry.Space.isLimitForkPresheafOfEtalePresentation`: the same equalizer diagram,
  as a diagram of presheaves on the spaces-étale site.
* `AlgebraicGeometry.Space.isLimitForkDirectImage`: the exact sequence
  `0 → f_*G → (V ↦ G(V ×_Y U)) → (V ↦ G(V ×_Y R))` of presheaves on `Y_{étale}`.
* `AlgebraicGeometry.Space.modulePushforward_additive`: the direct image of `𝒪_X`-modules is an
  additive functor.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### Products and fibre products -/

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Let `T` be a terminal object, let `Z` be a product `W × U` with projections `π` and `ρ`,
and let `Z₂` be a product `Z × U` with projections `a` and `b`. Then `a`, together with the
morphism `Z₂ ⟶ Z` whose components are `a ≫ π` and `b`, exhibits `Z₂` as the fibre product
`Z ×_W Z` of `π` with itself. -/
theorem isPullback_lift_of_isTerminal {T W U Z Z₂ : C} (hT : IsTerminal T)
    {π : Z ⟶ W} {ρ : Z ⟶ U} {a : Z₂ ⟶ Z} {b : Z₂ ⟶ U}
    (hZ : IsPullback π ρ (hT.from W) (hT.from U))
    (hZ₂ : IsPullback a b (hT.from Z) (hT.from U)) :
    IsPullback a (hZ.lift (a ≫ π) b (hT.hom_ext _ _)) π π := by
  refine IsPullback.mk' (hZ.lift_fst _ _ _).symm ?_ ?_
  · intro T' φ φ' h₀ h₁
    refine hZ₂.hom_ext h₀ ?_
    have hb : hZ.lift (a ≫ π) b (hT.hom_ext _ _) ≫ ρ = b := hZ.lift_snd _ _ _
    rw [← hb, ← Category.assoc, ← Category.assoc, h₁]
  · intro T' x y hxy
    refine ⟨hZ₂.lift x (y ≫ ρ) (hT.hom_ext _ _), hZ₂.lift_fst _ _ _, ?_⟩
    refine hZ.hom_ext ?_ ?_
    · rw [Category.assoc, hZ.lift_fst, ← Category.assoc, hZ₂.lift_fst, hxy]
    · rw [Category.assoc, hZ.lift_snd, hZ₂.lift_snd]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w w' u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Surjective one-element coverings of the spaces-étale site -/

namespace SpacesEtale

variable {X : AlgebraicSpaces B S hS}

/-- The morphism of algebraic spaces underlying the unique morphism from an object of the
spaces-étale site of `X` to the terminal object is the structure morphism of that object. -/
theorem toSpaces_map_from_idObj (W : SpacesEtale B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map ((isTerminal_idObj B S hS X).from W) = W.1.hom := by
  show W.obj.hom ≫ inv (𝟙 X) = W.1.hom
  simp

/-- The spaces-étale site of `X` has binary products. -/
instance instHasBinaryProducts : HasBinaryProducts (SpacesEtale B S hS X) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- A single morphism of the spaces-étale site of `X` whose underlying morphism of algebraic
spaces is surjective on points is a covering family. -/
theorem isCovering_singleton_of_isSurjective {W Z : SpacesEtale B S hS X} (g : Z ⟶ W)
    (hg : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map g).hom) :
    IsCovering B S hS X ⟨W, PreZeroHypercover.singleton.{u + 1} g⟩ := fun x =>
  ⟨default, (hg x).choose, (hg x).choose_spec⟩

/-- A one-element covering family of the spaces-étale site generates a covering sieve. -/
theorem generate_singleton_mem_topology {W Z : SpacesEtale B S hS X} (g : Z ⟶ W)
    (hg : IsCovering B S hS X ⟨W, PreZeroHypercover.singleton.{u + 1} g⟩) :
    Sieve.generate (Presieve.singleton g) ∈ topology B S hS X W := by
  rw [show Presieve.singleton g = (PreZeroHypercover.singleton.{u + 1} g).presieve₀ from
    (PreZeroHypercover.presieve₀_singleton g).symm]
  exact Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hg⟩

end SpacesEtale

/-! ### The sheaf condition for a surjective one-element covering -/

variable {X Y : AlgebraicSpaces B S hS} {A : Type w} [Category.{w'} A]

/-- The sheaf condition for a one-element covering of the spaces-étale site of `X` presented by a
surjective morphism `g : Z ⟶ W`, with a presentation `p, q` of the fibre product `Z ×_W Z`: for
every sheaf `P`, with values in an arbitrary category, the fork `P(W) → P(Z) ⇉ P(Z ×_W Z)` is a
limit. -/
noncomputable def isLimitForkOfSurjectiveSingleton (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {W Z Z₂ : SpacesEtale B S hS X} {g : Z ⟶ W} {p q : Z₂ ⟶ Z}
    (hg : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map g).hom)
    (hpb : IsPullback p q g g)
    (w : P.map g.op ≫ P.map p.op = P.map g.op ≫ P.map q.op) :
    IsLimit (Fork.ofι (P.map g.op) w) :=
  Presheaf.isLimitForkOfSingletonCovering (SpacesEtale.topology B S hS X) P hP hpb
    (SpacesEtale.generate_singleton_mem_topology B S hS g
      (SpacesEtale.isCovering_singleton_of_isSurjective B S hS g hg)) w

/-- If `U → X` is surjective and `Z` is the product `W ×_X U` in the spaces-étale site of `X`,
then the projection `Z ⟶ W` is surjective on points. -/
theorem isSurjective_of_isPullback_isTerminal {U : SmallEtale B S hS X.1}
    (hU : IsSurjective B S hS U.1.hom) {W Z : SpacesEtale B S hS X}
    {π : Z ⟶ W} {ρ : Z ⟶ (comparisonFunctor B S hS X).obj U}
    (hZ : IsPullback π ρ ((SpacesEtale.isTerminal_idObj B S hS X).from W)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map π).hom := by
  refine surjective_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (hZ.flip.map (SpacesEtale.toSpaces B S hS X))) ?_
  rw [congrArg (fun k => k.hom)
    (SpacesEtale.toSpaces_map_from_idObj B S hS ((comparisonFunctor B S hS X).obj U))]
  exact hU

/-! ### The equalizer diagram of an étale presentation -/

/-- For every étale scheme chart `U` of `X` there is an étale scheme chart `R` of `X` with two
morphisms `t, s : R ⟶ U` of the small étale site exhibiting `R` as the fibre product `U ×_X U`
in the spaces-étale site of `X`, that is as the product of the comparison image of `U` with
itself over the terminal object `X`. -/
theorem exists_relationChart (U : SmallEtale B S hS X.1) :
    ∃ (R : SmallEtale B S hS X.1) (t s : R ⟶ U),
      IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
        ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
        ((SpacesEtale.isTerminal_idObj B S hS X).from
          ((comparisonFunctor B S hS X).obj U)) :=
  exists_etaleChart_isPullback_self B S hS X (SpacesEtale.idObj B S hS X) U
    ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))

/-- Let `U` be an étale scheme chart of `X` whose structure morphism is surjective, let `R` be an
étale scheme chart with two morphisms `t, s : R ⟶ U` exhibiting it as `U ×_X U`, let `W` be any
object of the spaces-étale site of `X`, let `Z` be the product `W ×_X U` with projections `π` and
`ρ`, and let `Z₂` be the fibre product of `ρ` with `t`, with projections `p` and `c`; so `Z₂` is
`W ×_X R`. Let `q : Z₂ ⟶ Z` be the morphism with components `p ≫ π` and `c ≫ s`. Then for
every sheaf `P` on the spaces-étale site of `X`, with values in an arbitrary category,

`P(W) → P(Z) ⇉ P(Z₂)`

is an equalizer diagram, the two parallel arrows being restriction along `p` and along `q`. -/
noncomputable def isLimitForkOfEtalePresentation (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    {W Z Z₂ : SpacesEtale B S hS X} {π : Z ⟶ W} {ρ : Z ⟶ (comparisonFunctor B S hS X).obj U}
    {p q : Z₂ ⟶ Z} {c : Z₂ ⟶ (comparisonFunctor B S hS X).obj R}
    (hZ : IsPullback π ρ ((SpacesEtale.isTerminal_idObj B S hS X).from W)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (hZ₂ : IsPullback p c ρ ((comparisonFunctor B S hS X).map t))
    (hq₁ : q ≫ π = p ≫ π) (hq₂ : q ≫ ρ = c ≫ (comparisonFunctor B S hS X).map s)
    (w : P.map π.op ≫ P.map p.op = P.map π.op ≫ P.map q.op) :
    IsLimit (Fork.ofι (P.map π.op) w) := by
  have hprod : IsPullback p (c ≫ (comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from Z)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)) := by
    have h := (hZ₂.flip.paste_horiz hR.flip).flip
    rwa [show ρ ≫ (SpacesEtale.isTerminal_idObj B S hS X).from
      ((comparisonFunctor B S hS X).obj U) =
        (SpacesEtale.isTerminal_idObj B S hS X).from Z from
      (SpacesEtale.isTerminal_idObj B S hS X).hom_ext _ _] at h
  have hq : q = hZ.lift (p ≫ π) (c ≫ (comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).hom_ext _ _) := by
    refine hZ.hom_ext ?_ ?_
    · rw [hq₁, hZ.lift_fst]
    · rw [hq₂, hZ.lift_snd]
  subst hq
  exact isLimitForkOfSurjectiveSingleton B S hS P hP
    (isSurjective_of_isPullback_isTerminal B S hS hU hZ)
    (isPullback_lift_of_isTerminal (SpacesEtale.isTerminal_idObj B S hS X) hZ hprod) w

/-- The equalizer diagram of `AlgebraicGeometry.Space.isLimitForkOfEtalePresentation`, with the
morphism `q : Z₂ ⟶ Z` satisfying `q ≫ π = p ≫ π` and `q ≫ ρ = c ≫ s`, and the commutation of
the fork, produced rather than supplied. -/
theorem exists_isLimitFork_of_etalePresentation (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    {W Z Z₂ : SpacesEtale B S hS X} {π : Z ⟶ W} {ρ : Z ⟶ (comparisonFunctor B S hS X).obj U}
    {p : Z₂ ⟶ Z} {c : Z₂ ⟶ (comparisonFunctor B S hS X).obj R}
    (hZ : IsPullback π ρ ((SpacesEtale.isTerminal_idObj B S hS X).from W)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (hZ₂ : IsPullback p c ρ ((comparisonFunctor B S hS X).map t)) :
    ∃ (q : Z₂ ⟶ Z) (w : P.map π.op ≫ P.map p.op = P.map π.op ≫ P.map q.op),
      q ≫ π = p ≫ π ∧ q ≫ ρ = c ≫ (comparisonFunctor B S hS X).map s ∧
        Nonempty (IsLimit (Fork.ofι (P.map π.op) w)) := by
  refine ⟨hZ.lift (p ≫ π) (c ≫ (comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).hom_ext _ _), ?_, hZ.lift_fst _ _ _,
    hZ.lift_snd _ _ _, ?_⟩
  · rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hZ.lift_fst]
  · exact ⟨isLimitForkOfEtalePresentation B S hS P hP hU hR hZ hZ₂ (hZ.lift_fst _ _ _)
      (hZ.lift_snd _ _ _) _⟩

/-! ### The equalizer diagram for the chosen binary products, and its functoriality -/

/-- For the chosen binary products of the spaces-étale site: for every sheaf `P` and every
object `W`, the fork

`P(W) → P(U ⨯ W) ⇉ P(R ⨯ W)`

is a limit, the two parallel arrows being restriction along `prod.map t (𝟙 W)` and along
`prod.map s (𝟙 W)`. -/
noncomputable def isLimitForkProdOfEtalePresentation (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (W : SpacesEtale B S hS X)
    (w : P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯ W ⟶ W).op ≫
          P.map (prod.map ((comparisonFunctor B S hS X).map t) (𝟙 W)).op =
        P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯ W ⟶ W).op ≫
          P.map (prod.map ((comparisonFunctor B S hS X).map s) (𝟙 W)).op) :
    IsLimit (Fork.ofι (P.map (prod.snd :
      (comparisonFunctor B S hS X).obj U ⨯ W ⟶ W).op) w) :=
  isLimitForkOfEtalePresentation B S hS P hP hU hR
    ((IsPullback.of_isLimit_binaryFan_of_isTerminal
      (prodIsProd ((comparisonFunctor B S hS X).obj U) W)
      (SpacesEtale.isTerminal_idObj B S hS X)).flip)
    (IsPullback.of_prod_fst_with_id ((comparisonFunctor B S hS X).map t) W).flip
    (by simp) (by simp) w

/-- Restricting along the projection `U ⨯ W ⟶ W` and then along `prod.map t (𝟙 W)` or along
`prod.map s (𝟙 W)` gives the same map. -/
theorem fork_condition_prod (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    {U R : SmallEtale B S hS X.1} (t s : R ⟶ U) (W : SpacesEtale B S hS X) :
    P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯ W ⟶ W).op ≫
        P.map (prod.map ((comparisonFunctor B S hS X).map t) (𝟙 W)).op =
      P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯ W ⟶ W).op ≫
        P.map (prod.map ((comparisonFunctor B S hS X).map s) (𝟙 W)).op := by
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, prod.map_snd, prod.map_snd]

/-- The equality of `AlgebraicGeometry.Space.fork_condition_prod` at every object of the
spaces-étale site, as an equality of morphisms of presheaves. -/
theorem fork_condition_presheaf (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    {U R : SmallEtale B S hS X.1} (t s : R ⟶ U) :
    (Functor.whiskerRight
          (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
          P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P) ≫
        Functor.whiskerRight
          (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map t))) P =
      (Functor.whiskerRight
          (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
          P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P) ≫
        Functor.whiskerRight
          (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map s))) P := by
  ext k
  exact fork_condition_prod B S hS P t s k.unop

/-- The equalizer diagram of `AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation` as a
diagram of presheaves on the spaces-étale site of `X`: the three terms are `P`, the restriction
of `P` along `W ↦ U ⨯ W` and the restriction of `P` along `W ↦ R ⨯ W`, the first arrow is
restriction along the projection `U ⨯ - ⟶ -` and the two parallel arrows are restriction along
`t` and along `s`, and the fork so obtained is a limit in the category of presheaves. -/
noncomputable def isLimitForkPresheafOfEtalePresentation (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (w : (Functor.whiskerRight
            (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
            P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P) ≫
          Functor.whiskerRight
            (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map t))) P =
        (Functor.whiskerRight
            (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
            P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P) ≫
          Functor.whiskerRight
            (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map s))) P) :
    IsLimit (Fork.ofι (Functor.whiskerRight
      (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
      P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P) w) := by
  refine evaluationJointlyReflectsLimits _ (fun k => ?_)
  refine (isLimitMapConeForkEquiv ((evaluation (SpacesEtale B S hS X)ᵒᵖ A).obj k) w).symm ?_
  exact isLimitForkProdOfEtalePresentation B S hS P hP hU hR k.unop
    (congrArg (fun φ => NatTrans.app φ k) w)

/-! ### Sections of the direct image over a chart -/

/-- The sections over an étale scheme chart `V` of `Y` of the direct image of a sheaf of sets `G`
along `f` are the sections, over the base-changed chart `V ×_Y X`, of the extension of `G` to
the spaces-étale site of `X`. -/
theorem smallEtaleDirectImage_obj_obj_obj (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1) :
    ((smallEtaleDirectImage B S hS f).obj G).obj.obj (op V) =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.obj
        (op (chartBaseChange B S hS f V)) := rfl

/-- For an étale scheme chart `V` of `Y`, a surjective étale scheme chart `U` of `X` and
`R = U ×_X U`, the sequence of sections

`P(V ×_Y X) → P(V ×_Y U) ⇉ P(V ×_Y R)`

of a sheaf `P` on the spaces-étale site of `X` is an equalizer diagram, the two parallel arrows
being restriction along `t` and along `s`. -/
noncomputable def isLimitForkChartBaseChange (f : X ⟶ Y) (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)))
    (V : SmallEtale B S hS Y.1)
    (w : P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯
            chartBaseChange B S hS f V ⟶ chartBaseChange B S hS f V).op ≫
          P.map (prod.map ((comparisonFunctor B S hS X).map t)
            (𝟙 (chartBaseChange B S hS f V))).op =
        P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯
            chartBaseChange B S hS f V ⟶ chartBaseChange B S hS f V).op ≫
          P.map (prod.map ((comparisonFunctor B S hS X).map s)
            (𝟙 (chartBaseChange B S hS f V))).op) :
    IsLimit (Fork.ofι (P.map (prod.snd : (comparisonFunctor B S hS X).obj U ⨯
      chartBaseChange B S hS f V ⟶ chartBaseChange B S hS f V).op) w) :=
  isLimitForkProdOfEtalePresentation B S hS P hP hU hR (chartBaseChange B S hS f V) w

/-! ### The sequence on the small étale site of the target -/

/-- Base change of the étale scheme charts of `Y` to the spaces-étale site of `X`, as a functor:
it sends an étale scheme chart `V` of `Y` to the object `V ×_Y X`, which is
`AlgebraicGeometry.Space.chartBaseChange`. -/
noncomputable abbrev chartBaseChangeFunctor (f : X ⟶ Y) :
    SmallEtale B S hS Y.1 ⥤ SpacesEtale B S hS X :=
  comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor

/-- The equality of `AlgebraicGeometry.Space.fork_condition_prod` at every base-changed chart
`V ×_Y X`, as an equality of morphisms of presheaves on the small étale site of `Y`. -/
theorem fork_condition_chartBaseChange (f : X ⟶ Y) (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    {U R : SmallEtale B S hS X.1} (t s : R ⟶ U) :
    (Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
            P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P)) ≫
        Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map t))) P) =
      (Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
            P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P)) ≫
        Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map s))) P) := by
  ext k
  exact fork_condition_prod B S hS P t s (chartBaseChange B S hS f k.unop)

/-- For a sheaf `P` on the spaces-étale site of `X`, a surjective étale scheme chart `U` of `X`
and `R = U ×_X U` with its two projections `t, s`, the fork of presheaves on the small étale
site of `Y`

`V ↦ P(V ×_Y X)` → `V ↦ P(V ×_Y U)` ⇉ `V ↦ P(V ×_Y R)`

is a limit, the two parallel arrows being restriction along `t` and along `s`. -/
noncomputable def isLimitForkChartBaseChangePresheaf (f : X ⟶ Y)
    (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι (Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
      (Functor.whiskerRight
        (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε)) P :
        P ⟶ (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙ P))
      (fork_condition_chartBaseChange B S hS f P t s)) := by
  refine evaluationJointlyReflectsLimits _ (fun k => ?_)
  refine (isLimitMapConeForkEquiv ((evaluation (SmallEtale B S hS Y.1)ᵒᵖ A).obj k)
    (fork_condition_chartBaseChange B S hS f P t s)).symm ?_
  exact isLimitForkChartBaseChange B S hS f P hP hU hR k.unop
    (congrArg (fun φ => NatTrans.app φ k) (fork_condition_chartBaseChange B S hS f P t s))

/-- The presheaf `V ↦ P(V ×_Y X)` is the presheaf underlying the direct image of sheaves of sets
along `f`, when `P` is the extension of a sheaf `G` on the small étale site of `X` to the
spaces-étale site. -/
theorem chartBaseChangeFunctor_op_comp_eq (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (chartBaseChangeFunctor B S hS f).op ⋙
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj =
      ((smallEtaleDirectImage B S hS f).obj G).obj := rfl

/-- The sheaf of sets underlying the direct image of modules along `f` is the direct image of
the sheaf of sets underlying the module. -/
theorem moduleSheaf_modulePushforward (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)
        ((modulePushforward B S hS f).obj F) =
      (smallEtaleDirectImage B S hS f).obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) F) := rfl

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `U` be a surjective étale
scheme chart of `X`, let `R = U ×_X U` with its two projections `t, s : R ⟶ U`, and let `G` be a
sheaf of sets on the small étale site of `X`. Then the sequence of presheaves on the small
étale site of `Y`

`0 → f_*G → (V ↦ G(V ×_Y U)) → (V ↦ G(V ×_Y R))`,

whose second arrow is the difference of restriction along `t` and along `s`, is exact: the fork
is a limit. -/
noncomputable def isLimitForkDirectImage (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι (Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
        (Functor.whiskerRight
            (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε))
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj :
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj ⟶
            (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :
        ((smallEtaleDirectImage B S hS f).obj G).obj ⟶
          (chartBaseChangeFunctor B S hS f).op ⋙
            ((prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj))
      (fork_condition_chartBaseChange B S hS f _ t s)) :=
  isLimitForkChartBaseChangePresheaf B S hS f _
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).property hU hR

/-- For every surjective étale scheme chart `U` of `X` there is an étale scheme chart
`R = U ×_X U` with projections `t, s : R ⟶ U` for which the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage` is a limit. -/
theorem exists_relationChart_isLimitForkDirectImage (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (U : SmallEtale B S hS X.1)
    (hU : IsSurjective B S hS U.1.hom) :
    ∃ (R : SmallEtale B S hS X.1) (t s : R ⟶ U)
        (_ : IsPullback ((comparisonFunctor B S hS X).map t)
          ((comparisonFunctor B S hS X).map s)
          ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
          ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))),
      Nonempty (IsLimit (Fork.ofι _ (fork_condition_chartBaseChange B S hS f
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj t s))) := by
  obtain ⟨R, t, s, hR⟩ := exists_relationChart B S hS U
  exact ⟨R, t, s, hR, ⟨isLimitForkDirectImage B S hS f G hU hR⟩⟩

/-! ### The direct image of modules is a right adjoint -/

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces is a right adjoint. -/
instance isRightAdjoint_modulePushforward (f : X ⟶ Y) :
    (modulePushforward B S hS f).IsRightAdjoint :=
  (modulePullbackAdjunction B S hS f).isRightAdjoint

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces is an additive
functor. -/
@[stacks 03LU "additivity of the direct image"]
instance modulePushforward_additive (f : X ⟶ Y) :
    (modulePushforward B S hS f).Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry.Space

end
